#!/usr/bin/env python3
"""Reproduce the fixed_add source/execution/integer-correctness contract; final ANT connection remains pending."""
from __future__ import annotations
import argparse, hashlib, json, os, random, re, shutil, subprocess, sys, time
from pathlib import Path

def need(condition, message):
    if not condition:
        raise ValueError(message)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def atomic(path, value):
    need(not path.exists(), 'receipt already exists')
    tmp = path.with_name('.'+path.name+'.tmp')
    with tmp.open('x') as f:
        json.dump(value, f, indent=2, allow_nan=False)
        f.write('\n')
        f.flush()
        os.fsync(f.fileno())
    try:
        os.link(tmp, path)
    finally:
        tmp.unlink()

def main():
    ap = argparse.ArgumentParser(allow_abbrev=False, description=__doc__)
    ap.add_argument('--context', type=Path, required=True)
    ap.add_argument('--out', type=Path, required=True)
    ap.add_argument('--cc', default='cc')
    a = ap.parse_args()
    need(not a.out.exists(), 'fresh experiment-owned output directory required')
    mem = {l.split(':')[0]:int(l.split()[1])*1024 for l in Path('/proc/meminfo').read_text().splitlines()}
    need(mem['MemAvailable'] >= (256+256)*2**30, 'need 256GiB run allowance plus 256GiB host reserve')
    source = Path(__file__).resolve().parent
    pv = source.parent/'pv'
    a.out.mkdir(parents=True)
    (a.out/'native').mkdir()
    associations = []
    for formal, concrete in [('FFTSource.lean','w4_fft.c'),('FapFFTSource.lean','fap_fft.c'),('FFTRecursiveSource.lean','w4_fft_recursive.c'),('FapFFTRecursiveSource.lean','fap_fft_recursive.c')]:
        lean = pv/'lean'/formal
        cfile = pv/'fft'/concrete
        text = lean.read_text()
        match = re.search(r'^def sourceChars[^\n]*\[(.*?)\]\s*$',text,re.M)
        need(match is not None, 'formal sourceChars missing: '+formal)
        chars = match.group(1).split(', ')
        need(all(re.fullmatch(r'Char\.ofNat \d+', x) for x in chars), 'unsupported sourceChars encoding')
        encoded = ''.join(chr(int(x[11:])) for x in chars).encode()
        need(encoded == cfile.read_bytes(), 'actual C differs from formally parsed source string')
        snapshot = a.out/'native'/concrete
        snapshot.write_bytes(encoded)
        associations.append(dict(formal_origin=str(lean),formal_sha256=sha(lean),
            C_origin=str(cfile),C_sha256=sha(cfile),C_snapshot=str(snapshot)))
    # This mutation check audits exact file-to-formal-string association. It is
    # not a replacement for the general independent Lean source-parser proof.
    need(associations[0]['C_sha256'] != hashlib.sha256((a.out/'native/w4_fft.c').read_bytes()+b'\n').hexdigest(),
         'exact source association mutation was not distinguished')
    began = time.monotonic()
    compiler = shutil.which(a.cc)
    need(compiler is not None, 'C compiler missing')
    cversion = subprocess.run([compiler,'--version'],check=True,capture_output=True,text=True).stdout
    seed = 0x080A55
    rng = random.Random(seed)
    base = 10**9
    capacity = base**5
    patterns = [(12,0,6),(0,0,6),(6,0,6),(6,0,0),(0,0,0)]
    magnitude_pairs = [(0,0),(1,capacity-1),(capacity-1,capacity-1),(capacity//2,capacity//2),(capacity-1,1)]
    cases = []
    for pattern in patterns:
        for sa in [0,1]:
            for sb in [0,1]:
                for subtract in [0,1]:
                    for a_value,b_value in magnitude_pairs:
                        cases.append((pattern,sa,sb,subtract,a_value,b_value))
    for _ in range(64):
        cases.append((rng.choice(patterns),rng.randrange(2),rng.randrange(2),rng.randrange(2),rng.randrange(capacity),rng.randrange(capacity)))
    expected = []
    statements = []
    for (ost,ast,bst),sa,sb,subtract,a_value,b_value in cases:
        pool = [rng.randrange(base) for _ in range(24)]
        for start,value,sign in [(ast,a_value,sa)]+([] if bst==ast else [(bst,b_value,sb)]):
            for i in range(5):
                pool[start+i] = value%base
                value //= base
            pool[start+5] = sign
        a_value = sum(pool[ast+i]*base**i for i in range(5))
        b_value = sum(pool[bst+i]*base**i for i in range(5))
        sa = pool[ast+5]
        sb = pool[bst+5]
        effective_b = 1-sb if subtract else sb
        if sa==effective_b:
            total = a_value+b_value
            magnitude,status = total%capacity,total//capacity
            negative = sa
        elif a_value<b_value:
            magnitude,status,negative = b_value-a_value,0,effective_b
        else:
            magnitude,status,negative = a_value-b_value,0,sa
        if magnitude==0:
            negative = 0
        after = pool.copy()
        for i in range(5):
            after[ost+i] = magnitude%base
            magnitude //= base
        after[ost+5] = negative
        need(magnitude==0,'independent signed reference exceeds selected capacity')
        expected.append(' '.join(str(x) for x in [status]+after)+'\n')
        vals = ','.join(str(x)+'ULL' for x in pool)
        call = 'fixed_add(aa+'+str(ost)+',aa+'+str(ast)+',aa+'+str(bst)+','+str(subtract)+'ULL)'
        statements.append('{uint64_t aa[24]={'+vals+'};uint64_t r='+call+';'
            'printf("%llu",(unsigned long long)r);for(unsigned z=0;z<24;z++)printf(" %llu",(unsigned long long)aa[z]);puts("");}')
    native = []
    for concrete in ['w4_fft.c','fap_fft.c','w4_fft_recursive.c','fap_fft_recursive.c']:
        directory = a.out/'native'
        harness = directory/(concrete+'.harness.c')
        harness.write_text('#include <stdint.h>\n#include <limits.h>\n#include <string.h>\n'
            '_Static_assert(CHAR_BIT==8 && sizeof(uint64_t)==8 && sizeof(void*)==8,"selected ABI");\n'
            '#define main saved_numerical_main\n#include '+json.dumps(concrete)+'\n#undef main\n'
            'int main(void){\n'+'\n'.join(statements)+'\nreturn 0;}\n')
        exe = directory/(concrete+'.test')
        command = [compiler,'-std=c11','-O2','-Wall','-Wextra',str(harness),'-o',str(exe)]
        built = subprocess.run(command,capture_output=True,text=True)
        (directory/(concrete+'.compile.stdout')).write_text(built.stdout)
        (directory/(concrete+'.compile.stderr')).write_text(built.stderr)
        need(built.returncode==0, 'actual C helper compilation failed')
        run = subprocess.run([str(exe)],capture_output=True,text=True)
        (directory/(concrete+'.run.stdout')).write_text(run.stdout)
        (directory/(concrete+'.run.stderr')).write_text(run.stderr)
        need(run.returncode==0 and run.stderr=='', 'native helper test failed')
        need(run.stdout == ''.join(expected), 'native helper integer/slice frame check failed')
        native.append(dict(source=concrete,command=command,executable_sha256=sha(exe),
            harness_sha256=sha(harness),output_sha256=hashlib.sha256(run.stdout.encode()).hexdigest(),cases=len(cases)))
    controller = pv/'reproduce_lean.py'
    command = [sys.executable,str(controller),'--context',str(a.context),'--run',str(a.out/'lean'),
               '--root','ExplicitFFTAddAudit']
    with (a.out/'lean-controller.stdout').open('x') as out, (a.out/'lean-controller.stderr').open('x') as err:
        run = subprocess.run(command,stdout=out,stderr=err)
    need(run.returncode==0, 'full source-cold helper proof replay failed')
    proof = json.loads((a.out/'lean/RESULT.json').read_text())
    need(proof['status']=='PASS_SOURCE_COLD_SELECTED_MODULE_COMPILATION_ONLY','unexpected child proof receipt')
    audit = (a.out/'lean/logs/ExplicitFFTAddAudit.stdout').read_text()
    marker = 'FFT_ADD_SOURCE_AUDIT_PASS four-actual-C-files independently-parsed full-Call all-executions all-argument-orders signed-integer-add-sub alias-safe no-wrap temporary-lifetimes caller-frame Std3 final-ANT-connection-pending'
    need(audit.count(marker)==1, 'source/proof dependency audit did not pass exactly once')
    peak = 0
    for p in (a.out/'lean/logs').glob('*.time'):
        matches = re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())
        need(len(matches)==1,'missing resource usage')
        peak = max(peak,int(matches[0]))
    for row in associations:
        need(sha(Path(row['formal_origin']))==row['formal_sha256'] and
             sha(Path(row['C_origin']))==row['C_sha256'],'source changed during reproduction')
    atomic(a.out/'RESULT.json',dict(status='PASS_FIXED_ADD_SOURCE_EXECUTION_INTEGER_CONTRACT_ONLY',
        source_to_AST_execution_correctness_contract_complete=True,source_first_PV_complete=False,
        final_ANT_connection_pending=True,whole_FFT_norm_PV_complete=False,
        associations=associations,native_smoke_tests=native,random_seed=seed,C_compiler=cversion,
        C_compiler_sha256=sha(Path(compiler)),python=sys.version,proof_controller_sha256=sha(controller),
        command=command,proof_receipt_sha256=sha(a.out/'lean/RESULT.json'),
        modules=proof['modules'],seconds=time.monotonic()-began,peak_Lean_rss_kib=peak,oom_events=0,
        bytes=sum(p.stat().st_size for p in a.out.rglob('*') if p.is_file()),
        trust='Restricted C operational-model adequacy and documented LP64/ULL64 ABI; pinned compiler/core runtime, OS and hardware. No successful application effect, initial array representation, numerical FFT result, or final norm bound is trusted. Caller must establish the explicit typed-array/digit preconditions.',
        scope='Actual fixed_add in four preserved iterative/recursive w4/Fap C files; independent parsed syntax, complete Call termination and all-execution signed-integer correctness with zero checked overflow status, every permitted call argument order, safe word operations, temporary lifetimes and caller frames. Domain: normalized five base-billion digits/sign bits/subtract flag, exact-slice aliases or disjoint six-word slices. Native tests supplement the general proof. Final ANT connection remains pending.'))
    print('PASS fixed_add source/execution/integer contract; final ANT connection remains pending',flush=True)

if __name__=='__main__':
    main()
