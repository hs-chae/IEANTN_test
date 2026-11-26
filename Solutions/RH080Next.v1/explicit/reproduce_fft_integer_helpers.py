#!/usr/bin/env python3
"""Reproduce actual increment_words and divide_small source helper proofs (not whole FFT PV)."""
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
    for formal, concrete in [('FFTSource.lean','w4_fft.c'),('FapFFTSource.lean','fap_fft.c')]:
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
    seed = 0x080D06
    rng = random.Random(seed)
    base = 10**9
    cases = []
    for n in range(7):
        for fill in [0,base-1]:
            cases.append(('increment', [fill]*10, 1, n, 1, 0))
        for d in [1,2,3,100,131072,16777216,base-1]:
            for ceiling in [0,1]:
                cases.append(('divide',[rng.randrange(base) for _ in range(10)],1,n,d,ceiling))
    for _ in range(24):
        cases.append(('increment',[rng.randrange(base) for _ in range(10)],rng.randrange(3),rng.randrange(7),1,0))
        cases.append(('divide',[rng.randrange(base) for _ in range(10)],rng.randrange(3),rng.randrange(7),rng.randrange(1,base),rng.randrange(2)))
    expected = []
    statements = []
    for operation,data,start,n,d,ceiling in cases:
        before_value = sum(data[start+i]*base**i for i in range(n))
        if operation == 'increment':
            capacity = base**n
            value = (before_value+1)%capacity
            status = (before_value+1)//capacity
            call = 'increment_words(aa+'+str(start)+','+str(n)+'ULL)'
        else:
            value = before_value//d + int(ceiling and before_value%d!=0)
            status = 0
            call = 'divide_small(aa+'+str(start)+','+str(n)+'ULL,'+str(d)+'ULL,'+str(ceiling)+'ULL)'
        after = data.copy()
        for i in range(n):
            after[start+i] = value%base
            value //= base
        need(value==0,'independent integer reference exceeds selected capacity')
        expected.append(' '.join(str(x) for x in [status]+after)+'\n')
        vals = ','.join(str(x)+'ULL' for x in data)
        statements.append('{uint64_t aa[10]={'+vals+'};uint64_t r='+call+';'
            'printf("%llu",(unsigned long long)r);for(unsigned z=0;z<10;z++)printf(" %llu",(unsigned long long)aa[z]);puts("");}')
    native = []
    for concrete in ['w4_fft.c','fap_fft.c']:
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
               '--root','ExplicitFFTDivideAudit']
    with (a.out/'lean-controller.stdout').open('x') as out, (a.out/'lean-controller.stderr').open('x') as err:
        run = subprocess.run(command,stdout=out,stderr=err)
    need(run.returncode==0, 'full source-cold helper proof replay failed')
    proof = json.loads((a.out/'lean/RESULT.json').read_text())
    need(proof['status']=='PASS_SOURCE_COLD_SELECTED_MODULE_COMPILATION_ONLY','unexpected child proof receipt')
    audit = (a.out/'lean/logs/ExplicitFFTDivideAudit.stdout').read_text()
    marker = 'FFT_DIVIDE_SOURCE_AUDIT_PASS two-actual-C-files independently-parsed full-Call all-executions all-argument-orders exact-floor-or-ceiling no-wrap temporary-lifetimes caller-frame Std3 whole-FFT-norm-still-open'
    need(audit.count(marker)==1, 'source/proof dependency audit did not pass exactly once')
    peak = 0
    for p in (a.out/'lean/logs').glob('*.time'):
        matches = re.findall(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())
        need(len(matches)==1,'missing resource usage')
        peak = max(peak,int(matches[0]))
    for row in associations:
        need(sha(Path(row['formal_origin']))==row['formal_sha256'] and
             sha(Path(row['C_origin']))==row['C_sha256'],'source changed during reproduction')
    atomic(a.out/'RESULT.json',dict(status='PASS_SOURCE_FIRST_INCREMENT_AND_DIVIDE_HELPERS_ONLY',
        source_to_AST_execution_correctness_contract_complete=True,source_first_PV_complete=False,
        final_ANT_connection_pending=True,whole_FFT_norm_PV_complete=False,
        associations=associations,native_smoke_tests=native,random_seed=seed,C_compiler=cversion,
        C_compiler_sha256=sha(Path(compiler)),python=sys.version,proof_controller_sha256=sha(controller),
        command=command,proof_receipt_sha256=sha(a.out/'lean/RESULT.json'),
        modules=proof['modules'],seconds=time.monotonic()-began,peak_Lean_rss_kib=peak,oom_events=0,
        bytes=sum(p.stat().st_size for p in a.out.rglob('*') if p.is_file()),
        trust='Restricted C operational-model adequacy and documented LP64/ULL64 ABI; pinned compiler/core runtime, OS and hardware. No successful application effect, initial array representation, numerical FFT result, or final norm bound is trusted. Caller must establish the explicit typed-array/digit preconditions.',
        scope='Actual increment_words and divide_small helpers in both preserved C files, independently parsed syntax, complete Call termination and all-execution correctness including every permitted call argument order, exact encoded integer addition/floor/ceiling, temporary lifetimes, slice and caller-object frames. Domain: normalized base-billion digits, 0<=n<=6, 1<=d<1e9, ceiling=0 or1. Native tests are supplementary; they do not prove the theorem.'))
    print('PASS integer source contracts; final ANT connection and whole FFT norm remain open',flush=True)

if __name__=='__main__':
    main()
