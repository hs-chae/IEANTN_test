#!/usr/bin/env python3
"""Fresh source-only replay of the actual multiply suffix helper contracts.
This does not claim full C FFT-to-ANT source-first PV.
"""
import argparse,hashlib,json,os,subprocess,time,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parents[2]
S=ROOT/'Solutions/RH080Next.v1/pv'
OLD=ROOT/'Solutions/RH080Study.v1/pv'
CTX=None
GENERIC=('Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets')
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def atomic(p,x):
    need(not p.exists(),'Freshreceipt required')
    t=p.with_name('.'+p.name+'.tmp')
    with t.open('x')as f:json.dump(x,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
    try:os.link(t,p)
    finally:t.unlink()
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',type=Path,required=True);ap.add_argument('--root',action='append',default=[]);ap.add_argument('--context',type=Path,required=True);ap.add_argument('--memory-gib',type=int,default=128);a=ap.parse_args();CTX=a.context
    need(1<=a.memory_gib<=300,'Per-run memory ceiling must be 1..300GiB')
    mem={line.split(':')[0]:int(line.split()[1])*1024 for line in Path('/proc/meminfo').read_text().splitlines()}
    need(mem['MemAvailable'] >= (a.memory_gib+256)*2**30,'Insufficient RAM after 256GiB host reserve')
    need(not a.root,'This driver fixes the suffix audit root')
    a.root=['FFTFixedMultiplySuffixAudit']
    need(not a.run.exists(),'Freshsourcecold rundirectory required');a.run.mkdir(parents=True)
    source=a.run/'source';objects=a.run/'objects';logs=a.run/'logs'
    for p in [source,objects,logs]:p.mkdir()
    sys.path.insert(0,str(ROOT/'Solutions/RH080Next.v1/dual'))
    from reproduce_dual import context as validated_context
    c=validated_context(CTX,ROOT);compiler=Path(c['compiler']);need(sha(compiler)==c['compiler_sha256'],'Compilerbytes differ')
    seen=set();active=set();rows=[]
    def visit(n):
        if n in seen or n.split('.')[0]in GENERIC:return
        need(n not in active,'Importcycle');active.add(n)
        p=next((q for base in [S/'lean',OLD/'lean',OLD.parent/'sine',ROOT/'Solutions/RH080Next.v1/explicit',ROOT/'Solutions/CH2.v6',ROOT/'Solutions/RH080Next.v1/primal',ROOT/'Solutions/RH080Next.v1/dual',ROOT]if(q:=base/(n.replace('.','/')+'.lean')).is_file()),None)
        need(p is not None,'Missingappsource '+n)
        imports=[]
        for line in p.read_text().splitlines():
            if line.startswith('import '):imports.extend(line[7:].split('--',1)[0].split())
        for d in imports:visit(d)
        active.remove(n);seen.add(n)
        target=source/(n.replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(p.read_bytes())
        rows.append(dict(module=n,origin=str(p),source_sha256=sha(p),snapshot=str(target),imports=imports))
    for n in a.root:visit(n)
    actual_c=S/'fft/w4_fft_recursive.c'
    syntax=S/'lean/FFTRecursiveSource.lean'
    chars=next(line.split(':=',1)[1] for line in syntax.read_text().splitlines() if line.startswith('def sourceChars :'))
    import re
    reconstructed=bytes(int(x) for x in re.findall(r'Char.ofNat ([0-9]+)',chars))
    need(reconstructed==actual_c.read_bytes(),'Actual C/sourceChars byte mismatch')
    atomic(a.run/'SOURCE_BYTES.json',dict(actual_source=str(actual_c),source_sha256=sha(actual_c),source_syntax_sha256=sha(syntax),bytes=len(reconstructed),status='EXACT_BYTE_EQUALITY'))
    atomic(a.run/'PLAN.json',dict(status='FROZEN_SOURCE_COLD_DEVELOPMENT_PLAN_NOT_ACCEPTANCE',roots=a.root,source_rows=rows,context_sha256=sha(CTX),controller_sha256=sha(Path(__file__)),generic=c['generic_dependencies'],application_object_fallback=False,memory_ceiling_gib=a.memory_gib,MemAvailable_bytes_before=mem['MemAvailable']))
    (a.run/'reproduce_suffix.executed.py').write_bytes(Path(__file__).read_bytes())
    harness=ROOT/'Solutions/RH080Next.v1/primal/copy_words_harness.c'
    native_command=['cc','-std=c11','-O2','-Wall','-Wextra','-I',str(actual_c.parent),str(harness),'-o',str(a.run/'copy_words_harness')]
    compiler_version=subprocess.check_output(['cc','--version'],text=True)
    with (a.run/'native_compile.stdout').open('xb') as out,(a.run/'native_compile.stderr').open('xb') as err:
        native_compile=subprocess.run(native_command,stdout=out,stderr=err)
    need(native_compile.returncode==0,'Native actual-source helper compilation failed')
    native=subprocess.run([str(a.run/'copy_words_harness')],capture_output=True,text=True)
    (a.run/'native_run.stdout').write_text(native.stdout);(a.run/'native_run.stderr').write_text(native.stderr)
    need(native.returncode==0 and native.stdout.startswith('PASS actual copy_words: 1032 cases;'),'Native helper exercise failed')
    atomic(a.run/'NATIVE_HELPER_EXERCISE.json',dict(status='PASS_RUNTIME_EXERCISE_NOT_PROOF',compiler_version=compiler_version,command=native_command,source_sha256=sha(actual_c),harness_sha256=sha(harness),binary_sha256=sha(a.run/'copy_words_harness'),stdout=native.stdout,seed='4f1bbcdc7135a9e7'))
    started=time.monotonic();commands=[]
    env=dict(os.environ,LEAN_PATH=str(objects)+':'+c['generic_lean_path'],PYTHONDONTWRITEBYTECODE='1')
    for row in rows:
        n=row['module'];target=objects/(n.replace('.','/')+'.olean');target.parent.mkdir(parents=True,exist_ok=True)
        out=logs/(n+'.stdout');err=logs/(n+'.stderr');tm=logs/(n+'.time');command=['/usr/bin/time','-v','-o',str(tm),'prlimit','--as='+str(a.memory_gib*2**30),'--stack='+str(256*2**20),'--',str(compiler),'-j1','--root='+str(source),'-o',str(target),row['snapshot']]
        t=time.monotonic()
        with out.open('xb')as o,err.open('xb')as e:p=subprocess.run(command,cwd=source,env=env,stdout=o,stderr=e)
        item=dict(module=n,command=command,exitcode=p.returncode,seconds=time.monotonic()-t,stdout_sha256=sha(out),stderr_sha256=sha(err),time_sha256=sha(tm));commands.append(item)
        diagnostic=__import__('re').search(r'PANIC|error(?:\([^)]*\))?:|uncaught exception|failed to compile',out.read_text()+'\n'+err.read_text(),__import__('re').I)
        if p.returncode or diagnostic is not None:
            atomic(a.run/'FAILED.json',dict(status='SOURCE_COLD_DEVELOPMENT_COMPILE_FAILED',commands=commands));raise ValueError('Compilefailed '+n)
        need(target.is_file(),'Noobjectoutput');item['object_sha256']=sha(target)
        atomic(a.run/(n+'.COMPILED.json'),item)
    for row in rows:need(sha(Path(row['origin']))==row['source_sha256'],'Sourceschangedduringdevelopment')
    audit=logs/'FFTFixedMultiplySuffixAudit.stdout'
    need('MULTIPLY_SUFFIX_HELPER_AUDIT_PASS roots=15 closure=' in audit.read_text(),'Missing actual suffix typed/source/math/axiom gate')
    need('full_C_caller_and_ANT_PV=false' in audit.read_text(),'Missing explicit helper scope boundary')
    need(sha(Path(__file__))==json.loads((a.run/'PLAN.json').read_text())['controller_sha256'],'Controller changed')
    need(sha(actual_c)==json.loads((a.run/'SOURCE_BYTES.json').read_text())['source_sha256'],'Actual C changed')
    peak_kib=0;oom=0
    for tm in logs.glob('*.time'):
        text=tm.read_text()
        for line in text.splitlines():
            if 'Maximum resident set size (kbytes):' in line:peak_kib=max(peak_kib,int(line.rsplit(':',1)[1]))
        if 'Command terminated by signal 9' in text:oom+=1
    disk=sum(p.stat().st_size for p in a.run.rglob('*') if p.is_file())
    atomic(a.run/'RESULT.json',dict(peak_ram_kib=peak_kib,disk_bytes=disk,oom_or_sigkill_events=oom,status='PASS_SOURCE_COLD_MULTIPLY_SUFFIX_HELPER_CONTRACTS_NOT_FULL_FFT_PV',actual_source_sha256=sha(actual_c),roots=a.root,modules=len(rows),seconds=time.monotonic()-started,commands=commands,source_first_PV_complete=False,math_consumer_complete=False))
    print(json.dumps(dict(status='PASS_SOURCE_COLD_MULTIPLY_SUFFIX_HELPER_CONTRACTS_NOT_FULL_FFT_PV',modules=len(rows),seconds=time.monotonic()-started)))
if __name__=='__main__':main()
