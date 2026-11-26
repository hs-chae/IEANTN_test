#!/usr/bin/env python3
"""Actual unchanged C helper smoke/negative tests, separate from its Lean proof.
Acceptance uses explicit checks, including when Python runs with -O or -OO.
"""
import argparse, ctypes, hashlib, json, os, random, shutil, subprocess, time
from pathlib import Path
BASE=1000000000
SEED=20261125

def need(ok,message):
    if not ok: raise ValueError(message)
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()
def atomic(path,value):
    need(not path.exists(),'Fresh receipt required')
    temporary=path.with_name('.'+path.name+'.tmp')
    with temporary.open('x') as handle:
        json.dump(value,handle,indent=2,allow_nan=False);handle.write('\n');handle.flush();os.fsync(handle.fileno())
    try: os.link(temporary,path)
    finally: temporary.unlink()
def compile_library(compiler,source,output):
    command=[compiler,'-std=c11','-O2','-fPIC','-shared',str(source),'-o',str(output)]
    start=time.monotonic()
    result=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)
    need(result.returncode==0,'C compilation failed: '+result.stderr.decode(errors='replace'))
    need(output.is_file(),'Compiler produced no library')
    return dict(command=command,seconds=time.monotonic()-start,library_sha256=sha(output),source_sha256=sha(source))
def cases():
    rng=random.Random(SEED)
    for n in range(7):
        patterns=[[0]*n,[BASE-1]*n,[0 if i%2 else BASE-1 for i in range(n)],[(i+1)*17 for i in range(n)]]
        patterns += [[rng.randrange(BASE) for i in range(n)] for _ in range(4)]
        for start in [0,1,13,160]:
            for factor in [0,1,2,20,127008000,BASE-1]:
                for digits in patterns: yield n,start,factor,digits

def exercise(library):
    lib=ctypes.CDLL(str(library))
    function=lib.multiply_small
    function.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_uint64,ctypes.c_uint64]
    function.restype=ctypes.c_uint64
    tested=0;mismatches=0;first=None
    for n,start,factor,digits in cases():
        initial=[(2**64-1 if i%2 else 0x6C8E9CF570932BD5) for i in range(256)]
        initial[start:start+n]=digits
        storage=(ctypes.c_uint64*256)(*initial)
        pointer=ctypes.cast(ctypes.byref(storage,8*start),ctypes.POINTER(ctypes.c_uint64))
        returned=int(function(pointer,n,factor))
        total=sum(digit*BASE**i for i,digit in enumerate(digits))*factor
        expected=initial[:]
        for i in range(n): expected[start+i]=(total//BASE**i)%BASE
        carry=total//BASE**n
        actual=list(storage)
        if returned!=carry or actual!=expected:
            mismatches+=1
            if first is None: first=dict(n=n,start=start,factor=factor,input=digits,returned=returned,expected_carry=carry)
        tested+=1
    return dict(cases=tested,mismatches=mismatches,first_mismatch=first)

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--source',type=Path,default=Path(__file__).with_name('w4_fft_recursive.c'))
    ap.add_argument('--run',type=Path,required=True)
    a=ap.parse_args()
    need(ctypes.sizeof(ctypes.c_uint64)==8 and ctypes.sizeof(ctypes.c_void_p)==8,'Required documented 64-bit ABI unavailable')
    source=a.source.resolve();need(source.is_file(),'Actual C source missing')
    need(not a.run.exists(),'Fresh run directory required');a.run.mkdir(parents=True)
    original=source.read_bytes();compiler=shutil.which('cc');need(compiler is not None,'C compiler unavailable')
    version=subprocess.run([compiler,'--version'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)
    need(version.returncode==0,'Cannot identify C compiler')
    compiled=compile_library(compiler,source,a.run/'actual.so')
    actual=exercise(a.run/'actual.so');need(actual['cases']>0 and actual['mismatches']==0,'Actual helper disagreed with independent integer computation')
    text=original.decode('ascii')
    begin=text.index('uint64_t multiply_small(');end=text.index('uint64_t divide_small(',begin)
    helper=text[begin:end]
    mutations=[('multiplication-replaced-by-addition','(a[j]*m)','(a[j]+m)'),
               ('skipped-digit','j=(j+1ULL);','j=(j+2ULL);')]
    negative=[]
    for name,old,new in mutations:
        need(helper.count(old)==1,'Mutation does not identify exactly one actual source fragment')
        changed=text[:begin]+helper.replace(old,new)+text[end:]
        mutant=a.run/(name+'.c');mutant.write_text(changed)
        library=a.run/(name+'.so');receipt=compile_library(compiler,mutant,library);result=exercise(library)
        need(result['mismatches']>0,'Semantic mutation was not detected')
        negative.append(dict(name=name,compilation=receipt,result=result))
    need(source.read_bytes()==original,'Original actual C source changed during test')
    receipt=dict(status='PASS_ACTUAL_C_RUNTIME_SMOKE_AND_NEGATIVE_MUTATIONS_NOT_A_PROOF',seed=SEED,
        source=str(source),source_sha256=sha(source),validator_sha256=sha(Path(__file__)),
        compiler=str(Path(compiler).resolve()),compiler_sha256=sha(Path(compiler).resolve()),
        compiler_version=version.stdout.decode(errors='strict'),compilation=compiled,actual=actual,negative=negative,
        source_verification='General Lean execution/mathematical proof is separate; these finite tests do not establish PV',
        whole_FFT_source_PV=False)
    atomic(a.run/'RESULT.json',receipt)
    print(json.dumps(dict(status=receipt['status'],cases=actual['cases'],mutations_detected=len(negative))))
if __name__=='__main__': main()
