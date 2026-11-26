#!/usr/bin/env python3
"""Exercise the unchanged actual C fixed_multiply helper and semantic mutants.
These finite ABI/runtime checks are separate from the universal Lean source proof.
All acceptance conditions remain active under Python normal, -O and -OO.
"""
import argparse,ctypes,hashlib,json,os,random,shutil,subprocess,time,sys
from pathlib import Path
BASE=10**9
UNIT=10**36
SEED=20261125

def need(ok,message):
    if not ok:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def atomic(path,value):
    need(not path.exists(),'Fresh receipt required');temporary=path.with_name('.'+path.name+'.tmp')
    with temporary.open('x') as handle:
        json.dump(value,handle,indent=2,allow_nan=False);handle.write('\n');handle.flush();os.fsync(handle.fileno())
    try:os.link(temporary,path)
    finally:temporary.unlink()
def compile_library(compiler,source,output):
    command=[compiler,'-std=c11','-O2','-fPIC','-shared',str(source),'-o',str(output)]
    start=time.monotonic();run=subprocess.run(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False)
    need(run.returncode==0,'Actual C compile failed: '+run.stderr.decode(errors='replace'));need(output.is_file(),'Compiler produced no library')
    return dict(command=command,seconds=time.monotonic()-start,source_sha256=sha(source),library_sha256=sha(output))
def words(magnitude,sign):return [(magnitude//BASE**i)%BASE for i in range(5)]+[sign]
def integer(data):
    magnitude=sum(data[i]*BASE**i for i in range(5))
    return -magnitude if data[5] else magnitude

def cases():
    rng=random.Random(SEED)
    magnitudes=[0,1,BASE-1,UNIT-1,UNIT,UNIT+1,1000*UNIT-1,1000*UNIT]+[rng.randrange(1000*UNIT+1) for _ in range(24)]
    layouts=[('shared-root',128,134,160,36),('shared-terms',12,6,24,36),
             ('output-is-left',80,96,80,36),('output-is-right',80,96,96,36),
             ('output-overlaps-left',80,96,82,36),('equal-inputs',80,80,18,36),
             ('separate',0,0,0,0)]
    for number,a in enumerate(magnitudes):
        for b in [magnitudes[(number*7+3)%len(magnitudes)],UNIT+1,1000*UNIT]:
            for sa,sb in [(0,0),(0,1),(1,0),(1,1)]:
                for layout in layouts:yield layout,a,b,sa,sb

def exercise(library):
    loaded=ctypes.CDLL(str(library));function=loaded.fixed_multiply
    pointer=ctypes.POINTER(ctypes.c_uint64);function.argtypes=[pointer]*4;function.restype=ctypes.c_uint64
    tested=0;mismatches=0;first=None
    for layout,a,b,sa,sb in cases():
        name,astart,bstart,outstart,workstart=layout
        initial=[2**64-1 if i%2 else 0x6C8E9CF570932BD5 for i in range(256)]
        if name=='separate':
            arrays=[(ctypes.c_uint64*256)(*initial) for _ in range(4)]
            arrout,arra,arrb,arrwork=arrays
            for i,v in enumerate(words(a,sa)):arra[astart+i]=v
            for i,v in enumerate(words(b,sb)):arrb[bstart+i]=v
        else:
            buffer=(ctypes.c_uint64*256)(*initial)
            for i,v in enumerate(words(a,sa)):buffer[astart+i]=v
            for i,v in enumerate(words(b,sb)):buffer[bstart+i]=v
            arrays=[buffer];arrout=arra=arrb=arrwork=buffer
        snapshots=[list(arr) for arr in arrays]
        av=integer(list(arra)[astart:astart+6]);bv=integer(list(arrb)[bstart:bstart+6]);expected=av*bv//UNIT
        ptr=lambda array,start:ctypes.cast(ctypes.byref(array,8*start),pointer)
        status=int(function(ptr(arrout,outstart),ptr(arra,astart),ptr(arrb,bstart),ptr(arrwork,workstart)))
        actual=list(arrout)[outstart:outstart+6]
        failed=status!=0 or integer(actual)!=expected or any(v>=BASE for v in actual[:5]) or actual[5]>1
        for array,before in zip(arrays,snapshots):
            for index,value in enumerate(array):
                allowed=(array is arrout and outstart<=index<outstart+6) or (array is arrwork and workstart<=index<workstart+10)
                if not allowed and value!=before[index]:failed=True
        if failed:
            mismatches+=1
            if first is None:first=dict(layout=name,a=av,b=bv,status=status,output=actual,expected=expected)
        tested+=1
    return dict(cases=tested,mismatches=mismatches,first_mismatch=first)

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--source',type=Path,default=Path(__file__).with_name('w4_fft_recursive.c'));ap.add_argument('--run',type=Path,required=True);a=ap.parse_args()
    start=time.monotonic();need(ctypes.sizeof(ctypes.c_uint64)==8 and ctypes.sizeof(ctypes.c_void_p)==8,'Documented64-bit ABI unavailable')
    source=a.source.resolve();need(source.is_file(),'Actual C source missing');need(not a.run.exists(),'Fresh run required');a.run.mkdir(parents=True)
    original=source.read_bytes();compiler=shutil.which('cc');need(compiler is not None,'C compiler unavailable')
    version=subprocess.run([compiler,'--version'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False);need(version.returncode==0,'Cannot identify compiler')
    compilation=compile_library(compiler,source,a.run/'actual.so');actual=exercise(a.run/'actual.so');need(actual['cases']>0 and actual['mismatches']==0,'Actual C fixed_multiply mismatch')
    text=original.decode('ascii');begin=text.index('uint64_t fixed_multiply(');end=text.index('uint64_t complex_multiply(',begin);helper=text[begin:end]
    negative=[]
    for name,old,new in [('wrong-product-digit','work[k]=(t%1000000000ULL);','work[k]=((t+1ULL)%1000000000ULL);'),('wrong-fixed-scale','out[i]=work[(i+4ULL)];','out[i]=work[(i+3ULL)];')]:
        need(helper.count(old)==1,'Mutation source fragment is not unique');mutant=a.run/(name+'.c');mutant.write_text(text[:begin]+helper.replace(old,new)+text[end:])
        library=a.run/(name+'.so');compiled=compile_library(compiler,mutant,library);result=exercise(library);need(result['mismatches']>0,'Semantic source mutation escaped checks')
        negative.append(dict(name=name,compilation=compiled,result=result))
    need(source.read_bytes()==original,'Original actual C source changed')
    receipt=dict(status='PASS_ACTUAL_C_RUNTIME_SMOKE_AND_NEGATIVE_MUTATIONS_NOT_A_PROOF',source=str(source),source_sha256=sha(source),validator_sha256=sha(Path(__file__)),python_optimization=sys.flags.optimize,seed=SEED,parameters=dict(base=BASE,unit=UNIT,max_input_magnitude=1000*UNIT),compiler=str(Path(compiler).resolve()),compiler_sha256=sha(Path(compiler).resolve()),compiler_version=version.stdout.decode('utf-8'),compilation=compilation,actual=actual,negative=negative,seconds=time.monotonic()-start,owner_defined_source_first_PV_complete=False,scope='Finite runtime/source-association controls; universal Lean helper proof and final ANT consumption are separate.')
    atomic(a.run/'RESULT.json',receipt);print(json.dumps(dict(status=receipt['status'],cases=actual['cases'],mutations_detected=len(negative))))
if __name__=='__main__':main()
