#!/usr/bin/env python3
"""Runtime/negative controls of the unchanged actual C complex helper.
Universal Lean source correctness and final ANT consumption are separate.
"""
import argparse,ctypes,json,random,shutil,subprocess,sys,time
from pathlib import Path
import check_fixed_multiply as common
BASE=common.BASE
UNIT=common.UNIT
SEED=20261125

def cases():
    rng=random.Random(SEED)
    values=[0,1,UNIT-1,UNIT,UNIT+1,1000*UNIT-1,1000*UNIT]+[rng.randrange(1000*UNIT+1) for _ in range(17)]
    for number in range(len(values)):
        mags=[values[number],values[(number*3+1)%len(values)],values[(number*7+2)%len(values)],values[(number*11+3)%len(values)]]
        for bits in range(16):
            for layout in [('shared',80,96,160,0),('output-is-left',80,96,80,0),('output-overlaps-left',80,96,82,0),('separate',0,0,0,0)]:
                yield layout,mags,[(bits>>i)&1 for i in range(4)]

def exercise(library):
    loaded=ctypes.CDLL(str(library));function=loaded.complex_multiply
    pointer=ctypes.POINTER(ctypes.c_uint64);function.argtypes=[pointer]*4;function.restype=ctypes.c_uint64
    tested=0;mismatches=0;first=None
    for layout,mags,bits in cases():
        name,astart,bstart,outstart,workstart=layout
        initial=[2**64-1 if i%2 else 0x6C8E9CF570932BD5 for i in range(256)]
        if name=='separate':
            arrays=[(ctypes.c_uint64*256)(*initial) for _ in range(4)];arrout,arra,arrb,arrwork=arrays
        else:
            buffer=(ctypes.c_uint64*256)(*initial);arrays=[buffer];arrout=arra=arrb=arrwork=buffer
        for start,array,k in [(astart,arra,0),(astart+6,arra,1),(bstart,arrb,2),(bstart+6,arrb,3)]:
            for i,v in enumerate(common.words(mags[k],bits[k])):array[start+i]=v
        snapshots=[list(array) for array in arrays]
        ar=common.integer(list(arra)[astart:astart+6]);ai=common.integer(list(arra)[astart+6:astart+12])
        br=common.integer(list(arrb)[bstart:bstart+6]);bi=common.integer(list(arrb)[bstart+6:bstart+12])
        expected=(ar*br//UNIT-ai*bi//UNIT,ar*bi//UNIT+ai*br//UNIT)
        ptr=lambda array,start:ctypes.cast(ctypes.byref(array,8*start),pointer)
        status=int(function(ptr(arrout,outstart),ptr(arra,astart),ptr(arrb,bstart),ptr(arrwork,workstart)))
        result=list(arrout)[outstart:outstart+12]
        actual=(common.integer(result[:6]),common.integer(result[6:]))
        failed=status!=0 or actual!=expected or any(result[6*c+i]>=BASE for c in range(2)for i in range(5)) or result[5]>1 or result[11]>1
        for array,before in zip(arrays,snapshots):
            for i,value in enumerate(array):
                allowed=(array is arrout and outstart<=i<outstart+12) or (array is arrwork and workstart<=i<workstart+46)
                if not allowed and value!=before[i]:failed=True
        if failed:
            mismatches+=1
            if first is None:first=dict(layout=name,input=[ar,ai,br,bi],status=status,expected=expected,actual=actual)
        tested+=1
    return dict(cases=tested,mismatches=mismatches,first_mismatch=first)

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--source',type=Path,default=Path(__file__).with_name('w4_fft_recursive.c'));ap.add_argument('--run',type=Path,required=True);a=ap.parse_args()
    start=time.monotonic();common.need(ctypes.sizeof(ctypes.c_uint64)==8 and ctypes.sizeof(ctypes.c_void_p)==8,'Required64-bit ABI unavailable')
    source=a.source.resolve();common.need(source.is_file(),'Actual C source missing');common.need(not a.run.exists(),'Fresh run required');a.run.mkdir(parents=True)
    original=source.read_bytes();compiler=shutil.which('cc');common.need(compiler is not None,'C compiler unavailable')
    version=subprocess.run([compiler,'--version'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False);common.need(version.returncode==0,'Cannot identify compiler')
    compiled=common.compile_library(compiler,source,a.run/'actual.so');actual=exercise(a.run/'actual.so');common.need(actual['cases']>0 and actual['mismatches']==0,'Actual complex helper mismatch')
    text=original.decode('ascii');begin=text.index('uint64_t complex_multiply(');end=text.index('uint64_t initialize_root(',begin);helper=text[begin:end];negative=[]
    for name,old,new in [('wrong-real-sign','fixed_add(out,work,(work+6ULL),1ULL)','fixed_add(out,work,(work+6ULL),0ULL)'),('wrong-cross-product','fixed_multiply((work+12ULL),a,(b+6ULL),(work+36ULL))','fixed_multiply((work+12ULL),a,b,(work+36ULL))')]:
        common.need(helper.count(old)==1,'Mutation fragment is not unique');mutant=a.run/(name+'.c');mutant.write_text(text[:begin]+helper.replace(old,new)+text[end:])
        library=a.run/(name+'.so');compilation=common.compile_library(compiler,mutant,library);result=exercise(library);common.need(result['mismatches']>0,'Semantic source mutation escaped checks')
        negative.append(dict(name=name,compilation=compilation,result=result))
    common.need(source.read_bytes()==original,'Original source changed')
    receipt=dict(status='PASS_ACTUAL_C_RUNTIME_SMOKE_AND_NEGATIVE_MUTATIONS_NOT_A_PROOF',source=str(source),source_sha256=common.sha(source),validator_sha256=common.sha(Path(__file__)),common_validator_sha256=common.sha(Path(common.__file__)),python_optimization=sys.flags.optimize,seed=SEED,compiler=str(Path(compiler).resolve()),compiler_sha256=common.sha(Path(compiler).resolve()),compiler_version=version.stdout.decode('utf-8'),compilation=compiled,actual=actual,negative=negative,seconds=time.monotonic()-start,owner_defined_source_first_PV_complete=False)
    common.atomic(a.run/'RESULT.json',receipt);print(json.dumps(dict(status=receipt['status'],cases=actual['cases'],mutations_detected=len(negative))))
if __name__=='__main__':main()
