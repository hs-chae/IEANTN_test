#!/usr/bin/env python3
"""Bounded controls for the preserved source convert_bound helper.
These runtime tests are not the universal Lean source proof or final ANT link.
"""
import argparse,ctypes,json,random,shutil,subprocess,sys,time
from pathlib import Path
import check_fixed_multiply as common
BASE=10**9
MAX=2**64-1
SEED=20261125

def cases():
    rng=random.Random(SEED)
    for lo in [0,1,BASE-1]+[rng.randrange(BASE) for _ in range(29)]:
        for hi in [0,1,BASE-1,rng.randrange(BASE)]:
            yield [lo,hi,0,0,0,0]
            for k in range(2,6):
                data=[lo,hi,0,0,0,0];data[k]=rng.randrange(1,BASE);yield data

def exercise(library):
    lib=ctypes.CDLL(str(library));f=lib.convert_bound
    f.argtypes=[ctypes.POINTER(ctypes.c_uint64),ctypes.c_uint64];f.restype=ctypes.c_uint64
    count=0;errors=0;first=None
    for data in cases():
        for offset in [0,3,128]:
            initial=[0xD7A39265F01348BC]*150;initial[offset:offset+6]=data
            array=(ctypes.c_uint64*150)(*initial)
            ptr=ctypes.cast(ctypes.byref(array,offset*8),ctypes.POINTER(ctypes.c_uint64))
            actual=int(f(ptr,6));expected=MAX if any(data[2:]) else data[0]+BASE*data[1]
            bad=actual!=expected or list(array)!=initial
            if bad:
                errors+=1
                if first is None:first=dict(offset=offset,data=data,expected=expected,actual=actual)
            count+=1
    return dict(cases=count,mismatches=errors,first_mismatch=first)

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--source',type=Path,required=True);ap.add_argument('--run',type=Path,required=True);a=ap.parse_args()
    begin=time.monotonic();common.need(ctypes.sizeof(ctypes.c_uint64)==8 and ctypes.sizeof(ctypes.c_void_p)==8,'64-bit ABI required')
    source=a.source.resolve();common.need(source.is_file(),'Missing source');common.need(not a.run.exists(),'Fresh run required');a.run.mkdir(parents=True)
    original=source.read_bytes();text=original.decode('ascii');compiler=shutil.which('cc');common.need(compiler is not None,'Compiler unavailable')
    version=subprocess.run([compiler,'--version'],stdout=subprocess.PIPE,stderr=subprocess.PIPE,check=False);common.need(version.returncode==0,'Compiler identity unavailable')
    compilation=common.compile_library(compiler,source,a.run/'actual.so');actual=exercise(a.run/'actual.so');common.need(actual['cases']>0 and actual['mismatches']==0,'Actual C conversion mismatch')
    start=text.index('uint64_t convert_bound(');end=text.index('\n}',start)+2;fragment=text[start:end];negative=[]
    for label,old,new in [('skip-upper-word','uint64_t i=2ULL','uint64_t i=3ULL'),('wrong-base','1000000000ULL*a[1ULL]','100000000ULL*a[1ULL]')]:
        common.need(fragment.count(old)==1,'Mutation fragment not unique');mutant=a.run/(label+'.c');mutant.write_text(text[:start]+fragment.replace(old,new)+text[end:]);library=a.run/(label+'.so')
        compiled=common.compile_library(compiler,mutant,library);result=exercise(library);common.need(result['mismatches']>0,'Source mutation escaped controls');negative.append(dict(name=label,compilation=compiled,result=result))
    common.need(source.read_bytes()==original,'Original source changed')
    receipt=dict(status='PASS_ACTUAL_C_RUNTIME_SMOKE_AND_NEGATIVE_MUTATIONS_NOT_A_PROOF',source=str(source),source_sha256=common.sha(source),validator_sha256=common.sha(Path(__file__)),common_validator_sha256=common.sha(Path(common.__file__)),python_optimization=sys.flags.optimize,seed=SEED,compiler=str(Path(compiler).resolve()),compiler_sha256=common.sha(Path(compiler).resolve()),compiler_version=version.stdout.decode(),compilation=compilation,actual=actual,negative=negative,seconds=time.monotonic()-begin,owner_defined_source_first_PV_complete=False)
    common.atomic(a.run/'RESULT.json',receipt);print(json.dumps(dict(status=receipt['status'],cases=actual['cases'],mutations_detected=len(negative))))
if __name__=='__main__':main()
