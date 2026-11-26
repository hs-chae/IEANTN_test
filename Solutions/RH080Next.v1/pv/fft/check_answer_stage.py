#!/usr/bin/env python3
"""Exercise the verbatim final answer fragment with actual C convert_bound.
This scoped harness is not a full-main native run or a formal proof; Lean
separately proves the source syntax, real declarations, calls, guards/scopes.
"""
import argparse,ctypes,json,random,shutil,subprocess,sys,time
from pathlib import Path
import check_fixed_multiply as common
BASE=10**9
MAX=2**64-1
LIMIT=18446744073709551000
SEED=20261125

def cases():
    rng=random.Random(SEED)
    values=[0,1,BASE-1,BASE,BASE**2-1]+[rng.randrange(BASE**2) for _ in range(19)]
    inputs=[[v%BASE,v//BASE,0,0,0,0]for v in values]
    for k in range(2,6):
        data=[BASE-1,BASE-1,0,0,0,0];data[k]=BASE-1;inputs.append(data)
    for i,a in enumerate(inputs):
        for b in [inputs[(i*7+1)%len(inputs)],inputs[0],inputs[4],inputs[-1]]:
            for status in [0,1]:yield a,b,status

def exercise(library,allowance):
    lib=ctypes.CDLL(str(library));f=lib.answer_probe;p=ctypes.POINTER(ctypes.c_uint64);f.argtypes=[p,p,ctypes.c_uint64];f.restype=ctypes.c_uint64
    count=0;bad=0;first=None
    for a,b,status in cases():
        data=[0x69D15F3C2A7834BE]*512;data[192:198]=a;data[208:214]=b;array=(ctypes.c_uint64*512)(*data);ptr=lambda k:ctypes.cast(ctypes.byref(array,k*8),p)
        firstValue=MAX if any(a[2:]) else a[0]+BASE*a[1];secondValue=MAX if any(b[2:]) else b[0]+BASE*b[1]
        expected=firstValue+secondValue+allowance if status==0 and firstValue<LIMIT and secondValue<LIMIT-firstValue else MAX
        actual=int(f(ptr(192),ptr(208),status));failure=actual!=expected or list(array)!=data
        if failure:
            bad+=1
            if first is None:first=dict(total=a,quad=b,status=status,expected=expected,actual=actual)
        count+=1
    return dict(cases=count,mismatches=bad,first_mismatch=first)

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--source',type=Path,required=True);ap.add_argument('--run',type=Path,required=True);a=ap.parse_args();began=time.monotonic()
    source=a.source.resolve();common.need(source.is_file(),'Missing actual source');common.need(not a.run.exists(),'Fresh run required');a.run.mkdir(parents=True)
    original=source.read_bytes();text=original.decode('ascii');start=text.index('uint64_t answer=18446744073709551615ULL;');end=text.index('\n  free(data);',start);fragment=text[start:end]
    allowance=20 if source.name.startswith('fap_') else 100;common.need(fragment.count('+%dULL'%allowance)==1,'Original allowance not unique')
    compiler=shutil.which('cc');common.need(compiler is not None,'Compiler unavailable');version=subprocess.run([compiler,'--version'],capture_output=True,text=True);common.need(version.returncode==0,'Compiler identity unavailable')
    common.need('"'not in str(source) and '\\'not in str(source),'Unsupported C include path')
    prefix='#include "'+str(source)+'"\nuint64_t answer_probe(uint64_t *total,uint64_t *quad,uint64_t status){\n'
    suffix='\nreturn answer;\n}\n';harness=a.run/'actual-answer-harness.c';harness.write_text(prefix+fragment+suffix)
    compilation=common.compile_library(compiler,harness,a.run/'actual.so');actual=exercise(a.run/'actual.so',allowance);common.need(actual['cases']>0 and actual['mismatches']==0,'Actual verbatim answer fragment mismatch')
    negatives=[]
    for label,old,new in [('wrong-allowance','+%dULL'%allowance,'+%dULL'%(allowance-1)),('reversed-first-guard','first<18446744073709551000ULL','first>18446744073709551000ULL')]:
        common.need(fragment.count(old)==1,'Mutation fragment not unique');mutant=a.run/(label+'.c');mutant.write_text(prefix+fragment.replace(old,new)+suffix);library=a.run/(label+'.so');compiled=common.compile_library(compiler,mutant,library);result=exercise(library,allowance);common.need(result['mismatches']>0,'Source-fragment mutation escaped tests');negatives.append(dict(name=label,compilation=compiled,result=result))
    common.need(source.read_bytes()==original,'Original source changed')
    receipt=dict(status='PASS_VERBATIM_MAIN_ANSWER_FRAGMENT_WITH_ACTUAL_CONVERT_C_NOT_FULL_MAIN_OR_PROOF',source=str(source),source_sha256=common.sha(source),fragment_sha256=__import__('hashlib').sha256(fragment.encode()).hexdigest(),harness_sha256=common.sha(harness),validator_sha256=common.sha(Path(__file__)),common_validator_sha256=common.sha(Path(common.__file__)),python_optimization=sys.flags.optimize,seed=SEED,compiler=str(Path(compiler).resolve()),compiler_sha256=common.sha(Path(compiler).resolve()),compiler_version=version.stdout,compilation=compilation,actual=actual,negative=negatives,seconds=time.monotonic()-began,owner_defined_source_first_PV_complete=False)
    common.atomic(a.run/'RESULT.json',receipt);print(json.dumps(dict(status=receipt['status'],cases=actual['cases'],mutations=len(negatives))))
if __name__=='__main__':main()
