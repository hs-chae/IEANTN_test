#!/usr/bin/env python3
"""Actual C root/twiddle source controls; not a substitute for Lean proof.
N17 exercises the complete65536-entry table. N24 exercises4096 entries;
all8,388,608 iterations are covered by the generic Lean source theorem.
"""
import argparse,ctypes,json,shutil,subprocess,sys,time
from pathlib import Path
import check_fixed_multiply as common
U=10**36
PI=3141592653589793238462643383279502884
SEED=20261125

def root(n):
    x=2*PI//n;x2=x*x//U;ct=cr=U;st=sr=x
    for i in range(1,11):
        ct=(ct*x2//U)//(2*i*(2*i-1));st=(st*x2//U)//(2*i*(2*i+1));sgn=-1 if i%2 else 1;cr+=sgn*ct;sr+=sgn*st
    return cr,-sr

def mul(a,b):return a[0]*b[0]//U-a[1]*b[1]//U,a[0]*b[1]//U+a[1]*b[0]//U

def exercise(library):
    lib=ctypes.CDLL(str(library));ptrtype=ctypes.POINTER(ctypes.c_uint64)
    initialize=lib.initialize_root;initialize.argtypes=[ptrtype,ctypes.c_uint64,ptrtype];initialize.restype=ctypes.c_uint64
    multiply=lib.complex_multiply;multiply.argtypes=[ptrtype]*4;multiply.restype=ctypes.c_uint64
    results=[];errors=0
    for n,count in [(131072,65536),(16777216,4096)]:
        work=(ctypes.c_uint64*512)();table=(ctypes.c_uint64*(count*12))();p=lambda a,k:ctypes.cast(ctypes.byref(a,k*8),ptrtype)
        status=int(initialize(p(work,128),n,p(work,0)));expectedSeed=root(n);actualSeed=(common.integer(list(work)[128:134]),common.integer(list(work)[134:140]))
        bad=int(status!=0 or actualSeed!=expectedSeed);first=dict(stage='root',expected=expectedSeed,actual=actualSeed) if bad else None
        snapshot=list(work);table[4]=1;expected=(U,0)
        for j in range(1,count):
            status=int(multiply(p(table,j*12),p(table,(j-1)*12),p(work,128),p(work,0)));expected=mul(expected,expectedSeed)
            cell=list(table[j*12:j*12+12]);actual=(common.integer(cell[:6]),common.integer(cell[6:]));failed=status!=0 or actual!=expected or any(cell[c*6+k]>=10**9 for c in range(2)for k in range(5)) or cell[5]>1 or cell[11]>1
            if failed:
                bad+=1
                if first is None:first=dict(stage='twiddle',index=j,expected=expected,actual=actual,status=status)
        if list(work)[46:]!=snapshot[46:]:bad+=1;first=first or dict(stage='physical-work-frame')
        results.append(dict(n=n,entries=count,full_original_table=count==n//2,mismatches=bad,first_mismatch=first));errors+=bad
    return dict(grids=results,mismatches=errors)

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--source',type=Path,required=True);ap.add_argument('--run',type=Path,required=True);a=ap.parse_args();begin=time.monotonic()
    source=a.source.resolve();common.need(source.is_file(),'Missing actual source');common.need(not a.run.exists(),'Fresh run required');a.run.mkdir(parents=True)
    original=source.read_bytes();text=original.decode('ascii');compiler=shutil.which('cc');common.need(compiler is not None,'Compiler unavailable');version=subprocess.run([compiler,'--version'],capture_output=True,text=True);common.need(version.returncode==0,'Compiler identity unavailable')
    compilation=common.compile_library(compiler,source,a.run/'actual.so');actual=exercise(a.run/'actual.so');common.need(actual['mismatches']==0,'Actual C root/twiddle constructor mismatch')
    old='fixed_add(out,work,(work+6ULL),1ULL)';common.need(text.count(old)==1,'Mutation fragment not unique');mutant=a.run/'wrong-real-sign.c';mutant.write_text(text.replace(old,'fixed_add(out,work,(work+6ULL),0ULL)'));negativeCompile=common.compile_library(compiler,mutant,a.run/'wrong-real-sign.so');negative=exercise(a.run/'wrong-real-sign.so');common.need(negative['mismatches']>0,'Wrong source product sign escaped controls');common.need(source.read_bytes()==original,'Original source changed')
    receipt=dict(status='PASS_ACTUAL_C_ROOT_TWIDDLE_RUNTIME_AND_NEGATIVE_CONTROL_NOT_A_PROOF',source=str(source),source_sha256=common.sha(source),validator_sha256=common.sha(Path(__file__)),common_validator_sha256=common.sha(Path(common.__file__)),python_optimization=sys.flags.optimize,seed=SEED,compiler=str(Path(compiler).resolve()),compiler_sha256=common.sha(Path(compiler).resolve()),compiler_version=version.stdout,compilation=compilation,actual=actual,negative_compilation=negativeCompile,negative=negative,seconds=time.monotonic()-begin,owner_defined_source_first_PV_complete=False)
    common.atomic(a.run/'RESULT.json',receipt);print(json.dumps(dict(status=receipt['status'],entries_per_original=[g['entries'] for g in actual['grids']],negative_mismatches=negative['mismatches'])))
if __name__=='__main__':main()
