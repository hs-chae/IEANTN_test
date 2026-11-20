#!/usr/bin/env python3
"""Ordinary native observer; not acceptance of a Lean/source-PV claim."""
from pathlib import Path
import argparse,ctypes,hashlib,json,re,resource,shutil,subprocess,time
S=Path(__file__).resolve().parents[1]
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False)
 p.add_argument('--out',type=Path,required=True);p.add_argument('--rows-source',type=Path,required=True);p.add_argument('--rows-sha256',required=True)
 p.add_argument('--context',type=Path,default=S/'BUILD_CONTEXT.json');a=p.parse_args();out=a.out.resolve();need(out.is_relative_to(Path(json.loads(a.context.read_text())['new_application_object_root']).resolve().parent)and not out.exists(),'fresh experiment-owned output required')
 need(re.fullmatch('[0-9a-f]{64}',a.rows_sha256)is not None,'exact SHA256 required');need(sha(a.rows_source)==a.rows_sha256,'original row source hash mismatch')
 lines=a.rows_source.read_text().splitlines();definitions=[v for v in lines if v.startswith('noncomputable def rows : ')]
 need(len(definitions)==1,'one actual row array definition required')
 rows=[[int(v)for v in m.split(',')]for m in re.findall(r'\.leaf ⟨([0-9,]+)⟩',definitions[0])]
 need(len(rows)==285 and all(len(v)==7 for v in rows),'exact285 seven-field locked rows required');need(rows[0][0]==38358837683 and rows[-1][1]==38359837684,'locked million-window endpoints')
 sources=[S/'c'/n for n in ['verified_finite_exp.c','verified_finite_log.c','verified_finite_cell.c']];pins={str(v):sha(v)for v in sources}
 out.mkdir(parents=True);compiler=Path(shutil.which('gcc')).resolve();library=out/'libfinite_scalars.so';command=[str(compiler),'-std=c11','-O2','-Wall','-Wextra','-Werror','-Wno-empty-body','-shared','-fPIC',str(sources[-1]),'-o',str(library)]
 started=time.monotonic();proc=subprocess.run(command,capture_output=True,text=True);(out/'compiler.stdout').write_text(proc.stdout);(out/'compiler.stderr').write_text(proc.stderr);need(proc.returncode==0,'actual C compilation failed');need(all(sha(v)==pins[str(v)]for v in sources),'source changed during native compilation')
 lib=ctypes.CDLL(str(library));log=lib.rpc_log_upper;log.argtypes=[ctypes.c_uint64];log.restype=ctypes.c_uint64;cell=lib.rpc_finite_cell;cell.argtypes=[ctypes.c_uint64]*7;cell.restype=ctypes.c_int
 lo=lib.rpc_e_low;lo.argtypes=[];lo.restype=ctypes.c_uint64;hi=lib.rpc_e_high;hi.argtypes=[];hi.restype=ctypes.c_uint64
 need(lo()==3133965575612453533 and hi()==3133965575612453555,'native e outputs differ from separate formal source execution')
 observed=[]
 for i,row in enumerate(rows):
  got=log(row[0]);accepted=cell(*row);need(got==row[5]and accepted==1,f'actual row{i} source output mismatch');observed.append({'index':i,'n':row[0],'Lu':got,'cell_result':accepted})
 (out/'OUTPUTS.json').write_text(json.dumps(observed,separators=(',',':'))+'\n')
 result=dict(schema='RAMANUJAN_FINITE_SCALAR_NATIVE_OBSERVATION_V1',observer_sha256=sha(__file__),context=str(a.context.resolve()),context_sha256=sha(a.context),status='OBSERVED_ACTUAL_C_NUMERICAL_PROGRAM_NOT_FORMAL_PV_ACCEPTANCE',sources=pins,rows_source=str(a.rows_source.resolve()),rows_sha256=a.rows_sha256,rows=285,algorithm={'F':1<<60,'log_output_scale':1<<40,'terms':20,'tail_factor':41,'seven_fields':['n','next','j','P','Q','Lu','A']},command=command,compiler=str(compiler),compiler_sha256=sha(compiler),compiler_version=subprocess.check_output([str(compiler),'--version'],text=True).splitlines()[0],library_sha256=sha(library),outputs_sha256=sha(out/'OUTPUTS.json'),seconds=time.monotonic()-started,observer_peak_RSS_KiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,compiler_children_peak_RSS_KiB=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,disk_bytes=sum(v.stat().st_size for v in out.iterdir()if v.is_file()),trust='Ordinary GCC/ctypes/ABI/OS/hardware observation. Source identity, typed execution and mathematical consumption require separate Lean proofs; this observer is not a source-first PV theorem. The C++ adaptive generator and caller remain unverified.')
 (out/'RESULT.json.pending').write_text(json.dumps(result,indent=2)+'\n');(out/'RESULT.json.pending').replace(out/'RESULT.json');print(json.dumps(result))
if __name__=='__main__':main()
