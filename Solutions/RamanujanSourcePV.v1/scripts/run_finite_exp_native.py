#!/usr/bin/env python3
"""Observe the actual source-bound e functions; formal source proofs are separate."""
from pathlib import Path
import argparse,ctypes,hashlib,json,os,shutil,subprocess,time
S=Path(__file__).resolve().parents[1]
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(out.is_relative_to(Path('/data/ivy-ramanujan-source-pv-20261119'))and not out.exists(),'fresh owned native observation');out.mkdir(parents=True);source=S/'c/verified_finite_exp.c';source_hash=sha(source);compiler=Path(shutil.which('gcc')).resolve();library=out/'libfinite_exp.so';command=[str(compiler),'-std=c11','-O2','-Wall','-Wextra','-Werror','-shared','-fPIC',str(source),'-o',str(library)];start=time.monotonic();r=subprocess.run(command,capture_output=True,text=True);(out/'compiler.stdout').write_text(r.stdout);(out/'compiler.stderr').write_text(r.stderr);need(r.returncode==0,'actual C compilation');need(sha(source)==source_hash,'source unchanged during native compilation');program=ctypes.CDLL(str(library));values={}
 for name in ['rpc_e_low','rpc_e_high']:
  fn=getattr(program,name);fn.restype=ctypes.c_uint64;fn.argtypes=[];values[name]=fn()
 need(values=={'rpc_e_low':3133965575612453533,'rpc_e_high':3133965575612453555},'actual native values match separately proved source outputs');result=dict(status='ACTUAL_C_SOURCE_EXECUTION_OBSERVED_SEPARATE_FORMAL_SOURCE_PROOFS_EXIST',source=str(source),source_sha256=source_hash,compiler=str(compiler),compiler_sha256=sha(compiler),compiler_version=subprocess.check_output([str(compiler),'--version'],text=True).splitlines()[0],command=command,library_sha256=sha(library),values=values,seconds=time.monotonic()-start,formal_roots=['RamanujanPV.FiniteExpSource','RamanujanPV.FiniteExpExecute','RamanujanPV.FiniteExpLinked'],boundary='The ctypes observer/ABI/OS/compiler/hardware are recorded native trust boundaries. The actual C bodies/source identity/typed uint64 execution/call realization/real-e enclosure are separately Lean-proved; this native receipt alone is not PV. C++ generator/caller logic is not verified here.')
 temp=out/'RESULT.json.pending';temp.write_text(json.dumps(result,indent=2)+'\n');temp.replace(out/'RESULT.json');print(json.dumps(result))
if __name__=='__main__':main()
