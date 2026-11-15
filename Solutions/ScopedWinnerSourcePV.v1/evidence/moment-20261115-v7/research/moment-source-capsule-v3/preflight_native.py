"""Actual source/build/run/observed-source canary; not proof acceptance."""
from pathlib import Path
import argparse,subprocess,sys,importlib.util
B=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location("moment_recipe",B/"reproduce.py")
core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core)
def main():
 p=argparse.ArgumentParser();p.add_argument('--environment',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();lock,_,_,_=core.inputs();out=a.out.resolve();core.need(not out.exists()and B not in out.parents,'fresh external canary');out.mkdir(parents=True);environment=core.strict(a.environment);clang=str(Path(environment['compiler']).with_name('clang'));commands=[]
 routes=[['reproduce_numerics.py','--compiler',clang,'--out',str(out/'numerics')],['research/moment-hi-program-v1/reproduce_cpp_v2.py','--compiler',clang,'--baseline',str(out/'numerics/height/run.stdout'),'--out',str(out/'actual-cpp')],['research/moment-hi-program-v1/generate_observation_v1.py','--run',str(out/'actual-cpp'),'--source',str(out/'observed/SynergyMomentCHi/ObservedOutput.lean'),'--receipt',str(out/'OBSERVATION.json')]]
 flags=['-OO']if sys.flags.optimize>=2 else['-O']if sys.flags.optimize else[]
 for route in routes:
  cmd=[sys.executable,*flags,str(B/route[0]),*route[1:]];q=subprocess.run(cmd,check=False);core.need(q.returncode==0,'native canary child');commands.append(cmd)
 target=next(r for r in lock['sources']if r['module']=='SynergyMomentCHi.ObservedOutput');core.need(core.sha(out/'observed/SynergyMomentCHi/ObservedOutput.lean')==target['sha256'],'actual fresh footer reproduces source')
 core.atomic(out/'RECEIPT.json',dict(status='PASS_ACTUAL_NATIVE_SOURCE_LINKER_CRT_RUN_AND_OBSERVED_SOURCE_NOT_PROOF_REPLAY',commands=commands,source_lock_sha256=core.sha(B/'SOURCE_LOCK.json'),observed_source_sha256=target['sha256'],mathematical_acceptance=False))
if __name__=='__main__':main()
