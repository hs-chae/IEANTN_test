#!/usr/bin/env python3
"""Run actual pi-replayer preflights and rejection CLIs in all Python modes."""
from pathlib import Path
import argparse,hashlib,json,os,shutil,subprocess,sys
S=Path(__file__).resolve().parents[1];N=S.parents[1]
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
 out=a.out.resolve();need(not out.exists(),'fresh output required');out.mkdir(parents=True)
 fixture=out/'fixture/network';sub=fixture/'Solutions/RHLimit.v1';sub.mkdir(parents=True)
 manifest=S/'pi/SOURCE_CLOSURE.json';m=json.loads(manifest.read_text());paths=[N/r['path']for r in m['modules']]
 paths += [S/'pi/RESOURCES.json',S/'pi/frozen-source/c/verified_finite_log.c',manifest,S/'scripts/reproduce_pi_complete.py',N/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json']
 copied=[]
 for f in paths:
  q=fixture/f.relative_to(N);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(f,q);copied.append({'path':str(q.relative_to(fixture)),'sha256':sha(q),'bytes':q.stat().st_size})
 script=sub/'scripts/reproduce_pi_complete.py';pin=sub/'pi/SOURCE_CLOSURE.json';original=pin.read_bytes()
 changed=fixture/m['modules'][-1]['path'];source=changed.read_bytes();records=[]
 payload=sub/'pi/frozen-source/c/verified_finite_log.c';original_c=payload.read_bytes()
 for mode in [0,1,2]:
  flags=[]if mode==0 else['-O']if mode==1 else['-OO']
  for case in ['positive','unknown_flag','duplicate_json','nonfinite_json','changed_source','changed_resource','existing_output']:
   pin.write_bytes(original);changed.write_bytes(source);payload.write_bytes(original_c)
   output=out/f'not_created_{mode}_{case}'
   extra=[]
   if case=='duplicate_json':pin.write_text('{"modules":[],"modules":[]}')
   if case=='nonfinite_json':pin.write_text('{"modules":1e999}')
   if case=='changed_source':changed.write_bytes(source+b'\n-- intentional source identity rejection\n')
   if case=='changed_resource':payload.write_bytes(original_c+b'\n')
   if case=='unknown_flag':extra=['--nonexistent-option']
   if case=='existing_output':output.mkdir()
   cmd=[sys.executable,*flags,str(script),'--out',str(output),'--check',*extra]
   r=subprocess.run(cmd,capture_output=True,text=True);positive=case=='positive'
   need((r.returncode==0)==positive,'wrong CLI result:'+str((mode,case)))
   need(not(output/'RESULT.json').exists(),'preflight wrote acceptance receipt')
   if output.exists():need(case=='existing_output'and not list(output.iterdir()),'failed CLI changed output')
   (out/f'{mode}-{case}.stdout').write_text(r.stdout);(out/f'{mode}-{case}.stderr').write_text(r.stderr)
   records.append({'optimization':mode,'case':case,'command':cmd,'returncode':r.returncode,'expected':'preflight_only'if positive else'rejected'})
 pin.write_bytes(original);changed.write_bytes(source);payload.write_bytes(original_c)
 # Verify the exact private fixture membership and bytes before removing copies.
 actual={str(x.relative_to(fixture))for x in fixture.rglob('*')if x.is_file()}
 need(actual=={r['path']for r in copied},'fixture membership changed')
 for r in copied:need(sha(fixture/r['path'])==r['sha256'],'fixture source drift')
 preview={'owned_root':str(fixture),'files':copied,'bytes':sum(r['bytes']for r in copied)}
 (out/'CLEANUP_PREVIEW.json').write_text(json.dumps(preview,indent=2)+'\n')
 shutil.rmtree(out/'fixture')
 need(not(out/'fixture').exists(),'fixture cleanup incomplete')
 result={'status':'PASS_ACTUAL_PI_CLI_ALL_OPTIMIZATION_MODES','validator_sha256':sha(S/'scripts/reproduce_pi_complete.py'),'controller_sha256':sha(__file__),'source_manifest_sha256':sha(manifest),'cases':records,'positive_preflights':3,'rejections':18,'fresh_acceptance_receipts_written':0,'mathematical_build_repeated':False,'verified_regenerable_fixture_bytes_removed':preview['bytes']}
 pending=out/'RESULT.pending.json';pending.write_text(json.dumps(result,indent=2)+'\n');os.replace(pending,out/'RESULT.json');print(result['status'])
if __name__=='__main__':main()
