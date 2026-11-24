#!/usr/bin/env python3
"""Actual606b/source-comparison acceptance CLI in normal/-O/-OO; owned copy mutations only."""
from pathlib import Path
import argparse,json,hashlib,subprocess,shutil,sys,os
H=Path(__file__).resolve().parent
def need(b,s):
 if not b:raise ValueError(s)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--run',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh controls');out.mkdir(parents=True);clone=out/'mutant';shutil.copytree(a.run,clone,symlinks=True);rows=[]
 def cli(name,want):
  for mode in [[],['-O'],['-OO']]:
   cmd=[sys.executable,*mode,str(H/'reproduce.py'),'--verify',str(clone)];q=subprocess.run(cmd,capture_output=True,text=True);tag=str(len(rows))+'-'+name+'-O'+str(len(mode)and len(mode[0])-1);so=out/(tag+'.stdout');se=out/(tag+'.stderr');so.write_text(q.stdout);se.write_text(q.stderr);need((q.returncode==0)==want,'wrong actual acceptance outcome:'+tag);rows.append({'case':name,'mode':mode,'command':cmd,'returncode':q.returncode,'expected_accept':want,'stdout_sha256':sha(so),'stderr_sha256':sha(se)});(out/'PROGRESS.json').write_text(json.dumps({'completed_cases':len(rows),'last':name},indent=2)+'\n')
 cli('regular-relocated-copy',True);m=json.loads((clone/'SOURCE_CLOSURE.executed.json').read_text());mod=m['modules'][0]['module'];rel=mod.replace('.','/');targets=[clone/'source'/(rel+'.lean'),clone/'objects'/(rel+'.olean'),clone/'logs'/(mod+'.stdout'),clone/'logs'/(mod+'.stderr'),clone/'reproduce.executed.py',clone/'SOURCE_CLOSURE.executed.json',clone/'TREE_RSS.csv']
 for f in targets:
  need(f.resolve().is_relative_to(clone)and not f.is_symlink(),'owned mutation');old=f.read_bytes();f.write_bytes(old+b'\nMUTATION\n')
  try:cli('bytes-'+f.name,False)
  finally:f.write_bytes(old)
 original=(clone/'RESULT.json').read_bytes()
 for case in ['missing-probe','boolean-probe','nonzero-probe','wrong-probe-command','foreign-application','false-PV','wrong-total','missing-body-root','missing-new-combined-root','empty-new-inventory','missing-declared-import','missing-comparison-root','float-census']:
  rr=json.loads(original);restore=None
  if case=='float-census':rr['fresh_scientific_modules']=float(rr['fresh_scientific_modules'])
  elif case=='missing-probe':rr['dependency_probes'].pop()
  elif case=='boolean-probe':rr['dependency_probes'][0]['returncode']=False
  elif case=='nonzero-probe':rr['dependency_probes'][0]['returncode']=1
  elif case=='wrong-probe-command':rr['dependency_probes'][0]['command']=['false']
  elif case=='false-PV':rr['source_first_PV_claim']=True
  elif case=='wrong-total':rr['total_source_modules']-=1
  elif case in ['missing-body-root','missing-new-combined-root','empty-new-inventory','missing-declared-import','missing-comparison-root','float-census']:
   f=clone/'logs/FinalRam606Audit.stdout';restore=(f,f.read_bytes());ls=f.read_text().splitlines();target='actual_both_sign_inverse_lower' if case=='missing-comparison-root' else ('fully_derived_spectral_ramanujan' if case=='missing-new-combined-root' else 'fully_derived_box_network');f.write_text('\n'.join(l for l in ls if not('RH_RAM606_FINAL_BODY {'in l and target in l))+'\n');build=json.loads((clone/'BUILD.json').read_text());oldbuild=(clone/'BUILD.json').read_bytes();build['modules'][-1]['stdout_sha256']=sha(f);(clone/'BUILD.json').write_text(json.dumps(build,indent=2)+'\n');rr['BUILD_sha256']=sha(clone/'BUILD.json')
  elif case in ['empty-new-inventory','missing-declared-import']:
   q=rr['dependency_probes'][0];f=clone/'dependencies'/q['stdout'];restore=(f,f.read_bytes())
   if case=='empty-new-inventory':f.write_bytes(b'')
   else:
    needle='/'+m['modules'][0]['application_imports'][0].replace('.','/')+'.olean';oldlines=f.read_text().splitlines();newlines=[x for x in oldlines if not x.endswith(needle)];need(newlines and newlines!=oldlines,'remove actual declared app import');f.write_text('\n'.join(newlines)+'\n')
   q['stdout_sha256']=sha(f)
  else:
   q=rr['dependency_probes'][0];f=clone/'dependencies'/q['stdout'];restore=(f,f.read_bytes());f.write_bytes(f.read_bytes()+b'/tmp/foreign-application.olean\n');q['stdout_sha256']=sha(f)
  (clone/'RESULT.json').write_text(json.dumps(rr,indent=2)+'\n')
  try:cli(case,False)
  finally:
   (clone/'RESULT.json').write_bytes(original)
   if restore:restore[0].write_bytes(restore[1])
   if case in ['missing-body-root','missing-new-combined-root','empty-new-inventory','missing-declared-import','missing-comparison-root','float-census']:(clone/'BUILD.json').write_bytes(oldbuild)
 cli('restored',True);rr={'status':'PASS_ACTUAL_RAM606_CLI_CONTROLS_ALL_MODES','cases':len(rows),'controller_sha256':sha(H/'reproduce.py'),'control_source_sha256':sha(Path(__file__)),'accepted_run_RESULT_sha256':sha(a.run/'RESULT.json'),'rows':rows};candidate=out/'CANDIDATE.json';candidate.write_text(json.dumps(rr,indent=2)+'\n');os.replace(candidate,out/'RESULT.json');print(rr['status'],len(rows))
if __name__=='__main__':main()
