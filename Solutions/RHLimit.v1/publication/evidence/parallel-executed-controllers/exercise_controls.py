#!/usr/bin/env python3
"""Actual toy archive/parts CLIs and final-ready rejection gates in all modes.

No real research tree is frozen, archived or published by these controls.
"""
from pathlib import Path
import argparse,hashlib,io,json,os,subprocess,sys,tarfile
sys.dont_write_bytecode=True
from prepare_bundle import need,strict,save,sha
B=Path(__file__).resolve().parent

def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();out=a.out.resolve();need(not out.exists(),'fresh controls output');out.mkdir(parents=True);rows=[]
 frozen=out/'executed-controllers';frozen.mkdir();tools=['prepare_bundle.py','archive_tools.py','join_bundle.py','REPRODUCE_RH_LIMIT.py','FETCH_GENERIC_SOURCES.py','run_replay_bounded.py','exercise_controls.py'];before={}
 for name in tools:
  raw=(B/name).read_bytes();(frozen/name).write_bytes(raw);before[name]=sha(B/name)
 def cli(mode,tool,label,args,good):
  flags=[]if mode==0 else['-O']if mode==1 else['-OO'];cmd=[sys.executable,*flags,str(B/tool),*args];r=subprocess.run(cmd,text=True,capture_output=True)
  rows.append({'mode':mode,'label':label,'command':cmd,'returncode':r.returncode,'expected_success':good,'stdout':r.stdout,'stderr':r.stderr});save(out/'PARTIAL.json',{'rows':rows});need((r.returncode==0)==good,'unexpected CLI result:'+label)
 for mode in [0,1,2]:
  root=out/str(mode);root.mkdir();tree=root/'toy';tree.mkdir();(tree/'source.txt').write_text('Deterministic toy source.\n')
  cli(mode,'archive_tools.py','seal-toy',['seal','--tree',str(tree)],True)
  cli(mode,'prepare_bundle.py','verify-toy',['verify','--tree',str(tree)],True)
  archive=root/'TOY.tar.gz';cli(mode,'archive_tools.py','pack-toy',['pack','--tree',str(tree),'--out',str(archive)],True)
  extracted=root/'extracted';cli(mode,'prepare_bundle.py','extract-toy',['extract','--archive',str(archive),'--out',str(extracted)],True)
  parts=root/'parts';cli(mode,'join_bundle.py','split-toy',['--split',str(archive),'--out',str(parts),'--part-bytes','64'],True)
  cli(mode,'join_bundle.py','check-toy-parts',['--parts-dir',str(parts),'--check'],True)
  extractor=parts/'archive_tools.py';old_extractor=extractor.read_bytes();extractor.write_bytes(b'changed');cli(mode,'join_bundle.py','reject-corrupt-extraction-helper',['--parts-dir',str(parts),'--check'],False);extractor.write_bytes(old_extractor)
  joined=root/'joined.tar.gz';cli(mode,'join_bundle.py','join-toy',['--parts-dir',str(parts),'--out',str(joined)],True);need(sha(joined)==sha(archive),'joined bytes differ')
  extra=parts/'RH_LIMIT_SOURCE.part999';extra.write_bytes(b'extra');cli(mode,'join_bundle.py','reject-extra-part',['--parts-dir',str(parts),'--check'],False);extra.unlink()
  first=parts/'RH_LIMIT_SOURCE.part001';original=first.read_bytes();first.write_bytes(b'x'+original[1:]);cli(mode,'join_bundle.py','reject-corrupt-part',['--parts-dir',str(parts),'--check'],False);first.write_bytes(original)
  cli(mode,'join_bundle.py','reject-existing-join-output',['--parts-dir',str(parts),'--out',str(joined)],False)
  cli(mode,'join_bundle.py','reject-oversized-parts',['--split',str(archive),'--out',str(root/'oversized'),'--part-bytes',str(6*1024*1024+1)],False)
  cli(mode,'prepare_bundle.py','reject-no-final-ready',['pack','--tree',str(tree),'--out',str(root/'not-approved.tar.gz')],False)
  bad=root/'bad';bad.mkdir();(bad/'BUNDLE_MANIFEST.json').write_text('{"schema":"x","schema":"STRICT_RELATIVE_FILE_HASH_MANIFEST_V1","files":[]}');cli(mode,'prepare_bundle.py','reject-duplicate-JSON',['verify','--tree',str(bad)],False)
  (bad/'BUNDLE_MANIFEST.json').write_text('{"schema":"STRICT_RELATIVE_FILE_HASH_MANIFEST_V1","files":[],"overflow":1e999}');cli(mode,'prepare_bundle.py','reject-overflowing-JSON',['verify','--tree',str(bad)],False)
  (tree/'source.txt').write_text('changed\n');cli(mode,'prepare_bundle.py','reject-changed-source',['verify','--tree',str(tree)],False)
  (tree/'source.txt').write_text('Deterministic toy source.\n');(tree/'unlisted.txt').write_text('extra');cli(mode,'prepare_bundle.py','reject-extra-member',['verify','--tree',str(tree)],False)
  for label,members in {'parent':[('../x','file')],'absolute':[('/x','file')],'duplicate':[('x','file'),('x','file')],'link':[('x','link')],'prefix':[('x','file'),('x/y','file')],'noncanonical':[('a/../x','file')]}.items():
   malformed=root/(label+'.tar.gz')
   with tarfile.open(malformed,'w:gz')as tf:
    content=b'{}';info=tarfile.TarInfo('BUNDLE_MANIFEST.json');info.size=len(content);tf.addfile(info,io.BytesIO(content))
    for name,kind in members:
     info=tarfile.TarInfo(name)
     if kind=='link':info.type=tarfile.SYMTYPE;info.linkname='elsewhere';tf.addfile(info)
     else:info.size=len(content);tf.addfile(info,io.BytesIO(content))
   target=root/('invalid-'+label);cli(mode,'prepare_bundle.py','reject-invalid-member-'+label,['extract','--archive',str(malformed),'--out',str(target)],False);need(not target.exists(),'invalid archive wrote before member validation')
  plan=root/'plan.json';plan.write_text(json.dumps({'schema':'RH_LIMIT_SOURCE_BUNDLE_PLAN_V1','status':'DRAFT_SOURCE_PLAN_NOT_FROZEN','prior_archive_sha256':'4788c7dda3939a0c1dc5f7d7dbeddc87eb68d95036aa0d13d7027c5371734140','files':[]}));ready=root/'ready.json';ready.write_text('{"schema":"RH_LIMIT_ROOT_FINAL_READY_V1","status":"NOT_READY"}')
  target=root/'research-must-not-stage';cli(mode,'prepare_bundle.py','reject-nonready-freeze',['freeze','--plan',str(plan),'--ready',str(ready),'--out',str(target)],False);need(not target.exists(),'nonready source tree was staged')
  ready.write_text(json.dumps({'schema':'RH_LIMIT_ROOT_FINAL_READY_V1','status':'ROOT_FINAL_READY','approved_plan_sha256':'0'*64}));cli(mode,'prepare_bundle.py','reject-wrong-root-plan-hash',['freeze','--plan',str(plan),'--ready',str(ready),'--out',str(target)],False);need(not target.exists(),'unapproved plan was staged')
  for tool,args in [('prepare_bundle.py',['freeze']),('prepare_bundle.py',['plan']),('join_bundle.py',[]),('REPRODUCE_RH_LIMIT.py',[])]:cli(mode,tool,'reject-missing-active-CLI-arguments-'+tool,args,False)
  cli(mode,'prepare_bundle.py','reject-unknown-option',['plan','--unexpected'],False)
  record=root/'bounded';cli(mode,'run_replay_bounded.py','tiny-bounded-process',['--record',str(record),'--limit-gib','80','--group-gib','240','--wall-seconds','30','--',sys.executable,'-c','print(123)'],True)
  bounded=strict(record/'RESULT.json');need(bounded['returncode']==0 and bounded['aggregate_new_study_limit_bytes']==240*1024**3 and bounded['per_process_address_limit_bytes']==80*1024**3,'separate group/process resource limits')
  cli(mode,'run_replay_bounded.py','reject-group-over240',['--record',str(root/'must-not-run'),'--group-gib','241','--',sys.executable,'-c','print(123)'],False)
  toy=root/'orchestrator';cli(mode,'REPRODUCE_RH_LIMIT.py','toy-orchestrator-concurrency-dependencies-and-failures',['--self-test','--out',str(toy)],True)
  toy_result=strict(toy/'TOY_RESULT.json');need(toy_result['status']=='PASS_TOY_PARALLEL_SERIAL_FAILURE_AND_MEMORY_CONTROLS'and toy_result['mathematical_replay_performed']is False and len(toy_result['cases'])==6,'toy scheduler acceptance identity')
  cli(mode,'REPRODUCE_RH_LIMIT.py','reject-toy-with-production-context',['--self-test','--context',str(root/'never-used'),'--out',str(root/'must-not-launch')],False)
  cli(mode,'REPRODUCE_RH_LIMIT.py','reject-ambiguous-toy-serial',['--self-test','--serial','--out',str(root/'must-not-launch-serial')],False)
 for name in tools:need(sha(B/name)==before[name]==sha(frozen/name),'controller changed during controls')
 result={'schema':'RH_LIMIT_PUBLICATION_TOY_CONTROLS_V1','status':'PASS_ALL_TOY_ARCHIVE_PARTS_AND_READY_GATES_NORMAL_O_OO','real_study_frozen_or_archived':False,'cases':len(rows),'controller_sha256':sha(Path(__file__)),'tools_sha256':{n:sha(B/n)for n in ['prepare_bundle.py','archive_tools.py','join_bundle.py','REPRODUCE_RH_LIMIT.py']},'results':rows};save(out/'RESULT.json',result);print(json.dumps({'status':result['status'],'cases':len(rows)}))
if __name__=='__main__':main()
