#!/usr/bin/env python3
"""Actual small bundle build/reassembly/member checks in all Python modes.
Synthetic artifact controls only; no mathematical proof or production bundle.
"""
from pathlib import Path
import argparse,copy,hashlib,io,json,os,shutil,subprocess,sys,tarfile
from verify_bundle import need,sha,read_json
HERE=Path(__file__).resolve().parent

def atomic(p,j):p.write_text(json.dumps(j,indent=2)+'\n')
def main():
 ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--out',required=True,type=Path);a=ap.parse_args()
 need(not os.path.lexists(a.out),'Fresh control directory required');a.out.mkdir(parents=True)
 repo=a.out/'fixture-repo';repo.mkdir();source=repo/'tiny_source.c';source.write_text('int main(void) { return 0; }\n')
 for command in [['git','init','-q'],['git','add','tiny_source.c'],['git','-c','user.name=ArtifactFixture','-c','user.email=fixture@example.invalid','commit','-qm','Small packaging fixture only']]:subprocess.run(command,cwd=repo,check=True)
 commit=subprocess.run(['git','rev-parse','HEAD'],cwd=repo,capture_output=True,text=True,check=True).stdout.strip()
 good=dict(status='PASS_EXACT_REVIEWED_CAMPAIGN_SOURCE_SELECTION',reviewed_commit=commit,current_HEAD=commit,unresolved=[],files=[dict(file=source.name,sha256=sha(source),bytes=source.stat().st_size)],selected_files=1,selected_bytes=source.stat().st_size)
 goodpath=a.out/'source.json';atomic(goodpath,good)
 evsource=a.out/'synthetic-receipt.txt';evsource.write_text('Packaging-control artifact; no scientific acceptance.\n')
 evidence=dict(status='SYNTHETIC_ARTIFACT_CONTROL_ONLY',files=[dict(source=str(evsource),archive_path='evidence/synthetic-receipt.txt',bytes=evsource.stat().st_size,sha256=sha(evsource))]);evpath=a.out/'evidence.json';atomic(evpath,evidence)
 cases=[]
 def run(label,mode,args,ok):
  command=[sys.executable,*mode,*args];r=subprocess.run(command,capture_output=True,text=True)
  need((r.returncode==0)is ok,'Unexpected actual CLI result '+label)
  (a.out/(label+'.stdout')).write_text(r.stdout);(a.out/(label+'.stderr')).write_text(r.stderr)
  cases.append(dict(case=label,command=command,returncode=r.returncode,expected_success=ok,stdout_sha256=sha(a.out/(label+'.stdout')),stderr_sha256=sha(a.out/(label+'.stderr'))))
 for mode,tag in [([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]:
  folder=a.out/tag;folder.mkdir();built=folder/'built'
  base=[str(HERE/'build_bundle.py'),'--repository',str(repo),'--source-manifest',str(goodpath),'--evidence-manifest',str(evpath),'--name','SMALL_CONTROL','--part-bytes','512']
  run(tag+'-build',mode,[*base,'--out',str(built)],True)
  receipt=read_json(built/'BUNDLE_ACCEPTANCE.json');need(receipt['status']=='PASS_EXACT_SOURCE_EVIDENCE_ARCHIVE_PARTS_AND_REASSEMBLY_NOT_MATHEMATICAL_ACCEPTANCE','Missing actual small package gate')
  run(tag+'-reader',mode,[str(HERE/'verify_bundle.py'),'--parts',str(built/'BUNDLE_PARTS.json'),'--out',str(folder/'reassembled.tar.xz'),'--extract',str(folder/'restored')],True)
  need((folder/'restored/repo/tiny_source.c').read_bytes()==source.read_bytes(),'Actual extracted source differs')
  # Build failures must not create acceptance or an output directory.
  for name,change in [('incomplete',lambda j:j.update(status='INCOMPLETE_SOURCE_SELECTION_NO_FINAL_BUNDLE_ACCEPTANCE',unresolved=[{'kind':'pending'}])),('wrong-commit',lambda j:j.update(reviewed_commit='0'*40)),('changed-source-hash',lambda j:j['files'][0].update(sha256='0'*64)),('boolean-size',lambda j:j['files'][0].update(bytes=True)),('duplicate-source',lambda j:(j['files'].append(dict(j['files'][0])),j.update(selected_files=2,selected_bytes=2*source.stat().st_size)))]:
   bad=copy.deepcopy(good);change(bad);path=folder/(name+'.json');atomic(path,bad);dest=folder/(name+'-output')
   run(tag+'-'+name,mode,[str(HERE/'build_bundle.py'),'--repository',str(repo),'--source-manifest',str(path),'--out',str(dest)],False)
   need(not dest.exists(),'Rejected selection created output')
  run(tag+'-part-size-zero',mode,[*base,'--part-bytes','0','--out',str(folder/'zero')],False)
  need(not(folder/'zero').exists(),'Rejected size created output')
  run(tag+'-existing-output',mode,[*base,'--out',str(built)],False)
  run(tag+'-unknown-option',mode,[*base,'--output',str(folder/'unknown')],False)
  # Reader failures occur before reassembly/extraction creates final outputs.
  parts=read_json(built/'BUNDLE_PARTS.json')
  for name,change in [('boolean-index',lambda j:j['parts'][0].update(index=True)),('reverse-order',lambda j:j['parts'].reverse()),('wrong-part-hash',lambda j:j['parts'][0].update(sha256='0'*64)),('wrong-archive-hash',lambda j:j.update(archive_sha256='0'*64))]:
   bad=copy.deepcopy(parts);change(bad);path=built/(name+'.json');atomic(path,bad);dest=folder/(name+'.tar.xz')
   run(tag+'-'+name,mode,[str(HERE/'verify_bundle.py'),'--parts',str(path),'--out',str(dest)],False)
   need(not dest.exists(),'Rejected part inventory created final archive')
  # Repack with changed/unlisted/duplicate/path-invalid members.
  original=built/'SMALL_CONTROL.tar.xz'
  for kind in ['changed-member','extra-member','duplicate-member','invalid-path']:
   altered=folder/(kind+'.tar.xz')
   with tarfile.open(original,'r:xz')as src,tarfile.open(altered,'w:xz')as dst:
    for member in src.getmembers():
     data=src.extractfile(member).read()
     if kind=='changed-member'and member.name=='repo/tiny_source.c':data=b'X'+data[1:]
     dst.addfile(member,io.BytesIO(data))
    if kind!='changed-member':
     name={'extra-member':'extra.txt','duplicate-member':'repo/tiny_source.c','invalid-path':'../outside.txt'}[kind];extra=tarfile.TarInfo(name);extra.size=1;dst.addfile(extra,io.BytesIO(b'X'))
   extract=folder/(kind+'-extract')
   run(tag+'-'+kind,mode,[str(HERE/'verify_bundle.py'),'--archive',str(altered),'--extract',str(extract)],False)
   need(not extract.exists(),'Rejected archive created extraction tree')
 atomic(a.out/'RESULT.json',dict(status='PASS_SMALL_ACTUAL_BUNDLE_BUILDER_READER_ALL_PYTHON_MODES',cases=cases,positive=sum(r['expected_success']for r in cases),negative=sum(not r['expected_success']for r in cases),source_files={p.name:sha(p)for p in [HERE/'build_bundle.py',HERE/'verify_bundle.py',Path(__file__)]},heavy_job=False,production_bundle_created=False,mathematical_proof_or_PV_acceptance=False))
 print('PASS small actual bundle CLI controls: '+str(len(cases)))
if __name__=='__main__':main()
