#!/usr/bin/env python3
"""Build an exact, reproducible source/evidence archive after source-review gates.
Packaging verifies bytes; it creates no mathematical or source-first PV approval.
No directory recursion or implicit evidence selection is performed.
"""
from __future__ import annotations
import argparse,hashlib,io,json,lzma,os,re,shutil,stat,subprocess,sys,tarfile,time
from pathlib import Path,PurePosixPath
from verify_bundle import need,read_json,sha,member_path,verify_archive,reassemble
HERE=Path(__file__).resolve().parent
SOURCE_STATUS='PASS_EXACT_REVIEWED_CAMPAIGN_SOURCE_SELECTION'

def encoded(j):return(json.dumps(j,indent=2,sort_keys=True,ensure_ascii=False)+'\n').encode()
def atomic(p,j):
 temporary=p.with_suffix(p.suffix+'.pending');temporary.write_bytes(encoded(j));os.replace(temporary,p)
def admitted_name(name):
 member_path(name)
 # This is an explicit artifact allowlist, never a workspace dump.
 lowered=name.lower();parts=PurePosixPath(name).parts
 need(not any(x in ['.git','__pycache__','node_modules','memory','human_input']for x in parts),'Private/cache path cannot be bundled')
 need(not any(x in lowered for x in ['transcript','sdk_response','runtime_event','upload_reply_verified','directives_inbox']),'Private session material cannot be bundled')
 return name

def main():
 ap=argparse.ArgumentParser(allow_abbrev=False)
 ap.add_argument('--repository',required=True,type=Path);ap.add_argument('--source-manifest',required=True,type=Path)
 ap.add_argument('--evidence-manifest',action='append',type=Path,default=[])
 ap.add_argument('--supplement',action='append',default=[],metavar='NAME=PATH')
 ap.add_argument('--out',required=True,type=Path);ap.add_argument('--name',default='RH080_NEXT_REPRODUCIBLE_BUNDLE')
 ap.add_argument('--part-bytes',type=int,default=8000000)
 a=ap.parse_args();need(not os.path.lexists(a.out),'Fresh bundle output directory required')
 need(re.fullmatch(r'[A-Za-z0-9_-]+',a.name)is not None,'Plain artifact name required')
 need(1<=a.part_bytes<=8000000,'Parts must be at most8000000bytes')
 repository=a.repository.resolve(strict=True);source=read_json(a.source_manifest)
 need(source.get('status')==SOURCE_STATUS and source.get('unresolved')==[],'Reviewed complete source selection required')
 commit=source.get('reviewed_commit');need(type(commit)is str and re.fullmatch('[0-9a-f]{40}',commit)is not None,'Exact reviewed Git commit required')
 git=subprocess.run(['git','rev-parse','HEAD'],cwd=repository,capture_output=True,text=True)
 need(git.returncode==0 and git.stdout.strip()==commit==source.get('current_HEAD'),'Source review is not the current committed revision')
 files=source['files'];need(type(files)is list and type(source.get('selected_files'))is int and len(files)==source['selected_files'],'Selected source population differs')
 need(type(source.get('selected_bytes'))is int and sum(r['bytes']for r in files)==source['selected_bytes'],'Selected source byte total differs')
 entries={};paths={}
 def add(name,path=None,data=None,digest=None,size=None):
  admitted_name(name);need(name not in entries,'Duplicate archive destination: '+name)
  need((path is None)!=(data is None),'Exactly one source representation required')
  if path is not None:
   path=Path(path);need(path.is_file()and not path.is_symlink(),'Explicit regular source file required: '+str(path))
   st=path.stat();need(type(size)is int and st.st_size==size and sha(path)==digest,'Selected artifact bytes changed: '+str(path))
   entries[name]=dict(path=name,sha256=digest,bytes=size,mode=0o755 if st.st_mode&0o111 else 0o644);paths[name]=path
  else:
   need(type(data)is bytes,'Exact generated metadata bytes required');entries[name]=dict(path=name,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),mode=0o644);paths[name]=data
 for row in files:
  rel=row['file'];member_path(rel);p=repository.joinpath(*PurePosixPath(rel).parts)
  need(p.resolve().is_relative_to(repository),'Selected source resolves outside repository')
  add('repo/'+rel,path=p,digest=row['sha256'],size=row['bytes'])
 add('metadata/SOURCE_BUNDLE_MANIFEST.json',data=a.source_manifest.read_bytes())
 for index,manifest in enumerate(a.evidence_manifest,1):
  evidence=read_json(manifest);rows=evidence['files'];need(type(rows)is list,'Exact evidence-file list required')
  for row in rows:
   name=row['archive_path'];need(name.startswith('evidence/'),'Evidence must have explicit evidence/ destination')
   add(name,path=Path(row['source']),digest=row['sha256'],size=row['bytes'])
  add('metadata/EVIDENCE_MANIFEST_'+str(index)+'.json',data=manifest.read_bytes())
 for supplement in a.supplement:
  need('='in supplement,'Supplement requires NAME=PATH');name,path=supplement.split('=',1);p=Path(path)
  need(not name.lower().endswith(('.html','.htm')),'The single HTML reading report is delivered separately')
  add('supplement/'+name,path=p,digest=sha(p),size=p.stat().st_size)
 # Include the exact offline reader without adding a self-referential source commit.
 add('verify_bundle.py',path=HERE/'verify_bundle.py',digest=sha(HERE/'verify_bundle.py'),size=(HERE/'verify_bundle.py').stat().st_size)
 readme=('RH080 source/evidence bundle\n\nReviewed source commit: '+commit+'\n\n'
  'Sources are under repo/. Start with repo/Solutions/RH080Next.v1/reproduction/README.md.\n'
  'The exact source selector records the included mathematical/program closure and exclusions.\n'
  'Pinned generic dependencies are fetched by the bootstrap script; no application object cache is required.\n'
  'Large deterministic numerical data are regenerated from source and checked against exact inventories.\n'
  'Evidence and source inventories are separate. A receipt is not itself a mathematical proof.\n'
  'Original timed-study outcomes and trust boundaries remain as recorded in the report.\n'
  'Use python3 verify_bundle.py --archive ARCHIVE --extract FRESH_DIRECTORY to verify/extract.\n'
  'For split parts use python3 verify_bundle.py --parts BUNDLE_PARTS.json --out bundle.tar.xz --extract FRESH_DIRECTORY.\n')
 add('REPRODUCE_README.txt',data=readme.encode())
 inventory=dict(status='EXACT_ARCHIVE_MEMBER_BYTE_INVENTORY_NOT_MATHEMATICAL_ACCEPTANCE',reviewed_source_commit=commit,files=[entries[k]for k in sorted(entries)],manifest_itself_excluded_from_its_hash_inventory=True,source_selection_sha256=sha(a.source_manifest),explicit_evidence_manifest_sha256=[sha(p)for p in a.evidence_manifest],mathematical_proof_acceptance=False)
 manifest_bytes=encoded(inventory);a.out.mkdir(parents=True);archive=a.out/(a.name+'.tar.xz');started=time.monotonic()
 try:
  with tarfile.open(archive,'w:xz',preset=6,format=tarfile.PAX_FORMAT)as tar:
   for name in ['MANIFEST.json',*sorted(entries)]:
    value=manifest_bytes if name=='MANIFEST.json'else paths[name];data=value if isinstance(value,bytes)else None
    info=tarfile.TarInfo(name);info.size=len(data)if data is not None else entries[name]['bytes'];info.mode=0o644 if name=='MANIFEST.json'else entries[name]['mode'];info.mtime=0;info.uid=info.gid=0;info.uname=info.gname=''
    if data is not None:tar.addfile(info,io.BytesIO(data))
    else:
     with value.open('rb')as stream:tar.addfile(info,stream)
  checked=verify_archive(archive);digest=sha(archive);parts=[]
  with archive.open('rb')as stream:
   index=1
   while chunk:=stream.read(a.part_bytes):
    name=a.name+'.tar.xz.part-'+str(index).zfill(3);p=a.out/name;p.write_bytes(chunk)
    parts.append(dict(index=index,file=name,bytes=len(chunk),sha256=sha(p)));index+=1
  part_manifest=dict(status='EXACT_REPRODUCIBLE_BUNDLE_PART_INVENTORY_NOT_MATHEMATICAL_ACCEPTANCE',archive_file=archive.name,archive_bytes=archive.stat().st_size,archive_sha256=digest,parts=parts,member_manifest_sha256=hashlib.sha256(manifest_bytes).hexdigest(),reviewed_source_commit=commit,mathematical_proof_acceptance=False)
  atomic(a.out/'BUNDLE_PARTS.json',part_manifest)
  shutil.copyfile(HERE/'verify_bundle.py',a.out/'verify_bundle.py')
  # Independently exercise the delivered reassembly path before any success receipt.
  reassembled=a.out/'SELF_CHECK_REASSEMBLED.tar.xz';reassemble(a.out/'BUNDLE_PARTS.json',reassembled);check2=verify_archive(reassembled,digest);reassembled.unlink()
  receipt=dict(status='PASS_EXACT_SOURCE_EVIDENCE_ARCHIVE_PARTS_AND_REASSEMBLY_NOT_MATHEMATICAL_ACCEPTANCE',reviewed_source_commit=commit,source_selection_sha256=sha(a.source_manifest),member_manifest_sha256=hashlib.sha256(manifest_bytes).hexdigest(),files=len(entries),source_files=len(files),source_bytes=source['selected_bytes'],archive_sha256=digest,archive_bytes=archive.stat().st_size,parts=len(parts),part_manifest_sha256=sha(a.out/'BUNDLE_PARTS.json'),reader_sha256=sha(HERE/'verify_bundle.py'),builder_sha256=sha(Path(__file__)),python=sys.version,compression='stdlib lzma XZ preset6; deterministic tar uid/gid/mtime/order',tarfile_source_sha256=sha(Path(tarfile.__file__)),seconds=time.monotonic()-started,first_archive_check=checked,delivered_reader_reassembly_check=check2,cleanup_performed=False,mathematical_proof_acceptance=False)
  atomic(a.out/'BUNDLE_ACCEPTANCE.json',receipt);print(json.dumps({k:receipt[k]for k in ['status','files','archive_bytes','parts','seconds']},sort_keys=True))
 except BaseException as error:
  atomic(a.out/'BUNDLE_FAILURE.json',dict(status='NO_BUNDLE_ACCEPTANCE',error=type(error).__name__+': '+str(error),seconds=time.monotonic()-started));raise
if __name__=='__main__':main()
