from pathlib import Path
import hashlib,json,os,subprocess,sys,tempfile,time
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[2];E=R/'evidence/final24-actual-final-bundle-reproduction-v1'
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):
 h=hashlib.sha256()
 with p.open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def pin(p):return{'path':str(p),'sha256':sha(p),'bytes':p.stat().st_size}
def fresh(p,value):
 need(not p.exists(),'fresh actual receipt');fd,tmp=tempfile.mkstemp(prefix='.'+p.name+'.',dir=p.parent)
 try:
  with os.fdopen(fd,'w')as f:f.write(json.dumps(value,indent=2)+'\n');f.flush();os.fsync(f.fileno())
  os.link(tmp,p)
 finally:os.unlink(tmp)
def main():
 source=E/'OWNED_ROOT_AND_SOURCE_PINS.json';s=json.loads(source.read_bytes());T=Path(s['fresh_root']);B=Path(s['public_bundle']);need(T.parent==Path('/data')and T.name=='ivy-final24-actual-bundle-repro-ldnkxgks'and T.resolve()==T,'one exact fresh owned root');v=T/'bootstrap/verify_and_reconstruct.py';manifest=T/'bootstrap/PUBLIC_MANIFEST.json';need(sha(v)==s['verifier_sha256']and sha(manifest)==s['manifest_sha256'],'exact approved source manifest and verifier');m=json.loads(manifest.read_bytes());canonical=B/m['archive']['path'];need(sha(canonical)==m['archive']['sha256']=='a332f37373cfe5afb0c5800b5b62fa426671d42c3ed1370dcd26d0d99dca9b3d','actual canonical final archive');records=[]
 for mode in [[],['-O'],['-OO']]:
  label='normal'if not mode else mode[0][1:];archive=T/(label+'.reconstructed.evidence.tar.gz');argv=[sys.executable,'-I','-B',*mode,str(v),'--manifest',str(manifest),'--parts',str(B),'--out',str(archive)]
  if not mode:argv+=['--extract',str(T/'extracted')]
  started=time.monotonic();result=subprocess.run(argv,capture_output=True,text=True);out=E/(label+'.reconstruction.stdout');err=E/(label+'.reconstruction.stderr');need(not out.exists()and not err.exists(),'new actual command logs');out.write_text(result.stdout);err.write_text(result.stderr);need(result.returncode==0 and not result.stderr,'actual unchanged complete verifier must pass');verdict=json.loads(result.stdout);need(verdict['members']==7968 and verdict['archive_sha256']==m['archive']['sha256']and verdict['extracted']==(not mode)and verdict['models_compilers_numerics']==0,'all member/decompressed original checks and one extraction');ap=pin(archive);need(ap['sha256']==sha(canonical)==m['archive']['sha256']and ap['bytes']==m['archive']['bytes']==352175549,'fresh reconstructed bytes exactly equal canonical original');record={'label':label,'argv':argv,'returncode':result.returncode,'elapsed_seconds':time.monotonic()-started,'stdout':pin(out),'stderr':pin(err),'verifier':pin(v),'manifest':pin(manifest),'reconstructed_archive':ap,'canonical_original_archive':pin(canonical),'all7968_members_and_decompressed_original_JSON_verified':True,'extraction_performed':not mode,'new_scientific_or_model_execution':False};before=E/(label+'.ARCHIVE_VERIFIED_BEFORE_REGENERABLE_COPY_REMOVAL.json');fresh(before,record)
  need(archive.parent==T and archive.is_file()and not archive.is_symlink()and pin(archive)==ap,'only unchanged fresh owned duplicate archive removed');archive.unlink();removed={'status':'PASS_ONLY_VERIFIED_FRESH_RECONSTRUCTED_DUPLICATE_ARCHIVE_REMOVED_AFTER_DURABLE_RECEIPT','before_removal_receipt':pin(before),'removed_path':str(archive),'removed_bytes':ap['bytes'],'removed_sha256':ap['sha256'],'canonical_original_unchanged':pin(canonical),'other_paths_deleted':False};after=E/(label+'.VERIFIED_DUPLICATE_ARCHIVE_REMOVAL.json');fresh(after,removed);record['verified_regenerable_duplicate_removal_receipt']=pin(after);records.append(record)
 receipt=E/'ACTUAL_FINAL_BUNDLE_NORMAL_O_OO_RECONSTRUCTION_AND_ONE_EXTRACTION.json';fresh(receipt,{'status':'PASS_ACTUAL_FINAL_BUNDLE_ALL53_PARTS_7968_MEMBERS_AND_RESTORED_JSON_NORMAL_O_OO_ONE_EXTRACTION','source':pin(Path(__file__)),'owned_root_record':pin(source),'canonical_manifest':pin(B/'PUBLIC_MANIFEST.json'),'canonical_archive':pin(canonical),'records':records,'extraction':str(T/'extracted'),'extractions':1,'duplicate_reconstructed_archives_removed_only_after_full_verification':3,'duplicate_archive_bytes_removed':3*352175549,'new_scientific_or_Lean_execution':False});print(json.dumps({'receipt':pin(receipt),'extraction':str(T/'extracted'),'modes':3,'members':7968,'duplicate_archive_bytes_removed':3*352175549}))
if __name__=='__main__':main()
