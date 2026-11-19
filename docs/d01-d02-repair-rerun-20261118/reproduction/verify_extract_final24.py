"""Verify the final24 archive exactly; optionally extract only its7303 regular members."""
from pathlib import Path
import argparse,hashlib,json,shutil,tarfile
ARCHIVE_SHA='1da943a15aaebeb949a5ef472e82e97bb0d349d1914f2f0c01fbfe6f08a1de3a'
RECEIPT_SHA='6760619c22f46ce81163d8c7bc74cee6b3cb93dbd92b4720dda32bf6d2762670'
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--archive',type=Path,required=True);p.add_argument('--receipt',type=Path,required=True);p.add_argument('--out',type=Path);a=p.parse_args();need(sha(a.archive)==ARCHIVE_SHA and sha(a.receipt)==RECEIPT_SHA,'exact accepted final24 archive/receipt SHA256');r=json.loads(a.receipt.read_bytes());expected={x['relative_path']:x for x in r['members']};need(len(expected)==len(r['members'])==7303,'complete unique7303 regular member identities');out=None
 if a.out:
  out=a.out.absolute();need(out.resolve()==out and not out.exists()and out.parent.is_dir(),'fresh canonical output with existing parent');need(shutil.disk_usage(out.parent).free>=2*sum(x['bytes']for x in expected.values()),'adequate source-extraction disk (separate from unchanged scientific admission guard)')
 with tarfile.open(a.archive,'r:gz')as t:
  members=t.getmembers();need(len(members)==7303 and all(x.isfile()and not x.issym()and not x.islnk()for x in members),'regular-only exact archive census');seen=set()
  for member in members:
   q=Path(member.name);need(not q.is_absolute()and'..'not in q.parts and q.parts[0]=='source-tree','safe original archive member');relative=str(Path(*q.parts[1:]));need(relative in expected and relative not in seen,'exact unique source identity');seen.add(relative);raw=t.extractfile(member).read();need(len(raw)==expected[relative]['bytes']and hashlib.sha256(raw).hexdigest()==expected[relative]['sha256'],'every original archived source byte')
  need(seen==set(expected),'complete member coverage')
  if out:
   out.mkdir(mode=0o700)
   for member in members:
    relative=str(Path(*Path(member.name).parts[1:]));f=out/relative;f.parent.mkdir(parents=True,exist_ok=True)
    with f.open('xb')as stream:stream.write(t.extractfile(member).read())
    need(f.stat().st_size==expected[relative]['bytes']and sha(f)==expected[relative]['sha256'],'every fresh extracted byte')
   need({str(x.relative_to(out))for x in out.rglob('*')if x.is_file()}==set(expected),'complete fresh physical source membership')
 print(json.dumps({'status':'PASS_EXACT_FINAL24_ARCHIVE'+('_AND_FRESH_EXTRACTION'if out else '_VERIFICATION_ONLY'),'regular_members':7303,'archive_sha256':ARCHIVE_SHA,'source_root':str(out)if out else None,'source_compiler_model_or_scope_calls':0},sort_keys=True))
if __name__=='__main__':main()
