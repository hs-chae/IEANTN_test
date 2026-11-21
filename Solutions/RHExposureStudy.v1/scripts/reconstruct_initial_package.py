#!/usr/bin/env python3
"""Regenerate every mathematical file of the full initial treatment package.

The .git worktree pointer is metadata, not a mathematical input. The actual
worker had current sources but could not access external Git history.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,tarfile,time,zipfile
S=Path(__file__).resolve().parents[1];F=S/'frozen-inputs'
def need(b,s):
 if not b:raise ValueError(s)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);a=p.parse_args();O=a.out.resolve();need(not O.exists(),'fresh clone destination required');started=time.monotonic()
subprocess.run(['git','clone','--filter=blob:none','--no-checkout','https://github.com/hs-chae/IEANTN_test.git',str(O)],check=True)
subprocess.run(['git','checkout','--detach','d5e89350283e42a0c1b1c323fd18c8a41ec6937d'],cwd=O,check=True)
j=json.loads((F/'ORIGINAL_ADDITIONS.json').read_text());expected={r['path']:r for r in j['additions']}
with zipfile.ZipFile(F/'original-research-additions.zip')as z:
 need(set(z.namelist())==set(expected),'complete addon membership')
 for name in z.namelist():
  q=Path(name);need(not q.is_absolute()and'..'not in q.parts,'safe source path');raw=z.read(name);need(hashlib.sha256(raw).hexdigest()==expected[name]['sha256'],'addon source hash');target=O/q;target.parent.mkdir(parents=True,exist_ok=True)
  if target.exists():need(target.read_bytes()==raw,'refuse to replace different baseline source')
  else:target.write_bytes(raw)
archive=F/'upstream-d60421f-source.tar.gz';need(sha(archive)=='c28a425694e968b298e59d754c3b6b7303262c197666e152ddadfd4d5b06decb','upstream archive hash');dest=O/'docs/source-snapshots';dest.mkdir(parents=True,exist_ok=True)
with tarfile.open(archive)as t:
 for member in t.getmembers():
  q=Path(member.name);need(not q.is_absolute()and'..'not in q.parts,'safe archive path');need(member.isfile()or member.isdir(),'no source archive link/device surprises')
 t.extractall(dest,filter='data')
manifest=json.loads((F/'FULL_INITIAL_SOURCE_MANIFEST.json').read_text());bad=[];n=0
for row in manifest['files']:
 if row['path']=='.git':continue
 q=O/row['path']
 if 'symlink'in row:ok=q.is_symlink()and os.readlink(q)==row['symlink']
 else:ok=q.is_file()and q.stat().st_size==row['bytes']and sha(q)==row['sha256']
 n+=1
 if not ok:bad.append(row['path'])
result={'status':'PASS_EXACT_INITIAL_MATHEMATICAL_PACKAGE'if not bad else'FAILED_INITIAL_RECONSTRUCTION','verified_initial_entries_excluding_git_pointer':n,'mismatches':bad,'elapsed_seconds':time.monotonic()-started,'metadata_exception':'.git pointer; clean clone has independent metadata, unavailable external history is not a mathematical source file','script_sha256':sha(__file__)}
(O.parent/(O.name+'-RECONSTRUCTION.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));need(not bad,'initial mathematical source differs')
