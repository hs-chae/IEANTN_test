#!/usr/bin/env python3
"""Put the four parts and RH_EVIDENCE_PARTS.json beside this script.
Run: python JOIN_RH_EVIDENCE.py --restore
The two report HTML attachments can be read directly without running this.
"""
from pathlib import Path
import argparse,hashlib,json,os,subprocess,sys,zipfile,math
def need(b,s):
 if not b:raise ValueError(s)
def strict(raw):
 def pairs(rows):
  d={}
  for k,v in rows:need(k not in d,'duplicate JSON key');d[k]=v
  return d
 def number(s):
  v=float(s);need(math.isfinite(v),'nonfinite JSON');return v
 return json.loads(raw,object_pairs_hook=pairs,parse_float=number,parse_constant=lambda s:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb')as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--directory',type=Path,default=Path(__file__).resolve().parent);p.add_argument('--restore',action='store_true');p.add_argument('--out',type=Path);a=p.parse_args();B=a.directory.resolve();m=strict((B/'RH_EVIDENCE_PARTS.json').read_text());need(m['schema']=='RH_RESEARCH_EVIDENCE_PARTS_V1','parts schema');need(type(m['archive_bytes'])is int and m['archive_bytes']>0,'archive size');need(isinstance(m['parts'],list)and len(m['parts'])==4,'four exact parts');need(len({r['name']for r in m['parts']})==4,'duplicate part');target=B/m['archive_name'];need(target.parent==B,'archive path')
for row in m['parts']:
 q=B/row['name'];need(type(row['bytes'])is int and row['bytes']>0,'part size');need(q.parent==B and q.is_file()and q.stat().st_size==row['bytes']and sha(q)==row['sha256'],'missing or changed part:'+row['name'])
if target.exists():need(target.stat().st_size==m['archive_bytes']and sha(target)==m['archive_sha256'],'existing archive differs')
else:
 temp=B/(target.name+'.joining');need(not temp.exists(),'unfinished output exists; inspect it before retry')
 with temp.open('xb')as dst:
  for row in m['parts']:
   with(B/row['name']).open('rb')as src:
    for block in iter(lambda:src.read(1048576),b''):dst.write(block)
 need(temp.stat().st_size==m['archive_bytes']and sha(temp)==m['archive_sha256'],'joined archive differs');os.link(temp,target);temp.unlink()
print('PASS joined exact evidence archive',target,flush=True)
if a.restore:
 out=(a.out or B/'RH_PROPAGATION_STUDY').resolve();need(not out.exists(),'choose a fresh --out directory')
 with zipfile.ZipFile(target)as z:raw=z.read('RESTORE.py')
 need(hashlib.sha256(raw).hexdigest()==m['restore_sha256'],'restorer source differs');script=B/'RESTORE_RH_EVIDENCE.py'
 if script.exists():need(script.read_bytes()==raw,'existing restorer differs')
 else:script.write_bytes(raw)
 cmd=[sys.executable,*(['-OO']if sys.flags.optimize==2 else['-O']if sys.flags.optimize==1 else[]),str(script),str(target),'--out',str(out)];subprocess.run(cmd,check=True);print('Read',out/'README.md',flush=True)
