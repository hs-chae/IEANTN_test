"""Verify the downloadable source/evidence bundle without a second archive."""
from pathlib import Path
import argparse,hashlib,json,math,tarfile
EXPECTED_ARCHIVE='9db5107964292467bc0d3d81838b5f49c9b796afae7cb966dcdbde63305cbc70'
EXPECTED_MANIFEST='95c7baa8eccbfd4bb8e391debe6102dd7c65cf3c0606473d706f8cae825c6239'
MANIFEST_PATH='research/analytic/HELDOUT_MOMENT_SOURCE_EVIDENCE_V7_FILES.json'
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def parse(text):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicateJSON');d[k]=v
  return d
 def bad(s):raise ValueError('nonfiniteJSON')
 def floating(s):
  v=float(s);need(math.isfinite(v),'overflowJSON');return v
 return json.loads(text,object_pairs_hook=pairs,parse_float=floating,parse_constant=bad)
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--archive',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();need(not a.out.exists()and sha(a.archive)==EXPECTED_ARCHIVE,'fresh receipt and exact published archive');seen={};manifest=None
 with tarfile.open(a.archive,'r|xz')as t:
  for member in t:
   name=member.name;need(member.isfile()and name not in seen and not Path(name).is_absolute()and'..'not in Path(name).parts,'regular unique canonical member');need('HANDOFF'not in Path(name).name.upper()and Path(name).name!='HOST_CANARY'and'transcript'not in Path(name).name.lower(),'public scope');data=t.extractfile(member).read();seen[name]=(len(data),hashlib.sha256(data).hexdigest())
   if name==MANIFEST_PATH:need(seen[name][1]==EXPECTED_MANIFEST,'exact manifest bytes');manifest=parse(data.decode('utf-8'))
 need(manifest is not None,'manifest present');rows=manifest['files'];expected={r['path']:(r['bytes'],r['sha256'])for r in rows};need(len(expected)==len(rows)==27362,'unique exact file population');expected[MANIFEST_PATH]=seen[MANIFEST_PATH];need(seen==expected and len(seen)==27363,'every member byte length and SHA matches');rec=dict(status='PASS_COMPLETE_PUBLIC_MOMENT_V7_27363_MEMBER_READBACK',archive_sha256=EXPECTED_ARCHIVE,archive_bytes=a.archive.stat().st_size,manifest_sha256=EXPECTED_MANIFEST,members=len(seen),private_handoffs_transcripts_canary_files=False,report='exposure/heldout-audit-v1/HELDOUT_AND_MOMENT_ANT_REPORT_V6.html',qualification='Complete received-file/member integrity and publication-scope check. Mathematical proof/reproduction receipts are inside; this check is not another Lean replay.');a.out.parent.mkdir(parents=True,exist_ok=True);tmp=a.out.with_suffix('.pending');tmp.write_text(json.dumps(rec,indent=2,allow_nan=False)+'\n');tmp.replace(a.out);print(rec['status'])
if __name__=='__main__':main()
