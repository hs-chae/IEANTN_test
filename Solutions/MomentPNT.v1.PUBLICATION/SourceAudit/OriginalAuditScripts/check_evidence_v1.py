"""Recheck exact source/math-audit population, hashes and actual final structural gate."""
from pathlib import Path
import argparse,csv,json,hashlib,re,subprocess,sys,tempfile,os
B=Path(__file__).resolve().parent;R=B.parents[1]
def need(ok,message):
 if not ok:raise ValueError(message)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):
 def unique(items):
  d={}
  for k,v in items:need(k not in d,'Duplicate JSON key');d[k]=v
  return d
 return json.loads(p.read_text(),object_pairs_hook=unique,
  parse_constant=lambda _:(_ for _ in()).throw(ValueError('Nonfinite JSON')))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
 out=a.out.resolve();need(not out.exists()and out.is_relative_to(B),'Fresh owned receipt')
 p=read(B/'PRIMARY14_IDENTITIES_V1.json')['rows'];s=read(B/'SUPPORT_OBJECTS_V1.json')['rows']
 need(len(p)==14 and len(s)==45,'Requested exact interface/support population')
 for row in p+s:need(sha(R/row['file'])==row['file_sha256'],'Changed actual source '+row['file'])
 identities={(x['file'],str(x['decl_line']),x['lean_name'])for x in p+s};need(len(identities)==59,'Unique written-source identities')
 with(B/'REVIEW_DELTA_V3.csv').open()as h:ledger=list(csv.DictReader(h))
 need({(x['file'],x['decl_line'],x['lean_name'])for x in ledger}==identities,'Exact requested59coverage')
 formulas=read(B/'EXPLICIT_SUPPORT_FORMULAS_V1.json');need(len(formulas)==45,'All explicit sourceformulas')
 for row in ledger:
  if row['kind']=='support_definition':
   need(formulas[row['lean_name'].split('.')[-1]]in row['actual_primary_source_statement_or_explicit_absence'],'Missing exact primaryformula')
 paper_records=[]
 for name,key in [('MANIFEST_V1.json','primary_sources'),('MANIFEST_ADDITIONS_V1.json','sources')]:
  for x in read(B/'papers'/name)[key]:
   file=x['path'];path=R.parent/file if file.startswith(R.name+'/')else R/file
   need(sha(path)==x['sha256'],'Primary PDF changed '+str(path));paper_records.append({'file':str(path.relative_to(R)),'sha256':x['sha256']})
 need(len(paper_records)==9,'Nine actual primary PDFs')
 validator=Path('/ryu/hyunsik/.codex/skills/lean-source-math-audit/scripts/validate_ledger.py')
 command=[sys.executable,str(validator),'--scope',str(B/'SCOPE59_V1.csv'),'--ledger',str(B/'REVIEW_DELTA_V3.csv'),'--require-final']
 q=subprocess.run(command,capture_output=True,text=True);need(q.returncode==0,'Skill finalgate')
 report=B/'PRIMARY14_AND_SUPPORT_SOURCE_AUDIT_V4.html';render=read(B/'RENDER_RECEIPT_V4.json')
 need(sha(report)==render['report_sha256']and sha(B/'REVIEW_DELTA_V3.csv')==render['ledger_sha256'],'Rendered report/sourceledger identity')
 need(not re.search(r'\\(?:frac|sum|int|zeta|sigma)|\$\$',report.read_text()),'Unrendered mathematical TeX')
 receipt={'status':'PASS_EXACT59_SOURCE_HASHES_PRIMARY_PDFS_AND_FINAL_LEDGER_GATE','interfaces':14,'support_definitions':45,
  'rows':59,'material_mismatches_found':0,'qualifier':'Self-assessed mathematical source-contract comparison; no independent reproof of the nine papers, no sourcefirstPV/cold/officialregistry claim. Full requested59population checked; notallMathlib.',
  'inventory_sha256':sha(B/'PRIMARY14_IDENTITIES_V1.json'),'support_sha256':sha(B/'SUPPORT_OBJECTS_V1.json'),
  'ledger_sha256':sha(B/'REVIEW_DELTA_V3.csv'),'report_sha256':sha(report),'primary_pdfs':paper_records,
  'validator':str(validator),'validator_sha256':sha(validator),'command':command,'actual_exit':q.returncode,'actual_stdout':q.stdout,
  'checker_sha256':sha(Path(__file__))}
 out.parent.mkdir(parents=True,exist_ok=True);fd,name=tempfile.mkstemp(dir=out.parent,prefix='.'+out.name)
 try:
  with os.fdopen(fd,'w')as h:json.dump(receipt,h,indent=2,allow_nan=False);h.write('\n')
  os.replace(name,out)
 finally:
  if Path(name).exists():Path(name).unlink()
 print(out)
if __name__=='__main__':main()
