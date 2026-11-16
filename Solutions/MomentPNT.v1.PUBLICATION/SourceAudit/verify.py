"""Verify this published source audit offline, including exact original recovery."""
from pathlib import Path
from html.parser import HTMLParser
import argparse,csv,hashlib,html,json,math,re,sys,urllib.parse
B=Path(__file__).resolve().parent
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def digest(s):return hashlib.sha256(s.encode()).hexdigest()
def read(p):
 def pairs(xs):
  d={}
  for k,v in xs:need(k not in d,'duplicateJSON '+k);d[k]=v
  return d
 def bad(x):raise ValueError('nonfiniteJSON '+x)
 def floating(s):
  x=float(s);need(math.isfinite(x),'overflowJSON');return x
 return json.loads(p.read_text(),object_pairs_hook=pairs,parse_constant=bad,parse_float=floating)
class Links(HTMLParser):
 def __init__(self):super().__init__();self.links=[];self.active=[]
 def handle_starttag(self,t,attrs):
  if t in ['script','iframe']:self.active.append(t)
  for k,v in attrs:
   if k in ['href','src']:self.links.append((k,v))
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);ap.add_argument('--papers',type=Path);a=ap.parse_args();out=a.out.resolve();need(not out.exists()and out.is_relative_to(B),'fresh owned output');m=read(B/'LINK_ONLY_MANIFEST.json');text=(B/m['report']).read_text();need(sha(B/m['report'])==m['published_report_sha256'],'publishedHTML')
 need(len(m['mapping'])==48 and len(set(m['mapping'].values()))==48,'bijective exact48 hyperlinks');reverse={v:k for k,v in m['mapping'].items()}
 def undo(x):
  href=html.unescape(x.group(1));need(href in reverse,'all actualhrefsdeclared');return 'href="'+html.escape(reverse[href],quote=True)+'"'
 original=re.sub(r'href="([^"]+)"',undo,text);need(digest(original)==m['original_report_sha256']=='2988880a5612ab33f001216bd7a585bce85d7eea83ddf573eaa9494a4cffeaac','exact original HTML recovered')
 need(digest(re.sub(r'href="[^"]+"','href=""',text))==m['non_href_text_sha256'],'all nonhref bytes unchanged')
 formula=re.findall(r'<math\b[\s\S]*?</math>',text);need(len(formula)==83 and[digest(s)for s in formula]==m['all83_mathml_sha256'],'exactall83 MathML')
 need('\\('not in text and'\\['not in text and'$$'not in text,'no rawTeX delimiters')
 for row in m['source_snapshots']+m['original_copies']:
  p=B/row.get('published_path',row.get('path',''));need(p.is_file()and not p.is_symlink()and sha(p)==row['sha256'],'exact copied evidence '+str(p))
 need(len(m['source_snapshots'])==15,'all15actual samebyte sources')
 receipt=read(B/'RECEIPT_V2.json');need(sha(B/'RECEIPT_V2.json')=='643bf26807e647ff112fddedd5e06f987beeac679d8b6c2750ddb617995400c0'and receipt['audited_population']==59 and receipt['interfaces']==14 and receipt['support_definitions']==45,'exact completed original source audit')
 rows=list(csv.DictReader((B/'REVIEW_DELTA_V3.csv').open()));need(len(rows)==59,'exact59ledger');need(len({(r['file'],r['decl_line'],r['lean_name'])for r in rows})==59,'written source identities')
 papers=read(B/'PRIMARY_PAPERS.json');byurl={r['primary_url']:r for r in papers['papers']};need(len(byurl)==9,'exact9primary identities')
 p=Links();p.feed(text);need(len(p.links)==134 and not p.active,'exact134 passive/offline links');local=[];external=[]
 for key,link in p.links:
  u=urllib.parse.urlsplit(link)
  if u.scheme:
   base=urllib.parse.urlunsplit((u.scheme,u.netloc,u.path,u.query,''));need(key=='href'and base in byurl,'actualprimaryURLonly');need(re.fullmatch(r'page=[0-9]+',u.fragment)is not None and 1<=int(u.fragment[5:])<=byurl[base]['pages'],'exactPDFpageanchor');external.append(link)
  else:
   target=(B/urllib.parse.unquote(u.path)).resolve();need(target.is_relative_to(B)and target.is_file(),'alllocaltargetsexist '+link)
   if u.fragment.startswith('L'):need(u.fragment[1:].isdigit()and 1<=int(u.fragment[1:])<=len(target.read_text().splitlines()),'actualsource lineanchor')
   local.append(link)
 if a.papers:
  for row in papers['papers']:need(sha(a.papers/row['cached_name'])==row['cached_sha256'],'actualprimaryPDFregeneration '+row['cached_name'])
 data=dict(status='PASS_OFFLINE_PUBLIC_SOURCE59_LINK_ONLY_MATH_AND_EVIDENCE_GATE',actual_python_optimization=sys.flags.optimize,report_sha256=sha(B/m['report']),original_recovered_sha256=digest(original),static_mathml=83,unchanged_non_href_content=True,actual_source_snapshots=15,ledger_rows=59,hyperlinks=134,local_occurrences=len(local),external_primary_occurrences=len(external),primary_papers=9,local_targets_all_exist=True,primary_pdf_bytes_rechecked=a.papers is not None,validator_sha256=sha(Path(__file__)),qualification='Actual source/math content unchanged; paper URLs and PDFpages pinned to exact primary identities. External availability is not promised. KLN author origin currentlytimedout; its cached exact2018manuscript is retained privately and hash/primaryauthorURLpublished. No new paperreproof/numerical/PV/Comparator acceptance.')
 out.parent.mkdir(parents=True,exist_ok=True);out.write_text(json.dumps(data,indent=2)+'\n');print(data['status'],len(local),len(external))
if __name__=='__main__':main()
