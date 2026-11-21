#!/usr/bin/env python3
"""Neutral per-arm original-source broker; no model calls, no mathematical coaching."""
from pathlib import Path
import argparse,datetime,hashlib,ipaddress,json,os,re,socket,time,urllib.request,urllib.parse,urllib.error
import fitz
R=Path(__file__).resolve().parents[1];D=Path('/data/ivy-rh-propagation-20261120')
PRIMARY={'arxiv.org','export.arxiv.org','doi.org','api.crossref.org','www.ams.org','ams.org','www.cambridge.org','link.springer.com','www.sciencedirect.com','www.numdam.org','numdam.org','projecteuclid.org','academic.oup.com','www.dlmf.nist.gov','dlmf.nist.gov','eudml.org','maths.anu.edu.au','people.maths.bris.ac.uk','www.impan.pl'}
FORBIDDEN=re.compile(r'ieantn|hs-chae/IEANTN_test|qrh[-_]pv[-_]synergy|ramanujan[-_]source[-_]pv',re.I)
def sha(b):return hashlib.sha256(b).hexdigest()
def now():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def read(p):
 def pairs(items):
  d={}
  for k,v in items:
   if k in d:raise ValueError('duplicate JSON key')
   d[k]=v
  return d
 return json.loads(Path(p).read_bytes(),object_pairs_hook=pairs,parse_constant=lambda v:(_ for _ in()).throw(ValueError('nonfinite JSON')))
def atomic(p,d):
 p.parent.mkdir(parents=True,exist_ok=True);t=p.with_name('.'+p.name+'.pending')
 with t.open('w')as f:json.dump(d,f,indent=2,ensure_ascii=False,allow_nan=False);f.write('\n')
 os.replace(t,p)
def admissible(url):
 u=urllib.parse.urlsplit(url)
 if u.scheme!='https' or not u.hostname or u.username or u.password or u.port not in (None,443):raise ValueError('canonical HTTPS source required')
 if FORBIDDEN.search(url):raise ValueError('project-specific material not an admissible external mathematical source')
 if u.hostname not in PRIMARY:raise ValueError('NEEDS_PRIMARY_SOURCE_LOCATOR_REVIEW: any legitimate new mathematical domain may be approved equally; no negative mathematical conclusion')
 for r in socket.getaddrinfo(u.hostname,443,type=socket.SOCK_STREAM):
  if not ipaddress.ip_address(r[4][0]).is_global:raise ValueError('nonpublic destination')
 return url
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  admissible(newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def fetch(url):
 admissible(url);start=now();cache=D/'broker/source-cache'/sha(url.encode());meta=cache/'RETRIEVAL.json';data=cache/'SOURCE.bin'
 if meta.exists()and data.exists():
  old=read(meta);body=data.read_bytes()
  if old.get('request_url')!=url or sha(body)!=old.get('sha256'):raise RuntimeError('original-source cache hash mismatch')
  return body,dict(old,service_utc=start,cache_reused=True)
 req=urllib.request.Request(url,headers={'User-Agent':'RH mathematical source comparison research (original-source retrieval)'})
 for attempt in range(4):
  try:
   with urllib.request.build_opener(Redirect()).open(req,timeout=60)as f:
    final=f.url;headers=dict(f.headers.items());body=f.read(256*1024**2+1)
   break
  except urllib.error.HTTPError as e:
   if e.code not in (429,502,503)or attempt==3:raise
   time.sleep([2,5,10][attempt])
 if len(body)>256*1024**2:raise ValueError('large source requires explicit increased broker allocation, not denied mathematically')
 receipt={'request_url':url,'final_url':final,'request_utc':start,'complete_utc':now(),'headers':headers,'bytes':len(body),'sha256':sha(body),'cache_reused':False}
 cache.mkdir(parents=True,exist_ok=True);data.write_bytes(body);atomic(meta,receipt)
 return body,receipt
def handle(arm,request):
 ident=request.get('id')
 if not isinstance(ident,str)or not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]{0,79}',ident):raise ValueError('invalid unique request id')
 folder=D/'literature'/arm/'admissions'/ident;out=folder/'RECEIPT.json'
 if out.exists():
  old=read(out)
  if old['request']!=request:raise ValueError('source request ID reused for different request')
  return old
 folder.mkdir(parents=True,exist_ok=True);result={'schema':'RH_PRIMARY_SOURCE_ADMISSION_V1','arm':arm,'request':request,'started_utc':now(),'broker_source_sha256':sha(Path(__file__).read_bytes()),'mathematical_validity':'NOT_INFERRED_FROM_RETRIEVAL'}
 try:
  if request.get('url'):
   body,receipt=fetch(request['url']);name='SOURCE.pdf'if body.startswith(b'%PDF-')else 'SOURCE.html';(folder/name).write_bytes(body);result.update(status='ORIGINAL_SOURCE_RETRIEVED',retrieval=receipt,artifact=name)
   if name.endswith('.pdf'):
    doc=fitz.open(stream=body,filetype='pdf');text='\n'.join('\n=== PDF PAGE '+str(i+1)+' ===\n'+page.get_text(sort=True)for i,page in enumerate(doc));(folder/'SOURCE.txt').write_text(text);result['text']={'path':'SOURCE.txt','bytes':len(text.encode()),'sha256':sha(text.encode()),'extractor':'PyMuPDF '+fitz.VersionBind,'locator':'PDF pages and physical byte LF lines'}
  elif request.get('query'):
   query=request['query']
   if not isinstance(query,str)or FORBIDDEN.search(query):raise ValueError('request must concern external original mathematical literature')
   url='https://api.crossref.org/works?'+urllib.parse.urlencode({'query.bibliographic':query,'rows':20})
   body,receipt=fetch(url);metadata=json.loads(body);items=metadata.get('message',{}).get('items',[])
   # Publisher/author metadata only, no search engine snippets or project-derived explanations.
   clean=[item for item in items if not FORBIDDEN.search(json.dumps(item,ensure_ascii=False))]
   atomic(folder/'SEARCH_RESULTS.json',{'query':query,'source':'Crossref canonical publisher/author metadata','items':clean,'excluded_project_items':len(items)-len(clean)})
   result.update(status='PRIMARY_BIBLIOGRAPHIC_SEARCH_RETURNED',retrieval=receipt,artifact='SEARCH_RESULTS.json',source_response_sha256=sha(body))
   raw=D/'broker/raw-responses'/arm/ident/'RAW_CROSSREF_RESPONSE.json';raw.parent.mkdir(parents=True,exist_ok=True);raw.write_bytes(body)
   result['raw_source_response_retained_outside_worker_mount']=True
  else:raise ValueError('source request needs url or query')
 except Exception as e:result.update(status='SOURCE_REQUEST_PENDING_OR_FAILED_NOT_SOURCE_EVIDENCE',error_type=type(e).__name__,error=str(e))
 result['completed_utc']=now();atomic(out,result)
 log=D/'broker'/arm/'ADMISSIONS.jsonl';log.parent.mkdir(parents=True,exist_ok=True)
 with log.open('a')as f:f.write(json.dumps({'id':ident,'status':result['status'],'receipt':str(out),'receipt_sha256':sha(out.read_bytes()),'utc':now()})+'\n')
 return result
def scan():
 rows=[]
 for arm in ['NL_RH','IEANTN_RH']:
  for run in sorted((D/'runs').glob('*'+arm+'*')):
   snapshots=sorted(run.glob('checkpoint-*/files'))
   if (run/'submission').exists():snapshots.append(run/'submission')
   if not snapshots:continue
   for snapshot in snapshots[-2:]:
    for name in ['SOURCE_REQUESTS.json','source_requests.jsonl']:
     p=snapshot/name
     if not p.exists():continue
     try:
      requests=read(p)['requests']if name.endswith('.json')else[json.loads(line)for line in p.read_text().splitlines()if line.strip()]
      for req in requests:rows.append(handle(arm,req))
     except Exception as e:
      atomic(D/'broker'/arm/'LAST_QUEUE_ERROR.json',{'utc':now(),'path':str(p),'error':str(e),'no_math_result_inferred':True})
 return rows
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--once',action='store_true');p.add_argument('--canary',action='store_true');a=p.parse_args()
 if a.canary:
  rows=[handle(arm,{'id':'neutral-fetch-canary','url':'https://arxiv.org/abs/2312.05628v4'})for arm in ['NL_RH','IEANTN_RH']]
  if any(r['status']!='ORIGINAL_SOURCE_RETRIEVED'for r in rows):raise RuntimeError('actual paired source fetch canary failed')
  if rows[0]['retrieval']['sha256']!=rows[1]['retrieval']['sha256']:raise RuntimeError('same initial canonical source bytes differ')
  atomic(D/'setup/SOURCE_BROKER_CANARY.json',{'status':'PAIRED_ACTUAL_SOURCE_FETCH_PASS','arms_separately_delivered':True,'source_bytes_same':True,'receipts':rows})
  print(json.dumps({'status':'PAIRED_ACTUAL_SOURCE_FETCH_PASS'}));return
 while True:
  scan()
  if a.once:return
  time.sleep(10)
if __name__=='__main__':main()
