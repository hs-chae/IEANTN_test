#!/usr/bin/env python3
"""Read-only exact published GitHub-link and raw-byte association audit."""
import argparse,concurrent.futures,hashlib,json,os,subprocess,tempfile,time,urllib.request,urllib.error
from html.parser import HTMLParser
from pathlib import Path
from urllib.parse import urlsplit,unquote,quote

def need(x,m):
 if not x:raise ValueError(m)
def sha(b):return hashlib.sha256(b).hexdigest()
class Links(HTMLParser):
 def __init__(self):super().__init__();self.urls=[]
 def handle_starttag(self,t,a):
  if t=='a':
   q=dict(a)
   if q.get('href','').startswith('https://github.com/hs-chae/IEANTN_test/blob/'):self.urls.append(q['href'])
def fetch(url,method,limit=None):
 attempts=[]
 for turn in range(3):
  try:
   request=urllib.request.Request(url,method=method,headers={'User-Agent':'IvyMathematicalArtifactVerification/1.0'})
   with urllib.request.urlopen(request,timeout=30)as r:
    status=r.status;raw=r.read(limit)if limit is not None else b'';final=r.url
   attempts.append(dict(status=status,final_url=final));return raw,attempts
  except Exception as e:
   attempts.append(dict(error=type(e).__name__+': '+str(e)))
   if turn<2:time.sleep(0.5*(turn+1))
 return None,attempts
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--html',type=Path,required=True);p.add_argument('--repository',type=Path,required=True);p.add_argument('--commit',required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args();need(not a.out.exists(),'Fresh HTTP receipt required');need(len(a.commit)==40 and all(c in '0123456789abcdef'for c in a.commit),'Full pinned commit required');old=a.html.read_bytes();h=sha(old);x=Links();x.feed(old.decode());urls=sorted(set(x.urls));need(urls,'No source links');start=time.monotonic()
 def one(url):
  tail=unquote(urlsplit(url).path.split('/blob/',1)[1]);commit,path=tail.split('/',1);need(commit==a.commit,'Mixed source revision');need('..'not in Path(path).parts,'Unexpected source path');expected=subprocess.check_output(['git','show',commit+':'+path],cwd=a.repository);rawurl='https://raw.githubusercontent.com/hs-chae/IEANTN_test/'+commit+'/'+quote(path,safe='/');page,pa=fetch(url,'HEAD');raw,ra=fetch(rawurl,'GET',len(expected)+1);pageok=page is not None and pa[-1].get('status')==200;rawok=raw is not None and raw==expected;return dict(url=url,raw_url=rawurl,path=path,github_exact_page_HTTP200=pageok,raw_bytes_match_published_local_Git_blob=rawok,expected_bytes=len(expected),expected_sha256=sha(expected),received_bytes=len(raw)if raw is not None else None,received_sha256=sha(raw)if raw is not None else None,page_attempts=pa,raw_attempts=ra)
 with concurrent.futures.ThreadPoolExecutor(max_workers=2)as pool:rows=list(pool.map(one,urls))
 need(a.html.read_bytes()==old,'Report changed during HTTP checks');ok=all(r['github_exact_page_HTTP200']and r['raw_bytes_match_published_local_Git_blob']for r in rows);j=dict(status='PASS_EXACT_GITHUB_SOURCE_URLS_AND_RAW_BYTES'if ok else'FAIL_PUBLISHED_SOURCE_URL_OR_RAW_BYTES',commit=a.commit,html_sha256=h,links=len(rows),seconds=time.monotonic()-start,rows=rows,controller_sha256=sha(Path(__file__).read_bytes()));fd,name=tempfile.mkstemp(dir=a.out.parent,prefix='.http-receipt-');q=Path(name)
 try:
  with os.fdopen(fd,'w')as f:json.dump(j,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
  os.link(q,a.out)
 finally:q.unlink()
 print(json.dumps(dict(status=j['status'],links=len(rows),seconds=j['seconds'],bad_pages=sum(not r['github_exact_page_HTTP200']for r in rows),bad_raw=sum(not r['raw_bytes_match_published_local_Git_blob']for r in rows))))
 if not ok:raise SystemExit(1)
if __name__=='__main__':main()
