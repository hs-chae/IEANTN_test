#!/usr/bin/env python3
"""Fetch pinned originals for reading; this does not prove any source theorem."""
import argparse,hashlib,json,os,urllib.request
from pathlib import Path

def main():
 p=argparse.ArgumentParser(description=__doc__,allow_abbrev=False)
 p.add_argument('--out',type=Path,required=True)
 a=p.parse_args();out=a.out.resolve()
 if out.exists():raise ValueError('Fresh owned output directory required')
 out.mkdir(parents=True);rows=[]
 for row in json.loads(Path(__file__).with_name('SOURCE_URLS.json').read_text())['files']:
  try:
   content=urllib.request.urlopen(row['url'],timeout=90).read()
   sha=hashlib.sha256(content).hexdigest()
   if sha!=row['sha256']:raise ValueError('Pinned primary-source hash differs')
   if 'bytes' in row and len(content)!=row['bytes']:raise ValueError('Primary-source length differs')
   (out/row['name']).write_bytes(content)
   rows.append(dict(row,status='FETCHED_PINNED_PRIMARY_BYTES',actual_bytes=len(content)))
  except Exception as error:
   fallback=row.get('preserved_fallback')
   if fallback:
    original=Path(__file__).with_name(fallback)
    content=original.read_bytes()
    if hashlib.sha256(content).hexdigest()!=row['sha256']:raise ValueError('Preserved primary-source hash mismatch')
    (out/row['name']).write_bytes(content)
    rows.append(dict(row,status='USED_PRESERVED_PUBLIC_DOMAIN_PRIMARY_BYTES',remote_error=str(error),actual_bytes=len(content)))
   else:rows.append(dict(row,status='FETCH_FAILED_NOT_SOURCE_EVIDENCE',error=str(error)))
 temp=out/'DOWNLOAD.json.new'
 with temp.open('x') as stream:json.dump(rows,stream,indent=2);stream.write('\n');stream.flush();os.fsync(stream.fileno())
 os.replace(temp,out/'DOWNLOAD.json')
 if any(r['status'] not in ('FETCHED_PINNED_PRIMARY_BYTES','USED_PRESERVED_PUBLIC_DOMAIN_PRIMARY_BYTES') for r in rows):raise SystemExit('Some primary downloads failed; originals remain preserved, see DOWNLOAD.json')
 print('Pinned primary originals reproduced:',len(rows),'; archived fallback:',sum(r['status']=='USED_PRESERVED_PUBLIC_DOMAIN_PRIMARY_BYTES' for r in rows))
if __name__=='__main__':main()
