#!/usr/bin/env python3
from pathlib import Path
import argparse,json,os,re,tempfile
p=argparse.ArgumentParser();p.add_argument('--id',required=True);g=p.add_mutually_exclusive_group(required=True);g.add_argument('--url');g.add_argument('--query');a=p.parse_args()
if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]{0,79}',a.id):raise ValueError('simple unique request id required')
f=Path('/work/submission/SOURCE_REQUESTS.json');f.parent.mkdir(parents=True,exist_ok=True)
d=json.loads(f.read_text()) if f.exists() else {'requests':[]}
if any(r['id']==a.id for r in d['requests']):raise ValueError('preserve old request; choose new id')
d['requests'].append({'id':a.id,'kind':'url' if a.url else 'search','value':a.url or a.query})
fd,n=tempfile.mkstemp(prefix='.sources-',dir=f.parent)
with os.fdopen(fd,'w') as h:json.dump(d,h,indent=2);h.write('\n')
os.replace(n,f);print('Request queued; check /corpus/literature/admissions/'+a.id+' after broker processing. Continue independent work meanwhile.')
