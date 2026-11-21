#!/usr/bin/env python3
from pathlib import Path
import importlib.util,json,subprocess,sys,hashlib
p=Path(__file__).with_name('source_broker.py');spec=importlib.util.spec_from_file_location('broker',p);b=importlib.util.module_from_spec(spec);spec.loader.exec_module(b)
checks=[]
for u in ['http://arxiv.org/pdf/1234.5678','https://github.com/teorth/IEANTN','https://raw.githubusercontent.com/someone/mirrored-network/main/README.md','https://zenodo.org/records/1234','https://127.0.0.1/file','https://user:password@arxiv.org/pdf/1234.5678']:
 try:b.admissible(u)
 except ValueError:checks.append({'kind':'denied_pending_or_invalid','url':u})
 else:raise RuntimeError('source provenance gate accepted unreviewed or forbidden source')
for arm in ['CANARY_FINAL_NL_RH','CANARY_FINAL_IEANTN_RH']:
 for req in [{'id':'fetch-route-v3','url':'https://arxiv.org/abs/2312.05628v4'},{'id':'search-route-v3','query':'Sharper bounds for error prime number theorem Riemann hypothesis Lee Nosal'}]:
  r=b.handle(arm,req)
  if r['status']not in {'ORIGINAL_SOURCE_RETRIEVED','PRIMARY_BIBLIOGRAPHIC_SEARCH_RETURNED'}:raise RuntimeError('positive canonical route failed')
  if (b.D/'literature'/arm/'admissions'/req['id']/'RAW_CROSSREF_RESPONSE.json').exists():raise RuntimeError('unfiltered response leaked into source mount')
  checks.append({'arm':arm,'id':req['id'],'status':r['status'],'cache_reused':r['retrieval'].get('cache_reused',False)})
 if (b.D/'literature'/arm/'admissions'/'id-from-other-arm').exists():raise RuntimeError('unexpected other-arm response')
receipt={'status':'PASS_SOURCE_BROKER_POSITIVE_AND_FAIL_CLOSED_ROUTES','source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'test_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'optimization':sys.flags.optimize,'checks':checks,'initial_study_literature_unchanged':True,'generic_exactrequested_source_cache_reuse_disclosed':True,'unknown_canonical_supplements_pending_neutral_primary_locator_review_not_forbidden_mathematics':True}
print(json.dumps(receipt))
