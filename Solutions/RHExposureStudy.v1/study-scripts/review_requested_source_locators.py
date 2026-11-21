#!/usr/bin/env python3
"""Fulfil already-requested original publisher URLs after neutral locator review.

No source is supplied to an arm unless that arm already requested its exact URL.
No mathematical assertions or substituted papers are delivered.
"""
from pathlib import Path
import hashlib,importlib.util,json,datetime,urllib.parse
R=Path(__file__).resolve().parents[1];D=Path('/data/ivy-rh-propagation-20261120');p=R/'scripts/source_broker_v2.py';s=importlib.util.spec_from_file_location('sourcev2',p);m=importlib.util.module_from_spec(s);s.loader.exec_module(m)
review={'math.colgate.edu':'Integers original journal university host; requested literal PDF only, no presumed author/title match','files.ele-math.com':'Mathematical Inequalities and Applications original publisher PDF host','ems.press':'EMS Press original publisher and canonical article PDFs','www.worldscientific.com':'World Scientific canonical journal publisher','worldscientific.com':'World Scientific canonical journal publisher','www.degruyter.com':'De Gruyter canonical publisher','www.degruyterbrill.com':'De Gruyter Brill canonical publisher','reference-global.com':'Canonical journal publisher platform','www.reference-global.com':'Canonical journal publisher platform','link.springernature.com':'Springer Nature official journal platform redirect'}
m.b.PRIMARY.update(review)
rows=[]
for arm in ['NL_RH','IEANTN_RH']:
 for receipt in sorted((D/'literature'/arm/'admissions').glob('*/RECEIPT.json')):
  old=m.b.read(receipt)
  if 'NEEDS_PRIMARY_SOURCE_LOCATOR_REVIEW'not in old.get('error',''):continue
  request=old['request'];req=m.normalized(request);url=req.get('url')
  if not url:continue
  original=receipt.read_bytes();history=receipt.parent/'HISTORY/RECEIPT_BEFORE_PRIMARY_LOCATOR_REVIEW.json';history.parent.mkdir(exist_ok=True)
  if history.exists():raise RuntimeError('review repeat needs separate fresh attempt')
  history.write_bytes(original);receipt.unlink()
  result=m.handle(arm,request);result['neutral_primary_locator_review']={'reviewed_utc':m.b.now(),'review_source_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'approved_original_provider_domains':review,'exact_requested_url_only':url,'original_attempt':{'path':str(history),'sha256':hashlib.sha256(original).hexdigest()},'mathematical_source_claim_not_assumed_from_retrieval':True}
  m.b.atomic(receipt,result);rows.append({'arm':arm,'id':receipt.parent.name,'status':result['status'],'error':result.get('error'),'receipt':str(receipt),'sha256':hashlib.sha256(receipt.read_bytes()).hexdigest()})
(D/'setup/NEUTRAL_REQUESTED_SOURCE_LOCATOR_REVIEW.json').write_text(json.dumps({'utc':m.b.now(),'provider_approval':review,'only_already_requested_sources':True,'results':rows},indent=2)+'\n')
print(json.dumps(rows))
