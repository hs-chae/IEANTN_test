#!/usr/bin/env python3
"""Separate corrected114 freeze; rejected original bytes are never edited."""
from pathlib import Path
import copy,hashlib,json
HERE=Path(__file__).resolve().parent;I=HERE.parent;R=I.parents[2]
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 out=HERE/'capture';need(not out.exists(),'fresh corrected capture required');origin=I/'capture/SOURCE_CLOSURE.json';m=copy.deepcopy(json.loads(origin.read_text()));audit=json.loads((HERE/'AUTHOR_SOURCE_AUDIT.json').read_text());diffs=[x for x in audit['rows']if x.get('frozen_matches_current')is False]
 need(len(diffs)==1 and diffs[0]['module']=='OcticDerivativeMoments','exact independently identified correction only');fix=diffs[0];need(bool(fix['current_author_accepted_hash_receipts']),'corrected source has no author-accepted hash receipt')
 sources=[]
 for row in m['modules']:
  p=R/row['path'];need(sha(p)==row['sha256'],'original frozen source changed')
  if row['module']=='OcticDerivativeMoments':
   p=R/row['original_path'];need(sha(p)==fix['current_sha256'],'author-corrected source changed');row['sha256']=fix['current_sha256']
  elif row['original_path'] is not None:need(sha(R/row['original_path'])==row['sha256'],'another original-source drift')
  sources.append((row,p))
 out.mkdir();frozen=out/'frozen-source';frozen.mkdir()
 for row,p in sources:
  q=frozen/(row['module'].replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes());row['path']=str(q.relative_to(R))
 for rr in m['resources']:
  q=frozen/rr['relative_runtime_path'];q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes((R/rr['path']).read_bytes());need(sha(q)==rr['sha256'],'include source drift')
 m.update(selector_sha256=sha(__file__),rejected_original_manifest_sha256=sha(origin),correction={'module':fix['module'],'old_sha256':fix['frozen_sha256'],'new_sha256':fix['current_sha256'],'reason':'Original selector captured an author-active draft before its accepted final primitive/log-integral proofs. Original failed attempt remains historical and unaccepted. All114 exact identities reviewed; only this source hash differs.','author_accepted_receipts':fix['current_author_accepted_hash_receipts']},source_selection='Exact original114 identities; one explicitly documented author-accepted source correction, no removed module, mathematical target, source hypothesis or new numerical premise. All selected objects must be sourcefresh; transparent same-campaign identical prefix reuse is separately validated.')
 (out/'SOURCE_CLOSURE.json').write_text(json.dumps(m,indent=2)+'\n');print('CORRECTED114_FROZEN_ORIGINAL_PRESERVED',sha(out/'SOURCE_CLOSURE.json'))
if __name__=='__main__':main()
