"""Bind every audited written identity to the published exact source snapshots."""
from pathlib import Path
import hashlib,json,re,sys
B=Path(__file__).resolve().parent
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 rows=[]
 for name in ['PRIMARY14_IDENTITIES_V1.json','SUPPORT_OBJECTS_V1.json']:rows+=json.loads((B/name).read_text())['rows']
 need(len(rows)==59,'exact59 input/support identities')
 for row in rows:
  p=B/'SourceSnapshots'/row['file'];need(p.is_file()and sha(p)==row['file_sha256'],'actual source identity '+row['lean_name']);need(1<=int(row['decl_line'])<=len(p.read_text().splitlines()),'written declaration line')
 need(len({(x['file'],x['decl_line'],x['lean_name'])for x in rows})==59,'written identities do not collapse')
 metadata=B.parents[2]/'IEANTN/Nodes/MomentSourceInputs/v1/formalization.yaml';change=json.loads((B/'METADATA_PATH_ONLY_UPDATE.json').read_text());text=metadata.read_text();need(sha(metadata)==change['after_sha256'],'actual metadata path update')
 reverse=text.replace('Solutions/MomentPNT.v1.PUBLICATION/SourceAudit/RECEIPT_V2.json','audit/primary14-source-audit-v1/RECEIPT_V2.json').replace('Solutions/MomentPNT.v1.PUBLICATION/SourceAudit/PRIMARY14_AND_SUPPORT_SOURCE_AUDIT_V4.html','PRIMARY14_AND_SUPPORT_SOURCE_AUDIT_V4.html').replace('Solutions/MomentPNT.v1.PUBLICATION/SourceAudit/REVIEW_DELTA_V3.csv','REVIEW_DELTA_V3.csv')
 need(hashlib.sha256(reverse.encode()).hexdigest()==change['before_sha256'],'exactthree path-only substitutions')
 print('PASS_ALL59_SAMEBYTE_SOURCE_IDENTITIES_AND_METADATA_PATH_ONLY',sys.flags.optimize)
if __name__=='__main__':main()
