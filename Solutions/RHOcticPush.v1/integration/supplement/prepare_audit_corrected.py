#!/usr/bin/env python3
"""Additive correction of a failed generated auditor; original165 freeze remains unchanged."""
from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent;R=H.parents[3]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(b,s):
 if not b:raise ValueError(s)
out=H/'audit-corrected-capture';need(not out.exists(),'fresh capture required');old=H/'capture/SOURCE_CLOSURE.json';m=json.loads(old.read_text());q=m['modules'][-1];need(q['module']=='FinalSupplementAudit','only final auditor');s=(R/q['path']).read_text();need(s.count('let mut count := 0')==1,'exact isolated annotation');fixed=s.replace('let mut count := 0','let mut count : Nat := 0');out.mkdir();f=out/'FinalSupplementAudit.lean';f.write_text(fixed);q['path']=str(f.relative_to(R));q['sha256']=sha(f);m['original_failed_manifest_sha256']=sha(old);m['correction']='Only generated audit count has explicit Nat type; all164 mathematical/core/consumer source hashes and identities unchanged.';m['selector_sha256']=sha(Path(__file__));(out/'SOURCE_CLOSURE.json').write_text(json.dumps(m,indent=2)+'\n')
