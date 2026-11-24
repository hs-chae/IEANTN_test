#!/usr/bin/env python3
"""Exact generated challenge types; solutions imported, admitted challenges never."""
from pathlib import Path
import re,json,hashlib
HERE=Path(__file__).resolve().parent;I=HERE.parent;R=I.parents[2]
parts=['import OcticVerifiedEvolution\n\n'];rows=[]
for fam,ver in [('PrimeKernelInputs','v4'),('PrimeInterval','v4'),('PrimeQuantile','v3'),('Goldbach','v2')]:
 p=R/'IEANTN/Nodes'/fam/ver/'Challenge.lean';s=p.read_text();matches=list(re.finditer(r'^theorem ([A-Za-z0-9_\.]+)(.*?) := by\n  sorry\b',s,re.M|re.S))
 if not matches:raise ValueError('empty challenge file')
 for match in matches:
  name,sig=match.group(1),match.group(2);args=re.findall(r'\(([A-Za-z0-9_]+)\s*:',sig)
  if sig.count('(')!=len(args):raise ValueError('unsupported generated binder')
  parts.append('example'+sig+' :=\n  @'+name+(' '+' '.join(args)if args else'')+'\n\n#print axioms '+name+'\n')
  rows.append({'file':str(p.relative_to(R)),'line':s[:match.start()].count('\n')+1,'declaration':name,'verbatim_signature':sig,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
p=I/'ExactSupplementTypes.lean';p.write_text(''.join(parts));(HERE/'EXACT_CHALLENGE_TYPES.json').write_text(json.dumps({'method':'Verbatim generated type; independent actual solution constant; no admitted Challenge import','claims':rows,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest()},indent=2)+'\n');print(len(rows),'actual generated signature checks')
