#!/usr/bin/env python3
"""Exact verbatim606b Ramanujan challenge types; never imports admitted Challenges."""
from pathlib import Path
import re,json,hashlib
H=Path(__file__).resolve().parent;R=H.parents[3]
versions=[('RamanujanGap','v6')];parts=['import Ram606Network\n\n'];rows=[]
for f,v in versions:
 p=R/'IEANTN/Nodes'/f/v/'Challenge.lean';s=p.read_text();matches=list(re.finditer(r'^theorem ([A-Za-z0-9_\.]+)(.*?) := by\n  sorry\b',s,re.M|re.S))
 if not matches:raise ValueError('empty generated types:'+str(p))
 for m in matches:
  n,sig=m.group(1),m.group(2);args=re.findall(r'\(([A-Za-z0-9_]+)\s*:',sig)
  if sig.count('(')!=len(args):raise ValueError('unsupported generated binder')
  parts.append('example'+sig+' :=\n  @'+n+(' '+' '.join(args)if args else'')+'\n\n#print axioms '+n+'\n');rows.append({'file':str(p.relative_to(R)),'line':s[:m.start()].count('\n')+1,'declaration':n,'verbatim_signature':sig,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
p=H/'ExactRam606Types.lean';p.write_text(''.join(parts));(H/'EXACT_TYPES.json').write_text(json.dumps({'claims':rows,'source_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'method':'Exact generated type copied verbatim; actual independent solution constant, no admitted Challenge imported'},indent=2)+'\n');print('exacttypes',len(rows))
