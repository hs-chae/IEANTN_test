# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: OpenAI (Codex)
# Fresh isolated proof, actual C execution, and immutable strict readback.
import hashlib,json,subprocess,sys,time
from pathlib import Path
component,jobs,preflight=sys.argv[1:];s=Path('/task');o=Path('/work');start=time.monotonic();rows=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd):
 t=time.monotonic();q=subprocess.run(cmd);rows.append(dict(command=cmd,exit_code=q.returncode,seconds=time.monotonic()-t))
 if q.returncode:raise SystemExit(q.returncode)
producer='reproduce_v2.py'if component=='witness'else'reproduce.py';auditor='audit_replay_v2.py'if component=='witness'else'audit_replay.py';filename='STRICT_RECEIPT.json'if component=='witness'else'RECEIPT.json'
cmd=['/usr/bin/python3.10','-I','-B',str(s/producer),'--environment','/generic/ENVIRONMENT.json','--out','/work/proof','--jobs',jobs]
if preflight=='yes':cmd.append('--validate-only')
run(cmd)
if preflight=='yes':
 p=o/'proof/VALIDATION_PASS.json'
 if json.loads(p.read_text())['status']!='VALIDATION_ONLY_PASS_NO_PROOF_REPLAY':raise ValueError('component preflight missing')
 status='PREFLIGHT_ONLY_NO_PROOFS'
else:
 receipts=[]
 for mode in ['', '-O','-OO']:
  dest=o/('strict-'+(mode or'normal'));run(['/usr/bin/python3.10']+([mode]if mode else[])+['-I','-B',str(s/auditor),'--replay','/work/proof','--out',str(dest)]);receipts.append(dest/filename)
 expected='FINAL_STRICT_WITNESS_SOURCE_ONLY_PASS'if component=='witness'else'FINAL_STRICT_ACCEPTANCE_PASS'
 if any(json.loads(p.read_text())['status']!=expected for p in receipts)or len({sha(p)for p in receipts})!=1:raise ValueError('strict modes disagree')
 p=receipts[0];status='PASS_FRESH_SOURCE_C_AND_THREE_MODE_STRICT_OFFLINE_NAMESPACE'
d=dict(status=status,component=component,seconds=time.monotonic()-start,stages=rows,final_receipt_sha256=sha(p),source_lock_sha256=sha(s/'SOURCE_LOCK.json'))
(o/'NAMESPACE_PIPELINE_RECEIPT.json').write_text(json.dumps(d,indent=2)+'\n');print(status)
