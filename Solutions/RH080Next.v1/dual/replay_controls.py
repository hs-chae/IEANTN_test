#!/usr/bin/env python3
# Copyright (c) 2026 IEANTN contributors. All rights reserved.
# Released under Apache 2.0 license as described in LICENSE.
# Authors: OpenAI (Codex)
"""Actual optimized-CLI rejection controls for the supplementary Arb replay."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
root=Path(sys.argv[1]);root.mkdir(parents=True,exist_ok=False)
controller=Path(__file__).with_name('replay_source_dual.py')
original=controller.with_name('inputs')/'dual-rh.json';raw=original.read_text();d=json.loads(raw)
cases={
 'boolean_penalty':json.dumps(dict(d,A=True)),
 'floating_penalty':json.dumps(dict(d,A=3.27)),
 'overflow_float':raw[:-2]+',"unused":1e999}\n',
 'duplicate_key':raw[:-2]+',"A":"36/11"}\n',
 'nan_token':raw[:-2]+',"unused":NaN}\n',
 'boolean_mesh':json.dumps(dict(d,m=True)),
 'missing_wing':json.dumps(dict(d,wing_heights=d['wing_heights'][:-1])),
 'constraint_violation':json.dumps(dict(d,wing_heights=['2']+d['wing_heights'][1:])),
 'floating_height':json.dumps(dict(d,wing_heights=[0.5]+d['wing_heights'][1:])),
 'impossible_target':raw,
}
rows=[]
for mode in [[],['-O'],['-OO']]:
 for name,value in cases.items():
  p=root/(name+'.json')
  if not p.exists():p.write_text(value)
  label=name+'-'+str(len(mode)and len(mode[0])-1 or 0)
  run=root/label
  cmd=[sys.executable,*mode,str(controller),'--witness',str(p),'--run',str(run),'--panels','1024']
  if name=='impossible_target':cmd+=['--target','1/10']
  v=subprocess.run(cmd,capture_output=True,text=True)
  if v.returncode==0 or (run/'RESULT.json').exists():raise RuntimeError('Rejected invalid-input control: '+label)
  (root/(label+'.stderr')).write_text(v.stderr)
  rows.append({'case':name,'optimization':mode,'returncode':v.returncode,'command':cmd,'stderr_sha256':hashlib.sha256(v.stderr.encode()).hexdigest()})
receipt={'status':'PASS_ALL_30_ACTUAL_CLI_NEGATIVE_CONTROLS','controller_sha256':hashlib.sha256(controller.read_bytes()).hexdigest(),'control_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'rows':rows,'scope':'Acceptance logic remains active under normal,-O,-OO; not a proof of interval-engine correctness or PV.'}
p=root/'RESULT.json';t=root/'.RESULT.tmp'
with t.open('x')as f:json.dump(receipt,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
try:os.link(t,p)
finally:t.unlink()
print(receipt['status'])
