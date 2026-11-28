#!/usr/bin/env python3
"""Synthetic control-flow/freshness tests, not Lean/proof acceptance."""
import argparse,importlib.util,json,sys
from pathlib import Path
ap=argparse.ArgumentParser();ap.add_argument('--driver',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();a.out.mkdir()
sys.path.insert(0,str(a.driver.parent));spec=importlib.util.spec_from_file_location('driver',a.driver);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
def need(v,s):
 if not v:raise RuntimeError(s)
marker='C7_FULL_KERNEL_CONTROL_PASS exact-PV-and-FFT-only-control-types same-W4-2520-coefficients same-N24-norm same-ANT-residual-consumer Std3 no-native four-opaque-kernel-scalar-certificates no-new-numerical-premise unused-source-containing-imports-disclosed POSTHOC-NON-PV'
lines=[marker,'C7_FULL_KERNEL_CONTROL_AXIOMS','C7_PURE_N24_MODULE_GRAPH appmodules=1059 declarations=552925','C7_FULL_KERNEL_CONTROL_PROOF_CLOSURE names=3316 actual-C-source-correspondence-run=0','C7_PRUNED_PURE_DATA_BOUNDARIES []']
rows=[]
for case in ['positive','wrong-status','wrong-count','boolean-count','missing-pass','duplicate-pass','missing-evidence','existing-terminal']:
 root=a.out/case;root.mkdir();r=m.Runner(type('Args',(),dict(run=root,context=root/'context.json'))())
 commands=[]
 def call(stage,tag,cmd,protected):
  commands.append(cmd);need(protected,'unprotected compiler');need(cmd.count('--root')==1 and cmd[cmd.index('--root')+1]=='C7KernelAudit','wrong root');need('--source-root' not in cmd,'duplicate source root');need(cmd.count('--bank')==2,'missing banks')
  work=root/stage/'work';(work/'logs').mkdir(parents=True)
  result=dict(status='PASS_SOURCE_ASSOCIATED_BATCH_MODULES_ONLY',modules=3)
  if case=='wrong-status':result['status']='PASS_FAKE'
  if case=='wrong-count':result['modules']=2
  if case=='boolean-count':result['modules']=True
  (work/'RESULT.json').write_text(json.dumps(result))
  output=list(lines)
  if case=='missing-pass':output=output[1:]
  if case=='duplicate-pass':output.append(marker)
  if case=='missing-evidence':output=output[:-1]
  (work/'logs/C7KernelAudit.stdout').write_text('\n'.join(output)+'\n')
 r.call=call
 terminal=root/'c7-kernel-control/STAGE_RESULT.json'
 if case=='existing-terminal':terminal.parent.mkdir();terminal.write_text('ORIGINAL\n')
 failed=False
 try:r.run_stage('c7-kernel-control')
 except (ValueError,FileExistsError):failed=True
 need(failed==(case!='positive'),'case outcome differs '+case)
 if case=='positive':
  need(json.loads(terminal.read_text())['public_status']=='PASS_POSTHOC_FULL_KERNEL_NONPV_W4_CONTROL_SAME_PREMISES','final result absent')
 elif case=='existing-terminal':
  need(terminal.read_text()=='ORIGINAL\n','old terminal overwritten');need(not commands,'existing terminal launched compiler');need(not(root/'c7-kernel-control/C7_CONTROL_ACCEPTANCE.json').exists(),'existing terminal published acceptance')
 else:need(not terminal.exists(),'rejected case published stage result')
 rows.append(dict(case=case,rejected=failed,synthetic_compiler=True))
(a.out/'RESULT.json').write_text(json.dumps(dict(status='PASS_SYNTHETIC_C7_STAGE_CONTROL_FLOW_NOT_PROOF_ACCEPTANCE',positive=1,negative=7,cases=rows),indent=2)+'\n')
print(json.dumps(dict(positive=1,negative=7,source_first_PV=False,Lean_compiler_executed=False)))
