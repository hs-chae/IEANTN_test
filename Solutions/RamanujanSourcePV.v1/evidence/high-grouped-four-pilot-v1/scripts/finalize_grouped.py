#!/usr/bin/env python3
from pathlib import Path
import argparse,hashlib,json,math,re,sys
R=Path(__file__).resolve().parent;S=Path('/ryu/hyunsik/playground/independence/codex/ivy/ieantn-ramanujan-source-pv-20261119/network/Solutions/RamanujanSourcePV.v1')
def need(v,m):
 if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def pairs(xs):
 d={}
 for k,v in xs:need(k not in d,'duplicate key');d[k]=v
 return d
def reject(v):raise ValueError('nonfinite metadata')
def finite(v):
 x=float(v);need(math.isfinite(x),'finite metadata');return x
def read(p):return json.loads(Path(p).read_text(),object_pairs_hook=pairs,parse_constant=reject,parse_float=finite)
p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--out',type=Path,required=True);p.add_argument('--result',type=Path,default=R/'RESULT.json');a=p.parse_args();result=read(a.result);plan=read(R/'PLAN.json');context=read(S/'BUILD_CONTEXT.json');need(result['status']=='PASS_FOUR_COMPLETE_GROUPED_SAME32768_FACTS_AND_INDEPENDENT_TYPE_AXIOM_AUDIT'and result['all_workers_drained']and not result['failures']and not result['pending'],'complete exact bounded experiment');need({str(x['case'])for x in result['records']}=={'6','0','2500','47','Independent'}and len(result['records'])==5,'exact four-plus-audit universe');config={r['chunk']:r for r in plan['config']};checked=[]
for item in result['records']:
 case=item['case'];q=Path(item['receipt']);r=read(q);need(sha(q)==item['receipt_sha256']and r['status']=='COMPILED'and r['returncode']==0 and r['module']==item['module'],'actual accepted compiler receipt');need(sha(r['source'])==r['source_sha256']==item['source_sha256']==sha(q.parent/'source.lean'),'actual source/snapshot identity');need(sha(Path(r['command'][-1]))==r['object_sha256']==item['object_sha256'],'current object identity');need(r['compiler_sha256']==context['compiler_sha256']and r['generic_dependency_context_sha256']==sha(S/'BUILD_CONTEXT.json'),'fixed compiler/context');need(r['memory_limit_bytes']==96*1024**3 and set(r['affinity'])<={16,18},'actual profile resources')
 for f,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(q.parent/f)==r[key],'actual output identity')
 text=(q.parent/'stdout').read_text();source=Path(r['source']).read_text()
 if case=='Independent':
  names=[config[k]['namespace']+'.part_grouped'for k in [6,0,2500,47]]
  for k in config:need(f'example : allFrom (checkEntry nodes gaps gapCount) {k*32768} 32768=true := {config[k]["namespace"]}.part_grouped'in source,'independent exact full type')
 else:
  need(case in config and config[case]['module']==item['module']and config[case]['source_sha256']==r['source_sha256'],'exact fixed case source');need('import RamanujanPV.HighTransitionCount.Data'in source and 'import RamanujanPV.HighTransitionCount.Check'not in source,'no original monolithic proof reused');need(f'theorem part_grouped : allFrom (checkEntry nodes gaps gapCount) {case*32768} 32768=true'in source,'same original full predicate')
  for i in range(8):need(f'theorem sub_{i} : allFrom (checkEntry nodes gaps gapCount) {case*32768+i*4096} 4096=true := by decide +kernel'in source,'every unchanged4096 predicate')
  names=[config[case]['namespace']+'.'+name for name in ['append','append_checked']+[f'sub_{i}'for i in range(8)]+['part_grouped']]
 for name in names:need(f"'{name}' does not depend on any axioms"in text,'every compulsory actual numerical/composition fact hasemptyaxioms')
 checked.append(dict(module=item['module'],receipt=str(q),receipt_sha256=sha(q),source=r['source'],source_sha256=r['source_sha256'],object=r['command'][-1],object_sha256=r['object_sha256'],seconds=r['elapsed_seconds'],CPU_seconds=item['CPU_seconds'],actual_peak_RSS_bytes=item['peak_RSS_bytes'],observed_VmPeak_bytes=item['max_vm'],observed_VmPeak_is_lower_bound=True,observed_compiler=item.get('observed_compiler'),mandatory_empty_axiom_facts=names))
before=read(R/'BASELINE_BEFORE.json');after=read(R/'BASELINE_AFTER.json');need(before==after==result['baseline_before_after']and all(sha(p)==h for p,h in before.items()),'same original sources/Data before/after')
readback=dict(status='PASS_INDEPENDENT_FOUR_GROUPED_FULL_TYPES_EMPTY_AXIOMS_SOURCE_OBJECT_RESOURCES',python_optimization=sys.flags.optimize,result_sha256=sha(a.result),plan_sha256=sha(R/'PLAN.json'),selection_rule='Parent/root explicitly selected knownoutlier0006, firstreference0000, latereference2500 and still-runningoutlier0047. Intentional4of2768 nonrandom scope; no population-wide performance claim.',records=checked,actual_end_to_end_wall_seconds=result['seconds'],sampled_aggregate_RSS_peak_bytes=result['sampled_aggregate_RSS_peak_bytes'],sampled_aggregate_PSS_peak_bytes=result['sampled_aggregate_PSS_peak_bytes'],sampling_gap='V1 du failed on atomically renamed main RUN_STATE.pending. First6 proof continued independently and accepted. Its VM observation and aggregate trace have a gap; complete per-process GNUtimeRSS/CPU receipts remain.',original_source_Data_unchanged=True,main_campaign_unmodified=True,no_new_PV_algorithm_claim=True,original47_runtime_is_pending_right_censored=True)
need(not a.out.exists(),'fresh atomic readback');tmp=a.out.with_suffix(a.out.suffix+'.tmp');tmp.write_text(json.dumps(readback,indent=2)+'\n');tmp.replace(a.out);print(json.dumps(dict(status=readback['status'],optimization=sys.flags.optimize,cases=4,actual_full_fact_count=4)))
