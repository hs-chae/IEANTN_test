#!/usr/bin/env python3
"""After COMPLETE kernel count acceptance, instantiate the existing actual C proof.
The control mode uses only the already closed critical pair and is labelled so.
"""
from pathlib import Path
import argparse,hashlib,json,os,re,subprocess,sys,time
from execute_demand_high_resource import strict_text,check_result,need,STD3
S=Path(__file__).resolve().parents[1]
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return strict_text(Path(path).read_text())
def py(args):return [sys.executable,*(['-'+'O'*sys.flags.optimize]if sys.flags.optimize else[]),*map(str,args)]
def run(args,out,label):
    with(out/(label+'.stdout')).open('w')as so,(out/(label+'.stderr')).open('w')as se:r=subprocess.run(args,cwd=S,stdout=so,stderr=se)
    need(r.returncode==0,'actual source proof failed; retained '+label)
    emitted=read_line=(out/(label+'.stdout')).read_text().strip().splitlines()[-1]
    return Path(json.loads(emitted)['audit'])/'RUN.json'
def audit_receipt(path,module,source,empty):
    c=read(S/'BUILD_CONTEXT.json');r=read(path);folder=path.parent
    need(r['status']=='COMPILED'and r['returncode']==0 and r['module']==module and r['source_unchanged_during_compile']is True,'actual completed source proof')
    need(r['source_sha256']==sha(source)==sha(folder/'source.lean')and r['compiler_sha256']==sha(c['compiler'])and r['generic_dependency_context_sha256']==sha(S/'BUILD_CONTEXT.json'),'actual source/compiler/context')
    for n,k in [('stdout','stdout_sha256'),('stderr','stderr_sha256'),('rusage.txt','rusage_sha256')]:need(sha(folder/n)==r[k],'actual proof logs')
    obj=Path(c['new_application_object_root'])/Path(*module.split('.')).with_suffix('.olean');need(sha(obj)==r['object_sha256'],'actual proof object')
    log=(folder/'stdout').read_text();reports={}
    for symbol in re.findall(r'^#print axioms ([A-Za-z0-9_.]+)',source.read_text(),re.M):
        no=re.search("'"+re.escape(symbol)+"' does not depend on any axioms",log);ax=re.search("'"+re.escape(symbol)+r"' depends on axioms:\s*\[([^\]]*)\]",log,re.S);need(no is not None or ax is not None,'actual dependency report '+symbol);values=[]if no else[v.strip()for v in ax[1].split(',')if v.strip()];need(set(values)<=STD3 and(symbol not in empty or not values),'source proof trust boundary');reports[symbol]=values
    return dict(module=module,source=str(source),source_sha256=sha(source),receipt=str(path),receipt_sha256=sha(path),object_sha256=sha(obj),axioms=reports)
def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--kernel-result',type=Path);p.add_argument('--out',type=Path,required=True);p.add_argument('--cpus',default='96');p.add_argument('--memory-gib',type=int,default=256);p.add_argument('--control',action='store_true');a=p.parse_args()
    need(a.control==(a.kernel_result is None),'real mode requires complete kernel RESULT; control has no fake high RESULT');ctx=read(S/'BUILD_CONTEXT.json');owned=Path(ctx['new_application_object_root']).resolve().parent;out=a.out.resolve();need(out.is_relative_to(owned)and not out.exists(),'fresh owned source-stage output');need(1<=a.memory_gib<=300,'authorized per-run memory')
    kernel=None
    if not a.control:
        kernel=check_result(a.kernel_result);need(kernel['expected_pi']==[(1490000000000,55206486339)],'complete exact high target only')
    out.mkdir(parents=True);started=time.monotonic();cfile=S/'c/verified_quotient_count.c';csha=sha(cfile);(out/'verified_quotient_count.c').write_bytes(cfile.read_bytes());prefix='HighTransitionSourceClosed'if not a.control else'HighTransitionSourceControl_'+hashlib.sha256(str(out).encode()).hexdigest()[:10]
    ns='RamanujanPV.'+prefix
    if a.control:
        n=38358837683;value=1644673232;upstream='RamanujanPV.DemandCriticalPair.Final';input_fact='DemandCriticalPair.pi_38358837683'
    else:
        n=1490000000000;value=55206486339;upstream='RamanujanPV.HighTransitionCount.Final';input_fact='HighTransitionCount.pi_1490000000000'
    root=out/'source';source=root/'RamanujanPV'/(prefix+'.lean');source.parent.mkdir(parents=True)
    body=f'''/- Source count adapter. No physical native caller or full Ramanujan ray is asserted. -/
import {upstream}
import RamanujanPV.QuotientCountRealization
namespace {ns}
set_option autoImplicit false
def currentSource : String := include_str {json.dumps(str(cfile))}
theorem current_source_bytes : QuotientCSourceV2.actualSource=currentSource := by decide +kernel
theorem source_execution : QuotientCCell.SourceExecution {n} {value} :=
  QuotientCountRealization.source_execution_from_kernel_value (by norm_num) (by norm_num) {input_fact}
theorem natural_count_from_source : Nat.primeCounting {n}={value} :=
  QuotientCCell.source_execution_count source_execution
theorem ieantn_count_from_source : IEANTN.primeCounting ({n}:ℝ)={value} := by
  calc
    IEANTN.primeCounting ({n}:ℝ)=(Nat.primeCounting {n}:ℝ) := primeCounting_nat {n}
    _={value} := by exact_mod_cast natural_count_from_source
theorem source_linked_ieantn_count :
    LCMSourcePV.RestrictedC.SourceCorresponds QuotientCSourceV2.render currentSource () ∧
    QuotientCCell.SourceExecution {n} {value} ∧ IEANTN.primeCounting ({n}:ℝ)={value} := by
  refine ⟨?_,source_execution,ieantn_count_from_source⟩
  rw [←current_source_bytes]
  exact QuotientCSourceV2.actual_source_checked
#print axioms {ns}.current_source_bytes
#print axioms {ns}.source_execution
#print axioms {ns}.natural_count_from_source
#print axioms {ns}.ieantn_count_from_source
#print axioms {ns}.source_linked_ieantn_count
end {ns}
''';source.write_text(body);command=py([S/'scripts/compile_lean.py',ns,'--source-root',root,'--audit-root',out/'audit','--cpus',a.cpus,'--memory-gib',a.memory_gib]);receipt=run(command,out,'source-stage');records=[audit_receipt(receipt,ns,source,{ns+'.current_source_bytes'})]
    audit_name=ns+'Audit';audit_source=root/'RamanujanPV'/(prefix+'Audit.lean');required=[ns+'.current_source_bytes',ns+'.source_execution',ns+'.natural_count_from_source',ns+'.ieantn_count_from_source','RamanujanPV.QuotientCountRealization.source_execution_from_kernel_value','RamanujanPV.QuotientCCell.source_execution_count','RamanujanPV.QuotientCFunction.linked_function_refines','RamanujanPV.QuotientCFunction.completed_execution_correct','RamanujanPV.QuotientCSourceV2.actual_source_checked','RamanujanPV.QuotientCInit.initialization_loop','RamanujanPV.QuotientCWhole.outer_for_exec','RamanujanPV.QuotientCLarge.large_for_exec','RamanujanPV.QuotientCSmallLoop.small_branch_exec']
    audit_source.write_text('import '+ns+'\nimport Lean.Util.FoldConsts\nopen Lean Elab Command\nrun_cmd do\n  let env ← getEnv\n  let root := `'+ns+'.source_linked_ieantn_count\n  let required := ['+','.join('`'+v for v in required)+']\n  let mut seen : NameSet := ({} : NameSet).insert root\n  let mut pending := [root]\n  while !pending.isEmpty do\n    let name := pending.head!\n    pending := pending.tail!\n    let some info := env.find? name | throwError "Missing inspected constant {name}"\n    if name == `sorryAx || name == `Lean.ofReduceBool then throwError "Forbidden execution axiom {name}"\n    for dependency in info.getUsedConstantsAsSet.toList do\n      if !seen.contains dependency then\n        seen := seen.insert dependency\n        pending := dependency::pending\n  for name in required do\n    unless seen.contains name do throwError "Required actual source path absent {name}"\n    logInfo m!"REQUIRED_SOURCE_PATH_PRESENT {name}"\n  logInfo m!"COMPLETE_HIGH_SOURCE_CLOSURE {seen.size}"\nexample : RamanujanPV.QuotientCCell.SourceExecution '+str(n)+' '+str(value)+' := '+ns+'.source_execution\nexample : IEANTN.primeCounting ('+str(n)+':ℝ)='+str(value)+' := '+ns+'.ieantn_count_from_source\n#print axioms '+ns+'.source_linked_ieantn_count\n')
    audit_command=py([S/'scripts/compile_lean.py',audit_name,'--source-root',root,'--audit-root',out/'dependency-audit','--cpus',a.cpus,'--memory-gib',a.memory_gib]);r=run(audit_command,out,'source-audit');records.append(audit_receipt(r,audit_name,audit_source,set()));need('COMPLETE_HIGH_SOURCE_CLOSURE 'in(r.parent/'stdout').read_text(),'actual complete source closure audit');need(sha(cfile)==csha,'actual C bytes unchanged across proof compilation')
    result=dict(status='COMPLETE_SOURCE_LINKED_IEANTN_COUNT_INSTANCE'if not a.control else'CONTROL_EXISTING_CRITICAL_SOURCE_INSTANCE_ONLY',control=a.control,N=n,value=value,kernel_readback=kernel,kernel_result_sha256=sha(a.kernel_result)if a.kernel_result else None,source_first_PV=True,physical_native_process_or_driver_verified=False,full_finite_Ramanujan_range_completed=False,current_c_source_sha256=csha,controller_sha256=sha(__file__),seconds=time.monotonic()-started,records=records,required_source_paths=required,commands=[command,audit_command],remaining_trust='Pinned Lean kernel/compiler/core runtime, precise modeled C integers/owned-memory contracts, and documented native compiler/runtime/OS/hardware contracts when relating physical executions. This theorem proves modeled source execution and actual IEANTN count; no physical new caller/stdout association.')
    stage=out/'RESULT.json.pending';stage.write_text(json.dumps(result,indent=2,allow_nan=False)+'\n');stage.replace(out/'RESULT.json');print(json.dumps({'status':result['status'],'N':n,'value':value,'seconds':result['seconds']}))
if __name__=='__main__':main()
