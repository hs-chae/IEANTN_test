#!/usr/bin/env python3
"""Clean-directory full scalar source-PV recipe; no old application objects.
The ordinary native backend proposes data, not formal prime-count evidence.
"""
from pathlib import Path
import argparse,json,os,subprocess,sys,time
from execute_full_scalar_certificate import need,read,sha
S=Path(__file__).resolve().parents[1]
def main():
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--cpus',default=','.join(map(str,range(52,64))));p.add_argument('--jobs',type=int,default=12);p.add_argument('--profile32',action='store_true');p.add_argument('--plan-only',action='store_true');p.add_argument('--skip-native-count-challenge',action='store_true');a=p.parse_args()
 needed=set(range(16,32))
 if not a.skip_native_count_challenge:needed.update(range(32,48))
 need(needed<=os.sched_getaffinity(0),'native recipe requiresavailableCPU16..31 and optional32..47; no workstarted')
 c=read(a.context);need(sha(c['compiler'])==c['compiler_sha256'],'same pinned compiler');out=a.out.resolve();need(not out.exists()and out.parent.is_dir(),'fresh root with existing parent');cpus=list(map(int,a.cpus.split(',')));need(len(cpus)==len(set(cpus))and len(cpus)>=a.jobs and 1<=a.jobs<=12 and set(cpus)<=os.sched_getaffinity(0),'actual bounded distinct CPUs');out.mkdir();(out/'logs').mkdir();core=out/'core';context=out/'CONTEXT.json';c['new_application_object_root']=str(core/'lean');context.write_text(json.dumps(c,indent=2)+'\n');profile=out/'MODEL_MEMORY_PROFILES.json';profile.write_text(json.dumps({'exact':{'RamanujanPV.FiniteLogSource':96,'RamanujanPV.FiniteCellSource':96},'prefix':{}},indent=2)+'\n')
 raw=out/'native/ivy-ramanujan-source-pv-20261119';study=out/'native-study';run=study/'evidence/finite-actual-1490000000000/RUN.json';old=core/'original-scalars';oldrun=core/'original-scalars-run';new=core/'source-scalars';newrun=core/'source-scalars-run';basejobs=min(4,a.jobs);basecpus=','.join(map(str,cpus[:basejobs]));allcpus=','.join(map(str,cpus));commands=[]
 def add(label,args):commands.append(dict(label=label,command=[sys.executable,*map(str,args)]))
 add('native_data',[S/'scripts/reproduce_numerics.py','--scratch',raw,'--study',study,'--skip-exhaustive-count-check'])
 if not a.skip_native_count_challenge:add('ordinary_native_count_challenge',[S/'scripts/check_finite_independent.py','--study',study,'--scratch',raw,'--run','finite-actual-1490000000000','--workers','8'])
 add('fresh_all_source_models',[S/'scripts/reproduce_profiled_closure.py','--context',context,'--out',core,'--profile-json',profile,'--root','RamanujanPV.FullFiniteSourcePV','--theorem','RamanujanPV.FullFiniteSourcePV.row_source','--memory-gib','48','--aggregate-gib','300','--jobs',str(basejobs),'--cpus',basecpus])
 gen=[S/'scripts/generate_full_scalar_certificate.py','--run',run,'--certificates',raw/'finite-actual-1490000000000','--out',old,'--name','FullAdaptiveScalars','--rows-per-block','4096','--proof-chunk','512']
 if a.profile32:gen+=['--limit-rows','32']
 add('original_exact_scalar_inputs',gen)
 original=[S/'scripts/execute_full_scalar_certificate.py','--manifest',old/'PROPOSAL.json','--native-run',run,'--context',context,'--out',oldrun,'--jobs',str(a.jobs),'--memory-gib','24','--cpus',allcpus]
 if a.profile32:original+=['--allow-profile']
 add('original_kernel_math',original)
 generate=[S/'scripts/generate_full_source_rows.py','--original-manifest',old/'PROPOSAL.json','--original-result',oldrun/'RESULT.json','--out',new,'--name','FullAdaptiveSourcePV','--context',context]
 if a.profile32:generate+=['--allow-profile']
 add('source_row_proposal',generate)
 execute=[S/'scripts/execute_full_source_rows.py','--manifest',new/'PROPOSAL.json','--out',newrun,'--context',context,'--jobs',str(a.jobs),'--memory-gib','24','--cpus',allcpus]
 if a.profile32:execute+=['--allow-profile']
 add('all_actual_C_row_sources',execute)
 for flag,label in [([], 'normal'),(['-O'],'opt'),(['-OO'],'oo')]:
  add('final_readback_'+label,[*flag,S/'scripts/execute_full_source_rows.py','--check',newrun/'RESULT.json'])
 add('actual_CLI_controls',[S/'scripts/test_full_source_cli.py','--result',newrun/'RESULT.json','--out',core/'source-cli-controls'])
 if not a.profile32:add('ordinary_actual_C_observation',[S/'scripts/observe_full_source_rows.py','--original-manifest',old/'PROPOSAL.json','--context',context,'--out',core/'ordinary-C-observation','--cpu',str(cpus[0])])
 plan=dict(status='PLANNED_CLEAN_SOURCE_SCALAR_REPRODUCTION',commands=commands,profile32=a.profile32,original_numeric_target_unchanged=True,prime_counts_formally_proved_here=False,source_generator_random_seeds=None,source_root=str(S),controller_sha256=sha(__file__),input_context_sha256=sha(a.context),context=str(context),new_application_bank=str(core/'lean'),old_application_objects_used=False,original_math_source_out=str(old),source_scalar_out=str(new))
 (out/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
 if a.plan_only:print(json.dumps({'status':plan['status'],'steps':len(commands),'old_application_objects_used':False,'plan':str(out/'PLAN.json')}));return
 started=time.monotonic();records=[]
 for i,item in enumerate(commands):
  with(out/'logs'/f'{i:02d}-{item["label"]}.stdout').open('w')as so,(out/'logs'/f'{i:02d}-{item["label"]}.stderr').open('w')as se:
   t=time.monotonic();child=subprocess.run(item['command'],cwd=S,stdout=so,stderr=se)
  record=dict(label=item['label'],command=item['command'],returncode=child.returncode,seconds=time.monotonic()-t);records.append(record)
  (out/'PROGRESS.json').write_text(json.dumps({'records':records,'seconds':time.monotonic()-started},indent=2)+'\n')
  need(child.returncode==0,'reproduction step failure preserved: '+item['label'])
 result=dict(status='CLEAN_SOURCE_SCALAR_REPRODUCTION_PASS_COUNTS_OPEN',profile32=a.profile32,records=records,seconds=time.monotonic()-started,source_result=str(newrun/'RESULT.json'),source_result_sha256=sha(newrun/'RESULT.json'),prime_counts_formally_proved_here=False,old_application_objects_used=False,plan_sha256=sha(out/'PLAN.json'))
 tmp=out/'RESULT.pending';tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(out/'RESULT.json');print(json.dumps(result))
if __name__=='__main__':main()
