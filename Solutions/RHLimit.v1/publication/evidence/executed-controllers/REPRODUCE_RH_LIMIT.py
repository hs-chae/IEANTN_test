#!/usr/bin/env python3
"""Rebuild all RHLimit proof routes and regenerate the source-linked C workload.

Run from a verified restored package with a pinned relocated generic context.
Every application/LeanCert proof object is generated in fresh owned scratch.
"""
from pathlib import Path
import argparse,os,shutil,subprocess,sys,time
sys.dont_write_bytecode=True
from prepare_bundle import need,strict,safe,sha,save,verify

def main():
 here=Path(__file__).resolve().parent;net=here/'network';s=net/'Solutions/RHLimit.v1'
 p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--context',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--check',action='store_true');a=p.parse_args()
 need(sys.version_info>=(3,11),'Python3.11 or newer required');verify(here);out=a.out.resolve();need(not out.exists()and not out.is_relative_to(here),'fresh scratch outside package required')
 for cmd in ['git','gcc']:need(shutil.which(cmd),'missing system prerequisite:'+cmd)
 need(Path('/usr/bin/time').is_file(),'GNUtime required');ctx=strict(a.context);reference=strict(net/'Solutions/RHContinuation.v1/scripts/GENERIC_CONTEXT.json')
 need(sha(Path(ctx['compiler']))==ctx['compiler_sha256']==reference['compiler_sha256'],'exact compiler identity')
 need([(x['name'],x['revision'])for x in ctx['generic_dependencies']]==[(x['name'],x['revision'])for x in reference['generic_dependencies']],'generic source pins')
 for d in ctx['generic_dependencies']:
  need(subprocess.check_output(['git','rev-parse','HEAD'],cwd=d['path'],text=True).strip()==d['revision'],'generic checkout revision')
  need(subprocess.run(['git','diff','--quiet','HEAD','--'],cwd=d['path']).returncode==0,'modified pinned generic source')
 final=strict(here/'REPLAY_ROUTES.json');need(final['schema']=='RH_LIMIT_FINAL_CANONICAL_REPLAY_ROUTE_V1','canonical route schema');can=final['canonical'];script=here/safe(can['script']);need(script.is_file(),'missing final canonical replay script')
 need(isinstance(can['argv'],list)and all(isinstance(x,str)for x in can['argv']),'structured canonical arguments');need(can['expected_status']and safe(can['receipt']),'canonical final gate')
 commands=[('pi',[str(s/'scripts/reproduce_pi_complete.py')], 'PASS_COLD_ALL_261_SOURCE_MODULES_AND_FINAL_PI_CONSUMERS'),
 ('spectral',[str(s/'spectral/reproduce_cold_append.py')],'PASS_COLD261_PLUS_ALL55_SPECTRAL_SOURCES_AND_ACTUAL_CONSUMERS'),
 ('analytic-box',[str(s/'analytic/reproduce.py')],'PASS_ACTUAL_STIELTJES_CLOSURE_AND_SOURCE_LINKED_FOUR_INPUT_PNT'),
 ('analytic-absolute',[str(s/'analytic/reproduce_absolute.py')],'PASS_SOURCE_LINKED_ACTUAL_OCTIC_ABSOLUTE_STIELTJES'),
 ('octic',[str(s/'octic/reproduce.py')],'PASS_COMPLETE_SAME_SOURCE111_PLUS_FOUR_CLOSED_OCTIC_CONTRACTS')]
 for _,cmd,_ in commands:need(Path(cmd[0]).is_file(),'active proof route missing:'+cmd[0])
 env=os.environ.copy();env['IEANTN_GENERIC_CONTEXT']=str(a.context.resolve());env['PYTHONDONTWRITEBYTECODE']='1';env.pop('LEAN_PATH',None);env.pop('PYTHONOPTIMIZE',None)
 out.mkdir(parents=True);start=time.monotonic();receipt={'status':'RUNNING','controller_sha256':sha(Path(__file__)),'bundle_manifest_sha256':sha(here/'BUNDLE_MANIFEST.json'),'generic_context_sha256':sha(a.context),'steps':[]};save(out/'RESULT.json',receipt)
 if a.check:
  # The bank-dependent spectral/canonical checks run only after their fresh basis exists.
  for label,cmd,_ in commands:
   if label=='spectral':continue
   cp=subprocess.run([sys.executable,*cmd,'--out',str(out/(label+'-unused')),'--check'],env=env,text=True,capture_output=True)
   (out/(label+'.stdout')).write_text(cp.stdout);(out/(label+'.stderr')).write_text(cp.stderr);need(cp.returncode==0,'child source/dependency preflight:'+label)
  receipt.update(status='PASS_PACKAGE_AND_FOUR_BANK_FREE_SOURCE_PREFLIGHTS_ONLY',mathematical_replay_performed=False,bank_dependent_routes_pending=['spectral','canonical']);save(out/'RESULT.json',receipt);print(receipt['status']);return
 try:
  for label,cmd,expected in commands:
   dest=out/label;args=[sys.executable,*cmd,'--out',str(dest)]
   if label=='spectral':args+=['--basis',str(out/'pi')]
   cp=subprocess.run(args,env=env,text=True,capture_output=True);(out/(label+'.stdout')).write_text(cp.stdout);(out/(label+'.stderr')).write_text(cp.stderr);need(cp.returncode==0,'source replay failed:'+label)
   result=dest/'RESULT.json';j=strict(result);need(j['status']==expected,'unexpected mathematical result:'+label)
   receipt['steps'].append({'component':label,'command':args,'returncode':cp.returncode,'status':j['status'],'receipt_sha256':sha(result)});save(out/'RESULT.json',receipt);print('PASS',label,flush=True)
  replacements={'{pi}':str(out/'pi'),'{spectral}':str(out/'spectral'),'{analytic-box}':str(out/'analytic-box'),'{analytic-absolute}':str(out/'analytic-absolute'),'{octic}':str(out/'octic'),'{out}':str(out/'canonical'),'{context}':str(a.context.resolve()),'{network}':str(net)}
  args=[]
  for raw in can['argv']:
   value=raw
   for token,repl in replacements.items():value=value.replace(token,repl)
   need('{'not in value and'}'not in value,'unknown canonical argument placeholder');args.append(value)
  cmd=[sys.executable,str(script),*args];cp=subprocess.run(cmd,env=env,text=True,capture_output=True);(out/'canonical.stdout').write_text(cp.stdout);(out/'canonical.stderr').write_text(cp.stderr);need(cp.returncode==0,'final canonical replay failed')
  result=out/'canonical'/safe(can['receipt']);j=strict(result);need(j['status']==can['expected_status'],'canonical theorem gate')
  receipt['steps'].append({'component':'canonical','command':cmd,'returncode':0,'status':j['status'],'receipt_sha256':sha(result)})
  verify(here);receipt.update(status='PASS_ALL_RH_LIMIT_FRESH_SOURCE_NUMERICAL_AND_CANONICAL_ROUTES',seconds=time.monotonic()-start,whole_pipeline_source_first_PV=False,trust='Only specifically identified actualC execution components are source-firstPV. New interval/kernel proofs are ordinary kernel mathematics; RH, literature and open analytic inputs remain explicit.')
  save(out/'RESULT.json',receipt);print(receipt['status'])
 except BaseException as ex:
  receipt.update(status='FAIL_OR_PARTIAL_NO_FINAL_REPLAY_ACCEPTANCE',error=str(ex),seconds=time.monotonic()-start);save(out/'RESULT.json',receipt);raise
if __name__=='__main__':main()
