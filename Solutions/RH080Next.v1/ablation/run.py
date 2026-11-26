#!/usr/bin/env python3
"""Execute separate matched transfer sessions only after exact readiness gates."""
from pathlib import Path
import argparse,concurrent.futures,importlib.util,json,sys
HERE=Path(__file__).resolve().parent;D=Path('/data/ivy-rh080-next-20261125');RESULTS=D/'exposure-matched-v2';RESULTS.mkdir(exist_ok=True)
spec=importlib.util.spec_from_file_location('rh080_new_transfer_support',HERE/'run_support.py');core=importlib.util.module_from_spec(spec);spec.loader.exec_module(core);core.HERE=HERE;core.DATA=D
p=argparse.ArgumentParser(allow_abbrev=False);group=p.add_mutually_exclusive_group(required=True);group.add_argument('--fixture-only',action='store_true');group.add_argument('--check-research-locks-only',action='store_true');group.add_argument('--research',action='store_true');p.add_argument('--fixture-attempt',type=int,default=1);a=p.parse_args();core.need(1<=a.fixture_attempt<=9,'Bounded fresh fixture attempt');rows=core.load(HERE/'PREPARED_RUNTIMES_v2.json')['trials'];core.need(len(rows)==16,'Fixed trial universe');mode='normal'if not sys.flags.optimize else'O'*sys.flags.optimize

def check_proof_fixture(directory,lock):
 data=core.load(Path(core.load(lock)['out'])/'submission/PROOF_IMPORTS.json');core.need(data['status']=='PASS_ACTUAL_ASSIGNED_PROOF_IMPORT_MANIPULATION','Actual assigned exposure not checked');core.need(data['mode']==core.load(lock)['condition'],'Wrong assigned exposure');return data

if a.fixture_only:
 selected=rows if mode=='normal'else list({x['condition']:x for x in rows}.values())
 def one(pair):
  slot,row=pair;original=Path(row['directory'])
  if mode=='normal':
   result=core.one(row,slot,True,a.fixture_attempt);lock=Path(core.load(original/'PREFLIGHT.json')['fixture_lock_path']);check_proof_fixture(original,lock);return result
  directory=original.parent.parent/('optimization-'+mode)/row['trial'];directory.mkdir(parents=True);lock=core.load(Path(row['fixture_lock']));lock['out']=str(directory/'fixture-v1');path=directory/'FIXTURE_LOCK.json';core.save(path,lock);core.launch(path,True,slot,row['trial']+'-fixture-'+mode);core.accept_fixture(directory,path);check_proof_fixture(directory,path);return {'trial':row['trial'],'condition':row['condition'],'mode':mode,'status':'PASS_ACTUAL_OPTIMIZED_EXPOSURE_FIXTURE','preflight':core.pin(directory/'PREFLIGHT.json')}
 results=[]
 for start in range(0,len(selected),4):
  with concurrent.futures.ThreadPoolExecutor(max_workers=4)as pool:results.extend(pool.map(one,enumerate(selected[start:start+4])))
 core.save(RESULTS/('EXPOSURE_FIXTURES_'+mode+'.json'),{'status':'PASS_ALL_ASSIGNED_ACTUAL_FIXTURES_NO_INFERENCE','mode':mode,'cases':results,'model_calls':0});print('PASS_FIXTURES',mode,len(results));raise SystemExit(0)

if a.check_research_locks_only:
 results=[]
 for row in rows:
  directory=Path(row['directory']);preflight=directory/'PREFLIGHT.json';fixture_path=Path(core.load(preflight)['fixture_lock_path']);core.accept_fixture(directory,fixture_path);check_proof_fixture(directory,fixture_path);lock=core.load(fixture_path);protocol=core.load(HERE/'PROTOCOL.json');lock.update(fixture=False,out=str(directory/'research-v1'),preflight=core.pin(preflight),model=protocol['model']['alias'],effort=protocol['model']['reasoning_effort'],resources=protocol['budgets'],corpus_freeze=core.pin(HERE/'CORPUS_MANIFEST.json'));path=directory/('RESEARCH_LOCK_PREFLIGHT_'+mode+'.json');core.save(path,lock);command=[sys.executable]+([]if mode=='normal'else['-'+mode])+[str(HERE/'native_trial.py'),'--lock',str(path),'--check-only'];result=core.subprocess.run(command,capture_output=True,text=True);core.need(result.returncode==0,'Actual research-lock route failed');results.append({'trial':row['trial'],'returncode':result.returncode,'command':command,'stdout':result.stdout,'stderr':result.stderr})
 core.save(RESULTS/('EXPOSURE_RESEARCH_LOCKS_'+mode+'.json'),{'status':'PASS_ALL16_RESEARCH_LOCKS_NO_INFERENCE','mode':mode,'cases':results,'model_calls':0});print('PASS_LOCKS',mode,len(results));raise SystemExit(0)

core.need(mode=='normal','One exact normal controller for recorded research');ready=core.load(HERE/'READINESS.json');core.need(ready['status']=='READY_MATCHED16_ACTUAL_EXPOSURES_CHECKED_BEFORE_INFERENCE','Missing actual readiness')
for row in ready['checks']:core.need(core.sha(row['path'])==row['sha256'],'Readiness evidence changed')
core.need(ready['adapter_sha256']==core.sha(HERE/'native_trial.py')and ready['runner_sha256']==core.sha(Path(__file__))and ready['support_sha256']==core.sha(HERE/'run_support.py')and ready['fixture_sha256']==core.sha(HERE/'proof_fixture.py'),'Reviewed execution route changed')
results=[]
for start in range(0,16,4):
 block=rows[start:start+4];core.need(len({x['block']for x in block})==1 and len({x['condition']for x in block})==4,'Unmatched experimental block')
 with concurrent.futures.ThreadPoolExecutor(max_workers=4)as pool:result=list(pool.map(lambda pair:core.one(pair[1],pair[0],False,4),enumerate(block)))
 results.extend(result);core.save(RESULTS/('EXPOSURE_RESEARCH_BLOCK_'+str(start//4)+'.json'),{'status':'EXECUTED_NEW_TRANSFER_BLOCK_NOT_MATHEMATICAL_SCORING','rows':result,'original28_unchanged':True});print('COMPLETED_BLOCK',start//4,flush=True)
core.save(RESULTS/'EXPOSURE_RESEARCH_EXECUTION.json',{'status':'EXECUTED16_SEPARATE_PROSPECTIVE_TRANSFER_TRIALS_SCORING_PENDING','rows':results,'original28_unchanged':True});print('ALL16_EXECUTED_NOT_YET_MATH_SCORED')
