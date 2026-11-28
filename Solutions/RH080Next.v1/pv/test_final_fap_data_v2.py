#!/usr/bin/env python3
"""Actual all-mode source/data preparation and snapshot-verification controls.
No Lean compilation or numerical program is executed by these fixtures.
"""
from __future__ import annotations
import argparse,hashlib,json,os,shutil,subprocess,sys
from pathlib import Path
from final_fap_source_data_v2 import read_json,need,sha,stage_data,verify_data
HERE=Path(__file__).resolve().parent

def put(path,value):path.write_text(json.dumps(value,indent=2)+'\n')
def run_child(key,command,root,success,reason=None):
    r=subprocess.run(command,capture_output=True,timeout=180,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1',GIT_OPTIONAL_LOCKS='0'))
    (root/(key+'.stdout')).write_bytes(r.stdout);(root/(key+'.stderr')).write_bytes(r.stderr)
    need((r.returncode==0)==success,'Wrong actual data-control CLI outcome '+key)
    if reason:need(reason.encode()in r.stderr,'Wrong data-control rejection reason '+key)
    return dict(case=key,command=command,exitcode=r.returncode,intended_error=reason)

def stage_check(root,inventory):
    inv=read_json(inventory);need(not root.exists(),'Fresh staging fixture required');root.mkdir();source=root/'source';source.mkdir();rows=[]
    for x in inv['full_dependency_cone']:
        target=source/(x['module'].replace('.','/')+'.lean');target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(x['source_origin'],target)
        rows.append(dict(x,origin=x['source_origin'],snapshot=str(target)))
    staged=stage_data(source,inv['literal_data']);verify_data(source,staged,rows,inv['literal_data'])
    put(root/'STAGE.json',dict(source_rows=rows,staged_data=staged,inventory_data=inv['literal_data']))
    print(json.dumps(dict(status='PASS_LITERAL_DATA_STAGING_ONLY',modules=len(rows),files=len(staged),bytes=sum(x['bytes']for x in staged))))

def verify_stage(root):
    meta=read_json(root/'STAGE.json');verify_data(root/'source',meta['staged_data'],meta['source_rows'],meta['inventory_data'])
    print(json.dumps(dict(status='PASS_LITERAL_STAGED_DATA_VERIFICATION_ONLY',files=len(meta['staged_data']))))

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--controls',type=Path);ap.add_argument('--repository',type=Path,default=HERE.parents[2]);ap.add_argument('--context',type=Path);ap.add_argument('--scratch-root',type=Path);ap.add_argument('--stage-check',type=Path);ap.add_argument('--inventory',type=Path);ap.add_argument('--verify-stage',type=Path)
    a=ap.parse_args()
    if a.stage_check:need(a.inventory is not None,'Inventory required');stage_check(a.stage_check,a.inventory);return
    if a.verify_stage:verify_stage(a.verify_stage);return
    need(a.controls and a.context and a.scratch_root,'controls/context/scratch-root required');need(not a.controls.exists(),'Fresh controls required');root=a.controls;root.mkdir();repo=a.repository.resolve();inputs=read_json(HERE/'evidence/FINAL_FAP_SOURCE_COLD_INPUTS_V2.json');records=[];prepared=[];stages=[]
    def prep_command(flags,destination,source=repo,inputPath=HERE/'evidence/FINAL_FAP_SOURCE_COLD_INPUTS_V2.json'):
        return [sys.executable,*flags,str(HERE/'reproduce_final_fap_source_v2.py'),'--context',str(a.context),'--run',str(destination),'--repository',str(source),'--inputs',str(inputPath),'--scratch-root',str(a.scratch_root),'--workers','2','--worker-memory-gib','128','--prepare-only']
    modes=[([], 'normal'),(['-O'],'O'),(['-OO'],'OO')]
    for flags,name in modes:
        destination=root/('positive-'+name);records.append(run_child('positive-'+name,prep_command(flags,destination),root,True));inventory=destination.with_name(destination.name+'-inputs')/'SOURCE_INVENTORY.json';prepared.append(inventory)
        stage=root/('stage-'+name);records.append(run_child('stage-'+name,[sys.executable,*flags,str(Path(__file__)), '--stage-check',str(stage),'--inventory',str(inventory)],root,True));stages.append(stage)
    # A minimal private repository contains copies, never writable links to original inputs.
    clone=root/'repository';clone.mkdir()
    for row in inputs['sources']+inputs['data']:
        target=clone/row['path'];target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(repo/row['path'],target)
    original_data={row['path']:sha(repo/row['path'])for row in inputs['data']}
    prep_cases={'missing-data':'Missing literal data','mutated-data':'Literal data hash differs','traversal-input':'Unsafe relative literal input path','traversal-destination':'Unsafe relative literal destination','duplicate-data':'Duplicate literal data identity','omitted-data':'Missing/extra literal data universe','wrong-dimensions':'Literal loader identity/dimensions differ','duplicate-json':'Duplicate JSON key'}
    first=inputs['data'][0];original=(clone/first['path']).read_bytes()
    for case,reason in prep_cases.items():
        data=json.loads(json.dumps(inputs));path=root/(case+'-inputs.json');source=repo
        if case=='missing-data':source=clone;(clone/first['path']).unlink()
        elif case=='mutated-data':source=clone;raw=bytearray(original);raw[0]=ord('7')if raw[0]!=ord('7')else ord('6');(clone/first['path']).write_bytes(raw)
        elif case=='traversal-input':data['data'][0]['path']='../escape.csv'
        elif case=='traversal-destination':data['data'][0]['destination']='../escape.csv'
        elif case=='duplicate-data':data['data'][1]=dict(data['data'][0])
        elif case=='omitted-data':data['data'].pop()
        elif case=='wrong-dimensions':
            key='count'if 'count'in data['data'][0]else'width';data['data'][0][key]+=1
        put(path,data)
        if case=='duplicate-json':path.write_text('{"kind":"SOURCE_AND_LITERAL_DATA_IDENTITIES_NO_APPLICATION_PROOF_CACHE","kind":"DUPLICATE"}')
        for flags,name in modes:
            destination=root/(case+'-'+name);records.append(run_child('prep-'+case+'-'+name,prep_command(flags,destination,source,path),root,False,reason));need(not destination.exists()and not destination.with_name(destination.name+'-inputs').exists(),'Rejected preparation published inputs')
        if source==clone:(clone/first['path']).write_bytes(original)
    final_cases={'missing-snapshot':'Missing literal data','mutated-snapshot':'Literal data hash differs','traversal-snapshot':'Literal loader identity/dimensions differ','duplicate-snapshot':'Duplicate literal data identity','wrong-snapshot-owner':'Literal snapshot/owning-source association differs'}
    for case,reason in final_cases.items():
        fixture=root/case;shutil.copytree(stages[0],fixture);meta=read_json(fixture/'STAGE.json');target=fixture/'source'/meta['staged_data'][0]['destination']
        if case=='missing-snapshot':target.unlink()
        elif case=='mutated-snapshot':raw=bytearray(target.read_bytes());raw[0]=ord('8')if raw[0]!=ord('8')else ord('6');target.write_bytes(raw)
        elif case=='traversal-snapshot':meta['staged_data'][0]['destination']='../escape.csv';put(fixture/'STAGE.json',meta)
        elif case=='duplicate-snapshot':meta['staged_data'][1]=dict(meta['staged_data'][0]);put(fixture/'STAGE.json',meta)
        else:meta['staged_data'][0]['snapshot']=str(Path('/elsewhere')/Path(meta['staged_data'][0]['snapshot']).name);put(fixture/'STAGE.json',meta)
        for flags,name in modes:records.append(run_child('verify-'+case+'-'+name,[sys.executable,*flags,str(Path(__file__)),'--verify-stage',str(fixture)],root,False,reason))
        shutil.rmtree(fixture)
    for path,digest in original_data.items():need(sha(repo/path)==digest,'Original locked literal data changed')
    removed=[str(x)for x in [clone,*stages]]
    for path in [clone,*stages]:need(path.parent==root and not path.is_symlink(),'Fixture cleanup ownership');shutil.rmtree(path)
    record=dict(status='PASS_DATA_AWARE_PREPARATION_AND_FINAL_DATA_CHECKS_ALL_OPTIMIZATIONS',source_modules=681,literal_data_files=34,literal_data_bytes=104208750,prepare_positive_modes=3,stage_verify_positive_modes=3,prepare_negative_cases=len(prep_cases),prepare_negative_rejections=len(prep_cases)*3,final_data_negative_cases=len(final_cases),final_data_negative_rejections=len(final_cases)*3,original_sources_and_data_unchanged=True,regenerable_copied_fixtures_removed=removed,proof_or_native_program_executions=0,controller_sha256=sha(HERE/'reproduce_final_fap_source_v2.py'),cold_controller_sha256=sha(HERE/'reproduce_final_fap_source_cold_v2.py'),helper_sha256=sha(HERE/'final_fap_source_data_v2.py'),inputs_sha256=sha(HERE/'evidence/FINAL_FAP_SOURCE_COLD_INPUTS_V2.json'),cases=records)
    put(root/'RESULT.json',record);print(json.dumps({k:record[k]for k in ['status','prepare_negative_rejections','final_data_negative_rejections','original_sources_and_data_unchanged']}))
if __name__=='__main__':main()
