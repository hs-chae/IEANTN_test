"""Validate successful continuation receipts without relabeling their origin.
The original source-cold run and every interrupted continuation remain immutable.
"""
from pathlib import Path
import os
from reproduce_dual import need,sha,load
import resume_fft_dag_source_cold as original
V1_SHA='04421c858331351ed4e2dbf3bd7e13c3bac10182fb2c14c852fd1567afb5afa8'


def validate_nested_lineage(prefix,candidate,context_path,c,continuations):
    need(sha(Path(original.__file__))==V1_SHA,'Frozen v1 continuation controller changed')
    state=original.validate_prefix(prefix,candidate,context_path,c)
    base=dict(state['successful']);origins={n:prefix for n in base};logical={n:state['logical']for n in base};phases={n:'ORIGINAL_SOURCE_COLD'for n in base}
    inherited=[];skipped=[];seen_paths=set()
    for index,directory in enumerate(continuations,1):
        directory=directory.resolve();need(directory not in seen_paths and directory!=prefix,'Duplicate continuation path');seen_paths.add(directory)
        plan=load(directory/'PLAN.json')
        need(plan['status']=='FROZEN_SOURCE_COLD_LINEAGE_RESUME_NOT_MONOLITHIC_FRESH_NOT_C_PV','Only exact frozen v1 continuation receipts supported')
        need(plan['controller_sha256']==V1_SHA==sha(directory/'resume_driver.executed.py'),'Continuation controller/source identity differs')
        need(plan['original_controller_sha256']==original.ORIGINAL_DRIVER_SHA and sha(directory/'driver.executed.py')==original.ORIGINAL_DRIVER_SHA,'Original controller lineage differs')
        need(plan['original_prefix']==str(prefix) and plan['original_plan_sha256']==sha(prefix/'PLAN.json'),'Continuation is from another original experiment')
        need(plan['original_logical_run']==str(state['logical']) and plan['context_helper_sha256']==original.CONTEXT_HELPER_SHA,'Continuation logical/context lineage differs')
        need(plan['context_sha256']==sha(context_path) and plan['compiler_sha256']==c['compiler_sha256'] and plan['generic_dependencies']==c['generic_dependencies'],'Continuation compiler/context differs')
        need(plan['candidate_plan_sha256']==sha(candidate/'PLAN.json')and plan['proposal']==state['proposal']and plan['sources']==state['plan']['sources']and plan['payloads']==state['proposal']['payloads'],'Continuation candidate/source/data mathematics changed')
        need(plan['source_cold']is False and plan['source_cold_lineage_resume']is True and plan['outside_application_object_cache_used']is False,'Continuation misclassified or imported outside cache')
        need(plan['successful_prefix_modules']==len(base) and plan['fresh_modules_required']==len(state['rows'])-len(base)and set(plan['routes'])==set(base),'Continuation original reuse/fresh scope differs')
        for name,row in state['rows'].items():need(sha(directory/'sources'/row['file'])==row['sha256'],'Continuation source snapshot differs '+name)
        for row in state['proposal']['payloads']:
            path=directory/'sources'/row['file'];need(path.stat().st_size==row['bytes']and sha(path)==row['sha256'],'Continuation fixed literal differs')
        for name,record in base.items():
            route=plan['routes'][name]
            need(route['kind']=='REUSED_SUCCESSFUL_ORIGINAL_SOURCE_COLD_PREFIX'and route['original_receipt_sha256']==sha(prefix/(name+'.COMPILED.json'))and route['object_sha256']==record['object_sha256'],'Continuation reused receipt route differs')
            need(load(directory/(name+'.COMPILED.json'))==record,'Continuation altered original receipt')
            # Exact shared inode plus previously checked content is sufficient;
            # otherwise the same object bytes must still match the original hash.
            old=prefix/'objects'/(name.replace('.','/')+'.olean');current=directory/'objects'/(name.replace('.','/')+'.olean')
            if not(os.stat(old).st_ino==os.stat(current).st_ino and os.stat(old).st_dev==os.stat(current).st_dev):need(sha(current)==record['object_sha256'],'Continuation original object differs')
            for ext in['stdout','stderr','time']:need(sha(directory/(name+'.'+ext))==record[ext+'_sha256'],'Continuation original log differs')
        added=[];logical_run=None
        for path in sorted(directory.glob('*.COMPILED.json')):
            name=path.name.removesuffix('.COMPILED.json');need(name in state['rows'],'Unknown continuation receipt')
            if name in base:continue
            record=load(path)
            if record.get('returncode')!=0:
                skipped.append(dict(continuation=str(directory),module=name,returncode=record.get('returncode'),reason='NO_SUCCESSFUL_RECEIPT_NOT_REUSED'));continue
            command=record['command'];need(len(command)==7 and command[2]=='-R','Invalid continuation compiler source command')
            here=Path(command[3]);need(here.is_absolute()and here.name=='sources','Invalid recorded continuation source root')
            here=here.parent
            if logical_run is None:logical_run=here
            need(here==logical_run,'Mixed logical continuation compiler runs')
            record=original.receipt(directory,here,state['rows'][name],c['compiler'],True)
            expected=['/usr/bin/time','-v','-o',str(here/(name+'.time')),'prlimit','--as='+str(plan['per_compiler_AS_bytes']),'--stack='+str(256*2**20),'--',*original.lean_command(c['compiler'],here,state['rows'][name])]
            need(record['resource_command']==expected,'Continuation actual compiler/resource command differs')
            if name in state['successful']:
                need(state['successful'][name]['object_sha256']==record['object_sha256'],'Conflicting continuation outputs');continue
            state['successful'][name]=record;origins[name]=directory;logical[name]=here;phases[name]='VALIDATED_CONTINUATION_'+str(index);added.append(name)
        need(added,'Continuation contributes no new validated successful modules')
        inherited.append(dict(path=str(directory),plan_sha256=sha(directory/'PLAN.json'),controller_sha256=V1_SHA,logical_run=str(logical_run),added_modules=added,
                              original_result_present=(directory/'RESULT.json').is_file(),old_outcome_unchanged=True))
    for name in state['successful']:
        need(all(dep.split('.')[0]in original.GENERIC or dep in state['successful']for dep in state['rows'][name]['imports']),'Nested prefix lacks a verified dependency '+name)
    state.update(origins=origins,logical_origins=logical,phases=phases,original_successful_count=len(base),continuation_successful_count=len(state['successful'])-len(base),continuation_plans=inherited,skipped_continuation_receipts=skipped)
    return state
