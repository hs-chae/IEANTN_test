#!/usr/bin/env python3
"""Verify exact N24 regeneration bytes and actual producer/resource association.

This accepts deterministic data/source identity only, never a mathematical
proof, a source-first PV result, or final W4 consumer completion.
"""
from __future__ import annotations
import argparse,os,sys,time
from pathlib import Path
from bootstrap_context import PROJECT,REPOSITORY,atomic,need,read_json,sha
EXPECTED_SHA='e940c2081dab88fc308197080f5033c1f3a55ece638616e712b9367aebf67631'
IGNORED_PLAN_FIELDS={'producer_seconds','source_input'}

def events(row):
    text=row.get('memory.events');need(type(text)is str,'Completed owned memory events required')
    pairs=[line.split()for line in text.splitlines()]
    need(all(len(p)==2 for p in pairs),'Malformed owned memory events')
    result={key:int(value)for key,value in pairs}
    need(len(result)==len(pairs)and all(v>=0 for v in result.values()),'Duplicate/negative memory event counter')
    return result

def module_imports(path):
    result=[]
    with path.open()as stream:
        for line in stream:
            if line.startswith('import '):result += line[7:].split('--',1)[0].split()
            elif line.strip()and not line.startswith(('/-','--')):break
    return result

def verify(a):
    start=time.monotonic();validator_sha=sha(Path(__file__))
    expected=a.expected.resolve(strict=True);new=a.new.resolve(strict=True)
    need(sha(expected)==EXPECTED_SHA,'Frozen exact N24 expected inventory changed')
    fixed=read_json(expected)
    need(fixed['counts']==dict(sources=1033,generated_modules=1020,csv=937),'Fixed expected N24 populations differ')
    command=read_json(a.command_plan);supervisor=read_json(a.supervisor)
    need(supervisor['status']=='COMPLETE_CHILD_NOT_MATHEMATICAL_ACCEPTANCE'
        and type(supervisor.get('returncode'))is int and supervisor['returncode']==0
        and supervisor['failure']is None,'Actual producer did not complete under owned supervisor')
    need(supervisor['command_file_sha256']==sha(a.command_plan)
        and supervisor['command']==command['command'],'Actual supervised command association changed')
    producer=PROJECT/'dual/produce_fft_dag_certificate.py';supervisor_source=PROJECT/'pv/supervise_resource_run.py'
    pins={r['path']:r['sha256']for r in command['source_pins']}
    need(len(pins)==len(command['source_pins']),'Duplicate actual execution source pin')
    need(pins.get(str(producer))==fixed['producer_sha256']==sha(producer),'Actual fixed producer identity differs')
    need(pins.get(str(supervisor_source))==supervisor['supervisor_sha256']==sha(supervisor_source),'Owned supervisor source identity differs')
    for path,digest in pins.items():need(sha(Path(path))==digest,'Executed source pin changed')
    argv=command['command'];need(type(argv)is list and len(argv)==10,'Exact fixed regeneration argument vector required')
    need(argv[1:]==[str(producer),'--stages','24','--out',str(new),'--chunk-log','13','--pairs-per-module','524288'],
        'Producer source/parameters/output arguments differ')
    for suffix,key in [('stdout','stdout_sha256'),('stderr','stderr_sha256')]:
        need(sha(a.supervisor.with_suffix('.'+suffix))==supervisor[key],'Actual captured producer log changed')
    before,final=supervisor['before'],supervisor['final']
    need(before['path']==final['path']and type(a.unit)is str and a.unit.endswith('.service')and before['path'].endswith('/'+a.unit),
        'Expected actual owned regeneration service differs')
    for row in [before,final]:need(row.get('memory.max')==str(300*2**30)and row.get('memory.swap.max')=='0','Independent physical300GiB/noSwap contract differs')
    first,last=events(before),events(final);need(first.keys()==last.keys(),'Owned memory counter population changed')
    delta={k:last[k]-first[k]for k in first};need(all(v>=0 for v in delta.values())and delta.get('oom')==delta.get('oom_kill')==0,'Actual owned OOM counter delta differs')
    admission=supervisor['admission'];need(admission['available_RAM_bytes']>=2**40
        and admission['free_disk_bytes']>=2**40 and admission['owned_scratch_bytes']<270*2**30,
        'Actual independent RAM/disk/scratch admission differs')
    plan_path=new/'PLAN.json';initial_plan_sha=sha(plan_path);proposal=read_json(plan_path)
    keys=['stages','n','chunk','pairs_per_module','namespace','final_module','input_sha256',
          'producer_sha256','norm_numerator','total_abs','quad']
    for key in keys:need(type(proposal[key])is type(fixed[key])and proposal[key]==fixed[key],'Exact N24 parameter differs: '+key)
    need(proposal['modules']==fixed['generated_modules']and proposal['payloads']==fixed['payloads'],
        'Exact generated source/data inventories differ')
    source=REPOSITORY/fixed['source_input'];need(Path(proposal['source_input']).resolve()==source.resolve()
        and sha(source)==fixed['input_sha256'],'Actual fixed input bytes/path differ')
    original=a.original.resolve(strict=True)if a.original else None
    original_plan=None
    if original:
        need(original!=new and not new.is_relative_to(original)and not original.is_relative_to(new),'Original and new outputs must be disjoint')
        original_plan=read_json(original/'PLAN.json')
        need(sha(original/'PLAN.json')==fixed['candidate_plan_sha256'],'Frozen original candidate PLAN changed')
        need({k:v for k,v in proposal.items()if k not in IGNORED_PLAN_FIELDS}==
             {k:v for k,v in original_plan.items()if k not in IGNORED_PLAN_FIELDS},'Original/new exact PLAN identity differs')
    rows=fixed['generated_modules']+fixed['payloads'];names=[r['file']for r in rows]
    need(len(names)==len(set(names))==1957 and all(Path(n).name==n for n in names),'Exact flat generated file universe differs')
    need({p.name for p in new.iterdir()}==set(names)|{'PLAN.json'},'Unexpected or missing newly generated file')
    results=[]
    for i,row in enumerate(rows):
        p=new/row['file'];need(p.is_file()and not p.is_symlink()and p.stat().st_size==row['bytes'],'New generated file kind/size differs: '+row['file'])
        actual=sha(p);need(actual==row['sha256'],'New generated bytes differ: '+row['file'])
        original_sha=None
        if original:
            old=original/row['file'];need(old.is_file()and not old.is_symlink()and old.stat().st_size==row['bytes'],'Original candidate file kind/size differs')
            original_sha=sha(old);need(original_sha==actual,'Original/new generated bytes differ: '+row['file'])
        if p.suffix=='.lean':need(module_imports(p)==row['imports'],'Generated imports differ: '+row['file'])
        results.append(dict(file=row['file'],bytes=row['bytes'],expected_sha256=row['sha256'],new_sha256=actual,original_sha256=original_sha))
        if(i+1)%256==0:print('checked',i+1,'/1957 exact generated files',flush=True)
    need(sha(plan_path)==initial_plan_sha and sha(Path(__file__))==validator_sha and sha(producer)==fixed['producer_sha256']and sha(expected)==EXPECTED_SHA,'Producer/inventory changed during verification')
    if original:need(sha(original/'PLAN.json')==fixed['candidate_plan_sha256'],'Original PLAN changed during verification')
    samples=supervisor.get('samples',[])
    observed=[int(row['cgroup']['memory.current'])for row in samples if'cgroup'in row and'memory.current'in row['cgroup']]
    allocated=sum(p.stat().st_blocks*512 for p in new.iterdir())
    return dict(status='PASS_EXACT_N24_DETERMINISTIC_REGENERATION_BYTES_NOT_PROOF_NOT_PV',
        validator_sha256=validator_sha,expected_inventory_sha256=EXPECTED_SHA,
        new_output=str(new),new_plan_sha256=sha(plan_path),original_candidate=str(original)if original else None,
        original_plan_sha256=sha(original/'PLAN.json')if original else None,
        compared_to_original_candidate=original is not None,parameters={k:proposal[k]for k in keys},
        original_new_PLAN_ignored_fields=sorted(IGNORED_PLAN_FIELDS),fixed_input=dict(path=fixed['source_input'],sha256=sha(source)),
        command_file_sha256=sha(a.command_plan),supervisor_receipt_sha256=sha(a.supervisor),
        actual_command=argv,producer_python_binary_sha256=sha(Path(argv[0]).resolve()),
        producer_source_sha256=sha(producer),owned_resource_source_sha256=sha(supervisor_source),
        generated_Lean_files=1020,generated_CSV_files=937,verified_files=results,
        total_generated_bytes=sum(r['bytes']for r in rows),new_output_allocated_bytes=allocated,
        producer_seconds=proposal['producer_seconds'],supervisor_seconds=supervisor['seconds'],
        verification_seconds=time.monotonic()-start,actual_owned_memory_events_delta=delta,
        largest_sampled_cgroup_memory_current_bytes=max(observed)if observed else None,
        sampled_memory_is_not_exact_peak=True,physical_cgroup_limit_bytes=300*2**30,
        mathematical_proof=False,source_first_PV=False,production_N24_proof_acceptance=False,
        cleanup_performed=False,verifier_python=sys.version)

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['new','expected','supervisor','command-plan','output']:ap.add_argument('--'+name,required=True,type=Path)
    ap.add_argument('--original',type=Path);ap.add_argument('--unit',required=True);a=ap.parse_args()
    need(not os.path.lexists(a.output),'Fresh byte-verification receipt required')
    result=verify(a);atomic(a.output,result)
    print('PASS exact1957 generated files; deterministic identity only, no proof/PV/cleanup')
if __name__=='__main__':main()
