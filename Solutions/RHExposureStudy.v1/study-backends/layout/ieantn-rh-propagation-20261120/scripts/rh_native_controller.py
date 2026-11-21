#!/usr/bin/env python3
"""New two-arm RH protocol over the unchanged, pinned isolated native controller.

This module contains no mathematical discovery results. The native model is never
called by --check or --fixture. Source access is a per-arm trusted host broker;
the model tool gate and namespace executor remain the previously pinned code.
"""
from pathlib import Path
import argparse
import asyncio
import hashlib
import importlib.util
import json
import os
import re
import signal
import sys
import tempfile
import time

STUDY=Path(__file__).resolve().parents[1]
WORKSPACE=STUDY.parent
DATA=Path('/data/ivy-rh-propagation-20261120')
ORIGINAL=WORKSPACE/'ieantn-d01-d02-repair-rerun-20261118/scripts/followup_native_controller.py'
ORIGINAL_SHA='98295216807d7a0c53f9ef439158820b52b45615de12c6426f43ace6a02a4fc3'

def need(value,message):
    if not value:raise ValueError(message)

def sha(path):
    h=hashlib.sha256()
    with Path(path).open('rb')as f:
        for b in iter(lambda:f.read(1024**2),b''):h.update(b)
    return h.hexdigest()

def strict_loads(raw):
    def pairs(items):
        d={}
        for k,v in items:
            need(k not in d,'duplicate JSON key');d[k]=v
        return d
    return json.loads(raw,object_pairs_hook=pairs,parse_constant=lambda x:(_ for _ in()).throw(ValueError('nonfinite JSON')))

def read(path):return strict_loads(Path(path).read_bytes())

def pin(row):
    need(isinstance(row,dict)and isinstance(row.get('path'),str),'file pin required')
    p=Path(row['path'])
    need(p.is_absolute()and p.is_file()and not p.is_symlink(),'absolute regular pinned file required')
    need(sha(p)==row.get('sha256'),'file pin differs: '+str(p))
    return p

need(sha(ORIGINAL)==ORIGINAL_SHA,'unchanged followup source pin differs')
spec=importlib.util.spec_from_file_location('rh_pinned_followup',ORIGINAL)
followup=importlib.util.module_from_spec(spec);spec.loader.exec_module(followup)

def tree_inventory(root):
    root=Path(root)
    need(root.is_absolute()and root.resolve()==root and root.is_dir(),'canonical tree root required')
    rows=[]
    for parent,dirs,files in os.walk(root,followlinks=False):
        for name in sorted(dirs+files):
            p=Path(parent)/name;rel=p.relative_to(root).as_posix()
            if p.is_symlink():
                need(p.resolve().is_relative_to(root),'exposed symlink leaves allowed tree: '+str(p))
                rows.append({'path':rel,'symlink':os.readlink(p)})
            elif p.is_file():rows.append({'path':rel,'bytes':p.stat().st_size,'sha256':sha(p)})
            else:need(p.is_dir(),'nonregular exposure entry')
    return sorted(rows,key=lambda row:row['path'])

def check_tree(manifest_path,expected=None):
    manifest=read(manifest_path)
    need(isinstance(manifest,dict)and isinstance(manifest.get('files'),list),'tree manifest required')
    root=Path(manifest['root'])
    if expected is not None:need(root==Path(expected),'manifest root mismatch')
    need(manifest['files']==tree_inventory(root),'actual exposed tree differs: '+str(root))
    return root

def validate_runtime(runtime_path,packet_manifest_path):
    packet=check_tree(packet_manifest_path)
    runtime=read(runtime_path)
    need(runtime.get('schema')=='RH_PROPAGATION_RUNTIME_V1','new RH runtime schema required')
    need(runtime.get('arm')in {'NL_RH','IEANTN_RH'},'exactly the NL_RH and IEANTN_RH arms')
    need(runtime.get('external_network')is False and runtime.get('host_tools')is False,'worker raw network/host tools must be disabled')
    seen=set();generic=False;source_mounts=[]
    for row in runtime['mounts']:
        target=row['target']
        need(isinstance(target,str)and target.startswith('/')and os.path.normpath(target)==target,'canonical mount target required')
        allowed=target=='/opt/lean'or target.startswith('/generic/')or target=='/corpus/literature'or target=='/ieantn'or target=='/application-cache'
        need(allowed,'mount outside RH roots')
        need(target not in seen and not any(target.startswith(x+'/')or x.startswith(target+'/')for x in seen),'duplicate/overlapping mount target')
        seen.add(target)
        if runtime['arm']=='NL_RH':need(target not in {'/ieantn','/application-cache'}and row.get('role')not in {'native','application'},'NL project exposure forbidden')
        check_tree(pin(row['manifest']),row['source'])
        if target.startswith('/generic/'):generic=True
        if target=='/corpus/literature':source_mounts.append(row)
    need('/opt/lean'in seen and generic,'both arms require common Lean and generic dependencies')
    need(len(source_mounts)==1,'one private appendable literature mount required')
    if runtime['arm']=='IEANTN_RH':need('/ieantn'in seen,'full arm requires complete pinned IEANTN package')
    paths=runtime.get('lean_path',[])
    need(isinstance(paths,list)and len(paths)==len(set(paths))and paths,'nonempty unique Lean path list')
    for p in paths:need(isinstance(p,str)and os.path.normpath(p)==p and any(p==x or p.startswith(x+'/')for x in seen),'Lean path outside allowed mounted roots')
    return packet,runtime

def make_prompt(packet):
    return (packet/'TASK.md').read_text()+'''\n\nYour initial packet is read-only at /task; /task/RUNTIME_PATHS.json lists your other allowed mounts. Your own work persists under /work throughout this research stage. Both arms have the same generic mathematical tools. Raw Internet/browser/connectors are blocked; broad new literature remains available through your independent source-request service. Use /task/request_source.py to record bibliographic search or canonical primary-source fetch requests in /work/submission/SOURCE_REQUESTS.json. The service also accepts legacy flat source_requests.jsonl records with id, kind (search or fetch), and query or url. The trusted host service admits original papers and genuine supplements, and places response bytes and exact provenance under /corpus/literature. Read responses there; requests/results are not broadcast to another arm. You may introduce new legitimate mathematical source predicates. Do not infer that an unfulfilled request is a negative mathematical result. Save reproducible drafts and a source record early. Technical snapshots every60s are passive and do not stop your research. The first comparison is prospectively scheduled by your packet; continue meaningful routes beyond familiar imported consequences. Final readiness is not proof acceptance. Save regular flat submission files, STAGE_STATUS.json and LOCK.json containing their exact SHA256 hashes. Do not include LOCK.json in its own files list. Record four family keys PNT,Intervals,Weighted,Ramanujan and distinguish completed, partial, failed, and not established work.\n'''

def continuation_message(args,status):
    return ('Continue your own permitted mathematical research. Check your independent /corpus/literature responses and use /task/request_source.py to preserve source requests in SOURCE_REQUESTS.json. Pursue multiple substantive routes, exact full-domain arguments and downstream consumers; record failures and remaining assumptions. No other-arm result or mathematical evaluation is supplied. Planning milestones extend automatically. Mechanical submission status: '+json.dumps(status,sort_keys=True))

async def stage_ready(adapter,args):
    try:
        raw=await adapter.read_export('/work/submission/LOCK.json');lock=strict_loads(raw)
        need(isinstance(lock,dict)and isinstance(lock.get('files'),list),'LOCK files missing')
        names=set()
        for row in lock['files']:
            need(isinstance(row,dict),'LOCK row must be object')
            name=row.get('path');need(isinstance(name,str)and re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_.-]{0,127}',name)and name not in names and name!='LOCK.json','flat unique artifact required')
            names.add(name)
            meta=(await adapter.export_metadata(name)).get('result',{})
            need(meta.get('isFile')and not meta.get('isSymlink'),'regular source artifact required')
            body=await adapter.read_export('/work/submission/'+name)
            need(hashlib.sha256(body).hexdigest()==row.get('sha256'),'submission artifact hash differs')
        need('STAGE_STATUS.json'in names,'STAGE_STATUS.json must be locked')
        state=strict_loads(await adapter.read_export('/work/submission/STAGE_STATUS.json'))
        need(state.get('ready_for_review')is True,'worker research remains incomplete')
        families=state.get('families',{})
        need(set(families)==set(args.target_families),'all four common families must be assessed')
        allowed={'supported','incomplete','no_additional_improvement','false_with_counterexample','unassessed','supported_at_stated_trust_tier'}
        need(all(isinstance(v,dict)and v.get('status')in allowed for v in families.values()),'explicit family states required')
        need(state.get('serious_attempts_documented')is True,'multiple substantive routes and failures must be recorded')
        elapsed=time.monotonic()-adapter.budget_started
        need(elapsed>=args.minimum_research_seconds,'prospective first comparison time not reached')
        need(await adapter.read_export('/work/submission/LOCK.json')==raw,'LOCK changed during readback')
        return {'ready':True,'status':state,'lock_sha256':hashlib.sha256(raw).hexdigest(),'files':len(names),'mathematical_validity':'UNASSESSED_REQUIRES_SOURCE_AND_PROOF_REVIEW'}
    except Exception as e:return {'ready':False,'mechanical_or_worker_readiness_reason':str(e),'no_mathematical_judgment':True}

def configure_runtime(runtime,args):
    followup.configure_runtime(runtime,args)
    followup.core.BASE='You are an independent mathematical research worker in a controlled RH experiment. Follow only the assigned clean mission and allowed input packet. Retain RH visibly as a hypothesis.'
    followup.core.DEVELOPER='Use only your assigned OS-isolated executor, source packet and independent literature-request channel. You may derive mathematics, write Lean/programs, compute and request any legitimate relevant original paper or genuine supplement. Do not access other arms, prior sessions, evaluator files, host tools, browser, connectors, raw network or external message channels. No private reasoning transcripts. Publish mathematical statements, derivations, sources, real code/evidence, failed attempts and limitations. Source-first PV requires correspondence from actual program source through formal execution semantics to its mathematical consumer; label native-assisted or certificate checking separately. Keep all four target families represented. Save reproducible work under /work/submission. Planning milestones extend automatically; technical snapshots preserve ongoing state and only final submission freezes it.'
    followup.make_prompt=make_prompt;followup.continuation_message=continuation_message;followup.stage_ready=stage_ready

def validate_lock(args,runtime):
    if args.fixture:return
    need(args.lock is not None,'reviewed RH execution lock required')
    lock=read(args.lock)
    need(lock.get('schema')=='RH_PROPAGATION_EXECUTION_LOCK_V1'and lock.get('status')=='ROOT_APPROVED_RH_STAGE'and lock.get('reviewed_by')=='/root','reviewed RH lock required')
    need(lock.get('arm')==runtime['arm']and lock.get('run_id')==args.out.name,'arm/run identity mismatch')
    need(lock.get('model')==args.model and lock.get('effort')==args.effort,'model/reasoning differs')
    for key,path in [('packet_manifest',args.packet_manifest),('runtime_manifest',args.runtime),('controller_source',Path(__file__).resolve())]:need(pin(lock[key]).resolve()==path.resolve(),'lock pin path differs:'+key)
    protocol=read(pin(lock['protocol']))
    need(protocol.get('schema')=='RH_NL_IEANTN_PROTOCOL_V1','new RH protocol required')
    need(protocol.get('arms')==['NL_RH','IEANTN_RH']and protocol.get('targets')==args.target_families,'common arms/targets differ')
    need(protocol.get('model')==args.model and protocol.get('effort')==args.effort,'model/reasoning differs from protocol')
    resources={'memory_gib':args.memory_gib,'scratch_gib':args.scratch_gib,'cpus':args.cpus}
    need(all(protocol.get('resource_policy',{}).get(k)==v for k,v in resources.items()),'resources differ from common protocol')
    checkpoints=protocol.get('checkpoints',{})
    need(checkpoints.get('initial_minimum_research_opportunity_seconds')==args.minimum_research_seconds and checkpoints.get('generated_token_planning_milestone')==args.output and checkpoints.get('increment')==args.increment,'comparison/planning policy differs from protocol')
    need(checkpoints.get('technical_passive_seconds')==60 and checkpoints.get('token_or_operation_milestone_is_hard_cap')is False,'snapshot/planning policy differs')
    preflight=read(pin(lock['preflight']))
    need(preflight.get('status')=='PASS_EXACT_RH_PACKET_RUNTIME_OS_AND_NATIVE_TOOL_ISOLATION','exact new RH preflight required')
    need(preflight.get('controller_sha256')==sha(__file__)and preflight.get('packet_manifest_sha256')==sha(args.packet_manifest)and preflight.get('runtime_manifest_sha256')==sha(args.runtime),'preflight belongs to other bytes')
    need(lock.get('minimum_research_seconds')==args.minimum_research_seconds,'first comparison policy differs')
    need(lock.get('resources')==resources,'resource allocation differs')

def cli():
    p=argparse.ArgumentParser(description=__doc__,allow_abbrev=False)
    p.add_argument('--packet-manifest',type=Path,required=True);p.add_argument('--runtime',type=Path,required=True);p.add_argument('--out',type=Path,required=True);p.add_argument('--lock',type=Path)
    p.add_argument('--fixture',action='store_true');p.add_argument('--check',action='store_true')
    p.add_argument('--model',default='gpt-6.2-sol');p.add_argument('--effort',choices=['low','medium','high','xhigh'],default='high')
    p.add_argument('--initial-milestone',dest='output',type=int,default=250000);p.add_argument('--increment',type=int,default=250000)
    p.add_argument('--memory-gib',type=int,default=96);p.add_argument('--scratch-gib',type=int,default=64);p.add_argument('--cpus',type=int,default=8)
    p.add_argument('--minimum-research-seconds',type=int,default=3600);p.add_argument('--phase',default='RH_INDEPENDENT_RESEARCH')
    args=p.parse_args()
    for key in ('packet_manifest','runtime','out'):setattr(args,key,getattr(args,key).resolve())
    need(not args.out.exists()and (args.out.is_relative_to(STUDY)or args.out.is_relative_to(DATA)),'fresh owned output required')
    need(args.output>0 and args.increment>0 and 1<=args.memory_gib<=300 and 1<=args.scratch_gib<=300 and 1<=args.cpus<=32 and args.minimum_research_seconds>=0,'resource/planning parameters invalid')
    packet,runtime=validate_runtime(args.runtime,args.packet_manifest);args.packet=str(packet)
    args.target_families=['PNT','Intervals','Weighted','Ramanujan']
    validate_lock(args,runtime)
    if args.check:
        print(json.dumps({'status':'PASS_RH_METADATA_ONLY','model_calls':0,'runtime_arm':runtime['arm'],'controller_sha256':sha(__file__)}));return
    args.wall=86400;args.operations=None;args.responses=None
    args.fixture_hook_fault=False;args.fixture_artifact_name='canary.txt';args.fixture_boundary_steps=3;args.fixture_draft_at=1;args.fixture_budget_prefix=False
    args.per_response_max_output_tokens=None;args.paired_task_seed=0;args.compiler=False;args.python_only=False;args.environment='';args.python_optimization=sys.flags.optimize
    temp=DATA/'controller-private';temp.mkdir(parents=True,exist_ok=True);tempfile.tempdir=str(temp)
    configure_runtime(runtime,args)
    signal.signal(signal.SIGTERM,followup.signal_stop);signal.signal(signal.SIGINT,followup.signal_stop)
    if not args.fixture:followup.core.check_scope({'memory_gib':args.memory_gib,'cpus':args.cpus})
    asyncio.run(followup.main(args))
    result=read(args.out/'result.json')
    need(result.get('mechanical_submission_gate_passed')is True,'native stage failed its mechanical gate; see preserved result.json')

if __name__=='__main__':cli()
