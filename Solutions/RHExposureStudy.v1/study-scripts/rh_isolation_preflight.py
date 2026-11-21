#!/usr/bin/env python3
"""New RH exact-packet/runtime OS and native-tool canaries; no inference."""
from pathlib import Path
import argparse
import asyncio
import base64
import datetime
import hashlib
import importlib.util
import json
import os
import resource
import subprocess
import sys
from types import SimpleNamespace

HERE=Path(__file__).resolve().parent
def module(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
controller=module('rh_exact_controller',HERE/'rh_native_controller.py')
old=module('rh_old_os_probe',controller.WORKSPACE/'ieantn-d01-d02-repair-rerun-20261118/scripts/followup_isolation_preflight.py')
need=controller.need

async def prepare(args,packet,runtime):
    dummy=SimpleNamespace(memory_gib=args.memory_gib,wall=args.wall,scratch_gib=args.scratch_gib,cpus=args.cpus,model=args.model,out=str(args.out),output=1,operations=None,responses=None)
    controller.configure_runtime(runtime,dummy)
    adapter=controller.followup.RuntimeExecutor(args.out/'os-executor',packet,operation_limit=None)
    await adapter.start();data=controller.read(adapter.spec_path);await adapter.close()
    packet_rows=controller.read(args.packet_manifest)['files'];files=[r['path']for r in packet_rows if 'sha256'in r]
    namespaces={n:os.readlink('/proc/self/ns/'+n)for n in ('user','mnt','pid','net')}
    forbidden=[str(args.out/'parent-only.txt'),str(args.out/'sibling/only-sibling.txt'),str(controller.WORKSPACE/'memory/feedback.md'),str(Path.home()/'.codex/auth.json'),'/run/user/'+str(os.getuid())+'/bus','/tmp/ieantn-host-shared-cache-probe']+runtime.get('forbidden_paths',[])
    program=old.PROBE.replace('FORBIDDEN_PATHS',repr(forbidden)).replace('HOST_NAMESPACES',repr(namespaces)).replace('HOST_PID',str(os.getpid())).replace('PACKET_FILES',repr(files)).replace('MOUNTS',repr(runtime['mounts'])).replace('FORBIDDEN_IMPORTS',repr(runtime.get('forbidden_imports',['HiddenStudyAnswer']))).replace('REQUIRED_IMPORTS',repr(runtime.get('required_imports',[])))
    program=program.replace('/bin/lean','/opt/lean/bin/lean')
    program="from pathlib import Path\nif not Path('/opt/lean/bin/lean').is_file():raise RuntimeError('required generic Lean compiler absent')\n"+program
    data.update(command=['/usr/bin/python3.10','-I','-B','-c',program],cwd='/work')
    specpath=args.out/'OS_SPEC.json';specpath.write_text(json.dumps(data,indent=2)+'\n')
    return specpath

def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument('--packet-manifest',type=Path,required=True);p.add_argument('--runtime',type=Path,required=True);p.add_argument('--out',type=Path,required=True)
    p.add_argument('--model',default='gpt-6.2-sol');p.add_argument('--effort',default='high');p.add_argument('--wall',type=int,default=600)
    p.add_argument('--memory-gib',type=int,default=96);p.add_argument('--scratch-gib',type=int,default=64);p.add_argument('--cpus',type=int,default=8)
    args=p.parse_args()
    for k in ('packet_manifest','runtime','out'):setattr(args,k,getattr(args,k).resolve())
    need(not args.out.exists()and(args.out.is_relative_to(controller.STUDY)or args.out.is_relative_to(controller.DATA)),'fresh owned preflight required')
    need(1<=args.memory_gib<=300 and 1<=args.scratch_gib<=300 and 1<=args.cpus<=32 and 10<=args.wall<=1800,'preflight resource bounds')
    packet,runtime=controller.validate_runtime(args.runtime,args.packet_manifest)
    args.out.mkdir(parents=True);(args.out/'parent-only.txt').write_text('HIDDEN_PARENT\n');(args.out/'sibling').mkdir();(args.out/'sibling/only-sibling.txt').write_text('HIDDEN_SIBLING\n')
    pins={str(p):controller.sha(p)for p in (Path(__file__),HERE/'rh_native_controller.py',controller.ORIGINAL,controller.WORKSPACE/'ieantn-d01-d02-repair-rerun-20261118/scripts/followup_isolation_preflight.py')}
    specpath=asyncio.run(prepare(args,packet,runtime))
    helper=controller.followup.OLD/'sources/ieantn-protected-workspace-20260925-NrAB5O/app/IEANTN/web/server/agent-sandbox.py'
    command=['unshare','--user','--map-root-user','--mount','--propagation','private','--','/usr/bin/python3.10','-I','-B',str(helper),str(specpath)]
    def limits():
        resource.setrlimit(resource.RLIMIT_AS,(args.memory_gib*1024**3,)*2)
        resource.setrlimit(resource.RLIMIT_CPU,(args.wall,)*2)
        resource.setrlimit(resource.RLIMIT_FSIZE,(64*1024**2,)*2)
    proc=subprocess.run(command,input=b'',capture_output=True,timeout=args.wall,preexec_fn=limits,close_fds=True)
    (args.out/'os.stdout').write_bytes(proc.stdout);(args.out/'os.stderr').write_bytes(proc.stderr)
    need(proc.returncode==0,'OS runtime canary failed; preserved os.stderr')
    osresult=controller.strict_loads(proc.stdout);need(osresult.get('status')=='PASS_ACTUAL_OS_EXACT_RUNTIME_CANARIES','OS status differs')
    mode_checks=[]
    rejected_runtime=args.out/'NEGATIVE_NETWORK_RUNTIME.json'
    rejected=dict(runtime);rejected['external_network']=True
    rejected_runtime.write_text(json.dumps(rejected,indent=2)+'\n')
    for optimize in ([],['-O'],['-OO']):
        call=[sys.executable,'-I','-B']+optimize+[str(HERE/'rh_native_controller.py'),'--fixture','--check','--packet-manifest',str(args.packet_manifest),'--runtime',str(args.runtime),'--out',str(args.out/('unused-check-'+str(len(mode_checks))))]
        check=subprocess.run(call,capture_output=True,timeout=args.wall)
        need(check.returncode==0,'optimized metadata CLI failed')
        negative=call.copy();negative[negative.index('--runtime')+1]=str(rejected_runtime)
        rejected_call=subprocess.run(negative,capture_output=True,timeout=args.wall)
        need(rejected_call.returncode!=0 and b'worker raw network/host tools must be disabled'in rejected_call.stderr,'optimized CLI accepted raw network or failed for wrong reason')
        mode_checks.append({'optimization':optimize,'status':controller.strict_loads(check.stdout),'forbidden_network_rejected':True})
    fixture_path=args.out/'native-tool-fixture'
    call=[sys.executable,'-I','-B',str(HERE/'rh_native_controller.py'),'--fixture','--packet-manifest',str(args.packet_manifest),'--runtime',str(args.runtime),'--out',str(fixture_path),'--model',args.model,'--effort',args.effort,'--initial-milestone','1','--increment','1','--memory-gib',str(args.memory_gib),'--scratch-gib',str(args.scratch_gib),'--cpus',str(args.cpus)]
    fixture=subprocess.run(call,capture_output=True,timeout=args.wall+90)
    (args.out/'native.stdout').write_bytes(fixture.stdout);(args.out/'native.stderr').write_bytes(fixture.stderr)
    need(fixture.returncode==0,'native no-auth fixture failed; preserved native.stderr/result.json')
    native=controller.read(fixture_path/'result.json')
    need(native.get('mode')=='NOAUTH_FINAL_CONFIG_FIXTURE'and native.get('mechanical_submission_gate_passed')is True and native.get('artifact_export',{}).get('consistent')is True,'native tool/export gate failed')
    need(native.get('mcp_registry',{}).get('result',{}).get('data')==[],'connector registry nonempty')
    thread=native.get('thread_start',{}).get('result',{}).get('thread',{})
    need(thread.get('ephemeral')is True and thread.get('forkedFromId')is None and thread.get('parentThreadId')is None and thread.get('turns')==[],'fresh thread isolation failed')
    need(native.get('thread_start',{}).get('result',{}).get('instructionSources')==[],'external instructions loaded')
    requests=controller.read(fixture_path/'fixture_requests.json')
    denied=[item for request in requests for item in request.get('input',[])if item.get('call_id')=='fixture-denied'and item.get('type')in {'function_call_output','custom_tool_call_output'}]
    need(denied and all('blocked by PreToolUse hook'in item.get('output','')for item in denied),'actual unapproved tool was not denied')
    need(native.get('fixture_reasoning_setting',{}).get('effort')==args.effort,'reasoning fixture differs')
    need(native.get('milestone_is_hard_cap')is False and native.get('operation_limit')is None and native.get('response_limit')is None and native.get('wall_admission_limit')is None,'shadow planning hard cap')
    need(all(controller.sha(p)==v for p,v in pins.items()),'controller/preflight source changed')
    result={'schema':'RH_PROPAGATION_PREFLIGHT_V1','status':'PASS_EXACT_RH_PACKET_RUNTIME_OS_AND_NATIVE_TOOL_ISOLATION','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'model_calls':0,'fixture_remote_inference':False,'arm':runtime['arm'],'controller_sha256':controller.sha(HERE/'rh_native_controller.py'),'packet_manifest_sha256':controller.sha(args.packet_manifest),'runtime_manifest_sha256':controller.sha(args.runtime),'preflight_source_sha256':controller.sha(__file__),'source_pins':pins,'os_canary':osresult,'optimization_cli_checks':mode_checks,'native_fixture_result_sha256':controller.sha(fixture_path/'result.json'),'native_thread_id':thread.get('id'),'native_fixture_requests':len(requests),'source_service_status':'NOT_TESTED_HERE_REQUIRES_SEPARATE_LIVE_BROKER_CANARY'}
    target=args.out/'PREFLIGHT.json';temp=args.out/'PREFLIGHT.pending';temp.write_text(json.dumps(result,indent=2)+'\n');os.link(temp,target);temp.unlink()
    print(json.dumps({'status':result['status'],'receipt':str(target),'model_calls':0}))

if __name__=='__main__':main()
