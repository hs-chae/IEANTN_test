# Copyright (c) 2026 IEANTN contributors. Apache-2.0.
"""Exercise the exact assigned packet/runtime and the existing native tool gate; no model inference."""
from pathlib import Path
import argparse
import base64
import asyncio
import hashlib
import importlib.util
import json
import os
import resource
import subprocess
import sys
import time
from types import SimpleNamespace

HERE = Path(__file__).resolve().parent
STUDY = HERE.parent
spec = importlib.util.spec_from_file_location('deep_native_controller_preflight', HERE / 'followup_native_controller.py')
controller = importlib.util.module_from_spec(spec)
spec.loader.exec_module(controller)
need = controller.require

PROBE = r'''
from pathlib import Path
import errno,json,os,socket,subprocess
checks={}
for path in FORBIDDEN_PATHS:
    try:
        with open(path,'rb')as f:f.read(1)
    except OSError as error:checks['denied:'+path]={'denied':True,'errno':error.errno}
    else:raise RuntimeError('forbidden parent/sibling/credential/shared-cache path readable')
packet_files=PACKET_FILES
if not packet_files:raise RuntimeError('empty packet')
first=packet_files[0]
if not Path('/task/'+first).is_file():raise RuntimeError('permitted packet cannot be read')
with open('/task/'+first,'rb')as f:packet_size=len(f.read())
try:
    with open('/task/'+first,'ab')as f:f.write(b'BAD')
except OSError as error:
    if error.errno not in (errno.EROFS,errno.EACCES):raise
else:raise RuntimeError('packet is writable')
checks['packet_readable_and_readonly']=True
Path('/work/allowed-write.txt').write_text('PRIVATE_WORKSPACE_OK\n')
Path('/tmp/allowed-private-temp.txt').write_text('PRIVATE_TEMP_OK\n')
checks['private_write_and_temp']=True
if os.environ.get('HOME')!='/home/worker':raise RuntimeError('HOME is not private worker path')
if Path('/home/worker/.codex/auth.json').exists():raise RuntimeError('credential mounted')
if Path('/home/worker/.cache').exists():raise RuntimeError('shared home cache mounted')
checks['private_home_and_no_auth_or_shared_cache']=True
os.symlink(FORBIDDEN_PATHS[0],'/work/forbidden-parent-symlink')
try:
    with open('/work/forbidden-parent-symlink','rb')as f:f.read(1)
except OSError:checks['symlink_parent_escape_denied']=True
else:raise RuntimeError('symlink reaches parent')
host=HOST_NAMESPACES
for name,namespace in host.items():
    if os.readlink('/proc/self/ns/'+name)==namespace:raise RuntimeError('namespace not distinct: '+name)
checks['distinct_user_mount_pid_net_namespaces']=True
if Path('/proc/'+str(HOST_PID)+'/cmdline').exists():raise RuntimeError('host controller visible in private proc')
checks['host_sibling_process_hidden']=True
status={line.split(':',1)[0]:line.split(':',1)[1].strip()for line in Path('/proc/self/status').read_text().splitlines()if ':'in line}
if int(status['CapEff'],16)!=0 or status.get('NoNewPrivs')!='1':raise RuntimeError('capability/no_new_privs boundary missing')
checks['zero_effective_capabilities_and_no_new_privs']=True
net=socket.socket();net.settimeout(.25)
try:
    error=net.connect_ex(('1.1.1.1',443))
    if error==0:raise RuntimeError('external HTTP/TLS port reachable')
    checks['external_TCP_denied']={'errno':error}
finally:net.close()
try:socket.getaddrinfo('example.com',443)
except socket.gaierror:checks['external_DNS_denied']=True
else:raise RuntimeError('external DNS resolver usable')
for row in MOUNTS:
    point=Path(row['target'])
    if not point.is_dir():raise RuntimeError('assigned mount absent')
    probe=point/'.study-preflight-write-denied'
    try:probe.write_text('BAD')
    except OSError as error:
        if error.errno not in (errno.EROFS,errno.EACCES):raise
    else:raise RuntimeError('assigned runtime mount writable')
checks['all_assigned_mounts_readonly']=True
Path('/work/probe.c').write_text('#include <stdio.h>\nint main(void){puts("GENERIC_C_OK");return 0;}\n')
c=subprocess.run(['/usr/bin/gcc','-O2','/work/probe.c','-o','/work/probe-c'],capture_output=True,text=True)
if c.returncode:raise RuntimeError('generic C compile failed:'+c.stderr)
c=subprocess.run(['/work/probe-c'],capture_output=True,text=True)
if c.returncode or c.stdout!='GENERIC_C_OK\n':raise RuntimeError('generic C execution failed')
checks['generic_C_compile_and_execute']=True
import mpmath,sympy
if mpmath.__version__!='1.3.0' or sympy.__version__!='1.12':raise RuntimeError('generic Python package version mismatch')
mpmath.mp.dps=60
if abs(mpmath.exp(mpmath.log(2))-2)>mpmath.mpf('1e-55'):raise RuntimeError('mpmath elementary capability failed')
x=sympy.Symbol('x')
if sympy.expand((x+1)**3)!=x**3+3*x**2+3*x+1:raise RuntimeError('sympy exact algebra capability failed')
checks['generic_mpmath_sympy']={'mpmath':mpmath.__version__,'sympy':sympy.__version__,'mpmath_dps':60,'symbolic_exact_identity':True}
if Path('/bin/lean').exists():
    Path('/work/objects').mkdir()
    Path('/work/Probe.lean').write_text('import Mathlib.Tactic.NormNum\nexample : (2 : Nat) + 2 = 4 := by norm_num\n')
    p=subprocess.run(['/bin/lean','-o','/work/objects/Probe.olean','/work/Probe.lean'],capture_output=True,text=True)
    if p.returncode:raise RuntimeError('generic Lean baseline compile failed:'+p.stdout+p.stderr)
    checks['generic_Lean_compile']=True
    imports=REQUIRED_IMPORTS
    if imports:
        Path('/work/NativeBaseline.lean').write_text(''.join('import '+name+'\n'for name in imports))
        p=subprocess.run(['/bin/lean','-o','/work/objects/NativeBaseline.olean','/work/NativeBaseline.lean'],capture_output=True,text=True)
        if p.returncode:raise RuntimeError('actual native baseline imports failed:'+p.stdout+p.stderr)
        checks['actual_native_import_compile']={'imports':imports,'exit_code':p.returncode}
    for name in FORBIDDEN_IMPORTS:
        Path('/work/Blocked.lean').write_text('import '+name+'\n')
        p=subprocess.run(['/bin/lean','/work/Blocked.lean'],capture_output=True,text=True)
        if p.returncode==0:raise RuntimeError('forbidden hidden import available: '+name)
        checks['forbidden_import:'+name]={'denied':True,'exit_code':p.returncode}
else:checks['generic_Lean_compile']='NOT_MOUNTED_PAPER_ONLY_RUNTIME'
# Reflection observes only the assigned runtime import graph; provenance/claim audit is a separate gate.
if Path('/work/objects/Blocked.olean').exists():raise RuntimeError('unexpected hidden output')
print(json.dumps({'status':'PASS_ACTUAL_OS_EXACT_RUNTIME_CANARIES','checks':checks,'packet_probe_bytes':packet_size}))
'''

async def prepare_os_spec(args, out, packet, runtime):
    dummy = SimpleNamespace(memory_gib=args.memory_gib, wall=args.wall, scratch_gib=args.scratch_gib,
                            cpus=args.cpus, model=args.model, out=str(out), output=10, operations=16, responses=16)
    controller.configure_runtime(runtime, dummy)
    adapter = controller.RuntimeExecutor(out / 'os-executor', packet, operation_limit=16)
    await adapter.start()
    data = controller.strict_json(adapter.spec_path)
    await adapter.close()
    rows = controller.strict_json(args.packet_manifest)['files']
    ordinary = [row['path'] for row in rows if 'sha256' in row]
    host_namespaces = {n: os.readlink('/proc/self/ns/' + n) for n in ['mnt', 'pid', 'net', 'user']}
    forbidden = [str(out / 'parent-only.txt'), str(out / 'sibling' / 'only-sibling.txt'),
                 str(STUDY.parent / 'memory' / 'feedback.md'), str(Path.home() / '.codex/auth.json'),
                 '/run/user/' + str(os.getuid()) + '/bus', '/tmp/ieantn-host-shared-cache-probe']
    program = PROBE.replace('FORBIDDEN_PATHS', repr(forbidden)).replace('HOST_NAMESPACES', repr(host_namespaces))
    program = program.replace('HOST_PID', str(os.getpid())).replace('PACKET_FILES', repr(ordinary))
    program = program.replace('MOUNTS', repr(runtime['mounts'])).replace('FORBIDDEN_IMPORTS', repr(runtime.get('forbidden_imports', ['HiddenStudyAnswer'])))
    program = program.replace('REQUIRED_IMPORTS', repr(runtime.get('required_imports', [])))
    data['command'] = ['/usr/bin/python3.10', '-I', '-B', '-c', program]
    data['cwd'] = '/work'
    target = out / 'OS_SPEC.json'
    target.write_text(json.dumps(data, indent=2) + '\n')
    return target, host_namespaces

def atomic_new(path, value):
    need(not path.exists(), 'fresh preflight receipt required')
    temporary = path.with_suffix(path.suffix + '.pending')
    with temporary.open('x') as handle:
        json.dump(value, handle, indent=2, allow_nan=False)
        handle.write('\n')
    os.link(temporary, path)
    temporary.unlink()

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--packet-manifest', type=Path, required=True)
    p.add_argument('--runtime', type=Path, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--model', default='gpt-6.2-sol')
    p.add_argument('--wall', type=int, default=150)
    p.add_argument('--memory-gib', type=int, default=32)
    p.add_argument('--scratch-gib', type=int, default=8)
    p.add_argument('--cpus', type=int, default=4)
    p.add_argument('--os-only', action='store_true')
    args = p.parse_args()
    args.packet_manifest = args.packet_manifest.resolve()
    args.runtime = args.runtime.resolve()
    args.out = args.out.resolve()
    need(args.out.is_relative_to(STUDY) and not args.out.exists(), 'fresh own-study preflight output required')
    need(1 <= args.memory_gib <= 300 and 1 <= args.scratch_gib <= 300 and 1 <= args.cpus <= 32,
         'bounded preflight resources required')
    packet, runtime = controller.validate_runtime(args.runtime, args.packet_manifest)
    args.out.mkdir(parents=True)
    (args.out / 'parent-only.txt').write_text('THIS_PARENT_FILE_MUST_BE_HIDDEN\n')
    (args.out / 'sibling').mkdir()
    (args.out / 'sibling/only-sibling.txt').write_text('THIS_SIBLING_FILE_MUST_BE_HIDDEN\n')
    started = time.monotonic()
    own_source_before = controller.file_sha(__file__)
    controller_source_before = controller.file_sha(HERE / 'followup_native_controller.py')
    target, host = asyncio.run(prepare_os_spec(args, args.out, packet, runtime))
    helper = controller.OLD / 'sources/ieantn-protected-workspace-20260925-NrAB5O/app/IEANTN/web/server/agent-sandbox.py'
    command = ['unshare', '--user', '--map-root-user', '--mount', '--propagation', 'private', '--',
               '/usr/bin/python3.10', '-I', '-B', str(helper), str(target)]
    def limits():
        resource.setrlimit(resource.RLIMIT_AS, (args.memory_gib * 1024 ** 3,) * 2)
        resource.setrlimit(resource.RLIMIT_CPU, (args.wall,) * 2)
        resource.setrlimit(resource.RLIMIT_FSIZE, (64 * 1024 ** 2,) * 2)
    proc = subprocess.run(command, text=True, capture_output=True, timeout=args.wall,
                          preexec_fn=limits)
    (args.out / 'os.stdout').write_text(proc.stdout)
    (args.out / 'os.stderr').write_text(proc.stderr)
    need(proc.returncode == 0, 'actual OS canary failed: ' + proc.stderr[-1500:])
    canary = json.loads(proc.stdout)
    need(canary.get('status') == 'PASS_ACTUAL_OS_EXACT_RUNTIME_CANARIES', 'OS canary status')
    native = None
    if not args.os_only:
        command2 = [sys.executable, '-I', '-B', str(HERE / 'followup_native_controller.py'), '--fixture',
            '--packet-manifest', str(args.packet_manifest), '--runtime', str(args.runtime),
            '--out', str(args.out / 'native-tool-fixture'), '--phase', 'LIVE_INFRA_PREFLIGHT',
            '--model', args.model, '--effort', 'high', '--initial-milestone', '1', '--increment', '1', '--memory-gib', str(args.memory_gib),
            '--scratch-gib', str(args.scratch_gib), '--cpus', str(args.cpus)]
        fixture = subprocess.run(command2, capture_output=True, text=True, timeout=args.wall + 30)
        (args.out / 'native-fixture.stdout').write_text(fixture.stdout)
        (args.out / 'native-fixture.stderr').write_text(fixture.stderr)
        need(fixture.returncode == 0, 'native no-auth tool fixture failed: ' + fixture.stderr[-1500:])
        native = controller.strict_json(args.out / 'native-tool-fixture/result.json')
        need(native.get('mode') == 'NOAUTH_FINAL_CONFIG_FIXTURE' and
             native.get('mechanical_submission_gate_passed') is True and
             native.get('artifact_export', {}).get('consistent') is True,
             'no-auth native fixture did not pass its exact tool/export gate')
        need(native.get('mcp_registry', {}).get('result', {}).get('data') == [], 'native MCP registry nonempty')
        need(native.get('fixture_requests_count', 0) > 0, 'fixture did not exercise model tool path')
        need(any(row.get('action')=='AUTOMATIC_PLANNING_EXTENSION_NO_TERMINATION_NO_INVALIDATION' for row in native.get('planning_milestones',[])), 'actual fixture did not cross and automatically extend its planning milestone')
        transport=controller.strict_json(args.out/'native-tool-fixture/executor/transport.json')
        chunks=[]
        for row in transport:
            message=row.get('message',{})
            if row.get('direction')=='from_executor' and message.get('method')=='process/output' and message.get('params',{}).get('stream')=='stdout':
                chunks.append(base64.b64decode(message['params']['chunk'],validate=True))
        limits=[]
        for line in b''.join(chunks).decode().splitlines():
            try:value=json.loads(line)
            except (ValueError,TypeError):continue
            if isinstance(value,dict) and 'CPU_limit' in value and 'FSIZE_limit' in value:limits.append(value)
        need(len(limits)==1 and limits[0]['CPU_limit']==[-1,-1] and limits[0]['FSIZE_limit'][0]>=24*1024**3, 'actual native tool worker shadow limit audit failed')
        native['actual_worker_resource_limits']=limits[0]

        need(native.get('fixture_reasoning_setting',{}).get('effort')=='high','fixture did not use fixed high reasoning setting')
        need(native.get('milestone_is_hard_cap') is False and native.get('operation_limit') is None and native.get('response_limit') is None and native.get('wall_admission_limit') is None, 'follow-up must not reinstate old admission caps')
        thread = native.get('thread_start', {}).get('result', {}).get('thread', {})
        need(thread.get('ephemeral') is True and thread.get('forkedFromId') is None and
             thread.get('parentThreadId') is None and thread.get('turns') == [],
             'native fixture inherited a parent or previous thread')
        need(native.get('thread_start', {}).get('result', {}).get('instructionSources') == [],
             'native fixture loaded external instruction sources')
        requests = controller.strict_json(args.out / 'native-tool-fixture/fixture_requests.json')
        denied = [item for request in requests for item in request.get('input', [])
                  if item.get('call_id') == 'fixture-denied' and item.get('type') in
                  {'function_call_output', 'custom_tool_call_output'}]
        need(denied and all('blocked by PreToolUse hook' in item.get('output', '') for item in denied),
             'actual advertised unapproved tool was not denied by the exact tool hook')
    need(controller.file_sha(__file__)==own_source_before and controller.file_sha(HERE / 'followup_native_controller.py')==controller_source_before,'preflight/controller source changed during execution')
    status = 'PASS_ACTUAL_OS_ONLY_NATIVE_TOOL_FIXTURE_NOT_RUN' if args.os_only else 'PASS_EXACT_PACKET_RUNTIME_ACTUAL_OS_AND_MODEL_TOOL_ISOLATION'
    receipt = {'status': status, 'arm': runtime['arm'], 'utc': time.time(),
        'packet_manifest_sha256': controller.file_sha(args.packet_manifest),
        'runtime_manifest_sha256': controller.file_sha(args.runtime),
        'controller_sha256': controller.file_sha(HERE / 'followup_native_controller.py'),
        'preflight_source_sha256': controller.file_sha(__file__), 'OS_canary': canary,
        'native_tool_fixture_result_sha256': controller.file_sha(args.out / 'native-tool-fixture/result.json') if native else None,
        'native_model_inference_calls': 0, 'paid_service_calls': 0,
        'actual_native_worker_resource_limits':native.get('actual_worker_resource_limits') if native else None,
        'actual_fixture_over_planning_milestone_valid':bool(native and any(row.get('action')=='AUTOMATIC_PLANNING_EXTENSION_NO_TERMINATION_NO_INVALIDATION' for row in native.get('planning_milestones',[]))),
        'actual_OS_elapsed_seconds': time.monotonic() - started, 'host_namespaces': host,
        'scope': 'Actual OS namespace + exact native tool/hook/empty-MCP fixture; source provenance and native closure audits remain separate prerequisites.'}
    atomic_new(args.out / 'RECEIPT.json', receipt)
    print(json.dumps({'status': status, 'arm': runtime['arm'], 'elapsed_seconds': receipt['actual_OS_elapsed_seconds'],
                      'native_model_inference_calls': 0}))

if __name__ == '__main__':
    main()
