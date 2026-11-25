#!/usr/bin/env python3
"""Fresh-root NOAUTH fixture over the unchanged reviewed assigned executor.

Never launches research inference. Reuses the frozen protocol and exact assigned
content manifests, accepts explicit new source bindings, and routes the native
client exclusively through the reviewed local fake provider. Original drivers,
locks, outcomes and source pins are never edited.
"""
import argparse
import ast
import asyncio
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
from types import SimpleNamespace


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):
    need(p.is_file() and not p.is_symlink(),'Regular file required: '+str(p))
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(2**20),b''):h.update(b)
    return h.hexdigest()


def read(p):
    def pairs(items):
        x={}
        for k,v in items:
            need(k not in x,'Duplicate JSON key');x[k]=v
        return x
    return json.loads(p.read_bytes(),object_pairs_hook=pairs,
                      parse_constant=lambda x:(_ for _ in ()).throw(ValueError(x)))


def publish(p,value):
    need(not os.path.lexists(p),'Fresh receipt required')
    fd,name=tempfile.mkstemp(prefix='.fixture-',dir=p.parent);q=Path(name)
    try:
        with os.fdopen(fd,'w') as f:json.dump(value,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(q,p)
    finally:q.unlink()


def file_pin(p):return dict(path=str(p.resolve()),sha256=sha(p))


def import_file(name,p):
    spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--repository',type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--reference-lock',type=Path,required=True)
    ap.add_argument('--mount-map',type=Path)
    ap.add_argument('--python-packages-root',type=Path,required=True)
    ap.add_argument('--codex-client',type=Path,required=True)
    ap.add_argument('--codex-executor',type=Path,required=True)
    ap.add_argument('--prepare-only',action='store_true')
    ap.add_argument('--proof-mode',choices=['V0','V1'])
    a=ap.parse_args();R=a.repository.resolve(strict=True);E=R/'Solutions/RH080Study.v1/exposure-runtime'
    need(not a.root.exists(),'Fresh root required');root=a.root.resolve();need(not root.is_relative_to(R),'Runtime root must be outside publishable source');root.mkdir(parents=True)
    started=time.monotonic();controller_sha=sha(Path(__file__));(root/'launch_fixture.executed.py').write_bytes(Path(__file__).read_bytes())
    source_pins=read(E/'SOURCE_COMPONENTS.json')
    for row in source_pins['sources']:need(sha(R/row['path'])==row['sha256'],'Reviewed source component differs')
    reference=read(a.reference_lock)
    need(reference['schema']=='RH080_TRIAL_LOCK_V1' and reference['fixture'] is True and reference['reviewed_by']=='/root','Reviewed frozen fixture reference required')
    protocol_path=Path(reference['protocol']['path']);need(sha(protocol_path)==reference['protocol']['sha256'],'Frozen protocol differs')
    protocol=read(protocol_path);budget=protocol['budgets']
    need((budget['cpus'],budget['memory_gib'],budget['scratch_gib'])==(4,64,12),'Original matched trial budget differs')
    reference_runtime_path=Path(reference['runtime']['path']);need(sha(reference_runtime_path)==reference['runtime']['sha256'],'Original assigned runtime differs')
    runtime=read(reference_runtime_path);need(runtime['external_network'] is False and runtime['host_tools'] is False,'Assigned isolation scope differs')
    mapping=read(a.mount_map) if a.mount_map else {}
    need(set(mapping)<=set(row['target'] for row in runtime['mounts']),'Unknown replacement mount target')
    adapter_pin=read(E/'ADAPTER_PIN.json');original=R/adapter_pin['adapter_path'];need(sha(original)==adapter_pin['adapter_sha256'],'Original trial gate changed')
    acceptor_path=R/adapter_pin['fixture_acceptor_path']
    need(sha(acceptor_path)==adapter_pin['fixture_acceptor_sha256'],'Original fixture acceptor changed')
    acceptor=import_file('rh080_unchanged_actual_fixture_acceptor',acceptor_path)
    gate=import_file('rh080_original_fixture_metadata_gate',original);gate.DATA=root
    trees=root/'trees';trees.mkdir();bindings=[]
    for index,row in enumerate(runtime['mounts']):
        manifest_path=Path(row['manifest']['path']);need(sha(manifest_path)==row['manifest']['sha256'],'Assigned tree manifest changed')
        expected=read(manifest_path);source=Path(mapping.get(row['target'],row['source'])).resolve(strict=True)
        # Independently hash every actual replacement tree using the unchanged
        # assigned-runtime gate. Only the root path changes; content must match.
        rebound=dict(expected,root=str(source));target=trees/(str(index).zfill(2)+'.json');target.write_text(json.dumps(rebound,indent=2)+'\n')
        gate.check_tree(source,file_pin(target))
        row['source']=str(source);row['manifest']=file_pin(target)
        bindings.append(dict(target=row['target'],source=str(source),manifest_sha256=sha(target),content_manifest_sha256=sha(manifest_path)))
    runtime_path=root/'runtime.json';runtime_path.write_text(json.dumps(runtime,indent=2)+'\n')
    # Only a neutral controller fixture prompt is introduced, never model research.
    packet=root/'packet';packet.mkdir();task=packet/'TASK.md';task.write_text('NEUTRAL CLEAN-ROOT REPRODUCTION FIXTURE. No mathematical research or real model inference. Verify only the assigned offline runtime.\n')
    packet_manifest=root/'packet.json';packet_manifest.write_text(json.dumps(dict(root=str(packet),files={'TASK.md':sha(task)}),indent=2)+'\n')
    protocol_copy=root/'PROTOCOL.json';shutil.copyfile(protocol_path,protocol_copy)
    lock=dict(schema='RH080_TRIAL_LOCK_V1',reviewed_by='/root',fixture=True,
          condition=reference['condition'],task=reference['task'],replicate=reference['replicate'],
          protocol=file_pin(protocol_copy),runtime=file_pin(runtime_path),packet_manifest=file_pin(packet_manifest),out=str(root/'fixture'),
          review_basis='Parent root explicitly authorized an additive clean-root NOAUTH fixture with frozen source/protocol/budgets and no research inference; original results remain unchanged.')
    lock_path=root/'FIXTURE_LOCK.json';lock_path.write_text(json.dumps(lock,indent=2)+'\n')
    prior_argv=sys.argv;sys.argv=[str(original),'--lock',str(lock_path),'--fixture','--check-only']
    try:gate.main()
    finally:sys.argv=prior_argv
    # Recreate the two exact generic Python source trees in own runtime storage.
    backend_rel='layout/ieantn-deep-tertiary-exposure-a-20261117/scripts/native_controller_v2.py'
    backend=E/backend_rel;core=import_file('rh080_reviewed_clean_root_backend',backend)
    generic=read(E/'layout/ieantn-deep-tertiary-exposure-a-20261117/evidence/runner_python_package_trees.json')
    runtime_study=root/'runtime-study';python_target=runtime_study/'coordinator/runner-generic-python';python_target.mkdir(parents=True)
    for package in generic['packages']:
        name=package['name'];source=(a.python_packages_root/name).resolve(strict=True)
        need(core.tree_inventory(source)==package['files'],'Pinned generic Python source tree differs: '+name)
        target=python_target/name;shutil.copytree(source,target)
        need(core.tree_inventory(target)==package['files'],'Copied generic Python source tree differs: '+name)
    core.STUDY=runtime_study
    codex_client=a.codex_client.resolve(strict=True);codex_executor=a.codex_executor.resolve(strict=True)
    need(codex_client.is_file() and codex_executor.is_file(),'Native Codex client/executor missing')
    client_version=subprocess.check_output([str(codex_client),'--version'],text=True).strip()
    executor_version=subprocess.check_output([str(codex_executor),'--version'],text=True).strip()
    arguments=SimpleNamespace(out=root/'fixture',packet=packet,model=protocol['model']['alias'],effort=protocol['model']['reasoning_effort'],
        fixture=True,wall=budget['active_wall_seconds'],output=budget['output_token_admission'],operations=budget['executor_operations'],
        responses=budget['max_responses'],memory_gib=budget['memory_gib'],scratch_gib=budget['scratch_gib'],cpus=budget['cpus'],
        per_response_max_output_tokens=None,phase='RH080_ADDITIVE_CLEAN_ROOT_NOAUTH_FIXTURE',fixture_hook_fault=False,
        fixture_artifact_name='canary.txt',fixture_boundary_steps=3,fixture_draft_at=1,fixture_budget_prefix=False,
        paired_task_seed=reference['replicate'],compiler=False,python_only=False,environment='',python_optimization=sys.flags.optimize)
    core.configure_runtime(runtime,arguments)
    proof_source_hash=None
    if a.proof_mode is not None:
        need(any(row['target']=='/source_pv' for row in runtime['mounts']),'Actual proof-support mount missing')
        proof_source=E/'proof_fixture.py';proof_source_hash=sha(proof_source)
        proof_provider=import_file('rh080_noauth_actual_proof_import_fixture',proof_source)
        core.Fixture=proof_provider.handler(core.Fixture,a.proof_mode)
    transport=sys.modules['existing_executor_adapter'];expected_transport=E/'layout/ieantn-exposure-maximal-20261109/sources/controller/continuation-20261108/research/existing_executor_adapter.py'
    need(Path(transport.__file__).resolve()==expected_transport.resolve(),'Unexpected executor transport import')
    transport.NATIVE=codex_executor
    transport.HELPER=E/'layout/ieantn-exposure-maximal-20261109/sources/ieantn-protected-workspace-20260925-NrAB5O/app/IEANTN/web/server/agent-sandbox.py'
    core.make_prompt=lambda directory:(directory/'TASK.md').read_text()
    temporary=root/'controller-temporary';temporary.mkdir();tempfile.tempdir=str(temporary)
    client_bin=root/'controller-bin';client_bin.mkdir();(client_bin/'codex').symlink_to(codex_client)
    os.environ['PATH']=str(client_bin)+':'+os.environ.get('PATH','')
    empty_profile=root/'NO_ACCOUNT_PROFILE';empty_profile.mkdir();os.environ['CODEX_HOME']=str(empty_profile)
    # Do not inspect credential values; remove credential environment variables
    # from this NOAUTH controller process before invoking the fake provider.
    for name in ['OPENAI_API_KEY','OPENAI_ADMIN_KEY','ANTHROPIC_API_KEY','OPENROUTER_API_KEY','AZURE_OPENAI_API_KEY']:
        os.environ.pop(name,None)
    plan=dict(status='PREPARED_EXACT_ASSIGNED_RUNTIME_NOAUTH_FIXTURE_NOT_ACCEPTANCE',controller_sha256=controller_sha,
       source_manifest_sha256=sha(E/'SOURCE_COMPONENTS.json'),original_adapter_sha256=sha(original),backend_sha256=sha(backend),
       fixture_acceptor_sha256=sha(acceptor_path),
       reference_lock_sha256=sha(a.reference_lock),fixture_lock_sha256=sha(lock_path),runtime_sha256=sha(runtime_path),bindings=bindings,
       codex_client_sha256=sha(codex_client),codex_client_version=client_version,codex_executor_sha256=sha(codex_executor),codex_executor_version=executor_version,
       model_provider='Reviewed local fake provider, requires_openai_auth=false; no real research inference',
       proof_mode=a.proof_mode,proof_fixture_source_sha256=proof_source_hash,
       budgets=budget,credentials_read=False,old_sources_or_locks_modified=False,
       boundary='Fresh owned controller/packet/manifest/Python roots; assigned content roots supplied explicitly and byte-checked against frozen manifests, not claimed fetched anew from public URLs.')
    publish(root/'PLAN.json',plan)
    if a.prepare_only:
        print(json.dumps(dict(status=plan['status'],fixture_lock_sha256=sha(lock_path))));return
    try:
        asyncio.run(core.main(arguments))
        actual=read(root/'fixture/result.json')
        need(actual.get('mode')=='NOAUTH_FINAL_CONFIG_FIXTURE','Expected actual local-provider fixture result')
        # Reuse the actual frozen acceptor, including the exported artifact,
        # runtime probe, absent auth/canary/host paths and distinct namespaces.
        # No invented generic "fixture passed" flag is accepted.
        preflight_path=acceptor.accept_fixture(root,lock_path)
        accepted=read(preflight_path)
        need(accepted['status']=='PASS_EXACT_RH080_ASSIGNED_RUNTIME_AND_NATIVE_ISOLATION' and
             accepted['external_model_inference_calls']==0,'Actual fixture acceptance absent')
        if a.proof_mode is not None:
            proof_result=read(root/'fixture/submission/PROOF_IMPORTS.json')
            need(proof_result['mode']==a.proof_mode and
                 proof_result['status']=='PASS_ACTUAL_ASSIGNED_PROOF_IMPORT_MANIPULATION',
                 'Actual assigned D/C Lean proof imports failed; preserve exported diagnostic')
    except BaseException as error:
        publish(root/'FAILED.json',dict(status='ACTUAL_CLEAN_ROOT_NOAUTH_FIXTURE_FAILED',exception_type=type(error).__name__,message=str(error),
              seconds=time.monotonic()-started,plan_sha256=sha(root/'PLAN.json'),no_real_model_inference_requested=True))
        raise
    need(sha(Path(__file__))==controller_sha,'Fixture launcher changed during run')
    publish(root/'RESULT.json',dict(status='PASS_ACTUAL_CLEAN_ROOT_NOAUTH_ASSIGNED_NAMESPACE_FIXTURE',seconds=time.monotonic()-started,
          plan_sha256=sha(root/'PLAN.json'),actual_fixture_result_sha256=sha(root/'fixture/result.json'),fixture_lock_sha256=sha(lock_path),
          actual_preflight_sha256=sha(root/'PREFLIGHT.json'),
          no_real_model_inference_requested=True,credentials_read=False,original_outcomes_unchanged=True,
          scope='Actual neutral noauth fixture using exact assigned content and source runtime. Not a new research trial or a public-corpus download reconstruction.'))
    print(json.dumps(dict(status='PASS_ACTUAL_CLEAN_ROOT_NOAUTH_ASSIGNED_NAMESPACE_FIXTURE')))


if __name__=='__main__':main()
