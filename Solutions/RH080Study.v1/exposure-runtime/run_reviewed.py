#!/usr/bin/env python3
"""Clean-root transport for the unchanged reviewed fixture/research trial gate.

Defaults to metadata checking. Actual execution needs --execute-reviewed and the
original exact lock/protocol/mount/fixture/budget gates; this adapter does not
create research approval or relax any gate. No credentials are packaged.
"""
import argparse,hashlib,importlib.util,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
from strict_json import read


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(2**20),b''):h.update(b)
    return h.hexdigest()


def load(name,p):
    spec=importlib.util.spec_from_file_location(name,p);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--repository',type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument('--data-root',type=Path,required=True);ap.add_argument('--lock',type=Path,required=True)
    ap.add_argument('--fixture',action='store_true');ap.add_argument('--execute-reviewed',action='store_true')
    ap.add_argument('--python-packages-root',type=Path);ap.add_argument('--codex-client',type=Path);ap.add_argument('--codex-executor',type=Path)
    a=ap.parse_args();R=a.repository.resolve(strict=True);data=a.data_root.resolve(strict=True);lock=a.lock.resolve(strict=True)
    need(lock.is_relative_to(data) and not data.is_relative_to(R),'Explicit owned replay root/lock required')
    E=R/'Solutions/RH080Study.v1/exposure-runtime';pin=read(E/'ADAPTER_PIN.json')
    original=R/pin['adapter_path'];need(sha(original)==pin['adapter_sha256'],'Frozen trial gate differs')
    components=read(E/'SOURCE_COMPONENTS.json')
    for row in components['sources']:need(sha(R/row['path'])==row['sha256'],'Reviewed runtime source differs')
    gate=load('rh080_clean_root_unchanged_trial_gate',original);gate.DATA=data
    backend=E/'layout/ieantn-deep-tertiary-exposure-a-20261117/scripts/native_controller_v2.py';need(sha(backend)==pin['backend_sha256'],'Backend differs')
    gate.BACKEND=backend
    if a.execute_reviewed:
        need(all(x is not None for x in [a.python_packages_root,a.codex_client,a.codex_executor]),'Explicit Python/native-runtime roots required for execution')
        state=data/('binding-'+sha(lock)[:16]);need(not state.exists(),'Fresh binding execution required');state.mkdir()
        def bound_backend():
            core=load('rh080_clean_root_reviewed_native_backend',backend)
            generic=read(E/'layout/ieantn-deep-tertiary-exposure-a-20261117/evidence/runner_python_package_trees.json')
            python_target=state/'runtime-study/coordinator/runner-generic-python';python_target.mkdir(parents=True)
            for package in generic['packages']:
                source=(a.python_packages_root/package['name']).resolve(strict=True)
                need(core.tree_inventory(source)==package['files'],'Exact generic Python tree differs')
                target=python_target/package['name'];shutil.copytree(source,target)
                need(core.tree_inventory(target)==package['files'],'Generic Python copy differs')
            core.STUDY=state/'runtime-study'
            original_configure=core.configure_runtime
            def configure(runtime,args):
                original_configure(runtime,args)
                transport=sys.modules['existing_executor_adapter']
                expected=E/'layout/ieantn-exposure-maximal-20261109/sources/controller/continuation-20261108/research/existing_executor_adapter.py'
                need(Path(transport.__file__).resolve()==expected.resolve(),'Unexpected transport source')
                transport.NATIVE=a.codex_executor.resolve(strict=True)
                transport.HELPER=E/'layout/ieantn-exposure-maximal-20261109/sources/ieantn-protected-workspace-20260925-NrAB5O/app/IEANTN/web/server/agent-sandbox.py'
                if args.fixture:
                    profile=state/'NO_ACCOUNT_PROFILE';profile.mkdir();os.environ['CODEX_HOME']=str(profile)
                    for name in ['OPENAI_API_KEY','OPENAI_ADMIN_KEY','ANTHROPIC_API_KEY','OPENROUTER_API_KEY','AZURE_OPENAI_API_KEY']:os.environ.pop(name,None)
            core.configure_runtime=configure
            temporary=state/'controller-temporary';temporary.mkdir();tempfile.tempdir=str(temporary)
            client=a.codex_client.resolve(strict=True);executor=a.codex_executor.resolve(strict=True)
            binary=state/'controller-bin';binary.mkdir();(binary/'codex').symlink_to(client);os.environ['PATH']=str(binary)+':'+os.environ.get('PATH','')
            record=dict(status='EXPLICIT_REVIEWED_ROOT_BINDINGS_NOT_TRIAL_ACCEPTANCE',adapter_sha256=sha(Path(__file__)),lock_sha256=sha(lock),
                backend_sha256=sha(backend),original_trial_gate_sha256=sha(original),codex_client_sha256=sha(client),codex_executor_sha256=sha(executor),
                codex_client_version=subprocess.check_output([str(client),'--version'],text=True).strip(),fixture=a.fixture,
                original_checks_preserved=True,credentials_packaged=False)
            (state/'BINDINGS.json').write_text(json.dumps(record,indent=2)+'\n')
            return core
        gate.import_backend=bound_backend
    sys.argv=[str(original),'--lock',str(lock)]+(['--fixture']if a.fixture else [])+([]if a.execute_reviewed else ['--check-only'])
    gate.main()
    if a.execute_reviewed and a.fixture:
        acceptor_path=R/pin['fixture_acceptor_path']
        need(sha(acceptor_path)==pin['fixture_acceptor_sha256'],'Frozen actual fixture acceptor differs')
        acceptor=load('rh080_clean_root_actual_fixture_acceptor',acceptor_path)
        accepted=acceptor.accept_fixture(lock.parent,lock)
        print(json.dumps(dict(status='PASS_REVIEWED_CLEAN_ROOT_NOAUTH_EXECUTION_AND_ORIGINAL_FIXTURE_ACCEPTOR',
                              preflight=str(accepted),sha256=sha(accepted),external_model_inference_calls=0)))


if __name__=='__main__':main()
