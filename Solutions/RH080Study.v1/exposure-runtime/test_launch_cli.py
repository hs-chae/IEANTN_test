#!/usr/bin/env python3
"""Actual all-mode portable reference/metadata/prepare-only CLI guards.

No namespace worker or model is launched by these controls. The separate sealed
NOAUTH fixture receipts establish actual namespace/proof-import execution.
"""
import argparse,hashlib,json,os,subprocess,sys,tempfile
from pathlib import Path


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['repository','run','toolchain','packages','generic-source-root','corpus','representation','support','python-packages-root','codex-client','codex-executor']:
        ap.add_argument('--'+name,type=Path,required=True)
    a=ap.parse_args();R=a.repository.resolve(strict=True);E=R/'Solutions/RH080Study.v1/exposure-runtime'
    need(not a.run.exists(),'Fresh control output required');a.run.mkdir(parents=True);run=a.run.resolve();rows=[]
    def execute(name,command,good,marker):
        x=subprocess.run(list(map(str,command)),capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        (run/(name+'.stdout')).write_bytes(x.stdout);(run/(name+'.stderr')).write_bytes(x.stderr)
        need((x.returncode==0)==good,'Wrong control disposition '+name)
        need(marker.encode() in (x.stdout if good else x.stderr),'Intended actual route/guard absent '+name)
        rows.append(dict(name=name,command=list(map(str,command)),returncode=x.returncode,expected_success=good,intended_guard=marker,
                         stdout_sha256=sha(run/(name+'.stdout')),stderr_sha256=sha(run/(name+'.stderr'))))
    common=['--repository',R,'--template','followup-V0','--toolchain',a.toolchain,'--packages',a.packages,
            '--generic-source-root',a.generic_source_root,'--corpus',a.corpus,'--representation',a.representation,'--support',a.support]
    for label,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
        prefix=[sys.executable]+flags
        for filename in ['prepare_reference.py','launch_fixture.py','run_reviewed.py']:
            execute(label+'-help-'+filename,prefix+[E/filename,'--help'],True,'--root' if filename!='run_reviewed.py' else '--data-root')
        reference=run/(label+'-reference')
        execute(label+'-public-reference',prefix+[E/'prepare_reference.py']+common+['--root',reference],True,'PREPARED_PUBLIC_TEMPLATE_REFERENCE_NOT_EXECUTION_ACCEPTANCE')
        lock=reference/'REFERENCE_FIXTURE_LOCK.json'
        execute(label+'-actual-metadata',prefix+[E/'run_reviewed.py','--repository',R,'--data-root',reference,'--lock',lock,'--fixture'],True,
                'EXACT_LOCK_PACKET_RUNTIME_METADATA_CHECKED_NO_INFERENCE')
        prepared=run/(label+'-prepared-only')
        launch=prefix+[E/'launch_fixture.py','--repository',R,'--root',prepared,'--reference-lock',lock,
            '--python-packages-root',a.python_packages_root,'--codex-client',a.codex_client,'--codex-executor',a.codex_executor,'--prepare-only']
        execute(label+'-full-source-prepare-only',launch,True,'PREPARED_EXACT_ASSIGNED_RUNTIME_NOAUTH_FIXTURE_NOT_ACCEPTANCE')
        need((prepared/'PLAN.json').is_file() and not (prepared/'RESULT.json').exists() and not (prepared/'fixture').exists(),'Preparation overstated execution')
        execute(label+'-stale-root',launch,False,'Fresh root required')
        wrongmap=run/(label+'-wrongmap.json');wrongmap.write_text(json.dumps({'/unexpected':str(a.corpus)}))
        changed=list(launch);changed[changed.index('--root')+1]=run/(label+'-bad-target')
        execute(label+'-unexpected-mount-target',changed+['--mount-map',wrongmap],False,'Unknown replacement mount target')
        execute(label+'-lock-outside-root',prefix+[E/'run_reviewed.py','--repository',R,'--data-root',prepared,'--lock',lock,'--fixture'],False,
                'Explicit owned replay root/lock required')
    receipt=dict(status='PASS_27_ACTUAL_PORTABLE_NATIVE_REPLAY_CLI_ROUTES_ALL_PYTHON_MODES_NO_WORKERS',rows=rows,
                 controller_sha256=sha(Path(__file__)),model_calls=0,namespace_workers_started=0,
                 scope='All-mode public template construction, exact full-tree metadata/prepare route, real child CLIs and intended rejection guards; actual namespace execution has separate independently accepted receipts.')
    need(len(rows)==27,'Control population changed')
    fd,name=tempfile.mkstemp(prefix='.receipt-',dir=run);p=Path(name)
    try:
        with os.fdopen(fd,'w') as f:json.dump(receipt,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(p,run/'RESULT.json')
    finally:p.unlink()
    print(json.dumps(dict(status=receipt['status'],cases=len(rows))))


if __name__=='__main__':main()
