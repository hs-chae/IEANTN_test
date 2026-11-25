#!/usr/bin/env python3
"""Test study CLI/portability under normal/-O/-OO without rerunning heavy proofs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def publish(p,value):
    need(not p.exists(),'Fresh receipt required')
    fd,name=tempfile.mkstemp(prefix='.test-',dir=p.parent);q=Path(name)
    try:
        with os.fdopen(fd,'w') as f:
            json.dump(value,f,indent=2);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(q,p)
    finally:q.unlink()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--repository',type=Path,required=True)
    ap.add_argument('--context',type=Path,required=True)
    ap.add_argument('--run',type=Path,required=True)
    a=ap.parse_args();R=a.repository.resolve(strict=True);S=R/'Solutions/RH080Study.v1'
    need(not a.run.exists(),'Fresh test storage required');run=a.run.resolve();run.mkdir(parents=True)
    context=json.loads(a.context.read_text());inventory=json.loads((S/'REPRODUCTION_INPUTS.json').read_text())
    clone=run/'source-only/network';clone.mkdir(parents=True)
    for row in inventory['files']:
        source=R/row['path'];target=clone/row['path'];target.parent.mkdir(parents=True,exist_ok=True)
        need(sha(source)==row['sha256'],'Frozen package input changed')
        shutil.copyfile(source,target)
    shutil.copyfile(S/'REPRODUCTION_INPUTS.json',clone/'Solutions/RH080Study.v1/REPRODUCTION_INPUTS.json')
    need(not list(clone.rglob('*.olean')) and not list(clone.rglob('*.ilean')),'Application object in source-only extraction')
    controller=clone/'Solutions/RH080Study.v1/reproduce_study.py';controller_sha=sha(controller)
    packages=Path(context['generic_lean_path'].split(':')[0]).parents[4]
    need(packages.name=='packages','Generic package layout differs')
    rows=[];started=time.monotonic()
    def command(name,args,good,marker=None,target=None):
        completed=subprocess.run(list(map(str,args)),capture_output=True,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        out=run/(name+'.stdout');err=run/(name+'.stderr');out.write_bytes(completed.stdout);err.write_bytes(completed.stderr)
        need((completed.returncode==0)==good,'Wrong disposition: '+name)
        if marker:
            stream=completed.stdout if good else completed.stderr
            need(marker.encode() in stream,'Intended route/guard absent: '+name)
        if target is not None:
            need((target/'PREFLIGHT.json').exists()==good,'Wrong preflight receipt state: '+name)
            need(not (target/'RESULT.json').exists(),'Preflight/failed control published proof success')
        rows.append(dict(name=name,command=list(map(str,args)),returncode=completed.returncode,expected_success=good,
                         intended_guard=marker,stdout_sha256=sha(out),stderr_sha256=sha(err)))
    for label,flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
        prefix=[sys.executable]+flags
        command(label+'-help',prefix+[controller,'--help'],True,'--check-only')
        positive=run/(label+'-context-preflight')
        command(label+'-relocated-context',prefix+[controller,'--repository',clone,'--run',positive,'--context',a.context,'--check-only'],True,
                'PASS_STUDY_SOURCE_CONTEXT_AND_ACTUAL_CLI_PREFLIGHT_ONLY',positive)
        plan=json.loads((positive/'PLAN.json').read_text());need(plan['python_optimization']==len(flags)*(1 if label=='O' else 2),'Actual Python mode differs')
        generated=run/(label+'-generated-context')
        command(label+'-relocated-context-generation',prefix+[controller,'--repository',clone,'--run',generated,'--compiler',context['compiler'],
                '--packages',packages,'--check-only'],True,'PASS_STUDY_SOURCE_CONTEXT_AND_ACTUAL_CLI_PREFLIGHT_ONLY',generated)
        target=run/(label+'-both-context-routes')
        command(label+'-both-context-routes',prefix+[controller,'--repository',clone,'--run',target,'--context',a.context,
                '--compiler',context['compiler'],'--check-only'],False,'Use --context OR both --compiler and --packages',target)
        target=run/(label+'-partial-context')
        command(label+'-partial-context',prefix+[controller,'--repository',clone,'--run',target,'--compiler',context['compiler'],'--check-only'],False,
                'Both --compiler and --packages required',target)
        target=clone/('prohibited-run-'+label)
        command(label+'-run-inside-source',prefix+[controller,'--repository',clone,'--run',target,'--context',a.context,'--check-only'],False,
                'Run storage must be outside publishable repository',target)
        command(label+'-existing-run',prefix+[controller,'--repository',clone,'--run',positive,'--context',a.context,'--check-only'],False,
                'Fresh --run directory required')
        for name,patch,guard in [('wrong-compiler',lambda x:x.update(compiler_sha256='0'*64),'Pinned compiler bytes differ'),
              ('wrong-pins',lambda x:x['generic_dependencies'][0].update(revision='0'*40),'Generic dependency pins/order differ')]:
            bad=json.loads(a.context.read_text());patch(bad);badpath=run/(label+'-'+name+'.json');badpath.write_text(json.dumps(bad))
            target=run/(label+'-'+name)
            command(label+'-'+name,prefix+[controller,'--repository',clone,'--run',target,'--context',badpath,'--check-only'],False,guard,target)
        bad=run/(label+'-duplicate.json');bad.write_text('{"compiler":1,"compiler":2}')
        target=run/(label+'-duplicate-context')
        command(label+'-duplicate-context',prefix+[controller,'--repository',clone,'--run',target,'--context',bad,'--check-only'],False,
                'Duplicate JSON key',target)
        source=clone/'Solutions/RH080Study.v1/pv/dual_grid.c';original=source.read_bytes();source.write_bytes(original+b'\n// changed source\n')
        target=run/(label+'-changed-source')
        command(label+'-changed-source',prefix+[controller,'--repository',clone,'--run',target,'--context',a.context,'--check-only'],False,
                'Frozen reproduction source differs:',target)
        source.write_bytes(original)
        provider=clone/'Solutions/RH080Study.v1/functional/CompactDualStep.lean';saved=provider.read_bytes();provider.unlink()
        target=run/(label+'-missing-provider')
        command(label+'-missing-provider',prefix+[controller,'--repository',clone,'--run',target,'--context',a.context,'--check-only'],False,
                'Missing repository-contained application source:',target)
        provider.write_bytes(saved)
    need(sha(controller)==controller_sha,'Relocated controller changed')
    for row in inventory['files']:
        need(sha(clone/row['path'])==row['sha256'],'Source-only extraction not restored')
    receipt=dict(status='PASS_RELOCATED_SOURCE_ONLY_STUDY_CONTEXT_CLI_AND_GUARD_CONTROLS_ALL_PYTHON_MODES',rows=rows,
          source_only_repository=str(clone),source_files=len(inventory['files']),application_objects_present=False,
          wrapper_sha256=controller_sha,inventory_sha256=sha(S/'REPRODUCTION_INPUTS.json'),test_controller_sha256=sha(Path(__file__)),
          seconds=time.monotonic()-started,scope='Actual relocated preflight/context construction/child help/source closure/guard routes only; no heavy mathematical proof rerun is claimed.')
    publish(run/'RESULT.json',receipt);print(json.dumps(dict(status=receipt['status'],cases=len(rows))))


if __name__=='__main__':main()
