#!/usr/bin/env python3
"""Actual source/readback CLI controls in Python normal, -O and -OO.

Does not rerun the accepted 96 GiB kernel computation three times. It checks the
actual cold producer readback, preflight route, physical C-to-AST frontend route,
and rejection guards in every Python optimization mode. All fixture mutations
are confined to the fresh experiment-owned directory created by this script.
"""
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


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def atomic(p, value):
    need(not p.exists(), 'Fresh acceptance output required')
    fd, name = tempfile.mkstemp(prefix='.cli-', dir=p.parent)
    q = Path(name)
    try:
        with os.fdopen(fd, 'w') as f:
            json.dump(value, f, indent=2); f.write('\n'); f.flush(); os.fsync(f.fileno())
        os.link(q, p)
    finally:
        q.unlink()


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--repository', required=True, type=Path)
    ap.add_argument('--context', required=True, type=Path)
    ap.add_argument('--accepted-run', required=True, type=Path)
    ap.add_argument('--run', required=True, type=Path)
    a = ap.parse_args()
    repository = a.repository.resolve(strict=True)
    accepted = a.accepted_run.resolve(strict=True)
    need(not a.run.exists(), 'Fresh owned control directory required')
    run = a.run.resolve(); run.mkdir(parents=True)
    base = repository/'Solutions/RH080Study.v1/pv'
    scripts = {name: sha(base/name) for name in ['verify_joint.py','reproduce_joint.py','parse_source.py','reproduce_canonical.py']}
    controller_sha = sha(Path(__file__))
    rows = []
    started = time.monotonic()
    def execute(name, command, good, marker=None, output=None):
        completed = subprocess.run(command, capture_output=True)
        (run/(name+'.stdout')).write_bytes(completed.stdout)
        (run/(name+'.stderr')).write_bytes(completed.stderr)
        need((completed.returncode == 0) == good, 'Wrong CLI disposition: '+name)
        if marker:
            stream = completed.stdout if good else completed.stderr
            need(marker.encode() in stream, 'Intended guard did not fire: '+name)
        if output is not None:
            need(output.exists() == good, 'Wrong atomic acceptance state: '+name)
        rows.append(dict(name=name, command=command, returncode=completed.returncode,
                         stdout_sha256=sha(run/(name+'.stdout')),
                         stderr_sha256=sha(run/(name+'.stderr')), expected_success=good,
                         intended_guard=marker))
    # Rebase a private, complete copy so the verifier's absolute association
    # checks remain active. Never mutate the accepted producer bank.
    fixture = run/'fixture'; shutil.copytree(accepted, fixture)
    result = json.loads((fixture/'RESULT.json').read_text())
    plan = json.loads((fixture/'PLAN.json').read_text())
    def rebase(value):
        if isinstance(value, str):
            return value.replace(str(accepted), str(fixture))
        if isinstance(value, list):
            return [rebase(v) for v in value]
        if isinstance(value, dict):
            return {k:rebase(v) for k,v in value.items()}
        return value
    result, plan = rebase(result), rebase(plan)
    (fixture/'PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
    result['PLAN_sha256'] = sha(fixture/'PLAN.json')
    (fixture/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n')
    original_result = (fixture/'RESULT.json').read_bytes()
    for label, flags in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
        prefix = [sys.executable]+flags
        output = run/(label+'-positive.json')
        execute(label+'-actual-readback',prefix+[str(base/'verify_joint.py'),'--run',str(accepted),'--output',str(output)],True,
                'PASS_COMPLETE_JOINT_SOURCE_OBJECT_VALUE_AXIOM_AND_NATIVE_OUTPUT_READBACK', output)
        execute(label+'-preflight',prefix+[str(base/'reproduce_joint.py'),'--repository',str(repository),'--context',str(a.context),'--check-only'],True,
                'PASS_SOURCE_AND_GENERIC_PREFLIGHT_ONLY')
        execute(label+'-canonical-preflight',prefix+[str(base/'reproduce_canonical.py'),'--repository',str(repository),'--context',str(a.context),
                '--accepted-run',str(accepted),'--check-only'],True,'PASS_CANONICAL_APPEND_PREFLIGHT_ONLY')
        frontend = run/('frontend-'+label); frontend.mkdir(); (frontend/'lean').mkdir()
        for name in ['parse_source.py','dual_grid.c']:
            shutil.copyfile(base/name, frontend/name)
        execute(label+'-physical-source-frontend',prefix+[str(frontend/'parse_source.py')],True)
        for name in ['DualAST.lean','DualSource.lean']:
            need((frontend/'lean'/name).read_bytes() == (base/'lean'/name).read_bytes(), 'Actual frontend bytes differ: '+label)
        # Verify the private fixture before using it for negative controls.
        fixture_output=run/(label+'-fixture-positive.json')
        execute(label+'-rebased-fixture',prefix+[str(base/'verify_joint.py'),'--run',str(fixture),'--output',str(fixture_output)],True,None,fixture_output)
        mutations = [
            ('incomplete-status',lambda x:x.update(status='FAILED'), 'Incomplete actual producer status'),
            ('non-pv-boundary',lambda x:x.update(source_first_PV=False), 'Wrong source-first/application reuse boundary'),
            ('omitted-module',lambda x:x.update(modules=44), 'Wrong selected source population'),
            ('duplicate-build',lambda x:x['builds'].append(x['builds'][0]), 'Duplicate/incomplete module identities'),
            ('failed-compiler',lambda x:x['builds'][0].update(returncode=1), 'Failed compiler in accepted build'),
            ('changed-object-hash',lambda x:x['builds'][0].update(object_sha256='0'*64), 'Accepted object changed'),
            ('wrong-output-hash',lambda x:x.update(stdout_sha256='0'*64), 'Actual C stdout differs from proved bytes'),
            ('wrong-cap',lambda x:x['builds'][0].update(AS_cap_bytes=4*2**30), 'Actual compiler resource cap differs')]
        for name, mutate, guard in mutations:
            changed=json.loads(original_result); mutate(changed)
            (fixture/'RESULT.json').write_text(json.dumps(changed)+'\n')
            target=run/(label+'-'+name+'.json')
            execute(label+'-'+name,prefix+[str(base/'verify_joint.py'),'--run',str(fixture),'--output',str(target)],False,guard,target)
        for name, bad, guard in [('duplicate-json',b'{"status":"x","status":"y"}', 'Duplicate JSON key'),
                                 ('nonfinite-json',b'{"status":NaN}', 'NaN')]:
            (fixture/'RESULT.json').write_bytes(bad)
            target=run/(label+'-'+name+'.json')
            execute(label+'-'+name,prefix+[str(base/'verify_joint.py'),'--run',str(fixture),'--output',str(target)],False,guard,target)
        (fixture/'RESULT.json').write_bytes(original_result)
        # An import inventory altered consistently with its plan hash must still
        # be rejected against the actual imported source, rather than count only.
        old_plan=(fixture/'PLAN.json').read_bytes()
        changed_plan=json.loads(old_plan); changed_plan['modules'][-1]['imports']=[]
        (fixture/'PLAN.json').write_text(json.dumps(changed_plan)+'\n')
        changed_result=json.loads(original_result); changed_result['PLAN_sha256']=sha(fixture/'PLAN.json')
        (fixture/'RESULT.json').write_text(json.dumps(changed_result)+'\n')
        target=run/(label+'-false-import-inventory.json')
        execute(label+'-false-import-inventory',prefix+[str(base/'verify_joint.py'),'--run',str(fixture),'--output',str(target)],False,
                'Recorded imports differ from source',target)
        (fixture/'PLAN.json').write_bytes(old_plan); (fixture/'RESULT.json').write_bytes(original_result)
        # Atomic freshness prevents overwriting an already published receipt.
        execute(label+'-existing-receipt',prefix+[str(base/'verify_joint.py'),'--run',str(accepted),'--output',str(output)],False,
                'Fresh acceptance output required')
    need(all(sha(base/name)==value for name,value in scripts.items()),'Tested CLI changed during controls')
    need(sha(Path(__file__))==controller_sha,'CLI test controller changed during controls')
    receipt=dict(status='PASS_ACTUAL_SOURCE_PREFLIGHT_READBACK_AND_REJECTION_ROUTES_ALL_PYTHON_MODES',
                 rows=rows, source_first_cold_run=str(accepted), cold_result_sha256=sha(accepted/'RESULT.json'),
                 script_sha256=scripts, controller_sha256=controller_sha,
                 python_version=sys.version, seconds=time.monotonic()-started,
                 fixture_cleanup='Complete regenerable private fixture; safe to remove after retained receipts are checked.',
                 scope='Fresh source-only Lean proof executed once; every Python child CLI and actual physical-source regeneration checked under normal/-O/-OO. No numerical advantage attributed to PV.')
    atomic(run/'RESULT.json',receipt)
    print(json.dumps(dict(status=receipt['status'], cases=len(rows))))


if __name__=='__main__':
    main()
