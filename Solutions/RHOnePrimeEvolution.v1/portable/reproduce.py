#!/usr/bin/env python3
"""Fresh selected application proofs; kernel verification, not source-first PV.

Example:
 python3 reproduce.py --compiler /path/to/lean --generic-lean-path /p/mathlib/.lake/build/lib/lean:... --run /scratch/new-run --jobs 4
Use --check-only for source/dependency checks without compiling. Linux, GNU time
and prlimit are required. Generic package directories must have the pinned Git
revisions and clean tracked sources. No predecessor application objects are used.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

HERE=Path(__file__).resolve().parent
PREFIXES=('Mathlib','Lean','Init','Std','Aesop','Batteries','Qq')

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def load_json(text):
    def pairs(items):
        result={}
        for key,value in items:
            if key in result:raise ValueError('Duplicate JSON key '+key)
            result[key]=value
        return result
    return json.loads(text,object_pairs_hook=pairs)


def atomic(path,data):
    temporary=path.with_name(path.name+'.new')
    with temporary.open('x',encoding='utf-8') as f:
        json.dump(data,f,indent=2,ensure_ascii=False);f.write('\n');f.flush();os.fsync(f.fileno())
    os.replace(temporary,path)
    directory_fd=os.open(path.parent,os.O_RDONLY|os.O_DIRECTORY)
    try:os.fsync(directory_fd)
    finally:os.close(directory_fd)

def validate_sources(packet):
    manifest_path=packet/'SOURCE_MANIFEST.json';manifest=load_json(manifest_path.read_text())
    rows=manifest['modules'];table={}
    for row in rows:
        module=row['module']
        if not re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*',module):raise ValueError('Invalid module identity')
        if module in table:raise ValueError('Duplicate module identity '+module)
        expected='source/'+module.replace('.','/')+'.lean'
        if row['path']!=expected:raise ValueError('Invalid source path '+module)
        p=packet/expected
        if p.is_symlink() or not p.is_file():raise ValueError('Expected owned regular source '+module)
        if sha(p)!=row['sha256']:raise ValueError('Source hash mismatch '+module)
        imports=[]
        for line in p.read_text().split('\n'):
            if line.startswith('import '):imports.extend(line[7:].split('--',1)[0].split())
        if imports!=row['imports']:raise ValueError('Import association mismatch '+module)
        table[module]=row
    if len(table)!=manifest['module_count'] or manifest['module_count']<297:raise ValueError('Incomplete selected application manifest')
    visiting=set();visited=set()
    def visit(module):
        if module in visiting:raise ValueError('Application import cycle')
        if module in visited:return
        if module not in table:
            if any(module==x or module.startswith(x+'.') for x in PREFIXES):return
            raise ValueError('Missing application import '+module)
        visiting.add(module)
        for dependency in table[module]['imports']:visit(dependency)
        visiting.remove(module);visited.add(module)
    for root in manifest['roots']:visit(root)
    if visited!=set(table):raise ValueError('Unreachable or omitted application source')
    for key,file in [('controller_sha256','rebuild_closure.py'),('audit_runner_sha256','run_audit.py')]:
        if sha(packet/file)!=manifest[key]:raise ValueError('Controller identity mismatch '+file)
    return manifest

def validate_generic(paths,manifest):
    expected={r['name']:r['revision'] for r in manifest['generic_dependencies']};actual={}
    libraries=[]
    for raw in paths.split(':'):
        library=Path(raw).resolve(strict=True)
        if library.parts[-4:]!=('.lake','build','lib','lean'):raise ValueError('Generic library path must end .lake/build/lib/lean')
        package=library.parents[3]
        commit=subprocess.check_output(['git','-C',str(package),'rev-parse','HEAD'],text=True).strip()
        name=package.name
        if name not in expected or expected[name]!=commit:raise ValueError('Unexpected generic package/revision '+name)
        dirty=subprocess.check_output(['git','-C',str(package),'status','--porcelain','--untracked-files=no'],text=True)
        if dirty.strip():raise ValueError('Modified tracked generic source '+name)
        if name in actual:raise ValueError('Duplicate generic package '+name)
        actual[name]=commit;libraries.append(str(library))
    if set(actual)!=set(expected):raise ValueError('Incomplete generic dependency set')
    return libraries,actual

def main():
    ap=argparse.ArgumentParser(description=__doc__,allow_abbrev=False)
    ap.add_argument('--compiler',type=Path,required=True)
    ap.add_argument('--generic-lean-path',required=True)
    ap.add_argument('--run',type=Path)
    ap.add_argument('--jobs',type=int,default=2)
    ap.add_argument('--check-only',action='store_true')
    a=ap.parse_args()
    if a.jobs not in (1,2,3,4):raise ValueError('Worker count must be1..4')
    manifest=validate_sources(HERE)
    libraries,generic=validate_generic(a.generic_lean_path,manifest)
    compiler=a.compiler.resolve(strict=True)
    version=subprocess.check_output([str(compiler),'--version'],text=True).strip()
    if 'version 4.34.0-rc2' not in version:raise ValueError('Pinned Lean4.34.0-rc2 required')
    if a.check_only:
        print(json.dumps({'status':'PASS_SOURCE_AND_GENERIC_IDENTITIES_ONLY_NOT_PROOF_EXECUTION','modules':manifest['module_count'],'manifest_sha256':sha(HERE/'SOURCE_MANIFEST.json'),'compiler_sha256':sha(compiler),'generic':generic}));return
    if a.run is None:raise ValueError('--run is required for actual proof execution')
    run=a.run.resolve()
    if run.exists():raise ValueError('Fresh run directory required')
    run.mkdir(parents=True)
    began=time.monotonic()
    context={'compiler':str(compiler),'mathlib_commit':generic['mathlib'],'mathlib_lean_path':':'.join(libraries),'generic_dependency_versions':[{'name':k,'revision':v} for k,v in generic.items()]}
    controller=run/'controller';controller.mkdir()
    for name in ['rebuild_closure.py','run_audit.py','reproduce.py','SOURCE_MANIFEST.json']:
        (controller/name).write_bytes((HERE/name).read_bytes())
    atomic(controller/'BASELINE_IMPORTS.json',{'modules':[{'module':r['module'],'captured_path':r['path'],'sha256':r['sha256']} for r in manifest['modules']]})
    atomic(controller/'LOCAL_CONTEXT.json',context)
    command=[sys.executable,str(controller/'rebuild_closure.py'),'--repository',str(HERE),'--run',str(run/'compile'),'--roots',*manifest['roots'],'--jobs',str(a.jobs),'--compiler',str(compiler),'--generic-lean-path',':'.join(libraries)]
    atomic(run/'LAUNCH.json',{'status':'LAUNCH_NOT_ACCEPTANCE','frontend_sha256':sha(controller/'reproduce.py'),'manifest_sha256':sha(controller/'SOURCE_MANIFEST.json'),'compiler':str(compiler),'compiler_sha256':sha(compiler),'compiler_version':version,'command':command,'generic':generic})
    with (run/'compile.stdout').open('wb') as out,(run/'compile.stderr').open('wb') as err:
        process=subprocess.run(command,stdout=out,stderr=err)
    if process.returncode:raise RuntimeError('Fresh source build failed; preserved '+str(run))
    receipt=run/'compile/EXECUTION.json';e=load_json(receipt.read_text())
    if e['status']!='PASS_FRESH_TRANSITIVE_COMPILATION' or e['compiled_modules']!=manifest['module_count']:raise RuntimeError('Incomplete proof compilation')
    plan=load_json((run/'compile/PLAN.json').read_text());rows={r['module']:r for r in e['builds']}
    if sha(run/'compile/PLAN.json')!=e['PLAN_sha256']:raise RuntimeError('Compilation plan hash mismatch')
    for row in plan['modules']:
        if sha(Path(row['executed']))!=row['source_sha256']:raise RuntimeError('Executed source changed')
        if sha(run/'compile/objects'/(row['module'].replace('.','/')+'.olean'))!=rows[row['module']]['object_sha256']:raise RuntimeError('Compiled object changed')
    log=run/'compile/logs/FinalConsumerAudit.stdout'
    if 'INDEPENDENT_CANONICAL_AUDIT_PASS 25' not in log.read_text():raise RuntimeError('Missing actual complete canonical audit marker')
    audit_root=run/'audit-root';study=audit_root/'Solutions/RHOnePrimeEvolution.v1'
    (study/'scripts').mkdir(parents=True);(study/'integration_review').mkdir()
    atomic(study/'scripts/LOCAL_CONTEXT.json',context)
    (study/'integration_review/FinalConsumerAudit.lean').write_bytes((HERE/'source/FinalConsumerAudit.lean').read_bytes())
    audit_command=[sys.executable,str(controller/'run_audit.py'),'--repository',str(audit_root),'--run',str(run/'audit'),'--objects',str(run/'compile/objects')]
    with (run/'audit.stdout').open('wb') as out,(run/'audit.stderr').open('wb') as err:
        audit_process=subprocess.run(audit_command,stdout=out,stderr=err)
    if audit_process.returncode:raise RuntimeError('Independent exact-type/axiom/control audit failed; preserved '+str(run))
    audit=load_json((run/'audit/RESULT.json').read_text())
    if audit['status']!='PASS_INDEPENDENT_EXACT_TYPE_AXIOM_VALUE_AUDIT' or audit['headline_count']!=24 or audit['negative_mathematical_controls']!=6:raise RuntimeError('Incomplete independent audit')
    result={'status':'PASS_FRESH_RELOCATED_SOURCE_PROOFS_AND_24_HEADLINE_AUDIT','source_first_PV':False,'seconds':time.monotonic()-began,'module_count':manifest['module_count'],'roots':manifest['roots'],'frontend_sha256':sha(controller/'reproduce.py'),'source_manifest_sha256':sha(controller/'SOURCE_MANIFEST.json'),'compile_receipt_sha256':sha(receipt),'audit_receipt_sha256':sha(run/'audit/RESULT.json'),'compiler_sha256':sha(compiler),'generic':generic,'audit_command':audit_command,'metrics':{k:e[k] for k in ['sampled_peak_owned_tree_RSS_bytes','peak_individual_child_RSS_KiB','owned_allocated_disk_bytes','observed_SIGKILL_compiler_events']},'limit':'Explicit B source predicates remain hypotheses. Generic pinned libraries reused. No claim of whole-repository source audit, source-first PV or exact peak disk.'}
    atomic(run/'RESULT.json',result);print(json.dumps(result))

if __name__=='__main__':
    try:main()
    except (ValueError,RuntimeError,OSError,KeyError,subprocess.CalledProcessError) as error:
        print('ERROR: '+str(error),file=sys.stderr);sys.exit(1)
