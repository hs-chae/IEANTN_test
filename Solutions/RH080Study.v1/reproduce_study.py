#!/usr/bin/env python3
"""Reproduce frozen mathematical evidence from a clone/extracted source bundle.

Uses only this repository's application sources plus explicitly supplied pinned
Lean/Mathlib infrastructure. No historical /data or workspace object bank is a
fallback. Discovery-model sessions and restricted original-paper supplements are
separate, optional external studies, not deterministic proof reproduction.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(p):
    need(p.is_file() and not p.is_symlink(), 'Missing/aliased source: '+str(p))
    digest=hashlib.sha256()
    with p.open('rb') as stream:
        for block in iter(lambda:stream.read(2**20),b''):
            digest.update(block)
    return digest.hexdigest()


def read(p):
    def pairs(items):
        out = {}
        for key, value in items:
            need(key not in out, 'Duplicate JSON key')
            out[key] = value
        return out
    return json.loads(p.read_bytes(), object_pairs_hook=pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))


def publish(p, value):
    need(not os.path.lexists(p), 'Fresh receipt destination required')
    fd, name = tempfile.mkstemp(prefix='.study-', dir=p.parent)
    temporary = Path(name)
    try:
        with os.fdopen(fd, 'w') as f:
            json.dump(value, f, indent=2, allow_nan=False); f.write('\n'); f.flush(); os.fsync(f.fileno())
        os.link(temporary, p)
    finally:
        temporary.unlink()


def profiles(R):
    S = R/'Solutions/RH080Study.v1'
    old = R/'Solutions/RHOnePrimeEvolution.v1'
    cert = old/'gaussian_gap/portable/source'
    pv = [S/'pv/lean', S/'sine', S/'functional', cert]
    gaussian = [R, old/'gaussian_fourier', old/'gaussian_kernel', old/'gaussian_gap', cert]
    return {
      'pv': ('PVJointAudit', pv, {}),
      'canonical': ('PVCanonicalAudit', [R]+pv, {}),
      'cube': ('CubeConsumerAudit',[R,S/'estimates'],{'ThetaCubeSolution':R/'Solutions/ThetaCubePopulation.v1/Solution.lean'}),
      'zero': ('ZeroEnvelopeAudit',[R,S/'estimates'],{'ZeroEnvelopeSolution':R/'Solutions/ZeroCountEnvelope.v1/Solution.lean'}),
      'same_source': ('SameSourceConsumerAudit',[R,S/'estimates/same_source'],{'SameSourceSolution':R/'Solutions/PrimePowerPopulation.v2/Solution.lean'}),
      'pareto966': ('ParetoAudit',[R,S/'estimates/pareto966',S/'estimates'],{'ParetoSolution':R/'Solutions/ThetaCubePopulation.v2/Solution.lean'}),
      'g80': ('Primal80CanonicalAudit',[R,S/'primal80_gap',S/'primal80_fourier',S/'functional/primal40']+gaussian[1:],
              {'Primal80WitnessSolution':R/'Solutions/GaussianFourierWitness.v2/Solution.lean','Primal80AsymptoticSolution':R/'Solutions/RHAsymptoticGaussian.v2/Solution.lean'}),
      'g56': ('Primal56CanonicalAudit',[R,S/'primal56_gap',S/'primal56_fourier',S/'functional/primal28',S/'functional/primal40']+gaussian[1:],
              {'Primal56WitnessSolution':R/'Solutions/GaussianFourierWitness.v3/Solution.lean','Primal56AsymptoticSolution':R/'Solutions/RHAsymptoticGaussian.v3/Solution.lean'}),
      'figure': ('PopulationComparison',[S/'reports'],{}),
      'alternatives': ('RetunedBudgetBarrier',[S/'functional/alternatives'],{})}


def source_closure(R, profile):
    root, roots, aliases = profiles(R)[profile]
    generic = ('Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets')
    visited, active, rows = set(), set(), []
    def visit(module):
        if module in visited:
            return
        if any(module == p or module.startswith(p+'.') for p in generic):
            return
        need(module not in active, 'Application import cycle: '+module)
        active.add(module)
        candidates = [aliases.get(module)]+[p/(module.replace('.','/')+'.lean') for p in roots]
        source = next((p for p in candidates if p is not None and p.is_file()), None)
        need(source is not None, 'Missing repository-contained application source: '+module)
        need(source.resolve().is_relative_to(R), 'Application source escapes supplied repository')
        imports = []
        for line in source.read_text().splitlines():
            if line.startswith('import '):
                imports.extend(line[7:].split('--',1)[0].split())
        for dependency in imports:
            visit(dependency)
        active.remove(module);visited.add(module)
        rows.append(dict(profile=profile,module=module,path=str(source.relative_to(R)),sha256=sha(source),imports=imports))
    visit(root)
    return rows


def validate_context(context, S):
    c = read(context); pin = read(S/'estimates/DEPENDENCY_PINS.json')
    compiler = Path(c['compiler']).resolve(strict=True)
    need(sha(compiler) == c['compiler_sha256'] == pin['compiler_sha256'], 'Pinned compiler bytes differ')
    version = subprocess.check_output([str(compiler),'--version'],text=True).strip()
    need(version == c['compiler_version'] == pin['compiler_version'], 'Pinned compiler version differs')
    need(c['generic_dependencies'] == pin['generic_dependencies'], 'Generic dependency pins/order differ')
    paths = c['generic_lean_path'].split(':')
    need(len(paths)==8 and len(set(paths))==8, 'Exactly eight distinct generic libraries required')
    for name, dep in zip(paths,pin['generic_dependencies']):
        library = Path(name)
        need(library.is_absolute() and library.is_dir() and '/.lake/packages/' in name,
             'Generic library outside pinned package layout')
        need(library.parts[-4:]==('.lake','build','lib','lean'),'Generic library suffix differs')
        package = library.parents[3]
        need(package.name == dep['name'], 'Generic package identity/order differs')
        need(subprocess.check_output(['git','-C',str(package),'rev-parse','HEAD'],text=True).strip()==dep['revision'], 'Generic source revision differs')
        need(not subprocess.check_output(['git','-C',str(package),'status','--porcelain','--untracked-files=no'],text=True),'Generic source dirty')
    return c


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument('--repository',type=Path,default=Path(__file__).resolve().parents[2])
    parser.add_argument('--run',type=Path,required=True)
    parser.add_argument('--context',type=Path)
    parser.add_argument('--compiler',type=Path)
    parser.add_argument('--packages',type=Path)
    parser.add_argument('--lane',choices=['all','numerics','pv','estimates','g80','g56','figure','alternatives'],default='all')
    parser.add_argument('--check-only',action='store_true')
    parser.add_argument('--without-controls',action='store_true')
    parser.add_argument('--include-baseline',action='store_true')
    parser.add_argument('--flint-python',type=Path)
    a=parser.parse_args()
    R=a.repository.resolve(strict=True);S=R/'Solutions/RH080Study.v1'
    need((S/'pv/dual_grid.c').is_file(),'Repository study layout missing')
    need(not a.run.exists() and not a.run.is_symlink(),'Fresh --run directory required')
    need((a.context is not None) != (a.compiler is not None or a.packages is not None),
         'Use --context OR both --compiler and --packages')
    need(a.context is not None or (a.compiler is not None and a.packages is not None),'Both --compiler and --packages required')
    if a.lane=='alternatives':
        need(a.flint_python is not None,'Optional alternatives require explicit python-flint0.9.0 interpreter')
    run=a.run.resolve();need(not run.is_relative_to(R),'Run storage must be outside publishable repository')
    run.mkdir(parents=True);logs=run/'logs';logs.mkdir()
    flags=[] if not sys.flags.optimize else ['-O' if sys.flags.optimize==1 else '-OO']
    python=[sys.executable]+flags
    commands=[];start=time.monotonic();controller_sha=sha(Path(__file__))
    def execute(name,command,receipt=None):
        began=time.monotonic()
        timed=['/usr/bin/time','-v','-o',str(logs/(name+'.time'))]+list(map(str,command))
        with (logs/(name+'.stdout')).open('wb') as out,(logs/(name+'.stderr')).open('wb') as err:
            result=subprocess.run(timed,cwd=R,stdout=out,stderr=err,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
        row=dict(name=name,command=timed,returncode=result.returncode,seconds=time.monotonic()-began,
                 stdout_sha256=sha(logs/(name+'.stdout')),stderr_sha256=sha(logs/(name+'.stderr')),
                 time_sha256=sha(logs/(name+'.time')))
        commands.append(row)
        if result.returncode:
            publish(run/'FAILED.json',dict(status='FAILED_STUDY_CHILD_ROUTE',commands=commands))
            raise ValueError('Study child failed: '+name+'; see retained exact logs')
        if receipt is not None:
            need(receipt.is_file(),'Missing actual child receipt: '+name)
            row['receipt']=str(receipt);row['receipt_sha256']=sha(receipt)
        return row
    if a.context is None:
        context=run/'generic_context.json'
        execute('prepare-generic-context',python+[S.parent/'RHOnePrimeEvolution.v1/scripts/prepare_proof_context.py',
            '--packages',a.packages,'--compiler',a.compiler,'--output',context],context)
    else:
        context=run/'generic_context.json';context.write_bytes(a.context.read_bytes())
    c=validate_context(context,S)
    selected = (['pv','canonical','cube','zero','same_source','pareto966','g80','g56'] if a.lane=='all' else
                ['pv','canonical'] if a.lane=='pv' else ['cube','zero','same_source','pareto966'] if a.lane=='estimates' else
                [] if a.lane=='numerics' else [a.lane])
    closures={profile:source_closure(R,profile) for profile in selected}
    # Explicit resource and portability checks are preflight, not proof success.
    required_scripts=['pv/reproduce_joint.py','pv/reproduce_canonical.py','pv/verify_joint.py','pv/test_joint_cli.py',
        'pv/test_source_mutations.py','pv/parse_source.py','sine/generate_rational_cells.py',
        'functional/primal40/regenerate.py','functional/primal40/generate_kernel_cells.py','functional/primal40/prototype_cells.py',
        'functional/primal28/regenerate.py','primal80_fourier/generate_transform.py','primal56_fourier/generate_transform.py',
        'estimates/reproduce.py','estimates/test_controls.py','estimates/same_source/reproduce.py',
        'estimates/same_source/test_controls.py','estimates/same_source/test_validator.py','estimates/pareto966/reproduce.py',
        'estimates/pareto966/test_controls.py','estimates/pareto966/test_validator.py',
        'primal80_gap/reproduce_joint.py','primal80_gap/test_joint_controls.py','primal56_gap/reproduce_joint.py','primal56_gap/test_joint_controls.py']
    if a.lane=='figure':
        required_scripts+=['reports/reproduce_scalar.py']
    if a.lane=='alternatives':
        required_scripts+=['functional/alternatives/reproduce.py','functional/alternatives/probe.py']
    script_hashes={rel:sha(S/rel) for rel in required_scripts}
    for command in ['git','cc','prlimit']:
        need(shutil.which(command) is not None,'Required tool missing: '+command)
    need(Path('/usr/bin/time').is_file(),'GNU time missing')
    source_manifest=S/'REPRODUCTION_INPUTS.json'
    need(source_manifest.is_file(),'Frozen REPRODUCTION_INPUTS.json missing from source bundle')
    for row in read(source_manifest)['files']:
        relative=Path(row['path'])
        need(not relative.is_absolute() and '..' not in relative.parts,'Invalid repository-relative source identity')
        need(sha(R/relative)==row['sha256'],'Frozen reproduction source differs: '+row['path'])
    plan=dict(status='FROZEN_STUDY_REPRODUCTION_PLAN_NOT_ACCEPTANCE',lane=a.lane,selected_profiles=selected,
              closures=closures,context_sha256=sha(context),controller_sha256=controller_sha,child_script_sha256=script_hashes,
              generic_dependencies=c['generic_dependencies'],predecessor_application_objects_permitted=False,
              optional_baseline=a.include_baseline,controls=not a.without_controls,python_optimization=sys.flags.optimize,
              application_lookup='Fresh per-lane object banks only; canonical append explicitly consumes this run PV bank.',
              external_scopes='Original supplement/Arb replay requires separately supplied pinned primary sources; discovery-model sessions require model/runtime and are not byte-reproducible.')
    publish(run/'PLAN.json',plan)
    # Test actual safe CLI routes; do not pass --help to generators with top-level
    # write behavior. No proof run is implied by these child help/preflight routes.
    for rel in ['pv/reproduce_joint.py','pv/reproduce_canonical.py','estimates/reproduce.py','estimates/same_source/reproduce.py',
                'estimates/pareto966/reproduce.py','primal80_gap/reproduce_joint.py','primal56_gap/reproduce_joint.py',
                'functional/primal40/regenerate.py','functional/primal28/regenerate.py']:
        execute('help-'+rel.replace('/','-').replace('.py',''),python+[S/rel,'--help'])
    execute('pv-source-preflight',python+[S/'pv/reproduce_joint.py','--repository',R,'--context',context,'--check-only'])
    if a.check_only:
        publish(run/'PREFLIGHT.json',dict(status='PASS_STUDY_SOURCE_CONTEXT_AND_ACTUAL_CLI_PREFLIGHT_ONLY',
                selected_profiles=selected,source_counts={k:len(v) for k,v in closures.items()},commands=commands,
                plan_sha256=sha(run/'PLAN.json'),no_mathematical_proof_execution=True))
        print(json.dumps(dict(status='PASS_STUDY_SOURCE_CONTEXT_AND_ACTUAL_CLI_PREFLIGHT_ONLY',profiles=len(closures))))
        return
    if a.lane in ['all','numerics']:
        regeneration=run/'regeneration';regeneration.mkdir()
        execute('sine-byte-regeneration',python+[S/'sine/generate_rational_cells.py','--check'])
        for degree in ['40','28']:
            out=regeneration/('cells-'+degree)
            execute('regenerate-cells-'+degree,python+[S/('functional/primal'+degree+'/regenerate.py'),'--out',out],out/'REGENERATION_RECEIPT.json')
        shadow=regeneration/'shadow/network/Solutions/RH080Study.v1';shadow.mkdir(parents=True)
        for rel in ['functional/primal40','functional/primal28','primal80_fourier','primal56_fourier']:
            shutil.copytree(S/rel,shadow/rel,ignore=shutil.ignore_patterns('__pycache__','evidence','reviews','*.olean','*.ilean'))
        for degree in ['80','56']:
            folder='primal'+degree+'_fourier'
            execute('regenerate-transform-'+degree,python+[shadow/folder/'generate_transform.py'])
            names=['INPUTS.json','Primal'+degree+'CoefficientTransform.lean']
            if degree=='56':names.append('Primal56OriginalInput.lean')
            for name in names:
                need((shadow/folder/name).read_bytes()==(S/folder/name).read_bytes(),'Regenerated exact transform differs: '+name)
        # Actual source regeneration and compilation without claiming a proof.
        frontend=regeneration/'C-frontend';frontend.mkdir();(frontend/'lean').mkdir()
        for name in ['parse_source.py','dual_grid.c']:
            shutil.copyfile(S/'pv'/name,frontend/name)
        execute('actual-C-frontend',python+[frontend/'parse_source.py'])
        for name in ['DualAST.lean','DualSource.lean']:
            need((frontend/'lean'/name).read_bytes()==(S/'pv/lean'/name).read_bytes(),'Regenerated C source AST differs')
        execute('actual-C-compile',[shutil.which('cc'),'-std=c11','-O2','-Wall','-Wextra','-Werror','-pedantic',frontend/'dual_grid.c','-o',frontend/'dual_grid'])
        execute('actual-C-output',[frontend/'dual_grid'])
        need((logs/'actual-C-output.stdout').read_bytes()==b'1221161\n','Actual C captured bytes differ')
        artifacts=[dict(path=str(p.relative_to(regeneration)),sha256=sha(p),bytes=p.stat().st_size)
                   for p in sorted(regeneration.rglob('*')) if p.is_file()]
        publish(regeneration/'ARTIFACT_HASHES.json',dict(status='GENERATED_ARTIFACT_HASH_INVENTORY_NOT_A_PROOF',
                files=artifacts,total_logical_bytes=sum(row['bytes'] for row in artifacts),random_seed=None))
        publish(regeneration/'RESULT.json',dict(status='PASS_DETERMINISTIC_SOURCE_AND_NUMERICAL_REGENERATION_NOT_A_PROOF',
            cell_counts={'degree80':1193,'degree56':1135},random_seed=None,actual_C_source_sha256=sha(frontend/'dual_grid.c'),
            actual_C_binary_sha256=sha(frontend/'dual_grid'),actual_stdout_sha256=sha(logs/'actual-C-output.stdout'),
            artifact_inventory_sha256=sha(regeneration/'ARTIFACT_HASHES.json')))
    if a.lane in ['all','pv']:
        pv=run/'pv';canonical=run/'canonical'
        execute('pv-cold45',python+[S/'pv/reproduce_joint.py','--repository',R,'--context',context,'--run',pv],pv/'RESULT.json')
        execute('pv-independent-readback',python+[S/'pv/verify_joint.py','--run',pv,'--output',run/'PV_READBACK.json'],run/'PV_READBACK.json')
        execute('canonical-append8',python+[S/'pv/reproduce_canonical.py','--repository',R,'--context',context,'--accepted-run',pv,'--run',canonical],canonical/'RESULT.json')
        if not a.without_controls:
            control=run/'pv-cli-controls'
            execute('pv-allmode-CLI-controls',python+[S/'pv/test_joint_cli.py','--repository',R,'--context',context,'--accepted-run',pv,'--run',control],control/'RESULT.json')
            mutation_context=run/'mutation_context.json';mutation_context.write_text(json.dumps(dict(compiler=c['compiler'],LEAN_PATH=str(pv/'objects')+':'+c['generic_lean_path']))+'\n')
            for label,mode in [('normal',[]),('O',['-O']),('OO',['-OO'])]:
                target=run/('pv-source-controls-'+label)
                execute('pv-source-controls-'+label,[sys.executable]+mode+[S/'pv/test_source_mutations.py','--context',mutation_context,'--run',target],target/'ACCEPTANCE.json')
    if a.lane in ['all','estimates']:
        for lane,script in [('cube',S/'estimates/reproduce.py'),('zero',S/'estimates/reproduce.py'),
                            ('same_source',S/'estimates/same_source/reproduce.py'),('pareto966',S/'estimates/pareto966/reproduce.py')]:
            target=run/lane
            command=python+[script,'--repository',R,'--context',context,'--run',target]
            if lane in ['cube','zero']:command+=['--lane',lane]
            execute('estimate-'+lane,command,target/'RESULT.json')
            if not a.without_controls and lane!='zero':
                control=run/(lane+'-controls')
                execute('estimate-controls-'+lane,python+[script.with_name('test_controls.py'),'--context',context,'--objects',target/'objects','--run',control],control/'RESULT.json')
                if lane in ['same_source','pareto966']:
                    validator=run/(lane+'-validator-controls')
                    execute('validator-'+lane,python+[script.with_name('test_validator.py'),'--repository',R,'--context',context,'--run',validator],validator/'RESULT.json')
    cert=R/'Solutions/RHOnePrimeEvolution.v1/gaussian_gap/portable/source'
    for lane in ['g80','g56']:
        if a.lane in ['all',lane]:
            degree=lane[1:];target=run/lane;script=S/('primal'+degree+'_gap/reproduce_joint.py')
            execute(lane+'-full-cold80',python+[script,'--context',context,'--lean-cert-source',cert,'--out',target,
                        '--workers','4','--worker-memory-gib','32'],target/'RESULT.json')
            if not a.without_controls:
                controls=run/(lane+'-controls')
                execute(lane+'-controls',python+[script.with_name('test_joint_controls.py'),'--context',context,'--accepted',target,'--out',controls],controls/'RESULT.json')
    if a.lane=='figure':
        target=run/'figure-scalar'
        execute('figure-scalar-only',python+[S/'reports/reproduce_scalar.py','--context',context,'--run',target],target/'RESULT.json')
    if a.lane=='alternatives':
        target=run/'alternatives'
        execute('alternatives-scalar-and-external-E',python+[S/'functional/alternatives/reproduce.py','--context',context,'--flint-python',a.flint_python,'--out',target],target/'RESULT.json')
    if a.include_baseline:
        for packet,jobs in [('frontier300','4'),('gaussian53','2')]:
            target=run/('baseline-'+packet)
            execute('historical-baseline-'+packet,python+[S/'baseline/reproduce_baseline.py','--repository',R,'--context',context,'--run-root',target,'--packet',packet,'--jobs',jobs],target/'run/RESULT.json')
    need(sha(Path(__file__))==controller_sha,'Study controller changed during run')
    for rel,value in script_hashes.items():
        need(sha(S/rel)==value,'Child controller changed during reproduction: '+rel)
    for rows in closures.values():
        for row in rows:
            need(sha(R/row['path'])==row['sha256'],'Mathematical source changed during reproduction')
    status=('PASS_STUDY_REPLAY_CONTROLS_OMITTED' if a.without_controls else
            'PASS_FULL_FROZEN_STUDY_MATHEMATICAL_REPRODUCTION' if a.lane=='all' else
            'PASS_SELECTED_STUDY_REPRODUCTION')
    publish(run/'RESULT.json',dict(status=status,lane=a.lane,seconds=time.monotonic()-start,commands=commands,
            plan_sha256=sha(run/'PLAN.json'),controller_sha256=controller_sha,source_first_PV='Only the selected C+canonical path; other kernels remain D and numerical probes E.',
            original_outcomes_unchanged=True,model_discovery_sessions_reproduced=False,
            external_original_supplement_reproduced=False,without_controls=a.without_controls,
            limitations='Reproduces fixed mathematical/source evidence, not stochastic/model-discovery traces, source paper computations, official Comparator approval or compiler/runtime/hardware correctness. Child receipts specify actual resource metrics.'))
    print(json.dumps(dict(status=status,lane=a.lane,children=len(commands))))


if __name__=='__main__':
    main()
