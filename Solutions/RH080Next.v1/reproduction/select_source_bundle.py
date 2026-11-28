#!/usr/bin/env python3
"""Select exact campaign application sources; never create an archive or claim a proof.

The universe is explicit: all publishable project files, named proof-plan unions,
all16 exact locked payloads, and the core/node scaffold used by the normal CLI.
A missing final source family or reviewed commit leaves the selection incomplete.
"""
from __future__ import annotations
import argparse,collections,json,os,subprocess
from pathlib import Path
from bootstrap_context import PROJECT,REPOSITORY,atomic,need,read_json,sha,validate_context

GENERIC={'Mathlib','Lean','Init','Std','Aesop','Batteries','Qq','ProofWidgets','Plausible','ImportGraph','LeanSearchClient'}
REQUIRED_FAMILIES={'dual49':49,'gaussian92':92,'population91':91,'w4_math35':35,
                   'canonical_finite':None,'canonical_w4':None,'w4_actual':None}
ROOT_FILES=['LICENSE','README.md','CONTRIBUTING.md','SECURITY.md','STATE.md','GRAPH.md',
            'AGENTS.md','CLAUDE.md','requirements-dev.txt',
            'lakefile.toml','lake-manifest.json','lean-toolchain','IEANTN.lean',
            'docs/ARCHITECTURE.md','docs/NODES.md','scripts/ieantn.py','scripts/verify-comparator.sh']
FORBIDDEN_PARTS={'.git','.lake','__pycache__','memory','transcripts','sessions','credentials'}
OBJECT_SUFFIXES={'.olean','.ilean','.pyc','.o','.so','.a'}
PRIVATE_NAMES={'.env','auth.json','credentials.json','events.jsonl','worker_prompt.txt'}
CANONICAL_W4_ROOTS=['CanonicalW4NormNodeSolution','CanonicalW4GlobalNodeSolution',
 'CanonicalAnalyticFlatNodeSolution','CanonicalW4PopulationNodeSolution',
 'CanonicalW4ActualConsumers','CanonicalW4EvolutionAudit']

def imports(path):
    # Imports are a Lean module header. Stop before proof/data commands so a
    # generated multi-megabyte literal is never lexed as header text.
    names=[];depth=0;quoted=False
    with path.open()as stream:
        for line in stream:
            prefix=line.lstrip()
            if not depth and not quoted and prefix and not prefix.startswith(('/-','--','import ','public import ','prelude','module','\n')):
                return names
            out=[];i=0
            while i<len(line):
                ch=line[i];pair=line[i:i+2]
                if depth:
                    if pair=='/-':depth+=1;i+=2;continue
                    if pair=='-/':depth-=1;i+=2;continue
                    out.append(' ');i+=1;continue
                if quoted:
                    if ch=='\\':out.extend('  ');i+=2;continue
                    if ch=='"':quoted=False
                    out.append(' ');i+=1;continue
                if pair=='/-':depth=1;i+=2;continue
                if pair=='--':break
                if ch=='"':quoted=True;out.append(' ');i+=1;continue
                out.append(ch);i+=1
            clean=''.join(out).strip()
            if not clean:continue
            if clean.startswith('public import '):names.extend(clean[14:].split())
            elif clean.startswith('import '):names.extend(clean[7:].split())
            elif clean not in {'prelude','module'}:return names
    return names

def git(args):
    return subprocess.run(['git','-C',str(REPOSITORY)]+args,check=True,
        capture_output=True,env=dict(os.environ,GIT_OPTIONAL_LOCKS='0')).stdout

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--context',required=True,type=Path);ap.add_argument('--out',required=True,type=Path)
    ap.add_argument('--proof-plan',action='append',default=[],metavar='FAMILY=PATH')
    ap.add_argument('--reviewed-commit',help='Final reviewed HEAD; every selected repository byte must match it')
    ap.add_argument('--require-complete',action='store_true')
    a=ap.parse_args();need(not os.path.lexists(a.out),'Fresh bundle-selection output required')
    need(not a.out.resolve().is_relative_to(REPOSITORY.resolve()),'Private bundle-selection output must be outside the source checkout')
    selector_hash=sha(Path(__file__))
    context,_=validate_context(read_json(a.context));a.out.mkdir(parents=True)
    selected={};excluded=[];unresolved=[];identities=[];families={};plan_hashes=[];recipes=[]
    def problem(kind,**details):unresolved.append(dict(kind=kind,**details))
    def relative(path):
        p=Path(path)
        return p.relative_to(REPOSITORY).as_posix()if p.is_absolute()else p.as_posix()
    def add(path,reason,expected=None):
        p=Path(path)
        if not p.is_absolute():p=REPOSITORY/p
        try:rel=p.relative_to(REPOSITORY).as_posix()
        except ValueError:problem('source_outside_repository',source_basename=p.name,reason=reason);return
        if p.is_symlink()or not p.is_file():problem('missing_or_aliased_source',file=rel,reason=reason);return
        digest=sha(p)
        if expected is not None and digest!=expected:problem('source_hash_differs',file=rel,expected=expected,actual=digest,reason=reason);return
        if rel in selected:
            need(selected[rel]['sha256']==digest,'Source changed within selection: '+rel)
            selected[rel]['reasons'].add(reason)
        else:selected[rel]=dict(file=rel,sha256=digest,bytes=p.stat().st_size,reasons={reason})
    # Exact numerical producer manifests are provenance, never numerical proof.
    finite_path=PROJECT/'pv/evidence/FINAL_FAP_SOURCE_COLD_INPUTS_V2.json'
    finite=read_json(finite_path);need(len(finite['sources'])==681 and len(finite['data'])==34,'Fixed finite source/data universe differs')
    finite_csv={r['path']:r for r in finite['data']}
    finite_input='Solutions/RH080Study.v1/ablation/followup/independent-global-chord/inputs/witness-ap.json'
    add(finite_input,'finite17_fixed_input','9f545a294f104a1baaeccbb9bf625f6338fc020af9dce9ff7bd34352630a586a')
    finite_producer=PROJECT/'dual/produce_fft_forest_certificate.py';add(finite_producer,'finite17_producer')
    recipes.append(dict(id='finite17',producer=relative(finite_producer),producer_sha256=sha(finite_producer),
        command=['python3',relative(finite_producer),'--stages','17','--out','FRESH_FINITE_CANDIDATE'],
        fixed_input=finite_input,expected_inventory=relative(finite_path),expected_inventory_sha256=sha(finite_path),
        omitted_outputs=[dict(file=r['path'],sha256=r['sha256'],bytes=r['bytes'])for r in finite['data']],
        omitted_output_count=34,proposal_is_not_proof=True))
    n24_path=PROJECT/'dual/evidence/W4_N24_EXPECTED_INPUTS.json';n24=read_json(n24_path)
    need(n24['status']=='EXACT_EXPECTED_INPUT_INVENTORY_FROM_FROZEN_ORIGINAL_PLANS_NOT_PROOF'
        and n24['counts']==dict(sources=1033,generated_modules=1020,csv=937),'Exact N24 inventory differs')
    n24_generated={Path(r['file']).stem:r for r in n24['generated_modules']}
    checker_owned=[r for r in n24['sources']if r['kind']=='checker_owned']
    need(len(checker_owned)==1 and checker_owned[0]['module']=='W4D24ClaimAudit','Exact checker-owned generated source differs')
    n24_generated.update({r['module']:r for r in checker_owned})
    checker=PROJECT/'dual/reproduce_fft_dag_v2.py';add(checker,'N24_checker_owned_source_generator',n24['original_controller_sha256'])
    n24_by_file={r['file']:r for r in n24['generated_modules']+n24['payloads']+checker_owned}
    producer=PROJECT/'dual/produce_fft_dag_certificate.py';add(producer,'N24_producer',n24['producer_sha256'])
    add(n24['source_input'],'N24_fixed_input',n24['input_sha256'])
    virtual_prefix='Solutions/RH080Next.v1/generated/w4-dag24/'
    recipe_outputs=[dict(file=virtual_prefix+r['file'],sha256=r['sha256'],bytes=r['bytes'])
        for r in n24['generated_modules']+n24['payloads']]
    recipes.append(dict(id='N24',producer=relative(producer),producer_sha256=n24['producer_sha256'],
        command=['python3',relative(producer),'--stages','24','--chunk-log','13',
                 '--pairs-per-module','524288','--out','FRESH_N24_CANDIDATE'],
        fixed_input=n24['source_input'],fixed_input_sha256=n24['input_sha256'],
        expected_inventory=relative(n24_path),expected_inventory_sha256=sha(n24_path),
        parameters={k:n24[k]for k in ['stages','n','chunk','pairs_per_module','namespace','final_module',
                                      'norm_numerator','total_abs','quad']},
        omitted_outputs=recipe_outputs,omitted_output_count=1957,proposal_is_not_proof=True))
    recipes.append(dict(id='N24_checker_owned_audit',producer=relative(checker),producer_sha256=n24['original_controller_sha256'],
        command=['python3','-u',relative(checker),'--context','PINNED_CONTEXT','--candidate','FRESH_N24_CANDIDATE',
                 '--run','FRESH_N24_SOURCE_COLD_RUN','--workers','N'],
        omitted_outputs=[dict(file=virtual_prefix+r['file'],sha256=r['sha256'])for r in checker_owned],
        omitted_output_count=1,generated_during_source_cold_controller=True,proposal_is_not_proof=True))
    finite_generated={(r['module'],r['sha256']):r['path']for r in finite['sources']if '/generated/fap17/'in r['path']}
    # Every current project file is a candidate; final reviewed-commit matching
    # below, rather than a filename heuristic, establishes review admission.
    for p in sorted(PROJECT.rglob('*')):
        if not p.is_file()and not p.is_symlink():continue
        rel=p.relative_to(REPOSITORY).as_posix();parts=set(p.relative_to(PROJECT).parts)
        reason=None
        if parts&FORBIDDEN_PARTS:reason='private_or_build_directory'
        elif p.name in PRIVATE_NAMES:reason='private_transcript_or_credential_filename'
        elif p.suffix in OBJECT_SUFFIXES:reason='compiled_object_or_bytecode_retained_in_workspace'
        elif rel in finite_csv:
            need(sha(p)==finite_csv[rel]['sha256'],'Fixed finite CSV differs before omission')
            reason='exact_finite17_regeneration_recipe_and_expected_hash'
        elif rel.startswith(virtual_prefix):
            row=n24_by_file.get(p.name)
            if row and sha(p)==row['sha256']:reason='exact_N24_regeneration_recipe_and_expected_hash'
            else:problem('unmapped_generated_N24_file',file=rel);continue
        elif not p.is_symlink():
            with p.open('rb')as f:magic=f.read(4)
            if magic==b'\x7fELF':reason='compiled_executable_retained_in_workspace'
        if reason:excluded.append(dict(file=rel,reason=reason));continue
        add(p,'all_project_files_pending_final_review')
    # Core and all node metadata are needed by the normal CLI's global registry;
    # unrelated Solutions are not selected by this rule.
    for root in [REPOSITORY/'IEANTN',REPOSITORY/'Tools']:
        for p in sorted(root.rglob('*')):
            if p.is_file()and not any(x in p.parts for x in FORBIDDEN_PARTS):add(p,'normal_CLI_core_and_node_scaffold')
    for p in ROOT_FILES:add(p,'root_dependency_manifest_or_normal_CLI_documentation')
    # Original dual frontend/physical source bytes and external checker inputs.
    for directory in ['Solutions/RH080Study.v1/pv','Solutions/RH080Study.v1/functional']:
        root=REPOSITORY/directory
        for p in sorted(root.iterdir()):
            if p.is_file()and p.suffix in {'.c','.h','.hpp','.json','.py','.md'}:add(p,'original_dual_program_generator_input_or_contract')
    def consume(label,path,rows,expected_count=None):
        if expected_count is not None:need(len(rows)==expected_count,'Proof-plan source population differs: '+label)
        seen=set();family_rows=[]
        for row in rows:
            n=row['module'];raw=row.get('path',row.get('origin',row.get('original',row.get('source_origin',row.get('source')))))
            digest=row.get('source_sha256',row.get('sha256'));need(type(raw)is str and type(digest)is str,'Unrecognized exact proof-source row')
            p=Path(raw);p=p if p.is_absolute()else REPOSITORY/p
            generated=None
            try:rel=p.relative_to(REPOSITORY).as_posix()
            except ValueError:
                g=n24_generated.get(n)
                if g and digest==g['sha256']:
                    rel=virtual_prefix+g['file'];generated='N24'
                elif (n,digest)in finite_generated:
                    rel=finite_generated[(n,digest)];p=REPOSITORY/rel
                else:problem('unresolved_external_proof_source',family=label,module=n,source_basename=p.name,sha256=digest);continue
            identity=(n,rel,digest);need(identity not in seen,'Duplicate written-source identity in '+label);seen.add(identity)
            if generated is None:
                add(p,'proof_family:'+label,digest)
                deps=imports(p)if p.is_file()else[]
                if 'imports'in row:
                    recorded=[d for d in deps if d.split('.')[0]not in GENERIC]if label in {'gaussian92','population91'}else deps
                    need(recorded==row['imports'],'Actual imports differ from exact plan: '+label+'/'+n)
            else:deps=n24_generated[n]['imports']
            entry=dict(family=label,module=n,file=rel,sha256=digest,imports=deps)
            if generated:entry['regenerate_before_compile']=generated
            identities.append(entry);family_rows.append(entry)
        families[label]=dict(source_rows=len(rows),resolved_written_source_identities=len(family_rows),
            plan_sha256=sha(path),plan_kind='explicit_selected_proof_source_inventory')
        plan_hashes.append(dict(family=label,sha256=sha(path),manifest_basename=path.name))
        return family_rows
    consume('finite681',finite_path,finite['sources'],681)
    common_path=PROJECT/'ablation/review/COMMON169_SOURCE_INPUTS.json';common=read_json(common_path)
    consume('common169',common_path,common['modules'],169)
    consume('N24_1033',n24_path,[dict(r,origin=r.get('repository_source')or('/FRESH_N24_CANDIDATE/'+r['file']))for r in n24['sources']],1033)
    supplied={}
    for value in a.proof_plan:
        label,separator,raw=value.partition('=');need(separator and label in REQUIRED_FAMILIES and label not in supplied,'Exact unique named proof family required')
        path=Path(raw);plan=read_json(path);rows=plan.get('source_rows',plan.get('modules'))
        if isinstance(rows,dict):rows=[dict(v,module=n)for n,v in rows.items()]
        need(type(rows)is list,'Exact source rows required: '+label)
        if label.startswith('canonical')or label=='w4_actual':
            expected_roots={'canonical_finite':['CanonicalEvolutionAudit'],
                'canonical_w4':CANONICAL_W4_ROOTS,
                'w4_actual':['W4FFTCertifiedNorm','FFTW4SourceCertificate','FFTW4MainNumerics',
                             'FFTW4MainConsumers','PopulationEnvelopeConsumers','FFTW4MainAudit']}[label]
            need(plan.get('roots')==expected_roots,'Exact selected final proof roots differ: '+label)
            rows=rows+plan.get('accepted_dependencies',[])
            need(set(expected_roots)<={r['module']for r in rows},'Selected final root source rows missing: '+label)
        consume(label,path,rows,REQUIRED_FAMILIES[label]);supplied[label]=True
    for label in REQUIRED_FAMILIES:
        if label not in supplied:problem('required_proof_family_not_supplied',family=label)
    # Check selected proof import closure by written-source family. Module names
    # in distinct files remain separate identities throughout the manifest.
    by_family=collections.defaultdict(dict);global_modules=collections.defaultdict(set)
    for r in identities:by_family[r['family']][r['module']]=r;global_modules[r['module']].add(r['file'])
    for row in identities:
        for module in row['imports']:
            if module.split('.')[0]in GENERIC or module in by_family[row['family']]:continue
            direct=REPOSITORY/(module.replace('.','/')+'.lean')
            if direct.is_file():add(direct,'selected_proof_import:'+module)
            elif len(global_modules.get(module,set()))!=1:problem('unresolved_selected_proof_import',family=row['family'],module=row['module'],imported=module)
    # Exactly16 canonical payload directories, not every repeated LOCK snapshot.
    trials=[]
    for kind,root,count in [('primary3',PROJECT/'ablation/review/primary_locked_payloads',3),
       ('censored13',PROJECT/'ablation/review/supplemental_evidence_v1/locked_payloads',13)]:
        dirs=sorted(p for p in root.iterdir()if p.is_dir())if root.is_dir()else[]
        if len(dirs)!=count:problem('locked_payload_population_differs',kind=kind,expected=count,actual=len(dirs))
        for directory in dirs:
            lock=directory/'LOCK.json';value=read_json(lock);entries=value['files']
            need(len(entries)==len({r['path']for r in entries}),'Duplicate locked payload source')
            add(lock,'all16_locked_payload:'+directory.name)
            for entry in entries:
                need(Path(entry['path']).name==entry['path'],'Locked path escape')
                add(directory/entry['path'],'all16_locked_payload:'+directory.name,entry['sha256'])
            trials.append(dict(trial=directory.name,original_primary_status='admissible'if kind=='primary3'else'output_ceiling_censored',
                lock_file=relative(lock),lock_sha256=sha(lock),locked_files=len(entries)))
    if len({r['trial']for r in trials})!=16:problem('all16_distinct_locked_payload_universe_incomplete')
    for n in CANONICAL_W4_ROOTS:
        p=PROJECT/'explicit'/(n+'.lean')
        if not p.is_file():problem('final_canonical_source_pending',module=n,file=relative(p))
    # The CLI executable imports the complete core umbrella, whose scaffold is
    # already selected. Check every scaffold import recursively without loading
    # unrelated application solution trees.
    for p in list(selected):
        if p.endswith('.lean')and(p.startswith('IEANTN/')or p.startswith('Tools/')or p=='IEANTN.lean'):
            for module in imports(REPOSITORY/p):
                if module.split('.')[0]in GENERIC:continue
                target=module.replace('.','/')+'.lean'
                if target not in selected:problem('unresolved_normal_CLI_core_import',file=p,imported=module)
    head=git(['rev-parse','HEAD']).decode().strip();tracked=set(git(['ls-files','-z']).decode().split('\0'))
    project_prefix=PROJECT.relative_to(REPOSITORY).as_posix()+'/'
    for rel in tracked:
        if rel.startswith(project_prefix)and rel not in finite_csv and not(REPOSITORY/rel).exists():
            if not set(Path(rel).parts)&FORBIDDEN_PARTS and Path(rel).suffix not in OBJECT_SUFFIXES:
                problem('reviewed_project_source_missing_from_filesystem',file=rel)
    if not a.reviewed_commit:problem('final_reviewed_commit_not_supplied',current_HEAD=head)
    elif a.reviewed_commit!=head:problem('reviewed_commit_is_not_HEAD',reviewed_commit=a.reviewed_commit,current_HEAD=head)
    else:
        changed=set(git(['diff','--name-only',head,'--']).decode().splitlines())
        for rel in selected:
            if rel not in tracked:problem('selected_source_not_in_reviewed_commit',file=rel)
            elif rel in changed:problem('selected_source_differs_from_reviewed_commit',file=rel)
    for rel,row in selected.items():need(sha(REPOSITORY/rel)==row['sha256'],'Source changed during bundle selection: '+rel)
    files=[dict(row,reasons=sorted(row['reasons']))for _,row in sorted(selected.items())]
    status='PASS_EXACT_REVIEWED_CAMPAIGN_SOURCE_SELECTION'if not unresolved else'INCOMPLETE_SOURCE_SELECTION_NO_FINAL_BUNDLE_ACCEPTANCE'
    need(sha(Path(__file__))==selector_hash,'Selector changed during source selection')
    manifest=dict(status=status,selector_sha256=selector_hash,context_sha256=sha(a.context),
        compiler_sha256=context['compiler_sha256'],compiler_version=context['compiler_version'],generic_dependencies=context['generic_dependencies'],
        reviewed_commit=a.reviewed_commit,current_HEAD=head,files=files,selected_files=len(files),selected_bytes=sum(r['bytes']for r in files),
        exact_written_source_identities=identities,proof_family_coverage=families,proof_plan_identities=plan_hashes,
        locked_payloads=trials,regeneration_recipes=recipes,excluded_existing_files=excluded,unresolved=unresolved,
        selection_policy_author='Codex analytic_review at owner/root request',
        requested_universe='Complete selected campaign application proof/program/generator/input sources; all reviewed project files; all16 locks;169 common exposure; selected normal canonical CLI/core/node scaffold; exact regenerated N17/N24 outputs',
        inclusion_criteria=['Every project file passes final reviewed-commit byte matching except enumerated exclusions',
            'Union of exact identity-keyed source rows in681/49/92/91/35/169/N24/canonical/actual-consumer inventories',
            'All16 exact LOCK files and each enumerated payload byte','Root dependency manifests/docs and normal CLI core/node scaffold',
            'Original dual C/frontend/fixed inputs and exact N17/N24 producer/input/expected-output inventories'],
        exclusion_criteria=['Git/Lake/cache/private memory/transcript/credential material','Compiled objects/executables retained in workspace',
            'Only explicitly enumerated N17 CSV and N24 generated Lean/CSV with exact regeneration recipes/pins',
            'Unrelated application Solutions outside the explicit selected dependency unions'],
        coverage_is_not_a_source_claim_audit=True,mathematical_proof_acceptance=False,
        all_included_project_sources_are_not_claimed_compiled=True,
        archive_created=False,cleanup_performed=False,credentials_or_private_research_SDK_included=False)
    atomic(a.out/'SOURCE_BUNDLE_MANIFEST.json',manifest)
    print(json.dumps(dict(status=status,selected_files=len(files),selected_bytes=manifest['selected_bytes'],
        written_source_identities=len(identities),locked_payloads=len(trials),unresolved=len(unresolved))))
    if a.require_complete:need(not unresolved,'Source bundle selection has unresolved coverage/review obligations')
if __name__=='__main__':main()
