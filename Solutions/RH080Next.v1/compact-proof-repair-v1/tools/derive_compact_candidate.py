#!/usr/bin/env python3
"""Portable source-only candidate derivation; never a numerical/Lean/PV success."""
import argparse,os,shutil,subprocess,sys,tempfile,time
from pathlib import Path
from compact_contract import PACKAGE,HELPERS,AUDIT,FINAL,GENERATOR_SHA,load,sha,need,publish,imports,validate_original,validate_derived

def header_map(path):
    result={}
    for line in path.read_text().splitlines():
        if line.startswith('def ')or line.startswith('theorem '):
            need(':='in line,'Unsupported generated declaration header');name=line.split()[1];need(name not in result,'Duplicate public declaration');result[name]=line.split(':=',1)[0]
    return result

def clone(source,target,storage):
    need(not os.path.lexists(target),'Fresh destination required')
    target.parent.mkdir(parents=True,exist_ok=True)
    if storage=='hardlink':
        os.link(source,target);need(source.stat().st_ino==target.stat().st_ino and source.stat().st_dev==target.stat().st_dev,'Immutable source/data hardlink differs')
    else:shutil.copyfile(source,target)

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--candidate',type=Path,required=True);ap.add_argument('--out',type=Path,required=True)
    ap.add_argument('--project-root',type=Path,default=PACKAGE.parent);ap.add_argument('--input',type=Path)
    ap.add_argument('--storage',choices=['hardlink','copy'],default='hardlink');a=ap.parse_args()
    need(not os.path.lexists(a.out),'Fresh derived candidate directory required')
    a.candidate=a.candidate.resolve(strict=True);a.project_root=a.project_root.resolve(strict=True);a.out=a.out.absolute()
    original=validate_original(a.candidate,a.project_root,a.input);stage=original['stages'];started=time.monotonic();original_plan_sha=sha(a.candidate/'PLAN.json')
    a.out.mkdir(parents=True);(a.out/'original').mkdir();shutil.copyfile(a.candidate/'PLAN.json',a.out/'ORIGINAL_PRODUCER_PLAN.json')
    final=original['final_module']+'.lean';clone(a.candidate/final,a.out/'original'/final,a.storage)
    for row in original['modules']:
        if row['file']!=final:clone(a.candidate/row['file'],a.out/row['file'],a.storage)
    for row in original['payloads']:clone(a.candidate/row['file'],a.out/row['file'],a.storage)
    with tempfile.TemporaryDirectory(prefix='.proof-transform-',dir=a.out)as temporary:
        output=Path(temporary)/'assembly';flags=['-O']if sys.flags.optimize==1 else ['-OO']if sys.flags.optimize==2 else []
        command=[sys.executable,*flags,str(PACKAGE/'tools/generate_compact_final_v2.py'),'--stage',str(stage),'--original-final',str(a.candidate/final),'--original-audit',str(PACKAGE/'locked'/f'W4D{stage}ClaimAudit.lean'),'--helper-dir',str(PACKAGE/'helpers'),'--out',str(output)]
        run=subprocess.run(command,capture_output=True,text=True);(a.out/'GENERATOR.stdout').write_text(run.stdout);(a.out/'GENERATOR.stderr').write_text(run.stderr)
        need(run.returncode==0 and not run.stderr,'Pinned source-only generator failed')
        assembly=load(output/'ASSEMBLY.json');need(sha(output/final)==FINAL[stage],'Accepted compact Final source not reproduced')
        for name in [*HELPERS,final]:shutil.copyfile(output/name,a.out/name)
        shutil.copyfile(output/'ASSEMBLY.json',a.out/'PROOF_ASSEMBLY_RECEIPT.json')
    old_headers=header_map(a.out/'original'/final);new_headers=header_map(a.out/final)
    need(old_headers==new_headers and len(old_headers)==stage+7,'Original31/20 public declaration headers changed')
    identities=assembly['declaration_identity'];changed=[r['name'].split('.')[-1]for r in identities if not r['body_byte_identical']]
    need(changed==['top_shape','numerator_checked'],'Unexpected additional public proof body changed')
    proposal=dict(original);modules=[]
    for row in original['modules']:
        if row['file']==final:
            source=a.out/final;modules.append(dict(file=final,imports=imports(source),sha256=sha(source),bytes=source.stat().st_size))
        else:modules.append(row)
    for name,digest in HELPERS.items():
        source=a.out/name;need(sha(source)==digest,'Fixed helper changed');modules.append(dict(file=name,imports=imports(source),sha256=digest,bytes=source.stat().st_size))
    proposal['modules']=modules;proposal['compact_proof_repair']=dict(kind='SOURCE_ONLY_TWO_PROOF_BODIES_SAME_PUBLIC_TYPES',original_plan_sha256=original_plan_sha,generator_sha256=GENERATOR_SHA,transformer_sha256=sha(Path(__file__)),original_namespace_and_final_module_preserved=True,untrusted_proposal_not_proof_not_PV=True,original_plan_file='ORIGINAL_PRODUCER_PLAN.json',source_only_receipt_file='PROOF_TRANSFORM_RECEIPT.json')
    publish(a.out/'PLAN.json',proposal)
    publish(a.out/'PROOF_TRANSFORM_RECEIPT.json',dict(status='PASS_SOURCE_ONLY_TRANSFORM_NOT_PROOF_NOT_PV',original_candidate=str(a.candidate),derived_candidate=str(a.out),original_plan_sha256=original_plan_sha,derived_plan_sha256=sha(a.out/'PLAN.json'),source_generator_sha256=GENERATOR_SHA,transformer_sha256=sha(Path(__file__)),generator_command=command,generator_returncode=run.returncode,generator_stdout_sha256=sha(a.out/'GENERATOR.stdout'),generator_stderr_sha256=sha(a.out/'GENERATOR.stderr'),original_ClaimAudit_sha256=AUDIT[stage],same_public_headers=len(old_headers),changed_public_bodies=changed,public_declaration_identities=identities,original_numeric_sources_unchanged=len(original['modules'])-1,original_payloads_unchanged=len(original['payloads']),added_helpers=list(HELPERS),derived_proposal_modules=len(modules),expected_fresh_kernel_math_modules=122 if stage==13 else 1035,import_probe_excluded_from_candidate=True,checker_owned_audit_not_supplied_as_candidate=True,storage=a.storage,seconds=time.monotonic()-started,mathematical_claims_algorithms_inputs_C_and_parameters_unchanged=True,source_cold_replay_completed=False,source_first_PV_completed=False))
    validate_derived(a.out,a.project_root)
    need(sha(a.candidate/'PLAN.json')==original_plan_sha,'Original producer PLAN changed during transform')
    print('PASS SOURCE ONLY UNTRUSTED COMPACT CANDIDATE',stage,len(modules),flush=True)
if __name__=='__main__':main()
