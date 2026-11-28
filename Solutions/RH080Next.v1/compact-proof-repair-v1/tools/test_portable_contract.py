#!/usr/bin/env python3
"""Actual normal/-O/-OO source-only clean contracts and negative CLI controls."""
import argparse,json,os,shutil,subprocess,sys,time
from pathlib import Path
from compact_contract import PACKAGE,load,sha,need,publish,check_project

def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--project-root',type=Path,default=PACKAGE.parent);ap.add_argument('--original-n24',type=Path,required=True);ap.add_argument('--work',type=Path,required=True);a=ap.parse_args();need(not a.work.exists(),'Fresh portable controls required');project=a.project_root.resolve(strict=True);check_project(project);a.work=a.work.absolute();a.work.mkdir(parents=True);records=[];started=time.monotonic()
    original_input=PACKAGE/'locked/w4-input.json';prepare=PACKAGE/'tools/prepare_clean_compact_candidate.py';derive=PACKAGE/'tools/derive_compact_candidate.py';fresh=PACKAGE/'tools/verify_fresh_compact.py';exporter=PACKAGE/'tools/export_fresh_compact.py'
    def actual(command,label,mode,passed):
        tick=time.monotonic();r=subprocess.run(command,capture_output=True,text=True);need((r.returncode==0)==passed,'Unexpected actual portable control '+label);row=dict(label=label,mode=mode,command=command,returncode=r.returncode,seconds=time.monotonic()-tick,expected_success=passed,stdout=r.stdout,stderr=r.stderr);records.append(row);return row
    # All three modes regenerate the original small numerical data from the original producer.
    positives={}
    for mode,flags in enumerate([[],['-O'],['-OO']]):
        work=a.work/f'clean-s13-{mode}';actual([sys.executable,*flags,str(prepare),'--stage','13','--work',str(work),'--project-root',str(project)],'clean-original-S13-plus-compact-source-contract',mode,True);positives[mode]=work/'compact-candidate'
    # Full N24 source-only preservation: all original1020 sources and937 CSV hashes.
    for mode,flags in enumerate([[],['-O'],['-OO']]):
        target=a.work/f'derived-n24-{mode}';actual([sys.executable,*flags,str(derive),'--candidate',str(a.original_n24.resolve(strict=True)),'--out',str(target),'--project-root',str(project),'--input',str(original_input)],'original-N24-all-source-data-preserving-transform',mode,True)
    fixtures=a.work/'fixtures';fixtures.mkdir();base=a.work/'clean-s13-0/original-candidate'
    cases={}
    def fixture(label):
        path=fixtures/label;shutil.copytree(base,path);cases[label]=path;return path
    path=fixture('same-count-numeric-claim');j=load(path/'PLAN.json');j['norm_numerator']+=1;(path/'PLAN.json').write_text(json.dumps(j)+'\n')
    path=fixture('numeric-source-changed');j=load(path/'PLAN.json');source=path/j['modules'][0]['file'];source.write_text(source.read_text()+'\n-- changed immutable numeric source\n')
    path=fixture('literal-data-changed');j=load(path/'PLAN.json');source=path/j['payloads'][0]['file'];raw=source.read_bytes();source.write_bytes(b'0'+raw[1:])
    path=fixture('extra-numeric-module');j=load(path/'PLAN.json');j['modules'].append(dict(j['modules'][0],file='Unexpected.lean'));(path/'PLAN.json').write_text(json.dumps(j)+'\n')
    path=fixture('wrong-mathematical-stage');j=load(path/'PLAN.json');j['stages']=24;(path/'PLAN.json').write_text(json.dumps(j)+'\n')
    copies={}
    for label in ['same-count-audit-template','helper-proof-changed','locked-original-inventory-changed']:
        root=fixtures/label;shutil.copytree(PACKAGE,root,ignore=shutil.ignore_patterns('__pycache__'));copies[label]=root
    path=copies['same-count-audit-template']/'locked/W4D13ClaimAudit.lean';path.write_text(path.read_text().replace('13560177159173855','13560177159173856'))
    path=copies['helper-proof-changed']/'helpers/NormSymbolic.lean';path.write_text(path.read_text()+'\n-- changed proof identity\n')
    path=copies['locked-original-inventory-changed']/'locked/original-candidate-13.json';j=load(path);j['norm_numerator']+=1;path.write_text(json.dumps(j)+'\n')
    for mode,flags in enumerate([[],['-O'],['-OO']]):
        for label,path in cases.items():
            target=a.work/f'reject-{label}-{mode}';actual([sys.executable,*flags,str(derive),'--candidate',str(path),'--out',str(target),'--project-root',str(project),'--input',str(original_input)],label,mode,False);need(not(target/'PROOF_TRANSFORM_RECEIPT.json').exists(),'Rejected source transform published completion')
        for label,root in copies.items():
            target=a.work/f'reject-{label}-{mode}';actual([sys.executable,*flags,str(root/'tools/derive_compact_candidate.py'),'--candidate',str(base),'--out',str(target),'--project-root',str(project),'--input',str(original_input)],label,mode,False);need(not(target/'PROOF_TRANSFORM_RECEIPT.json').exists(),'Rejected package mutation published completion')
        actual([sys.executable,*flags,str(derive),'--candidate',str(base),'--out',str(positives[mode]),'--project-root',str(project),'--input',str(original_input)],'stale-derived-output',mode,False)
        empty=a.work/f'not-a-proof-{mode}';empty.mkdir();target=a.work/f'must-not-promote-{mode}.json'
        actual([sys.executable,*flags,str(fresh),'--run',str(empty),'--context',str(a.work/'no-context.json'),'--candidate',str(positives[mode]),'--output',str(target),'--project-root',str(project),'--proof-only-toy'],'source-only-contract-cannot-promote-to-fresh-proof',mode,False);need(not target.exists(),'Unverified source-only proposal promoted')
        fake=a.work/f'fake-acceptance-{mode}.json';fake.write_text(json.dumps(dict(status='PASS_INDEPENDENT_FRESH_COMPACT_W4_KERNEL_ONLY_NOT_C_PV',validator_sha256='0'*64,contract_sha256='0'*64))+'\n');context=a.work/f'dummy-context-{mode}.json';context.write_text('{}\n')
        target=a.work/f'must-not-export-{mode}';actual([sys.executable,*flags,str(exporter),'--base',str(empty),'--context',str(context),'--candidate',str(positives[mode]),'--accepted',str(fake),'--run',str(target),'--project-root',str(project),'--toy'],'forged-acceptance-cannot-export',mode,False);need(not target.exists(),'Forged acceptance exported')
    for stage,prefix in[(13,'clean-s13-'),(24,'derived-n24-')]:
        hashes=set()
        for mode in[0,1,2]:
            path=a.work/(prefix+str(mode));path=path/'compact-candidate'if stage==13 else path;hashes.add(sha(path/f'W4D{stage}Final.lean'))
        need(len(hashes)==1,'Source transformation differs under Python optimization')
    value=dict(status='PASS_ACTUAL_PORTABLE_SOURCE_CONTRACT_ALL_MODES',records=records,positive_actual_CLIs=sum(r['expected_success']for r in records),negative_actual_CLIs=sum(not r['expected_success']for r in records),original_n24_937_payloads_and_numeric_expected_hashes_checked_all_modes=True,original_source_helpers_and_audit_templates_pinned=True,three_regenerated_small_original_proposals=True,full_fresh_N24_or681_replay_claimed=False,source_only_not_PV=True,seconds=time.monotonic()-started,source_pins=[dict(path=str(p),sha256=sha(p))for p in[Path(__file__),prepare,derive,PACKAGE/'tools/compact_contract.py',fresh,exporter]])
    publish(a.work/'RESULT.json',value);print(value['status'],value['positive_actual_CLIs'],value['negative_actual_CLIs'],flush=True)
if __name__=='__main__':main()
