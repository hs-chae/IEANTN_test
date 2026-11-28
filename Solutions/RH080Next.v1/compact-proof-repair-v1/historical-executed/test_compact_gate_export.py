#!/usr/bin/env python3
"""Actual all-mode compact gate/export controls on accepted S13; preserve originals."""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
Q=Path(__file__).resolve().parent;OUT=Q/'compact-gate-export-controls-v1';CTX=Path('/data/ivy-rh-one-prime-20261124/clean_proof_context.json')
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    need(not OUT.exists(),'Fresh control directory required');OUT.mkdir();records=[]
    gate=Q/'verify_compact_final.py';exporter=Q/'export_compact_final_bank.py';base=Q/'run-s13-compact-v1';assembly=Q/'s13-compact-v1'
    before={str(p):sha(p)for p in[base/'PLAN.json',base/'RESULT.json',assembly/'ASSEMBLY.json',assembly/'W4D13Final.lean',assembly/'W4D13ClaimAudit.lean']}
    bad_assembly=OUT/'bad-assembly';shutil.copytree(assembly,bad_assembly);j=json.loads((bad_assembly/'ASSEMBLY.json').read_text());j['original_ClaimAudit_sha256']='0'*64;(bad_assembly/'ASSEMBLY.json').write_text(json.dumps(j)+'\n')
    bad_source=OUT/'bad-source';shutil.copytree(assembly,bad_source);f=bad_source/'W4D13Final.lean';f.write_text(f.read_text()+'\n-- source mutation\n')
    missing=OUT/'missing-audit';shutil.copytree(assembly,missing);(missing/'W4D13ClaimAudit.lean').unlink()
    def actual(cmd,label,mode,passed):
        r=subprocess.run(cmd,capture_output=True,text=True);need((r.returncode==0)==passed,'Unexpected actual CLI control '+label)
        records.append(dict(mode=mode,label=label,command=cmd,returncode=r.returncode,expected_success=passed,stdout=r.stdout,stderr=r.stderr))
    for mode,flags in enumerate([[],['-O'],['-OO']]):
        accepted=OUT/f'accepted-{mode}.json';args=['--run',str(base),'--assembly',str(assembly),'--context',str(CTX),'--out',str(accepted),'--toy']
        actual([sys.executable,*flags,str(gate),*args],'gate-positive',mode,True)
        for label,extra in [('stale-acceptance',args),('modified-assembly',['--run',str(base),'--assembly',str(bad_assembly),'--context',str(CTX),'--out',str(OUT/f'bad-assembly-{mode}.json'),'--toy']),('modified-source',['--run',str(base),'--assembly',str(bad_source),'--context',str(CTX),'--out',str(OUT/f'bad-source-{mode}.json'),'--toy']),('missing-audit',['--run',str(base),'--assembly',str(missing),'--context',str(CTX),'--out',str(OUT/f'missing-audit-{mode}.json'),'--toy']),('production-needs-actual-resources',['--run',str(base),'--assembly',str(assembly),'--context',str(CTX),'--out',str(OUT/f'wrong-tier-{mode}.json')]),('unknown-option',[*args,'--unknown-acceptance-flag'])]:
            actual([sys.executable,*flags,str(gate),*extra],label,mode,False)
        export=OUT/f'export-{mode}';exportargs=['--base',str(base),'--assembly',str(assembly),'--context',str(CTX),'--accepted',str(accepted),'--run',str(export),'--toy']
        actual([sys.executable,*flags,str(exporter),*exportargs],'export-positive',mode,True)
        plan=json.loads((export/'PLAN.json').read_text());need(len(plan['source_rows'])==122 and len(plan['per_module_lineage'])==122,'Wrong source/provider count');need(sum(plan['compile_phases'].values())==122,'Wrong phase total');need((export/'diagnostics/W4D13FinalImportsProbe.olean').is_file()and not(export/'objects/W4D13FinalImportsProbe.olean').exists(),'Probe entered math bank')
        for row in plan['source_rows']:
            n=row['module'];obj=export/'objects'/(n.replace('.','/')+'.olean');original=base/'objects'/(n.replace('.','/')+'.olean');need(obj.stat().st_ino==original.stat().st_ino and obj.stat().st_dev==original.stat().st_dev,'Large export artifact copied')
        actual([sys.executable,*flags,str(exporter),*exportargs],'stale-export',mode,False)
        source=json.loads(accepted.read_text())
        for key,value in [('plan_sha256','0'*64),('result_sha256','0'*64),('assembly_sha256','0'*64),('validator_sha256','0'*64),('math_bank_modules',123),('toy_only',False),('actual_resource_evidence',{'forged':'not production'})]:
            forged=dict(source);forged[key]=value;fp=OUT/f'forged-{key}-{mode}.json';fp.write_text(json.dumps(forged)+'\n');cmd=[sys.executable,*flags,str(exporter),'--base',str(base),'--assembly',str(assembly),'--context',str(CTX),'--accepted',str(fp),'--run',str(OUT/f'reject-{key}-{mode}'),'--toy'];actual(cmd,'export-tamper-'+key,mode,False)
        for label,text in [('duplicate-key',accepted.read_text().replace('{','{"status":"bad",',1)),('nonfinite','{"status":NaN}')]:
            fp=OUT/f'{label}-{mode}.json';fp.write_text(text);cmd=[sys.executable,*flags,str(exporter),'--base',str(base),'--assembly',str(assembly),'--context',str(CTX),'--accepted',str(fp),'--run',str(OUT/f'reject-{label}-{mode}'),'--toy'];actual(cmd,'export-strict-json-'+label,mode,False)
    for path,digest in before.items():need(sha(path)==digest,'Accepted original proof/source changed during controls')
    value=dict(status='PASS_ACTUAL_S13_COMPACT_GATE_AND_FORMAT_EXPORT_ALL_MODES',source_pins=[dict(path=str(p),sha256=sha(p))for p in[Path(__file__),gate,exporter]],positive_actual_CLIs=sum(r['expected_success']for r in records),negative_actual_CLIs=sum(not r['expected_success']for r in records),all3exports_have122math_providers=True,import_probe_preserved_only_as_diagnostic=True,all_large_objects_verified_hardlinks=True,original_sources_and_results_unmodified=True,production_N24_resource_route_not_claimed_tested_by_S13=True,records=records)
    fd,tmp=tempfile.mkstemp(prefix='.receipt-',dir=OUT)
    try:
        with os.fdopen(fd,'w')as f:json.dump(value,f,indent=2,allow_nan=False);f.write('\n');f.flush();os.fsync(f.fileno())
        os.link(tmp,OUT/'RESULT.json')
    finally:Path(tmp).unlink()
    print(value['status'],value['positive_actual_CLIs'],value['negative_actual_CLIs'],sha(OUT/'RESULT.json'))
if __name__=='__main__':main()
