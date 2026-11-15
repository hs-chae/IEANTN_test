"""Read-only reassociation of existing legacy density evidence. No fresh Lean replay."""
from pathlib import Path
import argparse,hashlib,json,re,os
B=Path(__file__).resolve().parent;R=B.parents[2]
def need(x,m):
    if not x:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p):
    def unique(pairs):
        d={}
        for k,v in pairs:
            need(k not in d,'duplicate JSON key '+k);d[k]=v
        return d
    return json.loads(p.read_text(),object_pairs_hook=unique)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);a=ap.parse_args();out=a.out.resolve()
    need(out.is_relative_to(R) and not out.exists(),'fresh owned output')
    for row in load(B/'EVIDENCE_LOCK.json')['files']:
        p=B/row['path'];need(p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],'pinned original evidence '+row['path'])
    sourceRows=load(B/'evidence/LEGACY525_SOURCE_MANIFEST.json')['files']
    need(len(sourceRows)==525 and len({r['path'] for r in sourceRows})==525,'all 525 original file identities')
    for row in sourceRows:need(sha(R/'network'/row['path'])==row['sha256'],'current matches original publication source '+row['path'])
    process=load(B/'evidence/verify-CH2.v6-process.json');log=B/'evidence/verify-CH2.v6.log'
    need(process['status']=='PASS' and process['exit_code']==0 and process['node']=='CH2.v6','actual legacy completion')
    need(sha(log)==process['log_sha256']=='fbe5ed353c33f503be862c24d5e402d8987b6caa1231c1cb824cdb7ac9a1e856','full original verifier log')
    text=log.read_text()
    for marker in ['nanoda kernel accepts the solution','Lean default kernel accepts the solution','comparator accepted Solutions/CH2.v6']:
        need(marker in text,'actual completed marker '+marker)
    audits=dict((n,[s.strip() for s in values.split(',') if s.strip()]) for n,values in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text))
    selected=['CH2QRH.densityFrontier_certified','CH2QRH.density_transfer_proved','CH2.v6.challenge_density_transfer']
    standard={'propext','Classical.choice','Quot.sound'}
    for n in selected:need(n in audits and set(audits[n])==standard,'complete legacy printed closure '+n)
    stages=load(B/'evidence/density-final-stages.json');contract=next(x for x in stages['jobs'] if x['label']=='density-contract-check')
    need(contract['exit_code']==0 and sha(B/'evidence/density-contract-check.log')==contract['log_sha256'],'exact old contract check log')
    contractText=(B/'evidence/density-contract-check.log').read_text()
    need("'exact_density_transfer_contract' depends on axioms: [propext, Classical.choice, Quot.sound]" in contractText,'actual exact-contract closure')
    old=(R/'network/Solutions/CH2.v6/DensitySolution.lean').read_text();segment=old.split('theorem CH2.v6.challenge_density_transfer',1)[1].split(':\n    CH2.v6.density_transfer',1)[0]
    preserved=re.findall(r'\((\w+) : ([^\n]+)\)',segment)
    need(len(preserved)==15,'fifteen original public binders')
    usedText=(R/'network/Solutions/CH2.v6/DensityCertificates.lean').read_text().split('theorem density_transfer_proved',1)[1].split(': CH2.v6.density_transfer',1)[0]
    used=re.findall(r'\((\w+) : ([^\)]+)\)',usedText);need(len(used)==13,'thirteen implementation inputs')
    primary=(R/'scoped/kernel-overlay51-v1/lean/WinnerDensityA/HeightPrimary.lean').read_text().split('structure PrimaryInputs',1)[1].split('theorem selected_lower_contour_param',1)[0]
    primaryFields=re.findall(r'^  (\w+) :',primary,re.M);need(len(primaryFields)==8,'eight current primary source fields')
    currentAdditional=['OriginalCHJSource','ZeroCount.v1.rvm_error_bound','ZeroCount.v1.rvm_error_small','LowZeroes.v1.no_zeroes_below_first_ordinate','RiemannHypothesisUpTo (3*10^12)','ZetaZeroFreeHalfPlane (7/8)']
    receiptPaths=sorted(p.name for p in (R/'network/receipts').glob('CH2.v6*.json'))
    need(not receiptPaths,'do not silently upgrade official receipt status')
    result=dict(status='PASS_REASSOCIATED_EXISTING_COMPLETE_LEGACY_DENSITY_KERNEL_EVIDENCE',
      evidence_lock_sha256=sha(B/'EVIDENCE_LOCK.json'),legacy_verifier_sha256=sha(log),
      legacy_seconds=process['seconds'],source_files_exactly_matching_contemporaneous_manifest=525,
      legacy_selected_complete_axiom_closures={n:audits[n] for n in selected},
      preserved_public_upstream_inputs=[dict(name=n,type=t) for n,t in preserved],
      used_implementation_upstream_inputs=[dict(name=n,type=t) for n,t in used],
      density_conclusion_additional_inputs=['FKS.v3.density_0618','RiemannHypothesisUpTo (3*10^12)','ZetaZeroFreeHalfPlane (7/8)'],
      current_primary_eight_fields=primaryFields,current_six_additional_inputs=currentAdditional,
      current_expanded_inputs=14,
      exact_legacy_contract='Fifteen upstream inputs preserved; thirteen used internally. Density conclusion then retains FKS, finite RH and QRH, and controls all twelve frontier rows.',
      current_contract='Current14 inputs include the eight different primary mollifier/density source relations and OriginalCHJSource. New pi/psi300 result is not a replacement proof of the old different-input/all12-row contract.',
      new_Lean_replay_performed=False,source_first_PV=False,official_registry_receipt_present=False,
      qualifications=['Historical local full comparator/kernel acceptance, not new source-first PV or official maintainer workflow receipt.',
        'No primary-paper source-completeness claim; this is an exact Lean contract and existing-evidence audit.',
        'Generated Challenge stubs were not used as proof-status evidence.'])
    out.parent.mkdir(parents=True,exist_ok=True);temp=out.with_suffix('.pending');need(not temp.exists(),'fresh atomic temporary');temp.write_text(json.dumps(result,indent=2)+'\n');os.replace(temp,out)
    print(result['status'])
if __name__=='__main__':main()
