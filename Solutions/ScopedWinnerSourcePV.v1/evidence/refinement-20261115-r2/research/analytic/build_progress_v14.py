"""Revalidate saved source/proof identities and freeze the additive 300-ray index."""
from pathlib import Path
import argparse,hashlib,json,os,re
B=Path(__file__).resolve().parent;R=B.parents[1]
STD3={'propext','Classical.choice','Quot.sound'}
def need(value,message):
    if not value:raise ValueError(message)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def load(path):
    def unique(pairs):
        d={}
        for k,v in pairs:
            if k in d:raise ValueError('duplicate JSON key '+k)
            d[k]=v
        return d
    return json.loads(path.read_text(),object_pairs_hook=unique)
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path);args=ap.parse_args()
    previous=B/'RESUME_ACTUAL_SOURCE_PROGRESS_V13.json';old=load(previous)
    need(old['component_count']==59 and old['root_count']==182,'pinned prior population')
    components=old['components'].copy()
    attempts=['count-boundary100-root-v1','count-cell-ordinate100-root-v1',
      'backward-height-contraction-root-v1','spectral-base300-root-v1',
      'height-budget300-root-v1','height-raw-spectral300-root-v1',
      'direct-psi-source-root-v1','height-pi-psi300-root-v1',
      'pure-kernel-pi-psi300-v2','main-pi-psi300-read-v1','main-pi-psi300-program-v1']
    for attempt in attempts:
        w=B/'work'/attempt;p=w/'RECEIPT.json';d=load(p)
        need(d['status']=='PASS_SELECTED_CONSUMERS_FULL_STD3_CLOSURES' and d['exit_code']==0 and d['source_unchanged'],'accepted strict receipt '+attempt)
        source=Path(d['command'][-3]);module=str(source.relative_to(B/'lean').with_suffix('')).replace('/','.')
        need(d['roots']==list(d['audits']),'exact requested roots '+module)
        components.append(dict(module=module,source=str(source.relative_to(R)),source_sha256=d['source_sha256'],
          receipt=str(p.relative_to(R)),receipt_sha256=sha(p),seconds=d['seconds'],object_sha256=d['object_sha256'],
          roots=[dict(name=n,axioms=a) for n,a in d['audits'].items()],tier='Strict warm source/kernel composition; final clean namespace replay separate.'))
    for row in components:
        source=R/row['source'];p=R/row['receipt'];d=load(p);w=p.parent
        need(sha(source)==sha(w/'source.lean')==row['source_sha256']==d['source_sha256'],'unchanged current/snapshot '+row['module'])
        need(sha(p)==row['receipt_sha256'] and d['exit_code']==0 and d['source_unchanged'],'accepted receipt '+row['module'])
        need(sha(w/'module.olean')==row['object_sha256']==d['object_sha256'],'accepted object '+row['module'])
        if 'bank' in d:
            published=Path(d['bank'])/Path(row['module'].replace('.','/')).with_suffix('.olean')
            need(sha(published)==row['object_sha256'],'published object '+row['module'])
        outputs=[q for q in (w/'stdout',w/'stdout.txt') if q.exists()]
        need(len(outputs)==1,'one actual compiler stdout '+row['module'])
        printed=dict((n,[x.strip() for x in a.split(',') if x.strip()]) for n,a in re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",outputs[0].read_text()))
        for root in row['roots']:
            need(root['name'] in printed and printed[root['name']]==root['axioms'] and set(root['axioms'])<=STD3,'actual full printed root '+root['name'])
    need(len(components)==70 and len({r['module'] for r in components})==70,'all 70 written modules without collapse')
    need(sum(len(r['roots']) for r in components)==202,'all 202 roots')
    result=dict(status='ACCEPTED_WARM_SOURCE_OBSERVED_PI_AND_DIRECT_PSI_FROM300_PLUS_RATIONAL_AND_CONTINUOUS_PRIME_RICH',
      previous_index=str(previous.relative_to(R)),previous_index_sha256=sha(previous),components=components,
      component_count=70,root_count=202,
      final_source_root='SynergyHeightC.MainPiPsi300Program.main_observed_pi_psi_300',
      rational_source_root='SynergyHeightC.MainRationalProgram.main_observed_rational_profile',
      continuous_source_root='SynergyHeightC.MainPrimeRichFunctionProgram.main_observed_prime_rich_function',
      mathematics='Same current fourteen expanded analytic inputs. Both normalized errors <=0.009354674*x^(-1/8) for all x>=exp300; direct psi source proof, unchanged numerical workload at330.',
      source_receipt='research/earlier-onset-v1/SOURCE_RECEIPT.json',
      fresh_kernel_comparator='research/analytic/PURE_KERNEL473_FRESH_ACCEPTANCE_V1.json',
      source_cold_300_acceptance=False,clean_source_namespace_acceptance=False,
      legacy_scope='Original public CH2.v6 challenge preserves fifteen inputs; implementation uses thirteen and then retains FKS density, finite RH and QRH. Its all12-row theorem differs from the current fourteen-input result.',
      historical_outcomes_changed=False,derivation_subsection_changed=False,
      limitations=['This index validates saved warm source/proof evidence, not full fresh or namespace-isolated source300 acceptance.',
        'Fresh kernel-only473/60 comparison is strengthened posthoc using campaign-generated numerical evidence, not original P0; no PV coefficient necessity.',
        'Constructed normal successful-stdio scenario, pinned compiler/runtime/ABI/Cstdio/OS/hardware contracts remain explicit.',
        'Final128 actual bytes separately Lean-compared; full98432byte hash retained, no separate comparison of every actual row claimed.',
        'Separate original Scoped Winner8192/16384 migration and changed-kernel leads remain outside this completion.'])
    out=args.out.resolve() if args.out else B/'RESUME_ACTUAL_SOURCE_PROGRESS_V14.json'
    need(out.is_relative_to(R) and not out.exists(),'fresh owned output')
    out.parent.mkdir(parents=True,exist_ok=True);tmp=out.with_suffix('.pending')
    need(not tmp.exists(),'fresh atomic temporary');tmp.write_text(json.dumps(result,indent=2)+'\n');os.replace(tmp,out)
    print(json.dumps(dict(status=result['status'],components=70,roots=202)))
if __name__=='__main__':main()
