"""Replay new work with the pinned generic and authorized application object bank.

Usage: /usr/bin/python3.10 -B reproduce.py /work/fresh_replay
The directory must not exist. No network access and no official Comparator claim.
"""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time

root=Path(__file__).resolve().parent
out=Path(sys.argv[1]).resolve()
if out==root or root in out.parents:
    raise ValueError('choose a separate output directory')
out.mkdir(parents=True,exist_ok=False)
mnt=json.loads(Path('/task/RUNTIME_PATHS.json').read_text())
env=os.environ.copy()
env['LEAN_PATH']=':'.join([str(out)]+[p for p in mnt['lean_path'] if p!='/work'])
env['PYTHONDONTWRITEBYTECODE']='1'
python='/usr/bin/python3.10'
lean='/opt/lean/bin/lean'

base=Path('/application-cache/IEANTN')
for p in base.rglob('*'):
    if p.is_file():
        q=out/'IEANTN'/p.relative_to(base)
        q.parent.mkdir(parents=True,exist_ok=True)
        q.symlink_to(p)

log=[]
def run(label, cmd):
    start=time.monotonic()
    with (out/(label+'.log')).open('w') as f:
        rc=subprocess.run(cmd,env=env,cwd=root,stdout=f,stderr=subprocess.STDOUT).returncode
    row={'label':label,'status':rc,'seconds':time.monotonic()-start}
    log.append(row)
    (out/'result.json').write_text(json.dumps(log,indent=2)+'\n')
    print(row,flush=True)
    if rc: raise RuntimeError(f'{label} failed')

def build(module, path=None, dep=False):
    p=Path(path) if path else root/(module+'.lean')
    if dep: run(module+'_deps',[python,'-B',str(root/'build_deps.py'),str(p)])
    run(module,[lean,'--root='+str(p.parent),'-o',str(out/(module+'.olean')),str(p)])
    lines=(out/(module+'.log')).read_text()
    if 'depends on axioms' in lines and ('sorryAx' in lines or 'native_decide' in lines):
        raise RuntimeError(f'{module}: unexpected axiom output')

build('SharedRH')
build('FullRH',dep=True)
build('OriginalPrimeInterval','/ieantn/Solutions/PrimeInterval.v1/Solution.lean',dep=True)
build('Intervals',dep=True)
build('Section9Cor13','/ieantn/Solutions/CH2.v1/Section9Cor13.lean',dep=True)
build('PNTFormal')
build('PNTScalar')
run('generate_loose',[python,'-B',str(root/'generate_loose.py'),str(out/'loose')])
for m in ['Loose7','Loose9','LooseLimit']:
    if (out/'loose'/(m+'.lean')).read_bytes() != (root/(m+'.lean')).read_bytes():
        raise RuntimeError(f'{m}: generated source differs')
    build(m,out/'loose'/(m+'.lean'))
build('LooseLowSum')
build('PNTReduced')
build('ClosedCH2Compat')
build('ClosedZeta','/ieantn/Solutions/ZetaLogDeriv.v1/Solution.lean')
build('PNTClosed')
build('NetworkReuse')
build('RamAlgebra',dep=True)
build('CoefficientPV')
build('GapFromSource')
build('FiniteClip')
build('RealCrossing')
build('CrossingBracket')
build('TableCompare')
build('ThetaSigned')
build('WeightedConsumer')
for m in ['ram_cert','refined_ram','crossing_cert','analytic_scalars','prefix_reduction','johnston_tail']:
    run(m,[python,'-B',str(root/(m+'.py'))])
run('gcc',['/usr/bin/gcc','-std=c11','-O2',str(root/'rh_coeff.c'),str(root/'CoefficientHarness.c'),
  '-o',str(out/'coefficient_native')])
run('coefficient_native',[str(out/'coefficient_native')])
print('Replayed all selected targets. Analytic paper proofs and primary literature inputs are separate.')
