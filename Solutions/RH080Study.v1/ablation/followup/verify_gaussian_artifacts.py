#!/usr/bin/env python3
"""Independent exact-input/Sturm/Arb checks of eligible Gaussian artifacts only."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction as Q
import hashlib
import json
import math
from pathlib import Path
import subprocess
import sys
import time


def need(ok, message):
    if not ok: raise ValueError(message)


def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    def pairs(items):
        out = {}
        for key, value in items:
            need(key not in out, 'Duplicate JSON key'); out[key] = value
        return out
    return json.loads(path.read_text(), object_pairs_hook=pairs, parse_float=str,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    for name in ['audit', 'reference', 'python-flint', 'out']:
        p.add_argument('--'+name, type=Path, required=True)
    p.add_argument('--curated-root', type=Path)
    a = p.parse_args(); need(not a.out.exists(), 'Fresh interval run required')
    audit = read(a.audit); need(audit['count'] == 8 and len(audit['trials']) == 8, 'All-eight completed readback required')
    root = Path(__file__).resolve().parents[4]
    generic = root/'Solutions/RH080Study.v1/functional/primal40'
    sys.path.insert(0, str(generic))
    from generate_kernel_cells import laguerre_polynomials, source_polynomials
    cases = [('V0-r0','gaussian_prior.json','monomial','36/11','.83401'),
             ('V0-r0','gaussian_fixed.json','monomial','36/11','1'),
             ('V0-r0','gaussian_reduced.json','monomial','36/11','1'),
             ('V1-r1','gauss-fixed.json','laguerre','36/11','.833946549'),
             ('V0-r1','g24.json','monomial','36/11','.833946826621'),
             ('V1-r0','g25.json','hermite','36/11','.833951'),
             ('V0-r1','g243.json','monomial','2.43036','.8'),
             ('V1-r0','gcrit.json','hermite','2.4304','.8'),
             ('V0-r0','gaussian_reduced.json','monomial','2.43','.8')]
    a.out.mkdir(parents=True); snapshot=a.out/'reference.py'; snapshot.write_bytes(a.reference.read_bytes())
    plans=[]
    for suffix, name, basis, penalty, target in cases:
        trial=next(t for t in audit['trials'] if t['id'].endswith(suffix) and t['task']=='functional')
        matches=[(q,f)for q in trial['timely_prefixes']for f in q['files']if f['file']==name]
        need(matches, 'Eligible numerical artifact absent')
        prefix, association=matches[-1]
        original_path=Path(prefix['path'])/name
        source=(a.curated_root/trial['id']/Path(prefix['path']).name/name
                if a.curated_root is not None else original_path)
        need(sha(source)==association['sha256'], 'Eligible original input differs')
        raw=read(source); data=raw['laguerre'] if basis=='laguerre' else raw
        coefficients=list(map(Q,data)); degree=len(coefficients)-1
        if basis=='laguerre':
            cs=coefficients; need(Q(raw['A'])==Q(penalty), 'Claimed penalty differs')
        elif basis=='hermite':
            cs=[c*((-4)**k)*math.factorial(k)for k,c in enumerate(coefficients)]
        else:
            residual=coefficients.copy(); cs=[Q(0)]*len(coefficients); polynomials=laguerre_polynomials(degree)
            for k in reversed(range(len(cs))):
                cs[k]=residual[k]/polynomials[k][k]
                for j in range(k+1):residual[j]-=cs[k]*polynomials[k][j]
            need(not any(residual), 'Exact monomial basis residual')
        packet=dict(degree=degree,physical_degree=2*degree,coefficients_decimal_exact_rationals=list(map(str,cs)))
        P,G=source_polynomials(packet)
        if basis=='monomial': need(P[::2]==coefficients and not any(P[1::2]), 'Original monomial association differs')
        if basis=='hermite':
            previous=[]; current=[Q(1)]; original=[Q(0)]*len(coefficients)
            for k,c in enumerate(coefficients):
                for j,v in enumerate(current): original[j]+=c*v
                nxt=[Q(0)]*(len(current)+1)
                for j,v in enumerate(current):nxt[j]-=2*(4*k+1)*v;nxt[j+1]+=8*v
                for j,v in enumerate(previous):nxt[j]-=4*(2*k)*(2*k-1)*v
                previous,current=current,nxt
            need(P[::2]==original, 'Original Hermite association differs')
        H=[Q(1)]; independent=[Q(0)]*len(P)
        for n in range(len(P)):
            if n%2==0:
                for j,v in enumerate(H):independent[j]+=(-1)**(n//2)*P[n]*v
            nxt=[Q(0)]*(len(H)+1)
            for j,v in enumerate(H):
                if j:nxt[j-1]+=Q(j,2)*v
                nxt[j+1]-=v
            H=nxt
        need(independent==G, 'Independent monomial Fourier association differs')
        folder=a.out/(suffix+'-'+name.replace('.json','')+'-A'+penalty.replace('/','_'));folder.mkdir()
        candidate=folder/'CANDIDATE.json';candidate.write_text(json.dumps(packet,indent=2)+'\n')
        plans.append(dict(trial=trial['id'],original_input=str(source),recorded_original_input=str(original_path),original_sha256=sha(source),basis=basis,
            physical_degree=2*degree,penalty=penalty,target=target,candidate=str(candidate),candidate_sha256=sha(candidate),folder=str(folder)))
    (a.out/'PLAN.json').write_text(json.dumps(dict(cases=plans,controller_sha256=sha(Path(__file__)),reference_sha256=sha(snapshot),audit_sha256=sha(a.audit),workers=2,per_reference_AS_GiB=64),indent=2)+'\n')
    flags=[] if not sys.flags.optimize else ['-O' if sys.flags.optimize==1 else '-OO']
    def one(row):
        folder=Path(row['folder']); began=time.monotonic()
        command=['prlimit','--as=68719476736','--','/usr/bin/time','-v','-o',str(folder/'GNU_TIME.txt'),str(a.python_flint),*flags,str(snapshot),'--candidate',row['candidate'],'--out',str(folder/'reference'),'--prec','256','--root-digits','45','--A',row['penalty']]
        with (folder/'stdout').open('wb')as out,(folder/'stderr').open('wb')as err:
            result=subprocess.run(command,stdout=out,stderr=err,timeout=240)
        report=dict(**row,command=command,returncode=result.returncode,seconds=time.monotonic()-began,
                    status='REFERENCE_REJECTED_NOT_A_PRIME_CLAIM_COUNTEREXAMPLE')
        if result.returncode==0:
            actual=read(folder/'reference/RESULT.json')
            check='import json,sys;from flint import arb,ctx;ctx.prec=256;d=json.load(open(sys.argv[1]));v=arb(d["enclosures"]["inverse_J"]);t=arb(sys.argv[2]);print(v<t);raise SystemExit(0 if v<t else 1)'
            target=subprocess.run([str(a.python_flint),*flags,'-c',check,str(folder/'reference/RESULT.json'),row['target']],capture_output=True,text=True)
            report.update(status='PASS_INDEPENDENT_EXACT_INPUT_FOURIER_STURM_ARB_TARGET'if target.returncode==0 else 'RIGOROUS_ENCLOSURE_DOES_NOT_ESTABLISH_TARGET',
                enclosures=actual['enclosures'],reference_receipt_sha256=sha(folder/'reference/RESULT.json'),target_comparison_returncode=target.returncode)
        (folder/'CHECK.json').write_text(json.dumps(report,indent=2)+'\n');return report
    with ThreadPoolExecutor(max_workers=2)as pool: results=list(pool.map(one,plans))
    record=dict(status='COMPLETED_ALL_NINE_EXTERNAL_INTERVAL_CHECKS_NOT_LEAN_OR_PV',cases=results,
        controller_sha256=sha(Path(__file__)),reference_sha256=sha(snapshot),original_files_modified=False,
        scope='Independent interval evidence only. Conditional reduced-penalty witnesses do not supply that analytic penalty; no full Lean ANT closure is inferred.')
    (a.out/'RESULT.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(dict(status=record['status'],cases=len(results),passed_targets=sum(r['status'].startswith('PASS_')for r in results))))


if __name__=='__main__':main()
