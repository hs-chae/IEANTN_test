#!/usr/bin/env python3
"""Fresh global-chord Fap computation plus the other recorded explicit profiles."""
import argparse,hashlib,importlib.util,json,math,os,re,subprocess,sys,time
from fractions import Fraction as Q
from pathlib import Path
sys.set_int_max_str_digits(1000000)


def need(ok,message):
    if not ok:raise ValueError(message)


def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--run',type=Path,required=True);a=ap.parse_args()
    need(not os.path.lexists(a.run),'fresh profile replay');a.run.mkdir(parents=True);here=Path(__file__).resolve().parent
    source=here/'review_global_chord.py';fft=here/'inputs/certify_integer.py';witness=here/'inputs/witness-ap.json'
    command=['/usr/bin/time','-v','-o',str(a.run/'norm.time'),'prlimit','--as='+str(64*2**30),'--',sys.executable,'-B',str(source),
        '--fft-source',str(fft),'--witness',str(witness),'--run',str(a.run/'numeric'),'--grid','524288','--mode','slab']
    began=time.monotonic()
    with(a.run/'norm.stdout').open('wb')as out,(a.run/'norm.stderr').open('wb')as err:
        p=subprocess.run(command,stdout=out,stderr=err,env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
    need(p.returncode==0,'fresh norm failed')
    d=json.loads((a.run/'numeric/RESULT.json').read_text())
    need(d['controller_sha256']==sha(source)and d['witness_sha256']==sha(witness),'fresh norm source/input association')
    s={k:Q(v['exact'])for k,v in d['scalars'].items()};U,F0,J,H,M,R,A0,V0,V1,D,L=[s[k]for k in ['U','F0','J','H','M','R','A0','V0','V1','D','signed_log_moment']]
    spec=importlib.util.spec_from_file_location('reviewed_applicability_helpers',here/'review_applicability.py');helpers=importlib.util.module_from_spec(spec);spec.loader.exec_module(helpers)
    log=helpers.log_bounds;ep=helpers.ep;E21=ep(Q(21),70);dm=Q(1,50000000);z=42/E21
    need(0<U<=2 and 0<D<=2 and R<=10 and A0<=2 and V0<=10 and V1<=50 and M<=2,'common scalar caps')
    # Universal remaining-error bound for every .74<=c<=1, using 3<pi<4.
    g1=(R*V1+2*V0)/6;cut=10*dm/6
    zeros=dm*(Q(3,10)*g1+12*(8*R*A0+g1));lowcut=2*A0*cut*(1-log(cut)[0])
    powers=M*(42+11*dm)**2/(2*log(Q(2))[0]*E21*(1-5*dm))*(1+R*42/(2*(1-6*dm)))
    pole=A0*21*(R*dm/2)**2/(1-R*dm/2);ymin=E21**2/2;trivial=dm*A0/((E21/2)*(ymin*ymin-1))
    errors=zeros+lowcut+powers+pole+trivial+2*Q(42**2,4)/E21+2*z/(2-z)
    need(errors<Q('.0012'),'common complete error budget')
    need(ep(Q(1),10)>2/Q('.74'),'historical bridge2/e<.74')
    eupper=ep(Q(1),10)+Q(1,math.factorial(11))/(1-Q(1,12))
    need(eupper<Q(11,4)and Q(11,4)**42<4*10**18,'analytic/finite overlap')
    rows=[];B=Q('4.00001')
    for cs,right,k,xmin,original in [('.78',70,16,4,'strict'),('.777',65,16,4,'strict'),('.74',63,16,11,'half-open'),('.75',70,16,11,'half-open'),('.85113',None,12,4,'half-open-or-strict-depending-on-source-prefix'),('.8',114,16,4,'strict')]:
        c=Q(cs);lk=log(Q(k))[1];q0=1-2*lk/42;need(q0>0,'positive block denominator')
        K=B*J*c*lk/q0+2*B*H/(k*q0)+L+Q('.0012')
        endpoints=[42,right]if right is not None else[42]
        margins={str(t):(c*D-U)*t/2+U*log(c*t/2)[0]-K for t in endpoints}
        low=min(margins.values());need(low>0,'profile endpoint margin')
        if right is None:need(c*D>=U,'profile ray monotonicity')
        count=low*E21/(M*(right if right is not None else 42));need(count>1,'strict upper endpoint upgrade')
        small=[]
        if xmin==4:
            for x,p in [(4,5),(5,7),(7,11)]:
                root=Q(math.isqrt(x*10**30),10**15);need(root*root<=x,'integer sqrt lower bound')
                gain=c*root*log(Q(x))[0]-(p-x);need(gain>0,'claimed small-x bridge')
                small.append(dict(x=x,next_prime=p,margin_exact=str(gain),margin_approx=float(gain)))
        rows.append(dict(coefficient=str(c),minimum_x=xmin,log_analytic_domain=[42,right],blocks=k,
            original_endpoint_convention=original,independent_strict_endpoint_conclusion=True,
            endpoint_margin_lowers={t:dict(exact=str(v),approx=float(v))for t,v in margins.items()},
            strict_half_open_count_lower=dict(exact=str(count),approx=float(count)),leading_margin_exact=str(c*D-U),small_x=small))
    times=(a.run/'norm.time').read_text();rss=re.search(r'Maximum resident set size \(kbytes\):\s*(\d+)',times);need(rss is not None,'RAM metric')
    result=dict(status='PASS_INDEPENDENT_GLOBAL_CHORD_FULL_RECORDED_FAP_PROFILE_TABLE',seconds=time.monotonic()-began,
        norm_grid=524288,norm_upper_exact=str(U),norm_upper_approx=float(U),common_error_upper_exact=str(errors),common_error_upper_approx=float(errors),
        command=command,maximum_numeric_rss_kib=int(rss.group(1)),numeric_receipt_sha256=sha(a.run/'numeric/RESULT.json'),
        source_hashes={n:sha(here/n)for n in ['review_profiles.py','review_global_chord.py','review_applicability.py','inputs/certify_integer.py','inputs/witness-ap.json']},
        rows=rows,source_first_PV=False,Lean_completed=False,network_promoted=False,
        scope='Independent written/source-conditional results, no original claim/outcome rewrite. Strict upgrade of originally half-open profiles is supplemental posthoc review.',
        finite_input='CMS(1.15), historical finite-gap computation, not regenerated here. .74/.75 begin at11; they do not claim coverage of x=7.')
    temp=a.run/'RESULT.json.tmp';temp.write_text(json.dumps(result,indent=2)+'\n');os.link(temp,a.run/'RESULT.json');temp.unlink()
    print(json.dumps(dict(status=result['status'],seconds=result['seconds'],rows=[dict(c=r['coefficient'],right=r['log_analytic_domain'][1],xmin=r['minimum_x'],margin=min(v['approx']for v in r['endpoint_margin_lowers'].values()))for r in rows])))

if __name__=='__main__':main()
