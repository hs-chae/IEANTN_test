#!/usr/bin/env python3
"""Second exact replay of the eligible trapezoid cells and whole-ray budgets.

The source/geometry/zero decomposition and continuum argument are separately
reviewed in CUBE_TRAPEZOID_SECOND_REVIEW.json. This is external E arithmetic.
"""
import argparse,ast,hashlib,json,time
from fractions import Fraction as Q
from pathlib import Path
from flint import arb,ctx,fmpq


def need(ok,message):
    if not ok:raise ValueError(message)


class Guards(ast.NodeTransformer):
    def visit_Assert(self,node):
        return ast.copy_location(ast.Expr(ast.Call(ast.Name('need',ast.Load()),
            [self.visit(node.test),ast.Constant('Exact source guard failed at line '+str(node.lineno))],[])),node)


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def A(q):
    q=Q(q);return arb(fmpq(q.numerator,q.denominator))


def lower_decimal(q,digits=14):
    q=Q(q);k=q.numerator*10**digits//q.denominator
    return f'{k//10**digits}.{k%10**digits:0{digits}d}'


def main():
    p=argparse.ArgumentParser(allow_abbrev=False);p.add_argument('--submitted',type=Path,required=True);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    need(not a.out.exists(),'Fresh second-review run required');a.out.mkdir(parents=True);ctx.prec=256;began=time.monotonic()
    source=a.submitted/'sinc_certificate.py'
    need(sha(source)=='c5658936b76c0fbc633bd46d2dab8db97ab8389067871969bf1ee760a57bb270','Eligible scalar source differs')
    tree=ast.fix_missing_locations(Guards().visit(ast.parse(source.read_text())))
    env=dict(__name__='second_review_exact_source',__file__=str(source),need=need)
    exec(compile(tree,str(source),'exec'),env)
    need(A('3.14159')<arb.pi() and arb.pi()<A('3.14160'),'Independent directed pi enclosure failed')
    need(arb(2).log()>A('.69'),'Prime-power exponent bound failed')
    cases=[(32,64,16384,Q('-.37'),Q(8),Q(8),Q('54.598'),2980,Q('.8591'),tuple(map(Q,('2.528','-2.218','2.841','6.562')))),
           (480,96,196608,Q('-.4'),Q('14.58'),Q('14.583039'),Q('1467.798'),2154433,Q('.9855'),tuple(map(Q,('3.635','1.526','4.536','8.611'))))]
    rows=[]
    for K,M,J,offset,lo,hi,sqrt_lower,n_lower,target,caps in cases:
        start=time.monotonic();actual=env['certificate'](K,M,J,offset)
        need(all(x<=y for x,y in zip(actual,caps)),'A/B/variation/log printed cap failed')
        alpha=arb(8).exp() if K==32 else arb(n_lower)
        need(alpha>=A(n_lower) and alpha.sqrt()>A(sqrt_lower),'Actual onset/square-root lower bound failed')
        if K==32:
            need(lo==hi==8,'Exact log(exp8)=8 identity differs')
        else:
            need(alpha.log()>=A(lo) and alpha.log()<=A(hi),'Actual log-onset bracket failed')
        need(A(Q(2*(K+1)*(n_lower+1),3*K*n_lower)).log()<A(offset),'T/n offset bound failed')
        need(A(Q(2*n_lower,3))>2*arb.pi(),'Whole BPT frequency domain failed')
        AA,BB,V,C=caps
        need(AA>0 and V>0 and C>0 and AA*(lo-2)+BB>=0,'Whole-ray derivative sign failed')
        need(Q(1,n_lower*lo)<Q('.001') and Q('1.001')**2*n_lower>=n_lower+1,'Uniform prime-power geometry failed')
        need(Q(3,4)*Q('1.001')**2+Q(1,2)*Q('1.001')/sqrt_lower<2,'Square-prime-power cap failed')
        need(Q(10,3)*Q('1.001')**2<4,'Higher-prime-power cap failed')
        main=Q(K,K+1)*Q(n_lower,n_lower+1)/(1+1/(n_lower*lo))
        zeros=(AA*hi+BB+Q(42,25)*(hi+C)*V/n_lower+Q(21,4*n_lower))/(3*sqrt_lower)
        powers=2*hi/(n_lower*sqrt_lower)+4*hi**2/n_lower**2
        trivial=Q(1,3*n_lower**5);bound=main-zeros-powers-trivial
        need(bound>target,'Independent exact final coefficient failed')
        row=dict(K=K,M=M,J=J,actual_scalar_caps=list(map(str,actual)),used_caps=list(map(str,caps)),
            main_lower=str(main),zero_loss_upper=str(zeros),prime_power_loss_upper=str(powers),trivial_loss_upper=str(trivial),
            exact_coefficient_lower=str(bound),safe_decimal_lower=lower_decimal(bound),target=str(target),seconds=time.monotonic()-start)
        rows.append(row);print('EXACT_FULL_RAY_PASS',K,row['safe_decimal_lower'],flush=True)
    seam=2154433
    need((seam+1)**3<10**19,'Finite/analytic seam left the Buthe domain')
    finite=(A(Q(19,30)+Q(26,25*1920))/arb(1920).sqrt())
    need(finite<A('.0145'),'Independent finite n1920 bridge failed')
    result=dict(status='PASS_SECOND_EXACT_TRAPEZOID_ALL_CELLS_RAY_DOMAINS_AND_FINITE_SEAM',cases=rows,
        finite_bridge_error_enclosure=str(finite),finite_source_domain='1423<=n^3<(n+1)^3<=1e19 on1920<=n<=2154433',
        source_sha256=sha(source),controller_sha256=sha(Path(__file__)),seconds=time.monotonic()-began,
        verification_tier='External exact arithmetic with separately reviewed Green/BPT/Buthe analytic derivation; not Lean or source-first PV.',
        original_source_modified=False,all_source_assertions_replaced_by_explicit_guards=True)
    (a.out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(result['status'],flush=True)


if __name__=='__main__':main()
