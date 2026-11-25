#!/usr/bin/env python3
"""Reviewed FFT/continuum-budget replay with optimization-effective guards.

The frozen submitted files are unchanged. Only selected reviewed functions are
evaluated, with each assert replaced by an explicit exception. This remains
external exact arithmetic plus a written analytic argument, not Lean or PV.
"""
import argparse, ast, hashlib, json, math, sys, time
from fractions import Fraction as Q
from pathlib import Path
from flint import arb, ctx, fmpq


def need(ok, message):
    if not ok: raise ValueError(message)


def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()


class Guards(ast.NodeTransformer):
    def visit_Assert(self, node):
        return ast.copy_location(ast.Expr(ast.Call(ast.Name('need', ast.Load()),
            [self.visit(node.test), ast.Constant('Reviewed source guard failed at line '+str(node.lineno))], [])), node)


def load_reviewed(path, selected=None, extra=None):
    tree=ast.parse(path.read_text())
    if selected is not None:
        tree=ast.Module([n for n in tree.body if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)) and n.name in selected],[])
        need({n.name for n in tree.body}==set(selected),'Reviewed function selection differs')
    tree=ast.fix_missing_locations(Guards().visit(tree))
    env=dict(__name__='reviewed_external_functions',__file__=str(path),need=need,Q=Q,Path=Path,json=json)
    if extra:env.update(extra)
    exec(compile(tree,str(path),'exec'),env)
    return env


def decimal_cap(q,n=14): return Q(-((-q*10**n)//1),10**n)


def A(q):
    q=Q(q);return arb(fmpq(q.numerator,q.denominator))


def main():
    p=argparse.ArgumentParser(allow_abbrev=False)
    for name in ['submitted','certificates','out']:p.add_argument('--'+name,type=Path,required=True)
    a=p.parse_args();need(not a.out.exists(),'Fresh exact replay output required');a.out.mkdir(parents=True)
    ctx.prec=256;began=time.monotonic();original=a.certificates/'certify_integer.py'
    primary=load_reviewed(original)
    pl=Q('3.14159265358979323846264338327950288419716939937510');pu=pl+Q(1,10**50)
    need(A(pl)<arb.pi() and arb.pi()<A(pu),'Directed independent pi enclosure failed')
    functions=['checked_eps','normfft','readwin','lowerlog','exp_pos_partial','margin']
    env=load_reviewed(a.submitted/'window_cert.py',functions,dict(real_dft=primary['real_dft'],UNIT=primary['UNIT'],
        positive_area=primary['positive_area'],PL=pl,PU=pu,capdec=decimal_cap))
    rows=[]
    for label,file,grid,tests in [
      ('Fap',a.certificates/'witness-ap.json',32768,[(Q('.8'),Q(42),Q(174),16),(Q('.85113'),Q(42),None,12),
         (Q('.78'),Q(42),Q(70),16),(Q('.777'),Q(42),Q(65),16),(Q('.74'),Q(42),Q(63),16),(Q('.75'),Q(42),Q(70),16)]),
      ('new_w4',a.submitted/'w4.json',524288,[(Q('.851062'),Q(42),None,1)])]:
        start=time.monotonic();info=env['readwin'](file,grid);print('NORM_COMPLETED',label,flush=True)
        outputs=[]
        for coefficient,left,right,blocks in tests:
            try:
                lower=env['margin'](info,coefficient,left,right,blocks)
                outputs.append(dict(coefficient=str(coefficient),log_domain=[str(left),str(right)if right is not None else None],blocks=blocks,
                    status='PASS_EXACT_POSITIVE_MARGIN_AND_REVIEWED_CONTINUUM_CRITERION',exact_margin_lower=str(lower),margin_decimal=str(A(lower))))
            except (ValueError,ArithmeticError)as error:
                outputs.append(dict(coefficient=str(coefficient),log_domain=[str(left),str(right)if right is not None else None],blocks=blocks,
                    status='REJECTED_THIS_REVIEWED_BUDGET_NOT_A_PRIME_COUNTEREXAMPLE',error=str(error)))
        small=[]
        for coefficient in [Q('.8'),Q('.78'),Q('.777')]:
            margins=[A(coefficient)*A(x).sqrt()*A(x).log()-A(next_prime-x)for x,next_prime in [(4,5),(5,7),(7,11)]]
            need(all(v>0 for v in margins),'Actual strict small-prime cover failed')
            small.append(dict(coefficient=str(coefficient),left_points=[4,5,7],next_primes=[5,7,11],directed_margins=[str(v)for v in margins]))
        need(2/arb(1).exp()<A(Q('.74')),'Finite historical-source gap coefficient comparison failed')
        row=dict(witness=label,input=str(file),input_sha256=sha(file),grid=grid,seconds=time.monotonic()-start,
            exact_geometry_and_norm={k:str(v)for k,v in info.items()},tests=outputs,strict_small_x_cover=small,
            finite_bridge='Literal CMS(1.15), gap<log(p)^2 for11<=p<=4e18; monotonic endpoint and2/e<.74. Analytic lower endpoint e42 overlaps this finite range.')
        (a.out/(label+'.json')).write_text(json.dumps(row,indent=2)+'\n');rows.append(row)
    record=dict(status='COMPLETED_REVIEWED_EXPLICIT_ARITHMETIC_AND_SMALL_COVER_NOT_LEAN_OR_PV',cases=rows,
        controller_sha256=sha(Path(__file__)),submitted_source_sha256=sha(a.submitted/'window_cert.py'),primary_integer_source_sha256=sha(original),
        assertion_policy='Every selected submitted assert and any primary assert evaluated as explicit need/exception; frozen submitted files were not edited.',
        seconds=time.monotonic()-began,python_optimization=sys.flags.optimize,
        scope='These positive arithmetic and continuum-budget guards require the separately reviewed Mellin/zero-count/MV/source hypotheses. No actual native-source correspondence or full Lean proof is claimed.')
    (a.out/'RESULT.json').write_text(json.dumps(record,indent=2)+'\n');print(record['status'],flush=True)


if __name__=='__main__':main()
