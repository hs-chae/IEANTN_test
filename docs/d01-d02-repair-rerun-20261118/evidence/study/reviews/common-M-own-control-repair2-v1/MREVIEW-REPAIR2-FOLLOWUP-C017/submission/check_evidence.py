"""Read exact original table cells, compare independently re-executed certificates."""
from pathlib import Path
from decimal import Decimal as D
from hashlib import sha256
import json, re, sys
A=Path(sys.argv[1] if len(sys.argv)>1 else '/work/exact')
S=Path(__file__).resolve().parent
P=Path('/corpus/originals')
idx=json.loads(Path('/task/CANDIDATE_INDEX.json').read_text())
digest=lambda p:sha256(p.read_bytes()).hexdigest()
for r in idx['candidate_files']:
    assert digest(A/r['original_name'])==r['sha256']==digest(Path('/task')/r['packet_name'])
print('verified restored candidate files',len(idx['candidate_files']))

def base(f):
    return (P/f'{f}.txt').read_text().split('\n')
def num(s):
    return D(s.replace(' · 10','e').replace('−','-').replace(' ',''))
def verify(modes,j,rec):
    t,*v,tag=rec
    src=next(n for n in modes if tag.startswith(n))
    fn, start, stop, offs=modes[src]
    a=base(fn)
    vv=v if len(v)==1 else v[:len(offs)]
    for i in range(start-1,stop):
        try:
            tt=num(a[i])
            if fn=='FKS' and start==2593 and 2728<=i+1<=2743 and (i+1-2728)%5==0:
                tt=D(10)**(int(tt)-100)
            if tt != t: continue
            if [num(a[i+k]) for k in offs]!=list(map(D,vv)): continue
        except ArithmeticError: continue
        print('table row',j,t,tag,fn+'.txt',i+1, [i+k+1 for k in offs])
        return
    raise AssertionError((j,t,v,tag))
tabs=json.loads((A/'source_tables.json').read_text())
for j, rec in enumerate(tabs['steps']):
    verify({'Dusart':('Dusart2018',481,765,[5]),
      'PT':('PlattTrudgian1809.03134v2',142,201,[5]),
      'FKS Thm1.1':('FKS',2317,2570,[6]),
      'FKS Table6':('FKS',2593,2770,[3])},j,rec)
for j, rec in enumerate(tabs['shapes'][:-1]):
    verify({'PT':('PlattTrudgian1809.03134v2',142,201,[2,3,4]),
      'FKS':('FKS',2593,2770,[1])},j,rec)
    assert rec[-2]=='5.573412' if j<10 else rec[2:5]==['1.5','2','5.5666305']
assert tabs['shapes'][-1][:5]==[1,'9.22022','1.5','.8476836','1']
print('FKS Cor 1.4 original LF140–142; generic branch code uses x>2 guard')

pairs={
 'certify':'analytic_run.txt','compact_r':'compact_r_run.txt',
 'endpoint':'endpoint_run.txt','finite_joins':'joins_run.txt',
 'finite_mertens':'finite_run.txt','finite_query-10007':'finite_query_run.txt',
 'finite_zoom':'zoom_run.txt','fixed_x_check':'fixed_x_check_run.txt',
 'power_prefix':'power_prefix_monotone_run.txt','repair_finite':'repair_finite_run.txt',
 'repair_joins':'rejoin_run.txt','repair_portfolio':'repair_portfolio.json',
 'repair_r':'repair_r_full_run.txt','repair_spectral':'repair_spectral_run.txt',
 'root_zoom':'root_zoom_run.txt','second_finite':'second_finite_run.txt',
 'second_m':'second_m_run.txt','second_portfolio':'second_portfolio.json',
 'second_r':'second_r_run.txt','source_audit':'source_run.txt',
 'repair_evaluate-log_200':'current_log_run.txt','repair_evaluate-x_1e70':'fixed_x_run.txt',
 'historical_log':'repair_eval_run.txt'}
for s,t in pairs.items():
    f=S/f'{s}.stdout'
    status=S/f'{s}.status'
    if not status.exists(): print('PENDING',s);continue
    eq=f.read_bytes()==(A/t).read_bytes()
    if s=='repair_evaluate-x_1e70':
        assert (A/t).read_bytes().startswith(f.read_bytes())
        print(s,'matches the x=1e70 prefix of compound receipt',t)
    else:
        assert eq,(s,t)
    assert status.read_text().strip()=='0'
    print(s,'status',status.read_text().strip(),'stdout',digest(f),'stderr',digest(S/f'{s}.stderr'),
          'byte equality with',t, eq)
