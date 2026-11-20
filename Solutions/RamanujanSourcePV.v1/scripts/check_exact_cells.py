#!/usr/bin/env python3
"""Independent exact-integer enclosure check of EVERY finite cell.
Uses 96-bit / 24-term log enclosures to challenge the generator's60-bit /20-term
implementation. This Python check is ordinary verification, NOT source-first PV.
"""
import argparse, concurrent.futures, fractions, hashlib, json, os, pathlib, struct, time
F=1<<60;G=1<<96;S=1<<20

def up(a,b):
 if b<=0:raise ValueError('positive denominator')
 return (a+b-1)//b

def independent_log_u(num,den):
 z=up(G*num,den);zz=up(z*z,G);power=z;total=0
 for k in range(24):
  total+=up(power,2*k+1);power=up(power*zz,G)
 return 2*total+up(2*power*G,49*(G-zz))
LOG2=independent_log_u(1,3)

def check_record(args):
 rec,mode,scratch,out=args;start=time.monotonic();os.sched_setaffinity(0,{48+rec['chunk']%8});path=scratch/(str(rec['chunk'])+'.bin')
 h=hashlib.sha256();expected=rec['begin'];cells=0;mingap=None;minwidth=None;maxwidth=0;previousj=0
 elo=F;term=F
 for k in range(1,21):term//=k;elo+=term
 ehi=elo+22
 with path.open('rb') as f:
  while True:
   data=f.read(56*4096)
   if not data:break
   if len(data)%56:raise ValueError('truncated row')
   h.update(data)
   for n,nxt,j,p,q,lu,a in struct.iter_unpack('<7Q',data):
    if n!=expected or not n<nxt<=rec['end_exclusive']:raise ValueError('coverage')
    if j<previousj or j!=n*F//ehi:raise ValueError('pi/e index')
    k=n.bit_length()-1;two=1<<k
    log96=k*LOG2+independent_log_u(n-two,n+two)
    if log96*(1<<40)>lu*G:raise ValueError('independent log upper fails')
    if a!=n*elo//lu:raise ValueError('factor A')
    gap=a*q-S*p*p
    if gap<=0:raise ValueError('strict predicate')
    mingap=gap if mingap is None else min(mingap,gap);width=nxt-n;minwidth=width if minwidth is None else min(minwidth,width);maxwidth=max(maxwidth,width)
    previousj=j;expected=nxt;cells+=1
 if expected!=rec['end_exclusive'] or cells!=rec['numeric_result']['cells'] or h.hexdigest()!=rec['certificate_sha256']:raise ValueError('final endpoint/count/hash')
 result={'chunk':rec['chunk'],'status':'EXACT_INTEGER_CELL_AND_ENCLOSURE_CHECK_PASS','cells':cells,'certificate_sha256':h.hexdigest(),'minimum_integer_gap':mingap,'minimum_width':minwidth,'maximum_width':maxwidth,'wall_seconds':time.monotonic()-start,'source_first_PV':False,'prime_count_values_checked_here':False}
 (out/(str(rec['chunk'])+'.json')).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['chunk','cells','wall_seconds']}),flush=True);return result

def main():
 p=argparse.ArgumentParser();p.add_argument('--study',type=pathlib.Path,required=True);p.add_argument('--scratch',type=pathlib.Path,required=True);p.add_argument('--run',required=True);a=p.parse_args();r=a.study.resolve();scratch=a.scratch.resolve()/a.run;run=json.loads((r/'evidence'/a.run/'RUN.json').read_text())
 if run['status']!='UNTRUSTED_NUMERICAL_GENERATION_COMPLETE':raise ValueError('unfinished run')
 out=r/'evidence'/(a.run+'-exact-enclosures');out.mkdir(exist_ok=False)
 term=fractions.Fraction(1);e=term
 for k in range(1,41):term/=k;e+=term
 upper=e+(term/41)*fractions.Fraction(42,41)
 elo=F;ft=F
 for k in range(1,21):ft//=k;elo+=ft
 if not fractions.Fraction(elo,F)<=e<=upper<=fractions.Fraction(elo+22,F):raise ValueError('independent e enclosure')
 t=time.monotonic()
 with concurrent.futures.ProcessPoolExecutor(max_workers=8) as pool:rs=list(pool.map(check_record,[(rec,run['mode'],scratch,out) for rec in run['records']]))
 result={'status':'ALL_EXACT_CELL_ENCLOSURES_CHECKED','formal_verification':False,'cells':sum(x['cells'] for x in rs),'minimum_integer_gap':min(x['minimum_integer_gap'] for x in rs),'e_lower':elo,'e_upper':elo+22,'wall_seconds':time.monotonic()-t,'records':rs,'script_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()};(out/'RESULT.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:result[k] for k in ['status','cells','wall_seconds']}))
if __name__=='__main__':main()
