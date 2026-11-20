#!/usr/bin/env python3
"""Deterministic untrusted immutable-array checker benchmark proposal."""
from pathlib import Path
import argparse,functools,math,sys
S=Path(__file__).resolve().parents[1]
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--n',type=int,required=True);a=ap.parse_args()
    if not 2<=a.n<=1000000:raise ValueError('first bounded benchmarks through1e6')
    sys.setrecursionlimit(10000);rows=[]
    @functools.lru_cache(None)
    def get(p,v):
        if p==2:row=(p,v,max(v-1,0),0,0,0,0)
        else:
            q=p-1;ia=get(q,v);ib=get(q,q);ic=get(q,q-1);id=get(q,v//q)
            av,bv,cv,dv=(rows[i][2]for i in [ia,ib,ic,id]);value=av if bv==cv or v<q*q else av-(dv-cv)
            if value<0:raise ValueError('negative proposed count')
            row=(p,v,value,ia,ib,ic,id)
        i=len(rows);rows.append(row);return i
    target=get(math.isqrt(a.n)+1,a.n);name=f'QuotientFastBench{a.n}';file=S/'RamanujanPV'/(name+'.lean')
    if file.exists():raise ValueError('fresh proposal')
    literal='#[\n'+',\n'.join('⟨'+','.join(map(str,row))+'⟩'for row in rows)+'\n]'
    file.write_text('/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\nimport RamanujanPV.QuotientFastCheck\nnamespace RamanujanPV.'+name+'\nopen QuotientAlgorithm QuotientFastCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\ndef nodes : Array Node := '+literal+'\ntheorem checked : checkFast nodes=true := by decide +kernel\ntheorem count : Nat.primeCounting '+str(a.n)+'='+str(rows[target][2])+' :=\n  QuotientFastCheck.certificate_pi (i:='+str(target)+') (n:=⟨'+','.join(map(str,rows[target]))+'⟩) checked (by decide +kernel) (by decide)\n#print axioms checked\n#print axioms count\nend RamanujanPV.'+name+'\n')
    print('UNTRUSTED_PROPOSAL',len(rows),'rows',file.stat().st_size,'bytes')
if __name__=='__main__':main()
