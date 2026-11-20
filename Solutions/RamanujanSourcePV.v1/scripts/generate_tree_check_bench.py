#!/usr/bin/env python3
"""Reproducible untrusted RArray certificate proposal; acceptance is Lean-only."""
from pathlib import Path
import argparse,functools,math,sys,hashlib,json,struct
S=Path(__file__).resolve().parents[1]
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--n',type=int,required=True);a=ap.parse_args()
    if not 2<=a.n<=1000000:raise ValueError('bounded first benchmark through1e6')
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
    target=get(math.isqrt(a.n)+1,a.n);name=f'QuotientTreeBench{a.n}';file=S/'RamanujanPV'/(name+'.lean')
    if file.exists():raise ValueError('fresh proposal')
    def tree(lo,hi):
        if hi-lo==1:return '(.leaf ⟨'+','.join(map(str,rows[lo]))+'⟩)'
        mid=(lo+hi)//2
        return f'(.branch {mid} '+tree(lo,mid)+' '+tree(mid,hi)+')'
    literal=tree(0,len(rows));root='⟨'+','.join(map(str,rows[target]))+'⟩'
    source='/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\nimport RamanujanPV.QuotientTreeCheck\nnamespace RamanujanPV.'+name+'\nopen QuotientAlgorithm QuotientTreeCheck\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\ndef nodes : Lean.RArray Node := '+literal+'\ntheorem checked : checkFrom nodes 0 '+str(len(rows))+'=true := by decide +kernel\ntheorem root_eq : nodes.get '+str(target)+'='+root+' := by decide +kernel\ntheorem count : Nat.primeCounting '+str(a.n)+'='+str(rows[target][2])+' := by\n  have h := QuotientTreeCheck.certificate_pi (count:='+str(len(rows))+') (i:='+str(target)+') checked (by decide) (by simpa only [root_eq] using (show ('+str(a.n)+':Nat)<'+str(rows[target][0])+'*'+str(rows[target][0])+' by decide))\n  simpa only [root_eq] using h\n#print axioms checked\n#print axioms count\nend RamanujanPV.'+name+'\n'
    file.write_text(source);raw=b''.join(struct.pack('<7Q',*row)for row in rows)
    print(json.dumps({'status':'UNTRUSTED_TREE_PROPOSAL_NOT_ACCEPTANCE','N':a.n,'records':len(rows),'record_sha256':hashlib.sha256(raw).hexdigest(),'source_bytes':len(source.encode()),'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'generator_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()},indent=2))
if __name__=='__main__':main()
