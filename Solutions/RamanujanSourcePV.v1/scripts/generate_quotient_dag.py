#!/usr/bin/env python3
"""Deterministic untrusted DAG proposer. Acceptance is a separate Lean proof."""
from pathlib import Path
import argparse,functools,hashlib,json,math,struct,sys
S=Path(__file__).resolve().parents[1]
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument("--n",type=int,required=True);ap.add_argument("--mode",choices=["array","proof"],default="array");a=ap.parse_args()
    need(2<=a.n<=1000000,"first bounded DAG benchmark through1e6")
    sys.setrecursionlimit(10000);rows=[]
    @functools.lru_cache(None)
    def get(p,v):
        if p==2:row=(p,v,max(v-1,0),0,0,0,0)
        else:
            q=p-1;ia=get(q,v);ib=get(q,q);ic=get(q,q-1);id=get(q,v//q)
            av,bv,cv,dv=(rows[i][2]for i in [ia,ib,ic,id]);value=av if bv==cv or v<q*q else av-(dv-cv)
            need(value>=0,"nonnegative exact count");row=(p,v,value,ia,ib,ic,id)
        i=len(rows);rows.append(row);return i
    target=get(math.isqrt(a.n)+1,a.n);name=f"QuotientBench{a.n}" if a.mode=="array" else f"QuotientProofBench{a.n}";module=S/"RamanujanPV"/(name+".lean")
    need(not module.exists(),"fresh exact benchmark source")
    terms=["⟨"+",".join(map(str,row))+"⟩"for row in rows]
    module.write_text("/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\nimport RamanujanPV.QuotientAlgorithm\nimport RamanujanPV.CheckerExecution\nnamespace RamanujanPV."+name+"\nopen QuotientAlgorithm\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\ndef nodes : List Node := ["+",\n".join(terms)+"]\ndef final : Array Node := nodes.toArray\ntheorem checked : checkAll #[] nodes=some final := by decide +kernel\ntheorem count : Nat.primeCounting "+str(a.n)+"="+str(rows[target][2])+" := by\n  exact certificate_pi (i:="+str(target)+") (n:=⟨"+",".join(map(str,rows[target]))+"⟩) checked (by decide +kernel) (by decide)\ntheorem source_run (heap : AST.C.Heap) :\n    ∃t, AST.C.Run AST.C.service (AST.C.stmt Source.countFunction.body)\n      (AST.C.countInput "+str(a.n)+" heap) (.returned t "+str(rows[target][2])+") ∧t.heap=heap := by\n  have run := (AST.C.source_count_is_primeCounting "+str(a.n)+" (by decide) heap).2.1\n  simpa only [count] using run\n#print axioms checked\n#print axioms count\n#print axioms source_run\nend RamanujanPV."+name+"\n")
    if a.mode=="proof":
        text="/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\nimport RamanujanPV.QuotientAlgorithm\nimport RamanujanPV.CheckerExecution\nnamespace RamanujanPV."+name+"\nopen QuotientSieve QuotientAlgorithm\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n"
        for i,(p,v,value,ia,ib,ic,id)in enumerate(rows):
            text+=f"theorem node_{i} : total {p} {v}={value} := "
            if p==2:text+=f"by simpa using total_initial {v}\n"
            else:text+=f"local_step (p:={p-1}) (v:={v}) (y:={value}) (by decide) node_{ia} node_{ib} node_{ic} node_{id} (by decide +kernel)\n"
        text+=f"theorem count : Nat.primeCounting {a.n}={rows[target][2]} := by\n  have h := node_{target}\n  rw [total_final (by decide)] at h\n  exact h\n#print axioms count\nend RamanujanPV.{name}\n"
        module.write_text(text)
    out=Path("/data/ivy-ramanujan-source-pv-20261119")/("quotient-proposal-"+a.mode+"-"+str(a.n));out.mkdir(exist_ok=False)
    with(out/"nodes.u64le").open("wb")as f:
        for row in rows:f.write(struct.pack("<7Q",*row))
    receipt={"status":"UNTRUSTED_DAG_PROPOSAL_NOT_PROOF","N":a.n,"target_index":target,"target_count":rows[target][2],"nodes":len(rows),"module":str(module),"module_sha256":sha(module),"data_sha256":sha(out/"nodes.u64le"),"data_bytes":(out/"nodes.u64le").stat().st_size,"generator_sha256":sha(__file__),"random_seed":None}
    (out/"PROPOSAL.json").write_text(json.dumps(receipt,indent=2)+"\n");print(json.dumps(receipt,indent=2))
if __name__=="__main__":main()
