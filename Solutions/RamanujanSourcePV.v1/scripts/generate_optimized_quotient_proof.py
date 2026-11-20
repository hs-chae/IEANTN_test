#!/usr/bin/env python3
"""Untrusted deterministic proposal for opaque Lucy quotient proofs.
Every composite gap, arithmetic update and final exact pi claim is Lean checked.
No claim is made that this Python proposer or optimized C source was verified.
"""
from pathlib import Path
import argparse,hashlib,json,math,time
S=Path(__file__).resolve().parents[1]
def need(v,m):
    if not v:raise ValueError(m)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument("--n",type=int,required=True);ap.add_argument("--aggregate",action="store_true");ap.add_argument("--explicit",action="store_true");ap.add_argument("--rfl",action="store_true");a=ap.parse_args()
    need(2<=a.n<=1000000,"bounded first optimized benchmark through1e6")
    start=time.monotonic();root=math.isqrt(a.n);spf=list(range(root+1));primes=[]
    for d in range(2,root+1):
        if spf[d]==d:
            primes.append(d)
            for k in range(d*d,root+1,d):
                if spf[k]==k:spf[k]=d
    values=sorted(set(range(1,root+1))|{a.n//i for i in range(1,root+1)})
    states={v:[max(v-1,0),f"(total_initial {v})",False]for v in values}
    name=("QuotientExplicit" if a.explicit else "QuotientAggregate" if a.aggregate else "QuotientOptimized")+("Rfl"if a.rfl else "")+str(a.n);module=S/"RamanujanPV"/(name+".lean");need(not module.exists(),"fresh owned proof source")
    text=["/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\nimport RamanujanPV.QuotientAlgorithm\nimport RamanujanPV.CheckerExecution\nnamespace RamanujanPV."+name+"\nopen QuotientSieve QuotientAlgorithm\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n"]
    previous=2;updates=0;finished=0;nextFinish=0;gaps=0;explicitRows={}
    for p in [*primes,root+1]:
        if p<previous:continue
        factors=[spf[k]for k in range(previous,p)]
        need(all(d>=2 and d<k and k%d==0 for k,d in zip(range(previous,p),factors)),"actual proposed complete composite gap")
        gap=f"gap_{gaps}";gaps+=1;literal="["+",".join(map(str,factors))+"]"
        text.append(f"theorem {gap} (v : Nat) : total {previous} v=total {p} v := jump_from_factors {previous} {literal} (by decide +kernel) v\n")
        def lift(v):
            val,proof,final=states[v]
            if final:return f"(use_finished (p:={p}) (by decide) {proof})"
            return f"(({gap} {v}).symm.trans {proof})"
        while nextFinish<len(values)and values[nextFinish]<p*p:
            v=values[nextFinish];nextFinish+=1
            if v!=a.n:
                proof=f"finished_{finished}";finished+=1
                text.append(f"theorem {proof} : Nat.primeCounting {v}={states[v][0]} := finish_value (p:={p}) (by decide) {lift(v)}\n")
                states[v]=[states[v][0],proof,True]
        if p==root+1:break
        bv,cv=states[p][0],states[p-1][0];bp,cp=lift(p),lift(p-1)
        for v in reversed(values):
            if v<p*p:break
            av,dv=states[v][0],states[v//p][0]
            new=av if bv==cv else av-(dv-cv)
            need(new>=0,"nonnegative mathematical subtraction")
            proof=f"node_{updates}";updates+=1;explicitRows[proof]=(av,bv,cv,dv)
            text.append(f"theorem {proof} : total {p+1} {v}={new} := local_step (p:={p}) (v:={v}) (y:={new}) (by decide) {lift(v)} {bp} {cp} {lift(v//p)} (by decide +kernel)\n")
            states[v]=[new,proof,False]
        previous=p+1
    result=states[a.n][0]
    text.append(f"theorem count : Nat.primeCounting {a.n}={result} := finish_value (p:={p}) (by decide) {lift(a.n)}\n")
    text.append(f"theorem source_run (heap : AST.C.Heap) :\n    ∃t, AST.C.Run AST.C.service (AST.C.stmt Source.countFunction.body)\n      (AST.C.countInput {a.n} heap) (.returned t {result}) ∧t.heap=heap := by\n  have run := (AST.C.source_count_is_primeCounting {a.n} (by decide) heap).2.1\n  simpa only [count] using run\n#print axioms count\n#print axioms source_run\nend RamanujanPV.{name}\n")
    source="".join(text)
    if a.explicit:
        import re
        source=source.replace("set_option Elab.async false", "attribute [local irreducible] QuotientSieve.total\nset_option Elab.async false")
        # Infer the numerical expression arguments only in this deterministic
        # untrusted generator; Lean checks their exact types and every equality.
        lines=[]
        for line in source.splitlines():
            if " := local_step "in line:
                m=re.match(r"theorem (node_\d+) : total (\d+) (\d+)=(\d+) := local_step \(p:=(\d+)\) \(v:=(\d+)\) \(y:=(\d+)\)",line)
                if not m:raise ValueError("exact node source grammar")
                # Arithmetic values are recovered from literal known-count
                # identities in a separate deterministic metadata map below.
                row=explicitRows[m[1]]
                args="".join(f" ({key}:={value})"for key,value in zip(["av","bv","cv","dv"],row))
                line=line.replace(" (by decide) ",args+" (by decide) ",1)
            lines.append(line)
        source="\n".join(lines)+"\n"
    if a.rfl:source=source.replace("(by decide +kernel)","rfl")
    if a.aggregate:
        startBody=source.index("theorem gap_0")
        startCount=source.index("theorem count :")
        startRun=source.index("theorem source_run")
        haves="\n".join("  have "+line[len("theorem "):]for line in source[startBody:startCount].splitlines())
        finalLine=source[startCount:startRun].strip();statement,proof=finalLine.split(" := ",1)
        source=source[:startBody]+statement+" := by\n"+haves+"\n  exact "+proof+"\n"+source[startRun:]
    module.write_text(source);out=Path("/data/ivy-ramanujan-source-pv-20261119")/("quotient-"+("explicit"if a.explicit else"aggregate"if a.aggregate else"optimized")+("-rfl"if a.rfl else"")+"-proposal-"+str(a.n));out.mkdir(exist_ok=False)
    receipt={"status":"UNTRUSTED_OPTIMIZED_PROOF_PROPOSAL_NOT_ACCEPTANCE","N":a.n,"pi":result,"updates":updates,"finished_cells":finished,"prime_gap_certificates":gaps,"module":str(module),"source_bytes":module.stat().st_size,"source_sha256":sha(module),"generator_sha256":sha(__file__),"generation_seconds":time.monotonic()-start,"seed":None,"trust_boundary":"Python optimization and candidate prime list untrusted; actual generated Lean proof checks every gap and arithmetic update. Optimized C source correspondence remains separate."}
    (out/"PROPOSAL.json").write_text(json.dumps(receipt,indent=2)+"\n");print(json.dumps(receipt,indent=2))
if __name__=="__main__":main()
