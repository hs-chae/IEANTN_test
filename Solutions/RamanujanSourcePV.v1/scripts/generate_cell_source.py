#!/usr/bin/env python3
"""Exact seven-field cell guard source and its structured AST (proposal only)."""
from pathlib import Path
import hashlib,json
from generate_log_source import expr,stmt,LH
S=Path(__file__).resolve().parents[1]
HEADER='/*\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n*/\n#include <stdint.h>\n#include "verified_finite_exp.c"\n#include "verified_finite_log.c"\n\n'
def wide(x):return('cast','__uint128_t',x)
def bad(condition):return('if',condition,('ret',0))
def main():
 fields=['n','next','j','P','Q','Lu','A']
 body=('seq',[
  bad(('<','n',38358837683)),bad(('<=','next','n')),bad(('>','next',2000000000001)),
  bad(('>','j','n')),bad(('>','Q','j')),bad(('>','P',('-','next',1))),bad(('==','Lu',0)),
  bad(('!=','Lu',('call','rpc_log_upper',['n']))),
  ('decl','uint64_t','lo',('call','rpc_e_low',[])),('decl','uint64_t','hi',('call','rpc_e_high',[])),
  bad(('>',('*',wide('j'),'hi'),('*',wide('n'),1<<60))),
  bad(('!=',wide('A'),('/',('*',wide('n'),'lo'),'Lu'))),
  ('ret',('<',('*',('*',wide(1<<20),'P'),'P'),('*',wide('A'),'Q')))])
 params=[('uint64_t',n)for n in fields]
 c=HEADER+'int rpc_finite_cell('+','.join(t+' '+n for t,n in params)+')'+stmt(body)+'\n'
 t=LH+'import RamanujanPV.FiniteLogSource\nimport RamanujanPV.FiniteExpSource\nnamespace RamanujanPV.FiniteCellSource\nopen LCMSourcePV.Witness.C\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 t+='def cellFunction : Function := ⟨"int","rpc_finite_cell",['+','.join('("'+a+'","'+b+'")'for a,b in params)+'],'+stmt(body,True)+'⟩\n'
 t+='def render (_ : Unit) : Option String := do\n  return '+json.dumps(HEADER)+'++(←renderFunctions [cellFunction])\ndef actualSource : String := include_str "../c/verified_finite_cell.c"\ntheorem actual_source_bytes : render ()=some actualSource := by decide +kernel\ntheorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource () :=\n  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource () actual_source_bytes (by decide +kernel)\n#print axioms actual_source_bytes\n#print axioms actual_source_checked\nend RamanujanPV.FiniteCellSource\n'
 for p,content in [(S/'c/verified_finite_cell.c',c),(S/'RamanujanPV/FiniteCellSource.lean',t)]:
  if p.exists()and p.read_text()!=content:raise ValueError('preserve existing source before modification')
  p.write_text(content);print(p,hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()
