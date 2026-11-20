#!/usr/bin/env python3
"""Deterministic structured-AST proposal for the original20-step e constants."""
from pathlib import Path
import json,hashlib
S=Path(__file__).resolve().parents[1]
HEADER='/*\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n*/\n#include <stdint.h>\n\n'
LH='/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\n'
def expr(x,lean=False):
 if isinstance(x,int):return f'(.nat {x})'if lean else str(x)
 if isinstance(x,str):return f'(.var "{x}")'if lean else x
 op,*args=x
 if op=='call':return '(.call '+expr(args[0],True)+' ['+','.join(expr(a,True)for a in args[1])+'])'if lean else expr(args[0])+'('+','.join(expr(a)for a in args[1])+')'
 if op=='++':return '(.unary "++" '+expr(args[0],True)+')'if lean else '(++'+expr(args[0])+')'
 return '(.binary "'+op+'" '+expr(args[0],True)+' '+expr(args[1],True)+')'if lean else '('+expr(args[0])+op+expr(args[1])+')'
def stmt(x,lean=False):
 op,*args=x
 if op=='seq':return '(.sequence ['+','.join(stmt(a,True)for a in args[0])+'])'if lean else '{'+'\n'.join(stmt(a)for a in args[0])+'}'
 if op=='decl':
  name,value=args
  return '(.declare [⟨"uint64_t","'+name+'",some '+expr(value,True)+'⟩])'if lean else 'uint64_t '+name+'='+expr(value)+';'
 if op=='eval':return '(.eval '+expr(args[0],True)+')'if lean else expr(args[0])+';'
 if op=='return':return '(.returnStmt '+expr(args[0],True)+')'if lean else 'return '+expr(args[0])+';'
 if op=='for':
  initial,guard,step,body=args
  return '(.forLoop '+stmt(initial,True)+' (some '+expr(guard,True)+') '+expr(step,True)+' '+stmt(body,True)+')'if lean else 'for('+stmt(initial)+expr(guard)+';'+expr(step)+')'+stmt(body)
 raise ValueError('unhandled structured statement')
def main():
 low=('seq',[('decl','term',1<<60),('decl','total',1<<60),('for',('decl','k',1),('<=','k',20),('++','k'),('seq',[('eval',('=','term',('/','term','k'))),('eval',('=','total',('+','total','term')))])),('return','total')])
 high=('seq',[('return',('+',('call','rpc_e_low',[]),22))])
 functions=[('lowFunction','rpc_e_low',low),('highFunction','rpc_e_high',high)]
 c=HEADER+'\n'.join('uint64_t '+name+'()'+stmt(body)+'\n'for _,name,body in functions)
 text=LH+'import LCMSourcePV.ASTLoops\nnamespace RamanujanPV.FiniteExpSource\nopen LCMSourcePV.Witness.C\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
 for symbol,name,body in functions:text+='def '+symbol+' : Function := ⟨"uint64_t","'+name+'",[],'+stmt(body,True)+'⟩\n'
 text+='def functions : List Function := [lowFunction,highFunction]\ndef render (_ : Unit) : Option String := do\n  return '+json.dumps(HEADER)+'++(←renderFunctions functions)\ndef actualSource : String := include_str "../c/verified_finite_exp.c"\ntheorem actual_source_bytes : render ()=some actualSource := by decide +kernel\ntheorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource () :=\n  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource () actual_source_bytes (by decide +kernel)\n#print axioms actual_source_bytes\n#print axioms actual_source_checked\nend RamanujanPV.FiniteExpSource\n'
 for p,payload in [(S/'c/verified_finite_exp.c',c),(S/'RamanujanPV/FiniteExpSource.lean',text)]:
  if p.exists()and p.read_text()!=payload:raise ValueError('existing source differs; preserve before replacement')
  p.write_text(payload);print(p,hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()
