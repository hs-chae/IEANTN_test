#!/usr/bin/env python3
"""Structured proposal matching the original F60/20-term/41-tail arithmetic."""
from pathlib import Path
import json,hashlib
S=Path(__file__).resolve().parents[1]
HEADER='/*\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n*/\n#include <stdint.h>\n\n'
LH='/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\n'
def expr(x,L=False):
 if isinstance(x,int):return f'(.nat {x})'if L else str(x)
 if isinstance(x,str):return f'(.var "{x}")'if L else x
 op,*a=x
 if op=='cast':return '(.cast "'+a[0]+'" '+expr(a[1],True)+')'if L else '(('+a[0]+')'+expr(a[1])+')'
 if op=='call':return '(.call '+expr(a[0],True)+' ['+','.join(expr(v,True)for v in a[1])+'])'if L else expr(a[0])+'('+','.join(expr(v)for v in a[1])+')'
 if op=='++':return '(.unary "++" '+expr(a[0],True)+')'if L else '(++'+expr(a[0])+')'
 return '(.binary "'+op+'" '+expr(a[0],True)+' '+expr(a[1],True)+')'if L else '('+expr(a[0])+op+expr(a[1])+')'
def stmt(x,L=False):
 op,*a=x
 if op=='seq':return '(.sequence ['+','.join(stmt(v,True)for v in a[0])+'])'if L else '{'+'\n'.join(stmt(v)for v in a[0])+'}'
 if op=='decl':
  typ,name,value=a;return '(.declare [⟨"'+typ+'","'+name+'",some '+expr(value,True)+'⟩])'if L else typ+' '+name+'='+expr(value)+';'
 if op=='eval':return '(.eval '+expr(a[0],True)+')'if L else expr(a[0])+';'
 if op=='ret':return '(.returnStmt '+expr(a[0],True)+')'if L else 'return '+expr(a[0])+';'
 if op=='if':return '(.branch '+expr(a[0],True)+' '+stmt(a[1],True)+' .skip)'if L else 'if('+expr(a[0])+')'+stmt(a[1])+'else ;'
 if op=='while':return '(.whileLoop '+expr(a[0],True)+' '+stmt(a[1],True)+')'if L else 'while('+expr(a[0])+')'+stmt(a[1])
 if op=='for':return '(.forLoop '+stmt(a[0],True)+' (some '+expr(a[1],True)+') '+expr(a[2],True)+' '+stmt(a[3],True)+')'if L else 'for('+stmt(a[0])+expr(a[1])+';'+expr(a[2])+')'+stmt(a[3])
 raise ValueError('unsupported structured statement')
def wide(x):return('cast','__uint128_t',x)
def narrow(x):return('cast','uint64_t',x)
def call(*args):return('call','rpc_log_ceildiv',list(args))
def main():
 ceil=('seq',[('if',('==','b',0),('ret',narrow(0))),('ret',narrow(('+',('/','a','b'),('!=',('%','a','b'),0))))])
 series=('seq',[('decl','uint64_t','F',1<<60),('decl','uint64_t','z',call(('*',wide('F'),'num'),'den')),('decl','uint64_t','z2',call(('*',wide('z'),'z'),'F')),('decl','uint64_t','power','z'),('decl','__uint128_t','sum',0),('for',('decl','uint64_t','k',0),('<','k',20),('++','k'),('seq',[('eval',('=','sum',('+','sum',call('power',('+',('*',2,'k'),1))))),('eval',('=','power',call(('*',wide('power'),'z2'),'F')))])),('ret',narrow(('+',('*',2,'sum'),call(('*',('*',wide(2),'power'),'F'),('*',wide(41),('-','F','z2'))))))])
 upper=('seq',[('if',('<','n',2),('ret',narrow(0))),('decl','uint64_t','two',1),('decl','uint64_t','k',0),('while',('<=','two',('/','n',2)),('seq',[('eval',('=','two',('*','two',2))),('eval',('++','k'))])),('decl','uint64_t','log2',('call','rpc_log_series_upper',[1,3])),('ret',call(('+',('*',wide('k'),'log2'),('call','rpc_log_series_upper',[('-','n','two'),('+','n','two')])),1<<20))])
 fs=[('ceilFunction','uint64_t','rpc_log_ceildiv',[('__uint128_t','a'),('__uint128_t','b')],ceil),('seriesFunction','uint64_t','rpc_log_series_upper',[('uint64_t','num'),('uint64_t','den')],series),('upperFunction','uint64_t','rpc_log_upper',[('uint64_t','n')],upper)]
 c=HEADER+'\n'.join(rt+' '+name+'('+','.join(t+' '+n for t,n in ps)+')'+stmt(body)+'\n'for _,rt,name,ps,body in fs)
 t=LH+'import LCMSourcePV.ASTLoops\nnamespace RamanujanPV.FiniteLogSource\nopen LCMSourcePV.Witness.C\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\nset_option Elab.async false\n'
 for symbol,rt,name,ps,body in fs:t+='def '+symbol+' : Function := ⟨"'+rt+'","'+name+'",['+','.join('("'+a+'","'+b+'")'for a,b in ps)+'],'+stmt(body,True)+'⟩\n'
 t+='def functions : List Function := [ceilFunction,seriesFunction,upperFunction]\ndef render (_ : Unit) : Option String := do\n  return '+json.dumps(HEADER)+'++(←renderFunctions functions)\ndef actualSource : String := include_str "../c/verified_finite_log.c"\ntheorem actual_source_bytes : render ()=some actualSource := by decide +kernel\ntheorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource () :=\n  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource () actual_source_bytes (by decide +kernel)\n#print axioms actual_source_bytes\n#print axioms actual_source_checked\nend RamanujanPV.FiniteLogSource\n'
 for p,text in [(S/'c/verified_finite_log.c',c),(S/'RamanujanPV/FiniteLogSource.lean',t)]:
  if p.exists()and p.read_text()!=text:raise ValueError('preserve existing source version before replacement')
  p.write_text(text);print(p,hashlib.sha256(p.read_bytes()).hexdigest())
if __name__=='__main__':main()
