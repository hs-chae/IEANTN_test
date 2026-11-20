#!/usr/bin/env python3
"""Regenerate structured-AST and executable C proposals; Lean checks the binding."""
from pathlib import Path
import json
S=Path(__file__).resolve().parents[1]
def var(n):return ('var',n)
def num(n):return ('nat',n)
def binary(op,a,b):return ('binary',op,a,b)
def at(name,index):return ('index',var(name),index)
def call(name,args):return ('call',var(name),args)
def inc(name):return ('unary','++',var(name))
def dec(name):return ('unary','--',var(name))
def seq(*stmts):return ('sequence',list(stmts))
def decl(name,e):return ('declare',[('uint64_t',name,e)])
def assign(name,e):return ('eval',binary('=',var(name),e))
def store(name,index,e):return ('eval',binary('=',at(name,index),e))
def ret(e):return ('returnStmt',e)
def branch(e,yes,no=('skip',)):return ('branch',e,yes,no)
def guard(e):return branch(e,ret(num(0)))
def loop(init,condition,step,body):return ('forLoop',init,condition,step,body)
def whileLoop(condition,body):return ('whileLoop',condition,body)
def cexpr(e):
 t,*a=e
 if t=='var':return a[0]
 if t=='nat':return str(a[0])
 if t=='binary':return '('+cexpr(a[1])+a[0]+cexpr(a[2])+')'
 if t=='unary':return '('+a[0]+cexpr(a[1])+')'
 if t=='index':return '('+cexpr(a[0])+'['+cexpr(a[1])+'])'
 if t=='call':return cexpr(a[0])+'('+','.join(map(cexpr,a[1]))+')'
 raise ValueError(t)
def leanexpr(e):
 t,*a=e
 if t=='var':return '(.var '+json.dumps(a[0])+')'
 if t=='nat':return '(.nat '+str(a[0])+')'
 if t=='binary':return '(.binary '+json.dumps(a[0])+' '+leanexpr(a[1])+' '+leanexpr(a[2])+')'
 if t=='unary':return '(.unary '+json.dumps(a[0])+' '+leanexpr(a[1])+')'
 if t=='index':return '(.index '+leanexpr(a[0])+' '+leanexpr(a[1])+')'
 if t=='call':return '(.call '+leanexpr(a[0])+' ['+','.join(map(leanexpr,a[1]))+'])'
 raise ValueError(t)
def cstmt(st):
 t,*a=st
 if t=='skip':return ';'
 if t=='sequence':return '{'+'\n'.join(map(cstmt,a[0]))+'}'
 if t=='declare':return '\n'.join(ty+' '+name+'='+cexpr(e)+';'for ty,name,e in a[0])
 if t=='eval':return cexpr(a[0])+';'
 if t=='returnStmt':return 'return '+cexpr(a[0])+';'
 if t=='branch':return 'if('+cexpr(a[0])+')'+cstmt(a[1])+'else '+cstmt(a[2])
 if t=='whileLoop':return 'while('+cexpr(a[0])+')'+cstmt(a[1])
 if t=='forLoop':return 'for('+cstmt(a[0])+cexpr(a[1])+';'+cexpr(a[2])+')'+cstmt(a[3])
 raise ValueError(t)
def leanstmt(st):
 t,*a=st
 if t=='skip':return '.skip'
 if t=='sequence':return '(.sequence ['+','.join(map(leanstmt,a[0]))+'])'
 if t=='declare':return '(.declare ['+','.join('⟨'+json.dumps(ty)+','+json.dumps(name)+',some '+leanexpr(e)+'⟩'for ty,name,e in a[0])+'])'
 if t=='eval':return '(.eval '+leanexpr(a[0])+')'
 if t=='returnStmt':return '(.returnStmt '+leanexpr(a[0])+')'
 if t=='branch':return '(.branch '+leanexpr(a[0])+' '+leanstmt(a[1])+' '+leanstmt(a[2])+')'
 if t=='whileLoop':return '(.whileLoop '+leanexpr(a[0])+' '+leanstmt(a[1])+')'
 if t=='forLoop':return '(.forLoop '+leanstmt(a[0])+' (some '+leanexpr(a[1])+') '+leanexpr(a[2])+' '+leanstmt(a[3])+')'
 raise ValueError(t)
def function(name,params,body):return ('uint64_t',name,params,body)
def cfun(f):
 ty,name,params,body=f
 return ty+' '+name+'('+','.join(t+' '+n for t,n in params)+')'+cstmt(body)+'\n'
def leanfun(f):
 ty,name,params,body=f
 return '⟨'+json.dumps(ty)+','+json.dumps(name)+',['+','.join('('+json.dumps(t)+','+json.dumps(n)+')'for t,n in params)+'],'+leanstmt(body)+'⟩'
def main():
 n,r,p,i,v,q,sub,before,stop,ip,square=[var(x)for x in ['n','r','p','i','v','q','sub','before','stop','ip','square']]
 rootFun=function('rpc_isqrt',[('uint64_t','n')],seq(decl('r',num(0)),whileLoop(binary('<=',binary('+',r,num(1)),binary('/',n,binary('+',r,num(1)))),seq(('eval',inc('r')))),ret(r)))
 largeBody=seq(decl('ip',binary('*',i,p)),decl('sub',num(0)),branch(binary('<=',ip,r),assign('sub',at('large',ip)),assign('sub',at('small',binary('/',n,ip)))),guard(binary('<',sub,before)),guard(binary('<',at('large',i),binary('-',sub,before))),store('large',i,binary('-',at('large',i),binary('-',sub,before))))
 smallBody=seq(decl('sub',at('small',binary('/',v,p))),guard(binary('<',sub,before)),guard(binary('<',at('small',v),binary('-',sub,before))),store('small',v,binary('-',at('small',v),binary('-',sub,before))),('eval',dec('v')))
 primeBody=seq(decl('before',at('small',binary('-',p,num(1)))),decl('stop',r),branch(binary('<',binary('/',n,binary('*',p,p)),r),assign('stop',binary('/',n,binary('*',p,p)))),loop(decl('i',num(1)),binary('<=',i,stop),inc('i'),largeBody),decl('square',binary('*',p,p)),branch(binary('<=',square,r),seq(decl('v',r),whileLoop(binary('<=',square,v),smallBody))))
 countFun=function('rpc_quotient_count',[('uint64_t','n'),('uint64_t','capacity'),('uint64_t*','small'),('uint64_t*','large')],seq(guard(binary('<',n,num(2))),guard(binary('>',n,num(2000000000000))),decl('r',call('rpc_isqrt',[n])),guard(binary('<=',var('capacity'),r)),loop(decl('i',num(1)),binary('<=',i,r),inc('i'),seq(store('small',i,binary('-',i,num(1))),store('large',i,binary('-',binary('/',n,i),num(1))))),loop(decl('p',num(2)),binary('<=',p,r),inc('p'),branch(binary('==',at('small',p),at('small',binary('-',p,num(1)))),('skip',),primeBody)),ret(at('large',num(1)))))
 functions=[rootFun,countFun]
 copyright='Copyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n'
 source='/*\n'+copyright+'*/\n#include <stdint.h>\n\n'+'\n'.join(map(cfun,functions))
 ctarget=S/'c/verified_quotient_count.c'
 if ctarget.exists() and ctarget.read_text()!=source:raise ValueError('existing C source differs; preserve it and use an explicit new version')
 if not ctarget.exists():ctarget.write_text(source)
 lean='/-\n'+copyright+'-/\nimport LCMSourcePV.ASTLoops\nnamespace RamanujanPV.QuotientCSource\nopen LCMSourcePV.Witness.C\nset_option autoImplicit false\nset_option maxHeartbeats 0\nset_option maxRecDepth 100000\n'
 lean+='def sqrtFunction : Function := '+leanfun(rootFun)+'\n'
 lean+='def countFunction : Function := '+leanfun(countFun)+'\n'
 lean+='def functions : List Function := [sqrtFunction,countFunction]\n'
 lean+='def render (_ : Unit) : Option String := do\n  return "#include <stdint.h>\\n\\n"++(←renderFunctions functions)\n'
 lean+='def actualSource : String := include_str "../c/verified_quotient_count.c"\n'
 lean+='theorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource () := by\n  refine ⟨(render ()).getD "",?_,?_,?_⟩\n  · simp [render]\n  · decide +kernel\n  · decide +kernel\n#print axioms actual_source_checked\nend RamanujanPV.QuotientCSource\n'
 lean=lean.replace('namespace RamanujanPV.QuotientCSource','namespace RamanujanPV.QuotientCSourceV2').replace('end RamanujanPV.QuotientCSource','end RamanujanPV.QuotientCSourceV2')
 prefix=source[:source.index('uint64_t rpc_isqrt')]
 lean=lean.replace('"#include <stdint.h>\\n\\n"',json.dumps(prefix))
 lean=lean[:lean.index('theorem actual_source_checked')]+"/-- Exact complete source bytes, including its copyright comment. The\nuntrusted deterministic renderer proposal is checked by the Lean kernel. -/\ntheorem actual_source_bytes : render ()=some actualSource := by decide +kernel\n/-- Byte identity avoids evaluating two full lexical scans. Only the actual\nsource's successful restricted scan remains a numerical kernel obligation. -/\ntheorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource () :=\n  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource ()\n    actual_source_bytes (by decide +kernel)\n#print axioms actual_source_bytes\n#print axioms actual_source_checked\nend RamanujanPV.QuotientCSourceV2\n"
 target=S/'RamanujanPV/QuotientCSourceV2.lean'
 if target.exists() and target.read_text()!=lean:raise ValueError('regenerated AST/binding differs from preserved source')
 if not target.exists():target.write_text(lean)
 alias='/-\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n-/\nimport RamanujanPV.QuotientCSourceV2\nnamespace RamanujanPV.QuotientCSource\nabbrev sqrtFunction := QuotientCSourceV2.sqrtFunction\nabbrev countFunction := QuotientCSourceV2.countFunction\nabbrev functions := QuotientCSourceV2.functions\nabbrev render := QuotientCSourceV2.render\nabbrev actualSource := QuotientCSourceV2.actualSource\n/-- The first direct binding attempt is archived with its failed render\nproof. This canonical interface uses the completed exact-byte refinement. -/\ntheorem actual_source_bytes : render ()=some actualSource := QuotientCSourceV2.actual_source_bytes\ntheorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource () :=\n  QuotientCSourceV2.actual_source_checked\n#print axioms actual_source_bytes\n#print axioms actual_source_checked\nend RamanujanPV.QuotientCSource\n'
 canonical=S/'RamanujanPV/QuotientCSource.lean'
 if canonical.exists() and canonical.read_text()!=alias:raise ValueError('canonical accepted source differs; never overwrite')
 if not canonical.exists():canonical.write_text(alias)
 print(json.dumps({'status':'SOURCE_AND_AST_PROPOSAL_REQUIRE_KERNEL_BINDING','C_bytes':len(source.encode()),'Lean_bytes':len(lean.encode())}))
if __name__=='__main__':main()
