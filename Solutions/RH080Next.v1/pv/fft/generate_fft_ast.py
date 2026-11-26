#!/usr/bin/env python3
"""Untrusted pointer/index candidate frontend, checked by independent grammar."""
import argparse,importlib.util,json,re,sys
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
S=HERE.parent
spec=importlib.util.spec_from_file_location('candidate_array_parser',HERE/'parse_arrays.py');module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
ap=argparse.ArgumentParser(allow_abbrev=False);ap.add_argument('--recursive',action='store_true');ap.add_argument('--fap',action='store_true');args=ap.parse_args()
prefix=('FapFFTRecursive'if args.recursive else'FapFFT')if args.fap else('FFTRecursive'if args.recursive else'FFT');ns='RH080Next.'+prefix+'PV'
raw=(HERE/(('fap_fft'if args.fap else'w4_fft')+('_recursive'if args.recursive else'')+'.c')).read_bytes();source=raw.decode('ascii');fs=module.Parser(source).functions()
head='''import GoldbachDirect.Correspondence.Specification
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RH080Next.FFTPV
open GoldbachDirect
'''
head=head.replace('RH080Next.FFTPV',ns)
ast='\n'.join('def '+n+'_ast : Function :=\n '+term+'\n'for n,term in fs)
ast+='\ndef program : Program := ['+', '.join(['.include .stdint','.include .stdio','.include .stdlib']+['.function '+n+'_ast'for n,_ in fs])+']\nend '+ns+'\n'
(S/'lean'/(prefix+'AST.lean')).write_text(head+ast)
template=(S/'lean/WindowSource.lean').read_text();template=template[template.index('def checkedSyntax'):].replace('RH080Next.WindowPV',ns)
a=template.index('theorem actual_ast_tokens');b=template.index('theorem actual_ast_guard',a)
proof='''theorem actual_ast_tokens : program.tokens = expectedTokens := by
  simp (config := { maxSteps := 10000000 }) only [program, Program.tokens, Top.tokens, Function.tokens,
    '''+', '.join(n+'_ast'for n,_ in fs)+''',
    Stmt.tokens, Expr.tokens, Literal.tokens, CType.tokens, Binary.token,
    comma, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.nil_append, List.append_nil]
  decide +kernel

'''
template=template[:a]+proof+template[b:]
chars=', '.join('Char.ofNat '+str(x)for x in raw)
ts=re.findall(r'"(?:[^"\\]|\\.)*"|[A-Za-z0-9_]+|==|!=|<=|>=|&&|\|\||[^\s]',re.sub(r'/\*.*?\*/','',source,flags=re.S))
sourceDefs='def sourceChars : List Char := ['+chars+']\ndef source : String := String.ofList sourceChars\ndef expectedTokens : List String := '+json.dumps(ts)+'\n'
(S/'lean'/(prefix+'Source.lean')).write_text(head.replace('import GoldbachDirect.Correspondence.Specification','import '+prefix+'AST')+sourceDefs+template)
print(json.dumps(dict(status='UNTRUSTED_ARRAY_AST_CANDIDATE',functions=len(fs),bytes=len(raw))))
