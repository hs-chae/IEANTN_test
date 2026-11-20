#!/usr/bin/env python3
"""Untrusted deterministic proposal of a structured AST and matching C source.

Lean independently checks exact source bytes against its typed AST renderer.
No primality flags, prime counts, expected outputs or source-execution facts
are generated or accepted by this script.
"""
from pathlib import Path
import json

S = Path(__file__).resolve().parents[1]


def V(name): return ('var', name)
def N(value): return ('nat', value)
def B(op, a, b): return ('binary', op, a, b)
def I(a, b): return ('index', a, b)
def U(op, a): return ('unary', op, a)
def Q(*body): return ('sequence', list(body))
def D(name, value): return ('declare', name, value)
def E(value): return ('eval', value)
def R(value): return ('returnStmt', value)
def F(name, start, guard, step, body): return ('forLoop', D(name, start), guard, step, body)
def H(guard, yes, no=('skip',)): return ('branch', guard, yes, no)
def A(name, value): return E(B('=', V(name), value))


body = Q(
    H(B('<', V('lo'), N(2)), R(N(0))),
    H(B('<', V('hi'), V('lo')), R(N(0))),
    H(B('>', V('hi'), N(2000000000000)), R(N(0))),
    D('length', B('+', B('-', V('hi'), V('lo')), N(1))),
    H(B('<', V('capacity'), V('length')), R(N(0))),
    F('i', N(0), B('<', V('i'), V('length')), U('++', V('i')),
      E(B('=', I(V('flags'), V('i')), N(1)))),
    F('d', N(2), B('<=', V('d'), B('/', V('hi'), V('d'))), U('++', V('d')),
      Q(D('first', B('*', B('/', V('lo'), V('d')), V('d'))),
        H(B('<', V('first'), V('lo')), A('first', B('+', V('first'), V('d')))),
        H(B('<', V('first'), B('*', V('d'), V('d'))), A('first', B('*', V('d'), V('d')))),
        F('m', V('first'), B('<=', V('m'), V('hi')), B('=', V('m'), B('+', V('m'), V('d'))),
          E(B('=', I(V('flags'), B('-', V('m'), V('lo'))), N(0)))))),
    D('count', N(0)),
    F('i', N(0), B('<', V('i'), V('length')), U('++', V('i')),
      Q(H(B('==', I(V('claims'), V('i')), I(V('flags'), V('i'))), ('skip',), R(N(0))),
        A('count', B('+', V('count'), I(V('flags'), V('i')))))),
    R(B('+', V('count'), N(1))),
)
parameters = [('uint64_t', 'lo'), ('uint64_t', 'hi'), ('uint64_t', 'capacity'),
              ('uint64_t*', 'claims'), ('uint64_t*', 'flags')]


def expression(e):
    tag = e[0]
    if tag == 'var': return e[1]
    if tag == 'nat': return str(e[1])
    if tag == 'binary': return '(' + expression(e[2]) + e[1] + expression(e[3]) + ')'
    if tag == 'index': return '(' + expression(e[1]) + '[' + expression(e[2]) + '])'
    if tag == 'unary': return '(' + e[1] + expression(e[2]) + ')'
    raise ValueError('unknown expression')


def statement(s):
    tag = s[0]
    if tag == 'skip': return ';'
    if tag == 'sequence': return '{' + '\n'.join(map(statement, s[1])) + '}'
    if tag == 'declare': return 'uint64_t ' + s[1] + '=' + expression(s[2]) + ';'
    if tag == 'eval': return expression(s[1]) + ';'
    if tag == 'returnStmt': return 'return ' + expression(s[1]) + ';'
    if tag == 'branch': return 'if(' + expression(s[1]) + ')' + statement(s[2]) + 'else ' + statement(s[3])
    if tag == 'forLoop': return 'for(' + statement(s[1]) + expression(s[2]) + ';' + expression(s[3]) + ')' + statement(s[4])
    raise ValueError('unknown statement')


def quote(s): return json.dumps(s)


def lean_expr(e):
    tag = e[0]
    if tag in ['var', 'nat']: return '(.' + tag + ' ' + (quote(e[1]) if tag == 'var' else str(e[1])) + ')'
    if tag == 'binary': return '(.binary ' + quote(e[1]) + ' ' + lean_expr(e[2]) + ' ' + lean_expr(e[3]) + ')'
    if tag == 'index': return '(.index ' + lean_expr(e[1]) + ' ' + lean_expr(e[2]) + ')'
    if tag == 'unary': return '(.unary ' + quote(e[1]) + ' ' + lean_expr(e[2]) + ')'
    raise ValueError('unknown expression')


def lean_stmt(s):
    tag = s[0]
    if tag == 'skip': return '.skip'
    if tag == 'sequence': return '(.sequence [' + ','.join(map(lean_stmt, s[1])) + '])'
    if tag == 'declare': return '(.declare [⟨"uint64_t",' + quote(s[1]) + ',some ' + lean_expr(s[2]) + '⟩])'
    if tag == 'eval': return '(.eval ' + lean_expr(s[1]) + ')'
    if tag == 'returnStmt': return '(.returnStmt ' + lean_expr(s[1]) + ')'
    if tag == 'branch': return '(.branch ' + lean_expr(s[1]) + ' ' + lean_stmt(s[2]) + ' ' + lean_stmt(s[3]) + ')'
    if tag == 'forLoop': return '(.forLoop ' + lean_stmt(s[1]) + ' (some ' + lean_expr(s[2]) + ') ' + lean_expr(s[3]) + ' ' + lean_stmt(s[4]) + ')'
    raise ValueError('unknown statement')


header = '/*\nCopyright (c) 2026 IEANTN contributors. All rights reserved.\nReleased under Apache 2.0 license as described in the file LICENSE.\nAuthors: OpenAI (Codex)\n*/\n#include <stdint.h>\n\n'
c_source = header + 'uint64_t rpc_check_segment(' + ','.join(t + ' ' + n for t, n in parameters) + ')' + statement(body) + '\n'
lean_source = '''/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
import RamanujanPV.QuotientCMachine
namespace RamanujanPV.SegmentCheckerSource
open LCMSourcePV.Witness.C
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def checkerFunction : Function := ⟨"uint64_t","rpc_check_segment",PARAMS,BODY⟩
def functions : List Function := [checkerFunction]
def render (program : List Function) : Option String := do
  return HEADER ++ (←renderFunctions program)
def actualSource : String := include_str "../c/verified_segment_checker.c"
theorem actual_source_bytes : render functions = some actualSource := by decide +kernel
theorem actual_source_checked : LCMSourcePV.RestrictedC.SourceCorresponds render actualSource functions :=
  LCMSourcePV.RestrictedC.source_corresponds_of_exact render actualSource functions
    actual_source_bytes (by decide +kernel)
theorem source_expression_depth : QuotientCMachine.stmtWithin 4 32 checkerFunction.body = true := by decide +kernel
#print axioms actual_source_checked
#print axioms source_expression_depth
end RamanujanPV.SegmentCheckerSource
'''.replace('PARAMS', '[' + ','.join('(' + quote(t) + ',' + quote(n) + ')' for t, n in parameters) + ']')
lean_source = lean_source.replace('BODY', lean_stmt(body)).replace('HEADER', quote(header))
(S / 'c' / 'verified_segment_checker.c').write_text(c_source)
(S / 'RamanujanPV' / 'SegmentCheckerSource.lean').write_text(lean_source)
print(json.dumps({'status': 'UNTRUSTED_SOURCE_AST_PROPOSAL_WRITTEN', 'function': 'rpc_check_segment',
                  'numerical_outputs_generated': False, 'next': 'Kernel source byte/depth check and execution correctness proofs.'}))
