#!/usr/bin/env python3
"""Untrusted candidate frontend; the reused independent Lean grammar checks it."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
sys.dont_write_bytecode = True
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OLD = ROOT/'Solutions/RH080Study.v1/pv'
HEADER = '''/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
'''


def need(value, message):
    if not value:
        raise ValueError(message)


def main():
    specification = importlib.util.spec_from_file_location('unchanged_candidate_parser', OLD/'parse_source.py')
    parser = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(parser)
    raw = (HERE/'window_scalars.c').read_bytes()
    source = raw.decode('ascii')
    need(bytes(map(ord, source)) == raw, 'Physical ASCII source differs')
    functions = parser.Parser(source).functions()
    prefix = HEADER+'''import GoldbachDirect.Correspondence.Specification

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace RH080Next.WindowPV
open GoldbachDirect

'''
    defs = ['def '+name+'_ast : Function :=\n  '+term+'\n' for name, term in functions]
    items = ['.include .stdint', '.include .stdio']+['.function '+name+'_ast' for name, _ in functions]
    defs.append('def program : Program := ['+', '.join(items)+']\n')
    (HERE/'lean/WindowAST.lean').write_text(prefix+'\n'.join(defs)+'\nend RH080Next.WindowPV\n')
    token_text = re.sub(r'/\*.*?\*/', '', source, flags=re.S)
    tokens = re.findall(r'"(?:[^"\\]|\\.)*"|[A-Za-z0-9_]+|==|!=|<=|>=|&&|\|\||[^\s]', token_text)
    chars = ', '.join('Char.ofNat '+str(x) for x in raw)
    body = ['def sourceChars : List Char := ['+chars+']\n',
            'def source : String := String.ofList sourceChars\n',
            'def expectedTokens : List String := '+json.dumps(tokens)+'\n']
    body.append('''def checkedSyntax (s : String) (p : Program) : Bool :=
  checkedSource s p && Correspondence.supportedProgramSyntax p &&
    Correspondence.preprocessingAccepted s

theorem checkedSyntax_sound {s : String} {p : Program}
    (checked : checkedSyntax s p = true) : Correspondence.SourceSyntaxCorresponds s p := by
  simp only [checkedSyntax, Bool.and_eq_true] at checked
  exact .derived (checkedSource_lexes checked.1.1)
    (Correspondence.supportedProgramSyntax_sound checked.1.2)
    (Correspondence.preprocessingAccepted_sound checked.2)

theorem actual_lexed : tokenize source = some expectedTokens := by
  unfold tokenize
  simp only [source,String.toList_ofList,String.length_ofList]
  decide +kernel

theorem actual_ast_tokens : program.tokens = expectedTokens := by
  simp (config := { maxSteps := 10000000 }) only [program, Program.tokens, Top.tokens, Function.tokens,
    '''+', '.join(name+'_ast' for name, _ in functions)+''',
    Stmt.tokens, Expr.tokens, Literal.tokens, CType.tokens, Binary.token,
    comma, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.nil_append, List.append_nil]
  decide +kernel

theorem actual_ast_guard : Correspondence.supportedProgramSyntax program = true := by
  decide +kernel

theorem actual_preprocessing : Correspondence.preprocessingAccepted source = true := by
  unfold Correspondence.preprocessingAccepted
  simp only [source,String.toList_ofList]
  decide +kernel

theorem actual_source_checked : checkedSyntax source program = true := by
  simp [checkedSyntax,checkedSource,actual_lexed,actual_ast_tokens,
    actual_ast_guard,actual_preprocessing]

theorem actual_source_syntax : Correspondence.SourceSyntaxCorresponds source program :=
  checkedSyntax_sound actual_source_checked

#print axioms checkedSyntax_sound
#print axioms actual_source_syntax
end RH080Next.WindowPV
''')
    (HERE/'lean/WindowSource.lean').write_text(prefix.replace('import GoldbachDirect.Correspondence.Specification','import WindowAST')+'\n'.join(body))
    data = json.loads((HERE/'w4.json').read_text())
    encoded = [data['scale']+x for x in data['coefficients']]
    data_source = HEADER+'''import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Range

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace RH080Next.WindowPV.Data

def scale : Nat := 10000000000000000
def mesh : Nat := 360
def encoded : List Nat := '''+str(encoded)+'''

def encodedNode (j : Nat) : Nat := encoded[j]?.getD scale
def integerNode (j : Nat) : Int := (encodedNode j : Int) - (scale : Int)
def rationalNode (j : Nat) : ℚ := (integerNode j : ℚ) / (scale : ℚ)
def nodes : List ℚ := (List.range encoded.length).map rationalNode

theorem encoded_length : encoded.length = 2520 := by decide +kernel
theorem encoded_all_fit : encoded.all (fun x => decide (x < 2*scale)) = true := by
  decide +kernel
theorem encoded_fit (j : Fin 2520) : encodedNode j.val < 2*scale := by
  have hj : j.val < encoded.length := by simpa only [encoded_length] using j.isLt
  change encoded[j.val]?.getD scale < 2*scale
  rw [List.getElem?_eq_getElem hj]
  exact of_decide_eq_true ((List.all_eq_true.mp encoded_all_fit) _ (List.getElem_mem hj))
theorem mesh_positive : 0 < mesh := by decide

end RH080Next.WindowPV.Data
'''
    (HERE/'lean/WindowData.lean').write_text(data_source)
    previous = (OLD/'lean/DualExecution.lean').read_text()
    previous = previous.replace('import DualAST', 'import WindowAST')
    previous = previous.replace('namespace RH080PV.Execution', 'namespace RH080Next.WindowPV.Execution')
    previous = previous.replace('RH080PV.program', 'RH080Next.WindowPV.program')
    previous = previous.replace('set_option maxRecDepth 100000', 'set_option maxRecDepth 1000000')
    cut = previous.index('/-- This is a modeled execution claim')
    previous = previous[:cut]+'end RH080Next.WindowPV.Execution\n'
    (HERE/'lean/WindowExecution.lean').write_text(previous)
    print(json.dumps({'status':'GENERATED_UNTRUSTED_CANDIDATE_AST_AND_DATA_NOT_PROOF',
                      'functions':[name for name, _ in functions],
                      'physical_source_sha256':hashlib.sha256(raw).hexdigest(),
                      'physical_source_bytes':len(raw),
                      'parser_sha256':hashlib.sha256((OLD/'parse_source.py').read_bytes()).hexdigest()}))


if __name__ == '__main__':
    main()
