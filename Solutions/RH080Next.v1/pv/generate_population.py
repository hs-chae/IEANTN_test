#!/usr/bin/env python3
"""Untrusted candidate frontend for a source-computed periodic norm enclosure.
Input is the unchanged exact 16-node population witness; output is not embedded.
Lean checks independently specified syntax, and checked C execution separately.
"""
import hashlib,importlib.util,json,re
from pathlib import Path
import sys
sys.dont_write_bytecode = True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
OLD=ROOT/'Solutions/RH080Study.v1/pv'
HEADER='''/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
'''
def main():
    data=json.loads((HERE/'population_m8_r2.json').read_text())
    if data['m']!=8 or data['scale']!=10**18 or len(data['coefficients'])!=16 or min(data['coefficients'])<0:
        raise ValueError('Unexpected fixed mathematical input')
    selector='\n'.join('  if (j == %dULL) { return %dULL; }'%(j,a) for j,a in enumerate(data['coefficients'])if a)
    old=(OLD/'dual_grid.c').read_text();sine=old[old.index('uint64_t sine_fixed'):old.index('uint64_t sample_bound')]
    source='''/* Copyright (c) 2026 IEANTN contributors. Apache-2.0. */
#include <stdint.h>
#include <stdio.h>

uint64_t coefficient(uint64_t j) {
'''+selector+'''
  return 0ULL;
}

'''+sine+'''uint64_t coefficient_times_sine(uint64_t a, uint64_t s) {
  uint64_t high = (a / 1000000000ULL);
  uint64_t low = (a % 1000000000ULL);
  return ((high * s) + ((low * s) / 1000000000ULL));
}

uint64_t sample_upper(uint64_t k) {
  uint64_t positive = 0ULL;
  uint64_t negative = 0ULL;
  uint64_t j = 0ULL;
  while (j < 16ULL) {
    uint64_t a = coefficient(j);
    if (a > 0ULL) {
      uint64_t r = ((((2ULL * j) * k) + 128ULL) % 512ULL);
      uint64_t flipped = 0ULL;
      if (r > 256ULL) { r = (512ULL - r); flipped = 1ULL; }
      if (r > 128ULL) { r = (256ULL - r); }
      uint64_t s = sine_fixed(r);
      uint64_t term = coefficient_times_sine(a, s);
      if (j > 0ULL) { term = (2ULL * term); }
      if (flipped == 0ULL) { positive = (positive + term); }
      else { negative = (negative + term); }
    }
    j = (j + 1ULL);
  }
  uint64_t absolute = 0ULL;
  if (positive >= negative) { absolute = (positive - negative); }
  else { absolute = (negative - positive); }
  return (absolute + 100000000000000ULL);
}

uint64_t chord_upper(void) {
  uint64_t sum = 0ULL;
  uint64_t j = 0ULL;
  while (j < 16ULL) {
    uint64_t a = coefficient(j);
    uint64_t factor = ((20ULL * j) * j);
    uint64_t high = (a / 196608ULL);
    uint64_t low = (a % 196608ULL);
    uint64_t term = ((high * factor) + ((((low * factor) + 196608ULL) - 1ULL) / 196608ULL));
    sum = (sum + term);
    j = (j + 1ULL);
  }
  return sum;
}

uint64_t population_norm_upper(void) {
  uint64_t sum = 0ULL;
  uint64_t k = 0ULL;
  while (k < 256ULL) {
    uint64_t value = sample_upper(k);
    sum = (sum + ((value + 255ULL) / 256ULL));
    k = (k + 1ULL);
  }
  return (sum + chord_upper());
}

int main(void) {
  printf("%llu\\n", (unsigned long long)population_norm_upper());
  return 0;
}
'''
    (HERE/'population_norm.c').write_text(source)
    spec=importlib.util.spec_from_file_location('old_untrusted_parser',OLD/'parse_source.py');parser=importlib.util.module_from_spec(spec);spec.loader.exec_module(parser)
    fs=parser.Parser(source).functions()
    prefix=HEADER+'''import GoldbachDirect.Correspondence.Specification
set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace RH080Next.PopulationPV
open GoldbachDirect
'''
    ast='\n'.join('def '+n+'_ast : Function :=\n  '+term+'\n'for n,term in fs)
    ast+='\ndef program : Program := ['+', '.join(['.include .stdint','.include .stdio']+['.function '+n+'_ast'for n,_ in fs])+']\n'
    (HERE/'lean/PopulationAST.lean').write_text(prefix+ast+'\nend RH080Next.PopulationPV\n')
    template=(HERE/'lean/WindowSource.lean').read_text();template=template[template.index('def checkedSyntax'):]
    template=template.replace('RH080Next.WindowPV','RH080Next.PopulationPV')
    a=template.index('theorem actual_ast_tokens');b=template.index('theorem actual_ast_guard',a)
    proof="""theorem actual_ast_tokens : program.tokens = expectedTokens := by
  simp (config := { maxSteps := 10000000 }) only [program, Program.tokens, Top.tokens, Function.tokens,
    """+', '.join(n+'_ast' for n,_ in fs)+""",
    Stmt.tokens, Expr.tokens, Literal.tokens, CType.tokens, Binary.token,
    comma, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
    List.nil_append, List.append_nil]
  decide +kernel

"""
    template=template[:a]+proof+template[b:]
    raw=source.encode('ascii');chars=', '.join('Char.ofNat '+str(x)for x in raw)
    ts=re.findall(r'"(?:[^"\\]|\\.)*"|[A-Za-z0-9_]+|==|!=|<=|>=|&&|\|\||[^\s]',re.sub(r'/\*.*?\*/','',source,flags=re.S))
    src='def sourceChars : List Char := ['+chars+']\ndef source : String := String.ofList sourceChars\ndef expectedTokens : List String := '+json.dumps(ts)+'\n'
    (HERE/'lean/PopulationSource.lean').write_text(prefix.replace('import GoldbachDirect.Correspondence.Specification','import PopulationAST')+src+template)
    execution=(HERE/'lean/WindowExecution.lean').read_text().replace('WindowAST','PopulationAST').replace('RH080Next.WindowPV','RH080Next.PopulationPV')
    (HERE/'lean/PopulationExecution.lean').write_text(execution)
    print(json.dumps({'source_sha256':hashlib.sha256(raw).hexdigest(),'bytes':len(raw),'functions':len(fs),'input_sha256':hashlib.sha256((HERE/'population_m8_r2.json').read_bytes()).hexdigest()}))
if __name__=='__main__':main()
