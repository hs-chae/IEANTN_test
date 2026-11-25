#!/usr/bin/env python3
"""Regenerate the fixed 129 rational rounding proofs, not a sine oracle."""
import argparse
from pathlib import Path

HEADER = """/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI (Codex)
-/
"""
OPTIONS = """set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RH080.SineBridge
"""


def outputs():
    result = {}
    for block in range(9):
        rows = []
        for r in range(16*block, min(16*(block+1), 129)):
            rows.append(f"theorem error{r:03d} : |(sineFixed {r} : ℚ)/1000000000 - polyQ ((3141592654*{r}/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by\n  norm_num [sineFixed, sineStep, polyQ, List.range_succ]\n")
        result[f"SineCells{block:02d}.lean"] = HEADER + "import SineSpec\n" + OPTIONS + "\n".join(rows) + "end RH080.SineBridge\n"
    imports = "\n".join(f"import SineCells{b:02d}" for b in range(9))
    statement = """
set_option autoImplicit false
set_option maxHeartbeats 0
namespace RH080.SineBridge
theorem rational_error (r : Fin 129) : |(sineFixed r.val : ℚ)/1000000000 - polyQ ((3141592654*r.val/256 : Nat)/1000000000 : ℚ)| ≤ 1/50000000 := by
  fin_cases r
"""
    statement += "".join(f"  · exact error{r:03d}\n" for r in range(129))
    statement += "end RH080.SineBridge\n#print axioms RH080.SineBridge.rational_error\n"
    result["SineRational.lean"] = HEADER + imports + statement
    return result


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument("--output", type=Path)
    p.add_argument("--check", action="store_true")
    a = p.parse_args()
    directory = a.output or Path(__file__).resolve().parent
    if a.check:
        for name, text in outputs().items():
            if (directory/name).read_bytes() != text.encode():
                raise ValueError("Generated source differs: " + name)
        print("PASS_TEN_GENERATED_SOURCES_BYTE_IDENTICAL_NOT_PROOF_ACCEPTANCE")
        return
    if a.output is None or directory.exists():
        raise ValueError("Fresh explicit output directory required")
    directory.mkdir(parents=True)
    for name, text in outputs().items():
        (directory/name).write_text(text)


if __name__ == "__main__":
    main()
