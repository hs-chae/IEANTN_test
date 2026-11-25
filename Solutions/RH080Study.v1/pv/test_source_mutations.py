#!/usr/bin/env python3
"""Kernel checks of actual C-source mutations against the unchanged parsed AST.

These are finite adversarial controls, not the general source-grammar soundness
proof. Each generated theorem is checked by the real Lean kernel, without native
execution axioms. Original source and accepted proof banks are never modified.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time


def need(ok, message):
    if not ok:
        raise ValueError(message)


def strict_json(raw):
    def pairs(items):
        out = {}
        for key, value in items:
            need(key not in out, "Duplicate JSON key")
            out[key] = value
        return out
    return json.loads(raw, object_pairs_hook=pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--context", type=Path, required=True)
    ap.add_argument("--run", type=Path, required=True)
    a = ap.parse_args()
    need(not a.run.exists(), "Fresh mutation run required")
    a.run.mkdir(parents=True)
    context = strict_json(a.context.read_bytes())
    here = Path(__file__).resolve().parent
    controller_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    compiler = Path(context["compiler"]).resolve(strict=True)
    pinned = strict_json((here.parent/"baseline/GENERIC_CONTEXT.json").read_bytes())
    compiler_hash = hashlib.sha256(compiler.read_bytes()).hexdigest()
    need(compiler_hash == pinned["compiler_sha256"], "Actual Lean compiler differs from pinned binary")
    original = (here/"dual_grid.c").read_bytes()
    text = original.decode("ascii")
    def replace(old, new):
        need(text.count(old) == 1, "Mutation trigger not unique: " + old)
        return text.replace(old, new).encode("ascii")
    variants = [
        ("leading_padding", b" \n"+original, True),
        ("trailing_comment", original+b"\n// extra mathematical source comment\n", True),
        ("changed_witness_jump", replace("837ULL", "838ULL"), False),
        ("changed_branch", replace("j == 4ULL", "j == 5ULL"), False),
        ("changed_sine_product", replace("(term * z)", "(term + z)"), False),
        ("changed_maximum_direction", replace("value > maximum", "value < maximum"), False),
        ("missing_grid_endpoint", replace("k <= 256ULL", "k < 256ULL"), False),
        ("wrong_main_call", replace("(unsigned long long)rh_dual_bound()",
                                    "(unsigned long long)sample_bound(0ULL)"), False),
        ("missing_output_newline", replace('"%llu\\n"', '"%llu"'), False),
        ("unsupported_macro", b"#define maximum value\n"+original, False),
    ]
    env = dict(os.environ, LEAN_PATH=context["LEAN_PATH"])
    rows = []
    for name, raw, accepted in variants:
        case = a.run/name; case.mkdir()
        (case/"source.c").write_bytes(raw)
        chars = ", ".join("Char.ofNat "+str(b) for b in raw)
        expectation = "true" if accepted else "false"
        lean = '''import DualSource
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RH080Mutation
def chars : List Char := ['''+chars+''']
def source : String := String.ofList chars
theorem checked : RH080PV.checkedSyntax source RH080PV.program = '''+expectation+''' := by
  simp only [RH080PV.checkedSyntax, GoldbachDirect.checkedSource,
    RH080PV.actual_ast_tokens, RH080PV.actual_ast_guard]
  unfold GoldbachDirect.tokenize GoldbachDirect.Correspondence.preprocessingAccepted
  simp only [source,String.toList_ofList,String.length_ofList]
  decide +kernel
#print axioms checked
end RH080Mutation
'''
        source = case/"Control.lean"; source.write_text(lean)
        command = ["prlimit", "--as="+str(16*2**30), "--", str(compiler), "-j2", str(source)]
        started = time.monotonic()
        result = subprocess.run(command, cwd=case, env=env, capture_output=True)
        (case/"stdout").write_bytes(result.stdout); (case/"stderr").write_bytes(result.stderr)
        need(result.returncode == 0, "Actual kernel mutation check failed: " + name)
        need(b"sorryAx" not in result.stdout and b"ofReduceBool" not in result.stdout,
             "Unverified execution fact in mutation control")
        rows.append(dict(name=name, expected_source_acceptance=accepted, returncode=result.returncode,
                         command=command, seconds=time.monotonic()-started,
                         C_source_sha256=hashlib.sha256(raw).hexdigest(),
                         Lean_source_sha256=hashlib.sha256(lean.encode()).hexdigest(),
                         stdout_sha256=hashlib.sha256(result.stdout).hexdigest(),
                         stderr_sha256=hashlib.sha256(result.stderr).hexdigest()))
    need((here/"dual_grid.c").read_bytes() == original, "Original C source changed")
    need(hashlib.sha256(Path(__file__).read_bytes()).hexdigest() == controller_hash,
         "Executing mutation controller changed")
    receipt = dict(status="PASS_TEN_ACTUAL_C_SOURCE_KERNEL_MUTATION_CONTROLS", rows=rows,
                   original_source_sha256=hashlib.sha256(original).hexdigest(),
                   compiler_sha256=compiler_hash,
                   controller_sha256=controller_hash,
                   python_optimization=sys.flags.optimize, general_soundness_proof_separate=True)
    fd, name = tempfile.mkstemp(dir=a.run, prefix=".acceptance-")
    temporary = Path(name)
    try:
        with os.fdopen(fd, "w") as out:
            json.dump(receipt, out, indent=2); out.write("\n"); out.flush(); os.fsync(out.fileno())
        os.link(temporary, a.run/"ACCEPTANCE.json")
    finally:
        temporary.unlink()
    print(json.dumps(dict(status=receipt["status"], cases=len(rows))))


if __name__ == "__main__":
    main()
