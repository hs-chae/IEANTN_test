#!/usr/bin/env python3
"""Strict readback of a completed fresh source-first dual execution study.

Checks consistency and complete source/object/audit/C-output association. It is
not an authenticity signature and does not replace fresh Lean compilation.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import tempfile


def need(ok, message):
    if not ok:
        raise ValueError(message)


def pairs(items):
    out = {}
    for key, value in items:
        need(key not in out, "Duplicate JSON key")
        out[key] = value
    return out


def read(path):
    return json.loads(path.read_bytes(), object_pairs_hook=pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))


def sha(path):
    need(path.is_file() and not path.is_symlink(), "Missing/aliased evidence file")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--run", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True)
    a = ap.parse_args()
    need(not a.output.exists(), "Fresh acceptance output required")
    root = a.run.resolve(strict=True)
    result = read(root/"RESULT.json")
    need(result["status"] == "PASS_FRESH_COMPLETE_SOURCE_FIRST_DUAL_PROGRAM_AND_FULL_MATHEMATICAL_CONSUMER",
         "Incomplete actual producer status")
    need(result["source_first_PV"] is True and result["predecessor_application_objects_used"] is False,
         "Wrong source-first/application reuse boundary")
    plan = read(root/"PLAN.json")
    need(sha(root/"PLAN.json") == result["PLAN_sha256"], "Plan changed")
    need(sha(root/"reproduce_joint.executed.py") == plan["controller_sha256"], "Executed controller differs")
    need(plan["predecessor_application_objects_used"] is False and plan["heavy_serialized"] is True,
         "Wrong fresh/serialized resource policy")
    need(plan["heavy_execution_AS_bytes"] == 256*2**30 and
         plan["per_normal_process_AS_bytes"] == 64*2**30, "Resource policy differs")
    count = result["modules"]
    need(type(count) is int and count == 45, "Wrong selected source population")
    builds = {r["module"]: r for r in result["builds"]}
    modules = {r["module"]: r for r in plan["modules"]}
    need(len(builds) == len(result["builds"]) == len(modules) == len(plan["modules"]) == count,
         "Duplicate/incomplete module identities")
    need(set(builds) == set(modules), "Source/build population differs")
    need(plan["roots"] == ["PVJointAudit"], "Wrong final proof root")
    for required in ["PVJointAudit", "DualActualRun", "DualSource", "DualOutput", "DualVerifiedSource",
                     "CompactDualSourceFirst", "DualSineExecution", "SineBridge", "FourierWeakDuality"]:
        need(required in modules, "Required final provider omitted: " + required)
    for name, item in modules.items():
        need(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", name),
             "Invalid module identity")
        source = root/"source"/(name.replace(".","/")+".lean")
        need(Path(item["executed"]) == source and source.resolve().is_relative_to(root),
             "Executed source association differs")
        row = builds[name]
        need(row["returncode"] == 0, "Failed compiler in accepted build")
        need(sha(source) == item["source_sha256"] == row["source_sha256"], "Executed source changed")
        obj = root/"objects"/(name.replace(".","/")+".olean")
        need(sha(obj) == row["object_sha256"], "Accepted object changed")
        stem = name.replace(".", "_")
        for suffix, key in [("stdout","stdout_sha256"),("stderr","stderr_sha256"),("time","time_sha256")]:
            need(sha(root/"logs"/(stem+"."+suffix)) == row[key], "Compiler/audit log changed")
        expected_cap = (256 if name == "DualActualRun" else 64)*2**30
        need(row["AS_cap_bytes"] == expected_cap, "Actual compiler resource cap differs")
        command = row["command"]
        need(command[-1] == str(source) and "-j2" in command and str(obj) in command
             and "--as="+str(expected_cap) in command, "Compiler invocation association differs")
    # Reconstruct the actual import closure independently of the producer's list.
    # A matching count or selected headline names cannot establish coverage.
    generic = ("Mathlib", "Lean", "Init", "Std", "Aesop", "Batteries", "Qq", "ProofWidgets")
    visited, active = set(), set()
    def visit(name):
        if name in visited:
            return
        if name not in modules:
            need(any(name == p or name.startswith(p+".") for p in generic),
                 "Missing application proof provider: " + name)
            return
        need(name not in active, "Cyclic actual source import closure")
        active.add(name)
        source = root/"source"/(name.replace(".","/")+".lean")
        imports = []
        for line in source.read_text().splitlines():
            if line.startswith("import "):
                imports.extend(line[7:].split("--",1)[0].split())
        need(imports == modules[name]["imports"], "Recorded imports differ from source")
        for dependency in imports:
            visit(dependency)
        active.remove(name); visited.add(name)
    visit("PVJointAudit")
    need(visited == set(modules), "Listed providers differ from actual final source closure")
    audit = root/"logs/PVJointAudit.stdout"
    need(sha(audit) == result["audit_stdout_sha256"], "Final audit differs")
    text = audit.read_text()
    need("PV_JOINT_AUDIT_PASS roots=13 edges=11 no-native no-sorry no-D-cap-shortcut" in text,
         "Actual complete source/axiom/value audit marker absent")
    need(text.count("PV_AXIOMS ") == 13 and text.count("PV_EDGE ") == 11 and
         text.count("PV_CLOSURE_SOURCE_EXECUTION_CONSUMED ") == 2, "Incomplete actual audit coverage")
    need("sorryAx" not in text and "ofReduceBool" not in text, "Unverified axiom in audit")
    source = root/"source-generator/dual_grid.c"
    need(sha(source) == result["actual_C_source_sha256"] == sha(root/"native/dual_grid.c"),
         "Numerical C source association differs")
    formal = (root/"source/DualSource.lean").read_text()
    section = formal.split("def sourceChars : List Char := [",1)[1].split("]",1)[0]
    represented = bytes(int(n) for n in re.findall(r"Char.ofNat ([0-9]+)", section))
    need(represented == source.read_bytes(), "Formal C source characters differ from actual C bytes")
    for name in ["DualAST.lean","DualSource.lean"]:
        need((root/"source-generator/lean"/name).read_bytes() == (root/"source"/name).read_bytes(),
             "Regenerated frontend differs")
    need(sha(root/"native/dual_grid") == result["executable_sha256"], "Executed C binary changed")
    need(sha(root/"native/stdout") == result["stdout_sha256"] and
         (root/"native/stdout").read_bytes() == b"1221161\n", "Actual C stdout differs from proved bytes")
    need(not (root/"native/stderr").read_bytes() and result["execution_returncode"] == 0
         and result["C_compile_returncode"] == 0, "Actual C compilation/execution failed")
    receipt = dict(status="PASS_COMPLETE_JOINT_SOURCE_OBJECT_VALUE_AXIOM_AND_NATIVE_OUTPUT_READBACK",
                   modules=count, source_first_PV=True, result_sha256=sha(root/"RESULT.json"),
                   plan_sha256=sha(root/"PLAN.json"), audit_sha256=sha(audit),
                   C_source_sha256=sha(source), actual_stdout_sha256=sha(root/"native/stdout"),
                   complete_fresh_producer_required=True,
                   canonical_IEANTN_integration="Separate focused compile/audit phase; this source-only mathematical replay does not claim that future canonical faces were already included.",
                   limitations="Consistency readback, not a signature or a replacement for the source-only compilation. Standard generic infrastructure/compiler/runtime/OS/hardware boundaries remain. Mathematical obstruction is for the specified L1 Fourier fragment; main output is conditional on performed successful I/O and independently recorded actual capture.")
    a.output.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary_name = tempfile.mkstemp(prefix=".joint-acceptance-", dir=a.output.parent)
    temporary = Path(temporary_name)
    try:
        with os.fdopen(fd,"w") as out:
            json.dump(receipt,out,indent=2); out.write("\n"); out.flush(); os.fsync(out.fileno())
        os.link(temporary,a.output)
    finally:
        temporary.unlink()
    print(json.dumps(dict(status=receipt["status"], modules=count)))


if __name__ == "__main__":
    main()
