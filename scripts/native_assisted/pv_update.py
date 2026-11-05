#!/usr/bin/env python3
"""Opt-in update workflow for a program-verified numerical provider (local, non-official).

A provider is registered in `scripts/native_assisted/providers.json`: its node conclusion, its
family (the shape of its selected program and of its mathematics), its parameters, its selected
C file, its Lean provider module and the gate endpoint that audits it. An update is a new entry
with `updated_from` naming the old provider and only the changed parameters.

    python scripts/native_assisted/pv_update.py plan     <conclusion>   # old vs new, consumers
    python scripts/native_assisted/pv_update.py generate <conclusion>   # C file + Lean data module
    python scripts/native_assisted/pv_update.py build    <conclusion>   # lake build (input_file aware)
    python scripts/native_assisted/pv_update.py gate     <conclusion>   # native-assisted gate
    python scripts/native_assisted/pv_update.py all      <conclusion>

What it does not do: it never writes a node statement, a justification, a receipt or an
attestation by hand. The statement in `Conclusions.lean` is the contributor's; the generated Lean
module only type-checks if that statement is what the family theorem proves. `gate` runs the real
checker, which builds and elaborates the proof. A changed C file or literal list is rebuilt
because the generated lakefile declares the C file as an `input_file` that the provider library
`needs` (Lake does not otherwise track `include_str`).

Families implemented: `ramanujan-budget` (selected wrapper `ramanujan_epsilon_bound`, family
theorem `PVRamanujan.budget_of_check`). Table 4 instances use the shared contract through
`PVTable4`, but their literals come from analytic enclosures that are not generated here.
"""
from __future__ import annotations

import hashlib
import importlib.util
import json
import pathlib
import struct
import subprocess
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
REGISTRY = HERE / "providers.json"
U = F(1, 2 ** 53)
LOW = F(1, 2 ** 40)


def frozen_generator():
    """The frozen Ramanujan generator, imported (not copied) for its exact `literal`/`upward`."""
    spec = importlib.util.spec_from_file_location(
        "frozen_generate", ROOT / "Solutions/RamanujanNumerics.v1/generate.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def registry() -> dict:
    return json.loads(REGISTRY.read_text())


#: Where an entry's files are. An update must name its own: inheriting them from `updated_from`
#: would make `generate` overwrite the old provider's selected file, module and lakefile.
LOCATION_KEYS = ("project", "source", "lean_lib", "lean_module", "gate_endpoint")


def entry(conclusion: str) -> dict:
    providers = registry()["providers"]
    if conclusion not in providers:
        raise SystemExit(f"{conclusion}: not registered in {REGISTRY.relative_to(ROOT)}")
    e = dict(providers[conclusion])
    base = e.get("updated_from")
    if base:
        missing = [k for k in LOCATION_KEYS if k not in e]
        if missing:
            raise SystemExit(f"{conclusion}: an update must name its own {', '.join(missing)}; "
                             f"inheriting them from {base} would overwrite its files")
        shared = [k for k in ("project", "source") if e[k] == providers[base].get(k)]
        if shared:
            raise SystemExit(f"{conclusion}: {', '.join(shared)} equal {base}'s; an update writes "
                             "a new provider, never over the old one")
        merged = dict(providers[base])
        merged["parameters"] = {**providers[base].get("parameters", {}), **e.get("parameters", {})}
        merged.update({k: v for k, v in e.items() if k != "parameters"})
        for k in ("allowance_def", "note", "math_inputs"):
            if k not in e:
                merged.pop(k, None)
        e = merged
    e["conclusion"] = conclusion
    return e


def q(s: str) -> F:
    return F(s)


# ------------------------------------------------------------------ the ramanujan-budget family

def ramanujan_values(e: dict) -> dict:
    """Exact data of one instance. Python floats are IEEE binary64 with round-to-nearest, so the
    run below is a diagnostic replay of the C program; Lean re-derives every value."""
    g = frozen_generator()
    p = e["parameters"]
    m, M, A, Y = (q(p[k]) for k in ("m", "M", "A", "Y"))
    n = int(p.get("groups", 7))
    targets = [2 * M, (2 * M + 132) / Y, (4 * M + 288) / Y ** 2, (12 * M + 576) / Y ** 3,
               48 * M / Y ** 4, M ** 2 / Y ** 5, max(F(0), -m) * (1 + 1 / A) ** 6]
    groups = [sum(targets[(7 * j) // n:(7 * (j + 1)) // n], F()) for j in range(n)]
    vals = [g.upward(max(v / F(4096), LOW)) for v in groups]
    if any(not LOW <= v <= 1 for v in vals):
        raise SystemExit("unsupported input range: every literal must lie in [2^-40, 1]")
    positive = max(F(0), m)
    s = 0.0
    for v in vals:
        s = s + float(v)
    r0 = s * 4096.0
    r1 = r0 - 134.0
    out = r1 - float(positive)
    if not (out > 0 and r1 > 0 and r0 > 0):
        raise SystemExit("an intermediate is not a positive normal value; the shared certificate "
                         "(FKS2Table4.additionCheck) does not cover it, so the instance would fail")
    S, OUT = F(s), F(out)
    k = n - 1
    gamma = k * U / (1 - k * U)
    eps = q(e.get("suffix_eps", "1/10000000000"))
    exact_at_s = 4096 * S - 134 - positive
    if abs(OUT - exact_at_s) > eps:
        raise SystemExit(f"suffix rounding error {float(abs(OUT - exact_at_s)):.3e} exceeds eps")
    fe = 4096 * (S / (1 - gamma) - S) + eps
    return {"targets": targets, "literals": [g.literal(v) for v in vals], "values": vals,
            "positive": positive, "sum": S, "out": OUT, "forward_error": fe,
            "certified_upper": OUT + fe,
            "out_bits": hex(struct.unpack(">Q", struct.pack(">d", out))[0])}


def c_source(e: dict, lits: list[str], positive: F) -> str:
    """The frozen generator's layout, so a regenerated file differs only in its data."""
    g = frozen_generator()
    n = len(lits)
    prefix = ("double sum(const double *a, unsigned n) {\n    double s = 0.0;\n"
              "    for (unsigned i = 0; i < n; ++i) {\n        s += a[i];\n    }\n    return s;\n}\n")
    return (prefix + "\nstatic const double inputs[" + str(n) + "] = {\n    " +
            ",\n    ".join(lits) + "\n};\ndouble ramanujan_epsilon_bound(void) {\n"
            "    double s = sum(inputs, " + str(n) + ");\n    double r = (s * 4096.0);\n"
            "    r = (r - 134.0);\n    r = (r - " + g.literal(positive) + ");\n    return r;\n}\n")


def lean_rat(x: F) -> str:
    return str(x.numerator) if x.denominator == 1 else f"({x.numerator} / {x.denominator})"


def lean_module(e: dict, lits: list[str], positive: F) -> str:
    g = frozen_generator()
    p = e["parameters"]
    m, M, A, Y = (q(p[k]) for k in ("m", "M", "A", "Y"))
    node, cid = e["conclusion"].rsplit(".", 1)
    lit_lines = ",\n    ".join(f'"{s}"' for s in lits)
    src_rel = pathlib.Path(e["source"]).relative_to(pathlib.Path(e["project"]))
    parts = " / ".join(f'"{x}"' for x in (("..",) + src_rel.parts))
    return f"""/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude), generated by scripts/native_assisted/pv_update.py
-/
import PVRamanujan.Family
import IEANTN.Nodes.{node}.Conclusions

/-!
# Provider data for `{e['conclusion']}` (generated)

Family `ramanujan-budget`, parameters `(m, M, A, Y) = ({p['m']}, {p['M']}, {p['A']}, {p['Y']})`,
{len(lits)} array entries. Generated from `scripts/native_assisted/providers.json`; regenerate with
`pv_update.py generate {e['conclusion']}`. Hand edits are overwritten.

This module holds data and one certificate. The proof is the shared family theorem
`PVRamanujan.budget_of_check`; nothing here restates execution, rounding or summation lemmas.
-/

namespace {node}.Provider

open Real PVCore

/-- The array literals of the selected file: each is the least binary64 value at or above the
corresponding term divided by 4096 (and at least `2⁻⁴⁰`). -/
def literals : List String := [
    {lit_lines}]

def program : Program := PVRamanujan.program literals "4096.0" "134.0" "{g.literal(positive)}"

/-- The selected C file, read at elaboration time. Its lakefile declares it as an `input_file`
that this library `needs`, so editing it forces a rebuild. -/
def source : String := include_str {parts}

/-- The one finite certificate of this provider. -/
theorem certificate :
    PVRamanujan.budgetCheck source program {lean_rat(m)} {lean_rat(M)} {lean_rat(A)} {lean_rat(Y)}
      ({e.get('suffix_eps', '1/10000000000').replace('/', ' / ')}) {lean_rat(q(e['bound']))} = true := by
  native_decide

/-- `{e['conclusion']}`, from the certificate and the family theorem. -/
theorem {cid} : {e['conclusion']} := by
  intro x hx
  have h := PVRamanujan.budget_of_check certificate x (by simpa using hx)
  have hb : (({lean_rat(q(e['bound']))} : ℚ) : ℝ) = {e.get('allowance_def', node + '.allowance')} := by
    norm_num [{e.get('allowance_def', node + '.allowance')}]
  rw [hb] at h
  simpa using h

end {node}.Provider
"""


def lakefile(e: dict) -> str:
    src_rel = pathlib.Path(e["source"]).relative_to(pathlib.Path(e["project"]))
    node = e["conclusion"].rsplit(".", 1)[0]
    pkg = "solution_" + node.replace(".", "_")
    return f"""name = "{pkg}"
version = "0.1.0"
defaultTargets = ["Solution"]

# Generated by scripts/native_assisted/pv_update.py for the {e['family']} family.
[[require]]
name = "IEANTN"
path = "../.."

[[require]]
name = "solution_ProgramVerification"
path = "../ProgramVerification"

# The selected C file is embedded by `include_str`, which Lake does not track. Declaring it as an
# input file that the provider library needs makes a changed file rebuild the provider.
[[input_file]]
name = "selected_source"
path = "{src_rel.as_posix()}"
text = true

[[lean_lib]]
name = "{e['lean_lib']}"
needs = ["selected_source"]

[[lean_lib]]
name = "Solution"
roots = ["Solution"]
"""


# ------------------------------------------------------------------ commands

def consumers_of(conclusion: str) -> list[str]:
    import yaml
    out = []
    for y in sorted((ROOT / "IEANTN/Nodes").glob("*/*/formalization.yaml")):
        d = yaml.safe_load(y.read_text())
        nid = d["node"]["id"]
        for c in d.get("conclusions") or []:
            for imp in c.get("imports") or []:
                if f"{imp.get('node')}.{imp.get('conclusion')}" == conclusion:
                    out.append(f"{nid}.{c['id']}")
    return out


def plan(conclusion: str) -> int:
    e = entry(conclusion)
    reg = registry()["providers"]
    base = reg[conclusion].get("updated_from")
    print(f"provider   {conclusion}  family={e['family']}")
    if base:
        old = reg[base]
        print(f"updated from {base}")
        for k, v in e["parameters"].items():
            ov = old.get("parameters", {}).get(k)
            mark = "  (changed)" if str(ov) != str(v) else ""
            print(f"  {k:8} {ov!s:>10} -> {v!s:<10}{mark}")
        print(f"  source   {old['source']} -> {e['source']}")
    v = ramanujan_values(e)
    print(f"array entries {len(v['literals'])}; output {float(v['out']):.10f}; "
          f"proved error {float(v['forward_error']):.3e}; certified upper {float(v['certified_upper']):.10f}")
    b = q(e["bound"]) if e.get("bound") else None
    print(f"statement bound {e.get('bound')} -> " + ("OK" if b is not None and v["certified_upper"] <= b
                                                   else "NOT met (choose a bound >= certified upper)"))
    print("consumers of the old conclusion:", ", ".join(consumers_of(base)) if base else "-")
    print("consumers of the new conclusion:", ", ".join(consumers_of(conclusion)) or "none yet")
    print("regenerates:", e["source"], "and", e["project"] + "/" + e["lean_module"])
    return 0


def generate(conclusion: str) -> int:
    e = entry(conclusion)
    v = ramanujan_values(e)
    if not e.get("bound") or v["certified_upper"] > q(e["bound"]):
        raise SystemExit("bound missing or below the certified upper value; run `plan`")
    proj = ROOT / e["project"]
    (proj / pathlib.Path(e["source"]).relative_to(e["project"])).parent.mkdir(parents=True, exist_ok=True)
    src = ROOT / e["source"]
    src.write_text(c_source(e, v["literals"], v["positive"]))
    mod = proj / e["lean_module"]
    mod.parent.mkdir(parents=True, exist_ok=True)
    mod.write_text(lean_module(e, v["literals"], v["positive"]))
    (proj / "lakefile.toml").write_text(lakefile(e))
    lib_root = proj / f"{e['lean_lib']}.lean"
    lib_root.write_text(f"import {e['lean_module'][:-len('.lean')].replace('/', '.')}\n")
    lock = {"conclusion": conclusion, "family": e["family"], "parameters": e["parameters"],
            "bound": e["bound"], "source": e["source"],
            "source_sha256": hashlib.sha256(src.read_bytes()).hexdigest(),
            "lean_module": e["project"] + "/" + e["lean_module"],
            "lean_module_sha256": hashlib.sha256(mod.read_bytes()).hexdigest(),
            "array_entries": len(v["literals"]), "diagnostic_output_bits": v["out_bits"],
            "diagnostic_certified_upper": str(v["certified_upper"])}
    (proj / "pv-provider.lock.json").write_text(json.dumps(lock, indent=1) + "\n")
    print(f"wrote {e['source']}, {e['project']}/{e['lean_module']}, lakefile.toml, pv-provider.lock.json")
    return 0


def build(conclusion: str) -> int:
    e = entry(conclusion)
    proj = ROOT / e["project"]
    r = subprocess.run(["lake", "build", "Solution"], cwd=proj, capture_output=True, text=True)
    print((r.stdout + r.stderr)[-1500:])
    return r.returncode


def gate(conclusion: str) -> int:
    e = entry(conclusion)
    return subprocess.run([sys.executable, str(HERE / "native_assisted_check.py"), "check",
                           e["gate_endpoint"]], cwd=ROOT).returncode


def main(argv: list[str]) -> int:
    if len(argv) != 3 or argv[1] not in ("plan", "generate", "build", "gate", "all"):
        print(__doc__)
        return 2
    cmd, c = argv[1], argv[2]
    if cmd == "all":
        for f in (plan, generate, build, gate):
            rc = f(c)
            if rc:
                return rc
        return 0
    return {"plan": plan, "generate": generate, "build": build, "gate": gate}[cmd](c)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
