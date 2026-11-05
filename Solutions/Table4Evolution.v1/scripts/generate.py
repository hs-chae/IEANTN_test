#!/usr/bin/env python3
"""Generate the Table 4 transport programs for chosen partitions of [300, 330] (untrusted helper).

    python scripts/generate.py            # write every configuration below
    python scripts/generate.py --check    # recompute and compare with the files on disk

For each configuration the script computes, in exact rational arithmetic and with the same
definitions as `Table4Evolution.Bounds` (`expPoly`, `gridDown`, `expLo`, `expHi`, `cellA`, `cellB`,
`cellHi`), the upper bound of every cell, rounds `2^k · bound` up to binary64 with the frozen
generator's `upward`, and writes:

* `c/<name>.c`: the frozen `sum` function and a wrapper of the `PVCore.Program` shape (or the
  `PVCore.ChunkedProgram` shape for more than 64 cells);
* `Table4Evolution/Data/<Name>.lean`: the boundaries and the literal strings.

Nothing here is trusted: Lean decodes the literals from the C file, re-evaluates every certificate
and proves the bounds. A wrong or stale literal makes the Lean build fail.
"""
from __future__ import annotations

import importlib.util
import math
import pathlib
import sys
from fractions import Fraction as F

HERE = pathlib.Path(__file__).resolve().parent
PROJECT = HERE.parent
ROOT = PROJECT.parent.parent
TABLE4 = ROOT / "Solutions" / "FKS2Numerics.v5" / "c" / "fks2_table4_transport.c"


def frozen():
    spec = importlib.util.spec_from_file_location(
        "frozen_generate", ROOT / "Solutions/RamanujanNumerics.v1/generate.py")
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


G = frozen()

# ---- the Lean definitions, exactly -------------------------------------------------------------
FACT = [math.factorial(k) for k in range(19)]


def exp_poly(x: F) -> F:
    y = x / 32
    return sum((y ** k / FACT[k] for k in range(19)), F(0))


def grid_down(x: F) -> F:
    return F(math.floor(x * 10 ** 18), 10 ** 18)


def exp_lo(x: F) -> F:
    return grid_down((exp_poly(x) - F(1, 10 ** 16)) ** 32)


def exp_hi(x: F) -> F:
    return grid_down((exp_poly(x) + F(1, 10 ** 16)) ** 32) + F(1, 10 ** 18)


def cell_a(s: F, lo: F, hi: F) -> F:
    return (hi - s * lo - 330) / 4


def cell_b(s: F, lo: F) -> F:
    return ((1 - s) * lo - 330) / 4


def cell_hi(s: F, m: F, lo: F, hi: F) -> F:
    return (330 * m / lo ** 2) * (exp_hi(cell_a(s, lo, hi)) ** 4 - exp_lo(cell_b(s, lo)) ** 4)


# ---- profiles ----------------------------------------------------------------------------------
def m_qrh(lo: F) -> F:
    return lo ** 2 / 283


def m_step(lo: F) -> F:
    if lo < 310:
        return F("1.6930e-12")
    if lo < 320:
        return F("1.6882e-12")
    if lo < 330:
        return F("1.6837e-12")
    return F("1.6795e-12")


K_AGENT_A = F("0.009782") + F(1, 10 ** 12)


def m_agent_a(lo: F) -> F:
    return K_AGENT_A


# ---- the constant literals of the existing programs (anchor, point, tail; scale) ---------------
QRH_CONST = {  # FKS2Table4.selected (FKS2Numerics.v5)
    "scale": "0.0000000000000000034694469519536141888238489627838134765625",
    "anchor": "0.00000000000000000000000017665089669250357659020871109627738508254054851897432852679253658940809745825362142568337731063365936279296875",
    "point": "0.0000000000000004683753925250112014211433790943236597355769056105767589315291843377053737640380859375",
    "tail": "0.000000000000000001427973757698204816618073176699030809477512038595703632026800988796821911819279193878173828125",
}
OLD_CONST = {  # FKS2Pair.Old.oldProgram (FKS2Numerics.v6)
    "scale": "0.000000000000003552713678800500929355621337890625",
    "anchor": "0.0000000000000000000000003492236819106224570749842044323542651977040183691099386744583195981046774836187296386924572288990020751953125",
    "point": "0.00000000000167950000000000006325582692276102616938705802684950185721390880644321441650390625",
    "tail": "0.0000000000000051204268292682928950204700138082945508563614302188771176815862418152391910552978515625",
}


def agent_a_const() -> dict:
    """Upper bounds of the anchor, point and tail for the profile `K·e^{-L/8}` (see `AgentA.lean`)."""
    k = 75
    point = K_AGENT_A * exp_hi(F(-330, 32)) ** 4            # K·e^{-330/8}
    tail = point / 328
    u0 = K_AGENT_A * exp_hi(F(-300, 32)) ** 4               # K·e^{-300/8}
    anchor = F(330, 300) * exp_hi(F(-15)) ** 2 * (F("1.6997e-12") + u0)
    lit = lambda q: G.literal(G.upward(q))
    return {"k": k, "scale": G.literal(F(1, 2 ** k)), "anchor": lit(anchor), "point": lit(point),
            "tail": lit(tail), "pointHi": point, "anchorHi": anchor}


def frange(a: F, b: F, step: F) -> list[F]:
    out, x = [], a
    while x < b:
        out.append(x)
        x += step
    return out + [b]


CONFIGS = [
    # name, Lean namespace, profile (s, m), boundaries, scale exponent k, constants, target
    dict(name="qrh_trunc2", ns="QRHTrunc", s=F(1, 8), m=m_qrh, bs=[F(300), F(329), F(330)], k=58,
         const=QRH_CONST, target=F(5, 10 ** 16)),
    dict(name="old_trunc3", ns="OldTrunc", s=F(0), m=m_step, bs=[F(300), F(328), F(329), F(330)],
         k=48, const=OLD_CONST, target=F(169, 10 ** 14)),
    dict(name="qrh_quarter120", ns="QRHQuarter", s=F(1, 8), m=m_qrh,
         bs=frange(F(300), F(330), F(1, 4)), k=60, const=QRH_CONST, target=None),
    dict(name="agentA_trunc4", ns="AgentATrunc", s=F(1, 8), m=m_agent_a,
         bs=[F(300), F(327), F(328), F(329), F(330)], k=75, const=None, target=None),
]


def frozen_sum_text() -> str:
    text = TABLE4.read_text()
    end = text.index("}\n", text.index("return s;")) + 2
    return text[:end]


def render_single(fn: str, lits: list[str], scale: str, ops: list[tuple[str, str]]) -> str:
    body = [f"    double s = sum(inputs, {len(lits)});", f"    double r = (s * {scale});"]
    body += [f"    r = (r {sign} {c});" for sign, c in ops]
    body.append("    return r;")
    return (frozen_sum_text() + f"\nstatic const double inputs[{len(lits)}] = {{\n    " +
            ",\n    ".join(lits) + "\n};\n" + f"double {fn}(void) {{\n" + "\n".join(body) + "\n}\n")


def render_chunked(fn: str, chunks: list[list[str]], scale: str, ops: list[tuple[str, str]]) -> str:
    sys.path.insert(0, str(ROOT / "scripts" / "native_assisted"))
    import pv_chunked  # noqa: E402  (the chunked token shape of PVCore.renderChunked)
    return pv_chunked.render(fn, chunks, scale, ops)


def lean_rat(q: F) -> str:
    return f"({q.numerator} : ℚ)" if q.denominator == 1 else f"(({q.numerator} : ℚ) / {q.denominator})"


LOW = F(1, 2 ** 40)  # FKS2SumBridge.low: the frozen sum's inputs must lie in [2^-40, 1]


def scale_exponent(his: list[F]) -> int:
    """The largest k with every 2^k·cellHi ≤ 1 after upward rounding (the input range of `sum`)."""
    k = 0
    while all(G.upward(F(2) ** (k + 1) * h) <= 1 for h in his):
        k += 1
    while any(G.upward(F(2) ** k * h) > 1 for h in his):
        k -= 1
    return k


def build(cfg: dict) -> dict:
    s, m, bs = cfg["s"], cfg["m"], cfg["bs"]
    const = cfg["const"] or agent_a_const()
    his = [cell_hi(s, m(lo), lo, hi) for lo, hi in zip(bs, bs[1:])]
    k = scale_exponent(his)
    xs = [G.upward(F(2) ** k * h) for h in his]
    if min(xs) < LOW:
        raise SystemExit(f"{cfg['name']}: cells span more than 2^40; split the program")
    lits = [G.literal(x) for x in xs]
    scale = G.literal(F(1, 2 ** k))
    ops = [("+", const["anchor"]), ("+", const["point"]), ("+", const["tail"])]
    if len(lits) <= 64:
        csrc = render_single("fks2_table4_transport", lits, scale, ops)
        chunks = [lits]
    else:
        chunks = [lits[:64], lits[64:]]
        csrc = render_chunked("fks2_table4_transport", chunks, scale, ops)
    # binary64 sequential sum as the program computes it, then the suffix
    acc = 0.0
    for x in xs:
        acc = acc + float(x)
    est = F(acc) * F(1, 2 ** k) + sum((F(o[1]) for o in ops), F(0))
    return dict(cfg, k=k, scale=scale, his=his, xs=xs, lits=lits, chunks=chunks, csrc=csrc, const=const,
                estimate=est)


def lean_data(r: dict) -> str:
    bs = ", ".join(lean_rat(b) for b in r["bs"])
    lits = ",\n    ".join(f'"{l}"' for l in r["lits"])
    extra = ""
    if r["const"] is not None:
        c = r["const"]
        q = lambda lit: lean_rat(F(lit))
        extra = (f'\ndef anchorLiteral : String := "{c["anchor"]}"\n'
                 f'def pointLiteral : String := "{c["point"]}"\ndef tailLiteral : String := "{c["tail"]}"\n'
                 f'\n/-- The exact binary64 values of the three constants (decoded from the literals). -/\n'
                 f'def anchorQ : ℚ := {q(c["anchor"])}\ndef pointQ : ℚ := {q(c["point"])}\n'
                 f'def tailQ : ℚ := {q(c["tail"])}\n')
    return f"""/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Agent B (Claude)
-/
import Mathlib.Data.Rat.Defs

/-! Generated by `scripts/generate.py` (configuration `{r["name"]}`); do not edit. Lean re-checks
every literal against `cellHi`; this file only records the data. -/

namespace Table4Evolution.{r["ns"]}

/-- Partition boundaries of `[300, 330]`. -/
def bs : List ℚ := [{bs}]

/-- Upward binary64 literals of `2^{r["k"]}·cellHi` for each cell, in order. -/
def literals : List String := [
    {lits}]

/-- The scale `2^-{r["k"]}`, as printed in the C file. -/
def scaleLiteral : String := "{r["scale"]}"

/-- The exact binary64 values of the cell literals (what `PVCore.decode` returns), for the kernel
route. -/
def xsQ : List ℚ := [{", ".join(lean_rat(x) for x in r["xs"])}]
{extra}
end Table4Evolution.{r["ns"]}
"""


def main(argv: list[str]) -> int:
    check = "--check" in argv
    (PROJECT / "c").mkdir(exist_ok=True)
    (PROJECT / "Table4Evolution" / "Data").mkdir(exist_ok=True)
    bad = 0
    for cfg in CONFIGS:
        r = build(cfg)
        r["cfg_const_is_new"] = cfg["const"] is None
        cpath = PROJECT / "c" / f"{r['name']}.c"
        lpath = PROJECT / "Table4Evolution" / "Data" / f"{r['ns']}.lean"
        ltext = lean_data(r)
        if check:
            same = cpath.read_text() == r["csrc"] and lpath.read_text() == ltext
            bad += not same
            print(f"{r['name']}: {'same' if same else 'DIFFERS'}")
            continue
        cpath.write_text(r["csrc"])
        lpath.write_text(ltext)
        print(f"{r['name']}: {len(r['lits'])} cells, chunks {[len(c) for c in r['chunks']]}, "
              f"program output ~ {float(r['estimate']):.6e}, target {r['target'] and float(r['target'])}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
