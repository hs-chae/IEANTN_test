#!/usr/bin/env python3
"""Regenerate docs/program-verification/PV_ENDPOINT_TABLES.md: the per-endpoint final tables (the 12
fields the restructuring prompt requires).

    python scripts/native_assisted/final_tables.py > docs/program-verification/PV_ENDPOINT_TABLES.md

Read-only: built from pv-evidence/*.native-assisted.local.json and endpoints.json.
"""
from __future__ import annotations

import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parent.parent
ENDPOINTS = json.loads((HERE / "endpoints.json").read_text())["endpoints"]

def all_sources(m: dict) -> list[dict]:
    """Every executed source of an attestation: its C files, or each backend's sources."""
    out = []
    backends = m.get("backends")
    if backends is None:
        for s in (m.get("S_source_identity") or {}).get("sources", []):
            out.append({"path": s["path"], "sha256": s.get("sha256"), "backend": "restricted-c-binary64",
                        "embedded_by": s.get("embedded_by", [])})
        return out
    for b in backends:
        S = b.get("S_source_identity") or {}
        for s in S.get("sources", []):
            out.append({"path": s["path"], "sha256": s.get("sha256"), "backend": b.get("backend"),
                        "embedded_by": s.get("embedded_by", [])})
        for s in S.get("program_sources", []):
            out.append({"path": s["path"], "sha256": s.get("sha256"), "backend": b.get("backend"),
                        "embedded_by": [p["name"] for p in S.get("programs", [])
                                        if p.get("source") == s["path"]]})
    return out


def method_theorems(m: dict, k: str) -> list[str]:
    """The A/E/C theorems of an attestation, from every backend when there are several."""
    if m.get("backends") is None:
        return (m.get(k) or {}).get("theorems", [])
    return [t for b in m["backends"] for t in (b.get(k) or {}).get("theorems", [])]



MODEL = {"restricted-c-binary64": "restricted C / binary64 RN model of the token-matched source",
         "lean-dyadic-expr": "exact dyadic interval evaluation of the pinned generated Lean expressions"}


def unused(s: dict) -> str:
    """A pinned Lean file that defines no program constant is the evaluator; a C file must be embedded."""
    return "no program constant (pinned evaluator and row syntax)" if s["backend"] == "lean-dyadic-expr" else "NOTHING"


def cell(s) -> str:
    return str(s).replace("|", "\\|").replace("\n", " ")


def short(s: str, n: int = 70) -> str:
    s = " ".join(str(s).split())
    return s if len(s) <= n else s[:n] + "…"


def table(key: str, r: dict) -> str:
    off = r.get("official") or {}
    ax = r.get("axioms") or {}
    m = r.get("method_checks") or {}
    natives = ax.get("native_facts", [])
    nat_txt = f"{len(natives)}: " + "; ".join(
        f"`{n['decl']}` ({n['source_file']}:{n['range']['start_line']}, token `{n['token']}`, "
        f"decides `{short(n.get('decided_proposition') or '')}`)" for n in natives) if natives else "0"
    rejected = ax.get("rejected") or []
    srcs = all_sources(m)
    src_txt = "; ".join(f"`{s['path']}` sha256 `{s['sha256']}` ({s['backend']}) used by "
                        f"{', '.join('`'+e+'`' for e in s['embedded_by']) or unused(s)}" for s in srcs) or "none configured"
    kinds = sorted({s["backend"] for s in srcs}) or ["restricted-c-binary64"]
    boundary = ("; ".join(MODEL.get(k, k) for k in kinds) + "; Lean compiler + runtime for the native "
                "facts and their library implementations; "
                + ("C compiler, " if "restricted-c-binary64" in kinds else "") + "OS and hardware not modelled")
    def thms(k):
        ts = method_theorems(m, k)
        return ", ".join(f"`{t}`" for t in ts[:3]) + (f", … ({len(ts) - 3} more)" if len(ts) > 3 else "")
    proofs = "; ".join(f"{k.split('_',1)[1]}: " + thms(k)
                       for k in ("A_source_association", "E_execution_witness", "C_generic_correctness"))
    hyps = "; ".join(f"`{h['type']}`" for h in r.get("remaining_hypotheses") or []) or "none (pure arithmetic or closed)"
    run = r.get("run") or {}
    pins = r.get("pins") or {}
    rows = [
        ("Claim / conclusion ID", f"`{key}` → `{r.get('endpoint')}` : `{r.get('statement')}`"),
        ("Official designated `kind`", f"{off.get('designated_kind', 'n/a (not a node conclusion)')} "
                                       f"(`{off.get('designated_id', '-')}`), unchanged"),
        ("Evidence method", f"{r.get('evidence_method')} (S/A/E/C/M = " + "/".join(
            "✓" if (m.get(k) or {}).get('ok') else "✗" for k in ("S_source_identity",
            "A_source_association", "E_execution_witness", "C_generic_correctness",
            "M_mathematical_endpoint")) + ")"),
        ("Native-assisted gate", f"**{r.get('status')}** ({str(run.get('checked_at_utc', ''))})"
                                 + (f": {'; '.join(r.get('reasons') or [])}" if r.get('reasons') else "")),
        ("Standard axioms", ", ".join(ax.get("standard", [])) +
         (f" (missing: {', '.join(ax['standard_missing'])})" if ax.get("standard_missing") else "")),
        ("Extra finite native facts", nat_txt),
        ("Other unwanted axioms / sorry", "none" if not rejected else "; ".join(
            f"`{x['name']}`: {x['why']}" for x in rejected)),
        ("Source / executable model", f"{src_txt}. Proofs: {proofs}. Closure fingerprint "
                                      f"`{(r.get('proof_closure_fingerprint') or '')[:16]}`, "
                                      f"{len(r.get('project_modules') or [])} project modules hashed"),
        ("Mathematical hypotheses", hyps),
        ("Real-world trust boundary", boundary),
        ("Official Comparator receipt", off.get("official_comparator_receipt", "n/a (not a node conclusion)")),
        ("Reproduction", f"Lean {r.get('lean_version')} ({pins.get('lean_toolchain')}), Mathlib "
                         f"`{(pins.get('mathlib') or '')[:12]}`, repo `{(pins.get('repository_commit') or '')[:12]}`; "
                         f"`{(run.get('build') or {}).get('command', 'build skipped')}` rc "
                         f"{(run.get('build') or {}).get('rc')} in `{r.get('project')}`; "
                         f"`python scripts/native_assisted/native_assisted_check.py check {key}`"),
    ]
    out = [f"## `{key}`\n", "| Field | Value |", "|---|---|"]
    out += [f"| {a} | {cell(b)} |" for a, b in rows]
    return "\n".join(out) + "\n"


HEAD = """# Per-endpoint final tables

Generated from `pv-evidence/*.native-assisted.local.json` by
`scripts/native_assisted/final_tables.py`. Do not edit by hand. There is one table per audited
endpoint, with the twelve fields the restructuring task requires. Each attestation is a local
research report, not an IEANTN verification receipt.

Shortened entries end in "…". Every native fact has type `@Eq Bool e Bool.true` (the checker
verifies this shape), and the "decides" text is the proposition `e` decides. Its full text is in the
attestation under `axioms.native_facts[].decided_proposition`, and the full theorem lists are under
`method_checks`.
"""


def main():
    parts = [HEAD]
    for key in ENDPOINTS:
        p = ROOT / "pv-evidence" / f"{key}.native-assisted.local.json"
        if p.is_file():
            parts.append(table(key, json.loads(p.read_text())))
        else:
            parts.append(f"## `{key}`\n\nnot-run\n")
    print("\n".join(parts))


if __name__ == "__main__":
    main()
