#!/usr/bin/env python3
"""Check the reviewed EN/KO report preimages and reproduce both HTML byte strings.

This is a report reproduction/semantic-regression gate, not a mathematics prover
or a whole-repository source-claim audit. Every condition uses explicit errors,
including under Python -O/-OO. It does not modify the report generator or reports.
"""
from __future__ import annotations
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import tempfile
import time

CAMPAIGN = Path(__file__).resolve().parents[3]
NETWORK = CAMPAIGN.parents[1]
REPORTS = CAMPAIGN / "reports"


def digest(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def require(c: bool, message: str) -> None:
    if not c:
        raise RuntimeError(message)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    require(not args.out.exists(), "output receipt must be fresh")
    args.out.parent.mkdir(parents=True, exist_ok=True)
    started = time.monotonic()
    inputs = [REPORTS / "render.py", REPORTS / "fonts/STIXGeneral.ttf"]
    inputs.extend(sorted((REPORTS / "render-support").rglob("*.py")))
    if (REPORTS / "FACTS.json").exists():
        inputs.append(REPORTS / "FACTS.json")
    before = {str(p.relative_to(NETWORK)): digest(p) for p in inputs}
    generator = (REPORTS / "render.py").read_text()
    requirements = {
        "square_profile_non_strict_and_domain": [r"\sqrt{x}[A_1(x)-\log x-E]\ge", r"1423^2\le x\le10^{19}"],
        "cube_profile_and_whole_band_gain": [r"u^6[A_1(u^{12})", r"7\le u,\ u^{12}\le10^{19}", r".01379001+.000229>.014"],
        "Mellin_domain_and_Stieltjes_limit": [r"0<s<1:", r"\gamma_1=\lim_{N\to\infty}"],
        "Nicolas_actual_W_and_summability": [r"W(x)=\Re\sum_{\rho}", r"\sum_\rho\left|", "x≥exp34"],
        "all21_coefficients_with_initial_zeros": ["all21 coefficients, including four initial zeros", "처음 4개가 0인 계수 21개"],
        "asymptotic_count_frontier_domain": ["asymptotic same-count infimum bounds with an unspecified onset", "시작점이 명시되지 않은 점근적"],
        "exact_Simonic_subpower_onset": [r"x\ge10^{10^{4.487}}", r"L\ge(\log10)10^{4.487}"],
        "actual_caption_proof_links": ["../signed/source/Table13Check.lean", "../signed/caption-source/Table13OtherColumns.lean"],
        "Mobius_analytic_gaps_explicit": ["are not all closed in Lean", "Lean에서 아직 닫히지 않았다"],
        "PV_boundary_explicit": ["The entire portfolio is not end-to-end source-first PV", "source-first PV of all prime counts"],
        "no_causality_claim": ["does not establish that exposure to the network caused better discovery", "원인이라는 결론은 내리지 않는다"],
    }
    for name, fragments in requirements.items():
        for fragment in fragments:
            require(fragment in generator, f"reviewed fragment missing: {name}: {fragment}")
    require("21positivecoefficients" not in generator.replace(" ", ""), "zero coefficients described as positive")
    spec = importlib.util.spec_from_file_location("reviewed_rh_report", REPORTS / "render.py")
    require(spec is not None and spec.loader is not None, "cannot load report generator")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    records = []
    with tempfile.TemporaryDirectory(prefix="report-review-", dir=args.out.parent) as temporary:
        module.OUT = Path(temporary)
        for lang in ("EN", "KO"):
            record = module.render(lang)
            actual = REPORTS / record["path"]
            generated = module.OUT / record["path"]
            require(actual.is_file(), f"report missing: {actual}")
            require(actual.read_bytes() == generated.read_bytes(), f"report/generator byte mismatch: {lang}")
            doc = actual.read_text()
            require(doc.count("<math") >= 25, f"missing static MathML: {lang}")
            require("data:font/ttf;base64," in doc, f"font not embedded: {lang}")
            require("<script" not in doc.lower(), f"external/script rendering dependency: {lang}")
            require(re.search(r"\\(?:\(|\)|\[|\])|\$\$", doc) is None, f"raw TeX delimiter: {lang}")
            records.append({**record, "exact_regeneration": True})
    after = {str(p.relative_to(NETWORK)): digest(p) for p in inputs}
    require(before == after, "report inputs changed during review; rerun")
    result = {
        "schema": "RH_REPORT_REGENERATION_REVIEW_V1", "status": "PASS",
        "scope": "Both current EN/KO standalone HTML reports and reviewed formula/status regression fragments; not an exhaustive proof/source audit.",
        "python": sys.version, "optimize": sys.flags.optimize,
        "inputs": before, "reports": records,
        "reviewed_regressions": list(requirements),
        "elapsed_seconds": time.monotonic() - started,
        "remaining": ["Open analytical Lean source predicates remain open", "No independent official Comparator run is asserted", "Native directed numerical comparisons are not PV"],
    }
    temporary = args.out.with_name(args.out.name + ".tmp")
    temporary.write_text(json.dumps(result, indent=2) + "\n")
    temporary.replace(args.out)
    print(json.dumps({"status": "PASS", "receipt": str(args.out), "reports": records}, indent=2))


if __name__ == "__main__":
    main()
