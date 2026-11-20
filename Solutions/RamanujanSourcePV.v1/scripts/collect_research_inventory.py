#!/usr/bin/env python3
"""Record selected actual proof receipts, never infer acceptance from source existence."""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import re

S = Path(__file__).resolve().parents[1]
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
SELECTED = {
    "CheckerExecution": ["AST.C.source_count_is_primeCounting", "AST.C.service_closed"],
    "QuotientCSourceV2": ["QuotientCSourceV2.actual_source_bytes", "QuotientCSourceV2.actual_source_checked"],
    "QuotientCFunction": ["QuotientCFunction.linked_function_refines", "QuotientCFunction.completed_execution_correct"],
    "QuotientCCell": ["QuotientCCell.source_execution_count", "QuotientCCell.complete_certificate_from_source"],
    "QuotientCountRealization": ["QuotientCountRealization.source_execution_from_kernel_value"],
    "FirstCriticalCell": ["FirstCriticalCell.conditional_first_critical_interval", "FirstCriticalCell.conditional_preceding_counterexample"],
    "RecoveredMargin": ["RecoveredMargin.first_cell_margin_from_source"],
    "FinalAnalytic": ["FinalAnalytic.quantitative_from40", "FinalAnalytic.analytic_ray", "FinalAnalytic.all_real_from_completed_finite_certificate"],
    "QuotientDriverExecution": ["QuotientDriverExecution.possible_success_source_run"],
    "QuotientDriverSuccess": ["QuotientDriverSuccess.successful_main_output"],
    "MillionSourceOutputs": ["MillionSourceOutputs.million", "MillionSourceOutputs.scaled_million"],
}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def need(value, message):
    if not value:
        raise ValueError(message)


def read(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, "duplicate JSON key: " + key)
            result[key] = value
        return result
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError("nonfinite JSON")))


def axioms(log, name):
    stem = "'" + re.escape("RamanujanPV." + name) + "'"
    reports = re.findall(stem + r" depends on axioms:\s*\[([^\]]*)\]", log, re.S)
    free = re.findall(stem + " does not depend on any axioms", log)
    need(len(reports) + len(free) == 1, "one actual axiom report required: " + name)
    result = [] if free else sorted(x.strip() for x in reports[0].split(",") if x.strip())
    need(set(result) <= STANDARD, "unaccepted axiom in selected proof: " + name)
    return result


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    claims = []
    for module, names in SELECTED.items():
        source = S / "RamanujanPV" / (module + ".lean")
        identity = sha(source)
        receipts = sorted((S / "audit" / ("RamanujanPV." + module)).glob("*/RUN.json"), key=lambda p: int(p.parent.name))
        accepted = []
        for receipt in receipts:
            data = read(receipt)
            if data.get("status") != "COMPILED" or data.get("returncode") != 0 or data.get("source_sha256") != identity:
                continue
            stdout = receipt.parent / "stdout"
            need(sha(stdout) == data["stdout_sha256"], "stdout identity drift: " + module)
            if (receipt.parent / "source.lean").exists():
                need(sha(receipt.parent / "source.lean") == identity, "snapshot identity drift: " + module)
            accepted.append((receipt, data, stdout.read_text()))
        need(bool(accepted), "no accepted receipt for exact current source: " + module)
        receipt, data, output = accepted[-1]
        for name in names:
            claims.append({
                "file": str(source.relative_to(S)), "declaration": "RamanujanPV." + name,
                "line": next((i for i, line in enumerate(source.read_text().splitlines(), 1) if re.search(r"\b(?:theorem|lemma)\s+" + re.escape(name.rsplit(".", 1)[-1]) + r"\b", line)), None),
                "source_sha256": identity, "receipt": str(receipt.relative_to(S)), "receipt_sha256": sha(receipt),
                "axioms": axioms(output, name), "status": "KERNEL_COMPILED_EXACT_SELECTED_STATEMENT",
                "mathematical_hypotheses_removed": False,
            })
    sources = [{"file": str(p.relative_to(S)), "sha256": sha(p)} for p in sorted((S / "c").glob("*")) if p.is_file()]
    result = {
        "schema": "ieantn.ramanujan.selected-research-inventory.v1",
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "selection_author": "Root research integration controller",
        "selection_rule": "Exact hand-enumerated declarations in SELECTED; current source hash, successful compiler receipt and actual named axiom report required. This is NOT an exhaustive source-claim census.",
        "selected_theorems": claims, "actual_executable_sources": sources,
        "full_finite_source_first_execution": "OPEN",
        "original_IEANTN_results_modified": False,
        "distinctions": ["Source-function correctness is not a proved concrete numerical value.", "Kernel certificates alone are not source-first PV.", "A conditional certificate consumer does not construct its finite certificate.", "Named analytic hypotheses remain theorem inputs, not new axioms."],
    }
    args.out.parent.mkdir(parents=True, exist_ok=True)
    temporary = args.out.with_name(args.out.name + ".tmp")
    temporary.write_text(json.dumps(result, indent=2) + "\n")
    temporary.replace(args.out)
    print(json.dumps({"status": "PASS_SELECTED_CURRENT_PROOF_RECEIPTS", "theorems": len(claims), "output": str(args.out), "sha256": sha(args.out)}))


if __name__ == "__main__":
    main()
