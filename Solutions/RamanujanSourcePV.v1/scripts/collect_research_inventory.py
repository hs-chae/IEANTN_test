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
    "CriticalSourceClosed": ["CriticalSourceClosed.p_source", "CriticalSourceClosed.q_source", "CriticalSourceClosed.first_critical_interval", "CriticalSourceClosed.first_critical_margin", "CriticalSourceClosed.preceding_counterexample", "CriticalSourceClosed.first_1001_real_interval", "CriticalSourceClosed.preceding_failure", "CriticalSourceClosed.successful_driver_bytes"],
    "CriticalWindowMargin": ["CriticalWindowMargin.margins_checked", "CriticalWindowMargin.uniform_gap"],
    "SegmentCFunction": ["SegmentCFunction.correct_claims_execution", "SegmentCFunction.incorrect_claims_execution", "SegmentCFunction.positive_output_sound"],
    "SegmentRamanujan1000": ["SegmentRamanujan1000.p_provider", "SegmentRamanujan1000.q_provider", "SegmentRamanujan1000.complete_certificate", "SegmentRamanujan1000.first_1001_real_interval"],
    "FiniteExpLinked": ["FiniteExpLinked.service_closed", "FiniteExpLinked.linked_high_executes", "FiniteExpLinked.high_completed_correct", "FiniteExpLinked.source_outputs_enclose_e"],
    "FiniteLogBounds": ["FiniteLogBounds.fixed_series_u64", "FiniteLogBounds.wide_products", "FiniteLogBounds.binary_output_u64"],
    "SourcePayloadAudit": ["SourcePayloadAudit.trial_current", "SourcePayloadAudit.quotient_current", "SourcePayloadAudit.driver_current", "SourcePayloadAudit.segment_current", "SourcePayloadAudit.exponential_current"],
    "CertificateMargin": ["CertificateMargin.checked_array_certificate"],
    "MillionCriticalSourceClosed": ["MillionCriticalSourceClosed.finite_certificate", "MillionCriticalSourceClosed.real_interval", "MillionCriticalSourceClosed.uniform_gap", "MillionCriticalSourceClosed.p_endpoint_count", "MillionCriticalSourceClosed.q_endpoint_count"],
    "SegmentRamanujanMillion": ["SegmentRamanujanMillion.p_provider", "SegmentRamanujanMillion.q_provider", "SegmentRamanujanMillion.complete_certificate", "SegmentRamanujanMillion.first_1000001_real_interval"],
    "SegmentSourceMargins": ["SegmentSourceMargins.million_margins_checked", "SegmentSourceMargins.million_gap", "SegmentSourceMargins.thousand_gap"],
    "FiniteSourceEnclosures": ["FiniteSourceEnclosures.actual_source_e_outputs", "FiniteSourceEnclosures.source_e_scaled", "FiniteSourceEnclosures.row_enclosures_of_log_upper"],
    "FullFiniteScalars": ["FullFiniteScalars.scalar_sound", "FullFiniteScalars.checked_block", "FullFiniteScalars.append_certificate", "FullFiniteScalars.complete_from_counts"],
    "FiniteCellInverse": ["FiniteCellInverse.positive_domain", "FiniteCellInverse.positive_fixed"],
    "FiniteGuardedMillion": ["FiniteGuardedMillion.derived_domains", "FiniteGuardedMillion.source_fixed", "FiniteGuardedMillion.complete_certificate", "FiniteGuardedMillion.first_1000001_real_interval", "FiniteGuardedMillion.uniform_gap"],
    "FiniteGuardedResult": ["FiniteGuardedResult.actual_source_bindings", "FiniteGuardedResult.source_linked_uniform_gap", "FiniteGuardedResult.source_linked_real_interval"],
    "FiniteLogSeriesExecute": ["FiniteLogSeriesExecute.function_executes", "FiniteLogSeriesExecute.completed_correct", "FiniteLogSeriesExecute.service_closed"],
    "FiniteLogUpperExecute": ["FiniteLogUpperExecute.function_executes", "FiniteLogUpperExecute.completed_correct", "FiniteLogUpperExecute.source_execution_from_math", "FiniteLogUpperExecute.source_log_upper_sound"],
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
    context = read(S / "BUILD_CONTEXT.json")
    objects = Path(context["new_application_object_root"])
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
        object_path = objects / "RamanujanPV" / (module + ".olean")
        need(sha(object_path) == data["object_sha256"], "current object identity drift: " + module)
        for name in names:
            claims.append({
                "file": str(source.relative_to(S)), "declaration": "RamanujanPV." + name,
                "line": next((i for i, line in enumerate(source.read_text().splitlines(), 1) if re.search(r"\b(?:theorem|lemma)\s+" + re.escape(name.rsplit(".", 1)[-1]) + r"\b", line)), None),
                "source_sha256": identity, "receipt": str(receipt.relative_to(S)), "receipt_sha256": sha(receipt),
                "axioms": axioms(output, name), "status": "KERNEL_COMPILED_EXACT_SELECTED_STATEMENT",
                "mathematical_hypotheses_removed": False,
                "native_execution_axioms": False,
            })
    sources = [{"file": str(p.relative_to(S)), "sha256": sha(p)} for p in sorted((S / "c").glob("*")) if p.is_file()]
    result = {
        "schema": "ieantn.ramanujan.selected-research-inventory.v1",
        "timestamp": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "selection_author": "Root research integration controller",
        "selection_rule": "Exact hand-enumerated declarations in SELECTED; current source hash, successful compiler receipt and actual named axiom report required. This is NOT an exhaustive source-claim census.",
        "selected_theorems": claims, "actual_executable_sources": sources,
        "full_finite_source_first_execution": "OPEN",
        "target_universe": "Every real x >= 38358837683, actual IEANTN primeCounting; finite witness through1490000000001 and explicit analytic ray thereafter.",
        "selection_coverage": "Selected integration claims only. The full finite witness is absent. This inventory does not prove a census of all source-attributed declarations, all551 generated local proofs, or all655 historical QRH dependency declarations.",
        "unresolved_obligations": ["Full finite prime-count evidence for every required certificate cell through1490000000001", "Full finite certificate and actual source-linked interval-checker execution", "Full C++ generator/caller source association; completed C scalar execution currently covers the selected million-window theorem"],
        "completed_local_source_chain": "FiniteGuardedResult: all counter/segment/e/log/cell source executions and every real x in[38358837683,38359837684), gap>501901; no supplied counts or analytic premises",
        "completed_full_scalar_mathematics": "All1755663 original rows: exact coverage/strict predicate/real e-log enclosures; excludes prime-count truth and is not C source-PV by itself",
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
