#!/usr/bin/env python3
"""Export theorem types from all thirteen censored immutable submissions.

These posthoc replays never change primary eligibility or prove an exposure
advantage. A compiler/type/axiom export is not independent claim interpretation.
The same existing offline runtime executes all submitted Lean code.
"""
import argparse
import asyncio
import hashlib
import re
from pathlib import Path
from types import SimpleNamespace
import run_review as common

D = common.D
ROOT = D / "exposure-supplemental-replay-v1"


def generic_audit(module):
    common.need(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", module) is not None, "Unsupported module name")
    return "import " + module + r'''
import Lean
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option pp.fullNames true
open Lean Elab Command Meta
run_cmd do
  let env←getEnv
  let moduleName : Name:=`MODULE
  let constants:=env.constants.toList.filter (fun pair=>match env.getModuleIdxFor? pair.1 with
    | some i=>env.header.moduleNames[i]! == moduleName
    | none=>false)
  let allowed:=#[`propext,`Classical.choice,`Quot.sound]
  let mut rows : Array Json:=#[]
  for (name,info) in constants do
    if let .axiomInfo _ := info then throwError "Submitted axiom {name}"
    if let .thmInfo t := info then
      let axioms←collectAxioms name
      unless axioms.all allowed.contains do throwError "Nonstandard theorem axiom {name}: {axioms}"
      let rendered←liftTermElabM <| Meta.ppExpr info.type
      rows:=rows.push (Json.mkObj [("declaration",toJson name.toString),("type",toJson rendered.pretty),
        ("axioms",toJson (axioms.map toString)),
        ("direct_dependencies",toJson (t.value.getUsedConstants.toList.map toString))])
  unless rows.size>0 do throwError "No submitted theorem declarations"
  liftIO <| IO.FS.writeFile "/work/submission/THEOREMS.json" (Json.compress (toJson rows))
  logInfo m!"SUPPLEMENTAL_TYPE_AXIOM_EXPORT_PASS module={moduleName} theorem_count={rows.size} CLAIM_INTERPRETATION_PENDING PRIMARY_ELIGIBILITY_UNCHANGED"
'''.replace("MODULE", module)


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--trial", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    common.need(args.out.resolve().is_relative_to(ROOT) and not args.out.exists(),
                "Fresh experiment-owned supplemental directory required")
    args.out.parent.mkdir(parents=True, exist_ok=True)
    primary = D / "exposure-matched-v2/EXPOSURE_RESEARCH_EXECUTION.json"
    summary = common.load(primary)
    rows = summary["rows"]
    common.need(len(rows) == 16 and len({row["trial"] for row in rows}) == 16, "Locked population changed")
    censored = {row["trial"] for row in rows if not row["discovery_admissible_for_evaluation"]}
    common.need(len(censored) == 13 and args.trial in censored, "This route only replays the thirteen censored submissions")
    selected = next(row for row in rows if row["trial"] == args.trial)
    common.need(selected["stop_reason"] == "GENERATED_OUTPUT_ADMISSION_CEILING", "Original censoring classification changed")
    trial = D / "exposure-controller-v2/trials" / args.trial / "research-v1"
    result = common.load(trial / "result.json")
    common.need(common.sha(trial / "result.json") == selected["result_sha256"], "Primary result changed")
    lock = trial / "submission/LOCK.json"
    common.need(common.sha(lock) == result["artifact_export"]["lock_sha256"] == selected["artifact_export"]["lock_sha256"],
                "Original immutable submission lock changed")
    files = common.load(lock)["files"]
    common.need(len(files) == len({row["path"] for row in files}), "Duplicate payload identity")
    for row in files:
        p = trial / "submission" / row["path"]
        common.need(p.name == row["path"] and p.is_file() and not p.is_symlink() and common.sha(p) == row["sha256"],
                    "Invalid or changed original payload")
    lean = [row for row in files if row["path"].endswith(".lean")]
    common.need(len(lean) == 1, "Record separately if no unique original Lean payload exists")
    source = (trial / "submission" / lean[0]["path"]).read_bytes()
    module = Path(lean[0]["path"]).stem
    audit = generic_audit(module)
    script = common.worker_source(args.trial, module, source, audit)
    packet = args.out.parent / (args.out.name + "-packet")
    common.need(not packet.exists(), "Fresh packet required")
    packet.mkdir()
    (packet / "TASK.md").write_text("Scripted supplemental compiler/type/axiom export only. Zero inference. Primary censored status remains unchanged.\n")
    (packet / "WORKER_SCRIPT.py").write_text(script)
    (packet / "IndependentAudit.lean").write_text(audit)
    runtime_path = D / "exposure-controller-v2/trials/fixed_width-B_named-r1/runtime.json"
    runtime = common.load(runtime_path)
    adapter = common.module_at("supplement_pinned_adapter", common.S / "ablation/native_trial.py")
    common.need(common.sha(common.BACKEND) == common.BACKEND_SHA, "Pinned offline executor changed")
    for mount in runtime["mounts"]:
        adapter.check_tree(Path(mount["source"]), mount["manifest"])
    common.need(runtime["external_network"] is False and runtime["host_tools"] is False, "Original offline boundary changed")
    config = SimpleNamespace(out=args.out, packet=packet, model="gpt-6.2-sol", effort="high", fixture=True,
        wall=1200, output=18000, operations=180, responses=96, memory_gib=64, scratch_gib=12, cpus=4,
        per_response_max_output_tokens=None, phase="CENSORED_SUPPLEMENTAL_TYPE_EXPORT_NOT_PRIMARY",
        fixture_hook_fault=False, fixture_artifact_name="REVIEW.json", fixture_boundary_steps=1,
        fixture_draft_at=1, fixture_budget_prefix=False, paired_task_seed=0, compiler=False,
        python_only=False, environment="", python_optimization=0)
    core = adapter.import_backend()
    core.configure_runtime(runtime, config)
    core.Fixture = common.scripted_handler(core.Fixture, script)
    core.make_prompt = lambda p: (p / "TASK.md").read_text()
    pins = dict(trial=args.trial, primary_summary_sha256=common.sha(primary),
        primary_result_sha256=common.sha(trial/"result.json"), primary_lock_sha256=common.sha(lock),
        source_sha256=hashlib.sha256(source).hexdigest(), common_runtime_sha256=common.sha(runtime_path),
        worker_script_sha256=common.sha(packet/"WORKER_SCRIPT.py"), audit_sha256=common.sha(packet/"IndependentAudit.lean"),
        backend_sha256=common.sha(common.BACKEND), controller_sha256=common.sha(Path(__file__)),
        external_model_inference_calls=0, primary_eligible=False,
        scope="SUPPLEMENTAL_TYPE_EXPORT_NOT_CLAIM_AUDIT_OR_PRIMARY_SUCCESS")
    common.save(args.out.parent/(args.out.name+".INPUTS.json"), pins)
    asyncio.run(core.main(config))
    common.need(common.sha(primary) == pins["primary_summary_sha256"] and common.sha(lock) == pins["primary_lock_sha256"]
                and common.sha(trial/"result.json") == pins["primary_result_sha256"], "Original evidence changed during supplemental replay")
    for row in files:
        common.need(common.sha(trial/"submission"/row["path"]) == row["sha256"], "Frozen payload changed")
    print("SUPPLEMENTAL_REPLAY_FINISHED", args.trial, flush=True)


if __name__ == "__main__":
    main()
