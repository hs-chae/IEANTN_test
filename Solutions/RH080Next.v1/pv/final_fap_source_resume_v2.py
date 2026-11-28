"""Preserve a verified prefix of this exact interrupted source-cold experiment.
No outside application proof cache is searched or imported.
"""
from pathlib import Path
import os
import shutil
from compile_verified_batch import atomic, need, sha, GENERIC
from final_fap_source_data_v2 import read_json, verify_data,check_file,relative
import reproduce_final_fap_source_cold_v2 as original


def validate_prefix(prefix, context, source_rows):
    plan = read_json(prefix / "PLAN.json")
    need(plan["source_cold"] is True and plan["application_object_fallback"] is False,
         "Prefix is not the same source-only experiment")
    need(plan["schema_version"] == 2 and plan["literal_data_files"] == 34,
         "Prefix literal data schema differs")
    need((prefix / "FAILED.json").is_file() and not (prefix / "RESULT.json").exists(),
         "Expected the retained interrupted source-cold prefix")
    failure = read_json(prefix / "FAILED.json")
    need(failure["completed"] == 357 and failure["total"] == 681 and
         failure["resource_failures"] == ["host RAM or campaign scratch reserve"],
         "Unexpected interrupted experiment scope")
    need(sha(context) == plan["context_sha256"] == sha(Path(plan["context"])),
         "Prefix compiler/context differs")
    need(sha(Path(plan["controller"])) == plan["controller_sha256"], "Prefix controller changed")
    need(sha(Path(original.__file__)) == plan["controller_sha256"], "Original source-cold controller differs")
    need(sha(Path(original.__file__).parent / "final_fap_source_data_v2.py") == plan["literal_data_helper_sha256"], "Prefix data helper changed")
    need(sha(Path(original.__file__).parent / "compile_verified_batch.py") == plan["helper_sha256"], "Prefix compiler helper changed")
    context_data = read_json(context)
    inventory = read_json(Path(plan["inventory"]))
    verify_data(prefix / "source", plan["literal_data"], plan["source_rows"], inventory["literal_data"])
    need(sha(prefix / "LITERAL_DATA.json") == plan["literal_data_manifest_sha256"],
         "Prefix literal manifest changed")
    before = {r["module"]: (r["origin"], r["source_sha256"], r["imports"]) for r in plan["source_rows"]}
    after = {r["module"]: (r["origin"], r["source_sha256"], r["imports"]) for r in source_rows}
    need(len(before) == len(after) == 681 and before == after, "Prefix source universe changed")
    for source in plan["source_rows"]:
        need(sha(Path(source["origin"])) == source["source_sha256"] and sha(Path(source["snapshot"])) == source["source_sha256"], "Prefix original/snapshot source changed")
    names = {p.name[:-len(".COMPILED.json")] for p in prefix.glob("*.COMPILED.json")}
    need(len(names) == 357 and names <= set(before), "Expected exactly357 successful cold modules")
    rows = []
    for row in plan["source_rows"]:
        name = row["module"]
        if name not in names:
            continue
        need(all(child.split(".")[0] in GENERIC or child in names for child in row["imports"]),
             "Prefix imports an outside application cache")
        receipt = original.module_valid(prefix, row)
        logical = Path(row["snapshot"]).parents[len(name.split("."))-1].parent
        expected_command = ["/usr/bin/time", "-v", "-o", str(logical/"logs"/(name+".time")),
            "prlimit", "--as="+str(plan["worker_AS_bytes"]), "--stack="+str(256*2**20), "--",
            context_data["compiler"], "-j1", "--root="+str(logical/"source"), "-o",
            str(logical/"objects"/(name.replace(".","/")+".olean")), row["snapshot"]]
        need(receipt["command"] == expected_command, "Prefix actual compiler/source command differs")
        attempt = read_json(prefix / (name + ".ATTEMPT.json"))
        need({k: v for k, v in receipt.items() if k != "object_sha256"} == attempt,
             "Prefix attempt/compile receipt differs")
        need(receipt["exitcode"] == 0, "Failed child is not reusable")
        rows.append(dict(module=name, source_sha256=row["source_sha256"],
                         receipt_sha256=sha(prefix / (name + ".COMPILED.json")),
                         attempt_sha256=sha(prefix / (name + ".ATTEMPT.json")),
                         object_sha256=receipt["object_sha256"],
                         stdout_sha256=receipt["stdout_sha256"],
                         stderr_sha256=receipt["stderr_sha256"],
                         time_sha256=receipt["time_sha256"]))
    need(len(rows) == 357, "Incomplete validated prefix")
    return dict(prefix=str(prefix.resolve()), prefix_plan_sha256=sha(prefix / "PLAN.json"),
                prefix_failure_sha256=sha(prefix / "FAILED.json"),
                prefix_literal_data_manifest_sha256=sha(prefix / "LITERAL_DATA.json"),
                modules=357, fresh_modules=324, rows=rows)


def install_prefix(prefix, run, manifest):
    records = []
    for row in manifest["rows"]:
        name = row["module"]
        relative = Path(name.replace(".", "/") + ".olean")
        target = run / "objects" / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        need(not target.exists(), "Fresh resumed object destination required")
        os.link(prefix / "objects" / relative, target)
        need(sha(target) == row["object_sha256"], "Resumed object bytes differ")
        for suffix in [".COMPILED.json", ".ATTEMPT.json"]:
            shutil.copyfile(prefix / (name + suffix), run / (name + suffix))
        for kind in ["stdout", "stderr", "time"]:
            os.link(prefix / "logs" / (name + "." + kind), run / "logs" / (name + "." + kind))
        atomic(run / (name + ".REUSED.json"), dict(prefix=manifest["prefix"], **row))
        records.append(read_json(run / (name + ".COMPILED.json")))
    atomic(run / "REUSED_SOURCE_COLD_PREFIX.json", manifest)
    return records


def verify_reused(run, plan):
    need(plan["same_experiment_source_cold_resume"] is True and
         plan["reused_source_cold_modules"] == 357 and plan["fresh_source_cold_modules"] == 324,
         "Incorrect source-cold resume scope")
    path = run / "REUSED_SOURCE_COLD_PREFIX.json"
    need(sha(path) == plan["resume_manifest_sha256"], "Resume manifest changed")
    manifest = read_json(path)
    prefix = Path(manifest["prefix"])
    expected = validate_prefix(prefix, Path(plan["context"]), plan["source_rows"])
    need(manifest == expected, "Same-experiment source-cold prefix changed")
    for row in manifest["rows"]:
        name = row["module"]
        need(sha(run / (name + ".COMPILED.json")) == row["receipt_sha256"] and
             sha(run / (name + ".ATTEMPT.json")) == row["attempt_sha256"],
             "Resumed compiler provenance differs")
        need(read_json(run / (name + ".REUSED.json")) == dict(prefix=manifest["prefix"], **row),
             "Resumed per-module lineage differs")
        need(sha(run / "objects" / (name.replace(".", "/") + ".olean")) == row["object_sha256"],
             "Resumed object changed")
        for kind in ["stdout", "stderr", "time"]:
            need(sha(run / "logs" / (name + "." + kind)) == row[kind + "_sha256"],
                 "Resumed compiler diagnostic/time changed")
    return {row["module"] for row in manifest["rows"]}


def link_literal_data(prefix, source_root, staged_rows):
    linked = []
    for row in staged_rows:
        destination = relative(row["destination"], "literal destination")
        target = source_root / destination
        need(target.resolve().is_relative_to(source_root.resolve()) and not target.exists(), "Fresh safe resumed literal snapshot required")
        target.parent.mkdir(parents=True, exist_ok=True)
        os.link(prefix / "source" / destination, target)
        check_file(target, row)
        linked.append(dict(row, snapshot=str(target)))
    return linked
