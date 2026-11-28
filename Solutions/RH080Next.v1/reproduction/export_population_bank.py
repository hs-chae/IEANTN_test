#!/usr/bin/env python3
"""Format-only export of an accepted91-module two-program population replay.

Every source, compiler command, captured log and object is rechecked. Original
command indices/receipt hashes are retained. This performs no new compilation.
"""
import argparse,os,re
from pathlib import Path
from bootstrap_context import PROJECT,REPOSITORY,atomic,need,read_json,sha,validate_context

STATUS="PASS_COMPLETE_SOURCE_FIRST_NUMERICAL_FOURIER_EVENTUAL_PRIME_POPULATION_AND_MATCHED_CONTROL"
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for n in ["base","context","run"]:ap.add_argument("--"+n,required=True,type=Path)
    a=ap.parse_args();base=a.base.resolve(strict=True);target=a.run.resolve()
    need(not os.path.lexists(target),"Fresh population format export required")
    c,_=validate_context(read_json(a.context));plan=read_json(base/"PLAN.json");result=read_json(base/"RESULT.json")
    need(result["status"]==STATUS and result["modules"]==result["newly_compiled_modules"]==91
        and result["full_source_cold"]is True and result["application_object_fallback"]is False,
        "Accepted complete91-source population gate absent")
    need(result["plan_sha256"]==sha(base/"PLAN.json")and plan["context_sha256"]==sha(a.context),
        "Original plan/context differs")
    need(plan["compiler_sha256"]==c["compiler_sha256"]and plan["generic_dependencies"]==c["generic_dependencies"],
        "Original generic/compiler association differs")
    need(sha(base/"reproduce.executed.py")==plan["controller_sha256"],"Executed original controller changed")
    sources=plan.get("source_rows",plan.get("modules"));need(type(sources)is list and len(sources)==91,"Original source population differs")
    names=[r["module"]for r in sources];need(len(set(names))==91,"Collapsed compiler identity")
    commands=result["commands"];need(type(commands)is list and len(commands)==91,"Original command population differs")
    receipts={}
    for index,row in enumerate(commands):
        n=row["module"];need(n not in receipts,"Duplicate original command")
        need(type(row.get("returncode"))is int and row["returncode"]==0,"Rejected original command")
        receipts[n]=(index,row)
    need(set(receipts)==set(names),"Original source/command universes differ")
    native=base/"NATIVE_AND_REGENERATION.json";need(sha(native)==result["native_receipt_sha256"],"Original C regeneration receipt changed")
    native_record=read_json(native)
    need(native_record["status"]=="PASS_ACTUAL_C_REGENERATION_EXECUTION_AND_LEAN_FIXTURE_BYTE_ASSOCIATION"
        and len(native_record["programs"])==2,"Original two-program physical association differs")
    expected=[("Population","population_norm.c","887721072633027910\n"),
              ("FlatPopulation","flat_population_norm.c","1120475208606944546\n")]
    for (prefix,filename,stdout),row in zip(expected,native_record["programs"]):
        source=base/"regenerated"/prefix/"population_norm.c";binary=source.parent/"program"
        need(row["program"]==filename and row["stdout"]==stdout and row["mathematical_output_not_assumed"]is True,"Actual native output association differs")
        need(sha(source)==sha(PROJECT/"pv"/filename)==row["source_sha256"],"Actual original C bytes differ")
        need(sha(binary)==row["executable_sha256"]and sha(Path(row["compiler"]))==row["compiler_sha256"],"Actual C compiler/binary identity differs")
    audit=(base/"logs/PopulationCanonicalAudit.stdout").read_text()
    need("POPULATION_CANONICAL_AUDIT_PASS roots=18 exact_inputs=2 exact_sources=2"in audit
        and "POPULATION_CANONICAL_SOURCE_CLOSURE_PASS"in audit
        and "POPULATION_CANONICAL_CONTROL_CLOSURE_PASS"in audit,"Original actual-source/control audit absent")
    axes=re.findall(r"POPULATION_CANONICAL_AXIOMS [^\n]+?: \[([^\]]*)\]",audit,re.S)
    need(len(axes)==18,"Original eighteen-root axiom audit incomplete")
    for x in axes:need({v.strip()for v in x.split(",")if v.strip()}<=
        {"propext","Classical.choice","Quot.sound"},"Unexpected source axiom")
    target.mkdir(parents=True)
    for n in ["source","objects","logs"]:(target/n).mkdir()
    exported=[]
    for source_row in sources:
        n=source_row["module"];index,row=receipts[n]
        origin=Path(source_row["origin"]);snapshot=base/"source"/(n.replace(".","/")+".lean")
        obj=base/"objects"/(n.replace(".","/")+".olean")
        digest=source_row["source_sha256"]
        need(origin.resolve().is_relative_to(REPOSITORY.resolve()),"Application source escapes public repository")
        need(sha(origin)==sha(snapshot)==row["source_sha256"]==digest,"Original source/snapshot association differs: "+n)
        need(str(snapshot)in row["command"]and c["compiler"]in row["command"],"Compiler did not consume exact source/compiler")
        need(sha(obj)==row["object_sha256"],"Original proof object differs")
        for suffix,key in [("stdout","stdout_sha256"),("stderr","stderr_sha256")]:
            log=base/"logs"/(n.replace(".","_")+"."+suffix);need(sha(log)==row[key],"Original captured log differs")
            os.link(log,target/"logs"/(n+"."+suffix))
        diagnostics=(base/"logs"/(n.replace(".","_")+".stdout")).read_text()+(base/"logs"/(n.replace(".","_")+".stderr")).read_text()
        need(re.search(r"PANIC|sorryAx|error(?:\([^)]*\))?:",diagnostics,re.I)is None,"Original compiler diagnostic")
        src=target/"source"/(n.replace(".","/")+".lean");out=target/"objects"/(n.replace(".","/")+".olean")
        src.parent.mkdir(parents=True,exist_ok=True);out.parent.mkdir(parents=True,exist_ok=True)
        os.link(snapshot,src);os.link(obj,out)
        normalized=dict(row,exitcode=row["returncode"],original_receipt=str(base/"RESULT.json"),
            original_receipt_sha256=sha(base/"RESULT.json"),original_command_index=index,
            original_command_record_module=n,original_log_paths={su:str(base/"logs"/(n.replace(".","_")+"."+su))for su in ["stdout","stderr"]},resource_receipt_kind="GNU_TIME_EMBEDDED_STDERR",
            format_only_export=True)
        atomic(target/(n+".COMPILED.json"),normalized)
        exported.append(dict(module=n,origin=str(origin),snapshot=str(src),source_sha256=digest,
            imports=source_row["imports"],original_snapshot=str(snapshot)))
    atomic(target/"PLAN.json",dict(status="FORMAT_ONLY_ACCEPTED_POPULATION_BANK",
        source_rows=exported,context_sha256=sha(a.context),source_cold=False,
        original_source_cold=True,original_plan=str(base/"PLAN.json"),
        original_plan_sha256=sha(base/"PLAN.json"),original_result=str(base/"RESULT.json"),
        original_result_sha256=sha(base/"RESULT.json"),controller_sha256=sha(Path(__file__)),
        original_compiler_controller_sha256=plan["controller_sha256"],
        application_object_fallback=False,immutable_objects_hardlinked=True))
    atomic(target/"RESULT.json",dict(status="PASS_FORMAT_ONLY_POPULATION91_BANK_EXPORT",
        modules=91,new_compilation=False,new_mathematical_acceptance=False,
        original_result_sha256=sha(base/"RESULT.json"),original_native_receipt_sha256=sha(native)))
    print("PASS format-only accepted population91 bank; no new compilation/proof")
if __name__=="__main__":main()
