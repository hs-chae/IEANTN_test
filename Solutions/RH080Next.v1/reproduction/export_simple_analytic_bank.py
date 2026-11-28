#!/usr/bin/env python3
"""Format-only export of the three accepted analytic command-list bank formats."""
import argparse,os,re
from pathlib import Path
from bootstrap_context import atomic,need,read_json,sha,validate_context

FORMATS={
 "AnalyticFlat64Audit":("PASS_SOURCE_COLD_KERNEL_ONLY_ANALYTIC_ANT",20,"FLAT64_AUDIT_PASS roots=21",21),
 "AnalyticFlatFamilyAudit":("PASS_SOURCE_COLD_KERNEL_ONLY_ANALYTIC_ANT",21,"FLAT_FAMILY_AUDIT_PASS roots=22",22),
 "AnalyticFlatFamilyAsymptoticAudit":("PASS_SOURCE_COLD_REAL_ALPHA_ASYMPTOTIC_ANALYTIC_ANT_NOT_PV",23,"REAL_ALPHA_ASYMPTOTIC_AUDIT_PASS roots=15",15),
}
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    for n in ["base","context","run"]:ap.add_argument("--"+n,required=True,type=Path)
    a=ap.parse_args();need(not os.path.lexists(a.run),"Fresh format-only bank required")
    validate_context(read_json(a.context))
    p=read_json(a.base/"PLAN.json");r=read_json(a.base/"RESULT.json")
    rows=p["source_rows"];names={x["module"]for x in rows}
    roots=[n for n in FORMATS if n in names]
    need(len(roots)==1,"Exactly one supported analytic audit required")
    root=roots[0];status,count,marker,axiom_count=FORMATS[root]
    need(r["status"]==status and r["source_cold"]is True and r["modules"]==count==len(rows)==len(names),
        "Accepted source-cold population differs")
    need(p["context_sha256"]==sha(a.context)and p["application_object_fallback"]is False,
        "Exact producer context/source boundary differs")
    commands=r["commands"];need(len(commands)==count,"Actual command population differs")
    by_name={}
    for command in commands:
        n=command["module"];need(n not in by_name,"Duplicate compiler identity")
        need(type(command.get("exitcode"))is int and command["exitcode"]==0,"Unaccepted compiler command")
        by_name[n]=command
    need(set(by_name)==names,"Source/actual-command universes differ")
    text=(a.base/"logs"/(root+".stdout")).read_text()
    need(marker in text,"Final exact typed/axiom/consumer gate absent")
    patterns=re.findall(r"(?:FLAT64_AXIOMS|FLAT_FAMILY_AXIOMS|REAL_ALPHA_ASYMPTOTIC_AXIOMS) [^\n]+?: \[([^\]]*)\]",text,re.S)
    need(len(patterns)==axiom_count,"Axiom audit population differs")
    for axes in patterns:need({x.strip()for x in axes.split(",")if x.strip()}<=
        {"propext","Classical.choice","Quot.sound"},"Nonstandard proof axiom")
    a.run.mkdir(parents=True)
    for n in ["source","objects","logs"]:(a.run/n).mkdir()
    exported=[]
    for row in rows:
        n=row["module"];source=Path(row["snapshot"]);origin=Path(row["origin"]);rc=by_name[n]
        need(sha(source)==sha(origin)==row["source_sha256"],"Actual source/snapshot differs")
        need(str(source)in rc["command"],"Compiler did not consume frozen source")
        need(read_json(a.context)["compiler"]in rc["command"],"Actual compiler differs")
        obj=a.base/"objects"/(n.replace(".","/")+".olean")
        need(sha(obj)==rc["object_sha256"],"Compiled object differs")
        src_target=a.run/"source"/(n.replace(".","/")+".lean")
        obj_target=a.run/"objects"/(n.replace(".","/")+".olean")
        for source_path,target in [(source,src_target),(obj,obj_target)]:
            target.parent.mkdir(parents=True,exist_ok=True);os.link(source_path,target)
        for suffix,key in [("stdout","stdout_sha256"),("stderr","stderr_sha256"),("time","time_sha256")]:
            source_path=a.base/"logs"/(n+"."+suffix)
            need(sha(source_path)==rc[key],"Actual log identity differs")
            os.link(source_path,a.run/"logs"/source_path.name)
        normalized=dict(rc,original_receipt=str(a.base/"RESULT.json"),
            original_receipt_sha256=sha(a.base/"RESULT.json"),
            original_command_record_module=n,format_only_export=True)
        atomic(a.run/(n+".COMPILED.json"),normalized)
        exported.append(dict(row,snapshot=str(src_target),original_snapshot=str(source)))
    atomic(a.run/"PLAN.json",dict(source_rows=exported,context_sha256=sha(a.context),
        source_cold=False,format_only_export_of_source_cold=True,
        original_plan=str(a.base/"PLAN.json"),original_plan_sha256=sha(a.base/"PLAN.json"),
        original_result=str(a.base/"RESULT.json"),original_result_sha256=sha(a.base/"RESULT.json"),
        controller_sha256=sha(Path(__file__)),application_object_fallback=False))
    atomic(a.run/"RESULT.json",dict(status="PASS_FORMAT_ONLY_ANALYTIC_BANK_EXPORT",
        modules=count,mathematics_reproved_here=False,new_mathematical_acceptance=False,
        immutable_objects_hardlinked=True,original_source_cold_result_sha256=sha(a.base/"RESULT.json")))
    print("PASS format-only analytic bank; no new proof or changed source")
if __name__=="__main__":main()
