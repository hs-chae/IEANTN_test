#!/usr/bin/env python3
"""Bounded actual CLI checks; never launches a heavy proof/numerical stage."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
from bootstrap_context import atomic,need,read_json,sha
HERE=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--context",required=True,type=Path);ap.add_argument("--run",required=True,type=Path)
    a=ap.parse_args();need(not a.run.exists(),"Fresh control directory required");a.run.mkdir(parents=True)
    good=read_json(a.context)
    bad_compiler=dict(good,compiler_sha256="0"*64);atomic(a.run/"bad-compiler.json",bad_compiler)
    bad_pins=json.loads(json.dumps(good));bad_pins["generic_dependencies"][0]["revision"]="0"*40
    atomic(a.run/"bad-pins.json",bad_pins)
    rows=[]
    for mode,label in [([],"normal"),(["-O"],"O"),(["-OO"],"OO")]:
        cases=[
            ("bootstrap-help",[str(HERE/"bootstrap_context.py"),"--help"],0),
            ("driver-help",[str(HERE/"reproduce_all.py"),"--help"],0),
            ("bootstrap-existing-pins",[str(HERE/"bootstrap_context.py"),"--from-context",str(a.context),"--output",str(a.run/(label+"-context.json"))],0),
            ("driver-plan-only",[str(HERE/"reproduce_all.py"),"--context",str(a.context),"--run",str(a.run/(label+"-plan"))],0),
            ("unknown-option",[str(HERE/"reproduce_all.py"),"--contex",str(a.context),"--run",str(a.run/(label+"-unknown"))],2),
            ("bad-compiler",[str(HERE/"reproduce_all.py"),"--context",str(a.run/"bad-compiler.json"),"--run",str(a.run/(label+"-badcompiler"))],1),
            ("bad-generic-pins",[str(HERE/"reproduce_all.py"),"--context",str(a.run/"bad-pins.json"),"--run",str(a.run/(label+"-badpins"))],1),
            ("existing-destination",[str(HERE/"reproduce_all.py"),"--context",str(a.context),"--run",str(a.run)],1),
            ("invalid-worker-count",[str(HERE/"reproduce_all.py"),"--context",str(a.context),"--run",str(a.run/(label+"-workers")),"--n24-workers","0"],1),
        ]
        for name,args,code in cases:
            cmd=[sys.executable]+mode+args
            r=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
            need(r.returncode==code,"Unexpected actual CLI result "+label+"/"+name)
            tag=label+"-"+name
            (a.run/(tag+".stdout")).write_text(r.stdout);(a.run/(tag+".stderr")).write_text(r.stderr)
            rows.append(dict(mode=label,case=name,command=cmd,returncode=r.returncode,
                stdout_sha256=sha(a.run/(tag+".stdout")),stderr_sha256=sha(a.run/(tag+".stderr"))))
        plan=read_json(a.run/(label+"-plan")/"PLAN.json")
        need(plan["status"]=="PLAN_ONLY_NOT_REPRODUCED"and plan["expensive_full_clean_replay_executed"]is False,
            "Plan accidentally claims execution")
        need(not(a.run/(label+"-plan")/"RESULT.json").exists(),"Plan-only result must not become acceptance")
        for suffix in ["unknown","badcompiler","badpins","workers"]:
            need(not(a.run/(label+"-"+suffix)).exists(),"Rejected CLI created acceptance/output")
    atomic(a.run/"RESULT.json",dict(status="PASS_BOUNDED_ACTUAL_PORTABLE_CLI_ALL_OPTIMIZATION_MODES",
        cases=rows,positive=12,negative=15,heavy_stage_launched=False,
        source_files={p.name:sha(p)for p in [HERE/"bootstrap_context.py",HERE/"reproduce_all.py"]}))
    print("PASS27 bounded actual CLI checks; no heavy pipeline launched")
if __name__=="__main__":main()
