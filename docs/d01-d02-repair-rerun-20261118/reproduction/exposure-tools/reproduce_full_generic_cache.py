#!/usr/bin/env python3
"""Portable additive E Mathlib/Tactic bootstrap after reproduce_baselines.py.

Consumes that recipe's completed owned output, never a host checkout. All new
cache downloads/writes are in a fresh supplement; the completed baseline is
rehash-checked and left unchanged. No inference or source-first PV claim.
"""
from pathlib import Path
import argparse
import gzip
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import threading
import time
import uuid

BASE = Path(__file__).with_name("reproduce_baselines.py")
BASE_SHA = "3f6715744151cfbf46354c648a3a192250acfc17addbfba92da316af366bb13e"
spec = importlib.util.spec_from_file_location("frozen_baseline_reproduction", BASE)
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)
need, sha, load, write = base.need, base.sha, base.read_json, base.write_json


def inventory(root):
    root = Path(root).resolve()
    rows=[]
    for parent, dirs, files in os.walk(root, followlinks=False):
        for name in dirs+files:
            p=Path(parent)/name;rel=p.relative_to(root)
            need(".git" not in rel.parts,"Git metadata in cache tree")
            if p.is_symlink():
                need(p.resolve().is_relative_to(root),"cache symlink leaves tree")
                rows.append({"path":rel.as_posix(),"symlink":os.readlink(p)})
            elif p.is_file():rows.append({"path":rel.as_posix(),"bytes":p.stat().st_size,"sha256":sha(p)})
            else:need(p.is_dir(),"nonordinary cache entry")
    return sorted(rows,key=lambda r:r["path"])


def verify_row(path,row):
    if "symlink"in row:return path.is_symlink() and os.readlink(path)==row["symlink"]
    return path.is_file() and not path.is_symlink() and path.stat().st_size==row["bytes"] and sha(path)==row["sha256"]


def check_input(root,frozen):
    receipt=load(root/"RESULT.json")
    need(receipt.get("status")=="PASS_BASELINE_COMPONENT_REPLAY" and receipt.get("pins_sha256")==base.PIN_SHA256,
         "completed portable baseline receipt required")
    own=root/"IEANTN";e=load(own/"RESULT.json");p=frozen["arms"]["IEANTN"]
    need(e.get("status")=="PASS_SOURCE_FRESH_APPLICATION_BASELINE_REBUILD" and e.get("source_commit")==p["commit"],"E baseline source identity differs")
    for row in e["generated_proof_artifacts"]:need(verify_row(own/row["path"],row),"accepted E proof artifact changed")
    for row in p["source_files"]:need(verify_row(own/"source"/row["path"],row),"pinned E original source changed")
    for dep in p["generic"]:
        for row in dep["source_files"]:need(verify_row(own/"source/.lake/packages"/dep["name"]/row["path"],row),"pinned generic source changed")
    base.check_tree(own/"toolchain",p["toolchain"]["files"])
    return own,e,p


def inside(args,frozen):
    started=time.monotonic();out=args.out;original_script=sha(__file__)
    actual=base.actual_resources(out)
    need(actual["memory.max"]==str(args.memory_gib*1024**3) and actual["memory.swap.max"]=="0","actual supplement memory/swap scope differs")
    need(0<len(actual["cpu_affinity"])<=8 and actual["rlimit_nofile"][0]>=65536,"actual supplement CPU/descriptor scope differs")
    write(out/"ACTUAL_RESOURCE_START.json",actual)
    own,old,specification=check_input(args.baseline,frozen)
    source=out/"source";source.mkdir();packages=source/".lake/packages";packages.mkdir(parents=True)
    for name in ["lakefile.toml","lake-manifest.json","lean-toolchain","LICENSE"]:
        if (own/"source"/name).is_file():shutil.copy2(own/"source"/name,source/name)
    prior={};overrides=[];generic=[];source_checks=[]
    for dep in specification["generic"]:
        original=own/"source/.lake/packages"/dep["name"];target=packages/dep["name"];target.mkdir()
        for row in dep["source_files"]:
            p=target/row["path"];p.parent.mkdir(parents=True,exist_ok=True)
            if "symlink"in row:p.symlink_to(row["symlink"])
            else:shutil.copy2(original/row["path"],p)
            need(verify_row(p,row),"copied source differs")
        objects=original/".lake/build/lib/lean"
        if objects.is_dir():
            rows=inventory(objects);prior[dep["name"]]=rows
            destination=target/".lake/build/lib/lean";destination.parent.mkdir(parents=True,exist_ok=True)
            subprocess.run(["/usr/bin/cp","--archive","--reflink=auto",str(objects),str(destination)],check=True)
            need(inventory(destination)==rows,"copied existing object bytes differ")
            generic.append(destination)
        entry=dep["manifest"]
        overrides.append({"type":"path","name":dep["name"],"scope":entry.get("scope",""),"dir":str(target),
                          "inherited":entry["inherited"],"configFile":entry.get("configFile"),"manifestFile":entry.get("manifestFile")})
        source_checks.append({"name":dep["name"],"commit":dep["commit"],"files":len(dep["source_files"])})
    write(out/"package-overrides.json",{"schemaVersion":"1.2.0","packages":overrides})
    tc=own/"toolchain";env=base.environment(tc,out);commands=[];lock=threading.Lock()
    cache_before=time.monotonic()
    base.command([str(tc/"bin/lake"),"--packages",str(out/"package-overrides.json"),"exe","cache","get","Mathlib","Mathlib.Tactic"],
                 source,env,out,commands,lock,"official-full-generic-cache-get")
    cache_elapsed=time.monotonic()-cache_before;restored=[]
    for name,rows in prior.items():
        destination=packages/name/".lake/build/lib/lean";original=own/"source/.lake/packages"/name/".lake/build/lib/lean"
        for row in rows:
            p=destination/row["path"]
            if not verify_row(p,row):
                preserved=out/"official-overwrites-preserved"/name/row["path"];preserved.parent.mkdir(parents=True,exist_ok=True)
                downloaded=sha(p) if p.is_file() and not p.is_symlink() else None
                if p.exists() or p.is_symlink():p.replace(preserved)
                p.parent.mkdir(parents=True,exist_ok=True)
                if "symlink"in row:p.symlink_to(row["symlink"])
                else:shutil.copy2(original/row["path"],p)
                restored.append({"package":name,"path":row["path"],"downloaded_sha256":downloaded,"preserved":str(preserved),"restored":row})
            need(verify_row(p,row),"existing object restoration failed")
    for root in ["Mathlib.olean","Mathlib/Tactic.olean"]:need((packages/"mathlib/.lake/build/lib/lean"/root).is_file(),"ordinary umbrella absent")
    core=own/"objects";contexts=[]
    cases=[("ordinary-core",None,"import IEANTN.Nodes.DudekPlatt.v2.Conclusions\nimport IEANTN.Nodes.Dusart2018.v1.Conclusions\n",None),
           ("DPv3",own/"selected/DudekPlatt.v3","import Shifts\nimport Bounds\nimport Solution\n","DudekPlatt.v3.challenge_criterion"),
           ("DPv2",own/"selected/DudekPlatt.v2","import Solution\n","DudekPlatt.v2.challenge_ramanujan_inequality_3915")]
    for name,selected,body,theorem in cases:
        program=out/(name+".lean");program.write_text("import Mathlib\nimport Mathlib.Tactic\n"+body+"example : (2:Nat)+2=4 := by norm_num\n"+
            ("#check "+theorem+"\n#print axioms "+theorem+"\n" if theorem else ""))
        paths=([selected]if selected else[])+[core]+generic
        text=base.command([str(tc/"bin/lean"),"-j8",str(program)],out,base.environment(tc,out,paths),out,commands,lock,"canary-"+name)
        if theorem:need("'"+theorem+"' depends on axioms: [propext, Classical.choice, Quot.sound]"in text,"selected theorem has unexpected axioms")
        contexts.append({"context":name,"source_sha256":sha(program),"theorem":theorem,"axioms":["propext","Classical.choice","Quot.sound"]if theorem else[],"returncode":0})
    # Recheck all baseline artifacts, sources and platform bytes after the supplement.
    check_input(args.baseline,frozen)
    manifests=[]
    for name in prior:
        rows=inventory(packages/name/".lake/build/lib/lean")
        for row in rows:
            if row["path"].endswith(".olean"):
                relative=row["path"][:-6]+".lean";candidates=[relative]
                if name=="batteries"and relative=="runLinter.lean":candidates.append("scripts/runLinter.lean")
                need(sum((packages/name/p).is_file()for p in candidates)==1,"object lacks unique permitted source association")
        path=out/("generic-objects-"+name+".json.gz")
        data=json.dumps({"schema":"DEEP_TERTIARY_TREE_V1","root":str(packages/name/".lake/build/lib/lean"),"files":rows},sort_keys=True).encode()
        path.write_bytes(gzip.compress(data,mtime=0));manifests.append({"package":name,"path":str(path),"sha256":sha(path),"files":len(rows),"original_rows_preserved":len(prior[name])})
    need(sha(__file__)==original_script,"supplement source changed during execution")
    write(out/"RESULT.json",{"status":"PASS_PORTABLE_SAME_OWNED_BASELINE_FULL_GENERIC_CACHE_SUPPLEMENT","inference_calls":0,
        "source_first_PV_claimed":False,"script_sha256":original_script,"baseline_script_sha256":BASE_SHA,"pins_sha256":base.PIN_SHA256,
        "baseline_result":{"path":str(args.baseline/"RESULT.json"),"sha256":sha(args.baseline/"RESULT.json")},
        "baseline_cold_host_execution":old["cold_host_execution"],"uses_only_previously_bootstrapped_owned_toolchain_and_sources":True,
        "external_host_checkout_or_cache_map_used":False,"original_baseline_unchanged":True,
        "same_mathlib_source_pin":"71a80585ee495fc24472fd0eaffc89d94e4fd8d6","source_checks":source_checks,
        "cache_fetch_elapsed_seconds":cache_elapsed,"elapsed_seconds":time.monotonic()-started,"contexts":contexts,
        "original_cache_rows_preserved":sum(len(x)for x in prior.values()),"overwrites_restored":restored,"cache_manifests":manifests,
        "commands":commands,"trust":"Official generic binary-cache/compiler/runtime/OS/hardware contracts retained; not an all-source platform build or source-first PV.",
        "mathematical_premises":"Unchanged150core+DP4 baseline. DP3 criterion and DP2 numerical/analytic theorem parameters stay explicit; no numerical premise promoted to a fact."})
    print(json.dumps({"status":"PASS_PORTABLE_SAME_OWNED_BASELINE_FULL_GENERIC_CACHE_SUPPLEMENT","elapsed_seconds":time.monotonic()-started}))


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--baseline",type=Path);p.add_argument("--out",type=Path)
    p.add_argument("--memory-gib",type=int,choices=[32,64],default=32);p.add_argument("--scratch-gib",type=int,choices=[32,48,64],default=32)
    p.add_argument("--cpus",default=None);p.add_argument("--inside-scope",action="store_true",help=argparse.SUPPRESS);p.add_argument("--validate-pins",action="store_true")
    args=p.parse_args();need(sha(BASE)==BASE_SHA,"frozen portable baseline script changed");frozen=base.pins()
    if args.validate_pins:print(json.dumps({"status":"PASS_PORTABLE_FULL_GENERIC_SUPPLEMENT_PINS","base_sha256":BASE_SHA,"pins_sha256":base.PIN_SHA256,"inference_calls":0}));return
    need(args.baseline is not None and args.out is not None,"completed --baseline and fresh --out required")
    args.baseline,args.out=args.baseline.resolve(),args.out.resolve()
    need(not args.out.is_relative_to(args.baseline) and not args.baseline.is_relative_to(args.out),"supplement and baseline roots must be disjoint")
    if args.inside_scope:inside(args,frozen);return
    need(not args.out.exists() and args.baseline.is_dir(),"fresh supplement output and existing baseline required")
    mem={line.split(':')[0]:int(line.split()[1])*1024 for line in Path('/proc/meminfo').read_text().splitlines()}
    need(mem['MemAvailable']>=(args.memory_gib+16)*1024**3,"insufficient independently available RAM")
    need(shutil.disk_usage(args.out.parent).free>=args.scratch_gib*1024**3,"insufficient independent free disk")
    args.out.mkdir();unit="ieantn-full-generic-replay-"+uuid.uuid4().hex[:12]
    cpus=args.cpus or ','.join(map(str,sorted(os.sched_getaffinity(0))[:8]))
    command=["systemd-run","--user","--wait","--collect","--pipe","--unit="+unit,"--property=MemoryMax="+str(args.memory_gib)+"G","--property=MemorySwapMax=0","--property=LimitNOFILE=65536","--property=TasksMax=1024","/usr/bin/taskset","--cpu-list",cpus,sys.executable,"-I","-B",str(Path(__file__).resolve()),"--inside-scope","--baseline",str(args.baseline),"--out",str(args.out),"--memory-gib",str(args.memory_gib)]
    write(args.out/"INVOCATION.json",{"command":command,"script_sha256":sha(__file__),"baseline":str(args.baseline),"scratch_limit_gib":args.scratch_gib,"inference_calls":0})
    samples=[];disk=[]
    with(args.out/"scope.stdout").open('x')as stdout,(args.out/"scope.stderr").open('x')as stderr:
        proc=subprocess.Popen(command,stdout=stdout,stderr=stderr);cg=None;next_disk=0;events={}
        while proc.poll()is None:
            if cg is None:
                query=subprocess.run(['systemctl','--user','show',unit,'-p','ControlGroup','--value'],capture_output=True,text=True)
                if query.stdout.strip():cg=Path('/sys/fs/cgroup')/query.stdout.strip().lstrip('/')
            if cg is not None:
                try:samples.append(int((cg/'memory.current').read_text()));events=dict(line.split()for line in(cg/'memory.events').read_text().splitlines())
                except FileNotFoundError:pass
            if time.monotonic()>=next_disk:
                usage=subprocess.run(['/usr/bin/du','-sk',str(args.out)],capture_output=True,text=True);need(usage.returncode==0,"owned scratch accounting failed")
                allocated=int(usage.stdout.split()[0])*1024;disk.append(allocated)
                if allocated>args.scratch_gib*1024**3:subprocess.run(['systemctl','--user','stop',unit],check=True)
                next_disk=time.monotonic()+10
            time.sleep(.5)
    write(args.out/"RESOURCE_END.json",{"returncode":proc.wait(),"sampled_charged_memory_peak_lower_bound_bytes":max(samples,default=None),"exact_peak_available":False,"memory_events_last_observed":events,"sampled_allocated_disk_peak_bytes":max(disk,default=None),"disk_samples":disk,"memory_samples":samples})
    need(proc.returncode==0 and(args.out/'RESULT.json').is_file(),"full generic supplement failed; logs preserved")
    print("PASS_PORTABLE_SAME_OWNED_BASELINE_FULL_GENERIC_CACHE_SUPPLEMENT",args.out/'RESULT.json')


if __name__=='__main__':main()
