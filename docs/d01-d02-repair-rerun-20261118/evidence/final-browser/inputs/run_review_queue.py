#!/usr/bin/env python3
"""Dedicated up-to-three common-evaluation queue; default is read-only checking.

No candidate mathematical payload is read to select/stop a run. --run requires
an exact independent ROOT queue authorization. It never uses a three-arm block.
"""
from pathlib import Path
import argparse
from concurrent.futures import ThreadPoolExecutor
import fcntl
import importlib.util
import json
import math
import os
import signal
import subprocess
import sys
import time
sys.dont_write_bytecode = True

S = Path(__file__).resolve().parents[1]


def module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    result = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(result)
    return result


review = module("common_review_queue_role", S / "scripts/review_controller.py")
resources = module("common_review_existing_resource_helpers", S / "scripts/run_block_v2.py")
need, load, sha, pin, write = review.need, review.load, review.sha, review.pin, review.atomic_new
stop_requested = False
GiB = 1024 ** 3


def stop(number, frame):
    global stop_requested
    stop_requested = True


def validate(queue_path, start_path=None):
    queue = load(queue_path)
    need(queue.get("schema") == "DEEP_TERTIARY_COMMON_EVALUATION_QUEUE_V1" and queue.get("role") == "EVALUATION",
         "dedicated common evaluation queue required")
    need(queue.get("resources") == review.BUDGET and queue.get("quota_admission_used_percent") == 90 and
         queue.get("model") == "gpt-6.2-sol" and queue.get("effort") == "high", "review queue common resources/model/quota differ")
    need(queue.get("concurrency") in {1, 3}, "review concurrency must be one or three")
    need(pin(queue["runtime_manifest"]) == review.RUNTIME and pin(queue["instructions"]) == review.INSTRUCTIONS,
         "review queue must use common environment/instructions")
    need(pin(queue["resource_helper"]) == S / "scripts/run_block_v2.py", "review resource helper differs")
    review.validate_selection_policy(queue["selection_policy"])
    gate = review.validate_main_gate(queue["all_main_submissions_gate"])
    entries = queue.get("entries", [])
    need(0 < len(entries) <= 24, "bounded review queue required")
    ids = set()
    primary_candidates = set()
    primary_sources = set()
    counts = {"PRIMARY": 0, "INDEPENDENT": 0}
    for row in entries:
        need(isinstance(row.get("review_id"), str) and row["review_id"].startswith("EVAL-") and
             row["review_id"].replace("-", "").isalnum() and row["review_id"] not in ids, "unique anonymous review id required")
        ids.add(row["review_id"])
        need(row.get("review_kind") in counts, "review kind")
        counts[row["review_kind"]] += 1
        if row["review_kind"] == "PRIMARY":
            need(row["candidate_id"] not in primary_candidates, "primary candidate repeated in review queue")
            primary_candidates.add(row["candidate_id"])
        packet = load(pin(row["packet_manifest"]))
        context = review.validate_packet_contract(Path(packet["root"]),load(review.RUNTIME))
        need(context["candidate_id"] == row["candidate_id"] and context["review_kind"] == row["review_kind"], "queue/candidate association differs")
        binding = load(pin(row["candidate_binding"]))
        if row["review_kind"] == "PRIMARY":
            need(binding.get("source_run_id") not in primary_sources, "original source run repeated in primary review queue")
            primary_sources.add(binding.get("source_run_id"))
        need(binding.get("status") == "PASS_ONE_LOCKED_WITHIN_BUDGET_SUBMISSION_SELECTED" and
             binding.get("packet_manifest_sha256") == row["packet_manifest"]["sha256"] and
             binding.get("candidate_id") == row["candidate_id"] and binding.get("new_posthoc_proof_added") is False and
             binding.get("original_payload_bytes_unchanged") is True, "candidate is not original locked in-budget proof")
        selected = [r for r in gate["runs"] if r["run_id"] == binding.get("source_run_id")]
        need(len(selected) == 1 and selected[0]["slot_state"] == "EXECUTED_DRAINED" and selected[0].get("locked_submission") is not None,
             "review selected an unstarted slot or a slot without eligible locked evidence")
        review.validate_candidate_binding(binding,gate,pin(row["packet_manifest"]))
        receipt = load(pin(row["preflight"]))
        need(receipt.get("status") == "PASS_COMMON_EVALUATION_EXACT_PACKET_OS_AND_REVIEW_TOOL_FIXTURE" and
             receipt.get("runtime_manifest_sha256") == queue["runtime_manifest"]["sha256"] and
             receipt.get("packet_manifest_sha256") == row["packet_manifest"]["sha256"] and
             receipt.get("controller_sha256") == sha(S / "scripts/review_controller.py") and
             receipt.get("preflight_sha256") == sha(S / "scripts/review_preflight.py") and
             receipt.get("review_instructions_sha256") == sha(review.INSTRUCTIONS) and
             receipt.get("common_checklist_sha256") == sha(review.CHECKLIST), "exact review preflight differs")
    need(counts["PRIMARY"] <= 18 and counts["INDEPENDENT"] <= 6, "fixed eighteen plus six review allowances exceeded")
    if start_path:
        root = load(start_path)
        need(root.get("schema") == "DEEP_TERTIARY_COMMON_EVALUATION_QUEUE_ROOT_REVIEW_V1" and
             root.get("status") == "ROOT_REVIEWED_COMMON_EVALUATION_QUEUE_START_AUTHORIZED" and root.get("reviewed_by") == "/root",
             "separate root-reviewed evaluation queue start required")
        need(pin(root["queue"]) == queue_path and root.get("launcher_sha256") == sha(__file__) and
             root.get("controller_sha256") == sha(S / "scripts/review_controller.py") and
             root.get("preflight_sha256") == sha(S / "scripts/review_preflight.py"), "root review binds different queue/source")
        need(root.get("all_main_submissions_gate") == queue["all_main_submissions_gate"] and
             root.get("no_automatic_retry") is True and root.get("no_primary_outcome_rescoring") is True and
             root.get("same_common_environment_for_all_origins") is True, "root review preservation/common policy differs")
        need(root.get("independent_selection_policy") == "STRONGEST_OR_DISPUTED_UNDER_COMMON_CHECKLIST_NOT_ORIGIN_ARM", "independent selection policy differs")
        need(gate.get("fixture_only") is not True and all(load(pin(row["preflight"])).get("fixture_only") is not True and
             load(pin(row["candidate_binding"])).get("fixture_only") is not True for row in entries), "synthetic fixtures cannot authorize a review queue")
    return queue


def reserve_one(review_id):
    registry_root = resources.GLOBAL_ADMIN
    registry_root.mkdir(exist_ok=True)
    handle = (registry_root / "allocations.lock").open("a")
    fcntl.flock(handle, fcntl.LOCK_EX)
    registry = registry_root / "allocations.json"
    try:
        document = load(registry) if registry.exists() else {"schema": "EXPOSURE_LONGCHAIN_RESOURCE_ALLOCATIONS_V1", "allocations": []}
        need(document.get("schema") == "EXPOSURE_LONGCHAIN_RESOURCE_ALLOCATIONS_V1", "shared administrative resource schema")
        active = [r for r in document["allocations"] if resources.unit_alive(r)]
        ours = [r for r in active if r.get("participant") == "A"]
        for rows, memory_cap, cpu_cap, scratch_cap in [(active,384,48,300),(ours,192,24,150)]:
            need(sum(r["memory_bytes"] for r in rows) + 64*GiB <= memory_cap*GiB and
                 sum(r["cpus"] for r in rows) + 8 <= cpu_cap and
                 sum(r["scratch_bytes"] for r in rows) + 25*GiB <= scratch_cap*GiB, "global/A review reservation unavailable")
        slots = [list(range(start,start+8)) for start in [32,40,48]]
        available = [slot for slot in slots if set(slot).issubset(os.sched_getaffinity(0)) and
                     all(not set(slot).intersection(r["CPU_affinity"]) for r in active)]
        need(bool(available), "review CPU affinity unavailable")
        cpus = available[0]
        need(resources.host_available() >= (512+64)*GiB + sum(r["memory_bytes"] for r in active), "review host RAM headroom unavailable")
        import shutil
        need(shutil.disk_usage(S).free >= (1024+300)*GiB, "review free disk headroom unavailable")
        unit = "ieantn-a-review-" + __import__("hashlib").sha256((str(S)+":"+review_id).encode()).hexdigest()[:16] + ".service"
        row = {"participant":"A","run":review_id,"unit":unit,"cgroup":None,"memory_bytes":64*GiB,"cpus":8,"CPU_affinity":cpus,"scratch_bytes":25*GiB}
        document["allocations"] = [r for r in document["allocations"] if r.get("participant") != "A" or resources.unit_alive(r)] + [row]
        resources.atomic(registry,document)
        return handle,row
    except BaseException:
        handle.close()
        raise


def quota(directory):
    raw = directory / "QUOTA_AND_MODEL_CATALOG_RAW.json"
    command = [sys.executable,"-I","-B",str(S/"scripts/review_controller.py"),"--catalog-only",str(raw)]
    run = subprocess.run(command,capture_output=True,text=True,timeout=70)
    (directory/"quota.stdout").write_text(run.stdout);(directory/"quota.stderr").write_text(run.stderr)
    need(run.returncode == 0 and raw.is_file(),"fresh review quota query unavailable; no review launched")
    document=load(raw)
    need(any(r.get("id")=="gpt-6.2-sol" for r in document.get("catalog",{}).get("data",[])),"fixed review model not offered")
    limits=document.get("rate_limits",{});window=limits.get("rateLimits",{}).get("primary")
    if not isinstance(window,dict):window=limits.get("rateLimitsByLimitId",{}).get("codex",{}).get("primary")
    need(isinstance(window,dict) and window.get("windowDurationMins")==10080,"weekly review quota unavailable")
    used=window.get("usedPercent")
    need(isinstance(used,(int,float)) and not isinstance(used,bool) and math.isfinite(used) and 0<=used<=100,"invalid review quota")
    document.update(observed_unix=time.time(),review_admission_used_percent=used,raw_capacity_receipt={"path":str(raw),"sha256":sha(raw)})
    path=directory/"QUOTA_ADMISSION.json";write(path,document)
    return used,path


def stop_and_drain_owned(reservation,process):
    """Bounded whole-unit stop, including a timeout in systemctl itself."""
    try:resources.ctl("--no-block","stop",reservation["unit"])
    except (subprocess.TimeoutExpired,OSError):pass
    try:process.wait(timeout=3)
    except subprocess.TimeoutExpired:pass
    try:alive=resources.unit_alive(reservation)
    except (subprocess.TimeoutExpired,OSError):alive=True
    if process.poll() is not None and not alive:return
    try:resources.ctl("kill","--kill-who=all","--signal=SIGKILL",reservation["unit"])
    except (subprocess.TimeoutExpired,OSError):pass
    # The cached, observed cgroup is an additional whole-owned-unit fallback.
    raw=reservation.get("cgroup")
    if isinstance(raw,str) and raw.startswith("/"):
        group=(Path("/sys/fs/cgroup")/raw.lstrip("/")).resolve()
        if group.is_relative_to("/sys/fs/cgroup") and reservation["unit"] in group.parts:
            try:(group/"cgroup.kill").write_text("1\n")
            except OSError:pass
    try:process.wait(timeout=3)
    except subprocess.TimeoutExpired:
        process.terminate()
        try:process.wait(timeout=1)
        except subprocess.TimeoutExpired:process.kill();process.wait(timeout=1)
    try:alive=resources.unit_alive(reservation)
    except (subprocess.TimeoutExpired,OSError):alive=True
    need(not alive,"owned review whole-unit cleanup could not confirm drain; reservation retained")


def start_entry(args, queue_path, queue, entry, directory, capacity):
    run_out=S/"runs-evaluation"/entry["review_id"]
    need(not run_out.exists(),"review already started; no automatic retry")
    # One shared ledger enforces total primary/independent slots across queues.
    ledger_path=S/"resources/common-evaluation-admissions.json"
    with (S/"resources/common-evaluation-admissions.lock").open("a") as ledger_lock:
        fcntl.flock(ledger_lock,fcntl.LOCK_EX)
        ledger=load(ledger_path) if ledger_path.exists() else {"entries":[]}
        need(all(r["review_id"]!=entry["review_id"] for r in ledger["entries"]),"review slot already admitted")
        cap=18 if entry["review_kind"]=="PRIMARY" else 6
        need(sum(r["review_kind"]==entry["review_kind"] for r in ledger["entries"])<cap,"total review session allowance exhausted")
        if entry["review_kind"]=="PRIMARY":need(not any(r["review_kind"]=="PRIMARY" and r["candidate_id"]==entry["candidate_id"] for r in ledger["entries"]),"primary candidate already reviewed")
        source_run_id=load(pin(entry["candidate_binding"]))["source_run_id"]
        if entry["review_kind"]=="PRIMARY":need(not any(r["review_kind"]=="PRIMARY" and r.get("source_run_id")==source_run_id for r in ledger["entries"]),"original source run already received primary review")
        lease,reservation=reserve_one(entry["review_id"])
        process=None;stdout=None;stderr=None
        try:
            ledger["entries"].append({"review_id":entry["review_id"],"review_kind":entry["review_kind"],"candidate_id":entry["candidate_id"],"source_run_id":source_run_id,"queue_sha256":sha(queue_path),"unit":reservation["unit"]})
            resources.atomic(ledger_path,ledger)
            lock={"schema":"DEEP_TERTIARY_EVALUATION_EXECUTION_LOCK_V1","status":"ROOT_REVIEWED_EVALUATION_START_AUTHORIZED","reviewed_by":"/root","role":"EVALUATION","run_id":entry["review_id"],"candidate_id":entry["candidate_id"],"review_kind":entry["review_kind"],"resources":review.BUDGET,"model":"gpt-6.2-sol","effort":"high","packet_manifest":entry["packet_manifest"],"runtime_manifest":queue["runtime_manifest"],"instructions":queue["instructions"],"preflight":entry["preflight"],"candidate_binding":entry["candidate_binding"],"all_main_submissions_gate":queue["all_main_submissions_gate"],"quota_receipt":{"path":str(capacity),"sha256":sha(capacity)},"queue_root_review":{"path":str(args.reviewed_start_file.resolve()),"sha256":sha(args.reviewed_start_file)},"source_pins":[{"path":str(S/"scripts"/name),"sha256":sha(S/"scripts"/name)} for name in ["review_controller.py","review_preflight.py","run_review_queue.py","native_controller_v2.py","run_block_v2.py","isolation_preflight_v2.py"]]+[{"path":str(review.CHECKLIST),"sha256":sha(review.CHECKLIST)}],"continuation_policy":"STOP_AFTER_FIRST_COMPLETED_REVIEW_NO_DISCOVERY_CONTINUATION"}
            execution=directory/"EXECUTION_LOCK.json";write(execution,lock)
            command=["systemd-run","--user","--wait","--collect","--pipe","--unit="+reservation["unit"],"--property=MemoryMax=64G","--property=MemorySwapMax=0","--property=TasksMax=512","--property=LimitNOFILE=65536","--property=KillMode=control-group","--property=TimeoutStopSec=15","--property=RuntimeMaxSec=3720","--setenv=PATH="+os.environ["PATH"],"/usr/bin/taskset","--cpu-list",','.join(map(str,reservation["CPU_affinity"])),sys.executable,"-I","-B",str(S/"scripts/review_controller.py"),"--run","--packet-manifest",str(pin(entry["packet_manifest"])),"--runtime",str(review.RUNTIME),"--lock",str(execution),"--out",str(run_out)]
            write(directory/"COMMAND.json",command)
            stdout=(directory/"controller.stdout").open("x");stderr=(directory/"controller.stderr").open("x")
            process=subprocess.Popen(command,stdout=stdout,stderr=stderr)
            for _ in range(200):
                if resources.unit_alive(reservation):break
                need(process.poll() is None,"review unit exited before registration")
                time.sleep(.05)
            need(resources.unit_alive(reservation),"review unit did not become visible while reservation lock held")
            group=resources.ctl("show",reservation["unit"],"--property=ControlGroup","--value").stdout.strip()
            need(group.startswith("/"),"owned review cgroup was not observed")
            reservation["cgroup"]=group
            document=load(resources.GLOBAL_ADMIN/"allocations.json")
            matching=[r for r in document["allocations"] if r.get("participant")=="A" and r.get("unit")==reservation["unit"]]
            need(len(matching)==1,"owned review reservation disappeared")
            matching[0]["cgroup"]=group
            resources.atomic(resources.GLOBAL_ADMIN/"allocations.json",document)
        except BaseException:
            try:
                if process is not None:stop_and_drain_owned(reservation,process)
            finally:
                for stream in [stdout,stderr]:
                    if stream is not None:stream.close()
            raise
        finally:lease.close()
    return process,stdout,stderr,reservation,run_out


def monitor_entry(entry,directory,state):
    process,stdout,stderr,reservation,run_out=state
    try:
        samples=[];started=time.monotonic()
        while process.poll() is None:
            sample=resources.cgroup_sample(reservation["unit"]);samples.append(sample)
            if stop_requested:resources.ctl("stop",reservation["unit"])
            time.sleep(.5)
        code=process.wait();stdout.close();stderr.close()
        need(not resources.unit_alive(reservation),"owned review unit did not drain")
        write(directory/"RESOURCE_SAMPLES.json",samples)
        result=load(run_out/"result.json") if (run_out/"result.json").exists() else {}
        summary={"review_id":entry["review_id"],"candidate_id":entry["candidate_id"],"review_kind":entry["review_kind"],"returncode":code,"elapsed_seconds":time.monotonic()-started,"review_execution_admissible":result.get("review_execution_admissible",False),"mathematical_outcome":"NOT_READ_OR_INFERRED_BY_LAUNCHER","sampled_charged_memory_peak_lower_bound_bytes":max((r.get("memory.current",0) or 0 for r in samples),default=0),"exact_peak_available":any(r.get("memory.peak") is not None for r in samples),"OOM_events_last_observed":next((r.get("memory.events") for r in reversed(samples) if r.get("memory.events") is not None),None),"host_output_usage":resources.owned_file_usage(directory),"private_scratch_metadata_recorded_in_samples":True,"execution_drained":True,"no_automatic_retry":True,"infrastructure_error":result.get("infrastructure_error")}
        write(directory/"RECEIPT.json",summary)
        return summary
    finally:
        try:stop_and_drain_owned(reservation,process)
        finally:stdout.close();stderr.close()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--queue",type=Path,required=True);p.add_argument("--reviewed-start-file",type=Path)
    p.add_argument("--run",action="store_true");p.add_argument("--check",action="store_true")
    p.add_argument("--out",type=Path)
    args=p.parse_args();need(not(args.run and args.check),"run/check modes exclusive")
    queue_path=args.queue.resolve();queue=validate(queue_path,args.reviewed_start_file)
    if not args.run:
        print(json.dumps({"status":"PASS_DEDICATED_REVIEW_QUEUE_NO_INFERENCE","entries":len(queue["entries"]),"concurrency":queue["concurrency"],"model_calls":0}));return
    need(args.reviewed_start_file is not None,"root-reviewed queue start file required")
    need(args.out is not None,"fresh review queue output required")
    out=args.out.resolve();need(out.is_relative_to(S/"resources") and not out.exists(),"fresh own review queue output required")
    out.mkdir();signal.signal(signal.SIGTERM,stop);signal.signal(signal.SIGINT,stop)
    rows=[];operational_stop=False
    for offset in range(0,len(queue["entries"]),queue["concurrency"]):
        if stop_requested or operational_stop:break
        batch=queue["entries"][offset:offset+queue["concurrency"]]
        batch_out=out/("batch-"+str(offset//queue["concurrency"]+1).zfill(2));batch_out.mkdir()
        used,capacity=quota(batch_out)
        if used>=90:
            write(batch_out/"STOPPED.json",{"status":"QUOTA90_REVIEW_BATCH_NOT_STARTED","used_percent":used,"model_calls":0});break
        # Start in fixed anonymous order; resource/ledger locks serialize admission.
        # Complete the whole batch before the next quota query; no M feedback.
        with ThreadPoolExecutor(max_workers=len(batch)) as pool:
            futures=[]
            for entry in batch:
                directory=batch_out/entry["review_id"];directory.mkdir()
                try:
                    state=start_entry(args,queue_path,queue,entry,directory,capacity)
                    future=pool.submit(monitor_entry,entry,directory,state)
                except Exception as error:
                    from concurrent.futures import Future
                    future=Future();future.set_exception(error)
                    operational_stop=True
                futures.append((entry,directory,future))
                if operational_stop:break
            for entry,directory,future in futures:
                try:
                    row=future.result()
                except Exception as error:
                    row={"review_id":entry["review_id"],"candidate_id":entry["candidate_id"],"review_kind":entry["review_kind"],"status":"OPERATIONAL_REVIEW_LAUNCH_OR_RESOURCE_FAILURE","error_type":type(error).__name__,"error":str(error),"no_automatic_retry":True,"mathematical_outcome":"NOT_ASSESSED_BY_LAUNCHER"}
                    if not(directory/"RECEIPT.json").exists():write(directory/"RECEIPT.json",row)
                    operational_stop=True
                rows.append(row)
                if row.get("returncode",0)!=0 or row.get("infrastructure_error"):operational_stop=True
    write(out/"QUEUE_RESULT.json",{"status":"COMMON_REVIEW_QUEUE_STOPPED_OR_DRAINED_NO_MATH_AGGREGATION","rows":rows,"concurrency":queue["concurrency"],"origin_arms_read":False,"new_discovery_attempted":False,"no_automatic_retry":True})
    print(json.dumps({"status":"COMMON_REVIEW_QUEUE_STOPPED_OR_DRAINED","reviews_drained_or_closed":len(rows)}))


if __name__=="__main__":main()
