"""One controlled mutation in a disposable worktree: apply, observe, restore, verify.

usage: python mutate.py <worktree> <mutation-id> <spec.json>

spec = {"file": "<path in worktree>", "edit": {"op": "append"|"replace", "text"| "old"/"new": ...},
        "core": bool,                       # rebuild the core and run `fingerprint --check` / `gen-challenges --check`
        "projects": ["Solutions/X", ...],   # solution projects to build after the edit, in order
        "drift_projects": [...],            # projects whose `solution_drift` is queried (in-memory receipt at HEAD)
        "pin": {"attestation": "pv-evidence/...json"} | null,   # compare the edited file's sha256 with an attested pin
        "expect": "<free text: what should happen>"}

Nothing is committed and no receipt is written: `solution_drift` is called with a receipt dict built in memory.
The worktree must be clean (tracked files) before the run; the script refuses otherwise, and verifies afterwards
that the file's sha256 and `git status` are back to the initial state, then rebuilds the projects (restore build).
"""
import hashlib, json, pathlib, re, subprocess, sys, time

W = pathlib.Path(sys.argv[1]).resolve(); MID = sys.argv[2]; spec = json.load(open(sys.argv[3]))
STUDY = pathlib.Path(__file__).resolve().parent.parent
LOGD = STUDY / "evidence" / "mutations" / f"{MID}_{W.name}"; LOGD.mkdir(parents=True, exist_ok=True)
PY = "/ryu/hyunsik/playground/independence/ieantn_qrh/agentB/tools/bin/python"
GUARD = str(STUDY / "scripts" / "guarded_build.sh")


def sh(cmd, cwd=W, **kw):
    return subprocess.run(cmd, cwd=cwd, capture_output=True, text=True, **kw)


def sha(p):
    return hashlib.sha256((W / p).read_bytes()).hexdigest()


def status():
    return sh(["git", "status", "--porcelain", "--untracked-files=no"]).stdout.strip()


def build(project, tag):
    log = LOGD / f"{tag}_{project.replace('/', '_')}.log"
    line = sh([GUARD, str(log), str(W / project), "lake", "build"]).stdout.strip().splitlines()[-1]
    text = log.read_text(errors="replace")
    built = re.findall(r"Built ([A-Za-z0-9_.]+)", text)
    failed = re.findall(r"(?:✖|error:) .*?(?:Building|building) ([A-Za-z0-9_.]+)", text) + re.findall(r"^✖ \[\d+/\d+\] Building ([A-Za-z0-9_.]+)", text, re.M)
    errs = [l for l in text.splitlines() if l.startswith("error:")][:3]
    rc = int(re.search(r"rc=(\d+)", line).group(1)); wall = re.search(r"wall=([\d.]+)s", line).group(1)
    peak = re.search(r"max_single_rss=(\d+)GB", line).group(1)
    return {"project": project, "rc": rc, "wall_s": float(wall), "max_single_rss_gb": int(peak), "built": built,
            "built_count": len(built), "failed_modules": sorted(set(failed)), "first_errors": errs, "log": str(log.relative_to(STUDY))}


def core_checks(tag):
    out = {}
    b = sh([GUARD, str(LOGD / f"{tag}_core.log"), str(W), "lake", "build"]).stdout.strip().splitlines()[-1]
    out["core_build"] = b.split(" cmd=")[0]
    fp = sh([PY, "scripts/ieantn.py", "fingerprint", "--check"])
    out["fingerprint_check"] = {"rc": fp.returncode, "tail": (fp.stdout + fp.stderr).strip().splitlines()[-3:]}
    gc = sh([PY, "scripts/ieantn.py", "gen-challenges", "--check"])
    out["gen_challenges_check"] = {"rc": gc.returncode, "tail": (gc.stdout + gc.stderr).strip().splitlines()[-2:]}
    return out


def drift(projects):
    head = sh(["git", "rev-parse", "HEAD"]).stdout.strip()
    code = ("import sys, json; sys.path.insert(0, 'scripts'); import ieantn\n"
            f"head = {head!r}\n"
            f"for p in {projects!r}:\n"
            "    print(json.dumps([p, ieantn.solution_drift({'repository': {'commit': head}, 'solution': {'project': p}})]))\n")
    r = sh([PY, "-c", code])
    out = [json.loads(l) for l in r.stdout.splitlines() if l.startswith("[")] or [["error", r.stderr[-400:]]]
    # the same query through the patched upstream tool (remedy R1, worktree agentB/pv8_wtU), rooted at this worktree
    code2 = ("import sys, json, pathlib, importlib.util\n"
             "spec = importlib.util.spec_from_file_location('ieantn_patched', "
             "'/ryu/hyunsik/playground/independence/ieantn_qrh/agentB/pv8_wtU/scripts/ieantn.py')\n"
             "m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m); m._set_root(pathlib.Path('.').resolve())\n"
             f"head = {head!r}\n"
             f"for p in {projects!r}:\n"
             "    print(json.dumps(['patched:' + p, m.solution_drift({'repository': {'commit': head}, 'solution': {'project': p}})]))\n")
    r2 = sh([PY, "-c", code2])
    out += [json.loads(l) for l in r2.stdout.splitlines() if l.startswith("[")] or [["patched-error", r2.stderr[-400:]]]
    return out


def assess(keys):
    """Grade an in-memory receipt per conclusion: recorded = fingerprints committed at HEAD (the conclusion and its
    imports, as `record-receipt` would record them), environment = current, then `assess` against fingerprints
    recomputed now. No receipt file is written."""
    if not keys: return None
    head = sh(["git", "rev-parse", "HEAD"]).stdout.strip()
    code = ("import sys, json, subprocess; sys.path.insert(0, 'scripts'); import ieantn\n"
            f"keys = {keys!r}; head = {head!r}\n"
            "recorded = {}\n"
            "for p in subprocess.run(['git', 'ls-files', 'IEANTN/Nodes/*/*/fingerprints.json'], capture_output=True, text=True).stdout.split():\n"
            "    blob = subprocess.run(['git', 'show', head + ':' + p], capture_output=True, text=True).stdout\n"
            "    recorded.update(json.loads(blob or '{}'))\n"
            "nodes = ieantn.load_nodes(); now = ieantn.compute_fingerprints(); out = {}\n"
            "for k in keys:\n"
            "    nid, cid = k.rsplit('.', 1)\n"
            "    c = [c for c in ieantn.conclusions_of(nodes[nid]) if c.get('id') == cid][0]\n"
            "    wanted = [k] + [f\"{d.get('node')}.{d.get('conclusion')}\" for d in (c.get('imports') or [])]\n"
            "    r = {'statement': {n: recorded.get(n) for n in wanted}, 'repository': {'commit': head},\n"
            "         'environment': ieantn.current_environment()}\n"
            "    out[k] = list(ieantn.assess(k, r, now, consult_history=True))\n"
            "print(json.dumps(out))\n")
    r = sh([PY, "-c", code])
    lines = [l for l in r.stdout.splitlines() if l.startswith("{")]
    return json.loads(lines[-1]) if lines else {"error": (r.stderr or r.stdout)[-500:]}


def pin(spec_pin, path):
    if not spec_pin: return None
    a = json.loads(sh(["git", "show", f"HEAD:{spec_pin['attestation']}"]).stdout)
    pins = json.dumps(a)
    cur = sha(path)
    return {"attestation": spec_pin["attestation"], "current_sha256": cur[:16], "pinned_in_attestation": cur in pins}


rec = {"mutation": MID, "worktree": str(W), "head": sh(["git", "rev-parse", "HEAD"]).stdout.strip(),
       "file": spec["file"], "edit": spec["edit"], "expect": spec.get("expect"), "started": time.strftime("%FT%TZ", time.gmtime())}
if status():
    sys.exit(f"refusing: worktree not clean:\n{status()}")
f = W / spec["file"]; before = f.read_bytes(); rec["sha256_before"] = sha(spec["file"])
rec["pin_before"] = pin(spec.get("pin"), spec["file"])
e = spec["edit"]
if e["op"] == "append":
    f.write_bytes(before + e["text"].encode())
elif e["op"] == "replace":
    s = before.decode(); assert s.count(e["old"]) == 1, "edit target not unique"
    f.write_bytes(s.replace(e["old"], e["new"]).encode())
rec["sha256_after_edit"] = sha(spec["file"]); rec["diff"] = sh(["git", "diff", "--stat"]).stdout.strip()
rec["pin_after_edit"] = pin(spec.get("pin"), spec["file"])
if spec.get("core"):
    rec["core_after_edit"] = core_checks("edit")
    rec["assess_after_edit"] = assess(spec.get("assess", []))
rec["builds_after_edit"] = [build(p, "edit") for p in spec["projects"]]
rec["drift_after_edit"] = drift(spec.get("drift_projects", spec["projects"]))
# restore
f.write_bytes(before)
rec["sha256_restored"] = sha(spec["file"]); rec["restored_identical"] = rec["sha256_restored"] == rec["sha256_before"]
rec["status_after_restore"] = status() or "clean"
if spec.get("core"): rec["core_after_restore"] = core_checks("restore")
rec["builds_after_restore"] = [build(p, "restore") for p in spec["projects"]]
rec["drift_after_restore"] = drift(spec.get("drift_projects", spec["projects"]))
rec["finished"] = time.strftime("%FT%TZ", time.gmtime())
(LOGD / "record.json").write_text(json.dumps(rec, indent=1, ensure_ascii=False))
short = {k: rec[k] for k in ("mutation", "restored_identical", "status_after_restore")}
short["after_edit"] = [(b["project"], b["rc"], b["built_count"], b["failed_modules"][:3]) for b in rec["builds_after_edit"]]
short["after_restore"] = [(b["project"], b["rc"], b["built_count"]) for b in rec["builds_after_restore"]]
short["drift_after_edit"] = rec["drift_after_edit"]
if spec.get("core"):
    short["fingerprint_after_edit"] = rec["core_after_edit"]["fingerprint_check"]["rc"]
    short["assess_after_edit"] = rec.get("assess_after_edit")
print(json.dumps(short, ensure_ascii=False))
