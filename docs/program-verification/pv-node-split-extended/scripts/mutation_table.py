"""Summarise every mutation record (evidence/mutations/*/record.json) as a Markdown table and a JSON digest."""
import json, pathlib, re, sys

E = pathlib.Path(__file__).resolve().parent.parent / "evidence" / "mutations"
rows = []
for rec_path in sorted(E.glob("*/record.json")):
    r = json.loads(rec_path.read_text())
    mid = r["mutation"]; world = mid.rsplit("_", 1)[1]
    ed = r["builds_after_edit"]; rs = r["builds_after_restore"]
    def mods(b):
        names = [m.split(".")[-1] if m.count(".") > 1 else m for m in b["built"]]
        return f"{b['built_count']}" + (f" ({', '.join(names[:6])}{'…' if len(names) > 6 else ''})" if names else "")
    edit = "; ".join(f"`{pathlib.PurePosixPath(b['project']).name}` rc={b['rc']}, built {mods(b)}, {b['wall_s']:.0f} s"
                     + (f", fails in {b['failed_modules'][:2]}" if b["failed_modules"] else "") for b in ed)
    restore = "; ".join(f"rc={b['rc']}, built {b['built_count']}, {b['wall_s']:.0f} s" for b in rs)
    drift = {d[0]: d[1] for d in r["drift_after_edit"] if isinstance(d, list) and len(d) == 2}
    own = [p for p in drift if not p.startswith("patched:") and p.startswith("Solutions/PVMatch") or p in ("Solutions/DudekPlattNumerics.v5", "Solutions/RamanujanGap.v3")]
    def short(note):
        if note is None: return "none"
        m = re.search(r"\((.*)\); the receipt", note); return "reported: " + (m.group(1) if m else note[:60])
    own_txt = "; ".join(f"{pathlib.PurePosixPath(p).name}: {short(drift[p])}" for p in own if p in drift)
    other_txt = "; ".join(f"{pathlib.PurePosixPath(p).name}: {short(drift[p])}" for p in drift
                          if not p.startswith("patched:") and p not in own)
    patched_txt = "; ".join(f"{pathlib.PurePosixPath(p[8:]).name}: {short(drift[p])}" for p in drift
                            if p.startswith("patched:") and p[8:] in own)
    fp = r.get("core_after_edit", {}).get("fingerprint_check", {})
    fp_txt = ("rc=%s %s" % (fp.get("rc"), " ".join(fp.get("tail", []))[-160:])) if fp else "n/a (no statement edited)"
    assess = r.get("assess_after_edit")
    pin = r.get("pin_after_edit")
    rows.append({"mutation": mid, "world": world, "file": r["file"], "expect": r.get("expect"),
                 "after_edit": edit, "restore": restore, "restored_identical": r["restored_identical"],
                 "status_after_restore": r["status_after_restore"], "drift_own_project": own_txt,
                 "drift_other_projects": other_txt, "drift_patched_tool": patched_txt, "fingerprint_check": fp_txt,
                 "assess": assess, "attestation_pin_still_matches": (pin or {}).get("pinned_in_attestation"),
                 "sha_before": r["sha256_before"][:12], "sha_after_edit": r["sha256_after_edit"][:12]})
json.dump(rows, open(E / "DIGEST.json", "w"), indent=1, ensure_ascii=False)
print("| Mutation | Layout | After the edit (per project) | Restore | Drift, node's own project (current tool) | Drift, same query, patched tool | Statement fingerprints | Receipt grade (in memory) | Attestation pin |")
print("|---|---|---|---|---|---|---|---|---|")
for x in rows:
    a = x["assess"]; a_txt = "; ".join(f"{k.split('.')[0]}: {v[0]}" for k, v in a.items()) if isinstance(a, dict) and "error" not in a else ("n/a" if not a else str(a)[:80])
    print(f"| {x['mutation'].rsplit('_',1)[0]} | {x['world']} | {x['after_edit']} | {x['restore']}; bytes restored: {x['restored_identical']}; tree {x['status_after_restore']} | {x['drift_own_project'] or 'n/a'} | {x['drift_patched_tool'] or 'n/a'} | {x['fingerprint_check']} | {a_txt} | {x['attestation_pin_still_matches'] if x['attestation_pin_still_matches'] is not None else 'n/a'} |")
