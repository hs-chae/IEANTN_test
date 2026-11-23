#!/usr/bin/env python3
"""Select, check, archive and safely extract the public continuation source closure.

Only stage writes a fresh destination; the mathematical checkout is read-only.
Generic dependency libraries and application objects are never selected.
"""
from pathlib import Path, PurePosixPath
from html.parser import HTMLParser
from urllib.parse import urlsplit, unquote
import argparse, gzip, hashlib, json, os, re, shutil, stat, subprocess, tarfile

FAMILIES = ["BoxMellinInputs.v1", "RHSmoothingInputs.v1", "RHSmoothing.v1",
            "PrimeKernelInputs.v1", "PrimeInterval.v2", "PrimeQuantile.v1",
            "Lcm.v4", "Primorial.v2", "RamanujanGap.v3", "Nicolas.v1",
            "MertensRH.v1", "MobiusRH.v1", "RHPrimeCounting.v1"]
OMIT_PARTS = {".git", ".lake", "__pycache__", "memory", "human_input"}
OMIT_SUFFIXES = {".pyc", ".pyo", ".olean", ".ilean", ".o"}

def need(value, message):
    if not value:
        raise ValueError(message)

def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()

def strict(path):
    def pairs(rows):
        result = {}
        for key, value in rows:
            need(key not in result, "duplicate JSON key: " + key)
            result[key] = value
        return result
    def number(raw):
        value = float(raw)
        need(abs(value) != float("inf"), "overflowing JSON float")
        return value
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs,
                      parse_float=number,
                      parse_constant=lambda _: (_ for _ in ()).throw(ValueError("nonfinite JSON")))

def safe(raw):
    need(isinstance(raw, str) and raw and "\\" not in raw and "\0" not in raw,
         "invalid path spelling")
    p = PurePosixPath(raw)
    need(not p.is_absolute() and raw == p.as_posix() and all(x not in {"", ".", ".."} for x in p.parts),
         "unsafe/noncanonical path: " + raw)
    return p

def save(path, value):
    temp = path.with_name(path.name + ".pending")
    need(not temp.exists(), "preexisting pending metadata")
    temp.write_text(json.dumps(value, indent=2, allow_nan=False) + "\n")
    os.replace(temp, path)

def regular_files(root):
    files = []
    for path in root.rglob("*"):
        need(not path.is_symlink(), "symlink in source/archive tree: " + str(path))
        if path.is_file():
            need(stat.S_ISREG(path.stat().st_mode), "nonregular file")
            need(not any(x in OMIT_PARTS for x in path.relative_to(root).parts),
                 "private/runtime directory in final source tree: " + str(path))
            files.append(path)
    return sorted(files)

def stage(network, out):
    network = network.resolve()
    need(network.is_dir() and not out.exists(), "network missing or destination exists")
    selected = {}
    excluded_papers = {}
    def add(path, reason):
        need(path.is_file() and not path.is_symlink(), "missing or linked input: " + str(path))
        rel = path.relative_to(network).as_posix()
        safe(rel)
        if path.suffix.lower() == '.pdf' and '/evidence/literature/' in '/' + rel:
            excluded_papers[rel] = {'path': rel, 'bytes': path.stat().st_size, 'sha256': sha(path),
                'reason': 'Regenerable third-party paper download omitted from distribution; original local paper, source URL/SHA and download/review receipts are retained; no Lean compilation uses this PDF.'}
            return
        if any(x in OMIT_PARTS for x in Path(rel).parts) or path.suffix in OMIT_SUFFIXES:
            return
        selected.setdefault(rel, set()).add(reason)
    def tree(path, reason):
        need(path.is_dir(), "missing selected source tree: " + str(path))
        for child in sorted(path.rglob("*")):
            if any(x in OMIT_PARTS for x in child.relative_to(network).parts):
                continue
            if child.is_file():
                add(child, reason)
    s = network / "Solutions/RHContinuation.v1"
    tree(network / "IEANTN", "Canonical IEANTN core, including all thirteen family nodes")
    tree(s, "Current continuation scientific source, reports and execution evidence")
    for filename in ["IEANTN.lean", "lean-toolchain", "lakefile.toml", "lake-manifest.json", "LICENSE"]:
        add(network / filename, "Exact core build/dependency/license metadata")
    for filename in ['README.md', 'RH_CONTINUATION_HANDOFF.md']:
        if (network / filename).is_file():
            add(network / filename, 'Public repository/continuation handoff document')
    solution_families = []
    leaf_families = []
    for family in FAMILIES:
        path = network / "Solutions" / family
        if path.is_dir():
            tree(path, "Canonical public solution: " + family)
            solution_families.append(family)
        else:
            need(family in {"BoxMellinInputs.v1", "PrimeKernelInputs.v1"}, "missing public solution")
            leaf_families.append(family)
    base = network / "Solutions/RHExposureStudy.v1/Ramanujan640"
    tree(base, "Historical 146-module source and LeanCert checker replay prerequisite")
    # Preserve compact public summaries only; do not copy private sessions or research packets.
    old_reports = network / "Solutions/RHExposureStudy.v1/reports"
    if old_reports.is_dir():
        for p in sorted(old_reports.rglob("*")):
            if p.is_file() and p.suffix in {".html", ".pdf", ".json", ".md", ".csv", ".svg", ".png"}:
                add(p, "Historical public report; original primary outcome remains unchanged")
    historical_missing = []
    class HistoricalLinks(HTMLParser):
        def handle_starttag(self, tag, attrs):
            for key, value in attrs:
                if key not in {'href', 'src'} or not value:
                    continue
                url = urlsplit(value)
                if url.scheme or url.netloc or not url.path:
                    continue
                target = (old_reports / unquote(url.path)).resolve()
                if not target.is_relative_to(network):
                    continue
                rel = target.relative_to(network).as_posix()
                if target.is_file():
                    add(target, 'Direct historical public summary link; original bytes preserved')
                else:
                    historical_missing.append(rel)
    links = HistoricalLinks()
    if old_reports.is_dir():
        for report in old_reports.glob('RH_PROPAGATION_REPORT_*.html'):
            links.feed(report.read_text())
    for filename in ["README.md", "LOCKED_PRIMARY_OUTCOMES.json"]:
        p = network / "Solutions/RHExposureStudy.v1" / filename
        if p.is_file():
            add(p, "Historical public source/outcome identity")
    # Resolve the same active closure as the frozen actual-C replay, then include every
    # include_str payload relative to the source file that consumes it.
    b = s / "parabolic"
    pv = network / "Solutions/RamanujanSourcePV.v1"
    roots = [b, pv, network, s / "integration/source"]
    found = {}
    order = []
    def visit(module):
        if module == "Mathlib" or module.startswith(("Mathlib.", "Init", "Lean", "Std")) or module in found:
            return
        need(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*", module), "module name")
        candidates = ([network / "Solutions/RHSmoothingInputs.v1/Solution.lean"] if module == "Solution" else [])
        candidates += [root / (module.replace(".", "/") + ".lean") for root in roots]
        matches = [p for p in candidates if p.is_file()]
        need(matches, "missing C-log application source: " + module)
        p = matches[0]
        found[module] = p
        add(p, "Active actual-C source closure: " + module)
        for payload in re.findall(r'include_str\s+"([^"\n]+)"', p.read_text()):
            target = (p.parent / payload).resolve()
            need(target.is_relative_to(network), "include_str escapes selected checkout")
            add(target, "Actual include_str payload for " + module)
        for line in p.read_text().split("\n"):
            if line.startswith("import "):
                for dep in line[7:].split():
                    if dep.startswith("--"):
                        break
                    visit(dep)
        order.append(module)
    visit("Solution")
    need(len(order) == 46, "changed expected C-log active closure")
    need(len(solution_families) == 11 and len(leaf_families) == 2, "thirteen-family source coverage")
    for filename in ["README.md", "lean-toolchain"]:
        add(pv / filename, "Historical source-first C component identity and trust boundary")
    out.mkdir(parents=True)
    inventory = []
    for rel, reasons in sorted(selected.items()):
        src = network / rel
        before = sha(src)
        dst = out / "network" / rel
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(src, dst)
        need(sha(src) == before == sha(dst), "source changed while staging: " + rel)
        inventory.append({"path": rel, "bytes": dst.stat().st_size, "sha256": before, "selection_reasons": sorted(reasons)})
    source_inventory = {"schema": "RH_CONTINUATION_PUBLIC_SOURCE_SELECTION_V1", "network_base_commit":
        subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=network, text=True).strip(),
        "selection_rule_author": "Ivy continuation evidence-preparation helper, instructed by owner/root",
        "scope": "Complete current RHContinuation.v1 scientific source/evidence; canonical core; thirteen new node families with eleven real public solutions and two open analytic leaves; exact default replay prerequisites; selected old public summaries",
        "excluded": ["All .git/.lake/__pycache__ trees", "Private agent sessions/transcripts, memory, owner prompts and canaries", "Precompiled application/checker Lean objects", "Generic Mathlib/compiler libraries (exact pins and bootstrap documented separately)", "Unselected historical source families, recoverable from pinned published repository"],
        'downloaded_paper_PDFs_excluded_from_distribution': list(excluded_papers.values()),
        "public_solution_families": solution_families, "open_analytic_leaf_families_without_solution": leaf_families,
        "historical_summary_relative_links_absent_from_supplied_base": sorted(set(historical_missing)),
        "historical_missing_link_policy": 'Original reports/outcomes are preserved. These exact historical relative targets are absent in the supplied base; consult the published-history/source-pin references, rather than treating these links as working bundle files.',
        "actual_C_application_modules": [{"module": m, "path": found[m].relative_to(network).as_posix(), "sha256": sha(found[m])} for m in order],
        "files": inventory}
    save(out / "SOURCE_SELECTION.json", source_inventory)
    shutil.copyfile(Path(__file__).resolve(), out / "prepare_bundle.py")
    # Pinned package URLs belong to the manifest; no source discovery or unpinned update occurs.
    lake = strict(network / "lake-manifest.json")
    save(out / "GENERIC_DEPENDENCY_PINS.json", {"toolchain": (network / "lean-toolchain").read_text().strip(),
        "compiler_sha256": strict(s / "scripts/GENERIC_CONTEXT.json")["compiler_sha256"],
        "lake_manifest_sha256": sha(network / "lake-manifest.json"), "packages": lake["packages"]})
    print(json.dumps({"status": "STAGED_NOT_YET_REPLAYED_OR_FROZEN", "files": len(inventory), "bytes": sum(r["bytes"] for r in inventory), "source_modules_C_log": len(order)}))

def manifest(tree):
    rows = []
    for p in regular_files(tree):
        rel = p.relative_to(tree).as_posix()
        safe(rel)
        if rel == "BUNDLE_MANIFEST.json":
            continue
        need(not rel.endswith(".pending"), "pending file in final tree")
        rows.append({"path": rel, "bytes": p.stat().st_size, "sha256": sha(p)})
    save(tree / "BUNDLE_MANIFEST.json", {"schema": "STRICT_RELATIVE_FILE_HASH_MANIFEST_V1", "files": rows})
    return rows

def verify(tree):
    m = strict(tree / "BUNDLE_MANIFEST.json")
    need(m["schema"] == "STRICT_RELATIVE_FILE_HASH_MANIFEST_V1" and isinstance(m["files"], list), "manifest schema")
    names = set()
    for row in m["files"]:
        rel = safe(row["path"]).as_posix()
        need(rel not in names and rel != "BUNDLE_MANIFEST.json", "duplicate/reserved file")
        names.add(rel)
        need(type(row["bytes"]) is int and row["bytes"] >= 0 and re.fullmatch("[0-9a-f]{64}", row["sha256"]), "invalid file identity")
        p = tree / rel
        need(p.is_file() and not p.is_symlink() and p.stat().st_size == row["bytes"] and sha(p) == row["sha256"], "file hash/size mismatch: " + rel)
    actual = {p.relative_to(tree).as_posix() for p in regular_files(tree)} - {"BUNDLE_MANIFEST.json"}
    need(actual == names, "manifest membership differs")
    return len(names)

def pack(tree, out):
    count = verify(tree)
    need(not out.resolve().is_relative_to(tree.resolve()), "archive output must be outside source tree")
    need(not out.exists() and not out.with_name(out.name + ".pending").exists(), "fresh archive required")
    temp = out.with_name(out.name + ".pending")
    with temp.open('xb') as raw, gzip.GzipFile(filename='', mode='wb', fileobj=raw,
            compresslevel=6, mtime=0) as compressed, tarfile.open(fileobj=compressed,
            mode='w', format=tarfile.PAX_FORMAT) as tf:
        for p in regular_files(tree):
            rel = p.relative_to(tree).as_posix()
            info = tf.gettarinfo(str(p), arcname=rel)
            info.uid = 0; info.gid = 0; info.uname = ""; info.gname = ""; info.mtime = 0
            info.mode = 0o644
            with p.open("rb") as stream:
                tf.addfile(info, stream)
    os.replace(temp, out)
    receipt = {"schema": "RH_CONTINUATION_ARCHIVE_IDENTITY_V1", "archive": out.name, "bytes": out.stat().st_size,
               "sha256": sha(out), "manifest_sha256": sha(tree / "BUNDLE_MANIFEST.json"), "manifest_files": count}
    save(out.with_name(out.name + ".json"), receipt)
    print(json.dumps(receipt))

def extract(archive, out):
    need(not out.exists(), "fresh extraction destination required")
    # Inspect every member before writing anything. Never use tar extractall.
    with tarfile.open(archive, "r:gz") as tf:
        members = tf.getmembers()
        names = set()
        for member in members:
            safe(member.name)
            need(member.name not in names and member.isfile() and member.size >= 0,
                 "duplicate, linked or nonregular archive member")
            names.add(member.name)
        for name in names:
            need(not any(parent.as_posix() in names for parent in PurePosixPath(name).parents
                         if parent.as_posix() != "."), "file/directory archive prefix collision")
        need("BUNDLE_MANIFEST.json" in names, "archive manifest absent")
        out.mkdir(parents=True)
        for member in members:
            target = out / member.name
            target.parent.mkdir(parents=True, exist_ok=True)
            with tf.extractfile(member) as src, target.open("xb") as dst:
                shutil.copyfileobj(src, dst)
    print(json.dumps({"status": "PASS_STRICT_ARCHIVE_EXTRACTION_AND_ALL_FILE_HASHES", "files": verify(out)}))

def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    sub = parser.add_subparsers(dest="action", required=True)
    p = sub.add_parser("stage", allow_abbrev=False); p.add_argument("--network", type=Path, required=True); p.add_argument("--out", type=Path, required=True)
    for action in ["seal", "verify"]:
        p = sub.add_parser(action, allow_abbrev=False); p.add_argument("--tree", type=Path, required=True)
    p = sub.add_parser("pack", allow_abbrev=False); p.add_argument("--tree", type=Path, required=True); p.add_argument("--out", type=Path, required=True)
    p = sub.add_parser("extract", allow_abbrev=False); p.add_argument("--archive", type=Path, required=True); p.add_argument("--out", type=Path, required=True)
    a = parser.parse_args()
    if a.action == "stage": stage(a.network, a.out)
    elif a.action == "seal": print(json.dumps({"status": "MANIFEST_SEALED", "files": len(manifest(a.tree))}))
    elif a.action == "verify": print(json.dumps({"status": "PASS_ALL_FILE_HASHES", "files": verify(a.tree)}))
    elif a.action == "pack": pack(a.tree, a.out)
    elif a.action == "extract": extract(a.archive, a.out)

if __name__ == "__main__":
    main()
