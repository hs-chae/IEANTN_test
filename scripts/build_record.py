"""`python scripts/ieantn.py build-record <node>`: compile a solution, record what it proves and
what it rests on.

A conclusion whose Lean proof has no Comparator receipt -- `lean-noncompliant` -- is otherwise
checked by nothing in this repository: `check` sees only that `Solutions/<node>/Solution.lean`
exists, and CI builds statements, not solutions. This writes one file per conclusion,
`build-records/<Node>.<conclusion>.json`, recording:

* whether the solution compiled. Every Lean file that embeds another file with `include_str` is
  recompiled first, because Lake tracks a module's own source and imports but not the files it
  reads with `include_str`, and would otherwise replay a build made from an older program;
* whether the solution theorem states exactly the generated challenge, up to binder names;
* every axiom in the proof: the three standard ones, each `native_decide` step with the
  proposition it decided, and anything else (which fails the record);
* the SHA-256 of every file the proof was built from: each non-library Lean module the solution
  imports, each file embedded with `include_str`, and the Lake configuration of every package. A
  package Lake fetched (LeanCert, say) is pinned by its revision in a hashed `lake-manifest.json`
  and named in the record, rather than hashed file by file.

`check` recomputes those hashes on every run, so an edit to any of those files makes the record
stale until this command is run again. A record is not a receipt. It says that the proof compiled
here and states its challenge; it does not say that Comparator accepted it, and a `native_decide`
step it lists is trusted, not checked by the kernel.
"""

from __future__ import annotations

import datetime as _dt
import json
import os
import pathlib
import re
import shutil
import subprocess
import tempfile
import time

import ieantn

SCHEMA = "ieantn-build-record/1"
NOTICE = (
    "Local build record written by `python scripts/ieantn.py build-record`. It says that this "
    "proof compiled here and states its challenge. It is not a Comparator receipt."
)
EXTRACTOR = pathlib.Path(__file__).resolve().parent / "BuildRecordExtract.lean"
STANDARD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})
#: `include_str "a"/"b"/"c.c"`: the path is string literals joined by `/`, relative to the file.
INCLUDE_STR = re.compile(r'include_str\s+((?:"[^"\n]*"\s*/\s*)*"[^"\n]*")')
#: Lake configuration that decides what a package builds against.
LAKE_CONFIG = ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain")
BUILD_TIMEOUT = 8 * 3600
EXTRACT_TIMEOUT = 3600


def run(command: list[str], cwd: pathlib.Path, timeout: int) -> tuple[int, str, float]:
    start = time.time()
    try:
        done = subprocess.run(command, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        return done.returncode, done.stdout + done.stderr, time.time() - start
    except subprocess.TimeoutExpired:
        return 124, "timed out", time.time() - start
    except FileNotFoundError as error:
        return 127, str(error), time.time() - start


def shown(path: pathlib.Path) -> str:
    """A path as a record shows it: relative to the repository, never a machine's absolute path."""
    resolved = path.resolve()
    root = ieantn.ROOT.resolve()
    return resolved.relative_to(root).as_posix() if resolved.is_relative_to(root) else str(path)


# ---------------------------------------------------------------------------
# Packages, modules and the files they embed
# ---------------------------------------------------------------------------


def required_packages(project: pathlib.Path) -> list[pathlib.Path]:
    """`project` and every package it requires by `path`, transitively, read from `lakefile.toml`."""
    seen: list[pathlib.Path] = []
    stack = [project.resolve()]
    while stack:
        package = stack.pop()
        if package in seen:
            continue
        seen.append(package)
        config = package / "lakefile.toml"
        if not config.is_file():
            continue
        for block in re.split(r"^\s*\[\[", config.read_text(encoding="utf-8"), flags=re.M):
            if block.startswith("require]]"):
                found = re.search(r'^\s*path\s*=\s*"([^"]+)"', block, re.M)
                if found:
                    stack.append((package / found.group(1)).resolve())
    return seen


def source_dirs(package: pathlib.Path) -> list[pathlib.Path]:
    """Where a package's modules live: the package itself, plus any `srcDir` it declares."""
    dirs = [package]
    config = package / "lakefile.toml"
    if config.is_file():
        for found in re.finditer(r'^\s*srcDir\s*=\s*"([^"]+)"', config.read_text(encoding="utf-8"),
                                 re.M):
            dirs.append((package / found.group(1)).resolve())
    return dirs


def package_lean_files(package: pathlib.Path) -> list[pathlib.Path]:
    """The package's own `.lean` files: no build outputs, and nothing in a nested package."""
    files: list[pathlib.Path] = []
    for directory, subdirs, names in os.walk(package):
        here = pathlib.Path(directory)
        subdirs[:] = sorted(
            name for name in subdirs
            if not name.startswith(".")
            and not any((here / name / config).is_file() for config in ("lakefile.toml",
                                                                         "lakefile.lean")))
        files += [here / name for name in sorted(names) if name.endswith(".lean")]
    return files


def embedded_paths(lean_file: pathlib.Path) -> list[pathlib.Path]:
    """Every file `lean_file` names in an `include_str`, resolved against its directory."""
    text = lean_file.read_text(encoding="utf-8", errors="replace")
    if "include_str" not in text:
        return []
    paths = []
    for found in INCLUDE_STR.finditer(text):
        pieces = re.findall(r'"([^"\n]*)"', found.group(1))
        paths.append((lean_file.parent / pathlib.Path(*pieces)).resolve())
    return paths


def module_path(package: pathlib.Path, lean_file: pathlib.Path) -> str | None:
    """`A/B/C` for the module `A.B.C` that `lean_file` defines in `package`."""
    for directory in sorted(source_dirs(package), key=lambda d: len(d.parts), reverse=True):
        if lean_file.resolve().is_relative_to(directory):
            return lean_file.resolve().relative_to(directory).with_suffix("").as_posix()
    return None


def force_rebuild(packages: list[pathlib.Path]) -> list[str]:
    """Delete the build outputs of every module that embeds a file, so Lake recompiles it.

    Lake decides freshness from a module's own source and its imports. A file read with
    `include_str` is neither, so after an edit to it Lake would replay the old build, and the
    record would describe a program that is no longer on disk.
    """
    forced: list[str] = []
    for package in packages:
        build = package / ".lake" / "build"
        if not build.is_dir():
            continue
        for lean_file in package_lean_files(package):
            if not embedded_paths(lean_file):
                continue
            path = module_path(package, lean_file)
            if path is None:
                continue
            for directory in (build / "lib" / "lean", build / "ir"):
                parent = (directory / path).parent
                stem = pathlib.PurePosixPath(path).name
                if parent.is_dir():
                    for artifact in parent.iterdir():
                        if artifact.is_file() and artifact.name.startswith(stem + "."):
                            artifact.unlink()
            forced.append(shown(lean_file))
    return forced


def resolve_source(module: str, olean: str) -> pathlib.Path | None:
    """The one source file for `module`, given the `.olean` it was loaded from; else `None`."""
    marker = "/.lake/build/lib/lean/"
    if marker not in olean:
        return None
    package = pathlib.Path(olean.split(marker)[0])
    relative = pathlib.Path(*module.split(".")).with_suffix(".lean")
    hits = {(directory / relative).resolve() for directory in source_dirs(package)
            if (directory / relative).is_file()}
    return hits.pop() if len(hits) == 1 else None


#: The solution module, compiled by this script outside Lake's build directory, and its source.
Compiled = tuple[str, pathlib.Path]


def locate(module: str, olean: str, compiled: Compiled | None = None) -> pathlib.Path | None:
    """`resolve_source`, except for the solution module this script compiled itself."""
    if compiled is not None and module == compiled[0]:
        return compiled[1]
    return resolve_source(module, olean)


IMPORT = re.compile(r"^\s*(?:public\s+|private\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.'«»]+)",
                    re.M)
LIBRARY_ROOTS = ("Init", "Std", "Lean", "Lake", "Mathlib", "Batteries", "Aesop", "Qq",
                 "Plausible", "ProofWidgets", "ImportGraph", "LeanSearchClient", "Cli")


def project_imports(lean_file: pathlib.Path) -> list[str]:
    """The non-library modules `lean_file` imports: what Lake must build before it compiles."""
    names = IMPORT.findall(lean_file.read_text(encoding="utf-8", errors="replace"))
    return [name for name in names
            if not any(name == root or name.startswith(root + ".") for root in LIBRARY_ROOTS)]


def text_at(path: pathlib.Path, span: dict) -> str | None:
    """The source text of a declaration range (1-based lines, 0-based codepoint columns)."""
    try:
        lines = path.read_text(encoding="utf-8").split("\n")
        first, start, last, end = (span["start_line"], span["start_col"], span["end_line"],
                                   span["end_col"])
        if first == last:
            return lines[first - 1][start:end]
        return "\n".join([lines[first - 1][start:]] + lines[first:last - 1] + [lines[last - 1][:end]])
    except (OSError, KeyError, IndexError, TypeError):
        return None


# ---------------------------------------------------------------------------
# Extraction and the rules
# ---------------------------------------------------------------------------


def extract(project: pathlib.Path, root_module: str, theorem: str, out: pathlib.Path,
            lib_dir: pathlib.Path | None) -> tuple[dict | None, dict]:
    command = ["lake", "env", "lean", "--run", str(EXTRACTOR), root_module, theorem, str(out)]
    if lib_dir is not None:
        command.append(str(lib_dir))
    rc, log, seconds = run(command, project, EXTRACT_TIMEOUT)
    meta = {"command": f"lake env lean --run scripts/{EXTRACTOR.name} {root_module} {theorem}",
            "cwd": shown(project), "rc": rc, "seconds": round(seconds, 1)}
    if rc != 0 or not out.is_file():
        meta["log_tail"] = log[-800:]
        return None, meta
    return json.loads(out.read_text(encoding="utf-8")), meta


def classify_axioms(data: dict, compiled: Compiled | None = None
                    ) -> tuple[list[str], list[dict], list[dict]]:
    """Split the proof's axioms into standard, `native_decide` steps, and everything else.

    A `native_decide` step counts only in the exact shape the tactic generates: an axiom
    `<theorem>._native.native_decide.ax_*` stating `@Eq Bool e true` for a closed `e`, declared in
    the same module as its owning theorem, whose source range is the `native_decide` token. Any
    other axiom -- `sorryAx`, a declared `axiom`, a hand-named imitation -- is "other".
    """
    olean_of = {m["module"]: m["olean"] for m in data.get("project_modules", [])}
    standard: set[str] = set()
    natives: list[dict] = []
    other: list[dict] = []
    for axiom in data.get("axioms", []):
        name, module = axiom.get("name", ""), axiom.get("module", "")
        if name in STANDARD_AXIOMS and module.startswith("Init"):
            standard.add(name)
            continue
        native = axiom.get("native") or {}
        span = axiom.get("range")
        source = locate(module, olean_of.get(module, ""), compiled)
        if (native.get("tactic") == "native_decide" and native.get("decl_exists")
                and native.get("decl_is_theorem") and native.get("decl_module") == module
                and native.get("eq_true_shape") and not native.get("has_fvar_or_mvar")
                and source is not None and span
                and (text_at(source, span) or "").strip() == "native_decide"):
            natives.append({"axiom": name, "theorem": native.get("decl"), "file": shown(source),
                            "line": span.get("start_line"),
                            "proposition": native.get("decided_prop_pp")})
            continue
        other.append({"axiom": name, "module": module})
    natives.sort(key=lambda entry: (entry["file"], entry["line"] or 0, entry["axiom"]))
    return sorted(standard), natives, other


def solution_module(project: pathlib.Path) -> str:
    """The module that holds the solution theorems: `comparator.json` says, else `Solution`."""
    config = project / "comparator.json"
    if config.is_file():
        try:
            named = json.loads(config.read_text(encoding="utf-8")).get("solution_module")
        except (OSError, ValueError):
            named = None
        if isinstance(named, str) and named:
            return named
    return "Solution"


def tracked_files() -> set[str]:
    """Paths git tracks, from the repository root. A record may rest only on these: anything else
    is absent from a fresh clone, so nobody else could rebuild what the record describes."""
    rc, log, _ = run(["git", "ls-files", "-z"], ieantn.ROOT, 120)
    return set(log.split("\0")) if rc == 0 else set()


def file_entries(paths: list[pathlib.Path]) -> list[dict]:
    unique = sorted({path.resolve() for path in paths}, key=shown)
    return [{"path": shown(path), "sha256": ieantn.sha256_file(path)} for path in unique]


def build_conclusion(node_id: str, conclusion: dict, project: pathlib.Path, build: dict,
                     packages: list[pathlib.Path], work: pathlib.Path, compiled: Compiled,
                     lib_dir: pathlib.Path) -> dict:
    cid = str(conclusion.get("id"))
    key = f"{node_id}.{cid}"
    theorem = str(conclusion.get("challenge") or f"{node_id}.challenge_{cid}")
    record: dict = {"schema": SCHEMA, "notice": NOTICE, "conclusion": key, "theorem": theorem,
                    "solution": shown(project)}
    reasons: list[str] = []
    meta: dict = {"build": build}
    for step in build["steps"]:
        if step["rc"] != 0:
            environment = step["rc"] in (124, 127, 137, 143, -9, -15)
            record.update(status="not-built" if environment else "failed",
                          reasons=[f"`{step['command']}` exited {step['rc']}"], run=meta)
            return record

    solution, meta["extract_solution"] = extract(project, compiled[0], theorem,
                                                 work / f"{cid}.json", lib_dir)
    family, version = node_id.rsplit(".", 1)
    challenge_module = f"IEANTN.Nodes.{family}.{version}.Challenge"
    challenge, meta["extract_challenge"] = extract(ieantn.ROOT, challenge_module, theorem,
                                                   work / f"{cid}.challenge.json", None)
    if solution is None or challenge is None:
        record.update(status="not-built", reasons=["the extractor did not run; see run.extract_*"],
                      run=meta)
        return record

    matches = (solution.get("endpoint_type_canonical") is not None
               and solution.get("endpoint_type_canonical") == challenge.get("endpoint_type_canonical"))
    if not matches:
        reasons.append("the solution theorem does not state the generated challenge")
    if solution.get("endpoint_kind") != "theorem":
        reasons.append(f"`{theorem}` is a {solution.get('endpoint_kind')}, not a theorem")
    if str(solution.get("endpoint_module", "")).endswith(".Challenge"):
        reasons.append(f"`{theorem}` resolved to the challenge itself, not to a solution")

    standard, natives, other = classify_axioms(solution, compiled)
    reasons += [f"axiom `{entry['axiom']}` ({entry['module']}) is neither standard nor a "
                "`native_decide` step" for entry in other]

    # Every file the proof was built from: project modules in the closure, what they embed, and
    # the Lake configuration of each package.
    modules: list[pathlib.Path] = []
    embedded: list[dict] = []
    pinned: set[str] = set()
    tracked = tracked_files()
    literals: dict[str, list[str]] = {}
    for literal in solution.get("string_literals", []):
        try:
            literals.setdefault(literal["module"], []).append(
                pathlib.Path(literal["file"]).read_text(encoding="utf-8"))
        except (OSError, KeyError):
            continue
    # Every module the solution imports, not only those whose constants the proof uses: an edit to
    # any of them can break the build, and the record must then stop describing it.
    for entry in solution.get("imported_modules") or solution.get("project_modules", []):
        if "/.lake/packages/" in entry["olean"]:
            # A dependency fetched by Lake (LeanCert, say): pinned by revision in a
            # `lake-manifest.json`, which is hashed below, rather than file by file.
            pinned.add(entry["olean"].split("/.lake/packages/", 1)[1].split("/", 1)[0])
            continue
        source = locate(entry["module"], entry["olean"], compiled)
        if source is None:
            reasons.append(f"module `{entry['module']}` does not map to exactly one source file")
            continue
        if not source.is_relative_to(ieantn.ROOT.resolve()):
            reasons.append(f"module `{entry['module']}` comes from outside the repository")
            continue
        if shown(source) not in tracked:
            reasons.append(f"{shown(source)} is not tracked by git, so a fresh clone cannot rebuild "
                           "this proof")
        modules.append(source)
        for path in embedded_paths(source):
            if not path.is_file():
                reasons.append(f"{shown(source)} embeds {shown(path)}, which does not exist")
                continue
            if not path.is_relative_to(ieantn.ROOT.resolve()):
                reasons.append(f"{shown(source)} embeds a file outside the repository")
                continue
            if shown(path) not in tracked:
                reasons.append(f"{shown(source)} embeds {shown(path)}, which git does not track")
            text = path.read_text(encoding="utf-8", errors="replace")
            embedded.append({"path": shown(path), "sha256": ieantn.sha256_file(path),
                             "embedded_by": shown(source),
                             # `true` when the build holds an identical copy as a string constant;
                             # `null` when the text is not kept as one, so it cannot be compared.
                             "copy_in_build_matches": True if text in literals.get(entry["module"], [])
                             else None})
    # A `lake-manifest.json` Lake wrote locally for a package that commits none is not part of
    # the repository; the revisions it would pin are then the ones in the committed manifests.
    config = [package / name for package in packages for name in LAKE_CONFIG
              if (package / name).is_file() and shown(package / name) in tracked]
    files = file_entries(modules + [ieantn.ROOT / item["path"] for item in embedded] + config)

    record.update({
        "status": "failed" if reasons else "passed",
        "reasons": reasons,
        "statement_matches_challenge": matches,
        "statement": solution.get("endpoint_type_pp"),
        "hypotheses": solution.get("endpoint_hypotheses", []),
        "axioms": {"standard": standard, "native_decide": natives, "other": other},
        "embedded_files": sorted(embedded, key=lambda item: item["path"]),
        "packages_pinned_by_manifest": sorted(pinned),
        "files": files,
        "lean": {"version": solution.get("lean_version"), "githash": solution.get("lean_githash")},
        "run": meta,
    })
    return record


def pins(project: pathlib.Path) -> dict:
    out: dict = {}
    toolchain = project / "lean-toolchain"
    if toolchain.is_file():
        out["lean_toolchain"] = toolchain.read_text(encoding="utf-8").strip()
    manifest = ieantn.ROOT / "lake-manifest.json"
    if manifest.is_file():
        for package in json.loads(manifest.read_text(encoding="utf-8")).get("packages", []):
            if package.get("name") == "mathlib":
                out["mathlib"] = package.get("rev")
    rc, log, _ = run(["git", "rev-parse", "HEAD"], ieantn.ROOT, 60)
    out["repository_commit"] = log.strip() if rc == 0 else None
    rc, log, _ = run(["git", "status", "--porcelain", "--untracked-files=no", "--", ".",
                      f":(exclude){ieantn.BUILD_RECORDS.name}"], ieantn.ROOT, 60)
    out["working_tree_clean"] = rc == 0 and not log.strip()
    return out


def main(node_id: str, only: str | None = None) -> bool:
    nodes = ieantn.load_nodes()
    if node_id not in nodes:
        print(f"error: unknown node `{node_id}`")
        return False
    project = ieantn.SOLUTIONS / node_id
    if not (project / "Solution.lean").is_file():
        print(f"error: no solution at {ieantn.rel(project)}")
        return False
    conclusions = [c for c in ieantn.conclusions_of(nodes[node_id])
                   if (c.get("id") == only if only is not None
                       else ieantn.designated_kind(c) == ieantn.NONCOMPLIANT_KIND)]
    if not conclusions:
        print(f"error: nothing to record in `{node_id}`"
              + (f" named `{only}`" if only else ": no conclusion designates `lean-noncompliant`"))
        return False

    packages = required_packages(project)
    forced = force_rebuild(packages)
    module = solution_module(project)
    source = project / pathlib.Path(*module.split(".")).with_suffix(".lean")
    print(f"  building {ieantn.rel(project)}; recompiling {len(forced)} file(s) that embed "
          "sources", flush=True)
    scratch = pathlib.Path(tempfile.mkdtemp(prefix="build-record-"))
    lib_dir = scratch / "lib"
    olean = lib_dir / pathlib.Path(*module.split(".")).with_suffix(".olean")
    olean.parent.mkdir(parents=True, exist_ok=True)
    # As the verification workflow does: the package's default targets, then the solution module.
    # The solution file is compiled here, into a scratch directory, because not every solution
    # package declares it as a library module; Lake builds what it imports first.
    commands = [["lake", "build"]]
    imports = project_imports(source) if source.is_file() else []
    if imports:
        commands.append(["lake", "build", *imports])
    commands.append(["lake", "env", "lean", source.relative_to(project).as_posix(), "-o",
                     str(olean), "-i", str(olean.with_suffix(".ilean"))])
    steps = []
    for command in commands:
        rc, log, seconds = run(command, project, BUILD_TIMEOUT)
        # Records are committed, so the scratch directory is not named.
        display = " ".join("<scratch>/" + pathlib.Path(part).name if part.startswith(str(scratch))
                           else part for part in command)
        step = {"command": display, "rc": rc, "seconds": round(seconds, 1)}
        if rc != 0:
            step["log_tail"] = log[-1500:]
            steps.append(step)
            break
        steps.append(step)
    build = {"steps": steps, "recompiled_for_embedded_sources": forced}
    stamp = {"checked_at_utc": _dt.datetime.now(_dt.timezone.utc).isoformat(timespec="seconds"),
             "pins": pins(project),
             "tools": {"build_record.py": ieantn.sha256_file(pathlib.Path(__file__)),
                       EXTRACTOR.name: ieantn.sha256_file(EXTRACTOR)}}

    ieantn.BUILD_RECORDS.mkdir(parents=True, exist_ok=True)
    ok = True
    try:
        for conclusion in conclusions:
            record = build_conclusion(node_id, conclusion, project, build, packages, scratch,
                                      (module, source.resolve()), lib_dir)
            record.update(stamp)
            path = ieantn.build_record_path(record["conclusion"])
            path.write_text(json.dumps(record, indent=1, ensure_ascii=False) + "\n",
                            encoding="utf-8")
            natives = len((record.get("axioms") or {}).get("native_decide") or [])
            print(f"  {record['status']:<9} {record['conclusion']}: "
                  + ("; ".join(record.get("reasons") or [])
                     or f"states the challenge, {natives} native_decide step(s), "
                        f"{len(record.get('files') or [])} files hashed")
                  + f"  -> {ieantn.rel(path)}")
            ok &= record["status"] == "passed"
    finally:
        shutil.rmtree(scratch, ignore_errors=True)
    return ok
