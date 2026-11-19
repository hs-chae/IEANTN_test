#!/usr/bin/env python3
"""Rebuild the two frozen proof baselines without calling a model.

Only the compressed, hash-pinned manifest beside this file is required. Public
GitHub archives supply sources; official Mathlib caches supply generic objects.
An optional, fully checked cache map permits a source-fresh component replay.
All writes are below a fresh --out directory. This is bounded host proof setup,
not a scored discovery sandbox or a source-first PV assertion.
"""
from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import datetime
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import resource
import shutil
import subprocess
import sys
import tarfile
import tempfile
import threading
import time
import urllib.request
import uuid
import zipfile


PIN_FILE = Path(__file__).with_name("baseline_reproduction_pins.json.gz")
PIN_SHA256 = "de395902e63692e37c7e043f8c2799b3ea84e3a8929aed21048ea12adf336555"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
RESUMING_COLD = False


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    digest = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def pairs(rows):
    result = {}
    for key, value in rows:
        need(key not in result, "duplicate JSON key: " + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=pairs,
                      parse_constant=lambda value: (_ for _ in ()).throw(ValueError(value)))


def write_json(path, value):
    path = Path(path)
    need(not path.exists(), "fresh receipt required: " + str(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name("." + path.name + ".tmp")
    with temporary.open("x") as stream:
        json.dump(value, stream, indent=2, allow_nan=False)
        stream.write("\n")
    os.link(temporary, path)
    temporary.unlink()


def pins():
    need(sha(PIN_FILE) == PIN_SHA256, "frozen baseline pin file changed")
    value = json.loads(gzip.decompress(PIN_FILE.read_bytes()), object_pairs_hook=pairs)
    need(value["schema"] == "IEANTN_BASELINE_REPRODUCTION_PINS_V1", "pin schema")
    return value


def safe_relative(value):
    p = PurePosixPath(value)
    need(not p.is_absolute() and ".." not in p.parts and ".git" not in p.parts,
         "noncanonical source path")
    need(p.as_posix() == value, "noncanonical archive member")
    return p


def inventory(root, skip_build_dirs=False):
    root = Path(root).resolve()
    rows = []
    for parent, directories, files in os.walk(root, followlinks=False):
        if skip_build_dirs:
            directories[:] = [name for name in directories if name not in {".lake", ".cache"}]
        for name in sorted(directories + files):
            p = Path(parent) / name
            rel = p.relative_to(root)
            need(".git" not in rel.parts, "Git data in an exposed/cache tree")
            if p.is_symlink():
                need(p.resolve().is_relative_to(root), "source/cache symlink leaves tree")
                rows.append({"path": rel.as_posix(), "symlink": os.readlink(p)})
            elif p.is_file():
                rows.append({"path": rel.as_posix(), "bytes": p.stat().st_size, "sha256": sha(p)})
            else:
                need(p.is_dir(), "nonregular cache entry")
    return sorted(rows, key=lambda row: row["path"])


def check_tree(root, expected):
    need(inventory(root) == sorted(expected, key=lambda row: row["path"]),
         "pinned cache/source tree differs: " + str(root))


def copied_tree(source, destination, expected):
    source, destination = Path(source).resolve(), Path(destination)
    check_tree(source, expected)
    need(not destination.exists(), "fresh copied tree required")
    destination.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["/usr/bin/cp", "--archive", "--reflink=auto", str(source), str(destination)],
                   check=True)
    check_tree(destination, expected)


def download(url, destination, records, expected_sha=None, expected_bytes=None):
    destination.parent.mkdir(parents=True, exist_ok=True)
    if RESUMING_COLD and destination.exists():
        size, actual = destination.stat().st_size, sha(destination)
        if expected_sha is not None:
            need(actual == expected_sha and size == expected_bytes, "owned release checkpoint differs")
        else:
            need(zipfile.is_zipfile(destination), "owned source-archive checkpoint is incomplete")
        records.append({"url": url, "path": str(destination), "bytes": size, "sha256": actual,
                        "same_owned_cold_attempt_checkpoint": True,
                        "identity_check": "pinned release digest or complete retained source-file hashes"})
        return destination
    need(not destination.exists(), "fresh archive required")
    request = urllib.request.Request(url, headers={"User-Agent": "IEANTN-Baseline-Reproduction/1"})
    size = 0
    digest = hashlib.sha256()
    with urllib.request.urlopen(request, timeout=90) as response, destination.open("xb") as output:
        for block in iter(lambda: response.read(1024 * 1024), b""):
            size += len(block)
            need(size <= (expected_bytes if expected_bytes is not None else 128 * 1024**2),
                 "archive exceeds its bounded size")
            digest.update(block)
            output.write(block)
    actual = digest.hexdigest()
    if expected_sha is not None:
        need(actual == expected_sha and size == expected_bytes, "official release archive differs")
    records.append({"url": url, "path": str(destination), "bytes": size, "sha256": actual,
                    "identity_check": "pinned archive digest" if expected_sha else
                    "every retained extracted source checked against frozen SHA256 inventory"})
    return destination


def source_archive(repository, commit, destination, expected, work, records,
                   generated_metadata=(), regenerate=None, allowed_extra=()):
    archive = download("https://codeload.github.com/" + repository + "/zip/" + commit,
                       work / "archives" / (repository.replace("/", "-") + "-" + commit + ".zip"),
                       records)
    need(RESUMING_COLD or not destination.exists(), "fresh source directory required")
    destination.mkdir(parents=True, exist_ok=RESUMING_COLD)
    generated = {row["path"]: row for row in generated_metadata}
    with zipfile.ZipFile(archive) as bundle:
        entries = bundle.infolist()
        need(bool(entries), "empty source archive")
        prefix = entries[0].filename.split("/")[0] + "/"
        by_name = {}
        for info in entries:
            need(info.filename.startswith(prefix), "inconsistent archive prefix")
            rel = info.filename[len(prefix):]
            if not rel or info.is_dir():
                continue
            safe_relative(rel)
            need(rel not in by_name, "duplicate source archive member")
            by_name[rel] = info
        for row in expected:
            rel = safe_relative(row["path"]).as_posix()
            if rel not in by_name:
                need(rel in generated, "original source member absent: " + rel)
                continue
            info = by_name[rel]
            target = destination / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            if RESUMING_COLD and target.exists():
                if "symlink" in row:
                    need(target.is_symlink() and os.readlink(target) == row["symlink"],
                         "owned source symlink checkpoint differs")
                else:
                    need(target.is_file() and target.stat().st_size == row["bytes"] and
                         sha(target) == row["sha256"], "owned source checkpoint differs")
                continue
            if "symlink" in row:
                value = bundle.read(info).decode()
                need(value == row["symlink"], "source symlink differs")
                need((target.parent / value).resolve().is_relative_to(destination.resolve()),
                     "source symlink leaves projection")
                target.symlink_to(value)
            else:
                need(info.file_size == row["bytes"], "source length differs")
                with bundle.open(info) as source, target.open("xb") as output:
                    shutil.copyfileobj(source, output, 1024 * 1024)
                need(sha(target) == row["sha256"], "source digest differs: " + rel)
                mode = (info.external_attr >> 16) & 0o777
                target.chmod(mode or 0o644)
    for recipe in generated_metadata:
        target = destination / recipe["path"]
        if not target.exists():
            need(regenerate is not None, "generated metadata recipe has no execution provider")
            regenerate(recipe, destination)
        need(target.stat().st_size == recipe["expected_bytes"] and
             sha(target) == recipe["expected_sha256"], "regenerated build metadata differs")
    actual = inventory(destination, skip_build_dirs=RESUMING_COLD)
    actual = [row for row in actual if row["path"] not in set(allowed_extra)]
    need(actual == sorted(expected, key=lambda row: row["path"]), "source projection differs")


def toolchain(spec, work, cached, downloads):
    destination = work / "toolchain"
    if RESUMING_COLD and destination.exists():
        check_tree(destination, spec["files"])
        archive = work / "archives" / spec["archive"]
        need(archive.exists() and sha(archive) == spec["sha256"],
             "resumed cold compiler lacks its exact downloaded release")
        downloads.append({"url": spec["url"], "path": str(archive), "sha256": sha(archive),
                          "same_owned_cold_attempt_checkpoint": True})
        return destination
    if cached:
        copied_tree(cached, destination, spec["files"])
    else:
        archive = download(spec["url"], work / "archives" / spec["archive"], downloads,
                           spec["sha256"], spec["bytes"])
        destination.mkdir()
        expected = {row["path"]: row for row in spec["files"]}
        seen = set()
        proc = subprocess.Popen(["/usr/bin/zstd", "--decompress", "--stdout", str(archive)],
                                stdout=subprocess.PIPE)
        try:
            with tarfile.open(fileobj=proc.stdout, mode="r|") as bundle:
                prefix = None
                for member in bundle:
                    parts = PurePosixPath(member.name).parts
                    if not parts:
                        continue
                    if prefix is None:
                        prefix = parts[0]
                    need(parts[0] == prefix, "release archive prefixes differ")
                    rel = "/".join(parts[1:])
                    if not rel or member.isdir() or rel not in expected:
                        continue
                    safe_relative(rel)
                    need(rel not in seen, "duplicate official toolchain member")
                    seen.add(rel)
                    row = expected[rel]
                    target = destination / rel
                    target.parent.mkdir(parents=True, exist_ok=True)
                    if "symlink" in row:
                        need(member.issym() and member.linkname == row["symlink"],
                             "official toolchain symlink differs")
                        need((target.parent / member.linkname).resolve().is_relative_to(destination),
                             "release symlink leaves its tree")
                        target.symlink_to(member.linkname)
                    else:
                        need(member.isfile() and member.size == row["bytes"], "release file differs")
                        with bundle.extractfile(member) as source, target.open("xb") as output:
                            shutil.copyfileobj(source, output, 1024 * 1024)
                        need(sha(target) == row["sha256"], "release member digest differs")
                        target.chmod(member.mode & 0o777)
            need(proc.wait() == 0 and seen == set(expected), "incomplete pinned release extraction")
        finally:
            if proc.poll() is None:
                proc.terminate()
            proc.wait()
        check_tree(destination, spec["files"])
    need(sha(destination / "bin/lean") == spec["binary_sha256"], "compiler binary differs")
    return destination


def command(argv, cwd, env, work, commands, lock, name):
    need(re.fullmatch(r"[A-Za-z0-9_.-]+", name), "noncanonical command label")
    logs = work / "commands"
    logs.mkdir(exist_ok=True)
    if RESUMING_COLD:
        original, count = name, 0
        while (logs / (name + ".stdout")).exists():
            count += 1
            name = original + "-resume" + str(count)
    stdout, stderr, usage = [logs / (name + suffix) for suffix in (".stdout", ".stderr", ".time")]
    need(not stdout.exists() and not stderr.exists(), "fresh command logs required")
    actual = ["/usr/bin/time", "-v", "-o", str(usage)] + list(argv)
    started = time.monotonic()
    with stdout.open("x") as out, stderr.open("x") as err:
        result = subprocess.run(actual, cwd=cwd, env=env, stdout=out, stderr=err)
    record = {"label": name, "argv": list(argv), "cwd": str(cwd),
              "elapsed_seconds": time.monotonic() - started, "returncode": result.returncode,
              "stdout": str(stdout), "stdout_sha256": sha(stdout),
              "stderr": str(stderr), "stderr_sha256": sha(stderr),
              "gnu_time": str(usage), "gnu_time_sha256": sha(usage)}
    with lock:
        commands.append(record)
        with (work / "COMMANDS.jsonl").open("a") as stream:
            stream.write(json.dumps(record, allow_nan=False) + "\n")
    need(result.returncode == 0, "command failed; original logs preserved: " + name)
    return stdout.read_text()


def environment(tc, work, paths=()):
    owned_home, owned_tmp, owned_cache = [work / name for name in ("home", "tmp", "cache")]
    for path in (owned_home, owned_tmp, owned_cache):
        path.mkdir(exist_ok=True)
    return {"PATH": str(tc / "bin") + ":/usr/bin:/bin", "LEAN_SYSROOT": str(tc),
            "LEAN_PATH": ":".join(map(str, paths)), "HOME": str(owned_home),
            "TMPDIR": str(owned_tmp), "XDG_CACHE_HOME": str(owned_cache),
            "MATHLIB_CACHE_DIR": str(owned_cache / "mathlib"), "LANG": "C", "LC_ALL": "C",
            "LEAN_NUM_THREADS": "4", "RAYON_NUM_THREADS": "8", "MALLOC_ARENA_MAX": "2"}


def compiler_flags(options):
    return ["-D" + name + "=" + (str(value).lower() if isinstance(value, bool) else str(value))
            for name, value in options.items()]


def validate_cache_map(cache, frozen, arms, output):
    """Support a complete checked cache map, or the separate no-cache path."""
    need(cache.get("schema") == "IEANTN_BASELINE_READ_ONLY_CACHE_MAP_V1", "cache map schema")
    need(isinstance(cache.get("arms"), dict), "cache arms mapping required")
    for arm in arms:
        entry = cache["arms"].get(arm)
        need(isinstance(entry, dict) and isinstance(entry.get("toolchain"), str),
             "complete cache map required: toolchain for " + arm)
        generic = entry.get("generic")
        names = {row["name"] for row in frozen["arms"][arm]["generic"]}
        need(isinstance(generic, dict) and set(generic) == names,
             "complete cache map required: generic names for " + arm)
        roots = [Path(entry["toolchain"]).resolve()]
        for dep in frozen["arms"][arm]["generic"]:
            item = generic[dep["name"]]
            need(isinstance(item, dict) and isinstance(item.get("source"), str),
                 "complete cache map required: generic source " + dep["name"])
            roots.append(Path(item["source"]).resolve())
            if dep["objects"] is not None:
                need(isinstance(item.get("objects"), str),
                     "complete cache map required: generic objects " + dep["name"])
                roots.append(Path(item["objects"]).resolve())
        for root in roots:
            need(root.is_dir(), "cache directory absent: " + str(root))
            need(not output.is_relative_to(root), "output must not be inside a reused cache tree")


def compile_graph(spec, source, objects, tc, generic_paths, work, commands, lock):
    objects.mkdir(parents=True, exist_ok=RESUMING_COLD)
    remaining = {row["module"]: row for row in spec["modules"]}
    finished = set()
    known = set(remaining)
    checkpoint_dir = work / "proof-command-checkpoints"
    checkpoint_dir.mkdir(exist_ok=True)
    compiler_digest = sha(tc / "bin/lean")
    if RESUMING_COLD:
        for name, row in list(remaining.items()):
            checkpoint_file = checkpoint_dir / (name + ".json")
            if not checkpoint_file.exists():
                continue
            checkpoint = read_json(checkpoint_file)
            need(checkpoint["source_sha256"] == row["sha256"] == sha(source / row["source"]) and
                 checkpoint["compiler_sha256"] == compiler_digest, "owned proof checkpoint inputs differ")
            for artifact in checkpoint["artifacts"]:
                need(sha(work / artifact["path"]) == artifact["sha256"], "owned proof checkpoint artifact differs")
            evidence = checkpoint["command_evidence"]
            for field, identity in (("stdout", "stdout_sha256"), ("stderr", "stderr_sha256"),
                                    ("gnu_time", "gnu_time_sha256")):
                need(sha(evidence[field]) == evidence[identity], "owned proof checkpoint command evidence differs")
            need(evidence["returncode"] == 0, "failed command cannot be a completed proof checkpoint")
            finished.add(name)
            del remaining[name]
    env = environment(tc, work, [objects] + generic_paths)
    flags = compiler_flags(spec.get("lean_options", {}))

    def compile_one(row):
        rel = row["source"]
        need(sha(source / rel) == row["sha256"], "source changed before compile")
        output = objects / Path(*row["module"].split("."))
        output.parent.mkdir(parents=True, exist_ok=True)
        argv = [str(tc / "bin/lean"), "-j4"] + flags + ["-o", str(output.with_suffix(".olean")),
                "-i", str(output.with_suffix(".ilean")), rel]
        command(argv, source, env, work, commands, lock, "compile-" + row["module"])
        artifacts = [{"path": str(path.relative_to(work)), "bytes": path.stat().st_size,
                      "sha256": sha(path)} for path in sorted(output.parent.glob(output.name + ".*"))
                     if path.is_file()]
        need(any(value["path"].endswith(".olean") for value in artifacts), "compiler emitted no proof object")
        with lock:
            producer = next(value for value in reversed(commands)
                            if value["argv"] == argv and value["returncode"] == 0)
            write_json(checkpoint_dir / (row["module"] + ".json"),
                       {"status": "OWNED_COLD_SOURCE_COMPILE_CHECKPOINT", "module": row["module"],
                        "source": row["source"], "source_sha256": row["sha256"],
                        "compiler_sha256": compiler_digest, "command_evidence": producer,
                        "artifacts": artifacts})
        return row["module"]

    with ThreadPoolExecutor(max_workers=2) as pool:
        while remaining:
            ready = sorted(name for name, row in remaining.items()
                           if (set(row["imports"]) & known) <= finished)
            need(bool(ready), "cycle or missing native source import in frozen graph")
            selected = ready[:2]
            futures = [pool.submit(compile_one, remaining[name]) for name in selected]
            for future in futures:
                finished.add(future.result())
            for name in selected:
                del remaining[name]
    return env


def axiom_audit(theorems, imports, source, env, tc, work, commands, lock, name):
    preview = work / (name + ".lean")
    preview.write_text("\n".join("import " + module for module in imports) + "\n" +
                       "\n".join("#print axioms " + theorem for theorem in theorems) + "\n")
    text = command([str(tc / "bin/lean"), "-j4", str(preview)], source, env, work,
                   commands, lock, name)
    for theorem in theorems:
        match = re.search(re.escape("'" + theorem + "' depends on axioms:") + r"\s*\[([^\]]*)\]", text)
        need(match is not None, "axiom output missing for " + theorem)
        actual = {value.strip() for value in match.group(1).split(",")}
        actual = {"Classical.choice" if value == "choice" else value for value in actual}
        need(actual == ALLOWED_AXIOMS, "unexpected theorem axiom closure: " + theorem)
    return {"theorems": theorems, "axioms": sorted(ALLOWED_AXIOMS), "status": "PASS"}


def reproduce_arm(arm, spec, root, cache):
    work = root / arm
    work.mkdir(exist_ok=RESUMING_COLD)
    downloads, commands, lock = [], [], threading.Lock()
    if RESUMING_COLD and (work / "COMMANDS.jsonl").exists():
        commands = [json.loads(line) for line in (work / "COMMANDS.jsonl").read_text().splitlines()]
    tc = toolchain(spec["toolchain"], work, cache.get("toolchain"), downloads)
    source = work / "source"
    source_archive(spec["repository"], spec["commit"], source, spec["source_files"], work, downloads,
                   allowed_extra=spec["generated_files"])
    for rel, text in spec["generated_files"].items():
        target = source / safe_relative(rel).as_posix()
        if RESUMING_COLD and target.exists():
            need(target.read_text() == text, "owned generated root checkpoint differs")
        else:
            need(not target.exists(), "generated native root would overwrite original source")
            target.write_text(text)
    packages = source / ".lake/packages"
    packages.mkdir(parents=True, exist_ok=RESUMING_COLD)
    generic_paths, overrides = [], []
    for dep in spec["generic"]:
        package = packages / dep["name"]
        cached = cache.get("generic", {}).get(dep["name"], {})
        if cached:
            copied_tree(cached["source"], package, dep["source_files"])
        else:
            def regenerate(recipe, directory):
                need(recipe["kind"] == "Lake.computeFileHash/writeFileHash" and recipe["text"] is True,
                     "unsupported generated metadata recipe")
                input_file = directory / recipe["input"]
                need(sha(input_file) == recipe["input_sha256"], "metadata original input differs")
                program = work / ("regenerate-" + dep["name"] + "-file-hash.lean")
                text = ('import Lake\ndef main (args : List String) : IO Unit := do\n'
                        '  match args with\n  | [input] =>\n'
                        '    let file := System.FilePath.mk input\n'
                        '    Lake.writeFileHash file (← Lake.computeFileHash file true)\n'
                        '  | _ => throw (IO.userError "exact input file required")\n')
                if program.exists():
                    need(program.read_text() == text, "metadata program checkpoint differs")
                else:
                    program.write_text(text)
                command([str(tc / "bin/lean"), "--run", str(program), str(input_file)],
                        directory, environment(tc, work), work, commands, lock,
                        "regenerate-" + dep["name"] + "-file-hash")
            source_archive(dep["repository"], dep["commit"], package, dep["source_files"], work,
                           downloads, dep.get("generated_metadata", []), regenerate)
        if dep["objects"] is not None and cached.get("objects"):
            copied_tree(cached["objects"], package / ".lake/build/lib/lean", dep["objects"])
        entry = dep["manifest"]
        overrides.append({"type": "path", "name": dep["name"], "scope": entry.get("scope", ""),
                          "dir": str(package), "inherited": entry["inherited"],
                          "configFile": entry.get("configFile"), "manifestFile": entry.get("manifestFile")})
    overrides_value = {"schemaVersion": "1.2.0", "packages": overrides}
    if RESUMING_COLD and (work / "package-overrides.json").exists():
        need(read_json(work / "package-overrides.json") == overrides_value, "owned overrides differ")
    else:
        write_json(work / "package-overrides.json", overrides_value)
    env = environment(tc, work)
    if not cache:
        bootstrap = work / "GENERIC_BOOTSTRAP_COMPLETE.json"
        if RESUMING_COLD and bootstrap.exists():
            previous = read_json(bootstrap)
            need(previous["source_commit"] == spec["commit"] and
                 previous["generic_dependency_commits"] == {dep["name"]: dep["commit"] for dep in spec["generic"]},
                 "owned generic bootstrap input checkpoint differs")
            for item in previous["commands"]:
                need(item["returncode"] == 0 and sha(item["stdout"]) == item["stdout_sha256"] and
                     sha(item["stderr"]) == item["stderr_sha256"], "owned generic bootstrap evidence differs")
        else:
            external = sorted({name for row in spec["modules"] for name in row["imports"]
                               if name == "Mathlib" or name.startswith("Mathlib.")})
            need(bool(external), "missing generic cache target inventory")
            command([str(tc / "bin/lake"), "--packages", str(work / "package-overrides.json"),
                     "exe", "cache", "get"] + external, source, env, work, commands, lock, "generic-cache-get")
            if arm == "PNT":
                command([str(tc / "bin/lake"), "--packages", str(work / "package-overrides.json"),
                         "build", "@LeanArchitect/Architect"], source, env, work, commands, lock,
                        "generic-architect-build")
            base_commands = [row for row in commands if row["label"] in
                             {"generic-cache-get", "generic-architect-build"} and row["returncode"] == 0]
            write_json(bootstrap, {"status": "PASS_OWNED_COLD_BASE_GENERIC_BOOTSTRAP",
                       "source_commit": spec["commit"],
                       "generic_dependency_commits": {dep["name"]: dep["commit"] for dep in spec["generic"]},
                       "commands": base_commands})
        native_names = {row["module"] for row in spec["modules"]}
        direct_external = sorted({name for row in spec["modules"] for name in row["imports"]
                                  if name not in native_names and
                                  not name.startswith(("Init", "Lean", "Std", "Mathlib"))})
        for module in direct_external:
            rel = Path(*module.split("."))
            if any((packages / dep["name"] / ".lake/build/lib/lean" / rel).with_suffix(".olean").exists()
                   for dep in spec["generic"]):
                continue
            providers = [dep for dep in spec["generic"]
                         if (packages / dep["name"] / rel).with_suffix(".lean").is_file()]
            need(len(providers) == 1, "missing direct generic provider: " + module)
            command([str(tc / "bin/lake"), "--packages", str(work / "package-overrides.json"),
                     "build", "@" + providers[0]["name"] + "/+" + module], source, env, work,
                    commands, lock, "generic-direct-" + module)
    for dep in spec["generic"]:
        objects = packages / dep["name"] / ".lake/build/lib/lean"
        if objects.is_dir():
            generic_paths.append(objects)
    objects = work / "objects"
    compiled_env = compile_graph(spec, source, objects, tc, generic_paths, work, commands, lock)
    audits = []
    if spec["native_axioms"]:
        audits.append(axiom_audit(spec["native_axioms"], ["PrimeNumberTheoremAnd"], source,
                                 compiled_env, tc, work, commands, lock, "native-axiom-audit"))
    selected_results = []
    for selected in spec.get("selected", []):
        selected_objects = work / "selected" / selected["project"]
        selected_objects.mkdir(parents=True)
        selected_env = environment(tc, work, [selected_objects, objects] + generic_paths)
        project = source / "Solutions" / selected["project"]
        for row in selected["modules"]:
            rel = Path(row["source"])
            need((source / rel).is_file(), "selected unchanged source absent")
            output = selected_objects / (row["module"] + ".olean")
            command([str(tc / "bin/lean"), "-j4", "-o", str(output), "-i",
                     str(output.with_suffix(".ilean")), rel.name], project, selected_env, work,
                    commands, lock, "selected-" + selected["project"] + "-" + row["module"])
        audit = axiom_audit([selected["axiom_theorem"]], ["Solution"], project, selected_env, tc,
                            work, commands, lock, "axioms-" + selected["project"])
        selected_results.append({"project": selected["project"], "axiom_audit": audit,
                                 "separate_solution_namespace": True})
    write_json(work / "DOWNLOADS.json", downloads)
    artifacts = []
    for target in [objects, work / "selected"]:
        if target.exists():
            artifacts.extend({"path": str(path.relative_to(work)), "bytes": path.stat().st_size,
                              "sha256": sha(path)} for path in sorted(target.rglob("*")) if path.is_file())
    result = {"arm": arm, "status": "PASS_SOURCE_FRESH_APPLICATION_BASELINE_REBUILD",
              "source_commit": spec["commit"], "source_modules_recompiled": len(spec["modules"]),
              "native_axiom_audits": audits, "selected_original_proofs": selected_results,
              "generic_objects_reused_from_local_cache": bool(cache),
              "toolchain_reused_from_local_cache": bool(cache.get("toolchain")),
              "cold_host_execution": not bool(cache),
              "compiler_and_mathlib_rebuilt_from_source": False,
              "cold_host_note": "No local dependency/toolchain cache reused; exact public releases/source archives and official generic binary caches fetched into this fresh directory." if not cache else
              "Pinned generic and compiler artifacts reused from the checked local cache map; not a fully cold host bootstrap.",
              "trust": "Pinned Lean compiler/kernel, generic dependency/cache contracts, OS/runtime/hardware. Existing unused upstream admissions remain; selected theorem closures are separately checked. No source-first PV claim.",
              "IEANTN_premises": "Core compilation does not prove every node. DPv3 is a criterion implication; DPv2 keeps criterion and pi_two_sided_pnt hypotheses. No numerical premise supplied as fact.",
              "commands": commands, "generated_proof_artifacts": artifacts}
    write_json(work / "RESULT.json", result)
    return result


def actual_resources(root):
    group = Path("/proc/self/cgroup").read_text().strip().split(":", 2)[2]
    base = Path("/sys/fs/cgroup") / group.lstrip("/")
    fields = {}
    for name in ("memory.max", "memory.swap.max", "memory.peak", "memory.events", "cpu.max"):
        p = base / name
        fields[name] = p.read_text().strip() if p.exists() else None
    fields["cpu_affinity"] = sorted(os.sched_getaffinity(0))
    fields["rlimit_nofile"] = list(resource.getrlimit(resource.RLIMIT_NOFILE))
    fields["cgroup"] = group
    return fields


def inside(args, frozen):
    root = args.out.resolve()
    executed_script_sha256 = sha(__file__)
    observed = actual_resources(root)
    need(observed["memory.max"] == str(args.memory_gib * 1024**3), "actual memory scope differs")
    need(observed["memory.swap.max"] == "0", "actual swap scope differs")
    need(0 < len(observed["cpu_affinity"]) <= 8, "actual taskset CPU cap differs")
    need(observed["rlimit_nofile"][0] >= 65536, "actual descriptor allowance too small")
    evidence = root / "execution-attempts" / args.attempt
    evidence.mkdir(parents=True)
    write_json(evidence / "ACTUAL_RESOURCE_START.json", observed)
    cache = read_json(args.cache_map) if args.cache_map else {"arms": {}}
    if args.cache_map:
        validate_cache_map(cache, frozen, args.arms, root)
    samples, stop = [], threading.Event()
    cg = Path("/sys/fs/cgroup") / observed["cgroup"].lstrip("/")

    def monitor():
        while not stop.wait(0.5):
            p = cg / "memory.current"
            if p.exists():
                samples.append(int(p.read_text()))

    thread = threading.Thread(target=monitor, daemon=True)
    thread.start()
    started = time.monotonic()
    results = []
    try:
        for arm in args.arms:
            prior = root / arm / "RESULT.json"
            if RESUMING_COLD and prior.exists():
                value = read_json(prior)
                need(value["status"] == "PASS_SOURCE_FRESH_APPLICATION_BASELINE_REBUILD" and
                     value["source_commit"] == frozen["arms"][arm]["commit"] and
                     value["cold_host_execution"] is True, "accepted owned cold checkpoint differs")
                for row in value["generated_proof_artifacts"]:
                    need(sha(root / arm / row["path"]) == row["sha256"], "accepted cold proof checkpoint changed")
                results.append(value)
                continue
            results.append(reproduce_arm(arm, frozen["arms"][arm], root, cache.get("arms", {}).get(arm, {})))
    finally:
        stop.set()
        thread.join()
        write_json(evidence / "ACTUAL_RESOURCE_END.json", actual_resources(root))
        write_json(evidence / "RESOURCE_SAMPLES.json", {"memory_current_samples": samples,
                   "peak_charged_memory_sampled_lower_bound": max(samples, default=None),
                   "exact_peak_memory": None, "note": "memory.peak may be unavailable; sampled maximum is a lower bound, not exact simultaneous peak.",
                   "elapsed_seconds": time.monotonic() - started})
    need(sha(__file__) == executed_script_sha256, "reproduction script changed during execution")
    write_json(root / "RESULT.json", {"status": "PASS_BASELINE_COMPONENT_REPLAY", "arms": results,
               "inference_calls": 0, "experimental_scores_modified": False,
               "script_sha256": sha(__file__), "pins_sha256": PIN_SHA256,
               "resource_evidence": str(evidence), "same_owned_cold_checkpoint_resume": RESUMING_COLD,
               "resource_policy": {"memory_gib": args.memory_gib, "swap_bytes": 0,
                                   "cpus": observed["cpu_affinity"], "nofile": 65536,
                                   "scratch_limit_gib": args.scratch_gib},
               "source_module_counts": {row["arm"]: row["source_modules_recompiled"] for row in results},
               "scope": "Fresh application source rebuild for selected arms: " + ", ".join(args.arms) +
               ". IEANTN includes its two separate original selected DP contexts when selected. Generic/compiler caches may be reused; no claim of a fully cold all-source platform rebuild."})
    print("PASS_BASELINE_COMPONENT_REPLAY", str(root / "RESULT.json"))


def main():
    global RESUMING_COLD
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path)
    parser.add_argument("--arms", nargs="+", choices=["PNT", "IEANTN"], default=["PNT", "IEANTN"])
    parser.add_argument("--cache-map", type=Path,
                        help="Optional COMPLETE exact pinned generic/toolchain cache map; never a native proof-object cache. Omit for public-source bootstrap.")
    parser.add_argument("--memory-gib", type=int, choices=[32, 64], default=32)
    parser.add_argument("--scratch-gib", type=int, choices=[32, 48, 64, 128], default=48,
                        help="Owned output allocated-block guard; no external cache or original directory is deleted.")
    parser.add_argument("--cpus", help="Eight or fewer permitted CPU numbers, e.g. 80-87; default first eight in affinity.")
    parser.add_argument("--inside-scope", action="store_true", help=argparse.SUPPRESS)
    parser.add_argument("--attempt", default="initial", help=argparse.SUPPRESS)
    parser.add_argument("--resume-cold", action="store_true",
                        help="Continue only an interrupted owned public-source cold bootstrap; no external cache map.")
    parser.add_argument("--validate-pins", action="store_true")
    args = parser.parse_args()
    RESUMING_COLD = args.resume_cold
    frozen = pins()
    if args.validate_pins:
        print(json.dumps({"status": "PASS_FROZEN_REPRODUCTION_PINS", "pins_sha256": PIN_SHA256,
                          "source_commits": {arm: value["commit"] for arm, value in frozen["arms"].items()},
                          "inference_calls": 0}))
        return
    need(args.out is not None, "fresh --out is required")
    need(len(set(args.arms)) == len(args.arms), "duplicate arm")
    if args.inside_scope:
        inside(args, frozen)
        return
    root = args.out.resolve()
    if RESUMING_COLD:
        need(args.cache_map is None and root.is_dir() and not (root / "RESULT.json").exists(),
             "resume requires an incomplete owned cold run and no external cache")
        previous = read_json(root / "REPRODUCTION_INVOCATION.json")
        need(previous["cache_map_sha256"] is None and
             previous["source_inputs"] == {arm: frozen["arms"][arm]["commit"] for arm in args.arms},
             "resume source inputs differ or original run used host caches")
    else:
        need(not root.exists(), "output exists; preserve prior attempts and use a fresh output path")
    if args.cache_map:
        validate_cache_map(read_json(args.cache_map), frozen, args.arms, root)
    need(sys.platform == "linux" and os.uname().machine == "x86_64", "pinned Linux x86_64 release required")
    for executable in ("systemd-run", "taskset", "tar", "zstd", "cp", "time"):
        need(shutil.which(executable) is not None, "missing prerequisite: " + executable)
    mem = {row.split(":", 1)[0]: row.split(":", 1)[1].strip() for row in Path("/proc/meminfo").read_text().splitlines()}
    available = int(mem["MemAvailable"].split()[0]) * 1024
    need(available >= (args.memory_gib + 16) * 1024**3, "insufficient available RAM plus host reserve")
    need(shutil.disk_usage(root.parent).free >= 48 * 1024**3, "insufficient separate scratch disk headroom")
    root.mkdir(parents=True, exist_ok=RESUMING_COLD)
    cpu_value = args.cpus or ",".join(map(str, sorted(os.sched_getaffinity(0))[:8]))
    unit = "ieantn-baseline-replay-" + uuid.uuid4().hex[:12]
    inner = [sys.executable, "-I", "-B", str(Path(__file__).resolve()), "--inside-scope", "--out", str(root),
             "--memory-gib", str(args.memory_gib), "--scratch-gib", str(args.scratch_gib), "--arms"] + args.arms
    inner += ["--attempt", unit]
    if RESUMING_COLD:
        inner += ["--resume-cold"]
    if args.cache_map:
        inner += ["--cache-map", str(args.cache_map.resolve())]
    cmd = ["systemd-run", "--user", "--wait", "--collect", "--pipe", "--unit=" + unit,
           "--property=MemoryMax=" + str(args.memory_gib) + "G", "--property=MemorySwapMax=0",
           "--property=LimitNOFILE=65536", "--property=TasksMax=1024", "--property=CPUQuota=800%",
           "/usr/bin/taskset", "--cpu-list", cpu_value] + inner
    invocation = root / ("REPRODUCTION_RESUME_INVOCATION-" + unit + ".json" if RESUMING_COLD else "REPRODUCTION_INVOCATION.json")
    write_json(invocation, {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
               "command": cmd, "script_sha256": sha(__file__), "pins_sha256": PIN_SHA256,
               "source_inputs": {arm: frozen["arms"][arm]["commit"] for arm in args.arms},
               "cache_map_sha256": sha(args.cache_map) if args.cache_map else None,
               "bounded_host_reproduction_not_discovery_sandbox": True, "inference_calls": 0})
    disk_samples = []
    prefix = "scope-resume-" + unit if RESUMING_COLD else "scope"
    with (root / (prefix + ".stdout")).open("x") as out, (root / (prefix + ".stderr")).open("x") as err:
        process = subprocess.Popen(cmd, stdout=out, stderr=err)
        next_sample = 0.0
        while process.poll() is None:
            if time.monotonic() >= next_sample:
                usage = subprocess.run(["/usr/bin/du", "-sk", str(root)], capture_output=True, text=True)
                need(usage.returncode == 0, "owned scratch accounting failed")
                allocated = int(usage.stdout.split()[0]) * 1024
                disk_samples.append({"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
                                     "allocated_bytes": allocated})
                if allocated > args.scratch_gib * 1024**3:
                    write_json(root / "SCRATCH_GUARD_STOP.json", {"limit_bytes": args.scratch_gib * 1024**3,
                               "observed_allocated_bytes": allocated, "owned_unit": unit,
                               "action": "stop only this reproduction's systemd unit; preserve all evidence"})
                    subprocess.run(["systemctl", "--user", "stop", unit], check=True)
                next_sample = time.monotonic() + 10
            time.sleep(0.5)
        returncode = process.wait()
    write_json(root / ("SCRATCH_SAMPLES-" + unit + ".json"), {"samples": disk_samples,
               "allocated_block_sum_peak_sampled_lower_bound_bytes": max((row["allocated_bytes"] for row in disk_samples), default=None),
               "limit_bytes": args.scratch_gib * 1024**3,
               "note": "du allocated-block sum may include shared extents; sample maximum is not an exact exclusive host-space peak."})
    need(returncode == 0, "bounded reproduction failed; original logs preserved under " + str(root))
    need((root / "RESULT.json").is_file(), "successful scope exited without final acceptance receipt")
    print("PASS_BASELINE_COMPONENT_REPLAY", str(root / "RESULT.json"))


if __name__ == "__main__":
    main()
