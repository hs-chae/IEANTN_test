"""Exact non-Lean inputs of the fixed finite-Fap cold replay.

CSV files contain untrusted literal proposals, never proofs. The unchanged
Lean loaders quote Int/List data; downstream kernel proofs check the trace.
"""
from __future__ import annotations
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil


def need(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_json(path):
    def pairs(items):
        result = {}
        for key, value in items:
            need(key not in result, "Duplicate JSON key " + key)
            result[key] = value
        return result
    def bad(value):
        raise ValueError("Nonfinite JSON value " + value)
    return json.loads(path.read_text(encoding="utf-8"), object_pairs_hook=pairs, parse_constant=bad)


def relative(value, description):
    need(type(value) is str and value and "\\" not in value,
         "Invalid relative " + description)
    path = PurePosixPath(value)
    need(not path.is_absolute() and ".." not in path.parts and "." not in path.parts
         and str(path) == value and value != ".", "Unsafe relative " + description)
    return Path(*path.parts)


def requests(source_rows):
    """Census every actual literal-loader invocation in the pinned sources."""
    found = {}
    destinations = set()
    for row in source_rows:
        origin = Path(row.get("origin", row.get("source_origin", "")))
        need(origin.is_file(), "Missing literal-owner Lean source")
        need(sha(origin) == row["source_sha256"], "Literal-owner Lean source changed")
        need(type(row["module"]) is str and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", row["module"]) is not None, "Invalid Lean module identity")
        parent = Path(row["module"].replace(".", "/")).parent
        for line, text in enumerate(origin.read_text().splitlines(), 1):
            pair = re.fullmatch(r'pair_certificate (\w+) from "([^"]+)" count (\d+)', text)
            forest = re.fullmatch(r'forest_certificate (\w+) from "([^"]+)" width (\d+) rows (\d+)', text)
            if not pair and not forest:
                continue
            match = pair or forest
            filename = relative(match[2], "loader filename")
            destination = (parent / filename).as_posix()
            relative(destination, "literal destination")
            identity = (row["module"], match[1])
            need(identity not in found, "Duplicate literal declaration identity")
            need(destination not in destinations, "Duplicate literal destination")
            destinations.add(destination)
            item = dict(owner_module=row["module"], declaration=match[1], line=line,
                        loader="pair_certificate" if pair else "forest_certificate",
                        destination=destination, source_origin=str((origin.parent / filename).resolve()))
            if pair:
                item.update(count=int(match[3]), entries=int(match[3]))
            else:
                width, rows = int(match[3]), int(match[4])
                need(width > 0, "Zero forest literal width")
                item.update(width=width, rows=rows, entries=width * rows)
            found[identity] = item
    return found


def check_file(path, row):
    need(path.is_file(), "Missing literal data " + str(path))
    need(type(row["bytes"]) is int and row["bytes"] > 0 and path.stat().st_size == row["bytes"],
         "Literal data byte length differs " + str(path))
    need(type(row["sha256"]) is str and re.fullmatch(r"[0-9a-f]{64}", row["sha256"]),
         "Invalid literal data hash")
    digest = hashlib.sha256()
    count = 0
    with path.open("rb") as stream:
        for line in stream:
            digest.update(line)
            # Locked data are ASCII decimal pairs terminated by LF.
            need(re.fullmatch(rb"-?[0-9]+,-?[0-9]+\n", line) is not None,
                 "Malformed literal pair data " + str(path))
            count += 1
    need(digest.hexdigest() == row["sha256"], "Literal data hash differs " + str(path))
    need(count == row["entries"], "Literal data count/width/rows differ " + str(path))


def inventory_data(data_rows, source_rows):
    expected = requests(source_rows)
    need(type(data_rows) is list and len(data_rows) == len(expected) == 34,
         "Missing/extra literal data universe")
    identities = set()
    destinations = set()
    origins = set()
    normalized = []
    for row in data_rows:
        identity = (row["owner_module"], row["declaration"])
        need(identity not in identities, "Duplicate literal data identity")
        identities.add(identity)
        need(identity in expected, "Unknown literal data declaration")
        request = expected[identity]
        for key, value in request.items():
            need(type(row.get(key)) is type(value) and row.get(key) == value,
                 "Literal loader identity/dimensions differ " + str(identity) + " " + key)
        relative(row["destination"], "literal destination")
        need(row["destination"] not in destinations, "Duplicate literal data destination")
        need(row["source_origin"] not in origins, "Duplicate literal data input")
        destinations.add(row["destination"])
        origins.add(row["source_origin"])
        allowed = set(request) | {"bytes", "sha256"}
        need(set(row) == allowed, "Unexpected literal data metadata fields")
        check_file(Path(row["source_origin"]), row)
        normalized.append(dict(row))
    need(identities == set(expected), "Omitted actual literal data declaration")
    return sorted(normalized, key=lambda row: row["destination"])


def portable_data(repository, data_rows, source_rows):
    """Resolve repository inputs before invoking the common identity checker."""
    need(type(data_rows) is list, "Literal data list required")
    normalized = []
    for raw in data_rows:
        row = dict(raw)
        path = relative(row.pop("path"), "literal input path")
        origin = (repository / path).resolve()
        need(origin.is_relative_to(repository), "Literal input escapes repository")
        row["source_origin"] = str(origin)
        # Check destination safety before comparison with the source locator.
        relative(row["destination"], "literal destination")
        normalized.append(row)
    return inventory_data(normalized, source_rows)


def stage_data(source_root, rows):
    staged = []
    lean_paths = {p.relative_to(source_root).as_posix() for p in source_root.rglob("*.lean")}
    for row in rows:
        destination = relative(row["destination"], "literal destination")
        need(destination.as_posix() not in lean_paths, "Literal data shadows Lean source")
        target = source_root / destination
        need(target.resolve().is_relative_to(source_root.resolve()), "Literal destination escapes source root")
        need(not target.exists(), "Fresh literal snapshot required")
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(row["source_origin"], target)
        check_file(target, row)
        staged.append(dict(row, snapshot=str(target)))
    return staged


def verify_data(source_root, staged, source_rows, inventory_rows):
    normalized = [{k: v for k, v in row.items() if k != "snapshot"} for row in staged]
    checked = inventory_data(normalized, source_rows)
    need(checked == inventory_data(inventory_rows, source_rows), "Inventory/plan literal identities differ")
    owners = {row["module"]: Path(row["snapshot"]) for row in source_rows}
    for row in staged:
        target = source_root / relative(row["destination"], "literal destination")
        need(target.resolve().is_relative_to(source_root.resolve()), "Literal snapshot escapes source root")
        # Recorded absolute paths remain provenance when artifacts are relocated.
        module_parent = Path(row["owner_module"].replace(".", "/")).parent
        local_path = Path(row["destination"]).relative_to(module_parent)
        expected_snapshot = owners[row["owner_module"]].parent / local_path
        need(Path(row["snapshot"]) == expected_snapshot, "Literal snapshot/owning-source association differs")
        check_file(target, row)
    return checked
