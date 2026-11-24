#!/usr/bin/env python3
"""Deterministic, hash-checked research export; never includes unlisted files."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import tempfile
import zipfile


def need(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def pairs(items):
    result = {}
    for key, value in items:
        need(key not in result, "Duplicate JSON key")
        result[key] = value
    return result


def parse(data):
    return json.loads(data, object_pairs_hook=pairs,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))


def path_ok(name):
    p = PurePosixPath(name)
    return bool(name) and not p.is_absolute() and ".." not in p.parts and "\\" not in name and str(p) == name


def validate_manifest(manifest):
    need(isinstance(manifest, dict) and set(manifest) ==
         {"format", "source_commit", "base_commit", "branch", "readme", "files"},
         "Unexpected manifest fields")
    need(manifest.get("format") == "IEANTN_RH_ONE_PRIME_EVIDENCE_V1", "Wrong bundle format")
    for field in ("source_commit", "base_commit"):
        value = manifest[field]
        need(isinstance(value, str) and len(value) == 40
             and all(c in "0123456789abcdef" for c in value), "Invalid commit identity")
    need(isinstance(manifest["branch"], str) and 0 < len(manifest["branch"]) <= 200
         and "\n" not in manifest["branch"], "Invalid branch identity")
    need(isinstance(manifest["readme"], str)
         and 0 < len(manifest["readme"].encode()) <= 65536, "Invalid README")
    files = manifest.get("files")
    need(isinstance(files, list) and 1 <= len(files) <= 10000, "Invalid file population")
    seen = set()
    for row in files:
        need(set(row) == {"path", "bytes", "sha256"}, "Unexpected row fields")
        name = row["path"]
        need(isinstance(name, str) and path_ok(name) and name not in seen, "Invalid/duplicate path")
        need(name not in {"BUNDLE_MANIFEST.json", "BUNDLE_README.txt"}, "Reserved path")
        need(type(row["bytes"]) is int and 0 <= row["bytes"] <= 32 * 1024**2, "Invalid file size")
        need(isinstance(row["sha256"], str) and len(row["sha256"]) == 64
             and all(c in "0123456789abcdef" for c in row["sha256"]), "Invalid SHA-256")
        seen.add(name)
    need(sum(row["bytes"] for row in files) <= 256 * 1024**2, "Export exceeds documented bound")
    return files


def verify(archive, destination=None):
    with zipfile.ZipFile(archive) as z:
        infos = z.infolist()
        names = [i.filename for i in infos]
        need(len(names) == len(set(names)), "Duplicate archive member")
        need(all(path_ok(n) for n in names), "Unsafe archive member")
        need(all(i.file_size <= 32 * 1024**2 for i in infos), "Oversized archive member")
        need(sum(i.file_size for i in infos) <= 256 * 1024**2, "Oversized archive")
        manifest = parse(z.read("BUNDLE_MANIFEST.json"))
        files = validate_manifest(manifest)
        need(z.read("BUNDLE_README.txt") == manifest["readme"].encode(),
             "README bytes differ from manifest")
        need(set(names) == {r["path"] for r in files} | {"BUNDLE_MANIFEST.json", "BUNDLE_README.txt"},
             "Archive population mismatch")
        data = {}
        for row in files:
            raw = z.read(row["path"])
            need(len(raw) == row["bytes"] and sha(raw) == row["sha256"], "Artifact hash/size mismatch")
            data[row["path"]] = raw
        if destination is not None:
            need(not os.path.lexists(destination), "Fresh extraction directory required")
            destination.mkdir(parents=True)
            for name in names:
                p = destination / name
                p.parent.mkdir(parents=True, exist_ok=True)
                p.write_bytes(data[name] if name in data else z.read(name))
    return {"status": "PASS_EXACT_ARCHIVE_POPULATION_AND_ALL_SHA256", "files": len(files),
            "archive_sha256": sha(Path(archive).read_bytes()), "archive_bytes": Path(archive).stat().st_size,
            "source_commit": manifest["source_commit"]}


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    sub = ap.add_subparsers(dest="action", required=True)
    build = sub.add_parser("build", allow_abbrev=False)
    build.add_argument("--repository", type=Path, required=True)
    build.add_argument("--selection", type=Path, required=True)
    build.add_argument("--output", type=Path, required=True)
    check = sub.add_parser("verify", allow_abbrev=False)
    check.add_argument("--archive", type=Path, required=True)
    check.add_argument("--extract", type=Path)
    a = ap.parse_args()
    if a.action == "verify":
        print(json.dumps(verify(a.archive, a.extract)))
        return
    manifest = parse(a.selection.read_bytes())
    files = validate_manifest(manifest)
    root = a.repository.resolve(strict=True)
    need(not os.path.lexists(a.output), "Fresh archive output required")
    a.output.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(dir=a.output.parent, prefix=".bundle-")
    os.close(fd)
    try:
        with zipfile.ZipFile(temporary, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9) as z:
            def put(name, raw):
                info = zipfile.ZipInfo(name, date_time=(2026, 11, 24, 0, 0, 0))
                info.compress_type = zipfile.ZIP_DEFLATED
                info.external_attr = 0o100644 << 16
                z.writestr(info, raw, compresslevel=9)
            put("BUNDLE_MANIFEST.json", (json.dumps(manifest, indent=2, ensure_ascii=False) + "\n").encode())
            put("BUNDLE_README.txt", manifest["readme"].encode())
            for row in sorted(files, key=lambda r: r["path"]):
                p = root / row["path"]
                need(not p.is_symlink() and p.resolve(strict=True).is_relative_to(root), "Non-owned/symlink source")
                raw = p.read_bytes()
                need(len(raw) == row["bytes"] and sha(raw) == row["sha256"], "Reviewed source changed")
                put(row["path"], raw)
        result = verify(temporary)
        os.link(temporary, a.output)
    finally:
        Path(temporary).unlink(missing_ok=True)
    print(json.dumps(result))


if __name__ == "__main__":
    main()
