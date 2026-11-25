#!/usr/bin/env python3
"""Verify a compact source/evidence bundle before extracting or reproducing it.

Byte identity is not a Lean proof. Run the included materializer and study
reproduction commands afterward to regenerate and check the mathematics.
"""
import argparse
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import stat
import tempfile
import zipfile


def need(ok, message):
    if not ok:
        raise ValueError(message)


def strict(raw):
    def unique(items):
        result = {}
        for key, value in items:
            need(key not in result, "Duplicate manifest key")
            result[key] = value
        return result
    def finite(value):
        result = float(value)
        need(math.isfinite(result), "Nonfinite manifest number")
        return result
    return json.loads(raw, object_pairs_hook=unique, parse_float=finite,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def safe_name(name):
    path = PurePosixPath(name)
    need(name and not path.is_absolute() and str(path) == name and ".." not in path.parts,
         "Nonrelative archive member")
    need("\\" not in name and ":" not in name and not name.endswith("/"), "Invalid archive member")
    return path


def verify(archive, expected):
    need(len(expected) == 64 and all(c in "0123456789abcdef" for c in expected), "Exact lowercase archive SHA256 required")
    need(digest(archive.read_bytes()) == expected, "Archive SHA256 differs")
    with zipfile.ZipFile(archive) as bundle:
        members = bundle.infolist()
        names = [m.filename for m in members]
        need(len(names) == len(set(names)) and "BUNDLE_MANIFEST.json" in names, "Missing or duplicate member")
        need(len(members) <= 10000 and sum(m.file_size for m in members) <= 2*2**30, "Unexpected bundle population/size")
        for member in members:
            safe_name(member.filename)
            need(not member.flag_bits & 1, "Encrypted bundle member")
            kind = stat.S_IFMT(member.external_attr >> 16)
            need(kind in (0, stat.S_IFREG), "Nonregular bundle member")
        manifest = strict(bundle.read("BUNDLE_MANIFEST.json"))
        need(manifest.get("schema") == "RH080_COMPACT_REPRODUCIBILITY_BUNDLE_V1", "Wrong bundle schema")
        commit = manifest.get("source_commit")
        need(isinstance(commit,str) and len(commit)==40 and all(c in "0123456789abcdef" for c in commit), "Unpinned source commit")
        rows = manifest["files"]
        need(isinstance(rows,list) and rows, "Empty payload manifest")
        listed = [row["path"] for row in rows]
        need(len(listed) == len(set(listed)) and set(names) == set(listed) | {"BUNDLE_MANIFEST.json"}, "Payload population differs")
        for row in rows:
            need(set(row) == {"path","bytes","sha256","role"}, "Unexpected payload schema")
            safe_name(row["path"])
            need(type(row["bytes"]) is int and row["bytes"] >= 0, "Invalid payload size")
            raw = bundle.read(row["path"])
            need(len(raw)==row["bytes"] and digest(raw)==row["sha256"], "Payload bytes differ: "+row["path"])
        readme = bundle.read("README_REPRODUCE.txt")
        need(digest(readme)==manifest["readme_sha256"], "Reserved README differs")
        generated = manifest["omitted_regenerable_sources"]
        need(isinstance(generated,list) and len(generated)==49 and len({x["path"] for x in generated})==49, "Wrong generated-source population")
        for row in generated:
            safe_name(row["path"])
            need(type(row["bytes"]) is int and row["bytes"]>0, "Invalid generated source size")
            h=row["sha256"]
            need(isinstance(h,str) and len(h)==64 and all(c in "0123456789abcdef" for c in h), "Invalid generated source hash")
        need(not set(x["path"] for x in generated) & set(names), "Regenerable source unexpectedly bundled")
        need(manifest["accepted_proof_sources_retained_in_pinned_repository"] is True,
             "Accepted source preservation boundary missing")
        return manifest


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--archive",type=Path,required=True)
    parser.add_argument("--expected-sha256",required=True)
    parser.add_argument("--extract",type=Path)
    parser.add_argument("--receipt",type=Path,required=True)
    args = parser.parse_args()
    need(not args.receipt.exists(), "Fresh verification receipt required")
    need(args.extract is None or not args.extract.exists(), "Fresh extraction directory required")
    manifest = verify(args.archive,args.expected_sha256)
    if args.extract:
        args.extract.mkdir(parents=True)
        with zipfile.ZipFile(args.archive) as bundle:
            for row in manifest["files"]:
                target=args.extract.joinpath(*PurePosixPath(row["path"]).parts)
                target.parent.mkdir(parents=True,exist_ok=True)
                with target.open("xb") as stream: stream.write(bundle.read(row["path"]))
            (args.extract/"BUNDLE_MANIFEST.json").write_bytes(bundle.read("BUNDLE_MANIFEST.json"))
        for row in manifest["files"]:
            target=args.extract/row["path"]
            need(digest(target.read_bytes())==row["sha256"],"Extracted bytes differ")
    receipt={"status":"PASS_ARCHIVE_AND_PAYLOAD_BYTES_NOT_A_MATHEMATICAL_PROOF",
             "archive_sha256":args.expected_sha256,"source_commit":manifest["source_commit"],
             "payload_files":len(manifest["files"]),"omitted_generated_sources":49,
             "extracted":str(args.extract) if args.extract else None}
    args.receipt.parent.mkdir(parents=True,exist_ok=True)
    fd,name=tempfile.mkstemp(prefix=".verified-",dir=args.receipt.parent)
    temporary=Path(name)
    try:
        with os.fdopen(fd,"w") as stream:
            stream.write(json.dumps(receipt,indent=2,allow_nan=False)+"\n")
        os.link(temporary,args.receipt)
    finally:
        temporary.unlink(missing_ok=True)
    print(json.dumps(receipt))


if __name__=="__main__":main()
