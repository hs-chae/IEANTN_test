#!/usr/bin/env python3
"""Actual bundle CLI controls in normal, -O and -OO modes, using tiny fixtures.

Copies and hashes the exact builder before execution. Every negative invokes the
real CLI, checks nonzero status, checks empty stdout and no extraction/output.
No assertion depends on Python optimization. Numerical proof acceptance is not
part of these storage and reproducibility controls.
"""
import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import warnings
import zipfile


def need(value, message):
    if not value:
        raise ValueError(message)


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def encoded(value):
    return (json.dumps(value, indent=2, ensure_ascii=False)+"\n").encode()


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--script", type=Path, required=True)
    ap.add_argument("--out", type=Path, required=True)
    args=ap.parse_args()
    out=args.out.absolute()
    need(not out.exists(), "Fresh owned test directory required")
    out.mkdir(parents=True)
    original=args.script.resolve(strict=True).read_bytes()
    script=out/"executed_builder.py"
    script.write_bytes(original)
    source_sha=digest(original)
    repo=out/"tiny-repository"
    repo.mkdir()
    sources={"proof.lean":b"-- deterministic tiny source fixture\nexample : 1 = 1 := rfl\n", "data/values.json":b"[3,5,7]\n"}
    for name, raw in sources.items():
        p=repo/name
        p.parent.mkdir(parents=True,exist_ok=True)
        p.write_bytes(raw)
    manifest={"format":"IEANTN_RH_ONE_PRIME_EVIDENCE_V1", "source_commit":"a"*40, "base_commit":"b"*40, "branch":"research/tiny-fixture",
              "readme":"Tiny deterministic reproduction fixture. No mathematical result claimed.\n",
              "files":[{"path":name,"bytes":len(raw),"sha256":digest(raw)} for name,raw in sorted(sources.items())]}
    selection=out/"selection.json"
    selection.write_bytes(encoded(manifest))
    rows=[]

    def call(mode, label, arguments, negative=False, absent=None):
        tag=mode[0]+"-"+label
        command=[sys.executable,*mode[1],str(script),*map(str,arguments)]
        process=subprocess.run(command,capture_output=True)
        stdout=out/(tag+".stdout")
        stderr=out/(tag+".stderr")
        stdout.write_bytes(process.stdout)
        stderr.write_bytes(process.stderr)
        no_output=absent is None or not absent.exists()
        expected_guard=None
        if negative:
            guards={
                "build-hash":"Reviewed source changed", "build-size":"Reviewed source changed",
                "build-missing":"FileNotFoundError", "build-duplicate":"Invalid/duplicate path",
                "build-traversal":"Invalid/duplicate path", "build-reserved":"Reserved path",
                "build-duplicate-json":"Duplicate JSON key", "build-wrong-commit":"Invalid commit identity",
                "build-nonstring-readme":"Invalid README", "build-unknown-arg":"unrecognized arguments",
                "build-existing-output":"Fresh archive output required",
                "verify-payload":"Artifact hash/size mismatch", "verify-hash":"Artifact hash/size mismatch",
                "verify-size":"Artifact hash/size mismatch", "verify-extra":"Archive population mismatch",
                "verify-missing":"Archive population mismatch", "verify-traversal":"Unsafe archive member",
                "verify-duplicate":"Duplicate archive member", "verify-duplicate-json":"Duplicate JSON key",
                "verify-duplicate-row":"Invalid/duplicate path", "verify-readme":"README bytes differ from manifest",
                "verify-wrong-commit":"Invalid commit identity", "verify-nonstring-readme":"Invalid README",
                "verify-existing-extraction":"Fresh extraction directory required",
                "verify-unknown-arg":"unrecognized arguments",
            }
            expected_guard=guards[label]
            passed=(process.returncode!=0 and not process.stdout and no_output
                    and expected_guard.encode() in process.stderr)
        else:
            passed=process.returncode==0
            try:
                result=json.loads(process.stdout)
                passed=passed and result.get("status")=="PASS_EXACT_ARCHIVE_POPULATION_AND_ALL_SHA256"
            except Exception:
                passed=False
        rows.append({"case":tag,"command":command,"expected_rejection":negative,
                     "returncode":process.returncode,"stdout_sha256":digest(process.stdout),
                     "stderr_sha256":digest(process.stderr),"expected_absent_output":str(absent) if absent else None,
                     "output_absent":no_output,"expected_stderr_guard":expected_guard,"pass":passed})
        return process, passed

    for mode in [("normal",[]),("O",["-O"]),("OO",["-OO"])]:
        prefix=mode[0]
        good=out/(prefix+"-good.zip")
        twin=out/(prefix+"-twin.zip")
        _, ok=call(mode,"build",["build","--repository",repo,"--selection",selection,"--output",good])
        need(ok,"Positive build failed; preserve current evidence")
        _, ok=call(mode,"deterministic-build",["build","--repository",repo,"--selection",selection,"--output",twin])
        need(ok and good.read_bytes()==twin.read_bytes(),"Independent builds not byte-identical")
        call(mode,"verify",["verify","--archive",good])
        extraction=out/(prefix+"-extracted")
        _, ok=call(mode,"extract",["verify","--archive",good,"--extract",extraction])
        need(ok,"Positive extraction failed")
        for name, raw in sources.items():
            need((extraction/name).read_bytes()==raw,"Extracted payload changed")
        need((extraction/"BUNDLE_README.txt").read_bytes()==manifest["readme"].encode(),"Extracted README changed")
        need(json.loads((extraction/"BUNDLE_MANIFEST.json").read_bytes())==manifest,"Extracted manifest changed")

        def bad_build(label, change=None, raw=None):
            copy=json.loads(json.dumps(manifest))
            if change:
                change(copy)
            p=out/(prefix+"-"+label+"-selection.json")
            p.write_bytes(raw if raw is not None else encoded(copy))
            target=out/(prefix+"-"+label+".zip")
            call(mode,label,["build","--repository",repo,"--selection",p,"--output",target],True,target)

        bad_build("build-hash",lambda m:m["files"][0].update(sha256="0"*64))
        bad_build("build-size",lambda m:m["files"][0].update(bytes=m["files"][0]["bytes"]+1))
        bad_build("build-missing",lambda m:m["files"][0].update(path="absent.lean"))
        bad_build("build-duplicate",lambda m:m["files"].append(dict(m["files"][0])))
        bad_build("build-traversal",lambda m:m["files"][0].update(path="../outside.lean"))
        bad_build("build-reserved",lambda m:m["files"][0].update(path="BUNDLE_README.txt"))
        raw=encoded(manifest).decode().replace('"format":','"format":"bad", "format":',1).encode()
        bad_build("build-duplicate-json",raw=raw)
        bad_build("build-wrong-commit",lambda m:m.update(source_commit="not-a-commit"))
        bad_build("build-nonstring-readme",lambda m:m.update(readme=17))
        target=out/(prefix+"-unsupported.zip")
        call(mode,"build-unknown-arg",["build","--repository",repo,"--selection",selection,"--output",target,"--unknown"],True,target)
        call(mode,"build-existing-output",["build","--repository",repo,"--selection",selection,"--output",good],True)

        with zipfile.ZipFile(good) as archive:
            members=[(info,archive.read(info.filename)) for info in archive.infolist()]

        def bad_archive(label, mutate):
            altered=mutate([(info,raw) for info,raw in members])
            p=out/(prefix+"-"+label+".zip")
            with warnings.catch_warnings():
                warnings.simplefilter("ignore",UserWarning)
                with zipfile.ZipFile(p,"w") as z:
                    for info,raw in altered:
                        z.writestr(info,raw)
            destination=out/(prefix+"-"+label+"-extract")
            call(mode,label,["verify","--archive",p,"--extract",destination],True,destination)

        def edit_manifest(items, change=None, raw_transform=None):
            result=[]
            for info,raw in items:
                if info.filename=="BUNDLE_MANIFEST.json":
                    if raw_transform:
                        raw=raw_transform(raw)
                    else:
                        m=json.loads(raw)
                        change(m)
                        raw=encoded(m)
                result.append((info,raw))
            return result

        bad_archive("verify-payload",lambda xs:[(i,b"changed payload\n" if i.filename=="proof.lean" else raw) for i,raw in xs])
        bad_archive("verify-hash",lambda xs:edit_manifest(xs,lambda m:m["files"][0].update(sha256="0"*64)))
        bad_archive("verify-size",lambda xs:edit_manifest(xs,lambda m:m["files"][0].update(bytes=m["files"][0]["bytes"]+1)))
        bad_archive("verify-extra",lambda xs:xs+[(zipfile.ZipInfo("unlisted.lean"),b"unlisted\n")])
        bad_archive("verify-missing",lambda xs:[(i,raw) for i,raw in xs if i.filename!="proof.lean"])
        bad_archive("verify-traversal",lambda xs:xs+[(zipfile.ZipInfo("../outside.lean"),b"outside\n")])
        bad_archive("verify-duplicate",lambda xs:xs+[next((i,raw) for i,raw in xs if i.filename=="proof.lean")])
        bad_archive("verify-duplicate-json",lambda xs:edit_manifest(xs,raw_transform=lambda raw:raw.replace(b'"format":',b'"format":"bad", "format":',1)))
        bad_archive("verify-duplicate-row",lambda xs:edit_manifest(xs,lambda m:m["files"].append(dict(m["files"][0]))))
        bad_archive("verify-readme",lambda xs:[(i,b"changed guide\n" if i.filename=="BUNDLE_README.txt" else raw) for i,raw in xs])
        bad_archive("verify-wrong-commit",lambda xs:edit_manifest(xs,lambda m:m.update(source_commit="not-a-commit")))
        bad_archive("verify-nonstring-readme",lambda xs:edit_manifest(xs,lambda m:m.update(readme=17)))
        call(mode,"verify-existing-extraction",["verify","--archive",good,"--extract",extraction],True)
        call(mode,"verify-unknown-arg",["verify","--archive",good,"--unknown"],True)

    failed=[r["case"] for r in rows if not r["pass"]]
    report={"status":"PASS_ALL_ACTUAL_BUNDLE_CLI_CONTROLS" if not failed else "FAIL_ACTUAL_BUNDLE_CLI_CONTROLS",
            "scope":"Archive storage/reproduction controls; not mathematical proof acceptance",
            "builder_sha256":source_sha,"test_sha256":digest(Path(__file__).read_bytes()),
            "python_version":sys.version,"cases":len(rows),"positive_cases":sum(not r["expected_rejection"] for r in rows),
            "negative_cases":sum(r["expected_rejection"] for r in rows),"failed_cases":failed,"rows":rows}
    (out/"RESULT.json").write_bytes(encoded(report))
    print(json.dumps({k:report[k] for k in ["status","builder_sha256","cases","positive_cases","negative_cases","failed_cases"]}))
    if failed:
        raise SystemExit(1)


if __name__=="__main__":
    main()
