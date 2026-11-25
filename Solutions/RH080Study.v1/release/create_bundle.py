#!/usr/bin/env python3
"""Create a deterministic compact bundle from an explicitly reviewed file list."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import zipfile

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from verify_bundle import need,safe_name,strict


def sha(raw):return hashlib.sha256(raw).hexdigest()


def main():
    parser=argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--repository",type=Path,required=True)
    parser.add_argument("--selection",type=Path,required=True)
    parser.add_argument("--output",type=Path,required=True)
    args=parser.parse_args()
    need(not args.output.exists(),"Fresh bundle required")
    selection=strict(args.selection.read_bytes())
    need(selection["reviewed_by"]=="/root","Reviewed selection required")
    need(selection.get("schema")=="RH080_REVIEWED_COMPACT_BUNDLE_SELECTION_V1","Wrong selection schema")
    rows=selection["files"]
    names=[row["path"] for row in rows]
    need(len(names)==len(set(names)),"Duplicate selected source")
    need(not {"BUNDLE_MANIFEST.json","README_REPRODUCE.txt"} & set(names),"Reserved bundle member in selection")
    blobs={}
    for row in rows:
        safe_name(row["path"])
        path=args.repository/row["path"]
        need(path.is_file() and not path.is_symlink() and path.resolve().is_relative_to(args.repository.resolve()),"Nonregular/outside source")
        raw=path.read_bytes()
        need(len(raw)==row["bytes"] and sha(raw)==row["sha256"],"Reviewed source changed")
        blobs[row["path"]]=raw
    readme=selection["readme"].encode()
    blobs["README_REPRODUCE.txt"]=readme
    files=rows+[{"path":"README_REPRODUCE.txt","bytes":len(readme),"sha256":sha(readme),"role":"reproduction_instructions"}]
    manifest={"schema":"RH080_COMPACT_REPRODUCIBILITY_BUNDLE_V1","source_commit":selection["source_commit"],
              "files":files,"readme_sha256":sha(readme),"omitted_regenerable_sources":selection["omitted_regenerable_sources"],
              "accepted_proof_sources_retained_in_pinned_repository":True,
              "proof_status_boundary":"Archive identity/regeneration is not a Lean proof; accepted source-cold receipts and fresh reproduction commands are included."}
    blobs["BUNDLE_MANIFEST.json"]=(json.dumps(manifest,indent=2,allow_nan=False)+"\n").encode()
    args.output.parent.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(args.output,"x",compression=zipfile.ZIP_DEFLATED,compresslevel=9)as bundle:
        for name,raw in sorted(blobs.items()):
            info=zipfile.ZipInfo(name,date_time=(2026,11,25,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED
            info.external_attr=0o100644<<16;bundle.writestr(info,raw,compresslevel=9)
    result={"status":"CREATED_COMPACT_BUNDLE_REQUIRES_INDEPENDENT_READBACK","bytes":args.output.stat().st_size,
            "sha256":sha(args.output.read_bytes()),"files":len(blobs),"omitted_generated_sources":49,
            "selection_sha256":sha(args.selection.read_bytes())}
    print(json.dumps(result))


if __name__=="__main__":main()
