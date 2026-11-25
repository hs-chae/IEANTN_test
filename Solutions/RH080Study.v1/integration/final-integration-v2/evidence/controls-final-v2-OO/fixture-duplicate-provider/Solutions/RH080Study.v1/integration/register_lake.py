#!/usr/bin/env python3
"""Register exactly the reviewed, hash-pinned local Lean providers with Lake."""
import argparse
import hashlib
import json
from pathlib import Path


def need(ok, message):
    if not ok:
        raise ValueError(message)


def read_json(path):
    def unique(items):
        result = {}
        for key, value in items:
            need(key not in result, "duplicate JSON key")
            result[key] = value
        return result
    return json.loads(path.read_bytes(), object_pairs_hook=unique,
                      parse_constant=lambda x: (_ for _ in ()).throw(ValueError(x)))


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def text_list(values):
    return "[" + ", ".join(json.dumps(v) for v in values) + "]"


def expected_files(repository, manifest):
    study = repository / "Solutions/RH080Study.v1"
    text = 'name = "RH080Study"\nversion = "0.1.0"\n'
    text += 'moreLeanArgs = ["-j2"]\n'
    text += "defaultTargets = " + text_list([g["library"] for g in manifest["groups"]]) + "\n\n"
    text += '[[require]]\nname = "IEANTN"\npath = "../.."\n'
    seen = set()
    for group in manifest["groups"]:
        root = repository / group["source_root"]
        need(root.resolve().is_relative_to(repository.resolve()), "provider outside checkout")
        names = []
        for entry in group["modules"]:
            module = entry["module"]
            need(module not in seen, "duplicate module provider: " + module)
            seen.add(module)
            path = root.joinpath(*module.split(".")).with_suffix(".lean")
            need(path.is_file() and not path.is_symlink(), "missing regular Lean provider")
            need(sha(path) == entry["sha256"], "provider changed: " + str(path))
            need("Audit" not in module and not module.endswith("Solution"), "replay-only provider")
            names.append(module)
        import os
        text += '\n[[lean_lib]]\nname = ' + json.dumps(group["library"]) + "\n"
        text += "srcDir = " + json.dumps(os.path.relpath(root, study)) + "\n"
        text += "roots = " + text_list(names) + "\n"
    outputs = {study / "lakefile.toml": text,
               study / "lean-toolchain": (repository / "lean-toolchain").read_text()}
    pinned = read_json(repository / "lake-manifest.json")
    inherited = []
    for entry in pinned["packages"]:
        row = dict(entry)
        row["inherited"] = True
        inherited.append(row)
    ieantn = {"type": "path", "scope": "", "name": "IEANTN",
              "manifestFile": "lake-manifest.json", "inherited": False,
              "dir": "../..", "configFile": "lakefile.toml"}

    def package_manifest(name, paths):
        return json.dumps({"version": pinned["version"], "packagesDir": ".lake/packages",
                           "packages": inherited + paths, "name": name,
                           "lakeDir": ".lake", "fixedToolchain": False}, indent=2) + "\n"

    outputs[study / "lake-manifest.json"] = package_manifest("RH080Study", [ieantn])
    for name in manifest["solution_projects"]:
        project = repository / "Solutions" / name
        need((project / "Solution.lean").is_file(), "solution missing")
        content = 'name = ' + json.dumps("solution_" + name.replace(".", "_")) + "\n"
        content += 'moreLeanArgs = ["-j2"]\n'
        content += 'defaultTargets = ["Solution"]\n\n'
        content += '[[require]]\nname = "RH080Study"\npath = "../RH080Study.v1"\n\n'
        content += '[[lean_lib]]\nname = "Solution"\nroots = ["Solution"]\n'
        outputs[project / "lakefile.toml"] = content
        outputs[project / "lean-toolchain"] = (repository / "lean-toolchain").read_text()
        parent = dict(ieantn)
        parent["inherited"] = True
        provider = {"type": "path", "scope": "", "name": "RH080Study",
                    "manifestFile": "lake-manifest.json", "inherited": False,
                    "dir": "../RH080Study.v1", "configFile": "lakefile.toml"}
        outputs[project / "lake-manifest.json"] = package_manifest(
            "solution_" + name.replace(".", "_"), [parent, provider])
    return outputs


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    here = Path(__file__).resolve().parent
    repository = here.parents[2]
    manifest = read_json(here / "LAKE_PROVIDER_MANIFEST.json")
    need(manifest.get("schema") == "RH080_LAKE_PROVIDERS_V1", "wrong manifest schema")
    outputs = expected_files(repository, manifest)
    for path, content in outputs.items():
        if args.check:
            need(path.read_text() == content, "Lake configuration differs: " + str(path))
        else:
            path.write_text(content)
    print(json.dumps({"status": "PASS_CHECKED_LAKE_REGISTRATION" if args.check else "GENERATED_LAKE_REGISTRATION",
                      "files": len(outputs),
                      "providers": sum(len(g["modules"]) for g in manifest["groups"]),
                      "scope": "Packaging and exact source identity; not a proof-build receipt"}))


if __name__ == "__main__":
    main()
