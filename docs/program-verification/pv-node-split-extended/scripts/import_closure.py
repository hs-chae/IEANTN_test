"""Static import closure of Lean modules, by package, from source files only (no build, no Lake).

usage: python import_closure.py <project-dir> <root-module> [<root-module> ...]

Packages are read from <project-dir>/lake-manifest.json (path packages resolved relative to the project);
git packages (Mathlib, Batteries, ...) are counted as one bucket and not walked. Prints, per package, how many
modules of the closure come from it, and how many of them are `CertData` certificate modules.
"""
import json, pathlib, re, sys

proj = pathlib.Path(sys.argv[1]).resolve(); roots = sys.argv[2:]
man = json.loads((proj / "lake-manifest.json").read_text())
pkg_dirs = {"<root>": proj}
for p in man["packages"]:
    if p["type"] == "path":
        pkg_dirs[p["name"]] = (proj / p["dir"]).resolve()
EXTERNAL = ("Mathlib", "Batteries", "Aesop", "Qq", "ProofWidgets", "Plausible", "ImportGraph", "LeanSearchClient", "Cli",
            "Lean", "Init", "Std", "Lake")


def locate(mod):
    rel = pathlib.Path(*mod.split(".")).with_suffix(".lean")
    hits = [(n, d / rel) for n, d in pkg_dirs.items() if (d / rel).is_file()]
    return hits


seen, ext, missing, order = {}, set(), set(), list(roots)
while order:
    m = order.pop()
    if m in seen or m in ext or m in missing: continue
    if m.split(".")[0] in EXTERNAL:
        ext.add(m); continue
    hits = locate(m)
    if not hits:
        missing.add(m); continue
    name, f = hits[0]
    seen[m] = (name, str(f), len(hits))
    for line in f.read_text(errors="replace").splitlines():
        s = line.strip()
        if s.startswith("import "):
            for x in s[len("import "):].split():
                if re.match(r"^[A-Za-z_][\w.']*$", x): order.append(x)
        elif s and not s.startswith(("--", "/-", "public", "module", "prelude")) and not s.startswith("import"):
            if s.startswith(("namespace", "open", "set_option", "theorem", "def", "lemma", "noncomputable", "section", "variable", "/--", "abbrev", "structure", "@[", "instance", "universe")):
                break
by = {}
for m, (n, f, k) in seen.items():
    b = by.setdefault(n, [0, 0]); b[0] += 1
    if "CertData" in m: b[1] += 1
ambiguous = sorted(m for m, (n, f, k) in seen.items() if k > 1)
print(json.dumps({"project": str(proj), "roots": roots, "modules_in_repo_packages": len(seen),
                  "external_modules_referenced": len(ext), "unresolved": sorted(missing)[:10],
                  "by_package": {n: {"modules": v[0], "certdata": v[1]} for n, v in sorted(by.items(), key=lambda t: -t[1][0])},
                  "module_names_found_in_several_packages": ambiguous[:20]}, indent=1))
