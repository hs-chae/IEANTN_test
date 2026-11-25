#!/usr/bin/env python3
"""Census every canonical conclusion; source-family flags are triage, not audit."""
import csv
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import yaml

S = Path(__file__).resolve().parents[1]
R = S.parents[1]
SIGNALS = ("RH", "CMS", "Schoenfeld", "Grenie", "Grenié", "Molteni", "Lee", "Nosal",
           "Blanquer", "Bellotti", "Wong", "Hasanalizade", "Platt", "Trudgian", "BPT",
           "Nicolas", "Green", "Box", "Perron", "Buthe", "Büthe", "Huxley", "Ramachandra")


def main():
    rows = []
    metadata = {}
    all_versions = []
    empty_versions = []
    for path in sorted((R / "IEANTN/Nodes").glob("*/*/formalization.yaml")):
        data = yaml.safe_load(path.read_text())
        node = data["node"]["id"]
        all_versions.append(node)
        if not data.get("conclusions", []):
            empty_versions.append(node)
        family = data["node"]["family"]
        lean = path.with_name("Conclusions.lean")
        text = lean.read_text()
        provenance = "\n".join([family, text, path.read_text()] +
                                 [p.read_text() for p in (path.with_name("README.md"),) if p.is_file()])
        matched = [word for word in SIGNALS if word.lower() in provenance.lower()]
        excluded = "ramanujan" in family.lower()
        for conclusion in data.get("conclusions", []):
            identity = node + "." + conclusion["id"]
            if identity in metadata:
                raise ValueError("Duplicate canonical conclusion identity")
            declaration = conclusion["declaration"]
            short = declaration.rsplit(".", 1)[-1]
            candidates = [i for i, line in enumerate(text.splitlines(), 1)
                          if re.match(r"^(?:noncomputable\s+)?def\s+" + re.escape(short) + r"(?:\s|:|\{|\()", line)]
            # Metadata identifies the compiler declaration. Multiple physical candidates
            # remain explicit rather than collapsing on a short name.
            line = candidates[0] if len(candidates) == 1 else ""
            imports = [(entry["node"] + "." + entry["conclusion"])
                       for entry in conclusion.get("imports", [])]
            row = {"file": str(lean.relative_to(R)), "declaration": declaration,
                   "physical_LF_line": line, "line_candidates": ";".join(map(str, candidates)),
                   "node": node, "conclusion": conclusion["id"], "node_kind": data["node"]["kind"],
                   "node_status": data["node"]["status"], "excluded_ramanujan": excluded,
                   "source_family_or_module_signals": ";".join(matched),
                   "literal_RH_in_module": "RiemannHypothesis" in text,
                   "declared_imports": ";".join(imports),
                   "designated_justification": conclusion.get("designated", ""),
                   "justification_kinds": ";".join(j.get("kind", "") for j in conclusion.get("justifications", [])),
                   "formal_source_sha256": hashlib.sha256(lean.read_bytes()).hexdigest(),
                   "proof_value_consumption": "NOT_ESTABLISHED_BY_THIS_CENSUS",
                   "primary_source_audit": "NOT_ESTABLISHED_BY_MECHANICAL_CENSUS",
                   "locator_status": "UNIQUE_METADATA_BASENAME_IN_THIS_FILE" if line else "REQUIRES_COMPILER_POSITION_DISAMBIGUATION"}
            metadata[identity] = {"row": row, "imports": imports}
            rows.append(row)
    rh = {key for key in metadata if key.startswith("RH.v1.")}
    changed = True
    while changed:
        changed = False
        for key, value in metadata.items():
            if key not in rh and any(i in rh for i in value["imports"]):
                rh.add(key)
                changed = True
    for key, value in metadata.items():
        value["row"]["declared_graph_reaches_RH_input"] = key in rh
    output = S / "estimates/CANONICAL_CONCLUSION_CENSUS.csv"
    buffer = io.StringIO(newline="")
    writer = csv.DictWriter(buffer, fieldnames=list(rows[0]))
    writer.writeheader()
    writer.writerows(rows)
    output.write_text(buffer.getvalue())
    summary = {"status": "COMPLETE_CANONICAL_METADATA_CENSUS_NOT_COMPLETE_SOURCE_AUDIT",
               "repository_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=R, text=True).strip(),
               "scope": "Every conclusion in every current canonical node/version formalization.yaml, including inactive/historical versions. Ramanujan is inventoried but excluded from research/scoring.",
               "selection_author": "/root", "selected_population": "ALL canonical conclusions, without a citation/sorry/filename inclusion filter",
               "source_signal_predicate": "Case-insensitive occurrence of any listed word in family name, full Conclusions module, full YAML or enclosing README. This is broad provenance triage only; it proves neither RH dependence nor source absence.",
               "signals": SIGNALS, "node_versions": len(all_versions),
               "node_versions_with_conclusions": len({r["node"] for r in rows}),
               "empty_conclusion_versions": empty_versions, "conclusions": len(rows),
               "ramanujan_excluded_conclusions": sum(r["excluded_ramanujan"] for r in rows),
               "literal_RH_module_rows": sum(r["literal_RH_in_module"] for r in rows),
               "declared_graph_reaches_RH_rows": len(rh),
               "proof_consumption_warning": "Declared graph edges are not proof-value consumption. Consult the separately compiled exact audits for the selected baseline and newly proved consumers.",
               "source_claim_warning": "This is not a checked source-claim universe. The separate17-row source catalog is a declared detailed subset, with pending source audits left pending; missing exact claims there do not establish global family absence.",
               "csv_sha256": hashlib.sha256(output.read_bytes()).hexdigest()}
    (S / "estimates/CANONICAL_CONCLUSION_CENSUS.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps({k: summary[k] for k in ("node_versions", "conclusions", "declared_graph_reaches_RH_rows", "status")}))


if __name__ == "__main__":
    main()
