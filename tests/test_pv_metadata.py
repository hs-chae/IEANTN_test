"""Program-verification metadata: optional, fail-closed, and invisible to nodes that do not use it.

Covers `check_pv_evidence`, the optional `verification_method` on a justification, and the opt-in
node-page rows. Uses the same fixture repository as tests/test_ieantn.py.
"""
from __future__ import annotations

import json
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from test_ieantn import FixtureRepo, ieantn  # noqa: E402

NONCOMPLIANT = (
    "  - id: main\n"
    "    declaration: {node}.main\n"
    "    challenge: {node}.challenge_main\n"
    "    imports: []\n"
    "    justifications:\n"
    "      - id: src\n"
    "        kind: lean-noncompliant\n"
    "        note: six finite native facts\n"
    "{extra}"
    "    designated: src\n"
)


def attestation(key: str, **over) -> dict:
    data = {"notice": "LOCAL RESEARCH ATTESTATION (native-assisted gate). Not an IEANTN "
                      "verification receipt.",
            "gate": "native-assisted", "status": "passed", "conclusion": key,
            "evidence_method": "lean-verified-program",
            "axioms": {"native_fact_count": 6, "rejected": []},
            "official": {"designated_kind": "lean-noncompliant",
                         "official_comparator_receipt": "absent"},
            "run": {"checked_at_utc": "2026-11-04T10:00:00+00:00"}}
    data.update(over)
    return data


class PVRepo(FixtureRepo):
    def node(self, extra: str = "") -> None:
        directory = self.write_node("A.v1", NONCOMPLIANT.replace("{extra}", extra))
        (self.root / "Solutions" / "A.v1").mkdir(parents=True, exist_ok=True)
        (self.root / "Solutions" / "A.v1" / "Solution.lean").write_text("", encoding="utf-8")
        (directory / "Conclusions.lean").write_text("def main : Prop := True\n", encoding="utf-8")

    def attest(self, **over) -> pathlib.Path:
        d = self.root / "pv-evidence"
        d.mkdir(exist_ok=True)
        p = d / "A.v1.main.native-assisted.local.json"
        p.write_text(json.dumps(attestation("A.v1.main", **over)), encoding="utf-8")
        return p

    def page(self) -> str:
        ieantn.pages(False)
        return (self.root / "docs" / "nodes" / "A-v1.md").read_text(encoding="utf-8")


class TestPages(PVRepo):
    def test_page_unchanged_without_attestation(self):
        self.node()
        page = self.page()
        self.assertNotIn("Evidence method", page)
        self.assertNotIn("native-assisted", page)

    def test_page_shows_the_four_labels_with_attestation(self):
        self.node()
        self.attest()
        page = self.page()
        self.assertIn("| Evidence method | lean-verified-program |", page)
        self.assertIn("native-assisted: **passed**", page)
        self.assertIn("not a receipt", page)
        self.assertIn("| Official IEANTN classification | `lean-noncompliant`", page)
        self.assertIn("| Official Comparator receipt | absent |", page)

    def test_page_never_says_verified_for_a_noncompliant_node(self):
        self.node()
        self.attest()
        self.assertNotIn("Verified (`lean-comparator`)", self.page())


class TestReaderRows(PVRepo):
    """The program/backend, trust, second-route and change rows (all opt-in, all from files)."""

    def sources(self):
        return {"S_source_identity": {"ok": True, "sources": [
                    {"path": "Solutions/A.v1/c/p.c", "sha256": "ab" * 32}]},
                "C_generic_correctness": {"ok": True, "theorems": ["PVCore.certified"]}}

    def test_program_and_trust_rows(self):
        self.node()
        self.attest(method_checks=self.sources())
        page = self.page()
        self.assertIn("| Program and backend | restricted C, IEEE binary64", page)
        self.assertIn("`Solutions/A.v1/c/p.c` (SHA256 `abababababab`)", page)
        self.assertIn("| Proved by | `PVCore.certified`", page)
        self.assertIn("except 6 finite computation(s)", page)
        self.assertIn("Not modelled: the C compiler", page)

    def test_consumer_without_sources_has_no_program_row(self):
        self.node()
        self.attest(axioms={"native_fact_count": 0, "rejected": []})
        page = self.page()
        self.assertNotIn("Program and backend", page)
        self.assertIn("The Lean kernel checks every step.", page)

    def test_second_route_row(self):
        self.node()
        self.attest()
        d = self.root / "pv-evidence"
        (d / "@pv.Other.main.native-assisted.local.json").write_text(json.dumps(
            attestation("@pv.Other.main", endpoint="Other.main", replays="A.v1.main",
                        axioms={"native_fact_count": 1, "rejected": []})), encoding="utf-8")
        page = self.page()
        self.assertIn("| Second checked route | `Other.main`: native-assisted **passed**, 1", page)

    def test_change_row_from_registry(self):
        self.node()
        self.attest()
        reg = self.root / "scripts" / "native_assisted"
        reg.mkdir(parents=True, exist_ok=True)
        (reg / "providers.json").write_text(json.dumps({"providers": {"A.v1.main": {
            "updated_from": "A.v0.main", "change": "range moved"}}}), encoding="utf-8")
        page = self.page()
        self.assertIn("| Changed from [`A.v0.main`]", page)
        self.assertIn("| range moved |", page)


class TestEvidenceCheck(PVRepo):
    def test_valid_attestation_passes(self):
        self.node()
        self.attest()
        self.assertTrue(ieantn.check_pv_evidence())

    def test_missing_notice_fails(self):
        self.node()
        self.attest(notice="all good")
        self.assertFalse(ieantn.check_pv_evidence())

    def test_claimed_receipt_without_receipt_fails(self):
        self.node()
        self.attest(official={"designated_kind": "lean-noncompliant",
                              "official_comparator_receipt": "present"})
        self.assertFalse(ieantn.check_pv_evidence())

    def test_kind_disagreement_fails(self):
        self.node()
        self.attest(official={"designated_kind": "lean-comparator",
                              "official_comparator_receipt": "absent"})
        self.assertFalse(ieantn.check_pv_evidence())

    def test_passed_with_rejected_axiom_fails(self):
        self.node()
        self.attest(axioms={"native_fact_count": 0, "rejected": [{"name": "sorryAx"}]})
        self.assertFalse(ieantn.check_pv_evidence())

    def test_unknown_status_fails(self):
        self.node()
        self.attest(status="officially-verified")
        self.assertFalse(ieantn.check_pv_evidence())

    def test_unknown_conclusion_fails(self):
        self.node()
        d = self.root / "pv-evidence"
        d.mkdir(exist_ok=True)
        (d / "B.v1.main.native-assisted.local.json").write_text(
            json.dumps(attestation("B.v1.main")), encoding="utf-8")
        self.assertFalse(ieantn.check_pv_evidence())

    def test_no_directory_is_fine(self):
        self.node()
        self.assertTrue(ieantn.check_pv_evidence())


class TestVerificationMethodField(PVRepo):
    def test_method_with_matching_attestation_passes_graph_check(self):
        self.node("        verification_method: lean-verified-program\n")
        self.attest()
        self.generate()
        self.assertTrue(ieantn.check_graph())

    def test_method_without_attestation_fails(self):
        self.node("        verification_method: lean-verified-program\n")
        self.generate()
        self.assertFalse(ieantn.check_graph())

    def test_unknown_method_fails(self):
        self.node("        verification_method: lean-verified-numerical\n")
        self.attest()
        self.generate()
        self.assertFalse(ieantn.check_graph())

    def test_method_disagreeing_with_attestation_fails(self):
        self.node("        verification_method: lean-verified-program\n")
        self.attest(evidence_method="not-program-verified")
        self.generate()
        self.assertFalse(ieantn.check_graph())

    def test_nodes_without_the_field_are_unaffected(self):
        self.node()
        self.generate()
        self.assertTrue(ieantn.check_graph())


if __name__ == "__main__":
    unittest.main()
