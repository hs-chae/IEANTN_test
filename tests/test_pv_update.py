"""The update workflow never writes a new provider over the old one.

Found by the independent reader (2026-11-05): an update entry that named only its changed
parameters inherited `project`, `source`, `lean_lib` and `lean_module` from `updated_from`, so
`pv_update.py generate` would have overwritten the old provider's selected C file, Lean module and
lakefile.
"""
from __future__ import annotations

import importlib.util
import json
import pathlib
import tempfile
import unittest
from unittest import mock

ROOT = pathlib.Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location(
    "pv_update", ROOT / "scripts" / "native_assisted" / "pv_update.py")
PV = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(PV)

BASE = {"family": "ramanujan-budget", "parameters": {"m": "119", "M": "131", "A": "3914", "Y": "3915"},
        "bound": "9101/1000", "project": "Solutions/Old", "source": "Solutions/Old/c/old.c",
        "lean_lib": "OldLib", "lean_module": "OldLib/Updated.lean", "gate_endpoint": "Old.v2.x",
        "note": "existing provider; the generator is not run on it"}
OWN = {"project": "Solutions/New", "source": "Solutions/New/c/budget.c", "lean_lib": "NewLib",
       "lean_module": "NewLib/Provider.lean", "gate_endpoint": "New.v3.x"}


class TestUpdateEntries(unittest.TestCase):
    def registry(self, update: dict) -> pathlib.Path:
        tmp = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False)
        json.dump({"providers": {"Old.v2.x": BASE, "New.v3.x": update}}, tmp)
        tmp.close()
        self.addCleanup(pathlib.Path(tmp.name).unlink)
        return pathlib.Path(tmp.name)

    def entry(self, update: dict) -> dict:
        with mock.patch.object(PV, "REGISTRY", self.registry(update)):
            return PV.entry("New.v3.x")

    def test_an_update_without_its_own_locations_is_refused(self):
        with self.assertRaises(SystemExit) as caught:
            self.entry({"updated_from": "Old.v2.x", "parameters": {"A": "400", "Y": "401"},
                        "bound": "9988/1000"})
        self.assertIn("would overwrite", str(caught.exception))

    def test_an_update_pointing_at_the_old_files_is_refused(self):
        same = {**OWN, "project": BASE["project"], "source": BASE["source"]}
        with self.assertRaises(SystemExit):
            self.entry({"updated_from": "Old.v2.x", "parameters": {"A": "400"}, **same})

    def test_a_complete_update_keeps_its_own_locations_and_drops_the_old_note(self):
        e = self.entry({"updated_from": "Old.v2.x", "parameters": {"A": "400", "Y": "401"},
                        "bound": "9988/1000", **OWN})
        for k, v in OWN.items():
            self.assertEqual(e[k], v)
        self.assertEqual(e["parameters"], {"m": "119", "M": "131", "A": "400", "Y": "401"})
        self.assertNotIn("note", e)


if __name__ == "__main__":
    unittest.main()
