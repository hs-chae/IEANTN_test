"""The node page says where a walkthrough is, whether an unjustified claim has a local proof, and
where a fork's files are.

Three reader complaints from the QRH integration audit (P1, P5, P7 in
`docs/program-verification/` history): the page never linked a node README; "unjustified" read as
"no proof" even where a complete local proof exists; and every Solution link on a fork pointed at
upstream `main`, which does not contain the fork's solutions.
"""
from __future__ import annotations

import contextlib
import io
import os
import pathlib
import sys
import unittest
from unittest import mock

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from test_ieantn import LITERATURE, FixtureRepo, ieantn  # noqa: E402

UNJUSTIFIED = LITERATURE.replace("kind: literature", "kind: none-yet")
PROGRESS = "  progress:\n    solution: Solutions/A.v1/\n    state: in-progress\n    remaining_holes: {holes}\n"


class PageRepo(FixtureRepo):
    def node(self, conclusions: str = LITERATURE, *, status: str = "active") -> pathlib.Path:
        return self.write_node("A.v1", conclusions, status=status)

    def solution(self) -> None:
        (self.root / "Solutions" / "A.v1").mkdir(parents=True, exist_ok=True)
        (self.root / "Solutions" / "A.v1" / "Solution.lean").write_text("", encoding="utf-8")

    def page(self) -> str:
        ieantn.pages(False)
        return (self.root / "docs" / "nodes" / "A-v1.md").read_text(encoding="utf-8")


class TestReadmeLink(PageRepo):
    def test_a_node_readme_is_linked(self) -> None:
        directory = self.node()
        (directory / "README.md").write_text("# Walkthrough\n", encoding="utf-8")
        self.assertIn("| Walkthrough | [`README.md`](../../IEANTN/Nodes/A/v1/README.md) |",
                      self.page())

    def test_no_row_without_a_readme(self) -> None:
        self.node()
        self.assertNotIn("| Walkthrough |", self.page())


class TestLocalProof(PageRepo):
    def test_complete_local_proof_is_named(self) -> None:
        self.node(UNJUSTIFIED + PROGRESS.format(holes=0))
        self.solution()
        page = self.page()
        self.assertIn("| Evidence | unjustified (`none-yet`) |", page)
        self.assertIn("| Local proof | complete in [`Solutions/A.v1`](../../Solutions/A.v1), "
                      "0 remaining holes;", page)

    def test_holes_mean_no_row(self) -> None:
        self.node(UNJUSTIFIED + PROGRESS.format(holes=2))
        self.solution()
        self.assertNotIn("| Local proof |", self.page())

    def test_a_recorded_zero_without_a_solution_file_means_no_row(self) -> None:
        """The marker alone is a claim about files; the file has to be there."""
        self.node(UNJUSTIFIED + PROGRESS.format(holes=0))
        self.assertNotIn("| Local proof |", self.page())

    def test_only_unjustified_conclusions_get_the_row(self) -> None:
        self.node(LITERATURE + PROGRESS.format(holes=0))
        self.solution()
        self.assertNotIn("| Local proof |", self.page())

    def test_a_path_outside_solutions_is_not_linked(self) -> None:
        self.node(UNJUSTIFIED + PROGRESS.format(holes=0).replace("Solutions/A.v1/", "../etc/"))
        self.solution()
        self.assertNotIn("| Local proof |", self.page())


class TestStatusWarning(PageRepo):
    def _graph(self) -> tuple[bool, str]:
        printed = io.StringIO()
        with contextlib.redirect_stdout(printed):
            passed = ieantn.check_graph()
        return passed, printed.getvalue()

    def test_awaiting_solution_with_every_proof_complete_warns(self) -> None:
        self.node(UNJUSTIFIED + PROGRESS.format(holes=0), status="awaiting-solution")
        self.solution()
        passed, printed = self._graph()
        self.assertTrue(passed, "a status that lags the files is a warning, not an error")
        self.assertIn("awaiting-verification", printed)

    def test_no_warning_while_holes_remain(self) -> None:
        self.node(UNJUSTIFIED + PROGRESS.format(holes=1), status="awaiting-solution")
        self.solution()
        self.assertNotIn("awaiting-verification", self._graph()[1])


class TestRepositoryLinks(PageRepo):
    def test_upstream_main_by_default(self) -> None:
        self.node()
        self.solution()
        self.assertIn("(https://github.com/teorth/IEANTN/tree/main/Solutions/A.v1)", self.page())

    def test_a_fork_points_at_its_own_branch(self) -> None:
        self.node()
        self.solution()
        with mock.patch.object(ieantn, "REPOSITORY_URL", "https://github.com/hs-chae/IEANTN_test"), \
                mock.patch.object(ieantn, "REPOSITORY_BRANCH", "qrh-2pv"):
            page = self.page()
        self.assertIn("(https://github.com/hs-chae/IEANTN_test/tree/qrh-2pv/Solutions/A.v1)", page)

    def test_settings_come_from_the_environment(self) -> None:
        with mock.patch.dict(os.environ, {"X_URL": "https://github.com/hs-chae/IEANTN_test/"}):
            self.assertEqual(ieantn._repository_setting("X_URL", "d", r"https://[A-Za-z0-9._~/-]+"),
                             "https://github.com/hs-chae/IEANTN_test")
        with mock.patch.dict(os.environ, {}, clear=True):
            self.assertEqual(ieantn._repository_setting("X_URL", "d", r"x"), "d")

    def test_a_value_that_is_not_a_plain_url_is_refused(self) -> None:
        with mock.patch.dict(os.environ, {"X_URL": "https://x.org/a) [b](c"}):
            with self.assertRaises(SystemExit):
                ieantn._repository_setting("X_URL", "d", r"https://[A-Za-z0-9._~/-]+")


if __name__ == "__main__":
    unittest.main()
