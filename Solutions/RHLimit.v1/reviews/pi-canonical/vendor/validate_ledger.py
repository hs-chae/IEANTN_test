#!/usr/bin/env python3
"""Fail-closed structural validator for a Lean source/math audit delta."""

from __future__ import annotations

import argparse
import csv
from collections import Counter
from pathlib import Path


ID = ("file", "decl_line", "lean_name")
FIELDS = ID + (
    "kind", "proposed_verification_status", "actual_lean_declaration",
    "actual_primary_source_statement_or_explicit_absence", "original_locator",
    "domain_and_hypotheses", "lean_source_comparison", "mathematical_check",
    "full_scope_attribution_evidence", "trust_boundary", "notes",
)
FINAL = {"external_verified", "internal_verified"}
PENDING = {"pending_primary_source_locator", "pending_full_provenance_census"}


def read(path: Path) -> list[dict[str, str]]:
    with path.open(encoding="utf-8", newline="") as handle:
        reader = csv.DictReader(handle)
        found = set(reader.fieldnames or [])
        missing = set(ID) - found
        if missing:
            raise SystemExit(f"{path}: missing identity columns {sorted(missing)}")
        return list(reader)


def key(row: dict[str, str]) -> tuple[str, str, str]:
    return tuple(row[name].strip() for name in ID)  # type: ignore[return-value]


def require(row: dict[str, str], field: str) -> None:
    if not row.get(field, "").strip():
        raise SystemExit(f"{key(row)}: missing {field}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scope", required=True, type=Path)
    parser.add_argument("--ledger", required=True, type=Path)
    parser.add_argument("--require-final", action="store_true")
    args = parser.parse_args()
    scope, ledger = read(args.scope), read(args.ledger)
    scope_keys, ledger_keys = {key(r) for r in scope}, {key(r) for r in ledger}
    if len(scope_keys) != len(scope):
        raise SystemExit("Scope has duplicate written-source identities")
    if len(ledger_keys) != len(ledger):
        raise SystemExit("Ledger has duplicate written-source identities")
    if scope_keys != ledger_keys:
        raise SystemExit(f"Coverage mismatch: missing={len(scope_keys-ledger_keys)} extra={len(ledger_keys-scope_keys)}")
    for row in ledger:
        for field in FIELDS:
            require(row, field)
        status = row["proposed_verification_status"].strip()
        if status not in FINAL | PENDING:
            raise SystemExit(f"{key(row)}: invalid status {status!r}")
        if args.require_final and status not in FINAL:
            raise SystemExit(f"{key(row)}: non-final status {status}")
    print({"rows": len(ledger), "statuses": dict(Counter(r["proposed_verification_status"] for r in ledger))})


if __name__ == "__main__":
    main()
