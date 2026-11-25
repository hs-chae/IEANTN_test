#!/usr/bin/env python3
"""Use the unchanged assigned-runtime adapter with this new protocol directory."""
import hashlib
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent
PARENT = HERE.parent / "native_trial.py"
EXPECTED = "5e1c693289b1e540734f1aeab3c75655d70f6442e6f8a9928586487655812ccb"


def main():
    if hashlib.sha256(PARENT.read_bytes()).hexdigest() != EXPECTED:
        raise ValueError("Pinned primary adapter changed")
    spec = importlib.util.spec_from_file_location("rh080_followup_pinned_adapter", PARENT)
    core = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(core)
    core.HERE = HERE
    core.__file__ = str(Path(__file__).resolve())
    core.main()


if __name__ == "__main__":
    main()
