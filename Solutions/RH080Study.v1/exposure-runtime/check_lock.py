#!/usr/bin/env python3
"""Additive clean-root metadata adapter for the unchanged historical trial gate.

This command ALWAYS selects the original --check-only route. It cannot start a
worker/model, fabricate a fixture acceptance, or edit/reapprove historical locks.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys


def need(ok,message):
    if not ok:raise ValueError(message)


def main():
    ap=argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument('--repository',type=Path,default=Path(__file__).resolve().parents[3])
    ap.add_argument('--data-root',type=Path,required=True)
    ap.add_argument('--lock',type=Path,required=True)
    ap.add_argument('--fixture',action='store_true')
    a=ap.parse_args();R=a.repository.resolve(strict=True);data=a.data_root.resolve(strict=True);lock=a.lock.resolve(strict=True)
    need(lock.is_relative_to(data),'Lock must be under explicit clean data root')
    need(not data.is_relative_to(R),'Replay data must be outside publishable source')
    here=R/'Solutions/RH080Study.v1/exposure-runtime';pin=json.loads((here/'ADAPTER_PIN.json').read_text())
    original=R/pin['adapter_path'];need(hashlib.sha256(original.read_bytes()).hexdigest()==pin['adapter_sha256'],'Frozen trial adapter changed')
    backend=here/'layout/ieantn-deep-tertiary-exposure-a-20261117/scripts/native_controller_v2.py'
    need(hashlib.sha256(backend.read_bytes()).hexdigest()==pin['backend_sha256'],'Reviewed backend source changed')
    spec=importlib.util.spec_from_file_location('rh080_unchanged_trial_metadata',original)
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    module.DATA=data;module.BACKEND=backend
    # Root bindings are explicit transport arguments. All original protocol,
    # pin, assigned-mount, successful-fixture, premise and fresh-output checks
    # remain inside the unchanged original gate. No acceptance is synthesized.
    sys.argv=[str(original),'--lock',str(lock),'--check-only']+(['--fixture'] if a.fixture else [])
    module.main()


if __name__=='__main__':main()
