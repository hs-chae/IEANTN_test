#!/bin/bash
set -eu
case "$0" in */*) cd -- "${0%/*}";; esac
exec /usr/bin/python3.10 -Bu d02_check.py constants centered mertens compact tails extra early_compact strip smoothcheck q2check onsets basic_mid
