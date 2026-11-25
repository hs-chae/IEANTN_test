#!/usr/bin/env python3
"""Recreate the small rational dual input; search is not its soundness proof.

Pinned search: NumPy 2.4.6, SciPy 1.17.0 (HiGHS defaults), no stochastic search.
The exact rational witness is checked independently after this LP/rationalization.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path

import numpy as np
import scipy
from scipy.optimize import linprog


def need(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    p = argparse.ArgumentParser(allow_abbrev=False)
    p.add_argument("--output", type=Path, required=True)
    p.add_argument("--expected", type=Path)
    a = p.parse_args()
    need(not a.output.exists(), "Fresh output required")
    need(np.__version__ == "2.4.6" and scipy.__version__ == "1.17.0",
         "Pinned numerical-search dependency versions required")
    penalty, mesh, support, panels, scale = Fraction(36, 11), 4, 5, 2400, 256
    u = np.linspace(0, mesh / 2, panels + 1)
    centers = (np.arange(mesh, mesh * support) + 0.5) / mesh
    basis = (2 / mesh) * np.sinc(u / mesh)[:, None] * np.cos(2 * np.pi * u[:, None] * centers)
    fixed = 2 * np.sinc(2 * u)
    minus_one = -np.ones(len(u))
    upper = np.vstack([np.column_stack([basis, minus_one]),
                       np.column_stack([-basis, minus_one])])
    result = linprog(np.r_[np.zeros(len(centers)), 1], A_ub=upper,
                     b_ub=np.r_[-fixed, fixed],
                     bounds=[(float(1 - penalty), 1)] * len(centers) + [(0, None)],
                     method="highs")
    need(result.success, "Exploratory LP failed")
    first_round = [min(Fraction(1), max(1-penalty, Fraction(round(10**10 * value), 10**10)))
                   for value in result.x[:-1]]
    lower = math.ceil((1-penalty)*scale)
    heights = [scale]*mesh + [max(lower, min(scale, round(value*scale))) for value in first_round]
    exact = dict(A=str(penalty), m=mesh, support=support, height_scale=scale,
                 positive_heights=heights, target_global_bound="123/100")
    if a.expected:
        expected = json.loads(a.expected.read_text())
        need(all(expected[key] == value for key, value in exact.items()),
             "Recreated witness differs; do not replace the fixed experimental input")
    a.output.parent.mkdir(parents=True, exist_ok=True)
    a.output.write_text(json.dumps(exact, indent=2) + "\n")
    print(json.dumps(dict(status="RECREATED_EXACT_FIXED_RATIONAL_INPUT_NOT_A_PROOF",
                         coefficients=heights, exploratory_sample_max=float(result.fun),
                         output_sha256=hashlib.sha256(a.output.read_bytes()).hexdigest(),
                         numpy=np.__version__, scipy=scipy.__version__)))


if __name__ == "__main__":
    main()
