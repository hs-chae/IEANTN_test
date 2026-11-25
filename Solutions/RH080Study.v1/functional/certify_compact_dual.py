#!/usr/bin/env python3
"""Independent direct-sine ball check of a small rational CMS dual witness.

External rigorous interval execution, not Lean kernel checking or source-first PV.
All acceptance checks remain active under Python optimization.
"""
import argparse
from fractions import Fraction
import hashlib
import json
import math
import os
from pathlib import Path
import tempfile
import time

from flint import arb, ctx, fmpq


def need(condition, message):
    if not condition:
        raise ValueError(message)


def ball(q):
    q = Fraction(q)
    return arb(fmpq(q.numerator, q.denominator))


def pairs(items):
    result = {}
    for key, value in items:
        need(key not in result, "Duplicate JSON key")
        result[key] = value
    return result


def finite(value):
    result = float(value)
    need(math.isfinite(result), "Nonfinite JSON value")
    return result


def reject_constant(value):
    raise ValueError("Nonfinite JSON constant: " + value)


def publish(path, receipt):
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix=".dual-", suffix=".tmp", dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(fd, "w") as stream:
            stream.write(json.dumps(receipt, indent=2, allow_nan=False) + "\n")
        os.link(temporary, path)
    finally:
        temporary.unlink()


def main():
    ap = argparse.ArgumentParser(allow_abbrev=False)
    ap.add_argument("--witness", type=Path, required=True)
    ap.add_argument("--panels", type=int, default=256)
    ap.add_argument("--bits", type=int, default=128)
    ap.add_argument("--output", type=Path, required=True)
    args = ap.parse_args()
    need(not args.output.exists(), "Fresh output required")
    need(args.bits >= 96 and args.panels >= 1, "Insufficient precision or grid")
    ctx.prec = args.bits
    data = json.loads(args.witness.read_text(), object_pairs_hook=pairs,
                      parse_float=finite, parse_constant=reject_constant)
    m, support, scale = data["m"], data["support"], data["height_scale"]
    need(type(m) is int and m > 0 and type(support) is int and support > 1,
         "Invalid step partition")
    need(type(scale) is int and scale > 0, "Invalid rational scale")
    raw = data["positive_heights"]
    need(all(type(x) is int for x in raw) and len(raw) == m * support,
         "Incomplete exact height data")
    heights = [Fraction(x, scale) for x in raw]
    penalty = Fraction(data["A"])
    need(penalty >= 1 and heights[:m] == [Fraction(1)] * m,
         "Central steps must equal one")
    need(all(1 - penalty <= h <= 1 for h in heights[m:]),
         "An exterior step violates dual feasibility")
    jumps = [a - b for a, b in zip(heights, heights[1:] + [Fraction(0)])]
    started = time.monotonic()
    # At u_k=m*k/(2G), numerator=sum_j jump_j sin(pi*j*k/G).
    # Every sample is computed directly, independently of the source DFT verifier.
    samples = [abs(ball(2 * sum(heights) / m))]
    for k in range(1, args.panels + 1):
        numerator = arb(0)
        for j, jump in enumerate(jumps, 1):
            numerator += ball(jump) * (arb.pi() * ball(Fraction(j * k, args.panels))).sin()
        u = Fraction(m * k, 2 * args.panels)
        samples.append(abs(numerator / (arb.pi() * ball(u))))
    sampled = arb(0)
    for value in samples:
        sampled = sampled.max(value.abs_upper())
    moment = sum(abs(h) * ((j + 1) ** 3 - j ** 3)
                 for j, h in enumerate(heights)) / (3 * m ** 3)
    step = Fraction(m, 2 * args.panels)
    remainder = arb.pi() ** 2 * ball(moment * step ** 2)
    total = sampled + remainder
    target = Fraction(data["target_global_bound"])
    need(target > 0 and total < ball(target), "Global supremum target not established")
    need(target < Fraction(5, 4), "Target does not exclude coefficient four-fifths")
    receipt = dict(
        status="PASS_EXTERNAL_DIRECT_ARB_ALL_GRID_POINTS_AND_ANALYTIC_INTERPOLATION",
        evidence_tier="External ball computation with written continuum proof; not Lean D or PV C",
        witness_sha256=hashlib.sha256(args.witness.read_bytes()).hexdigest(),
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        penalty=str(penalty), mesh=m, support=support, scale=scale,
        panels=args.panels, sample_count=len(samples), bits=args.bits,
        exact_second_moment=str(moment), exact_step=str(step),
        sampled_supremum_upper=str(sampled.abs_upper()),
        interpolation_upper=str(remainder.abs_upper()),
        global_supremum_upper=str(total.abs_upper()),
        accepted_rational_supremum=str(target),
        resulting_framework_quotient_floor=str(1 / target),
        floor_strictly_exceeds_four_fifths=1 / target > Fraction(4, 5),
        jumps=[str(j) for j in jumps], seconds=time.monotonic() - started,
        analytic_scope="Even compact step function V, V=1 on(-1,1),1-A<=V<=1 exterior; inverse Fourier transform folds to[0,m/2]; derivative/chord interpolation includes every real point and periodic tail. Weak duality uses the source general Fejer/Fubini argument, separately from this numerical execution.")
    publish(args.output, receipt)
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()
