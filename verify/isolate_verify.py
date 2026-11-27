#!/usr/bin/env python3
"""Verify a local root bracket and monotonicity for the SHA-pinned BCK witness.

Only the Python standard library and exact integer arithmetic are used.
The full-ray positivity certificate is a separate proof obligation.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from math import factorial, gcd
from pathlib import Path

WITNESS_SHA256 = "ae71adf610b66f2742021b8abcb7fb0156d79936db44b727eee18fe4891213a8"
DOMAIN = ("1.906880", "1.906888")
BRACKET = (
    "1.9068842799708925802167577406",
    "1.9068842799708925802167577407",
)
DEGREE = 16_384
PREFIX = 640
PRECISION_BITS = 1536
SCALE = 1 << PRECISION_BITS
TAIL_BITS = 400
TAIL = 1 << (PRECISION_BITS - TAIL_BITS)


def ceil_div(numerator: int, denominator: int) -> int:
    return -((-numerator) // denominator)


def checked_input(path: Path) -> list[Fraction]:
    raw = path.read_bytes()
    if sha256(raw).hexdigest() != WITNESS_SHA256:
        raise ValueError("witness SHA-256 mismatch")
    data = json.loads(raw)
    if (data["schema"] != "even-laguerre-alpha-minus-half-v1"
            or Fraction(data["t"]) != Fraction(DOMAIN[1])
            or len(data["coefficients"]) != DEGREE // 2 + 1):
        raise ValueError("unexpected witness convention")
    return [Fraction(coefficient) for coefficient in data["coefficients"]]


def weights(modes: list[Fraction]) -> list[int]:
    common = 1
    for mode in modes:
        denominator = mode.denominator
        common = (common // gcd(common, denominator)) * denominator
    return [mode.numerator * (common // mode.denominator) for mode in modes]


def exact_point(integer_weights: list[int], t: Fraction) -> dict:
    """Sign by the complete integer recurrence, without truncation.

    At degree n the basis value is scaled by (2q)^n n!, where t=p/q.
    The accumulator carries the same positive scale and the weight denominator.
    """
    p, q = t.numerator, t.denominator
    previous, current = 0, 1
    total = integer_weights[0]
    q_squared = q * q
    for n in range(DEGREE):
        previous, current = (
            current,
            ((4*n + 1)*q - 2*p)*current - 2*n*(2*n - 1)*q_squared*previous,
        )
        total *= 2*q*(n + 1)
        if n & 1:
            total += integer_weights[(n + 1) // 2] * current
    return {
        "t_rational": str(t),
        "sign": (total > 0) - (total < 0),
        "scaled_numerator_magnitude_bits": total.bit_length(),
    }


def verify_tail(modes: list[Fraction]) -> int:
    """Bound the dropped terms of P and P' by 2^-TAIL_BITS on [0,2]."""
    # For L_n^(-1/2), |[t^j] L_n| = binom(n-1/2,n-j)/j!
    # <= binom(n,j)/j! <= DEGREE^j/(j!)^2.
    mass = sum(map(abs, modes)).__ceil__()
    j = PREFIX + 1
    # Successive derivative majorants have ratio 2*DEGREE/(j*(j+1));
    # the ratio for P is smaller. Both are below one half.
    first = mass * (2 * DEGREE)**j
    denominator = factorial(j)**2
    if not (4 * DEGREE < j * (j + 1)
            and first << (TAIL_BITS + 1) < denominator
            and (j * first) << TAIL_BITS < denominator):
        raise ArithmeticError("failed to enclose the discarded power terms")
    return mass


def power_prefix(modes: list[Fraction]) -> tuple[list[int], list[int]]:
    """Return directed integer bounds for 2^PRECISION_BITS times each coefficient."""
    lower, upper = [0] * (PREFIX + 1), [0] * (PREFIX + 1)
    central_lo = central_hi = SCALE
    denominators = [(j + 1) * (2*j + 1) for j in range(PREFIX)]
    for n in range(DEGREE + 1):
        if not n & 1:
            mode = modes[n // 2]
            p, q = abs(mode.numerator), mode.denominator
            lo = central_lo * p // q
            hi = ceil_div(central_hi * p, q)
            stop = min(PREFIX, n)
            sign = -1 if mode < 0 else 1
            for j in range(stop + 1):
                if sign < 0:
                    lower[j] -= hi
                    upper[j] -= lo
                else:
                    lower[j] += lo
                    upper[j] += hi
                if j < stop:
                    # Consecutive magnitudes of coefficients of L_n^(-1/2).
                    factor = 2 * (n - j)
                    denominator = denominators[j]
                    lo = lo * factor // denominator
                    hi = ceil_div(hi * factor, denominator)
        # L_n^(-1/2)(0) = 4^-n binom(2n,n).
        central_lo = central_lo * (2*n + 1) // (2*n + 2)
        central_hi = ceil_div(central_hi * (2*n + 1), 2*n + 2)
    for j in range(1, PREFIX + 1, 2):
        lower[j], upper[j] = -upper[j], -lower[j]
    return lower, upper


def translate(lower: list[int], upper: list[int], a: Fraction, width: Fraction):
    """Directed coefficient bounds after the affine substitution t=a+width*z."""
    ap, aq = a.numerator, a.denominator
    hp, hq = width.numerator, width.denominator
    out_lo, out_hi = [], []
    for j in range(len(lower) - 1, -1, -1):
        lo, hi = [0] * (len(out_lo) + 1), [0] * (len(out_hi) + 1)
        for i, (x, y) in enumerate(zip(out_lo, out_hi)):
            lo[i] += x * ap // aq
            lo[i + 1] += x * hp // hq
            hi[i] += ceil_div(y * ap, aq)
            hi[i + 1] += ceil_div(y * hp, hq)
        lo[0] += lower[j]
        hi[0] += upper[j]
        out_lo, out_hi = lo, hi
    return out_lo, out_hi


def derivative_enclosure(modes: list[Fraction], left: Fraction, right: Fraction):
    lower, upper = power_prefix(modes)
    d_lo = [j * lower[j] for j in range(1, PREFIX + 1)]
    d_hi = [j * upper[j] for j in range(1, PREFIX + 1)]
    lo, hi = translate(d_lo, d_hi, left, right - left)
    # For z in [0,1], each nonconstant monomial lies between zero and one.
    return (lo[0] + sum(min(0, value) for value in lo[1:]) - TAIL,
            hi[0] + sum(max(0, value) for value in hi[1:]) + TAIL)


def decimal_outward(lo: int, hi: int, places: int) -> list[str]:
    scale = 10**places

    def display(value: int) -> str:
        whole, part = divmod(abs(value), scale)
        sign = "-" if value < 0 else ""
        return f"{sign}{whole}.{part:0{places}d}"

    return [display(lo * scale // SCALE), display(ceil_div(hi * scale, SCALE))]


def verify(path: Path) -> dict:
    modes = checked_input(path)
    left, right = map(Fraction, DOMAIN)
    a, b = map(Fraction, BRACKET)
    if not 0 < left < a < b < right < 2:
        raise ValueError("endpoint order or derivative domain")
    mass = verify_tail(modes)
    integer_weights = weights(modes)
    point_checks = [exact_point(integer_weights, t) for t in (a, b)]
    if [check["sign"] for check in point_checks] != [-1, 1]:
        raise ArithmeticError("endpoint signs do not isolate a root")
    lo, hi = derivative_enclosure(modes, left, right)
    if not 0 < lo <= hi:
        raise ArithmeticError("derivative enclosure does not prove positivity")
    return {
        "status": "verified",
        "witness_sha256": WITNESS_SHA256,
        "polynomial_degree": DEGREE,
        "root_bracket_decimal": list(BRACKET),
        "root_bracket_width": str(b - a),
        "endpoint_exact_integer_evaluations": point_checks,
        "derivative_domain": list(DOMAIN),
        "derivative_enclosure_decimal_outward": decimal_outward(lo, hi, 55),
        "derivative_enclosure_rational": [
            str(Fraction(lo, SCALE)), str(Fraction(hi, SCALE))
        ],
        "fixed_point_bits": PRECISION_BITS,
        "power_prefix_degree": PREFIX,
        "coefficient_absolute_sum_upper_integer": mass,
        "power_and_derivative_tail_upper": str(Fraction(1, 1 << TAIL_BITS)),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("witness", type=Path, help="original BCK-degree-16384.json")
    args = parser.parse_args()
    print(json.dumps(verify(args.witness), indent=2))


if __name__ == "__main__":
    main()
