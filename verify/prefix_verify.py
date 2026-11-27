"""Solver-free Arb Bernstein certificate for the short interval."""
from math import comb, factorial

from flint import arb, arb_poly, ctx

from audit_verify import rational

# Adapted from the BCK Arb prefix verifier.
# Original source SHA-256: 613360822331622a26ffb23c98d9b42211bb1c8a59ee9b75bab41bf2e1791099


def truncated_power(modes, limit):
    """Sum explicitly signed Laguerre coefficient magnitudes in ball arithmetic."""
    degree = 2 * (len(modes) - 1)
    positive = [arb(0) for _ in range(limit + 1)]
    inverse = [arb(2) / ((j + 1) * (2 * j + 1)) for j in range(limit)]
    value_at_zero = arb(1)
    for n in range(degree + 1):
        if n % 2 == 0:
            term = modes[n // 2] * value_at_zero
            upper = min(n, limit)
            for j in range(upper):
                positive[j] += term
                term *= (n - j) * inverse[j]
            positive[upper] += term
        value_at_zero *= arb(2 * n + 1) / (2 * (n + 1))
    return [(-1)**j * x for j, x in enumerate(positive)]


def binomial_transform(coefficients, factors, kernel):
    weighted = arb_poly([a*b for a, b in zip(coefficients, factors)])
    product = weighted * kernel
    return [product[j] / (factors[j] * factors[0]) for j in range(len(coefficients))]


def algorithm(candidate, right, limit, precision, max_depth, log):
    degree = 2 * (len(candidate["coefficients"]) - 1)
    left = rational(candidate["t"])
    if not 0 < left < right or not 1 <= limit < degree:
        raise ValueError("Require 0 < left < right and truncation below degree")
    with ctx.workdps(precision):
        modes = [arb(rational(v)) for v in candidate["coefficients"]]
        # |[t^j]P| <= (sum |a|) N^j/(j!)^2. The ensuing majorants on
        # |t|<=right have ratios <= N*right/(limit+2)^2.
        geometric = arb(degree * right) / (limit + 2)**2
        if not geometric < 1:
            raise ValueError("Truncation too short for a geometric upper remainder")
        remainder = (sum(map(abs, modes), arb(0)) * arb(degree * right)**(limit + 1)
                     / factorial(limit + 1)**2 / (1 - geometric)).upper()
        log(event="majorant", degree=degree, limit=limit, remainder=remainder.str(12))
        power = truncated_power(modes, limit)
        log(event="truncated_power")
        affine = arb_poly(power)(arb_poly([arb(left), arb(right - left)]))
        factors = [1] * (limit + 1)
        for j in range(limit, 0, -1):
            factors[j - 1] = factors[j] * j
        kernel = arb_poly(factors)
        coefficients = binomial_transform(
            [affine[j] / comb(limit, j) for j in range(limit + 1)], factors, kernel
        )

        stack = [(left, right, coefficients, 0)]
        leaves = deepest = 0
        while stack:
            a, b, coefficients, depth = stack.pop()
            if all(x > remainder for x in coefficients):
                leaves += 1
                deepest = max(deepest, depth)
                continue
            if coefficients[0] < -remainder or coefficients[-1] < -remainder:
                where = a if coefficients[0] < -remainder else b
                log(event="result", status="negative_point", t=str(where))
                return 1
            if depth == max_depth:
                log(event="result", status="inconclusive", interval=[str(a), str(b)], leaves=leaves)
                return 1
            mid = (a + b) / 2
            lo = binomial_transform(coefficients, factors, kernel)
            hi = binomial_transform(coefficients[::-1], factors, kernel)
            lo = [v / (1 << j) for j, v in enumerate(lo)]
            hi = [v / (1 << j) for j, v in enumerate(hi)][::-1]
            stack.extend([(mid, b, hi, depth + 1), (a, mid, lo, depth + 1)])
        log(event="result", status="certified_bounded_interval",
            interval=[str(left), str(right)], leaves=leaves, depth=deepest)
        return 0
