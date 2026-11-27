"""Recompute either solver-free full-ray proof for BCK-degree-16384.json.

Requires Python 3.9+ and python-flint (tested with 0.9.0). From the release root:
  python3 -B verify/check.py compact
  python3 -B verify/check.py hybrid
"""
import argparse
from fractions import Fraction
import json
from math import factorial
from pathlib import Path
import sys
from time import monotonic
from types import SimpleNamespace

from flint import fmpq, fmpq_poly, fmpz, fmpz_poly

import audit_verify
import descartes
import power_tree
import prefix_verify
from inputs import CUTOFF, OLD_CUTOFF, WITNESS_PATH, WITNESS_SHA256, checked_document, digest
from signpoint import sign_at
from verify import exterior

# Adapted from the BCK step 1.2 driver. Original source SHA-256: dd838e106012ce1f6c6a21f46c3164b121ad532871a44c7e3e4cd9a5b2453745


def emit(event, **data):
    print(json.dumps({"event": event, **data}, default=str), file=sys.stderr, flush=True)


def check_cover(leaves, left, right):
    previous = left
    for a, b in sorted((Fraction(a), Fraction(b)) for a, b in leaves):
        if b <= left:
            continue
        if max(a, left) != previous or b <= previous:
            raise ArithmeticError(f"cover gap or overlap at {previous}: [{a}, {b}]")
        previous = b
    if previous != right:
        raise ArithmeticError(f"cover ends at {previous}, expected {right}")


def exact_threshold_leaf(coefficients, root, threshold, seam, radius, bits):
    """A single rational leaf from the cutoff to the audited suffix."""
    degree = 2*(len(coefficients)-1)
    order = 640
    if not (0 < threshold < seam <= 2 and order < degree):
        raise ValueError("invalid localized leaf")
    mass = sum(map(abs, coefficients), fmpq(0))
    ratio = fmpq(2*degree, (order+2)**2)
    if not ratio < 1:
        raise ArithmeticError("Laguerre tail majorant is not geometric")
    remainder = (mass*(2*degree)**(order+1) /
                 factorial(order+1)**2 / (1-ratio))
    remainder_upper = fmpq(1, 2**400)
    if not remainder < remainder_upper:
        raise ArithmeticError("Laguerre tail remainder budget failed")
    local = fmpq_poly(root[:order+1])(
        fmpq_poly([threshold/radius, (seam-threshold)/radius]))
    derivative_lower = local[1] + sum((min(0, j*local[j]) for j in range(2, order+1)), fmpq(0))
    derivative_witness = fmpq(1, 2**20)
    constant_witness = fmpq(1, 2**60)
    scale = 2**bits
    if not (derivative_lower > scale*derivative_witness and
            local[0] > scale*(constant_witness + remainder_upper)):
        raise ArithmeticError("exact localized lower polynomial did not certify the leaf")
    return {"interval": [str(threshold), str(seam)], "leading_power_terms": order+1,
            "taylor_remainder_absolute_upper": str(remainder_upper),
            "normalized_leaf_derivative_lower": str(derivative_witness),
            "strict_polynomial_lower": str(constant_witness),
            "coordinate": "t = left + (right-left)*u, 0 <= u <= 1"}


def exact_tail(coefficients, threshold, args):
    """Reuse the audit power floor, integer dyadic maps and exterior bound."""
    radius = 65536
    far = audit_verify.laguerre_dominance_ray(coefficients, fmpq(1023, 1024))
    if far["nonnegative"] is not True or Fraction(far["ray_start"]) > radius:
        raise ArithmeticError("exterior did not meet compact coverage")
    root = audit_verify.laguerre_power_floor(coefficients, radius, args.bits)
    emit("power_floor_ready", radius=radius, bits=args.bits)
    seam = audit_verify.rational(str(OLD_CUTOFF))
    prefix = exact_threshold_leaf(coefficients, root, threshold, seam, radius, args.bits)
    emit("threshold_leaf_certified", **prefix)
    leaves = [prefix["interval"]]
    threshold = seam
    shift_one = fmpz_poly([1, 1])
    stack = [(root, fmpq(0), fmpq(radius), 0)]
    clips = []
    nodes = deepest = 0
    while stack and nodes < args.max_nodes:
        values, left, right, depth = stack.pop()
        nodes += 1
        deepest = max(deepest, depth)
        values = audit_verify.compact_unit_lower(values, args.bits)
        if left < threshold and len(values) <= 64:
            clips.append({"depth": depth, "original": [str(left), str(right)],
                          "restricted": [str(threshold), str(right)], "degree": len(values)-1})
            cut = (threshold-left)/(right-left)
            localized = fmpq_poly(values)(fmpq_poly([cut, 1-cut]))
            values = localized.numer().coeffs() or [fmpz(0)]
            left = threshold
        if audit_verify.unit_horner_lower(values) >= 0:
            leaves.append([str(max(left, threshold)), str(right)])
            continue
        if depth == args.max_depth:
            stack.append((values, left, right, depth))
            break
        degree = len(values)-1
        scaled = fmpz_poly([c << (degree-j) for j, c in enumerate(values)])
        translated = scaled(shift_one)
        middle = (left+right)/2
        stack.append(([translated[j] >> degree for j in range(degree+1)],
                      middle, right, depth+1))
        if middle > threshold:
            stack.append(([c >> j for j, c in enumerate(values)], left, middle, depth+1))
    unresolved = None
    if stack:
        _, left, right, _ = stack[-1]
        unresolved = [str(max(left, threshold)), str(right)]
    return {"nonnegative": True if not stack else None, "dominance_ray": far,
            "first_unresolved_interval": unresolved, "compact_radius": radius,
            "certified_intervals": leaves, "nodes": nodes, "max_depth_used": deepest,
            "threshold_clips": clips, "exact_threshold_leaf": prefix,
            "threshold_tail_budget_shift": None}


def compact(args, doc):
    threshold = audit_verify.rational(doc["t"])
    coefficients = [audit_verify.rational(token) for token in doc["coefficients"]]
    origin = audit_verify.laguerre_point_sign(coefficients, audit_verify.rational("0"))
    point = audit_verify.laguerre_point_sign(coefficients, threshold)
    if origin["sign"] != -1 or point["sign"] != 1:
        raise ArithmeticError("strict origin or cutoff sign failed")
    tail = exact_tail(coefficients, threshold, args)
    if (tail["nonnegative"] is not True or
            tail["first_unresolved_interval"] is not None):
        return {"status": "inconclusive", "tail": tail}
    radius = Fraction(tail["compact_radius"])
    if Fraction(tail["dominance_ray"]["ray_start"]) > radius:
        raise ArithmeticError("no compact/exterior overlap")
    leaves = tail["certified_intervals"]
    check_cover(leaves, args.cutoff, radius)
    left, right = min((Fraction(a), Fraction(b)) for a, b in leaves)
    return {"status": "certified_full_ray", "method": "exact rounded power and Horner",
            "origin": origin, "cutoff_point": point, "bits": args.bits,
            "max_depth": args.max_depth, "max_nodes": args.max_nodes,
            "first_leaf_width": str(right-left), "tail": tail}


def hybrid(args, doc):
    coeffs = list(map(Fraction, doc["coefficients"]))
    degree = 2*(len(coeffs)-1)
    radius = 4*degree
    seam = Fraction(2)
    origin, _ = sign_at(coeffs, Fraction(0))
    if origin != -1 or coeffs[-1] <= 0:
        raise ArithmeticError("strict origin or leading sign failed")
    prefix = []

    def prefix_log(**row):
        prefix.append(row)
        emit("prefix", detail=row)

    prefix_rc = prefix_verify.algorithm(doc, audit_verify.rational(str(seam)),
                                        660, 400, args.max_depth, prefix_log)
    if prefix_rc or prefix[-1].get("interval") != [str(args.cutoff), str(seam)]:
        return {"status": "inconclusive", "prefix": prefix}
    if prefix[-1]["status"] != "certified_bounded_interval":
        raise ArithmeticError("unexpected prefix result")
    negative_mode = exterior(coeffs, degree)
    leaves = []
    splits = 0

    def record(action, **row):
        nonlocal splits
        if action == "proved":
            leaves.append(row)
        elif action == "split":
            splits += 1
            if splits >= args.max_nodes:
                raise ArithmeticError("hybrid compact split budget exhausted")

    values = descartes.prepare(coeffs, radius, args.bits, emit)
    power_tree.visit(values, Fraction(0), Fraction(radius), "",
                                SimpleNamespace(right=True, omit_below=seam,
                                                max_depth=args.max_depth), record)
    check_cover(((row["left"], row["right"]) for row in leaves), seam, Fraction(radius))
    return {"status": "certified_full_ray", "method": "Arb Bernstein prefix, exact lower tree, monic exterior",
            "origin_sign": origin, "prefix": prefix, "compact_interval": [str(seam), radius],
            "compact_splits": splits, "compact_max_depth_used": max(len(row["path"]) for row in leaves),
            "compact_leaves": leaves, "exterior_from": radius, "highest_negative_mode": negative_mode,
            "bits": args.bits, "max_depth": args.max_depth, "max_nodes": args.max_nodes}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("mode", choices=("compact", "hybrid"))
    parser.add_argument("--witness", type=Path, default=WITNESS_PATH)
    parser.add_argument("--bits", type=int, default=120)
    parser.add_argument("--max-depth", type=int, default=55)
    parser.add_argument("--max-nodes", type=int, default=25000)
    args = parser.parse_args()
    args.cutoff = CUTOFF
    if args.bits < 32 or args.max_depth < 0 or args.max_nodes <= 0:
        parser.error("expected bits >= 32, nonnegative depth, and positive node budget")
    if fmpz(-3) >> 1 != -2:
        raise ArithmeticError("FLINT signed right shift must implement floor division")
    start = monotonic()
    doc = checked_document(args.witness)
    verify = compact if args.mode == "compact" else hybrid
    result = verify(args, doc)
    if digest(args.witness) != WITNESS_SHA256:
        raise ArithmeticError("witness changed during verification")
    print(json.dumps({"witness_sha256": WITNESS_SHA256, "cutoff": str(CUTOFF), **result,
                      "seconds": round(monotonic()-start, 3)}, indent=2))
    return 0 if result["status"] == "certified_full_ray" else 1


if __name__ == "__main__":
    raise SystemExit(main())
