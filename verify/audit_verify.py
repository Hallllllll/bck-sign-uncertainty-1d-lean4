"""Exact audit primitives for the integer full-ray check."""
from fractions import Fraction
from math import lcm
import re

from flint import fmpq, fmpz, fmpz_poly

# Adapted from the BCK project audit verifier.
# Original source SHA-256: d1dc964554dd7a8578273b774e5ac591d24f56ac7b529bd1c47a9bfdef60309a


def rational(value):
    """Read integers, fractions, and finite decimal strings exactly."""
    if type(value) is int:
        return fmpq(value)
    if isinstance(value, str) and re.fullmatch(
        r"[+-]?(?:[0-9]+/[0-9]+|(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?)",
        value,
    ):
        try:
            exact = Fraction(value)
        except ZeroDivisionError as error:
            raise ValueError(f"invalid rational {value!r}") from error
        return fmpq(exact.numerator, exact.denominator)
    raise ValueError(f"expected an exact rational, got {value!r}")


def sign(value):
    return int(value > 0) - int(value < 0)


def laguerre_point_sign(coefficients, point):
    """Evaluate by backward Clenshaw in scaled integers, without expansion."""
    denominator = lcm(*(int(c.denominator) for c in coefficients))
    weights = [
        c.numerator * (denominator // int(c.denominator)) for c in coefficients
    ]
    p, q = point.numerator, point.denominator
    degree = 2 * (len(weights) - 1)
    following = second_following = fmpz(0)
    scale = fmpz(1)
    for n in range(degree, -1, -1):
        # Clenshaw's nth state is scaled by denominator * (2q)^(d-n) d!/n!.
        # Ratios of consecutive scales clear the recurrence denominators.
        state = ((4 * n + 1) * q - 2 * p) * following
        state -= (2 * n + 1) * (n + 1) * 2 * q * q * second_following
        if n % 2 == 0:
            state += weights[n // 2] * scale
        second_following, following = following, state
        if n:
            scale *= 2 * q * n
    return {"point": str(point), "sign": sign(following),
            "scaled_numerator_bits": int(following.bit_length())}


def laguerre_dominance_ray(coefficients, ratio):
    """Prove a far ray by bounding consecutive Laguerre ratios."""
    if not 0 < ratio < 1:
        raise ValueError("dominance ratio must be strictly between zero and one")
    degree = 2 * (len(coefficients) - 1)
    if degree == 0:
        return {"nonnegative": coefficients[0] >= 0,
                "ray_start": "0" if coefficients[0] >= 0 else None,
                "ratio_bound": str(ratio)}

    start = 2 * degree - fmpq(3, 2) + (degree - fmpq(3, 2)) * ratio + degree / ratio
    # For A_n = (-1)^n L_n^(-1/2), the recurrence inductively gives
    # A_n/A_(n+1) <= ratio there. Bound every negative earlier mode
    # against the top mode and drop earlier nonnegative modes.
    loss = fmpq(0)
    for coefficient in coefficients[:-1]:
        loss = (loss + max(-coefficient, 0)) * ratio * ratio
    certified = coefficients[-1] >= loss
    return {
        "nonnegative": True if certified else None,
        "ray_start": str(start) if certified else None,
        "ratio_bound": str(ratio),
        "leading_mode_sign": sign(coefficients[-1]),
    }


def laguerre_power_floor(coefficients, radius, bits):
    """Return integer coefficients of a lower polynomial for P(radius*x)."""
    degree = 2 * (len(coefficients) - 1)
    common = lcm(*(int(c.denominator) for c in coefficients))
    modes = [fmpz(0)] * (degree + 1)
    central = fmpz(1)
    for n in range(degree + 1):
        if n % 2 == 0:
            c = coefficients[n // 2]
            modes[n] = central * c.numerator * (common // int(c.denominator))
            modes[n] <<= 2 * (degree - n)
        central = central * (4 * n + 2) // (n + 1)
    shifted = fmpz_poly(modes)(fmpz_poly([1, 1]))
    # (-4)^j j!/(2j)! = (-2)^j/(2j-1)!!.
    denominator = fmpz(common) << (2 * degree)
    numerator_scale = fmpz(1) << bits
    lower = []
    for j in range(degree + 1):
        lower.append((shifted[j] * numerator_scale) // denominator)
        denominator *= 2 * j + 1
        numerator_scale *= -2 * radius
    return lower


def compact_unit_lower(values, bits):
    """Compress only after localization to the unit interval."""
    shift = max(0, values[0].bit_length() - bits) if values[0] > 0 else 0
    if shift:
        values = [c >> shift for c in values]
    tolerance = max(32, (values[0] >> 54) if values[0] > 0 else 0)
    stop = len(values)
    cost = fmpz(0)
    deficit = fmpz(0)
    while stop > 1:
        c = values[stop - 1]
        cost += abs(c)
        if cost > tolerance:
            break
        deficit += min(0, c)
        stop -= 1
    # On [0,1], each removed negative term is bounded below by the
    # same coefficient times x^(stop-1). Removed positive terms help.
    reduced = values[:stop]
    reduced[-1] += deficit
    return reduced


def unit_horner_lower(values):
    bound = fmpz(0)
    for c in reversed(values):
        bound = c + min(0, bound)
    return bound
