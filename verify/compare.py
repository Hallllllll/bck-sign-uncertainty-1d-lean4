"""Check the rational upper score and exact margins using only the stdlib.

From the release root: python3 -B verify/compare.py
The full-ray proof and the supplied Tomar v6 enclosure are separate inputs
to the mathematical comparison. This command checks the rational arithmetic.
"""
import argparse
from fractions import Fraction
import json
from pathlib import Path

from inputs import CUTOFF, WITNESS_PATH, WITNESS_SHA256, checked_document
import tomar_v6

OLD_UPPER = Fraction(151745325561309057, 500000000000000000)
RELEASE_UPPER = Fraction(151745029530798611, 500000000000000000)


def arctan_interval(reciprocal, terms):
    total = sum((Fraction((-1)**j, (2*j+1)*reciprocal**(2*j+1))
                 for j in range(terms)), Fraction(0))
    next_sum = total + Fraction((-1)**terms, (2*terms+1)*reciprocal**(2*terms+1))
    return min(total, next_sum), max(total, next_sum)


def machin_interval(terms5, terms239):
    low5, high5 = arctan_interval(5, terms5)
    low239, high239 = arctan_interval(239, terms239)
    return 16*low5 - 4*high239, 16*high5 - 4*low239


def compare(witness):
    checked_document(witness)
    lo, hi = map(Fraction, tomar_v6.SCORE_BRACKET)
    published = Fraction(tomar_v6.PUBLISHED_SCORE)
    if (lo, hi) != tuple(Fraction(r)**2 for r in tomar_v6.RADIUS_BRACKET):
        raise ArithmeticError("wrong exact squared root bracket")
    if not 0 < lo < hi < published == Fraction(tomar_v6.PUBLISHED_RADIUS)**2:
        raise ArithmeticError("Tomar bracket or published score is inconsistent")

    pi_lowers = [machin_interval(45, 15)[0], machin_interval(24, 9)[0]]
    pi_upper = machin_interval(31, 11)[1]
    candidates = [CUTOFF/(2*p) for p in pi_lowers]
    lower = CUTOFF/(2*pi_upper)
    scale = 10**18
    upper = Fraction(-(-max(candidates)*scale // 1), scale)
    previous_grid = upper - Fraction(1, scale)
    if not previous_grid < lower <= min(candidates) <= max(candidates) <= upper:
        raise ArithmeticError("pi bracket does not isolate the upward grid rounding")
    if not upper == RELEASE_UPPER < min(lo, OLD_UPPER):
        raise ArithmeticError("rounded bound disagrees with the release or fails to improve")
    return {
        "witness_sha256": WITNESS_SHA256,
        "cutoff": str(CUTOFF),
        "status": "exact_comparisons_passed",
        "upper": str(upper),
        "least_upward_18_decimal_grid_bound": str(upper),
        "previous_grid_bound": str(previous_grid),
        "pi_lower_exact": list(map(str, pi_lowers)),
        "pi_upper_exact": str(pi_upper),
        "t_over_twice_pi_upper_minus_previous_grid": str(lower-previous_grid),
        "upper_minus_t_over_twice_pi_lower": [str(upper-c) for c in candidates],
        "tomar_certificate_filename": tomar_v6.CERTIFICATE_FILENAME,
        "tomar_certificate_sha256": tomar_v6.CERTIFICATE_SHA256,
        "tomar_certificate_source": tomar_v6.SOURCE_URL,
        "tomar_enclosure_status": "supplied_input_not_recomputed",
        "tomar_published": str(published),
        "tomar_root_radius_bracket": list(tomar_v6.RADIUS_BRACKET),
        "tomar_root_score_bracket": [str(lo), str(hi)],
        "gain_over_tomar_published": str(published-upper),
        "gain_over_tomar_actual_score_bracket": [str(lo-upper), str(hi-upper)],
        "gain_over_previous_bound": str(OLD_UPPER-upper),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--witness", type=Path, default=WITNESS_PATH)
    args = parser.parse_args()
    print(json.dumps(compare(args.witness), indent=2))


if __name__ == "__main__":
    main()
