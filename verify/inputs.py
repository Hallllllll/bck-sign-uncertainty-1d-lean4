"""Immutable release witness and exact polynomial-coordinate cutoffs."""
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path

WITNESS_PATH = Path(__file__).resolve().parent.parent / "BCK-degree-16384.json"
WITNESS_SHA256 = "ae71adf610b66f2742021b8abcb7fb0156d79936db44b727eee18fe4891213a8"
SCHEMA = "even-laguerre-alpha-minus-half-v1"
DEGREE = 16384
OLD_CUTOFF = Fraction(238361, 125000)
CUTOFF = Fraction(1906884279970892581, 1000000000000000000)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def unique_keys(pairs):
    data = {}
    for key, value in pairs:
        if key in data:
            raise ValueError(f"duplicate JSON key {key!r}")
        data[key] = value
    return data


def checked_document(path):
    raw = path.read_bytes()
    if sha256(raw).hexdigest() != WITNESS_SHA256:
        raise ValueError("witness SHA-256 mismatch")
    data = json.loads(raw, object_pairs_hook=unique_keys)
    if (data["schema"] != SCHEMA or Fraction(data["t"]) != OLD_CUTOFF
            or len(data["coefficients"]) != DEGREE // 2 + 1):
        raise ValueError("unexpected witness convention")
    # Leave the published witness bytes, including the original cutoff, intact.
    return {**data, "t": str(CUTOFF)}
