"""Export exact normalized vectors and half-interval transition residuals."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import re
import shutil
from time import perf_counter

from flint import fmpz

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
from power import prepare, shift_one

PLAN = ROOT / "NextProof/CompactPlan16384.lean"
CANDIDATE = ROOT / "BCK-degree-16384.json"
CUTOFF = Fraction(238361, 125000)
RADIUS = 65536
POWER_BITS = 100
CHUNK_SIZE = 128
MAX_UNESTIMATED_BYTES = 2_000_000_000
MAX_ESTIMATED_BYTES = 3_650_000_000
MIN_FREE_BYTES = 12 * 1024**3
FORMAT = "bck-compact-transition-v1"


@dataclass(frozen=True, slots=True)
class Node:
    tag: str
    k: int = 0
    m: int = 0
    children: tuple[Node, ...] = ()
    size: int = 1


def parse_plan(source):
    """Read constructor data only. References must name earlier definitions."""
    defs = {}
    chunks = re.findall(
        r"^(?:private )?def (\w+) : Plan :=\n(.*?)(?=^(?:private )?def |^end NextProof\.Compact)",
        source, re.MULTILINE | re.DOTALL,
    )
    for name, body in chunks:
        tokens = iter(re.findall(r"\.\w+|[()]|\w+", body))

        def expression():
            token = next(tokens)
            if token == "(":
                value = expression()
                if next(tokens) != ")":
                    raise ValueError(f"unbalanced plan expression in {name}")
                return value
            if token == ".skip":
                return Node("skip")
            if token in (".leaf", ".split"):
                k, m = int(next(tokens)), int(next(tokens))
                children = (expression(), expression()) if token == ".split" else ()
                return Node(token[1:], k, m, children, 1 + sum(c.size for c in children))
            return defs[token]

        if name in defs:
            raise ValueError(f"duplicate plan definition {name}")
        defs[name] = expression()
        if next(tokens, None) is not None:
            raise ValueError(f"unconsumed plan tokens in {name}")
    return defs["plan16384"]


def paths(node, path=""):
    yield path, node
    for s, child in enumerate(node.children):
        yield from paths(child, path + str(s))


def absolute_sum(values):
    return sum(map(abs, values), fmpz(0))


def signed_size(value):
    return (value.bit_length() + 8) // 8


def unit_lower(values):
    result = fmpz(0)
    for value in reversed(values):
        result = value + min(0, result)
    return result


def sign_guard(values):
    return (values[0] if values else fmpz(0)) + sum(
        (min(0, x) for x in values[1:]), fmpz(0)
    )


def hexint(value):
    return hex(int(value))


def initialize_candidate(raw):
    candidate = json.loads(raw)
    if (candidate["schema"] != "even-laguerre-alpha-minus-half-v1"
            or Fraction(candidate["t"]) != CUTOFF
            or len(candidate["coefficients"]) != 8193):
        raise ValueError("candidate does not match the compiled plan convention")
    return prepare(list(map(Fraction, candidate["coefficients"])), RADIUS, POWER_BITS)


def normalize(raw, node):
    if node.tag == "skip" or node.m >= len(raw):
        raise ValueError("normalization applied to a skip or incompatible vector")
    quotients = [c >> node.k for c in raw] if node.k else raw
    keep = quotients[:node.m + 1]
    keep[0] -= absolute_sum(quotients[node.m + 1:])
    return keep


def half_exact(parent, s):
    """Coefficients of 2^len(parent) V((X+s)/2), in ascending order."""
    n = len(parent)
    homogeneous = [c << (n - j) for j, c in enumerate(parent)]
    if s == 0:
        return homogeneous
    if s == 1:
        return shift_one(homogeneous)
    raise ValueError("half side must be 0 or 1")


def residual(exact, child, shift, *, in_place=False):
    tail = exact if in_place else exact.copy()
    for i, value in enumerate(child):
        tail[i] -= value << shift
    # Keep internal zeros, since their indices are part of the identity.
    while tail and tail[-1] == 0:
        tail.pop()
    guard = sign_guard(tail)
    if guard < 0:
        raise ArithmeticError("negative constant-plus-negative-mass guard")
    return tail, guard


def transition(parent, node, s):
    n = len(parent)
    exact = half_exact(parent, s)
    child = normalize([value >> n for value in exact], node)
    e, guard = residual(exact, child, n + node.k, in_place=True)
    return child, e, guard


def interval_data(left, right):
    return {"left": str(left), "right": str(right)}


def next_interval(left, right, s):
    middle = (left + right) / 2
    return (left, middle) if s == 0 else (middle, right)


class ShardWriter:
    def __init__(self, destination, cap, *, min_free, store_left):
        self.destination = destination
        self.cap = cap
        self.min_free = min_free
        self.store_left = store_left
        self.bytes_written = 0
        self.shards = 0
        self.vector_bytes = 0
        self.residual_bytes = {"left": 0, "right": 0, "root": 0}
        self.edge_counts = {"derived_left": 0, "stored_left": 0, "stored_right": 0}
        self.nodes = 0
        self.started = perf_counter()
        self.since_update = self.started

    def disk_check(self, pending=0):
        if self.min_free:
            free = shutil.disk_usage(self.destination).free
            if free - pending < self.min_free:
                raise RuntimeError(f"free disk would drop below {self.min_free} bytes "
                                   f"(free={free}, pending={pending})")

    def progress(self):
        self.nodes += 1
        now = perf_counter()
        if now - self.since_update >= 15:
            print(json.dumps({"event": "progress", "nodes": self.nodes, "shards": self.shards,
                              "binary_bytes": self.bytes_written, "edges": self.edge_counts,
                              "seconds": round(now - self.started, 3)}), flush=True)
            self.since_update = now

    def vector(self, stem, values, logical_terms=None, *, residual_kind=None):
        logical_terms = len(values) if logical_terms is None else logical_terms
        if len(values) > logical_terms:
            raise ValueError("stored vector exceeds its logical length")
        files = []
        total = sum(4 + signed_size(value) for value in values)
        if self.bytes_written + total > self.cap:
            raise RuntimeError(f"binary output cap of {self.cap} bytes would be exceeded")
        self.disk_check(total)
        for offset in range(0, len(values), CHUNK_SIZE):
            part = values[offset:offset + CHUNK_SIZE]
            name = f"vectors/{stem}-{offset // CHUNK_SIZE:04d}.bin"
            payload = bytearray()
            for value in part:
                size = signed_size(value)
                payload.extend(size.to_bytes(4, "little"))
                payload.extend(int(value).to_bytes(size, "little", signed=True))
            self.disk_check(len(payload))
            (self.destination / name).write_bytes(payload)
            files.append({"file": name, "offset": offset, "count": len(part),
                          "bytes": len(payload), "sha256": sha256(payload).hexdigest()})
        self.bytes_written += total
        self.shards += len(files)
        if residual_kind is None:
            self.vector_bytes += total
        else:
            self.residual_bytes[residual_kind] += total
        return {"logical_terms": logical_terms, "stored_terms": len(values),
                "bytes": total, "files": files}


def transition_record(writer, parent, parent_path, child, child_path, s, node, e, guard):
    n = len(parent)
    bound = ((absolute_sum(parent) << n)
             + (absolute_sum(child) << (n + node.k)) + absolute_sum(e))
    b = bound.bit_length()
    kind = "left" if s == 0 else "right"
    writer.edge_counts[f"stored_{kind}"] += 1
    if (fmpz(1) << b) <= bound:
        raise ArithmeticError("radix does not dominate the coefficient bound")
    return {
        "kind": "stored-residual",
        "parent": parent_path, "child": child_path, "s": s, "n": n,
        "k": node.k, "b": b, "sign_guard_hex": hexint(guard),
        "sign_guard_nonnegative": True,
        "E": writer.vector(f"{child_path}-E", e, logical_terms=n, residual_kind=kind),
    }


def root_record(writer, q, node, v):
    e, guard = residual(q, v, node.k)
    bound = absolute_sum(q) + (absolute_sum(v) << node.k) + absolute_sum(e)
    if q[0] >= 0:
        raise ArithmeticError("source vector has nonnegative Q[0]")
    return {
        "kind": "global-root-normalization", "Q_terms": len(q),
        "Q_origin_hex": hexint(q[0]), "Q_origin_negative": True,
        "k": node.k, "b": bound.bit_length(),
        "sign_guard_hex": hexint(guard), "sign_guard_nonnegative": True,
        "Q": {"same_as_V_at": ""} if node.k == 0 and q == v else writer.vector("root-Q", q),
        "E": writer.vector("root-E", e, logical_terms=len(q), residual_kind="root"),
    }


def export_subtree(writer, nodes, node, path, left, right, v, incoming=None):
    info = {"kind": node.tag, "interval": interval_data(left, right)}
    nodes[path] = info
    writer.progress()
    if node.tag == "skip":
        if not right < CUTOFF:
            raise ArithmeticError("skip endpoint reaches the cutoff")
        return
    info.update(k=node.k, m=node.m, V=writer.vector(f"{path or 'root'}-V", v))
    if incoming is not None:
        info["incoming"] = incoming
    if node.tag == "leaf":
        guard = unit_lower(v)
        if guard < 0:
            raise ArithmeticError("negative leaf guard")
        info["unit_lower_hex"] = hexint(guard)
        return
    info["children"] = [path + "0", path + "1"]
    for s, child_plan in enumerate(node.children):
        child_path = path + str(s)
        cl, cr = next_interval(left, right, s)
        if child_plan.tag == "skip":
            export_subtree(writer, nodes, child_plan, child_path, cl, cr, None)
            continue
        if s == 0 and not writer.store_left:
            child = normalize([value >> j for j, value in enumerate(v)], child_plan)
            edge = {"kind": "derived-left", "parent": path, "child": child_path,
                    "s": 0, "n": len(v), "k": child_plan.k}
            writer.edge_counts["derived_left"] += 1
        else:
            child, e, guard = transition(v, child_plan, s)
            edge = transition_record(writer, v, path, child, child_path, s, child_plan, e, guard)
            del e
        export_subtree(writer, nodes, child_plan, child_path, cl, cr, child, edge)
        del child


def locate(plan, q, path):
    """Compute just the ancestor chain and keep one incoming edge for the pilot."""
    node = plan
    v = normalize(q, node)
    left, right = Fraction(0), Fraction(RADIUS)
    anchor = None
    for i, step in enumerate(path):
        if node.tag != "split":
            raise ValueError(f"path descends through {node.tag} at {path[:i]!r}")
        s = int(step)
        child = node.children[s]
        if child.tag == "skip":
            raise ValueError(f"path enters skip at {path[:i+1]!r}")
        before = left, right
        left, right = next_interval(left, right, s)
        if i + 1 == len(path):
            w, e, guard = transition(v, child, s)
            anchor = (v, s, e, guard, before, node.k, node.m)
        else:
            n = len(v)
            w = normalize([c >> n for c in half_exact(v, s)], child)
        node, v = child, w
    return node, v, left, right, anchor


def planning_estimate(plan, *, store_left=True):
    """A plan-only upper estimate for E payloads, without replaying the tree."""
    # After child normalization the discarded absolute sum is below 2^62:
    # positive scaled constant has <=110 bits, and the tolerance uses >>48.
    # E at kept terms is the Euclidean remainder, with the tail charge at 0.
    # A dropped E coefficient is bounded by its charged term and one remainder.
    edge_records = edge_terms = count = 0
    for _, node in paths(plan):
        if node.tag != "split":
            continue
        n = node.m + 1
        for s, child in enumerate(node.children):
            if child.tag == "skip" or (s == 0 and not store_left):
                continue
            count += 1
            edge_terms += n
            edge_records += n * (4 + (n + child.k + 62 + 8) // 8)
    # Prior recorded exact global retained magnitude bits and term count.
    normalized_records_bound = (5_460_333_879 + 7) // 8 + 5 * 2_301_732
    return {"edges": count, "residual_logical_terms": edge_terms,
            "residual_signed_record_upper_bytes": edge_records,
            "normalized_signed_record_upper_bytes_from_prior_stats": normalized_records_bound,
            "total_signed_record_upper_bytes": edge_records + normalized_records_bound,
            "method": "plan-only bound; no coefficient replay or output files"}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--path", default="", help="binary prefix; L/R are accepted aliases")
    destinations = parser.add_mutually_exclusive_group(required=True)
    destinations.add_argument("--out", type=Path)
    destinations.add_argument("--estimate", action="store_true")
    destinations.add_argument("--list-pilots", action="store_true")
    parser.add_argument("--full", action="store_true",
                        help="allow the prior-estimated complete root export")
    parser.add_argument("--left-e", action=argparse.BooleanOptionalAction, default=None,
                        help="store left residuals (default on for stages, off for --full)")
    parser.add_argument("--max-bytes", type=int)
    args = parser.parse_args(argv)
    maximum = MAX_ESTIMATED_BYTES if args.full else MAX_UNESTIMATED_BYTES
    args.max_bytes = maximum if args.max_bytes is None else args.max_bytes
    store_left = not args.full if args.left_e is None else args.left_e
    path = args.path.upper().translate(str.maketrans({"L": "0", "R": "1"}))
    if not re.fullmatch("[01]*", path):
        parser.error("--path must contain only 0/1 or L/R")
    if args.full and (path or args.out is None):
        parser.error("--full requires --out and an empty path")
    if not 0 < args.max_bytes <= maximum:
        parser.error(f"--max-bytes must be between 1 and {maximum}")
    plan_raw = PLAN.read_bytes()
    plan_source = plan_raw.decode()
    plan = parse_plan(plan_source)
    if args.estimate:
        if path:
            parser.error("--estimate covers the whole plan and requires an empty path")
        print(json.dumps(planning_estimate(plan, store_left=store_left), indent=2))
        return
    if args.list_pilots:
        candidates = [(p, n) for p, n in paths(plan) if p.startswith(path)
                      and n.tag == "split" and 60 <= n.m <= 128]
        for p, n in sorted(candidates, key=lambda pair: (
                not 7 <= pair[1].size <= 31, pair[0].count("1"), len(pair[0]), pair[0]))[:20]:
            print(json.dumps({"path": p, "degree": n.m, "nodes": n.size}))
        return

    destination = args.out.resolve()
    if destination.exists():
        parser.error("--out already exists")
    # The conservative whole-tree estimate is available without replay; use
    # it to refuse accidentally attempting a multi-GB full-root export.
    estimate = planning_estimate(plan, store_left=store_left)
    if not path and estimate["total_signed_record_upper_bytes"] > args.max_bytes:
        parser.error("whole-root archive exceeds the conservative cap; export a --path stage")
    if args.full:
        free = shutil.disk_usage(destination.parent).free
        if free < MIN_FREE_BYTES:
            parser.error(f"full export requires at least {MIN_FREE_BYTES} free bytes; have {free}")
        print(json.dumps({"event": "authorized_full_export", "output": str(destination),
                          "cap_bytes": args.max_bytes, "free_bytes": free,
                          "min_free_bytes": MIN_FREE_BYTES, "store_left": store_left,
                          "estimate": estimate}), flush=True)
    start = perf_counter()
    raw = CANDIDATE.read_bytes()
    candidate_sha = sha256(raw).hexdigest()
    if f"Input SHA-256 {candidate_sha}." not in plan_source:
        raise ValueError("the candidate hash does not match the plan source")
    q = initialize_candidate(raw)
    node, v, left, right, anchor = locate(plan, q, path)
    print(json.dumps({"event": "subtree_ready", "path": path, "degree": node.m,
                      "nodes": node.size, "seconds": round(perf_counter() - start, 3)}), flush=True)
    destination.mkdir(parents=True)
    (destination / "vectors").mkdir()
    writer = ShardWriter(destination, args.max_bytes,
                         min_free=MIN_FREE_BYTES if args.full else 0, store_left=store_left)
    writer.disk_check()
    manifest = {
        "format": FORMAT,
        "encoding": "uint32_le_byte_count_then_signed_twos_complement_le",
        "coefficient_order": "ascending",
        "stage_path": path,
        "stage_interval": interval_data(left, right),
        "cutoff_t": str(CUTOFF),
        "root_interval": interval_data(Fraction(0), Fraction(RADIUS)),
        "root_power_bits": POWER_BITS,
        "candidate_sha256": candidate_sha,
        "plan_sha256": sha256(plan_raw).hexdigest(),
        "root_origin_Q": {"constant_hex": hexint(q[0]), "negative": q[0] < 0,
                          "scope": "constant of the integer lower polynomial Q"},
        "nodes": {},
        "left_edge_mode": "stored-residual" if store_left else "derived-left",
    }
    if anchor is None:
        manifest["root_binding"] = root_record(writer, q, node, v)
        incoming = None
    else:
        parent, s, e, guard, (pl, pr), pk, pm = anchor
        manifest["stage_anchor"] = {
            "kind": "supplied_normalized_parent",
            "path": path[:-1], "interval": interval_data(pl, pr),
            "k": pk, "m": pm, "V": writer.vector("anchor-parent-V", parent),
            "scope": "transition from the supplied parent; ancestors are outside this stage",
        }
        if s == 0 and not store_left:
            incoming = {"kind": "derived-left", "parent": path[:-1], "child": path,
                        "s": 0, "n": len(parent), "k": node.k}
            writer.edge_counts["derived_left"] += 1
        else:
            incoming = transition_record(writer, parent, path[:-1], v, path, s, node, e, guard)
        del parent, e
    del q, anchor
    export_subtree(writer, manifest["nodes"], node, path, left, right, v, incoming)
    if len(manifest["nodes"]) != node.size:
        raise ArithmeticError("subtree node count mismatch")
    manifest["counts"] = {"nodes": node.size, "shards": writer.shards,
                          "binary_bytes": writer.bytes_written}
    manifest["export"] = {"edges": writer.edge_counts, "vector_bytes": writer.vector_bytes,
                          "residual_bytes": writer.residual_bytes,
                          "cap_bytes": args.max_bytes, "min_free_bytes": writer.min_free}
    # Serialize incrementally, avoiding a second in-memory copy of the large index.
    pending = destination / "manifest.json.tmp"
    metadata_bytes = 0
    next_disk_check = 0
    with pending.open("xb") as stream:
        for piece in json.JSONEncoder(indent=2).iterencode(manifest):
            encoded = piece.encode()
            metadata_bytes += len(encoded)
            if writer.bytes_written + metadata_bytes + 1 > args.max_bytes:
                raise RuntimeError("total output cap would be exceeded by the manifest")
            if metadata_bytes >= next_disk_check:
                writer.disk_check(1 << 20)
                next_disk_check = metadata_bytes + (1 << 20)
            stream.write(encoded)
        writer.disk_check(1)
        stream.write(b"\n")
        metadata_bytes += 1
    writer.disk_check()
    pending.replace(destination / "manifest.json")
    print(json.dumps({"event": "written", "seconds": round(perf_counter() - start, 3),
                      **manifest["counts"], **manifest["export"], "manifest_bytes": metadata_bytes,
                      "free_bytes": shutil.disk_usage(destination).free,
                      "manifest": str(destination / "manifest.json")}), flush=True)


if __name__ == "__main__":
    main()
