"""Regenerate and verify the certificate's exact binary inputs."""
import argparse
from hashlib import file_digest, sha256
from pathlib import Path
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parents[1]
REFERENCE = Path(__file__).with_name("input-digests.tsv")


def verify(root):
    for row in REFERENCE.read_text(encoding="ascii").splitlines():
        relative, count, size, expected = row.split("\t")
        directory = root / relative
        paths = sorted(directory.glob("*.bin"))
        if len(paths) != int(count):
            raise ValueError(f"{relative}: expected {count} binary files, found {len(paths)}")
        listing_hash = sha256()
        total = 0
        for path in paths:
            if path.is_symlink() or not path.is_file():
                raise ValueError(f"{relative}/{path.name}: expected a regular file")
            total += path.stat().st_size
            with path.open("rb") as stream:
                digest = file_digest(stream, "sha256").hexdigest()
            listing_hash.update(f"{digest}  {path.name}\n".encode("ascii"))
        if total != int(size) or listing_hash.hexdigest() != expected:
            raise ValueError(f"{relative}: corpus digest or byte count does not match")
        print(row, flush=True)


def generate(root):
    import flint
    if flint.__version__ != "0.9.0":
        raise ValueError(f"expected python-flint 0.9.0, found {flint.__version__}")
    import compact
    import tail

    names = ("compact_cert", "tail_cert")
    for name in names:
        path = root / name
        if path.exists() or path.is_symlink():
            raise ValueError(f"{path}: outputs already exist; use verify or a fresh destination")
    with TemporaryDirectory(prefix=".bck-inputs-", dir=root) as temp:
        stage = Path(temp)
        (stage / "compact_cert").mkdir()
        compact.main(["--out", str(stage / "compact_cert/pilot"), "--path",
                      "00000001000000", "--left-e"])
        compact.main(["--out", str(stage / "compact_cert/full"), "--full",
                      "--no-left-e", "--max-bytes", "3650000000"])
        tail.build(ROOT / "BCK-degree-16384.json", stage / "tail_cert/shards")
        verify(stage)
        for name in names:
            (stage / name).rename(root / name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("generate", "verify"))
    parser.add_argument("--output", type=Path, default=ROOT,
                        help="corpus parent, defaults to the checkout root")
    args = parser.parse_args()
    root = args.output.resolve()
    try:
        if args.command == "generate":
            root.mkdir(parents=True, exist_ok=True)
            generate(root)
        else:
            verify(root)
    except (OSError, ValueError, ImportError, ArithmeticError, RuntimeError) as error:
        parser.exit(1, f"{parser.prog}: {error}\n")


if __name__ == "__main__":
    main()
