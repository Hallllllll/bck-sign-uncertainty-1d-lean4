# One-dimensional BCK sign uncertainty bound

This repository proves an unconditional upper bound for the squared positive-sign uncertainty constant in dimension one, represented in Lean 4 by `NextProof.AplusSquared`. The witness is a self-Fourier function of the form $P(2\pi x^2)\exp(-\pi x^2)$ with 8,193 even-index Laguerre modes and degree 16,384 in the polynomial coordinate $t=2\pi x^2$. Lean proves that it is negative at the origin and nonnegative for every $t\ge t^*$. The resulting squared bound is $A_+(1)^2\le U^*$.

```text
t* = 1906884279970892581/1000000000000000000 = 1.906884279970892581
U* = 151745029530798611/500000000000000000  = 0.303490059061597222
```

Here `U*` is the upward rounding of `t*/(2π)` to the 18-decimal grid. The last sign-changing root of the witness polynomial lies strictly between the exact decimals `1.9068842799708925802167577406` and `1.9068842799708925802167577407`.

## Comparison with Tomar v6

Tejasvi Singh Tomar's v6 Gaussian witness certifies the published radius `5509/10000`, giving the published squared score `30349081/100000000`. Its actual last sign-changing radius was independently isolated in the open interval with rational endpoints `101623087556280535787126849/184467440737095516160000000` and `2032461751125610715742537/3689348814741910323200000`. Squaring gives a score near `0.30349065741836995`, with outward decimal enclosure `[0.303490657418369951824519212483, 0.303490657418369951824519218457]`. [Tomar v6 README](https://raw.githubusercontent.com/tejasvi/sign-uncertainty-constant/v6/README.md) · [Tomar v6 certificate](https://raw.githubusercontent.com/tejasvi/sign-uncertainty-constant/v6/certs/pcert_r05509_NR2.json)

- The published squared score minus `U*` equals `375469201389/500000000000000000` exactly.
- The actual squared last-root radius minus `U*` is strictly greater than `12725641180479920815196532803884695479493068114673/21267647932558653966460912964485513216000000000000000000`. This exact rational margin uses the lower endpoint of the independently isolated score interval. The comparison script checks the arithmetic from the supplied Tomar enclosure.

## Lean verification

The unconditional theorem has this statement. [Lean source](NextProof/ProjectedBound.lean)

```lean
theorem NextProof.projected_rational_upper :
    NextProof.AplusSquared ≤ (151745029530798611 : ℝ) / 500000000000000000
```

The standalone axiom audit produced the following output.

```text
'NextProof.projected_rational_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The recorded x86-64 Ubuntu 24.04.4 LTS run used one AMD EPYC 7513 (32 physical cores, 64 logical CPUs, 98,804,584 KiB of system RAM as reported by Linux).

| Operation | Wall time | Peak RSS (KiB, GNU time) | Result |
| --- | ---: | ---: | --- |
| Clean `lake build`, `LEAN_NUM_THREADS=16` | 21:55.88 | 10,523,168 | Exit 0 |
| Independent named `leanchecker` replay, eight workers with one Lean thread each | 22:38.56 | 9,170,196 | 352/352 modules, all exit 0 |

Flipping the leading coefficient and moving the cutoff to 1.906884279970892580 each made the corresponding Lake build fail with exit 1. Both restored targets and the full restored project built with exit 0.

## Reproduce

Run from a fresh checkout on Linux with Bash, Python 3.11 or newer, GNU coreutils, and the pinned Lean 4.36.0 toolchain available through Elan. The generator writes 43,524 binary inputs totaling 2,561,379,294 bytes. Allow additional disk space for dependencies and compiled objects.

The byte-identical [witness JSON](BCK-degree-16384.json) retains the original field `"t": "1906888/1000000"`. The tightened cutoff is set separately in the verification code and Lean certificate.

```bash
set -euo pipefail
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -r reproduce/requirements.txt

printf '%s  %s\n' \
  ae71adf610b66f2742021b8abcb7fb0156d79936db44b727eee18fe4891213a8 \
  BCK-degree-16384.json | sha256sum -c -
sha256sum -c reproduce/lean-sources.sha256

python -B verify/isolate_verify.py BCK-degree-16384.json
python -B verify/check.py compact
python -B verify/check.py hybrid
python -B verify/compare.py
python -B reproduce/inputs.py generate
python -B reproduce/inputs.py verify

lake exe cache get
test ! -e .lake/build
LEAN_NUM_THREADS=16 lake build
printf 'import NextProof\n#print axioms NextProof.projected_rational_upper\n' \
  | lake env lean --stdin
```

Replay every local module sequentially in a separate checker process. The root module `NextProof` needs its compiled child directory on `LEAN_PATH` so the checker can resolve the namespace.

```bash
set -euo pipefail
export LC_ALL=C LEAN_NUM_THREADS=1
replay_dir=$(mktemp -d)
base_lean_path=$(lake env printenv LEAN_PATH)
lib_dir="$PWD/.lake/build/lib/lean"

{ find NextProof -type f -name '*.lean'; printf '%s\n' NextProof.lean; } \
  | sed -e 's/\.lean$//' -e 's|/|.|g' | sort > "$replay_dir/modules"
(cd "$lib_dir" && find . -type f -name '*.olean') \
  | sed -e 's|^\./||' -e 's/\.olean$//' -e 's|/|.|g' \
  | sort > "$replay_dir/compiled"
diff -u "$replay_dir/modules" "$replay_dir/compiled"
test "$(wc -l < "$replay_dir/modules")" -eq 352

while IFS= read -r module; do
  module_path="$lib_dir/${module//./\/}"
  checker=(lake env)
  if [[ -d "$module_path" ]]; then
    checker+=(env "LEAN_PATH=$module_path:$base_lean_path")
  fi
  "${checker[@]}" leanchecker -v "$module" > "$replay_dir/$module.log" 2>&1
  test "$(grep '^replaying ' "$replay_dir/$module.log")" = "replaying $module"
done < "$replay_dir/modules"
printf 'Replayed 352/352 local modules. Logs in %s\n' "$replay_dir"
```

## Disclosure

GPT-6.2 Astra and GPT-6.2 Sol in Codex assisted with the computation, Lean formalization, verification, and documentation.
