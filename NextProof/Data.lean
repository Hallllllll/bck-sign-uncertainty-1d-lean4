import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Rat.Defs

namespace NextProof

noncomputable section

open Polynomial

/-- Non-record control for the analytic bridge. -/
def samplePolynomial : ℚ[X] := X^2 - 3*X

/-- Threshold in the polynomial variable s = 2πx². -/
def sampleThreshold : ℚ := 3

end

end NextProof
