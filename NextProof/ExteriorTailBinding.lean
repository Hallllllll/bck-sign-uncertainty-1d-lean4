import NextProof.ExteriorCertificate16384
import NextProof.TailModes

namespace NextProof.Exterior

open Polynomial

/-- The exterior witness uses the same ascending dense series convention as the interval verifier. -/
theorem series_eq_tail (j : ℕ) (ws : List ℤ) : series j ws = Tail.series j ws := by
  induction ws generalizing j with
  | nil => rfl
  | cons w ws ih => simp only [series, Tail.series, ih]

theorem projected16384_eq_tail_series :
    projected16384 =
      C (1 / (Data16384.denominator : ℚ)) * Tail.series 0 Data16384.weights := by
  rw [projected16384, witness, series_eq_tail]

end NextProof.Exterior
