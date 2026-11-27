import NextProof.Spec
import NextProof.ExteriorCertificate16384
import NextProof.CompactEdge

namespace NextProof
open Tail Compact

/-- A complete compact interval certificate plus the independently certified exterior
establishes the claimed rational bound for the sign uncertainty constant. -/
theorem projected_upper_from_cover (w : Blocks) (hc : Covers (1906884279970892581/65536000000000000000000) w)
    (hp : ∀ z : ℝ, 0 ≤ z → horner z w.list ≤
      (2:ℝ)^100 * Exterior.projected16384.eval₂ (algebraMap ℚ ℝ) (65536*z)) :
    AplusSquared ≤ (151745029530798611:ℝ)/500000000000000000 := by
  have ht : ∀ t : ℝ, 1906884279970892581/1000000000000000000 ≤ t → 0 ≤ Exterior.projected16384.eval₂ (algebraMap ℚ ℝ) t := by
    intro t hl
    by_cases hb : 65536 ≤ t
    · exact (Exterior.projected16384_far _ hb).le
    have hz : 0 ≤ t/65536 := by linarith
    have hs := hc (t/65536) hz (by linarith) (by norm_num; linarith)
    have h := hs.trans (hp _ hz)
    rw [show 65536*(t/65536)=t by ring] at h
    exact nonneg_of_mul_nonneg_right h (by positivity)
  have hn : radialGaussian Exterior.projected16384 ≠ 0 := by
    intro h
    have hx := Exterior.projected16384_gaussian_origin
    simp [h] at hx
  have h := upper_from_polynomial _ (1906884279970892581/1000000000000000000) (by norm_num)
    Exterior.projected16384_self_fourier hn Exterior.projected16384_origin.le ht
  apply h.trans
  rw [div_le_iff₀ (by positivity)]
  linarith [Real.pi_gt_d20]

end NextProof
#print axioms NextProof.projected_upper_from_cover
