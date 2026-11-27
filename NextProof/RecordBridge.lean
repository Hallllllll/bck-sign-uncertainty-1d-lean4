import NextProof.Spec
import NextProof.TailPower16384
import NextProof.CompactPlan16384

namespace NextProof

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

theorem projected_full_tail (compact_check_16384 : Compact.check Compact.plan16384 (238361/(125000*65536)) Tail.powerLower = true) (t : ℝ) (ht : 238361/125000 ≤ t) :
    0 ≤ Exterior.projected16384.eval₂ (algebraMap ℚ ℝ) t := by
  by_cases h : 65536 ≤ t
  · exact (Exterior.projected16384_far _ h).le
  have hz : 0 ≤ t/65536 := by linarith
  have hc := Compact.check_sound Compact.plan16384 (238361/(125000*65536)) Tail.powerLower
    compact_check_16384 (t/65536) hz (by linarith) (by push_cast; linarith)
  have hp := hc.trans (Tail.powerLower_le _ hz)
  rw [show 65536*(t/65536)=t by ring] at hp
  exact nonneg_of_mul_nonneg_right hp (by positivity)

theorem projected_product_of_check (hc : Compact.check Compact.plan16384 (238361/(125000*65536)) Tail.powerLower = true) :
    AplusSquared ≤ (238361:ℝ)/(250000*Real.pi) := by
  convert upper_from_polynomial Exterior.projected16384 (238361/125000)
    (by norm_num) Exterior.projected16384_self_fourier
    (fun h => by
      have hx := Exterior.projected16384_gaussian_origin
      rw [h] at hx
      simpa using hx) Exterior.projected16384_origin.le (projected_full_tail hc) using 1
  ring

/-- A rational upper bound, rounding the product outward. -/
theorem projected_rational_of_check (hc : Compact.check Compact.plan16384 (238361/(125000*65536)) Tail.powerLower = true) :
    AplusSquared ≤ (151745325561309057:ℝ)/500000000000000000 := by
  apply (projected_product_of_check hc).trans
  rw [div_le_iff₀ (by positivity)]
  linarith [Real.pi_gt_d20]

end NextProof
#print axioms NextProof.projected_rational_of_check
