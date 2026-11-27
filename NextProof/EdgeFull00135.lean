import NextProof.OptEdge00135Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00132
import NextProof.EdgeFull00134

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp100 : Blocks := NextProof.EdgeRecovery.R1001.P.data
private theorem bp1000 : Branch 0 (-4095761639/1024000000 : ℚ) vp100 := by
  apply branch_left_normalized (c:=vp1000) (k:=0) (m:=6965) (by decide +kernel)
  rw [show 2*(-4095761639/1024000000 : ℚ) - ((0:ℤ):ℚ) = (-4095761639/512000000 : ℚ) by norm_num]
  exact coverp1000
noncomputable def ep1001 : Blocks := NextProof.EdgeRecovery.R1001.E.data
private theorem idp1001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100.list =
    C ((2:ℤ)^15079) * horner X vp1001.list + horner X ep1001.list := by
  exact NextProof.EdgeRecovery.R1001.identity
private theorem bp1001 : Branch 1 (-4095761639/1024000000 : ℚ) vp100 := by
  apply branch_checked idp1001 (by positivity) (by decide +kernel)
  rw [show 2*(-4095761639/1024000000 : ℚ) - ((1:ℤ):ℚ) = (-4607761639/512000000 : ℚ) by norm_num]
  exact coverp1001
theorem coverp100 : Covers (-4095761639/1024000000 : ℚ) vp100 := join_branches bp1000 bp1001
end NextProof.EdgeFull

