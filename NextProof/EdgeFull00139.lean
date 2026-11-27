import NextProof.OptEdge00139Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00135
import NextProof.EdgeFull00138

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp10 : Blocks := NextProof.EdgeRecovery.R101.P.data
private theorem bp100 : Branch 0 (-4095761639/2048000000 : ℚ) vp10 := by
  apply branch_left_normalized (c:=vp100) (k:=0) (m:=12123) (by decide +kernel)
  rw [show 2*(-4095761639/2048000000 : ℚ) - ((0:ℤ):ℚ) = (-4095761639/1024000000 : ℚ) by norm_num]
  exact coverp100
noncomputable def ep101 : Blocks := NextProof.EdgeRecovery.R101.E.data
private theorem idp101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10.list =
    C ((2:ℤ)^22294) * horner X vp101.list + horner X ep101.list := by
  exact NextProof.EdgeRecovery.R101.identity
private theorem bp101 : Branch 1 (-4095761639/2048000000 : ℚ) vp10 := by
  apply branch_checked idp101 (by positivity) (by decide +kernel)
  rw [show 2*(-4095761639/2048000000 : ℚ) - ((1:ℤ):ℚ) = (-5119761639/1024000000 : ℚ) by norm_num]
  exact coverp101
theorem coverp10 : Covers (-4095761639/2048000000 : ℚ) vp10 := join_branches bp100 bp101
end NextProof.EdgeFull

