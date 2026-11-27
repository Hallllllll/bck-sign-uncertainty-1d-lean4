import NextProof.OptEdge00096Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00090
import NextProof.EdgeFull00095

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp0010 : Blocks := NextProof.EdgeRecovery.R00101.P.data
private theorem bp00100 : Branch 0 (-1023761639/512000000 : ℚ) vp0010 := by
  apply branch_left_normalized (c:=vp00100) (k:=0) (m:=6959) (by decide +kernel)
  rw [show 2*(-1023761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-1023761639/256000000 : ℚ) by norm_num]
  exact coverp00100
noncomputable def ep00101 : Blocks := NextProof.EdgeRecovery.R00101.E.data
private theorem idp00101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010.list =
    C ((2:ℤ)^13590) * horner X vp00101.list + horner X ep00101.list := by
  exact NextProof.EdgeRecovery.R00101.identity
private theorem bp00101 : Branch 1 (-1023761639/512000000 : ℚ) vp0010 := by
  apply branch_checked idp00101 (by positivity) (by decide +kernel)
  rw [show 2*(-1023761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-1279761639/256000000 : ℚ) by norm_num]
  exact coverp00101
theorem coverp0010 : Covers (-1023761639/512000000 : ℚ) vp0010 := join_branches bp00100 bp00101
end NextProof.EdgeFull

