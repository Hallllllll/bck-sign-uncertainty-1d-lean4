import NextProof.OptEdge00107Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00101
import NextProof.EdgeFull00106

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp0011 : Blocks := NextProof.EdgeRecovery.R00111.P.data
private theorem bp00110 : Branch 0 (-1535761639/512000000 : ℚ) vp0011 := by
  apply branch_left_normalized (c:=vp00110) (k:=0) (m:=5827) (by decide +kernel)
  rw [show 2*(-1535761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-1535761639/256000000 : ℚ) by norm_num]
  exact coverp00110
noncomputable def ep00111 : Blocks := NextProof.EdgeRecovery.R00111.E.data
private theorem idp00111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011.list =
    C ((2:ℤ)^11908) * horner X vp00111.list + horner X ep00111.list := by
  exact NextProof.EdgeRecovery.R00111.identity
private theorem bp00111 : Branch 1 (-1535761639/512000000 : ℚ) vp0011 := by
  apply branch_checked idp00111 (by positivity) (by decide +kernel)
  rw [show 2*(-1535761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-1791761639/256000000 : ℚ) by norm_num]
  exact coverp00111
theorem coverp0011 : Covers (-1535761639/512000000 : ℚ) vp0011 := join_branches bp00110 bp00111
end NextProof.EdgeFull

