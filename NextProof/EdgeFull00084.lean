import NextProof.OptEdge00084Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00075
import NextProof.EdgeFull00083

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp0001 : Blocks := NextProof.EdgeRecovery.R00011.P.data
private theorem bp00010 : Branch 0 (-511761639/512000000 : ℚ) vp0001 := by
  apply branch_left_normalized (c:=vp00010) (k:=0) (m:=9307) (by decide +kernel)
  rw [show 2*(-511761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-511761639/256000000 : ℚ) by norm_num]
  exact coverp00010
noncomputable def ep00011 : Blocks := NextProof.EdgeRecovery.R00011.E.data
private theorem idp00011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001.list =
    C ((2:ℤ)^15732) * horner X vp00011.list + horner X ep00011.list := by
  exact NextProof.EdgeRecovery.R00011.identity
private theorem bp00011 : Branch 1 (-511761639/512000000 : ℚ) vp0001 := by
  apply branch_checked idp00011 (by positivity) (by decide +kernel)
  rw [show 2*(-511761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-767761639/256000000 : ℚ) by norm_num]
  exact coverp00011
theorem coverp0001 : Covers (-511761639/512000000 : ℚ) vp0001 := join_branches bp00010 bp00011
end NextProof.EdgeFull

