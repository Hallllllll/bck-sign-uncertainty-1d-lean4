import NextProof.OptEdge00128Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00125
import NextProof.EdgeFull00127

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp011 : Blocks := NextProof.EdgeRecovery.R0111.P.data
private theorem bp0110 : Branch 0 (-3071761639/1024000000 : ℚ) vp011 := by
  apply branch_left_normalized (c:=vp0110) (k:=0) (m:=7877) (by decide +kernel)
  rw [show 2*(-3071761639/1024000000 : ℚ) - ((0:ℤ):ℚ) = (-3071761639/512000000 : ℚ) by norm_num]
  exact coverp0110
noncomputable def ep0111 : Blocks := NextProof.EdgeRecovery.R0111.E.data
private theorem idp0111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011.list =
    C ((2:ℤ)^16325) * horner X vp0111.list + horner X ep0111.list := by
  exact NextProof.EdgeRecovery.R0111.identity
private theorem bp0111 : Branch 1 (-3071761639/1024000000 : ℚ) vp011 := by
  apply branch_checked idp0111 (by positivity) (by decide +kernel)
  rw [show 2*(-3071761639/1024000000 : ℚ) - ((1:ℤ):ℚ) = (-3583761639/512000000 : ℚ) by norm_num]
  exact coverp0111
theorem coverp011 : Covers (-3071761639/1024000000 : ℚ) vp011 := join_branches bp0110 bp0111
end NextProof.EdgeFull

