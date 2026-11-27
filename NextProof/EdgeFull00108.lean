import NextProof.OptEdge00108Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00096
import NextProof.EdgeFull00107

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp001 : Blocks := NextProof.EdgeRecovery.R0011.P.data
private theorem bp0010 : Branch 0 (-1023761639/1024000000 : ℚ) vp001 := by
  apply branch_left_normalized (c:=vp0010) (k:=0) (m:=12119) (by decide +kernel)
  rw [show 2*(-1023761639/1024000000 : ℚ) - ((0:ℤ):ℚ) = (-1023761639/512000000 : ℚ) by norm_num]
  exact coverp0010
noncomputable def ep0011 : Blocks := NextProof.EdgeRecovery.R0011.E.data
private theorem idp0011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001.list =
    C ((2:ℤ)^19333) * horner X vp0011.list + horner X ep0011.list := by
  exact NextProof.EdgeRecovery.R0011.identity
private theorem bp0011 : Branch 1 (-1023761639/1024000000 : ℚ) vp001 := by
  apply branch_checked idp0011 (by positivity) (by decide +kernel)
  rw [show 2*(-1023761639/1024000000 : ℚ) - ((1:ℤ):ℚ) = (-1535761639/512000000 : ℚ) by norm_num]
  exact coverp0011
theorem coverp001 : Covers (-1023761639/1024000000 : ℚ) vp001 := join_branches bp0010 bp0011
end NextProof.EdgeFull

