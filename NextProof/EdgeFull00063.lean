import NextProof.OptEdge00063Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00057
import NextProof.EdgeFull00062

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp00001 : Blocks := NextProof.EdgeRecovery.R000011.P.data
private theorem bp000010 : Branch 0 (-255761639/256000000 : ℚ) vp00001 := by
  apply branch_left_normalized (c:=vp000010) (k:=0) (m:=6958) (by decide +kernel)
  rw [show 2*(-255761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-255761639/128000000 : ℚ) by norm_num]
  exact coverp000010
noncomputable def ep000011 : Blocks := NextProof.EdgeRecovery.R000011.E.data
private theorem idp000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001.list =
    C ((2:ℤ)^12053) * horner X vp000011.list + horner X ep000011.list := by
  exact NextProof.EdgeRecovery.R000011.identity
private theorem bp000011 : Branch 1 (-255761639/256000000 : ℚ) vp00001 := by
  apply branch_checked idp000011 (by positivity) (by decide +kernel)
  rw [show 2*(-255761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-383761639/128000000 : ℚ) by norm_num]
  exact coverp000011
theorem coverp00001 : Covers (-255761639/256000000 : ℚ) vp00001 := join_branches bp000010 bp000011
end NextProof.EdgeFull

