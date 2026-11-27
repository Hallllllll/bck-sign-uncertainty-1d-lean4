import NextProof.OptEdge00075Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00069
import NextProof.EdgeFull00074

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp00010 : Blocks := NextProof.EdgeRecovery.R000101.P.data
private theorem bp000100 : Branch 0 (-511761639/256000000 : ℚ) vp00010 := by
  apply branch_left_normalized (c:=vp000100) (k:=0) (m:=5115) (by decide +kernel)
  rw [show 2*(-511761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-511761639/128000000 : ℚ) by norm_num]
  exact coverp000100
noncomputable def ep000101 : Blocks := NextProof.EdgeRecovery.R000101.E.data
private theorem idp000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010.list =
    C ((2:ℤ)^10036) * horner X vp000101.list + horner X ep000101.list := by
  exact NextProof.EdgeRecovery.R000101.identity
private theorem bp000101 : Branch 1 (-511761639/256000000 : ℚ) vp00010 := by
  apply branch_checked idp000101 (by positivity) (by decide +kernel)
  rw [show 2*(-511761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-639761639/128000000 : ℚ) by norm_num]
  exact coverp000101
theorem coverp00010 : Covers (-511761639/256000000 : ℚ) vp00010 := join_branches bp000100 bp000101
end NextProof.EdgeFull

