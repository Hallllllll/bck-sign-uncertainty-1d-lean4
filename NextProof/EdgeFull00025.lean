import NextProof.LeftKernel
import NextProof.OptEdge00025Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00019
import NextProof.EdgeFull00024

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp00000000 : Blocks := NextProof.EdgeRecovery.R000000001.P.data
private theorem bp000000000 : Branch 0 (1906884279970892581/256000000000000000000 : ℚ) vp00000000 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp000000000) (k:=0) (m:=14847) (by decide +kernel)
  rw [show 2*(1906884279970892581/256000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/128000000000000000000 : ℚ) by norm_num]
  exact coverp000000000
noncomputable def ep000000001 : Blocks := NextProof.EdgeRecovery.R000000001.E.data
private theorem idp000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000.list =
    C ((2:ℤ)^15171) * horner X vp000000001.list + horner X ep000000001.list := by
  exact NextProof.EdgeRecovery.R000000001.identity
private theorem bp000000001 : Branch 1 (1906884279970892581/256000000000000000000 : ℚ) vp00000000 := by
  apply branch_checked idp000000001 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/256000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-126093115720029107419/128000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp000000001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp00000000 : Covers (1906884279970892581/256000000000000000000 : ℚ) vp00000000 := join_branches bp000000000 bp000000001
end NextProof.EdgeFull

