import NextProof.LeftKernel
import NextProof.OptEdge00050Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00038
import NextProof.EdgeFull00049

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp00000 : Blocks := NextProof.EdgeRecovery.R000001.P.data
private theorem bp000000 : Branch 0 (1906884279970892581/2048000000000000000000 : ℚ) vp00000 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp000000) (k:=0) (m:=15615) (by decide +kernel)
  rw [show 2*(1906884279970892581/2048000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/1024000000000000000000 : ℚ) by norm_num]
  exact coverp000000
noncomputable def ep000001 : Blocks := NextProof.EdgeRecovery.R000001.E.data
private theorem idp000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000.list =
    C ((2:ℤ)^16599) * horner X vp000001.list + horner X ep000001.list := by
  exact NextProof.EdgeRecovery.R000001.identity
private theorem bp000001 : Branch 1 (1906884279970892581/2048000000000000000000 : ℚ) vp00000 := by
  apply branch_checked idp000001 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/2048000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-1022093115720029107419/1024000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp000001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp00000 : Covers (1906884279970892581/2048000000000000000000 : ℚ) vp00000 := join_branches bp000000 bp000001
end NextProof.EdgeFull

