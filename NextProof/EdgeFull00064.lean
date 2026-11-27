import NextProof.LeftKernel
import NextProof.OptEdge00064Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00050
import NextProof.EdgeFull00063

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp0000 : Blocks := NextProof.EdgeRecovery.R00001.P.data
private theorem bp00000 : Branch 0 (1906884279970892581/4096000000000000000000 : ℚ) vp0000 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp00000) (k:=0) (m:=15871) (by decide +kernel)
  rw [show 2*(1906884279970892581/4096000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/2048000000000000000000 : ℚ) by norm_num]
  exact coverp00000
noncomputable def ep00001 : Blocks := NextProof.EdgeRecovery.R00001.E.data
private theorem idp00001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000.list =
    C ((2:ℤ)^17592) * horner X vp00001.list + horner X ep00001.list := by
  exact NextProof.EdgeRecovery.R00001.identity
private theorem bp00001 : Branch 1 (1906884279970892581/4096000000000000000000 : ℚ) vp0000 := by
  apply branch_checked idp00001 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/4096000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-2046093115720029107419/2048000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp00001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp0000 : Covers (1906884279970892581/4096000000000000000000 : ℚ) vp0000 := join_branches bp00000 bp00001
end NextProof.EdgeFull

