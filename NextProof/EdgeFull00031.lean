import NextProof.LeftKernel
import NextProof.OptEdge00031Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00025
import NextProof.EdgeFull00030

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp0000000 : Blocks := NextProof.EdgeRecovery.R00000001.P.data
private theorem bp00000000 : Branch 0 (1906884279970892581/512000000000000000000 : ℚ) vp0000000 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp00000000) (k:=0) (m:=15103) (by decide +kernel)
  rw [show 2*(1906884279970892581/512000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/256000000000000000000 : ℚ) by norm_num]
  exact coverp00000000
noncomputable def ep00000001 : Blocks := NextProof.EdgeRecovery.R00000001.E.data
private theorem idp00000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000.list =
    C ((2:ℤ)^15521) * horner X vp00000001.list + horner X ep00000001.list := by
  exact NextProof.EdgeRecovery.R00000001.identity
private theorem bp00000001 : Branch 1 (1906884279970892581/512000000000000000000 : ℚ) vp0000000 := by
  apply branch_checked idp00000001 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/512000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-254093115720029107419/256000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp00000001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp0000000 : Covers (1906884279970892581/512000000000000000000 : ℚ) vp0000000 := join_branches bp00000000 bp00000001
end NextProof.EdgeFull

