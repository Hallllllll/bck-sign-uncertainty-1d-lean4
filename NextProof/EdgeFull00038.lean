import NextProof.LeftKernel
import NextProof.OptEdge00038Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00031
import NextProof.EdgeFull00037

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp000000 : Blocks := NextProof.EdgeRecovery.R0000001.P.data
private theorem bp0000000 : Branch 0 (1906884279970892581/1024000000000000000000 : ℚ) vp000000 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp0000000) (k:=0) (m:=15359) (by decide +kernel)
  rw [show 2*(1906884279970892581/1024000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/512000000000000000000 : ℚ) by norm_num]
  exact coverp0000000
noncomputable def ep0000001 : Blocks := NextProof.EdgeRecovery.R0000001.E.data
private theorem idp0000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000.list =
    C ((2:ℤ)^15975) * horner X vp0000001.list + horner X ep0000001.list := by
  exact NextProof.EdgeRecovery.R0000001.identity
private theorem bp0000001 : Branch 1 (1906884279970892581/1024000000000000000000 : ℚ) vp000000 := by
  apply branch_checked idp0000001 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/1024000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-510093115720029107419/512000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp0000001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp000000 : Covers (1906884279970892581/1024000000000000000000 : ℚ) vp000000 := join_branches bp0000000 bp0000001
end NextProof.EdgeFull

