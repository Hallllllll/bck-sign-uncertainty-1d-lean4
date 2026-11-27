import NextProof.LeftKernel
import NextProof.OptEdge00085Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00064
import NextProof.EdgeFull00084

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp000 : Blocks := NextProof.EdgeRecovery.R0001.P.data
private theorem bp0000 : Branch 0 (1906884279970892581/8192000000000000000000 : ℚ) vp000 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp0000) (k:=0) (m:=16127) (by decide +kernel)
  rw [show 2*(1906884279970892581/8192000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/4096000000000000000000 : ℚ) by norm_num]
  exact coverp0000
noncomputable def ep0001 : Blocks := NextProof.EdgeRecovery.R0001.E.data
private theorem idp0001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000.list =
    C ((2:ℤ)^19325) * horner X vp0001.list + horner X ep0001.list := by
  exact NextProof.EdgeRecovery.R0001.identity
private theorem bp0001 : Branch 1 (1906884279970892581/8192000000000000000000 : ℚ) vp000 := by
  apply branch_checked idp0001 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/8192000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-4094093115720029107419/4096000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp0001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp000 : Covers (1906884279970892581/8192000000000000000000 : ℚ) vp000 := join_branches bp0000 bp0001
end NextProof.EdgeFull

