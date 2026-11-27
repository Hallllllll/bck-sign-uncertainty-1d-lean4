import NextProof.LeftKernel
import NextProof.OptEdge00147Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00130
import NextProof.EdgeFull00146

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vroot : Blocks := NextProof.EdgeRecovery.R1.P.data
private theorem bp0 : Branch 0 (1906884279970892581/65536000000000000000000 : ℚ) vroot := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp0) (k:=0) (m:=16384) (by decide +kernel)
  rw [show 2*(1906884279970892581/65536000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/32768000000000000000000 : ℚ) by norm_num]
  exact coverp0
noncomputable def ep1 : Blocks := NextProof.EdgeRecovery.R1.E.data
private theorem idp1 : halfForm (X:ℤ[X]) (C (1:ℤ)) vroot.list =
    C ((2:ℤ)^39997) * horner X vp1.list + horner X ep1.list := by
  exact NextProof.EdgeRecovery.R1.identity
private theorem bp1 : Branch 1 (1906884279970892581/65536000000000000000000 : ℚ) vroot := by
  apply branch_checked idp1 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/65536000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-32766093115720029107419/32768000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp1 x hx hx' (le_trans (by norm_num) hx)
theorem coverroot : Covers (1906884279970892581/65536000000000000000000 : ℚ) vroot := join_branches bp0 bp1
end NextProof.EdgeFull

#print axioms NextProof.EdgeFull.coverroot
