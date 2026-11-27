import NextProof.LeftKernel
import NextProof.OptEdge00109Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00085
import NextProof.EdgeFull00108

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp00 : Blocks := NextProof.EdgeRecovery.R001.P.data
private theorem bp000 : Branch 0 (1906884279970892581/16384000000000000000000 : ℚ) vp00 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp000) (k:=0) (m:=16384) (by decide +kernel)
  rw [show 2*(1906884279970892581/16384000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/8192000000000000000000 : ℚ) by norm_num]
  exact coverp000
noncomputable def ep001 : Blocks := NextProof.EdgeRecovery.R001.E.data
private theorem idp001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00.list =
    C ((2:ℤ)^22277) * horner X vp001.list + horner X ep001.list := by
  exact NextProof.EdgeRecovery.R001.identity
private theorem bp001 : Branch 1 (1906884279970892581/16384000000000000000000 : ℚ) vp00 := by
  apply branch_checked idp001 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/16384000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-8190093115720029107419/8192000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp00 : Covers (1906884279970892581/16384000000000000000000 : ℚ) vp00 := join_branches bp000 bp001
end NextProof.EdgeFull

