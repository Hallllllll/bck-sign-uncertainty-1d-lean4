import NextProof.LeftKernel
import NextProof.OptEdge00130Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00109
import NextProof.EdgeFull00129

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp0 : Blocks := NextProof.EdgeRecovery.R01.P.data
private theorem bp00 : Branch 0 (1906884279970892581/32768000000000000000000 : ℚ) vp0 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp00) (k:=0) (m:=16384) (by decide +kernel)
  rw [show 2*(1906884279970892581/32768000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/16384000000000000000000 : ℚ) by norm_num]
  exact coverp00
noncomputable def ep01 : Blocks := NextProof.EdgeRecovery.R01.E.data
private theorem idp01 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0.list =
    C ((2:ℤ)^28182) * horner X vp01.list + horner X ep01.list := by
  exact NextProof.EdgeRecovery.R01.identity
private theorem bp01 : Branch 1 (1906884279970892581/32768000000000000000000 : ℚ) vp0 := by
  apply branch_checked idp01 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/32768000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-16382093115720029107419/16384000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp01 x hx hx' (le_trans (by norm_num) hx)
theorem coverp0 : Covers (1906884279970892581/32768000000000000000000 : ℚ) vp0 := join_branches bp00 bp01
end NextProof.EdgeFull

