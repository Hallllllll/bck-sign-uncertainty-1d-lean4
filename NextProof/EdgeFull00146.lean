import NextProof.OptEdge00146Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00139
import NextProof.EdgeFull00145

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp1 : Blocks := NextProof.EdgeRecovery.R11.P.data
private theorem bp10 : Branch 0 (-4095761639/4096000000 : ℚ) vp1 := by
  apply branch_left_normalized (c:=vp10) (k:=0) (m:=16384) (by decide +kernel)
  rw [show 2*(-4095761639/4096000000 : ℚ) - ((0:ℤ):ℚ) = (-4095761639/2048000000 : ℚ) by norm_num]
  exact coverp10
noncomputable def ep11 : Blocks := NextProof.EdgeRecovery.R11.E.data
private theorem idp11 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1.list =
    C ((2:ℤ)^28203) * horner X vp11.list + horner X ep11.list := by
  exact NextProof.EdgeRecovery.R11.identity
private theorem bp11 : Branch 1 (-4095761639/4096000000 : ℚ) vp1 := by
  apply branch_checked idp11 (by positivity) (by decide +kernel)
  rw [show 2*(-4095761639/4096000000 : ℚ) - ((1:ℤ):ℚ) = (-6143761639/2048000000 : ℚ) by norm_num]
  exact coverp11
theorem coverp1 : Covers (-4095761639/4096000000 : ℚ) vp1 := join_branches bp10 bp11
end NextProof.EdgeFull

