import NextProof.OptEdge00145Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00142
import NextProof.EdgeFull00144

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp11 : Blocks := NextProof.EdgeRecovery.R111.P.data
private theorem bp110 : Branch 0 (-6143761639/2048000000 : ℚ) vp11 := by
  apply branch_left_normalized (c:=vp110) (k:=0) (m:=9914) (by decide +kernel)
  rw [show 2*(-6143761639/2048000000 : ℚ) - ((0:ℤ):ℚ) = (-6143761639/1024000000 : ℚ) by norm_num]
  exact coverp110
noncomputable def ep111 : Blocks := NextProof.EdgeRecovery.R111.E.data
private theorem idp111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11.list =
    C ((2:ℤ)^20005) * horner X vp111.list + horner X ep111.list := by
  exact NextProof.EdgeRecovery.R111.identity
private theorem bp111 : Branch 1 (-6143761639/2048000000 : ℚ) vp11 := by
  apply branch_checked idp111 (by positivity) (by decide +kernel)
  rw [show 2*(-6143761639/2048000000 : ℚ) - ((1:ℤ):ℚ) = (-7167761639/1024000000 : ℚ) by norm_num]
  exact coverp111
theorem coverp11 : Covers (-6143761639/2048000000 : ℚ) vp11 := join_branches bp110 bp111
end NextProof.EdgeFull

