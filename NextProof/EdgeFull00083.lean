import NextProof.OptEdge00083Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00080
import NextProof.EdgeFull00082

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp00011 : Blocks := NextProof.EdgeRecovery.R000111.P.data
private theorem bp000110 : Branch 0 (-767761639/256000000 : ℚ) vp00011 := by
  apply branch_left_normalized (c:=vp000110) (k:=0) (m:=4253) (by decide +kernel)
  rw [show 2*(-767761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-767761639/128000000 : ℚ) by norm_num]
  exact coverp000110
noncomputable def ep000111 : Blocks := NextProof.EdgeRecovery.R000111.E.data
private theorem idp000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011.list =
    C ((2:ℤ)^8616) * horner X vp000111.list + horner X ep000111.list := by
  exact NextProof.EdgeRecovery.R000111.identity
private theorem bp000111 : Branch 1 (-767761639/256000000 : ℚ) vp00011 := by
  apply branch_checked idp000111 (by positivity) (by decide +kernel)
  rw [show 2*(-767761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-895761639/128000000 : ℚ) by norm_num]
  exact coverp000111
theorem coverp00011 : Covers (-767761639/256000000 : ℚ) vp00011 := join_branches bp000110 bp000111
end NextProof.EdgeFull

