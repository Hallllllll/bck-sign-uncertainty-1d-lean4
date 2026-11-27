import NextProof.OptEdge00129Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00120
import NextProof.EdgeFull00128

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp01 : Blocks := NextProof.EdgeRecovery.R011.P.data
private theorem bp010 : Branch 0 (-2047761639/2048000000 : ℚ) vp01 := by
  apply branch_left_normalized (c:=vp010) (k:=0) (m:=15084) (by decide +kernel)
  rw [show 2*(-2047761639/2048000000 : ℚ) - ((0:ℤ):ℚ) = (-2047761639/1024000000 : ℚ) by norm_num]
  exact coverp010
noncomputable def ep011 : Blocks := NextProof.EdgeRecovery.R011.E.data
private theorem idp011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01.list =
    C ((2:ℤ)^22291) * horner X vp011.list + horner X ep011.list := by
  exact NextProof.EdgeRecovery.R011.identity
private theorem bp011 : Branch 1 (-2047761639/2048000000 : ℚ) vp01 := by
  apply branch_checked idp011 (by positivity) (by decide +kernel)
  rw [show 2*(-2047761639/2048000000 : ℚ) - ((1:ℤ):ℚ) = (-3071761639/1024000000 : ℚ) by norm_num]
  exact coverp011
theorem coverp01 : Covers (-2047761639/2048000000 : ℚ) vp01 := join_branches bp010 bp011
end NextProof.EdgeFull

