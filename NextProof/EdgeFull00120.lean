import NextProof.OptEdge00120Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00114
import NextProof.EdgeFull00119

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

noncomputable def vp010 : Blocks := NextProof.EdgeRecovery.R0101.P.data
private theorem bp0100 : Branch 0 (-2047761639/1024000000 : ℚ) vp010 := by
  apply branch_left_normalized (c:=vp0100) (k:=0) (m:=9311) (by decide +kernel)
  rw [show 2*(-2047761639/1024000000 : ℚ) - ((0:ℤ):ℚ) = (-2047761639/512000000 : ℚ) by norm_num]
  exact coverp0100
noncomputable def ep0101 : Blocks := NextProof.EdgeRecovery.R0101.E.data
private theorem idp0101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010.list =
    C ((2:ℤ)^18036) * horner X vp0101.list + horner X ep0101.list := by
  exact NextProof.EdgeRecovery.R0101.identity
private theorem bp0101 : Branch 1 (-2047761639/1024000000 : ℚ) vp010 := by
  apply branch_checked idp0101 (by positivity) (by decide +kernel)
  rw [show 2*(-2047761639/1024000000 : ℚ) - ((1:ℤ):ℚ) = (-2559761639/512000000 : ℚ) by norm_num]
  exact coverp0101
theorem coverp010 : Covers (-2047761639/1024000000 : ℚ) vp010 := join_branches bp0100 bp0101
end NextProof.EdgeFull

