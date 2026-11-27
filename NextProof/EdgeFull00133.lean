import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp10011111111_0 : Blocks := edgeBlocks% "full/vectors/10011111111-V-0000.bin"
noncomputable def vp10011111111 : Blocks := vp10011111111_0
theorem coverp10011111111 : Covers (-5115761639/4000000 : ℚ) vp10011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp10011111110_0 : Blocks := edgeBlocks% "full/vectors/10011111110-V-0000.bin"
noncomputable def vp10011111110 : Blocks := vp10011111110_0
theorem coverp10011111110 : Covers (-5111761639/4000000 : ℚ) vp10011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001111111_0 : Blocks := edgeBlocks% "full/vectors/1001111111-V-0000.bin"
private noncomputable def vp1001111111_1 : Blocks := edgeBlocks% "full/vectors/1001111111-V-0001.bin"
noncomputable def vp1001111111 : Blocks := (Blocks.join vp1001111111_0 vp1001111111_1)
private theorem bp10011111110 : Branch 0 (-5111761639/8000000 : ℚ) vp1001111111 := by
  apply branch_left_normalized (c:=vp10011111110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5111761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5111761639/4000000 : ℚ) by norm_num]
  exact coverp10011111110
private noncomputable def ep10011111111_0 : Blocks := edgeBlocks% "full/vectors/10011111111-E-0000.bin"
private noncomputable def ep10011111111_1 : Blocks := edgeBlocks% "full/vectors/10011111111-E-0001.bin"
noncomputable def ep10011111111 : Blocks := (Blocks.join ep10011111111_0 ep10011111111_1)
private theorem idp10011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001111111.list =
    C ((2:ℤ)^155) * horner X vp10011111111.list + horner X ep10011111111.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011111111 : Branch 1 (-5111761639/8000000 : ℚ) vp1001111111 := by
  apply branch_checked idp10011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-5111761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5115761639/4000000 : ℚ) by norm_num]
  exact coverp10011111111
theorem coverp1001111111 : Covers (-5111761639/8000000 : ℚ) vp1001111111 := join_branches bp10011111110 bp10011111111
private noncomputable def vp10011111101_0 : Blocks := edgeBlocks% "full/vectors/10011111101-V-0000.bin"
noncomputable def vp10011111101 : Blocks := vp10011111101_0
theorem coverp10011111101 : Covers (-5107761639/4000000 : ℚ) vp10011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp10011111100_0 : Blocks := edgeBlocks% "full/vectors/10011111100-V-0000.bin"
noncomputable def vp10011111100 : Blocks := vp10011111100_0
theorem coverp10011111100 : Covers (-5103761639/4000000 : ℚ) vp10011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp1001111110_0 : Blocks := edgeBlocks% "full/vectors/1001111110-V-0000.bin"
private noncomputable def vp1001111110_1 : Blocks := edgeBlocks% "full/vectors/1001111110-V-0001.bin"
noncomputable def vp1001111110 : Blocks := (Blocks.join vp1001111110_0 vp1001111110_1)
private theorem bp10011111100 : Branch 0 (-5103761639/8000000 : ℚ) vp1001111110 := by
  apply branch_left_normalized (c:=vp10011111100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-5103761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5103761639/4000000 : ℚ) by norm_num]
  exact coverp10011111100
private noncomputable def ep10011111101_0 : Blocks := edgeBlocks% "full/vectors/10011111101-E-0000.bin"
private noncomputable def ep10011111101_1 : Blocks := edgeBlocks% "full/vectors/10011111101-E-0001.bin"
noncomputable def ep10011111101 : Blocks := (Blocks.join ep10011111101_0 ep10011111101_1)
private theorem idp10011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001111110.list =
    C ((2:ℤ)^155) * horner X vp10011111101.list + horner X ep10011111101.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011111101 : Branch 1 (-5103761639/8000000 : ℚ) vp1001111110 := by
  apply branch_checked idp10011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-5103761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5107761639/4000000 : ℚ) by norm_num]
  exact coverp10011111101
theorem coverp1001111110 : Covers (-5103761639/8000000 : ℚ) vp1001111110 := join_branches bp10011111100 bp10011111101
private noncomputable def vp100111111_0 : Blocks := edgeBlocks% "full/vectors/100111111-V-0000.bin"
private noncomputable def vp100111111_1 : Blocks := edgeBlocks% "full/vectors/100111111-V-0001.bin"
noncomputable def vp100111111 : Blocks := (Blocks.join vp100111111_0 vp100111111_1)
private theorem bp1001111110 : Branch 0 (-5103761639/16000000 : ℚ) vp100111111 := by
  apply branch_left_normalized (c:=vp1001111110) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-5103761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5103761639/8000000 : ℚ) by norm_num]
  exact coverp1001111110
private noncomputable def ep1001111111_0 : Blocks := edgeBlocks% "full/vectors/1001111111-E-0000.bin"
private noncomputable def ep1001111111_1 : Blocks := edgeBlocks% "full/vectors/1001111111-E-0001.bin"
noncomputable def ep1001111111 : Blocks := (Blocks.join ep1001111111_0 ep1001111111_1)
private theorem idp1001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100111111.list =
    C ((2:ℤ)^289) * horner X vp1001111111.list + horner X ep1001111111.list := by
  exact edge_identity (B := (2:ℤ)^461) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001111111 : Branch 1 (-5103761639/16000000 : ℚ) vp100111111 := by
  apply branch_checked idp1001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-5103761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5111761639/8000000 : ℚ) by norm_num]
  exact coverp1001111111
theorem coverp100111111 : Covers (-5103761639/16000000 : ℚ) vp100111111 := join_branches bp1001111110 bp1001111111
private noncomputable def vp10011111011_0 : Blocks := edgeBlocks% "full/vectors/10011111011-V-0000.bin"
noncomputable def vp10011111011 : Blocks := vp10011111011_0
theorem coverp10011111011 : Covers (-5099761639/4000000 : ℚ) vp10011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp10011111010_0 : Blocks := edgeBlocks% "full/vectors/10011111010-V-0000.bin"
noncomputable def vp10011111010 : Blocks := vp10011111010_0
theorem coverp10011111010 : Covers (-5095761639/4000000 : ℚ) vp10011111010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001111101_0 : Blocks := edgeBlocks% "full/vectors/1001111101-V-0000.bin"
private noncomputable def vp1001111101_1 : Blocks := edgeBlocks% "full/vectors/1001111101-V-0001.bin"
noncomputable def vp1001111101 : Blocks := (Blocks.join vp1001111101_0 vp1001111101_1)
private theorem bp10011111010 : Branch 0 (-5095761639/8000000 : ℚ) vp1001111101 := by
  apply branch_left_normalized (c:=vp10011111010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-5095761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5095761639/4000000 : ℚ) by norm_num]
  exact coverp10011111010
private noncomputable def ep10011111011_0 : Blocks := edgeBlocks% "full/vectors/10011111011-E-0000.bin"
private noncomputable def ep10011111011_1 : Blocks := edgeBlocks% "full/vectors/10011111011-E-0001.bin"
noncomputable def ep10011111011 : Blocks := (Blocks.join ep10011111011_0 ep10011111011_1)
private theorem idp10011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001111101.list =
    C ((2:ℤ)^156) * horner X vp10011111011.list + horner X ep10011111011.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011111011 : Branch 1 (-5095761639/8000000 : ℚ) vp1001111101 := by
  apply branch_checked idp10011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-5095761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5099761639/4000000 : ℚ) by norm_num]
  exact coverp10011111011
theorem coverp1001111101 : Covers (-5095761639/8000000 : ℚ) vp1001111101 := join_branches bp10011111010 bp10011111011
private noncomputable def vp10011111001_0 : Blocks := edgeBlocks% "full/vectors/10011111001-V-0000.bin"
noncomputable def vp10011111001 : Blocks := vp10011111001_0
theorem coverp10011111001 : Covers (-5091761639/4000000 : ℚ) vp10011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp10011111000_0 : Blocks := edgeBlocks% "full/vectors/10011111000-V-0000.bin"
noncomputable def vp10011111000 : Blocks := vp10011111000_0
theorem coverp10011111000 : Covers (-5087761639/4000000 : ℚ) vp10011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001111100_0 : Blocks := edgeBlocks% "full/vectors/1001111100-V-0000.bin"
private noncomputable def vp1001111100_1 : Blocks := edgeBlocks% "full/vectors/1001111100-V-0001.bin"
noncomputable def vp1001111100 : Blocks := (Blocks.join vp1001111100_0 vp1001111100_1)
private theorem bp10011111000 : Branch 0 (-5087761639/8000000 : ℚ) vp1001111100 := by
  apply branch_left_normalized (c:=vp10011111000) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-5087761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5087761639/4000000 : ℚ) by norm_num]
  exact coverp10011111000
private noncomputable def ep10011111001_0 : Blocks := edgeBlocks% "full/vectors/10011111001-E-0000.bin"
private noncomputable def ep10011111001_1 : Blocks := edgeBlocks% "full/vectors/10011111001-E-0001.bin"
noncomputable def ep10011111001 : Blocks := (Blocks.join ep10011111001_0 ep10011111001_1)
private theorem idp10011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001111100.list =
    C ((2:ℤ)^156) * horner X vp10011111001.list + horner X ep10011111001.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011111001 : Branch 1 (-5087761639/8000000 : ℚ) vp1001111100 := by
  apply branch_checked idp10011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-5087761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5091761639/4000000 : ℚ) by norm_num]
  exact coverp10011111001
theorem coverp1001111100 : Covers (-5087761639/8000000 : ℚ) vp1001111100 := join_branches bp10011111000 bp10011111001
private noncomputable def vp100111110_0 : Blocks := edgeBlocks% "full/vectors/100111110-V-0000.bin"
private noncomputable def vp100111110_1 : Blocks := edgeBlocks% "full/vectors/100111110-V-0001.bin"
noncomputable def vp100111110 : Blocks := (Blocks.join vp100111110_0 vp100111110_1)
private theorem bp1001111100 : Branch 0 (-5087761639/16000000 : ℚ) vp100111110 := by
  apply branch_left_normalized (c:=vp1001111100) (k:=0) (m:=132) (by decide +kernel)
  rw [show 2*(-5087761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5087761639/8000000 : ℚ) by norm_num]
  exact coverp1001111100
private noncomputable def ep1001111101_0 : Blocks := edgeBlocks% "full/vectors/1001111101-E-0000.bin"
private noncomputable def ep1001111101_1 : Blocks := edgeBlocks% "full/vectors/1001111101-E-0001.bin"
noncomputable def ep1001111101 : Blocks := (Blocks.join ep1001111101_0 ep1001111101_1)
private theorem idp1001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100111110.list =
    C ((2:ℤ)^289) * horner X vp1001111101.list + horner X ep1001111101.list := by
  exact edge_identity (B := (2:ℤ)^461) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001111101 : Branch 1 (-5087761639/16000000 : ℚ) vp100111110 := by
  apply branch_checked idp1001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-5087761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5095761639/8000000 : ℚ) by norm_num]
  exact coverp1001111101
theorem coverp100111110 : Covers (-5087761639/16000000 : ℚ) vp100111110 := join_branches bp1001111100 bp1001111101
private noncomputable def vp10011111_0 : Blocks := edgeBlocks% "full/vectors/10011111-V-0000.bin"
private noncomputable def vp10011111_1 : Blocks := edgeBlocks% "full/vectors/10011111-V-0001.bin"
private noncomputable def vp10011111_2 : Blocks := edgeBlocks% "full/vectors/10011111-V-0002.bin"
private noncomputable def vp10011111_3 : Blocks := edgeBlocks% "full/vectors/10011111-V-0003.bin"
noncomputable def vp10011111 : Blocks := (Blocks.join (Blocks.join vp10011111_0 vp10011111_1) (Blocks.join vp10011111_2 vp10011111_3))
private theorem bp100111110 : Branch 0 (-5087761639/32000000 : ℚ) vp10011111 := by
  apply branch_left_normalized (c:=vp100111110) (k:=0) (m:=242) (by decide +kernel)
  rw [show 2*(-5087761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5087761639/16000000 : ℚ) by norm_num]
  exact coverp100111110
private noncomputable def ep100111111_0 : Blocks := edgeBlocks% "full/vectors/100111111-E-0000.bin"
private noncomputable def ep100111111_1 : Blocks := edgeBlocks% "full/vectors/100111111-E-0001.bin"
private noncomputable def ep100111111_2 : Blocks := edgeBlocks% "full/vectors/100111111-E-0002.bin"
private noncomputable def ep100111111_3 : Blocks := edgeBlocks% "full/vectors/100111111-E-0003.bin"
noncomputable def ep100111111 : Blocks := (Blocks.join (Blocks.join ep100111111_0 ep100111111_1) (Blocks.join ep100111111_2 ep100111111_3))
private theorem idp100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10011111.list =
    C ((2:ℤ)^554) * horner X vp100111111.list + horner X ep100111111.list := by
  exact edge_identity (B := (2:ℤ)^797) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100111111 : Branch 1 (-5087761639/32000000 : ℚ) vp10011111 := by
  apply branch_checked idp100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-5087761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5103761639/16000000 : ℚ) by norm_num]
  exact coverp100111111
theorem coverp10011111 : Covers (-5087761639/32000000 : ℚ) vp10011111 := join_branches bp100111110 bp100111111
private noncomputable def vp10011110111_0 : Blocks := edgeBlocks% "full/vectors/10011110111-V-0000.bin"
noncomputable def vp10011110111 : Blocks := vp10011110111_0
theorem coverp10011110111 : Covers (-5083761639/4000000 : ℚ) vp10011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp10011110110_0 : Blocks := edgeBlocks% "full/vectors/10011110110-V-0000.bin"
noncomputable def vp10011110110 : Blocks := vp10011110110_0
theorem coverp10011110110 : Covers (-5079761639/4000000 : ℚ) vp10011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001111011_0 : Blocks := edgeBlocks% "full/vectors/1001111011-V-0000.bin"
private noncomputable def vp1001111011_1 : Blocks := edgeBlocks% "full/vectors/1001111011-V-0001.bin"
noncomputable def vp1001111011 : Blocks := (Blocks.join vp1001111011_0 vp1001111011_1)
private theorem bp10011110110 : Branch 0 (-5079761639/8000000 : ℚ) vp1001111011 := by
  apply branch_left_normalized (c:=vp10011110110) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-5079761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5079761639/4000000 : ℚ) by norm_num]
  exact coverp10011110110
private noncomputable def ep10011110111_0 : Blocks := edgeBlocks% "full/vectors/10011110111-E-0000.bin"
private noncomputable def ep10011110111_1 : Blocks := edgeBlocks% "full/vectors/10011110111-E-0001.bin"
noncomputable def ep10011110111 : Blocks := (Blocks.join ep10011110111_0 ep10011110111_1)
private theorem idp10011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001111011.list =
    C ((2:ℤ)^156) * horner X vp10011110111.list + horner X ep10011110111.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011110111 : Branch 1 (-5079761639/8000000 : ℚ) vp1001111011 := by
  apply branch_checked idp10011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-5079761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5083761639/4000000 : ℚ) by norm_num]
  exact coverp10011110111
theorem coverp1001111011 : Covers (-5079761639/8000000 : ℚ) vp1001111011 := join_branches bp10011110110 bp10011110111
private noncomputable def vp10011110101_0 : Blocks := edgeBlocks% "full/vectors/10011110101-V-0000.bin"
noncomputable def vp10011110101 : Blocks := vp10011110101_0
theorem coverp10011110101 : Covers (-5075761639/4000000 : ℚ) vp10011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp10011110100_0 : Blocks := edgeBlocks% "full/vectors/10011110100-V-0000.bin"
noncomputable def vp10011110100 : Blocks := vp10011110100_0
theorem coverp10011110100 : Covers (-5071761639/4000000 : ℚ) vp10011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp1001111010_0 : Blocks := edgeBlocks% "full/vectors/1001111010-V-0000.bin"
private noncomputable def vp1001111010_1 : Blocks := edgeBlocks% "full/vectors/1001111010-V-0001.bin"
noncomputable def vp1001111010 : Blocks := (Blocks.join vp1001111010_0 vp1001111010_1)
private theorem bp10011110100 : Branch 0 (-5071761639/8000000 : ℚ) vp1001111010 := by
  apply branch_left_normalized (c:=vp10011110100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-5071761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5071761639/4000000 : ℚ) by norm_num]
  exact coverp10011110100
private noncomputable def ep10011110101_0 : Blocks := edgeBlocks% "full/vectors/10011110101-E-0000.bin"
private noncomputable def ep10011110101_1 : Blocks := edgeBlocks% "full/vectors/10011110101-E-0001.bin"
noncomputable def ep10011110101 : Blocks := (Blocks.join ep10011110101_0 ep10011110101_1)
private theorem idp10011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001111010.list =
    C ((2:ℤ)^156) * horner X vp10011110101.list + horner X ep10011110101.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011110101 : Branch 1 (-5071761639/8000000 : ℚ) vp1001111010 := by
  apply branch_checked idp10011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-5071761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5075761639/4000000 : ℚ) by norm_num]
  exact coverp10011110101
theorem coverp1001111010 : Covers (-5071761639/8000000 : ℚ) vp1001111010 := join_branches bp10011110100 bp10011110101
private noncomputable def vp100111101_0 : Blocks := edgeBlocks% "full/vectors/100111101-V-0000.bin"
private noncomputable def vp100111101_1 : Blocks := edgeBlocks% "full/vectors/100111101-V-0001.bin"
noncomputable def vp100111101 : Blocks := (Blocks.join vp100111101_0 vp100111101_1)
private theorem bp1001111010 : Branch 0 (-5071761639/16000000 : ℚ) vp100111101 := by
  apply branch_left_normalized (c:=vp1001111010) (k:=0) (m:=132) (by decide +kernel)
  rw [show 2*(-5071761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5071761639/8000000 : ℚ) by norm_num]
  exact coverp1001111010
private noncomputable def ep1001111011_0 : Blocks := edgeBlocks% "full/vectors/1001111011-E-0000.bin"
private noncomputable def ep1001111011_1 : Blocks := edgeBlocks% "full/vectors/1001111011-E-0001.bin"
noncomputable def ep1001111011 : Blocks := (Blocks.join ep1001111011_0 ep1001111011_1)
private theorem idp1001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100111101.list =
    C ((2:ℤ)^290) * horner X vp1001111011.list + horner X ep1001111011.list := by
  exact edge_identity (B := (2:ℤ)^462) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001111011 : Branch 1 (-5071761639/16000000 : ℚ) vp100111101 := by
  apply branch_checked idp1001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-5071761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5079761639/8000000 : ℚ) by norm_num]
  exact coverp1001111011
theorem coverp100111101 : Covers (-5071761639/16000000 : ℚ) vp100111101 := join_branches bp1001111010 bp1001111011
private noncomputable def vp10011110011_0 : Blocks := edgeBlocks% "full/vectors/10011110011-V-0000.bin"
noncomputable def vp10011110011 : Blocks := vp10011110011_0
theorem coverp10011110011 : Covers (-5067761639/4000000 : ℚ) vp10011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp10011110010_0 : Blocks := edgeBlocks% "full/vectors/10011110010-V-0000.bin"
noncomputable def vp10011110010 : Blocks := vp10011110010_0
theorem coverp10011110010 : Covers (-5063761639/4000000 : ℚ) vp10011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001111001_0 : Blocks := edgeBlocks% "full/vectors/1001111001-V-0000.bin"
private noncomputable def vp1001111001_1 : Blocks := edgeBlocks% "full/vectors/1001111001-V-0001.bin"
noncomputable def vp1001111001 : Blocks := (Blocks.join vp1001111001_0 vp1001111001_1)
private theorem bp10011110010 : Branch 0 (-5063761639/8000000 : ℚ) vp1001111001 := by
  apply branch_left_normalized (c:=vp10011110010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-5063761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5063761639/4000000 : ℚ) by norm_num]
  exact coverp10011110010
private noncomputable def ep10011110011_0 : Blocks := edgeBlocks% "full/vectors/10011110011-E-0000.bin"
private noncomputable def ep10011110011_1 : Blocks := edgeBlocks% "full/vectors/10011110011-E-0001.bin"
noncomputable def ep10011110011 : Blocks := (Blocks.join ep10011110011_0 ep10011110011_1)
private theorem idp10011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001111001.list =
    C ((2:ℤ)^156) * horner X vp10011110011.list + horner X ep10011110011.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011110011 : Branch 1 (-5063761639/8000000 : ℚ) vp1001111001 := by
  apply branch_checked idp10011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-5063761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5067761639/4000000 : ℚ) by norm_num]
  exact coverp10011110011
theorem coverp1001111001 : Covers (-5063761639/8000000 : ℚ) vp1001111001 := join_branches bp10011110010 bp10011110011
private noncomputable def vp10011110001_0 : Blocks := edgeBlocks% "full/vectors/10011110001-V-0000.bin"
noncomputable def vp10011110001 : Blocks := vp10011110001_0
theorem coverp10011110001 : Covers (-5059761639/4000000 : ℚ) vp10011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp10011110000_0 : Blocks := edgeBlocks% "full/vectors/10011110000-V-0000.bin"
noncomputable def vp10011110000 : Blocks := vp10011110000_0
theorem coverp10011110000 : Covers (-5055761639/4000000 : ℚ) vp10011110000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001111000_0 : Blocks := edgeBlocks% "full/vectors/1001111000-V-0000.bin"
private noncomputable def vp1001111000_1 : Blocks := edgeBlocks% "full/vectors/1001111000-V-0001.bin"
noncomputable def vp1001111000 : Blocks := (Blocks.join vp1001111000_0 vp1001111000_1)
private theorem bp10011110000 : Branch 0 (-5055761639/8000000 : ℚ) vp1001111000 := by
  apply branch_left_normalized (c:=vp10011110000) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-5055761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5055761639/4000000 : ℚ) by norm_num]
  exact coverp10011110000
private noncomputable def ep10011110001_0 : Blocks := edgeBlocks% "full/vectors/10011110001-E-0000.bin"
private noncomputable def ep10011110001_1 : Blocks := edgeBlocks% "full/vectors/10011110001-E-0001.bin"
noncomputable def ep10011110001 : Blocks := (Blocks.join ep10011110001_0 ep10011110001_1)
private theorem idp10011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001111000.list =
    C ((2:ℤ)^156) * horner X vp10011110001.list + horner X ep10011110001.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011110001 : Branch 1 (-5055761639/8000000 : ℚ) vp1001111000 := by
  apply branch_checked idp10011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-5055761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5059761639/4000000 : ℚ) by norm_num]
  exact coverp10011110001
theorem coverp1001111000 : Covers (-5055761639/8000000 : ℚ) vp1001111000 := join_branches bp10011110000 bp10011110001
private noncomputable def vp100111100_0 : Blocks := edgeBlocks% "full/vectors/100111100-V-0000.bin"
private noncomputable def vp100111100_1 : Blocks := edgeBlocks% "full/vectors/100111100-V-0001.bin"
noncomputable def vp100111100 : Blocks := (Blocks.join vp100111100_0 vp100111100_1)
private theorem bp1001111000 : Branch 0 (-5055761639/16000000 : ℚ) vp100111100 := by
  apply branch_left_normalized (c:=vp1001111000) (k:=0) (m:=132) (by decide +kernel)
  rw [show 2*(-5055761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5055761639/8000000 : ℚ) by norm_num]
  exact coverp1001111000
private noncomputable def ep1001111001_0 : Blocks := edgeBlocks% "full/vectors/1001111001-E-0000.bin"
private noncomputable def ep1001111001_1 : Blocks := edgeBlocks% "full/vectors/1001111001-E-0001.bin"
noncomputable def ep1001111001 : Blocks := (Blocks.join ep1001111001_0 ep1001111001_1)
private theorem idp1001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100111100.list =
    C ((2:ℤ)^289) * horner X vp1001111001.list + horner X ep1001111001.list := by
  exact edge_identity (B := (2:ℤ)^462) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001111001 : Branch 1 (-5055761639/16000000 : ℚ) vp100111100 := by
  apply branch_checked idp1001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-5055761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5063761639/8000000 : ℚ) by norm_num]
  exact coverp1001111001
theorem coverp100111100 : Covers (-5055761639/16000000 : ℚ) vp100111100 := join_branches bp1001111000 bp1001111001
private noncomputable def vp10011110_0 : Blocks := edgeBlocks% "full/vectors/10011110-V-0000.bin"
private noncomputable def vp10011110_1 : Blocks := edgeBlocks% "full/vectors/10011110-V-0001.bin"
private noncomputable def vp10011110_2 : Blocks := edgeBlocks% "full/vectors/10011110-V-0002.bin"
private noncomputable def vp10011110_3 : Blocks := edgeBlocks% "full/vectors/10011110-V-0003.bin"
noncomputable def vp10011110 : Blocks := (Blocks.join (Blocks.join vp10011110_0 vp10011110_1) (Blocks.join vp10011110_2 vp10011110_3))
private theorem bp100111100 : Branch 0 (-5055761639/32000000 : ℚ) vp10011110 := by
  apply branch_left_normalized (c:=vp100111100) (k:=0) (m:=242) (by decide +kernel)
  rw [show 2*(-5055761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5055761639/16000000 : ℚ) by norm_num]
  exact coverp100111100
private noncomputable def ep100111101_0 : Blocks := edgeBlocks% "full/vectors/100111101-E-0000.bin"
private noncomputable def ep100111101_1 : Blocks := edgeBlocks% "full/vectors/100111101-E-0001.bin"
private noncomputable def ep100111101_2 : Blocks := edgeBlocks% "full/vectors/100111101-E-0002.bin"
private noncomputable def ep100111101_3 : Blocks := edgeBlocks% "full/vectors/100111101-E-0003.bin"
noncomputable def ep100111101 : Blocks := (Blocks.join (Blocks.join ep100111101_0 ep100111101_1) (Blocks.join ep100111101_2 ep100111101_3))
private theorem idp100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10011110.list =
    C ((2:ℤ)^555) * horner X vp100111101.list + horner X ep100111101.list := by
  exact edge_identity (B := (2:ℤ)^799) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100111101 : Branch 1 (-5055761639/32000000 : ℚ) vp10011110 := by
  apply branch_checked idp100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-5055761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5071761639/16000000 : ℚ) by norm_num]
  exact coverp100111101
theorem coverp10011110 : Covers (-5055761639/32000000 : ℚ) vp10011110 := join_branches bp100111100 bp100111101
private noncomputable def vp1001111_0 : Blocks := edgeBlocks% "full/vectors/1001111-V-0000.bin"
private noncomputable def vp1001111_1 : Blocks := edgeBlocks% "full/vectors/1001111-V-0001.bin"
private noncomputable def vp1001111_2 : Blocks := edgeBlocks% "full/vectors/1001111-V-0002.bin"
private noncomputable def vp1001111_3 : Blocks := edgeBlocks% "full/vectors/1001111-V-0003.bin"
private noncomputable def vp1001111_4 : Blocks := edgeBlocks% "full/vectors/1001111-V-0004.bin"
private noncomputable def vp1001111_5 : Blocks := edgeBlocks% "full/vectors/1001111-V-0005.bin"
private noncomputable def vp1001111_6 : Blocks := edgeBlocks% "full/vectors/1001111-V-0006.bin"
private noncomputable def vp1001111_7 : Blocks := edgeBlocks% "full/vectors/1001111-V-0007.bin"
noncomputable def vp1001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1001111_0 vp1001111_1) (Blocks.join vp1001111_2 vp1001111_3)) (Blocks.join (Blocks.join vp1001111_4 vp1001111_5) (Blocks.join vp1001111_6 vp1001111_7)))
private theorem bp10011110 : Branch 0 (-5055761639/64000000 : ℚ) vp1001111 := by
  apply branch_left_normalized (c:=vp10011110) (k:=0) (m:=462) (by decide +kernel)
  rw [show 2*(-5055761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5055761639/32000000 : ℚ) by norm_num]
  exact coverp10011110
private noncomputable def ep10011111_0 : Blocks := edgeBlocks% "full/vectors/10011111-E-0000.bin"
private noncomputable def ep10011111_1 : Blocks := edgeBlocks% "full/vectors/10011111-E-0001.bin"
private noncomputable def ep10011111_2 : Blocks := edgeBlocks% "full/vectors/10011111-E-0002.bin"
private noncomputable def ep10011111_3 : Blocks := edgeBlocks% "full/vectors/10011111-E-0003.bin"
private noncomputable def ep10011111_4 : Blocks := edgeBlocks% "full/vectors/10011111-E-0004.bin"
private noncomputable def ep10011111_5 : Blocks := edgeBlocks% "full/vectors/10011111-E-0005.bin"
private noncomputable def ep10011111_6 : Blocks := edgeBlocks% "full/vectors/10011111-E-0006.bin"
private noncomputable def ep10011111_7 : Blocks := edgeBlocks% "full/vectors/10011111-E-0007.bin"
noncomputable def ep10011111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10011111_0 ep10011111_1) (Blocks.join ep10011111_2 ep10011111_3)) (Blocks.join (Blocks.join ep10011111_4 ep10011111_5) (Blocks.join ep10011111_6 ep10011111_7)))
private theorem idp10011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001111.list =
    C ((2:ℤ)^1082) * horner X vp10011111.list + horner X ep10011111.list := by
  exact edge_identity (B := (2:ℤ)^1466) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011111 : Branch 1 (-5055761639/64000000 : ℚ) vp1001111 := by
  apply branch_checked idp10011111 (by positivity) (by decide +kernel)
  rw [show 2*(-5055761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5087761639/32000000 : ℚ) by norm_num]
  exact coverp10011111
theorem coverp1001111 : Covers (-5055761639/64000000 : ℚ) vp1001111 := join_branches bp10011110 bp10011111
private noncomputable def vp10011101111_0 : Blocks := edgeBlocks% "full/vectors/10011101111-V-0000.bin"
noncomputable def vp10011101111 : Blocks := vp10011101111_0
theorem coverp10011101111 : Covers (-5051761639/4000000 : ℚ) vp10011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp10011101110_0 : Blocks := edgeBlocks% "full/vectors/10011101110-V-0000.bin"
noncomputable def vp10011101110 : Blocks := vp10011101110_0
theorem coverp10011101110 : Covers (-5047761639/4000000 : ℚ) vp10011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001110111_0 : Blocks := edgeBlocks% "full/vectors/1001110111-V-0000.bin"
private noncomputable def vp1001110111_1 : Blocks := edgeBlocks% "full/vectors/1001110111-V-0001.bin"
noncomputable def vp1001110111 : Blocks := (Blocks.join vp1001110111_0 vp1001110111_1)
private theorem bp10011101110 : Branch 0 (-5047761639/8000000 : ℚ) vp1001110111 := by
  apply branch_left_normalized (c:=vp10011101110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5047761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5047761639/4000000 : ℚ) by norm_num]
  exact coverp10011101110
private noncomputable def ep10011101111_0 : Blocks := edgeBlocks% "full/vectors/10011101111-E-0000.bin"
private noncomputable def ep10011101111_1 : Blocks := edgeBlocks% "full/vectors/10011101111-E-0001.bin"
noncomputable def ep10011101111 : Blocks := (Blocks.join ep10011101111_0 ep10011101111_1)
private theorem idp10011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001110111.list =
    C ((2:ℤ)^154) * horner X vp10011101111.list + horner X ep10011101111.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011101111 : Branch 1 (-5047761639/8000000 : ℚ) vp1001110111 := by
  apply branch_checked idp10011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-5047761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5051761639/4000000 : ℚ) by norm_num]
  exact coverp10011101111
theorem coverp1001110111 : Covers (-5047761639/8000000 : ℚ) vp1001110111 := join_branches bp10011101110 bp10011101111
private noncomputable def vp1001110110_0 : Blocks := edgeBlocks% "full/vectors/1001110110-V-0000.bin"
private noncomputable def vp1001110110_1 : Blocks := edgeBlocks% "full/vectors/1001110110-V-0001.bin"
noncomputable def vp1001110110 : Blocks := (Blocks.join vp1001110110_0 vp1001110110_1)
theorem coverp1001110110 : Covers (-5039761639/8000000 : ℚ) vp1001110110 := cover_leaf (by decide +kernel)
private noncomputable def vp100111011_0 : Blocks := edgeBlocks% "full/vectors/100111011-V-0000.bin"
private noncomputable def vp100111011_1 : Blocks := edgeBlocks% "full/vectors/100111011-V-0001.bin"
noncomputable def vp100111011 : Blocks := (Blocks.join vp100111011_0 vp100111011_1)
private theorem bp1001110110 : Branch 0 (-5039761639/16000000 : ℚ) vp100111011 := by
  apply branch_left_normalized (c:=vp1001110110) (k:=0) (m:=130) (by decide +kernel)
  rw [show 2*(-5039761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5039761639/8000000 : ℚ) by norm_num]
  exact coverp1001110110
private noncomputable def ep1001110111_0 : Blocks := edgeBlocks% "full/vectors/1001110111-E-0000.bin"
private noncomputable def ep1001110111_1 : Blocks := edgeBlocks% "full/vectors/1001110111-E-0001.bin"
noncomputable def ep1001110111 : Blocks := (Blocks.join ep1001110111_0 ep1001110111_1)
private theorem idp1001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100111011.list =
    C ((2:ℤ)^287) * horner X vp1001110111.list + horner X ep1001110111.list := by
  exact edge_identity (B := (2:ℤ)^457) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001110111 : Branch 1 (-5039761639/16000000 : ℚ) vp100111011 := by
  apply branch_checked idp1001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-5039761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5047761639/8000000 : ℚ) by norm_num]
  exact coverp1001110111
theorem coverp100111011 : Covers (-5039761639/16000000 : ℚ) vp100111011 := join_branches bp1001110110 bp1001110111
private noncomputable def vp1001110101_0 : Blocks := edgeBlocks% "full/vectors/1001110101-V-0000.bin"
private noncomputable def vp1001110101_1 : Blocks := edgeBlocks% "full/vectors/1001110101-V-0001.bin"
noncomputable def vp1001110101 : Blocks := (Blocks.join vp1001110101_0 vp1001110101_1)
theorem coverp1001110101 : Covers (-5031761639/8000000 : ℚ) vp1001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp1001110100_0 : Blocks := edgeBlocks% "full/vectors/1001110100-V-0000.bin"
private noncomputable def vp1001110100_1 : Blocks := edgeBlocks% "full/vectors/1001110100-V-0001.bin"
noncomputable def vp1001110100 : Blocks := (Blocks.join vp1001110100_0 vp1001110100_1)
theorem coverp1001110100 : Covers (-5023761639/8000000 : ℚ) vp1001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp100111010_0 : Blocks := edgeBlocks% "full/vectors/100111010-V-0000.bin"
private noncomputable def vp100111010_1 : Blocks := edgeBlocks% "full/vectors/100111010-V-0001.bin"
noncomputable def vp100111010 : Blocks := (Blocks.join vp100111010_0 vp100111010_1)
private theorem bp1001110100 : Branch 0 (-5023761639/16000000 : ℚ) vp100111010 := by
  apply branch_left_normalized (c:=vp1001110100) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-5023761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5023761639/8000000 : ℚ) by norm_num]
  exact coverp1001110100
private noncomputable def ep1001110101_0 : Blocks := edgeBlocks% "full/vectors/1001110101-E-0000.bin"
private noncomputable def ep1001110101_1 : Blocks := edgeBlocks% "full/vectors/1001110101-E-0001.bin"
noncomputable def ep1001110101 : Blocks := (Blocks.join ep1001110101_0 ep1001110101_1)
private theorem idp1001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100111010.list =
    C ((2:ℤ)^286) * horner X vp1001110101.list + horner X ep1001110101.list := by
  exact edge_identity (B := (2:ℤ)^454) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001110101 : Branch 1 (-5023761639/16000000 : ℚ) vp100111010 := by
  apply branch_checked idp1001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-5023761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5031761639/8000000 : ℚ) by norm_num]
  exact coverp1001110101
theorem coverp100111010 : Covers (-5023761639/16000000 : ℚ) vp100111010 := join_branches bp1001110100 bp1001110101
private noncomputable def vp10011101_0 : Blocks := edgeBlocks% "full/vectors/10011101-V-0000.bin"
private noncomputable def vp10011101_1 : Blocks := edgeBlocks% "full/vectors/10011101-V-0001.bin"
private noncomputable def vp10011101_2 : Blocks := edgeBlocks% "full/vectors/10011101-V-0002.bin"
private noncomputable def vp10011101_3 : Blocks := edgeBlocks% "full/vectors/10011101-V-0003.bin"
noncomputable def vp10011101 : Blocks := (Blocks.join (Blocks.join vp10011101_0 vp10011101_1) (Blocks.join vp10011101_2 vp10011101_3))
private theorem bp100111010 : Branch 0 (-5023761639/32000000 : ℚ) vp10011101 := by
  apply branch_left_normalized (c:=vp100111010) (k:=0) (m:=240) (by decide +kernel)
  rw [show 2*(-5023761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5023761639/16000000 : ℚ) by norm_num]
  exact coverp100111010
private noncomputable def ep100111011_0 : Blocks := edgeBlocks% "full/vectors/100111011-E-0000.bin"
private noncomputable def ep100111011_1 : Blocks := edgeBlocks% "full/vectors/100111011-E-0001.bin"
private noncomputable def ep100111011_2 : Blocks := edgeBlocks% "full/vectors/100111011-E-0002.bin"
private noncomputable def ep100111011_3 : Blocks := edgeBlocks% "full/vectors/100111011-E-0003.bin"
noncomputable def ep100111011 : Blocks := (Blocks.join (Blocks.join ep100111011_0 ep100111011_1) (Blocks.join ep100111011_2 ep100111011_3))
private theorem idp100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10011101.list =
    C ((2:ℤ)^551) * horner X vp100111011.list + horner X ep100111011.list := by
  exact edge_identity (B := (2:ℤ)^792) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100111011 : Branch 1 (-5023761639/32000000 : ℚ) vp10011101 := by
  apply branch_checked idp100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-5023761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5039761639/16000000 : ℚ) by norm_num]
  exact coverp100111011
theorem coverp10011101 : Covers (-5023761639/32000000 : ℚ) vp10011101 := join_branches bp100111010 bp100111011
private noncomputable def vp1001110011_0 : Blocks := edgeBlocks% "full/vectors/1001110011-V-0000.bin"
private noncomputable def vp1001110011_1 : Blocks := edgeBlocks% "full/vectors/1001110011-V-0001.bin"
noncomputable def vp1001110011 : Blocks := (Blocks.join vp1001110011_0 vp1001110011_1)
theorem coverp1001110011 : Covers (-5015761639/8000000 : ℚ) vp1001110011 := cover_leaf (by decide +kernel)
private noncomputable def vp1001110010_0 : Blocks := edgeBlocks% "full/vectors/1001110010-V-0000.bin"
private noncomputable def vp1001110010_1 : Blocks := edgeBlocks% "full/vectors/1001110010-V-0001.bin"
noncomputable def vp1001110010 : Blocks := (Blocks.join vp1001110010_0 vp1001110010_1)
theorem coverp1001110010 : Covers (-5007761639/8000000 : ℚ) vp1001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp100111001_0 : Blocks := edgeBlocks% "full/vectors/100111001-V-0000.bin"
private noncomputable def vp100111001_1 : Blocks := edgeBlocks% "full/vectors/100111001-V-0001.bin"
noncomputable def vp100111001 : Blocks := (Blocks.join vp100111001_0 vp100111001_1)
private theorem bp1001110010 : Branch 0 (-5007761639/16000000 : ℚ) vp100111001 := by
  apply branch_left_normalized (c:=vp1001110010) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-5007761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5007761639/8000000 : ℚ) by norm_num]
  exact coverp1001110010
private noncomputable def ep1001110011_0 : Blocks := edgeBlocks% "full/vectors/1001110011-E-0000.bin"
private noncomputable def ep1001110011_1 : Blocks := edgeBlocks% "full/vectors/1001110011-E-0001.bin"
noncomputable def ep1001110011 : Blocks := (Blocks.join ep1001110011_0 ep1001110011_1)
private theorem idp1001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100111001.list =
    C ((2:ℤ)^288) * horner X vp1001110011.list + horner X ep1001110011.list := by
  exact edge_identity (B := (2:ℤ)^455) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001110011 : Branch 1 (-5007761639/16000000 : ℚ) vp100111001 := by
  apply branch_checked idp1001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-5007761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5015761639/8000000 : ℚ) by norm_num]
  exact coverp1001110011
theorem coverp100111001 : Covers (-5007761639/16000000 : ℚ) vp100111001 := join_branches bp1001110010 bp1001110011
private noncomputable def vp1001110001_0 : Blocks := edgeBlocks% "full/vectors/1001110001-V-0000.bin"
private noncomputable def vp1001110001_1 : Blocks := edgeBlocks% "full/vectors/1001110001-V-0001.bin"
noncomputable def vp1001110001 : Blocks := (Blocks.join vp1001110001_0 vp1001110001_1)
theorem coverp1001110001 : Covers (-4999761639/8000000 : ℚ) vp1001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp1001110000_0 : Blocks := edgeBlocks% "full/vectors/1001110000-V-0000.bin"
private noncomputable def vp1001110000_1 : Blocks := edgeBlocks% "full/vectors/1001110000-V-0001.bin"
noncomputable def vp1001110000 : Blocks := (Blocks.join vp1001110000_0 vp1001110000_1)
theorem coverp1001110000 : Covers (-4991761639/8000000 : ℚ) vp1001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp100111000_0 : Blocks := edgeBlocks% "full/vectors/100111000-V-0000.bin"
private noncomputable def vp100111000_1 : Blocks := edgeBlocks% "full/vectors/100111000-V-0001.bin"
noncomputable def vp100111000 : Blocks := (Blocks.join vp100111000_0 vp100111000_1)
private theorem bp1001110000 : Branch 0 (-4991761639/16000000 : ℚ) vp100111000 := by
  apply branch_left_normalized (c:=vp1001110000) (k:=0) (m:=130) (by decide +kernel)
  rw [show 2*(-4991761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4991761639/8000000 : ℚ) by norm_num]
  exact coverp1001110000
private noncomputable def ep1001110001_0 : Blocks := edgeBlocks% "full/vectors/1001110001-E-0000.bin"
private noncomputable def ep1001110001_1 : Blocks := edgeBlocks% "full/vectors/1001110001-E-0001.bin"
noncomputable def ep1001110001 : Blocks := (Blocks.join ep1001110001_0 ep1001110001_1)
private theorem idp1001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100111000.list =
    C ((2:ℤ)^290) * horner X vp1001110001.list + horner X ep1001110001.list := by
  exact edge_identity (B := (2:ℤ)^458) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001110001 : Branch 1 (-4991761639/16000000 : ℚ) vp100111000 := by
  apply branch_checked idp1001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-4991761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4999761639/8000000 : ℚ) by norm_num]
  exact coverp1001110001
theorem coverp100111000 : Covers (-4991761639/16000000 : ℚ) vp100111000 := join_branches bp1001110000 bp1001110001
private noncomputable def vp10011100_0 : Blocks := edgeBlocks% "full/vectors/10011100-V-0000.bin"
private noncomputable def vp10011100_1 : Blocks := edgeBlocks% "full/vectors/10011100-V-0001.bin"
private noncomputable def vp10011100_2 : Blocks := edgeBlocks% "full/vectors/10011100-V-0002.bin"
private noncomputable def vp10011100_3 : Blocks := edgeBlocks% "full/vectors/10011100-V-0003.bin"
noncomputable def vp10011100 : Blocks := (Blocks.join (Blocks.join vp10011100_0 vp10011100_1) (Blocks.join vp10011100_2 vp10011100_3))
private theorem bp100111000 : Branch 0 (-4991761639/32000000 : ℚ) vp10011100 := by
  apply branch_left_normalized (c:=vp100111000) (k:=0) (m:=242) (by decide +kernel)
  rw [show 2*(-4991761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4991761639/16000000 : ℚ) by norm_num]
  exact coverp100111000
private noncomputable def ep100111001_0 : Blocks := edgeBlocks% "full/vectors/100111001-E-0000.bin"
private noncomputable def ep100111001_1 : Blocks := edgeBlocks% "full/vectors/100111001-E-0001.bin"
private noncomputable def ep100111001_2 : Blocks := edgeBlocks% "full/vectors/100111001-E-0002.bin"
private noncomputable def ep100111001_3 : Blocks := edgeBlocks% "full/vectors/100111001-E-0003.bin"
noncomputable def ep100111001 : Blocks := (Blocks.join (Blocks.join ep100111001_0 ep100111001_1) (Blocks.join ep100111001_2 ep100111001_3))
private theorem idp100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10011100.list =
    C ((2:ℤ)^557) * horner X vp100111001.list + horner X ep100111001.list := by
  exact edge_identity (B := (2:ℤ)^796) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100111001 : Branch 1 (-4991761639/32000000 : ℚ) vp10011100 := by
  apply branch_checked idp100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-4991761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5007761639/16000000 : ℚ) by norm_num]
  exact coverp100111001
theorem coverp10011100 : Covers (-4991761639/32000000 : ℚ) vp10011100 := join_branches bp100111000 bp100111001
private noncomputable def vp1001110_0 : Blocks := edgeBlocks% "full/vectors/1001110-V-0000.bin"
private noncomputable def vp1001110_1 : Blocks := edgeBlocks% "full/vectors/1001110-V-0001.bin"
private noncomputable def vp1001110_2 : Blocks := edgeBlocks% "full/vectors/1001110-V-0002.bin"
private noncomputable def vp1001110_3 : Blocks := edgeBlocks% "full/vectors/1001110-V-0003.bin"
private noncomputable def vp1001110_4 : Blocks := edgeBlocks% "full/vectors/1001110-V-0004.bin"
private noncomputable def vp1001110_5 : Blocks := edgeBlocks% "full/vectors/1001110-V-0005.bin"
private noncomputable def vp1001110_6 : Blocks := edgeBlocks% "full/vectors/1001110-V-0006.bin"
private noncomputable def vp1001110_7 : Blocks := edgeBlocks% "full/vectors/1001110-V-0007.bin"
noncomputable def vp1001110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1001110_0 vp1001110_1) (Blocks.join vp1001110_2 vp1001110_3)) (Blocks.join (Blocks.join vp1001110_4 vp1001110_5) (Blocks.join vp1001110_6 vp1001110_7)))
private theorem bp10011100 : Branch 0 (-4991761639/64000000 : ℚ) vp1001110 := by
  apply branch_left_normalized (c:=vp10011100) (k:=0) (m:=462) (by decide +kernel)
  rw [show 2*(-4991761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4991761639/32000000 : ℚ) by norm_num]
  exact coverp10011100
private noncomputable def ep10011101_0 : Blocks := edgeBlocks% "full/vectors/10011101-E-0000.bin"
private noncomputable def ep10011101_1 : Blocks := edgeBlocks% "full/vectors/10011101-E-0001.bin"
private noncomputable def ep10011101_2 : Blocks := edgeBlocks% "full/vectors/10011101-E-0002.bin"
private noncomputable def ep10011101_3 : Blocks := edgeBlocks% "full/vectors/10011101-E-0003.bin"
private noncomputable def ep10011101_4 : Blocks := edgeBlocks% "full/vectors/10011101-E-0004.bin"
private noncomputable def ep10011101_5 : Blocks := edgeBlocks% "full/vectors/10011101-E-0005.bin"
private noncomputable def ep10011101_6 : Blocks := edgeBlocks% "full/vectors/10011101-E-0006.bin"
private noncomputable def ep10011101_7 : Blocks := edgeBlocks% "full/vectors/10011101-E-0007.bin"
noncomputable def ep10011101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10011101_0 ep10011101_1) (Blocks.join ep10011101_2 ep10011101_3)) (Blocks.join (Blocks.join ep10011101_4 ep10011101_5) (Blocks.join ep10011101_6 ep10011101_7)))
private theorem idp10011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001110.list =
    C ((2:ℤ)^1085) * horner X vp10011101.list + horner X ep10011101.list := by
  exact edge_identity (B := (2:ℤ)^1467) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011101 : Branch 1 (-4991761639/64000000 : ℚ) vp1001110 := by
  apply branch_checked idp10011101 (by positivity) (by decide +kernel)
  rw [show 2*(-4991761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5023761639/32000000 : ℚ) by norm_num]
  exact coverp10011101
theorem coverp1001110 : Covers (-4991761639/64000000 : ℚ) vp1001110 := join_branches bp10011100 bp10011101
private noncomputable def vp100111_0 : Blocks := edgeBlocks% "full/vectors/100111-V-0000.bin"
private noncomputable def vp100111_1 : Blocks := edgeBlocks% "full/vectors/100111-V-0001.bin"
private noncomputable def vp100111_2 : Blocks := edgeBlocks% "full/vectors/100111-V-0002.bin"
private noncomputable def vp100111_3 : Blocks := edgeBlocks% "full/vectors/100111-V-0003.bin"
private noncomputable def vp100111_4 : Blocks := edgeBlocks% "full/vectors/100111-V-0004.bin"
private noncomputable def vp100111_5 : Blocks := edgeBlocks% "full/vectors/100111-V-0005.bin"
private noncomputable def vp100111_6 : Blocks := edgeBlocks% "full/vectors/100111-V-0006.bin"
private noncomputable def vp100111_7 : Blocks := edgeBlocks% "full/vectors/100111-V-0007.bin"
private noncomputable def vp100111_8 : Blocks := edgeBlocks% "full/vectors/100111-V-0008.bin"
private noncomputable def vp100111_9 : Blocks := edgeBlocks% "full/vectors/100111-V-0009.bin"
private noncomputable def vp100111_10 : Blocks := edgeBlocks% "full/vectors/100111-V-0010.bin"
private noncomputable def vp100111_11 : Blocks := edgeBlocks% "full/vectors/100111-V-0011.bin"
private noncomputable def vp100111_12 : Blocks := edgeBlocks% "full/vectors/100111-V-0012.bin"
private noncomputable def vp100111_13 : Blocks := edgeBlocks% "full/vectors/100111-V-0013.bin"
noncomputable def vp100111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp100111_0 (Blocks.join vp100111_1 vp100111_2)) (Blocks.join (Blocks.join vp100111_3 vp100111_4) (Blocks.join vp100111_5 vp100111_6))) (Blocks.join (Blocks.join vp100111_7 (Blocks.join vp100111_8 vp100111_9)) (Blocks.join (Blocks.join vp100111_10 vp100111_11) (Blocks.join vp100111_12 vp100111_13))))
private theorem bp1001110 : Branch 0 (-4991761639/128000000 : ℚ) vp100111 := by
  apply branch_left_normalized (c:=vp1001110) (k:=0) (m:=898) (by decide +kernel)
  rw [show 2*(-4991761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-4991761639/64000000 : ℚ) by norm_num]
  exact coverp1001110
private noncomputable def ep1001111_0 : Blocks := edgeBlocks% "full/vectors/1001111-E-0000.bin"
private noncomputable def ep1001111_1 : Blocks := edgeBlocks% "full/vectors/1001111-E-0001.bin"
private noncomputable def ep1001111_2 : Blocks := edgeBlocks% "full/vectors/1001111-E-0002.bin"
private noncomputable def ep1001111_3 : Blocks := edgeBlocks% "full/vectors/1001111-E-0003.bin"
private noncomputable def ep1001111_4 : Blocks := edgeBlocks% "full/vectors/1001111-E-0004.bin"
private noncomputable def ep1001111_5 : Blocks := edgeBlocks% "full/vectors/1001111-E-0005.bin"
private noncomputable def ep1001111_6 : Blocks := edgeBlocks% "full/vectors/1001111-E-0006.bin"
private noncomputable def ep1001111_7 : Blocks := edgeBlocks% "full/vectors/1001111-E-0007.bin"
private noncomputable def ep1001111_8 : Blocks := edgeBlocks% "full/vectors/1001111-E-0008.bin"
private noncomputable def ep1001111_9 : Blocks := edgeBlocks% "full/vectors/1001111-E-0009.bin"
private noncomputable def ep1001111_10 : Blocks := edgeBlocks% "full/vectors/1001111-E-0010.bin"
private noncomputable def ep1001111_11 : Blocks := edgeBlocks% "full/vectors/1001111-E-0011.bin"
private noncomputable def ep1001111_12 : Blocks := edgeBlocks% "full/vectors/1001111-E-0012.bin"
private noncomputable def ep1001111_13 : Blocks := edgeBlocks% "full/vectors/1001111-E-0013.bin"
noncomputable def ep1001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1001111_0 (Blocks.join ep1001111_1 ep1001111_2)) (Blocks.join (Blocks.join ep1001111_3 ep1001111_4) (Blocks.join ep1001111_5 ep1001111_6))) (Blocks.join (Blocks.join ep1001111_7 (Blocks.join ep1001111_8 ep1001111_9)) (Blocks.join (Blocks.join ep1001111_10 ep1001111_11) (Blocks.join ep1001111_12 ep1001111_13))))
private theorem idp1001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100111.list =
    C ((2:ℤ)^2119) * horner X vp1001111.list + horner X ep1001111.list := by
  exact edge_identity (B := (2:ℤ)^2788) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001111 : Branch 1 (-4991761639/128000000 : ℚ) vp100111 := by
  apply branch_checked idp1001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4991761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-5055761639/64000000 : ℚ) by norm_num]
  exact coverp1001111
theorem coverp100111 : Covers (-4991761639/128000000 : ℚ) vp100111 := join_branches bp1001110 bp1001111
private noncomputable def vp1001101111_0 : Blocks := edgeBlocks% "full/vectors/1001101111-V-0000.bin"
private noncomputable def vp1001101111_1 : Blocks := edgeBlocks% "full/vectors/1001101111-V-0001.bin"
noncomputable def vp1001101111 : Blocks := (Blocks.join vp1001101111_0 vp1001101111_1)
theorem coverp1001101111 : Covers (-4983761639/8000000 : ℚ) vp1001101111 := cover_leaf (by decide +kernel)
private noncomputable def vp1001101110_0 : Blocks := edgeBlocks% "full/vectors/1001101110-V-0000.bin"
private noncomputable def vp1001101110_1 : Blocks := edgeBlocks% "full/vectors/1001101110-V-0001.bin"
noncomputable def vp1001101110 : Blocks := (Blocks.join vp1001101110_0 vp1001101110_1)
theorem coverp1001101110 : Covers (-4975761639/8000000 : ℚ) vp1001101110 := cover_leaf (by decide +kernel)
private noncomputable def vp100110111_0 : Blocks := edgeBlocks% "full/vectors/100110111-V-0000.bin"
private noncomputable def vp100110111_1 : Blocks := edgeBlocks% "full/vectors/100110111-V-0001.bin"
noncomputable def vp100110111 : Blocks := (Blocks.join vp100110111_0 vp100110111_1)
private theorem bp1001101110 : Branch 0 (-4975761639/16000000 : ℚ) vp100110111 := by
  apply branch_left_normalized (c:=vp1001101110) (k:=0) (m:=132) (by decide +kernel)
  rw [show 2*(-4975761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4975761639/8000000 : ℚ) by norm_num]
  exact coverp1001101110
private noncomputable def ep1001101111_0 : Blocks := edgeBlocks% "full/vectors/1001101111-E-0000.bin"
private noncomputable def ep1001101111_1 : Blocks := edgeBlocks% "full/vectors/1001101111-E-0001.bin"
noncomputable def ep1001101111 : Blocks := (Blocks.join ep1001101111_0 ep1001101111_1)
private theorem idp1001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100110111.list =
    C ((2:ℤ)^293) * horner X vp1001101111.list + horner X ep1001101111.list := by
  exact edge_identity (B := (2:ℤ)^464) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001101111 : Branch 1 (-4975761639/16000000 : ℚ) vp100110111 := by
  apply branch_checked idp1001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-4975761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4983761639/8000000 : ℚ) by norm_num]
  exact coverp1001101111
theorem coverp100110111 : Covers (-4975761639/16000000 : ℚ) vp100110111 := join_branches bp1001101110 bp1001101111
private noncomputable def vp10011011011_0 : Blocks := edgeBlocks% "full/vectors/10011011011-V-0000.bin"
noncomputable def vp10011011011 : Blocks := vp10011011011_0
theorem coverp10011011011 : Covers (-4971761639/4000000 : ℚ) vp10011011011 := cover_leaf (by decide +kernel)
private noncomputable def vp10011011010_0 : Blocks := edgeBlocks% "full/vectors/10011011010-V-0000.bin"
noncomputable def vp10011011010 : Blocks := vp10011011010_0
theorem coverp10011011010 : Covers (-4967761639/4000000 : ℚ) vp10011011010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001101101_0 : Blocks := edgeBlocks% "full/vectors/1001101101-V-0000.bin"
private noncomputable def vp1001101101_1 : Blocks := edgeBlocks% "full/vectors/1001101101-V-0001.bin"
noncomputable def vp1001101101 : Blocks := (Blocks.join vp1001101101_0 vp1001101101_1)
private theorem bp10011011010 : Branch 0 (-4967761639/8000000 : ℚ) vp1001101101 := by
  apply branch_left_normalized (c:=vp10011011010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-4967761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4967761639/4000000 : ℚ) by norm_num]
  exact coverp10011011010
private noncomputable def ep10011011011_0 : Blocks := edgeBlocks% "full/vectors/10011011011-E-0000.bin"
private noncomputable def ep10011011011_1 : Blocks := edgeBlocks% "full/vectors/10011011011-E-0001.bin"
noncomputable def ep10011011011 : Blocks := (Blocks.join ep10011011011_0 ep10011011011_1)
private theorem idp10011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001101101.list =
    C ((2:ℤ)^157) * horner X vp10011011011.list + horner X ep10011011011.list := by
  exact edge_identity (B := (2:ℤ)^295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011011011 : Branch 1 (-4967761639/8000000 : ℚ) vp1001101101 := by
  apply branch_checked idp10011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-4967761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4971761639/4000000 : ℚ) by norm_num]
  exact coverp10011011011
theorem coverp1001101101 : Covers (-4967761639/8000000 : ℚ) vp1001101101 := join_branches bp10011011010 bp10011011011
private noncomputable def vp10011011001_0 : Blocks := edgeBlocks% "full/vectors/10011011001-V-0000.bin"
noncomputable def vp10011011001 : Blocks := vp10011011001_0
theorem coverp10011011001 : Covers (-4963761639/4000000 : ℚ) vp10011011001 := cover_leaf (by decide +kernel)
private noncomputable def vp10011011000_0 : Blocks := edgeBlocks% "full/vectors/10011011000-V-0000.bin"
noncomputable def vp10011011000 : Blocks := vp10011011000_0
theorem coverp10011011000 : Covers (-4959761639/4000000 : ℚ) vp10011011000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001101100_0 : Blocks := edgeBlocks% "full/vectors/1001101100-V-0000.bin"
private noncomputable def vp1001101100_1 : Blocks := edgeBlocks% "full/vectors/1001101100-V-0001.bin"
noncomputable def vp1001101100 : Blocks := (Blocks.join vp1001101100_0 vp1001101100_1)
private theorem bp10011011000 : Branch 0 (-4959761639/8000000 : ℚ) vp1001101100 := by
  apply branch_left_normalized (c:=vp10011011000) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-4959761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4959761639/4000000 : ℚ) by norm_num]
  exact coverp10011011000
private noncomputable def ep10011011001_0 : Blocks := edgeBlocks% "full/vectors/10011011001-E-0000.bin"
private noncomputable def ep10011011001_1 : Blocks := edgeBlocks% "full/vectors/10011011001-E-0001.bin"
noncomputable def ep10011011001 : Blocks := (Blocks.join ep10011011001_0 ep10011011001_1)
private theorem idp10011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001101100.list =
    C ((2:ℤ)^157) * horner X vp10011011001.list + horner X ep10011011001.list := by
  exact edge_identity (B := (2:ℤ)^295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011011001 : Branch 1 (-4959761639/8000000 : ℚ) vp1001101100 := by
  apply branch_checked idp10011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-4959761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4963761639/4000000 : ℚ) by norm_num]
  exact coverp10011011001
theorem coverp1001101100 : Covers (-4959761639/8000000 : ℚ) vp1001101100 := join_branches bp10011011000 bp10011011001
private noncomputable def vp100110110_0 : Blocks := edgeBlocks% "full/vectors/100110110-V-0000.bin"
private noncomputable def vp100110110_1 : Blocks := edgeBlocks% "full/vectors/100110110-V-0001.bin"
noncomputable def vp100110110 : Blocks := (Blocks.join vp100110110_0 vp100110110_1)
private theorem bp1001101100 : Branch 0 (-4959761639/16000000 : ℚ) vp100110110 := by
  apply branch_left_normalized (c:=vp1001101100) (k:=0) (m:=133) (by decide +kernel)
  rw [show 2*(-4959761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4959761639/8000000 : ℚ) by norm_num]
  exact coverp1001101100
private noncomputable def ep1001101101_0 : Blocks := edgeBlocks% "full/vectors/1001101101-E-0000.bin"
private noncomputable def ep1001101101_1 : Blocks := edgeBlocks% "full/vectors/1001101101-E-0001.bin"
noncomputable def ep1001101101 : Blocks := (Blocks.join ep1001101101_0 ep1001101101_1)
private theorem idp1001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100110110.list =
    C ((2:ℤ)^292) * horner X vp1001101101.list + horner X ep1001101101.list := by
  exact edge_identity (B := (2:ℤ)^466) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001101101 : Branch 1 (-4959761639/16000000 : ℚ) vp100110110 := by
  apply branch_checked idp1001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-4959761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4967761639/8000000 : ℚ) by norm_num]
  exact coverp1001101101
theorem coverp100110110 : Covers (-4959761639/16000000 : ℚ) vp100110110 := join_branches bp1001101100 bp1001101101
private noncomputable def vp10011011_0 : Blocks := edgeBlocks% "full/vectors/10011011-V-0000.bin"
private noncomputable def vp10011011_1 : Blocks := edgeBlocks% "full/vectors/10011011-V-0001.bin"
private noncomputable def vp10011011_2 : Blocks := edgeBlocks% "full/vectors/10011011-V-0002.bin"
private noncomputable def vp10011011_3 : Blocks := edgeBlocks% "full/vectors/10011011-V-0003.bin"
noncomputable def vp10011011 : Blocks := (Blocks.join (Blocks.join vp10011011_0 vp10011011_1) (Blocks.join vp10011011_2 vp10011011_3))
private theorem bp100110110 : Branch 0 (-4959761639/32000000 : ℚ) vp10011011 := by
  apply branch_left_normalized (c:=vp100110110) (k:=0) (m:=245) (by decide +kernel)
  rw [show 2*(-4959761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4959761639/16000000 : ℚ) by norm_num]
  exact coverp100110110
private noncomputable def ep100110111_0 : Blocks := edgeBlocks% "full/vectors/100110111-E-0000.bin"
private noncomputable def ep100110111_1 : Blocks := edgeBlocks% "full/vectors/100110111-E-0001.bin"
private noncomputable def ep100110111_2 : Blocks := edgeBlocks% "full/vectors/100110111-E-0002.bin"
private noncomputable def ep100110111_3 : Blocks := edgeBlocks% "full/vectors/100110111-E-0003.bin"
noncomputable def ep100110111 : Blocks := (Blocks.join (Blocks.join ep100110111_0 ep100110111_1) (Blocks.join ep100110111_2 ep100110111_3))
private theorem idp100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10011011.list =
    C ((2:ℤ)^561) * horner X vp100110111.list + horner X ep100110111.list := by
  exact edge_identity (B := (2:ℤ)^806) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100110111 : Branch 1 (-4959761639/32000000 : ℚ) vp10011011 := by
  apply branch_checked idp100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-4959761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4975761639/16000000 : ℚ) by norm_num]
  exact coverp100110111
theorem coverp10011011 : Covers (-4959761639/32000000 : ℚ) vp10011011 := join_branches bp100110110 bp100110111
private noncomputable def vp10011010111_0 : Blocks := edgeBlocks% "full/vectors/10011010111-V-0000.bin"
noncomputable def vp10011010111 : Blocks := vp10011010111_0
theorem coverp10011010111 : Covers (-4955761639/4000000 : ℚ) vp10011010111 := cover_leaf (by decide +kernel)
private noncomputable def vp10011010110_0 : Blocks := edgeBlocks% "full/vectors/10011010110-V-0000.bin"
noncomputable def vp10011010110 : Blocks := vp10011010110_0
theorem coverp10011010110 : Covers (-4951761639/4000000 : ℚ) vp10011010110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001101011_0 : Blocks := edgeBlocks% "full/vectors/1001101011-V-0000.bin"
private noncomputable def vp1001101011_1 : Blocks := edgeBlocks% "full/vectors/1001101011-V-0001.bin"
noncomputable def vp1001101011 : Blocks := (Blocks.join vp1001101011_0 vp1001101011_1)
private theorem bp10011010110 : Branch 0 (-4951761639/8000000 : ℚ) vp1001101011 := by
  apply branch_left_normalized (c:=vp10011010110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4951761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4951761639/4000000 : ℚ) by norm_num]
  exact coverp10011010110
private noncomputable def ep10011010111_0 : Blocks := edgeBlocks% "full/vectors/10011010111-E-0000.bin"
private noncomputable def ep10011010111_1 : Blocks := edgeBlocks% "full/vectors/10011010111-E-0001.bin"
noncomputable def ep10011010111 : Blocks := (Blocks.join ep10011010111_0 ep10011010111_1)
private theorem idp10011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001101011.list =
    C ((2:ℤ)^157) * horner X vp10011010111.list + horner X ep10011010111.list := by
  exact edge_identity (B := (2:ℤ)^294) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011010111 : Branch 1 (-4951761639/8000000 : ℚ) vp1001101011 := by
  apply branch_checked idp10011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-4951761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4955761639/4000000 : ℚ) by norm_num]
  exact coverp10011010111
theorem coverp1001101011 : Covers (-4951761639/8000000 : ℚ) vp1001101011 := join_branches bp10011010110 bp10011010111
private noncomputable def vp10011010101_0 : Blocks := edgeBlocks% "full/vectors/10011010101-V-0000.bin"
noncomputable def vp10011010101 : Blocks := vp10011010101_0
theorem coverp10011010101 : Covers (-4947761639/4000000 : ℚ) vp10011010101 := cover_leaf (by decide +kernel)
private noncomputable def vp10011010100_0 : Blocks := edgeBlocks% "full/vectors/10011010100-V-0000.bin"
noncomputable def vp10011010100 : Blocks := vp10011010100_0
theorem coverp10011010100 : Covers (-4943761639/4000000 : ℚ) vp10011010100 := cover_leaf (by decide +kernel)
private noncomputable def vp1001101010_0 : Blocks := edgeBlocks% "full/vectors/1001101010-V-0000.bin"
private noncomputable def vp1001101010_1 : Blocks := edgeBlocks% "full/vectors/1001101010-V-0001.bin"
noncomputable def vp1001101010 : Blocks := (Blocks.join vp1001101010_0 vp1001101010_1)
private theorem bp10011010100 : Branch 0 (-4943761639/8000000 : ℚ) vp1001101010 := by
  apply branch_left_normalized (c:=vp10011010100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-4943761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4943761639/4000000 : ℚ) by norm_num]
  exact coverp10011010100
private noncomputable def ep10011010101_0 : Blocks := edgeBlocks% "full/vectors/10011010101-E-0000.bin"
private noncomputable def ep10011010101_1 : Blocks := edgeBlocks% "full/vectors/10011010101-E-0001.bin"
noncomputable def ep10011010101 : Blocks := (Blocks.join ep10011010101_0 ep10011010101_1)
private theorem idp10011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001101010.list =
    C ((2:ℤ)^158) * horner X vp10011010101.list + horner X ep10011010101.list := by
  exact edge_identity (B := (2:ℤ)^295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011010101 : Branch 1 (-4943761639/8000000 : ℚ) vp1001101010 := by
  apply branch_checked idp10011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4943761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4947761639/4000000 : ℚ) by norm_num]
  exact coverp10011010101
theorem coverp1001101010 : Covers (-4943761639/8000000 : ℚ) vp1001101010 := join_branches bp10011010100 bp10011010101
private noncomputable def vp100110101_0 : Blocks := edgeBlocks% "full/vectors/100110101-V-0000.bin"
private noncomputable def vp100110101_1 : Blocks := edgeBlocks% "full/vectors/100110101-V-0001.bin"
noncomputable def vp100110101 : Blocks := (Blocks.join vp100110101_0 vp100110101_1)
private theorem bp1001101010 : Branch 0 (-4943761639/16000000 : ℚ) vp100110101 := by
  apply branch_left_normalized (c:=vp1001101010) (k:=0) (m:=134) (by decide +kernel)
  rw [show 2*(-4943761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4943761639/8000000 : ℚ) by norm_num]
  exact coverp1001101010
private noncomputable def ep1001101011_0 : Blocks := edgeBlocks% "full/vectors/1001101011-E-0000.bin"
private noncomputable def ep1001101011_1 : Blocks := edgeBlocks% "full/vectors/1001101011-E-0001.bin"
noncomputable def ep1001101011 : Blocks := (Blocks.join ep1001101011_0 ep1001101011_1)
private theorem idp1001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100110101.list =
    C ((2:ℤ)^292) * horner X vp1001101011.list + horner X ep1001101011.list := by
  exact edge_identity (B := (2:ℤ)^466) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001101011 : Branch 1 (-4943761639/16000000 : ℚ) vp100110101 := by
  apply branch_checked idp1001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-4943761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4951761639/8000000 : ℚ) by norm_num]
  exact coverp1001101011
theorem coverp100110101 : Covers (-4943761639/16000000 : ℚ) vp100110101 := join_branches bp1001101010 bp1001101011
private noncomputable def vp10011010011_0 : Blocks := edgeBlocks% "full/vectors/10011010011-V-0000.bin"
noncomputable def vp10011010011 : Blocks := vp10011010011_0
theorem coverp10011010011 : Covers (-4939761639/4000000 : ℚ) vp10011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp10011010010_0 : Blocks := edgeBlocks% "full/vectors/10011010010-V-0000.bin"
noncomputable def vp10011010010 : Blocks := vp10011010010_0
theorem coverp10011010010 : Covers (-4935761639/4000000 : ℚ) vp10011010010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001101001_0 : Blocks := edgeBlocks% "full/vectors/1001101001-V-0000.bin"
private noncomputable def vp1001101001_1 : Blocks := edgeBlocks% "full/vectors/1001101001-V-0001.bin"
noncomputable def vp1001101001 : Blocks := (Blocks.join vp1001101001_0 vp1001101001_1)
private theorem bp10011010010 : Branch 0 (-4935761639/8000000 : ℚ) vp1001101001 := by
  apply branch_left_normalized (c:=vp10011010010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-4935761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4935761639/4000000 : ℚ) by norm_num]
  exact coverp10011010010
private noncomputable def ep10011010011_0 : Blocks := edgeBlocks% "full/vectors/10011010011-E-0000.bin"
private noncomputable def ep10011010011_1 : Blocks := edgeBlocks% "full/vectors/10011010011-E-0001.bin"
noncomputable def ep10011010011 : Blocks := (Blocks.join ep10011010011_0 ep10011010011_1)
private theorem idp10011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001101001.list =
    C ((2:ℤ)^159) * horner X vp10011010011.list + horner X ep10011010011.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011010011 : Branch 1 (-4935761639/8000000 : ℚ) vp1001101001 := by
  apply branch_checked idp10011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4935761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4939761639/4000000 : ℚ) by norm_num]
  exact coverp10011010011
theorem coverp1001101001 : Covers (-4935761639/8000000 : ℚ) vp1001101001 := join_branches bp10011010010 bp10011010011
private noncomputable def vp10011010001_0 : Blocks := edgeBlocks% "full/vectors/10011010001-V-0000.bin"
noncomputable def vp10011010001 : Blocks := vp10011010001_0
theorem coverp10011010001 : Covers (-4931761639/4000000 : ℚ) vp10011010001 := cover_leaf (by decide +kernel)
private noncomputable def vp10011010000_0 : Blocks := edgeBlocks% "full/vectors/10011010000-V-0000.bin"
noncomputable def vp10011010000 : Blocks := vp10011010000_0
theorem coverp10011010000 : Covers (-4927761639/4000000 : ℚ) vp10011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001101000_0 : Blocks := edgeBlocks% "full/vectors/1001101000-V-0000.bin"
private noncomputable def vp1001101000_1 : Blocks := edgeBlocks% "full/vectors/1001101000-V-0001.bin"
noncomputable def vp1001101000 : Blocks := (Blocks.join vp1001101000_0 vp1001101000_1)
private theorem bp10011010000 : Branch 0 (-4927761639/8000000 : ℚ) vp1001101000 := by
  apply branch_left_normalized (c:=vp10011010000) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4927761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4927761639/4000000 : ℚ) by norm_num]
  exact coverp10011010000
private noncomputable def ep10011010001_0 : Blocks := edgeBlocks% "full/vectors/10011010001-E-0000.bin"
private noncomputable def ep10011010001_1 : Blocks := edgeBlocks% "full/vectors/10011010001-E-0001.bin"
noncomputable def ep10011010001 : Blocks := (Blocks.join ep10011010001_0 ep10011010001_1)
private theorem idp10011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001101000.list =
    C ((2:ℤ)^157) * horner X vp10011010001.list + horner X ep10011010001.list := by
  exact edge_identity (B := (2:ℤ)^295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011010001 : Branch 1 (-4927761639/8000000 : ℚ) vp1001101000 := by
  apply branch_checked idp10011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4927761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4931761639/4000000 : ℚ) by norm_num]
  exact coverp10011010001
theorem coverp1001101000 : Covers (-4927761639/8000000 : ℚ) vp1001101000 := join_branches bp10011010000 bp10011010001
private noncomputable def vp100110100_0 : Blocks := edgeBlocks% "full/vectors/100110100-V-0000.bin"
private noncomputable def vp100110100_1 : Blocks := edgeBlocks% "full/vectors/100110100-V-0001.bin"
noncomputable def vp100110100 : Blocks := (Blocks.join vp100110100_0 vp100110100_1)
private theorem bp1001101000 : Branch 0 (-4927761639/16000000 : ℚ) vp100110100 := by
  apply branch_left_normalized (c:=vp1001101000) (k:=0) (m:=133) (by decide +kernel)
  rw [show 2*(-4927761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4927761639/8000000 : ℚ) by norm_num]
  exact coverp1001101000
private noncomputable def ep1001101001_0 : Blocks := edgeBlocks% "full/vectors/1001101001-E-0000.bin"
private noncomputable def ep1001101001_1 : Blocks := edgeBlocks% "full/vectors/1001101001-E-0001.bin"
noncomputable def ep1001101001 : Blocks := (Blocks.join ep1001101001_0 ep1001101001_1)
private theorem idp1001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100110100.list =
    C ((2:ℤ)^293) * horner X vp1001101001.list + horner X ep1001101001.list := by
  exact edge_identity (B := (2:ℤ)^467) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001101001 : Branch 1 (-4927761639/16000000 : ℚ) vp100110100 := by
  apply branch_checked idp1001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-4927761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4935761639/8000000 : ℚ) by norm_num]
  exact coverp1001101001
theorem coverp100110100 : Covers (-4927761639/16000000 : ℚ) vp100110100 := join_branches bp1001101000 bp1001101001
private noncomputable def vp10011010_0 : Blocks := edgeBlocks% "full/vectors/10011010-V-0000.bin"
private noncomputable def vp10011010_1 : Blocks := edgeBlocks% "full/vectors/10011010-V-0001.bin"
private noncomputable def vp10011010_2 : Blocks := edgeBlocks% "full/vectors/10011010-V-0002.bin"
private noncomputable def vp10011010_3 : Blocks := edgeBlocks% "full/vectors/10011010-V-0003.bin"
noncomputable def vp10011010 : Blocks := (Blocks.join (Blocks.join vp10011010_0 vp10011010_1) (Blocks.join vp10011010_2 vp10011010_3))
private theorem bp100110100 : Branch 0 (-4927761639/32000000 : ℚ) vp10011010 := by
  apply branch_left_normalized (c:=vp100110100) (k:=0) (m:=246) (by decide +kernel)
  rw [show 2*(-4927761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4927761639/16000000 : ℚ) by norm_num]
  exact coverp100110100
private noncomputable def ep100110101_0 : Blocks := edgeBlocks% "full/vectors/100110101-E-0000.bin"
private noncomputable def ep100110101_1 : Blocks := edgeBlocks% "full/vectors/100110101-E-0001.bin"
private noncomputable def ep100110101_2 : Blocks := edgeBlocks% "full/vectors/100110101-E-0002.bin"
private noncomputable def ep100110101_3 : Blocks := edgeBlocks% "full/vectors/100110101-E-0003.bin"
noncomputable def ep100110101 : Blocks := (Blocks.join (Blocks.join ep100110101_0 ep100110101_1) (Blocks.join ep100110101_2 ep100110101_3))
private theorem idp100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10011010.list =
    C ((2:ℤ)^562) * horner X vp100110101.list + horner X ep100110101.list := by
  exact edge_identity (B := (2:ℤ)^808) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100110101 : Branch 1 (-4927761639/32000000 : ℚ) vp10011010 := by
  apply branch_checked idp100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-4927761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4943761639/16000000 : ℚ) by norm_num]
  exact coverp100110101
theorem coverp10011010 : Covers (-4927761639/32000000 : ℚ) vp10011010 := join_branches bp100110100 bp100110101
private noncomputable def vp1001101_0 : Blocks := edgeBlocks% "full/vectors/1001101-V-0000.bin"
private noncomputable def vp1001101_1 : Blocks := edgeBlocks% "full/vectors/1001101-V-0001.bin"
private noncomputable def vp1001101_2 : Blocks := edgeBlocks% "full/vectors/1001101-V-0002.bin"
private noncomputable def vp1001101_3 : Blocks := edgeBlocks% "full/vectors/1001101-V-0003.bin"
private noncomputable def vp1001101_4 : Blocks := edgeBlocks% "full/vectors/1001101-V-0004.bin"
private noncomputable def vp1001101_5 : Blocks := edgeBlocks% "full/vectors/1001101-V-0005.bin"
private noncomputable def vp1001101_6 : Blocks := edgeBlocks% "full/vectors/1001101-V-0006.bin"
private noncomputable def vp1001101_7 : Blocks := edgeBlocks% "full/vectors/1001101-V-0007.bin"
noncomputable def vp1001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1001101_0 vp1001101_1) (Blocks.join vp1001101_2 vp1001101_3)) (Blocks.join (Blocks.join vp1001101_4 vp1001101_5) (Blocks.join vp1001101_6 vp1001101_7)))
private theorem bp10011010 : Branch 0 (-4927761639/64000000 : ℚ) vp1001101 := by
  apply branch_left_normalized (c:=vp10011010) (k:=0) (m:=468) (by decide +kernel)
  rw [show 2*(-4927761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4927761639/32000000 : ℚ) by norm_num]
  exact coverp10011010
private noncomputable def ep10011011_0 : Blocks := edgeBlocks% "full/vectors/10011011-E-0000.bin"
private noncomputable def ep10011011_1 : Blocks := edgeBlocks% "full/vectors/10011011-E-0001.bin"
private noncomputable def ep10011011_2 : Blocks := edgeBlocks% "full/vectors/10011011-E-0002.bin"
private noncomputable def ep10011011_3 : Blocks := edgeBlocks% "full/vectors/10011011-E-0003.bin"
private noncomputable def ep10011011_4 : Blocks := edgeBlocks% "full/vectors/10011011-E-0004.bin"
private noncomputable def ep10011011_5 : Blocks := edgeBlocks% "full/vectors/10011011-E-0005.bin"
private noncomputable def ep10011011_6 : Blocks := edgeBlocks% "full/vectors/10011011-E-0006.bin"
private noncomputable def ep10011011_7 : Blocks := edgeBlocks% "full/vectors/10011011-E-0007.bin"
noncomputable def ep10011011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10011011_0 ep10011011_1) (Blocks.join ep10011011_2 ep10011011_3)) (Blocks.join (Blocks.join ep10011011_4 ep10011011_5) (Blocks.join ep10011011_6 ep10011011_7)))
private theorem idp10011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001101.list =
    C ((2:ℤ)^1094) * horner X vp10011011.list + horner X ep10011011.list := by
  exact edge_identity (B := (2:ℤ)^1484) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011011 : Branch 1 (-4927761639/64000000 : ℚ) vp1001101 := by
  apply branch_checked idp10011011 (by positivity) (by decide +kernel)
  rw [show 2*(-4927761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4959761639/32000000 : ℚ) by norm_num]
  exact coverp10011011
theorem coverp1001101 : Covers (-4927761639/64000000 : ℚ) vp1001101 := join_branches bp10011010 bp10011011
private noncomputable def vp10011001111_0 : Blocks := edgeBlocks% "full/vectors/10011001111-V-0000.bin"
noncomputable def vp10011001111 : Blocks := vp10011001111_0
theorem coverp10011001111 : Covers (-4923761639/4000000 : ℚ) vp10011001111 := cover_leaf (by decide +kernel)
private noncomputable def vp10011001110_0 : Blocks := edgeBlocks% "full/vectors/10011001110-V-0000.bin"
noncomputable def vp10011001110 : Blocks := vp10011001110_0
theorem coverp10011001110 : Covers (-4919761639/4000000 : ℚ) vp10011001110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001100111_0 : Blocks := edgeBlocks% "full/vectors/1001100111-V-0000.bin"
private noncomputable def vp1001100111_1 : Blocks := edgeBlocks% "full/vectors/1001100111-V-0001.bin"
noncomputable def vp1001100111 : Blocks := (Blocks.join vp1001100111_0 vp1001100111_1)
private theorem bp10011001110 : Branch 0 (-4919761639/8000000 : ℚ) vp1001100111 := by
  apply branch_left_normalized (c:=vp10011001110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4919761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4919761639/4000000 : ℚ) by norm_num]
  exact coverp10011001110
private noncomputable def ep10011001111_0 : Blocks := edgeBlocks% "full/vectors/10011001111-E-0000.bin"
private noncomputable def ep10011001111_1 : Blocks := edgeBlocks% "full/vectors/10011001111-E-0001.bin"
noncomputable def ep10011001111 : Blocks := (Blocks.join ep10011001111_0 ep10011001111_1)
private theorem idp10011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001100111.list =
    C ((2:ℤ)^157) * horner X vp10011001111.list + horner X ep10011001111.list := by
  exact edge_identity (B := (2:ℤ)^295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011001111 : Branch 1 (-4919761639/8000000 : ℚ) vp1001100111 := by
  apply branch_checked idp10011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4919761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4923761639/4000000 : ℚ) by norm_num]
  exact coverp10011001111
theorem coverp1001100111 : Covers (-4919761639/8000000 : ℚ) vp1001100111 := join_branches bp10011001110 bp10011001111
private noncomputable def vp10011001101_0 : Blocks := edgeBlocks% "full/vectors/10011001101-V-0000.bin"
noncomputable def vp10011001101 : Blocks := vp10011001101_0
theorem coverp10011001101 : Covers (-4915761639/4000000 : ℚ) vp10011001101 := cover_leaf (by decide +kernel)
private noncomputable def vp10011001100_0 : Blocks := edgeBlocks% "full/vectors/10011001100-V-0000.bin"
noncomputable def vp10011001100 : Blocks := vp10011001100_0
theorem coverp10011001100 : Covers (-4911761639/4000000 : ℚ) vp10011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp1001100110_0 : Blocks := edgeBlocks% "full/vectors/1001100110-V-0000.bin"
private noncomputable def vp1001100110_1 : Blocks := edgeBlocks% "full/vectors/1001100110-V-0001.bin"
noncomputable def vp1001100110 : Blocks := (Blocks.join vp1001100110_0 vp1001100110_1)
private theorem bp10011001100 : Branch 0 (-4911761639/8000000 : ℚ) vp1001100110 := by
  apply branch_left_normalized (c:=vp10011001100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-4911761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4911761639/4000000 : ℚ) by norm_num]
  exact coverp10011001100
private noncomputable def ep10011001101_0 : Blocks := edgeBlocks% "full/vectors/10011001101-E-0000.bin"
private noncomputable def ep10011001101_1 : Blocks := edgeBlocks% "full/vectors/10011001101-E-0001.bin"
noncomputable def ep10011001101 : Blocks := (Blocks.join ep10011001101_0 ep10011001101_1)
private theorem idp10011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001100110.list =
    C ((2:ℤ)^158) * horner X vp10011001101.list + horner X ep10011001101.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011001101 : Branch 1 (-4911761639/8000000 : ℚ) vp1001100110 := by
  apply branch_checked idp10011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4911761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4915761639/4000000 : ℚ) by norm_num]
  exact coverp10011001101
theorem coverp1001100110 : Covers (-4911761639/8000000 : ℚ) vp1001100110 := join_branches bp10011001100 bp10011001101
private noncomputable def vp100110011_0 : Blocks := edgeBlocks% "full/vectors/100110011-V-0000.bin"
private noncomputable def vp100110011_1 : Blocks := edgeBlocks% "full/vectors/100110011-V-0001.bin"
noncomputable def vp100110011 : Blocks := (Blocks.join vp100110011_0 vp100110011_1)
private theorem bp1001100110 : Branch 0 (-4911761639/16000000 : ℚ) vp100110011 := by
  apply branch_left_normalized (c:=vp1001100110) (k:=0) (m:=134) (by decide +kernel)
  rw [show 2*(-4911761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4911761639/8000000 : ℚ) by norm_num]
  exact coverp1001100110
private noncomputable def ep1001100111_0 : Blocks := edgeBlocks% "full/vectors/1001100111-E-0000.bin"
private noncomputable def ep1001100111_1 : Blocks := edgeBlocks% "full/vectors/1001100111-E-0001.bin"
noncomputable def ep1001100111 : Blocks := (Blocks.join ep1001100111_0 ep1001100111_1)
private theorem idp1001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100110011.list =
    C ((2:ℤ)^293) * horner X vp1001100111.list + horner X ep1001100111.list := by
  exact edge_identity (B := (2:ℤ)^467) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001100111 : Branch 1 (-4911761639/16000000 : ℚ) vp100110011 := by
  apply branch_checked idp1001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-4911761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4919761639/8000000 : ℚ) by norm_num]
  exact coverp1001100111
theorem coverp100110011 : Covers (-4911761639/16000000 : ℚ) vp100110011 := join_branches bp1001100110 bp1001100111
private noncomputable def vp10011001011_0 : Blocks := edgeBlocks% "full/vectors/10011001011-V-0000.bin"
noncomputable def vp10011001011 : Blocks := vp10011001011_0
theorem coverp10011001011 : Covers (-4907761639/4000000 : ℚ) vp10011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp10011001010_0 : Blocks := edgeBlocks% "full/vectors/10011001010-V-0000.bin"
noncomputable def vp10011001010 : Blocks := vp10011001010_0
theorem coverp10011001010 : Covers (-4903761639/4000000 : ℚ) vp10011001010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001100101_0 : Blocks := edgeBlocks% "full/vectors/1001100101-V-0000.bin"
private noncomputable def vp1001100101_1 : Blocks := edgeBlocks% "full/vectors/1001100101-V-0001.bin"
noncomputable def vp1001100101 : Blocks := (Blocks.join vp1001100101_0 vp1001100101_1)
private theorem bp10011001010 : Branch 0 (-4903761639/8000000 : ℚ) vp1001100101 := by
  apply branch_left_normalized (c:=vp10011001010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-4903761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4903761639/4000000 : ℚ) by norm_num]
  exact coverp10011001010
private noncomputable def ep10011001011_0 : Blocks := edgeBlocks% "full/vectors/10011001011-E-0000.bin"
private noncomputable def ep10011001011_1 : Blocks := edgeBlocks% "full/vectors/10011001011-E-0001.bin"
noncomputable def ep10011001011 : Blocks := (Blocks.join ep10011001011_0 ep10011001011_1)
private theorem idp10011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001100101.list =
    C ((2:ℤ)^158) * horner X vp10011001011.list + horner X ep10011001011.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011001011 : Branch 1 (-4903761639/8000000 : ℚ) vp1001100101 := by
  apply branch_checked idp10011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4903761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4907761639/4000000 : ℚ) by norm_num]
  exact coverp10011001011
theorem coverp1001100101 : Covers (-4903761639/8000000 : ℚ) vp1001100101 := join_branches bp10011001010 bp10011001011
private noncomputable def vp10011001001_0 : Blocks := edgeBlocks% "full/vectors/10011001001-V-0000.bin"
noncomputable def vp10011001001 : Blocks := vp10011001001_0
theorem coverp10011001001 : Covers (-4899761639/4000000 : ℚ) vp10011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp10011001000_0 : Blocks := edgeBlocks% "full/vectors/10011001000-V-0000.bin"
noncomputable def vp10011001000 : Blocks := vp10011001000_0
theorem coverp10011001000 : Covers (-4895761639/4000000 : ℚ) vp10011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001100100_0 : Blocks := edgeBlocks% "full/vectors/1001100100-V-0000.bin"
private noncomputable def vp1001100100_1 : Blocks := edgeBlocks% "full/vectors/1001100100-V-0001.bin"
noncomputable def vp1001100100 : Blocks := (Blocks.join vp1001100100_0 vp1001100100_1)
private theorem bp10011001000 : Branch 0 (-4895761639/8000000 : ℚ) vp1001100100 := by
  apply branch_left_normalized (c:=vp10011001000) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4895761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4895761639/4000000 : ℚ) by norm_num]
  exact coverp10011001000
private noncomputable def ep10011001001_0 : Blocks := edgeBlocks% "full/vectors/10011001001-E-0000.bin"
private noncomputable def ep10011001001_1 : Blocks := edgeBlocks% "full/vectors/10011001001-E-0001.bin"
noncomputable def ep10011001001 : Blocks := (Blocks.join ep10011001001_0 ep10011001001_1)
private theorem idp10011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001100100.list =
    C ((2:ℤ)^157) * horner X vp10011001001.list + horner X ep10011001001.list := by
  exact edge_identity (B := (2:ℤ)^295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011001001 : Branch 1 (-4895761639/8000000 : ℚ) vp1001100100 := by
  apply branch_checked idp10011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4895761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4899761639/4000000 : ℚ) by norm_num]
  exact coverp10011001001
theorem coverp1001100100 : Covers (-4895761639/8000000 : ℚ) vp1001100100 := join_branches bp10011001000 bp10011001001
private noncomputable def vp100110010_0 : Blocks := edgeBlocks% "full/vectors/100110010-V-0000.bin"
private noncomputable def vp100110010_1 : Blocks := edgeBlocks% "full/vectors/100110010-V-0001.bin"
noncomputable def vp100110010 : Blocks := (Blocks.join vp100110010_0 vp100110010_1)
private theorem bp1001100100 : Branch 0 (-4895761639/16000000 : ℚ) vp100110010 := by
  apply branch_left_normalized (c:=vp1001100100) (k:=0) (m:=133) (by decide +kernel)
  rw [show 2*(-4895761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4895761639/8000000 : ℚ) by norm_num]
  exact coverp1001100100
private noncomputable def ep1001100101_0 : Blocks := edgeBlocks% "full/vectors/1001100101-E-0000.bin"
private noncomputable def ep1001100101_1 : Blocks := edgeBlocks% "full/vectors/1001100101-E-0001.bin"
noncomputable def ep1001100101 : Blocks := (Blocks.join ep1001100101_0 ep1001100101_1)
private theorem idp1001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100110010.list =
    C ((2:ℤ)^294) * horner X vp1001100101.list + horner X ep1001100101.list := by
  exact edge_identity (B := (2:ℤ)^468) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001100101 : Branch 1 (-4895761639/16000000 : ℚ) vp100110010 := by
  apply branch_checked idp1001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-4895761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4903761639/8000000 : ℚ) by norm_num]
  exact coverp1001100101
theorem coverp100110010 : Covers (-4895761639/16000000 : ℚ) vp100110010 := join_branches bp1001100100 bp1001100101
private noncomputable def vp10011001_0 : Blocks := edgeBlocks% "full/vectors/10011001-V-0000.bin"
private noncomputable def vp10011001_1 : Blocks := edgeBlocks% "full/vectors/10011001-V-0001.bin"
private noncomputable def vp10011001_2 : Blocks := edgeBlocks% "full/vectors/10011001-V-0002.bin"
private noncomputable def vp10011001_3 : Blocks := edgeBlocks% "full/vectors/10011001-V-0003.bin"
noncomputable def vp10011001 : Blocks := (Blocks.join (Blocks.join vp10011001_0 vp10011001_1) (Blocks.join vp10011001_2 vp10011001_3))
private theorem bp100110010 : Branch 0 (-4895761639/32000000 : ℚ) vp10011001 := by
  apply branch_left_normalized (c:=vp100110010) (k:=0) (m:=247) (by decide +kernel)
  rw [show 2*(-4895761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4895761639/16000000 : ℚ) by norm_num]
  exact coverp100110010
private noncomputable def ep100110011_0 : Blocks := edgeBlocks% "full/vectors/100110011-E-0000.bin"
private noncomputable def ep100110011_1 : Blocks := edgeBlocks% "full/vectors/100110011-E-0001.bin"
private noncomputable def ep100110011_2 : Blocks := edgeBlocks% "full/vectors/100110011-E-0002.bin"
private noncomputable def ep100110011_3 : Blocks := edgeBlocks% "full/vectors/100110011-E-0003.bin"
noncomputable def ep100110011 : Blocks := (Blocks.join (Blocks.join ep100110011_0 ep100110011_1) (Blocks.join ep100110011_2 ep100110011_3))
private theorem idp100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10011001.list =
    C ((2:ℤ)^563) * horner X vp100110011.list + horner X ep100110011.list := by
  exact edge_identity (B := (2:ℤ)^810) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100110011 : Branch 1 (-4895761639/32000000 : ℚ) vp10011001 := by
  apply branch_checked idp100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-4895761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4911761639/16000000 : ℚ) by norm_num]
  exact coverp100110011
theorem coverp10011001 : Covers (-4895761639/32000000 : ℚ) vp10011001 := join_branches bp100110010 bp100110011
private noncomputable def vp10011000111_0 : Blocks := edgeBlocks% "full/vectors/10011000111-V-0000.bin"
noncomputable def vp10011000111 : Blocks := vp10011000111_0
theorem coverp10011000111 : Covers (-4891761639/4000000 : ℚ) vp10011000111 := cover_leaf (by decide +kernel)
private noncomputable def vp10011000110_0 : Blocks := edgeBlocks% "full/vectors/10011000110-V-0000.bin"
noncomputable def vp10011000110 : Blocks := vp10011000110_0
theorem coverp10011000110 : Covers (-4887761639/4000000 : ℚ) vp10011000110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001100011_0 : Blocks := edgeBlocks% "full/vectors/1001100011-V-0000.bin"
private noncomputable def vp1001100011_1 : Blocks := edgeBlocks% "full/vectors/1001100011-V-0001.bin"
noncomputable def vp1001100011 : Blocks := (Blocks.join vp1001100011_0 vp1001100011_1)
private theorem bp10011000110 : Branch 0 (-4887761639/8000000 : ℚ) vp1001100011 := by
  apply branch_left_normalized (c:=vp10011000110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4887761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4887761639/4000000 : ℚ) by norm_num]
  exact coverp10011000110
private noncomputable def ep10011000111_0 : Blocks := edgeBlocks% "full/vectors/10011000111-E-0000.bin"
private noncomputable def ep10011000111_1 : Blocks := edgeBlocks% "full/vectors/10011000111-E-0001.bin"
noncomputable def ep10011000111 : Blocks := (Blocks.join ep10011000111_0 ep10011000111_1)
private theorem idp10011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001100011.list =
    C ((2:ℤ)^159) * horner X vp10011000111.list + horner X ep10011000111.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011000111 : Branch 1 (-4887761639/8000000 : ℚ) vp1001100011 := by
  apply branch_checked idp10011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4887761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4891761639/4000000 : ℚ) by norm_num]
  exact coverp10011000111
theorem coverp1001100011 : Covers (-4887761639/8000000 : ℚ) vp1001100011 := join_branches bp10011000110 bp10011000111
private noncomputable def vp10011000101_0 : Blocks := edgeBlocks% "full/vectors/10011000101-V-0000.bin"
noncomputable def vp10011000101 : Blocks := vp10011000101_0
theorem coverp10011000101 : Covers (-4883761639/4000000 : ℚ) vp10011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp10011000100_0 : Blocks := edgeBlocks% "full/vectors/10011000100-V-0000.bin"
noncomputable def vp10011000100 : Blocks := vp10011000100_0
theorem coverp10011000100 : Covers (-4879761639/4000000 : ℚ) vp10011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp1001100010_0 : Blocks := edgeBlocks% "full/vectors/1001100010-V-0000.bin"
private noncomputable def vp1001100010_1 : Blocks := edgeBlocks% "full/vectors/1001100010-V-0001.bin"
noncomputable def vp1001100010 : Blocks := (Blocks.join vp1001100010_0 vp1001100010_1)
private theorem bp10011000100 : Branch 0 (-4879761639/8000000 : ℚ) vp1001100010 := by
  apply branch_left_normalized (c:=vp10011000100) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4879761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4879761639/4000000 : ℚ) by norm_num]
  exact coverp10011000100
private noncomputable def ep10011000101_0 : Blocks := edgeBlocks% "full/vectors/10011000101-E-0000.bin"
private noncomputable def ep10011000101_1 : Blocks := edgeBlocks% "full/vectors/10011000101-E-0001.bin"
noncomputable def ep10011000101 : Blocks := (Blocks.join ep10011000101_0 ep10011000101_1)
private theorem idp10011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001100010.list =
    C ((2:ℤ)^158) * horner X vp10011000101.list + horner X ep10011000101.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011000101 : Branch 1 (-4879761639/8000000 : ℚ) vp1001100010 := by
  apply branch_checked idp10011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4879761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4883761639/4000000 : ℚ) by norm_num]
  exact coverp10011000101
theorem coverp1001100010 : Covers (-4879761639/8000000 : ℚ) vp1001100010 := join_branches bp10011000100 bp10011000101
private noncomputable def vp100110001_0 : Blocks := edgeBlocks% "full/vectors/100110001-V-0000.bin"
private noncomputable def vp100110001_1 : Blocks := edgeBlocks% "full/vectors/100110001-V-0001.bin"
noncomputable def vp100110001 : Blocks := (Blocks.join vp100110001_0 vp100110001_1)
private theorem bp1001100010 : Branch 0 (-4879761639/16000000 : ℚ) vp100110001 := by
  apply branch_left_normalized (c:=vp1001100010) (k:=0) (m:=134) (by decide +kernel)
  rw [show 2*(-4879761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4879761639/8000000 : ℚ) by norm_num]
  exact coverp1001100010
private noncomputable def ep1001100011_0 : Blocks := edgeBlocks% "full/vectors/1001100011-E-0000.bin"
private noncomputable def ep1001100011_1 : Blocks := edgeBlocks% "full/vectors/1001100011-E-0001.bin"
noncomputable def ep1001100011 : Blocks := (Blocks.join ep1001100011_0 ep1001100011_1)
private theorem idp1001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100110001.list =
    C ((2:ℤ)^293) * horner X vp1001100011.list + horner X ep1001100011.list := by
  exact edge_identity (B := (2:ℤ)^468) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001100011 : Branch 1 (-4879761639/16000000 : ℚ) vp100110001 := by
  apply branch_checked idp1001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-4879761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4887761639/8000000 : ℚ) by norm_num]
  exact coverp1001100011
theorem coverp100110001 : Covers (-4879761639/16000000 : ℚ) vp100110001 := join_branches bp1001100010 bp1001100011
private noncomputable def vp10011000011_0 : Blocks := edgeBlocks% "full/vectors/10011000011-V-0000.bin"
noncomputable def vp10011000011 : Blocks := vp10011000011_0
theorem coverp10011000011 : Covers (-4875761639/4000000 : ℚ) vp10011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp10011000010_0 : Blocks := edgeBlocks% "full/vectors/10011000010-V-0000.bin"
noncomputable def vp10011000010 : Blocks := vp10011000010_0
theorem coverp10011000010 : Covers (-4871761639/4000000 : ℚ) vp10011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001100001_0 : Blocks := edgeBlocks% "full/vectors/1001100001-V-0000.bin"
private noncomputable def vp1001100001_1 : Blocks := edgeBlocks% "full/vectors/1001100001-V-0001.bin"
noncomputable def vp1001100001 : Blocks := (Blocks.join vp1001100001_0 vp1001100001_1)
private theorem bp10011000010 : Branch 0 (-4871761639/8000000 : ℚ) vp1001100001 := by
  apply branch_left_normalized (c:=vp10011000010) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4871761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4871761639/4000000 : ℚ) by norm_num]
  exact coverp10011000010
private noncomputable def ep10011000011_0 : Blocks := edgeBlocks% "full/vectors/10011000011-E-0000.bin"
private noncomputable def ep10011000011_1 : Blocks := edgeBlocks% "full/vectors/10011000011-E-0001.bin"
noncomputable def ep10011000011 : Blocks := (Blocks.join ep10011000011_0 ep10011000011_1)
private theorem idp10011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001100001.list =
    C ((2:ℤ)^158) * horner X vp10011000011.list + horner X ep10011000011.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011000011 : Branch 1 (-4871761639/8000000 : ℚ) vp1001100001 := by
  apply branch_checked idp10011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-4871761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4875761639/4000000 : ℚ) by norm_num]
  exact coverp10011000011
theorem coverp1001100001 : Covers (-4871761639/8000000 : ℚ) vp1001100001 := join_branches bp10011000010 bp10011000011
private noncomputable def vp10011000001_0 : Blocks := edgeBlocks% "full/vectors/10011000001-V-0000.bin"
noncomputable def vp10011000001 : Blocks := vp10011000001_0
theorem coverp10011000001 : Covers (-4867761639/4000000 : ℚ) vp10011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp10011000000_0 : Blocks := edgeBlocks% "full/vectors/10011000000-V-0000.bin"
noncomputable def vp10011000000 : Blocks := vp10011000000_0
theorem coverp10011000000 : Covers (-4863761639/4000000 : ℚ) vp10011000000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001100000_0 : Blocks := edgeBlocks% "full/vectors/1001100000-V-0000.bin"
private noncomputable def vp1001100000_1 : Blocks := edgeBlocks% "full/vectors/1001100000-V-0001.bin"
noncomputable def vp1001100000 : Blocks := (Blocks.join vp1001100000_0 vp1001100000_1)
private theorem bp10011000000 : Branch 0 (-4863761639/8000000 : ℚ) vp1001100000 := by
  apply branch_left_normalized (c:=vp10011000000) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-4863761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4863761639/4000000 : ℚ) by norm_num]
  exact coverp10011000000
private noncomputable def ep10011000001_0 : Blocks := edgeBlocks% "full/vectors/10011000001-E-0000.bin"
private noncomputable def ep10011000001_1 : Blocks := edgeBlocks% "full/vectors/10011000001-E-0001.bin"
noncomputable def ep10011000001 : Blocks := (Blocks.join ep10011000001_0 ep10011000001_1)
private theorem idp10011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001100000.list =
    C ((2:ℤ)^158) * horner X vp10011000001.list + horner X ep10011000001.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011000001 : Branch 1 (-4863761639/8000000 : ℚ) vp1001100000 := by
  apply branch_checked idp10011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-4863761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4867761639/4000000 : ℚ) by norm_num]
  exact coverp10011000001
theorem coverp1001100000 : Covers (-4863761639/8000000 : ℚ) vp1001100000 := join_branches bp10011000000 bp10011000001
private noncomputable def vp100110000_0 : Blocks := edgeBlocks% "full/vectors/100110000-V-0000.bin"
private noncomputable def vp100110000_1 : Blocks := edgeBlocks% "full/vectors/100110000-V-0001.bin"
noncomputable def vp100110000 : Blocks := (Blocks.join vp100110000_0 vp100110000_1)
private theorem bp1001100000 : Branch 0 (-4863761639/16000000 : ℚ) vp100110000 := by
  apply branch_left_normalized (c:=vp1001100000) (k:=0) (m:=134) (by decide +kernel)
  rw [show 2*(-4863761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4863761639/8000000 : ℚ) by norm_num]
  exact coverp1001100000
private noncomputable def ep1001100001_0 : Blocks := edgeBlocks% "full/vectors/1001100001-E-0000.bin"
private noncomputable def ep1001100001_1 : Blocks := edgeBlocks% "full/vectors/1001100001-E-0001.bin"
noncomputable def ep1001100001 : Blocks := (Blocks.join ep1001100001_0 ep1001100001_1)
private theorem idp1001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100110000.list =
    C ((2:ℤ)^294) * horner X vp1001100001.list + horner X ep1001100001.list := by
  exact edge_identity (B := (2:ℤ)^469) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001100001 : Branch 1 (-4863761639/16000000 : ℚ) vp100110000 := by
  apply branch_checked idp1001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-4863761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4871761639/8000000 : ℚ) by norm_num]
  exact coverp1001100001
theorem coverp100110000 : Covers (-4863761639/16000000 : ℚ) vp100110000 := join_branches bp1001100000 bp1001100001
private noncomputable def vp10011000_0 : Blocks := edgeBlocks% "full/vectors/10011000-V-0000.bin"
private noncomputable def vp10011000_1 : Blocks := edgeBlocks% "full/vectors/10011000-V-0001.bin"
private noncomputable def vp10011000_2 : Blocks := edgeBlocks% "full/vectors/10011000-V-0002.bin"
private noncomputable def vp10011000_3 : Blocks := edgeBlocks% "full/vectors/10011000-V-0003.bin"
noncomputable def vp10011000 : Blocks := (Blocks.join (Blocks.join vp10011000_0 vp10011000_1) (Blocks.join vp10011000_2 vp10011000_3))
private theorem bp100110000 : Branch 0 (-4863761639/32000000 : ℚ) vp10011000 := by
  apply branch_left_normalized (c:=vp100110000) (k:=0) (m:=247) (by decide +kernel)
  rw [show 2*(-4863761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4863761639/16000000 : ℚ) by norm_num]
  exact coverp100110000
private noncomputable def ep100110001_0 : Blocks := edgeBlocks% "full/vectors/100110001-E-0000.bin"
private noncomputable def ep100110001_1 : Blocks := edgeBlocks% "full/vectors/100110001-E-0001.bin"
private noncomputable def ep100110001_2 : Blocks := edgeBlocks% "full/vectors/100110001-E-0002.bin"
private noncomputable def ep100110001_3 : Blocks := edgeBlocks% "full/vectors/100110001-E-0003.bin"
noncomputable def ep100110001 : Blocks := (Blocks.join (Blocks.join ep100110001_0 ep100110001_1) (Blocks.join ep100110001_2 ep100110001_3))
private theorem idp100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10011000.list =
    C ((2:ℤ)^564) * horner X vp100110001.list + horner X ep100110001.list := by
  exact edge_identity (B := (2:ℤ)^812) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100110001 : Branch 1 (-4863761639/32000000 : ℚ) vp10011000 := by
  apply branch_checked idp100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-4863761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4879761639/16000000 : ℚ) by norm_num]
  exact coverp100110001
theorem coverp10011000 : Covers (-4863761639/32000000 : ℚ) vp10011000 := join_branches bp100110000 bp100110001
private noncomputable def vp1001100_0 : Blocks := edgeBlocks% "full/vectors/1001100-V-0000.bin"
private noncomputable def vp1001100_1 : Blocks := edgeBlocks% "full/vectors/1001100-V-0001.bin"
private noncomputable def vp1001100_2 : Blocks := edgeBlocks% "full/vectors/1001100-V-0002.bin"
private noncomputable def vp1001100_3 : Blocks := edgeBlocks% "full/vectors/1001100-V-0003.bin"
private noncomputable def vp1001100_4 : Blocks := edgeBlocks% "full/vectors/1001100-V-0004.bin"
private noncomputable def vp1001100_5 : Blocks := edgeBlocks% "full/vectors/1001100-V-0005.bin"
private noncomputable def vp1001100_6 : Blocks := edgeBlocks% "full/vectors/1001100-V-0006.bin"
private noncomputable def vp1001100_7 : Blocks := edgeBlocks% "full/vectors/1001100-V-0007.bin"
noncomputable def vp1001100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1001100_0 vp1001100_1) (Blocks.join vp1001100_2 vp1001100_3)) (Blocks.join (Blocks.join vp1001100_4 vp1001100_5) (Blocks.join vp1001100_6 vp1001100_7)))
private theorem bp10011000 : Branch 0 (-4863761639/64000000 : ℚ) vp1001100 := by
  apply branch_left_normalized (c:=vp10011000) (k:=0) (m:=471) (by decide +kernel)
  rw [show 2*(-4863761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4863761639/32000000 : ℚ) by norm_num]
  exact coverp10011000
private noncomputable def ep10011001_0 : Blocks := edgeBlocks% "full/vectors/10011001-E-0000.bin"
private noncomputable def ep10011001_1 : Blocks := edgeBlocks% "full/vectors/10011001-E-0001.bin"
private noncomputable def ep10011001_2 : Blocks := edgeBlocks% "full/vectors/10011001-E-0002.bin"
private noncomputable def ep10011001_3 : Blocks := edgeBlocks% "full/vectors/10011001-E-0003.bin"
private noncomputable def ep10011001_4 : Blocks := edgeBlocks% "full/vectors/10011001-E-0004.bin"
private noncomputable def ep10011001_5 : Blocks := edgeBlocks% "full/vectors/10011001-E-0005.bin"
private noncomputable def ep10011001_6 : Blocks := edgeBlocks% "full/vectors/10011001-E-0006.bin"
private noncomputable def ep10011001_7 : Blocks := edgeBlocks% "full/vectors/10011001-E-0007.bin"
noncomputable def ep10011001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10011001_0 ep10011001_1) (Blocks.join ep10011001_2 ep10011001_3)) (Blocks.join (Blocks.join ep10011001_4 ep10011001_5) (Blocks.join ep10011001_6 ep10011001_7)))
private theorem idp10011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001100.list =
    C ((2:ℤ)^1099) * horner X vp10011001.list + horner X ep10011001.list := by
  exact edge_identity (B := (2:ℤ)^1492) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10011001 : Branch 1 (-4863761639/64000000 : ℚ) vp1001100 := by
  apply branch_checked idp10011001 (by positivity) (by decide +kernel)
  rw [show 2*(-4863761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4895761639/32000000 : ℚ) by norm_num]
  exact coverp10011001
theorem coverp1001100 : Covers (-4863761639/64000000 : ℚ) vp1001100 := join_branches bp10011000 bp10011001
private noncomputable def vp100110_0 : Blocks := edgeBlocks% "full/vectors/100110-V-0000.bin"
private noncomputable def vp100110_1 : Blocks := edgeBlocks% "full/vectors/100110-V-0001.bin"
private noncomputable def vp100110_2 : Blocks := edgeBlocks% "full/vectors/100110-V-0002.bin"
private noncomputable def vp100110_3 : Blocks := edgeBlocks% "full/vectors/100110-V-0003.bin"
private noncomputable def vp100110_4 : Blocks := edgeBlocks% "full/vectors/100110-V-0004.bin"
private noncomputable def vp100110_5 : Blocks := edgeBlocks% "full/vectors/100110-V-0005.bin"
private noncomputable def vp100110_6 : Blocks := edgeBlocks% "full/vectors/100110-V-0006.bin"
private noncomputable def vp100110_7 : Blocks := edgeBlocks% "full/vectors/100110-V-0007.bin"
private noncomputable def vp100110_8 : Blocks := edgeBlocks% "full/vectors/100110-V-0008.bin"
private noncomputable def vp100110_9 : Blocks := edgeBlocks% "full/vectors/100110-V-0009.bin"
private noncomputable def vp100110_10 : Blocks := edgeBlocks% "full/vectors/100110-V-0010.bin"
private noncomputable def vp100110_11 : Blocks := edgeBlocks% "full/vectors/100110-V-0011.bin"
private noncomputable def vp100110_12 : Blocks := edgeBlocks% "full/vectors/100110-V-0012.bin"
private noncomputable def vp100110_13 : Blocks := edgeBlocks% "full/vectors/100110-V-0013.bin"
noncomputable def vp100110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp100110_0 (Blocks.join vp100110_1 vp100110_2)) (Blocks.join (Blocks.join vp100110_3 vp100110_4) (Blocks.join vp100110_5 vp100110_6))) (Blocks.join (Blocks.join vp100110_7 (Blocks.join vp100110_8 vp100110_9)) (Blocks.join (Blocks.join vp100110_10 vp100110_11) (Blocks.join vp100110_12 vp100110_13))))
private theorem bp1001100 : Branch 0 (-4863761639/128000000 : ℚ) vp100110 := by
  apply branch_left_normalized (c:=vp1001100) (k:=0) (m:=913) (by decide +kernel)
  rw [show 2*(-4863761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-4863761639/64000000 : ℚ) by norm_num]
  exact coverp1001100
private noncomputable def ep1001101_0 : Blocks := edgeBlocks% "full/vectors/1001101-E-0000.bin"
private noncomputable def ep1001101_1 : Blocks := edgeBlocks% "full/vectors/1001101-E-0001.bin"
private noncomputable def ep1001101_2 : Blocks := edgeBlocks% "full/vectors/1001101-E-0002.bin"
private noncomputable def ep1001101_3 : Blocks := edgeBlocks% "full/vectors/1001101-E-0003.bin"
private noncomputable def ep1001101_4 : Blocks := edgeBlocks% "full/vectors/1001101-E-0004.bin"
private noncomputable def ep1001101_5 : Blocks := edgeBlocks% "full/vectors/1001101-E-0005.bin"
private noncomputable def ep1001101_6 : Blocks := edgeBlocks% "full/vectors/1001101-E-0006.bin"
private noncomputable def ep1001101_7 : Blocks := edgeBlocks% "full/vectors/1001101-E-0007.bin"
private noncomputable def ep1001101_8 : Blocks := edgeBlocks% "full/vectors/1001101-E-0008.bin"
private noncomputable def ep1001101_9 : Blocks := edgeBlocks% "full/vectors/1001101-E-0009.bin"
private noncomputable def ep1001101_10 : Blocks := edgeBlocks% "full/vectors/1001101-E-0010.bin"
private noncomputable def ep1001101_11 : Blocks := edgeBlocks% "full/vectors/1001101-E-0011.bin"
private noncomputable def ep1001101_12 : Blocks := edgeBlocks% "full/vectors/1001101-E-0012.bin"
private noncomputable def ep1001101_13 : Blocks := edgeBlocks% "full/vectors/1001101-E-0013.bin"
noncomputable def ep1001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1001101_0 (Blocks.join ep1001101_1 ep1001101_2)) (Blocks.join (Blocks.join ep1001101_3 ep1001101_4) (Blocks.join ep1001101_5 ep1001101_6))) (Blocks.join (Blocks.join ep1001101_7 (Blocks.join ep1001101_8 ep1001101_9)) (Blocks.join (Blocks.join ep1001101_10 ep1001101_11) (Blocks.join ep1001101_12 ep1001101_13))))
private theorem idp1001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100110.list =
    C ((2:ℤ)^2148) * horner X vp1001101.list + horner X ep1001101.list := by
  exact edge_identity (B := (2:ℤ)^2829) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001101 : Branch 1 (-4863761639/128000000 : ℚ) vp100110 := by
  apply branch_checked idp1001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4863761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-4927761639/64000000 : ℚ) by norm_num]
  exact coverp1001101
theorem coverp100110 : Covers (-4863761639/128000000 : ℚ) vp100110 := join_branches bp1001100 bp1001101
private noncomputable def vp10011_0 : Blocks := edgeBlocks% "full/vectors/10011-V-0000.bin"
private noncomputable def vp10011_1 : Blocks := edgeBlocks% "full/vectors/10011-V-0001.bin"
private noncomputable def vp10011_2 : Blocks := edgeBlocks% "full/vectors/10011-V-0002.bin"
private noncomputable def vp10011_3 : Blocks := edgeBlocks% "full/vectors/10011-V-0003.bin"
private noncomputable def vp10011_4 : Blocks := edgeBlocks% "full/vectors/10011-V-0004.bin"
private noncomputable def vp10011_5 : Blocks := edgeBlocks% "full/vectors/10011-V-0005.bin"
private noncomputable def vp10011_6 : Blocks := edgeBlocks% "full/vectors/10011-V-0006.bin"
private noncomputable def vp10011_7 : Blocks := edgeBlocks% "full/vectors/10011-V-0007.bin"
private noncomputable def vp10011_8 : Blocks := edgeBlocks% "full/vectors/10011-V-0008.bin"
private noncomputable def vp10011_9 : Blocks := edgeBlocks% "full/vectors/10011-V-0009.bin"
private noncomputable def vp10011_10 : Blocks := edgeBlocks% "full/vectors/10011-V-0010.bin"
private noncomputable def vp10011_11 : Blocks := edgeBlocks% "full/vectors/10011-V-0011.bin"
private noncomputable def vp10011_12 : Blocks := edgeBlocks% "full/vectors/10011-V-0012.bin"
private noncomputable def vp10011_13 : Blocks := edgeBlocks% "full/vectors/10011-V-0013.bin"
private noncomputable def vp10011_14 : Blocks := edgeBlocks% "full/vectors/10011-V-0014.bin"
private noncomputable def vp10011_15 : Blocks := edgeBlocks% "full/vectors/10011-V-0015.bin"
private noncomputable def vp10011_16 : Blocks := edgeBlocks% "full/vectors/10011-V-0016.bin"
private noncomputable def vp10011_17 : Blocks := edgeBlocks% "full/vectors/10011-V-0017.bin"
private noncomputable def vp10011_18 : Blocks := edgeBlocks% "full/vectors/10011-V-0018.bin"
private noncomputable def vp10011_19 : Blocks := edgeBlocks% "full/vectors/10011-V-0019.bin"
private noncomputable def vp10011_20 : Blocks := edgeBlocks% "full/vectors/10011-V-0020.bin"
private noncomputable def vp10011_21 : Blocks := edgeBlocks% "full/vectors/10011-V-0021.bin"
private noncomputable def vp10011_22 : Blocks := edgeBlocks% "full/vectors/10011-V-0022.bin"
private noncomputable def vp10011_23 : Blocks := edgeBlocks% "full/vectors/10011-V-0023.bin"
private noncomputable def vp10011_24 : Blocks := edgeBlocks% "full/vectors/10011-V-0024.bin"
private noncomputable def vp10011_25 : Blocks := edgeBlocks% "full/vectors/10011-V-0025.bin"
private noncomputable def vp10011_26 : Blocks := edgeBlocks% "full/vectors/10011-V-0026.bin"
noncomputable def vp10011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp10011_0 (Blocks.join vp10011_1 vp10011_2)) (Blocks.join vp10011_3 (Blocks.join vp10011_4 vp10011_5))) (Blocks.join (Blocks.join vp10011_6 (Blocks.join vp10011_7 vp10011_8)) (Blocks.join (Blocks.join vp10011_9 vp10011_10) (Blocks.join vp10011_11 vp10011_12)))) (Blocks.join (Blocks.join (Blocks.join vp10011_13 (Blocks.join vp10011_14 vp10011_15)) (Blocks.join (Blocks.join vp10011_16 vp10011_17) (Blocks.join vp10011_18 vp10011_19))) (Blocks.join (Blocks.join vp10011_20 (Blocks.join vp10011_21 vp10011_22)) (Blocks.join (Blocks.join vp10011_23 vp10011_24) (Blocks.join vp10011_25 vp10011_26)))))
private theorem bp100110 : Branch 0 (-4863761639/256000000 : ℚ) vp10011 := by
  apply branch_left_normalized (c:=vp100110) (k:=0) (m:=1778) (by decide +kernel)
  rw [show 2*(-4863761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-4863761639/128000000 : ℚ) by norm_num]
  exact coverp100110
private noncomputable def ep100111_0 : Blocks := edgeBlocks% "full/vectors/100111-E-0000.bin"
private noncomputable def ep100111_1 : Blocks := edgeBlocks% "full/vectors/100111-E-0001.bin"
private noncomputable def ep100111_2 : Blocks := edgeBlocks% "full/vectors/100111-E-0002.bin"
private noncomputable def ep100111_3 : Blocks := edgeBlocks% "full/vectors/100111-E-0003.bin"
private noncomputable def ep100111_4 : Blocks := edgeBlocks% "full/vectors/100111-E-0004.bin"
private noncomputable def ep100111_5 : Blocks := edgeBlocks% "full/vectors/100111-E-0005.bin"
private noncomputable def ep100111_6 : Blocks := edgeBlocks% "full/vectors/100111-E-0006.bin"
private noncomputable def ep100111_7 : Blocks := edgeBlocks% "full/vectors/100111-E-0007.bin"
private noncomputable def ep100111_8 : Blocks := edgeBlocks% "full/vectors/100111-E-0008.bin"
private noncomputable def ep100111_9 : Blocks := edgeBlocks% "full/vectors/100111-E-0009.bin"
private noncomputable def ep100111_10 : Blocks := edgeBlocks% "full/vectors/100111-E-0010.bin"
private noncomputable def ep100111_11 : Blocks := edgeBlocks% "full/vectors/100111-E-0011.bin"
private noncomputable def ep100111_12 : Blocks := edgeBlocks% "full/vectors/100111-E-0012.bin"
private noncomputable def ep100111_13 : Blocks := edgeBlocks% "full/vectors/100111-E-0013.bin"
private noncomputable def ep100111_14 : Blocks := edgeBlocks% "full/vectors/100111-E-0014.bin"
private noncomputable def ep100111_15 : Blocks := edgeBlocks% "full/vectors/100111-E-0015.bin"
private noncomputable def ep100111_16 : Blocks := edgeBlocks% "full/vectors/100111-E-0016.bin"
private noncomputable def ep100111_17 : Blocks := edgeBlocks% "full/vectors/100111-E-0017.bin"
private noncomputable def ep100111_18 : Blocks := edgeBlocks% "full/vectors/100111-E-0018.bin"
private noncomputable def ep100111_19 : Blocks := edgeBlocks% "full/vectors/100111-E-0019.bin"
private noncomputable def ep100111_20 : Blocks := edgeBlocks% "full/vectors/100111-E-0020.bin"
private noncomputable def ep100111_21 : Blocks := edgeBlocks% "full/vectors/100111-E-0021.bin"
private noncomputable def ep100111_22 : Blocks := edgeBlocks% "full/vectors/100111-E-0022.bin"
private noncomputable def ep100111_23 : Blocks := edgeBlocks% "full/vectors/100111-E-0023.bin"
private noncomputable def ep100111_24 : Blocks := edgeBlocks% "full/vectors/100111-E-0024.bin"
private noncomputable def ep100111_25 : Blocks := edgeBlocks% "full/vectors/100111-E-0025.bin"
private noncomputable def ep100111_26 : Blocks := edgeBlocks% "full/vectors/100111-E-0026.bin"
noncomputable def ep100111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep100111_0 (Blocks.join ep100111_1 ep100111_2)) (Blocks.join ep100111_3 (Blocks.join ep100111_4 ep100111_5))) (Blocks.join (Blocks.join ep100111_6 (Blocks.join ep100111_7 ep100111_8)) (Blocks.join (Blocks.join ep100111_9 ep100111_10) (Blocks.join ep100111_11 ep100111_12)))) (Blocks.join (Blocks.join (Blocks.join ep100111_13 (Blocks.join ep100111_14 ep100111_15)) (Blocks.join (Blocks.join ep100111_16 ep100111_17) (Blocks.join ep100111_18 ep100111_19))) (Blocks.join (Blocks.join ep100111_20 (Blocks.join ep100111_21 ep100111_22)) (Blocks.join (Blocks.join ep100111_23 ep100111_24) (Blocks.join ep100111_25 ep100111_26)))))
private def ptsp100111 : List ℤ := [((2:ℤ)^3491+0),((2:ℤ)^3491+1)]
private theorem boundp100111 : 2^vp10011.size*absSum vp10011.list + ((2:ℤ)^4180*absSum vp100111.list+absSum ep100111.list) < (2:ℤ)^5417 := by decide +kernel
private theorem pointp100111_0 : fastHom 1 ((2:ℤ)^3491+0) vp10011 = ((2:ℤ)^4180)*vp100111.subst ((2:ℤ)^3491+0)+ep100111.subst ((2:ℤ)^3491+0) := by decide +kernel
private theorem pointp100111_1 : fastHom 1 ((2:ℤ)^3491+1) vp10011 = ((2:ℤ)^4180)*vp100111.subst ((2:ℤ)^3491+1)+ep100111.subst ((2:ℤ)^3491+1) := by decide +kernel
private theorem checkp100111 (x:ℤ) (hx:x ∈ ptsp100111) : fastHom 1 x vp10011 = ((2:ℤ)^4180)*vp100111.subst x+ep100111.subst x := by
  simp only [ptsp100111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp100111_0
  · exact pointp100111_1
private theorem idp100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10011.list =
    C ((2:ℤ)^4180) * horner X vp100111.list + horner X ep100111.list := by
  apply edge_identity (B := (2:ℤ)^5417) (by decide) (by positivity) (by positivity) boundp100111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp100111 (by decide +kernel)
  · have h : ptsp100111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp100111.trans_le (by decide +kernel)
  · exact checkp100111
private theorem bp100111 : Branch 1 (-4863761639/256000000 : ℚ) vp10011 := by
  apply branch_checked idp100111 (by positivity) (by decide +kernel)
  rw [show 2*(-4863761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-4991761639/128000000 : ℚ) by norm_num]
  exact coverp100111
theorem coverp10011 : Covers (-4863761639/256000000 : ℚ) vp10011 := join_branches bp100110 bp100111
end NextProof.EdgeFull

