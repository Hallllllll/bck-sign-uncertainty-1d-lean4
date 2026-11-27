import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp10001111111_0 : Blocks := edgeBlocks% "full/vectors/10001111111-V-0000.bin"
noncomputable def vp10001111111 : Blocks := vp10001111111_0
theorem coverp10001111111 : Covers (-4603761639/4000000 : ℚ) vp10001111111 := cover_leaf (by decide +kernel)
private noncomputable def vp10001111110_0 : Blocks := edgeBlocks% "full/vectors/10001111110-V-0000.bin"
noncomputable def vp10001111110 : Blocks := vp10001111110_0
theorem coverp10001111110 : Covers (-4599761639/4000000 : ℚ) vp10001111110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000111111_0 : Blocks := edgeBlocks% "full/vectors/1000111111-V-0000.bin"
private noncomputable def vp1000111111_1 : Blocks := edgeBlocks% "full/vectors/1000111111-V-0001.bin"
noncomputable def vp1000111111 : Blocks := (Blocks.join vp1000111111_0 vp1000111111_1)
private theorem bp10001111110 : Branch 0 (-4599761639/8000000 : ℚ) vp1000111111 := by
  apply branch_left_normalized (c:=vp10001111110) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4599761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4599761639/4000000 : ℚ) by norm_num]
  exact coverp10001111110
private noncomputable def ep10001111111_0 : Blocks := edgeBlocks% "full/vectors/10001111111-E-0000.bin"
private noncomputable def ep10001111111_1 : Blocks := edgeBlocks% "full/vectors/10001111111-E-0001.bin"
noncomputable def ep10001111111 : Blocks := (Blocks.join ep10001111111_0 ep10001111111_1)
private theorem idp10001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000111111.list =
    C ((2:ℤ)^159) * horner X vp10001111111.list + horner X ep10001111111.list := by
  exact edge_identity (B := (2:ℤ)^298) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001111111 : Branch 1 (-4599761639/8000000 : ℚ) vp1000111111 := by
  apply branch_checked idp10001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-4599761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4603761639/4000000 : ℚ) by norm_num]
  exact coverp10001111111
theorem coverp1000111111 : Covers (-4599761639/8000000 : ℚ) vp1000111111 := join_branches bp10001111110 bp10001111111
private noncomputable def vp10001111101_0 : Blocks := edgeBlocks% "full/vectors/10001111101-V-0000.bin"
noncomputable def vp10001111101 : Blocks := vp10001111101_0
theorem coverp10001111101 : Covers (-4595761639/4000000 : ℚ) vp10001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp10001111100_0 : Blocks := edgeBlocks% "full/vectors/10001111100-V-0000.bin"
noncomputable def vp10001111100 : Blocks := vp10001111100_0
theorem coverp10001111100 : Covers (-4591761639/4000000 : ℚ) vp10001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000111110_0 : Blocks := edgeBlocks% "full/vectors/1000111110-V-0000.bin"
private noncomputable def vp1000111110_1 : Blocks := edgeBlocks% "full/vectors/1000111110-V-0001.bin"
noncomputable def vp1000111110 : Blocks := (Blocks.join vp1000111110_0 vp1000111110_1)
private theorem bp10001111100 : Branch 0 (-4591761639/8000000 : ℚ) vp1000111110 := by
  apply branch_left_normalized (c:=vp10001111100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-4591761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4591761639/4000000 : ℚ) by norm_num]
  exact coverp10001111100
private noncomputable def ep10001111101_0 : Blocks := edgeBlocks% "full/vectors/10001111101-E-0000.bin"
private noncomputable def ep10001111101_1 : Blocks := edgeBlocks% "full/vectors/10001111101-E-0001.bin"
noncomputable def ep10001111101 : Blocks := (Blocks.join ep10001111101_0 ep10001111101_1)
private theorem idp10001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000111110.list =
    C ((2:ℤ)^158) * horner X vp10001111101.list + horner X ep10001111101.list := by
  exact edge_identity (B := (2:ℤ)^294) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001111101 : Branch 1 (-4591761639/8000000 : ℚ) vp1000111110 := by
  apply branch_checked idp10001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-4591761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4595761639/4000000 : ℚ) by norm_num]
  exact coverp10001111101
theorem coverp1000111110 : Covers (-4591761639/8000000 : ℚ) vp1000111110 := join_branches bp10001111100 bp10001111101
private noncomputable def vp100011111_0 : Blocks := edgeBlocks% "full/vectors/100011111-V-0000.bin"
private noncomputable def vp100011111_1 : Blocks := edgeBlocks% "full/vectors/100011111-V-0001.bin"
noncomputable def vp100011111 : Blocks := (Blocks.join vp100011111_0 vp100011111_1)
private theorem bp1000111110 : Branch 0 (-4591761639/16000000 : ℚ) vp100011111 := by
  apply branch_left_normalized (c:=vp1000111110) (k:=0) (m:=135) (by decide +kernel)
  rw [show 2*(-4591761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4591761639/8000000 : ℚ) by norm_num]
  exact coverp1000111110
private noncomputable def ep1000111111_0 : Blocks := edgeBlocks% "full/vectors/1000111111-E-0000.bin"
private noncomputable def ep1000111111_1 : Blocks := edgeBlocks% "full/vectors/1000111111-E-0001.bin"
noncomputable def ep1000111111 : Blocks := (Blocks.join ep1000111111_0 ep1000111111_1)
private theorem idp1000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100011111.list =
    C ((2:ℤ)^295) * horner X vp1000111111.list + horner X ep1000111111.list := by
  exact edge_identity (B := (2:ℤ)^472) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000111111 : Branch 1 (-4591761639/16000000 : ℚ) vp100011111 := by
  apply branch_checked idp1000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-4591761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4599761639/8000000 : ℚ) by norm_num]
  exact coverp1000111111
theorem coverp100011111 : Covers (-4591761639/16000000 : ℚ) vp100011111 := join_branches bp1000111110 bp1000111111
private noncomputable def vp1000111101_0 : Blocks := edgeBlocks% "full/vectors/1000111101-V-0000.bin"
private noncomputable def vp1000111101_1 : Blocks := edgeBlocks% "full/vectors/1000111101-V-0001.bin"
noncomputable def vp1000111101 : Blocks := (Blocks.join vp1000111101_0 vp1000111101_1)
theorem coverp1000111101 : Covers (-4583761639/8000000 : ℚ) vp1000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp1000111100_0 : Blocks := edgeBlocks% "full/vectors/1000111100-V-0000.bin"
private noncomputable def vp1000111100_1 : Blocks := edgeBlocks% "full/vectors/1000111100-V-0001.bin"
noncomputable def vp1000111100 : Blocks := (Blocks.join vp1000111100_0 vp1000111100_1)
theorem coverp1000111100 : Covers (-4575761639/8000000 : ℚ) vp1000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp100011110_0 : Blocks := edgeBlocks% "full/vectors/100011110-V-0000.bin"
private noncomputable def vp100011110_1 : Blocks := edgeBlocks% "full/vectors/100011110-V-0001.bin"
noncomputable def vp100011110 : Blocks := (Blocks.join vp100011110_0 vp100011110_1)
private theorem bp1000111100 : Branch 0 (-4575761639/16000000 : ℚ) vp100011110 := by
  apply branch_left_normalized (c:=vp1000111100) (k:=0) (m:=134) (by decide +kernel)
  rw [show 2*(-4575761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4575761639/8000000 : ℚ) by norm_num]
  exact coverp1000111100
private noncomputable def ep1000111101_0 : Blocks := edgeBlocks% "full/vectors/1000111101-E-0000.bin"
private noncomputable def ep1000111101_1 : Blocks := edgeBlocks% "full/vectors/1000111101-E-0001.bin"
noncomputable def ep1000111101 : Blocks := (Blocks.join ep1000111101_0 ep1000111101_1)
private theorem idp1000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100011110.list =
    C ((2:ℤ)^296) * horner X vp1000111101.list + horner X ep1000111101.list := by
  exact edge_identity (B := (2:ℤ)^469) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000111101 : Branch 1 (-4575761639/16000000 : ℚ) vp100011110 := by
  apply branch_checked idp1000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-4575761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4583761639/8000000 : ℚ) by norm_num]
  exact coverp1000111101
theorem coverp100011110 : Covers (-4575761639/16000000 : ℚ) vp100011110 := join_branches bp1000111100 bp1000111101
private noncomputable def vp10001111_0 : Blocks := edgeBlocks% "full/vectors/10001111-V-0000.bin"
private noncomputable def vp10001111_1 : Blocks := edgeBlocks% "full/vectors/10001111-V-0001.bin"
private noncomputable def vp10001111_2 : Blocks := edgeBlocks% "full/vectors/10001111-V-0002.bin"
private noncomputable def vp10001111_3 : Blocks := edgeBlocks% "full/vectors/10001111-V-0003.bin"
noncomputable def vp10001111 : Blocks := (Blocks.join (Blocks.join vp10001111_0 vp10001111_1) (Blocks.join vp10001111_2 vp10001111_3))
private theorem bp100011110 : Branch 0 (-4575761639/32000000 : ℚ) vp10001111 := by
  apply branch_left_normalized (c:=vp100011110) (k:=0) (m:=250) (by decide +kernel)
  rw [show 2*(-4575761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4575761639/16000000 : ℚ) by norm_num]
  exact coverp100011110
private noncomputable def ep100011111_0 : Blocks := edgeBlocks% "full/vectors/100011111-E-0000.bin"
private noncomputable def ep100011111_1 : Blocks := edgeBlocks% "full/vectors/100011111-E-0001.bin"
private noncomputable def ep100011111_2 : Blocks := edgeBlocks% "full/vectors/100011111-E-0002.bin"
private noncomputable def ep100011111_3 : Blocks := edgeBlocks% "full/vectors/100011111-E-0003.bin"
noncomputable def ep100011111 : Blocks := (Blocks.join (Blocks.join ep100011111_0 ep100011111_1) (Blocks.join ep100011111_2 ep100011111_3))
private theorem idp100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10001111.list =
    C ((2:ℤ)^571) * horner X vp100011111.list + horner X ep100011111.list := by
  exact edge_identity (B := (2:ℤ)^822) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100011111 : Branch 1 (-4575761639/32000000 : ℚ) vp10001111 := by
  apply branch_checked idp100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-4575761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4591761639/16000000 : ℚ) by norm_num]
  exact coverp100011111
theorem coverp10001111 : Covers (-4575761639/32000000 : ℚ) vp10001111 := join_branches bp100011110 bp100011111
private noncomputable def vp1000111011_0 : Blocks := edgeBlocks% "full/vectors/1000111011-V-0000.bin"
private noncomputable def vp1000111011_1 : Blocks := edgeBlocks% "full/vectors/1000111011-V-0001.bin"
noncomputable def vp1000111011 : Blocks := (Blocks.join vp1000111011_0 vp1000111011_1)
theorem coverp1000111011 : Covers (-4567761639/8000000 : ℚ) vp1000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp1000111010_0 : Blocks := edgeBlocks% "full/vectors/1000111010-V-0000.bin"
private noncomputable def vp1000111010_1 : Blocks := edgeBlocks% "full/vectors/1000111010-V-0001.bin"
noncomputable def vp1000111010 : Blocks := (Blocks.join vp1000111010_0 vp1000111010_1)
theorem coverp1000111010 : Covers (-4559761639/8000000 : ℚ) vp1000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp100011101_0 : Blocks := edgeBlocks% "full/vectors/100011101-V-0000.bin"
private noncomputable def vp100011101_1 : Blocks := edgeBlocks% "full/vectors/100011101-V-0001.bin"
noncomputable def vp100011101 : Blocks := (Blocks.join vp100011101_0 vp100011101_1)
private theorem bp1000111010 : Branch 0 (-4559761639/16000000 : ℚ) vp100011101 := by
  apply branch_left_normalized (c:=vp1000111010) (k:=0) (m:=134) (by decide +kernel)
  rw [show 2*(-4559761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4559761639/8000000 : ℚ) by norm_num]
  exact coverp1000111010
private noncomputable def ep1000111011_0 : Blocks := edgeBlocks% "full/vectors/1000111011-E-0000.bin"
private noncomputable def ep1000111011_1 : Blocks := edgeBlocks% "full/vectors/1000111011-E-0001.bin"
noncomputable def ep1000111011 : Blocks := (Blocks.join ep1000111011_0 ep1000111011_1)
private theorem idp1000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100011101.list =
    C ((2:ℤ)^297) * horner X vp1000111011.list + horner X ep1000111011.list := by
  exact edge_identity (B := (2:ℤ)^468) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000111011 : Branch 1 (-4559761639/16000000 : ℚ) vp100011101 := by
  apply branch_checked idp1000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-4559761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4567761639/8000000 : ℚ) by norm_num]
  exact coverp1000111011
theorem coverp100011101 : Covers (-4559761639/16000000 : ℚ) vp100011101 := join_branches bp1000111010 bp1000111011
private noncomputable def vp1000111001_0 : Blocks := edgeBlocks% "full/vectors/1000111001-V-0000.bin"
private noncomputable def vp1000111001_1 : Blocks := edgeBlocks% "full/vectors/1000111001-V-0001.bin"
noncomputable def vp1000111001 : Blocks := (Blocks.join vp1000111001_0 vp1000111001_1)
theorem coverp1000111001 : Covers (-4551761639/8000000 : ℚ) vp1000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp1000111000_0 : Blocks := edgeBlocks% "full/vectors/1000111000-V-0000.bin"
private noncomputable def vp1000111000_1 : Blocks := edgeBlocks% "full/vectors/1000111000-V-0001.bin"
noncomputable def vp1000111000 : Blocks := (Blocks.join vp1000111000_0 vp1000111000_1)
theorem coverp1000111000 : Covers (-4543761639/8000000 : ℚ) vp1000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp100011100_0 : Blocks := edgeBlocks% "full/vectors/100011100-V-0000.bin"
private noncomputable def vp100011100_1 : Blocks := edgeBlocks% "full/vectors/100011100-V-0001.bin"
noncomputable def vp100011100 : Blocks := (Blocks.join vp100011100_0 vp100011100_1)
private theorem bp1000111000 : Branch 0 (-4543761639/16000000 : ℚ) vp100011100 := by
  apply branch_left_normalized (c:=vp1000111000) (k:=0) (m:=135) (by decide +kernel)
  rw [show 2*(-4543761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4543761639/8000000 : ℚ) by norm_num]
  exact coverp1000111000
private noncomputable def ep1000111001_0 : Blocks := edgeBlocks% "full/vectors/1000111001-E-0000.bin"
private noncomputable def ep1000111001_1 : Blocks := edgeBlocks% "full/vectors/1000111001-E-0001.bin"
noncomputable def ep1000111001 : Blocks := (Blocks.join ep1000111001_0 ep1000111001_1)
private theorem idp1000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100011100.list =
    C ((2:ℤ)^300) * horner X vp1000111001.list + horner X ep1000111001.list := by
  exact edge_identity (B := (2:ℤ)^472) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000111001 : Branch 1 (-4543761639/16000000 : ℚ) vp100011100 := by
  apply branch_checked idp1000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-4543761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4551761639/8000000 : ℚ) by norm_num]
  exact coverp1000111001
theorem coverp100011100 : Covers (-4543761639/16000000 : ℚ) vp100011100 := join_branches bp1000111000 bp1000111001
private noncomputable def vp10001110_0 : Blocks := edgeBlocks% "full/vectors/10001110-V-0000.bin"
private noncomputable def vp10001110_1 : Blocks := edgeBlocks% "full/vectors/10001110-V-0001.bin"
private noncomputable def vp10001110_2 : Blocks := edgeBlocks% "full/vectors/10001110-V-0002.bin"
private noncomputable def vp10001110_3 : Blocks := edgeBlocks% "full/vectors/10001110-V-0003.bin"
noncomputable def vp10001110 : Blocks := (Blocks.join (Blocks.join vp10001110_0 vp10001110_1) (Blocks.join vp10001110_2 vp10001110_3))
private theorem bp100011100 : Branch 0 (-4543761639/32000000 : ℚ) vp10001110 := by
  apply branch_left_normalized (c:=vp100011100) (k:=0) (m:=252) (by decide +kernel)
  rw [show 2*(-4543761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4543761639/16000000 : ℚ) by norm_num]
  exact coverp100011100
private noncomputable def ep100011101_0 : Blocks := edgeBlocks% "full/vectors/100011101-E-0000.bin"
private noncomputable def ep100011101_1 : Blocks := edgeBlocks% "full/vectors/100011101-E-0001.bin"
private noncomputable def ep100011101_2 : Blocks := edgeBlocks% "full/vectors/100011101-E-0002.bin"
private noncomputable def ep100011101_3 : Blocks := edgeBlocks% "full/vectors/100011101-E-0003.bin"
noncomputable def ep100011101 : Blocks := (Blocks.join (Blocks.join ep100011101_0 ep100011101_1) (Blocks.join ep100011101_2 ep100011101_3))
private theorem idp100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10001110.list =
    C ((2:ℤ)^578) * horner X vp100011101.list + horner X ep100011101.list := by
  exact edge_identity (B := (2:ℤ)^827) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100011101 : Branch 1 (-4543761639/32000000 : ℚ) vp10001110 := by
  apply branch_checked idp100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-4543761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4559761639/16000000 : ℚ) by norm_num]
  exact coverp100011101
theorem coverp10001110 : Covers (-4543761639/32000000 : ℚ) vp10001110 := join_branches bp100011100 bp100011101
private noncomputable def vp1000111_0 : Blocks := edgeBlocks% "full/vectors/1000111-V-0000.bin"
private noncomputable def vp1000111_1 : Blocks := edgeBlocks% "full/vectors/1000111-V-0001.bin"
private noncomputable def vp1000111_2 : Blocks := edgeBlocks% "full/vectors/1000111-V-0002.bin"
private noncomputable def vp1000111_3 : Blocks := edgeBlocks% "full/vectors/1000111-V-0003.bin"
private noncomputable def vp1000111_4 : Blocks := edgeBlocks% "full/vectors/1000111-V-0004.bin"
private noncomputable def vp1000111_5 : Blocks := edgeBlocks% "full/vectors/1000111-V-0005.bin"
private noncomputable def vp1000111_6 : Blocks := edgeBlocks% "full/vectors/1000111-V-0006.bin"
private noncomputable def vp1000111_7 : Blocks := edgeBlocks% "full/vectors/1000111-V-0007.bin"
noncomputable def vp1000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1000111_0 vp1000111_1) (Blocks.join vp1000111_2 vp1000111_3)) (Blocks.join (Blocks.join vp1000111_4 vp1000111_5) (Blocks.join vp1000111_6 vp1000111_7)))
private theorem bp10001110 : Branch 0 (-4543761639/64000000 : ℚ) vp1000111 := by
  apply branch_left_normalized (c:=vp10001110) (k:=0) (m:=483) (by decide +kernel)
  rw [show 2*(-4543761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4543761639/32000000 : ℚ) by norm_num]
  exact coverp10001110
private noncomputable def ep10001111_0 : Blocks := edgeBlocks% "full/vectors/10001111-E-0000.bin"
private noncomputable def ep10001111_1 : Blocks := edgeBlocks% "full/vectors/10001111-E-0001.bin"
private noncomputable def ep10001111_2 : Blocks := edgeBlocks% "full/vectors/10001111-E-0002.bin"
private noncomputable def ep10001111_3 : Blocks := edgeBlocks% "full/vectors/10001111-E-0003.bin"
private noncomputable def ep10001111_4 : Blocks := edgeBlocks% "full/vectors/10001111-E-0004.bin"
private noncomputable def ep10001111_5 : Blocks := edgeBlocks% "full/vectors/10001111-E-0005.bin"
private noncomputable def ep10001111_6 : Blocks := edgeBlocks% "full/vectors/10001111-E-0006.bin"
private noncomputable def ep10001111_7 : Blocks := edgeBlocks% "full/vectors/10001111-E-0007.bin"
noncomputable def ep10001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10001111_0 ep10001111_1) (Blocks.join ep10001111_2 ep10001111_3)) (Blocks.join (Blocks.join ep10001111_4 ep10001111_5) (Blocks.join ep10001111_6 ep10001111_7)))
private theorem idp10001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000111.list =
    C ((2:ℤ)^1127) * horner X vp10001111.list + horner X ep10001111.list := by
  exact edge_identity (B := (2:ℤ)^1530) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001111 : Branch 1 (-4543761639/64000000 : ℚ) vp1000111 := by
  apply branch_checked idp10001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4543761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4575761639/32000000 : ℚ) by norm_num]
  exact coverp10001111
theorem coverp1000111 : Covers (-4543761639/64000000 : ℚ) vp1000111 := join_branches bp10001110 bp10001111
private noncomputable def vp1000110111_0 : Blocks := edgeBlocks% "full/vectors/1000110111-V-0000.bin"
private noncomputable def vp1000110111_1 : Blocks := edgeBlocks% "full/vectors/1000110111-V-0001.bin"
noncomputable def vp1000110111 : Blocks := (Blocks.join vp1000110111_0 vp1000110111_1)
theorem coverp1000110111 : Covers (-4535761639/8000000 : ℚ) vp1000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp10001101101_0 : Blocks := edgeBlocks% "full/vectors/10001101101-V-0000.bin"
noncomputable def vp10001101101 : Blocks := vp10001101101_0
theorem coverp10001101101 : Covers (-4531761639/4000000 : ℚ) vp10001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp10001101100_0 : Blocks := edgeBlocks% "full/vectors/10001101100-V-0000.bin"
noncomputable def vp10001101100 : Blocks := vp10001101100_0
theorem coverp10001101100 : Covers (-4527761639/4000000 : ℚ) vp10001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000110110_0 : Blocks := edgeBlocks% "full/vectors/1000110110-V-0000.bin"
private noncomputable def vp1000110110_1 : Blocks := edgeBlocks% "full/vectors/1000110110-V-0001.bin"
noncomputable def vp1000110110 : Blocks := (Blocks.join vp1000110110_0 vp1000110110_1)
private theorem bp10001101100 : Branch 0 (-4527761639/8000000 : ℚ) vp1000110110 := by
  apply branch_left_normalized (c:=vp10001101100) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4527761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4527761639/4000000 : ℚ) by norm_num]
  exact coverp10001101100
private noncomputable def ep10001101101_0 : Blocks := edgeBlocks% "full/vectors/10001101101-E-0000.bin"
private noncomputable def ep10001101101_1 : Blocks := edgeBlocks% "full/vectors/10001101101-E-0001.bin"
noncomputable def ep10001101101 : Blocks := (Blocks.join ep10001101101_0 ep10001101101_1)
private theorem idp10001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000110110.list =
    C ((2:ℤ)^164) * horner X vp10001101101.list + horner X ep10001101101.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001101101 : Branch 1 (-4527761639/8000000 : ℚ) vp1000110110 := by
  apply branch_checked idp10001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-4527761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4531761639/4000000 : ℚ) by norm_num]
  exact coverp10001101101
theorem coverp1000110110 : Covers (-4527761639/8000000 : ℚ) vp1000110110 := join_branches bp10001101100 bp10001101101
private noncomputable def vp100011011_0 : Blocks := edgeBlocks% "full/vectors/100011011-V-0000.bin"
private noncomputable def vp100011011_1 : Blocks := edgeBlocks% "full/vectors/100011011-V-0001.bin"
private noncomputable def vp100011011_2 : Blocks := edgeBlocks% "full/vectors/100011011-V-0002.bin"
noncomputable def vp100011011 : Blocks := (Blocks.join vp100011011_0 (Blocks.join vp100011011_1 vp100011011_2))
private theorem bp1000110110 : Branch 0 (-4527761639/16000000 : ℚ) vp100011011 := by
  apply branch_left_normalized (c:=vp1000110110) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-4527761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4527761639/8000000 : ℚ) by norm_num]
  exact coverp1000110110
private noncomputable def ep1000110111_0 : Blocks := edgeBlocks% "full/vectors/1000110111-E-0000.bin"
private noncomputable def ep1000110111_1 : Blocks := edgeBlocks% "full/vectors/1000110111-E-0001.bin"
private noncomputable def ep1000110111_2 : Blocks := edgeBlocks% "full/vectors/1000110111-E-0002.bin"
noncomputable def ep1000110111 : Blocks := (Blocks.join ep1000110111_0 (Blocks.join ep1000110111_1 ep1000110111_2))
private theorem idp1000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100011011.list =
    C ((2:ℤ)^306) * horner X vp1000110111.list + horner X ep1000110111.list := by
  exact edge_identity (B := (2:ℤ)^482) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000110111 : Branch 1 (-4527761639/16000000 : ℚ) vp100011011 := by
  apply branch_checked idp1000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-4527761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4535761639/8000000 : ℚ) by norm_num]
  exact coverp1000110111
theorem coverp100011011 : Covers (-4527761639/16000000 : ℚ) vp100011011 := join_branches bp1000110110 bp1000110111
private noncomputable def vp10001101011_0 : Blocks := edgeBlocks% "full/vectors/10001101011-V-0000.bin"
noncomputable def vp10001101011 : Blocks := vp10001101011_0
theorem coverp10001101011 : Covers (-4523761639/4000000 : ℚ) vp10001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp10001101010_0 : Blocks := edgeBlocks% "full/vectors/10001101010-V-0000.bin"
noncomputable def vp10001101010 : Blocks := vp10001101010_0
theorem coverp10001101010 : Covers (-4519761639/4000000 : ℚ) vp10001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp1000110101_0 : Blocks := edgeBlocks% "full/vectors/1000110101-V-0000.bin"
private noncomputable def vp1000110101_1 : Blocks := edgeBlocks% "full/vectors/1000110101-V-0001.bin"
noncomputable def vp1000110101 : Blocks := (Blocks.join vp1000110101_0 vp1000110101_1)
private theorem bp10001101010 : Branch 0 (-4519761639/8000000 : ℚ) vp1000110101 := by
  apply branch_left_normalized (c:=vp10001101010) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4519761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4519761639/4000000 : ℚ) by norm_num]
  exact coverp10001101010
private noncomputable def ep10001101011_0 : Blocks := edgeBlocks% "full/vectors/10001101011-E-0000.bin"
private noncomputable def ep10001101011_1 : Blocks := edgeBlocks% "full/vectors/10001101011-E-0001.bin"
noncomputable def ep10001101011 : Blocks := (Blocks.join ep10001101011_0 ep10001101011_1)
private theorem idp10001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000110101.list =
    C ((2:ℤ)^162) * horner X vp10001101011.list + horner X ep10001101011.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001101011 : Branch 1 (-4519761639/8000000 : ℚ) vp1000110101 := by
  apply branch_checked idp10001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-4519761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4523761639/4000000 : ℚ) by norm_num]
  exact coverp10001101011
theorem coverp1000110101 : Covers (-4519761639/8000000 : ℚ) vp1000110101 := join_branches bp10001101010 bp10001101011
private noncomputable def vp10001101001_0 : Blocks := edgeBlocks% "full/vectors/10001101001-V-0000.bin"
noncomputable def vp10001101001 : Blocks := vp10001101001_0
theorem coverp10001101001 : Covers (-4515761639/4000000 : ℚ) vp10001101001 := cover_leaf (by decide +kernel)
private noncomputable def vp10001101000_0 : Blocks := edgeBlocks% "full/vectors/10001101000-V-0000.bin"
noncomputable def vp10001101000 : Blocks := vp10001101000_0
theorem coverp10001101000 : Covers (-4511761639/4000000 : ℚ) vp10001101000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000110100_0 : Blocks := edgeBlocks% "full/vectors/1000110100-V-0000.bin"
private noncomputable def vp1000110100_1 : Blocks := edgeBlocks% "full/vectors/1000110100-V-0001.bin"
noncomputable def vp1000110100 : Blocks := (Blocks.join vp1000110100_0 vp1000110100_1)
private theorem bp10001101000 : Branch 0 (-4511761639/8000000 : ℚ) vp1000110100 := by
  apply branch_left_normalized (c:=vp10001101000) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4511761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4511761639/4000000 : ℚ) by norm_num]
  exact coverp10001101000
private noncomputable def ep10001101001_0 : Blocks := edgeBlocks% "full/vectors/10001101001-E-0000.bin"
private noncomputable def ep10001101001_1 : Blocks := edgeBlocks% "full/vectors/10001101001-E-0001.bin"
noncomputable def ep10001101001 : Blocks := (Blocks.join ep10001101001_0 ep10001101001_1)
private theorem idp10001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000110100.list =
    C ((2:ℤ)^162) * horner X vp10001101001.list + horner X ep10001101001.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001101001 : Branch 1 (-4511761639/8000000 : ℚ) vp1000110100 := by
  apply branch_checked idp10001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-4511761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4515761639/4000000 : ℚ) by norm_num]
  exact coverp10001101001
theorem coverp1000110100 : Covers (-4511761639/8000000 : ℚ) vp1000110100 := join_branches bp10001101000 bp10001101001
private noncomputable def vp100011010_0 : Blocks := edgeBlocks% "full/vectors/100011010-V-0000.bin"
private noncomputable def vp100011010_1 : Blocks := edgeBlocks% "full/vectors/100011010-V-0001.bin"
private noncomputable def vp100011010_2 : Blocks := edgeBlocks% "full/vectors/100011010-V-0002.bin"
noncomputable def vp100011010 : Blocks := (Blocks.join vp100011010_0 (Blocks.join vp100011010_1 vp100011010_2))
private theorem bp1000110100 : Branch 0 (-4511761639/16000000 : ℚ) vp100011010 := by
  apply branch_left_normalized (c:=vp1000110100) (k:=0) (m:=138) (by decide +kernel)
  rw [show 2*(-4511761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4511761639/8000000 : ℚ) by norm_num]
  exact coverp1000110100
private noncomputable def ep1000110101_0 : Blocks := edgeBlocks% "full/vectors/1000110101-E-0000.bin"
private noncomputable def ep1000110101_1 : Blocks := edgeBlocks% "full/vectors/1000110101-E-0001.bin"
private noncomputable def ep1000110101_2 : Blocks := edgeBlocks% "full/vectors/1000110101-E-0002.bin"
noncomputable def ep1000110101 : Blocks := (Blocks.join ep1000110101_0 (Blocks.join ep1000110101_1 ep1000110101_2))
private theorem idp1000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100011010.list =
    C ((2:ℤ)^303) * horner X vp1000110101.list + horner X ep1000110101.list := by
  exact edge_identity (B := (2:ℤ)^482) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000110101 : Branch 1 (-4511761639/16000000 : ℚ) vp100011010 := by
  apply branch_checked idp1000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-4511761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4519761639/8000000 : ℚ) by norm_num]
  exact coverp1000110101
theorem coverp100011010 : Covers (-4511761639/16000000 : ℚ) vp100011010 := join_branches bp1000110100 bp1000110101
private noncomputable def vp10001101_0 : Blocks := edgeBlocks% "full/vectors/10001101-V-0000.bin"
private noncomputable def vp10001101_1 : Blocks := edgeBlocks% "full/vectors/10001101-V-0001.bin"
private noncomputable def vp10001101_2 : Blocks := edgeBlocks% "full/vectors/10001101-V-0002.bin"
private noncomputable def vp10001101_3 : Blocks := edgeBlocks% "full/vectors/10001101-V-0003.bin"
noncomputable def vp10001101 : Blocks := (Blocks.join (Blocks.join vp10001101_0 vp10001101_1) (Blocks.join vp10001101_2 vp10001101_3))
private theorem bp100011010 : Branch 0 (-4511761639/32000000 : ℚ) vp10001101 := by
  apply branch_left_normalized (c:=vp100011010) (k:=0) (m:=256) (by decide +kernel)
  rw [show 2*(-4511761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4511761639/16000000 : ℚ) by norm_num]
  exact coverp100011010
private noncomputable def ep100011011_0 : Blocks := edgeBlocks% "full/vectors/100011011-E-0000.bin"
private noncomputable def ep100011011_1 : Blocks := edgeBlocks% "full/vectors/100011011-E-0001.bin"
private noncomputable def ep100011011_2 : Blocks := edgeBlocks% "full/vectors/100011011-E-0002.bin"
private noncomputable def ep100011011_3 : Blocks := edgeBlocks% "full/vectors/100011011-E-0003.bin"
noncomputable def ep100011011 : Blocks := (Blocks.join (Blocks.join ep100011011_0 ep100011011_1) (Blocks.join ep100011011_2 ep100011011_3))
private theorem idp100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10001101.list =
    C ((2:ℤ)^581) * horner X vp100011011.list + horner X ep100011011.list := by
  exact edge_identity (B := (2:ℤ)^838) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100011011 : Branch 1 (-4511761639/32000000 : ℚ) vp10001101 := by
  apply branch_checked idp100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-4511761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4527761639/16000000 : ℚ) by norm_num]
  exact coverp100011011
theorem coverp10001101 : Covers (-4511761639/32000000 : ℚ) vp10001101 := join_branches bp100011010 bp100011011
private noncomputable def vp10001100111_0 : Blocks := edgeBlocks% "full/vectors/10001100111-V-0000.bin"
noncomputable def vp10001100111 : Blocks := vp10001100111_0
theorem coverp10001100111 : Covers (-4507761639/4000000 : ℚ) vp10001100111 := cover_leaf (by decide +kernel)
private noncomputable def vp10001100110_0 : Blocks := edgeBlocks% "full/vectors/10001100110-V-0000.bin"
noncomputable def vp10001100110 : Blocks := vp10001100110_0
theorem coverp10001100110 : Covers (-4503761639/4000000 : ℚ) vp10001100110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000110011_0 : Blocks := edgeBlocks% "full/vectors/1000110011-V-0000.bin"
private noncomputable def vp1000110011_1 : Blocks := edgeBlocks% "full/vectors/1000110011-V-0001.bin"
noncomputable def vp1000110011 : Blocks := (Blocks.join vp1000110011_0 vp1000110011_1)
private theorem bp10001100110 : Branch 0 (-4503761639/8000000 : ℚ) vp1000110011 := by
  apply branch_left_normalized (c:=vp10001100110) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4503761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4503761639/4000000 : ℚ) by norm_num]
  exact coverp10001100110
private noncomputable def ep10001100111_0 : Blocks := edgeBlocks% "full/vectors/10001100111-E-0000.bin"
private noncomputable def ep10001100111_1 : Blocks := edgeBlocks% "full/vectors/10001100111-E-0001.bin"
noncomputable def ep10001100111 : Blocks := (Blocks.join ep10001100111_0 ep10001100111_1)
private theorem idp10001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000110011.list =
    C ((2:ℤ)^162) * horner X vp10001100111.list + horner X ep10001100111.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001100111 : Branch 1 (-4503761639/8000000 : ℚ) vp1000110011 := by
  apply branch_checked idp10001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-4503761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4507761639/4000000 : ℚ) by norm_num]
  exact coverp10001100111
theorem coverp1000110011 : Covers (-4503761639/8000000 : ℚ) vp1000110011 := join_branches bp10001100110 bp10001100111
private noncomputable def vp10001100101_0 : Blocks := edgeBlocks% "full/vectors/10001100101-V-0000.bin"
noncomputable def vp10001100101 : Blocks := vp10001100101_0
theorem coverp10001100101 : Covers (-4499761639/4000000 : ℚ) vp10001100101 := cover_leaf (by decide +kernel)
private noncomputable def vp10001100100_0 : Blocks := edgeBlocks% "full/vectors/10001100100-V-0000.bin"
noncomputable def vp10001100100 : Blocks := vp10001100100_0
theorem coverp10001100100 : Covers (-4495761639/4000000 : ℚ) vp10001100100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000110010_0 : Blocks := edgeBlocks% "full/vectors/1000110010-V-0000.bin"
private noncomputable def vp1000110010_1 : Blocks := edgeBlocks% "full/vectors/1000110010-V-0001.bin"
noncomputable def vp1000110010 : Blocks := (Blocks.join vp1000110010_0 vp1000110010_1)
private theorem bp10001100100 : Branch 0 (-4495761639/8000000 : ℚ) vp1000110010 := by
  apply branch_left_normalized (c:=vp10001100100) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4495761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4495761639/4000000 : ℚ) by norm_num]
  exact coverp10001100100
private noncomputable def ep10001100101_0 : Blocks := edgeBlocks% "full/vectors/10001100101-E-0000.bin"
private noncomputable def ep10001100101_1 : Blocks := edgeBlocks% "full/vectors/10001100101-E-0001.bin"
noncomputable def ep10001100101 : Blocks := (Blocks.join ep10001100101_0 ep10001100101_1)
private theorem idp10001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000110010.list =
    C ((2:ℤ)^164) * horner X vp10001100101.list + horner X ep10001100101.list := by
  exact edge_identity (B := (2:ℤ)^304) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001100101 : Branch 1 (-4495761639/8000000 : ℚ) vp1000110010 := by
  apply branch_checked idp10001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-4495761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4499761639/4000000 : ℚ) by norm_num]
  exact coverp10001100101
theorem coverp1000110010 : Covers (-4495761639/8000000 : ℚ) vp1000110010 := join_branches bp10001100100 bp10001100101
private noncomputable def vp100011001_0 : Blocks := edgeBlocks% "full/vectors/100011001-V-0000.bin"
private noncomputable def vp100011001_1 : Blocks := edgeBlocks% "full/vectors/100011001-V-0001.bin"
noncomputable def vp100011001 : Blocks := (Blocks.join vp100011001_0 vp100011001_1)
private theorem bp1000110010 : Branch 0 (-4495761639/16000000 : ℚ) vp100011001 := by
  apply branch_left_normalized (c:=vp1000110010) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-4495761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4495761639/8000000 : ℚ) by norm_num]
  exact coverp1000110010
private noncomputable def ep1000110011_0 : Blocks := edgeBlocks% "full/vectors/1000110011-E-0000.bin"
private noncomputable def ep1000110011_1 : Blocks := edgeBlocks% "full/vectors/1000110011-E-0001.bin"
noncomputable def ep1000110011 : Blocks := (Blocks.join ep1000110011_0 ep1000110011_1)
private theorem idp1000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100011001.list =
    C ((2:ℤ)^303) * horner X vp1000110011.list + horner X ep1000110011.list := by
  exact edge_identity (B := (2:ℤ)^482) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000110011 : Branch 1 (-4495761639/16000000 : ℚ) vp100011001 := by
  apply branch_checked idp1000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-4495761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4503761639/8000000 : ℚ) by norm_num]
  exact coverp1000110011
theorem coverp100011001 : Covers (-4495761639/16000000 : ℚ) vp100011001 := join_branches bp1000110010 bp1000110011
private noncomputable def vp10001100011_0 : Blocks := edgeBlocks% "full/vectors/10001100011-V-0000.bin"
noncomputable def vp10001100011 : Blocks := vp10001100011_0
theorem coverp10001100011 : Covers (-4491761639/4000000 : ℚ) vp10001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp10001100010_0 : Blocks := edgeBlocks% "full/vectors/10001100010-V-0000.bin"
noncomputable def vp10001100010 : Blocks := vp10001100010_0
theorem coverp10001100010 : Covers (-4487761639/4000000 : ℚ) vp10001100010 := cover_leaf (by decide +kernel)
private noncomputable def vp1000110001_0 : Blocks := edgeBlocks% "full/vectors/1000110001-V-0000.bin"
private noncomputable def vp1000110001_1 : Blocks := edgeBlocks% "full/vectors/1000110001-V-0001.bin"
noncomputable def vp1000110001 : Blocks := (Blocks.join vp1000110001_0 vp1000110001_1)
private theorem bp10001100010 : Branch 0 (-4487761639/8000000 : ℚ) vp1000110001 := by
  apply branch_left_normalized (c:=vp10001100010) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4487761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4487761639/4000000 : ℚ) by norm_num]
  exact coverp10001100010
private noncomputable def ep10001100011_0 : Blocks := edgeBlocks% "full/vectors/10001100011-E-0000.bin"
private noncomputable def ep10001100011_1 : Blocks := edgeBlocks% "full/vectors/10001100011-E-0001.bin"
noncomputable def ep10001100011 : Blocks := (Blocks.join ep10001100011_0 ep10001100011_1)
private theorem idp10001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000110001.list =
    C ((2:ℤ)^163) * horner X vp10001100011.list + horner X ep10001100011.list := by
  exact edge_identity (B := (2:ℤ)^304) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001100011 : Branch 1 (-4487761639/8000000 : ℚ) vp1000110001 := by
  apply branch_checked idp10001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-4487761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4491761639/4000000 : ℚ) by norm_num]
  exact coverp10001100011
theorem coverp1000110001 : Covers (-4487761639/8000000 : ℚ) vp1000110001 := join_branches bp10001100010 bp10001100011
private noncomputable def vp10001100001_0 : Blocks := edgeBlocks% "full/vectors/10001100001-V-0000.bin"
noncomputable def vp10001100001 : Blocks := vp10001100001_0
theorem coverp10001100001 : Covers (-4483761639/4000000 : ℚ) vp10001100001 := cover_leaf (by decide +kernel)
private noncomputable def vp10001100000_0 : Blocks := edgeBlocks% "full/vectors/10001100000-V-0000.bin"
noncomputable def vp10001100000 : Blocks := vp10001100000_0
theorem coverp10001100000 : Covers (-4479761639/4000000 : ℚ) vp10001100000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000110000_0 : Blocks := edgeBlocks% "full/vectors/1000110000-V-0000.bin"
private noncomputable def vp1000110000_1 : Blocks := edgeBlocks% "full/vectors/1000110000-V-0001.bin"
noncomputable def vp1000110000 : Blocks := (Blocks.join vp1000110000_0 vp1000110000_1)
private theorem bp10001100000 : Branch 0 (-4479761639/8000000 : ℚ) vp1000110000 := by
  apply branch_left_normalized (c:=vp10001100000) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4479761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4479761639/4000000 : ℚ) by norm_num]
  exact coverp10001100000
private noncomputable def ep10001100001_0 : Blocks := edgeBlocks% "full/vectors/10001100001-E-0000.bin"
private noncomputable def ep10001100001_1 : Blocks := edgeBlocks% "full/vectors/10001100001-E-0001.bin"
noncomputable def ep10001100001 : Blocks := (Blocks.join ep10001100001_0 ep10001100001_1)
private theorem idp10001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000110000.list =
    C ((2:ℤ)^163) * horner X vp10001100001.list + horner X ep10001100001.list := by
  exact edge_identity (B := (2:ℤ)^304) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001100001 : Branch 1 (-4479761639/8000000 : ℚ) vp1000110000 := by
  apply branch_checked idp10001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-4479761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4483761639/4000000 : ℚ) by norm_num]
  exact coverp10001100001
theorem coverp1000110000 : Covers (-4479761639/8000000 : ℚ) vp1000110000 := join_branches bp10001100000 bp10001100001
private noncomputable def vp100011000_0 : Blocks := edgeBlocks% "full/vectors/100011000-V-0000.bin"
private noncomputable def vp100011000_1 : Blocks := edgeBlocks% "full/vectors/100011000-V-0001.bin"
private noncomputable def vp100011000_2 : Blocks := edgeBlocks% "full/vectors/100011000-V-0002.bin"
noncomputable def vp100011000 : Blocks := (Blocks.join vp100011000_0 (Blocks.join vp100011000_1 vp100011000_2))
private theorem bp1000110000 : Branch 0 (-4479761639/16000000 : ℚ) vp100011000 := by
  apply branch_left_normalized (c:=vp1000110000) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-4479761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4479761639/8000000 : ℚ) by norm_num]
  exact coverp1000110000
private noncomputable def ep1000110001_0 : Blocks := edgeBlocks% "full/vectors/1000110001-E-0000.bin"
private noncomputable def ep1000110001_1 : Blocks := edgeBlocks% "full/vectors/1000110001-E-0001.bin"
private noncomputable def ep1000110001_2 : Blocks := edgeBlocks% "full/vectors/1000110001-E-0002.bin"
noncomputable def ep1000110001 : Blocks := (Blocks.join ep1000110001_0 (Blocks.join ep1000110001_1 ep1000110001_2))
private theorem idp1000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100011000.list =
    C ((2:ℤ)^303) * horner X vp1000110001.list + horner X ep1000110001.list := by
  exact edge_identity (B := (2:ℤ)^483) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000110001 : Branch 1 (-4479761639/16000000 : ℚ) vp100011000 := by
  apply branch_checked idp1000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-4479761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4487761639/8000000 : ℚ) by norm_num]
  exact coverp1000110001
theorem coverp100011000 : Covers (-4479761639/16000000 : ℚ) vp100011000 := join_branches bp1000110000 bp1000110001
private noncomputable def vp10001100_0 : Blocks := edgeBlocks% "full/vectors/10001100-V-0000.bin"
private noncomputable def vp10001100_1 : Blocks := edgeBlocks% "full/vectors/10001100-V-0001.bin"
private noncomputable def vp10001100_2 : Blocks := edgeBlocks% "full/vectors/10001100-V-0002.bin"
private noncomputable def vp10001100_3 : Blocks := edgeBlocks% "full/vectors/10001100-V-0003.bin"
noncomputable def vp10001100 : Blocks := (Blocks.join (Blocks.join vp10001100_0 vp10001100_1) (Blocks.join vp10001100_2 vp10001100_3))
private theorem bp100011000 : Branch 0 (-4479761639/32000000 : ℚ) vp10001100 := by
  apply branch_left_normalized (c:=vp100011000) (k:=0) (m:=256) (by decide +kernel)
  rw [show 2*(-4479761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4479761639/16000000 : ℚ) by norm_num]
  exact coverp100011000
private noncomputable def ep100011001_0 : Blocks := edgeBlocks% "full/vectors/100011001-E-0000.bin"
private noncomputable def ep100011001_1 : Blocks := edgeBlocks% "full/vectors/100011001-E-0001.bin"
private noncomputable def ep100011001_2 : Blocks := edgeBlocks% "full/vectors/100011001-E-0002.bin"
private noncomputable def ep100011001_3 : Blocks := edgeBlocks% "full/vectors/100011001-E-0003.bin"
noncomputable def ep100011001 : Blocks := (Blocks.join (Blocks.join ep100011001_0 ep100011001_1) (Blocks.join ep100011001_2 ep100011001_3))
private theorem idp100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10001100.list =
    C ((2:ℤ)^583) * horner X vp100011001.list + horner X ep100011001.list := by
  exact edge_identity (B := (2:ℤ)^841) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100011001 : Branch 1 (-4479761639/32000000 : ℚ) vp10001100 := by
  apply branch_checked idp100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-4479761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4495761639/16000000 : ℚ) by norm_num]
  exact coverp100011001
theorem coverp10001100 : Covers (-4479761639/32000000 : ℚ) vp10001100 := join_branches bp100011000 bp100011001
private noncomputable def vp1000110_0 : Blocks := edgeBlocks% "full/vectors/1000110-V-0000.bin"
private noncomputable def vp1000110_1 : Blocks := edgeBlocks% "full/vectors/1000110-V-0001.bin"
private noncomputable def vp1000110_2 : Blocks := edgeBlocks% "full/vectors/1000110-V-0002.bin"
private noncomputable def vp1000110_3 : Blocks := edgeBlocks% "full/vectors/1000110-V-0003.bin"
private noncomputable def vp1000110_4 : Blocks := edgeBlocks% "full/vectors/1000110-V-0004.bin"
private noncomputable def vp1000110_5 : Blocks := edgeBlocks% "full/vectors/1000110-V-0005.bin"
private noncomputable def vp1000110_6 : Blocks := edgeBlocks% "full/vectors/1000110-V-0006.bin"
private noncomputable def vp1000110_7 : Blocks := edgeBlocks% "full/vectors/1000110-V-0007.bin"
noncomputable def vp1000110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1000110_0 vp1000110_1) (Blocks.join vp1000110_2 vp1000110_3)) (Blocks.join (Blocks.join vp1000110_4 vp1000110_5) (Blocks.join vp1000110_6 vp1000110_7)))
private theorem bp10001100 : Branch 0 (-4479761639/64000000 : ℚ) vp1000110 := by
  apply branch_left_normalized (c:=vp10001100) (k:=0) (m:=490) (by decide +kernel)
  rw [show 2*(-4479761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4479761639/32000000 : ℚ) by norm_num]
  exact coverp10001100
private noncomputable def ep10001101_0 : Blocks := edgeBlocks% "full/vectors/10001101-E-0000.bin"
private noncomputable def ep10001101_1 : Blocks := edgeBlocks% "full/vectors/10001101-E-0001.bin"
private noncomputable def ep10001101_2 : Blocks := edgeBlocks% "full/vectors/10001101-E-0002.bin"
private noncomputable def ep10001101_3 : Blocks := edgeBlocks% "full/vectors/10001101-E-0003.bin"
private noncomputable def ep10001101_4 : Blocks := edgeBlocks% "full/vectors/10001101-E-0004.bin"
private noncomputable def ep10001101_5 : Blocks := edgeBlocks% "full/vectors/10001101-E-0005.bin"
private noncomputable def ep10001101_6 : Blocks := edgeBlocks% "full/vectors/10001101-E-0006.bin"
private noncomputable def ep10001101_7 : Blocks := edgeBlocks% "full/vectors/10001101-E-0007.bin"
noncomputable def ep10001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10001101_0 ep10001101_1) (Blocks.join ep10001101_2 ep10001101_3)) (Blocks.join (Blocks.join ep10001101_4 ep10001101_5) (Blocks.join ep10001101_6 ep10001101_7)))
private theorem idp10001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000110.list =
    C ((2:ℤ)^1136) * horner X vp10001101.list + horner X ep10001101.list := by
  exact edge_identity (B := (2:ℤ)^1549) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001101 : Branch 1 (-4479761639/64000000 : ℚ) vp1000110 := by
  apply branch_checked idp10001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4479761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4511761639/32000000 : ℚ) by norm_num]
  exact coverp10001101
theorem coverp1000110 : Covers (-4479761639/64000000 : ℚ) vp1000110 := join_branches bp10001100 bp10001101
private noncomputable def vp100011_0 : Blocks := edgeBlocks% "full/vectors/100011-V-0000.bin"
private noncomputable def vp100011_1 : Blocks := edgeBlocks% "full/vectors/100011-V-0001.bin"
private noncomputable def vp100011_2 : Blocks := edgeBlocks% "full/vectors/100011-V-0002.bin"
private noncomputable def vp100011_3 : Blocks := edgeBlocks% "full/vectors/100011-V-0003.bin"
private noncomputable def vp100011_4 : Blocks := edgeBlocks% "full/vectors/100011-V-0004.bin"
private noncomputable def vp100011_5 : Blocks := edgeBlocks% "full/vectors/100011-V-0005.bin"
private noncomputable def vp100011_6 : Blocks := edgeBlocks% "full/vectors/100011-V-0006.bin"
private noncomputable def vp100011_7 : Blocks := edgeBlocks% "full/vectors/100011-V-0007.bin"
private noncomputable def vp100011_8 : Blocks := edgeBlocks% "full/vectors/100011-V-0008.bin"
private noncomputable def vp100011_9 : Blocks := edgeBlocks% "full/vectors/100011-V-0009.bin"
private noncomputable def vp100011_10 : Blocks := edgeBlocks% "full/vectors/100011-V-0010.bin"
private noncomputable def vp100011_11 : Blocks := edgeBlocks% "full/vectors/100011-V-0011.bin"
private noncomputable def vp100011_12 : Blocks := edgeBlocks% "full/vectors/100011-V-0012.bin"
private noncomputable def vp100011_13 : Blocks := edgeBlocks% "full/vectors/100011-V-0013.bin"
private noncomputable def vp100011_14 : Blocks := edgeBlocks% "full/vectors/100011-V-0014.bin"
noncomputable def vp100011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp100011_0 (Blocks.join vp100011_1 vp100011_2)) (Blocks.join (Blocks.join vp100011_3 vp100011_4) (Blocks.join vp100011_5 vp100011_6))) (Blocks.join (Blocks.join (Blocks.join vp100011_7 vp100011_8) (Blocks.join vp100011_9 vp100011_10)) (Blocks.join (Blocks.join vp100011_11 vp100011_12) (Blocks.join vp100011_13 vp100011_14))))
private theorem bp1000110 : Branch 0 (-4479761639/128000000 : ℚ) vp100011 := by
  apply branch_left_normalized (c:=vp1000110) (k:=0) (m:=950) (by decide +kernel)
  rw [show 2*(-4479761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-4479761639/64000000 : ℚ) by norm_num]
  exact coverp1000110
private noncomputable def ep1000111_0 : Blocks := edgeBlocks% "full/vectors/1000111-E-0000.bin"
private noncomputable def ep1000111_1 : Blocks := edgeBlocks% "full/vectors/1000111-E-0001.bin"
private noncomputable def ep1000111_2 : Blocks := edgeBlocks% "full/vectors/1000111-E-0002.bin"
private noncomputable def ep1000111_3 : Blocks := edgeBlocks% "full/vectors/1000111-E-0003.bin"
private noncomputable def ep1000111_4 : Blocks := edgeBlocks% "full/vectors/1000111-E-0004.bin"
private noncomputable def ep1000111_5 : Blocks := edgeBlocks% "full/vectors/1000111-E-0005.bin"
private noncomputable def ep1000111_6 : Blocks := edgeBlocks% "full/vectors/1000111-E-0006.bin"
private noncomputable def ep1000111_7 : Blocks := edgeBlocks% "full/vectors/1000111-E-0007.bin"
private noncomputable def ep1000111_8 : Blocks := edgeBlocks% "full/vectors/1000111-E-0008.bin"
private noncomputable def ep1000111_9 : Blocks := edgeBlocks% "full/vectors/1000111-E-0009.bin"
private noncomputable def ep1000111_10 : Blocks := edgeBlocks% "full/vectors/1000111-E-0010.bin"
private noncomputable def ep1000111_11 : Blocks := edgeBlocks% "full/vectors/1000111-E-0011.bin"
private noncomputable def ep1000111_12 : Blocks := edgeBlocks% "full/vectors/1000111-E-0012.bin"
private noncomputable def ep1000111_13 : Blocks := edgeBlocks% "full/vectors/1000111-E-0013.bin"
private noncomputable def ep1000111_14 : Blocks := edgeBlocks% "full/vectors/1000111-E-0014.bin"
noncomputable def ep1000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1000111_0 (Blocks.join ep1000111_1 ep1000111_2)) (Blocks.join (Blocks.join ep1000111_3 ep1000111_4) (Blocks.join ep1000111_5 ep1000111_6))) (Blocks.join (Blocks.join (Blocks.join ep1000111_7 ep1000111_8) (Blocks.join ep1000111_9 ep1000111_10)) (Blocks.join (Blocks.join ep1000111_11 ep1000111_12) (Blocks.join ep1000111_13 ep1000111_14))))
private theorem idp1000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100011.list =
    C ((2:ℤ)^2226) * horner X vp1000111.list + horner X ep1000111.list := by
  exact edge_identity (B := (2:ℤ)^2941) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000111 : Branch 1 (-4479761639/128000000 : ℚ) vp100011 := by
  apply branch_checked idp1000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4479761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-4543761639/64000000 : ℚ) by norm_num]
  exact coverp1000111
theorem coverp100011 : Covers (-4479761639/128000000 : ℚ) vp100011 := join_branches bp1000110 bp1000111
private noncomputable def vp10001011111_0 : Blocks := edgeBlocks% "full/vectors/10001011111-V-0000.bin"
noncomputable def vp10001011111 : Blocks := vp10001011111_0
theorem coverp10001011111 : Covers (-4475761639/4000000 : ℚ) vp10001011111 := cover_leaf (by decide +kernel)
private noncomputable def vp10001011110_0 : Blocks := edgeBlocks% "full/vectors/10001011110-V-0000.bin"
noncomputable def vp10001011110 : Blocks := vp10001011110_0
theorem coverp10001011110 : Covers (-4471761639/4000000 : ℚ) vp10001011110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000101111_0 : Blocks := edgeBlocks% "full/vectors/1000101111-V-0000.bin"
private noncomputable def vp1000101111_1 : Blocks := edgeBlocks% "full/vectors/1000101111-V-0001.bin"
noncomputable def vp1000101111 : Blocks := (Blocks.join vp1000101111_0 vp1000101111_1)
private theorem bp10001011110 : Branch 0 (-4471761639/8000000 : ℚ) vp1000101111 := by
  apply branch_left_normalized (c:=vp10001011110) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4471761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4471761639/4000000 : ℚ) by norm_num]
  exact coverp10001011110
private noncomputable def ep10001011111_0 : Blocks := edgeBlocks% "full/vectors/10001011111-E-0000.bin"
private noncomputable def ep10001011111_1 : Blocks := edgeBlocks% "full/vectors/10001011111-E-0001.bin"
noncomputable def ep10001011111 : Blocks := (Blocks.join ep10001011111_0 ep10001011111_1)
private theorem idp10001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000101111.list =
    C ((2:ℤ)^163) * horner X vp10001011111.list + horner X ep10001011111.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001011111 : Branch 1 (-4471761639/8000000 : ℚ) vp1000101111 := by
  apply branch_checked idp10001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-4471761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4475761639/4000000 : ℚ) by norm_num]
  exact coverp10001011111
theorem coverp1000101111 : Covers (-4471761639/8000000 : ℚ) vp1000101111 := join_branches bp10001011110 bp10001011111
private noncomputable def vp10001011101_0 : Blocks := edgeBlocks% "full/vectors/10001011101-V-0000.bin"
noncomputable def vp10001011101 : Blocks := vp10001011101_0
theorem coverp10001011101 : Covers (-4467761639/4000000 : ℚ) vp10001011101 := cover_leaf (by decide +kernel)
private noncomputable def vp10001011100_0 : Blocks := edgeBlocks% "full/vectors/10001011100-V-0000.bin"
noncomputable def vp10001011100 : Blocks := vp10001011100_0
theorem coverp10001011100 : Covers (-4463761639/4000000 : ℚ) vp10001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000101110_0 : Blocks := edgeBlocks% "full/vectors/1000101110-V-0000.bin"
private noncomputable def vp1000101110_1 : Blocks := edgeBlocks% "full/vectors/1000101110-V-0001.bin"
noncomputable def vp1000101110 : Blocks := (Blocks.join vp1000101110_0 vp1000101110_1)
private theorem bp10001011100 : Branch 0 (-4463761639/8000000 : ℚ) vp1000101110 := by
  apply branch_left_normalized (c:=vp10001011100) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4463761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4463761639/4000000 : ℚ) by norm_num]
  exact coverp10001011100
private noncomputable def ep10001011101_0 : Blocks := edgeBlocks% "full/vectors/10001011101-E-0000.bin"
private noncomputable def ep10001011101_1 : Blocks := edgeBlocks% "full/vectors/10001011101-E-0001.bin"
noncomputable def ep10001011101 : Blocks := (Blocks.join ep10001011101_0 ep10001011101_1)
private theorem idp10001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000101110.list =
    C ((2:ℤ)^163) * horner X vp10001011101.list + horner X ep10001011101.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001011101 : Branch 1 (-4463761639/8000000 : ℚ) vp1000101110 := by
  apply branch_checked idp10001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-4463761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4467761639/4000000 : ℚ) by norm_num]
  exact coverp10001011101
theorem coverp1000101110 : Covers (-4463761639/8000000 : ℚ) vp1000101110 := join_branches bp10001011100 bp10001011101
private noncomputable def vp100010111_0 : Blocks := edgeBlocks% "full/vectors/100010111-V-0000.bin"
private noncomputable def vp100010111_1 : Blocks := edgeBlocks% "full/vectors/100010111-V-0001.bin"
private noncomputable def vp100010111_2 : Blocks := edgeBlocks% "full/vectors/100010111-V-0002.bin"
noncomputable def vp100010111 : Blocks := (Blocks.join vp100010111_0 (Blocks.join vp100010111_1 vp100010111_2))
private theorem bp1000101110 : Branch 0 (-4463761639/16000000 : ℚ) vp100010111 := by
  apply branch_left_normalized (c:=vp1000101110) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-4463761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4463761639/8000000 : ℚ) by norm_num]
  exact coverp1000101110
private noncomputable def ep1000101111_0 : Blocks := edgeBlocks% "full/vectors/1000101111-E-0000.bin"
private noncomputable def ep1000101111_1 : Blocks := edgeBlocks% "full/vectors/1000101111-E-0001.bin"
private noncomputable def ep1000101111_2 : Blocks := edgeBlocks% "full/vectors/1000101111-E-0002.bin"
noncomputable def ep1000101111 : Blocks := (Blocks.join ep1000101111_0 (Blocks.join ep1000101111_1 ep1000101111_2))
private theorem idp1000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100010111.list =
    C ((2:ℤ)^304) * horner X vp1000101111.list + horner X ep1000101111.list := by
  exact edge_identity (B := (2:ℤ)^484) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000101111 : Branch 1 (-4463761639/16000000 : ℚ) vp100010111 := by
  apply branch_checked idp1000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-4463761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4471761639/8000000 : ℚ) by norm_num]
  exact coverp1000101111
theorem coverp100010111 : Covers (-4463761639/16000000 : ℚ) vp100010111 := join_branches bp1000101110 bp1000101111
private noncomputable def vp10001011011_0 : Blocks := edgeBlocks% "full/vectors/10001011011-V-0000.bin"
noncomputable def vp10001011011 : Blocks := vp10001011011_0
theorem coverp10001011011 : Covers (-4459761639/4000000 : ℚ) vp10001011011 := cover_leaf (by decide +kernel)
private noncomputable def vp10001011010_0 : Blocks := edgeBlocks% "full/vectors/10001011010-V-0000.bin"
noncomputable def vp10001011010 : Blocks := vp10001011010_0
theorem coverp10001011010 : Covers (-4455761639/4000000 : ℚ) vp10001011010 := cover_leaf (by decide +kernel)
private noncomputable def vp1000101101_0 : Blocks := edgeBlocks% "full/vectors/1000101101-V-0000.bin"
private noncomputable def vp1000101101_1 : Blocks := edgeBlocks% "full/vectors/1000101101-V-0001.bin"
noncomputable def vp1000101101 : Blocks := (Blocks.join vp1000101101_0 vp1000101101_1)
private theorem bp10001011010 : Branch 0 (-4455761639/8000000 : ℚ) vp1000101101 := by
  apply branch_left_normalized (c:=vp10001011010) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-4455761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4455761639/4000000 : ℚ) by norm_num]
  exact coverp10001011010
private noncomputable def ep10001011011_0 : Blocks := edgeBlocks% "full/vectors/10001011011-E-0000.bin"
private noncomputable def ep10001011011_1 : Blocks := edgeBlocks% "full/vectors/10001011011-E-0001.bin"
noncomputable def ep10001011011 : Blocks := (Blocks.join ep10001011011_0 ep10001011011_1)
private theorem idp10001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000101101.list =
    C ((2:ℤ)^165) * horner X vp10001011011.list + horner X ep10001011011.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001011011 : Branch 1 (-4455761639/8000000 : ℚ) vp1000101101 := by
  apply branch_checked idp10001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-4455761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4459761639/4000000 : ℚ) by norm_num]
  exact coverp10001011011
theorem coverp1000101101 : Covers (-4455761639/8000000 : ℚ) vp1000101101 := join_branches bp10001011010 bp10001011011
private noncomputable def vp10001011001_0 : Blocks := edgeBlocks% "full/vectors/10001011001-V-0000.bin"
noncomputable def vp10001011001 : Blocks := vp10001011001_0
theorem coverp10001011001 : Covers (-4451761639/4000000 : ℚ) vp10001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp10001011000_0 : Blocks := edgeBlocks% "full/vectors/10001011000-V-0000.bin"
noncomputable def vp10001011000 : Blocks := vp10001011000_0
theorem coverp10001011000 : Covers (-4447761639/4000000 : ℚ) vp10001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000101100_0 : Blocks := edgeBlocks% "full/vectors/1000101100-V-0000.bin"
private noncomputable def vp1000101100_1 : Blocks := edgeBlocks% "full/vectors/1000101100-V-0001.bin"
noncomputable def vp1000101100 : Blocks := (Blocks.join vp1000101100_0 vp1000101100_1)
private theorem bp10001011000 : Branch 0 (-4447761639/8000000 : ℚ) vp1000101100 := by
  apply branch_left_normalized (c:=vp10001011000) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4447761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4447761639/4000000 : ℚ) by norm_num]
  exact coverp10001011000
private noncomputable def ep10001011001_0 : Blocks := edgeBlocks% "full/vectors/10001011001-E-0000.bin"
private noncomputable def ep10001011001_1 : Blocks := edgeBlocks% "full/vectors/10001011001-E-0001.bin"
noncomputable def ep10001011001 : Blocks := (Blocks.join ep10001011001_0 ep10001011001_1)
private theorem idp10001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000101100.list =
    C ((2:ℤ)^164) * horner X vp10001011001.list + horner X ep10001011001.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001011001 : Branch 1 (-4447761639/8000000 : ℚ) vp1000101100 := by
  apply branch_checked idp10001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-4447761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4451761639/4000000 : ℚ) by norm_num]
  exact coverp10001011001
theorem coverp1000101100 : Covers (-4447761639/8000000 : ℚ) vp1000101100 := join_branches bp10001011000 bp10001011001
private noncomputable def vp100010110_0 : Blocks := edgeBlocks% "full/vectors/100010110-V-0000.bin"
private noncomputable def vp100010110_1 : Blocks := edgeBlocks% "full/vectors/100010110-V-0001.bin"
private noncomputable def vp100010110_2 : Blocks := edgeBlocks% "full/vectors/100010110-V-0002.bin"
noncomputable def vp100010110 : Blocks := (Blocks.join vp100010110_0 (Blocks.join vp100010110_1 vp100010110_2))
private theorem bp1000101100 : Branch 0 (-4447761639/16000000 : ℚ) vp100010110 := by
  apply branch_left_normalized (c:=vp1000101100) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-4447761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4447761639/8000000 : ℚ) by norm_num]
  exact coverp1000101100
private noncomputable def ep1000101101_0 : Blocks := edgeBlocks% "full/vectors/1000101101-E-0000.bin"
private noncomputable def ep1000101101_1 : Blocks := edgeBlocks% "full/vectors/1000101101-E-0001.bin"
private noncomputable def ep1000101101_2 : Blocks := edgeBlocks% "full/vectors/1000101101-E-0002.bin"
noncomputable def ep1000101101 : Blocks := (Blocks.join ep1000101101_0 (Blocks.join ep1000101101_1 ep1000101101_2))
private theorem idp1000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100010110.list =
    C ((2:ℤ)^305) * horner X vp1000101101.list + horner X ep1000101101.list := by
  exact edge_identity (B := (2:ℤ)^486) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000101101 : Branch 1 (-4447761639/16000000 : ℚ) vp100010110 := by
  apply branch_checked idp1000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-4447761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4455761639/8000000 : ℚ) by norm_num]
  exact coverp1000101101
theorem coverp100010110 : Covers (-4447761639/16000000 : ℚ) vp100010110 := join_branches bp1000101100 bp1000101101
private noncomputable def vp10001011_0 : Blocks := edgeBlocks% "full/vectors/10001011-V-0000.bin"
private noncomputable def vp10001011_1 : Blocks := edgeBlocks% "full/vectors/10001011-V-0001.bin"
private noncomputable def vp10001011_2 : Blocks := edgeBlocks% "full/vectors/10001011-V-0002.bin"
private noncomputable def vp10001011_3 : Blocks := edgeBlocks% "full/vectors/10001011-V-0003.bin"
noncomputable def vp10001011 : Blocks := (Blocks.join (Blocks.join vp10001011_0 vp10001011_1) (Blocks.join vp10001011_2 vp10001011_3))
private theorem bp100010110 : Branch 0 (-4447761639/32000000 : ℚ) vp10001011 := by
  apply branch_left_normalized (c:=vp100010110) (k:=0) (m:=258) (by decide +kernel)
  rw [show 2*(-4447761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4447761639/16000000 : ℚ) by norm_num]
  exact coverp100010110
private noncomputable def ep100010111_0 : Blocks := edgeBlocks% "full/vectors/100010111-E-0000.bin"
private noncomputable def ep100010111_1 : Blocks := edgeBlocks% "full/vectors/100010111-E-0001.bin"
private noncomputable def ep100010111_2 : Blocks := edgeBlocks% "full/vectors/100010111-E-0002.bin"
private noncomputable def ep100010111_3 : Blocks := edgeBlocks% "full/vectors/100010111-E-0003.bin"
noncomputable def ep100010111 : Blocks := (Blocks.join (Blocks.join ep100010111_0 ep100010111_1) (Blocks.join ep100010111_2 ep100010111_3))
private theorem idp100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10001011.list =
    C ((2:ℤ)^585) * horner X vp100010111.list + horner X ep100010111.list := by
  exact edge_identity (B := (2:ℤ)^843) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100010111 : Branch 1 (-4447761639/32000000 : ℚ) vp10001011 := by
  apply branch_checked idp100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-4447761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4463761639/16000000 : ℚ) by norm_num]
  exact coverp100010111
theorem coverp10001011 : Covers (-4447761639/32000000 : ℚ) vp10001011 := join_branches bp100010110 bp100010111
private noncomputable def vp10001010111_0 : Blocks := edgeBlocks% "full/vectors/10001010111-V-0000.bin"
noncomputable def vp10001010111 : Blocks := vp10001010111_0
theorem coverp10001010111 : Covers (-4443761639/4000000 : ℚ) vp10001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp10001010110_0 : Blocks := edgeBlocks% "full/vectors/10001010110-V-0000.bin"
noncomputable def vp10001010110 : Blocks := vp10001010110_0
theorem coverp10001010110 : Covers (-4439761639/4000000 : ℚ) vp10001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000101011_0 : Blocks := edgeBlocks% "full/vectors/1000101011-V-0000.bin"
private noncomputable def vp1000101011_1 : Blocks := edgeBlocks% "full/vectors/1000101011-V-0001.bin"
noncomputable def vp1000101011 : Blocks := (Blocks.join vp1000101011_0 vp1000101011_1)
private theorem bp10001010110 : Branch 0 (-4439761639/8000000 : ℚ) vp1000101011 := by
  apply branch_left_normalized (c:=vp10001010110) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4439761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4439761639/4000000 : ℚ) by norm_num]
  exact coverp10001010110
private noncomputable def ep10001010111_0 : Blocks := edgeBlocks% "full/vectors/10001010111-E-0000.bin"
private noncomputable def ep10001010111_1 : Blocks := edgeBlocks% "full/vectors/10001010111-E-0001.bin"
noncomputable def ep10001010111 : Blocks := (Blocks.join ep10001010111_0 ep10001010111_1)
private theorem idp10001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000101011.list =
    C ((2:ℤ)^163) * horner X vp10001010111.list + horner X ep10001010111.list := by
  exact edge_identity (B := (2:ℤ)^304) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001010111 : Branch 1 (-4439761639/8000000 : ℚ) vp1000101011 := by
  apply branch_checked idp10001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-4439761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4443761639/4000000 : ℚ) by norm_num]
  exact coverp10001010111
theorem coverp1000101011 : Covers (-4439761639/8000000 : ℚ) vp1000101011 := join_branches bp10001010110 bp10001010111
private noncomputable def vp10001010101_0 : Blocks := edgeBlocks% "full/vectors/10001010101-V-0000.bin"
noncomputable def vp10001010101 : Blocks := vp10001010101_0
theorem coverp10001010101 : Covers (-4435761639/4000000 : ℚ) vp10001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp10001010100_0 : Blocks := edgeBlocks% "full/vectors/10001010100-V-0000.bin"
noncomputable def vp10001010100 : Blocks := vp10001010100_0
theorem coverp10001010100 : Covers (-4431761639/4000000 : ℚ) vp10001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000101010_0 : Blocks := edgeBlocks% "full/vectors/1000101010-V-0000.bin"
private noncomputable def vp1000101010_1 : Blocks := edgeBlocks% "full/vectors/1000101010-V-0001.bin"
noncomputable def vp1000101010 : Blocks := (Blocks.join vp1000101010_0 vp1000101010_1)
private theorem bp10001010100 : Branch 0 (-4431761639/8000000 : ℚ) vp1000101010 := by
  apply branch_left_normalized (c:=vp10001010100) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-4431761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4431761639/4000000 : ℚ) by norm_num]
  exact coverp10001010100
private noncomputable def ep10001010101_0 : Blocks := edgeBlocks% "full/vectors/10001010101-E-0000.bin"
private noncomputable def ep10001010101_1 : Blocks := edgeBlocks% "full/vectors/10001010101-E-0001.bin"
noncomputable def ep10001010101 : Blocks := (Blocks.join ep10001010101_0 ep10001010101_1)
private theorem idp10001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000101010.list =
    C ((2:ℤ)^164) * horner X vp10001010101.list + horner X ep10001010101.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001010101 : Branch 1 (-4431761639/8000000 : ℚ) vp1000101010 := by
  apply branch_checked idp10001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4431761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4435761639/4000000 : ℚ) by norm_num]
  exact coverp10001010101
theorem coverp1000101010 : Covers (-4431761639/8000000 : ℚ) vp1000101010 := join_branches bp10001010100 bp10001010101
private noncomputable def vp100010101_0 : Blocks := edgeBlocks% "full/vectors/100010101-V-0000.bin"
private noncomputable def vp100010101_1 : Blocks := edgeBlocks% "full/vectors/100010101-V-0001.bin"
private noncomputable def vp100010101_2 : Blocks := edgeBlocks% "full/vectors/100010101-V-0002.bin"
noncomputable def vp100010101 : Blocks := (Blocks.join vp100010101_0 (Blocks.join vp100010101_1 vp100010101_2))
private theorem bp1000101010 : Branch 0 (-4431761639/16000000 : ℚ) vp100010101 := by
  apply branch_left_normalized (c:=vp1000101010) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-4431761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4431761639/8000000 : ℚ) by norm_num]
  exact coverp1000101010
private noncomputable def ep1000101011_0 : Blocks := edgeBlocks% "full/vectors/1000101011-E-0000.bin"
private noncomputable def ep1000101011_1 : Blocks := edgeBlocks% "full/vectors/1000101011-E-0001.bin"
private noncomputable def ep1000101011_2 : Blocks := edgeBlocks% "full/vectors/1000101011-E-0002.bin"
noncomputable def ep1000101011 : Blocks := (Blocks.join ep1000101011_0 (Blocks.join ep1000101011_1 ep1000101011_2))
private theorem idp1000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100010101.list =
    C ((2:ℤ)^305) * horner X vp1000101011.list + horner X ep1000101011.list := by
  exact edge_identity (B := (2:ℤ)^486) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000101011 : Branch 1 (-4431761639/16000000 : ℚ) vp100010101 := by
  apply branch_checked idp1000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-4431761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4439761639/8000000 : ℚ) by norm_num]
  exact coverp1000101011
theorem coverp100010101 : Covers (-4431761639/16000000 : ℚ) vp100010101 := join_branches bp1000101010 bp1000101011
private noncomputable def vp10001010011_0 : Blocks := edgeBlocks% "full/vectors/10001010011-V-0000.bin"
noncomputable def vp10001010011 : Blocks := vp10001010011_0
theorem coverp10001010011 : Covers (-4427761639/4000000 : ℚ) vp10001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp10001010010_0 : Blocks := edgeBlocks% "full/vectors/10001010010-V-0000.bin"
noncomputable def vp10001010010 : Blocks := vp10001010010_0
theorem coverp10001010010 : Covers (-4423761639/4000000 : ℚ) vp10001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp1000101001_0 : Blocks := edgeBlocks% "full/vectors/1000101001-V-0000.bin"
private noncomputable def vp1000101001_1 : Blocks := edgeBlocks% "full/vectors/1000101001-V-0001.bin"
noncomputable def vp1000101001 : Blocks := (Blocks.join vp1000101001_0 vp1000101001_1)
private theorem bp10001010010 : Branch 0 (-4423761639/8000000 : ℚ) vp1000101001 := by
  apply branch_left_normalized (c:=vp10001010010) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-4423761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4423761639/4000000 : ℚ) by norm_num]
  exact coverp10001010010
private noncomputable def ep10001010011_0 : Blocks := edgeBlocks% "full/vectors/10001010011-E-0000.bin"
private noncomputable def ep10001010011_1 : Blocks := edgeBlocks% "full/vectors/10001010011-E-0001.bin"
noncomputable def ep10001010011 : Blocks := (Blocks.join ep10001010011_0 ep10001010011_1)
private theorem idp10001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000101001.list =
    C ((2:ℤ)^164) * horner X vp10001010011.list + horner X ep10001010011.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001010011 : Branch 1 (-4423761639/8000000 : ℚ) vp1000101001 := by
  apply branch_checked idp10001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4423761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4427761639/4000000 : ℚ) by norm_num]
  exact coverp10001010011
theorem coverp1000101001 : Covers (-4423761639/8000000 : ℚ) vp1000101001 := join_branches bp10001010010 bp10001010011
private noncomputable def vp10001010001_0 : Blocks := edgeBlocks% "full/vectors/10001010001-V-0000.bin"
noncomputable def vp10001010001 : Blocks := vp10001010001_0
theorem coverp10001010001 : Covers (-4419761639/4000000 : ℚ) vp10001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp10001010000_0 : Blocks := edgeBlocks% "full/vectors/10001010000-V-0000.bin"
noncomputable def vp10001010000 : Blocks := vp10001010000_0
theorem coverp10001010000 : Covers (-4415761639/4000000 : ℚ) vp10001010000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000101000_0 : Blocks := edgeBlocks% "full/vectors/1000101000-V-0000.bin"
private noncomputable def vp1000101000_1 : Blocks := edgeBlocks% "full/vectors/1000101000-V-0001.bin"
noncomputable def vp1000101000 : Blocks := (Blocks.join vp1000101000_0 vp1000101000_1)
private theorem bp10001010000 : Branch 0 (-4415761639/8000000 : ℚ) vp1000101000 := by
  apply branch_left_normalized (c:=vp10001010000) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-4415761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4415761639/4000000 : ℚ) by norm_num]
  exact coverp10001010000
private noncomputable def ep10001010001_0 : Blocks := edgeBlocks% "full/vectors/10001010001-E-0000.bin"
private noncomputable def ep10001010001_1 : Blocks := edgeBlocks% "full/vectors/10001010001-E-0001.bin"
noncomputable def ep10001010001 : Blocks := (Blocks.join ep10001010001_0 ep10001010001_1)
private theorem idp10001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000101000.list =
    C ((2:ℤ)^163) * horner X vp10001010001.list + horner X ep10001010001.list := by
  exact edge_identity (B := (2:ℤ)^304) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001010001 : Branch 1 (-4415761639/8000000 : ℚ) vp1000101000 := by
  apply branch_checked idp10001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4415761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4419761639/4000000 : ℚ) by norm_num]
  exact coverp10001010001
theorem coverp1000101000 : Covers (-4415761639/8000000 : ℚ) vp1000101000 := join_branches bp10001010000 bp10001010001
private noncomputable def vp100010100_0 : Blocks := edgeBlocks% "full/vectors/100010100-V-0000.bin"
private noncomputable def vp100010100_1 : Blocks := edgeBlocks% "full/vectors/100010100-V-0001.bin"
private noncomputable def vp100010100_2 : Blocks := edgeBlocks% "full/vectors/100010100-V-0002.bin"
noncomputable def vp100010100 : Blocks := (Blocks.join vp100010100_0 (Blocks.join vp100010100_1 vp100010100_2))
private theorem bp1000101000 : Branch 0 (-4415761639/16000000 : ℚ) vp100010100 := by
  apply branch_left_normalized (c:=vp1000101000) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-4415761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4415761639/8000000 : ℚ) by norm_num]
  exact coverp1000101000
private noncomputable def ep1000101001_0 : Blocks := edgeBlocks% "full/vectors/1000101001-E-0000.bin"
private noncomputable def ep1000101001_1 : Blocks := edgeBlocks% "full/vectors/1000101001-E-0001.bin"
private noncomputable def ep1000101001_2 : Blocks := edgeBlocks% "full/vectors/1000101001-E-0002.bin"
noncomputable def ep1000101001 : Blocks := (Blocks.join ep1000101001_0 (Blocks.join ep1000101001_1 ep1000101001_2))
private theorem idp1000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100010100.list =
    C ((2:ℤ)^306) * horner X vp1000101001.list + horner X ep1000101001.list := by
  exact edge_identity (B := (2:ℤ)^486) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000101001 : Branch 1 (-4415761639/16000000 : ℚ) vp100010100 := by
  apply branch_checked idp1000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-4415761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4423761639/8000000 : ℚ) by norm_num]
  exact coverp1000101001
theorem coverp100010100 : Covers (-4415761639/16000000 : ℚ) vp100010100 := join_branches bp1000101000 bp1000101001
private noncomputable def vp10001010_0 : Blocks := edgeBlocks% "full/vectors/10001010-V-0000.bin"
private noncomputable def vp10001010_1 : Blocks := edgeBlocks% "full/vectors/10001010-V-0001.bin"
private noncomputable def vp10001010_2 : Blocks := edgeBlocks% "full/vectors/10001010-V-0002.bin"
private noncomputable def vp10001010_3 : Blocks := edgeBlocks% "full/vectors/10001010-V-0003.bin"
noncomputable def vp10001010 : Blocks := (Blocks.join (Blocks.join vp10001010_0 vp10001010_1) (Blocks.join vp10001010_2 vp10001010_3))
private theorem bp100010100 : Branch 0 (-4415761639/32000000 : ℚ) vp10001010 := by
  apply branch_left_normalized (c:=vp100010100) (k:=0) (m:=259) (by decide +kernel)
  rw [show 2*(-4415761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4415761639/16000000 : ℚ) by norm_num]
  exact coverp100010100
private noncomputable def ep100010101_0 : Blocks := edgeBlocks% "full/vectors/100010101-E-0000.bin"
private noncomputable def ep100010101_1 : Blocks := edgeBlocks% "full/vectors/100010101-E-0001.bin"
private noncomputable def ep100010101_2 : Blocks := edgeBlocks% "full/vectors/100010101-E-0002.bin"
private noncomputable def ep100010101_3 : Blocks := edgeBlocks% "full/vectors/100010101-E-0003.bin"
noncomputable def ep100010101 : Blocks := (Blocks.join (Blocks.join ep100010101_0 ep100010101_1) (Blocks.join ep100010101_2 ep100010101_3))
private theorem idp100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10001010.list =
    C ((2:ℤ)^586) * horner X vp100010101.list + horner X ep100010101.list := by
  exact edge_identity (B := (2:ℤ)^846) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100010101 : Branch 1 (-4415761639/32000000 : ℚ) vp10001010 := by
  apply branch_checked idp100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4415761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4431761639/16000000 : ℚ) by norm_num]
  exact coverp100010101
theorem coverp10001010 : Covers (-4415761639/32000000 : ℚ) vp10001010 := join_branches bp100010100 bp100010101
private noncomputable def vp1000101_0 : Blocks := edgeBlocks% "full/vectors/1000101-V-0000.bin"
private noncomputable def vp1000101_1 : Blocks := edgeBlocks% "full/vectors/1000101-V-0001.bin"
private noncomputable def vp1000101_2 : Blocks := edgeBlocks% "full/vectors/1000101-V-0002.bin"
private noncomputable def vp1000101_3 : Blocks := edgeBlocks% "full/vectors/1000101-V-0003.bin"
private noncomputable def vp1000101_4 : Blocks := edgeBlocks% "full/vectors/1000101-V-0004.bin"
private noncomputable def vp1000101_5 : Blocks := edgeBlocks% "full/vectors/1000101-V-0005.bin"
private noncomputable def vp1000101_6 : Blocks := edgeBlocks% "full/vectors/1000101-V-0006.bin"
private noncomputable def vp1000101_7 : Blocks := edgeBlocks% "full/vectors/1000101-V-0007.bin"
noncomputable def vp1000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1000101_0 vp1000101_1) (Blocks.join vp1000101_2 vp1000101_3)) (Blocks.join (Blocks.join vp1000101_4 vp1000101_5) (Blocks.join vp1000101_6 vp1000101_7)))
private theorem bp10001010 : Branch 0 (-4415761639/64000000 : ℚ) vp1000101 := by
  apply branch_left_normalized (c:=vp10001010) (k:=0) (m:=493) (by decide +kernel)
  rw [show 2*(-4415761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4415761639/32000000 : ℚ) by norm_num]
  exact coverp10001010
private noncomputable def ep10001011_0 : Blocks := edgeBlocks% "full/vectors/10001011-E-0000.bin"
private noncomputable def ep10001011_1 : Blocks := edgeBlocks% "full/vectors/10001011-E-0001.bin"
private noncomputable def ep10001011_2 : Blocks := edgeBlocks% "full/vectors/10001011-E-0002.bin"
private noncomputable def ep10001011_3 : Blocks := edgeBlocks% "full/vectors/10001011-E-0003.bin"
private noncomputable def ep10001011_4 : Blocks := edgeBlocks% "full/vectors/10001011-E-0004.bin"
private noncomputable def ep10001011_5 : Blocks := edgeBlocks% "full/vectors/10001011-E-0005.bin"
private noncomputable def ep10001011_6 : Blocks := edgeBlocks% "full/vectors/10001011-E-0006.bin"
private noncomputable def ep10001011_7 : Blocks := edgeBlocks% "full/vectors/10001011-E-0007.bin"
noncomputable def ep10001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10001011_0 ep10001011_1) (Blocks.join ep10001011_2 ep10001011_3)) (Blocks.join (Blocks.join ep10001011_4 ep10001011_5) (Blocks.join ep10001011_6 ep10001011_7)))
private theorem idp10001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000101.list =
    C ((2:ℤ)^1141) * horner X vp10001011.list + horner X ep10001011.list := by
  exact edge_identity (B := (2:ℤ)^1558) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001011 : Branch 1 (-4415761639/64000000 : ℚ) vp1000101 := by
  apply branch_checked idp10001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4415761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4447761639/32000000 : ℚ) by norm_num]
  exact coverp10001011
theorem coverp1000101 : Covers (-4415761639/64000000 : ℚ) vp1000101 := join_branches bp10001010 bp10001011
private noncomputable def vp10001001111_0 : Blocks := edgeBlocks% "full/vectors/10001001111-V-0000.bin"
noncomputable def vp10001001111 : Blocks := vp10001001111_0
theorem coverp10001001111 : Covers (-4411761639/4000000 : ℚ) vp10001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp10001001110_0 : Blocks := edgeBlocks% "full/vectors/10001001110-V-0000.bin"
noncomputable def vp10001001110 : Blocks := vp10001001110_0
theorem coverp10001001110 : Covers (-4407761639/4000000 : ℚ) vp10001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000100111_0 : Blocks := edgeBlocks% "full/vectors/1000100111-V-0000.bin"
private noncomputable def vp1000100111_1 : Blocks := edgeBlocks% "full/vectors/1000100111-V-0001.bin"
noncomputable def vp1000100111 : Blocks := (Blocks.join vp1000100111_0 vp1000100111_1)
private theorem bp10001001110 : Branch 0 (-4407761639/8000000 : ℚ) vp1000100111 := by
  apply branch_left_normalized (c:=vp10001001110) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-4407761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4407761639/4000000 : ℚ) by norm_num]
  exact coverp10001001110
private noncomputable def ep10001001111_0 : Blocks := edgeBlocks% "full/vectors/10001001111-E-0000.bin"
private noncomputable def ep10001001111_1 : Blocks := edgeBlocks% "full/vectors/10001001111-E-0001.bin"
noncomputable def ep10001001111 : Blocks := (Blocks.join ep10001001111_0 ep10001001111_1)
private theorem idp10001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000100111.list =
    C ((2:ℤ)^165) * horner X vp10001001111.list + horner X ep10001001111.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001001111 : Branch 1 (-4407761639/8000000 : ℚ) vp1000100111 := by
  apply branch_checked idp10001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4407761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4411761639/4000000 : ℚ) by norm_num]
  exact coverp10001001111
theorem coverp1000100111 : Covers (-4407761639/8000000 : ℚ) vp1000100111 := join_branches bp10001001110 bp10001001111
private noncomputable def vp10001001101_0 : Blocks := edgeBlocks% "full/vectors/10001001101-V-0000.bin"
noncomputable def vp10001001101 : Blocks := vp10001001101_0
theorem coverp10001001101 : Covers (-4403761639/4000000 : ℚ) vp10001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp10001001100_0 : Blocks := edgeBlocks% "full/vectors/10001001100-V-0000.bin"
noncomputable def vp10001001100 : Blocks := vp10001001100_0
theorem coverp10001001100 : Covers (-4399761639/4000000 : ℚ) vp10001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000100110_0 : Blocks := edgeBlocks% "full/vectors/1000100110-V-0000.bin"
private noncomputable def vp1000100110_1 : Blocks := edgeBlocks% "full/vectors/1000100110-V-0001.bin"
noncomputable def vp1000100110 : Blocks := (Blocks.join vp1000100110_0 vp1000100110_1)
private theorem bp10001001100 : Branch 0 (-4399761639/8000000 : ℚ) vp1000100110 := by
  apply branch_left_normalized (c:=vp10001001100) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4399761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4399761639/4000000 : ℚ) by norm_num]
  exact coverp10001001100
private noncomputable def ep10001001101_0 : Blocks := edgeBlocks% "full/vectors/10001001101-E-0000.bin"
private noncomputable def ep10001001101_1 : Blocks := edgeBlocks% "full/vectors/10001001101-E-0001.bin"
noncomputable def ep10001001101 : Blocks := (Blocks.join ep10001001101_0 ep10001001101_1)
private theorem idp10001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000100110.list =
    C ((2:ℤ)^164) * horner X vp10001001101.list + horner X ep10001001101.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001001101 : Branch 1 (-4399761639/8000000 : ℚ) vp1000100110 := by
  apply branch_checked idp10001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4399761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4403761639/4000000 : ℚ) by norm_num]
  exact coverp10001001101
theorem coverp1000100110 : Covers (-4399761639/8000000 : ℚ) vp1000100110 := join_branches bp10001001100 bp10001001101
private noncomputable def vp100010011_0 : Blocks := edgeBlocks% "full/vectors/100010011-V-0000.bin"
private noncomputable def vp100010011_1 : Blocks := edgeBlocks% "full/vectors/100010011-V-0001.bin"
private noncomputable def vp100010011_2 : Blocks := edgeBlocks% "full/vectors/100010011-V-0002.bin"
noncomputable def vp100010011 : Blocks := (Blocks.join vp100010011_0 (Blocks.join vp100010011_1 vp100010011_2))
private theorem bp1000100110 : Branch 0 (-4399761639/16000000 : ℚ) vp100010011 := by
  apply branch_left_normalized (c:=vp1000100110) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-4399761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4399761639/8000000 : ℚ) by norm_num]
  exact coverp1000100110
private noncomputable def ep1000100111_0 : Blocks := edgeBlocks% "full/vectors/1000100111-E-0000.bin"
private noncomputable def ep1000100111_1 : Blocks := edgeBlocks% "full/vectors/1000100111-E-0001.bin"
private noncomputable def ep1000100111_2 : Blocks := edgeBlocks% "full/vectors/1000100111-E-0002.bin"
noncomputable def ep1000100111 : Blocks := (Blocks.join ep1000100111_0 (Blocks.join ep1000100111_1 ep1000100111_2))
private theorem idp1000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100010011.list =
    C ((2:ℤ)^306) * horner X vp1000100111.list + horner X ep1000100111.list := by
  exact edge_identity (B := (2:ℤ)^487) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000100111 : Branch 1 (-4399761639/16000000 : ℚ) vp100010011 := by
  apply branch_checked idp1000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-4399761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4407761639/8000000 : ℚ) by norm_num]
  exact coverp1000100111
theorem coverp100010011 : Covers (-4399761639/16000000 : ℚ) vp100010011 := join_branches bp1000100110 bp1000100111
private noncomputable def vp10001001011_0 : Blocks := edgeBlocks% "full/vectors/10001001011-V-0000.bin"
noncomputable def vp10001001011 : Blocks := vp10001001011_0
theorem coverp10001001011 : Covers (-4395761639/4000000 : ℚ) vp10001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp10001001010_0 : Blocks := edgeBlocks% "full/vectors/10001001010-V-0000.bin"
noncomputable def vp10001001010 : Blocks := vp10001001010_0
theorem coverp10001001010 : Covers (-4391761639/4000000 : ℚ) vp10001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp1000100101_0 : Blocks := edgeBlocks% "full/vectors/1000100101-V-0000.bin"
private noncomputable def vp1000100101_1 : Blocks := edgeBlocks% "full/vectors/1000100101-V-0001.bin"
noncomputable def vp1000100101 : Blocks := (Blocks.join vp1000100101_0 vp1000100101_1)
private theorem bp10001001010 : Branch 0 (-4391761639/8000000 : ℚ) vp1000100101 := by
  apply branch_left_normalized (c:=vp10001001010) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-4391761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4391761639/4000000 : ℚ) by norm_num]
  exact coverp10001001010
private noncomputable def ep10001001011_0 : Blocks := edgeBlocks% "full/vectors/10001001011-E-0000.bin"
private noncomputable def ep10001001011_1 : Blocks := edgeBlocks% "full/vectors/10001001011-E-0001.bin"
noncomputable def ep10001001011 : Blocks := (Blocks.join ep10001001011_0 ep10001001011_1)
private theorem idp10001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000100101.list =
    C ((2:ℤ)^164) * horner X vp10001001011.list + horner X ep10001001011.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001001011 : Branch 1 (-4391761639/8000000 : ℚ) vp1000100101 := by
  apply branch_checked idp10001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4391761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4395761639/4000000 : ℚ) by norm_num]
  exact coverp10001001011
theorem coverp1000100101 : Covers (-4391761639/8000000 : ℚ) vp1000100101 := join_branches bp10001001010 bp10001001011
private noncomputable def vp10001001001_0 : Blocks := edgeBlocks% "full/vectors/10001001001-V-0000.bin"
noncomputable def vp10001001001 : Blocks := vp10001001001_0
theorem coverp10001001001 : Covers (-4387761639/4000000 : ℚ) vp10001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp10001001000_0 : Blocks := edgeBlocks% "full/vectors/10001001000-V-0000.bin"
noncomputable def vp10001001000 : Blocks := vp10001001000_0
theorem coverp10001001000 : Covers (-4383761639/4000000 : ℚ) vp10001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000100100_0 : Blocks := edgeBlocks% "full/vectors/1000100100-V-0000.bin"
private noncomputable def vp1000100100_1 : Blocks := edgeBlocks% "full/vectors/1000100100-V-0001.bin"
noncomputable def vp1000100100 : Blocks := (Blocks.join vp1000100100_0 vp1000100100_1)
private theorem bp10001001000 : Branch 0 (-4383761639/8000000 : ℚ) vp1000100100 := by
  apply branch_left_normalized (c:=vp10001001000) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4383761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4383761639/4000000 : ℚ) by norm_num]
  exact coverp10001001000
private noncomputable def ep10001001001_0 : Blocks := edgeBlocks% "full/vectors/10001001001-E-0000.bin"
private noncomputable def ep10001001001_1 : Blocks := edgeBlocks% "full/vectors/10001001001-E-0001.bin"
noncomputable def ep10001001001 : Blocks := (Blocks.join ep10001001001_0 ep10001001001_1)
private theorem idp10001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000100100.list =
    C ((2:ℤ)^162) * horner X vp10001001001.list + horner X ep10001001001.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001001001 : Branch 1 (-4383761639/8000000 : ℚ) vp1000100100 := by
  apply branch_checked idp10001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4383761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4387761639/4000000 : ℚ) by norm_num]
  exact coverp10001001001
theorem coverp1000100100 : Covers (-4383761639/8000000 : ℚ) vp1000100100 := join_branches bp10001001000 bp10001001001
private noncomputable def vp100010010_0 : Blocks := edgeBlocks% "full/vectors/100010010-V-0000.bin"
private noncomputable def vp100010010_1 : Blocks := edgeBlocks% "full/vectors/100010010-V-0001.bin"
private noncomputable def vp100010010_2 : Blocks := edgeBlocks% "full/vectors/100010010-V-0002.bin"
noncomputable def vp100010010 : Blocks := (Blocks.join vp100010010_0 (Blocks.join vp100010010_1 vp100010010_2))
private theorem bp1000100100 : Branch 0 (-4383761639/16000000 : ℚ) vp100010010 := by
  apply branch_left_normalized (c:=vp1000100100) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-4383761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4383761639/8000000 : ℚ) by norm_num]
  exact coverp1000100100
private noncomputable def ep1000100101_0 : Blocks := edgeBlocks% "full/vectors/1000100101-E-0000.bin"
private noncomputable def ep1000100101_1 : Blocks := edgeBlocks% "full/vectors/1000100101-E-0001.bin"
private noncomputable def ep1000100101_2 : Blocks := edgeBlocks% "full/vectors/1000100101-E-0002.bin"
noncomputable def ep1000100101 : Blocks := (Blocks.join ep1000100101_0 (Blocks.join ep1000100101_1 ep1000100101_2))
private theorem idp1000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100010010.list =
    C ((2:ℤ)^303) * horner X vp1000100101.list + horner X ep1000100101.list := by
  exact edge_identity (B := (2:ℤ)^484) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000100101 : Branch 1 (-4383761639/16000000 : ℚ) vp100010010 := by
  apply branch_checked idp1000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-4383761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4391761639/8000000 : ℚ) by norm_num]
  exact coverp1000100101
theorem coverp100010010 : Covers (-4383761639/16000000 : ℚ) vp100010010 := join_branches bp1000100100 bp1000100101
private noncomputable def vp10001001_0 : Blocks := edgeBlocks% "full/vectors/10001001-V-0000.bin"
private noncomputable def vp10001001_1 : Blocks := edgeBlocks% "full/vectors/10001001-V-0001.bin"
private noncomputable def vp10001001_2 : Blocks := edgeBlocks% "full/vectors/10001001-V-0002.bin"
private noncomputable def vp10001001_3 : Blocks := edgeBlocks% "full/vectors/10001001-V-0003.bin"
noncomputable def vp10001001 : Blocks := (Blocks.join (Blocks.join vp10001001_0 vp10001001_1) (Blocks.join vp10001001_2 vp10001001_3))
private theorem bp100010010 : Branch 0 (-4383761639/32000000 : ℚ) vp10001001 := by
  apply branch_left_normalized (c:=vp100010010) (k:=0) (m:=258) (by decide +kernel)
  rw [show 2*(-4383761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4383761639/16000000 : ℚ) by norm_num]
  exact coverp100010010
private noncomputable def ep100010011_0 : Blocks := edgeBlocks% "full/vectors/100010011-E-0000.bin"
private noncomputable def ep100010011_1 : Blocks := edgeBlocks% "full/vectors/100010011-E-0001.bin"
private noncomputable def ep100010011_2 : Blocks := edgeBlocks% "full/vectors/100010011-E-0002.bin"
private noncomputable def ep100010011_3 : Blocks := edgeBlocks% "full/vectors/100010011-E-0003.bin"
noncomputable def ep100010011 : Blocks := (Blocks.join (Blocks.join ep100010011_0 ep100010011_1) (Blocks.join ep100010011_2 ep100010011_3))
private theorem idp100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10001001.list =
    C ((2:ℤ)^584) * horner X vp100010011.list + horner X ep100010011.list := by
  exact edge_identity (B := (2:ℤ)^845) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100010011 : Branch 1 (-4383761639/32000000 : ℚ) vp10001001 := by
  apply branch_checked idp100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4383761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4399761639/16000000 : ℚ) by norm_num]
  exact coverp100010011
theorem coverp10001001 : Covers (-4383761639/32000000 : ℚ) vp10001001 := join_branches bp100010010 bp100010011
private noncomputable def vp10001000111_0 : Blocks := edgeBlocks% "full/vectors/10001000111-V-0000.bin"
noncomputable def vp10001000111 : Blocks := vp10001000111_0
theorem coverp10001000111 : Covers (-4379761639/4000000 : ℚ) vp10001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp10001000110_0 : Blocks := edgeBlocks% "full/vectors/10001000110-V-0000.bin"
noncomputable def vp10001000110 : Blocks := vp10001000110_0
theorem coverp10001000110 : Covers (-4375761639/4000000 : ℚ) vp10001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000100011_0 : Blocks := edgeBlocks% "full/vectors/1000100011-V-0000.bin"
private noncomputable def vp1000100011_1 : Blocks := edgeBlocks% "full/vectors/1000100011-V-0001.bin"
noncomputable def vp1000100011 : Blocks := (Blocks.join vp1000100011_0 vp1000100011_1)
private theorem bp10001000110 : Branch 0 (-4375761639/8000000 : ℚ) vp1000100011 := by
  apply branch_left_normalized (c:=vp10001000110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4375761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4375761639/4000000 : ℚ) by norm_num]
  exact coverp10001000110
private noncomputable def ep10001000111_0 : Blocks := edgeBlocks% "full/vectors/10001000111-E-0000.bin"
private noncomputable def ep10001000111_1 : Blocks := edgeBlocks% "full/vectors/10001000111-E-0001.bin"
noncomputable def ep10001000111 : Blocks := (Blocks.join ep10001000111_0 ep10001000111_1)
private theorem idp10001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000100011.list =
    C ((2:ℤ)^161) * horner X vp10001000111.list + horner X ep10001000111.list := by
  exact edge_identity (B := (2:ℤ)^298) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001000111 : Branch 1 (-4375761639/8000000 : ℚ) vp1000100011 := by
  apply branch_checked idp10001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4375761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4379761639/4000000 : ℚ) by norm_num]
  exact coverp10001000111
theorem coverp1000100011 : Covers (-4375761639/8000000 : ℚ) vp1000100011 := join_branches bp10001000110 bp10001000111
private noncomputable def vp10001000101_0 : Blocks := edgeBlocks% "full/vectors/10001000101-V-0000.bin"
noncomputable def vp10001000101 : Blocks := vp10001000101_0
theorem coverp10001000101 : Covers (-4371761639/4000000 : ℚ) vp10001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp10001000100_0 : Blocks := edgeBlocks% "full/vectors/10001000100-V-0000.bin"
noncomputable def vp10001000100 : Blocks := vp10001000100_0
theorem coverp10001000100 : Covers (-4367761639/4000000 : ℚ) vp10001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000100010_0 : Blocks := edgeBlocks% "full/vectors/1000100010-V-0000.bin"
private noncomputable def vp1000100010_1 : Blocks := edgeBlocks% "full/vectors/1000100010-V-0001.bin"
noncomputable def vp1000100010 : Blocks := (Blocks.join vp1000100010_0 vp1000100010_1)
private theorem bp10001000100 : Branch 0 (-4367761639/8000000 : ℚ) vp1000100010 := by
  apply branch_left_normalized (c:=vp10001000100) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4367761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4367761639/4000000 : ℚ) by norm_num]
  exact coverp10001000100
private noncomputable def ep10001000101_0 : Blocks := edgeBlocks% "full/vectors/10001000101-E-0000.bin"
private noncomputable def ep10001000101_1 : Blocks := edgeBlocks% "full/vectors/10001000101-E-0001.bin"
noncomputable def ep10001000101 : Blocks := (Blocks.join ep10001000101_0 ep10001000101_1)
private theorem idp10001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000100010.list =
    C ((2:ℤ)^161) * horner X vp10001000101.list + horner X ep10001000101.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001000101 : Branch 1 (-4367761639/8000000 : ℚ) vp1000100010 := by
  apply branch_checked idp10001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4367761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4371761639/4000000 : ℚ) by norm_num]
  exact coverp10001000101
theorem coverp1000100010 : Covers (-4367761639/8000000 : ℚ) vp1000100010 := join_branches bp10001000100 bp10001000101
private noncomputable def vp100010001_0 : Blocks := edgeBlocks% "full/vectors/100010001-V-0000.bin"
private noncomputable def vp100010001_1 : Blocks := edgeBlocks% "full/vectors/100010001-V-0001.bin"
noncomputable def vp100010001 : Blocks := (Blocks.join vp100010001_0 vp100010001_1)
private theorem bp1000100010 : Branch 0 (-4367761639/16000000 : ℚ) vp100010001 := by
  apply branch_left_normalized (c:=vp1000100010) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-4367761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4367761639/8000000 : ℚ) by norm_num]
  exact coverp1000100010
private noncomputable def ep1000100011_0 : Blocks := edgeBlocks% "full/vectors/1000100011-E-0000.bin"
private noncomputable def ep1000100011_1 : Blocks := edgeBlocks% "full/vectors/1000100011-E-0001.bin"
noncomputable def ep1000100011 : Blocks := (Blocks.join ep1000100011_0 ep1000100011_1)
private theorem idp1000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100010001.list =
    C ((2:ℤ)^301) * horner X vp1000100011.list + horner X ep1000100011.list := by
  exact edge_identity (B := (2:ℤ)^477) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000100011 : Branch 1 (-4367761639/16000000 : ℚ) vp100010001 := by
  apply branch_checked idp1000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-4367761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4375761639/8000000 : ℚ) by norm_num]
  exact coverp1000100011
theorem coverp100010001 : Covers (-4367761639/16000000 : ℚ) vp100010001 := join_branches bp1000100010 bp1000100011
private noncomputable def vp1000100001_0 : Blocks := edgeBlocks% "full/vectors/1000100001-V-0000.bin"
private noncomputable def vp1000100001_1 : Blocks := edgeBlocks% "full/vectors/1000100001-V-0001.bin"
noncomputable def vp1000100001 : Blocks := (Blocks.join vp1000100001_0 vp1000100001_1)
theorem coverp1000100001 : Covers (-4359761639/8000000 : ℚ) vp1000100001 := cover_leaf (by decide +kernel)
private noncomputable def vp1000100000_0 : Blocks := edgeBlocks% "full/vectors/1000100000-V-0000.bin"
private noncomputable def vp1000100000_1 : Blocks := edgeBlocks% "full/vectors/1000100000-V-0001.bin"
noncomputable def vp1000100000 : Blocks := (Blocks.join vp1000100000_0 vp1000100000_1)
theorem coverp1000100000 : Covers (-4351761639/8000000 : ℚ) vp1000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp100010000_0 : Blocks := edgeBlocks% "full/vectors/100010000-V-0000.bin"
private noncomputable def vp100010000_1 : Blocks := edgeBlocks% "full/vectors/100010000-V-0001.bin"
noncomputable def vp100010000 : Blocks := (Blocks.join vp100010000_0 vp100010000_1)
private theorem bp1000100000 : Branch 0 (-4351761639/16000000 : ℚ) vp100010000 := by
  apply branch_left_normalized (c:=vp1000100000) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-4351761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4351761639/8000000 : ℚ) by norm_num]
  exact coverp1000100000
private noncomputable def ep1000100001_0 : Blocks := edgeBlocks% "full/vectors/1000100001-E-0000.bin"
private noncomputable def ep1000100001_1 : Blocks := edgeBlocks% "full/vectors/1000100001-E-0001.bin"
noncomputable def ep1000100001 : Blocks := (Blocks.join ep1000100001_0 ep1000100001_1)
private theorem idp1000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100010000.list =
    C ((2:ℤ)^301) * horner X vp1000100001.list + horner X ep1000100001.list := by
  exact edge_identity (B := (2:ℤ)^475) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000100001 : Branch 1 (-4351761639/16000000 : ℚ) vp100010000 := by
  apply branch_checked idp1000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-4351761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4359761639/8000000 : ℚ) by norm_num]
  exact coverp1000100001
theorem coverp100010000 : Covers (-4351761639/16000000 : ℚ) vp100010000 := join_branches bp1000100000 bp1000100001
private noncomputable def vp10001000_0 : Blocks := edgeBlocks% "full/vectors/10001000-V-0000.bin"
private noncomputable def vp10001000_1 : Blocks := edgeBlocks% "full/vectors/10001000-V-0001.bin"
private noncomputable def vp10001000_2 : Blocks := edgeBlocks% "full/vectors/10001000-V-0002.bin"
private noncomputable def vp10001000_3 : Blocks := edgeBlocks% "full/vectors/10001000-V-0003.bin"
noncomputable def vp10001000 : Blocks := (Blocks.join (Blocks.join vp10001000_0 vp10001000_1) (Blocks.join vp10001000_2 vp10001000_3))
private theorem bp100010000 : Branch 0 (-4351761639/32000000 : ℚ) vp10001000 := by
  apply branch_left_normalized (c:=vp100010000) (k:=0) (m:=254) (by decide +kernel)
  rw [show 2*(-4351761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4351761639/16000000 : ℚ) by norm_num]
  exact coverp100010000
private noncomputable def ep100010001_0 : Blocks := edgeBlocks% "full/vectors/100010001-E-0000.bin"
private noncomputable def ep100010001_1 : Blocks := edgeBlocks% "full/vectors/100010001-E-0001.bin"
private noncomputable def ep100010001_2 : Blocks := edgeBlocks% "full/vectors/100010001-E-0002.bin"
private noncomputable def ep100010001_3 : Blocks := edgeBlocks% "full/vectors/100010001-E-0003.bin"
noncomputable def ep100010001 : Blocks := (Blocks.join (Blocks.join ep100010001_0 ep100010001_1) (Blocks.join ep100010001_2 ep100010001_3))
private theorem idp100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10001000.list =
    C ((2:ℤ)^583) * horner X vp100010001.list + horner X ep100010001.list := by
  exact edge_identity (B := (2:ℤ)^838) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100010001 : Branch 1 (-4351761639/32000000 : ℚ) vp10001000 := by
  apply branch_checked idp100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4351761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4367761639/16000000 : ℚ) by norm_num]
  exact coverp100010001
theorem coverp10001000 : Covers (-4351761639/32000000 : ℚ) vp10001000 := join_branches bp100010000 bp100010001
private noncomputable def vp1000100_0 : Blocks := edgeBlocks% "full/vectors/1000100-V-0000.bin"
private noncomputable def vp1000100_1 : Blocks := edgeBlocks% "full/vectors/1000100-V-0001.bin"
private noncomputable def vp1000100_2 : Blocks := edgeBlocks% "full/vectors/1000100-V-0002.bin"
private noncomputable def vp1000100_3 : Blocks := edgeBlocks% "full/vectors/1000100-V-0003.bin"
private noncomputable def vp1000100_4 : Blocks := edgeBlocks% "full/vectors/1000100-V-0004.bin"
private noncomputable def vp1000100_5 : Blocks := edgeBlocks% "full/vectors/1000100-V-0005.bin"
private noncomputable def vp1000100_6 : Blocks := edgeBlocks% "full/vectors/1000100-V-0006.bin"
private noncomputable def vp1000100_7 : Blocks := edgeBlocks% "full/vectors/1000100-V-0007.bin"
noncomputable def vp1000100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1000100_0 vp1000100_1) (Blocks.join vp1000100_2 vp1000100_3)) (Blocks.join (Blocks.join vp1000100_4 vp1000100_5) (Blocks.join vp1000100_6 vp1000100_7)))
private theorem bp10001000 : Branch 0 (-4351761639/64000000 : ℚ) vp1000100 := by
  apply branch_left_normalized (c:=vp10001000) (k:=0) (m:=491) (by decide +kernel)
  rw [show 2*(-4351761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4351761639/32000000 : ℚ) by norm_num]
  exact coverp10001000
private noncomputable def ep10001001_0 : Blocks := edgeBlocks% "full/vectors/10001001-E-0000.bin"
private noncomputable def ep10001001_1 : Blocks := edgeBlocks% "full/vectors/10001001-E-0001.bin"
private noncomputable def ep10001001_2 : Blocks := edgeBlocks% "full/vectors/10001001-E-0002.bin"
private noncomputable def ep10001001_3 : Blocks := edgeBlocks% "full/vectors/10001001-E-0003.bin"
private noncomputable def ep10001001_4 : Blocks := edgeBlocks% "full/vectors/10001001-E-0004.bin"
private noncomputable def ep10001001_5 : Blocks := edgeBlocks% "full/vectors/10001001-E-0005.bin"
private noncomputable def ep10001001_6 : Blocks := edgeBlocks% "full/vectors/10001001-E-0006.bin"
private noncomputable def ep10001001_7 : Blocks := edgeBlocks% "full/vectors/10001001-E-0007.bin"
noncomputable def ep10001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10001001_0 ep10001001_1) (Blocks.join ep10001001_2 ep10001001_3)) (Blocks.join (Blocks.join ep10001001_4 ep10001001_5) (Blocks.join ep10001001_6 ep10001001_7)))
private theorem idp10001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000100.list =
    C ((2:ℤ)^1138) * horner X vp10001001.list + horner X ep10001001.list := by
  exact edge_identity (B := (2:ℤ)^1557) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10001001 : Branch 1 (-4351761639/64000000 : ℚ) vp1000100 := by
  apply branch_checked idp10001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4351761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4383761639/32000000 : ℚ) by norm_num]
  exact coverp10001001
theorem coverp1000100 : Covers (-4351761639/64000000 : ℚ) vp1000100 := join_branches bp10001000 bp10001001
private noncomputable def vp100010_0 : Blocks := edgeBlocks% "full/vectors/100010-V-0000.bin"
private noncomputable def vp100010_1 : Blocks := edgeBlocks% "full/vectors/100010-V-0001.bin"
private noncomputable def vp100010_2 : Blocks := edgeBlocks% "full/vectors/100010-V-0002.bin"
private noncomputable def vp100010_3 : Blocks := edgeBlocks% "full/vectors/100010-V-0003.bin"
private noncomputable def vp100010_4 : Blocks := edgeBlocks% "full/vectors/100010-V-0004.bin"
private noncomputable def vp100010_5 : Blocks := edgeBlocks% "full/vectors/100010-V-0005.bin"
private noncomputable def vp100010_6 : Blocks := edgeBlocks% "full/vectors/100010-V-0006.bin"
private noncomputable def vp100010_7 : Blocks := edgeBlocks% "full/vectors/100010-V-0007.bin"
private noncomputable def vp100010_8 : Blocks := edgeBlocks% "full/vectors/100010-V-0008.bin"
private noncomputable def vp100010_9 : Blocks := edgeBlocks% "full/vectors/100010-V-0009.bin"
private noncomputable def vp100010_10 : Blocks := edgeBlocks% "full/vectors/100010-V-0010.bin"
private noncomputable def vp100010_11 : Blocks := edgeBlocks% "full/vectors/100010-V-0011.bin"
private noncomputable def vp100010_12 : Blocks := edgeBlocks% "full/vectors/100010-V-0012.bin"
private noncomputable def vp100010_13 : Blocks := edgeBlocks% "full/vectors/100010-V-0013.bin"
private noncomputable def vp100010_14 : Blocks := edgeBlocks% "full/vectors/100010-V-0014.bin"
noncomputable def vp100010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp100010_0 (Blocks.join vp100010_1 vp100010_2)) (Blocks.join (Blocks.join vp100010_3 vp100010_4) (Blocks.join vp100010_5 vp100010_6))) (Blocks.join (Blocks.join (Blocks.join vp100010_7 vp100010_8) (Blocks.join vp100010_9 vp100010_10)) (Blocks.join (Blocks.join vp100010_11 vp100010_12) (Blocks.join vp100010_13 vp100010_14))))
private theorem bp1000100 : Branch 0 (-4351761639/128000000 : ℚ) vp100010 := by
  apply branch_left_normalized (c:=vp1000100) (k:=0) (m:=958) (by decide +kernel)
  rw [show 2*(-4351761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-4351761639/64000000 : ℚ) by norm_num]
  exact coverp1000100
private noncomputable def ep1000101_0 : Blocks := edgeBlocks% "full/vectors/1000101-E-0000.bin"
private noncomputable def ep1000101_1 : Blocks := edgeBlocks% "full/vectors/1000101-E-0001.bin"
private noncomputable def ep1000101_2 : Blocks := edgeBlocks% "full/vectors/1000101-E-0002.bin"
private noncomputable def ep1000101_3 : Blocks := edgeBlocks% "full/vectors/1000101-E-0003.bin"
private noncomputable def ep1000101_4 : Blocks := edgeBlocks% "full/vectors/1000101-E-0004.bin"
private noncomputable def ep1000101_5 : Blocks := edgeBlocks% "full/vectors/1000101-E-0005.bin"
private noncomputable def ep1000101_6 : Blocks := edgeBlocks% "full/vectors/1000101-E-0006.bin"
private noncomputable def ep1000101_7 : Blocks := edgeBlocks% "full/vectors/1000101-E-0007.bin"
private noncomputable def ep1000101_8 : Blocks := edgeBlocks% "full/vectors/1000101-E-0008.bin"
private noncomputable def ep1000101_9 : Blocks := edgeBlocks% "full/vectors/1000101-E-0009.bin"
private noncomputable def ep1000101_10 : Blocks := edgeBlocks% "full/vectors/1000101-E-0010.bin"
private noncomputable def ep1000101_11 : Blocks := edgeBlocks% "full/vectors/1000101-E-0011.bin"
private noncomputable def ep1000101_12 : Blocks := edgeBlocks% "full/vectors/1000101-E-0012.bin"
private noncomputable def ep1000101_13 : Blocks := edgeBlocks% "full/vectors/1000101-E-0013.bin"
private noncomputable def ep1000101_14 : Blocks := edgeBlocks% "full/vectors/1000101-E-0014.bin"
noncomputable def ep1000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1000101_0 (Blocks.join ep1000101_1 ep1000101_2)) (Blocks.join (Blocks.join ep1000101_3 ep1000101_4) (Blocks.join ep1000101_5 ep1000101_6))) (Blocks.join (Blocks.join (Blocks.join ep1000101_7 ep1000101_8) (Blocks.join ep1000101_9 ep1000101_10)) (Blocks.join (Blocks.join ep1000101_11 ep1000101_12) (Blocks.join ep1000101_13 ep1000101_14))))
private theorem idp1000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100010.list =
    C ((2:ℤ)^2234) * horner X vp1000101.list + horner X ep1000101.list := by
  exact edge_identity (B := (2:ℤ)^2968) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000101 : Branch 1 (-4351761639/128000000 : ℚ) vp100010 := by
  apply branch_checked idp1000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4351761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-4415761639/64000000 : ℚ) by norm_num]
  exact coverp1000101
theorem coverp100010 : Covers (-4351761639/128000000 : ℚ) vp100010 := join_branches bp1000100 bp1000101
private noncomputable def vp10001_0 : Blocks := edgeBlocks% "full/vectors/10001-V-0000.bin"
private noncomputable def vp10001_1 : Blocks := edgeBlocks% "full/vectors/10001-V-0001.bin"
private noncomputable def vp10001_2 : Blocks := edgeBlocks% "full/vectors/10001-V-0002.bin"
private noncomputable def vp10001_3 : Blocks := edgeBlocks% "full/vectors/10001-V-0003.bin"
private noncomputable def vp10001_4 : Blocks := edgeBlocks% "full/vectors/10001-V-0004.bin"
private noncomputable def vp10001_5 : Blocks := edgeBlocks% "full/vectors/10001-V-0005.bin"
private noncomputable def vp10001_6 : Blocks := edgeBlocks% "full/vectors/10001-V-0006.bin"
private noncomputable def vp10001_7 : Blocks := edgeBlocks% "full/vectors/10001-V-0007.bin"
private noncomputable def vp10001_8 : Blocks := edgeBlocks% "full/vectors/10001-V-0008.bin"
private noncomputable def vp10001_9 : Blocks := edgeBlocks% "full/vectors/10001-V-0009.bin"
private noncomputable def vp10001_10 : Blocks := edgeBlocks% "full/vectors/10001-V-0010.bin"
private noncomputable def vp10001_11 : Blocks := edgeBlocks% "full/vectors/10001-V-0011.bin"
private noncomputable def vp10001_12 : Blocks := edgeBlocks% "full/vectors/10001-V-0012.bin"
private noncomputable def vp10001_13 : Blocks := edgeBlocks% "full/vectors/10001-V-0013.bin"
private noncomputable def vp10001_14 : Blocks := edgeBlocks% "full/vectors/10001-V-0014.bin"
private noncomputable def vp10001_15 : Blocks := edgeBlocks% "full/vectors/10001-V-0015.bin"
private noncomputable def vp10001_16 : Blocks := edgeBlocks% "full/vectors/10001-V-0016.bin"
private noncomputable def vp10001_17 : Blocks := edgeBlocks% "full/vectors/10001-V-0017.bin"
private noncomputable def vp10001_18 : Blocks := edgeBlocks% "full/vectors/10001-V-0018.bin"
private noncomputable def vp10001_19 : Blocks := edgeBlocks% "full/vectors/10001-V-0019.bin"
private noncomputable def vp10001_20 : Blocks := edgeBlocks% "full/vectors/10001-V-0020.bin"
private noncomputable def vp10001_21 : Blocks := edgeBlocks% "full/vectors/10001-V-0021.bin"
private noncomputable def vp10001_22 : Blocks := edgeBlocks% "full/vectors/10001-V-0022.bin"
private noncomputable def vp10001_23 : Blocks := edgeBlocks% "full/vectors/10001-V-0023.bin"
private noncomputable def vp10001_24 : Blocks := edgeBlocks% "full/vectors/10001-V-0024.bin"
private noncomputable def vp10001_25 : Blocks := edgeBlocks% "full/vectors/10001-V-0025.bin"
private noncomputable def vp10001_26 : Blocks := edgeBlocks% "full/vectors/10001-V-0026.bin"
private noncomputable def vp10001_27 : Blocks := edgeBlocks% "full/vectors/10001-V-0027.bin"
private noncomputable def vp10001_28 : Blocks := edgeBlocks% "full/vectors/10001-V-0028.bin"
noncomputable def vp10001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp10001_0 (Blocks.join vp10001_1 vp10001_2)) (Blocks.join (Blocks.join vp10001_3 vp10001_4) (Blocks.join vp10001_5 vp10001_6))) (Blocks.join (Blocks.join vp10001_7 (Blocks.join vp10001_8 vp10001_9)) (Blocks.join (Blocks.join vp10001_10 vp10001_11) (Blocks.join vp10001_12 vp10001_13)))) (Blocks.join (Blocks.join (Blocks.join vp10001_14 (Blocks.join vp10001_15 vp10001_16)) (Blocks.join (Blocks.join vp10001_17 vp10001_18) (Blocks.join vp10001_19 vp10001_20))) (Blocks.join (Blocks.join (Blocks.join vp10001_21 vp10001_22) (Blocks.join vp10001_23 vp10001_24)) (Blocks.join (Blocks.join vp10001_25 vp10001_26) (Blocks.join vp10001_27 vp10001_28)))))
private theorem bp100010 : Branch 0 (-4351761639/256000000 : ℚ) vp10001 := by
  apply branch_left_normalized (c:=vp100010) (k:=0) (m:=1871) (by decide +kernel)
  rw [show 2*(-4351761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-4351761639/128000000 : ℚ) by norm_num]
  exact coverp100010
private noncomputable def ep100011_0 : Blocks := edgeBlocks% "full/vectors/100011-E-0000.bin"
private noncomputable def ep100011_1 : Blocks := edgeBlocks% "full/vectors/100011-E-0001.bin"
private noncomputable def ep100011_2 : Blocks := edgeBlocks% "full/vectors/100011-E-0002.bin"
private noncomputable def ep100011_3 : Blocks := edgeBlocks% "full/vectors/100011-E-0003.bin"
private noncomputable def ep100011_4 : Blocks := edgeBlocks% "full/vectors/100011-E-0004.bin"
private noncomputable def ep100011_5 : Blocks := edgeBlocks% "full/vectors/100011-E-0005.bin"
private noncomputable def ep100011_6 : Blocks := edgeBlocks% "full/vectors/100011-E-0006.bin"
private noncomputable def ep100011_7 : Blocks := edgeBlocks% "full/vectors/100011-E-0007.bin"
private noncomputable def ep100011_8 : Blocks := edgeBlocks% "full/vectors/100011-E-0008.bin"
private noncomputable def ep100011_9 : Blocks := edgeBlocks% "full/vectors/100011-E-0009.bin"
private noncomputable def ep100011_10 : Blocks := edgeBlocks% "full/vectors/100011-E-0010.bin"
private noncomputable def ep100011_11 : Blocks := edgeBlocks% "full/vectors/100011-E-0011.bin"
private noncomputable def ep100011_12 : Blocks := edgeBlocks% "full/vectors/100011-E-0012.bin"
private noncomputable def ep100011_13 : Blocks := edgeBlocks% "full/vectors/100011-E-0013.bin"
private noncomputable def ep100011_14 : Blocks := edgeBlocks% "full/vectors/100011-E-0014.bin"
private noncomputable def ep100011_15 : Blocks := edgeBlocks% "full/vectors/100011-E-0015.bin"
private noncomputable def ep100011_16 : Blocks := edgeBlocks% "full/vectors/100011-E-0016.bin"
private noncomputable def ep100011_17 : Blocks := edgeBlocks% "full/vectors/100011-E-0017.bin"
private noncomputable def ep100011_18 : Blocks := edgeBlocks% "full/vectors/100011-E-0018.bin"
private noncomputable def ep100011_19 : Blocks := edgeBlocks% "full/vectors/100011-E-0019.bin"
private noncomputable def ep100011_20 : Blocks := edgeBlocks% "full/vectors/100011-E-0020.bin"
private noncomputable def ep100011_21 : Blocks := edgeBlocks% "full/vectors/100011-E-0021.bin"
private noncomputable def ep100011_22 : Blocks := edgeBlocks% "full/vectors/100011-E-0022.bin"
private noncomputable def ep100011_23 : Blocks := edgeBlocks% "full/vectors/100011-E-0023.bin"
private noncomputable def ep100011_24 : Blocks := edgeBlocks% "full/vectors/100011-E-0024.bin"
private noncomputable def ep100011_25 : Blocks := edgeBlocks% "full/vectors/100011-E-0025.bin"
private noncomputable def ep100011_26 : Blocks := edgeBlocks% "full/vectors/100011-E-0026.bin"
private noncomputable def ep100011_27 : Blocks := edgeBlocks% "full/vectors/100011-E-0027.bin"
private noncomputable def ep100011_28 : Blocks := edgeBlocks% "full/vectors/100011-E-0028.bin"
noncomputable def ep100011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep100011_0 (Blocks.join ep100011_1 ep100011_2)) (Blocks.join (Blocks.join ep100011_3 ep100011_4) (Blocks.join ep100011_5 ep100011_6))) (Blocks.join (Blocks.join ep100011_7 (Blocks.join ep100011_8 ep100011_9)) (Blocks.join (Blocks.join ep100011_10 ep100011_11) (Blocks.join ep100011_12 ep100011_13)))) (Blocks.join (Blocks.join (Blocks.join ep100011_14 (Blocks.join ep100011_15 ep100011_16)) (Blocks.join (Blocks.join ep100011_17 ep100011_18) (Blocks.join ep100011_19 ep100011_20))) (Blocks.join (Blocks.join (Blocks.join ep100011_21 ep100011_22) (Blocks.join ep100011_23 ep100011_24)) (Blocks.join (Blocks.join ep100011_25 ep100011_26) (Blocks.join ep100011_27 ep100011_28)))))
private def ptsp100011 : List ℤ := [((2:ℤ)^3319+0),((2:ℤ)^3319+1)]
private theorem boundp100011 : 2^vp10001.size*absSum vp10001.list + ((2:ℤ)^4346*absSum vp100011.list+absSum ep100011.list) < (2:ℤ)^5693 := by decide +kernel
private theorem pointp100011_0 : fastHom 1 ((2:ℤ)^3319+0) vp10001 = ((2:ℤ)^4346)*vp100011.subst ((2:ℤ)^3319+0)+ep100011.subst ((2:ℤ)^3319+0) := by decide +kernel
private theorem pointp100011_1 : fastHom 1 ((2:ℤ)^3319+1) vp10001 = ((2:ℤ)^4346)*vp100011.subst ((2:ℤ)^3319+1)+ep100011.subst ((2:ℤ)^3319+1) := by decide +kernel
private theorem checkp100011 (x:ℤ) (hx:x ∈ ptsp100011) : fastHom 1 x vp10001 = ((2:ℤ)^4346)*vp100011.subst x+ep100011.subst x := by
  simp only [ptsp100011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp100011_0
  · exact pointp100011_1
private theorem idp100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10001.list =
    C ((2:ℤ)^4346) * horner X vp100011.list + horner X ep100011.list := by
  apply edge_identity (B := (2:ℤ)^5693) (by decide) (by positivity) (by positivity) boundp100011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp100011 (by decide +kernel)
  · have h : ptsp100011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp100011.trans_le (by decide +kernel)
  · exact checkp100011
private theorem bp100011 : Branch 1 (-4351761639/256000000 : ℚ) vp10001 := by
  apply branch_checked idp100011 (by positivity) (by decide +kernel)
  rw [show 2*(-4351761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-4479761639/128000000 : ℚ) by norm_num]
  exact coverp100011
theorem coverp10001 : Covers (-4351761639/256000000 : ℚ) vp10001 := join_branches bp100010 bp100011
end NextProof.EdgeFull

