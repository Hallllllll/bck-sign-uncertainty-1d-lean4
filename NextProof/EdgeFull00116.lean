import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00115

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp010100111111_0 : Blocks := edgeBlocks% "full/vectors/010100111111-V-0000.bin"
noncomputable def vp010100111111 : Blocks := vp010100111111_0
theorem coverp010100111111 : Covers (-2685761639/2000000 : ℚ) vp010100111111 := cover_leaf (by decide +kernel)
private noncomputable def vp010100111110_0 : Blocks := edgeBlocks% "full/vectors/010100111110-V-0000.bin"
noncomputable def vp010100111110 : Blocks := vp010100111110_0
theorem coverp010100111110 : Covers (-2683761639/2000000 : ℚ) vp010100111110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010011111_0 : Blocks := edgeBlocks% "full/vectors/01010011111-V-0000.bin"
noncomputable def vp01010011111 : Blocks := vp01010011111_0
private theorem bp010100111110 : Branch 0 (-2683761639/4000000 : ℚ) vp01010011111 := by
  apply branch_left_normalized (c:=vp010100111110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2683761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2683761639/2000000 : ℚ) by norm_num]
  exact coverp010100111110
private noncomputable def ep010100111111_0 : Blocks := edgeBlocks% "full/vectors/010100111111-E-0000.bin"
noncomputable def ep010100111111 : Blocks := ep010100111111_0
private theorem idp010100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010011111.list =
    C ((2:ℤ)^107) * horner X vp010100111111.list + horner X ep010100111111.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100111111 : Branch 1 (-2683761639/4000000 : ℚ) vp01010011111 := by
  apply branch_checked idp010100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2683761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2685761639/2000000 : ℚ) by norm_num]
  exact coverp010100111111
theorem coverp01010011111 : Covers (-2683761639/4000000 : ℚ) vp01010011111 := join_branches bp010100111110 bp010100111111
private noncomputable def vp010100111101_0 : Blocks := edgeBlocks% "full/vectors/010100111101-V-0000.bin"
noncomputable def vp010100111101 : Blocks := vp010100111101_0
theorem coverp010100111101 : Covers (-2681761639/2000000 : ℚ) vp010100111101 := cover_leaf (by decide +kernel)
private noncomputable def vp010100111100_0 : Blocks := edgeBlocks% "full/vectors/010100111100-V-0000.bin"
noncomputable def vp010100111100 : Blocks := vp010100111100_0
theorem coverp010100111100 : Covers (-2679761639/2000000 : ℚ) vp010100111100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010011110_0 : Blocks := edgeBlocks% "full/vectors/01010011110-V-0000.bin"
noncomputable def vp01010011110 : Blocks := vp01010011110_0
private theorem bp010100111100 : Branch 0 (-2679761639/4000000 : ℚ) vp01010011110 := by
  apply branch_left_normalized (c:=vp010100111100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2679761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2679761639/2000000 : ℚ) by norm_num]
  exact coverp010100111100
private noncomputable def ep010100111101_0 : Blocks := edgeBlocks% "full/vectors/010100111101-E-0000.bin"
noncomputable def ep010100111101 : Blocks := ep010100111101_0
private theorem idp010100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010011110.list =
    C ((2:ℤ)^108) * horner X vp010100111101.list + horner X ep010100111101.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100111101 : Branch 1 (-2679761639/4000000 : ℚ) vp01010011110 := by
  apply branch_checked idp010100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2679761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2681761639/2000000 : ℚ) by norm_num]
  exact coverp010100111101
theorem coverp01010011110 : Covers (-2679761639/4000000 : ℚ) vp01010011110 := join_branches bp010100111100 bp010100111101
private noncomputable def vp0101001111_0 : Blocks := edgeBlocks% "full/vectors/0101001111-V-0000.bin"
private noncomputable def vp0101001111_1 : Blocks := edgeBlocks% "full/vectors/0101001111-V-0001.bin"
noncomputable def vp0101001111 : Blocks := (Blocks.join vp0101001111_0 vp0101001111_1)
private theorem bp01010011110 : Branch 0 (-2679761639/8000000 : ℚ) vp0101001111 := by
  apply branch_left_normalized (c:=vp01010011110) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-2679761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2679761639/4000000 : ℚ) by norm_num]
  exact coverp01010011110
private noncomputable def ep01010011111_0 : Blocks := edgeBlocks% "full/vectors/01010011111-E-0000.bin"
private noncomputable def ep01010011111_1 : Blocks := edgeBlocks% "full/vectors/01010011111-E-0001.bin"
noncomputable def ep01010011111 : Blocks := (Blocks.join ep01010011111_0 ep01010011111_1)
private theorem idp01010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101001111.list =
    C ((2:ℤ)^196) * horner X vp01010011111.list + horner X ep01010011111.list := by
  exact edge_identity (B := (2:ℤ)^353) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010011111 : Branch 1 (-2679761639/8000000 : ℚ) vp0101001111 := by
  apply branch_checked idp01010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2679761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2683761639/4000000 : ℚ) by norm_num]
  exact coverp01010011111
theorem coverp0101001111 : Covers (-2679761639/8000000 : ℚ) vp0101001111 := join_branches bp01010011110 bp01010011111
private noncomputable def vp010100111011_0 : Blocks := edgeBlocks% "full/vectors/010100111011-V-0000.bin"
noncomputable def vp010100111011 : Blocks := vp010100111011_0
theorem coverp010100111011 : Covers (-2677761639/2000000 : ℚ) vp010100111011 := cover_leaf (by decide +kernel)
private noncomputable def vp010100111010_0 : Blocks := edgeBlocks% "full/vectors/010100111010-V-0000.bin"
noncomputable def vp010100111010 : Blocks := vp010100111010_0
theorem coverp010100111010 : Covers (-2675761639/2000000 : ℚ) vp010100111010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010011101_0 : Blocks := edgeBlocks% "full/vectors/01010011101-V-0000.bin"
noncomputable def vp01010011101 : Blocks := vp01010011101_0
private theorem bp010100111010 : Branch 0 (-2675761639/4000000 : ℚ) vp01010011101 := by
  apply branch_left_normalized (c:=vp010100111010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2675761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2675761639/2000000 : ℚ) by norm_num]
  exact coverp010100111010
private noncomputable def ep010100111011_0 : Blocks := edgeBlocks% "full/vectors/010100111011-E-0000.bin"
noncomputable def ep010100111011 : Blocks := ep010100111011_0
private theorem idp010100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010011101.list =
    C ((2:ℤ)^111) * horner X vp010100111011.list + horner X ep010100111011.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100111011 : Branch 1 (-2675761639/4000000 : ℚ) vp01010011101 := by
  apply branch_checked idp010100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2675761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2677761639/2000000 : ℚ) by norm_num]
  exact coverp010100111011
theorem coverp01010011101 : Covers (-2675761639/4000000 : ℚ) vp01010011101 := join_branches bp010100111010 bp010100111011
private noncomputable def vp010100111001_0 : Blocks := edgeBlocks% "full/vectors/010100111001-V-0000.bin"
noncomputable def vp010100111001 : Blocks := vp010100111001_0
theorem coverp010100111001 : Covers (-2673761639/2000000 : ℚ) vp010100111001 := cover_leaf (by decide +kernel)
private noncomputable def vp010100111000_0 : Blocks := edgeBlocks% "full/vectors/010100111000-V-0000.bin"
noncomputable def vp010100111000 : Blocks := vp010100111000_0
theorem coverp010100111000 : Covers (-2671761639/2000000 : ℚ) vp010100111000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010011100_0 : Blocks := edgeBlocks% "full/vectors/01010011100-V-0000.bin"
noncomputable def vp01010011100 : Blocks := vp01010011100_0
private theorem bp010100111000 : Branch 0 (-2671761639/4000000 : ℚ) vp01010011100 := by
  apply branch_left_normalized (c:=vp010100111000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2671761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2671761639/2000000 : ℚ) by norm_num]
  exact coverp010100111000
private noncomputable def ep010100111001_0 : Blocks := edgeBlocks% "full/vectors/010100111001-E-0000.bin"
noncomputable def ep010100111001 : Blocks := ep010100111001_0
private theorem idp010100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010011100.list =
    C ((2:ℤ)^105) * horner X vp010100111001.list + horner X ep010100111001.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100111001 : Branch 1 (-2671761639/4000000 : ℚ) vp01010011100 := by
  apply branch_checked idp010100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2671761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2673761639/2000000 : ℚ) by norm_num]
  exact coverp010100111001
theorem coverp01010011100 : Covers (-2671761639/4000000 : ℚ) vp01010011100 := join_branches bp010100111000 bp010100111001
private noncomputable def vp0101001110_0 : Blocks := edgeBlocks% "full/vectors/0101001110-V-0000.bin"
private noncomputable def vp0101001110_1 : Blocks := edgeBlocks% "full/vectors/0101001110-V-0001.bin"
noncomputable def vp0101001110 : Blocks := (Blocks.join vp0101001110_0 vp0101001110_1)
private theorem bp01010011100 : Branch 0 (-2671761639/8000000 : ℚ) vp0101001110 := by
  apply branch_left_normalized (c:=vp01010011100) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-2671761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2671761639/4000000 : ℚ) by norm_num]
  exact coverp01010011100
private noncomputable def ep01010011101_0 : Blocks := edgeBlocks% "full/vectors/01010011101-E-0000.bin"
private noncomputable def ep01010011101_1 : Blocks := edgeBlocks% "full/vectors/01010011101-E-0001.bin"
noncomputable def ep01010011101 : Blocks := (Blocks.join ep01010011101_0 ep01010011101_1)
private theorem idp01010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101001110.list =
    C ((2:ℤ)^194) * horner X vp01010011101.list + horner X ep01010011101.list := by
  exact edge_identity (B := (2:ℤ)^352) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010011101 : Branch 1 (-2671761639/8000000 : ℚ) vp0101001110 := by
  apply branch_checked idp01010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2671761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2675761639/4000000 : ℚ) by norm_num]
  exact coverp01010011101
theorem coverp0101001110 : Covers (-2671761639/8000000 : ℚ) vp0101001110 := join_branches bp01010011100 bp01010011101
private noncomputable def vp010100111_0 : Blocks := edgeBlocks% "full/vectors/010100111-V-0000.bin"
private noncomputable def vp010100111_1 : Blocks := edgeBlocks% "full/vectors/010100111-V-0001.bin"
private noncomputable def vp010100111_2 : Blocks := edgeBlocks% "full/vectors/010100111-V-0002.bin"
noncomputable def vp010100111 : Blocks := (Blocks.join vp010100111_0 (Blocks.join vp010100111_1 vp010100111_2))
private theorem bp0101001110 : Branch 0 (-2671761639/16000000 : ℚ) vp010100111 := by
  apply branch_left_normalized (c:=vp0101001110) (k:=0) (m:=172) (by decide +kernel)
  rw [show 2*(-2671761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2671761639/8000000 : ℚ) by norm_num]
  exact coverp0101001110
private noncomputable def ep0101001111_0 : Blocks := edgeBlocks% "full/vectors/0101001111-E-0000.bin"
private noncomputable def ep0101001111_1 : Blocks := edgeBlocks% "full/vectors/0101001111-E-0001.bin"
private noncomputable def ep0101001111_2 : Blocks := edgeBlocks% "full/vectors/0101001111-E-0002.bin"
noncomputable def ep0101001111 : Blocks := (Blocks.join ep0101001111_0 (Blocks.join ep0101001111_1 ep0101001111_2))
private theorem idp0101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010100111.list =
    C ((2:ℤ)^370) * horner X vp0101001111.list + horner X ep0101001111.list := by
  exact edge_identity (B := (2:ℤ)^584) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101001111 : Branch 1 (-2671761639/16000000 : ℚ) vp010100111 := by
  apply branch_checked idp0101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2671761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2679761639/8000000 : ℚ) by norm_num]
  exact coverp0101001111
theorem coverp010100111 : Covers (-2671761639/16000000 : ℚ) vp010100111 := join_branches bp0101001110 bp0101001111
private noncomputable def vp010100110111_0 : Blocks := edgeBlocks% "full/vectors/010100110111-V-0000.bin"
noncomputable def vp010100110111 : Blocks := vp010100110111_0
theorem coverp010100110111 : Covers (-2669761639/2000000 : ℚ) vp010100110111 := cover_leaf (by decide +kernel)
private noncomputable def vp010100110110_0 : Blocks := edgeBlocks% "full/vectors/010100110110-V-0000.bin"
noncomputable def vp010100110110 : Blocks := vp010100110110_0
theorem coverp010100110110 : Covers (-2667761639/2000000 : ℚ) vp010100110110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010011011_0 : Blocks := edgeBlocks% "full/vectors/01010011011-V-0000.bin"
noncomputable def vp01010011011 : Blocks := vp01010011011_0
private theorem bp010100110110 : Branch 0 (-2667761639/4000000 : ℚ) vp01010011011 := by
  apply branch_left_normalized (c:=vp010100110110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-2667761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2667761639/2000000 : ℚ) by norm_num]
  exact coverp010100110110
private noncomputable def ep010100110111_0 : Blocks := edgeBlocks% "full/vectors/010100110111-E-0000.bin"
noncomputable def ep010100110111 : Blocks := ep010100110111_0
private theorem idp010100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010011011.list =
    C ((2:ℤ)^104) * horner X vp010100110111.list + horner X ep010100110111.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100110111 : Branch 1 (-2667761639/4000000 : ℚ) vp01010011011 := by
  apply branch_checked idp010100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2667761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2669761639/2000000 : ℚ) by norm_num]
  exact coverp010100110111
theorem coverp01010011011 : Covers (-2667761639/4000000 : ℚ) vp01010011011 := join_branches bp010100110110 bp010100110111
private noncomputable def vp01010011010_0 : Blocks := edgeBlocks% "full/vectors/01010011010-V-0000.bin"
noncomputable def vp01010011010 : Blocks := vp01010011010_0
theorem coverp01010011010 : Covers (-2663761639/4000000 : ℚ) vp01010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0101001101_0 : Blocks := edgeBlocks% "full/vectors/0101001101-V-0000.bin"
private noncomputable def vp0101001101_1 : Blocks := edgeBlocks% "full/vectors/0101001101-V-0001.bin"
noncomputable def vp0101001101 : Blocks := (Blocks.join vp0101001101_0 vp0101001101_1)
private theorem bp01010011010 : Branch 0 (-2663761639/8000000 : ℚ) vp0101001101 := by
  apply branch_left_normalized (c:=vp01010011010) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-2663761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2663761639/4000000 : ℚ) by norm_num]
  exact coverp01010011010
private noncomputable def ep01010011011_0 : Blocks := edgeBlocks% "full/vectors/01010011011-E-0000.bin"
private noncomputable def ep01010011011_1 : Blocks := edgeBlocks% "full/vectors/01010011011-E-0001.bin"
noncomputable def ep01010011011 : Blocks := (Blocks.join ep01010011011_0 ep01010011011_1)
private theorem idp01010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101001101.list =
    C ((2:ℤ)^192) * horner X vp01010011011.list + horner X ep01010011011.list := by
  exact edge_identity (B := (2:ℤ)^344) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010011011 : Branch 1 (-2663761639/8000000 : ℚ) vp0101001101 := by
  apply branch_checked idp01010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2663761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2667761639/4000000 : ℚ) by norm_num]
  exact coverp01010011011
theorem coverp0101001101 : Covers (-2663761639/8000000 : ℚ) vp0101001101 := join_branches bp01010011010 bp01010011011
private noncomputable def vp01010011001_0 : Blocks := edgeBlocks% "full/vectors/01010011001-V-0000.bin"
noncomputable def vp01010011001 : Blocks := vp01010011001_0
theorem coverp01010011001 : Covers (-2659761639/4000000 : ℚ) vp01010011001 := cover_leaf (by decide +kernel)
private noncomputable def vp01010011000_0 : Blocks := edgeBlocks% "full/vectors/01010011000-V-0000.bin"
noncomputable def vp01010011000 : Blocks := vp01010011000_0
theorem coverp01010011000 : Covers (-2655761639/4000000 : ℚ) vp01010011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0101001100_0 : Blocks := edgeBlocks% "full/vectors/0101001100-V-0000.bin"
private noncomputable def vp0101001100_1 : Blocks := edgeBlocks% "full/vectors/0101001100-V-0001.bin"
noncomputable def vp0101001100 : Blocks := (Blocks.join vp0101001100_0 vp0101001100_1)
private theorem bp01010011000 : Branch 0 (-2655761639/8000000 : ℚ) vp0101001100 := by
  apply branch_left_normalized (c:=vp01010011000) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-2655761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2655761639/4000000 : ℚ) by norm_num]
  exact coverp01010011000
private noncomputable def ep01010011001_0 : Blocks := edgeBlocks% "full/vectors/01010011001-E-0000.bin"
private noncomputable def ep01010011001_1 : Blocks := edgeBlocks% "full/vectors/01010011001-E-0001.bin"
noncomputable def ep01010011001 : Blocks := (Blocks.join ep01010011001_0 ep01010011001_1)
private theorem idp01010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101001100.list =
    C ((2:ℤ)^191) * horner X vp01010011001.list + horner X ep01010011001.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010011001 : Branch 1 (-2655761639/8000000 : ℚ) vp0101001100 := by
  apply branch_checked idp01010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2655761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2659761639/4000000 : ℚ) by norm_num]
  exact coverp01010011001
theorem coverp0101001100 : Covers (-2655761639/8000000 : ℚ) vp0101001100 := join_branches bp01010011000 bp01010011001
private noncomputable def vp010100110_0 : Blocks := edgeBlocks% "full/vectors/010100110-V-0000.bin"
private noncomputable def vp010100110_1 : Blocks := edgeBlocks% "full/vectors/010100110-V-0001.bin"
private noncomputable def vp010100110_2 : Blocks := edgeBlocks% "full/vectors/010100110-V-0002.bin"
noncomputable def vp010100110 : Blocks := (Blocks.join vp010100110_0 (Blocks.join vp010100110_1 vp010100110_2))
private theorem bp0101001100 : Branch 0 (-2655761639/16000000 : ℚ) vp010100110 := by
  apply branch_left_normalized (c:=vp0101001100) (k:=0) (m:=168) (by decide +kernel)
  rw [show 2*(-2655761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2655761639/8000000 : ℚ) by norm_num]
  exact coverp0101001100
private noncomputable def ep0101001101_0 : Blocks := edgeBlocks% "full/vectors/0101001101-E-0000.bin"
private noncomputable def ep0101001101_1 : Blocks := edgeBlocks% "full/vectors/0101001101-E-0001.bin"
private noncomputable def ep0101001101_2 : Blocks := edgeBlocks% "full/vectors/0101001101-E-0002.bin"
noncomputable def ep0101001101 : Blocks := (Blocks.join ep0101001101_0 (Blocks.join ep0101001101_1 ep0101001101_2))
private theorem idp0101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010100110.list =
    C ((2:ℤ)^365) * horner X vp0101001101.list + horner X ep0101001101.list := by
  exact edge_identity (B := (2:ℤ)^574) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101001101 : Branch 1 (-2655761639/16000000 : ℚ) vp010100110 := by
  apply branch_checked idp0101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2655761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2663761639/8000000 : ℚ) by norm_num]
  exact coverp0101001101
theorem coverp010100110 : Covers (-2655761639/16000000 : ℚ) vp010100110 := join_branches bp0101001100 bp0101001101
private noncomputable def vp01010011_0 : Blocks := edgeBlocks% "full/vectors/01010011-V-0000.bin"
private noncomputable def vp01010011_1 : Blocks := edgeBlocks% "full/vectors/01010011-V-0001.bin"
private noncomputable def vp01010011_2 : Blocks := edgeBlocks% "full/vectors/01010011-V-0002.bin"
private noncomputable def vp01010011_3 : Blocks := edgeBlocks% "full/vectors/01010011-V-0003.bin"
private noncomputable def vp01010011_4 : Blocks := edgeBlocks% "full/vectors/01010011-V-0004.bin"
noncomputable def vp01010011 : Blocks := (Blocks.join (Blocks.join vp01010011_0 vp01010011_1) (Blocks.join vp01010011_2 (Blocks.join vp01010011_3 vp01010011_4)))
private theorem bp010100110 : Branch 0 (-2655761639/32000000 : ℚ) vp01010011 := by
  apply branch_left_normalized (c:=vp010100110) (k:=0) (m:=320) (by decide +kernel)
  rw [show 2*(-2655761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2655761639/16000000 : ℚ) by norm_num]
  exact coverp010100110
private noncomputable def ep010100111_0 : Blocks := edgeBlocks% "full/vectors/010100111-E-0000.bin"
private noncomputable def ep010100111_1 : Blocks := edgeBlocks% "full/vectors/010100111-E-0001.bin"
private noncomputable def ep010100111_2 : Blocks := edgeBlocks% "full/vectors/010100111-E-0002.bin"
private noncomputable def ep010100111_3 : Blocks := edgeBlocks% "full/vectors/010100111-E-0003.bin"
private noncomputable def ep010100111_4 : Blocks := edgeBlocks% "full/vectors/010100111-E-0004.bin"
noncomputable def ep010100111 : Blocks := (Blocks.join (Blocks.join ep010100111_0 ep010100111_1) (Blocks.join ep010100111_2 (Blocks.join ep010100111_3 ep010100111_4)))
private theorem idp010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010011.list =
    C ((2:ℤ)^707) * horner X vp010100111.list + horner X ep010100111.list := by
  exact edge_identity (B := (2:ℤ)^1036) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100111 : Branch 1 (-2655761639/32000000 : ℚ) vp01010011 := by
  apply branch_checked idp010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2655761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2671761639/16000000 : ℚ) by norm_num]
  exact coverp010100111
theorem coverp01010011 : Covers (-2655761639/32000000 : ℚ) vp01010011 := join_branches bp010100110 bp010100111
private noncomputable def vp01010010111_0 : Blocks := edgeBlocks% "full/vectors/01010010111-V-0000.bin"
noncomputable def vp01010010111 : Blocks := vp01010010111_0
theorem coverp01010010111 : Covers (-2651761639/4000000 : ℚ) vp01010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp01010010110_0 : Blocks := edgeBlocks% "full/vectors/01010010110-V-0000.bin"
noncomputable def vp01010010110 : Blocks := vp01010010110_0
theorem coverp01010010110 : Covers (-2647761639/4000000 : ℚ) vp01010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0101001011_0 : Blocks := edgeBlocks% "full/vectors/0101001011-V-0000.bin"
private noncomputable def vp0101001011_1 : Blocks := edgeBlocks% "full/vectors/0101001011-V-0001.bin"
noncomputable def vp0101001011 : Blocks := (Blocks.join vp0101001011_0 vp0101001011_1)
private theorem bp01010010110 : Branch 0 (-2647761639/8000000 : ℚ) vp0101001011 := by
  apply branch_left_normalized (c:=vp01010010110) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-2647761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2647761639/4000000 : ℚ) by norm_num]
  exact coverp01010010110
private noncomputable def ep01010010111_0 : Blocks := edgeBlocks% "full/vectors/01010010111-E-0000.bin"
private noncomputable def ep01010010111_1 : Blocks := edgeBlocks% "full/vectors/01010010111-E-0001.bin"
noncomputable def ep01010010111 : Blocks := (Blocks.join ep01010010111_0 ep01010010111_1)
private theorem idp01010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101001011.list =
    C ((2:ℤ)^193) * horner X vp01010010111.list + horner X ep01010010111.list := by
  exact edge_identity (B := (2:ℤ)^342) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010010111 : Branch 1 (-2647761639/8000000 : ℚ) vp0101001011 := by
  apply branch_checked idp01010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2647761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2651761639/4000000 : ℚ) by norm_num]
  exact coverp01010010111
theorem coverp0101001011 : Covers (-2647761639/8000000 : ℚ) vp0101001011 := join_branches bp01010010110 bp01010010111
private noncomputable def vp01010010101_0 : Blocks := edgeBlocks% "full/vectors/01010010101-V-0000.bin"
noncomputable def vp01010010101 : Blocks := vp01010010101_0
theorem coverp01010010101 : Covers (-2643761639/4000000 : ℚ) vp01010010101 := cover_leaf (by decide +kernel)
private noncomputable def vp01010010100_0 : Blocks := edgeBlocks% "full/vectors/01010010100-V-0000.bin"
noncomputable def vp01010010100 : Blocks := vp01010010100_0
theorem coverp01010010100 : Covers (-2639761639/4000000 : ℚ) vp01010010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0101001010_0 : Blocks := edgeBlocks% "full/vectors/0101001010-V-0000.bin"
private noncomputable def vp0101001010_1 : Blocks := edgeBlocks% "full/vectors/0101001010-V-0001.bin"
noncomputable def vp0101001010 : Blocks := (Blocks.join vp0101001010_0 vp0101001010_1)
private theorem bp01010010100 : Branch 0 (-2639761639/8000000 : ℚ) vp0101001010 := by
  apply branch_left_normalized (c:=vp01010010100) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-2639761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2639761639/4000000 : ℚ) by norm_num]
  exact coverp01010010100
private noncomputable def ep01010010101_0 : Blocks := edgeBlocks% "full/vectors/01010010101-E-0000.bin"
private noncomputable def ep01010010101_1 : Blocks := edgeBlocks% "full/vectors/01010010101-E-0001.bin"
noncomputable def ep01010010101 : Blocks := (Blocks.join ep01010010101_0 ep01010010101_1)
private theorem idp01010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101001010.list =
    C ((2:ℤ)^194) * horner X vp01010010101.list + horner X ep01010010101.list := by
  exact edge_identity (B := (2:ℤ)^343) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010010101 : Branch 1 (-2639761639/8000000 : ℚ) vp0101001010 := by
  apply branch_checked idp01010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2639761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2643761639/4000000 : ℚ) by norm_num]
  exact coverp01010010101
theorem coverp0101001010 : Covers (-2639761639/8000000 : ℚ) vp0101001010 := join_branches bp01010010100 bp01010010101
private noncomputable def vp010100101_0 : Blocks := edgeBlocks% "full/vectors/010100101-V-0000.bin"
private noncomputable def vp010100101_1 : Blocks := edgeBlocks% "full/vectors/010100101-V-0001.bin"
private noncomputable def vp010100101_2 : Blocks := edgeBlocks% "full/vectors/010100101-V-0002.bin"
noncomputable def vp010100101 : Blocks := (Blocks.join vp010100101_0 (Blocks.join vp010100101_1 vp010100101_2))
private theorem bp0101001010 : Branch 0 (-2639761639/16000000 : ℚ) vp010100101 := by
  apply branch_left_normalized (c:=vp0101001010) (k:=0) (m:=169) (by decide +kernel)
  rw [show 2*(-2639761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2639761639/8000000 : ℚ) by norm_num]
  exact coverp0101001010
private noncomputable def ep0101001011_0 : Blocks := edgeBlocks% "full/vectors/0101001011-E-0000.bin"
private noncomputable def ep0101001011_1 : Blocks := edgeBlocks% "full/vectors/0101001011-E-0001.bin"
private noncomputable def ep0101001011_2 : Blocks := edgeBlocks% "full/vectors/0101001011-E-0002.bin"
noncomputable def ep0101001011 : Blocks := (Blocks.join ep0101001011_0 (Blocks.join ep0101001011_1 ep0101001011_2))
private theorem idp0101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010100101.list =
    C ((2:ℤ)^369) * horner X vp0101001011.list + horner X ep0101001011.list := by
  exact edge_identity (B := (2:ℤ)^576) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101001011 : Branch 1 (-2639761639/16000000 : ℚ) vp010100101 := by
  apply branch_checked idp0101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2639761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2647761639/8000000 : ℚ) by norm_num]
  exact coverp0101001011
theorem coverp010100101 : Covers (-2639761639/16000000 : ℚ) vp010100101 := join_branches bp0101001010 bp0101001011
private noncomputable def vp01010010011_0 : Blocks := edgeBlocks% "full/vectors/01010010011-V-0000.bin"
noncomputable def vp01010010011 : Blocks := vp01010010011_0
theorem coverp01010010011 : Covers (-2635761639/4000000 : ℚ) vp01010010011 := cover_leaf (by decide +kernel)
private noncomputable def vp01010010010_0 : Blocks := edgeBlocks% "full/vectors/01010010010-V-0000.bin"
noncomputable def vp01010010010 : Blocks := vp01010010010_0
theorem coverp01010010010 : Covers (-2631761639/4000000 : ℚ) vp01010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0101001001_0 : Blocks := edgeBlocks% "full/vectors/0101001001-V-0000.bin"
private noncomputable def vp0101001001_1 : Blocks := edgeBlocks% "full/vectors/0101001001-V-0001.bin"
noncomputable def vp0101001001 : Blocks := (Blocks.join vp0101001001_0 vp0101001001_1)
private theorem bp01010010010 : Branch 0 (-2631761639/8000000 : ℚ) vp0101001001 := by
  apply branch_left_normalized (c:=vp01010010010) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-2631761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2631761639/4000000 : ℚ) by norm_num]
  exact coverp01010010010
private noncomputable def ep01010010011_0 : Blocks := edgeBlocks% "full/vectors/01010010011-E-0000.bin"
private noncomputable def ep01010010011_1 : Blocks := edgeBlocks% "full/vectors/01010010011-E-0001.bin"
noncomputable def ep01010010011 : Blocks := (Blocks.join ep01010010011_0 ep01010010011_1)
private theorem idp01010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101001001.list =
    C ((2:ℤ)^197) * horner X vp01010010011.list + horner X ep01010010011.list := by
  exact edge_identity (B := (2:ℤ)^348) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010010011 : Branch 1 (-2631761639/8000000 : ℚ) vp0101001001 := by
  apply branch_checked idp01010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2631761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2635761639/4000000 : ℚ) by norm_num]
  exact coverp01010010011
theorem coverp0101001001 : Covers (-2631761639/8000000 : ℚ) vp0101001001 := join_branches bp01010010010 bp01010010011
private noncomputable def vp01010010001_0 : Blocks := edgeBlocks% "full/vectors/01010010001-V-0000.bin"
noncomputable def vp01010010001 : Blocks := vp01010010001_0
theorem coverp01010010001 : Covers (-2627761639/4000000 : ℚ) vp01010010001 := cover_leaf (by decide +kernel)
private noncomputable def vp010100100001_0 : Blocks := edgeBlocks% "full/vectors/010100100001-V-0000.bin"
noncomputable def vp010100100001 : Blocks := vp010100100001_0
theorem coverp010100100001 : Covers (-2625761639/2000000 : ℚ) vp010100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp010100100000_0 : Blocks := edgeBlocks% "full/vectors/010100100000-V-0000.bin"
noncomputable def vp010100100000 : Blocks := vp010100100000_0
theorem coverp010100100000 : Covers (-2623761639/2000000 : ℚ) vp010100100000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010010000_0 : Blocks := edgeBlocks% "full/vectors/01010010000-V-0000.bin"
noncomputable def vp01010010000 : Blocks := vp01010010000_0
private theorem bp010100100000 : Branch 0 (-2623761639/4000000 : ℚ) vp01010010000 := by
  apply branch_left_normalized (c:=vp010100100000) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2623761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2623761639/2000000 : ℚ) by norm_num]
  exact coverp010100100000
private noncomputable def ep010100100001_0 : Blocks := edgeBlocks% "full/vectors/010100100001-E-0000.bin"
noncomputable def ep010100100001 : Blocks := ep010100100001_0
private theorem idp010100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010010000.list =
    C ((2:ℤ)^113) * horner X vp010100100001.list + horner X ep010100100001.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100100001 : Branch 1 (-2623761639/4000000 : ℚ) vp01010010000 := by
  apply branch_checked idp010100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2623761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2625761639/2000000 : ℚ) by norm_num]
  exact coverp010100100001
theorem coverp01010010000 : Covers (-2623761639/4000000 : ℚ) vp01010010000 := join_branches bp010100100000 bp010100100001
private noncomputable def vp0101001000_0 : Blocks := edgeBlocks% "full/vectors/0101001000-V-0000.bin"
private noncomputable def vp0101001000_1 : Blocks := edgeBlocks% "full/vectors/0101001000-V-0001.bin"
noncomputable def vp0101001000 : Blocks := (Blocks.join vp0101001000_0 vp0101001000_1)
private theorem bp01010010000 : Branch 0 (-2623761639/8000000 : ℚ) vp0101001000 := by
  apply branch_left_normalized (c:=vp01010010000) (k:=0) (m:=98) (by decide +kernel)
  rw [show 2*(-2623761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2623761639/4000000 : ℚ) by norm_num]
  exact coverp01010010000
private noncomputable def ep01010010001_0 : Blocks := edgeBlocks% "full/vectors/01010010001-E-0000.bin"
private noncomputable def ep01010010001_1 : Blocks := edgeBlocks% "full/vectors/01010010001-E-0001.bin"
noncomputable def ep01010010001 : Blocks := (Blocks.join ep01010010001_0 ep01010010001_1)
private theorem idp01010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101001000.list =
    C ((2:ℤ)^203) * horner X vp01010010001.list + horner X ep01010010001.list := by
  exact edge_identity (B := (2:ℤ)^359) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010010001 : Branch 1 (-2623761639/8000000 : ℚ) vp0101001000 := by
  apply branch_checked idp01010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2623761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2627761639/4000000 : ℚ) by norm_num]
  exact coverp01010010001
theorem coverp0101001000 : Covers (-2623761639/8000000 : ℚ) vp0101001000 := join_branches bp01010010000 bp01010010001
private noncomputable def vp010100100_0 : Blocks := edgeBlocks% "full/vectors/010100100-V-0000.bin"
private noncomputable def vp010100100_1 : Blocks := edgeBlocks% "full/vectors/010100100-V-0001.bin"
private noncomputable def vp010100100_2 : Blocks := edgeBlocks% "full/vectors/010100100-V-0002.bin"
noncomputable def vp010100100 : Blocks := (Blocks.join vp010100100_0 (Blocks.join vp010100100_1 vp010100100_2))
private theorem bp0101001000 : Branch 0 (-2623761639/16000000 : ℚ) vp010100100 := by
  apply branch_left_normalized (c:=vp0101001000) (k:=0) (m:=175) (by decide +kernel)
  rw [show 2*(-2623761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2623761639/8000000 : ℚ) by norm_num]
  exact coverp0101001000
private noncomputable def ep0101001001_0 : Blocks := edgeBlocks% "full/vectors/0101001001-E-0000.bin"
private noncomputable def ep0101001001_1 : Blocks := edgeBlocks% "full/vectors/0101001001-E-0001.bin"
private noncomputable def ep0101001001_2 : Blocks := edgeBlocks% "full/vectors/0101001001-E-0002.bin"
noncomputable def ep0101001001 : Blocks := (Blocks.join ep0101001001_0 (Blocks.join ep0101001001_1 ep0101001001_2))
private theorem idp0101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010100100.list =
    C ((2:ℤ)^382) * horner X vp0101001001.list + horner X ep0101001001.list := by
  exact edge_identity (B := (2:ℤ)^593) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101001001 : Branch 1 (-2623761639/16000000 : ℚ) vp010100100 := by
  apply branch_checked idp0101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2623761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2631761639/8000000 : ℚ) by norm_num]
  exact coverp0101001001
theorem coverp010100100 : Covers (-2623761639/16000000 : ℚ) vp010100100 := join_branches bp0101001000 bp0101001001
private noncomputable def vp01010010_0 : Blocks := edgeBlocks% "full/vectors/01010010-V-0000.bin"
private noncomputable def vp01010010_1 : Blocks := edgeBlocks% "full/vectors/01010010-V-0001.bin"
private noncomputable def vp01010010_2 : Blocks := edgeBlocks% "full/vectors/01010010-V-0002.bin"
private noncomputable def vp01010010_3 : Blocks := edgeBlocks% "full/vectors/01010010-V-0003.bin"
private noncomputable def vp01010010_4 : Blocks := edgeBlocks% "full/vectors/01010010-V-0004.bin"
noncomputable def vp01010010 : Blocks := (Blocks.join (Blocks.join vp01010010_0 vp01010010_1) (Blocks.join vp01010010_2 (Blocks.join vp01010010_3 vp01010010_4)))
private theorem bp010100100 : Branch 0 (-2623761639/32000000 : ℚ) vp01010010 := by
  apply branch_left_normalized (c:=vp010100100) (k:=0) (m:=328) (by decide +kernel)
  rw [show 2*(-2623761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2623761639/16000000 : ℚ) by norm_num]
  exact coverp010100100
private noncomputable def ep010100101_0 : Blocks := edgeBlocks% "full/vectors/010100101-E-0000.bin"
private noncomputable def ep010100101_1 : Blocks := edgeBlocks% "full/vectors/010100101-E-0001.bin"
private noncomputable def ep010100101_2 : Blocks := edgeBlocks% "full/vectors/010100101-E-0002.bin"
private noncomputable def ep010100101_3 : Blocks := edgeBlocks% "full/vectors/010100101-E-0003.bin"
private noncomputable def ep010100101_4 : Blocks := edgeBlocks% "full/vectors/010100101-E-0004.bin"
noncomputable def ep010100101 : Blocks := (Blocks.join (Blocks.join ep010100101_0 ep010100101_1) (Blocks.join ep010100101_2 (Blocks.join ep010100101_3 ep010100101_4)))
private theorem idp010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010010.list =
    C ((2:ℤ)^734) * horner X vp010100101.list + horner X ep010100101.list := by
  exact edge_identity (B := (2:ℤ)^1059) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100101 : Branch 1 (-2623761639/32000000 : ℚ) vp01010010 := by
  apply branch_checked idp010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2623761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2639761639/16000000 : ℚ) by norm_num]
  exact coverp010100101
theorem coverp01010010 : Covers (-2623761639/32000000 : ℚ) vp01010010 := join_branches bp010100100 bp010100101
private noncomputable def vp0101001_0 : Blocks := edgeBlocks% "full/vectors/0101001-V-0000.bin"
private noncomputable def vp0101001_1 : Blocks := edgeBlocks% "full/vectors/0101001-V-0001.bin"
private noncomputable def vp0101001_2 : Blocks := edgeBlocks% "full/vectors/0101001-V-0002.bin"
private noncomputable def vp0101001_3 : Blocks := edgeBlocks% "full/vectors/0101001-V-0003.bin"
private noncomputable def vp0101001_4 : Blocks := edgeBlocks% "full/vectors/0101001-V-0004.bin"
private noncomputable def vp0101001_5 : Blocks := edgeBlocks% "full/vectors/0101001-V-0005.bin"
private noncomputable def vp0101001_6 : Blocks := edgeBlocks% "full/vectors/0101001-V-0006.bin"
private noncomputable def vp0101001_7 : Blocks := edgeBlocks% "full/vectors/0101001-V-0007.bin"
private noncomputable def vp0101001_8 : Blocks := edgeBlocks% "full/vectors/0101001-V-0008.bin"
private noncomputable def vp0101001_9 : Blocks := edgeBlocks% "full/vectors/0101001-V-0009.bin"
noncomputable def vp0101001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0101001_0 vp0101001_1) (Blocks.join vp0101001_2 (Blocks.join vp0101001_3 vp0101001_4))) (Blocks.join (Blocks.join vp0101001_5 vp0101001_6) (Blocks.join vp0101001_7 (Blocks.join vp0101001_8 vp0101001_9))))
private theorem bp01010010 : Branch 0 (-2623761639/64000000 : ℚ) vp0101001 := by
  apply branch_left_normalized (c:=vp01010010) (k:=0) (m:=631) (by decide +kernel)
  rw [show 2*(-2623761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2623761639/32000000 : ℚ) by norm_num]
  exact coverp01010010
private noncomputable def ep01010011_0 : Blocks := edgeBlocks% "full/vectors/01010011-E-0000.bin"
private noncomputable def ep01010011_1 : Blocks := edgeBlocks% "full/vectors/01010011-E-0001.bin"
private noncomputable def ep01010011_2 : Blocks := edgeBlocks% "full/vectors/01010011-E-0002.bin"
private noncomputable def ep01010011_3 : Blocks := edgeBlocks% "full/vectors/01010011-E-0003.bin"
private noncomputable def ep01010011_4 : Blocks := edgeBlocks% "full/vectors/01010011-E-0004.bin"
private noncomputable def ep01010011_5 : Blocks := edgeBlocks% "full/vectors/01010011-E-0005.bin"
private noncomputable def ep01010011_6 : Blocks := edgeBlocks% "full/vectors/01010011-E-0006.bin"
private noncomputable def ep01010011_7 : Blocks := edgeBlocks% "full/vectors/01010011-E-0007.bin"
private noncomputable def ep01010011_8 : Blocks := edgeBlocks% "full/vectors/01010011-E-0008.bin"
private noncomputable def ep01010011_9 : Blocks := edgeBlocks% "full/vectors/01010011-E-0009.bin"
noncomputable def ep01010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01010011_0 ep01010011_1) (Blocks.join ep01010011_2 (Blocks.join ep01010011_3 ep01010011_4))) (Blocks.join (Blocks.join ep01010011_5 ep01010011_6) (Blocks.join ep01010011_7 (Blocks.join ep01010011_8 ep01010011_9))))
private theorem idp01010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101001.list =
    C ((2:ℤ)^1424) * horner X vp01010011.list + horner X ep01010011.list := by
  exact edge_identity (B := (2:ℤ)^1979) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010011 : Branch 1 (-2623761639/64000000 : ℚ) vp0101001 := by
  apply branch_checked idp01010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2623761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2655761639/32000000 : ℚ) by norm_num]
  exact coverp01010011
theorem coverp0101001 : Covers (-2623761639/64000000 : ℚ) vp0101001 := join_branches bp01010010 bp01010011
private noncomputable def vp010100011111_0 : Blocks := edgeBlocks% "full/vectors/010100011111-V-0000.bin"
noncomputable def vp010100011111 : Blocks := vp010100011111_0
theorem coverp010100011111 : Covers (-2621761639/2000000 : ℚ) vp010100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp010100011110_0 : Blocks := edgeBlocks% "full/vectors/010100011110-V-0000.bin"
noncomputable def vp010100011110 : Blocks := vp010100011110_0
theorem coverp010100011110 : Covers (-2619761639/2000000 : ℚ) vp010100011110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010001111_0 : Blocks := edgeBlocks% "full/vectors/01010001111-V-0000.bin"
noncomputable def vp01010001111 : Blocks := vp01010001111_0
private theorem bp010100011110 : Branch 0 (-2619761639/4000000 : ℚ) vp01010001111 := by
  apply branch_left_normalized (c:=vp010100011110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2619761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2619761639/2000000 : ℚ) by norm_num]
  exact coverp010100011110
private noncomputable def ep010100011111_0 : Blocks := edgeBlocks% "full/vectors/010100011111-E-0000.bin"
noncomputable def ep010100011111 : Blocks := ep010100011111_0
private theorem idp010100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010001111.list =
    C ((2:ℤ)^109) * horner X vp010100011111.list + horner X ep010100011111.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100011111 : Branch 1 (-2619761639/4000000 : ℚ) vp01010001111 := by
  apply branch_checked idp010100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2619761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2621761639/2000000 : ℚ) by norm_num]
  exact coverp010100011111
theorem coverp01010001111 : Covers (-2619761639/4000000 : ℚ) vp01010001111 := join_branches bp010100011110 bp010100011111
private noncomputable def vp010100011101_0 : Blocks := edgeBlocks% "full/vectors/010100011101-V-0000.bin"
noncomputable def vp010100011101 : Blocks := vp010100011101_0
theorem coverp010100011101 : Covers (-2617761639/2000000 : ℚ) vp010100011101 := cover_leaf (by decide +kernel)
private noncomputable def vp010100011100_0 : Blocks := edgeBlocks% "full/vectors/010100011100-V-0000.bin"
noncomputable def vp010100011100 : Blocks := vp010100011100_0
theorem coverp010100011100 : Covers (-2615761639/2000000 : ℚ) vp010100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010001110_0 : Blocks := edgeBlocks% "full/vectors/01010001110-V-0000.bin"
noncomputable def vp01010001110 : Blocks := vp01010001110_0
private theorem bp010100011100 : Branch 0 (-2615761639/4000000 : ℚ) vp01010001110 := by
  apply branch_left_normalized (c:=vp010100011100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2615761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2615761639/2000000 : ℚ) by norm_num]
  exact coverp010100011100
private noncomputable def ep010100011101_0 : Blocks := edgeBlocks% "full/vectors/010100011101-E-0000.bin"
noncomputable def ep010100011101 : Blocks := ep010100011101_0
private theorem idp010100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010001110.list =
    C ((2:ℤ)^110) * horner X vp010100011101.list + horner X ep010100011101.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100011101 : Branch 1 (-2615761639/4000000 : ℚ) vp01010001110 := by
  apply branch_checked idp010100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2615761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2617761639/2000000 : ℚ) by norm_num]
  exact coverp010100011101
theorem coverp01010001110 : Covers (-2615761639/4000000 : ℚ) vp01010001110 := join_branches bp010100011100 bp010100011101
private noncomputable def vp0101000111_0 : Blocks := edgeBlocks% "full/vectors/0101000111-V-0000.bin"
private noncomputable def vp0101000111_1 : Blocks := edgeBlocks% "full/vectors/0101000111-V-0001.bin"
noncomputable def vp0101000111 : Blocks := (Blocks.join vp0101000111_0 vp0101000111_1)
private theorem bp01010001110 : Branch 0 (-2615761639/8000000 : ℚ) vp0101000111 := by
  apply branch_left_normalized (c:=vp01010001110) (k:=0) (m:=97) (by decide +kernel)
  rw [show 2*(-2615761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2615761639/4000000 : ℚ) by norm_num]
  exact coverp01010001110
private noncomputable def ep01010001111_0 : Blocks := edgeBlocks% "full/vectors/01010001111-E-0000.bin"
private noncomputable def ep01010001111_1 : Blocks := edgeBlocks% "full/vectors/01010001111-E-0001.bin"
noncomputable def ep01010001111 : Blocks := (Blocks.join ep01010001111_0 ep01010001111_1)
private theorem idp01010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101000111.list =
    C ((2:ℤ)^199) * horner X vp01010001111.list + horner X ep01010001111.list := by
  exact edge_identity (B := (2:ℤ)^357) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010001111 : Branch 1 (-2615761639/8000000 : ℚ) vp0101000111 := by
  apply branch_checked idp01010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2615761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2619761639/4000000 : ℚ) by norm_num]
  exact coverp01010001111
theorem coverp0101000111 : Covers (-2615761639/8000000 : ℚ) vp0101000111 := join_branches bp01010001110 bp01010001111
private noncomputable def vp010100011011_0 : Blocks := edgeBlocks% "full/vectors/010100011011-V-0000.bin"
noncomputable def vp010100011011 : Blocks := vp010100011011_0
theorem coverp010100011011 : Covers (-2613761639/2000000 : ℚ) vp010100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp010100011010_0 : Blocks := edgeBlocks% "full/vectors/010100011010-V-0000.bin"
noncomputable def vp010100011010 : Blocks := vp010100011010_0
theorem coverp010100011010 : Covers (-2611761639/2000000 : ℚ) vp010100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010001101_0 : Blocks := edgeBlocks% "full/vectors/01010001101-V-0000.bin"
noncomputable def vp01010001101 : Blocks := vp01010001101_0
private theorem bp010100011010 : Branch 0 (-2611761639/4000000 : ℚ) vp01010001101 := by
  apply branch_left_normalized (c:=vp010100011010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2611761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2611761639/2000000 : ℚ) by norm_num]
  exact coverp010100011010
private noncomputable def ep010100011011_0 : Blocks := edgeBlocks% "full/vectors/010100011011-E-0000.bin"
noncomputable def ep010100011011 : Blocks := ep010100011011_0
private theorem idp010100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010001101.list =
    C ((2:ℤ)^111) * horner X vp010100011011.list + horner X ep010100011011.list := by
  exact edge_identity (B := (2:ℤ)^240) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100011011 : Branch 1 (-2611761639/4000000 : ℚ) vp01010001101 := by
  apply branch_checked idp010100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2611761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2613761639/2000000 : ℚ) by norm_num]
  exact coverp010100011011
theorem coverp01010001101 : Covers (-2611761639/4000000 : ℚ) vp01010001101 := join_branches bp010100011010 bp010100011011
private noncomputable def vp010100011001_0 : Blocks := edgeBlocks% "full/vectors/010100011001-V-0000.bin"
noncomputable def vp010100011001 : Blocks := vp010100011001_0
theorem coverp010100011001 : Covers (-2609761639/2000000 : ℚ) vp010100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp010100011000_0 : Blocks := edgeBlocks% "full/vectors/010100011000-V-0000.bin"
noncomputable def vp010100011000 : Blocks := vp010100011000_0
theorem coverp010100011000 : Covers (-2607761639/2000000 : ℚ) vp010100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010001100_0 : Blocks := edgeBlocks% "full/vectors/01010001100-V-0000.bin"
noncomputable def vp01010001100 : Blocks := vp01010001100_0
private theorem bp010100011000 : Branch 0 (-2607761639/4000000 : ℚ) vp01010001100 := by
  apply branch_left_normalized (c:=vp010100011000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2607761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2607761639/2000000 : ℚ) by norm_num]
  exact coverp010100011000
private noncomputable def ep010100011001_0 : Blocks := edgeBlocks% "full/vectors/010100011001-E-0000.bin"
noncomputable def ep010100011001 : Blocks := ep010100011001_0
private theorem idp010100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010001100.list =
    C ((2:ℤ)^111) * horner X vp010100011001.list + horner X ep010100011001.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100011001 : Branch 1 (-2607761639/4000000 : ℚ) vp01010001100 := by
  apply branch_checked idp010100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2607761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2609761639/2000000 : ℚ) by norm_num]
  exact coverp010100011001
theorem coverp01010001100 : Covers (-2607761639/4000000 : ℚ) vp01010001100 := join_branches bp010100011000 bp010100011001
private noncomputable def vp0101000110_0 : Blocks := edgeBlocks% "full/vectors/0101000110-V-0000.bin"
private noncomputable def vp0101000110_1 : Blocks := edgeBlocks% "full/vectors/0101000110-V-0001.bin"
noncomputable def vp0101000110 : Blocks := (Blocks.join vp0101000110_0 vp0101000110_1)
private theorem bp01010001100 : Branch 0 (-2607761639/8000000 : ℚ) vp0101000110 := by
  apply branch_left_normalized (c:=vp01010001100) (k:=0) (m:=98) (by decide +kernel)
  rw [show 2*(-2607761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2607761639/4000000 : ℚ) by norm_num]
  exact coverp01010001100
private noncomputable def ep01010001101_0 : Blocks := edgeBlocks% "full/vectors/01010001101-E-0000.bin"
private noncomputable def ep01010001101_1 : Blocks := edgeBlocks% "full/vectors/01010001101-E-0001.bin"
noncomputable def ep01010001101 : Blocks := (Blocks.join ep01010001101_0 ep01010001101_1)
private theorem idp01010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101000110.list =
    C ((2:ℤ)^200) * horner X vp01010001101.list + horner X ep01010001101.list := by
  exact edge_identity (B := (2:ℤ)^359) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010001101 : Branch 1 (-2607761639/8000000 : ℚ) vp0101000110 := by
  apply branch_checked idp01010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2607761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2611761639/4000000 : ℚ) by norm_num]
  exact coverp01010001101
theorem coverp0101000110 : Covers (-2607761639/8000000 : ℚ) vp0101000110 := join_branches bp01010001100 bp01010001101
private noncomputable def vp010100011_0 : Blocks := edgeBlocks% "full/vectors/010100011-V-0000.bin"
private noncomputable def vp010100011_1 : Blocks := edgeBlocks% "full/vectors/010100011-V-0001.bin"
private noncomputable def vp010100011_2 : Blocks := edgeBlocks% "full/vectors/010100011-V-0002.bin"
noncomputable def vp010100011 : Blocks := (Blocks.join vp010100011_0 (Blocks.join vp010100011_1 vp010100011_2))
private theorem bp0101000110 : Branch 0 (-2607761639/16000000 : ℚ) vp010100011 := by
  apply branch_left_normalized (c:=vp0101000110) (k:=0) (m:=175) (by decide +kernel)
  rw [show 2*(-2607761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2607761639/8000000 : ℚ) by norm_num]
  exact coverp0101000110
private noncomputable def ep0101000111_0 : Blocks := edgeBlocks% "full/vectors/0101000111-E-0000.bin"
private noncomputable def ep0101000111_1 : Blocks := edgeBlocks% "full/vectors/0101000111-E-0001.bin"
private noncomputable def ep0101000111_2 : Blocks := edgeBlocks% "full/vectors/0101000111-E-0002.bin"
noncomputable def ep0101000111 : Blocks := (Blocks.join ep0101000111_0 (Blocks.join ep0101000111_1 ep0101000111_2))
private theorem idp0101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010100011.list =
    C ((2:ℤ)^378) * horner X vp0101000111.list + horner X ep0101000111.list := by
  exact edge_identity (B := (2:ℤ)^595) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101000111 : Branch 1 (-2607761639/16000000 : ℚ) vp010100011 := by
  apply branch_checked idp0101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2607761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2615761639/8000000 : ℚ) by norm_num]
  exact coverp0101000111
theorem coverp010100011 : Covers (-2607761639/16000000 : ℚ) vp010100011 := join_branches bp0101000110 bp0101000111
private noncomputable def vp010100010111_0 : Blocks := edgeBlocks% "full/vectors/010100010111-V-0000.bin"
noncomputable def vp010100010111 : Blocks := vp010100010111_0
theorem coverp010100010111 : Covers (-2605761639/2000000 : ℚ) vp010100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp010100010110_0 : Blocks := edgeBlocks% "full/vectors/010100010110-V-0000.bin"
noncomputable def vp010100010110 : Blocks := vp010100010110_0
theorem coverp010100010110 : Covers (-2603761639/2000000 : ℚ) vp010100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010001011_0 : Blocks := edgeBlocks% "full/vectors/01010001011-V-0000.bin"
noncomputable def vp01010001011 : Blocks := vp01010001011_0
private theorem bp010100010110 : Branch 0 (-2603761639/4000000 : ℚ) vp01010001011 := by
  apply branch_left_normalized (c:=vp010100010110) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2603761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2603761639/2000000 : ℚ) by norm_num]
  exact coverp010100010110
private noncomputable def ep010100010111_0 : Blocks := edgeBlocks% "full/vectors/010100010111-E-0000.bin"
noncomputable def ep010100010111 : Blocks := ep010100010111_0
private theorem idp010100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010001011.list =
    C ((2:ℤ)^111) * horner X vp010100010111.list + horner X ep010100010111.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100010111 : Branch 1 (-2603761639/4000000 : ℚ) vp01010001011 := by
  apply branch_checked idp010100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2603761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2605761639/2000000 : ℚ) by norm_num]
  exact coverp010100010111
theorem coverp01010001011 : Covers (-2603761639/4000000 : ℚ) vp01010001011 := join_branches bp010100010110 bp010100010111
private noncomputable def vp010100010101_0 : Blocks := edgeBlocks% "full/vectors/010100010101-V-0000.bin"
noncomputable def vp010100010101 : Blocks := vp010100010101_0
theorem coverp010100010101 : Covers (-2601761639/2000000 : ℚ) vp010100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp010100010100_0 : Blocks := edgeBlocks% "full/vectors/010100010100-V-0000.bin"
noncomputable def vp010100010100 : Blocks := vp010100010100_0
theorem coverp010100010100 : Covers (-2599761639/2000000 : ℚ) vp010100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010001010_0 : Blocks := edgeBlocks% "full/vectors/01010001010-V-0000.bin"
noncomputable def vp01010001010 : Blocks := vp01010001010_0
private theorem bp010100010100 : Branch 0 (-2599761639/4000000 : ℚ) vp01010001010 := by
  apply branch_left_normalized (c:=vp010100010100) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2599761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2599761639/2000000 : ℚ) by norm_num]
  exact coverp010100010100
private noncomputable def ep010100010101_0 : Blocks := edgeBlocks% "full/vectors/010100010101-E-0000.bin"
noncomputable def ep010100010101 : Blocks := ep010100010101_0
private theorem idp010100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010001010.list =
    C ((2:ℤ)^111) * horner X vp010100010101.list + horner X ep010100010101.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100010101 : Branch 1 (-2599761639/4000000 : ℚ) vp01010001010 := by
  apply branch_checked idp010100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2599761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2601761639/2000000 : ℚ) by norm_num]
  exact coverp010100010101
theorem coverp01010001010 : Covers (-2599761639/4000000 : ℚ) vp01010001010 := join_branches bp010100010100 bp010100010101
private noncomputable def vp0101000101_0 : Blocks := edgeBlocks% "full/vectors/0101000101-V-0000.bin"
private noncomputable def vp0101000101_1 : Blocks := edgeBlocks% "full/vectors/0101000101-V-0001.bin"
noncomputable def vp0101000101 : Blocks := (Blocks.join vp0101000101_0 vp0101000101_1)
private theorem bp01010001010 : Branch 0 (-2599761639/8000000 : ℚ) vp0101000101 := by
  apply branch_left_normalized (c:=vp01010001010) (k:=0) (m:=98) (by decide +kernel)
  rw [show 2*(-2599761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2599761639/4000000 : ℚ) by norm_num]
  exact coverp01010001010
private noncomputable def ep01010001011_0 : Blocks := edgeBlocks% "full/vectors/01010001011-E-0000.bin"
private noncomputable def ep01010001011_1 : Blocks := edgeBlocks% "full/vectors/01010001011-E-0001.bin"
noncomputable def ep01010001011 : Blocks := (Blocks.join ep01010001011_0 ep01010001011_1)
private theorem idp01010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101000101.list =
    C ((2:ℤ)^199) * horner X vp01010001011.list + horner X ep01010001011.list := by
  exact edge_identity (B := (2:ℤ)^359) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010001011 : Branch 1 (-2599761639/8000000 : ℚ) vp0101000101 := by
  apply branch_checked idp01010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2599761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2603761639/4000000 : ℚ) by norm_num]
  exact coverp01010001011
theorem coverp0101000101 : Covers (-2599761639/8000000 : ℚ) vp0101000101 := join_branches bp01010001010 bp01010001011
private noncomputable def vp010100010011_0 : Blocks := edgeBlocks% "full/vectors/010100010011-V-0000.bin"
noncomputable def vp010100010011 : Blocks := vp010100010011_0
theorem coverp010100010011 : Covers (-2597761639/2000000 : ℚ) vp010100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp010100010010_0 : Blocks := edgeBlocks% "full/vectors/010100010010-V-0000.bin"
noncomputable def vp010100010010 : Blocks := vp010100010010_0
theorem coverp010100010010 : Covers (-2595761639/2000000 : ℚ) vp010100010010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010001001_0 : Blocks := edgeBlocks% "full/vectors/01010001001-V-0000.bin"
noncomputable def vp01010001001 : Blocks := vp01010001001_0
private theorem bp010100010010 : Branch 0 (-2595761639/4000000 : ℚ) vp01010001001 := by
  apply branch_left_normalized (c:=vp010100010010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2595761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2595761639/2000000 : ℚ) by norm_num]
  exact coverp010100010010
private noncomputable def ep010100010011_0 : Blocks := edgeBlocks% "full/vectors/010100010011-E-0000.bin"
noncomputable def ep010100010011 : Blocks := ep010100010011_0
private theorem idp010100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010001001.list =
    C ((2:ℤ)^110) * horner X vp010100010011.list + horner X ep010100010011.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100010011 : Branch 1 (-2595761639/4000000 : ℚ) vp01010001001 := by
  apply branch_checked idp010100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2595761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2597761639/2000000 : ℚ) by norm_num]
  exact coverp010100010011
theorem coverp01010001001 : Covers (-2595761639/4000000 : ℚ) vp01010001001 := join_branches bp010100010010 bp010100010011
private noncomputable def vp010100010001_0 : Blocks := edgeBlocks% "full/vectors/010100010001-V-0000.bin"
noncomputable def vp010100010001 : Blocks := vp010100010001_0
theorem coverp010100010001 : Covers (-2593761639/2000000 : ℚ) vp010100010001 := cover_leaf (by decide +kernel)
private noncomputable def vp010100010000_0 : Blocks := edgeBlocks% "full/vectors/010100010000-V-0000.bin"
noncomputable def vp010100010000 : Blocks := vp010100010000_0
theorem coverp010100010000 : Covers (-2591761639/2000000 : ℚ) vp010100010000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010001000_0 : Blocks := edgeBlocks% "full/vectors/01010001000-V-0000.bin"
noncomputable def vp01010001000 : Blocks := vp01010001000_0
private theorem bp010100010000 : Branch 0 (-2591761639/4000000 : ℚ) vp01010001000 := by
  apply branch_left_normalized (c:=vp010100010000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2591761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2591761639/2000000 : ℚ) by norm_num]
  exact coverp010100010000
private noncomputable def ep010100010001_0 : Blocks := edgeBlocks% "full/vectors/010100010001-E-0000.bin"
noncomputable def ep010100010001 : Blocks := ep010100010001_0
private theorem idp010100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010001000.list =
    C ((2:ℤ)^110) * horner X vp010100010001.list + horner X ep010100010001.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100010001 : Branch 1 (-2591761639/4000000 : ℚ) vp01010001000 := by
  apply branch_checked idp010100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2591761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2593761639/2000000 : ℚ) by norm_num]
  exact coverp010100010001
theorem coverp01010001000 : Covers (-2591761639/4000000 : ℚ) vp01010001000 := join_branches bp010100010000 bp010100010001
private noncomputable def vp0101000100_0 : Blocks := edgeBlocks% "full/vectors/0101000100-V-0000.bin"
private noncomputable def vp0101000100_1 : Blocks := edgeBlocks% "full/vectors/0101000100-V-0001.bin"
noncomputable def vp0101000100 : Blocks := (Blocks.join vp0101000100_0 vp0101000100_1)
private theorem bp01010001000 : Branch 0 (-2591761639/8000000 : ℚ) vp0101000100 := by
  apply branch_left_normalized (c:=vp01010001000) (k:=0) (m:=98) (by decide +kernel)
  rw [show 2*(-2591761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2591761639/4000000 : ℚ) by norm_num]
  exact coverp01010001000
private noncomputable def ep01010001001_0 : Blocks := edgeBlocks% "full/vectors/01010001001-E-0000.bin"
private noncomputable def ep01010001001_1 : Blocks := edgeBlocks% "full/vectors/01010001001-E-0001.bin"
noncomputable def ep01010001001 : Blocks := (Blocks.join ep01010001001_0 ep01010001001_1)
private theorem idp01010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101000100.list =
    C ((2:ℤ)^200) * horner X vp01010001001.list + horner X ep01010001001.list := by
  exact edge_identity (B := (2:ℤ)^360) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010001001 : Branch 1 (-2591761639/8000000 : ℚ) vp0101000100 := by
  apply branch_checked idp01010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2591761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2595761639/4000000 : ℚ) by norm_num]
  exact coverp01010001001
theorem coverp0101000100 : Covers (-2591761639/8000000 : ℚ) vp0101000100 := join_branches bp01010001000 bp01010001001
private noncomputable def vp010100010_0 : Blocks := edgeBlocks% "full/vectors/010100010-V-0000.bin"
private noncomputable def vp010100010_1 : Blocks := edgeBlocks% "full/vectors/010100010-V-0001.bin"
private noncomputable def vp010100010_2 : Blocks := edgeBlocks% "full/vectors/010100010-V-0002.bin"
noncomputable def vp010100010 : Blocks := (Blocks.join vp010100010_0 (Blocks.join vp010100010_1 vp010100010_2))
private theorem bp0101000100 : Branch 0 (-2591761639/16000000 : ℚ) vp010100010 := by
  apply branch_left_normalized (c:=vp0101000100) (k:=0) (m:=176) (by decide +kernel)
  rw [show 2*(-2591761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2591761639/8000000 : ℚ) by norm_num]
  exact coverp0101000100
private noncomputable def ep0101000101_0 : Blocks := edgeBlocks% "full/vectors/0101000101-E-0000.bin"
private noncomputable def ep0101000101_1 : Blocks := edgeBlocks% "full/vectors/0101000101-E-0001.bin"
private noncomputable def ep0101000101_2 : Blocks := edgeBlocks% "full/vectors/0101000101-E-0002.bin"
noncomputable def ep0101000101 : Blocks := (Blocks.join ep0101000101_0 (Blocks.join ep0101000101_1 ep0101000101_2))
private theorem idp0101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010100010.list =
    C ((2:ℤ)^376) * horner X vp0101000101.list + horner X ep0101000101.list := by
  exact edge_identity (B := (2:ℤ)^595) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101000101 : Branch 1 (-2591761639/16000000 : ℚ) vp010100010 := by
  apply branch_checked idp0101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2591761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2599761639/8000000 : ℚ) by norm_num]
  exact coverp0101000101
theorem coverp010100010 : Covers (-2591761639/16000000 : ℚ) vp010100010 := join_branches bp0101000100 bp0101000101
private noncomputable def vp01010001_0 : Blocks := edgeBlocks% "full/vectors/01010001-V-0000.bin"
private noncomputable def vp01010001_1 : Blocks := edgeBlocks% "full/vectors/01010001-V-0001.bin"
private noncomputable def vp01010001_2 : Blocks := edgeBlocks% "full/vectors/01010001-V-0002.bin"
private noncomputable def vp01010001_3 : Blocks := edgeBlocks% "full/vectors/01010001-V-0003.bin"
private noncomputable def vp01010001_4 : Blocks := edgeBlocks% "full/vectors/01010001-V-0004.bin"
noncomputable def vp01010001 : Blocks := (Blocks.join (Blocks.join vp01010001_0 vp01010001_1) (Blocks.join vp01010001_2 (Blocks.join vp01010001_3 vp01010001_4)))
private theorem bp010100010 : Branch 0 (-2591761639/32000000 : ℚ) vp01010001 := by
  apply branch_left_normalized (c:=vp010100010) (k:=0) (m:=329) (by decide +kernel)
  rw [show 2*(-2591761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2591761639/16000000 : ℚ) by norm_num]
  exact coverp010100010
private noncomputable def ep010100011_0 : Blocks := edgeBlocks% "full/vectors/010100011-E-0000.bin"
private noncomputable def ep010100011_1 : Blocks := edgeBlocks% "full/vectors/010100011-E-0001.bin"
private noncomputable def ep010100011_2 : Blocks := edgeBlocks% "full/vectors/010100011-E-0002.bin"
private noncomputable def ep010100011_3 : Blocks := edgeBlocks% "full/vectors/010100011-E-0003.bin"
private noncomputable def ep010100011_4 : Blocks := edgeBlocks% "full/vectors/010100011-E-0004.bin"
noncomputable def ep010100011 : Blocks := (Blocks.join (Blocks.join ep010100011_0 ep010100011_1) (Blocks.join ep010100011_2 (Blocks.join ep010100011_3 ep010100011_4)))
private theorem idp010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010001.list =
    C ((2:ℤ)^728) * horner X vp010100011.list + horner X ep010100011.list := by
  exact edge_identity (B := (2:ℤ)^1064) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100011 : Branch 1 (-2591761639/32000000 : ℚ) vp01010001 := by
  apply branch_checked idp010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2591761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2607761639/16000000 : ℚ) by norm_num]
  exact coverp010100011
theorem coverp01010001 : Covers (-2591761639/32000000 : ℚ) vp01010001 := join_branches bp010100010 bp010100011
private noncomputable def vp010100001111_0 : Blocks := edgeBlocks% "full/vectors/010100001111-V-0000.bin"
noncomputable def vp010100001111 : Blocks := vp010100001111_0
theorem coverp010100001111 : Covers (-2589761639/2000000 : ℚ) vp010100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp010100001110_0 : Blocks := edgeBlocks% "full/vectors/010100001110-V-0000.bin"
noncomputable def vp010100001110 : Blocks := vp010100001110_0
theorem coverp010100001110 : Covers (-2587761639/2000000 : ℚ) vp010100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010000111_0 : Blocks := edgeBlocks% "full/vectors/01010000111-V-0000.bin"
noncomputable def vp01010000111 : Blocks := vp01010000111_0
private theorem bp010100001110 : Branch 0 (-2587761639/4000000 : ℚ) vp01010000111 := by
  apply branch_left_normalized (c:=vp010100001110) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2587761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2587761639/2000000 : ℚ) by norm_num]
  exact coverp010100001110
private noncomputable def ep010100001111_0 : Blocks := edgeBlocks% "full/vectors/010100001111-E-0000.bin"
noncomputable def ep010100001111 : Blocks := ep010100001111_0
private theorem idp010100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010000111.list =
    C ((2:ℤ)^110) * horner X vp010100001111.list + horner X ep010100001111.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100001111 : Branch 1 (-2587761639/4000000 : ℚ) vp01010000111 := by
  apply branch_checked idp010100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2587761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2589761639/2000000 : ℚ) by norm_num]
  exact coverp010100001111
theorem coverp01010000111 : Covers (-2587761639/4000000 : ℚ) vp01010000111 := join_branches bp010100001110 bp010100001111
private noncomputable def vp010100001101_0 : Blocks := edgeBlocks% "full/vectors/010100001101-V-0000.bin"
noncomputable def vp010100001101 : Blocks := vp010100001101_0
theorem coverp010100001101 : Covers (-2585761639/2000000 : ℚ) vp010100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp010100001100_0 : Blocks := edgeBlocks% "full/vectors/010100001100-V-0000.bin"
noncomputable def vp010100001100 : Blocks := vp010100001100_0
theorem coverp010100001100 : Covers (-2583761639/2000000 : ℚ) vp010100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010000110_0 : Blocks := edgeBlocks% "full/vectors/01010000110-V-0000.bin"
noncomputable def vp01010000110 : Blocks := vp01010000110_0
private theorem bp010100001100 : Branch 0 (-2583761639/4000000 : ℚ) vp01010000110 := by
  apply branch_left_normalized (c:=vp010100001100) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2583761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2583761639/2000000 : ℚ) by norm_num]
  exact coverp010100001100
private noncomputable def ep010100001101_0 : Blocks := edgeBlocks% "full/vectors/010100001101-E-0000.bin"
noncomputable def ep010100001101 : Blocks := ep010100001101_0
private theorem idp010100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010000110.list =
    C ((2:ℤ)^111) * horner X vp010100001101.list + horner X ep010100001101.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100001101 : Branch 1 (-2583761639/4000000 : ℚ) vp01010000110 := by
  apply branch_checked idp010100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2583761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2585761639/2000000 : ℚ) by norm_num]
  exact coverp010100001101
theorem coverp01010000110 : Covers (-2583761639/4000000 : ℚ) vp01010000110 := join_branches bp010100001100 bp010100001101
private noncomputable def vp0101000011_0 : Blocks := edgeBlocks% "full/vectors/0101000011-V-0000.bin"
private noncomputable def vp0101000011_1 : Blocks := edgeBlocks% "full/vectors/0101000011-V-0001.bin"
noncomputable def vp0101000011 : Blocks := (Blocks.join vp0101000011_0 vp0101000011_1)
private theorem bp01010000110 : Branch 0 (-2583761639/8000000 : ℚ) vp0101000011 := by
  apply branch_left_normalized (c:=vp01010000110) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-2583761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2583761639/4000000 : ℚ) by norm_num]
  exact coverp01010000110
private noncomputable def ep01010000111_0 : Blocks := edgeBlocks% "full/vectors/01010000111-E-0000.bin"
private noncomputable def ep01010000111_1 : Blocks := edgeBlocks% "full/vectors/01010000111-E-0001.bin"
noncomputable def ep01010000111 : Blocks := (Blocks.join ep01010000111_0 ep01010000111_1)
private theorem idp01010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101000011.list =
    C ((2:ℤ)^201) * horner X vp01010000111.list + horner X ep01010000111.list := by
  exact edge_identity (B := (2:ℤ)^361) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010000111 : Branch 1 (-2583761639/8000000 : ℚ) vp0101000011 := by
  apply branch_checked idp01010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2583761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2587761639/4000000 : ℚ) by norm_num]
  exact coverp01010000111
theorem coverp0101000011 : Covers (-2583761639/8000000 : ℚ) vp0101000011 := join_branches bp01010000110 bp01010000111
private noncomputable def vp010100001011_0 : Blocks := edgeBlocks% "full/vectors/010100001011-V-0000.bin"
noncomputable def vp010100001011 : Blocks := vp010100001011_0
theorem coverp010100001011 : Covers (-2581761639/2000000 : ℚ) vp010100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp010100001010_0 : Blocks := edgeBlocks% "full/vectors/010100001010-V-0000.bin"
noncomputable def vp010100001010 : Blocks := vp010100001010_0
theorem coverp010100001010 : Covers (-2579761639/2000000 : ℚ) vp010100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010000101_0 : Blocks := edgeBlocks% "full/vectors/01010000101-V-0000.bin"
noncomputable def vp01010000101 : Blocks := vp01010000101_0
private theorem bp010100001010 : Branch 0 (-2579761639/4000000 : ℚ) vp01010000101 := by
  apply branch_left_normalized (c:=vp010100001010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2579761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2579761639/2000000 : ℚ) by norm_num]
  exact coverp010100001010
private noncomputable def ep010100001011_0 : Blocks := edgeBlocks% "full/vectors/010100001011-E-0000.bin"
noncomputable def ep010100001011 : Blocks := ep010100001011_0
private theorem idp010100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010000101.list =
    C ((2:ℤ)^110) * horner X vp010100001011.list + horner X ep010100001011.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100001011 : Branch 1 (-2579761639/4000000 : ℚ) vp01010000101 := by
  apply branch_checked idp010100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2579761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2581761639/2000000 : ℚ) by norm_num]
  exact coverp010100001011
theorem coverp01010000101 : Covers (-2579761639/4000000 : ℚ) vp01010000101 := join_branches bp010100001010 bp010100001011
private noncomputable def vp010100001001_0 : Blocks := edgeBlocks% "full/vectors/010100001001-V-0000.bin"
noncomputable def vp010100001001 : Blocks := vp010100001001_0
theorem coverp010100001001 : Covers (-2577761639/2000000 : ℚ) vp010100001001 := cover_leaf (by decide +kernel)
private noncomputable def vp010100001000_0 : Blocks := edgeBlocks% "full/vectors/010100001000-V-0000.bin"
noncomputable def vp010100001000 : Blocks := vp010100001000_0
theorem coverp010100001000 : Covers (-2575761639/2000000 : ℚ) vp010100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010000100_0 : Blocks := edgeBlocks% "full/vectors/01010000100-V-0000.bin"
noncomputable def vp01010000100 : Blocks := vp01010000100_0
private theorem bp010100001000 : Branch 0 (-2575761639/4000000 : ℚ) vp01010000100 := by
  apply branch_left_normalized (c:=vp010100001000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2575761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2575761639/2000000 : ℚ) by norm_num]
  exact coverp010100001000
private noncomputable def ep010100001001_0 : Blocks := edgeBlocks% "full/vectors/010100001001-E-0000.bin"
noncomputable def ep010100001001 : Blocks := ep010100001001_0
private theorem idp010100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010000100.list =
    C ((2:ℤ)^112) * horner X vp010100001001.list + horner X ep010100001001.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100001001 : Branch 1 (-2575761639/4000000 : ℚ) vp01010000100 := by
  apply branch_checked idp010100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2575761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2577761639/2000000 : ℚ) by norm_num]
  exact coverp010100001001
theorem coverp01010000100 : Covers (-2575761639/4000000 : ℚ) vp01010000100 := join_branches bp010100001000 bp010100001001
private noncomputable def vp0101000010_0 : Blocks := edgeBlocks% "full/vectors/0101000010-V-0000.bin"
private noncomputable def vp0101000010_1 : Blocks := edgeBlocks% "full/vectors/0101000010-V-0001.bin"
noncomputable def vp0101000010 : Blocks := (Blocks.join vp0101000010_0 vp0101000010_1)
private theorem bp01010000100 : Branch 0 (-2575761639/8000000 : ℚ) vp0101000010 := by
  apply branch_left_normalized (c:=vp01010000100) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-2575761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2575761639/4000000 : ℚ) by norm_num]
  exact coverp01010000100
private noncomputable def ep01010000101_0 : Blocks := edgeBlocks% "full/vectors/01010000101-E-0000.bin"
private noncomputable def ep01010000101_1 : Blocks := edgeBlocks% "full/vectors/01010000101-E-0001.bin"
noncomputable def ep01010000101 : Blocks := (Blocks.join ep01010000101_0 ep01010000101_1)
private theorem idp01010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101000010.list =
    C ((2:ℤ)^202) * horner X vp01010000101.list + horner X ep01010000101.list := by
  exact edge_identity (B := (2:ℤ)^362) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010000101 : Branch 1 (-2575761639/8000000 : ℚ) vp0101000010 := by
  apply branch_checked idp01010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2575761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2579761639/4000000 : ℚ) by norm_num]
  exact coverp01010000101
theorem coverp0101000010 : Covers (-2575761639/8000000 : ℚ) vp0101000010 := join_branches bp01010000100 bp01010000101
private noncomputable def vp010100001_0 : Blocks := edgeBlocks% "full/vectors/010100001-V-0000.bin"
private noncomputable def vp010100001_1 : Blocks := edgeBlocks% "full/vectors/010100001-V-0001.bin"
private noncomputable def vp010100001_2 : Blocks := edgeBlocks% "full/vectors/010100001-V-0002.bin"
noncomputable def vp010100001 : Blocks := (Blocks.join vp010100001_0 (Blocks.join vp010100001_1 vp010100001_2))
private theorem bp0101000010 : Branch 0 (-2575761639/16000000 : ℚ) vp010100001 := by
  apply branch_left_normalized (c:=vp0101000010) (k:=0) (m:=177) (by decide +kernel)
  rw [show 2*(-2575761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2575761639/8000000 : ℚ) by norm_num]
  exact coverp0101000010
private noncomputable def ep0101000011_0 : Blocks := edgeBlocks% "full/vectors/0101000011-E-0000.bin"
private noncomputable def ep0101000011_1 : Blocks := edgeBlocks% "full/vectors/0101000011-E-0001.bin"
private noncomputable def ep0101000011_2 : Blocks := edgeBlocks% "full/vectors/0101000011-E-0002.bin"
noncomputable def ep0101000011 : Blocks := (Blocks.join ep0101000011_0 (Blocks.join ep0101000011_1 ep0101000011_2))
private theorem idp0101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010100001.list =
    C ((2:ℤ)^379) * horner X vp0101000011.list + horner X ep0101000011.list := by
  exact edge_identity (B := (2:ℤ)^598) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101000011 : Branch 1 (-2575761639/16000000 : ℚ) vp010100001 := by
  apply branch_checked idp0101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2575761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2583761639/8000000 : ℚ) by norm_num]
  exact coverp0101000011
theorem coverp010100001 : Covers (-2575761639/16000000 : ℚ) vp010100001 := join_branches bp0101000010 bp0101000011
private noncomputable def vp010100000111_0 : Blocks := edgeBlocks% "full/vectors/010100000111-V-0000.bin"
noncomputable def vp010100000111 : Blocks := vp010100000111_0
theorem coverp010100000111 : Covers (-2573761639/2000000 : ℚ) vp010100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp010100000110_0 : Blocks := edgeBlocks% "full/vectors/010100000110-V-0000.bin"
noncomputable def vp010100000110 : Blocks := vp010100000110_0
theorem coverp010100000110 : Covers (-2571761639/2000000 : ℚ) vp010100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010000011_0 : Blocks := edgeBlocks% "full/vectors/01010000011-V-0000.bin"
noncomputable def vp01010000011 : Blocks := vp01010000011_0
private theorem bp010100000110 : Branch 0 (-2571761639/4000000 : ℚ) vp01010000011 := by
  apply branch_left_normalized (c:=vp010100000110) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2571761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2571761639/2000000 : ℚ) by norm_num]
  exact coverp010100000110
private noncomputable def ep010100000111_0 : Blocks := edgeBlocks% "full/vectors/010100000111-E-0000.bin"
noncomputable def ep010100000111 : Blocks := ep010100000111_0
private theorem idp010100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010000011.list =
    C ((2:ℤ)^111) * horner X vp010100000111.list + horner X ep010100000111.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100000111 : Branch 1 (-2571761639/4000000 : ℚ) vp01010000011 := by
  apply branch_checked idp010100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2571761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2573761639/2000000 : ℚ) by norm_num]
  exact coverp010100000111
theorem coverp01010000011 : Covers (-2571761639/4000000 : ℚ) vp01010000011 := join_branches bp010100000110 bp010100000111
private noncomputable def vp010100000101_0 : Blocks := edgeBlocks% "full/vectors/010100000101-V-0000.bin"
noncomputable def vp010100000101 : Blocks := vp010100000101_0
theorem coverp010100000101 : Covers (-2569761639/2000000 : ℚ) vp010100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp010100000100_0 : Blocks := edgeBlocks% "full/vectors/010100000100-V-0000.bin"
noncomputable def vp010100000100 : Blocks := vp010100000100_0
theorem coverp010100000100 : Covers (-2567761639/2000000 : ℚ) vp010100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010000010_0 : Blocks := edgeBlocks% "full/vectors/01010000010-V-0000.bin"
noncomputable def vp01010000010 : Blocks := vp01010000010_0
private theorem bp010100000100 : Branch 0 (-2567761639/4000000 : ℚ) vp01010000010 := by
  apply branch_left_normalized (c:=vp010100000100) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2567761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2567761639/2000000 : ℚ) by norm_num]
  exact coverp010100000100
private noncomputable def ep010100000101_0 : Blocks := edgeBlocks% "full/vectors/010100000101-E-0000.bin"
noncomputable def ep010100000101 : Blocks := ep010100000101_0
private theorem idp010100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010000010.list =
    C ((2:ℤ)^112) * horner X vp010100000101.list + horner X ep010100000101.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100000101 : Branch 1 (-2567761639/4000000 : ℚ) vp01010000010 := by
  apply branch_checked idp010100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2567761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2569761639/2000000 : ℚ) by norm_num]
  exact coverp010100000101
theorem coverp01010000010 : Covers (-2567761639/4000000 : ℚ) vp01010000010 := join_branches bp010100000100 bp010100000101
private noncomputable def vp0101000001_0 : Blocks := edgeBlocks% "full/vectors/0101000001-V-0000.bin"
private noncomputable def vp0101000001_1 : Blocks := edgeBlocks% "full/vectors/0101000001-V-0001.bin"
noncomputable def vp0101000001 : Blocks := (Blocks.join vp0101000001_0 vp0101000001_1)
private theorem bp01010000010 : Branch 0 (-2567761639/8000000 : ℚ) vp0101000001 := by
  apply branch_left_normalized (c:=vp01010000010) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-2567761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2567761639/4000000 : ℚ) by norm_num]
  exact coverp01010000010
private noncomputable def ep01010000011_0 : Blocks := edgeBlocks% "full/vectors/01010000011-E-0000.bin"
private noncomputable def ep01010000011_1 : Blocks := edgeBlocks% "full/vectors/01010000011-E-0001.bin"
noncomputable def ep01010000011 : Blocks := (Blocks.join ep01010000011_0 ep01010000011_1)
private theorem idp01010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101000001.list =
    C ((2:ℤ)^201) * horner X vp01010000011.list + horner X ep01010000011.list := by
  exact edge_identity (B := (2:ℤ)^362) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010000011 : Branch 1 (-2567761639/8000000 : ℚ) vp0101000001 := by
  apply branch_checked idp01010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2567761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2571761639/4000000 : ℚ) by norm_num]
  exact coverp01010000011
theorem coverp0101000001 : Covers (-2567761639/8000000 : ℚ) vp0101000001 := join_branches bp01010000010 bp01010000011
private noncomputable def vp010100000011_0 : Blocks := edgeBlocks% "full/vectors/010100000011-V-0000.bin"
noncomputable def vp010100000011 : Blocks := vp010100000011_0
theorem coverp010100000011 : Covers (-2565761639/2000000 : ℚ) vp010100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp010100000010_0 : Blocks := edgeBlocks% "full/vectors/010100000010-V-0000.bin"
noncomputable def vp010100000010 : Blocks := vp010100000010_0
theorem coverp010100000010 : Covers (-2563761639/2000000 : ℚ) vp010100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010000001_0 : Blocks := edgeBlocks% "full/vectors/01010000001-V-0000.bin"
noncomputable def vp01010000001 : Blocks := vp01010000001_0
private theorem bp010100000010 : Branch 0 (-2563761639/4000000 : ℚ) vp01010000001 := by
  apply branch_left_normalized (c:=vp010100000010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2563761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2563761639/2000000 : ℚ) by norm_num]
  exact coverp010100000010
private noncomputable def ep010100000011_0 : Blocks := edgeBlocks% "full/vectors/010100000011-E-0000.bin"
noncomputable def ep010100000011 : Blocks := ep010100000011_0
private theorem idp010100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010000001.list =
    C ((2:ℤ)^112) * horner X vp010100000011.list + horner X ep010100000011.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100000011 : Branch 1 (-2563761639/4000000 : ℚ) vp01010000001 := by
  apply branch_checked idp010100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2563761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2565761639/2000000 : ℚ) by norm_num]
  exact coverp010100000011
theorem coverp01010000001 : Covers (-2563761639/4000000 : ℚ) vp01010000001 := join_branches bp010100000010 bp010100000011
private noncomputable def vp010100000001_0 : Blocks := edgeBlocks% "full/vectors/010100000001-V-0000.bin"
noncomputable def vp010100000001 : Blocks := vp010100000001_0
theorem coverp010100000001 : Covers (-2561761639/2000000 : ℚ) vp010100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp010100000000_0 : Blocks := edgeBlocks% "full/vectors/010100000000-V-0000.bin"
noncomputable def vp010100000000 : Blocks := vp010100000000_0
theorem coverp010100000000 : Covers (-2559761639/2000000 : ℚ) vp010100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010000000_0 : Blocks := edgeBlocks% "full/vectors/01010000000-V-0000.bin"
noncomputable def vp01010000000 : Blocks := vp01010000000_0
private theorem bp010100000000 : Branch 0 (-2559761639/4000000 : ℚ) vp01010000000 := by
  apply branch_left_normalized (c:=vp010100000000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2559761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2559761639/2000000 : ℚ) by norm_num]
  exact coverp010100000000
private noncomputable def ep010100000001_0 : Blocks := edgeBlocks% "full/vectors/010100000001-E-0000.bin"
noncomputable def ep010100000001 : Blocks := ep010100000001_0
private theorem idp010100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010000000.list =
    C ((2:ℤ)^112) * horner X vp010100000001.list + horner X ep010100000001.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100000001 : Branch 1 (-2559761639/4000000 : ℚ) vp01010000000 := by
  apply branch_checked idp010100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2559761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2561761639/2000000 : ℚ) by norm_num]
  exact coverp010100000001
theorem coverp01010000000 : Covers (-2559761639/4000000 : ℚ) vp01010000000 := join_branches bp010100000000 bp010100000001
private noncomputable def vp0101000000_0 : Blocks := edgeBlocks% "full/vectors/0101000000-V-0000.bin"
private noncomputable def vp0101000000_1 : Blocks := edgeBlocks% "full/vectors/0101000000-V-0001.bin"
noncomputable def vp0101000000 : Blocks := (Blocks.join vp0101000000_0 vp0101000000_1)
private theorem bp01010000000 : Branch 0 (-2559761639/8000000 : ℚ) vp0101000000 := by
  apply branch_left_normalized (c:=vp01010000000) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-2559761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2559761639/4000000 : ℚ) by norm_num]
  exact coverp01010000000
private noncomputable def ep01010000001_0 : Blocks := edgeBlocks% "full/vectors/01010000001-E-0000.bin"
private noncomputable def ep01010000001_1 : Blocks := edgeBlocks% "full/vectors/01010000001-E-0001.bin"
noncomputable def ep01010000001 : Blocks := (Blocks.join ep01010000001_0 ep01010000001_1)
private theorem idp01010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101000000.list =
    C ((2:ℤ)^201) * horner X vp01010000001.list + horner X ep01010000001.list := by
  exact edge_identity (B := (2:ℤ)^362) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010000001 : Branch 1 (-2559761639/8000000 : ℚ) vp0101000000 := by
  apply branch_checked idp01010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2559761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2563761639/4000000 : ℚ) by norm_num]
  exact coverp01010000001
theorem coverp0101000000 : Covers (-2559761639/8000000 : ℚ) vp0101000000 := join_branches bp01010000000 bp01010000001
private noncomputable def vp010100000_0 : Blocks := edgeBlocks% "full/vectors/010100000-V-0000.bin"
private noncomputable def vp010100000_1 : Blocks := edgeBlocks% "full/vectors/010100000-V-0001.bin"
private noncomputable def vp010100000_2 : Blocks := edgeBlocks% "full/vectors/010100000-V-0002.bin"
noncomputable def vp010100000 : Blocks := (Blocks.join vp010100000_0 (Blocks.join vp010100000_1 vp010100000_2))
private theorem bp0101000000 : Branch 0 (-2559761639/16000000 : ℚ) vp010100000 := by
  apply branch_left_normalized (c:=vp0101000000) (k:=0) (m:=177) (by decide +kernel)
  rw [show 2*(-2559761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2559761639/8000000 : ℚ) by norm_num]
  exact coverp0101000000
private noncomputable def ep0101000001_0 : Blocks := edgeBlocks% "full/vectors/0101000001-E-0000.bin"
private noncomputable def ep0101000001_1 : Blocks := edgeBlocks% "full/vectors/0101000001-E-0001.bin"
private noncomputable def ep0101000001_2 : Blocks := edgeBlocks% "full/vectors/0101000001-E-0002.bin"
noncomputable def ep0101000001 : Blocks := (Blocks.join ep0101000001_0 (Blocks.join ep0101000001_1 ep0101000001_2))
private theorem idp0101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010100000.list =
    C ((2:ℤ)^379) * horner X vp0101000001.list + horner X ep0101000001.list := by
  exact edge_identity (B := (2:ℤ)^599) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101000001 : Branch 1 (-2559761639/16000000 : ℚ) vp010100000 := by
  apply branch_checked idp0101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2559761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2567761639/8000000 : ℚ) by norm_num]
  exact coverp0101000001
theorem coverp010100000 : Covers (-2559761639/16000000 : ℚ) vp010100000 := join_branches bp0101000000 bp0101000001
private noncomputable def vp01010000_0 : Blocks := edgeBlocks% "full/vectors/01010000-V-0000.bin"
private noncomputable def vp01010000_1 : Blocks := edgeBlocks% "full/vectors/01010000-V-0001.bin"
private noncomputable def vp01010000_2 : Blocks := edgeBlocks% "full/vectors/01010000-V-0002.bin"
private noncomputable def vp01010000_3 : Blocks := edgeBlocks% "full/vectors/01010000-V-0003.bin"
private noncomputable def vp01010000_4 : Blocks := edgeBlocks% "full/vectors/01010000-V-0004.bin"
noncomputable def vp01010000 : Blocks := (Blocks.join (Blocks.join vp01010000_0 vp01010000_1) (Blocks.join vp01010000_2 (Blocks.join vp01010000_3 vp01010000_4)))
private theorem bp010100000 : Branch 0 (-2559761639/32000000 : ℚ) vp01010000 := by
  apply branch_left_normalized (c:=vp010100000) (k:=0) (m:=332) (by decide +kernel)
  rw [show 2*(-2559761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2559761639/16000000 : ℚ) by norm_num]
  exact coverp010100000
private noncomputable def ep010100001_0 : Blocks := edgeBlocks% "full/vectors/010100001-E-0000.bin"
private noncomputable def ep010100001_1 : Blocks := edgeBlocks% "full/vectors/010100001-E-0001.bin"
private noncomputable def ep010100001_2 : Blocks := edgeBlocks% "full/vectors/010100001-E-0002.bin"
private noncomputable def ep010100001_3 : Blocks := edgeBlocks% "full/vectors/010100001-E-0003.bin"
private noncomputable def ep010100001_4 : Blocks := edgeBlocks% "full/vectors/010100001-E-0004.bin"
noncomputable def ep010100001 : Blocks := (Blocks.join (Blocks.join ep010100001_0 ep010100001_1) (Blocks.join ep010100001_2 (Blocks.join ep010100001_3 ep010100001_4)))
private theorem idp010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010000.list =
    C ((2:ℤ)^731) * horner X vp010100001.list + horner X ep010100001.list := by
  exact edge_identity (B := (2:ℤ)^1069) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010100001 : Branch 1 (-2559761639/32000000 : ℚ) vp01010000 := by
  apply branch_checked idp010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2559761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2575761639/16000000 : ℚ) by norm_num]
  exact coverp010100001
theorem coverp01010000 : Covers (-2559761639/32000000 : ℚ) vp01010000 := join_branches bp010100000 bp010100001
private noncomputable def vp0101000_0 : Blocks := edgeBlocks% "full/vectors/0101000-V-0000.bin"
private noncomputable def vp0101000_1 : Blocks := edgeBlocks% "full/vectors/0101000-V-0001.bin"
private noncomputable def vp0101000_2 : Blocks := edgeBlocks% "full/vectors/0101000-V-0002.bin"
private noncomputable def vp0101000_3 : Blocks := edgeBlocks% "full/vectors/0101000-V-0003.bin"
private noncomputable def vp0101000_4 : Blocks := edgeBlocks% "full/vectors/0101000-V-0004.bin"
private noncomputable def vp0101000_5 : Blocks := edgeBlocks% "full/vectors/0101000-V-0005.bin"
private noncomputable def vp0101000_6 : Blocks := edgeBlocks% "full/vectors/0101000-V-0006.bin"
private noncomputable def vp0101000_7 : Blocks := edgeBlocks% "full/vectors/0101000-V-0007.bin"
private noncomputable def vp0101000_8 : Blocks := edgeBlocks% "full/vectors/0101000-V-0008.bin"
private noncomputable def vp0101000_9 : Blocks := edgeBlocks% "full/vectors/0101000-V-0009.bin"
noncomputable def vp0101000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0101000_0 vp0101000_1) (Blocks.join vp0101000_2 (Blocks.join vp0101000_3 vp0101000_4))) (Blocks.join (Blocks.join vp0101000_5 vp0101000_6) (Blocks.join vp0101000_7 (Blocks.join vp0101000_8 vp0101000_9))))
private theorem bp01010000 : Branch 0 (-2559761639/64000000 : ℚ) vp0101000 := by
  apply branch_left_normalized (c:=vp01010000) (k:=0) (m:=638) (by decide +kernel)
  rw [show 2*(-2559761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2559761639/32000000 : ℚ) by norm_num]
  exact coverp01010000
private noncomputable def ep01010001_0 : Blocks := edgeBlocks% "full/vectors/01010001-E-0000.bin"
private noncomputable def ep01010001_1 : Blocks := edgeBlocks% "full/vectors/01010001-E-0001.bin"
private noncomputable def ep01010001_2 : Blocks := edgeBlocks% "full/vectors/01010001-E-0002.bin"
private noncomputable def ep01010001_3 : Blocks := edgeBlocks% "full/vectors/01010001-E-0003.bin"
private noncomputable def ep01010001_4 : Blocks := edgeBlocks% "full/vectors/01010001-E-0004.bin"
private noncomputable def ep01010001_5 : Blocks := edgeBlocks% "full/vectors/01010001-E-0005.bin"
private noncomputable def ep01010001_6 : Blocks := edgeBlocks% "full/vectors/01010001-E-0006.bin"
private noncomputable def ep01010001_7 : Blocks := edgeBlocks% "full/vectors/01010001-E-0007.bin"
private noncomputable def ep01010001_8 : Blocks := edgeBlocks% "full/vectors/01010001-E-0008.bin"
private noncomputable def ep01010001_9 : Blocks := edgeBlocks% "full/vectors/01010001-E-0009.bin"
noncomputable def ep01010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01010001_0 ep01010001_1) (Blocks.join ep01010001_2 (Blocks.join ep01010001_3 ep01010001_4))) (Blocks.join (Blocks.join ep01010001_5 ep01010001_6) (Blocks.join ep01010001_7 (Blocks.join ep01010001_8 ep01010001_9))))
private theorem idp01010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101000.list =
    C ((2:ℤ)^1430) * horner X vp01010001.list + horner X ep01010001.list := by
  exact edge_identity (B := (2:ℤ)^2002) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010001 : Branch 1 (-2559761639/64000000 : ℚ) vp0101000 := by
  apply branch_checked idp01010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2559761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2591761639/32000000 : ℚ) by norm_num]
  exact coverp01010001
theorem coverp0101000 : Covers (-2559761639/64000000 : ℚ) vp0101000 := join_branches bp01010000 bp01010001
private noncomputable def vp010100_0 : Blocks := edgeBlocks% "full/vectors/010100-V-0000.bin"
private noncomputable def vp010100_1 : Blocks := edgeBlocks% "full/vectors/010100-V-0001.bin"
private noncomputable def vp010100_2 : Blocks := edgeBlocks% "full/vectors/010100-V-0002.bin"
private noncomputable def vp010100_3 : Blocks := edgeBlocks% "full/vectors/010100-V-0003.bin"
private noncomputable def vp010100_4 : Blocks := edgeBlocks% "full/vectors/010100-V-0004.bin"
private noncomputable def vp010100_5 : Blocks := edgeBlocks% "full/vectors/010100-V-0005.bin"
private noncomputable def vp010100_6 : Blocks := edgeBlocks% "full/vectors/010100-V-0006.bin"
private noncomputable def vp010100_7 : Blocks := edgeBlocks% "full/vectors/010100-V-0007.bin"
private noncomputable def vp010100_8 : Blocks := edgeBlocks% "full/vectors/010100-V-0008.bin"
private noncomputable def vp010100_9 : Blocks := edgeBlocks% "full/vectors/010100-V-0009.bin"
private noncomputable def vp010100_10 : Blocks := edgeBlocks% "full/vectors/010100-V-0010.bin"
private noncomputable def vp010100_11 : Blocks := edgeBlocks% "full/vectors/010100-V-0011.bin"
private noncomputable def vp010100_12 : Blocks := edgeBlocks% "full/vectors/010100-V-0012.bin"
private noncomputable def vp010100_13 : Blocks := edgeBlocks% "full/vectors/010100-V-0013.bin"
private noncomputable def vp010100_14 : Blocks := edgeBlocks% "full/vectors/010100-V-0014.bin"
private noncomputable def vp010100_15 : Blocks := edgeBlocks% "full/vectors/010100-V-0015.bin"
private noncomputable def vp010100_16 : Blocks := edgeBlocks% "full/vectors/010100-V-0016.bin"
private noncomputable def vp010100_17 : Blocks := edgeBlocks% "full/vectors/010100-V-0017.bin"
private noncomputable def vp010100_18 : Blocks := edgeBlocks% "full/vectors/010100-V-0018.bin"
noncomputable def vp010100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp010100_0 vp010100_1) (Blocks.join vp010100_2 vp010100_3)) (Blocks.join (Blocks.join vp010100_4 vp010100_5) (Blocks.join vp010100_6 (Blocks.join vp010100_7 vp010100_8)))) (Blocks.join (Blocks.join (Blocks.join vp010100_9 vp010100_10) (Blocks.join vp010100_11 (Blocks.join vp010100_12 vp010100_13))) (Blocks.join (Blocks.join vp010100_14 vp010100_15) (Blocks.join vp010100_16 (Blocks.join vp010100_17 vp010100_18)))))
private theorem bp0101000 : Branch 0 (-2559761639/128000000 : ℚ) vp010100 := by
  apply branch_left_normalized (c:=vp0101000) (k:=0) (m:=1244) (by decide +kernel)
  rw [show 2*(-2559761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-2559761639/64000000 : ℚ) by norm_num]
  exact coverp0101000
private noncomputable def ep0101001_0 : Blocks := edgeBlocks% "full/vectors/0101001-E-0000.bin"
private noncomputable def ep0101001_1 : Blocks := edgeBlocks% "full/vectors/0101001-E-0001.bin"
private noncomputable def ep0101001_2 : Blocks := edgeBlocks% "full/vectors/0101001-E-0002.bin"
private noncomputable def ep0101001_3 : Blocks := edgeBlocks% "full/vectors/0101001-E-0003.bin"
private noncomputable def ep0101001_4 : Blocks := edgeBlocks% "full/vectors/0101001-E-0004.bin"
private noncomputable def ep0101001_5 : Blocks := edgeBlocks% "full/vectors/0101001-E-0005.bin"
private noncomputable def ep0101001_6 : Blocks := edgeBlocks% "full/vectors/0101001-E-0006.bin"
private noncomputable def ep0101001_7 : Blocks := edgeBlocks% "full/vectors/0101001-E-0007.bin"
private noncomputable def ep0101001_8 : Blocks := edgeBlocks% "full/vectors/0101001-E-0008.bin"
private noncomputable def ep0101001_9 : Blocks := edgeBlocks% "full/vectors/0101001-E-0009.bin"
private noncomputable def ep0101001_10 : Blocks := edgeBlocks% "full/vectors/0101001-E-0010.bin"
private noncomputable def ep0101001_11 : Blocks := edgeBlocks% "full/vectors/0101001-E-0011.bin"
private noncomputable def ep0101001_12 : Blocks := edgeBlocks% "full/vectors/0101001-E-0012.bin"
private noncomputable def ep0101001_13 : Blocks := edgeBlocks% "full/vectors/0101001-E-0013.bin"
private noncomputable def ep0101001_14 : Blocks := edgeBlocks% "full/vectors/0101001-E-0014.bin"
private noncomputable def ep0101001_15 : Blocks := edgeBlocks% "full/vectors/0101001-E-0015.bin"
private noncomputable def ep0101001_16 : Blocks := edgeBlocks% "full/vectors/0101001-E-0016.bin"
private noncomputable def ep0101001_17 : Blocks := edgeBlocks% "full/vectors/0101001-E-0017.bin"
private noncomputable def ep0101001_18 : Blocks := edgeBlocks% "full/vectors/0101001-E-0018.bin"
noncomputable def ep0101001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0101001_0 ep0101001_1) (Blocks.join ep0101001_2 ep0101001_3)) (Blocks.join (Blocks.join ep0101001_4 ep0101001_5) (Blocks.join ep0101001_6 (Blocks.join ep0101001_7 ep0101001_8)))) (Blocks.join (Blocks.join (Blocks.join ep0101001_9 ep0101001_10) (Blocks.join ep0101001_11 (Blocks.join ep0101001_12 ep0101001_13))) (Blocks.join (Blocks.join ep0101001_14 ep0101001_15) (Blocks.join ep0101001_16 (Blocks.join ep0101001_17 ep0101001_18)))))
private theorem idp0101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010100.list =
    C ((2:ℤ)^2786) * horner X vp0101001.list + horner X ep0101001.list := by
  exact edge_identity (B := (2:ℤ)^3821) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101001 : Branch 1 (-2559761639/128000000 : ℚ) vp010100 := by
  apply branch_checked idp0101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2559761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-2623761639/64000000 : ℚ) by norm_num]
  exact coverp0101001
theorem coverp010100 : Covers (-2559761639/128000000 : ℚ) vp010100 := join_branches bp0101000 bp0101001
private noncomputable def vp01010_0 : Blocks := edgeBlocks% "full/vectors/01010-V-0000.bin"
private noncomputable def vp01010_1 : Blocks := edgeBlocks% "full/vectors/01010-V-0001.bin"
private noncomputable def vp01010_2 : Blocks := edgeBlocks% "full/vectors/01010-V-0002.bin"
private noncomputable def vp01010_3 : Blocks := edgeBlocks% "full/vectors/01010-V-0003.bin"
private noncomputable def vp01010_4 : Blocks := edgeBlocks% "full/vectors/01010-V-0004.bin"
private noncomputable def vp01010_5 : Blocks := edgeBlocks% "full/vectors/01010-V-0005.bin"
private noncomputable def vp01010_6 : Blocks := edgeBlocks% "full/vectors/01010-V-0006.bin"
private noncomputable def vp01010_7 : Blocks := edgeBlocks% "full/vectors/01010-V-0007.bin"
private noncomputable def vp01010_8 : Blocks := edgeBlocks% "full/vectors/01010-V-0008.bin"
private noncomputable def vp01010_9 : Blocks := edgeBlocks% "full/vectors/01010-V-0009.bin"
private noncomputable def vp01010_10 : Blocks := edgeBlocks% "full/vectors/01010-V-0010.bin"
private noncomputable def vp01010_11 : Blocks := edgeBlocks% "full/vectors/01010-V-0011.bin"
private noncomputable def vp01010_12 : Blocks := edgeBlocks% "full/vectors/01010-V-0012.bin"
private noncomputable def vp01010_13 : Blocks := edgeBlocks% "full/vectors/01010-V-0013.bin"
private noncomputable def vp01010_14 : Blocks := edgeBlocks% "full/vectors/01010-V-0014.bin"
private noncomputable def vp01010_15 : Blocks := edgeBlocks% "full/vectors/01010-V-0015.bin"
private noncomputable def vp01010_16 : Blocks := edgeBlocks% "full/vectors/01010-V-0016.bin"
private noncomputable def vp01010_17 : Blocks := edgeBlocks% "full/vectors/01010-V-0017.bin"
private noncomputable def vp01010_18 : Blocks := edgeBlocks% "full/vectors/01010-V-0018.bin"
private noncomputable def vp01010_19 : Blocks := edgeBlocks% "full/vectors/01010-V-0019.bin"
private noncomputable def vp01010_20 : Blocks := edgeBlocks% "full/vectors/01010-V-0020.bin"
private noncomputable def vp01010_21 : Blocks := edgeBlocks% "full/vectors/01010-V-0021.bin"
private noncomputable def vp01010_22 : Blocks := edgeBlocks% "full/vectors/01010-V-0022.bin"
private noncomputable def vp01010_23 : Blocks := edgeBlocks% "full/vectors/01010-V-0023.bin"
private noncomputable def vp01010_24 : Blocks := edgeBlocks% "full/vectors/01010-V-0024.bin"
private noncomputable def vp01010_25 : Blocks := edgeBlocks% "full/vectors/01010-V-0025.bin"
private noncomputable def vp01010_26 : Blocks := edgeBlocks% "full/vectors/01010-V-0026.bin"
private noncomputable def vp01010_27 : Blocks := edgeBlocks% "full/vectors/01010-V-0027.bin"
private noncomputable def vp01010_28 : Blocks := edgeBlocks% "full/vectors/01010-V-0028.bin"
private noncomputable def vp01010_29 : Blocks := edgeBlocks% "full/vectors/01010-V-0029.bin"
private noncomputable def vp01010_30 : Blocks := edgeBlocks% "full/vectors/01010-V-0030.bin"
private noncomputable def vp01010_31 : Blocks := edgeBlocks% "full/vectors/01010-V-0031.bin"
private noncomputable def vp01010_32 : Blocks := edgeBlocks% "full/vectors/01010-V-0032.bin"
private noncomputable def vp01010_33 : Blocks := edgeBlocks% "full/vectors/01010-V-0033.bin"
private noncomputable def vp01010_34 : Blocks := edgeBlocks% "full/vectors/01010-V-0034.bin"
private noncomputable def vp01010_35 : Blocks := edgeBlocks% "full/vectors/01010-V-0035.bin"
private noncomputable def vp01010_36 : Blocks := edgeBlocks% "full/vectors/01010-V-0036.bin"
noncomputable def vp01010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01010_0 vp01010_1) (Blocks.join vp01010_2 vp01010_3)) (Blocks.join (Blocks.join vp01010_4 vp01010_5) (Blocks.join vp01010_6 (Blocks.join vp01010_7 vp01010_8)))) (Blocks.join (Blocks.join (Blocks.join vp01010_9 vp01010_10) (Blocks.join vp01010_11 vp01010_12)) (Blocks.join (Blocks.join vp01010_13 vp01010_14) (Blocks.join vp01010_15 (Blocks.join vp01010_16 vp01010_17))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01010_18 vp01010_19) (Blocks.join vp01010_20 vp01010_21)) (Blocks.join (Blocks.join vp01010_22 vp01010_23) (Blocks.join vp01010_24 (Blocks.join vp01010_25 vp01010_26)))) (Blocks.join (Blocks.join (Blocks.join vp01010_27 vp01010_28) (Blocks.join vp01010_29 (Blocks.join vp01010_30 vp01010_31))) (Blocks.join (Blocks.join vp01010_32 vp01010_33) (Blocks.join vp01010_34 (Blocks.join vp01010_35 vp01010_36))))))
private theorem bp010100 : Branch 0 (-2559761639/256000000 : ℚ) vp01010 := by
  apply branch_left_normalized (c:=vp010100) (k:=0) (m:=2416) (by decide +kernel)
  rw [show 2*(-2559761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-2559761639/128000000 : ℚ) by norm_num]
  exact coverp010100
private noncomputable def ep010101_0 : Blocks := edgeBlocks% "full/vectors/010101-E-0000.bin"
private noncomputable def ep010101_1 : Blocks := edgeBlocks% "full/vectors/010101-E-0001.bin"
private noncomputable def ep010101_2 : Blocks := edgeBlocks% "full/vectors/010101-E-0002.bin"
private noncomputable def ep010101_3 : Blocks := edgeBlocks% "full/vectors/010101-E-0003.bin"
private noncomputable def ep010101_4 : Blocks := edgeBlocks% "full/vectors/010101-E-0004.bin"
private noncomputable def ep010101_5 : Blocks := edgeBlocks% "full/vectors/010101-E-0005.bin"
private noncomputable def ep010101_6 : Blocks := edgeBlocks% "full/vectors/010101-E-0006.bin"
private noncomputable def ep010101_7 : Blocks := edgeBlocks% "full/vectors/010101-E-0007.bin"
private noncomputable def ep010101_8 : Blocks := edgeBlocks% "full/vectors/010101-E-0008.bin"
private noncomputable def ep010101_9 : Blocks := edgeBlocks% "full/vectors/010101-E-0009.bin"
private noncomputable def ep010101_10 : Blocks := edgeBlocks% "full/vectors/010101-E-0010.bin"
private noncomputable def ep010101_11 : Blocks := edgeBlocks% "full/vectors/010101-E-0011.bin"
private noncomputable def ep010101_12 : Blocks := edgeBlocks% "full/vectors/010101-E-0012.bin"
private noncomputable def ep010101_13 : Blocks := edgeBlocks% "full/vectors/010101-E-0013.bin"
private noncomputable def ep010101_14 : Blocks := edgeBlocks% "full/vectors/010101-E-0014.bin"
private noncomputable def ep010101_15 : Blocks := edgeBlocks% "full/vectors/010101-E-0015.bin"
private noncomputable def ep010101_16 : Blocks := edgeBlocks% "full/vectors/010101-E-0016.bin"
private noncomputable def ep010101_17 : Blocks := edgeBlocks% "full/vectors/010101-E-0017.bin"
private noncomputable def ep010101_18 : Blocks := edgeBlocks% "full/vectors/010101-E-0018.bin"
private noncomputable def ep010101_19 : Blocks := edgeBlocks% "full/vectors/010101-E-0019.bin"
private noncomputable def ep010101_20 : Blocks := edgeBlocks% "full/vectors/010101-E-0020.bin"
private noncomputable def ep010101_21 : Blocks := edgeBlocks% "full/vectors/010101-E-0021.bin"
private noncomputable def ep010101_22 : Blocks := edgeBlocks% "full/vectors/010101-E-0022.bin"
private noncomputable def ep010101_23 : Blocks := edgeBlocks% "full/vectors/010101-E-0023.bin"
private noncomputable def ep010101_24 : Blocks := edgeBlocks% "full/vectors/010101-E-0024.bin"
private noncomputable def ep010101_25 : Blocks := edgeBlocks% "full/vectors/010101-E-0025.bin"
private noncomputable def ep010101_26 : Blocks := edgeBlocks% "full/vectors/010101-E-0026.bin"
private noncomputable def ep010101_27 : Blocks := edgeBlocks% "full/vectors/010101-E-0027.bin"
private noncomputable def ep010101_28 : Blocks := edgeBlocks% "full/vectors/010101-E-0028.bin"
private noncomputable def ep010101_29 : Blocks := edgeBlocks% "full/vectors/010101-E-0029.bin"
private noncomputable def ep010101_30 : Blocks := edgeBlocks% "full/vectors/010101-E-0030.bin"
private noncomputable def ep010101_31 : Blocks := edgeBlocks% "full/vectors/010101-E-0031.bin"
private noncomputable def ep010101_32 : Blocks := edgeBlocks% "full/vectors/010101-E-0032.bin"
private noncomputable def ep010101_33 : Blocks := edgeBlocks% "full/vectors/010101-E-0033.bin"
private noncomputable def ep010101_34 : Blocks := edgeBlocks% "full/vectors/010101-E-0034.bin"
private noncomputable def ep010101_35 : Blocks := edgeBlocks% "full/vectors/010101-E-0035.bin"
private noncomputable def ep010101_36 : Blocks := edgeBlocks% "full/vectors/010101-E-0036.bin"
noncomputable def ep010101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep010101_0 ep010101_1) (Blocks.join ep010101_2 ep010101_3)) (Blocks.join (Blocks.join ep010101_4 ep010101_5) (Blocks.join ep010101_6 (Blocks.join ep010101_7 ep010101_8)))) (Blocks.join (Blocks.join (Blocks.join ep010101_9 ep010101_10) (Blocks.join ep010101_11 ep010101_12)) (Blocks.join (Blocks.join ep010101_13 ep010101_14) (Blocks.join ep010101_15 (Blocks.join ep010101_16 ep010101_17))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep010101_18 ep010101_19) (Blocks.join ep010101_20 ep010101_21)) (Blocks.join (Blocks.join ep010101_22 ep010101_23) (Blocks.join ep010101_24 (Blocks.join ep010101_25 ep010101_26)))) (Blocks.join (Blocks.join (Blocks.join ep010101_27 ep010101_28) (Blocks.join ep010101_29 (Blocks.join ep010101_30 ep010101_31))) (Blocks.join (Blocks.join ep010101_32 ep010101_33) (Blocks.join ep010101_34 (Blocks.join ep010101_35 ep010101_36))))))
private def ptsp010101 : List ℤ := [((2:ℤ)^2594+0),((2:ℤ)^2594+1),((2:ℤ)^2594+2)]
private theorem boundp010101 : 2^vp01010.size*absSum vp01010.list + ((2:ℤ)^5365*absSum vp010101.list+absSum ep010101.list) < (2:ℤ)^7298 := by decide +kernel
private theorem pointp010101_0 : fastHom 1 ((2:ℤ)^2594+0) vp01010 = ((2:ℤ)^5365)*vp010101.subst ((2:ℤ)^2594+0)+ep010101.subst ((2:ℤ)^2594+0) := by decide +kernel
private theorem pointp010101_1 : fastHom 1 ((2:ℤ)^2594+1) vp01010 = ((2:ℤ)^5365)*vp010101.subst ((2:ℤ)^2594+1)+ep010101.subst ((2:ℤ)^2594+1) := by decide +kernel
private theorem pointp010101_2 : fastHom 1 ((2:ℤ)^2594+2) vp01010 = ((2:ℤ)^5365)*vp010101.subst ((2:ℤ)^2594+2)+ep010101.subst ((2:ℤ)^2594+2) := by decide +kernel
private theorem checkp010101 (x:ℤ) (hx:x ∈ ptsp010101) : fastHom 1 x vp01010 = ((2:ℤ)^5365)*vp010101.subst x+ep010101.subst x := by
  simp only [ptsp010101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp010101_0
  · exact pointp010101_1
  · exact pointp010101_2
private theorem idp010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010.list =
    C ((2:ℤ)^5365) * horner X vp010101.list + horner X ep010101.list := by
  apply edge_identity (B := (2:ℤ)^7298) (by decide) (by positivity) (by positivity) boundp010101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp010101 (by decide +kernel)
  · have h : ptsp010101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp010101.trans_le (by decide +kernel)
  · exact checkp010101
private theorem bp010101 : Branch 1 (-2559761639/256000000 : ℚ) vp01010 := by
  apply branch_checked idp010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2559761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-2687761639/128000000 : ℚ) by norm_num]
  exact coverp010101
theorem coverp01010 : Covers (-2559761639/256000000 : ℚ) vp01010 := join_branches bp010100 bp010101
end NextProof.EdgeFull

