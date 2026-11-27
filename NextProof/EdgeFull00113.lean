import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00112

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp010010111111_0 : Blocks := edgeBlocks% "full/vectors/010010111111-V-0000.bin"
noncomputable def vp010010111111 : Blocks := vp010010111111_0
theorem coverp010010111111 : Covers (-2429761639/2000000 : ℚ) vp010010111111 := cover_leaf (by decide +kernel)
private noncomputable def vp010010111110_0 : Blocks := edgeBlocks% "full/vectors/010010111110-V-0000.bin"
noncomputable def vp010010111110 : Blocks := vp010010111110_0
theorem coverp010010111110 : Covers (-2427761639/2000000 : ℚ) vp010010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001011111_0 : Blocks := edgeBlocks% "full/vectors/01001011111-V-0000.bin"
noncomputable def vp01001011111 : Blocks := vp01001011111_0
private theorem bp010010111110 : Branch 0 (-2427761639/4000000 : ℚ) vp01001011111 := by
  apply branch_left_normalized (c:=vp010010111110) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2427761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2427761639/2000000 : ℚ) by norm_num]
  exact coverp010010111110
private noncomputable def ep010010111111_0 : Blocks := edgeBlocks% "full/vectors/010010111111-E-0000.bin"
noncomputable def ep010010111111 : Blocks := ep010010111111_0
private theorem idp010010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001011111.list =
    C ((2:ℤ)^113) * horner X vp010010111111.list + horner X ep010010111111.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010111111 : Branch 1 (-2427761639/4000000 : ℚ) vp01001011111 := by
  apply branch_checked idp010010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2427761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2429761639/2000000 : ℚ) by norm_num]
  exact coverp010010111111
theorem coverp01001011111 : Covers (-2427761639/4000000 : ℚ) vp01001011111 := join_branches bp010010111110 bp010010111111
private noncomputable def vp010010111101_0 : Blocks := edgeBlocks% "full/vectors/010010111101-V-0000.bin"
noncomputable def vp010010111101 : Blocks := vp010010111101_0
theorem coverp010010111101 : Covers (-2425761639/2000000 : ℚ) vp010010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp010010111100_0 : Blocks := edgeBlocks% "full/vectors/010010111100-V-0000.bin"
noncomputable def vp010010111100 : Blocks := vp010010111100_0
theorem coverp010010111100 : Covers (-2423761639/2000000 : ℚ) vp010010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001011110_0 : Blocks := edgeBlocks% "full/vectors/01001011110-V-0000.bin"
noncomputable def vp01001011110 : Blocks := vp01001011110_0
private theorem bp010010111100 : Branch 0 (-2423761639/4000000 : ℚ) vp01001011110 := by
  apply branch_left_normalized (c:=vp010010111100) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2423761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2423761639/2000000 : ℚ) by norm_num]
  exact coverp010010111100
private noncomputable def ep010010111101_0 : Blocks := edgeBlocks% "full/vectors/010010111101-E-0000.bin"
noncomputable def ep010010111101 : Blocks := ep010010111101_0
private theorem idp010010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001011110.list =
    C ((2:ℤ)^114) * horner X vp010010111101.list + horner X ep010010111101.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010111101 : Branch 1 (-2423761639/4000000 : ℚ) vp01001011110 := by
  apply branch_checked idp010010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2423761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2425761639/2000000 : ℚ) by norm_num]
  exact coverp010010111101
theorem coverp01001011110 : Covers (-2423761639/4000000 : ℚ) vp01001011110 := join_branches bp010010111100 bp010010111101
private noncomputable def vp0100101111_0 : Blocks := edgeBlocks% "full/vectors/0100101111-V-0000.bin"
private noncomputable def vp0100101111_1 : Blocks := edgeBlocks% "full/vectors/0100101111-V-0001.bin"
noncomputable def vp0100101111 : Blocks := (Blocks.join vp0100101111_0 vp0100101111_1)
private theorem bp01001011110 : Branch 0 (-2423761639/8000000 : ℚ) vp0100101111 := by
  apply branch_left_normalized (c:=vp01001011110) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-2423761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2423761639/4000000 : ℚ) by norm_num]
  exact coverp01001011110
private noncomputable def ep01001011111_0 : Blocks := edgeBlocks% "full/vectors/01001011111-E-0000.bin"
private noncomputable def ep01001011111_1 : Blocks := edgeBlocks% "full/vectors/01001011111-E-0001.bin"
noncomputable def ep01001011111 : Blocks := (Blocks.join ep01001011111_0 ep01001011111_1)
private theorem idp01001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100101111.list =
    C ((2:ℤ)^206) * horner X vp01001011111.list + horner X ep01001011111.list := by
  exact edge_identity (B := (2:ℤ)^368) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001011111 : Branch 1 (-2423761639/8000000 : ℚ) vp0100101111 := by
  apply branch_checked idp01001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2423761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2427761639/4000000 : ℚ) by norm_num]
  exact coverp01001011111
theorem coverp0100101111 : Covers (-2423761639/8000000 : ℚ) vp0100101111 := join_branches bp01001011110 bp01001011111
private noncomputable def vp010010111011_0 : Blocks := edgeBlocks% "full/vectors/010010111011-V-0000.bin"
noncomputable def vp010010111011 : Blocks := vp010010111011_0
theorem coverp010010111011 : Covers (-2421761639/2000000 : ℚ) vp010010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp010010111010_0 : Blocks := edgeBlocks% "full/vectors/010010111010-V-0000.bin"
noncomputable def vp010010111010 : Blocks := vp010010111010_0
theorem coverp010010111010 : Covers (-2419761639/2000000 : ℚ) vp010010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001011101_0 : Blocks := edgeBlocks% "full/vectors/01001011101-V-0000.bin"
noncomputable def vp01001011101 : Blocks := vp01001011101_0
private theorem bp010010111010 : Branch 0 (-2419761639/4000000 : ℚ) vp01001011101 := by
  apply branch_left_normalized (c:=vp010010111010) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2419761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2419761639/2000000 : ℚ) by norm_num]
  exact coverp010010111010
private noncomputable def ep010010111011_0 : Blocks := edgeBlocks% "full/vectors/010010111011-E-0000.bin"
noncomputable def ep010010111011 : Blocks := ep010010111011_0
private theorem idp010010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001011101.list =
    C ((2:ℤ)^114) * horner X vp010010111011.list + horner X ep010010111011.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010111011 : Branch 1 (-2419761639/4000000 : ℚ) vp01001011101 := by
  apply branch_checked idp010010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2419761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2421761639/2000000 : ℚ) by norm_num]
  exact coverp010010111011
theorem coverp01001011101 : Covers (-2419761639/4000000 : ℚ) vp01001011101 := join_branches bp010010111010 bp010010111011
private noncomputable def vp010010111001_0 : Blocks := edgeBlocks% "full/vectors/010010111001-V-0000.bin"
noncomputable def vp010010111001 : Blocks := vp010010111001_0
theorem coverp010010111001 : Covers (-2417761639/2000000 : ℚ) vp010010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp010010111000_0 : Blocks := edgeBlocks% "full/vectors/010010111000-V-0000.bin"
noncomputable def vp010010111000 : Blocks := vp010010111000_0
theorem coverp010010111000 : Covers (-2415761639/2000000 : ℚ) vp010010111000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001011100_0 : Blocks := edgeBlocks% "full/vectors/01001011100-V-0000.bin"
noncomputable def vp01001011100 : Blocks := vp01001011100_0
private theorem bp010010111000 : Branch 0 (-2415761639/4000000 : ℚ) vp01001011100 := by
  apply branch_left_normalized (c:=vp010010111000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2415761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2415761639/2000000 : ℚ) by norm_num]
  exact coverp010010111000
private noncomputable def ep010010111001_0 : Blocks := edgeBlocks% "full/vectors/010010111001-E-0000.bin"
noncomputable def ep010010111001 : Blocks := ep010010111001_0
private theorem idp010010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001011100.list =
    C ((2:ℤ)^114) * horner X vp010010111001.list + horner X ep010010111001.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010111001 : Branch 1 (-2415761639/4000000 : ℚ) vp01001011100 := by
  apply branch_checked idp010010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2415761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2417761639/2000000 : ℚ) by norm_num]
  exact coverp010010111001
theorem coverp01001011100 : Covers (-2415761639/4000000 : ℚ) vp01001011100 := join_branches bp010010111000 bp010010111001
private noncomputable def vp0100101110_0 : Blocks := edgeBlocks% "full/vectors/0100101110-V-0000.bin"
private noncomputable def vp0100101110_1 : Blocks := edgeBlocks% "full/vectors/0100101110-V-0001.bin"
noncomputable def vp0100101110 : Blocks := (Blocks.join vp0100101110_0 vp0100101110_1)
private theorem bp01001011100 : Branch 0 (-2415761639/8000000 : ℚ) vp0100101110 := by
  apply branch_left_normalized (c:=vp01001011100) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-2415761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2415761639/4000000 : ℚ) by norm_num]
  exact coverp01001011100
private noncomputable def ep01001011101_0 : Blocks := edgeBlocks% "full/vectors/01001011101-E-0000.bin"
private noncomputable def ep01001011101_1 : Blocks := edgeBlocks% "full/vectors/01001011101-E-0001.bin"
noncomputable def ep01001011101 : Blocks := (Blocks.join ep01001011101_0 ep01001011101_1)
private theorem idp01001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100101110.list =
    C ((2:ℤ)^206) * horner X vp01001011101.list + horner X ep01001011101.list := by
  exact edge_identity (B := (2:ℤ)^369) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001011101 : Branch 1 (-2415761639/8000000 : ℚ) vp0100101110 := by
  apply branch_checked idp01001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2415761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2419761639/4000000 : ℚ) by norm_num]
  exact coverp01001011101
theorem coverp0100101110 : Covers (-2415761639/8000000 : ℚ) vp0100101110 := join_branches bp01001011100 bp01001011101
private noncomputable def vp010010111_0 : Blocks := edgeBlocks% "full/vectors/010010111-V-0000.bin"
private noncomputable def vp010010111_1 : Blocks := edgeBlocks% "full/vectors/010010111-V-0001.bin"
private noncomputable def vp010010111_2 : Blocks := edgeBlocks% "full/vectors/010010111-V-0002.bin"
noncomputable def vp010010111 : Blocks := (Blocks.join vp010010111_0 (Blocks.join vp010010111_1 vp010010111_2))
private theorem bp0100101110 : Branch 0 (-2415761639/16000000 : ℚ) vp010010111 := by
  apply branch_left_normalized (c:=vp0100101110) (k:=0) (m:=182) (by decide +kernel)
  rw [show 2*(-2415761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2415761639/8000000 : ℚ) by norm_num]
  exact coverp0100101110
private noncomputable def ep0100101111_0 : Blocks := edgeBlocks% "full/vectors/0100101111-E-0000.bin"
private noncomputable def ep0100101111_1 : Blocks := edgeBlocks% "full/vectors/0100101111-E-0001.bin"
private noncomputable def ep0100101111_2 : Blocks := edgeBlocks% "full/vectors/0100101111-E-0002.bin"
noncomputable def ep0100101111 : Blocks := (Blocks.join ep0100101111_0 (Blocks.join ep0100101111_1 ep0100101111_2))
private theorem idp0100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010010111.list =
    C ((2:ℤ)^388) * horner X vp0100101111.list + horner X ep0100101111.list := by
  exact edge_identity (B := (2:ℤ)^613) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100101111 : Branch 1 (-2415761639/16000000 : ℚ) vp010010111 := by
  apply branch_checked idp0100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2415761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2423761639/8000000 : ℚ) by norm_num]
  exact coverp0100101111
theorem coverp010010111 : Covers (-2415761639/16000000 : ℚ) vp010010111 := join_branches bp0100101110 bp0100101111
private noncomputable def vp010010110111_0 : Blocks := edgeBlocks% "full/vectors/010010110111-V-0000.bin"
noncomputable def vp010010110111 : Blocks := vp010010110111_0
theorem coverp010010110111 : Covers (-2413761639/2000000 : ℚ) vp010010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp010010110110_0 : Blocks := edgeBlocks% "full/vectors/010010110110-V-0000.bin"
noncomputable def vp010010110110 : Blocks := vp010010110110_0
theorem coverp010010110110 : Covers (-2411761639/2000000 : ℚ) vp010010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001011011_0 : Blocks := edgeBlocks% "full/vectors/01001011011-V-0000.bin"
noncomputable def vp01001011011 : Blocks := vp01001011011_0
private theorem bp010010110110 : Branch 0 (-2411761639/4000000 : ℚ) vp01001011011 := by
  apply branch_left_normalized (c:=vp010010110110) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2411761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2411761639/2000000 : ℚ) by norm_num]
  exact coverp010010110110
private noncomputable def ep010010110111_0 : Blocks := edgeBlocks% "full/vectors/010010110111-E-0000.bin"
noncomputable def ep010010110111 : Blocks := ep010010110111_0
private theorem idp010010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001011011.list =
    C ((2:ℤ)^114) * horner X vp010010110111.list + horner X ep010010110111.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010110111 : Branch 1 (-2411761639/4000000 : ℚ) vp01001011011 := by
  apply branch_checked idp010010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2411761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2413761639/2000000 : ℚ) by norm_num]
  exact coverp010010110111
theorem coverp01001011011 : Covers (-2411761639/4000000 : ℚ) vp01001011011 := join_branches bp010010110110 bp010010110111
private noncomputable def vp010010110101_0 : Blocks := edgeBlocks% "full/vectors/010010110101-V-0000.bin"
noncomputable def vp010010110101 : Blocks := vp010010110101_0
theorem coverp010010110101 : Covers (-2409761639/2000000 : ℚ) vp010010110101 := cover_leaf (by decide +kernel)
private noncomputable def vp010010110100_0 : Blocks := edgeBlocks% "full/vectors/010010110100-V-0000.bin"
noncomputable def vp010010110100 : Blocks := vp010010110100_0
theorem coverp010010110100 : Covers (-2407761639/2000000 : ℚ) vp010010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001011010_0 : Blocks := edgeBlocks% "full/vectors/01001011010-V-0000.bin"
noncomputable def vp01001011010 : Blocks := vp01001011010_0
private theorem bp010010110100 : Branch 0 (-2407761639/4000000 : ℚ) vp01001011010 := by
  apply branch_left_normalized (c:=vp010010110100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2407761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2407761639/2000000 : ℚ) by norm_num]
  exact coverp010010110100
private noncomputable def ep010010110101_0 : Blocks := edgeBlocks% "full/vectors/010010110101-E-0000.bin"
noncomputable def ep010010110101 : Blocks := ep010010110101_0
private theorem idp010010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001011010.list =
    C ((2:ℤ)^114) * horner X vp010010110101.list + horner X ep010010110101.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010110101 : Branch 1 (-2407761639/4000000 : ℚ) vp01001011010 := by
  apply branch_checked idp010010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2407761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2409761639/2000000 : ℚ) by norm_num]
  exact coverp010010110101
theorem coverp01001011010 : Covers (-2407761639/4000000 : ℚ) vp01001011010 := join_branches bp010010110100 bp010010110101
private noncomputable def vp0100101101_0 : Blocks := edgeBlocks% "full/vectors/0100101101-V-0000.bin"
private noncomputable def vp0100101101_1 : Blocks := edgeBlocks% "full/vectors/0100101101-V-0001.bin"
noncomputable def vp0100101101 : Blocks := (Blocks.join vp0100101101_0 vp0100101101_1)
private theorem bp01001011010 : Branch 0 (-2407761639/8000000 : ℚ) vp0100101101 := by
  apply branch_left_normalized (c:=vp01001011010) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-2407761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2407761639/4000000 : ℚ) by norm_num]
  exact coverp01001011010
private noncomputable def ep01001011011_0 : Blocks := edgeBlocks% "full/vectors/01001011011-E-0000.bin"
private noncomputable def ep01001011011_1 : Blocks := edgeBlocks% "full/vectors/01001011011-E-0001.bin"
noncomputable def ep01001011011 : Blocks := (Blocks.join ep01001011011_0 ep01001011011_1)
private theorem idp01001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100101101.list =
    C ((2:ℤ)^206) * horner X vp01001011011.list + horner X ep01001011011.list := by
  exact edge_identity (B := (2:ℤ)^369) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001011011 : Branch 1 (-2407761639/8000000 : ℚ) vp0100101101 := by
  apply branch_checked idp01001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2407761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2411761639/4000000 : ℚ) by norm_num]
  exact coverp01001011011
theorem coverp0100101101 : Covers (-2407761639/8000000 : ℚ) vp0100101101 := join_branches bp01001011010 bp01001011011
private noncomputable def vp010010110011_0 : Blocks := edgeBlocks% "full/vectors/010010110011-V-0000.bin"
noncomputable def vp010010110011 : Blocks := vp010010110011_0
theorem coverp010010110011 : Covers (-2405761639/2000000 : ℚ) vp010010110011 := cover_leaf (by decide +kernel)
private noncomputable def vp010010110010_0 : Blocks := edgeBlocks% "full/vectors/010010110010-V-0000.bin"
noncomputable def vp010010110010 : Blocks := vp010010110010_0
theorem coverp010010110010 : Covers (-2403761639/2000000 : ℚ) vp010010110010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001011001_0 : Blocks := edgeBlocks% "full/vectors/01001011001-V-0000.bin"
noncomputable def vp01001011001 : Blocks := vp01001011001_0
private theorem bp010010110010 : Branch 0 (-2403761639/4000000 : ℚ) vp01001011001 := by
  apply branch_left_normalized (c:=vp010010110010) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2403761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2403761639/2000000 : ℚ) by norm_num]
  exact coverp010010110010
private noncomputable def ep010010110011_0 : Blocks := edgeBlocks% "full/vectors/010010110011-E-0000.bin"
noncomputable def ep010010110011 : Blocks := ep010010110011_0
private theorem idp010010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001011001.list =
    C ((2:ℤ)^113) * horner X vp010010110011.list + horner X ep010010110011.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010110011 : Branch 1 (-2403761639/4000000 : ℚ) vp01001011001 := by
  apply branch_checked idp010010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2403761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2405761639/2000000 : ℚ) by norm_num]
  exact coverp010010110011
theorem coverp01001011001 : Covers (-2403761639/4000000 : ℚ) vp01001011001 := join_branches bp010010110010 bp010010110011
private noncomputable def vp010010110001_0 : Blocks := edgeBlocks% "full/vectors/010010110001-V-0000.bin"
noncomputable def vp010010110001 : Blocks := vp010010110001_0
theorem coverp010010110001 : Covers (-2401761639/2000000 : ℚ) vp010010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp010010110000_0 : Blocks := edgeBlocks% "full/vectors/010010110000-V-0000.bin"
noncomputable def vp010010110000 : Blocks := vp010010110000_0
theorem coverp010010110000 : Covers (-2399761639/2000000 : ℚ) vp010010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001011000_0 : Blocks := edgeBlocks% "full/vectors/01001011000-V-0000.bin"
noncomputable def vp01001011000 : Blocks := vp01001011000_0
private theorem bp010010110000 : Branch 0 (-2399761639/4000000 : ℚ) vp01001011000 := by
  apply branch_left_normalized (c:=vp010010110000) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2399761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2399761639/2000000 : ℚ) by norm_num]
  exact coverp010010110000
private noncomputable def ep010010110001_0 : Blocks := edgeBlocks% "full/vectors/010010110001-E-0000.bin"
noncomputable def ep010010110001 : Blocks := ep010010110001_0
private theorem idp010010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001011000.list =
    C ((2:ℤ)^113) * horner X vp010010110001.list + horner X ep010010110001.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010110001 : Branch 1 (-2399761639/4000000 : ℚ) vp01001011000 := by
  apply branch_checked idp010010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2399761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2401761639/2000000 : ℚ) by norm_num]
  exact coverp010010110001
theorem coverp01001011000 : Covers (-2399761639/4000000 : ℚ) vp01001011000 := join_branches bp010010110000 bp010010110001
private noncomputable def vp0100101100_0 : Blocks := edgeBlocks% "full/vectors/0100101100-V-0000.bin"
private noncomputable def vp0100101100_1 : Blocks := edgeBlocks% "full/vectors/0100101100-V-0001.bin"
noncomputable def vp0100101100 : Blocks := (Blocks.join vp0100101100_0 vp0100101100_1)
private theorem bp01001011000 : Branch 0 (-2399761639/8000000 : ℚ) vp0100101100 := by
  apply branch_left_normalized (c:=vp01001011000) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-2399761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2399761639/4000000 : ℚ) by norm_num]
  exact coverp01001011000
private noncomputable def ep01001011001_0 : Blocks := edgeBlocks% "full/vectors/01001011001-E-0000.bin"
private noncomputable def ep01001011001_1 : Blocks := edgeBlocks% "full/vectors/01001011001-E-0001.bin"
noncomputable def ep01001011001 : Blocks := (Blocks.join ep01001011001_0 ep01001011001_1)
private theorem idp01001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100101100.list =
    C ((2:ℤ)^206) * horner X vp01001011001.list + horner X ep01001011001.list := by
  exact edge_identity (B := (2:ℤ)^369) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001011001 : Branch 1 (-2399761639/8000000 : ℚ) vp0100101100 := by
  apply branch_checked idp01001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2399761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2403761639/4000000 : ℚ) by norm_num]
  exact coverp01001011001
theorem coverp0100101100 : Covers (-2399761639/8000000 : ℚ) vp0100101100 := join_branches bp01001011000 bp01001011001
private noncomputable def vp010010110_0 : Blocks := edgeBlocks% "full/vectors/010010110-V-0000.bin"
private noncomputable def vp010010110_1 : Blocks := edgeBlocks% "full/vectors/010010110-V-0001.bin"
private noncomputable def vp010010110_2 : Blocks := edgeBlocks% "full/vectors/010010110-V-0002.bin"
noncomputable def vp010010110 : Blocks := (Blocks.join vp010010110_0 (Blocks.join vp010010110_1 vp010010110_2))
private theorem bp0100101100 : Branch 0 (-2399761639/16000000 : ℚ) vp010010110 := by
  apply branch_left_normalized (c:=vp0100101100) (k:=0) (m:=182) (by decide +kernel)
  rw [show 2*(-2399761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2399761639/8000000 : ℚ) by norm_num]
  exact coverp0100101100
private noncomputable def ep0100101101_0 : Blocks := edgeBlocks% "full/vectors/0100101101-E-0000.bin"
private noncomputable def ep0100101101_1 : Blocks := edgeBlocks% "full/vectors/0100101101-E-0001.bin"
private noncomputable def ep0100101101_2 : Blocks := edgeBlocks% "full/vectors/0100101101-E-0002.bin"
noncomputable def ep0100101101 : Blocks := (Blocks.join ep0100101101_0 (Blocks.join ep0100101101_1 ep0100101101_2))
private theorem idp0100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010010110.list =
    C ((2:ℤ)^389) * horner X vp0100101101.list + horner X ep0100101101.list := by
  exact edge_identity (B := (2:ℤ)^614) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100101101 : Branch 1 (-2399761639/16000000 : ℚ) vp010010110 := by
  apply branch_checked idp0100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2399761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2407761639/8000000 : ℚ) by norm_num]
  exact coverp0100101101
theorem coverp010010110 : Covers (-2399761639/16000000 : ℚ) vp010010110 := join_branches bp0100101100 bp0100101101
private noncomputable def vp01001011_0 : Blocks := edgeBlocks% "full/vectors/01001011-V-0000.bin"
private noncomputable def vp01001011_1 : Blocks := edgeBlocks% "full/vectors/01001011-V-0001.bin"
private noncomputable def vp01001011_2 : Blocks := edgeBlocks% "full/vectors/01001011-V-0002.bin"
private noncomputable def vp01001011_3 : Blocks := edgeBlocks% "full/vectors/01001011-V-0003.bin"
private noncomputable def vp01001011_4 : Blocks := edgeBlocks% "full/vectors/01001011-V-0004.bin"
private noncomputable def vp01001011_5 : Blocks := edgeBlocks% "full/vectors/01001011-V-0005.bin"
noncomputable def vp01001011 : Blocks := (Blocks.join (Blocks.join vp01001011_0 (Blocks.join vp01001011_1 vp01001011_2)) (Blocks.join vp01001011_3 (Blocks.join vp01001011_4 vp01001011_5)))
private theorem bp010010110 : Branch 0 (-2399761639/32000000 : ℚ) vp01001011 := by
  apply branch_left_normalized (c:=vp010010110) (k:=0) (m:=342) (by decide +kernel)
  rw [show 2*(-2399761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2399761639/16000000 : ℚ) by norm_num]
  exact coverp010010110
private noncomputable def ep010010111_0 : Blocks := edgeBlocks% "full/vectors/010010111-E-0000.bin"
private noncomputable def ep010010111_1 : Blocks := edgeBlocks% "full/vectors/010010111-E-0001.bin"
private noncomputable def ep010010111_2 : Blocks := edgeBlocks% "full/vectors/010010111-E-0002.bin"
private noncomputable def ep010010111_3 : Blocks := edgeBlocks% "full/vectors/010010111-E-0003.bin"
private noncomputable def ep010010111_4 : Blocks := edgeBlocks% "full/vectors/010010111-E-0004.bin"
private noncomputable def ep010010111_5 : Blocks := edgeBlocks% "full/vectors/010010111-E-0005.bin"
noncomputable def ep010010111 : Blocks := (Blocks.join (Blocks.join ep010010111_0 (Blocks.join ep010010111_1 ep010010111_2)) (Blocks.join ep010010111_3 (Blocks.join ep010010111_4 ep010010111_5)))
private theorem idp010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001011.list =
    C ((2:ℤ)^752) * horner X vp010010111.list + horner X ep010010111.list := by
  exact edge_identity (B := (2:ℤ)^1101) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010111 : Branch 1 (-2399761639/32000000 : ℚ) vp01001011 := by
  apply branch_checked idp010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2399761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2415761639/16000000 : ℚ) by norm_num]
  exact coverp010010111
theorem coverp01001011 : Covers (-2399761639/32000000 : ℚ) vp01001011 := join_branches bp010010110 bp010010111
private noncomputable def vp010010101111_0 : Blocks := edgeBlocks% "full/vectors/010010101111-V-0000.bin"
noncomputable def vp010010101111 : Blocks := vp010010101111_0
theorem coverp010010101111 : Covers (-2397761639/2000000 : ℚ) vp010010101111 := cover_leaf (by decide +kernel)
private noncomputable def vp010010101110_0 : Blocks := edgeBlocks% "full/vectors/010010101110-V-0000.bin"
noncomputable def vp010010101110 : Blocks := vp010010101110_0
theorem coverp010010101110 : Covers (-2395761639/2000000 : ℚ) vp010010101110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001010111_0 : Blocks := edgeBlocks% "full/vectors/01001010111-V-0000.bin"
noncomputable def vp01001010111 : Blocks := vp01001010111_0
private theorem bp010010101110 : Branch 0 (-2395761639/4000000 : ℚ) vp01001010111 := by
  apply branch_left_normalized (c:=vp010010101110) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2395761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2395761639/2000000 : ℚ) by norm_num]
  exact coverp010010101110
private noncomputable def ep010010101111_0 : Blocks := edgeBlocks% "full/vectors/010010101111-E-0000.bin"
noncomputable def ep010010101111 : Blocks := ep010010101111_0
private theorem idp010010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001010111.list =
    C ((2:ℤ)^113) * horner X vp010010101111.list + horner X ep010010101111.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010101111 : Branch 1 (-2395761639/4000000 : ℚ) vp01001010111 := by
  apply branch_checked idp010010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2395761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2397761639/2000000 : ℚ) by norm_num]
  exact coverp010010101111
theorem coverp01001010111 : Covers (-2395761639/4000000 : ℚ) vp01001010111 := join_branches bp010010101110 bp010010101111
private noncomputable def vp010010101101_0 : Blocks := edgeBlocks% "full/vectors/010010101101-V-0000.bin"
noncomputable def vp010010101101 : Blocks := vp010010101101_0
theorem coverp010010101101 : Covers (-2393761639/2000000 : ℚ) vp010010101101 := cover_leaf (by decide +kernel)
private noncomputable def vp010010101100_0 : Blocks := edgeBlocks% "full/vectors/010010101100-V-0000.bin"
noncomputable def vp010010101100 : Blocks := vp010010101100_0
theorem coverp010010101100 : Covers (-2391761639/2000000 : ℚ) vp010010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001010110_0 : Blocks := edgeBlocks% "full/vectors/01001010110-V-0000.bin"
noncomputable def vp01001010110 : Blocks := vp01001010110_0
private theorem bp010010101100 : Branch 0 (-2391761639/4000000 : ℚ) vp01001010110 := by
  apply branch_left_normalized (c:=vp010010101100) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2391761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2391761639/2000000 : ℚ) by norm_num]
  exact coverp010010101100
private noncomputable def ep010010101101_0 : Blocks := edgeBlocks% "full/vectors/010010101101-E-0000.bin"
noncomputable def ep010010101101 : Blocks := ep010010101101_0
private theorem idp010010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001010110.list =
    C ((2:ℤ)^113) * horner X vp010010101101.list + horner X ep010010101101.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010101101 : Branch 1 (-2391761639/4000000 : ℚ) vp01001010110 := by
  apply branch_checked idp010010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2391761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2393761639/2000000 : ℚ) by norm_num]
  exact coverp010010101101
theorem coverp01001010110 : Covers (-2391761639/4000000 : ℚ) vp01001010110 := join_branches bp010010101100 bp010010101101
private noncomputable def vp0100101011_0 : Blocks := edgeBlocks% "full/vectors/0100101011-V-0000.bin"
private noncomputable def vp0100101011_1 : Blocks := edgeBlocks% "full/vectors/0100101011-V-0001.bin"
noncomputable def vp0100101011 : Blocks := (Blocks.join vp0100101011_0 vp0100101011_1)
private theorem bp01001010110 : Branch 0 (-2391761639/8000000 : ℚ) vp0100101011 := by
  apply branch_left_normalized (c:=vp01001010110) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-2391761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2391761639/4000000 : ℚ) by norm_num]
  exact coverp01001010110
private noncomputable def ep01001010111_0 : Blocks := edgeBlocks% "full/vectors/01001010111-E-0000.bin"
private noncomputable def ep01001010111_1 : Blocks := edgeBlocks% "full/vectors/01001010111-E-0001.bin"
noncomputable def ep01001010111 : Blocks := (Blocks.join ep01001010111_0 ep01001010111_1)
private theorem idp01001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100101011.list =
    C ((2:ℤ)^207) * horner X vp01001010111.list + horner X ep01001010111.list := by
  exact edge_identity (B := (2:ℤ)^370) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001010111 : Branch 1 (-2391761639/8000000 : ℚ) vp0100101011 := by
  apply branch_checked idp01001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2391761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2395761639/4000000 : ℚ) by norm_num]
  exact coverp01001010111
theorem coverp0100101011 : Covers (-2391761639/8000000 : ℚ) vp0100101011 := join_branches bp01001010110 bp01001010111
private noncomputable def vp010010101011_0 : Blocks := edgeBlocks% "full/vectors/010010101011-V-0000.bin"
noncomputable def vp010010101011 : Blocks := vp010010101011_0
theorem coverp010010101011 : Covers (-2389761639/2000000 : ℚ) vp010010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp010010101010_0 : Blocks := edgeBlocks% "full/vectors/010010101010-V-0000.bin"
noncomputable def vp010010101010 : Blocks := vp010010101010_0
theorem coverp010010101010 : Covers (-2387761639/2000000 : ℚ) vp010010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001010101_0 : Blocks := edgeBlocks% "full/vectors/01001010101-V-0000.bin"
noncomputable def vp01001010101 : Blocks := vp01001010101_0
private theorem bp010010101010 : Branch 0 (-2387761639/4000000 : ℚ) vp01001010101 := by
  apply branch_left_normalized (c:=vp010010101010) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2387761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2387761639/2000000 : ℚ) by norm_num]
  exact coverp010010101010
private noncomputable def ep010010101011_0 : Blocks := edgeBlocks% "full/vectors/010010101011-E-0000.bin"
noncomputable def ep010010101011 : Blocks := ep010010101011_0
private theorem idp010010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001010101.list =
    C ((2:ℤ)^113) * horner X vp010010101011.list + horner X ep010010101011.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010101011 : Branch 1 (-2387761639/4000000 : ℚ) vp01001010101 := by
  apply branch_checked idp010010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2387761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2389761639/2000000 : ℚ) by norm_num]
  exact coverp010010101011
theorem coverp01001010101 : Covers (-2387761639/4000000 : ℚ) vp01001010101 := join_branches bp010010101010 bp010010101011
private noncomputable def vp010010101001_0 : Blocks := edgeBlocks% "full/vectors/010010101001-V-0000.bin"
noncomputable def vp010010101001 : Blocks := vp010010101001_0
theorem coverp010010101001 : Covers (-2385761639/2000000 : ℚ) vp010010101001 := cover_leaf (by decide +kernel)
private noncomputable def vp010010101000_0 : Blocks := edgeBlocks% "full/vectors/010010101000-V-0000.bin"
noncomputable def vp010010101000 : Blocks := vp010010101000_0
theorem coverp010010101000 : Covers (-2383761639/2000000 : ℚ) vp010010101000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001010100_0 : Blocks := edgeBlocks% "full/vectors/01001010100-V-0000.bin"
noncomputable def vp01001010100 : Blocks := vp01001010100_0
private theorem bp010010101000 : Branch 0 (-2383761639/4000000 : ℚ) vp01001010100 := by
  apply branch_left_normalized (c:=vp010010101000) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2383761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2383761639/2000000 : ℚ) by norm_num]
  exact coverp010010101000
private noncomputable def ep010010101001_0 : Blocks := edgeBlocks% "full/vectors/010010101001-E-0000.bin"
noncomputable def ep010010101001 : Blocks := ep010010101001_0
private theorem idp010010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001010100.list =
    C ((2:ℤ)^113) * horner X vp010010101001.list + horner X ep010010101001.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010101001 : Branch 1 (-2383761639/4000000 : ℚ) vp01001010100 := by
  apply branch_checked idp010010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2383761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2385761639/2000000 : ℚ) by norm_num]
  exact coverp010010101001
theorem coverp01001010100 : Covers (-2383761639/4000000 : ℚ) vp01001010100 := join_branches bp010010101000 bp010010101001
private noncomputable def vp0100101010_0 : Blocks := edgeBlocks% "full/vectors/0100101010-V-0000.bin"
private noncomputable def vp0100101010_1 : Blocks := edgeBlocks% "full/vectors/0100101010-V-0001.bin"
noncomputable def vp0100101010 : Blocks := (Blocks.join vp0100101010_0 vp0100101010_1)
private theorem bp01001010100 : Branch 0 (-2383761639/8000000 : ℚ) vp0100101010 := by
  apply branch_left_normalized (c:=vp01001010100) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-2383761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2383761639/4000000 : ℚ) by norm_num]
  exact coverp01001010100
private noncomputable def ep01001010101_0 : Blocks := edgeBlocks% "full/vectors/01001010101-E-0000.bin"
private noncomputable def ep01001010101_1 : Blocks := edgeBlocks% "full/vectors/01001010101-E-0001.bin"
noncomputable def ep01001010101 : Blocks := (Blocks.join ep01001010101_0 ep01001010101_1)
private theorem idp01001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100101010.list =
    C ((2:ℤ)^207) * horner X vp01001010101.list + horner X ep01001010101.list := by
  exact edge_identity (B := (2:ℤ)^370) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001010101 : Branch 1 (-2383761639/8000000 : ℚ) vp0100101010 := by
  apply branch_checked idp01001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2383761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2387761639/4000000 : ℚ) by norm_num]
  exact coverp01001010101
theorem coverp0100101010 : Covers (-2383761639/8000000 : ℚ) vp0100101010 := join_branches bp01001010100 bp01001010101
private noncomputable def vp010010101_0 : Blocks := edgeBlocks% "full/vectors/010010101-V-0000.bin"
private noncomputable def vp010010101_1 : Blocks := edgeBlocks% "full/vectors/010010101-V-0001.bin"
private noncomputable def vp010010101_2 : Blocks := edgeBlocks% "full/vectors/010010101-V-0002.bin"
noncomputable def vp010010101 : Blocks := (Blocks.join vp010010101_0 (Blocks.join vp010010101_1 vp010010101_2))
private theorem bp0100101010 : Branch 0 (-2383761639/16000000 : ℚ) vp010010101 := by
  apply branch_left_normalized (c:=vp0100101010) (k:=0) (m:=183) (by decide +kernel)
  rw [show 2*(-2383761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2383761639/8000000 : ℚ) by norm_num]
  exact coverp0100101010
private noncomputable def ep0100101011_0 : Blocks := edgeBlocks% "full/vectors/0100101011-E-0000.bin"
private noncomputable def ep0100101011_1 : Blocks := edgeBlocks% "full/vectors/0100101011-E-0001.bin"
private noncomputable def ep0100101011_2 : Blocks := edgeBlocks% "full/vectors/0100101011-E-0002.bin"
noncomputable def ep0100101011 : Blocks := (Blocks.join ep0100101011_0 (Blocks.join ep0100101011_1 ep0100101011_2))
private theorem idp0100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010010101.list =
    C ((2:ℤ)^390) * horner X vp0100101011.list + horner X ep0100101011.list := by
  exact edge_identity (B := (2:ℤ)^615) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100101011 : Branch 1 (-2383761639/16000000 : ℚ) vp010010101 := by
  apply branch_checked idp0100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2383761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2391761639/8000000 : ℚ) by norm_num]
  exact coverp0100101011
theorem coverp010010101 : Covers (-2383761639/16000000 : ℚ) vp010010101 := join_branches bp0100101010 bp0100101011
private noncomputable def vp010010100111_0 : Blocks := edgeBlocks% "full/vectors/010010100111-V-0000.bin"
noncomputable def vp010010100111 : Blocks := vp010010100111_0
theorem coverp010010100111 : Covers (-2381761639/2000000 : ℚ) vp010010100111 := cover_leaf (by decide +kernel)
private noncomputable def vp010010100110_0 : Blocks := edgeBlocks% "full/vectors/010010100110-V-0000.bin"
noncomputable def vp010010100110 : Blocks := vp010010100110_0
theorem coverp010010100110 : Covers (-2379761639/2000000 : ℚ) vp010010100110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001010011_0 : Blocks := edgeBlocks% "full/vectors/01001010011-V-0000.bin"
noncomputable def vp01001010011 : Blocks := vp01001010011_0
private theorem bp010010100110 : Branch 0 (-2379761639/4000000 : ℚ) vp01001010011 := by
  apply branch_left_normalized (c:=vp010010100110) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2379761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2379761639/2000000 : ℚ) by norm_num]
  exact coverp010010100110
private noncomputable def ep010010100111_0 : Blocks := edgeBlocks% "full/vectors/010010100111-E-0000.bin"
noncomputable def ep010010100111 : Blocks := ep010010100111_0
private theorem idp010010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001010011.list =
    C ((2:ℤ)^114) * horner X vp010010100111.list + horner X ep010010100111.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010100111 : Branch 1 (-2379761639/4000000 : ℚ) vp01001010011 := by
  apply branch_checked idp010010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2379761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2381761639/2000000 : ℚ) by norm_num]
  exact coverp010010100111
theorem coverp01001010011 : Covers (-2379761639/4000000 : ℚ) vp01001010011 := join_branches bp010010100110 bp010010100111
private noncomputable def vp010010100101_0 : Blocks := edgeBlocks% "full/vectors/010010100101-V-0000.bin"
noncomputable def vp010010100101 : Blocks := vp010010100101_0
theorem coverp010010100101 : Covers (-2377761639/2000000 : ℚ) vp010010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp010010100100_0 : Blocks := edgeBlocks% "full/vectors/010010100100-V-0000.bin"
noncomputable def vp010010100100 : Blocks := vp010010100100_0
theorem coverp010010100100 : Covers (-2375761639/2000000 : ℚ) vp010010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001010010_0 : Blocks := edgeBlocks% "full/vectors/01001010010-V-0000.bin"
noncomputable def vp01001010010 : Blocks := vp01001010010_0
private theorem bp010010100100 : Branch 0 (-2375761639/4000000 : ℚ) vp01001010010 := by
  apply branch_left_normalized (c:=vp010010100100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2375761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2375761639/2000000 : ℚ) by norm_num]
  exact coverp010010100100
private noncomputable def ep010010100101_0 : Blocks := edgeBlocks% "full/vectors/010010100101-E-0000.bin"
noncomputable def ep010010100101 : Blocks := ep010010100101_0
private theorem idp010010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001010010.list =
    C ((2:ℤ)^113) * horner X vp010010100101.list + horner X ep010010100101.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010100101 : Branch 1 (-2375761639/4000000 : ℚ) vp01001010010 := by
  apply branch_checked idp010010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2375761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2377761639/2000000 : ℚ) by norm_num]
  exact coverp010010100101
theorem coverp01001010010 : Covers (-2375761639/4000000 : ℚ) vp01001010010 := join_branches bp010010100100 bp010010100101
private noncomputable def vp0100101001_0 : Blocks := edgeBlocks% "full/vectors/0100101001-V-0000.bin"
private noncomputable def vp0100101001_1 : Blocks := edgeBlocks% "full/vectors/0100101001-V-0001.bin"
noncomputable def vp0100101001 : Blocks := (Blocks.join vp0100101001_0 vp0100101001_1)
private theorem bp01001010010 : Branch 0 (-2375761639/8000000 : ℚ) vp0100101001 := by
  apply branch_left_normalized (c:=vp01001010010) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-2375761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2375761639/4000000 : ℚ) by norm_num]
  exact coverp01001010010
private noncomputable def ep01001010011_0 : Blocks := edgeBlocks% "full/vectors/01001010011-E-0000.bin"
private noncomputable def ep01001010011_1 : Blocks := edgeBlocks% "full/vectors/01001010011-E-0001.bin"
noncomputable def ep01001010011 : Blocks := (Blocks.join ep01001010011_0 ep01001010011_1)
private theorem idp01001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100101001.list =
    C ((2:ℤ)^205) * horner X vp01001010011.list + horner X ep01001010011.list := by
  exact edge_identity (B := (2:ℤ)^369) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001010011 : Branch 1 (-2375761639/8000000 : ℚ) vp0100101001 := by
  apply branch_checked idp01001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2375761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2379761639/4000000 : ℚ) by norm_num]
  exact coverp01001010011
theorem coverp0100101001 : Covers (-2375761639/8000000 : ℚ) vp0100101001 := join_branches bp01001010010 bp01001010011
private noncomputable def vp010010100011_0 : Blocks := edgeBlocks% "full/vectors/010010100011-V-0000.bin"
noncomputable def vp010010100011 : Blocks := vp010010100011_0
theorem coverp010010100011 : Covers (-2373761639/2000000 : ℚ) vp010010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp010010100010_0 : Blocks := edgeBlocks% "full/vectors/010010100010-V-0000.bin"
noncomputable def vp010010100010 : Blocks := vp010010100010_0
theorem coverp010010100010 : Covers (-2371761639/2000000 : ℚ) vp010010100010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001010001_0 : Blocks := edgeBlocks% "full/vectors/01001010001-V-0000.bin"
noncomputable def vp01001010001 : Blocks := vp01001010001_0
private theorem bp010010100010 : Branch 0 (-2371761639/4000000 : ℚ) vp01001010001 := by
  apply branch_left_normalized (c:=vp010010100010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2371761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2371761639/2000000 : ℚ) by norm_num]
  exact coverp010010100010
private noncomputable def ep010010100011_0 : Blocks := edgeBlocks% "full/vectors/010010100011-E-0000.bin"
noncomputable def ep010010100011 : Blocks := ep010010100011_0
private theorem idp010010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001010001.list =
    C ((2:ℤ)^113) * horner X vp010010100011.list + horner X ep010010100011.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010100011 : Branch 1 (-2371761639/4000000 : ℚ) vp01001010001 := by
  apply branch_checked idp010010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2371761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2373761639/2000000 : ℚ) by norm_num]
  exact coverp010010100011
theorem coverp01001010001 : Covers (-2371761639/4000000 : ℚ) vp01001010001 := join_branches bp010010100010 bp010010100011
private noncomputable def vp010010100001_0 : Blocks := edgeBlocks% "full/vectors/010010100001-V-0000.bin"
noncomputable def vp010010100001 : Blocks := vp010010100001_0
theorem coverp010010100001 : Covers (-2369761639/2000000 : ℚ) vp010010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp010010100000_0 : Blocks := edgeBlocks% "full/vectors/010010100000-V-0000.bin"
noncomputable def vp010010100000 : Blocks := vp010010100000_0
theorem coverp010010100000 : Covers (-2367761639/2000000 : ℚ) vp010010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001010000_0 : Blocks := edgeBlocks% "full/vectors/01001010000-V-0000.bin"
noncomputable def vp01001010000 : Blocks := vp01001010000_0
private theorem bp010010100000 : Branch 0 (-2367761639/4000000 : ℚ) vp01001010000 := by
  apply branch_left_normalized (c:=vp010010100000) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2367761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2367761639/2000000 : ℚ) by norm_num]
  exact coverp010010100000
private noncomputable def ep010010100001_0 : Blocks := edgeBlocks% "full/vectors/010010100001-E-0000.bin"
noncomputable def ep010010100001 : Blocks := ep010010100001_0
private theorem idp010010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001010000.list =
    C ((2:ℤ)^114) * horner X vp010010100001.list + horner X ep010010100001.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010100001 : Branch 1 (-2367761639/4000000 : ℚ) vp01001010000 := by
  apply branch_checked idp010010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2367761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2369761639/2000000 : ℚ) by norm_num]
  exact coverp010010100001
theorem coverp01001010000 : Covers (-2367761639/4000000 : ℚ) vp01001010000 := join_branches bp010010100000 bp010010100001
private noncomputable def vp0100101000_0 : Blocks := edgeBlocks% "full/vectors/0100101000-V-0000.bin"
private noncomputable def vp0100101000_1 : Blocks := edgeBlocks% "full/vectors/0100101000-V-0001.bin"
noncomputable def vp0100101000 : Blocks := (Blocks.join vp0100101000_0 vp0100101000_1)
private theorem bp01001010000 : Branch 0 (-2367761639/8000000 : ℚ) vp0100101000 := by
  apply branch_left_normalized (c:=vp01001010000) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-2367761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2367761639/4000000 : ℚ) by norm_num]
  exact coverp01001010000
private noncomputable def ep01001010001_0 : Blocks := edgeBlocks% "full/vectors/01001010001-E-0000.bin"
private noncomputable def ep01001010001_1 : Blocks := edgeBlocks% "full/vectors/01001010001-E-0001.bin"
noncomputable def ep01001010001 : Blocks := (Blocks.join ep01001010001_0 ep01001010001_1)
private theorem idp01001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100101000.list =
    C ((2:ℤ)^208) * horner X vp01001010001.list + horner X ep01001010001.list := by
  exact edge_identity (B := (2:ℤ)^370) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001010001 : Branch 1 (-2367761639/8000000 : ℚ) vp0100101000 := by
  apply branch_checked idp01001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2367761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2371761639/4000000 : ℚ) by norm_num]
  exact coverp01001010001
theorem coverp0100101000 : Covers (-2367761639/8000000 : ℚ) vp0100101000 := join_branches bp01001010000 bp01001010001
private noncomputable def vp010010100_0 : Blocks := edgeBlocks% "full/vectors/010010100-V-0000.bin"
private noncomputable def vp010010100_1 : Blocks := edgeBlocks% "full/vectors/010010100-V-0001.bin"
private noncomputable def vp010010100_2 : Blocks := edgeBlocks% "full/vectors/010010100-V-0002.bin"
noncomputable def vp010010100 : Blocks := (Blocks.join vp010010100_0 (Blocks.join vp010010100_1 vp010010100_2))
private theorem bp0100101000 : Branch 0 (-2367761639/16000000 : ℚ) vp010010100 := by
  apply branch_left_normalized (c:=vp0100101000) (k:=0) (m:=183) (by decide +kernel)
  rw [show 2*(-2367761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2367761639/8000000 : ℚ) by norm_num]
  exact coverp0100101000
private noncomputable def ep0100101001_0 : Blocks := edgeBlocks% "full/vectors/0100101001-E-0000.bin"
private noncomputable def ep0100101001_1 : Blocks := edgeBlocks% "full/vectors/0100101001-E-0001.bin"
private noncomputable def ep0100101001_2 : Blocks := edgeBlocks% "full/vectors/0100101001-E-0002.bin"
noncomputable def ep0100101001 : Blocks := (Blocks.join ep0100101001_0 (Blocks.join ep0100101001_1 ep0100101001_2))
private theorem idp0100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010010100.list =
    C ((2:ℤ)^391) * horner X vp0100101001.list + horner X ep0100101001.list := by
  exact edge_identity (B := (2:ℤ)^617) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100101001 : Branch 1 (-2367761639/16000000 : ℚ) vp010010100 := by
  apply branch_checked idp0100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2367761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2375761639/8000000 : ℚ) by norm_num]
  exact coverp0100101001
theorem coverp010010100 : Covers (-2367761639/16000000 : ℚ) vp010010100 := join_branches bp0100101000 bp0100101001
private noncomputable def vp01001010_0 : Blocks := edgeBlocks% "full/vectors/01001010-V-0000.bin"
private noncomputable def vp01001010_1 : Blocks := edgeBlocks% "full/vectors/01001010-V-0001.bin"
private noncomputable def vp01001010_2 : Blocks := edgeBlocks% "full/vectors/01001010-V-0002.bin"
private noncomputable def vp01001010_3 : Blocks := edgeBlocks% "full/vectors/01001010-V-0003.bin"
private noncomputable def vp01001010_4 : Blocks := edgeBlocks% "full/vectors/01001010-V-0004.bin"
private noncomputable def vp01001010_5 : Blocks := edgeBlocks% "full/vectors/01001010-V-0005.bin"
noncomputable def vp01001010 : Blocks := (Blocks.join (Blocks.join vp01001010_0 (Blocks.join vp01001010_1 vp01001010_2)) (Blocks.join vp01001010_3 (Blocks.join vp01001010_4 vp01001010_5)))
private theorem bp010010100 : Branch 0 (-2367761639/32000000 : ℚ) vp01001010 := by
  apply branch_left_normalized (c:=vp010010100) (k:=0) (m:=344) (by decide +kernel)
  rw [show 2*(-2367761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2367761639/16000000 : ℚ) by norm_num]
  exact coverp010010100
private noncomputable def ep010010101_0 : Blocks := edgeBlocks% "full/vectors/010010101-E-0000.bin"
private noncomputable def ep010010101_1 : Blocks := edgeBlocks% "full/vectors/010010101-E-0001.bin"
private noncomputable def ep010010101_2 : Blocks := edgeBlocks% "full/vectors/010010101-E-0002.bin"
private noncomputable def ep010010101_3 : Blocks := edgeBlocks% "full/vectors/010010101-E-0003.bin"
private noncomputable def ep010010101_4 : Blocks := edgeBlocks% "full/vectors/010010101-E-0004.bin"
private noncomputable def ep010010101_5 : Blocks := edgeBlocks% "full/vectors/010010101-E-0005.bin"
noncomputable def ep010010101 : Blocks := (Blocks.join (Blocks.join ep010010101_0 (Blocks.join ep010010101_1 ep010010101_2)) (Blocks.join ep010010101_3 (Blocks.join ep010010101_4 ep010010101_5)))
private theorem idp010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001010.list =
    C ((2:ℤ)^756) * horner X vp010010101.list + horner X ep010010101.list := by
  exact edge_identity (B := (2:ℤ)^1106) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010101 : Branch 1 (-2367761639/32000000 : ℚ) vp01001010 := by
  apply branch_checked idp010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2367761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2383761639/16000000 : ℚ) by norm_num]
  exact coverp010010101
theorem coverp01001010 : Covers (-2367761639/32000000 : ℚ) vp01001010 := join_branches bp010010100 bp010010101
private noncomputable def vp0100101_0 : Blocks := edgeBlocks% "full/vectors/0100101-V-0000.bin"
private noncomputable def vp0100101_1 : Blocks := edgeBlocks% "full/vectors/0100101-V-0001.bin"
private noncomputable def vp0100101_2 : Blocks := edgeBlocks% "full/vectors/0100101-V-0002.bin"
private noncomputable def vp0100101_3 : Blocks := edgeBlocks% "full/vectors/0100101-V-0003.bin"
private noncomputable def vp0100101_4 : Blocks := edgeBlocks% "full/vectors/0100101-V-0004.bin"
private noncomputable def vp0100101_5 : Blocks := edgeBlocks% "full/vectors/0100101-V-0005.bin"
private noncomputable def vp0100101_6 : Blocks := edgeBlocks% "full/vectors/0100101-V-0006.bin"
private noncomputable def vp0100101_7 : Blocks := edgeBlocks% "full/vectors/0100101-V-0007.bin"
private noncomputable def vp0100101_8 : Blocks := edgeBlocks% "full/vectors/0100101-V-0008.bin"
private noncomputable def vp0100101_9 : Blocks := edgeBlocks% "full/vectors/0100101-V-0009.bin"
private noncomputable def vp0100101_10 : Blocks := edgeBlocks% "full/vectors/0100101-V-0010.bin"
noncomputable def vp0100101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0100101_0 vp0100101_1) (Blocks.join vp0100101_2 (Blocks.join vp0100101_3 vp0100101_4))) (Blocks.join (Blocks.join vp0100101_5 (Blocks.join vp0100101_6 vp0100101_7)) (Blocks.join vp0100101_8 (Blocks.join vp0100101_9 vp0100101_10))))
private theorem bp01001010 : Branch 0 (-2367761639/64000000 : ℚ) vp0100101 := by
  apply branch_left_normalized (c:=vp01001010) (k:=0) (m:=663) (by decide +kernel)
  rw [show 2*(-2367761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2367761639/32000000 : ℚ) by norm_num]
  exact coverp01001010
private noncomputable def ep01001011_0 : Blocks := edgeBlocks% "full/vectors/01001011-E-0000.bin"
private noncomputable def ep01001011_1 : Blocks := edgeBlocks% "full/vectors/01001011-E-0001.bin"
private noncomputable def ep01001011_2 : Blocks := edgeBlocks% "full/vectors/01001011-E-0002.bin"
private noncomputable def ep01001011_3 : Blocks := edgeBlocks% "full/vectors/01001011-E-0003.bin"
private noncomputable def ep01001011_4 : Blocks := edgeBlocks% "full/vectors/01001011-E-0004.bin"
private noncomputable def ep01001011_5 : Blocks := edgeBlocks% "full/vectors/01001011-E-0005.bin"
private noncomputable def ep01001011_6 : Blocks := edgeBlocks% "full/vectors/01001011-E-0006.bin"
private noncomputable def ep01001011_7 : Blocks := edgeBlocks% "full/vectors/01001011-E-0007.bin"
private noncomputable def ep01001011_8 : Blocks := edgeBlocks% "full/vectors/01001011-E-0008.bin"
private noncomputable def ep01001011_9 : Blocks := edgeBlocks% "full/vectors/01001011-E-0009.bin"
private noncomputable def ep01001011_10 : Blocks := edgeBlocks% "full/vectors/01001011-E-0010.bin"
noncomputable def ep01001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01001011_0 ep01001011_1) (Blocks.join ep01001011_2 (Blocks.join ep01001011_3 ep01001011_4))) (Blocks.join (Blocks.join ep01001011_5 (Blocks.join ep01001011_6 ep01001011_7)) (Blocks.join ep01001011_8 (Blocks.join ep01001011_9 ep01001011_10))))
private theorem idp01001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100101.list =
    C ((2:ℤ)^1476) * horner X vp01001011.list + horner X ep01001011.list := by
  exact edge_identity (B := (2:ℤ)^2074) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001011 : Branch 1 (-2367761639/64000000 : ℚ) vp0100101 := by
  apply branch_checked idp01001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2367761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2399761639/32000000 : ℚ) by norm_num]
  exact coverp01001011
theorem coverp0100101 : Covers (-2367761639/64000000 : ℚ) vp0100101 := join_branches bp01001010 bp01001011
private noncomputable def vp010010011111_0 : Blocks := edgeBlocks% "full/vectors/010010011111-V-0000.bin"
noncomputable def vp010010011111 : Blocks := vp010010011111_0
theorem coverp010010011111 : Covers (-2365761639/2000000 : ℚ) vp010010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp010010011110_0 : Blocks := edgeBlocks% "full/vectors/010010011110-V-0000.bin"
noncomputable def vp010010011110 : Blocks := vp010010011110_0
theorem coverp010010011110 : Covers (-2363761639/2000000 : ℚ) vp010010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001001111_0 : Blocks := edgeBlocks% "full/vectors/01001001111-V-0000.bin"
noncomputable def vp01001001111 : Blocks := vp01001001111_0
private theorem bp010010011110 : Branch 0 (-2363761639/4000000 : ℚ) vp01001001111 := by
  apply branch_left_normalized (c:=vp010010011110) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2363761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2363761639/2000000 : ℚ) by norm_num]
  exact coverp010010011110
private noncomputable def ep010010011111_0 : Blocks := edgeBlocks% "full/vectors/010010011111-E-0000.bin"
noncomputable def ep010010011111 : Blocks := ep010010011111_0
private theorem idp010010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001001111.list =
    C ((2:ℤ)^113) * horner X vp010010011111.list + horner X ep010010011111.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010011111 : Branch 1 (-2363761639/4000000 : ℚ) vp01001001111 := by
  apply branch_checked idp010010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2363761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2365761639/2000000 : ℚ) by norm_num]
  exact coverp010010011111
theorem coverp01001001111 : Covers (-2363761639/4000000 : ℚ) vp01001001111 := join_branches bp010010011110 bp010010011111
private noncomputable def vp010010011101_0 : Blocks := edgeBlocks% "full/vectors/010010011101-V-0000.bin"
noncomputable def vp010010011101 : Blocks := vp010010011101_0
theorem coverp010010011101 : Covers (-2361761639/2000000 : ℚ) vp010010011101 := cover_leaf (by decide +kernel)
private noncomputable def vp010010011100_0 : Blocks := edgeBlocks% "full/vectors/010010011100-V-0000.bin"
noncomputable def vp010010011100 : Blocks := vp010010011100_0
theorem coverp010010011100 : Covers (-2359761639/2000000 : ℚ) vp010010011100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001001110_0 : Blocks := edgeBlocks% "full/vectors/01001001110-V-0000.bin"
noncomputable def vp01001001110 : Blocks := vp01001001110_0
private theorem bp010010011100 : Branch 0 (-2359761639/4000000 : ℚ) vp01001001110 := by
  apply branch_left_normalized (c:=vp010010011100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2359761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2359761639/2000000 : ℚ) by norm_num]
  exact coverp010010011100
private noncomputable def ep010010011101_0 : Blocks := edgeBlocks% "full/vectors/010010011101-E-0000.bin"
noncomputable def ep010010011101 : Blocks := ep010010011101_0
private theorem idp010010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001001110.list =
    C ((2:ℤ)^112) * horner X vp010010011101.list + horner X ep010010011101.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010011101 : Branch 1 (-2359761639/4000000 : ℚ) vp01001001110 := by
  apply branch_checked idp010010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2359761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2361761639/2000000 : ℚ) by norm_num]
  exact coverp010010011101
theorem coverp01001001110 : Covers (-2359761639/4000000 : ℚ) vp01001001110 := join_branches bp010010011100 bp010010011101
private noncomputable def vp0100100111_0 : Blocks := edgeBlocks% "full/vectors/0100100111-V-0000.bin"
private noncomputable def vp0100100111_1 : Blocks := edgeBlocks% "full/vectors/0100100111-V-0001.bin"
noncomputable def vp0100100111 : Blocks := (Blocks.join vp0100100111_0 vp0100100111_1)
private theorem bp01001001110 : Branch 0 (-2359761639/8000000 : ℚ) vp0100100111 := by
  apply branch_left_normalized (c:=vp01001001110) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-2359761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2359761639/4000000 : ℚ) by norm_num]
  exact coverp01001001110
private noncomputable def ep01001001111_0 : Blocks := edgeBlocks% "full/vectors/01001001111-E-0000.bin"
private noncomputable def ep01001001111_1 : Blocks := edgeBlocks% "full/vectors/01001001111-E-0001.bin"
noncomputable def ep01001001111 : Blocks := (Blocks.join ep01001001111_0 ep01001001111_1)
private theorem idp01001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100100111.list =
    C ((2:ℤ)^205) * horner X vp01001001111.list + horner X ep01001001111.list := by
  exact edge_identity (B := (2:ℤ)^368) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001001111 : Branch 1 (-2359761639/8000000 : ℚ) vp0100100111 := by
  apply branch_checked idp01001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2359761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2363761639/4000000 : ℚ) by norm_num]
  exact coverp01001001111
theorem coverp0100100111 : Covers (-2359761639/8000000 : ℚ) vp0100100111 := join_branches bp01001001110 bp01001001111
private noncomputable def vp010010011011_0 : Blocks := edgeBlocks% "full/vectors/010010011011-V-0000.bin"
noncomputable def vp010010011011 : Blocks := vp010010011011_0
theorem coverp010010011011 : Covers (-2357761639/2000000 : ℚ) vp010010011011 := cover_leaf (by decide +kernel)
private noncomputable def vp010010011010_0 : Blocks := edgeBlocks% "full/vectors/010010011010-V-0000.bin"
noncomputable def vp010010011010 : Blocks := vp010010011010_0
theorem coverp010010011010 : Covers (-2355761639/2000000 : ℚ) vp010010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001001101_0 : Blocks := edgeBlocks% "full/vectors/01001001101-V-0000.bin"
noncomputable def vp01001001101 : Blocks := vp01001001101_0
private theorem bp010010011010 : Branch 0 (-2355761639/4000000 : ℚ) vp01001001101 := by
  apply branch_left_normalized (c:=vp010010011010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2355761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2355761639/2000000 : ℚ) by norm_num]
  exact coverp010010011010
private noncomputable def ep010010011011_0 : Blocks := edgeBlocks% "full/vectors/010010011011-E-0000.bin"
noncomputable def ep010010011011 : Blocks := ep010010011011_0
private theorem idp010010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001001101.list =
    C ((2:ℤ)^113) * horner X vp010010011011.list + horner X ep010010011011.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010011011 : Branch 1 (-2355761639/4000000 : ℚ) vp01001001101 := by
  apply branch_checked idp010010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2355761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2357761639/2000000 : ℚ) by norm_num]
  exact coverp010010011011
theorem coverp01001001101 : Covers (-2355761639/4000000 : ℚ) vp01001001101 := join_branches bp010010011010 bp010010011011
private noncomputable def vp010010011001_0 : Blocks := edgeBlocks% "full/vectors/010010011001-V-0000.bin"
noncomputable def vp010010011001 : Blocks := vp010010011001_0
theorem coverp010010011001 : Covers (-2353761639/2000000 : ℚ) vp010010011001 := cover_leaf (by decide +kernel)
private noncomputable def vp010010011000_0 : Blocks := edgeBlocks% "full/vectors/010010011000-V-0000.bin"
noncomputable def vp010010011000 : Blocks := vp010010011000_0
theorem coverp010010011000 : Covers (-2351761639/2000000 : ℚ) vp010010011000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001001100_0 : Blocks := edgeBlocks% "full/vectors/01001001100-V-0000.bin"
noncomputable def vp01001001100 : Blocks := vp01001001100_0
private theorem bp010010011000 : Branch 0 (-2351761639/4000000 : ℚ) vp01001001100 := by
  apply branch_left_normalized (c:=vp010010011000) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2351761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2351761639/2000000 : ℚ) by norm_num]
  exact coverp010010011000
private noncomputable def ep010010011001_0 : Blocks := edgeBlocks% "full/vectors/010010011001-E-0000.bin"
noncomputable def ep010010011001 : Blocks := ep010010011001_0
private theorem idp010010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001001100.list =
    C ((2:ℤ)^116) * horner X vp010010011001.list + horner X ep010010011001.list := by
  exact edge_identity (B := (2:ℤ)^247) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010011001 : Branch 1 (-2351761639/4000000 : ℚ) vp01001001100 := by
  apply branch_checked idp010010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2351761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2353761639/2000000 : ℚ) by norm_num]
  exact coverp010010011001
theorem coverp01001001100 : Covers (-2351761639/4000000 : ℚ) vp01001001100 := join_branches bp010010011000 bp010010011001
private noncomputable def vp0100100110_0 : Blocks := edgeBlocks% "full/vectors/0100100110-V-0000.bin"
private noncomputable def vp0100100110_1 : Blocks := edgeBlocks% "full/vectors/0100100110-V-0001.bin"
noncomputable def vp0100100110 : Blocks := (Blocks.join vp0100100110_0 vp0100100110_1)
private theorem bp01001001100 : Branch 0 (-2351761639/8000000 : ℚ) vp0100100110 := by
  apply branch_left_normalized (c:=vp01001001100) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-2351761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2351761639/4000000 : ℚ) by norm_num]
  exact coverp01001001100
private noncomputable def ep01001001101_0 : Blocks := edgeBlocks% "full/vectors/01001001101-E-0000.bin"
private noncomputable def ep01001001101_1 : Blocks := edgeBlocks% "full/vectors/01001001101-E-0001.bin"
noncomputable def ep01001001101 : Blocks := (Blocks.join ep01001001101_0 ep01001001101_1)
private theorem idp01001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100100110.list =
    C ((2:ℤ)^210) * horner X vp01001001101.list + horner X ep01001001101.list := by
  exact edge_identity (B := (2:ℤ)^372) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001001101 : Branch 1 (-2351761639/8000000 : ℚ) vp0100100110 := by
  apply branch_checked idp01001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2351761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2355761639/4000000 : ℚ) by norm_num]
  exact coverp01001001101
theorem coverp0100100110 : Covers (-2351761639/8000000 : ℚ) vp0100100110 := join_branches bp01001001100 bp01001001101
private noncomputable def vp010010011_0 : Blocks := edgeBlocks% "full/vectors/010010011-V-0000.bin"
private noncomputable def vp010010011_1 : Blocks := edgeBlocks% "full/vectors/010010011-V-0001.bin"
private noncomputable def vp010010011_2 : Blocks := edgeBlocks% "full/vectors/010010011-V-0002.bin"
noncomputable def vp010010011 : Blocks := (Blocks.join vp010010011_0 (Blocks.join vp010010011_1 vp010010011_2))
private theorem bp0100100110 : Branch 0 (-2351761639/16000000 : ℚ) vp010010011 := by
  apply branch_left_normalized (c:=vp0100100110) (k:=0) (m:=184) (by decide +kernel)
  rw [show 2*(-2351761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2351761639/8000000 : ℚ) by norm_num]
  exact coverp0100100110
private noncomputable def ep0100100111_0 : Blocks := edgeBlocks% "full/vectors/0100100111-E-0000.bin"
private noncomputable def ep0100100111_1 : Blocks := edgeBlocks% "full/vectors/0100100111-E-0001.bin"
private noncomputable def ep0100100111_2 : Blocks := edgeBlocks% "full/vectors/0100100111-E-0002.bin"
noncomputable def ep0100100111 : Blocks := (Blocks.join ep0100100111_0 (Blocks.join ep0100100111_1 ep0100100111_2))
private theorem idp0100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010010011.list =
    C ((2:ℤ)^395) * horner X vp0100100111.list + horner X ep0100100111.list := by
  exact edge_identity (B := (2:ℤ)^620) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100100111 : Branch 1 (-2351761639/16000000 : ℚ) vp010010011 := by
  apply branch_checked idp0100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2351761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2359761639/8000000 : ℚ) by norm_num]
  exact coverp0100100111
theorem coverp010010011 : Covers (-2351761639/16000000 : ℚ) vp010010011 := join_branches bp0100100110 bp0100100111
private noncomputable def vp010010010111_0 : Blocks := edgeBlocks% "full/vectors/010010010111-V-0000.bin"
noncomputable def vp010010010111 : Blocks := vp010010010111_0
theorem coverp010010010111 : Covers (-2349761639/2000000 : ℚ) vp010010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp010010010110_0 : Blocks := edgeBlocks% "full/vectors/010010010110-V-0000.bin"
noncomputable def vp010010010110 : Blocks := vp010010010110_0
theorem coverp010010010110 : Covers (-2347761639/2000000 : ℚ) vp010010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001001011_0 : Blocks := edgeBlocks% "full/vectors/01001001011-V-0000.bin"
noncomputable def vp01001001011 : Blocks := vp01001001011_0
private theorem bp010010010110 : Branch 0 (-2347761639/4000000 : ℚ) vp01001001011 := by
  apply branch_left_normalized (c:=vp010010010110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2347761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2347761639/2000000 : ℚ) by norm_num]
  exact coverp010010010110
private noncomputable def ep010010010111_0 : Blocks := edgeBlocks% "full/vectors/010010010111-E-0000.bin"
noncomputable def ep010010010111 : Blocks := ep010010010111_0
private theorem idp010010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001001011.list =
    C ((2:ℤ)^110) * horner X vp010010010111.list + horner X ep010010010111.list := by
  exact edge_identity (B := (2:ℤ)^240) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010010111 : Branch 1 (-2347761639/4000000 : ℚ) vp01001001011 := by
  apply branch_checked idp010010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2347761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2349761639/2000000 : ℚ) by norm_num]
  exact coverp010010010111
theorem coverp01001001011 : Covers (-2347761639/4000000 : ℚ) vp01001001011 := join_branches bp010010010110 bp010010010111
private noncomputable def vp010010010101_0 : Blocks := edgeBlocks% "full/vectors/010010010101-V-0000.bin"
noncomputable def vp010010010101 : Blocks := vp010010010101_0
theorem coverp010010010101 : Covers (-2345761639/2000000 : ℚ) vp010010010101 := cover_leaf (by decide +kernel)
private noncomputable def vp010010010100_0 : Blocks := edgeBlocks% "full/vectors/010010010100-V-0000.bin"
noncomputable def vp010010010100 : Blocks := vp010010010100_0
theorem coverp010010010100 : Covers (-2343761639/2000000 : ℚ) vp010010010100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001001010_0 : Blocks := edgeBlocks% "full/vectors/01001001010-V-0000.bin"
noncomputable def vp01001001010 : Blocks := vp01001001010_0
private theorem bp010010010100 : Branch 0 (-2343761639/4000000 : ℚ) vp01001001010 := by
  apply branch_left_normalized (c:=vp010010010100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2343761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2343761639/2000000 : ℚ) by norm_num]
  exact coverp010010010100
private noncomputable def ep010010010101_0 : Blocks := edgeBlocks% "full/vectors/010010010101-E-0000.bin"
noncomputable def ep010010010101 : Blocks := ep010010010101_0
private theorem idp010010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001001010.list =
    C ((2:ℤ)^110) * horner X vp010010010101.list + horner X ep010010010101.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010010101 : Branch 1 (-2343761639/4000000 : ℚ) vp01001001010 := by
  apply branch_checked idp010010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2343761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2345761639/2000000 : ℚ) by norm_num]
  exact coverp010010010101
theorem coverp01001001010 : Covers (-2343761639/4000000 : ℚ) vp01001001010 := join_branches bp010010010100 bp010010010101
private noncomputable def vp0100100101_0 : Blocks := edgeBlocks% "full/vectors/0100100101-V-0000.bin"
private noncomputable def vp0100100101_1 : Blocks := edgeBlocks% "full/vectors/0100100101-V-0001.bin"
noncomputable def vp0100100101 : Blocks := (Blocks.join vp0100100101_0 vp0100100101_1)
private theorem bp01001001010 : Branch 0 (-2343761639/8000000 : ℚ) vp0100100101 := by
  apply branch_left_normalized (c:=vp01001001010) (k:=0) (m:=98) (by decide +kernel)
  rw [show 2*(-2343761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2343761639/4000000 : ℚ) by norm_num]
  exact coverp01001001010
private noncomputable def ep01001001011_0 : Blocks := edgeBlocks% "full/vectors/01001001011-E-0000.bin"
private noncomputable def ep01001001011_1 : Blocks := edgeBlocks% "full/vectors/01001001011-E-0001.bin"
noncomputable def ep01001001011 : Blocks := (Blocks.join ep01001001011_0 ep01001001011_1)
private theorem idp01001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100100101.list =
    C ((2:ℤ)^202) * horner X vp01001001011.list + horner X ep01001001011.list := by
  exact edge_identity (B := (2:ℤ)^361) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001001011 : Branch 1 (-2343761639/8000000 : ℚ) vp0100100101 := by
  apply branch_checked idp01001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2343761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2347761639/4000000 : ℚ) by norm_num]
  exact coverp01001001011
theorem coverp0100100101 : Covers (-2343761639/8000000 : ℚ) vp0100100101 := join_branches bp01001001010 bp01001001011
private noncomputable def vp010010010011_0 : Blocks := edgeBlocks% "full/vectors/010010010011-V-0000.bin"
noncomputable def vp010010010011 : Blocks := vp010010010011_0
theorem coverp010010010011 : Covers (-2341761639/2000000 : ℚ) vp010010010011 := cover_leaf (by decide +kernel)
private noncomputable def vp010010010010_0 : Blocks := edgeBlocks% "full/vectors/010010010010-V-0000.bin"
noncomputable def vp010010010010 : Blocks := vp010010010010_0
theorem coverp010010010010 : Covers (-2339761639/2000000 : ℚ) vp010010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001001001_0 : Blocks := edgeBlocks% "full/vectors/01001001001-V-0000.bin"
noncomputable def vp01001001001 : Blocks := vp01001001001_0
private theorem bp010010010010 : Branch 0 (-2339761639/4000000 : ℚ) vp01001001001 := by
  apply branch_left_normalized (c:=vp010010010010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2339761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2339761639/2000000 : ℚ) by norm_num]
  exact coverp010010010010
private noncomputable def ep010010010011_0 : Blocks := edgeBlocks% "full/vectors/010010010011-E-0000.bin"
noncomputable def ep010010010011 : Blocks := ep010010010011_0
private theorem idp010010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001001001.list =
    C ((2:ℤ)^109) * horner X vp010010010011.list + horner X ep010010010011.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010010011 : Branch 1 (-2339761639/4000000 : ℚ) vp01001001001 := by
  apply branch_checked idp010010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2339761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2341761639/2000000 : ℚ) by norm_num]
  exact coverp010010010011
theorem coverp01001001001 : Covers (-2339761639/4000000 : ℚ) vp01001001001 := join_branches bp010010010010 bp010010010011
private noncomputable def vp01001001000_0 : Blocks := edgeBlocks% "full/vectors/01001001000-V-0000.bin"
noncomputable def vp01001001000 : Blocks := vp01001001000_0
theorem coverp01001001000 : Covers (-2335761639/4000000 : ℚ) vp01001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0100100100_0 : Blocks := edgeBlocks% "full/vectors/0100100100-V-0000.bin"
private noncomputable def vp0100100100_1 : Blocks := edgeBlocks% "full/vectors/0100100100-V-0001.bin"
noncomputable def vp0100100100 : Blocks := (Blocks.join vp0100100100_0 vp0100100100_1)
private theorem bp01001001000 : Branch 0 (-2335761639/8000000 : ℚ) vp0100100100 := by
  apply branch_left_normalized (c:=vp01001001000) (k:=0) (m:=97) (by decide +kernel)
  rw [show 2*(-2335761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2335761639/4000000 : ℚ) by norm_num]
  exact coverp01001001000
private noncomputable def ep01001001001_0 : Blocks := edgeBlocks% "full/vectors/01001001001-E-0000.bin"
private noncomputable def ep01001001001_1 : Blocks := edgeBlocks% "full/vectors/01001001001-E-0001.bin"
noncomputable def ep01001001001 : Blocks := (Blocks.join ep01001001001_0 ep01001001001_1)
private theorem idp01001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100100100.list =
    C ((2:ℤ)^201) * horner X vp01001001001.list + horner X ep01001001001.list := by
  exact edge_identity (B := (2:ℤ)^357) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001001001 : Branch 1 (-2335761639/8000000 : ℚ) vp0100100100 := by
  apply branch_checked idp01001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2335761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2339761639/4000000 : ℚ) by norm_num]
  exact coverp01001001001
theorem coverp0100100100 : Covers (-2335761639/8000000 : ℚ) vp0100100100 := join_branches bp01001001000 bp01001001001
private noncomputable def vp010010010_0 : Blocks := edgeBlocks% "full/vectors/010010010-V-0000.bin"
private noncomputable def vp010010010_1 : Blocks := edgeBlocks% "full/vectors/010010010-V-0001.bin"
private noncomputable def vp010010010_2 : Blocks := edgeBlocks% "full/vectors/010010010-V-0002.bin"
noncomputable def vp010010010 : Blocks := (Blocks.join vp010010010_0 (Blocks.join vp010010010_1 vp010010010_2))
private theorem bp0100100100 : Branch 0 (-2335761639/16000000 : ℚ) vp010010010 := by
  apply branch_left_normalized (c:=vp0100100100) (k:=0) (m:=178) (by decide +kernel)
  rw [show 2*(-2335761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2335761639/8000000 : ℚ) by norm_num]
  exact coverp0100100100
private noncomputable def ep0100100101_0 : Blocks := edgeBlocks% "full/vectors/0100100101-E-0000.bin"
private noncomputable def ep0100100101_1 : Blocks := edgeBlocks% "full/vectors/0100100101-E-0001.bin"
private noncomputable def ep0100100101_2 : Blocks := edgeBlocks% "full/vectors/0100100101-E-0002.bin"
noncomputable def ep0100100101 : Blocks := (Blocks.join ep0100100101_0 (Blocks.join ep0100100101_1 ep0100100101_2))
private theorem idp0100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010010010.list =
    C ((2:ℤ)^385) * horner X vp0100100101.list + horner X ep0100100101.list := by
  exact edge_identity (B := (2:ℤ)^605) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100100101 : Branch 1 (-2335761639/16000000 : ℚ) vp010010010 := by
  apply branch_checked idp0100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2335761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2343761639/8000000 : ℚ) by norm_num]
  exact coverp0100100101
theorem coverp010010010 : Covers (-2335761639/16000000 : ℚ) vp010010010 := join_branches bp0100100100 bp0100100101
private noncomputable def vp01001001_0 : Blocks := edgeBlocks% "full/vectors/01001001-V-0000.bin"
private noncomputable def vp01001001_1 : Blocks := edgeBlocks% "full/vectors/01001001-V-0001.bin"
private noncomputable def vp01001001_2 : Blocks := edgeBlocks% "full/vectors/01001001-V-0002.bin"
private noncomputable def vp01001001_3 : Blocks := edgeBlocks% "full/vectors/01001001-V-0003.bin"
private noncomputable def vp01001001_4 : Blocks := edgeBlocks% "full/vectors/01001001-V-0004.bin"
private noncomputable def vp01001001_5 : Blocks := edgeBlocks% "full/vectors/01001001-V-0005.bin"
noncomputable def vp01001001 : Blocks := (Blocks.join (Blocks.join vp01001001_0 (Blocks.join vp01001001_1 vp01001001_2)) (Blocks.join vp01001001_3 (Blocks.join vp01001001_4 vp01001001_5)))
private theorem bp010010010 : Branch 0 (-2335761639/32000000 : ℚ) vp01001001 := by
  apply branch_left_normalized (c:=vp010010010) (k:=0) (m:=340) (by decide +kernel)
  rw [show 2*(-2335761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2335761639/16000000 : ℚ) by norm_num]
  exact coverp010010010
private noncomputable def ep010010011_0 : Blocks := edgeBlocks% "full/vectors/010010011-E-0000.bin"
private noncomputable def ep010010011_1 : Blocks := edgeBlocks% "full/vectors/010010011-E-0001.bin"
private noncomputable def ep010010011_2 : Blocks := edgeBlocks% "full/vectors/010010011-E-0002.bin"
private noncomputable def ep010010011_3 : Blocks := edgeBlocks% "full/vectors/010010011-E-0003.bin"
private noncomputable def ep010010011_4 : Blocks := edgeBlocks% "full/vectors/010010011-E-0004.bin"
private noncomputable def ep010010011_5 : Blocks := edgeBlocks% "full/vectors/010010011-E-0005.bin"
noncomputable def ep010010011 : Blocks := (Blocks.join (Blocks.join ep010010011_0 (Blocks.join ep010010011_1 ep010010011_2)) (Blocks.join ep010010011_3 (Blocks.join ep010010011_4 ep010010011_5)))
private theorem idp010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001001.list =
    C ((2:ℤ)^745) * horner X vp010010011.list + horner X ep010010011.list := by
  exact edge_identity (B := (2:ℤ)^1098) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010011 : Branch 1 (-2335761639/32000000 : ℚ) vp01001001 := by
  apply branch_checked idp010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2335761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2351761639/16000000 : ℚ) by norm_num]
  exact coverp010010011
theorem coverp01001001 : Covers (-2335761639/32000000 : ℚ) vp01001001 := join_branches bp010010010 bp010010011
private noncomputable def vp01001000111_0 : Blocks := edgeBlocks% "full/vectors/01001000111-V-0000.bin"
noncomputable def vp01001000111 : Blocks := vp01001000111_0
theorem coverp01001000111 : Covers (-2331761639/4000000 : ℚ) vp01001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp01001000110_0 : Blocks := edgeBlocks% "full/vectors/01001000110-V-0000.bin"
noncomputable def vp01001000110 : Blocks := vp01001000110_0
theorem coverp01001000110 : Covers (-2327761639/4000000 : ℚ) vp01001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0100100011_0 : Blocks := edgeBlocks% "full/vectors/0100100011-V-0000.bin"
private noncomputable def vp0100100011_1 : Blocks := edgeBlocks% "full/vectors/0100100011-V-0001.bin"
noncomputable def vp0100100011 : Blocks := (Blocks.join vp0100100011_0 vp0100100011_1)
private theorem bp01001000110 : Branch 0 (-2327761639/8000000 : ℚ) vp0100100011 := by
  apply branch_left_normalized (c:=vp01001000110) (k:=0) (m:=97) (by decide +kernel)
  rw [show 2*(-2327761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2327761639/4000000 : ℚ) by norm_num]
  exact coverp01001000110
private noncomputable def ep01001000111_0 : Blocks := edgeBlocks% "full/vectors/01001000111-E-0000.bin"
private noncomputable def ep01001000111_1 : Blocks := edgeBlocks% "full/vectors/01001000111-E-0001.bin"
noncomputable def ep01001000111 : Blocks := (Blocks.join ep01001000111_0 ep01001000111_1)
private theorem idp01001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100100011.list =
    C ((2:ℤ)^202) * horner X vp01001000111.list + horner X ep01001000111.list := by
  exact edge_identity (B := (2:ℤ)^357) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001000111 : Branch 1 (-2327761639/8000000 : ℚ) vp0100100011 := by
  apply branch_checked idp01001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2327761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2331761639/4000000 : ℚ) by norm_num]
  exact coverp01001000111
theorem coverp0100100011 : Covers (-2327761639/8000000 : ℚ) vp0100100011 := join_branches bp01001000110 bp01001000111
private noncomputable def vp01001000101_0 : Blocks := edgeBlocks% "full/vectors/01001000101-V-0000.bin"
noncomputable def vp01001000101 : Blocks := vp01001000101_0
theorem coverp01001000101 : Covers (-2323761639/4000000 : ℚ) vp01001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp01001000100_0 : Blocks := edgeBlocks% "full/vectors/01001000100-V-0000.bin"
noncomputable def vp01001000100 : Blocks := vp01001000100_0
theorem coverp01001000100 : Covers (-2319761639/4000000 : ℚ) vp01001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0100100010_0 : Blocks := edgeBlocks% "full/vectors/0100100010-V-0000.bin"
private noncomputable def vp0100100010_1 : Blocks := edgeBlocks% "full/vectors/0100100010-V-0001.bin"
noncomputable def vp0100100010 : Blocks := (Blocks.join vp0100100010_0 vp0100100010_1)
private theorem bp01001000100 : Branch 0 (-2319761639/8000000 : ℚ) vp0100100010 := by
  apply branch_left_normalized (c:=vp01001000100) (k:=0) (m:=98) (by decide +kernel)
  rw [show 2*(-2319761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2319761639/4000000 : ℚ) by norm_num]
  exact coverp01001000100
private noncomputable def ep01001000101_0 : Blocks := edgeBlocks% "full/vectors/01001000101-E-0000.bin"
private noncomputable def ep01001000101_1 : Blocks := edgeBlocks% "full/vectors/01001000101-E-0001.bin"
noncomputable def ep01001000101 : Blocks := (Blocks.join ep01001000101_0 ep01001000101_1)
private theorem idp01001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100100010.list =
    C ((2:ℤ)^203) * horner X vp01001000101.list + horner X ep01001000101.list := by
  exact edge_identity (B := (2:ℤ)^358) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001000101 : Branch 1 (-2319761639/8000000 : ℚ) vp0100100010 := by
  apply branch_checked idp01001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2319761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2323761639/4000000 : ℚ) by norm_num]
  exact coverp01001000101
theorem coverp0100100010 : Covers (-2319761639/8000000 : ℚ) vp0100100010 := join_branches bp01001000100 bp01001000101
private noncomputable def vp010010001_0 : Blocks := edgeBlocks% "full/vectors/010010001-V-0000.bin"
private noncomputable def vp010010001_1 : Blocks := edgeBlocks% "full/vectors/010010001-V-0001.bin"
private noncomputable def vp010010001_2 : Blocks := edgeBlocks% "full/vectors/010010001-V-0002.bin"
noncomputable def vp010010001 : Blocks := (Blocks.join vp010010001_0 (Blocks.join vp010010001_1 vp010010001_2))
private theorem bp0100100010 : Branch 0 (-2319761639/16000000 : ℚ) vp010010001 := by
  apply branch_left_normalized (c:=vp0100100010) (k:=0) (m:=179) (by decide +kernel)
  rw [show 2*(-2319761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2319761639/8000000 : ℚ) by norm_num]
  exact coverp0100100010
private noncomputable def ep0100100011_0 : Blocks := edgeBlocks% "full/vectors/0100100011-E-0000.bin"
private noncomputable def ep0100100011_1 : Blocks := edgeBlocks% "full/vectors/0100100011-E-0001.bin"
private noncomputable def ep0100100011_2 : Blocks := edgeBlocks% "full/vectors/0100100011-E-0002.bin"
noncomputable def ep0100100011 : Blocks := (Blocks.join ep0100100011_0 (Blocks.join ep0100100011_1 ep0100100011_2))
private theorem idp0100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010010001.list =
    C ((2:ℤ)^388) * horner X vp0100100011.list + horner X ep0100100011.list := by
  exact edge_identity (B := (2:ℤ)^606) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100100011 : Branch 1 (-2319761639/16000000 : ℚ) vp010010001 := by
  apply branch_checked idp0100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2319761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2327761639/8000000 : ℚ) by norm_num]
  exact coverp0100100011
theorem coverp010010001 : Covers (-2319761639/16000000 : ℚ) vp010010001 := join_branches bp0100100010 bp0100100011
private noncomputable def vp01001000011_0 : Blocks := edgeBlocks% "full/vectors/01001000011-V-0000.bin"
noncomputable def vp01001000011 : Blocks := vp01001000011_0
theorem coverp01001000011 : Covers (-2315761639/4000000 : ℚ) vp01001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp01001000010_0 : Blocks := edgeBlocks% "full/vectors/01001000010-V-0000.bin"
noncomputable def vp01001000010 : Blocks := vp01001000010_0
theorem coverp01001000010 : Covers (-2311761639/4000000 : ℚ) vp01001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0100100001_0 : Blocks := edgeBlocks% "full/vectors/0100100001-V-0000.bin"
private noncomputable def vp0100100001_1 : Blocks := edgeBlocks% "full/vectors/0100100001-V-0001.bin"
noncomputable def vp0100100001 : Blocks := (Blocks.join vp0100100001_0 vp0100100001_1)
private theorem bp01001000010 : Branch 0 (-2311761639/8000000 : ℚ) vp0100100001 := by
  apply branch_left_normalized (c:=vp01001000010) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-2311761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2311761639/4000000 : ℚ) by norm_num]
  exact coverp01001000010
private noncomputable def ep01001000011_0 : Blocks := edgeBlocks% "full/vectors/01001000011-E-0000.bin"
private noncomputable def ep01001000011_1 : Blocks := edgeBlocks% "full/vectors/01001000011-E-0001.bin"
noncomputable def ep01001000011 : Blocks := (Blocks.join ep01001000011_0 ep01001000011_1)
private theorem idp01001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100100001.list =
    C ((2:ℤ)^207) * horner X vp01001000011.list + horner X ep01001000011.list := by
  exact edge_identity (B := (2:ℤ)^363) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001000011 : Branch 1 (-2311761639/8000000 : ℚ) vp0100100001 := by
  apply branch_checked idp01001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2311761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2315761639/4000000 : ℚ) by norm_num]
  exact coverp01001000011
theorem coverp0100100001 : Covers (-2311761639/8000000 : ℚ) vp0100100001 := join_branches bp01001000010 bp01001000011
private noncomputable def vp010010000011_0 : Blocks := edgeBlocks% "full/vectors/010010000011-V-0000.bin"
noncomputable def vp010010000011 : Blocks := vp010010000011_0
theorem coverp010010000011 : Covers (-2309761639/2000000 : ℚ) vp010010000011 := cover_leaf (by decide +kernel)
private noncomputable def vp010010000010_0 : Blocks := edgeBlocks% "full/vectors/010010000010-V-0000.bin"
noncomputable def vp010010000010 : Blocks := vp010010000010_0
theorem coverp010010000010 : Covers (-2307761639/2000000 : ℚ) vp010010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001000001_0 : Blocks := edgeBlocks% "full/vectors/01001000001-V-0000.bin"
noncomputable def vp01001000001 : Blocks := vp01001000001_0
private theorem bp010010000010 : Branch 0 (-2307761639/4000000 : ℚ) vp01001000001 := by
  apply branch_left_normalized (c:=vp010010000010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2307761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2307761639/2000000 : ℚ) by norm_num]
  exact coverp010010000010
private noncomputable def ep010010000011_0 : Blocks := edgeBlocks% "full/vectors/010010000011-E-0000.bin"
noncomputable def ep010010000011 : Blocks := ep010010000011_0
private theorem idp010010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001000001.list =
    C ((2:ℤ)^116) * horner X vp010010000011.list + horner X ep010010000011.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010000011 : Branch 1 (-2307761639/4000000 : ℚ) vp01001000001 := by
  apply branch_checked idp010010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2307761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2309761639/2000000 : ℚ) by norm_num]
  exact coverp010010000011
theorem coverp01001000001 : Covers (-2307761639/4000000 : ℚ) vp01001000001 := join_branches bp010010000010 bp010010000011
private noncomputable def vp010010000001_0 : Blocks := edgeBlocks% "full/vectors/010010000001-V-0000.bin"
noncomputable def vp010010000001 : Blocks := vp010010000001_0
theorem coverp010010000001 : Covers (-2305761639/2000000 : ℚ) vp010010000001 := cover_leaf (by decide +kernel)
private noncomputable def vp010010000000_0 : Blocks := edgeBlocks% "full/vectors/010010000000-V-0000.bin"
noncomputable def vp010010000000 : Blocks := vp010010000000_0
theorem coverp010010000000 : Covers (-2303761639/2000000 : ℚ) vp010010000000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001000000_0 : Blocks := edgeBlocks% "full/vectors/01001000000-V-0000.bin"
noncomputable def vp01001000000 : Blocks := vp01001000000_0
private theorem bp010010000000 : Branch 0 (-2303761639/4000000 : ℚ) vp01001000000 := by
  apply branch_left_normalized (c:=vp010010000000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2303761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2303761639/2000000 : ℚ) by norm_num]
  exact coverp010010000000
private noncomputable def ep010010000001_0 : Blocks := edgeBlocks% "full/vectors/010010000001-E-0000.bin"
noncomputable def ep010010000001 : Blocks := ep010010000001_0
private theorem idp010010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001000000.list =
    C ((2:ℤ)^112) * horner X vp010010000001.list + horner X ep010010000001.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010000001 : Branch 1 (-2303761639/4000000 : ℚ) vp01001000000 := by
  apply branch_checked idp010010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2303761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2305761639/2000000 : ℚ) by norm_num]
  exact coverp010010000001
theorem coverp01001000000 : Covers (-2303761639/4000000 : ℚ) vp01001000000 := join_branches bp010010000000 bp010010000001
private noncomputable def vp0100100000_0 : Blocks := edgeBlocks% "full/vectors/0100100000-V-0000.bin"
private noncomputable def vp0100100000_1 : Blocks := edgeBlocks% "full/vectors/0100100000-V-0001.bin"
noncomputable def vp0100100000 : Blocks := (Blocks.join vp0100100000_0 vp0100100000_1)
private theorem bp01001000000 : Branch 0 (-2303761639/8000000 : ℚ) vp0100100000 := by
  apply branch_left_normalized (c:=vp01001000000) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-2303761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2303761639/4000000 : ℚ) by norm_num]
  exact coverp01001000000
private noncomputable def ep01001000001_0 : Blocks := edgeBlocks% "full/vectors/01001000001-E-0000.bin"
private noncomputable def ep01001000001_1 : Blocks := edgeBlocks% "full/vectors/01001000001-E-0001.bin"
noncomputable def ep01001000001 : Blocks := (Blocks.join ep01001000001_0 ep01001000001_1)
private theorem idp01001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100100000.list =
    C ((2:ℤ)^209) * horner X vp01001000001.list + horner X ep01001000001.list := by
  exact edge_identity (B := (2:ℤ)^371) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001000001 : Branch 1 (-2303761639/8000000 : ℚ) vp0100100000 := by
  apply branch_checked idp01001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2303761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2307761639/4000000 : ℚ) by norm_num]
  exact coverp01001000001
theorem coverp0100100000 : Covers (-2303761639/8000000 : ℚ) vp0100100000 := join_branches bp01001000000 bp01001000001
private noncomputable def vp010010000_0 : Blocks := edgeBlocks% "full/vectors/010010000-V-0000.bin"
private noncomputable def vp010010000_1 : Blocks := edgeBlocks% "full/vectors/010010000-V-0001.bin"
private noncomputable def vp010010000_2 : Blocks := edgeBlocks% "full/vectors/010010000-V-0002.bin"
noncomputable def vp010010000 : Blocks := (Blocks.join vp010010000_0 (Blocks.join vp010010000_1 vp010010000_2))
private theorem bp0100100000 : Branch 0 (-2303761639/16000000 : ℚ) vp010010000 := by
  apply branch_left_normalized (c:=vp0100100000) (k:=0) (m:=184) (by decide +kernel)
  rw [show 2*(-2303761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2303761639/8000000 : ℚ) by norm_num]
  exact coverp0100100000
private noncomputable def ep0100100001_0 : Blocks := edgeBlocks% "full/vectors/0100100001-E-0000.bin"
private noncomputable def ep0100100001_1 : Blocks := edgeBlocks% "full/vectors/0100100001-E-0001.bin"
private noncomputable def ep0100100001_2 : Blocks := edgeBlocks% "full/vectors/0100100001-E-0002.bin"
noncomputable def ep0100100001 : Blocks := (Blocks.join ep0100100001_0 (Blocks.join ep0100100001_1 ep0100100001_2))
private theorem idp0100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010010000.list =
    C ((2:ℤ)^399) * horner X vp0100100001.list + horner X ep0100100001.list := by
  exact edge_identity (B := (2:ℤ)^621) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100100001 : Branch 1 (-2303761639/16000000 : ℚ) vp010010000 := by
  apply branch_checked idp0100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2303761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2311761639/8000000 : ℚ) by norm_num]
  exact coverp0100100001
theorem coverp010010000 : Covers (-2303761639/16000000 : ℚ) vp010010000 := join_branches bp0100100000 bp0100100001
private noncomputable def vp01001000_0 : Blocks := edgeBlocks% "full/vectors/01001000-V-0000.bin"
private noncomputable def vp01001000_1 : Blocks := edgeBlocks% "full/vectors/01001000-V-0001.bin"
private noncomputable def vp01001000_2 : Blocks := edgeBlocks% "full/vectors/01001000-V-0002.bin"
private noncomputable def vp01001000_3 : Blocks := edgeBlocks% "full/vectors/01001000-V-0003.bin"
private noncomputable def vp01001000_4 : Blocks := edgeBlocks% "full/vectors/01001000-V-0004.bin"
private noncomputable def vp01001000_5 : Blocks := edgeBlocks% "full/vectors/01001000-V-0005.bin"
noncomputable def vp01001000 : Blocks := (Blocks.join (Blocks.join vp01001000_0 (Blocks.join vp01001000_1 vp01001000_2)) (Blocks.join vp01001000_3 (Blocks.join vp01001000_4 vp01001000_5)))
private theorem bp010010000 : Branch 0 (-2303761639/32000000 : ℚ) vp01001000 := by
  apply branch_left_normalized (c:=vp010010000) (k:=0) (m:=347) (by decide +kernel)
  rw [show 2*(-2303761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2303761639/16000000 : ℚ) by norm_num]
  exact coverp010010000
private noncomputable def ep010010001_0 : Blocks := edgeBlocks% "full/vectors/010010001-E-0000.bin"
private noncomputable def ep010010001_1 : Blocks := edgeBlocks% "full/vectors/010010001-E-0001.bin"
private noncomputable def ep010010001_2 : Blocks := edgeBlocks% "full/vectors/010010001-E-0002.bin"
private noncomputable def ep010010001_3 : Blocks := edgeBlocks% "full/vectors/010010001-E-0003.bin"
private noncomputable def ep010010001_4 : Blocks := edgeBlocks% "full/vectors/010010001-E-0004.bin"
private noncomputable def ep010010001_5 : Blocks := edgeBlocks% "full/vectors/010010001-E-0005.bin"
noncomputable def ep010010001 : Blocks := (Blocks.join (Blocks.join ep010010001_0 (Blocks.join ep010010001_1 ep010010001_2)) (Blocks.join ep010010001_3 (Blocks.join ep010010001_4 ep010010001_5)))
private theorem idp010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001000.list =
    C ((2:ℤ)^771) * horner X vp010010001.list + horner X ep010010001.list := by
  exact edge_identity (B := (2:ℤ)^1117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010010001 : Branch 1 (-2303761639/32000000 : ℚ) vp01001000 := by
  apply branch_checked idp010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2303761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2319761639/16000000 : ℚ) by norm_num]
  exact coverp010010001
theorem coverp01001000 : Covers (-2303761639/32000000 : ℚ) vp01001000 := join_branches bp010010000 bp010010001
private noncomputable def vp0100100_0 : Blocks := edgeBlocks% "full/vectors/0100100-V-0000.bin"
private noncomputable def vp0100100_1 : Blocks := edgeBlocks% "full/vectors/0100100-V-0001.bin"
private noncomputable def vp0100100_2 : Blocks := edgeBlocks% "full/vectors/0100100-V-0002.bin"
private noncomputable def vp0100100_3 : Blocks := edgeBlocks% "full/vectors/0100100-V-0003.bin"
private noncomputable def vp0100100_4 : Blocks := edgeBlocks% "full/vectors/0100100-V-0004.bin"
private noncomputable def vp0100100_5 : Blocks := edgeBlocks% "full/vectors/0100100-V-0005.bin"
private noncomputable def vp0100100_6 : Blocks := edgeBlocks% "full/vectors/0100100-V-0006.bin"
private noncomputable def vp0100100_7 : Blocks := edgeBlocks% "full/vectors/0100100-V-0007.bin"
private noncomputable def vp0100100_8 : Blocks := edgeBlocks% "full/vectors/0100100-V-0008.bin"
private noncomputable def vp0100100_9 : Blocks := edgeBlocks% "full/vectors/0100100-V-0009.bin"
private noncomputable def vp0100100_10 : Blocks := edgeBlocks% "full/vectors/0100100-V-0010.bin"
noncomputable def vp0100100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0100100_0 vp0100100_1) (Blocks.join vp0100100_2 (Blocks.join vp0100100_3 vp0100100_4))) (Blocks.join (Blocks.join vp0100100_5 (Blocks.join vp0100100_6 vp0100100_7)) (Blocks.join vp0100100_8 (Blocks.join vp0100100_9 vp0100100_10))))
private theorem bp01001000 : Branch 0 (-2303761639/64000000 : ℚ) vp0100100 := by
  apply branch_left_normalized (c:=vp01001000) (k:=0) (m:=670) (by decide +kernel)
  rw [show 2*(-2303761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2303761639/32000000 : ℚ) by norm_num]
  exact coverp01001000
private noncomputable def ep01001001_0 : Blocks := edgeBlocks% "full/vectors/01001001-E-0000.bin"
private noncomputable def ep01001001_1 : Blocks := edgeBlocks% "full/vectors/01001001-E-0001.bin"
private noncomputable def ep01001001_2 : Blocks := edgeBlocks% "full/vectors/01001001-E-0002.bin"
private noncomputable def ep01001001_3 : Blocks := edgeBlocks% "full/vectors/01001001-E-0003.bin"
private noncomputable def ep01001001_4 : Blocks := edgeBlocks% "full/vectors/01001001-E-0004.bin"
private noncomputable def ep01001001_5 : Blocks := edgeBlocks% "full/vectors/01001001-E-0005.bin"
private noncomputable def ep01001001_6 : Blocks := edgeBlocks% "full/vectors/01001001-E-0006.bin"
private noncomputable def ep01001001_7 : Blocks := edgeBlocks% "full/vectors/01001001-E-0007.bin"
private noncomputable def ep01001001_8 : Blocks := edgeBlocks% "full/vectors/01001001-E-0008.bin"
private noncomputable def ep01001001_9 : Blocks := edgeBlocks% "full/vectors/01001001-E-0009.bin"
private noncomputable def ep01001001_10 : Blocks := edgeBlocks% "full/vectors/01001001-E-0010.bin"
noncomputable def ep01001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01001001_0 ep01001001_1) (Blocks.join ep01001001_2 (Blocks.join ep01001001_3 ep01001001_4))) (Blocks.join (Blocks.join ep01001001_5 (Blocks.join ep01001001_6 ep01001001_7)) (Blocks.join ep01001001_8 (Blocks.join ep01001001_9 ep01001001_10))))
private theorem idp01001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100100.list =
    C ((2:ℤ)^1500) * horner X vp01001001.list + horner X ep01001001.list := by
  exact edge_identity (B := (2:ℤ)^2098) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001001 : Branch 1 (-2303761639/64000000 : ℚ) vp0100100 := by
  apply branch_checked idp01001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2303761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2335761639/32000000 : ℚ) by norm_num]
  exact coverp01001001
theorem coverp0100100 : Covers (-2303761639/64000000 : ℚ) vp0100100 := join_branches bp01001000 bp01001001
private noncomputable def vp010010_0 : Blocks := edgeBlocks% "full/vectors/010010-V-0000.bin"
private noncomputable def vp010010_1 : Blocks := edgeBlocks% "full/vectors/010010-V-0001.bin"
private noncomputable def vp010010_2 : Blocks := edgeBlocks% "full/vectors/010010-V-0002.bin"
private noncomputable def vp010010_3 : Blocks := edgeBlocks% "full/vectors/010010-V-0003.bin"
private noncomputable def vp010010_4 : Blocks := edgeBlocks% "full/vectors/010010-V-0004.bin"
private noncomputable def vp010010_5 : Blocks := edgeBlocks% "full/vectors/010010-V-0005.bin"
private noncomputable def vp010010_6 : Blocks := edgeBlocks% "full/vectors/010010-V-0006.bin"
private noncomputable def vp010010_7 : Blocks := edgeBlocks% "full/vectors/010010-V-0007.bin"
private noncomputable def vp010010_8 : Blocks := edgeBlocks% "full/vectors/010010-V-0008.bin"
private noncomputable def vp010010_9 : Blocks := edgeBlocks% "full/vectors/010010-V-0009.bin"
private noncomputable def vp010010_10 : Blocks := edgeBlocks% "full/vectors/010010-V-0010.bin"
private noncomputable def vp010010_11 : Blocks := edgeBlocks% "full/vectors/010010-V-0011.bin"
private noncomputable def vp010010_12 : Blocks := edgeBlocks% "full/vectors/010010-V-0012.bin"
private noncomputable def vp010010_13 : Blocks := edgeBlocks% "full/vectors/010010-V-0013.bin"
private noncomputable def vp010010_14 : Blocks := edgeBlocks% "full/vectors/010010-V-0014.bin"
private noncomputable def vp010010_15 : Blocks := edgeBlocks% "full/vectors/010010-V-0015.bin"
private noncomputable def vp010010_16 : Blocks := edgeBlocks% "full/vectors/010010-V-0016.bin"
private noncomputable def vp010010_17 : Blocks := edgeBlocks% "full/vectors/010010-V-0017.bin"
private noncomputable def vp010010_18 : Blocks := edgeBlocks% "full/vectors/010010-V-0018.bin"
private noncomputable def vp010010_19 : Blocks := edgeBlocks% "full/vectors/010010-V-0019.bin"
noncomputable def vp010010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp010010_0 vp010010_1) (Blocks.join vp010010_2 (Blocks.join vp010010_3 vp010010_4))) (Blocks.join (Blocks.join vp010010_5 vp010010_6) (Blocks.join vp010010_7 (Blocks.join vp010010_8 vp010010_9)))) (Blocks.join (Blocks.join (Blocks.join vp010010_10 vp010010_11) (Blocks.join vp010010_12 (Blocks.join vp010010_13 vp010010_14))) (Blocks.join (Blocks.join vp010010_15 vp010010_16) (Blocks.join vp010010_17 (Blocks.join vp010010_18 vp010010_19)))))
private theorem bp0100100 : Branch 0 (-2303761639/128000000 : ℚ) vp010010 := by
  apply branch_left_normalized (c:=vp0100100) (k:=0) (m:=1307) (by decide +kernel)
  rw [show 2*(-2303761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-2303761639/64000000 : ℚ) by norm_num]
  exact coverp0100100
private noncomputable def ep0100101_0 : Blocks := edgeBlocks% "full/vectors/0100101-E-0000.bin"
private noncomputable def ep0100101_1 : Blocks := edgeBlocks% "full/vectors/0100101-E-0001.bin"
private noncomputable def ep0100101_2 : Blocks := edgeBlocks% "full/vectors/0100101-E-0002.bin"
private noncomputable def ep0100101_3 : Blocks := edgeBlocks% "full/vectors/0100101-E-0003.bin"
private noncomputable def ep0100101_4 : Blocks := edgeBlocks% "full/vectors/0100101-E-0004.bin"
private noncomputable def ep0100101_5 : Blocks := edgeBlocks% "full/vectors/0100101-E-0005.bin"
private noncomputable def ep0100101_6 : Blocks := edgeBlocks% "full/vectors/0100101-E-0006.bin"
private noncomputable def ep0100101_7 : Blocks := edgeBlocks% "full/vectors/0100101-E-0007.bin"
private noncomputable def ep0100101_8 : Blocks := edgeBlocks% "full/vectors/0100101-E-0008.bin"
private noncomputable def ep0100101_9 : Blocks := edgeBlocks% "full/vectors/0100101-E-0009.bin"
private noncomputable def ep0100101_10 : Blocks := edgeBlocks% "full/vectors/0100101-E-0010.bin"
private noncomputable def ep0100101_11 : Blocks := edgeBlocks% "full/vectors/0100101-E-0011.bin"
private noncomputable def ep0100101_12 : Blocks := edgeBlocks% "full/vectors/0100101-E-0012.bin"
private noncomputable def ep0100101_13 : Blocks := edgeBlocks% "full/vectors/0100101-E-0013.bin"
private noncomputable def ep0100101_14 : Blocks := edgeBlocks% "full/vectors/0100101-E-0014.bin"
private noncomputable def ep0100101_15 : Blocks := edgeBlocks% "full/vectors/0100101-E-0015.bin"
private noncomputable def ep0100101_16 : Blocks := edgeBlocks% "full/vectors/0100101-E-0016.bin"
private noncomputable def ep0100101_17 : Blocks := edgeBlocks% "full/vectors/0100101-E-0017.bin"
private noncomputable def ep0100101_18 : Blocks := edgeBlocks% "full/vectors/0100101-E-0018.bin"
private noncomputable def ep0100101_19 : Blocks := edgeBlocks% "full/vectors/0100101-E-0019.bin"
noncomputable def ep0100101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0100101_0 ep0100101_1) (Blocks.join ep0100101_2 (Blocks.join ep0100101_3 ep0100101_4))) (Blocks.join (Blocks.join ep0100101_5 ep0100101_6) (Blocks.join ep0100101_7 (Blocks.join ep0100101_8 ep0100101_9)))) (Blocks.join (Blocks.join (Blocks.join ep0100101_10 ep0100101_11) (Blocks.join ep0100101_12 (Blocks.join ep0100101_13 ep0100101_14))) (Blocks.join (Blocks.join ep0100101_15 ep0100101_16) (Blocks.join ep0100101_17 (Blocks.join ep0100101_18 ep0100101_19)))))
private theorem idp0100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010010.list =
    C ((2:ℤ)^2908) * horner X vp0100101.list + horner X ep0100101.list := by
  exact edge_identity (B := (2:ℤ)^4011) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100101 : Branch 1 (-2303761639/128000000 : ℚ) vp010010 := by
  apply branch_checked idp0100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2303761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-2367761639/64000000 : ℚ) by norm_num]
  exact coverp0100101
theorem coverp010010 : Covers (-2303761639/128000000 : ℚ) vp010010 := join_branches bp0100100 bp0100101
private noncomputable def vp01001_0 : Blocks := edgeBlocks% "full/vectors/01001-V-0000.bin"
private noncomputable def vp01001_1 : Blocks := edgeBlocks% "full/vectors/01001-V-0001.bin"
private noncomputable def vp01001_2 : Blocks := edgeBlocks% "full/vectors/01001-V-0002.bin"
private noncomputable def vp01001_3 : Blocks := edgeBlocks% "full/vectors/01001-V-0003.bin"
private noncomputable def vp01001_4 : Blocks := edgeBlocks% "full/vectors/01001-V-0004.bin"
private noncomputable def vp01001_5 : Blocks := edgeBlocks% "full/vectors/01001-V-0005.bin"
private noncomputable def vp01001_6 : Blocks := edgeBlocks% "full/vectors/01001-V-0006.bin"
private noncomputable def vp01001_7 : Blocks := edgeBlocks% "full/vectors/01001-V-0007.bin"
private noncomputable def vp01001_8 : Blocks := edgeBlocks% "full/vectors/01001-V-0008.bin"
private noncomputable def vp01001_9 : Blocks := edgeBlocks% "full/vectors/01001-V-0009.bin"
private noncomputable def vp01001_10 : Blocks := edgeBlocks% "full/vectors/01001-V-0010.bin"
private noncomputable def vp01001_11 : Blocks := edgeBlocks% "full/vectors/01001-V-0011.bin"
private noncomputable def vp01001_12 : Blocks := edgeBlocks% "full/vectors/01001-V-0012.bin"
private noncomputable def vp01001_13 : Blocks := edgeBlocks% "full/vectors/01001-V-0013.bin"
private noncomputable def vp01001_14 : Blocks := edgeBlocks% "full/vectors/01001-V-0014.bin"
private noncomputable def vp01001_15 : Blocks := edgeBlocks% "full/vectors/01001-V-0015.bin"
private noncomputable def vp01001_16 : Blocks := edgeBlocks% "full/vectors/01001-V-0016.bin"
private noncomputable def vp01001_17 : Blocks := edgeBlocks% "full/vectors/01001-V-0017.bin"
private noncomputable def vp01001_18 : Blocks := edgeBlocks% "full/vectors/01001-V-0018.bin"
private noncomputable def vp01001_19 : Blocks := edgeBlocks% "full/vectors/01001-V-0019.bin"
private noncomputable def vp01001_20 : Blocks := edgeBlocks% "full/vectors/01001-V-0020.bin"
private noncomputable def vp01001_21 : Blocks := edgeBlocks% "full/vectors/01001-V-0021.bin"
private noncomputable def vp01001_22 : Blocks := edgeBlocks% "full/vectors/01001-V-0022.bin"
private noncomputable def vp01001_23 : Blocks := edgeBlocks% "full/vectors/01001-V-0023.bin"
private noncomputable def vp01001_24 : Blocks := edgeBlocks% "full/vectors/01001-V-0024.bin"
private noncomputable def vp01001_25 : Blocks := edgeBlocks% "full/vectors/01001-V-0025.bin"
private noncomputable def vp01001_26 : Blocks := edgeBlocks% "full/vectors/01001-V-0026.bin"
private noncomputable def vp01001_27 : Blocks := edgeBlocks% "full/vectors/01001-V-0027.bin"
private noncomputable def vp01001_28 : Blocks := edgeBlocks% "full/vectors/01001-V-0028.bin"
private noncomputable def vp01001_29 : Blocks := edgeBlocks% "full/vectors/01001-V-0029.bin"
private noncomputable def vp01001_30 : Blocks := edgeBlocks% "full/vectors/01001-V-0030.bin"
private noncomputable def vp01001_31 : Blocks := edgeBlocks% "full/vectors/01001-V-0031.bin"
private noncomputable def vp01001_32 : Blocks := edgeBlocks% "full/vectors/01001-V-0032.bin"
private noncomputable def vp01001_33 : Blocks := edgeBlocks% "full/vectors/01001-V-0033.bin"
private noncomputable def vp01001_34 : Blocks := edgeBlocks% "full/vectors/01001-V-0034.bin"
private noncomputable def vp01001_35 : Blocks := edgeBlocks% "full/vectors/01001-V-0035.bin"
private noncomputable def vp01001_36 : Blocks := edgeBlocks% "full/vectors/01001-V-0036.bin"
private noncomputable def vp01001_37 : Blocks := edgeBlocks% "full/vectors/01001-V-0037.bin"
noncomputable def vp01001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01001_0 vp01001_1) (Blocks.join vp01001_2 vp01001_3)) (Blocks.join (Blocks.join vp01001_4 vp01001_5) (Blocks.join vp01001_6 (Blocks.join vp01001_7 vp01001_8)))) (Blocks.join (Blocks.join (Blocks.join vp01001_9 vp01001_10) (Blocks.join vp01001_11 (Blocks.join vp01001_12 vp01001_13))) (Blocks.join (Blocks.join vp01001_14 vp01001_15) (Blocks.join vp01001_16 (Blocks.join vp01001_17 vp01001_18))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01001_19 vp01001_20) (Blocks.join vp01001_21 vp01001_22)) (Blocks.join (Blocks.join vp01001_23 vp01001_24) (Blocks.join vp01001_25 (Blocks.join vp01001_26 vp01001_27)))) (Blocks.join (Blocks.join (Blocks.join vp01001_28 vp01001_29) (Blocks.join vp01001_30 (Blocks.join vp01001_31 vp01001_32))) (Blocks.join (Blocks.join vp01001_33 vp01001_34) (Blocks.join vp01001_35 (Blocks.join vp01001_36 vp01001_37))))))
private theorem bp010010 : Branch 0 (-2303761639/256000000 : ℚ) vp01001 := by
  apply branch_left_normalized (c:=vp010010) (k:=0) (m:=2539) (by decide +kernel)
  rw [show 2*(-2303761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-2303761639/128000000 : ℚ) by norm_num]
  exact coverp010010
private noncomputable def ep010011_0 : Blocks := edgeBlocks% "full/vectors/010011-E-0000.bin"
private noncomputable def ep010011_1 : Blocks := edgeBlocks% "full/vectors/010011-E-0001.bin"
private noncomputable def ep010011_2 : Blocks := edgeBlocks% "full/vectors/010011-E-0002.bin"
private noncomputable def ep010011_3 : Blocks := edgeBlocks% "full/vectors/010011-E-0003.bin"
private noncomputable def ep010011_4 : Blocks := edgeBlocks% "full/vectors/010011-E-0004.bin"
private noncomputable def ep010011_5 : Blocks := edgeBlocks% "full/vectors/010011-E-0005.bin"
private noncomputable def ep010011_6 : Blocks := edgeBlocks% "full/vectors/010011-E-0006.bin"
private noncomputable def ep010011_7 : Blocks := edgeBlocks% "full/vectors/010011-E-0007.bin"
private noncomputable def ep010011_8 : Blocks := edgeBlocks% "full/vectors/010011-E-0008.bin"
private noncomputable def ep010011_9 : Blocks := edgeBlocks% "full/vectors/010011-E-0009.bin"
private noncomputable def ep010011_10 : Blocks := edgeBlocks% "full/vectors/010011-E-0010.bin"
private noncomputable def ep010011_11 : Blocks := edgeBlocks% "full/vectors/010011-E-0011.bin"
private noncomputable def ep010011_12 : Blocks := edgeBlocks% "full/vectors/010011-E-0012.bin"
private noncomputable def ep010011_13 : Blocks := edgeBlocks% "full/vectors/010011-E-0013.bin"
private noncomputable def ep010011_14 : Blocks := edgeBlocks% "full/vectors/010011-E-0014.bin"
private noncomputable def ep010011_15 : Blocks := edgeBlocks% "full/vectors/010011-E-0015.bin"
private noncomputable def ep010011_16 : Blocks := edgeBlocks% "full/vectors/010011-E-0016.bin"
private noncomputable def ep010011_17 : Blocks := edgeBlocks% "full/vectors/010011-E-0017.bin"
private noncomputable def ep010011_18 : Blocks := edgeBlocks% "full/vectors/010011-E-0018.bin"
private noncomputable def ep010011_19 : Blocks := edgeBlocks% "full/vectors/010011-E-0019.bin"
private noncomputable def ep010011_20 : Blocks := edgeBlocks% "full/vectors/010011-E-0020.bin"
private noncomputable def ep010011_21 : Blocks := edgeBlocks% "full/vectors/010011-E-0021.bin"
private noncomputable def ep010011_22 : Blocks := edgeBlocks% "full/vectors/010011-E-0022.bin"
private noncomputable def ep010011_23 : Blocks := edgeBlocks% "full/vectors/010011-E-0023.bin"
private noncomputable def ep010011_24 : Blocks := edgeBlocks% "full/vectors/010011-E-0024.bin"
private noncomputable def ep010011_25 : Blocks := edgeBlocks% "full/vectors/010011-E-0025.bin"
private noncomputable def ep010011_26 : Blocks := edgeBlocks% "full/vectors/010011-E-0026.bin"
private noncomputable def ep010011_27 : Blocks := edgeBlocks% "full/vectors/010011-E-0027.bin"
private noncomputable def ep010011_28 : Blocks := edgeBlocks% "full/vectors/010011-E-0028.bin"
private noncomputable def ep010011_29 : Blocks := edgeBlocks% "full/vectors/010011-E-0029.bin"
private noncomputable def ep010011_30 : Blocks := edgeBlocks% "full/vectors/010011-E-0030.bin"
private noncomputable def ep010011_31 : Blocks := edgeBlocks% "full/vectors/010011-E-0031.bin"
private noncomputable def ep010011_32 : Blocks := edgeBlocks% "full/vectors/010011-E-0032.bin"
private noncomputable def ep010011_33 : Blocks := edgeBlocks% "full/vectors/010011-E-0033.bin"
private noncomputable def ep010011_34 : Blocks := edgeBlocks% "full/vectors/010011-E-0034.bin"
private noncomputable def ep010011_35 : Blocks := edgeBlocks% "full/vectors/010011-E-0035.bin"
private noncomputable def ep010011_36 : Blocks := edgeBlocks% "full/vectors/010011-E-0036.bin"
private noncomputable def ep010011_37 : Blocks := edgeBlocks% "full/vectors/010011-E-0037.bin"
noncomputable def ep010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep010011_0 ep010011_1) (Blocks.join ep010011_2 ep010011_3)) (Blocks.join (Blocks.join ep010011_4 ep010011_5) (Blocks.join ep010011_6 (Blocks.join ep010011_7 ep010011_8)))) (Blocks.join (Blocks.join (Blocks.join ep010011_9 ep010011_10) (Blocks.join ep010011_11 (Blocks.join ep010011_12 ep010011_13))) (Blocks.join (Blocks.join ep010011_14 ep010011_15) (Blocks.join ep010011_16 (Blocks.join ep010011_17 ep010011_18))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep010011_19 ep010011_20) (Blocks.join ep010011_21 ep010011_22)) (Blocks.join (Blocks.join ep010011_23 ep010011_24) (Blocks.join ep010011_25 (Blocks.join ep010011_26 ep010011_27)))) (Blocks.join (Blocks.join (Blocks.join ep010011_28 ep010011_29) (Blocks.join ep010011_30 (Blocks.join ep010011_31 ep010011_32))) (Blocks.join (Blocks.join ep010011_33 ep010011_34) (Blocks.join ep010011_35 (Blocks.join ep010011_36 ep010011_37))))))
private def ptsp010011 : List ℤ := [((2:ℤ)^2472+0),((2:ℤ)^2472+1),((2:ℤ)^2472+2),((2:ℤ)^2472+3)]
private theorem boundp010011 : 2^vp01001.size*absSum vp01001.list + ((2:ℤ)^5591*absSum vp010011.list+absSum ep010011.list) < (2:ℤ)^7658 := by decide +kernel
private theorem pointp010011_0 : fastHom 1 ((2:ℤ)^2472+0) vp01001 = ((2:ℤ)^5591)*vp010011.subst ((2:ℤ)^2472+0)+ep010011.subst ((2:ℤ)^2472+0) := by decide +kernel
private theorem pointp010011_1 : fastHom 1 ((2:ℤ)^2472+1) vp01001 = ((2:ℤ)^5591)*vp010011.subst ((2:ℤ)^2472+1)+ep010011.subst ((2:ℤ)^2472+1) := by decide +kernel
private theorem pointp010011_2 : fastHom 1 ((2:ℤ)^2472+2) vp01001 = ((2:ℤ)^5591)*vp010011.subst ((2:ℤ)^2472+2)+ep010011.subst ((2:ℤ)^2472+2) := by decide +kernel
private theorem pointp010011_3 : fastHom 1 ((2:ℤ)^2472+3) vp01001 = ((2:ℤ)^5591)*vp010011.subst ((2:ℤ)^2472+3)+ep010011.subst ((2:ℤ)^2472+3) := by decide +kernel
private theorem checkp010011 (x:ℤ) (hx:x ∈ ptsp010011) : fastHom 1 x vp01001 = ((2:ℤ)^5591)*vp010011.subst x+ep010011.subst x := by
  simp only [ptsp010011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pointp010011_0
  · exact pointp010011_1
  · exact pointp010011_2
  · exact pointp010011_3
private theorem idp010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001.list =
    C ((2:ℤ)^5591) * horner X vp010011.list + horner X ep010011.list := by
  apply edge_identity (B := (2:ℤ)^7658) (by decide) (by positivity) (by positivity) boundp010011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp010011 (by decide +kernel)
  · have h : ptsp010011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp010011.trans_le (by decide +kernel)
  · exact checkp010011
private theorem bp010011 : Branch 1 (-2303761639/256000000 : ℚ) vp01001 := by
  apply branch_checked idp010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2303761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-2431761639/128000000 : ℚ) by norm_num]
  exact coverp010011
theorem coverp01001 : Covers (-2303761639/256000000 : ℚ) vp01001 := join_branches bp010010 bp010011
end NextProof.EdgeFull

