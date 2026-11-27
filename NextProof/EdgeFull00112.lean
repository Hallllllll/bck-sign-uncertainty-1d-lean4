import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp010011111111_0 : Blocks := edgeBlocks% "full/vectors/010011111111-V-0000.bin"
noncomputable def vp010011111111 : Blocks := vp010011111111_0
theorem coverp010011111111 : Covers (-2557761639/2000000 : ℚ) vp010011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp010011111110_0 : Blocks := edgeBlocks% "full/vectors/010011111110-V-0000.bin"
noncomputable def vp010011111110 : Blocks := vp010011111110_0
theorem coverp010011111110 : Covers (-2555761639/2000000 : ℚ) vp010011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001111111_0 : Blocks := edgeBlocks% "full/vectors/01001111111-V-0000.bin"
noncomputable def vp01001111111 : Blocks := vp01001111111_0
private theorem bp010011111110 : Branch 0 (-2555761639/4000000 : ℚ) vp01001111111 := by
  apply branch_left_normalized (c:=vp010011111110) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2555761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2555761639/2000000 : ℚ) by norm_num]
  exact coverp010011111110
private noncomputable def ep010011111111_0 : Blocks := edgeBlocks% "full/vectors/010011111111-E-0000.bin"
noncomputable def ep010011111111 : Blocks := ep010011111111_0
private theorem idp010011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001111111.list =
    C ((2:ℤ)^112) * horner X vp010011111111.list + horner X ep010011111111.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011111111 : Branch 1 (-2555761639/4000000 : ℚ) vp01001111111 := by
  apply branch_checked idp010011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2555761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2557761639/2000000 : ℚ) by norm_num]
  exact coverp010011111111
theorem coverp01001111111 : Covers (-2555761639/4000000 : ℚ) vp01001111111 := join_branches bp010011111110 bp010011111111
private noncomputable def vp010011111101_0 : Blocks := edgeBlocks% "full/vectors/010011111101-V-0000.bin"
noncomputable def vp010011111101 : Blocks := vp010011111101_0
theorem coverp010011111101 : Covers (-2553761639/2000000 : ℚ) vp010011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp010011111100_0 : Blocks := edgeBlocks% "full/vectors/010011111100-V-0000.bin"
noncomputable def vp010011111100 : Blocks := vp010011111100_0
theorem coverp010011111100 : Covers (-2551761639/2000000 : ℚ) vp010011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001111110_0 : Blocks := edgeBlocks% "full/vectors/01001111110-V-0000.bin"
noncomputable def vp01001111110 : Blocks := vp01001111110_0
private theorem bp010011111100 : Branch 0 (-2551761639/4000000 : ℚ) vp01001111110 := by
  apply branch_left_normalized (c:=vp010011111100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2551761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2551761639/2000000 : ℚ) by norm_num]
  exact coverp010011111100
private noncomputable def ep010011111101_0 : Blocks := edgeBlocks% "full/vectors/010011111101-E-0000.bin"
noncomputable def ep010011111101 : Blocks := ep010011111101_0
private theorem idp010011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001111110.list =
    C ((2:ℤ)^111) * horner X vp010011111101.list + horner X ep010011111101.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011111101 : Branch 1 (-2551761639/4000000 : ℚ) vp01001111110 := by
  apply branch_checked idp010011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2551761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2553761639/2000000 : ℚ) by norm_num]
  exact coverp010011111101
theorem coverp01001111110 : Covers (-2551761639/4000000 : ℚ) vp01001111110 := join_branches bp010011111100 bp010011111101
private noncomputable def vp0100111111_0 : Blocks := edgeBlocks% "full/vectors/0100111111-V-0000.bin"
private noncomputable def vp0100111111_1 : Blocks := edgeBlocks% "full/vectors/0100111111-V-0001.bin"
noncomputable def vp0100111111 : Blocks := (Blocks.join vp0100111111_0 vp0100111111_1)
private theorem bp01001111110 : Branch 0 (-2551761639/8000000 : ℚ) vp0100111111 := by
  apply branch_left_normalized (c:=vp01001111110) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-2551761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2551761639/4000000 : ℚ) by norm_num]
  exact coverp01001111110
private noncomputable def ep01001111111_0 : Blocks := edgeBlocks% "full/vectors/01001111111-E-0000.bin"
private noncomputable def ep01001111111_1 : Blocks := edgeBlocks% "full/vectors/01001111111-E-0001.bin"
noncomputable def ep01001111111 : Blocks := (Blocks.join ep01001111111_0 ep01001111111_1)
private theorem idp01001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100111111.list =
    C ((2:ℤ)^201) * horner X vp01001111111.list + horner X ep01001111111.list := by
  exact edge_identity (B := (2:ℤ)^362) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001111111 : Branch 1 (-2551761639/8000000 : ℚ) vp0100111111 := by
  apply branch_checked idp01001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2551761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2555761639/4000000 : ℚ) by norm_num]
  exact coverp01001111111
theorem coverp0100111111 : Covers (-2551761639/8000000 : ℚ) vp0100111111 := join_branches bp01001111110 bp01001111111
private noncomputable def vp010011111011_0 : Blocks := edgeBlocks% "full/vectors/010011111011-V-0000.bin"
noncomputable def vp010011111011 : Blocks := vp010011111011_0
theorem coverp010011111011 : Covers (-2549761639/2000000 : ℚ) vp010011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp010011111010_0 : Blocks := edgeBlocks% "full/vectors/010011111010-V-0000.bin"
noncomputable def vp010011111010 : Blocks := vp010011111010_0
theorem coverp010011111010 : Covers (-2547761639/2000000 : ℚ) vp010011111010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001111101_0 : Blocks := edgeBlocks% "full/vectors/01001111101-V-0000.bin"
noncomputable def vp01001111101 : Blocks := vp01001111101_0
private theorem bp010011111010 : Branch 0 (-2547761639/4000000 : ℚ) vp01001111101 := by
  apply branch_left_normalized (c:=vp010011111010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2547761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2547761639/2000000 : ℚ) by norm_num]
  exact coverp010011111010
private noncomputable def ep010011111011_0 : Blocks := edgeBlocks% "full/vectors/010011111011-E-0000.bin"
noncomputable def ep010011111011 : Blocks := ep010011111011_0
private theorem idp010011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001111101.list =
    C ((2:ℤ)^111) * horner X vp010011111011.list + horner X ep010011111011.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011111011 : Branch 1 (-2547761639/4000000 : ℚ) vp01001111101 := by
  apply branch_checked idp010011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2547761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2549761639/2000000 : ℚ) by norm_num]
  exact coverp010011111011
theorem coverp01001111101 : Covers (-2547761639/4000000 : ℚ) vp01001111101 := join_branches bp010011111010 bp010011111011
private noncomputable def vp010011111001_0 : Blocks := edgeBlocks% "full/vectors/010011111001-V-0000.bin"
noncomputable def vp010011111001 : Blocks := vp010011111001_0
theorem coverp010011111001 : Covers (-2545761639/2000000 : ℚ) vp010011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp010011111000_0 : Blocks := edgeBlocks% "full/vectors/010011111000-V-0000.bin"
noncomputable def vp010011111000 : Blocks := vp010011111000_0
theorem coverp010011111000 : Covers (-2543761639/2000000 : ℚ) vp010011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001111100_0 : Blocks := edgeBlocks% "full/vectors/01001111100-V-0000.bin"
noncomputable def vp01001111100 : Blocks := vp01001111100_0
private theorem bp010011111000 : Branch 0 (-2543761639/4000000 : ℚ) vp01001111100 := by
  apply branch_left_normalized (c:=vp010011111000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2543761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2543761639/2000000 : ℚ) by norm_num]
  exact coverp010011111000
private noncomputable def ep010011111001_0 : Blocks := edgeBlocks% "full/vectors/010011111001-E-0000.bin"
noncomputable def ep010011111001 : Blocks := ep010011111001_0
private theorem idp010011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001111100.list =
    C ((2:ℤ)^110) * horner X vp010011111001.list + horner X ep010011111001.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011111001 : Branch 1 (-2543761639/4000000 : ℚ) vp01001111100 := by
  apply branch_checked idp010011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2543761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2545761639/2000000 : ℚ) by norm_num]
  exact coverp010011111001
theorem coverp01001111100 : Covers (-2543761639/4000000 : ℚ) vp01001111100 := join_branches bp010011111000 bp010011111001
private noncomputable def vp0100111110_0 : Blocks := edgeBlocks% "full/vectors/0100111110-V-0000.bin"
private noncomputable def vp0100111110_1 : Blocks := edgeBlocks% "full/vectors/0100111110-V-0001.bin"
noncomputable def vp0100111110 : Blocks := (Blocks.join vp0100111110_0 vp0100111110_1)
private theorem bp01001111100 : Branch 0 (-2543761639/8000000 : ℚ) vp0100111110 := by
  apply branch_left_normalized (c:=vp01001111100) (k:=0) (m:=98) (by decide +kernel)
  rw [show 2*(-2543761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2543761639/4000000 : ℚ) by norm_num]
  exact coverp01001111100
private noncomputable def ep01001111101_0 : Blocks := edgeBlocks% "full/vectors/01001111101-E-0000.bin"
private noncomputable def ep01001111101_1 : Blocks := edgeBlocks% "full/vectors/01001111101-E-0001.bin"
noncomputable def ep01001111101 : Blocks := (Blocks.join ep01001111101_0 ep01001111101_1)
private theorem idp01001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100111110.list =
    C ((2:ℤ)^202) * horner X vp01001111101.list + horner X ep01001111101.list := by
  exact edge_identity (B := (2:ℤ)^363) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001111101 : Branch 1 (-2543761639/8000000 : ℚ) vp0100111110 := by
  apply branch_checked idp01001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2543761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2547761639/4000000 : ℚ) by norm_num]
  exact coverp01001111101
theorem coverp0100111110 : Covers (-2543761639/8000000 : ℚ) vp0100111110 := join_branches bp01001111100 bp01001111101
private noncomputable def vp010011111_0 : Blocks := edgeBlocks% "full/vectors/010011111-V-0000.bin"
private noncomputable def vp010011111_1 : Blocks := edgeBlocks% "full/vectors/010011111-V-0001.bin"
private noncomputable def vp010011111_2 : Blocks := edgeBlocks% "full/vectors/010011111-V-0002.bin"
noncomputable def vp010011111 : Blocks := (Blocks.join vp010011111_0 (Blocks.join vp010011111_1 vp010011111_2))
private theorem bp0100111110 : Branch 0 (-2543761639/16000000 : ℚ) vp010011111 := by
  apply branch_left_normalized (c:=vp0100111110) (k:=0) (m:=178) (by decide +kernel)
  rw [show 2*(-2543761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2543761639/8000000 : ℚ) by norm_num]
  exact coverp0100111110
private noncomputable def ep0100111111_0 : Blocks := edgeBlocks% "full/vectors/0100111111-E-0000.bin"
private noncomputable def ep0100111111_1 : Blocks := edgeBlocks% "full/vectors/0100111111-E-0001.bin"
private noncomputable def ep0100111111_2 : Blocks := edgeBlocks% "full/vectors/0100111111-E-0002.bin"
noncomputable def ep0100111111 : Blocks := (Blocks.join ep0100111111_0 (Blocks.join ep0100111111_1 ep0100111111_2))
private theorem idp0100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010011111.list =
    C ((2:ℤ)^380) * horner X vp0100111111.list + horner X ep0100111111.list := by
  exact edge_identity (B := (2:ℤ)^600) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100111111 : Branch 1 (-2543761639/16000000 : ℚ) vp010011111 := by
  apply branch_checked idp0100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2543761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2551761639/8000000 : ℚ) by norm_num]
  exact coverp0100111111
theorem coverp010011111 : Covers (-2543761639/16000000 : ℚ) vp010011111 := join_branches bp0100111110 bp0100111111
private noncomputable def vp010011110111_0 : Blocks := edgeBlocks% "full/vectors/010011110111-V-0000.bin"
noncomputable def vp010011110111 : Blocks := vp010011110111_0
theorem coverp010011110111 : Covers (-2541761639/2000000 : ℚ) vp010011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp010011110110_0 : Blocks := edgeBlocks% "full/vectors/010011110110-V-0000.bin"
noncomputable def vp010011110110 : Blocks := vp010011110110_0
theorem coverp010011110110 : Covers (-2539761639/2000000 : ℚ) vp010011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001111011_0 : Blocks := edgeBlocks% "full/vectors/01001111011-V-0000.bin"
noncomputable def vp01001111011 : Blocks := vp01001111011_0
private theorem bp010011110110 : Branch 0 (-2539761639/4000000 : ℚ) vp01001111011 := by
  apply branch_left_normalized (c:=vp010011110110) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2539761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2539761639/2000000 : ℚ) by norm_num]
  exact coverp010011110110
private noncomputable def ep010011110111_0 : Blocks := edgeBlocks% "full/vectors/010011110111-E-0000.bin"
noncomputable def ep010011110111 : Blocks := ep010011110111_0
private theorem idp010011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001111011.list =
    C ((2:ℤ)^111) * horner X vp010011110111.list + horner X ep010011110111.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011110111 : Branch 1 (-2539761639/4000000 : ℚ) vp01001111011 := by
  apply branch_checked idp010011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2539761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2541761639/2000000 : ℚ) by norm_num]
  exact coverp010011110111
theorem coverp01001111011 : Covers (-2539761639/4000000 : ℚ) vp01001111011 := join_branches bp010011110110 bp010011110111
private noncomputable def vp010011110101_0 : Blocks := edgeBlocks% "full/vectors/010011110101-V-0000.bin"
noncomputable def vp010011110101 : Blocks := vp010011110101_0
theorem coverp010011110101 : Covers (-2537761639/2000000 : ℚ) vp010011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp010011110100_0 : Blocks := edgeBlocks% "full/vectors/010011110100-V-0000.bin"
noncomputable def vp010011110100 : Blocks := vp010011110100_0
theorem coverp010011110100 : Covers (-2535761639/2000000 : ℚ) vp010011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001111010_0 : Blocks := edgeBlocks% "full/vectors/01001111010-V-0000.bin"
noncomputable def vp01001111010 : Blocks := vp01001111010_0
private theorem bp010011110100 : Branch 0 (-2535761639/4000000 : ℚ) vp01001111010 := by
  apply branch_left_normalized (c:=vp010011110100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2535761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2535761639/2000000 : ℚ) by norm_num]
  exact coverp010011110100
private noncomputable def ep010011110101_0 : Blocks := edgeBlocks% "full/vectors/010011110101-E-0000.bin"
noncomputable def ep010011110101 : Blocks := ep010011110101_0
private theorem idp010011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001111010.list =
    C ((2:ℤ)^111) * horner X vp010011110101.list + horner X ep010011110101.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011110101 : Branch 1 (-2535761639/4000000 : ℚ) vp01001111010 := by
  apply branch_checked idp010011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2535761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2537761639/2000000 : ℚ) by norm_num]
  exact coverp010011110101
theorem coverp01001111010 : Covers (-2535761639/4000000 : ℚ) vp01001111010 := join_branches bp010011110100 bp010011110101
private noncomputable def vp0100111101_0 : Blocks := edgeBlocks% "full/vectors/0100111101-V-0000.bin"
private noncomputable def vp0100111101_1 : Blocks := edgeBlocks% "full/vectors/0100111101-V-0001.bin"
noncomputable def vp0100111101 : Blocks := (Blocks.join vp0100111101_0 vp0100111101_1)
private theorem bp01001111010 : Branch 0 (-2535761639/8000000 : ℚ) vp0100111101 := by
  apply branch_left_normalized (c:=vp01001111010) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-2535761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2535761639/4000000 : ℚ) by norm_num]
  exact coverp01001111010
private noncomputable def ep01001111011_0 : Blocks := edgeBlocks% "full/vectors/01001111011-E-0000.bin"
private noncomputable def ep01001111011_1 : Blocks := edgeBlocks% "full/vectors/01001111011-E-0001.bin"
noncomputable def ep01001111011 : Blocks := (Blocks.join ep01001111011_0 ep01001111011_1)
private theorem idp01001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100111101.list =
    C ((2:ℤ)^202) * horner X vp01001111011.list + horner X ep01001111011.list := by
  exact edge_identity (B := (2:ℤ)^363) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001111011 : Branch 1 (-2535761639/8000000 : ℚ) vp0100111101 := by
  apply branch_checked idp01001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2535761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2539761639/4000000 : ℚ) by norm_num]
  exact coverp01001111011
theorem coverp0100111101 : Covers (-2535761639/8000000 : ℚ) vp0100111101 := join_branches bp01001111010 bp01001111011
private noncomputable def vp010011110011_0 : Blocks := edgeBlocks% "full/vectors/010011110011-V-0000.bin"
noncomputable def vp010011110011 : Blocks := vp010011110011_0
theorem coverp010011110011 : Covers (-2533761639/2000000 : ℚ) vp010011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp010011110010_0 : Blocks := edgeBlocks% "full/vectors/010011110010-V-0000.bin"
noncomputable def vp010011110010 : Blocks := vp010011110010_0
theorem coverp010011110010 : Covers (-2531761639/2000000 : ℚ) vp010011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001111001_0 : Blocks := edgeBlocks% "full/vectors/01001111001-V-0000.bin"
noncomputable def vp01001111001 : Blocks := vp01001111001_0
private theorem bp010011110010 : Branch 0 (-2531761639/4000000 : ℚ) vp01001111001 := by
  apply branch_left_normalized (c:=vp010011110010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2531761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2531761639/2000000 : ℚ) by norm_num]
  exact coverp010011110010
private noncomputable def ep010011110011_0 : Blocks := edgeBlocks% "full/vectors/010011110011-E-0000.bin"
noncomputable def ep010011110011 : Blocks := ep010011110011_0
private theorem idp010011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001111001.list =
    C ((2:ℤ)^111) * horner X vp010011110011.list + horner X ep010011110011.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011110011 : Branch 1 (-2531761639/4000000 : ℚ) vp01001111001 := by
  apply branch_checked idp010011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2531761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2533761639/2000000 : ℚ) by norm_num]
  exact coverp010011110011
theorem coverp01001111001 : Covers (-2531761639/4000000 : ℚ) vp01001111001 := join_branches bp010011110010 bp010011110011
private noncomputable def vp010011110001_0 : Blocks := edgeBlocks% "full/vectors/010011110001-V-0000.bin"
noncomputable def vp010011110001 : Blocks := vp010011110001_0
theorem coverp010011110001 : Covers (-2529761639/2000000 : ℚ) vp010011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp010011110000_0 : Blocks := edgeBlocks% "full/vectors/010011110000-V-0000.bin"
noncomputable def vp010011110000 : Blocks := vp010011110000_0
theorem coverp010011110000 : Covers (-2527761639/2000000 : ℚ) vp010011110000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001111000_0 : Blocks := edgeBlocks% "full/vectors/01001111000-V-0000.bin"
noncomputable def vp01001111000 : Blocks := vp01001111000_0
private theorem bp010011110000 : Branch 0 (-2527761639/4000000 : ℚ) vp01001111000 := by
  apply branch_left_normalized (c:=vp010011110000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2527761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2527761639/2000000 : ℚ) by norm_num]
  exact coverp010011110000
private noncomputable def ep010011110001_0 : Blocks := edgeBlocks% "full/vectors/010011110001-E-0000.bin"
noncomputable def ep010011110001 : Blocks := ep010011110001_0
private theorem idp010011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001111000.list =
    C ((2:ℤ)^112) * horner X vp010011110001.list + horner X ep010011110001.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011110001 : Branch 1 (-2527761639/4000000 : ℚ) vp01001111000 := by
  apply branch_checked idp010011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2527761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2529761639/2000000 : ℚ) by norm_num]
  exact coverp010011110001
theorem coverp01001111000 : Covers (-2527761639/4000000 : ℚ) vp01001111000 := join_branches bp010011110000 bp010011110001
private noncomputable def vp0100111100_0 : Blocks := edgeBlocks% "full/vectors/0100111100-V-0000.bin"
private noncomputable def vp0100111100_1 : Blocks := edgeBlocks% "full/vectors/0100111100-V-0001.bin"
noncomputable def vp0100111100 : Blocks := (Blocks.join vp0100111100_0 vp0100111100_1)
private theorem bp01001111000 : Branch 0 (-2527761639/8000000 : ℚ) vp0100111100 := by
  apply branch_left_normalized (c:=vp01001111000) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-2527761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2527761639/4000000 : ℚ) by norm_num]
  exact coverp01001111000
private noncomputable def ep01001111001_0 : Blocks := edgeBlocks% "full/vectors/01001111001-E-0000.bin"
private noncomputable def ep01001111001_1 : Blocks := edgeBlocks% "full/vectors/01001111001-E-0001.bin"
noncomputable def ep01001111001 : Blocks := (Blocks.join ep01001111001_0 ep01001111001_1)
private theorem idp01001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100111100.list =
    C ((2:ℤ)^203) * horner X vp01001111001.list + horner X ep01001111001.list := by
  exact edge_identity (B := (2:ℤ)^364) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001111001 : Branch 1 (-2527761639/8000000 : ℚ) vp0100111100 := by
  apply branch_checked idp01001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2527761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2531761639/4000000 : ℚ) by norm_num]
  exact coverp01001111001
theorem coverp0100111100 : Covers (-2527761639/8000000 : ℚ) vp0100111100 := join_branches bp01001111000 bp01001111001
private noncomputable def vp010011110_0 : Blocks := edgeBlocks% "full/vectors/010011110-V-0000.bin"
private noncomputable def vp010011110_1 : Blocks := edgeBlocks% "full/vectors/010011110-V-0001.bin"
private noncomputable def vp010011110_2 : Blocks := edgeBlocks% "full/vectors/010011110-V-0002.bin"
noncomputable def vp010011110 : Blocks := (Blocks.join vp010011110_0 (Blocks.join vp010011110_1 vp010011110_2))
private theorem bp0100111100 : Branch 0 (-2527761639/16000000 : ℚ) vp010011110 := by
  apply branch_left_normalized (c:=vp0100111100) (k:=0) (m:=178) (by decide +kernel)
  rw [show 2*(-2527761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2527761639/8000000 : ℚ) by norm_num]
  exact coverp0100111100
private noncomputable def ep0100111101_0 : Blocks := edgeBlocks% "full/vectors/0100111101-E-0000.bin"
private noncomputable def ep0100111101_1 : Blocks := edgeBlocks% "full/vectors/0100111101-E-0001.bin"
private noncomputable def ep0100111101_2 : Blocks := edgeBlocks% "full/vectors/0100111101-E-0002.bin"
noncomputable def ep0100111101 : Blocks := (Blocks.join ep0100111101_0 (Blocks.join ep0100111101_1 ep0100111101_2))
private theorem idp0100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010011110.list =
    C ((2:ℤ)^382) * horner X vp0100111101.list + horner X ep0100111101.list := by
  exact edge_identity (B := (2:ℤ)^602) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100111101 : Branch 1 (-2527761639/16000000 : ℚ) vp010011110 := by
  apply branch_checked idp0100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2527761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2535761639/8000000 : ℚ) by norm_num]
  exact coverp0100111101
theorem coverp010011110 : Covers (-2527761639/16000000 : ℚ) vp010011110 := join_branches bp0100111100 bp0100111101
private noncomputable def vp01001111_0 : Blocks := edgeBlocks% "full/vectors/01001111-V-0000.bin"
private noncomputable def vp01001111_1 : Blocks := edgeBlocks% "full/vectors/01001111-V-0001.bin"
private noncomputable def vp01001111_2 : Blocks := edgeBlocks% "full/vectors/01001111-V-0002.bin"
private noncomputable def vp01001111_3 : Blocks := edgeBlocks% "full/vectors/01001111-V-0003.bin"
private noncomputable def vp01001111_4 : Blocks := edgeBlocks% "full/vectors/01001111-V-0004.bin"
private noncomputable def vp01001111_5 : Blocks := edgeBlocks% "full/vectors/01001111-V-0005.bin"
noncomputable def vp01001111 : Blocks := (Blocks.join (Blocks.join vp01001111_0 (Blocks.join vp01001111_1 vp01001111_2)) (Blocks.join vp01001111_3 (Blocks.join vp01001111_4 vp01001111_5)))
private theorem bp010011110 : Branch 0 (-2527761639/32000000 : ℚ) vp01001111 := by
  apply branch_left_normalized (c:=vp010011110) (k:=0) (m:=334) (by decide +kernel)
  rw [show 2*(-2527761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2527761639/16000000 : ℚ) by norm_num]
  exact coverp010011110
private noncomputable def ep010011111_0 : Blocks := edgeBlocks% "full/vectors/010011111-E-0000.bin"
private noncomputable def ep010011111_1 : Blocks := edgeBlocks% "full/vectors/010011111-E-0001.bin"
private noncomputable def ep010011111_2 : Blocks := edgeBlocks% "full/vectors/010011111-E-0002.bin"
private noncomputable def ep010011111_3 : Blocks := edgeBlocks% "full/vectors/010011111-E-0003.bin"
private noncomputable def ep010011111_4 : Blocks := edgeBlocks% "full/vectors/010011111-E-0004.bin"
private noncomputable def ep010011111_5 : Blocks := edgeBlocks% "full/vectors/010011111-E-0005.bin"
noncomputable def ep010011111 : Blocks := (Blocks.join (Blocks.join ep010011111_0 (Blocks.join ep010011111_1 ep010011111_2)) (Blocks.join ep010011111_3 (Blocks.join ep010011111_4 ep010011111_5)))
private theorem idp010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001111.list =
    C ((2:ℤ)^737) * horner X vp010011111.list + horner X ep010011111.list := by
  exact edge_identity (B := (2:ℤ)^1077) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011111 : Branch 1 (-2527761639/32000000 : ℚ) vp01001111 := by
  apply branch_checked idp010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2527761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2543761639/16000000 : ℚ) by norm_num]
  exact coverp010011111
theorem coverp01001111 : Covers (-2527761639/32000000 : ℚ) vp01001111 := join_branches bp010011110 bp010011111
private noncomputable def vp010011101111_0 : Blocks := edgeBlocks% "full/vectors/010011101111-V-0000.bin"
noncomputable def vp010011101111 : Blocks := vp010011101111_0
theorem coverp010011101111 : Covers (-2525761639/2000000 : ℚ) vp010011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp010011101110_0 : Blocks := edgeBlocks% "full/vectors/010011101110-V-0000.bin"
noncomputable def vp010011101110 : Blocks := vp010011101110_0
theorem coverp010011101110 : Covers (-2523761639/2000000 : ℚ) vp010011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001110111_0 : Blocks := edgeBlocks% "full/vectors/01001110111-V-0000.bin"
noncomputable def vp01001110111 : Blocks := vp01001110111_0
private theorem bp010011101110 : Branch 0 (-2523761639/4000000 : ℚ) vp01001110111 := by
  apply branch_left_normalized (c:=vp010011101110) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2523761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2523761639/2000000 : ℚ) by norm_num]
  exact coverp010011101110
private noncomputable def ep010011101111_0 : Blocks := edgeBlocks% "full/vectors/010011101111-E-0000.bin"
noncomputable def ep010011101111 : Blocks := ep010011101111_0
private theorem idp010011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001110111.list =
    C ((2:ℤ)^112) * horner X vp010011101111.list + horner X ep010011101111.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011101111 : Branch 1 (-2523761639/4000000 : ℚ) vp01001110111 := by
  apply branch_checked idp010011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2523761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2525761639/2000000 : ℚ) by norm_num]
  exact coverp010011101111
theorem coverp01001110111 : Covers (-2523761639/4000000 : ℚ) vp01001110111 := join_branches bp010011101110 bp010011101111
private noncomputable def vp010011101101_0 : Blocks := edgeBlocks% "full/vectors/010011101101-V-0000.bin"
noncomputable def vp010011101101 : Blocks := vp010011101101_0
theorem coverp010011101101 : Covers (-2521761639/2000000 : ℚ) vp010011101101 := cover_leaf (by decide +kernel)
private noncomputable def vp010011101100_0 : Blocks := edgeBlocks% "full/vectors/010011101100-V-0000.bin"
noncomputable def vp010011101100 : Blocks := vp010011101100_0
theorem coverp010011101100 : Covers (-2519761639/2000000 : ℚ) vp010011101100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001110110_0 : Blocks := edgeBlocks% "full/vectors/01001110110-V-0000.bin"
noncomputable def vp01001110110 : Blocks := vp01001110110_0
private theorem bp010011101100 : Branch 0 (-2519761639/4000000 : ℚ) vp01001110110 := by
  apply branch_left_normalized (c:=vp010011101100) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2519761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2519761639/2000000 : ℚ) by norm_num]
  exact coverp010011101100
private noncomputable def ep010011101101_0 : Blocks := edgeBlocks% "full/vectors/010011101101-E-0000.bin"
noncomputable def ep010011101101 : Blocks := ep010011101101_0
private theorem idp010011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001110110.list =
    C ((2:ℤ)^111) * horner X vp010011101101.list + horner X ep010011101101.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011101101 : Branch 1 (-2519761639/4000000 : ℚ) vp01001110110 := by
  apply branch_checked idp010011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2519761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2521761639/2000000 : ℚ) by norm_num]
  exact coverp010011101101
theorem coverp01001110110 : Covers (-2519761639/4000000 : ℚ) vp01001110110 := join_branches bp010011101100 bp010011101101
private noncomputable def vp0100111011_0 : Blocks := edgeBlocks% "full/vectors/0100111011-V-0000.bin"
private noncomputable def vp0100111011_1 : Blocks := edgeBlocks% "full/vectors/0100111011-V-0001.bin"
noncomputable def vp0100111011 : Blocks := (Blocks.join vp0100111011_0 vp0100111011_1)
private theorem bp01001110110 : Branch 0 (-2519761639/8000000 : ℚ) vp0100111011 := by
  apply branch_left_normalized (c:=vp01001110110) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-2519761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2519761639/4000000 : ℚ) by norm_num]
  exact coverp01001110110
private noncomputable def ep01001110111_0 : Blocks := edgeBlocks% "full/vectors/01001110111-E-0000.bin"
private noncomputable def ep01001110111_1 : Blocks := edgeBlocks% "full/vectors/01001110111-E-0001.bin"
noncomputable def ep01001110111 : Blocks := (Blocks.join ep01001110111_0 ep01001110111_1)
private theorem idp01001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100111011.list =
    C ((2:ℤ)^201) * horner X vp01001110111.list + horner X ep01001110111.list := by
  exact edge_identity (B := (2:ℤ)^363) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001110111 : Branch 1 (-2519761639/8000000 : ℚ) vp0100111011 := by
  apply branch_checked idp01001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2519761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2523761639/4000000 : ℚ) by norm_num]
  exact coverp01001110111
theorem coverp0100111011 : Covers (-2519761639/8000000 : ℚ) vp0100111011 := join_branches bp01001110110 bp01001110111
private noncomputable def vp010011101011_0 : Blocks := edgeBlocks% "full/vectors/010011101011-V-0000.bin"
noncomputable def vp010011101011 : Blocks := vp010011101011_0
theorem coverp010011101011 : Covers (-2517761639/2000000 : ℚ) vp010011101011 := cover_leaf (by decide +kernel)
private noncomputable def vp010011101010_0 : Blocks := edgeBlocks% "full/vectors/010011101010-V-0000.bin"
noncomputable def vp010011101010 : Blocks := vp010011101010_0
theorem coverp010011101010 : Covers (-2515761639/2000000 : ℚ) vp010011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001110101_0 : Blocks := edgeBlocks% "full/vectors/01001110101-V-0000.bin"
noncomputable def vp01001110101 : Blocks := vp01001110101_0
private theorem bp010011101010 : Branch 0 (-2515761639/4000000 : ℚ) vp01001110101 := by
  apply branch_left_normalized (c:=vp010011101010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2515761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2515761639/2000000 : ℚ) by norm_num]
  exact coverp010011101010
private noncomputable def ep010011101011_0 : Blocks := edgeBlocks% "full/vectors/010011101011-E-0000.bin"
noncomputable def ep010011101011 : Blocks := ep010011101011_0
private theorem idp010011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001110101.list =
    C ((2:ℤ)^112) * horner X vp010011101011.list + horner X ep010011101011.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011101011 : Branch 1 (-2515761639/4000000 : ℚ) vp01001110101 := by
  apply branch_checked idp010011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2515761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2517761639/2000000 : ℚ) by norm_num]
  exact coverp010011101011
theorem coverp01001110101 : Covers (-2515761639/4000000 : ℚ) vp01001110101 := join_branches bp010011101010 bp010011101011
private noncomputable def vp010011101001_0 : Blocks := edgeBlocks% "full/vectors/010011101001-V-0000.bin"
noncomputable def vp010011101001 : Blocks := vp010011101001_0
theorem coverp010011101001 : Covers (-2513761639/2000000 : ℚ) vp010011101001 := cover_leaf (by decide +kernel)
private noncomputable def vp010011101000_0 : Blocks := edgeBlocks% "full/vectors/010011101000-V-0000.bin"
noncomputable def vp010011101000 : Blocks := vp010011101000_0
theorem coverp010011101000 : Covers (-2511761639/2000000 : ℚ) vp010011101000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001110100_0 : Blocks := edgeBlocks% "full/vectors/01001110100-V-0000.bin"
noncomputable def vp01001110100 : Blocks := vp01001110100_0
private theorem bp010011101000 : Branch 0 (-2511761639/4000000 : ℚ) vp01001110100 := by
  apply branch_left_normalized (c:=vp010011101000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2511761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2511761639/2000000 : ℚ) by norm_num]
  exact coverp010011101000
private noncomputable def ep010011101001_0 : Blocks := edgeBlocks% "full/vectors/010011101001-E-0000.bin"
noncomputable def ep010011101001 : Blocks := ep010011101001_0
private theorem idp010011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001110100.list =
    C ((2:ℤ)^113) * horner X vp010011101001.list + horner X ep010011101001.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011101001 : Branch 1 (-2511761639/4000000 : ℚ) vp01001110100 := by
  apply branch_checked idp010011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2511761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2513761639/2000000 : ℚ) by norm_num]
  exact coverp010011101001
theorem coverp01001110100 : Covers (-2511761639/4000000 : ℚ) vp01001110100 := join_branches bp010011101000 bp010011101001
private noncomputable def vp0100111010_0 : Blocks := edgeBlocks% "full/vectors/0100111010-V-0000.bin"
private noncomputable def vp0100111010_1 : Blocks := edgeBlocks% "full/vectors/0100111010-V-0001.bin"
noncomputable def vp0100111010 : Blocks := (Blocks.join vp0100111010_0 vp0100111010_1)
private theorem bp01001110100 : Branch 0 (-2511761639/8000000 : ℚ) vp0100111010 := by
  apply branch_left_normalized (c:=vp01001110100) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-2511761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2511761639/4000000 : ℚ) by norm_num]
  exact coverp01001110100
private noncomputable def ep01001110101_0 : Blocks := edgeBlocks% "full/vectors/01001110101-E-0000.bin"
private noncomputable def ep01001110101_1 : Blocks := edgeBlocks% "full/vectors/01001110101-E-0001.bin"
noncomputable def ep01001110101 : Blocks := (Blocks.join ep01001110101_0 ep01001110101_1)
private theorem idp01001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100111010.list =
    C ((2:ℤ)^204) * horner X vp01001110101.list + horner X ep01001110101.list := by
  exact edge_identity (B := (2:ℤ)^365) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001110101 : Branch 1 (-2511761639/8000000 : ℚ) vp0100111010 := by
  apply branch_checked idp01001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2511761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2515761639/4000000 : ℚ) by norm_num]
  exact coverp01001110101
theorem coverp0100111010 : Covers (-2511761639/8000000 : ℚ) vp0100111010 := join_branches bp01001110100 bp01001110101
private noncomputable def vp010011101_0 : Blocks := edgeBlocks% "full/vectors/010011101-V-0000.bin"
private noncomputable def vp010011101_1 : Blocks := edgeBlocks% "full/vectors/010011101-V-0001.bin"
private noncomputable def vp010011101_2 : Blocks := edgeBlocks% "full/vectors/010011101-V-0002.bin"
noncomputable def vp010011101 : Blocks := (Blocks.join vp010011101_0 (Blocks.join vp010011101_1 vp010011101_2))
private theorem bp0100111010 : Branch 0 (-2511761639/16000000 : ℚ) vp010011101 := by
  apply branch_left_normalized (c:=vp0100111010) (k:=0) (m:=179) (by decide +kernel)
  rw [show 2*(-2511761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2511761639/8000000 : ℚ) by norm_num]
  exact coverp0100111010
private noncomputable def ep0100111011_0 : Blocks := edgeBlocks% "full/vectors/0100111011-E-0000.bin"
private noncomputable def ep0100111011_1 : Blocks := edgeBlocks% "full/vectors/0100111011-E-0001.bin"
private noncomputable def ep0100111011_2 : Blocks := edgeBlocks% "full/vectors/0100111011-E-0002.bin"
noncomputable def ep0100111011 : Blocks := (Blocks.join ep0100111011_0 (Blocks.join ep0100111011_1 ep0100111011_2))
private theorem idp0100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010011101.list =
    C ((2:ℤ)^383) * horner X vp0100111011.list + horner X ep0100111011.list := by
  exact edge_identity (B := (2:ℤ)^604) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100111011 : Branch 1 (-2511761639/16000000 : ℚ) vp010011101 := by
  apply branch_checked idp0100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2511761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2519761639/8000000 : ℚ) by norm_num]
  exact coverp0100111011
theorem coverp010011101 : Covers (-2511761639/16000000 : ℚ) vp010011101 := join_branches bp0100111010 bp0100111011
private noncomputable def vp010011100111_0 : Blocks := edgeBlocks% "full/vectors/010011100111-V-0000.bin"
noncomputable def vp010011100111 : Blocks := vp010011100111_0
theorem coverp010011100111 : Covers (-2509761639/2000000 : ℚ) vp010011100111 := cover_leaf (by decide +kernel)
private noncomputable def vp010011100110_0 : Blocks := edgeBlocks% "full/vectors/010011100110-V-0000.bin"
noncomputable def vp010011100110 : Blocks := vp010011100110_0
theorem coverp010011100110 : Covers (-2507761639/2000000 : ℚ) vp010011100110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001110011_0 : Blocks := edgeBlocks% "full/vectors/01001110011-V-0000.bin"
noncomputable def vp01001110011 : Blocks := vp01001110011_0
private theorem bp010011100110 : Branch 0 (-2507761639/4000000 : ℚ) vp01001110011 := by
  apply branch_left_normalized (c:=vp010011100110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2507761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2507761639/2000000 : ℚ) by norm_num]
  exact coverp010011100110
private noncomputable def ep010011100111_0 : Blocks := edgeBlocks% "full/vectors/010011100111-E-0000.bin"
noncomputable def ep010011100111 : Blocks := ep010011100111_0
private theorem idp010011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001110011.list =
    C ((2:ℤ)^107) * horner X vp010011100111.list + horner X ep010011100111.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011100111 : Branch 1 (-2507761639/4000000 : ℚ) vp01001110011 := by
  apply branch_checked idp010011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2507761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2509761639/2000000 : ℚ) by norm_num]
  exact coverp010011100111
theorem coverp01001110011 : Covers (-2507761639/4000000 : ℚ) vp01001110011 := join_branches bp010011100110 bp010011100111
private noncomputable def vp010011100101_0 : Blocks := edgeBlocks% "full/vectors/010011100101-V-0000.bin"
noncomputable def vp010011100101 : Blocks := vp010011100101_0
theorem coverp010011100101 : Covers (-2505761639/2000000 : ℚ) vp010011100101 := cover_leaf (by decide +kernel)
private noncomputable def vp010011100100_0 : Blocks := edgeBlocks% "full/vectors/010011100100-V-0000.bin"
noncomputable def vp010011100100 : Blocks := vp010011100100_0
theorem coverp010011100100 : Covers (-2503761639/2000000 : ℚ) vp010011100100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001110010_0 : Blocks := edgeBlocks% "full/vectors/01001110010-V-0000.bin"
noncomputable def vp01001110010 : Blocks := vp01001110010_0
private theorem bp010011100100 : Branch 0 (-2503761639/4000000 : ℚ) vp01001110010 := by
  apply branch_left_normalized (c:=vp010011100100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2503761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2503761639/2000000 : ℚ) by norm_num]
  exact coverp010011100100
private noncomputable def ep010011100101_0 : Blocks := edgeBlocks% "full/vectors/010011100101-E-0000.bin"
noncomputable def ep010011100101 : Blocks := ep010011100101_0
private theorem idp010011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001110010.list =
    C ((2:ℤ)^108) * horner X vp010011100101.list + horner X ep010011100101.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011100101 : Branch 1 (-2503761639/4000000 : ℚ) vp01001110010 := by
  apply branch_checked idp010011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2503761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2505761639/2000000 : ℚ) by norm_num]
  exact coverp010011100101
theorem coverp01001110010 : Covers (-2503761639/4000000 : ℚ) vp01001110010 := join_branches bp010011100100 bp010011100101
private noncomputable def vp0100111001_0 : Blocks := edgeBlocks% "full/vectors/0100111001-V-0000.bin"
private noncomputable def vp0100111001_1 : Blocks := edgeBlocks% "full/vectors/0100111001-V-0001.bin"
noncomputable def vp0100111001 : Blocks := (Blocks.join vp0100111001_0 vp0100111001_1)
private theorem bp01001110010 : Branch 0 (-2503761639/8000000 : ℚ) vp0100111001 := by
  apply branch_left_normalized (c:=vp01001110010) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-2503761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2503761639/4000000 : ℚ) by norm_num]
  exact coverp01001110010
private noncomputable def ep01001110011_0 : Blocks := edgeBlocks% "full/vectors/01001110011-E-0000.bin"
private noncomputable def ep01001110011_1 : Blocks := edgeBlocks% "full/vectors/01001110011-E-0001.bin"
noncomputable def ep01001110011 : Blocks := (Blocks.join ep01001110011_0 ep01001110011_1)
private theorem idp01001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100111001.list =
    C ((2:ℤ)^197) * horner X vp01001110011.list + horner X ep01001110011.list := by
  exact edge_identity (B := (2:ℤ)^354) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001110011 : Branch 1 (-2503761639/8000000 : ℚ) vp0100111001 := by
  apply branch_checked idp01001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2503761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2507761639/4000000 : ℚ) by norm_num]
  exact coverp01001110011
theorem coverp0100111001 : Covers (-2503761639/8000000 : ℚ) vp0100111001 := join_branches bp01001110010 bp01001110011
private noncomputable def vp010011100011_0 : Blocks := edgeBlocks% "full/vectors/010011100011-V-0000.bin"
noncomputable def vp010011100011 : Blocks := vp010011100011_0
theorem coverp010011100011 : Covers (-2501761639/2000000 : ℚ) vp010011100011 := cover_leaf (by decide +kernel)
private noncomputable def vp010011100010_0 : Blocks := edgeBlocks% "full/vectors/010011100010-V-0000.bin"
noncomputable def vp010011100010 : Blocks := vp010011100010_0
theorem coverp010011100010 : Covers (-2499761639/2000000 : ℚ) vp010011100010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001110001_0 : Blocks := edgeBlocks% "full/vectors/01001110001-V-0000.bin"
noncomputable def vp01001110001 : Blocks := vp01001110001_0
private theorem bp010011100010 : Branch 0 (-2499761639/4000000 : ℚ) vp01001110001 := by
  apply branch_left_normalized (c:=vp010011100010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-2499761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2499761639/2000000 : ℚ) by norm_num]
  exact coverp010011100010
private noncomputable def ep010011100011_0 : Blocks := edgeBlocks% "full/vectors/010011100011-E-0000.bin"
noncomputable def ep010011100011 : Blocks := ep010011100011_0
private theorem idp010011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001110001.list =
    C ((2:ℤ)^107) * horner X vp010011100011.list + horner X ep010011100011.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011100011 : Branch 1 (-2499761639/4000000 : ℚ) vp01001110001 := by
  apply branch_checked idp010011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2499761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2501761639/2000000 : ℚ) by norm_num]
  exact coverp010011100011
theorem coverp01001110001 : Covers (-2499761639/4000000 : ℚ) vp01001110001 := join_branches bp010011100010 bp010011100011
private noncomputable def vp01001110000_0 : Blocks := edgeBlocks% "full/vectors/01001110000-V-0000.bin"
noncomputable def vp01001110000 : Blocks := vp01001110000_0
theorem coverp01001110000 : Covers (-2495761639/4000000 : ℚ) vp01001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0100111000_0 : Blocks := edgeBlocks% "full/vectors/0100111000-V-0000.bin"
private noncomputable def vp0100111000_1 : Blocks := edgeBlocks% "full/vectors/0100111000-V-0001.bin"
noncomputable def vp0100111000 : Blocks := (Blocks.join vp0100111000_0 vp0100111000_1)
private theorem bp01001110000 : Branch 0 (-2495761639/8000000 : ℚ) vp0100111000 := by
  apply branch_left_normalized (c:=vp01001110000) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-2495761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2495761639/4000000 : ℚ) by norm_num]
  exact coverp01001110000
private noncomputable def ep01001110001_0 : Blocks := edgeBlocks% "full/vectors/01001110001-E-0000.bin"
private noncomputable def ep01001110001_1 : Blocks := edgeBlocks% "full/vectors/01001110001-E-0001.bin"
noncomputable def ep01001110001 : Blocks := (Blocks.join ep01001110001_0 ep01001110001_1)
private theorem idp01001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100111000.list =
    C ((2:ℤ)^196) * horner X vp01001110001.list + horner X ep01001110001.list := by
  exact edge_identity (B := (2:ℤ)^349) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001110001 : Branch 1 (-2495761639/8000000 : ℚ) vp0100111000 := by
  apply branch_checked idp01001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2495761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2499761639/4000000 : ℚ) by norm_num]
  exact coverp01001110001
theorem coverp0100111000 : Covers (-2495761639/8000000 : ℚ) vp0100111000 := join_branches bp01001110000 bp01001110001
private noncomputable def vp010011100_0 : Blocks := edgeBlocks% "full/vectors/010011100-V-0000.bin"
private noncomputable def vp010011100_1 : Blocks := edgeBlocks% "full/vectors/010011100-V-0001.bin"
private noncomputable def vp010011100_2 : Blocks := edgeBlocks% "full/vectors/010011100-V-0002.bin"
noncomputable def vp010011100 : Blocks := (Blocks.join vp010011100_0 (Blocks.join vp010011100_1 vp010011100_2))
private theorem bp0100111000 : Branch 0 (-2495761639/16000000 : ℚ) vp010011100 := by
  apply branch_left_normalized (c:=vp0100111000) (k:=0) (m:=173) (by decide +kernel)
  rw [show 2*(-2495761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2495761639/8000000 : ℚ) by norm_num]
  exact coverp0100111000
private noncomputable def ep0100111001_0 : Blocks := edgeBlocks% "full/vectors/0100111001-E-0000.bin"
private noncomputable def ep0100111001_1 : Blocks := edgeBlocks% "full/vectors/0100111001-E-0001.bin"
private noncomputable def ep0100111001_2 : Blocks := edgeBlocks% "full/vectors/0100111001-E-0002.bin"
noncomputable def ep0100111001 : Blocks := (Blocks.join ep0100111001_0 (Blocks.join ep0100111001_1 ep0100111001_2))
private theorem idp0100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010011100.list =
    C ((2:ℤ)^374) * horner X vp0100111001.list + horner X ep0100111001.list := by
  exact edge_identity (B := (2:ℤ)^590) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100111001 : Branch 1 (-2495761639/16000000 : ℚ) vp010011100 := by
  apply branch_checked idp0100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2495761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2503761639/8000000 : ℚ) by norm_num]
  exact coverp0100111001
theorem coverp010011100 : Covers (-2495761639/16000000 : ℚ) vp010011100 := join_branches bp0100111000 bp0100111001
private noncomputable def vp01001110_0 : Blocks := edgeBlocks% "full/vectors/01001110-V-0000.bin"
private noncomputable def vp01001110_1 : Blocks := edgeBlocks% "full/vectors/01001110-V-0001.bin"
private noncomputable def vp01001110_2 : Blocks := edgeBlocks% "full/vectors/01001110-V-0002.bin"
private noncomputable def vp01001110_3 : Blocks := edgeBlocks% "full/vectors/01001110-V-0003.bin"
private noncomputable def vp01001110_4 : Blocks := edgeBlocks% "full/vectors/01001110-V-0004.bin"
private noncomputable def vp01001110_5 : Blocks := edgeBlocks% "full/vectors/01001110-V-0005.bin"
noncomputable def vp01001110 : Blocks := (Blocks.join (Blocks.join vp01001110_0 (Blocks.join vp01001110_1 vp01001110_2)) (Blocks.join vp01001110_3 (Blocks.join vp01001110_4 vp01001110_5)))
private theorem bp010011100 : Branch 0 (-2495761639/32000000 : ℚ) vp01001110 := by
  apply branch_left_normalized (c:=vp010011100) (k:=0) (m:=330) (by decide +kernel)
  rw [show 2*(-2495761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2495761639/16000000 : ℚ) by norm_num]
  exact coverp010011100
private noncomputable def ep010011101_0 : Blocks := edgeBlocks% "full/vectors/010011101-E-0000.bin"
private noncomputable def ep010011101_1 : Blocks := edgeBlocks% "full/vectors/010011101-E-0001.bin"
private noncomputable def ep010011101_2 : Blocks := edgeBlocks% "full/vectors/010011101-E-0002.bin"
private noncomputable def ep010011101_3 : Blocks := edgeBlocks% "full/vectors/010011101-E-0003.bin"
private noncomputable def ep010011101_4 : Blocks := edgeBlocks% "full/vectors/010011101-E-0004.bin"
private noncomputable def ep010011101_5 : Blocks := edgeBlocks% "full/vectors/010011101-E-0005.bin"
noncomputable def ep010011101 : Blocks := (Blocks.join (Blocks.join ep010011101_0 (Blocks.join ep010011101_1 ep010011101_2)) (Blocks.join ep010011101_3 (Blocks.join ep010011101_4 ep010011101_5)))
private theorem idp010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001110.list =
    C ((2:ℤ)^725) * horner X vp010011101.list + horner X ep010011101.list := by
  exact edge_identity (B := (2:ℤ)^1067) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011101 : Branch 1 (-2495761639/32000000 : ℚ) vp01001110 := by
  apply branch_checked idp010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2495761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2511761639/16000000 : ℚ) by norm_num]
  exact coverp010011101
theorem coverp01001110 : Covers (-2495761639/32000000 : ℚ) vp01001110 := join_branches bp010011100 bp010011101
private noncomputable def vp0100111_0 : Blocks := edgeBlocks% "full/vectors/0100111-V-0000.bin"
private noncomputable def vp0100111_1 : Blocks := edgeBlocks% "full/vectors/0100111-V-0001.bin"
private noncomputable def vp0100111_2 : Blocks := edgeBlocks% "full/vectors/0100111-V-0002.bin"
private noncomputable def vp0100111_3 : Blocks := edgeBlocks% "full/vectors/0100111-V-0003.bin"
private noncomputable def vp0100111_4 : Blocks := edgeBlocks% "full/vectors/0100111-V-0004.bin"
private noncomputable def vp0100111_5 : Blocks := edgeBlocks% "full/vectors/0100111-V-0005.bin"
private noncomputable def vp0100111_6 : Blocks := edgeBlocks% "full/vectors/0100111-V-0006.bin"
private noncomputable def vp0100111_7 : Blocks := edgeBlocks% "full/vectors/0100111-V-0007.bin"
private noncomputable def vp0100111_8 : Blocks := edgeBlocks% "full/vectors/0100111-V-0008.bin"
private noncomputable def vp0100111_9 : Blocks := edgeBlocks% "full/vectors/0100111-V-0009.bin"
noncomputable def vp0100111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0100111_0 vp0100111_1) (Blocks.join vp0100111_2 (Blocks.join vp0100111_3 vp0100111_4))) (Blocks.join (Blocks.join vp0100111_5 vp0100111_6) (Blocks.join vp0100111_7 (Blocks.join vp0100111_8 vp0100111_9))))
private theorem bp01001110 : Branch 0 (-2495761639/64000000 : ℚ) vp0100111 := by
  apply branch_left_normalized (c:=vp01001110) (k:=0) (m:=641) (by decide +kernel)
  rw [show 2*(-2495761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2495761639/32000000 : ℚ) by norm_num]
  exact coverp01001110
private noncomputable def ep01001111_0 : Blocks := edgeBlocks% "full/vectors/01001111-E-0000.bin"
private noncomputable def ep01001111_1 : Blocks := edgeBlocks% "full/vectors/01001111-E-0001.bin"
private noncomputable def ep01001111_2 : Blocks := edgeBlocks% "full/vectors/01001111-E-0002.bin"
private noncomputable def ep01001111_3 : Blocks := edgeBlocks% "full/vectors/01001111-E-0003.bin"
private noncomputable def ep01001111_4 : Blocks := edgeBlocks% "full/vectors/01001111-E-0004.bin"
private noncomputable def ep01001111_5 : Blocks := edgeBlocks% "full/vectors/01001111-E-0005.bin"
private noncomputable def ep01001111_6 : Blocks := edgeBlocks% "full/vectors/01001111-E-0006.bin"
private noncomputable def ep01001111_7 : Blocks := edgeBlocks% "full/vectors/01001111-E-0007.bin"
private noncomputable def ep01001111_8 : Blocks := edgeBlocks% "full/vectors/01001111-E-0008.bin"
private noncomputable def ep01001111_9 : Blocks := edgeBlocks% "full/vectors/01001111-E-0009.bin"
noncomputable def ep01001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01001111_0 ep01001111_1) (Blocks.join ep01001111_2 (Blocks.join ep01001111_3 ep01001111_4))) (Blocks.join (Blocks.join ep01001111_5 ep01001111_6) (Blocks.join ep01001111_7 (Blocks.join ep01001111_8 ep01001111_9))))
private theorem idp01001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100111.list =
    C ((2:ℤ)^1428) * horner X vp01001111.list + horner X ep01001111.list := by
  exact edge_identity (B := (2:ℤ)^2009) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001111 : Branch 1 (-2495761639/64000000 : ℚ) vp0100111 := by
  apply branch_checked idp01001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2495761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2527761639/32000000 : ℚ) by norm_num]
  exact coverp01001111
theorem coverp0100111 : Covers (-2495761639/64000000 : ℚ) vp0100111 := join_branches bp01001110 bp01001111
private noncomputable def vp01001101111_0 : Blocks := edgeBlocks% "full/vectors/01001101111-V-0000.bin"
noncomputable def vp01001101111 : Blocks := vp01001101111_0
theorem coverp01001101111 : Covers (-2491761639/4000000 : ℚ) vp01001101111 := cover_leaf (by decide +kernel)
private noncomputable def vp01001101110_0 : Blocks := edgeBlocks% "full/vectors/01001101110-V-0000.bin"
noncomputable def vp01001101110 : Blocks := vp01001101110_0
theorem coverp01001101110 : Covers (-2487761639/4000000 : ℚ) vp01001101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0100110111_0 : Blocks := edgeBlocks% "full/vectors/0100110111-V-0000.bin"
private noncomputable def vp0100110111_1 : Blocks := edgeBlocks% "full/vectors/0100110111-V-0001.bin"
noncomputable def vp0100110111 : Blocks := (Blocks.join vp0100110111_0 vp0100110111_1)
private theorem bp01001101110 : Branch 0 (-2487761639/8000000 : ℚ) vp0100110111 := by
  apply branch_left_normalized (c:=vp01001101110) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-2487761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2487761639/4000000 : ℚ) by norm_num]
  exact coverp01001101110
private noncomputable def ep01001101111_0 : Blocks := edgeBlocks% "full/vectors/01001101111-E-0000.bin"
private noncomputable def ep01001101111_1 : Blocks := edgeBlocks% "full/vectors/01001101111-E-0001.bin"
noncomputable def ep01001101111 : Blocks := (Blocks.join ep01001101111_0 ep01001101111_1)
private theorem idp01001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100110111.list =
    C ((2:ℤ)^196) * horner X vp01001101111.list + horner X ep01001101111.list := by
  exact edge_identity (B := (2:ℤ)^348) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001101111 : Branch 1 (-2487761639/8000000 : ℚ) vp0100110111 := by
  apply branch_checked idp01001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2487761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2491761639/4000000 : ℚ) by norm_num]
  exact coverp01001101111
theorem coverp0100110111 : Covers (-2487761639/8000000 : ℚ) vp0100110111 := join_branches bp01001101110 bp01001101111
private noncomputable def vp01001101101_0 : Blocks := edgeBlocks% "full/vectors/01001101101-V-0000.bin"
noncomputable def vp01001101101 : Blocks := vp01001101101_0
theorem coverp01001101101 : Covers (-2483761639/4000000 : ℚ) vp01001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp01001101100_0 : Blocks := edgeBlocks% "full/vectors/01001101100-V-0000.bin"
noncomputable def vp01001101100 : Blocks := vp01001101100_0
theorem coverp01001101100 : Covers (-2479761639/4000000 : ℚ) vp01001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0100110110_0 : Blocks := edgeBlocks% "full/vectors/0100110110-V-0000.bin"
private noncomputable def vp0100110110_1 : Blocks := edgeBlocks% "full/vectors/0100110110-V-0001.bin"
noncomputable def vp0100110110 : Blocks := (Blocks.join vp0100110110_0 vp0100110110_1)
private theorem bp01001101100 : Branch 0 (-2479761639/8000000 : ℚ) vp0100110110 := by
  apply branch_left_normalized (c:=vp01001101100) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-2479761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2479761639/4000000 : ℚ) by norm_num]
  exact coverp01001101100
private noncomputable def ep01001101101_0 : Blocks := edgeBlocks% "full/vectors/01001101101-E-0000.bin"
private noncomputable def ep01001101101_1 : Blocks := edgeBlocks% "full/vectors/01001101101-E-0001.bin"
noncomputable def ep01001101101 : Blocks := (Blocks.join ep01001101101_0 ep01001101101_1)
private theorem idp01001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100110110.list =
    C ((2:ℤ)^199) * horner X vp01001101101.list + horner X ep01001101101.list := by
  exact edge_identity (B := (2:ℤ)^350) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001101101 : Branch 1 (-2479761639/8000000 : ℚ) vp0100110110 := by
  apply branch_checked idp01001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2479761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2483761639/4000000 : ℚ) by norm_num]
  exact coverp01001101101
theorem coverp0100110110 : Covers (-2479761639/8000000 : ℚ) vp0100110110 := join_branches bp01001101100 bp01001101101
private noncomputable def vp010011011_0 : Blocks := edgeBlocks% "full/vectors/010011011-V-0000.bin"
private noncomputable def vp010011011_1 : Blocks := edgeBlocks% "full/vectors/010011011-V-0001.bin"
private noncomputable def vp010011011_2 : Blocks := edgeBlocks% "full/vectors/010011011-V-0002.bin"
noncomputable def vp010011011 : Blocks := (Blocks.join vp010011011_0 (Blocks.join vp010011011_1 vp010011011_2))
private theorem bp0100110110 : Branch 0 (-2479761639/16000000 : ℚ) vp010011011 := by
  apply branch_left_normalized (c:=vp0100110110) (k:=0) (m:=174) (by decide +kernel)
  rw [show 2*(-2479761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2479761639/8000000 : ℚ) by norm_num]
  exact coverp0100110110
private noncomputable def ep0100110111_0 : Blocks := edgeBlocks% "full/vectors/0100110111-E-0000.bin"
private noncomputable def ep0100110111_1 : Blocks := edgeBlocks% "full/vectors/0100110111-E-0001.bin"
private noncomputable def ep0100110111_2 : Blocks := edgeBlocks% "full/vectors/0100110111-E-0002.bin"
noncomputable def ep0100110111 : Blocks := (Blocks.join ep0100110111_0 (Blocks.join ep0100110111_1 ep0100110111_2))
private theorem idp0100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010011011.list =
    C ((2:ℤ)^378) * horner X vp0100110111.list + horner X ep0100110111.list := by
  exact edge_identity (B := (2:ℤ)^590) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100110111 : Branch 1 (-2479761639/16000000 : ℚ) vp010011011 := by
  apply branch_checked idp0100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2479761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2487761639/8000000 : ℚ) by norm_num]
  exact coverp0100110111
theorem coverp010011011 : Covers (-2479761639/16000000 : ℚ) vp010011011 := join_branches bp0100110110 bp0100110111
private noncomputable def vp01001101011_0 : Blocks := edgeBlocks% "full/vectors/01001101011-V-0000.bin"
noncomputable def vp01001101011 : Blocks := vp01001101011_0
theorem coverp01001101011 : Covers (-2475761639/4000000 : ℚ) vp01001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp01001101010_0 : Blocks := edgeBlocks% "full/vectors/01001101010-V-0000.bin"
noncomputable def vp01001101010 : Blocks := vp01001101010_0
theorem coverp01001101010 : Covers (-2471761639/4000000 : ℚ) vp01001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0100110101_0 : Blocks := edgeBlocks% "full/vectors/0100110101-V-0000.bin"
private noncomputable def vp0100110101_1 : Blocks := edgeBlocks% "full/vectors/0100110101-V-0001.bin"
noncomputable def vp0100110101 : Blocks := (Blocks.join vp0100110101_0 vp0100110101_1)
private theorem bp01001101010 : Branch 0 (-2471761639/8000000 : ℚ) vp0100110101 := by
  apply branch_left_normalized (c:=vp01001101010) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-2471761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2471761639/4000000 : ℚ) by norm_num]
  exact coverp01001101010
private noncomputable def ep01001101011_0 : Blocks := edgeBlocks% "full/vectors/01001101011-E-0000.bin"
private noncomputable def ep01001101011_1 : Blocks := edgeBlocks% "full/vectors/01001101011-E-0001.bin"
noncomputable def ep01001101011 : Blocks := (Blocks.join ep01001101011_0 ep01001101011_1)
private theorem idp01001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100110101.list =
    C ((2:ℤ)^200) * horner X vp01001101011.list + horner X ep01001101011.list := by
  exact edge_identity (B := (2:ℤ)^353) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001101011 : Branch 1 (-2471761639/8000000 : ℚ) vp0100110101 := by
  apply branch_checked idp01001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2471761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2475761639/4000000 : ℚ) by norm_num]
  exact coverp01001101011
theorem coverp0100110101 : Covers (-2471761639/8000000 : ℚ) vp0100110101 := join_branches bp01001101010 bp01001101011
private noncomputable def vp01001101001_0 : Blocks := edgeBlocks% "full/vectors/01001101001-V-0000.bin"
noncomputable def vp01001101001 : Blocks := vp01001101001_0
theorem coverp01001101001 : Covers (-2467761639/4000000 : ℚ) vp01001101001 := cover_leaf (by decide +kernel)
private noncomputable def vp010011010001_0 : Blocks := edgeBlocks% "full/vectors/010011010001-V-0000.bin"
noncomputable def vp010011010001 : Blocks := vp010011010001_0
theorem coverp010011010001 : Covers (-2465761639/2000000 : ℚ) vp010011010001 := cover_leaf (by decide +kernel)
private noncomputable def vp010011010000_0 : Blocks := edgeBlocks% "full/vectors/010011010000-V-0000.bin"
noncomputable def vp010011010000 : Blocks := vp010011010000_0
theorem coverp010011010000 : Covers (-2463761639/2000000 : ℚ) vp010011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001101000_0 : Blocks := edgeBlocks% "full/vectors/01001101000-V-0000.bin"
noncomputable def vp01001101000 : Blocks := vp01001101000_0
private theorem bp010011010000 : Branch 0 (-2463761639/4000000 : ℚ) vp01001101000 := by
  apply branch_left_normalized (c:=vp010011010000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2463761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2463761639/2000000 : ℚ) by norm_num]
  exact coverp010011010000
private noncomputable def ep010011010001_0 : Blocks := edgeBlocks% "full/vectors/010011010001-E-0000.bin"
noncomputable def ep010011010001 : Blocks := ep010011010001_0
private theorem idp010011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001101000.list =
    C ((2:ℤ)^114) * horner X vp010011010001.list + horner X ep010011010001.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011010001 : Branch 1 (-2463761639/4000000 : ℚ) vp01001101000 := by
  apply branch_checked idp010011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2463761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2465761639/2000000 : ℚ) by norm_num]
  exact coverp010011010001
theorem coverp01001101000 : Covers (-2463761639/4000000 : ℚ) vp01001101000 := join_branches bp010011010000 bp010011010001
private noncomputable def vp0100110100_0 : Blocks := edgeBlocks% "full/vectors/0100110100-V-0000.bin"
private noncomputable def vp0100110100_1 : Blocks := edgeBlocks% "full/vectors/0100110100-V-0001.bin"
noncomputable def vp0100110100 : Blocks := (Blocks.join vp0100110100_0 vp0100110100_1)
private theorem bp01001101000 : Branch 0 (-2463761639/8000000 : ℚ) vp0100110100 := by
  apply branch_left_normalized (c:=vp01001101000) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-2463761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2463761639/4000000 : ℚ) by norm_num]
  exact coverp01001101000
private noncomputable def ep01001101001_0 : Blocks := edgeBlocks% "full/vectors/01001101001-E-0000.bin"
private noncomputable def ep01001101001_1 : Blocks := edgeBlocks% "full/vectors/01001101001-E-0001.bin"
noncomputable def ep01001101001 : Blocks := (Blocks.join ep01001101001_0 ep01001101001_1)
private theorem idp01001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100110100.list =
    C ((2:ℤ)^207) * horner X vp01001101001.list + horner X ep01001101001.list := by
  exact edge_identity (B := (2:ℤ)^363) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001101001 : Branch 1 (-2463761639/8000000 : ℚ) vp0100110100 := by
  apply branch_checked idp01001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2463761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2467761639/4000000 : ℚ) by norm_num]
  exact coverp01001101001
theorem coverp0100110100 : Covers (-2463761639/8000000 : ℚ) vp0100110100 := join_branches bp01001101000 bp01001101001
private noncomputable def vp010011010_0 : Blocks := edgeBlocks% "full/vectors/010011010-V-0000.bin"
private noncomputable def vp010011010_1 : Blocks := edgeBlocks% "full/vectors/010011010-V-0001.bin"
private noncomputable def vp010011010_2 : Blocks := edgeBlocks% "full/vectors/010011010-V-0002.bin"
noncomputable def vp010011010 : Blocks := (Blocks.join vp010011010_0 (Blocks.join vp010011010_1 vp010011010_2))
private theorem bp0100110100 : Branch 0 (-2463761639/16000000 : ℚ) vp010011010 := by
  apply branch_left_normalized (c:=vp0100110100) (k:=0) (m:=179) (by decide +kernel)
  rw [show 2*(-2463761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2463761639/8000000 : ℚ) by norm_num]
  exact coverp0100110100
private noncomputable def ep0100110101_0 : Blocks := edgeBlocks% "full/vectors/0100110101-E-0000.bin"
private noncomputable def ep0100110101_1 : Blocks := edgeBlocks% "full/vectors/0100110101-E-0001.bin"
private noncomputable def ep0100110101_2 : Blocks := edgeBlocks% "full/vectors/0100110101-E-0002.bin"
noncomputable def ep0100110101 : Blocks := (Blocks.join ep0100110101_0 (Blocks.join ep0100110101_1 ep0100110101_2))
private theorem idp0100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010011010.list =
    C ((2:ℤ)^389) * horner X vp0100110101.list + horner X ep0100110101.list := by
  exact edge_identity (B := (2:ℤ)^604) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100110101 : Branch 1 (-2463761639/16000000 : ℚ) vp010011010 := by
  apply branch_checked idp0100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2463761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2471761639/8000000 : ℚ) by norm_num]
  exact coverp0100110101
theorem coverp010011010 : Covers (-2463761639/16000000 : ℚ) vp010011010 := join_branches bp0100110100 bp0100110101
private noncomputable def vp01001101_0 : Blocks := edgeBlocks% "full/vectors/01001101-V-0000.bin"
private noncomputable def vp01001101_1 : Blocks := edgeBlocks% "full/vectors/01001101-V-0001.bin"
private noncomputable def vp01001101_2 : Blocks := edgeBlocks% "full/vectors/01001101-V-0002.bin"
private noncomputable def vp01001101_3 : Blocks := edgeBlocks% "full/vectors/01001101-V-0003.bin"
private noncomputable def vp01001101_4 : Blocks := edgeBlocks% "full/vectors/01001101-V-0004.bin"
private noncomputable def vp01001101_5 : Blocks := edgeBlocks% "full/vectors/01001101-V-0005.bin"
noncomputable def vp01001101 : Blocks := (Blocks.join (Blocks.join vp01001101_0 (Blocks.join vp01001101_1 vp01001101_2)) (Blocks.join vp01001101_3 (Blocks.join vp01001101_4 vp01001101_5)))
private theorem bp010011010 : Branch 0 (-2463761639/32000000 : ℚ) vp01001101 := by
  apply branch_left_normalized (c:=vp010011010) (k:=0) (m:=336) (by decide +kernel)
  rw [show 2*(-2463761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2463761639/16000000 : ℚ) by norm_num]
  exact coverp010011010
private noncomputable def ep010011011_0 : Blocks := edgeBlocks% "full/vectors/010011011-E-0000.bin"
private noncomputable def ep010011011_1 : Blocks := edgeBlocks% "full/vectors/010011011-E-0001.bin"
private noncomputable def ep010011011_2 : Blocks := edgeBlocks% "full/vectors/010011011-E-0002.bin"
private noncomputable def ep010011011_3 : Blocks := edgeBlocks% "full/vectors/010011011-E-0003.bin"
private noncomputable def ep010011011_4 : Blocks := edgeBlocks% "full/vectors/010011011-E-0004.bin"
private noncomputable def ep010011011_5 : Blocks := edgeBlocks% "full/vectors/010011011-E-0005.bin"
noncomputable def ep010011011 : Blocks := (Blocks.join (Blocks.join ep010011011_0 (Blocks.join ep010011011_1 ep010011011_2)) (Blocks.join ep010011011_3 (Blocks.join ep010011011_4 ep010011011_5)))
private theorem idp010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001101.list =
    C ((2:ℤ)^751) * horner X vp010011011.list + horner X ep010011011.list := by
  exact edge_identity (B := (2:ℤ)^1086) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011011 : Branch 1 (-2463761639/32000000 : ℚ) vp01001101 := by
  apply branch_checked idp010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2463761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2479761639/16000000 : ℚ) by norm_num]
  exact coverp010011011
theorem coverp01001101 : Covers (-2463761639/32000000 : ℚ) vp01001101 := join_branches bp010011010 bp010011011
private noncomputable def vp010011001111_0 : Blocks := edgeBlocks% "full/vectors/010011001111-V-0000.bin"
noncomputable def vp010011001111 : Blocks := vp010011001111_0
theorem coverp010011001111 : Covers (-2461761639/2000000 : ℚ) vp010011001111 := cover_leaf (by decide +kernel)
private noncomputable def vp010011001110_0 : Blocks := edgeBlocks% "full/vectors/010011001110-V-0000.bin"
noncomputable def vp010011001110 : Blocks := vp010011001110_0
theorem coverp010011001110 : Covers (-2459761639/2000000 : ℚ) vp010011001110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001100111_0 : Blocks := edgeBlocks% "full/vectors/01001100111-V-0000.bin"
noncomputable def vp01001100111 : Blocks := vp01001100111_0
private theorem bp010011001110 : Branch 0 (-2459761639/4000000 : ℚ) vp01001100111 := by
  apply branch_left_normalized (c:=vp010011001110) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2459761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2459761639/2000000 : ℚ) by norm_num]
  exact coverp010011001110
private noncomputable def ep010011001111_0 : Blocks := edgeBlocks% "full/vectors/010011001111-E-0000.bin"
noncomputable def ep010011001111 : Blocks := ep010011001111_0
private theorem idp010011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001100111.list =
    C ((2:ℤ)^109) * horner X vp010011001111.list + horner X ep010011001111.list := by
  exact edge_identity (B := (2:ℤ)^240) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011001111 : Branch 1 (-2459761639/4000000 : ℚ) vp01001100111 := by
  apply branch_checked idp010011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2459761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2461761639/2000000 : ℚ) by norm_num]
  exact coverp010011001111
theorem coverp01001100111 : Covers (-2459761639/4000000 : ℚ) vp01001100111 := join_branches bp010011001110 bp010011001111
private noncomputable def vp010011001101_0 : Blocks := edgeBlocks% "full/vectors/010011001101-V-0000.bin"
noncomputable def vp010011001101 : Blocks := vp010011001101_0
theorem coverp010011001101 : Covers (-2457761639/2000000 : ℚ) vp010011001101 := cover_leaf (by decide +kernel)
private noncomputable def vp010011001100_0 : Blocks := edgeBlocks% "full/vectors/010011001100-V-0000.bin"
noncomputable def vp010011001100 : Blocks := vp010011001100_0
theorem coverp010011001100 : Covers (-2455761639/2000000 : ℚ) vp010011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001100110_0 : Blocks := edgeBlocks% "full/vectors/01001100110-V-0000.bin"
noncomputable def vp01001100110 : Blocks := vp01001100110_0
private theorem bp010011001100 : Branch 0 (-2455761639/4000000 : ℚ) vp01001100110 := by
  apply branch_left_normalized (c:=vp010011001100) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2455761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2455761639/2000000 : ℚ) by norm_num]
  exact coverp010011001100
private noncomputable def ep010011001101_0 : Blocks := edgeBlocks% "full/vectors/010011001101-E-0000.bin"
noncomputable def ep010011001101 : Blocks := ep010011001101_0
private theorem idp010011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001100110.list =
    C ((2:ℤ)^112) * horner X vp010011001101.list + horner X ep010011001101.list := by
  exact edge_identity (B := (2:ℤ)^240) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011001101 : Branch 1 (-2455761639/4000000 : ℚ) vp01001100110 := by
  apply branch_checked idp010011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2455761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2457761639/2000000 : ℚ) by norm_num]
  exact coverp010011001101
theorem coverp01001100110 : Covers (-2455761639/4000000 : ℚ) vp01001100110 := join_branches bp010011001100 bp010011001101
private noncomputable def vp0100110011_0 : Blocks := edgeBlocks% "full/vectors/0100110011-V-0000.bin"
private noncomputable def vp0100110011_1 : Blocks := edgeBlocks% "full/vectors/0100110011-V-0001.bin"
noncomputable def vp0100110011 : Blocks := (Blocks.join vp0100110011_0 vp0100110011_1)
private theorem bp01001100110 : Branch 0 (-2455761639/8000000 : ℚ) vp0100110011 := by
  apply branch_left_normalized (c:=vp01001100110) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-2455761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2455761639/4000000 : ℚ) by norm_num]
  exact coverp01001100110
private noncomputable def ep01001100111_0 : Blocks := edgeBlocks% "full/vectors/01001100111-E-0000.bin"
private noncomputable def ep01001100111_1 : Blocks := edgeBlocks% "full/vectors/01001100111-E-0001.bin"
noncomputable def ep01001100111 : Blocks := (Blocks.join ep01001100111_0 ep01001100111_1)
private theorem idp01001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100110011.list =
    C ((2:ℤ)^202) * horner X vp01001100111.list + horner X ep01001100111.list := by
  exact edge_identity (B := (2:ℤ)^362) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001100111 : Branch 1 (-2455761639/8000000 : ℚ) vp0100110011 := by
  apply branch_checked idp01001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2455761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2459761639/4000000 : ℚ) by norm_num]
  exact coverp01001100111
theorem coverp0100110011 : Covers (-2455761639/8000000 : ℚ) vp0100110011 := join_branches bp01001100110 bp01001100111
private noncomputable def vp010011001011_0 : Blocks := edgeBlocks% "full/vectors/010011001011-V-0000.bin"
noncomputable def vp010011001011 : Blocks := vp010011001011_0
theorem coverp010011001011 : Covers (-2453761639/2000000 : ℚ) vp010011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp010011001010_0 : Blocks := edgeBlocks% "full/vectors/010011001010-V-0000.bin"
noncomputable def vp010011001010 : Blocks := vp010011001010_0
theorem coverp010011001010 : Covers (-2451761639/2000000 : ℚ) vp010011001010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001100101_0 : Blocks := edgeBlocks% "full/vectors/01001100101-V-0000.bin"
noncomputable def vp01001100101 : Blocks := vp01001100101_0
private theorem bp010011001010 : Branch 0 (-2451761639/4000000 : ℚ) vp01001100101 := by
  apply branch_left_normalized (c:=vp010011001010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2451761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2451761639/2000000 : ℚ) by norm_num]
  exact coverp010011001010
private noncomputable def ep010011001011_0 : Blocks := edgeBlocks% "full/vectors/010011001011-E-0000.bin"
noncomputable def ep010011001011 : Blocks := ep010011001011_0
private theorem idp010011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001100101.list =
    C ((2:ℤ)^112) * horner X vp010011001011.list + horner X ep010011001011.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011001011 : Branch 1 (-2451761639/4000000 : ℚ) vp01001100101 := by
  apply branch_checked idp010011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2451761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2453761639/2000000 : ℚ) by norm_num]
  exact coverp010011001011
theorem coverp01001100101 : Covers (-2451761639/4000000 : ℚ) vp01001100101 := join_branches bp010011001010 bp010011001011
private noncomputable def vp010011001001_0 : Blocks := edgeBlocks% "full/vectors/010011001001-V-0000.bin"
noncomputable def vp010011001001 : Blocks := vp010011001001_0
theorem coverp010011001001 : Covers (-2449761639/2000000 : ℚ) vp010011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp010011001000_0 : Blocks := edgeBlocks% "full/vectors/010011001000-V-0000.bin"
noncomputable def vp010011001000 : Blocks := vp010011001000_0
theorem coverp010011001000 : Covers (-2447761639/2000000 : ℚ) vp010011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001100100_0 : Blocks := edgeBlocks% "full/vectors/01001100100-V-0000.bin"
noncomputable def vp01001100100 : Blocks := vp01001100100_0
private theorem bp010011001000 : Branch 0 (-2447761639/4000000 : ℚ) vp01001100100 := by
  apply branch_left_normalized (c:=vp010011001000) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2447761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2447761639/2000000 : ℚ) by norm_num]
  exact coverp010011001000
private noncomputable def ep010011001001_0 : Blocks := edgeBlocks% "full/vectors/010011001001-E-0000.bin"
noncomputable def ep010011001001 : Blocks := ep010011001001_0
private theorem idp010011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001100100.list =
    C ((2:ℤ)^114) * horner X vp010011001001.list + horner X ep010011001001.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011001001 : Branch 1 (-2447761639/4000000 : ℚ) vp01001100100 := by
  apply branch_checked idp010011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2447761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2449761639/2000000 : ℚ) by norm_num]
  exact coverp010011001001
theorem coverp01001100100 : Covers (-2447761639/4000000 : ℚ) vp01001100100 := join_branches bp010011001000 bp010011001001
private noncomputable def vp0100110010_0 : Blocks := edgeBlocks% "full/vectors/0100110010-V-0000.bin"
private noncomputable def vp0100110010_1 : Blocks := edgeBlocks% "full/vectors/0100110010-V-0001.bin"
noncomputable def vp0100110010 : Blocks := (Blocks.join vp0100110010_0 vp0100110010_1)
private theorem bp01001100100 : Branch 0 (-2447761639/8000000 : ℚ) vp0100110010 := by
  apply branch_left_normalized (c:=vp01001100100) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-2447761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2447761639/4000000 : ℚ) by norm_num]
  exact coverp01001100100
private noncomputable def ep01001100101_0 : Blocks := edgeBlocks% "full/vectors/01001100101-E-0000.bin"
private noncomputable def ep01001100101_1 : Blocks := edgeBlocks% "full/vectors/01001100101-E-0001.bin"
noncomputable def ep01001100101 : Blocks := (Blocks.join ep01001100101_0 ep01001100101_1)
private theorem idp01001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100110010.list =
    C ((2:ℤ)^207) * horner X vp01001100101.list + horner X ep01001100101.list := by
  exact edge_identity (B := (2:ℤ)^367) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001100101 : Branch 1 (-2447761639/8000000 : ℚ) vp0100110010 := by
  apply branch_checked idp01001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2447761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2451761639/4000000 : ℚ) by norm_num]
  exact coverp01001100101
theorem coverp0100110010 : Covers (-2447761639/8000000 : ℚ) vp0100110010 := join_branches bp01001100100 bp01001100101
private noncomputable def vp010011001_0 : Blocks := edgeBlocks% "full/vectors/010011001-V-0000.bin"
private noncomputable def vp010011001_1 : Blocks := edgeBlocks% "full/vectors/010011001-V-0001.bin"
private noncomputable def vp010011001_2 : Blocks := edgeBlocks% "full/vectors/010011001-V-0002.bin"
noncomputable def vp010011001 : Blocks := (Blocks.join vp010011001_0 (Blocks.join vp010011001_1 vp010011001_2))
private theorem bp0100110010 : Branch 0 (-2447761639/16000000 : ℚ) vp010011001 := by
  apply branch_left_normalized (c:=vp0100110010) (k:=0) (m:=181) (by decide +kernel)
  rw [show 2*(-2447761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2447761639/8000000 : ℚ) by norm_num]
  exact coverp0100110010
private noncomputable def ep0100110011_0 : Blocks := edgeBlocks% "full/vectors/0100110011-E-0000.bin"
private noncomputable def ep0100110011_1 : Blocks := edgeBlocks% "full/vectors/0100110011-E-0001.bin"
private noncomputable def ep0100110011_2 : Blocks := edgeBlocks% "full/vectors/0100110011-E-0002.bin"
noncomputable def ep0100110011 : Blocks := (Blocks.join ep0100110011_0 (Blocks.join ep0100110011_1 ep0100110011_2))
private theorem idp0100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010011001.list =
    C ((2:ℤ)^389) * horner X vp0100110011.list + horner X ep0100110011.list := by
  exact edge_identity (B := (2:ℤ)^610) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100110011 : Branch 1 (-2447761639/16000000 : ℚ) vp010011001 := by
  apply branch_checked idp0100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2447761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2455761639/8000000 : ℚ) by norm_num]
  exact coverp0100110011
theorem coverp010011001 : Covers (-2447761639/16000000 : ℚ) vp010011001 := join_branches bp0100110010 bp0100110011
private noncomputable def vp010011000111_0 : Blocks := edgeBlocks% "full/vectors/010011000111-V-0000.bin"
noncomputable def vp010011000111 : Blocks := vp010011000111_0
theorem coverp010011000111 : Covers (-2445761639/2000000 : ℚ) vp010011000111 := cover_leaf (by decide +kernel)
private noncomputable def vp010011000110_0 : Blocks := edgeBlocks% "full/vectors/010011000110-V-0000.bin"
noncomputable def vp010011000110 : Blocks := vp010011000110_0
theorem coverp010011000110 : Covers (-2443761639/2000000 : ℚ) vp010011000110 := cover_leaf (by decide +kernel)
private noncomputable def vp01001100011_0 : Blocks := edgeBlocks% "full/vectors/01001100011-V-0000.bin"
noncomputable def vp01001100011 : Blocks := vp01001100011_0
private theorem bp010011000110 : Branch 0 (-2443761639/4000000 : ℚ) vp01001100011 := by
  apply branch_left_normalized (c:=vp010011000110) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2443761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2443761639/2000000 : ℚ) by norm_num]
  exact coverp010011000110
private noncomputable def ep010011000111_0 : Blocks := edgeBlocks% "full/vectors/010011000111-E-0000.bin"
noncomputable def ep010011000111 : Blocks := ep010011000111_0
private theorem idp010011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001100011.list =
    C ((2:ℤ)^112) * horner X vp010011000111.list + horner X ep010011000111.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011000111 : Branch 1 (-2443761639/4000000 : ℚ) vp01001100011 := by
  apply branch_checked idp010011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2443761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2445761639/2000000 : ℚ) by norm_num]
  exact coverp010011000111
theorem coverp01001100011 : Covers (-2443761639/4000000 : ℚ) vp01001100011 := join_branches bp010011000110 bp010011000111
private noncomputable def vp010011000101_0 : Blocks := edgeBlocks% "full/vectors/010011000101-V-0000.bin"
noncomputable def vp010011000101 : Blocks := vp010011000101_0
theorem coverp010011000101 : Covers (-2441761639/2000000 : ℚ) vp010011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp010011000100_0 : Blocks := edgeBlocks% "full/vectors/010011000100-V-0000.bin"
noncomputable def vp010011000100 : Blocks := vp010011000100_0
theorem coverp010011000100 : Covers (-2439761639/2000000 : ℚ) vp010011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp01001100010_0 : Blocks := edgeBlocks% "full/vectors/01001100010-V-0000.bin"
noncomputable def vp01001100010 : Blocks := vp01001100010_0
private theorem bp010011000100 : Branch 0 (-2439761639/4000000 : ℚ) vp01001100010 := by
  apply branch_left_normalized (c:=vp010011000100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2439761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2439761639/2000000 : ℚ) by norm_num]
  exact coverp010011000100
private noncomputable def ep010011000101_0 : Blocks := edgeBlocks% "full/vectors/010011000101-E-0000.bin"
noncomputable def ep010011000101 : Blocks := ep010011000101_0
private theorem idp010011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001100010.list =
    C ((2:ℤ)^113) * horner X vp010011000101.list + horner X ep010011000101.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011000101 : Branch 1 (-2439761639/4000000 : ℚ) vp01001100010 := by
  apply branch_checked idp010011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2439761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2441761639/2000000 : ℚ) by norm_num]
  exact coverp010011000101
theorem coverp01001100010 : Covers (-2439761639/4000000 : ℚ) vp01001100010 := join_branches bp010011000100 bp010011000101
private noncomputable def vp0100110001_0 : Blocks := edgeBlocks% "full/vectors/0100110001-V-0000.bin"
private noncomputable def vp0100110001_1 : Blocks := edgeBlocks% "full/vectors/0100110001-V-0001.bin"
noncomputable def vp0100110001 : Blocks := (Blocks.join vp0100110001_0 vp0100110001_1)
private theorem bp01001100010 : Branch 0 (-2439761639/8000000 : ℚ) vp0100110001 := by
  apply branch_left_normalized (c:=vp01001100010) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-2439761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2439761639/4000000 : ℚ) by norm_num]
  exact coverp01001100010
private noncomputable def ep01001100011_0 : Blocks := edgeBlocks% "full/vectors/01001100011-E-0000.bin"
private noncomputable def ep01001100011_1 : Blocks := edgeBlocks% "full/vectors/01001100011-E-0001.bin"
noncomputable def ep01001100011 : Blocks := (Blocks.join ep01001100011_0 ep01001100011_1)
private theorem idp01001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100110001.list =
    C ((2:ℤ)^204) * horner X vp01001100011.list + horner X ep01001100011.list := by
  exact edge_identity (B := (2:ℤ)^366) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001100011 : Branch 1 (-2439761639/8000000 : ℚ) vp0100110001 := by
  apply branch_checked idp01001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2439761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2443761639/4000000 : ℚ) by norm_num]
  exact coverp01001100011
theorem coverp0100110001 : Covers (-2439761639/8000000 : ℚ) vp0100110001 := join_branches bp01001100010 bp01001100011
private noncomputable def vp010011000011_0 : Blocks := edgeBlocks% "full/vectors/010011000011-V-0000.bin"
noncomputable def vp010011000011 : Blocks := vp010011000011_0
theorem coverp010011000011 : Covers (-2437761639/2000000 : ℚ) vp010011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp010011000010_0 : Blocks := edgeBlocks% "full/vectors/010011000010-V-0000.bin"
noncomputable def vp010011000010 : Blocks := vp010011000010_0
theorem coverp010011000010 : Covers (-2435761639/2000000 : ℚ) vp010011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp01001100001_0 : Blocks := edgeBlocks% "full/vectors/01001100001-V-0000.bin"
noncomputable def vp01001100001 : Blocks := vp01001100001_0
private theorem bp010011000010 : Branch 0 (-2435761639/4000000 : ℚ) vp01001100001 := by
  apply branch_left_normalized (c:=vp010011000010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2435761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2435761639/2000000 : ℚ) by norm_num]
  exact coverp010011000010
private noncomputable def ep010011000011_0 : Blocks := edgeBlocks% "full/vectors/010011000011-E-0000.bin"
noncomputable def ep010011000011 : Blocks := ep010011000011_0
private theorem idp010011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001100001.list =
    C ((2:ℤ)^113) * horner X vp010011000011.list + horner X ep010011000011.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011000011 : Branch 1 (-2435761639/4000000 : ℚ) vp01001100001 := by
  apply branch_checked idp010011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2435761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2437761639/2000000 : ℚ) by norm_num]
  exact coverp010011000011
theorem coverp01001100001 : Covers (-2435761639/4000000 : ℚ) vp01001100001 := join_branches bp010011000010 bp010011000011
private noncomputable def vp010011000001_0 : Blocks := edgeBlocks% "full/vectors/010011000001-V-0000.bin"
noncomputable def vp010011000001 : Blocks := vp010011000001_0
theorem coverp010011000001 : Covers (-2433761639/2000000 : ℚ) vp010011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp010011000000_0 : Blocks := edgeBlocks% "full/vectors/010011000000-V-0000.bin"
noncomputable def vp010011000000 : Blocks := vp010011000000_0
theorem coverp010011000000 : Covers (-2431761639/2000000 : ℚ) vp010011000000 := cover_leaf (by decide +kernel)
private noncomputable def vp01001100000_0 : Blocks := edgeBlocks% "full/vectors/01001100000-V-0000.bin"
noncomputable def vp01001100000 : Blocks := vp01001100000_0
private theorem bp010011000000 : Branch 0 (-2431761639/4000000 : ℚ) vp01001100000 := by
  apply branch_left_normalized (c:=vp010011000000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2431761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2431761639/2000000 : ℚ) by norm_num]
  exact coverp010011000000
private noncomputable def ep010011000001_0 : Blocks := edgeBlocks% "full/vectors/010011000001-E-0000.bin"
noncomputable def ep010011000001 : Blocks := ep010011000001_0
private theorem idp010011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001100000.list =
    C ((2:ℤ)^112) * horner X vp010011000001.list + horner X ep010011000001.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011000001 : Branch 1 (-2431761639/4000000 : ℚ) vp01001100000 := by
  apply branch_checked idp010011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2431761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2433761639/2000000 : ℚ) by norm_num]
  exact coverp010011000001
theorem coverp01001100000 : Covers (-2431761639/4000000 : ℚ) vp01001100000 := join_branches bp010011000000 bp010011000001
private noncomputable def vp0100110000_0 : Blocks := edgeBlocks% "full/vectors/0100110000-V-0000.bin"
private noncomputable def vp0100110000_1 : Blocks := edgeBlocks% "full/vectors/0100110000-V-0001.bin"
noncomputable def vp0100110000 : Blocks := (Blocks.join vp0100110000_0 vp0100110000_1)
private theorem bp01001100000 : Branch 0 (-2431761639/8000000 : ℚ) vp0100110000 := by
  apply branch_left_normalized (c:=vp01001100000) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-2431761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2431761639/4000000 : ℚ) by norm_num]
  exact coverp01001100000
private noncomputable def ep01001100001_0 : Blocks := edgeBlocks% "full/vectors/01001100001-E-0000.bin"
private noncomputable def ep01001100001_1 : Blocks := edgeBlocks% "full/vectors/01001100001-E-0001.bin"
noncomputable def ep01001100001 : Blocks := (Blocks.join ep01001100001_0 ep01001100001_1)
private theorem idp01001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100110000.list =
    C ((2:ℤ)^204) * horner X vp01001100001.list + horner X ep01001100001.list := by
  exact edge_identity (B := (2:ℤ)^367) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001100001 : Branch 1 (-2431761639/8000000 : ℚ) vp0100110000 := by
  apply branch_checked idp01001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2431761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2435761639/4000000 : ℚ) by norm_num]
  exact coverp01001100001
theorem coverp0100110000 : Covers (-2431761639/8000000 : ℚ) vp0100110000 := join_branches bp01001100000 bp01001100001
private noncomputable def vp010011000_0 : Blocks := edgeBlocks% "full/vectors/010011000-V-0000.bin"
private noncomputable def vp010011000_1 : Blocks := edgeBlocks% "full/vectors/010011000-V-0001.bin"
private noncomputable def vp010011000_2 : Blocks := edgeBlocks% "full/vectors/010011000-V-0002.bin"
noncomputable def vp010011000 : Blocks := (Blocks.join vp010011000_0 (Blocks.join vp010011000_1 vp010011000_2))
private theorem bp0100110000 : Branch 0 (-2431761639/16000000 : ℚ) vp010011000 := by
  apply branch_left_normalized (c:=vp0100110000) (k:=0) (m:=181) (by decide +kernel)
  rw [show 2*(-2431761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2431761639/8000000 : ℚ) by norm_num]
  exact coverp0100110000
private noncomputable def ep0100110001_0 : Blocks := edgeBlocks% "full/vectors/0100110001-E-0000.bin"
private noncomputable def ep0100110001_1 : Blocks := edgeBlocks% "full/vectors/0100110001-E-0001.bin"
private noncomputable def ep0100110001_2 : Blocks := edgeBlocks% "full/vectors/0100110001-E-0002.bin"
noncomputable def ep0100110001 : Blocks := (Blocks.join ep0100110001_0 (Blocks.join ep0100110001_1 ep0100110001_2))
private theorem idp0100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010011000.list =
    C ((2:ℤ)^386) * horner X vp0100110001.list + horner X ep0100110001.list := by
  exact edge_identity (B := (2:ℤ)^610) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100110001 : Branch 1 (-2431761639/16000000 : ℚ) vp010011000 := by
  apply branch_checked idp0100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2431761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2439761639/8000000 : ℚ) by norm_num]
  exact coverp0100110001
theorem coverp010011000 : Covers (-2431761639/16000000 : ℚ) vp010011000 := join_branches bp0100110000 bp0100110001
private noncomputable def vp01001100_0 : Blocks := edgeBlocks% "full/vectors/01001100-V-0000.bin"
private noncomputable def vp01001100_1 : Blocks := edgeBlocks% "full/vectors/01001100-V-0001.bin"
private noncomputable def vp01001100_2 : Blocks := edgeBlocks% "full/vectors/01001100-V-0002.bin"
private noncomputable def vp01001100_3 : Blocks := edgeBlocks% "full/vectors/01001100-V-0003.bin"
private noncomputable def vp01001100_4 : Blocks := edgeBlocks% "full/vectors/01001100-V-0004.bin"
private noncomputable def vp01001100_5 : Blocks := edgeBlocks% "full/vectors/01001100-V-0005.bin"
noncomputable def vp01001100 : Blocks := (Blocks.join (Blocks.join vp01001100_0 (Blocks.join vp01001100_1 vp01001100_2)) (Blocks.join vp01001100_3 (Blocks.join vp01001100_4 vp01001100_5)))
private theorem bp010011000 : Branch 0 (-2431761639/32000000 : ℚ) vp01001100 := by
  apply branch_left_normalized (c:=vp010011000) (k:=0) (m:=339) (by decide +kernel)
  rw [show 2*(-2431761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2431761639/16000000 : ℚ) by norm_num]
  exact coverp010011000
private noncomputable def ep010011001_0 : Blocks := edgeBlocks% "full/vectors/010011001-E-0000.bin"
private noncomputable def ep010011001_1 : Blocks := edgeBlocks% "full/vectors/010011001-E-0001.bin"
private noncomputable def ep010011001_2 : Blocks := edgeBlocks% "full/vectors/010011001-E-0002.bin"
private noncomputable def ep010011001_3 : Blocks := edgeBlocks% "full/vectors/010011001-E-0003.bin"
private noncomputable def ep010011001_4 : Blocks := edgeBlocks% "full/vectors/010011001-E-0004.bin"
private noncomputable def ep010011001_5 : Blocks := edgeBlocks% "full/vectors/010011001-E-0005.bin"
noncomputable def ep010011001 : Blocks := (Blocks.join (Blocks.join ep010011001_0 (Blocks.join ep010011001_1 ep010011001_2)) (Blocks.join ep010011001_3 (Blocks.join ep010011001_4 ep010011001_5)))
private theorem idp010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01001100.list =
    C ((2:ℤ)^748) * horner X vp010011001.list + horner X ep010011001.list := by
  exact edge_identity (B := (2:ℤ)^1094) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010011001 : Branch 1 (-2431761639/32000000 : ℚ) vp01001100 := by
  apply branch_checked idp010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2431761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2447761639/16000000 : ℚ) by norm_num]
  exact coverp010011001
theorem coverp01001100 : Covers (-2431761639/32000000 : ℚ) vp01001100 := join_branches bp010011000 bp010011001
private noncomputable def vp0100110_0 : Blocks := edgeBlocks% "full/vectors/0100110-V-0000.bin"
private noncomputable def vp0100110_1 : Blocks := edgeBlocks% "full/vectors/0100110-V-0001.bin"
private noncomputable def vp0100110_2 : Blocks := edgeBlocks% "full/vectors/0100110-V-0002.bin"
private noncomputable def vp0100110_3 : Blocks := edgeBlocks% "full/vectors/0100110-V-0003.bin"
private noncomputable def vp0100110_4 : Blocks := edgeBlocks% "full/vectors/0100110-V-0004.bin"
private noncomputable def vp0100110_5 : Blocks := edgeBlocks% "full/vectors/0100110-V-0005.bin"
private noncomputable def vp0100110_6 : Blocks := edgeBlocks% "full/vectors/0100110-V-0006.bin"
private noncomputable def vp0100110_7 : Blocks := edgeBlocks% "full/vectors/0100110-V-0007.bin"
private noncomputable def vp0100110_8 : Blocks := edgeBlocks% "full/vectors/0100110-V-0008.bin"
private noncomputable def vp0100110_9 : Blocks := edgeBlocks% "full/vectors/0100110-V-0009.bin"
noncomputable def vp0100110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0100110_0 vp0100110_1) (Blocks.join vp0100110_2 (Blocks.join vp0100110_3 vp0100110_4))) (Blocks.join (Blocks.join vp0100110_5 vp0100110_6) (Blocks.join vp0100110_7 (Blocks.join vp0100110_8 vp0100110_9))))
private theorem bp01001100 : Branch 0 (-2431761639/64000000 : ℚ) vp0100110 := by
  apply branch_left_normalized (c:=vp01001100) (k:=0) (m:=655) (by decide +kernel)
  rw [show 2*(-2431761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2431761639/32000000 : ℚ) by norm_num]
  exact coverp01001100
private noncomputable def ep01001101_0 : Blocks := edgeBlocks% "full/vectors/01001101-E-0000.bin"
private noncomputable def ep01001101_1 : Blocks := edgeBlocks% "full/vectors/01001101-E-0001.bin"
private noncomputable def ep01001101_2 : Blocks := edgeBlocks% "full/vectors/01001101-E-0002.bin"
private noncomputable def ep01001101_3 : Blocks := edgeBlocks% "full/vectors/01001101-E-0003.bin"
private noncomputable def ep01001101_4 : Blocks := edgeBlocks% "full/vectors/01001101-E-0004.bin"
private noncomputable def ep01001101_5 : Blocks := edgeBlocks% "full/vectors/01001101-E-0005.bin"
private noncomputable def ep01001101_6 : Blocks := edgeBlocks% "full/vectors/01001101-E-0006.bin"
private noncomputable def ep01001101_7 : Blocks := edgeBlocks% "full/vectors/01001101-E-0007.bin"
private noncomputable def ep01001101_8 : Blocks := edgeBlocks% "full/vectors/01001101-E-0008.bin"
private noncomputable def ep01001101_9 : Blocks := edgeBlocks% "full/vectors/01001101-E-0009.bin"
noncomputable def ep01001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01001101_0 ep01001101_1) (Blocks.join ep01001101_2 (Blocks.join ep01001101_3 ep01001101_4))) (Blocks.join (Blocks.join ep01001101_5 ep01001101_6) (Blocks.join ep01001101_7 (Blocks.join ep01001101_8 ep01001101_9))))
private theorem idp01001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100110.list =
    C ((2:ℤ)^1460) * horner X vp01001101.list + horner X ep01001101.list := by
  exact edge_identity (B := (2:ℤ)^2048) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01001101 : Branch 1 (-2431761639/64000000 : ℚ) vp0100110 := by
  apply branch_checked idp01001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2431761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2463761639/32000000 : ℚ) by norm_num]
  exact coverp01001101
theorem coverp0100110 : Covers (-2431761639/64000000 : ℚ) vp0100110 := join_branches bp01001100 bp01001101
private noncomputable def vp010011_0 : Blocks := edgeBlocks% "full/vectors/010011-V-0000.bin"
private noncomputable def vp010011_1 : Blocks := edgeBlocks% "full/vectors/010011-V-0001.bin"
private noncomputable def vp010011_2 : Blocks := edgeBlocks% "full/vectors/010011-V-0002.bin"
private noncomputable def vp010011_3 : Blocks := edgeBlocks% "full/vectors/010011-V-0003.bin"
private noncomputable def vp010011_4 : Blocks := edgeBlocks% "full/vectors/010011-V-0004.bin"
private noncomputable def vp010011_5 : Blocks := edgeBlocks% "full/vectors/010011-V-0005.bin"
private noncomputable def vp010011_6 : Blocks := edgeBlocks% "full/vectors/010011-V-0006.bin"
private noncomputable def vp010011_7 : Blocks := edgeBlocks% "full/vectors/010011-V-0007.bin"
private noncomputable def vp010011_8 : Blocks := edgeBlocks% "full/vectors/010011-V-0008.bin"
private noncomputable def vp010011_9 : Blocks := edgeBlocks% "full/vectors/010011-V-0009.bin"
private noncomputable def vp010011_10 : Blocks := edgeBlocks% "full/vectors/010011-V-0010.bin"
private noncomputable def vp010011_11 : Blocks := edgeBlocks% "full/vectors/010011-V-0011.bin"
private noncomputable def vp010011_12 : Blocks := edgeBlocks% "full/vectors/010011-V-0012.bin"
private noncomputable def vp010011_13 : Blocks := edgeBlocks% "full/vectors/010011-V-0013.bin"
private noncomputable def vp010011_14 : Blocks := edgeBlocks% "full/vectors/010011-V-0014.bin"
private noncomputable def vp010011_15 : Blocks := edgeBlocks% "full/vectors/010011-V-0015.bin"
private noncomputable def vp010011_16 : Blocks := edgeBlocks% "full/vectors/010011-V-0016.bin"
private noncomputable def vp010011_17 : Blocks := edgeBlocks% "full/vectors/010011-V-0017.bin"
private noncomputable def vp010011_18 : Blocks := edgeBlocks% "full/vectors/010011-V-0018.bin"
private noncomputable def vp010011_19 : Blocks := edgeBlocks% "full/vectors/010011-V-0019.bin"
noncomputable def vp010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp010011_0 vp010011_1) (Blocks.join vp010011_2 (Blocks.join vp010011_3 vp010011_4))) (Blocks.join (Blocks.join vp010011_5 vp010011_6) (Blocks.join vp010011_7 (Blocks.join vp010011_8 vp010011_9)))) (Blocks.join (Blocks.join (Blocks.join vp010011_10 vp010011_11) (Blocks.join vp010011_12 (Blocks.join vp010011_13 vp010011_14))) (Blocks.join (Blocks.join vp010011_15 vp010011_16) (Blocks.join vp010011_17 (Blocks.join vp010011_18 vp010011_19)))))
private theorem bp0100110 : Branch 0 (-2431761639/128000000 : ℚ) vp010011 := by
  apply branch_left_normalized (c:=vp0100110) (k:=0) (m:=1273) (by decide +kernel)
  rw [show 2*(-2431761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-2431761639/64000000 : ℚ) by norm_num]
  exact coverp0100110
private noncomputable def ep0100111_0 : Blocks := edgeBlocks% "full/vectors/0100111-E-0000.bin"
private noncomputable def ep0100111_1 : Blocks := edgeBlocks% "full/vectors/0100111-E-0001.bin"
private noncomputable def ep0100111_2 : Blocks := edgeBlocks% "full/vectors/0100111-E-0002.bin"
private noncomputable def ep0100111_3 : Blocks := edgeBlocks% "full/vectors/0100111-E-0003.bin"
private noncomputable def ep0100111_4 : Blocks := edgeBlocks% "full/vectors/0100111-E-0004.bin"
private noncomputable def ep0100111_5 : Blocks := edgeBlocks% "full/vectors/0100111-E-0005.bin"
private noncomputable def ep0100111_6 : Blocks := edgeBlocks% "full/vectors/0100111-E-0006.bin"
private noncomputable def ep0100111_7 : Blocks := edgeBlocks% "full/vectors/0100111-E-0007.bin"
private noncomputable def ep0100111_8 : Blocks := edgeBlocks% "full/vectors/0100111-E-0008.bin"
private noncomputable def ep0100111_9 : Blocks := edgeBlocks% "full/vectors/0100111-E-0009.bin"
private noncomputable def ep0100111_10 : Blocks := edgeBlocks% "full/vectors/0100111-E-0010.bin"
private noncomputable def ep0100111_11 : Blocks := edgeBlocks% "full/vectors/0100111-E-0011.bin"
private noncomputable def ep0100111_12 : Blocks := edgeBlocks% "full/vectors/0100111-E-0012.bin"
private noncomputable def ep0100111_13 : Blocks := edgeBlocks% "full/vectors/0100111-E-0013.bin"
private noncomputable def ep0100111_14 : Blocks := edgeBlocks% "full/vectors/0100111-E-0014.bin"
private noncomputable def ep0100111_15 : Blocks := edgeBlocks% "full/vectors/0100111-E-0015.bin"
private noncomputable def ep0100111_16 : Blocks := edgeBlocks% "full/vectors/0100111-E-0016.bin"
private noncomputable def ep0100111_17 : Blocks := edgeBlocks% "full/vectors/0100111-E-0017.bin"
private noncomputable def ep0100111_18 : Blocks := edgeBlocks% "full/vectors/0100111-E-0018.bin"
private noncomputable def ep0100111_19 : Blocks := edgeBlocks% "full/vectors/0100111-E-0019.bin"
noncomputable def ep0100111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0100111_0 ep0100111_1) (Blocks.join ep0100111_2 (Blocks.join ep0100111_3 ep0100111_4))) (Blocks.join (Blocks.join ep0100111_5 ep0100111_6) (Blocks.join ep0100111_7 (Blocks.join ep0100111_8 ep0100111_9)))) (Blocks.join (Blocks.join (Blocks.join ep0100111_10 ep0100111_11) (Blocks.join ep0100111_12 (Blocks.join ep0100111_13 ep0100111_14))) (Blocks.join (Blocks.join ep0100111_15 ep0100111_16) (Blocks.join ep0100111_17 (Blocks.join ep0100111_18 ep0100111_19)))))
private theorem idp0100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010011.list =
    C ((2:ℤ)^2856) * horner X vp0100111.list + horner X ep0100111.list := by
  exact edge_identity (B := (2:ℤ)^3915) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100111 : Branch 1 (-2431761639/128000000 : ℚ) vp010011 := by
  apply branch_checked idp0100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2431761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-2495761639/64000000 : ℚ) by norm_num]
  exact coverp0100111
theorem coverp010011 : Covers (-2431761639/128000000 : ℚ) vp010011 := join_branches bp0100110 bp0100111
end NextProof.EdgeFull

