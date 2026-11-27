import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp01010111111_0 : Blocks := edgeBlocks% "full/vectors/01010111111-V-0000.bin"
noncomputable def vp01010111111 : Blocks := vp01010111111_0
theorem coverp01010111111 : Covers (-2811761639/4000000 : ℚ) vp01010111111 := cover_leaf (by decide +kernel)
private noncomputable def vp01010111110_0 : Blocks := edgeBlocks% "full/vectors/01010111110-V-0000.bin"
noncomputable def vp01010111110 : Blocks := vp01010111110_0
theorem coverp01010111110 : Covers (-2807761639/4000000 : ℚ) vp01010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0101011111_0 : Blocks := edgeBlocks% "full/vectors/0101011111-V-0000.bin"
private noncomputable def vp0101011111_1 : Blocks := edgeBlocks% "full/vectors/0101011111-V-0001.bin"
noncomputable def vp0101011111 : Blocks := (Blocks.join vp0101011111_0 vp0101011111_1)
private theorem bp01010111110 : Branch 0 (-2807761639/8000000 : ℚ) vp0101011111 := by
  apply branch_left_normalized (c:=vp01010111110) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-2807761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2807761639/4000000 : ℚ) by norm_num]
  exact coverp01010111110
private noncomputable def ep01010111111_0 : Blocks := edgeBlocks% "full/vectors/01010111111-E-0000.bin"
private noncomputable def ep01010111111_1 : Blocks := edgeBlocks% "full/vectors/01010111111-E-0001.bin"
noncomputable def ep01010111111 : Blocks := (Blocks.join ep01010111111_0 ep01010111111_1)
private theorem idp01010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101011111.list =
    C ((2:ℤ)^190) * horner X vp01010111111.list + horner X ep01010111111.list := by
  exact edge_identity (B := (2:ℤ)^337) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010111111 : Branch 1 (-2807761639/8000000 : ℚ) vp0101011111 := by
  apply branch_checked idp01010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2807761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2811761639/4000000 : ℚ) by norm_num]
  exact coverp01010111111
theorem coverp0101011111 : Covers (-2807761639/8000000 : ℚ) vp0101011111 := join_branches bp01010111110 bp01010111111
private noncomputable def vp01010111101_0 : Blocks := edgeBlocks% "full/vectors/01010111101-V-0000.bin"
noncomputable def vp01010111101 : Blocks := vp01010111101_0
theorem coverp01010111101 : Covers (-2803761639/4000000 : ℚ) vp01010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp01010111100_0 : Blocks := edgeBlocks% "full/vectors/01010111100-V-0000.bin"
noncomputable def vp01010111100 : Blocks := vp01010111100_0
theorem coverp01010111100 : Covers (-2799761639/4000000 : ℚ) vp01010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0101011110_0 : Blocks := edgeBlocks% "full/vectors/0101011110-V-0000.bin"
private noncomputable def vp0101011110_1 : Blocks := edgeBlocks% "full/vectors/0101011110-V-0001.bin"
noncomputable def vp0101011110 : Blocks := (Blocks.join vp0101011110_0 vp0101011110_1)
private theorem bp01010111100 : Branch 0 (-2799761639/8000000 : ℚ) vp0101011110 := by
  apply branch_left_normalized (c:=vp01010111100) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-2799761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2799761639/4000000 : ℚ) by norm_num]
  exact coverp01010111100
private noncomputable def ep01010111101_0 : Blocks := edgeBlocks% "full/vectors/01010111101-E-0000.bin"
private noncomputable def ep01010111101_1 : Blocks := edgeBlocks% "full/vectors/01010111101-E-0001.bin"
noncomputable def ep01010111101 : Blocks := (Blocks.join ep01010111101_0 ep01010111101_1)
private theorem idp01010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101011110.list =
    C ((2:ℤ)^191) * horner X vp01010111101.list + horner X ep01010111101.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010111101 : Branch 1 (-2799761639/8000000 : ℚ) vp0101011110 := by
  apply branch_checked idp01010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2799761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2803761639/4000000 : ℚ) by norm_num]
  exact coverp01010111101
theorem coverp0101011110 : Covers (-2799761639/8000000 : ℚ) vp0101011110 := join_branches bp01010111100 bp01010111101
private noncomputable def vp010101111_0 : Blocks := edgeBlocks% "full/vectors/010101111-V-0000.bin"
private noncomputable def vp010101111_1 : Blocks := edgeBlocks% "full/vectors/010101111-V-0001.bin"
private noncomputable def vp010101111_2 : Blocks := edgeBlocks% "full/vectors/010101111-V-0002.bin"
noncomputable def vp010101111 : Blocks := (Blocks.join vp010101111_0 (Blocks.join vp010101111_1 vp010101111_2))
private theorem bp0101011110 : Branch 0 (-2799761639/16000000 : ℚ) vp010101111 := by
  apply branch_left_normalized (c:=vp0101011110) (k:=0) (m:=166) (by decide +kernel)
  rw [show 2*(-2799761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2799761639/8000000 : ℚ) by norm_num]
  exact coverp0101011110
private noncomputable def ep0101011111_0 : Blocks := edgeBlocks% "full/vectors/0101011111-E-0000.bin"
private noncomputable def ep0101011111_1 : Blocks := edgeBlocks% "full/vectors/0101011111-E-0001.bin"
private noncomputable def ep0101011111_2 : Blocks := edgeBlocks% "full/vectors/0101011111-E-0002.bin"
noncomputable def ep0101011111 : Blocks := (Blocks.join ep0101011111_0 (Blocks.join ep0101011111_1 ep0101011111_2))
private theorem idp0101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010101111.list =
    C ((2:ℤ)^363) * horner X vp0101011111.list + horner X ep0101011111.list := by
  exact edge_identity (B := (2:ℤ)^567) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101011111 : Branch 1 (-2799761639/16000000 : ℚ) vp010101111 := by
  apply branch_checked idp0101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2799761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2807761639/8000000 : ℚ) by norm_num]
  exact coverp0101011111
theorem coverp010101111 : Covers (-2799761639/16000000 : ℚ) vp010101111 := join_branches bp0101011110 bp0101011111
private noncomputable def vp01010111011_0 : Blocks := edgeBlocks% "full/vectors/01010111011-V-0000.bin"
noncomputable def vp01010111011 : Blocks := vp01010111011_0
theorem coverp01010111011 : Covers (-2795761639/4000000 : ℚ) vp01010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp010101110101_0 : Blocks := edgeBlocks% "full/vectors/010101110101-V-0000.bin"
noncomputable def vp010101110101 : Blocks := vp010101110101_0
theorem coverp010101110101 : Covers (-2793761639/2000000 : ℚ) vp010101110101 := cover_leaf (by decide +kernel)
private noncomputable def vp010101110100_0 : Blocks := edgeBlocks% "full/vectors/010101110100-V-0000.bin"
noncomputable def vp010101110100 : Blocks := vp010101110100_0
theorem coverp010101110100 : Covers (-2791761639/2000000 : ℚ) vp010101110100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010111010_0 : Blocks := edgeBlocks% "full/vectors/01010111010-V-0000.bin"
noncomputable def vp01010111010 : Blocks := vp01010111010_0
private theorem bp010101110100 : Branch 0 (-2791761639/4000000 : ℚ) vp01010111010 := by
  apply branch_left_normalized (c:=vp010101110100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2791761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2791761639/2000000 : ℚ) by norm_num]
  exact coverp010101110100
private noncomputable def ep010101110101_0 : Blocks := edgeBlocks% "full/vectors/010101110101-E-0000.bin"
noncomputable def ep010101110101 : Blocks := ep010101110101_0
private theorem idp010101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010111010.list =
    C ((2:ℤ)^109) * horner X vp010101110101.list + horner X ep010101110101.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101110101 : Branch 1 (-2791761639/4000000 : ℚ) vp01010111010 := by
  apply branch_checked idp010101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2791761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2793761639/2000000 : ℚ) by norm_num]
  exact coverp010101110101
theorem coverp01010111010 : Covers (-2791761639/4000000 : ℚ) vp01010111010 := join_branches bp010101110100 bp010101110101
private noncomputable def vp0101011101_0 : Blocks := edgeBlocks% "full/vectors/0101011101-V-0000.bin"
private noncomputable def vp0101011101_1 : Blocks := edgeBlocks% "full/vectors/0101011101-V-0001.bin"
noncomputable def vp0101011101 : Blocks := (Blocks.join vp0101011101_0 vp0101011101_1)
private theorem bp01010111010 : Branch 0 (-2791761639/8000000 : ℚ) vp0101011101 := by
  apply branch_left_normalized (c:=vp01010111010) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-2791761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2791761639/4000000 : ℚ) by norm_num]
  exact coverp01010111010
private noncomputable def ep01010111011_0 : Blocks := edgeBlocks% "full/vectors/01010111011-E-0000.bin"
private noncomputable def ep01010111011_1 : Blocks := edgeBlocks% "full/vectors/01010111011-E-0001.bin"
noncomputable def ep01010111011 : Blocks := (Blocks.join ep01010111011_0 ep01010111011_1)
private theorem idp01010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101011101.list =
    C ((2:ℤ)^197) * horner X vp01010111011.list + horner X ep01010111011.list := by
  exact edge_identity (B := (2:ℤ)^350) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010111011 : Branch 1 (-2791761639/8000000 : ℚ) vp0101011101 := by
  apply branch_checked idp01010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2791761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2795761639/4000000 : ℚ) by norm_num]
  exact coverp01010111011
theorem coverp0101011101 : Covers (-2791761639/8000000 : ℚ) vp0101011101 := join_branches bp01010111010 bp01010111011
private noncomputable def vp010101110011_0 : Blocks := edgeBlocks% "full/vectors/010101110011-V-0000.bin"
noncomputable def vp010101110011 : Blocks := vp010101110011_0
theorem coverp010101110011 : Covers (-2789761639/2000000 : ℚ) vp010101110011 := cover_leaf (by decide +kernel)
private noncomputable def vp010101110010_0 : Blocks := edgeBlocks% "full/vectors/010101110010-V-0000.bin"
noncomputable def vp010101110010 : Blocks := vp010101110010_0
theorem coverp010101110010 : Covers (-2787761639/2000000 : ℚ) vp010101110010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010111001_0 : Blocks := edgeBlocks% "full/vectors/01010111001-V-0000.bin"
noncomputable def vp01010111001 : Blocks := vp01010111001_0
private theorem bp010101110010 : Branch 0 (-2787761639/4000000 : ℚ) vp01010111001 := by
  apply branch_left_normalized (c:=vp010101110010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2787761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2787761639/2000000 : ℚ) by norm_num]
  exact coverp010101110010
private noncomputable def ep010101110011_0 : Blocks := edgeBlocks% "full/vectors/010101110011-E-0000.bin"
noncomputable def ep010101110011 : Blocks := ep010101110011_0
private theorem idp010101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010111001.list =
    C ((2:ℤ)^106) * horner X vp010101110011.list + horner X ep010101110011.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101110011 : Branch 1 (-2787761639/4000000 : ℚ) vp01010111001 := by
  apply branch_checked idp010101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2787761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2789761639/2000000 : ℚ) by norm_num]
  exact coverp010101110011
theorem coverp01010111001 : Covers (-2787761639/4000000 : ℚ) vp01010111001 := join_branches bp010101110010 bp010101110011
private noncomputable def vp010101110001_0 : Blocks := edgeBlocks% "full/vectors/010101110001-V-0000.bin"
noncomputable def vp010101110001 : Blocks := vp010101110001_0
theorem coverp010101110001 : Covers (-2785761639/2000000 : ℚ) vp010101110001 := cover_leaf (by decide +kernel)
private noncomputable def vp010101110000_0 : Blocks := edgeBlocks% "full/vectors/010101110000-V-0000.bin"
noncomputable def vp010101110000 : Blocks := vp010101110000_0
theorem coverp010101110000 : Covers (-2783761639/2000000 : ℚ) vp010101110000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010111000_0 : Blocks := edgeBlocks% "full/vectors/01010111000-V-0000.bin"
noncomputable def vp01010111000 : Blocks := vp01010111000_0
private theorem bp010101110000 : Branch 0 (-2783761639/4000000 : ℚ) vp01010111000 := by
  apply branch_left_normalized (c:=vp010101110000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2783761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2783761639/2000000 : ℚ) by norm_num]
  exact coverp010101110000
private noncomputable def ep010101110001_0 : Blocks := edgeBlocks% "full/vectors/010101110001-E-0000.bin"
noncomputable def ep010101110001 : Blocks := ep010101110001_0
private theorem idp010101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010111000.list =
    C ((2:ℤ)^107) * horner X vp010101110001.list + horner X ep010101110001.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101110001 : Branch 1 (-2783761639/4000000 : ℚ) vp01010111000 := by
  apply branch_checked idp010101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2783761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2785761639/2000000 : ℚ) by norm_num]
  exact coverp010101110001
theorem coverp01010111000 : Covers (-2783761639/4000000 : ℚ) vp01010111000 := join_branches bp010101110000 bp010101110001
private noncomputable def vp0101011100_0 : Blocks := edgeBlocks% "full/vectors/0101011100-V-0000.bin"
private noncomputable def vp0101011100_1 : Blocks := edgeBlocks% "full/vectors/0101011100-V-0001.bin"
noncomputable def vp0101011100 : Blocks := (Blocks.join vp0101011100_0 vp0101011100_1)
private theorem bp01010111000 : Branch 0 (-2783761639/8000000 : ℚ) vp0101011100 := by
  apply branch_left_normalized (c:=vp01010111000) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-2783761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2783761639/4000000 : ℚ) by norm_num]
  exact coverp01010111000
private noncomputable def ep01010111001_0 : Blocks := edgeBlocks% "full/vectors/01010111001-E-0000.bin"
private noncomputable def ep01010111001_1 : Blocks := edgeBlocks% "full/vectors/01010111001-E-0001.bin"
noncomputable def ep01010111001 : Blocks := (Blocks.join ep01010111001_0 ep01010111001_1)
private theorem idp01010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101011100.list =
    C ((2:ℤ)^194) * horner X vp01010111001.list + horner X ep01010111001.list := by
  exact edge_identity (B := (2:ℤ)^350) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010111001 : Branch 1 (-2783761639/8000000 : ℚ) vp0101011100 := by
  apply branch_checked idp01010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2783761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2787761639/4000000 : ℚ) by norm_num]
  exact coverp01010111001
theorem coverp0101011100 : Covers (-2783761639/8000000 : ℚ) vp0101011100 := join_branches bp01010111000 bp01010111001
private noncomputable def vp010101110_0 : Blocks := edgeBlocks% "full/vectors/010101110-V-0000.bin"
private noncomputable def vp010101110_1 : Blocks := edgeBlocks% "full/vectors/010101110-V-0001.bin"
private noncomputable def vp010101110_2 : Blocks := edgeBlocks% "full/vectors/010101110-V-0002.bin"
noncomputable def vp010101110 : Blocks := (Blocks.join vp010101110_0 (Blocks.join vp010101110_1 vp010101110_2))
private theorem bp0101011100 : Branch 0 (-2783761639/16000000 : ℚ) vp010101110 := by
  apply branch_left_normalized (c:=vp0101011100) (k:=0) (m:=170) (by decide +kernel)
  rw [show 2*(-2783761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2783761639/8000000 : ℚ) by norm_num]
  exact coverp0101011100
private noncomputable def ep0101011101_0 : Blocks := edgeBlocks% "full/vectors/0101011101-E-0000.bin"
private noncomputable def ep0101011101_1 : Blocks := edgeBlocks% "full/vectors/0101011101-E-0001.bin"
private noncomputable def ep0101011101_2 : Blocks := edgeBlocks% "full/vectors/0101011101-E-0002.bin"
noncomputable def ep0101011101 : Blocks := (Blocks.join ep0101011101_0 (Blocks.join ep0101011101_1 ep0101011101_2))
private theorem idp0101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010101110.list =
    C ((2:ℤ)^365) * horner X vp0101011101.list + horner X ep0101011101.list := by
  exact edge_identity (B := (2:ℤ)^577) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101011101 : Branch 1 (-2783761639/16000000 : ℚ) vp010101110 := by
  apply branch_checked idp0101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2783761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2791761639/8000000 : ℚ) by norm_num]
  exact coverp0101011101
theorem coverp010101110 : Covers (-2783761639/16000000 : ℚ) vp010101110 := join_branches bp0101011100 bp0101011101
private noncomputable def vp01010111_0 : Blocks := edgeBlocks% "full/vectors/01010111-V-0000.bin"
private noncomputable def vp01010111_1 : Blocks := edgeBlocks% "full/vectors/01010111-V-0001.bin"
private noncomputable def vp01010111_2 : Blocks := edgeBlocks% "full/vectors/01010111-V-0002.bin"
private noncomputable def vp01010111_3 : Blocks := edgeBlocks% "full/vectors/01010111-V-0003.bin"
private noncomputable def vp01010111_4 : Blocks := edgeBlocks% "full/vectors/01010111-V-0004.bin"
noncomputable def vp01010111 : Blocks := (Blocks.join (Blocks.join vp01010111_0 vp01010111_1) (Blocks.join vp01010111_2 (Blocks.join vp01010111_3 vp01010111_4)))
private theorem bp010101110 : Branch 0 (-2783761639/32000000 : ℚ) vp01010111 := by
  apply branch_left_normalized (c:=vp010101110) (k:=0) (m:=318) (by decide +kernel)
  rw [show 2*(-2783761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2783761639/16000000 : ℚ) by norm_num]
  exact coverp010101110
private noncomputable def ep010101111_0 : Blocks := edgeBlocks% "full/vectors/010101111-E-0000.bin"
private noncomputable def ep010101111_1 : Blocks := edgeBlocks% "full/vectors/010101111-E-0001.bin"
private noncomputable def ep010101111_2 : Blocks := edgeBlocks% "full/vectors/010101111-E-0002.bin"
private noncomputable def ep010101111_3 : Blocks := edgeBlocks% "full/vectors/010101111-E-0003.bin"
private noncomputable def ep010101111_4 : Blocks := edgeBlocks% "full/vectors/010101111-E-0004.bin"
noncomputable def ep010101111 : Blocks := (Blocks.join (Blocks.join ep010101111_0 ep010101111_1) (Blocks.join ep010101111_2 (Blocks.join ep010101111_3 ep010101111_4)))
private theorem idp010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010111.list =
    C ((2:ℤ)^712) * horner X vp010101111.list + horner X ep010101111.list := by
  exact edge_identity (B := (2:ℤ)^1030) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101111 : Branch 1 (-2783761639/32000000 : ℚ) vp01010111 := by
  apply branch_checked idp010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2783761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2799761639/16000000 : ℚ) by norm_num]
  exact coverp010101111
theorem coverp01010111 : Covers (-2783761639/32000000 : ℚ) vp01010111 := join_branches bp010101110 bp010101111
private noncomputable def vp010101101111_0 : Blocks := edgeBlocks% "full/vectors/010101101111-V-0000.bin"
noncomputable def vp010101101111 : Blocks := vp010101101111_0
theorem coverp010101101111 : Covers (-2781761639/2000000 : ℚ) vp010101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp010101101110_0 : Blocks := edgeBlocks% "full/vectors/010101101110-V-0000.bin"
noncomputable def vp010101101110 : Blocks := vp010101101110_0
theorem coverp010101101110 : Covers (-2779761639/2000000 : ℚ) vp010101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010110111_0 : Blocks := edgeBlocks% "full/vectors/01010110111-V-0000.bin"
noncomputable def vp01010110111 : Blocks := vp01010110111_0
private theorem bp010101101110 : Branch 0 (-2779761639/4000000 : ℚ) vp01010110111 := by
  apply branch_left_normalized (c:=vp010101101110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2779761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2779761639/2000000 : ℚ) by norm_num]
  exact coverp010101101110
private noncomputable def ep010101101111_0 : Blocks := edgeBlocks% "full/vectors/010101101111-E-0000.bin"
noncomputable def ep010101101111 : Blocks := ep010101101111_0
private theorem idp010101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010110111.list =
    C ((2:ℤ)^107) * horner X vp010101101111.list + horner X ep010101101111.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101101111 : Branch 1 (-2779761639/4000000 : ℚ) vp01010110111 := by
  apply branch_checked idp010101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2779761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2781761639/2000000 : ℚ) by norm_num]
  exact coverp010101101111
theorem coverp01010110111 : Covers (-2779761639/4000000 : ℚ) vp01010110111 := join_branches bp010101101110 bp010101101111
private noncomputable def vp010101101101_0 : Blocks := edgeBlocks% "full/vectors/010101101101-V-0000.bin"
noncomputable def vp010101101101 : Blocks := vp010101101101_0
theorem coverp010101101101 : Covers (-2777761639/2000000 : ℚ) vp010101101101 := cover_leaf (by decide +kernel)
private noncomputable def vp010101101100_0 : Blocks := edgeBlocks% "full/vectors/010101101100-V-0000.bin"
noncomputable def vp010101101100 : Blocks := vp010101101100_0
theorem coverp010101101100 : Covers (-2775761639/2000000 : ℚ) vp010101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010110110_0 : Blocks := edgeBlocks% "full/vectors/01010110110-V-0000.bin"
noncomputable def vp01010110110 : Blocks := vp01010110110_0
private theorem bp010101101100 : Branch 0 (-2775761639/4000000 : ℚ) vp01010110110 := by
  apply branch_left_normalized (c:=vp010101101100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2775761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2775761639/2000000 : ℚ) by norm_num]
  exact coverp010101101100
private noncomputable def ep010101101101_0 : Blocks := edgeBlocks% "full/vectors/010101101101-E-0000.bin"
noncomputable def ep010101101101 : Blocks := ep010101101101_0
private theorem idp010101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010110110.list =
    C ((2:ℤ)^109) * horner X vp010101101101.list + horner X ep010101101101.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101101101 : Branch 1 (-2775761639/4000000 : ℚ) vp01010110110 := by
  apply branch_checked idp010101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2775761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2777761639/2000000 : ℚ) by norm_num]
  exact coverp010101101101
theorem coverp01010110110 : Covers (-2775761639/4000000 : ℚ) vp01010110110 := join_branches bp010101101100 bp010101101101
private noncomputable def vp0101011011_0 : Blocks := edgeBlocks% "full/vectors/0101011011-V-0000.bin"
private noncomputable def vp0101011011_1 : Blocks := edgeBlocks% "full/vectors/0101011011-V-0001.bin"
noncomputable def vp0101011011 : Blocks := (Blocks.join vp0101011011_0 vp0101011011_1)
private theorem bp01010110110 : Branch 0 (-2775761639/8000000 : ℚ) vp0101011011 := by
  apply branch_left_normalized (c:=vp01010110110) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-2775761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2775761639/4000000 : ℚ) by norm_num]
  exact coverp01010110110
private noncomputable def ep01010110111_0 : Blocks := edgeBlocks% "full/vectors/01010110111-E-0000.bin"
private noncomputable def ep01010110111_1 : Blocks := edgeBlocks% "full/vectors/01010110111-E-0001.bin"
noncomputable def ep01010110111 : Blocks := (Blocks.join ep01010110111_0 ep01010110111_1)
private theorem idp01010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101011011.list =
    C ((2:ℤ)^195) * horner X vp01010110111.list + horner X ep01010110111.list := by
  exact edge_identity (B := (2:ℤ)^351) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010110111 : Branch 1 (-2775761639/8000000 : ℚ) vp0101011011 := by
  apply branch_checked idp01010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2775761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2779761639/4000000 : ℚ) by norm_num]
  exact coverp01010110111
theorem coverp0101011011 : Covers (-2775761639/8000000 : ℚ) vp0101011011 := join_branches bp01010110110 bp01010110111
private noncomputable def vp010101101011_0 : Blocks := edgeBlocks% "full/vectors/010101101011-V-0000.bin"
noncomputable def vp010101101011 : Blocks := vp010101101011_0
theorem coverp010101101011 : Covers (-2773761639/2000000 : ℚ) vp010101101011 := cover_leaf (by decide +kernel)
private noncomputable def vp010101101010_0 : Blocks := edgeBlocks% "full/vectors/010101101010-V-0000.bin"
noncomputable def vp010101101010 : Blocks := vp010101101010_0
theorem coverp010101101010 : Covers (-2771761639/2000000 : ℚ) vp010101101010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010110101_0 : Blocks := edgeBlocks% "full/vectors/01010110101-V-0000.bin"
noncomputable def vp01010110101 : Blocks := vp01010110101_0
private theorem bp010101101010 : Branch 0 (-2771761639/4000000 : ℚ) vp01010110101 := by
  apply branch_left_normalized (c:=vp010101101010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2771761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2771761639/2000000 : ℚ) by norm_num]
  exact coverp010101101010
private noncomputable def ep010101101011_0 : Blocks := edgeBlocks% "full/vectors/010101101011-E-0000.bin"
noncomputable def ep010101101011 : Blocks := ep010101101011_0
private theorem idp010101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010110101.list =
    C ((2:ℤ)^109) * horner X vp010101101011.list + horner X ep010101101011.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101101011 : Branch 1 (-2771761639/4000000 : ℚ) vp01010110101 := by
  apply branch_checked idp010101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2771761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2773761639/2000000 : ℚ) by norm_num]
  exact coverp010101101011
theorem coverp01010110101 : Covers (-2771761639/4000000 : ℚ) vp01010110101 := join_branches bp010101101010 bp010101101011
private noncomputable def vp010101101001_0 : Blocks := edgeBlocks% "full/vectors/010101101001-V-0000.bin"
noncomputable def vp010101101001 : Blocks := vp010101101001_0
theorem coverp010101101001 : Covers (-2769761639/2000000 : ℚ) vp010101101001 := cover_leaf (by decide +kernel)
private noncomputable def vp010101101000_0 : Blocks := edgeBlocks% "full/vectors/010101101000-V-0000.bin"
noncomputable def vp010101101000 : Blocks := vp010101101000_0
theorem coverp010101101000 : Covers (-2767761639/2000000 : ℚ) vp010101101000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010110100_0 : Blocks := edgeBlocks% "full/vectors/01010110100-V-0000.bin"
noncomputable def vp01010110100 : Blocks := vp01010110100_0
private theorem bp010101101000 : Branch 0 (-2767761639/4000000 : ℚ) vp01010110100 := by
  apply branch_left_normalized (c:=vp010101101000) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2767761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2767761639/2000000 : ℚ) by norm_num]
  exact coverp010101101000
private noncomputable def ep010101101001_0 : Blocks := edgeBlocks% "full/vectors/010101101001-E-0000.bin"
noncomputable def ep010101101001 : Blocks := ep010101101001_0
private theorem idp010101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010110100.list =
    C ((2:ℤ)^108) * horner X vp010101101001.list + horner X ep010101101001.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101101001 : Branch 1 (-2767761639/4000000 : ℚ) vp01010110100 := by
  apply branch_checked idp010101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2767761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2769761639/2000000 : ℚ) by norm_num]
  exact coverp010101101001
theorem coverp01010110100 : Covers (-2767761639/4000000 : ℚ) vp01010110100 := join_branches bp010101101000 bp010101101001
private noncomputable def vp0101011010_0 : Blocks := edgeBlocks% "full/vectors/0101011010-V-0000.bin"
private noncomputable def vp0101011010_1 : Blocks := edgeBlocks% "full/vectors/0101011010-V-0001.bin"
noncomputable def vp0101011010 : Blocks := (Blocks.join vp0101011010_0 vp0101011010_1)
private theorem bp01010110100 : Branch 0 (-2767761639/8000000 : ℚ) vp0101011010 := by
  apply branch_left_normalized (c:=vp01010110100) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-2767761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2767761639/4000000 : ℚ) by norm_num]
  exact coverp01010110100
private noncomputable def ep01010110101_0 : Blocks := edgeBlocks% "full/vectors/01010110101-E-0000.bin"
private noncomputable def ep01010110101_1 : Blocks := edgeBlocks% "full/vectors/01010110101-E-0001.bin"
noncomputable def ep01010110101 : Blocks := (Blocks.join ep01010110101_0 ep01010110101_1)
private theorem idp01010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101011010.list =
    C ((2:ℤ)^195) * horner X vp01010110101.list + horner X ep01010110101.list := by
  exact edge_identity (B := (2:ℤ)^353) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010110101 : Branch 1 (-2767761639/8000000 : ℚ) vp0101011010 := by
  apply branch_checked idp01010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2767761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2771761639/4000000 : ℚ) by norm_num]
  exact coverp01010110101
theorem coverp0101011010 : Covers (-2767761639/8000000 : ℚ) vp0101011010 := join_branches bp01010110100 bp01010110101
private noncomputable def vp010101101_0 : Blocks := edgeBlocks% "full/vectors/010101101-V-0000.bin"
private noncomputable def vp010101101_1 : Blocks := edgeBlocks% "full/vectors/010101101-V-0001.bin"
private noncomputable def vp010101101_2 : Blocks := edgeBlocks% "full/vectors/010101101-V-0002.bin"
noncomputable def vp010101101 : Blocks := (Blocks.join vp010101101_0 (Blocks.join vp010101101_1 vp010101101_2))
private theorem bp0101011010 : Branch 0 (-2767761639/16000000 : ℚ) vp010101101 := by
  apply branch_left_normalized (c:=vp0101011010) (k:=0) (m:=171) (by decide +kernel)
  rw [show 2*(-2767761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2767761639/8000000 : ℚ) by norm_num]
  exact coverp0101011010
private noncomputable def ep0101011011_0 : Blocks := edgeBlocks% "full/vectors/0101011011-E-0000.bin"
private noncomputable def ep0101011011_1 : Blocks := edgeBlocks% "full/vectors/0101011011-E-0001.bin"
private noncomputable def ep0101011011_2 : Blocks := edgeBlocks% "full/vectors/0101011011-E-0002.bin"
noncomputable def ep0101011011 : Blocks := (Blocks.join ep0101011011_0 (Blocks.join ep0101011011_1 ep0101011011_2))
private theorem idp0101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010101101.list =
    C ((2:ℤ)^368) * horner X vp0101011011.list + horner X ep0101011011.list := by
  exact edge_identity (B := (2:ℤ)^581) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101011011 : Branch 1 (-2767761639/16000000 : ℚ) vp010101101 := by
  apply branch_checked idp0101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2767761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2775761639/8000000 : ℚ) by norm_num]
  exact coverp0101011011
theorem coverp010101101 : Covers (-2767761639/16000000 : ℚ) vp010101101 := join_branches bp0101011010 bp0101011011
private noncomputable def vp010101100111_0 : Blocks := edgeBlocks% "full/vectors/010101100111-V-0000.bin"
noncomputable def vp010101100111 : Blocks := vp010101100111_0
theorem coverp010101100111 : Covers (-2765761639/2000000 : ℚ) vp010101100111 := cover_leaf (by decide +kernel)
private noncomputable def vp010101100110_0 : Blocks := edgeBlocks% "full/vectors/010101100110-V-0000.bin"
noncomputable def vp010101100110 : Blocks := vp010101100110_0
theorem coverp010101100110 : Covers (-2763761639/2000000 : ℚ) vp010101100110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010110011_0 : Blocks := edgeBlocks% "full/vectors/01010110011-V-0000.bin"
noncomputable def vp01010110011 : Blocks := vp01010110011_0
private theorem bp010101100110 : Branch 0 (-2763761639/4000000 : ℚ) vp01010110011 := by
  apply branch_left_normalized (c:=vp010101100110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2763761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2763761639/2000000 : ℚ) by norm_num]
  exact coverp010101100110
private noncomputable def ep010101100111_0 : Blocks := edgeBlocks% "full/vectors/010101100111-E-0000.bin"
noncomputable def ep010101100111 : Blocks := ep010101100111_0
private theorem idp010101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010110011.list =
    C ((2:ℤ)^108) * horner X vp010101100111.list + horner X ep010101100111.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101100111 : Branch 1 (-2763761639/4000000 : ℚ) vp01010110011 := by
  apply branch_checked idp010101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2763761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2765761639/2000000 : ℚ) by norm_num]
  exact coverp010101100111
theorem coverp01010110011 : Covers (-2763761639/4000000 : ℚ) vp01010110011 := join_branches bp010101100110 bp010101100111
private noncomputable def vp010101100101_0 : Blocks := edgeBlocks% "full/vectors/010101100101-V-0000.bin"
noncomputable def vp010101100101 : Blocks := vp010101100101_0
theorem coverp010101100101 : Covers (-2761761639/2000000 : ℚ) vp010101100101 := cover_leaf (by decide +kernel)
private noncomputable def vp010101100100_0 : Blocks := edgeBlocks% "full/vectors/010101100100-V-0000.bin"
noncomputable def vp010101100100 : Blocks := vp010101100100_0
theorem coverp010101100100 : Covers (-2759761639/2000000 : ℚ) vp010101100100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010110010_0 : Blocks := edgeBlocks% "full/vectors/01010110010-V-0000.bin"
noncomputable def vp01010110010 : Blocks := vp01010110010_0
private theorem bp010101100100 : Branch 0 (-2759761639/4000000 : ℚ) vp01010110010 := by
  apply branch_left_normalized (c:=vp010101100100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2759761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2759761639/2000000 : ℚ) by norm_num]
  exact coverp010101100100
private noncomputable def ep010101100101_0 : Blocks := edgeBlocks% "full/vectors/010101100101-E-0000.bin"
noncomputable def ep010101100101 : Blocks := ep010101100101_0
private theorem idp010101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010110010.list =
    C ((2:ℤ)^109) * horner X vp010101100101.list + horner X ep010101100101.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101100101 : Branch 1 (-2759761639/4000000 : ℚ) vp01010110010 := by
  apply branch_checked idp010101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2759761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2761761639/2000000 : ℚ) by norm_num]
  exact coverp010101100101
theorem coverp01010110010 : Covers (-2759761639/4000000 : ℚ) vp01010110010 := join_branches bp010101100100 bp010101100101
private noncomputable def vp0101011001_0 : Blocks := edgeBlocks% "full/vectors/0101011001-V-0000.bin"
private noncomputable def vp0101011001_1 : Blocks := edgeBlocks% "full/vectors/0101011001-V-0001.bin"
noncomputable def vp0101011001 : Blocks := (Blocks.join vp0101011001_0 vp0101011001_1)
private theorem bp01010110010 : Branch 0 (-2759761639/8000000 : ℚ) vp0101011001 := by
  apply branch_left_normalized (c:=vp01010110010) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-2759761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2759761639/4000000 : ℚ) by norm_num]
  exact coverp01010110010
private noncomputable def ep01010110011_0 : Blocks := edgeBlocks% "full/vectors/01010110011-E-0000.bin"
private noncomputable def ep01010110011_1 : Blocks := edgeBlocks% "full/vectors/01010110011-E-0001.bin"
noncomputable def ep01010110011 : Blocks := (Blocks.join ep01010110011_0 ep01010110011_1)
private theorem idp01010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101011001.list =
    C ((2:ℤ)^195) * horner X vp01010110011.list + horner X ep01010110011.list := by
  exact edge_identity (B := (2:ℤ)^353) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010110011 : Branch 1 (-2759761639/8000000 : ℚ) vp0101011001 := by
  apply branch_checked idp01010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2759761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2763761639/4000000 : ℚ) by norm_num]
  exact coverp01010110011
theorem coverp0101011001 : Covers (-2759761639/8000000 : ℚ) vp0101011001 := join_branches bp01010110010 bp01010110011
private noncomputable def vp010101100011_0 : Blocks := edgeBlocks% "full/vectors/010101100011-V-0000.bin"
noncomputable def vp010101100011 : Blocks := vp010101100011_0
theorem coverp010101100011 : Covers (-2757761639/2000000 : ℚ) vp010101100011 := cover_leaf (by decide +kernel)
private noncomputable def vp010101100010_0 : Blocks := edgeBlocks% "full/vectors/010101100010-V-0000.bin"
noncomputable def vp010101100010 : Blocks := vp010101100010_0
theorem coverp010101100010 : Covers (-2755761639/2000000 : ℚ) vp010101100010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010110001_0 : Blocks := edgeBlocks% "full/vectors/01010110001-V-0000.bin"
noncomputable def vp01010110001 : Blocks := vp01010110001_0
private theorem bp010101100010 : Branch 0 (-2755761639/4000000 : ℚ) vp01010110001 := by
  apply branch_left_normalized (c:=vp010101100010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2755761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2755761639/2000000 : ℚ) by norm_num]
  exact coverp010101100010
private noncomputable def ep010101100011_0 : Blocks := edgeBlocks% "full/vectors/010101100011-E-0000.bin"
noncomputable def ep010101100011 : Blocks := ep010101100011_0
private theorem idp010101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010110001.list =
    C ((2:ℤ)^109) * horner X vp010101100011.list + horner X ep010101100011.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101100011 : Branch 1 (-2755761639/4000000 : ℚ) vp01010110001 := by
  apply branch_checked idp010101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2755761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2757761639/2000000 : ℚ) by norm_num]
  exact coverp010101100011
theorem coverp01010110001 : Covers (-2755761639/4000000 : ℚ) vp01010110001 := join_branches bp010101100010 bp010101100011
private noncomputable def vp010101100001_0 : Blocks := edgeBlocks% "full/vectors/010101100001-V-0000.bin"
noncomputable def vp010101100001 : Blocks := vp010101100001_0
theorem coverp010101100001 : Covers (-2753761639/2000000 : ℚ) vp010101100001 := cover_leaf (by decide +kernel)
private noncomputable def vp010101100000_0 : Blocks := edgeBlocks% "full/vectors/010101100000-V-0000.bin"
noncomputable def vp010101100000 : Blocks := vp010101100000_0
theorem coverp010101100000 : Covers (-2751761639/2000000 : ℚ) vp010101100000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010110000_0 : Blocks := edgeBlocks% "full/vectors/01010110000-V-0000.bin"
noncomputable def vp01010110000 : Blocks := vp01010110000_0
private theorem bp010101100000 : Branch 0 (-2751761639/4000000 : ℚ) vp01010110000 := by
  apply branch_left_normalized (c:=vp010101100000) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2751761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2751761639/2000000 : ℚ) by norm_num]
  exact coverp010101100000
private noncomputable def ep010101100001_0 : Blocks := edgeBlocks% "full/vectors/010101100001-E-0000.bin"
noncomputable def ep010101100001 : Blocks := ep010101100001_0
private theorem idp010101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010110000.list =
    C ((2:ℤ)^109) * horner X vp010101100001.list + horner X ep010101100001.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101100001 : Branch 1 (-2751761639/4000000 : ℚ) vp01010110000 := by
  apply branch_checked idp010101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2751761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2753761639/2000000 : ℚ) by norm_num]
  exact coverp010101100001
theorem coverp01010110000 : Covers (-2751761639/4000000 : ℚ) vp01010110000 := join_branches bp010101100000 bp010101100001
private noncomputable def vp0101011000_0 : Blocks := edgeBlocks% "full/vectors/0101011000-V-0000.bin"
private noncomputable def vp0101011000_1 : Blocks := edgeBlocks% "full/vectors/0101011000-V-0001.bin"
noncomputable def vp0101011000 : Blocks := (Blocks.join vp0101011000_0 vp0101011000_1)
private theorem bp01010110000 : Branch 0 (-2751761639/8000000 : ℚ) vp0101011000 := by
  apply branch_left_normalized (c:=vp01010110000) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-2751761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2751761639/4000000 : ℚ) by norm_num]
  exact coverp01010110000
private noncomputable def ep01010110001_0 : Blocks := edgeBlocks% "full/vectors/01010110001-E-0000.bin"
private noncomputable def ep01010110001_1 : Blocks := edgeBlocks% "full/vectors/01010110001-E-0001.bin"
noncomputable def ep01010110001 : Blocks := (Blocks.join ep01010110001_0 ep01010110001_1)
private theorem idp01010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101011000.list =
    C ((2:ℤ)^196) * horner X vp01010110001.list + horner X ep01010110001.list := by
  exact edge_identity (B := (2:ℤ)^354) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010110001 : Branch 1 (-2751761639/8000000 : ℚ) vp0101011000 := by
  apply branch_checked idp01010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2751761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2755761639/4000000 : ℚ) by norm_num]
  exact coverp01010110001
theorem coverp0101011000 : Covers (-2751761639/8000000 : ℚ) vp0101011000 := join_branches bp01010110000 bp01010110001
private noncomputable def vp010101100_0 : Blocks := edgeBlocks% "full/vectors/010101100-V-0000.bin"
private noncomputable def vp010101100_1 : Blocks := edgeBlocks% "full/vectors/010101100-V-0001.bin"
private noncomputable def vp010101100_2 : Blocks := edgeBlocks% "full/vectors/010101100-V-0002.bin"
noncomputable def vp010101100 : Blocks := (Blocks.join vp010101100_0 (Blocks.join vp010101100_1 vp010101100_2))
private theorem bp0101011000 : Branch 0 (-2751761639/16000000 : ℚ) vp010101100 := by
  apply branch_left_normalized (c:=vp0101011000) (k:=0) (m:=172) (by decide +kernel)
  rw [show 2*(-2751761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2751761639/8000000 : ℚ) by norm_num]
  exact coverp0101011000
private noncomputable def ep0101011001_0 : Blocks := edgeBlocks% "full/vectors/0101011001-E-0000.bin"
private noncomputable def ep0101011001_1 : Blocks := edgeBlocks% "full/vectors/0101011001-E-0001.bin"
private noncomputable def ep0101011001_2 : Blocks := edgeBlocks% "full/vectors/0101011001-E-0002.bin"
noncomputable def ep0101011001 : Blocks := (Blocks.join ep0101011001_0 (Blocks.join ep0101011001_1 ep0101011001_2))
private theorem idp0101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010101100.list =
    C ((2:ℤ)^368) * horner X vp0101011001.list + horner X ep0101011001.list := by
  exact edge_identity (B := (2:ℤ)^582) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101011001 : Branch 1 (-2751761639/16000000 : ℚ) vp010101100 := by
  apply branch_checked idp0101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2751761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2759761639/8000000 : ℚ) by norm_num]
  exact coverp0101011001
theorem coverp010101100 : Covers (-2751761639/16000000 : ℚ) vp010101100 := join_branches bp0101011000 bp0101011001
private noncomputable def vp01010110_0 : Blocks := edgeBlocks% "full/vectors/01010110-V-0000.bin"
private noncomputable def vp01010110_1 : Blocks := edgeBlocks% "full/vectors/01010110-V-0001.bin"
private noncomputable def vp01010110_2 : Blocks := edgeBlocks% "full/vectors/01010110-V-0002.bin"
private noncomputable def vp01010110_3 : Blocks := edgeBlocks% "full/vectors/01010110-V-0003.bin"
private noncomputable def vp01010110_4 : Blocks := edgeBlocks% "full/vectors/01010110-V-0004.bin"
noncomputable def vp01010110 : Blocks := (Blocks.join (Blocks.join vp01010110_0 vp01010110_1) (Blocks.join vp01010110_2 (Blocks.join vp01010110_3 vp01010110_4)))
private theorem bp010101100 : Branch 0 (-2751761639/32000000 : ℚ) vp01010110 := by
  apply branch_left_normalized (c:=vp010101100) (k:=0) (m:=321) (by decide +kernel)
  rw [show 2*(-2751761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2751761639/16000000 : ℚ) by norm_num]
  exact coverp010101100
private noncomputable def ep010101101_0 : Blocks := edgeBlocks% "full/vectors/010101101-E-0000.bin"
private noncomputable def ep010101101_1 : Blocks := edgeBlocks% "full/vectors/010101101-E-0001.bin"
private noncomputable def ep010101101_2 : Blocks := edgeBlocks% "full/vectors/010101101-E-0002.bin"
private noncomputable def ep010101101_3 : Blocks := edgeBlocks% "full/vectors/010101101-E-0003.bin"
private noncomputable def ep010101101_4 : Blocks := edgeBlocks% "full/vectors/010101101-E-0004.bin"
noncomputable def ep010101101 : Blocks := (Blocks.join (Blocks.join ep010101101_0 ep010101101_1) (Blocks.join ep010101101_2 (Blocks.join ep010101101_3 ep010101101_4)))
private theorem idp010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010110.list =
    C ((2:ℤ)^710) * horner X vp010101101.list + horner X ep010101101.list := by
  exact edge_identity (B := (2:ℤ)^1037) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101101 : Branch 1 (-2751761639/32000000 : ℚ) vp01010110 := by
  apply branch_checked idp010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2751761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2767761639/16000000 : ℚ) by norm_num]
  exact coverp010101101
theorem coverp01010110 : Covers (-2751761639/32000000 : ℚ) vp01010110 := join_branches bp010101100 bp010101101
private noncomputable def vp0101011_0 : Blocks := edgeBlocks% "full/vectors/0101011-V-0000.bin"
private noncomputable def vp0101011_1 : Blocks := edgeBlocks% "full/vectors/0101011-V-0001.bin"
private noncomputable def vp0101011_2 : Blocks := edgeBlocks% "full/vectors/0101011-V-0002.bin"
private noncomputable def vp0101011_3 : Blocks := edgeBlocks% "full/vectors/0101011-V-0003.bin"
private noncomputable def vp0101011_4 : Blocks := edgeBlocks% "full/vectors/0101011-V-0004.bin"
private noncomputable def vp0101011_5 : Blocks := edgeBlocks% "full/vectors/0101011-V-0005.bin"
private noncomputable def vp0101011_6 : Blocks := edgeBlocks% "full/vectors/0101011-V-0006.bin"
private noncomputable def vp0101011_7 : Blocks := edgeBlocks% "full/vectors/0101011-V-0007.bin"
private noncomputable def vp0101011_8 : Blocks := edgeBlocks% "full/vectors/0101011-V-0008.bin"
private noncomputable def vp0101011_9 : Blocks := edgeBlocks% "full/vectors/0101011-V-0009.bin"
noncomputable def vp0101011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0101011_0 vp0101011_1) (Blocks.join vp0101011_2 (Blocks.join vp0101011_3 vp0101011_4))) (Blocks.join (Blocks.join vp0101011_5 vp0101011_6) (Blocks.join vp0101011_7 (Blocks.join vp0101011_8 vp0101011_9))))
private theorem bp01010110 : Branch 0 (-2751761639/64000000 : ℚ) vp0101011 := by
  apply branch_left_normalized (c:=vp01010110) (k:=0) (m:=617) (by decide +kernel)
  rw [show 2*(-2751761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2751761639/32000000 : ℚ) by norm_num]
  exact coverp01010110
private noncomputable def ep01010111_0 : Blocks := edgeBlocks% "full/vectors/01010111-E-0000.bin"
private noncomputable def ep01010111_1 : Blocks := edgeBlocks% "full/vectors/01010111-E-0001.bin"
private noncomputable def ep01010111_2 : Blocks := edgeBlocks% "full/vectors/01010111-E-0002.bin"
private noncomputable def ep01010111_3 : Blocks := edgeBlocks% "full/vectors/01010111-E-0003.bin"
private noncomputable def ep01010111_4 : Blocks := edgeBlocks% "full/vectors/01010111-E-0004.bin"
private noncomputable def ep01010111_5 : Blocks := edgeBlocks% "full/vectors/01010111-E-0005.bin"
private noncomputable def ep01010111_6 : Blocks := edgeBlocks% "full/vectors/01010111-E-0006.bin"
private noncomputable def ep01010111_7 : Blocks := edgeBlocks% "full/vectors/01010111-E-0007.bin"
private noncomputable def ep01010111_8 : Blocks := edgeBlocks% "full/vectors/01010111-E-0008.bin"
private noncomputable def ep01010111_9 : Blocks := edgeBlocks% "full/vectors/01010111-E-0009.bin"
noncomputable def ep01010111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01010111_0 ep01010111_1) (Blocks.join ep01010111_2 (Blocks.join ep01010111_3 ep01010111_4))) (Blocks.join (Blocks.join ep01010111_5 ep01010111_6) (Blocks.join ep01010111_7 (Blocks.join ep01010111_8 ep01010111_9))))
private theorem idp01010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101011.list =
    C ((2:ℤ)^1387) * horner X vp01010111.list + horner X ep01010111.list := by
  exact edge_identity (B := (2:ℤ)^1935) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010111 : Branch 1 (-2751761639/64000000 : ℚ) vp0101011 := by
  apply branch_checked idp01010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2751761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2783761639/32000000 : ℚ) by norm_num]
  exact coverp01010111
theorem coverp0101011 : Covers (-2751761639/64000000 : ℚ) vp0101011 := join_branches bp01010110 bp01010111
private noncomputable def vp010101011111_0 : Blocks := edgeBlocks% "full/vectors/010101011111-V-0000.bin"
noncomputable def vp010101011111 : Blocks := vp010101011111_0
theorem coverp010101011111 : Covers (-2749761639/2000000 : ℚ) vp010101011111 := cover_leaf (by decide +kernel)
private noncomputable def vp010101011110_0 : Blocks := edgeBlocks% "full/vectors/010101011110-V-0000.bin"
noncomputable def vp010101011110 : Blocks := vp010101011110_0
theorem coverp010101011110 : Covers (-2747761639/2000000 : ℚ) vp010101011110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010101111_0 : Blocks := edgeBlocks% "full/vectors/01010101111-V-0000.bin"
noncomputable def vp01010101111 : Blocks := vp01010101111_0
private theorem bp010101011110 : Branch 0 (-2747761639/4000000 : ℚ) vp01010101111 := by
  apply branch_left_normalized (c:=vp010101011110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2747761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2747761639/2000000 : ℚ) by norm_num]
  exact coverp010101011110
private noncomputable def ep010101011111_0 : Blocks := edgeBlocks% "full/vectors/010101011111-E-0000.bin"
noncomputable def ep010101011111 : Blocks := ep010101011111_0
private theorem idp010101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010101111.list =
    C ((2:ℤ)^109) * horner X vp010101011111.list + horner X ep010101011111.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101011111 : Branch 1 (-2747761639/4000000 : ℚ) vp01010101111 := by
  apply branch_checked idp010101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2747761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2749761639/2000000 : ℚ) by norm_num]
  exact coverp010101011111
theorem coverp01010101111 : Covers (-2747761639/4000000 : ℚ) vp01010101111 := join_branches bp010101011110 bp010101011111
private noncomputable def vp010101011101_0 : Blocks := edgeBlocks% "full/vectors/010101011101-V-0000.bin"
noncomputable def vp010101011101 : Blocks := vp010101011101_0
theorem coverp010101011101 : Covers (-2745761639/2000000 : ℚ) vp010101011101 := cover_leaf (by decide +kernel)
private noncomputable def vp010101011100_0 : Blocks := edgeBlocks% "full/vectors/010101011100-V-0000.bin"
noncomputable def vp010101011100 : Blocks := vp010101011100_0
theorem coverp010101011100 : Covers (-2743761639/2000000 : ℚ) vp010101011100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010101110_0 : Blocks := edgeBlocks% "full/vectors/01010101110-V-0000.bin"
noncomputable def vp01010101110 : Blocks := vp01010101110_0
private theorem bp010101011100 : Branch 0 (-2743761639/4000000 : ℚ) vp01010101110 := by
  apply branch_left_normalized (c:=vp010101011100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2743761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2743761639/2000000 : ℚ) by norm_num]
  exact coverp010101011100
private noncomputable def ep010101011101_0 : Blocks := edgeBlocks% "full/vectors/010101011101-E-0000.bin"
noncomputable def ep010101011101 : Blocks := ep010101011101_0
private theorem idp010101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010101110.list =
    C ((2:ℤ)^108) * horner X vp010101011101.list + horner X ep010101011101.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101011101 : Branch 1 (-2743761639/4000000 : ℚ) vp01010101110 := by
  apply branch_checked idp010101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2743761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2745761639/2000000 : ℚ) by norm_num]
  exact coverp010101011101
theorem coverp01010101110 : Covers (-2743761639/4000000 : ℚ) vp01010101110 := join_branches bp010101011100 bp010101011101
private noncomputable def vp0101010111_0 : Blocks := edgeBlocks% "full/vectors/0101010111-V-0000.bin"
private noncomputable def vp0101010111_1 : Blocks := edgeBlocks% "full/vectors/0101010111-V-0001.bin"
noncomputable def vp0101010111 : Blocks := (Blocks.join vp0101010111_0 vp0101010111_1)
private theorem bp01010101110 : Branch 0 (-2743761639/8000000 : ℚ) vp0101010111 := by
  apply branch_left_normalized (c:=vp01010101110) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-2743761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2743761639/4000000 : ℚ) by norm_num]
  exact coverp01010101110
private noncomputable def ep01010101111_0 : Blocks := edgeBlocks% "full/vectors/01010101111-E-0000.bin"
private noncomputable def ep01010101111_1 : Blocks := edgeBlocks% "full/vectors/01010101111-E-0001.bin"
noncomputable def ep01010101111 : Blocks := (Blocks.join ep01010101111_0 ep01010101111_1)
private theorem idp01010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101010111.list =
    C ((2:ℤ)^196) * horner X vp01010101111.list + horner X ep01010101111.list := by
  exact edge_identity (B := (2:ℤ)^354) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010101111 : Branch 1 (-2743761639/8000000 : ℚ) vp0101010111 := by
  apply branch_checked idp01010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2743761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2747761639/4000000 : ℚ) by norm_num]
  exact coverp01010101111
theorem coverp0101010111 : Covers (-2743761639/8000000 : ℚ) vp0101010111 := join_branches bp01010101110 bp01010101111
private noncomputable def vp010101011011_0 : Blocks := edgeBlocks% "full/vectors/010101011011-V-0000.bin"
noncomputable def vp010101011011 : Blocks := vp010101011011_0
theorem coverp010101011011 : Covers (-2741761639/2000000 : ℚ) vp010101011011 := cover_leaf (by decide +kernel)
private noncomputable def vp010101011010_0 : Blocks := edgeBlocks% "full/vectors/010101011010-V-0000.bin"
noncomputable def vp010101011010 : Blocks := vp010101011010_0
theorem coverp010101011010 : Covers (-2739761639/2000000 : ℚ) vp010101011010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010101101_0 : Blocks := edgeBlocks% "full/vectors/01010101101-V-0000.bin"
noncomputable def vp01010101101 : Blocks := vp01010101101_0
private theorem bp010101011010 : Branch 0 (-2739761639/4000000 : ℚ) vp01010101101 := by
  apply branch_left_normalized (c:=vp010101011010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2739761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2739761639/2000000 : ℚ) by norm_num]
  exact coverp010101011010
private noncomputable def ep010101011011_0 : Blocks := edgeBlocks% "full/vectors/010101011011-E-0000.bin"
noncomputable def ep010101011011 : Blocks := ep010101011011_0
private theorem idp010101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010101101.list =
    C ((2:ℤ)^108) * horner X vp010101011011.list + horner X ep010101011011.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101011011 : Branch 1 (-2739761639/4000000 : ℚ) vp01010101101 := by
  apply branch_checked idp010101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2739761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2741761639/2000000 : ℚ) by norm_num]
  exact coverp010101011011
theorem coverp01010101101 : Covers (-2739761639/4000000 : ℚ) vp01010101101 := join_branches bp010101011010 bp010101011011
private noncomputable def vp010101011001_0 : Blocks := edgeBlocks% "full/vectors/010101011001-V-0000.bin"
noncomputable def vp010101011001 : Blocks := vp010101011001_0
theorem coverp010101011001 : Covers (-2737761639/2000000 : ℚ) vp010101011001 := cover_leaf (by decide +kernel)
private noncomputable def vp010101011000_0 : Blocks := edgeBlocks% "full/vectors/010101011000-V-0000.bin"
noncomputable def vp010101011000 : Blocks := vp010101011000_0
theorem coverp010101011000 : Covers (-2735761639/2000000 : ℚ) vp010101011000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010101100_0 : Blocks := edgeBlocks% "full/vectors/01010101100-V-0000.bin"
noncomputable def vp01010101100 : Blocks := vp01010101100_0
private theorem bp010101011000 : Branch 0 (-2735761639/4000000 : ℚ) vp01010101100 := by
  apply branch_left_normalized (c:=vp010101011000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2735761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2735761639/2000000 : ℚ) by norm_num]
  exact coverp010101011000
private noncomputable def ep010101011001_0 : Blocks := edgeBlocks% "full/vectors/010101011001-E-0000.bin"
noncomputable def ep010101011001 : Blocks := ep010101011001_0
private theorem idp010101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010101100.list =
    C ((2:ℤ)^108) * horner X vp010101011001.list + horner X ep010101011001.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101011001 : Branch 1 (-2735761639/4000000 : ℚ) vp01010101100 := by
  apply branch_checked idp010101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2735761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2737761639/2000000 : ℚ) by norm_num]
  exact coverp010101011001
theorem coverp01010101100 : Covers (-2735761639/4000000 : ℚ) vp01010101100 := join_branches bp010101011000 bp010101011001
private noncomputable def vp0101010110_0 : Blocks := edgeBlocks% "full/vectors/0101010110-V-0000.bin"
private noncomputable def vp0101010110_1 : Blocks := edgeBlocks% "full/vectors/0101010110-V-0001.bin"
noncomputable def vp0101010110 : Blocks := (Blocks.join vp0101010110_0 vp0101010110_1)
private theorem bp01010101100 : Branch 0 (-2735761639/8000000 : ℚ) vp0101010110 := by
  apply branch_left_normalized (c:=vp01010101100) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-2735761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2735761639/4000000 : ℚ) by norm_num]
  exact coverp01010101100
private noncomputable def ep01010101101_0 : Blocks := edgeBlocks% "full/vectors/01010101101-E-0000.bin"
private noncomputable def ep01010101101_1 : Blocks := edgeBlocks% "full/vectors/01010101101-E-0001.bin"
noncomputable def ep01010101101 : Blocks := (Blocks.join ep01010101101_0 ep01010101101_1)
private theorem idp01010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101010110.list =
    C ((2:ℤ)^195) * horner X vp01010101101.list + horner X ep01010101101.list := by
  exact edge_identity (B := (2:ℤ)^353) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010101101 : Branch 1 (-2735761639/8000000 : ℚ) vp0101010110 := by
  apply branch_checked idp01010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2735761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2739761639/4000000 : ℚ) by norm_num]
  exact coverp01010101101
theorem coverp0101010110 : Covers (-2735761639/8000000 : ℚ) vp0101010110 := join_branches bp01010101100 bp01010101101
private noncomputable def vp010101011_0 : Blocks := edgeBlocks% "full/vectors/010101011-V-0000.bin"
private noncomputable def vp010101011_1 : Blocks := edgeBlocks% "full/vectors/010101011-V-0001.bin"
private noncomputable def vp010101011_2 : Blocks := edgeBlocks% "full/vectors/010101011-V-0002.bin"
noncomputable def vp010101011 : Blocks := (Blocks.join vp010101011_0 (Blocks.join vp010101011_1 vp010101011_2))
private theorem bp0101010110 : Branch 0 (-2735761639/16000000 : ℚ) vp010101011 := by
  apply branch_left_normalized (c:=vp0101010110) (k:=0) (m:=171) (by decide +kernel)
  rw [show 2*(-2735761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2735761639/8000000 : ℚ) by norm_num]
  exact coverp0101010110
private noncomputable def ep0101010111_0 : Blocks := edgeBlocks% "full/vectors/0101010111-E-0000.bin"
private noncomputable def ep0101010111_1 : Blocks := edgeBlocks% "full/vectors/0101010111-E-0001.bin"
private noncomputable def ep0101010111_2 : Blocks := edgeBlocks% "full/vectors/0101010111-E-0002.bin"
noncomputable def ep0101010111 : Blocks := (Blocks.join ep0101010111_0 (Blocks.join ep0101010111_1 ep0101010111_2))
private theorem idp0101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010101011.list =
    C ((2:ℤ)^369) * horner X vp0101010111.list + horner X ep0101010111.list := by
  exact edge_identity (B := (2:ℤ)^583) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101010111 : Branch 1 (-2735761639/16000000 : ℚ) vp010101011 := by
  apply branch_checked idp0101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2735761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2743761639/8000000 : ℚ) by norm_num]
  exact coverp0101010111
theorem coverp010101011 : Covers (-2735761639/16000000 : ℚ) vp010101011 := join_branches bp0101010110 bp0101010111
private noncomputable def vp010101010111_0 : Blocks := edgeBlocks% "full/vectors/010101010111-V-0000.bin"
noncomputable def vp010101010111 : Blocks := vp010101010111_0
theorem coverp010101010111 : Covers (-2733761639/2000000 : ℚ) vp010101010111 := cover_leaf (by decide +kernel)
private noncomputable def vp010101010110_0 : Blocks := edgeBlocks% "full/vectors/010101010110-V-0000.bin"
noncomputable def vp010101010110 : Blocks := vp010101010110_0
theorem coverp010101010110 : Covers (-2731761639/2000000 : ℚ) vp010101010110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010101011_0 : Blocks := edgeBlocks% "full/vectors/01010101011-V-0000.bin"
noncomputable def vp01010101011 : Blocks := vp01010101011_0
private theorem bp010101010110 : Branch 0 (-2731761639/4000000 : ℚ) vp01010101011 := by
  apply branch_left_normalized (c:=vp010101010110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2731761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2731761639/2000000 : ℚ) by norm_num]
  exact coverp010101010110
private noncomputable def ep010101010111_0 : Blocks := edgeBlocks% "full/vectors/010101010111-E-0000.bin"
noncomputable def ep010101010111 : Blocks := ep010101010111_0
private theorem idp010101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010101011.list =
    C ((2:ℤ)^108) * horner X vp010101010111.list + horner X ep010101010111.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101010111 : Branch 1 (-2731761639/4000000 : ℚ) vp01010101011 := by
  apply branch_checked idp010101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2731761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2733761639/2000000 : ℚ) by norm_num]
  exact coverp010101010111
theorem coverp01010101011 : Covers (-2731761639/4000000 : ℚ) vp01010101011 := join_branches bp010101010110 bp010101010111
private noncomputable def vp010101010101_0 : Blocks := edgeBlocks% "full/vectors/010101010101-V-0000.bin"
noncomputable def vp010101010101 : Blocks := vp010101010101_0
theorem coverp010101010101 : Covers (-2729761639/2000000 : ℚ) vp010101010101 := cover_leaf (by decide +kernel)
private noncomputable def vp010101010100_0 : Blocks := edgeBlocks% "full/vectors/010101010100-V-0000.bin"
noncomputable def vp010101010100 : Blocks := vp010101010100_0
theorem coverp010101010100 : Covers (-2727761639/2000000 : ℚ) vp010101010100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010101010_0 : Blocks := edgeBlocks% "full/vectors/01010101010-V-0000.bin"
noncomputable def vp01010101010 : Blocks := vp01010101010_0
private theorem bp010101010100 : Branch 0 (-2727761639/4000000 : ℚ) vp01010101010 := by
  apply branch_left_normalized (c:=vp010101010100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2727761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2727761639/2000000 : ℚ) by norm_num]
  exact coverp010101010100
private noncomputable def ep010101010101_0 : Blocks := edgeBlocks% "full/vectors/010101010101-E-0000.bin"
noncomputable def ep010101010101 : Blocks := ep010101010101_0
private theorem idp010101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010101010.list =
    C ((2:ℤ)^108) * horner X vp010101010101.list + horner X ep010101010101.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101010101 : Branch 1 (-2727761639/4000000 : ℚ) vp01010101010 := by
  apply branch_checked idp010101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2727761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2729761639/2000000 : ℚ) by norm_num]
  exact coverp010101010101
theorem coverp01010101010 : Covers (-2727761639/4000000 : ℚ) vp01010101010 := join_branches bp010101010100 bp010101010101
private noncomputable def vp0101010101_0 : Blocks := edgeBlocks% "full/vectors/0101010101-V-0000.bin"
private noncomputable def vp0101010101_1 : Blocks := edgeBlocks% "full/vectors/0101010101-V-0001.bin"
noncomputable def vp0101010101 : Blocks := (Blocks.join vp0101010101_0 vp0101010101_1)
private theorem bp01010101010 : Branch 0 (-2727761639/8000000 : ℚ) vp0101010101 := by
  apply branch_left_normalized (c:=vp01010101010) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-2727761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2727761639/4000000 : ℚ) by norm_num]
  exact coverp01010101010
private noncomputable def ep01010101011_0 : Blocks := edgeBlocks% "full/vectors/01010101011-E-0000.bin"
private noncomputable def ep01010101011_1 : Blocks := edgeBlocks% "full/vectors/01010101011-E-0001.bin"
noncomputable def ep01010101011 : Blocks := (Blocks.join ep01010101011_0 ep01010101011_1)
private theorem idp01010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101010101.list =
    C ((2:ℤ)^196) * horner X vp01010101011.list + horner X ep01010101011.list := by
  exact edge_identity (B := (2:ℤ)^354) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010101011 : Branch 1 (-2727761639/8000000 : ℚ) vp0101010101 := by
  apply branch_checked idp01010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2727761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2731761639/4000000 : ℚ) by norm_num]
  exact coverp01010101011
theorem coverp0101010101 : Covers (-2727761639/8000000 : ℚ) vp0101010101 := join_branches bp01010101010 bp01010101011
private noncomputable def vp010101010011_0 : Blocks := edgeBlocks% "full/vectors/010101010011-V-0000.bin"
noncomputable def vp010101010011 : Blocks := vp010101010011_0
theorem coverp010101010011 : Covers (-2725761639/2000000 : ℚ) vp010101010011 := cover_leaf (by decide +kernel)
private noncomputable def vp010101010010_0 : Blocks := edgeBlocks% "full/vectors/010101010010-V-0000.bin"
noncomputable def vp010101010010 : Blocks := vp010101010010_0
theorem coverp010101010010 : Covers (-2723761639/2000000 : ℚ) vp010101010010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010101001_0 : Blocks := edgeBlocks% "full/vectors/01010101001-V-0000.bin"
noncomputable def vp01010101001 : Blocks := vp01010101001_0
private theorem bp010101010010 : Branch 0 (-2723761639/4000000 : ℚ) vp01010101001 := by
  apply branch_left_normalized (c:=vp010101010010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2723761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2723761639/2000000 : ℚ) by norm_num]
  exact coverp010101010010
private noncomputable def ep010101010011_0 : Blocks := edgeBlocks% "full/vectors/010101010011-E-0000.bin"
noncomputable def ep010101010011 : Blocks := ep010101010011_0
private theorem idp010101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010101001.list =
    C ((2:ℤ)^108) * horner X vp010101010011.list + horner X ep010101010011.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101010011 : Branch 1 (-2723761639/4000000 : ℚ) vp01010101001 := by
  apply branch_checked idp010101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2723761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2725761639/2000000 : ℚ) by norm_num]
  exact coverp010101010011
theorem coverp01010101001 : Covers (-2723761639/4000000 : ℚ) vp01010101001 := join_branches bp010101010010 bp010101010011
private noncomputable def vp010101010001_0 : Blocks := edgeBlocks% "full/vectors/010101010001-V-0000.bin"
noncomputable def vp010101010001 : Blocks := vp010101010001_0
theorem coverp010101010001 : Covers (-2721761639/2000000 : ℚ) vp010101010001 := cover_leaf (by decide +kernel)
private noncomputable def vp010101010000_0 : Blocks := edgeBlocks% "full/vectors/010101010000-V-0000.bin"
noncomputable def vp010101010000 : Blocks := vp010101010000_0
theorem coverp010101010000 : Covers (-2719761639/2000000 : ℚ) vp010101010000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010101000_0 : Blocks := edgeBlocks% "full/vectors/01010101000-V-0000.bin"
noncomputable def vp01010101000 : Blocks := vp01010101000_0
private theorem bp010101010000 : Branch 0 (-2719761639/4000000 : ℚ) vp01010101000 := by
  apply branch_left_normalized (c:=vp010101010000) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2719761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2719761639/2000000 : ℚ) by norm_num]
  exact coverp010101010000
private noncomputable def ep010101010001_0 : Blocks := edgeBlocks% "full/vectors/010101010001-E-0000.bin"
noncomputable def ep010101010001 : Blocks := ep010101010001_0
private theorem idp010101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010101000.list =
    C ((2:ℤ)^110) * horner X vp010101010001.list + horner X ep010101010001.list := by
  exact edge_identity (B := (2:ℤ)^240) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101010001 : Branch 1 (-2719761639/4000000 : ℚ) vp01010101000 := by
  apply branch_checked idp010101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2719761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2721761639/2000000 : ℚ) by norm_num]
  exact coverp010101010001
theorem coverp01010101000 : Covers (-2719761639/4000000 : ℚ) vp01010101000 := join_branches bp010101010000 bp010101010001
private noncomputable def vp0101010100_0 : Blocks := edgeBlocks% "full/vectors/0101010100-V-0000.bin"
private noncomputable def vp0101010100_1 : Blocks := edgeBlocks% "full/vectors/0101010100-V-0001.bin"
noncomputable def vp0101010100 : Blocks := (Blocks.join vp0101010100_0 vp0101010100_1)
private theorem bp01010101000 : Branch 0 (-2719761639/8000000 : ℚ) vp0101010100 := by
  apply branch_left_normalized (c:=vp01010101000) (k:=0) (m:=97) (by decide +kernel)
  rw [show 2*(-2719761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2719761639/4000000 : ℚ) by norm_num]
  exact coverp01010101000
private noncomputable def ep01010101001_0 : Blocks := edgeBlocks% "full/vectors/01010101001-E-0000.bin"
private noncomputable def ep01010101001_1 : Blocks := edgeBlocks% "full/vectors/01010101001-E-0001.bin"
noncomputable def ep01010101001 : Blocks := (Blocks.join ep01010101001_0 ep01010101001_1)
private theorem idp01010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101010100.list =
    C ((2:ℤ)^198) * horner X vp01010101001.list + horner X ep01010101001.list := by
  exact edge_identity (B := (2:ℤ)^356) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010101001 : Branch 1 (-2719761639/8000000 : ℚ) vp0101010100 := by
  apply branch_checked idp01010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2719761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2723761639/4000000 : ℚ) by norm_num]
  exact coverp01010101001
theorem coverp0101010100 : Covers (-2719761639/8000000 : ℚ) vp0101010100 := join_branches bp01010101000 bp01010101001
private noncomputable def vp010101010_0 : Blocks := edgeBlocks% "full/vectors/010101010-V-0000.bin"
private noncomputable def vp010101010_1 : Blocks := edgeBlocks% "full/vectors/010101010-V-0001.bin"
private noncomputable def vp010101010_2 : Blocks := edgeBlocks% "full/vectors/010101010-V-0002.bin"
noncomputable def vp010101010 : Blocks := (Blocks.join vp010101010_0 (Blocks.join vp010101010_1 vp010101010_2))
private theorem bp0101010100 : Branch 0 (-2719761639/16000000 : ℚ) vp010101010 := by
  apply branch_left_normalized (c:=vp0101010100) (k:=0) (m:=173) (by decide +kernel)
  rw [show 2*(-2719761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2719761639/8000000 : ℚ) by norm_num]
  exact coverp0101010100
private noncomputable def ep0101010101_0 : Blocks := edgeBlocks% "full/vectors/0101010101-E-0000.bin"
private noncomputable def ep0101010101_1 : Blocks := edgeBlocks% "full/vectors/0101010101-E-0001.bin"
private noncomputable def ep0101010101_2 : Blocks := edgeBlocks% "full/vectors/0101010101-E-0002.bin"
noncomputable def ep0101010101 : Blocks := (Blocks.join ep0101010101_0 (Blocks.join ep0101010101_1 ep0101010101_2))
private theorem idp0101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010101010.list =
    C ((2:ℤ)^371) * horner X vp0101010101.list + horner X ep0101010101.list := by
  exact edge_identity (B := (2:ℤ)^586) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101010101 : Branch 1 (-2719761639/16000000 : ℚ) vp010101010 := by
  apply branch_checked idp0101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2719761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2727761639/8000000 : ℚ) by norm_num]
  exact coverp0101010101
theorem coverp010101010 : Covers (-2719761639/16000000 : ℚ) vp010101010 := join_branches bp0101010100 bp0101010101
private noncomputable def vp01010101_0 : Blocks := edgeBlocks% "full/vectors/01010101-V-0000.bin"
private noncomputable def vp01010101_1 : Blocks := edgeBlocks% "full/vectors/01010101-V-0001.bin"
private noncomputable def vp01010101_2 : Blocks := edgeBlocks% "full/vectors/01010101-V-0002.bin"
private noncomputable def vp01010101_3 : Blocks := edgeBlocks% "full/vectors/01010101-V-0003.bin"
private noncomputable def vp01010101_4 : Blocks := edgeBlocks% "full/vectors/01010101-V-0004.bin"
noncomputable def vp01010101 : Blocks := (Blocks.join (Blocks.join vp01010101_0 vp01010101_1) (Blocks.join vp01010101_2 (Blocks.join vp01010101_3 vp01010101_4)))
private theorem bp010101010 : Branch 0 (-2719761639/32000000 : ℚ) vp01010101 := by
  apply branch_left_normalized (c:=vp010101010) (k:=0) (m:=323) (by decide +kernel)
  rw [show 2*(-2719761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2719761639/16000000 : ℚ) by norm_num]
  exact coverp010101010
private noncomputable def ep010101011_0 : Blocks := edgeBlocks% "full/vectors/010101011-E-0000.bin"
private noncomputable def ep010101011_1 : Blocks := edgeBlocks% "full/vectors/010101011-E-0001.bin"
private noncomputable def ep010101011_2 : Blocks := edgeBlocks% "full/vectors/010101011-E-0002.bin"
private noncomputable def ep010101011_3 : Blocks := edgeBlocks% "full/vectors/010101011-E-0003.bin"
private noncomputable def ep010101011_4 : Blocks := edgeBlocks% "full/vectors/010101011-E-0004.bin"
noncomputable def ep010101011 : Blocks := (Blocks.join (Blocks.join ep010101011_0 ep010101011_1) (Blocks.join ep010101011_2 (Blocks.join ep010101011_3 ep010101011_4)))
private theorem idp010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010101.list =
    C ((2:ℤ)^715) * horner X vp010101011.list + horner X ep010101011.list := by
  exact edge_identity (B := (2:ℤ)^1043) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101011 : Branch 1 (-2719761639/32000000 : ℚ) vp01010101 := by
  apply branch_checked idp010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2719761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2735761639/16000000 : ℚ) by norm_num]
  exact coverp010101011
theorem coverp01010101 : Covers (-2719761639/32000000 : ℚ) vp01010101 := join_branches bp010101010 bp010101011
private noncomputable def vp010101001111_0 : Blocks := edgeBlocks% "full/vectors/010101001111-V-0000.bin"
noncomputable def vp010101001111 : Blocks := vp010101001111_0
theorem coverp010101001111 : Covers (-2717761639/2000000 : ℚ) vp010101001111 := cover_leaf (by decide +kernel)
private noncomputable def vp010101001110_0 : Blocks := edgeBlocks% "full/vectors/010101001110-V-0000.bin"
noncomputable def vp010101001110 : Blocks := vp010101001110_0
theorem coverp010101001110 : Covers (-2715761639/2000000 : ℚ) vp010101001110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010100111_0 : Blocks := edgeBlocks% "full/vectors/01010100111-V-0000.bin"
noncomputable def vp01010100111 : Blocks := vp01010100111_0
private theorem bp010101001110 : Branch 0 (-2715761639/4000000 : ℚ) vp01010100111 := by
  apply branch_left_normalized (c:=vp010101001110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2715761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2715761639/2000000 : ℚ) by norm_num]
  exact coverp010101001110
private noncomputable def ep010101001111_0 : Blocks := edgeBlocks% "full/vectors/010101001111-E-0000.bin"
noncomputable def ep010101001111 : Blocks := ep010101001111_0
private theorem idp010101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010100111.list =
    C ((2:ℤ)^109) * horner X vp010101001111.list + horner X ep010101001111.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101001111 : Branch 1 (-2715761639/4000000 : ℚ) vp01010100111 := by
  apply branch_checked idp010101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2715761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2717761639/2000000 : ℚ) by norm_num]
  exact coverp010101001111
theorem coverp01010100111 : Covers (-2715761639/4000000 : ℚ) vp01010100111 := join_branches bp010101001110 bp010101001111
private noncomputable def vp010101001101_0 : Blocks := edgeBlocks% "full/vectors/010101001101-V-0000.bin"
noncomputable def vp010101001101 : Blocks := vp010101001101_0
theorem coverp010101001101 : Covers (-2713761639/2000000 : ℚ) vp010101001101 := cover_leaf (by decide +kernel)
private noncomputable def vp010101001100_0 : Blocks := edgeBlocks% "full/vectors/010101001100-V-0000.bin"
noncomputable def vp010101001100 : Blocks := vp010101001100_0
theorem coverp010101001100 : Covers (-2711761639/2000000 : ℚ) vp010101001100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010100110_0 : Blocks := edgeBlocks% "full/vectors/01010100110-V-0000.bin"
noncomputable def vp01010100110 : Blocks := vp01010100110_0
private theorem bp010101001100 : Branch 0 (-2711761639/4000000 : ℚ) vp01010100110 := by
  apply branch_left_normalized (c:=vp010101001100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2711761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2711761639/2000000 : ℚ) by norm_num]
  exact coverp010101001100
private noncomputable def ep010101001101_0 : Blocks := edgeBlocks% "full/vectors/010101001101-E-0000.bin"
noncomputable def ep010101001101 : Blocks := ep010101001101_0
private theorem idp010101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010100110.list =
    C ((2:ℤ)^109) * horner X vp010101001101.list + horner X ep010101001101.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101001101 : Branch 1 (-2711761639/4000000 : ℚ) vp01010100110 := by
  apply branch_checked idp010101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2711761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2713761639/2000000 : ℚ) by norm_num]
  exact coverp010101001101
theorem coverp01010100110 : Covers (-2711761639/4000000 : ℚ) vp01010100110 := join_branches bp010101001100 bp010101001101
private noncomputable def vp0101010011_0 : Blocks := edgeBlocks% "full/vectors/0101010011-V-0000.bin"
private noncomputable def vp0101010011_1 : Blocks := edgeBlocks% "full/vectors/0101010011-V-0001.bin"
noncomputable def vp0101010011 : Blocks := (Blocks.join vp0101010011_0 vp0101010011_1)
private theorem bp01010100110 : Branch 0 (-2711761639/8000000 : ℚ) vp0101010011 := by
  apply branch_left_normalized (c:=vp01010100110) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-2711761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2711761639/4000000 : ℚ) by norm_num]
  exact coverp01010100110
private noncomputable def ep01010100111_0 : Blocks := edgeBlocks% "full/vectors/01010100111-E-0000.bin"
private noncomputable def ep01010100111_1 : Blocks := edgeBlocks% "full/vectors/01010100111-E-0001.bin"
noncomputable def ep01010100111 : Blocks := (Blocks.join ep01010100111_0 ep01010100111_1)
private theorem idp01010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101010011.list =
    C ((2:ℤ)^197) * horner X vp01010100111.list + horner X ep01010100111.list := by
  exact edge_identity (B := (2:ℤ)^356) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010100111 : Branch 1 (-2711761639/8000000 : ℚ) vp0101010011 := by
  apply branch_checked idp01010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2711761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2715761639/4000000 : ℚ) by norm_num]
  exact coverp01010100111
theorem coverp0101010011 : Covers (-2711761639/8000000 : ℚ) vp0101010011 := join_branches bp01010100110 bp01010100111
private noncomputable def vp010101001011_0 : Blocks := edgeBlocks% "full/vectors/010101001011-V-0000.bin"
noncomputable def vp010101001011 : Blocks := vp010101001011_0
theorem coverp010101001011 : Covers (-2709761639/2000000 : ℚ) vp010101001011 := cover_leaf (by decide +kernel)
private noncomputable def vp010101001010_0 : Blocks := edgeBlocks% "full/vectors/010101001010-V-0000.bin"
noncomputable def vp010101001010 : Blocks := vp010101001010_0
theorem coverp010101001010 : Covers (-2707761639/2000000 : ℚ) vp010101001010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010100101_0 : Blocks := edgeBlocks% "full/vectors/01010100101-V-0000.bin"
noncomputable def vp01010100101 : Blocks := vp01010100101_0
private theorem bp010101001010 : Branch 0 (-2707761639/4000000 : ℚ) vp01010100101 := by
  apply branch_left_normalized (c:=vp010101001010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2707761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2707761639/2000000 : ℚ) by norm_num]
  exact coverp010101001010
private noncomputable def ep010101001011_0 : Blocks := edgeBlocks% "full/vectors/010101001011-E-0000.bin"
noncomputable def ep010101001011 : Blocks := ep010101001011_0
private theorem idp010101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010100101.list =
    C ((2:ℤ)^108) * horner X vp010101001011.list + horner X ep010101001011.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101001011 : Branch 1 (-2707761639/4000000 : ℚ) vp01010100101 := by
  apply branch_checked idp010101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2707761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2709761639/2000000 : ℚ) by norm_num]
  exact coverp010101001011
theorem coverp01010100101 : Covers (-2707761639/4000000 : ℚ) vp01010100101 := join_branches bp010101001010 bp010101001011
private noncomputable def vp010101001001_0 : Blocks := edgeBlocks% "full/vectors/010101001001-V-0000.bin"
noncomputable def vp010101001001 : Blocks := vp010101001001_0
theorem coverp010101001001 : Covers (-2705761639/2000000 : ℚ) vp010101001001 := cover_leaf (by decide +kernel)
private noncomputable def vp010101001000_0 : Blocks := edgeBlocks% "full/vectors/010101001000-V-0000.bin"
noncomputable def vp010101001000 : Blocks := vp010101001000_0
theorem coverp010101001000 : Covers (-2703761639/2000000 : ℚ) vp010101001000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010100100_0 : Blocks := edgeBlocks% "full/vectors/01010100100-V-0000.bin"
noncomputable def vp01010100100 : Blocks := vp01010100100_0
private theorem bp010101001000 : Branch 0 (-2703761639/4000000 : ℚ) vp01010100100 := by
  apply branch_left_normalized (c:=vp010101001000) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2703761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2703761639/2000000 : ℚ) by norm_num]
  exact coverp010101001000
private noncomputable def ep010101001001_0 : Blocks := edgeBlocks% "full/vectors/010101001001-E-0000.bin"
noncomputable def ep010101001001 : Blocks := ep010101001001_0
private theorem idp010101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010100100.list =
    C ((2:ℤ)^110) * horner X vp010101001001.list + horner X ep010101001001.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101001001 : Branch 1 (-2703761639/4000000 : ℚ) vp01010100100 := by
  apply branch_checked idp010101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2703761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2705761639/2000000 : ℚ) by norm_num]
  exact coverp010101001001
theorem coverp01010100100 : Covers (-2703761639/4000000 : ℚ) vp01010100100 := join_branches bp010101001000 bp010101001001
private noncomputable def vp0101010010_0 : Blocks := edgeBlocks% "full/vectors/0101010010-V-0000.bin"
private noncomputable def vp0101010010_1 : Blocks := edgeBlocks% "full/vectors/0101010010-V-0001.bin"
noncomputable def vp0101010010 : Blocks := (Blocks.join vp0101010010_0 vp0101010010_1)
private theorem bp01010100100 : Branch 0 (-2703761639/8000000 : ℚ) vp0101010010 := by
  apply branch_left_normalized (c:=vp01010100100) (k:=0) (m:=97) (by decide +kernel)
  rw [show 2*(-2703761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2703761639/4000000 : ℚ) by norm_num]
  exact coverp01010100100
private noncomputable def ep01010100101_0 : Blocks := edgeBlocks% "full/vectors/01010100101-E-0000.bin"
private noncomputable def ep01010100101_1 : Blocks := edgeBlocks% "full/vectors/01010100101-E-0001.bin"
noncomputable def ep01010100101 : Blocks := (Blocks.join ep01010100101_0 ep01010100101_1)
private theorem idp01010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101010010.list =
    C ((2:ℤ)^198) * horner X vp01010100101.list + horner X ep01010100101.list := by
  exact edge_identity (B := (2:ℤ)^355) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010100101 : Branch 1 (-2703761639/8000000 : ℚ) vp0101010010 := by
  apply branch_checked idp01010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2703761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2707761639/4000000 : ℚ) by norm_num]
  exact coverp01010100101
theorem coverp0101010010 : Covers (-2703761639/8000000 : ℚ) vp0101010010 := join_branches bp01010100100 bp01010100101
private noncomputable def vp010101001_0 : Blocks := edgeBlocks% "full/vectors/010101001-V-0000.bin"
private noncomputable def vp010101001_1 : Blocks := edgeBlocks% "full/vectors/010101001-V-0001.bin"
private noncomputable def vp010101001_2 : Blocks := edgeBlocks% "full/vectors/010101001-V-0002.bin"
noncomputable def vp010101001 : Blocks := (Blocks.join vp010101001_0 (Blocks.join vp010101001_1 vp010101001_2))
private theorem bp0101010010 : Branch 0 (-2703761639/16000000 : ℚ) vp010101001 := by
  apply branch_left_normalized (c:=vp0101010010) (k:=0) (m:=173) (by decide +kernel)
  rw [show 2*(-2703761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2703761639/8000000 : ℚ) by norm_num]
  exact coverp0101010010
private noncomputable def ep0101010011_0 : Blocks := edgeBlocks% "full/vectors/0101010011-E-0000.bin"
private noncomputable def ep0101010011_1 : Blocks := edgeBlocks% "full/vectors/0101010011-E-0001.bin"
private noncomputable def ep0101010011_2 : Blocks := edgeBlocks% "full/vectors/0101010011-E-0002.bin"
noncomputable def ep0101010011 : Blocks := (Blocks.join ep0101010011_0 (Blocks.join ep0101010011_1 ep0101010011_2))
private theorem idp0101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010101001.list =
    C ((2:ℤ)^370) * horner X vp0101010011.list + horner X ep0101010011.list := by
  exact edge_identity (B := (2:ℤ)^586) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101010011 : Branch 1 (-2703761639/16000000 : ℚ) vp010101001 := by
  apply branch_checked idp0101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2703761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2711761639/8000000 : ℚ) by norm_num]
  exact coverp0101010011
theorem coverp010101001 : Covers (-2703761639/16000000 : ℚ) vp010101001 := join_branches bp0101010010 bp0101010011
private noncomputable def vp010101000111_0 : Blocks := edgeBlocks% "full/vectors/010101000111-V-0000.bin"
noncomputable def vp010101000111 : Blocks := vp010101000111_0
theorem coverp010101000111 : Covers (-2701761639/2000000 : ℚ) vp010101000111 := cover_leaf (by decide +kernel)
private noncomputable def vp010101000110_0 : Blocks := edgeBlocks% "full/vectors/010101000110-V-0000.bin"
noncomputable def vp010101000110 : Blocks := vp010101000110_0
theorem coverp010101000110 : Covers (-2699761639/2000000 : ℚ) vp010101000110 := cover_leaf (by decide +kernel)
private noncomputable def vp01010100011_0 : Blocks := edgeBlocks% "full/vectors/01010100011-V-0000.bin"
noncomputable def vp01010100011 : Blocks := vp01010100011_0
private theorem bp010101000110 : Branch 0 (-2699761639/4000000 : ℚ) vp01010100011 := by
  apply branch_left_normalized (c:=vp010101000110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2699761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2699761639/2000000 : ℚ) by norm_num]
  exact coverp010101000110
private noncomputable def ep010101000111_0 : Blocks := edgeBlocks% "full/vectors/010101000111-E-0000.bin"
noncomputable def ep010101000111 : Blocks := ep010101000111_0
private theorem idp010101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010100011.list =
    C ((2:ℤ)^109) * horner X vp010101000111.list + horner X ep010101000111.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101000111 : Branch 1 (-2699761639/4000000 : ℚ) vp01010100011 := by
  apply branch_checked idp010101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2699761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2701761639/2000000 : ℚ) by norm_num]
  exact coverp010101000111
theorem coverp01010100011 : Covers (-2699761639/4000000 : ℚ) vp01010100011 := join_branches bp010101000110 bp010101000111
private noncomputable def vp010101000101_0 : Blocks := edgeBlocks% "full/vectors/010101000101-V-0000.bin"
noncomputable def vp010101000101 : Blocks := vp010101000101_0
theorem coverp010101000101 : Covers (-2697761639/2000000 : ℚ) vp010101000101 := cover_leaf (by decide +kernel)
private noncomputable def vp010101000100_0 : Blocks := edgeBlocks% "full/vectors/010101000100-V-0000.bin"
noncomputable def vp010101000100 : Blocks := vp010101000100_0
theorem coverp010101000100 : Covers (-2695761639/2000000 : ℚ) vp010101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp01010100010_0 : Blocks := edgeBlocks% "full/vectors/01010100010-V-0000.bin"
noncomputable def vp01010100010 : Blocks := vp01010100010_0
private theorem bp010101000100 : Branch 0 (-2695761639/4000000 : ℚ) vp01010100010 := by
  apply branch_left_normalized (c:=vp010101000100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2695761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2695761639/2000000 : ℚ) by norm_num]
  exact coverp010101000100
private noncomputable def ep010101000101_0 : Blocks := edgeBlocks% "full/vectors/010101000101-E-0000.bin"
noncomputable def ep010101000101 : Blocks := ep010101000101_0
private theorem idp010101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010100010.list =
    C ((2:ℤ)^108) * horner X vp010101000101.list + horner X ep010101000101.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101000101 : Branch 1 (-2695761639/4000000 : ℚ) vp01010100010 := by
  apply branch_checked idp010101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2695761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2697761639/2000000 : ℚ) by norm_num]
  exact coverp010101000101
theorem coverp01010100010 : Covers (-2695761639/4000000 : ℚ) vp01010100010 := join_branches bp010101000100 bp010101000101
private noncomputable def vp0101010001_0 : Blocks := edgeBlocks% "full/vectors/0101010001-V-0000.bin"
private noncomputable def vp0101010001_1 : Blocks := edgeBlocks% "full/vectors/0101010001-V-0001.bin"
noncomputable def vp0101010001 : Blocks := (Blocks.join vp0101010001_0 vp0101010001_1)
private theorem bp01010100010 : Branch 0 (-2695761639/8000000 : ℚ) vp0101010001 := by
  apply branch_left_normalized (c:=vp01010100010) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-2695761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2695761639/4000000 : ℚ) by norm_num]
  exact coverp01010100010
private noncomputable def ep01010100011_0 : Blocks := edgeBlocks% "full/vectors/01010100011-E-0000.bin"
private noncomputable def ep01010100011_1 : Blocks := edgeBlocks% "full/vectors/01010100011-E-0001.bin"
noncomputable def ep01010100011 : Blocks := (Blocks.join ep01010100011_0 ep01010100011_1)
private theorem idp01010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101010001.list =
    C ((2:ℤ)^196) * horner X vp01010100011.list + horner X ep01010100011.list := by
  exact edge_identity (B := (2:ℤ)^354) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010100011 : Branch 1 (-2695761639/8000000 : ℚ) vp0101010001 := by
  apply branch_checked idp01010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2695761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2699761639/4000000 : ℚ) by norm_num]
  exact coverp01010100011
theorem coverp0101010001 : Covers (-2695761639/8000000 : ℚ) vp0101010001 := join_branches bp01010100010 bp01010100011
private noncomputable def vp010101000011_0 : Blocks := edgeBlocks% "full/vectors/010101000011-V-0000.bin"
noncomputable def vp010101000011 : Blocks := vp010101000011_0
theorem coverp010101000011 : Covers (-2693761639/2000000 : ℚ) vp010101000011 := cover_leaf (by decide +kernel)
private noncomputable def vp010101000010_0 : Blocks := edgeBlocks% "full/vectors/010101000010-V-0000.bin"
noncomputable def vp010101000010 : Blocks := vp010101000010_0
theorem coverp010101000010 : Covers (-2691761639/2000000 : ℚ) vp010101000010 := cover_leaf (by decide +kernel)
private noncomputable def vp01010100001_0 : Blocks := edgeBlocks% "full/vectors/01010100001-V-0000.bin"
noncomputable def vp01010100001 : Blocks := vp01010100001_0
private theorem bp010101000010 : Branch 0 (-2691761639/4000000 : ℚ) vp01010100001 := by
  apply branch_left_normalized (c:=vp010101000010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2691761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2691761639/2000000 : ℚ) by norm_num]
  exact coverp010101000010
private noncomputable def ep010101000011_0 : Blocks := edgeBlocks% "full/vectors/010101000011-E-0000.bin"
noncomputable def ep010101000011 : Blocks := ep010101000011_0
private theorem idp010101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010100001.list =
    C ((2:ℤ)^109) * horner X vp010101000011.list + horner X ep010101000011.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101000011 : Branch 1 (-2691761639/4000000 : ℚ) vp01010100001 := by
  apply branch_checked idp010101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2691761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2693761639/2000000 : ℚ) by norm_num]
  exact coverp010101000011
theorem coverp01010100001 : Covers (-2691761639/4000000 : ℚ) vp01010100001 := join_branches bp010101000010 bp010101000011
private noncomputable def vp010101000001_0 : Blocks := edgeBlocks% "full/vectors/010101000001-V-0000.bin"
noncomputable def vp010101000001 : Blocks := vp010101000001_0
theorem coverp010101000001 : Covers (-2689761639/2000000 : ℚ) vp010101000001 := cover_leaf (by decide +kernel)
private noncomputable def vp010101000000_0 : Blocks := edgeBlocks% "full/vectors/010101000000-V-0000.bin"
noncomputable def vp010101000000 : Blocks := vp010101000000_0
theorem coverp010101000000 : Covers (-2687761639/2000000 : ℚ) vp010101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp01010100000_0 : Blocks := edgeBlocks% "full/vectors/01010100000-V-0000.bin"
noncomputable def vp01010100000 : Blocks := vp01010100000_0
private theorem bp010101000000 : Branch 0 (-2687761639/4000000 : ℚ) vp01010100000 := by
  apply branch_left_normalized (c:=vp010101000000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2687761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2687761639/2000000 : ℚ) by norm_num]
  exact coverp010101000000
private noncomputable def ep010101000001_0 : Blocks := edgeBlocks% "full/vectors/010101000001-E-0000.bin"
noncomputable def ep010101000001 : Blocks := ep010101000001_0
private theorem idp010101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010100000.list =
    C ((2:ℤ)^110) * horner X vp010101000001.list + horner X ep010101000001.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101000001 : Branch 1 (-2687761639/4000000 : ℚ) vp01010100000 := by
  apply branch_checked idp010101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2687761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2689761639/2000000 : ℚ) by norm_num]
  exact coverp010101000001
theorem coverp01010100000 : Covers (-2687761639/4000000 : ℚ) vp01010100000 := join_branches bp010101000000 bp010101000001
private noncomputable def vp0101010000_0 : Blocks := edgeBlocks% "full/vectors/0101010000-V-0000.bin"
private noncomputable def vp0101010000_1 : Blocks := edgeBlocks% "full/vectors/0101010000-V-0001.bin"
noncomputable def vp0101010000 : Blocks := (Blocks.join vp0101010000_0 vp0101010000_1)
private theorem bp01010100000 : Branch 0 (-2687761639/8000000 : ℚ) vp0101010000 := by
  apply branch_left_normalized (c:=vp01010100000) (k:=0) (m:=97) (by decide +kernel)
  rw [show 2*(-2687761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2687761639/4000000 : ℚ) by norm_num]
  exact coverp01010100000
private noncomputable def ep01010100001_0 : Blocks := edgeBlocks% "full/vectors/01010100001-E-0000.bin"
private noncomputable def ep01010100001_1 : Blocks := edgeBlocks% "full/vectors/01010100001-E-0001.bin"
noncomputable def ep01010100001 : Blocks := (Blocks.join ep01010100001_0 ep01010100001_1)
private theorem idp01010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101010000.list =
    C ((2:ℤ)^197) * horner X vp01010100001.list + horner X ep01010100001.list := by
  exact edge_identity (B := (2:ℤ)^355) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010100001 : Branch 1 (-2687761639/8000000 : ℚ) vp0101010000 := by
  apply branch_checked idp01010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2687761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2691761639/4000000 : ℚ) by norm_num]
  exact coverp01010100001
theorem coverp0101010000 : Covers (-2687761639/8000000 : ℚ) vp0101010000 := join_branches bp01010100000 bp01010100001
private noncomputable def vp010101000_0 : Blocks := edgeBlocks% "full/vectors/010101000-V-0000.bin"
private noncomputable def vp010101000_1 : Blocks := edgeBlocks% "full/vectors/010101000-V-0001.bin"
private noncomputable def vp010101000_2 : Blocks := edgeBlocks% "full/vectors/010101000-V-0002.bin"
noncomputable def vp010101000 : Blocks := (Blocks.join vp010101000_0 (Blocks.join vp010101000_1 vp010101000_2))
private theorem bp0101010000 : Branch 0 (-2687761639/16000000 : ℚ) vp010101000 := by
  apply branch_left_normalized (c:=vp0101010000) (k:=0) (m:=173) (by decide +kernel)
  rw [show 2*(-2687761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2687761639/8000000 : ℚ) by norm_num]
  exact coverp0101010000
private noncomputable def ep0101010001_0 : Blocks := edgeBlocks% "full/vectors/0101010001-E-0000.bin"
private noncomputable def ep0101010001_1 : Blocks := edgeBlocks% "full/vectors/0101010001-E-0001.bin"
private noncomputable def ep0101010001_2 : Blocks := edgeBlocks% "full/vectors/0101010001-E-0002.bin"
noncomputable def ep0101010001 : Blocks := (Blocks.join ep0101010001_0 (Blocks.join ep0101010001_1 ep0101010001_2))
private theorem idp0101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010101000.list =
    C ((2:ℤ)^373) * horner X vp0101010001.list + horner X ep0101010001.list := by
  exact edge_identity (B := (2:ℤ)^588) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101010001 : Branch 1 (-2687761639/16000000 : ℚ) vp010101000 := by
  apply branch_checked idp0101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2687761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2695761639/8000000 : ℚ) by norm_num]
  exact coverp0101010001
theorem coverp010101000 : Covers (-2687761639/16000000 : ℚ) vp010101000 := join_branches bp0101010000 bp0101010001
private noncomputable def vp01010100_0 : Blocks := edgeBlocks% "full/vectors/01010100-V-0000.bin"
private noncomputable def vp01010100_1 : Blocks := edgeBlocks% "full/vectors/01010100-V-0001.bin"
private noncomputable def vp01010100_2 : Blocks := edgeBlocks% "full/vectors/01010100-V-0002.bin"
private noncomputable def vp01010100_3 : Blocks := edgeBlocks% "full/vectors/01010100-V-0003.bin"
private noncomputable def vp01010100_4 : Blocks := edgeBlocks% "full/vectors/01010100-V-0004.bin"
noncomputable def vp01010100 : Blocks := (Blocks.join (Blocks.join vp01010100_0 vp01010100_1) (Blocks.join vp01010100_2 (Blocks.join vp01010100_3 vp01010100_4)))
private theorem bp010101000 : Branch 0 (-2687761639/32000000 : ℚ) vp01010100 := by
  apply branch_left_normalized (c:=vp010101000) (k:=0) (m:=325) (by decide +kernel)
  rw [show 2*(-2687761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2687761639/16000000 : ℚ) by norm_num]
  exact coverp010101000
private noncomputable def ep010101001_0 : Blocks := edgeBlocks% "full/vectors/010101001-E-0000.bin"
private noncomputable def ep010101001_1 : Blocks := edgeBlocks% "full/vectors/010101001-E-0001.bin"
private noncomputable def ep010101001_2 : Blocks := edgeBlocks% "full/vectors/010101001-E-0002.bin"
private noncomputable def ep010101001_3 : Blocks := edgeBlocks% "full/vectors/010101001-E-0003.bin"
private noncomputable def ep010101001_4 : Blocks := edgeBlocks% "full/vectors/010101001-E-0004.bin"
noncomputable def ep010101001 : Blocks := (Blocks.join (Blocks.join ep010101001_0 ep010101001_1) (Blocks.join ep010101001_2 (Blocks.join ep010101001_3 ep010101001_4)))
private theorem idp010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01010100.list =
    C ((2:ℤ)^717) * horner X vp010101001.list + horner X ep010101001.list := by
  exact edge_identity (B := (2:ℤ)^1047) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010101001 : Branch 1 (-2687761639/32000000 : ℚ) vp01010100 := by
  apply branch_checked idp010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2687761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2703761639/16000000 : ℚ) by norm_num]
  exact coverp010101001
theorem coverp01010100 : Covers (-2687761639/32000000 : ℚ) vp01010100 := join_branches bp010101000 bp010101001
private noncomputable def vp0101010_0 : Blocks := edgeBlocks% "full/vectors/0101010-V-0000.bin"
private noncomputable def vp0101010_1 : Blocks := edgeBlocks% "full/vectors/0101010-V-0001.bin"
private noncomputable def vp0101010_2 : Blocks := edgeBlocks% "full/vectors/0101010-V-0002.bin"
private noncomputable def vp0101010_3 : Blocks := edgeBlocks% "full/vectors/0101010-V-0003.bin"
private noncomputable def vp0101010_4 : Blocks := edgeBlocks% "full/vectors/0101010-V-0004.bin"
private noncomputable def vp0101010_5 : Blocks := edgeBlocks% "full/vectors/0101010-V-0005.bin"
private noncomputable def vp0101010_6 : Blocks := edgeBlocks% "full/vectors/0101010-V-0006.bin"
private noncomputable def vp0101010_7 : Blocks := edgeBlocks% "full/vectors/0101010-V-0007.bin"
private noncomputable def vp0101010_8 : Blocks := edgeBlocks% "full/vectors/0101010-V-0008.bin"
private noncomputable def vp0101010_9 : Blocks := edgeBlocks% "full/vectors/0101010-V-0009.bin"
noncomputable def vp0101010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0101010_0 vp0101010_1) (Blocks.join vp0101010_2 (Blocks.join vp0101010_3 vp0101010_4))) (Blocks.join (Blocks.join vp0101010_5 vp0101010_6) (Blocks.join vp0101010_7 (Blocks.join vp0101010_8 vp0101010_9))))
private theorem bp01010100 : Branch 0 (-2687761639/64000000 : ℚ) vp0101010 := by
  apply branch_left_normalized (c:=vp01010100) (k:=0) (m:=624) (by decide +kernel)
  rw [show 2*(-2687761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2687761639/32000000 : ℚ) by norm_num]
  exact coverp01010100
private noncomputable def ep01010101_0 : Blocks := edgeBlocks% "full/vectors/01010101-E-0000.bin"
private noncomputable def ep01010101_1 : Blocks := edgeBlocks% "full/vectors/01010101-E-0001.bin"
private noncomputable def ep01010101_2 : Blocks := edgeBlocks% "full/vectors/01010101-E-0002.bin"
private noncomputable def ep01010101_3 : Blocks := edgeBlocks% "full/vectors/01010101-E-0003.bin"
private noncomputable def ep01010101_4 : Blocks := edgeBlocks% "full/vectors/01010101-E-0004.bin"
private noncomputable def ep01010101_5 : Blocks := edgeBlocks% "full/vectors/01010101-E-0005.bin"
private noncomputable def ep01010101_6 : Blocks := edgeBlocks% "full/vectors/01010101-E-0006.bin"
private noncomputable def ep01010101_7 : Blocks := edgeBlocks% "full/vectors/01010101-E-0007.bin"
private noncomputable def ep01010101_8 : Blocks := edgeBlocks% "full/vectors/01010101-E-0008.bin"
private noncomputable def ep01010101_9 : Blocks := edgeBlocks% "full/vectors/01010101-E-0009.bin"
noncomputable def ep01010101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01010101_0 ep01010101_1) (Blocks.join ep01010101_2 (Blocks.join ep01010101_3 ep01010101_4))) (Blocks.join (Blocks.join ep01010101_5 ep01010101_6) (Blocks.join ep01010101_7 (Blocks.join ep01010101_8 ep01010101_9))))
private theorem idp01010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101010.list =
    C ((2:ℤ)^1399) * horner X vp01010101.list + horner X ep01010101.list := by
  exact edge_identity (B := (2:ℤ)^1956) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01010101 : Branch 1 (-2687761639/64000000 : ℚ) vp0101010 := by
  apply branch_checked idp01010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2687761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2719761639/32000000 : ℚ) by norm_num]
  exact coverp01010101
theorem coverp0101010 : Covers (-2687761639/64000000 : ℚ) vp0101010 := join_branches bp01010100 bp01010101
private noncomputable def vp010101_0 : Blocks := edgeBlocks% "full/vectors/010101-V-0000.bin"
private noncomputable def vp010101_1 : Blocks := edgeBlocks% "full/vectors/010101-V-0001.bin"
private noncomputable def vp010101_2 : Blocks := edgeBlocks% "full/vectors/010101-V-0002.bin"
private noncomputable def vp010101_3 : Blocks := edgeBlocks% "full/vectors/010101-V-0003.bin"
private noncomputable def vp010101_4 : Blocks := edgeBlocks% "full/vectors/010101-V-0004.bin"
private noncomputable def vp010101_5 : Blocks := edgeBlocks% "full/vectors/010101-V-0005.bin"
private noncomputable def vp010101_6 : Blocks := edgeBlocks% "full/vectors/010101-V-0006.bin"
private noncomputable def vp010101_7 : Blocks := edgeBlocks% "full/vectors/010101-V-0007.bin"
private noncomputable def vp010101_8 : Blocks := edgeBlocks% "full/vectors/010101-V-0008.bin"
private noncomputable def vp010101_9 : Blocks := edgeBlocks% "full/vectors/010101-V-0009.bin"
private noncomputable def vp010101_10 : Blocks := edgeBlocks% "full/vectors/010101-V-0010.bin"
private noncomputable def vp010101_11 : Blocks := edgeBlocks% "full/vectors/010101-V-0011.bin"
private noncomputable def vp010101_12 : Blocks := edgeBlocks% "full/vectors/010101-V-0012.bin"
private noncomputable def vp010101_13 : Blocks := edgeBlocks% "full/vectors/010101-V-0013.bin"
private noncomputable def vp010101_14 : Blocks := edgeBlocks% "full/vectors/010101-V-0014.bin"
private noncomputable def vp010101_15 : Blocks := edgeBlocks% "full/vectors/010101-V-0015.bin"
private noncomputable def vp010101_16 : Blocks := edgeBlocks% "full/vectors/010101-V-0016.bin"
private noncomputable def vp010101_17 : Blocks := edgeBlocks% "full/vectors/010101-V-0017.bin"
private noncomputable def vp010101_18 : Blocks := edgeBlocks% "full/vectors/010101-V-0018.bin"
noncomputable def vp010101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp010101_0 vp010101_1) (Blocks.join vp010101_2 vp010101_3)) (Blocks.join (Blocks.join vp010101_4 vp010101_5) (Blocks.join vp010101_6 (Blocks.join vp010101_7 vp010101_8)))) (Blocks.join (Blocks.join (Blocks.join vp010101_9 vp010101_10) (Blocks.join vp010101_11 (Blocks.join vp010101_12 vp010101_13))) (Blocks.join (Blocks.join vp010101_14 vp010101_15) (Blocks.join vp010101_16 (Blocks.join vp010101_17 vp010101_18)))))
private theorem bp0101010 : Branch 0 (-2687761639/128000000 : ℚ) vp010101 := by
  apply branch_left_normalized (c:=vp0101010) (k:=0) (m:=1214) (by decide +kernel)
  rw [show 2*(-2687761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-2687761639/64000000 : ℚ) by norm_num]
  exact coverp0101010
private noncomputable def ep0101011_0 : Blocks := edgeBlocks% "full/vectors/0101011-E-0000.bin"
private noncomputable def ep0101011_1 : Blocks := edgeBlocks% "full/vectors/0101011-E-0001.bin"
private noncomputable def ep0101011_2 : Blocks := edgeBlocks% "full/vectors/0101011-E-0002.bin"
private noncomputable def ep0101011_3 : Blocks := edgeBlocks% "full/vectors/0101011-E-0003.bin"
private noncomputable def ep0101011_4 : Blocks := edgeBlocks% "full/vectors/0101011-E-0004.bin"
private noncomputable def ep0101011_5 : Blocks := edgeBlocks% "full/vectors/0101011-E-0005.bin"
private noncomputable def ep0101011_6 : Blocks := edgeBlocks% "full/vectors/0101011-E-0006.bin"
private noncomputable def ep0101011_7 : Blocks := edgeBlocks% "full/vectors/0101011-E-0007.bin"
private noncomputable def ep0101011_8 : Blocks := edgeBlocks% "full/vectors/0101011-E-0008.bin"
private noncomputable def ep0101011_9 : Blocks := edgeBlocks% "full/vectors/0101011-E-0009.bin"
private noncomputable def ep0101011_10 : Blocks := edgeBlocks% "full/vectors/0101011-E-0010.bin"
private noncomputable def ep0101011_11 : Blocks := edgeBlocks% "full/vectors/0101011-E-0011.bin"
private noncomputable def ep0101011_12 : Blocks := edgeBlocks% "full/vectors/0101011-E-0012.bin"
private noncomputable def ep0101011_13 : Blocks := edgeBlocks% "full/vectors/0101011-E-0013.bin"
private noncomputable def ep0101011_14 : Blocks := edgeBlocks% "full/vectors/0101011-E-0014.bin"
private noncomputable def ep0101011_15 : Blocks := edgeBlocks% "full/vectors/0101011-E-0015.bin"
private noncomputable def ep0101011_16 : Blocks := edgeBlocks% "full/vectors/0101011-E-0016.bin"
private noncomputable def ep0101011_17 : Blocks := edgeBlocks% "full/vectors/0101011-E-0017.bin"
private noncomputable def ep0101011_18 : Blocks := edgeBlocks% "full/vectors/0101011-E-0018.bin"
noncomputable def ep0101011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0101011_0 ep0101011_1) (Blocks.join ep0101011_2 ep0101011_3)) (Blocks.join (Blocks.join ep0101011_4 ep0101011_5) (Blocks.join ep0101011_6 (Blocks.join ep0101011_7 ep0101011_8)))) (Blocks.join (Blocks.join (Blocks.join ep0101011_9 ep0101011_10) (Blocks.join ep0101011_11 (Blocks.join ep0101011_12 ep0101011_13))) (Blocks.join (Blocks.join ep0101011_14 ep0101011_15) (Blocks.join ep0101011_16 (Blocks.join ep0101011_17 ep0101011_18)))))
private theorem idp0101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010101.list =
    C ((2:ℤ)^2731) * horner X vp0101011.list + horner X ep0101011.list := by
  exact edge_identity (B := (2:ℤ)^3735) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101011 : Branch 1 (-2687761639/128000000 : ℚ) vp010101 := by
  apply branch_checked idp0101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2687761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-2751761639/64000000 : ℚ) by norm_num]
  exact coverp0101011
theorem coverp010101 : Covers (-2687761639/128000000 : ℚ) vp010101 := join_branches bp0101010 bp0101011
end NextProof.EdgeFull

