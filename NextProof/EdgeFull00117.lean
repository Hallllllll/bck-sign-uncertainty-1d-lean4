import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp010111111111_0 : Blocks := edgeBlocks% "full/vectors/010111111111-V-0000.bin"
noncomputable def vp010111111111 : Blocks := vp010111111111_0
theorem coverp010111111111 : Covers (-3069761639/2000000 : ℚ) vp010111111111 := cover_leaf (by decide +kernel)
private noncomputable def vp010111111110_0 : Blocks := edgeBlocks% "full/vectors/010111111110-V-0000.bin"
noncomputable def vp010111111110 : Blocks := vp010111111110_0
theorem coverp010111111110 : Covers (-3067761639/2000000 : ℚ) vp010111111110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011111111_0 : Blocks := edgeBlocks% "full/vectors/01011111111-V-0000.bin"
noncomputable def vp01011111111 : Blocks := vp01011111111_0
private theorem bp010111111110 : Branch 0 (-3067761639/4000000 : ℚ) vp01011111111 := by
  apply branch_left_normalized (c:=vp010111111110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3067761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3067761639/2000000 : ℚ) by norm_num]
  exact coverp010111111110
private noncomputable def ep010111111111_0 : Blocks := edgeBlocks% "full/vectors/010111111111-E-0000.bin"
noncomputable def ep010111111111 : Blocks := ep010111111111_0
private theorem idp010111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011111111.list =
    C ((2:ℤ)^104) * horner X vp010111111111.list + horner X ep010111111111.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111111111 : Branch 1 (-3067761639/4000000 : ℚ) vp01011111111 := by
  apply branch_checked idp010111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3067761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3069761639/2000000 : ℚ) by norm_num]
  exact coverp010111111111
theorem coverp01011111111 : Covers (-3067761639/4000000 : ℚ) vp01011111111 := join_branches bp010111111110 bp010111111111
private noncomputable def vp010111111101_0 : Blocks := edgeBlocks% "full/vectors/010111111101-V-0000.bin"
noncomputable def vp010111111101 : Blocks := vp010111111101_0
theorem coverp010111111101 : Covers (-3065761639/2000000 : ℚ) vp010111111101 := cover_leaf (by decide +kernel)
private noncomputable def vp010111111100_0 : Blocks := edgeBlocks% "full/vectors/010111111100-V-0000.bin"
noncomputable def vp010111111100 : Blocks := vp010111111100_0
theorem coverp010111111100 : Covers (-3063761639/2000000 : ℚ) vp010111111100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011111110_0 : Blocks := edgeBlocks% "full/vectors/01011111110-V-0000.bin"
noncomputable def vp01011111110 : Blocks := vp01011111110_0
private theorem bp010111111100 : Branch 0 (-3063761639/4000000 : ℚ) vp01011111110 := by
  apply branch_left_normalized (c:=vp010111111100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3063761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3063761639/2000000 : ℚ) by norm_num]
  exact coverp010111111100
private noncomputable def ep010111111101_0 : Blocks := edgeBlocks% "full/vectors/010111111101-E-0000.bin"
noncomputable def ep010111111101 : Blocks := ep010111111101_0
private theorem idp010111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011111110.list =
    C ((2:ℤ)^103) * horner X vp010111111101.list + horner X ep010111111101.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111111101 : Branch 1 (-3063761639/4000000 : ℚ) vp01011111110 := by
  apply branch_checked idp010111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3063761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3065761639/2000000 : ℚ) by norm_num]
  exact coverp010111111101
theorem coverp01011111110 : Covers (-3063761639/4000000 : ℚ) vp01011111110 := join_branches bp010111111100 bp010111111101
private noncomputable def vp0101111111_0 : Blocks := edgeBlocks% "full/vectors/0101111111-V-0000.bin"
private noncomputable def vp0101111111_1 : Blocks := edgeBlocks% "full/vectors/0101111111-V-0001.bin"
noncomputable def vp0101111111 : Blocks := (Blocks.join vp0101111111_0 vp0101111111_1)
private theorem bp01011111110 : Branch 0 (-3063761639/8000000 : ℚ) vp0101111111 := by
  apply branch_left_normalized (c:=vp01011111110) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-3063761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3063761639/4000000 : ℚ) by norm_num]
  exact coverp01011111110
private noncomputable def ep01011111111_0 : Blocks := edgeBlocks% "full/vectors/01011111111-E-0000.bin"
private noncomputable def ep01011111111_1 : Blocks := edgeBlocks% "full/vectors/01011111111-E-0001.bin"
noncomputable def ep01011111111 : Blocks := (Blocks.join ep01011111111_0 ep01011111111_1)
private theorem idp01011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101111111.list =
    C ((2:ℤ)^188) * horner X vp01011111111.list + horner X ep01011111111.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011111111 : Branch 1 (-3063761639/8000000 : ℚ) vp0101111111 := by
  apply branch_checked idp01011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3063761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3067761639/4000000 : ℚ) by norm_num]
  exact coverp01011111111
theorem coverp0101111111 : Covers (-3063761639/8000000 : ℚ) vp0101111111 := join_branches bp01011111110 bp01011111111
private noncomputable def vp010111111011_0 : Blocks := edgeBlocks% "full/vectors/010111111011-V-0000.bin"
noncomputable def vp010111111011 : Blocks := vp010111111011_0
theorem coverp010111111011 : Covers (-3061761639/2000000 : ℚ) vp010111111011 := cover_leaf (by decide +kernel)
private noncomputable def vp010111111010_0 : Blocks := edgeBlocks% "full/vectors/010111111010-V-0000.bin"
noncomputable def vp010111111010 : Blocks := vp010111111010_0
theorem coverp010111111010 : Covers (-3059761639/2000000 : ℚ) vp010111111010 := cover_leaf (by decide +kernel)
private noncomputable def vp01011111101_0 : Blocks := edgeBlocks% "full/vectors/01011111101-V-0000.bin"
noncomputable def vp01011111101 : Blocks := vp01011111101_0
private theorem bp010111111010 : Branch 0 (-3059761639/4000000 : ℚ) vp01011111101 := by
  apply branch_left_normalized (c:=vp010111111010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3059761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3059761639/2000000 : ℚ) by norm_num]
  exact coverp010111111010
private noncomputable def ep010111111011_0 : Blocks := edgeBlocks% "full/vectors/010111111011-E-0000.bin"
noncomputable def ep010111111011 : Blocks := ep010111111011_0
private theorem idp010111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011111101.list =
    C ((2:ℤ)^104) * horner X vp010111111011.list + horner X ep010111111011.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111111011 : Branch 1 (-3059761639/4000000 : ℚ) vp01011111101 := by
  apply branch_checked idp010111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3059761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3061761639/2000000 : ℚ) by norm_num]
  exact coverp010111111011
theorem coverp01011111101 : Covers (-3059761639/4000000 : ℚ) vp01011111101 := join_branches bp010111111010 bp010111111011
private noncomputable def vp010111111001_0 : Blocks := edgeBlocks% "full/vectors/010111111001-V-0000.bin"
noncomputable def vp010111111001 : Blocks := vp010111111001_0
theorem coverp010111111001 : Covers (-3057761639/2000000 : ℚ) vp010111111001 := cover_leaf (by decide +kernel)
private noncomputable def vp010111111000_0 : Blocks := edgeBlocks% "full/vectors/010111111000-V-0000.bin"
noncomputable def vp010111111000 : Blocks := vp010111111000_0
theorem coverp010111111000 : Covers (-3055761639/2000000 : ℚ) vp010111111000 := cover_leaf (by decide +kernel)
private noncomputable def vp01011111100_0 : Blocks := edgeBlocks% "full/vectors/01011111100-V-0000.bin"
noncomputable def vp01011111100 : Blocks := vp01011111100_0
private theorem bp010111111000 : Branch 0 (-3055761639/4000000 : ℚ) vp01011111100 := by
  apply branch_left_normalized (c:=vp010111111000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3055761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3055761639/2000000 : ℚ) by norm_num]
  exact coverp010111111000
private noncomputable def ep010111111001_0 : Blocks := edgeBlocks% "full/vectors/010111111001-E-0000.bin"
noncomputable def ep010111111001 : Blocks := ep010111111001_0
private theorem idp010111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011111100.list =
    C ((2:ℤ)^104) * horner X vp010111111001.list + horner X ep010111111001.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111111001 : Branch 1 (-3055761639/4000000 : ℚ) vp01011111100 := by
  apply branch_checked idp010111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3055761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3057761639/2000000 : ℚ) by norm_num]
  exact coverp010111111001
theorem coverp01011111100 : Covers (-3055761639/4000000 : ℚ) vp01011111100 := join_branches bp010111111000 bp010111111001
private noncomputable def vp0101111110_0 : Blocks := edgeBlocks% "full/vectors/0101111110-V-0000.bin"
private noncomputable def vp0101111110_1 : Blocks := edgeBlocks% "full/vectors/0101111110-V-0001.bin"
noncomputable def vp0101111110 : Blocks := (Blocks.join vp0101111110_0 vp0101111110_1)
private theorem bp01011111100 : Branch 0 (-3055761639/8000000 : ℚ) vp0101111110 := by
  apply branch_left_normalized (c:=vp01011111100) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-3055761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3055761639/4000000 : ℚ) by norm_num]
  exact coverp01011111100
private noncomputable def ep01011111101_0 : Blocks := edgeBlocks% "full/vectors/01011111101-E-0000.bin"
private noncomputable def ep01011111101_1 : Blocks := edgeBlocks% "full/vectors/01011111101-E-0001.bin"
noncomputable def ep01011111101 : Blocks := (Blocks.join ep01011111101_0 ep01011111101_1)
private theorem idp01011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101111110.list =
    C ((2:ℤ)^188) * horner X vp01011111101.list + horner X ep01011111101.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011111101 : Branch 1 (-3055761639/8000000 : ℚ) vp0101111110 := by
  apply branch_checked idp01011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3055761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3059761639/4000000 : ℚ) by norm_num]
  exact coverp01011111101
theorem coverp0101111110 : Covers (-3055761639/8000000 : ℚ) vp0101111110 := join_branches bp01011111100 bp01011111101
private noncomputable def vp010111111_0 : Blocks := edgeBlocks% "full/vectors/010111111-V-0000.bin"
private noncomputable def vp010111111_1 : Blocks := edgeBlocks% "full/vectors/010111111-V-0001.bin"
private noncomputable def vp010111111_2 : Blocks := edgeBlocks% "full/vectors/010111111-V-0002.bin"
noncomputable def vp010111111 : Blocks := (Blocks.join vp010111111_0 (Blocks.join vp010111111_1 vp010111111_2))
private theorem bp0101111110 : Branch 0 (-3055761639/16000000 : ℚ) vp010111111 := by
  apply branch_left_normalized (c:=vp0101111110) (k:=0) (m:=164) (by decide +kernel)
  rw [show 2*(-3055761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3055761639/8000000 : ℚ) by norm_num]
  exact coverp0101111110
private noncomputable def ep0101111111_0 : Blocks := edgeBlocks% "full/vectors/0101111111-E-0000.bin"
private noncomputable def ep0101111111_1 : Blocks := edgeBlocks% "full/vectors/0101111111-E-0001.bin"
private noncomputable def ep0101111111_2 : Blocks := edgeBlocks% "full/vectors/0101111111-E-0002.bin"
noncomputable def ep0101111111 : Blocks := (Blocks.join ep0101111111_0 (Blocks.join ep0101111111_1 ep0101111111_2))
private theorem idp0101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010111111.list =
    C ((2:ℤ)^352) * horner X vp0101111111.list + horner X ep0101111111.list := by
  exact edge_identity (B := (2:ℤ)^557) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101111111 : Branch 1 (-3055761639/16000000 : ℚ) vp010111111 := by
  apply branch_checked idp0101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3055761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3063761639/8000000 : ℚ) by norm_num]
  exact coverp0101111111
theorem coverp010111111 : Covers (-3055761639/16000000 : ℚ) vp010111111 := join_branches bp0101111110 bp0101111111
private noncomputable def vp010111110111_0 : Blocks := edgeBlocks% "full/vectors/010111110111-V-0000.bin"
noncomputable def vp010111110111 : Blocks := vp010111110111_0
theorem coverp010111110111 : Covers (-3053761639/2000000 : ℚ) vp010111110111 := cover_leaf (by decide +kernel)
private noncomputable def vp010111110110_0 : Blocks := edgeBlocks% "full/vectors/010111110110-V-0000.bin"
noncomputable def vp010111110110 : Blocks := vp010111110110_0
theorem coverp010111110110 : Covers (-3051761639/2000000 : ℚ) vp010111110110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011111011_0 : Blocks := edgeBlocks% "full/vectors/01011111011-V-0000.bin"
noncomputable def vp01011111011 : Blocks := vp01011111011_0
private theorem bp010111110110 : Branch 0 (-3051761639/4000000 : ℚ) vp01011111011 := by
  apply branch_left_normalized (c:=vp010111110110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3051761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3051761639/2000000 : ℚ) by norm_num]
  exact coverp010111110110
private noncomputable def ep010111110111_0 : Blocks := edgeBlocks% "full/vectors/010111110111-E-0000.bin"
noncomputable def ep010111110111 : Blocks := ep010111110111_0
private theorem idp010111110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011111011.list =
    C ((2:ℤ)^105) * horner X vp010111110111.list + horner X ep010111110111.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111110111 : Branch 1 (-3051761639/4000000 : ℚ) vp01011111011 := by
  apply branch_checked idp010111110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3051761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3053761639/2000000 : ℚ) by norm_num]
  exact coverp010111110111
theorem coverp01011111011 : Covers (-3051761639/4000000 : ℚ) vp01011111011 := join_branches bp010111110110 bp010111110111
private noncomputable def vp010111110101_0 : Blocks := edgeBlocks% "full/vectors/010111110101-V-0000.bin"
noncomputable def vp010111110101 : Blocks := vp010111110101_0
theorem coverp010111110101 : Covers (-3049761639/2000000 : ℚ) vp010111110101 := cover_leaf (by decide +kernel)
private noncomputable def vp010111110100_0 : Blocks := edgeBlocks% "full/vectors/010111110100-V-0000.bin"
noncomputable def vp010111110100 : Blocks := vp010111110100_0
theorem coverp010111110100 : Covers (-3047761639/2000000 : ℚ) vp010111110100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011111010_0 : Blocks := edgeBlocks% "full/vectors/01011111010-V-0000.bin"
noncomputable def vp01011111010 : Blocks := vp01011111010_0
private theorem bp010111110100 : Branch 0 (-3047761639/4000000 : ℚ) vp01011111010 := by
  apply branch_left_normalized (c:=vp010111110100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3047761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3047761639/2000000 : ℚ) by norm_num]
  exact coverp010111110100
private noncomputable def ep010111110101_0 : Blocks := edgeBlocks% "full/vectors/010111110101-E-0000.bin"
noncomputable def ep010111110101 : Blocks := ep010111110101_0
private theorem idp010111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011111010.list =
    C ((2:ℤ)^105) * horner X vp010111110101.list + horner X ep010111110101.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111110101 : Branch 1 (-3047761639/4000000 : ℚ) vp01011111010 := by
  apply branch_checked idp010111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3047761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3049761639/2000000 : ℚ) by norm_num]
  exact coverp010111110101
theorem coverp01011111010 : Covers (-3047761639/4000000 : ℚ) vp01011111010 := join_branches bp010111110100 bp010111110101
private noncomputable def vp0101111101_0 : Blocks := edgeBlocks% "full/vectors/0101111101-V-0000.bin"
private noncomputable def vp0101111101_1 : Blocks := edgeBlocks% "full/vectors/0101111101-V-0001.bin"
noncomputable def vp0101111101 : Blocks := (Blocks.join vp0101111101_0 vp0101111101_1)
private theorem bp01011111010 : Branch 0 (-3047761639/8000000 : ℚ) vp0101111101 := by
  apply branch_left_normalized (c:=vp01011111010) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-3047761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3047761639/4000000 : ℚ) by norm_num]
  exact coverp01011111010
private noncomputable def ep01011111011_0 : Blocks := edgeBlocks% "full/vectors/01011111011-E-0000.bin"
private noncomputable def ep01011111011_1 : Blocks := edgeBlocks% "full/vectors/01011111011-E-0001.bin"
noncomputable def ep01011111011 : Blocks := (Blocks.join ep01011111011_0 ep01011111011_1)
private theorem idp01011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101111101.list =
    C ((2:ℤ)^188) * horner X vp01011111011.list + horner X ep01011111011.list := by
  exact edge_identity (B := (2:ℤ)^342) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011111011 : Branch 1 (-3047761639/8000000 : ℚ) vp0101111101 := by
  apply branch_checked idp01011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3047761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3051761639/4000000 : ℚ) by norm_num]
  exact coverp01011111011
theorem coverp0101111101 : Covers (-3047761639/8000000 : ℚ) vp0101111101 := join_branches bp01011111010 bp01011111011
private noncomputable def vp010111110011_0 : Blocks := edgeBlocks% "full/vectors/010111110011-V-0000.bin"
noncomputable def vp010111110011 : Blocks := vp010111110011_0
theorem coverp010111110011 : Covers (-3045761639/2000000 : ℚ) vp010111110011 := cover_leaf (by decide +kernel)
private noncomputable def vp010111110010_0 : Blocks := edgeBlocks% "full/vectors/010111110010-V-0000.bin"
noncomputable def vp010111110010 : Blocks := vp010111110010_0
theorem coverp010111110010 : Covers (-3043761639/2000000 : ℚ) vp010111110010 := cover_leaf (by decide +kernel)
private noncomputable def vp01011111001_0 : Blocks := edgeBlocks% "full/vectors/01011111001-V-0000.bin"
noncomputable def vp01011111001 : Blocks := vp01011111001_0
private theorem bp010111110010 : Branch 0 (-3043761639/4000000 : ℚ) vp01011111001 := by
  apply branch_left_normalized (c:=vp010111110010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3043761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3043761639/2000000 : ℚ) by norm_num]
  exact coverp010111110010
private noncomputable def ep010111110011_0 : Blocks := edgeBlocks% "full/vectors/010111110011-E-0000.bin"
noncomputable def ep010111110011 : Blocks := ep010111110011_0
private theorem idp010111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011111001.list =
    C ((2:ℤ)^103) * horner X vp010111110011.list + horner X ep010111110011.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111110011 : Branch 1 (-3043761639/4000000 : ℚ) vp01011111001 := by
  apply branch_checked idp010111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3043761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3045761639/2000000 : ℚ) by norm_num]
  exact coverp010111110011
theorem coverp01011111001 : Covers (-3043761639/4000000 : ℚ) vp01011111001 := join_branches bp010111110010 bp010111110011
private noncomputable def vp010111110001_0 : Blocks := edgeBlocks% "full/vectors/010111110001-V-0000.bin"
noncomputable def vp010111110001 : Blocks := vp010111110001_0
theorem coverp010111110001 : Covers (-3041761639/2000000 : ℚ) vp010111110001 := cover_leaf (by decide +kernel)
private noncomputable def vp010111110000_0 : Blocks := edgeBlocks% "full/vectors/010111110000-V-0000.bin"
noncomputable def vp010111110000 : Blocks := vp010111110000_0
theorem coverp010111110000 : Covers (-3039761639/2000000 : ℚ) vp010111110000 := cover_leaf (by decide +kernel)
private noncomputable def vp01011111000_0 : Blocks := edgeBlocks% "full/vectors/01011111000-V-0000.bin"
noncomputable def vp01011111000 : Blocks := vp01011111000_0
private theorem bp010111110000 : Branch 0 (-3039761639/4000000 : ℚ) vp01011111000 := by
  apply branch_left_normalized (c:=vp010111110000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3039761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3039761639/2000000 : ℚ) by norm_num]
  exact coverp010111110000
private noncomputable def ep010111110001_0 : Blocks := edgeBlocks% "full/vectors/010111110001-E-0000.bin"
noncomputable def ep010111110001 : Blocks := ep010111110001_0
private theorem idp010111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011111000.list =
    C ((2:ℤ)^105) * horner X vp010111110001.list + horner X ep010111110001.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111110001 : Branch 1 (-3039761639/4000000 : ℚ) vp01011111000 := by
  apply branch_checked idp010111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3039761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3041761639/2000000 : ℚ) by norm_num]
  exact coverp010111110001
theorem coverp01011111000 : Covers (-3039761639/4000000 : ℚ) vp01011111000 := join_branches bp010111110000 bp010111110001
private noncomputable def vp0101111100_0 : Blocks := edgeBlocks% "full/vectors/0101111100-V-0000.bin"
private noncomputable def vp0101111100_1 : Blocks := edgeBlocks% "full/vectors/0101111100-V-0001.bin"
noncomputable def vp0101111100 : Blocks := (Blocks.join vp0101111100_0 vp0101111100_1)
private theorem bp01011111000 : Branch 0 (-3039761639/8000000 : ℚ) vp0101111100 := by
  apply branch_left_normalized (c:=vp01011111000) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-3039761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3039761639/4000000 : ℚ) by norm_num]
  exact coverp01011111000
private noncomputable def ep01011111001_0 : Blocks := edgeBlocks% "full/vectors/01011111001-E-0000.bin"
private noncomputable def ep01011111001_1 : Blocks := edgeBlocks% "full/vectors/01011111001-E-0001.bin"
noncomputable def ep01011111001 : Blocks := (Blocks.join ep01011111001_0 ep01011111001_1)
private theorem idp01011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101111100.list =
    C ((2:ℤ)^188) * horner X vp01011111001.list + horner X ep01011111001.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011111001 : Branch 1 (-3039761639/8000000 : ℚ) vp0101111100 := by
  apply branch_checked idp01011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3039761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3043761639/4000000 : ℚ) by norm_num]
  exact coverp01011111001
theorem coverp0101111100 : Covers (-3039761639/8000000 : ℚ) vp0101111100 := join_branches bp01011111000 bp01011111001
private noncomputable def vp010111110_0 : Blocks := edgeBlocks% "full/vectors/010111110-V-0000.bin"
private noncomputable def vp010111110_1 : Blocks := edgeBlocks% "full/vectors/010111110-V-0001.bin"
private noncomputable def vp010111110_2 : Blocks := edgeBlocks% "full/vectors/010111110-V-0002.bin"
noncomputable def vp010111110 : Blocks := (Blocks.join vp010111110_0 (Blocks.join vp010111110_1 vp010111110_2))
private theorem bp0101111100 : Branch 0 (-3039761639/16000000 : ℚ) vp010111110 := by
  apply branch_left_normalized (c:=vp0101111100) (k:=0) (m:=164) (by decide +kernel)
  rw [show 2*(-3039761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3039761639/8000000 : ℚ) by norm_num]
  exact coverp0101111100
private noncomputable def ep0101111101_0 : Blocks := edgeBlocks% "full/vectors/0101111101-E-0000.bin"
private noncomputable def ep0101111101_1 : Blocks := edgeBlocks% "full/vectors/0101111101-E-0001.bin"
private noncomputable def ep0101111101_2 : Blocks := edgeBlocks% "full/vectors/0101111101-E-0002.bin"
noncomputable def ep0101111101 : Blocks := (Blocks.join ep0101111101_0 (Blocks.join ep0101111101_1 ep0101111101_2))
private theorem idp0101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010111110.list =
    C ((2:ℤ)^352) * horner X vp0101111101.list + horner X ep0101111101.list := by
  exact edge_identity (B := (2:ℤ)^558) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101111101 : Branch 1 (-3039761639/16000000 : ℚ) vp010111110 := by
  apply branch_checked idp0101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3039761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3047761639/8000000 : ℚ) by norm_num]
  exact coverp0101111101
theorem coverp010111110 : Covers (-3039761639/16000000 : ℚ) vp010111110 := join_branches bp0101111100 bp0101111101
private noncomputable def vp01011111_0 : Blocks := edgeBlocks% "full/vectors/01011111-V-0000.bin"
private noncomputable def vp01011111_1 : Blocks := edgeBlocks% "full/vectors/01011111-V-0001.bin"
private noncomputable def vp01011111_2 : Blocks := edgeBlocks% "full/vectors/01011111-V-0002.bin"
private noncomputable def vp01011111_3 : Blocks := edgeBlocks% "full/vectors/01011111-V-0003.bin"
private noncomputable def vp01011111_4 : Blocks := edgeBlocks% "full/vectors/01011111-V-0004.bin"
noncomputable def vp01011111 : Blocks := (Blocks.join (Blocks.join vp01011111_0 vp01011111_1) (Blocks.join vp01011111_2 (Blocks.join vp01011111_3 vp01011111_4)))
private theorem bp010111110 : Branch 0 (-3039761639/32000000 : ℚ) vp01011111 := by
  apply branch_left_normalized (c:=vp010111110) (k:=0) (m:=306) (by decide +kernel)
  rw [show 2*(-3039761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3039761639/16000000 : ℚ) by norm_num]
  exact coverp010111110
private noncomputable def ep010111111_0 : Blocks := edgeBlocks% "full/vectors/010111111-E-0000.bin"
private noncomputable def ep010111111_1 : Blocks := edgeBlocks% "full/vectors/010111111-E-0001.bin"
private noncomputable def ep010111111_2 : Blocks := edgeBlocks% "full/vectors/010111111-E-0002.bin"
private noncomputable def ep010111111_3 : Blocks := edgeBlocks% "full/vectors/010111111-E-0003.bin"
private noncomputable def ep010111111_4 : Blocks := edgeBlocks% "full/vectors/010111111-E-0004.bin"
noncomputable def ep010111111 : Blocks := (Blocks.join (Blocks.join ep010111111_0 ep010111111_1) (Blocks.join ep010111111_2 (Blocks.join ep010111111_3 ep010111111_4)))
private theorem idp010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011111.list =
    C ((2:ℤ)^681) * horner X vp010111111.list + horner X ep010111111.list := by
  exact edge_identity (B := (2:ℤ)^991) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111111 : Branch 1 (-3039761639/32000000 : ℚ) vp01011111 := by
  apply branch_checked idp010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3039761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3055761639/16000000 : ℚ) by norm_num]
  exact coverp010111111
theorem coverp01011111 : Covers (-3039761639/32000000 : ℚ) vp01011111 := join_branches bp010111110 bp010111111
private noncomputable def vp010111101111_0 : Blocks := edgeBlocks% "full/vectors/010111101111-V-0000.bin"
noncomputable def vp010111101111 : Blocks := vp010111101111_0
theorem coverp010111101111 : Covers (-3037761639/2000000 : ℚ) vp010111101111 := cover_leaf (by decide +kernel)
private noncomputable def vp010111101110_0 : Blocks := edgeBlocks% "full/vectors/010111101110-V-0000.bin"
noncomputable def vp010111101110 : Blocks := vp010111101110_0
theorem coverp010111101110 : Covers (-3035761639/2000000 : ℚ) vp010111101110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011110111_0 : Blocks := edgeBlocks% "full/vectors/01011110111-V-0000.bin"
noncomputable def vp01011110111 : Blocks := vp01011110111_0
private theorem bp010111101110 : Branch 0 (-3035761639/4000000 : ℚ) vp01011110111 := by
  apply branch_left_normalized (c:=vp010111101110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3035761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3035761639/2000000 : ℚ) by norm_num]
  exact coverp010111101110
private noncomputable def ep010111101111_0 : Blocks := edgeBlocks% "full/vectors/010111101111-E-0000.bin"
noncomputable def ep010111101111 : Blocks := ep010111101111_0
private theorem idp010111101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011110111.list =
    C ((2:ℤ)^105) * horner X vp010111101111.list + horner X ep010111101111.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111101111 : Branch 1 (-3035761639/4000000 : ℚ) vp01011110111 := by
  apply branch_checked idp010111101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3035761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3037761639/2000000 : ℚ) by norm_num]
  exact coverp010111101111
theorem coverp01011110111 : Covers (-3035761639/4000000 : ℚ) vp01011110111 := join_branches bp010111101110 bp010111101111
private noncomputable def vp010111101101_0 : Blocks := edgeBlocks% "full/vectors/010111101101-V-0000.bin"
noncomputable def vp010111101101 : Blocks := vp010111101101_0
theorem coverp010111101101 : Covers (-3033761639/2000000 : ℚ) vp010111101101 := cover_leaf (by decide +kernel)
private noncomputable def vp010111101100_0 : Blocks := edgeBlocks% "full/vectors/010111101100-V-0000.bin"
noncomputable def vp010111101100 : Blocks := vp010111101100_0
theorem coverp010111101100 : Covers (-3031761639/2000000 : ℚ) vp010111101100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011110110_0 : Blocks := edgeBlocks% "full/vectors/01011110110-V-0000.bin"
noncomputable def vp01011110110 : Blocks := vp01011110110_0
private theorem bp010111101100 : Branch 0 (-3031761639/4000000 : ℚ) vp01011110110 := by
  apply branch_left_normalized (c:=vp010111101100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-3031761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3031761639/2000000 : ℚ) by norm_num]
  exact coverp010111101100
private noncomputable def ep010111101101_0 : Blocks := edgeBlocks% "full/vectors/010111101101-E-0000.bin"
noncomputable def ep010111101101 : Blocks := ep010111101101_0
private theorem idp010111101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011110110.list =
    C ((2:ℤ)^104) * horner X vp010111101101.list + horner X ep010111101101.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111101101 : Branch 1 (-3031761639/4000000 : ℚ) vp01011110110 := by
  apply branch_checked idp010111101101 (by positivity) (by decide +kernel)
  rw [show 2*(-3031761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3033761639/2000000 : ℚ) by norm_num]
  exact coverp010111101101
theorem coverp01011110110 : Covers (-3031761639/4000000 : ℚ) vp01011110110 := join_branches bp010111101100 bp010111101101
private noncomputable def vp0101111011_0 : Blocks := edgeBlocks% "full/vectors/0101111011-V-0000.bin"
private noncomputable def vp0101111011_1 : Blocks := edgeBlocks% "full/vectors/0101111011-V-0001.bin"
noncomputable def vp0101111011 : Blocks := (Blocks.join vp0101111011_0 vp0101111011_1)
private theorem bp01011110110 : Branch 0 (-3031761639/8000000 : ℚ) vp0101111011 := by
  apply branch_left_normalized (c:=vp01011110110) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-3031761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3031761639/4000000 : ℚ) by norm_num]
  exact coverp01011110110
private noncomputable def ep01011110111_0 : Blocks := edgeBlocks% "full/vectors/01011110111-E-0000.bin"
private noncomputable def ep01011110111_1 : Blocks := edgeBlocks% "full/vectors/01011110111-E-0001.bin"
noncomputable def ep01011110111 : Blocks := (Blocks.join ep01011110111_0 ep01011110111_1)
private theorem idp01011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101111011.list =
    C ((2:ℤ)^188) * horner X vp01011110111.list + horner X ep01011110111.list := by
  exact edge_identity (B := (2:ℤ)^342) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011110111 : Branch 1 (-3031761639/8000000 : ℚ) vp0101111011 := by
  apply branch_checked idp01011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3031761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3035761639/4000000 : ℚ) by norm_num]
  exact coverp01011110111
theorem coverp0101111011 : Covers (-3031761639/8000000 : ℚ) vp0101111011 := join_branches bp01011110110 bp01011110111
private noncomputable def vp010111101011_0 : Blocks := edgeBlocks% "full/vectors/010111101011-V-0000.bin"
noncomputable def vp010111101011 : Blocks := vp010111101011_0
theorem coverp010111101011 : Covers (-3029761639/2000000 : ℚ) vp010111101011 := cover_leaf (by decide +kernel)
private noncomputable def vp010111101010_0 : Blocks := edgeBlocks% "full/vectors/010111101010-V-0000.bin"
noncomputable def vp010111101010 : Blocks := vp010111101010_0
theorem coverp010111101010 : Covers (-3027761639/2000000 : ℚ) vp010111101010 := cover_leaf (by decide +kernel)
private noncomputable def vp01011110101_0 : Blocks := edgeBlocks% "full/vectors/01011110101-V-0000.bin"
noncomputable def vp01011110101 : Blocks := vp01011110101_0
private theorem bp010111101010 : Branch 0 (-3027761639/4000000 : ℚ) vp01011110101 := by
  apply branch_left_normalized (c:=vp010111101010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3027761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3027761639/2000000 : ℚ) by norm_num]
  exact coverp010111101010
private noncomputable def ep010111101011_0 : Blocks := edgeBlocks% "full/vectors/010111101011-E-0000.bin"
noncomputable def ep010111101011 : Blocks := ep010111101011_0
private theorem idp010111101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011110101.list =
    C ((2:ℤ)^103) * horner X vp010111101011.list + horner X ep010111101011.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111101011 : Branch 1 (-3027761639/4000000 : ℚ) vp01011110101 := by
  apply branch_checked idp010111101011 (by positivity) (by decide +kernel)
  rw [show 2*(-3027761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3029761639/2000000 : ℚ) by norm_num]
  exact coverp010111101011
theorem coverp01011110101 : Covers (-3027761639/4000000 : ℚ) vp01011110101 := join_branches bp010111101010 bp010111101011
private noncomputable def vp010111101001_0 : Blocks := edgeBlocks% "full/vectors/010111101001-V-0000.bin"
noncomputable def vp010111101001 : Blocks := vp010111101001_0
theorem coverp010111101001 : Covers (-3025761639/2000000 : ℚ) vp010111101001 := cover_leaf (by decide +kernel)
private noncomputable def vp010111101000_0 : Blocks := edgeBlocks% "full/vectors/010111101000-V-0000.bin"
noncomputable def vp010111101000 : Blocks := vp010111101000_0
theorem coverp010111101000 : Covers (-3023761639/2000000 : ℚ) vp010111101000 := cover_leaf (by decide +kernel)
private noncomputable def vp01011110100_0 : Blocks := edgeBlocks% "full/vectors/01011110100-V-0000.bin"
noncomputable def vp01011110100 : Blocks := vp01011110100_0
private theorem bp010111101000 : Branch 0 (-3023761639/4000000 : ℚ) vp01011110100 := by
  apply branch_left_normalized (c:=vp010111101000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3023761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3023761639/2000000 : ℚ) by norm_num]
  exact coverp010111101000
private noncomputable def ep010111101001_0 : Blocks := edgeBlocks% "full/vectors/010111101001-E-0000.bin"
noncomputable def ep010111101001 : Blocks := ep010111101001_0
private theorem idp010111101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011110100.list =
    C ((2:ℤ)^104) * horner X vp010111101001.list + horner X ep010111101001.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111101001 : Branch 1 (-3023761639/4000000 : ℚ) vp01011110100 := by
  apply branch_checked idp010111101001 (by positivity) (by decide +kernel)
  rw [show 2*(-3023761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3025761639/2000000 : ℚ) by norm_num]
  exact coverp010111101001
theorem coverp01011110100 : Covers (-3023761639/4000000 : ℚ) vp01011110100 := join_branches bp010111101000 bp010111101001
private noncomputable def vp0101111010_0 : Blocks := edgeBlocks% "full/vectors/0101111010-V-0000.bin"
private noncomputable def vp0101111010_1 : Blocks := edgeBlocks% "full/vectors/0101111010-V-0001.bin"
noncomputable def vp0101111010 : Blocks := (Blocks.join vp0101111010_0 vp0101111010_1)
private theorem bp01011110100 : Branch 0 (-3023761639/8000000 : ℚ) vp0101111010 := by
  apply branch_left_normalized (c:=vp01011110100) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-3023761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3023761639/4000000 : ℚ) by norm_num]
  exact coverp01011110100
private noncomputable def ep01011110101_0 : Blocks := edgeBlocks% "full/vectors/01011110101-E-0000.bin"
private noncomputable def ep01011110101_1 : Blocks := edgeBlocks% "full/vectors/01011110101-E-0001.bin"
noncomputable def ep01011110101 : Blocks := (Blocks.join ep01011110101_0 ep01011110101_1)
private theorem idp01011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101111010.list =
    C ((2:ℤ)^187) * horner X vp01011110101.list + horner X ep01011110101.list := by
  exact edge_identity (B := (2:ℤ)^339) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011110101 : Branch 1 (-3023761639/8000000 : ℚ) vp0101111010 := by
  apply branch_checked idp01011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3023761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3027761639/4000000 : ℚ) by norm_num]
  exact coverp01011110101
theorem coverp0101111010 : Covers (-3023761639/8000000 : ℚ) vp0101111010 := join_branches bp01011110100 bp01011110101
private noncomputable def vp010111101_0 : Blocks := edgeBlocks% "full/vectors/010111101-V-0000.bin"
private noncomputable def vp010111101_1 : Blocks := edgeBlocks% "full/vectors/010111101-V-0001.bin"
private noncomputable def vp010111101_2 : Blocks := edgeBlocks% "full/vectors/010111101-V-0002.bin"
noncomputable def vp010111101 : Blocks := (Blocks.join vp010111101_0 (Blocks.join vp010111101_1 vp010111101_2))
private theorem bp0101111010 : Branch 0 (-3023761639/16000000 : ℚ) vp010111101 := by
  apply branch_left_normalized (c:=vp0101111010) (k:=0) (m:=163) (by decide +kernel)
  rw [show 2*(-3023761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3023761639/8000000 : ℚ) by norm_num]
  exact coverp0101111010
private noncomputable def ep0101111011_0 : Blocks := edgeBlocks% "full/vectors/0101111011-E-0000.bin"
private noncomputable def ep0101111011_1 : Blocks := edgeBlocks% "full/vectors/0101111011-E-0001.bin"
private noncomputable def ep0101111011_2 : Blocks := edgeBlocks% "full/vectors/0101111011-E-0002.bin"
noncomputable def ep0101111011 : Blocks := (Blocks.join ep0101111011_0 (Blocks.join ep0101111011_1 ep0101111011_2))
private theorem idp0101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010111101.list =
    C ((2:ℤ)^351) * horner X vp0101111011.list + horner X ep0101111011.list := by
  exact edge_identity (B := (2:ℤ)^558) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101111011 : Branch 1 (-3023761639/16000000 : ℚ) vp010111101 := by
  apply branch_checked idp0101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3023761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3031761639/8000000 : ℚ) by norm_num]
  exact coverp0101111011
theorem coverp010111101 : Covers (-3023761639/16000000 : ℚ) vp010111101 := join_branches bp0101111010 bp0101111011
private noncomputable def vp010111100111_0 : Blocks := edgeBlocks% "full/vectors/010111100111-V-0000.bin"
noncomputable def vp010111100111 : Blocks := vp010111100111_0
theorem coverp010111100111 : Covers (-3021761639/2000000 : ℚ) vp010111100111 := cover_leaf (by decide +kernel)
private noncomputable def vp010111100110_0 : Blocks := edgeBlocks% "full/vectors/010111100110-V-0000.bin"
noncomputable def vp010111100110 : Blocks := vp010111100110_0
theorem coverp010111100110 : Covers (-3019761639/2000000 : ℚ) vp010111100110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011110011_0 : Blocks := edgeBlocks% "full/vectors/01011110011-V-0000.bin"
noncomputable def vp01011110011 : Blocks := vp01011110011_0
private theorem bp010111100110 : Branch 0 (-3019761639/4000000 : ℚ) vp01011110011 := by
  apply branch_left_normalized (c:=vp010111100110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3019761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3019761639/2000000 : ℚ) by norm_num]
  exact coverp010111100110
private noncomputable def ep010111100111_0 : Blocks := edgeBlocks% "full/vectors/010111100111-E-0000.bin"
noncomputable def ep010111100111 : Blocks := ep010111100111_0
private theorem idp010111100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011110011.list =
    C ((2:ℤ)^104) * horner X vp010111100111.list + horner X ep010111100111.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111100111 : Branch 1 (-3019761639/4000000 : ℚ) vp01011110011 := by
  apply branch_checked idp010111100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3019761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3021761639/2000000 : ℚ) by norm_num]
  exact coverp010111100111
theorem coverp01011110011 : Covers (-3019761639/4000000 : ℚ) vp01011110011 := join_branches bp010111100110 bp010111100111
private noncomputable def vp010111100101_0 : Blocks := edgeBlocks% "full/vectors/010111100101-V-0000.bin"
noncomputable def vp010111100101 : Blocks := vp010111100101_0
theorem coverp010111100101 : Covers (-3017761639/2000000 : ℚ) vp010111100101 := cover_leaf (by decide +kernel)
private noncomputable def vp010111100100_0 : Blocks := edgeBlocks% "full/vectors/010111100100-V-0000.bin"
noncomputable def vp010111100100 : Blocks := vp010111100100_0
theorem coverp010111100100 : Covers (-3015761639/2000000 : ℚ) vp010111100100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011110010_0 : Blocks := edgeBlocks% "full/vectors/01011110010-V-0000.bin"
noncomputable def vp01011110010 : Blocks := vp01011110010_0
private theorem bp010111100100 : Branch 0 (-3015761639/4000000 : ℚ) vp01011110010 := by
  apply branch_left_normalized (c:=vp010111100100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3015761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3015761639/2000000 : ℚ) by norm_num]
  exact coverp010111100100
private noncomputable def ep010111100101_0 : Blocks := edgeBlocks% "full/vectors/010111100101-E-0000.bin"
noncomputable def ep010111100101 : Blocks := ep010111100101_0
private theorem idp010111100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011110010.list =
    C ((2:ℤ)^103) * horner X vp010111100101.list + horner X ep010111100101.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111100101 : Branch 1 (-3015761639/4000000 : ℚ) vp01011110010 := by
  apply branch_checked idp010111100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3015761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3017761639/2000000 : ℚ) by norm_num]
  exact coverp010111100101
theorem coverp01011110010 : Covers (-3015761639/4000000 : ℚ) vp01011110010 := join_branches bp010111100100 bp010111100101
private noncomputable def vp0101111001_0 : Blocks := edgeBlocks% "full/vectors/0101111001-V-0000.bin"
private noncomputable def vp0101111001_1 : Blocks := edgeBlocks% "full/vectors/0101111001-V-0001.bin"
noncomputable def vp0101111001 : Blocks := (Blocks.join vp0101111001_0 vp0101111001_1)
private theorem bp01011110010 : Branch 0 (-3015761639/8000000 : ℚ) vp0101111001 := by
  apply branch_left_normalized (c:=vp01011110010) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-3015761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3015761639/4000000 : ℚ) by norm_num]
  exact coverp01011110010
private noncomputable def ep01011110011_0 : Blocks := edgeBlocks% "full/vectors/01011110011-E-0000.bin"
private noncomputable def ep01011110011_1 : Blocks := edgeBlocks% "full/vectors/01011110011-E-0001.bin"
noncomputable def ep01011110011 : Blocks := (Blocks.join ep01011110011_0 ep01011110011_1)
private theorem idp01011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101111001.list =
    C ((2:ℤ)^186) * horner X vp01011110011.list + horner X ep01011110011.list := by
  exact edge_identity (B := (2:ℤ)^338) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011110011 : Branch 1 (-3015761639/8000000 : ℚ) vp0101111001 := by
  apply branch_checked idp01011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3015761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3019761639/4000000 : ℚ) by norm_num]
  exact coverp01011110011
theorem coverp0101111001 : Covers (-3015761639/8000000 : ℚ) vp0101111001 := join_branches bp01011110010 bp01011110011
private noncomputable def vp01011110001_0 : Blocks := edgeBlocks% "full/vectors/01011110001-V-0000.bin"
noncomputable def vp01011110001 : Blocks := vp01011110001_0
theorem coverp01011110001 : Covers (-3011761639/4000000 : ℚ) vp01011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp01011110000_0 : Blocks := edgeBlocks% "full/vectors/01011110000-V-0000.bin"
noncomputable def vp01011110000 : Blocks := vp01011110000_0
theorem coverp01011110000 : Covers (-3007761639/4000000 : ℚ) vp01011110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0101111000_0 : Blocks := edgeBlocks% "full/vectors/0101111000-V-0000.bin"
private noncomputable def vp0101111000_1 : Blocks := edgeBlocks% "full/vectors/0101111000-V-0001.bin"
noncomputable def vp0101111000 : Blocks := (Blocks.join vp0101111000_0 vp0101111000_1)
private theorem bp01011110000 : Branch 0 (-3007761639/8000000 : ℚ) vp0101111000 := by
  apply branch_left_normalized (c:=vp01011110000) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-3007761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3007761639/4000000 : ℚ) by norm_num]
  exact coverp01011110000
private noncomputable def ep01011110001_0 : Blocks := edgeBlocks% "full/vectors/01011110001-E-0000.bin"
private noncomputable def ep01011110001_1 : Blocks := edgeBlocks% "full/vectors/01011110001-E-0001.bin"
noncomputable def ep01011110001 : Blocks := (Blocks.join ep01011110001_0 ep01011110001_1)
private theorem idp01011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101111000.list =
    C ((2:ℤ)^183) * horner X vp01011110001.list + horner X ep01011110001.list := by
  exact edge_identity (B := (2:ℤ)^332) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011110001 : Branch 1 (-3007761639/8000000 : ℚ) vp0101111000 := by
  apply branch_checked idp01011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3007761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3011761639/4000000 : ℚ) by norm_num]
  exact coverp01011110001
theorem coverp0101111000 : Covers (-3007761639/8000000 : ℚ) vp0101111000 := join_branches bp01011110000 bp01011110001
private noncomputable def vp010111100_0 : Blocks := edgeBlocks% "full/vectors/010111100-V-0000.bin"
private noncomputable def vp010111100_1 : Blocks := edgeBlocks% "full/vectors/010111100-V-0001.bin"
private noncomputable def vp010111100_2 : Blocks := edgeBlocks% "full/vectors/010111100-V-0002.bin"
noncomputable def vp010111100 : Blocks := (Blocks.join vp010111100_0 (Blocks.join vp010111100_1 vp010111100_2))
private theorem bp0101111000 : Branch 0 (-3007761639/16000000 : ℚ) vp010111100 := by
  apply branch_left_normalized (c:=vp0101111000) (k:=0) (m:=161) (by decide +kernel)
  rw [show 2*(-3007761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3007761639/8000000 : ℚ) by norm_num]
  exact coverp0101111000
private noncomputable def ep0101111001_0 : Blocks := edgeBlocks% "full/vectors/0101111001-E-0000.bin"
private noncomputable def ep0101111001_1 : Blocks := edgeBlocks% "full/vectors/0101111001-E-0001.bin"
private noncomputable def ep0101111001_2 : Blocks := edgeBlocks% "full/vectors/0101111001-E-0002.bin"
noncomputable def ep0101111001 : Blocks := (Blocks.join ep0101111001_0 (Blocks.join ep0101111001_1 ep0101111001_2))
private theorem idp0101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010111100.list =
    C ((2:ℤ)^346) * horner X vp0101111001.list + horner X ep0101111001.list := by
  exact edge_identity (B := (2:ℤ)^550) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101111001 : Branch 1 (-3007761639/16000000 : ℚ) vp010111100 := by
  apply branch_checked idp0101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3007761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3015761639/8000000 : ℚ) by norm_num]
  exact coverp0101111001
theorem coverp010111100 : Covers (-3007761639/16000000 : ℚ) vp010111100 := join_branches bp0101111000 bp0101111001
private noncomputable def vp01011110_0 : Blocks := edgeBlocks% "full/vectors/01011110-V-0000.bin"
private noncomputable def vp01011110_1 : Blocks := edgeBlocks% "full/vectors/01011110-V-0001.bin"
private noncomputable def vp01011110_2 : Blocks := edgeBlocks% "full/vectors/01011110-V-0002.bin"
private noncomputable def vp01011110_3 : Blocks := edgeBlocks% "full/vectors/01011110-V-0003.bin"
private noncomputable def vp01011110_4 : Blocks := edgeBlocks% "full/vectors/01011110-V-0004.bin"
noncomputable def vp01011110 : Blocks := (Blocks.join (Blocks.join vp01011110_0 vp01011110_1) (Blocks.join vp01011110_2 (Blocks.join vp01011110_3 vp01011110_4)))
private theorem bp010111100 : Branch 0 (-3007761639/32000000 : ℚ) vp01011110 := by
  apply branch_left_normalized (c:=vp010111100) (k:=0) (m:=303) (by decide +kernel)
  rw [show 2*(-3007761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3007761639/16000000 : ℚ) by norm_num]
  exact coverp010111100
private noncomputable def ep010111101_0 : Blocks := edgeBlocks% "full/vectors/010111101-E-0000.bin"
private noncomputable def ep010111101_1 : Blocks := edgeBlocks% "full/vectors/010111101-E-0001.bin"
private noncomputable def ep010111101_2 : Blocks := edgeBlocks% "full/vectors/010111101-E-0002.bin"
private noncomputable def ep010111101_3 : Blocks := edgeBlocks% "full/vectors/010111101-E-0003.bin"
private noncomputable def ep010111101_4 : Blocks := edgeBlocks% "full/vectors/010111101-E-0004.bin"
noncomputable def ep010111101 : Blocks := (Blocks.join (Blocks.join ep010111101_0 ep010111101_1) (Blocks.join ep010111101_2 (Blocks.join ep010111101_3 ep010111101_4)))
private theorem idp010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011110.list =
    C ((2:ℤ)^675) * horner X vp010111101.list + horner X ep010111101.list := by
  exact edge_identity (B := (2:ℤ)^985) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111101 : Branch 1 (-3007761639/32000000 : ℚ) vp01011110 := by
  apply branch_checked idp010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3007761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3023761639/16000000 : ℚ) by norm_num]
  exact coverp010111101
theorem coverp01011110 : Covers (-3007761639/32000000 : ℚ) vp01011110 := join_branches bp010111100 bp010111101
private noncomputable def vp0101111_0 : Blocks := edgeBlocks% "full/vectors/0101111-V-0000.bin"
private noncomputable def vp0101111_1 : Blocks := edgeBlocks% "full/vectors/0101111-V-0001.bin"
private noncomputable def vp0101111_2 : Blocks := edgeBlocks% "full/vectors/0101111-V-0002.bin"
private noncomputable def vp0101111_3 : Blocks := edgeBlocks% "full/vectors/0101111-V-0003.bin"
private noncomputable def vp0101111_4 : Blocks := edgeBlocks% "full/vectors/0101111-V-0004.bin"
private noncomputable def vp0101111_5 : Blocks := edgeBlocks% "full/vectors/0101111-V-0005.bin"
private noncomputable def vp0101111_6 : Blocks := edgeBlocks% "full/vectors/0101111-V-0006.bin"
private noncomputable def vp0101111_7 : Blocks := edgeBlocks% "full/vectors/0101111-V-0007.bin"
private noncomputable def vp0101111_8 : Blocks := edgeBlocks% "full/vectors/0101111-V-0008.bin"
noncomputable def vp0101111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0101111_0 vp0101111_1) (Blocks.join vp0101111_2 vp0101111_3)) (Blocks.join (Blocks.join vp0101111_4 vp0101111_5) (Blocks.join vp0101111_6 (Blocks.join vp0101111_7 vp0101111_8))))
private theorem bp01011110 : Branch 0 (-3007761639/64000000 : ℚ) vp0101111 := by
  apply branch_left_normalized (c:=vp01011110) (k:=0) (m:=587) (by decide +kernel)
  rw [show 2*(-3007761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3007761639/32000000 : ℚ) by norm_num]
  exact coverp01011110
private noncomputable def ep01011111_0 : Blocks := edgeBlocks% "full/vectors/01011111-E-0000.bin"
private noncomputable def ep01011111_1 : Blocks := edgeBlocks% "full/vectors/01011111-E-0001.bin"
private noncomputable def ep01011111_2 : Blocks := edgeBlocks% "full/vectors/01011111-E-0002.bin"
private noncomputable def ep01011111_3 : Blocks := edgeBlocks% "full/vectors/01011111-E-0003.bin"
private noncomputable def ep01011111_4 : Blocks := edgeBlocks% "full/vectors/01011111-E-0004.bin"
private noncomputable def ep01011111_5 : Blocks := edgeBlocks% "full/vectors/01011111-E-0005.bin"
private noncomputable def ep01011111_6 : Blocks := edgeBlocks% "full/vectors/01011111-E-0006.bin"
private noncomputable def ep01011111_7 : Blocks := edgeBlocks% "full/vectors/01011111-E-0007.bin"
private noncomputable def ep01011111_8 : Blocks := edgeBlocks% "full/vectors/01011111-E-0008.bin"
noncomputable def ep01011111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01011111_0 ep01011111_1) (Blocks.join ep01011111_2 ep01011111_3)) (Blocks.join (Blocks.join ep01011111_4 ep01011111_5) (Blocks.join ep01011111_6 (Blocks.join ep01011111_7 ep01011111_8))))
private theorem idp01011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101111.list =
    C ((2:ℤ)^1325) * horner X vp01011111.list + horner X ep01011111.list := by
  exact edge_identity (B := (2:ℤ)^1846) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011111 : Branch 1 (-3007761639/64000000 : ℚ) vp0101111 := by
  apply branch_checked idp01011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3007761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3039761639/32000000 : ℚ) by norm_num]
  exact coverp01011111
theorem coverp0101111 : Covers (-3007761639/64000000 : ℚ) vp0101111 := join_branches bp01011110 bp01011111
private noncomputable def vp01011101111_0 : Blocks := edgeBlocks% "full/vectors/01011101111-V-0000.bin"
noncomputable def vp01011101111 : Blocks := vp01011101111_0
theorem coverp01011101111 : Covers (-3003761639/4000000 : ℚ) vp01011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp01011101110_0 : Blocks := edgeBlocks% "full/vectors/01011101110-V-0000.bin"
noncomputable def vp01011101110 : Blocks := vp01011101110_0
theorem coverp01011101110 : Covers (-2999761639/4000000 : ℚ) vp01011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0101110111_0 : Blocks := edgeBlocks% "full/vectors/0101110111-V-0000.bin"
private noncomputable def vp0101110111_1 : Blocks := edgeBlocks% "full/vectors/0101110111-V-0001.bin"
noncomputable def vp0101110111 : Blocks := (Blocks.join vp0101110111_0 vp0101110111_1)
private theorem bp01011101110 : Branch 0 (-2999761639/8000000 : ℚ) vp0101110111 := by
  apply branch_left_normalized (c:=vp01011101110) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-2999761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2999761639/4000000 : ℚ) by norm_num]
  exact coverp01011101110
private noncomputable def ep01011101111_0 : Blocks := edgeBlocks% "full/vectors/01011101111-E-0000.bin"
private noncomputable def ep01011101111_1 : Blocks := edgeBlocks% "full/vectors/01011101111-E-0001.bin"
noncomputable def ep01011101111 : Blocks := (Blocks.join ep01011101111_0 ep01011101111_1)
private theorem idp01011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101110111.list =
    C ((2:ℤ)^184) * horner X vp01011101111.list + horner X ep01011101111.list := by
  exact edge_identity (B := (2:ℤ)^330) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011101111 : Branch 1 (-2999761639/8000000 : ℚ) vp0101110111 := by
  apply branch_checked idp01011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2999761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3003761639/4000000 : ℚ) by norm_num]
  exact coverp01011101111
theorem coverp0101110111 : Covers (-2999761639/8000000 : ℚ) vp0101110111 := join_branches bp01011101110 bp01011101111
private noncomputable def vp01011101101_0 : Blocks := edgeBlocks% "full/vectors/01011101101-V-0000.bin"
noncomputable def vp01011101101 : Blocks := vp01011101101_0
theorem coverp01011101101 : Covers (-2995761639/4000000 : ℚ) vp01011101101 := cover_leaf (by decide +kernel)
private noncomputable def vp01011101100_0 : Blocks := edgeBlocks% "full/vectors/01011101100-V-0000.bin"
noncomputable def vp01011101100 : Blocks := vp01011101100_0
theorem coverp01011101100 : Covers (-2991761639/4000000 : ℚ) vp01011101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0101110110_0 : Blocks := edgeBlocks% "full/vectors/0101110110-V-0000.bin"
private noncomputable def vp0101110110_1 : Blocks := edgeBlocks% "full/vectors/0101110110-V-0001.bin"
noncomputable def vp0101110110 : Blocks := (Blocks.join vp0101110110_0 vp0101110110_1)
private theorem bp01011101100 : Branch 0 (-2991761639/8000000 : ℚ) vp0101110110 := by
  apply branch_left_normalized (c:=vp01011101100) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-2991761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2991761639/4000000 : ℚ) by norm_num]
  exact coverp01011101100
private noncomputable def ep01011101101_0 : Blocks := edgeBlocks% "full/vectors/01011101101-E-0000.bin"
private noncomputable def ep01011101101_1 : Blocks := edgeBlocks% "full/vectors/01011101101-E-0001.bin"
noncomputable def ep01011101101 : Blocks := (Blocks.join ep01011101101_0 ep01011101101_1)
private theorem idp01011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101110110.list =
    C ((2:ℤ)^184) * horner X vp01011101101.list + horner X ep01011101101.list := by
  exact edge_identity (B := (2:ℤ)^328) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011101101 : Branch 1 (-2991761639/8000000 : ℚ) vp0101110110 := by
  apply branch_checked idp01011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2991761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2995761639/4000000 : ℚ) by norm_num]
  exact coverp01011101101
theorem coverp0101110110 : Covers (-2991761639/8000000 : ℚ) vp0101110110 := join_branches bp01011101100 bp01011101101
private noncomputable def vp010111011_0 : Blocks := edgeBlocks% "full/vectors/010111011-V-0000.bin"
private noncomputable def vp010111011_1 : Blocks := edgeBlocks% "full/vectors/010111011-V-0001.bin"
private noncomputable def vp010111011_2 : Blocks := edgeBlocks% "full/vectors/010111011-V-0002.bin"
noncomputable def vp010111011 : Blocks := (Blocks.join vp010111011_0 (Blocks.join vp010111011_1 vp010111011_2))
private theorem bp0101110110 : Branch 0 (-2991761639/16000000 : ℚ) vp010111011 := by
  apply branch_left_normalized (c:=vp0101110110) (k:=0) (m:=160) (by decide +kernel)
  rw [show 2*(-2991761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2991761639/8000000 : ℚ) by norm_num]
  exact coverp0101110110
private noncomputable def ep0101110111_0 : Blocks := edgeBlocks% "full/vectors/0101110111-E-0000.bin"
private noncomputable def ep0101110111_1 : Blocks := edgeBlocks% "full/vectors/0101110111-E-0001.bin"
private noncomputable def ep0101110111_2 : Blocks := edgeBlocks% "full/vectors/0101110111-E-0002.bin"
noncomputable def ep0101110111 : Blocks := (Blocks.join ep0101110111_0 (Blocks.join ep0101110111_1 ep0101110111_2))
private theorem idp0101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010111011.list =
    C ((2:ℤ)^349) * horner X vp0101110111.list + horner X ep0101110111.list := by
  exact edge_identity (B := (2:ℤ)^548) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101110111 : Branch 1 (-2991761639/16000000 : ℚ) vp010111011 := by
  apply branch_checked idp0101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2991761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2999761639/8000000 : ℚ) by norm_num]
  exact coverp0101110111
theorem coverp010111011 : Covers (-2991761639/16000000 : ℚ) vp010111011 := join_branches bp0101110110 bp0101110111
private noncomputable def vp01011101011_0 : Blocks := edgeBlocks% "full/vectors/01011101011-V-0000.bin"
noncomputable def vp01011101011 : Blocks := vp01011101011_0
theorem coverp01011101011 : Covers (-2987761639/4000000 : ℚ) vp01011101011 := cover_leaf (by decide +kernel)
private noncomputable def vp01011101010_0 : Blocks := edgeBlocks% "full/vectors/01011101010-V-0000.bin"
noncomputable def vp01011101010 : Blocks := vp01011101010_0
theorem coverp01011101010 : Covers (-2983761639/4000000 : ℚ) vp01011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0101110101_0 : Blocks := edgeBlocks% "full/vectors/0101110101-V-0000.bin"
private noncomputable def vp0101110101_1 : Blocks := edgeBlocks% "full/vectors/0101110101-V-0001.bin"
noncomputable def vp0101110101 : Blocks := (Blocks.join vp0101110101_0 vp0101110101_1)
private theorem bp01011101010 : Branch 0 (-2983761639/8000000 : ℚ) vp0101110101 := by
  apply branch_left_normalized (c:=vp01011101010) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-2983761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2983761639/4000000 : ℚ) by norm_num]
  exact coverp01011101010
private noncomputable def ep01011101011_0 : Blocks := edgeBlocks% "full/vectors/01011101011-E-0000.bin"
private noncomputable def ep01011101011_1 : Blocks := edgeBlocks% "full/vectors/01011101011-E-0001.bin"
noncomputable def ep01011101011 : Blocks := (Blocks.join ep01011101011_0 ep01011101011_1)
private theorem idp01011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101110101.list =
    C ((2:ℤ)^184) * horner X vp01011101011.list + horner X ep01011101011.list := by
  exact edge_identity (B := (2:ℤ)^328) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011101011 : Branch 1 (-2983761639/8000000 : ℚ) vp0101110101 := by
  apply branch_checked idp01011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2983761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2987761639/4000000 : ℚ) by norm_num]
  exact coverp01011101011
theorem coverp0101110101 : Covers (-2983761639/8000000 : ℚ) vp0101110101 := join_branches bp01011101010 bp01011101011
private noncomputable def vp01011101001_0 : Blocks := edgeBlocks% "full/vectors/01011101001-V-0000.bin"
noncomputable def vp01011101001 : Blocks := vp01011101001_0
theorem coverp01011101001 : Covers (-2979761639/4000000 : ℚ) vp01011101001 := cover_leaf (by decide +kernel)
private noncomputable def vp01011101000_0 : Blocks := edgeBlocks% "full/vectors/01011101000-V-0000.bin"
noncomputable def vp01011101000 : Blocks := vp01011101000_0
theorem coverp01011101000 : Covers (-2975761639/4000000 : ℚ) vp01011101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0101110100_0 : Blocks := edgeBlocks% "full/vectors/0101110100-V-0000.bin"
private noncomputable def vp0101110100_1 : Blocks := edgeBlocks% "full/vectors/0101110100-V-0001.bin"
noncomputable def vp0101110100 : Blocks := (Blocks.join vp0101110100_0 vp0101110100_1)
private theorem bp01011101000 : Branch 0 (-2975761639/8000000 : ℚ) vp0101110100 := by
  apply branch_left_normalized (c:=vp01011101000) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-2975761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2975761639/4000000 : ℚ) by norm_num]
  exact coverp01011101000
private noncomputable def ep01011101001_0 : Blocks := edgeBlocks% "full/vectors/01011101001-E-0000.bin"
private noncomputable def ep01011101001_1 : Blocks := edgeBlocks% "full/vectors/01011101001-E-0001.bin"
noncomputable def ep01011101001 : Blocks := (Blocks.join ep01011101001_0 ep01011101001_1)
private theorem idp01011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101110100.list =
    C ((2:ℤ)^186) * horner X vp01011101001.list + horner X ep01011101001.list := by
  exact edge_identity (B := (2:ℤ)^332) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011101001 : Branch 1 (-2975761639/8000000 : ℚ) vp0101110100 := by
  apply branch_checked idp01011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2975761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2979761639/4000000 : ℚ) by norm_num]
  exact coverp01011101001
theorem coverp0101110100 : Covers (-2975761639/8000000 : ℚ) vp0101110100 := join_branches bp01011101000 bp01011101001
private noncomputable def vp010111010_0 : Blocks := edgeBlocks% "full/vectors/010111010-V-0000.bin"
private noncomputable def vp010111010_1 : Blocks := edgeBlocks% "full/vectors/010111010-V-0001.bin"
private noncomputable def vp010111010_2 : Blocks := edgeBlocks% "full/vectors/010111010-V-0002.bin"
noncomputable def vp010111010 : Blocks := (Blocks.join vp010111010_0 (Blocks.join vp010111010_1 vp010111010_2))
private theorem bp0101110100 : Branch 0 (-2975761639/16000000 : ℚ) vp010111010 := by
  apply branch_left_normalized (c:=vp0101110100) (k:=0) (m:=161) (by decide +kernel)
  rw [show 2*(-2975761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2975761639/8000000 : ℚ) by norm_num]
  exact coverp0101110100
private noncomputable def ep0101110101_0 : Blocks := edgeBlocks% "full/vectors/0101110101-E-0000.bin"
private noncomputable def ep0101110101_1 : Blocks := edgeBlocks% "full/vectors/0101110101-E-0001.bin"
private noncomputable def ep0101110101_2 : Blocks := edgeBlocks% "full/vectors/0101110101-E-0002.bin"
noncomputable def ep0101110101 : Blocks := (Blocks.join ep0101110101_0 (Blocks.join ep0101110101_1 ep0101110101_2))
private theorem idp0101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010111010.list =
    C ((2:ℤ)^354) * horner X vp0101110101.list + horner X ep0101110101.list := by
  exact edge_identity (B := (2:ℤ)^553) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101110101 : Branch 1 (-2975761639/16000000 : ℚ) vp010111010 := by
  apply branch_checked idp0101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2975761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2983761639/8000000 : ℚ) by norm_num]
  exact coverp0101110101
theorem coverp010111010 : Covers (-2975761639/16000000 : ℚ) vp010111010 := join_branches bp0101110100 bp0101110101
private noncomputable def vp01011101_0 : Blocks := edgeBlocks% "full/vectors/01011101-V-0000.bin"
private noncomputable def vp01011101_1 : Blocks := edgeBlocks% "full/vectors/01011101-V-0001.bin"
private noncomputable def vp01011101_2 : Blocks := edgeBlocks% "full/vectors/01011101-V-0002.bin"
private noncomputable def vp01011101_3 : Blocks := edgeBlocks% "full/vectors/01011101-V-0003.bin"
private noncomputable def vp01011101_4 : Blocks := edgeBlocks% "full/vectors/01011101-V-0004.bin"
noncomputable def vp01011101 : Blocks := (Blocks.join (Blocks.join vp01011101_0 vp01011101_1) (Blocks.join vp01011101_2 (Blocks.join vp01011101_3 vp01011101_4)))
private theorem bp010111010 : Branch 0 (-2975761639/32000000 : ℚ) vp01011101 := by
  apply branch_left_normalized (c:=vp010111010) (k:=0) (m:=305) (by decide +kernel)
  rw [show 2*(-2975761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2975761639/16000000 : ℚ) by norm_num]
  exact coverp010111010
private noncomputable def ep010111011_0 : Blocks := edgeBlocks% "full/vectors/010111011-E-0000.bin"
private noncomputable def ep010111011_1 : Blocks := edgeBlocks% "full/vectors/010111011-E-0001.bin"
private noncomputable def ep010111011_2 : Blocks := edgeBlocks% "full/vectors/010111011-E-0002.bin"
private noncomputable def ep010111011_3 : Blocks := edgeBlocks% "full/vectors/010111011-E-0003.bin"
private noncomputable def ep010111011_4 : Blocks := edgeBlocks% "full/vectors/010111011-E-0004.bin"
noncomputable def ep010111011 : Blocks := (Blocks.join (Blocks.join ep010111011_0 ep010111011_1) (Blocks.join ep010111011_2 (Blocks.join ep010111011_3 ep010111011_4)))
private theorem idp010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011101.list =
    C ((2:ℤ)^686) * horner X vp010111011.list + horner X ep010111011.list := by
  exact edge_identity (B := (2:ℤ)^990) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111011 : Branch 1 (-2975761639/32000000 : ℚ) vp01011101 := by
  apply branch_checked idp010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2975761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2991761639/16000000 : ℚ) by norm_num]
  exact coverp010111011
theorem coverp01011101 : Covers (-2975761639/32000000 : ℚ) vp01011101 := join_branches bp010111010 bp010111011
private noncomputable def vp01011100111_0 : Blocks := edgeBlocks% "full/vectors/01011100111-V-0000.bin"
noncomputable def vp01011100111 : Blocks := vp01011100111_0
theorem coverp01011100111 : Covers (-2971761639/4000000 : ℚ) vp01011100111 := cover_leaf (by decide +kernel)
private noncomputable def vp01011100110_0 : Blocks := edgeBlocks% "full/vectors/01011100110-V-0000.bin"
noncomputable def vp01011100110 : Blocks := vp01011100110_0
theorem coverp01011100110 : Covers (-2967761639/4000000 : ℚ) vp01011100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0101110011_0 : Blocks := edgeBlocks% "full/vectors/0101110011-V-0000.bin"
private noncomputable def vp0101110011_1 : Blocks := edgeBlocks% "full/vectors/0101110011-V-0001.bin"
noncomputable def vp0101110011 : Blocks := (Blocks.join vp0101110011_0 vp0101110011_1)
private theorem bp01011100110 : Branch 0 (-2967761639/8000000 : ℚ) vp0101110011 := by
  apply branch_left_normalized (c:=vp01011100110) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-2967761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2967761639/4000000 : ℚ) by norm_num]
  exact coverp01011100110
private noncomputable def ep01011100111_0 : Blocks := edgeBlocks% "full/vectors/01011100111-E-0000.bin"
private noncomputable def ep01011100111_1 : Blocks := edgeBlocks% "full/vectors/01011100111-E-0001.bin"
noncomputable def ep01011100111 : Blocks := (Blocks.join ep01011100111_0 ep01011100111_1)
private theorem idp01011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101110011.list =
    C ((2:ℤ)^191) * horner X vp01011100111.list + horner X ep01011100111.list := by
  exact edge_identity (B := (2:ℤ)^339) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011100111 : Branch 1 (-2967761639/8000000 : ℚ) vp0101110011 := by
  apply branch_checked idp01011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2967761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2971761639/4000000 : ℚ) by norm_num]
  exact coverp01011100111
theorem coverp0101110011 : Covers (-2967761639/8000000 : ℚ) vp0101110011 := join_branches bp01011100110 bp01011100111
private noncomputable def vp01011100101_0 : Blocks := edgeBlocks% "full/vectors/01011100101-V-0000.bin"
noncomputable def vp01011100101 : Blocks := vp01011100101_0
theorem coverp01011100101 : Covers (-2963761639/4000000 : ℚ) vp01011100101 := cover_leaf (by decide +kernel)
private noncomputable def vp010111001001_0 : Blocks := edgeBlocks% "full/vectors/010111001001-V-0000.bin"
noncomputable def vp010111001001 : Blocks := vp010111001001_0
theorem coverp010111001001 : Covers (-2961761639/2000000 : ℚ) vp010111001001 := cover_leaf (by decide +kernel)
private noncomputable def vp010111001000_0 : Blocks := edgeBlocks% "full/vectors/010111001000-V-0000.bin"
noncomputable def vp010111001000 : Blocks := vp010111001000_0
theorem coverp010111001000 : Covers (-2959761639/2000000 : ℚ) vp010111001000 := cover_leaf (by decide +kernel)
private noncomputable def vp01011100100_0 : Blocks := edgeBlocks% "full/vectors/01011100100-V-0000.bin"
noncomputable def vp01011100100 : Blocks := vp01011100100_0
private theorem bp010111001000 : Branch 0 (-2959761639/4000000 : ℚ) vp01011100100 := by
  apply branch_left_normalized (c:=vp010111001000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-2959761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2959761639/2000000 : ℚ) by norm_num]
  exact coverp010111001000
private noncomputable def ep010111001001_0 : Blocks := edgeBlocks% "full/vectors/010111001001-E-0000.bin"
noncomputable def ep010111001001 : Blocks := ep010111001001_0
private theorem idp010111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011100100.list =
    C ((2:ℤ)^104) * horner X vp010111001001.list + horner X ep010111001001.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111001001 : Branch 1 (-2959761639/4000000 : ℚ) vp01011100100 := by
  apply branch_checked idp010111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2959761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2961761639/2000000 : ℚ) by norm_num]
  exact coverp010111001001
theorem coverp01011100100 : Covers (-2959761639/4000000 : ℚ) vp01011100100 := join_branches bp010111001000 bp010111001001
private noncomputable def vp0101110010_0 : Blocks := edgeBlocks% "full/vectors/0101110010-V-0000.bin"
private noncomputable def vp0101110010_1 : Blocks := edgeBlocks% "full/vectors/0101110010-V-0001.bin"
noncomputable def vp0101110010 : Blocks := (Blocks.join vp0101110010_0 vp0101110010_1)
private theorem bp01011100100 : Branch 0 (-2959761639/8000000 : ℚ) vp0101110010 := by
  apply branch_left_normalized (c:=vp01011100100) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-2959761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2959761639/4000000 : ℚ) by norm_num]
  exact coverp01011100100
private noncomputable def ep01011100101_0 : Blocks := edgeBlocks% "full/vectors/01011100101-E-0000.bin"
private noncomputable def ep01011100101_1 : Blocks := edgeBlocks% "full/vectors/01011100101-E-0001.bin"
noncomputable def ep01011100101 : Blocks := (Blocks.join ep01011100101_0 ep01011100101_1)
private theorem idp01011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101110010.list =
    C ((2:ℤ)^188) * horner X vp01011100101.list + horner X ep01011100101.list := by
  exact edge_identity (B := (2:ℤ)^343) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011100101 : Branch 1 (-2959761639/8000000 : ℚ) vp0101110010 := by
  apply branch_checked idp01011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2959761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2963761639/4000000 : ℚ) by norm_num]
  exact coverp01011100101
theorem coverp0101110010 : Covers (-2959761639/8000000 : ℚ) vp0101110010 := join_branches bp01011100100 bp01011100101
private noncomputable def vp010111001_0 : Blocks := edgeBlocks% "full/vectors/010111001-V-0000.bin"
private noncomputable def vp010111001_1 : Blocks := edgeBlocks% "full/vectors/010111001-V-0001.bin"
private noncomputable def vp010111001_2 : Blocks := edgeBlocks% "full/vectors/010111001-V-0002.bin"
noncomputable def vp010111001 : Blocks := (Blocks.join vp010111001_0 (Blocks.join vp010111001_1 vp010111001_2))
private theorem bp0101110010 : Branch 0 (-2959761639/16000000 : ℚ) vp010111001 := by
  apply branch_left_normalized (c:=vp0101110010) (k:=0) (m:=166) (by decide +kernel)
  rw [show 2*(-2959761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2959761639/8000000 : ℚ) by norm_num]
  exact coverp0101110010
private noncomputable def ep0101110011_0 : Blocks := edgeBlocks% "full/vectors/0101110011-E-0000.bin"
private noncomputable def ep0101110011_1 : Blocks := edgeBlocks% "full/vectors/0101110011-E-0001.bin"
private noncomputable def ep0101110011_2 : Blocks := edgeBlocks% "full/vectors/0101110011-E-0002.bin"
noncomputable def ep0101110011 : Blocks := (Blocks.join ep0101110011_0 (Blocks.join ep0101110011_1 ep0101110011_2))
private theorem idp0101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010111001.list =
    C ((2:ℤ)^358) * horner X vp0101110011.list + horner X ep0101110011.list := by
  exact edge_identity (B := (2:ℤ)^563) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101110011 : Branch 1 (-2959761639/16000000 : ℚ) vp010111001 := by
  apply branch_checked idp0101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2959761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2967761639/8000000 : ℚ) by norm_num]
  exact coverp0101110011
theorem coverp010111001 : Covers (-2959761639/16000000 : ℚ) vp010111001 := join_branches bp0101110010 bp0101110011
private noncomputable def vp010111000111_0 : Blocks := edgeBlocks% "full/vectors/010111000111-V-0000.bin"
noncomputable def vp010111000111 : Blocks := vp010111000111_0
theorem coverp010111000111 : Covers (-2957761639/2000000 : ℚ) vp010111000111 := cover_leaf (by decide +kernel)
private noncomputable def vp010111000110_0 : Blocks := edgeBlocks% "full/vectors/010111000110-V-0000.bin"
noncomputable def vp010111000110 : Blocks := vp010111000110_0
theorem coverp010111000110 : Covers (-2955761639/2000000 : ℚ) vp010111000110 := cover_leaf (by decide +kernel)
private noncomputable def vp01011100011_0 : Blocks := edgeBlocks% "full/vectors/01011100011-V-0000.bin"
noncomputable def vp01011100011 : Blocks := vp01011100011_0
private theorem bp010111000110 : Branch 0 (-2955761639/4000000 : ℚ) vp01011100011 := by
  apply branch_left_normalized (c:=vp010111000110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-2955761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2955761639/2000000 : ℚ) by norm_num]
  exact coverp010111000110
private noncomputable def ep010111000111_0 : Blocks := edgeBlocks% "full/vectors/010111000111-E-0000.bin"
noncomputable def ep010111000111 : Blocks := ep010111000111_0
private theorem idp010111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011100011.list =
    C ((2:ℤ)^105) * horner X vp010111000111.list + horner X ep010111000111.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111000111 : Branch 1 (-2955761639/4000000 : ℚ) vp01011100011 := by
  apply branch_checked idp010111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2955761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2957761639/2000000 : ℚ) by norm_num]
  exact coverp010111000111
theorem coverp01011100011 : Covers (-2955761639/4000000 : ℚ) vp01011100011 := join_branches bp010111000110 bp010111000111
private noncomputable def vp010111000101_0 : Blocks := edgeBlocks% "full/vectors/010111000101-V-0000.bin"
noncomputable def vp010111000101 : Blocks := vp010111000101_0
theorem coverp010111000101 : Covers (-2953761639/2000000 : ℚ) vp010111000101 := cover_leaf (by decide +kernel)
private noncomputable def vp010111000100_0 : Blocks := edgeBlocks% "full/vectors/010111000100-V-0000.bin"
noncomputable def vp010111000100 : Blocks := vp010111000100_0
theorem coverp010111000100 : Covers (-2951761639/2000000 : ℚ) vp010111000100 := cover_leaf (by decide +kernel)
private noncomputable def vp01011100010_0 : Blocks := edgeBlocks% "full/vectors/01011100010-V-0000.bin"
noncomputable def vp01011100010 : Blocks := vp01011100010_0
private theorem bp010111000100 : Branch 0 (-2951761639/4000000 : ℚ) vp01011100010 := by
  apply branch_left_normalized (c:=vp010111000100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-2951761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2951761639/2000000 : ℚ) by norm_num]
  exact coverp010111000100
private noncomputable def ep010111000101_0 : Blocks := edgeBlocks% "full/vectors/010111000101-E-0000.bin"
noncomputable def ep010111000101 : Blocks := ep010111000101_0
private theorem idp010111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011100010.list =
    C ((2:ℤ)^106) * horner X vp010111000101.list + horner X ep010111000101.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111000101 : Branch 1 (-2951761639/4000000 : ℚ) vp01011100010 := by
  apply branch_checked idp010111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2951761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2953761639/2000000 : ℚ) by norm_num]
  exact coverp010111000101
theorem coverp01011100010 : Covers (-2951761639/4000000 : ℚ) vp01011100010 := join_branches bp010111000100 bp010111000101
private noncomputable def vp0101110001_0 : Blocks := edgeBlocks% "full/vectors/0101110001-V-0000.bin"
private noncomputable def vp0101110001_1 : Blocks := edgeBlocks% "full/vectors/0101110001-V-0001.bin"
noncomputable def vp0101110001 : Blocks := (Blocks.join vp0101110001_0 vp0101110001_1)
private theorem bp01011100010 : Branch 0 (-2951761639/8000000 : ℚ) vp0101110001 := by
  apply branch_left_normalized (c:=vp01011100010) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-2951761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2951761639/4000000 : ℚ) by norm_num]
  exact coverp01011100010
private noncomputable def ep01011100011_0 : Blocks := edgeBlocks% "full/vectors/01011100011-E-0000.bin"
private noncomputable def ep01011100011_1 : Blocks := edgeBlocks% "full/vectors/01011100011-E-0001.bin"
noncomputable def ep01011100011 : Blocks := (Blocks.join ep01011100011_0 ep01011100011_1)
private theorem idp01011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101110001.list =
    C ((2:ℤ)^190) * horner X vp01011100011.list + horner X ep01011100011.list := by
  exact edge_identity (B := (2:ℤ)^343) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011100011 : Branch 1 (-2951761639/8000000 : ℚ) vp0101110001 := by
  apply branch_checked idp01011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2951761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2955761639/4000000 : ℚ) by norm_num]
  exact coverp01011100011
theorem coverp0101110001 : Covers (-2951761639/8000000 : ℚ) vp0101110001 := join_branches bp01011100010 bp01011100011
private noncomputable def vp010111000011_0 : Blocks := edgeBlocks% "full/vectors/010111000011-V-0000.bin"
noncomputable def vp010111000011 : Blocks := vp010111000011_0
theorem coverp010111000011 : Covers (-2949761639/2000000 : ℚ) vp010111000011 := cover_leaf (by decide +kernel)
private noncomputable def vp010111000010_0 : Blocks := edgeBlocks% "full/vectors/010111000010-V-0000.bin"
noncomputable def vp010111000010 : Blocks := vp010111000010_0
theorem coverp010111000010 : Covers (-2947761639/2000000 : ℚ) vp010111000010 := cover_leaf (by decide +kernel)
private noncomputable def vp01011100001_0 : Blocks := edgeBlocks% "full/vectors/01011100001-V-0000.bin"
noncomputable def vp01011100001 : Blocks := vp01011100001_0
private theorem bp010111000010 : Branch 0 (-2947761639/4000000 : ℚ) vp01011100001 := by
  apply branch_left_normalized (c:=vp010111000010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-2947761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2947761639/2000000 : ℚ) by norm_num]
  exact coverp010111000010
private noncomputable def ep010111000011_0 : Blocks := edgeBlocks% "full/vectors/010111000011-E-0000.bin"
noncomputable def ep010111000011 : Blocks := ep010111000011_0
private theorem idp010111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011100001.list =
    C ((2:ℤ)^106) * horner X vp010111000011.list + horner X ep010111000011.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111000011 : Branch 1 (-2947761639/4000000 : ℚ) vp01011100001 := by
  apply branch_checked idp010111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-2947761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2949761639/2000000 : ℚ) by norm_num]
  exact coverp010111000011
theorem coverp01011100001 : Covers (-2947761639/4000000 : ℚ) vp01011100001 := join_branches bp010111000010 bp010111000011
private noncomputable def vp010111000001_0 : Blocks := edgeBlocks% "full/vectors/010111000001-V-0000.bin"
noncomputable def vp010111000001 : Blocks := vp010111000001_0
theorem coverp010111000001 : Covers (-2945761639/2000000 : ℚ) vp010111000001 := cover_leaf (by decide +kernel)
private noncomputable def vp010111000000_0 : Blocks := edgeBlocks% "full/vectors/010111000000-V-0000.bin"
noncomputable def vp010111000000 : Blocks := vp010111000000_0
theorem coverp010111000000 : Covers (-2943761639/2000000 : ℚ) vp010111000000 := cover_leaf (by decide +kernel)
private noncomputable def vp01011100000_0 : Blocks := edgeBlocks% "full/vectors/01011100000-V-0000.bin"
noncomputable def vp01011100000 : Blocks := vp01011100000_0
private theorem bp010111000000 : Branch 0 (-2943761639/4000000 : ℚ) vp01011100000 := by
  apply branch_left_normalized (c:=vp010111000000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-2943761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2943761639/2000000 : ℚ) by norm_num]
  exact coverp010111000000
private noncomputable def ep010111000001_0 : Blocks := edgeBlocks% "full/vectors/010111000001-E-0000.bin"
noncomputable def ep010111000001 : Blocks := ep010111000001_0
private theorem idp010111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011100000.list =
    C ((2:ℤ)^106) * horner X vp010111000001.list + horner X ep010111000001.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111000001 : Branch 1 (-2943761639/4000000 : ℚ) vp01011100000 := by
  apply branch_checked idp010111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2943761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2945761639/2000000 : ℚ) by norm_num]
  exact coverp010111000001
theorem coverp01011100000 : Covers (-2943761639/4000000 : ℚ) vp01011100000 := join_branches bp010111000000 bp010111000001
private noncomputable def vp0101110000_0 : Blocks := edgeBlocks% "full/vectors/0101110000-V-0000.bin"
private noncomputable def vp0101110000_1 : Blocks := edgeBlocks% "full/vectors/0101110000-V-0001.bin"
noncomputable def vp0101110000 : Blocks := (Blocks.join vp0101110000_0 vp0101110000_1)
private theorem bp01011100000 : Branch 0 (-2943761639/8000000 : ℚ) vp0101110000 := by
  apply branch_left_normalized (c:=vp01011100000) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-2943761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2943761639/4000000 : ℚ) by norm_num]
  exact coverp01011100000
private noncomputable def ep01011100001_0 : Blocks := edgeBlocks% "full/vectors/01011100001-E-0000.bin"
private noncomputable def ep01011100001_1 : Blocks := edgeBlocks% "full/vectors/01011100001-E-0001.bin"
noncomputable def ep01011100001 : Blocks := (Blocks.join ep01011100001_0 ep01011100001_1)
private theorem idp01011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101110000.list =
    C ((2:ℤ)^190) * horner X vp01011100001.list + horner X ep01011100001.list := by
  exact edge_identity (B := (2:ℤ)^345) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011100001 : Branch 1 (-2943761639/8000000 : ℚ) vp0101110000 := by
  apply branch_checked idp01011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2943761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2947761639/4000000 : ℚ) by norm_num]
  exact coverp01011100001
theorem coverp0101110000 : Covers (-2943761639/8000000 : ℚ) vp0101110000 := join_branches bp01011100000 bp01011100001
private noncomputable def vp010111000_0 : Blocks := edgeBlocks% "full/vectors/010111000-V-0000.bin"
private noncomputable def vp010111000_1 : Blocks := edgeBlocks% "full/vectors/010111000-V-0001.bin"
private noncomputable def vp010111000_2 : Blocks := edgeBlocks% "full/vectors/010111000-V-0002.bin"
noncomputable def vp010111000 : Blocks := (Blocks.join vp010111000_0 (Blocks.join vp010111000_1 vp010111000_2))
private theorem bp0101110000 : Branch 0 (-2943761639/16000000 : ℚ) vp010111000 := by
  apply branch_left_normalized (c:=vp0101110000) (k:=0) (m:=166) (by decide +kernel)
  rw [show 2*(-2943761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2943761639/8000000 : ℚ) by norm_num]
  exact coverp0101110000
private noncomputable def ep0101110001_0 : Blocks := edgeBlocks% "full/vectors/0101110001-E-0000.bin"
private noncomputable def ep0101110001_1 : Blocks := edgeBlocks% "full/vectors/0101110001-E-0001.bin"
private noncomputable def ep0101110001_2 : Blocks := edgeBlocks% "full/vectors/0101110001-E-0002.bin"
noncomputable def ep0101110001 : Blocks := (Blocks.join ep0101110001_0 (Blocks.join ep0101110001_1 ep0101110001_2))
private theorem idp0101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010111000.list =
    C ((2:ℤ)^359) * horner X vp0101110001.list + horner X ep0101110001.list := by
  exact edge_identity (B := (2:ℤ)^567) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101110001 : Branch 1 (-2943761639/16000000 : ℚ) vp010111000 := by
  apply branch_checked idp0101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2943761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2951761639/8000000 : ℚ) by norm_num]
  exact coverp0101110001
theorem coverp010111000 : Covers (-2943761639/16000000 : ℚ) vp010111000 := join_branches bp0101110000 bp0101110001
private noncomputable def vp01011100_0 : Blocks := edgeBlocks% "full/vectors/01011100-V-0000.bin"
private noncomputable def vp01011100_1 : Blocks := edgeBlocks% "full/vectors/01011100-V-0001.bin"
private noncomputable def vp01011100_2 : Blocks := edgeBlocks% "full/vectors/01011100-V-0002.bin"
private noncomputable def vp01011100_3 : Blocks := edgeBlocks% "full/vectors/01011100-V-0003.bin"
private noncomputable def vp01011100_4 : Blocks := edgeBlocks% "full/vectors/01011100-V-0004.bin"
noncomputable def vp01011100 : Blocks := (Blocks.join (Blocks.join vp01011100_0 vp01011100_1) (Blocks.join vp01011100_2 (Blocks.join vp01011100_3 vp01011100_4)))
private theorem bp010111000 : Branch 0 (-2943761639/32000000 : ℚ) vp01011100 := by
  apply branch_left_normalized (c:=vp010111000) (k:=0) (m:=311) (by decide +kernel)
  rw [show 2*(-2943761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2943761639/16000000 : ℚ) by norm_num]
  exact coverp010111000
private noncomputable def ep010111001_0 : Blocks := edgeBlocks% "full/vectors/010111001-E-0000.bin"
private noncomputable def ep010111001_1 : Blocks := edgeBlocks% "full/vectors/010111001-E-0001.bin"
private noncomputable def ep010111001_2 : Blocks := edgeBlocks% "full/vectors/010111001-E-0002.bin"
private noncomputable def ep010111001_3 : Blocks := edgeBlocks% "full/vectors/010111001-E-0003.bin"
private noncomputable def ep010111001_4 : Blocks := edgeBlocks% "full/vectors/010111001-E-0004.bin"
noncomputable def ep010111001 : Blocks := (Blocks.join (Blocks.join ep010111001_0 ep010111001_1) (Blocks.join ep010111001_2 (Blocks.join ep010111001_3 ep010111001_4)))
private theorem idp010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01011100.list =
    C ((2:ℤ)^693) * horner X vp010111001.list + horner X ep010111001.list := by
  exact edge_identity (B := (2:ℤ)^1007) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010111001 : Branch 1 (-2943761639/32000000 : ℚ) vp01011100 := by
  apply branch_checked idp010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2943761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2959761639/16000000 : ℚ) by norm_num]
  exact coverp010111001
theorem coverp01011100 : Covers (-2943761639/32000000 : ℚ) vp01011100 := join_branches bp010111000 bp010111001
private noncomputable def vp0101110_0 : Blocks := edgeBlocks% "full/vectors/0101110-V-0000.bin"
private noncomputable def vp0101110_1 : Blocks := edgeBlocks% "full/vectors/0101110-V-0001.bin"
private noncomputable def vp0101110_2 : Blocks := edgeBlocks% "full/vectors/0101110-V-0002.bin"
private noncomputable def vp0101110_3 : Blocks := edgeBlocks% "full/vectors/0101110-V-0003.bin"
private noncomputable def vp0101110_4 : Blocks := edgeBlocks% "full/vectors/0101110-V-0004.bin"
private noncomputable def vp0101110_5 : Blocks := edgeBlocks% "full/vectors/0101110-V-0005.bin"
private noncomputable def vp0101110_6 : Blocks := edgeBlocks% "full/vectors/0101110-V-0006.bin"
private noncomputable def vp0101110_7 : Blocks := edgeBlocks% "full/vectors/0101110-V-0007.bin"
private noncomputable def vp0101110_8 : Blocks := edgeBlocks% "full/vectors/0101110-V-0008.bin"
private noncomputable def vp0101110_9 : Blocks := edgeBlocks% "full/vectors/0101110-V-0009.bin"
noncomputable def vp0101110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0101110_0 vp0101110_1) (Blocks.join vp0101110_2 (Blocks.join vp0101110_3 vp0101110_4))) (Blocks.join (Blocks.join vp0101110_5 vp0101110_6) (Blocks.join vp0101110_7 (Blocks.join vp0101110_8 vp0101110_9))))
private theorem bp01011100 : Branch 0 (-2943761639/64000000 : ℚ) vp0101110 := by
  apply branch_left_normalized (c:=vp01011100) (k:=0) (m:=598) (by decide +kernel)
  rw [show 2*(-2943761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2943761639/32000000 : ℚ) by norm_num]
  exact coverp01011100
private noncomputable def ep01011101_0 : Blocks := edgeBlocks% "full/vectors/01011101-E-0000.bin"
private noncomputable def ep01011101_1 : Blocks := edgeBlocks% "full/vectors/01011101-E-0001.bin"
private noncomputable def ep01011101_2 : Blocks := edgeBlocks% "full/vectors/01011101-E-0002.bin"
private noncomputable def ep01011101_3 : Blocks := edgeBlocks% "full/vectors/01011101-E-0003.bin"
private noncomputable def ep01011101_4 : Blocks := edgeBlocks% "full/vectors/01011101-E-0004.bin"
private noncomputable def ep01011101_5 : Blocks := edgeBlocks% "full/vectors/01011101-E-0005.bin"
private noncomputable def ep01011101_6 : Blocks := edgeBlocks% "full/vectors/01011101-E-0006.bin"
private noncomputable def ep01011101_7 : Blocks := edgeBlocks% "full/vectors/01011101-E-0007.bin"
private noncomputable def ep01011101_8 : Blocks := edgeBlocks% "full/vectors/01011101-E-0008.bin"
private noncomputable def ep01011101_9 : Blocks := edgeBlocks% "full/vectors/01011101-E-0009.bin"
noncomputable def ep01011101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01011101_0 ep01011101_1) (Blocks.join ep01011101_2 (Blocks.join ep01011101_3 ep01011101_4))) (Blocks.join (Blocks.join ep01011101_5 ep01011101_6) (Blocks.join ep01011101_7 (Blocks.join ep01011101_8 ep01011101_9))))
private theorem idp01011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0101110.list =
    C ((2:ℤ)^1355) * horner X vp01011101.list + horner X ep01011101.list := by
  exact edge_identity (B := (2:ℤ)^1876) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01011101 : Branch 1 (-2943761639/64000000 : ℚ) vp0101110 := by
  apply branch_checked idp01011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2943761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2975761639/32000000 : ℚ) by norm_num]
  exact coverp01011101
theorem coverp0101110 : Covers (-2943761639/64000000 : ℚ) vp0101110 := join_branches bp01011100 bp01011101
private noncomputable def vp010111_0 : Blocks := edgeBlocks% "full/vectors/010111-V-0000.bin"
private noncomputable def vp010111_1 : Blocks := edgeBlocks% "full/vectors/010111-V-0001.bin"
private noncomputable def vp010111_2 : Blocks := edgeBlocks% "full/vectors/010111-V-0002.bin"
private noncomputable def vp010111_3 : Blocks := edgeBlocks% "full/vectors/010111-V-0003.bin"
private noncomputable def vp010111_4 : Blocks := edgeBlocks% "full/vectors/010111-V-0004.bin"
private noncomputable def vp010111_5 : Blocks := edgeBlocks% "full/vectors/010111-V-0005.bin"
private noncomputable def vp010111_6 : Blocks := edgeBlocks% "full/vectors/010111-V-0006.bin"
private noncomputable def vp010111_7 : Blocks := edgeBlocks% "full/vectors/010111-V-0007.bin"
private noncomputable def vp010111_8 : Blocks := edgeBlocks% "full/vectors/010111-V-0008.bin"
private noncomputable def vp010111_9 : Blocks := edgeBlocks% "full/vectors/010111-V-0009.bin"
private noncomputable def vp010111_10 : Blocks := edgeBlocks% "full/vectors/010111-V-0010.bin"
private noncomputable def vp010111_11 : Blocks := edgeBlocks% "full/vectors/010111-V-0011.bin"
private noncomputable def vp010111_12 : Blocks := edgeBlocks% "full/vectors/010111-V-0012.bin"
private noncomputable def vp010111_13 : Blocks := edgeBlocks% "full/vectors/010111-V-0013.bin"
private noncomputable def vp010111_14 : Blocks := edgeBlocks% "full/vectors/010111-V-0014.bin"
private noncomputable def vp010111_15 : Blocks := edgeBlocks% "full/vectors/010111-V-0015.bin"
private noncomputable def vp010111_16 : Blocks := edgeBlocks% "full/vectors/010111-V-0016.bin"
private noncomputable def vp010111_17 : Blocks := edgeBlocks% "full/vectors/010111-V-0017.bin"
noncomputable def vp010111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp010111_0 vp010111_1) (Blocks.join vp010111_2 vp010111_3)) (Blocks.join (Blocks.join vp010111_4 vp010111_5) (Blocks.join vp010111_6 (Blocks.join vp010111_7 vp010111_8)))) (Blocks.join (Blocks.join (Blocks.join vp010111_9 vp010111_10) (Blocks.join vp010111_11 vp010111_12)) (Blocks.join (Blocks.join vp010111_13 vp010111_14) (Blocks.join vp010111_15 (Blocks.join vp010111_16 vp010111_17)))))
private theorem bp0101110 : Branch 0 (-2943761639/128000000 : ℚ) vp010111 := by
  apply branch_left_normalized (c:=vp0101110) (k:=0) (m:=1162) (by decide +kernel)
  rw [show 2*(-2943761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-2943761639/64000000 : ℚ) by norm_num]
  exact coverp0101110
private noncomputable def ep0101111_0 : Blocks := edgeBlocks% "full/vectors/0101111-E-0000.bin"
private noncomputable def ep0101111_1 : Blocks := edgeBlocks% "full/vectors/0101111-E-0001.bin"
private noncomputable def ep0101111_2 : Blocks := edgeBlocks% "full/vectors/0101111-E-0002.bin"
private noncomputable def ep0101111_3 : Blocks := edgeBlocks% "full/vectors/0101111-E-0003.bin"
private noncomputable def ep0101111_4 : Blocks := edgeBlocks% "full/vectors/0101111-E-0004.bin"
private noncomputable def ep0101111_5 : Blocks := edgeBlocks% "full/vectors/0101111-E-0005.bin"
private noncomputable def ep0101111_6 : Blocks := edgeBlocks% "full/vectors/0101111-E-0006.bin"
private noncomputable def ep0101111_7 : Blocks := edgeBlocks% "full/vectors/0101111-E-0007.bin"
private noncomputable def ep0101111_8 : Blocks := edgeBlocks% "full/vectors/0101111-E-0008.bin"
private noncomputable def ep0101111_9 : Blocks := edgeBlocks% "full/vectors/0101111-E-0009.bin"
private noncomputable def ep0101111_10 : Blocks := edgeBlocks% "full/vectors/0101111-E-0010.bin"
private noncomputable def ep0101111_11 : Blocks := edgeBlocks% "full/vectors/0101111-E-0011.bin"
private noncomputable def ep0101111_12 : Blocks := edgeBlocks% "full/vectors/0101111-E-0012.bin"
private noncomputable def ep0101111_13 : Blocks := edgeBlocks% "full/vectors/0101111-E-0013.bin"
private noncomputable def ep0101111_14 : Blocks := edgeBlocks% "full/vectors/0101111-E-0014.bin"
private noncomputable def ep0101111_15 : Blocks := edgeBlocks% "full/vectors/0101111-E-0015.bin"
private noncomputable def ep0101111_16 : Blocks := edgeBlocks% "full/vectors/0101111-E-0016.bin"
private noncomputable def ep0101111_17 : Blocks := edgeBlocks% "full/vectors/0101111-E-0017.bin"
noncomputable def ep0101111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0101111_0 ep0101111_1) (Blocks.join ep0101111_2 ep0101111_3)) (Blocks.join (Blocks.join ep0101111_4 ep0101111_5) (Blocks.join ep0101111_6 (Blocks.join ep0101111_7 ep0101111_8)))) (Blocks.join (Blocks.join (Blocks.join ep0101111_9 ep0101111_10) (Blocks.join ep0101111_11 ep0101111_12)) (Blocks.join (Blocks.join ep0101111_13 ep0101111_14) (Blocks.join ep0101111_15 (Blocks.join ep0101111_16 ep0101111_17)))))
private theorem idp0101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010111.list =
    C ((2:ℤ)^2639) * horner X vp0101111.list + horner X ep0101111.list := by
  exact edge_identity (B := (2:ℤ)^3579) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0101111 : Branch 1 (-2943761639/128000000 : ℚ) vp010111 := by
  apply branch_checked idp0101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2943761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-3007761639/64000000 : ℚ) by norm_num]
  exact coverp0101111
theorem coverp010111 : Covers (-2943761639/128000000 : ℚ) vp010111 := join_branches bp0101110 bp0101111
end NextProof.EdgeFull

