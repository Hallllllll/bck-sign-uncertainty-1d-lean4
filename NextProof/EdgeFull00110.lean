import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp010001111111_0 : Blocks := edgeBlocks% "full/vectors/010001111111-V-0000.bin"
noncomputable def vp010001111111 : Blocks := vp010001111111_0
theorem coverp010001111111 : Covers (-2301761639/2000000 : ℚ) vp010001111111 := cover_leaf (by decide +kernel)
private noncomputable def vp010001111110_0 : Blocks := edgeBlocks% "full/vectors/010001111110-V-0000.bin"
noncomputable def vp010001111110 : Blocks := vp010001111110_0
theorem coverp010001111110 : Covers (-2299761639/2000000 : ℚ) vp010001111110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000111111_0 : Blocks := edgeBlocks% "full/vectors/01000111111-V-0000.bin"
noncomputable def vp01000111111 : Blocks := vp01000111111_0
private theorem bp010001111110 : Branch 0 (-2299761639/4000000 : ℚ) vp01000111111 := by
  apply branch_left_normalized (c:=vp010001111110) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2299761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2299761639/2000000 : ℚ) by norm_num]
  exact coverp010001111110
private noncomputable def ep010001111111_0 : Blocks := edgeBlocks% "full/vectors/010001111111-E-0000.bin"
noncomputable def ep010001111111 : Blocks := ep010001111111_0
private theorem idp010001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000111111.list =
    C ((2:ℤ)^114) * horner X vp010001111111.list + horner X ep010001111111.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001111111 : Branch 1 (-2299761639/4000000 : ℚ) vp01000111111 := by
  apply branch_checked idp010001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2299761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2301761639/2000000 : ℚ) by norm_num]
  exact coverp010001111111
theorem coverp01000111111 : Covers (-2299761639/4000000 : ℚ) vp01000111111 := join_branches bp010001111110 bp010001111111
private noncomputable def vp010001111101_0 : Blocks := edgeBlocks% "full/vectors/010001111101-V-0000.bin"
noncomputable def vp010001111101 : Blocks := vp010001111101_0
theorem coverp010001111101 : Covers (-2297761639/2000000 : ℚ) vp010001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp010001111100_0 : Blocks := edgeBlocks% "full/vectors/010001111100-V-0000.bin"
noncomputable def vp010001111100 : Blocks := vp010001111100_0
theorem coverp010001111100 : Covers (-2295761639/2000000 : ℚ) vp010001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000111110_0 : Blocks := edgeBlocks% "full/vectors/01000111110-V-0000.bin"
noncomputable def vp01000111110 : Blocks := vp01000111110_0
private theorem bp010001111100 : Branch 0 (-2295761639/4000000 : ℚ) vp01000111110 := by
  apply branch_left_normalized (c:=vp010001111100) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2295761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2295761639/2000000 : ℚ) by norm_num]
  exact coverp010001111100
private noncomputable def ep010001111101_0 : Blocks := edgeBlocks% "full/vectors/010001111101-E-0000.bin"
noncomputable def ep010001111101 : Blocks := ep010001111101_0
private theorem idp010001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000111110.list =
    C ((2:ℤ)^115) * horner X vp010001111101.list + horner X ep010001111101.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001111101 : Branch 1 (-2295761639/4000000 : ℚ) vp01000111110 := by
  apply branch_checked idp010001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2295761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2297761639/2000000 : ℚ) by norm_num]
  exact coverp010001111101
theorem coverp01000111110 : Covers (-2295761639/4000000 : ℚ) vp01000111110 := join_branches bp010001111100 bp010001111101
private noncomputable def vp0100011111_0 : Blocks := edgeBlocks% "full/vectors/0100011111-V-0000.bin"
private noncomputable def vp0100011111_1 : Blocks := edgeBlocks% "full/vectors/0100011111-V-0001.bin"
noncomputable def vp0100011111 : Blocks := (Blocks.join vp0100011111_0 vp0100011111_1)
private theorem bp01000111110 : Branch 0 (-2295761639/8000000 : ℚ) vp0100011111 := by
  apply branch_left_normalized (c:=vp01000111110) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-2295761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2295761639/4000000 : ℚ) by norm_num]
  exact coverp01000111110
private noncomputable def ep01000111111_0 : Blocks := edgeBlocks% "full/vectors/01000111111-E-0000.bin"
private noncomputable def ep01000111111_1 : Blocks := edgeBlocks% "full/vectors/01000111111-E-0001.bin"
noncomputable def ep01000111111 : Blocks := (Blocks.join ep01000111111_0 ep01000111111_1)
private theorem idp01000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100011111.list =
    C ((2:ℤ)^209) * horner X vp01000111111.list + horner X ep01000111111.list := by
  exact edge_identity (B := (2:ℤ)^371) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000111111 : Branch 1 (-2295761639/8000000 : ℚ) vp0100011111 := by
  apply branch_checked idp01000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2295761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2299761639/4000000 : ℚ) by norm_num]
  exact coverp01000111111
theorem coverp0100011111 : Covers (-2295761639/8000000 : ℚ) vp0100011111 := join_branches bp01000111110 bp01000111111
private noncomputable def vp010001111011_0 : Blocks := edgeBlocks% "full/vectors/010001111011-V-0000.bin"
noncomputable def vp010001111011 : Blocks := vp010001111011_0
theorem coverp010001111011 : Covers (-2293761639/2000000 : ℚ) vp010001111011 := cover_leaf (by decide +kernel)
private noncomputable def vp010001111010_0 : Blocks := edgeBlocks% "full/vectors/010001111010-V-0000.bin"
noncomputable def vp010001111010 : Blocks := vp010001111010_0
theorem coverp010001111010 : Covers (-2291761639/2000000 : ℚ) vp010001111010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000111101_0 : Blocks := edgeBlocks% "full/vectors/01000111101-V-0000.bin"
noncomputable def vp01000111101 : Blocks := vp01000111101_0
private theorem bp010001111010 : Branch 0 (-2291761639/4000000 : ℚ) vp01000111101 := by
  apply branch_left_normalized (c:=vp010001111010) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2291761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2291761639/2000000 : ℚ) by norm_num]
  exact coverp010001111010
private noncomputable def ep010001111011_0 : Blocks := edgeBlocks% "full/vectors/010001111011-E-0000.bin"
noncomputable def ep010001111011 : Blocks := ep010001111011_0
private theorem idp010001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000111101.list =
    C ((2:ℤ)^117) * horner X vp010001111011.list + horner X ep010001111011.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001111011 : Branch 1 (-2291761639/4000000 : ℚ) vp01000111101 := by
  apply branch_checked idp010001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2291761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2293761639/2000000 : ℚ) by norm_num]
  exact coverp010001111011
theorem coverp01000111101 : Covers (-2291761639/4000000 : ℚ) vp01000111101 := join_branches bp010001111010 bp010001111011
private noncomputable def vp010001111001_0 : Blocks := edgeBlocks% "full/vectors/010001111001-V-0000.bin"
noncomputable def vp010001111001 : Blocks := vp010001111001_0
theorem coverp010001111001 : Covers (-2289761639/2000000 : ℚ) vp010001111001 := cover_leaf (by decide +kernel)
private noncomputable def vp010001111000_0 : Blocks := edgeBlocks% "full/vectors/010001111000-V-0000.bin"
noncomputable def vp010001111000 : Blocks := vp010001111000_0
theorem coverp010001111000 : Covers (-2287761639/2000000 : ℚ) vp010001111000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000111100_0 : Blocks := edgeBlocks% "full/vectors/01000111100-V-0000.bin"
noncomputable def vp01000111100 : Blocks := vp01000111100_0
private theorem bp010001111000 : Branch 0 (-2287761639/4000000 : ℚ) vp01000111100 := by
  apply branch_left_normalized (c:=vp010001111000) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2287761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2287761639/2000000 : ℚ) by norm_num]
  exact coverp010001111000
private noncomputable def ep010001111001_0 : Blocks := edgeBlocks% "full/vectors/010001111001-E-0000.bin"
noncomputable def ep010001111001 : Blocks := ep010001111001_0
private theorem idp010001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000111100.list =
    C ((2:ℤ)^114) * horner X vp010001111001.list + horner X ep010001111001.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001111001 : Branch 1 (-2287761639/4000000 : ℚ) vp01000111100 := by
  apply branch_checked idp010001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2287761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2289761639/2000000 : ℚ) by norm_num]
  exact coverp010001111001
theorem coverp01000111100 : Covers (-2287761639/4000000 : ℚ) vp01000111100 := join_branches bp010001111000 bp010001111001
private noncomputable def vp0100011110_0 : Blocks := edgeBlocks% "full/vectors/0100011110-V-0000.bin"
private noncomputable def vp0100011110_1 : Blocks := edgeBlocks% "full/vectors/0100011110-V-0001.bin"
noncomputable def vp0100011110 : Blocks := (Blocks.join vp0100011110_0 vp0100011110_1)
private theorem bp01000111100 : Branch 0 (-2287761639/8000000 : ℚ) vp0100011110 := by
  apply branch_left_normalized (c:=vp01000111100) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-2287761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2287761639/4000000 : ℚ) by norm_num]
  exact coverp01000111100
private noncomputable def ep01000111101_0 : Blocks := edgeBlocks% "full/vectors/01000111101-E-0000.bin"
private noncomputable def ep01000111101_1 : Blocks := edgeBlocks% "full/vectors/01000111101-E-0001.bin"
noncomputable def ep01000111101 : Blocks := (Blocks.join ep01000111101_0 ep01000111101_1)
private theorem idp01000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100011110.list =
    C ((2:ℤ)^207) * horner X vp01000111101.list + horner X ep01000111101.list := by
  exact edge_identity (B := (2:ℤ)^373) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000111101 : Branch 1 (-2287761639/8000000 : ℚ) vp0100011110 := by
  apply branch_checked idp01000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2287761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2291761639/4000000 : ℚ) by norm_num]
  exact coverp01000111101
theorem coverp0100011110 : Covers (-2287761639/8000000 : ℚ) vp0100011110 := join_branches bp01000111100 bp01000111101
private noncomputable def vp010001111_0 : Blocks := edgeBlocks% "full/vectors/010001111-V-0000.bin"
private noncomputable def vp010001111_1 : Blocks := edgeBlocks% "full/vectors/010001111-V-0001.bin"
private noncomputable def vp010001111_2 : Blocks := edgeBlocks% "full/vectors/010001111-V-0002.bin"
noncomputable def vp010001111 : Blocks := (Blocks.join vp010001111_0 (Blocks.join vp010001111_1 vp010001111_2))
private theorem bp0100011110 : Branch 0 (-2287761639/16000000 : ℚ) vp010001111 := by
  apply branch_left_normalized (c:=vp0100011110) (k:=0) (m:=185) (by decide +kernel)
  rw [show 2*(-2287761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2287761639/8000000 : ℚ) by norm_num]
  exact coverp0100011110
private noncomputable def ep0100011111_0 : Blocks := edgeBlocks% "full/vectors/0100011111-E-0000.bin"
private noncomputable def ep0100011111_1 : Blocks := edgeBlocks% "full/vectors/0100011111-E-0001.bin"
private noncomputable def ep0100011111_2 : Blocks := edgeBlocks% "full/vectors/0100011111-E-0002.bin"
noncomputable def ep0100011111 : Blocks := (Blocks.join ep0100011111_0 (Blocks.join ep0100011111_1 ep0100011111_2))
private theorem idp0100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010001111.list =
    C ((2:ℤ)^397) * horner X vp0100011111.list + horner X ep0100011111.list := by
  exact edge_identity (B := (2:ℤ)^624) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100011111 : Branch 1 (-2287761639/16000000 : ℚ) vp010001111 := by
  apply branch_checked idp0100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2287761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2295761639/8000000 : ℚ) by norm_num]
  exact coverp0100011111
theorem coverp010001111 : Covers (-2287761639/16000000 : ℚ) vp010001111 := join_branches bp0100011110 bp0100011111
private noncomputable def vp010001110111_0 : Blocks := edgeBlocks% "full/vectors/010001110111-V-0000.bin"
noncomputable def vp010001110111 : Blocks := vp010001110111_0
theorem coverp010001110111 : Covers (-2285761639/2000000 : ℚ) vp010001110111 := cover_leaf (by decide +kernel)
private noncomputable def vp010001110110_0 : Blocks := edgeBlocks% "full/vectors/010001110110-V-0000.bin"
noncomputable def vp010001110110 : Blocks := vp010001110110_0
theorem coverp010001110110 : Covers (-2283761639/2000000 : ℚ) vp010001110110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000111011_0 : Blocks := edgeBlocks% "full/vectors/01000111011-V-0000.bin"
noncomputable def vp01000111011 : Blocks := vp01000111011_0
private theorem bp010001110110 : Branch 0 (-2283761639/4000000 : ℚ) vp01000111011 := by
  apply branch_left_normalized (c:=vp010001110110) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2283761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2283761639/2000000 : ℚ) by norm_num]
  exact coverp010001110110
private noncomputable def ep010001110111_0 : Blocks := edgeBlocks% "full/vectors/010001110111-E-0000.bin"
noncomputable def ep010001110111 : Blocks := ep010001110111_0
private theorem idp010001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000111011.list =
    C ((2:ℤ)^115) * horner X vp010001110111.list + horner X ep010001110111.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001110111 : Branch 1 (-2283761639/4000000 : ℚ) vp01000111011 := by
  apply branch_checked idp010001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2283761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2285761639/2000000 : ℚ) by norm_num]
  exact coverp010001110111
theorem coverp01000111011 : Covers (-2283761639/4000000 : ℚ) vp01000111011 := join_branches bp010001110110 bp010001110111
private noncomputable def vp010001110101_0 : Blocks := edgeBlocks% "full/vectors/010001110101-V-0000.bin"
noncomputable def vp010001110101 : Blocks := vp010001110101_0
theorem coverp010001110101 : Covers (-2281761639/2000000 : ℚ) vp010001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp010001110100_0 : Blocks := edgeBlocks% "full/vectors/010001110100-V-0000.bin"
noncomputable def vp010001110100 : Blocks := vp010001110100_0
theorem coverp010001110100 : Covers (-2279761639/2000000 : ℚ) vp010001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000111010_0 : Blocks := edgeBlocks% "full/vectors/01000111010-V-0000.bin"
noncomputable def vp01000111010 : Blocks := vp01000111010_0
private theorem bp010001110100 : Branch 0 (-2279761639/4000000 : ℚ) vp01000111010 := by
  apply branch_left_normalized (c:=vp010001110100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2279761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2279761639/2000000 : ℚ) by norm_num]
  exact coverp010001110100
private noncomputable def ep010001110101_0 : Blocks := edgeBlocks% "full/vectors/010001110101-E-0000.bin"
noncomputable def ep010001110101 : Blocks := ep010001110101_0
private theorem idp010001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000111010.list =
    C ((2:ℤ)^116) * horner X vp010001110101.list + horner X ep010001110101.list := by
  exact edge_identity (B := (2:ℤ)^248) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001110101 : Branch 1 (-2279761639/4000000 : ℚ) vp01000111010 := by
  apply branch_checked idp010001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2279761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2281761639/2000000 : ℚ) by norm_num]
  exact coverp010001110101
theorem coverp01000111010 : Covers (-2279761639/4000000 : ℚ) vp01000111010 := join_branches bp010001110100 bp010001110101
private noncomputable def vp0100011101_0 : Blocks := edgeBlocks% "full/vectors/0100011101-V-0000.bin"
private noncomputable def vp0100011101_1 : Blocks := edgeBlocks% "full/vectors/0100011101-V-0001.bin"
noncomputable def vp0100011101 : Blocks := (Blocks.join vp0100011101_0 vp0100011101_1)
private theorem bp01000111010 : Branch 0 (-2279761639/8000000 : ℚ) vp0100011101 := by
  apply branch_left_normalized (c:=vp01000111010) (k:=0) (m:=103) (by decide +kernel)
  rw [show 2*(-2279761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2279761639/4000000 : ℚ) by norm_num]
  exact coverp01000111010
private noncomputable def ep01000111011_0 : Blocks := edgeBlocks% "full/vectors/01000111011-E-0000.bin"
private noncomputable def ep01000111011_1 : Blocks := edgeBlocks% "full/vectors/01000111011-E-0001.bin"
noncomputable def ep01000111011 : Blocks := (Blocks.join ep01000111011_0 ep01000111011_1)
private theorem idp01000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100011101.list =
    C ((2:ℤ)^211) * horner X vp01000111011.list + horner X ep01000111011.list := by
  exact edge_identity (B := (2:ℤ)^375) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000111011 : Branch 1 (-2279761639/8000000 : ℚ) vp0100011101 := by
  apply branch_checked idp01000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2279761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2283761639/4000000 : ℚ) by norm_num]
  exact coverp01000111011
theorem coverp0100011101 : Covers (-2279761639/8000000 : ℚ) vp0100011101 := join_branches bp01000111010 bp01000111011
private noncomputable def vp010001110011_0 : Blocks := edgeBlocks% "full/vectors/010001110011-V-0000.bin"
noncomputable def vp010001110011 : Blocks := vp010001110011_0
theorem coverp010001110011 : Covers (-2277761639/2000000 : ℚ) vp010001110011 := cover_leaf (by decide +kernel)
private noncomputable def vp010001110010_0 : Blocks := edgeBlocks% "full/vectors/010001110010-V-0000.bin"
noncomputable def vp010001110010 : Blocks := vp010001110010_0
theorem coverp010001110010 : Covers (-2275761639/2000000 : ℚ) vp010001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000111001_0 : Blocks := edgeBlocks% "full/vectors/01000111001-V-0000.bin"
noncomputable def vp01000111001 : Blocks := vp01000111001_0
private theorem bp010001110010 : Branch 0 (-2275761639/4000000 : ℚ) vp01000111001 := by
  apply branch_left_normalized (c:=vp010001110010) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2275761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2275761639/2000000 : ℚ) by norm_num]
  exact coverp010001110010
private noncomputable def ep010001110011_0 : Blocks := edgeBlocks% "full/vectors/010001110011-E-0000.bin"
noncomputable def ep010001110011 : Blocks := ep010001110011_0
private theorem idp010001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000111001.list =
    C ((2:ℤ)^116) * horner X vp010001110011.list + horner X ep010001110011.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001110011 : Branch 1 (-2275761639/4000000 : ℚ) vp01000111001 := by
  apply branch_checked idp010001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2275761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2277761639/2000000 : ℚ) by norm_num]
  exact coverp010001110011
theorem coverp01000111001 : Covers (-2275761639/4000000 : ℚ) vp01000111001 := join_branches bp010001110010 bp010001110011
private noncomputable def vp010001110001_0 : Blocks := edgeBlocks% "full/vectors/010001110001-V-0000.bin"
noncomputable def vp010001110001 : Blocks := vp010001110001_0
theorem coverp010001110001 : Covers (-2273761639/2000000 : ℚ) vp010001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp010001110000_0 : Blocks := edgeBlocks% "full/vectors/010001110000-V-0000.bin"
noncomputable def vp010001110000 : Blocks := vp010001110000_0
theorem coverp010001110000 : Covers (-2271761639/2000000 : ℚ) vp010001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000111000_0 : Blocks := edgeBlocks% "full/vectors/01000111000-V-0000.bin"
noncomputable def vp01000111000 : Blocks := vp01000111000_0
private theorem bp010001110000 : Branch 0 (-2271761639/4000000 : ℚ) vp01000111000 := by
  apply branch_left_normalized (c:=vp010001110000) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2271761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2271761639/2000000 : ℚ) by norm_num]
  exact coverp010001110000
private noncomputable def ep010001110001_0 : Blocks := edgeBlocks% "full/vectors/010001110001-E-0000.bin"
noncomputable def ep010001110001 : Blocks := ep010001110001_0
private theorem idp010001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000111000.list =
    C ((2:ℤ)^115) * horner X vp010001110001.list + horner X ep010001110001.list := by
  exact edge_identity (B := (2:ℤ)^248) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001110001 : Branch 1 (-2271761639/4000000 : ℚ) vp01000111000 := by
  apply branch_checked idp010001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2271761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2273761639/2000000 : ℚ) by norm_num]
  exact coverp010001110001
theorem coverp01000111000 : Covers (-2271761639/4000000 : ℚ) vp01000111000 := join_branches bp010001110000 bp010001110001
private noncomputable def vp0100011100_0 : Blocks := edgeBlocks% "full/vectors/0100011100-V-0000.bin"
private noncomputable def vp0100011100_1 : Blocks := edgeBlocks% "full/vectors/0100011100-V-0001.bin"
noncomputable def vp0100011100 : Blocks := (Blocks.join vp0100011100_0 vp0100011100_1)
private theorem bp01000111000 : Branch 0 (-2271761639/8000000 : ℚ) vp0100011100 := by
  apply branch_left_normalized (c:=vp01000111000) (k:=0) (m:=103) (by decide +kernel)
  rw [show 2*(-2271761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2271761639/4000000 : ℚ) by norm_num]
  exact coverp01000111000
private noncomputable def ep01000111001_0 : Blocks := edgeBlocks% "full/vectors/01000111001-E-0000.bin"
private noncomputable def ep01000111001_1 : Blocks := edgeBlocks% "full/vectors/01000111001-E-0001.bin"
noncomputable def ep01000111001 : Blocks := (Blocks.join ep01000111001_0 ep01000111001_1)
private theorem idp01000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100011100.list =
    C ((2:ℤ)^209) * horner X vp01000111001.list + horner X ep01000111001.list := by
  exact edge_identity (B := (2:ℤ)^375) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000111001 : Branch 1 (-2271761639/8000000 : ℚ) vp0100011100 := by
  apply branch_checked idp01000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2271761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2275761639/4000000 : ℚ) by norm_num]
  exact coverp01000111001
theorem coverp0100011100 : Covers (-2271761639/8000000 : ℚ) vp0100011100 := join_branches bp01000111000 bp01000111001
private noncomputable def vp010001110_0 : Blocks := edgeBlocks% "full/vectors/010001110-V-0000.bin"
private noncomputable def vp010001110_1 : Blocks := edgeBlocks% "full/vectors/010001110-V-0001.bin"
private noncomputable def vp010001110_2 : Blocks := edgeBlocks% "full/vectors/010001110-V-0002.bin"
noncomputable def vp010001110 : Blocks := (Blocks.join vp010001110_0 (Blocks.join vp010001110_1 vp010001110_2))
private theorem bp0100011100 : Branch 0 (-2271761639/16000000 : ℚ) vp010001110 := by
  apply branch_left_normalized (c:=vp0100011100) (k:=0) (m:=186) (by decide +kernel)
  rw [show 2*(-2271761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2271761639/8000000 : ℚ) by norm_num]
  exact coverp0100011100
private noncomputable def ep0100011101_0 : Blocks := edgeBlocks% "full/vectors/0100011101-E-0000.bin"
private noncomputable def ep0100011101_1 : Blocks := edgeBlocks% "full/vectors/0100011101-E-0001.bin"
private noncomputable def ep0100011101_2 : Blocks := edgeBlocks% "full/vectors/0100011101-E-0002.bin"
noncomputable def ep0100011101 : Blocks := (Blocks.join ep0100011101_0 (Blocks.join ep0100011101_1 ep0100011101_2))
private theorem idp0100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010001110.list =
    C ((2:ℤ)^397) * horner X vp0100011101.list + horner X ep0100011101.list := by
  exact edge_identity (B := (2:ℤ)^626) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100011101 : Branch 1 (-2271761639/16000000 : ℚ) vp010001110 := by
  apply branch_checked idp0100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2271761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2279761639/8000000 : ℚ) by norm_num]
  exact coverp0100011101
theorem coverp010001110 : Covers (-2271761639/16000000 : ℚ) vp010001110 := join_branches bp0100011100 bp0100011101
private noncomputable def vp01000111_0 : Blocks := edgeBlocks% "full/vectors/01000111-V-0000.bin"
private noncomputable def vp01000111_1 : Blocks := edgeBlocks% "full/vectors/01000111-V-0001.bin"
private noncomputable def vp01000111_2 : Blocks := edgeBlocks% "full/vectors/01000111-V-0002.bin"
private noncomputable def vp01000111_3 : Blocks := edgeBlocks% "full/vectors/01000111-V-0003.bin"
private noncomputable def vp01000111_4 : Blocks := edgeBlocks% "full/vectors/01000111-V-0004.bin"
private noncomputable def vp01000111_5 : Blocks := edgeBlocks% "full/vectors/01000111-V-0005.bin"
noncomputable def vp01000111 : Blocks := (Blocks.join (Blocks.join vp01000111_0 (Blocks.join vp01000111_1 vp01000111_2)) (Blocks.join vp01000111_3 (Blocks.join vp01000111_4 vp01000111_5)))
private theorem bp010001110 : Branch 0 (-2271761639/32000000 : ℚ) vp01000111 := by
  apply branch_left_normalized (c:=vp010001110) (k:=0) (m:=350) (by decide +kernel)
  rw [show 2*(-2271761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2271761639/16000000 : ℚ) by norm_num]
  exact coverp010001110
private noncomputable def ep010001111_0 : Blocks := edgeBlocks% "full/vectors/010001111-E-0000.bin"
private noncomputable def ep010001111_1 : Blocks := edgeBlocks% "full/vectors/010001111-E-0001.bin"
private noncomputable def ep010001111_2 : Blocks := edgeBlocks% "full/vectors/010001111-E-0002.bin"
private noncomputable def ep010001111_3 : Blocks := edgeBlocks% "full/vectors/010001111-E-0003.bin"
private noncomputable def ep010001111_4 : Blocks := edgeBlocks% "full/vectors/010001111-E-0004.bin"
private noncomputable def ep010001111_5 : Blocks := edgeBlocks% "full/vectors/010001111-E-0005.bin"
noncomputable def ep010001111 : Blocks := (Blocks.join (Blocks.join ep010001111_0 (Blocks.join ep010001111_1 ep010001111_2)) (Blocks.join ep010001111_3 (Blocks.join ep010001111_4 ep010001111_5)))
private theorem idp010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000111.list =
    C ((2:ℤ)^770) * horner X vp010001111.list + horner X ep010001111.list := by
  exact edge_identity (B := (2:ℤ)^1127) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001111 : Branch 1 (-2271761639/32000000 : ℚ) vp01000111 := by
  apply branch_checked idp010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2271761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2287761639/16000000 : ℚ) by norm_num]
  exact coverp010001111
theorem coverp01000111 : Covers (-2271761639/32000000 : ℚ) vp01000111 := join_branches bp010001110 bp010001111
private noncomputable def vp010001101111_0 : Blocks := edgeBlocks% "full/vectors/010001101111-V-0000.bin"
noncomputable def vp010001101111 : Blocks := vp010001101111_0
theorem coverp010001101111 : Covers (-2269761639/2000000 : ℚ) vp010001101111 := cover_leaf (by decide +kernel)
private noncomputable def vp010001101110_0 : Blocks := edgeBlocks% "full/vectors/010001101110-V-0000.bin"
noncomputable def vp010001101110 : Blocks := vp010001101110_0
theorem coverp010001101110 : Covers (-2267761639/2000000 : ℚ) vp010001101110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000110111_0 : Blocks := edgeBlocks% "full/vectors/01000110111-V-0000.bin"
noncomputable def vp01000110111 : Blocks := vp01000110111_0
private theorem bp010001101110 : Branch 0 (-2267761639/4000000 : ℚ) vp01000110111 := by
  apply branch_left_normalized (c:=vp010001101110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2267761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2267761639/2000000 : ℚ) by norm_num]
  exact coverp010001101110
private noncomputable def ep010001101111_0 : Blocks := edgeBlocks% "full/vectors/010001101111-E-0000.bin"
noncomputable def ep010001101111 : Blocks := ep010001101111_0
private theorem idp010001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000110111.list =
    C ((2:ℤ)^117) * horner X vp010001101111.list + horner X ep010001101111.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001101111 : Branch 1 (-2267761639/4000000 : ℚ) vp01000110111 := by
  apply branch_checked idp010001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2267761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2269761639/2000000 : ℚ) by norm_num]
  exact coverp010001101111
theorem coverp01000110111 : Covers (-2267761639/4000000 : ℚ) vp01000110111 := join_branches bp010001101110 bp010001101111
private noncomputable def vp010001101101_0 : Blocks := edgeBlocks% "full/vectors/010001101101-V-0000.bin"
noncomputable def vp010001101101 : Blocks := vp010001101101_0
theorem coverp010001101101 : Covers (-2265761639/2000000 : ℚ) vp010001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp010001101100_0 : Blocks := edgeBlocks% "full/vectors/010001101100-V-0000.bin"
noncomputable def vp010001101100 : Blocks := vp010001101100_0
theorem coverp010001101100 : Covers (-2263761639/2000000 : ℚ) vp010001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000110110_0 : Blocks := edgeBlocks% "full/vectors/01000110110-V-0000.bin"
noncomputable def vp01000110110 : Blocks := vp01000110110_0
private theorem bp010001101100 : Branch 0 (-2263761639/4000000 : ℚ) vp01000110110 := by
  apply branch_left_normalized (c:=vp010001101100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2263761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2263761639/2000000 : ℚ) by norm_num]
  exact coverp010001101100
private noncomputable def ep010001101101_0 : Blocks := edgeBlocks% "full/vectors/010001101101-E-0000.bin"
noncomputable def ep010001101101 : Blocks := ep010001101101_0
private theorem idp010001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000110110.list =
    C ((2:ℤ)^116) * horner X vp010001101101.list + horner X ep010001101101.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001101101 : Branch 1 (-2263761639/4000000 : ℚ) vp01000110110 := by
  apply branch_checked idp010001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2263761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2265761639/2000000 : ℚ) by norm_num]
  exact coverp010001101101
theorem coverp01000110110 : Covers (-2263761639/4000000 : ℚ) vp01000110110 := join_branches bp010001101100 bp010001101101
private noncomputable def vp0100011011_0 : Blocks := edgeBlocks% "full/vectors/0100011011-V-0000.bin"
private noncomputable def vp0100011011_1 : Blocks := edgeBlocks% "full/vectors/0100011011-V-0001.bin"
noncomputable def vp0100011011 : Blocks := (Blocks.join vp0100011011_0 vp0100011011_1)
private theorem bp01000110110 : Branch 0 (-2263761639/8000000 : ℚ) vp0100011011 := by
  apply branch_left_normalized (c:=vp01000110110) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-2263761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2263761639/4000000 : ℚ) by norm_num]
  exact coverp01000110110
private noncomputable def ep01000110111_0 : Blocks := edgeBlocks% "full/vectors/01000110111-E-0000.bin"
private noncomputable def ep01000110111_1 : Blocks := edgeBlocks% "full/vectors/01000110111-E-0001.bin"
noncomputable def ep01000110111 : Blocks := (Blocks.join ep01000110111_0 ep01000110111_1)
private theorem idp01000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100011011.list =
    C ((2:ℤ)^211) * horner X vp01000110111.list + horner X ep01000110111.list := by
  exact edge_identity (B := (2:ℤ)^377) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000110111 : Branch 1 (-2263761639/8000000 : ℚ) vp0100011011 := by
  apply branch_checked idp01000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2263761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2267761639/4000000 : ℚ) by norm_num]
  exact coverp01000110111
theorem coverp0100011011 : Covers (-2263761639/8000000 : ℚ) vp0100011011 := join_branches bp01000110110 bp01000110111
private noncomputable def vp010001101011_0 : Blocks := edgeBlocks% "full/vectors/010001101011-V-0000.bin"
noncomputable def vp010001101011 : Blocks := vp010001101011_0
theorem coverp010001101011 : Covers (-2261761639/2000000 : ℚ) vp010001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp010001101010_0 : Blocks := edgeBlocks% "full/vectors/010001101010-V-0000.bin"
noncomputable def vp010001101010 : Blocks := vp010001101010_0
theorem coverp010001101010 : Covers (-2259761639/2000000 : ℚ) vp010001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000110101_0 : Blocks := edgeBlocks% "full/vectors/01000110101-V-0000.bin"
noncomputable def vp01000110101 : Blocks := vp01000110101_0
private theorem bp010001101010 : Branch 0 (-2259761639/4000000 : ℚ) vp01000110101 := by
  apply branch_left_normalized (c:=vp010001101010) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2259761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2259761639/2000000 : ℚ) by norm_num]
  exact coverp010001101010
private noncomputable def ep010001101011_0 : Blocks := edgeBlocks% "full/vectors/010001101011-E-0000.bin"
noncomputable def ep010001101011 : Blocks := ep010001101011_0
private theorem idp010001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000110101.list =
    C ((2:ℤ)^116) * horner X vp010001101011.list + horner X ep010001101011.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001101011 : Branch 1 (-2259761639/4000000 : ℚ) vp01000110101 := by
  apply branch_checked idp010001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2259761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2261761639/2000000 : ℚ) by norm_num]
  exact coverp010001101011
theorem coverp01000110101 : Covers (-2259761639/4000000 : ℚ) vp01000110101 := join_branches bp010001101010 bp010001101011
private noncomputable def vp010001101001_0 : Blocks := edgeBlocks% "full/vectors/010001101001-V-0000.bin"
noncomputable def vp010001101001 : Blocks := vp010001101001_0
theorem coverp010001101001 : Covers (-2257761639/2000000 : ℚ) vp010001101001 := cover_leaf (by decide +kernel)
private noncomputable def vp010001101000_0 : Blocks := edgeBlocks% "full/vectors/010001101000-V-0000.bin"
noncomputable def vp010001101000 : Blocks := vp010001101000_0
theorem coverp010001101000 : Covers (-2255761639/2000000 : ℚ) vp010001101000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000110100_0 : Blocks := edgeBlocks% "full/vectors/01000110100-V-0000.bin"
noncomputable def vp01000110100 : Blocks := vp01000110100_0
private theorem bp010001101000 : Branch 0 (-2255761639/4000000 : ℚ) vp01000110100 := by
  apply branch_left_normalized (c:=vp010001101000) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2255761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2255761639/2000000 : ℚ) by norm_num]
  exact coverp010001101000
private noncomputable def ep010001101001_0 : Blocks := edgeBlocks% "full/vectors/010001101001-E-0000.bin"
noncomputable def ep010001101001 : Blocks := ep010001101001_0
private theorem idp010001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000110100.list =
    C ((2:ℤ)^117) * horner X vp010001101001.list + horner X ep010001101001.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001101001 : Branch 1 (-2255761639/4000000 : ℚ) vp01000110100 := by
  apply branch_checked idp010001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2255761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2257761639/2000000 : ℚ) by norm_num]
  exact coverp010001101001
theorem coverp01000110100 : Covers (-2255761639/4000000 : ℚ) vp01000110100 := join_branches bp010001101000 bp010001101001
private noncomputable def vp0100011010_0 : Blocks := edgeBlocks% "full/vectors/0100011010-V-0000.bin"
private noncomputable def vp0100011010_1 : Blocks := edgeBlocks% "full/vectors/0100011010-V-0001.bin"
noncomputable def vp0100011010 : Blocks := (Blocks.join vp0100011010_0 vp0100011010_1)
private theorem bp01000110100 : Branch 0 (-2255761639/8000000 : ℚ) vp0100011010 := by
  apply branch_left_normalized (c:=vp01000110100) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-2255761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2255761639/4000000 : ℚ) by norm_num]
  exact coverp01000110100
private noncomputable def ep01000110101_0 : Blocks := edgeBlocks% "full/vectors/01000110101-E-0000.bin"
private noncomputable def ep01000110101_1 : Blocks := edgeBlocks% "full/vectors/01000110101-E-0001.bin"
noncomputable def ep01000110101 : Blocks := (Blocks.join ep01000110101_0 ep01000110101_1)
private theorem idp01000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100011010.list =
    C ((2:ℤ)^211) * horner X vp01000110101.list + horner X ep01000110101.list := by
  exact edge_identity (B := (2:ℤ)^377) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000110101 : Branch 1 (-2255761639/8000000 : ℚ) vp0100011010 := by
  apply branch_checked idp01000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2255761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2259761639/4000000 : ℚ) by norm_num]
  exact coverp01000110101
theorem coverp0100011010 : Covers (-2255761639/8000000 : ℚ) vp0100011010 := join_branches bp01000110100 bp01000110101
private noncomputable def vp010001101_0 : Blocks := edgeBlocks% "full/vectors/010001101-V-0000.bin"
private noncomputable def vp010001101_1 : Blocks := edgeBlocks% "full/vectors/010001101-V-0001.bin"
private noncomputable def vp010001101_2 : Blocks := edgeBlocks% "full/vectors/010001101-V-0002.bin"
noncomputable def vp010001101 : Blocks := (Blocks.join vp010001101_0 (Blocks.join vp010001101_1 vp010001101_2))
private theorem bp0100011010 : Branch 0 (-2255761639/16000000 : ℚ) vp010001101 := by
  apply branch_left_normalized (c:=vp0100011010) (k:=0) (m:=187) (by decide +kernel)
  rw [show 2*(-2255761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2255761639/8000000 : ℚ) by norm_num]
  exact coverp0100011010
private noncomputable def ep0100011011_0 : Blocks := edgeBlocks% "full/vectors/0100011011-E-0000.bin"
private noncomputable def ep0100011011_1 : Blocks := edgeBlocks% "full/vectors/0100011011-E-0001.bin"
private noncomputable def ep0100011011_2 : Blocks := edgeBlocks% "full/vectors/0100011011-E-0002.bin"
noncomputable def ep0100011011 : Blocks := (Blocks.join ep0100011011_0 (Blocks.join ep0100011011_1 ep0100011011_2))
private theorem idp0100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010001101.list =
    C ((2:ℤ)^399) * horner X vp0100011011.list + horner X ep0100011011.list := by
  exact edge_identity (B := (2:ℤ)^630) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100011011 : Branch 1 (-2255761639/16000000 : ℚ) vp010001101 := by
  apply branch_checked idp0100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2255761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2263761639/8000000 : ℚ) by norm_num]
  exact coverp0100011011
theorem coverp010001101 : Covers (-2255761639/16000000 : ℚ) vp010001101 := join_branches bp0100011010 bp0100011011
private noncomputable def vp010001100111_0 : Blocks := edgeBlocks% "full/vectors/010001100111-V-0000.bin"
noncomputable def vp010001100111 : Blocks := vp010001100111_0
theorem coverp010001100111 : Covers (-2253761639/2000000 : ℚ) vp010001100111 := cover_leaf (by decide +kernel)
private noncomputable def vp010001100110_0 : Blocks := edgeBlocks% "full/vectors/010001100110-V-0000.bin"
noncomputable def vp010001100110 : Blocks := vp010001100110_0
theorem coverp010001100110 : Covers (-2251761639/2000000 : ℚ) vp010001100110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000110011_0 : Blocks := edgeBlocks% "full/vectors/01000110011-V-0000.bin"
noncomputable def vp01000110011 : Blocks := vp01000110011_0
private theorem bp010001100110 : Branch 0 (-2251761639/4000000 : ℚ) vp01000110011 := by
  apply branch_left_normalized (c:=vp010001100110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2251761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2251761639/2000000 : ℚ) by norm_num]
  exact coverp010001100110
private noncomputable def ep010001100111_0 : Blocks := edgeBlocks% "full/vectors/010001100111-E-0000.bin"
noncomputable def ep010001100111 : Blocks := ep010001100111_0
private theorem idp010001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000110011.list =
    C ((2:ℤ)^116) * horner X vp010001100111.list + horner X ep010001100111.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001100111 : Branch 1 (-2251761639/4000000 : ℚ) vp01000110011 := by
  apply branch_checked idp010001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2251761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2253761639/2000000 : ℚ) by norm_num]
  exact coverp010001100111
theorem coverp01000110011 : Covers (-2251761639/4000000 : ℚ) vp01000110011 := join_branches bp010001100110 bp010001100111
private noncomputable def vp010001100101_0 : Blocks := edgeBlocks% "full/vectors/010001100101-V-0000.bin"
noncomputable def vp010001100101 : Blocks := vp010001100101_0
theorem coverp010001100101 : Covers (-2249761639/2000000 : ℚ) vp010001100101 := cover_leaf (by decide +kernel)
private noncomputable def vp010001100100_0 : Blocks := edgeBlocks% "full/vectors/010001100100-V-0000.bin"
noncomputable def vp010001100100 : Blocks := vp010001100100_0
theorem coverp010001100100 : Covers (-2247761639/2000000 : ℚ) vp010001100100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000110010_0 : Blocks := edgeBlocks% "full/vectors/01000110010-V-0000.bin"
noncomputable def vp01000110010 : Blocks := vp01000110010_0
private theorem bp010001100100 : Branch 0 (-2247761639/4000000 : ℚ) vp01000110010 := by
  apply branch_left_normalized (c:=vp010001100100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2247761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2247761639/2000000 : ℚ) by norm_num]
  exact coverp010001100100
private noncomputable def ep010001100101_0 : Blocks := edgeBlocks% "full/vectors/010001100101-E-0000.bin"
noncomputable def ep010001100101 : Blocks := ep010001100101_0
private theorem idp010001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000110010.list =
    C ((2:ℤ)^116) * horner X vp010001100101.list + horner X ep010001100101.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001100101 : Branch 1 (-2247761639/4000000 : ℚ) vp01000110010 := by
  apply branch_checked idp010001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2247761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2249761639/2000000 : ℚ) by norm_num]
  exact coverp010001100101
theorem coverp01000110010 : Covers (-2247761639/4000000 : ℚ) vp01000110010 := join_branches bp010001100100 bp010001100101
private noncomputable def vp0100011001_0 : Blocks := edgeBlocks% "full/vectors/0100011001-V-0000.bin"
private noncomputable def vp0100011001_1 : Blocks := edgeBlocks% "full/vectors/0100011001-V-0001.bin"
noncomputable def vp0100011001 : Blocks := (Blocks.join vp0100011001_0 vp0100011001_1)
private theorem bp01000110010 : Branch 0 (-2247761639/8000000 : ℚ) vp0100011001 := by
  apply branch_left_normalized (c:=vp01000110010) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-2247761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2247761639/4000000 : ℚ) by norm_num]
  exact coverp01000110010
private noncomputable def ep01000110011_0 : Blocks := edgeBlocks% "full/vectors/01000110011-E-0000.bin"
private noncomputable def ep01000110011_1 : Blocks := edgeBlocks% "full/vectors/01000110011-E-0001.bin"
noncomputable def ep01000110011 : Blocks := (Blocks.join ep01000110011_0 ep01000110011_1)
private theorem idp01000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100011001.list =
    C ((2:ℤ)^212) * horner X vp01000110011.list + horner X ep01000110011.list := by
  exact edge_identity (B := (2:ℤ)^378) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000110011 : Branch 1 (-2247761639/8000000 : ℚ) vp0100011001 := by
  apply branch_checked idp01000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2247761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2251761639/4000000 : ℚ) by norm_num]
  exact coverp01000110011
theorem coverp0100011001 : Covers (-2247761639/8000000 : ℚ) vp0100011001 := join_branches bp01000110010 bp01000110011
private noncomputable def vp010001100011_0 : Blocks := edgeBlocks% "full/vectors/010001100011-V-0000.bin"
noncomputable def vp010001100011 : Blocks := vp010001100011_0
theorem coverp010001100011 : Covers (-2245761639/2000000 : ℚ) vp010001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp010001100010_0 : Blocks := edgeBlocks% "full/vectors/010001100010-V-0000.bin"
noncomputable def vp010001100010 : Blocks := vp010001100010_0
theorem coverp010001100010 : Covers (-2243761639/2000000 : ℚ) vp010001100010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000110001_0 : Blocks := edgeBlocks% "full/vectors/01000110001-V-0000.bin"
noncomputable def vp01000110001 : Blocks := vp01000110001_0
private theorem bp010001100010 : Branch 0 (-2243761639/4000000 : ℚ) vp01000110001 := by
  apply branch_left_normalized (c:=vp010001100010) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2243761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2243761639/2000000 : ℚ) by norm_num]
  exact coverp010001100010
private noncomputable def ep010001100011_0 : Blocks := edgeBlocks% "full/vectors/010001100011-E-0000.bin"
noncomputable def ep010001100011 : Blocks := ep010001100011_0
private theorem idp010001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000110001.list =
    C ((2:ℤ)^116) * horner X vp010001100011.list + horner X ep010001100011.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001100011 : Branch 1 (-2243761639/4000000 : ℚ) vp01000110001 := by
  apply branch_checked idp010001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2243761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2245761639/2000000 : ℚ) by norm_num]
  exact coverp010001100011
theorem coverp01000110001 : Covers (-2243761639/4000000 : ℚ) vp01000110001 := join_branches bp010001100010 bp010001100011
private noncomputable def vp010001100001_0 : Blocks := edgeBlocks% "full/vectors/010001100001-V-0000.bin"
noncomputable def vp010001100001 : Blocks := vp010001100001_0
theorem coverp010001100001 : Covers (-2241761639/2000000 : ℚ) vp010001100001 := cover_leaf (by decide +kernel)
private noncomputable def vp010001100000_0 : Blocks := edgeBlocks% "full/vectors/010001100000-V-0000.bin"
noncomputable def vp010001100000 : Blocks := vp010001100000_0
theorem coverp010001100000 : Covers (-2239761639/2000000 : ℚ) vp010001100000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000110000_0 : Blocks := edgeBlocks% "full/vectors/01000110000-V-0000.bin"
noncomputable def vp01000110000 : Blocks := vp01000110000_0
private theorem bp010001100000 : Branch 0 (-2239761639/4000000 : ℚ) vp01000110000 := by
  apply branch_left_normalized (c:=vp010001100000) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2239761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2239761639/2000000 : ℚ) by norm_num]
  exact coverp010001100000
private noncomputable def ep010001100001_0 : Blocks := edgeBlocks% "full/vectors/010001100001-E-0000.bin"
noncomputable def ep010001100001 : Blocks := ep010001100001_0
private theorem idp010001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000110000.list =
    C ((2:ℤ)^117) * horner X vp010001100001.list + horner X ep010001100001.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001100001 : Branch 1 (-2239761639/4000000 : ℚ) vp01000110000 := by
  apply branch_checked idp010001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2239761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2241761639/2000000 : ℚ) by norm_num]
  exact coverp010001100001
theorem coverp01000110000 : Covers (-2239761639/4000000 : ℚ) vp01000110000 := join_branches bp010001100000 bp010001100001
private noncomputable def vp0100011000_0 : Blocks := edgeBlocks% "full/vectors/0100011000-V-0000.bin"
private noncomputable def vp0100011000_1 : Blocks := edgeBlocks% "full/vectors/0100011000-V-0001.bin"
noncomputable def vp0100011000 : Blocks := (Blocks.join vp0100011000_0 vp0100011000_1)
private theorem bp01000110000 : Branch 0 (-2239761639/8000000 : ℚ) vp0100011000 := by
  apply branch_left_normalized (c:=vp01000110000) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-2239761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2239761639/4000000 : ℚ) by norm_num]
  exact coverp01000110000
private noncomputable def ep01000110001_0 : Blocks := edgeBlocks% "full/vectors/01000110001-E-0000.bin"
private noncomputable def ep01000110001_1 : Blocks := edgeBlocks% "full/vectors/01000110001-E-0001.bin"
noncomputable def ep01000110001 : Blocks := (Blocks.join ep01000110001_0 ep01000110001_1)
private theorem idp01000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100011000.list =
    C ((2:ℤ)^213) * horner X vp01000110001.list + horner X ep01000110001.list := by
  exact edge_identity (B := (2:ℤ)^379) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000110001 : Branch 1 (-2239761639/8000000 : ℚ) vp0100011000 := by
  apply branch_checked idp01000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2239761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2243761639/4000000 : ℚ) by norm_num]
  exact coverp01000110001
theorem coverp0100011000 : Covers (-2239761639/8000000 : ℚ) vp0100011000 := join_branches bp01000110000 bp01000110001
private noncomputable def vp010001100_0 : Blocks := edgeBlocks% "full/vectors/010001100-V-0000.bin"
private noncomputable def vp010001100_1 : Blocks := edgeBlocks% "full/vectors/010001100-V-0001.bin"
private noncomputable def vp010001100_2 : Blocks := edgeBlocks% "full/vectors/010001100-V-0002.bin"
noncomputable def vp010001100 : Blocks := (Blocks.join vp010001100_0 (Blocks.join vp010001100_1 vp010001100_2))
private theorem bp0100011000 : Branch 0 (-2239761639/16000000 : ℚ) vp010001100 := by
  apply branch_left_normalized (c:=vp0100011000) (k:=0) (m:=188) (by decide +kernel)
  rw [show 2*(-2239761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2239761639/8000000 : ℚ) by norm_num]
  exact coverp0100011000
private noncomputable def ep0100011001_0 : Blocks := edgeBlocks% "full/vectors/0100011001-E-0000.bin"
private noncomputable def ep0100011001_1 : Blocks := edgeBlocks% "full/vectors/0100011001-E-0001.bin"
private noncomputable def ep0100011001_2 : Blocks := edgeBlocks% "full/vectors/0100011001-E-0002.bin"
noncomputable def ep0100011001 : Blocks := (Blocks.join ep0100011001_0 (Blocks.join ep0100011001_1 ep0100011001_2))
private theorem idp0100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010001100.list =
    C ((2:ℤ)^402) * horner X vp0100011001.list + horner X ep0100011001.list := by
  exact edge_identity (B := (2:ℤ)^633) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100011001 : Branch 1 (-2239761639/16000000 : ℚ) vp010001100 := by
  apply branch_checked idp0100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2239761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2247761639/8000000 : ℚ) by norm_num]
  exact coverp0100011001
theorem coverp010001100 : Covers (-2239761639/16000000 : ℚ) vp010001100 := join_branches bp0100011000 bp0100011001
private noncomputable def vp01000110_0 : Blocks := edgeBlocks% "full/vectors/01000110-V-0000.bin"
private noncomputable def vp01000110_1 : Blocks := edgeBlocks% "full/vectors/01000110-V-0001.bin"
private noncomputable def vp01000110_2 : Blocks := edgeBlocks% "full/vectors/01000110-V-0002.bin"
private noncomputable def vp01000110_3 : Blocks := edgeBlocks% "full/vectors/01000110-V-0003.bin"
private noncomputable def vp01000110_4 : Blocks := edgeBlocks% "full/vectors/01000110-V-0004.bin"
private noncomputable def vp01000110_5 : Blocks := edgeBlocks% "full/vectors/01000110-V-0005.bin"
noncomputable def vp01000110 : Blocks := (Blocks.join (Blocks.join vp01000110_0 (Blocks.join vp01000110_1 vp01000110_2)) (Blocks.join vp01000110_3 (Blocks.join vp01000110_4 vp01000110_5)))
private theorem bp010001100 : Branch 0 (-2239761639/32000000 : ℚ) vp01000110 := by
  apply branch_left_normalized (c:=vp010001100) (k:=0) (m:=354) (by decide +kernel)
  rw [show 2*(-2239761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2239761639/16000000 : ℚ) by norm_num]
  exact coverp010001100
private noncomputable def ep010001101_0 : Blocks := edgeBlocks% "full/vectors/010001101-E-0000.bin"
private noncomputable def ep010001101_1 : Blocks := edgeBlocks% "full/vectors/010001101-E-0001.bin"
private noncomputable def ep010001101_2 : Blocks := edgeBlocks% "full/vectors/010001101-E-0002.bin"
private noncomputable def ep010001101_3 : Blocks := edgeBlocks% "full/vectors/010001101-E-0003.bin"
private noncomputable def ep010001101_4 : Blocks := edgeBlocks% "full/vectors/010001101-E-0004.bin"
private noncomputable def ep010001101_5 : Blocks := edgeBlocks% "full/vectors/010001101-E-0005.bin"
noncomputable def ep010001101 : Blocks := (Blocks.join (Blocks.join ep010001101_0 (Blocks.join ep010001101_1 ep010001101_2)) (Blocks.join ep010001101_3 (Blocks.join ep010001101_4 ep010001101_5)))
private theorem idp010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000110.list =
    C ((2:ℤ)^775) * horner X vp010001101.list + horner X ep010001101.list := by
  exact edge_identity (B := (2:ℤ)^1135) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001101 : Branch 1 (-2239761639/32000000 : ℚ) vp01000110 := by
  apply branch_checked idp010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2239761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2255761639/16000000 : ℚ) by norm_num]
  exact coverp010001101
theorem coverp01000110 : Covers (-2239761639/32000000 : ℚ) vp01000110 := join_branches bp010001100 bp010001101
private noncomputable def vp0100011_0 : Blocks := edgeBlocks% "full/vectors/0100011-V-0000.bin"
private noncomputable def vp0100011_1 : Blocks := edgeBlocks% "full/vectors/0100011-V-0001.bin"
private noncomputable def vp0100011_2 : Blocks := edgeBlocks% "full/vectors/0100011-V-0002.bin"
private noncomputable def vp0100011_3 : Blocks := edgeBlocks% "full/vectors/0100011-V-0003.bin"
private noncomputable def vp0100011_4 : Blocks := edgeBlocks% "full/vectors/0100011-V-0004.bin"
private noncomputable def vp0100011_5 : Blocks := edgeBlocks% "full/vectors/0100011-V-0005.bin"
private noncomputable def vp0100011_6 : Blocks := edgeBlocks% "full/vectors/0100011-V-0006.bin"
private noncomputable def vp0100011_7 : Blocks := edgeBlocks% "full/vectors/0100011-V-0007.bin"
private noncomputable def vp0100011_8 : Blocks := edgeBlocks% "full/vectors/0100011-V-0008.bin"
private noncomputable def vp0100011_9 : Blocks := edgeBlocks% "full/vectors/0100011-V-0009.bin"
private noncomputable def vp0100011_10 : Blocks := edgeBlocks% "full/vectors/0100011-V-0010.bin"
noncomputable def vp0100011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0100011_0 vp0100011_1) (Blocks.join vp0100011_2 (Blocks.join vp0100011_3 vp0100011_4))) (Blocks.join (Blocks.join vp0100011_5 (Blocks.join vp0100011_6 vp0100011_7)) (Blocks.join vp0100011_8 (Blocks.join vp0100011_9 vp0100011_10))))
private theorem bp01000110 : Branch 0 (-2239761639/64000000 : ℚ) vp0100011 := by
  apply branch_left_normalized (c:=vp01000110) (k:=0) (m:=681) (by decide +kernel)
  rw [show 2*(-2239761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2239761639/32000000 : ℚ) by norm_num]
  exact coverp01000110
private noncomputable def ep01000111_0 : Blocks := edgeBlocks% "full/vectors/01000111-E-0000.bin"
private noncomputable def ep01000111_1 : Blocks := edgeBlocks% "full/vectors/01000111-E-0001.bin"
private noncomputable def ep01000111_2 : Blocks := edgeBlocks% "full/vectors/01000111-E-0002.bin"
private noncomputable def ep01000111_3 : Blocks := edgeBlocks% "full/vectors/01000111-E-0003.bin"
private noncomputable def ep01000111_4 : Blocks := edgeBlocks% "full/vectors/01000111-E-0004.bin"
private noncomputable def ep01000111_5 : Blocks := edgeBlocks% "full/vectors/01000111-E-0005.bin"
private noncomputable def ep01000111_6 : Blocks := edgeBlocks% "full/vectors/01000111-E-0006.bin"
private noncomputable def ep01000111_7 : Blocks := edgeBlocks% "full/vectors/01000111-E-0007.bin"
private noncomputable def ep01000111_8 : Blocks := edgeBlocks% "full/vectors/01000111-E-0008.bin"
private noncomputable def ep01000111_9 : Blocks := edgeBlocks% "full/vectors/01000111-E-0009.bin"
private noncomputable def ep01000111_10 : Blocks := edgeBlocks% "full/vectors/01000111-E-0010.bin"
noncomputable def ep01000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01000111_0 ep01000111_1) (Blocks.join ep01000111_2 (Blocks.join ep01000111_3 ep01000111_4))) (Blocks.join (Blocks.join ep01000111_5 (Blocks.join ep01000111_6 ep01000111_7)) (Blocks.join ep01000111_8 (Blocks.join ep01000111_9 ep01000111_10))))
private theorem idp01000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100011.list =
    C ((2:ℤ)^1513) * horner X vp01000111.list + horner X ep01000111.list := by
  exact edge_identity (B := (2:ℤ)^2130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000111 : Branch 1 (-2239761639/64000000 : ℚ) vp0100011 := by
  apply branch_checked idp01000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2239761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2271761639/32000000 : ℚ) by norm_num]
  exact coverp01000111
theorem coverp0100011 : Covers (-2239761639/64000000 : ℚ) vp0100011 := join_branches bp01000110 bp01000111
private noncomputable def vp010001011111_0 : Blocks := edgeBlocks% "full/vectors/010001011111-V-0000.bin"
noncomputable def vp010001011111 : Blocks := vp010001011111_0
theorem coverp010001011111 : Covers (-2237761639/2000000 : ℚ) vp010001011111 := cover_leaf (by decide +kernel)
private noncomputable def vp010001011110_0 : Blocks := edgeBlocks% "full/vectors/010001011110-V-0000.bin"
noncomputable def vp010001011110 : Blocks := vp010001011110_0
theorem coverp010001011110 : Covers (-2235761639/2000000 : ℚ) vp010001011110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000101111_0 : Blocks := edgeBlocks% "full/vectors/01000101111-V-0000.bin"
noncomputable def vp01000101111 : Blocks := vp01000101111_0
private theorem bp010001011110 : Branch 0 (-2235761639/4000000 : ℚ) vp01000101111 := by
  apply branch_left_normalized (c:=vp010001011110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2235761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2235761639/2000000 : ℚ) by norm_num]
  exact coverp010001011110
private noncomputable def ep010001011111_0 : Blocks := edgeBlocks% "full/vectors/010001011111-E-0000.bin"
noncomputable def ep010001011111 : Blocks := ep010001011111_0
private theorem idp010001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000101111.list =
    C ((2:ℤ)^117) * horner X vp010001011111.list + horner X ep010001011111.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001011111 : Branch 1 (-2235761639/4000000 : ℚ) vp01000101111 := by
  apply branch_checked idp010001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-2235761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2237761639/2000000 : ℚ) by norm_num]
  exact coverp010001011111
theorem coverp01000101111 : Covers (-2235761639/4000000 : ℚ) vp01000101111 := join_branches bp010001011110 bp010001011111
private noncomputable def vp010001011101_0 : Blocks := edgeBlocks% "full/vectors/010001011101-V-0000.bin"
noncomputable def vp010001011101 : Blocks := vp010001011101_0
theorem coverp010001011101 : Covers (-2233761639/2000000 : ℚ) vp010001011101 := cover_leaf (by decide +kernel)
private noncomputable def vp010001011100_0 : Blocks := edgeBlocks% "full/vectors/010001011100-V-0000.bin"
noncomputable def vp010001011100 : Blocks := vp010001011100_0
theorem coverp010001011100 : Covers (-2231761639/2000000 : ℚ) vp010001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000101110_0 : Blocks := edgeBlocks% "full/vectors/01000101110-V-0000.bin"
noncomputable def vp01000101110 : Blocks := vp01000101110_0
private theorem bp010001011100 : Branch 0 (-2231761639/4000000 : ℚ) vp01000101110 := by
  apply branch_left_normalized (c:=vp010001011100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2231761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2231761639/2000000 : ℚ) by norm_num]
  exact coverp010001011100
private noncomputable def ep010001011101_0 : Blocks := edgeBlocks% "full/vectors/010001011101-E-0000.bin"
noncomputable def ep010001011101 : Blocks := ep010001011101_0
private theorem idp010001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000101110.list =
    C ((2:ℤ)^116) * horner X vp010001011101.list + horner X ep010001011101.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001011101 : Branch 1 (-2231761639/4000000 : ℚ) vp01000101110 := by
  apply branch_checked idp010001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2231761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2233761639/2000000 : ℚ) by norm_num]
  exact coverp010001011101
theorem coverp01000101110 : Covers (-2231761639/4000000 : ℚ) vp01000101110 := join_branches bp010001011100 bp010001011101
private noncomputable def vp0100010111_0 : Blocks := edgeBlocks% "full/vectors/0100010111-V-0000.bin"
private noncomputable def vp0100010111_1 : Blocks := edgeBlocks% "full/vectors/0100010111-V-0001.bin"
noncomputable def vp0100010111 : Blocks := (Blocks.join vp0100010111_0 vp0100010111_1)
private theorem bp01000101110 : Branch 0 (-2231761639/8000000 : ℚ) vp0100010111 := by
  apply branch_left_normalized (c:=vp01000101110) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-2231761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2231761639/4000000 : ℚ) by norm_num]
  exact coverp01000101110
private noncomputable def ep01000101111_0 : Blocks := edgeBlocks% "full/vectors/01000101111-E-0000.bin"
private noncomputable def ep01000101111_1 : Blocks := edgeBlocks% "full/vectors/01000101111-E-0001.bin"
noncomputable def ep01000101111 : Blocks := (Blocks.join ep01000101111_0 ep01000101111_1)
private theorem idp01000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100010111.list =
    C ((2:ℤ)^211) * horner X vp01000101111.list + horner X ep01000101111.list := by
  exact edge_identity (B := (2:ℤ)^378) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000101111 : Branch 1 (-2231761639/8000000 : ℚ) vp0100010111 := by
  apply branch_checked idp01000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2231761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2235761639/4000000 : ℚ) by norm_num]
  exact coverp01000101111
theorem coverp0100010111 : Covers (-2231761639/8000000 : ℚ) vp0100010111 := join_branches bp01000101110 bp01000101111
private noncomputable def vp010001011011_0 : Blocks := edgeBlocks% "full/vectors/010001011011-V-0000.bin"
noncomputable def vp010001011011 : Blocks := vp010001011011_0
theorem coverp010001011011 : Covers (-2229761639/2000000 : ℚ) vp010001011011 := cover_leaf (by decide +kernel)
private noncomputable def vp010001011010_0 : Blocks := edgeBlocks% "full/vectors/010001011010-V-0000.bin"
noncomputable def vp010001011010 : Blocks := vp010001011010_0
theorem coverp010001011010 : Covers (-2227761639/2000000 : ℚ) vp010001011010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000101101_0 : Blocks := edgeBlocks% "full/vectors/01000101101-V-0000.bin"
noncomputable def vp01000101101 : Blocks := vp01000101101_0
private theorem bp010001011010 : Branch 0 (-2227761639/4000000 : ℚ) vp01000101101 := by
  apply branch_left_normalized (c:=vp010001011010) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2227761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2227761639/2000000 : ℚ) by norm_num]
  exact coverp010001011010
private noncomputable def ep010001011011_0 : Blocks := edgeBlocks% "full/vectors/010001011011-E-0000.bin"
noncomputable def ep010001011011 : Blocks := ep010001011011_0
private theorem idp010001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000101101.list =
    C ((2:ℤ)^117) * horner X vp010001011011.list + horner X ep010001011011.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001011011 : Branch 1 (-2227761639/4000000 : ℚ) vp01000101101 := by
  apply branch_checked idp010001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-2227761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2229761639/2000000 : ℚ) by norm_num]
  exact coverp010001011011
theorem coverp01000101101 : Covers (-2227761639/4000000 : ℚ) vp01000101101 := join_branches bp010001011010 bp010001011011
private noncomputable def vp010001011001_0 : Blocks := edgeBlocks% "full/vectors/010001011001-V-0000.bin"
noncomputable def vp010001011001 : Blocks := vp010001011001_0
theorem coverp010001011001 : Covers (-2225761639/2000000 : ℚ) vp010001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp010001011000_0 : Blocks := edgeBlocks% "full/vectors/010001011000-V-0000.bin"
noncomputable def vp010001011000 : Blocks := vp010001011000_0
theorem coverp010001011000 : Covers (-2223761639/2000000 : ℚ) vp010001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000101100_0 : Blocks := edgeBlocks% "full/vectors/01000101100-V-0000.bin"
noncomputable def vp01000101100 : Blocks := vp01000101100_0
private theorem bp010001011000 : Branch 0 (-2223761639/4000000 : ℚ) vp01000101100 := by
  apply branch_left_normalized (c:=vp010001011000) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2223761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2223761639/2000000 : ℚ) by norm_num]
  exact coverp010001011000
private noncomputable def ep010001011001_0 : Blocks := edgeBlocks% "full/vectors/010001011001-E-0000.bin"
noncomputable def ep010001011001 : Blocks := ep010001011001_0
private theorem idp010001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000101100.list =
    C ((2:ℤ)^117) * horner X vp010001011001.list + horner X ep010001011001.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001011001 : Branch 1 (-2223761639/4000000 : ℚ) vp01000101100 := by
  apply branch_checked idp010001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2223761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2225761639/2000000 : ℚ) by norm_num]
  exact coverp010001011001
theorem coverp01000101100 : Covers (-2223761639/4000000 : ℚ) vp01000101100 := join_branches bp010001011000 bp010001011001
private noncomputable def vp0100010110_0 : Blocks := edgeBlocks% "full/vectors/0100010110-V-0000.bin"
private noncomputable def vp0100010110_1 : Blocks := edgeBlocks% "full/vectors/0100010110-V-0001.bin"
noncomputable def vp0100010110 : Blocks := (Blocks.join vp0100010110_0 vp0100010110_1)
private theorem bp01000101100 : Branch 0 (-2223761639/8000000 : ℚ) vp0100010110 := by
  apply branch_left_normalized (c:=vp01000101100) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-2223761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2223761639/4000000 : ℚ) by norm_num]
  exact coverp01000101100
private noncomputable def ep01000101101_0 : Blocks := edgeBlocks% "full/vectors/01000101101-E-0000.bin"
private noncomputable def ep01000101101_1 : Blocks := edgeBlocks% "full/vectors/01000101101-E-0001.bin"
noncomputable def ep01000101101 : Blocks := (Blocks.join ep01000101101_0 ep01000101101_1)
private theorem idp01000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100010110.list =
    C ((2:ℤ)^212) * horner X vp01000101101.list + horner X ep01000101101.list := by
  exact edge_identity (B := (2:ℤ)^379) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000101101 : Branch 1 (-2223761639/8000000 : ℚ) vp0100010110 := by
  apply branch_checked idp01000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2223761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2227761639/4000000 : ℚ) by norm_num]
  exact coverp01000101101
theorem coverp0100010110 : Covers (-2223761639/8000000 : ℚ) vp0100010110 := join_branches bp01000101100 bp01000101101
private noncomputable def vp010001011_0 : Blocks := edgeBlocks% "full/vectors/010001011-V-0000.bin"
private noncomputable def vp010001011_1 : Blocks := edgeBlocks% "full/vectors/010001011-V-0001.bin"
private noncomputable def vp010001011_2 : Blocks := edgeBlocks% "full/vectors/010001011-V-0002.bin"
noncomputable def vp010001011 : Blocks := (Blocks.join vp010001011_0 (Blocks.join vp010001011_1 vp010001011_2))
private theorem bp0100010110 : Branch 0 (-2223761639/16000000 : ℚ) vp010001011 := by
  apply branch_left_normalized (c:=vp0100010110) (k:=0) (m:=188) (by decide +kernel)
  rw [show 2*(-2223761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2223761639/8000000 : ℚ) by norm_num]
  exact coverp0100010110
private noncomputable def ep0100010111_0 : Blocks := edgeBlocks% "full/vectors/0100010111-E-0000.bin"
private noncomputable def ep0100010111_1 : Blocks := edgeBlocks% "full/vectors/0100010111-E-0001.bin"
private noncomputable def ep0100010111_2 : Blocks := edgeBlocks% "full/vectors/0100010111-E-0002.bin"
noncomputable def ep0100010111 : Blocks := (Blocks.join ep0100010111_0 (Blocks.join ep0100010111_1 ep0100010111_2))
private theorem idp0100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010001011.list =
    C ((2:ℤ)^403) * horner X vp0100010111.list + horner X ep0100010111.list := by
  exact edge_identity (B := (2:ℤ)^634) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100010111 : Branch 1 (-2223761639/16000000 : ℚ) vp010001011 := by
  apply branch_checked idp0100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2223761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2231761639/8000000 : ℚ) by norm_num]
  exact coverp0100010111
theorem coverp010001011 : Covers (-2223761639/16000000 : ℚ) vp010001011 := join_branches bp0100010110 bp0100010111
private noncomputable def vp010001010111_0 : Blocks := edgeBlocks% "full/vectors/010001010111-V-0000.bin"
noncomputable def vp010001010111 : Blocks := vp010001010111_0
theorem coverp010001010111 : Covers (-2221761639/2000000 : ℚ) vp010001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp010001010110_0 : Blocks := edgeBlocks% "full/vectors/010001010110-V-0000.bin"
noncomputable def vp010001010110 : Blocks := vp010001010110_0
theorem coverp010001010110 : Covers (-2219761639/2000000 : ℚ) vp010001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000101011_0 : Blocks := edgeBlocks% "full/vectors/01000101011-V-0000.bin"
noncomputable def vp01000101011 : Blocks := vp01000101011_0
private theorem bp010001010110 : Branch 0 (-2219761639/4000000 : ℚ) vp01000101011 := by
  apply branch_left_normalized (c:=vp010001010110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2219761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2219761639/2000000 : ℚ) by norm_num]
  exact coverp010001010110
private noncomputable def ep010001010111_0 : Blocks := edgeBlocks% "full/vectors/010001010111-E-0000.bin"
noncomputable def ep010001010111 : Blocks := ep010001010111_0
private theorem idp010001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000101011.list =
    C ((2:ℤ)^117) * horner X vp010001010111.list + horner X ep010001010111.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001010111 : Branch 1 (-2219761639/4000000 : ℚ) vp01000101011 := by
  apply branch_checked idp010001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2219761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2221761639/2000000 : ℚ) by norm_num]
  exact coverp010001010111
theorem coverp01000101011 : Covers (-2219761639/4000000 : ℚ) vp01000101011 := join_branches bp010001010110 bp010001010111
private noncomputable def vp010001010101_0 : Blocks := edgeBlocks% "full/vectors/010001010101-V-0000.bin"
noncomputable def vp010001010101 : Blocks := vp010001010101_0
theorem coverp010001010101 : Covers (-2217761639/2000000 : ℚ) vp010001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp010001010100_0 : Blocks := edgeBlocks% "full/vectors/010001010100-V-0000.bin"
noncomputable def vp010001010100 : Blocks := vp010001010100_0
theorem coverp010001010100 : Covers (-2215761639/2000000 : ℚ) vp010001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000101010_0 : Blocks := edgeBlocks% "full/vectors/01000101010-V-0000.bin"
noncomputable def vp01000101010 : Blocks := vp01000101010_0
private theorem bp010001010100 : Branch 0 (-2215761639/4000000 : ℚ) vp01000101010 := by
  apply branch_left_normalized (c:=vp010001010100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2215761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2215761639/2000000 : ℚ) by norm_num]
  exact coverp010001010100
private noncomputable def ep010001010101_0 : Blocks := edgeBlocks% "full/vectors/010001010101-E-0000.bin"
noncomputable def ep010001010101 : Blocks := ep010001010101_0
private theorem idp010001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000101010.list =
    C ((2:ℤ)^117) * horner X vp010001010101.list + horner X ep010001010101.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001010101 : Branch 1 (-2215761639/4000000 : ℚ) vp01000101010 := by
  apply branch_checked idp010001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2215761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2217761639/2000000 : ℚ) by norm_num]
  exact coverp010001010101
theorem coverp01000101010 : Covers (-2215761639/4000000 : ℚ) vp01000101010 := join_branches bp010001010100 bp010001010101
private noncomputable def vp0100010101_0 : Blocks := edgeBlocks% "full/vectors/0100010101-V-0000.bin"
private noncomputable def vp0100010101_1 : Blocks := edgeBlocks% "full/vectors/0100010101-V-0001.bin"
noncomputable def vp0100010101 : Blocks := (Blocks.join vp0100010101_0 vp0100010101_1)
private theorem bp01000101010 : Branch 0 (-2215761639/8000000 : ℚ) vp0100010101 := by
  apply branch_left_normalized (c:=vp01000101010) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-2215761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2215761639/4000000 : ℚ) by norm_num]
  exact coverp01000101010
private noncomputable def ep01000101011_0 : Blocks := edgeBlocks% "full/vectors/01000101011-E-0000.bin"
private noncomputable def ep01000101011_1 : Blocks := edgeBlocks% "full/vectors/01000101011-E-0001.bin"
noncomputable def ep01000101011 : Blocks := (Blocks.join ep01000101011_0 ep01000101011_1)
private theorem idp01000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100010101.list =
    C ((2:ℤ)^212) * horner X vp01000101011.list + horner X ep01000101011.list := by
  exact edge_identity (B := (2:ℤ)^378) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000101011 : Branch 1 (-2215761639/8000000 : ℚ) vp0100010101 := by
  apply branch_checked idp01000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2215761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2219761639/4000000 : ℚ) by norm_num]
  exact coverp01000101011
theorem coverp0100010101 : Covers (-2215761639/8000000 : ℚ) vp0100010101 := join_branches bp01000101010 bp01000101011
private noncomputable def vp010001010011_0 : Blocks := edgeBlocks% "full/vectors/010001010011-V-0000.bin"
noncomputable def vp010001010011 : Blocks := vp010001010011_0
theorem coverp010001010011 : Covers (-2213761639/2000000 : ℚ) vp010001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp010001010010_0 : Blocks := edgeBlocks% "full/vectors/010001010010-V-0000.bin"
noncomputable def vp010001010010 : Blocks := vp010001010010_0
theorem coverp010001010010 : Covers (-2211761639/2000000 : ℚ) vp010001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000101001_0 : Blocks := edgeBlocks% "full/vectors/01000101001-V-0000.bin"
noncomputable def vp01000101001 : Blocks := vp01000101001_0
private theorem bp010001010010 : Branch 0 (-2211761639/4000000 : ℚ) vp01000101001 := by
  apply branch_left_normalized (c:=vp010001010010) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2211761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2211761639/2000000 : ℚ) by norm_num]
  exact coverp010001010010
private noncomputable def ep010001010011_0 : Blocks := edgeBlocks% "full/vectors/010001010011-E-0000.bin"
noncomputable def ep010001010011 : Blocks := ep010001010011_0
private theorem idp010001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000101001.list =
    C ((2:ℤ)^118) * horner X vp010001010011.list + horner X ep010001010011.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001010011 : Branch 1 (-2211761639/4000000 : ℚ) vp01000101001 := by
  apply branch_checked idp010001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2211761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2213761639/2000000 : ℚ) by norm_num]
  exact coverp010001010011
theorem coverp01000101001 : Covers (-2211761639/4000000 : ℚ) vp01000101001 := join_branches bp010001010010 bp010001010011
private noncomputable def vp010001010001_0 : Blocks := edgeBlocks% "full/vectors/010001010001-V-0000.bin"
noncomputable def vp010001010001 : Blocks := vp010001010001_0
theorem coverp010001010001 : Covers (-2209761639/2000000 : ℚ) vp010001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp010001010000_0 : Blocks := edgeBlocks% "full/vectors/010001010000-V-0000.bin"
noncomputable def vp010001010000 : Blocks := vp010001010000_0
theorem coverp010001010000 : Covers (-2207761639/2000000 : ℚ) vp010001010000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000101000_0 : Blocks := edgeBlocks% "full/vectors/01000101000-V-0000.bin"
noncomputable def vp01000101000 : Blocks := vp01000101000_0
private theorem bp010001010000 : Branch 0 (-2207761639/4000000 : ℚ) vp01000101000 := by
  apply branch_left_normalized (c:=vp010001010000) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2207761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2207761639/2000000 : ℚ) by norm_num]
  exact coverp010001010000
private noncomputable def ep010001010001_0 : Blocks := edgeBlocks% "full/vectors/010001010001-E-0000.bin"
noncomputable def ep010001010001 : Blocks := ep010001010001_0
private theorem idp010001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000101000.list =
    C ((2:ℤ)^114) * horner X vp010001010001.list + horner X ep010001010001.list := by
  exact edge_identity (B := (2:ℤ)^247) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001010001 : Branch 1 (-2207761639/4000000 : ℚ) vp01000101000 := by
  apply branch_checked idp010001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2207761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2209761639/2000000 : ℚ) by norm_num]
  exact coverp010001010001
theorem coverp01000101000 : Covers (-2207761639/4000000 : ℚ) vp01000101000 := join_branches bp010001010000 bp010001010001
private noncomputable def vp0100010100_0 : Blocks := edgeBlocks% "full/vectors/0100010100-V-0000.bin"
private noncomputable def vp0100010100_1 : Blocks := edgeBlocks% "full/vectors/0100010100-V-0001.bin"
noncomputable def vp0100010100 : Blocks := (Blocks.join vp0100010100_0 vp0100010100_1)
private theorem bp01000101000 : Branch 0 (-2207761639/8000000 : ℚ) vp0100010100 := by
  apply branch_left_normalized (c:=vp01000101000) (k:=0) (m:=103) (by decide +kernel)
  rw [show 2*(-2207761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2207761639/4000000 : ℚ) by norm_num]
  exact coverp01000101000
private noncomputable def ep01000101001_0 : Blocks := edgeBlocks% "full/vectors/01000101001-E-0000.bin"
private noncomputable def ep01000101001_1 : Blocks := edgeBlocks% "full/vectors/01000101001-E-0001.bin"
noncomputable def ep01000101001 : Blocks := (Blocks.join ep01000101001_0 ep01000101001_1)
private theorem idp01000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100010100.list =
    C ((2:ℤ)^210) * horner X vp01000101001.list + horner X ep01000101001.list := by
  exact edge_identity (B := (2:ℤ)^377) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000101001 : Branch 1 (-2207761639/8000000 : ℚ) vp0100010100 := by
  apply branch_checked idp01000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2207761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2211761639/4000000 : ℚ) by norm_num]
  exact coverp01000101001
theorem coverp0100010100 : Covers (-2207761639/8000000 : ℚ) vp0100010100 := join_branches bp01000101000 bp01000101001
private noncomputable def vp010001010_0 : Blocks := edgeBlocks% "full/vectors/010001010-V-0000.bin"
private noncomputable def vp010001010_1 : Blocks := edgeBlocks% "full/vectors/010001010-V-0001.bin"
private noncomputable def vp010001010_2 : Blocks := edgeBlocks% "full/vectors/010001010-V-0002.bin"
noncomputable def vp010001010 : Blocks := (Blocks.join vp010001010_0 (Blocks.join vp010001010_1 vp010001010_2))
private theorem bp0100010100 : Branch 0 (-2207761639/16000000 : ℚ) vp010001010 := by
  apply branch_left_normalized (c:=vp0100010100) (k:=0) (m:=188) (by decide +kernel)
  rw [show 2*(-2207761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2207761639/8000000 : ℚ) by norm_num]
  exact coverp0100010100
private noncomputable def ep0100010101_0 : Blocks := edgeBlocks% "full/vectors/0100010101-E-0000.bin"
private noncomputable def ep0100010101_1 : Blocks := edgeBlocks% "full/vectors/0100010101-E-0001.bin"
private noncomputable def ep0100010101_2 : Blocks := edgeBlocks% "full/vectors/0100010101-E-0002.bin"
noncomputable def ep0100010101 : Blocks := (Blocks.join ep0100010101_0 (Blocks.join ep0100010101_1 ep0100010101_2))
private theorem idp0100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010001010.list =
    C ((2:ℤ)^400) * horner X vp0100010101.list + horner X ep0100010101.list := by
  exact edge_identity (B := (2:ℤ)^631) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100010101 : Branch 1 (-2207761639/16000000 : ℚ) vp010001010 := by
  apply branch_checked idp0100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2207761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2215761639/8000000 : ℚ) by norm_num]
  exact coverp0100010101
theorem coverp010001010 : Covers (-2207761639/16000000 : ℚ) vp010001010 := join_branches bp0100010100 bp0100010101
private noncomputable def vp01000101_0 : Blocks := edgeBlocks% "full/vectors/01000101-V-0000.bin"
private noncomputable def vp01000101_1 : Blocks := edgeBlocks% "full/vectors/01000101-V-0001.bin"
private noncomputable def vp01000101_2 : Blocks := edgeBlocks% "full/vectors/01000101-V-0002.bin"
private noncomputable def vp01000101_3 : Blocks := edgeBlocks% "full/vectors/01000101-V-0003.bin"
private noncomputable def vp01000101_4 : Blocks := edgeBlocks% "full/vectors/01000101-V-0004.bin"
private noncomputable def vp01000101_5 : Blocks := edgeBlocks% "full/vectors/01000101-V-0005.bin"
noncomputable def vp01000101 : Blocks := (Blocks.join (Blocks.join vp01000101_0 (Blocks.join vp01000101_1 vp01000101_2)) (Blocks.join vp01000101_3 (Blocks.join vp01000101_4 vp01000101_5)))
private theorem bp010001010 : Branch 0 (-2207761639/32000000 : ℚ) vp01000101 := by
  apply branch_left_normalized (c:=vp010001010) (k:=0) (m:=354) (by decide +kernel)
  rw [show 2*(-2207761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2207761639/16000000 : ℚ) by norm_num]
  exact coverp010001010
private noncomputable def ep010001011_0 : Blocks := edgeBlocks% "full/vectors/010001011-E-0000.bin"
private noncomputable def ep010001011_1 : Blocks := edgeBlocks% "full/vectors/010001011-E-0001.bin"
private noncomputable def ep010001011_2 : Blocks := edgeBlocks% "full/vectors/010001011-E-0002.bin"
private noncomputable def ep010001011_3 : Blocks := edgeBlocks% "full/vectors/010001011-E-0003.bin"
private noncomputable def ep010001011_4 : Blocks := edgeBlocks% "full/vectors/010001011-E-0004.bin"
private noncomputable def ep010001011_5 : Blocks := edgeBlocks% "full/vectors/010001011-E-0005.bin"
noncomputable def ep010001011 : Blocks := (Blocks.join (Blocks.join ep010001011_0 (Blocks.join ep010001011_1 ep010001011_2)) (Blocks.join ep010001011_3 (Blocks.join ep010001011_4 ep010001011_5)))
private theorem idp010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000101.list =
    C ((2:ℤ)^775) * horner X vp010001011.list + horner X ep010001011.list := by
  exact edge_identity (B := (2:ℤ)^1138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001011 : Branch 1 (-2207761639/32000000 : ℚ) vp01000101 := by
  apply branch_checked idp010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2207761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2223761639/16000000 : ℚ) by norm_num]
  exact coverp010001011
theorem coverp01000101 : Covers (-2207761639/32000000 : ℚ) vp01000101 := join_branches bp010001010 bp010001011
private noncomputable def vp010001001111_0 : Blocks := edgeBlocks% "full/vectors/010001001111-V-0000.bin"
noncomputable def vp010001001111 : Blocks := vp010001001111_0
theorem coverp010001001111 : Covers (-2205761639/2000000 : ℚ) vp010001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp010001001110_0 : Blocks := edgeBlocks% "full/vectors/010001001110-V-0000.bin"
noncomputable def vp010001001110 : Blocks := vp010001001110_0
theorem coverp010001001110 : Covers (-2203761639/2000000 : ℚ) vp010001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000100111_0 : Blocks := edgeBlocks% "full/vectors/01000100111-V-0000.bin"
noncomputable def vp01000100111 : Blocks := vp01000100111_0
private theorem bp010001001110 : Branch 0 (-2203761639/4000000 : ℚ) vp01000100111 := by
  apply branch_left_normalized (c:=vp010001001110) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2203761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2203761639/2000000 : ℚ) by norm_num]
  exact coverp010001001110
private noncomputable def ep010001001111_0 : Blocks := edgeBlocks% "full/vectors/010001001111-E-0000.bin"
noncomputable def ep010001001111 : Blocks := ep010001001111_0
private theorem idp010001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000100111.list =
    C ((2:ℤ)^115) * horner X vp010001001111.list + horner X ep010001001111.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001001111 : Branch 1 (-2203761639/4000000 : ℚ) vp01000100111 := by
  apply branch_checked idp010001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-2203761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2205761639/2000000 : ℚ) by norm_num]
  exact coverp010001001111
theorem coverp01000100111 : Covers (-2203761639/4000000 : ℚ) vp01000100111 := join_branches bp010001001110 bp010001001111
private noncomputable def vp010001001101_0 : Blocks := edgeBlocks% "full/vectors/010001001101-V-0000.bin"
noncomputable def vp010001001101 : Blocks := vp010001001101_0
theorem coverp010001001101 : Covers (-2201761639/2000000 : ℚ) vp010001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp010001001100_0 : Blocks := edgeBlocks% "full/vectors/010001001100-V-0000.bin"
noncomputable def vp010001001100 : Blocks := vp010001001100_0
theorem coverp010001001100 : Covers (-2199761639/2000000 : ℚ) vp010001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000100110_0 : Blocks := edgeBlocks% "full/vectors/01000100110-V-0000.bin"
noncomputable def vp01000100110 : Blocks := vp01000100110_0
private theorem bp010001001100 : Branch 0 (-2199761639/4000000 : ℚ) vp01000100110 := by
  apply branch_left_normalized (c:=vp010001001100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-2199761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2199761639/2000000 : ℚ) by norm_num]
  exact coverp010001001100
private noncomputable def ep010001001101_0 : Blocks := edgeBlocks% "full/vectors/010001001101-E-0000.bin"
noncomputable def ep010001001101 : Blocks := ep010001001101_0
private theorem idp010001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000100110.list =
    C ((2:ℤ)^118) * horner X vp010001001101.list + horner X ep010001001101.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001001101 : Branch 1 (-2199761639/4000000 : ℚ) vp01000100110 := by
  apply branch_checked idp010001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2199761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2201761639/2000000 : ℚ) by norm_num]
  exact coverp010001001101
theorem coverp01000100110 : Covers (-2199761639/4000000 : ℚ) vp01000100110 := join_branches bp010001001100 bp010001001101
private noncomputable def vp0100010011_0 : Blocks := edgeBlocks% "full/vectors/0100010011-V-0000.bin"
private noncomputable def vp0100010011_1 : Blocks := edgeBlocks% "full/vectors/0100010011-V-0001.bin"
noncomputable def vp0100010011 : Blocks := (Blocks.join vp0100010011_0 vp0100010011_1)
private theorem bp01000100110 : Branch 0 (-2199761639/8000000 : ℚ) vp0100010011 := by
  apply branch_left_normalized (c:=vp01000100110) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-2199761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2199761639/4000000 : ℚ) by norm_num]
  exact coverp01000100110
private noncomputable def ep01000100111_0 : Blocks := edgeBlocks% "full/vectors/01000100111-E-0000.bin"
private noncomputable def ep01000100111_1 : Blocks := edgeBlocks% "full/vectors/01000100111-E-0001.bin"
noncomputable def ep01000100111 : Blocks := (Blocks.join ep01000100111_0 ep01000100111_1)
private theorem idp01000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100010011.list =
    C ((2:ℤ)^214) * horner X vp01000100111.list + horner X ep01000100111.list := by
  exact edge_identity (B := (2:ℤ)^378) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000100111 : Branch 1 (-2199761639/8000000 : ℚ) vp0100010011 := by
  apply branch_checked idp01000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2199761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2203761639/4000000 : ℚ) by norm_num]
  exact coverp01000100111
theorem coverp0100010011 : Covers (-2199761639/8000000 : ℚ) vp0100010011 := join_branches bp01000100110 bp01000100111
private noncomputable def vp010001001011_0 : Blocks := edgeBlocks% "full/vectors/010001001011-V-0000.bin"
noncomputable def vp010001001011 : Blocks := vp010001001011_0
theorem coverp010001001011 : Covers (-2197761639/2000000 : ℚ) vp010001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp010001001010_0 : Blocks := edgeBlocks% "full/vectors/010001001010-V-0000.bin"
noncomputable def vp010001001010 : Blocks := vp010001001010_0
theorem coverp010001001010 : Covers (-2195761639/2000000 : ℚ) vp010001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp01000100101_0 : Blocks := edgeBlocks% "full/vectors/01000100101-V-0000.bin"
noncomputable def vp01000100101 : Blocks := vp01000100101_0
private theorem bp010001001010 : Branch 0 (-2195761639/4000000 : ℚ) vp01000100101 := by
  apply branch_left_normalized (c:=vp010001001010) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2195761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2195761639/2000000 : ℚ) by norm_num]
  exact coverp010001001010
private noncomputable def ep010001001011_0 : Blocks := edgeBlocks% "full/vectors/010001001011-E-0000.bin"
noncomputable def ep010001001011 : Blocks := ep010001001011_0
private theorem idp010001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000100101.list =
    C ((2:ℤ)^112) * horner X vp010001001011.list + horner X ep010001001011.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001001011 : Branch 1 (-2195761639/4000000 : ℚ) vp01000100101 := by
  apply branch_checked idp010001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2195761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2197761639/2000000 : ℚ) by norm_num]
  exact coverp010001001011
theorem coverp01000100101 : Covers (-2195761639/4000000 : ℚ) vp01000100101 := join_branches bp010001001010 bp010001001011
private noncomputable def vp010001001001_0 : Blocks := edgeBlocks% "full/vectors/010001001001-V-0000.bin"
noncomputable def vp010001001001 : Blocks := vp010001001001_0
theorem coverp010001001001 : Covers (-2193761639/2000000 : ℚ) vp010001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp010001001000_0 : Blocks := edgeBlocks% "full/vectors/010001001000-V-0000.bin"
noncomputable def vp010001001000 : Blocks := vp010001001000_0
theorem coverp010001001000 : Covers (-2191761639/2000000 : ℚ) vp010001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp01000100100_0 : Blocks := edgeBlocks% "full/vectors/01000100100-V-0000.bin"
noncomputable def vp01000100100 : Blocks := vp01000100100_0
private theorem bp010001001000 : Branch 0 (-2191761639/4000000 : ℚ) vp01000100100 := by
  apply branch_left_normalized (c:=vp010001001000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2191761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2191761639/2000000 : ℚ) by norm_num]
  exact coverp010001001000
private noncomputable def ep010001001001_0 : Blocks := edgeBlocks% "full/vectors/010001001001-E-0000.bin"
noncomputable def ep010001001001 : Blocks := ep010001001001_0
private theorem idp010001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000100100.list =
    C ((2:ℤ)^113) * horner X vp010001001001.list + horner X ep010001001001.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001001001 : Branch 1 (-2191761639/4000000 : ℚ) vp01000100100 := by
  apply branch_checked idp010001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2191761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2193761639/2000000 : ℚ) by norm_num]
  exact coverp010001001001
theorem coverp01000100100 : Covers (-2191761639/4000000 : ℚ) vp01000100100 := join_branches bp010001001000 bp010001001001
private noncomputable def vp0100010010_0 : Blocks := edgeBlocks% "full/vectors/0100010010-V-0000.bin"
private noncomputable def vp0100010010_1 : Blocks := edgeBlocks% "full/vectors/0100010010-V-0001.bin"
noncomputable def vp0100010010 : Blocks := (Blocks.join vp0100010010_0 vp0100010010_1)
private theorem bp01000100100 : Branch 0 (-2191761639/8000000 : ℚ) vp0100010010 := by
  apply branch_left_normalized (c:=vp01000100100) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-2191761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2191761639/4000000 : ℚ) by norm_num]
  exact coverp01000100100
private noncomputable def ep01000100101_0 : Blocks := edgeBlocks% "full/vectors/01000100101-E-0000.bin"
private noncomputable def ep01000100101_1 : Blocks := edgeBlocks% "full/vectors/01000100101-E-0001.bin"
noncomputable def ep01000100101 : Blocks := (Blocks.join ep01000100101_0 ep01000100101_1)
private theorem idp01000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100010010.list =
    C ((2:ℤ)^207) * horner X vp01000100101.list + horner X ep01000100101.list := by
  exact edge_identity (B := (2:ℤ)^371) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000100101 : Branch 1 (-2191761639/8000000 : ℚ) vp0100010010 := by
  apply branch_checked idp01000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2191761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2195761639/4000000 : ℚ) by norm_num]
  exact coverp01000100101
theorem coverp0100010010 : Covers (-2191761639/8000000 : ℚ) vp0100010010 := join_branches bp01000100100 bp01000100101
private noncomputable def vp010001001_0 : Blocks := edgeBlocks% "full/vectors/010001001-V-0000.bin"
private noncomputable def vp010001001_1 : Blocks := edgeBlocks% "full/vectors/010001001-V-0001.bin"
private noncomputable def vp010001001_2 : Blocks := edgeBlocks% "full/vectors/010001001-V-0002.bin"
noncomputable def vp010001001 : Blocks := (Blocks.join vp010001001_0 (Blocks.join vp010001001_1 vp010001001_2))
private theorem bp0100010010 : Branch 0 (-2191761639/16000000 : ℚ) vp010001001 := by
  apply branch_left_normalized (c:=vp0100010010) (k:=0) (m:=186) (by decide +kernel)
  rw [show 2*(-2191761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2191761639/8000000 : ℚ) by norm_num]
  exact coverp0100010010
private noncomputable def ep0100010011_0 : Blocks := edgeBlocks% "full/vectors/0100010011-E-0000.bin"
private noncomputable def ep0100010011_1 : Blocks := edgeBlocks% "full/vectors/0100010011-E-0001.bin"
private noncomputable def ep0100010011_2 : Blocks := edgeBlocks% "full/vectors/0100010011-E-0002.bin"
noncomputable def ep0100010011 : Blocks := (Blocks.join ep0100010011_0 (Blocks.join ep0100010011_1 ep0100010011_2))
private theorem idp0100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010001001.list =
    C ((2:ℤ)^395) * horner X vp0100010011.list + horner X ep0100010011.list := by
  exact edge_identity (B := (2:ℤ)^627) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100010011 : Branch 1 (-2191761639/16000000 : ℚ) vp010001001 := by
  apply branch_checked idp0100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2191761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2199761639/8000000 : ℚ) by norm_num]
  exact coverp0100010011
theorem coverp010001001 : Covers (-2191761639/16000000 : ℚ) vp010001001 := join_branches bp0100010010 bp0100010011
private noncomputable def vp010001000111_0 : Blocks := edgeBlocks% "full/vectors/010001000111-V-0000.bin"
noncomputable def vp010001000111 : Blocks := vp010001000111_0
theorem coverp010001000111 : Covers (-2189761639/2000000 : ℚ) vp010001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp010001000110_0 : Blocks := edgeBlocks% "full/vectors/010001000110-V-0000.bin"
noncomputable def vp010001000110 : Blocks := vp010001000110_0
theorem coverp010001000110 : Covers (-2187761639/2000000 : ℚ) vp010001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp01000100011_0 : Blocks := edgeBlocks% "full/vectors/01000100011-V-0000.bin"
noncomputable def vp01000100011 : Blocks := vp01000100011_0
private theorem bp010001000110 : Branch 0 (-2187761639/4000000 : ℚ) vp01000100011 := by
  apply branch_left_normalized (c:=vp010001000110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2187761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2187761639/2000000 : ℚ) by norm_num]
  exact coverp010001000110
private noncomputable def ep010001000111_0 : Blocks := edgeBlocks% "full/vectors/010001000111-E-0000.bin"
noncomputable def ep010001000111 : Blocks := ep010001000111_0
private theorem idp010001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000100011.list =
    C ((2:ℤ)^112) * horner X vp010001000111.list + horner X ep010001000111.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001000111 : Branch 1 (-2187761639/4000000 : ℚ) vp01000100011 := by
  apply branch_checked idp010001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2187761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2189761639/2000000 : ℚ) by norm_num]
  exact coverp010001000111
theorem coverp01000100011 : Covers (-2187761639/4000000 : ℚ) vp01000100011 := join_branches bp010001000110 bp010001000111
private noncomputable def vp010001000101_0 : Blocks := edgeBlocks% "full/vectors/010001000101-V-0000.bin"
noncomputable def vp010001000101 : Blocks := vp010001000101_0
theorem coverp010001000101 : Covers (-2185761639/2000000 : ℚ) vp010001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp010001000100_0 : Blocks := edgeBlocks% "full/vectors/010001000100-V-0000.bin"
noncomputable def vp010001000100 : Blocks := vp010001000100_0
theorem coverp010001000100 : Covers (-2183761639/2000000 : ℚ) vp010001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp01000100010_0 : Blocks := edgeBlocks% "full/vectors/01000100010-V-0000.bin"
noncomputable def vp01000100010 : Blocks := vp01000100010_0
private theorem bp010001000100 : Branch 0 (-2183761639/4000000 : ℚ) vp01000100010 := by
  apply branch_left_normalized (c:=vp010001000100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-2183761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2183761639/2000000 : ℚ) by norm_num]
  exact coverp010001000100
private noncomputable def ep010001000101_0 : Blocks := edgeBlocks% "full/vectors/010001000101-E-0000.bin"
noncomputable def ep010001000101 : Blocks := ep010001000101_0
private theorem idp010001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000100010.list =
    C ((2:ℤ)^112) * horner X vp010001000101.list + horner X ep010001000101.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001000101 : Branch 1 (-2183761639/4000000 : ℚ) vp01000100010 := by
  apply branch_checked idp010001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2183761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2185761639/2000000 : ℚ) by norm_num]
  exact coverp010001000101
theorem coverp01000100010 : Covers (-2183761639/4000000 : ℚ) vp01000100010 := join_branches bp010001000100 bp010001000101
private noncomputable def vp0100010001_0 : Blocks := edgeBlocks% "full/vectors/0100010001-V-0000.bin"
private noncomputable def vp0100010001_1 : Blocks := edgeBlocks% "full/vectors/0100010001-V-0001.bin"
noncomputable def vp0100010001 : Blocks := (Blocks.join vp0100010001_0 vp0100010001_1)
private theorem bp01000100010 : Branch 0 (-2183761639/8000000 : ℚ) vp0100010001 := by
  apply branch_left_normalized (c:=vp01000100010) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-2183761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2183761639/4000000 : ℚ) by norm_num]
  exact coverp01000100010
private noncomputable def ep01000100011_0 : Blocks := edgeBlocks% "full/vectors/01000100011-E-0000.bin"
private noncomputable def ep01000100011_1 : Blocks := edgeBlocks% "full/vectors/01000100011-E-0001.bin"
noncomputable def ep01000100011 : Blocks := (Blocks.join ep01000100011_0 ep01000100011_1)
private theorem idp01000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100010001.list =
    C ((2:ℤ)^207) * horner X vp01000100011.list + horner X ep01000100011.list := by
  exact edge_identity (B := (2:ℤ)^366) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000100011 : Branch 1 (-2183761639/8000000 : ℚ) vp0100010001 := by
  apply branch_checked idp01000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2183761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2187761639/4000000 : ℚ) by norm_num]
  exact coverp01000100011
theorem coverp0100010001 : Covers (-2183761639/8000000 : ℚ) vp0100010001 := join_branches bp01000100010 bp01000100011
private noncomputable def vp01000100001_0 : Blocks := edgeBlocks% "full/vectors/01000100001-V-0000.bin"
noncomputable def vp01000100001 : Blocks := vp01000100001_0
theorem coverp01000100001 : Covers (-2179761639/4000000 : ℚ) vp01000100001 := cover_leaf (by decide +kernel)
private noncomputable def vp01000100000_0 : Blocks := edgeBlocks% "full/vectors/01000100000-V-0000.bin"
noncomputable def vp01000100000 : Blocks := vp01000100000_0
theorem coverp01000100000 : Covers (-2175761639/4000000 : ℚ) vp01000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0100010000_0 : Blocks := edgeBlocks% "full/vectors/0100010000-V-0000.bin"
private noncomputable def vp0100010000_1 : Blocks := edgeBlocks% "full/vectors/0100010000-V-0001.bin"
noncomputable def vp0100010000 : Blocks := (Blocks.join vp0100010000_0 vp0100010000_1)
private theorem bp01000100000 : Branch 0 (-2175761639/8000000 : ℚ) vp0100010000 := by
  apply branch_left_normalized (c:=vp01000100000) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-2175761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2175761639/4000000 : ℚ) by norm_num]
  exact coverp01000100000
private noncomputable def ep01000100001_0 : Blocks := edgeBlocks% "full/vectors/01000100001-E-0000.bin"
private noncomputable def ep01000100001_1 : Blocks := edgeBlocks% "full/vectors/01000100001-E-0001.bin"
noncomputable def ep01000100001 : Blocks := (Blocks.join ep01000100001_0 ep01000100001_1)
private theorem idp01000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100010000.list =
    C ((2:ℤ)^208) * horner X vp01000100001.list + horner X ep01000100001.list := by
  exact edge_identity (B := (2:ℤ)^366) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000100001 : Branch 1 (-2175761639/8000000 : ℚ) vp0100010000 := by
  apply branch_checked idp01000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-2175761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2179761639/4000000 : ℚ) by norm_num]
  exact coverp01000100001
theorem coverp0100010000 : Covers (-2175761639/8000000 : ℚ) vp0100010000 := join_branches bp01000100000 bp01000100001
private noncomputable def vp010001000_0 : Blocks := edgeBlocks% "full/vectors/010001000-V-0000.bin"
private noncomputable def vp010001000_1 : Blocks := edgeBlocks% "full/vectors/010001000-V-0001.bin"
private noncomputable def vp010001000_2 : Blocks := edgeBlocks% "full/vectors/010001000-V-0002.bin"
noncomputable def vp010001000 : Blocks := (Blocks.join vp010001000_0 (Blocks.join vp010001000_1 vp010001000_2))
private theorem bp0100010000 : Branch 0 (-2175761639/16000000 : ℚ) vp010001000 := by
  apply branch_left_normalized (c:=vp0100010000) (k:=0) (m:=184) (by decide +kernel)
  rw [show 2*(-2175761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2175761639/8000000 : ℚ) by norm_num]
  exact coverp0100010000
private noncomputable def ep0100010001_0 : Blocks := edgeBlocks% "full/vectors/0100010001-E-0000.bin"
private noncomputable def ep0100010001_1 : Blocks := edgeBlocks% "full/vectors/0100010001-E-0001.bin"
private noncomputable def ep0100010001_2 : Blocks := edgeBlocks% "full/vectors/0100010001-E-0002.bin"
noncomputable def ep0100010001 : Blocks := (Blocks.join ep0100010001_0 (Blocks.join ep0100010001_1 ep0100010001_2))
private theorem idp0100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010001000.list =
    C ((2:ℤ)^399) * horner X vp0100010001.list + horner X ep0100010001.list := by
  exact edge_identity (B := (2:ℤ)^623) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100010001 : Branch 1 (-2175761639/16000000 : ℚ) vp010001000 := by
  apply branch_checked idp0100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-2175761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2183761639/8000000 : ℚ) by norm_num]
  exact coverp0100010001
theorem coverp010001000 : Covers (-2175761639/16000000 : ℚ) vp010001000 := join_branches bp0100010000 bp0100010001
private noncomputable def vp01000100_0 : Blocks := edgeBlocks% "full/vectors/01000100-V-0000.bin"
private noncomputable def vp01000100_1 : Blocks := edgeBlocks% "full/vectors/01000100-V-0001.bin"
private noncomputable def vp01000100_2 : Blocks := edgeBlocks% "full/vectors/01000100-V-0002.bin"
private noncomputable def vp01000100_3 : Blocks := edgeBlocks% "full/vectors/01000100-V-0003.bin"
private noncomputable def vp01000100_4 : Blocks := edgeBlocks% "full/vectors/01000100-V-0004.bin"
private noncomputable def vp01000100_5 : Blocks := edgeBlocks% "full/vectors/01000100-V-0005.bin"
noncomputable def vp01000100 : Blocks := (Blocks.join (Blocks.join vp01000100_0 (Blocks.join vp01000100_1 vp01000100_2)) (Blocks.join vp01000100_3 (Blocks.join vp01000100_4 vp01000100_5)))
private theorem bp010001000 : Branch 0 (-2175761639/32000000 : ℚ) vp01000100 := by
  apply branch_left_normalized (c:=vp010001000) (k:=0) (m:=352) (by decide +kernel)
  rw [show 2*(-2175761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2175761639/16000000 : ℚ) by norm_num]
  exact coverp010001000
private noncomputable def ep010001001_0 : Blocks := edgeBlocks% "full/vectors/010001001-E-0000.bin"
private noncomputable def ep010001001_1 : Blocks := edgeBlocks% "full/vectors/010001001-E-0001.bin"
private noncomputable def ep010001001_2 : Blocks := edgeBlocks% "full/vectors/010001001-E-0002.bin"
private noncomputable def ep010001001_3 : Blocks := edgeBlocks% "full/vectors/010001001-E-0003.bin"
private noncomputable def ep010001001_4 : Blocks := edgeBlocks% "full/vectors/010001001-E-0004.bin"
private noncomputable def ep010001001_5 : Blocks := edgeBlocks% "full/vectors/010001001-E-0005.bin"
noncomputable def ep010001001 : Blocks := (Blocks.join (Blocks.join ep010001001_0 (Blocks.join ep010001001_1 ep010001001_2)) (Blocks.join ep010001001_3 (Blocks.join ep010001001_4 ep010001001_5)))
private theorem idp010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01000100.list =
    C ((2:ℤ)^774) * horner X vp010001001.list + horner X ep010001001.list := by
  exact edge_identity (B := (2:ℤ)^1133) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp010001001 : Branch 1 (-2175761639/32000000 : ℚ) vp01000100 := by
  apply branch_checked idp010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2175761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2191761639/16000000 : ℚ) by norm_num]
  exact coverp010001001
theorem coverp01000100 : Covers (-2175761639/32000000 : ℚ) vp01000100 := join_branches bp010001000 bp010001001
private noncomputable def vp0100010_0 : Blocks := edgeBlocks% "full/vectors/0100010-V-0000.bin"
private noncomputable def vp0100010_1 : Blocks := edgeBlocks% "full/vectors/0100010-V-0001.bin"
private noncomputable def vp0100010_2 : Blocks := edgeBlocks% "full/vectors/0100010-V-0002.bin"
private noncomputable def vp0100010_3 : Blocks := edgeBlocks% "full/vectors/0100010-V-0003.bin"
private noncomputable def vp0100010_4 : Blocks := edgeBlocks% "full/vectors/0100010-V-0004.bin"
private noncomputable def vp0100010_5 : Blocks := edgeBlocks% "full/vectors/0100010-V-0005.bin"
private noncomputable def vp0100010_6 : Blocks := edgeBlocks% "full/vectors/0100010-V-0006.bin"
private noncomputable def vp0100010_7 : Blocks := edgeBlocks% "full/vectors/0100010-V-0007.bin"
private noncomputable def vp0100010_8 : Blocks := edgeBlocks% "full/vectors/0100010-V-0008.bin"
private noncomputable def vp0100010_9 : Blocks := edgeBlocks% "full/vectors/0100010-V-0009.bin"
private noncomputable def vp0100010_10 : Blocks := edgeBlocks% "full/vectors/0100010-V-0010.bin"
noncomputable def vp0100010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0100010_0 vp0100010_1) (Blocks.join vp0100010_2 (Blocks.join vp0100010_3 vp0100010_4))) (Blocks.join (Blocks.join vp0100010_5 (Blocks.join vp0100010_6 vp0100010_7)) (Blocks.join vp0100010_8 (Blocks.join vp0100010_9 vp0100010_10))))
private theorem bp01000100 : Branch 0 (-2175761639/64000000 : ℚ) vp0100010 := by
  apply branch_left_normalized (c:=vp01000100) (k:=0) (m:=684) (by decide +kernel)
  rw [show 2*(-2175761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-2175761639/32000000 : ℚ) by norm_num]
  exact coverp01000100
private noncomputable def ep01000101_0 : Blocks := edgeBlocks% "full/vectors/01000101-E-0000.bin"
private noncomputable def ep01000101_1 : Blocks := edgeBlocks% "full/vectors/01000101-E-0001.bin"
private noncomputable def ep01000101_2 : Blocks := edgeBlocks% "full/vectors/01000101-E-0002.bin"
private noncomputable def ep01000101_3 : Blocks := edgeBlocks% "full/vectors/01000101-E-0003.bin"
private noncomputable def ep01000101_4 : Blocks := edgeBlocks% "full/vectors/01000101-E-0004.bin"
private noncomputable def ep01000101_5 : Blocks := edgeBlocks% "full/vectors/01000101-E-0005.bin"
private noncomputable def ep01000101_6 : Blocks := edgeBlocks% "full/vectors/01000101-E-0006.bin"
private noncomputable def ep01000101_7 : Blocks := edgeBlocks% "full/vectors/01000101-E-0007.bin"
private noncomputable def ep01000101_8 : Blocks := edgeBlocks% "full/vectors/01000101-E-0008.bin"
private noncomputable def ep01000101_9 : Blocks := edgeBlocks% "full/vectors/01000101-E-0009.bin"
private noncomputable def ep01000101_10 : Blocks := edgeBlocks% "full/vectors/01000101-E-0010.bin"
noncomputable def ep01000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01000101_0 ep01000101_1) (Blocks.join ep01000101_2 (Blocks.join ep01000101_3 ep01000101_4))) (Blocks.join (Blocks.join ep01000101_5 (Blocks.join ep01000101_6 ep01000101_7)) (Blocks.join ep01000101_8 (Blocks.join ep01000101_9 ep01000101_10))))
private theorem idp01000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0100010.list =
    C ((2:ℤ)^1515) * horner X vp01000101.list + horner X ep01000101.list := by
  exact edge_identity (B := (2:ℤ)^2140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01000101 : Branch 1 (-2175761639/64000000 : ℚ) vp0100010 := by
  apply branch_checked idp01000101 (by positivity) (by decide +kernel)
  rw [show 2*(-2175761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2207761639/32000000 : ℚ) by norm_num]
  exact coverp01000101
theorem coverp0100010 : Covers (-2175761639/64000000 : ℚ) vp0100010 := join_branches bp01000100 bp01000101
private noncomputable def vp010001_0 : Blocks := edgeBlocks% "full/vectors/010001-V-0000.bin"
private noncomputable def vp010001_1 : Blocks := edgeBlocks% "full/vectors/010001-V-0001.bin"
private noncomputable def vp010001_2 : Blocks := edgeBlocks% "full/vectors/010001-V-0002.bin"
private noncomputable def vp010001_3 : Blocks := edgeBlocks% "full/vectors/010001-V-0003.bin"
private noncomputable def vp010001_4 : Blocks := edgeBlocks% "full/vectors/010001-V-0004.bin"
private noncomputable def vp010001_5 : Blocks := edgeBlocks% "full/vectors/010001-V-0005.bin"
private noncomputable def vp010001_6 : Blocks := edgeBlocks% "full/vectors/010001-V-0006.bin"
private noncomputable def vp010001_7 : Blocks := edgeBlocks% "full/vectors/010001-V-0007.bin"
private noncomputable def vp010001_8 : Blocks := edgeBlocks% "full/vectors/010001-V-0008.bin"
private noncomputable def vp010001_9 : Blocks := edgeBlocks% "full/vectors/010001-V-0009.bin"
private noncomputable def vp010001_10 : Blocks := edgeBlocks% "full/vectors/010001-V-0010.bin"
private noncomputable def vp010001_11 : Blocks := edgeBlocks% "full/vectors/010001-V-0011.bin"
private noncomputable def vp010001_12 : Blocks := edgeBlocks% "full/vectors/010001-V-0012.bin"
private noncomputable def vp010001_13 : Blocks := edgeBlocks% "full/vectors/010001-V-0013.bin"
private noncomputable def vp010001_14 : Blocks := edgeBlocks% "full/vectors/010001-V-0014.bin"
private noncomputable def vp010001_15 : Blocks := edgeBlocks% "full/vectors/010001-V-0015.bin"
private noncomputable def vp010001_16 : Blocks := edgeBlocks% "full/vectors/010001-V-0016.bin"
private noncomputable def vp010001_17 : Blocks := edgeBlocks% "full/vectors/010001-V-0017.bin"
private noncomputable def vp010001_18 : Blocks := edgeBlocks% "full/vectors/010001-V-0018.bin"
private noncomputable def vp010001_19 : Blocks := edgeBlocks% "full/vectors/010001-V-0019.bin"
private noncomputable def vp010001_20 : Blocks := edgeBlocks% "full/vectors/010001-V-0020.bin"
noncomputable def vp010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp010001_0 vp010001_1) (Blocks.join vp010001_2 (Blocks.join vp010001_3 vp010001_4))) (Blocks.join (Blocks.join vp010001_5 vp010001_6) (Blocks.join vp010001_7 (Blocks.join vp010001_8 vp010001_9)))) (Blocks.join (Blocks.join (Blocks.join vp010001_10 vp010001_11) (Blocks.join vp010001_12 (Blocks.join vp010001_13 vp010001_14))) (Blocks.join (Blocks.join vp010001_15 (Blocks.join vp010001_16 vp010001_17)) (Blocks.join vp010001_18 (Blocks.join vp010001_19 vp010001_20)))))
private theorem bp0100010 : Branch 0 (-2175761639/128000000 : ℚ) vp010001 := by
  apply branch_left_normalized (c:=vp0100010) (k:=0) (m:=1337) (by decide +kernel)
  rw [show 2*(-2175761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-2175761639/64000000 : ℚ) by norm_num]
  exact coverp0100010
private noncomputable def ep0100011_0 : Blocks := edgeBlocks% "full/vectors/0100011-E-0000.bin"
private noncomputable def ep0100011_1 : Blocks := edgeBlocks% "full/vectors/0100011-E-0001.bin"
private noncomputable def ep0100011_2 : Blocks := edgeBlocks% "full/vectors/0100011-E-0002.bin"
private noncomputable def ep0100011_3 : Blocks := edgeBlocks% "full/vectors/0100011-E-0003.bin"
private noncomputable def ep0100011_4 : Blocks := edgeBlocks% "full/vectors/0100011-E-0004.bin"
private noncomputable def ep0100011_5 : Blocks := edgeBlocks% "full/vectors/0100011-E-0005.bin"
private noncomputable def ep0100011_6 : Blocks := edgeBlocks% "full/vectors/0100011-E-0006.bin"
private noncomputable def ep0100011_7 : Blocks := edgeBlocks% "full/vectors/0100011-E-0007.bin"
private noncomputable def ep0100011_8 : Blocks := edgeBlocks% "full/vectors/0100011-E-0008.bin"
private noncomputable def ep0100011_9 : Blocks := edgeBlocks% "full/vectors/0100011-E-0009.bin"
private noncomputable def ep0100011_10 : Blocks := edgeBlocks% "full/vectors/0100011-E-0010.bin"
private noncomputable def ep0100011_11 : Blocks := edgeBlocks% "full/vectors/0100011-E-0011.bin"
private noncomputable def ep0100011_12 : Blocks := edgeBlocks% "full/vectors/0100011-E-0012.bin"
private noncomputable def ep0100011_13 : Blocks := edgeBlocks% "full/vectors/0100011-E-0013.bin"
private noncomputable def ep0100011_14 : Blocks := edgeBlocks% "full/vectors/0100011-E-0014.bin"
private noncomputable def ep0100011_15 : Blocks := edgeBlocks% "full/vectors/0100011-E-0015.bin"
private noncomputable def ep0100011_16 : Blocks := edgeBlocks% "full/vectors/0100011-E-0016.bin"
private noncomputable def ep0100011_17 : Blocks := edgeBlocks% "full/vectors/0100011-E-0017.bin"
private noncomputable def ep0100011_18 : Blocks := edgeBlocks% "full/vectors/0100011-E-0018.bin"
private noncomputable def ep0100011_19 : Blocks := edgeBlocks% "full/vectors/0100011-E-0019.bin"
private noncomputable def ep0100011_20 : Blocks := edgeBlocks% "full/vectors/0100011-E-0020.bin"
noncomputable def ep0100011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0100011_0 ep0100011_1) (Blocks.join ep0100011_2 (Blocks.join ep0100011_3 ep0100011_4))) (Blocks.join (Blocks.join ep0100011_5 ep0100011_6) (Blocks.join ep0100011_7 (Blocks.join ep0100011_8 ep0100011_9)))) (Blocks.join (Blocks.join (Blocks.join ep0100011_10 ep0100011_11) (Blocks.join ep0100011_12 (Blocks.join ep0100011_13 ep0100011_14))) (Blocks.join (Blocks.join ep0100011_15 (Blocks.join ep0100011_16 ep0100011_17)) (Blocks.join ep0100011_18 (Blocks.join ep0100011_19 ep0100011_20)))))
private theorem idp0100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp010001.list =
    C ((2:ℤ)^2964) * horner X vp0100011.list + horner X ep0100011.list := by
  exact edge_identity (B := (2:ℤ)^4108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0100011 : Branch 1 (-2175761639/128000000 : ℚ) vp010001 := by
  apply branch_checked idp0100011 (by positivity) (by decide +kernel)
  rw [show 2*(-2175761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-2239761639/64000000 : ℚ) by norm_num]
  exact coverp0100011
theorem coverp010001 : Covers (-2175761639/128000000 : ℚ) vp010001 := join_branches bp0100010 bp0100011
end NextProof.EdgeFull

