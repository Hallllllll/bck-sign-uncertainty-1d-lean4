import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00010101111111_0 : Blocks := edgeBlocks% "full/vectors/00010101111111-V-0000.bin"
noncomputable def vp00010101111111 : Blocks := vp00010101111111_0
theorem coverp00010101111111 : Covers (-703261639/500000 : ℚ) vp00010101111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101111110_0 : Blocks := edgeBlocks% "full/vectors/00010101111110-V-0000.bin"
noncomputable def vp00010101111110 : Blocks := vp00010101111110_0
theorem coverp00010101111110 : Covers (-702761639/500000 : ℚ) vp00010101111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010111111_0 : Blocks := edgeBlocks% "full/vectors/0001010111111-V-0000.bin"
noncomputable def vp0001010111111 : Blocks := vp0001010111111_0
private theorem bp00010101111110 : Branch 0 (-702761639/1000000 : ℚ) vp0001010111111 := by
  apply branch_left_normalized (c:=vp00010101111110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-702761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-702761639/500000 : ℚ) by norm_num]
  exact coverp00010101111110
private noncomputable def ep00010101111111_0 : Blocks := edgeBlocks% "full/vectors/00010101111111-E-0000.bin"
noncomputable def ep00010101111111 : Blocks := ep00010101111111_0
private theorem idp00010101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010111111.list =
    C ((2:ℤ)^61) * horner X vp00010101111111.list + horner X ep00010101111111.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101111111 : Branch 1 (-702761639/1000000 : ℚ) vp0001010111111 := by
  apply branch_checked idp00010101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-702761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-703261639/500000 : ℚ) by norm_num]
  exact coverp00010101111111
theorem coverp0001010111111 : Covers (-702761639/1000000 : ℚ) vp0001010111111 := join_branches bp00010101111110 bp00010101111111
private noncomputable def vp00010101111101_0 : Blocks := edgeBlocks% "full/vectors/00010101111101-V-0000.bin"
noncomputable def vp00010101111101 : Blocks := vp00010101111101_0
theorem coverp00010101111101 : Covers (-702261639/500000 : ℚ) vp00010101111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101111100_0 : Blocks := edgeBlocks% "full/vectors/00010101111100-V-0000.bin"
noncomputable def vp00010101111100 : Blocks := vp00010101111100_0
theorem coverp00010101111100 : Covers (-701761639/500000 : ℚ) vp00010101111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010111110_0 : Blocks := edgeBlocks% "full/vectors/0001010111110-V-0000.bin"
noncomputable def vp0001010111110 : Blocks := vp0001010111110_0
private theorem bp00010101111100 : Branch 0 (-701761639/1000000 : ℚ) vp0001010111110 := by
  apply branch_left_normalized (c:=vp00010101111100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-701761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-701761639/500000 : ℚ) by norm_num]
  exact coverp00010101111100
private noncomputable def ep00010101111101_0 : Blocks := edgeBlocks% "full/vectors/00010101111101-E-0000.bin"
noncomputable def ep00010101111101 : Blocks := ep00010101111101_0
private theorem idp00010101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010111110.list =
    C ((2:ℤ)^60) * horner X vp00010101111101.list + horner X ep00010101111101.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101111101 : Branch 1 (-701761639/1000000 : ℚ) vp0001010111110 := by
  apply branch_checked idp00010101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-701761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-702261639/500000 : ℚ) by norm_num]
  exact coverp00010101111101
theorem coverp0001010111110 : Covers (-701761639/1000000 : ℚ) vp0001010111110 := join_branches bp00010101111100 bp00010101111101
private noncomputable def vp000101011111_0 : Blocks := edgeBlocks% "full/vectors/000101011111-V-0000.bin"
noncomputable def vp000101011111 : Blocks := vp000101011111_0
private theorem bp0001010111110 : Branch 0 (-701761639/2000000 : ℚ) vp000101011111 := by
  apply branch_left_normalized (c:=vp0001010111110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-701761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-701761639/1000000 : ℚ) by norm_num]
  exact coverp0001010111110
private noncomputable def ep0001010111111_0 : Blocks := edgeBlocks% "full/vectors/0001010111111-E-0000.bin"
noncomputable def ep0001010111111 : Blocks := ep0001010111111_0
private theorem idp0001010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101011111.list =
    C ((2:ℤ)^101) * horner X vp0001010111111.list + horner X ep0001010111111.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010111111 : Branch 1 (-701761639/2000000 : ℚ) vp000101011111 := by
  apply branch_checked idp0001010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-701761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-702761639/1000000 : ℚ) by norm_num]
  exact coverp0001010111111
theorem coverp000101011111 : Covers (-701761639/2000000 : ℚ) vp000101011111 := join_branches bp0001010111110 bp0001010111111
private noncomputable def vp00010101111011_0 : Blocks := edgeBlocks% "full/vectors/00010101111011-V-0000.bin"
noncomputable def vp00010101111011 : Blocks := vp00010101111011_0
theorem coverp00010101111011 : Covers (-701261639/500000 : ℚ) vp00010101111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101111010_0 : Blocks := edgeBlocks% "full/vectors/00010101111010-V-0000.bin"
noncomputable def vp00010101111010 : Blocks := vp00010101111010_0
theorem coverp00010101111010 : Covers (-700761639/500000 : ℚ) vp00010101111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010111101_0 : Blocks := edgeBlocks% "full/vectors/0001010111101-V-0000.bin"
noncomputable def vp0001010111101 : Blocks := vp0001010111101_0
private theorem bp00010101111010 : Branch 0 (-700761639/1000000 : ℚ) vp0001010111101 := by
  apply branch_left_normalized (c:=vp00010101111010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-700761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-700761639/500000 : ℚ) by norm_num]
  exact coverp00010101111010
private noncomputable def ep00010101111011_0 : Blocks := edgeBlocks% "full/vectors/00010101111011-E-0000.bin"
noncomputable def ep00010101111011 : Blocks := ep00010101111011_0
private theorem idp00010101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010111101.list =
    C ((2:ℤ)^61) * horner X vp00010101111011.list + horner X ep00010101111011.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101111011 : Branch 1 (-700761639/1000000 : ℚ) vp0001010111101 := by
  apply branch_checked idp00010101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-700761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-701261639/500000 : ℚ) by norm_num]
  exact coverp00010101111011
theorem coverp0001010111101 : Covers (-700761639/1000000 : ℚ) vp0001010111101 := join_branches bp00010101111010 bp00010101111011
private noncomputable def vp00010101111001_0 : Blocks := edgeBlocks% "full/vectors/00010101111001-V-0000.bin"
noncomputable def vp00010101111001 : Blocks := vp00010101111001_0
theorem coverp00010101111001 : Covers (-700261639/500000 : ℚ) vp00010101111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101111000_0 : Blocks := edgeBlocks% "full/vectors/00010101111000-V-0000.bin"
noncomputable def vp00010101111000 : Blocks := vp00010101111000_0
theorem coverp00010101111000 : Covers (-699761639/500000 : ℚ) vp00010101111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010111100_0 : Blocks := edgeBlocks% "full/vectors/0001010111100-V-0000.bin"
noncomputable def vp0001010111100 : Blocks := vp0001010111100_0
private theorem bp00010101111000 : Branch 0 (-699761639/1000000 : ℚ) vp0001010111100 := by
  apply branch_left_normalized (c:=vp00010101111000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-699761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-699761639/500000 : ℚ) by norm_num]
  exact coverp00010101111000
private noncomputable def ep00010101111001_0 : Blocks := edgeBlocks% "full/vectors/00010101111001-E-0000.bin"
noncomputable def ep00010101111001 : Blocks := ep00010101111001_0
private theorem idp00010101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010111100.list =
    C ((2:ℤ)^61) * horner X vp00010101111001.list + horner X ep00010101111001.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101111001 : Branch 1 (-699761639/1000000 : ℚ) vp0001010111100 := by
  apply branch_checked idp00010101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-699761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-700261639/500000 : ℚ) by norm_num]
  exact coverp00010101111001
theorem coverp0001010111100 : Covers (-699761639/1000000 : ℚ) vp0001010111100 := join_branches bp00010101111000 bp00010101111001
private noncomputable def vp000101011110_0 : Blocks := edgeBlocks% "full/vectors/000101011110-V-0000.bin"
noncomputable def vp000101011110 : Blocks := vp000101011110_0
private theorem bp0001010111100 : Branch 0 (-699761639/2000000 : ℚ) vp000101011110 := by
  apply branch_left_normalized (c:=vp0001010111100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-699761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-699761639/1000000 : ℚ) by norm_num]
  exact coverp0001010111100
private noncomputable def ep0001010111101_0 : Blocks := edgeBlocks% "full/vectors/0001010111101-E-0000.bin"
noncomputable def ep0001010111101 : Blocks := ep0001010111101_0
private theorem idp0001010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101011110.list =
    C ((2:ℤ)^102) * horner X vp0001010111101.list + horner X ep0001010111101.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010111101 : Branch 1 (-699761639/2000000 : ℚ) vp000101011110 := by
  apply branch_checked idp0001010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-699761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-700761639/1000000 : ℚ) by norm_num]
  exact coverp0001010111101
theorem coverp000101011110 : Covers (-699761639/2000000 : ℚ) vp000101011110 := join_branches bp0001010111100 bp0001010111101
private noncomputable def vp00010101111_0 : Blocks := edgeBlocks% "full/vectors/00010101111-V-0000.bin"
private noncomputable def vp00010101111_1 : Blocks := edgeBlocks% "full/vectors/00010101111-V-0001.bin"
noncomputable def vp00010101111 : Blocks := (Blocks.join vp00010101111_0 vp00010101111_1)
private theorem bp000101011110 : Branch 0 (-699761639/4000000 : ℚ) vp00010101111 := by
  apply branch_left_normalized (c:=vp000101011110) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-699761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-699761639/2000000 : ℚ) by norm_num]
  exact coverp000101011110
private noncomputable def ep000101011111_0 : Blocks := edgeBlocks% "full/vectors/000101011111-E-0000.bin"
private noncomputable def ep000101011111_1 : Blocks := edgeBlocks% "full/vectors/000101011111-E-0001.bin"
noncomputable def ep000101011111 : Blocks := (Blocks.join ep000101011111_0 ep000101011111_1)
private theorem idp000101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010101111.list =
    C ((2:ℤ)^183) * horner X vp000101011111.list + horner X ep000101011111.list := by
  exact edge_identity (B := (2:ℤ)^351) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101011111 : Branch 1 (-699761639/4000000 : ℚ) vp00010101111 := by
  apply branch_checked idp000101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-699761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-701761639/2000000 : ℚ) by norm_num]
  exact coverp000101011111
theorem coverp00010101111 : Covers (-699761639/4000000 : ℚ) vp00010101111 := join_branches bp000101011110 bp000101011111
private noncomputable def vp00010101110111_0 : Blocks := edgeBlocks% "full/vectors/00010101110111-V-0000.bin"
noncomputable def vp00010101110111 : Blocks := vp00010101110111_0
theorem coverp00010101110111 : Covers (-699261639/500000 : ℚ) vp00010101110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101110110_0 : Blocks := edgeBlocks% "full/vectors/00010101110110-V-0000.bin"
noncomputable def vp00010101110110 : Blocks := vp00010101110110_0
theorem coverp00010101110110 : Covers (-698761639/500000 : ℚ) vp00010101110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010111011_0 : Blocks := edgeBlocks% "full/vectors/0001010111011-V-0000.bin"
noncomputable def vp0001010111011 : Blocks := vp0001010111011_0
private theorem bp00010101110110 : Branch 0 (-698761639/1000000 : ℚ) vp0001010111011 := by
  apply branch_left_normalized (c:=vp00010101110110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-698761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-698761639/500000 : ℚ) by norm_num]
  exact coverp00010101110110
private noncomputable def ep00010101110111_0 : Blocks := edgeBlocks% "full/vectors/00010101110111-E-0000.bin"
noncomputable def ep00010101110111 : Blocks := ep00010101110111_0
private theorem idp00010101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010111011.list =
    C ((2:ℤ)^60) * horner X vp00010101110111.list + horner X ep00010101110111.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101110111 : Branch 1 (-698761639/1000000 : ℚ) vp0001010111011 := by
  apply branch_checked idp00010101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-698761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-699261639/500000 : ℚ) by norm_num]
  exact coverp00010101110111
theorem coverp0001010111011 : Covers (-698761639/1000000 : ℚ) vp0001010111011 := join_branches bp00010101110110 bp00010101110111
private noncomputable def vp00010101110101_0 : Blocks := edgeBlocks% "full/vectors/00010101110101-V-0000.bin"
noncomputable def vp00010101110101 : Blocks := vp00010101110101_0
theorem coverp00010101110101 : Covers (-698261639/500000 : ℚ) vp00010101110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101110100_0 : Blocks := edgeBlocks% "full/vectors/00010101110100-V-0000.bin"
noncomputable def vp00010101110100 : Blocks := vp00010101110100_0
theorem coverp00010101110100 : Covers (-697761639/500000 : ℚ) vp00010101110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010111010_0 : Blocks := edgeBlocks% "full/vectors/0001010111010-V-0000.bin"
noncomputable def vp0001010111010 : Blocks := vp0001010111010_0
private theorem bp00010101110100 : Branch 0 (-697761639/1000000 : ℚ) vp0001010111010 := by
  apply branch_left_normalized (c:=vp00010101110100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-697761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-697761639/500000 : ℚ) by norm_num]
  exact coverp00010101110100
private noncomputable def ep00010101110101_0 : Blocks := edgeBlocks% "full/vectors/00010101110101-E-0000.bin"
noncomputable def ep00010101110101 : Blocks := ep00010101110101_0
private theorem idp00010101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010111010.list =
    C ((2:ℤ)^60) * horner X vp00010101110101.list + horner X ep00010101110101.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101110101 : Branch 1 (-697761639/1000000 : ℚ) vp0001010111010 := by
  apply branch_checked idp00010101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-697761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-698261639/500000 : ℚ) by norm_num]
  exact coverp00010101110101
theorem coverp0001010111010 : Covers (-697761639/1000000 : ℚ) vp0001010111010 := join_branches bp00010101110100 bp00010101110101
private noncomputable def vp000101011101_0 : Blocks := edgeBlocks% "full/vectors/000101011101-V-0000.bin"
noncomputable def vp000101011101 : Blocks := vp000101011101_0
private theorem bp0001010111010 : Branch 0 (-697761639/2000000 : ℚ) vp000101011101 := by
  apply branch_left_normalized (c:=vp0001010111010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-697761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-697761639/1000000 : ℚ) by norm_num]
  exact coverp0001010111010
private noncomputable def ep0001010111011_0 : Blocks := edgeBlocks% "full/vectors/0001010111011-E-0000.bin"
noncomputable def ep0001010111011 : Blocks := ep0001010111011_0
private theorem idp0001010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101011101.list =
    C ((2:ℤ)^102) * horner X vp0001010111011.list + horner X ep0001010111011.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010111011 : Branch 1 (-697761639/2000000 : ℚ) vp000101011101 := by
  apply branch_checked idp0001010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-697761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-698761639/1000000 : ℚ) by norm_num]
  exact coverp0001010111011
theorem coverp000101011101 : Covers (-697761639/2000000 : ℚ) vp000101011101 := join_branches bp0001010111010 bp0001010111011
private noncomputable def vp00010101110011_0 : Blocks := edgeBlocks% "full/vectors/00010101110011-V-0000.bin"
noncomputable def vp00010101110011 : Blocks := vp00010101110011_0
theorem coverp00010101110011 : Covers (-697261639/500000 : ℚ) vp00010101110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101110010_0 : Blocks := edgeBlocks% "full/vectors/00010101110010-V-0000.bin"
noncomputable def vp00010101110010 : Blocks := vp00010101110010_0
theorem coverp00010101110010 : Covers (-696761639/500000 : ℚ) vp00010101110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010111001_0 : Blocks := edgeBlocks% "full/vectors/0001010111001-V-0000.bin"
noncomputable def vp0001010111001 : Blocks := vp0001010111001_0
private theorem bp00010101110010 : Branch 0 (-696761639/1000000 : ℚ) vp0001010111001 := by
  apply branch_left_normalized (c:=vp00010101110010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-696761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-696761639/500000 : ℚ) by norm_num]
  exact coverp00010101110010
private noncomputable def ep00010101110011_0 : Blocks := edgeBlocks% "full/vectors/00010101110011-E-0000.bin"
noncomputable def ep00010101110011 : Blocks := ep00010101110011_0
private theorem idp00010101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010111001.list =
    C ((2:ℤ)^61) * horner X vp00010101110011.list + horner X ep00010101110011.list := by
  exact edge_identity (B := (2:ℤ)^180) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101110011 : Branch 1 (-696761639/1000000 : ℚ) vp0001010111001 := by
  apply branch_checked idp00010101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-696761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-697261639/500000 : ℚ) by norm_num]
  exact coverp00010101110011
theorem coverp0001010111001 : Covers (-696761639/1000000 : ℚ) vp0001010111001 := join_branches bp00010101110010 bp00010101110011
private noncomputable def vp00010101110001_0 : Blocks := edgeBlocks% "full/vectors/00010101110001-V-0000.bin"
noncomputable def vp00010101110001 : Blocks := vp00010101110001_0
theorem coverp00010101110001 : Covers (-696261639/500000 : ℚ) vp00010101110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101110000_0 : Blocks := edgeBlocks% "full/vectors/00010101110000-V-0000.bin"
noncomputable def vp00010101110000 : Blocks := vp00010101110000_0
theorem coverp00010101110000 : Covers (-695761639/500000 : ℚ) vp00010101110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010111000_0 : Blocks := edgeBlocks% "full/vectors/0001010111000-V-0000.bin"
noncomputable def vp0001010111000 : Blocks := vp0001010111000_0
private theorem bp00010101110000 : Branch 0 (-695761639/1000000 : ℚ) vp0001010111000 := by
  apply branch_left_normalized (c:=vp00010101110000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-695761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-695761639/500000 : ℚ) by norm_num]
  exact coverp00010101110000
private noncomputable def ep00010101110001_0 : Blocks := edgeBlocks% "full/vectors/00010101110001-E-0000.bin"
noncomputable def ep00010101110001 : Blocks := ep00010101110001_0
private theorem idp00010101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010111000.list =
    C ((2:ℤ)^61) * horner X vp00010101110001.list + horner X ep00010101110001.list := by
  exact edge_identity (B := (2:ℤ)^180) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101110001 : Branch 1 (-695761639/1000000 : ℚ) vp0001010111000 := by
  apply branch_checked idp00010101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-695761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-696261639/500000 : ℚ) by norm_num]
  exact coverp00010101110001
theorem coverp0001010111000 : Covers (-695761639/1000000 : ℚ) vp0001010111000 := join_branches bp00010101110000 bp00010101110001
private noncomputable def vp000101011100_0 : Blocks := edgeBlocks% "full/vectors/000101011100-V-0000.bin"
noncomputable def vp000101011100 : Blocks := vp000101011100_0
private theorem bp0001010111000 : Branch 0 (-695761639/2000000 : ℚ) vp000101011100 := by
  apply branch_left_normalized (c:=vp0001010111000) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-695761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-695761639/1000000 : ℚ) by norm_num]
  exact coverp0001010111000
private noncomputable def ep0001010111001_0 : Blocks := edgeBlocks% "full/vectors/0001010111001-E-0000.bin"
noncomputable def ep0001010111001 : Blocks := ep0001010111001_0
private theorem idp0001010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101011100.list =
    C ((2:ℤ)^103) * horner X vp0001010111001.list + horner X ep0001010111001.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010111001 : Branch 1 (-695761639/2000000 : ℚ) vp000101011100 := by
  apply branch_checked idp0001010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-695761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-696761639/1000000 : ℚ) by norm_num]
  exact coverp0001010111001
theorem coverp000101011100 : Covers (-695761639/2000000 : ℚ) vp000101011100 := join_branches bp0001010111000 bp0001010111001
private noncomputable def vp00010101110_0 : Blocks := edgeBlocks% "full/vectors/00010101110-V-0000.bin"
private noncomputable def vp00010101110_1 : Blocks := edgeBlocks% "full/vectors/00010101110-V-0001.bin"
noncomputable def vp00010101110 : Blocks := (Blocks.join vp00010101110_0 vp00010101110_1)
private theorem bp000101011100 : Branch 0 (-695761639/4000000 : ℚ) vp00010101110 := by
  apply branch_left_normalized (c:=vp000101011100) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-695761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-695761639/2000000 : ℚ) by norm_num]
  exact coverp000101011100
private noncomputable def ep000101011101_0 : Blocks := edgeBlocks% "full/vectors/000101011101-E-0000.bin"
private noncomputable def ep000101011101_1 : Blocks := edgeBlocks% "full/vectors/000101011101-E-0001.bin"
noncomputable def ep000101011101 : Blocks := (Blocks.join ep000101011101_0 ep000101011101_1)
private theorem idp000101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010101110.list =
    C ((2:ℤ)^184) * horner X vp000101011101.list + horner X ep000101011101.list := by
  exact edge_identity (B := (2:ℤ)^353) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101011101 : Branch 1 (-695761639/4000000 : ℚ) vp00010101110 := by
  apply branch_checked idp000101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-695761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-697761639/2000000 : ℚ) by norm_num]
  exact coverp000101011101
theorem coverp00010101110 : Covers (-695761639/4000000 : ℚ) vp00010101110 := join_branches bp000101011100 bp000101011101
private noncomputable def vp0001010111_0 : Blocks := edgeBlocks% "full/vectors/0001010111-V-0000.bin"
private noncomputable def vp0001010111_1 : Blocks := edgeBlocks% "full/vectors/0001010111-V-0001.bin"
private noncomputable def vp0001010111_2 : Blocks := edgeBlocks% "full/vectors/0001010111-V-0002.bin"
noncomputable def vp0001010111 : Blocks := (Blocks.join vp0001010111_0 (Blocks.join vp0001010111_1 vp0001010111_2))
private theorem bp00010101110 : Branch 0 (-695761639/8000000 : ℚ) vp0001010111 := by
  apply branch_left_normalized (c:=vp00010101110) (k:=0) (m:=171) (by decide +kernel)
  rw [show 2*(-695761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-695761639/4000000 : ℚ) by norm_num]
  exact coverp00010101110
private noncomputable def ep00010101111_0 : Blocks := edgeBlocks% "full/vectors/00010101111-E-0000.bin"
private noncomputable def ep00010101111_1 : Blocks := edgeBlocks% "full/vectors/00010101111-E-0001.bin"
private noncomputable def ep00010101111_2 : Blocks := edgeBlocks% "full/vectors/00010101111-E-0002.bin"
noncomputable def ep00010101111 : Blocks := (Blocks.join ep00010101111_0 (Blocks.join ep00010101111_1 ep00010101111_2))
private theorem idp00010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010111.list =
    C ((2:ℤ)^345) * horner X vp00010101111.list + horner X ep00010101111.list := by
  exact edge_identity (B := (2:ℤ)^581) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101111 : Branch 1 (-695761639/8000000 : ℚ) vp0001010111 := by
  apply branch_checked idp00010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-695761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-699761639/4000000 : ℚ) by norm_num]
  exact coverp00010101111
theorem coverp0001010111 : Covers (-695761639/8000000 : ℚ) vp0001010111 := join_branches bp00010101110 bp00010101111
private noncomputable def vp00010101101111_0 : Blocks := edgeBlocks% "full/vectors/00010101101111-V-0000.bin"
noncomputable def vp00010101101111 : Blocks := vp00010101101111_0
theorem coverp00010101101111 : Covers (-695261639/500000 : ℚ) vp00010101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101101110_0 : Blocks := edgeBlocks% "full/vectors/00010101101110-V-0000.bin"
noncomputable def vp00010101101110 : Blocks := vp00010101101110_0
theorem coverp00010101101110 : Covers (-694761639/500000 : ℚ) vp00010101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010110111_0 : Blocks := edgeBlocks% "full/vectors/0001010110111-V-0000.bin"
noncomputable def vp0001010110111 : Blocks := vp0001010110111_0
private theorem bp00010101101110 : Branch 0 (-694761639/1000000 : ℚ) vp0001010110111 := by
  apply branch_left_normalized (c:=vp00010101101110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-694761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-694761639/500000 : ℚ) by norm_num]
  exact coverp00010101101110
private noncomputable def ep00010101101111_0 : Blocks := edgeBlocks% "full/vectors/00010101101111-E-0000.bin"
noncomputable def ep00010101101111 : Blocks := ep00010101101111_0
private theorem idp00010101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010110111.list =
    C ((2:ℤ)^61) * horner X vp00010101101111.list + horner X ep00010101101111.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101101111 : Branch 1 (-694761639/1000000 : ℚ) vp0001010110111 := by
  apply branch_checked idp00010101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-694761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-695261639/500000 : ℚ) by norm_num]
  exact coverp00010101101111
theorem coverp0001010110111 : Covers (-694761639/1000000 : ℚ) vp0001010110111 := join_branches bp00010101101110 bp00010101101111
private noncomputable def vp00010101101101_0 : Blocks := edgeBlocks% "full/vectors/00010101101101-V-0000.bin"
noncomputable def vp00010101101101 : Blocks := vp00010101101101_0
theorem coverp00010101101101 : Covers (-694261639/500000 : ℚ) vp00010101101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101101100_0 : Blocks := edgeBlocks% "full/vectors/00010101101100-V-0000.bin"
noncomputable def vp00010101101100 : Blocks := vp00010101101100_0
theorem coverp00010101101100 : Covers (-693761639/500000 : ℚ) vp00010101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010110110_0 : Blocks := edgeBlocks% "full/vectors/0001010110110-V-0000.bin"
noncomputable def vp0001010110110 : Blocks := vp0001010110110_0
private theorem bp00010101101100 : Branch 0 (-693761639/1000000 : ℚ) vp0001010110110 := by
  apply branch_left_normalized (c:=vp00010101101100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-693761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-693761639/500000 : ℚ) by norm_num]
  exact coverp00010101101100
private noncomputable def ep00010101101101_0 : Blocks := edgeBlocks% "full/vectors/00010101101101-E-0000.bin"
noncomputable def ep00010101101101 : Blocks := ep00010101101101_0
private theorem idp00010101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010110110.list =
    C ((2:ℤ)^60) * horner X vp00010101101101.list + horner X ep00010101101101.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101101101 : Branch 1 (-693761639/1000000 : ℚ) vp0001010110110 := by
  apply branch_checked idp00010101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-693761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-694261639/500000 : ℚ) by norm_num]
  exact coverp00010101101101
theorem coverp0001010110110 : Covers (-693761639/1000000 : ℚ) vp0001010110110 := join_branches bp00010101101100 bp00010101101101
private noncomputable def vp000101011011_0 : Blocks := edgeBlocks% "full/vectors/000101011011-V-0000.bin"
noncomputable def vp000101011011 : Blocks := vp000101011011_0
private theorem bp0001010110110 : Branch 0 (-693761639/2000000 : ℚ) vp000101011011 := by
  apply branch_left_normalized (c:=vp0001010110110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-693761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-693761639/1000000 : ℚ) by norm_num]
  exact coverp0001010110110
private noncomputable def ep0001010110111_0 : Blocks := edgeBlocks% "full/vectors/0001010110111-E-0000.bin"
noncomputable def ep0001010110111 : Blocks := ep0001010110111_0
private theorem idp0001010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101011011.list =
    C ((2:ℤ)^101) * horner X vp0001010110111.list + horner X ep0001010110111.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010110111 : Branch 1 (-693761639/2000000 : ℚ) vp000101011011 := by
  apply branch_checked idp0001010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-693761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-694761639/1000000 : ℚ) by norm_num]
  exact coverp0001010110111
theorem coverp000101011011 : Covers (-693761639/2000000 : ℚ) vp000101011011 := join_branches bp0001010110110 bp0001010110111
private noncomputable def vp00010101101011_0 : Blocks := edgeBlocks% "full/vectors/00010101101011-V-0000.bin"
noncomputable def vp00010101101011 : Blocks := vp00010101101011_0
theorem coverp00010101101011 : Covers (-693261639/500000 : ℚ) vp00010101101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101101010_0 : Blocks := edgeBlocks% "full/vectors/00010101101010-V-0000.bin"
noncomputable def vp00010101101010 : Blocks := vp00010101101010_0
theorem coverp00010101101010 : Covers (-692761639/500000 : ℚ) vp00010101101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010110101_0 : Blocks := edgeBlocks% "full/vectors/0001010110101-V-0000.bin"
noncomputable def vp0001010110101 : Blocks := vp0001010110101_0
private theorem bp00010101101010 : Branch 0 (-692761639/1000000 : ℚ) vp0001010110101 := by
  apply branch_left_normalized (c:=vp00010101101010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-692761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-692761639/500000 : ℚ) by norm_num]
  exact coverp00010101101010
private noncomputable def ep00010101101011_0 : Blocks := edgeBlocks% "full/vectors/00010101101011-E-0000.bin"
noncomputable def ep00010101101011 : Blocks := ep00010101101011_0
private theorem idp00010101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010110101.list =
    C ((2:ℤ)^60) * horner X vp00010101101011.list + horner X ep00010101101011.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101101011 : Branch 1 (-692761639/1000000 : ℚ) vp0001010110101 := by
  apply branch_checked idp00010101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-692761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-693261639/500000 : ℚ) by norm_num]
  exact coverp00010101101011
theorem coverp0001010110101 : Covers (-692761639/1000000 : ℚ) vp0001010110101 := join_branches bp00010101101010 bp00010101101011
private noncomputable def vp00010101101001_0 : Blocks := edgeBlocks% "full/vectors/00010101101001-V-0000.bin"
noncomputable def vp00010101101001 : Blocks := vp00010101101001_0
theorem coverp00010101101001 : Covers (-692261639/500000 : ℚ) vp00010101101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101101000_0 : Blocks := edgeBlocks% "full/vectors/00010101101000-V-0000.bin"
noncomputable def vp00010101101000 : Blocks := vp00010101101000_0
theorem coverp00010101101000 : Covers (-691761639/500000 : ℚ) vp00010101101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010110100_0 : Blocks := edgeBlocks% "full/vectors/0001010110100-V-0000.bin"
noncomputable def vp0001010110100 : Blocks := vp0001010110100_0
private theorem bp00010101101000 : Branch 0 (-691761639/1000000 : ℚ) vp0001010110100 := by
  apply branch_left_normalized (c:=vp00010101101000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-691761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-691761639/500000 : ℚ) by norm_num]
  exact coverp00010101101000
private noncomputable def ep00010101101001_0 : Blocks := edgeBlocks% "full/vectors/00010101101001-E-0000.bin"
noncomputable def ep00010101101001 : Blocks := ep00010101101001_0
private theorem idp00010101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010110100.list =
    C ((2:ℤ)^60) * horner X vp00010101101001.list + horner X ep00010101101001.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101101001 : Branch 1 (-691761639/1000000 : ℚ) vp0001010110100 := by
  apply branch_checked idp00010101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-691761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-692261639/500000 : ℚ) by norm_num]
  exact coverp00010101101001
theorem coverp0001010110100 : Covers (-691761639/1000000 : ℚ) vp0001010110100 := join_branches bp00010101101000 bp00010101101001
private noncomputable def vp000101011010_0 : Blocks := edgeBlocks% "full/vectors/000101011010-V-0000.bin"
noncomputable def vp000101011010 : Blocks := vp000101011010_0
private theorem bp0001010110100 : Branch 0 (-691761639/2000000 : ℚ) vp000101011010 := by
  apply branch_left_normalized (c:=vp0001010110100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-691761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-691761639/1000000 : ℚ) by norm_num]
  exact coverp0001010110100
private noncomputable def ep0001010110101_0 : Blocks := edgeBlocks% "full/vectors/0001010110101-E-0000.bin"
noncomputable def ep0001010110101 : Blocks := ep0001010110101_0
private theorem idp0001010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101011010.list =
    C ((2:ℤ)^102) * horner X vp0001010110101.list + horner X ep0001010110101.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010110101 : Branch 1 (-691761639/2000000 : ℚ) vp000101011010 := by
  apply branch_checked idp0001010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-691761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-692761639/1000000 : ℚ) by norm_num]
  exact coverp0001010110101
theorem coverp000101011010 : Covers (-691761639/2000000 : ℚ) vp000101011010 := join_branches bp0001010110100 bp0001010110101
private noncomputable def vp00010101101_0 : Blocks := edgeBlocks% "full/vectors/00010101101-V-0000.bin"
private noncomputable def vp00010101101_1 : Blocks := edgeBlocks% "full/vectors/00010101101-V-0001.bin"
noncomputable def vp00010101101 : Blocks := (Blocks.join vp00010101101_0 vp00010101101_1)
private theorem bp000101011010 : Branch 0 (-691761639/4000000 : ℚ) vp00010101101 := by
  apply branch_left_normalized (c:=vp000101011010) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-691761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-691761639/2000000 : ℚ) by norm_num]
  exact coverp000101011010
private noncomputable def ep000101011011_0 : Blocks := edgeBlocks% "full/vectors/000101011011-E-0000.bin"
private noncomputable def ep000101011011_1 : Blocks := edgeBlocks% "full/vectors/000101011011-E-0001.bin"
noncomputable def ep000101011011 : Blocks := (Blocks.join ep000101011011_0 ep000101011011_1)
private theorem idp000101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010101101.list =
    C ((2:ℤ)^184) * horner X vp000101011011.list + horner X ep000101011011.list := by
  exact edge_identity (B := (2:ℤ)^352) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101011011 : Branch 1 (-691761639/4000000 : ℚ) vp00010101101 := by
  apply branch_checked idp000101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-691761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-693761639/2000000 : ℚ) by norm_num]
  exact coverp000101011011
theorem coverp00010101101 : Covers (-691761639/4000000 : ℚ) vp00010101101 := join_branches bp000101011010 bp000101011011
private noncomputable def vp00010101100111_0 : Blocks := edgeBlocks% "full/vectors/00010101100111-V-0000.bin"
noncomputable def vp00010101100111 : Blocks := vp00010101100111_0
theorem coverp00010101100111 : Covers (-691261639/500000 : ℚ) vp00010101100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101100110_0 : Blocks := edgeBlocks% "full/vectors/00010101100110-V-0000.bin"
noncomputable def vp00010101100110 : Blocks := vp00010101100110_0
theorem coverp00010101100110 : Covers (-690761639/500000 : ℚ) vp00010101100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010110011_0 : Blocks := edgeBlocks% "full/vectors/0001010110011-V-0000.bin"
noncomputable def vp0001010110011 : Blocks := vp0001010110011_0
private theorem bp00010101100110 : Branch 0 (-690761639/1000000 : ℚ) vp0001010110011 := by
  apply branch_left_normalized (c:=vp00010101100110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-690761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-690761639/500000 : ℚ) by norm_num]
  exact coverp00010101100110
private noncomputable def ep00010101100111_0 : Blocks := edgeBlocks% "full/vectors/00010101100111-E-0000.bin"
noncomputable def ep00010101100111 : Blocks := ep00010101100111_0
private theorem idp00010101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010110011.list =
    C ((2:ℤ)^61) * horner X vp00010101100111.list + horner X ep00010101100111.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101100111 : Branch 1 (-690761639/1000000 : ℚ) vp0001010110011 := by
  apply branch_checked idp00010101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-690761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-691261639/500000 : ℚ) by norm_num]
  exact coverp00010101100111
theorem coverp0001010110011 : Covers (-690761639/1000000 : ℚ) vp0001010110011 := join_branches bp00010101100110 bp00010101100111
private noncomputable def vp00010101100101_0 : Blocks := edgeBlocks% "full/vectors/00010101100101-V-0000.bin"
noncomputable def vp00010101100101 : Blocks := vp00010101100101_0
theorem coverp00010101100101 : Covers (-690261639/500000 : ℚ) vp00010101100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101100100_0 : Blocks := edgeBlocks% "full/vectors/00010101100100-V-0000.bin"
noncomputable def vp00010101100100 : Blocks := vp00010101100100_0
theorem coverp00010101100100 : Covers (-689761639/500000 : ℚ) vp00010101100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010110010_0 : Blocks := edgeBlocks% "full/vectors/0001010110010-V-0000.bin"
noncomputable def vp0001010110010 : Blocks := vp0001010110010_0
private theorem bp00010101100100 : Branch 0 (-689761639/1000000 : ℚ) vp0001010110010 := by
  apply branch_left_normalized (c:=vp00010101100100) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-689761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-689761639/500000 : ℚ) by norm_num]
  exact coverp00010101100100
private noncomputable def ep00010101100101_0 : Blocks := edgeBlocks% "full/vectors/00010101100101-E-0000.bin"
noncomputable def ep00010101100101 : Blocks := ep00010101100101_0
private theorem idp00010101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010110010.list =
    C ((2:ℤ)^61) * horner X vp00010101100101.list + horner X ep00010101100101.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101100101 : Branch 1 (-689761639/1000000 : ℚ) vp0001010110010 := by
  apply branch_checked idp00010101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-689761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-690261639/500000 : ℚ) by norm_num]
  exact coverp00010101100101
theorem coverp0001010110010 : Covers (-689761639/1000000 : ℚ) vp0001010110010 := join_branches bp00010101100100 bp00010101100101
private noncomputable def vp000101011001_0 : Blocks := edgeBlocks% "full/vectors/000101011001-V-0000.bin"
noncomputable def vp000101011001 : Blocks := vp000101011001_0
private theorem bp0001010110010 : Branch 0 (-689761639/2000000 : ℚ) vp000101011001 := by
  apply branch_left_normalized (c:=vp0001010110010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-689761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-689761639/1000000 : ℚ) by norm_num]
  exact coverp0001010110010
private noncomputable def ep0001010110011_0 : Blocks := edgeBlocks% "full/vectors/0001010110011-E-0000.bin"
noncomputable def ep0001010110011 : Blocks := ep0001010110011_0
private theorem idp0001010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101011001.list =
    C ((2:ℤ)^103) * horner X vp0001010110011.list + horner X ep0001010110011.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010110011 : Branch 1 (-689761639/2000000 : ℚ) vp000101011001 := by
  apply branch_checked idp0001010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-689761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-690761639/1000000 : ℚ) by norm_num]
  exact coverp0001010110011
theorem coverp000101011001 : Covers (-689761639/2000000 : ℚ) vp000101011001 := join_branches bp0001010110010 bp0001010110011
private noncomputable def vp00010101100011_0 : Blocks := edgeBlocks% "full/vectors/00010101100011-V-0000.bin"
noncomputable def vp00010101100011 : Blocks := vp00010101100011_0
theorem coverp00010101100011 : Covers (-689261639/500000 : ℚ) vp00010101100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101100010_0 : Blocks := edgeBlocks% "full/vectors/00010101100010-V-0000.bin"
noncomputable def vp00010101100010 : Blocks := vp00010101100010_0
theorem coverp00010101100010 : Covers (-688761639/500000 : ℚ) vp00010101100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010110001_0 : Blocks := edgeBlocks% "full/vectors/0001010110001-V-0000.bin"
noncomputable def vp0001010110001 : Blocks := vp0001010110001_0
private theorem bp00010101100010 : Branch 0 (-688761639/1000000 : ℚ) vp0001010110001 := by
  apply branch_left_normalized (c:=vp00010101100010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-688761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-688761639/500000 : ℚ) by norm_num]
  exact coverp00010101100010
private noncomputable def ep00010101100011_0 : Blocks := edgeBlocks% "full/vectors/00010101100011-E-0000.bin"
noncomputable def ep00010101100011 : Blocks := ep00010101100011_0
private theorem idp00010101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010110001.list =
    C ((2:ℤ)^60) * horner X vp00010101100011.list + horner X ep00010101100011.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101100011 : Branch 1 (-688761639/1000000 : ℚ) vp0001010110001 := by
  apply branch_checked idp00010101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-688761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-689261639/500000 : ℚ) by norm_num]
  exact coverp00010101100011
theorem coverp0001010110001 : Covers (-688761639/1000000 : ℚ) vp0001010110001 := join_branches bp00010101100010 bp00010101100011
private noncomputable def vp00010101100001_0 : Blocks := edgeBlocks% "full/vectors/00010101100001-V-0000.bin"
noncomputable def vp00010101100001 : Blocks := vp00010101100001_0
theorem coverp00010101100001 : Covers (-688261639/500000 : ℚ) vp00010101100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101100000_0 : Blocks := edgeBlocks% "full/vectors/00010101100000-V-0000.bin"
noncomputable def vp00010101100000 : Blocks := vp00010101100000_0
theorem coverp00010101100000 : Covers (-687761639/500000 : ℚ) vp00010101100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010110000_0 : Blocks := edgeBlocks% "full/vectors/0001010110000-V-0000.bin"
noncomputable def vp0001010110000 : Blocks := vp0001010110000_0
private theorem bp00010101100000 : Branch 0 (-687761639/1000000 : ℚ) vp0001010110000 := by
  apply branch_left_normalized (c:=vp00010101100000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-687761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-687761639/500000 : ℚ) by norm_num]
  exact coverp00010101100000
private noncomputable def ep00010101100001_0 : Blocks := edgeBlocks% "full/vectors/00010101100001-E-0000.bin"
noncomputable def ep00010101100001 : Blocks := ep00010101100001_0
private theorem idp00010101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010110000.list =
    C ((2:ℤ)^59) * horner X vp00010101100001.list + horner X ep00010101100001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101100001 : Branch 1 (-687761639/1000000 : ℚ) vp0001010110000 := by
  apply branch_checked idp00010101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-687761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-688261639/500000 : ℚ) by norm_num]
  exact coverp00010101100001
theorem coverp0001010110000 : Covers (-687761639/1000000 : ℚ) vp0001010110000 := join_branches bp00010101100000 bp00010101100001
private noncomputable def vp000101011000_0 : Blocks := edgeBlocks% "full/vectors/000101011000-V-0000.bin"
noncomputable def vp000101011000 : Blocks := vp000101011000_0
private theorem bp0001010110000 : Branch 0 (-687761639/2000000 : ℚ) vp000101011000 := by
  apply branch_left_normalized (c:=vp0001010110000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-687761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-687761639/1000000 : ℚ) by norm_num]
  exact coverp0001010110000
private noncomputable def ep0001010110001_0 : Blocks := edgeBlocks% "full/vectors/0001010110001-E-0000.bin"
noncomputable def ep0001010110001 : Blocks := ep0001010110001_0
private theorem idp0001010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101011000.list =
    C ((2:ℤ)^101) * horner X vp0001010110001.list + horner X ep0001010110001.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010110001 : Branch 1 (-687761639/2000000 : ℚ) vp000101011000 := by
  apply branch_checked idp0001010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-687761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-688761639/1000000 : ℚ) by norm_num]
  exact coverp0001010110001
theorem coverp000101011000 : Covers (-687761639/2000000 : ℚ) vp000101011000 := join_branches bp0001010110000 bp0001010110001
private noncomputable def vp00010101100_0 : Blocks := edgeBlocks% "full/vectors/00010101100-V-0000.bin"
private noncomputable def vp00010101100_1 : Blocks := edgeBlocks% "full/vectors/00010101100-V-0001.bin"
noncomputable def vp00010101100 : Blocks := (Blocks.join vp00010101100_0 vp00010101100_1)
private theorem bp000101011000 : Branch 0 (-687761639/4000000 : ℚ) vp00010101100 := by
  apply branch_left_normalized (c:=vp000101011000) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-687761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-687761639/2000000 : ℚ) by norm_num]
  exact coverp000101011000
private noncomputable def ep000101011001_0 : Blocks := edgeBlocks% "full/vectors/000101011001-E-0000.bin"
private noncomputable def ep000101011001_1 : Blocks := edgeBlocks% "full/vectors/000101011001-E-0001.bin"
noncomputable def ep000101011001 : Blocks := (Blocks.join ep000101011001_0 ep000101011001_1)
private theorem idp000101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010101100.list =
    C ((2:ℤ)^182) * horner X vp000101011001.list + horner X ep000101011001.list := by
  exact edge_identity (B := (2:ℤ)^352) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101011001 : Branch 1 (-687761639/4000000 : ℚ) vp00010101100 := by
  apply branch_checked idp000101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-687761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-689761639/2000000 : ℚ) by norm_num]
  exact coverp000101011001
theorem coverp00010101100 : Covers (-687761639/4000000 : ℚ) vp00010101100 := join_branches bp000101011000 bp000101011001
private noncomputable def vp0001010110_0 : Blocks := edgeBlocks% "full/vectors/0001010110-V-0000.bin"
private noncomputable def vp0001010110_1 : Blocks := edgeBlocks% "full/vectors/0001010110-V-0001.bin"
private noncomputable def vp0001010110_2 : Blocks := edgeBlocks% "full/vectors/0001010110-V-0002.bin"
noncomputable def vp0001010110 : Blocks := (Blocks.join vp0001010110_0 (Blocks.join vp0001010110_1 vp0001010110_2))
private theorem bp00010101100 : Branch 0 (-687761639/8000000 : ℚ) vp0001010110 := by
  apply branch_left_normalized (c:=vp00010101100) (k:=0) (m:=171) (by decide +kernel)
  rw [show 2*(-687761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-687761639/4000000 : ℚ) by norm_num]
  exact coverp00010101100
private noncomputable def ep00010101101_0 : Blocks := edgeBlocks% "full/vectors/00010101101-E-0000.bin"
private noncomputable def ep00010101101_1 : Blocks := edgeBlocks% "full/vectors/00010101101-E-0001.bin"
private noncomputable def ep00010101101_2 : Blocks := edgeBlocks% "full/vectors/00010101101-E-0002.bin"
noncomputable def ep00010101101 : Blocks := (Blocks.join ep00010101101_0 (Blocks.join ep00010101101_1 ep00010101101_2))
private theorem idp00010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010110.list =
    C ((2:ℤ)^343) * horner X vp00010101101.list + horner X ep00010101101.list := by
  exact edge_identity (B := (2:ℤ)^580) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101101 : Branch 1 (-687761639/8000000 : ℚ) vp0001010110 := by
  apply branch_checked idp00010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-687761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-691761639/4000000 : ℚ) by norm_num]
  exact coverp00010101101
theorem coverp0001010110 : Covers (-687761639/8000000 : ℚ) vp0001010110 := join_branches bp00010101100 bp00010101101
private noncomputable def vp000101011_0 : Blocks := edgeBlocks% "full/vectors/000101011-V-0000.bin"
private noncomputable def vp000101011_1 : Blocks := edgeBlocks% "full/vectors/000101011-V-0001.bin"
private noncomputable def vp000101011_2 : Blocks := edgeBlocks% "full/vectors/000101011-V-0002.bin"
private noncomputable def vp000101011_3 : Blocks := edgeBlocks% "full/vectors/000101011-V-0003.bin"
private noncomputable def vp000101011_4 : Blocks := edgeBlocks% "full/vectors/000101011-V-0004.bin"
noncomputable def vp000101011 : Blocks := (Blocks.join (Blocks.join vp000101011_0 vp000101011_1) (Blocks.join vp000101011_2 (Blocks.join vp000101011_3 vp000101011_4)))
private theorem bp0001010110 : Branch 0 (-687761639/16000000 : ℚ) vp000101011 := by
  apply branch_left_normalized (c:=vp0001010110) (k:=0) (m:=320) (by decide +kernel)
  rw [show 2*(-687761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-687761639/8000000 : ℚ) by norm_num]
  exact coverp0001010110
private noncomputable def ep0001010111_0 : Blocks := edgeBlocks% "full/vectors/0001010111-E-0000.bin"
private noncomputable def ep0001010111_1 : Blocks := edgeBlocks% "full/vectors/0001010111-E-0001.bin"
private noncomputable def ep0001010111_2 : Blocks := edgeBlocks% "full/vectors/0001010111-E-0002.bin"
private noncomputable def ep0001010111_3 : Blocks := edgeBlocks% "full/vectors/0001010111-E-0003.bin"
private noncomputable def ep0001010111_4 : Blocks := edgeBlocks% "full/vectors/0001010111-E-0004.bin"
noncomputable def ep0001010111 : Blocks := (Blocks.join (Blocks.join ep0001010111_0 ep0001010111_1) (Blocks.join ep0001010111_2 (Blocks.join ep0001010111_3 ep0001010111_4)))
private theorem idp0001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101011.list =
    C ((2:ℤ)^662) * horner X vp0001010111.list + horner X ep0001010111.list := by
  exact edge_identity (B := (2:ℤ)^1036) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010111 : Branch 1 (-687761639/16000000 : ℚ) vp000101011 := by
  apply branch_checked idp0001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-687761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-695761639/8000000 : ℚ) by norm_num]
  exact coverp0001010111
theorem coverp000101011 : Covers (-687761639/16000000 : ℚ) vp000101011 := join_branches bp0001010110 bp0001010111
private noncomputable def vp00010101011111_0 : Blocks := edgeBlocks% "full/vectors/00010101011111-V-0000.bin"
noncomputable def vp00010101011111 : Blocks := vp00010101011111_0
theorem coverp00010101011111 : Covers (-687261639/500000 : ℚ) vp00010101011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101011110_0 : Blocks := edgeBlocks% "full/vectors/00010101011110-V-0000.bin"
noncomputable def vp00010101011110 : Blocks := vp00010101011110_0
theorem coverp00010101011110 : Covers (-686761639/500000 : ℚ) vp00010101011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010101111_0 : Blocks := edgeBlocks% "full/vectors/0001010101111-V-0000.bin"
noncomputable def vp0001010101111 : Blocks := vp0001010101111_0
private theorem bp00010101011110 : Branch 0 (-686761639/1000000 : ℚ) vp0001010101111 := by
  apply branch_left_normalized (c:=vp00010101011110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-686761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-686761639/500000 : ℚ) by norm_num]
  exact coverp00010101011110
private noncomputable def ep00010101011111_0 : Blocks := edgeBlocks% "full/vectors/00010101011111-E-0000.bin"
noncomputable def ep00010101011111 : Blocks := ep00010101011111_0
private theorem idp00010101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010101111.list =
    C ((2:ℤ)^59) * horner X vp00010101011111.list + horner X ep00010101011111.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101011111 : Branch 1 (-686761639/1000000 : ℚ) vp0001010101111 := by
  apply branch_checked idp00010101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-686761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-687261639/500000 : ℚ) by norm_num]
  exact coverp00010101011111
theorem coverp0001010101111 : Covers (-686761639/1000000 : ℚ) vp0001010101111 := join_branches bp00010101011110 bp00010101011111
private noncomputable def vp00010101011101_0 : Blocks := edgeBlocks% "full/vectors/00010101011101-V-0000.bin"
noncomputable def vp00010101011101 : Blocks := vp00010101011101_0
theorem coverp00010101011101 : Covers (-686261639/500000 : ℚ) vp00010101011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101011100_0 : Blocks := edgeBlocks% "full/vectors/00010101011100-V-0000.bin"
noncomputable def vp00010101011100 : Blocks := vp00010101011100_0
theorem coverp00010101011100 : Covers (-685761639/500000 : ℚ) vp00010101011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010101110_0 : Blocks := edgeBlocks% "full/vectors/0001010101110-V-0000.bin"
noncomputable def vp0001010101110 : Blocks := vp0001010101110_0
private theorem bp00010101011100 : Branch 0 (-685761639/1000000 : ℚ) vp0001010101110 := by
  apply branch_left_normalized (c:=vp00010101011100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-685761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-685761639/500000 : ℚ) by norm_num]
  exact coverp00010101011100
private noncomputable def ep00010101011101_0 : Blocks := edgeBlocks% "full/vectors/00010101011101-E-0000.bin"
noncomputable def ep00010101011101 : Blocks := ep00010101011101_0
private theorem idp00010101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010101110.list =
    C ((2:ℤ)^60) * horner X vp00010101011101.list + horner X ep00010101011101.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101011101 : Branch 1 (-685761639/1000000 : ℚ) vp0001010101110 := by
  apply branch_checked idp00010101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-685761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-686261639/500000 : ℚ) by norm_num]
  exact coverp00010101011101
theorem coverp0001010101110 : Covers (-685761639/1000000 : ℚ) vp0001010101110 := join_branches bp00010101011100 bp00010101011101
private noncomputable def vp000101010111_0 : Blocks := edgeBlocks% "full/vectors/000101010111-V-0000.bin"
noncomputable def vp000101010111 : Blocks := vp000101010111_0
private theorem bp0001010101110 : Branch 0 (-685761639/2000000 : ℚ) vp000101010111 := by
  apply branch_left_normalized (c:=vp0001010101110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-685761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-685761639/1000000 : ℚ) by norm_num]
  exact coverp0001010101110
private noncomputable def ep0001010101111_0 : Blocks := edgeBlocks% "full/vectors/0001010101111-E-0000.bin"
noncomputable def ep0001010101111 : Blocks := ep0001010101111_0
private theorem idp0001010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101010111.list =
    C ((2:ℤ)^102) * horner X vp0001010101111.list + horner X ep0001010101111.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010101111 : Branch 1 (-685761639/2000000 : ℚ) vp000101010111 := by
  apply branch_checked idp0001010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-685761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-686761639/1000000 : ℚ) by norm_num]
  exact coverp0001010101111
theorem coverp000101010111 : Covers (-685761639/2000000 : ℚ) vp000101010111 := join_branches bp0001010101110 bp0001010101111
private noncomputable def vp00010101011011_0 : Blocks := edgeBlocks% "full/vectors/00010101011011-V-0000.bin"
noncomputable def vp00010101011011 : Blocks := vp00010101011011_0
theorem coverp00010101011011 : Covers (-685261639/500000 : ℚ) vp00010101011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101011010_0 : Blocks := edgeBlocks% "full/vectors/00010101011010-V-0000.bin"
noncomputable def vp00010101011010 : Blocks := vp00010101011010_0
theorem coverp00010101011010 : Covers (-684761639/500000 : ℚ) vp00010101011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010101101_0 : Blocks := edgeBlocks% "full/vectors/0001010101101-V-0000.bin"
noncomputable def vp0001010101101 : Blocks := vp0001010101101_0
private theorem bp00010101011010 : Branch 0 (-684761639/1000000 : ℚ) vp0001010101101 := by
  apply branch_left_normalized (c:=vp00010101011010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-684761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-684761639/500000 : ℚ) by norm_num]
  exact coverp00010101011010
private noncomputable def ep00010101011011_0 : Blocks := edgeBlocks% "full/vectors/00010101011011-E-0000.bin"
noncomputable def ep00010101011011 : Blocks := ep00010101011011_0
private theorem idp00010101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010101101.list =
    C ((2:ℤ)^60) * horner X vp00010101011011.list + horner X ep00010101011011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101011011 : Branch 1 (-684761639/1000000 : ℚ) vp0001010101101 := by
  apply branch_checked idp00010101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-684761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-685261639/500000 : ℚ) by norm_num]
  exact coverp00010101011011
theorem coverp0001010101101 : Covers (-684761639/1000000 : ℚ) vp0001010101101 := join_branches bp00010101011010 bp00010101011011
private noncomputable def vp00010101011001_0 : Blocks := edgeBlocks% "full/vectors/00010101011001-V-0000.bin"
noncomputable def vp00010101011001 : Blocks := vp00010101011001_0
theorem coverp00010101011001 : Covers (-684261639/500000 : ℚ) vp00010101011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101011000_0 : Blocks := edgeBlocks% "full/vectors/00010101011000-V-0000.bin"
noncomputable def vp00010101011000 : Blocks := vp00010101011000_0
theorem coverp00010101011000 : Covers (-683761639/500000 : ℚ) vp00010101011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010101100_0 : Blocks := edgeBlocks% "full/vectors/0001010101100-V-0000.bin"
noncomputable def vp0001010101100 : Blocks := vp0001010101100_0
private theorem bp00010101011000 : Branch 0 (-683761639/1000000 : ℚ) vp0001010101100 := by
  apply branch_left_normalized (c:=vp00010101011000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-683761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-683761639/500000 : ℚ) by norm_num]
  exact coverp00010101011000
private noncomputable def ep00010101011001_0 : Blocks := edgeBlocks% "full/vectors/00010101011001-E-0000.bin"
noncomputable def ep00010101011001 : Blocks := ep00010101011001_0
private theorem idp00010101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010101100.list =
    C ((2:ℤ)^61) * horner X vp00010101011001.list + horner X ep00010101011001.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101011001 : Branch 1 (-683761639/1000000 : ℚ) vp0001010101100 := by
  apply branch_checked idp00010101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-683761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-684261639/500000 : ℚ) by norm_num]
  exact coverp00010101011001
theorem coverp0001010101100 : Covers (-683761639/1000000 : ℚ) vp0001010101100 := join_branches bp00010101011000 bp00010101011001
private noncomputable def vp000101010110_0 : Blocks := edgeBlocks% "full/vectors/000101010110-V-0000.bin"
noncomputable def vp000101010110 : Blocks := vp000101010110_0
private theorem bp0001010101100 : Branch 0 (-683761639/2000000 : ℚ) vp000101010110 := by
  apply branch_left_normalized (c:=vp0001010101100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-683761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-683761639/1000000 : ℚ) by norm_num]
  exact coverp0001010101100
private noncomputable def ep0001010101101_0 : Blocks := edgeBlocks% "full/vectors/0001010101101-E-0000.bin"
noncomputable def ep0001010101101 : Blocks := ep0001010101101_0
private theorem idp0001010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101010110.list =
    C ((2:ℤ)^103) * horner X vp0001010101101.list + horner X ep0001010101101.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010101101 : Branch 1 (-683761639/2000000 : ℚ) vp000101010110 := by
  apply branch_checked idp0001010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-683761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-684761639/1000000 : ℚ) by norm_num]
  exact coverp0001010101101
theorem coverp000101010110 : Covers (-683761639/2000000 : ℚ) vp000101010110 := join_branches bp0001010101100 bp0001010101101
private noncomputable def vp00010101011_0 : Blocks := edgeBlocks% "full/vectors/00010101011-V-0000.bin"
private noncomputable def vp00010101011_1 : Blocks := edgeBlocks% "full/vectors/00010101011-V-0001.bin"
noncomputable def vp00010101011 : Blocks := (Blocks.join vp00010101011_0 vp00010101011_1)
private theorem bp000101010110 : Branch 0 (-683761639/4000000 : ℚ) vp00010101011 := by
  apply branch_left_normalized (c:=vp000101010110) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-683761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-683761639/2000000 : ℚ) by norm_num]
  exact coverp000101010110
private noncomputable def ep000101010111_0 : Blocks := edgeBlocks% "full/vectors/000101010111-E-0000.bin"
private noncomputable def ep000101010111_1 : Blocks := edgeBlocks% "full/vectors/000101010111-E-0001.bin"
noncomputable def ep000101010111 : Blocks := (Blocks.join ep000101010111_0 ep000101010111_1)
private theorem idp000101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010101011.list =
    C ((2:ℤ)^185) * horner X vp000101010111.list + horner X ep000101010111.list := by
  exact edge_identity (B := (2:ℤ)^353) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101010111 : Branch 1 (-683761639/4000000 : ℚ) vp00010101011 := by
  apply branch_checked idp000101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-683761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-685761639/2000000 : ℚ) by norm_num]
  exact coverp000101010111
theorem coverp00010101011 : Covers (-683761639/4000000 : ℚ) vp00010101011 := join_branches bp000101010110 bp000101010111
private noncomputable def vp00010101010111_0 : Blocks := edgeBlocks% "full/vectors/00010101010111-V-0000.bin"
noncomputable def vp00010101010111 : Blocks := vp00010101010111_0
theorem coverp00010101010111 : Covers (-683261639/500000 : ℚ) vp00010101010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101010110_0 : Blocks := edgeBlocks% "full/vectors/00010101010110-V-0000.bin"
noncomputable def vp00010101010110 : Blocks := vp00010101010110_0
theorem coverp00010101010110 : Covers (-682761639/500000 : ℚ) vp00010101010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010101011_0 : Blocks := edgeBlocks% "full/vectors/0001010101011-V-0000.bin"
noncomputable def vp0001010101011 : Blocks := vp0001010101011_0
private theorem bp00010101010110 : Branch 0 (-682761639/1000000 : ℚ) vp0001010101011 := by
  apply branch_left_normalized (c:=vp00010101010110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-682761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-682761639/500000 : ℚ) by norm_num]
  exact coverp00010101010110
private noncomputable def ep00010101010111_0 : Blocks := edgeBlocks% "full/vectors/00010101010111-E-0000.bin"
noncomputable def ep00010101010111 : Blocks := ep00010101010111_0
private theorem idp00010101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010101011.list =
    C ((2:ℤ)^61) * horner X vp00010101010111.list + horner X ep00010101010111.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101010111 : Branch 1 (-682761639/1000000 : ℚ) vp0001010101011 := by
  apply branch_checked idp00010101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-682761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-683261639/500000 : ℚ) by norm_num]
  exact coverp00010101010111
theorem coverp0001010101011 : Covers (-682761639/1000000 : ℚ) vp0001010101011 := join_branches bp00010101010110 bp00010101010111
private noncomputable def vp00010101010101_0 : Blocks := edgeBlocks% "full/vectors/00010101010101-V-0000.bin"
noncomputable def vp00010101010101 : Blocks := vp00010101010101_0
theorem coverp00010101010101 : Covers (-682261639/500000 : ℚ) vp00010101010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101010100_0 : Blocks := edgeBlocks% "full/vectors/00010101010100-V-0000.bin"
noncomputable def vp00010101010100 : Blocks := vp00010101010100_0
theorem coverp00010101010100 : Covers (-681761639/500000 : ℚ) vp00010101010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010101010_0 : Blocks := edgeBlocks% "full/vectors/0001010101010-V-0000.bin"
noncomputable def vp0001010101010 : Blocks := vp0001010101010_0
private theorem bp00010101010100 : Branch 0 (-681761639/1000000 : ℚ) vp0001010101010 := by
  apply branch_left_normalized (c:=vp00010101010100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-681761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-681761639/500000 : ℚ) by norm_num]
  exact coverp00010101010100
private noncomputable def ep00010101010101_0 : Blocks := edgeBlocks% "full/vectors/00010101010101-E-0000.bin"
noncomputable def ep00010101010101 : Blocks := ep00010101010101_0
private theorem idp00010101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010101010.list =
    C ((2:ℤ)^60) * horner X vp00010101010101.list + horner X ep00010101010101.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101010101 : Branch 1 (-681761639/1000000 : ℚ) vp0001010101010 := by
  apply branch_checked idp00010101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-681761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-682261639/500000 : ℚ) by norm_num]
  exact coverp00010101010101
theorem coverp0001010101010 : Covers (-681761639/1000000 : ℚ) vp0001010101010 := join_branches bp00010101010100 bp00010101010101
private noncomputable def vp000101010101_0 : Blocks := edgeBlocks% "full/vectors/000101010101-V-0000.bin"
noncomputable def vp000101010101 : Blocks := vp000101010101_0
private theorem bp0001010101010 : Branch 0 (-681761639/2000000 : ℚ) vp000101010101 := by
  apply branch_left_normalized (c:=vp0001010101010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-681761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-681761639/1000000 : ℚ) by norm_num]
  exact coverp0001010101010
private noncomputable def ep0001010101011_0 : Blocks := edgeBlocks% "full/vectors/0001010101011-E-0000.bin"
noncomputable def ep0001010101011 : Blocks := ep0001010101011_0
private theorem idp0001010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101010101.list =
    C ((2:ℤ)^103) * horner X vp0001010101011.list + horner X ep0001010101011.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010101011 : Branch 1 (-681761639/2000000 : ℚ) vp000101010101 := by
  apply branch_checked idp0001010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-681761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-682761639/1000000 : ℚ) by norm_num]
  exact coverp0001010101011
theorem coverp000101010101 : Covers (-681761639/2000000 : ℚ) vp000101010101 := join_branches bp0001010101010 bp0001010101011
private noncomputable def vp00010101010011_0 : Blocks := edgeBlocks% "full/vectors/00010101010011-V-0000.bin"
noncomputable def vp00010101010011 : Blocks := vp00010101010011_0
theorem coverp00010101010011 : Covers (-681261639/500000 : ℚ) vp00010101010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101010010_0 : Blocks := edgeBlocks% "full/vectors/00010101010010-V-0000.bin"
noncomputable def vp00010101010010 : Blocks := vp00010101010010_0
theorem coverp00010101010010 : Covers (-680761639/500000 : ℚ) vp00010101010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010101001_0 : Blocks := edgeBlocks% "full/vectors/0001010101001-V-0000.bin"
noncomputable def vp0001010101001 : Blocks := vp0001010101001_0
private theorem bp00010101010010 : Branch 0 (-680761639/1000000 : ℚ) vp0001010101001 := by
  apply branch_left_normalized (c:=vp00010101010010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-680761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-680761639/500000 : ℚ) by norm_num]
  exact coverp00010101010010
private noncomputable def ep00010101010011_0 : Blocks := edgeBlocks% "full/vectors/00010101010011-E-0000.bin"
noncomputable def ep00010101010011 : Blocks := ep00010101010011_0
private theorem idp00010101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010101001.list =
    C ((2:ℤ)^60) * horner X vp00010101010011.list + horner X ep00010101010011.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101010011 : Branch 1 (-680761639/1000000 : ℚ) vp0001010101001 := by
  apply branch_checked idp00010101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-680761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-681261639/500000 : ℚ) by norm_num]
  exact coverp00010101010011
theorem coverp0001010101001 : Covers (-680761639/1000000 : ℚ) vp0001010101001 := join_branches bp00010101010010 bp00010101010011
private noncomputable def vp00010101010001_0 : Blocks := edgeBlocks% "full/vectors/00010101010001-V-0000.bin"
noncomputable def vp00010101010001 : Blocks := vp00010101010001_0
theorem coverp00010101010001 : Covers (-680261639/500000 : ℚ) vp00010101010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101010000_0 : Blocks := edgeBlocks% "full/vectors/00010101010000-V-0000.bin"
noncomputable def vp00010101010000 : Blocks := vp00010101010000_0
theorem coverp00010101010000 : Covers (-679761639/500000 : ℚ) vp00010101010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010101000_0 : Blocks := edgeBlocks% "full/vectors/0001010101000-V-0000.bin"
noncomputable def vp0001010101000 : Blocks := vp0001010101000_0
private theorem bp00010101010000 : Branch 0 (-679761639/1000000 : ℚ) vp0001010101000 := by
  apply branch_left_normalized (c:=vp00010101010000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-679761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-679761639/500000 : ℚ) by norm_num]
  exact coverp00010101010000
private noncomputable def ep00010101010001_0 : Blocks := edgeBlocks% "full/vectors/00010101010001-E-0000.bin"
noncomputable def ep00010101010001 : Blocks := ep00010101010001_0
private theorem idp00010101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010101000.list =
    C ((2:ℤ)^59) * horner X vp00010101010001.list + horner X ep00010101010001.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101010001 : Branch 1 (-679761639/1000000 : ℚ) vp0001010101000 := by
  apply branch_checked idp00010101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-679761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-680261639/500000 : ℚ) by norm_num]
  exact coverp00010101010001
theorem coverp0001010101000 : Covers (-679761639/1000000 : ℚ) vp0001010101000 := join_branches bp00010101010000 bp00010101010001
private noncomputable def vp000101010100_0 : Blocks := edgeBlocks% "full/vectors/000101010100-V-0000.bin"
noncomputable def vp000101010100 : Blocks := vp000101010100_0
private theorem bp0001010101000 : Branch 0 (-679761639/2000000 : ℚ) vp000101010100 := by
  apply branch_left_normalized (c:=vp0001010101000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-679761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-679761639/1000000 : ℚ) by norm_num]
  exact coverp0001010101000
private noncomputable def ep0001010101001_0 : Blocks := edgeBlocks% "full/vectors/0001010101001-E-0000.bin"
noncomputable def ep0001010101001 : Blocks := ep0001010101001_0
private theorem idp0001010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101010100.list =
    C ((2:ℤ)^100) * horner X vp0001010101001.list + horner X ep0001010101001.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010101001 : Branch 1 (-679761639/2000000 : ℚ) vp000101010100 := by
  apply branch_checked idp0001010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-679761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-680761639/1000000 : ℚ) by norm_num]
  exact coverp0001010101001
theorem coverp000101010100 : Covers (-679761639/2000000 : ℚ) vp000101010100 := join_branches bp0001010101000 bp0001010101001
private noncomputable def vp00010101010_0 : Blocks := edgeBlocks% "full/vectors/00010101010-V-0000.bin"
private noncomputable def vp00010101010_1 : Blocks := edgeBlocks% "full/vectors/00010101010-V-0001.bin"
noncomputable def vp00010101010 : Blocks := (Blocks.join vp00010101010_0 vp00010101010_1)
private theorem bp000101010100 : Branch 0 (-679761639/4000000 : ℚ) vp00010101010 := by
  apply branch_left_normalized (c:=vp000101010100) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-679761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-679761639/2000000 : ℚ) by norm_num]
  exact coverp000101010100
private noncomputable def ep000101010101_0 : Blocks := edgeBlocks% "full/vectors/000101010101-E-0000.bin"
private noncomputable def ep000101010101_1 : Blocks := edgeBlocks% "full/vectors/000101010101-E-0001.bin"
noncomputable def ep000101010101 : Blocks := (Blocks.join ep000101010101_0 ep000101010101_1)
private theorem idp000101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010101010.list =
    C ((2:ℤ)^180) * horner X vp000101010101.list + horner X ep000101010101.list := by
  exact edge_identity (B := (2:ℤ)^350) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101010101 : Branch 1 (-679761639/4000000 : ℚ) vp00010101010 := by
  apply branch_checked idp000101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-679761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-681761639/2000000 : ℚ) by norm_num]
  exact coverp000101010101
theorem coverp00010101010 : Covers (-679761639/4000000 : ℚ) vp00010101010 := join_branches bp000101010100 bp000101010101
private noncomputable def vp0001010101_0 : Blocks := edgeBlocks% "full/vectors/0001010101-V-0000.bin"
private noncomputable def vp0001010101_1 : Blocks := edgeBlocks% "full/vectors/0001010101-V-0001.bin"
private noncomputable def vp0001010101_2 : Blocks := edgeBlocks% "full/vectors/0001010101-V-0002.bin"
noncomputable def vp0001010101 : Blocks := (Blocks.join vp0001010101_0 (Blocks.join vp0001010101_1 vp0001010101_2))
private theorem bp00010101010 : Branch 0 (-679761639/8000000 : ℚ) vp0001010101 := by
  apply branch_left_normalized (c:=vp00010101010) (k:=0) (m:=170) (by decide +kernel)
  rw [show 2*(-679761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-679761639/4000000 : ℚ) by norm_num]
  exact coverp00010101010
private noncomputable def ep00010101011_0 : Blocks := edgeBlocks% "full/vectors/00010101011-E-0000.bin"
private noncomputable def ep00010101011_1 : Blocks := edgeBlocks% "full/vectors/00010101011-E-0001.bin"
private noncomputable def ep00010101011_2 : Blocks := edgeBlocks% "full/vectors/00010101011-E-0002.bin"
noncomputable def ep00010101011 : Blocks := (Blocks.join ep00010101011_0 (Blocks.join ep00010101011_1 ep00010101011_2))
private theorem idp00010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010101.list =
    C ((2:ℤ)^344) * horner X vp00010101011.list + horner X ep00010101011.list := by
  exact edge_identity (B := (2:ℤ)^581) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101011 : Branch 1 (-679761639/8000000 : ℚ) vp0001010101 := by
  apply branch_checked idp00010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-679761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-683761639/4000000 : ℚ) by norm_num]
  exact coverp00010101011
theorem coverp0001010101 : Covers (-679761639/8000000 : ℚ) vp0001010101 := join_branches bp00010101010 bp00010101011
private noncomputable def vp0001010100111_0 : Blocks := edgeBlocks% "full/vectors/0001010100111-V-0000.bin"
noncomputable def vp0001010100111 : Blocks := vp0001010100111_0
theorem coverp0001010100111 : Covers (-678761639/1000000 : ℚ) vp0001010100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010100110_0 : Blocks := edgeBlocks% "full/vectors/0001010100110-V-0000.bin"
noncomputable def vp0001010100110 : Blocks := vp0001010100110_0
theorem coverp0001010100110 : Covers (-677761639/1000000 : ℚ) vp0001010100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000101010011_0 : Blocks := edgeBlocks% "full/vectors/000101010011-V-0000.bin"
noncomputable def vp000101010011 : Blocks := vp000101010011_0
private theorem bp0001010100110 : Branch 0 (-677761639/2000000 : ℚ) vp000101010011 := by
  apply branch_left_normalized (c:=vp0001010100110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-677761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-677761639/1000000 : ℚ) by norm_num]
  exact coverp0001010100110
private noncomputable def ep0001010100111_0 : Blocks := edgeBlocks% "full/vectors/0001010100111-E-0000.bin"
noncomputable def ep0001010100111 : Blocks := ep0001010100111_0
private theorem idp0001010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101010011.list =
    C ((2:ℤ)^101) * horner X vp0001010100111.list + horner X ep0001010100111.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010100111 : Branch 1 (-677761639/2000000 : ℚ) vp000101010011 := by
  apply branch_checked idp0001010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-677761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-678761639/1000000 : ℚ) by norm_num]
  exact coverp0001010100111
theorem coverp000101010011 : Covers (-677761639/2000000 : ℚ) vp000101010011 := join_branches bp0001010100110 bp0001010100111
private noncomputable def vp0001010100101_0 : Blocks := edgeBlocks% "full/vectors/0001010100101-V-0000.bin"
noncomputable def vp0001010100101 : Blocks := vp0001010100101_0
theorem coverp0001010100101 : Covers (-676761639/1000000 : ℚ) vp0001010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010100100_0 : Blocks := edgeBlocks% "full/vectors/0001010100100-V-0000.bin"
noncomputable def vp0001010100100 : Blocks := vp0001010100100_0
theorem coverp0001010100100 : Covers (-675761639/1000000 : ℚ) vp0001010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp000101010010_0 : Blocks := edgeBlocks% "full/vectors/000101010010-V-0000.bin"
noncomputable def vp000101010010 : Blocks := vp000101010010_0
private theorem bp0001010100100 : Branch 0 (-675761639/2000000 : ℚ) vp000101010010 := by
  apply branch_left_normalized (c:=vp0001010100100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-675761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-675761639/1000000 : ℚ) by norm_num]
  exact coverp0001010100100
private noncomputable def ep0001010100101_0 : Blocks := edgeBlocks% "full/vectors/0001010100101-E-0000.bin"
noncomputable def ep0001010100101 : Blocks := ep0001010100101_0
private theorem idp0001010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101010010.list =
    C ((2:ℤ)^104) * horner X vp0001010100101.list + horner X ep0001010100101.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010100101 : Branch 1 (-675761639/2000000 : ℚ) vp000101010010 := by
  apply branch_checked idp0001010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-675761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-676761639/1000000 : ℚ) by norm_num]
  exact coverp0001010100101
theorem coverp000101010010 : Covers (-675761639/2000000 : ℚ) vp000101010010 := join_branches bp0001010100100 bp0001010100101
private noncomputable def vp00010101001_0 : Blocks := edgeBlocks% "full/vectors/00010101001-V-0000.bin"
private noncomputable def vp00010101001_1 : Blocks := edgeBlocks% "full/vectors/00010101001-V-0001.bin"
noncomputable def vp00010101001 : Blocks := (Blocks.join vp00010101001_0 vp00010101001_1)
private theorem bp000101010010 : Branch 0 (-675761639/4000000 : ℚ) vp00010101001 := by
  apply branch_left_normalized (c:=vp000101010010) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-675761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-675761639/2000000 : ℚ) by norm_num]
  exact coverp000101010010
private noncomputable def ep000101010011_0 : Blocks := edgeBlocks% "full/vectors/000101010011-E-0000.bin"
private noncomputable def ep000101010011_1 : Blocks := edgeBlocks% "full/vectors/000101010011-E-0001.bin"
noncomputable def ep000101010011 : Blocks := (Blocks.join ep000101010011_0 ep000101010011_1)
private theorem idp000101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010101001.list =
    C ((2:ℤ)^187) * horner X vp000101010011.list + horner X ep000101010011.list := by
  exact edge_identity (B := (2:ℤ)^353) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101010011 : Branch 1 (-675761639/4000000 : ℚ) vp00010101001 := by
  apply branch_checked idp000101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-675761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-677761639/2000000 : ℚ) by norm_num]
  exact coverp000101010011
theorem coverp00010101001 : Covers (-675761639/4000000 : ℚ) vp00010101001 := join_branches bp000101010010 bp000101010011
private noncomputable def vp00010101000111_0 : Blocks := edgeBlocks% "full/vectors/00010101000111-V-0000.bin"
noncomputable def vp00010101000111 : Blocks := vp00010101000111_0
theorem coverp00010101000111 : Covers (-675261639/500000 : ℚ) vp00010101000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101000110_0 : Blocks := edgeBlocks% "full/vectors/00010101000110-V-0000.bin"
noncomputable def vp00010101000110 : Blocks := vp00010101000110_0
theorem coverp00010101000110 : Covers (-674761639/500000 : ℚ) vp00010101000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010100011_0 : Blocks := edgeBlocks% "full/vectors/0001010100011-V-0000.bin"
noncomputable def vp0001010100011 : Blocks := vp0001010100011_0
private theorem bp00010101000110 : Branch 0 (-674761639/1000000 : ℚ) vp0001010100011 := by
  apply branch_left_normalized (c:=vp00010101000110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-674761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-674761639/500000 : ℚ) by norm_num]
  exact coverp00010101000110
private noncomputable def ep00010101000111_0 : Blocks := edgeBlocks% "full/vectors/00010101000111-E-0000.bin"
noncomputable def ep00010101000111 : Blocks := ep00010101000111_0
private theorem idp00010101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010100011.list =
    C ((2:ℤ)^61) * horner X vp00010101000111.list + horner X ep00010101000111.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101000111 : Branch 1 (-674761639/1000000 : ℚ) vp0001010100011 := by
  apply branch_checked idp00010101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-674761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-675261639/500000 : ℚ) by norm_num]
  exact coverp00010101000111
theorem coverp0001010100011 : Covers (-674761639/1000000 : ℚ) vp0001010100011 := join_branches bp00010101000110 bp00010101000111
private noncomputable def vp00010101000101_0 : Blocks := edgeBlocks% "full/vectors/00010101000101-V-0000.bin"
noncomputable def vp00010101000101 : Blocks := vp00010101000101_0
theorem coverp00010101000101 : Covers (-674261639/500000 : ℚ) vp00010101000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010101000100_0 : Blocks := edgeBlocks% "full/vectors/00010101000100-V-0000.bin"
noncomputable def vp00010101000100 : Blocks := vp00010101000100_0
theorem coverp00010101000100 : Covers (-673761639/500000 : ℚ) vp00010101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010100010_0 : Blocks := edgeBlocks% "full/vectors/0001010100010-V-0000.bin"
noncomputable def vp0001010100010 : Blocks := vp0001010100010_0
private theorem bp00010101000100 : Branch 0 (-673761639/1000000 : ℚ) vp0001010100010 := by
  apply branch_left_normalized (c:=vp00010101000100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-673761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-673761639/500000 : ℚ) by norm_num]
  exact coverp00010101000100
private noncomputable def ep00010101000101_0 : Blocks := edgeBlocks% "full/vectors/00010101000101-E-0000.bin"
noncomputable def ep00010101000101 : Blocks := ep00010101000101_0
private theorem idp00010101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010100010.list =
    C ((2:ℤ)^58) * horner X vp00010101000101.list + horner X ep00010101000101.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101000101 : Branch 1 (-673761639/1000000 : ℚ) vp0001010100010 := by
  apply branch_checked idp00010101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-673761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-674261639/500000 : ℚ) by norm_num]
  exact coverp00010101000101
theorem coverp0001010100010 : Covers (-673761639/1000000 : ℚ) vp0001010100010 := join_branches bp00010101000100 bp00010101000101
private noncomputable def vp000101010001_0 : Blocks := edgeBlocks% "full/vectors/000101010001-V-0000.bin"
noncomputable def vp000101010001 : Blocks := vp000101010001_0
private theorem bp0001010100010 : Branch 0 (-673761639/2000000 : ℚ) vp000101010001 := by
  apply branch_left_normalized (c:=vp0001010100010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-673761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-673761639/1000000 : ℚ) by norm_num]
  exact coverp0001010100010
private noncomputable def ep0001010100011_0 : Blocks := edgeBlocks% "full/vectors/0001010100011-E-0000.bin"
noncomputable def ep0001010100011 : Blocks := ep0001010100011_0
private theorem idp0001010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101010001.list =
    C ((2:ℤ)^98) * horner X vp0001010100011.list + horner X ep0001010100011.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010100011 : Branch 1 (-673761639/2000000 : ℚ) vp000101010001 := by
  apply branch_checked idp0001010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-673761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-674761639/1000000 : ℚ) by norm_num]
  exact coverp0001010100011
theorem coverp000101010001 : Covers (-673761639/2000000 : ℚ) vp000101010001 := join_branches bp0001010100010 bp0001010100011
private noncomputable def vp0001010100001_0 : Blocks := edgeBlocks% "full/vectors/0001010100001-V-0000.bin"
noncomputable def vp0001010100001 : Blocks := vp0001010100001_0
theorem coverp0001010100001 : Covers (-672761639/1000000 : ℚ) vp0001010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010100000_0 : Blocks := edgeBlocks% "full/vectors/0001010100000-V-0000.bin"
noncomputable def vp0001010100000 : Blocks := vp0001010100000_0
theorem coverp0001010100000 : Covers (-671761639/1000000 : ℚ) vp0001010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000101010000_0 : Blocks := edgeBlocks% "full/vectors/000101010000-V-0000.bin"
noncomputable def vp000101010000 : Blocks := vp000101010000_0
private theorem bp0001010100000 : Branch 0 (-671761639/2000000 : ℚ) vp000101010000 := by
  apply branch_left_normalized (c:=vp0001010100000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-671761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-671761639/1000000 : ℚ) by norm_num]
  exact coverp0001010100000
private noncomputable def ep0001010100001_0 : Blocks := edgeBlocks% "full/vectors/0001010100001-E-0000.bin"
noncomputable def ep0001010100001 : Blocks := ep0001010100001_0
private theorem idp0001010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101010000.list =
    C ((2:ℤ)^98) * horner X vp0001010100001.list + horner X ep0001010100001.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010100001 : Branch 1 (-671761639/2000000 : ℚ) vp000101010000 := by
  apply branch_checked idp0001010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-671761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-672761639/1000000 : ℚ) by norm_num]
  exact coverp0001010100001
theorem coverp000101010000 : Covers (-671761639/2000000 : ℚ) vp000101010000 := join_branches bp0001010100000 bp0001010100001
private noncomputable def vp00010101000_0 : Blocks := edgeBlocks% "full/vectors/00010101000-V-0000.bin"
private noncomputable def vp00010101000_1 : Blocks := edgeBlocks% "full/vectors/00010101000-V-0001.bin"
noncomputable def vp00010101000 : Blocks := (Blocks.join vp00010101000_0 vp00010101000_1)
private theorem bp000101010000 : Branch 0 (-671761639/4000000 : ℚ) vp00010101000 := by
  apply branch_left_normalized (c:=vp000101010000) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-671761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-671761639/2000000 : ℚ) by norm_num]
  exact coverp000101010000
private noncomputable def ep000101010001_0 : Blocks := edgeBlocks% "full/vectors/000101010001-E-0000.bin"
private noncomputable def ep000101010001_1 : Blocks := edgeBlocks% "full/vectors/000101010001-E-0001.bin"
noncomputable def ep000101010001 : Blocks := (Blocks.join ep000101010001_0 ep000101010001_1)
private theorem idp000101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010101000.list =
    C ((2:ℤ)^178) * horner X vp000101010001.list + horner X ep000101010001.list := by
  exact edge_identity (B := (2:ℤ)^344) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101010001 : Branch 1 (-671761639/4000000 : ℚ) vp00010101000 := by
  apply branch_checked idp000101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-671761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-673761639/2000000 : ℚ) by norm_num]
  exact coverp000101010001
theorem coverp00010101000 : Covers (-671761639/4000000 : ℚ) vp00010101000 := join_branches bp000101010000 bp000101010001
private noncomputable def vp0001010100_0 : Blocks := edgeBlocks% "full/vectors/0001010100-V-0000.bin"
private noncomputable def vp0001010100_1 : Blocks := edgeBlocks% "full/vectors/0001010100-V-0001.bin"
private noncomputable def vp0001010100_2 : Blocks := edgeBlocks% "full/vectors/0001010100-V-0002.bin"
noncomputable def vp0001010100 : Blocks := (Blocks.join vp0001010100_0 (Blocks.join vp0001010100_1 vp0001010100_2))
private theorem bp00010101000 : Branch 0 (-671761639/8000000 : ℚ) vp0001010100 := by
  apply branch_left_normalized (c:=vp00010101000) (k:=0) (m:=169) (by decide +kernel)
  rw [show 2*(-671761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-671761639/4000000 : ℚ) by norm_num]
  exact coverp00010101000
private noncomputable def ep00010101001_0 : Blocks := edgeBlocks% "full/vectors/00010101001-E-0000.bin"
private noncomputable def ep00010101001_1 : Blocks := edgeBlocks% "full/vectors/00010101001-E-0001.bin"
private noncomputable def ep00010101001_2 : Blocks := edgeBlocks% "full/vectors/00010101001-E-0002.bin"
noncomputable def ep00010101001 : Blocks := (Blocks.join ep00010101001_0 (Blocks.join ep00010101001_1 ep00010101001_2))
private theorem idp00010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010100.list =
    C ((2:ℤ)^338) * horner X vp00010101001.list + horner X ep00010101001.list := by
  exact edge_identity (B := (2:ℤ)^576) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101001 : Branch 1 (-671761639/8000000 : ℚ) vp0001010100 := by
  apply branch_checked idp00010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-671761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-675761639/4000000 : ℚ) by norm_num]
  exact coverp00010101001
theorem coverp0001010100 : Covers (-671761639/8000000 : ℚ) vp0001010100 := join_branches bp00010101000 bp00010101001
private noncomputable def vp000101010_0 : Blocks := edgeBlocks% "full/vectors/000101010-V-0000.bin"
private noncomputable def vp000101010_1 : Blocks := edgeBlocks% "full/vectors/000101010-V-0001.bin"
private noncomputable def vp000101010_2 : Blocks := edgeBlocks% "full/vectors/000101010-V-0002.bin"
private noncomputable def vp000101010_3 : Blocks := edgeBlocks% "full/vectors/000101010-V-0003.bin"
private noncomputable def vp000101010_4 : Blocks := edgeBlocks% "full/vectors/000101010-V-0004.bin"
noncomputable def vp000101010 : Blocks := (Blocks.join (Blocks.join vp000101010_0 vp000101010_1) (Blocks.join vp000101010_2 (Blocks.join vp000101010_3 vp000101010_4)))
private theorem bp0001010100 : Branch 0 (-671761639/16000000 : ℚ) vp000101010 := by
  apply branch_left_normalized (c:=vp0001010100) (k:=0) (m:=320) (by decide +kernel)
  rw [show 2*(-671761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-671761639/8000000 : ℚ) by norm_num]
  exact coverp0001010100
private noncomputable def ep0001010101_0 : Blocks := edgeBlocks% "full/vectors/0001010101-E-0000.bin"
private noncomputable def ep0001010101_1 : Blocks := edgeBlocks% "full/vectors/0001010101-E-0001.bin"
private noncomputable def ep0001010101_2 : Blocks := edgeBlocks% "full/vectors/0001010101-E-0002.bin"
private noncomputable def ep0001010101_3 : Blocks := edgeBlocks% "full/vectors/0001010101-E-0003.bin"
private noncomputable def ep0001010101_4 : Blocks := edgeBlocks% "full/vectors/0001010101-E-0004.bin"
noncomputable def ep0001010101 : Blocks := (Blocks.join (Blocks.join ep0001010101_0 ep0001010101_1) (Blocks.join ep0001010101_2 (Blocks.join ep0001010101_3 ep0001010101_4)))
private theorem idp0001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101010.list =
    C ((2:ℤ)^661) * horner X vp0001010101.list + horner X ep0001010101.list := by
  exact edge_identity (B := (2:ℤ)^1035) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010101 : Branch 1 (-671761639/16000000 : ℚ) vp000101010 := by
  apply branch_checked idp0001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-671761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-679761639/8000000 : ℚ) by norm_num]
  exact coverp0001010101
theorem coverp000101010 : Covers (-671761639/16000000 : ℚ) vp000101010 := join_branches bp0001010100 bp0001010101
private noncomputable def vp00010101_0 : Blocks := edgeBlocks% "full/vectors/00010101-V-0000.bin"
private noncomputable def vp00010101_1 : Blocks := edgeBlocks% "full/vectors/00010101-V-0001.bin"
private noncomputable def vp00010101_2 : Blocks := edgeBlocks% "full/vectors/00010101-V-0002.bin"
private noncomputable def vp00010101_3 : Blocks := edgeBlocks% "full/vectors/00010101-V-0003.bin"
private noncomputable def vp00010101_4 : Blocks := edgeBlocks% "full/vectors/00010101-V-0004.bin"
private noncomputable def vp00010101_5 : Blocks := edgeBlocks% "full/vectors/00010101-V-0005.bin"
private noncomputable def vp00010101_6 : Blocks := edgeBlocks% "full/vectors/00010101-V-0006.bin"
private noncomputable def vp00010101_7 : Blocks := edgeBlocks% "full/vectors/00010101-V-0007.bin"
private noncomputable def vp00010101_8 : Blocks := edgeBlocks% "full/vectors/00010101-V-0008.bin"
private noncomputable def vp00010101_9 : Blocks := edgeBlocks% "full/vectors/00010101-V-0009.bin"
noncomputable def vp00010101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00010101_0 vp00010101_1) (Blocks.join vp00010101_2 (Blocks.join vp00010101_3 vp00010101_4))) (Blocks.join (Blocks.join vp00010101_5 vp00010101_6) (Blocks.join vp00010101_7 (Blocks.join vp00010101_8 vp00010101_9))))
private theorem bp000101010 : Branch 0 (-671761639/32000000 : ℚ) vp00010101 := by
  apply branch_left_normalized (c:=vp000101010) (k:=0) (m:=619) (by decide +kernel)
  rw [show 2*(-671761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-671761639/16000000 : ℚ) by norm_num]
  exact coverp000101010
private noncomputable def ep000101011_0 : Blocks := edgeBlocks% "full/vectors/000101011-E-0000.bin"
private noncomputable def ep000101011_1 : Blocks := edgeBlocks% "full/vectors/000101011-E-0001.bin"
private noncomputable def ep000101011_2 : Blocks := edgeBlocks% "full/vectors/000101011-E-0002.bin"
private noncomputable def ep000101011_3 : Blocks := edgeBlocks% "full/vectors/000101011-E-0003.bin"
private noncomputable def ep000101011_4 : Blocks := edgeBlocks% "full/vectors/000101011-E-0004.bin"
private noncomputable def ep000101011_5 : Blocks := edgeBlocks% "full/vectors/000101011-E-0005.bin"
private noncomputable def ep000101011_6 : Blocks := edgeBlocks% "full/vectors/000101011-E-0006.bin"
private noncomputable def ep000101011_7 : Blocks := edgeBlocks% "full/vectors/000101011-E-0007.bin"
private noncomputable def ep000101011_8 : Blocks := edgeBlocks% "full/vectors/000101011-E-0008.bin"
private noncomputable def ep000101011_9 : Blocks := edgeBlocks% "full/vectors/000101011-E-0009.bin"
noncomputable def ep000101011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000101011_0 ep000101011_1) (Blocks.join ep000101011_2 (Blocks.join ep000101011_3 ep000101011_4))) (Blocks.join (Blocks.join ep000101011_5 ep000101011_6) (Blocks.join ep000101011_7 (Blocks.join ep000101011_8 ep000101011_9))))
private theorem idp000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010101.list =
    C ((2:ℤ)^1297) * horner X vp000101011.list + horner X ep000101011.list := by
  exact edge_identity (B := (2:ℤ)^1945) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101011 : Branch 1 (-671761639/32000000 : ℚ) vp00010101 := by
  apply branch_checked idp000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-671761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-687761639/16000000 : ℚ) by norm_num]
  exact coverp000101011
theorem coverp00010101 : Covers (-671761639/32000000 : ℚ) vp00010101 := join_branches bp000101010 bp000101011
end NextProof.EdgeFull

