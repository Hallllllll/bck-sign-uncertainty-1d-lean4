import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000111111111_0 : Blocks := edgeBlocks% "full/vectors/0000111111111-V-0000.bin"
noncomputable def vp0000111111111 : Blocks := vp0000111111111_0
theorem coverp0000111111111 : Covers (-510761639/1000000 : ℚ) vp0000111111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111111110_0 : Blocks := edgeBlocks% "full/vectors/0000111111110-V-0000.bin"
noncomputable def vp0000111111110 : Blocks := vp0000111111110_0
theorem coverp0000111111110 : Covers (-509761639/1000000 : ℚ) vp0000111111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000011111111_0 : Blocks := edgeBlocks% "full/vectors/000011111111-V-0000.bin"
noncomputable def vp000011111111 : Blocks := vp000011111111_0
private theorem bp0000111111110 : Branch 0 (-509761639/2000000 : ℚ) vp000011111111 := by
  apply branch_left_normalized (c:=vp0000111111110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-509761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-509761639/1000000 : ℚ) by norm_num]
  exact coverp0000111111110
private noncomputable def ep0000111111111_0 : Blocks := edgeBlocks% "full/vectors/0000111111111-E-0000.bin"
noncomputable def ep0000111111111 : Blocks := ep0000111111111_0
private theorem idp0000111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011111111.list =
    C ((2:ℤ)^108) * horner X vp0000111111111.list + horner X ep0000111111111.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111111111 : Branch 1 (-509761639/2000000 : ℚ) vp000011111111 := by
  apply branch_checked idp0000111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-509761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-510761639/1000000 : ℚ) by norm_num]
  exact coverp0000111111111
theorem coverp000011111111 : Covers (-509761639/2000000 : ℚ) vp000011111111 := join_branches bp0000111111110 bp0000111111111
private noncomputable def vp0000111111101_0 : Blocks := edgeBlocks% "full/vectors/0000111111101-V-0000.bin"
noncomputable def vp0000111111101 : Blocks := vp0000111111101_0
theorem coverp0000111111101 : Covers (-508761639/1000000 : ℚ) vp0000111111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111111100_0 : Blocks := edgeBlocks% "full/vectors/0000111111100-V-0000.bin"
noncomputable def vp0000111111100 : Blocks := vp0000111111100_0
theorem coverp0000111111100 : Covers (-507761639/1000000 : ℚ) vp0000111111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000011111110_0 : Blocks := edgeBlocks% "full/vectors/000011111110-V-0000.bin"
noncomputable def vp000011111110 : Blocks := vp000011111110_0
private theorem bp0000111111100 : Branch 0 (-507761639/2000000 : ℚ) vp000011111110 := by
  apply branch_left_normalized (c:=vp0000111111100) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-507761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-507761639/1000000 : ℚ) by norm_num]
  exact coverp0000111111100
private noncomputable def ep0000111111101_0 : Blocks := edgeBlocks% "full/vectors/0000111111101-E-0000.bin"
noncomputable def ep0000111111101 : Blocks := ep0000111111101_0
private theorem idp0000111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011111110.list =
    C ((2:ℤ)^109) * horner X vp0000111111101.list + horner X ep0000111111101.list := by
  exact edge_identity (B := (2:ℤ)^240) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111111101 : Branch 1 (-507761639/2000000 : ℚ) vp000011111110 := by
  apply branch_checked idp0000111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-507761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-508761639/1000000 : ℚ) by norm_num]
  exact coverp0000111111101
theorem coverp000011111110 : Covers (-507761639/2000000 : ℚ) vp000011111110 := join_branches bp0000111111100 bp0000111111101
private noncomputable def vp00001111111_0 : Blocks := edgeBlocks% "full/vectors/00001111111-V-0000.bin"
private noncomputable def vp00001111111_1 : Blocks := edgeBlocks% "full/vectors/00001111111-V-0001.bin"
noncomputable def vp00001111111 : Blocks := (Blocks.join vp00001111111_0 vp00001111111_1)
private theorem bp000011111110 : Branch 0 (-507761639/4000000 : ℚ) vp00001111111 := by
  apply branch_left_normalized (c:=vp000011111110) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-507761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-507761639/2000000 : ℚ) by norm_num]
  exact coverp000011111110
private noncomputable def ep000011111111_0 : Blocks := edgeBlocks% "full/vectors/000011111111-E-0000.bin"
private noncomputable def ep000011111111_1 : Blocks := edgeBlocks% "full/vectors/000011111111-E-0001.bin"
noncomputable def ep000011111111 : Blocks := (Blocks.join ep000011111111_0 ep000011111111_1)
private theorem idp000011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001111111.list =
    C ((2:ℤ)^202) * horner X vp000011111111.list + horner X ep000011111111.list := by
  exact edge_identity (B := (2:ℤ)^373) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011111111 : Branch 1 (-507761639/4000000 : ℚ) vp00001111111 := by
  apply branch_checked idp000011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-507761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-509761639/2000000 : ℚ) by norm_num]
  exact coverp000011111111
theorem coverp00001111111 : Covers (-507761639/4000000 : ℚ) vp00001111111 := join_branches bp000011111110 bp000011111111
private noncomputable def vp0000111111011_0 : Blocks := edgeBlocks% "full/vectors/0000111111011-V-0000.bin"
noncomputable def vp0000111111011 : Blocks := vp0000111111011_0
theorem coverp0000111111011 : Covers (-506761639/1000000 : ℚ) vp0000111111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111111010_0 : Blocks := edgeBlocks% "full/vectors/0000111111010-V-0000.bin"
noncomputable def vp0000111111010 : Blocks := vp0000111111010_0
theorem coverp0000111111010 : Covers (-505761639/1000000 : ℚ) vp0000111111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000011111101_0 : Blocks := edgeBlocks% "full/vectors/000011111101-V-0000.bin"
noncomputable def vp000011111101 : Blocks := vp000011111101_0
private theorem bp0000111111010 : Branch 0 (-505761639/2000000 : ℚ) vp000011111101 := by
  apply branch_left_normalized (c:=vp0000111111010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-505761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-505761639/1000000 : ℚ) by norm_num]
  exact coverp0000111111010
private noncomputable def ep0000111111011_0 : Blocks := edgeBlocks% "full/vectors/0000111111011-E-0000.bin"
noncomputable def ep0000111111011 : Blocks := ep0000111111011_0
private theorem idp0000111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011111101.list =
    C ((2:ℤ)^109) * horner X vp0000111111011.list + horner X ep0000111111011.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111111011 : Branch 1 (-505761639/2000000 : ℚ) vp000011111101 := by
  apply branch_checked idp0000111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-505761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-506761639/1000000 : ℚ) by norm_num]
  exact coverp0000111111011
theorem coverp000011111101 : Covers (-505761639/2000000 : ℚ) vp000011111101 := join_branches bp0000111111010 bp0000111111011
private noncomputable def vp0000111111001_0 : Blocks := edgeBlocks% "full/vectors/0000111111001-V-0000.bin"
noncomputable def vp0000111111001 : Blocks := vp0000111111001_0
theorem coverp0000111111001 : Covers (-504761639/1000000 : ℚ) vp0000111111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111111000_0 : Blocks := edgeBlocks% "full/vectors/0000111111000-V-0000.bin"
noncomputable def vp0000111111000 : Blocks := vp0000111111000_0
theorem coverp0000111111000 : Covers (-503761639/1000000 : ℚ) vp0000111111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000011111100_0 : Blocks := edgeBlocks% "full/vectors/000011111100-V-0000.bin"
noncomputable def vp000011111100 : Blocks := vp000011111100_0
private theorem bp0000111111000 : Branch 0 (-503761639/2000000 : ℚ) vp000011111100 := by
  apply branch_left_normalized (c:=vp0000111111000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-503761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-503761639/1000000 : ℚ) by norm_num]
  exact coverp0000111111000
private noncomputable def ep0000111111001_0 : Blocks := edgeBlocks% "full/vectors/0000111111001-E-0000.bin"
noncomputable def ep0000111111001 : Blocks := ep0000111111001_0
private theorem idp0000111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011111100.list =
    C ((2:ℤ)^109) * horner X vp0000111111001.list + horner X ep0000111111001.list := by
  exact edge_identity (B := (2:ℤ)^240) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111111001 : Branch 1 (-503761639/2000000 : ℚ) vp000011111100 := by
  apply branch_checked idp0000111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-503761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-504761639/1000000 : ℚ) by norm_num]
  exact coverp0000111111001
theorem coverp000011111100 : Covers (-503761639/2000000 : ℚ) vp000011111100 := join_branches bp0000111111000 bp0000111111001
private noncomputable def vp00001111110_0 : Blocks := edgeBlocks% "full/vectors/00001111110-V-0000.bin"
private noncomputable def vp00001111110_1 : Blocks := edgeBlocks% "full/vectors/00001111110-V-0001.bin"
noncomputable def vp00001111110 : Blocks := (Blocks.join vp00001111110_0 vp00001111110_1)
private theorem bp000011111100 : Branch 0 (-503761639/4000000 : ℚ) vp00001111110 := by
  apply branch_left_normalized (c:=vp000011111100) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-503761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-503761639/2000000 : ℚ) by norm_num]
  exact coverp000011111100
private noncomputable def ep000011111101_0 : Blocks := edgeBlocks% "full/vectors/000011111101-E-0000.bin"
private noncomputable def ep000011111101_1 : Blocks := edgeBlocks% "full/vectors/000011111101-E-0001.bin"
noncomputable def ep000011111101 : Blocks := (Blocks.join ep000011111101_0 ep000011111101_1)
private theorem idp000011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001111110.list =
    C ((2:ℤ)^203) * horner X vp000011111101.list + horner X ep000011111101.list := by
  exact edge_identity (B := (2:ℤ)^374) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011111101 : Branch 1 (-503761639/4000000 : ℚ) vp00001111110 := by
  apply branch_checked idp000011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-503761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-505761639/2000000 : ℚ) by norm_num]
  exact coverp000011111101
theorem coverp00001111110 : Covers (-503761639/4000000 : ℚ) vp00001111110 := join_branches bp000011111100 bp000011111101
private noncomputable def vp0000111111_0 : Blocks := edgeBlocks% "full/vectors/0000111111-V-0000.bin"
private noncomputable def vp0000111111_1 : Blocks := edgeBlocks% "full/vectors/0000111111-V-0001.bin"
private noncomputable def vp0000111111_2 : Blocks := edgeBlocks% "full/vectors/0000111111-V-0002.bin"
noncomputable def vp0000111111 : Blocks := (Blocks.join vp0000111111_0 (Blocks.join vp0000111111_1 vp0000111111_2))
private theorem bp00001111110 : Branch 0 (-503761639/8000000 : ℚ) vp0000111111 := by
  apply branch_left_normalized (c:=vp00001111110) (k:=0) (m:=190) (by decide +kernel)
  rw [show 2*(-503761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-503761639/4000000 : ℚ) by norm_num]
  exact coverp00001111110
private noncomputable def ep00001111111_0 : Blocks := edgeBlocks% "full/vectors/00001111111-E-0000.bin"
private noncomputable def ep00001111111_1 : Blocks := edgeBlocks% "full/vectors/00001111111-E-0001.bin"
private noncomputable def ep00001111111_2 : Blocks := edgeBlocks% "full/vectors/00001111111-E-0002.bin"
noncomputable def ep00001111111 : Blocks := (Blocks.join ep00001111111_0 (Blocks.join ep00001111111_1 ep00001111111_2))
private theorem idp00001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111111.list =
    C ((2:ℤ)^387) * horner X vp00001111111.list + horner X ep00001111111.list := by
  exact edge_identity (B := (2:ℤ)^640) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111111 : Branch 1 (-503761639/8000000 : ℚ) vp0000111111 := by
  apply branch_checked idp00001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-503761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-507761639/4000000 : ℚ) by norm_num]
  exact coverp00001111111
theorem coverp0000111111 : Covers (-503761639/8000000 : ℚ) vp0000111111 := join_branches bp00001111110 bp00001111111
private noncomputable def vp0000111110111_0 : Blocks := edgeBlocks% "full/vectors/0000111110111-V-0000.bin"
noncomputable def vp0000111110111 : Blocks := vp0000111110111_0
theorem coverp0000111110111 : Covers (-502761639/1000000 : ℚ) vp0000111110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111110110_0 : Blocks := edgeBlocks% "full/vectors/0000111110110-V-0000.bin"
noncomputable def vp0000111110110 : Blocks := vp0000111110110_0
theorem coverp0000111110110 : Covers (-501761639/1000000 : ℚ) vp0000111110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000011111011_0 : Blocks := edgeBlocks% "full/vectors/000011111011-V-0000.bin"
noncomputable def vp000011111011 : Blocks := vp000011111011_0
private theorem bp0000111110110 : Branch 0 (-501761639/2000000 : ℚ) vp000011111011 := by
  apply branch_left_normalized (c:=vp0000111110110) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-501761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-501761639/1000000 : ℚ) by norm_num]
  exact coverp0000111110110
private noncomputable def ep0000111110111_0 : Blocks := edgeBlocks% "full/vectors/0000111110111-E-0000.bin"
noncomputable def ep0000111110111 : Blocks := ep0000111110111_0
private theorem idp0000111110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011111011.list =
    C ((2:ℤ)^110) * horner X vp0000111110111.list + horner X ep0000111110111.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111110111 : Branch 1 (-501761639/2000000 : ℚ) vp000011111011 := by
  apply branch_checked idp0000111110111 (by positivity) (by decide +kernel)
  rw [show 2*(-501761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-502761639/1000000 : ℚ) by norm_num]
  exact coverp0000111110111
theorem coverp000011111011 : Covers (-501761639/2000000 : ℚ) vp000011111011 := join_branches bp0000111110110 bp0000111110111
private noncomputable def vp0000111110101_0 : Blocks := edgeBlocks% "full/vectors/0000111110101-V-0000.bin"
noncomputable def vp0000111110101 : Blocks := vp0000111110101_0
theorem coverp0000111110101 : Covers (-500761639/1000000 : ℚ) vp0000111110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111110100_0 : Blocks := edgeBlocks% "full/vectors/0000111110100-V-0000.bin"
noncomputable def vp0000111110100 : Blocks := vp0000111110100_0
theorem coverp0000111110100 : Covers (-499761639/1000000 : ℚ) vp0000111110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000011111010_0 : Blocks := edgeBlocks% "full/vectors/000011111010-V-0000.bin"
noncomputable def vp000011111010 : Blocks := vp000011111010_0
private theorem bp0000111110100 : Branch 0 (-499761639/2000000 : ℚ) vp000011111010 := by
  apply branch_left_normalized (c:=vp0000111110100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-499761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-499761639/1000000 : ℚ) by norm_num]
  exact coverp0000111110100
private noncomputable def ep0000111110101_0 : Blocks := edgeBlocks% "full/vectors/0000111110101-E-0000.bin"
noncomputable def ep0000111110101 : Blocks := ep0000111110101_0
private theorem idp0000111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011111010.list =
    C ((2:ℤ)^110) * horner X vp0000111110101.list + horner X ep0000111110101.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111110101 : Branch 1 (-499761639/2000000 : ℚ) vp000011111010 := by
  apply branch_checked idp0000111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-499761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-500761639/1000000 : ℚ) by norm_num]
  exact coverp0000111110101
theorem coverp000011111010 : Covers (-499761639/2000000 : ℚ) vp000011111010 := join_branches bp0000111110100 bp0000111110101
private noncomputable def vp00001111101_0 : Blocks := edgeBlocks% "full/vectors/00001111101-V-0000.bin"
private noncomputable def vp00001111101_1 : Blocks := edgeBlocks% "full/vectors/00001111101-V-0001.bin"
noncomputable def vp00001111101 : Blocks := (Blocks.join vp00001111101_0 vp00001111101_1)
private theorem bp000011111010 : Branch 0 (-499761639/4000000 : ℚ) vp00001111101 := by
  apply branch_left_normalized (c:=vp000011111010) (k:=0) (m:=103) (by decide +kernel)
  rw [show 2*(-499761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-499761639/2000000 : ℚ) by norm_num]
  exact coverp000011111010
private noncomputable def ep000011111011_0 : Blocks := edgeBlocks% "full/vectors/000011111011-E-0000.bin"
private noncomputable def ep000011111011_1 : Blocks := edgeBlocks% "full/vectors/000011111011-E-0001.bin"
noncomputable def ep000011111011 : Blocks := (Blocks.join ep000011111011_0 ep000011111011_1)
private theorem idp000011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001111101.list =
    C ((2:ℤ)^204) * horner X vp000011111011.list + horner X ep000011111011.list := by
  exact edge_identity (B := (2:ℤ)^377) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011111011 : Branch 1 (-499761639/4000000 : ℚ) vp00001111101 := by
  apply branch_checked idp000011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-499761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-501761639/2000000 : ℚ) by norm_num]
  exact coverp000011111011
theorem coverp00001111101 : Covers (-499761639/4000000 : ℚ) vp00001111101 := join_branches bp000011111010 bp000011111011
private noncomputable def vp0000111110011_0 : Blocks := edgeBlocks% "full/vectors/0000111110011-V-0000.bin"
noncomputable def vp0000111110011 : Blocks := vp0000111110011_0
theorem coverp0000111110011 : Covers (-498761639/1000000 : ℚ) vp0000111110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111110010_0 : Blocks := edgeBlocks% "full/vectors/0000111110010-V-0000.bin"
noncomputable def vp0000111110010 : Blocks := vp0000111110010_0
theorem coverp0000111110010 : Covers (-497761639/1000000 : ℚ) vp0000111110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000011111001_0 : Blocks := edgeBlocks% "full/vectors/000011111001-V-0000.bin"
noncomputable def vp000011111001 : Blocks := vp000011111001_0
private theorem bp0000111110010 : Branch 0 (-497761639/2000000 : ℚ) vp000011111001 := by
  apply branch_left_normalized (c:=vp0000111110010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-497761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-497761639/1000000 : ℚ) by norm_num]
  exact coverp0000111110010
private noncomputable def ep0000111110011_0 : Blocks := edgeBlocks% "full/vectors/0000111110011-E-0000.bin"
noncomputable def ep0000111110011 : Blocks := ep0000111110011_0
private theorem idp0000111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011111001.list =
    C ((2:ℤ)^111) * horner X vp0000111110011.list + horner X ep0000111110011.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111110011 : Branch 1 (-497761639/2000000 : ℚ) vp000011111001 := by
  apply branch_checked idp0000111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-497761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-498761639/1000000 : ℚ) by norm_num]
  exact coverp0000111110011
theorem coverp000011111001 : Covers (-497761639/2000000 : ℚ) vp000011111001 := join_branches bp0000111110010 bp0000111110011
private noncomputable def vp0000111110001_0 : Blocks := edgeBlocks% "full/vectors/0000111110001-V-0000.bin"
noncomputable def vp0000111110001 : Blocks := vp0000111110001_0
theorem coverp0000111110001 : Covers (-496761639/1000000 : ℚ) vp0000111110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111110000_0 : Blocks := edgeBlocks% "full/vectors/0000111110000-V-0000.bin"
noncomputable def vp0000111110000 : Blocks := vp0000111110000_0
theorem coverp0000111110000 : Covers (-495761639/1000000 : ℚ) vp0000111110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000011111000_0 : Blocks := edgeBlocks% "full/vectors/000011111000-V-0000.bin"
noncomputable def vp000011111000 : Blocks := vp000011111000_0
private theorem bp0000111110000 : Branch 0 (-495761639/2000000 : ℚ) vp000011111000 := by
  apply branch_left_normalized (c:=vp0000111110000) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-495761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-495761639/1000000 : ℚ) by norm_num]
  exact coverp0000111110000
private noncomputable def ep0000111110001_0 : Blocks := edgeBlocks% "full/vectors/0000111110001-E-0000.bin"
noncomputable def ep0000111110001 : Blocks := ep0000111110001_0
private theorem idp0000111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011111000.list =
    C ((2:ℤ)^113) * horner X vp0000111110001.list + horner X ep0000111110001.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111110001 : Branch 1 (-495761639/2000000 : ℚ) vp000011111000 := by
  apply branch_checked idp0000111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-495761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-496761639/1000000 : ℚ) by norm_num]
  exact coverp0000111110001
theorem coverp000011111000 : Covers (-495761639/2000000 : ℚ) vp000011111000 := join_branches bp0000111110000 bp0000111110001
private noncomputable def vp00001111100_0 : Blocks := edgeBlocks% "full/vectors/00001111100-V-0000.bin"
private noncomputable def vp00001111100_1 : Blocks := edgeBlocks% "full/vectors/00001111100-V-0001.bin"
noncomputable def vp00001111100 : Blocks := (Blocks.join vp00001111100_0 vp00001111100_1)
private theorem bp000011111000 : Branch 0 (-495761639/4000000 : ℚ) vp00001111100 := by
  apply branch_left_normalized (c:=vp000011111000) (k:=0) (m:=105) (by decide +kernel)
  rw [show 2*(-495761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-495761639/2000000 : ℚ) by norm_num]
  exact coverp000011111000
private noncomputable def ep000011111001_0 : Blocks := edgeBlocks% "full/vectors/000011111001-E-0000.bin"
private noncomputable def ep000011111001_1 : Blocks := edgeBlocks% "full/vectors/000011111001-E-0001.bin"
noncomputable def ep000011111001 : Blocks := (Blocks.join ep000011111001_0 ep000011111001_1)
private theorem idp000011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001111100.list =
    C ((2:ℤ)^207) * horner X vp000011111001.list + horner X ep000011111001.list := by
  exact edge_identity (B := (2:ℤ)^381) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011111001 : Branch 1 (-495761639/4000000 : ℚ) vp00001111100 := by
  apply branch_checked idp000011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-495761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-497761639/2000000 : ℚ) by norm_num]
  exact coverp000011111001
theorem coverp00001111100 : Covers (-495761639/4000000 : ℚ) vp00001111100 := join_branches bp000011111000 bp000011111001
private noncomputable def vp0000111110_0 : Blocks := edgeBlocks% "full/vectors/0000111110-V-0000.bin"
private noncomputable def vp0000111110_1 : Blocks := edgeBlocks% "full/vectors/0000111110-V-0001.bin"
private noncomputable def vp0000111110_2 : Blocks := edgeBlocks% "full/vectors/0000111110-V-0002.bin"
noncomputable def vp0000111110 : Blocks := (Blocks.join vp0000111110_0 (Blocks.join vp0000111110_1 vp0000111110_2))
private theorem bp00001111100 : Branch 0 (-495761639/8000000 : ℚ) vp0000111110 := by
  apply branch_left_normalized (c:=vp00001111100) (k:=0) (m:=193) (by decide +kernel)
  rw [show 2*(-495761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-495761639/4000000 : ℚ) by norm_num]
  exact coverp00001111100
private noncomputable def ep00001111101_0 : Blocks := edgeBlocks% "full/vectors/00001111101-E-0000.bin"
private noncomputable def ep00001111101_1 : Blocks := edgeBlocks% "full/vectors/00001111101-E-0001.bin"
private noncomputable def ep00001111101_2 : Blocks := edgeBlocks% "full/vectors/00001111101-E-0002.bin"
noncomputable def ep00001111101 : Blocks := (Blocks.join ep00001111101_0 (Blocks.join ep00001111101_1 ep00001111101_2))
private theorem idp00001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111110.list =
    C ((2:ℤ)^395) * horner X vp00001111101.list + horner X ep00001111101.list := by
  exact edge_identity (B := (2:ℤ)^650) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111101 : Branch 1 (-495761639/8000000 : ℚ) vp0000111110 := by
  apply branch_checked idp00001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-495761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-499761639/4000000 : ℚ) by norm_num]
  exact coverp00001111101
theorem coverp0000111110 : Covers (-495761639/8000000 : ℚ) vp0000111110 := join_branches bp00001111100 bp00001111101
private noncomputable def vp000011111_0 : Blocks := edgeBlocks% "full/vectors/000011111-V-0000.bin"
private noncomputable def vp000011111_1 : Blocks := edgeBlocks% "full/vectors/000011111-V-0001.bin"
private noncomputable def vp000011111_2 : Blocks := edgeBlocks% "full/vectors/000011111-V-0002.bin"
private noncomputable def vp000011111_3 : Blocks := edgeBlocks% "full/vectors/000011111-V-0003.bin"
private noncomputable def vp000011111_4 : Blocks := edgeBlocks% "full/vectors/000011111-V-0004.bin"
private noncomputable def vp000011111_5 : Blocks := edgeBlocks% "full/vectors/000011111-V-0005.bin"
noncomputable def vp000011111 : Blocks := (Blocks.join (Blocks.join vp000011111_0 (Blocks.join vp000011111_1 vp000011111_2)) (Blocks.join vp000011111_3 (Blocks.join vp000011111_4 vp000011111_5)))
private theorem bp0000111110 : Branch 0 (-495761639/16000000 : ℚ) vp000011111 := by
  apply branch_left_normalized (c:=vp0000111110) (k:=0) (m:=369) (by decide +kernel)
  rw [show 2*(-495761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-495761639/8000000 : ℚ) by norm_num]
  exact coverp0000111110
private noncomputable def ep0000111111_0 : Blocks := edgeBlocks% "full/vectors/0000111111-E-0000.bin"
private noncomputable def ep0000111111_1 : Blocks := edgeBlocks% "full/vectors/0000111111-E-0001.bin"
private noncomputable def ep0000111111_2 : Blocks := edgeBlocks% "full/vectors/0000111111-E-0002.bin"
private noncomputable def ep0000111111_3 : Blocks := edgeBlocks% "full/vectors/0000111111-E-0003.bin"
private noncomputable def ep0000111111_4 : Blocks := edgeBlocks% "full/vectors/0000111111-E-0004.bin"
private noncomputable def ep0000111111_5 : Blocks := edgeBlocks% "full/vectors/0000111111-E-0005.bin"
noncomputable def ep0000111111 : Blocks := (Blocks.join (Blocks.join ep0000111111_0 (Blocks.join ep0000111111_1 ep0000111111_2)) (Blocks.join ep0000111111_3 (Blocks.join ep0000111111_4 ep0000111111_5)))
private theorem idp0000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011111.list =
    C ((2:ℤ)^767) * horner X vp0000111111.list + horner X ep0000111111.list := by
  exact edge_identity (B := (2:ℤ)^1185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111111 : Branch 1 (-495761639/16000000 : ℚ) vp000011111 := by
  apply branch_checked idp0000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-495761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-503761639/8000000 : ℚ) by norm_num]
  exact coverp0000111111
theorem coverp000011111 : Covers (-495761639/16000000 : ℚ) vp000011111 := join_branches bp0000111110 bp0000111111
private noncomputable def vp0000111101111_0 : Blocks := edgeBlocks% "full/vectors/0000111101111-V-0000.bin"
noncomputable def vp0000111101111 : Blocks := vp0000111101111_0
theorem coverp0000111101111 : Covers (-494761639/1000000 : ℚ) vp0000111101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111101110_0 : Blocks := edgeBlocks% "full/vectors/0000111101110-V-0000.bin"
noncomputable def vp0000111101110 : Blocks := vp0000111101110_0
theorem coverp0000111101110 : Covers (-493761639/1000000 : ℚ) vp0000111101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000011110111_0 : Blocks := edgeBlocks% "full/vectors/000011110111-V-0000.bin"
noncomputable def vp000011110111 : Blocks := vp000011110111_0
private theorem bp0000111101110 : Branch 0 (-493761639/2000000 : ℚ) vp000011110111 := by
  apply branch_left_normalized (c:=vp0000111101110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-493761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-493761639/1000000 : ℚ) by norm_num]
  exact coverp0000111101110
private noncomputable def ep0000111101111_0 : Blocks := edgeBlocks% "full/vectors/0000111101111-E-0000.bin"
noncomputable def ep0000111101111 : Blocks := ep0000111101111_0
private theorem idp0000111101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011110111.list =
    C ((2:ℤ)^114) * horner X vp0000111101111.list + horner X ep0000111101111.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111101111 : Branch 1 (-493761639/2000000 : ℚ) vp000011110111 := by
  apply branch_checked idp0000111101111 (by positivity) (by decide +kernel)
  rw [show 2*(-493761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-494761639/1000000 : ℚ) by norm_num]
  exact coverp0000111101111
theorem coverp000011110111 : Covers (-493761639/2000000 : ℚ) vp000011110111 := join_branches bp0000111101110 bp0000111101111
private noncomputable def vp0000111101101_0 : Blocks := edgeBlocks% "full/vectors/0000111101101-V-0000.bin"
noncomputable def vp0000111101101 : Blocks := vp0000111101101_0
theorem coverp0000111101101 : Covers (-492761639/1000000 : ℚ) vp0000111101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111011001_0 : Blocks := edgeBlocks% "full/vectors/00001111011001-V-0000.bin"
noncomputable def vp00001111011001 : Blocks := vp00001111011001_0
theorem coverp00001111011001 : Covers (-492261639/500000 : ℚ) vp00001111011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111011000_0 : Blocks := edgeBlocks% "full/vectors/00001111011000-V-0000.bin"
noncomputable def vp00001111011000 : Blocks := vp00001111011000_0
theorem coverp00001111011000 : Covers (-491761639/500000 : ℚ) vp00001111011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111101100_0 : Blocks := edgeBlocks% "full/vectors/0000111101100-V-0000.bin"
noncomputable def vp0000111101100 : Blocks := vp0000111101100_0
private theorem bp00001111011000 : Branch 0 (-491761639/1000000 : ℚ) vp0000111101100 := by
  apply branch_left_normalized (c:=vp00001111011000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-491761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-491761639/500000 : ℚ) by norm_num]
  exact coverp00001111011000
private noncomputable def ep00001111011001_0 : Blocks := edgeBlocks% "full/vectors/00001111011001-E-0000.bin"
noncomputable def ep00001111011001 : Blocks := ep00001111011001_0
private theorem idp00001111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111101100.list =
    C ((2:ℤ)^68) * horner X vp00001111011001.list + horner X ep00001111011001.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111011001 : Branch 1 (-491761639/1000000 : ℚ) vp0000111101100 := by
  apply branch_checked idp00001111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-491761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-492261639/500000 : ℚ) by norm_num]
  exact coverp00001111011001
theorem coverp0000111101100 : Covers (-491761639/1000000 : ℚ) vp0000111101100 := join_branches bp00001111011000 bp00001111011001
private noncomputable def vp000011110110_0 : Blocks := edgeBlocks% "full/vectors/000011110110-V-0000.bin"
noncomputable def vp000011110110 : Blocks := vp000011110110_0
private theorem bp0000111101100 : Branch 0 (-491761639/2000000 : ℚ) vp000011110110 := by
  apply branch_left_normalized (c:=vp0000111101100) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-491761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-491761639/1000000 : ℚ) by norm_num]
  exact coverp0000111101100
private noncomputable def ep0000111101101_0 : Blocks := edgeBlocks% "full/vectors/0000111101101-E-0000.bin"
noncomputable def ep0000111101101 : Blocks := ep0000111101101_0
private theorem idp0000111101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011110110.list =
    C ((2:ℤ)^117) * horner X vp0000111101101.list + horner X ep0000111101101.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111101101 : Branch 1 (-491761639/2000000 : ℚ) vp000011110110 := by
  apply branch_checked idp0000111101101 (by positivity) (by decide +kernel)
  rw [show 2*(-491761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-492761639/1000000 : ℚ) by norm_num]
  exact coverp0000111101101
theorem coverp000011110110 : Covers (-491761639/2000000 : ℚ) vp000011110110 := join_branches bp0000111101100 bp0000111101101
private noncomputable def vp00001111011_0 : Blocks := edgeBlocks% "full/vectors/00001111011-V-0000.bin"
private noncomputable def vp00001111011_1 : Blocks := edgeBlocks% "full/vectors/00001111011-V-0001.bin"
noncomputable def vp00001111011 : Blocks := (Blocks.join vp00001111011_0 vp00001111011_1)
private theorem bp000011110110 : Branch 0 (-491761639/4000000 : ℚ) vp00001111011 := by
  apply branch_left_normalized (c:=vp000011110110) (k:=0) (m:=108) (by decide +kernel)
  rw [show 2*(-491761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-491761639/2000000 : ℚ) by norm_num]
  exact coverp000011110110
private noncomputable def ep000011110111_0 : Blocks := edgeBlocks% "full/vectors/000011110111-E-0000.bin"
private noncomputable def ep000011110111_1 : Blocks := edgeBlocks% "full/vectors/000011110111-E-0001.bin"
noncomputable def ep000011110111 : Blocks := (Blocks.join ep000011110111_0 ep000011110111_1)
private theorem idp000011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001111011.list =
    C ((2:ℤ)^213) * horner X vp000011110111.list + horner X ep000011110111.list := by
  exact edge_identity (B := (2:ℤ)^390) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011110111 : Branch 1 (-491761639/4000000 : ℚ) vp00001111011 := by
  apply branch_checked idp000011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-491761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-493761639/2000000 : ℚ) by norm_num]
  exact coverp000011110111
theorem coverp00001111011 : Covers (-491761639/4000000 : ℚ) vp00001111011 := join_branches bp000011110110 bp000011110111
private noncomputable def vp00001111010111_0 : Blocks := edgeBlocks% "full/vectors/00001111010111-V-0000.bin"
noncomputable def vp00001111010111 : Blocks := vp00001111010111_0
theorem coverp00001111010111 : Covers (-491261639/500000 : ℚ) vp00001111010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111010110_0 : Blocks := edgeBlocks% "full/vectors/00001111010110-V-0000.bin"
noncomputable def vp00001111010110 : Blocks := vp00001111010110_0
theorem coverp00001111010110 : Covers (-490761639/500000 : ℚ) vp00001111010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111101011_0 : Blocks := edgeBlocks% "full/vectors/0000111101011-V-0000.bin"
noncomputable def vp0000111101011 : Blocks := vp0000111101011_0
private theorem bp00001111010110 : Branch 0 (-490761639/1000000 : ℚ) vp0000111101011 := by
  apply branch_left_normalized (c:=vp00001111010110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-490761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-490761639/500000 : ℚ) by norm_num]
  exact coverp00001111010110
private noncomputable def ep00001111010111_0 : Blocks := edgeBlocks% "full/vectors/00001111010111-E-0000.bin"
noncomputable def ep00001111010111 : Blocks := ep00001111010111_0
private theorem idp00001111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111101011.list =
    C ((2:ℤ)^71) * horner X vp00001111010111.list + horner X ep00001111010111.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111010111 : Branch 1 (-490761639/1000000 : ℚ) vp0000111101011 := by
  apply branch_checked idp00001111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-490761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-491261639/500000 : ℚ) by norm_num]
  exact coverp00001111010111
theorem coverp0000111101011 : Covers (-490761639/1000000 : ℚ) vp0000111101011 := join_branches bp00001111010110 bp00001111010111
private noncomputable def vp00001111010101_0 : Blocks := edgeBlocks% "full/vectors/00001111010101-V-0000.bin"
noncomputable def vp00001111010101 : Blocks := vp00001111010101_0
theorem coverp00001111010101 : Covers (-490261639/500000 : ℚ) vp00001111010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111010100_0 : Blocks := edgeBlocks% "full/vectors/00001111010100-V-0000.bin"
noncomputable def vp00001111010100 : Blocks := vp00001111010100_0
theorem coverp00001111010100 : Covers (-489761639/500000 : ℚ) vp00001111010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111101010_0 : Blocks := edgeBlocks% "full/vectors/0000111101010-V-0000.bin"
noncomputable def vp0000111101010 : Blocks := vp0000111101010_0
private theorem bp00001111010100 : Branch 0 (-489761639/1000000 : ℚ) vp0000111101010 := by
  apply branch_left_normalized (c:=vp00001111010100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-489761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-489761639/500000 : ℚ) by norm_num]
  exact coverp00001111010100
private noncomputable def ep00001111010101_0 : Blocks := edgeBlocks% "full/vectors/00001111010101-E-0000.bin"
noncomputable def ep00001111010101 : Blocks := ep00001111010101_0
private theorem idp00001111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111101010.list =
    C ((2:ℤ)^66) * horner X vp00001111010101.list + horner X ep00001111010101.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111010101 : Branch 1 (-489761639/1000000 : ℚ) vp0000111101010 := by
  apply branch_checked idp00001111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-489761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-490261639/500000 : ℚ) by norm_num]
  exact coverp00001111010101
theorem coverp0000111101010 : Covers (-489761639/1000000 : ℚ) vp0000111101010 := join_branches bp00001111010100 bp00001111010101
private noncomputable def vp000011110101_0 : Blocks := edgeBlocks% "full/vectors/000011110101-V-0000.bin"
noncomputable def vp000011110101 : Blocks := vp000011110101_0
private theorem bp0000111101010 : Branch 0 (-489761639/2000000 : ℚ) vp000011110101 := by
  apply branch_left_normalized (c:=vp0000111101010) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-489761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-489761639/1000000 : ℚ) by norm_num]
  exact coverp0000111101010
private noncomputable def ep0000111101011_0 : Blocks := edgeBlocks% "full/vectors/0000111101011-E-0000.bin"
noncomputable def ep0000111101011 : Blocks := ep0000111101011_0
private theorem idp0000111101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011110101.list =
    C ((2:ℤ)^113) * horner X vp0000111101011.list + horner X ep0000111101011.list := by
  exact edge_identity (B := (2:ℤ)^257) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111101011 : Branch 1 (-489761639/2000000 : ℚ) vp000011110101 := by
  apply branch_checked idp0000111101011 (by positivity) (by decide +kernel)
  rw [show 2*(-489761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-490761639/1000000 : ℚ) by norm_num]
  exact coverp0000111101011
theorem coverp000011110101 : Covers (-489761639/2000000 : ℚ) vp000011110101 := join_branches bp0000111101010 bp0000111101011
private noncomputable def vp00001111010011_0 : Blocks := edgeBlocks% "full/vectors/00001111010011-V-0000.bin"
noncomputable def vp00001111010011 : Blocks := vp00001111010011_0
theorem coverp00001111010011 : Covers (-489261639/500000 : ℚ) vp00001111010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111010010_0 : Blocks := edgeBlocks% "full/vectors/00001111010010-V-0000.bin"
noncomputable def vp00001111010010 : Blocks := vp00001111010010_0
theorem coverp00001111010010 : Covers (-488761639/500000 : ℚ) vp00001111010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111101001_0 : Blocks := edgeBlocks% "full/vectors/0000111101001-V-0000.bin"
noncomputable def vp0000111101001 : Blocks := vp0000111101001_0
private theorem bp00001111010010 : Branch 0 (-488761639/1000000 : ℚ) vp0000111101001 := by
  apply branch_left_normalized (c:=vp00001111010010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-488761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-488761639/500000 : ℚ) by norm_num]
  exact coverp00001111010010
private noncomputable def ep00001111010011_0 : Blocks := edgeBlocks% "full/vectors/00001111010011-E-0000.bin"
noncomputable def ep00001111010011 : Blocks := ep00001111010011_0
private theorem idp00001111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111101001.list =
    C ((2:ℤ)^66) * horner X vp00001111010011.list + horner X ep00001111010011.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111010011 : Branch 1 (-488761639/1000000 : ℚ) vp0000111101001 := by
  apply branch_checked idp00001111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-488761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-489261639/500000 : ℚ) by norm_num]
  exact coverp00001111010011
theorem coverp0000111101001 : Covers (-488761639/1000000 : ℚ) vp0000111101001 := join_branches bp00001111010010 bp00001111010011
private noncomputable def vp00001111010001_0 : Blocks := edgeBlocks% "full/vectors/00001111010001-V-0000.bin"
noncomputable def vp00001111010001 : Blocks := vp00001111010001_0
theorem coverp00001111010001 : Covers (-488261639/500000 : ℚ) vp00001111010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111010000_0 : Blocks := edgeBlocks% "full/vectors/00001111010000-V-0000.bin"
noncomputable def vp00001111010000 : Blocks := vp00001111010000_0
theorem coverp00001111010000 : Covers (-487761639/500000 : ℚ) vp00001111010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111101000_0 : Blocks := edgeBlocks% "full/vectors/0000111101000-V-0000.bin"
noncomputable def vp0000111101000 : Blocks := vp0000111101000_0
private theorem bp00001111010000 : Branch 0 (-487761639/1000000 : ℚ) vp0000111101000 := by
  apply branch_left_normalized (c:=vp00001111010000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-487761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-487761639/500000 : ℚ) by norm_num]
  exact coverp00001111010000
private noncomputable def ep00001111010001_0 : Blocks := edgeBlocks% "full/vectors/00001111010001-E-0000.bin"
noncomputable def ep00001111010001 : Blocks := ep00001111010001_0
private theorem idp00001111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111101000.list =
    C ((2:ℤ)^67) * horner X vp00001111010001.list + horner X ep00001111010001.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111010001 : Branch 1 (-487761639/1000000 : ℚ) vp0000111101000 := by
  apply branch_checked idp00001111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-487761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-488261639/500000 : ℚ) by norm_num]
  exact coverp00001111010001
theorem coverp0000111101000 : Covers (-487761639/1000000 : ℚ) vp0000111101000 := join_branches bp00001111010000 bp00001111010001
private noncomputable def vp000011110100_0 : Blocks := edgeBlocks% "full/vectors/000011110100-V-0000.bin"
noncomputable def vp000011110100 : Blocks := vp000011110100_0
private theorem bp0000111101000 : Branch 0 (-487761639/2000000 : ℚ) vp000011110100 := by
  apply branch_left_normalized (c:=vp0000111101000) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-487761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-487761639/1000000 : ℚ) by norm_num]
  exact coverp0000111101000
private noncomputable def ep0000111101001_0 : Blocks := edgeBlocks% "full/vectors/0000111101001-E-0000.bin"
noncomputable def ep0000111101001 : Blocks := ep0000111101001_0
private theorem idp0000111101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011110100.list =
    C ((2:ℤ)^116) * horner X vp0000111101001.list + horner X ep0000111101001.list := by
  exact edge_identity (B := (2:ℤ)^256) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111101001 : Branch 1 (-487761639/2000000 : ℚ) vp000011110100 := by
  apply branch_checked idp0000111101001 (by positivity) (by decide +kernel)
  rw [show 2*(-487761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-488761639/1000000 : ℚ) by norm_num]
  exact coverp0000111101001
theorem coverp000011110100 : Covers (-487761639/2000000 : ℚ) vp000011110100 := join_branches bp0000111101000 bp0000111101001
private noncomputable def vp00001111010_0 : Blocks := edgeBlocks% "full/vectors/00001111010-V-0000.bin"
private noncomputable def vp00001111010_1 : Blocks := edgeBlocks% "full/vectors/00001111010-V-0001.bin"
noncomputable def vp00001111010 : Blocks := (Blocks.join vp00001111010_0 vp00001111010_1)
private theorem bp000011110100 : Branch 0 (-487761639/4000000 : ℚ) vp00001111010 := by
  apply branch_left_normalized (c:=vp000011110100) (k:=0) (m:=109) (by decide +kernel)
  rw [show 2*(-487761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-487761639/2000000 : ℚ) by norm_num]
  exact coverp000011110100
private noncomputable def ep000011110101_0 : Blocks := edgeBlocks% "full/vectors/000011110101-E-0000.bin"
private noncomputable def ep000011110101_1 : Blocks := edgeBlocks% "full/vectors/000011110101-E-0001.bin"
noncomputable def ep000011110101 : Blocks := (Blocks.join ep000011110101_0 ep000011110101_1)
private theorem idp000011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001111010.list =
    C ((2:ℤ)^210) * horner X vp000011110101.list + horner X ep000011110101.list := by
  exact edge_identity (B := (2:ℤ)^393) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011110101 : Branch 1 (-487761639/4000000 : ℚ) vp00001111010 := by
  apply branch_checked idp000011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-487761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-489761639/2000000 : ℚ) by norm_num]
  exact coverp000011110101
theorem coverp00001111010 : Covers (-487761639/4000000 : ℚ) vp00001111010 := join_branches bp000011110100 bp000011110101
private noncomputable def vp0000111101_0 : Blocks := edgeBlocks% "full/vectors/0000111101-V-0000.bin"
private noncomputable def vp0000111101_1 : Blocks := edgeBlocks% "full/vectors/0000111101-V-0001.bin"
private noncomputable def vp0000111101_2 : Blocks := edgeBlocks% "full/vectors/0000111101-V-0002.bin"
noncomputable def vp0000111101 : Blocks := (Blocks.join vp0000111101_0 (Blocks.join vp0000111101_1 vp0000111101_2))
private theorem bp00001111010 : Branch 0 (-487761639/8000000 : ℚ) vp0000111101 := by
  apply branch_left_normalized (c:=vp00001111010) (k:=0) (m:=198) (by decide +kernel)
  rw [show 2*(-487761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-487761639/4000000 : ℚ) by norm_num]
  exact coverp00001111010
private noncomputable def ep00001111011_0 : Blocks := edgeBlocks% "full/vectors/00001111011-E-0000.bin"
private noncomputable def ep00001111011_1 : Blocks := edgeBlocks% "full/vectors/00001111011-E-0001.bin"
private noncomputable def ep00001111011_2 : Blocks := edgeBlocks% "full/vectors/00001111011-E-0002.bin"
noncomputable def ep00001111011 : Blocks := (Blocks.join ep00001111011_0 (Blocks.join ep00001111011_1 ep00001111011_2))
private theorem idp00001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111101.list =
    C ((2:ℤ)^400) * horner X vp00001111011.list + horner X ep00001111011.list := by
  exact edge_identity (B := (2:ℤ)^664) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111011 : Branch 1 (-487761639/8000000 : ℚ) vp0000111101 := by
  apply branch_checked idp00001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-487761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-491761639/4000000 : ℚ) by norm_num]
  exact coverp00001111011
theorem coverp0000111101 : Covers (-487761639/8000000 : ℚ) vp0000111101 := join_branches bp00001111010 bp00001111011
private noncomputable def vp00001111001111_0 : Blocks := edgeBlocks% "full/vectors/00001111001111-V-0000.bin"
noncomputable def vp00001111001111 : Blocks := vp00001111001111_0
theorem coverp00001111001111 : Covers (-487261639/500000 : ℚ) vp00001111001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111001110_0 : Blocks := edgeBlocks% "full/vectors/00001111001110-V-0000.bin"
noncomputable def vp00001111001110 : Blocks := vp00001111001110_0
theorem coverp00001111001110 : Covers (-486761639/500000 : ℚ) vp00001111001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111100111_0 : Blocks := edgeBlocks% "full/vectors/0000111100111-V-0000.bin"
noncomputable def vp0000111100111 : Blocks := vp0000111100111_0
private theorem bp00001111001110 : Branch 0 (-486761639/1000000 : ℚ) vp0000111100111 := by
  apply branch_left_normalized (c:=vp00001111001110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-486761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-486761639/500000 : ℚ) by norm_num]
  exact coverp00001111001110
private noncomputable def ep00001111001111_0 : Blocks := edgeBlocks% "full/vectors/00001111001111-E-0000.bin"
noncomputable def ep00001111001111 : Blocks := ep00001111001111_0
private theorem idp00001111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111100111.list =
    C ((2:ℤ)^68) * horner X vp00001111001111.list + horner X ep00001111001111.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111001111 : Branch 1 (-486761639/1000000 : ℚ) vp0000111100111 := by
  apply branch_checked idp00001111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-486761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-487261639/500000 : ℚ) by norm_num]
  exact coverp00001111001111
theorem coverp0000111100111 : Covers (-486761639/1000000 : ℚ) vp0000111100111 := join_branches bp00001111001110 bp00001111001111
private noncomputable def vp00001111001101_0 : Blocks := edgeBlocks% "full/vectors/00001111001101-V-0000.bin"
noncomputable def vp00001111001101 : Blocks := vp00001111001101_0
theorem coverp00001111001101 : Covers (-486261639/500000 : ℚ) vp00001111001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111001100_0 : Blocks := edgeBlocks% "full/vectors/00001111001100-V-0000.bin"
noncomputable def vp00001111001100 : Blocks := vp00001111001100_0
theorem coverp00001111001100 : Covers (-485761639/500000 : ℚ) vp00001111001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111100110_0 : Blocks := edgeBlocks% "full/vectors/0000111100110-V-0000.bin"
noncomputable def vp0000111100110 : Blocks := vp0000111100110_0
private theorem bp00001111001100 : Branch 0 (-485761639/1000000 : ℚ) vp0000111100110 := by
  apply branch_left_normalized (c:=vp00001111001100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-485761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-485761639/500000 : ℚ) by norm_num]
  exact coverp00001111001100
private noncomputable def ep00001111001101_0 : Blocks := edgeBlocks% "full/vectors/00001111001101-E-0000.bin"
noncomputable def ep00001111001101 : Blocks := ep00001111001101_0
private theorem idp00001111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111100110.list =
    C ((2:ℤ)^69) * horner X vp00001111001101.list + horner X ep00001111001101.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111001101 : Branch 1 (-485761639/1000000 : ℚ) vp0000111100110 := by
  apply branch_checked idp00001111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-485761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-486261639/500000 : ℚ) by norm_num]
  exact coverp00001111001101
theorem coverp0000111100110 : Covers (-485761639/1000000 : ℚ) vp0000111100110 := join_branches bp00001111001100 bp00001111001101
private noncomputable def vp000011110011_0 : Blocks := edgeBlocks% "full/vectors/000011110011-V-0000.bin"
noncomputable def vp000011110011 : Blocks := vp000011110011_0
private theorem bp0000111100110 : Branch 0 (-485761639/2000000 : ℚ) vp000011110011 := by
  apply branch_left_normalized (c:=vp0000111100110) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-485761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-485761639/1000000 : ℚ) by norm_num]
  exact coverp0000111100110
private noncomputable def ep0000111100111_0 : Blocks := edgeBlocks% "full/vectors/0000111100111-E-0000.bin"
noncomputable def ep0000111100111 : Blocks := ep0000111100111_0
private theorem idp0000111100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011110011.list =
    C ((2:ℤ)^117) * horner X vp0000111100111.list + horner X ep0000111100111.list := by
  exact edge_identity (B := (2:ℤ)^258) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111100111 : Branch 1 (-485761639/2000000 : ℚ) vp000011110011 := by
  apply branch_checked idp0000111100111 (by positivity) (by decide +kernel)
  rw [show 2*(-485761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-486761639/1000000 : ℚ) by norm_num]
  exact coverp0000111100111
theorem coverp000011110011 : Covers (-485761639/2000000 : ℚ) vp000011110011 := join_branches bp0000111100110 bp0000111100111
private noncomputable def vp00001111001011_0 : Blocks := edgeBlocks% "full/vectors/00001111001011-V-0000.bin"
noncomputable def vp00001111001011 : Blocks := vp00001111001011_0
theorem coverp00001111001011 : Covers (-485261639/500000 : ℚ) vp00001111001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111001010_0 : Blocks := edgeBlocks% "full/vectors/00001111001010-V-0000.bin"
noncomputable def vp00001111001010 : Blocks := vp00001111001010_0
theorem coverp00001111001010 : Covers (-484761639/500000 : ℚ) vp00001111001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111100101_0 : Blocks := edgeBlocks% "full/vectors/0000111100101-V-0000.bin"
noncomputable def vp0000111100101 : Blocks := vp0000111100101_0
private theorem bp00001111001010 : Branch 0 (-484761639/1000000 : ℚ) vp0000111100101 := by
  apply branch_left_normalized (c:=vp00001111001010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-484761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-484761639/500000 : ℚ) by norm_num]
  exact coverp00001111001010
private noncomputable def ep00001111001011_0 : Blocks := edgeBlocks% "full/vectors/00001111001011-E-0000.bin"
noncomputable def ep00001111001011 : Blocks := ep00001111001011_0
private theorem idp00001111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111100101.list =
    C ((2:ℤ)^68) * horner X vp00001111001011.list + horner X ep00001111001011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111001011 : Branch 1 (-484761639/1000000 : ℚ) vp0000111100101 := by
  apply branch_checked idp00001111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-484761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-485261639/500000 : ℚ) by norm_num]
  exact coverp00001111001011
theorem coverp0000111100101 : Covers (-484761639/1000000 : ℚ) vp0000111100101 := join_branches bp00001111001010 bp00001111001011
private noncomputable def vp00001111001001_0 : Blocks := edgeBlocks% "full/vectors/00001111001001-V-0000.bin"
noncomputable def vp00001111001001 : Blocks := vp00001111001001_0
theorem coverp00001111001001 : Covers (-484261639/500000 : ℚ) vp00001111001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111001000_0 : Blocks := edgeBlocks% "full/vectors/00001111001000-V-0000.bin"
noncomputable def vp00001111001000 : Blocks := vp00001111001000_0
theorem coverp00001111001000 : Covers (-483761639/500000 : ℚ) vp00001111001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111100100_0 : Blocks := edgeBlocks% "full/vectors/0000111100100-V-0000.bin"
noncomputable def vp0000111100100 : Blocks := vp0000111100100_0
private theorem bp00001111001000 : Branch 0 (-483761639/1000000 : ℚ) vp0000111100100 := by
  apply branch_left_normalized (c:=vp00001111001000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-483761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-483761639/500000 : ℚ) by norm_num]
  exact coverp00001111001000
private noncomputable def ep00001111001001_0 : Blocks := edgeBlocks% "full/vectors/00001111001001-E-0000.bin"
noncomputable def ep00001111001001 : Blocks := ep00001111001001_0
private theorem idp00001111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111100100.list =
    C ((2:ℤ)^69) * horner X vp00001111001001.list + horner X ep00001111001001.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111001001 : Branch 1 (-483761639/1000000 : ℚ) vp0000111100100 := by
  apply branch_checked idp00001111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-483761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-484261639/500000 : ℚ) by norm_num]
  exact coverp00001111001001
theorem coverp0000111100100 : Covers (-483761639/1000000 : ℚ) vp0000111100100 := join_branches bp00001111001000 bp00001111001001
private noncomputable def vp000011110010_0 : Blocks := edgeBlocks% "full/vectors/000011110010-V-0000.bin"
noncomputable def vp000011110010 : Blocks := vp000011110010_0
private theorem bp0000111100100 : Branch 0 (-483761639/2000000 : ℚ) vp000011110010 := by
  apply branch_left_normalized (c:=vp0000111100100) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-483761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-483761639/1000000 : ℚ) by norm_num]
  exact coverp0000111100100
private noncomputable def ep0000111100101_0 : Blocks := edgeBlocks% "full/vectors/0000111100101-E-0000.bin"
noncomputable def ep0000111100101 : Blocks := ep0000111100101_0
private theorem idp0000111100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011110010.list =
    C ((2:ℤ)^118) * horner X vp0000111100101.list + horner X ep0000111100101.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111100101 : Branch 1 (-483761639/2000000 : ℚ) vp000011110010 := by
  apply branch_checked idp0000111100101 (by positivity) (by decide +kernel)
  rw [show 2*(-483761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-484761639/1000000 : ℚ) by norm_num]
  exact coverp0000111100101
theorem coverp000011110010 : Covers (-483761639/2000000 : ℚ) vp000011110010 := join_branches bp0000111100100 bp0000111100101
private noncomputable def vp00001111001_0 : Blocks := edgeBlocks% "full/vectors/00001111001-V-0000.bin"
private noncomputable def vp00001111001_1 : Blocks := edgeBlocks% "full/vectors/00001111001-V-0001.bin"
noncomputable def vp00001111001 : Blocks := (Blocks.join vp00001111001_0 vp00001111001_1)
private theorem bp000011110010 : Branch 0 (-483761639/4000000 : ℚ) vp00001111001 := by
  apply branch_left_normalized (c:=vp000011110010) (k:=0) (m:=111) (by decide +kernel)
  rw [show 2*(-483761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-483761639/2000000 : ℚ) by norm_num]
  exact coverp000011110010
private noncomputable def ep000011110011_0 : Blocks := edgeBlocks% "full/vectors/000011110011-E-0000.bin"
private noncomputable def ep000011110011_1 : Blocks := edgeBlocks% "full/vectors/000011110011-E-0001.bin"
noncomputable def ep000011110011 : Blocks := (Blocks.join ep000011110011_0 ep000011110011_1)
private theorem idp000011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001111001.list =
    C ((2:ℤ)^215) * horner X vp000011110011.list + horner X ep000011110011.list := by
  exact edge_identity (B := (2:ℤ)^399) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011110011 : Branch 1 (-483761639/4000000 : ℚ) vp00001111001 := by
  apply branch_checked idp000011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-483761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-485761639/2000000 : ℚ) by norm_num]
  exact coverp000011110011
theorem coverp00001111001 : Covers (-483761639/4000000 : ℚ) vp00001111001 := join_branches bp000011110010 bp000011110011
private noncomputable def vp00001111000111_0 : Blocks := edgeBlocks% "full/vectors/00001111000111-V-0000.bin"
noncomputable def vp00001111000111 : Blocks := vp00001111000111_0
theorem coverp00001111000111 : Covers (-483261639/500000 : ℚ) vp00001111000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111000110_0 : Blocks := edgeBlocks% "full/vectors/00001111000110-V-0000.bin"
noncomputable def vp00001111000110 : Blocks := vp00001111000110_0
theorem coverp00001111000110 : Covers (-482761639/500000 : ℚ) vp00001111000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111100011_0 : Blocks := edgeBlocks% "full/vectors/0000111100011-V-0000.bin"
noncomputable def vp0000111100011 : Blocks := vp0000111100011_0
private theorem bp00001111000110 : Branch 0 (-482761639/1000000 : ℚ) vp0000111100011 := by
  apply branch_left_normalized (c:=vp00001111000110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-482761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-482761639/500000 : ℚ) by norm_num]
  exact coverp00001111000110
private noncomputable def ep00001111000111_0 : Blocks := edgeBlocks% "full/vectors/00001111000111-E-0000.bin"
noncomputable def ep00001111000111 : Blocks := ep00001111000111_0
private theorem idp00001111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111100011.list =
    C ((2:ℤ)^68) * horner X vp00001111000111.list + horner X ep00001111000111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111000111 : Branch 1 (-482761639/1000000 : ℚ) vp0000111100011 := by
  apply branch_checked idp00001111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-482761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-483261639/500000 : ℚ) by norm_num]
  exact coverp00001111000111
theorem coverp0000111100011 : Covers (-482761639/1000000 : ℚ) vp0000111100011 := join_branches bp00001111000110 bp00001111000111
private noncomputable def vp00001111000101_0 : Blocks := edgeBlocks% "full/vectors/00001111000101-V-0000.bin"
noncomputable def vp00001111000101 : Blocks := vp00001111000101_0
theorem coverp00001111000101 : Covers (-482261639/500000 : ℚ) vp00001111000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111000100_0 : Blocks := edgeBlocks% "full/vectors/00001111000100-V-0000.bin"
noncomputable def vp00001111000100 : Blocks := vp00001111000100_0
theorem coverp00001111000100 : Covers (-481761639/500000 : ℚ) vp00001111000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111100010_0 : Blocks := edgeBlocks% "full/vectors/0000111100010-V-0000.bin"
noncomputable def vp0000111100010 : Blocks := vp0000111100010_0
private theorem bp00001111000100 : Branch 0 (-481761639/1000000 : ℚ) vp0000111100010 := by
  apply branch_left_normalized (c:=vp00001111000100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-481761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-481761639/500000 : ℚ) by norm_num]
  exact coverp00001111000100
private noncomputable def ep00001111000101_0 : Blocks := edgeBlocks% "full/vectors/00001111000101-E-0000.bin"
noncomputable def ep00001111000101 : Blocks := ep00001111000101_0
private theorem idp00001111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111100010.list =
    C ((2:ℤ)^68) * horner X vp00001111000101.list + horner X ep00001111000101.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111000101 : Branch 1 (-481761639/1000000 : ℚ) vp0000111100010 := by
  apply branch_checked idp00001111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-481761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-482261639/500000 : ℚ) by norm_num]
  exact coverp00001111000101
theorem coverp0000111100010 : Covers (-481761639/1000000 : ℚ) vp0000111100010 := join_branches bp00001111000100 bp00001111000101
private noncomputable def vp000011110001_0 : Blocks := edgeBlocks% "full/vectors/000011110001-V-0000.bin"
noncomputable def vp000011110001 : Blocks := vp000011110001_0
private theorem bp0000111100010 : Branch 0 (-481761639/2000000 : ℚ) vp000011110001 := by
  apply branch_left_normalized (c:=vp0000111100010) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-481761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-481761639/1000000 : ℚ) by norm_num]
  exact coverp0000111100010
private noncomputable def ep0000111100011_0 : Blocks := edgeBlocks% "full/vectors/0000111100011-E-0000.bin"
noncomputable def ep0000111100011 : Blocks := ep0000111100011_0
private theorem idp0000111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011110001.list =
    C ((2:ℤ)^116) * horner X vp0000111100011.list + horner X ep0000111100011.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111100011 : Branch 1 (-481761639/2000000 : ℚ) vp000011110001 := by
  apply branch_checked idp0000111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-481761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-482761639/1000000 : ℚ) by norm_num]
  exact coverp0000111100011
theorem coverp000011110001 : Covers (-481761639/2000000 : ℚ) vp000011110001 := join_branches bp0000111100010 bp0000111100011
private noncomputable def vp00001111000011_0 : Blocks := edgeBlocks% "full/vectors/00001111000011-V-0000.bin"
noncomputable def vp00001111000011 : Blocks := vp00001111000011_0
theorem coverp00001111000011 : Covers (-481261639/500000 : ℚ) vp00001111000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111000010_0 : Blocks := edgeBlocks% "full/vectors/00001111000010-V-0000.bin"
noncomputable def vp00001111000010 : Blocks := vp00001111000010_0
theorem coverp00001111000010 : Covers (-480761639/500000 : ℚ) vp00001111000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111100001_0 : Blocks := edgeBlocks% "full/vectors/0000111100001-V-0000.bin"
noncomputable def vp0000111100001 : Blocks := vp0000111100001_0
private theorem bp00001111000010 : Branch 0 (-480761639/1000000 : ℚ) vp0000111100001 := by
  apply branch_left_normalized (c:=vp00001111000010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-480761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-480761639/500000 : ℚ) by norm_num]
  exact coverp00001111000010
private noncomputable def ep00001111000011_0 : Blocks := edgeBlocks% "full/vectors/00001111000011-E-0000.bin"
noncomputable def ep00001111000011 : Blocks := ep00001111000011_0
private theorem idp00001111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111100001.list =
    C ((2:ℤ)^69) * horner X vp00001111000011.list + horner X ep00001111000011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111000011 : Branch 1 (-480761639/1000000 : ℚ) vp0000111100001 := by
  apply branch_checked idp00001111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-480761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-481261639/500000 : ℚ) by norm_num]
  exact coverp00001111000011
theorem coverp0000111100001 : Covers (-480761639/1000000 : ℚ) vp0000111100001 := join_branches bp00001111000010 bp00001111000011
private noncomputable def vp00001111000001_0 : Blocks := edgeBlocks% "full/vectors/00001111000001-V-0000.bin"
noncomputable def vp00001111000001 : Blocks := vp00001111000001_0
theorem coverp00001111000001 : Covers (-480261639/500000 : ℚ) vp00001111000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001111000000_0 : Blocks := edgeBlocks% "full/vectors/00001111000000-V-0000.bin"
noncomputable def vp00001111000000 : Blocks := vp00001111000000_0
theorem coverp00001111000000 : Covers (-479761639/500000 : ℚ) vp00001111000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000111100000_0 : Blocks := edgeBlocks% "full/vectors/0000111100000-V-0000.bin"
noncomputable def vp0000111100000 : Blocks := vp0000111100000_0
private theorem bp00001111000000 : Branch 0 (-479761639/1000000 : ℚ) vp0000111100000 := by
  apply branch_left_normalized (c:=vp00001111000000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-479761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-479761639/500000 : ℚ) by norm_num]
  exact coverp00001111000000
private noncomputable def ep00001111000001_0 : Blocks := edgeBlocks% "full/vectors/00001111000001-E-0000.bin"
noncomputable def ep00001111000001 : Blocks := ep00001111000001_0
private theorem idp00001111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111100000.list =
    C ((2:ℤ)^69) * horner X vp00001111000001.list + horner X ep00001111000001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111000001 : Branch 1 (-479761639/1000000 : ℚ) vp0000111100000 := by
  apply branch_checked idp00001111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-479761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-480261639/500000 : ℚ) by norm_num]
  exact coverp00001111000001
theorem coverp0000111100000 : Covers (-479761639/1000000 : ℚ) vp0000111100000 := join_branches bp00001111000000 bp00001111000001
private noncomputable def vp000011110000_0 : Blocks := edgeBlocks% "full/vectors/000011110000-V-0000.bin"
noncomputable def vp000011110000 : Blocks := vp000011110000_0
private theorem bp0000111100000 : Branch 0 (-479761639/2000000 : ℚ) vp000011110000 := by
  apply branch_left_normalized (c:=vp0000111100000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-479761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-479761639/1000000 : ℚ) by norm_num]
  exact coverp0000111100000
private noncomputable def ep0000111100001_0 : Blocks := edgeBlocks% "full/vectors/0000111100001-E-0000.bin"
noncomputable def ep0000111100001 : Blocks := ep0000111100001_0
private theorem idp0000111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011110000.list =
    C ((2:ℤ)^117) * horner X vp0000111100001.list + horner X ep0000111100001.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111100001 : Branch 1 (-479761639/2000000 : ℚ) vp000011110000 := by
  apply branch_checked idp0000111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-479761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-480761639/1000000 : ℚ) by norm_num]
  exact coverp0000111100001
theorem coverp000011110000 : Covers (-479761639/2000000 : ℚ) vp000011110000 := join_branches bp0000111100000 bp0000111100001
private noncomputable def vp00001111000_0 : Blocks := edgeBlocks% "full/vectors/00001111000-V-0000.bin"
private noncomputable def vp00001111000_1 : Blocks := edgeBlocks% "full/vectors/00001111000-V-0001.bin"
noncomputable def vp00001111000 : Blocks := (Blocks.join vp00001111000_0 vp00001111000_1)
private theorem bp000011110000 : Branch 0 (-479761639/4000000 : ℚ) vp00001111000 := by
  apply branch_left_normalized (c:=vp000011110000) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-479761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-479761639/2000000 : ℚ) by norm_num]
  exact coverp000011110000
private noncomputable def ep000011110001_0 : Blocks := edgeBlocks% "full/vectors/000011110001-E-0000.bin"
private noncomputable def ep000011110001_1 : Blocks := edgeBlocks% "full/vectors/000011110001-E-0001.bin"
noncomputable def ep000011110001 : Blocks := (Blocks.join ep000011110001_0 ep000011110001_1)
private theorem idp000011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001111000.list =
    C ((2:ℤ)^214) * horner X vp000011110001.list + horner X ep000011110001.list := by
  exact edge_identity (B := (2:ℤ)^398) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011110001 : Branch 1 (-479761639/4000000 : ℚ) vp00001111000 := by
  apply branch_checked idp000011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-479761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-481761639/2000000 : ℚ) by norm_num]
  exact coverp000011110001
theorem coverp00001111000 : Covers (-479761639/4000000 : ℚ) vp00001111000 := join_branches bp000011110000 bp000011110001
private noncomputable def vp0000111100_0 : Blocks := edgeBlocks% "full/vectors/0000111100-V-0000.bin"
private noncomputable def vp0000111100_1 : Blocks := edgeBlocks% "full/vectors/0000111100-V-0001.bin"
private noncomputable def vp0000111100_2 : Blocks := edgeBlocks% "full/vectors/0000111100-V-0002.bin"
noncomputable def vp0000111100 : Blocks := (Blocks.join vp0000111100_0 (Blocks.join vp0000111100_1 vp0000111100_2))
private theorem bp00001111000 : Branch 0 (-479761639/8000000 : ℚ) vp0000111100 := by
  apply branch_left_normalized (c:=vp00001111000) (k:=0) (m:=201) (by decide +kernel)
  rw [show 2*(-479761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-479761639/4000000 : ℚ) by norm_num]
  exact coverp00001111000
private noncomputable def ep00001111001_0 : Blocks := edgeBlocks% "full/vectors/00001111001-E-0000.bin"
private noncomputable def ep00001111001_1 : Blocks := edgeBlocks% "full/vectors/00001111001-E-0001.bin"
private noncomputable def ep00001111001_2 : Blocks := edgeBlocks% "full/vectors/00001111001-E-0002.bin"
noncomputable def ep00001111001 : Blocks := (Blocks.join ep00001111001_0 (Blocks.join ep00001111001_1 ep00001111001_2))
private theorem idp00001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000111100.list =
    C ((2:ℤ)^403) * horner X vp00001111001.list + horner X ep00001111001.list := by
  exact edge_identity (B := (2:ℤ)^672) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001111001 : Branch 1 (-479761639/8000000 : ℚ) vp0000111100 := by
  apply branch_checked idp00001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-479761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-483761639/4000000 : ℚ) by norm_num]
  exact coverp00001111001
theorem coverp0000111100 : Covers (-479761639/8000000 : ℚ) vp0000111100 := join_branches bp00001111000 bp00001111001
private noncomputable def vp000011110_0 : Blocks := edgeBlocks% "full/vectors/000011110-V-0000.bin"
private noncomputable def vp000011110_1 : Blocks := edgeBlocks% "full/vectors/000011110-V-0001.bin"
private noncomputable def vp000011110_2 : Blocks := edgeBlocks% "full/vectors/000011110-V-0002.bin"
private noncomputable def vp000011110_3 : Blocks := edgeBlocks% "full/vectors/000011110-V-0003.bin"
private noncomputable def vp000011110_4 : Blocks := edgeBlocks% "full/vectors/000011110-V-0004.bin"
private noncomputable def vp000011110_5 : Blocks := edgeBlocks% "full/vectors/000011110-V-0005.bin"
noncomputable def vp000011110 : Blocks := (Blocks.join (Blocks.join vp000011110_0 (Blocks.join vp000011110_1 vp000011110_2)) (Blocks.join vp000011110_3 (Blocks.join vp000011110_4 vp000011110_5)))
private theorem bp0000111100 : Branch 0 (-479761639/16000000 : ℚ) vp000011110 := by
  apply branch_left_normalized (c:=vp0000111100) (k:=0) (m:=380) (by decide +kernel)
  rw [show 2*(-479761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-479761639/8000000 : ℚ) by norm_num]
  exact coverp0000111100
private noncomputable def ep0000111101_0 : Blocks := edgeBlocks% "full/vectors/0000111101-E-0000.bin"
private noncomputable def ep0000111101_1 : Blocks := edgeBlocks% "full/vectors/0000111101-E-0001.bin"
private noncomputable def ep0000111101_2 : Blocks := edgeBlocks% "full/vectors/0000111101-E-0002.bin"
private noncomputable def ep0000111101_3 : Blocks := edgeBlocks% "full/vectors/0000111101-E-0003.bin"
private noncomputable def ep0000111101_4 : Blocks := edgeBlocks% "full/vectors/0000111101-E-0004.bin"
private noncomputable def ep0000111101_5 : Blocks := edgeBlocks% "full/vectors/0000111101-E-0005.bin"
noncomputable def ep0000111101 : Blocks := (Blocks.join (Blocks.join ep0000111101_0 (Blocks.join ep0000111101_1 ep0000111101_2)) (Blocks.join ep0000111101_3 (Blocks.join ep0000111101_4 ep0000111101_5)))
private theorem idp0000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011110.list =
    C ((2:ℤ)^782) * horner X vp0000111101.list + horner X ep0000111101.list := by
  exact edge_identity (B := (2:ℤ)^1215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000111101 : Branch 1 (-479761639/16000000 : ℚ) vp000011110 := by
  apply branch_checked idp0000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-479761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-487761639/8000000 : ℚ) by norm_num]
  exact coverp0000111101
theorem coverp000011110 : Covers (-479761639/16000000 : ℚ) vp000011110 := join_branches bp0000111100 bp0000111101
private noncomputable def vp00001111_0 : Blocks := edgeBlocks% "full/vectors/00001111-V-0000.bin"
private noncomputable def vp00001111_1 : Blocks := edgeBlocks% "full/vectors/00001111-V-0001.bin"
private noncomputable def vp00001111_2 : Blocks := edgeBlocks% "full/vectors/00001111-V-0002.bin"
private noncomputable def vp00001111_3 : Blocks := edgeBlocks% "full/vectors/00001111-V-0003.bin"
private noncomputable def vp00001111_4 : Blocks := edgeBlocks% "full/vectors/00001111-V-0004.bin"
private noncomputable def vp00001111_5 : Blocks := edgeBlocks% "full/vectors/00001111-V-0005.bin"
private noncomputable def vp00001111_6 : Blocks := edgeBlocks% "full/vectors/00001111-V-0006.bin"
private noncomputable def vp00001111_7 : Blocks := edgeBlocks% "full/vectors/00001111-V-0007.bin"
private noncomputable def vp00001111_8 : Blocks := edgeBlocks% "full/vectors/00001111-V-0008.bin"
private noncomputable def vp00001111_9 : Blocks := edgeBlocks% "full/vectors/00001111-V-0009.bin"
private noncomputable def vp00001111_10 : Blocks := edgeBlocks% "full/vectors/00001111-V-0010.bin"
private noncomputable def vp00001111_11 : Blocks := edgeBlocks% "full/vectors/00001111-V-0011.bin"
noncomputable def vp00001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00001111_0 (Blocks.join vp00001111_1 vp00001111_2)) (Blocks.join vp00001111_3 (Blocks.join vp00001111_4 vp00001111_5))) (Blocks.join (Blocks.join vp00001111_6 (Blocks.join vp00001111_7 vp00001111_8)) (Blocks.join vp00001111_9 (Blocks.join vp00001111_10 vp00001111_11))))
private theorem bp000011110 : Branch 0 (-479761639/32000000 : ℚ) vp00001111 := by
  apply branch_left_normalized (c:=vp000011110) (k:=0) (m:=733) (by decide +kernel)
  rw [show 2*(-479761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-479761639/16000000 : ℚ) by norm_num]
  exact coverp000011110
private noncomputable def ep000011111_0 : Blocks := edgeBlocks% "full/vectors/000011111-E-0000.bin"
private noncomputable def ep000011111_1 : Blocks := edgeBlocks% "full/vectors/000011111-E-0001.bin"
private noncomputable def ep000011111_2 : Blocks := edgeBlocks% "full/vectors/000011111-E-0002.bin"
private noncomputable def ep000011111_3 : Blocks := edgeBlocks% "full/vectors/000011111-E-0003.bin"
private noncomputable def ep000011111_4 : Blocks := edgeBlocks% "full/vectors/000011111-E-0004.bin"
private noncomputable def ep000011111_5 : Blocks := edgeBlocks% "full/vectors/000011111-E-0005.bin"
private noncomputable def ep000011111_6 : Blocks := edgeBlocks% "full/vectors/000011111-E-0006.bin"
private noncomputable def ep000011111_7 : Blocks := edgeBlocks% "full/vectors/000011111-E-0007.bin"
private noncomputable def ep000011111_8 : Blocks := edgeBlocks% "full/vectors/000011111-E-0008.bin"
private noncomputable def ep000011111_9 : Blocks := edgeBlocks% "full/vectors/000011111-E-0009.bin"
private noncomputable def ep000011111_10 : Blocks := edgeBlocks% "full/vectors/000011111-E-0010.bin"
private noncomputable def ep000011111_11 : Blocks := edgeBlocks% "full/vectors/000011111-E-0011.bin"
noncomputable def ep000011111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000011111_0 (Blocks.join ep000011111_1 ep000011111_2)) (Blocks.join ep000011111_3 (Blocks.join ep000011111_4 ep000011111_5))) (Blocks.join (Blocks.join ep000011111_6 (Blocks.join ep000011111_7 ep000011111_8)) (Blocks.join ep000011111_9 (Blocks.join ep000011111_10 ep000011111_11))))
private theorem idp000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001111.list =
    C ((2:ℤ)^1528) * horner X vp000011111.list + horner X ep000011111.list := by
  exact edge_identity (B := (2:ℤ)^2286) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011111 : Branch 1 (-479761639/32000000 : ℚ) vp00001111 := by
  apply branch_checked idp000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-479761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-495761639/16000000 : ℚ) by norm_num]
  exact coverp000011111
theorem coverp00001111 : Covers (-479761639/32000000 : ℚ) vp00001111 := join_branches bp000011110 bp000011111
end NextProof.EdgeFull

