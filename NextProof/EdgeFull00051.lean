import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000010001111111_0 : Blocks := edgeBlocks% "full/vectors/000010001111111-V-0000.bin"
noncomputable def vp000010001111111 : Blocks := vp000010001111111_0
theorem coverp000010001111111 : Covers (-287511639/250000 : ℚ) vp000010001111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001111110_0 : Blocks := edgeBlocks% "full/vectors/000010001111110-V-0000.bin"
noncomputable def vp000010001111110 : Blocks := vp000010001111110_0
theorem coverp000010001111110 : Covers (-287261639/250000 : ℚ) vp000010001111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000111111_0 : Blocks := edgeBlocks% "full/vectors/00001000111111-V-0000.bin"
noncomputable def vp00001000111111 : Blocks := vp00001000111111_0
private theorem bp000010001111110 : Branch 0 (-287261639/500000 : ℚ) vp00001000111111 := by
  apply branch_left_normalized (c:=vp000010001111110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-287261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-287261639/250000 : ℚ) by norm_num]
  exact coverp000010001111110
private noncomputable def ep000010001111111_0 : Blocks := edgeBlocks% "full/vectors/000010001111111-E-0000.bin"
noncomputable def ep000010001111111 : Blocks := ep000010001111111_0
private theorem idp000010001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000111111.list =
    C ((2:ℤ)^50) * horner X vp000010001111111.list + horner X ep000010001111111.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001111111 : Branch 1 (-287261639/500000 : ℚ) vp00001000111111 := by
  apply branch_checked idp000010001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-287261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-287511639/250000 : ℚ) by norm_num]
  exact coverp000010001111111
theorem coverp00001000111111 : Covers (-287261639/500000 : ℚ) vp00001000111111 := join_branches bp000010001111110 bp000010001111111
private noncomputable def vp000010001111101_0 : Blocks := edgeBlocks% "full/vectors/000010001111101-V-0000.bin"
noncomputable def vp000010001111101 : Blocks := vp000010001111101_0
theorem coverp000010001111101 : Covers (-287011639/250000 : ℚ) vp000010001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001111100_0 : Blocks := edgeBlocks% "full/vectors/000010001111100-V-0000.bin"
noncomputable def vp000010001111100 : Blocks := vp000010001111100_0
theorem coverp000010001111100 : Covers (-286761639/250000 : ℚ) vp000010001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000111110_0 : Blocks := edgeBlocks% "full/vectors/00001000111110-V-0000.bin"
noncomputable def vp00001000111110 : Blocks := vp00001000111110_0
private theorem bp000010001111100 : Branch 0 (-286761639/500000 : ℚ) vp00001000111110 := by
  apply branch_left_normalized (c:=vp000010001111100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-286761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-286761639/250000 : ℚ) by norm_num]
  exact coverp000010001111100
private noncomputable def ep000010001111101_0 : Blocks := edgeBlocks% "full/vectors/000010001111101-E-0000.bin"
noncomputable def ep000010001111101 : Blocks := ep000010001111101_0
private theorem idp000010001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000111110.list =
    C ((2:ℤ)^51) * horner X vp000010001111101.list + horner X ep000010001111101.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001111101 : Branch 1 (-286761639/500000 : ℚ) vp00001000111110 := by
  apply branch_checked idp000010001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-286761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-287011639/250000 : ℚ) by norm_num]
  exact coverp000010001111101
theorem coverp00001000111110 : Covers (-286761639/500000 : ℚ) vp00001000111110 := join_branches bp000010001111100 bp000010001111101
private noncomputable def vp0000100011111_0 : Blocks := edgeBlocks% "full/vectors/0000100011111-V-0000.bin"
noncomputable def vp0000100011111 : Blocks := vp0000100011111_0
private theorem bp00001000111110 : Branch 0 (-286761639/1000000 : ℚ) vp0000100011111 := by
  apply branch_left_normalized (c:=vp00001000111110) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-286761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-286761639/500000 : ℚ) by norm_num]
  exact coverp00001000111110
private noncomputable def ep00001000111111_0 : Blocks := edgeBlocks% "full/vectors/00001000111111-E-0000.bin"
noncomputable def ep00001000111111 : Blocks := ep00001000111111_0
private theorem idp00001000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100011111.list =
    C ((2:ℤ)^83) * horner X vp00001000111111.list + horner X ep00001000111111.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000111111 : Branch 1 (-286761639/1000000 : ℚ) vp0000100011111 := by
  apply branch_checked idp00001000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-286761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-287261639/500000 : ℚ) by norm_num]
  exact coverp00001000111111
theorem coverp0000100011111 : Covers (-286761639/1000000 : ℚ) vp0000100011111 := join_branches bp00001000111110 bp00001000111111
private noncomputable def vp000010001111011_0 : Blocks := edgeBlocks% "full/vectors/000010001111011-V-0000.bin"
noncomputable def vp000010001111011 : Blocks := vp000010001111011_0
theorem coverp000010001111011 : Covers (-286511639/250000 : ℚ) vp000010001111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001111010_0 : Blocks := edgeBlocks% "full/vectors/000010001111010-V-0000.bin"
noncomputable def vp000010001111010 : Blocks := vp000010001111010_0
theorem coverp000010001111010 : Covers (-286261639/250000 : ℚ) vp000010001111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000111101_0 : Blocks := edgeBlocks% "full/vectors/00001000111101-V-0000.bin"
noncomputable def vp00001000111101 : Blocks := vp00001000111101_0
private theorem bp000010001111010 : Branch 0 (-286261639/500000 : ℚ) vp00001000111101 := by
  apply branch_left_normalized (c:=vp000010001111010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-286261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-286261639/250000 : ℚ) by norm_num]
  exact coverp000010001111010
private noncomputable def ep000010001111011_0 : Blocks := edgeBlocks% "full/vectors/000010001111011-E-0000.bin"
noncomputable def ep000010001111011 : Blocks := ep000010001111011_0
private theorem idp000010001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000111101.list =
    C ((2:ℤ)^51) * horner X vp000010001111011.list + horner X ep000010001111011.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001111011 : Branch 1 (-286261639/500000 : ℚ) vp00001000111101 := by
  apply branch_checked idp000010001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-286261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-286511639/250000 : ℚ) by norm_num]
  exact coverp000010001111011
theorem coverp00001000111101 : Covers (-286261639/500000 : ℚ) vp00001000111101 := join_branches bp000010001111010 bp000010001111011
private noncomputable def vp000010001111001_0 : Blocks := edgeBlocks% "full/vectors/000010001111001-V-0000.bin"
noncomputable def vp000010001111001 : Blocks := vp000010001111001_0
theorem coverp000010001111001 : Covers (-286011639/250000 : ℚ) vp000010001111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001111000_0 : Blocks := edgeBlocks% "full/vectors/000010001111000-V-0000.bin"
noncomputable def vp000010001111000 : Blocks := vp000010001111000_0
theorem coverp000010001111000 : Covers (-285761639/250000 : ℚ) vp000010001111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000111100_0 : Blocks := edgeBlocks% "full/vectors/00001000111100-V-0000.bin"
noncomputable def vp00001000111100 : Blocks := vp00001000111100_0
private theorem bp000010001111000 : Branch 0 (-285761639/500000 : ℚ) vp00001000111100 := by
  apply branch_left_normalized (c:=vp000010001111000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-285761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-285761639/250000 : ℚ) by norm_num]
  exact coverp000010001111000
private noncomputable def ep000010001111001_0 : Blocks := edgeBlocks% "full/vectors/000010001111001-E-0000.bin"
noncomputable def ep000010001111001 : Blocks := ep000010001111001_0
private theorem idp000010001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000111100.list =
    C ((2:ℤ)^51) * horner X vp000010001111001.list + horner X ep000010001111001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001111001 : Branch 1 (-285761639/500000 : ℚ) vp00001000111100 := by
  apply branch_checked idp000010001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-285761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-286011639/250000 : ℚ) by norm_num]
  exact coverp000010001111001
theorem coverp00001000111100 : Covers (-285761639/500000 : ℚ) vp00001000111100 := join_branches bp000010001111000 bp000010001111001
private noncomputable def vp0000100011110_0 : Blocks := edgeBlocks% "full/vectors/0000100011110-V-0000.bin"
noncomputable def vp0000100011110 : Blocks := vp0000100011110_0
private theorem bp00001000111100 : Branch 0 (-285761639/1000000 : ℚ) vp0000100011110 := by
  apply branch_left_normalized (c:=vp00001000111100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-285761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-285761639/500000 : ℚ) by norm_num]
  exact coverp00001000111100
private noncomputable def ep00001000111101_0 : Blocks := edgeBlocks% "full/vectors/00001000111101-E-0000.bin"
noncomputable def ep00001000111101 : Blocks := ep00001000111101_0
private theorem idp00001000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100011110.list =
    C ((2:ℤ)^83) * horner X vp00001000111101.list + horner X ep00001000111101.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000111101 : Branch 1 (-285761639/1000000 : ℚ) vp0000100011110 := by
  apply branch_checked idp00001000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-285761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-286261639/500000 : ℚ) by norm_num]
  exact coverp00001000111101
theorem coverp0000100011110 : Covers (-285761639/1000000 : ℚ) vp0000100011110 := join_branches bp00001000111100 bp00001000111101
private noncomputable def vp000010001111_0 : Blocks := edgeBlocks% "full/vectors/000010001111-V-0000.bin"
private noncomputable def vp000010001111_1 : Blocks := edgeBlocks% "full/vectors/000010001111-V-0001.bin"
noncomputable def vp000010001111 : Blocks := (Blocks.join vp000010001111_0 vp000010001111_1)
private theorem bp0000100011110 : Branch 0 (-285761639/2000000 : ℚ) vp000010001111 := by
  apply branch_left_normalized (c:=vp0000100011110) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-285761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-285761639/1000000 : ℚ) by norm_num]
  exact coverp0000100011110
private noncomputable def ep0000100011111_0 : Blocks := edgeBlocks% "full/vectors/0000100011111-E-0000.bin"
private noncomputable def ep0000100011111_1 : Blocks := edgeBlocks% "full/vectors/0000100011111-E-0001.bin"
noncomputable def ep0000100011111 : Blocks := (Blocks.join ep0000100011111_0 ep0000100011111_1)
private theorem idp0000100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010001111.list =
    C ((2:ℤ)^146) * horner X vp0000100011111.list + horner X ep0000100011111.list := by
  exact edge_identity (B := (2:ℤ)^304) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100011111 : Branch 1 (-285761639/2000000 : ℚ) vp000010001111 := by
  apply branch_checked idp0000100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-285761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-286761639/1000000 : ℚ) by norm_num]
  exact coverp0000100011111
theorem coverp000010001111 : Covers (-285761639/2000000 : ℚ) vp000010001111 := join_branches bp0000100011110 bp0000100011111
private noncomputable def vp000010001110111_0 : Blocks := edgeBlocks% "full/vectors/000010001110111-V-0000.bin"
noncomputable def vp000010001110111 : Blocks := vp000010001110111_0
theorem coverp000010001110111 : Covers (-285511639/250000 : ℚ) vp000010001110111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001110110_0 : Blocks := edgeBlocks% "full/vectors/000010001110110-V-0000.bin"
noncomputable def vp000010001110110 : Blocks := vp000010001110110_0
theorem coverp000010001110110 : Covers (-285261639/250000 : ℚ) vp000010001110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000111011_0 : Blocks := edgeBlocks% "full/vectors/00001000111011-V-0000.bin"
noncomputable def vp00001000111011 : Blocks := vp00001000111011_0
private theorem bp000010001110110 : Branch 0 (-285261639/500000 : ℚ) vp00001000111011 := by
  apply branch_left_normalized (c:=vp000010001110110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-285261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-285261639/250000 : ℚ) by norm_num]
  exact coverp000010001110110
private noncomputable def ep000010001110111_0 : Blocks := edgeBlocks% "full/vectors/000010001110111-E-0000.bin"
noncomputable def ep000010001110111 : Blocks := ep000010001110111_0
private theorem idp000010001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000111011.list =
    C ((2:ℤ)^52) * horner X vp000010001110111.list + horner X ep000010001110111.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001110111 : Branch 1 (-285261639/500000 : ℚ) vp00001000111011 := by
  apply branch_checked idp000010001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-285261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-285511639/250000 : ℚ) by norm_num]
  exact coverp000010001110111
theorem coverp00001000111011 : Covers (-285261639/500000 : ℚ) vp00001000111011 := join_branches bp000010001110110 bp000010001110111
private noncomputable def vp000010001110101_0 : Blocks := edgeBlocks% "full/vectors/000010001110101-V-0000.bin"
noncomputable def vp000010001110101 : Blocks := vp000010001110101_0
theorem coverp000010001110101 : Covers (-285011639/250000 : ℚ) vp000010001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001110100_0 : Blocks := edgeBlocks% "full/vectors/000010001110100-V-0000.bin"
noncomputable def vp000010001110100 : Blocks := vp000010001110100_0
theorem coverp000010001110100 : Covers (-284761639/250000 : ℚ) vp000010001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000111010_0 : Blocks := edgeBlocks% "full/vectors/00001000111010-V-0000.bin"
noncomputable def vp00001000111010 : Blocks := vp00001000111010_0
private theorem bp000010001110100 : Branch 0 (-284761639/500000 : ℚ) vp00001000111010 := by
  apply branch_left_normalized (c:=vp000010001110100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-284761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-284761639/250000 : ℚ) by norm_num]
  exact coverp000010001110100
private noncomputable def ep000010001110101_0 : Blocks := edgeBlocks% "full/vectors/000010001110101-E-0000.bin"
noncomputable def ep000010001110101 : Blocks := ep000010001110101_0
private theorem idp000010001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000111010.list =
    C ((2:ℤ)^50) * horner X vp000010001110101.list + horner X ep000010001110101.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001110101 : Branch 1 (-284761639/500000 : ℚ) vp00001000111010 := by
  apply branch_checked idp000010001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-284761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-285011639/250000 : ℚ) by norm_num]
  exact coverp000010001110101
theorem coverp00001000111010 : Covers (-284761639/500000 : ℚ) vp00001000111010 := join_branches bp000010001110100 bp000010001110101
private noncomputable def vp0000100011101_0 : Blocks := edgeBlocks% "full/vectors/0000100011101-V-0000.bin"
noncomputable def vp0000100011101 : Blocks := vp0000100011101_0
private theorem bp00001000111010 : Branch 0 (-284761639/1000000 : ℚ) vp0000100011101 := by
  apply branch_left_normalized (c:=vp00001000111010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-284761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-284761639/500000 : ℚ) by norm_num]
  exact coverp00001000111010
private noncomputable def ep00001000111011_0 : Blocks := edgeBlocks% "full/vectors/00001000111011-E-0000.bin"
noncomputable def ep00001000111011 : Blocks := ep00001000111011_0
private theorem idp00001000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100011101.list =
    C ((2:ℤ)^82) * horner X vp00001000111011.list + horner X ep00001000111011.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000111011 : Branch 1 (-284761639/1000000 : ℚ) vp0000100011101 := by
  apply branch_checked idp00001000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-284761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-285261639/500000 : ℚ) by norm_num]
  exact coverp00001000111011
theorem coverp0000100011101 : Covers (-284761639/1000000 : ℚ) vp0000100011101 := join_branches bp00001000111010 bp00001000111011
private noncomputable def vp000010001110011_0 : Blocks := edgeBlocks% "full/vectors/000010001110011-V-0000.bin"
noncomputable def vp000010001110011 : Blocks := vp000010001110011_0
theorem coverp000010001110011 : Covers (-284511639/250000 : ℚ) vp000010001110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001110010_0 : Blocks := edgeBlocks% "full/vectors/000010001110010-V-0000.bin"
noncomputable def vp000010001110010 : Blocks := vp000010001110010_0
theorem coverp000010001110010 : Covers (-284261639/250000 : ℚ) vp000010001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000111001_0 : Blocks := edgeBlocks% "full/vectors/00001000111001-V-0000.bin"
noncomputable def vp00001000111001 : Blocks := vp00001000111001_0
private theorem bp000010001110010 : Branch 0 (-284261639/500000 : ℚ) vp00001000111001 := by
  apply branch_left_normalized (c:=vp000010001110010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-284261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-284261639/250000 : ℚ) by norm_num]
  exact coverp000010001110010
private noncomputable def ep000010001110011_0 : Blocks := edgeBlocks% "full/vectors/000010001110011-E-0000.bin"
noncomputable def ep000010001110011 : Blocks := ep000010001110011_0
private theorem idp000010001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000111001.list =
    C ((2:ℤ)^51) * horner X vp000010001110011.list + horner X ep000010001110011.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001110011 : Branch 1 (-284261639/500000 : ℚ) vp00001000111001 := by
  apply branch_checked idp000010001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-284261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-284511639/250000 : ℚ) by norm_num]
  exact coverp000010001110011
theorem coverp00001000111001 : Covers (-284261639/500000 : ℚ) vp00001000111001 := join_branches bp000010001110010 bp000010001110011
private noncomputable def vp000010001110001_0 : Blocks := edgeBlocks% "full/vectors/000010001110001-V-0000.bin"
noncomputable def vp000010001110001 : Blocks := vp000010001110001_0
theorem coverp000010001110001 : Covers (-284011639/250000 : ℚ) vp000010001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001110000_0 : Blocks := edgeBlocks% "full/vectors/000010001110000-V-0000.bin"
noncomputable def vp000010001110000 : Blocks := vp000010001110000_0
theorem coverp000010001110000 : Covers (-283761639/250000 : ℚ) vp000010001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000111000_0 : Blocks := edgeBlocks% "full/vectors/00001000111000-V-0000.bin"
noncomputable def vp00001000111000 : Blocks := vp00001000111000_0
private theorem bp000010001110000 : Branch 0 (-283761639/500000 : ℚ) vp00001000111000 := by
  apply branch_left_normalized (c:=vp000010001110000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-283761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-283761639/250000 : ℚ) by norm_num]
  exact coverp000010001110000
private noncomputable def ep000010001110001_0 : Blocks := edgeBlocks% "full/vectors/000010001110001-E-0000.bin"
noncomputable def ep000010001110001 : Blocks := ep000010001110001_0
private theorem idp000010001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000111000.list =
    C ((2:ℤ)^51) * horner X vp000010001110001.list + horner X ep000010001110001.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001110001 : Branch 1 (-283761639/500000 : ℚ) vp00001000111000 := by
  apply branch_checked idp000010001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-283761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-284011639/250000 : ℚ) by norm_num]
  exact coverp000010001110001
theorem coverp00001000111000 : Covers (-283761639/500000 : ℚ) vp00001000111000 := join_branches bp000010001110000 bp000010001110001
private noncomputable def vp0000100011100_0 : Blocks := edgeBlocks% "full/vectors/0000100011100-V-0000.bin"
noncomputable def vp0000100011100 : Blocks := vp0000100011100_0
private theorem bp00001000111000 : Branch 0 (-283761639/1000000 : ℚ) vp0000100011100 := by
  apply branch_left_normalized (c:=vp00001000111000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-283761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-283761639/500000 : ℚ) by norm_num]
  exact coverp00001000111000
private noncomputable def ep00001000111001_0 : Blocks := edgeBlocks% "full/vectors/00001000111001-E-0000.bin"
noncomputable def ep00001000111001 : Blocks := ep00001000111001_0
private theorem idp00001000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100011100.list =
    C ((2:ℤ)^83) * horner X vp00001000111001.list + horner X ep00001000111001.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000111001 : Branch 1 (-283761639/1000000 : ℚ) vp0000100011100 := by
  apply branch_checked idp00001000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-283761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-284261639/500000 : ℚ) by norm_num]
  exact coverp00001000111001
theorem coverp0000100011100 : Covers (-283761639/1000000 : ℚ) vp0000100011100 := join_branches bp00001000111000 bp00001000111001
private noncomputable def vp000010001110_0 : Blocks := edgeBlocks% "full/vectors/000010001110-V-0000.bin"
private noncomputable def vp000010001110_1 : Blocks := edgeBlocks% "full/vectors/000010001110-V-0001.bin"
noncomputable def vp000010001110 : Blocks := (Blocks.join vp000010001110_0 vp000010001110_1)
private theorem bp0000100011100 : Branch 0 (-283761639/2000000 : ℚ) vp000010001110 := by
  apply branch_left_normalized (c:=vp0000100011100) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-283761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-283761639/1000000 : ℚ) by norm_num]
  exact coverp0000100011100
private noncomputable def ep0000100011101_0 : Blocks := edgeBlocks% "full/vectors/0000100011101-E-0000.bin"
private noncomputable def ep0000100011101_1 : Blocks := edgeBlocks% "full/vectors/0000100011101-E-0001.bin"
noncomputable def ep0000100011101 : Blocks := (Blocks.join ep0000100011101_0 ep0000100011101_1)
private theorem idp0000100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010001110.list =
    C ((2:ℤ)^146) * horner X vp0000100011101.list + horner X ep0000100011101.list := by
  exact edge_identity (B := (2:ℤ)^304) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100011101 : Branch 1 (-283761639/2000000 : ℚ) vp000010001110 := by
  apply branch_checked idp0000100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-283761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-284761639/1000000 : ℚ) by norm_num]
  exact coverp0000100011101
theorem coverp000010001110 : Covers (-283761639/2000000 : ℚ) vp000010001110 := join_branches bp0000100011100 bp0000100011101
private noncomputable def vp00001000111_0 : Blocks := edgeBlocks% "full/vectors/00001000111-V-0000.bin"
private noncomputable def vp00001000111_1 : Blocks := edgeBlocks% "full/vectors/00001000111-V-0001.bin"
private noncomputable def vp00001000111_2 : Blocks := edgeBlocks% "full/vectors/00001000111-V-0002.bin"
noncomputable def vp00001000111 : Blocks := (Blocks.join vp00001000111_0 (Blocks.join vp00001000111_1 vp00001000111_2))
private theorem bp000010001110 : Branch 0 (-283761639/4000000 : ℚ) vp00001000111 := by
  apply branch_left_normalized (c:=vp000010001110) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-283761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-283761639/2000000 : ℚ) by norm_num]
  exact coverp000010001110
private noncomputable def ep000010001111_0 : Blocks := edgeBlocks% "full/vectors/000010001111-E-0000.bin"
private noncomputable def ep000010001111_1 : Blocks := edgeBlocks% "full/vectors/000010001111-E-0001.bin"
private noncomputable def ep000010001111_2 : Blocks := edgeBlocks% "full/vectors/000010001111-E-0002.bin"
noncomputable def ep000010001111 : Blocks := (Blocks.join ep000010001111_0 (Blocks.join ep000010001111_1 ep000010001111_2))
private theorem idp000010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000111.list =
    C ((2:ℤ)^268) * horner X vp000010001111.list + horner X ep000010001111.list := by
  exact edge_identity (B := (2:ℤ)^483) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001111 : Branch 1 (-283761639/4000000 : ℚ) vp00001000111 := by
  apply branch_checked idp000010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-283761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-285761639/2000000 : ℚ) by norm_num]
  exact coverp000010001111
theorem coverp00001000111 : Covers (-283761639/4000000 : ℚ) vp00001000111 := join_branches bp000010001110 bp000010001111
private noncomputable def vp000010001101111_0 : Blocks := edgeBlocks% "full/vectors/000010001101111-V-0000.bin"
noncomputable def vp000010001101111 : Blocks := vp000010001101111_0
theorem coverp000010001101111 : Covers (-283511639/250000 : ℚ) vp000010001101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001101110_0 : Blocks := edgeBlocks% "full/vectors/000010001101110-V-0000.bin"
noncomputable def vp000010001101110 : Blocks := vp000010001101110_0
theorem coverp000010001101110 : Covers (-283261639/250000 : ℚ) vp000010001101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000110111_0 : Blocks := edgeBlocks% "full/vectors/00001000110111-V-0000.bin"
noncomputable def vp00001000110111 : Blocks := vp00001000110111_0
private theorem bp000010001101110 : Branch 0 (-283261639/500000 : ℚ) vp00001000110111 := by
  apply branch_left_normalized (c:=vp000010001101110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-283261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-283261639/250000 : ℚ) by norm_num]
  exact coverp000010001101110
private noncomputable def ep000010001101111_0 : Blocks := edgeBlocks% "full/vectors/000010001101111-E-0000.bin"
noncomputable def ep000010001101111 : Blocks := ep000010001101111_0
private theorem idp000010001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000110111.list =
    C ((2:ℤ)^50) * horner X vp000010001101111.list + horner X ep000010001101111.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001101111 : Branch 1 (-283261639/500000 : ℚ) vp00001000110111 := by
  apply branch_checked idp000010001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-283261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-283511639/250000 : ℚ) by norm_num]
  exact coverp000010001101111
theorem coverp00001000110111 : Covers (-283261639/500000 : ℚ) vp00001000110111 := join_branches bp000010001101110 bp000010001101111
private noncomputable def vp000010001101101_0 : Blocks := edgeBlocks% "full/vectors/000010001101101-V-0000.bin"
noncomputable def vp000010001101101 : Blocks := vp000010001101101_0
theorem coverp000010001101101 : Covers (-283011639/250000 : ℚ) vp000010001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001101100_0 : Blocks := edgeBlocks% "full/vectors/000010001101100-V-0000.bin"
noncomputable def vp000010001101100 : Blocks := vp000010001101100_0
theorem coverp000010001101100 : Covers (-282761639/250000 : ℚ) vp000010001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000110110_0 : Blocks := edgeBlocks% "full/vectors/00001000110110-V-0000.bin"
noncomputable def vp00001000110110 : Blocks := vp00001000110110_0
private theorem bp000010001101100 : Branch 0 (-282761639/500000 : ℚ) vp00001000110110 := by
  apply branch_left_normalized (c:=vp000010001101100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-282761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-282761639/250000 : ℚ) by norm_num]
  exact coverp000010001101100
private noncomputable def ep000010001101101_0 : Blocks := edgeBlocks% "full/vectors/000010001101101-E-0000.bin"
noncomputable def ep000010001101101 : Blocks := ep000010001101101_0
private theorem idp000010001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000110110.list =
    C ((2:ℤ)^51) * horner X vp000010001101101.list + horner X ep000010001101101.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001101101 : Branch 1 (-282761639/500000 : ℚ) vp00001000110110 := by
  apply branch_checked idp000010001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-282761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-283011639/250000 : ℚ) by norm_num]
  exact coverp000010001101101
theorem coverp00001000110110 : Covers (-282761639/500000 : ℚ) vp00001000110110 := join_branches bp000010001101100 bp000010001101101
private noncomputable def vp0000100011011_0 : Blocks := edgeBlocks% "full/vectors/0000100011011-V-0000.bin"
noncomputable def vp0000100011011 : Blocks := vp0000100011011_0
private theorem bp00001000110110 : Branch 0 (-282761639/1000000 : ℚ) vp0000100011011 := by
  apply branch_left_normalized (c:=vp00001000110110) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-282761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-282761639/500000 : ℚ) by norm_num]
  exact coverp00001000110110
private noncomputable def ep00001000110111_0 : Blocks := edgeBlocks% "full/vectors/00001000110111-E-0000.bin"
noncomputable def ep00001000110111 : Blocks := ep00001000110111_0
private theorem idp00001000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100011011.list =
    C ((2:ℤ)^84) * horner X vp00001000110111.list + horner X ep00001000110111.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000110111 : Branch 1 (-282761639/1000000 : ℚ) vp0000100011011 := by
  apply branch_checked idp00001000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-282761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-283261639/500000 : ℚ) by norm_num]
  exact coverp00001000110111
theorem coverp0000100011011 : Covers (-282761639/1000000 : ℚ) vp0000100011011 := join_branches bp00001000110110 bp00001000110111
private noncomputable def vp000010001101011_0 : Blocks := edgeBlocks% "full/vectors/000010001101011-V-0000.bin"
noncomputable def vp000010001101011 : Blocks := vp000010001101011_0
theorem coverp000010001101011 : Covers (-282511639/250000 : ℚ) vp000010001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001101010_0 : Blocks := edgeBlocks% "full/vectors/000010001101010-V-0000.bin"
noncomputable def vp000010001101010 : Blocks := vp000010001101010_0
theorem coverp000010001101010 : Covers (-282261639/250000 : ℚ) vp000010001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000110101_0 : Blocks := edgeBlocks% "full/vectors/00001000110101-V-0000.bin"
noncomputable def vp00001000110101 : Blocks := vp00001000110101_0
private theorem bp000010001101010 : Branch 0 (-282261639/500000 : ℚ) vp00001000110101 := by
  apply branch_left_normalized (c:=vp000010001101010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-282261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-282261639/250000 : ℚ) by norm_num]
  exact coverp000010001101010
private noncomputable def ep000010001101011_0 : Blocks := edgeBlocks% "full/vectors/000010001101011-E-0000.bin"
noncomputable def ep000010001101011 : Blocks := ep000010001101011_0
private theorem idp000010001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000110101.list =
    C ((2:ℤ)^52) * horner X vp000010001101011.list + horner X ep000010001101011.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001101011 : Branch 1 (-282261639/500000 : ℚ) vp00001000110101 := by
  apply branch_checked idp000010001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-282261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-282511639/250000 : ℚ) by norm_num]
  exact coverp000010001101011
theorem coverp00001000110101 : Covers (-282261639/500000 : ℚ) vp00001000110101 := join_branches bp000010001101010 bp000010001101011
private noncomputable def vp000010001101001_0 : Blocks := edgeBlocks% "full/vectors/000010001101001-V-0000.bin"
noncomputable def vp000010001101001 : Blocks := vp000010001101001_0
theorem coverp000010001101001 : Covers (-282011639/250000 : ℚ) vp000010001101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001101000_0 : Blocks := edgeBlocks% "full/vectors/000010001101000-V-0000.bin"
noncomputable def vp000010001101000 : Blocks := vp000010001101000_0
theorem coverp000010001101000 : Covers (-281761639/250000 : ℚ) vp000010001101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000110100_0 : Blocks := edgeBlocks% "full/vectors/00001000110100-V-0000.bin"
noncomputable def vp00001000110100 : Blocks := vp00001000110100_0
private theorem bp000010001101000 : Branch 0 (-281761639/500000 : ℚ) vp00001000110100 := by
  apply branch_left_normalized (c:=vp000010001101000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-281761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-281761639/250000 : ℚ) by norm_num]
  exact coverp000010001101000
private noncomputable def ep000010001101001_0 : Blocks := edgeBlocks% "full/vectors/000010001101001-E-0000.bin"
noncomputable def ep000010001101001 : Blocks := ep000010001101001_0
private theorem idp000010001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000110100.list =
    C ((2:ℤ)^51) * horner X vp000010001101001.list + horner X ep000010001101001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001101001 : Branch 1 (-281761639/500000 : ℚ) vp00001000110100 := by
  apply branch_checked idp000010001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-281761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-282011639/250000 : ℚ) by norm_num]
  exact coverp000010001101001
theorem coverp00001000110100 : Covers (-281761639/500000 : ℚ) vp00001000110100 := join_branches bp000010001101000 bp000010001101001
private noncomputable def vp0000100011010_0 : Blocks := edgeBlocks% "full/vectors/0000100011010-V-0000.bin"
noncomputable def vp0000100011010 : Blocks := vp0000100011010_0
private theorem bp00001000110100 : Branch 0 (-281761639/1000000 : ℚ) vp0000100011010 := by
  apply branch_left_normalized (c:=vp00001000110100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-281761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-281761639/500000 : ℚ) by norm_num]
  exact coverp00001000110100
private noncomputable def ep00001000110101_0 : Blocks := edgeBlocks% "full/vectors/00001000110101-E-0000.bin"
noncomputable def ep00001000110101 : Blocks := ep00001000110101_0
private theorem idp00001000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100011010.list =
    C ((2:ℤ)^84) * horner X vp00001000110101.list + horner X ep00001000110101.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000110101 : Branch 1 (-281761639/1000000 : ℚ) vp0000100011010 := by
  apply branch_checked idp00001000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-281761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-282261639/500000 : ℚ) by norm_num]
  exact coverp00001000110101
theorem coverp0000100011010 : Covers (-281761639/1000000 : ℚ) vp0000100011010 := join_branches bp00001000110100 bp00001000110101
private noncomputable def vp000010001101_0 : Blocks := edgeBlocks% "full/vectors/000010001101-V-0000.bin"
private noncomputable def vp000010001101_1 : Blocks := edgeBlocks% "full/vectors/000010001101-V-0001.bin"
noncomputable def vp000010001101 : Blocks := (Blocks.join vp000010001101_0 vp000010001101_1)
private theorem bp0000100011010 : Branch 0 (-281761639/2000000 : ℚ) vp000010001101 := by
  apply branch_left_normalized (c:=vp0000100011010) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-281761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-281761639/1000000 : ℚ) by norm_num]
  exact coverp0000100011010
private noncomputable def ep0000100011011_0 : Blocks := edgeBlocks% "full/vectors/0000100011011-E-0000.bin"
private noncomputable def ep0000100011011_1 : Blocks := edgeBlocks% "full/vectors/0000100011011-E-0001.bin"
noncomputable def ep0000100011011 : Blocks := (Blocks.join ep0000100011011_0 ep0000100011011_1)
private theorem idp0000100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010001101.list =
    C ((2:ℤ)^146) * horner X vp0000100011011.list + horner X ep0000100011011.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100011011 : Branch 1 (-281761639/2000000 : ℚ) vp000010001101 := by
  apply branch_checked idp0000100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-281761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-282761639/1000000 : ℚ) by norm_num]
  exact coverp0000100011011
theorem coverp000010001101 : Covers (-281761639/2000000 : ℚ) vp000010001101 := join_branches bp0000100011010 bp0000100011011
private noncomputable def vp000010001100111_0 : Blocks := edgeBlocks% "full/vectors/000010001100111-V-0000.bin"
noncomputable def vp000010001100111 : Blocks := vp000010001100111_0
theorem coverp000010001100111 : Covers (-281511639/250000 : ℚ) vp000010001100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001100110_0 : Blocks := edgeBlocks% "full/vectors/000010001100110-V-0000.bin"
noncomputable def vp000010001100110 : Blocks := vp000010001100110_0
theorem coverp000010001100110 : Covers (-281261639/250000 : ℚ) vp000010001100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000110011_0 : Blocks := edgeBlocks% "full/vectors/00001000110011-V-0000.bin"
noncomputable def vp00001000110011 : Blocks := vp00001000110011_0
private theorem bp000010001100110 : Branch 0 (-281261639/500000 : ℚ) vp00001000110011 := by
  apply branch_left_normalized (c:=vp000010001100110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-281261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-281261639/250000 : ℚ) by norm_num]
  exact coverp000010001100110
private noncomputable def ep000010001100111_0 : Blocks := edgeBlocks% "full/vectors/000010001100111-E-0000.bin"
noncomputable def ep000010001100111 : Blocks := ep000010001100111_0
private theorem idp000010001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000110011.list =
    C ((2:ℤ)^52) * horner X vp000010001100111.list + horner X ep000010001100111.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001100111 : Branch 1 (-281261639/500000 : ℚ) vp00001000110011 := by
  apply branch_checked idp000010001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-281261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-281511639/250000 : ℚ) by norm_num]
  exact coverp000010001100111
theorem coverp00001000110011 : Covers (-281261639/500000 : ℚ) vp00001000110011 := join_branches bp000010001100110 bp000010001100111
private noncomputable def vp000010001100101_0 : Blocks := edgeBlocks% "full/vectors/000010001100101-V-0000.bin"
noncomputable def vp000010001100101 : Blocks := vp000010001100101_0
theorem coverp000010001100101 : Covers (-281011639/250000 : ℚ) vp000010001100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001100100_0 : Blocks := edgeBlocks% "full/vectors/000010001100100-V-0000.bin"
noncomputable def vp000010001100100 : Blocks := vp000010001100100_0
theorem coverp000010001100100 : Covers (-280761639/250000 : ℚ) vp000010001100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000110010_0 : Blocks := edgeBlocks% "full/vectors/00001000110010-V-0000.bin"
noncomputable def vp00001000110010 : Blocks := vp00001000110010_0
private theorem bp000010001100100 : Branch 0 (-280761639/500000 : ℚ) vp00001000110010 := by
  apply branch_left_normalized (c:=vp000010001100100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-280761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-280761639/250000 : ℚ) by norm_num]
  exact coverp000010001100100
private noncomputable def ep000010001100101_0 : Blocks := edgeBlocks% "full/vectors/000010001100101-E-0000.bin"
noncomputable def ep000010001100101 : Blocks := ep000010001100101_0
private theorem idp000010001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000110010.list =
    C ((2:ℤ)^50) * horner X vp000010001100101.list + horner X ep000010001100101.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001100101 : Branch 1 (-280761639/500000 : ℚ) vp00001000110010 := by
  apply branch_checked idp000010001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-280761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-281011639/250000 : ℚ) by norm_num]
  exact coverp000010001100101
theorem coverp00001000110010 : Covers (-280761639/500000 : ℚ) vp00001000110010 := join_branches bp000010001100100 bp000010001100101
private noncomputable def vp0000100011001_0 : Blocks := edgeBlocks% "full/vectors/0000100011001-V-0000.bin"
noncomputable def vp0000100011001 : Blocks := vp0000100011001_0
private theorem bp00001000110010 : Branch 0 (-280761639/1000000 : ℚ) vp0000100011001 := by
  apply branch_left_normalized (c:=vp00001000110010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-280761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-280761639/500000 : ℚ) by norm_num]
  exact coverp00001000110010
private noncomputable def ep00001000110011_0 : Blocks := edgeBlocks% "full/vectors/00001000110011-E-0000.bin"
noncomputable def ep00001000110011 : Blocks := ep00001000110011_0
private theorem idp00001000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100011001.list =
    C ((2:ℤ)^83) * horner X vp00001000110011.list + horner X ep00001000110011.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000110011 : Branch 1 (-280761639/1000000 : ℚ) vp0000100011001 := by
  apply branch_checked idp00001000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-280761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-281261639/500000 : ℚ) by norm_num]
  exact coverp00001000110011
theorem coverp0000100011001 : Covers (-280761639/1000000 : ℚ) vp0000100011001 := join_branches bp00001000110010 bp00001000110011
private noncomputable def vp000010001100011_0 : Blocks := edgeBlocks% "full/vectors/000010001100011-V-0000.bin"
noncomputable def vp000010001100011 : Blocks := vp000010001100011_0
theorem coverp000010001100011 : Covers (-280511639/250000 : ℚ) vp000010001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001100010_0 : Blocks := edgeBlocks% "full/vectors/000010001100010-V-0000.bin"
noncomputable def vp000010001100010 : Blocks := vp000010001100010_0
theorem coverp000010001100010 : Covers (-280261639/250000 : ℚ) vp000010001100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000110001_0 : Blocks := edgeBlocks% "full/vectors/00001000110001-V-0000.bin"
noncomputable def vp00001000110001 : Blocks := vp00001000110001_0
private theorem bp000010001100010 : Branch 0 (-280261639/500000 : ℚ) vp00001000110001 := by
  apply branch_left_normalized (c:=vp000010001100010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-280261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-280261639/250000 : ℚ) by norm_num]
  exact coverp000010001100010
private noncomputable def ep000010001100011_0 : Blocks := edgeBlocks% "full/vectors/000010001100011-E-0000.bin"
noncomputable def ep000010001100011 : Blocks := ep000010001100011_0
private theorem idp000010001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000110001.list =
    C ((2:ℤ)^51) * horner X vp000010001100011.list + horner X ep000010001100011.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001100011 : Branch 1 (-280261639/500000 : ℚ) vp00001000110001 := by
  apply branch_checked idp000010001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-280261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-280511639/250000 : ℚ) by norm_num]
  exact coverp000010001100011
theorem coverp00001000110001 : Covers (-280261639/500000 : ℚ) vp00001000110001 := join_branches bp000010001100010 bp000010001100011
private noncomputable def vp000010001100001_0 : Blocks := edgeBlocks% "full/vectors/000010001100001-V-0000.bin"
noncomputable def vp000010001100001 : Blocks := vp000010001100001_0
theorem coverp000010001100001 : Covers (-280011639/250000 : ℚ) vp000010001100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001100000_0 : Blocks := edgeBlocks% "full/vectors/000010001100000-V-0000.bin"
noncomputable def vp000010001100000 : Blocks := vp000010001100000_0
theorem coverp000010001100000 : Covers (-279761639/250000 : ℚ) vp000010001100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000110000_0 : Blocks := edgeBlocks% "full/vectors/00001000110000-V-0000.bin"
noncomputable def vp00001000110000 : Blocks := vp00001000110000_0
private theorem bp000010001100000 : Branch 0 (-279761639/500000 : ℚ) vp00001000110000 := by
  apply branch_left_normalized (c:=vp000010001100000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-279761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-279761639/250000 : ℚ) by norm_num]
  exact coverp000010001100000
private noncomputable def ep000010001100001_0 : Blocks := edgeBlocks% "full/vectors/000010001100001-E-0000.bin"
noncomputable def ep000010001100001 : Blocks := ep000010001100001_0
private theorem idp000010001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000110000.list =
    C ((2:ℤ)^51) * horner X vp000010001100001.list + horner X ep000010001100001.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001100001 : Branch 1 (-279761639/500000 : ℚ) vp00001000110000 := by
  apply branch_checked idp000010001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-279761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-280011639/250000 : ℚ) by norm_num]
  exact coverp000010001100001
theorem coverp00001000110000 : Covers (-279761639/500000 : ℚ) vp00001000110000 := join_branches bp000010001100000 bp000010001100001
private noncomputable def vp0000100011000_0 : Blocks := edgeBlocks% "full/vectors/0000100011000-V-0000.bin"
noncomputable def vp0000100011000 : Blocks := vp0000100011000_0
private theorem bp00001000110000 : Branch 0 (-279761639/1000000 : ℚ) vp0000100011000 := by
  apply branch_left_normalized (c:=vp00001000110000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-279761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-279761639/500000 : ℚ) by norm_num]
  exact coverp00001000110000
private noncomputable def ep00001000110001_0 : Blocks := edgeBlocks% "full/vectors/00001000110001-E-0000.bin"
noncomputable def ep00001000110001 : Blocks := ep00001000110001_0
private theorem idp00001000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100011000.list =
    C ((2:ℤ)^84) * horner X vp00001000110001.list + horner X ep00001000110001.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000110001 : Branch 1 (-279761639/1000000 : ℚ) vp0000100011000 := by
  apply branch_checked idp00001000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-279761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-280261639/500000 : ℚ) by norm_num]
  exact coverp00001000110001
theorem coverp0000100011000 : Covers (-279761639/1000000 : ℚ) vp0000100011000 := join_branches bp00001000110000 bp00001000110001
private noncomputable def vp000010001100_0 : Blocks := edgeBlocks% "full/vectors/000010001100-V-0000.bin"
private noncomputable def vp000010001100_1 : Blocks := edgeBlocks% "full/vectors/000010001100-V-0001.bin"
noncomputable def vp000010001100 : Blocks := (Blocks.join vp000010001100_0 vp000010001100_1)
private theorem bp0000100011000 : Branch 0 (-279761639/2000000 : ℚ) vp000010001100 := by
  apply branch_left_normalized (c:=vp0000100011000) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-279761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-279761639/1000000 : ℚ) by norm_num]
  exact coverp0000100011000
private noncomputable def ep0000100011001_0 : Blocks := edgeBlocks% "full/vectors/0000100011001-E-0000.bin"
private noncomputable def ep0000100011001_1 : Blocks := edgeBlocks% "full/vectors/0000100011001-E-0001.bin"
noncomputable def ep0000100011001 : Blocks := (Blocks.join ep0000100011001_0 ep0000100011001_1)
private theorem idp0000100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010001100.list =
    C ((2:ℤ)^147) * horner X vp0000100011001.list + horner X ep0000100011001.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100011001 : Branch 1 (-279761639/2000000 : ℚ) vp000010001100 := by
  apply branch_checked idp0000100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-279761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-280761639/1000000 : ℚ) by norm_num]
  exact coverp0000100011001
theorem coverp000010001100 : Covers (-279761639/2000000 : ℚ) vp000010001100 := join_branches bp0000100011000 bp0000100011001
private noncomputable def vp00001000110_0 : Blocks := edgeBlocks% "full/vectors/00001000110-V-0000.bin"
private noncomputable def vp00001000110_1 : Blocks := edgeBlocks% "full/vectors/00001000110-V-0001.bin"
private noncomputable def vp00001000110_2 : Blocks := edgeBlocks% "full/vectors/00001000110-V-0002.bin"
noncomputable def vp00001000110 : Blocks := (Blocks.join vp00001000110_0 (Blocks.join vp00001000110_1 vp00001000110_2))
private theorem bp000010001100 : Branch 0 (-279761639/4000000 : ℚ) vp00001000110 := by
  apply branch_left_normalized (c:=vp000010001100) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-279761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-279761639/2000000 : ℚ) by norm_num]
  exact coverp000010001100
private noncomputable def ep000010001101_0 : Blocks := edgeBlocks% "full/vectors/000010001101-E-0000.bin"
private noncomputable def ep000010001101_1 : Blocks := edgeBlocks% "full/vectors/000010001101-E-0001.bin"
private noncomputable def ep000010001101_2 : Blocks := edgeBlocks% "full/vectors/000010001101-E-0002.bin"
noncomputable def ep000010001101 : Blocks := (Blocks.join ep000010001101_0 (Blocks.join ep000010001101_1 ep000010001101_2))
private theorem idp000010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000110.list =
    C ((2:ℤ)^270) * horner X vp000010001101.list + horner X ep000010001101.list := by
  exact edge_identity (B := (2:ℤ)^486) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001101 : Branch 1 (-279761639/4000000 : ℚ) vp00001000110 := by
  apply branch_checked idp000010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-279761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-281761639/2000000 : ℚ) by norm_num]
  exact coverp000010001101
theorem coverp00001000110 : Covers (-279761639/4000000 : ℚ) vp00001000110 := join_branches bp000010001100 bp000010001101
private noncomputable def vp0000100011_0 : Blocks := edgeBlocks% "full/vectors/0000100011-V-0000.bin"
private noncomputable def vp0000100011_1 : Blocks := edgeBlocks% "full/vectors/0000100011-V-0001.bin"
private noncomputable def vp0000100011_2 : Blocks := edgeBlocks% "full/vectors/0000100011-V-0002.bin"
private noncomputable def vp0000100011_3 : Blocks := edgeBlocks% "full/vectors/0000100011-V-0003.bin"
noncomputable def vp0000100011 : Blocks := (Blocks.join (Blocks.join vp0000100011_0 vp0000100011_1) (Blocks.join vp0000100011_2 vp0000100011_3))
private theorem bp00001000110 : Branch 0 (-279761639/8000000 : ℚ) vp0000100011 := by
  apply branch_left_normalized (c:=vp00001000110) (k:=0) (m:=258) (by decide +kernel)
  rw [show 2*(-279761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-279761639/4000000 : ℚ) by norm_num]
  exact coverp00001000110
private noncomputable def ep00001000111_0 : Blocks := edgeBlocks% "full/vectors/00001000111-E-0000.bin"
private noncomputable def ep00001000111_1 : Blocks := edgeBlocks% "full/vectors/00001000111-E-0001.bin"
private noncomputable def ep00001000111_2 : Blocks := edgeBlocks% "full/vectors/00001000111-E-0002.bin"
private noncomputable def ep00001000111_3 : Blocks := edgeBlocks% "full/vectors/00001000111-E-0003.bin"
noncomputable def ep00001000111 : Blocks := (Blocks.join (Blocks.join ep00001000111_0 ep00001000111_1) (Blocks.join ep00001000111_2 ep00001000111_3))
private theorem idp00001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100011.list =
    C ((2:ℤ)^514) * horner X vp00001000111.list + horner X ep00001000111.list := by
  exact edge_identity (B := (2:ℤ)^842) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000111 : Branch 1 (-279761639/8000000 : ℚ) vp0000100011 := by
  apply branch_checked idp00001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-279761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-283761639/4000000 : ℚ) by norm_num]
  exact coverp00001000111
theorem coverp0000100011 : Covers (-279761639/8000000 : ℚ) vp0000100011 := join_branches bp00001000110 bp00001000111
private noncomputable def vp000010001011111_0 : Blocks := edgeBlocks% "full/vectors/000010001011111-V-0000.bin"
noncomputable def vp000010001011111 : Blocks := vp000010001011111_0
theorem coverp000010001011111 : Covers (-279511639/250000 : ℚ) vp000010001011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001011110_0 : Blocks := edgeBlocks% "full/vectors/000010001011110-V-0000.bin"
noncomputable def vp000010001011110 : Blocks := vp000010001011110_0
theorem coverp000010001011110 : Covers (-279261639/250000 : ℚ) vp000010001011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000101111_0 : Blocks := edgeBlocks% "full/vectors/00001000101111-V-0000.bin"
noncomputable def vp00001000101111 : Blocks := vp00001000101111_0
private theorem bp000010001011110 : Branch 0 (-279261639/500000 : ℚ) vp00001000101111 := by
  apply branch_left_normalized (c:=vp000010001011110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-279261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-279261639/250000 : ℚ) by norm_num]
  exact coverp000010001011110
private noncomputable def ep000010001011111_0 : Blocks := edgeBlocks% "full/vectors/000010001011111-E-0000.bin"
noncomputable def ep000010001011111 : Blocks := ep000010001011111_0
private theorem idp000010001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000101111.list =
    C ((2:ℤ)^50) * horner X vp000010001011111.list + horner X ep000010001011111.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001011111 : Branch 1 (-279261639/500000 : ℚ) vp00001000101111 := by
  apply branch_checked idp000010001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-279261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-279511639/250000 : ℚ) by norm_num]
  exact coverp000010001011111
theorem coverp00001000101111 : Covers (-279261639/500000 : ℚ) vp00001000101111 := join_branches bp000010001011110 bp000010001011111
private noncomputable def vp000010001011101_0 : Blocks := edgeBlocks% "full/vectors/000010001011101-V-0000.bin"
noncomputable def vp000010001011101 : Blocks := vp000010001011101_0
theorem coverp000010001011101 : Covers (-279011639/250000 : ℚ) vp000010001011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001011100_0 : Blocks := edgeBlocks% "full/vectors/000010001011100-V-0000.bin"
noncomputable def vp000010001011100 : Blocks := vp000010001011100_0
theorem coverp000010001011100 : Covers (-278761639/250000 : ℚ) vp000010001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000101110_0 : Blocks := edgeBlocks% "full/vectors/00001000101110-V-0000.bin"
noncomputable def vp00001000101110 : Blocks := vp00001000101110_0
private theorem bp000010001011100 : Branch 0 (-278761639/500000 : ℚ) vp00001000101110 := by
  apply branch_left_normalized (c:=vp000010001011100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-278761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-278761639/250000 : ℚ) by norm_num]
  exact coverp000010001011100
private noncomputable def ep000010001011101_0 : Blocks := edgeBlocks% "full/vectors/000010001011101-E-0000.bin"
noncomputable def ep000010001011101 : Blocks := ep000010001011101_0
private theorem idp000010001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000101110.list =
    C ((2:ℤ)^51) * horner X vp000010001011101.list + horner X ep000010001011101.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001011101 : Branch 1 (-278761639/500000 : ℚ) vp00001000101110 := by
  apply branch_checked idp000010001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-278761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-279011639/250000 : ℚ) by norm_num]
  exact coverp000010001011101
theorem coverp00001000101110 : Covers (-278761639/500000 : ℚ) vp00001000101110 := join_branches bp000010001011100 bp000010001011101
private noncomputable def vp0000100010111_0 : Blocks := edgeBlocks% "full/vectors/0000100010111-V-0000.bin"
noncomputable def vp0000100010111 : Blocks := vp0000100010111_0
private theorem bp00001000101110 : Branch 0 (-278761639/1000000 : ℚ) vp0000100010111 := by
  apply branch_left_normalized (c:=vp00001000101110) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-278761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-278761639/500000 : ℚ) by norm_num]
  exact coverp00001000101110
private noncomputable def ep00001000101111_0 : Blocks := edgeBlocks% "full/vectors/00001000101111-E-0000.bin"
noncomputable def ep00001000101111 : Blocks := ep00001000101111_0
private theorem idp00001000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100010111.list =
    C ((2:ℤ)^84) * horner X vp00001000101111.list + horner X ep00001000101111.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000101111 : Branch 1 (-278761639/1000000 : ℚ) vp0000100010111 := by
  apply branch_checked idp00001000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-278761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-279261639/500000 : ℚ) by norm_num]
  exact coverp00001000101111
theorem coverp0000100010111 : Covers (-278761639/1000000 : ℚ) vp0000100010111 := join_branches bp00001000101110 bp00001000101111
private noncomputable def vp000010001011011_0 : Blocks := edgeBlocks% "full/vectors/000010001011011-V-0000.bin"
noncomputable def vp000010001011011 : Blocks := vp000010001011011_0
theorem coverp000010001011011 : Covers (-278511639/250000 : ℚ) vp000010001011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001011010_0 : Blocks := edgeBlocks% "full/vectors/000010001011010-V-0000.bin"
noncomputable def vp000010001011010 : Blocks := vp000010001011010_0
theorem coverp000010001011010 : Covers (-278261639/250000 : ℚ) vp000010001011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000101101_0 : Blocks := edgeBlocks% "full/vectors/00001000101101-V-0000.bin"
noncomputable def vp00001000101101 : Blocks := vp00001000101101_0
private theorem bp000010001011010 : Branch 0 (-278261639/500000 : ℚ) vp00001000101101 := by
  apply branch_left_normalized (c:=vp000010001011010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-278261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-278261639/250000 : ℚ) by norm_num]
  exact coverp000010001011010
private noncomputable def ep000010001011011_0 : Blocks := edgeBlocks% "full/vectors/000010001011011-E-0000.bin"
noncomputable def ep000010001011011 : Blocks := ep000010001011011_0
private theorem idp000010001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000101101.list =
    C ((2:ℤ)^52) * horner X vp000010001011011.list + horner X ep000010001011011.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001011011 : Branch 1 (-278261639/500000 : ℚ) vp00001000101101 := by
  apply branch_checked idp000010001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-278261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-278511639/250000 : ℚ) by norm_num]
  exact coverp000010001011011
theorem coverp00001000101101 : Covers (-278261639/500000 : ℚ) vp00001000101101 := join_branches bp000010001011010 bp000010001011011
private noncomputable def vp000010001011001_0 : Blocks := edgeBlocks% "full/vectors/000010001011001-V-0000.bin"
noncomputable def vp000010001011001 : Blocks := vp000010001011001_0
theorem coverp000010001011001 : Covers (-278011639/250000 : ℚ) vp000010001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001011000_0 : Blocks := edgeBlocks% "full/vectors/000010001011000-V-0000.bin"
noncomputable def vp000010001011000 : Blocks := vp000010001011000_0
theorem coverp000010001011000 : Covers (-277761639/250000 : ℚ) vp000010001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000101100_0 : Blocks := edgeBlocks% "full/vectors/00001000101100-V-0000.bin"
noncomputable def vp00001000101100 : Blocks := vp00001000101100_0
private theorem bp000010001011000 : Branch 0 (-277761639/500000 : ℚ) vp00001000101100 := by
  apply branch_left_normalized (c:=vp000010001011000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-277761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-277761639/250000 : ℚ) by norm_num]
  exact coverp000010001011000
private noncomputable def ep000010001011001_0 : Blocks := edgeBlocks% "full/vectors/000010001011001-E-0000.bin"
noncomputable def ep000010001011001 : Blocks := ep000010001011001_0
private theorem idp000010001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000101100.list =
    C ((2:ℤ)^52) * horner X vp000010001011001.list + horner X ep000010001011001.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001011001 : Branch 1 (-277761639/500000 : ℚ) vp00001000101100 := by
  apply branch_checked idp000010001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-277761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-278011639/250000 : ℚ) by norm_num]
  exact coverp000010001011001
theorem coverp00001000101100 : Covers (-277761639/500000 : ℚ) vp00001000101100 := join_branches bp000010001011000 bp000010001011001
private noncomputable def vp0000100010110_0 : Blocks := edgeBlocks% "full/vectors/0000100010110-V-0000.bin"
noncomputable def vp0000100010110 : Blocks := vp0000100010110_0
private theorem bp00001000101100 : Branch 0 (-277761639/1000000 : ℚ) vp0000100010110 := by
  apply branch_left_normalized (c:=vp00001000101100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-277761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-277761639/500000 : ℚ) by norm_num]
  exact coverp00001000101100
private noncomputable def ep00001000101101_0 : Blocks := edgeBlocks% "full/vectors/00001000101101-E-0000.bin"
noncomputable def ep00001000101101 : Blocks := ep00001000101101_0
private theorem idp00001000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100010110.list =
    C ((2:ℤ)^84) * horner X vp00001000101101.list + horner X ep00001000101101.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000101101 : Branch 1 (-277761639/1000000 : ℚ) vp0000100010110 := by
  apply branch_checked idp00001000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-277761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-278261639/500000 : ℚ) by norm_num]
  exact coverp00001000101101
theorem coverp0000100010110 : Covers (-277761639/1000000 : ℚ) vp0000100010110 := join_branches bp00001000101100 bp00001000101101
private noncomputable def vp000010001011_0 : Blocks := edgeBlocks% "full/vectors/000010001011-V-0000.bin"
private noncomputable def vp000010001011_1 : Blocks := edgeBlocks% "full/vectors/000010001011-V-0001.bin"
noncomputable def vp000010001011 : Blocks := (Blocks.join vp000010001011_0 vp000010001011_1)
private theorem bp0000100010110 : Branch 0 (-277761639/2000000 : ℚ) vp000010001011 := by
  apply branch_left_normalized (c:=vp0000100010110) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-277761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-277761639/1000000 : ℚ) by norm_num]
  exact coverp0000100010110
private noncomputable def ep0000100010111_0 : Blocks := edgeBlocks% "full/vectors/0000100010111-E-0000.bin"
private noncomputable def ep0000100010111_1 : Blocks := edgeBlocks% "full/vectors/0000100010111-E-0001.bin"
noncomputable def ep0000100010111 : Blocks := (Blocks.join ep0000100010111_0 ep0000100010111_1)
private theorem idp0000100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010001011.list =
    C ((2:ℤ)^147) * horner X vp0000100010111.list + horner X ep0000100010111.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100010111 : Branch 1 (-277761639/2000000 : ℚ) vp000010001011 := by
  apply branch_checked idp0000100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-277761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-278761639/1000000 : ℚ) by norm_num]
  exact coverp0000100010111
theorem coverp000010001011 : Covers (-277761639/2000000 : ℚ) vp000010001011 := join_branches bp0000100010110 bp0000100010111
private noncomputable def vp000010001010111_0 : Blocks := edgeBlocks% "full/vectors/000010001010111-V-0000.bin"
noncomputable def vp000010001010111 : Blocks := vp000010001010111_0
theorem coverp000010001010111 : Covers (-277511639/250000 : ℚ) vp000010001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001010110_0 : Blocks := edgeBlocks% "full/vectors/000010001010110-V-0000.bin"
noncomputable def vp000010001010110 : Blocks := vp000010001010110_0
theorem coverp000010001010110 : Covers (-277261639/250000 : ℚ) vp000010001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000101011_0 : Blocks := edgeBlocks% "full/vectors/00001000101011-V-0000.bin"
noncomputable def vp00001000101011 : Blocks := vp00001000101011_0
private theorem bp000010001010110 : Branch 0 (-277261639/500000 : ℚ) vp00001000101011 := by
  apply branch_left_normalized (c:=vp000010001010110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-277261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-277261639/250000 : ℚ) by norm_num]
  exact coverp000010001010110
private noncomputable def ep000010001010111_0 : Blocks := edgeBlocks% "full/vectors/000010001010111-E-0000.bin"
noncomputable def ep000010001010111 : Blocks := ep000010001010111_0
private theorem idp000010001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000101011.list =
    C ((2:ℤ)^52) * horner X vp000010001010111.list + horner X ep000010001010111.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001010111 : Branch 1 (-277261639/500000 : ℚ) vp00001000101011 := by
  apply branch_checked idp000010001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-277261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-277511639/250000 : ℚ) by norm_num]
  exact coverp000010001010111
theorem coverp00001000101011 : Covers (-277261639/500000 : ℚ) vp00001000101011 := join_branches bp000010001010110 bp000010001010111
private noncomputable def vp000010001010101_0 : Blocks := edgeBlocks% "full/vectors/000010001010101-V-0000.bin"
noncomputable def vp000010001010101 : Blocks := vp000010001010101_0
theorem coverp000010001010101 : Covers (-277011639/250000 : ℚ) vp000010001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001010100_0 : Blocks := edgeBlocks% "full/vectors/000010001010100-V-0000.bin"
noncomputable def vp000010001010100 : Blocks := vp000010001010100_0
theorem coverp000010001010100 : Covers (-276761639/250000 : ℚ) vp000010001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000101010_0 : Blocks := edgeBlocks% "full/vectors/00001000101010-V-0000.bin"
noncomputable def vp00001000101010 : Blocks := vp00001000101010_0
private theorem bp000010001010100 : Branch 0 (-276761639/500000 : ℚ) vp00001000101010 := by
  apply branch_left_normalized (c:=vp000010001010100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-276761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-276761639/250000 : ℚ) by norm_num]
  exact coverp000010001010100
private noncomputable def ep000010001010101_0 : Blocks := edgeBlocks% "full/vectors/000010001010101-E-0000.bin"
noncomputable def ep000010001010101 : Blocks := ep000010001010101_0
private theorem idp000010001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000101010.list =
    C ((2:ℤ)^50) * horner X vp000010001010101.list + horner X ep000010001010101.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001010101 : Branch 1 (-276761639/500000 : ℚ) vp00001000101010 := by
  apply branch_checked idp000010001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-276761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-277011639/250000 : ℚ) by norm_num]
  exact coverp000010001010101
theorem coverp00001000101010 : Covers (-276761639/500000 : ℚ) vp00001000101010 := join_branches bp000010001010100 bp000010001010101
private noncomputable def vp0000100010101_0 : Blocks := edgeBlocks% "full/vectors/0000100010101-V-0000.bin"
noncomputable def vp0000100010101 : Blocks := vp0000100010101_0
private theorem bp00001000101010 : Branch 0 (-276761639/1000000 : ℚ) vp0000100010101 := by
  apply branch_left_normalized (c:=vp00001000101010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-276761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-276761639/500000 : ℚ) by norm_num]
  exact coverp00001000101010
private noncomputable def ep00001000101011_0 : Blocks := edgeBlocks% "full/vectors/00001000101011-E-0000.bin"
noncomputable def ep00001000101011 : Blocks := ep00001000101011_0
private theorem idp00001000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100010101.list =
    C ((2:ℤ)^83) * horner X vp00001000101011.list + horner X ep00001000101011.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000101011 : Branch 1 (-276761639/1000000 : ℚ) vp0000100010101 := by
  apply branch_checked idp00001000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-276761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-277261639/500000 : ℚ) by norm_num]
  exact coverp00001000101011
theorem coverp0000100010101 : Covers (-276761639/1000000 : ℚ) vp0000100010101 := join_branches bp00001000101010 bp00001000101011
private noncomputable def vp000010001010011_0 : Blocks := edgeBlocks% "full/vectors/000010001010011-V-0000.bin"
noncomputable def vp000010001010011 : Blocks := vp000010001010011_0
theorem coverp000010001010011 : Covers (-276511639/250000 : ℚ) vp000010001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001010010_0 : Blocks := edgeBlocks% "full/vectors/000010001010010-V-0000.bin"
noncomputable def vp000010001010010 : Blocks := vp000010001010010_0
theorem coverp000010001010010 : Covers (-276261639/250000 : ℚ) vp000010001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000101001_0 : Blocks := edgeBlocks% "full/vectors/00001000101001-V-0000.bin"
noncomputable def vp00001000101001 : Blocks := vp00001000101001_0
private theorem bp000010001010010 : Branch 0 (-276261639/500000 : ℚ) vp00001000101001 := by
  apply branch_left_normalized (c:=vp000010001010010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-276261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-276261639/250000 : ℚ) by norm_num]
  exact coverp000010001010010
private noncomputable def ep000010001010011_0 : Blocks := edgeBlocks% "full/vectors/000010001010011-E-0000.bin"
noncomputable def ep000010001010011 : Blocks := ep000010001010011_0
private theorem idp000010001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000101001.list =
    C ((2:ℤ)^51) * horner X vp000010001010011.list + horner X ep000010001010011.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001010011 : Branch 1 (-276261639/500000 : ℚ) vp00001000101001 := by
  apply branch_checked idp000010001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-276261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-276511639/250000 : ℚ) by norm_num]
  exact coverp000010001010011
theorem coverp00001000101001 : Covers (-276261639/500000 : ℚ) vp00001000101001 := join_branches bp000010001010010 bp000010001010011
private noncomputable def vp000010001010001_0 : Blocks := edgeBlocks% "full/vectors/000010001010001-V-0000.bin"
noncomputable def vp000010001010001 : Blocks := vp000010001010001_0
theorem coverp000010001010001 : Covers (-276011639/250000 : ℚ) vp000010001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001010000_0 : Blocks := edgeBlocks% "full/vectors/000010001010000-V-0000.bin"
noncomputable def vp000010001010000 : Blocks := vp000010001010000_0
theorem coverp000010001010000 : Covers (-275761639/250000 : ℚ) vp000010001010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000101000_0 : Blocks := edgeBlocks% "full/vectors/00001000101000-V-0000.bin"
noncomputable def vp00001000101000 : Blocks := vp00001000101000_0
private theorem bp000010001010000 : Branch 0 (-275761639/500000 : ℚ) vp00001000101000 := by
  apply branch_left_normalized (c:=vp000010001010000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-275761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-275761639/250000 : ℚ) by norm_num]
  exact coverp000010001010000
private noncomputable def ep000010001010001_0 : Blocks := edgeBlocks% "full/vectors/000010001010001-E-0000.bin"
noncomputable def ep000010001010001 : Blocks := ep000010001010001_0
private theorem idp000010001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000101000.list =
    C ((2:ℤ)^51) * horner X vp000010001010001.list + horner X ep000010001010001.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001010001 : Branch 1 (-275761639/500000 : ℚ) vp00001000101000 := by
  apply branch_checked idp000010001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-275761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-276011639/250000 : ℚ) by norm_num]
  exact coverp000010001010001
theorem coverp00001000101000 : Covers (-275761639/500000 : ℚ) vp00001000101000 := join_branches bp000010001010000 bp000010001010001
private noncomputable def vp0000100010100_0 : Blocks := edgeBlocks% "full/vectors/0000100010100-V-0000.bin"
noncomputable def vp0000100010100 : Blocks := vp0000100010100_0
private theorem bp00001000101000 : Branch 0 (-275761639/1000000 : ℚ) vp0000100010100 := by
  apply branch_left_normalized (c:=vp00001000101000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-275761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-275761639/500000 : ℚ) by norm_num]
  exact coverp00001000101000
private noncomputable def ep00001000101001_0 : Blocks := edgeBlocks% "full/vectors/00001000101001-E-0000.bin"
noncomputable def ep00001000101001 : Blocks := ep00001000101001_0
private theorem idp00001000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100010100.list =
    C ((2:ℤ)^85) * horner X vp00001000101001.list + horner X ep00001000101001.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000101001 : Branch 1 (-275761639/1000000 : ℚ) vp0000100010100 := by
  apply branch_checked idp00001000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-275761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-276261639/500000 : ℚ) by norm_num]
  exact coverp00001000101001
theorem coverp0000100010100 : Covers (-275761639/1000000 : ℚ) vp0000100010100 := join_branches bp00001000101000 bp00001000101001
private noncomputable def vp000010001010_0 : Blocks := edgeBlocks% "full/vectors/000010001010-V-0000.bin"
private noncomputable def vp000010001010_1 : Blocks := edgeBlocks% "full/vectors/000010001010-V-0001.bin"
noncomputable def vp000010001010 : Blocks := (Blocks.join vp000010001010_0 vp000010001010_1)
private theorem bp0000100010100 : Branch 0 (-275761639/2000000 : ℚ) vp000010001010 := by
  apply branch_left_normalized (c:=vp0000100010100) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-275761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-275761639/1000000 : ℚ) by norm_num]
  exact coverp0000100010100
private noncomputable def ep0000100010101_0 : Blocks := edgeBlocks% "full/vectors/0000100010101-E-0000.bin"
private noncomputable def ep0000100010101_1 : Blocks := edgeBlocks% "full/vectors/0000100010101-E-0001.bin"
noncomputable def ep0000100010101 : Blocks := (Blocks.join ep0000100010101_0 ep0000100010101_1)
private theorem idp0000100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010001010.list =
    C ((2:ℤ)^147) * horner X vp0000100010101.list + horner X ep0000100010101.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100010101 : Branch 1 (-275761639/2000000 : ℚ) vp000010001010 := by
  apply branch_checked idp0000100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-275761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-276761639/1000000 : ℚ) by norm_num]
  exact coverp0000100010101
theorem coverp000010001010 : Covers (-275761639/2000000 : ℚ) vp000010001010 := join_branches bp0000100010100 bp0000100010101
private noncomputable def vp00001000101_0 : Blocks := edgeBlocks% "full/vectors/00001000101-V-0000.bin"
private noncomputable def vp00001000101_1 : Blocks := edgeBlocks% "full/vectors/00001000101-V-0001.bin"
private noncomputable def vp00001000101_2 : Blocks := edgeBlocks% "full/vectors/00001000101-V-0002.bin"
noncomputable def vp00001000101 : Blocks := (Blocks.join vp00001000101_0 (Blocks.join vp00001000101_1 vp00001000101_2))
private theorem bp000010001010 : Branch 0 (-275761639/4000000 : ℚ) vp00001000101 := by
  apply branch_left_normalized (c:=vp000010001010) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-275761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-275761639/2000000 : ℚ) by norm_num]
  exact coverp000010001010
private noncomputable def ep000010001011_0 : Blocks := edgeBlocks% "full/vectors/000010001011-E-0000.bin"
private noncomputable def ep000010001011_1 : Blocks := edgeBlocks% "full/vectors/000010001011-E-0001.bin"
private noncomputable def ep000010001011_2 : Blocks := edgeBlocks% "full/vectors/000010001011-E-0002.bin"
noncomputable def ep000010001011 : Blocks := (Blocks.join ep000010001011_0 (Blocks.join ep000010001011_1 ep000010001011_2))
private theorem idp000010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000101.list =
    C ((2:ℤ)^271) * horner X vp000010001011.list + horner X ep000010001011.list := by
  exact edge_identity (B := (2:ℤ)^488) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001011 : Branch 1 (-275761639/4000000 : ℚ) vp00001000101 := by
  apply branch_checked idp000010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-275761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-277761639/2000000 : ℚ) by norm_num]
  exact coverp000010001011
theorem coverp00001000101 : Covers (-275761639/4000000 : ℚ) vp00001000101 := join_branches bp000010001010 bp000010001011
private noncomputable def vp000010001001111_0 : Blocks := edgeBlocks% "full/vectors/000010001001111-V-0000.bin"
noncomputable def vp000010001001111 : Blocks := vp000010001001111_0
theorem coverp000010001001111 : Covers (-275511639/250000 : ℚ) vp000010001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001001110_0 : Blocks := edgeBlocks% "full/vectors/000010001001110-V-0000.bin"
noncomputable def vp000010001001110 : Blocks := vp000010001001110_0
theorem coverp000010001001110 : Covers (-275261639/250000 : ℚ) vp000010001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000100111_0 : Blocks := edgeBlocks% "full/vectors/00001000100111-V-0000.bin"
noncomputable def vp00001000100111 : Blocks := vp00001000100111_0
private theorem bp000010001001110 : Branch 0 (-275261639/500000 : ℚ) vp00001000100111 := by
  apply branch_left_normalized (c:=vp000010001001110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-275261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-275261639/250000 : ℚ) by norm_num]
  exact coverp000010001001110
private noncomputable def ep000010001001111_0 : Blocks := edgeBlocks% "full/vectors/000010001001111-E-0000.bin"
noncomputable def ep000010001001111 : Blocks := ep000010001001111_0
private theorem idp000010001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000100111.list =
    C ((2:ℤ)^51) * horner X vp000010001001111.list + horner X ep000010001001111.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001001111 : Branch 1 (-275261639/500000 : ℚ) vp00001000100111 := by
  apply branch_checked idp000010001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-275261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-275511639/250000 : ℚ) by norm_num]
  exact coverp000010001001111
theorem coverp00001000100111 : Covers (-275261639/500000 : ℚ) vp00001000100111 := join_branches bp000010001001110 bp000010001001111
private noncomputable def vp000010001001101_0 : Blocks := edgeBlocks% "full/vectors/000010001001101-V-0000.bin"
noncomputable def vp000010001001101 : Blocks := vp000010001001101_0
theorem coverp000010001001101 : Covers (-275011639/250000 : ℚ) vp000010001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001001100_0 : Blocks := edgeBlocks% "full/vectors/000010001001100-V-0000.bin"
noncomputable def vp000010001001100 : Blocks := vp000010001001100_0
theorem coverp000010001001100 : Covers (-274761639/250000 : ℚ) vp000010001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000100110_0 : Blocks := edgeBlocks% "full/vectors/00001000100110-V-0000.bin"
noncomputable def vp00001000100110 : Blocks := vp00001000100110_0
private theorem bp000010001001100 : Branch 0 (-274761639/500000 : ℚ) vp00001000100110 := by
  apply branch_left_normalized (c:=vp000010001001100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-274761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-274761639/250000 : ℚ) by norm_num]
  exact coverp000010001001100
private noncomputable def ep000010001001101_0 : Blocks := edgeBlocks% "full/vectors/000010001001101-E-0000.bin"
noncomputable def ep000010001001101 : Blocks := ep000010001001101_0
private theorem idp000010001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000100110.list =
    C ((2:ℤ)^51) * horner X vp000010001001101.list + horner X ep000010001001101.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001001101 : Branch 1 (-274761639/500000 : ℚ) vp00001000100110 := by
  apply branch_checked idp000010001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-274761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-275011639/250000 : ℚ) by norm_num]
  exact coverp000010001001101
theorem coverp00001000100110 : Covers (-274761639/500000 : ℚ) vp00001000100110 := join_branches bp000010001001100 bp000010001001101
private noncomputable def vp0000100010011_0 : Blocks := edgeBlocks% "full/vectors/0000100010011-V-0000.bin"
noncomputable def vp0000100010011 : Blocks := vp0000100010011_0
private theorem bp00001000100110 : Branch 0 (-274761639/1000000 : ℚ) vp0000100010011 := by
  apply branch_left_normalized (c:=vp00001000100110) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-274761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-274761639/500000 : ℚ) by norm_num]
  exact coverp00001000100110
private noncomputable def ep00001000100111_0 : Blocks := edgeBlocks% "full/vectors/00001000100111-E-0000.bin"
noncomputable def ep00001000100111 : Blocks := ep00001000100111_0
private theorem idp00001000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100010011.list =
    C ((2:ℤ)^85) * horner X vp00001000100111.list + horner X ep00001000100111.list := by
  exact edge_identity (B := (2:ℤ)^216) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000100111 : Branch 1 (-274761639/1000000 : ℚ) vp0000100010011 := by
  apply branch_checked idp00001000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-274761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-275261639/500000 : ℚ) by norm_num]
  exact coverp00001000100111
theorem coverp0000100010011 : Covers (-274761639/1000000 : ℚ) vp0000100010011 := join_branches bp00001000100110 bp00001000100111
private noncomputable def vp000010001001011_0 : Blocks := edgeBlocks% "full/vectors/000010001001011-V-0000.bin"
noncomputable def vp000010001001011 : Blocks := vp000010001001011_0
theorem coverp000010001001011 : Covers (-274511639/250000 : ℚ) vp000010001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001001010_0 : Blocks := edgeBlocks% "full/vectors/000010001001010-V-0000.bin"
noncomputable def vp000010001001010 : Blocks := vp000010001001010_0
theorem coverp000010001001010 : Covers (-274261639/250000 : ℚ) vp000010001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000100101_0 : Blocks := edgeBlocks% "full/vectors/00001000100101-V-0000.bin"
noncomputable def vp00001000100101 : Blocks := vp00001000100101_0
private theorem bp000010001001010 : Branch 0 (-274261639/500000 : ℚ) vp00001000100101 := by
  apply branch_left_normalized (c:=vp000010001001010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-274261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-274261639/250000 : ℚ) by norm_num]
  exact coverp000010001001010
private noncomputable def ep000010001001011_0 : Blocks := edgeBlocks% "full/vectors/000010001001011-E-0000.bin"
noncomputable def ep000010001001011 : Blocks := ep000010001001011_0
private theorem idp000010001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000100101.list =
    C ((2:ℤ)^51) * horner X vp000010001001011.list + horner X ep000010001001011.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001001011 : Branch 1 (-274261639/500000 : ℚ) vp00001000100101 := by
  apply branch_checked idp000010001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-274261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-274511639/250000 : ℚ) by norm_num]
  exact coverp000010001001011
theorem coverp00001000100101 : Covers (-274261639/500000 : ℚ) vp00001000100101 := join_branches bp000010001001010 bp000010001001011
private noncomputable def vp000010001001001_0 : Blocks := edgeBlocks% "full/vectors/000010001001001-V-0000.bin"
noncomputable def vp000010001001001 : Blocks := vp000010001001001_0
theorem coverp000010001001001 : Covers (-274011639/250000 : ℚ) vp000010001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001001000_0 : Blocks := edgeBlocks% "full/vectors/000010001001000-V-0000.bin"
noncomputable def vp000010001001000 : Blocks := vp000010001001000_0
theorem coverp000010001001000 : Covers (-273761639/250000 : ℚ) vp000010001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000100100_0 : Blocks := edgeBlocks% "full/vectors/00001000100100-V-0000.bin"
noncomputable def vp00001000100100 : Blocks := vp00001000100100_0
private theorem bp000010001001000 : Branch 0 (-273761639/500000 : ℚ) vp00001000100100 := by
  apply branch_left_normalized (c:=vp000010001001000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-273761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-273761639/250000 : ℚ) by norm_num]
  exact coverp000010001001000
private noncomputable def ep000010001001001_0 : Blocks := edgeBlocks% "full/vectors/000010001001001-E-0000.bin"
noncomputable def ep000010001001001 : Blocks := ep000010001001001_0
private theorem idp000010001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000100100.list =
    C ((2:ℤ)^51) * horner X vp000010001001001.list + horner X ep000010001001001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001001001 : Branch 1 (-273761639/500000 : ℚ) vp00001000100100 := by
  apply branch_checked idp000010001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-273761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-274011639/250000 : ℚ) by norm_num]
  exact coverp000010001001001
theorem coverp00001000100100 : Covers (-273761639/500000 : ℚ) vp00001000100100 := join_branches bp000010001001000 bp000010001001001
private noncomputable def vp0000100010010_0 : Blocks := edgeBlocks% "full/vectors/0000100010010-V-0000.bin"
noncomputable def vp0000100010010 : Blocks := vp0000100010010_0
private theorem bp00001000100100 : Branch 0 (-273761639/1000000 : ℚ) vp0000100010010 := by
  apply branch_left_normalized (c:=vp00001000100100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-273761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-273761639/500000 : ℚ) by norm_num]
  exact coverp00001000100100
private noncomputable def ep00001000100101_0 : Blocks := edgeBlocks% "full/vectors/00001000100101-E-0000.bin"
noncomputable def ep00001000100101 : Blocks := ep00001000100101_0
private theorem idp00001000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100010010.list =
    C ((2:ℤ)^83) * horner X vp00001000100101.list + horner X ep00001000100101.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000100101 : Branch 1 (-273761639/1000000 : ℚ) vp0000100010010 := by
  apply branch_checked idp00001000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-273761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-274261639/500000 : ℚ) by norm_num]
  exact coverp00001000100101
theorem coverp0000100010010 : Covers (-273761639/1000000 : ℚ) vp0000100010010 := join_branches bp00001000100100 bp00001000100101
private noncomputable def vp000010001001_0 : Blocks := edgeBlocks% "full/vectors/000010001001-V-0000.bin"
private noncomputable def vp000010001001_1 : Blocks := edgeBlocks% "full/vectors/000010001001-V-0001.bin"
noncomputable def vp000010001001 : Blocks := (Blocks.join vp000010001001_0 vp000010001001_1)
private theorem bp0000100010010 : Branch 0 (-273761639/2000000 : ℚ) vp000010001001 := by
  apply branch_left_normalized (c:=vp0000100010010) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-273761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-273761639/1000000 : ℚ) by norm_num]
  exact coverp0000100010010
private noncomputable def ep0000100010011_0 : Blocks := edgeBlocks% "full/vectors/0000100010011-E-0000.bin"
private noncomputable def ep0000100010011_1 : Blocks := edgeBlocks% "full/vectors/0000100010011-E-0001.bin"
noncomputable def ep0000100010011 : Blocks := (Blocks.join ep0000100010011_0 ep0000100010011_1)
private theorem idp0000100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010001001.list =
    C ((2:ℤ)^147) * horner X vp0000100010011.list + horner X ep0000100010011.list := by
  exact edge_identity (B := (2:ℤ)^307) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100010011 : Branch 1 (-273761639/2000000 : ℚ) vp000010001001 := by
  apply branch_checked idp0000100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-273761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-274761639/1000000 : ℚ) by norm_num]
  exact coverp0000100010011
theorem coverp000010001001 : Covers (-273761639/2000000 : ℚ) vp000010001001 := join_branches bp0000100010010 bp0000100010011
private noncomputable def vp000010001000111_0 : Blocks := edgeBlocks% "full/vectors/000010001000111-V-0000.bin"
noncomputable def vp000010001000111 : Blocks := vp000010001000111_0
theorem coverp000010001000111 : Covers (-273511639/250000 : ℚ) vp000010001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001000110_0 : Blocks := edgeBlocks% "full/vectors/000010001000110-V-0000.bin"
noncomputable def vp000010001000110 : Blocks := vp000010001000110_0
theorem coverp000010001000110 : Covers (-273261639/250000 : ℚ) vp000010001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000100011_0 : Blocks := edgeBlocks% "full/vectors/00001000100011-V-0000.bin"
noncomputable def vp00001000100011 : Blocks := vp00001000100011_0
private theorem bp000010001000110 : Branch 0 (-273261639/500000 : ℚ) vp00001000100011 := by
  apply branch_left_normalized (c:=vp000010001000110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-273261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-273261639/250000 : ℚ) by norm_num]
  exact coverp000010001000110
private noncomputable def ep000010001000111_0 : Blocks := edgeBlocks% "full/vectors/000010001000111-E-0000.bin"
noncomputable def ep000010001000111 : Blocks := ep000010001000111_0
private theorem idp000010001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000100011.list =
    C ((2:ℤ)^51) * horner X vp000010001000111.list + horner X ep000010001000111.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001000111 : Branch 1 (-273261639/500000 : ℚ) vp00001000100011 := by
  apply branch_checked idp000010001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-273261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-273511639/250000 : ℚ) by norm_num]
  exact coverp000010001000111
theorem coverp00001000100011 : Covers (-273261639/500000 : ℚ) vp00001000100011 := join_branches bp000010001000110 bp000010001000111
private noncomputable def vp000010001000101_0 : Blocks := edgeBlocks% "full/vectors/000010001000101-V-0000.bin"
noncomputable def vp000010001000101 : Blocks := vp000010001000101_0
theorem coverp000010001000101 : Covers (-273011639/250000 : ℚ) vp000010001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001000100_0 : Blocks := edgeBlocks% "full/vectors/000010001000100-V-0000.bin"
noncomputable def vp000010001000100 : Blocks := vp000010001000100_0
theorem coverp000010001000100 : Covers (-272761639/250000 : ℚ) vp000010001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000100010_0 : Blocks := edgeBlocks% "full/vectors/00001000100010-V-0000.bin"
noncomputable def vp00001000100010 : Blocks := vp00001000100010_0
private theorem bp000010001000100 : Branch 0 (-272761639/500000 : ℚ) vp00001000100010 := by
  apply branch_left_normalized (c:=vp000010001000100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-272761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-272761639/250000 : ℚ) by norm_num]
  exact coverp000010001000100
private noncomputable def ep000010001000101_0 : Blocks := edgeBlocks% "full/vectors/000010001000101-E-0000.bin"
noncomputable def ep000010001000101 : Blocks := ep000010001000101_0
private theorem idp000010001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000100010.list =
    C ((2:ℤ)^52) * horner X vp000010001000101.list + horner X ep000010001000101.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001000101 : Branch 1 (-272761639/500000 : ℚ) vp00001000100010 := by
  apply branch_checked idp000010001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-272761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-273011639/250000 : ℚ) by norm_num]
  exact coverp000010001000101
theorem coverp00001000100010 : Covers (-272761639/500000 : ℚ) vp00001000100010 := join_branches bp000010001000100 bp000010001000101
private noncomputable def vp0000100010001_0 : Blocks := edgeBlocks% "full/vectors/0000100010001-V-0000.bin"
noncomputable def vp0000100010001 : Blocks := vp0000100010001_0
private theorem bp00001000100010 : Branch 0 (-272761639/1000000 : ℚ) vp0000100010001 := by
  apply branch_left_normalized (c:=vp00001000100010) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-272761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-272761639/500000 : ℚ) by norm_num]
  exact coverp00001000100010
private noncomputable def ep00001000100011_0 : Blocks := edgeBlocks% "full/vectors/00001000100011-E-0000.bin"
noncomputable def ep00001000100011 : Blocks := ep00001000100011_0
private theorem idp00001000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100010001.list =
    C ((2:ℤ)^84) * horner X vp00001000100011.list + horner X ep00001000100011.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000100011 : Branch 1 (-272761639/1000000 : ℚ) vp0000100010001 := by
  apply branch_checked idp00001000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-272761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-273261639/500000 : ℚ) by norm_num]
  exact coverp00001000100011
theorem coverp0000100010001 : Covers (-272761639/1000000 : ℚ) vp0000100010001 := join_branches bp00001000100010 bp00001000100011
private noncomputable def vp000010001000011_0 : Blocks := edgeBlocks% "full/vectors/000010001000011-V-0000.bin"
noncomputable def vp000010001000011 : Blocks := vp000010001000011_0
theorem coverp000010001000011 : Covers (-272511639/250000 : ℚ) vp000010001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001000010_0 : Blocks := edgeBlocks% "full/vectors/000010001000010-V-0000.bin"
noncomputable def vp000010001000010 : Blocks := vp000010001000010_0
theorem coverp000010001000010 : Covers (-272261639/250000 : ℚ) vp000010001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000100001_0 : Blocks := edgeBlocks% "full/vectors/00001000100001-V-0000.bin"
noncomputable def vp00001000100001 : Blocks := vp00001000100001_0
private theorem bp000010001000010 : Branch 0 (-272261639/500000 : ℚ) vp00001000100001 := by
  apply branch_left_normalized (c:=vp000010001000010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-272261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-272261639/250000 : ℚ) by norm_num]
  exact coverp000010001000010
private noncomputable def ep000010001000011_0 : Blocks := edgeBlocks% "full/vectors/000010001000011-E-0000.bin"
noncomputable def ep000010001000011 : Blocks := ep000010001000011_0
private theorem idp000010001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000100001.list =
    C ((2:ℤ)^52) * horner X vp000010001000011.list + horner X ep000010001000011.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001000011 : Branch 1 (-272261639/500000 : ℚ) vp00001000100001 := by
  apply branch_checked idp000010001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-272261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-272511639/250000 : ℚ) by norm_num]
  exact coverp000010001000011
theorem coverp00001000100001 : Covers (-272261639/500000 : ℚ) vp00001000100001 := join_branches bp000010001000010 bp000010001000011
private noncomputable def vp000010001000001_0 : Blocks := edgeBlocks% "full/vectors/000010001000001-V-0000.bin"
noncomputable def vp000010001000001 : Blocks := vp000010001000001_0
theorem coverp000010001000001 : Covers (-272011639/250000 : ℚ) vp000010001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010001000000_0 : Blocks := edgeBlocks% "full/vectors/000010001000000-V-0000.bin"
noncomputable def vp000010001000000 : Blocks := vp000010001000000_0
theorem coverp000010001000000 : Covers (-271761639/250000 : ℚ) vp000010001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000100000_0 : Blocks := edgeBlocks% "full/vectors/00001000100000-V-0000.bin"
noncomputable def vp00001000100000 : Blocks := vp00001000100000_0
private theorem bp000010001000000 : Branch 0 (-271761639/500000 : ℚ) vp00001000100000 := by
  apply branch_left_normalized (c:=vp000010001000000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-271761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-271761639/250000 : ℚ) by norm_num]
  exact coverp000010001000000
private noncomputable def ep000010001000001_0 : Blocks := edgeBlocks% "full/vectors/000010001000001-E-0000.bin"
noncomputable def ep000010001000001 : Blocks := ep000010001000001_0
private theorem idp000010001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000100000.list =
    C ((2:ℤ)^52) * horner X vp000010001000001.list + horner X ep000010001000001.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001000001 : Branch 1 (-271761639/500000 : ℚ) vp00001000100000 := by
  apply branch_checked idp000010001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-271761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-272011639/250000 : ℚ) by norm_num]
  exact coverp000010001000001
theorem coverp00001000100000 : Covers (-271761639/500000 : ℚ) vp00001000100000 := join_branches bp000010001000000 bp000010001000001
private noncomputable def vp0000100010000_0 : Blocks := edgeBlocks% "full/vectors/0000100010000-V-0000.bin"
noncomputable def vp0000100010000 : Blocks := vp0000100010000_0
private theorem bp00001000100000 : Branch 0 (-271761639/1000000 : ℚ) vp0000100010000 := by
  apply branch_left_normalized (c:=vp00001000100000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-271761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-271761639/500000 : ℚ) by norm_num]
  exact coverp00001000100000
private noncomputable def ep00001000100001_0 : Blocks := edgeBlocks% "full/vectors/00001000100001-E-0000.bin"
noncomputable def ep00001000100001 : Blocks := ep00001000100001_0
private theorem idp00001000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100010000.list =
    C ((2:ℤ)^84) * horner X vp00001000100001.list + horner X ep00001000100001.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000100001 : Branch 1 (-271761639/1000000 : ℚ) vp0000100010000 := by
  apply branch_checked idp00001000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-271761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-272261639/500000 : ℚ) by norm_num]
  exact coverp00001000100001
theorem coverp0000100010000 : Covers (-271761639/1000000 : ℚ) vp0000100010000 := join_branches bp00001000100000 bp00001000100001
private noncomputable def vp000010001000_0 : Blocks := edgeBlocks% "full/vectors/000010001000-V-0000.bin"
private noncomputable def vp000010001000_1 : Blocks := edgeBlocks% "full/vectors/000010001000-V-0001.bin"
noncomputable def vp000010001000 : Blocks := (Blocks.join vp000010001000_0 vp000010001000_1)
private theorem bp0000100010000 : Branch 0 (-271761639/2000000 : ℚ) vp000010001000 := by
  apply branch_left_normalized (c:=vp0000100010000) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-271761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-271761639/1000000 : ℚ) by norm_num]
  exact coverp0000100010000
private noncomputable def ep0000100010001_0 : Blocks := edgeBlocks% "full/vectors/0000100010001-E-0000.bin"
private noncomputable def ep0000100010001_1 : Blocks := edgeBlocks% "full/vectors/0000100010001-E-0001.bin"
noncomputable def ep0000100010001 : Blocks := (Blocks.join ep0000100010001_0 ep0000100010001_1)
private theorem idp0000100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010001000.list =
    C ((2:ℤ)^148) * horner X vp0000100010001.list + horner X ep0000100010001.list := by
  exact edge_identity (B := (2:ℤ)^307) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100010001 : Branch 1 (-271761639/2000000 : ℚ) vp000010001000 := by
  apply branch_checked idp0000100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-271761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-272761639/1000000 : ℚ) by norm_num]
  exact coverp0000100010001
theorem coverp000010001000 : Covers (-271761639/2000000 : ℚ) vp000010001000 := join_branches bp0000100010000 bp0000100010001
private noncomputable def vp00001000100_0 : Blocks := edgeBlocks% "full/vectors/00001000100-V-0000.bin"
private noncomputable def vp00001000100_1 : Blocks := edgeBlocks% "full/vectors/00001000100-V-0001.bin"
private noncomputable def vp00001000100_2 : Blocks := edgeBlocks% "full/vectors/00001000100-V-0002.bin"
noncomputable def vp00001000100 : Blocks := (Blocks.join vp00001000100_0 (Blocks.join vp00001000100_1 vp00001000100_2))
private theorem bp000010001000 : Branch 0 (-271761639/4000000 : ℚ) vp00001000100 := by
  apply branch_left_normalized (c:=vp000010001000) (k:=0) (m:=141) (by decide +kernel)
  rw [show 2*(-271761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-271761639/2000000 : ℚ) by norm_num]
  exact coverp000010001000
private noncomputable def ep000010001001_0 : Blocks := edgeBlocks% "full/vectors/000010001001-E-0000.bin"
private noncomputable def ep000010001001_1 : Blocks := edgeBlocks% "full/vectors/000010001001-E-0001.bin"
private noncomputable def ep000010001001_2 : Blocks := edgeBlocks% "full/vectors/000010001001-E-0002.bin"
noncomputable def ep000010001001 : Blocks := (Blocks.join ep000010001001_0 (Blocks.join ep000010001001_1 ep000010001001_2))
private theorem idp000010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000100.list =
    C ((2:ℤ)^274) * horner X vp000010001001.list + horner X ep000010001001.list := by
  exact edge_identity (B := (2:ℤ)^490) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001001 : Branch 1 (-271761639/4000000 : ℚ) vp00001000100 := by
  apply branch_checked idp000010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-271761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-273761639/2000000 : ℚ) by norm_num]
  exact coverp000010001001
theorem coverp00001000100 : Covers (-271761639/4000000 : ℚ) vp00001000100 := join_branches bp000010001000 bp000010001001
private noncomputable def vp0000100010_0 : Blocks := edgeBlocks% "full/vectors/0000100010-V-0000.bin"
private noncomputable def vp0000100010_1 : Blocks := edgeBlocks% "full/vectors/0000100010-V-0001.bin"
private noncomputable def vp0000100010_2 : Blocks := edgeBlocks% "full/vectors/0000100010-V-0002.bin"
private noncomputable def vp0000100010_3 : Blocks := edgeBlocks% "full/vectors/0000100010-V-0003.bin"
noncomputable def vp0000100010 : Blocks := (Blocks.join (Blocks.join vp0000100010_0 vp0000100010_1) (Blocks.join vp0000100010_2 vp0000100010_3))
private theorem bp00001000100 : Branch 0 (-271761639/8000000 : ℚ) vp0000100010 := by
  apply branch_left_normalized (c:=vp00001000100) (k:=0) (m:=261) (by decide +kernel)
  rw [show 2*(-271761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-271761639/4000000 : ℚ) by norm_num]
  exact coverp00001000100
private noncomputable def ep00001000101_0 : Blocks := edgeBlocks% "full/vectors/00001000101-E-0000.bin"
private noncomputable def ep00001000101_1 : Blocks := edgeBlocks% "full/vectors/00001000101-E-0001.bin"
private noncomputable def ep00001000101_2 : Blocks := edgeBlocks% "full/vectors/00001000101-E-0002.bin"
private noncomputable def ep00001000101_3 : Blocks := edgeBlocks% "full/vectors/00001000101-E-0003.bin"
noncomputable def ep00001000101 : Blocks := (Blocks.join (Blocks.join ep00001000101_0 ep00001000101_1) (Blocks.join ep00001000101_2 ep00001000101_3))
private theorem idp00001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100010.list =
    C ((2:ℤ)^521) * horner X vp00001000101.list + horner X ep00001000101.list := by
  exact edge_identity (B := (2:ℤ)^853) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000101 : Branch 1 (-271761639/8000000 : ℚ) vp0000100010 := by
  apply branch_checked idp00001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-271761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-275761639/4000000 : ℚ) by norm_num]
  exact coverp00001000101
theorem coverp0000100010 : Covers (-271761639/8000000 : ℚ) vp0000100010 := join_branches bp00001000100 bp00001000101
private noncomputable def vp000010001_0 : Blocks := edgeBlocks% "full/vectors/000010001-V-0000.bin"
private noncomputable def vp000010001_1 : Blocks := edgeBlocks% "full/vectors/000010001-V-0001.bin"
private noncomputable def vp000010001_2 : Blocks := edgeBlocks% "full/vectors/000010001-V-0002.bin"
private noncomputable def vp000010001_3 : Blocks := edgeBlocks% "full/vectors/000010001-V-0003.bin"
private noncomputable def vp000010001_4 : Blocks := edgeBlocks% "full/vectors/000010001-V-0004.bin"
private noncomputable def vp000010001_5 : Blocks := edgeBlocks% "full/vectors/000010001-V-0005.bin"
private noncomputable def vp000010001_6 : Blocks := edgeBlocks% "full/vectors/000010001-V-0006.bin"
private noncomputable def vp000010001_7 : Blocks := edgeBlocks% "full/vectors/000010001-V-0007.bin"
noncomputable def vp000010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000010001_0 vp000010001_1) (Blocks.join vp000010001_2 vp000010001_3)) (Blocks.join (Blocks.join vp000010001_4 vp000010001_5) (Blocks.join vp000010001_6 vp000010001_7)))
private theorem bp0000100010 : Branch 0 (-271761639/16000000 : ℚ) vp000010001 := by
  apply branch_left_normalized (c:=vp0000100010) (k:=0) (m:=497) (by decide +kernel)
  rw [show 2*(-271761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-271761639/8000000 : ℚ) by norm_num]
  exact coverp0000100010
private noncomputable def ep0000100011_0 : Blocks := edgeBlocks% "full/vectors/0000100011-E-0000.bin"
private noncomputable def ep0000100011_1 : Blocks := edgeBlocks% "full/vectors/0000100011-E-0001.bin"
private noncomputable def ep0000100011_2 : Blocks := edgeBlocks% "full/vectors/0000100011-E-0002.bin"
private noncomputable def ep0000100011_3 : Blocks := edgeBlocks% "full/vectors/0000100011-E-0003.bin"
private noncomputable def ep0000100011_4 : Blocks := edgeBlocks% "full/vectors/0000100011-E-0004.bin"
private noncomputable def ep0000100011_5 : Blocks := edgeBlocks% "full/vectors/0000100011-E-0005.bin"
private noncomputable def ep0000100011_6 : Blocks := edgeBlocks% "full/vectors/0000100011-E-0006.bin"
private noncomputable def ep0000100011_7 : Blocks := edgeBlocks% "full/vectors/0000100011-E-0007.bin"
noncomputable def ep0000100011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000100011_0 ep0000100011_1) (Blocks.join ep0000100011_2 ep0000100011_3)) (Blocks.join (Blocks.join ep0000100011_4 ep0000100011_5) (Blocks.join ep0000100011_6 ep0000100011_7)))
private theorem idp0000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010001.list =
    C ((2:ℤ)^1010) * horner X vp0000100011.list + horner X ep0000100011.list := by
  exact edge_identity (B := (2:ℤ)^1570) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100011 : Branch 1 (-271761639/16000000 : ℚ) vp000010001 := by
  apply branch_checked idp0000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-271761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-279761639/8000000 : ℚ) by norm_num]
  exact coverp0000100011
theorem coverp000010001 : Covers (-271761639/16000000 : ℚ) vp000010001 := join_branches bp0000100010 bp0000100011
end NextProof.EdgeFull

