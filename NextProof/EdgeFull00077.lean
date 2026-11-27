import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00076

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00011000111111_0 : Blocks := edgeBlocks% "full/vectors/00011000111111-V-0000.bin"
noncomputable def vp00011000111111 : Blocks := vp00011000111111_0
theorem coverp00011000111111 : Covers (-799261639/500000 : ℚ) vp00011000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000111110_0 : Blocks := edgeBlocks% "full/vectors/00011000111110-V-0000.bin"
noncomputable def vp00011000111110 : Blocks := vp00011000111110_0
theorem coverp00011000111110 : Covers (-798761639/500000 : ℚ) vp00011000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100011111_0 : Blocks := edgeBlocks% "full/vectors/0001100011111-V-0000.bin"
noncomputable def vp0001100011111 : Blocks := vp0001100011111_0
private theorem bp00011000111110 : Branch 0 (-798761639/1000000 : ℚ) vp0001100011111 := by
  apply branch_left_normalized (c:=vp00011000111110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-798761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-798761639/500000 : ℚ) by norm_num]
  exact coverp00011000111110
private noncomputable def ep00011000111111_0 : Blocks := edgeBlocks% "full/vectors/00011000111111-E-0000.bin"
noncomputable def ep00011000111111 : Blocks := ep00011000111111_0
private theorem idp00011000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100011111.list =
    C ((2:ℤ)^58) * horner X vp00011000111111.list + horner X ep00011000111111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000111111 : Branch 1 (-798761639/1000000 : ℚ) vp0001100011111 := by
  apply branch_checked idp00011000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-798761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-799261639/500000 : ℚ) by norm_num]
  exact coverp00011000111111
theorem coverp0001100011111 : Covers (-798761639/1000000 : ℚ) vp0001100011111 := join_branches bp00011000111110 bp00011000111111
private noncomputable def vp00011000111101_0 : Blocks := edgeBlocks% "full/vectors/00011000111101-V-0000.bin"
noncomputable def vp00011000111101 : Blocks := vp00011000111101_0
theorem coverp00011000111101 : Covers (-798261639/500000 : ℚ) vp00011000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000111100_0 : Blocks := edgeBlocks% "full/vectors/00011000111100-V-0000.bin"
noncomputable def vp00011000111100 : Blocks := vp00011000111100_0
theorem coverp00011000111100 : Covers (-797761639/500000 : ℚ) vp00011000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100011110_0 : Blocks := edgeBlocks% "full/vectors/0001100011110-V-0000.bin"
noncomputable def vp0001100011110 : Blocks := vp0001100011110_0
private theorem bp00011000111100 : Branch 0 (-797761639/1000000 : ℚ) vp0001100011110 := by
  apply branch_left_normalized (c:=vp00011000111100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-797761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-797761639/500000 : ℚ) by norm_num]
  exact coverp00011000111100
private noncomputable def ep00011000111101_0 : Blocks := edgeBlocks% "full/vectors/00011000111101-E-0000.bin"
noncomputable def ep00011000111101 : Blocks := ep00011000111101_0
private theorem idp00011000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100011110.list =
    C ((2:ℤ)^58) * horner X vp00011000111101.list + horner X ep00011000111101.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000111101 : Branch 1 (-797761639/1000000 : ℚ) vp0001100011110 := by
  apply branch_checked idp00011000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-797761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-798261639/500000 : ℚ) by norm_num]
  exact coverp00011000111101
theorem coverp0001100011110 : Covers (-797761639/1000000 : ℚ) vp0001100011110 := join_branches bp00011000111100 bp00011000111101
private noncomputable def vp000110001111_0 : Blocks := edgeBlocks% "full/vectors/000110001111-V-0000.bin"
noncomputable def vp000110001111 : Blocks := vp000110001111_0
private theorem bp0001100011110 : Branch 0 (-797761639/2000000 : ℚ) vp000110001111 := by
  apply branch_left_normalized (c:=vp0001100011110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-797761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-797761639/1000000 : ℚ) by norm_num]
  exact coverp0001100011110
private noncomputable def ep0001100011111_0 : Blocks := edgeBlocks% "full/vectors/0001100011111-E-0000.bin"
noncomputable def ep0001100011111 : Blocks := ep0001100011111_0
private theorem idp0001100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110001111.list =
    C ((2:ℤ)^97) * horner X vp0001100011111.list + horner X ep0001100011111.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100011111 : Branch 1 (-797761639/2000000 : ℚ) vp000110001111 := by
  apply branch_checked idp0001100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-797761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-798761639/1000000 : ℚ) by norm_num]
  exact coverp0001100011111
theorem coverp000110001111 : Covers (-797761639/2000000 : ℚ) vp000110001111 := join_branches bp0001100011110 bp0001100011111
private noncomputable def vp00011000111011_0 : Blocks := edgeBlocks% "full/vectors/00011000111011-V-0000.bin"
noncomputable def vp00011000111011 : Blocks := vp00011000111011_0
theorem coverp00011000111011 : Covers (-797261639/500000 : ℚ) vp00011000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000111010_0 : Blocks := edgeBlocks% "full/vectors/00011000111010-V-0000.bin"
noncomputable def vp00011000111010 : Blocks := vp00011000111010_0
theorem coverp00011000111010 : Covers (-796761639/500000 : ℚ) vp00011000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100011101_0 : Blocks := edgeBlocks% "full/vectors/0001100011101-V-0000.bin"
noncomputable def vp0001100011101 : Blocks := vp0001100011101_0
private theorem bp00011000111010 : Branch 0 (-796761639/1000000 : ℚ) vp0001100011101 := by
  apply branch_left_normalized (c:=vp00011000111010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-796761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-796761639/500000 : ℚ) by norm_num]
  exact coverp00011000111010
private noncomputable def ep00011000111011_0 : Blocks := edgeBlocks% "full/vectors/00011000111011-E-0000.bin"
noncomputable def ep00011000111011 : Blocks := ep00011000111011_0
private theorem idp00011000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100011101.list =
    C ((2:ℤ)^58) * horner X vp00011000111011.list + horner X ep00011000111011.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000111011 : Branch 1 (-796761639/1000000 : ℚ) vp0001100011101 := by
  apply branch_checked idp00011000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-796761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-797261639/500000 : ℚ) by norm_num]
  exact coverp00011000111011
theorem coverp0001100011101 : Covers (-796761639/1000000 : ℚ) vp0001100011101 := join_branches bp00011000111010 bp00011000111011
private noncomputable def vp00011000111001_0 : Blocks := edgeBlocks% "full/vectors/00011000111001-V-0000.bin"
noncomputable def vp00011000111001 : Blocks := vp00011000111001_0
theorem coverp00011000111001 : Covers (-796261639/500000 : ℚ) vp00011000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000111000_0 : Blocks := edgeBlocks% "full/vectors/00011000111000-V-0000.bin"
noncomputable def vp00011000111000 : Blocks := vp00011000111000_0
theorem coverp00011000111000 : Covers (-795761639/500000 : ℚ) vp00011000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100011100_0 : Blocks := edgeBlocks% "full/vectors/0001100011100-V-0000.bin"
noncomputable def vp0001100011100 : Blocks := vp0001100011100_0
private theorem bp00011000111000 : Branch 0 (-795761639/1000000 : ℚ) vp0001100011100 := by
  apply branch_left_normalized (c:=vp00011000111000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-795761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-795761639/500000 : ℚ) by norm_num]
  exact coverp00011000111000
private noncomputable def ep00011000111001_0 : Blocks := edgeBlocks% "full/vectors/00011000111001-E-0000.bin"
noncomputable def ep00011000111001 : Blocks := ep00011000111001_0
private theorem idp00011000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100011100.list =
    C ((2:ℤ)^57) * horner X vp00011000111001.list + horner X ep00011000111001.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000111001 : Branch 1 (-795761639/1000000 : ℚ) vp0001100011100 := by
  apply branch_checked idp00011000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-795761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-796261639/500000 : ℚ) by norm_num]
  exact coverp00011000111001
theorem coverp0001100011100 : Covers (-795761639/1000000 : ℚ) vp0001100011100 := join_branches bp00011000111000 bp00011000111001
private noncomputable def vp000110001110_0 : Blocks := edgeBlocks% "full/vectors/000110001110-V-0000.bin"
noncomputable def vp000110001110 : Blocks := vp000110001110_0
private theorem bp0001100011100 : Branch 0 (-795761639/2000000 : ℚ) vp000110001110 := by
  apply branch_left_normalized (c:=vp0001100011100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-795761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-795761639/1000000 : ℚ) by norm_num]
  exact coverp0001100011100
private noncomputable def ep0001100011101_0 : Blocks := edgeBlocks% "full/vectors/0001100011101-E-0000.bin"
noncomputable def ep0001100011101 : Blocks := ep0001100011101_0
private theorem idp0001100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110001110.list =
    C ((2:ℤ)^97) * horner X vp0001100011101.list + horner X ep0001100011101.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100011101 : Branch 1 (-795761639/2000000 : ℚ) vp000110001110 := by
  apply branch_checked idp0001100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-795761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-796761639/1000000 : ℚ) by norm_num]
  exact coverp0001100011101
theorem coverp000110001110 : Covers (-795761639/2000000 : ℚ) vp000110001110 := join_branches bp0001100011100 bp0001100011101
private noncomputable def vp00011000111_0 : Blocks := edgeBlocks% "full/vectors/00011000111-V-0000.bin"
private noncomputable def vp00011000111_1 : Blocks := edgeBlocks% "full/vectors/00011000111-V-0001.bin"
noncomputable def vp00011000111 : Blocks := (Blocks.join vp00011000111_0 vp00011000111_1)
private theorem bp000110001110 : Branch 0 (-795761639/4000000 : ℚ) vp00011000111 := by
  apply branch_left_normalized (c:=vp000110001110) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-795761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-795761639/2000000 : ℚ) by norm_num]
  exact coverp000110001110
private noncomputable def ep000110001111_0 : Blocks := edgeBlocks% "full/vectors/000110001111-E-0000.bin"
private noncomputable def ep000110001111_1 : Blocks := edgeBlocks% "full/vectors/000110001111-E-0001.bin"
noncomputable def ep000110001111 : Blocks := (Blocks.join ep000110001111_0 ep000110001111_1)
private theorem idp000110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011000111.list =
    C ((2:ℤ)^173) * horner X vp000110001111.list + horner X ep000110001111.list := by
  exact edge_identity (B := (2:ℤ)^337) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110001111 : Branch 1 (-795761639/4000000 : ℚ) vp00011000111 := by
  apply branch_checked idp000110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-795761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-797761639/2000000 : ℚ) by norm_num]
  exact coverp000110001111
theorem coverp00011000111 : Covers (-795761639/4000000 : ℚ) vp00011000111 := join_branches bp000110001110 bp000110001111
private noncomputable def vp00011000110111_0 : Blocks := edgeBlocks% "full/vectors/00011000110111-V-0000.bin"
noncomputable def vp00011000110111 : Blocks := vp00011000110111_0
theorem coverp00011000110111 : Covers (-795261639/500000 : ℚ) vp00011000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000110110_0 : Blocks := edgeBlocks% "full/vectors/00011000110110-V-0000.bin"
noncomputable def vp00011000110110 : Blocks := vp00011000110110_0
theorem coverp00011000110110 : Covers (-794761639/500000 : ℚ) vp00011000110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100011011_0 : Blocks := edgeBlocks% "full/vectors/0001100011011-V-0000.bin"
noncomputable def vp0001100011011 : Blocks := vp0001100011011_0
private theorem bp00011000110110 : Branch 0 (-794761639/1000000 : ℚ) vp0001100011011 := by
  apply branch_left_normalized (c:=vp00011000110110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-794761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-794761639/500000 : ℚ) by norm_num]
  exact coverp00011000110110
private noncomputable def ep00011000110111_0 : Blocks := edgeBlocks% "full/vectors/00011000110111-E-0000.bin"
noncomputable def ep00011000110111 : Blocks := ep00011000110111_0
private theorem idp00011000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100011011.list =
    C ((2:ℤ)^58) * horner X vp00011000110111.list + horner X ep00011000110111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000110111 : Branch 1 (-794761639/1000000 : ℚ) vp0001100011011 := by
  apply branch_checked idp00011000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-794761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-795261639/500000 : ℚ) by norm_num]
  exact coverp00011000110111
theorem coverp0001100011011 : Covers (-794761639/1000000 : ℚ) vp0001100011011 := join_branches bp00011000110110 bp00011000110111
private noncomputable def vp00011000110101_0 : Blocks := edgeBlocks% "full/vectors/00011000110101-V-0000.bin"
noncomputable def vp00011000110101 : Blocks := vp00011000110101_0
theorem coverp00011000110101 : Covers (-794261639/500000 : ℚ) vp00011000110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000110100_0 : Blocks := edgeBlocks% "full/vectors/00011000110100-V-0000.bin"
noncomputable def vp00011000110100 : Blocks := vp00011000110100_0
theorem coverp00011000110100 : Covers (-793761639/500000 : ℚ) vp00011000110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100011010_0 : Blocks := edgeBlocks% "full/vectors/0001100011010-V-0000.bin"
noncomputable def vp0001100011010 : Blocks := vp0001100011010_0
private theorem bp00011000110100 : Branch 0 (-793761639/1000000 : ℚ) vp0001100011010 := by
  apply branch_left_normalized (c:=vp00011000110100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-793761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-793761639/500000 : ℚ) by norm_num]
  exact coverp00011000110100
private noncomputable def ep00011000110101_0 : Blocks := edgeBlocks% "full/vectors/00011000110101-E-0000.bin"
noncomputable def ep00011000110101 : Blocks := ep00011000110101_0
private theorem idp00011000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100011010.list =
    C ((2:ℤ)^58) * horner X vp00011000110101.list + horner X ep00011000110101.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000110101 : Branch 1 (-793761639/1000000 : ℚ) vp0001100011010 := by
  apply branch_checked idp00011000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-793761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-794261639/500000 : ℚ) by norm_num]
  exact coverp00011000110101
theorem coverp0001100011010 : Covers (-793761639/1000000 : ℚ) vp0001100011010 := join_branches bp00011000110100 bp00011000110101
private noncomputable def vp000110001101_0 : Blocks := edgeBlocks% "full/vectors/000110001101-V-0000.bin"
noncomputable def vp000110001101 : Blocks := vp000110001101_0
private theorem bp0001100011010 : Branch 0 (-793761639/2000000 : ℚ) vp000110001101 := by
  apply branch_left_normalized (c:=vp0001100011010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-793761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-793761639/1000000 : ℚ) by norm_num]
  exact coverp0001100011010
private noncomputable def ep0001100011011_0 : Blocks := edgeBlocks% "full/vectors/0001100011011-E-0000.bin"
noncomputable def ep0001100011011 : Blocks := ep0001100011011_0
private theorem idp0001100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110001101.list =
    C ((2:ℤ)^98) * horner X vp0001100011011.list + horner X ep0001100011011.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100011011 : Branch 1 (-793761639/2000000 : ℚ) vp000110001101 := by
  apply branch_checked idp0001100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-793761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-794761639/1000000 : ℚ) by norm_num]
  exact coverp0001100011011
theorem coverp000110001101 : Covers (-793761639/2000000 : ℚ) vp000110001101 := join_branches bp0001100011010 bp0001100011011
private noncomputable def vp00011000110011_0 : Blocks := edgeBlocks% "full/vectors/00011000110011-V-0000.bin"
noncomputable def vp00011000110011 : Blocks := vp00011000110011_0
theorem coverp00011000110011 : Covers (-793261639/500000 : ℚ) vp00011000110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000110010_0 : Blocks := edgeBlocks% "full/vectors/00011000110010-V-0000.bin"
noncomputable def vp00011000110010 : Blocks := vp00011000110010_0
theorem coverp00011000110010 : Covers (-792761639/500000 : ℚ) vp00011000110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100011001_0 : Blocks := edgeBlocks% "full/vectors/0001100011001-V-0000.bin"
noncomputable def vp0001100011001 : Blocks := vp0001100011001_0
private theorem bp00011000110010 : Branch 0 (-792761639/1000000 : ℚ) vp0001100011001 := by
  apply branch_left_normalized (c:=vp00011000110010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-792761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-792761639/500000 : ℚ) by norm_num]
  exact coverp00011000110010
private noncomputable def ep00011000110011_0 : Blocks := edgeBlocks% "full/vectors/00011000110011-E-0000.bin"
noncomputable def ep00011000110011 : Blocks := ep00011000110011_0
private theorem idp00011000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100011001.list =
    C ((2:ℤ)^59) * horner X vp00011000110011.list + horner X ep00011000110011.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000110011 : Branch 1 (-792761639/1000000 : ℚ) vp0001100011001 := by
  apply branch_checked idp00011000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-792761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-793261639/500000 : ℚ) by norm_num]
  exact coverp00011000110011
theorem coverp0001100011001 : Covers (-792761639/1000000 : ℚ) vp0001100011001 := join_branches bp00011000110010 bp00011000110011
private noncomputable def vp00011000110001_0 : Blocks := edgeBlocks% "full/vectors/00011000110001-V-0000.bin"
noncomputable def vp00011000110001 : Blocks := vp00011000110001_0
theorem coverp00011000110001 : Covers (-792261639/500000 : ℚ) vp00011000110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000110000_0 : Blocks := edgeBlocks% "full/vectors/00011000110000-V-0000.bin"
noncomputable def vp00011000110000 : Blocks := vp00011000110000_0
theorem coverp00011000110000 : Covers (-791761639/500000 : ℚ) vp00011000110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100011000_0 : Blocks := edgeBlocks% "full/vectors/0001100011000-V-0000.bin"
noncomputable def vp0001100011000 : Blocks := vp0001100011000_0
private theorem bp00011000110000 : Branch 0 (-791761639/1000000 : ℚ) vp0001100011000 := by
  apply branch_left_normalized (c:=vp00011000110000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-791761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-791761639/500000 : ℚ) by norm_num]
  exact coverp00011000110000
private noncomputable def ep00011000110001_0 : Blocks := edgeBlocks% "full/vectors/00011000110001-E-0000.bin"
noncomputable def ep00011000110001 : Blocks := ep00011000110001_0
private theorem idp00011000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100011000.list =
    C ((2:ℤ)^59) * horner X vp00011000110001.list + horner X ep00011000110001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000110001 : Branch 1 (-791761639/1000000 : ℚ) vp0001100011000 := by
  apply branch_checked idp00011000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-791761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-792261639/500000 : ℚ) by norm_num]
  exact coverp00011000110001
theorem coverp0001100011000 : Covers (-791761639/1000000 : ℚ) vp0001100011000 := join_branches bp00011000110000 bp00011000110001
private noncomputable def vp000110001100_0 : Blocks := edgeBlocks% "full/vectors/000110001100-V-0000.bin"
noncomputable def vp000110001100 : Blocks := vp000110001100_0
private theorem bp0001100011000 : Branch 0 (-791761639/2000000 : ℚ) vp000110001100 := by
  apply branch_left_normalized (c:=vp0001100011000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-791761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-791761639/1000000 : ℚ) by norm_num]
  exact coverp0001100011000
private noncomputable def ep0001100011001_0 : Blocks := edgeBlocks% "full/vectors/0001100011001-E-0000.bin"
noncomputable def ep0001100011001 : Blocks := ep0001100011001_0
private theorem idp0001100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110001100.list =
    C ((2:ℤ)^98) * horner X vp0001100011001.list + horner X ep0001100011001.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100011001 : Branch 1 (-791761639/2000000 : ℚ) vp000110001100 := by
  apply branch_checked idp0001100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-791761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-792761639/1000000 : ℚ) by norm_num]
  exact coverp0001100011001
theorem coverp000110001100 : Covers (-791761639/2000000 : ℚ) vp000110001100 := join_branches bp0001100011000 bp0001100011001
private noncomputable def vp00011000110_0 : Blocks := edgeBlocks% "full/vectors/00011000110-V-0000.bin"
private noncomputable def vp00011000110_1 : Blocks := edgeBlocks% "full/vectors/00011000110-V-0001.bin"
noncomputable def vp00011000110 : Blocks := (Blocks.join vp00011000110_0 vp00011000110_1)
private theorem bp000110001100 : Branch 0 (-791761639/4000000 : ℚ) vp00011000110 := by
  apply branch_left_normalized (c:=vp000110001100) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-791761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-791761639/2000000 : ℚ) by norm_num]
  exact coverp000110001100
private noncomputable def ep000110001101_0 : Blocks := edgeBlocks% "full/vectors/000110001101-E-0000.bin"
private noncomputable def ep000110001101_1 : Blocks := edgeBlocks% "full/vectors/000110001101-E-0001.bin"
noncomputable def ep000110001101 : Blocks := (Blocks.join ep000110001101_0 ep000110001101_1)
private theorem idp000110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011000110.list =
    C ((2:ℤ)^175) * horner X vp000110001101.list + horner X ep000110001101.list := by
  exact edge_identity (B := (2:ℤ)^339) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110001101 : Branch 1 (-791761639/4000000 : ℚ) vp00011000110 := by
  apply branch_checked idp000110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-791761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-793761639/2000000 : ℚ) by norm_num]
  exact coverp000110001101
theorem coverp00011000110 : Covers (-791761639/4000000 : ℚ) vp00011000110 := join_branches bp000110001100 bp000110001101
private noncomputable def vp0001100011_0 : Blocks := edgeBlocks% "full/vectors/0001100011-V-0000.bin"
private noncomputable def vp0001100011_1 : Blocks := edgeBlocks% "full/vectors/0001100011-V-0001.bin"
private noncomputable def vp0001100011_2 : Blocks := edgeBlocks% "full/vectors/0001100011-V-0002.bin"
noncomputable def vp0001100011 : Blocks := (Blocks.join vp0001100011_0 (Blocks.join vp0001100011_1 vp0001100011_2))
private theorem bp00011000110 : Branch 0 (-791761639/8000000 : ℚ) vp0001100011 := by
  apply branch_left_normalized (c:=vp00011000110) (k:=0) (m:=162) (by decide +kernel)
  rw [show 2*(-791761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-791761639/4000000 : ℚ) by norm_num]
  exact coverp00011000110
private noncomputable def ep00011000111_0 : Blocks := edgeBlocks% "full/vectors/00011000111-E-0000.bin"
private noncomputable def ep00011000111_1 : Blocks := edgeBlocks% "full/vectors/00011000111-E-0001.bin"
private noncomputable def ep00011000111_2 : Blocks := edgeBlocks% "full/vectors/00011000111-E-0002.bin"
noncomputable def ep00011000111 : Blocks := (Blocks.join ep00011000111_0 (Blocks.join ep00011000111_1 ep00011000111_2))
private theorem idp00011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100011.list =
    C ((2:ℤ)^326) * horner X vp00011000111.list + horner X ep00011000111.list := by
  exact edge_identity (B := (2:ℤ)^552) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000111 : Branch 1 (-791761639/8000000 : ℚ) vp0001100011 := by
  apply branch_checked idp00011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-791761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-795761639/4000000 : ℚ) by norm_num]
  exact coverp00011000111
theorem coverp0001100011 : Covers (-791761639/8000000 : ℚ) vp0001100011 := join_branches bp00011000110 bp00011000111
private noncomputable def vp00011000101111_0 : Blocks := edgeBlocks% "full/vectors/00011000101111-V-0000.bin"
noncomputable def vp00011000101111 : Blocks := vp00011000101111_0
theorem coverp00011000101111 : Covers (-791261639/500000 : ℚ) vp00011000101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000101110_0 : Blocks := edgeBlocks% "full/vectors/00011000101110-V-0000.bin"
noncomputable def vp00011000101110 : Blocks := vp00011000101110_0
theorem coverp00011000101110 : Covers (-790761639/500000 : ℚ) vp00011000101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100010111_0 : Blocks := edgeBlocks% "full/vectors/0001100010111-V-0000.bin"
noncomputable def vp0001100010111 : Blocks := vp0001100010111_0
private theorem bp00011000101110 : Branch 0 (-790761639/1000000 : ℚ) vp0001100010111 := by
  apply branch_left_normalized (c:=vp00011000101110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-790761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-790761639/500000 : ℚ) by norm_num]
  exact coverp00011000101110
private noncomputable def ep00011000101111_0 : Blocks := edgeBlocks% "full/vectors/00011000101111-E-0000.bin"
noncomputable def ep00011000101111 : Blocks := ep00011000101111_0
private theorem idp00011000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100010111.list =
    C ((2:ℤ)^58) * horner X vp00011000101111.list + horner X ep00011000101111.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000101111 : Branch 1 (-790761639/1000000 : ℚ) vp0001100010111 := by
  apply branch_checked idp00011000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-790761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-791261639/500000 : ℚ) by norm_num]
  exact coverp00011000101111
theorem coverp0001100010111 : Covers (-790761639/1000000 : ℚ) vp0001100010111 := join_branches bp00011000101110 bp00011000101111
private noncomputable def vp00011000101101_0 : Blocks := edgeBlocks% "full/vectors/00011000101101-V-0000.bin"
noncomputable def vp00011000101101 : Blocks := vp00011000101101_0
theorem coverp00011000101101 : Covers (-790261639/500000 : ℚ) vp00011000101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000101100_0 : Blocks := edgeBlocks% "full/vectors/00011000101100-V-0000.bin"
noncomputable def vp00011000101100 : Blocks := vp00011000101100_0
theorem coverp00011000101100 : Covers (-789761639/500000 : ℚ) vp00011000101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100010110_0 : Blocks := edgeBlocks% "full/vectors/0001100010110-V-0000.bin"
noncomputable def vp0001100010110 : Blocks := vp0001100010110_0
private theorem bp00011000101100 : Branch 0 (-789761639/1000000 : ℚ) vp0001100010110 := by
  apply branch_left_normalized (c:=vp00011000101100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-789761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-789761639/500000 : ℚ) by norm_num]
  exact coverp00011000101100
private noncomputable def ep00011000101101_0 : Blocks := edgeBlocks% "full/vectors/00011000101101-E-0000.bin"
noncomputable def ep00011000101101 : Blocks := ep00011000101101_0
private theorem idp00011000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100010110.list =
    C ((2:ℤ)^59) * horner X vp00011000101101.list + horner X ep00011000101101.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000101101 : Branch 1 (-789761639/1000000 : ℚ) vp0001100010110 := by
  apply branch_checked idp00011000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-789761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-790261639/500000 : ℚ) by norm_num]
  exact coverp00011000101101
theorem coverp0001100010110 : Covers (-789761639/1000000 : ℚ) vp0001100010110 := join_branches bp00011000101100 bp00011000101101
private noncomputable def vp000110001011_0 : Blocks := edgeBlocks% "full/vectors/000110001011-V-0000.bin"
noncomputable def vp000110001011 : Blocks := vp000110001011_0
private theorem bp0001100010110 : Branch 0 (-789761639/2000000 : ℚ) vp000110001011 := by
  apply branch_left_normalized (c:=vp0001100010110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-789761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-789761639/1000000 : ℚ) by norm_num]
  exact coverp0001100010110
private noncomputable def ep0001100010111_0 : Blocks := edgeBlocks% "full/vectors/0001100010111-E-0000.bin"
noncomputable def ep0001100010111 : Blocks := ep0001100010111_0
private theorem idp0001100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110001011.list =
    C ((2:ℤ)^98) * horner X vp0001100010111.list + horner X ep0001100010111.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100010111 : Branch 1 (-789761639/2000000 : ℚ) vp000110001011 := by
  apply branch_checked idp0001100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-789761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-790761639/1000000 : ℚ) by norm_num]
  exact coverp0001100010111
theorem coverp000110001011 : Covers (-789761639/2000000 : ℚ) vp000110001011 := join_branches bp0001100010110 bp0001100010111
private noncomputable def vp00011000101011_0 : Blocks := edgeBlocks% "full/vectors/00011000101011-V-0000.bin"
noncomputable def vp00011000101011 : Blocks := vp00011000101011_0
theorem coverp00011000101011 : Covers (-789261639/500000 : ℚ) vp00011000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000101010_0 : Blocks := edgeBlocks% "full/vectors/00011000101010-V-0000.bin"
noncomputable def vp00011000101010 : Blocks := vp00011000101010_0
theorem coverp00011000101010 : Covers (-788761639/500000 : ℚ) vp00011000101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100010101_0 : Blocks := edgeBlocks% "full/vectors/0001100010101-V-0000.bin"
noncomputable def vp0001100010101 : Blocks := vp0001100010101_0
private theorem bp00011000101010 : Branch 0 (-788761639/1000000 : ℚ) vp0001100010101 := by
  apply branch_left_normalized (c:=vp00011000101010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-788761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-788761639/500000 : ℚ) by norm_num]
  exact coverp00011000101010
private noncomputable def ep00011000101011_0 : Blocks := edgeBlocks% "full/vectors/00011000101011-E-0000.bin"
noncomputable def ep00011000101011 : Blocks := ep00011000101011_0
private theorem idp00011000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100010101.list =
    C ((2:ℤ)^58) * horner X vp00011000101011.list + horner X ep00011000101011.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000101011 : Branch 1 (-788761639/1000000 : ℚ) vp0001100010101 := by
  apply branch_checked idp00011000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-788761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-789261639/500000 : ℚ) by norm_num]
  exact coverp00011000101011
theorem coverp0001100010101 : Covers (-788761639/1000000 : ℚ) vp0001100010101 := join_branches bp00011000101010 bp00011000101011
private noncomputable def vp00011000101001_0 : Blocks := edgeBlocks% "full/vectors/00011000101001-V-0000.bin"
noncomputable def vp00011000101001 : Blocks := vp00011000101001_0
theorem coverp00011000101001 : Covers (-788261639/500000 : ℚ) vp00011000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000101000_0 : Blocks := edgeBlocks% "full/vectors/00011000101000-V-0000.bin"
noncomputable def vp00011000101000 : Blocks := vp00011000101000_0
theorem coverp00011000101000 : Covers (-787761639/500000 : ℚ) vp00011000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100010100_0 : Blocks := edgeBlocks% "full/vectors/0001100010100-V-0000.bin"
noncomputable def vp0001100010100 : Blocks := vp0001100010100_0
private theorem bp00011000101000 : Branch 0 (-787761639/1000000 : ℚ) vp0001100010100 := by
  apply branch_left_normalized (c:=vp00011000101000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-787761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-787761639/500000 : ℚ) by norm_num]
  exact coverp00011000101000
private noncomputable def ep00011000101001_0 : Blocks := edgeBlocks% "full/vectors/00011000101001-E-0000.bin"
noncomputable def ep00011000101001 : Blocks := ep00011000101001_0
private theorem idp00011000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100010100.list =
    C ((2:ℤ)^58) * horner X vp00011000101001.list + horner X ep00011000101001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000101001 : Branch 1 (-787761639/1000000 : ℚ) vp0001100010100 := by
  apply branch_checked idp00011000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-787761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-788261639/500000 : ℚ) by norm_num]
  exact coverp00011000101001
theorem coverp0001100010100 : Covers (-787761639/1000000 : ℚ) vp0001100010100 := join_branches bp00011000101000 bp00011000101001
private noncomputable def vp000110001010_0 : Blocks := edgeBlocks% "full/vectors/000110001010-V-0000.bin"
noncomputable def vp000110001010 : Blocks := vp000110001010_0
private theorem bp0001100010100 : Branch 0 (-787761639/2000000 : ℚ) vp000110001010 := by
  apply branch_left_normalized (c:=vp0001100010100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-787761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-787761639/1000000 : ℚ) by norm_num]
  exact coverp0001100010100
private noncomputable def ep0001100010101_0 : Blocks := edgeBlocks% "full/vectors/0001100010101-E-0000.bin"
noncomputable def ep0001100010101 : Blocks := ep0001100010101_0
private theorem idp0001100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110001010.list =
    C ((2:ℤ)^98) * horner X vp0001100010101.list + horner X ep0001100010101.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100010101 : Branch 1 (-787761639/2000000 : ℚ) vp000110001010 := by
  apply branch_checked idp0001100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-787761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-788761639/1000000 : ℚ) by norm_num]
  exact coverp0001100010101
theorem coverp000110001010 : Covers (-787761639/2000000 : ℚ) vp000110001010 := join_branches bp0001100010100 bp0001100010101
private noncomputable def vp00011000101_0 : Blocks := edgeBlocks% "full/vectors/00011000101-V-0000.bin"
private noncomputable def vp00011000101_1 : Blocks := edgeBlocks% "full/vectors/00011000101-V-0001.bin"
noncomputable def vp00011000101 : Blocks := (Blocks.join vp00011000101_0 vp00011000101_1)
private theorem bp000110001010 : Branch 0 (-787761639/4000000 : ℚ) vp00011000101 := by
  apply branch_left_normalized (c:=vp000110001010) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-787761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-787761639/2000000 : ℚ) by norm_num]
  exact coverp000110001010
private noncomputable def ep000110001011_0 : Blocks := edgeBlocks% "full/vectors/000110001011-E-0000.bin"
private noncomputable def ep000110001011_1 : Blocks := edgeBlocks% "full/vectors/000110001011-E-0001.bin"
noncomputable def ep000110001011 : Blocks := (Blocks.join ep000110001011_0 ep000110001011_1)
private theorem idp000110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011000101.list =
    C ((2:ℤ)^175) * horner X vp000110001011.list + horner X ep000110001011.list := by
  exact edge_identity (B := (2:ℤ)^339) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110001011 : Branch 1 (-787761639/4000000 : ℚ) vp00011000101 := by
  apply branch_checked idp000110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-787761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-789761639/2000000 : ℚ) by norm_num]
  exact coverp000110001011
theorem coverp00011000101 : Covers (-787761639/4000000 : ℚ) vp00011000101 := join_branches bp000110001010 bp000110001011
private noncomputable def vp00011000100111_0 : Blocks := edgeBlocks% "full/vectors/00011000100111-V-0000.bin"
noncomputable def vp00011000100111 : Blocks := vp00011000100111_0
theorem coverp00011000100111 : Covers (-787261639/500000 : ℚ) vp00011000100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000100110_0 : Blocks := edgeBlocks% "full/vectors/00011000100110-V-0000.bin"
noncomputable def vp00011000100110 : Blocks := vp00011000100110_0
theorem coverp00011000100110 : Covers (-786761639/500000 : ℚ) vp00011000100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100010011_0 : Blocks := edgeBlocks% "full/vectors/0001100010011-V-0000.bin"
noncomputable def vp0001100010011 : Blocks := vp0001100010011_0
private theorem bp00011000100110 : Branch 0 (-786761639/1000000 : ℚ) vp0001100010011 := by
  apply branch_left_normalized (c:=vp00011000100110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-786761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-786761639/500000 : ℚ) by norm_num]
  exact coverp00011000100110
private noncomputable def ep00011000100111_0 : Blocks := edgeBlocks% "full/vectors/00011000100111-E-0000.bin"
noncomputable def ep00011000100111 : Blocks := ep00011000100111_0
private theorem idp00011000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100010011.list =
    C ((2:ℤ)^57) * horner X vp00011000100111.list + horner X ep00011000100111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000100111 : Branch 1 (-786761639/1000000 : ℚ) vp0001100010011 := by
  apply branch_checked idp00011000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-786761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-787261639/500000 : ℚ) by norm_num]
  exact coverp00011000100111
theorem coverp0001100010011 : Covers (-786761639/1000000 : ℚ) vp0001100010011 := join_branches bp00011000100110 bp00011000100111
private noncomputable def vp00011000100101_0 : Blocks := edgeBlocks% "full/vectors/00011000100101-V-0000.bin"
noncomputable def vp00011000100101 : Blocks := vp00011000100101_0
theorem coverp00011000100101 : Covers (-786261639/500000 : ℚ) vp00011000100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000100100_0 : Blocks := edgeBlocks% "full/vectors/00011000100100-V-0000.bin"
noncomputable def vp00011000100100 : Blocks := vp00011000100100_0
theorem coverp00011000100100 : Covers (-785761639/500000 : ℚ) vp00011000100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100010010_0 : Blocks := edgeBlocks% "full/vectors/0001100010010-V-0000.bin"
noncomputable def vp0001100010010 : Blocks := vp0001100010010_0
private theorem bp00011000100100 : Branch 0 (-785761639/1000000 : ℚ) vp0001100010010 := by
  apply branch_left_normalized (c:=vp00011000100100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-785761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-785761639/500000 : ℚ) by norm_num]
  exact coverp00011000100100
private noncomputable def ep00011000100101_0 : Blocks := edgeBlocks% "full/vectors/00011000100101-E-0000.bin"
noncomputable def ep00011000100101 : Blocks := ep00011000100101_0
private theorem idp00011000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100010010.list =
    C ((2:ℤ)^58) * horner X vp00011000100101.list + horner X ep00011000100101.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000100101 : Branch 1 (-785761639/1000000 : ℚ) vp0001100010010 := by
  apply branch_checked idp00011000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-785761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-786261639/500000 : ℚ) by norm_num]
  exact coverp00011000100101
theorem coverp0001100010010 : Covers (-785761639/1000000 : ℚ) vp0001100010010 := join_branches bp00011000100100 bp00011000100101
private noncomputable def vp000110001001_0 : Blocks := edgeBlocks% "full/vectors/000110001001-V-0000.bin"
noncomputable def vp000110001001 : Blocks := vp000110001001_0
private theorem bp0001100010010 : Branch 0 (-785761639/2000000 : ℚ) vp000110001001 := by
  apply branch_left_normalized (c:=vp0001100010010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-785761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-785761639/1000000 : ℚ) by norm_num]
  exact coverp0001100010010
private noncomputable def ep0001100010011_0 : Blocks := edgeBlocks% "full/vectors/0001100010011-E-0000.bin"
noncomputable def ep0001100010011 : Blocks := ep0001100010011_0
private theorem idp0001100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110001001.list =
    C ((2:ℤ)^98) * horner X vp0001100010011.list + horner X ep0001100010011.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100010011 : Branch 1 (-785761639/2000000 : ℚ) vp000110001001 := by
  apply branch_checked idp0001100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-785761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-786761639/1000000 : ℚ) by norm_num]
  exact coverp0001100010011
theorem coverp000110001001 : Covers (-785761639/2000000 : ℚ) vp000110001001 := join_branches bp0001100010010 bp0001100010011
private noncomputable def vp00011000100011_0 : Blocks := edgeBlocks% "full/vectors/00011000100011-V-0000.bin"
noncomputable def vp00011000100011 : Blocks := vp00011000100011_0
theorem coverp00011000100011 : Covers (-785261639/500000 : ℚ) vp00011000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000100010_0 : Blocks := edgeBlocks% "full/vectors/00011000100010-V-0000.bin"
noncomputable def vp00011000100010 : Blocks := vp00011000100010_0
theorem coverp00011000100010 : Covers (-784761639/500000 : ℚ) vp00011000100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100010001_0 : Blocks := edgeBlocks% "full/vectors/0001100010001-V-0000.bin"
noncomputable def vp0001100010001 : Blocks := vp0001100010001_0
private theorem bp00011000100010 : Branch 0 (-784761639/1000000 : ℚ) vp0001100010001 := by
  apply branch_left_normalized (c:=vp00011000100010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-784761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-784761639/500000 : ℚ) by norm_num]
  exact coverp00011000100010
private noncomputable def ep00011000100011_0 : Blocks := edgeBlocks% "full/vectors/00011000100011-E-0000.bin"
noncomputable def ep00011000100011 : Blocks := ep00011000100011_0
private theorem idp00011000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100010001.list =
    C ((2:ℤ)^59) * horner X vp00011000100011.list + horner X ep00011000100011.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000100011 : Branch 1 (-784761639/1000000 : ℚ) vp0001100010001 := by
  apply branch_checked idp00011000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-784761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-785261639/500000 : ℚ) by norm_num]
  exact coverp00011000100011
theorem coverp0001100010001 : Covers (-784761639/1000000 : ℚ) vp0001100010001 := join_branches bp00011000100010 bp00011000100011
private noncomputable def vp00011000100001_0 : Blocks := edgeBlocks% "full/vectors/00011000100001-V-0000.bin"
noncomputable def vp00011000100001 : Blocks := vp00011000100001_0
theorem coverp00011000100001 : Covers (-784261639/500000 : ℚ) vp00011000100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000100000_0 : Blocks := edgeBlocks% "full/vectors/00011000100000-V-0000.bin"
noncomputable def vp00011000100000 : Blocks := vp00011000100000_0
theorem coverp00011000100000 : Covers (-783761639/500000 : ℚ) vp00011000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100010000_0 : Blocks := edgeBlocks% "full/vectors/0001100010000-V-0000.bin"
noncomputable def vp0001100010000 : Blocks := vp0001100010000_0
private theorem bp00011000100000 : Branch 0 (-783761639/1000000 : ℚ) vp0001100010000 := by
  apply branch_left_normalized (c:=vp00011000100000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-783761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-783761639/500000 : ℚ) by norm_num]
  exact coverp00011000100000
private noncomputable def ep00011000100001_0 : Blocks := edgeBlocks% "full/vectors/00011000100001-E-0000.bin"
noncomputable def ep00011000100001 : Blocks := ep00011000100001_0
private theorem idp00011000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100010000.list =
    C ((2:ℤ)^59) * horner X vp00011000100001.list + horner X ep00011000100001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000100001 : Branch 1 (-783761639/1000000 : ℚ) vp0001100010000 := by
  apply branch_checked idp00011000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-783761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-784261639/500000 : ℚ) by norm_num]
  exact coverp00011000100001
theorem coverp0001100010000 : Covers (-783761639/1000000 : ℚ) vp0001100010000 := join_branches bp00011000100000 bp00011000100001
private noncomputable def vp000110001000_0 : Blocks := edgeBlocks% "full/vectors/000110001000-V-0000.bin"
noncomputable def vp000110001000 : Blocks := vp000110001000_0
private theorem bp0001100010000 : Branch 0 (-783761639/2000000 : ℚ) vp000110001000 := by
  apply branch_left_normalized (c:=vp0001100010000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-783761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-783761639/1000000 : ℚ) by norm_num]
  exact coverp0001100010000
private noncomputable def ep0001100010001_0 : Blocks := edgeBlocks% "full/vectors/0001100010001-E-0000.bin"
noncomputable def ep0001100010001 : Blocks := ep0001100010001_0
private theorem idp0001100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110001000.list =
    C ((2:ℤ)^98) * horner X vp0001100010001.list + horner X ep0001100010001.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100010001 : Branch 1 (-783761639/2000000 : ℚ) vp000110001000 := by
  apply branch_checked idp0001100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-783761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-784761639/1000000 : ℚ) by norm_num]
  exact coverp0001100010001
theorem coverp000110001000 : Covers (-783761639/2000000 : ℚ) vp000110001000 := join_branches bp0001100010000 bp0001100010001
private noncomputable def vp00011000100_0 : Blocks := edgeBlocks% "full/vectors/00011000100-V-0000.bin"
private noncomputable def vp00011000100_1 : Blocks := edgeBlocks% "full/vectors/00011000100-V-0001.bin"
noncomputable def vp00011000100 : Blocks := (Blocks.join vp00011000100_0 vp00011000100_1)
private theorem bp000110001000 : Branch 0 (-783761639/4000000 : ℚ) vp00011000100 := by
  apply branch_left_normalized (c:=vp000110001000) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-783761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-783761639/2000000 : ℚ) by norm_num]
  exact coverp000110001000
private noncomputable def ep000110001001_0 : Blocks := edgeBlocks% "full/vectors/000110001001-E-0000.bin"
private noncomputable def ep000110001001_1 : Blocks := edgeBlocks% "full/vectors/000110001001-E-0001.bin"
noncomputable def ep000110001001 : Blocks := (Blocks.join ep000110001001_0 ep000110001001_1)
private theorem idp000110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011000100.list =
    C ((2:ℤ)^176) * horner X vp000110001001.list + horner X ep000110001001.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110001001 : Branch 1 (-783761639/4000000 : ℚ) vp00011000100 := by
  apply branch_checked idp000110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-783761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-785761639/2000000 : ℚ) by norm_num]
  exact coverp000110001001
theorem coverp00011000100 : Covers (-783761639/4000000 : ℚ) vp00011000100 := join_branches bp000110001000 bp000110001001
private noncomputable def vp0001100010_0 : Blocks := edgeBlocks% "full/vectors/0001100010-V-0000.bin"
private noncomputable def vp0001100010_1 : Blocks := edgeBlocks% "full/vectors/0001100010-V-0001.bin"
private noncomputable def vp0001100010_2 : Blocks := edgeBlocks% "full/vectors/0001100010-V-0002.bin"
noncomputable def vp0001100010 : Blocks := (Blocks.join vp0001100010_0 (Blocks.join vp0001100010_1 vp0001100010_2))
private theorem bp00011000100 : Branch 0 (-783761639/8000000 : ℚ) vp0001100010 := by
  apply branch_left_normalized (c:=vp00011000100) (k:=0) (m:=163) (by decide +kernel)
  rw [show 2*(-783761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-783761639/4000000 : ℚ) by norm_num]
  exact coverp00011000100
private noncomputable def ep00011000101_0 : Blocks := edgeBlocks% "full/vectors/00011000101-E-0000.bin"
private noncomputable def ep00011000101_1 : Blocks := edgeBlocks% "full/vectors/00011000101-E-0001.bin"
private noncomputable def ep00011000101_2 : Blocks := edgeBlocks% "full/vectors/00011000101-E-0002.bin"
noncomputable def ep00011000101 : Blocks := (Blocks.join ep00011000101_0 (Blocks.join ep00011000101_1 ep00011000101_2))
private theorem idp00011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100010.list =
    C ((2:ℤ)^326) * horner X vp00011000101.list + horner X ep00011000101.list := by
  exact edge_identity (B := (2:ℤ)^554) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000101 : Branch 1 (-783761639/8000000 : ℚ) vp0001100010 := by
  apply branch_checked idp00011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-783761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-787761639/4000000 : ℚ) by norm_num]
  exact coverp00011000101
theorem coverp0001100010 : Covers (-783761639/8000000 : ℚ) vp0001100010 := join_branches bp00011000100 bp00011000101
private noncomputable def vp000110001_0 : Blocks := edgeBlocks% "full/vectors/000110001-V-0000.bin"
private noncomputable def vp000110001_1 : Blocks := edgeBlocks% "full/vectors/000110001-V-0001.bin"
private noncomputable def vp000110001_2 : Blocks := edgeBlocks% "full/vectors/000110001-V-0002.bin"
private noncomputable def vp000110001_3 : Blocks := edgeBlocks% "full/vectors/000110001-V-0003.bin"
private noncomputable def vp000110001_4 : Blocks := edgeBlocks% "full/vectors/000110001-V-0004.bin"
noncomputable def vp000110001 : Blocks := (Blocks.join (Blocks.join vp000110001_0 vp000110001_1) (Blocks.join vp000110001_2 (Blocks.join vp000110001_3 vp000110001_4)))
private theorem bp0001100010 : Branch 0 (-783761639/16000000 : ℚ) vp000110001 := by
  apply branch_left_normalized (c:=vp0001100010) (k:=0) (m:=302) (by decide +kernel)
  rw [show 2*(-783761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-783761639/8000000 : ℚ) by norm_num]
  exact coverp0001100010
private noncomputable def ep0001100011_0 : Blocks := edgeBlocks% "full/vectors/0001100011-E-0000.bin"
private noncomputable def ep0001100011_1 : Blocks := edgeBlocks% "full/vectors/0001100011-E-0001.bin"
private noncomputable def ep0001100011_2 : Blocks := edgeBlocks% "full/vectors/0001100011-E-0002.bin"
private noncomputable def ep0001100011_3 : Blocks := edgeBlocks% "full/vectors/0001100011-E-0003.bin"
private noncomputable def ep0001100011_4 : Blocks := edgeBlocks% "full/vectors/0001100011-E-0004.bin"
noncomputable def ep0001100011 : Blocks := (Blocks.join (Blocks.join ep0001100011_0 ep0001100011_1) (Blocks.join ep0001100011_2 (Blocks.join ep0001100011_3 ep0001100011_4)))
private theorem idp0001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110001.list =
    C ((2:ℤ)^627) * horner X vp0001100011.list + horner X ep0001100011.list := by
  exact edge_identity (B := (2:ℤ)^980) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100011 : Branch 1 (-783761639/16000000 : ℚ) vp000110001 := by
  apply branch_checked idp0001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-783761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-791761639/8000000 : ℚ) by norm_num]
  exact coverp0001100011
theorem coverp000110001 : Covers (-783761639/16000000 : ℚ) vp000110001 := join_branches bp0001100010 bp0001100011
private noncomputable def vp00011000011111_0 : Blocks := edgeBlocks% "full/vectors/00011000011111-V-0000.bin"
noncomputable def vp00011000011111 : Blocks := vp00011000011111_0
theorem coverp00011000011111 : Covers (-783261639/500000 : ℚ) vp00011000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000011110_0 : Blocks := edgeBlocks% "full/vectors/00011000011110-V-0000.bin"
noncomputable def vp00011000011110 : Blocks := vp00011000011110_0
theorem coverp00011000011110 : Covers (-782761639/500000 : ℚ) vp00011000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100001111_0 : Blocks := edgeBlocks% "full/vectors/0001100001111-V-0000.bin"
noncomputable def vp0001100001111 : Blocks := vp0001100001111_0
private theorem bp00011000011110 : Branch 0 (-782761639/1000000 : ℚ) vp0001100001111 := by
  apply branch_left_normalized (c:=vp00011000011110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-782761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-782761639/500000 : ℚ) by norm_num]
  exact coverp00011000011110
private noncomputable def ep00011000011111_0 : Blocks := edgeBlocks% "full/vectors/00011000011111-E-0000.bin"
noncomputable def ep00011000011111 : Blocks := ep00011000011111_0
private theorem idp00011000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100001111.list =
    C ((2:ℤ)^59) * horner X vp00011000011111.list + horner X ep00011000011111.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000011111 : Branch 1 (-782761639/1000000 : ℚ) vp0001100001111 := by
  apply branch_checked idp00011000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-782761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-783261639/500000 : ℚ) by norm_num]
  exact coverp00011000011111
theorem coverp0001100001111 : Covers (-782761639/1000000 : ℚ) vp0001100001111 := join_branches bp00011000011110 bp00011000011111
private noncomputable def vp00011000011101_0 : Blocks := edgeBlocks% "full/vectors/00011000011101-V-0000.bin"
noncomputable def vp00011000011101 : Blocks := vp00011000011101_0
theorem coverp00011000011101 : Covers (-782261639/500000 : ℚ) vp00011000011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000011100_0 : Blocks := edgeBlocks% "full/vectors/00011000011100-V-0000.bin"
noncomputable def vp00011000011100 : Blocks := vp00011000011100_0
theorem coverp00011000011100 : Covers (-781761639/500000 : ℚ) vp00011000011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100001110_0 : Blocks := edgeBlocks% "full/vectors/0001100001110-V-0000.bin"
noncomputable def vp0001100001110 : Blocks := vp0001100001110_0
private theorem bp00011000011100 : Branch 0 (-781761639/1000000 : ℚ) vp0001100001110 := by
  apply branch_left_normalized (c:=vp00011000011100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-781761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-781761639/500000 : ℚ) by norm_num]
  exact coverp00011000011100
private noncomputable def ep00011000011101_0 : Blocks := edgeBlocks% "full/vectors/00011000011101-E-0000.bin"
noncomputable def ep00011000011101 : Blocks := ep00011000011101_0
private theorem idp00011000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100001110.list =
    C ((2:ℤ)^59) * horner X vp00011000011101.list + horner X ep00011000011101.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000011101 : Branch 1 (-781761639/1000000 : ℚ) vp0001100001110 := by
  apply branch_checked idp00011000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-781761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-782261639/500000 : ℚ) by norm_num]
  exact coverp00011000011101
theorem coverp0001100001110 : Covers (-781761639/1000000 : ℚ) vp0001100001110 := join_branches bp00011000011100 bp00011000011101
private noncomputable def vp000110000111_0 : Blocks := edgeBlocks% "full/vectors/000110000111-V-0000.bin"
noncomputable def vp000110000111 : Blocks := vp000110000111_0
private theorem bp0001100001110 : Branch 0 (-781761639/2000000 : ℚ) vp000110000111 := by
  apply branch_left_normalized (c:=vp0001100001110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-781761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-781761639/1000000 : ℚ) by norm_num]
  exact coverp0001100001110
private noncomputable def ep0001100001111_0 : Blocks := edgeBlocks% "full/vectors/0001100001111-E-0000.bin"
noncomputable def ep0001100001111 : Blocks := ep0001100001111_0
private theorem idp0001100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110000111.list =
    C ((2:ℤ)^97) * horner X vp0001100001111.list + horner X ep0001100001111.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100001111 : Branch 1 (-781761639/2000000 : ℚ) vp000110000111 := by
  apply branch_checked idp0001100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-781761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-782761639/1000000 : ℚ) by norm_num]
  exact coverp0001100001111
theorem coverp000110000111 : Covers (-781761639/2000000 : ℚ) vp000110000111 := join_branches bp0001100001110 bp0001100001111
private noncomputable def vp00011000011011_0 : Blocks := edgeBlocks% "full/vectors/00011000011011-V-0000.bin"
noncomputable def vp00011000011011 : Blocks := vp00011000011011_0
theorem coverp00011000011011 : Covers (-781261639/500000 : ℚ) vp00011000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000011010_0 : Blocks := edgeBlocks% "full/vectors/00011000011010-V-0000.bin"
noncomputable def vp00011000011010 : Blocks := vp00011000011010_0
theorem coverp00011000011010 : Covers (-780761639/500000 : ℚ) vp00011000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100001101_0 : Blocks := edgeBlocks% "full/vectors/0001100001101-V-0000.bin"
noncomputable def vp0001100001101 : Blocks := vp0001100001101_0
private theorem bp00011000011010 : Branch 0 (-780761639/1000000 : ℚ) vp0001100001101 := by
  apply branch_left_normalized (c:=vp00011000011010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-780761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-780761639/500000 : ℚ) by norm_num]
  exact coverp00011000011010
private noncomputable def ep00011000011011_0 : Blocks := edgeBlocks% "full/vectors/00011000011011-E-0000.bin"
noncomputable def ep00011000011011 : Blocks := ep00011000011011_0
private theorem idp00011000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100001101.list =
    C ((2:ℤ)^59) * horner X vp00011000011011.list + horner X ep00011000011011.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000011011 : Branch 1 (-780761639/1000000 : ℚ) vp0001100001101 := by
  apply branch_checked idp00011000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-780761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-781261639/500000 : ℚ) by norm_num]
  exact coverp00011000011011
theorem coverp0001100001101 : Covers (-780761639/1000000 : ℚ) vp0001100001101 := join_branches bp00011000011010 bp00011000011011
private noncomputable def vp00011000011001_0 : Blocks := edgeBlocks% "full/vectors/00011000011001-V-0000.bin"
noncomputable def vp00011000011001 : Blocks := vp00011000011001_0
theorem coverp00011000011001 : Covers (-780261639/500000 : ℚ) vp00011000011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000011000_0 : Blocks := edgeBlocks% "full/vectors/00011000011000-V-0000.bin"
noncomputable def vp00011000011000 : Blocks := vp00011000011000_0
theorem coverp00011000011000 : Covers (-779761639/500000 : ℚ) vp00011000011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100001100_0 : Blocks := edgeBlocks% "full/vectors/0001100001100-V-0000.bin"
noncomputable def vp0001100001100 : Blocks := vp0001100001100_0
private theorem bp00011000011000 : Branch 0 (-779761639/1000000 : ℚ) vp0001100001100 := by
  apply branch_left_normalized (c:=vp00011000011000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-779761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-779761639/500000 : ℚ) by norm_num]
  exact coverp00011000011000
private noncomputable def ep00011000011001_0 : Blocks := edgeBlocks% "full/vectors/00011000011001-E-0000.bin"
noncomputable def ep00011000011001 : Blocks := ep00011000011001_0
private theorem idp00011000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100001100.list =
    C ((2:ℤ)^59) * horner X vp00011000011001.list + horner X ep00011000011001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000011001 : Branch 1 (-779761639/1000000 : ℚ) vp0001100001100 := by
  apply branch_checked idp00011000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-779761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-780261639/500000 : ℚ) by norm_num]
  exact coverp00011000011001
theorem coverp0001100001100 : Covers (-779761639/1000000 : ℚ) vp0001100001100 := join_branches bp00011000011000 bp00011000011001
private noncomputable def vp000110000110_0 : Blocks := edgeBlocks% "full/vectors/000110000110-V-0000.bin"
noncomputable def vp000110000110 : Blocks := vp000110000110_0
private theorem bp0001100001100 : Branch 0 (-779761639/2000000 : ℚ) vp000110000110 := by
  apply branch_left_normalized (c:=vp0001100001100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-779761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-779761639/1000000 : ℚ) by norm_num]
  exact coverp0001100001100
private noncomputable def ep0001100001101_0 : Blocks := edgeBlocks% "full/vectors/0001100001101-E-0000.bin"
noncomputable def ep0001100001101 : Blocks := ep0001100001101_0
private theorem idp0001100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110000110.list =
    C ((2:ℤ)^99) * horner X vp0001100001101.list + horner X ep0001100001101.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100001101 : Branch 1 (-779761639/2000000 : ℚ) vp000110000110 := by
  apply branch_checked idp0001100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-779761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-780761639/1000000 : ℚ) by norm_num]
  exact coverp0001100001101
theorem coverp000110000110 : Covers (-779761639/2000000 : ℚ) vp000110000110 := join_branches bp0001100001100 bp0001100001101
private noncomputable def vp00011000011_0 : Blocks := edgeBlocks% "full/vectors/00011000011-V-0000.bin"
private noncomputable def vp00011000011_1 : Blocks := edgeBlocks% "full/vectors/00011000011-V-0001.bin"
noncomputable def vp00011000011 : Blocks := (Blocks.join vp00011000011_0 vp00011000011_1)
private theorem bp000110000110 : Branch 0 (-779761639/4000000 : ℚ) vp00011000011 := by
  apply branch_left_normalized (c:=vp000110000110) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-779761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-779761639/2000000 : ℚ) by norm_num]
  exact coverp000110000110
private noncomputable def ep000110000111_0 : Blocks := edgeBlocks% "full/vectors/000110000111-E-0000.bin"
private noncomputable def ep000110000111_1 : Blocks := edgeBlocks% "full/vectors/000110000111-E-0001.bin"
noncomputable def ep000110000111 : Blocks := (Blocks.join ep000110000111_0 ep000110000111_1)
private theorem idp000110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011000011.list =
    C ((2:ℤ)^175) * horner X vp000110000111.list + horner X ep000110000111.list := by
  exact edge_identity (B := (2:ℤ)^339) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110000111 : Branch 1 (-779761639/4000000 : ℚ) vp00011000011 := by
  apply branch_checked idp000110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-779761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-781761639/2000000 : ℚ) by norm_num]
  exact coverp000110000111
theorem coverp00011000011 : Covers (-779761639/4000000 : ℚ) vp00011000011 := join_branches bp000110000110 bp000110000111
private noncomputable def vp00011000010111_0 : Blocks := edgeBlocks% "full/vectors/00011000010111-V-0000.bin"
noncomputable def vp00011000010111 : Blocks := vp00011000010111_0
theorem coverp00011000010111 : Covers (-779261639/500000 : ℚ) vp00011000010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000010110_0 : Blocks := edgeBlocks% "full/vectors/00011000010110-V-0000.bin"
noncomputable def vp00011000010110 : Blocks := vp00011000010110_0
theorem coverp00011000010110 : Covers (-778761639/500000 : ℚ) vp00011000010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100001011_0 : Blocks := edgeBlocks% "full/vectors/0001100001011-V-0000.bin"
noncomputable def vp0001100001011 : Blocks := vp0001100001011_0
private theorem bp00011000010110 : Branch 0 (-778761639/1000000 : ℚ) vp0001100001011 := by
  apply branch_left_normalized (c:=vp00011000010110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-778761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-778761639/500000 : ℚ) by norm_num]
  exact coverp00011000010110
private noncomputable def ep00011000010111_0 : Blocks := edgeBlocks% "full/vectors/00011000010111-E-0000.bin"
noncomputable def ep00011000010111 : Blocks := ep00011000010111_0
private theorem idp00011000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100001011.list =
    C ((2:ℤ)^59) * horner X vp00011000010111.list + horner X ep00011000010111.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000010111 : Branch 1 (-778761639/1000000 : ℚ) vp0001100001011 := by
  apply branch_checked idp00011000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-778761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-779261639/500000 : ℚ) by norm_num]
  exact coverp00011000010111
theorem coverp0001100001011 : Covers (-778761639/1000000 : ℚ) vp0001100001011 := join_branches bp00011000010110 bp00011000010111
private noncomputable def vp00011000010101_0 : Blocks := edgeBlocks% "full/vectors/00011000010101-V-0000.bin"
noncomputable def vp00011000010101 : Blocks := vp00011000010101_0
theorem coverp00011000010101 : Covers (-778261639/500000 : ℚ) vp00011000010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000010100_0 : Blocks := edgeBlocks% "full/vectors/00011000010100-V-0000.bin"
noncomputable def vp00011000010100 : Blocks := vp00011000010100_0
theorem coverp00011000010100 : Covers (-777761639/500000 : ℚ) vp00011000010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100001010_0 : Blocks := edgeBlocks% "full/vectors/0001100001010-V-0000.bin"
noncomputable def vp0001100001010 : Blocks := vp0001100001010_0
private theorem bp00011000010100 : Branch 0 (-777761639/1000000 : ℚ) vp0001100001010 := by
  apply branch_left_normalized (c:=vp00011000010100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-777761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-777761639/500000 : ℚ) by norm_num]
  exact coverp00011000010100
private noncomputable def ep00011000010101_0 : Blocks := edgeBlocks% "full/vectors/00011000010101-E-0000.bin"
noncomputable def ep00011000010101 : Blocks := ep00011000010101_0
private theorem idp00011000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100001010.list =
    C ((2:ℤ)^58) * horner X vp00011000010101.list + horner X ep00011000010101.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000010101 : Branch 1 (-777761639/1000000 : ℚ) vp0001100001010 := by
  apply branch_checked idp00011000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-777761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-778261639/500000 : ℚ) by norm_num]
  exact coverp00011000010101
theorem coverp0001100001010 : Covers (-777761639/1000000 : ℚ) vp0001100001010 := join_branches bp00011000010100 bp00011000010101
private noncomputable def vp000110000101_0 : Blocks := edgeBlocks% "full/vectors/000110000101-V-0000.bin"
noncomputable def vp000110000101 : Blocks := vp000110000101_0
private theorem bp0001100001010 : Branch 0 (-777761639/2000000 : ℚ) vp000110000101 := by
  apply branch_left_normalized (c:=vp0001100001010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-777761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-777761639/1000000 : ℚ) by norm_num]
  exact coverp0001100001010
private noncomputable def ep0001100001011_0 : Blocks := edgeBlocks% "full/vectors/0001100001011-E-0000.bin"
noncomputable def ep0001100001011 : Blocks := ep0001100001011_0
private theorem idp0001100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110000101.list =
    C ((2:ℤ)^98) * horner X vp0001100001011.list + horner X ep0001100001011.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100001011 : Branch 1 (-777761639/2000000 : ℚ) vp000110000101 := by
  apply branch_checked idp0001100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-777761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-778761639/1000000 : ℚ) by norm_num]
  exact coverp0001100001011
theorem coverp000110000101 : Covers (-777761639/2000000 : ℚ) vp000110000101 := join_branches bp0001100001010 bp0001100001011
private noncomputable def vp00011000010011_0 : Blocks := edgeBlocks% "full/vectors/00011000010011-V-0000.bin"
noncomputable def vp00011000010011 : Blocks := vp00011000010011_0
theorem coverp00011000010011 : Covers (-777261639/500000 : ℚ) vp00011000010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000010010_0 : Blocks := edgeBlocks% "full/vectors/00011000010010-V-0000.bin"
noncomputable def vp00011000010010 : Blocks := vp00011000010010_0
theorem coverp00011000010010 : Covers (-776761639/500000 : ℚ) vp00011000010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100001001_0 : Blocks := edgeBlocks% "full/vectors/0001100001001-V-0000.bin"
noncomputable def vp0001100001001 : Blocks := vp0001100001001_0
private theorem bp00011000010010 : Branch 0 (-776761639/1000000 : ℚ) vp0001100001001 := by
  apply branch_left_normalized (c:=vp00011000010010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-776761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-776761639/500000 : ℚ) by norm_num]
  exact coverp00011000010010
private noncomputable def ep00011000010011_0 : Blocks := edgeBlocks% "full/vectors/00011000010011-E-0000.bin"
noncomputable def ep00011000010011 : Blocks := ep00011000010011_0
private theorem idp00011000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100001001.list =
    C ((2:ℤ)^59) * horner X vp00011000010011.list + horner X ep00011000010011.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000010011 : Branch 1 (-776761639/1000000 : ℚ) vp0001100001001 := by
  apply branch_checked idp00011000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-776761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-777261639/500000 : ℚ) by norm_num]
  exact coverp00011000010011
theorem coverp0001100001001 : Covers (-776761639/1000000 : ℚ) vp0001100001001 := join_branches bp00011000010010 bp00011000010011
private noncomputable def vp00011000010001_0 : Blocks := edgeBlocks% "full/vectors/00011000010001-V-0000.bin"
noncomputable def vp00011000010001 : Blocks := vp00011000010001_0
theorem coverp00011000010001 : Covers (-776261639/500000 : ℚ) vp00011000010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000010000_0 : Blocks := edgeBlocks% "full/vectors/00011000010000-V-0000.bin"
noncomputable def vp00011000010000 : Blocks := vp00011000010000_0
theorem coverp00011000010000 : Covers (-775761639/500000 : ℚ) vp00011000010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100001000_0 : Blocks := edgeBlocks% "full/vectors/0001100001000-V-0000.bin"
noncomputable def vp0001100001000 : Blocks := vp0001100001000_0
private theorem bp00011000010000 : Branch 0 (-775761639/1000000 : ℚ) vp0001100001000 := by
  apply branch_left_normalized (c:=vp00011000010000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-775761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-775761639/500000 : ℚ) by norm_num]
  exact coverp00011000010000
private noncomputable def ep00011000010001_0 : Blocks := edgeBlocks% "full/vectors/00011000010001-E-0000.bin"
noncomputable def ep00011000010001 : Blocks := ep00011000010001_0
private theorem idp00011000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100001000.list =
    C ((2:ℤ)^58) * horner X vp00011000010001.list + horner X ep00011000010001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000010001 : Branch 1 (-775761639/1000000 : ℚ) vp0001100001000 := by
  apply branch_checked idp00011000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-775761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-776261639/500000 : ℚ) by norm_num]
  exact coverp00011000010001
theorem coverp0001100001000 : Covers (-775761639/1000000 : ℚ) vp0001100001000 := join_branches bp00011000010000 bp00011000010001
private noncomputable def vp000110000100_0 : Blocks := edgeBlocks% "full/vectors/000110000100-V-0000.bin"
noncomputable def vp000110000100 : Blocks := vp000110000100_0
private theorem bp0001100001000 : Branch 0 (-775761639/2000000 : ℚ) vp000110000100 := by
  apply branch_left_normalized (c:=vp0001100001000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-775761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-775761639/1000000 : ℚ) by norm_num]
  exact coverp0001100001000
private noncomputable def ep0001100001001_0 : Blocks := edgeBlocks% "full/vectors/0001100001001-E-0000.bin"
noncomputable def ep0001100001001 : Blocks := ep0001100001001_0
private theorem idp0001100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110000100.list =
    C ((2:ℤ)^99) * horner X vp0001100001001.list + horner X ep0001100001001.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100001001 : Branch 1 (-775761639/2000000 : ℚ) vp000110000100 := by
  apply branch_checked idp0001100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-775761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-776761639/1000000 : ℚ) by norm_num]
  exact coverp0001100001001
theorem coverp000110000100 : Covers (-775761639/2000000 : ℚ) vp000110000100 := join_branches bp0001100001000 bp0001100001001
private noncomputable def vp00011000010_0 : Blocks := edgeBlocks% "full/vectors/00011000010-V-0000.bin"
private noncomputable def vp00011000010_1 : Blocks := edgeBlocks% "full/vectors/00011000010-V-0001.bin"
noncomputable def vp00011000010 : Blocks := (Blocks.join vp00011000010_0 vp00011000010_1)
private theorem bp000110000100 : Branch 0 (-775761639/4000000 : ℚ) vp00011000010 := by
  apply branch_left_normalized (c:=vp000110000100) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-775761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-775761639/2000000 : ℚ) by norm_num]
  exact coverp000110000100
private noncomputable def ep000110000101_0 : Blocks := edgeBlocks% "full/vectors/000110000101-E-0000.bin"
private noncomputable def ep000110000101_1 : Blocks := edgeBlocks% "full/vectors/000110000101-E-0001.bin"
noncomputable def ep000110000101 : Blocks := (Blocks.join ep000110000101_0 ep000110000101_1)
private theorem idp000110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011000010.list =
    C ((2:ℤ)^176) * horner X vp000110000101.list + horner X ep000110000101.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110000101 : Branch 1 (-775761639/4000000 : ℚ) vp00011000010 := by
  apply branch_checked idp000110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-775761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-777761639/2000000 : ℚ) by norm_num]
  exact coverp000110000101
theorem coverp00011000010 : Covers (-775761639/4000000 : ℚ) vp00011000010 := join_branches bp000110000100 bp000110000101
private noncomputable def vp0001100001_0 : Blocks := edgeBlocks% "full/vectors/0001100001-V-0000.bin"
private noncomputable def vp0001100001_1 : Blocks := edgeBlocks% "full/vectors/0001100001-V-0001.bin"
private noncomputable def vp0001100001_2 : Blocks := edgeBlocks% "full/vectors/0001100001-V-0002.bin"
noncomputable def vp0001100001 : Blocks := (Blocks.join vp0001100001_0 (Blocks.join vp0001100001_1 vp0001100001_2))
private theorem bp00011000010 : Branch 0 (-775761639/8000000 : ℚ) vp0001100001 := by
  apply branch_left_normalized (c:=vp00011000010) (k:=0) (m:=163) (by decide +kernel)
  rw [show 2*(-775761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-775761639/4000000 : ℚ) by norm_num]
  exact coverp00011000010
private noncomputable def ep00011000011_0 : Blocks := edgeBlocks% "full/vectors/00011000011-E-0000.bin"
private noncomputable def ep00011000011_1 : Blocks := edgeBlocks% "full/vectors/00011000011-E-0001.bin"
private noncomputable def ep00011000011_2 : Blocks := edgeBlocks% "full/vectors/00011000011-E-0002.bin"
noncomputable def ep00011000011 : Blocks := (Blocks.join ep00011000011_0 (Blocks.join ep00011000011_1 ep00011000011_2))
private theorem idp00011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100001.list =
    C ((2:ℤ)^328) * horner X vp00011000011.list + horner X ep00011000011.list := by
  exact edge_identity (B := (2:ℤ)^556) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000011 : Branch 1 (-775761639/8000000 : ℚ) vp0001100001 := by
  apply branch_checked idp00011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-775761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-779761639/4000000 : ℚ) by norm_num]
  exact coverp00011000011
theorem coverp0001100001 : Covers (-775761639/8000000 : ℚ) vp0001100001 := join_branches bp00011000010 bp00011000011
private noncomputable def vp00011000001111_0 : Blocks := edgeBlocks% "full/vectors/00011000001111-V-0000.bin"
noncomputable def vp00011000001111 : Blocks := vp00011000001111_0
theorem coverp00011000001111 : Covers (-775261639/500000 : ℚ) vp00011000001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000001110_0 : Blocks := edgeBlocks% "full/vectors/00011000001110-V-0000.bin"
noncomputable def vp00011000001110 : Blocks := vp00011000001110_0
theorem coverp00011000001110 : Covers (-774761639/500000 : ℚ) vp00011000001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100000111_0 : Blocks := edgeBlocks% "full/vectors/0001100000111-V-0000.bin"
noncomputable def vp0001100000111 : Blocks := vp0001100000111_0
private theorem bp00011000001110 : Branch 0 (-774761639/1000000 : ℚ) vp0001100000111 := by
  apply branch_left_normalized (c:=vp00011000001110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-774761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-774761639/500000 : ℚ) by norm_num]
  exact coverp00011000001110
private noncomputable def ep00011000001111_0 : Blocks := edgeBlocks% "full/vectors/00011000001111-E-0000.bin"
noncomputable def ep00011000001111 : Blocks := ep00011000001111_0
private theorem idp00011000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100000111.list =
    C ((2:ℤ)^57) * horner X vp00011000001111.list + horner X ep00011000001111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000001111 : Branch 1 (-774761639/1000000 : ℚ) vp0001100000111 := by
  apply branch_checked idp00011000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-774761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-775261639/500000 : ℚ) by norm_num]
  exact coverp00011000001111
theorem coverp0001100000111 : Covers (-774761639/1000000 : ℚ) vp0001100000111 := join_branches bp00011000001110 bp00011000001111
private noncomputable def vp00011000001101_0 : Blocks := edgeBlocks% "full/vectors/00011000001101-V-0000.bin"
noncomputable def vp00011000001101 : Blocks := vp00011000001101_0
theorem coverp00011000001101 : Covers (-774261639/500000 : ℚ) vp00011000001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000001100_0 : Blocks := edgeBlocks% "full/vectors/00011000001100-V-0000.bin"
noncomputable def vp00011000001100 : Blocks := vp00011000001100_0
theorem coverp00011000001100 : Covers (-773761639/500000 : ℚ) vp00011000001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100000110_0 : Blocks := edgeBlocks% "full/vectors/0001100000110-V-0000.bin"
noncomputable def vp0001100000110 : Blocks := vp0001100000110_0
private theorem bp00011000001100 : Branch 0 (-773761639/1000000 : ℚ) vp0001100000110 := by
  apply branch_left_normalized (c:=vp00011000001100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-773761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-773761639/500000 : ℚ) by norm_num]
  exact coverp00011000001100
private noncomputable def ep00011000001101_0 : Blocks := edgeBlocks% "full/vectors/00011000001101-E-0000.bin"
noncomputable def ep00011000001101 : Blocks := ep00011000001101_0
private theorem idp00011000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100000110.list =
    C ((2:ℤ)^58) * horner X vp00011000001101.list + horner X ep00011000001101.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000001101 : Branch 1 (-773761639/1000000 : ℚ) vp0001100000110 := by
  apply branch_checked idp00011000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-773761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-774261639/500000 : ℚ) by norm_num]
  exact coverp00011000001101
theorem coverp0001100000110 : Covers (-773761639/1000000 : ℚ) vp0001100000110 := join_branches bp00011000001100 bp00011000001101
private noncomputable def vp000110000011_0 : Blocks := edgeBlocks% "full/vectors/000110000011-V-0000.bin"
noncomputable def vp000110000011 : Blocks := vp000110000011_0
private theorem bp0001100000110 : Branch 0 (-773761639/2000000 : ℚ) vp000110000011 := by
  apply branch_left_normalized (c:=vp0001100000110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-773761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-773761639/1000000 : ℚ) by norm_num]
  exact coverp0001100000110
private noncomputable def ep0001100000111_0 : Blocks := edgeBlocks% "full/vectors/0001100000111-E-0000.bin"
noncomputable def ep0001100000111 : Blocks := ep0001100000111_0
private theorem idp0001100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110000011.list =
    C ((2:ℤ)^98) * horner X vp0001100000111.list + horner X ep0001100000111.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100000111 : Branch 1 (-773761639/2000000 : ℚ) vp000110000011 := by
  apply branch_checked idp0001100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-773761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-774761639/1000000 : ℚ) by norm_num]
  exact coverp0001100000111
theorem coverp000110000011 : Covers (-773761639/2000000 : ℚ) vp000110000011 := join_branches bp0001100000110 bp0001100000111
private noncomputable def vp00011000001011_0 : Blocks := edgeBlocks% "full/vectors/00011000001011-V-0000.bin"
noncomputable def vp00011000001011 : Blocks := vp00011000001011_0
theorem coverp00011000001011 : Covers (-773261639/500000 : ℚ) vp00011000001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000001010_0 : Blocks := edgeBlocks% "full/vectors/00011000001010-V-0000.bin"
noncomputable def vp00011000001010 : Blocks := vp00011000001010_0
theorem coverp00011000001010 : Covers (-772761639/500000 : ℚ) vp00011000001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100000101_0 : Blocks := edgeBlocks% "full/vectors/0001100000101-V-0000.bin"
noncomputable def vp0001100000101 : Blocks := vp0001100000101_0
private theorem bp00011000001010 : Branch 0 (-772761639/1000000 : ℚ) vp0001100000101 := by
  apply branch_left_normalized (c:=vp00011000001010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-772761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-772761639/500000 : ℚ) by norm_num]
  exact coverp00011000001010
private noncomputable def ep00011000001011_0 : Blocks := edgeBlocks% "full/vectors/00011000001011-E-0000.bin"
noncomputable def ep00011000001011 : Blocks := ep00011000001011_0
private theorem idp00011000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100000101.list =
    C ((2:ℤ)^58) * horner X vp00011000001011.list + horner X ep00011000001011.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000001011 : Branch 1 (-772761639/1000000 : ℚ) vp0001100000101 := by
  apply branch_checked idp00011000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-772761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-773261639/500000 : ℚ) by norm_num]
  exact coverp00011000001011
theorem coverp0001100000101 : Covers (-772761639/1000000 : ℚ) vp0001100000101 := join_branches bp00011000001010 bp00011000001011
private noncomputable def vp00011000001001_0 : Blocks := edgeBlocks% "full/vectors/00011000001001-V-0000.bin"
noncomputable def vp00011000001001 : Blocks := vp00011000001001_0
theorem coverp00011000001001 : Covers (-772261639/500000 : ℚ) vp00011000001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000001000_0 : Blocks := edgeBlocks% "full/vectors/00011000001000-V-0000.bin"
noncomputable def vp00011000001000 : Blocks := vp00011000001000_0
theorem coverp00011000001000 : Covers (-771761639/500000 : ℚ) vp00011000001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100000100_0 : Blocks := edgeBlocks% "full/vectors/0001100000100-V-0000.bin"
noncomputable def vp0001100000100 : Blocks := vp0001100000100_0
private theorem bp00011000001000 : Branch 0 (-771761639/1000000 : ℚ) vp0001100000100 := by
  apply branch_left_normalized (c:=vp00011000001000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-771761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-771761639/500000 : ℚ) by norm_num]
  exact coverp00011000001000
private noncomputable def ep00011000001001_0 : Blocks := edgeBlocks% "full/vectors/00011000001001-E-0000.bin"
noncomputable def ep00011000001001 : Blocks := ep00011000001001_0
private theorem idp00011000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100000100.list =
    C ((2:ℤ)^59) * horner X vp00011000001001.list + horner X ep00011000001001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000001001 : Branch 1 (-771761639/1000000 : ℚ) vp0001100000100 := by
  apply branch_checked idp00011000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-771761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-772261639/500000 : ℚ) by norm_num]
  exact coverp00011000001001
theorem coverp0001100000100 : Covers (-771761639/1000000 : ℚ) vp0001100000100 := join_branches bp00011000001000 bp00011000001001
private noncomputable def vp000110000010_0 : Blocks := edgeBlocks% "full/vectors/000110000010-V-0000.bin"
noncomputable def vp000110000010 : Blocks := vp000110000010_0
private theorem bp0001100000100 : Branch 0 (-771761639/2000000 : ℚ) vp000110000010 := by
  apply branch_left_normalized (c:=vp0001100000100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-771761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-771761639/1000000 : ℚ) by norm_num]
  exact coverp0001100000100
private noncomputable def ep0001100000101_0 : Blocks := edgeBlocks% "full/vectors/0001100000101-E-0000.bin"
noncomputable def ep0001100000101 : Blocks := ep0001100000101_0
private theorem idp0001100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110000010.list =
    C ((2:ℤ)^98) * horner X vp0001100000101.list + horner X ep0001100000101.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100000101 : Branch 1 (-771761639/2000000 : ℚ) vp000110000010 := by
  apply branch_checked idp0001100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-771761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-772761639/1000000 : ℚ) by norm_num]
  exact coverp0001100000101
theorem coverp000110000010 : Covers (-771761639/2000000 : ℚ) vp000110000010 := join_branches bp0001100000100 bp0001100000101
private noncomputable def vp00011000001_0 : Blocks := edgeBlocks% "full/vectors/00011000001-V-0000.bin"
private noncomputable def vp00011000001_1 : Blocks := edgeBlocks% "full/vectors/00011000001-V-0001.bin"
noncomputable def vp00011000001 : Blocks := (Blocks.join vp00011000001_0 vp00011000001_1)
private theorem bp000110000010 : Branch 0 (-771761639/4000000 : ℚ) vp00011000001 := by
  apply branch_left_normalized (c:=vp000110000010) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-771761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-771761639/2000000 : ℚ) by norm_num]
  exact coverp000110000010
private noncomputable def ep000110000011_0 : Blocks := edgeBlocks% "full/vectors/000110000011-E-0000.bin"
private noncomputable def ep000110000011_1 : Blocks := edgeBlocks% "full/vectors/000110000011-E-0001.bin"
noncomputable def ep000110000011 : Blocks := (Blocks.join ep000110000011_0 ep000110000011_1)
private theorem idp000110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011000001.list =
    C ((2:ℤ)^176) * horner X vp000110000011.list + horner X ep000110000011.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110000011 : Branch 1 (-771761639/4000000 : ℚ) vp00011000001 := by
  apply branch_checked idp000110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-771761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-773761639/2000000 : ℚ) by norm_num]
  exact coverp000110000011
theorem coverp00011000001 : Covers (-771761639/4000000 : ℚ) vp00011000001 := join_branches bp000110000010 bp000110000011
private noncomputable def vp00011000000111_0 : Blocks := edgeBlocks% "full/vectors/00011000000111-V-0000.bin"
noncomputable def vp00011000000111 : Blocks := vp00011000000111_0
theorem coverp00011000000111 : Covers (-771261639/500000 : ℚ) vp00011000000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000000110_0 : Blocks := edgeBlocks% "full/vectors/00011000000110-V-0000.bin"
noncomputable def vp00011000000110 : Blocks := vp00011000000110_0
theorem coverp00011000000110 : Covers (-770761639/500000 : ℚ) vp00011000000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100000011_0 : Blocks := edgeBlocks% "full/vectors/0001100000011-V-0000.bin"
noncomputable def vp0001100000011 : Blocks := vp0001100000011_0
private theorem bp00011000000110 : Branch 0 (-770761639/1000000 : ℚ) vp0001100000011 := by
  apply branch_left_normalized (c:=vp00011000000110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-770761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-770761639/500000 : ℚ) by norm_num]
  exact coverp00011000000110
private noncomputable def ep00011000000111_0 : Blocks := edgeBlocks% "full/vectors/00011000000111-E-0000.bin"
noncomputable def ep00011000000111 : Blocks := ep00011000000111_0
private theorem idp00011000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100000011.list =
    C ((2:ℤ)^59) * horner X vp00011000000111.list + horner X ep00011000000111.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000000111 : Branch 1 (-770761639/1000000 : ℚ) vp0001100000011 := by
  apply branch_checked idp00011000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-770761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-771261639/500000 : ℚ) by norm_num]
  exact coverp00011000000111
theorem coverp0001100000011 : Covers (-770761639/1000000 : ℚ) vp0001100000011 := join_branches bp00011000000110 bp00011000000111
private noncomputable def vp00011000000101_0 : Blocks := edgeBlocks% "full/vectors/00011000000101-V-0000.bin"
noncomputable def vp00011000000101 : Blocks := vp00011000000101_0
theorem coverp00011000000101 : Covers (-770261639/500000 : ℚ) vp00011000000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000000100_0 : Blocks := edgeBlocks% "full/vectors/00011000000100-V-0000.bin"
noncomputable def vp00011000000100 : Blocks := vp00011000000100_0
theorem coverp00011000000100 : Covers (-769761639/500000 : ℚ) vp00011000000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100000010_0 : Blocks := edgeBlocks% "full/vectors/0001100000010-V-0000.bin"
noncomputable def vp0001100000010 : Blocks := vp0001100000010_0
private theorem bp00011000000100 : Branch 0 (-769761639/1000000 : ℚ) vp0001100000010 := by
  apply branch_left_normalized (c:=vp00011000000100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-769761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-769761639/500000 : ℚ) by norm_num]
  exact coverp00011000000100
private noncomputable def ep00011000000101_0 : Blocks := edgeBlocks% "full/vectors/00011000000101-E-0000.bin"
noncomputable def ep00011000000101 : Blocks := ep00011000000101_0
private theorem idp00011000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100000010.list =
    C ((2:ℤ)^59) * horner X vp00011000000101.list + horner X ep00011000000101.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000000101 : Branch 1 (-769761639/1000000 : ℚ) vp0001100000010 := by
  apply branch_checked idp00011000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-769761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-770261639/500000 : ℚ) by norm_num]
  exact coverp00011000000101
theorem coverp0001100000010 : Covers (-769761639/1000000 : ℚ) vp0001100000010 := join_branches bp00011000000100 bp00011000000101
private noncomputable def vp000110000001_0 : Blocks := edgeBlocks% "full/vectors/000110000001-V-0000.bin"
noncomputable def vp000110000001 : Blocks := vp000110000001_0
private theorem bp0001100000010 : Branch 0 (-769761639/2000000 : ℚ) vp000110000001 := by
  apply branch_left_normalized (c:=vp0001100000010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-769761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-769761639/1000000 : ℚ) by norm_num]
  exact coverp0001100000010
private noncomputable def ep0001100000011_0 : Blocks := edgeBlocks% "full/vectors/0001100000011-E-0000.bin"
noncomputable def ep0001100000011 : Blocks := ep0001100000011_0
private theorem idp0001100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110000001.list =
    C ((2:ℤ)^99) * horner X vp0001100000011.list + horner X ep0001100000011.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100000011 : Branch 1 (-769761639/2000000 : ℚ) vp000110000001 := by
  apply branch_checked idp0001100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-769761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-770761639/1000000 : ℚ) by norm_num]
  exact coverp0001100000011
theorem coverp000110000001 : Covers (-769761639/2000000 : ℚ) vp000110000001 := join_branches bp0001100000010 bp0001100000011
private noncomputable def vp00011000000011_0 : Blocks := edgeBlocks% "full/vectors/00011000000011-V-0000.bin"
noncomputable def vp00011000000011 : Blocks := vp00011000000011_0
theorem coverp00011000000011 : Covers (-769261639/500000 : ℚ) vp00011000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000000010_0 : Blocks := edgeBlocks% "full/vectors/00011000000010-V-0000.bin"
noncomputable def vp00011000000010 : Blocks := vp00011000000010_0
theorem coverp00011000000010 : Covers (-768761639/500000 : ℚ) vp00011000000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100000001_0 : Blocks := edgeBlocks% "full/vectors/0001100000001-V-0000.bin"
noncomputable def vp0001100000001 : Blocks := vp0001100000001_0
private theorem bp00011000000010 : Branch 0 (-768761639/1000000 : ℚ) vp0001100000001 := by
  apply branch_left_normalized (c:=vp00011000000010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-768761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-768761639/500000 : ℚ) by norm_num]
  exact coverp00011000000010
private noncomputable def ep00011000000011_0 : Blocks := edgeBlocks% "full/vectors/00011000000011-E-0000.bin"
noncomputable def ep00011000000011 : Blocks := ep00011000000011_0
private theorem idp00011000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100000001.list =
    C ((2:ℤ)^59) * horner X vp00011000000011.list + horner X ep00011000000011.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000000011 : Branch 1 (-768761639/1000000 : ℚ) vp0001100000001 := by
  apply branch_checked idp00011000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-768761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-769261639/500000 : ℚ) by norm_num]
  exact coverp00011000000011
theorem coverp0001100000001 : Covers (-768761639/1000000 : ℚ) vp0001100000001 := join_branches bp00011000000010 bp00011000000011
private noncomputable def vp00011000000001_0 : Blocks := edgeBlocks% "full/vectors/00011000000001-V-0000.bin"
noncomputable def vp00011000000001 : Blocks := vp00011000000001_0
theorem coverp00011000000001 : Covers (-768261639/500000 : ℚ) vp00011000000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011000000000_0 : Blocks := edgeBlocks% "full/vectors/00011000000000-V-0000.bin"
noncomputable def vp00011000000000 : Blocks := vp00011000000000_0
theorem coverp00011000000000 : Covers (-767761639/500000 : ℚ) vp00011000000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100000000_0 : Blocks := edgeBlocks% "full/vectors/0001100000000-V-0000.bin"
noncomputable def vp0001100000000 : Blocks := vp0001100000000_0
private theorem bp00011000000000 : Branch 0 (-767761639/1000000 : ℚ) vp0001100000000 := by
  apply branch_left_normalized (c:=vp00011000000000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-767761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-767761639/500000 : ℚ) by norm_num]
  exact coverp00011000000000
private noncomputable def ep00011000000001_0 : Blocks := edgeBlocks% "full/vectors/00011000000001-E-0000.bin"
noncomputable def ep00011000000001 : Blocks := ep00011000000001_0
private theorem idp00011000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100000000.list =
    C ((2:ℤ)^58) * horner X vp00011000000001.list + horner X ep00011000000001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000000001 : Branch 1 (-767761639/1000000 : ℚ) vp0001100000000 := by
  apply branch_checked idp00011000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-767761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-768261639/500000 : ℚ) by norm_num]
  exact coverp00011000000001
theorem coverp0001100000000 : Covers (-767761639/1000000 : ℚ) vp0001100000000 := join_branches bp00011000000000 bp00011000000001
private noncomputable def vp000110000000_0 : Blocks := edgeBlocks% "full/vectors/000110000000-V-0000.bin"
noncomputable def vp000110000000 : Blocks := vp000110000000_0
private theorem bp0001100000000 : Branch 0 (-767761639/2000000 : ℚ) vp000110000000 := by
  apply branch_left_normalized (c:=vp0001100000000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-767761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-767761639/1000000 : ℚ) by norm_num]
  exact coverp0001100000000
private noncomputable def ep0001100000001_0 : Blocks := edgeBlocks% "full/vectors/0001100000001-E-0000.bin"
noncomputable def ep0001100000001 : Blocks := ep0001100000001_0
private theorem idp0001100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110000000.list =
    C ((2:ℤ)^98) * horner X vp0001100000001.list + horner X ep0001100000001.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100000001 : Branch 1 (-767761639/2000000 : ℚ) vp000110000000 := by
  apply branch_checked idp0001100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-767761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-768761639/1000000 : ℚ) by norm_num]
  exact coverp0001100000001
theorem coverp000110000000 : Covers (-767761639/2000000 : ℚ) vp000110000000 := join_branches bp0001100000000 bp0001100000001
private noncomputable def vp00011000000_0 : Blocks := edgeBlocks% "full/vectors/00011000000-V-0000.bin"
private noncomputable def vp00011000000_1 : Blocks := edgeBlocks% "full/vectors/00011000000-V-0001.bin"
noncomputable def vp00011000000 : Blocks := (Blocks.join vp00011000000_0 vp00011000000_1)
private theorem bp000110000000 : Branch 0 (-767761639/4000000 : ℚ) vp00011000000 := by
  apply branch_left_normalized (c:=vp000110000000) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-767761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-767761639/2000000 : ℚ) by norm_num]
  exact coverp000110000000
private noncomputable def ep000110000001_0 : Blocks := edgeBlocks% "full/vectors/000110000001-E-0000.bin"
private noncomputable def ep000110000001_1 : Blocks := edgeBlocks% "full/vectors/000110000001-E-0001.bin"
noncomputable def ep000110000001 : Blocks := (Blocks.join ep000110000001_0 ep000110000001_1)
private theorem idp000110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011000000.list =
    C ((2:ℤ)^174) * horner X vp000110000001.list + horner X ep000110000001.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110000001 : Branch 1 (-767761639/4000000 : ℚ) vp00011000000 := by
  apply branch_checked idp000110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-767761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-769761639/2000000 : ℚ) by norm_num]
  exact coverp000110000001
theorem coverp00011000000 : Covers (-767761639/4000000 : ℚ) vp00011000000 := join_branches bp000110000000 bp000110000001
private noncomputable def vp0001100000_0 : Blocks := edgeBlocks% "full/vectors/0001100000-V-0000.bin"
private noncomputable def vp0001100000_1 : Blocks := edgeBlocks% "full/vectors/0001100000-V-0001.bin"
private noncomputable def vp0001100000_2 : Blocks := edgeBlocks% "full/vectors/0001100000-V-0002.bin"
noncomputable def vp0001100000 : Blocks := (Blocks.join vp0001100000_0 (Blocks.join vp0001100000_1 vp0001100000_2))
private theorem bp00011000000 : Branch 0 (-767761639/8000000 : ℚ) vp0001100000 := by
  apply branch_left_normalized (c:=vp00011000000) (k:=0) (m:=163) (by decide +kernel)
  rw [show 2*(-767761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-767761639/4000000 : ℚ) by norm_num]
  exact coverp00011000000
private noncomputable def ep00011000001_0 : Blocks := edgeBlocks% "full/vectors/00011000001-E-0000.bin"
private noncomputable def ep00011000001_1 : Blocks := edgeBlocks% "full/vectors/00011000001-E-0001.bin"
private noncomputable def ep00011000001_2 : Blocks := edgeBlocks% "full/vectors/00011000001-E-0002.bin"
noncomputable def ep00011000001 : Blocks := (Blocks.join ep00011000001_0 (Blocks.join ep00011000001_1 ep00011000001_2))
private theorem idp00011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100000.list =
    C ((2:ℤ)^328) * horner X vp00011000001.list + horner X ep00011000001.list := by
  exact edge_identity (B := (2:ℤ)^557) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011000001 : Branch 1 (-767761639/8000000 : ℚ) vp0001100000 := by
  apply branch_checked idp00011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-767761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-771761639/4000000 : ℚ) by norm_num]
  exact coverp00011000001
theorem coverp0001100000 : Covers (-767761639/8000000 : ℚ) vp0001100000 := join_branches bp00011000000 bp00011000001
private noncomputable def vp000110000_0 : Blocks := edgeBlocks% "full/vectors/000110000-V-0000.bin"
private noncomputable def vp000110000_1 : Blocks := edgeBlocks% "full/vectors/000110000-V-0001.bin"
private noncomputable def vp000110000_2 : Blocks := edgeBlocks% "full/vectors/000110000-V-0002.bin"
private noncomputable def vp000110000_3 : Blocks := edgeBlocks% "full/vectors/000110000-V-0003.bin"
private noncomputable def vp000110000_4 : Blocks := edgeBlocks% "full/vectors/000110000-V-0004.bin"
noncomputable def vp000110000 : Blocks := (Blocks.join (Blocks.join vp000110000_0 vp000110000_1) (Blocks.join vp000110000_2 (Blocks.join vp000110000_3 vp000110000_4)))
private theorem bp0001100000 : Branch 0 (-767761639/16000000 : ℚ) vp000110000 := by
  apply branch_left_normalized (c:=vp0001100000) (k:=0) (m:=305) (by decide +kernel)
  rw [show 2*(-767761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-767761639/8000000 : ℚ) by norm_num]
  exact coverp0001100000
private noncomputable def ep0001100001_0 : Blocks := edgeBlocks% "full/vectors/0001100001-E-0000.bin"
private noncomputable def ep0001100001_1 : Blocks := edgeBlocks% "full/vectors/0001100001-E-0001.bin"
private noncomputable def ep0001100001_2 : Blocks := edgeBlocks% "full/vectors/0001100001-E-0002.bin"
private noncomputable def ep0001100001_3 : Blocks := edgeBlocks% "full/vectors/0001100001-E-0003.bin"
private noncomputable def ep0001100001_4 : Blocks := edgeBlocks% "full/vectors/0001100001-E-0004.bin"
noncomputable def ep0001100001 : Blocks := (Blocks.join (Blocks.join ep0001100001_0 ep0001100001_1) (Blocks.join ep0001100001_2 (Blocks.join ep0001100001_3 ep0001100001_4)))
private theorem idp0001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110000.list =
    C ((2:ℤ)^631) * horner X vp0001100001.list + horner X ep0001100001.list := by
  exact edge_identity (B := (2:ℤ)^987) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100001 : Branch 1 (-767761639/16000000 : ℚ) vp000110000 := by
  apply branch_checked idp0001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-767761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-775761639/8000000 : ℚ) by norm_num]
  exact coverp0001100001
theorem coverp000110000 : Covers (-767761639/16000000 : ℚ) vp000110000 := join_branches bp0001100000 bp0001100001
private noncomputable def vp00011000_0 : Blocks := edgeBlocks% "full/vectors/00011000-V-0000.bin"
private noncomputable def vp00011000_1 : Blocks := edgeBlocks% "full/vectors/00011000-V-0001.bin"
private noncomputable def vp00011000_2 : Blocks := edgeBlocks% "full/vectors/00011000-V-0002.bin"
private noncomputable def vp00011000_3 : Blocks := edgeBlocks% "full/vectors/00011000-V-0003.bin"
private noncomputable def vp00011000_4 : Blocks := edgeBlocks% "full/vectors/00011000-V-0004.bin"
private noncomputable def vp00011000_5 : Blocks := edgeBlocks% "full/vectors/00011000-V-0005.bin"
private noncomputable def vp00011000_6 : Blocks := edgeBlocks% "full/vectors/00011000-V-0006.bin"
private noncomputable def vp00011000_7 : Blocks := edgeBlocks% "full/vectors/00011000-V-0007.bin"
private noncomputable def vp00011000_8 : Blocks := edgeBlocks% "full/vectors/00011000-V-0008.bin"
noncomputable def vp00011000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00011000_0 vp00011000_1) (Blocks.join vp00011000_2 vp00011000_3)) (Blocks.join (Blocks.join vp00011000_4 vp00011000_5) (Blocks.join vp00011000_6 (Blocks.join vp00011000_7 vp00011000_8))))
private theorem bp000110000 : Branch 0 (-767761639/32000000 : ℚ) vp00011000 := by
  apply branch_left_normalized (c:=vp000110000) (k:=0) (m:=585) (by decide +kernel)
  rw [show 2*(-767761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-767761639/16000000 : ℚ) by norm_num]
  exact coverp000110000
private noncomputable def ep000110001_0 : Blocks := edgeBlocks% "full/vectors/000110001-E-0000.bin"
private noncomputable def ep000110001_1 : Blocks := edgeBlocks% "full/vectors/000110001-E-0001.bin"
private noncomputable def ep000110001_2 : Blocks := edgeBlocks% "full/vectors/000110001-E-0002.bin"
private noncomputable def ep000110001_3 : Blocks := edgeBlocks% "full/vectors/000110001-E-0003.bin"
private noncomputable def ep000110001_4 : Blocks := edgeBlocks% "full/vectors/000110001-E-0004.bin"
private noncomputable def ep000110001_5 : Blocks := edgeBlocks% "full/vectors/000110001-E-0005.bin"
private noncomputable def ep000110001_6 : Blocks := edgeBlocks% "full/vectors/000110001-E-0006.bin"
private noncomputable def ep000110001_7 : Blocks := edgeBlocks% "full/vectors/000110001-E-0007.bin"
private noncomputable def ep000110001_8 : Blocks := edgeBlocks% "full/vectors/000110001-E-0008.bin"
noncomputable def ep000110001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000110001_0 ep000110001_1) (Blocks.join ep000110001_2 ep000110001_3)) (Blocks.join (Blocks.join ep000110001_4 ep000110001_5) (Blocks.join ep000110001_6 (Blocks.join ep000110001_7 ep000110001_8))))
private theorem idp000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011000.list =
    C ((2:ℤ)^1230) * horner X vp000110001.list + horner X ep000110001.list := by
  exact edge_identity (B := (2:ℤ)^1839) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110001 : Branch 1 (-767761639/32000000 : ℚ) vp00011000 := by
  apply branch_checked idp000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-767761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-783761639/16000000 : ℚ) by norm_num]
  exact coverp000110001
theorem coverp00011000 : Covers (-767761639/32000000 : ℚ) vp00011000 := join_branches bp000110000 bp000110001
private noncomputable def vp0001100_0 : Blocks := edgeBlocks% "full/vectors/0001100-V-0000.bin"
private noncomputable def vp0001100_1 : Blocks := edgeBlocks% "full/vectors/0001100-V-0001.bin"
private noncomputable def vp0001100_2 : Blocks := edgeBlocks% "full/vectors/0001100-V-0002.bin"
private noncomputable def vp0001100_3 : Blocks := edgeBlocks% "full/vectors/0001100-V-0003.bin"
private noncomputable def vp0001100_4 : Blocks := edgeBlocks% "full/vectors/0001100-V-0004.bin"
private noncomputable def vp0001100_5 : Blocks := edgeBlocks% "full/vectors/0001100-V-0005.bin"
private noncomputable def vp0001100_6 : Blocks := edgeBlocks% "full/vectors/0001100-V-0006.bin"
private noncomputable def vp0001100_7 : Blocks := edgeBlocks% "full/vectors/0001100-V-0007.bin"
private noncomputable def vp0001100_8 : Blocks := edgeBlocks% "full/vectors/0001100-V-0008.bin"
private noncomputable def vp0001100_9 : Blocks := edgeBlocks% "full/vectors/0001100-V-0009.bin"
private noncomputable def vp0001100_10 : Blocks := edgeBlocks% "full/vectors/0001100-V-0010.bin"
private noncomputable def vp0001100_11 : Blocks := edgeBlocks% "full/vectors/0001100-V-0011.bin"
private noncomputable def vp0001100_12 : Blocks := edgeBlocks% "full/vectors/0001100-V-0012.bin"
private noncomputable def vp0001100_13 : Blocks := edgeBlocks% "full/vectors/0001100-V-0013.bin"
private noncomputable def vp0001100_14 : Blocks := edgeBlocks% "full/vectors/0001100-V-0014.bin"
private noncomputable def vp0001100_15 : Blocks := edgeBlocks% "full/vectors/0001100-V-0015.bin"
private noncomputable def vp0001100_16 : Blocks := edgeBlocks% "full/vectors/0001100-V-0016.bin"
private noncomputable def vp0001100_17 : Blocks := edgeBlocks% "full/vectors/0001100-V-0017.bin"
noncomputable def vp0001100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0001100_0 vp0001100_1) (Blocks.join vp0001100_2 vp0001100_3)) (Blocks.join (Blocks.join vp0001100_4 vp0001100_5) (Blocks.join vp0001100_6 (Blocks.join vp0001100_7 vp0001100_8)))) (Blocks.join (Blocks.join (Blocks.join vp0001100_9 vp0001100_10) (Blocks.join vp0001100_11 vp0001100_12)) (Blocks.join (Blocks.join vp0001100_13 vp0001100_14) (Blocks.join vp0001100_15 (Blocks.join vp0001100_16 vp0001100_17)))))
private theorem bp00011000 : Branch 0 (-767761639/64000000 : ℚ) vp0001100 := by
  apply branch_left_normalized (c:=vp00011000) (k:=0) (m:=1138) (by decide +kernel)
  rw [show 2*(-767761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-767761639/32000000 : ℚ) by norm_num]
  exact coverp00011000
private noncomputable def ep00011001_0 : Blocks := edgeBlocks% "full/vectors/00011001-E-0000.bin"
private noncomputable def ep00011001_1 : Blocks := edgeBlocks% "full/vectors/00011001-E-0001.bin"
private noncomputable def ep00011001_2 : Blocks := edgeBlocks% "full/vectors/00011001-E-0002.bin"
private noncomputable def ep00011001_3 : Blocks := edgeBlocks% "full/vectors/00011001-E-0003.bin"
private noncomputable def ep00011001_4 : Blocks := edgeBlocks% "full/vectors/00011001-E-0004.bin"
private noncomputable def ep00011001_5 : Blocks := edgeBlocks% "full/vectors/00011001-E-0005.bin"
private noncomputable def ep00011001_6 : Blocks := edgeBlocks% "full/vectors/00011001-E-0006.bin"
private noncomputable def ep00011001_7 : Blocks := edgeBlocks% "full/vectors/00011001-E-0007.bin"
private noncomputable def ep00011001_8 : Blocks := edgeBlocks% "full/vectors/00011001-E-0008.bin"
private noncomputable def ep00011001_9 : Blocks := edgeBlocks% "full/vectors/00011001-E-0009.bin"
private noncomputable def ep00011001_10 : Blocks := edgeBlocks% "full/vectors/00011001-E-0010.bin"
private noncomputable def ep00011001_11 : Blocks := edgeBlocks% "full/vectors/00011001-E-0011.bin"
private noncomputable def ep00011001_12 : Blocks := edgeBlocks% "full/vectors/00011001-E-0012.bin"
private noncomputable def ep00011001_13 : Blocks := edgeBlocks% "full/vectors/00011001-E-0013.bin"
private noncomputable def ep00011001_14 : Blocks := edgeBlocks% "full/vectors/00011001-E-0014.bin"
private noncomputable def ep00011001_15 : Blocks := edgeBlocks% "full/vectors/00011001-E-0015.bin"
private noncomputable def ep00011001_16 : Blocks := edgeBlocks% "full/vectors/00011001-E-0016.bin"
private noncomputable def ep00011001_17 : Blocks := edgeBlocks% "full/vectors/00011001-E-0017.bin"
noncomputable def ep00011001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00011001_0 ep00011001_1) (Blocks.join ep00011001_2 ep00011001_3)) (Blocks.join (Blocks.join ep00011001_4 ep00011001_5) (Blocks.join ep00011001_6 (Blocks.join ep00011001_7 ep00011001_8)))) (Blocks.join (Blocks.join (Blocks.join ep00011001_9 ep00011001_10) (Blocks.join ep00011001_11 ep00011001_12)) (Blocks.join (Blocks.join ep00011001_13 ep00011001_14) (Blocks.join ep00011001_15 (Blocks.join ep00011001_16 ep00011001_17)))))
private theorem idp00011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100.list =
    C ((2:ℤ)^2399) * horner X vp00011001.list + horner X ep00011001.list := by
  exact edge_identity (B := (2:ℤ)^3508) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001 : Branch 1 (-767761639/64000000 : ℚ) vp0001100 := by
  apply branch_checked idp00011001 (by positivity) (by decide +kernel)
  rw [show 2*(-767761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-799761639/32000000 : ℚ) by norm_num]
  exact coverp00011001
theorem coverp0001100 : Covers (-767761639/64000000 : ℚ) vp0001100 := join_branches bp00011000 bp00011001
end NextProof.EdgeFull

