import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00039

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000001000111111_0 : Blocks := edgeBlocks% "full/vectors/000001000111111-V-0000.bin"
noncomputable def vp000001000111111 : Blocks := vp000001000111111_0
theorem coverp000001000111111 : Covers (-143511639/250000 : ℚ) vp000001000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000111110_0 : Blocks := edgeBlocks% "full/vectors/000001000111110-V-0000.bin"
noncomputable def vp000001000111110 : Blocks := vp000001000111110_0
theorem coverp000001000111110 : Covers (-143261639/250000 : ℚ) vp000001000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100011111_0 : Blocks := edgeBlocks% "full/vectors/00000100011111-V-0000.bin"
noncomputable def vp00000100011111 : Blocks := vp00000100011111_0
private theorem bp000001000111110 : Branch 0 (-143261639/500000 : ℚ) vp00000100011111 := by
  apply branch_left_normalized (c:=vp000001000111110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-143261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-143261639/250000 : ℚ) by norm_num]
  exact coverp000001000111110
private noncomputable def ep000001000111111_0 : Blocks := edgeBlocks% "full/vectors/000001000111111-E-0000.bin"
noncomputable def ep000001000111111 : Blocks := ep000001000111111_0
private theorem idp000001000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100011111.list =
    C ((2:ℤ)^63) * horner X vp000001000111111.list + horner X ep000001000111111.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000111111 : Branch 1 (-143261639/500000 : ℚ) vp00000100011111 := by
  apply branch_checked idp000001000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-143261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-143511639/250000 : ℚ) by norm_num]
  exact coverp000001000111111
theorem coverp00000100011111 : Covers (-143261639/500000 : ℚ) vp00000100011111 := join_branches bp000001000111110 bp000001000111111
private noncomputable def vp000001000111101_0 : Blocks := edgeBlocks% "full/vectors/000001000111101-V-0000.bin"
noncomputable def vp000001000111101 : Blocks := vp000001000111101_0
theorem coverp000001000111101 : Covers (-143011639/250000 : ℚ) vp000001000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000111100_0 : Blocks := edgeBlocks% "full/vectors/000001000111100-V-0000.bin"
noncomputable def vp000001000111100 : Blocks := vp000001000111100_0
theorem coverp000001000111100 : Covers (-142761639/250000 : ℚ) vp000001000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100011110_0 : Blocks := edgeBlocks% "full/vectors/00000100011110-V-0000.bin"
noncomputable def vp00000100011110 : Blocks := vp00000100011110_0
private theorem bp000001000111100 : Branch 0 (-142761639/500000 : ℚ) vp00000100011110 := by
  apply branch_left_normalized (c:=vp000001000111100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-142761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-142761639/250000 : ℚ) by norm_num]
  exact coverp000001000111100
private noncomputable def ep000001000111101_0 : Blocks := edgeBlocks% "full/vectors/000001000111101-E-0000.bin"
noncomputable def ep000001000111101 : Blocks := ep000001000111101_0
private theorem idp000001000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100011110.list =
    C ((2:ℤ)^64) * horner X vp000001000111101.list + horner X ep000001000111101.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000111101 : Branch 1 (-142761639/500000 : ℚ) vp00000100011110 := by
  apply branch_checked idp000001000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-142761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-143011639/250000 : ℚ) by norm_num]
  exact coverp000001000111101
theorem coverp00000100011110 : Covers (-142761639/500000 : ℚ) vp00000100011110 := join_branches bp000001000111100 bp000001000111101
private noncomputable def vp0000010001111_0 : Blocks := edgeBlocks% "full/vectors/0000010001111-V-0000.bin"
noncomputable def vp0000010001111 : Blocks := vp0000010001111_0
private theorem bp00000100011110 : Branch 0 (-142761639/1000000 : ℚ) vp0000010001111 := by
  apply branch_left_normalized (c:=vp00000100011110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-142761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-142761639/500000 : ℚ) by norm_num]
  exact coverp00000100011110
private noncomputable def ep00000100011111_0 : Blocks := edgeBlocks% "full/vectors/00000100011111-E-0000.bin"
noncomputable def ep00000100011111 : Blocks := ep00000100011111_0
private theorem idp00000100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010001111.list =
    C ((2:ℤ)^107) * horner X vp00000100011111.list + horner X ep00000100011111.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100011111 : Branch 1 (-142761639/1000000 : ℚ) vp0000010001111 := by
  apply branch_checked idp00000100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-142761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-143261639/500000 : ℚ) by norm_num]
  exact coverp00000100011111
theorem coverp0000010001111 : Covers (-142761639/1000000 : ℚ) vp0000010001111 := join_branches bp00000100011110 bp00000100011111
private noncomputable def vp000001000111011_0 : Blocks := edgeBlocks% "full/vectors/000001000111011-V-0000.bin"
noncomputable def vp000001000111011 : Blocks := vp000001000111011_0
theorem coverp000001000111011 : Covers (-142511639/250000 : ℚ) vp000001000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000111010_0 : Blocks := edgeBlocks% "full/vectors/000001000111010-V-0000.bin"
noncomputable def vp000001000111010 : Blocks := vp000001000111010_0
theorem coverp000001000111010 : Covers (-142261639/250000 : ℚ) vp000001000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100011101_0 : Blocks := edgeBlocks% "full/vectors/00000100011101-V-0000.bin"
noncomputable def vp00000100011101 : Blocks := vp00000100011101_0
private theorem bp000001000111010 : Branch 0 (-142261639/500000 : ℚ) vp00000100011101 := by
  apply branch_left_normalized (c:=vp000001000111010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-142261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-142261639/250000 : ℚ) by norm_num]
  exact coverp000001000111010
private noncomputable def ep000001000111011_0 : Blocks := edgeBlocks% "full/vectors/000001000111011-E-0000.bin"
noncomputable def ep000001000111011 : Blocks := ep000001000111011_0
private theorem idp000001000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100011101.list =
    C ((2:ℤ)^63) * horner X vp000001000111011.list + horner X ep000001000111011.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000111011 : Branch 1 (-142261639/500000 : ℚ) vp00000100011101 := by
  apply branch_checked idp000001000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-142261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-142511639/250000 : ℚ) by norm_num]
  exact coverp000001000111011
theorem coverp00000100011101 : Covers (-142261639/500000 : ℚ) vp00000100011101 := join_branches bp000001000111010 bp000001000111011
private noncomputable def vp000001000111001_0 : Blocks := edgeBlocks% "full/vectors/000001000111001-V-0000.bin"
noncomputable def vp000001000111001 : Blocks := vp000001000111001_0
theorem coverp000001000111001 : Covers (-142011639/250000 : ℚ) vp000001000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000111000_0 : Blocks := edgeBlocks% "full/vectors/000001000111000-V-0000.bin"
noncomputable def vp000001000111000 : Blocks := vp000001000111000_0
theorem coverp000001000111000 : Covers (-141761639/250000 : ℚ) vp000001000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100011100_0 : Blocks := edgeBlocks% "full/vectors/00000100011100-V-0000.bin"
noncomputable def vp00000100011100 : Blocks := vp00000100011100_0
private theorem bp000001000111000 : Branch 0 (-141761639/500000 : ℚ) vp00000100011100 := by
  apply branch_left_normalized (c:=vp000001000111000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-141761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-141761639/250000 : ℚ) by norm_num]
  exact coverp000001000111000
private noncomputable def ep000001000111001_0 : Blocks := edgeBlocks% "full/vectors/000001000111001-E-0000.bin"
noncomputable def ep000001000111001 : Blocks := ep000001000111001_0
private theorem idp000001000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100011100.list =
    C ((2:ℤ)^64) * horner X vp000001000111001.list + horner X ep000001000111001.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000111001 : Branch 1 (-141761639/500000 : ℚ) vp00000100011100 := by
  apply branch_checked idp000001000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-141761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-142011639/250000 : ℚ) by norm_num]
  exact coverp000001000111001
theorem coverp00000100011100 : Covers (-141761639/500000 : ℚ) vp00000100011100 := join_branches bp000001000111000 bp000001000111001
private noncomputable def vp0000010001110_0 : Blocks := edgeBlocks% "full/vectors/0000010001110-V-0000.bin"
noncomputable def vp0000010001110 : Blocks := vp0000010001110_0
private theorem bp00000100011100 : Branch 0 (-141761639/1000000 : ℚ) vp0000010001110 := by
  apply branch_left_normalized (c:=vp00000100011100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-141761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-141761639/500000 : ℚ) by norm_num]
  exact coverp00000100011100
private noncomputable def ep00000100011101_0 : Blocks := edgeBlocks% "full/vectors/00000100011101-E-0000.bin"
noncomputable def ep00000100011101 : Blocks := ep00000100011101_0
private theorem idp00000100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010001110.list =
    C ((2:ℤ)^108) * horner X vp00000100011101.list + horner X ep00000100011101.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100011101 : Branch 1 (-141761639/1000000 : ℚ) vp0000010001110 := by
  apply branch_checked idp00000100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-141761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-142261639/500000 : ℚ) by norm_num]
  exact coverp00000100011101
theorem coverp0000010001110 : Covers (-141761639/1000000 : ℚ) vp0000010001110 := join_branches bp00000100011100 bp00000100011101
private noncomputable def vp000001000111_0 : Blocks := edgeBlocks% "full/vectors/000001000111-V-0000.bin"
private noncomputable def vp000001000111_1 : Blocks := edgeBlocks% "full/vectors/000001000111-V-0001.bin"
noncomputable def vp000001000111 : Blocks := (Blocks.join vp000001000111_0 vp000001000111_1)
private theorem bp0000010001110 : Branch 0 (-141761639/2000000 : ℚ) vp000001000111 := by
  apply branch_left_normalized (c:=vp0000010001110) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-141761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-141761639/1000000 : ℚ) by norm_num]
  exact coverp0000010001110
private noncomputable def ep0000010001111_0 : Blocks := edgeBlocks% "full/vectors/0000010001111-E-0000.bin"
private noncomputable def ep0000010001111_1 : Blocks := edgeBlocks% "full/vectors/0000010001111-E-0001.bin"
noncomputable def ep0000010001111 : Blocks := (Blocks.join ep0000010001111_0 ep0000010001111_1)
private theorem idp0000010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001000111.list =
    C ((2:ℤ)^192) * horner X vp0000010001111.list + horner X ep0000010001111.list := by
  exact edge_identity (B := (2:ℤ)^376) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010001111 : Branch 1 (-141761639/2000000 : ℚ) vp000001000111 := by
  apply branch_checked idp0000010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-141761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-142761639/1000000 : ℚ) by norm_num]
  exact coverp0000010001111
theorem coverp000001000111 : Covers (-141761639/2000000 : ℚ) vp000001000111 := join_branches bp0000010001110 bp0000010001111
private noncomputable def vp000001000110111_0 : Blocks := edgeBlocks% "full/vectors/000001000110111-V-0000.bin"
noncomputable def vp000001000110111 : Blocks := vp000001000110111_0
theorem coverp000001000110111 : Covers (-141511639/250000 : ℚ) vp000001000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000110110_0 : Blocks := edgeBlocks% "full/vectors/000001000110110-V-0000.bin"
noncomputable def vp000001000110110 : Blocks := vp000001000110110_0
theorem coverp000001000110110 : Covers (-141261639/250000 : ℚ) vp000001000110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100011011_0 : Blocks := edgeBlocks% "full/vectors/00000100011011-V-0000.bin"
noncomputable def vp00000100011011 : Blocks := vp00000100011011_0
private theorem bp000001000110110 : Branch 0 (-141261639/500000 : ℚ) vp00000100011011 := by
  apply branch_left_normalized (c:=vp000001000110110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-141261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-141261639/250000 : ℚ) by norm_num]
  exact coverp000001000110110
private noncomputable def ep000001000110111_0 : Blocks := edgeBlocks% "full/vectors/000001000110111-E-0000.bin"
noncomputable def ep000001000110111 : Blocks := ep000001000110111_0
private theorem idp000001000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100011011.list =
    C ((2:ℤ)^63) * horner X vp000001000110111.list + horner X ep000001000110111.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000110111 : Branch 1 (-141261639/500000 : ℚ) vp00000100011011 := by
  apply branch_checked idp000001000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-141261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-141511639/250000 : ℚ) by norm_num]
  exact coverp000001000110111
theorem coverp00000100011011 : Covers (-141261639/500000 : ℚ) vp00000100011011 := join_branches bp000001000110110 bp000001000110111
private noncomputable def vp000001000110101_0 : Blocks := edgeBlocks% "full/vectors/000001000110101-V-0000.bin"
noncomputable def vp000001000110101 : Blocks := vp000001000110101_0
theorem coverp000001000110101 : Covers (-141011639/250000 : ℚ) vp000001000110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000110100_0 : Blocks := edgeBlocks% "full/vectors/000001000110100-V-0000.bin"
noncomputable def vp000001000110100 : Blocks := vp000001000110100_0
theorem coverp000001000110100 : Covers (-140761639/250000 : ℚ) vp000001000110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100011010_0 : Blocks := edgeBlocks% "full/vectors/00000100011010-V-0000.bin"
noncomputable def vp00000100011010 : Blocks := vp00000100011010_0
private theorem bp000001000110100 : Branch 0 (-140761639/500000 : ℚ) vp00000100011010 := by
  apply branch_left_normalized (c:=vp000001000110100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-140761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-140761639/250000 : ℚ) by norm_num]
  exact coverp000001000110100
private noncomputable def ep000001000110101_0 : Blocks := edgeBlocks% "full/vectors/000001000110101-E-0000.bin"
noncomputable def ep000001000110101 : Blocks := ep000001000110101_0
private theorem idp000001000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100011010.list =
    C ((2:ℤ)^65) * horner X vp000001000110101.list + horner X ep000001000110101.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000110101 : Branch 1 (-140761639/500000 : ℚ) vp00000100011010 := by
  apply branch_checked idp000001000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-140761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-141011639/250000 : ℚ) by norm_num]
  exact coverp000001000110101
theorem coverp00000100011010 : Covers (-140761639/500000 : ℚ) vp00000100011010 := join_branches bp000001000110100 bp000001000110101
private noncomputable def vp0000010001101_0 : Blocks := edgeBlocks% "full/vectors/0000010001101-V-0000.bin"
noncomputable def vp0000010001101 : Blocks := vp0000010001101_0
private theorem bp00000100011010 : Branch 0 (-140761639/1000000 : ℚ) vp0000010001101 := by
  apply branch_left_normalized (c:=vp00000100011010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-140761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-140761639/500000 : ℚ) by norm_num]
  exact coverp00000100011010
private noncomputable def ep00000100011011_0 : Blocks := edgeBlocks% "full/vectors/00000100011011-E-0000.bin"
noncomputable def ep00000100011011 : Blocks := ep00000100011011_0
private theorem idp00000100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010001101.list =
    C ((2:ℤ)^110) * horner X vp00000100011011.list + horner X ep00000100011011.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100011011 : Branch 1 (-140761639/1000000 : ℚ) vp0000010001101 := by
  apply branch_checked idp00000100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-140761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-141261639/500000 : ℚ) by norm_num]
  exact coverp00000100011011
theorem coverp0000010001101 : Covers (-140761639/1000000 : ℚ) vp0000010001101 := join_branches bp00000100011010 bp00000100011011
private noncomputable def vp000001000110011_0 : Blocks := edgeBlocks% "full/vectors/000001000110011-V-0000.bin"
noncomputable def vp000001000110011 : Blocks := vp000001000110011_0
theorem coverp000001000110011 : Covers (-140511639/250000 : ℚ) vp000001000110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000110010_0 : Blocks := edgeBlocks% "full/vectors/000001000110010-V-0000.bin"
noncomputable def vp000001000110010 : Blocks := vp000001000110010_0
theorem coverp000001000110010 : Covers (-140261639/250000 : ℚ) vp000001000110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100011001_0 : Blocks := edgeBlocks% "full/vectors/00000100011001-V-0000.bin"
noncomputable def vp00000100011001 : Blocks := vp00000100011001_0
private theorem bp000001000110010 : Branch 0 (-140261639/500000 : ℚ) vp00000100011001 := by
  apply branch_left_normalized (c:=vp000001000110010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-140261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-140261639/250000 : ℚ) by norm_num]
  exact coverp000001000110010
private noncomputable def ep000001000110011_0 : Blocks := edgeBlocks% "full/vectors/000001000110011-E-0000.bin"
noncomputable def ep000001000110011 : Blocks := ep000001000110011_0
private theorem idp000001000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100011001.list =
    C ((2:ℤ)^64) * horner X vp000001000110011.list + horner X ep000001000110011.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000110011 : Branch 1 (-140261639/500000 : ℚ) vp00000100011001 := by
  apply branch_checked idp000001000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-140261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-140511639/250000 : ℚ) by norm_num]
  exact coverp000001000110011
theorem coverp00000100011001 : Covers (-140261639/500000 : ℚ) vp00000100011001 := join_branches bp000001000110010 bp000001000110011
private noncomputable def vp000001000110001_0 : Blocks := edgeBlocks% "full/vectors/000001000110001-V-0000.bin"
noncomputable def vp000001000110001 : Blocks := vp000001000110001_0
theorem coverp000001000110001 : Covers (-140011639/250000 : ℚ) vp000001000110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000110000_0 : Blocks := edgeBlocks% "full/vectors/000001000110000-V-0000.bin"
noncomputable def vp000001000110000 : Blocks := vp000001000110000_0
theorem coverp000001000110000 : Covers (-139761639/250000 : ℚ) vp000001000110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100011000_0 : Blocks := edgeBlocks% "full/vectors/00000100011000-V-0000.bin"
noncomputable def vp00000100011000 : Blocks := vp00000100011000_0
private theorem bp000001000110000 : Branch 0 (-139761639/500000 : ℚ) vp00000100011000 := by
  apply branch_left_normalized (c:=vp000001000110000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-139761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-139761639/250000 : ℚ) by norm_num]
  exact coverp000001000110000
private noncomputable def ep000001000110001_0 : Blocks := edgeBlocks% "full/vectors/000001000110001-E-0000.bin"
noncomputable def ep000001000110001 : Blocks := ep000001000110001_0
private theorem idp000001000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100011000.list =
    C ((2:ℤ)^63) * horner X vp000001000110001.list + horner X ep000001000110001.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000110001 : Branch 1 (-139761639/500000 : ℚ) vp00000100011000 := by
  apply branch_checked idp000001000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-139761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-140011639/250000 : ℚ) by norm_num]
  exact coverp000001000110001
theorem coverp00000100011000 : Covers (-139761639/500000 : ℚ) vp00000100011000 := join_branches bp000001000110000 bp000001000110001
private noncomputable def vp0000010001100_0 : Blocks := edgeBlocks% "full/vectors/0000010001100-V-0000.bin"
noncomputable def vp0000010001100 : Blocks := vp0000010001100_0
private theorem bp00000100011000 : Branch 0 (-139761639/1000000 : ℚ) vp0000010001100 := by
  apply branch_left_normalized (c:=vp00000100011000) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-139761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-139761639/500000 : ℚ) by norm_num]
  exact coverp00000100011000
private noncomputable def ep00000100011001_0 : Blocks := edgeBlocks% "full/vectors/00000100011001-E-0000.bin"
noncomputable def ep00000100011001 : Blocks := ep00000100011001_0
private theorem idp00000100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010001100.list =
    C ((2:ℤ)^107) * horner X vp00000100011001.list + horner X ep00000100011001.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100011001 : Branch 1 (-139761639/1000000 : ℚ) vp0000010001100 := by
  apply branch_checked idp00000100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-139761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-140261639/500000 : ℚ) by norm_num]
  exact coverp00000100011001
theorem coverp0000010001100 : Covers (-139761639/1000000 : ℚ) vp0000010001100 := join_branches bp00000100011000 bp00000100011001
private noncomputable def vp000001000110_0 : Blocks := edgeBlocks% "full/vectors/000001000110-V-0000.bin"
private noncomputable def vp000001000110_1 : Blocks := edgeBlocks% "full/vectors/000001000110-V-0001.bin"
noncomputable def vp000001000110 : Blocks := (Blocks.join vp000001000110_0 vp000001000110_1)
private theorem bp0000010001100 : Branch 0 (-139761639/2000000 : ℚ) vp000001000110 := by
  apply branch_left_normalized (c:=vp0000010001100) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-139761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-139761639/1000000 : ℚ) by norm_num]
  exact coverp0000010001100
private noncomputable def ep0000010001101_0 : Blocks := edgeBlocks% "full/vectors/0000010001101-E-0000.bin"
private noncomputable def ep0000010001101_1 : Blocks := edgeBlocks% "full/vectors/0000010001101-E-0001.bin"
noncomputable def ep0000010001101 : Blocks := (Blocks.join ep0000010001101_0 ep0000010001101_1)
private theorem idp0000010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001000110.list =
    C ((2:ℤ)^194) * horner X vp0000010001101.list + horner X ep0000010001101.list := by
  exact edge_identity (B := (2:ℤ)^379) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010001101 : Branch 1 (-139761639/2000000 : ℚ) vp000001000110 := by
  apply branch_checked idp0000010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-139761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-140761639/1000000 : ℚ) by norm_num]
  exact coverp0000010001101
theorem coverp000001000110 : Covers (-139761639/2000000 : ℚ) vp000001000110 := join_branches bp0000010001100 bp0000010001101
private noncomputable def vp00000100011_0 : Blocks := edgeBlocks% "full/vectors/00000100011-V-0000.bin"
private noncomputable def vp00000100011_1 : Blocks := edgeBlocks% "full/vectors/00000100011-V-0001.bin"
private noncomputable def vp00000100011_2 : Blocks := edgeBlocks% "full/vectors/00000100011-V-0002.bin"
noncomputable def vp00000100011 : Blocks := (Blocks.join vp00000100011_0 (Blocks.join vp00000100011_1 vp00000100011_2))
private theorem bp000001000110 : Branch 0 (-139761639/4000000 : ℚ) vp00000100011 := by
  apply branch_left_normalized (c:=vp000001000110) (k:=0) (m:=188) (by decide +kernel)
  rw [show 2*(-139761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-139761639/2000000 : ℚ) by norm_num]
  exact coverp000001000110
private noncomputable def ep000001000111_0 : Blocks := edgeBlocks% "full/vectors/000001000111-E-0000.bin"
private noncomputable def ep000001000111_1 : Blocks := edgeBlocks% "full/vectors/000001000111-E-0001.bin"
private noncomputable def ep000001000111_2 : Blocks := edgeBlocks% "full/vectors/000001000111-E-0002.bin"
noncomputable def ep000001000111 : Blocks := (Blocks.join ep000001000111_0 (Blocks.join ep000001000111_1 ep000001000111_2))
private theorem idp000001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100011.list =
    C ((2:ℤ)^366) * horner X vp000001000111.list + horner X ep000001000111.list := by
  exact edge_identity (B := (2:ℤ)^632) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000111 : Branch 1 (-139761639/4000000 : ℚ) vp00000100011 := by
  apply branch_checked idp000001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-139761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-141761639/2000000 : ℚ) by norm_num]
  exact coverp000001000111
theorem coverp00000100011 : Covers (-139761639/4000000 : ℚ) vp00000100011 := join_branches bp000001000110 bp000001000111
private noncomputable def vp000001000101111_0 : Blocks := edgeBlocks% "full/vectors/000001000101111-V-0000.bin"
noncomputable def vp000001000101111 : Blocks := vp000001000101111_0
theorem coverp000001000101111 : Covers (-139511639/250000 : ℚ) vp000001000101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000101110_0 : Blocks := edgeBlocks% "full/vectors/000001000101110-V-0000.bin"
noncomputable def vp000001000101110 : Blocks := vp000001000101110_0
theorem coverp000001000101110 : Covers (-139261639/250000 : ℚ) vp000001000101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100010111_0 : Blocks := edgeBlocks% "full/vectors/00000100010111-V-0000.bin"
noncomputable def vp00000100010111 : Blocks := vp00000100010111_0
private theorem bp000001000101110 : Branch 0 (-139261639/500000 : ℚ) vp00000100010111 := by
  apply branch_left_normalized (c:=vp000001000101110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-139261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-139261639/250000 : ℚ) by norm_num]
  exact coverp000001000101110
private noncomputable def ep000001000101111_0 : Blocks := edgeBlocks% "full/vectors/000001000101111-E-0000.bin"
noncomputable def ep000001000101111 : Blocks := ep000001000101111_0
private theorem idp000001000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100010111.list =
    C ((2:ℤ)^63) * horner X vp000001000101111.list + horner X ep000001000101111.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000101111 : Branch 1 (-139261639/500000 : ℚ) vp00000100010111 := by
  apply branch_checked idp000001000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-139261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-139511639/250000 : ℚ) by norm_num]
  exact coverp000001000101111
theorem coverp00000100010111 : Covers (-139261639/500000 : ℚ) vp00000100010111 := join_branches bp000001000101110 bp000001000101111
private noncomputable def vp000001000101101_0 : Blocks := edgeBlocks% "full/vectors/000001000101101-V-0000.bin"
noncomputable def vp000001000101101 : Blocks := vp000001000101101_0
theorem coverp000001000101101 : Covers (-139011639/250000 : ℚ) vp000001000101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000101100_0 : Blocks := edgeBlocks% "full/vectors/000001000101100-V-0000.bin"
noncomputable def vp000001000101100 : Blocks := vp000001000101100_0
theorem coverp000001000101100 : Covers (-138761639/250000 : ℚ) vp000001000101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100010110_0 : Blocks := edgeBlocks% "full/vectors/00000100010110-V-0000.bin"
noncomputable def vp00000100010110 : Blocks := vp00000100010110_0
private theorem bp000001000101100 : Branch 0 (-138761639/500000 : ℚ) vp00000100010110 := by
  apply branch_left_normalized (c:=vp000001000101100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-138761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-138761639/250000 : ℚ) by norm_num]
  exact coverp000001000101100
private noncomputable def ep000001000101101_0 : Blocks := edgeBlocks% "full/vectors/000001000101101-E-0000.bin"
noncomputable def ep000001000101101 : Blocks := ep000001000101101_0
private theorem idp000001000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100010110.list =
    C ((2:ℤ)^63) * horner X vp000001000101101.list + horner X ep000001000101101.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000101101 : Branch 1 (-138761639/500000 : ℚ) vp00000100010110 := by
  apply branch_checked idp000001000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-138761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-139011639/250000 : ℚ) by norm_num]
  exact coverp000001000101101
theorem coverp00000100010110 : Covers (-138761639/500000 : ℚ) vp00000100010110 := join_branches bp000001000101100 bp000001000101101
private noncomputable def vp0000010001011_0 : Blocks := edgeBlocks% "full/vectors/0000010001011-V-0000.bin"
noncomputable def vp0000010001011 : Blocks := vp0000010001011_0
private theorem bp00000100010110 : Branch 0 (-138761639/1000000 : ℚ) vp0000010001011 := by
  apply branch_left_normalized (c:=vp00000100010110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-138761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-138761639/500000 : ℚ) by norm_num]
  exact coverp00000100010110
private noncomputable def ep00000100010111_0 : Blocks := edgeBlocks% "full/vectors/00000100010111-E-0000.bin"
noncomputable def ep00000100010111 : Blocks := ep00000100010111_0
private theorem idp00000100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010001011.list =
    C ((2:ℤ)^107) * horner X vp00000100010111.list + horner X ep00000100010111.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100010111 : Branch 1 (-138761639/1000000 : ℚ) vp0000010001011 := by
  apply branch_checked idp00000100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-138761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-139261639/500000 : ℚ) by norm_num]
  exact coverp00000100010111
theorem coverp0000010001011 : Covers (-138761639/1000000 : ℚ) vp0000010001011 := join_branches bp00000100010110 bp00000100010111
private noncomputable def vp000001000101011_0 : Blocks := edgeBlocks% "full/vectors/000001000101011-V-0000.bin"
noncomputable def vp000001000101011 : Blocks := vp000001000101011_0
theorem coverp000001000101011 : Covers (-138511639/250000 : ℚ) vp000001000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000101010_0 : Blocks := edgeBlocks% "full/vectors/000001000101010-V-0000.bin"
noncomputable def vp000001000101010 : Blocks := vp000001000101010_0
theorem coverp000001000101010 : Covers (-138261639/250000 : ℚ) vp000001000101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100010101_0 : Blocks := edgeBlocks% "full/vectors/00000100010101-V-0000.bin"
noncomputable def vp00000100010101 : Blocks := vp00000100010101_0
private theorem bp000001000101010 : Branch 0 (-138261639/500000 : ℚ) vp00000100010101 := by
  apply branch_left_normalized (c:=vp000001000101010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-138261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-138261639/250000 : ℚ) by norm_num]
  exact coverp000001000101010
private noncomputable def ep000001000101011_0 : Blocks := edgeBlocks% "full/vectors/000001000101011-E-0000.bin"
noncomputable def ep000001000101011 : Blocks := ep000001000101011_0
private theorem idp000001000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100010101.list =
    C ((2:ℤ)^63) * horner X vp000001000101011.list + horner X ep000001000101011.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000101011 : Branch 1 (-138261639/500000 : ℚ) vp00000100010101 := by
  apply branch_checked idp000001000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-138261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-138511639/250000 : ℚ) by norm_num]
  exact coverp000001000101011
theorem coverp00000100010101 : Covers (-138261639/500000 : ℚ) vp00000100010101 := join_branches bp000001000101010 bp000001000101011
private noncomputable def vp000001000101001_0 : Blocks := edgeBlocks% "full/vectors/000001000101001-V-0000.bin"
noncomputable def vp000001000101001 : Blocks := vp000001000101001_0
theorem coverp000001000101001 : Covers (-138011639/250000 : ℚ) vp000001000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000101000_0 : Blocks := edgeBlocks% "full/vectors/000001000101000-V-0000.bin"
noncomputable def vp000001000101000 : Blocks := vp000001000101000_0
theorem coverp000001000101000 : Covers (-137761639/250000 : ℚ) vp000001000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100010100_0 : Blocks := edgeBlocks% "full/vectors/00000100010100-V-0000.bin"
noncomputable def vp00000100010100 : Blocks := vp00000100010100_0
private theorem bp000001000101000 : Branch 0 (-137761639/500000 : ℚ) vp00000100010100 := by
  apply branch_left_normalized (c:=vp000001000101000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-137761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-137761639/250000 : ℚ) by norm_num]
  exact coverp000001000101000
private noncomputable def ep000001000101001_0 : Blocks := edgeBlocks% "full/vectors/000001000101001-E-0000.bin"
noncomputable def ep000001000101001 : Blocks := ep000001000101001_0
private theorem idp000001000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100010100.list =
    C ((2:ℤ)^65) * horner X vp000001000101001.list + horner X ep000001000101001.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000101001 : Branch 1 (-137761639/500000 : ℚ) vp00000100010100 := by
  apply branch_checked idp000001000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-137761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-138011639/250000 : ℚ) by norm_num]
  exact coverp000001000101001
theorem coverp00000100010100 : Covers (-137761639/500000 : ℚ) vp00000100010100 := join_branches bp000001000101000 bp000001000101001
private noncomputable def vp0000010001010_0 : Blocks := edgeBlocks% "full/vectors/0000010001010-V-0000.bin"
noncomputable def vp0000010001010 : Blocks := vp0000010001010_0
private theorem bp00000100010100 : Branch 0 (-137761639/1000000 : ℚ) vp0000010001010 := by
  apply branch_left_normalized (c:=vp00000100010100) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-137761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-137761639/500000 : ℚ) by norm_num]
  exact coverp00000100010100
private noncomputable def ep00000100010101_0 : Blocks := edgeBlocks% "full/vectors/00000100010101-E-0000.bin"
noncomputable def ep00000100010101 : Blocks := ep00000100010101_0
private theorem idp00000100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010001010.list =
    C ((2:ℤ)^110) * horner X vp00000100010101.list + horner X ep00000100010101.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100010101 : Branch 1 (-137761639/1000000 : ℚ) vp0000010001010 := by
  apply branch_checked idp00000100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-137761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-138261639/500000 : ℚ) by norm_num]
  exact coverp00000100010101
theorem coverp0000010001010 : Covers (-137761639/1000000 : ℚ) vp0000010001010 := join_branches bp00000100010100 bp00000100010101
private noncomputable def vp000001000101_0 : Blocks := edgeBlocks% "full/vectors/000001000101-V-0000.bin"
private noncomputable def vp000001000101_1 : Blocks := edgeBlocks% "full/vectors/000001000101-V-0001.bin"
noncomputable def vp000001000101 : Blocks := (Blocks.join vp000001000101_0 vp000001000101_1)
private theorem bp0000010001010 : Branch 0 (-137761639/2000000 : ℚ) vp000001000101 := by
  apply branch_left_normalized (c:=vp0000010001010) (k:=0) (m:=105) (by decide +kernel)
  rw [show 2*(-137761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-137761639/1000000 : ℚ) by norm_num]
  exact coverp0000010001010
private noncomputable def ep0000010001011_0 : Blocks := edgeBlocks% "full/vectors/0000010001011-E-0000.bin"
private noncomputable def ep0000010001011_1 : Blocks := edgeBlocks% "full/vectors/0000010001011-E-0001.bin"
noncomputable def ep0000010001011 : Blocks := (Blocks.join ep0000010001011_0 ep0000010001011_1)
private theorem idp0000010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001000101.list =
    C ((2:ℤ)^197) * horner X vp0000010001011.list + horner X ep0000010001011.list := by
  exact edge_identity (B := (2:ℤ)^380) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010001011 : Branch 1 (-137761639/2000000 : ℚ) vp000001000101 := by
  apply branch_checked idp0000010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-137761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-138761639/1000000 : ℚ) by norm_num]
  exact coverp0000010001011
theorem coverp000001000101 : Covers (-137761639/2000000 : ℚ) vp000001000101 := join_branches bp0000010001010 bp0000010001011
private noncomputable def vp000001000100111_0 : Blocks := edgeBlocks% "full/vectors/000001000100111-V-0000.bin"
noncomputable def vp000001000100111 : Blocks := vp000001000100111_0
theorem coverp000001000100111 : Covers (-137511639/250000 : ℚ) vp000001000100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000100110_0 : Blocks := edgeBlocks% "full/vectors/000001000100110-V-0000.bin"
noncomputable def vp000001000100110 : Blocks := vp000001000100110_0
theorem coverp000001000100110 : Covers (-137261639/250000 : ℚ) vp000001000100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100010011_0 : Blocks := edgeBlocks% "full/vectors/00000100010011-V-0000.bin"
noncomputable def vp00000100010011 : Blocks := vp00000100010011_0
private theorem bp000001000100110 : Branch 0 (-137261639/500000 : ℚ) vp00000100010011 := by
  apply branch_left_normalized (c:=vp000001000100110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-137261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-137261639/250000 : ℚ) by norm_num]
  exact coverp000001000100110
private noncomputable def ep000001000100111_0 : Blocks := edgeBlocks% "full/vectors/000001000100111-E-0000.bin"
noncomputable def ep000001000100111 : Blocks := ep000001000100111_0
private theorem idp000001000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100010011.list =
    C ((2:ℤ)^65) * horner X vp000001000100111.list + horner X ep000001000100111.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000100111 : Branch 1 (-137261639/500000 : ℚ) vp00000100010011 := by
  apply branch_checked idp000001000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-137261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-137511639/250000 : ℚ) by norm_num]
  exact coverp000001000100111
theorem coverp00000100010011 : Covers (-137261639/500000 : ℚ) vp00000100010011 := join_branches bp000001000100110 bp000001000100111
private noncomputable def vp000001000100101_0 : Blocks := edgeBlocks% "full/vectors/000001000100101-V-0000.bin"
noncomputable def vp000001000100101 : Blocks := vp000001000100101_0
theorem coverp000001000100101 : Covers (-137011639/250000 : ℚ) vp000001000100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000100100_0 : Blocks := edgeBlocks% "full/vectors/000001000100100-V-0000.bin"
noncomputable def vp000001000100100 : Blocks := vp000001000100100_0
theorem coverp000001000100100 : Covers (-136761639/250000 : ℚ) vp000001000100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100010010_0 : Blocks := edgeBlocks% "full/vectors/00000100010010-V-0000.bin"
noncomputable def vp00000100010010 : Blocks := vp00000100010010_0
private theorem bp000001000100100 : Branch 0 (-136761639/500000 : ℚ) vp00000100010010 := by
  apply branch_left_normalized (c:=vp000001000100100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-136761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-136761639/250000 : ℚ) by norm_num]
  exact coverp000001000100100
private noncomputable def ep000001000100101_0 : Blocks := edgeBlocks% "full/vectors/000001000100101-E-0000.bin"
noncomputable def ep000001000100101 : Blocks := ep000001000100101_0
private theorem idp000001000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100010010.list =
    C ((2:ℤ)^64) * horner X vp000001000100101.list + horner X ep000001000100101.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000100101 : Branch 1 (-136761639/500000 : ℚ) vp00000100010010 := by
  apply branch_checked idp000001000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-136761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-137011639/250000 : ℚ) by norm_num]
  exact coverp000001000100101
theorem coverp00000100010010 : Covers (-136761639/500000 : ℚ) vp00000100010010 := join_branches bp000001000100100 bp000001000100101
private noncomputable def vp0000010001001_0 : Blocks := edgeBlocks% "full/vectors/0000010001001-V-0000.bin"
noncomputable def vp0000010001001 : Blocks := vp0000010001001_0
private theorem bp00000100010010 : Branch 0 (-136761639/1000000 : ℚ) vp0000010001001 := by
  apply branch_left_normalized (c:=vp00000100010010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-136761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-136761639/500000 : ℚ) by norm_num]
  exact coverp00000100010010
private noncomputable def ep00000100010011_0 : Blocks := edgeBlocks% "full/vectors/00000100010011-E-0000.bin"
noncomputable def ep00000100010011 : Blocks := ep00000100010011_0
private theorem idp00000100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010001001.list =
    C ((2:ℤ)^109) * horner X vp00000100010011.list + horner X ep00000100010011.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100010011 : Branch 1 (-136761639/1000000 : ℚ) vp0000010001001 := by
  apply branch_checked idp00000100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-136761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-137261639/500000 : ℚ) by norm_num]
  exact coverp00000100010011
theorem coverp0000010001001 : Covers (-136761639/1000000 : ℚ) vp0000010001001 := join_branches bp00000100010010 bp00000100010011
private noncomputable def vp000001000100011_0 : Blocks := edgeBlocks% "full/vectors/000001000100011-V-0000.bin"
noncomputable def vp000001000100011 : Blocks := vp000001000100011_0
theorem coverp000001000100011 : Covers (-136511639/250000 : ℚ) vp000001000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000100010_0 : Blocks := edgeBlocks% "full/vectors/000001000100010-V-0000.bin"
noncomputable def vp000001000100010 : Blocks := vp000001000100010_0
theorem coverp000001000100010 : Covers (-136261639/250000 : ℚ) vp000001000100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100010001_0 : Blocks := edgeBlocks% "full/vectors/00000100010001-V-0000.bin"
noncomputable def vp00000100010001 : Blocks := vp00000100010001_0
private theorem bp000001000100010 : Branch 0 (-136261639/500000 : ℚ) vp00000100010001 := by
  apply branch_left_normalized (c:=vp000001000100010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-136261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-136261639/250000 : ℚ) by norm_num]
  exact coverp000001000100010
private noncomputable def ep000001000100011_0 : Blocks := edgeBlocks% "full/vectors/000001000100011-E-0000.bin"
noncomputable def ep000001000100011 : Blocks := ep000001000100011_0
private theorem idp000001000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100010001.list =
    C ((2:ℤ)^63) * horner X vp000001000100011.list + horner X ep000001000100011.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000100011 : Branch 1 (-136261639/500000 : ℚ) vp00000100010001 := by
  apply branch_checked idp000001000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-136261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-136511639/250000 : ℚ) by norm_num]
  exact coverp000001000100011
theorem coverp00000100010001 : Covers (-136261639/500000 : ℚ) vp00000100010001 := join_branches bp000001000100010 bp000001000100011
private noncomputable def vp000001000100001_0 : Blocks := edgeBlocks% "full/vectors/000001000100001-V-0000.bin"
noncomputable def vp000001000100001 : Blocks := vp000001000100001_0
theorem coverp000001000100001 : Covers (-136011639/250000 : ℚ) vp000001000100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000100000_0 : Blocks := edgeBlocks% "full/vectors/000001000100000-V-0000.bin"
noncomputable def vp000001000100000 : Blocks := vp000001000100000_0
theorem coverp000001000100000 : Covers (-135761639/250000 : ℚ) vp000001000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100010000_0 : Blocks := edgeBlocks% "full/vectors/00000100010000-V-0000.bin"
noncomputable def vp00000100010000 : Blocks := vp00000100010000_0
private theorem bp000001000100000 : Branch 0 (-135761639/500000 : ℚ) vp00000100010000 := by
  apply branch_left_normalized (c:=vp000001000100000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-135761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-135761639/250000 : ℚ) by norm_num]
  exact coverp000001000100000
private noncomputable def ep000001000100001_0 : Blocks := edgeBlocks% "full/vectors/000001000100001-E-0000.bin"
noncomputable def ep000001000100001 : Blocks := ep000001000100001_0
private theorem idp000001000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100010000.list =
    C ((2:ℤ)^63) * horner X vp000001000100001.list + horner X ep000001000100001.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000100001 : Branch 1 (-135761639/500000 : ℚ) vp00000100010000 := by
  apply branch_checked idp000001000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-135761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-136011639/250000 : ℚ) by norm_num]
  exact coverp000001000100001
theorem coverp00000100010000 : Covers (-135761639/500000 : ℚ) vp00000100010000 := join_branches bp000001000100000 bp000001000100001
private noncomputable def vp0000010001000_0 : Blocks := edgeBlocks% "full/vectors/0000010001000-V-0000.bin"
noncomputable def vp0000010001000 : Blocks := vp0000010001000_0
private theorem bp00000100010000 : Branch 0 (-135761639/1000000 : ℚ) vp0000010001000 := by
  apply branch_left_normalized (c:=vp00000100010000) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-135761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-135761639/500000 : ℚ) by norm_num]
  exact coverp00000100010000
private noncomputable def ep00000100010001_0 : Blocks := edgeBlocks% "full/vectors/00000100010001-E-0000.bin"
noncomputable def ep00000100010001 : Blocks := ep00000100010001_0
private theorem idp00000100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010001000.list =
    C ((2:ℤ)^107) * horner X vp00000100010001.list + horner X ep00000100010001.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100010001 : Branch 1 (-135761639/1000000 : ℚ) vp0000010001000 := by
  apply branch_checked idp00000100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-135761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-136261639/500000 : ℚ) by norm_num]
  exact coverp00000100010001
theorem coverp0000010001000 : Covers (-135761639/1000000 : ℚ) vp0000010001000 := join_branches bp00000100010000 bp00000100010001
private noncomputable def vp000001000100_0 : Blocks := edgeBlocks% "full/vectors/000001000100-V-0000.bin"
private noncomputable def vp000001000100_1 : Blocks := edgeBlocks% "full/vectors/000001000100-V-0001.bin"
noncomputable def vp000001000100 : Blocks := (Blocks.join vp000001000100_0 vp000001000100_1)
private theorem bp0000010001000 : Branch 0 (-135761639/2000000 : ℚ) vp000001000100 := by
  apply branch_left_normalized (c:=vp0000010001000) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-135761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-135761639/1000000 : ℚ) by norm_num]
  exact coverp0000010001000
private noncomputable def ep0000010001001_0 : Blocks := edgeBlocks% "full/vectors/0000010001001-E-0000.bin"
private noncomputable def ep0000010001001_1 : Blocks := edgeBlocks% "full/vectors/0000010001001-E-0001.bin"
noncomputable def ep0000010001001 : Blocks := (Blocks.join ep0000010001001_0 ep0000010001001_1)
private theorem idp0000010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001000100.list =
    C ((2:ℤ)^194) * horner X vp0000010001001.list + horner X ep0000010001001.list := by
  exact edge_identity (B := (2:ℤ)^380) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010001001 : Branch 1 (-135761639/2000000 : ℚ) vp000001000100 := by
  apply branch_checked idp0000010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-135761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-136761639/1000000 : ℚ) by norm_num]
  exact coverp0000010001001
theorem coverp000001000100 : Covers (-135761639/2000000 : ℚ) vp000001000100 := join_branches bp0000010001000 bp0000010001001
private noncomputable def vp00000100010_0 : Blocks := edgeBlocks% "full/vectors/00000100010-V-0000.bin"
private noncomputable def vp00000100010_1 : Blocks := edgeBlocks% "full/vectors/00000100010-V-0001.bin"
private noncomputable def vp00000100010_2 : Blocks := edgeBlocks% "full/vectors/00000100010-V-0002.bin"
noncomputable def vp00000100010 : Blocks := (Blocks.join vp00000100010_0 (Blocks.join vp00000100010_1 vp00000100010_2))
private theorem bp000001000100 : Branch 0 (-135761639/4000000 : ℚ) vp00000100010 := by
  apply branch_left_normalized (c:=vp000001000100) (k:=0) (m:=190) (by decide +kernel)
  rw [show 2*(-135761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-135761639/2000000 : ℚ) by norm_num]
  exact coverp000001000100
private noncomputable def ep000001000101_0 : Blocks := edgeBlocks% "full/vectors/000001000101-E-0000.bin"
private noncomputable def ep000001000101_1 : Blocks := edgeBlocks% "full/vectors/000001000101-E-0001.bin"
private noncomputable def ep000001000101_2 : Blocks := edgeBlocks% "full/vectors/000001000101-E-0002.bin"
noncomputable def ep000001000101 : Blocks := (Blocks.join ep000001000101_0 (Blocks.join ep000001000101_1 ep000001000101_2))
private theorem idp000001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100010.list =
    C ((2:ℤ)^368) * horner X vp000001000101.list + horner X ep000001000101.list := by
  exact edge_identity (B := (2:ℤ)^636) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000101 : Branch 1 (-135761639/4000000 : ℚ) vp00000100010 := by
  apply branch_checked idp000001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-135761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-137761639/2000000 : ℚ) by norm_num]
  exact coverp000001000101
theorem coverp00000100010 : Covers (-135761639/4000000 : ℚ) vp00000100010 := join_branches bp000001000100 bp000001000101
private noncomputable def vp0000010001_0 : Blocks := edgeBlocks% "full/vectors/0000010001-V-0000.bin"
private noncomputable def vp0000010001_1 : Blocks := edgeBlocks% "full/vectors/0000010001-V-0001.bin"
private noncomputable def vp0000010001_2 : Blocks := edgeBlocks% "full/vectors/0000010001-V-0002.bin"
private noncomputable def vp0000010001_3 : Blocks := edgeBlocks% "full/vectors/0000010001-V-0003.bin"
private noncomputable def vp0000010001_4 : Blocks := edgeBlocks% "full/vectors/0000010001-V-0004.bin"
private noncomputable def vp0000010001_5 : Blocks := edgeBlocks% "full/vectors/0000010001-V-0005.bin"
noncomputable def vp0000010001 : Blocks := (Blocks.join (Blocks.join vp0000010001_0 (Blocks.join vp0000010001_1 vp0000010001_2)) (Blocks.join vp0000010001_3 (Blocks.join vp0000010001_4 vp0000010001_5)))
private theorem bp00000100010 : Branch 0 (-135761639/8000000 : ℚ) vp0000010001 := by
  apply branch_left_normalized (c:=vp00000100010) (k:=0) (m:=357) (by decide +kernel)
  rw [show 2*(-135761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-135761639/4000000 : ℚ) by norm_num]
  exact coverp00000100010
private noncomputable def ep00000100011_0 : Blocks := edgeBlocks% "full/vectors/00000100011-E-0000.bin"
private noncomputable def ep00000100011_1 : Blocks := edgeBlocks% "full/vectors/00000100011-E-0001.bin"
private noncomputable def ep00000100011_2 : Blocks := edgeBlocks% "full/vectors/00000100011-E-0002.bin"
private noncomputable def ep00000100011_3 : Blocks := edgeBlocks% "full/vectors/00000100011-E-0003.bin"
private noncomputable def ep00000100011_4 : Blocks := edgeBlocks% "full/vectors/00000100011-E-0004.bin"
private noncomputable def ep00000100011_5 : Blocks := edgeBlocks% "full/vectors/00000100011-E-0005.bin"
noncomputable def ep00000100011 : Blocks := (Blocks.join (Blocks.join ep00000100011_0 (Blocks.join ep00000100011_1 ep00000100011_2)) (Blocks.join ep00000100011_3 (Blocks.join ep00000100011_4 ep00000100011_5)))
private theorem idp00000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010001.list =
    C ((2:ℤ)^711) * horner X vp00000100011.list + horner X ep00000100011.list := by
  exact edge_identity (B := (2:ℤ)^1147) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100011 : Branch 1 (-135761639/8000000 : ℚ) vp0000010001 := by
  apply branch_checked idp00000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-135761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-139761639/4000000 : ℚ) by norm_num]
  exact coverp00000100011
theorem coverp0000010001 : Covers (-135761639/8000000 : ℚ) vp0000010001 := join_branches bp00000100010 bp00000100011
private noncomputable def vp000001000011111_0 : Blocks := edgeBlocks% "full/vectors/000001000011111-V-0000.bin"
noncomputable def vp000001000011111 : Blocks := vp000001000011111_0
theorem coverp000001000011111 : Covers (-135511639/250000 : ℚ) vp000001000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000011110_0 : Blocks := edgeBlocks% "full/vectors/000001000011110-V-0000.bin"
noncomputable def vp000001000011110 : Blocks := vp000001000011110_0
theorem coverp000001000011110 : Covers (-135261639/250000 : ℚ) vp000001000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100001111_0 : Blocks := edgeBlocks% "full/vectors/00000100001111-V-0000.bin"
noncomputable def vp00000100001111 : Blocks := vp00000100001111_0
private theorem bp000001000011110 : Branch 0 (-135261639/500000 : ℚ) vp00000100001111 := by
  apply branch_left_normalized (c:=vp000001000011110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-135261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-135261639/250000 : ℚ) by norm_num]
  exact coverp000001000011110
private noncomputable def ep000001000011111_0 : Blocks := edgeBlocks% "full/vectors/000001000011111-E-0000.bin"
noncomputable def ep000001000011111 : Blocks := ep000001000011111_0
private theorem idp000001000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100001111.list =
    C ((2:ℤ)^64) * horner X vp000001000011111.list + horner X ep000001000011111.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000011111 : Branch 1 (-135261639/500000 : ℚ) vp00000100001111 := by
  apply branch_checked idp000001000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-135261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-135511639/250000 : ℚ) by norm_num]
  exact coverp000001000011111
theorem coverp00000100001111 : Covers (-135261639/500000 : ℚ) vp00000100001111 := join_branches bp000001000011110 bp000001000011111
private noncomputable def vp000001000011101_0 : Blocks := edgeBlocks% "full/vectors/000001000011101-V-0000.bin"
noncomputable def vp000001000011101 : Blocks := vp000001000011101_0
theorem coverp000001000011101 : Covers (-135011639/250000 : ℚ) vp000001000011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000011100_0 : Blocks := edgeBlocks% "full/vectors/000001000011100-V-0000.bin"
noncomputable def vp000001000011100 : Blocks := vp000001000011100_0
theorem coverp000001000011100 : Covers (-134761639/250000 : ℚ) vp000001000011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100001110_0 : Blocks := edgeBlocks% "full/vectors/00000100001110-V-0000.bin"
noncomputable def vp00000100001110 : Blocks := vp00000100001110_0
private theorem bp000001000011100 : Branch 0 (-134761639/500000 : ℚ) vp00000100001110 := by
  apply branch_left_normalized (c:=vp000001000011100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-134761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-134761639/250000 : ℚ) by norm_num]
  exact coverp000001000011100
private noncomputable def ep000001000011101_0 : Blocks := edgeBlocks% "full/vectors/000001000011101-E-0000.bin"
noncomputable def ep000001000011101 : Blocks := ep000001000011101_0
private theorem idp000001000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100001110.list =
    C ((2:ℤ)^66) * horner X vp000001000011101.list + horner X ep000001000011101.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000011101 : Branch 1 (-134761639/500000 : ℚ) vp00000100001110 := by
  apply branch_checked idp000001000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-134761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-135011639/250000 : ℚ) by norm_num]
  exact coverp000001000011101
theorem coverp00000100001110 : Covers (-134761639/500000 : ℚ) vp00000100001110 := join_branches bp000001000011100 bp000001000011101
private noncomputable def vp0000010000111_0 : Blocks := edgeBlocks% "full/vectors/0000010000111-V-0000.bin"
noncomputable def vp0000010000111 : Blocks := vp0000010000111_0
private theorem bp00000100001110 : Branch 0 (-134761639/1000000 : ℚ) vp0000010000111 := by
  apply branch_left_normalized (c:=vp00000100001110) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-134761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-134761639/500000 : ℚ) by norm_num]
  exact coverp00000100001110
private noncomputable def ep00000100001111_0 : Blocks := edgeBlocks% "full/vectors/00000100001111-E-0000.bin"
noncomputable def ep00000100001111 : Blocks := ep00000100001111_0
private theorem idp00000100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010000111.list =
    C ((2:ℤ)^112) * horner X vp00000100001111.list + horner X ep00000100001111.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100001111 : Branch 1 (-134761639/1000000 : ℚ) vp0000010000111 := by
  apply branch_checked idp00000100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-134761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-135261639/500000 : ℚ) by norm_num]
  exact coverp00000100001111
theorem coverp0000010000111 : Covers (-134761639/1000000 : ℚ) vp0000010000111 := join_branches bp00000100001110 bp00000100001111
private noncomputable def vp000001000011011_0 : Blocks := edgeBlocks% "full/vectors/000001000011011-V-0000.bin"
noncomputable def vp000001000011011 : Blocks := vp000001000011011_0
theorem coverp000001000011011 : Covers (-134511639/250000 : ℚ) vp000001000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000011010_0 : Blocks := edgeBlocks% "full/vectors/000001000011010-V-0000.bin"
noncomputable def vp000001000011010 : Blocks := vp000001000011010_0
theorem coverp000001000011010 : Covers (-134261639/250000 : ℚ) vp000001000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100001101_0 : Blocks := edgeBlocks% "full/vectors/00000100001101-V-0000.bin"
noncomputable def vp00000100001101 : Blocks := vp00000100001101_0
private theorem bp000001000011010 : Branch 0 (-134261639/500000 : ℚ) vp00000100001101 := by
  apply branch_left_normalized (c:=vp000001000011010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-134261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-134261639/250000 : ℚ) by norm_num]
  exact coverp000001000011010
private noncomputable def ep000001000011011_0 : Blocks := edgeBlocks% "full/vectors/000001000011011-E-0000.bin"
noncomputable def ep000001000011011 : Blocks := ep000001000011011_0
private theorem idp000001000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100001101.list =
    C ((2:ℤ)^63) * horner X vp000001000011011.list + horner X ep000001000011011.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000011011 : Branch 1 (-134261639/500000 : ℚ) vp00000100001101 := by
  apply branch_checked idp000001000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-134261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-134511639/250000 : ℚ) by norm_num]
  exact coverp000001000011011
theorem coverp00000100001101 : Covers (-134261639/500000 : ℚ) vp00000100001101 := join_branches bp000001000011010 bp000001000011011
private noncomputable def vp000001000011001_0 : Blocks := edgeBlocks% "full/vectors/000001000011001-V-0000.bin"
noncomputable def vp000001000011001 : Blocks := vp000001000011001_0
theorem coverp000001000011001 : Covers (-134011639/250000 : ℚ) vp000001000011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000011000_0 : Blocks := edgeBlocks% "full/vectors/000001000011000-V-0000.bin"
noncomputable def vp000001000011000 : Blocks := vp000001000011000_0
theorem coverp000001000011000 : Covers (-133761639/250000 : ℚ) vp000001000011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100001100_0 : Blocks := edgeBlocks% "full/vectors/00000100001100-V-0000.bin"
noncomputable def vp00000100001100 : Blocks := vp00000100001100_0
private theorem bp000001000011000 : Branch 0 (-133761639/500000 : ℚ) vp00000100001100 := by
  apply branch_left_normalized (c:=vp000001000011000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-133761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-133761639/250000 : ℚ) by norm_num]
  exact coverp000001000011000
private noncomputable def ep000001000011001_0 : Blocks := edgeBlocks% "full/vectors/000001000011001-E-0000.bin"
noncomputable def ep000001000011001 : Blocks := ep000001000011001_0
private theorem idp000001000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100001100.list =
    C ((2:ℤ)^61) * horner X vp000001000011001.list + horner X ep000001000011001.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000011001 : Branch 1 (-133761639/500000 : ℚ) vp00000100001100 := by
  apply branch_checked idp000001000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-133761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-134011639/250000 : ℚ) by norm_num]
  exact coverp000001000011001
theorem coverp00000100001100 : Covers (-133761639/500000 : ℚ) vp00000100001100 := join_branches bp000001000011000 bp000001000011001
private noncomputable def vp0000010000110_0 : Blocks := edgeBlocks% "full/vectors/0000010000110-V-0000.bin"
noncomputable def vp0000010000110 : Blocks := vp0000010000110_0
private theorem bp00000100001100 : Branch 0 (-133761639/1000000 : ℚ) vp0000010000110 := by
  apply branch_left_normalized (c:=vp00000100001100) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-133761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-133761639/500000 : ℚ) by norm_num]
  exact coverp00000100001100
private noncomputable def ep00000100001101_0 : Blocks := edgeBlocks% "full/vectors/00000100001101-E-0000.bin"
noncomputable def ep00000100001101 : Blocks := ep00000100001101_0
private theorem idp00000100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010000110.list =
    C ((2:ℤ)^105) * horner X vp00000100001101.list + horner X ep00000100001101.list := by
  exact edge_identity (B := (2:ℤ)^247) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100001101 : Branch 1 (-133761639/1000000 : ℚ) vp0000010000110 := by
  apply branch_checked idp00000100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-133761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-134261639/500000 : ℚ) by norm_num]
  exact coverp00000100001101
theorem coverp0000010000110 : Covers (-133761639/1000000 : ℚ) vp0000010000110 := join_branches bp00000100001100 bp00000100001101
private noncomputable def vp000001000011_0 : Blocks := edgeBlocks% "full/vectors/000001000011-V-0000.bin"
private noncomputable def vp000001000011_1 : Blocks := edgeBlocks% "full/vectors/000001000011-V-0001.bin"
noncomputable def vp000001000011 : Blocks := (Blocks.join vp000001000011_0 vp000001000011_1)
private theorem bp0000010000110 : Branch 0 (-133761639/2000000 : ℚ) vp000001000011 := by
  apply branch_left_normalized (c:=vp0000010000110) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-133761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-133761639/1000000 : ℚ) by norm_num]
  exact coverp0000010000110
private noncomputable def ep0000010000111_0 : Blocks := edgeBlocks% "full/vectors/0000010000111-E-0000.bin"
private noncomputable def ep0000010000111_1 : Blocks := edgeBlocks% "full/vectors/0000010000111-E-0001.bin"
noncomputable def ep0000010000111 : Blocks := (Blocks.join ep0000010000111_0 ep0000010000111_1)
private theorem idp0000010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001000011.list =
    C ((2:ℤ)^191) * horner X vp0000010000111.list + horner X ep0000010000111.list := by
  exact edge_identity (B := (2:ℤ)^377) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010000111 : Branch 1 (-133761639/2000000 : ℚ) vp000001000011 := by
  apply branch_checked idp0000010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-133761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-134761639/1000000 : ℚ) by norm_num]
  exact coverp0000010000111
theorem coverp000001000011 : Covers (-133761639/2000000 : ℚ) vp000001000011 := join_branches bp0000010000110 bp0000010000111
private noncomputable def vp000001000010111_0 : Blocks := edgeBlocks% "full/vectors/000001000010111-V-0000.bin"
noncomputable def vp000001000010111 : Blocks := vp000001000010111_0
theorem coverp000001000010111 : Covers (-133511639/250000 : ℚ) vp000001000010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000010110_0 : Blocks := edgeBlocks% "full/vectors/000001000010110-V-0000.bin"
noncomputable def vp000001000010110 : Blocks := vp000001000010110_0
theorem coverp000001000010110 : Covers (-133261639/250000 : ℚ) vp000001000010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100001011_0 : Blocks := edgeBlocks% "full/vectors/00000100001011-V-0000.bin"
noncomputable def vp00000100001011 : Blocks := vp00000100001011_0
private theorem bp000001000010110 : Branch 0 (-133261639/500000 : ℚ) vp00000100001011 := by
  apply branch_left_normalized (c:=vp000001000010110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-133261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-133261639/250000 : ℚ) by norm_num]
  exact coverp000001000010110
private noncomputable def ep000001000010111_0 : Blocks := edgeBlocks% "full/vectors/000001000010111-E-0000.bin"
noncomputable def ep000001000010111 : Blocks := ep000001000010111_0
private theorem idp000001000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100001011.list =
    C ((2:ℤ)^61) * horner X vp000001000010111.list + horner X ep000001000010111.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000010111 : Branch 1 (-133261639/500000 : ℚ) vp00000100001011 := by
  apply branch_checked idp000001000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-133261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-133511639/250000 : ℚ) by norm_num]
  exact coverp000001000010111
theorem coverp00000100001011 : Covers (-133261639/500000 : ℚ) vp00000100001011 := join_branches bp000001000010110 bp000001000010111
private noncomputable def vp000001000010101_0 : Blocks := edgeBlocks% "full/vectors/000001000010101-V-0000.bin"
noncomputable def vp000001000010101 : Blocks := vp000001000010101_0
theorem coverp000001000010101 : Covers (-133011639/250000 : ℚ) vp000001000010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000010100_0 : Blocks := edgeBlocks% "full/vectors/000001000010100-V-0000.bin"
noncomputable def vp000001000010100 : Blocks := vp000001000010100_0
theorem coverp000001000010100 : Covers (-132761639/250000 : ℚ) vp000001000010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100001010_0 : Blocks := edgeBlocks% "full/vectors/00000100001010-V-0000.bin"
noncomputable def vp00000100001010 : Blocks := vp00000100001010_0
private theorem bp000001000010100 : Branch 0 (-132761639/500000 : ℚ) vp00000100001010 := by
  apply branch_left_normalized (c:=vp000001000010100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-132761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-132761639/250000 : ℚ) by norm_num]
  exact coverp000001000010100
private noncomputable def ep000001000010101_0 : Blocks := edgeBlocks% "full/vectors/000001000010101-E-0000.bin"
noncomputable def ep000001000010101 : Blocks := ep000001000010101_0
private theorem idp000001000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100001010.list =
    C ((2:ℤ)^60) * horner X vp000001000010101.list + horner X ep000001000010101.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000010101 : Branch 1 (-132761639/500000 : ℚ) vp00000100001010 := by
  apply branch_checked idp000001000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-132761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-133011639/250000 : ℚ) by norm_num]
  exact coverp000001000010101
theorem coverp00000100001010 : Covers (-132761639/500000 : ℚ) vp00000100001010 := join_branches bp000001000010100 bp000001000010101
private noncomputable def vp0000010000101_0 : Blocks := edgeBlocks% "full/vectors/0000010000101-V-0000.bin"
noncomputable def vp0000010000101 : Blocks := vp0000010000101_0
private theorem bp00000100001010 : Branch 0 (-132761639/1000000 : ℚ) vp0000010000101 := by
  apply branch_left_normalized (c:=vp00000100001010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-132761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-132761639/500000 : ℚ) by norm_num]
  exact coverp00000100001010
private noncomputable def ep00000100001011_0 : Blocks := edgeBlocks% "full/vectors/00000100001011-E-0000.bin"
noncomputable def ep00000100001011 : Blocks := ep00000100001011_0
private theorem idp00000100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010000101.list =
    C ((2:ℤ)^105) * horner X vp00000100001011.list + horner X ep00000100001011.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100001011 : Branch 1 (-132761639/1000000 : ℚ) vp0000010000101 := by
  apply branch_checked idp00000100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-132761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-133261639/500000 : ℚ) by norm_num]
  exact coverp00000100001011
theorem coverp0000010000101 : Covers (-132761639/1000000 : ℚ) vp0000010000101 := join_branches bp00000100001010 bp00000100001011
private noncomputable def vp000001000010011_0 : Blocks := edgeBlocks% "full/vectors/000001000010011-V-0000.bin"
noncomputable def vp000001000010011 : Blocks := vp000001000010011_0
theorem coverp000001000010011 : Covers (-132511639/250000 : ℚ) vp000001000010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001000010010_0 : Blocks := edgeBlocks% "full/vectors/000001000010010-V-0000.bin"
noncomputable def vp000001000010010 : Blocks := vp000001000010010_0
theorem coverp000001000010010 : Covers (-132261639/250000 : ℚ) vp000001000010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100001001_0 : Blocks := edgeBlocks% "full/vectors/00000100001001-V-0000.bin"
noncomputable def vp00000100001001 : Blocks := vp00000100001001_0
private theorem bp000001000010010 : Branch 0 (-132261639/500000 : ℚ) vp00000100001001 := by
  apply branch_left_normalized (c:=vp000001000010010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-132261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-132261639/250000 : ℚ) by norm_num]
  exact coverp000001000010010
private noncomputable def ep000001000010011_0 : Blocks := edgeBlocks% "full/vectors/000001000010011-E-0000.bin"
noncomputable def ep000001000010011 : Blocks := ep000001000010011_0
private theorem idp000001000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100001001.list =
    C ((2:ℤ)^60) * horner X vp000001000010011.list + horner X ep000001000010011.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000010011 : Branch 1 (-132261639/500000 : ℚ) vp00000100001001 := by
  apply branch_checked idp000001000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-132261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-132511639/250000 : ℚ) by norm_num]
  exact coverp000001000010011
theorem coverp00000100001001 : Covers (-132261639/500000 : ℚ) vp00000100001001 := join_branches bp000001000010010 bp000001000010011
private noncomputable def vp00000100001000_0 : Blocks := edgeBlocks% "full/vectors/00000100001000-V-0000.bin"
noncomputable def vp00000100001000 : Blocks := vp00000100001000_0
theorem coverp00000100001000 : Covers (-131761639/500000 : ℚ) vp00000100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010000100_0 : Blocks := edgeBlocks% "full/vectors/0000010000100-V-0000.bin"
noncomputable def vp0000010000100 : Blocks := vp0000010000100_0
private theorem bp00000100001000 : Branch 0 (-131761639/1000000 : ℚ) vp0000010000100 := by
  apply branch_left_normalized (c:=vp00000100001000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-131761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-131761639/500000 : ℚ) by norm_num]
  exact coverp00000100001000
private noncomputable def ep00000100001001_0 : Blocks := edgeBlocks% "full/vectors/00000100001001-E-0000.bin"
noncomputable def ep00000100001001 : Blocks := ep00000100001001_0
private theorem idp00000100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010000100.list =
    C ((2:ℤ)^104) * horner X vp00000100001001.list + horner X ep00000100001001.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100001001 : Branch 1 (-131761639/1000000 : ℚ) vp0000010000100 := by
  apply branch_checked idp00000100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-131761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-132261639/500000 : ℚ) by norm_num]
  exact coverp00000100001001
theorem coverp0000010000100 : Covers (-131761639/1000000 : ℚ) vp0000010000100 := join_branches bp00000100001000 bp00000100001001
private noncomputable def vp000001000010_0 : Blocks := edgeBlocks% "full/vectors/000001000010-V-0000.bin"
private noncomputable def vp000001000010_1 : Blocks := edgeBlocks% "full/vectors/000001000010-V-0001.bin"
noncomputable def vp000001000010 : Blocks := (Blocks.join vp000001000010_0 vp000001000010_1)
private theorem bp0000010000100 : Branch 0 (-131761639/2000000 : ℚ) vp000001000010 := by
  apply branch_left_normalized (c:=vp0000010000100) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-131761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-131761639/1000000 : ℚ) by norm_num]
  exact coverp0000010000100
private noncomputable def ep0000010000101_0 : Blocks := edgeBlocks% "full/vectors/0000010000101-E-0000.bin"
private noncomputable def ep0000010000101_1 : Blocks := edgeBlocks% "full/vectors/0000010000101-E-0001.bin"
noncomputable def ep0000010000101 : Blocks := (Blocks.join ep0000010000101_0 ep0000010000101_1)
private theorem idp0000010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001000010.list =
    C ((2:ℤ)^191) * horner X vp0000010000101.list + horner X ep0000010000101.list := by
  exact edge_identity (B := (2:ℤ)^370) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010000101 : Branch 1 (-131761639/2000000 : ℚ) vp000001000010 := by
  apply branch_checked idp0000010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-131761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-132761639/1000000 : ℚ) by norm_num]
  exact coverp0000010000101
theorem coverp000001000010 : Covers (-131761639/2000000 : ℚ) vp000001000010 := join_branches bp0000010000100 bp0000010000101
private noncomputable def vp00000100001_0 : Blocks := edgeBlocks% "full/vectors/00000100001-V-0000.bin"
private noncomputable def vp00000100001_1 : Blocks := edgeBlocks% "full/vectors/00000100001-V-0001.bin"
private noncomputable def vp00000100001_2 : Blocks := edgeBlocks% "full/vectors/00000100001-V-0002.bin"
noncomputable def vp00000100001 : Blocks := (Blocks.join vp00000100001_0 (Blocks.join vp00000100001_1 vp00000100001_2))
private theorem bp000001000010 : Branch 0 (-131761639/4000000 : ℚ) vp00000100001 := by
  apply branch_left_normalized (c:=vp000001000010) (k:=0) (m:=187) (by decide +kernel)
  rw [show 2*(-131761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-131761639/2000000 : ℚ) by norm_num]
  exact coverp000001000010
private noncomputable def ep000001000011_0 : Blocks := edgeBlocks% "full/vectors/000001000011-E-0000.bin"
private noncomputable def ep000001000011_1 : Blocks := edgeBlocks% "full/vectors/000001000011-E-0001.bin"
private noncomputable def ep000001000011_2 : Blocks := edgeBlocks% "full/vectors/000001000011-E-0002.bin"
noncomputable def ep000001000011 : Blocks := (Blocks.join ep000001000011_0 (Blocks.join ep000001000011_1 ep000001000011_2))
private theorem idp000001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100001.list =
    C ((2:ℤ)^364) * horner X vp000001000011.list + horner X ep000001000011.list := by
  exact edge_identity (B := (2:ℤ)^631) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000011 : Branch 1 (-131761639/4000000 : ℚ) vp00000100001 := by
  apply branch_checked idp000001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-131761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-133761639/2000000 : ℚ) by norm_num]
  exact coverp000001000011
theorem coverp00000100001 : Covers (-131761639/4000000 : ℚ) vp00000100001 := join_branches bp000001000010 bp000001000011
private noncomputable def vp00000100000111_0 : Blocks := edgeBlocks% "full/vectors/00000100000111-V-0000.bin"
noncomputable def vp00000100000111 : Blocks := vp00000100000111_0
theorem coverp00000100000111 : Covers (-131261639/500000 : ℚ) vp00000100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100000110_0 : Blocks := edgeBlocks% "full/vectors/00000100000110-V-0000.bin"
noncomputable def vp00000100000110 : Blocks := vp00000100000110_0
theorem coverp00000100000110 : Covers (-130761639/500000 : ℚ) vp00000100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010000011_0 : Blocks := edgeBlocks% "full/vectors/0000010000011-V-0000.bin"
noncomputable def vp0000010000011 : Blocks := vp0000010000011_0
private theorem bp00000100000110 : Branch 0 (-130761639/1000000 : ℚ) vp0000010000011 := by
  apply branch_left_normalized (c:=vp00000100000110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-130761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-130761639/500000 : ℚ) by norm_num]
  exact coverp00000100000110
private noncomputable def ep00000100000111_0 : Blocks := edgeBlocks% "full/vectors/00000100000111-E-0000.bin"
noncomputable def ep00000100000111 : Blocks := ep00000100000111_0
private theorem idp00000100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010000011.list =
    C ((2:ℤ)^104) * horner X vp00000100000111.list + horner X ep00000100000111.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100000111 : Branch 1 (-130761639/1000000 : ℚ) vp0000010000011 := by
  apply branch_checked idp00000100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-130761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-131261639/500000 : ℚ) by norm_num]
  exact coverp00000100000111
theorem coverp0000010000011 : Covers (-130761639/1000000 : ℚ) vp0000010000011 := join_branches bp00000100000110 bp00000100000111
private noncomputable def vp00000100000101_0 : Blocks := edgeBlocks% "full/vectors/00000100000101-V-0000.bin"
noncomputable def vp00000100000101 : Blocks := vp00000100000101_0
theorem coverp00000100000101 : Covers (-130261639/500000 : ℚ) vp00000100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100000100_0 : Blocks := edgeBlocks% "full/vectors/00000100000100-V-0000.bin"
noncomputable def vp00000100000100 : Blocks := vp00000100000100_0
theorem coverp00000100000100 : Covers (-129761639/500000 : ℚ) vp00000100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010000010_0 : Blocks := edgeBlocks% "full/vectors/0000010000010-V-0000.bin"
noncomputable def vp0000010000010 : Blocks := vp0000010000010_0
private theorem bp00000100000100 : Branch 0 (-129761639/1000000 : ℚ) vp0000010000010 := by
  apply branch_left_normalized (c:=vp00000100000100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-129761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-129761639/500000 : ℚ) by norm_num]
  exact coverp00000100000100
private noncomputable def ep00000100000101_0 : Blocks := edgeBlocks% "full/vectors/00000100000101-E-0000.bin"
noncomputable def ep00000100000101 : Blocks := ep00000100000101_0
private theorem idp00000100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010000010.list =
    C ((2:ℤ)^105) * horner X vp00000100000101.list + horner X ep00000100000101.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100000101 : Branch 1 (-129761639/1000000 : ℚ) vp0000010000010 := by
  apply branch_checked idp00000100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-129761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-130261639/500000 : ℚ) by norm_num]
  exact coverp00000100000101
theorem coverp0000010000010 : Covers (-129761639/1000000 : ℚ) vp0000010000010 := join_branches bp00000100000100 bp00000100000101
private noncomputable def vp000001000001_0 : Blocks := edgeBlocks% "full/vectors/000001000001-V-0000.bin"
private noncomputable def vp000001000001_1 : Blocks := edgeBlocks% "full/vectors/000001000001-V-0001.bin"
noncomputable def vp000001000001 : Blocks := (Blocks.join vp000001000001_0 vp000001000001_1)
private theorem bp0000010000010 : Branch 0 (-129761639/2000000 : ℚ) vp000001000001 := by
  apply branch_left_normalized (c:=vp0000010000010) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-129761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-129761639/1000000 : ℚ) by norm_num]
  exact coverp0000010000010
private noncomputable def ep0000010000011_0 : Blocks := edgeBlocks% "full/vectors/0000010000011-E-0000.bin"
private noncomputable def ep0000010000011_1 : Blocks := edgeBlocks% "full/vectors/0000010000011-E-0001.bin"
noncomputable def ep0000010000011 : Blocks := (Blocks.join ep0000010000011_0 ep0000010000011_1)
private theorem idp0000010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001000001.list =
    C ((2:ℤ)^193) * horner X vp0000010000011.list + horner X ep0000010000011.list := by
  exact edge_identity (B := (2:ℤ)^370) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010000011 : Branch 1 (-129761639/2000000 : ℚ) vp000001000001 := by
  apply branch_checked idp0000010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-129761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-130761639/1000000 : ℚ) by norm_num]
  exact coverp0000010000011
theorem coverp000001000001 : Covers (-129761639/2000000 : ℚ) vp000001000001 := join_branches bp0000010000010 bp0000010000011
private noncomputable def vp00000100000011_0 : Blocks := edgeBlocks% "full/vectors/00000100000011-V-0000.bin"
noncomputable def vp00000100000011 : Blocks := vp00000100000011_0
theorem coverp00000100000011 : Covers (-129261639/500000 : ℚ) vp00000100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100000010_0 : Blocks := edgeBlocks% "full/vectors/00000100000010-V-0000.bin"
noncomputable def vp00000100000010 : Blocks := vp00000100000010_0
theorem coverp00000100000010 : Covers (-128761639/500000 : ℚ) vp00000100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010000001_0 : Blocks := edgeBlocks% "full/vectors/0000010000001-V-0000.bin"
noncomputable def vp0000010000001 : Blocks := vp0000010000001_0
private theorem bp00000100000010 : Branch 0 (-128761639/1000000 : ℚ) vp0000010000001 := by
  apply branch_left_normalized (c:=vp00000100000010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-128761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-128761639/500000 : ℚ) by norm_num]
  exact coverp00000100000010
private noncomputable def ep00000100000011_0 : Blocks := edgeBlocks% "full/vectors/00000100000011-E-0000.bin"
noncomputable def ep00000100000011 : Blocks := ep00000100000011_0
private theorem idp00000100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010000001.list =
    C ((2:ℤ)^104) * horner X vp00000100000011.list + horner X ep00000100000011.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100000011 : Branch 1 (-128761639/1000000 : ℚ) vp0000010000001 := by
  apply branch_checked idp00000100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-128761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-129261639/500000 : ℚ) by norm_num]
  exact coverp00000100000011
theorem coverp0000010000001 : Covers (-128761639/1000000 : ℚ) vp0000010000001 := join_branches bp00000100000010 bp00000100000011
private noncomputable def vp00000100000001_0 : Blocks := edgeBlocks% "full/vectors/00000100000001-V-0000.bin"
noncomputable def vp00000100000001 : Blocks := vp00000100000001_0
theorem coverp00000100000001 : Covers (-128261639/500000 : ℚ) vp00000100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100000000_0 : Blocks := edgeBlocks% "full/vectors/00000100000000-V-0000.bin"
noncomputable def vp00000100000000 : Blocks := vp00000100000000_0
theorem coverp00000100000000 : Covers (-127761639/500000 : ℚ) vp00000100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010000000_0 : Blocks := edgeBlocks% "full/vectors/0000010000000-V-0000.bin"
noncomputable def vp0000010000000 : Blocks := vp0000010000000_0
private theorem bp00000100000000 : Branch 0 (-127761639/1000000 : ℚ) vp0000010000000 := by
  apply branch_left_normalized (c:=vp00000100000000) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-127761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-127761639/500000 : ℚ) by norm_num]
  exact coverp00000100000000
private noncomputable def ep00000100000001_0 : Blocks := edgeBlocks% "full/vectors/00000100000001-E-0000.bin"
noncomputable def ep00000100000001 : Blocks := ep00000100000001_0
private theorem idp00000100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010000000.list =
    C ((2:ℤ)^105) * horner X vp00000100000001.list + horner X ep00000100000001.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100000001 : Branch 1 (-127761639/1000000 : ℚ) vp0000010000000 := by
  apply branch_checked idp00000100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-127761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-128261639/500000 : ℚ) by norm_num]
  exact coverp00000100000001
theorem coverp0000010000000 : Covers (-127761639/1000000 : ℚ) vp0000010000000 := join_branches bp00000100000000 bp00000100000001
private noncomputable def vp000001000000_0 : Blocks := edgeBlocks% "full/vectors/000001000000-V-0000.bin"
private noncomputable def vp000001000000_1 : Blocks := edgeBlocks% "full/vectors/000001000000-V-0001.bin"
noncomputable def vp000001000000 : Blocks := (Blocks.join vp000001000000_0 vp000001000000_1)
private theorem bp0000010000000 : Branch 0 (-127761639/2000000 : ℚ) vp000001000000 := by
  apply branch_left_normalized (c:=vp0000010000000) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-127761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-127761639/1000000 : ℚ) by norm_num]
  exact coverp0000010000000
private noncomputable def ep0000010000001_0 : Blocks := edgeBlocks% "full/vectors/0000010000001-E-0000.bin"
private noncomputable def ep0000010000001_1 : Blocks := edgeBlocks% "full/vectors/0000010000001-E-0001.bin"
noncomputable def ep0000010000001 : Blocks := (Blocks.join ep0000010000001_0 ep0000010000001_1)
private theorem idp0000010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001000000.list =
    C ((2:ℤ)^195) * horner X vp0000010000001.list + horner X ep0000010000001.list := by
  exact edge_identity (B := (2:ℤ)^371) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010000001 : Branch 1 (-127761639/2000000 : ℚ) vp000001000000 := by
  apply branch_checked idp0000010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-127761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-128761639/1000000 : ℚ) by norm_num]
  exact coverp0000010000001
theorem coverp000001000000 : Covers (-127761639/2000000 : ℚ) vp000001000000 := join_branches bp0000010000000 bp0000010000001
private noncomputable def vp00000100000_0 : Blocks := edgeBlocks% "full/vectors/00000100000-V-0000.bin"
private noncomputable def vp00000100000_1 : Blocks := edgeBlocks% "full/vectors/00000100000-V-0001.bin"
private noncomputable def vp00000100000_2 : Blocks := edgeBlocks% "full/vectors/00000100000-V-0002.bin"
noncomputable def vp00000100000 : Blocks := (Blocks.join vp00000100000_0 (Blocks.join vp00000100000_1 vp00000100000_2))
private theorem bp000001000000 : Branch 0 (-127761639/4000000 : ℚ) vp00000100000 := by
  apply branch_left_normalized (c:=vp000001000000) (k:=0) (m:=188) (by decide +kernel)
  rw [show 2*(-127761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-127761639/2000000 : ℚ) by norm_num]
  exact coverp000001000000
private noncomputable def ep000001000001_0 : Blocks := edgeBlocks% "full/vectors/000001000001-E-0000.bin"
private noncomputable def ep000001000001_1 : Blocks := edgeBlocks% "full/vectors/000001000001-E-0001.bin"
private noncomputable def ep000001000001_2 : Blocks := edgeBlocks% "full/vectors/000001000001-E-0002.bin"
noncomputable def ep000001000001 : Blocks := (Blocks.join ep000001000001_0 (Blocks.join ep000001000001_1 ep000001000001_2))
private theorem idp000001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100000.list =
    C ((2:ℤ)^373) * horner X vp000001000001.list + horner X ep000001000001.list := by
  exact edge_identity (B := (2:ℤ)^636) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001000001 : Branch 1 (-127761639/4000000 : ℚ) vp00000100000 := by
  apply branch_checked idp000001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-127761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-129761639/2000000 : ℚ) by norm_num]
  exact coverp000001000001
theorem coverp00000100000 : Covers (-127761639/4000000 : ℚ) vp00000100000 := join_branches bp000001000000 bp000001000001
private noncomputable def vp0000010000_0 : Blocks := edgeBlocks% "full/vectors/0000010000-V-0000.bin"
private noncomputable def vp0000010000_1 : Blocks := edgeBlocks% "full/vectors/0000010000-V-0001.bin"
private noncomputable def vp0000010000_2 : Blocks := edgeBlocks% "full/vectors/0000010000-V-0002.bin"
private noncomputable def vp0000010000_3 : Blocks := edgeBlocks% "full/vectors/0000010000-V-0003.bin"
private noncomputable def vp0000010000_4 : Blocks := edgeBlocks% "full/vectors/0000010000-V-0004.bin"
private noncomputable def vp0000010000_5 : Blocks := edgeBlocks% "full/vectors/0000010000-V-0005.bin"
noncomputable def vp0000010000 : Blocks := (Blocks.join (Blocks.join vp0000010000_0 (Blocks.join vp0000010000_1 vp0000010000_2)) (Blocks.join vp0000010000_3 (Blocks.join vp0000010000_4 vp0000010000_5)))
private theorem bp00000100000 : Branch 0 (-127761639/8000000 : ℚ) vp0000010000 := by
  apply branch_left_normalized (c:=vp00000100000) (k:=0) (m:=361) (by decide +kernel)
  rw [show 2*(-127761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-127761639/4000000 : ℚ) by norm_num]
  exact coverp00000100000
private noncomputable def ep00000100001_0 : Blocks := edgeBlocks% "full/vectors/00000100001-E-0000.bin"
private noncomputable def ep00000100001_1 : Blocks := edgeBlocks% "full/vectors/00000100001-E-0001.bin"
private noncomputable def ep00000100001_2 : Blocks := edgeBlocks% "full/vectors/00000100001-E-0002.bin"
private noncomputable def ep00000100001_3 : Blocks := edgeBlocks% "full/vectors/00000100001-E-0003.bin"
private noncomputable def ep00000100001_4 : Blocks := edgeBlocks% "full/vectors/00000100001-E-0004.bin"
private noncomputable def ep00000100001_5 : Blocks := edgeBlocks% "full/vectors/00000100001-E-0005.bin"
noncomputable def ep00000100001 : Blocks := (Blocks.join (Blocks.join ep00000100001_0 (Blocks.join ep00000100001_1 ep00000100001_2)) (Blocks.join ep00000100001_3 (Blocks.join ep00000100001_4 ep00000100001_5)))
private theorem idp00000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010000.list =
    C ((2:ℤ)^725) * horner X vp00000100001.list + horner X ep00000100001.list := by
  exact edge_identity (B := (2:ℤ)^1161) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100001 : Branch 1 (-127761639/8000000 : ℚ) vp0000010000 := by
  apply branch_checked idp00000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-127761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-131761639/4000000 : ℚ) by norm_num]
  exact coverp00000100001
theorem coverp0000010000 : Covers (-127761639/8000000 : ℚ) vp0000010000 := join_branches bp00000100000 bp00000100001
private noncomputable def vp000001000_0 : Blocks := edgeBlocks% "full/vectors/000001000-V-0000.bin"
private noncomputable def vp000001000_1 : Blocks := edgeBlocks% "full/vectors/000001000-V-0001.bin"
private noncomputable def vp000001000_2 : Blocks := edgeBlocks% "full/vectors/000001000-V-0002.bin"
private noncomputable def vp000001000_3 : Blocks := edgeBlocks% "full/vectors/000001000-V-0003.bin"
private noncomputable def vp000001000_4 : Blocks := edgeBlocks% "full/vectors/000001000-V-0004.bin"
private noncomputable def vp000001000_5 : Blocks := edgeBlocks% "full/vectors/000001000-V-0005.bin"
private noncomputable def vp000001000_6 : Blocks := edgeBlocks% "full/vectors/000001000-V-0006.bin"
private noncomputable def vp000001000_7 : Blocks := edgeBlocks% "full/vectors/000001000-V-0007.bin"
private noncomputable def vp000001000_8 : Blocks := edgeBlocks% "full/vectors/000001000-V-0008.bin"
private noncomputable def vp000001000_9 : Blocks := edgeBlocks% "full/vectors/000001000-V-0009.bin"
private noncomputable def vp000001000_10 : Blocks := edgeBlocks% "full/vectors/000001000-V-0010.bin"
noncomputable def vp000001000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000001000_0 vp000001000_1) (Blocks.join vp000001000_2 (Blocks.join vp000001000_3 vp000001000_4))) (Blocks.join (Blocks.join vp000001000_5 (Blocks.join vp000001000_6 vp000001000_7)) (Blocks.join vp000001000_8 (Blocks.join vp000001000_9 vp000001000_10))))
private theorem bp0000010000 : Branch 0 (-127761639/16000000 : ℚ) vp000001000 := by
  apply branch_left_normalized (c:=vp0000010000) (k:=0) (m:=703) (by decide +kernel)
  rw [show 2*(-127761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-127761639/8000000 : ℚ) by norm_num]
  exact coverp0000010000
private noncomputable def ep0000010001_0 : Blocks := edgeBlocks% "full/vectors/0000010001-E-0000.bin"
private noncomputable def ep0000010001_1 : Blocks := edgeBlocks% "full/vectors/0000010001-E-0001.bin"
private noncomputable def ep0000010001_2 : Blocks := edgeBlocks% "full/vectors/0000010001-E-0002.bin"
private noncomputable def ep0000010001_3 : Blocks := edgeBlocks% "full/vectors/0000010001-E-0003.bin"
private noncomputable def ep0000010001_4 : Blocks := edgeBlocks% "full/vectors/0000010001-E-0004.bin"
private noncomputable def ep0000010001_5 : Blocks := edgeBlocks% "full/vectors/0000010001-E-0005.bin"
private noncomputable def ep0000010001_6 : Blocks := edgeBlocks% "full/vectors/0000010001-E-0006.bin"
private noncomputable def ep0000010001_7 : Blocks := edgeBlocks% "full/vectors/0000010001-E-0007.bin"
private noncomputable def ep0000010001_8 : Blocks := edgeBlocks% "full/vectors/0000010001-E-0008.bin"
private noncomputable def ep0000010001_9 : Blocks := edgeBlocks% "full/vectors/0000010001-E-0009.bin"
private noncomputable def ep0000010001_10 : Blocks := edgeBlocks% "full/vectors/0000010001-E-0010.bin"
noncomputable def ep0000010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000010001_0 ep0000010001_1) (Blocks.join ep0000010001_2 (Blocks.join ep0000010001_3 ep0000010001_4))) (Blocks.join (Blocks.join ep0000010001_5 (Blocks.join ep0000010001_6 ep0000010001_7)) (Blocks.join ep0000010001_8 (Blocks.join ep0000010001_9 ep0000010001_10))))
private theorem idp0000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001000.list =
    C ((2:ℤ)^1413) * horner X vp0000010001.list + horner X ep0000010001.list := by
  exact edge_identity (B := (2:ℤ)^2199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010001 : Branch 1 (-127761639/16000000 : ℚ) vp000001000 := by
  apply branch_checked idp0000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-127761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-135761639/8000000 : ℚ) by norm_num]
  exact coverp0000010001
theorem coverp000001000 : Covers (-127761639/16000000 : ℚ) vp000001000 := join_branches bp0000010000 bp0000010001
private noncomputable def vp00000100_0 : Blocks := edgeBlocks% "full/vectors/00000100-V-0000.bin"
private noncomputable def vp00000100_1 : Blocks := edgeBlocks% "full/vectors/00000100-V-0001.bin"
private noncomputable def vp00000100_2 : Blocks := edgeBlocks% "full/vectors/00000100-V-0002.bin"
private noncomputable def vp00000100_3 : Blocks := edgeBlocks% "full/vectors/00000100-V-0003.bin"
private noncomputable def vp00000100_4 : Blocks := edgeBlocks% "full/vectors/00000100-V-0004.bin"
private noncomputable def vp00000100_5 : Blocks := edgeBlocks% "full/vectors/00000100-V-0005.bin"
private noncomputable def vp00000100_6 : Blocks := edgeBlocks% "full/vectors/00000100-V-0006.bin"
private noncomputable def vp00000100_7 : Blocks := edgeBlocks% "full/vectors/00000100-V-0007.bin"
private noncomputable def vp00000100_8 : Blocks := edgeBlocks% "full/vectors/00000100-V-0008.bin"
private noncomputable def vp00000100_9 : Blocks := edgeBlocks% "full/vectors/00000100-V-0009.bin"
private noncomputable def vp00000100_10 : Blocks := edgeBlocks% "full/vectors/00000100-V-0010.bin"
private noncomputable def vp00000100_11 : Blocks := edgeBlocks% "full/vectors/00000100-V-0011.bin"
private noncomputable def vp00000100_12 : Blocks := edgeBlocks% "full/vectors/00000100-V-0012.bin"
private noncomputable def vp00000100_13 : Blocks := edgeBlocks% "full/vectors/00000100-V-0013.bin"
private noncomputable def vp00000100_14 : Blocks := edgeBlocks% "full/vectors/00000100-V-0014.bin"
private noncomputable def vp00000100_15 : Blocks := edgeBlocks% "full/vectors/00000100-V-0015.bin"
private noncomputable def vp00000100_16 : Blocks := edgeBlocks% "full/vectors/00000100-V-0016.bin"
private noncomputable def vp00000100_17 : Blocks := edgeBlocks% "full/vectors/00000100-V-0017.bin"
private noncomputable def vp00000100_18 : Blocks := edgeBlocks% "full/vectors/00000100-V-0018.bin"
private noncomputable def vp00000100_19 : Blocks := edgeBlocks% "full/vectors/00000100-V-0019.bin"
private noncomputable def vp00000100_20 : Blocks := edgeBlocks% "full/vectors/00000100-V-0020.bin"
noncomputable def vp00000100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00000100_0 vp00000100_1) (Blocks.join vp00000100_2 (Blocks.join vp00000100_3 vp00000100_4))) (Blocks.join (Blocks.join vp00000100_5 vp00000100_6) (Blocks.join vp00000100_7 (Blocks.join vp00000100_8 vp00000100_9)))) (Blocks.join (Blocks.join (Blocks.join vp00000100_10 vp00000100_11) (Blocks.join vp00000100_12 (Blocks.join vp00000100_13 vp00000100_14))) (Blocks.join (Blocks.join vp00000100_15 (Blocks.join vp00000100_16 vp00000100_17)) (Blocks.join vp00000100_18 (Blocks.join vp00000100_19 vp00000100_20)))))
private theorem bp000001000 : Branch 0 (-127761639/32000000 : ℚ) vp00000100 := by
  apply branch_left_normalized (c:=vp000001000) (k:=0) (m:=1376) (by decide +kernel)
  rw [show 2*(-127761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-127761639/16000000 : ℚ) by norm_num]
  exact coverp000001000
private noncomputable def ep000001001_0 : Blocks := edgeBlocks% "full/vectors/000001001-E-0000.bin"
private noncomputable def ep000001001_1 : Blocks := edgeBlocks% "full/vectors/000001001-E-0001.bin"
private noncomputable def ep000001001_2 : Blocks := edgeBlocks% "full/vectors/000001001-E-0002.bin"
private noncomputable def ep000001001_3 : Blocks := edgeBlocks% "full/vectors/000001001-E-0003.bin"
private noncomputable def ep000001001_4 : Blocks := edgeBlocks% "full/vectors/000001001-E-0004.bin"
private noncomputable def ep000001001_5 : Blocks := edgeBlocks% "full/vectors/000001001-E-0005.bin"
private noncomputable def ep000001001_6 : Blocks := edgeBlocks% "full/vectors/000001001-E-0006.bin"
private noncomputable def ep000001001_7 : Blocks := edgeBlocks% "full/vectors/000001001-E-0007.bin"
private noncomputable def ep000001001_8 : Blocks := edgeBlocks% "full/vectors/000001001-E-0008.bin"
private noncomputable def ep000001001_9 : Blocks := edgeBlocks% "full/vectors/000001001-E-0009.bin"
private noncomputable def ep000001001_10 : Blocks := edgeBlocks% "full/vectors/000001001-E-0010.bin"
private noncomputable def ep000001001_11 : Blocks := edgeBlocks% "full/vectors/000001001-E-0011.bin"
private noncomputable def ep000001001_12 : Blocks := edgeBlocks% "full/vectors/000001001-E-0012.bin"
private noncomputable def ep000001001_13 : Blocks := edgeBlocks% "full/vectors/000001001-E-0013.bin"
private noncomputable def ep000001001_14 : Blocks := edgeBlocks% "full/vectors/000001001-E-0014.bin"
private noncomputable def ep000001001_15 : Blocks := edgeBlocks% "full/vectors/000001001-E-0015.bin"
private noncomputable def ep000001001_16 : Blocks := edgeBlocks% "full/vectors/000001001-E-0016.bin"
private noncomputable def ep000001001_17 : Blocks := edgeBlocks% "full/vectors/000001001-E-0017.bin"
private noncomputable def ep000001001_18 : Blocks := edgeBlocks% "full/vectors/000001001-E-0018.bin"
private noncomputable def ep000001001_19 : Blocks := edgeBlocks% "full/vectors/000001001-E-0019.bin"
private noncomputable def ep000001001_20 : Blocks := edgeBlocks% "full/vectors/000001001-E-0020.bin"
noncomputable def ep000001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep000001001_0 ep000001001_1) (Blocks.join ep000001001_2 (Blocks.join ep000001001_3 ep000001001_4))) (Blocks.join (Blocks.join ep000001001_5 ep000001001_6) (Blocks.join ep000001001_7 (Blocks.join ep000001001_8 ep000001001_9)))) (Blocks.join (Blocks.join (Blocks.join ep000001001_10 ep000001001_11) (Blocks.join ep000001001_12 (Blocks.join ep000001001_13 ep000001001_14))) (Blocks.join (Blocks.join ep000001001_15 (Blocks.join ep000001001_16 ep000001001_17)) (Blocks.join ep000001001_18 (Blocks.join ep000001001_19 ep000001001_20)))))
private theorem idp000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100.list =
    C ((2:ℤ)^2760) * horner X vp000001001.list + horner X ep000001001.list := by
  exact edge_identity (B := (2:ℤ)^4225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001 : Branch 1 (-127761639/32000000 : ℚ) vp00000100 := by
  apply branch_checked idp000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-127761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-143761639/16000000 : ℚ) by norm_num]
  exact coverp000001001
theorem coverp00000100 : Covers (-127761639/32000000 : ℚ) vp00000100 := join_branches bp000001000 bp000001001
end NextProof.EdgeFull

