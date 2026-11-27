import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000001101111111_0 : Blocks := edgeBlocks% "full/vectors/000001101111111-V-0000.bin"
noncomputable def vp000001101111111 : Blocks := vp000001101111111_0
theorem coverp000001101111111 : Covers (-223511639/250000 : ℚ) vp000001101111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001101111110_0 : Blocks := edgeBlocks% "full/vectors/000001101111110-V-0000.bin"
noncomputable def vp000001101111110 : Blocks := vp000001101111110_0
theorem coverp000001101111110 : Covers (-223261639/250000 : ℚ) vp000001101111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110111111_0 : Blocks := edgeBlocks% "full/vectors/00000110111111-V-0000.bin"
noncomputable def vp00000110111111 : Blocks := vp00000110111111_0
private theorem bp000001101111110 : Branch 0 (-223261639/500000 : ℚ) vp00000110111111 := by
  apply branch_left_normalized (c:=vp000001101111110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-223261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-223261639/250000 : ℚ) by norm_num]
  exact coverp000001101111110
private noncomputable def ep000001101111111_0 : Blocks := edgeBlocks% "full/vectors/000001101111111-E-0000.bin"
noncomputable def ep000001101111111 : Blocks := ep000001101111111_0
private theorem idp000001101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110111111.list =
    C ((2:ℤ)^53) * horner X vp000001101111111.list + horner X ep000001101111111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101111111 : Branch 1 (-223261639/500000 : ℚ) vp00000110111111 := by
  apply branch_checked idp000001101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-223261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-223511639/250000 : ℚ) by norm_num]
  exact coverp000001101111111
theorem coverp00000110111111 : Covers (-223261639/500000 : ℚ) vp00000110111111 := join_branches bp000001101111110 bp000001101111111
private noncomputable def vp000001101111101_0 : Blocks := edgeBlocks% "full/vectors/000001101111101-V-0000.bin"
noncomputable def vp000001101111101 : Blocks := vp000001101111101_0
theorem coverp000001101111101 : Covers (-223011639/250000 : ℚ) vp000001101111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001101111100_0 : Blocks := edgeBlocks% "full/vectors/000001101111100-V-0000.bin"
noncomputable def vp000001101111100 : Blocks := vp000001101111100_0
theorem coverp000001101111100 : Covers (-222761639/250000 : ℚ) vp000001101111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110111110_0 : Blocks := edgeBlocks% "full/vectors/00000110111110-V-0000.bin"
noncomputable def vp00000110111110 : Blocks := vp00000110111110_0
private theorem bp000001101111100 : Branch 0 (-222761639/500000 : ℚ) vp00000110111110 := by
  apply branch_left_normalized (c:=vp000001101111100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-222761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-222761639/250000 : ℚ) by norm_num]
  exact coverp000001101111100
private noncomputable def ep000001101111101_0 : Blocks := edgeBlocks% "full/vectors/000001101111101-E-0000.bin"
noncomputable def ep000001101111101 : Blocks := ep000001101111101_0
private theorem idp000001101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110111110.list =
    C ((2:ℤ)^52) * horner X vp000001101111101.list + horner X ep000001101111101.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101111101 : Branch 1 (-222761639/500000 : ℚ) vp00000110111110 := by
  apply branch_checked idp000001101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-222761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-223011639/250000 : ℚ) by norm_num]
  exact coverp000001101111101
theorem coverp00000110111110 : Covers (-222761639/500000 : ℚ) vp00000110111110 := join_branches bp000001101111100 bp000001101111101
private noncomputable def vp0000011011111_0 : Blocks := edgeBlocks% "full/vectors/0000011011111-V-0000.bin"
noncomputable def vp0000011011111 : Blocks := vp0000011011111_0
private theorem bp00000110111110 : Branch 0 (-222761639/1000000 : ℚ) vp0000011011111 := by
  apply branch_left_normalized (c:=vp00000110111110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-222761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-222761639/500000 : ℚ) by norm_num]
  exact coverp00000110111110
private noncomputable def ep00000110111111_0 : Blocks := edgeBlocks% "full/vectors/00000110111111-E-0000.bin"
noncomputable def ep00000110111111 : Blocks := ep00000110111111_0
private theorem idp00000110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011011111.list =
    C ((2:ℤ)^88) * horner X vp00000110111111.list + horner X ep00000110111111.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110111111 : Branch 1 (-222761639/1000000 : ℚ) vp0000011011111 := by
  apply branch_checked idp00000110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-222761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-223261639/500000 : ℚ) by norm_num]
  exact coverp00000110111111
theorem coverp0000011011111 : Covers (-222761639/1000000 : ℚ) vp0000011011111 := join_branches bp00000110111110 bp00000110111111
private noncomputable def vp000001101111011_0 : Blocks := edgeBlocks% "full/vectors/000001101111011-V-0000.bin"
noncomputable def vp000001101111011 : Blocks := vp000001101111011_0
theorem coverp000001101111011 : Covers (-222511639/250000 : ℚ) vp000001101111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001101111010_0 : Blocks := edgeBlocks% "full/vectors/000001101111010-V-0000.bin"
noncomputable def vp000001101111010 : Blocks := vp000001101111010_0
theorem coverp000001101111010 : Covers (-222261639/250000 : ℚ) vp000001101111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110111101_0 : Blocks := edgeBlocks% "full/vectors/00000110111101-V-0000.bin"
noncomputable def vp00000110111101 : Blocks := vp00000110111101_0
private theorem bp000001101111010 : Branch 0 (-222261639/500000 : ℚ) vp00000110111101 := by
  apply branch_left_normalized (c:=vp000001101111010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-222261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-222261639/250000 : ℚ) by norm_num]
  exact coverp000001101111010
private noncomputable def ep000001101111011_0 : Blocks := edgeBlocks% "full/vectors/000001101111011-E-0000.bin"
noncomputable def ep000001101111011 : Blocks := ep000001101111011_0
private theorem idp000001101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110111101.list =
    C ((2:ℤ)^53) * horner X vp000001101111011.list + horner X ep000001101111011.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101111011 : Branch 1 (-222261639/500000 : ℚ) vp00000110111101 := by
  apply branch_checked idp000001101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-222261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-222511639/250000 : ℚ) by norm_num]
  exact coverp000001101111011
theorem coverp00000110111101 : Covers (-222261639/500000 : ℚ) vp00000110111101 := join_branches bp000001101111010 bp000001101111011
private noncomputable def vp000001101111001_0 : Blocks := edgeBlocks% "full/vectors/000001101111001-V-0000.bin"
noncomputable def vp000001101111001 : Blocks := vp000001101111001_0
theorem coverp000001101111001 : Covers (-222011639/250000 : ℚ) vp000001101111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001101111000_0 : Blocks := edgeBlocks% "full/vectors/000001101111000-V-0000.bin"
noncomputable def vp000001101111000 : Blocks := vp000001101111000_0
theorem coverp000001101111000 : Covers (-221761639/250000 : ℚ) vp000001101111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110111100_0 : Blocks := edgeBlocks% "full/vectors/00000110111100-V-0000.bin"
noncomputable def vp00000110111100 : Blocks := vp00000110111100_0
private theorem bp000001101111000 : Branch 0 (-221761639/500000 : ℚ) vp00000110111100 := by
  apply branch_left_normalized (c:=vp000001101111000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-221761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-221761639/250000 : ℚ) by norm_num]
  exact coverp000001101111000
private noncomputable def ep000001101111001_0 : Blocks := edgeBlocks% "full/vectors/000001101111001-E-0000.bin"
noncomputable def ep000001101111001 : Blocks := ep000001101111001_0
private theorem idp000001101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110111100.list =
    C ((2:ℤ)^54) * horner X vp000001101111001.list + horner X ep000001101111001.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101111001 : Branch 1 (-221761639/500000 : ℚ) vp00000110111100 := by
  apply branch_checked idp000001101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-221761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-222011639/250000 : ℚ) by norm_num]
  exact coverp000001101111001
theorem coverp00000110111100 : Covers (-221761639/500000 : ℚ) vp00000110111100 := join_branches bp000001101111000 bp000001101111001
private noncomputable def vp0000011011110_0 : Blocks := edgeBlocks% "full/vectors/0000011011110-V-0000.bin"
noncomputable def vp0000011011110 : Blocks := vp0000011011110_0
private theorem bp00000110111100 : Branch 0 (-221761639/1000000 : ℚ) vp0000011011110 := by
  apply branch_left_normalized (c:=vp00000110111100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-221761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-221761639/500000 : ℚ) by norm_num]
  exact coverp00000110111100
private noncomputable def ep00000110111101_0 : Blocks := edgeBlocks% "full/vectors/00000110111101-E-0000.bin"
noncomputable def ep00000110111101 : Blocks := ep00000110111101_0
private theorem idp00000110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011011110.list =
    C ((2:ℤ)^89) * horner X vp00000110111101.list + horner X ep00000110111101.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110111101 : Branch 1 (-221761639/1000000 : ℚ) vp0000011011110 := by
  apply branch_checked idp00000110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-221761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-222261639/500000 : ℚ) by norm_num]
  exact coverp00000110111101
theorem coverp0000011011110 : Covers (-221761639/1000000 : ℚ) vp0000011011110 := join_branches bp00000110111100 bp00000110111101
private noncomputable def vp000001101111_0 : Blocks := edgeBlocks% "full/vectors/000001101111-V-0000.bin"
private noncomputable def vp000001101111_1 : Blocks := edgeBlocks% "full/vectors/000001101111-V-0001.bin"
noncomputable def vp000001101111 : Blocks := (Blocks.join vp000001101111_0 vp000001101111_1)
private theorem bp0000011011110 : Branch 0 (-221761639/2000000 : ℚ) vp000001101111 := by
  apply branch_left_normalized (c:=vp0000011011110) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-221761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-221761639/1000000 : ℚ) by norm_num]
  exact coverp0000011011110
private noncomputable def ep0000011011111_0 : Blocks := edgeBlocks% "full/vectors/0000011011111-E-0000.bin"
private noncomputable def ep0000011011111_1 : Blocks := edgeBlocks% "full/vectors/0000011011111-E-0001.bin"
noncomputable def ep0000011011111 : Blocks := (Blocks.join ep0000011011111_0 ep0000011011111_1)
private theorem idp0000011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001101111.list =
    C ((2:ℤ)^157) * horner X vp0000011011111.list + horner X ep0000011011111.list := by
  exact edge_identity (B := (2:ℤ)^321) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011011111 : Branch 1 (-221761639/2000000 : ℚ) vp000001101111 := by
  apply branch_checked idp0000011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-221761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-222761639/1000000 : ℚ) by norm_num]
  exact coverp0000011011111
theorem coverp000001101111 : Covers (-221761639/2000000 : ℚ) vp000001101111 := join_branches bp0000011011110 bp0000011011111
private noncomputable def vp000001101110111_0 : Blocks := edgeBlocks% "full/vectors/000001101110111-V-0000.bin"
noncomputable def vp000001101110111 : Blocks := vp000001101110111_0
theorem coverp000001101110111 : Covers (-221511639/250000 : ℚ) vp000001101110111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001101110110_0 : Blocks := edgeBlocks% "full/vectors/000001101110110-V-0000.bin"
noncomputable def vp000001101110110 : Blocks := vp000001101110110_0
theorem coverp000001101110110 : Covers (-221261639/250000 : ℚ) vp000001101110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110111011_0 : Blocks := edgeBlocks% "full/vectors/00000110111011-V-0000.bin"
noncomputable def vp00000110111011 : Blocks := vp00000110111011_0
private theorem bp000001101110110 : Branch 0 (-221261639/500000 : ℚ) vp00000110111011 := by
  apply branch_left_normalized (c:=vp000001101110110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-221261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-221261639/250000 : ℚ) by norm_num]
  exact coverp000001101110110
private noncomputable def ep000001101110111_0 : Blocks := edgeBlocks% "full/vectors/000001101110111-E-0000.bin"
noncomputable def ep000001101110111 : Blocks := ep000001101110111_0
private theorem idp000001101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110111011.list =
    C ((2:ℤ)^53) * horner X vp000001101110111.list + horner X ep000001101110111.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101110111 : Branch 1 (-221261639/500000 : ℚ) vp00000110111011 := by
  apply branch_checked idp000001101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-221261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-221511639/250000 : ℚ) by norm_num]
  exact coverp000001101110111
theorem coverp00000110111011 : Covers (-221261639/500000 : ℚ) vp00000110111011 := join_branches bp000001101110110 bp000001101110111
private noncomputable def vp00000110111010_0 : Blocks := edgeBlocks% "full/vectors/00000110111010-V-0000.bin"
noncomputable def vp00000110111010 : Blocks := vp00000110111010_0
theorem coverp00000110111010 : Covers (-220761639/500000 : ℚ) vp00000110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011011101_0 : Blocks := edgeBlocks% "full/vectors/0000011011101-V-0000.bin"
noncomputable def vp0000011011101 : Blocks := vp0000011011101_0
private theorem bp00000110111010 : Branch 0 (-220761639/1000000 : ℚ) vp0000011011101 := by
  apply branch_left_normalized (c:=vp00000110111010) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-220761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-220761639/500000 : ℚ) by norm_num]
  exact coverp00000110111010
private noncomputable def ep00000110111011_0 : Blocks := edgeBlocks% "full/vectors/00000110111011-E-0000.bin"
noncomputable def ep00000110111011 : Blocks := ep00000110111011_0
private theorem idp00000110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011011101.list =
    C ((2:ℤ)^90) * horner X vp00000110111011.list + horner X ep00000110111011.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110111011 : Branch 1 (-220761639/1000000 : ℚ) vp0000011011101 := by
  apply branch_checked idp00000110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-220761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-221261639/500000 : ℚ) by norm_num]
  exact coverp00000110111011
theorem coverp0000011011101 : Covers (-220761639/1000000 : ℚ) vp0000011011101 := join_branches bp00000110111010 bp00000110111011
private noncomputable def vp000001101110011_0 : Blocks := edgeBlocks% "full/vectors/000001101110011-V-0000.bin"
noncomputable def vp000001101110011 : Blocks := vp000001101110011_0
theorem coverp000001101110011 : Covers (-220511639/250000 : ℚ) vp000001101110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001101110010_0 : Blocks := edgeBlocks% "full/vectors/000001101110010-V-0000.bin"
noncomputable def vp000001101110010 : Blocks := vp000001101110010_0
theorem coverp000001101110010 : Covers (-220261639/250000 : ℚ) vp000001101110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110111001_0 : Blocks := edgeBlocks% "full/vectors/00000110111001-V-0000.bin"
noncomputable def vp00000110111001 : Blocks := vp00000110111001_0
private theorem bp000001101110010 : Branch 0 (-220261639/500000 : ℚ) vp00000110111001 := by
  apply branch_left_normalized (c:=vp000001101110010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-220261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-220261639/250000 : ℚ) by norm_num]
  exact coverp000001101110010
private noncomputable def ep000001101110011_0 : Blocks := edgeBlocks% "full/vectors/000001101110011-E-0000.bin"
noncomputable def ep000001101110011 : Blocks := ep000001101110011_0
private theorem idp000001101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110111001.list =
    C ((2:ℤ)^55) * horner X vp000001101110011.list + horner X ep000001101110011.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101110011 : Branch 1 (-220261639/500000 : ℚ) vp00000110111001 := by
  apply branch_checked idp000001101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-220261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-220511639/250000 : ℚ) by norm_num]
  exact coverp000001101110011
theorem coverp00000110111001 : Covers (-220261639/500000 : ℚ) vp00000110111001 := join_branches bp000001101110010 bp000001101110011
private noncomputable def vp000001101110001_0 : Blocks := edgeBlocks% "full/vectors/000001101110001-V-0000.bin"
noncomputable def vp000001101110001 : Blocks := vp000001101110001_0
theorem coverp000001101110001 : Covers (-220011639/250000 : ℚ) vp000001101110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001101110000_0 : Blocks := edgeBlocks% "full/vectors/000001101110000-V-0000.bin"
noncomputable def vp000001101110000 : Blocks := vp000001101110000_0
theorem coverp000001101110000 : Covers (-219761639/250000 : ℚ) vp000001101110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110111000_0 : Blocks := edgeBlocks% "full/vectors/00000110111000-V-0000.bin"
noncomputable def vp00000110111000 : Blocks := vp00000110111000_0
private theorem bp000001101110000 : Branch 0 (-219761639/500000 : ℚ) vp00000110111000 := by
  apply branch_left_normalized (c:=vp000001101110000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-219761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-219761639/250000 : ℚ) by norm_num]
  exact coverp000001101110000
private noncomputable def ep000001101110001_0 : Blocks := edgeBlocks% "full/vectors/000001101110001-E-0000.bin"
noncomputable def ep000001101110001 : Blocks := ep000001101110001_0
private theorem idp000001101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110111000.list =
    C ((2:ℤ)^56) * horner X vp000001101110001.list + horner X ep000001101110001.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101110001 : Branch 1 (-219761639/500000 : ℚ) vp00000110111000 := by
  apply branch_checked idp000001101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-219761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-220011639/250000 : ℚ) by norm_num]
  exact coverp000001101110001
theorem coverp00000110111000 : Covers (-219761639/500000 : ℚ) vp00000110111000 := join_branches bp000001101110000 bp000001101110001
private noncomputable def vp0000011011100_0 : Blocks := edgeBlocks% "full/vectors/0000011011100-V-0000.bin"
noncomputable def vp0000011011100 : Blocks := vp0000011011100_0
private theorem bp00000110111000 : Branch 0 (-219761639/1000000 : ℚ) vp0000011011100 := by
  apply branch_left_normalized (c:=vp00000110111000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-219761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-219761639/500000 : ℚ) by norm_num]
  exact coverp00000110111000
private noncomputable def ep00000110111001_0 : Blocks := edgeBlocks% "full/vectors/00000110111001-E-0000.bin"
noncomputable def ep00000110111001 : Blocks := ep00000110111001_0
private theorem idp00000110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011011100.list =
    C ((2:ℤ)^94) * horner X vp00000110111001.list + horner X ep00000110111001.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110111001 : Branch 1 (-219761639/1000000 : ℚ) vp0000011011100 := by
  apply branch_checked idp00000110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-219761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-220261639/500000 : ℚ) by norm_num]
  exact coverp00000110111001
theorem coverp0000011011100 : Covers (-219761639/1000000 : ℚ) vp0000011011100 := join_branches bp00000110111000 bp00000110111001
private noncomputable def vp000001101110_0 : Blocks := edgeBlocks% "full/vectors/000001101110-V-0000.bin"
private noncomputable def vp000001101110_1 : Blocks := edgeBlocks% "full/vectors/000001101110-V-0001.bin"
noncomputable def vp000001101110 : Blocks := (Blocks.join vp000001101110_0 vp000001101110_1)
private theorem bp0000011011100 : Branch 0 (-219761639/2000000 : ℚ) vp000001101110 := by
  apply branch_left_normalized (c:=vp0000011011100) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-219761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-219761639/1000000 : ℚ) by norm_num]
  exact coverp0000011011100
private noncomputable def ep0000011011101_0 : Blocks := edgeBlocks% "full/vectors/0000011011101-E-0000.bin"
private noncomputable def ep0000011011101_1 : Blocks := edgeBlocks% "full/vectors/0000011011101-E-0001.bin"
noncomputable def ep0000011011101 : Blocks := (Blocks.join ep0000011011101_0 ep0000011011101_1)
private theorem idp0000011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001101110.list =
    C ((2:ℤ)^164) * horner X vp0000011011101.list + horner X ep0000011011101.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011011101 : Branch 1 (-219761639/2000000 : ℚ) vp000001101110 := by
  apply branch_checked idp0000011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-219761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-220761639/1000000 : ℚ) by norm_num]
  exact coverp0000011011101
theorem coverp000001101110 : Covers (-219761639/2000000 : ℚ) vp000001101110 := join_branches bp0000011011100 bp0000011011101
private noncomputable def vp00000110111_0 : Blocks := edgeBlocks% "full/vectors/00000110111-V-0000.bin"
private noncomputable def vp00000110111_1 : Blocks := edgeBlocks% "full/vectors/00000110111-V-0001.bin"
private noncomputable def vp00000110111_2 : Blocks := edgeBlocks% "full/vectors/00000110111-V-0002.bin"
noncomputable def vp00000110111 : Blocks := (Blocks.join vp00000110111_0 (Blocks.join vp00000110111_1 vp00000110111_2))
private theorem bp000001101110 : Branch 0 (-219761639/4000000 : ℚ) vp00000110111 := by
  apply branch_left_normalized (c:=vp000001101110) (k:=0) (m:=154) (by decide +kernel)
  rw [show 2*(-219761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-219761639/2000000 : ℚ) by norm_num]
  exact coverp000001101110
private noncomputable def ep000001101111_0 : Blocks := edgeBlocks% "full/vectors/000001101111-E-0000.bin"
private noncomputable def ep000001101111_1 : Blocks := edgeBlocks% "full/vectors/000001101111-E-0001.bin"
private noncomputable def ep000001101111_2 : Blocks := edgeBlocks% "full/vectors/000001101111-E-0002.bin"
noncomputable def ep000001101111 : Blocks := (Blocks.join ep000001101111_0 (Blocks.join ep000001101111_1 ep000001101111_2))
private theorem idp000001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110111.list =
    C ((2:ℤ)^302) * horner X vp000001101111.list + horner X ep000001101111.list := by
  exact edge_identity (B := (2:ℤ)^530) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101111 : Branch 1 (-219761639/4000000 : ℚ) vp00000110111 := by
  apply branch_checked idp000001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-219761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-221761639/2000000 : ℚ) by norm_num]
  exact coverp000001101111
theorem coverp00000110111 : Covers (-219761639/4000000 : ℚ) vp00000110111 := join_branches bp000001101110 bp000001101111
private noncomputable def vp000001101101111_0 : Blocks := edgeBlocks% "full/vectors/000001101101111-V-0000.bin"
noncomputable def vp000001101101111 : Blocks := vp000001101101111_0
theorem coverp000001101101111 : Covers (-219511639/250000 : ℚ) vp000001101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001101101110_0 : Blocks := edgeBlocks% "full/vectors/000001101101110-V-0000.bin"
noncomputable def vp000001101101110 : Blocks := vp000001101101110_0
theorem coverp000001101101110 : Covers (-219261639/250000 : ℚ) vp000001101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110110111_0 : Blocks := edgeBlocks% "full/vectors/00000110110111-V-0000.bin"
noncomputable def vp00000110110111 : Blocks := vp00000110110111_0
private theorem bp000001101101110 : Branch 0 (-219261639/500000 : ℚ) vp00000110110111 := by
  apply branch_left_normalized (c:=vp000001101101110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-219261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-219261639/250000 : ℚ) by norm_num]
  exact coverp000001101101110
private noncomputable def ep000001101101111_0 : Blocks := edgeBlocks% "full/vectors/000001101101111-E-0000.bin"
noncomputable def ep000001101101111 : Blocks := ep000001101101111_0
private theorem idp000001101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110110111.list =
    C ((2:ℤ)^53) * horner X vp000001101101111.list + horner X ep000001101101111.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101101111 : Branch 1 (-219261639/500000 : ℚ) vp00000110110111 := by
  apply branch_checked idp000001101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-219261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-219511639/250000 : ℚ) by norm_num]
  exact coverp000001101101111
theorem coverp00000110110111 : Covers (-219261639/500000 : ℚ) vp00000110110111 := join_branches bp000001101101110 bp000001101101111
private noncomputable def vp000001101101101_0 : Blocks := edgeBlocks% "full/vectors/000001101101101-V-0000.bin"
noncomputable def vp000001101101101 : Blocks := vp000001101101101_0
theorem coverp000001101101101 : Covers (-219011639/250000 : ℚ) vp000001101101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001101101100_0 : Blocks := edgeBlocks% "full/vectors/000001101101100-V-0000.bin"
noncomputable def vp000001101101100 : Blocks := vp000001101101100_0
theorem coverp000001101101100 : Covers (-218761639/250000 : ℚ) vp000001101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110110110_0 : Blocks := edgeBlocks% "full/vectors/00000110110110-V-0000.bin"
noncomputable def vp00000110110110 : Blocks := vp00000110110110_0
private theorem bp000001101101100 : Branch 0 (-218761639/500000 : ℚ) vp00000110110110 := by
  apply branch_left_normalized (c:=vp000001101101100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-218761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-218761639/250000 : ℚ) by norm_num]
  exact coverp000001101101100
private noncomputable def ep000001101101101_0 : Blocks := edgeBlocks% "full/vectors/000001101101101-E-0000.bin"
noncomputable def ep000001101101101 : Blocks := ep000001101101101_0
private theorem idp000001101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110110110.list =
    C ((2:ℤ)^52) * horner X vp000001101101101.list + horner X ep000001101101101.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101101101 : Branch 1 (-218761639/500000 : ℚ) vp00000110110110 := by
  apply branch_checked idp000001101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-218761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-219011639/250000 : ℚ) by norm_num]
  exact coverp000001101101101
theorem coverp00000110110110 : Covers (-218761639/500000 : ℚ) vp00000110110110 := join_branches bp000001101101100 bp000001101101101
private noncomputable def vp0000011011011_0 : Blocks := edgeBlocks% "full/vectors/0000011011011-V-0000.bin"
noncomputable def vp0000011011011 : Blocks := vp0000011011011_0
private theorem bp00000110110110 : Branch 0 (-218761639/1000000 : ℚ) vp0000011011011 := by
  apply branch_left_normalized (c:=vp00000110110110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-218761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-218761639/500000 : ℚ) by norm_num]
  exact coverp00000110110110
private noncomputable def ep00000110110111_0 : Blocks := edgeBlocks% "full/vectors/00000110110111-E-0000.bin"
noncomputable def ep00000110110111 : Blocks := ep00000110110111_0
private theorem idp00000110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011011011.list =
    C ((2:ℤ)^86) * horner X vp00000110110111.list + horner X ep00000110110111.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110110111 : Branch 1 (-218761639/1000000 : ℚ) vp0000011011011 := by
  apply branch_checked idp00000110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-218761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-219261639/500000 : ℚ) by norm_num]
  exact coverp00000110110111
theorem coverp0000011011011 : Covers (-218761639/1000000 : ℚ) vp0000011011011 := join_branches bp00000110110110 bp00000110110111
private noncomputable def vp00000110110101_0 : Blocks := edgeBlocks% "full/vectors/00000110110101-V-0000.bin"
noncomputable def vp00000110110101 : Blocks := vp00000110110101_0
theorem coverp00000110110101 : Covers (-218261639/500000 : ℚ) vp00000110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110110100_0 : Blocks := edgeBlocks% "full/vectors/00000110110100-V-0000.bin"
noncomputable def vp00000110110100 : Blocks := vp00000110110100_0
theorem coverp00000110110100 : Covers (-217761639/500000 : ℚ) vp00000110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011011010_0 : Blocks := edgeBlocks% "full/vectors/0000011011010-V-0000.bin"
noncomputable def vp0000011011010 : Blocks := vp0000011011010_0
private theorem bp00000110110100 : Branch 0 (-217761639/1000000 : ℚ) vp0000011011010 := by
  apply branch_left_normalized (c:=vp00000110110100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-217761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-217761639/500000 : ℚ) by norm_num]
  exact coverp00000110110100
private noncomputable def ep00000110110101_0 : Blocks := edgeBlocks% "full/vectors/00000110110101-E-0000.bin"
noncomputable def ep00000110110101 : Blocks := ep00000110110101_0
private theorem idp00000110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011011010.list =
    C ((2:ℤ)^87) * horner X vp00000110110101.list + horner X ep00000110110101.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110110101 : Branch 1 (-217761639/1000000 : ℚ) vp0000011011010 := by
  apply branch_checked idp00000110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-217761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-218261639/500000 : ℚ) by norm_num]
  exact coverp00000110110101
theorem coverp0000011011010 : Covers (-217761639/1000000 : ℚ) vp0000011011010 := join_branches bp00000110110100 bp00000110110101
private noncomputable def vp000001101101_0 : Blocks := edgeBlocks% "full/vectors/000001101101-V-0000.bin"
private noncomputable def vp000001101101_1 : Blocks := edgeBlocks% "full/vectors/000001101101-V-0001.bin"
noncomputable def vp000001101101 : Blocks := (Blocks.join vp000001101101_0 vp000001101101_1)
private theorem bp0000011011010 : Branch 0 (-217761639/2000000 : ℚ) vp000001101101 := by
  apply branch_left_normalized (c:=vp0000011011010) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-217761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-217761639/1000000 : ℚ) by norm_num]
  exact coverp0000011011010
private noncomputable def ep0000011011011_0 : Blocks := edgeBlocks% "full/vectors/0000011011011-E-0000.bin"
private noncomputable def ep0000011011011_1 : Blocks := edgeBlocks% "full/vectors/0000011011011-E-0001.bin"
noncomputable def ep0000011011011 : Blocks := (Blocks.join ep0000011011011_0 ep0000011011011_1)
private theorem idp0000011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001101101.list =
    C ((2:ℤ)^154) * horner X vp0000011011011.list + horner X ep0000011011011.list := by
  exact edge_identity (B := (2:ℤ)^316) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011011011 : Branch 1 (-217761639/2000000 : ℚ) vp000001101101 := by
  apply branch_checked idp0000011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-217761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-218761639/1000000 : ℚ) by norm_num]
  exact coverp0000011011011
theorem coverp000001101101 : Covers (-217761639/2000000 : ℚ) vp000001101101 := join_branches bp0000011011010 bp0000011011011
private noncomputable def vp00000110110011_0 : Blocks := edgeBlocks% "full/vectors/00000110110011-V-0000.bin"
noncomputable def vp00000110110011 : Blocks := vp00000110110011_0
theorem coverp00000110110011 : Covers (-217261639/500000 : ℚ) vp00000110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110110010_0 : Blocks := edgeBlocks% "full/vectors/00000110110010-V-0000.bin"
noncomputable def vp00000110110010 : Blocks := vp00000110110010_0
theorem coverp00000110110010 : Covers (-216761639/500000 : ℚ) vp00000110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011011001_0 : Blocks := edgeBlocks% "full/vectors/0000011011001-V-0000.bin"
noncomputable def vp0000011011001 : Blocks := vp0000011011001_0
private theorem bp00000110110010 : Branch 0 (-216761639/1000000 : ℚ) vp0000011011001 := by
  apply branch_left_normalized (c:=vp00000110110010) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-216761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-216761639/500000 : ℚ) by norm_num]
  exact coverp00000110110010
private noncomputable def ep00000110110011_0 : Blocks := edgeBlocks% "full/vectors/00000110110011-E-0000.bin"
noncomputable def ep00000110110011 : Blocks := ep00000110110011_0
private theorem idp00000110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011011001.list =
    C ((2:ℤ)^86) * horner X vp00000110110011.list + horner X ep00000110110011.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110110011 : Branch 1 (-216761639/1000000 : ℚ) vp0000011011001 := by
  apply branch_checked idp00000110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-216761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-217261639/500000 : ℚ) by norm_num]
  exact coverp00000110110011
theorem coverp0000011011001 : Covers (-216761639/1000000 : ℚ) vp0000011011001 := join_branches bp00000110110010 bp00000110110011
private noncomputable def vp00000110110001_0 : Blocks := edgeBlocks% "full/vectors/00000110110001-V-0000.bin"
noncomputable def vp00000110110001 : Blocks := vp00000110110001_0
theorem coverp00000110110001 : Covers (-216261639/500000 : ℚ) vp00000110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110110000_0 : Blocks := edgeBlocks% "full/vectors/00000110110000-V-0000.bin"
noncomputable def vp00000110110000 : Blocks := vp00000110110000_0
theorem coverp00000110110000 : Covers (-215761639/500000 : ℚ) vp00000110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011011000_0 : Blocks := edgeBlocks% "full/vectors/0000011011000-V-0000.bin"
noncomputable def vp0000011011000 : Blocks := vp0000011011000_0
private theorem bp00000110110000 : Branch 0 (-215761639/1000000 : ℚ) vp0000011011000 := by
  apply branch_left_normalized (c:=vp00000110110000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-215761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-215761639/500000 : ℚ) by norm_num]
  exact coverp00000110110000
private noncomputable def ep00000110110001_0 : Blocks := edgeBlocks% "full/vectors/00000110110001-E-0000.bin"
noncomputable def ep00000110110001 : Blocks := ep00000110110001_0
private theorem idp00000110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011011000.list =
    C ((2:ℤ)^86) * horner X vp00000110110001.list + horner X ep00000110110001.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110110001 : Branch 1 (-215761639/1000000 : ℚ) vp0000011011000 := by
  apply branch_checked idp00000110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-215761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-216261639/500000 : ℚ) by norm_num]
  exact coverp00000110110001
theorem coverp0000011011000 : Covers (-215761639/1000000 : ℚ) vp0000011011000 := join_branches bp00000110110000 bp00000110110001
private noncomputable def vp000001101100_0 : Blocks := edgeBlocks% "full/vectors/000001101100-V-0000.bin"
private noncomputable def vp000001101100_1 : Blocks := edgeBlocks% "full/vectors/000001101100-V-0001.bin"
noncomputable def vp000001101100 : Blocks := (Blocks.join vp000001101100_0 vp000001101100_1)
private theorem bp0000011011000 : Branch 0 (-215761639/2000000 : ℚ) vp000001101100 := by
  apply branch_left_normalized (c:=vp0000011011000) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-215761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-215761639/1000000 : ℚ) by norm_num]
  exact coverp0000011011000
private noncomputable def ep0000011011001_0 : Blocks := edgeBlocks% "full/vectors/0000011011001-E-0000.bin"
private noncomputable def ep0000011011001_1 : Blocks := edgeBlocks% "full/vectors/0000011011001-E-0001.bin"
noncomputable def ep0000011011001 : Blocks := (Blocks.join ep0000011011001_0 ep0000011011001_1)
private theorem idp0000011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001101100.list =
    C ((2:ℤ)^155) * horner X vp0000011011001.list + horner X ep0000011011001.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011011001 : Branch 1 (-215761639/2000000 : ℚ) vp000001101100 := by
  apply branch_checked idp0000011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-215761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-216761639/1000000 : ℚ) by norm_num]
  exact coverp0000011011001
theorem coverp000001101100 : Covers (-215761639/2000000 : ℚ) vp000001101100 := join_branches bp0000011011000 bp0000011011001
private noncomputable def vp00000110110_0 : Blocks := edgeBlocks% "full/vectors/00000110110-V-0000.bin"
private noncomputable def vp00000110110_1 : Blocks := edgeBlocks% "full/vectors/00000110110-V-0001.bin"
private noncomputable def vp00000110110_2 : Blocks := edgeBlocks% "full/vectors/00000110110-V-0002.bin"
noncomputable def vp00000110110 : Blocks := (Blocks.join vp00000110110_0 (Blocks.join vp00000110110_1 vp00000110110_2))
private theorem bp000001101100 : Branch 0 (-215761639/4000000 : ℚ) vp00000110110 := by
  apply branch_left_normalized (c:=vp000001101100) (k:=0) (m:=149) (by decide +kernel)
  rw [show 2*(-215761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-215761639/2000000 : ℚ) by norm_num]
  exact coverp000001101100
private noncomputable def ep000001101101_0 : Blocks := edgeBlocks% "full/vectors/000001101101-E-0000.bin"
private noncomputable def ep000001101101_1 : Blocks := edgeBlocks% "full/vectors/000001101101-E-0001.bin"
private noncomputable def ep000001101101_2 : Blocks := edgeBlocks% "full/vectors/000001101101-E-0002.bin"
noncomputable def ep000001101101 : Blocks := (Blocks.join ep000001101101_0 (Blocks.join ep000001101101_1 ep000001101101_2))
private theorem idp000001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110110.list =
    C ((2:ℤ)^293) * horner X vp000001101101.list + horner X ep000001101101.list := by
  exact edge_identity (B := (2:ℤ)^518) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101101 : Branch 1 (-215761639/4000000 : ℚ) vp00000110110 := by
  apply branch_checked idp000001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-215761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-217761639/2000000 : ℚ) by norm_num]
  exact coverp000001101101
theorem coverp00000110110 : Covers (-215761639/4000000 : ℚ) vp00000110110 := join_branches bp000001101100 bp000001101101
private noncomputable def vp0000011011_0 : Blocks := edgeBlocks% "full/vectors/0000011011-V-0000.bin"
private noncomputable def vp0000011011_1 : Blocks := edgeBlocks% "full/vectors/0000011011-V-0001.bin"
private noncomputable def vp0000011011_2 : Blocks := edgeBlocks% "full/vectors/0000011011-V-0002.bin"
private noncomputable def vp0000011011_3 : Blocks := edgeBlocks% "full/vectors/0000011011-V-0003.bin"
private noncomputable def vp0000011011_4 : Blocks := edgeBlocks% "full/vectors/0000011011-V-0004.bin"
noncomputable def vp0000011011 : Blocks := (Blocks.join (Blocks.join vp0000011011_0 vp0000011011_1) (Blocks.join vp0000011011_2 (Blocks.join vp0000011011_3 vp0000011011_4)))
private theorem bp00000110110 : Branch 0 (-215761639/8000000 : ℚ) vp0000011011 := by
  apply branch_left_normalized (c:=vp00000110110) (k:=0) (m:=283) (by decide +kernel)
  rw [show 2*(-215761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-215761639/4000000 : ℚ) by norm_num]
  exact coverp00000110110
private noncomputable def ep00000110111_0 : Blocks := edgeBlocks% "full/vectors/00000110111-E-0000.bin"
private noncomputable def ep00000110111_1 : Blocks := edgeBlocks% "full/vectors/00000110111-E-0001.bin"
private noncomputable def ep00000110111_2 : Blocks := edgeBlocks% "full/vectors/00000110111-E-0002.bin"
private noncomputable def ep00000110111_3 : Blocks := edgeBlocks% "full/vectors/00000110111-E-0003.bin"
private noncomputable def ep00000110111_4 : Blocks := edgeBlocks% "full/vectors/00000110111-E-0004.bin"
noncomputable def ep00000110111 : Blocks := (Blocks.join (Blocks.join ep00000110111_0 ep00000110111_1) (Blocks.join ep00000110111_2 (Blocks.join ep00000110111_3 ep00000110111_4)))
private theorem idp00000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011011.list =
    C ((2:ℤ)^562) * horner X vp00000110111.list + horner X ep00000110111.list := by
  exact edge_identity (B := (2:ℤ)^924) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110111 : Branch 1 (-215761639/8000000 : ℚ) vp0000011011 := by
  apply branch_checked idp00000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-215761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-219761639/4000000 : ℚ) by norm_num]
  exact coverp00000110111
theorem coverp0000011011 : Covers (-215761639/8000000 : ℚ) vp0000011011 := join_branches bp00000110110 bp00000110111
private noncomputable def vp00000110101111_0 : Blocks := edgeBlocks% "full/vectors/00000110101111-V-0000.bin"
noncomputable def vp00000110101111 : Blocks := vp00000110101111_0
theorem coverp00000110101111 : Covers (-215261639/500000 : ℚ) vp00000110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110101110_0 : Blocks := edgeBlocks% "full/vectors/00000110101110-V-0000.bin"
noncomputable def vp00000110101110 : Blocks := vp00000110101110_0
theorem coverp00000110101110 : Covers (-214761639/500000 : ℚ) vp00000110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011010111_0 : Blocks := edgeBlocks% "full/vectors/0000011010111-V-0000.bin"
noncomputable def vp0000011010111 : Blocks := vp0000011010111_0
private theorem bp00000110101110 : Branch 0 (-214761639/1000000 : ℚ) vp0000011010111 := by
  apply branch_left_normalized (c:=vp00000110101110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-214761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-214761639/500000 : ℚ) by norm_num]
  exact coverp00000110101110
private noncomputable def ep00000110101111_0 : Blocks := edgeBlocks% "full/vectors/00000110101111-E-0000.bin"
noncomputable def ep00000110101111 : Blocks := ep00000110101111_0
private theorem idp00000110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011010111.list =
    C ((2:ℤ)^86) * horner X vp00000110101111.list + horner X ep00000110101111.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110101111 : Branch 1 (-214761639/1000000 : ℚ) vp0000011010111 := by
  apply branch_checked idp00000110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-214761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-215261639/500000 : ℚ) by norm_num]
  exact coverp00000110101111
theorem coverp0000011010111 : Covers (-214761639/1000000 : ℚ) vp0000011010111 := join_branches bp00000110101110 bp00000110101111
private noncomputable def vp00000110101101_0 : Blocks := edgeBlocks% "full/vectors/00000110101101-V-0000.bin"
noncomputable def vp00000110101101 : Blocks := vp00000110101101_0
theorem coverp00000110101101 : Covers (-214261639/500000 : ℚ) vp00000110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110101100_0 : Blocks := edgeBlocks% "full/vectors/00000110101100-V-0000.bin"
noncomputable def vp00000110101100 : Blocks := vp00000110101100_0
theorem coverp00000110101100 : Covers (-213761639/500000 : ℚ) vp00000110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011010110_0 : Blocks := edgeBlocks% "full/vectors/0000011010110-V-0000.bin"
noncomputable def vp0000011010110 : Blocks := vp0000011010110_0
private theorem bp00000110101100 : Branch 0 (-213761639/1000000 : ℚ) vp0000011010110 := by
  apply branch_left_normalized (c:=vp00000110101100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-213761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-213761639/500000 : ℚ) by norm_num]
  exact coverp00000110101100
private noncomputable def ep00000110101101_0 : Blocks := edgeBlocks% "full/vectors/00000110101101-E-0000.bin"
noncomputable def ep00000110101101 : Blocks := ep00000110101101_0
private theorem idp00000110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011010110.list =
    C ((2:ℤ)^86) * horner X vp00000110101101.list + horner X ep00000110101101.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110101101 : Branch 1 (-213761639/1000000 : ℚ) vp0000011010110 := by
  apply branch_checked idp00000110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-213761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-214261639/500000 : ℚ) by norm_num]
  exact coverp00000110101101
theorem coverp0000011010110 : Covers (-213761639/1000000 : ℚ) vp0000011010110 := join_branches bp00000110101100 bp00000110101101
private noncomputable def vp000001101011_0 : Blocks := edgeBlocks% "full/vectors/000001101011-V-0000.bin"
private noncomputable def vp000001101011_1 : Blocks := edgeBlocks% "full/vectors/000001101011-V-0001.bin"
noncomputable def vp000001101011 : Blocks := (Blocks.join vp000001101011_0 vp000001101011_1)
private theorem bp0000011010110 : Branch 0 (-213761639/2000000 : ℚ) vp000001101011 := by
  apply branch_left_normalized (c:=vp0000011010110) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-213761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-213761639/1000000 : ℚ) by norm_num]
  exact coverp0000011010110
private noncomputable def ep0000011010111_0 : Blocks := edgeBlocks% "full/vectors/0000011010111-E-0000.bin"
private noncomputable def ep0000011010111_1 : Blocks := edgeBlocks% "full/vectors/0000011010111-E-0001.bin"
noncomputable def ep0000011010111 : Blocks := (Blocks.join ep0000011010111_0 ep0000011010111_1)
private theorem idp0000011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001101011.list =
    C ((2:ℤ)^156) * horner X vp0000011010111.list + horner X ep0000011010111.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011010111 : Branch 1 (-213761639/2000000 : ℚ) vp000001101011 := by
  apply branch_checked idp0000011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-213761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-214761639/1000000 : ℚ) by norm_num]
  exact coverp0000011010111
theorem coverp000001101011 : Covers (-213761639/2000000 : ℚ) vp000001101011 := join_branches bp0000011010110 bp0000011010111
private noncomputable def vp00000110101011_0 : Blocks := edgeBlocks% "full/vectors/00000110101011-V-0000.bin"
noncomputable def vp00000110101011 : Blocks := vp00000110101011_0
theorem coverp00000110101011 : Covers (-213261639/500000 : ℚ) vp00000110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110101010_0 : Blocks := edgeBlocks% "full/vectors/00000110101010-V-0000.bin"
noncomputable def vp00000110101010 : Blocks := vp00000110101010_0
theorem coverp00000110101010 : Covers (-212761639/500000 : ℚ) vp00000110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011010101_0 : Blocks := edgeBlocks% "full/vectors/0000011010101-V-0000.bin"
noncomputable def vp0000011010101 : Blocks := vp0000011010101_0
private theorem bp00000110101010 : Branch 0 (-212761639/1000000 : ℚ) vp0000011010101 := by
  apply branch_left_normalized (c:=vp00000110101010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-212761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-212761639/500000 : ℚ) by norm_num]
  exact coverp00000110101010
private noncomputable def ep00000110101011_0 : Blocks := edgeBlocks% "full/vectors/00000110101011-E-0000.bin"
noncomputable def ep00000110101011 : Blocks := ep00000110101011_0
private theorem idp00000110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011010101.list =
    C ((2:ℤ)^85) * horner X vp00000110101011.list + horner X ep00000110101011.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110101011 : Branch 1 (-212761639/1000000 : ℚ) vp0000011010101 := by
  apply branch_checked idp00000110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-212761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-213261639/500000 : ℚ) by norm_num]
  exact coverp00000110101011
theorem coverp0000011010101 : Covers (-212761639/1000000 : ℚ) vp0000011010101 := join_branches bp00000110101010 bp00000110101011
private noncomputable def vp00000110101001_0 : Blocks := edgeBlocks% "full/vectors/00000110101001-V-0000.bin"
noncomputable def vp00000110101001 : Blocks := vp00000110101001_0
theorem coverp00000110101001 : Covers (-212261639/500000 : ℚ) vp00000110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110101000_0 : Blocks := edgeBlocks% "full/vectors/00000110101000-V-0000.bin"
noncomputable def vp00000110101000 : Blocks := vp00000110101000_0
theorem coverp00000110101000 : Covers (-211761639/500000 : ℚ) vp00000110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011010100_0 : Blocks := edgeBlocks% "full/vectors/0000011010100-V-0000.bin"
noncomputable def vp0000011010100 : Blocks := vp0000011010100_0
private theorem bp00000110101000 : Branch 0 (-211761639/1000000 : ℚ) vp0000011010100 := by
  apply branch_left_normalized (c:=vp00000110101000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-211761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-211761639/500000 : ℚ) by norm_num]
  exact coverp00000110101000
private noncomputable def ep00000110101001_0 : Blocks := edgeBlocks% "full/vectors/00000110101001-E-0000.bin"
noncomputable def ep00000110101001 : Blocks := ep00000110101001_0
private theorem idp00000110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011010100.list =
    C ((2:ℤ)^86) * horner X vp00000110101001.list + horner X ep00000110101001.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110101001 : Branch 1 (-211761639/1000000 : ℚ) vp0000011010100 := by
  apply branch_checked idp00000110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-211761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-212261639/500000 : ℚ) by norm_num]
  exact coverp00000110101001
theorem coverp0000011010100 : Covers (-211761639/1000000 : ℚ) vp0000011010100 := join_branches bp00000110101000 bp00000110101001
private noncomputable def vp000001101010_0 : Blocks := edgeBlocks% "full/vectors/000001101010-V-0000.bin"
private noncomputable def vp000001101010_1 : Blocks := edgeBlocks% "full/vectors/000001101010-V-0001.bin"
noncomputable def vp000001101010 : Blocks := (Blocks.join vp000001101010_0 vp000001101010_1)
private theorem bp0000011010100 : Branch 0 (-211761639/2000000 : ℚ) vp000001101010 := by
  apply branch_left_normalized (c:=vp0000011010100) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-211761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-211761639/1000000 : ℚ) by norm_num]
  exact coverp0000011010100
private noncomputable def ep0000011010101_0 : Blocks := edgeBlocks% "full/vectors/0000011010101-E-0000.bin"
private noncomputable def ep0000011010101_1 : Blocks := edgeBlocks% "full/vectors/0000011010101-E-0001.bin"
noncomputable def ep0000011010101 : Blocks := (Blocks.join ep0000011010101_0 ep0000011010101_1)
private theorem idp0000011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001101010.list =
    C ((2:ℤ)^156) * horner X vp0000011010101.list + horner X ep0000011010101.list := by
  exact edge_identity (B := (2:ℤ)^312) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011010101 : Branch 1 (-211761639/2000000 : ℚ) vp000001101010 := by
  apply branch_checked idp0000011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-211761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-212761639/1000000 : ℚ) by norm_num]
  exact coverp0000011010101
theorem coverp000001101010 : Covers (-211761639/2000000 : ℚ) vp000001101010 := join_branches bp0000011010100 bp0000011010101
private noncomputable def vp00000110101_0 : Blocks := edgeBlocks% "full/vectors/00000110101-V-0000.bin"
private noncomputable def vp00000110101_1 : Blocks := edgeBlocks% "full/vectors/00000110101-V-0001.bin"
private noncomputable def vp00000110101_2 : Blocks := edgeBlocks% "full/vectors/00000110101-V-0002.bin"
noncomputable def vp00000110101 : Blocks := (Blocks.join vp00000110101_0 (Blocks.join vp00000110101_1 vp00000110101_2))
private theorem bp000001101010 : Branch 0 (-211761639/4000000 : ℚ) vp00000110101 := by
  apply branch_left_normalized (c:=vp000001101010) (k:=0) (m:=149) (by decide +kernel)
  rw [show 2*(-211761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-211761639/2000000 : ℚ) by norm_num]
  exact coverp000001101010
private noncomputable def ep000001101011_0 : Blocks := edgeBlocks% "full/vectors/000001101011-E-0000.bin"
private noncomputable def ep000001101011_1 : Blocks := edgeBlocks% "full/vectors/000001101011-E-0001.bin"
private noncomputable def ep000001101011_2 : Blocks := edgeBlocks% "full/vectors/000001101011-E-0002.bin"
noncomputable def ep000001101011 : Blocks := (Blocks.join ep000001101011_0 (Blocks.join ep000001101011_1 ep000001101011_2))
private theorem idp000001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110101.list =
    C ((2:ℤ)^296) * horner X vp000001101011.list + horner X ep000001101011.list := by
  exact edge_identity (B := (2:ℤ)^518) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101011 : Branch 1 (-211761639/4000000 : ℚ) vp00000110101 := by
  apply branch_checked idp000001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-211761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-213761639/2000000 : ℚ) by norm_num]
  exact coverp000001101011
theorem coverp00000110101 : Covers (-211761639/4000000 : ℚ) vp00000110101 := join_branches bp000001101010 bp000001101011
private noncomputable def vp00000110100111_0 : Blocks := edgeBlocks% "full/vectors/00000110100111-V-0000.bin"
noncomputable def vp00000110100111 : Blocks := vp00000110100111_0
theorem coverp00000110100111 : Covers (-211261639/500000 : ℚ) vp00000110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110100110_0 : Blocks := edgeBlocks% "full/vectors/00000110100110-V-0000.bin"
noncomputable def vp00000110100110 : Blocks := vp00000110100110_0
theorem coverp00000110100110 : Covers (-210761639/500000 : ℚ) vp00000110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011010011_0 : Blocks := edgeBlocks% "full/vectors/0000011010011-V-0000.bin"
noncomputable def vp0000011010011 : Blocks := vp0000011010011_0
private theorem bp00000110100110 : Branch 0 (-210761639/1000000 : ℚ) vp0000011010011 := by
  apply branch_left_normalized (c:=vp00000110100110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-210761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-210761639/500000 : ℚ) by norm_num]
  exact coverp00000110100110
private noncomputable def ep00000110100111_0 : Blocks := edgeBlocks% "full/vectors/00000110100111-E-0000.bin"
noncomputable def ep00000110100111 : Blocks := ep00000110100111_0
private theorem idp00000110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011010011.list =
    C ((2:ℤ)^85) * horner X vp00000110100111.list + horner X ep00000110100111.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110100111 : Branch 1 (-210761639/1000000 : ℚ) vp0000011010011 := by
  apply branch_checked idp00000110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-210761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-211261639/500000 : ℚ) by norm_num]
  exact coverp00000110100111
theorem coverp0000011010011 : Covers (-210761639/1000000 : ℚ) vp0000011010011 := join_branches bp00000110100110 bp00000110100111
private noncomputable def vp00000110100101_0 : Blocks := edgeBlocks% "full/vectors/00000110100101-V-0000.bin"
noncomputable def vp00000110100101 : Blocks := vp00000110100101_0
theorem coverp00000110100101 : Covers (-210261639/500000 : ℚ) vp00000110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110100100_0 : Blocks := edgeBlocks% "full/vectors/00000110100100-V-0000.bin"
noncomputable def vp00000110100100 : Blocks := vp00000110100100_0
theorem coverp00000110100100 : Covers (-209761639/500000 : ℚ) vp00000110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011010010_0 : Blocks := edgeBlocks% "full/vectors/0000011010010-V-0000.bin"
noncomputable def vp0000011010010 : Blocks := vp0000011010010_0
private theorem bp00000110100100 : Branch 0 (-209761639/1000000 : ℚ) vp0000011010010 := by
  apply branch_left_normalized (c:=vp00000110100100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-209761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-209761639/500000 : ℚ) by norm_num]
  exact coverp00000110100100
private noncomputable def ep00000110100101_0 : Blocks := edgeBlocks% "full/vectors/00000110100101-E-0000.bin"
noncomputable def ep00000110100101 : Blocks := ep00000110100101_0
private theorem idp00000110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011010010.list =
    C ((2:ℤ)^86) * horner X vp00000110100101.list + horner X ep00000110100101.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110100101 : Branch 1 (-209761639/1000000 : ℚ) vp0000011010010 := by
  apply branch_checked idp00000110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-209761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-210261639/500000 : ℚ) by norm_num]
  exact coverp00000110100101
theorem coverp0000011010010 : Covers (-209761639/1000000 : ℚ) vp0000011010010 := join_branches bp00000110100100 bp00000110100101
private noncomputable def vp000001101001_0 : Blocks := edgeBlocks% "full/vectors/000001101001-V-0000.bin"
private noncomputable def vp000001101001_1 : Blocks := edgeBlocks% "full/vectors/000001101001-V-0001.bin"
noncomputable def vp000001101001 : Blocks := (Blocks.join vp000001101001_0 vp000001101001_1)
private theorem bp0000011010010 : Branch 0 (-209761639/2000000 : ℚ) vp000001101001 := by
  apply branch_left_normalized (c:=vp0000011010010) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-209761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-209761639/1000000 : ℚ) by norm_num]
  exact coverp0000011010010
private noncomputable def ep0000011010011_0 : Blocks := edgeBlocks% "full/vectors/0000011010011-E-0000.bin"
private noncomputable def ep0000011010011_1 : Blocks := edgeBlocks% "full/vectors/0000011010011-E-0001.bin"
noncomputable def ep0000011010011 : Blocks := (Blocks.join ep0000011010011_0 ep0000011010011_1)
private theorem idp0000011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001101001.list =
    C ((2:ℤ)^157) * horner X vp0000011010011.list + horner X ep0000011010011.list := by
  exact edge_identity (B := (2:ℤ)^312) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011010011 : Branch 1 (-209761639/2000000 : ℚ) vp000001101001 := by
  apply branch_checked idp0000011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-209761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-210761639/1000000 : ℚ) by norm_num]
  exact coverp0000011010011
theorem coverp000001101001 : Covers (-209761639/2000000 : ℚ) vp000001101001 := join_branches bp0000011010010 bp0000011010011
private noncomputable def vp00000110100011_0 : Blocks := edgeBlocks% "full/vectors/00000110100011-V-0000.bin"
noncomputable def vp00000110100011 : Blocks := vp00000110100011_0
theorem coverp00000110100011 : Covers (-209261639/500000 : ℚ) vp00000110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110100010_0 : Blocks := edgeBlocks% "full/vectors/00000110100010-V-0000.bin"
noncomputable def vp00000110100010 : Blocks := vp00000110100010_0
theorem coverp00000110100010 : Covers (-208761639/500000 : ℚ) vp00000110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011010001_0 : Blocks := edgeBlocks% "full/vectors/0000011010001-V-0000.bin"
noncomputable def vp0000011010001 : Blocks := vp0000011010001_0
private theorem bp00000110100010 : Branch 0 (-208761639/1000000 : ℚ) vp0000011010001 := by
  apply branch_left_normalized (c:=vp00000110100010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-208761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-208761639/500000 : ℚ) by norm_num]
  exact coverp00000110100010
private noncomputable def ep00000110100011_0 : Blocks := edgeBlocks% "full/vectors/00000110100011-E-0000.bin"
noncomputable def ep00000110100011 : Blocks := ep00000110100011_0
private theorem idp00000110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011010001.list =
    C ((2:ℤ)^86) * horner X vp00000110100011.list + horner X ep00000110100011.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110100011 : Branch 1 (-208761639/1000000 : ℚ) vp0000011010001 := by
  apply branch_checked idp00000110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-208761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-209261639/500000 : ℚ) by norm_num]
  exact coverp00000110100011
theorem coverp0000011010001 : Covers (-208761639/1000000 : ℚ) vp0000011010001 := join_branches bp00000110100010 bp00000110100011
private noncomputable def vp00000110100001_0 : Blocks := edgeBlocks% "full/vectors/00000110100001-V-0000.bin"
noncomputable def vp00000110100001 : Blocks := vp00000110100001_0
theorem coverp00000110100001 : Covers (-208261639/500000 : ℚ) vp00000110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110100000_0 : Blocks := edgeBlocks% "full/vectors/00000110100000-V-0000.bin"
noncomputable def vp00000110100000 : Blocks := vp00000110100000_0
theorem coverp00000110100000 : Covers (-207761639/500000 : ℚ) vp00000110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011010000_0 : Blocks := edgeBlocks% "full/vectors/0000011010000-V-0000.bin"
noncomputable def vp0000011010000 : Blocks := vp0000011010000_0
private theorem bp00000110100000 : Branch 0 (-207761639/1000000 : ℚ) vp0000011010000 := by
  apply branch_left_normalized (c:=vp00000110100000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-207761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-207761639/500000 : ℚ) by norm_num]
  exact coverp00000110100000
private noncomputable def ep00000110100001_0 : Blocks := edgeBlocks% "full/vectors/00000110100001-E-0000.bin"
noncomputable def ep00000110100001 : Blocks := ep00000110100001_0
private theorem idp00000110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011010000.list =
    C ((2:ℤ)^87) * horner X vp00000110100001.list + horner X ep00000110100001.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110100001 : Branch 1 (-207761639/1000000 : ℚ) vp0000011010000 := by
  apply branch_checked idp00000110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-207761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-208261639/500000 : ℚ) by norm_num]
  exact coverp00000110100001
theorem coverp0000011010000 : Covers (-207761639/1000000 : ℚ) vp0000011010000 := join_branches bp00000110100000 bp00000110100001
private noncomputable def vp000001101000_0 : Blocks := edgeBlocks% "full/vectors/000001101000-V-0000.bin"
private noncomputable def vp000001101000_1 : Blocks := edgeBlocks% "full/vectors/000001101000-V-0001.bin"
noncomputable def vp000001101000 : Blocks := (Blocks.join vp000001101000_0 vp000001101000_1)
private theorem bp0000011010000 : Branch 0 (-207761639/2000000 : ℚ) vp000001101000 := by
  apply branch_left_normalized (c:=vp0000011010000) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-207761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-207761639/1000000 : ℚ) by norm_num]
  exact coverp0000011010000
private noncomputable def ep0000011010001_0 : Blocks := edgeBlocks% "full/vectors/0000011010001-E-0000.bin"
private noncomputable def ep0000011010001_1 : Blocks := edgeBlocks% "full/vectors/0000011010001-E-0001.bin"
noncomputable def ep0000011010001 : Blocks := (Blocks.join ep0000011010001_0 ep0000011010001_1)
private theorem idp0000011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001101000.list =
    C ((2:ℤ)^158) * horner X vp0000011010001.list + horner X ep0000011010001.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011010001 : Branch 1 (-207761639/2000000 : ℚ) vp000001101000 := by
  apply branch_checked idp0000011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-207761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-208761639/1000000 : ℚ) by norm_num]
  exact coverp0000011010001
theorem coverp000001101000 : Covers (-207761639/2000000 : ℚ) vp000001101000 := join_branches bp0000011010000 bp0000011010001
private noncomputable def vp00000110100_0 : Blocks := edgeBlocks% "full/vectors/00000110100-V-0000.bin"
private noncomputable def vp00000110100_1 : Blocks := edgeBlocks% "full/vectors/00000110100-V-0001.bin"
private noncomputable def vp00000110100_2 : Blocks := edgeBlocks% "full/vectors/00000110100-V-0002.bin"
noncomputable def vp00000110100 : Blocks := (Blocks.join vp00000110100_0 (Blocks.join vp00000110100_1 vp00000110100_2))
private theorem bp000001101000 : Branch 0 (-207761639/4000000 : ℚ) vp00000110100 := by
  apply branch_left_normalized (c:=vp000001101000) (k:=0) (m:=151) (by decide +kernel)
  rw [show 2*(-207761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-207761639/2000000 : ℚ) by norm_num]
  exact coverp000001101000
private noncomputable def ep000001101001_0 : Blocks := edgeBlocks% "full/vectors/000001101001-E-0000.bin"
private noncomputable def ep000001101001_1 : Blocks := edgeBlocks% "full/vectors/000001101001-E-0001.bin"
private noncomputable def ep000001101001_2 : Blocks := edgeBlocks% "full/vectors/000001101001-E-0002.bin"
noncomputable def ep000001101001 : Blocks := (Blocks.join ep000001101001_0 (Blocks.join ep000001101001_1 ep000001101001_2))
private theorem idp000001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110100.list =
    C ((2:ℤ)^300) * horner X vp000001101001.list + horner X ep000001101001.list := by
  exact edge_identity (B := (2:ℤ)^522) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101001 : Branch 1 (-207761639/4000000 : ℚ) vp00000110100 := by
  apply branch_checked idp000001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-207761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-209761639/2000000 : ℚ) by norm_num]
  exact coverp000001101001
theorem coverp00000110100 : Covers (-207761639/4000000 : ℚ) vp00000110100 := join_branches bp000001101000 bp000001101001
private noncomputable def vp0000011010_0 : Blocks := edgeBlocks% "full/vectors/0000011010-V-0000.bin"
private noncomputable def vp0000011010_1 : Blocks := edgeBlocks% "full/vectors/0000011010-V-0001.bin"
private noncomputable def vp0000011010_2 : Blocks := edgeBlocks% "full/vectors/0000011010-V-0002.bin"
private noncomputable def vp0000011010_3 : Blocks := edgeBlocks% "full/vectors/0000011010-V-0003.bin"
private noncomputable def vp0000011010_4 : Blocks := edgeBlocks% "full/vectors/0000011010-V-0004.bin"
noncomputable def vp0000011010 : Blocks := (Blocks.join (Blocks.join vp0000011010_0 vp0000011010_1) (Blocks.join vp0000011010_2 (Blocks.join vp0000011010_3 vp0000011010_4)))
private theorem bp00000110100 : Branch 0 (-207761639/8000000 : ℚ) vp0000011010 := by
  apply branch_left_normalized (c:=vp00000110100) (k:=0) (m:=287) (by decide +kernel)
  rw [show 2*(-207761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-207761639/4000000 : ℚ) by norm_num]
  exact coverp00000110100
private noncomputable def ep00000110101_0 : Blocks := edgeBlocks% "full/vectors/00000110101-E-0000.bin"
private noncomputable def ep00000110101_1 : Blocks := edgeBlocks% "full/vectors/00000110101-E-0001.bin"
private noncomputable def ep00000110101_2 : Blocks := edgeBlocks% "full/vectors/00000110101-E-0002.bin"
private noncomputable def ep00000110101_3 : Blocks := edgeBlocks% "full/vectors/00000110101-E-0003.bin"
private noncomputable def ep00000110101_4 : Blocks := edgeBlocks% "full/vectors/00000110101-E-0004.bin"
noncomputable def ep00000110101 : Blocks := (Blocks.join (Blocks.join ep00000110101_0 ep00000110101_1) (Blocks.join ep00000110101_2 (Blocks.join ep00000110101_3 ep00000110101_4)))
private theorem idp00000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011010.list =
    C ((2:ℤ)^580) * horner X vp00000110101.list + horner X ep00000110101.list := by
  exact edge_identity (B := (2:ℤ)^936) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110101 : Branch 1 (-207761639/8000000 : ℚ) vp0000011010 := by
  apply branch_checked idp00000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-207761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-211761639/4000000 : ℚ) by norm_num]
  exact coverp00000110101
theorem coverp0000011010 : Covers (-207761639/8000000 : ℚ) vp0000011010 := join_branches bp00000110100 bp00000110101
private noncomputable def vp000001101_0 : Blocks := edgeBlocks% "full/vectors/000001101-V-0000.bin"
private noncomputable def vp000001101_1 : Blocks := edgeBlocks% "full/vectors/000001101-V-0001.bin"
private noncomputable def vp000001101_2 : Blocks := edgeBlocks% "full/vectors/000001101-V-0002.bin"
private noncomputable def vp000001101_3 : Blocks := edgeBlocks% "full/vectors/000001101-V-0003.bin"
private noncomputable def vp000001101_4 : Blocks := edgeBlocks% "full/vectors/000001101-V-0004.bin"
private noncomputable def vp000001101_5 : Blocks := edgeBlocks% "full/vectors/000001101-V-0005.bin"
private noncomputable def vp000001101_6 : Blocks := edgeBlocks% "full/vectors/000001101-V-0006.bin"
private noncomputable def vp000001101_7 : Blocks := edgeBlocks% "full/vectors/000001101-V-0007.bin"
private noncomputable def vp000001101_8 : Blocks := edgeBlocks% "full/vectors/000001101-V-0008.bin"
noncomputable def vp000001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000001101_0 vp000001101_1) (Blocks.join vp000001101_2 vp000001101_3)) (Blocks.join (Blocks.join vp000001101_4 vp000001101_5) (Blocks.join vp000001101_6 (Blocks.join vp000001101_7 vp000001101_8))))
private theorem bp0000011010 : Branch 0 (-207761639/16000000 : ℚ) vp000001101 := by
  apply branch_left_normalized (c:=vp0000011010) (k:=0) (m:=556) (by decide +kernel)
  rw [show 2*(-207761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-207761639/8000000 : ℚ) by norm_num]
  exact coverp0000011010
private noncomputable def ep0000011011_0 : Blocks := edgeBlocks% "full/vectors/0000011011-E-0000.bin"
private noncomputable def ep0000011011_1 : Blocks := edgeBlocks% "full/vectors/0000011011-E-0001.bin"
private noncomputable def ep0000011011_2 : Blocks := edgeBlocks% "full/vectors/0000011011-E-0002.bin"
private noncomputable def ep0000011011_3 : Blocks := edgeBlocks% "full/vectors/0000011011-E-0003.bin"
private noncomputable def ep0000011011_4 : Blocks := edgeBlocks% "full/vectors/0000011011-E-0004.bin"
private noncomputable def ep0000011011_5 : Blocks := edgeBlocks% "full/vectors/0000011011-E-0005.bin"
private noncomputable def ep0000011011_6 : Blocks := edgeBlocks% "full/vectors/0000011011-E-0006.bin"
private noncomputable def ep0000011011_7 : Blocks := edgeBlocks% "full/vectors/0000011011-E-0007.bin"
private noncomputable def ep0000011011_8 : Blocks := edgeBlocks% "full/vectors/0000011011-E-0008.bin"
noncomputable def ep0000011011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000011011_0 ep0000011011_1) (Blocks.join ep0000011011_2 ep0000011011_3)) (Blocks.join (Blocks.join ep0000011011_4 ep0000011011_5) (Blocks.join ep0000011011_6 (Blocks.join ep0000011011_7 ep0000011011_8))))
private theorem idp0000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001101.list =
    C ((2:ℤ)^1133) * horner X vp0000011011.list + horner X ep0000011011.list := by
  exact edge_identity (B := (2:ℤ)^1755) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011011 : Branch 1 (-207761639/16000000 : ℚ) vp000001101 := by
  apply branch_checked idp0000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-207761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-215761639/8000000 : ℚ) by norm_num]
  exact coverp0000011011
theorem coverp000001101 : Covers (-207761639/16000000 : ℚ) vp000001101 := join_branches bp0000011010 bp0000011011
end NextProof.EdgeFull

