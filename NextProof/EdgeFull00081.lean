import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0001111111111_0 : Blocks := edgeBlocks% "full/vectors/0001111111111-V-0000.bin"
noncomputable def vp0001111111111 : Blocks := vp0001111111111_0
theorem coverp0001111111111 : Covers (-1022761639/1000000 : ℚ) vp0001111111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111111110_0 : Blocks := edgeBlocks% "full/vectors/0001111111110-V-0000.bin"
noncomputable def vp0001111111110 : Blocks := vp0001111111110_0
theorem coverp0001111111110 : Covers (-1021761639/1000000 : ℚ) vp0001111111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111111111_0 : Blocks := edgeBlocks% "full/vectors/000111111111-V-0000.bin"
noncomputable def vp000111111111 : Blocks := vp000111111111_0
private theorem bp0001111111110 : Branch 0 (-1021761639/2000000 : ℚ) vp000111111111 := by
  apply branch_left_normalized (c:=vp0001111111110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1021761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1021761639/1000000 : ℚ) by norm_num]
  exact coverp0001111111110
private noncomputable def ep0001111111111_0 : Blocks := edgeBlocks% "full/vectors/0001111111111-E-0000.bin"
noncomputable def ep0001111111111 : Blocks := ep0001111111111_0
private theorem idp0001111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111111111.list =
    C ((2:ℤ)^87) * horner X vp0001111111111.list + horner X ep0001111111111.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111111111 : Branch 1 (-1021761639/2000000 : ℚ) vp000111111111 := by
  apply branch_checked idp0001111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1021761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1022761639/1000000 : ℚ) by norm_num]
  exact coverp0001111111111
theorem coverp000111111111 : Covers (-1021761639/2000000 : ℚ) vp000111111111 := join_branches bp0001111111110 bp0001111111111
private noncomputable def vp0001111111101_0 : Blocks := edgeBlocks% "full/vectors/0001111111101-V-0000.bin"
noncomputable def vp0001111111101 : Blocks := vp0001111111101_0
theorem coverp0001111111101 : Covers (-1020761639/1000000 : ℚ) vp0001111111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111111100_0 : Blocks := edgeBlocks% "full/vectors/0001111111100-V-0000.bin"
noncomputable def vp0001111111100 : Blocks := vp0001111111100_0
theorem coverp0001111111100 : Covers (-1019761639/1000000 : ℚ) vp0001111111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111111110_0 : Blocks := edgeBlocks% "full/vectors/000111111110-V-0000.bin"
noncomputable def vp000111111110 : Blocks := vp000111111110_0
private theorem bp0001111111100 : Branch 0 (-1019761639/2000000 : ℚ) vp000111111110 := by
  apply branch_left_normalized (c:=vp0001111111100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1019761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1019761639/1000000 : ℚ) by norm_num]
  exact coverp0001111111100
private noncomputable def ep0001111111101_0 : Blocks := edgeBlocks% "full/vectors/0001111111101-E-0000.bin"
noncomputable def ep0001111111101 : Blocks := ep0001111111101_0
private theorem idp0001111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111111110.list =
    C ((2:ℤ)^91) * horner X vp0001111111101.list + horner X ep0001111111101.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111111101 : Branch 1 (-1019761639/2000000 : ℚ) vp000111111110 := by
  apply branch_checked idp0001111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1019761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1020761639/1000000 : ℚ) by norm_num]
  exact coverp0001111111101
theorem coverp000111111110 : Covers (-1019761639/2000000 : ℚ) vp000111111110 := join_branches bp0001111111100 bp0001111111101
private noncomputable def vp00011111111_0 : Blocks := edgeBlocks% "full/vectors/00011111111-V-0000.bin"
private noncomputable def vp00011111111_1 : Blocks := edgeBlocks% "full/vectors/00011111111-V-0001.bin"
noncomputable def vp00011111111 : Blocks := (Blocks.join vp00011111111_0 vp00011111111_1)
private theorem bp000111111110 : Branch 0 (-1019761639/4000000 : ℚ) vp00011111111 := by
  apply branch_left_normalized (c:=vp000111111110) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-1019761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1019761639/2000000 : ℚ) by norm_num]
  exact coverp000111111110
private noncomputable def ep000111111111_0 : Blocks := edgeBlocks% "full/vectors/000111111111-E-0000.bin"
private noncomputable def ep000111111111_1 : Blocks := edgeBlocks% "full/vectors/000111111111-E-0001.bin"
noncomputable def ep000111111111 : Blocks := (Blocks.join ep000111111111_0 ep000111111111_1)
private theorem idp000111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011111111.list =
    C ((2:ℤ)^160) * horner X vp000111111111.list + horner X ep000111111111.list := by
  exact edge_identity (B := (2:ℤ)^309) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111111111 : Branch 1 (-1019761639/4000000 : ℚ) vp00011111111 := by
  apply branch_checked idp000111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1019761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1021761639/2000000 : ℚ) by norm_num]
  exact coverp000111111111
theorem coverp00011111111 : Covers (-1019761639/4000000 : ℚ) vp00011111111 := join_branches bp000111111110 bp000111111111
private noncomputable def vp0001111111011_0 : Blocks := edgeBlocks% "full/vectors/0001111111011-V-0000.bin"
noncomputable def vp0001111111011 : Blocks := vp0001111111011_0
theorem coverp0001111111011 : Covers (-1018761639/1000000 : ℚ) vp0001111111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111111010_0 : Blocks := edgeBlocks% "full/vectors/0001111111010-V-0000.bin"
noncomputable def vp0001111111010 : Blocks := vp0001111111010_0
theorem coverp0001111111010 : Covers (-1017761639/1000000 : ℚ) vp0001111111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111111101_0 : Blocks := edgeBlocks% "full/vectors/000111111101-V-0000.bin"
noncomputable def vp000111111101 : Blocks := vp000111111101_0
private theorem bp0001111111010 : Branch 0 (-1017761639/2000000 : ℚ) vp000111111101 := by
  apply branch_left_normalized (c:=vp0001111111010) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1017761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1017761639/1000000 : ℚ) by norm_num]
  exact coverp0001111111010
private noncomputable def ep0001111111011_0 : Blocks := edgeBlocks% "full/vectors/0001111111011-E-0000.bin"
noncomputable def ep0001111111011 : Blocks := ep0001111111011_0
private theorem idp0001111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111111101.list =
    C ((2:ℤ)^84) * horner X vp0001111111011.list + horner X ep0001111111011.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111111011 : Branch 1 (-1017761639/2000000 : ℚ) vp000111111101 := by
  apply branch_checked idp0001111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1017761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1018761639/1000000 : ℚ) by norm_num]
  exact coverp0001111111011
theorem coverp000111111101 : Covers (-1017761639/2000000 : ℚ) vp000111111101 := join_branches bp0001111111010 bp0001111111011
private noncomputable def vp0001111111001_0 : Blocks := edgeBlocks% "full/vectors/0001111111001-V-0000.bin"
noncomputable def vp0001111111001 : Blocks := vp0001111111001_0
theorem coverp0001111111001 : Covers (-1016761639/1000000 : ℚ) vp0001111111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111111000_0 : Blocks := edgeBlocks% "full/vectors/0001111111000-V-0000.bin"
noncomputable def vp0001111111000 : Blocks := vp0001111111000_0
theorem coverp0001111111000 : Covers (-1015761639/1000000 : ℚ) vp0001111111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111111100_0 : Blocks := edgeBlocks% "full/vectors/000111111100-V-0000.bin"
noncomputable def vp000111111100 : Blocks := vp000111111100_0
private theorem bp0001111111000 : Branch 0 (-1015761639/2000000 : ℚ) vp000111111100 := by
  apply branch_left_normalized (c:=vp0001111111000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1015761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1015761639/1000000 : ℚ) by norm_num]
  exact coverp0001111111000
private noncomputable def ep0001111111001_0 : Blocks := edgeBlocks% "full/vectors/0001111111001-E-0000.bin"
noncomputable def ep0001111111001 : Blocks := ep0001111111001_0
private theorem idp0001111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111111100.list =
    C ((2:ℤ)^86) * horner X vp0001111111001.list + horner X ep0001111111001.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111111001 : Branch 1 (-1015761639/2000000 : ℚ) vp000111111100 := by
  apply branch_checked idp0001111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1015761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1016761639/1000000 : ℚ) by norm_num]
  exact coverp0001111111001
theorem coverp000111111100 : Covers (-1015761639/2000000 : ℚ) vp000111111100 := join_branches bp0001111111000 bp0001111111001
private noncomputable def vp00011111110_0 : Blocks := edgeBlocks% "full/vectors/00011111110-V-0000.bin"
private noncomputable def vp00011111110_1 : Blocks := edgeBlocks% "full/vectors/00011111110-V-0001.bin"
noncomputable def vp00011111110 : Blocks := (Blocks.join vp00011111110_0 vp00011111110_1)
private theorem bp000111111100 : Branch 0 (-1015761639/4000000 : ℚ) vp00011111110 := by
  apply branch_left_normalized (c:=vp000111111100) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-1015761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1015761639/2000000 : ℚ) by norm_num]
  exact coverp000111111100
private noncomputable def ep000111111101_0 : Blocks := edgeBlocks% "full/vectors/000111111101-E-0000.bin"
private noncomputable def ep000111111101_1 : Blocks := edgeBlocks% "full/vectors/000111111101-E-0001.bin"
noncomputable def ep000111111101 : Blocks := (Blocks.join ep000111111101_0 ep000111111101_1)
private theorem idp000111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011111110.list =
    C ((2:ℤ)^153) * horner X vp000111111101.list + horner X ep000111111101.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111111101 : Branch 1 (-1015761639/4000000 : ℚ) vp00011111110 := by
  apply branch_checked idp000111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1015761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1017761639/2000000 : ℚ) by norm_num]
  exact coverp000111111101
theorem coverp00011111110 : Covers (-1015761639/4000000 : ℚ) vp00011111110 := join_branches bp000111111100 bp000111111101
private noncomputable def vp0001111111_0 : Blocks := edgeBlocks% "full/vectors/0001111111-V-0000.bin"
private noncomputable def vp0001111111_1 : Blocks := edgeBlocks% "full/vectors/0001111111-V-0001.bin"
private noncomputable def vp0001111111_2 : Blocks := edgeBlocks% "full/vectors/0001111111-V-0002.bin"
noncomputable def vp0001111111 : Blocks := (Blocks.join vp0001111111_0 (Blocks.join vp0001111111_1 vp0001111111_2))
private theorem bp00011111110 : Branch 0 (-1015761639/8000000 : ℚ) vp0001111111 := by
  apply branch_left_normalized (c:=vp00011111110) (k:=0) (m:=142) (by decide +kernel)
  rw [show 2*(-1015761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1015761639/4000000 : ℚ) by norm_num]
  exact coverp00011111110
private noncomputable def ep00011111111_0 : Blocks := edgeBlocks% "full/vectors/00011111111-E-0000.bin"
private noncomputable def ep00011111111_1 : Blocks := edgeBlocks% "full/vectors/00011111111-E-0001.bin"
private noncomputable def ep00011111111_2 : Blocks := edgeBlocks% "full/vectors/00011111111-E-0002.bin"
noncomputable def ep00011111111 : Blocks := (Blocks.join ep00011111111_0 (Blocks.join ep00011111111_1 ep00011111111_2))
private theorem idp00011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001111111.list =
    C ((2:ℤ)^286) * horner X vp00011111111.list + horner X ep00011111111.list := by
  exact edge_identity (B := (2:ℤ)^493) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011111111 : Branch 1 (-1015761639/8000000 : ℚ) vp0001111111 := by
  apply branch_checked idp00011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1015761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1019761639/4000000 : ℚ) by norm_num]
  exact coverp00011111111
theorem coverp0001111111 : Covers (-1015761639/8000000 : ℚ) vp0001111111 := join_branches bp00011111110 bp00011111111
private noncomputable def vp0001111110111_0 : Blocks := edgeBlocks% "full/vectors/0001111110111-V-0000.bin"
noncomputable def vp0001111110111 : Blocks := vp0001111110111_0
theorem coverp0001111110111 : Covers (-1014761639/1000000 : ℚ) vp0001111110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111110110_0 : Blocks := edgeBlocks% "full/vectors/0001111110110-V-0000.bin"
noncomputable def vp0001111110110 : Blocks := vp0001111110110_0
theorem coverp0001111110110 : Covers (-1013761639/1000000 : ℚ) vp0001111110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111111011_0 : Blocks := edgeBlocks% "full/vectors/000111111011-V-0000.bin"
noncomputable def vp000111111011 : Blocks := vp000111111011_0
private theorem bp0001111110110 : Branch 0 (-1013761639/2000000 : ℚ) vp000111111011 := by
  apply branch_left_normalized (c:=vp0001111110110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1013761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1013761639/1000000 : ℚ) by norm_num]
  exact coverp0001111110110
private noncomputable def ep0001111110111_0 : Blocks := edgeBlocks% "full/vectors/0001111110111-E-0000.bin"
noncomputable def ep0001111110111 : Blocks := ep0001111110111_0
private theorem idp0001111110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111111011.list =
    C ((2:ℤ)^87) * horner X vp0001111110111.list + horner X ep0001111110111.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111110111 : Branch 1 (-1013761639/2000000 : ℚ) vp000111111011 := by
  apply branch_checked idp0001111110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1013761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1014761639/1000000 : ℚ) by norm_num]
  exact coverp0001111110111
theorem coverp000111111011 : Covers (-1013761639/2000000 : ℚ) vp000111111011 := join_branches bp0001111110110 bp0001111110111
private noncomputable def vp0001111110101_0 : Blocks := edgeBlocks% "full/vectors/0001111110101-V-0000.bin"
noncomputable def vp0001111110101 : Blocks := vp0001111110101_0
theorem coverp0001111110101 : Covers (-1012761639/1000000 : ℚ) vp0001111110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111110100_0 : Blocks := edgeBlocks% "full/vectors/0001111110100-V-0000.bin"
noncomputable def vp0001111110100 : Blocks := vp0001111110100_0
theorem coverp0001111110100 : Covers (-1011761639/1000000 : ℚ) vp0001111110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111111010_0 : Blocks := edgeBlocks% "full/vectors/000111111010-V-0000.bin"
noncomputable def vp000111111010 : Blocks := vp000111111010_0
private theorem bp0001111110100 : Branch 0 (-1011761639/2000000 : ℚ) vp000111111010 := by
  apply branch_left_normalized (c:=vp0001111110100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1011761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1011761639/1000000 : ℚ) by norm_num]
  exact coverp0001111110100
private noncomputable def ep0001111110101_0 : Blocks := edgeBlocks% "full/vectors/0001111110101-E-0000.bin"
noncomputable def ep0001111110101 : Blocks := ep0001111110101_0
private theorem idp0001111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111111010.list =
    C ((2:ℤ)^88) * horner X vp0001111110101.list + horner X ep0001111110101.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111110101 : Branch 1 (-1011761639/2000000 : ℚ) vp000111111010 := by
  apply branch_checked idp0001111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1011761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1012761639/1000000 : ℚ) by norm_num]
  exact coverp0001111110101
theorem coverp000111111010 : Covers (-1011761639/2000000 : ℚ) vp000111111010 := join_branches bp0001111110100 bp0001111110101
private noncomputable def vp00011111101_0 : Blocks := edgeBlocks% "full/vectors/00011111101-V-0000.bin"
private noncomputable def vp00011111101_1 : Blocks := edgeBlocks% "full/vectors/00011111101-V-0001.bin"
noncomputable def vp00011111101 : Blocks := (Blocks.join vp00011111101_0 vp00011111101_1)
private theorem bp000111111010 : Branch 0 (-1011761639/4000000 : ℚ) vp00011111101 := by
  apply branch_left_normalized (c:=vp000111111010) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-1011761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1011761639/2000000 : ℚ) by norm_num]
  exact coverp000111111010
private noncomputable def ep000111111011_0 : Blocks := edgeBlocks% "full/vectors/000111111011-E-0000.bin"
private noncomputable def ep000111111011_1 : Blocks := edgeBlocks% "full/vectors/000111111011-E-0001.bin"
noncomputable def ep000111111011 : Blocks := (Blocks.join ep000111111011_0 ep000111111011_1)
private theorem idp000111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011111101.list =
    C ((2:ℤ)^156) * horner X vp000111111011.list + horner X ep000111111011.list := by
  exact edge_identity (B := (2:ℤ)^307) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111111011 : Branch 1 (-1011761639/4000000 : ℚ) vp00011111101 := by
  apply branch_checked idp000111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1011761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1013761639/2000000 : ℚ) by norm_num]
  exact coverp000111111011
theorem coverp00011111101 : Covers (-1011761639/4000000 : ℚ) vp00011111101 := join_branches bp000111111010 bp000111111011
private noncomputable def vp0001111110011_0 : Blocks := edgeBlocks% "full/vectors/0001111110011-V-0000.bin"
noncomputable def vp0001111110011 : Blocks := vp0001111110011_0
theorem coverp0001111110011 : Covers (-1010761639/1000000 : ℚ) vp0001111110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111110010_0 : Blocks := edgeBlocks% "full/vectors/0001111110010-V-0000.bin"
noncomputable def vp0001111110010 : Blocks := vp0001111110010_0
theorem coverp0001111110010 : Covers (-1009761639/1000000 : ℚ) vp0001111110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111111001_0 : Blocks := edgeBlocks% "full/vectors/000111111001-V-0000.bin"
noncomputable def vp000111111001 : Blocks := vp000111111001_0
private theorem bp0001111110010 : Branch 0 (-1009761639/2000000 : ℚ) vp000111111001 := by
  apply branch_left_normalized (c:=vp0001111110010) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1009761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1009761639/1000000 : ℚ) by norm_num]
  exact coverp0001111110010
private noncomputable def ep0001111110011_0 : Blocks := edgeBlocks% "full/vectors/0001111110011-E-0000.bin"
noncomputable def ep0001111110011 : Blocks := ep0001111110011_0
private theorem idp0001111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111111001.list =
    C ((2:ℤ)^90) * horner X vp0001111110011.list + horner X ep0001111110011.list := by
  exact edge_identity (B := (2:ℤ)^216) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111110011 : Branch 1 (-1009761639/2000000 : ℚ) vp000111111001 := by
  apply branch_checked idp0001111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1009761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1010761639/1000000 : ℚ) by norm_num]
  exact coverp0001111110011
theorem coverp000111111001 : Covers (-1009761639/2000000 : ℚ) vp000111111001 := join_branches bp0001111110010 bp0001111110011
private noncomputable def vp0001111110001_0 : Blocks := edgeBlocks% "full/vectors/0001111110001-V-0000.bin"
noncomputable def vp0001111110001 : Blocks := vp0001111110001_0
theorem coverp0001111110001 : Covers (-1008761639/1000000 : ℚ) vp0001111110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111110000_0 : Blocks := edgeBlocks% "full/vectors/0001111110000-V-0000.bin"
noncomputable def vp0001111110000 : Blocks := vp0001111110000_0
theorem coverp0001111110000 : Covers (-1007761639/1000000 : ℚ) vp0001111110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111111000_0 : Blocks := edgeBlocks% "full/vectors/000111111000-V-0000.bin"
noncomputable def vp000111111000 : Blocks := vp000111111000_0
private theorem bp0001111110000 : Branch 0 (-1007761639/2000000 : ℚ) vp000111111000 := by
  apply branch_left_normalized (c:=vp0001111110000) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-1007761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1007761639/1000000 : ℚ) by norm_num]
  exact coverp0001111110000
private noncomputable def ep0001111110001_0 : Blocks := edgeBlocks% "full/vectors/0001111110001-E-0000.bin"
noncomputable def ep0001111110001 : Blocks := ep0001111110001_0
private theorem idp0001111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111111000.list =
    C ((2:ℤ)^89) * horner X vp0001111110001.list + horner X ep0001111110001.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111110001 : Branch 1 (-1007761639/2000000 : ℚ) vp000111111000 := by
  apply branch_checked idp0001111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1007761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1008761639/1000000 : ℚ) by norm_num]
  exact coverp0001111110001
theorem coverp000111111000 : Covers (-1007761639/2000000 : ℚ) vp000111111000 := join_branches bp0001111110000 bp0001111110001
private noncomputable def vp00011111100_0 : Blocks := edgeBlocks% "full/vectors/00011111100-V-0000.bin"
private noncomputable def vp00011111100_1 : Blocks := edgeBlocks% "full/vectors/00011111100-V-0001.bin"
noncomputable def vp00011111100 : Blocks := (Blocks.join vp00011111100_0 vp00011111100_1)
private theorem bp000111111000 : Branch 0 (-1007761639/4000000 : ℚ) vp00011111100 := by
  apply branch_left_normalized (c:=vp000111111000) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-1007761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1007761639/2000000 : ℚ) by norm_num]
  exact coverp000111111000
private noncomputable def ep000111111001_0 : Blocks := edgeBlocks% "full/vectors/000111111001-E-0000.bin"
private noncomputable def ep000111111001_1 : Blocks := edgeBlocks% "full/vectors/000111111001-E-0001.bin"
noncomputable def ep000111111001 : Blocks := (Blocks.join ep000111111001_0 ep000111111001_1)
private theorem idp000111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011111100.list =
    C ((2:ℤ)^160) * horner X vp000111111001.list + horner X ep000111111001.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111111001 : Branch 1 (-1007761639/4000000 : ℚ) vp00011111100 := by
  apply branch_checked idp000111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1007761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1009761639/2000000 : ℚ) by norm_num]
  exact coverp000111111001
theorem coverp00011111100 : Covers (-1007761639/4000000 : ℚ) vp00011111100 := join_branches bp000111111000 bp000111111001
private noncomputable def vp0001111110_0 : Blocks := edgeBlocks% "full/vectors/0001111110-V-0000.bin"
private noncomputable def vp0001111110_1 : Blocks := edgeBlocks% "full/vectors/0001111110-V-0001.bin"
private noncomputable def vp0001111110_2 : Blocks := edgeBlocks% "full/vectors/0001111110-V-0002.bin"
noncomputable def vp0001111110 : Blocks := (Blocks.join vp0001111110_0 (Blocks.join vp0001111110_1 vp0001111110_2))
private theorem bp00011111100 : Branch 0 (-1007761639/8000000 : ℚ) vp0001111110 := by
  apply branch_left_normalized (c:=vp00011111100) (k:=0) (m:=146) (by decide +kernel)
  rw [show 2*(-1007761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1007761639/4000000 : ℚ) by norm_num]
  exact coverp00011111100
private noncomputable def ep00011111101_0 : Blocks := edgeBlocks% "full/vectors/00011111101-E-0000.bin"
private noncomputable def ep00011111101_1 : Blocks := edgeBlocks% "full/vectors/00011111101-E-0001.bin"
private noncomputable def ep00011111101_2 : Blocks := edgeBlocks% "full/vectors/00011111101-E-0002.bin"
noncomputable def ep00011111101 : Blocks := (Blocks.join ep00011111101_0 (Blocks.join ep00011111101_1 ep00011111101_2))
private theorem idp00011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001111110.list =
    C ((2:ℤ)^298) * horner X vp00011111101.list + horner X ep00011111101.list := by
  exact edge_identity (B := (2:ℤ)^504) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011111101 : Branch 1 (-1007761639/8000000 : ℚ) vp0001111110 := by
  apply branch_checked idp00011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1007761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1011761639/4000000 : ℚ) by norm_num]
  exact coverp00011111101
theorem coverp0001111110 : Covers (-1007761639/8000000 : ℚ) vp0001111110 := join_branches bp00011111100 bp00011111101
private noncomputable def vp000111111_0 : Blocks := edgeBlocks% "full/vectors/000111111-V-0000.bin"
private noncomputable def vp000111111_1 : Blocks := edgeBlocks% "full/vectors/000111111-V-0001.bin"
private noncomputable def vp000111111_2 : Blocks := edgeBlocks% "full/vectors/000111111-V-0002.bin"
private noncomputable def vp000111111_3 : Blocks := edgeBlocks% "full/vectors/000111111-V-0003.bin"
private noncomputable def vp000111111_4 : Blocks := edgeBlocks% "full/vectors/000111111-V-0004.bin"
noncomputable def vp000111111 : Blocks := (Blocks.join (Blocks.join vp000111111_0 vp000111111_1) (Blocks.join vp000111111_2 (Blocks.join vp000111111_3 vp000111111_4)))
private theorem bp0001111110 : Branch 0 (-1007761639/16000000 : ℚ) vp000111111 := by
  apply branch_left_normalized (c:=vp0001111110) (k:=0) (m:=270) (by decide +kernel)
  rw [show 2*(-1007761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1007761639/8000000 : ℚ) by norm_num]
  exact coverp0001111110
private noncomputable def ep0001111111_0 : Blocks := edgeBlocks% "full/vectors/0001111111-E-0000.bin"
private noncomputable def ep0001111111_1 : Blocks := edgeBlocks% "full/vectors/0001111111-E-0001.bin"
private noncomputable def ep0001111111_2 : Blocks := edgeBlocks% "full/vectors/0001111111-E-0002.bin"
private noncomputable def ep0001111111_3 : Blocks := edgeBlocks% "full/vectors/0001111111-E-0003.bin"
private noncomputable def ep0001111111_4 : Blocks := edgeBlocks% "full/vectors/0001111111-E-0004.bin"
noncomputable def ep0001111111 : Blocks := (Blocks.join (Blocks.join ep0001111111_0 ep0001111111_1) (Blocks.join ep0001111111_2 (Blocks.join ep0001111111_3 ep0001111111_4)))
private theorem idp0001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111111.list =
    C ((2:ℤ)^567) * horner X vp0001111111.list + horner X ep0001111111.list := by
  exact edge_identity (B := (2:ℤ)^880) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111111 : Branch 1 (-1007761639/16000000 : ℚ) vp000111111 := by
  apply branch_checked idp0001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1007761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1015761639/8000000 : ℚ) by norm_num]
  exact coverp0001111111
theorem coverp000111111 : Covers (-1007761639/16000000 : ℚ) vp000111111 := join_branches bp0001111110 bp0001111111
private noncomputable def vp0001111101111_0 : Blocks := edgeBlocks% "full/vectors/0001111101111-V-0000.bin"
noncomputable def vp0001111101111 : Blocks := vp0001111101111_0
theorem coverp0001111101111 : Covers (-1006761639/1000000 : ℚ) vp0001111101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111101110_0 : Blocks := edgeBlocks% "full/vectors/0001111101110-V-0000.bin"
noncomputable def vp0001111101110 : Blocks := vp0001111101110_0
theorem coverp0001111101110 : Covers (-1005761639/1000000 : ℚ) vp0001111101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111110111_0 : Blocks := edgeBlocks% "full/vectors/000111110111-V-0000.bin"
noncomputable def vp000111110111 : Blocks := vp000111110111_0
private theorem bp0001111101110 : Branch 0 (-1005761639/2000000 : ℚ) vp000111110111 := by
  apply branch_left_normalized (c:=vp0001111101110) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-1005761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1005761639/1000000 : ℚ) by norm_num]
  exact coverp0001111101110
private noncomputable def ep0001111101111_0 : Blocks := edgeBlocks% "full/vectors/0001111101111-E-0000.bin"
noncomputable def ep0001111101111 : Blocks := ep0001111101111_0
private theorem idp0001111101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111110111.list =
    C ((2:ℤ)^89) * horner X vp0001111101111.list + horner X ep0001111101111.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111101111 : Branch 1 (-1005761639/2000000 : ℚ) vp000111110111 := by
  apply branch_checked idp0001111101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1005761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1006761639/1000000 : ℚ) by norm_num]
  exact coverp0001111101111
theorem coverp000111110111 : Covers (-1005761639/2000000 : ℚ) vp000111110111 := join_branches bp0001111101110 bp0001111101111
private noncomputable def vp0001111101101_0 : Blocks := edgeBlocks% "full/vectors/0001111101101-V-0000.bin"
noncomputable def vp0001111101101 : Blocks := vp0001111101101_0
theorem coverp0001111101101 : Covers (-1004761639/1000000 : ℚ) vp0001111101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111101100_0 : Blocks := edgeBlocks% "full/vectors/0001111101100-V-0000.bin"
noncomputable def vp0001111101100 : Blocks := vp0001111101100_0
theorem coverp0001111101100 : Covers (-1003761639/1000000 : ℚ) vp0001111101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111110110_0 : Blocks := edgeBlocks% "full/vectors/000111110110-V-0000.bin"
noncomputable def vp000111110110 : Blocks := vp000111110110_0
private theorem bp0001111101100 : Branch 0 (-1003761639/2000000 : ℚ) vp000111110110 := by
  apply branch_left_normalized (c:=vp0001111101100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-1003761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1003761639/1000000 : ℚ) by norm_num]
  exact coverp0001111101100
private noncomputable def ep0001111101101_0 : Blocks := edgeBlocks% "full/vectors/0001111101101-E-0000.bin"
noncomputable def ep0001111101101 : Blocks := ep0001111101101_0
private theorem idp0001111101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111110110.list =
    C ((2:ℤ)^89) * horner X vp0001111101101.list + horner X ep0001111101101.list := by
  exact edge_identity (B := (2:ℤ)^216) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111101101 : Branch 1 (-1003761639/2000000 : ℚ) vp000111110110 := by
  apply branch_checked idp0001111101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1003761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1004761639/1000000 : ℚ) by norm_num]
  exact coverp0001111101101
theorem coverp000111110110 : Covers (-1003761639/2000000 : ℚ) vp000111110110 := join_branches bp0001111101100 bp0001111101101
private noncomputable def vp00011111011_0 : Blocks := edgeBlocks% "full/vectors/00011111011-V-0000.bin"
private noncomputable def vp00011111011_1 : Blocks := edgeBlocks% "full/vectors/00011111011-V-0001.bin"
noncomputable def vp00011111011 : Blocks := (Blocks.join vp00011111011_0 vp00011111011_1)
private theorem bp000111110110 : Branch 0 (-1003761639/4000000 : ℚ) vp00011111011 := by
  apply branch_left_normalized (c:=vp000111110110) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-1003761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1003761639/2000000 : ℚ) by norm_num]
  exact coverp000111110110
private noncomputable def ep000111110111_0 : Blocks := edgeBlocks% "full/vectors/000111110111-E-0000.bin"
private noncomputable def ep000111110111_1 : Blocks := edgeBlocks% "full/vectors/000111110111-E-0001.bin"
noncomputable def ep000111110111 : Blocks := (Blocks.join ep000111110111_0 ep000111110111_1)
private theorem idp000111110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011111011.list =
    C ((2:ℤ)^157) * horner X vp000111110111.list + horner X ep000111110111.list := by
  exact edge_identity (B := (2:ℤ)^312) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111110111 : Branch 1 (-1003761639/4000000 : ℚ) vp00011111011 := by
  apply branch_checked idp000111110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1003761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1005761639/2000000 : ℚ) by norm_num]
  exact coverp000111110111
theorem coverp00011111011 : Covers (-1003761639/4000000 : ℚ) vp00011111011 := join_branches bp000111110110 bp000111110111
private noncomputable def vp0001111101011_0 : Blocks := edgeBlocks% "full/vectors/0001111101011-V-0000.bin"
noncomputable def vp0001111101011 : Blocks := vp0001111101011_0
theorem coverp0001111101011 : Covers (-1002761639/1000000 : ℚ) vp0001111101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111101010_0 : Blocks := edgeBlocks% "full/vectors/0001111101010-V-0000.bin"
noncomputable def vp0001111101010 : Blocks := vp0001111101010_0
theorem coverp0001111101010 : Covers (-1001761639/1000000 : ℚ) vp0001111101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111110101_0 : Blocks := edgeBlocks% "full/vectors/000111110101-V-0000.bin"
noncomputable def vp000111110101 : Blocks := vp000111110101_0
private theorem bp0001111101010 : Branch 0 (-1001761639/2000000 : ℚ) vp000111110101 := by
  apply branch_left_normalized (c:=vp0001111101010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-1001761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1001761639/1000000 : ℚ) by norm_num]
  exact coverp0001111101010
private noncomputable def ep0001111101011_0 : Blocks := edgeBlocks% "full/vectors/0001111101011-E-0000.bin"
noncomputable def ep0001111101011 : Blocks := ep0001111101011_0
private theorem idp0001111101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111110101.list =
    C ((2:ℤ)^90) * horner X vp0001111101011.list + horner X ep0001111101011.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111101011 : Branch 1 (-1001761639/2000000 : ℚ) vp000111110101 := by
  apply branch_checked idp0001111101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1001761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1002761639/1000000 : ℚ) by norm_num]
  exact coverp0001111101011
theorem coverp000111110101 : Covers (-1001761639/2000000 : ℚ) vp000111110101 := join_branches bp0001111101010 bp0001111101011
private noncomputable def vp0001111101001_0 : Blocks := edgeBlocks% "full/vectors/0001111101001-V-0000.bin"
noncomputable def vp0001111101001 : Blocks := vp0001111101001_0
theorem coverp0001111101001 : Covers (-1000761639/1000000 : ℚ) vp0001111101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111101000_0 : Blocks := edgeBlocks% "full/vectors/0001111101000-V-0000.bin"
noncomputable def vp0001111101000 : Blocks := vp0001111101000_0
theorem coverp0001111101000 : Covers (-999761639/1000000 : ℚ) vp0001111101000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111110100_0 : Blocks := edgeBlocks% "full/vectors/000111110100-V-0000.bin"
noncomputable def vp000111110100 : Blocks := vp000111110100_0
private theorem bp0001111101000 : Branch 0 (-999761639/2000000 : ℚ) vp000111110100 := by
  apply branch_left_normalized (c:=vp0001111101000) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-999761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-999761639/1000000 : ℚ) by norm_num]
  exact coverp0001111101000
private noncomputable def ep0001111101001_0 : Blocks := edgeBlocks% "full/vectors/0001111101001-E-0000.bin"
noncomputable def ep0001111101001 : Blocks := ep0001111101001_0
private theorem idp0001111101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111110100.list =
    C ((2:ℤ)^90) * horner X vp0001111101001.list + horner X ep0001111101001.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111101001 : Branch 1 (-999761639/2000000 : ℚ) vp000111110100 := by
  apply branch_checked idp0001111101001 (by positivity) (by decide +kernel)
  rw [show 2*(-999761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1000761639/1000000 : ℚ) by norm_num]
  exact coverp0001111101001
theorem coverp000111110100 : Covers (-999761639/2000000 : ℚ) vp000111110100 := join_branches bp0001111101000 bp0001111101001
private noncomputable def vp00011111010_0 : Blocks := edgeBlocks% "full/vectors/00011111010-V-0000.bin"
private noncomputable def vp00011111010_1 : Blocks := edgeBlocks% "full/vectors/00011111010-V-0001.bin"
noncomputable def vp00011111010 : Blocks := (Blocks.join vp00011111010_0 vp00011111010_1)
private theorem bp000111110100 : Branch 0 (-999761639/4000000 : ℚ) vp00011111010 := by
  apply branch_left_normalized (c:=vp000111110100) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-999761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-999761639/2000000 : ℚ) by norm_num]
  exact coverp000111110100
private noncomputable def ep000111110101_0 : Blocks := edgeBlocks% "full/vectors/000111110101-E-0000.bin"
private noncomputable def ep000111110101_1 : Blocks := edgeBlocks% "full/vectors/000111110101-E-0001.bin"
noncomputable def ep000111110101 : Blocks := (Blocks.join ep000111110101_0 ep000111110101_1)
private theorem idp000111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011111010.list =
    C ((2:ℤ)^159) * horner X vp000111110101.list + horner X ep000111110101.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111110101 : Branch 1 (-999761639/4000000 : ℚ) vp00011111010 := by
  apply branch_checked idp000111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-999761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1001761639/2000000 : ℚ) by norm_num]
  exact coverp000111110101
theorem coverp00011111010 : Covers (-999761639/4000000 : ℚ) vp00011111010 := join_branches bp000111110100 bp000111110101
private noncomputable def vp0001111101_0 : Blocks := edgeBlocks% "full/vectors/0001111101-V-0000.bin"
private noncomputable def vp0001111101_1 : Blocks := edgeBlocks% "full/vectors/0001111101-V-0001.bin"
private noncomputable def vp0001111101_2 : Blocks := edgeBlocks% "full/vectors/0001111101-V-0002.bin"
noncomputable def vp0001111101 : Blocks := (Blocks.join vp0001111101_0 (Blocks.join vp0001111101_1 vp0001111101_2))
private theorem bp00011111010 : Branch 0 (-999761639/8000000 : ℚ) vp0001111101 := by
  apply branch_left_normalized (c:=vp00011111010) (k:=0) (m:=146) (by decide +kernel)
  rw [show 2*(-999761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-999761639/4000000 : ℚ) by norm_num]
  exact coverp00011111010
private noncomputable def ep00011111011_0 : Blocks := edgeBlocks% "full/vectors/00011111011-E-0000.bin"
private noncomputable def ep00011111011_1 : Blocks := edgeBlocks% "full/vectors/00011111011-E-0001.bin"
private noncomputable def ep00011111011_2 : Blocks := edgeBlocks% "full/vectors/00011111011-E-0002.bin"
noncomputable def ep00011111011 : Blocks := (Blocks.join ep00011111011_0 (Blocks.join ep00011111011_1 ep00011111011_2))
private theorem idp00011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001111101.list =
    C ((2:ℤ)^296) * horner X vp00011111011.list + horner X ep00011111011.list := by
  exact edge_identity (B := (2:ℤ)^505) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011111011 : Branch 1 (-999761639/8000000 : ℚ) vp0001111101 := by
  apply branch_checked idp00011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-999761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1003761639/4000000 : ℚ) by norm_num]
  exact coverp00011111011
theorem coverp0001111101 : Covers (-999761639/8000000 : ℚ) vp0001111101 := join_branches bp00011111010 bp00011111011
private noncomputable def vp0001111100111_0 : Blocks := edgeBlocks% "full/vectors/0001111100111-V-0000.bin"
noncomputable def vp0001111100111 : Blocks := vp0001111100111_0
theorem coverp0001111100111 : Covers (-998761639/1000000 : ℚ) vp0001111100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111100110_0 : Blocks := edgeBlocks% "full/vectors/0001111100110-V-0000.bin"
noncomputable def vp0001111100110 : Blocks := vp0001111100110_0
theorem coverp0001111100110 : Covers (-997761639/1000000 : ℚ) vp0001111100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111110011_0 : Blocks := edgeBlocks% "full/vectors/000111110011-V-0000.bin"
noncomputable def vp000111110011 : Blocks := vp000111110011_0
private theorem bp0001111100110 : Branch 0 (-997761639/2000000 : ℚ) vp000111110011 := by
  apply branch_left_normalized (c:=vp0001111100110) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-997761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-997761639/1000000 : ℚ) by norm_num]
  exact coverp0001111100110
private noncomputable def ep0001111100111_0 : Blocks := edgeBlocks% "full/vectors/0001111100111-E-0000.bin"
noncomputable def ep0001111100111 : Blocks := ep0001111100111_0
private theorem idp0001111100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111110011.list =
    C ((2:ℤ)^89) * horner X vp0001111100111.list + horner X ep0001111100111.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111100111 : Branch 1 (-997761639/2000000 : ℚ) vp000111110011 := by
  apply branch_checked idp0001111100111 (by positivity) (by decide +kernel)
  rw [show 2*(-997761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-998761639/1000000 : ℚ) by norm_num]
  exact coverp0001111100111
theorem coverp000111110011 : Covers (-997761639/2000000 : ℚ) vp000111110011 := join_branches bp0001111100110 bp0001111100111
private noncomputable def vp0001111100101_0 : Blocks := edgeBlocks% "full/vectors/0001111100101-V-0000.bin"
noncomputable def vp0001111100101 : Blocks := vp0001111100101_0
theorem coverp0001111100101 : Covers (-996761639/1000000 : ℚ) vp0001111100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111100100_0 : Blocks := edgeBlocks% "full/vectors/0001111100100-V-0000.bin"
noncomputable def vp0001111100100 : Blocks := vp0001111100100_0
theorem coverp0001111100100 : Covers (-995761639/1000000 : ℚ) vp0001111100100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111110010_0 : Blocks := edgeBlocks% "full/vectors/000111110010-V-0000.bin"
noncomputable def vp000111110010 : Blocks := vp000111110010_0
private theorem bp0001111100100 : Branch 0 (-995761639/2000000 : ℚ) vp000111110010 := by
  apply branch_left_normalized (c:=vp0001111100100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-995761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-995761639/1000000 : ℚ) by norm_num]
  exact coverp0001111100100
private noncomputable def ep0001111100101_0 : Blocks := edgeBlocks% "full/vectors/0001111100101-E-0000.bin"
noncomputable def ep0001111100101 : Blocks := ep0001111100101_0
private theorem idp0001111100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111110010.list =
    C ((2:ℤ)^89) * horner X vp0001111100101.list + horner X ep0001111100101.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111100101 : Branch 1 (-995761639/2000000 : ℚ) vp000111110010 := by
  apply branch_checked idp0001111100101 (by positivity) (by decide +kernel)
  rw [show 2*(-995761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-996761639/1000000 : ℚ) by norm_num]
  exact coverp0001111100101
theorem coverp000111110010 : Covers (-995761639/2000000 : ℚ) vp000111110010 := join_branches bp0001111100100 bp0001111100101
private noncomputable def vp00011111001_0 : Blocks := edgeBlocks% "full/vectors/00011111001-V-0000.bin"
private noncomputable def vp00011111001_1 : Blocks := edgeBlocks% "full/vectors/00011111001-V-0001.bin"
noncomputable def vp00011111001 : Blocks := (Blocks.join vp00011111001_0 vp00011111001_1)
private theorem bp000111110010 : Branch 0 (-995761639/4000000 : ℚ) vp00011111001 := by
  apply branch_left_normalized (c:=vp000111110010) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-995761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-995761639/2000000 : ℚ) by norm_num]
  exact coverp000111110010
private noncomputable def ep000111110011_0 : Blocks := edgeBlocks% "full/vectors/000111110011-E-0000.bin"
private noncomputable def ep000111110011_1 : Blocks := edgeBlocks% "full/vectors/000111110011-E-0001.bin"
noncomputable def ep000111110011 : Blocks := (Blocks.join ep000111110011_0 ep000111110011_1)
private theorem idp000111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011111001.list =
    C ((2:ℤ)^159) * horner X vp000111110011.list + horner X ep000111110011.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111110011 : Branch 1 (-995761639/4000000 : ℚ) vp00011111001 := by
  apply branch_checked idp000111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-995761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-997761639/2000000 : ℚ) by norm_num]
  exact coverp000111110011
theorem coverp00011111001 : Covers (-995761639/4000000 : ℚ) vp00011111001 := join_branches bp000111110010 bp000111110011
private noncomputable def vp0001111100011_0 : Blocks := edgeBlocks% "full/vectors/0001111100011-V-0000.bin"
noncomputable def vp0001111100011 : Blocks := vp0001111100011_0
theorem coverp0001111100011 : Covers (-994761639/1000000 : ℚ) vp0001111100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111100010_0 : Blocks := edgeBlocks% "full/vectors/0001111100010-V-0000.bin"
noncomputable def vp0001111100010 : Blocks := vp0001111100010_0
theorem coverp0001111100010 : Covers (-993761639/1000000 : ℚ) vp0001111100010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111110001_0 : Blocks := edgeBlocks% "full/vectors/000111110001-V-0000.bin"
noncomputable def vp000111110001 : Blocks := vp000111110001_0
private theorem bp0001111100010 : Branch 0 (-993761639/2000000 : ℚ) vp000111110001 := by
  apply branch_left_normalized (c:=vp0001111100010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-993761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-993761639/1000000 : ℚ) by norm_num]
  exact coverp0001111100010
private noncomputable def ep0001111100011_0 : Blocks := edgeBlocks% "full/vectors/0001111100011-E-0000.bin"
noncomputable def ep0001111100011 : Blocks := ep0001111100011_0
private theorem idp0001111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111110001.list =
    C ((2:ℤ)^90) * horner X vp0001111100011.list + horner X ep0001111100011.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111100011 : Branch 1 (-993761639/2000000 : ℚ) vp000111110001 := by
  apply branch_checked idp0001111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-993761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-994761639/1000000 : ℚ) by norm_num]
  exact coverp0001111100011
theorem coverp000111110001 : Covers (-993761639/2000000 : ℚ) vp000111110001 := join_branches bp0001111100010 bp0001111100011
private noncomputable def vp0001111100001_0 : Blocks := edgeBlocks% "full/vectors/0001111100001-V-0000.bin"
noncomputable def vp0001111100001 : Blocks := vp0001111100001_0
theorem coverp0001111100001 : Covers (-992761639/1000000 : ℚ) vp0001111100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111100000_0 : Blocks := edgeBlocks% "full/vectors/0001111100000-V-0000.bin"
noncomputable def vp0001111100000 : Blocks := vp0001111100000_0
theorem coverp0001111100000 : Covers (-991761639/1000000 : ℚ) vp0001111100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111110000_0 : Blocks := edgeBlocks% "full/vectors/000111110000-V-0000.bin"
noncomputable def vp000111110000 : Blocks := vp000111110000_0
private theorem bp0001111100000 : Branch 0 (-991761639/2000000 : ℚ) vp000111110000 := by
  apply branch_left_normalized (c:=vp0001111100000) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-991761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-991761639/1000000 : ℚ) by norm_num]
  exact coverp0001111100000
private noncomputable def ep0001111100001_0 : Blocks := edgeBlocks% "full/vectors/0001111100001-E-0000.bin"
noncomputable def ep0001111100001 : Blocks := ep0001111100001_0
private theorem idp0001111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111110000.list =
    C ((2:ℤ)^90) * horner X vp0001111100001.list + horner X ep0001111100001.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111100001 : Branch 1 (-991761639/2000000 : ℚ) vp000111110000 := by
  apply branch_checked idp0001111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-991761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-992761639/1000000 : ℚ) by norm_num]
  exact coverp0001111100001
theorem coverp000111110000 : Covers (-991761639/2000000 : ℚ) vp000111110000 := join_branches bp0001111100000 bp0001111100001
private noncomputable def vp00011111000_0 : Blocks := edgeBlocks% "full/vectors/00011111000-V-0000.bin"
private noncomputable def vp00011111000_1 : Blocks := edgeBlocks% "full/vectors/00011111000-V-0001.bin"
noncomputable def vp00011111000 : Blocks := (Blocks.join vp00011111000_0 vp00011111000_1)
private theorem bp000111110000 : Branch 0 (-991761639/4000000 : ℚ) vp00011111000 := by
  apply branch_left_normalized (c:=vp000111110000) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-991761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-991761639/2000000 : ℚ) by norm_num]
  exact coverp000111110000
private noncomputable def ep000111110001_0 : Blocks := edgeBlocks% "full/vectors/000111110001-E-0000.bin"
private noncomputable def ep000111110001_1 : Blocks := edgeBlocks% "full/vectors/000111110001-E-0001.bin"
noncomputable def ep000111110001 : Blocks := (Blocks.join ep000111110001_0 ep000111110001_1)
private theorem idp000111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011111000.list =
    C ((2:ℤ)^160) * horner X vp000111110001.list + horner X ep000111110001.list := by
  exact edge_identity (B := (2:ℤ)^316) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111110001 : Branch 1 (-991761639/4000000 : ℚ) vp00011111000 := by
  apply branch_checked idp000111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-991761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-993761639/2000000 : ℚ) by norm_num]
  exact coverp000111110001
theorem coverp00011111000 : Covers (-991761639/4000000 : ℚ) vp00011111000 := join_branches bp000111110000 bp000111110001
private noncomputable def vp0001111100_0 : Blocks := edgeBlocks% "full/vectors/0001111100-V-0000.bin"
private noncomputable def vp0001111100_1 : Blocks := edgeBlocks% "full/vectors/0001111100-V-0001.bin"
private noncomputable def vp0001111100_2 : Blocks := edgeBlocks% "full/vectors/0001111100-V-0002.bin"
noncomputable def vp0001111100 : Blocks := (Blocks.join vp0001111100_0 (Blocks.join vp0001111100_1 vp0001111100_2))
private theorem bp00011111000 : Branch 0 (-991761639/8000000 : ℚ) vp0001111100 := by
  apply branch_left_normalized (c:=vp00011111000) (k:=0) (m:=147) (by decide +kernel)
  rw [show 2*(-991761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-991761639/4000000 : ℚ) by norm_num]
  exact coverp00011111000
private noncomputable def ep00011111001_0 : Blocks := edgeBlocks% "full/vectors/00011111001-E-0000.bin"
private noncomputable def ep00011111001_1 : Blocks := edgeBlocks% "full/vectors/00011111001-E-0001.bin"
private noncomputable def ep00011111001_2 : Blocks := edgeBlocks% "full/vectors/00011111001-E-0002.bin"
noncomputable def ep00011111001 : Blocks := (Blocks.join ep00011111001_0 (Blocks.join ep00011111001_1 ep00011111001_2))
private theorem idp00011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001111100.list =
    C ((2:ℤ)^296) * horner X vp00011111001.list + horner X ep00011111001.list := by
  exact edge_identity (B := (2:ℤ)^507) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011111001 : Branch 1 (-991761639/8000000 : ℚ) vp0001111100 := by
  apply branch_checked idp00011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-991761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-995761639/4000000 : ℚ) by norm_num]
  exact coverp00011111001
theorem coverp0001111100 : Covers (-991761639/8000000 : ℚ) vp0001111100 := join_branches bp00011111000 bp00011111001
private noncomputable def vp000111110_0 : Blocks := edgeBlocks% "full/vectors/000111110-V-0000.bin"
private noncomputable def vp000111110_1 : Blocks := edgeBlocks% "full/vectors/000111110-V-0001.bin"
private noncomputable def vp000111110_2 : Blocks := edgeBlocks% "full/vectors/000111110-V-0002.bin"
private noncomputable def vp000111110_3 : Blocks := edgeBlocks% "full/vectors/000111110-V-0003.bin"
private noncomputable def vp000111110_4 : Blocks := edgeBlocks% "full/vectors/000111110-V-0004.bin"
noncomputable def vp000111110 : Blocks := (Blocks.join (Blocks.join vp000111110_0 vp000111110_1) (Blocks.join vp000111110_2 (Blocks.join vp000111110_3 vp000111110_4)))
private theorem bp0001111100 : Branch 0 (-991761639/16000000 : ℚ) vp000111110 := by
  apply branch_left_normalized (c:=vp0001111100) (k:=0) (m:=271) (by decide +kernel)
  rw [show 2*(-991761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-991761639/8000000 : ℚ) by norm_num]
  exact coverp0001111100
private noncomputable def ep0001111101_0 : Blocks := edgeBlocks% "full/vectors/0001111101-E-0000.bin"
private noncomputable def ep0001111101_1 : Blocks := edgeBlocks% "full/vectors/0001111101-E-0001.bin"
private noncomputable def ep0001111101_2 : Blocks := edgeBlocks% "full/vectors/0001111101-E-0002.bin"
private noncomputable def ep0001111101_3 : Blocks := edgeBlocks% "full/vectors/0001111101-E-0003.bin"
private noncomputable def ep0001111101_4 : Blocks := edgeBlocks% "full/vectors/0001111101-E-0004.bin"
noncomputable def ep0001111101 : Blocks := (Blocks.join (Blocks.join ep0001111101_0 ep0001111101_1) (Blocks.join ep0001111101_2 (Blocks.join ep0001111101_3 ep0001111101_4)))
private theorem idp0001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111110.list =
    C ((2:ℤ)^567) * horner X vp0001111101.list + horner X ep0001111101.list := by
  exact edge_identity (B := (2:ℤ)^887) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111101 : Branch 1 (-991761639/16000000 : ℚ) vp000111110 := by
  apply branch_checked idp0001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-991761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-999761639/8000000 : ℚ) by norm_num]
  exact coverp0001111101
theorem coverp000111110 : Covers (-991761639/16000000 : ℚ) vp000111110 := join_branches bp0001111100 bp0001111101
private noncomputable def vp00011111_0 : Blocks := edgeBlocks% "full/vectors/00011111-V-0000.bin"
private noncomputable def vp00011111_1 : Blocks := edgeBlocks% "full/vectors/00011111-V-0001.bin"
private noncomputable def vp00011111_2 : Blocks := edgeBlocks% "full/vectors/00011111-V-0002.bin"
private noncomputable def vp00011111_3 : Blocks := edgeBlocks% "full/vectors/00011111-V-0003.bin"
private noncomputable def vp00011111_4 : Blocks := edgeBlocks% "full/vectors/00011111-V-0004.bin"
private noncomputable def vp00011111_5 : Blocks := edgeBlocks% "full/vectors/00011111-V-0005.bin"
private noncomputable def vp00011111_6 : Blocks := edgeBlocks% "full/vectors/00011111-V-0006.bin"
private noncomputable def vp00011111_7 : Blocks := edgeBlocks% "full/vectors/00011111-V-0007.bin"
noncomputable def vp00011111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00011111_0 vp00011111_1) (Blocks.join vp00011111_2 vp00011111_3)) (Blocks.join (Blocks.join vp00011111_4 vp00011111_5) (Blocks.join vp00011111_6 vp00011111_7)))
private theorem bp000111110 : Branch 0 (-991761639/32000000 : ℚ) vp00011111 := by
  apply branch_left_normalized (c:=vp000111110) (k:=0) (m:=519) (by decide +kernel)
  rw [show 2*(-991761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-991761639/16000000 : ℚ) by norm_num]
  exact coverp000111110
private noncomputable def ep000111111_0 : Blocks := edgeBlocks% "full/vectors/000111111-E-0000.bin"
private noncomputable def ep000111111_1 : Blocks := edgeBlocks% "full/vectors/000111111-E-0001.bin"
private noncomputable def ep000111111_2 : Blocks := edgeBlocks% "full/vectors/000111111-E-0002.bin"
private noncomputable def ep000111111_3 : Blocks := edgeBlocks% "full/vectors/000111111-E-0003.bin"
private noncomputable def ep000111111_4 : Blocks := edgeBlocks% "full/vectors/000111111-E-0004.bin"
private noncomputable def ep000111111_5 : Blocks := edgeBlocks% "full/vectors/000111111-E-0005.bin"
private noncomputable def ep000111111_6 : Blocks := edgeBlocks% "full/vectors/000111111-E-0006.bin"
private noncomputable def ep000111111_7 : Blocks := edgeBlocks% "full/vectors/000111111-E-0007.bin"
noncomputable def ep000111111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000111111_0 ep000111111_1) (Blocks.join ep000111111_2 ep000111111_3)) (Blocks.join (Blocks.join ep000111111_4 ep000111111_5) (Blocks.join ep000111111_6 ep000111111_7)))
private theorem idp000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011111.list =
    C ((2:ℤ)^1101) * horner X vp000111111.list + horner X ep000111111.list := by
  exact edge_identity (B := (2:ℤ)^1638) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111111 : Branch 1 (-991761639/32000000 : ℚ) vp00011111 := by
  apply branch_checked idp000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-991761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1007761639/16000000 : ℚ) by norm_num]
  exact coverp000111111
theorem coverp00011111 : Covers (-991761639/32000000 : ℚ) vp00011111 := join_branches bp000111110 bp000111111
private noncomputable def vp0001111011111_0 : Blocks := edgeBlocks% "full/vectors/0001111011111-V-0000.bin"
noncomputable def vp0001111011111 : Blocks := vp0001111011111_0
theorem coverp0001111011111 : Covers (-990761639/1000000 : ℚ) vp0001111011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111011110_0 : Blocks := edgeBlocks% "full/vectors/0001111011110-V-0000.bin"
noncomputable def vp0001111011110 : Blocks := vp0001111011110_0
theorem coverp0001111011110 : Covers (-989761639/1000000 : ℚ) vp0001111011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111101111_0 : Blocks := edgeBlocks% "full/vectors/000111101111-V-0000.bin"
noncomputable def vp000111101111 : Blocks := vp000111101111_0
private theorem bp0001111011110 : Branch 0 (-989761639/2000000 : ℚ) vp000111101111 := by
  apply branch_left_normalized (c:=vp0001111011110) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-989761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-989761639/1000000 : ℚ) by norm_num]
  exact coverp0001111011110
private noncomputable def ep0001111011111_0 : Blocks := edgeBlocks% "full/vectors/0001111011111-E-0000.bin"
noncomputable def ep0001111011111 : Blocks := ep0001111011111_0
private theorem idp0001111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111101111.list =
    C ((2:ℤ)^90) * horner X vp0001111011111.list + horner X ep0001111011111.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111011111 : Branch 1 (-989761639/2000000 : ℚ) vp000111101111 := by
  apply branch_checked idp0001111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-989761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-990761639/1000000 : ℚ) by norm_num]
  exact coverp0001111011111
theorem coverp000111101111 : Covers (-989761639/2000000 : ℚ) vp000111101111 := join_branches bp0001111011110 bp0001111011111
private noncomputable def vp0001111011101_0 : Blocks := edgeBlocks% "full/vectors/0001111011101-V-0000.bin"
noncomputable def vp0001111011101 : Blocks := vp0001111011101_0
theorem coverp0001111011101 : Covers (-988761639/1000000 : ℚ) vp0001111011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111011100_0 : Blocks := edgeBlocks% "full/vectors/0001111011100-V-0000.bin"
noncomputable def vp0001111011100 : Blocks := vp0001111011100_0
theorem coverp0001111011100 : Covers (-987761639/1000000 : ℚ) vp0001111011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111101110_0 : Blocks := edgeBlocks% "full/vectors/000111101110-V-0000.bin"
noncomputable def vp000111101110 : Blocks := vp000111101110_0
private theorem bp0001111011100 : Branch 0 (-987761639/2000000 : ℚ) vp000111101110 := by
  apply branch_left_normalized (c:=vp0001111011100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-987761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-987761639/1000000 : ℚ) by norm_num]
  exact coverp0001111011100
private noncomputable def ep0001111011101_0 : Blocks := edgeBlocks% "full/vectors/0001111011101-E-0000.bin"
noncomputable def ep0001111011101 : Blocks := ep0001111011101_0
private theorem idp0001111011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111101110.list =
    C ((2:ℤ)^90) * horner X vp0001111011101.list + horner X ep0001111011101.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111011101 : Branch 1 (-987761639/2000000 : ℚ) vp000111101110 := by
  apply branch_checked idp0001111011101 (by positivity) (by decide +kernel)
  rw [show 2*(-987761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-988761639/1000000 : ℚ) by norm_num]
  exact coverp0001111011101
theorem coverp000111101110 : Covers (-987761639/2000000 : ℚ) vp000111101110 := join_branches bp0001111011100 bp0001111011101
private noncomputable def vp00011110111_0 : Blocks := edgeBlocks% "full/vectors/00011110111-V-0000.bin"
private noncomputable def vp00011110111_1 : Blocks := edgeBlocks% "full/vectors/00011110111-V-0001.bin"
noncomputable def vp00011110111 : Blocks := (Blocks.join vp00011110111_0 vp00011110111_1)
private theorem bp000111101110 : Branch 0 (-987761639/4000000 : ℚ) vp00011110111 := by
  apply branch_left_normalized (c:=vp000111101110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-987761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-987761639/2000000 : ℚ) by norm_num]
  exact coverp000111101110
private noncomputable def ep000111101111_0 : Blocks := edgeBlocks% "full/vectors/000111101111-E-0000.bin"
private noncomputable def ep000111101111_1 : Blocks := edgeBlocks% "full/vectors/000111101111-E-0001.bin"
noncomputable def ep000111101111 : Blocks := (Blocks.join ep000111101111_0 ep000111101111_1)
private theorem idp000111101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011110111.list =
    C ((2:ℤ)^159) * horner X vp000111101111.list + horner X ep000111101111.list := by
  exact edge_identity (B := (2:ℤ)^315) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111101111 : Branch 1 (-987761639/4000000 : ℚ) vp00011110111 := by
  apply branch_checked idp000111101111 (by positivity) (by decide +kernel)
  rw [show 2*(-987761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-989761639/2000000 : ℚ) by norm_num]
  exact coverp000111101111
theorem coverp00011110111 : Covers (-987761639/4000000 : ℚ) vp00011110111 := join_branches bp000111101110 bp000111101111
private noncomputable def vp0001111011011_0 : Blocks := edgeBlocks% "full/vectors/0001111011011-V-0000.bin"
noncomputable def vp0001111011011 : Blocks := vp0001111011011_0
theorem coverp0001111011011 : Covers (-986761639/1000000 : ℚ) vp0001111011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111011010_0 : Blocks := edgeBlocks% "full/vectors/0001111011010-V-0000.bin"
noncomputable def vp0001111011010 : Blocks := vp0001111011010_0
theorem coverp0001111011010 : Covers (-985761639/1000000 : ℚ) vp0001111011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111101101_0 : Blocks := edgeBlocks% "full/vectors/000111101101-V-0000.bin"
noncomputable def vp000111101101 : Blocks := vp000111101101_0
private theorem bp0001111011010 : Branch 0 (-985761639/2000000 : ℚ) vp000111101101 := by
  apply branch_left_normalized (c:=vp0001111011010) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-985761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-985761639/1000000 : ℚ) by norm_num]
  exact coverp0001111011010
private noncomputable def ep0001111011011_0 : Blocks := edgeBlocks% "full/vectors/0001111011011-E-0000.bin"
noncomputable def ep0001111011011 : Blocks := ep0001111011011_0
private theorem idp0001111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111101101.list =
    C ((2:ℤ)^89) * horner X vp0001111011011.list + horner X ep0001111011011.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111011011 : Branch 1 (-985761639/2000000 : ℚ) vp000111101101 := by
  apply branch_checked idp0001111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-985761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-986761639/1000000 : ℚ) by norm_num]
  exact coverp0001111011011
theorem coverp000111101101 : Covers (-985761639/2000000 : ℚ) vp000111101101 := join_branches bp0001111011010 bp0001111011011
private noncomputable def vp0001111011001_0 : Blocks := edgeBlocks% "full/vectors/0001111011001-V-0000.bin"
noncomputable def vp0001111011001 : Blocks := vp0001111011001_0
theorem coverp0001111011001 : Covers (-984761639/1000000 : ℚ) vp0001111011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111011000_0 : Blocks := edgeBlocks% "full/vectors/0001111011000-V-0000.bin"
noncomputable def vp0001111011000 : Blocks := vp0001111011000_0
theorem coverp0001111011000 : Covers (-983761639/1000000 : ℚ) vp0001111011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111101100_0 : Blocks := edgeBlocks% "full/vectors/000111101100-V-0000.bin"
noncomputable def vp000111101100 : Blocks := vp000111101100_0
private theorem bp0001111011000 : Branch 0 (-983761639/2000000 : ℚ) vp000111101100 := by
  apply branch_left_normalized (c:=vp0001111011000) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-983761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-983761639/1000000 : ℚ) by norm_num]
  exact coverp0001111011000
private noncomputable def ep0001111011001_0 : Blocks := edgeBlocks% "full/vectors/0001111011001-E-0000.bin"
noncomputable def ep0001111011001 : Blocks := ep0001111011001_0
private theorem idp0001111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111101100.list =
    C ((2:ℤ)^91) * horner X vp0001111011001.list + horner X ep0001111011001.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111011001 : Branch 1 (-983761639/2000000 : ℚ) vp000111101100 := by
  apply branch_checked idp0001111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-983761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-984761639/1000000 : ℚ) by norm_num]
  exact coverp0001111011001
theorem coverp000111101100 : Covers (-983761639/2000000 : ℚ) vp000111101100 := join_branches bp0001111011000 bp0001111011001
private noncomputable def vp00011110110_0 : Blocks := edgeBlocks% "full/vectors/00011110110-V-0000.bin"
private noncomputable def vp00011110110_1 : Blocks := edgeBlocks% "full/vectors/00011110110-V-0001.bin"
noncomputable def vp00011110110 : Blocks := (Blocks.join vp00011110110_0 vp00011110110_1)
private theorem bp000111101100 : Branch 0 (-983761639/4000000 : ℚ) vp00011110110 := by
  apply branch_left_normalized (c:=vp000111101100) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-983761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-983761639/2000000 : ℚ) by norm_num]
  exact coverp000111101100
private noncomputable def ep000111101101_0 : Blocks := edgeBlocks% "full/vectors/000111101101-E-0000.bin"
private noncomputable def ep000111101101_1 : Blocks := edgeBlocks% "full/vectors/000111101101-E-0001.bin"
noncomputable def ep000111101101 : Blocks := (Blocks.join ep000111101101_0 ep000111101101_1)
private theorem idp000111101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011110110.list =
    C ((2:ℤ)^160) * horner X vp000111101101.list + horner X ep000111101101.list := by
  exact edge_identity (B := (2:ℤ)^315) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111101101 : Branch 1 (-983761639/4000000 : ℚ) vp00011110110 := by
  apply branch_checked idp000111101101 (by positivity) (by decide +kernel)
  rw [show 2*(-983761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-985761639/2000000 : ℚ) by norm_num]
  exact coverp000111101101
theorem coverp00011110110 : Covers (-983761639/4000000 : ℚ) vp00011110110 := join_branches bp000111101100 bp000111101101
private noncomputable def vp0001111011_0 : Blocks := edgeBlocks% "full/vectors/0001111011-V-0000.bin"
private noncomputable def vp0001111011_1 : Blocks := edgeBlocks% "full/vectors/0001111011-V-0001.bin"
private noncomputable def vp0001111011_2 : Blocks := edgeBlocks% "full/vectors/0001111011-V-0002.bin"
noncomputable def vp0001111011 : Blocks := (Blocks.join vp0001111011_0 (Blocks.join vp0001111011_1 vp0001111011_2))
private theorem bp00011110110 : Branch 0 (-983761639/8000000 : ℚ) vp0001111011 := by
  apply branch_left_normalized (c:=vp00011110110) (k:=0) (m:=147) (by decide +kernel)
  rw [show 2*(-983761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-983761639/4000000 : ℚ) by norm_num]
  exact coverp00011110110
private noncomputable def ep00011110111_0 : Blocks := edgeBlocks% "full/vectors/00011110111-E-0000.bin"
private noncomputable def ep00011110111_1 : Blocks := edgeBlocks% "full/vectors/00011110111-E-0001.bin"
private noncomputable def ep00011110111_2 : Blocks := edgeBlocks% "full/vectors/00011110111-E-0002.bin"
noncomputable def ep00011110111 : Blocks := (Blocks.join ep00011110111_0 (Blocks.join ep00011110111_1 ep00011110111_2))
private theorem idp00011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001111011.list =
    C ((2:ℤ)^296) * horner X vp00011110111.list + horner X ep00011110111.list := by
  exact edge_identity (B := (2:ℤ)^507) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011110111 : Branch 1 (-983761639/8000000 : ℚ) vp0001111011 := by
  apply branch_checked idp00011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-983761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-987761639/4000000 : ℚ) by norm_num]
  exact coverp00011110111
theorem coverp0001111011 : Covers (-983761639/8000000 : ℚ) vp0001111011 := join_branches bp00011110110 bp00011110111
private noncomputable def vp0001111010111_0 : Blocks := edgeBlocks% "full/vectors/0001111010111-V-0000.bin"
noncomputable def vp0001111010111 : Blocks := vp0001111010111_0
theorem coverp0001111010111 : Covers (-982761639/1000000 : ℚ) vp0001111010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111010110_0 : Blocks := edgeBlocks% "full/vectors/0001111010110-V-0000.bin"
noncomputable def vp0001111010110 : Blocks := vp0001111010110_0
theorem coverp0001111010110 : Covers (-981761639/1000000 : ℚ) vp0001111010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111101011_0 : Blocks := edgeBlocks% "full/vectors/000111101011-V-0000.bin"
noncomputable def vp000111101011 : Blocks := vp000111101011_0
private theorem bp0001111010110 : Branch 0 (-981761639/2000000 : ℚ) vp000111101011 := by
  apply branch_left_normalized (c:=vp0001111010110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-981761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-981761639/1000000 : ℚ) by norm_num]
  exact coverp0001111010110
private noncomputable def ep0001111010111_0 : Blocks := edgeBlocks% "full/vectors/0001111010111-E-0000.bin"
noncomputable def ep0001111010111 : Blocks := ep0001111010111_0
private theorem idp0001111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111101011.list =
    C ((2:ℤ)^91) * horner X vp0001111010111.list + horner X ep0001111010111.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111010111 : Branch 1 (-981761639/2000000 : ℚ) vp000111101011 := by
  apply branch_checked idp0001111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-981761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-982761639/1000000 : ℚ) by norm_num]
  exact coverp0001111010111
theorem coverp000111101011 : Covers (-981761639/2000000 : ℚ) vp000111101011 := join_branches bp0001111010110 bp0001111010111
private noncomputable def vp0001111010101_0 : Blocks := edgeBlocks% "full/vectors/0001111010101-V-0000.bin"
noncomputable def vp0001111010101 : Blocks := vp0001111010101_0
theorem coverp0001111010101 : Covers (-980761639/1000000 : ℚ) vp0001111010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111010100_0 : Blocks := edgeBlocks% "full/vectors/0001111010100-V-0000.bin"
noncomputable def vp0001111010100 : Blocks := vp0001111010100_0
theorem coverp0001111010100 : Covers (-979761639/1000000 : ℚ) vp0001111010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111101010_0 : Blocks := edgeBlocks% "full/vectors/000111101010-V-0000.bin"
noncomputable def vp000111101010 : Blocks := vp000111101010_0
private theorem bp0001111010100 : Branch 0 (-979761639/2000000 : ℚ) vp000111101010 := by
  apply branch_left_normalized (c:=vp0001111010100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-979761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-979761639/1000000 : ℚ) by norm_num]
  exact coverp0001111010100
private noncomputable def ep0001111010101_0 : Blocks := edgeBlocks% "full/vectors/0001111010101-E-0000.bin"
noncomputable def ep0001111010101 : Blocks := ep0001111010101_0
private theorem idp0001111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111101010.list =
    C ((2:ℤ)^90) * horner X vp0001111010101.list + horner X ep0001111010101.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111010101 : Branch 1 (-979761639/2000000 : ℚ) vp000111101010 := by
  apply branch_checked idp0001111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-979761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-980761639/1000000 : ℚ) by norm_num]
  exact coverp0001111010101
theorem coverp000111101010 : Covers (-979761639/2000000 : ℚ) vp000111101010 := join_branches bp0001111010100 bp0001111010101
private noncomputable def vp00011110101_0 : Blocks := edgeBlocks% "full/vectors/00011110101-V-0000.bin"
private noncomputable def vp00011110101_1 : Blocks := edgeBlocks% "full/vectors/00011110101-V-0001.bin"
noncomputable def vp00011110101 : Blocks := (Blocks.join vp00011110101_0 vp00011110101_1)
private theorem bp000111101010 : Branch 0 (-979761639/4000000 : ℚ) vp00011110101 := by
  apply branch_left_normalized (c:=vp000111101010) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-979761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-979761639/2000000 : ℚ) by norm_num]
  exact coverp000111101010
private noncomputable def ep000111101011_0 : Blocks := edgeBlocks% "full/vectors/000111101011-E-0000.bin"
private noncomputable def ep000111101011_1 : Blocks := edgeBlocks% "full/vectors/000111101011-E-0001.bin"
noncomputable def ep000111101011 : Blocks := (Blocks.join ep000111101011_0 ep000111101011_1)
private theorem idp000111101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011110101.list =
    C ((2:ℤ)^160) * horner X vp000111101011.list + horner X ep000111101011.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111101011 : Branch 1 (-979761639/4000000 : ℚ) vp00011110101 := by
  apply branch_checked idp000111101011 (by positivity) (by decide +kernel)
  rw [show 2*(-979761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-981761639/2000000 : ℚ) by norm_num]
  exact coverp000111101011
theorem coverp00011110101 : Covers (-979761639/4000000 : ℚ) vp00011110101 := join_branches bp000111101010 bp000111101011
private noncomputable def vp0001111010011_0 : Blocks := edgeBlocks% "full/vectors/0001111010011-V-0000.bin"
noncomputable def vp0001111010011 : Blocks := vp0001111010011_0
theorem coverp0001111010011 : Covers (-978761639/1000000 : ℚ) vp0001111010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111010010_0 : Blocks := edgeBlocks% "full/vectors/0001111010010-V-0000.bin"
noncomputable def vp0001111010010 : Blocks := vp0001111010010_0
theorem coverp0001111010010 : Covers (-977761639/1000000 : ℚ) vp0001111010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111101001_0 : Blocks := edgeBlocks% "full/vectors/000111101001-V-0000.bin"
noncomputable def vp000111101001 : Blocks := vp000111101001_0
private theorem bp0001111010010 : Branch 0 (-977761639/2000000 : ℚ) vp000111101001 := by
  apply branch_left_normalized (c:=vp0001111010010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-977761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-977761639/1000000 : ℚ) by norm_num]
  exact coverp0001111010010
private noncomputable def ep0001111010011_0 : Blocks := edgeBlocks% "full/vectors/0001111010011-E-0000.bin"
noncomputable def ep0001111010011 : Blocks := ep0001111010011_0
private theorem idp0001111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111101001.list =
    C ((2:ℤ)^91) * horner X vp0001111010011.list + horner X ep0001111010011.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111010011 : Branch 1 (-977761639/2000000 : ℚ) vp000111101001 := by
  apply branch_checked idp0001111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-977761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-978761639/1000000 : ℚ) by norm_num]
  exact coverp0001111010011
theorem coverp000111101001 : Covers (-977761639/2000000 : ℚ) vp000111101001 := join_branches bp0001111010010 bp0001111010011
private noncomputable def vp0001111010001_0 : Blocks := edgeBlocks% "full/vectors/0001111010001-V-0000.bin"
noncomputable def vp0001111010001 : Blocks := vp0001111010001_0
theorem coverp0001111010001 : Covers (-976761639/1000000 : ℚ) vp0001111010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111010000_0 : Blocks := edgeBlocks% "full/vectors/0001111010000-V-0000.bin"
noncomputable def vp0001111010000 : Blocks := vp0001111010000_0
theorem coverp0001111010000 : Covers (-975761639/1000000 : ℚ) vp0001111010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111101000_0 : Blocks := edgeBlocks% "full/vectors/000111101000-V-0000.bin"
noncomputable def vp000111101000 : Blocks := vp000111101000_0
private theorem bp0001111010000 : Branch 0 (-975761639/2000000 : ℚ) vp000111101000 := by
  apply branch_left_normalized (c:=vp0001111010000) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-975761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-975761639/1000000 : ℚ) by norm_num]
  exact coverp0001111010000
private noncomputable def ep0001111010001_0 : Blocks := edgeBlocks% "full/vectors/0001111010001-E-0000.bin"
noncomputable def ep0001111010001 : Blocks := ep0001111010001_0
private theorem idp0001111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111101000.list =
    C ((2:ℤ)^91) * horner X vp0001111010001.list + horner X ep0001111010001.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111010001 : Branch 1 (-975761639/2000000 : ℚ) vp000111101000 := by
  apply branch_checked idp0001111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-975761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-976761639/1000000 : ℚ) by norm_num]
  exact coverp0001111010001
theorem coverp000111101000 : Covers (-975761639/2000000 : ℚ) vp000111101000 := join_branches bp0001111010000 bp0001111010001
private noncomputable def vp00011110100_0 : Blocks := edgeBlocks% "full/vectors/00011110100-V-0000.bin"
private noncomputable def vp00011110100_1 : Blocks := edgeBlocks% "full/vectors/00011110100-V-0001.bin"
noncomputable def vp00011110100 : Blocks := (Blocks.join vp00011110100_0 vp00011110100_1)
private theorem bp000111101000 : Branch 0 (-975761639/4000000 : ℚ) vp00011110100 := by
  apply branch_left_normalized (c:=vp000111101000) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-975761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-975761639/2000000 : ℚ) by norm_num]
  exact coverp000111101000
private noncomputable def ep000111101001_0 : Blocks := edgeBlocks% "full/vectors/000111101001-E-0000.bin"
private noncomputable def ep000111101001_1 : Blocks := edgeBlocks% "full/vectors/000111101001-E-0001.bin"
noncomputable def ep000111101001 : Blocks := (Blocks.join ep000111101001_0 ep000111101001_1)
private theorem idp000111101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011110100.list =
    C ((2:ℤ)^161) * horner X vp000111101001.list + horner X ep000111101001.list := by
  exact edge_identity (B := (2:ℤ)^318) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111101001 : Branch 1 (-975761639/4000000 : ℚ) vp00011110100 := by
  apply branch_checked idp000111101001 (by positivity) (by decide +kernel)
  rw [show 2*(-975761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-977761639/2000000 : ℚ) by norm_num]
  exact coverp000111101001
theorem coverp00011110100 : Covers (-975761639/4000000 : ℚ) vp00011110100 := join_branches bp000111101000 bp000111101001
private noncomputable def vp0001111010_0 : Blocks := edgeBlocks% "full/vectors/0001111010-V-0000.bin"
private noncomputable def vp0001111010_1 : Blocks := edgeBlocks% "full/vectors/0001111010-V-0001.bin"
private noncomputable def vp0001111010_2 : Blocks := edgeBlocks% "full/vectors/0001111010-V-0002.bin"
noncomputable def vp0001111010 : Blocks := (Blocks.join vp0001111010_0 (Blocks.join vp0001111010_1 vp0001111010_2))
private theorem bp00011110100 : Branch 0 (-975761639/8000000 : ℚ) vp0001111010 := by
  apply branch_left_normalized (c:=vp00011110100) (k:=0) (m:=148) (by decide +kernel)
  rw [show 2*(-975761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-975761639/4000000 : ℚ) by norm_num]
  exact coverp00011110100
private noncomputable def ep00011110101_0 : Blocks := edgeBlocks% "full/vectors/00011110101-E-0000.bin"
private noncomputable def ep00011110101_1 : Blocks := edgeBlocks% "full/vectors/00011110101-E-0001.bin"
private noncomputable def ep00011110101_2 : Blocks := edgeBlocks% "full/vectors/00011110101-E-0002.bin"
noncomputable def ep00011110101 : Blocks := (Blocks.join ep00011110101_0 (Blocks.join ep00011110101_1 ep00011110101_2))
private theorem idp00011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001111010.list =
    C ((2:ℤ)^298) * horner X vp00011110101.list + horner X ep00011110101.list := by
  exact edge_identity (B := (2:ℤ)^509) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011110101 : Branch 1 (-975761639/8000000 : ℚ) vp0001111010 := by
  apply branch_checked idp00011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-975761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-979761639/4000000 : ℚ) by norm_num]
  exact coverp00011110101
theorem coverp0001111010 : Covers (-975761639/8000000 : ℚ) vp0001111010 := join_branches bp00011110100 bp00011110101
private noncomputable def vp000111101_0 : Blocks := edgeBlocks% "full/vectors/000111101-V-0000.bin"
private noncomputable def vp000111101_1 : Blocks := edgeBlocks% "full/vectors/000111101-V-0001.bin"
private noncomputable def vp000111101_2 : Blocks := edgeBlocks% "full/vectors/000111101-V-0002.bin"
private noncomputable def vp000111101_3 : Blocks := edgeBlocks% "full/vectors/000111101-V-0003.bin"
private noncomputable def vp000111101_4 : Blocks := edgeBlocks% "full/vectors/000111101-V-0004.bin"
noncomputable def vp000111101 : Blocks := (Blocks.join (Blocks.join vp000111101_0 vp000111101_1) (Blocks.join vp000111101_2 (Blocks.join vp000111101_3 vp000111101_4)))
private theorem bp0001111010 : Branch 0 (-975761639/16000000 : ℚ) vp000111101 := by
  apply branch_left_normalized (c:=vp0001111010) (k:=0) (m:=273) (by decide +kernel)
  rw [show 2*(-975761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-975761639/8000000 : ℚ) by norm_num]
  exact coverp0001111010
private noncomputable def ep0001111011_0 : Blocks := edgeBlocks% "full/vectors/0001111011-E-0000.bin"
private noncomputable def ep0001111011_1 : Blocks := edgeBlocks% "full/vectors/0001111011-E-0001.bin"
private noncomputable def ep0001111011_2 : Blocks := edgeBlocks% "full/vectors/0001111011-E-0002.bin"
private noncomputable def ep0001111011_3 : Blocks := edgeBlocks% "full/vectors/0001111011-E-0003.bin"
private noncomputable def ep0001111011_4 : Blocks := edgeBlocks% "full/vectors/0001111011-E-0004.bin"
noncomputable def ep0001111011 : Blocks := (Blocks.join (Blocks.join ep0001111011_0 ep0001111011_1) (Blocks.join ep0001111011_2 (Blocks.join ep0001111011_3 ep0001111011_4)))
private theorem idp0001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111101.list =
    C ((2:ℤ)^571) * horner X vp0001111011.list + horner X ep0001111011.list := by
  exact edge_identity (B := (2:ℤ)^892) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111011 : Branch 1 (-975761639/16000000 : ℚ) vp000111101 := by
  apply branch_checked idp0001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-975761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-983761639/8000000 : ℚ) by norm_num]
  exact coverp0001111011
theorem coverp000111101 : Covers (-975761639/16000000 : ℚ) vp000111101 := join_branches bp0001111010 bp0001111011
private noncomputable def vp0001111001111_0 : Blocks := edgeBlocks% "full/vectors/0001111001111-V-0000.bin"
noncomputable def vp0001111001111 : Blocks := vp0001111001111_0
theorem coverp0001111001111 : Covers (-974761639/1000000 : ℚ) vp0001111001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111001110_0 : Blocks := edgeBlocks% "full/vectors/0001111001110-V-0000.bin"
noncomputable def vp0001111001110 : Blocks := vp0001111001110_0
theorem coverp0001111001110 : Covers (-973761639/1000000 : ℚ) vp0001111001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111100111_0 : Blocks := edgeBlocks% "full/vectors/000111100111-V-0000.bin"
noncomputable def vp000111100111 : Blocks := vp000111100111_0
private theorem bp0001111001110 : Branch 0 (-973761639/2000000 : ℚ) vp000111100111 := by
  apply branch_left_normalized (c:=vp0001111001110) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-973761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-973761639/1000000 : ℚ) by norm_num]
  exact coverp0001111001110
private noncomputable def ep0001111001111_0 : Blocks := edgeBlocks% "full/vectors/0001111001111-E-0000.bin"
noncomputable def ep0001111001111 : Blocks := ep0001111001111_0
private theorem idp0001111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111100111.list =
    C ((2:ℤ)^90) * horner X vp0001111001111.list + horner X ep0001111001111.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111001111 : Branch 1 (-973761639/2000000 : ℚ) vp000111100111 := by
  apply branch_checked idp0001111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-973761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-974761639/1000000 : ℚ) by norm_num]
  exact coverp0001111001111
theorem coverp000111100111 : Covers (-973761639/2000000 : ℚ) vp000111100111 := join_branches bp0001111001110 bp0001111001111
private noncomputable def vp0001111001101_0 : Blocks := edgeBlocks% "full/vectors/0001111001101-V-0000.bin"
noncomputable def vp0001111001101 : Blocks := vp0001111001101_0
theorem coverp0001111001101 : Covers (-972761639/1000000 : ℚ) vp0001111001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111001100_0 : Blocks := edgeBlocks% "full/vectors/0001111001100-V-0000.bin"
noncomputable def vp0001111001100 : Blocks := vp0001111001100_0
theorem coverp0001111001100 : Covers (-971761639/1000000 : ℚ) vp0001111001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111100110_0 : Blocks := edgeBlocks% "full/vectors/000111100110-V-0000.bin"
noncomputable def vp000111100110 : Blocks := vp000111100110_0
private theorem bp0001111001100 : Branch 0 (-971761639/2000000 : ℚ) vp000111100110 := by
  apply branch_left_normalized (c:=vp0001111001100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-971761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-971761639/1000000 : ℚ) by norm_num]
  exact coverp0001111001100
private noncomputable def ep0001111001101_0 : Blocks := edgeBlocks% "full/vectors/0001111001101-E-0000.bin"
noncomputable def ep0001111001101 : Blocks := ep0001111001101_0
private theorem idp0001111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111100110.list =
    C ((2:ℤ)^89) * horner X vp0001111001101.list + horner X ep0001111001101.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111001101 : Branch 1 (-971761639/2000000 : ℚ) vp000111100110 := by
  apply branch_checked idp0001111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-971761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-972761639/1000000 : ℚ) by norm_num]
  exact coverp0001111001101
theorem coverp000111100110 : Covers (-971761639/2000000 : ℚ) vp000111100110 := join_branches bp0001111001100 bp0001111001101
private noncomputable def vp00011110011_0 : Blocks := edgeBlocks% "full/vectors/00011110011-V-0000.bin"
private noncomputable def vp00011110011_1 : Blocks := edgeBlocks% "full/vectors/00011110011-V-0001.bin"
noncomputable def vp00011110011 : Blocks := (Blocks.join vp00011110011_0 vp00011110011_1)
private theorem bp000111100110 : Branch 0 (-971761639/4000000 : ℚ) vp00011110011 := by
  apply branch_left_normalized (c:=vp000111100110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-971761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-971761639/2000000 : ℚ) by norm_num]
  exact coverp000111100110
private noncomputable def ep000111100111_0 : Blocks := edgeBlocks% "full/vectors/000111100111-E-0000.bin"
private noncomputable def ep000111100111_1 : Blocks := edgeBlocks% "full/vectors/000111100111-E-0001.bin"
noncomputable def ep000111100111 : Blocks := (Blocks.join ep000111100111_0 ep000111100111_1)
private theorem idp000111100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011110011.list =
    C ((2:ℤ)^160) * horner X vp000111100111.list + horner X ep000111100111.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111100111 : Branch 1 (-971761639/4000000 : ℚ) vp00011110011 := by
  apply branch_checked idp000111100111 (by positivity) (by decide +kernel)
  rw [show 2*(-971761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-973761639/2000000 : ℚ) by norm_num]
  exact coverp000111100111
theorem coverp00011110011 : Covers (-971761639/4000000 : ℚ) vp00011110011 := join_branches bp000111100110 bp000111100111
private noncomputable def vp0001111001011_0 : Blocks := edgeBlocks% "full/vectors/0001111001011-V-0000.bin"
noncomputable def vp0001111001011 : Blocks := vp0001111001011_0
theorem coverp0001111001011 : Covers (-970761639/1000000 : ℚ) vp0001111001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111001010_0 : Blocks := edgeBlocks% "full/vectors/0001111001010-V-0000.bin"
noncomputable def vp0001111001010 : Blocks := vp0001111001010_0
theorem coverp0001111001010 : Covers (-969761639/1000000 : ℚ) vp0001111001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111100101_0 : Blocks := edgeBlocks% "full/vectors/000111100101-V-0000.bin"
noncomputable def vp000111100101 : Blocks := vp000111100101_0
private theorem bp0001111001010 : Branch 0 (-969761639/2000000 : ℚ) vp000111100101 := by
  apply branch_left_normalized (c:=vp0001111001010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-969761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-969761639/1000000 : ℚ) by norm_num]
  exact coverp0001111001010
private noncomputable def ep0001111001011_0 : Blocks := edgeBlocks% "full/vectors/0001111001011-E-0000.bin"
noncomputable def ep0001111001011 : Blocks := ep0001111001011_0
private theorem idp0001111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111100101.list =
    C ((2:ℤ)^89) * horner X vp0001111001011.list + horner X ep0001111001011.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111001011 : Branch 1 (-969761639/2000000 : ℚ) vp000111100101 := by
  apply branch_checked idp0001111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-969761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-970761639/1000000 : ℚ) by norm_num]
  exact coverp0001111001011
theorem coverp000111100101 : Covers (-969761639/2000000 : ℚ) vp000111100101 := join_branches bp0001111001010 bp0001111001011
private noncomputable def vp0001111001001_0 : Blocks := edgeBlocks% "full/vectors/0001111001001-V-0000.bin"
noncomputable def vp0001111001001 : Blocks := vp0001111001001_0
theorem coverp0001111001001 : Covers (-968761639/1000000 : ℚ) vp0001111001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111001000_0 : Blocks := edgeBlocks% "full/vectors/0001111001000-V-0000.bin"
noncomputable def vp0001111001000 : Blocks := vp0001111001000_0
theorem coverp0001111001000 : Covers (-967761639/1000000 : ℚ) vp0001111001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111100100_0 : Blocks := edgeBlocks% "full/vectors/000111100100-V-0000.bin"
noncomputable def vp000111100100 : Blocks := vp000111100100_0
private theorem bp0001111001000 : Branch 0 (-967761639/2000000 : ℚ) vp000111100100 := by
  apply branch_left_normalized (c:=vp0001111001000) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-967761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-967761639/1000000 : ℚ) by norm_num]
  exact coverp0001111001000
private noncomputable def ep0001111001001_0 : Blocks := edgeBlocks% "full/vectors/0001111001001-E-0000.bin"
noncomputable def ep0001111001001 : Blocks := ep0001111001001_0
private theorem idp0001111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111100100.list =
    C ((2:ℤ)^90) * horner X vp0001111001001.list + horner X ep0001111001001.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111001001 : Branch 1 (-967761639/2000000 : ℚ) vp000111100100 := by
  apply branch_checked idp0001111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-967761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-968761639/1000000 : ℚ) by norm_num]
  exact coverp0001111001001
theorem coverp000111100100 : Covers (-967761639/2000000 : ℚ) vp000111100100 := join_branches bp0001111001000 bp0001111001001
private noncomputable def vp00011110010_0 : Blocks := edgeBlocks% "full/vectors/00011110010-V-0000.bin"
private noncomputable def vp00011110010_1 : Blocks := edgeBlocks% "full/vectors/00011110010-V-0001.bin"
noncomputable def vp00011110010 : Blocks := (Blocks.join vp00011110010_0 vp00011110010_1)
private theorem bp000111100100 : Branch 0 (-967761639/4000000 : ℚ) vp00011110010 := by
  apply branch_left_normalized (c:=vp000111100100) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-967761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-967761639/2000000 : ℚ) by norm_num]
  exact coverp000111100100
private noncomputable def ep000111100101_0 : Blocks := edgeBlocks% "full/vectors/000111100101-E-0000.bin"
private noncomputable def ep000111100101_1 : Blocks := edgeBlocks% "full/vectors/000111100101-E-0001.bin"
noncomputable def ep000111100101 : Blocks := (Blocks.join ep000111100101_0 ep000111100101_1)
private theorem idp000111100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011110010.list =
    C ((2:ℤ)^160) * horner X vp000111100101.list + horner X ep000111100101.list := by
  exact edge_identity (B := (2:ℤ)^316) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111100101 : Branch 1 (-967761639/4000000 : ℚ) vp00011110010 := by
  apply branch_checked idp000111100101 (by positivity) (by decide +kernel)
  rw [show 2*(-967761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-969761639/2000000 : ℚ) by norm_num]
  exact coverp000111100101
theorem coverp00011110010 : Covers (-967761639/4000000 : ℚ) vp00011110010 := join_branches bp000111100100 bp000111100101
private noncomputable def vp0001111001_0 : Blocks := edgeBlocks% "full/vectors/0001111001-V-0000.bin"
private noncomputable def vp0001111001_1 : Blocks := edgeBlocks% "full/vectors/0001111001-V-0001.bin"
private noncomputable def vp0001111001_2 : Blocks := edgeBlocks% "full/vectors/0001111001-V-0002.bin"
noncomputable def vp0001111001 : Blocks := (Blocks.join vp0001111001_0 (Blocks.join vp0001111001_1 vp0001111001_2))
private theorem bp00011110010 : Branch 0 (-967761639/8000000 : ℚ) vp0001111001 := by
  apply branch_left_normalized (c:=vp00011110010) (k:=0) (m:=147) (by decide +kernel)
  rw [show 2*(-967761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-967761639/4000000 : ℚ) by norm_num]
  exact coverp00011110010
private noncomputable def ep00011110011_0 : Blocks := edgeBlocks% "full/vectors/00011110011-E-0000.bin"
private noncomputable def ep00011110011_1 : Blocks := edgeBlocks% "full/vectors/00011110011-E-0001.bin"
private noncomputable def ep00011110011_2 : Blocks := edgeBlocks% "full/vectors/00011110011-E-0002.bin"
noncomputable def ep00011110011 : Blocks := (Blocks.join ep00011110011_0 (Blocks.join ep00011110011_1 ep00011110011_2))
private theorem idp00011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001111001.list =
    C ((2:ℤ)^298) * horner X vp00011110011.list + horner X ep00011110011.list := by
  exact edge_identity (B := (2:ℤ)^510) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011110011 : Branch 1 (-967761639/8000000 : ℚ) vp0001111001 := by
  apply branch_checked idp00011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-967761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-971761639/4000000 : ℚ) by norm_num]
  exact coverp00011110011
theorem coverp0001111001 : Covers (-967761639/8000000 : ℚ) vp0001111001 := join_branches bp00011110010 bp00011110011
private noncomputable def vp0001111000111_0 : Blocks := edgeBlocks% "full/vectors/0001111000111-V-0000.bin"
noncomputable def vp0001111000111 : Blocks := vp0001111000111_0
theorem coverp0001111000111 : Covers (-966761639/1000000 : ℚ) vp0001111000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111000110_0 : Blocks := edgeBlocks% "full/vectors/0001111000110-V-0000.bin"
noncomputable def vp0001111000110 : Blocks := vp0001111000110_0
theorem coverp0001111000110 : Covers (-965761639/1000000 : ℚ) vp0001111000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000111100011_0 : Blocks := edgeBlocks% "full/vectors/000111100011-V-0000.bin"
noncomputable def vp000111100011 : Blocks := vp000111100011_0
private theorem bp0001111000110 : Branch 0 (-965761639/2000000 : ℚ) vp000111100011 := by
  apply branch_left_normalized (c:=vp0001111000110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-965761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-965761639/1000000 : ℚ) by norm_num]
  exact coverp0001111000110
private noncomputable def ep0001111000111_0 : Blocks := edgeBlocks% "full/vectors/0001111000111-E-0000.bin"
noncomputable def ep0001111000111 : Blocks := ep0001111000111_0
private theorem idp0001111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111100011.list =
    C ((2:ℤ)^91) * horner X vp0001111000111.list + horner X ep0001111000111.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111000111 : Branch 1 (-965761639/2000000 : ℚ) vp000111100011 := by
  apply branch_checked idp0001111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-965761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-966761639/1000000 : ℚ) by norm_num]
  exact coverp0001111000111
theorem coverp000111100011 : Covers (-965761639/2000000 : ℚ) vp000111100011 := join_branches bp0001111000110 bp0001111000111
private noncomputable def vp0001111000101_0 : Blocks := edgeBlocks% "full/vectors/0001111000101-V-0000.bin"
noncomputable def vp0001111000101 : Blocks := vp0001111000101_0
theorem coverp0001111000101 : Covers (-964761639/1000000 : ℚ) vp0001111000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111000100_0 : Blocks := edgeBlocks% "full/vectors/0001111000100-V-0000.bin"
noncomputable def vp0001111000100 : Blocks := vp0001111000100_0
theorem coverp0001111000100 : Covers (-963761639/1000000 : ℚ) vp0001111000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000111100010_0 : Blocks := edgeBlocks% "full/vectors/000111100010-V-0000.bin"
noncomputable def vp000111100010 : Blocks := vp000111100010_0
private theorem bp0001111000100 : Branch 0 (-963761639/2000000 : ℚ) vp000111100010 := by
  apply branch_left_normalized (c:=vp0001111000100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-963761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-963761639/1000000 : ℚ) by norm_num]
  exact coverp0001111000100
private noncomputable def ep0001111000101_0 : Blocks := edgeBlocks% "full/vectors/0001111000101-E-0000.bin"
noncomputable def ep0001111000101 : Blocks := ep0001111000101_0
private theorem idp0001111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111100010.list =
    C ((2:ℤ)^89) * horner X vp0001111000101.list + horner X ep0001111000101.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111000101 : Branch 1 (-963761639/2000000 : ℚ) vp000111100010 := by
  apply branch_checked idp0001111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-963761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-964761639/1000000 : ℚ) by norm_num]
  exact coverp0001111000101
theorem coverp000111100010 : Covers (-963761639/2000000 : ℚ) vp000111100010 := join_branches bp0001111000100 bp0001111000101
private noncomputable def vp00011110001_0 : Blocks := edgeBlocks% "full/vectors/00011110001-V-0000.bin"
private noncomputable def vp00011110001_1 : Blocks := edgeBlocks% "full/vectors/00011110001-V-0001.bin"
noncomputable def vp00011110001 : Blocks := (Blocks.join vp00011110001_0 vp00011110001_1)
private theorem bp000111100010 : Branch 0 (-963761639/4000000 : ℚ) vp00011110001 := by
  apply branch_left_normalized (c:=vp000111100010) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-963761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-963761639/2000000 : ℚ) by norm_num]
  exact coverp000111100010
private noncomputable def ep000111100011_0 : Blocks := edgeBlocks% "full/vectors/000111100011-E-0000.bin"
private noncomputable def ep000111100011_1 : Blocks := edgeBlocks% "full/vectors/000111100011-E-0001.bin"
noncomputable def ep000111100011 : Blocks := (Blocks.join ep000111100011_0 ep000111100011_1)
private theorem idp000111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011110001.list =
    C ((2:ℤ)^158) * horner X vp000111100011.list + horner X ep000111100011.list := by
  exact edge_identity (B := (2:ℤ)^316) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111100011 : Branch 1 (-963761639/4000000 : ℚ) vp00011110001 := by
  apply branch_checked idp000111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-963761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-965761639/2000000 : ℚ) by norm_num]
  exact coverp000111100011
theorem coverp00011110001 : Covers (-963761639/4000000 : ℚ) vp00011110001 := join_branches bp000111100010 bp000111100011
private noncomputable def vp0001111000011_0 : Blocks := edgeBlocks% "full/vectors/0001111000011-V-0000.bin"
noncomputable def vp0001111000011 : Blocks := vp0001111000011_0
theorem coverp0001111000011 : Covers (-962761639/1000000 : ℚ) vp0001111000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111000010_0 : Blocks := edgeBlocks% "full/vectors/0001111000010-V-0000.bin"
noncomputable def vp0001111000010 : Blocks := vp0001111000010_0
theorem coverp0001111000010 : Covers (-961761639/1000000 : ℚ) vp0001111000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000111100001_0 : Blocks := edgeBlocks% "full/vectors/000111100001-V-0000.bin"
noncomputable def vp000111100001 : Blocks := vp000111100001_0
private theorem bp0001111000010 : Branch 0 (-961761639/2000000 : ℚ) vp000111100001 := by
  apply branch_left_normalized (c:=vp0001111000010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-961761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-961761639/1000000 : ℚ) by norm_num]
  exact coverp0001111000010
private noncomputable def ep0001111000011_0 : Blocks := edgeBlocks% "full/vectors/0001111000011-E-0000.bin"
noncomputable def ep0001111000011 : Blocks := ep0001111000011_0
private theorem idp0001111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111100001.list =
    C ((2:ℤ)^89) * horner X vp0001111000011.list + horner X ep0001111000011.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111000011 : Branch 1 (-961761639/2000000 : ℚ) vp000111100001 := by
  apply branch_checked idp0001111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-961761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-962761639/1000000 : ℚ) by norm_num]
  exact coverp0001111000011
theorem coverp000111100001 : Covers (-961761639/2000000 : ℚ) vp000111100001 := join_branches bp0001111000010 bp0001111000011
private noncomputable def vp0001111000001_0 : Blocks := edgeBlocks% "full/vectors/0001111000001-V-0000.bin"
noncomputable def vp0001111000001 : Blocks := vp0001111000001_0
theorem coverp0001111000001 : Covers (-960761639/1000000 : ℚ) vp0001111000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001111000000_0 : Blocks := edgeBlocks% "full/vectors/0001111000000-V-0000.bin"
noncomputable def vp0001111000000 : Blocks := vp0001111000000_0
theorem coverp0001111000000 : Covers (-959761639/1000000 : ℚ) vp0001111000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000111100000_0 : Blocks := edgeBlocks% "full/vectors/000111100000-V-0000.bin"
noncomputable def vp000111100000 : Blocks := vp000111100000_0
private theorem bp0001111000000 : Branch 0 (-959761639/2000000 : ℚ) vp000111100000 := by
  apply branch_left_normalized (c:=vp0001111000000) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-959761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-959761639/1000000 : ℚ) by norm_num]
  exact coverp0001111000000
private noncomputable def ep0001111000001_0 : Blocks := edgeBlocks% "full/vectors/0001111000001-E-0000.bin"
noncomputable def ep0001111000001 : Blocks := ep0001111000001_0
private theorem idp0001111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111100000.list =
    C ((2:ℤ)^90) * horner X vp0001111000001.list + horner X ep0001111000001.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111000001 : Branch 1 (-959761639/2000000 : ℚ) vp000111100000 := by
  apply branch_checked idp0001111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-959761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-960761639/1000000 : ℚ) by norm_num]
  exact coverp0001111000001
theorem coverp000111100000 : Covers (-959761639/2000000 : ℚ) vp000111100000 := join_branches bp0001111000000 bp0001111000001
private noncomputable def vp00011110000_0 : Blocks := edgeBlocks% "full/vectors/00011110000-V-0000.bin"
private noncomputable def vp00011110000_1 : Blocks := edgeBlocks% "full/vectors/00011110000-V-0001.bin"
noncomputable def vp00011110000 : Blocks := (Blocks.join vp00011110000_0 vp00011110000_1)
private theorem bp000111100000 : Branch 0 (-959761639/4000000 : ℚ) vp00011110000 := by
  apply branch_left_normalized (c:=vp000111100000) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-959761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-959761639/2000000 : ℚ) by norm_num]
  exact coverp000111100000
private noncomputable def ep000111100001_0 : Blocks := edgeBlocks% "full/vectors/000111100001-E-0000.bin"
private noncomputable def ep000111100001_1 : Blocks := edgeBlocks% "full/vectors/000111100001-E-0001.bin"
noncomputable def ep000111100001 : Blocks := (Blocks.join ep000111100001_0 ep000111100001_1)
private theorem idp000111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011110000.list =
    C ((2:ℤ)^160) * horner X vp000111100001.list + horner X ep000111100001.list := by
  exact edge_identity (B := (2:ℤ)^315) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111100001 : Branch 1 (-959761639/4000000 : ℚ) vp00011110000 := by
  apply branch_checked idp000111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-959761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-961761639/2000000 : ℚ) by norm_num]
  exact coverp000111100001
theorem coverp00011110000 : Covers (-959761639/4000000 : ℚ) vp00011110000 := join_branches bp000111100000 bp000111100001
private noncomputable def vp0001111000_0 : Blocks := edgeBlocks% "full/vectors/0001111000-V-0000.bin"
private noncomputable def vp0001111000_1 : Blocks := edgeBlocks% "full/vectors/0001111000-V-0001.bin"
private noncomputable def vp0001111000_2 : Blocks := edgeBlocks% "full/vectors/0001111000-V-0002.bin"
noncomputable def vp0001111000 : Blocks := (Blocks.join vp0001111000_0 (Blocks.join vp0001111000_1 vp0001111000_2))
private theorem bp00011110000 : Branch 0 (-959761639/8000000 : ℚ) vp0001111000 := by
  apply branch_left_normalized (c:=vp00011110000) (k:=0) (m:=147) (by decide +kernel)
  rw [show 2*(-959761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-959761639/4000000 : ℚ) by norm_num]
  exact coverp00011110000
private noncomputable def ep00011110001_0 : Blocks := edgeBlocks% "full/vectors/00011110001-E-0000.bin"
private noncomputable def ep00011110001_1 : Blocks := edgeBlocks% "full/vectors/00011110001-E-0001.bin"
private noncomputable def ep00011110001_2 : Blocks := edgeBlocks% "full/vectors/00011110001-E-0002.bin"
noncomputable def ep00011110001 : Blocks := (Blocks.join ep00011110001_0 (Blocks.join ep00011110001_1 ep00011110001_2))
private theorem idp00011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001111000.list =
    C ((2:ℤ)^297) * horner X vp00011110001.list + horner X ep00011110001.list := by
  exact edge_identity (B := (2:ℤ)^509) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011110001 : Branch 1 (-959761639/8000000 : ℚ) vp0001111000 := by
  apply branch_checked idp00011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-959761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-963761639/4000000 : ℚ) by norm_num]
  exact coverp00011110001
theorem coverp0001111000 : Covers (-959761639/8000000 : ℚ) vp0001111000 := join_branches bp00011110000 bp00011110001
private noncomputable def vp000111100_0 : Blocks := edgeBlocks% "full/vectors/000111100-V-0000.bin"
private noncomputable def vp000111100_1 : Blocks := edgeBlocks% "full/vectors/000111100-V-0001.bin"
private noncomputable def vp000111100_2 : Blocks := edgeBlocks% "full/vectors/000111100-V-0002.bin"
private noncomputable def vp000111100_3 : Blocks := edgeBlocks% "full/vectors/000111100-V-0003.bin"
private noncomputable def vp000111100_4 : Blocks := edgeBlocks% "full/vectors/000111100-V-0004.bin"
noncomputable def vp000111100 : Blocks := (Blocks.join (Blocks.join vp000111100_0 vp000111100_1) (Blocks.join vp000111100_2 (Blocks.join vp000111100_3 vp000111100_4)))
private theorem bp0001111000 : Branch 0 (-959761639/16000000 : ℚ) vp000111100 := by
  apply branch_left_normalized (c:=vp0001111000) (k:=0) (m:=274) (by decide +kernel)
  rw [show 2*(-959761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-959761639/8000000 : ℚ) by norm_num]
  exact coverp0001111000
private noncomputable def ep0001111001_0 : Blocks := edgeBlocks% "full/vectors/0001111001-E-0000.bin"
private noncomputable def ep0001111001_1 : Blocks := edgeBlocks% "full/vectors/0001111001-E-0001.bin"
private noncomputable def ep0001111001_2 : Blocks := edgeBlocks% "full/vectors/0001111001-E-0002.bin"
private noncomputable def ep0001111001_3 : Blocks := edgeBlocks% "full/vectors/0001111001-E-0003.bin"
private noncomputable def ep0001111001_4 : Blocks := edgeBlocks% "full/vectors/0001111001-E-0004.bin"
noncomputable def ep0001111001 : Blocks := (Blocks.join (Blocks.join ep0001111001_0 ep0001111001_1) (Blocks.join ep0001111001_2 (Blocks.join ep0001111001_3 ep0001111001_4)))
private theorem idp0001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000111100.list =
    C ((2:ℤ)^572) * horner X vp0001111001.list + horner X ep0001111001.list := by
  exact edge_identity (B := (2:ℤ)^895) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001111001 : Branch 1 (-959761639/16000000 : ℚ) vp000111100 := by
  apply branch_checked idp0001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-959761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-967761639/8000000 : ℚ) by norm_num]
  exact coverp0001111001
theorem coverp000111100 : Covers (-959761639/16000000 : ℚ) vp000111100 := join_branches bp0001111000 bp0001111001
private noncomputable def vp00011110_0 : Blocks := edgeBlocks% "full/vectors/00011110-V-0000.bin"
private noncomputable def vp00011110_1 : Blocks := edgeBlocks% "full/vectors/00011110-V-0001.bin"
private noncomputable def vp00011110_2 : Blocks := edgeBlocks% "full/vectors/00011110-V-0002.bin"
private noncomputable def vp00011110_3 : Blocks := edgeBlocks% "full/vectors/00011110-V-0003.bin"
private noncomputable def vp00011110_4 : Blocks := edgeBlocks% "full/vectors/00011110-V-0004.bin"
private noncomputable def vp00011110_5 : Blocks := edgeBlocks% "full/vectors/00011110-V-0005.bin"
private noncomputable def vp00011110_6 : Blocks := edgeBlocks% "full/vectors/00011110-V-0006.bin"
private noncomputable def vp00011110_7 : Blocks := edgeBlocks% "full/vectors/00011110-V-0007.bin"
noncomputable def vp00011110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00011110_0 vp00011110_1) (Blocks.join vp00011110_2 vp00011110_3)) (Blocks.join (Blocks.join vp00011110_4 vp00011110_5) (Blocks.join vp00011110_6 vp00011110_7)))
private theorem bp000111100 : Branch 0 (-959761639/32000000 : ℚ) vp00011110 := by
  apply branch_left_normalized (c:=vp000111100) (k:=0) (m:=526) (by decide +kernel)
  rw [show 2*(-959761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-959761639/16000000 : ℚ) by norm_num]
  exact coverp000111100
private noncomputable def ep000111101_0 : Blocks := edgeBlocks% "full/vectors/000111101-E-0000.bin"
private noncomputable def ep000111101_1 : Blocks := edgeBlocks% "full/vectors/000111101-E-0001.bin"
private noncomputable def ep000111101_2 : Blocks := edgeBlocks% "full/vectors/000111101-E-0002.bin"
private noncomputable def ep000111101_3 : Blocks := edgeBlocks% "full/vectors/000111101-E-0003.bin"
private noncomputable def ep000111101_4 : Blocks := edgeBlocks% "full/vectors/000111101-E-0004.bin"
private noncomputable def ep000111101_5 : Blocks := edgeBlocks% "full/vectors/000111101-E-0005.bin"
private noncomputable def ep000111101_6 : Blocks := edgeBlocks% "full/vectors/000111101-E-0006.bin"
private noncomputable def ep000111101_7 : Blocks := edgeBlocks% "full/vectors/000111101-E-0007.bin"
noncomputable def ep000111101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000111101_0 ep000111101_1) (Blocks.join ep000111101_2 ep000111101_3)) (Blocks.join (Blocks.join ep000111101_4 ep000111101_5) (Blocks.join ep000111101_6 ep000111101_7)))
private theorem idp000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011110.list =
    C ((2:ℤ)^1112) * horner X vp000111101.list + horner X ep000111101.list := by
  exact edge_identity (B := (2:ℤ)^1658) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000111101 : Branch 1 (-959761639/32000000 : ℚ) vp00011110 := by
  apply branch_checked idp000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-959761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-975761639/16000000 : ℚ) by norm_num]
  exact coverp000111101
theorem coverp00011110 : Covers (-959761639/32000000 : ℚ) vp00011110 := join_branches bp000111100 bp000111101
private noncomputable def vp0001111_0 : Blocks := edgeBlocks% "full/vectors/0001111-V-0000.bin"
private noncomputable def vp0001111_1 : Blocks := edgeBlocks% "full/vectors/0001111-V-0001.bin"
private noncomputable def vp0001111_2 : Blocks := edgeBlocks% "full/vectors/0001111-V-0002.bin"
private noncomputable def vp0001111_3 : Blocks := edgeBlocks% "full/vectors/0001111-V-0003.bin"
private noncomputable def vp0001111_4 : Blocks := edgeBlocks% "full/vectors/0001111-V-0004.bin"
private noncomputable def vp0001111_5 : Blocks := edgeBlocks% "full/vectors/0001111-V-0005.bin"
private noncomputable def vp0001111_6 : Blocks := edgeBlocks% "full/vectors/0001111-V-0006.bin"
private noncomputable def vp0001111_7 : Blocks := edgeBlocks% "full/vectors/0001111-V-0007.bin"
private noncomputable def vp0001111_8 : Blocks := edgeBlocks% "full/vectors/0001111-V-0008.bin"
private noncomputable def vp0001111_9 : Blocks := edgeBlocks% "full/vectors/0001111-V-0009.bin"
private noncomputable def vp0001111_10 : Blocks := edgeBlocks% "full/vectors/0001111-V-0010.bin"
private noncomputable def vp0001111_11 : Blocks := edgeBlocks% "full/vectors/0001111-V-0011.bin"
private noncomputable def vp0001111_12 : Blocks := edgeBlocks% "full/vectors/0001111-V-0012.bin"
private noncomputable def vp0001111_13 : Blocks := edgeBlocks% "full/vectors/0001111-V-0013.bin"
private noncomputable def vp0001111_14 : Blocks := edgeBlocks% "full/vectors/0001111-V-0014.bin"
private noncomputable def vp0001111_15 : Blocks := edgeBlocks% "full/vectors/0001111-V-0015.bin"
noncomputable def vp0001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0001111_0 vp0001111_1) (Blocks.join vp0001111_2 vp0001111_3)) (Blocks.join (Blocks.join vp0001111_4 vp0001111_5) (Blocks.join vp0001111_6 vp0001111_7))) (Blocks.join (Blocks.join (Blocks.join vp0001111_8 vp0001111_9) (Blocks.join vp0001111_10 vp0001111_11)) (Blocks.join (Blocks.join vp0001111_12 vp0001111_13) (Blocks.join vp0001111_14 vp0001111_15))))
private theorem bp00011110 : Branch 0 (-959761639/64000000 : ℚ) vp0001111 := by
  apply branch_left_normalized (c:=vp00011110) (k:=0) (m:=1021) (by decide +kernel)
  rw [show 2*(-959761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-959761639/32000000 : ℚ) by norm_num]
  exact coverp00011110
private noncomputable def ep00011111_0 : Blocks := edgeBlocks% "full/vectors/00011111-E-0000.bin"
private noncomputable def ep00011111_1 : Blocks := edgeBlocks% "full/vectors/00011111-E-0001.bin"
private noncomputable def ep00011111_2 : Blocks := edgeBlocks% "full/vectors/00011111-E-0002.bin"
private noncomputable def ep00011111_3 : Blocks := edgeBlocks% "full/vectors/00011111-E-0003.bin"
private noncomputable def ep00011111_4 : Blocks := edgeBlocks% "full/vectors/00011111-E-0004.bin"
private noncomputable def ep00011111_5 : Blocks := edgeBlocks% "full/vectors/00011111-E-0005.bin"
private noncomputable def ep00011111_6 : Blocks := edgeBlocks% "full/vectors/00011111-E-0006.bin"
private noncomputable def ep00011111_7 : Blocks := edgeBlocks% "full/vectors/00011111-E-0007.bin"
private noncomputable def ep00011111_8 : Blocks := edgeBlocks% "full/vectors/00011111-E-0008.bin"
private noncomputable def ep00011111_9 : Blocks := edgeBlocks% "full/vectors/00011111-E-0009.bin"
private noncomputable def ep00011111_10 : Blocks := edgeBlocks% "full/vectors/00011111-E-0010.bin"
private noncomputable def ep00011111_11 : Blocks := edgeBlocks% "full/vectors/00011111-E-0011.bin"
private noncomputable def ep00011111_12 : Blocks := edgeBlocks% "full/vectors/00011111-E-0012.bin"
private noncomputable def ep00011111_13 : Blocks := edgeBlocks% "full/vectors/00011111-E-0013.bin"
private noncomputable def ep00011111_14 : Blocks := edgeBlocks% "full/vectors/00011111-E-0014.bin"
private noncomputable def ep00011111_15 : Blocks := edgeBlocks% "full/vectors/00011111-E-0015.bin"
noncomputable def ep00011111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00011111_0 ep00011111_1) (Blocks.join ep00011111_2 ep00011111_3)) (Blocks.join (Blocks.join ep00011111_4 ep00011111_5) (Blocks.join ep00011111_6 ep00011111_7))) (Blocks.join (Blocks.join (Blocks.join ep00011111_8 ep00011111_9) (Blocks.join ep00011111_10 ep00011111_11)) (Blocks.join (Blocks.join ep00011111_12 ep00011111_13) (Blocks.join ep00011111_14 ep00011111_15))))
private theorem idp00011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001111.list =
    C ((2:ℤ)^2173) * horner X vp00011111.list + horner X ep00011111.list := by
  exact edge_identity (B := (2:ℤ)^3157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011111 : Branch 1 (-959761639/64000000 : ℚ) vp0001111 := by
  apply branch_checked idp00011111 (by positivity) (by decide +kernel)
  rw [show 2*(-959761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-991761639/32000000 : ℚ) by norm_num]
  exact coverp00011111
theorem coverp0001111 : Covers (-959761639/64000000 : ℚ) vp0001111 := join_branches bp00011110 bp00011111
end NextProof.EdgeFull

