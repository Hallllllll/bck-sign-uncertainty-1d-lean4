import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000000111111111_0 : Blocks := edgeBlocks% "full/vectors/00000000111111111-V-0000.bin"
noncomputable def vp00000000111111111 : Blocks := vp00000000111111111_0
theorem coverp00000000111111111 : Covers (-31699139/62500 : ℚ) vp00000000111111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111111110_0 : Blocks := edgeBlocks% "full/vectors/00000000111111110-V-0000.bin"
noncomputable def vp00000000111111110 : Blocks := vp00000000111111110_0
theorem coverp00000000111111110 : Covers (-31636639/62500 : ℚ) vp00000000111111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011111111_0 : Blocks := edgeBlocks% "full/vectors/0000000011111111-V-0000.bin"
noncomputable def vp0000000011111111 : Blocks := vp0000000011111111_0
private theorem bp00000000111111110 : Branch 0 (-31636639/125000 : ℚ) vp0000000011111111 := by
  apply branch_left_normalized (c:=vp00000000111111110) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-31636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-31636639/62500 : ℚ) by norm_num]
  exact coverp00000000111111110
private noncomputable def ep00000000111111111_0 : Blocks := edgeBlocks% "full/vectors/00000000111111111-E-0000.bin"
noncomputable def ep00000000111111111 : Blocks := ep00000000111111111_0
private theorem idp00000000111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011111111.list =
    C ((2:ℤ)^41) * horner X vp00000000111111111.list + horner X ep00000000111111111.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111111111 : Branch 1 (-31636639/125000 : ℚ) vp0000000011111111 := by
  apply branch_checked idp00000000111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-31636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-31699139/62500 : ℚ) by norm_num]
  exact coverp00000000111111111
theorem coverp0000000011111111 : Covers (-31636639/125000 : ℚ) vp0000000011111111 := join_branches bp00000000111111110 bp00000000111111111
private noncomputable def vp00000000111111101_0 : Blocks := edgeBlocks% "full/vectors/00000000111111101-V-0000.bin"
noncomputable def vp00000000111111101 : Blocks := vp00000000111111101_0
theorem coverp00000000111111101 : Covers (-31574139/62500 : ℚ) vp00000000111111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111111100_0 : Blocks := edgeBlocks% "full/vectors/00000000111111100-V-0000.bin"
noncomputable def vp00000000111111100 : Blocks := vp00000000111111100_0
theorem coverp00000000111111100 : Covers (-31511639/62500 : ℚ) vp00000000111111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011111110_0 : Blocks := edgeBlocks% "full/vectors/0000000011111110-V-0000.bin"
noncomputable def vp0000000011111110 : Blocks := vp0000000011111110_0
private theorem bp00000000111111100 : Branch 0 (-31511639/125000 : ℚ) vp0000000011111110 := by
  apply branch_left_normalized (c:=vp00000000111111100) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-31511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-31511639/62500 : ℚ) by norm_num]
  exact coverp00000000111111100
private noncomputable def ep00000000111111101_0 : Blocks := edgeBlocks% "full/vectors/00000000111111101-E-0000.bin"
noncomputable def ep00000000111111101 : Blocks := ep00000000111111101_0
private theorem idp00000000111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011111110.list =
    C ((2:ℤ)^42) * horner X vp00000000111111101.list + horner X ep00000000111111101.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111111101 : Branch 1 (-31511639/125000 : ℚ) vp0000000011111110 := by
  apply branch_checked idp00000000111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-31511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-31574139/62500 : ℚ) by norm_num]
  exact coverp00000000111111101
theorem coverp0000000011111110 : Covers (-31511639/125000 : ℚ) vp0000000011111110 := join_branches bp00000000111111100 bp00000000111111101
private noncomputable def vp000000001111111_0 : Blocks := edgeBlocks% "full/vectors/000000001111111-V-0000.bin"
noncomputable def vp000000001111111 : Blocks := vp000000001111111_0
private theorem bp0000000011111110 : Branch 0 (-31511639/250000 : ℚ) vp000000001111111 := by
  apply branch_left_normalized (c:=vp0000000011111110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-31511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-31511639/125000 : ℚ) by norm_num]
  exact coverp0000000011111110
private noncomputable def ep0000000011111111_0 : Blocks := edgeBlocks% "full/vectors/0000000011111111-E-0000.bin"
noncomputable def ep0000000011111111 : Blocks := ep0000000011111111_0
private theorem idp0000000011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001111111.list =
    C ((2:ℤ)^65) * horner X vp0000000011111111.list + horner X ep0000000011111111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011111111 : Branch 1 (-31511639/250000 : ℚ) vp000000001111111 := by
  apply branch_checked idp0000000011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-31511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-31636639/125000 : ℚ) by norm_num]
  exact coverp0000000011111111
theorem coverp000000001111111 : Covers (-31511639/250000 : ℚ) vp000000001111111 := join_branches bp0000000011111110 bp0000000011111111
private noncomputable def vp00000000111111011_0 : Blocks := edgeBlocks% "full/vectors/00000000111111011-V-0000.bin"
noncomputable def vp00000000111111011 : Blocks := vp00000000111111011_0
theorem coverp00000000111111011 : Covers (-31449139/62500 : ℚ) vp00000000111111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111111010_0 : Blocks := edgeBlocks% "full/vectors/00000000111111010-V-0000.bin"
noncomputable def vp00000000111111010 : Blocks := vp00000000111111010_0
theorem coverp00000000111111010 : Covers (-31386639/62500 : ℚ) vp00000000111111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011111101_0 : Blocks := edgeBlocks% "full/vectors/0000000011111101-V-0000.bin"
noncomputable def vp0000000011111101 : Blocks := vp0000000011111101_0
private theorem bp00000000111111010 : Branch 0 (-31386639/125000 : ℚ) vp0000000011111101 := by
  apply branch_left_normalized (c:=vp00000000111111010) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-31386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-31386639/62500 : ℚ) by norm_num]
  exact coverp00000000111111010
private noncomputable def ep00000000111111011_0 : Blocks := edgeBlocks% "full/vectors/00000000111111011-E-0000.bin"
noncomputable def ep00000000111111011 : Blocks := ep00000000111111011_0
private theorem idp00000000111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011111101.list =
    C ((2:ℤ)^41) * horner X vp00000000111111011.list + horner X ep00000000111111011.list := by
  exact edge_identity (B := (2:ℤ)^154) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111111011 : Branch 1 (-31386639/125000 : ℚ) vp0000000011111101 := by
  apply branch_checked idp00000000111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-31386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-31449139/62500 : ℚ) by norm_num]
  exact coverp00000000111111011
theorem coverp0000000011111101 : Covers (-31386639/125000 : ℚ) vp0000000011111101 := join_branches bp00000000111111010 bp00000000111111011
private noncomputable def vp0000000011111100_0 : Blocks := edgeBlocks% "full/vectors/0000000011111100-V-0000.bin"
noncomputable def vp0000000011111100 : Blocks := vp0000000011111100_0
theorem coverp0000000011111100 : Covers (-31261639/125000 : ℚ) vp0000000011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001111110_0 : Blocks := edgeBlocks% "full/vectors/000000001111110-V-0000.bin"
noncomputable def vp000000001111110 : Blocks := vp000000001111110_0
private theorem bp0000000011111100 : Branch 0 (-31261639/250000 : ℚ) vp000000001111110 := by
  apply branch_left_normalized (c:=vp0000000011111100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-31261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-31261639/125000 : ℚ) by norm_num]
  exact coverp0000000011111100
private noncomputable def ep0000000011111101_0 : Blocks := edgeBlocks% "full/vectors/0000000011111101-E-0000.bin"
noncomputable def ep0000000011111101 : Blocks := ep0000000011111101_0
private theorem idp0000000011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001111110.list =
    C ((2:ℤ)^66) * horner X vp0000000011111101.list + horner X ep0000000011111101.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011111101 : Branch 1 (-31261639/250000 : ℚ) vp000000001111110 := by
  apply branch_checked idp0000000011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-31261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-31386639/125000 : ℚ) by norm_num]
  exact coverp0000000011111101
theorem coverp000000001111110 : Covers (-31261639/250000 : ℚ) vp000000001111110 := join_branches bp0000000011111100 bp0000000011111101
private noncomputable def vp00000000111111_0 : Blocks := edgeBlocks% "full/vectors/00000000111111-V-0000.bin"
noncomputable def vp00000000111111 : Blocks := vp00000000111111_0
private theorem bp000000001111110 : Branch 0 (-31261639/500000 : ℚ) vp00000000111111 := by
  apply branch_left_normalized (c:=vp000000001111110) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-31261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-31261639/250000 : ℚ) by norm_num]
  exact coverp000000001111110
private noncomputable def ep000000001111111_0 : Blocks := edgeBlocks% "full/vectors/000000001111111-E-0000.bin"
noncomputable def ep000000001111111 : Blocks := ep000000001111111_0
private theorem idp000000001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111111.list =
    C ((2:ℤ)^110) * horner X vp000000001111111.list + horner X ep000000001111111.list := by
  exact edge_identity (B := (2:ℤ)^257) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001111111 : Branch 1 (-31261639/500000 : ℚ) vp00000000111111 := by
  apply branch_checked idp000000001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-31261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-31511639/250000 : ℚ) by norm_num]
  exact coverp000000001111111
theorem coverp00000000111111 : Covers (-31261639/500000 : ℚ) vp00000000111111 := join_branches bp000000001111110 bp000000001111111
private noncomputable def vp0000000011111011_0 : Blocks := edgeBlocks% "full/vectors/0000000011111011-V-0000.bin"
noncomputable def vp0000000011111011 : Blocks := vp0000000011111011_0
theorem coverp0000000011111011 : Covers (-31136639/125000 : ℚ) vp0000000011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111110101_0 : Blocks := edgeBlocks% "full/vectors/00000000111110101-V-0000.bin"
noncomputable def vp00000000111110101 : Blocks := vp00000000111110101_0
theorem coverp00000000111110101 : Covers (-31074139/62500 : ℚ) vp00000000111110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111110100_0 : Blocks := edgeBlocks% "full/vectors/00000000111110100-V-0000.bin"
noncomputable def vp00000000111110100 : Blocks := vp00000000111110100_0
theorem coverp00000000111110100 : Covers (-31011639/62500 : ℚ) vp00000000111110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011111010_0 : Blocks := edgeBlocks% "full/vectors/0000000011111010-V-0000.bin"
noncomputable def vp0000000011111010 : Blocks := vp0000000011111010_0
private theorem bp00000000111110100 : Branch 0 (-31011639/125000 : ℚ) vp0000000011111010 := by
  apply branch_left_normalized (c:=vp00000000111110100) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-31011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-31011639/62500 : ℚ) by norm_num]
  exact coverp00000000111110100
private noncomputable def ep00000000111110101_0 : Blocks := edgeBlocks% "full/vectors/00000000111110101-E-0000.bin"
noncomputable def ep00000000111110101 : Blocks := ep00000000111110101_0
private theorem idp00000000111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011111010.list =
    C ((2:ℤ)^42) * horner X vp00000000111110101.list + horner X ep00000000111110101.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111110101 : Branch 1 (-31011639/125000 : ℚ) vp0000000011111010 := by
  apply branch_checked idp00000000111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-31011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-31074139/62500 : ℚ) by norm_num]
  exact coverp00000000111110101
theorem coverp0000000011111010 : Covers (-31011639/125000 : ℚ) vp0000000011111010 := join_branches bp00000000111110100 bp00000000111110101
private noncomputable def vp000000001111101_0 : Blocks := edgeBlocks% "full/vectors/000000001111101-V-0000.bin"
noncomputable def vp000000001111101 : Blocks := vp000000001111101_0
private theorem bp0000000011111010 : Branch 0 (-31011639/250000 : ℚ) vp000000001111101 := by
  apply branch_left_normalized (c:=vp0000000011111010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-31011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-31011639/125000 : ℚ) by norm_num]
  exact coverp0000000011111010
private noncomputable def ep0000000011111011_0 : Blocks := edgeBlocks% "full/vectors/0000000011111011-E-0000.bin"
noncomputable def ep0000000011111011 : Blocks := ep0000000011111011_0
private theorem idp0000000011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001111101.list =
    C ((2:ℤ)^66) * horner X vp0000000011111011.list + horner X ep0000000011111011.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011111011 : Branch 1 (-31011639/250000 : ℚ) vp000000001111101 := by
  apply branch_checked idp0000000011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-31011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-31136639/125000 : ℚ) by norm_num]
  exact coverp0000000011111011
theorem coverp000000001111101 : Covers (-31011639/250000 : ℚ) vp000000001111101 := join_branches bp0000000011111010 bp0000000011111011
private noncomputable def vp00000000111110011_0 : Blocks := edgeBlocks% "full/vectors/00000000111110011-V-0000.bin"
noncomputable def vp00000000111110011 : Blocks := vp00000000111110011_0
theorem coverp00000000111110011 : Covers (-30949139/62500 : ℚ) vp00000000111110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111110010_0 : Blocks := edgeBlocks% "full/vectors/00000000111110010-V-0000.bin"
noncomputable def vp00000000111110010 : Blocks := vp00000000111110010_0
theorem coverp00000000111110010 : Covers (-30886639/62500 : ℚ) vp00000000111110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011111001_0 : Blocks := edgeBlocks% "full/vectors/0000000011111001-V-0000.bin"
noncomputable def vp0000000011111001 : Blocks := vp0000000011111001_0
private theorem bp00000000111110010 : Branch 0 (-30886639/125000 : ℚ) vp0000000011111001 := by
  apply branch_left_normalized (c:=vp00000000111110010) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-30886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-30886639/62500 : ℚ) by norm_num]
  exact coverp00000000111110010
private noncomputable def ep00000000111110011_0 : Blocks := edgeBlocks% "full/vectors/00000000111110011-E-0000.bin"
noncomputable def ep00000000111110011 : Blocks := ep00000000111110011_0
private theorem idp00000000111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011111001.list =
    C ((2:ℤ)^41) * horner X vp00000000111110011.list + horner X ep00000000111110011.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111110011 : Branch 1 (-30886639/125000 : ℚ) vp0000000011111001 := by
  apply branch_checked idp00000000111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-30886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-30949139/62500 : ℚ) by norm_num]
  exact coverp00000000111110011
theorem coverp0000000011111001 : Covers (-30886639/125000 : ℚ) vp0000000011111001 := join_branches bp00000000111110010 bp00000000111110011
private noncomputable def vp00000000111110001_0 : Blocks := edgeBlocks% "full/vectors/00000000111110001-V-0000.bin"
noncomputable def vp00000000111110001 : Blocks := vp00000000111110001_0
theorem coverp00000000111110001 : Covers (-30824139/62500 : ℚ) vp00000000111110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111110000_0 : Blocks := edgeBlocks% "full/vectors/00000000111110000-V-0000.bin"
noncomputable def vp00000000111110000 : Blocks := vp00000000111110000_0
theorem coverp00000000111110000 : Covers (-30761639/62500 : ℚ) vp00000000111110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011111000_0 : Blocks := edgeBlocks% "full/vectors/0000000011111000-V-0000.bin"
noncomputable def vp0000000011111000 : Blocks := vp0000000011111000_0
private theorem bp00000000111110000 : Branch 0 (-30761639/125000 : ℚ) vp0000000011111000 := by
  apply branch_left_normalized (c:=vp00000000111110000) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-30761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-30761639/62500 : ℚ) by norm_num]
  exact coverp00000000111110000
private noncomputable def ep00000000111110001_0 : Blocks := edgeBlocks% "full/vectors/00000000111110001-E-0000.bin"
noncomputable def ep00000000111110001 : Blocks := ep00000000111110001_0
private theorem idp00000000111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011111000.list =
    C ((2:ℤ)^41) * horner X vp00000000111110001.list + horner X ep00000000111110001.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111110001 : Branch 1 (-30761639/125000 : ℚ) vp0000000011111000 := by
  apply branch_checked idp00000000111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-30761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-30824139/62500 : ℚ) by norm_num]
  exact coverp00000000111110001
theorem coverp0000000011111000 : Covers (-30761639/125000 : ℚ) vp0000000011111000 := join_branches bp00000000111110000 bp00000000111110001
private noncomputable def vp000000001111100_0 : Blocks := edgeBlocks% "full/vectors/000000001111100-V-0000.bin"
noncomputable def vp000000001111100 : Blocks := vp000000001111100_0
private theorem bp0000000011111000 : Branch 0 (-30761639/250000 : ℚ) vp000000001111100 := by
  apply branch_left_normalized (c:=vp0000000011111000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-30761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-30761639/125000 : ℚ) by norm_num]
  exact coverp0000000011111000
private noncomputable def ep0000000011111001_0 : Blocks := edgeBlocks% "full/vectors/0000000011111001-E-0000.bin"
noncomputable def ep0000000011111001 : Blocks := ep0000000011111001_0
private theorem idp0000000011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001111100.list =
    C ((2:ℤ)^65) * horner X vp0000000011111001.list + horner X ep0000000011111001.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011111001 : Branch 1 (-30761639/250000 : ℚ) vp000000001111100 := by
  apply branch_checked idp0000000011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-30761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-30886639/125000 : ℚ) by norm_num]
  exact coverp0000000011111001
theorem coverp000000001111100 : Covers (-30761639/250000 : ℚ) vp000000001111100 := join_branches bp0000000011111000 bp0000000011111001
private noncomputable def vp00000000111110_0 : Blocks := edgeBlocks% "full/vectors/00000000111110-V-0000.bin"
noncomputable def vp00000000111110 : Blocks := vp00000000111110_0
private theorem bp000000001111100 : Branch 0 (-30761639/500000 : ℚ) vp00000000111110 := by
  apply branch_left_normalized (c:=vp000000001111100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-30761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-30761639/250000 : ℚ) by norm_num]
  exact coverp000000001111100
private noncomputable def ep000000001111101_0 : Blocks := edgeBlocks% "full/vectors/000000001111101-E-0000.bin"
noncomputable def ep000000001111101 : Blocks := ep000000001111101_0
private theorem idp000000001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111110.list =
    C ((2:ℤ)^110) * horner X vp000000001111101.list + horner X ep000000001111101.list := by
  exact edge_identity (B := (2:ℤ)^258) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001111101 : Branch 1 (-30761639/500000 : ℚ) vp00000000111110 := by
  apply branch_checked idp000000001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-30761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-31011639/250000 : ℚ) by norm_num]
  exact coverp000000001111101
theorem coverp00000000111110 : Covers (-30761639/500000 : ℚ) vp00000000111110 := join_branches bp000000001111100 bp000000001111101
private noncomputable def vp0000000011111_0 : Blocks := edgeBlocks% "full/vectors/0000000011111-V-0000.bin"
private noncomputable def vp0000000011111_1 : Blocks := edgeBlocks% "full/vectors/0000000011111-V-0001.bin"
noncomputable def vp0000000011111 : Blocks := (Blocks.join vp0000000011111_0 vp0000000011111_1)
private theorem bp00000000111110 : Branch 0 (-30761639/1000000 : ℚ) vp0000000011111 := by
  apply branch_left_normalized (c:=vp00000000111110) (k:=0) (m:=109) (by decide +kernel)
  rw [show 2*(-30761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-30761639/500000 : ℚ) by norm_num]
  exact coverp00000000111110
private noncomputable def ep00000000111111_0 : Blocks := edgeBlocks% "full/vectors/00000000111111-E-0000.bin"
private noncomputable def ep00000000111111_1 : Blocks := edgeBlocks% "full/vectors/00000000111111-E-0001.bin"
noncomputable def ep00000000111111 : Blocks := (Blocks.join ep00000000111111_0 ep00000000111111_1)
private theorem idp00000000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011111.list =
    C ((2:ℤ)^202) * horner X vp00000000111111.list + horner X ep00000000111111.list := by
  exact edge_identity (B := (2:ℤ)^393) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111111 : Branch 1 (-30761639/1000000 : ℚ) vp0000000011111 := by
  apply branch_checked idp00000000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-30761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-31261639/500000 : ℚ) by norm_num]
  exact coverp00000000111111
theorem coverp0000000011111 : Covers (-30761639/1000000 : ℚ) vp0000000011111 := join_branches bp00000000111110 bp00000000111111
private noncomputable def vp0000000011110111_0 : Blocks := edgeBlocks% "full/vectors/0000000011110111-V-0000.bin"
noncomputable def vp0000000011110111 : Blocks := vp0000000011110111_0
theorem coverp0000000011110111 : Covers (-30636639/125000 : ℚ) vp0000000011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011110110_0 : Blocks := edgeBlocks% "full/vectors/0000000011110110-V-0000.bin"
noncomputable def vp0000000011110110 : Blocks := vp0000000011110110_0
theorem coverp0000000011110110 : Covers (-30511639/125000 : ℚ) vp0000000011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001111011_0 : Blocks := edgeBlocks% "full/vectors/000000001111011-V-0000.bin"
noncomputable def vp000000001111011 : Blocks := vp000000001111011_0
private theorem bp0000000011110110 : Branch 0 (-30511639/250000 : ℚ) vp000000001111011 := by
  apply branch_left_normalized (c:=vp0000000011110110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-30511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-30511639/125000 : ℚ) by norm_num]
  exact coverp0000000011110110
private noncomputable def ep0000000011110111_0 : Blocks := edgeBlocks% "full/vectors/0000000011110111-E-0000.bin"
noncomputable def ep0000000011110111 : Blocks := ep0000000011110111_0
private theorem idp0000000011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001111011.list =
    C ((2:ℤ)^64) * horner X vp0000000011110111.list + horner X ep0000000011110111.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011110111 : Branch 1 (-30511639/250000 : ℚ) vp000000001111011 := by
  apply branch_checked idp0000000011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-30511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-30636639/125000 : ℚ) by norm_num]
  exact coverp0000000011110111
theorem coverp000000001111011 : Covers (-30511639/250000 : ℚ) vp000000001111011 := join_branches bp0000000011110110 bp0000000011110111
private noncomputable def vp0000000011110101_0 : Blocks := edgeBlocks% "full/vectors/0000000011110101-V-0000.bin"
noncomputable def vp0000000011110101 : Blocks := vp0000000011110101_0
theorem coverp0000000011110101 : Covers (-30386639/125000 : ℚ) vp0000000011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011110100_0 : Blocks := edgeBlocks% "full/vectors/0000000011110100-V-0000.bin"
noncomputable def vp0000000011110100 : Blocks := vp0000000011110100_0
theorem coverp0000000011110100 : Covers (-30261639/125000 : ℚ) vp0000000011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001111010_0 : Blocks := edgeBlocks% "full/vectors/000000001111010-V-0000.bin"
noncomputable def vp000000001111010 : Blocks := vp000000001111010_0
private theorem bp0000000011110100 : Branch 0 (-30261639/250000 : ℚ) vp000000001111010 := by
  apply branch_left_normalized (c:=vp0000000011110100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-30261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-30261639/125000 : ℚ) by norm_num]
  exact coverp0000000011110100
private noncomputable def ep0000000011110101_0 : Blocks := edgeBlocks% "full/vectors/0000000011110101-E-0000.bin"
noncomputable def ep0000000011110101 : Blocks := ep0000000011110101_0
private theorem idp0000000011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001111010.list =
    C ((2:ℤ)^65) * horner X vp0000000011110101.list + horner X ep0000000011110101.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011110101 : Branch 1 (-30261639/250000 : ℚ) vp000000001111010 := by
  apply branch_checked idp0000000011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-30261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-30386639/125000 : ℚ) by norm_num]
  exact coverp0000000011110101
theorem coverp000000001111010 : Covers (-30261639/250000 : ℚ) vp000000001111010 := join_branches bp0000000011110100 bp0000000011110101
private noncomputable def vp00000000111101_0 : Blocks := edgeBlocks% "full/vectors/00000000111101-V-0000.bin"
noncomputable def vp00000000111101 : Blocks := vp00000000111101_0
private theorem bp000000001111010 : Branch 0 (-30261639/500000 : ℚ) vp00000000111101 := by
  apply branch_left_normalized (c:=vp000000001111010) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-30261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-30261639/250000 : ℚ) by norm_num]
  exact coverp000000001111010
private noncomputable def ep000000001111011_0 : Blocks := edgeBlocks% "full/vectors/000000001111011-E-0000.bin"
noncomputable def ep000000001111011 : Blocks := ep000000001111011_0
private theorem idp000000001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111101.list =
    C ((2:ℤ)^112) * horner X vp000000001111011.list + horner X ep000000001111011.list := by
  exact edge_identity (B := (2:ℤ)^257) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001111011 : Branch 1 (-30261639/500000 : ℚ) vp00000000111101 := by
  apply branch_checked idp000000001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-30261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-30511639/250000 : ℚ) by norm_num]
  exact coverp000000001111011
theorem coverp00000000111101 : Covers (-30261639/500000 : ℚ) vp00000000111101 := join_branches bp000000001111010 bp000000001111011
private noncomputable def vp0000000011110011_0 : Blocks := edgeBlocks% "full/vectors/0000000011110011-V-0000.bin"
noncomputable def vp0000000011110011 : Blocks := vp0000000011110011_0
theorem coverp0000000011110011 : Covers (-30136639/125000 : ℚ) vp0000000011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011110010_0 : Blocks := edgeBlocks% "full/vectors/0000000011110010-V-0000.bin"
noncomputable def vp0000000011110010 : Blocks := vp0000000011110010_0
theorem coverp0000000011110010 : Covers (-30011639/125000 : ℚ) vp0000000011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001111001_0 : Blocks := edgeBlocks% "full/vectors/000000001111001-V-0000.bin"
noncomputable def vp000000001111001 : Blocks := vp000000001111001_0
private theorem bp0000000011110010 : Branch 0 (-30011639/250000 : ℚ) vp000000001111001 := by
  apply branch_left_normalized (c:=vp0000000011110010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-30011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-30011639/125000 : ℚ) by norm_num]
  exact coverp0000000011110010
private noncomputable def ep0000000011110011_0 : Blocks := edgeBlocks% "full/vectors/0000000011110011-E-0000.bin"
noncomputable def ep0000000011110011 : Blocks := ep0000000011110011_0
private theorem idp0000000011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001111001.list =
    C ((2:ℤ)^66) * horner X vp0000000011110011.list + horner X ep0000000011110011.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011110011 : Branch 1 (-30011639/250000 : ℚ) vp000000001111001 := by
  apply branch_checked idp0000000011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-30011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-30136639/125000 : ℚ) by norm_num]
  exact coverp0000000011110011
theorem coverp000000001111001 : Covers (-30011639/250000 : ℚ) vp000000001111001 := join_branches bp0000000011110010 bp0000000011110011
private noncomputable def vp0000000011110001_0 : Blocks := edgeBlocks% "full/vectors/0000000011110001-V-0000.bin"
noncomputable def vp0000000011110001 : Blocks := vp0000000011110001_0
theorem coverp0000000011110001 : Covers (-29886639/125000 : ℚ) vp0000000011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111100001_0 : Blocks := edgeBlocks% "full/vectors/00000000111100001-V-0000.bin"
noncomputable def vp00000000111100001 : Blocks := vp00000000111100001_0
theorem coverp00000000111100001 : Covers (-29824139/62500 : ℚ) vp00000000111100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111100000_0 : Blocks := edgeBlocks% "full/vectors/00000000111100000-V-0000.bin"
noncomputable def vp00000000111100000 : Blocks := vp00000000111100000_0
theorem coverp00000000111100000 : Covers (-29761639/62500 : ℚ) vp00000000111100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011110000_0 : Blocks := edgeBlocks% "full/vectors/0000000011110000-V-0000.bin"
noncomputable def vp0000000011110000 : Blocks := vp0000000011110000_0
private theorem bp00000000111100000 : Branch 0 (-29761639/125000 : ℚ) vp0000000011110000 := by
  apply branch_left_normalized (c:=vp00000000111100000) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-29761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-29761639/62500 : ℚ) by norm_num]
  exact coverp00000000111100000
private noncomputable def ep00000000111100001_0 : Blocks := edgeBlocks% "full/vectors/00000000111100001-E-0000.bin"
noncomputable def ep00000000111100001 : Blocks := ep00000000111100001_0
private theorem idp00000000111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011110000.list =
    C ((2:ℤ)^43) * horner X vp00000000111100001.list + horner X ep00000000111100001.list := by
  exact edge_identity (B := (2:ℤ)^159) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111100001 : Branch 1 (-29761639/125000 : ℚ) vp0000000011110000 := by
  apply branch_checked idp00000000111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-29761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-29824139/62500 : ℚ) by norm_num]
  exact coverp00000000111100001
theorem coverp0000000011110000 : Covers (-29761639/125000 : ℚ) vp0000000011110000 := join_branches bp00000000111100000 bp00000000111100001
private noncomputable def vp000000001111000_0 : Blocks := edgeBlocks% "full/vectors/000000001111000-V-0000.bin"
noncomputable def vp000000001111000 : Blocks := vp000000001111000_0
private theorem bp0000000011110000 : Branch 0 (-29761639/250000 : ℚ) vp000000001111000 := by
  apply branch_left_normalized (c:=vp0000000011110000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-29761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-29761639/125000 : ℚ) by norm_num]
  exact coverp0000000011110000
private noncomputable def ep0000000011110001_0 : Blocks := edgeBlocks% "full/vectors/0000000011110001-E-0000.bin"
noncomputable def ep0000000011110001 : Blocks := ep0000000011110001_0
private theorem idp0000000011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001111000.list =
    C ((2:ℤ)^68) * horner X vp0000000011110001.list + horner X ep0000000011110001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011110001 : Branch 1 (-29761639/250000 : ℚ) vp000000001111000 := by
  apply branch_checked idp0000000011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-29761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-29886639/125000 : ℚ) by norm_num]
  exact coverp0000000011110001
theorem coverp000000001111000 : Covers (-29761639/250000 : ℚ) vp000000001111000 := join_branches bp0000000011110000 bp0000000011110001
private noncomputable def vp00000000111100_0 : Blocks := edgeBlocks% "full/vectors/00000000111100-V-0000.bin"
noncomputable def vp00000000111100 : Blocks := vp00000000111100_0
private theorem bp000000001111000 : Branch 0 (-29761639/500000 : ℚ) vp00000000111100 := by
  apply branch_left_normalized (c:=vp000000001111000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-29761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-29761639/250000 : ℚ) by norm_num]
  exact coverp000000001111000
private noncomputable def ep000000001111001_0 : Blocks := edgeBlocks% "full/vectors/000000001111001-E-0000.bin"
noncomputable def ep000000001111001 : Blocks := ep000000001111001_0
private theorem idp000000001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111100.list =
    C ((2:ℤ)^120) * horner X vp000000001111001.list + horner X ep000000001111001.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001111001 : Branch 1 (-29761639/500000 : ℚ) vp00000000111100 := by
  apply branch_checked idp000000001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-29761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-30011639/250000 : ℚ) by norm_num]
  exact coverp000000001111001
theorem coverp00000000111100 : Covers (-29761639/500000 : ℚ) vp00000000111100 := join_branches bp000000001111000 bp000000001111001
private noncomputable def vp0000000011110_0 : Blocks := edgeBlocks% "full/vectors/0000000011110-V-0000.bin"
private noncomputable def vp0000000011110_1 : Blocks := edgeBlocks% "full/vectors/0000000011110-V-0001.bin"
noncomputable def vp0000000011110 : Blocks := (Blocks.join vp0000000011110_0 vp0000000011110_1)
private theorem bp00000000111100 : Branch 0 (-29761639/1000000 : ℚ) vp0000000011110 := by
  apply branch_left_normalized (c:=vp00000000111100) (k:=0) (m:=113) (by decide +kernel)
  rw [show 2*(-29761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-29761639/500000 : ℚ) by norm_num]
  exact coverp00000000111100
private noncomputable def ep00000000111101_0 : Blocks := edgeBlocks% "full/vectors/00000000111101-E-0000.bin"
private noncomputable def ep00000000111101_1 : Blocks := edgeBlocks% "full/vectors/00000000111101-E-0001.bin"
noncomputable def ep00000000111101 : Blocks := (Blocks.join ep00000000111101_0 ep00000000111101_1)
private theorem idp00000000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011110.list =
    C ((2:ℤ)^210) * horner X vp00000000111101.list + horner X ep00000000111101.list := by
  exact edge_identity (B := (2:ℤ)^402) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111101 : Branch 1 (-29761639/1000000 : ℚ) vp0000000011110 := by
  apply branch_checked idp00000000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-29761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-30261639/500000 : ℚ) by norm_num]
  exact coverp00000000111101
theorem coverp0000000011110 : Covers (-29761639/1000000 : ℚ) vp0000000011110 := join_branches bp00000000111100 bp00000000111101
private noncomputable def vp000000001111_0 : Blocks := edgeBlocks% "full/vectors/000000001111-V-0000.bin"
private noncomputable def vp000000001111_1 : Blocks := edgeBlocks% "full/vectors/000000001111-V-0001.bin"
private noncomputable def vp000000001111_2 : Blocks := edgeBlocks% "full/vectors/000000001111-V-0002.bin"
noncomputable def vp000000001111 : Blocks := (Blocks.join vp000000001111_0 (Blocks.join vp000000001111_1 vp000000001111_2))
private theorem bp0000000011110 : Branch 0 (-29761639/2000000 : ℚ) vp000000001111 := by
  apply branch_left_normalized (c:=vp0000000011110) (k:=0) (m:=202) (by decide +kernel)
  rw [show 2*(-29761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-29761639/1000000 : ℚ) by norm_num]
  exact coverp0000000011110
private noncomputable def ep0000000011111_0 : Blocks := edgeBlocks% "full/vectors/0000000011111-E-0000.bin"
private noncomputable def ep0000000011111_1 : Blocks := edgeBlocks% "full/vectors/0000000011111-E-0001.bin"
private noncomputable def ep0000000011111_2 : Blocks := edgeBlocks% "full/vectors/0000000011111-E-0002.bin"
noncomputable def ep0000000011111 : Blocks := (Blocks.join ep0000000011111_0 (Blocks.join ep0000000011111_1 ep0000000011111_2))
private theorem idp0000000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001111.list =
    C ((2:ℤ)^391) * horner X vp0000000011111.list + horner X ep0000000011111.list := by
  exact edge_identity (B := (2:ℤ)^676) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011111 : Branch 1 (-29761639/2000000 : ℚ) vp000000001111 := by
  apply branch_checked idp0000000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-29761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-30761639/1000000 : ℚ) by norm_num]
  exact coverp0000000011111
theorem coverp000000001111 : Covers (-29761639/2000000 : ℚ) vp000000001111 := join_branches bp0000000011110 bp0000000011111
private noncomputable def vp00000000111011111_0 : Blocks := edgeBlocks% "full/vectors/00000000111011111-V-0000.bin"
noncomputable def vp00000000111011111 : Blocks := vp00000000111011111_0
theorem coverp00000000111011111 : Covers (-29699139/62500 : ℚ) vp00000000111011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111011110_0 : Blocks := edgeBlocks% "full/vectors/00000000111011110-V-0000.bin"
noncomputable def vp00000000111011110 : Blocks := vp00000000111011110_0
theorem coverp00000000111011110 : Covers (-29636639/62500 : ℚ) vp00000000111011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011101111_0 : Blocks := edgeBlocks% "full/vectors/0000000011101111-V-0000.bin"
noncomputable def vp0000000011101111 : Blocks := vp0000000011101111_0
private theorem bp00000000111011110 : Branch 0 (-29636639/125000 : ℚ) vp0000000011101111 := by
  apply branch_left_normalized (c:=vp00000000111011110) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-29636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-29636639/62500 : ℚ) by norm_num]
  exact coverp00000000111011110
private noncomputable def ep00000000111011111_0 : Blocks := edgeBlocks% "full/vectors/00000000111011111-E-0000.bin"
noncomputable def ep00000000111011111 : Blocks := ep00000000111011111_0
private theorem idp00000000111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011101111.list =
    C ((2:ℤ)^43) * horner X vp00000000111011111.list + horner X ep00000000111011111.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111011111 : Branch 1 (-29636639/125000 : ℚ) vp0000000011101111 := by
  apply branch_checked idp00000000111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-29636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-29699139/62500 : ℚ) by norm_num]
  exact coverp00000000111011111
theorem coverp0000000011101111 : Covers (-29636639/125000 : ℚ) vp0000000011101111 := join_branches bp00000000111011110 bp00000000111011111
private noncomputable def vp000000001110111011_0 : Blocks := edgeBlocks% "full/vectors/000000001110111011-V-0000.bin"
noncomputable def vp000000001110111011 : Blocks := vp000000001110111011_0
theorem coverp000000001110111011 : Covers (-29605389/31250 : ℚ) vp000000001110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001110111010_0 : Blocks := edgeBlocks% "full/vectors/000000001110111010-V-0000.bin"
noncomputable def vp000000001110111010 : Blocks := vp000000001110111010_0
theorem coverp000000001110111010 : Covers (-29574139/31250 : ℚ) vp000000001110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111011101_0 : Blocks := edgeBlocks% "full/vectors/00000000111011101-V-0000.bin"
noncomputable def vp00000000111011101 : Blocks := vp00000000111011101_0
private theorem bp000000001110111010 : Branch 0 (-29574139/62500 : ℚ) vp00000000111011101 := by
  apply branch_left_normalized (c:=vp000000001110111010) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-29574139/62500 : ℚ) - ((0:ℤ):ℚ) = (-29574139/31250 : ℚ) by norm_num]
  exact coverp000000001110111010
private noncomputable def ep000000001110111011_0 : Blocks := edgeBlocks% "full/vectors/000000001110111011-E-0000.bin"
noncomputable def ep000000001110111011 : Blocks := ep000000001110111011_0
private theorem idp000000001110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111011101.list =
    C ((2:ℤ)^28) * horner X vp000000001110111011.list + horner X ep000000001110111011.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001110111011 : Branch 1 (-29574139/62500 : ℚ) vp00000000111011101 := by
  apply branch_checked idp000000001110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-29574139/62500 : ℚ) - ((1:ℤ):ℚ) = (-29605389/31250 : ℚ) by norm_num]
  exact coverp000000001110111011
theorem coverp00000000111011101 : Covers (-29574139/62500 : ℚ) vp00000000111011101 := join_branches bp000000001110111010 bp000000001110111011
private noncomputable def vp00000000111011100_0 : Blocks := edgeBlocks% "full/vectors/00000000111011100-V-0000.bin"
noncomputable def vp00000000111011100 : Blocks := vp00000000111011100_0
theorem coverp00000000111011100 : Covers (-29511639/62500 : ℚ) vp00000000111011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011101110_0 : Blocks := edgeBlocks% "full/vectors/0000000011101110-V-0000.bin"
noncomputable def vp0000000011101110 : Blocks := vp0000000011101110_0
private theorem bp00000000111011100 : Branch 0 (-29511639/125000 : ℚ) vp0000000011101110 := by
  apply branch_left_normalized (c:=vp00000000111011100) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-29511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-29511639/62500 : ℚ) by norm_num]
  exact coverp00000000111011100
private noncomputable def ep00000000111011101_0 : Blocks := edgeBlocks% "full/vectors/00000000111011101-E-0000.bin"
noncomputable def ep00000000111011101 : Blocks := ep00000000111011101_0
private theorem idp00000000111011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011101110.list =
    C ((2:ℤ)^41) * horner X vp00000000111011101.list + horner X ep00000000111011101.list := by
  exact edge_identity (B := (2:ℤ)^154) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111011101 : Branch 1 (-29511639/125000 : ℚ) vp0000000011101110 := by
  apply branch_checked idp00000000111011101 (by positivity) (by decide +kernel)
  rw [show 2*(-29511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-29574139/62500 : ℚ) by norm_num]
  exact coverp00000000111011101
theorem coverp0000000011101110 : Covers (-29511639/125000 : ℚ) vp0000000011101110 := join_branches bp00000000111011100 bp00000000111011101
private noncomputable def vp000000001110111_0 : Blocks := edgeBlocks% "full/vectors/000000001110111-V-0000.bin"
noncomputable def vp000000001110111 : Blocks := vp000000001110111_0
private theorem bp0000000011101110 : Branch 0 (-29511639/250000 : ℚ) vp000000001110111 := by
  apply branch_left_normalized (c:=vp0000000011101110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-29511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-29511639/125000 : ℚ) by norm_num]
  exact coverp0000000011101110
private noncomputable def ep0000000011101111_0 : Blocks := edgeBlocks% "full/vectors/0000000011101111-E-0000.bin"
noncomputable def ep0000000011101111 : Blocks := ep0000000011101111_0
private theorem idp0000000011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110111.list =
    C ((2:ℤ)^66) * horner X vp0000000011101111.list + horner X ep0000000011101111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011101111 : Branch 1 (-29511639/250000 : ℚ) vp000000001110111 := by
  apply branch_checked idp0000000011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-29511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-29636639/125000 : ℚ) by norm_num]
  exact coverp0000000011101111
theorem coverp000000001110111 : Covers (-29511639/250000 : ℚ) vp000000001110111 := join_branches bp0000000011101110 bp0000000011101111
private noncomputable def vp0000000011101101_0 : Blocks := edgeBlocks% "full/vectors/0000000011101101-V-0000.bin"
noncomputable def vp0000000011101101 : Blocks := vp0000000011101101_0
theorem coverp0000000011101101 : Covers (-29386639/125000 : ℚ) vp0000000011101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011101100_0 : Blocks := edgeBlocks% "full/vectors/0000000011101100-V-0000.bin"
noncomputable def vp0000000011101100 : Blocks := vp0000000011101100_0
theorem coverp0000000011101100 : Covers (-29261639/125000 : ℚ) vp0000000011101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001110110_0 : Blocks := edgeBlocks% "full/vectors/000000001110110-V-0000.bin"
noncomputable def vp000000001110110 : Blocks := vp000000001110110_0
private theorem bp0000000011101100 : Branch 0 (-29261639/250000 : ℚ) vp000000001110110 := by
  apply branch_left_normalized (c:=vp0000000011101100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-29261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-29261639/125000 : ℚ) by norm_num]
  exact coverp0000000011101100
private noncomputable def ep0000000011101101_0 : Blocks := edgeBlocks% "full/vectors/0000000011101101-E-0000.bin"
noncomputable def ep0000000011101101 : Blocks := ep0000000011101101_0
private theorem idp0000000011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110110.list =
    C ((2:ℤ)^67) * horner X vp0000000011101101.list + horner X ep0000000011101101.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011101101 : Branch 1 (-29261639/250000 : ℚ) vp000000001110110 := by
  apply branch_checked idp0000000011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-29261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-29386639/125000 : ℚ) by norm_num]
  exact coverp0000000011101101
theorem coverp000000001110110 : Covers (-29261639/250000 : ℚ) vp000000001110110 := join_branches bp0000000011101100 bp0000000011101101
private noncomputable def vp00000000111011_0 : Blocks := edgeBlocks% "full/vectors/00000000111011-V-0000.bin"
noncomputable def vp00000000111011 : Blocks := vp00000000111011_0
private theorem bp000000001110110 : Branch 0 (-29261639/500000 : ℚ) vp00000000111011 := by
  apply branch_left_normalized (c:=vp000000001110110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-29261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-29261639/250000 : ℚ) by norm_num]
  exact coverp000000001110110
private noncomputable def ep000000001110111_0 : Blocks := edgeBlocks% "full/vectors/000000001110111-E-0000.bin"
noncomputable def ep000000001110111 : Blocks := ep000000001110111_0
private theorem idp000000001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111011.list =
    C ((2:ℤ)^112) * horner X vp000000001110111.list + horner X ep000000001110111.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001110111 : Branch 1 (-29261639/500000 : ℚ) vp00000000111011 := by
  apply branch_checked idp000000001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-29261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-29511639/250000 : ℚ) by norm_num]
  exact coverp000000001110111
theorem coverp00000000111011 : Covers (-29261639/500000 : ℚ) vp00000000111011 := join_branches bp000000001110110 bp000000001110111
private noncomputable def vp0000000011101011_0 : Blocks := edgeBlocks% "full/vectors/0000000011101011-V-0000.bin"
noncomputable def vp0000000011101011 : Blocks := vp0000000011101011_0
theorem coverp0000000011101011 : Covers (-29136639/125000 : ℚ) vp0000000011101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111010101_0 : Blocks := edgeBlocks% "full/vectors/00000000111010101-V-0000.bin"
noncomputable def vp00000000111010101 : Blocks := vp00000000111010101_0
theorem coverp00000000111010101 : Covers (-29074139/62500 : ℚ) vp00000000111010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111010100_0 : Blocks := edgeBlocks% "full/vectors/00000000111010100-V-0000.bin"
noncomputable def vp00000000111010100 : Blocks := vp00000000111010100_0
theorem coverp00000000111010100 : Covers (-29011639/62500 : ℚ) vp00000000111010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011101010_0 : Blocks := edgeBlocks% "full/vectors/0000000011101010-V-0000.bin"
noncomputable def vp0000000011101010 : Blocks := vp0000000011101010_0
private theorem bp00000000111010100 : Branch 0 (-29011639/125000 : ℚ) vp0000000011101010 := by
  apply branch_left_normalized (c:=vp00000000111010100) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-29011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-29011639/62500 : ℚ) by norm_num]
  exact coverp00000000111010100
private noncomputable def ep00000000111010101_0 : Blocks := edgeBlocks% "full/vectors/00000000111010101-E-0000.bin"
noncomputable def ep00000000111010101 : Blocks := ep00000000111010101_0
private theorem idp00000000111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011101010.list =
    C ((2:ℤ)^43) * horner X vp00000000111010101.list + horner X ep00000000111010101.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111010101 : Branch 1 (-29011639/125000 : ℚ) vp0000000011101010 := by
  apply branch_checked idp00000000111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-29011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-29074139/62500 : ℚ) by norm_num]
  exact coverp00000000111010101
theorem coverp0000000011101010 : Covers (-29011639/125000 : ℚ) vp0000000011101010 := join_branches bp00000000111010100 bp00000000111010101
private noncomputable def vp000000001110101_0 : Blocks := edgeBlocks% "full/vectors/000000001110101-V-0000.bin"
noncomputable def vp000000001110101 : Blocks := vp000000001110101_0
private theorem bp0000000011101010 : Branch 0 (-29011639/250000 : ℚ) vp000000001110101 := by
  apply branch_left_normalized (c:=vp0000000011101010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-29011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-29011639/125000 : ℚ) by norm_num]
  exact coverp0000000011101010
private noncomputable def ep0000000011101011_0 : Blocks := edgeBlocks% "full/vectors/0000000011101011-E-0000.bin"
noncomputable def ep0000000011101011 : Blocks := ep0000000011101011_0
private theorem idp0000000011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110101.list =
    C ((2:ℤ)^68) * horner X vp0000000011101011.list + horner X ep0000000011101011.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011101011 : Branch 1 (-29011639/250000 : ℚ) vp000000001110101 := by
  apply branch_checked idp0000000011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-29011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-29136639/125000 : ℚ) by norm_num]
  exact coverp0000000011101011
theorem coverp000000001110101 : Covers (-29011639/250000 : ℚ) vp000000001110101 := join_branches bp0000000011101010 bp0000000011101011
private noncomputable def vp00000000111010011_0 : Blocks := edgeBlocks% "full/vectors/00000000111010011-V-0000.bin"
noncomputable def vp00000000111010011 : Blocks := vp00000000111010011_0
theorem coverp00000000111010011 : Covers (-28949139/62500 : ℚ) vp00000000111010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001110100101_0 : Blocks := edgeBlocks% "full/vectors/000000001110100101-V-0000.bin"
noncomputable def vp000000001110100101 : Blocks := vp000000001110100101_0
theorem coverp000000001110100101 : Covers (-28917889/31250 : ℚ) vp000000001110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001110100100_0 : Blocks := edgeBlocks% "full/vectors/000000001110100100-V-0000.bin"
noncomputable def vp000000001110100100 : Blocks := vp000000001110100100_0
theorem coverp000000001110100100 : Covers (-28886639/31250 : ℚ) vp000000001110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111010010_0 : Blocks := edgeBlocks% "full/vectors/00000000111010010-V-0000.bin"
noncomputable def vp00000000111010010 : Blocks := vp00000000111010010_0
private theorem bp000000001110100100 : Branch 0 (-28886639/62500 : ℚ) vp00000000111010010 := by
  apply branch_left_normalized (c:=vp000000001110100100) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-28886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-28886639/31250 : ℚ) by norm_num]
  exact coverp000000001110100100
private noncomputable def ep000000001110100101_0 : Blocks := edgeBlocks% "full/vectors/000000001110100101-E-0000.bin"
noncomputable def ep000000001110100101 : Blocks := ep000000001110100101_0
private theorem idp000000001110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111010010.list =
    C ((2:ℤ)^29) * horner X vp000000001110100101.list + horner X ep000000001110100101.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001110100101 : Branch 1 (-28886639/62500 : ℚ) vp00000000111010010 := by
  apply branch_checked idp000000001110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-28886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-28917889/31250 : ℚ) by norm_num]
  exact coverp000000001110100101
theorem coverp00000000111010010 : Covers (-28886639/62500 : ℚ) vp00000000111010010 := join_branches bp000000001110100100 bp000000001110100101
private noncomputable def vp0000000011101001_0 : Blocks := edgeBlocks% "full/vectors/0000000011101001-V-0000.bin"
noncomputable def vp0000000011101001 : Blocks := vp0000000011101001_0
private theorem bp00000000111010010 : Branch 0 (-28886639/125000 : ℚ) vp0000000011101001 := by
  apply branch_left_normalized (c:=vp00000000111010010) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-28886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-28886639/62500 : ℚ) by norm_num]
  exact coverp00000000111010010
private noncomputable def ep00000000111010011_0 : Blocks := edgeBlocks% "full/vectors/00000000111010011-E-0000.bin"
noncomputable def ep00000000111010011 : Blocks := ep00000000111010011_0
private theorem idp00000000111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011101001.list =
    C ((2:ℤ)^43) * horner X vp00000000111010011.list + horner X ep00000000111010011.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111010011 : Branch 1 (-28886639/125000 : ℚ) vp0000000011101001 := by
  apply branch_checked idp00000000111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-28886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-28949139/62500 : ℚ) by norm_num]
  exact coverp00000000111010011
theorem coverp0000000011101001 : Covers (-28886639/125000 : ℚ) vp0000000011101001 := join_branches bp00000000111010010 bp00000000111010011
private noncomputable def vp000000001110100011_0 : Blocks := edgeBlocks% "full/vectors/000000001110100011-V-0000.bin"
noncomputable def vp000000001110100011 : Blocks := vp000000001110100011_0
theorem coverp000000001110100011 : Covers (-28855389/31250 : ℚ) vp000000001110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001110100010_0 : Blocks := edgeBlocks% "full/vectors/000000001110100010-V-0000.bin"
noncomputable def vp000000001110100010 : Blocks := vp000000001110100010_0
theorem coverp000000001110100010 : Covers (-28824139/31250 : ℚ) vp000000001110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111010001_0 : Blocks := edgeBlocks% "full/vectors/00000000111010001-V-0000.bin"
noncomputable def vp00000000111010001 : Blocks := vp00000000111010001_0
private theorem bp000000001110100010 : Branch 0 (-28824139/62500 : ℚ) vp00000000111010001 := by
  apply branch_left_normalized (c:=vp000000001110100010) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-28824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-28824139/31250 : ℚ) by norm_num]
  exact coverp000000001110100010
private noncomputable def ep000000001110100011_0 : Blocks := edgeBlocks% "full/vectors/000000001110100011-E-0000.bin"
noncomputable def ep000000001110100011 : Blocks := ep000000001110100011_0
private theorem idp000000001110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111010001.list =
    C ((2:ℤ)^28) * horner X vp000000001110100011.list + horner X ep000000001110100011.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001110100011 : Branch 1 (-28824139/62500 : ℚ) vp00000000111010001 := by
  apply branch_checked idp000000001110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-28824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-28855389/31250 : ℚ) by norm_num]
  exact coverp000000001110100011
theorem coverp00000000111010001 : Covers (-28824139/62500 : ℚ) vp00000000111010001 := join_branches bp000000001110100010 bp000000001110100011
private noncomputable def vp00000000111010000_0 : Blocks := edgeBlocks% "full/vectors/00000000111010000-V-0000.bin"
noncomputable def vp00000000111010000 : Blocks := vp00000000111010000_0
theorem coverp00000000111010000 : Covers (-28761639/62500 : ℚ) vp00000000111010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011101000_0 : Blocks := edgeBlocks% "full/vectors/0000000011101000-V-0000.bin"
noncomputable def vp0000000011101000 : Blocks := vp0000000011101000_0
private theorem bp00000000111010000 : Branch 0 (-28761639/125000 : ℚ) vp0000000011101000 := by
  apply branch_left_normalized (c:=vp00000000111010000) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-28761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-28761639/62500 : ℚ) by norm_num]
  exact coverp00000000111010000
private noncomputable def ep00000000111010001_0 : Blocks := edgeBlocks% "full/vectors/00000000111010001-E-0000.bin"
noncomputable def ep00000000111010001 : Blocks := ep00000000111010001_0
private theorem idp00000000111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011101000.list =
    C ((2:ℤ)^41) * horner X vp00000000111010001.list + horner X ep00000000111010001.list := by
  exact edge_identity (B := (2:ℤ)^154) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111010001 : Branch 1 (-28761639/125000 : ℚ) vp0000000011101000 := by
  apply branch_checked idp00000000111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-28761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-28824139/62500 : ℚ) by norm_num]
  exact coverp00000000111010001
theorem coverp0000000011101000 : Covers (-28761639/125000 : ℚ) vp0000000011101000 := join_branches bp00000000111010000 bp00000000111010001
private noncomputable def vp000000001110100_0 : Blocks := edgeBlocks% "full/vectors/000000001110100-V-0000.bin"
noncomputable def vp000000001110100 : Blocks := vp000000001110100_0
private theorem bp0000000011101000 : Branch 0 (-28761639/250000 : ℚ) vp000000001110100 := by
  apply branch_left_normalized (c:=vp0000000011101000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-28761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-28761639/125000 : ℚ) by norm_num]
  exact coverp0000000011101000
private noncomputable def ep0000000011101001_0 : Blocks := edgeBlocks% "full/vectors/0000000011101001-E-0000.bin"
noncomputable def ep0000000011101001 : Blocks := ep0000000011101001_0
private theorem idp0000000011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110100.list =
    C ((2:ℤ)^65) * horner X vp0000000011101001.list + horner X ep0000000011101001.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011101001 : Branch 1 (-28761639/250000 : ℚ) vp000000001110100 := by
  apply branch_checked idp0000000011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-28761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-28886639/125000 : ℚ) by norm_num]
  exact coverp0000000011101001
theorem coverp000000001110100 : Covers (-28761639/250000 : ℚ) vp000000001110100 := join_branches bp0000000011101000 bp0000000011101001
private noncomputable def vp00000000111010_0 : Blocks := edgeBlocks% "full/vectors/00000000111010-V-0000.bin"
noncomputable def vp00000000111010 : Blocks := vp00000000111010_0
private theorem bp000000001110100 : Branch 0 (-28761639/500000 : ℚ) vp00000000111010 := by
  apply branch_left_normalized (c:=vp000000001110100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-28761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-28761639/250000 : ℚ) by norm_num]
  exact coverp000000001110100
private noncomputable def ep000000001110101_0 : Blocks := edgeBlocks% "full/vectors/000000001110101-E-0000.bin"
noncomputable def ep000000001110101 : Blocks := ep000000001110101_0
private theorem idp000000001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111010.list =
    C ((2:ℤ)^112) * horner X vp000000001110101.list + horner X ep000000001110101.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001110101 : Branch 1 (-28761639/500000 : ℚ) vp00000000111010 := by
  apply branch_checked idp000000001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-28761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-29011639/250000 : ℚ) by norm_num]
  exact coverp000000001110101
theorem coverp00000000111010 : Covers (-28761639/500000 : ℚ) vp00000000111010 := join_branches bp000000001110100 bp000000001110101
private noncomputable def vp0000000011101_0 : Blocks := edgeBlocks% "full/vectors/0000000011101-V-0000.bin"
private noncomputable def vp0000000011101_1 : Blocks := edgeBlocks% "full/vectors/0000000011101-V-0001.bin"
noncomputable def vp0000000011101 : Blocks := (Blocks.join vp0000000011101_0 vp0000000011101_1)
private theorem bp00000000111010 : Branch 0 (-28761639/1000000 : ℚ) vp0000000011101 := by
  apply branch_left_normalized (c:=vp00000000111010) (k:=0) (m:=111) (by decide +kernel)
  rw [show 2*(-28761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-28761639/500000 : ℚ) by norm_num]
  exact coverp00000000111010
private noncomputable def ep00000000111011_0 : Blocks := edgeBlocks% "full/vectors/00000000111011-E-0000.bin"
private noncomputable def ep00000000111011_1 : Blocks := edgeBlocks% "full/vectors/00000000111011-E-0001.bin"
noncomputable def ep00000000111011 : Blocks := (Blocks.join ep00000000111011_0 ep00000000111011_1)
private theorem idp00000000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011101.list =
    C ((2:ℤ)^204) * horner X vp00000000111011.list + horner X ep00000000111011.list := by
  exact edge_identity (B := (2:ℤ)^398) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111011 : Branch 1 (-28761639/1000000 : ℚ) vp0000000011101 := by
  apply branch_checked idp00000000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-28761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-29261639/500000 : ℚ) by norm_num]
  exact coverp00000000111011
theorem coverp0000000011101 : Covers (-28761639/1000000 : ℚ) vp0000000011101 := join_branches bp00000000111010 bp00000000111011
private noncomputable def vp00000000111001111_0 : Blocks := edgeBlocks% "full/vectors/00000000111001111-V-0000.bin"
noncomputable def vp00000000111001111 : Blocks := vp00000000111001111_0
theorem coverp00000000111001111 : Covers (-28699139/62500 : ℚ) vp00000000111001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111001110_0 : Blocks := edgeBlocks% "full/vectors/00000000111001110-V-0000.bin"
noncomputable def vp00000000111001110 : Blocks := vp00000000111001110_0
theorem coverp00000000111001110 : Covers (-28636639/62500 : ℚ) vp00000000111001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011100111_0 : Blocks := edgeBlocks% "full/vectors/0000000011100111-V-0000.bin"
noncomputable def vp0000000011100111 : Blocks := vp0000000011100111_0
private theorem bp00000000111001110 : Branch 0 (-28636639/125000 : ℚ) vp0000000011100111 := by
  apply branch_left_normalized (c:=vp00000000111001110) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-28636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-28636639/62500 : ℚ) by norm_num]
  exact coverp00000000111001110
private noncomputable def ep00000000111001111_0 : Blocks := edgeBlocks% "full/vectors/00000000111001111-E-0000.bin"
noncomputable def ep00000000111001111 : Blocks := ep00000000111001111_0
private theorem idp00000000111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011100111.list =
    C ((2:ℤ)^43) * horner X vp00000000111001111.list + horner X ep00000000111001111.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111001111 : Branch 1 (-28636639/125000 : ℚ) vp0000000011100111 := by
  apply branch_checked idp00000000111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-28636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-28699139/62500 : ℚ) by norm_num]
  exact coverp00000000111001111
theorem coverp0000000011100111 : Covers (-28636639/125000 : ℚ) vp0000000011100111 := join_branches bp00000000111001110 bp00000000111001111
private noncomputable def vp000000001110011011_0 : Blocks := edgeBlocks% "full/vectors/000000001110011011-V-0000.bin"
noncomputable def vp000000001110011011 : Blocks := vp000000001110011011_0
theorem coverp000000001110011011 : Covers (-28605389/31250 : ℚ) vp000000001110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111001101011_0 : Blocks := edgeBlocks% "full/vectors/00000000111001101011-V-0000.bin"
noncomputable def vp00000000111001101011 : Blocks := vp00000000111001101011_0
theorem coverp00000000111001101011 : Covers (-57195153/15625 : ℚ) vp00000000111001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111001101010_0 : Blocks := edgeBlocks% "full/vectors/00000000111001101010-V-0000.bin"
noncomputable def vp00000000111001101010 : Blocks := vp00000000111001101010_0
theorem coverp00000000111001101010 : Covers (-57179528/15625 : ℚ) vp00000000111001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011100110101_0 : Blocks := edgeBlocks% "full/vectors/0000000011100110101-V-0000.bin"
noncomputable def vp0000000011100110101 : Blocks := vp0000000011100110101_0
private theorem bp00000000111001101010 : Branch 0 (-28589764/15625 : ℚ) vp0000000011100110101 := by
  apply branch_left_normalized (c:=vp00000000111001101010) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-28589764/15625 : ℚ) - ((0:ℤ):ℚ) = (-57179528/15625 : ℚ) by norm_num]
  exact coverp00000000111001101010
private noncomputable def ep00000000111001101011_0 : Blocks := edgeBlocks% "full/vectors/00000000111001101011-E-0000.bin"
noncomputable def ep00000000111001101011 : Blocks := ep00000000111001101011_0
private theorem idp00000000111001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011100110101.list =
    C ((2:ℤ)^15) * horner X vp00000000111001101011.list + horner X ep00000000111001101011.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111001101011 : Branch 1 (-28589764/15625 : ℚ) vp0000000011100110101 := by
  apply branch_checked idp00000000111001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-28589764/15625 : ℚ) - ((1:ℤ):ℚ) = (-57195153/15625 : ℚ) by norm_num]
  exact coverp00000000111001101011
theorem coverp0000000011100110101 : Covers (-28589764/15625 : ℚ) vp0000000011100110101 := join_branches bp00000000111001101010 bp00000000111001101011
private noncomputable def vp0000000011100110100_0 : Blocks := edgeBlocks% "full/vectors/0000000011100110100-V-0000.bin"
noncomputable def vp0000000011100110100 : Blocks := vp0000000011100110100_0
theorem coverp0000000011100110100 : Covers (-28574139/15625 : ℚ) vp0000000011100110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001110011010_0 : Blocks := edgeBlocks% "full/vectors/000000001110011010-V-0000.bin"
noncomputable def vp000000001110011010 : Blocks := vp000000001110011010_0
private theorem bp0000000011100110100 : Branch 0 (-28574139/31250 : ℚ) vp000000001110011010 := by
  apply branch_left_normalized (c:=vp0000000011100110100) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-28574139/31250 : ℚ) - ((0:ℤ):ℚ) = (-28574139/15625 : ℚ) by norm_num]
  exact coverp0000000011100110100
private noncomputable def ep0000000011100110101_0 : Blocks := edgeBlocks% "full/vectors/0000000011100110101-E-0000.bin"
noncomputable def ep0000000011100110101 : Blocks := ep0000000011100110101_0
private theorem idp0000000011100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110011010.list =
    C ((2:ℤ)^20) * horner X vp0000000011100110101.list + horner X ep0000000011100110101.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011100110101 : Branch 1 (-28574139/31250 : ℚ) vp000000001110011010 := by
  apply branch_checked idp0000000011100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-28574139/31250 : ℚ) - ((1:ℤ):ℚ) = (-28589764/15625 : ℚ) by norm_num]
  exact coverp0000000011100110101
theorem coverp000000001110011010 : Covers (-28574139/31250 : ℚ) vp000000001110011010 := join_branches bp0000000011100110100 bp0000000011100110101
private noncomputable def vp00000000111001101_0 : Blocks := edgeBlocks% "full/vectors/00000000111001101-V-0000.bin"
noncomputable def vp00000000111001101 : Blocks := vp00000000111001101_0
private theorem bp000000001110011010 : Branch 0 (-28574139/62500 : ℚ) vp00000000111001101 := by
  apply branch_left_normalized (c:=vp000000001110011010) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-28574139/62500 : ℚ) - ((0:ℤ):ℚ) = (-28574139/31250 : ℚ) by norm_num]
  exact coverp000000001110011010
private noncomputable def ep000000001110011011_0 : Blocks := edgeBlocks% "full/vectors/000000001110011011-E-0000.bin"
noncomputable def ep000000001110011011 : Blocks := ep000000001110011011_0
private theorem idp000000001110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111001101.list =
    C ((2:ℤ)^28) * horner X vp000000001110011011.list + horner X ep000000001110011011.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001110011011 : Branch 1 (-28574139/62500 : ℚ) vp00000000111001101 := by
  apply branch_checked idp000000001110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-28574139/62500 : ℚ) - ((1:ℤ):ℚ) = (-28605389/31250 : ℚ) by norm_num]
  exact coverp000000001110011011
theorem coverp00000000111001101 : Covers (-28574139/62500 : ℚ) vp00000000111001101 := join_branches bp000000001110011010 bp000000001110011011
private noncomputable def vp000000001110011001_0 : Blocks := edgeBlocks% "full/vectors/000000001110011001-V-0000.bin"
noncomputable def vp000000001110011001 : Blocks := vp000000001110011001_0
theorem coverp000000001110011001 : Covers (-28542889/31250 : ℚ) vp000000001110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001110011000_0 : Blocks := edgeBlocks% "full/vectors/000000001110011000-V-0000.bin"
noncomputable def vp000000001110011000 : Blocks := vp000000001110011000_0
theorem coverp000000001110011000 : Covers (-28511639/31250 : ℚ) vp000000001110011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111001100_0 : Blocks := edgeBlocks% "full/vectors/00000000111001100-V-0000.bin"
noncomputable def vp00000000111001100 : Blocks := vp00000000111001100_0
private theorem bp000000001110011000 : Branch 0 (-28511639/62500 : ℚ) vp00000000111001100 := by
  apply branch_left_normalized (c:=vp000000001110011000) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-28511639/62500 : ℚ) - ((0:ℤ):ℚ) = (-28511639/31250 : ℚ) by norm_num]
  exact coverp000000001110011000
private noncomputable def ep000000001110011001_0 : Blocks := edgeBlocks% "full/vectors/000000001110011001-E-0000.bin"
noncomputable def ep000000001110011001 : Blocks := ep000000001110011001_0
private theorem idp000000001110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111001100.list =
    C ((2:ℤ)^27) * horner X vp000000001110011001.list + horner X ep000000001110011001.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001110011001 : Branch 1 (-28511639/62500 : ℚ) vp00000000111001100 := by
  apply branch_checked idp000000001110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-28511639/62500 : ℚ) - ((1:ℤ):ℚ) = (-28542889/31250 : ℚ) by norm_num]
  exact coverp000000001110011001
theorem coverp00000000111001100 : Covers (-28511639/62500 : ℚ) vp00000000111001100 := join_branches bp000000001110011000 bp000000001110011001
private noncomputable def vp0000000011100110_0 : Blocks := edgeBlocks% "full/vectors/0000000011100110-V-0000.bin"
noncomputable def vp0000000011100110 : Blocks := vp0000000011100110_0
private theorem bp00000000111001100 : Branch 0 (-28511639/125000 : ℚ) vp0000000011100110 := by
  apply branch_left_normalized (c:=vp00000000111001100) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-28511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-28511639/62500 : ℚ) by norm_num]
  exact coverp00000000111001100
private noncomputable def ep00000000111001101_0 : Blocks := edgeBlocks% "full/vectors/00000000111001101-E-0000.bin"
noncomputable def ep00000000111001101 : Blocks := ep00000000111001101_0
private theorem idp00000000111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011100110.list =
    C ((2:ℤ)^41) * horner X vp00000000111001101.list + horner X ep00000000111001101.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111001101 : Branch 1 (-28511639/125000 : ℚ) vp0000000011100110 := by
  apply branch_checked idp00000000111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-28511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-28574139/62500 : ℚ) by norm_num]
  exact coverp00000000111001101
theorem coverp0000000011100110 : Covers (-28511639/125000 : ℚ) vp0000000011100110 := join_branches bp00000000111001100 bp00000000111001101
private noncomputable def vp000000001110011_0 : Blocks := edgeBlocks% "full/vectors/000000001110011-V-0000.bin"
noncomputable def vp000000001110011 : Blocks := vp000000001110011_0
private theorem bp0000000011100110 : Branch 0 (-28511639/250000 : ℚ) vp000000001110011 := by
  apply branch_left_normalized (c:=vp0000000011100110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-28511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-28511639/125000 : ℚ) by norm_num]
  exact coverp0000000011100110
private noncomputable def ep0000000011100111_0 : Blocks := edgeBlocks% "full/vectors/0000000011100111-E-0000.bin"
noncomputable def ep0000000011100111 : Blocks := ep0000000011100111_0
private theorem idp0000000011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110011.list =
    C ((2:ℤ)^65) * horner X vp0000000011100111.list + horner X ep0000000011100111.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011100111 : Branch 1 (-28511639/250000 : ℚ) vp000000001110011 := by
  apply branch_checked idp0000000011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-28511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-28636639/125000 : ℚ) by norm_num]
  exact coverp0000000011100111
theorem coverp000000001110011 : Covers (-28511639/250000 : ℚ) vp000000001110011 := join_branches bp0000000011100110 bp0000000011100111
private noncomputable def vp00000000111001011_0 : Blocks := edgeBlocks% "full/vectors/00000000111001011-V-0000.bin"
noncomputable def vp00000000111001011 : Blocks := vp00000000111001011_0
theorem coverp00000000111001011 : Covers (-28449139/62500 : ℚ) vp00000000111001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111001010_0 : Blocks := edgeBlocks% "full/vectors/00000000111001010-V-0000.bin"
noncomputable def vp00000000111001010 : Blocks := vp00000000111001010_0
theorem coverp00000000111001010 : Covers (-28386639/62500 : ℚ) vp00000000111001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011100101_0 : Blocks := edgeBlocks% "full/vectors/0000000011100101-V-0000.bin"
noncomputable def vp0000000011100101 : Blocks := vp0000000011100101_0
private theorem bp00000000111001010 : Branch 0 (-28386639/125000 : ℚ) vp0000000011100101 := by
  apply branch_left_normalized (c:=vp00000000111001010) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-28386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-28386639/62500 : ℚ) by norm_num]
  exact coverp00000000111001010
private noncomputable def ep00000000111001011_0 : Blocks := edgeBlocks% "full/vectors/00000000111001011-E-0000.bin"
noncomputable def ep00000000111001011 : Blocks := ep00000000111001011_0
private theorem idp00000000111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011100101.list =
    C ((2:ℤ)^45) * horner X vp00000000111001011.list + horner X ep00000000111001011.list := by
  exact edge_identity (B := (2:ℤ)^160) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111001011 : Branch 1 (-28386639/125000 : ℚ) vp0000000011100101 := by
  apply branch_checked idp00000000111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-28386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-28449139/62500 : ℚ) by norm_num]
  exact coverp00000000111001011
theorem coverp0000000011100101 : Covers (-28386639/125000 : ℚ) vp0000000011100101 := join_branches bp00000000111001010 bp00000000111001011
private noncomputable def vp000000001110010011_0 : Blocks := edgeBlocks% "full/vectors/000000001110010011-V-0000.bin"
noncomputable def vp000000001110010011 : Blocks := vp000000001110010011_0
theorem coverp000000001110010011 : Covers (-28355389/31250 : ℚ) vp000000001110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001110010010_0 : Blocks := edgeBlocks% "full/vectors/000000001110010010-V-0000.bin"
noncomputable def vp000000001110010010 : Blocks := vp000000001110010010_0
theorem coverp000000001110010010 : Covers (-28324139/31250 : ℚ) vp000000001110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111001001_0 : Blocks := edgeBlocks% "full/vectors/00000000111001001-V-0000.bin"
noncomputable def vp00000000111001001 : Blocks := vp00000000111001001_0
private theorem bp000000001110010010 : Branch 0 (-28324139/62500 : ℚ) vp00000000111001001 := by
  apply branch_left_normalized (c:=vp000000001110010010) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-28324139/62500 : ℚ) - ((0:ℤ):ℚ) = (-28324139/31250 : ℚ) by norm_num]
  exact coverp000000001110010010
private noncomputable def ep000000001110010011_0 : Blocks := edgeBlocks% "full/vectors/000000001110010011-E-0000.bin"
noncomputable def ep000000001110010011 : Blocks := ep000000001110010011_0
private theorem idp000000001110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111001001.list =
    C ((2:ℤ)^29) * horner X vp000000001110010011.list + horner X ep000000001110010011.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001110010011 : Branch 1 (-28324139/62500 : ℚ) vp00000000111001001 := by
  apply branch_checked idp000000001110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-28324139/62500 : ℚ) - ((1:ℤ):ℚ) = (-28355389/31250 : ℚ) by norm_num]
  exact coverp000000001110010011
theorem coverp00000000111001001 : Covers (-28324139/62500 : ℚ) vp00000000111001001 := join_branches bp000000001110010010 bp000000001110010011
private noncomputable def vp0000000011100100011_0 : Blocks := edgeBlocks% "full/vectors/0000000011100100011-V-0000.bin"
noncomputable def vp0000000011100100011 : Blocks := vp0000000011100100011_0
theorem coverp0000000011100100011 : Covers (-28308514/15625 : ℚ) vp0000000011100100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011100100010_0 : Blocks := edgeBlocks% "full/vectors/0000000011100100010-V-0000.bin"
noncomputable def vp0000000011100100010 : Blocks := vp0000000011100100010_0
theorem coverp0000000011100100010 : Covers (-28292889/15625 : ℚ) vp0000000011100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001110010001_0 : Blocks := edgeBlocks% "full/vectors/000000001110010001-V-0000.bin"
noncomputable def vp000000001110010001 : Blocks := vp000000001110010001_0
private theorem bp0000000011100100010 : Branch 0 (-28292889/31250 : ℚ) vp000000001110010001 := by
  apply branch_left_normalized (c:=vp0000000011100100010) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-28292889/31250 : ℚ) - ((0:ℤ):ℚ) = (-28292889/15625 : ℚ) by norm_num]
  exact coverp0000000011100100010
private noncomputable def ep0000000011100100011_0 : Blocks := edgeBlocks% "full/vectors/0000000011100100011-E-0000.bin"
noncomputable def ep0000000011100100011 : Blocks := ep0000000011100100011_0
private theorem idp0000000011100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110010001.list =
    C ((2:ℤ)^21) * horner X vp0000000011100100011.list + horner X ep0000000011100100011.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011100100011 : Branch 1 (-28292889/31250 : ℚ) vp000000001110010001 := by
  apply branch_checked idp0000000011100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-28292889/31250 : ℚ) - ((1:ℤ):ℚ) = (-28308514/15625 : ℚ) by norm_num]
  exact coverp0000000011100100011
theorem coverp000000001110010001 : Covers (-28292889/31250 : ℚ) vp000000001110010001 := join_branches bp0000000011100100010 bp0000000011100100011
private noncomputable def vp0000000011100100001_0 : Blocks := edgeBlocks% "full/vectors/0000000011100100001-V-0000.bin"
noncomputable def vp0000000011100100001 : Blocks := vp0000000011100100001_0
theorem coverp0000000011100100001 : Covers (-28277264/15625 : ℚ) vp0000000011100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011100100000_0 : Blocks := edgeBlocks% "full/vectors/0000000011100100000-V-0000.bin"
noncomputable def vp0000000011100100000 : Blocks := vp0000000011100100000_0
theorem coverp0000000011100100000 : Covers (-28261639/15625 : ℚ) vp0000000011100100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001110010000_0 : Blocks := edgeBlocks% "full/vectors/000000001110010000-V-0000.bin"
noncomputable def vp000000001110010000 : Blocks := vp000000001110010000_0
private theorem bp0000000011100100000 : Branch 0 (-28261639/31250 : ℚ) vp000000001110010000 := by
  apply branch_left_normalized (c:=vp0000000011100100000) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-28261639/31250 : ℚ) - ((0:ℤ):ℚ) = (-28261639/15625 : ℚ) by norm_num]
  exact coverp0000000011100100000
private noncomputable def ep0000000011100100001_0 : Blocks := edgeBlocks% "full/vectors/0000000011100100001-E-0000.bin"
noncomputable def ep0000000011100100001 : Blocks := ep0000000011100100001_0
private theorem idp0000000011100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110010000.list =
    C ((2:ℤ)^21) * horner X vp0000000011100100001.list + horner X ep0000000011100100001.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011100100001 : Branch 1 (-28261639/31250 : ℚ) vp000000001110010000 := by
  apply branch_checked idp0000000011100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-28261639/31250 : ℚ) - ((1:ℤ):ℚ) = (-28277264/15625 : ℚ) by norm_num]
  exact coverp0000000011100100001
theorem coverp000000001110010000 : Covers (-28261639/31250 : ℚ) vp000000001110010000 := join_branches bp0000000011100100000 bp0000000011100100001
private noncomputable def vp00000000111001000_0 : Blocks := edgeBlocks% "full/vectors/00000000111001000-V-0000.bin"
noncomputable def vp00000000111001000 : Blocks := vp00000000111001000_0
private theorem bp000000001110010000 : Branch 0 (-28261639/62500 : ℚ) vp00000000111001000 := by
  apply branch_left_normalized (c:=vp000000001110010000) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-28261639/62500 : ℚ) - ((0:ℤ):ℚ) = (-28261639/31250 : ℚ) by norm_num]
  exact coverp000000001110010000
private noncomputable def ep000000001110010001_0 : Blocks := edgeBlocks% "full/vectors/000000001110010001-E-0000.bin"
noncomputable def ep000000001110010001 : Blocks := ep000000001110010001_0
private theorem idp000000001110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111001000.list =
    C ((2:ℤ)^29) * horner X vp000000001110010001.list + horner X ep000000001110010001.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001110010001 : Branch 1 (-28261639/62500 : ℚ) vp00000000111001000 := by
  apply branch_checked idp000000001110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-28261639/62500 : ℚ) - ((1:ℤ):ℚ) = (-28292889/31250 : ℚ) by norm_num]
  exact coverp000000001110010001
theorem coverp00000000111001000 : Covers (-28261639/62500 : ℚ) vp00000000111001000 := join_branches bp000000001110010000 bp000000001110010001
private noncomputable def vp0000000011100100_0 : Blocks := edgeBlocks% "full/vectors/0000000011100100-V-0000.bin"
noncomputable def vp0000000011100100 : Blocks := vp0000000011100100_0
private theorem bp00000000111001000 : Branch 0 (-28261639/125000 : ℚ) vp0000000011100100 := by
  apply branch_left_normalized (c:=vp00000000111001000) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-28261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-28261639/62500 : ℚ) by norm_num]
  exact coverp00000000111001000
private noncomputable def ep00000000111001001_0 : Blocks := edgeBlocks% "full/vectors/00000000111001001-E-0000.bin"
noncomputable def ep00000000111001001 : Blocks := ep00000000111001001_0
private theorem idp00000000111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011100100.list =
    C ((2:ℤ)^42) * horner X vp00000000111001001.list + horner X ep00000000111001001.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111001001 : Branch 1 (-28261639/125000 : ℚ) vp0000000011100100 := by
  apply branch_checked idp00000000111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-28261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-28324139/62500 : ℚ) by norm_num]
  exact coverp00000000111001001
theorem coverp0000000011100100 : Covers (-28261639/125000 : ℚ) vp0000000011100100 := join_branches bp00000000111001000 bp00000000111001001
private noncomputable def vp000000001110010_0 : Blocks := edgeBlocks% "full/vectors/000000001110010-V-0000.bin"
noncomputable def vp000000001110010 : Blocks := vp000000001110010_0
private theorem bp0000000011100100 : Branch 0 (-28261639/250000 : ℚ) vp000000001110010 := by
  apply branch_left_normalized (c:=vp0000000011100100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-28261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-28261639/125000 : ℚ) by norm_num]
  exact coverp0000000011100100
private noncomputable def ep0000000011100101_0 : Blocks := edgeBlocks% "full/vectors/0000000011100101-E-0000.bin"
noncomputable def ep0000000011100101 : Blocks := ep0000000011100101_0
private theorem idp0000000011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110010.list =
    C ((2:ℤ)^67) * horner X vp0000000011100101.list + horner X ep0000000011100101.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011100101 : Branch 1 (-28261639/250000 : ℚ) vp000000001110010 := by
  apply branch_checked idp0000000011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-28261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-28386639/125000 : ℚ) by norm_num]
  exact coverp0000000011100101
theorem coverp000000001110010 : Covers (-28261639/250000 : ℚ) vp000000001110010 := join_branches bp0000000011100100 bp0000000011100101
private noncomputable def vp00000000111001_0 : Blocks := edgeBlocks% "full/vectors/00000000111001-V-0000.bin"
noncomputable def vp00000000111001 : Blocks := vp00000000111001_0
private theorem bp000000001110010 : Branch 0 (-28261639/500000 : ℚ) vp00000000111001 := by
  apply branch_left_normalized (c:=vp000000001110010) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-28261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-28261639/250000 : ℚ) by norm_num]
  exact coverp000000001110010
private noncomputable def ep000000001110011_0 : Blocks := edgeBlocks% "full/vectors/000000001110011-E-0000.bin"
noncomputable def ep000000001110011 : Blocks := ep000000001110011_0
private theorem idp000000001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111001.list =
    C ((2:ℤ)^118) * horner X vp000000001110011.list + horner X ep000000001110011.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001110011 : Branch 1 (-28261639/500000 : ℚ) vp00000000111001 := by
  apply branch_checked idp000000001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-28261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-28511639/250000 : ℚ) by norm_num]
  exact coverp000000001110011
theorem coverp00000000111001 : Covers (-28261639/500000 : ℚ) vp00000000111001 := join_branches bp000000001110010 bp000000001110011
private noncomputable def vp00000000111000111_0 : Blocks := edgeBlocks% "full/vectors/00000000111000111-V-0000.bin"
noncomputable def vp00000000111000111 : Blocks := vp00000000111000111_0
theorem coverp00000000111000111 : Covers (-28199139/62500 : ℚ) vp00000000111000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111000110_0 : Blocks := edgeBlocks% "full/vectors/00000000111000110-V-0000.bin"
noncomputable def vp00000000111000110 : Blocks := vp00000000111000110_0
theorem coverp00000000111000110 : Covers (-28136639/62500 : ℚ) vp00000000111000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011100011_0 : Blocks := edgeBlocks% "full/vectors/0000000011100011-V-0000.bin"
noncomputable def vp0000000011100011 : Blocks := vp0000000011100011_0
private theorem bp00000000111000110 : Branch 0 (-28136639/125000 : ℚ) vp0000000011100011 := by
  apply branch_left_normalized (c:=vp00000000111000110) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-28136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-28136639/62500 : ℚ) by norm_num]
  exact coverp00000000111000110
private noncomputable def ep00000000111000111_0 : Blocks := edgeBlocks% "full/vectors/00000000111000111-E-0000.bin"
noncomputable def ep00000000111000111 : Blocks := ep00000000111000111_0
private theorem idp00000000111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011100011.list =
    C ((2:ℤ)^41) * horner X vp00000000111000111.list + horner X ep00000000111000111.list := by
  exact edge_identity (B := (2:ℤ)^154) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111000111 : Branch 1 (-28136639/125000 : ℚ) vp0000000011100011 := by
  apply branch_checked idp00000000111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-28136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-28199139/62500 : ℚ) by norm_num]
  exact coverp00000000111000111
theorem coverp0000000011100011 : Covers (-28136639/125000 : ℚ) vp0000000011100011 := join_branches bp00000000111000110 bp00000000111000111
private noncomputable def vp00000000111000101_0 : Blocks := edgeBlocks% "full/vectors/00000000111000101-V-0000.bin"
noncomputable def vp00000000111000101 : Blocks := vp00000000111000101_0
theorem coverp00000000111000101 : Covers (-28074139/62500 : ℚ) vp00000000111000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000111000100_0 : Blocks := edgeBlocks% "full/vectors/00000000111000100-V-0000.bin"
noncomputable def vp00000000111000100 : Blocks := vp00000000111000100_0
theorem coverp00000000111000100 : Covers (-28011639/62500 : ℚ) vp00000000111000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011100010_0 : Blocks := edgeBlocks% "full/vectors/0000000011100010-V-0000.bin"
noncomputable def vp0000000011100010 : Blocks := vp0000000011100010_0
private theorem bp00000000111000100 : Branch 0 (-28011639/125000 : ℚ) vp0000000011100010 := by
  apply branch_left_normalized (c:=vp00000000111000100) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-28011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-28011639/62500 : ℚ) by norm_num]
  exact coverp00000000111000100
private noncomputable def ep00000000111000101_0 : Blocks := edgeBlocks% "full/vectors/00000000111000101-E-0000.bin"
noncomputable def ep00000000111000101 : Blocks := ep00000000111000101_0
private theorem idp00000000111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011100010.list =
    C ((2:ℤ)^41) * horner X vp00000000111000101.list + horner X ep00000000111000101.list := by
  exact edge_identity (B := (2:ℤ)^154) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111000101 : Branch 1 (-28011639/125000 : ℚ) vp0000000011100010 := by
  apply branch_checked idp00000000111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-28011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-28074139/62500 : ℚ) by norm_num]
  exact coverp00000000111000101
theorem coverp0000000011100010 : Covers (-28011639/125000 : ℚ) vp0000000011100010 := join_branches bp00000000111000100 bp00000000111000101
private noncomputable def vp000000001110001_0 : Blocks := edgeBlocks% "full/vectors/000000001110001-V-0000.bin"
noncomputable def vp000000001110001 : Blocks := vp000000001110001_0
private theorem bp0000000011100010 : Branch 0 (-28011639/250000 : ℚ) vp000000001110001 := by
  apply branch_left_normalized (c:=vp0000000011100010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-28011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-28011639/125000 : ℚ) by norm_num]
  exact coverp0000000011100010
private noncomputable def ep0000000011100011_0 : Blocks := edgeBlocks% "full/vectors/0000000011100011-E-0000.bin"
noncomputable def ep0000000011100011 : Blocks := ep0000000011100011_0
private theorem idp0000000011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110001.list =
    C ((2:ℤ)^65) * horner X vp0000000011100011.list + horner X ep0000000011100011.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011100011 : Branch 1 (-28011639/250000 : ℚ) vp000000001110001 := by
  apply branch_checked idp0000000011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-28011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-28136639/125000 : ℚ) by norm_num]
  exact coverp0000000011100011
theorem coverp000000001110001 : Covers (-28011639/250000 : ℚ) vp000000001110001 := join_branches bp0000000011100010 bp0000000011100011
private noncomputable def vp0000000011100001_0 : Blocks := edgeBlocks% "full/vectors/0000000011100001-V-0000.bin"
noncomputable def vp0000000011100001 : Blocks := vp0000000011100001_0
theorem coverp0000000011100001 : Covers (-27886639/125000 : ℚ) vp0000000011100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011100000_0 : Blocks := edgeBlocks% "full/vectors/0000000011100000-V-0000.bin"
noncomputable def vp0000000011100000 : Blocks := vp0000000011100000_0
theorem coverp0000000011100000 : Covers (-27761639/125000 : ℚ) vp0000000011100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001110000_0 : Blocks := edgeBlocks% "full/vectors/000000001110000-V-0000.bin"
noncomputable def vp000000001110000 : Blocks := vp000000001110000_0
private theorem bp0000000011100000 : Branch 0 (-27761639/250000 : ℚ) vp000000001110000 := by
  apply branch_left_normalized (c:=vp0000000011100000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-27761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-27761639/125000 : ℚ) by norm_num]
  exact coverp0000000011100000
private noncomputable def ep0000000011100001_0 : Blocks := edgeBlocks% "full/vectors/0000000011100001-E-0000.bin"
noncomputable def ep0000000011100001 : Blocks := ep0000000011100001_0
private theorem idp0000000011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110000.list =
    C ((2:ℤ)^67) * horner X vp0000000011100001.list + horner X ep0000000011100001.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011100001 : Branch 1 (-27761639/250000 : ℚ) vp000000001110000 := by
  apply branch_checked idp0000000011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-27761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-27886639/125000 : ℚ) by norm_num]
  exact coverp0000000011100001
theorem coverp000000001110000 : Covers (-27761639/250000 : ℚ) vp000000001110000 := join_branches bp0000000011100000 bp0000000011100001
private noncomputable def vp00000000111000_0 : Blocks := edgeBlocks% "full/vectors/00000000111000-V-0000.bin"
noncomputable def vp00000000111000 : Blocks := vp00000000111000_0
private theorem bp000000001110000 : Branch 0 (-27761639/500000 : ℚ) vp00000000111000 := by
  apply branch_left_normalized (c:=vp000000001110000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-27761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-27761639/250000 : ℚ) by norm_num]
  exact coverp000000001110000
private noncomputable def ep000000001110001_0 : Blocks := edgeBlocks% "full/vectors/000000001110001-E-0000.bin"
noncomputable def ep000000001110001 : Blocks := ep000000001110001_0
private theorem idp000000001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111000.list =
    C ((2:ℤ)^115) * horner X vp000000001110001.list + horner X ep000000001110001.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001110001 : Branch 1 (-27761639/500000 : ℚ) vp00000000111000 := by
  apply branch_checked idp000000001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-27761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-28011639/250000 : ℚ) by norm_num]
  exact coverp000000001110001
theorem coverp00000000111000 : Covers (-27761639/500000 : ℚ) vp00000000111000 := join_branches bp000000001110000 bp000000001110001
private noncomputable def vp0000000011100_0 : Blocks := edgeBlocks% "full/vectors/0000000011100-V-0000.bin"
private noncomputable def vp0000000011100_1 : Blocks := edgeBlocks% "full/vectors/0000000011100-V-0001.bin"
noncomputable def vp0000000011100 : Blocks := (Blocks.join vp0000000011100_0 vp0000000011100_1)
private theorem bp00000000111000 : Branch 0 (-27761639/1000000 : ℚ) vp0000000011100 := by
  apply branch_left_normalized (c:=vp00000000111000) (k:=0) (m:=112) (by decide +kernel)
  rw [show 2*(-27761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-27761639/500000 : ℚ) by norm_num]
  exact coverp00000000111000
private noncomputable def ep00000000111001_0 : Blocks := edgeBlocks% "full/vectors/00000000111001-E-0000.bin"
private noncomputable def ep00000000111001_1 : Blocks := edgeBlocks% "full/vectors/00000000111001-E-0001.bin"
noncomputable def ep00000000111001 : Blocks := (Blocks.join ep00000000111001_0 ep00000000111001_1)
private theorem idp00000000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011100.list =
    C ((2:ℤ)^206) * horner X vp00000000111001.list + horner X ep00000000111001.list := by
  exact edge_identity (B := (2:ℤ)^402) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111001 : Branch 1 (-27761639/1000000 : ℚ) vp0000000011100 := by
  apply branch_checked idp00000000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-27761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-28261639/500000 : ℚ) by norm_num]
  exact coverp00000000111001
theorem coverp0000000011100 : Covers (-27761639/1000000 : ℚ) vp0000000011100 := join_branches bp00000000111000 bp00000000111001
private noncomputable def vp000000001110_0 : Blocks := edgeBlocks% "full/vectors/000000001110-V-0000.bin"
private noncomputable def vp000000001110_1 : Blocks := edgeBlocks% "full/vectors/000000001110-V-0001.bin"
private noncomputable def vp000000001110_2 : Blocks := edgeBlocks% "full/vectors/000000001110-V-0002.bin"
private noncomputable def vp000000001110_3 : Blocks := edgeBlocks% "full/vectors/000000001110-V-0003.bin"
noncomputable def vp000000001110 : Blocks := (Blocks.join (Blocks.join vp000000001110_0 vp000000001110_1) (Blocks.join vp000000001110_2 vp000000001110_3))
private theorem bp0000000011100 : Branch 0 (-27761639/2000000 : ℚ) vp000000001110 := by
  apply branch_left_normalized (c:=vp0000000011100) (k:=0) (m:=205) (by decide +kernel)
  rw [show 2*(-27761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-27761639/1000000 : ℚ) by norm_num]
  exact coverp0000000011100
private noncomputable def ep0000000011101_0 : Blocks := edgeBlocks% "full/vectors/0000000011101-E-0000.bin"
private noncomputable def ep0000000011101_1 : Blocks := edgeBlocks% "full/vectors/0000000011101-E-0001.bin"
private noncomputable def ep0000000011101_2 : Blocks := edgeBlocks% "full/vectors/0000000011101-E-0002.bin"
private noncomputable def ep0000000011101_3 : Blocks := edgeBlocks% "full/vectors/0000000011101-E-0003.bin"
noncomputable def ep0000000011101 : Blocks := (Blocks.join (Blocks.join ep0000000011101_0 ep0000000011101_1) (Blocks.join ep0000000011101_2 ep0000000011101_3))
private theorem idp0000000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001110.list =
    C ((2:ℤ)^395) * horner X vp0000000011101.list + horner X ep0000000011101.list := by
  exact edge_identity (B := (2:ℤ)^685) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011101 : Branch 1 (-27761639/2000000 : ℚ) vp000000001110 := by
  apply branch_checked idp0000000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-27761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-28761639/1000000 : ℚ) by norm_num]
  exact coverp0000000011101
theorem coverp000000001110 : Covers (-27761639/2000000 : ℚ) vp000000001110 := join_branches bp0000000011100 bp0000000011101
private noncomputable def vp00000000111_0 : Blocks := edgeBlocks% "full/vectors/00000000111-V-0000.bin"
private noncomputable def vp00000000111_1 : Blocks := edgeBlocks% "full/vectors/00000000111-V-0001.bin"
private noncomputable def vp00000000111_2 : Blocks := edgeBlocks% "full/vectors/00000000111-V-0002.bin"
private noncomputable def vp00000000111_3 : Blocks := edgeBlocks% "full/vectors/00000000111-V-0003.bin"
private noncomputable def vp00000000111_4 : Blocks := edgeBlocks% "full/vectors/00000000111-V-0004.bin"
private noncomputable def vp00000000111_5 : Blocks := edgeBlocks% "full/vectors/00000000111-V-0005.bin"
noncomputable def vp00000000111 : Blocks := (Blocks.join (Blocks.join vp00000000111_0 (Blocks.join vp00000000111_1 vp00000000111_2)) (Blocks.join vp00000000111_3 (Blocks.join vp00000000111_4 vp00000000111_5)))
private theorem bp000000001110 : Branch 0 (-27761639/4000000 : ℚ) vp00000000111 := by
  apply branch_left_normalized (c:=vp000000001110) (k:=0) (m:=389) (by decide +kernel)
  rw [show 2*(-27761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-27761639/2000000 : ℚ) by norm_num]
  exact coverp000000001110
private noncomputable def ep000000001111_0 : Blocks := edgeBlocks% "full/vectors/000000001111-E-0000.bin"
private noncomputable def ep000000001111_1 : Blocks := edgeBlocks% "full/vectors/000000001111-E-0001.bin"
private noncomputable def ep000000001111_2 : Blocks := edgeBlocks% "full/vectors/000000001111-E-0002.bin"
private noncomputable def ep000000001111_3 : Blocks := edgeBlocks% "full/vectors/000000001111-E-0003.bin"
private noncomputable def ep000000001111_4 : Blocks := edgeBlocks% "full/vectors/000000001111-E-0004.bin"
private noncomputable def ep000000001111_5 : Blocks := edgeBlocks% "full/vectors/000000001111-E-0005.bin"
noncomputable def ep000000001111 : Blocks := (Blocks.join (Blocks.join ep000000001111_0 (Blocks.join ep000000001111_1 ep000000001111_2)) (Blocks.join ep000000001111_3 (Blocks.join ep000000001111_4 ep000000001111_5)))
private theorem idp000000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000111.list =
    C ((2:ℤ)^761) * horner X vp000000001111.list + horner X ep000000001111.list := by
  exact edge_identity (B := (2:ℤ)^1247) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001111 : Branch 1 (-27761639/4000000 : ℚ) vp00000000111 := by
  apply branch_checked idp000000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-27761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-29761639/2000000 : ℚ) by norm_num]
  exact coverp000000001111
theorem coverp00000000111 : Covers (-27761639/4000000 : ℚ) vp00000000111 := join_branches bp000000001110 bp000000001111
end NextProof.EdgeFull

