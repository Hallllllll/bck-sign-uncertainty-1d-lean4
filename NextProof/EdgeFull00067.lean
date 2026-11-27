import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00010011111111_0 : Blocks := edgeBlocks% "full/vectors/00010011111111-V-0000.bin"
noncomputable def vp00010011111111 : Blocks := vp00010011111111_0
theorem coverp00010011111111 : Covers (-639261639/500000 : ℚ) vp00010011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011111110_0 : Blocks := edgeBlocks% "full/vectors/00010011111110-V-0000.bin"
noncomputable def vp00010011111110 : Blocks := vp00010011111110_0
theorem coverp00010011111110 : Covers (-638761639/500000 : ℚ) vp00010011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001111111_0 : Blocks := edgeBlocks% "full/vectors/0001001111111-V-0000.bin"
noncomputable def vp0001001111111 : Blocks := vp0001001111111_0
private theorem bp00010011111110 : Branch 0 (-638761639/1000000 : ℚ) vp0001001111111 := by
  apply branch_left_normalized (c:=vp00010011111110) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-638761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-638761639/500000 : ℚ) by norm_num]
  exact coverp00010011111110
private noncomputable def ep00010011111111_0 : Blocks := edgeBlocks% "full/vectors/00010011111111-E-0000.bin"
noncomputable def ep00010011111111 : Blocks := ep00010011111111_0
private theorem idp00010011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001111111.list =
    C ((2:ℤ)^62) * horner X vp00010011111111.list + horner X ep00010011111111.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011111111 : Branch 1 (-638761639/1000000 : ℚ) vp0001001111111 := by
  apply branch_checked idp00010011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-638761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-639261639/500000 : ℚ) by norm_num]
  exact coverp00010011111111
theorem coverp0001001111111 : Covers (-638761639/1000000 : ℚ) vp0001001111111 := join_branches bp00010011111110 bp00010011111111
private noncomputable def vp00010011111101_0 : Blocks := edgeBlocks% "full/vectors/00010011111101-V-0000.bin"
noncomputable def vp00010011111101 : Blocks := vp00010011111101_0
theorem coverp00010011111101 : Covers (-638261639/500000 : ℚ) vp00010011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011111100_0 : Blocks := edgeBlocks% "full/vectors/00010011111100-V-0000.bin"
noncomputable def vp00010011111100 : Blocks := vp00010011111100_0
theorem coverp00010011111100 : Covers (-637761639/500000 : ℚ) vp00010011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001111110_0 : Blocks := edgeBlocks% "full/vectors/0001001111110-V-0000.bin"
noncomputable def vp0001001111110 : Blocks := vp0001001111110_0
private theorem bp00010011111100 : Branch 0 (-637761639/1000000 : ℚ) vp0001001111110 := by
  apply branch_left_normalized (c:=vp00010011111100) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-637761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-637761639/500000 : ℚ) by norm_num]
  exact coverp00010011111100
private noncomputable def ep00010011111101_0 : Blocks := edgeBlocks% "full/vectors/00010011111101-E-0000.bin"
noncomputable def ep00010011111101 : Blocks := ep00010011111101_0
private theorem idp00010011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001111110.list =
    C ((2:ℤ)^63) * horner X vp00010011111101.list + horner X ep00010011111101.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011111101 : Branch 1 (-637761639/1000000 : ℚ) vp0001001111110 := by
  apply branch_checked idp00010011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-637761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-638261639/500000 : ℚ) by norm_num]
  exact coverp00010011111101
theorem coverp0001001111110 : Covers (-637761639/1000000 : ℚ) vp0001001111110 := join_branches bp00010011111100 bp00010011111101
private noncomputable def vp000100111111_0 : Blocks := edgeBlocks% "full/vectors/000100111111-V-0000.bin"
noncomputable def vp000100111111 : Blocks := vp000100111111_0
private theorem bp0001001111110 : Branch 0 (-637761639/2000000 : ℚ) vp000100111111 := by
  apply branch_left_normalized (c:=vp0001001111110) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-637761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-637761639/1000000 : ℚ) by norm_num]
  exact coverp0001001111110
private noncomputable def ep0001001111111_0 : Blocks := edgeBlocks% "full/vectors/0001001111111-E-0000.bin"
noncomputable def ep0001001111111 : Blocks := ep0001001111111_0
private theorem idp0001001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100111111.list =
    C ((2:ℤ)^105) * horner X vp0001001111111.list + horner X ep0001001111111.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001111111 : Branch 1 (-637761639/2000000 : ℚ) vp000100111111 := by
  apply branch_checked idp0001001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-637761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-638761639/1000000 : ℚ) by norm_num]
  exact coverp0001001111111
theorem coverp000100111111 : Covers (-637761639/2000000 : ℚ) vp000100111111 := join_branches bp0001001111110 bp0001001111111
private noncomputable def vp00010011111011_0 : Blocks := edgeBlocks% "full/vectors/00010011111011-V-0000.bin"
noncomputable def vp00010011111011 : Blocks := vp00010011111011_0
theorem coverp00010011111011 : Covers (-637261639/500000 : ℚ) vp00010011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011111010_0 : Blocks := edgeBlocks% "full/vectors/00010011111010-V-0000.bin"
noncomputable def vp00010011111010 : Blocks := vp00010011111010_0
theorem coverp00010011111010 : Covers (-636761639/500000 : ℚ) vp00010011111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001111101_0 : Blocks := edgeBlocks% "full/vectors/0001001111101-V-0000.bin"
noncomputable def vp0001001111101 : Blocks := vp0001001111101_0
private theorem bp00010011111010 : Branch 0 (-636761639/1000000 : ℚ) vp0001001111101 := by
  apply branch_left_normalized (c:=vp00010011111010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-636761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-636761639/500000 : ℚ) by norm_num]
  exact coverp00010011111010
private noncomputable def ep00010011111011_0 : Blocks := edgeBlocks% "full/vectors/00010011111011-E-0000.bin"
noncomputable def ep00010011111011 : Blocks := ep00010011111011_0
private theorem idp00010011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001111101.list =
    C ((2:ℤ)^63) * horner X vp00010011111011.list + horner X ep00010011111011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011111011 : Branch 1 (-636761639/1000000 : ℚ) vp0001001111101 := by
  apply branch_checked idp00010011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-636761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-637261639/500000 : ℚ) by norm_num]
  exact coverp00010011111011
theorem coverp0001001111101 : Covers (-636761639/1000000 : ℚ) vp0001001111101 := join_branches bp00010011111010 bp00010011111011
private noncomputable def vp00010011111001_0 : Blocks := edgeBlocks% "full/vectors/00010011111001-V-0000.bin"
noncomputable def vp00010011111001 : Blocks := vp00010011111001_0
theorem coverp00010011111001 : Covers (-636261639/500000 : ℚ) vp00010011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011111000_0 : Blocks := edgeBlocks% "full/vectors/00010011111000-V-0000.bin"
noncomputable def vp00010011111000 : Blocks := vp00010011111000_0
theorem coverp00010011111000 : Covers (-635761639/500000 : ℚ) vp00010011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001111100_0 : Blocks := edgeBlocks% "full/vectors/0001001111100-V-0000.bin"
noncomputable def vp0001001111100 : Blocks := vp0001001111100_0
private theorem bp00010011111000 : Branch 0 (-635761639/1000000 : ℚ) vp0001001111100 := by
  apply branch_left_normalized (c:=vp00010011111000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-635761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-635761639/500000 : ℚ) by norm_num]
  exact coverp00010011111000
private noncomputable def ep00010011111001_0 : Blocks := edgeBlocks% "full/vectors/00010011111001-E-0000.bin"
noncomputable def ep00010011111001 : Blocks := ep00010011111001_0
private theorem idp00010011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001111100.list =
    C ((2:ℤ)^63) * horner X vp00010011111001.list + horner X ep00010011111001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011111001 : Branch 1 (-635761639/1000000 : ℚ) vp0001001111100 := by
  apply branch_checked idp00010011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-635761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-636261639/500000 : ℚ) by norm_num]
  exact coverp00010011111001
theorem coverp0001001111100 : Covers (-635761639/1000000 : ℚ) vp0001001111100 := join_branches bp00010011111000 bp00010011111001
private noncomputable def vp000100111110_0 : Blocks := edgeBlocks% "full/vectors/000100111110-V-0000.bin"
noncomputable def vp000100111110 : Blocks := vp000100111110_0
private theorem bp0001001111100 : Branch 0 (-635761639/2000000 : ℚ) vp000100111110 := by
  apply branch_left_normalized (c:=vp0001001111100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-635761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-635761639/1000000 : ℚ) by norm_num]
  exact coverp0001001111100
private noncomputable def ep0001001111101_0 : Blocks := edgeBlocks% "full/vectors/0001001111101-E-0000.bin"
noncomputable def ep0001001111101 : Blocks := ep0001001111101_0
private theorem idp0001001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100111110.list =
    C ((2:ℤ)^106) * horner X vp0001001111101.list + horner X ep0001001111101.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001111101 : Branch 1 (-635761639/2000000 : ℚ) vp000100111110 := by
  apply branch_checked idp0001001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-635761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-636761639/1000000 : ℚ) by norm_num]
  exact coverp0001001111101
theorem coverp000100111110 : Covers (-635761639/2000000 : ℚ) vp000100111110 := join_branches bp0001001111100 bp0001001111101
private noncomputable def vp00010011111_0 : Blocks := edgeBlocks% "full/vectors/00010011111-V-0000.bin"
private noncomputable def vp00010011111_1 : Blocks := edgeBlocks% "full/vectors/00010011111-V-0001.bin"
noncomputable def vp00010011111 : Blocks := (Blocks.join vp00010011111_0 vp00010011111_1)
private theorem bp000100111110 : Branch 0 (-635761639/4000000 : ℚ) vp00010011111 := by
  apply branch_left_normalized (c:=vp000100111110) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-635761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-635761639/2000000 : ℚ) by norm_num]
  exact coverp000100111110
private noncomputable def ep000100111111_0 : Blocks := edgeBlocks% "full/vectors/000100111111-E-0000.bin"
private noncomputable def ep000100111111_1 : Blocks := edgeBlocks% "full/vectors/000100111111-E-0001.bin"
noncomputable def ep000100111111 : Blocks := (Blocks.join ep000100111111_0 ep000100111111_1)
private theorem idp000100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010011111.list =
    C ((2:ℤ)^191) * horner X vp000100111111.list + horner X ep000100111111.list := by
  exact edge_identity (B := (2:ℤ)^364) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100111111 : Branch 1 (-635761639/4000000 : ℚ) vp00010011111 := by
  apply branch_checked idp000100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-635761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-637761639/2000000 : ℚ) by norm_num]
  exact coverp000100111111
theorem coverp00010011111 : Covers (-635761639/4000000 : ℚ) vp00010011111 := join_branches bp000100111110 bp000100111111
private noncomputable def vp00010011110111_0 : Blocks := edgeBlocks% "full/vectors/00010011110111-V-0000.bin"
noncomputable def vp00010011110111 : Blocks := vp00010011110111_0
theorem coverp00010011110111 : Covers (-635261639/500000 : ℚ) vp00010011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011110110_0 : Blocks := edgeBlocks% "full/vectors/00010011110110-V-0000.bin"
noncomputable def vp00010011110110 : Blocks := vp00010011110110_0
theorem coverp00010011110110 : Covers (-634761639/500000 : ℚ) vp00010011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001111011_0 : Blocks := edgeBlocks% "full/vectors/0001001111011-V-0000.bin"
noncomputable def vp0001001111011 : Blocks := vp0001001111011_0
private theorem bp00010011110110 : Branch 0 (-634761639/1000000 : ℚ) vp0001001111011 := by
  apply branch_left_normalized (c:=vp00010011110110) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-634761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-634761639/500000 : ℚ) by norm_num]
  exact coverp00010011110110
private noncomputable def ep00010011110111_0 : Blocks := edgeBlocks% "full/vectors/00010011110111-E-0000.bin"
noncomputable def ep00010011110111 : Blocks := ep00010011110111_0
private theorem idp00010011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001111011.list =
    C ((2:ℤ)^63) * horner X vp00010011110111.list + horner X ep00010011110111.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011110111 : Branch 1 (-634761639/1000000 : ℚ) vp0001001111011 := by
  apply branch_checked idp00010011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-634761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-635261639/500000 : ℚ) by norm_num]
  exact coverp00010011110111
theorem coverp0001001111011 : Covers (-634761639/1000000 : ℚ) vp0001001111011 := join_branches bp00010011110110 bp00010011110111
private noncomputable def vp00010011110101_0 : Blocks := edgeBlocks% "full/vectors/00010011110101-V-0000.bin"
noncomputable def vp00010011110101 : Blocks := vp00010011110101_0
theorem coverp00010011110101 : Covers (-634261639/500000 : ℚ) vp00010011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011110100_0 : Blocks := edgeBlocks% "full/vectors/00010011110100-V-0000.bin"
noncomputable def vp00010011110100 : Blocks := vp00010011110100_0
theorem coverp00010011110100 : Covers (-633761639/500000 : ℚ) vp00010011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001111010_0 : Blocks := edgeBlocks% "full/vectors/0001001111010-V-0000.bin"
noncomputable def vp0001001111010 : Blocks := vp0001001111010_0
private theorem bp00010011110100 : Branch 0 (-633761639/1000000 : ℚ) vp0001001111010 := by
  apply branch_left_normalized (c:=vp00010011110100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-633761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-633761639/500000 : ℚ) by norm_num]
  exact coverp00010011110100
private noncomputable def ep00010011110101_0 : Blocks := edgeBlocks% "full/vectors/00010011110101-E-0000.bin"
noncomputable def ep00010011110101 : Blocks := ep00010011110101_0
private theorem idp00010011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001111010.list =
    C ((2:ℤ)^62) * horner X vp00010011110101.list + horner X ep00010011110101.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011110101 : Branch 1 (-633761639/1000000 : ℚ) vp0001001111010 := by
  apply branch_checked idp00010011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-633761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-634261639/500000 : ℚ) by norm_num]
  exact coverp00010011110101
theorem coverp0001001111010 : Covers (-633761639/1000000 : ℚ) vp0001001111010 := join_branches bp00010011110100 bp00010011110101
private noncomputable def vp000100111101_0 : Blocks := edgeBlocks% "full/vectors/000100111101-V-0000.bin"
noncomputable def vp000100111101 : Blocks := vp000100111101_0
private theorem bp0001001111010 : Branch 0 (-633761639/2000000 : ℚ) vp000100111101 := by
  apply branch_left_normalized (c:=vp0001001111010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-633761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-633761639/1000000 : ℚ) by norm_num]
  exact coverp0001001111010
private noncomputable def ep0001001111011_0 : Blocks := edgeBlocks% "full/vectors/0001001111011-E-0000.bin"
noncomputable def ep0001001111011 : Blocks := ep0001001111011_0
private theorem idp0001001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100111101.list =
    C ((2:ℤ)^105) * horner X vp0001001111011.list + horner X ep0001001111011.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001111011 : Branch 1 (-633761639/2000000 : ℚ) vp000100111101 := by
  apply branch_checked idp0001001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-633761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-634761639/1000000 : ℚ) by norm_num]
  exact coverp0001001111011
theorem coverp000100111101 : Covers (-633761639/2000000 : ℚ) vp000100111101 := join_branches bp0001001111010 bp0001001111011
private noncomputable def vp00010011110011_0 : Blocks := edgeBlocks% "full/vectors/00010011110011-V-0000.bin"
noncomputable def vp00010011110011 : Blocks := vp00010011110011_0
theorem coverp00010011110011 : Covers (-633261639/500000 : ℚ) vp00010011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011110010_0 : Blocks := edgeBlocks% "full/vectors/00010011110010-V-0000.bin"
noncomputable def vp00010011110010 : Blocks := vp00010011110010_0
theorem coverp00010011110010 : Covers (-632761639/500000 : ℚ) vp00010011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001111001_0 : Blocks := edgeBlocks% "full/vectors/0001001111001-V-0000.bin"
noncomputable def vp0001001111001 : Blocks := vp0001001111001_0
private theorem bp00010011110010 : Branch 0 (-632761639/1000000 : ℚ) vp0001001111001 := by
  apply branch_left_normalized (c:=vp00010011110010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-632761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-632761639/500000 : ℚ) by norm_num]
  exact coverp00010011110010
private noncomputable def ep00010011110011_0 : Blocks := edgeBlocks% "full/vectors/00010011110011-E-0000.bin"
noncomputable def ep00010011110011 : Blocks := ep00010011110011_0
private theorem idp00010011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001111001.list =
    C ((2:ℤ)^63) * horner X vp00010011110011.list + horner X ep00010011110011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011110011 : Branch 1 (-632761639/1000000 : ℚ) vp0001001111001 := by
  apply branch_checked idp00010011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-632761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-633261639/500000 : ℚ) by norm_num]
  exact coverp00010011110011
theorem coverp0001001111001 : Covers (-632761639/1000000 : ℚ) vp0001001111001 := join_branches bp00010011110010 bp00010011110011
private noncomputable def vp00010011110001_0 : Blocks := edgeBlocks% "full/vectors/00010011110001-V-0000.bin"
noncomputable def vp00010011110001 : Blocks := vp00010011110001_0
theorem coverp00010011110001 : Covers (-632261639/500000 : ℚ) vp00010011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011110000_0 : Blocks := edgeBlocks% "full/vectors/00010011110000-V-0000.bin"
noncomputable def vp00010011110000 : Blocks := vp00010011110000_0
theorem coverp00010011110000 : Covers (-631761639/500000 : ℚ) vp00010011110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001111000_0 : Blocks := edgeBlocks% "full/vectors/0001001111000-V-0000.bin"
noncomputable def vp0001001111000 : Blocks := vp0001001111000_0
private theorem bp00010011110000 : Branch 0 (-631761639/1000000 : ℚ) vp0001001111000 := by
  apply branch_left_normalized (c:=vp00010011110000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-631761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-631761639/500000 : ℚ) by norm_num]
  exact coverp00010011110000
private noncomputable def ep00010011110001_0 : Blocks := edgeBlocks% "full/vectors/00010011110001-E-0000.bin"
noncomputable def ep00010011110001 : Blocks := ep00010011110001_0
private theorem idp00010011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001111000.list =
    C ((2:ℤ)^63) * horner X vp00010011110001.list + horner X ep00010011110001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011110001 : Branch 1 (-631761639/1000000 : ℚ) vp0001001111000 := by
  apply branch_checked idp00010011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-631761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-632261639/500000 : ℚ) by norm_num]
  exact coverp00010011110001
theorem coverp0001001111000 : Covers (-631761639/1000000 : ℚ) vp0001001111000 := join_branches bp00010011110000 bp00010011110001
private noncomputable def vp000100111100_0 : Blocks := edgeBlocks% "full/vectors/000100111100-V-0000.bin"
noncomputable def vp000100111100 : Blocks := vp000100111100_0
private theorem bp0001001111000 : Branch 0 (-631761639/2000000 : ℚ) vp000100111100 := by
  apply branch_left_normalized (c:=vp0001001111000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-631761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-631761639/1000000 : ℚ) by norm_num]
  exact coverp0001001111000
private noncomputable def ep0001001111001_0 : Blocks := edgeBlocks% "full/vectors/0001001111001-E-0000.bin"
noncomputable def ep0001001111001 : Blocks := ep0001001111001_0
private theorem idp0001001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100111100.list =
    C ((2:ℤ)^106) * horner X vp0001001111001.list + horner X ep0001001111001.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001111001 : Branch 1 (-631761639/2000000 : ℚ) vp000100111100 := by
  apply branch_checked idp0001001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-631761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-632761639/1000000 : ℚ) by norm_num]
  exact coverp0001001111001
theorem coverp000100111100 : Covers (-631761639/2000000 : ℚ) vp000100111100 := join_branches bp0001001111000 bp0001001111001
private noncomputable def vp00010011110_0 : Blocks := edgeBlocks% "full/vectors/00010011110-V-0000.bin"
private noncomputable def vp00010011110_1 : Blocks := edgeBlocks% "full/vectors/00010011110-V-0001.bin"
noncomputable def vp00010011110 : Blocks := (Blocks.join vp00010011110_0 vp00010011110_1)
private theorem bp000100111100 : Branch 0 (-631761639/4000000 : ℚ) vp00010011110 := by
  apply branch_left_normalized (c:=vp000100111100) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-631761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-631761639/2000000 : ℚ) by norm_num]
  exact coverp000100111100
private noncomputable def ep000100111101_0 : Blocks := edgeBlocks% "full/vectors/000100111101-E-0000.bin"
private noncomputable def ep000100111101_1 : Blocks := edgeBlocks% "full/vectors/000100111101-E-0001.bin"
noncomputable def ep000100111101 : Blocks := (Blocks.join ep000100111101_0 ep000100111101_1)
private theorem idp000100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010011110.list =
    C ((2:ℤ)^192) * horner X vp000100111101.list + horner X ep000100111101.list := by
  exact edge_identity (B := (2:ℤ)^365) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100111101 : Branch 1 (-631761639/4000000 : ℚ) vp00010011110 := by
  apply branch_checked idp000100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-631761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-633761639/2000000 : ℚ) by norm_num]
  exact coverp000100111101
theorem coverp00010011110 : Covers (-631761639/4000000 : ℚ) vp00010011110 := join_branches bp000100111100 bp000100111101
private noncomputable def vp0001001111_0 : Blocks := edgeBlocks% "full/vectors/0001001111-V-0000.bin"
private noncomputable def vp0001001111_1 : Blocks := edgeBlocks% "full/vectors/0001001111-V-0001.bin"
private noncomputable def vp0001001111_2 : Blocks := edgeBlocks% "full/vectors/0001001111-V-0002.bin"
noncomputable def vp0001001111 : Blocks := (Blocks.join vp0001001111_0 (Blocks.join vp0001001111_1 vp0001001111_2))
private theorem bp00010011110 : Branch 0 (-631761639/8000000 : ℚ) vp0001001111 := by
  apply branch_left_normalized (c:=vp00010011110) (k:=0) (m:=179) (by decide +kernel)
  rw [show 2*(-631761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-631761639/4000000 : ℚ) by norm_num]
  exact coverp00010011110
private noncomputable def ep00010011111_0 : Blocks := edgeBlocks% "full/vectors/00010011111-E-0000.bin"
private noncomputable def ep00010011111_1 : Blocks := edgeBlocks% "full/vectors/00010011111-E-0001.bin"
private noncomputable def ep00010011111_2 : Blocks := edgeBlocks% "full/vectors/00010011111-E-0002.bin"
noncomputable def ep00010011111 : Blocks := (Blocks.join ep00010011111_0 (Blocks.join ep00010011111_1 ep00010011111_2))
private theorem idp00010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001111.list =
    C ((2:ℤ)^359) * horner X vp00010011111.list + horner X ep00010011111.list := by
  exact edge_identity (B := (2:ℤ)^604) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011111 : Branch 1 (-631761639/8000000 : ℚ) vp0001001111 := by
  apply branch_checked idp00010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-631761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-635761639/4000000 : ℚ) by norm_num]
  exact coverp00010011111
theorem coverp0001001111 : Covers (-631761639/8000000 : ℚ) vp0001001111 := join_branches bp00010011110 bp00010011111
private noncomputable def vp00010011101111_0 : Blocks := edgeBlocks% "full/vectors/00010011101111-V-0000.bin"
noncomputable def vp00010011101111 : Blocks := vp00010011101111_0
theorem coverp00010011101111 : Covers (-631261639/500000 : ℚ) vp00010011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011101110_0 : Blocks := edgeBlocks% "full/vectors/00010011101110-V-0000.bin"
noncomputable def vp00010011101110 : Blocks := vp00010011101110_0
theorem coverp00010011101110 : Covers (-630761639/500000 : ℚ) vp00010011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001110111_0 : Blocks := edgeBlocks% "full/vectors/0001001110111-V-0000.bin"
noncomputable def vp0001001110111 : Blocks := vp0001001110111_0
private theorem bp00010011101110 : Branch 0 (-630761639/1000000 : ℚ) vp0001001110111 := by
  apply branch_left_normalized (c:=vp00010011101110) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-630761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-630761639/500000 : ℚ) by norm_num]
  exact coverp00010011101110
private noncomputable def ep00010011101111_0 : Blocks := edgeBlocks% "full/vectors/00010011101111-E-0000.bin"
noncomputable def ep00010011101111 : Blocks := ep00010011101111_0
private theorem idp00010011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001110111.list =
    C ((2:ℤ)^63) * horner X vp00010011101111.list + horner X ep00010011101111.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011101111 : Branch 1 (-630761639/1000000 : ℚ) vp0001001110111 := by
  apply branch_checked idp00010011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-630761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-631261639/500000 : ℚ) by norm_num]
  exact coverp00010011101111
theorem coverp0001001110111 : Covers (-630761639/1000000 : ℚ) vp0001001110111 := join_branches bp00010011101110 bp00010011101111
private noncomputable def vp00010011101101_0 : Blocks := edgeBlocks% "full/vectors/00010011101101-V-0000.bin"
noncomputable def vp00010011101101 : Blocks := vp00010011101101_0
theorem coverp00010011101101 : Covers (-630261639/500000 : ℚ) vp00010011101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011101100_0 : Blocks := edgeBlocks% "full/vectors/00010011101100-V-0000.bin"
noncomputable def vp00010011101100 : Blocks := vp00010011101100_0
theorem coverp00010011101100 : Covers (-629761639/500000 : ℚ) vp00010011101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001110110_0 : Blocks := edgeBlocks% "full/vectors/0001001110110-V-0000.bin"
noncomputable def vp0001001110110 : Blocks := vp0001001110110_0
private theorem bp00010011101100 : Branch 0 (-629761639/1000000 : ℚ) vp0001001110110 := by
  apply branch_left_normalized (c:=vp00010011101100) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-629761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-629761639/500000 : ℚ) by norm_num]
  exact coverp00010011101100
private noncomputable def ep00010011101101_0 : Blocks := edgeBlocks% "full/vectors/00010011101101-E-0000.bin"
noncomputable def ep00010011101101 : Blocks := ep00010011101101_0
private theorem idp00010011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001110110.list =
    C ((2:ℤ)^62) * horner X vp00010011101101.list + horner X ep00010011101101.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011101101 : Branch 1 (-629761639/1000000 : ℚ) vp0001001110110 := by
  apply branch_checked idp00010011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-629761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-630261639/500000 : ℚ) by norm_num]
  exact coverp00010011101101
theorem coverp0001001110110 : Covers (-629761639/1000000 : ℚ) vp0001001110110 := join_branches bp00010011101100 bp00010011101101
private noncomputable def vp000100111011_0 : Blocks := edgeBlocks% "full/vectors/000100111011-V-0000.bin"
noncomputable def vp000100111011 : Blocks := vp000100111011_0
private theorem bp0001001110110 : Branch 0 (-629761639/2000000 : ℚ) vp000100111011 := by
  apply branch_left_normalized (c:=vp0001001110110) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-629761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-629761639/1000000 : ℚ) by norm_num]
  exact coverp0001001110110
private noncomputable def ep0001001110111_0 : Blocks := edgeBlocks% "full/vectors/0001001110111-E-0000.bin"
noncomputable def ep0001001110111 : Blocks := ep0001001110111_0
private theorem idp0001001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100111011.list =
    C ((2:ℤ)^106) * horner X vp0001001110111.list + horner X ep0001001110111.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001110111 : Branch 1 (-629761639/2000000 : ℚ) vp000100111011 := by
  apply branch_checked idp0001001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-629761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-630761639/1000000 : ℚ) by norm_num]
  exact coverp0001001110111
theorem coverp000100111011 : Covers (-629761639/2000000 : ℚ) vp000100111011 := join_branches bp0001001110110 bp0001001110111
private noncomputable def vp00010011101011_0 : Blocks := edgeBlocks% "full/vectors/00010011101011-V-0000.bin"
noncomputable def vp00010011101011 : Blocks := vp00010011101011_0
theorem coverp00010011101011 : Covers (-629261639/500000 : ℚ) vp00010011101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011101010_0 : Blocks := edgeBlocks% "full/vectors/00010011101010-V-0000.bin"
noncomputable def vp00010011101010 : Blocks := vp00010011101010_0
theorem coverp00010011101010 : Covers (-628761639/500000 : ℚ) vp00010011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001110101_0 : Blocks := edgeBlocks% "full/vectors/0001001110101-V-0000.bin"
noncomputable def vp0001001110101 : Blocks := vp0001001110101_0
private theorem bp00010011101010 : Branch 0 (-628761639/1000000 : ℚ) vp0001001110101 := by
  apply branch_left_normalized (c:=vp00010011101010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-628761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-628761639/500000 : ℚ) by norm_num]
  exact coverp00010011101010
private noncomputable def ep00010011101011_0 : Blocks := edgeBlocks% "full/vectors/00010011101011-E-0000.bin"
noncomputable def ep00010011101011 : Blocks := ep00010011101011_0
private theorem idp00010011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001110101.list =
    C ((2:ℤ)^63) * horner X vp00010011101011.list + horner X ep00010011101011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011101011 : Branch 1 (-628761639/1000000 : ℚ) vp0001001110101 := by
  apply branch_checked idp00010011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-628761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-629261639/500000 : ℚ) by norm_num]
  exact coverp00010011101011
theorem coverp0001001110101 : Covers (-628761639/1000000 : ℚ) vp0001001110101 := join_branches bp00010011101010 bp00010011101011
private noncomputable def vp00010011101001_0 : Blocks := edgeBlocks% "full/vectors/00010011101001-V-0000.bin"
noncomputable def vp00010011101001 : Blocks := vp00010011101001_0
theorem coverp00010011101001 : Covers (-628261639/500000 : ℚ) vp00010011101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011101000_0 : Blocks := edgeBlocks% "full/vectors/00010011101000-V-0000.bin"
noncomputable def vp00010011101000 : Blocks := vp00010011101000_0
theorem coverp00010011101000 : Covers (-627761639/500000 : ℚ) vp00010011101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001110100_0 : Blocks := edgeBlocks% "full/vectors/0001001110100-V-0000.bin"
noncomputable def vp0001001110100 : Blocks := vp0001001110100_0
private theorem bp00010011101000 : Branch 0 (-627761639/1000000 : ℚ) vp0001001110100 := by
  apply branch_left_normalized (c:=vp00010011101000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-627761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-627761639/500000 : ℚ) by norm_num]
  exact coverp00010011101000
private noncomputable def ep00010011101001_0 : Blocks := edgeBlocks% "full/vectors/00010011101001-E-0000.bin"
noncomputable def ep00010011101001 : Blocks := ep00010011101001_0
private theorem idp00010011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001110100.list =
    C ((2:ℤ)^63) * horner X vp00010011101001.list + horner X ep00010011101001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011101001 : Branch 1 (-627761639/1000000 : ℚ) vp0001001110100 := by
  apply branch_checked idp00010011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-627761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-628261639/500000 : ℚ) by norm_num]
  exact coverp00010011101001
theorem coverp0001001110100 : Covers (-627761639/1000000 : ℚ) vp0001001110100 := join_branches bp00010011101000 bp00010011101001
private noncomputable def vp000100111010_0 : Blocks := edgeBlocks% "full/vectors/000100111010-V-0000.bin"
noncomputable def vp000100111010 : Blocks := vp000100111010_0
private theorem bp0001001110100 : Branch 0 (-627761639/2000000 : ℚ) vp000100111010 := by
  apply branch_left_normalized (c:=vp0001001110100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-627761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-627761639/1000000 : ℚ) by norm_num]
  exact coverp0001001110100
private noncomputable def ep0001001110101_0 : Blocks := edgeBlocks% "full/vectors/0001001110101-E-0000.bin"
noncomputable def ep0001001110101 : Blocks := ep0001001110101_0
private theorem idp0001001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100111010.list =
    C ((2:ℤ)^107) * horner X vp0001001110101.list + horner X ep0001001110101.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001110101 : Branch 1 (-627761639/2000000 : ℚ) vp000100111010 := by
  apply branch_checked idp0001001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-627761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-628761639/1000000 : ℚ) by norm_num]
  exact coverp0001001110101
theorem coverp000100111010 : Covers (-627761639/2000000 : ℚ) vp000100111010 := join_branches bp0001001110100 bp0001001110101
private noncomputable def vp00010011101_0 : Blocks := edgeBlocks% "full/vectors/00010011101-V-0000.bin"
private noncomputable def vp00010011101_1 : Blocks := edgeBlocks% "full/vectors/00010011101-V-0001.bin"
noncomputable def vp00010011101 : Blocks := (Blocks.join vp00010011101_0 vp00010011101_1)
private theorem bp000100111010 : Branch 0 (-627761639/4000000 : ℚ) vp00010011101 := by
  apply branch_left_normalized (c:=vp000100111010) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-627761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-627761639/2000000 : ℚ) by norm_num]
  exact coverp000100111010
private noncomputable def ep000100111011_0 : Blocks := edgeBlocks% "full/vectors/000100111011-E-0000.bin"
private noncomputable def ep000100111011_1 : Blocks := edgeBlocks% "full/vectors/000100111011-E-0001.bin"
noncomputable def ep000100111011 : Blocks := (Blocks.join ep000100111011_0 ep000100111011_1)
private theorem idp000100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010011101.list =
    C ((2:ℤ)^192) * horner X vp000100111011.list + horner X ep000100111011.list := by
  exact edge_identity (B := (2:ℤ)^365) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100111011 : Branch 1 (-627761639/4000000 : ℚ) vp00010011101 := by
  apply branch_checked idp000100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-627761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-629761639/2000000 : ℚ) by norm_num]
  exact coverp000100111011
theorem coverp00010011101 : Covers (-627761639/4000000 : ℚ) vp00010011101 := join_branches bp000100111010 bp000100111011
private noncomputable def vp00010011100111_0 : Blocks := edgeBlocks% "full/vectors/00010011100111-V-0000.bin"
noncomputable def vp00010011100111 : Blocks := vp00010011100111_0
theorem coverp00010011100111 : Covers (-627261639/500000 : ℚ) vp00010011100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011100110_0 : Blocks := edgeBlocks% "full/vectors/00010011100110-V-0000.bin"
noncomputable def vp00010011100110 : Blocks := vp00010011100110_0
theorem coverp00010011100110 : Covers (-626761639/500000 : ℚ) vp00010011100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001110011_0 : Blocks := edgeBlocks% "full/vectors/0001001110011-V-0000.bin"
noncomputable def vp0001001110011 : Blocks := vp0001001110011_0
private theorem bp00010011100110 : Branch 0 (-626761639/1000000 : ℚ) vp0001001110011 := by
  apply branch_left_normalized (c:=vp00010011100110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-626761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-626761639/500000 : ℚ) by norm_num]
  exact coverp00010011100110
private noncomputable def ep00010011100111_0 : Blocks := edgeBlocks% "full/vectors/00010011100111-E-0000.bin"
noncomputable def ep00010011100111 : Blocks := ep00010011100111_0
private theorem idp00010011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001110011.list =
    C ((2:ℤ)^63) * horner X vp00010011100111.list + horner X ep00010011100111.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011100111 : Branch 1 (-626761639/1000000 : ℚ) vp0001001110011 := by
  apply branch_checked idp00010011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-626761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-627261639/500000 : ℚ) by norm_num]
  exact coverp00010011100111
theorem coverp0001001110011 : Covers (-626761639/1000000 : ℚ) vp0001001110011 := join_branches bp00010011100110 bp00010011100111
private noncomputable def vp00010011100101_0 : Blocks := edgeBlocks% "full/vectors/00010011100101-V-0000.bin"
noncomputable def vp00010011100101 : Blocks := vp00010011100101_0
theorem coverp00010011100101 : Covers (-626261639/500000 : ℚ) vp00010011100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011100100_0 : Blocks := edgeBlocks% "full/vectors/00010011100100-V-0000.bin"
noncomputable def vp00010011100100 : Blocks := vp00010011100100_0
theorem coverp00010011100100 : Covers (-625761639/500000 : ℚ) vp00010011100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001110010_0 : Blocks := edgeBlocks% "full/vectors/0001001110010-V-0000.bin"
noncomputable def vp0001001110010 : Blocks := vp0001001110010_0
private theorem bp00010011100100 : Branch 0 (-625761639/1000000 : ℚ) vp0001001110010 := by
  apply branch_left_normalized (c:=vp00010011100100) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-625761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-625761639/500000 : ℚ) by norm_num]
  exact coverp00010011100100
private noncomputable def ep00010011100101_0 : Blocks := edgeBlocks% "full/vectors/00010011100101-E-0000.bin"
noncomputable def ep00010011100101 : Blocks := ep00010011100101_0
private theorem idp00010011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001110010.list =
    C ((2:ℤ)^63) * horner X vp00010011100101.list + horner X ep00010011100101.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011100101 : Branch 1 (-625761639/1000000 : ℚ) vp0001001110010 := by
  apply branch_checked idp00010011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-625761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-626261639/500000 : ℚ) by norm_num]
  exact coverp00010011100101
theorem coverp0001001110010 : Covers (-625761639/1000000 : ℚ) vp0001001110010 := join_branches bp00010011100100 bp00010011100101
private noncomputable def vp000100111001_0 : Blocks := edgeBlocks% "full/vectors/000100111001-V-0000.bin"
noncomputable def vp000100111001 : Blocks := vp000100111001_0
private theorem bp0001001110010 : Branch 0 (-625761639/2000000 : ℚ) vp000100111001 := by
  apply branch_left_normalized (c:=vp0001001110010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-625761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-625761639/1000000 : ℚ) by norm_num]
  exact coverp0001001110010
private noncomputable def ep0001001110011_0 : Blocks := edgeBlocks% "full/vectors/0001001110011-E-0000.bin"
noncomputable def ep0001001110011 : Blocks := ep0001001110011_0
private theorem idp0001001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100111001.list =
    C ((2:ℤ)^107) * horner X vp0001001110011.list + horner X ep0001001110011.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001110011 : Branch 1 (-625761639/2000000 : ℚ) vp000100111001 := by
  apply branch_checked idp0001001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-625761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-626761639/1000000 : ℚ) by norm_num]
  exact coverp0001001110011
theorem coverp000100111001 : Covers (-625761639/2000000 : ℚ) vp000100111001 := join_branches bp0001001110010 bp0001001110011
private noncomputable def vp00010011100011_0 : Blocks := edgeBlocks% "full/vectors/00010011100011-V-0000.bin"
noncomputable def vp00010011100011 : Blocks := vp00010011100011_0
theorem coverp00010011100011 : Covers (-625261639/500000 : ℚ) vp00010011100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011100010_0 : Blocks := edgeBlocks% "full/vectors/00010011100010-V-0000.bin"
noncomputable def vp00010011100010 : Blocks := vp00010011100010_0
theorem coverp00010011100010 : Covers (-624761639/500000 : ℚ) vp00010011100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001110001_0 : Blocks := edgeBlocks% "full/vectors/0001001110001-V-0000.bin"
noncomputable def vp0001001110001 : Blocks := vp0001001110001_0
private theorem bp00010011100010 : Branch 0 (-624761639/1000000 : ℚ) vp0001001110001 := by
  apply branch_left_normalized (c:=vp00010011100010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-624761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-624761639/500000 : ℚ) by norm_num]
  exact coverp00010011100010
private noncomputable def ep00010011100011_0 : Blocks := edgeBlocks% "full/vectors/00010011100011-E-0000.bin"
noncomputable def ep00010011100011 : Blocks := ep00010011100011_0
private theorem idp00010011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001110001.list =
    C ((2:ℤ)^63) * horner X vp00010011100011.list + horner X ep00010011100011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011100011 : Branch 1 (-624761639/1000000 : ℚ) vp0001001110001 := by
  apply branch_checked idp00010011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-624761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-625261639/500000 : ℚ) by norm_num]
  exact coverp00010011100011
theorem coverp0001001110001 : Covers (-624761639/1000000 : ℚ) vp0001001110001 := join_branches bp00010011100010 bp00010011100011
private noncomputable def vp00010011100001_0 : Blocks := edgeBlocks% "full/vectors/00010011100001-V-0000.bin"
noncomputable def vp00010011100001 : Blocks := vp00010011100001_0
theorem coverp00010011100001 : Covers (-624261639/500000 : ℚ) vp00010011100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011100000_0 : Blocks := edgeBlocks% "full/vectors/00010011100000-V-0000.bin"
noncomputable def vp00010011100000 : Blocks := vp00010011100000_0
theorem coverp00010011100000 : Covers (-623761639/500000 : ℚ) vp00010011100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001110000_0 : Blocks := edgeBlocks% "full/vectors/0001001110000-V-0000.bin"
noncomputable def vp0001001110000 : Blocks := vp0001001110000_0
private theorem bp00010011100000 : Branch 0 (-623761639/1000000 : ℚ) vp0001001110000 := by
  apply branch_left_normalized (c:=vp00010011100000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-623761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-623761639/500000 : ℚ) by norm_num]
  exact coverp00010011100000
private noncomputable def ep00010011100001_0 : Blocks := edgeBlocks% "full/vectors/00010011100001-E-0000.bin"
noncomputable def ep00010011100001 : Blocks := ep00010011100001_0
private theorem idp00010011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001110000.list =
    C ((2:ℤ)^63) * horner X vp00010011100001.list + horner X ep00010011100001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011100001 : Branch 1 (-623761639/1000000 : ℚ) vp0001001110000 := by
  apply branch_checked idp00010011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-623761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-624261639/500000 : ℚ) by norm_num]
  exact coverp00010011100001
theorem coverp0001001110000 : Covers (-623761639/1000000 : ℚ) vp0001001110000 := join_branches bp00010011100000 bp00010011100001
private noncomputable def vp000100111000_0 : Blocks := edgeBlocks% "full/vectors/000100111000-V-0000.bin"
noncomputable def vp000100111000 : Blocks := vp000100111000_0
private theorem bp0001001110000 : Branch 0 (-623761639/2000000 : ℚ) vp000100111000 := by
  apply branch_left_normalized (c:=vp0001001110000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-623761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-623761639/1000000 : ℚ) by norm_num]
  exact coverp0001001110000
private noncomputable def ep0001001110001_0 : Blocks := edgeBlocks% "full/vectors/0001001110001-E-0000.bin"
noncomputable def ep0001001110001 : Blocks := ep0001001110001_0
private theorem idp0001001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100111000.list =
    C ((2:ℤ)^107) * horner X vp0001001110001.list + horner X ep0001001110001.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001110001 : Branch 1 (-623761639/2000000 : ℚ) vp000100111000 := by
  apply branch_checked idp0001001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-623761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-624761639/1000000 : ℚ) by norm_num]
  exact coverp0001001110001
theorem coverp000100111000 : Covers (-623761639/2000000 : ℚ) vp000100111000 := join_branches bp0001001110000 bp0001001110001
private noncomputable def vp00010011100_0 : Blocks := edgeBlocks% "full/vectors/00010011100-V-0000.bin"
private noncomputable def vp00010011100_1 : Blocks := edgeBlocks% "full/vectors/00010011100-V-0001.bin"
noncomputable def vp00010011100 : Blocks := (Blocks.join vp00010011100_0 vp00010011100_1)
private theorem bp000100111000 : Branch 0 (-623761639/4000000 : ℚ) vp00010011100 := by
  apply branch_left_normalized (c:=vp000100111000) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-623761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-623761639/2000000 : ℚ) by norm_num]
  exact coverp000100111000
private noncomputable def ep000100111001_0 : Blocks := edgeBlocks% "full/vectors/000100111001-E-0000.bin"
private noncomputable def ep000100111001_1 : Blocks := edgeBlocks% "full/vectors/000100111001-E-0001.bin"
noncomputable def ep000100111001 : Blocks := (Blocks.join ep000100111001_0 ep000100111001_1)
private theorem idp000100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010011100.list =
    C ((2:ℤ)^191) * horner X vp000100111001.list + horner X ep000100111001.list := by
  exact edge_identity (B := (2:ℤ)^365) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100111001 : Branch 1 (-623761639/4000000 : ℚ) vp00010011100 := by
  apply branch_checked idp000100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-623761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-625761639/2000000 : ℚ) by norm_num]
  exact coverp000100111001
theorem coverp00010011100 : Covers (-623761639/4000000 : ℚ) vp00010011100 := join_branches bp000100111000 bp000100111001
private noncomputable def vp0001001110_0 : Blocks := edgeBlocks% "full/vectors/0001001110-V-0000.bin"
private noncomputable def vp0001001110_1 : Blocks := edgeBlocks% "full/vectors/0001001110-V-0001.bin"
private noncomputable def vp0001001110_2 : Blocks := edgeBlocks% "full/vectors/0001001110-V-0002.bin"
noncomputable def vp0001001110 : Blocks := (Blocks.join vp0001001110_0 (Blocks.join vp0001001110_1 vp0001001110_2))
private theorem bp00010011100 : Branch 0 (-623761639/8000000 : ℚ) vp0001001110 := by
  apply branch_left_normalized (c:=vp00010011100) (k:=0) (m:=179) (by decide +kernel)
  rw [show 2*(-623761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-623761639/4000000 : ℚ) by norm_num]
  exact coverp00010011100
private noncomputable def ep00010011101_0 : Blocks := edgeBlocks% "full/vectors/00010011101-E-0000.bin"
private noncomputable def ep00010011101_1 : Blocks := edgeBlocks% "full/vectors/00010011101-E-0001.bin"
private noncomputable def ep00010011101_2 : Blocks := edgeBlocks% "full/vectors/00010011101-E-0002.bin"
noncomputable def ep00010011101 : Blocks := (Blocks.join ep00010011101_0 (Blocks.join ep00010011101_1 ep00010011101_2))
private theorem idp00010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001110.list =
    C ((2:ℤ)^360) * horner X vp00010011101.list + horner X ep00010011101.list := by
  exact edge_identity (B := (2:ℤ)^606) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011101 : Branch 1 (-623761639/8000000 : ℚ) vp0001001110 := by
  apply branch_checked idp00010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-623761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-627761639/4000000 : ℚ) by norm_num]
  exact coverp00010011101
theorem coverp0001001110 : Covers (-623761639/8000000 : ℚ) vp0001001110 := join_branches bp00010011100 bp00010011101
private noncomputable def vp000100111_0 : Blocks := edgeBlocks% "full/vectors/000100111-V-0000.bin"
private noncomputable def vp000100111_1 : Blocks := edgeBlocks% "full/vectors/000100111-V-0001.bin"
private noncomputable def vp000100111_2 : Blocks := edgeBlocks% "full/vectors/000100111-V-0002.bin"
private noncomputable def vp000100111_3 : Blocks := edgeBlocks% "full/vectors/000100111-V-0003.bin"
private noncomputable def vp000100111_4 : Blocks := edgeBlocks% "full/vectors/000100111-V-0004.bin"
private noncomputable def vp000100111_5 : Blocks := edgeBlocks% "full/vectors/000100111-V-0005.bin"
noncomputable def vp000100111 : Blocks := (Blocks.join (Blocks.join vp000100111_0 (Blocks.join vp000100111_1 vp000100111_2)) (Blocks.join vp000100111_3 (Blocks.join vp000100111_4 vp000100111_5)))
private theorem bp0001001110 : Branch 0 (-623761639/16000000 : ℚ) vp000100111 := by
  apply branch_left_normalized (c:=vp0001001110) (k:=0) (m:=336) (by decide +kernel)
  rw [show 2*(-623761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-623761639/8000000 : ℚ) by norm_num]
  exact coverp0001001110
private noncomputable def ep0001001111_0 : Blocks := edgeBlocks% "full/vectors/0001001111-E-0000.bin"
private noncomputable def ep0001001111_1 : Blocks := edgeBlocks% "full/vectors/0001001111-E-0001.bin"
private noncomputable def ep0001001111_2 : Blocks := edgeBlocks% "full/vectors/0001001111-E-0002.bin"
private noncomputable def ep0001001111_3 : Blocks := edgeBlocks% "full/vectors/0001001111-E-0003.bin"
private noncomputable def ep0001001111_4 : Blocks := edgeBlocks% "full/vectors/0001001111-E-0004.bin"
private noncomputable def ep0001001111_5 : Blocks := edgeBlocks% "full/vectors/0001001111-E-0005.bin"
noncomputable def ep0001001111 : Blocks := (Blocks.join (Blocks.join ep0001001111_0 (Blocks.join ep0001001111_1 ep0001001111_2)) (Blocks.join ep0001001111_3 (Blocks.join ep0001001111_4 ep0001001111_5)))
private theorem idp0001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100111.list =
    C ((2:ℤ)^694) * horner X vp0001001111.list + horner X ep0001001111.list := by
  exact edge_identity (B := (2:ℤ)^1083) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001111 : Branch 1 (-623761639/16000000 : ℚ) vp000100111 := by
  apply branch_checked idp0001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-623761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-631761639/8000000 : ℚ) by norm_num]
  exact coverp0001001111
theorem coverp000100111 : Covers (-623761639/16000000 : ℚ) vp000100111 := join_branches bp0001001110 bp0001001111
private noncomputable def vp00010011011111_0 : Blocks := edgeBlocks% "full/vectors/00010011011111-V-0000.bin"
noncomputable def vp00010011011111 : Blocks := vp00010011011111_0
theorem coverp00010011011111 : Covers (-623261639/500000 : ℚ) vp00010011011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011011110_0 : Blocks := edgeBlocks% "full/vectors/00010011011110-V-0000.bin"
noncomputable def vp00010011011110 : Blocks := vp00010011011110_0
theorem coverp00010011011110 : Covers (-622761639/500000 : ℚ) vp00010011011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001101111_0 : Blocks := edgeBlocks% "full/vectors/0001001101111-V-0000.bin"
noncomputable def vp0001001101111 : Blocks := vp0001001101111_0
private theorem bp00010011011110 : Branch 0 (-622761639/1000000 : ℚ) vp0001001101111 := by
  apply branch_left_normalized (c:=vp00010011011110) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-622761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-622761639/500000 : ℚ) by norm_num]
  exact coverp00010011011110
private noncomputable def ep00010011011111_0 : Blocks := edgeBlocks% "full/vectors/00010011011111-E-0000.bin"
noncomputable def ep00010011011111 : Blocks := ep00010011011111_0
private theorem idp00010011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001101111.list =
    C ((2:ℤ)^63) * horner X vp00010011011111.list + horner X ep00010011011111.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011011111 : Branch 1 (-622761639/1000000 : ℚ) vp0001001101111 := by
  apply branch_checked idp00010011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-622761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-623261639/500000 : ℚ) by norm_num]
  exact coverp00010011011111
theorem coverp0001001101111 : Covers (-622761639/1000000 : ℚ) vp0001001101111 := join_branches bp00010011011110 bp00010011011111
private noncomputable def vp00010011011101_0 : Blocks := edgeBlocks% "full/vectors/00010011011101-V-0000.bin"
noncomputable def vp00010011011101 : Blocks := vp00010011011101_0
theorem coverp00010011011101 : Covers (-622261639/500000 : ℚ) vp00010011011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011011100_0 : Blocks := edgeBlocks% "full/vectors/00010011011100-V-0000.bin"
noncomputable def vp00010011011100 : Blocks := vp00010011011100_0
theorem coverp00010011011100 : Covers (-621761639/500000 : ℚ) vp00010011011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001101110_0 : Blocks := edgeBlocks% "full/vectors/0001001101110-V-0000.bin"
noncomputable def vp0001001101110 : Blocks := vp0001001101110_0
private theorem bp00010011011100 : Branch 0 (-621761639/1000000 : ℚ) vp0001001101110 := by
  apply branch_left_normalized (c:=vp00010011011100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-621761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-621761639/500000 : ℚ) by norm_num]
  exact coverp00010011011100
private noncomputable def ep00010011011101_0 : Blocks := edgeBlocks% "full/vectors/00010011011101-E-0000.bin"
noncomputable def ep00010011011101 : Blocks := ep00010011011101_0
private theorem idp00010011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001101110.list =
    C ((2:ℤ)^64) * horner X vp00010011011101.list + horner X ep00010011011101.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011011101 : Branch 1 (-621761639/1000000 : ℚ) vp0001001101110 := by
  apply branch_checked idp00010011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-621761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-622261639/500000 : ℚ) by norm_num]
  exact coverp00010011011101
theorem coverp0001001101110 : Covers (-621761639/1000000 : ℚ) vp0001001101110 := join_branches bp00010011011100 bp00010011011101
private noncomputable def vp000100110111_0 : Blocks := edgeBlocks% "full/vectors/000100110111-V-0000.bin"
noncomputable def vp000100110111 : Blocks := vp000100110111_0
private theorem bp0001001101110 : Branch 0 (-621761639/2000000 : ℚ) vp000100110111 := by
  apply branch_left_normalized (c:=vp0001001101110) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-621761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-621761639/1000000 : ℚ) by norm_num]
  exact coverp0001001101110
private noncomputable def ep0001001101111_0 : Blocks := edgeBlocks% "full/vectors/0001001101111-E-0000.bin"
noncomputable def ep0001001101111 : Blocks := ep0001001101111_0
private theorem idp0001001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100110111.list =
    C ((2:ℤ)^106) * horner X vp0001001101111.list + horner X ep0001001101111.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001101111 : Branch 1 (-621761639/2000000 : ℚ) vp000100110111 := by
  apply branch_checked idp0001001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-621761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-622761639/1000000 : ℚ) by norm_num]
  exact coverp0001001101111
theorem coverp000100110111 : Covers (-621761639/2000000 : ℚ) vp000100110111 := join_branches bp0001001101110 bp0001001101111
private noncomputable def vp00010011011011_0 : Blocks := edgeBlocks% "full/vectors/00010011011011-V-0000.bin"
noncomputable def vp00010011011011 : Blocks := vp00010011011011_0
theorem coverp00010011011011 : Covers (-621261639/500000 : ℚ) vp00010011011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011011010_0 : Blocks := edgeBlocks% "full/vectors/00010011011010-V-0000.bin"
noncomputable def vp00010011011010 : Blocks := vp00010011011010_0
theorem coverp00010011011010 : Covers (-620761639/500000 : ℚ) vp00010011011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001101101_0 : Blocks := edgeBlocks% "full/vectors/0001001101101-V-0000.bin"
noncomputable def vp0001001101101 : Blocks := vp0001001101101_0
private theorem bp00010011011010 : Branch 0 (-620761639/1000000 : ℚ) vp0001001101101 := by
  apply branch_left_normalized (c:=vp00010011011010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-620761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-620761639/500000 : ℚ) by norm_num]
  exact coverp00010011011010
private noncomputable def ep00010011011011_0 : Blocks := edgeBlocks% "full/vectors/00010011011011-E-0000.bin"
noncomputable def ep00010011011011 : Blocks := ep00010011011011_0
private theorem idp00010011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001101101.list =
    C ((2:ℤ)^62) * horner X vp00010011011011.list + horner X ep00010011011011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011011011 : Branch 1 (-620761639/1000000 : ℚ) vp0001001101101 := by
  apply branch_checked idp00010011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-620761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-621261639/500000 : ℚ) by norm_num]
  exact coverp00010011011011
theorem coverp0001001101101 : Covers (-620761639/1000000 : ℚ) vp0001001101101 := join_branches bp00010011011010 bp00010011011011
private noncomputable def vp00010011011001_0 : Blocks := edgeBlocks% "full/vectors/00010011011001-V-0000.bin"
noncomputable def vp00010011011001 : Blocks := vp00010011011001_0
theorem coverp00010011011001 : Covers (-620261639/500000 : ℚ) vp00010011011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011011000_0 : Blocks := edgeBlocks% "full/vectors/00010011011000-V-0000.bin"
noncomputable def vp00010011011000 : Blocks := vp00010011011000_0
theorem coverp00010011011000 : Covers (-619761639/500000 : ℚ) vp00010011011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001101100_0 : Blocks := edgeBlocks% "full/vectors/0001001101100-V-0000.bin"
noncomputable def vp0001001101100 : Blocks := vp0001001101100_0
private theorem bp00010011011000 : Branch 0 (-619761639/1000000 : ℚ) vp0001001101100 := by
  apply branch_left_normalized (c:=vp00010011011000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-619761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-619761639/500000 : ℚ) by norm_num]
  exact coverp00010011011000
private noncomputable def ep00010011011001_0 : Blocks := edgeBlocks% "full/vectors/00010011011001-E-0000.bin"
noncomputable def ep00010011011001 : Blocks := ep00010011011001_0
private theorem idp00010011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001101100.list =
    C ((2:ℤ)^63) * horner X vp00010011011001.list + horner X ep00010011011001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011011001 : Branch 1 (-619761639/1000000 : ℚ) vp0001001101100 := by
  apply branch_checked idp00010011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-619761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-620261639/500000 : ℚ) by norm_num]
  exact coverp00010011011001
theorem coverp0001001101100 : Covers (-619761639/1000000 : ℚ) vp0001001101100 := join_branches bp00010011011000 bp00010011011001
private noncomputable def vp000100110110_0 : Blocks := edgeBlocks% "full/vectors/000100110110-V-0000.bin"
noncomputable def vp000100110110 : Blocks := vp000100110110_0
private theorem bp0001001101100 : Branch 0 (-619761639/2000000 : ℚ) vp000100110110 := by
  apply branch_left_normalized (c:=vp0001001101100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-619761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-619761639/1000000 : ℚ) by norm_num]
  exact coverp0001001101100
private noncomputable def ep0001001101101_0 : Blocks := edgeBlocks% "full/vectors/0001001101101-E-0000.bin"
noncomputable def ep0001001101101 : Blocks := ep0001001101101_0
private theorem idp0001001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100110110.list =
    C ((2:ℤ)^107) * horner X vp0001001101101.list + horner X ep0001001101101.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001101101 : Branch 1 (-619761639/2000000 : ℚ) vp000100110110 := by
  apply branch_checked idp0001001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-619761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-620761639/1000000 : ℚ) by norm_num]
  exact coverp0001001101101
theorem coverp000100110110 : Covers (-619761639/2000000 : ℚ) vp000100110110 := join_branches bp0001001101100 bp0001001101101
private noncomputable def vp00010011011_0 : Blocks := edgeBlocks% "full/vectors/00010011011-V-0000.bin"
private noncomputable def vp00010011011_1 : Blocks := edgeBlocks% "full/vectors/00010011011-V-0001.bin"
noncomputable def vp00010011011 : Blocks := (Blocks.join vp00010011011_0 vp00010011011_1)
private theorem bp000100110110 : Branch 0 (-619761639/4000000 : ℚ) vp00010011011 := by
  apply branch_left_normalized (c:=vp000100110110) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-619761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-619761639/2000000 : ℚ) by norm_num]
  exact coverp000100110110
private noncomputable def ep000100110111_0 : Blocks := edgeBlocks% "full/vectors/000100110111-E-0000.bin"
private noncomputable def ep000100110111_1 : Blocks := edgeBlocks% "full/vectors/000100110111-E-0001.bin"
noncomputable def ep000100110111 : Blocks := (Blocks.join ep000100110111_0 ep000100110111_1)
private theorem idp000100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010011011.list =
    C ((2:ℤ)^192) * horner X vp000100110111.list + horner X ep000100110111.list := by
  exact edge_identity (B := (2:ℤ)^366) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100110111 : Branch 1 (-619761639/4000000 : ℚ) vp00010011011 := by
  apply branch_checked idp000100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-619761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-621761639/2000000 : ℚ) by norm_num]
  exact coverp000100110111
theorem coverp00010011011 : Covers (-619761639/4000000 : ℚ) vp00010011011 := join_branches bp000100110110 bp000100110111
private noncomputable def vp00010011010111_0 : Blocks := edgeBlocks% "full/vectors/00010011010111-V-0000.bin"
noncomputable def vp00010011010111 : Blocks := vp00010011010111_0
theorem coverp00010011010111 : Covers (-619261639/500000 : ℚ) vp00010011010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011010110_0 : Blocks := edgeBlocks% "full/vectors/00010011010110-V-0000.bin"
noncomputable def vp00010011010110 : Blocks := vp00010011010110_0
theorem coverp00010011010110 : Covers (-618761639/500000 : ℚ) vp00010011010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001101011_0 : Blocks := edgeBlocks% "full/vectors/0001001101011-V-0000.bin"
noncomputable def vp0001001101011 : Blocks := vp0001001101011_0
private theorem bp00010011010110 : Branch 0 (-618761639/1000000 : ℚ) vp0001001101011 := by
  apply branch_left_normalized (c:=vp00010011010110) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-618761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-618761639/500000 : ℚ) by norm_num]
  exact coverp00010011010110
private noncomputable def ep00010011010111_0 : Blocks := edgeBlocks% "full/vectors/00010011010111-E-0000.bin"
noncomputable def ep00010011010111 : Blocks := ep00010011010111_0
private theorem idp00010011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001101011.list =
    C ((2:ℤ)^63) * horner X vp00010011010111.list + horner X ep00010011010111.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011010111 : Branch 1 (-618761639/1000000 : ℚ) vp0001001101011 := by
  apply branch_checked idp00010011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-618761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-619261639/500000 : ℚ) by norm_num]
  exact coverp00010011010111
theorem coverp0001001101011 : Covers (-618761639/1000000 : ℚ) vp0001001101011 := join_branches bp00010011010110 bp00010011010111
private noncomputable def vp00010011010101_0 : Blocks := edgeBlocks% "full/vectors/00010011010101-V-0000.bin"
noncomputable def vp00010011010101 : Blocks := vp00010011010101_0
theorem coverp00010011010101 : Covers (-618261639/500000 : ℚ) vp00010011010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011010100_0 : Blocks := edgeBlocks% "full/vectors/00010011010100-V-0000.bin"
noncomputable def vp00010011010100 : Blocks := vp00010011010100_0
theorem coverp00010011010100 : Covers (-617761639/500000 : ℚ) vp00010011010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001101010_0 : Blocks := edgeBlocks% "full/vectors/0001001101010-V-0000.bin"
noncomputable def vp0001001101010 : Blocks := vp0001001101010_0
private theorem bp00010011010100 : Branch 0 (-617761639/1000000 : ℚ) vp0001001101010 := by
  apply branch_left_normalized (c:=vp00010011010100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-617761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-617761639/500000 : ℚ) by norm_num]
  exact coverp00010011010100
private noncomputable def ep00010011010101_0 : Blocks := edgeBlocks% "full/vectors/00010011010101-E-0000.bin"
noncomputable def ep00010011010101 : Blocks := ep00010011010101_0
private theorem idp00010011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001101010.list =
    C ((2:ℤ)^63) * horner X vp00010011010101.list + horner X ep00010011010101.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011010101 : Branch 1 (-617761639/1000000 : ℚ) vp0001001101010 := by
  apply branch_checked idp00010011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-617761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-618261639/500000 : ℚ) by norm_num]
  exact coverp00010011010101
theorem coverp0001001101010 : Covers (-617761639/1000000 : ℚ) vp0001001101010 := join_branches bp00010011010100 bp00010011010101
private noncomputable def vp000100110101_0 : Blocks := edgeBlocks% "full/vectors/000100110101-V-0000.bin"
noncomputable def vp000100110101 : Blocks := vp000100110101_0
private theorem bp0001001101010 : Branch 0 (-617761639/2000000 : ℚ) vp000100110101 := by
  apply branch_left_normalized (c:=vp0001001101010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-617761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-617761639/1000000 : ℚ) by norm_num]
  exact coverp0001001101010
private noncomputable def ep0001001101011_0 : Blocks := edgeBlocks% "full/vectors/0001001101011-E-0000.bin"
noncomputable def ep0001001101011 : Blocks := ep0001001101011_0
private theorem idp0001001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100110101.list =
    C ((2:ℤ)^106) * horner X vp0001001101011.list + horner X ep0001001101011.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001101011 : Branch 1 (-617761639/2000000 : ℚ) vp000100110101 := by
  apply branch_checked idp0001001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-617761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-618761639/1000000 : ℚ) by norm_num]
  exact coverp0001001101011
theorem coverp000100110101 : Covers (-617761639/2000000 : ℚ) vp000100110101 := join_branches bp0001001101010 bp0001001101011
private noncomputable def vp00010011010011_0 : Blocks := edgeBlocks% "full/vectors/00010011010011-V-0000.bin"
noncomputable def vp00010011010011 : Blocks := vp00010011010011_0
theorem coverp00010011010011 : Covers (-617261639/500000 : ℚ) vp00010011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011010010_0 : Blocks := edgeBlocks% "full/vectors/00010011010010-V-0000.bin"
noncomputable def vp00010011010010 : Blocks := vp00010011010010_0
theorem coverp00010011010010 : Covers (-616761639/500000 : ℚ) vp00010011010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001101001_0 : Blocks := edgeBlocks% "full/vectors/0001001101001-V-0000.bin"
noncomputable def vp0001001101001 : Blocks := vp0001001101001_0
private theorem bp00010011010010 : Branch 0 (-616761639/1000000 : ℚ) vp0001001101001 := by
  apply branch_left_normalized (c:=vp00010011010010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-616761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-616761639/500000 : ℚ) by norm_num]
  exact coverp00010011010010
private noncomputable def ep00010011010011_0 : Blocks := edgeBlocks% "full/vectors/00010011010011-E-0000.bin"
noncomputable def ep00010011010011 : Blocks := ep00010011010011_0
private theorem idp00010011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001101001.list =
    C ((2:ℤ)^63) * horner X vp00010011010011.list + horner X ep00010011010011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011010011 : Branch 1 (-616761639/1000000 : ℚ) vp0001001101001 := by
  apply branch_checked idp00010011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-616761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-617261639/500000 : ℚ) by norm_num]
  exact coverp00010011010011
theorem coverp0001001101001 : Covers (-616761639/1000000 : ℚ) vp0001001101001 := join_branches bp00010011010010 bp00010011010011
private noncomputable def vp00010011010001_0 : Blocks := edgeBlocks% "full/vectors/00010011010001-V-0000.bin"
noncomputable def vp00010011010001 : Blocks := vp00010011010001_0
theorem coverp00010011010001 : Covers (-616261639/500000 : ℚ) vp00010011010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011010000_0 : Blocks := edgeBlocks% "full/vectors/00010011010000-V-0000.bin"
noncomputable def vp00010011010000 : Blocks := vp00010011010000_0
theorem coverp00010011010000 : Covers (-615761639/500000 : ℚ) vp00010011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001101000_0 : Blocks := edgeBlocks% "full/vectors/0001001101000-V-0000.bin"
noncomputable def vp0001001101000 : Blocks := vp0001001101000_0
private theorem bp00010011010000 : Branch 0 (-615761639/1000000 : ℚ) vp0001001101000 := by
  apply branch_left_normalized (c:=vp00010011010000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-615761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-615761639/500000 : ℚ) by norm_num]
  exact coverp00010011010000
private noncomputable def ep00010011010001_0 : Blocks := edgeBlocks% "full/vectors/00010011010001-E-0000.bin"
noncomputable def ep00010011010001 : Blocks := ep00010011010001_0
private theorem idp00010011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001101000.list =
    C ((2:ℤ)^63) * horner X vp00010011010001.list + horner X ep00010011010001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011010001 : Branch 1 (-615761639/1000000 : ℚ) vp0001001101000 := by
  apply branch_checked idp00010011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-615761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-616261639/500000 : ℚ) by norm_num]
  exact coverp00010011010001
theorem coverp0001001101000 : Covers (-615761639/1000000 : ℚ) vp0001001101000 := join_branches bp00010011010000 bp00010011010001
private noncomputable def vp000100110100_0 : Blocks := edgeBlocks% "full/vectors/000100110100-V-0000.bin"
noncomputable def vp000100110100 : Blocks := vp000100110100_0
private theorem bp0001001101000 : Branch 0 (-615761639/2000000 : ℚ) vp000100110100 := by
  apply branch_left_normalized (c:=vp0001001101000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-615761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-615761639/1000000 : ℚ) by norm_num]
  exact coverp0001001101000
private noncomputable def ep0001001101001_0 : Blocks := edgeBlocks% "full/vectors/0001001101001-E-0000.bin"
noncomputable def ep0001001101001 : Blocks := ep0001001101001_0
private theorem idp0001001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100110100.list =
    C ((2:ℤ)^108) * horner X vp0001001101001.list + horner X ep0001001101001.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001101001 : Branch 1 (-615761639/2000000 : ℚ) vp000100110100 := by
  apply branch_checked idp0001001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-615761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-616761639/1000000 : ℚ) by norm_num]
  exact coverp0001001101001
theorem coverp000100110100 : Covers (-615761639/2000000 : ℚ) vp000100110100 := join_branches bp0001001101000 bp0001001101001
private noncomputable def vp00010011010_0 : Blocks := edgeBlocks% "full/vectors/00010011010-V-0000.bin"
private noncomputable def vp00010011010_1 : Blocks := edgeBlocks% "full/vectors/00010011010-V-0001.bin"
noncomputable def vp00010011010 : Blocks := (Blocks.join vp00010011010_0 vp00010011010_1)
private theorem bp000100110100 : Branch 0 (-615761639/4000000 : ℚ) vp00010011010 := by
  apply branch_left_normalized (c:=vp000100110100) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-615761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-615761639/2000000 : ℚ) by norm_num]
  exact coverp000100110100
private noncomputable def ep000100110101_0 : Blocks := edgeBlocks% "full/vectors/000100110101-E-0000.bin"
private noncomputable def ep000100110101_1 : Blocks := edgeBlocks% "full/vectors/000100110101-E-0001.bin"
noncomputable def ep000100110101 : Blocks := (Blocks.join ep000100110101_0 ep000100110101_1)
private theorem idp000100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010011010.list =
    C ((2:ℤ)^193) * horner X vp000100110101.list + horner X ep000100110101.list := by
  exact edge_identity (B := (2:ℤ)^367) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100110101 : Branch 1 (-615761639/4000000 : ℚ) vp00010011010 := by
  apply branch_checked idp000100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-615761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-617761639/2000000 : ℚ) by norm_num]
  exact coverp000100110101
theorem coverp00010011010 : Covers (-615761639/4000000 : ℚ) vp00010011010 := join_branches bp000100110100 bp000100110101
private noncomputable def vp0001001101_0 : Blocks := edgeBlocks% "full/vectors/0001001101-V-0000.bin"
private noncomputable def vp0001001101_1 : Blocks := edgeBlocks% "full/vectors/0001001101-V-0001.bin"
private noncomputable def vp0001001101_2 : Blocks := edgeBlocks% "full/vectors/0001001101-V-0002.bin"
noncomputable def vp0001001101 : Blocks := (Blocks.join vp0001001101_0 (Blocks.join vp0001001101_1 vp0001001101_2))
private theorem bp00010011010 : Branch 0 (-615761639/8000000 : ℚ) vp0001001101 := by
  apply branch_left_normalized (c:=vp00010011010) (k:=0) (m:=180) (by decide +kernel)
  rw [show 2*(-615761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-615761639/4000000 : ℚ) by norm_num]
  exact coverp00010011010
private noncomputable def ep00010011011_0 : Blocks := edgeBlocks% "full/vectors/00010011011-E-0000.bin"
private noncomputable def ep00010011011_1 : Blocks := edgeBlocks% "full/vectors/00010011011-E-0001.bin"
private noncomputable def ep00010011011_2 : Blocks := edgeBlocks% "full/vectors/00010011011-E-0002.bin"
noncomputable def ep00010011011 : Blocks := (Blocks.join ep00010011011_0 (Blocks.join ep00010011011_1 ep00010011011_2))
private theorem idp00010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001101.list =
    C ((2:ℤ)^362) * horner X vp00010011011.list + horner X ep00010011011.list := by
  exact edge_identity (B := (2:ℤ)^609) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011011 : Branch 1 (-615761639/8000000 : ℚ) vp0001001101 := by
  apply branch_checked idp00010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-615761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-619761639/4000000 : ℚ) by norm_num]
  exact coverp00010011011
theorem coverp0001001101 : Covers (-615761639/8000000 : ℚ) vp0001001101 := join_branches bp00010011010 bp00010011011
private noncomputable def vp00010011001111_0 : Blocks := edgeBlocks% "full/vectors/00010011001111-V-0000.bin"
noncomputable def vp00010011001111 : Blocks := vp00010011001111_0
theorem coverp00010011001111 : Covers (-615261639/500000 : ℚ) vp00010011001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011001110_0 : Blocks := edgeBlocks% "full/vectors/00010011001110-V-0000.bin"
noncomputable def vp00010011001110 : Blocks := vp00010011001110_0
theorem coverp00010011001110 : Covers (-614761639/500000 : ℚ) vp00010011001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001100111_0 : Blocks := edgeBlocks% "full/vectors/0001001100111-V-0000.bin"
noncomputable def vp0001001100111 : Blocks := vp0001001100111_0
private theorem bp00010011001110 : Branch 0 (-614761639/1000000 : ℚ) vp0001001100111 := by
  apply branch_left_normalized (c:=vp00010011001110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-614761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-614761639/500000 : ℚ) by norm_num]
  exact coverp00010011001110
private noncomputable def ep00010011001111_0 : Blocks := edgeBlocks% "full/vectors/00010011001111-E-0000.bin"
noncomputable def ep00010011001111 : Blocks := ep00010011001111_0
private theorem idp00010011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001100111.list =
    C ((2:ℤ)^64) * horner X vp00010011001111.list + horner X ep00010011001111.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011001111 : Branch 1 (-614761639/1000000 : ℚ) vp0001001100111 := by
  apply branch_checked idp00010011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-614761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-615261639/500000 : ℚ) by norm_num]
  exact coverp00010011001111
theorem coverp0001001100111 : Covers (-614761639/1000000 : ℚ) vp0001001100111 := join_branches bp00010011001110 bp00010011001111
private noncomputable def vp00010011001101_0 : Blocks := edgeBlocks% "full/vectors/00010011001101-V-0000.bin"
noncomputable def vp00010011001101 : Blocks := vp00010011001101_0
theorem coverp00010011001101 : Covers (-614261639/500000 : ℚ) vp00010011001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011001100_0 : Blocks := edgeBlocks% "full/vectors/00010011001100-V-0000.bin"
noncomputable def vp00010011001100 : Blocks := vp00010011001100_0
theorem coverp00010011001100 : Covers (-613761639/500000 : ℚ) vp00010011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001100110_0 : Blocks := edgeBlocks% "full/vectors/0001001100110-V-0000.bin"
noncomputable def vp0001001100110 : Blocks := vp0001001100110_0
private theorem bp00010011001100 : Branch 0 (-613761639/1000000 : ℚ) vp0001001100110 := by
  apply branch_left_normalized (c:=vp00010011001100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-613761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-613761639/500000 : ℚ) by norm_num]
  exact coverp00010011001100
private noncomputable def ep00010011001101_0 : Blocks := edgeBlocks% "full/vectors/00010011001101-E-0000.bin"
noncomputable def ep00010011001101 : Blocks := ep00010011001101_0
private theorem idp00010011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001100110.list =
    C ((2:ℤ)^63) * horner X vp00010011001101.list + horner X ep00010011001101.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011001101 : Branch 1 (-613761639/1000000 : ℚ) vp0001001100110 := by
  apply branch_checked idp00010011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-613761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-614261639/500000 : ℚ) by norm_num]
  exact coverp00010011001101
theorem coverp0001001100110 : Covers (-613761639/1000000 : ℚ) vp0001001100110 := join_branches bp00010011001100 bp00010011001101
private noncomputable def vp000100110011_0 : Blocks := edgeBlocks% "full/vectors/000100110011-V-0000.bin"
noncomputable def vp000100110011 : Blocks := vp000100110011_0
private theorem bp0001001100110 : Branch 0 (-613761639/2000000 : ℚ) vp000100110011 := by
  apply branch_left_normalized (c:=vp0001001100110) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-613761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-613761639/1000000 : ℚ) by norm_num]
  exact coverp0001001100110
private noncomputable def ep0001001100111_0 : Blocks := edgeBlocks% "full/vectors/0001001100111-E-0000.bin"
noncomputable def ep0001001100111 : Blocks := ep0001001100111_0
private theorem idp0001001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100110011.list =
    C ((2:ℤ)^108) * horner X vp0001001100111.list + horner X ep0001001100111.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001100111 : Branch 1 (-613761639/2000000 : ℚ) vp000100110011 := by
  apply branch_checked idp0001001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-613761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-614761639/1000000 : ℚ) by norm_num]
  exact coverp0001001100111
theorem coverp000100110011 : Covers (-613761639/2000000 : ℚ) vp000100110011 := join_branches bp0001001100110 bp0001001100111
private noncomputable def vp00010011001011_0 : Blocks := edgeBlocks% "full/vectors/00010011001011-V-0000.bin"
noncomputable def vp00010011001011 : Blocks := vp00010011001011_0
theorem coverp00010011001011 : Covers (-613261639/500000 : ℚ) vp00010011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011001010_0 : Blocks := edgeBlocks% "full/vectors/00010011001010-V-0000.bin"
noncomputable def vp00010011001010 : Blocks := vp00010011001010_0
theorem coverp00010011001010 : Covers (-612761639/500000 : ℚ) vp00010011001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001100101_0 : Blocks := edgeBlocks% "full/vectors/0001001100101-V-0000.bin"
noncomputable def vp0001001100101 : Blocks := vp0001001100101_0
private theorem bp00010011001010 : Branch 0 (-612761639/1000000 : ℚ) vp0001001100101 := by
  apply branch_left_normalized (c:=vp00010011001010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-612761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-612761639/500000 : ℚ) by norm_num]
  exact coverp00010011001010
private noncomputable def ep00010011001011_0 : Blocks := edgeBlocks% "full/vectors/00010011001011-E-0000.bin"
noncomputable def ep00010011001011 : Blocks := ep00010011001011_0
private theorem idp00010011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001100101.list =
    C ((2:ℤ)^63) * horner X vp00010011001011.list + horner X ep00010011001011.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011001011 : Branch 1 (-612761639/1000000 : ℚ) vp0001001100101 := by
  apply branch_checked idp00010011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-612761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-613261639/500000 : ℚ) by norm_num]
  exact coverp00010011001011
theorem coverp0001001100101 : Covers (-612761639/1000000 : ℚ) vp0001001100101 := join_branches bp00010011001010 bp00010011001011
private noncomputable def vp00010011001001_0 : Blocks := edgeBlocks% "full/vectors/00010011001001-V-0000.bin"
noncomputable def vp00010011001001 : Blocks := vp00010011001001_0
theorem coverp00010011001001 : Covers (-612261639/500000 : ℚ) vp00010011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011001000_0 : Blocks := edgeBlocks% "full/vectors/00010011001000-V-0000.bin"
noncomputable def vp00010011001000 : Blocks := vp00010011001000_0
theorem coverp00010011001000 : Covers (-611761639/500000 : ℚ) vp00010011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001100100_0 : Blocks := edgeBlocks% "full/vectors/0001001100100-V-0000.bin"
noncomputable def vp0001001100100 : Blocks := vp0001001100100_0
private theorem bp00010011001000 : Branch 0 (-611761639/1000000 : ℚ) vp0001001100100 := by
  apply branch_left_normalized (c:=vp00010011001000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-611761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-611761639/500000 : ℚ) by norm_num]
  exact coverp00010011001000
private noncomputable def ep00010011001001_0 : Blocks := edgeBlocks% "full/vectors/00010011001001-E-0000.bin"
noncomputable def ep00010011001001 : Blocks := ep00010011001001_0
private theorem idp00010011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001100100.list =
    C ((2:ℤ)^63) * horner X vp00010011001001.list + horner X ep00010011001001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011001001 : Branch 1 (-611761639/1000000 : ℚ) vp0001001100100 := by
  apply branch_checked idp00010011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-611761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-612261639/500000 : ℚ) by norm_num]
  exact coverp00010011001001
theorem coverp0001001100100 : Covers (-611761639/1000000 : ℚ) vp0001001100100 := join_branches bp00010011001000 bp00010011001001
private noncomputable def vp000100110010_0 : Blocks := edgeBlocks% "full/vectors/000100110010-V-0000.bin"
noncomputable def vp000100110010 : Blocks := vp000100110010_0
private theorem bp0001001100100 : Branch 0 (-611761639/2000000 : ℚ) vp000100110010 := by
  apply branch_left_normalized (c:=vp0001001100100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-611761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-611761639/1000000 : ℚ) by norm_num]
  exact coverp0001001100100
private noncomputable def ep0001001100101_0 : Blocks := edgeBlocks% "full/vectors/0001001100101-E-0000.bin"
noncomputable def ep0001001100101 : Blocks := ep0001001100101_0
private theorem idp0001001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100110010.list =
    C ((2:ℤ)^107) * horner X vp0001001100101.list + horner X ep0001001100101.list := by
  exact edge_identity (B := (2:ℤ)^245) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001100101 : Branch 1 (-611761639/2000000 : ℚ) vp000100110010 := by
  apply branch_checked idp0001001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-611761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-612761639/1000000 : ℚ) by norm_num]
  exact coverp0001001100101
theorem coverp000100110010 : Covers (-611761639/2000000 : ℚ) vp000100110010 := join_branches bp0001001100100 bp0001001100101
private noncomputable def vp00010011001_0 : Blocks := edgeBlocks% "full/vectors/00010011001-V-0000.bin"
private noncomputable def vp00010011001_1 : Blocks := edgeBlocks% "full/vectors/00010011001-V-0001.bin"
noncomputable def vp00010011001 : Blocks := (Blocks.join vp00010011001_0 vp00010011001_1)
private theorem bp000100110010 : Branch 0 (-611761639/4000000 : ℚ) vp00010011001 := by
  apply branch_left_normalized (c:=vp000100110010) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-611761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-611761639/2000000 : ℚ) by norm_num]
  exact coverp000100110010
private noncomputable def ep000100110011_0 : Blocks := edgeBlocks% "full/vectors/000100110011-E-0000.bin"
private noncomputable def ep000100110011_1 : Blocks := edgeBlocks% "full/vectors/000100110011-E-0001.bin"
noncomputable def ep000100110011 : Blocks := (Blocks.join ep000100110011_0 ep000100110011_1)
private theorem idp000100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010011001.list =
    C ((2:ℤ)^192) * horner X vp000100110011.list + horner X ep000100110011.list := by
  exact edge_identity (B := (2:ℤ)^367) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100110011 : Branch 1 (-611761639/4000000 : ℚ) vp00010011001 := by
  apply branch_checked idp000100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-611761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-613761639/2000000 : ℚ) by norm_num]
  exact coverp000100110011
theorem coverp00010011001 : Covers (-611761639/4000000 : ℚ) vp00010011001 := join_branches bp000100110010 bp000100110011
private noncomputable def vp00010011000111_0 : Blocks := edgeBlocks% "full/vectors/00010011000111-V-0000.bin"
noncomputable def vp00010011000111 : Blocks := vp00010011000111_0
theorem coverp00010011000111 : Covers (-611261639/500000 : ℚ) vp00010011000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011000110_0 : Blocks := edgeBlocks% "full/vectors/00010011000110-V-0000.bin"
noncomputable def vp00010011000110 : Blocks := vp00010011000110_0
theorem coverp00010011000110 : Covers (-610761639/500000 : ℚ) vp00010011000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001100011_0 : Blocks := edgeBlocks% "full/vectors/0001001100011-V-0000.bin"
noncomputable def vp0001001100011 : Blocks := vp0001001100011_0
private theorem bp00010011000110 : Branch 0 (-610761639/1000000 : ℚ) vp0001001100011 := by
  apply branch_left_normalized (c:=vp00010011000110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-610761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-610761639/500000 : ℚ) by norm_num]
  exact coverp00010011000110
private noncomputable def ep00010011000111_0 : Blocks := edgeBlocks% "full/vectors/00010011000111-E-0000.bin"
noncomputable def ep00010011000111 : Blocks := ep00010011000111_0
private theorem idp00010011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001100011.list =
    C ((2:ℤ)^63) * horner X vp00010011000111.list + horner X ep00010011000111.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011000111 : Branch 1 (-610761639/1000000 : ℚ) vp0001001100011 := by
  apply branch_checked idp00010011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-610761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-611261639/500000 : ℚ) by norm_num]
  exact coverp00010011000111
theorem coverp0001001100011 : Covers (-610761639/1000000 : ℚ) vp0001001100011 := join_branches bp00010011000110 bp00010011000111
private noncomputable def vp00010011000101_0 : Blocks := edgeBlocks% "full/vectors/00010011000101-V-0000.bin"
noncomputable def vp00010011000101 : Blocks := vp00010011000101_0
theorem coverp00010011000101 : Covers (-610261639/500000 : ℚ) vp00010011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011000100_0 : Blocks := edgeBlocks% "full/vectors/00010011000100-V-0000.bin"
noncomputable def vp00010011000100 : Blocks := vp00010011000100_0
theorem coverp00010011000100 : Covers (-609761639/500000 : ℚ) vp00010011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001100010_0 : Blocks := edgeBlocks% "full/vectors/0001001100010-V-0000.bin"
noncomputable def vp0001001100010 : Blocks := vp0001001100010_0
private theorem bp00010011000100 : Branch 0 (-609761639/1000000 : ℚ) vp0001001100010 := by
  apply branch_left_normalized (c:=vp00010011000100) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-609761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-609761639/500000 : ℚ) by norm_num]
  exact coverp00010011000100
private noncomputable def ep00010011000101_0 : Blocks := edgeBlocks% "full/vectors/00010011000101-E-0000.bin"
noncomputable def ep00010011000101 : Blocks := ep00010011000101_0
private theorem idp00010011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001100010.list =
    C ((2:ℤ)^63) * horner X vp00010011000101.list + horner X ep00010011000101.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011000101 : Branch 1 (-609761639/1000000 : ℚ) vp0001001100010 := by
  apply branch_checked idp00010011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-609761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-610261639/500000 : ℚ) by norm_num]
  exact coverp00010011000101
theorem coverp0001001100010 : Covers (-609761639/1000000 : ℚ) vp0001001100010 := join_branches bp00010011000100 bp00010011000101
private noncomputable def vp000100110001_0 : Blocks := edgeBlocks% "full/vectors/000100110001-V-0000.bin"
noncomputable def vp000100110001 : Blocks := vp000100110001_0
private theorem bp0001001100010 : Branch 0 (-609761639/2000000 : ℚ) vp000100110001 := by
  apply branch_left_normalized (c:=vp0001001100010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-609761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-609761639/1000000 : ℚ) by norm_num]
  exact coverp0001001100010
private noncomputable def ep0001001100011_0 : Blocks := edgeBlocks% "full/vectors/0001001100011-E-0000.bin"
noncomputable def ep0001001100011 : Blocks := ep0001001100011_0
private theorem idp0001001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100110001.list =
    C ((2:ℤ)^107) * horner X vp0001001100011.list + horner X ep0001001100011.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001100011 : Branch 1 (-609761639/2000000 : ℚ) vp000100110001 := by
  apply branch_checked idp0001001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-609761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-610761639/1000000 : ℚ) by norm_num]
  exact coverp0001001100011
theorem coverp000100110001 : Covers (-609761639/2000000 : ℚ) vp000100110001 := join_branches bp0001001100010 bp0001001100011
private noncomputable def vp00010011000011_0 : Blocks := edgeBlocks% "full/vectors/00010011000011-V-0000.bin"
noncomputable def vp00010011000011 : Blocks := vp00010011000011_0
theorem coverp00010011000011 : Covers (-609261639/500000 : ℚ) vp00010011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011000010_0 : Blocks := edgeBlocks% "full/vectors/00010011000010-V-0000.bin"
noncomputable def vp00010011000010 : Blocks := vp00010011000010_0
theorem coverp00010011000010 : Covers (-608761639/500000 : ℚ) vp00010011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001100001_0 : Blocks := edgeBlocks% "full/vectors/0001001100001-V-0000.bin"
noncomputable def vp0001001100001 : Blocks := vp0001001100001_0
private theorem bp00010011000010 : Branch 0 (-608761639/1000000 : ℚ) vp0001001100001 := by
  apply branch_left_normalized (c:=vp00010011000010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-608761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-608761639/500000 : ℚ) by norm_num]
  exact coverp00010011000010
private noncomputable def ep00010011000011_0 : Blocks := edgeBlocks% "full/vectors/00010011000011-E-0000.bin"
noncomputable def ep00010011000011 : Blocks := ep00010011000011_0
private theorem idp00010011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001100001.list =
    C ((2:ℤ)^64) * horner X vp00010011000011.list + horner X ep00010011000011.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011000011 : Branch 1 (-608761639/1000000 : ℚ) vp0001001100001 := by
  apply branch_checked idp00010011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-608761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-609261639/500000 : ℚ) by norm_num]
  exact coverp00010011000011
theorem coverp0001001100001 : Covers (-608761639/1000000 : ℚ) vp0001001100001 := join_branches bp00010011000010 bp00010011000011
private noncomputable def vp00010011000001_0 : Blocks := edgeBlocks% "full/vectors/00010011000001-V-0000.bin"
noncomputable def vp00010011000001 : Blocks := vp00010011000001_0
theorem coverp00010011000001 : Covers (-608261639/500000 : ℚ) vp00010011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010011000000_0 : Blocks := edgeBlocks% "full/vectors/00010011000000-V-0000.bin"
noncomputable def vp00010011000000 : Blocks := vp00010011000000_0
theorem coverp00010011000000 : Covers (-607761639/500000 : ℚ) vp00010011000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001100000_0 : Blocks := edgeBlocks% "full/vectors/0001001100000-V-0000.bin"
noncomputable def vp0001001100000 : Blocks := vp0001001100000_0
private theorem bp00010011000000 : Branch 0 (-607761639/1000000 : ℚ) vp0001001100000 := by
  apply branch_left_normalized (c:=vp00010011000000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-607761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-607761639/500000 : ℚ) by norm_num]
  exact coverp00010011000000
private noncomputable def ep00010011000001_0 : Blocks := edgeBlocks% "full/vectors/00010011000001-E-0000.bin"
noncomputable def ep00010011000001 : Blocks := ep00010011000001_0
private theorem idp00010011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001100000.list =
    C ((2:ℤ)^63) * horner X vp00010011000001.list + horner X ep00010011000001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011000001 : Branch 1 (-607761639/1000000 : ℚ) vp0001001100000 := by
  apply branch_checked idp00010011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-607761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-608261639/500000 : ℚ) by norm_num]
  exact coverp00010011000001
theorem coverp0001001100000 : Covers (-607761639/1000000 : ℚ) vp0001001100000 := join_branches bp00010011000000 bp00010011000001
private noncomputable def vp000100110000_0 : Blocks := edgeBlocks% "full/vectors/000100110000-V-0000.bin"
noncomputable def vp000100110000 : Blocks := vp000100110000_0
private theorem bp0001001100000 : Branch 0 (-607761639/2000000 : ℚ) vp000100110000 := by
  apply branch_left_normalized (c:=vp0001001100000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-607761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-607761639/1000000 : ℚ) by norm_num]
  exact coverp0001001100000
private noncomputable def ep0001001100001_0 : Blocks := edgeBlocks% "full/vectors/0001001100001-E-0000.bin"
noncomputable def ep0001001100001 : Blocks := ep0001001100001_0
private theorem idp0001001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100110000.list =
    C ((2:ℤ)^108) * horner X vp0001001100001.list + horner X ep0001001100001.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001100001 : Branch 1 (-607761639/2000000 : ℚ) vp000100110000 := by
  apply branch_checked idp0001001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-607761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-608761639/1000000 : ℚ) by norm_num]
  exact coverp0001001100001
theorem coverp000100110000 : Covers (-607761639/2000000 : ℚ) vp000100110000 := join_branches bp0001001100000 bp0001001100001
private noncomputable def vp00010011000_0 : Blocks := edgeBlocks% "full/vectors/00010011000-V-0000.bin"
private noncomputable def vp00010011000_1 : Blocks := edgeBlocks% "full/vectors/00010011000-V-0001.bin"
noncomputable def vp00010011000 : Blocks := (Blocks.join vp00010011000_0 vp00010011000_1)
private theorem bp000100110000 : Branch 0 (-607761639/4000000 : ℚ) vp00010011000 := by
  apply branch_left_normalized (c:=vp000100110000) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-607761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-607761639/2000000 : ℚ) by norm_num]
  exact coverp000100110000
private noncomputable def ep000100110001_0 : Blocks := edgeBlocks% "full/vectors/000100110001-E-0000.bin"
private noncomputable def ep000100110001_1 : Blocks := edgeBlocks% "full/vectors/000100110001-E-0001.bin"
noncomputable def ep000100110001 : Blocks := (Blocks.join ep000100110001_0 ep000100110001_1)
private theorem idp000100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010011000.list =
    C ((2:ℤ)^195) * horner X vp000100110001.list + horner X ep000100110001.list := by
  exact edge_identity (B := (2:ℤ)^369) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100110001 : Branch 1 (-607761639/4000000 : ℚ) vp00010011000 := by
  apply branch_checked idp000100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-607761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-609761639/2000000 : ℚ) by norm_num]
  exact coverp000100110001
theorem coverp00010011000 : Covers (-607761639/4000000 : ℚ) vp00010011000 := join_branches bp000100110000 bp000100110001
private noncomputable def vp0001001100_0 : Blocks := edgeBlocks% "full/vectors/0001001100-V-0000.bin"
private noncomputable def vp0001001100_1 : Blocks := edgeBlocks% "full/vectors/0001001100-V-0001.bin"
private noncomputable def vp0001001100_2 : Blocks := edgeBlocks% "full/vectors/0001001100-V-0002.bin"
noncomputable def vp0001001100 : Blocks := (Blocks.join vp0001001100_0 (Blocks.join vp0001001100_1 vp0001001100_2))
private theorem bp00010011000 : Branch 0 (-607761639/8000000 : ℚ) vp0001001100 := by
  apply branch_left_normalized (c:=vp00010011000) (k:=0) (m:=182) (by decide +kernel)
  rw [show 2*(-607761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-607761639/4000000 : ℚ) by norm_num]
  exact coverp00010011000
private noncomputable def ep00010011001_0 : Blocks := edgeBlocks% "full/vectors/00010011001-E-0000.bin"
private noncomputable def ep00010011001_1 : Blocks := edgeBlocks% "full/vectors/00010011001-E-0001.bin"
private noncomputable def ep00010011001_2 : Blocks := edgeBlocks% "full/vectors/00010011001-E-0002.bin"
noncomputable def ep00010011001 : Blocks := (Blocks.join ep00010011001_0 (Blocks.join ep00010011001_1 ep00010011001_2))
private theorem idp00010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001100.list =
    C ((2:ℤ)^365) * horner X vp00010011001.list + horner X ep00010011001.list := by
  exact edge_identity (B := (2:ℤ)^613) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011001 : Branch 1 (-607761639/8000000 : ℚ) vp0001001100 := by
  apply branch_checked idp00010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-607761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-611761639/4000000 : ℚ) by norm_num]
  exact coverp00010011001
theorem coverp0001001100 : Covers (-607761639/8000000 : ℚ) vp0001001100 := join_branches bp00010011000 bp00010011001
private noncomputable def vp000100110_0 : Blocks := edgeBlocks% "full/vectors/000100110-V-0000.bin"
private noncomputable def vp000100110_1 : Blocks := edgeBlocks% "full/vectors/000100110-V-0001.bin"
private noncomputable def vp000100110_2 : Blocks := edgeBlocks% "full/vectors/000100110-V-0002.bin"
private noncomputable def vp000100110_3 : Blocks := edgeBlocks% "full/vectors/000100110-V-0003.bin"
private noncomputable def vp000100110_4 : Blocks := edgeBlocks% "full/vectors/000100110-V-0004.bin"
private noncomputable def vp000100110_5 : Blocks := edgeBlocks% "full/vectors/000100110-V-0005.bin"
noncomputable def vp000100110 : Blocks := (Blocks.join (Blocks.join vp000100110_0 (Blocks.join vp000100110_1 vp000100110_2)) (Blocks.join vp000100110_3 (Blocks.join vp000100110_4 vp000100110_5)))
private theorem bp0001001100 : Branch 0 (-607761639/16000000 : ℚ) vp000100110 := by
  apply branch_left_normalized (c:=vp0001001100) (k:=0) (m:=341) (by decide +kernel)
  rw [show 2*(-607761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-607761639/8000000 : ℚ) by norm_num]
  exact coverp0001001100
private noncomputable def ep0001001101_0 : Blocks := edgeBlocks% "full/vectors/0001001101-E-0000.bin"
private noncomputable def ep0001001101_1 : Blocks := edgeBlocks% "full/vectors/0001001101-E-0001.bin"
private noncomputable def ep0001001101_2 : Blocks := edgeBlocks% "full/vectors/0001001101-E-0002.bin"
private noncomputable def ep0001001101_3 : Blocks := edgeBlocks% "full/vectors/0001001101-E-0003.bin"
private noncomputable def ep0001001101_4 : Blocks := edgeBlocks% "full/vectors/0001001101-E-0004.bin"
private noncomputable def ep0001001101_5 : Blocks := edgeBlocks% "full/vectors/0001001101-E-0005.bin"
noncomputable def ep0001001101 : Blocks := (Blocks.join (Blocks.join ep0001001101_0 (Blocks.join ep0001001101_1 ep0001001101_2)) (Blocks.join ep0001001101_3 (Blocks.join ep0001001101_4 ep0001001101_5)))
private theorem idp0001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100110.list =
    C ((2:ℤ)^702) * horner X vp0001001101.list + horner X ep0001001101.list := by
  exact edge_identity (B := (2:ℤ)^1095) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001101 : Branch 1 (-607761639/16000000 : ℚ) vp000100110 := by
  apply branch_checked idp0001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-607761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-615761639/8000000 : ℚ) by norm_num]
  exact coverp0001001101
theorem coverp000100110 : Covers (-607761639/16000000 : ℚ) vp000100110 := join_branches bp0001001100 bp0001001101
private noncomputable def vp00010011_0 : Blocks := edgeBlocks% "full/vectors/00010011-V-0000.bin"
private noncomputable def vp00010011_1 : Blocks := edgeBlocks% "full/vectors/00010011-V-0001.bin"
private noncomputable def vp00010011_2 : Blocks := edgeBlocks% "full/vectors/00010011-V-0002.bin"
private noncomputable def vp00010011_3 : Blocks := edgeBlocks% "full/vectors/00010011-V-0003.bin"
private noncomputable def vp00010011_4 : Blocks := edgeBlocks% "full/vectors/00010011-V-0004.bin"
private noncomputable def vp00010011_5 : Blocks := edgeBlocks% "full/vectors/00010011-V-0005.bin"
private noncomputable def vp00010011_6 : Blocks := edgeBlocks% "full/vectors/00010011-V-0006.bin"
private noncomputable def vp00010011_7 : Blocks := edgeBlocks% "full/vectors/00010011-V-0007.bin"
private noncomputable def vp00010011_8 : Blocks := edgeBlocks% "full/vectors/00010011-V-0008.bin"
private noncomputable def vp00010011_9 : Blocks := edgeBlocks% "full/vectors/00010011-V-0009.bin"
noncomputable def vp00010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00010011_0 vp00010011_1) (Blocks.join vp00010011_2 (Blocks.join vp00010011_3 vp00010011_4))) (Blocks.join (Blocks.join vp00010011_5 vp00010011_6) (Blocks.join vp00010011_7 (Blocks.join vp00010011_8 vp00010011_9))))
private theorem bp000100110 : Branch 0 (-607761639/32000000 : ℚ) vp00010011 := by
  apply branch_left_normalized (c:=vp000100110) (k:=0) (m:=655) (by decide +kernel)
  rw [show 2*(-607761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-607761639/16000000 : ℚ) by norm_num]
  exact coverp000100110
private noncomputable def ep000100111_0 : Blocks := edgeBlocks% "full/vectors/000100111-E-0000.bin"
private noncomputable def ep000100111_1 : Blocks := edgeBlocks% "full/vectors/000100111-E-0001.bin"
private noncomputable def ep000100111_2 : Blocks := edgeBlocks% "full/vectors/000100111-E-0002.bin"
private noncomputable def ep000100111_3 : Blocks := edgeBlocks% "full/vectors/000100111-E-0003.bin"
private noncomputable def ep000100111_4 : Blocks := edgeBlocks% "full/vectors/000100111-E-0004.bin"
private noncomputable def ep000100111_5 : Blocks := edgeBlocks% "full/vectors/000100111-E-0005.bin"
private noncomputable def ep000100111_6 : Blocks := edgeBlocks% "full/vectors/000100111-E-0006.bin"
private noncomputable def ep000100111_7 : Blocks := edgeBlocks% "full/vectors/000100111-E-0007.bin"
private noncomputable def ep000100111_8 : Blocks := edgeBlocks% "full/vectors/000100111-E-0008.bin"
private noncomputable def ep000100111_9 : Blocks := edgeBlocks% "full/vectors/000100111-E-0009.bin"
noncomputable def ep000100111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000100111_0 ep000100111_1) (Blocks.join ep000100111_2 (Blocks.join ep000100111_3 ep000100111_4))) (Blocks.join (Blocks.join ep000100111_5 ep000100111_6) (Blocks.join ep000100111_7 (Blocks.join ep000100111_8 ep000100111_9))))
private theorem idp000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010011.list =
    C ((2:ℤ)^1368) * horner X vp000100111.list + horner X ep000100111.list := by
  exact edge_identity (B := (2:ℤ)^2050) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100111 : Branch 1 (-607761639/32000000 : ℚ) vp00010011 := by
  apply branch_checked idp000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-607761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-623761639/16000000 : ℚ) by norm_num]
  exact coverp000100111
theorem coverp00010011 : Covers (-607761639/32000000 : ℚ) vp00010011 := join_branches bp000100110 bp000100111
end NextProof.EdgeFull

