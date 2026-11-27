import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000000101111111_0 : Blocks := edgeBlocks% "full/vectors/0000000101111111-V-0000.bin"
noncomputable def vp0000000101111111 : Blocks := vp0000000101111111_0
theorem coverp0000000101111111 : Covers (-47636639/125000 : ℚ) vp0000000101111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101111110_0 : Blocks := edgeBlocks% "full/vectors/0000000101111110-V-0000.bin"
noncomputable def vp0000000101111110 : Blocks := vp0000000101111110_0
theorem coverp0000000101111110 : Covers (-47511639/125000 : ℚ) vp0000000101111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010111111_0 : Blocks := edgeBlocks% "full/vectors/000000010111111-V-0000.bin"
noncomputable def vp000000010111111 : Blocks := vp000000010111111_0
private theorem bp0000000101111110 : Branch 0 (-47511639/250000 : ℚ) vp000000010111111 := by
  apply branch_left_normalized (c:=vp0000000101111110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-47511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-47511639/125000 : ℚ) by norm_num]
  exact coverp0000000101111110
private noncomputable def ep0000000101111111_0 : Blocks := edgeBlocks% "full/vectors/0000000101111111-E-0000.bin"
noncomputable def ep0000000101111111 : Blocks := ep0000000101111111_0
private theorem idp0000000101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010111111.list =
    C ((2:ℤ)^56) * horner X vp0000000101111111.list + horner X ep0000000101111111.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101111111 : Branch 1 (-47511639/250000 : ℚ) vp000000010111111 := by
  apply branch_checked idp0000000101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-47511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-47636639/125000 : ℚ) by norm_num]
  exact coverp0000000101111111
theorem coverp000000010111111 : Covers (-47511639/250000 : ℚ) vp000000010111111 := join_branches bp0000000101111110 bp0000000101111111
private noncomputable def vp0000000101111101_0 : Blocks := edgeBlocks% "full/vectors/0000000101111101-V-0000.bin"
noncomputable def vp0000000101111101 : Blocks := vp0000000101111101_0
theorem coverp0000000101111101 : Covers (-47386639/125000 : ℚ) vp0000000101111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101111100_0 : Blocks := edgeBlocks% "full/vectors/0000000101111100-V-0000.bin"
noncomputable def vp0000000101111100 : Blocks := vp0000000101111100_0
theorem coverp0000000101111100 : Covers (-47261639/125000 : ℚ) vp0000000101111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010111110_0 : Blocks := edgeBlocks% "full/vectors/000000010111110-V-0000.bin"
noncomputable def vp000000010111110 : Blocks := vp000000010111110_0
private theorem bp0000000101111100 : Branch 0 (-47261639/250000 : ℚ) vp000000010111110 := by
  apply branch_left_normalized (c:=vp0000000101111100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-47261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-47261639/125000 : ℚ) by norm_num]
  exact coverp0000000101111100
private noncomputable def ep0000000101111101_0 : Blocks := edgeBlocks% "full/vectors/0000000101111101-E-0000.bin"
noncomputable def ep0000000101111101 : Blocks := ep0000000101111101_0
private theorem idp0000000101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010111110.list =
    C ((2:ℤ)^57) * horner X vp0000000101111101.list + horner X ep0000000101111101.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101111101 : Branch 1 (-47261639/250000 : ℚ) vp000000010111110 := by
  apply branch_checked idp0000000101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-47261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-47386639/125000 : ℚ) by norm_num]
  exact coverp0000000101111101
theorem coverp000000010111110 : Covers (-47261639/250000 : ℚ) vp000000010111110 := join_branches bp0000000101111100 bp0000000101111101
private noncomputable def vp00000001011111_0 : Blocks := edgeBlocks% "full/vectors/00000001011111-V-0000.bin"
noncomputable def vp00000001011111 : Blocks := vp00000001011111_0
private theorem bp000000010111110 : Branch 0 (-47261639/500000 : ℚ) vp00000001011111 := by
  apply branch_left_normalized (c:=vp000000010111110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-47261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-47261639/250000 : ℚ) by norm_num]
  exact coverp000000010111110
private noncomputable def ep000000010111111_0 : Blocks := edgeBlocks% "full/vectors/000000010111111-E-0000.bin"
noncomputable def ep000000010111111 : Blocks := ep000000010111111_0
private theorem idp000000010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001011111.list =
    C ((2:ℤ)^96) * horner X vp000000010111111.list + horner X ep000000010111111.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010111111 : Branch 1 (-47261639/500000 : ℚ) vp00000001011111 := by
  apply branch_checked idp000000010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-47261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-47511639/250000 : ℚ) by norm_num]
  exact coverp000000010111111
theorem coverp00000001011111 : Covers (-47261639/500000 : ℚ) vp00000001011111 := join_branches bp000000010111110 bp000000010111111
private noncomputable def vp0000000101111011_0 : Blocks := edgeBlocks% "full/vectors/0000000101111011-V-0000.bin"
noncomputable def vp0000000101111011 : Blocks := vp0000000101111011_0
theorem coverp0000000101111011 : Covers (-47136639/125000 : ℚ) vp0000000101111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101111010_0 : Blocks := edgeBlocks% "full/vectors/0000000101111010-V-0000.bin"
noncomputable def vp0000000101111010 : Blocks := vp0000000101111010_0
theorem coverp0000000101111010 : Covers (-47011639/125000 : ℚ) vp0000000101111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010111101_0 : Blocks := edgeBlocks% "full/vectors/000000010111101-V-0000.bin"
noncomputable def vp000000010111101 : Blocks := vp000000010111101_0
private theorem bp0000000101111010 : Branch 0 (-47011639/250000 : ℚ) vp000000010111101 := by
  apply branch_left_normalized (c:=vp0000000101111010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-47011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-47011639/125000 : ℚ) by norm_num]
  exact coverp0000000101111010
private noncomputable def ep0000000101111011_0 : Blocks := edgeBlocks% "full/vectors/0000000101111011-E-0000.bin"
noncomputable def ep0000000101111011 : Blocks := ep0000000101111011_0
private theorem idp0000000101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010111101.list =
    C ((2:ℤ)^58) * horner X vp0000000101111011.list + horner X ep0000000101111011.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101111011 : Branch 1 (-47011639/250000 : ℚ) vp000000010111101 := by
  apply branch_checked idp0000000101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-47011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-47136639/125000 : ℚ) by norm_num]
  exact coverp0000000101111011
theorem coverp000000010111101 : Covers (-47011639/250000 : ℚ) vp000000010111101 := join_branches bp0000000101111010 bp0000000101111011
private noncomputable def vp0000000101111001_0 : Blocks := edgeBlocks% "full/vectors/0000000101111001-V-0000.bin"
noncomputable def vp0000000101111001 : Blocks := vp0000000101111001_0
theorem coverp0000000101111001 : Covers (-46886639/125000 : ℚ) vp0000000101111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101111000_0 : Blocks := edgeBlocks% "full/vectors/0000000101111000-V-0000.bin"
noncomputable def vp0000000101111000 : Blocks := vp0000000101111000_0
theorem coverp0000000101111000 : Covers (-46761639/125000 : ℚ) vp0000000101111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010111100_0 : Blocks := edgeBlocks% "full/vectors/000000010111100-V-0000.bin"
noncomputable def vp000000010111100 : Blocks := vp000000010111100_0
private theorem bp0000000101111000 : Branch 0 (-46761639/250000 : ℚ) vp000000010111100 := by
  apply branch_left_normalized (c:=vp0000000101111000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-46761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-46761639/125000 : ℚ) by norm_num]
  exact coverp0000000101111000
private noncomputable def ep0000000101111001_0 : Blocks := edgeBlocks% "full/vectors/0000000101111001-E-0000.bin"
noncomputable def ep0000000101111001 : Blocks := ep0000000101111001_0
private theorem idp0000000101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010111100.list =
    C ((2:ℤ)^57) * horner X vp0000000101111001.list + horner X ep0000000101111001.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101111001 : Branch 1 (-46761639/250000 : ℚ) vp000000010111100 := by
  apply branch_checked idp0000000101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-46761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-46886639/125000 : ℚ) by norm_num]
  exact coverp0000000101111001
theorem coverp000000010111100 : Covers (-46761639/250000 : ℚ) vp000000010111100 := join_branches bp0000000101111000 bp0000000101111001
private noncomputable def vp00000001011110_0 : Blocks := edgeBlocks% "full/vectors/00000001011110-V-0000.bin"
noncomputable def vp00000001011110 : Blocks := vp00000001011110_0
private theorem bp000000010111100 : Branch 0 (-46761639/500000 : ℚ) vp00000001011110 := by
  apply branch_left_normalized (c:=vp000000010111100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-46761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-46761639/250000 : ℚ) by norm_num]
  exact coverp000000010111100
private noncomputable def ep000000010111101_0 : Blocks := edgeBlocks% "full/vectors/000000010111101-E-0000.bin"
noncomputable def ep000000010111101 : Blocks := ep000000010111101_0
private theorem idp000000010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001011110.list =
    C ((2:ℤ)^95) * horner X vp000000010111101.list + horner X ep000000010111101.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010111101 : Branch 1 (-46761639/500000 : ℚ) vp00000001011110 := by
  apply branch_checked idp000000010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-46761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-47011639/250000 : ℚ) by norm_num]
  exact coverp000000010111101
theorem coverp00000001011110 : Covers (-46761639/500000 : ℚ) vp00000001011110 := join_branches bp000000010111100 bp000000010111101
private noncomputable def vp0000000101111_0 : Blocks := edgeBlocks% "full/vectors/0000000101111-V-0000.bin"
private noncomputable def vp0000000101111_1 : Blocks := edgeBlocks% "full/vectors/0000000101111-V-0001.bin"
noncomputable def vp0000000101111 : Blocks := (Blocks.join vp0000000101111_0 vp0000000101111_1)
private theorem bp00000001011110 : Branch 0 (-46761639/1000000 : ℚ) vp0000000101111 := by
  apply branch_left_normalized (c:=vp00000001011110) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-46761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-46761639/500000 : ℚ) by norm_num]
  exact coverp00000001011110
private noncomputable def ep00000001011111_0 : Blocks := edgeBlocks% "full/vectors/00000001011111-E-0000.bin"
private noncomputable def ep00000001011111_1 : Blocks := edgeBlocks% "full/vectors/00000001011111-E-0001.bin"
noncomputable def ep00000001011111 : Blocks := (Blocks.join ep00000001011111_0 ep00000001011111_1)
private theorem idp00000001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000101111.list =
    C ((2:ℤ)^171) * horner X vp00000001011111.list + horner X ep00000001011111.list := by
  exact edge_identity (B := (2:ℤ)^346) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001011111 : Branch 1 (-46761639/1000000 : ℚ) vp0000000101111 := by
  apply branch_checked idp00000001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-46761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-47261639/500000 : ℚ) by norm_num]
  exact coverp00000001011111
theorem coverp0000000101111 : Covers (-46761639/1000000 : ℚ) vp0000000101111 := join_branches bp00000001011110 bp00000001011111
private noncomputable def vp0000000101110111_0 : Blocks := edgeBlocks% "full/vectors/0000000101110111-V-0000.bin"
noncomputable def vp0000000101110111 : Blocks := vp0000000101110111_0
theorem coverp0000000101110111 : Covers (-46636639/125000 : ℚ) vp0000000101110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101110110_0 : Blocks := edgeBlocks% "full/vectors/0000000101110110-V-0000.bin"
noncomputable def vp0000000101110110 : Blocks := vp0000000101110110_0
theorem coverp0000000101110110 : Covers (-46511639/125000 : ℚ) vp0000000101110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010111011_0 : Blocks := edgeBlocks% "full/vectors/000000010111011-V-0000.bin"
noncomputable def vp000000010111011 : Blocks := vp000000010111011_0
private theorem bp0000000101110110 : Branch 0 (-46511639/250000 : ℚ) vp000000010111011 := by
  apply branch_left_normalized (c:=vp0000000101110110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-46511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-46511639/125000 : ℚ) by norm_num]
  exact coverp0000000101110110
private noncomputable def ep0000000101110111_0 : Blocks := edgeBlocks% "full/vectors/0000000101110111-E-0000.bin"
noncomputable def ep0000000101110111 : Blocks := ep0000000101110111_0
private theorem idp0000000101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010111011.list =
    C ((2:ℤ)^56) * horner X vp0000000101110111.list + horner X ep0000000101110111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101110111 : Branch 1 (-46511639/250000 : ℚ) vp000000010111011 := by
  apply branch_checked idp0000000101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-46511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-46636639/125000 : ℚ) by norm_num]
  exact coverp0000000101110111
theorem coverp000000010111011 : Covers (-46511639/250000 : ℚ) vp000000010111011 := join_branches bp0000000101110110 bp0000000101110111
private noncomputable def vp0000000101110101_0 : Blocks := edgeBlocks% "full/vectors/0000000101110101-V-0000.bin"
noncomputable def vp0000000101110101 : Blocks := vp0000000101110101_0
theorem coverp0000000101110101 : Covers (-46386639/125000 : ℚ) vp0000000101110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101110100_0 : Blocks := edgeBlocks% "full/vectors/0000000101110100-V-0000.bin"
noncomputable def vp0000000101110100 : Blocks := vp0000000101110100_0
theorem coverp0000000101110100 : Covers (-46261639/125000 : ℚ) vp0000000101110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010111010_0 : Blocks := edgeBlocks% "full/vectors/000000010111010-V-0000.bin"
noncomputable def vp000000010111010 : Blocks := vp000000010111010_0
private theorem bp0000000101110100 : Branch 0 (-46261639/250000 : ℚ) vp000000010111010 := by
  apply branch_left_normalized (c:=vp0000000101110100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-46261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-46261639/125000 : ℚ) by norm_num]
  exact coverp0000000101110100
private noncomputable def ep0000000101110101_0 : Blocks := edgeBlocks% "full/vectors/0000000101110101-E-0000.bin"
noncomputable def ep0000000101110101 : Blocks := ep0000000101110101_0
private theorem idp0000000101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010111010.list =
    C ((2:ℤ)^55) * horner X vp0000000101110101.list + horner X ep0000000101110101.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101110101 : Branch 1 (-46261639/250000 : ℚ) vp000000010111010 := by
  apply branch_checked idp0000000101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-46261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-46386639/125000 : ℚ) by norm_num]
  exact coverp0000000101110101
theorem coverp000000010111010 : Covers (-46261639/250000 : ℚ) vp000000010111010 := join_branches bp0000000101110100 bp0000000101110101
private noncomputable def vp00000001011101_0 : Blocks := edgeBlocks% "full/vectors/00000001011101-V-0000.bin"
noncomputable def vp00000001011101 : Blocks := vp00000001011101_0
private theorem bp000000010111010 : Branch 0 (-46261639/500000 : ℚ) vp00000001011101 := by
  apply branch_left_normalized (c:=vp000000010111010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-46261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-46261639/250000 : ℚ) by norm_num]
  exact coverp000000010111010
private noncomputable def ep000000010111011_0 : Blocks := edgeBlocks% "full/vectors/000000010111011-E-0000.bin"
noncomputable def ep000000010111011 : Blocks := ep000000010111011_0
private theorem idp000000010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001011101.list =
    C ((2:ℤ)^93) * horner X vp000000010111011.list + horner X ep000000010111011.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010111011 : Branch 1 (-46261639/500000 : ℚ) vp00000001011101 := by
  apply branch_checked idp000000010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-46261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-46511639/250000 : ℚ) by norm_num]
  exact coverp000000010111011
theorem coverp00000001011101 : Covers (-46261639/500000 : ℚ) vp00000001011101 := join_branches bp000000010111010 bp000000010111011
private noncomputable def vp0000000101110011_0 : Blocks := edgeBlocks% "full/vectors/0000000101110011-V-0000.bin"
noncomputable def vp0000000101110011 : Blocks := vp0000000101110011_0
theorem coverp0000000101110011 : Covers (-46136639/125000 : ℚ) vp0000000101110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101110010_0 : Blocks := edgeBlocks% "full/vectors/0000000101110010-V-0000.bin"
noncomputable def vp0000000101110010 : Blocks := vp0000000101110010_0
theorem coverp0000000101110010 : Covers (-46011639/125000 : ℚ) vp0000000101110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010111001_0 : Blocks := edgeBlocks% "full/vectors/000000010111001-V-0000.bin"
noncomputable def vp000000010111001 : Blocks := vp000000010111001_0
private theorem bp0000000101110010 : Branch 0 (-46011639/250000 : ℚ) vp000000010111001 := by
  apply branch_left_normalized (c:=vp0000000101110010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-46011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-46011639/125000 : ℚ) by norm_num]
  exact coverp0000000101110010
private noncomputable def ep0000000101110011_0 : Blocks := edgeBlocks% "full/vectors/0000000101110011-E-0000.bin"
noncomputable def ep0000000101110011 : Blocks := ep0000000101110011_0
private theorem idp0000000101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010111001.list =
    C ((2:ℤ)^56) * horner X vp0000000101110011.list + horner X ep0000000101110011.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101110011 : Branch 1 (-46011639/250000 : ℚ) vp000000010111001 := by
  apply branch_checked idp0000000101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-46011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-46136639/125000 : ℚ) by norm_num]
  exact coverp0000000101110011
theorem coverp000000010111001 : Covers (-46011639/250000 : ℚ) vp000000010111001 := join_branches bp0000000101110010 bp0000000101110011
private noncomputable def vp0000000101110001_0 : Blocks := edgeBlocks% "full/vectors/0000000101110001-V-0000.bin"
noncomputable def vp0000000101110001 : Blocks := vp0000000101110001_0
theorem coverp0000000101110001 : Covers (-45886639/125000 : ℚ) vp0000000101110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101110000_0 : Blocks := edgeBlocks% "full/vectors/0000000101110000-V-0000.bin"
noncomputable def vp0000000101110000 : Blocks := vp0000000101110000_0
theorem coverp0000000101110000 : Covers (-45761639/125000 : ℚ) vp0000000101110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010111000_0 : Blocks := edgeBlocks% "full/vectors/000000010111000-V-0000.bin"
noncomputable def vp000000010111000 : Blocks := vp000000010111000_0
private theorem bp0000000101110000 : Branch 0 (-45761639/250000 : ℚ) vp000000010111000 := by
  apply branch_left_normalized (c:=vp0000000101110000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-45761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-45761639/125000 : ℚ) by norm_num]
  exact coverp0000000101110000
private noncomputable def ep0000000101110001_0 : Blocks := edgeBlocks% "full/vectors/0000000101110001-E-0000.bin"
noncomputable def ep0000000101110001 : Blocks := ep0000000101110001_0
private theorem idp0000000101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010111000.list =
    C ((2:ℤ)^56) * horner X vp0000000101110001.list + horner X ep0000000101110001.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101110001 : Branch 1 (-45761639/250000 : ℚ) vp000000010111000 := by
  apply branch_checked idp0000000101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-45761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-45886639/125000 : ℚ) by norm_num]
  exact coverp0000000101110001
theorem coverp000000010111000 : Covers (-45761639/250000 : ℚ) vp000000010111000 := join_branches bp0000000101110000 bp0000000101110001
private noncomputable def vp00000001011100_0 : Blocks := edgeBlocks% "full/vectors/00000001011100-V-0000.bin"
noncomputable def vp00000001011100 : Blocks := vp00000001011100_0
private theorem bp000000010111000 : Branch 0 (-45761639/500000 : ℚ) vp00000001011100 := by
  apply branch_left_normalized (c:=vp000000010111000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-45761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-45761639/250000 : ℚ) by norm_num]
  exact coverp000000010111000
private noncomputable def ep000000010111001_0 : Blocks := edgeBlocks% "full/vectors/000000010111001-E-0000.bin"
noncomputable def ep000000010111001 : Blocks := ep000000010111001_0
private theorem idp000000010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001011100.list =
    C ((2:ℤ)^93) * horner X vp000000010111001.list + horner X ep000000010111001.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010111001 : Branch 1 (-45761639/500000 : ℚ) vp00000001011100 := by
  apply branch_checked idp000000010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-45761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-46011639/250000 : ℚ) by norm_num]
  exact coverp000000010111001
theorem coverp00000001011100 : Covers (-45761639/500000 : ℚ) vp00000001011100 := join_branches bp000000010111000 bp000000010111001
private noncomputable def vp0000000101110_0 : Blocks := edgeBlocks% "full/vectors/0000000101110-V-0000.bin"
private noncomputable def vp0000000101110_1 : Blocks := edgeBlocks% "full/vectors/0000000101110-V-0001.bin"
noncomputable def vp0000000101110 : Blocks := (Blocks.join vp0000000101110_0 vp0000000101110_1)
private theorem bp00000001011100 : Branch 0 (-45761639/1000000 : ℚ) vp0000000101110 := by
  apply branch_left_normalized (c:=vp00000001011100) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-45761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-45761639/500000 : ℚ) by norm_num]
  exact coverp00000001011100
private noncomputable def ep00000001011101_0 : Blocks := edgeBlocks% "full/vectors/00000001011101-E-0000.bin"
private noncomputable def ep00000001011101_1 : Blocks := edgeBlocks% "full/vectors/00000001011101-E-0001.bin"
noncomputable def ep00000001011101 : Blocks := (Blocks.join ep00000001011101_0 ep00000001011101_1)
private theorem idp00000001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000101110.list =
    C ((2:ℤ)^168) * horner X vp00000001011101.list + horner X ep00000001011101.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001011101 : Branch 1 (-45761639/1000000 : ℚ) vp0000000101110 := by
  apply branch_checked idp00000001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-45761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-46261639/500000 : ℚ) by norm_num]
  exact coverp00000001011101
theorem coverp0000000101110 : Covers (-45761639/1000000 : ℚ) vp0000000101110 := join_branches bp00000001011100 bp00000001011101
private noncomputable def vp000000010111_0 : Blocks := edgeBlocks% "full/vectors/000000010111-V-0000.bin"
private noncomputable def vp000000010111_1 : Blocks := edgeBlocks% "full/vectors/000000010111-V-0001.bin"
private noncomputable def vp000000010111_2 : Blocks := edgeBlocks% "full/vectors/000000010111-V-0002.bin"
noncomputable def vp000000010111 : Blocks := (Blocks.join vp000000010111_0 (Blocks.join vp000000010111_1 vp000000010111_2))
private theorem bp0000000101110 : Branch 0 (-45761639/2000000 : ℚ) vp000000010111 := by
  apply branch_left_normalized (c:=vp0000000101110) (k:=0) (m:=165) (by decide +kernel)
  rw [show 2*(-45761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-45761639/1000000 : ℚ) by norm_num]
  exact coverp0000000101110
private noncomputable def ep0000000101111_0 : Blocks := edgeBlocks% "full/vectors/0000000101111-E-0000.bin"
private noncomputable def ep0000000101111_1 : Blocks := edgeBlocks% "full/vectors/0000000101111-E-0001.bin"
private noncomputable def ep0000000101111_2 : Blocks := edgeBlocks% "full/vectors/0000000101111-E-0002.bin"
noncomputable def ep0000000101111 : Blocks := (Blocks.join ep0000000101111_0 (Blocks.join ep0000000101111_1 ep0000000101111_2))
private theorem idp0000000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010111.list =
    C ((2:ℤ)^310) * horner X vp0000000101111.list + horner X ep0000000101111.list := by
  exact edge_identity (B := (2:ℤ)^561) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101111 : Branch 1 (-45761639/2000000 : ℚ) vp000000010111 := by
  apply branch_checked idp0000000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-45761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-46761639/1000000 : ℚ) by norm_num]
  exact coverp0000000101111
theorem coverp000000010111 : Covers (-45761639/2000000 : ℚ) vp000000010111 := join_branches bp0000000101110 bp0000000101111
private noncomputable def vp0000000101101111_0 : Blocks := edgeBlocks% "full/vectors/0000000101101111-V-0000.bin"
noncomputable def vp0000000101101111 : Blocks := vp0000000101101111_0
theorem coverp0000000101101111 : Covers (-45636639/125000 : ℚ) vp0000000101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101101110_0 : Blocks := edgeBlocks% "full/vectors/0000000101101110-V-0000.bin"
noncomputable def vp0000000101101110 : Blocks := vp0000000101101110_0
theorem coverp0000000101101110 : Covers (-45511639/125000 : ℚ) vp0000000101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010110111_0 : Blocks := edgeBlocks% "full/vectors/000000010110111-V-0000.bin"
noncomputable def vp000000010110111 : Blocks := vp000000010110111_0
private theorem bp0000000101101110 : Branch 0 (-45511639/250000 : ℚ) vp000000010110111 := by
  apply branch_left_normalized (c:=vp0000000101101110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-45511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-45511639/125000 : ℚ) by norm_num]
  exact coverp0000000101101110
private noncomputable def ep0000000101101111_0 : Blocks := edgeBlocks% "full/vectors/0000000101101111-E-0000.bin"
noncomputable def ep0000000101101111 : Blocks := ep0000000101101111_0
private theorem idp0000000101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010110111.list =
    C ((2:ℤ)^56) * horner X vp0000000101101111.list + horner X ep0000000101101111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101101111 : Branch 1 (-45511639/250000 : ℚ) vp000000010110111 := by
  apply branch_checked idp0000000101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-45511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-45636639/125000 : ℚ) by norm_num]
  exact coverp0000000101101111
theorem coverp000000010110111 : Covers (-45511639/250000 : ℚ) vp000000010110111 := join_branches bp0000000101101110 bp0000000101101111
private noncomputable def vp0000000101101101_0 : Blocks := edgeBlocks% "full/vectors/0000000101101101-V-0000.bin"
noncomputable def vp0000000101101101 : Blocks := vp0000000101101101_0
theorem coverp0000000101101101 : Covers (-45386639/125000 : ℚ) vp0000000101101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101101100_0 : Blocks := edgeBlocks% "full/vectors/0000000101101100-V-0000.bin"
noncomputable def vp0000000101101100 : Blocks := vp0000000101101100_0
theorem coverp0000000101101100 : Covers (-45261639/125000 : ℚ) vp0000000101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010110110_0 : Blocks := edgeBlocks% "full/vectors/000000010110110-V-0000.bin"
noncomputable def vp000000010110110 : Blocks := vp000000010110110_0
private theorem bp0000000101101100 : Branch 0 (-45261639/250000 : ℚ) vp000000010110110 := by
  apply branch_left_normalized (c:=vp0000000101101100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-45261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-45261639/125000 : ℚ) by norm_num]
  exact coverp0000000101101100
private noncomputable def ep0000000101101101_0 : Blocks := edgeBlocks% "full/vectors/0000000101101101-E-0000.bin"
noncomputable def ep0000000101101101 : Blocks := ep0000000101101101_0
private theorem idp0000000101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010110110.list =
    C ((2:ℤ)^57) * horner X vp0000000101101101.list + horner X ep0000000101101101.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101101101 : Branch 1 (-45261639/250000 : ℚ) vp000000010110110 := by
  apply branch_checked idp0000000101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-45261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-45386639/125000 : ℚ) by norm_num]
  exact coverp0000000101101101
theorem coverp000000010110110 : Covers (-45261639/250000 : ℚ) vp000000010110110 := join_branches bp0000000101101100 bp0000000101101101
private noncomputable def vp00000001011011_0 : Blocks := edgeBlocks% "full/vectors/00000001011011-V-0000.bin"
noncomputable def vp00000001011011 : Blocks := vp00000001011011_0
private theorem bp000000010110110 : Branch 0 (-45261639/500000 : ℚ) vp00000001011011 := by
  apply branch_left_normalized (c:=vp000000010110110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-45261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-45261639/250000 : ℚ) by norm_num]
  exact coverp000000010110110
private noncomputable def ep000000010110111_0 : Blocks := edgeBlocks% "full/vectors/000000010110111-E-0000.bin"
noncomputable def ep000000010110111 : Blocks := ep000000010110111_0
private theorem idp000000010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001011011.list =
    C ((2:ℤ)^95) * horner X vp000000010110111.list + horner X ep000000010110111.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010110111 : Branch 1 (-45261639/500000 : ℚ) vp00000001011011 := by
  apply branch_checked idp000000010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-45261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-45511639/250000 : ℚ) by norm_num]
  exact coverp000000010110111
theorem coverp00000001011011 : Covers (-45261639/500000 : ℚ) vp00000001011011 := join_branches bp000000010110110 bp000000010110111
private noncomputable def vp0000000101101011_0 : Blocks := edgeBlocks% "full/vectors/0000000101101011-V-0000.bin"
noncomputable def vp0000000101101011 : Blocks := vp0000000101101011_0
theorem coverp0000000101101011 : Covers (-45136639/125000 : ℚ) vp0000000101101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101101010_0 : Blocks := edgeBlocks% "full/vectors/0000000101101010-V-0000.bin"
noncomputable def vp0000000101101010 : Blocks := vp0000000101101010_0
theorem coverp0000000101101010 : Covers (-45011639/125000 : ℚ) vp0000000101101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010110101_0 : Blocks := edgeBlocks% "full/vectors/000000010110101-V-0000.bin"
noncomputable def vp000000010110101 : Blocks := vp000000010110101_0
private theorem bp0000000101101010 : Branch 0 (-45011639/250000 : ℚ) vp000000010110101 := by
  apply branch_left_normalized (c:=vp0000000101101010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-45011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-45011639/125000 : ℚ) by norm_num]
  exact coverp0000000101101010
private noncomputable def ep0000000101101011_0 : Blocks := edgeBlocks% "full/vectors/0000000101101011-E-0000.bin"
noncomputable def ep0000000101101011 : Blocks := ep0000000101101011_0
private theorem idp0000000101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010110101.list =
    C ((2:ℤ)^58) * horner X vp0000000101101011.list + horner X ep0000000101101011.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101101011 : Branch 1 (-45011639/250000 : ℚ) vp000000010110101 := by
  apply branch_checked idp0000000101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-45011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-45136639/125000 : ℚ) by norm_num]
  exact coverp0000000101101011
theorem coverp000000010110101 : Covers (-45011639/250000 : ℚ) vp000000010110101 := join_branches bp0000000101101010 bp0000000101101011
private noncomputable def vp0000000101101001_0 : Blocks := edgeBlocks% "full/vectors/0000000101101001-V-0000.bin"
noncomputable def vp0000000101101001 : Blocks := vp0000000101101001_0
theorem coverp0000000101101001 : Covers (-44886639/125000 : ℚ) vp0000000101101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010110100011_0 : Blocks := edgeBlocks% "full/vectors/000000010110100011-V-0000.bin"
noncomputable def vp000000010110100011 : Blocks := vp000000010110100011_0
theorem coverp000000010110100011 : Covers (-44855389/31250 : ℚ) vp000000010110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010110100010_0 : Blocks := edgeBlocks% "full/vectors/000000010110100010-V-0000.bin"
noncomputable def vp000000010110100010 : Blocks := vp000000010110100010_0
theorem coverp000000010110100010 : Covers (-44824139/31250 : ℚ) vp000000010110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001011010001_0 : Blocks := edgeBlocks% "full/vectors/00000001011010001-V-0000.bin"
noncomputable def vp00000001011010001 : Blocks := vp00000001011010001_0
private theorem bp000000010110100010 : Branch 0 (-44824139/62500 : ℚ) vp00000001011010001 := by
  apply branch_left_normalized (c:=vp000000010110100010) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-44824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-44824139/31250 : ℚ) by norm_num]
  exact coverp000000010110100010
private noncomputable def ep000000010110100011_0 : Blocks := edgeBlocks% "full/vectors/000000010110100011-E-0000.bin"
noncomputable def ep000000010110100011 : Blocks := ep000000010110100011_0
private theorem idp000000010110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001011010001.list =
    C ((2:ℤ)^26) * horner X vp000000010110100011.list + horner X ep000000010110100011.list := by
  exact edge_identity (B := (2:ℤ)^134) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010110100011 : Branch 1 (-44824139/62500 : ℚ) vp00000001011010001 := by
  apply branch_checked idp000000010110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-44824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-44855389/31250 : ℚ) by norm_num]
  exact coverp000000010110100011
theorem coverp00000001011010001 : Covers (-44824139/62500 : ℚ) vp00000001011010001 := join_branches bp000000010110100010 bp000000010110100011
private noncomputable def vp00000001011010000_0 : Blocks := edgeBlocks% "full/vectors/00000001011010000-V-0000.bin"
noncomputable def vp00000001011010000 : Blocks := vp00000001011010000_0
theorem coverp00000001011010000 : Covers (-44761639/62500 : ℚ) vp00000001011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101101000_0 : Blocks := edgeBlocks% "full/vectors/0000000101101000-V-0000.bin"
noncomputable def vp0000000101101000 : Blocks := vp0000000101101000_0
private theorem bp00000001011010000 : Branch 0 (-44761639/125000 : ℚ) vp0000000101101000 := by
  apply branch_left_normalized (c:=vp00000001011010000) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-44761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-44761639/62500 : ℚ) by norm_num]
  exact coverp00000001011010000
private noncomputable def ep00000001011010001_0 : Blocks := edgeBlocks% "full/vectors/00000001011010001-E-0000.bin"
noncomputable def ep00000001011010001 : Blocks := ep00000001011010001_0
private theorem idp00000001011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000101101000.list =
    C ((2:ℤ)^36) * horner X vp00000001011010001.list + horner X ep00000001011010001.list := by
  exact edge_identity (B := (2:ℤ)^146) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001011010001 : Branch 1 (-44761639/125000 : ℚ) vp0000000101101000 := by
  apply branch_checked idp00000001011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-44761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-44824139/62500 : ℚ) by norm_num]
  exact coverp00000001011010001
theorem coverp0000000101101000 : Covers (-44761639/125000 : ℚ) vp0000000101101000 := join_branches bp00000001011010000 bp00000001011010001
private noncomputable def vp000000010110100_0 : Blocks := edgeBlocks% "full/vectors/000000010110100-V-0000.bin"
noncomputable def vp000000010110100 : Blocks := vp000000010110100_0
private theorem bp0000000101101000 : Branch 0 (-44761639/250000 : ℚ) vp000000010110100 := by
  apply branch_left_normalized (c:=vp0000000101101000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-44761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-44761639/125000 : ℚ) by norm_num]
  exact coverp0000000101101000
private noncomputable def ep0000000101101001_0 : Blocks := edgeBlocks% "full/vectors/0000000101101001-E-0000.bin"
noncomputable def ep0000000101101001 : Blocks := ep0000000101101001_0
private theorem idp0000000101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010110100.list =
    C ((2:ℤ)^57) * horner X vp0000000101101001.list + horner X ep0000000101101001.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101101001 : Branch 1 (-44761639/250000 : ℚ) vp000000010110100 := by
  apply branch_checked idp0000000101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-44761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-44886639/125000 : ℚ) by norm_num]
  exact coverp0000000101101001
theorem coverp000000010110100 : Covers (-44761639/250000 : ℚ) vp000000010110100 := join_branches bp0000000101101000 bp0000000101101001
private noncomputable def vp00000001011010_0 : Blocks := edgeBlocks% "full/vectors/00000001011010-V-0000.bin"
noncomputable def vp00000001011010 : Blocks := vp00000001011010_0
private theorem bp000000010110100 : Branch 0 (-44761639/500000 : ℚ) vp00000001011010 := by
  apply branch_left_normalized (c:=vp000000010110100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-44761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-44761639/250000 : ℚ) by norm_num]
  exact coverp000000010110100
private noncomputable def ep000000010110101_0 : Blocks := edgeBlocks% "full/vectors/000000010110101-E-0000.bin"
noncomputable def ep000000010110101 : Blocks := ep000000010110101_0
private theorem idp000000010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001011010.list =
    C ((2:ℤ)^95) * horner X vp000000010110101.list + horner X ep000000010110101.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010110101 : Branch 1 (-44761639/500000 : ℚ) vp00000001011010 := by
  apply branch_checked idp000000010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-44761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-45011639/250000 : ℚ) by norm_num]
  exact coverp000000010110101
theorem coverp00000001011010 : Covers (-44761639/500000 : ℚ) vp00000001011010 := join_branches bp000000010110100 bp000000010110101
private noncomputable def vp0000000101101_0 : Blocks := edgeBlocks% "full/vectors/0000000101101-V-0000.bin"
private noncomputable def vp0000000101101_1 : Blocks := edgeBlocks% "full/vectors/0000000101101-V-0001.bin"
noncomputable def vp0000000101101 : Blocks := (Blocks.join vp0000000101101_0 vp0000000101101_1)
private theorem bp00000001011010 : Branch 0 (-44761639/1000000 : ℚ) vp0000000101101 := by
  apply branch_left_normalized (c:=vp00000001011010) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-44761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-44761639/500000 : ℚ) by norm_num]
  exact coverp00000001011010
private noncomputable def ep00000001011011_0 : Blocks := edgeBlocks% "full/vectors/00000001011011-E-0000.bin"
private noncomputable def ep00000001011011_1 : Blocks := edgeBlocks% "full/vectors/00000001011011-E-0001.bin"
noncomputable def ep00000001011011 : Blocks := (Blocks.join ep00000001011011_0 ep00000001011011_1)
private theorem idp00000001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000101101.list =
    C ((2:ℤ)^172) * horner X vp00000001011011.list + horner X ep00000001011011.list := by
  exact edge_identity (B := (2:ℤ)^345) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001011011 : Branch 1 (-44761639/1000000 : ℚ) vp0000000101101 := by
  apply branch_checked idp00000001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-44761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-45261639/500000 : ℚ) by norm_num]
  exact coverp00000001011011
theorem coverp0000000101101 : Covers (-44761639/1000000 : ℚ) vp0000000101101 := join_branches bp00000001011010 bp00000001011011
private noncomputable def vp0000000101100111_0 : Blocks := edgeBlocks% "full/vectors/0000000101100111-V-0000.bin"
noncomputable def vp0000000101100111 : Blocks := vp0000000101100111_0
theorem coverp0000000101100111 : Covers (-44636639/125000 : ℚ) vp0000000101100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101100110_0 : Blocks := edgeBlocks% "full/vectors/0000000101100110-V-0000.bin"
noncomputable def vp0000000101100110 : Blocks := vp0000000101100110_0
theorem coverp0000000101100110 : Covers (-44511639/125000 : ℚ) vp0000000101100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010110011_0 : Blocks := edgeBlocks% "full/vectors/000000010110011-V-0000.bin"
noncomputable def vp000000010110011 : Blocks := vp000000010110011_0
private theorem bp0000000101100110 : Branch 0 (-44511639/250000 : ℚ) vp000000010110011 := by
  apply branch_left_normalized (c:=vp0000000101100110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-44511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-44511639/125000 : ℚ) by norm_num]
  exact coverp0000000101100110
private noncomputable def ep0000000101100111_0 : Blocks := edgeBlocks% "full/vectors/0000000101100111-E-0000.bin"
noncomputable def ep0000000101100111 : Blocks := ep0000000101100111_0
private theorem idp0000000101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010110011.list =
    C ((2:ℤ)^55) * horner X vp0000000101100111.list + horner X ep0000000101100111.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101100111 : Branch 1 (-44511639/250000 : ℚ) vp000000010110011 := by
  apply branch_checked idp0000000101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-44511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-44636639/125000 : ℚ) by norm_num]
  exact coverp0000000101100111
theorem coverp000000010110011 : Covers (-44511639/250000 : ℚ) vp000000010110011 := join_branches bp0000000101100110 bp0000000101100111
private noncomputable def vp0000000101100101_0 : Blocks := edgeBlocks% "full/vectors/0000000101100101-V-0000.bin"
noncomputable def vp0000000101100101 : Blocks := vp0000000101100101_0
theorem coverp0000000101100101 : Covers (-44386639/125000 : ℚ) vp0000000101100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101100100_0 : Blocks := edgeBlocks% "full/vectors/0000000101100100-V-0000.bin"
noncomputable def vp0000000101100100 : Blocks := vp0000000101100100_0
theorem coverp0000000101100100 : Covers (-44261639/125000 : ℚ) vp0000000101100100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010110010_0 : Blocks := edgeBlocks% "full/vectors/000000010110010-V-0000.bin"
noncomputable def vp000000010110010 : Blocks := vp000000010110010_0
private theorem bp0000000101100100 : Branch 0 (-44261639/250000 : ℚ) vp000000010110010 := by
  apply branch_left_normalized (c:=vp0000000101100100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-44261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-44261639/125000 : ℚ) by norm_num]
  exact coverp0000000101100100
private noncomputable def ep0000000101100101_0 : Blocks := edgeBlocks% "full/vectors/0000000101100101-E-0000.bin"
noncomputable def ep0000000101100101 : Blocks := ep0000000101100101_0
private theorem idp0000000101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010110010.list =
    C ((2:ℤ)^54) * horner X vp0000000101100101.list + horner X ep0000000101100101.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101100101 : Branch 1 (-44261639/250000 : ℚ) vp000000010110010 := by
  apply branch_checked idp0000000101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-44261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-44386639/125000 : ℚ) by norm_num]
  exact coverp0000000101100101
theorem coverp000000010110010 : Covers (-44261639/250000 : ℚ) vp000000010110010 := join_branches bp0000000101100100 bp0000000101100101
private noncomputable def vp00000001011001_0 : Blocks := edgeBlocks% "full/vectors/00000001011001-V-0000.bin"
noncomputable def vp00000001011001 : Blocks := vp00000001011001_0
private theorem bp000000010110010 : Branch 0 (-44261639/500000 : ℚ) vp00000001011001 := by
  apply branch_left_normalized (c:=vp000000010110010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-44261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-44261639/250000 : ℚ) by norm_num]
  exact coverp000000010110010
private noncomputable def ep000000010110011_0 : Blocks := edgeBlocks% "full/vectors/000000010110011-E-0000.bin"
noncomputable def ep000000010110011 : Blocks := ep000000010110011_0
private theorem idp000000010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001011001.list =
    C ((2:ℤ)^92) * horner X vp000000010110011.list + horner X ep000000010110011.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010110011 : Branch 1 (-44261639/500000 : ℚ) vp00000001011001 := by
  apply branch_checked idp000000010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-44261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-44511639/250000 : ℚ) by norm_num]
  exact coverp000000010110011
theorem coverp00000001011001 : Covers (-44261639/500000 : ℚ) vp00000001011001 := join_branches bp000000010110010 bp000000010110011
private noncomputable def vp0000000101100011_0 : Blocks := edgeBlocks% "full/vectors/0000000101100011-V-0000.bin"
noncomputable def vp0000000101100011 : Blocks := vp0000000101100011_0
theorem coverp0000000101100011 : Covers (-44136639/125000 : ℚ) vp0000000101100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000101100010_0 : Blocks := edgeBlocks% "full/vectors/0000000101100010-V-0000.bin"
noncomputable def vp0000000101100010 : Blocks := vp0000000101100010_0
theorem coverp0000000101100010 : Covers (-44011639/125000 : ℚ) vp0000000101100010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010110001_0 : Blocks := edgeBlocks% "full/vectors/000000010110001-V-0000.bin"
noncomputable def vp000000010110001 : Blocks := vp000000010110001_0
private theorem bp0000000101100010 : Branch 0 (-44011639/250000 : ℚ) vp000000010110001 := by
  apply branch_left_normalized (c:=vp0000000101100010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-44011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-44011639/125000 : ℚ) by norm_num]
  exact coverp0000000101100010
private noncomputable def ep0000000101100011_0 : Blocks := edgeBlocks% "full/vectors/0000000101100011-E-0000.bin"
noncomputable def ep0000000101100011 : Blocks := ep0000000101100011_0
private theorem idp0000000101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010110001.list =
    C ((2:ℤ)^54) * horner X vp0000000101100011.list + horner X ep0000000101100011.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101100011 : Branch 1 (-44011639/250000 : ℚ) vp000000010110001 := by
  apply branch_checked idp0000000101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-44011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-44136639/125000 : ℚ) by norm_num]
  exact coverp0000000101100011
theorem coverp000000010110001 : Covers (-44011639/250000 : ℚ) vp000000010110001 := join_branches bp0000000101100010 bp0000000101100011
private noncomputable def vp000000010110000_0 : Blocks := edgeBlocks% "full/vectors/000000010110000-V-0000.bin"
noncomputable def vp000000010110000 : Blocks := vp000000010110000_0
theorem coverp000000010110000 : Covers (-43761639/250000 : ℚ) vp000000010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001011000_0 : Blocks := edgeBlocks% "full/vectors/00000001011000-V-0000.bin"
noncomputable def vp00000001011000 : Blocks := vp00000001011000_0
private theorem bp000000010110000 : Branch 0 (-43761639/500000 : ℚ) vp00000001011000 := by
  apply branch_left_normalized (c:=vp000000010110000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-43761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-43761639/250000 : ℚ) by norm_num]
  exact coverp000000010110000
private noncomputable def ep000000010110001_0 : Blocks := edgeBlocks% "full/vectors/000000010110001-E-0000.bin"
noncomputable def ep000000010110001 : Blocks := ep000000010110001_0
private theorem idp000000010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001011000.list =
    C ((2:ℤ)^91) * horner X vp000000010110001.list + horner X ep000000010110001.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010110001 : Branch 1 (-43761639/500000 : ℚ) vp00000001011000 := by
  apply branch_checked idp000000010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-43761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-44011639/250000 : ℚ) by norm_num]
  exact coverp000000010110001
theorem coverp00000001011000 : Covers (-43761639/500000 : ℚ) vp00000001011000 := join_branches bp000000010110000 bp000000010110001
private noncomputable def vp0000000101100_0 : Blocks := edgeBlocks% "full/vectors/0000000101100-V-0000.bin"
private noncomputable def vp0000000101100_1 : Blocks := edgeBlocks% "full/vectors/0000000101100-V-0001.bin"
noncomputable def vp0000000101100 : Blocks := (Blocks.join vp0000000101100_0 vp0000000101100_1)
private theorem bp00000001011000 : Branch 0 (-43761639/1000000 : ℚ) vp0000000101100 := by
  apply branch_left_normalized (c:=vp00000001011000) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-43761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-43761639/500000 : ℚ) by norm_num]
  exact coverp00000001011000
private noncomputable def ep00000001011001_0 : Blocks := edgeBlocks% "full/vectors/00000001011001-E-0000.bin"
private noncomputable def ep00000001011001_1 : Blocks := edgeBlocks% "full/vectors/00000001011001-E-0001.bin"
noncomputable def ep00000001011001 : Blocks := (Blocks.join ep00000001011001_0 ep00000001011001_1)
private theorem idp00000001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000101100.list =
    C ((2:ℤ)^165) * horner X vp00000001011001.list + horner X ep00000001011001.list := by
  exact edge_identity (B := (2:ℤ)^336) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001011001 : Branch 1 (-43761639/1000000 : ℚ) vp0000000101100 := by
  apply branch_checked idp00000001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-43761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-44261639/500000 : ℚ) by norm_num]
  exact coverp00000001011001
theorem coverp0000000101100 : Covers (-43761639/1000000 : ℚ) vp0000000101100 := join_branches bp00000001011000 bp00000001011001
private noncomputable def vp000000010110_0 : Blocks := edgeBlocks% "full/vectors/000000010110-V-0000.bin"
private noncomputable def vp000000010110_1 : Blocks := edgeBlocks% "full/vectors/000000010110-V-0001.bin"
private noncomputable def vp000000010110_2 : Blocks := edgeBlocks% "full/vectors/000000010110-V-0002.bin"
noncomputable def vp000000010110 : Blocks := (Blocks.join vp000000010110_0 (Blocks.join vp000000010110_1 vp000000010110_2))
private theorem bp0000000101100 : Branch 0 (-43761639/2000000 : ℚ) vp000000010110 := by
  apply branch_left_normalized (c:=vp0000000101100) (k:=0) (m:=164) (by decide +kernel)
  rw [show 2*(-43761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-43761639/1000000 : ℚ) by norm_num]
  exact coverp0000000101100
private noncomputable def ep0000000101101_0 : Blocks := edgeBlocks% "full/vectors/0000000101101-E-0000.bin"
private noncomputable def ep0000000101101_1 : Blocks := edgeBlocks% "full/vectors/0000000101101-E-0001.bin"
private noncomputable def ep0000000101101_2 : Blocks := edgeBlocks% "full/vectors/0000000101101-E-0002.bin"
noncomputable def ep0000000101101 : Blocks := (Blocks.join ep0000000101101_0 (Blocks.join ep0000000101101_1 ep0000000101101_2))
private theorem idp0000000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010110.list =
    C ((2:ℤ)^313) * horner X vp0000000101101.list + horner X ep0000000101101.list := by
  exact edge_identity (B := (2:ℤ)^563) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101101 : Branch 1 (-43761639/2000000 : ℚ) vp000000010110 := by
  apply branch_checked idp0000000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-43761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-44761639/1000000 : ℚ) by norm_num]
  exact coverp0000000101101
theorem coverp000000010110 : Covers (-43761639/2000000 : ℚ) vp000000010110 := join_branches bp0000000101100 bp0000000101101
private noncomputable def vp00000001011_0 : Blocks := edgeBlocks% "full/vectors/00000001011-V-0000.bin"
private noncomputable def vp00000001011_1 : Blocks := edgeBlocks% "full/vectors/00000001011-V-0001.bin"
private noncomputable def vp00000001011_2 : Blocks := edgeBlocks% "full/vectors/00000001011-V-0002.bin"
private noncomputable def vp00000001011_3 : Blocks := edgeBlocks% "full/vectors/00000001011-V-0003.bin"
private noncomputable def vp00000001011_4 : Blocks := edgeBlocks% "full/vectors/00000001011-V-0004.bin"
noncomputable def vp00000001011 : Blocks := (Blocks.join (Blocks.join vp00000001011_0 vp00000001011_1) (Blocks.join vp00000001011_2 (Blocks.join vp00000001011_3 vp00000001011_4)))
private theorem bp000000010110 : Branch 0 (-43761639/4000000 : ℚ) vp00000001011 := by
  apply branch_left_normalized (c:=vp000000010110) (k:=0) (m:=312) (by decide +kernel)
  rw [show 2*(-43761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-43761639/2000000 : ℚ) by norm_num]
  exact coverp000000010110
private noncomputable def ep000000010111_0 : Blocks := edgeBlocks% "full/vectors/000000010111-E-0000.bin"
private noncomputable def ep000000010111_1 : Blocks := edgeBlocks% "full/vectors/000000010111-E-0001.bin"
private noncomputable def ep000000010111_2 : Blocks := edgeBlocks% "full/vectors/000000010111-E-0002.bin"
private noncomputable def ep000000010111_3 : Blocks := edgeBlocks% "full/vectors/000000010111-E-0003.bin"
private noncomputable def ep000000010111_4 : Blocks := edgeBlocks% "full/vectors/000000010111-E-0004.bin"
noncomputable def ep000000010111 : Blocks := (Blocks.join (Blocks.join ep000000010111_0 ep000000010111_1) (Blocks.join ep000000010111_2 (Blocks.join ep000000010111_3 ep000000010111_4)))
private theorem idp000000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001011.list =
    C ((2:ℤ)^611) * horner X vp000000010111.list + horner X ep000000010111.list := by
  exact edge_identity (B := (2:ℤ)^1011) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010111 : Branch 1 (-43761639/4000000 : ℚ) vp00000001011 := by
  apply branch_checked idp000000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-43761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-45761639/2000000 : ℚ) by norm_num]
  exact coverp000000010111
theorem coverp00000001011 : Covers (-43761639/4000000 : ℚ) vp00000001011 := join_branches bp000000010110 bp000000010111
private noncomputable def vp000000010101111_0 : Blocks := edgeBlocks% "full/vectors/000000010101111-V-0000.bin"
noncomputable def vp000000010101111 : Blocks := vp000000010101111_0
theorem coverp000000010101111 : Covers (-43511639/250000 : ℚ) vp000000010101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010101110_0 : Blocks := edgeBlocks% "full/vectors/000000010101110-V-0000.bin"
noncomputable def vp000000010101110 : Blocks := vp000000010101110_0
theorem coverp000000010101110 : Covers (-43261639/250000 : ℚ) vp000000010101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001010111_0 : Blocks := edgeBlocks% "full/vectors/00000001010111-V-0000.bin"
noncomputable def vp00000001010111 : Blocks := vp00000001010111_0
private theorem bp000000010101110 : Branch 0 (-43261639/500000 : ℚ) vp00000001010111 := by
  apply branch_left_normalized (c:=vp000000010101110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-43261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-43261639/250000 : ℚ) by norm_num]
  exact coverp000000010101110
private noncomputable def ep000000010101111_0 : Blocks := edgeBlocks% "full/vectors/000000010101111-E-0000.bin"
noncomputable def ep000000010101111 : Blocks := ep000000010101111_0
private theorem idp000000010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001010111.list =
    C ((2:ℤ)^91) * horner X vp000000010101111.list + horner X ep000000010101111.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010101111 : Branch 1 (-43261639/500000 : ℚ) vp00000001010111 := by
  apply branch_checked idp000000010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-43261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-43511639/250000 : ℚ) by norm_num]
  exact coverp000000010101111
theorem coverp00000001010111 : Covers (-43261639/500000 : ℚ) vp00000001010111 := join_branches bp000000010101110 bp000000010101111
private noncomputable def vp000000010101101_0 : Blocks := edgeBlocks% "full/vectors/000000010101101-V-0000.bin"
noncomputable def vp000000010101101 : Blocks := vp000000010101101_0
theorem coverp000000010101101 : Covers (-43011639/250000 : ℚ) vp000000010101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010101100_0 : Blocks := edgeBlocks% "full/vectors/000000010101100-V-0000.bin"
noncomputable def vp000000010101100 : Blocks := vp000000010101100_0
theorem coverp000000010101100 : Covers (-42761639/250000 : ℚ) vp000000010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001010110_0 : Blocks := edgeBlocks% "full/vectors/00000001010110-V-0000.bin"
noncomputable def vp00000001010110 : Blocks := vp00000001010110_0
private theorem bp000000010101100 : Branch 0 (-42761639/500000 : ℚ) vp00000001010110 := by
  apply branch_left_normalized (c:=vp000000010101100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-42761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-42761639/250000 : ℚ) by norm_num]
  exact coverp000000010101100
private noncomputable def ep000000010101101_0 : Blocks := edgeBlocks% "full/vectors/000000010101101-E-0000.bin"
noncomputable def ep000000010101101 : Blocks := ep000000010101101_0
private theorem idp000000010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001010110.list =
    C ((2:ℤ)^92) * horner X vp000000010101101.list + horner X ep000000010101101.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010101101 : Branch 1 (-42761639/500000 : ℚ) vp00000001010110 := by
  apply branch_checked idp000000010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-42761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-43011639/250000 : ℚ) by norm_num]
  exact coverp000000010101101
theorem coverp00000001010110 : Covers (-42761639/500000 : ℚ) vp00000001010110 := join_branches bp000000010101100 bp000000010101101
private noncomputable def vp0000000101011_0 : Blocks := edgeBlocks% "full/vectors/0000000101011-V-0000.bin"
private noncomputable def vp0000000101011_1 : Blocks := edgeBlocks% "full/vectors/0000000101011-V-0001.bin"
noncomputable def vp0000000101011 : Blocks := (Blocks.join vp0000000101011_0 vp0000000101011_1)
private theorem bp00000001010110 : Branch 0 (-42761639/1000000 : ℚ) vp0000000101011 := by
  apply branch_left_normalized (c:=vp00000001010110) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-42761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-42761639/500000 : ℚ) by norm_num]
  exact coverp00000001010110
private noncomputable def ep00000001010111_0 : Blocks := edgeBlocks% "full/vectors/00000001010111-E-0000.bin"
private noncomputable def ep00000001010111_1 : Blocks := edgeBlocks% "full/vectors/00000001010111-E-0001.bin"
noncomputable def ep00000001010111 : Blocks := (Blocks.join ep00000001010111_0 ep00000001010111_1)
private theorem idp00000001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000101011.list =
    C ((2:ℤ)^167) * horner X vp00000001010111.list + horner X ep00000001010111.list := by
  exact edge_identity (B := (2:ℤ)^335) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001010111 : Branch 1 (-42761639/1000000 : ℚ) vp0000000101011 := by
  apply branch_checked idp00000001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-42761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-43261639/500000 : ℚ) by norm_num]
  exact coverp00000001010111
theorem coverp0000000101011 : Covers (-42761639/1000000 : ℚ) vp0000000101011 := join_branches bp00000001010110 bp00000001010111
private noncomputable def vp000000010101011_0 : Blocks := edgeBlocks% "full/vectors/000000010101011-V-0000.bin"
noncomputable def vp000000010101011 : Blocks := vp000000010101011_0
theorem coverp000000010101011 : Covers (-42511639/250000 : ℚ) vp000000010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010101010_0 : Blocks := edgeBlocks% "full/vectors/000000010101010-V-0000.bin"
noncomputable def vp000000010101010 : Blocks := vp000000010101010_0
theorem coverp000000010101010 : Covers (-42261639/250000 : ℚ) vp000000010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001010101_0 : Blocks := edgeBlocks% "full/vectors/00000001010101-V-0000.bin"
noncomputable def vp00000001010101 : Blocks := vp00000001010101_0
private theorem bp000000010101010 : Branch 0 (-42261639/500000 : ℚ) vp00000001010101 := by
  apply branch_left_normalized (c:=vp000000010101010) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-42261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-42261639/250000 : ℚ) by norm_num]
  exact coverp000000010101010
private noncomputable def ep000000010101011_0 : Blocks := edgeBlocks% "full/vectors/000000010101011-E-0000.bin"
noncomputable def ep000000010101011 : Blocks := ep000000010101011_0
private theorem idp000000010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001010101.list =
    C ((2:ℤ)^93) * horner X vp000000010101011.list + horner X ep000000010101011.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010101011 : Branch 1 (-42261639/500000 : ℚ) vp00000001010101 := by
  apply branch_checked idp000000010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-42261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-42511639/250000 : ℚ) by norm_num]
  exact coverp000000010101011
theorem coverp00000001010101 : Covers (-42261639/500000 : ℚ) vp00000001010101 := join_branches bp000000010101010 bp000000010101011
private noncomputable def vp000000010101001_0 : Blocks := edgeBlocks% "full/vectors/000000010101001-V-0000.bin"
noncomputable def vp000000010101001 : Blocks := vp000000010101001_0
theorem coverp000000010101001 : Covers (-42011639/250000 : ℚ) vp000000010101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010101000_0 : Blocks := edgeBlocks% "full/vectors/000000010101000-V-0000.bin"
noncomputable def vp000000010101000 : Blocks := vp000000010101000_0
theorem coverp000000010101000 : Covers (-41761639/250000 : ℚ) vp000000010101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001010100_0 : Blocks := edgeBlocks% "full/vectors/00000001010100-V-0000.bin"
noncomputable def vp00000001010100 : Blocks := vp00000001010100_0
private theorem bp000000010101000 : Branch 0 (-41761639/500000 : ℚ) vp00000001010100 := by
  apply branch_left_normalized (c:=vp000000010101000) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-41761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-41761639/250000 : ℚ) by norm_num]
  exact coverp000000010101000
private noncomputable def ep000000010101001_0 : Blocks := edgeBlocks% "full/vectors/000000010101001-E-0000.bin"
noncomputable def ep000000010101001 : Blocks := ep000000010101001_0
private theorem idp000000010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001010100.list =
    C ((2:ℤ)^92) * horner X vp000000010101001.list + horner X ep000000010101001.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010101001 : Branch 1 (-41761639/500000 : ℚ) vp00000001010100 := by
  apply branch_checked idp000000010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-41761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-42011639/250000 : ℚ) by norm_num]
  exact coverp000000010101001
theorem coverp00000001010100 : Covers (-41761639/500000 : ℚ) vp00000001010100 := join_branches bp000000010101000 bp000000010101001
private noncomputable def vp0000000101010_0 : Blocks := edgeBlocks% "full/vectors/0000000101010-V-0000.bin"
private noncomputable def vp0000000101010_1 : Blocks := edgeBlocks% "full/vectors/0000000101010-V-0001.bin"
noncomputable def vp0000000101010 : Blocks := (Blocks.join vp0000000101010_0 vp0000000101010_1)
private theorem bp00000001010100 : Branch 0 (-41761639/1000000 : ℚ) vp0000000101010 := by
  apply branch_left_normalized (c:=vp00000001010100) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-41761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-41761639/500000 : ℚ) by norm_num]
  exact coverp00000001010100
private noncomputable def ep00000001010101_0 : Blocks := edgeBlocks% "full/vectors/00000001010101-E-0000.bin"
private noncomputable def ep00000001010101_1 : Blocks := edgeBlocks% "full/vectors/00000001010101-E-0001.bin"
noncomputable def ep00000001010101 : Blocks := (Blocks.join ep00000001010101_0 ep00000001010101_1)
private theorem idp00000001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000101010.list =
    C ((2:ℤ)^169) * horner X vp00000001010101.list + horner X ep00000001010101.list := by
  exact edge_identity (B := (2:ℤ)^337) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001010101 : Branch 1 (-41761639/1000000 : ℚ) vp0000000101010 := by
  apply branch_checked idp00000001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-41761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-42261639/500000 : ℚ) by norm_num]
  exact coverp00000001010101
theorem coverp0000000101010 : Covers (-41761639/1000000 : ℚ) vp0000000101010 := join_branches bp00000001010100 bp00000001010101
private noncomputable def vp000000010101_0 : Blocks := edgeBlocks% "full/vectors/000000010101-V-0000.bin"
private noncomputable def vp000000010101_1 : Blocks := edgeBlocks% "full/vectors/000000010101-V-0001.bin"
private noncomputable def vp000000010101_2 : Blocks := edgeBlocks% "full/vectors/000000010101-V-0002.bin"
noncomputable def vp000000010101 : Blocks := (Blocks.join vp000000010101_0 (Blocks.join vp000000010101_1 vp000000010101_2))
private theorem bp0000000101010 : Branch 0 (-41761639/2000000 : ℚ) vp000000010101 := by
  apply branch_left_normalized (c:=vp0000000101010) (k:=0) (m:=166) (by decide +kernel)
  rw [show 2*(-41761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-41761639/1000000 : ℚ) by norm_num]
  exact coverp0000000101010
private noncomputable def ep0000000101011_0 : Blocks := edgeBlocks% "full/vectors/0000000101011-E-0000.bin"
private noncomputable def ep0000000101011_1 : Blocks := edgeBlocks% "full/vectors/0000000101011-E-0001.bin"
private noncomputable def ep0000000101011_2 : Blocks := edgeBlocks% "full/vectors/0000000101011-E-0002.bin"
noncomputable def ep0000000101011 : Blocks := (Blocks.join ep0000000101011_0 (Blocks.join ep0000000101011_1 ep0000000101011_2))
private theorem idp0000000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010101.list =
    C ((2:ℤ)^323) * horner X vp0000000101011.list + horner X ep0000000101011.list := by
  exact edge_identity (B := (2:ℤ)^568) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101011 : Branch 1 (-41761639/2000000 : ℚ) vp000000010101 := by
  apply branch_checked idp0000000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-41761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-42761639/1000000 : ℚ) by norm_num]
  exact coverp0000000101011
theorem coverp000000010101 : Covers (-41761639/2000000 : ℚ) vp000000010101 := join_branches bp0000000101010 bp0000000101011
private noncomputable def vp000000010100111_0 : Blocks := edgeBlocks% "full/vectors/000000010100111-V-0000.bin"
noncomputable def vp000000010100111 : Blocks := vp000000010100111_0
theorem coverp000000010100111 : Covers (-41511639/250000 : ℚ) vp000000010100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010100110_0 : Blocks := edgeBlocks% "full/vectors/000000010100110-V-0000.bin"
noncomputable def vp000000010100110 : Blocks := vp000000010100110_0
theorem coverp000000010100110 : Covers (-41261639/250000 : ℚ) vp000000010100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001010011_0 : Blocks := edgeBlocks% "full/vectors/00000001010011-V-0000.bin"
noncomputable def vp00000001010011 : Blocks := vp00000001010011_0
private theorem bp000000010100110 : Branch 0 (-41261639/500000 : ℚ) vp00000001010011 := by
  apply branch_left_normalized (c:=vp000000010100110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-41261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-41261639/250000 : ℚ) by norm_num]
  exact coverp000000010100110
private noncomputable def ep000000010100111_0 : Blocks := edgeBlocks% "full/vectors/000000010100111-E-0000.bin"
noncomputable def ep000000010100111 : Blocks := ep000000010100111_0
private theorem idp000000010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001010011.list =
    C ((2:ℤ)^93) * horner X vp000000010100111.list + horner X ep000000010100111.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010100111 : Branch 1 (-41261639/500000 : ℚ) vp00000001010011 := by
  apply branch_checked idp000000010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-41261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-41511639/250000 : ℚ) by norm_num]
  exact coverp000000010100111
theorem coverp00000001010011 : Covers (-41261639/500000 : ℚ) vp00000001010011 := join_branches bp000000010100110 bp000000010100111
private noncomputable def vp000000010100101_0 : Blocks := edgeBlocks% "full/vectors/000000010100101-V-0000.bin"
noncomputable def vp000000010100101 : Blocks := vp000000010100101_0
theorem coverp000000010100101 : Covers (-41011639/250000 : ℚ) vp000000010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010100100_0 : Blocks := edgeBlocks% "full/vectors/000000010100100-V-0000.bin"
noncomputable def vp000000010100100 : Blocks := vp000000010100100_0
theorem coverp000000010100100 : Covers (-40761639/250000 : ℚ) vp000000010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001010010_0 : Blocks := edgeBlocks% "full/vectors/00000001010010-V-0000.bin"
noncomputable def vp00000001010010 : Blocks := vp00000001010010_0
private theorem bp000000010100100 : Branch 0 (-40761639/500000 : ℚ) vp00000001010010 := by
  apply branch_left_normalized (c:=vp000000010100100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-40761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-40761639/250000 : ℚ) by norm_num]
  exact coverp000000010100100
private noncomputable def ep000000010100101_0 : Blocks := edgeBlocks% "full/vectors/000000010100101-E-0000.bin"
noncomputable def ep000000010100101 : Blocks := ep000000010100101_0
private theorem idp000000010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001010010.list =
    C ((2:ℤ)^93) * horner X vp000000010100101.list + horner X ep000000010100101.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010100101 : Branch 1 (-40761639/500000 : ℚ) vp00000001010010 := by
  apply branch_checked idp000000010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-40761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-41011639/250000 : ℚ) by norm_num]
  exact coverp000000010100101
theorem coverp00000001010010 : Covers (-40761639/500000 : ℚ) vp00000001010010 := join_branches bp000000010100100 bp000000010100101
private noncomputable def vp0000000101001_0 : Blocks := edgeBlocks% "full/vectors/0000000101001-V-0000.bin"
private noncomputable def vp0000000101001_1 : Blocks := edgeBlocks% "full/vectors/0000000101001-V-0001.bin"
noncomputable def vp0000000101001 : Blocks := (Blocks.join vp0000000101001_0 vp0000000101001_1)
private theorem bp00000001010010 : Branch 0 (-40761639/1000000 : ℚ) vp0000000101001 := by
  apply branch_left_normalized (c:=vp00000001010010) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-40761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-40761639/500000 : ℚ) by norm_num]
  exact coverp00000001010010
private noncomputable def ep00000001010011_0 : Blocks := edgeBlocks% "full/vectors/00000001010011-E-0000.bin"
private noncomputable def ep00000001010011_1 : Blocks := edgeBlocks% "full/vectors/00000001010011-E-0001.bin"
noncomputable def ep00000001010011 : Blocks := (Blocks.join ep00000001010011_0 ep00000001010011_1)
private theorem idp00000001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000101001.list =
    C ((2:ℤ)^170) * horner X vp00000001010011.list + horner X ep00000001010011.list := by
  exact edge_identity (B := (2:ℤ)^338) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001010011 : Branch 1 (-40761639/1000000 : ℚ) vp0000000101001 := by
  apply branch_checked idp00000001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-40761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-41261639/500000 : ℚ) by norm_num]
  exact coverp00000001010011
theorem coverp0000000101001 : Covers (-40761639/1000000 : ℚ) vp0000000101001 := join_branches bp00000001010010 bp00000001010011
private noncomputable def vp000000010100011_0 : Blocks := edgeBlocks% "full/vectors/000000010100011-V-0000.bin"
noncomputable def vp000000010100011 : Blocks := vp000000010100011_0
theorem coverp000000010100011 : Covers (-40511639/250000 : ℚ) vp000000010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010100010_0 : Blocks := edgeBlocks% "full/vectors/000000010100010-V-0000.bin"
noncomputable def vp000000010100010 : Blocks := vp000000010100010_0
theorem coverp000000010100010 : Covers (-40261639/250000 : ℚ) vp000000010100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001010001_0 : Blocks := edgeBlocks% "full/vectors/00000001010001-V-0000.bin"
noncomputable def vp00000001010001 : Blocks := vp00000001010001_0
private theorem bp000000010100010 : Branch 0 (-40261639/500000 : ℚ) vp00000001010001 := by
  apply branch_left_normalized (c:=vp000000010100010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-40261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-40261639/250000 : ℚ) by norm_num]
  exact coverp000000010100010
private noncomputable def ep000000010100011_0 : Blocks := edgeBlocks% "full/vectors/000000010100011-E-0000.bin"
noncomputable def ep000000010100011 : Blocks := ep000000010100011_0
private theorem idp000000010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001010001.list =
    C ((2:ℤ)^93) * horner X vp000000010100011.list + horner X ep000000010100011.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010100011 : Branch 1 (-40261639/500000 : ℚ) vp00000001010001 := by
  apply branch_checked idp000000010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-40261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-40511639/250000 : ℚ) by norm_num]
  exact coverp000000010100011
theorem coverp00000001010001 : Covers (-40261639/500000 : ℚ) vp00000001010001 := join_branches bp000000010100010 bp000000010100011
private noncomputable def vp000000010100001_0 : Blocks := edgeBlocks% "full/vectors/000000010100001-V-0000.bin"
noncomputable def vp000000010100001 : Blocks := vp000000010100001_0
theorem coverp000000010100001 : Covers (-40011639/250000 : ℚ) vp000000010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010100000_0 : Blocks := edgeBlocks% "full/vectors/000000010100000-V-0000.bin"
noncomputable def vp000000010100000 : Blocks := vp000000010100000_0
theorem coverp000000010100000 : Covers (-39761639/250000 : ℚ) vp000000010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001010000_0 : Blocks := edgeBlocks% "full/vectors/00000001010000-V-0000.bin"
noncomputable def vp00000001010000 : Blocks := vp00000001010000_0
private theorem bp000000010100000 : Branch 0 (-39761639/500000 : ℚ) vp00000001010000 := by
  apply branch_left_normalized (c:=vp000000010100000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-39761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-39761639/250000 : ℚ) by norm_num]
  exact coverp000000010100000
private noncomputable def ep000000010100001_0 : Blocks := edgeBlocks% "full/vectors/000000010100001-E-0000.bin"
noncomputable def ep000000010100001 : Blocks := ep000000010100001_0
private theorem idp000000010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001010000.list =
    C ((2:ℤ)^94) * horner X vp000000010100001.list + horner X ep000000010100001.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010100001 : Branch 1 (-39761639/500000 : ℚ) vp00000001010000 := by
  apply branch_checked idp000000010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-39761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-40011639/250000 : ℚ) by norm_num]
  exact coverp000000010100001
theorem coverp00000001010000 : Covers (-39761639/500000 : ℚ) vp00000001010000 := join_branches bp000000010100000 bp000000010100001
private noncomputable def vp0000000101000_0 : Blocks := edgeBlocks% "full/vectors/0000000101000-V-0000.bin"
private noncomputable def vp0000000101000_1 : Blocks := edgeBlocks% "full/vectors/0000000101000-V-0001.bin"
noncomputable def vp0000000101000 : Blocks := (Blocks.join vp0000000101000_0 vp0000000101000_1)
private theorem bp00000001010000 : Branch 0 (-39761639/1000000 : ℚ) vp0000000101000 := by
  apply branch_left_normalized (c:=vp00000001010000) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-39761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-39761639/500000 : ℚ) by norm_num]
  exact coverp00000001010000
private noncomputable def ep00000001010001_0 : Blocks := edgeBlocks% "full/vectors/00000001010001-E-0000.bin"
private noncomputable def ep00000001010001_1 : Blocks := edgeBlocks% "full/vectors/00000001010001-E-0001.bin"
noncomputable def ep00000001010001 : Blocks := (Blocks.join ep00000001010001_0 ep00000001010001_1)
private theorem idp00000001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000101000.list =
    C ((2:ℤ)^173) * horner X vp00000001010001.list + horner X ep00000001010001.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001010001 : Branch 1 (-39761639/1000000 : ℚ) vp0000000101000 := by
  apply branch_checked idp00000001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-39761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-40261639/500000 : ℚ) by norm_num]
  exact coverp00000001010001
theorem coverp0000000101000 : Covers (-39761639/1000000 : ℚ) vp0000000101000 := join_branches bp00000001010000 bp00000001010001
private noncomputable def vp000000010100_0 : Blocks := edgeBlocks% "full/vectors/000000010100-V-0000.bin"
private noncomputable def vp000000010100_1 : Blocks := edgeBlocks% "full/vectors/000000010100-V-0001.bin"
private noncomputable def vp000000010100_2 : Blocks := edgeBlocks% "full/vectors/000000010100-V-0002.bin"
noncomputable def vp000000010100 : Blocks := (Blocks.join vp000000010100_0 (Blocks.join vp000000010100_1 vp000000010100_2))
private theorem bp0000000101000 : Branch 0 (-39761639/2000000 : ℚ) vp000000010100 := by
  apply branch_left_normalized (c:=vp0000000101000) (k:=0) (m:=169) (by decide +kernel)
  rw [show 2*(-39761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-39761639/1000000 : ℚ) by norm_num]
  exact coverp0000000101000
private noncomputable def ep0000000101001_0 : Blocks := edgeBlocks% "full/vectors/0000000101001-E-0000.bin"
private noncomputable def ep0000000101001_1 : Blocks := edgeBlocks% "full/vectors/0000000101001-E-0001.bin"
private noncomputable def ep0000000101001_2 : Blocks := edgeBlocks% "full/vectors/0000000101001-E-0002.bin"
noncomputable def ep0000000101001 : Blocks := (Blocks.join ep0000000101001_0 (Blocks.join ep0000000101001_1 ep0000000101001_2))
private theorem idp0000000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010100.list =
    C ((2:ℤ)^330) * horner X vp0000000101001.list + horner X ep0000000101001.list := by
  exact edge_identity (B := (2:ℤ)^577) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101001 : Branch 1 (-39761639/2000000 : ℚ) vp000000010100 := by
  apply branch_checked idp0000000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-39761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-40761639/1000000 : ℚ) by norm_num]
  exact coverp0000000101001
theorem coverp000000010100 : Covers (-39761639/2000000 : ℚ) vp000000010100 := join_branches bp0000000101000 bp0000000101001
private noncomputable def vp00000001010_0 : Blocks := edgeBlocks% "full/vectors/00000001010-V-0000.bin"
private noncomputable def vp00000001010_1 : Blocks := edgeBlocks% "full/vectors/00000001010-V-0001.bin"
private noncomputable def vp00000001010_2 : Blocks := edgeBlocks% "full/vectors/00000001010-V-0002.bin"
private noncomputable def vp00000001010_3 : Blocks := edgeBlocks% "full/vectors/00000001010-V-0003.bin"
private noncomputable def vp00000001010_4 : Blocks := edgeBlocks% "full/vectors/00000001010-V-0004.bin"
noncomputable def vp00000001010 : Blocks := (Blocks.join (Blocks.join vp00000001010_0 vp00000001010_1) (Blocks.join vp00000001010_2 (Blocks.join vp00000001010_3 vp00000001010_4)))
private theorem bp000000010100 : Branch 0 (-39761639/4000000 : ℚ) vp00000001010 := by
  apply branch_left_normalized (c:=vp000000010100) (k:=0) (m:=323) (by decide +kernel)
  rw [show 2*(-39761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-39761639/2000000 : ℚ) by norm_num]
  exact coverp000000010100
private noncomputable def ep000000010101_0 : Blocks := edgeBlocks% "full/vectors/000000010101-E-0000.bin"
private noncomputable def ep000000010101_1 : Blocks := edgeBlocks% "full/vectors/000000010101-E-0001.bin"
private noncomputable def ep000000010101_2 : Blocks := edgeBlocks% "full/vectors/000000010101-E-0002.bin"
private noncomputable def ep000000010101_3 : Blocks := edgeBlocks% "full/vectors/000000010101-E-0003.bin"
private noncomputable def ep000000010101_4 : Blocks := edgeBlocks% "full/vectors/000000010101-E-0004.bin"
noncomputable def ep000000010101 : Blocks := (Blocks.join (Blocks.join ep000000010101_0 ep000000010101_1) (Blocks.join ep000000010101_2 (Blocks.join ep000000010101_3 ep000000010101_4)))
private theorem idp000000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001010.list =
    C ((2:ℤ)^642) * horner X vp000000010101.list + horner X ep000000010101.list := by
  exact edge_identity (B := (2:ℤ)^1049) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010101 : Branch 1 (-39761639/4000000 : ℚ) vp00000001010 := by
  apply branch_checked idp000000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-39761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-41761639/2000000 : ℚ) by norm_num]
  exact coverp000000010101
theorem coverp00000001010 : Covers (-39761639/4000000 : ℚ) vp00000001010 := join_branches bp000000010100 bp000000010101
private noncomputable def vp0000000101_0 : Blocks := edgeBlocks% "full/vectors/0000000101-V-0000.bin"
private noncomputable def vp0000000101_1 : Blocks := edgeBlocks% "full/vectors/0000000101-V-0001.bin"
private noncomputable def vp0000000101_2 : Blocks := edgeBlocks% "full/vectors/0000000101-V-0002.bin"
private noncomputable def vp0000000101_3 : Blocks := edgeBlocks% "full/vectors/0000000101-V-0003.bin"
private noncomputable def vp0000000101_4 : Blocks := edgeBlocks% "full/vectors/0000000101-V-0004.bin"
private noncomputable def vp0000000101_5 : Blocks := edgeBlocks% "full/vectors/0000000101-V-0005.bin"
private noncomputable def vp0000000101_6 : Blocks := edgeBlocks% "full/vectors/0000000101-V-0006.bin"
private noncomputable def vp0000000101_7 : Blocks := edgeBlocks% "full/vectors/0000000101-V-0007.bin"
private noncomputable def vp0000000101_8 : Blocks := edgeBlocks% "full/vectors/0000000101-V-0008.bin"
private noncomputable def vp0000000101_9 : Blocks := edgeBlocks% "full/vectors/0000000101-V-0009.bin"
noncomputable def vp0000000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0000000101_0 vp0000000101_1) (Blocks.join vp0000000101_2 (Blocks.join vp0000000101_3 vp0000000101_4))) (Blocks.join (Blocks.join vp0000000101_5 vp0000000101_6) (Blocks.join vp0000000101_7 (Blocks.join vp0000000101_8 vp0000000101_9))))
private theorem bp00000001010 : Branch 0 (-39761639/8000000 : ℚ) vp0000000101 := by
  apply branch_left_normalized (c:=vp00000001010) (k:=0) (m:=630) (by decide +kernel)
  rw [show 2*(-39761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-39761639/4000000 : ℚ) by norm_num]
  exact coverp00000001010
private noncomputable def ep00000001011_0 : Blocks := edgeBlocks% "full/vectors/00000001011-E-0000.bin"
private noncomputable def ep00000001011_1 : Blocks := edgeBlocks% "full/vectors/00000001011-E-0001.bin"
private noncomputable def ep00000001011_2 : Blocks := edgeBlocks% "full/vectors/00000001011-E-0002.bin"
private noncomputable def ep00000001011_3 : Blocks := edgeBlocks% "full/vectors/00000001011-E-0003.bin"
private noncomputable def ep00000001011_4 : Blocks := edgeBlocks% "full/vectors/00000001011-E-0004.bin"
private noncomputable def ep00000001011_5 : Blocks := edgeBlocks% "full/vectors/00000001011-E-0005.bin"
private noncomputable def ep00000001011_6 : Blocks := edgeBlocks% "full/vectors/00000001011-E-0006.bin"
private noncomputable def ep00000001011_7 : Blocks := edgeBlocks% "full/vectors/00000001011-E-0007.bin"
private noncomputable def ep00000001011_8 : Blocks := edgeBlocks% "full/vectors/00000001011-E-0008.bin"
private noncomputable def ep00000001011_9 : Blocks := edgeBlocks% "full/vectors/00000001011-E-0009.bin"
noncomputable def ep00000001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00000001011_0 ep00000001011_1) (Blocks.join ep00000001011_2 (Blocks.join ep00000001011_3 ep00000001011_4))) (Blocks.join (Blocks.join ep00000001011_5 ep00000001011_6) (Blocks.join ep00000001011_7 (Blocks.join ep00000001011_8 ep00000001011_9))))
private theorem idp00000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000101.list =
    C ((2:ℤ)^1255) * horner X vp00000001011.list + horner X ep00000001011.list := by
  exact edge_identity (B := (2:ℤ)^1981) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001011 : Branch 1 (-39761639/8000000 : ℚ) vp0000000101 := by
  apply branch_checked idp00000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-39761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-43761639/4000000 : ℚ) by norm_num]
  exact coverp00000001011
theorem coverp0000000101 : Covers (-39761639/8000000 : ℚ) vp0000000101 := join_branches bp00000001010 bp00000001011
end NextProof.EdgeFull

