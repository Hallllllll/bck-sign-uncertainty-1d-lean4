import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000001011111111_0 : Blocks := edgeBlocks% "full/vectors/000001011111111-V-0000.bin"
noncomputable def vp000001011111111 : Blocks := vp000001011111111_0
theorem coverp000001011111111 : Covers (-191511639/250000 : ℚ) vp000001011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011111110_0 : Blocks := edgeBlocks% "full/vectors/000001011111110-V-0000.bin"
noncomputable def vp000001011111110 : Blocks := vp000001011111110_0
theorem coverp000001011111110 : Covers (-191261639/250000 : ℚ) vp000001011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101111111_0 : Blocks := edgeBlocks% "full/vectors/00000101111111-V-0000.bin"
noncomputable def vp00000101111111 : Blocks := vp00000101111111_0
private theorem bp000001011111110 : Branch 0 (-191261639/500000 : ℚ) vp00000101111111 := by
  apply branch_left_normalized (c:=vp000001011111110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-191261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-191261639/250000 : ℚ) by norm_num]
  exact coverp000001011111110
private noncomputable def ep000001011111111_0 : Blocks := edgeBlocks% "full/vectors/000001011111111-E-0000.bin"
noncomputable def ep000001011111111 : Blocks := ep000001011111111_0
private theorem idp000001011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101111111.list =
    C ((2:ℤ)^57) * horner X vp000001011111111.list + horner X ep000001011111111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011111111 : Branch 1 (-191261639/500000 : ℚ) vp00000101111111 := by
  apply branch_checked idp000001011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-191261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-191511639/250000 : ℚ) by norm_num]
  exact coverp000001011111111
theorem coverp00000101111111 : Covers (-191261639/500000 : ℚ) vp00000101111111 := join_branches bp000001011111110 bp000001011111111
private noncomputable def vp000001011111101_0 : Blocks := edgeBlocks% "full/vectors/000001011111101-V-0000.bin"
noncomputable def vp000001011111101 : Blocks := vp000001011111101_0
theorem coverp000001011111101 : Covers (-191011639/250000 : ℚ) vp000001011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011111100_0 : Blocks := edgeBlocks% "full/vectors/000001011111100-V-0000.bin"
noncomputable def vp000001011111100 : Blocks := vp000001011111100_0
theorem coverp000001011111100 : Covers (-190761639/250000 : ℚ) vp000001011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101111110_0 : Blocks := edgeBlocks% "full/vectors/00000101111110-V-0000.bin"
noncomputable def vp00000101111110 : Blocks := vp00000101111110_0
private theorem bp000001011111100 : Branch 0 (-190761639/500000 : ℚ) vp00000101111110 := by
  apply branch_left_normalized (c:=vp000001011111100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-190761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-190761639/250000 : ℚ) by norm_num]
  exact coverp000001011111100
private noncomputable def ep000001011111101_0 : Blocks := edgeBlocks% "full/vectors/000001011111101-E-0000.bin"
noncomputable def ep000001011111101 : Blocks := ep000001011111101_0
private theorem idp000001011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101111110.list =
    C ((2:ℤ)^58) * horner X vp000001011111101.list + horner X ep000001011111101.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011111101 : Branch 1 (-190761639/500000 : ℚ) vp00000101111110 := by
  apply branch_checked idp000001011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-190761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-191011639/250000 : ℚ) by norm_num]
  exact coverp000001011111101
theorem coverp00000101111110 : Covers (-190761639/500000 : ℚ) vp00000101111110 := join_branches bp000001011111100 bp000001011111101
private noncomputable def vp0000010111111_0 : Blocks := edgeBlocks% "full/vectors/0000010111111-V-0000.bin"
noncomputable def vp0000010111111 : Blocks := vp0000010111111_0
private theorem bp00000101111110 : Branch 0 (-190761639/1000000 : ℚ) vp0000010111111 := by
  apply branch_left_normalized (c:=vp00000101111110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-190761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-190761639/500000 : ℚ) by norm_num]
  exact coverp00000101111110
private noncomputable def ep00000101111111_0 : Blocks := edgeBlocks% "full/vectors/00000101111111-E-0000.bin"
noncomputable def ep00000101111111 : Blocks := ep00000101111111_0
private theorem idp00000101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010111111.list =
    C ((2:ℤ)^96) * horner X vp00000101111111.list + horner X ep00000101111111.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101111111 : Branch 1 (-190761639/1000000 : ℚ) vp0000010111111 := by
  apply branch_checked idp00000101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-190761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-191261639/500000 : ℚ) by norm_num]
  exact coverp00000101111111
theorem coverp0000010111111 : Covers (-190761639/1000000 : ℚ) vp0000010111111 := join_branches bp00000101111110 bp00000101111111
private noncomputable def vp000001011111011_0 : Blocks := edgeBlocks% "full/vectors/000001011111011-V-0000.bin"
noncomputable def vp000001011111011 : Blocks := vp000001011111011_0
theorem coverp000001011111011 : Covers (-190511639/250000 : ℚ) vp000001011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011111010_0 : Blocks := edgeBlocks% "full/vectors/000001011111010-V-0000.bin"
noncomputable def vp000001011111010 : Blocks := vp000001011111010_0
theorem coverp000001011111010 : Covers (-190261639/250000 : ℚ) vp000001011111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101111101_0 : Blocks := edgeBlocks% "full/vectors/00000101111101-V-0000.bin"
noncomputable def vp00000101111101 : Blocks := vp00000101111101_0
private theorem bp000001011111010 : Branch 0 (-190261639/500000 : ℚ) vp00000101111101 := by
  apply branch_left_normalized (c:=vp000001011111010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-190261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-190261639/250000 : ℚ) by norm_num]
  exact coverp000001011111010
private noncomputable def ep000001011111011_0 : Blocks := edgeBlocks% "full/vectors/000001011111011-E-0000.bin"
noncomputable def ep000001011111011 : Blocks := ep000001011111011_0
private theorem idp000001011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101111101.list =
    C ((2:ℤ)^58) * horner X vp000001011111011.list + horner X ep000001011111011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011111011 : Branch 1 (-190261639/500000 : ℚ) vp00000101111101 := by
  apply branch_checked idp000001011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-190261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-190511639/250000 : ℚ) by norm_num]
  exact coverp000001011111011
theorem coverp00000101111101 : Covers (-190261639/500000 : ℚ) vp00000101111101 := join_branches bp000001011111010 bp000001011111011
private noncomputable def vp000001011111001_0 : Blocks := edgeBlocks% "full/vectors/000001011111001-V-0000.bin"
noncomputable def vp000001011111001 : Blocks := vp000001011111001_0
theorem coverp000001011111001 : Covers (-190011639/250000 : ℚ) vp000001011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011111000_0 : Blocks := edgeBlocks% "full/vectors/000001011111000-V-0000.bin"
noncomputable def vp000001011111000 : Blocks := vp000001011111000_0
theorem coverp000001011111000 : Covers (-189761639/250000 : ℚ) vp000001011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101111100_0 : Blocks := edgeBlocks% "full/vectors/00000101111100-V-0000.bin"
noncomputable def vp00000101111100 : Blocks := vp00000101111100_0
private theorem bp000001011111000 : Branch 0 (-189761639/500000 : ℚ) vp00000101111100 := by
  apply branch_left_normalized (c:=vp000001011111000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-189761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-189761639/250000 : ℚ) by norm_num]
  exact coverp000001011111000
private noncomputable def ep000001011111001_0 : Blocks := edgeBlocks% "full/vectors/000001011111001-E-0000.bin"
noncomputable def ep000001011111001 : Blocks := ep000001011111001_0
private theorem idp000001011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101111100.list =
    C ((2:ℤ)^57) * horner X vp000001011111001.list + horner X ep000001011111001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011111001 : Branch 1 (-189761639/500000 : ℚ) vp00000101111100 := by
  apply branch_checked idp000001011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-189761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-190011639/250000 : ℚ) by norm_num]
  exact coverp000001011111001
theorem coverp00000101111100 : Covers (-189761639/500000 : ℚ) vp00000101111100 := join_branches bp000001011111000 bp000001011111001
private noncomputable def vp0000010111110_0 : Blocks := edgeBlocks% "full/vectors/0000010111110-V-0000.bin"
noncomputable def vp0000010111110 : Blocks := vp0000010111110_0
private theorem bp00000101111100 : Branch 0 (-189761639/1000000 : ℚ) vp0000010111110 := by
  apply branch_left_normalized (c:=vp00000101111100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-189761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-189761639/500000 : ℚ) by norm_num]
  exact coverp00000101111100
private noncomputable def ep00000101111101_0 : Blocks := edgeBlocks% "full/vectors/00000101111101-E-0000.bin"
noncomputable def ep00000101111101 : Blocks := ep00000101111101_0
private theorem idp00000101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010111110.list =
    C ((2:ℤ)^97) * horner X vp00000101111101.list + horner X ep00000101111101.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101111101 : Branch 1 (-189761639/1000000 : ℚ) vp0000010111110 := by
  apply branch_checked idp00000101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-189761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-190261639/500000 : ℚ) by norm_num]
  exact coverp00000101111101
theorem coverp0000010111110 : Covers (-189761639/1000000 : ℚ) vp0000010111110 := join_branches bp00000101111100 bp00000101111101
private noncomputable def vp000001011111_0 : Blocks := edgeBlocks% "full/vectors/000001011111-V-0000.bin"
private noncomputable def vp000001011111_1 : Blocks := edgeBlocks% "full/vectors/000001011111-V-0001.bin"
noncomputable def vp000001011111 : Blocks := (Blocks.join vp000001011111_0 vp000001011111_1)
private theorem bp0000010111110 : Branch 0 (-189761639/2000000 : ℚ) vp000001011111 := by
  apply branch_left_normalized (c:=vp0000010111110) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-189761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-189761639/1000000 : ℚ) by norm_num]
  exact coverp0000010111110
private noncomputable def ep0000010111111_0 : Blocks := edgeBlocks% "full/vectors/0000010111111-E-0000.bin"
private noncomputable def ep0000010111111_1 : Blocks := edgeBlocks% "full/vectors/0000010111111-E-0001.bin"
noncomputable def ep0000010111111 : Blocks := (Blocks.join ep0000010111111_0 ep0000010111111_1)
private theorem idp0000010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001011111.list =
    C ((2:ℤ)^172) * horner X vp0000010111111.list + horner X ep0000010111111.list := by
  exact edge_identity (B := (2:ℤ)^344) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010111111 : Branch 1 (-189761639/2000000 : ℚ) vp000001011111 := by
  apply branch_checked idp0000010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-189761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-190761639/1000000 : ℚ) by norm_num]
  exact coverp0000010111111
theorem coverp000001011111 : Covers (-189761639/2000000 : ℚ) vp000001011111 := join_branches bp0000010111110 bp0000010111111
private noncomputable def vp000001011110111_0 : Blocks := edgeBlocks% "full/vectors/000001011110111-V-0000.bin"
noncomputable def vp000001011110111 : Blocks := vp000001011110111_0
theorem coverp000001011110111 : Covers (-189511639/250000 : ℚ) vp000001011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011110110_0 : Blocks := edgeBlocks% "full/vectors/000001011110110-V-0000.bin"
noncomputable def vp000001011110110 : Blocks := vp000001011110110_0
theorem coverp000001011110110 : Covers (-189261639/250000 : ℚ) vp000001011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101111011_0 : Blocks := edgeBlocks% "full/vectors/00000101111011-V-0000.bin"
noncomputable def vp00000101111011 : Blocks := vp00000101111011_0
private theorem bp000001011110110 : Branch 0 (-189261639/500000 : ℚ) vp00000101111011 := by
  apply branch_left_normalized (c:=vp000001011110110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-189261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-189261639/250000 : ℚ) by norm_num]
  exact coverp000001011110110
private noncomputable def ep000001011110111_0 : Blocks := edgeBlocks% "full/vectors/000001011110111-E-0000.bin"
noncomputable def ep000001011110111 : Blocks := ep000001011110111_0
private theorem idp000001011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101111011.list =
    C ((2:ℤ)^58) * horner X vp000001011110111.list + horner X ep000001011110111.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011110111 : Branch 1 (-189261639/500000 : ℚ) vp00000101111011 := by
  apply branch_checked idp000001011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-189261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-189511639/250000 : ℚ) by norm_num]
  exact coverp000001011110111
theorem coverp00000101111011 : Covers (-189261639/500000 : ℚ) vp00000101111011 := join_branches bp000001011110110 bp000001011110111
private noncomputable def vp000001011110101_0 : Blocks := edgeBlocks% "full/vectors/000001011110101-V-0000.bin"
noncomputable def vp000001011110101 : Blocks := vp000001011110101_0
theorem coverp000001011110101 : Covers (-189011639/250000 : ℚ) vp000001011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011110100_0 : Blocks := edgeBlocks% "full/vectors/000001011110100-V-0000.bin"
noncomputable def vp000001011110100 : Blocks := vp000001011110100_0
theorem coverp000001011110100 : Covers (-188761639/250000 : ℚ) vp000001011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101111010_0 : Blocks := edgeBlocks% "full/vectors/00000101111010-V-0000.bin"
noncomputable def vp00000101111010 : Blocks := vp00000101111010_0
private theorem bp000001011110100 : Branch 0 (-188761639/500000 : ℚ) vp00000101111010 := by
  apply branch_left_normalized (c:=vp000001011110100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-188761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-188761639/250000 : ℚ) by norm_num]
  exact coverp000001011110100
private noncomputable def ep000001011110101_0 : Blocks := edgeBlocks% "full/vectors/000001011110101-E-0000.bin"
noncomputable def ep000001011110101 : Blocks := ep000001011110101_0
private theorem idp000001011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101111010.list =
    C ((2:ℤ)^58) * horner X vp000001011110101.list + horner X ep000001011110101.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011110101 : Branch 1 (-188761639/500000 : ℚ) vp00000101111010 := by
  apply branch_checked idp000001011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-188761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-189011639/250000 : ℚ) by norm_num]
  exact coverp000001011110101
theorem coverp00000101111010 : Covers (-188761639/500000 : ℚ) vp00000101111010 := join_branches bp000001011110100 bp000001011110101
private noncomputable def vp0000010111101_0 : Blocks := edgeBlocks% "full/vectors/0000010111101-V-0000.bin"
noncomputable def vp0000010111101 : Blocks := vp0000010111101_0
private theorem bp00000101111010 : Branch 0 (-188761639/1000000 : ℚ) vp0000010111101 := by
  apply branch_left_normalized (c:=vp00000101111010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-188761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-188761639/500000 : ℚ) by norm_num]
  exact coverp00000101111010
private noncomputable def ep00000101111011_0 : Blocks := edgeBlocks% "full/vectors/00000101111011-E-0000.bin"
noncomputable def ep00000101111011 : Blocks := ep00000101111011_0
private theorem idp00000101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010111101.list =
    C ((2:ℤ)^96) * horner X vp00000101111011.list + horner X ep00000101111011.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101111011 : Branch 1 (-188761639/1000000 : ℚ) vp0000010111101 := by
  apply branch_checked idp00000101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-188761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-189261639/500000 : ℚ) by norm_num]
  exact coverp00000101111011
theorem coverp0000010111101 : Covers (-188761639/1000000 : ℚ) vp0000010111101 := join_branches bp00000101111010 bp00000101111011
private noncomputable def vp000001011110011_0 : Blocks := edgeBlocks% "full/vectors/000001011110011-V-0000.bin"
noncomputable def vp000001011110011 : Blocks := vp000001011110011_0
theorem coverp000001011110011 : Covers (-188511639/250000 : ℚ) vp000001011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011110010_0 : Blocks := edgeBlocks% "full/vectors/000001011110010-V-0000.bin"
noncomputable def vp000001011110010 : Blocks := vp000001011110010_0
theorem coverp000001011110010 : Covers (-188261639/250000 : ℚ) vp000001011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101111001_0 : Blocks := edgeBlocks% "full/vectors/00000101111001-V-0000.bin"
noncomputable def vp00000101111001 : Blocks := vp00000101111001_0
private theorem bp000001011110010 : Branch 0 (-188261639/500000 : ℚ) vp00000101111001 := by
  apply branch_left_normalized (c:=vp000001011110010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-188261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-188261639/250000 : ℚ) by norm_num]
  exact coverp000001011110010
private noncomputable def ep000001011110011_0 : Blocks := edgeBlocks% "full/vectors/000001011110011-E-0000.bin"
noncomputable def ep000001011110011 : Blocks := ep000001011110011_0
private theorem idp000001011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101111001.list =
    C ((2:ℤ)^58) * horner X vp000001011110011.list + horner X ep000001011110011.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011110011 : Branch 1 (-188261639/500000 : ℚ) vp00000101111001 := by
  apply branch_checked idp000001011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-188261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-188511639/250000 : ℚ) by norm_num]
  exact coverp000001011110011
theorem coverp00000101111001 : Covers (-188261639/500000 : ℚ) vp00000101111001 := join_branches bp000001011110010 bp000001011110011
private noncomputable def vp000001011110001_0 : Blocks := edgeBlocks% "full/vectors/000001011110001-V-0000.bin"
noncomputable def vp000001011110001 : Blocks := vp000001011110001_0
theorem coverp000001011110001 : Covers (-188011639/250000 : ℚ) vp000001011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011110000_0 : Blocks := edgeBlocks% "full/vectors/000001011110000-V-0000.bin"
noncomputable def vp000001011110000 : Blocks := vp000001011110000_0
theorem coverp000001011110000 : Covers (-187761639/250000 : ℚ) vp000001011110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101111000_0 : Blocks := edgeBlocks% "full/vectors/00000101111000-V-0000.bin"
noncomputable def vp00000101111000 : Blocks := vp00000101111000_0
private theorem bp000001011110000 : Branch 0 (-187761639/500000 : ℚ) vp00000101111000 := by
  apply branch_left_normalized (c:=vp000001011110000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-187761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-187761639/250000 : ℚ) by norm_num]
  exact coverp000001011110000
private noncomputable def ep000001011110001_0 : Blocks := edgeBlocks% "full/vectors/000001011110001-E-0000.bin"
noncomputable def ep000001011110001 : Blocks := ep000001011110001_0
private theorem idp000001011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101111000.list =
    C ((2:ℤ)^58) * horner X vp000001011110001.list + horner X ep000001011110001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011110001 : Branch 1 (-187761639/500000 : ℚ) vp00000101111000 := by
  apply branch_checked idp000001011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-187761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-188011639/250000 : ℚ) by norm_num]
  exact coverp000001011110001
theorem coverp00000101111000 : Covers (-187761639/500000 : ℚ) vp00000101111000 := join_branches bp000001011110000 bp000001011110001
private noncomputable def vp0000010111100_0 : Blocks := edgeBlocks% "full/vectors/0000010111100-V-0000.bin"
noncomputable def vp0000010111100 : Blocks := vp0000010111100_0
private theorem bp00000101111000 : Branch 0 (-187761639/1000000 : ℚ) vp0000010111100 := by
  apply branch_left_normalized (c:=vp00000101111000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-187761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-187761639/500000 : ℚ) by norm_num]
  exact coverp00000101111000
private noncomputable def ep00000101111001_0 : Blocks := edgeBlocks% "full/vectors/00000101111001-E-0000.bin"
noncomputable def ep00000101111001 : Blocks := ep00000101111001_0
private theorem idp00000101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010111100.list =
    C ((2:ℤ)^96) * horner X vp00000101111001.list + horner X ep00000101111001.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101111001 : Branch 1 (-187761639/1000000 : ℚ) vp0000010111100 := by
  apply branch_checked idp00000101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-187761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-188261639/500000 : ℚ) by norm_num]
  exact coverp00000101111001
theorem coverp0000010111100 : Covers (-187761639/1000000 : ℚ) vp0000010111100 := join_branches bp00000101111000 bp00000101111001
private noncomputable def vp000001011110_0 : Blocks := edgeBlocks% "full/vectors/000001011110-V-0000.bin"
private noncomputable def vp000001011110_1 : Blocks := edgeBlocks% "full/vectors/000001011110-V-0001.bin"
noncomputable def vp000001011110 : Blocks := (Blocks.join vp000001011110_0 vp000001011110_1)
private theorem bp0000010111100 : Branch 0 (-187761639/2000000 : ℚ) vp000001011110 := by
  apply branch_left_normalized (c:=vp0000010111100) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-187761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-187761639/1000000 : ℚ) by norm_num]
  exact coverp0000010111100
private noncomputable def ep0000010111101_0 : Blocks := edgeBlocks% "full/vectors/0000010111101-E-0000.bin"
private noncomputable def ep0000010111101_1 : Blocks := edgeBlocks% "full/vectors/0000010111101-E-0001.bin"
noncomputable def ep0000010111101 : Blocks := (Blocks.join ep0000010111101_0 ep0000010111101_1)
private theorem idp0000010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001011110.list =
    C ((2:ℤ)^172) * horner X vp0000010111101.list + horner X ep0000010111101.list := by
  exact edge_identity (B := (2:ℤ)^345) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010111101 : Branch 1 (-187761639/2000000 : ℚ) vp000001011110 := by
  apply branch_checked idp0000010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-187761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-188761639/1000000 : ℚ) by norm_num]
  exact coverp0000010111101
theorem coverp000001011110 : Covers (-187761639/2000000 : ℚ) vp000001011110 := join_branches bp0000010111100 bp0000010111101
private noncomputable def vp00000101111_0 : Blocks := edgeBlocks% "full/vectors/00000101111-V-0000.bin"
private noncomputable def vp00000101111_1 : Blocks := edgeBlocks% "full/vectors/00000101111-V-0001.bin"
private noncomputable def vp00000101111_2 : Blocks := edgeBlocks% "full/vectors/00000101111-V-0002.bin"
noncomputable def vp00000101111 : Blocks := (Blocks.join vp00000101111_0 (Blocks.join vp00000101111_1 vp00000101111_2))
private theorem bp000001011110 : Branch 0 (-187761639/4000000 : ℚ) vp00000101111 := by
  apply branch_left_normalized (c:=vp000001011110) (k:=0) (m:=166) (by decide +kernel)
  rw [show 2*(-187761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-187761639/2000000 : ℚ) by norm_num]
  exact coverp000001011110
private noncomputable def ep000001011111_0 : Blocks := edgeBlocks% "full/vectors/000001011111-E-0000.bin"
private noncomputable def ep000001011111_1 : Blocks := edgeBlocks% "full/vectors/000001011111-E-0001.bin"
private noncomputable def ep000001011111_2 : Blocks := edgeBlocks% "full/vectors/000001011111-E-0002.bin"
noncomputable def ep000001011111 : Blocks := (Blocks.join ep000001011111_0 (Blocks.join ep000001011111_1 ep000001011111_2))
private theorem idp000001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101111.list =
    C ((2:ℤ)^321) * horner X vp000001011111.list + horner X ep000001011111.list := by
  exact edge_identity (B := (2:ℤ)^564) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011111 : Branch 1 (-187761639/4000000 : ℚ) vp00000101111 := by
  apply branch_checked idp000001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-187761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-189761639/2000000 : ℚ) by norm_num]
  exact coverp000001011111
theorem coverp00000101111 : Covers (-187761639/4000000 : ℚ) vp00000101111 := join_branches bp000001011110 bp000001011111
private noncomputable def vp000001011101111_0 : Blocks := edgeBlocks% "full/vectors/000001011101111-V-0000.bin"
noncomputable def vp000001011101111 : Blocks := vp000001011101111_0
theorem coverp000001011101111 : Covers (-187511639/250000 : ℚ) vp000001011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011101110_0 : Blocks := edgeBlocks% "full/vectors/000001011101110-V-0000.bin"
noncomputable def vp000001011101110 : Blocks := vp000001011101110_0
theorem coverp000001011101110 : Covers (-187261639/250000 : ℚ) vp000001011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101110111_0 : Blocks := edgeBlocks% "full/vectors/00000101110111-V-0000.bin"
noncomputable def vp00000101110111 : Blocks := vp00000101110111_0
private theorem bp000001011101110 : Branch 0 (-187261639/500000 : ℚ) vp00000101110111 := by
  apply branch_left_normalized (c:=vp000001011101110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-187261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-187261639/250000 : ℚ) by norm_num]
  exact coverp000001011101110
private noncomputable def ep000001011101111_0 : Blocks := edgeBlocks% "full/vectors/000001011101111-E-0000.bin"
noncomputable def ep000001011101111 : Blocks := ep000001011101111_0
private theorem idp000001011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101110111.list =
    C ((2:ℤ)^58) * horner X vp000001011101111.list + horner X ep000001011101111.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011101111 : Branch 1 (-187261639/500000 : ℚ) vp00000101110111 := by
  apply branch_checked idp000001011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-187261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-187511639/250000 : ℚ) by norm_num]
  exact coverp000001011101111
theorem coverp00000101110111 : Covers (-187261639/500000 : ℚ) vp00000101110111 := join_branches bp000001011101110 bp000001011101111
private noncomputable def vp000001011101101_0 : Blocks := edgeBlocks% "full/vectors/000001011101101-V-0000.bin"
noncomputable def vp000001011101101 : Blocks := vp000001011101101_0
theorem coverp000001011101101 : Covers (-187011639/250000 : ℚ) vp000001011101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011101100_0 : Blocks := edgeBlocks% "full/vectors/000001011101100-V-0000.bin"
noncomputable def vp000001011101100 : Blocks := vp000001011101100_0
theorem coverp000001011101100 : Covers (-186761639/250000 : ℚ) vp000001011101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101110110_0 : Blocks := edgeBlocks% "full/vectors/00000101110110-V-0000.bin"
noncomputable def vp00000101110110 : Blocks := vp00000101110110_0
private theorem bp000001011101100 : Branch 0 (-186761639/500000 : ℚ) vp00000101110110 := by
  apply branch_left_normalized (c:=vp000001011101100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-186761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-186761639/250000 : ℚ) by norm_num]
  exact coverp000001011101100
private noncomputable def ep000001011101101_0 : Blocks := edgeBlocks% "full/vectors/000001011101101-E-0000.bin"
noncomputable def ep000001011101101 : Blocks := ep000001011101101_0
private theorem idp000001011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101110110.list =
    C ((2:ℤ)^58) * horner X vp000001011101101.list + horner X ep000001011101101.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011101101 : Branch 1 (-186761639/500000 : ℚ) vp00000101110110 := by
  apply branch_checked idp000001011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-186761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-187011639/250000 : ℚ) by norm_num]
  exact coverp000001011101101
theorem coverp00000101110110 : Covers (-186761639/500000 : ℚ) vp00000101110110 := join_branches bp000001011101100 bp000001011101101
private noncomputable def vp0000010111011_0 : Blocks := edgeBlocks% "full/vectors/0000010111011-V-0000.bin"
noncomputable def vp0000010111011 : Blocks := vp0000010111011_0
private theorem bp00000101110110 : Branch 0 (-186761639/1000000 : ℚ) vp0000010111011 := by
  apply branch_left_normalized (c:=vp00000101110110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-186761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-186761639/500000 : ℚ) by norm_num]
  exact coverp00000101110110
private noncomputable def ep00000101110111_0 : Blocks := edgeBlocks% "full/vectors/00000101110111-E-0000.bin"
noncomputable def ep00000101110111 : Blocks := ep00000101110111_0
private theorem idp00000101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010111011.list =
    C ((2:ℤ)^96) * horner X vp00000101110111.list + horner X ep00000101110111.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101110111 : Branch 1 (-186761639/1000000 : ℚ) vp0000010111011 := by
  apply branch_checked idp00000101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-186761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-187261639/500000 : ℚ) by norm_num]
  exact coverp00000101110111
theorem coverp0000010111011 : Covers (-186761639/1000000 : ℚ) vp0000010111011 := join_branches bp00000101110110 bp00000101110111
private noncomputable def vp000001011101011_0 : Blocks := edgeBlocks% "full/vectors/000001011101011-V-0000.bin"
noncomputable def vp000001011101011 : Blocks := vp000001011101011_0
theorem coverp000001011101011 : Covers (-186511639/250000 : ℚ) vp000001011101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011101010_0 : Blocks := edgeBlocks% "full/vectors/000001011101010-V-0000.bin"
noncomputable def vp000001011101010 : Blocks := vp000001011101010_0
theorem coverp000001011101010 : Covers (-186261639/250000 : ℚ) vp000001011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101110101_0 : Blocks := edgeBlocks% "full/vectors/00000101110101-V-0000.bin"
noncomputable def vp00000101110101 : Blocks := vp00000101110101_0
private theorem bp000001011101010 : Branch 0 (-186261639/500000 : ℚ) vp00000101110101 := by
  apply branch_left_normalized (c:=vp000001011101010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-186261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-186261639/250000 : ℚ) by norm_num]
  exact coverp000001011101010
private noncomputable def ep000001011101011_0 : Blocks := edgeBlocks% "full/vectors/000001011101011-E-0000.bin"
noncomputable def ep000001011101011 : Blocks := ep000001011101011_0
private theorem idp000001011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101110101.list =
    C ((2:ℤ)^57) * horner X vp000001011101011.list + horner X ep000001011101011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011101011 : Branch 1 (-186261639/500000 : ℚ) vp00000101110101 := by
  apply branch_checked idp000001011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-186261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-186511639/250000 : ℚ) by norm_num]
  exact coverp000001011101011
theorem coverp00000101110101 : Covers (-186261639/500000 : ℚ) vp00000101110101 := join_branches bp000001011101010 bp000001011101011
private noncomputable def vp000001011101001_0 : Blocks := edgeBlocks% "full/vectors/000001011101001-V-0000.bin"
noncomputable def vp000001011101001 : Blocks := vp000001011101001_0
theorem coverp000001011101001 : Covers (-186011639/250000 : ℚ) vp000001011101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011101000_0 : Blocks := edgeBlocks% "full/vectors/000001011101000-V-0000.bin"
noncomputable def vp000001011101000 : Blocks := vp000001011101000_0
theorem coverp000001011101000 : Covers (-185761639/250000 : ℚ) vp000001011101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101110100_0 : Blocks := edgeBlocks% "full/vectors/00000101110100-V-0000.bin"
noncomputable def vp00000101110100 : Blocks := vp00000101110100_0
private theorem bp000001011101000 : Branch 0 (-185761639/500000 : ℚ) vp00000101110100 := by
  apply branch_left_normalized (c:=vp000001011101000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-185761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-185761639/250000 : ℚ) by norm_num]
  exact coverp000001011101000
private noncomputable def ep000001011101001_0 : Blocks := edgeBlocks% "full/vectors/000001011101001-E-0000.bin"
noncomputable def ep000001011101001 : Blocks := ep000001011101001_0
private theorem idp000001011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101110100.list =
    C ((2:ℤ)^59) * horner X vp000001011101001.list + horner X ep000001011101001.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011101001 : Branch 1 (-185761639/500000 : ℚ) vp00000101110100 := by
  apply branch_checked idp000001011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-185761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-186011639/250000 : ℚ) by norm_num]
  exact coverp000001011101001
theorem coverp00000101110100 : Covers (-185761639/500000 : ℚ) vp00000101110100 := join_branches bp000001011101000 bp000001011101001
private noncomputable def vp0000010111010_0 : Blocks := edgeBlocks% "full/vectors/0000010111010-V-0000.bin"
noncomputable def vp0000010111010 : Blocks := vp0000010111010_0
private theorem bp00000101110100 : Branch 0 (-185761639/1000000 : ℚ) vp0000010111010 := by
  apply branch_left_normalized (c:=vp00000101110100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-185761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-185761639/500000 : ℚ) by norm_num]
  exact coverp00000101110100
private noncomputable def ep00000101110101_0 : Blocks := edgeBlocks% "full/vectors/00000101110101-E-0000.bin"
noncomputable def ep00000101110101 : Blocks := ep00000101110101_0
private theorem idp00000101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010111010.list =
    C ((2:ℤ)^99) * horner X vp00000101110101.list + horner X ep00000101110101.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101110101 : Branch 1 (-185761639/1000000 : ℚ) vp0000010111010 := by
  apply branch_checked idp00000101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-185761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-186261639/500000 : ℚ) by norm_num]
  exact coverp00000101110101
theorem coverp0000010111010 : Covers (-185761639/1000000 : ℚ) vp0000010111010 := join_branches bp00000101110100 bp00000101110101
private noncomputable def vp000001011101_0 : Blocks := edgeBlocks% "full/vectors/000001011101-V-0000.bin"
private noncomputable def vp000001011101_1 : Blocks := edgeBlocks% "full/vectors/000001011101-V-0001.bin"
noncomputable def vp000001011101 : Blocks := (Blocks.join vp000001011101_0 vp000001011101_1)
private theorem bp0000010111010 : Branch 0 (-185761639/2000000 : ℚ) vp000001011101 := by
  apply branch_left_normalized (c:=vp0000010111010) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-185761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-185761639/1000000 : ℚ) by norm_num]
  exact coverp0000010111010
private noncomputable def ep0000010111011_0 : Blocks := edgeBlocks% "full/vectors/0000010111011-E-0000.bin"
private noncomputable def ep0000010111011_1 : Blocks := edgeBlocks% "full/vectors/0000010111011-E-0001.bin"
noncomputable def ep0000010111011 : Blocks := (Blocks.join ep0000010111011_0 ep0000010111011_1)
private theorem idp0000010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001011101.list =
    C ((2:ℤ)^175) * horner X vp0000010111011.list + horner X ep0000010111011.list := by
  exact edge_identity (B := (2:ℤ)^347) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010111011 : Branch 1 (-185761639/2000000 : ℚ) vp000001011101 := by
  apply branch_checked idp0000010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-185761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-186761639/1000000 : ℚ) by norm_num]
  exact coverp0000010111011
theorem coverp000001011101 : Covers (-185761639/2000000 : ℚ) vp000001011101 := join_branches bp0000010111010 bp0000010111011
private noncomputable def vp000001011100111_0 : Blocks := edgeBlocks% "full/vectors/000001011100111-V-0000.bin"
noncomputable def vp000001011100111 : Blocks := vp000001011100111_0
theorem coverp000001011100111 : Covers (-185511639/250000 : ℚ) vp000001011100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011100110_0 : Blocks := edgeBlocks% "full/vectors/000001011100110-V-0000.bin"
noncomputable def vp000001011100110 : Blocks := vp000001011100110_0
theorem coverp000001011100110 : Covers (-185261639/250000 : ℚ) vp000001011100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101110011_0 : Blocks := edgeBlocks% "full/vectors/00000101110011-V-0000.bin"
noncomputable def vp00000101110011 : Blocks := vp00000101110011_0
private theorem bp000001011100110 : Branch 0 (-185261639/500000 : ℚ) vp00000101110011 := by
  apply branch_left_normalized (c:=vp000001011100110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-185261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-185261639/250000 : ℚ) by norm_num]
  exact coverp000001011100110
private noncomputable def ep000001011100111_0 : Blocks := edgeBlocks% "full/vectors/000001011100111-E-0000.bin"
noncomputable def ep000001011100111 : Blocks := ep000001011100111_0
private theorem idp000001011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101110011.list =
    C ((2:ℤ)^59) * horner X vp000001011100111.list + horner X ep000001011100111.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011100111 : Branch 1 (-185261639/500000 : ℚ) vp00000101110011 := by
  apply branch_checked idp000001011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-185261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-185511639/250000 : ℚ) by norm_num]
  exact coverp000001011100111
theorem coverp00000101110011 : Covers (-185261639/500000 : ℚ) vp00000101110011 := join_branches bp000001011100110 bp000001011100111
private noncomputable def vp000001011100101_0 : Blocks := edgeBlocks% "full/vectors/000001011100101-V-0000.bin"
noncomputable def vp000001011100101 : Blocks := vp000001011100101_0
theorem coverp000001011100101 : Covers (-185011639/250000 : ℚ) vp000001011100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011100100_0 : Blocks := edgeBlocks% "full/vectors/000001011100100-V-0000.bin"
noncomputable def vp000001011100100 : Blocks := vp000001011100100_0
theorem coverp000001011100100 : Covers (-184761639/250000 : ℚ) vp000001011100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101110010_0 : Blocks := edgeBlocks% "full/vectors/00000101110010-V-0000.bin"
noncomputable def vp00000101110010 : Blocks := vp00000101110010_0
private theorem bp000001011100100 : Branch 0 (-184761639/500000 : ℚ) vp00000101110010 := by
  apply branch_left_normalized (c:=vp000001011100100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-184761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-184761639/250000 : ℚ) by norm_num]
  exact coverp000001011100100
private noncomputable def ep000001011100101_0 : Blocks := edgeBlocks% "full/vectors/000001011100101-E-0000.bin"
noncomputable def ep000001011100101 : Blocks := ep000001011100101_0
private theorem idp000001011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101110010.list =
    C ((2:ℤ)^58) * horner X vp000001011100101.list + horner X ep000001011100101.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011100101 : Branch 1 (-184761639/500000 : ℚ) vp00000101110010 := by
  apply branch_checked idp000001011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-184761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-185011639/250000 : ℚ) by norm_num]
  exact coverp000001011100101
theorem coverp00000101110010 : Covers (-184761639/500000 : ℚ) vp00000101110010 := join_branches bp000001011100100 bp000001011100101
private noncomputable def vp0000010111001_0 : Blocks := edgeBlocks% "full/vectors/0000010111001-V-0000.bin"
noncomputable def vp0000010111001 : Blocks := vp0000010111001_0
private theorem bp00000101110010 : Branch 0 (-184761639/1000000 : ℚ) vp0000010111001 := by
  apply branch_left_normalized (c:=vp00000101110010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-184761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-184761639/500000 : ℚ) by norm_num]
  exact coverp00000101110010
private noncomputable def ep00000101110011_0 : Blocks := edgeBlocks% "full/vectors/00000101110011-E-0000.bin"
noncomputable def ep00000101110011 : Blocks := ep00000101110011_0
private theorem idp00000101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010111001.list =
    C ((2:ℤ)^97) * horner X vp00000101110011.list + horner X ep00000101110011.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101110011 : Branch 1 (-184761639/1000000 : ℚ) vp0000010111001 := by
  apply branch_checked idp00000101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-184761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-185261639/500000 : ℚ) by norm_num]
  exact coverp00000101110011
theorem coverp0000010111001 : Covers (-184761639/1000000 : ℚ) vp0000010111001 := join_branches bp00000101110010 bp00000101110011
private noncomputable def vp000001011100011_0 : Blocks := edgeBlocks% "full/vectors/000001011100011-V-0000.bin"
noncomputable def vp000001011100011 : Blocks := vp000001011100011_0
theorem coverp000001011100011 : Covers (-184511639/250000 : ℚ) vp000001011100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011100010_0 : Blocks := edgeBlocks% "full/vectors/000001011100010-V-0000.bin"
noncomputable def vp000001011100010 : Blocks := vp000001011100010_0
theorem coverp000001011100010 : Covers (-184261639/250000 : ℚ) vp000001011100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101110001_0 : Blocks := edgeBlocks% "full/vectors/00000101110001-V-0000.bin"
noncomputable def vp00000101110001 : Blocks := vp00000101110001_0
private theorem bp000001011100010 : Branch 0 (-184261639/500000 : ℚ) vp00000101110001 := by
  apply branch_left_normalized (c:=vp000001011100010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-184261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-184261639/250000 : ℚ) by norm_num]
  exact coverp000001011100010
private noncomputable def ep000001011100011_0 : Blocks := edgeBlocks% "full/vectors/000001011100011-E-0000.bin"
noncomputable def ep000001011100011 : Blocks := ep000001011100011_0
private theorem idp000001011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101110001.list =
    C ((2:ℤ)^58) * horner X vp000001011100011.list + horner X ep000001011100011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011100011 : Branch 1 (-184261639/500000 : ℚ) vp00000101110001 := by
  apply branch_checked idp000001011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-184261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-184511639/250000 : ℚ) by norm_num]
  exact coverp000001011100011
theorem coverp00000101110001 : Covers (-184261639/500000 : ℚ) vp00000101110001 := join_branches bp000001011100010 bp000001011100011
private noncomputable def vp000001011100001_0 : Blocks := edgeBlocks% "full/vectors/000001011100001-V-0000.bin"
noncomputable def vp000001011100001 : Blocks := vp000001011100001_0
theorem coverp000001011100001 : Covers (-184011639/250000 : ℚ) vp000001011100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011100000_0 : Blocks := edgeBlocks% "full/vectors/000001011100000-V-0000.bin"
noncomputable def vp000001011100000 : Blocks := vp000001011100000_0
theorem coverp000001011100000 : Covers (-183761639/250000 : ℚ) vp000001011100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101110000_0 : Blocks := edgeBlocks% "full/vectors/00000101110000-V-0000.bin"
noncomputable def vp00000101110000 : Blocks := vp00000101110000_0
private theorem bp000001011100000 : Branch 0 (-183761639/500000 : ℚ) vp00000101110000 := by
  apply branch_left_normalized (c:=vp000001011100000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-183761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-183761639/250000 : ℚ) by norm_num]
  exact coverp000001011100000
private noncomputable def ep000001011100001_0 : Blocks := edgeBlocks% "full/vectors/000001011100001-E-0000.bin"
noncomputable def ep000001011100001 : Blocks := ep000001011100001_0
private theorem idp000001011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101110000.list =
    C ((2:ℤ)^58) * horner X vp000001011100001.list + horner X ep000001011100001.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011100001 : Branch 1 (-183761639/500000 : ℚ) vp00000101110000 := by
  apply branch_checked idp000001011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-183761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-184011639/250000 : ℚ) by norm_num]
  exact coverp000001011100001
theorem coverp00000101110000 : Covers (-183761639/500000 : ℚ) vp00000101110000 := join_branches bp000001011100000 bp000001011100001
private noncomputable def vp0000010111000_0 : Blocks := edgeBlocks% "full/vectors/0000010111000-V-0000.bin"
noncomputable def vp0000010111000 : Blocks := vp0000010111000_0
private theorem bp00000101110000 : Branch 0 (-183761639/1000000 : ℚ) vp0000010111000 := by
  apply branch_left_normalized (c:=vp00000101110000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-183761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-183761639/500000 : ℚ) by norm_num]
  exact coverp00000101110000
private noncomputable def ep00000101110001_0 : Blocks := edgeBlocks% "full/vectors/00000101110001-E-0000.bin"
noncomputable def ep00000101110001 : Blocks := ep00000101110001_0
private theorem idp00000101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010111000.list =
    C ((2:ℤ)^98) * horner X vp00000101110001.list + horner X ep00000101110001.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101110001 : Branch 1 (-183761639/1000000 : ℚ) vp0000010111000 := by
  apply branch_checked idp00000101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-183761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-184261639/500000 : ℚ) by norm_num]
  exact coverp00000101110001
theorem coverp0000010111000 : Covers (-183761639/1000000 : ℚ) vp0000010111000 := join_branches bp00000101110000 bp00000101110001
private noncomputable def vp000001011100_0 : Blocks := edgeBlocks% "full/vectors/000001011100-V-0000.bin"
private noncomputable def vp000001011100_1 : Blocks := edgeBlocks% "full/vectors/000001011100-V-0001.bin"
noncomputable def vp000001011100 : Blocks := (Blocks.join vp000001011100_0 vp000001011100_1)
private theorem bp0000010111000 : Branch 0 (-183761639/2000000 : ℚ) vp000001011100 := by
  apply branch_left_normalized (c:=vp0000010111000) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-183761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-183761639/1000000 : ℚ) by norm_num]
  exact coverp0000010111000
private noncomputable def ep0000010111001_0 : Blocks := edgeBlocks% "full/vectors/0000010111001-E-0000.bin"
private noncomputable def ep0000010111001_1 : Blocks := edgeBlocks% "full/vectors/0000010111001-E-0001.bin"
noncomputable def ep0000010111001 : Blocks := (Blocks.join ep0000010111001_0 ep0000010111001_1)
private theorem idp0000010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001011100.list =
    C ((2:ℤ)^173) * horner X vp0000010111001.list + horner X ep0000010111001.list := by
  exact edge_identity (B := (2:ℤ)^346) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010111001 : Branch 1 (-183761639/2000000 : ℚ) vp000001011100 := by
  apply branch_checked idp0000010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-183761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-184761639/1000000 : ℚ) by norm_num]
  exact coverp0000010111001
theorem coverp000001011100 : Covers (-183761639/2000000 : ℚ) vp000001011100 := join_branches bp0000010111000 bp0000010111001
private noncomputable def vp00000101110_0 : Blocks := edgeBlocks% "full/vectors/00000101110-V-0000.bin"
private noncomputable def vp00000101110_1 : Blocks := edgeBlocks% "full/vectors/00000101110-V-0001.bin"
private noncomputable def vp00000101110_2 : Blocks := edgeBlocks% "full/vectors/00000101110-V-0002.bin"
noncomputable def vp00000101110 : Blocks := (Blocks.join vp00000101110_0 (Blocks.join vp00000101110_1 vp00000101110_2))
private theorem bp000001011100 : Branch 0 (-183761639/4000000 : ℚ) vp00000101110 := by
  apply branch_left_normalized (c:=vp000001011100) (k:=0) (m:=167) (by decide +kernel)
  rw [show 2*(-183761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-183761639/2000000 : ℚ) by norm_num]
  exact coverp000001011100
private noncomputable def ep000001011101_0 : Blocks := edgeBlocks% "full/vectors/000001011101-E-0000.bin"
private noncomputable def ep000001011101_1 : Blocks := edgeBlocks% "full/vectors/000001011101-E-0001.bin"
private noncomputable def ep000001011101_2 : Blocks := edgeBlocks% "full/vectors/000001011101-E-0002.bin"
noncomputable def ep000001011101 : Blocks := (Blocks.join ep000001011101_0 (Blocks.join ep000001011101_1 ep000001011101_2))
private theorem idp000001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101110.list =
    C ((2:ℤ)^323) * horner X vp000001011101.list + horner X ep000001011101.list := by
  exact edge_identity (B := (2:ℤ)^568) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011101 : Branch 1 (-183761639/4000000 : ℚ) vp00000101110 := by
  apply branch_checked idp000001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-183761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-185761639/2000000 : ℚ) by norm_num]
  exact coverp000001011101
theorem coverp00000101110 : Covers (-183761639/4000000 : ℚ) vp00000101110 := join_branches bp000001011100 bp000001011101
private noncomputable def vp0000010111_0 : Blocks := edgeBlocks% "full/vectors/0000010111-V-0000.bin"
private noncomputable def vp0000010111_1 : Blocks := edgeBlocks% "full/vectors/0000010111-V-0001.bin"
private noncomputable def vp0000010111_2 : Blocks := edgeBlocks% "full/vectors/0000010111-V-0002.bin"
private noncomputable def vp0000010111_3 : Blocks := edgeBlocks% "full/vectors/0000010111-V-0003.bin"
private noncomputable def vp0000010111_4 : Blocks := edgeBlocks% "full/vectors/0000010111-V-0004.bin"
noncomputable def vp0000010111 : Blocks := (Blocks.join (Blocks.join vp0000010111_0 vp0000010111_1) (Blocks.join vp0000010111_2 (Blocks.join vp0000010111_3 vp0000010111_4)))
private theorem bp00000101110 : Branch 0 (-183761639/8000000 : ℚ) vp0000010111 := by
  apply branch_left_normalized (c:=vp00000101110) (k:=0) (m:=312) (by decide +kernel)
  rw [show 2*(-183761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-183761639/4000000 : ℚ) by norm_num]
  exact coverp00000101110
private noncomputable def ep00000101111_0 : Blocks := edgeBlocks% "full/vectors/00000101111-E-0000.bin"
private noncomputable def ep00000101111_1 : Blocks := edgeBlocks% "full/vectors/00000101111-E-0001.bin"
private noncomputable def ep00000101111_2 : Blocks := edgeBlocks% "full/vectors/00000101111-E-0002.bin"
private noncomputable def ep00000101111_3 : Blocks := edgeBlocks% "full/vectors/00000101111-E-0003.bin"
private noncomputable def ep00000101111_4 : Blocks := edgeBlocks% "full/vectors/00000101111-E-0004.bin"
noncomputable def ep00000101111 : Blocks := (Blocks.join (Blocks.join ep00000101111_0 ep00000101111_1) (Blocks.join ep00000101111_2 (Blocks.join ep00000101111_3 ep00000101111_4)))
private theorem idp00000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010111.list =
    C ((2:ℤ)^622) * horner X vp00000101111.list + horner X ep00000101111.list := by
  exact edge_identity (B := (2:ℤ)^1007) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101111 : Branch 1 (-183761639/8000000 : ℚ) vp0000010111 := by
  apply branch_checked idp00000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-183761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-187761639/4000000 : ℚ) by norm_num]
  exact coverp00000101111
theorem coverp0000010111 : Covers (-183761639/8000000 : ℚ) vp0000010111 := join_branches bp00000101110 bp00000101111
private noncomputable def vp000001011011111_0 : Blocks := edgeBlocks% "full/vectors/000001011011111-V-0000.bin"
noncomputable def vp000001011011111 : Blocks := vp000001011011111_0
theorem coverp000001011011111 : Covers (-183511639/250000 : ℚ) vp000001011011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011011110_0 : Blocks := edgeBlocks% "full/vectors/000001011011110-V-0000.bin"
noncomputable def vp000001011011110 : Blocks := vp000001011011110_0
theorem coverp000001011011110 : Covers (-183261639/250000 : ℚ) vp000001011011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101101111_0 : Blocks := edgeBlocks% "full/vectors/00000101101111-V-0000.bin"
noncomputable def vp00000101101111 : Blocks := vp00000101101111_0
private theorem bp000001011011110 : Branch 0 (-183261639/500000 : ℚ) vp00000101101111 := by
  apply branch_left_normalized (c:=vp000001011011110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-183261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-183261639/250000 : ℚ) by norm_num]
  exact coverp000001011011110
private noncomputable def ep000001011011111_0 : Blocks := edgeBlocks% "full/vectors/000001011011111-E-0000.bin"
noncomputable def ep000001011011111 : Blocks := ep000001011011111_0
private theorem idp000001011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101101111.list =
    C ((2:ℤ)^57) * horner X vp000001011011111.list + horner X ep000001011011111.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011011111 : Branch 1 (-183261639/500000 : ℚ) vp00000101101111 := by
  apply branch_checked idp000001011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-183261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-183511639/250000 : ℚ) by norm_num]
  exact coverp000001011011111
theorem coverp00000101101111 : Covers (-183261639/500000 : ℚ) vp00000101101111 := join_branches bp000001011011110 bp000001011011111
private noncomputable def vp000001011011101_0 : Blocks := edgeBlocks% "full/vectors/000001011011101-V-0000.bin"
noncomputable def vp000001011011101 : Blocks := vp000001011011101_0
theorem coverp000001011011101 : Covers (-183011639/250000 : ℚ) vp000001011011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011011100_0 : Blocks := edgeBlocks% "full/vectors/000001011011100-V-0000.bin"
noncomputable def vp000001011011100 : Blocks := vp000001011011100_0
theorem coverp000001011011100 : Covers (-182761639/250000 : ℚ) vp000001011011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101101110_0 : Blocks := edgeBlocks% "full/vectors/00000101101110-V-0000.bin"
noncomputable def vp00000101101110 : Blocks := vp00000101101110_0
private theorem bp000001011011100 : Branch 0 (-182761639/500000 : ℚ) vp00000101101110 := by
  apply branch_left_normalized (c:=vp000001011011100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-182761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-182761639/250000 : ℚ) by norm_num]
  exact coverp000001011011100
private noncomputable def ep000001011011101_0 : Blocks := edgeBlocks% "full/vectors/000001011011101-E-0000.bin"
noncomputable def ep000001011011101 : Blocks := ep000001011011101_0
private theorem idp000001011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101101110.list =
    C ((2:ℤ)^58) * horner X vp000001011011101.list + horner X ep000001011011101.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011011101 : Branch 1 (-182761639/500000 : ℚ) vp00000101101110 := by
  apply branch_checked idp000001011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-182761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-183011639/250000 : ℚ) by norm_num]
  exact coverp000001011011101
theorem coverp00000101101110 : Covers (-182761639/500000 : ℚ) vp00000101101110 := join_branches bp000001011011100 bp000001011011101
private noncomputable def vp0000010110111_0 : Blocks := edgeBlocks% "full/vectors/0000010110111-V-0000.bin"
noncomputable def vp0000010110111 : Blocks := vp0000010110111_0
private theorem bp00000101101110 : Branch 0 (-182761639/1000000 : ℚ) vp0000010110111 := by
  apply branch_left_normalized (c:=vp00000101101110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-182761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-182761639/500000 : ℚ) by norm_num]
  exact coverp00000101101110
private noncomputable def ep00000101101111_0 : Blocks := edgeBlocks% "full/vectors/00000101101111-E-0000.bin"
noncomputable def ep00000101101111 : Blocks := ep00000101101111_0
private theorem idp00000101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010110111.list =
    C ((2:ℤ)^97) * horner X vp00000101101111.list + horner X ep00000101101111.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101101111 : Branch 1 (-182761639/1000000 : ℚ) vp0000010110111 := by
  apply branch_checked idp00000101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-182761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-183261639/500000 : ℚ) by norm_num]
  exact coverp00000101101111
theorem coverp0000010110111 : Covers (-182761639/1000000 : ℚ) vp0000010110111 := join_branches bp00000101101110 bp00000101101111
private noncomputable def vp000001011011011_0 : Blocks := edgeBlocks% "full/vectors/000001011011011-V-0000.bin"
noncomputable def vp000001011011011 : Blocks := vp000001011011011_0
theorem coverp000001011011011 : Covers (-182511639/250000 : ℚ) vp000001011011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011011010_0 : Blocks := edgeBlocks% "full/vectors/000001011011010-V-0000.bin"
noncomputable def vp000001011011010 : Blocks := vp000001011011010_0
theorem coverp000001011011010 : Covers (-182261639/250000 : ℚ) vp000001011011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101101101_0 : Blocks := edgeBlocks% "full/vectors/00000101101101-V-0000.bin"
noncomputable def vp00000101101101 : Blocks := vp00000101101101_0
private theorem bp000001011011010 : Branch 0 (-182261639/500000 : ℚ) vp00000101101101 := by
  apply branch_left_normalized (c:=vp000001011011010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-182261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-182261639/250000 : ℚ) by norm_num]
  exact coverp000001011011010
private noncomputable def ep000001011011011_0 : Blocks := edgeBlocks% "full/vectors/000001011011011-E-0000.bin"
noncomputable def ep000001011011011 : Blocks := ep000001011011011_0
private theorem idp000001011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101101101.list =
    C ((2:ℤ)^59) * horner X vp000001011011011.list + horner X ep000001011011011.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011011011 : Branch 1 (-182261639/500000 : ℚ) vp00000101101101 := by
  apply branch_checked idp000001011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-182261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-182511639/250000 : ℚ) by norm_num]
  exact coverp000001011011011
theorem coverp00000101101101 : Covers (-182261639/500000 : ℚ) vp00000101101101 := join_branches bp000001011011010 bp000001011011011
private noncomputable def vp000001011011001_0 : Blocks := edgeBlocks% "full/vectors/000001011011001-V-0000.bin"
noncomputable def vp000001011011001 : Blocks := vp000001011011001_0
theorem coverp000001011011001 : Covers (-182011639/250000 : ℚ) vp000001011011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011011000_0 : Blocks := edgeBlocks% "full/vectors/000001011011000-V-0000.bin"
noncomputable def vp000001011011000 : Blocks := vp000001011011000_0
theorem coverp000001011011000 : Covers (-181761639/250000 : ℚ) vp000001011011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101101100_0 : Blocks := edgeBlocks% "full/vectors/00000101101100-V-0000.bin"
noncomputable def vp00000101101100 : Blocks := vp00000101101100_0
private theorem bp000001011011000 : Branch 0 (-181761639/500000 : ℚ) vp00000101101100 := by
  apply branch_left_normalized (c:=vp000001011011000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-181761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-181761639/250000 : ℚ) by norm_num]
  exact coverp000001011011000
private noncomputable def ep000001011011001_0 : Blocks := edgeBlocks% "full/vectors/000001011011001-E-0000.bin"
noncomputable def ep000001011011001 : Blocks := ep000001011011001_0
private theorem idp000001011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101101100.list =
    C ((2:ℤ)^59) * horner X vp000001011011001.list + horner X ep000001011011001.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011011001 : Branch 1 (-181761639/500000 : ℚ) vp00000101101100 := by
  apply branch_checked idp000001011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-181761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-182011639/250000 : ℚ) by norm_num]
  exact coverp000001011011001
theorem coverp00000101101100 : Covers (-181761639/500000 : ℚ) vp00000101101100 := join_branches bp000001011011000 bp000001011011001
private noncomputable def vp0000010110110_0 : Blocks := edgeBlocks% "full/vectors/0000010110110-V-0000.bin"
noncomputable def vp0000010110110 : Blocks := vp0000010110110_0
private theorem bp00000101101100 : Branch 0 (-181761639/1000000 : ℚ) vp0000010110110 := by
  apply branch_left_normalized (c:=vp00000101101100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-181761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-181761639/500000 : ℚ) by norm_num]
  exact coverp00000101101100
private noncomputable def ep00000101101101_0 : Blocks := edgeBlocks% "full/vectors/00000101101101-E-0000.bin"
noncomputable def ep00000101101101 : Blocks := ep00000101101101_0
private theorem idp00000101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010110110.list =
    C ((2:ℤ)^98) * horner X vp00000101101101.list + horner X ep00000101101101.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101101101 : Branch 1 (-181761639/1000000 : ℚ) vp0000010110110 := by
  apply branch_checked idp00000101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-181761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-182261639/500000 : ℚ) by norm_num]
  exact coverp00000101101101
theorem coverp0000010110110 : Covers (-181761639/1000000 : ℚ) vp0000010110110 := join_branches bp00000101101100 bp00000101101101
private noncomputable def vp000001011011_0 : Blocks := edgeBlocks% "full/vectors/000001011011-V-0000.bin"
private noncomputable def vp000001011011_1 : Blocks := edgeBlocks% "full/vectors/000001011011-V-0001.bin"
noncomputable def vp000001011011 : Blocks := (Blocks.join vp000001011011_0 vp000001011011_1)
private theorem bp0000010110110 : Branch 0 (-181761639/2000000 : ℚ) vp000001011011 := by
  apply branch_left_normalized (c:=vp0000010110110) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-181761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-181761639/1000000 : ℚ) by norm_num]
  exact coverp0000010110110
private noncomputable def ep0000010110111_0 : Blocks := edgeBlocks% "full/vectors/0000010110111-E-0000.bin"
private noncomputable def ep0000010110111_1 : Blocks := edgeBlocks% "full/vectors/0000010110111-E-0001.bin"
noncomputable def ep0000010110111 : Blocks := (Blocks.join ep0000010110111_0 ep0000010110111_1)
private theorem idp0000010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001011011.list =
    C ((2:ℤ)^176) * horner X vp0000010110111.list + horner X ep0000010110111.list := by
  exact edge_identity (B := (2:ℤ)^349) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010110111 : Branch 1 (-181761639/2000000 : ℚ) vp000001011011 := by
  apply branch_checked idp0000010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-181761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-182761639/1000000 : ℚ) by norm_num]
  exact coverp0000010110111
theorem coverp000001011011 : Covers (-181761639/2000000 : ℚ) vp000001011011 := join_branches bp0000010110110 bp0000010110111
private noncomputable def vp000001011010111_0 : Blocks := edgeBlocks% "full/vectors/000001011010111-V-0000.bin"
noncomputable def vp000001011010111 : Blocks := vp000001011010111_0
theorem coverp000001011010111 : Covers (-181511639/250000 : ℚ) vp000001011010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011010110_0 : Blocks := edgeBlocks% "full/vectors/000001011010110-V-0000.bin"
noncomputable def vp000001011010110 : Blocks := vp000001011010110_0
theorem coverp000001011010110 : Covers (-181261639/250000 : ℚ) vp000001011010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101101011_0 : Blocks := edgeBlocks% "full/vectors/00000101101011-V-0000.bin"
noncomputable def vp00000101101011 : Blocks := vp00000101101011_0
private theorem bp000001011010110 : Branch 0 (-181261639/500000 : ℚ) vp00000101101011 := by
  apply branch_left_normalized (c:=vp000001011010110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-181261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-181261639/250000 : ℚ) by norm_num]
  exact coverp000001011010110
private noncomputable def ep000001011010111_0 : Blocks := edgeBlocks% "full/vectors/000001011010111-E-0000.bin"
noncomputable def ep000001011010111 : Blocks := ep000001011010111_0
private theorem idp000001011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101101011.list =
    C ((2:ℤ)^58) * horner X vp000001011010111.list + horner X ep000001011010111.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011010111 : Branch 1 (-181261639/500000 : ℚ) vp00000101101011 := by
  apply branch_checked idp000001011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-181261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-181511639/250000 : ℚ) by norm_num]
  exact coverp000001011010111
theorem coverp00000101101011 : Covers (-181261639/500000 : ℚ) vp00000101101011 := join_branches bp000001011010110 bp000001011010111
private noncomputable def vp000001011010101_0 : Blocks := edgeBlocks% "full/vectors/000001011010101-V-0000.bin"
noncomputable def vp000001011010101 : Blocks := vp000001011010101_0
theorem coverp000001011010101 : Covers (-181011639/250000 : ℚ) vp000001011010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011010100_0 : Blocks := edgeBlocks% "full/vectors/000001011010100-V-0000.bin"
noncomputable def vp000001011010100 : Blocks := vp000001011010100_0
theorem coverp000001011010100 : Covers (-180761639/250000 : ℚ) vp000001011010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101101010_0 : Blocks := edgeBlocks% "full/vectors/00000101101010-V-0000.bin"
noncomputable def vp00000101101010 : Blocks := vp00000101101010_0
private theorem bp000001011010100 : Branch 0 (-180761639/500000 : ℚ) vp00000101101010 := by
  apply branch_left_normalized (c:=vp000001011010100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-180761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-180761639/250000 : ℚ) by norm_num]
  exact coverp000001011010100
private noncomputable def ep000001011010101_0 : Blocks := edgeBlocks% "full/vectors/000001011010101-E-0000.bin"
noncomputable def ep000001011010101 : Blocks := ep000001011010101_0
private theorem idp000001011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101101010.list =
    C ((2:ℤ)^58) * horner X vp000001011010101.list + horner X ep000001011010101.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011010101 : Branch 1 (-180761639/500000 : ℚ) vp00000101101010 := by
  apply branch_checked idp000001011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-180761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-181011639/250000 : ℚ) by norm_num]
  exact coverp000001011010101
theorem coverp00000101101010 : Covers (-180761639/500000 : ℚ) vp00000101101010 := join_branches bp000001011010100 bp000001011010101
private noncomputable def vp0000010110101_0 : Blocks := edgeBlocks% "full/vectors/0000010110101-V-0000.bin"
noncomputable def vp0000010110101 : Blocks := vp0000010110101_0
private theorem bp00000101101010 : Branch 0 (-180761639/1000000 : ℚ) vp0000010110101 := by
  apply branch_left_normalized (c:=vp00000101101010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-180761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-180761639/500000 : ℚ) by norm_num]
  exact coverp00000101101010
private noncomputable def ep00000101101011_0 : Blocks := edgeBlocks% "full/vectors/00000101101011-E-0000.bin"
noncomputable def ep00000101101011 : Blocks := ep00000101101011_0
private theorem idp00000101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010110101.list =
    C ((2:ℤ)^97) * horner X vp00000101101011.list + horner X ep00000101101011.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101101011 : Branch 1 (-180761639/1000000 : ℚ) vp0000010110101 := by
  apply branch_checked idp00000101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-180761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-181261639/500000 : ℚ) by norm_num]
  exact coverp00000101101011
theorem coverp0000010110101 : Covers (-180761639/1000000 : ℚ) vp0000010110101 := join_branches bp00000101101010 bp00000101101011
private noncomputable def vp000001011010011_0 : Blocks := edgeBlocks% "full/vectors/000001011010011-V-0000.bin"
noncomputable def vp000001011010011 : Blocks := vp000001011010011_0
theorem coverp000001011010011 : Covers (-180511639/250000 : ℚ) vp000001011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011010010_0 : Blocks := edgeBlocks% "full/vectors/000001011010010-V-0000.bin"
noncomputable def vp000001011010010 : Blocks := vp000001011010010_0
theorem coverp000001011010010 : Covers (-180261639/250000 : ℚ) vp000001011010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101101001_0 : Blocks := edgeBlocks% "full/vectors/00000101101001-V-0000.bin"
noncomputable def vp00000101101001 : Blocks := vp00000101101001_0
private theorem bp000001011010010 : Branch 0 (-180261639/500000 : ℚ) vp00000101101001 := by
  apply branch_left_normalized (c:=vp000001011010010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-180261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-180261639/250000 : ℚ) by norm_num]
  exact coverp000001011010010
private noncomputable def ep000001011010011_0 : Blocks := edgeBlocks% "full/vectors/000001011010011-E-0000.bin"
noncomputable def ep000001011010011 : Blocks := ep000001011010011_0
private theorem idp000001011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101101001.list =
    C ((2:ℤ)^58) * horner X vp000001011010011.list + horner X ep000001011010011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011010011 : Branch 1 (-180261639/500000 : ℚ) vp00000101101001 := by
  apply branch_checked idp000001011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-180261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-180511639/250000 : ℚ) by norm_num]
  exact coverp000001011010011
theorem coverp00000101101001 : Covers (-180261639/500000 : ℚ) vp00000101101001 := join_branches bp000001011010010 bp000001011010011
private noncomputable def vp000001011010001_0 : Blocks := edgeBlocks% "full/vectors/000001011010001-V-0000.bin"
noncomputable def vp000001011010001 : Blocks := vp000001011010001_0
theorem coverp000001011010001 : Covers (-180011639/250000 : ℚ) vp000001011010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011010000_0 : Blocks := edgeBlocks% "full/vectors/000001011010000-V-0000.bin"
noncomputable def vp000001011010000 : Blocks := vp000001011010000_0
theorem coverp000001011010000 : Covers (-179761639/250000 : ℚ) vp000001011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101101000_0 : Blocks := edgeBlocks% "full/vectors/00000101101000-V-0000.bin"
noncomputable def vp00000101101000 : Blocks := vp00000101101000_0
private theorem bp000001011010000 : Branch 0 (-179761639/500000 : ℚ) vp00000101101000 := by
  apply branch_left_normalized (c:=vp000001011010000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-179761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-179761639/250000 : ℚ) by norm_num]
  exact coverp000001011010000
private noncomputable def ep000001011010001_0 : Blocks := edgeBlocks% "full/vectors/000001011010001-E-0000.bin"
noncomputable def ep000001011010001 : Blocks := ep000001011010001_0
private theorem idp000001011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101101000.list =
    C ((2:ℤ)^59) * horner X vp000001011010001.list + horner X ep000001011010001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011010001 : Branch 1 (-179761639/500000 : ℚ) vp00000101101000 := by
  apply branch_checked idp000001011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-179761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-180011639/250000 : ℚ) by norm_num]
  exact coverp000001011010001
theorem coverp00000101101000 : Covers (-179761639/500000 : ℚ) vp00000101101000 := join_branches bp000001011010000 bp000001011010001
private noncomputable def vp0000010110100_0 : Blocks := edgeBlocks% "full/vectors/0000010110100-V-0000.bin"
noncomputable def vp0000010110100 : Blocks := vp0000010110100_0
private theorem bp00000101101000 : Branch 0 (-179761639/1000000 : ℚ) vp0000010110100 := by
  apply branch_left_normalized (c:=vp00000101101000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-179761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-179761639/500000 : ℚ) by norm_num]
  exact coverp00000101101000
private noncomputable def ep00000101101001_0 : Blocks := edgeBlocks% "full/vectors/00000101101001-E-0000.bin"
noncomputable def ep00000101101001 : Blocks := ep00000101101001_0
private theorem idp00000101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010110100.list =
    C ((2:ℤ)^98) * horner X vp00000101101001.list + horner X ep00000101101001.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101101001 : Branch 1 (-179761639/1000000 : ℚ) vp0000010110100 := by
  apply branch_checked idp00000101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-179761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-180261639/500000 : ℚ) by norm_num]
  exact coverp00000101101001
theorem coverp0000010110100 : Covers (-179761639/1000000 : ℚ) vp0000010110100 := join_branches bp00000101101000 bp00000101101001
private noncomputable def vp000001011010_0 : Blocks := edgeBlocks% "full/vectors/000001011010-V-0000.bin"
private noncomputable def vp000001011010_1 : Blocks := edgeBlocks% "full/vectors/000001011010-V-0001.bin"
noncomputable def vp000001011010 : Blocks := (Blocks.join vp000001011010_0 vp000001011010_1)
private theorem bp0000010110100 : Branch 0 (-179761639/2000000 : ℚ) vp000001011010 := by
  apply branch_left_normalized (c:=vp0000010110100) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-179761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-179761639/1000000 : ℚ) by norm_num]
  exact coverp0000010110100
private noncomputable def ep0000010110101_0 : Blocks := edgeBlocks% "full/vectors/0000010110101-E-0000.bin"
private noncomputable def ep0000010110101_1 : Blocks := edgeBlocks% "full/vectors/0000010110101-E-0001.bin"
noncomputable def ep0000010110101 : Blocks := (Blocks.join ep0000010110101_0 ep0000010110101_1)
private theorem idp0000010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001011010.list =
    C ((2:ℤ)^174) * horner X vp0000010110101.list + horner X ep0000010110101.list := by
  exact edge_identity (B := (2:ℤ)^347) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010110101 : Branch 1 (-179761639/2000000 : ℚ) vp000001011010 := by
  apply branch_checked idp0000010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-179761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-180761639/1000000 : ℚ) by norm_num]
  exact coverp0000010110101
theorem coverp000001011010 : Covers (-179761639/2000000 : ℚ) vp000001011010 := join_branches bp0000010110100 bp0000010110101
private noncomputable def vp00000101101_0 : Blocks := edgeBlocks% "full/vectors/00000101101-V-0000.bin"
private noncomputable def vp00000101101_1 : Blocks := edgeBlocks% "full/vectors/00000101101-V-0001.bin"
private noncomputable def vp00000101101_2 : Blocks := edgeBlocks% "full/vectors/00000101101-V-0002.bin"
noncomputable def vp00000101101 : Blocks := (Blocks.join vp00000101101_0 (Blocks.join vp00000101101_1 vp00000101101_2))
private theorem bp000001011010 : Branch 0 (-179761639/4000000 : ℚ) vp00000101101 := by
  apply branch_left_normalized (c:=vp000001011010) (k:=0) (m:=168) (by decide +kernel)
  rw [show 2*(-179761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-179761639/2000000 : ℚ) by norm_num]
  exact coverp000001011010
private noncomputable def ep000001011011_0 : Blocks := edgeBlocks% "full/vectors/000001011011-E-0000.bin"
private noncomputable def ep000001011011_1 : Blocks := edgeBlocks% "full/vectors/000001011011-E-0001.bin"
private noncomputable def ep000001011011_2 : Blocks := edgeBlocks% "full/vectors/000001011011-E-0002.bin"
noncomputable def ep000001011011 : Blocks := (Blocks.join ep000001011011_0 (Blocks.join ep000001011011_1 ep000001011011_2))
private theorem idp000001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101101.list =
    C ((2:ℤ)^324) * horner X vp000001011011.list + horner X ep000001011011.list := by
  exact edge_identity (B := (2:ℤ)^571) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011011 : Branch 1 (-179761639/4000000 : ℚ) vp00000101101 := by
  apply branch_checked idp000001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-179761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-181761639/2000000 : ℚ) by norm_num]
  exact coverp000001011011
theorem coverp00000101101 : Covers (-179761639/4000000 : ℚ) vp00000101101 := join_branches bp000001011010 bp000001011011
private noncomputable def vp000001011001111_0 : Blocks := edgeBlocks% "full/vectors/000001011001111-V-0000.bin"
noncomputable def vp000001011001111 : Blocks := vp000001011001111_0
theorem coverp000001011001111 : Covers (-179511639/250000 : ℚ) vp000001011001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011001110_0 : Blocks := edgeBlocks% "full/vectors/000001011001110-V-0000.bin"
noncomputable def vp000001011001110 : Blocks := vp000001011001110_0
theorem coverp000001011001110 : Covers (-179261639/250000 : ℚ) vp000001011001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101100111_0 : Blocks := edgeBlocks% "full/vectors/00000101100111-V-0000.bin"
noncomputable def vp00000101100111 : Blocks := vp00000101100111_0
private theorem bp000001011001110 : Branch 0 (-179261639/500000 : ℚ) vp00000101100111 := by
  apply branch_left_normalized (c:=vp000001011001110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-179261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-179261639/250000 : ℚ) by norm_num]
  exact coverp000001011001110
private noncomputable def ep000001011001111_0 : Blocks := edgeBlocks% "full/vectors/000001011001111-E-0000.bin"
noncomputable def ep000001011001111 : Blocks := ep000001011001111_0
private theorem idp000001011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101100111.list =
    C ((2:ℤ)^58) * horner X vp000001011001111.list + horner X ep000001011001111.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011001111 : Branch 1 (-179261639/500000 : ℚ) vp00000101100111 := by
  apply branch_checked idp000001011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-179261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-179511639/250000 : ℚ) by norm_num]
  exact coverp000001011001111
theorem coverp00000101100111 : Covers (-179261639/500000 : ℚ) vp00000101100111 := join_branches bp000001011001110 bp000001011001111
private noncomputable def vp000001011001101_0 : Blocks := edgeBlocks% "full/vectors/000001011001101-V-0000.bin"
noncomputable def vp000001011001101 : Blocks := vp000001011001101_0
theorem coverp000001011001101 : Covers (-179011639/250000 : ℚ) vp000001011001101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011001100_0 : Blocks := edgeBlocks% "full/vectors/000001011001100-V-0000.bin"
noncomputable def vp000001011001100 : Blocks := vp000001011001100_0
theorem coverp000001011001100 : Covers (-178761639/250000 : ℚ) vp000001011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101100110_0 : Blocks := edgeBlocks% "full/vectors/00000101100110-V-0000.bin"
noncomputable def vp00000101100110 : Blocks := vp00000101100110_0
private theorem bp000001011001100 : Branch 0 (-178761639/500000 : ℚ) vp00000101100110 := by
  apply branch_left_normalized (c:=vp000001011001100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-178761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-178761639/250000 : ℚ) by norm_num]
  exact coverp000001011001100
private noncomputable def ep000001011001101_0 : Blocks := edgeBlocks% "full/vectors/000001011001101-E-0000.bin"
noncomputable def ep000001011001101 : Blocks := ep000001011001101_0
private theorem idp000001011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101100110.list =
    C ((2:ℤ)^59) * horner X vp000001011001101.list + horner X ep000001011001101.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011001101 : Branch 1 (-178761639/500000 : ℚ) vp00000101100110 := by
  apply branch_checked idp000001011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-178761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-179011639/250000 : ℚ) by norm_num]
  exact coverp000001011001101
theorem coverp00000101100110 : Covers (-178761639/500000 : ℚ) vp00000101100110 := join_branches bp000001011001100 bp000001011001101
private noncomputable def vp0000010110011_0 : Blocks := edgeBlocks% "full/vectors/0000010110011-V-0000.bin"
noncomputable def vp0000010110011 : Blocks := vp0000010110011_0
private theorem bp00000101100110 : Branch 0 (-178761639/1000000 : ℚ) vp0000010110011 := by
  apply branch_left_normalized (c:=vp00000101100110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-178761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-178761639/500000 : ℚ) by norm_num]
  exact coverp00000101100110
private noncomputable def ep00000101100111_0 : Blocks := edgeBlocks% "full/vectors/00000101100111-E-0000.bin"
noncomputable def ep00000101100111 : Blocks := ep00000101100111_0
private theorem idp00000101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010110011.list =
    C ((2:ℤ)^98) * horner X vp00000101100111.list + horner X ep00000101100111.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101100111 : Branch 1 (-178761639/1000000 : ℚ) vp0000010110011 := by
  apply branch_checked idp00000101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-178761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-179261639/500000 : ℚ) by norm_num]
  exact coverp00000101100111
theorem coverp0000010110011 : Covers (-178761639/1000000 : ℚ) vp0000010110011 := join_branches bp00000101100110 bp00000101100111
private noncomputable def vp000001011001011_0 : Blocks := edgeBlocks% "full/vectors/000001011001011-V-0000.bin"
noncomputable def vp000001011001011 : Blocks := vp000001011001011_0
theorem coverp000001011001011 : Covers (-178511639/250000 : ℚ) vp000001011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011001010_0 : Blocks := edgeBlocks% "full/vectors/000001011001010-V-0000.bin"
noncomputable def vp000001011001010 : Blocks := vp000001011001010_0
theorem coverp000001011001010 : Covers (-178261639/250000 : ℚ) vp000001011001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101100101_0 : Blocks := edgeBlocks% "full/vectors/00000101100101-V-0000.bin"
noncomputable def vp00000101100101 : Blocks := vp00000101100101_0
private theorem bp000001011001010 : Branch 0 (-178261639/500000 : ℚ) vp00000101100101 := by
  apply branch_left_normalized (c:=vp000001011001010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-178261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-178261639/250000 : ℚ) by norm_num]
  exact coverp000001011001010
private noncomputable def ep000001011001011_0 : Blocks := edgeBlocks% "full/vectors/000001011001011-E-0000.bin"
noncomputable def ep000001011001011 : Blocks := ep000001011001011_0
private theorem idp000001011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101100101.list =
    C ((2:ℤ)^59) * horner X vp000001011001011.list + horner X ep000001011001011.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011001011 : Branch 1 (-178261639/500000 : ℚ) vp00000101100101 := by
  apply branch_checked idp000001011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-178261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-178511639/250000 : ℚ) by norm_num]
  exact coverp000001011001011
theorem coverp00000101100101 : Covers (-178261639/500000 : ℚ) vp00000101100101 := join_branches bp000001011001010 bp000001011001011
private noncomputable def vp000001011001001_0 : Blocks := edgeBlocks% "full/vectors/000001011001001-V-0000.bin"
noncomputable def vp000001011001001 : Blocks := vp000001011001001_0
theorem coverp000001011001001 : Covers (-178011639/250000 : ℚ) vp000001011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011001000_0 : Blocks := edgeBlocks% "full/vectors/000001011001000-V-0000.bin"
noncomputable def vp000001011001000 : Blocks := vp000001011001000_0
theorem coverp000001011001000 : Covers (-177761639/250000 : ℚ) vp000001011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101100100_0 : Blocks := edgeBlocks% "full/vectors/00000101100100-V-0000.bin"
noncomputable def vp00000101100100 : Blocks := vp00000101100100_0
private theorem bp000001011001000 : Branch 0 (-177761639/500000 : ℚ) vp00000101100100 := by
  apply branch_left_normalized (c:=vp000001011001000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-177761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-177761639/250000 : ℚ) by norm_num]
  exact coverp000001011001000
private noncomputable def ep000001011001001_0 : Blocks := edgeBlocks% "full/vectors/000001011001001-E-0000.bin"
noncomputable def ep000001011001001 : Blocks := ep000001011001001_0
private theorem idp000001011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101100100.list =
    C ((2:ℤ)^60) * horner X vp000001011001001.list + horner X ep000001011001001.list := by
  exact edge_identity (B := (2:ℤ)^180) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011001001 : Branch 1 (-177761639/500000 : ℚ) vp00000101100100 := by
  apply branch_checked idp000001011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-177761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-178011639/250000 : ℚ) by norm_num]
  exact coverp000001011001001
theorem coverp00000101100100 : Covers (-177761639/500000 : ℚ) vp00000101100100 := join_branches bp000001011001000 bp000001011001001
private noncomputable def vp0000010110010_0 : Blocks := edgeBlocks% "full/vectors/0000010110010-V-0000.bin"
noncomputable def vp0000010110010 : Blocks := vp0000010110010_0
private theorem bp00000101100100 : Branch 0 (-177761639/1000000 : ℚ) vp0000010110010 := by
  apply branch_left_normalized (c:=vp00000101100100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-177761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-177761639/500000 : ℚ) by norm_num]
  exact coverp00000101100100
private noncomputable def ep00000101100101_0 : Blocks := edgeBlocks% "full/vectors/00000101100101-E-0000.bin"
noncomputable def ep00000101100101 : Blocks := ep00000101100101_0
private theorem idp00000101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010110010.list =
    C ((2:ℤ)^100) * horner X vp00000101100101.list + horner X ep00000101100101.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101100101 : Branch 1 (-177761639/1000000 : ℚ) vp0000010110010 := by
  apply branch_checked idp00000101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-177761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-178261639/500000 : ℚ) by norm_num]
  exact coverp00000101100101
theorem coverp0000010110010 : Covers (-177761639/1000000 : ℚ) vp0000010110010 := join_branches bp00000101100100 bp00000101100101
private noncomputable def vp000001011001_0 : Blocks := edgeBlocks% "full/vectors/000001011001-V-0000.bin"
private noncomputable def vp000001011001_1 : Blocks := edgeBlocks% "full/vectors/000001011001-V-0001.bin"
noncomputable def vp000001011001 : Blocks := (Blocks.join vp000001011001_0 vp000001011001_1)
private theorem bp0000010110010 : Branch 0 (-177761639/2000000 : ℚ) vp000001011001 := by
  apply branch_left_normalized (c:=vp0000010110010) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-177761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-177761639/1000000 : ℚ) by norm_num]
  exact coverp0000010110010
private noncomputable def ep0000010110011_0 : Blocks := edgeBlocks% "full/vectors/0000010110011-E-0000.bin"
private noncomputable def ep0000010110011_1 : Blocks := edgeBlocks% "full/vectors/0000010110011-E-0001.bin"
noncomputable def ep0000010110011 : Blocks := (Blocks.join ep0000010110011_0 ep0000010110011_1)
private theorem idp0000010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001011001.list =
    C ((2:ℤ)^179) * horner X vp0000010110011.list + horner X ep0000010110011.list := by
  exact edge_identity (B := (2:ℤ)^352) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010110011 : Branch 1 (-177761639/2000000 : ℚ) vp000001011001 := by
  apply branch_checked idp0000010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-177761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-178761639/1000000 : ℚ) by norm_num]
  exact coverp0000010110011
theorem coverp000001011001 : Covers (-177761639/2000000 : ℚ) vp000001011001 := join_branches bp0000010110010 bp0000010110011
private noncomputable def vp000001011000111_0 : Blocks := edgeBlocks% "full/vectors/000001011000111-V-0000.bin"
noncomputable def vp000001011000111 : Blocks := vp000001011000111_0
theorem coverp000001011000111 : Covers (-177511639/250000 : ℚ) vp000001011000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011000110_0 : Blocks := edgeBlocks% "full/vectors/000001011000110-V-0000.bin"
noncomputable def vp000001011000110 : Blocks := vp000001011000110_0
theorem coverp000001011000110 : Covers (-177261639/250000 : ℚ) vp000001011000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101100011_0 : Blocks := edgeBlocks% "full/vectors/00000101100011-V-0000.bin"
noncomputable def vp00000101100011 : Blocks := vp00000101100011_0
private theorem bp000001011000110 : Branch 0 (-177261639/500000 : ℚ) vp00000101100011 := by
  apply branch_left_normalized (c:=vp000001011000110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-177261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-177261639/250000 : ℚ) by norm_num]
  exact coverp000001011000110
private noncomputable def ep000001011000111_0 : Blocks := edgeBlocks% "full/vectors/000001011000111-E-0000.bin"
noncomputable def ep000001011000111 : Blocks := ep000001011000111_0
private theorem idp000001011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101100011.list =
    C ((2:ℤ)^58) * horner X vp000001011000111.list + horner X ep000001011000111.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011000111 : Branch 1 (-177261639/500000 : ℚ) vp00000101100011 := by
  apply branch_checked idp000001011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-177261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-177511639/250000 : ℚ) by norm_num]
  exact coverp000001011000111
theorem coverp00000101100011 : Covers (-177261639/500000 : ℚ) vp00000101100011 := join_branches bp000001011000110 bp000001011000111
private noncomputable def vp000001011000101_0 : Blocks := edgeBlocks% "full/vectors/000001011000101-V-0000.bin"
noncomputable def vp000001011000101 : Blocks := vp000001011000101_0
theorem coverp000001011000101 : Covers (-177011639/250000 : ℚ) vp000001011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011000100_0 : Blocks := edgeBlocks% "full/vectors/000001011000100-V-0000.bin"
noncomputable def vp000001011000100 : Blocks := vp000001011000100_0
theorem coverp000001011000100 : Covers (-176761639/250000 : ℚ) vp000001011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101100010_0 : Blocks := edgeBlocks% "full/vectors/00000101100010-V-0000.bin"
noncomputable def vp00000101100010 : Blocks := vp00000101100010_0
private theorem bp000001011000100 : Branch 0 (-176761639/500000 : ℚ) vp00000101100010 := by
  apply branch_left_normalized (c:=vp000001011000100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-176761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-176761639/250000 : ℚ) by norm_num]
  exact coverp000001011000100
private noncomputable def ep000001011000101_0 : Blocks := edgeBlocks% "full/vectors/000001011000101-E-0000.bin"
noncomputable def ep000001011000101 : Blocks := ep000001011000101_0
private theorem idp000001011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101100010.list =
    C ((2:ℤ)^57) * horner X vp000001011000101.list + horner X ep000001011000101.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011000101 : Branch 1 (-176761639/500000 : ℚ) vp00000101100010 := by
  apply branch_checked idp000001011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-176761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-177011639/250000 : ℚ) by norm_num]
  exact coverp000001011000101
theorem coverp00000101100010 : Covers (-176761639/500000 : ℚ) vp00000101100010 := join_branches bp000001011000100 bp000001011000101
private noncomputable def vp0000010110001_0 : Blocks := edgeBlocks% "full/vectors/0000010110001-V-0000.bin"
noncomputable def vp0000010110001 : Blocks := vp0000010110001_0
private theorem bp00000101100010 : Branch 0 (-176761639/1000000 : ℚ) vp0000010110001 := by
  apply branch_left_normalized (c:=vp00000101100010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-176761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-176761639/500000 : ℚ) by norm_num]
  exact coverp00000101100010
private noncomputable def ep00000101100011_0 : Blocks := edgeBlocks% "full/vectors/00000101100011-E-0000.bin"
noncomputable def ep00000101100011 : Blocks := ep00000101100011_0
private theorem idp00000101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010110001.list =
    C ((2:ℤ)^95) * horner X vp00000101100011.list + horner X ep00000101100011.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101100011 : Branch 1 (-176761639/1000000 : ℚ) vp0000010110001 := by
  apply branch_checked idp00000101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-176761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-177261639/500000 : ℚ) by norm_num]
  exact coverp00000101100011
theorem coverp0000010110001 : Covers (-176761639/1000000 : ℚ) vp0000010110001 := join_branches bp00000101100010 bp00000101100011
private noncomputable def vp000001011000011_0 : Blocks := edgeBlocks% "full/vectors/000001011000011-V-0000.bin"
noncomputable def vp000001011000011 : Blocks := vp000001011000011_0
theorem coverp000001011000011 : Covers (-176511639/250000 : ℚ) vp000001011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011000010_0 : Blocks := edgeBlocks% "full/vectors/000001011000010-V-0000.bin"
noncomputable def vp000001011000010 : Blocks := vp000001011000010_0
theorem coverp000001011000010 : Covers (-176261639/250000 : ℚ) vp000001011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101100001_0 : Blocks := edgeBlocks% "full/vectors/00000101100001-V-0000.bin"
noncomputable def vp00000101100001 : Blocks := vp00000101100001_0
private theorem bp000001011000010 : Branch 0 (-176261639/500000 : ℚ) vp00000101100001 := by
  apply branch_left_normalized (c:=vp000001011000010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-176261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-176261639/250000 : ℚ) by norm_num]
  exact coverp000001011000010
private noncomputable def ep000001011000011_0 : Blocks := edgeBlocks% "full/vectors/000001011000011-E-0000.bin"
noncomputable def ep000001011000011 : Blocks := ep000001011000011_0
private theorem idp000001011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101100001.list =
    C ((2:ℤ)^57) * horner X vp000001011000011.list + horner X ep000001011000011.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011000011 : Branch 1 (-176261639/500000 : ℚ) vp00000101100001 := by
  apply branch_checked idp000001011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-176261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-176511639/250000 : ℚ) by norm_num]
  exact coverp000001011000011
theorem coverp00000101100001 : Covers (-176261639/500000 : ℚ) vp00000101100001 := join_branches bp000001011000010 bp000001011000011
private noncomputable def vp000001011000001_0 : Blocks := edgeBlocks% "full/vectors/000001011000001-V-0000.bin"
noncomputable def vp000001011000001 : Blocks := vp000001011000001_0
theorem coverp000001011000001 : Covers (-176011639/250000 : ℚ) vp000001011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001011000000_0 : Blocks := edgeBlocks% "full/vectors/000001011000000-V-0000.bin"
noncomputable def vp000001011000000 : Blocks := vp000001011000000_0
theorem coverp000001011000000 : Covers (-175761639/250000 : ℚ) vp000001011000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101100000_0 : Blocks := edgeBlocks% "full/vectors/00000101100000-V-0000.bin"
noncomputable def vp00000101100000 : Blocks := vp00000101100000_0
private theorem bp000001011000000 : Branch 0 (-175761639/500000 : ℚ) vp00000101100000 := by
  apply branch_left_normalized (c:=vp000001011000000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-175761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-175761639/250000 : ℚ) by norm_num]
  exact coverp000001011000000
private noncomputable def ep000001011000001_0 : Blocks := edgeBlocks% "full/vectors/000001011000001-E-0000.bin"
noncomputable def ep000001011000001 : Blocks := ep000001011000001_0
private theorem idp000001011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101100000.list =
    C ((2:ℤ)^57) * horner X vp000001011000001.list + horner X ep000001011000001.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011000001 : Branch 1 (-175761639/500000 : ℚ) vp00000101100000 := by
  apply branch_checked idp000001011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-175761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-176011639/250000 : ℚ) by norm_num]
  exact coverp000001011000001
theorem coverp00000101100000 : Covers (-175761639/500000 : ℚ) vp00000101100000 := join_branches bp000001011000000 bp000001011000001
private noncomputable def vp0000010110000_0 : Blocks := edgeBlocks% "full/vectors/0000010110000-V-0000.bin"
noncomputable def vp0000010110000 : Blocks := vp0000010110000_0
private theorem bp00000101100000 : Branch 0 (-175761639/1000000 : ℚ) vp0000010110000 := by
  apply branch_left_normalized (c:=vp00000101100000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-175761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-175761639/500000 : ℚ) by norm_num]
  exact coverp00000101100000
private noncomputable def ep00000101100001_0 : Blocks := edgeBlocks% "full/vectors/00000101100001-E-0000.bin"
noncomputable def ep00000101100001 : Blocks := ep00000101100001_0
private theorem idp00000101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010110000.list =
    C ((2:ℤ)^98) * horner X vp00000101100001.list + horner X ep00000101100001.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101100001 : Branch 1 (-175761639/1000000 : ℚ) vp0000010110000 := by
  apply branch_checked idp00000101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-175761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-176261639/500000 : ℚ) by norm_num]
  exact coverp00000101100001
theorem coverp0000010110000 : Covers (-175761639/1000000 : ℚ) vp0000010110000 := join_branches bp00000101100000 bp00000101100001
private noncomputable def vp000001011000_0 : Blocks := edgeBlocks% "full/vectors/000001011000-V-0000.bin"
private noncomputable def vp000001011000_1 : Blocks := edgeBlocks% "full/vectors/000001011000-V-0001.bin"
noncomputable def vp000001011000 : Blocks := (Blocks.join vp000001011000_0 vp000001011000_1)
private theorem bp0000010110000 : Branch 0 (-175761639/2000000 : ℚ) vp000001011000 := by
  apply branch_left_normalized (c:=vp0000010110000) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-175761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-175761639/1000000 : ℚ) by norm_num]
  exact coverp0000010110000
private noncomputable def ep0000010110001_0 : Blocks := edgeBlocks% "full/vectors/0000010110001-E-0000.bin"
private noncomputable def ep0000010110001_1 : Blocks := edgeBlocks% "full/vectors/0000010110001-E-0001.bin"
noncomputable def ep0000010110001 : Blocks := (Blocks.join ep0000010110001_0 ep0000010110001_1)
private theorem idp0000010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001011000.list =
    C ((2:ℤ)^174) * horner X vp0000010110001.list + horner X ep0000010110001.list := by
  exact edge_identity (B := (2:ℤ)^346) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010110001 : Branch 1 (-175761639/2000000 : ℚ) vp000001011000 := by
  apply branch_checked idp0000010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-175761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-176761639/1000000 : ℚ) by norm_num]
  exact coverp0000010110001
theorem coverp000001011000 : Covers (-175761639/2000000 : ℚ) vp000001011000 := join_branches bp0000010110000 bp0000010110001
private noncomputable def vp00000101100_0 : Blocks := edgeBlocks% "full/vectors/00000101100-V-0000.bin"
private noncomputable def vp00000101100_1 : Blocks := edgeBlocks% "full/vectors/00000101100-V-0001.bin"
private noncomputable def vp00000101100_2 : Blocks := edgeBlocks% "full/vectors/00000101100-V-0002.bin"
noncomputable def vp00000101100 : Blocks := (Blocks.join vp00000101100_0 (Blocks.join vp00000101100_1 vp00000101100_2))
private theorem bp000001011000 : Branch 0 (-175761639/4000000 : ℚ) vp00000101100 := by
  apply branch_left_normalized (c:=vp000001011000) (k:=0) (m:=168) (by decide +kernel)
  rw [show 2*(-175761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-175761639/2000000 : ℚ) by norm_num]
  exact coverp000001011000
private noncomputable def ep000001011001_0 : Blocks := edgeBlocks% "full/vectors/000001011001-E-0000.bin"
private noncomputable def ep000001011001_1 : Blocks := edgeBlocks% "full/vectors/000001011001-E-0001.bin"
private noncomputable def ep000001011001_2 : Blocks := edgeBlocks% "full/vectors/000001011001-E-0002.bin"
noncomputable def ep000001011001 : Blocks := (Blocks.join ep000001011001_0 (Blocks.join ep000001011001_1 ep000001011001_2))
private theorem idp000001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101100.list =
    C ((2:ℤ)^324) * horner X vp000001011001.list + horner X ep000001011001.list := by
  exact edge_identity (B := (2:ℤ)^572) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011001 : Branch 1 (-175761639/4000000 : ℚ) vp00000101100 := by
  apply branch_checked idp000001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-175761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-177761639/2000000 : ℚ) by norm_num]
  exact coverp000001011001
theorem coverp00000101100 : Covers (-175761639/4000000 : ℚ) vp00000101100 := join_branches bp000001011000 bp000001011001
private noncomputable def vp0000010110_0 : Blocks := edgeBlocks% "full/vectors/0000010110-V-0000.bin"
private noncomputable def vp0000010110_1 : Blocks := edgeBlocks% "full/vectors/0000010110-V-0001.bin"
private noncomputable def vp0000010110_2 : Blocks := edgeBlocks% "full/vectors/0000010110-V-0002.bin"
private noncomputable def vp0000010110_3 : Blocks := edgeBlocks% "full/vectors/0000010110-V-0003.bin"
private noncomputable def vp0000010110_4 : Blocks := edgeBlocks% "full/vectors/0000010110-V-0004.bin"
noncomputable def vp0000010110 : Blocks := (Blocks.join (Blocks.join vp0000010110_0 vp0000010110_1) (Blocks.join vp0000010110_2 (Blocks.join vp0000010110_3 vp0000010110_4)))
private theorem bp00000101100 : Branch 0 (-175761639/8000000 : ℚ) vp0000010110 := by
  apply branch_left_normalized (c:=vp00000101100) (k:=0) (m:=316) (by decide +kernel)
  rw [show 2*(-175761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-175761639/4000000 : ℚ) by norm_num]
  exact coverp00000101100
private noncomputable def ep00000101101_0 : Blocks := edgeBlocks% "full/vectors/00000101101-E-0000.bin"
private noncomputable def ep00000101101_1 : Blocks := edgeBlocks% "full/vectors/00000101101-E-0001.bin"
private noncomputable def ep00000101101_2 : Blocks := edgeBlocks% "full/vectors/00000101101-E-0002.bin"
private noncomputable def ep00000101101_3 : Blocks := edgeBlocks% "full/vectors/00000101101-E-0003.bin"
private noncomputable def ep00000101101_4 : Blocks := edgeBlocks% "full/vectors/00000101101-E-0004.bin"
noncomputable def ep00000101101 : Blocks := (Blocks.join (Blocks.join ep00000101101_0 ep00000101101_1) (Blocks.join ep00000101101_2 (Blocks.join ep00000101101_3 ep00000101101_4)))
private theorem idp00000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010110.list =
    C ((2:ℤ)^630) * horner X vp00000101101.list + horner X ep00000101101.list := by
  exact edge_identity (B := (2:ℤ)^1021) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101101 : Branch 1 (-175761639/8000000 : ℚ) vp0000010110 := by
  apply branch_checked idp00000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-175761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-179761639/4000000 : ℚ) by norm_num]
  exact coverp00000101101
theorem coverp0000010110 : Covers (-175761639/8000000 : ℚ) vp0000010110 := join_branches bp00000101100 bp00000101101
private noncomputable def vp000001011_0 : Blocks := edgeBlocks% "full/vectors/000001011-V-0000.bin"
private noncomputable def vp000001011_1 : Blocks := edgeBlocks% "full/vectors/000001011-V-0001.bin"
private noncomputable def vp000001011_2 : Blocks := edgeBlocks% "full/vectors/000001011-V-0002.bin"
private noncomputable def vp000001011_3 : Blocks := edgeBlocks% "full/vectors/000001011-V-0003.bin"
private noncomputable def vp000001011_4 : Blocks := edgeBlocks% "full/vectors/000001011-V-0004.bin"
private noncomputable def vp000001011_5 : Blocks := edgeBlocks% "full/vectors/000001011-V-0005.bin"
private noncomputable def vp000001011_6 : Blocks := edgeBlocks% "full/vectors/000001011-V-0006.bin"
private noncomputable def vp000001011_7 : Blocks := edgeBlocks% "full/vectors/000001011-V-0007.bin"
private noncomputable def vp000001011_8 : Blocks := edgeBlocks% "full/vectors/000001011-V-0008.bin"
private noncomputable def vp000001011_9 : Blocks := edgeBlocks% "full/vectors/000001011-V-0009.bin"
noncomputable def vp000001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000001011_0 vp000001011_1) (Blocks.join vp000001011_2 (Blocks.join vp000001011_3 vp000001011_4))) (Blocks.join (Blocks.join vp000001011_5 vp000001011_6) (Blocks.join vp000001011_7 (Blocks.join vp000001011_8 vp000001011_9))))
private theorem bp0000010110 : Branch 0 (-175761639/16000000 : ℚ) vp000001011 := by
  apply branch_left_normalized (c:=vp0000010110) (k:=0) (m:=608) (by decide +kernel)
  rw [show 2*(-175761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-175761639/8000000 : ℚ) by norm_num]
  exact coverp0000010110
private noncomputable def ep0000010111_0 : Blocks := edgeBlocks% "full/vectors/0000010111-E-0000.bin"
private noncomputable def ep0000010111_1 : Blocks := edgeBlocks% "full/vectors/0000010111-E-0001.bin"
private noncomputable def ep0000010111_2 : Blocks := edgeBlocks% "full/vectors/0000010111-E-0002.bin"
private noncomputable def ep0000010111_3 : Blocks := edgeBlocks% "full/vectors/0000010111-E-0003.bin"
private noncomputable def ep0000010111_4 : Blocks := edgeBlocks% "full/vectors/0000010111-E-0004.bin"
private noncomputable def ep0000010111_5 : Blocks := edgeBlocks% "full/vectors/0000010111-E-0005.bin"
private noncomputable def ep0000010111_6 : Blocks := edgeBlocks% "full/vectors/0000010111-E-0006.bin"
private noncomputable def ep0000010111_7 : Blocks := edgeBlocks% "full/vectors/0000010111-E-0007.bin"
private noncomputable def ep0000010111_8 : Blocks := edgeBlocks% "full/vectors/0000010111-E-0008.bin"
private noncomputable def ep0000010111_9 : Blocks := edgeBlocks% "full/vectors/0000010111-E-0009.bin"
noncomputable def ep0000010111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000010111_0 ep0000010111_1) (Blocks.join ep0000010111_2 (Blocks.join ep0000010111_3 ep0000010111_4))) (Blocks.join (Blocks.join ep0000010111_5 ep0000010111_6) (Blocks.join ep0000010111_7 (Blocks.join ep0000010111_8 ep0000010111_9))))
private theorem idp0000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001011.list =
    C ((2:ℤ)^1230) * horner X vp0000010111.list + horner X ep0000010111.list := by
  exact edge_identity (B := (2:ℤ)^1911) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010111 : Branch 1 (-175761639/16000000 : ℚ) vp000001011 := by
  apply branch_checked idp0000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-175761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-183761639/8000000 : ℚ) by norm_num]
  exact coverp0000010111
theorem coverp000001011 : Covers (-175761639/16000000 : ℚ) vp000001011 := join_branches bp0000010110 bp0000010111
end NextProof.EdgeFull

