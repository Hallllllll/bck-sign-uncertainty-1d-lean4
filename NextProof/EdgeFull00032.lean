import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000001001111111_0 : Blocks := edgeBlocks% "full/vectors/0000001001111111-V-0000.bin"
noncomputable def vp0000001001111111 : Blocks := vp0000001001111111_0
theorem coverp0000001001111111 : Covers (-79636639/125000 : ℚ) vp0000001001111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001111110_0 : Blocks := edgeBlocks% "full/vectors/0000001001111110-V-0000.bin"
noncomputable def vp0000001001111110 : Blocks := vp0000001001111110_0
theorem coverp0000001001111110 : Covers (-79511639/125000 : ℚ) vp0000001001111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100111111_0 : Blocks := edgeBlocks% "full/vectors/000000100111111-V-0000.bin"
noncomputable def vp000000100111111 : Blocks := vp000000100111111_0
private theorem bp0000001001111110 : Branch 0 (-79511639/250000 : ℚ) vp000000100111111 := by
  apply branch_left_normalized (c:=vp0000001001111110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-79511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-79511639/125000 : ℚ) by norm_num]
  exact coverp0000001001111110
private noncomputable def ep0000001001111111_0 : Blocks := edgeBlocks% "full/vectors/0000001001111111-E-0000.bin"
noncomputable def ep0000001001111111 : Blocks := ep0000001001111111_0
private theorem idp0000001001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100111111.list =
    C ((2:ℤ)^47) * horner X vp0000001001111111.list + horner X ep0000001001111111.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001111111 : Branch 1 (-79511639/250000 : ℚ) vp000000100111111 := by
  apply branch_checked idp0000001001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-79511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-79636639/125000 : ℚ) by norm_num]
  exact coverp0000001001111111
theorem coverp000000100111111 : Covers (-79511639/250000 : ℚ) vp000000100111111 := join_branches bp0000001001111110 bp0000001001111111
private noncomputable def vp0000001001111101_0 : Blocks := edgeBlocks% "full/vectors/0000001001111101-V-0000.bin"
noncomputable def vp0000001001111101 : Blocks := vp0000001001111101_0
theorem coverp0000001001111101 : Covers (-79386639/125000 : ℚ) vp0000001001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001111100_0 : Blocks := edgeBlocks% "full/vectors/0000001001111100-V-0000.bin"
noncomputable def vp0000001001111100 : Blocks := vp0000001001111100_0
theorem coverp0000001001111100 : Covers (-79261639/125000 : ℚ) vp0000001001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100111110_0 : Blocks := edgeBlocks% "full/vectors/000000100111110-V-0000.bin"
noncomputable def vp000000100111110 : Blocks := vp000000100111110_0
private theorem bp0000001001111100 : Branch 0 (-79261639/250000 : ℚ) vp000000100111110 := by
  apply branch_left_normalized (c:=vp0000001001111100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-79261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-79261639/125000 : ℚ) by norm_num]
  exact coverp0000001001111100
private noncomputable def ep0000001001111101_0 : Blocks := edgeBlocks% "full/vectors/0000001001111101-E-0000.bin"
noncomputable def ep0000001001111101 : Blocks := ep0000001001111101_0
private theorem idp0000001001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100111110.list =
    C ((2:ℤ)^48) * horner X vp0000001001111101.list + horner X ep0000001001111101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001111101 : Branch 1 (-79261639/250000 : ℚ) vp000000100111110 := by
  apply branch_checked idp0000001001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-79261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-79386639/125000 : ℚ) by norm_num]
  exact coverp0000001001111101
theorem coverp000000100111110 : Covers (-79261639/250000 : ℚ) vp000000100111110 := join_branches bp0000001001111100 bp0000001001111101
private noncomputable def vp00000010011111_0 : Blocks := edgeBlocks% "full/vectors/00000010011111-V-0000.bin"
noncomputable def vp00000010011111 : Blocks := vp00000010011111_0
private theorem bp000000100111110 : Branch 0 (-79261639/500000 : ℚ) vp00000010011111 := by
  apply branch_left_normalized (c:=vp000000100111110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-79261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-79261639/250000 : ℚ) by norm_num]
  exact coverp000000100111110
private noncomputable def ep000000100111111_0 : Blocks := edgeBlocks% "full/vectors/000000100111111-E-0000.bin"
noncomputable def ep000000100111111 : Blocks := ep000000100111111_0
private theorem idp000000100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010011111.list =
    C ((2:ℤ)^78) * horner X vp000000100111111.list + horner X ep000000100111111.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100111111 : Branch 1 (-79261639/500000 : ℚ) vp00000010011111 := by
  apply branch_checked idp000000100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-79261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-79511639/250000 : ℚ) by norm_num]
  exact coverp000000100111111
theorem coverp00000010011111 : Covers (-79261639/500000 : ℚ) vp00000010011111 := join_branches bp000000100111110 bp000000100111111
private noncomputable def vp0000001001111011_0 : Blocks := edgeBlocks% "full/vectors/0000001001111011-V-0000.bin"
noncomputable def vp0000001001111011 : Blocks := vp0000001001111011_0
theorem coverp0000001001111011 : Covers (-79136639/125000 : ℚ) vp0000001001111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001111010_0 : Blocks := edgeBlocks% "full/vectors/0000001001111010-V-0000.bin"
noncomputable def vp0000001001111010 : Blocks := vp0000001001111010_0
theorem coverp0000001001111010 : Covers (-79011639/125000 : ℚ) vp0000001001111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100111101_0 : Blocks := edgeBlocks% "full/vectors/000000100111101-V-0000.bin"
noncomputable def vp000000100111101 : Blocks := vp000000100111101_0
private theorem bp0000001001111010 : Branch 0 (-79011639/250000 : ℚ) vp000000100111101 := by
  apply branch_left_normalized (c:=vp0000001001111010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-79011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-79011639/125000 : ℚ) by norm_num]
  exact coverp0000001001111010
private noncomputable def ep0000001001111011_0 : Blocks := edgeBlocks% "full/vectors/0000001001111011-E-0000.bin"
noncomputable def ep0000001001111011 : Blocks := ep0000001001111011_0
private theorem idp0000001001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100111101.list =
    C ((2:ℤ)^48) * horner X vp0000001001111011.list + horner X ep0000001001111011.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001111011 : Branch 1 (-79011639/250000 : ℚ) vp000000100111101 := by
  apply branch_checked idp0000001001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-79011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-79136639/125000 : ℚ) by norm_num]
  exact coverp0000001001111011
theorem coverp000000100111101 : Covers (-79011639/250000 : ℚ) vp000000100111101 := join_branches bp0000001001111010 bp0000001001111011
private noncomputable def vp0000001001111001_0 : Blocks := edgeBlocks% "full/vectors/0000001001111001-V-0000.bin"
noncomputable def vp0000001001111001 : Blocks := vp0000001001111001_0
theorem coverp0000001001111001 : Covers (-78886639/125000 : ℚ) vp0000001001111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001111000_0 : Blocks := edgeBlocks% "full/vectors/0000001001111000-V-0000.bin"
noncomputable def vp0000001001111000 : Blocks := vp0000001001111000_0
theorem coverp0000001001111000 : Covers (-78761639/125000 : ℚ) vp0000001001111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100111100_0 : Blocks := edgeBlocks% "full/vectors/000000100111100-V-0000.bin"
noncomputable def vp000000100111100 : Blocks := vp000000100111100_0
private theorem bp0000001001111000 : Branch 0 (-78761639/250000 : ℚ) vp000000100111100 := by
  apply branch_left_normalized (c:=vp0000001001111000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-78761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-78761639/125000 : ℚ) by norm_num]
  exact coverp0000001001111000
private noncomputable def ep0000001001111001_0 : Blocks := edgeBlocks% "full/vectors/0000001001111001-E-0000.bin"
noncomputable def ep0000001001111001 : Blocks := ep0000001001111001_0
private theorem idp0000001001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100111100.list =
    C ((2:ℤ)^49) * horner X vp0000001001111001.list + horner X ep0000001001111001.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001111001 : Branch 1 (-78761639/250000 : ℚ) vp000000100111100 := by
  apply branch_checked idp0000001001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-78761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-78886639/125000 : ℚ) by norm_num]
  exact coverp0000001001111001
theorem coverp000000100111100 : Covers (-78761639/250000 : ℚ) vp000000100111100 := join_branches bp0000001001111000 bp0000001001111001
private noncomputable def vp00000010011110_0 : Blocks := edgeBlocks% "full/vectors/00000010011110-V-0000.bin"
noncomputable def vp00000010011110 : Blocks := vp00000010011110_0
private theorem bp000000100111100 : Branch 0 (-78761639/500000 : ℚ) vp00000010011110 := by
  apply branch_left_normalized (c:=vp000000100111100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-78761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-78761639/250000 : ℚ) by norm_num]
  exact coverp000000100111100
private noncomputable def ep000000100111101_0 : Blocks := edgeBlocks% "full/vectors/000000100111101-E-0000.bin"
noncomputable def ep000000100111101 : Blocks := ep000000100111101_0
private theorem idp000000100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010011110.list =
    C ((2:ℤ)^79) * horner X vp000000100111101.list + horner X ep000000100111101.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100111101 : Branch 1 (-78761639/500000 : ℚ) vp00000010011110 := by
  apply branch_checked idp000000100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-78761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-79011639/250000 : ℚ) by norm_num]
  exact coverp000000100111101
theorem coverp00000010011110 : Covers (-78761639/500000 : ℚ) vp00000010011110 := join_branches bp000000100111100 bp000000100111101
private noncomputable def vp0000001001111_0 : Blocks := edgeBlocks% "full/vectors/0000001001111-V-0000.bin"
private noncomputable def vp0000001001111_1 : Blocks := edgeBlocks% "full/vectors/0000001001111-V-0001.bin"
noncomputable def vp0000001001111 : Blocks := (Blocks.join vp0000001001111_0 vp0000001001111_1)
private theorem bp00000010011110 : Branch 0 (-78761639/1000000 : ℚ) vp0000001001111 := by
  apply branch_left_normalized (c:=vp00000010011110) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-78761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-78761639/500000 : ℚ) by norm_num]
  exact coverp00000010011110
private noncomputable def ep00000010011111_0 : Blocks := edgeBlocks% "full/vectors/00000010011111-E-0000.bin"
private noncomputable def ep00000010011111_1 : Blocks := edgeBlocks% "full/vectors/00000010011111-E-0001.bin"
noncomputable def ep00000010011111 : Blocks := (Blocks.join ep00000010011111_0 ep00000010011111_1)
private theorem idp00000010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001001111.list =
    C ((2:ℤ)^137) * horner X vp00000010011111.list + horner X ep00000010011111.list := by
  exact edge_identity (B := (2:ℤ)^294) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010011111 : Branch 1 (-78761639/1000000 : ℚ) vp0000001001111 := by
  apply branch_checked idp00000010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-78761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-79261639/500000 : ℚ) by norm_num]
  exact coverp00000010011111
theorem coverp0000001001111 : Covers (-78761639/1000000 : ℚ) vp0000001001111 := join_branches bp00000010011110 bp00000010011111
private noncomputable def vp0000001001110111_0 : Blocks := edgeBlocks% "full/vectors/0000001001110111-V-0000.bin"
noncomputable def vp0000001001110111 : Blocks := vp0000001001110111_0
theorem coverp0000001001110111 : Covers (-78636639/125000 : ℚ) vp0000001001110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001110110_0 : Blocks := edgeBlocks% "full/vectors/0000001001110110-V-0000.bin"
noncomputable def vp0000001001110110 : Blocks := vp0000001001110110_0
theorem coverp0000001001110110 : Covers (-78511639/125000 : ℚ) vp0000001001110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100111011_0 : Blocks := edgeBlocks% "full/vectors/000000100111011-V-0000.bin"
noncomputable def vp000000100111011 : Blocks := vp000000100111011_0
private theorem bp0000001001110110 : Branch 0 (-78511639/250000 : ℚ) vp000000100111011 := by
  apply branch_left_normalized (c:=vp0000001001110110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-78511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-78511639/125000 : ℚ) by norm_num]
  exact coverp0000001001110110
private noncomputable def ep0000001001110111_0 : Blocks := edgeBlocks% "full/vectors/0000001001110111-E-0000.bin"
noncomputable def ep0000001001110111 : Blocks := ep0000001001110111_0
private theorem idp0000001001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100111011.list =
    C ((2:ℤ)^49) * horner X vp0000001001110111.list + horner X ep0000001001110111.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001110111 : Branch 1 (-78511639/250000 : ℚ) vp000000100111011 := by
  apply branch_checked idp0000001001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-78511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-78636639/125000 : ℚ) by norm_num]
  exact coverp0000001001110111
theorem coverp000000100111011 : Covers (-78511639/250000 : ℚ) vp000000100111011 := join_branches bp0000001001110110 bp0000001001110111
private noncomputable def vp0000001001110101_0 : Blocks := edgeBlocks% "full/vectors/0000001001110101-V-0000.bin"
noncomputable def vp0000001001110101 : Blocks := vp0000001001110101_0
theorem coverp0000001001110101 : Covers (-78386639/125000 : ℚ) vp0000001001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001110100_0 : Blocks := edgeBlocks% "full/vectors/0000001001110100-V-0000.bin"
noncomputable def vp0000001001110100 : Blocks := vp0000001001110100_0
theorem coverp0000001001110100 : Covers (-78261639/125000 : ℚ) vp0000001001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100111010_0 : Blocks := edgeBlocks% "full/vectors/000000100111010-V-0000.bin"
noncomputable def vp000000100111010 : Blocks := vp000000100111010_0
private theorem bp0000001001110100 : Branch 0 (-78261639/250000 : ℚ) vp000000100111010 := by
  apply branch_left_normalized (c:=vp0000001001110100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-78261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-78261639/125000 : ℚ) by norm_num]
  exact coverp0000001001110100
private noncomputable def ep0000001001110101_0 : Blocks := edgeBlocks% "full/vectors/0000001001110101-E-0000.bin"
noncomputable def ep0000001001110101 : Blocks := ep0000001001110101_0
private theorem idp0000001001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100111010.list =
    C ((2:ℤ)^49) * horner X vp0000001001110101.list + horner X ep0000001001110101.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001110101 : Branch 1 (-78261639/250000 : ℚ) vp000000100111010 := by
  apply branch_checked idp0000001001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-78261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-78386639/125000 : ℚ) by norm_num]
  exact coverp0000001001110101
theorem coverp000000100111010 : Covers (-78261639/250000 : ℚ) vp000000100111010 := join_branches bp0000001001110100 bp0000001001110101
private noncomputable def vp00000010011101_0 : Blocks := edgeBlocks% "full/vectors/00000010011101-V-0000.bin"
noncomputable def vp00000010011101 : Blocks := vp00000010011101_0
private theorem bp000000100111010 : Branch 0 (-78261639/500000 : ℚ) vp00000010011101 := by
  apply branch_left_normalized (c:=vp000000100111010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-78261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-78261639/250000 : ℚ) by norm_num]
  exact coverp000000100111010
private noncomputable def ep000000100111011_0 : Blocks := edgeBlocks% "full/vectors/000000100111011-E-0000.bin"
noncomputable def ep000000100111011 : Blocks := ep000000100111011_0
private theorem idp000000100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010011101.list =
    C ((2:ℤ)^80) * horner X vp000000100111011.list + horner X ep000000100111011.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100111011 : Branch 1 (-78261639/500000 : ℚ) vp00000010011101 := by
  apply branch_checked idp000000100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-78261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-78511639/250000 : ℚ) by norm_num]
  exact coverp000000100111011
theorem coverp00000010011101 : Covers (-78261639/500000 : ℚ) vp00000010011101 := join_branches bp000000100111010 bp000000100111011
private noncomputable def vp0000001001110011_0 : Blocks := edgeBlocks% "full/vectors/0000001001110011-V-0000.bin"
noncomputable def vp0000001001110011 : Blocks := vp0000001001110011_0
theorem coverp0000001001110011 : Covers (-78136639/125000 : ℚ) vp0000001001110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001110010_0 : Blocks := edgeBlocks% "full/vectors/0000001001110010-V-0000.bin"
noncomputable def vp0000001001110010 : Blocks := vp0000001001110010_0
theorem coverp0000001001110010 : Covers (-78011639/125000 : ℚ) vp0000001001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100111001_0 : Blocks := edgeBlocks% "full/vectors/000000100111001-V-0000.bin"
noncomputable def vp000000100111001 : Blocks := vp000000100111001_0
private theorem bp0000001001110010 : Branch 0 (-78011639/250000 : ℚ) vp000000100111001 := by
  apply branch_left_normalized (c:=vp0000001001110010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-78011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-78011639/125000 : ℚ) by norm_num]
  exact coverp0000001001110010
private noncomputable def ep0000001001110011_0 : Blocks := edgeBlocks% "full/vectors/0000001001110011-E-0000.bin"
noncomputable def ep0000001001110011 : Blocks := ep0000001001110011_0
private theorem idp0000001001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100111001.list =
    C ((2:ℤ)^48) * horner X vp0000001001110011.list + horner X ep0000001001110011.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001110011 : Branch 1 (-78011639/250000 : ℚ) vp000000100111001 := by
  apply branch_checked idp0000001001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-78011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-78136639/125000 : ℚ) by norm_num]
  exact coverp0000001001110011
theorem coverp000000100111001 : Covers (-78011639/250000 : ℚ) vp000000100111001 := join_branches bp0000001001110010 bp0000001001110011
private noncomputable def vp0000001001110001_0 : Blocks := edgeBlocks% "full/vectors/0000001001110001-V-0000.bin"
noncomputable def vp0000001001110001 : Blocks := vp0000001001110001_0
theorem coverp0000001001110001 : Covers (-77886639/125000 : ℚ) vp0000001001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001110000_0 : Blocks := edgeBlocks% "full/vectors/0000001001110000-V-0000.bin"
noncomputable def vp0000001001110000 : Blocks := vp0000001001110000_0
theorem coverp0000001001110000 : Covers (-77761639/125000 : ℚ) vp0000001001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100111000_0 : Blocks := edgeBlocks% "full/vectors/000000100111000-V-0000.bin"
noncomputable def vp000000100111000 : Blocks := vp000000100111000_0
private theorem bp0000001001110000 : Branch 0 (-77761639/250000 : ℚ) vp000000100111000 := by
  apply branch_left_normalized (c:=vp0000001001110000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-77761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-77761639/125000 : ℚ) by norm_num]
  exact coverp0000001001110000
private noncomputable def ep0000001001110001_0 : Blocks := edgeBlocks% "full/vectors/0000001001110001-E-0000.bin"
noncomputable def ep0000001001110001 : Blocks := ep0000001001110001_0
private theorem idp0000001001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100111000.list =
    C ((2:ℤ)^48) * horner X vp0000001001110001.list + horner X ep0000001001110001.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001110001 : Branch 1 (-77761639/250000 : ℚ) vp000000100111000 := by
  apply branch_checked idp0000001001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-77761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-77886639/125000 : ℚ) by norm_num]
  exact coverp0000001001110001
theorem coverp000000100111000 : Covers (-77761639/250000 : ℚ) vp000000100111000 := join_branches bp0000001001110000 bp0000001001110001
private noncomputable def vp00000010011100_0 : Blocks := edgeBlocks% "full/vectors/00000010011100-V-0000.bin"
noncomputable def vp00000010011100 : Blocks := vp00000010011100_0
private theorem bp000000100111000 : Branch 0 (-77761639/500000 : ℚ) vp00000010011100 := by
  apply branch_left_normalized (c:=vp000000100111000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-77761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-77761639/250000 : ℚ) by norm_num]
  exact coverp000000100111000
private noncomputable def ep000000100111001_0 : Blocks := edgeBlocks% "full/vectors/000000100111001-E-0000.bin"
noncomputable def ep000000100111001 : Blocks := ep000000100111001_0
private theorem idp000000100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010011100.list =
    C ((2:ℤ)^78) * horner X vp000000100111001.list + horner X ep000000100111001.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100111001 : Branch 1 (-77761639/500000 : ℚ) vp00000010011100 := by
  apply branch_checked idp000000100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-77761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-78011639/250000 : ℚ) by norm_num]
  exact coverp000000100111001
theorem coverp00000010011100 : Covers (-77761639/500000 : ℚ) vp00000010011100 := join_branches bp000000100111000 bp000000100111001
private noncomputable def vp0000001001110_0 : Blocks := edgeBlocks% "full/vectors/0000001001110-V-0000.bin"
private noncomputable def vp0000001001110_1 : Blocks := edgeBlocks% "full/vectors/0000001001110-V-0001.bin"
noncomputable def vp0000001001110 : Blocks := (Blocks.join vp0000001001110_0 vp0000001001110_1)
private theorem bp00000010011100 : Branch 0 (-77761639/1000000 : ℚ) vp0000001001110 := by
  apply branch_left_normalized (c:=vp00000010011100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-77761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-77761639/500000 : ℚ) by norm_num]
  exact coverp00000010011100
private noncomputable def ep00000010011101_0 : Blocks := edgeBlocks% "full/vectors/00000010011101-E-0000.bin"
private noncomputable def ep00000010011101_1 : Blocks := edgeBlocks% "full/vectors/00000010011101-E-0001.bin"
noncomputable def ep00000010011101 : Blocks := (Blocks.join ep00000010011101_0 ep00000010011101_1)
private theorem idp00000010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001001110.list =
    C ((2:ℤ)^135) * horner X vp00000010011101.list + horner X ep00000010011101.list := by
  exact edge_identity (B := (2:ℤ)^294) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010011101 : Branch 1 (-77761639/1000000 : ℚ) vp0000001001110 := by
  apply branch_checked idp00000010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-77761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-78261639/500000 : ℚ) by norm_num]
  exact coverp00000010011101
theorem coverp0000001001110 : Covers (-77761639/1000000 : ℚ) vp0000001001110 := join_branches bp00000010011100 bp00000010011101
private noncomputable def vp000000100111_0 : Blocks := edgeBlocks% "full/vectors/000000100111-V-0000.bin"
private noncomputable def vp000000100111_1 : Blocks := edgeBlocks% "full/vectors/000000100111-V-0001.bin"
noncomputable def vp000000100111 : Blocks := (Blocks.join vp000000100111_0 vp000000100111_1)
private theorem bp0000001001110 : Branch 0 (-77761639/2000000 : ℚ) vp000000100111 := by
  apply branch_left_normalized (c:=vp0000001001110) (k:=0) (m:=133) (by decide +kernel)
  rw [show 2*(-77761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-77761639/1000000 : ℚ) by norm_num]
  exact coverp0000001001110
private noncomputable def ep0000001001111_0 : Blocks := edgeBlocks% "full/vectors/0000001001111-E-0000.bin"
private noncomputable def ep0000001001111_1 : Blocks := edgeBlocks% "full/vectors/0000001001111-E-0001.bin"
noncomputable def ep0000001001111 : Blocks := (Blocks.join ep0000001001111_0 ep0000001001111_1)
private theorem idp0000001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100111.list =
    C ((2:ℤ)^250) * horner X vp0000001001111.list + horner X ep0000001001111.list := by
  exact edge_identity (B := (2:ℤ)^464) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001111 : Branch 1 (-77761639/2000000 : ℚ) vp000000100111 := by
  apply branch_checked idp0000001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-77761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-78761639/1000000 : ℚ) by norm_num]
  exact coverp0000001001111
theorem coverp000000100111 : Covers (-77761639/2000000 : ℚ) vp000000100111 := join_branches bp0000001001110 bp0000001001111
private noncomputable def vp0000001001101111_0 : Blocks := edgeBlocks% "full/vectors/0000001001101111-V-0000.bin"
noncomputable def vp0000001001101111 : Blocks := vp0000001001101111_0
theorem coverp0000001001101111 : Covers (-77636639/125000 : ℚ) vp0000001001101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001101110_0 : Blocks := edgeBlocks% "full/vectors/0000001001101110-V-0000.bin"
noncomputable def vp0000001001101110 : Blocks := vp0000001001101110_0
theorem coverp0000001001101110 : Covers (-77511639/125000 : ℚ) vp0000001001101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100110111_0 : Blocks := edgeBlocks% "full/vectors/000000100110111-V-0000.bin"
noncomputable def vp000000100110111 : Blocks := vp000000100110111_0
private theorem bp0000001001101110 : Branch 0 (-77511639/250000 : ℚ) vp000000100110111 := by
  apply branch_left_normalized (c:=vp0000001001101110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-77511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-77511639/125000 : ℚ) by norm_num]
  exact coverp0000001001101110
private noncomputable def ep0000001001101111_0 : Blocks := edgeBlocks% "full/vectors/0000001001101111-E-0000.bin"
noncomputable def ep0000001001101111 : Blocks := ep0000001001101111_0
private theorem idp0000001001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100110111.list =
    C ((2:ℤ)^48) * horner X vp0000001001101111.list + horner X ep0000001001101111.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001101111 : Branch 1 (-77511639/250000 : ℚ) vp000000100110111 := by
  apply branch_checked idp0000001001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-77511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-77636639/125000 : ℚ) by norm_num]
  exact coverp0000001001101111
theorem coverp000000100110111 : Covers (-77511639/250000 : ℚ) vp000000100110111 := join_branches bp0000001001101110 bp0000001001101111
private noncomputable def vp0000001001101101_0 : Blocks := edgeBlocks% "full/vectors/0000001001101101-V-0000.bin"
noncomputable def vp0000001001101101 : Blocks := vp0000001001101101_0
theorem coverp0000001001101101 : Covers (-77386639/125000 : ℚ) vp0000001001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001101100_0 : Blocks := edgeBlocks% "full/vectors/0000001001101100-V-0000.bin"
noncomputable def vp0000001001101100 : Blocks := vp0000001001101100_0
theorem coverp0000001001101100 : Covers (-77261639/125000 : ℚ) vp0000001001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100110110_0 : Blocks := edgeBlocks% "full/vectors/000000100110110-V-0000.bin"
noncomputable def vp000000100110110 : Blocks := vp000000100110110_0
private theorem bp0000001001101100 : Branch 0 (-77261639/250000 : ℚ) vp000000100110110 := by
  apply branch_left_normalized (c:=vp0000001001101100) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-77261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-77261639/125000 : ℚ) by norm_num]
  exact coverp0000001001101100
private noncomputable def ep0000001001101101_0 : Blocks := edgeBlocks% "full/vectors/0000001001101101-E-0000.bin"
noncomputable def ep0000001001101101 : Blocks := ep0000001001101101_0
private theorem idp0000001001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100110110.list =
    C ((2:ℤ)^48) * horner X vp0000001001101101.list + horner X ep0000001001101101.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001101101 : Branch 1 (-77261639/250000 : ℚ) vp000000100110110 := by
  apply branch_checked idp0000001001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-77261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-77386639/125000 : ℚ) by norm_num]
  exact coverp0000001001101101
theorem coverp000000100110110 : Covers (-77261639/250000 : ℚ) vp000000100110110 := join_branches bp0000001001101100 bp0000001001101101
private noncomputable def vp00000010011011_0 : Blocks := edgeBlocks% "full/vectors/00000010011011-V-0000.bin"
noncomputable def vp00000010011011 : Blocks := vp00000010011011_0
private theorem bp000000100110110 : Branch 0 (-77261639/500000 : ℚ) vp00000010011011 := by
  apply branch_left_normalized (c:=vp000000100110110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-77261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-77261639/250000 : ℚ) by norm_num]
  exact coverp000000100110110
private noncomputable def ep000000100110111_0 : Blocks := edgeBlocks% "full/vectors/000000100110111-E-0000.bin"
noncomputable def ep000000100110111 : Blocks := ep000000100110111_0
private theorem idp000000100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010011011.list =
    C ((2:ℤ)^78) * horner X vp000000100110111.list + horner X ep000000100110111.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100110111 : Branch 1 (-77261639/500000 : ℚ) vp00000010011011 := by
  apply branch_checked idp000000100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-77261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-77511639/250000 : ℚ) by norm_num]
  exact coverp000000100110111
theorem coverp00000010011011 : Covers (-77261639/500000 : ℚ) vp00000010011011 := join_branches bp000000100110110 bp000000100110111
private noncomputable def vp0000001001101011_0 : Blocks := edgeBlocks% "full/vectors/0000001001101011-V-0000.bin"
noncomputable def vp0000001001101011 : Blocks := vp0000001001101011_0
theorem coverp0000001001101011 : Covers (-77136639/125000 : ℚ) vp0000001001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001101010_0 : Blocks := edgeBlocks% "full/vectors/0000001001101010-V-0000.bin"
noncomputable def vp0000001001101010 : Blocks := vp0000001001101010_0
theorem coverp0000001001101010 : Covers (-77011639/125000 : ℚ) vp0000001001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100110101_0 : Blocks := edgeBlocks% "full/vectors/000000100110101-V-0000.bin"
noncomputable def vp000000100110101 : Blocks := vp000000100110101_0
private theorem bp0000001001101010 : Branch 0 (-77011639/250000 : ℚ) vp000000100110101 := by
  apply branch_left_normalized (c:=vp0000001001101010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-77011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-77011639/125000 : ℚ) by norm_num]
  exact coverp0000001001101010
private noncomputable def ep0000001001101011_0 : Blocks := edgeBlocks% "full/vectors/0000001001101011-E-0000.bin"
noncomputable def ep0000001001101011 : Blocks := ep0000001001101011_0
private theorem idp0000001001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100110101.list =
    C ((2:ℤ)^47) * horner X vp0000001001101011.list + horner X ep0000001001101011.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001101011 : Branch 1 (-77011639/250000 : ℚ) vp000000100110101 := by
  apply branch_checked idp0000001001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-77011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-77136639/125000 : ℚ) by norm_num]
  exact coverp0000001001101011
theorem coverp000000100110101 : Covers (-77011639/250000 : ℚ) vp000000100110101 := join_branches bp0000001001101010 bp0000001001101011
private noncomputable def vp0000001001101001_0 : Blocks := edgeBlocks% "full/vectors/0000001001101001-V-0000.bin"
noncomputable def vp0000001001101001 : Blocks := vp0000001001101001_0
theorem coverp0000001001101001 : Covers (-76886639/125000 : ℚ) vp0000001001101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001101000_0 : Blocks := edgeBlocks% "full/vectors/0000001001101000-V-0000.bin"
noncomputable def vp0000001001101000 : Blocks := vp0000001001101000_0
theorem coverp0000001001101000 : Covers (-76761639/125000 : ℚ) vp0000001001101000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100110100_0 : Blocks := edgeBlocks% "full/vectors/000000100110100-V-0000.bin"
noncomputable def vp000000100110100 : Blocks := vp000000100110100_0
private theorem bp0000001001101000 : Branch 0 (-76761639/250000 : ℚ) vp000000100110100 := by
  apply branch_left_normalized (c:=vp0000001001101000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-76761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-76761639/125000 : ℚ) by norm_num]
  exact coverp0000001001101000
private noncomputable def ep0000001001101001_0 : Blocks := edgeBlocks% "full/vectors/0000001001101001-E-0000.bin"
noncomputable def ep0000001001101001 : Blocks := ep0000001001101001_0
private theorem idp0000001001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100110100.list =
    C ((2:ℤ)^49) * horner X vp0000001001101001.list + horner X ep0000001001101001.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001101001 : Branch 1 (-76761639/250000 : ℚ) vp000000100110100 := by
  apply branch_checked idp0000001001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-76761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-76886639/125000 : ℚ) by norm_num]
  exact coverp0000001001101001
theorem coverp000000100110100 : Covers (-76761639/250000 : ℚ) vp000000100110100 := join_branches bp0000001001101000 bp0000001001101001
private noncomputable def vp00000010011010_0 : Blocks := edgeBlocks% "full/vectors/00000010011010-V-0000.bin"
noncomputable def vp00000010011010 : Blocks := vp00000010011010_0
private theorem bp000000100110100 : Branch 0 (-76761639/500000 : ℚ) vp00000010011010 := by
  apply branch_left_normalized (c:=vp000000100110100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-76761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-76761639/250000 : ℚ) by norm_num]
  exact coverp000000100110100
private noncomputable def ep000000100110101_0 : Blocks := edgeBlocks% "full/vectors/000000100110101-E-0000.bin"
noncomputable def ep000000100110101 : Blocks := ep000000100110101_0
private theorem idp000000100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010011010.list =
    C ((2:ℤ)^79) * horner X vp000000100110101.list + horner X ep000000100110101.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100110101 : Branch 1 (-76761639/500000 : ℚ) vp00000010011010 := by
  apply branch_checked idp000000100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-76761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-77011639/250000 : ℚ) by norm_num]
  exact coverp000000100110101
theorem coverp00000010011010 : Covers (-76761639/500000 : ℚ) vp00000010011010 := join_branches bp000000100110100 bp000000100110101
private noncomputable def vp0000001001101_0 : Blocks := edgeBlocks% "full/vectors/0000001001101-V-0000.bin"
private noncomputable def vp0000001001101_1 : Blocks := edgeBlocks% "full/vectors/0000001001101-V-0001.bin"
noncomputable def vp0000001001101 : Blocks := (Blocks.join vp0000001001101_0 vp0000001001101_1)
private theorem bp00000010011010 : Branch 0 (-76761639/1000000 : ℚ) vp0000001001101 := by
  apply branch_left_normalized (c:=vp00000010011010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-76761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-76761639/500000 : ℚ) by norm_num]
  exact coverp00000010011010
private noncomputable def ep00000010011011_0 : Blocks := edgeBlocks% "full/vectors/00000010011011-E-0000.bin"
private noncomputable def ep00000010011011_1 : Blocks := edgeBlocks% "full/vectors/00000010011011-E-0001.bin"
noncomputable def ep00000010011011 : Blocks := (Blocks.join ep00000010011011_0 ep00000010011011_1)
private theorem idp00000010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001001101.list =
    C ((2:ℤ)^137) * horner X vp00000010011011.list + horner X ep00000010011011.list := by
  exact edge_identity (B := (2:ℤ)^294) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010011011 : Branch 1 (-76761639/1000000 : ℚ) vp0000001001101 := by
  apply branch_checked idp00000010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-76761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-77261639/500000 : ℚ) by norm_num]
  exact coverp00000010011011
theorem coverp0000001001101 : Covers (-76761639/1000000 : ℚ) vp0000001001101 := join_branches bp00000010011010 bp00000010011011
private noncomputable def vp0000001001100111_0 : Blocks := edgeBlocks% "full/vectors/0000001001100111-V-0000.bin"
noncomputable def vp0000001001100111 : Blocks := vp0000001001100111_0
theorem coverp0000001001100111 : Covers (-76636639/125000 : ℚ) vp0000001001100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001100110_0 : Blocks := edgeBlocks% "full/vectors/0000001001100110-V-0000.bin"
noncomputable def vp0000001001100110 : Blocks := vp0000001001100110_0
theorem coverp0000001001100110 : Covers (-76511639/125000 : ℚ) vp0000001001100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100110011_0 : Blocks := edgeBlocks% "full/vectors/000000100110011-V-0000.bin"
noncomputable def vp000000100110011 : Blocks := vp000000100110011_0
private theorem bp0000001001100110 : Branch 0 (-76511639/250000 : ℚ) vp000000100110011 := by
  apply branch_left_normalized (c:=vp0000001001100110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-76511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-76511639/125000 : ℚ) by norm_num]
  exact coverp0000001001100110
private noncomputable def ep0000001001100111_0 : Blocks := edgeBlocks% "full/vectors/0000001001100111-E-0000.bin"
noncomputable def ep0000001001100111 : Blocks := ep0000001001100111_0
private theorem idp0000001001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100110011.list =
    C ((2:ℤ)^49) * horner X vp0000001001100111.list + horner X ep0000001001100111.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001100111 : Branch 1 (-76511639/250000 : ℚ) vp000000100110011 := by
  apply branch_checked idp0000001001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-76511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-76636639/125000 : ℚ) by norm_num]
  exact coverp0000001001100111
theorem coverp000000100110011 : Covers (-76511639/250000 : ℚ) vp000000100110011 := join_branches bp0000001001100110 bp0000001001100111
private noncomputable def vp0000001001100101_0 : Blocks := edgeBlocks% "full/vectors/0000001001100101-V-0000.bin"
noncomputable def vp0000001001100101 : Blocks := vp0000001001100101_0
theorem coverp0000001001100101 : Covers (-76386639/125000 : ℚ) vp0000001001100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001100100_0 : Blocks := edgeBlocks% "full/vectors/0000001001100100-V-0000.bin"
noncomputable def vp0000001001100100 : Blocks := vp0000001001100100_0
theorem coverp0000001001100100 : Covers (-76261639/125000 : ℚ) vp0000001001100100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100110010_0 : Blocks := edgeBlocks% "full/vectors/000000100110010-V-0000.bin"
noncomputable def vp000000100110010 : Blocks := vp000000100110010_0
private theorem bp0000001001100100 : Branch 0 (-76261639/250000 : ℚ) vp000000100110010 := by
  apply branch_left_normalized (c:=vp0000001001100100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-76261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-76261639/125000 : ℚ) by norm_num]
  exact coverp0000001001100100
private noncomputable def ep0000001001100101_0 : Blocks := edgeBlocks% "full/vectors/0000001001100101-E-0000.bin"
noncomputable def ep0000001001100101 : Blocks := ep0000001001100101_0
private theorem idp0000001001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100110010.list =
    C ((2:ℤ)^50) * horner X vp0000001001100101.list + horner X ep0000001001100101.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001100101 : Branch 1 (-76261639/250000 : ℚ) vp000000100110010 := by
  apply branch_checked idp0000001001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-76261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-76386639/125000 : ℚ) by norm_num]
  exact coverp0000001001100101
theorem coverp000000100110010 : Covers (-76261639/250000 : ℚ) vp000000100110010 := join_branches bp0000001001100100 bp0000001001100101
private noncomputable def vp00000010011001_0 : Blocks := edgeBlocks% "full/vectors/00000010011001-V-0000.bin"
noncomputable def vp00000010011001 : Blocks := vp00000010011001_0
private theorem bp000000100110010 : Branch 0 (-76261639/500000 : ℚ) vp00000010011001 := by
  apply branch_left_normalized (c:=vp000000100110010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-76261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-76261639/250000 : ℚ) by norm_num]
  exact coverp000000100110010
private noncomputable def ep000000100110011_0 : Blocks := edgeBlocks% "full/vectors/000000100110011-E-0000.bin"
noncomputable def ep000000100110011 : Blocks := ep000000100110011_0
private theorem idp000000100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010011001.list =
    C ((2:ℤ)^81) * horner X vp000000100110011.list + horner X ep000000100110011.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100110011 : Branch 1 (-76261639/500000 : ℚ) vp00000010011001 := by
  apply branch_checked idp000000100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-76261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-76511639/250000 : ℚ) by norm_num]
  exact coverp000000100110011
theorem coverp00000010011001 : Covers (-76261639/500000 : ℚ) vp00000010011001 := join_branches bp000000100110010 bp000000100110011
private noncomputable def vp0000001001100011_0 : Blocks := edgeBlocks% "full/vectors/0000001001100011-V-0000.bin"
noncomputable def vp0000001001100011 : Blocks := vp0000001001100011_0
theorem coverp0000001001100011 : Covers (-76136639/125000 : ℚ) vp0000001001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001100010_0 : Blocks := edgeBlocks% "full/vectors/0000001001100010-V-0000.bin"
noncomputable def vp0000001001100010 : Blocks := vp0000001001100010_0
theorem coverp0000001001100010 : Covers (-76011639/125000 : ℚ) vp0000001001100010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100110001_0 : Blocks := edgeBlocks% "full/vectors/000000100110001-V-0000.bin"
noncomputable def vp000000100110001 : Blocks := vp000000100110001_0
private theorem bp0000001001100010 : Branch 0 (-76011639/250000 : ℚ) vp000000100110001 := by
  apply branch_left_normalized (c:=vp0000001001100010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-76011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-76011639/125000 : ℚ) by norm_num]
  exact coverp0000001001100010
private noncomputable def ep0000001001100011_0 : Blocks := edgeBlocks% "full/vectors/0000001001100011-E-0000.bin"
noncomputable def ep0000001001100011 : Blocks := ep0000001001100011_0
private theorem idp0000001001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100110001.list =
    C ((2:ℤ)^50) * horner X vp0000001001100011.list + horner X ep0000001001100011.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001100011 : Branch 1 (-76011639/250000 : ℚ) vp000000100110001 := by
  apply branch_checked idp0000001001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-76011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-76136639/125000 : ℚ) by norm_num]
  exact coverp0000001001100011
theorem coverp000000100110001 : Covers (-76011639/250000 : ℚ) vp000000100110001 := join_branches bp0000001001100010 bp0000001001100011
private noncomputable def vp0000001001100001_0 : Blocks := edgeBlocks% "full/vectors/0000001001100001-V-0000.bin"
noncomputable def vp0000001001100001 : Blocks := vp0000001001100001_0
theorem coverp0000001001100001 : Covers (-75886639/125000 : ℚ) vp0000001001100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001100000_0 : Blocks := edgeBlocks% "full/vectors/0000001001100000-V-0000.bin"
noncomputable def vp0000001001100000 : Blocks := vp0000001001100000_0
theorem coverp0000001001100000 : Covers (-75761639/125000 : ℚ) vp0000001001100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100110000_0 : Blocks := edgeBlocks% "full/vectors/000000100110000-V-0000.bin"
noncomputable def vp000000100110000 : Blocks := vp000000100110000_0
private theorem bp0000001001100000 : Branch 0 (-75761639/250000 : ℚ) vp000000100110000 := by
  apply branch_left_normalized (c:=vp0000001001100000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-75761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-75761639/125000 : ℚ) by norm_num]
  exact coverp0000001001100000
private noncomputable def ep0000001001100001_0 : Blocks := edgeBlocks% "full/vectors/0000001001100001-E-0000.bin"
noncomputable def ep0000001001100001 : Blocks := ep0000001001100001_0
private theorem idp0000001001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100110000.list =
    C ((2:ℤ)^49) * horner X vp0000001001100001.list + horner X ep0000001001100001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001100001 : Branch 1 (-75761639/250000 : ℚ) vp000000100110000 := by
  apply branch_checked idp0000001001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-75761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-75886639/125000 : ℚ) by norm_num]
  exact coverp0000001001100001
theorem coverp000000100110000 : Covers (-75761639/250000 : ℚ) vp000000100110000 := join_branches bp0000001001100000 bp0000001001100001
private noncomputable def vp00000010011000_0 : Blocks := edgeBlocks% "full/vectors/00000010011000-V-0000.bin"
noncomputable def vp00000010011000 : Blocks := vp00000010011000_0
private theorem bp000000100110000 : Branch 0 (-75761639/500000 : ℚ) vp00000010011000 := by
  apply branch_left_normalized (c:=vp000000100110000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-75761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-75761639/250000 : ℚ) by norm_num]
  exact coverp000000100110000
private noncomputable def ep000000100110001_0 : Blocks := edgeBlocks% "full/vectors/000000100110001-E-0000.bin"
noncomputable def ep000000100110001 : Blocks := ep000000100110001_0
private theorem idp000000100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010011000.list =
    C ((2:ℤ)^79) * horner X vp000000100110001.list + horner X ep000000100110001.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100110001 : Branch 1 (-75761639/500000 : ℚ) vp00000010011000 := by
  apply branch_checked idp000000100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-75761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-76011639/250000 : ℚ) by norm_num]
  exact coverp000000100110001
theorem coverp00000010011000 : Covers (-75761639/500000 : ℚ) vp00000010011000 := join_branches bp000000100110000 bp000000100110001
private noncomputable def vp0000001001100_0 : Blocks := edgeBlocks% "full/vectors/0000001001100-V-0000.bin"
private noncomputable def vp0000001001100_1 : Blocks := edgeBlocks% "full/vectors/0000001001100-V-0001.bin"
noncomputable def vp0000001001100 : Blocks := (Blocks.join vp0000001001100_0 vp0000001001100_1)
private theorem bp00000010011000 : Branch 0 (-75761639/1000000 : ℚ) vp0000001001100 := by
  apply branch_left_normalized (c:=vp00000010011000) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-75761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-75761639/500000 : ℚ) by norm_num]
  exact coverp00000010011000
private noncomputable def ep00000010011001_0 : Blocks := edgeBlocks% "full/vectors/00000010011001-E-0000.bin"
private noncomputable def ep00000010011001_1 : Blocks := edgeBlocks% "full/vectors/00000010011001-E-0001.bin"
noncomputable def ep00000010011001 : Blocks := (Blocks.join ep00000010011001_0 ep00000010011001_1)
private theorem idp00000010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001001100.list =
    C ((2:ℤ)^139) * horner X vp00000010011001.list + horner X ep00000010011001.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010011001 : Branch 1 (-75761639/1000000 : ℚ) vp0000001001100 := by
  apply branch_checked idp00000010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-75761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-76261639/500000 : ℚ) by norm_num]
  exact coverp00000010011001
theorem coverp0000001001100 : Covers (-75761639/1000000 : ℚ) vp0000001001100 := join_branches bp00000010011000 bp00000010011001
private noncomputable def vp000000100110_0 : Blocks := edgeBlocks% "full/vectors/000000100110-V-0000.bin"
private noncomputable def vp000000100110_1 : Blocks := edgeBlocks% "full/vectors/000000100110-V-0001.bin"
noncomputable def vp000000100110 : Blocks := (Blocks.join vp000000100110_0 vp000000100110_1)
private theorem bp0000001001100 : Branch 0 (-75761639/2000000 : ℚ) vp000000100110 := by
  apply branch_left_normalized (c:=vp0000001001100) (k:=0) (m:=135) (by decide +kernel)
  rw [show 2*(-75761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-75761639/1000000 : ℚ) by norm_num]
  exact coverp0000001001100
private noncomputable def ep0000001001101_0 : Blocks := edgeBlocks% "full/vectors/0000001001101-E-0000.bin"
private noncomputable def ep0000001001101_1 : Blocks := edgeBlocks% "full/vectors/0000001001101-E-0001.bin"
noncomputable def ep0000001001101 : Blocks := (Blocks.join ep0000001001101_0 ep0000001001101_1)
private theorem idp0000001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100110.list =
    C ((2:ℤ)^257) * horner X vp0000001001101.list + horner X ep0000001001101.list := by
  exact edge_identity (B := (2:ℤ)^471) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001101 : Branch 1 (-75761639/2000000 : ℚ) vp000000100110 := by
  apply branch_checked idp0000001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-75761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-76761639/1000000 : ℚ) by norm_num]
  exact coverp0000001001101
theorem coverp000000100110 : Covers (-75761639/2000000 : ℚ) vp000000100110 := join_branches bp0000001001100 bp0000001001101
private noncomputable def vp00000010011_0 : Blocks := edgeBlocks% "full/vectors/00000010011-V-0000.bin"
private noncomputable def vp00000010011_1 : Blocks := edgeBlocks% "full/vectors/00000010011-V-0001.bin"
private noncomputable def vp00000010011_2 : Blocks := edgeBlocks% "full/vectors/00000010011-V-0002.bin"
private noncomputable def vp00000010011_3 : Blocks := edgeBlocks% "full/vectors/00000010011-V-0003.bin"
noncomputable def vp00000010011 : Blocks := (Blocks.join (Blocks.join vp00000010011_0 vp00000010011_1) (Blocks.join vp00000010011_2 vp00000010011_3))
private theorem bp000000100110 : Branch 0 (-75761639/4000000 : ℚ) vp00000010011 := by
  apply branch_left_normalized (c:=vp000000100110) (k:=0) (m:=248) (by decide +kernel)
  rw [show 2*(-75761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-75761639/2000000 : ℚ) by norm_num]
  exact coverp000000100110
private noncomputable def ep000000100111_0 : Blocks := edgeBlocks% "full/vectors/000000100111-E-0000.bin"
private noncomputable def ep000000100111_1 : Blocks := edgeBlocks% "full/vectors/000000100111-E-0001.bin"
private noncomputable def ep000000100111_2 : Blocks := edgeBlocks% "full/vectors/000000100111-E-0002.bin"
private noncomputable def ep000000100111_3 : Blocks := edgeBlocks% "full/vectors/000000100111-E-0003.bin"
noncomputable def ep000000100111 : Blocks := (Blocks.join (Blocks.join ep000000100111_0 ep000000100111_1) (Blocks.join ep000000100111_2 ep000000100111_3))
private theorem idp000000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010011.list =
    C ((2:ℤ)^486) * horner X vp000000100111.list + horner X ep000000100111.list := by
  exact edge_identity (B := (2:ℤ)^815) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100111 : Branch 1 (-75761639/4000000 : ℚ) vp00000010011 := by
  apply branch_checked idp000000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-75761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-77761639/2000000 : ℚ) by norm_num]
  exact coverp000000100111
theorem coverp00000010011 : Covers (-75761639/4000000 : ℚ) vp00000010011 := join_branches bp000000100110 bp000000100111
private noncomputable def vp0000001001011111_0 : Blocks := edgeBlocks% "full/vectors/0000001001011111-V-0000.bin"
noncomputable def vp0000001001011111 : Blocks := vp0000001001011111_0
theorem coverp0000001001011111 : Covers (-75636639/125000 : ℚ) vp0000001001011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001011110_0 : Blocks := edgeBlocks% "full/vectors/0000001001011110-V-0000.bin"
noncomputable def vp0000001001011110 : Blocks := vp0000001001011110_0
theorem coverp0000001001011110 : Covers (-75511639/125000 : ℚ) vp0000001001011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100101111_0 : Blocks := edgeBlocks% "full/vectors/000000100101111-V-0000.bin"
noncomputable def vp000000100101111 : Blocks := vp000000100101111_0
private theorem bp0000001001011110 : Branch 0 (-75511639/250000 : ℚ) vp000000100101111 := by
  apply branch_left_normalized (c:=vp0000001001011110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-75511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-75511639/125000 : ℚ) by norm_num]
  exact coverp0000001001011110
private noncomputable def ep0000001001011111_0 : Blocks := edgeBlocks% "full/vectors/0000001001011111-E-0000.bin"
noncomputable def ep0000001001011111 : Blocks := ep0000001001011111_0
private theorem idp0000001001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100101111.list =
    C ((2:ℤ)^48) * horner X vp0000001001011111.list + horner X ep0000001001011111.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001011111 : Branch 1 (-75511639/250000 : ℚ) vp000000100101111 := by
  apply branch_checked idp0000001001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-75511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-75636639/125000 : ℚ) by norm_num]
  exact coverp0000001001011111
theorem coverp000000100101111 : Covers (-75511639/250000 : ℚ) vp000000100101111 := join_branches bp0000001001011110 bp0000001001011111
private noncomputable def vp0000001001011101_0 : Blocks := edgeBlocks% "full/vectors/0000001001011101-V-0000.bin"
noncomputable def vp0000001001011101 : Blocks := vp0000001001011101_0
theorem coverp0000001001011101 : Covers (-75386639/125000 : ℚ) vp0000001001011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001011100_0 : Blocks := edgeBlocks% "full/vectors/0000001001011100-V-0000.bin"
noncomputable def vp0000001001011100 : Blocks := vp0000001001011100_0
theorem coverp0000001001011100 : Covers (-75261639/125000 : ℚ) vp0000001001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100101110_0 : Blocks := edgeBlocks% "full/vectors/000000100101110-V-0000.bin"
noncomputable def vp000000100101110 : Blocks := vp000000100101110_0
private theorem bp0000001001011100 : Branch 0 (-75261639/250000 : ℚ) vp000000100101110 := by
  apply branch_left_normalized (c:=vp0000001001011100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-75261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-75261639/125000 : ℚ) by norm_num]
  exact coverp0000001001011100
private noncomputable def ep0000001001011101_0 : Blocks := edgeBlocks% "full/vectors/0000001001011101-E-0000.bin"
noncomputable def ep0000001001011101 : Blocks := ep0000001001011101_0
private theorem idp0000001001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100101110.list =
    C ((2:ℤ)^48) * horner X vp0000001001011101.list + horner X ep0000001001011101.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001011101 : Branch 1 (-75261639/250000 : ℚ) vp000000100101110 := by
  apply branch_checked idp0000001001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-75261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-75386639/125000 : ℚ) by norm_num]
  exact coverp0000001001011101
theorem coverp000000100101110 : Covers (-75261639/250000 : ℚ) vp000000100101110 := join_branches bp0000001001011100 bp0000001001011101
private noncomputable def vp00000010010111_0 : Blocks := edgeBlocks% "full/vectors/00000010010111-V-0000.bin"
noncomputable def vp00000010010111 : Blocks := vp00000010010111_0
private theorem bp000000100101110 : Branch 0 (-75261639/500000 : ℚ) vp00000010010111 := by
  apply branch_left_normalized (c:=vp000000100101110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-75261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-75261639/250000 : ℚ) by norm_num]
  exact coverp000000100101110
private noncomputable def ep000000100101111_0 : Blocks := edgeBlocks% "full/vectors/000000100101111-E-0000.bin"
noncomputable def ep000000100101111 : Blocks := ep000000100101111_0
private theorem idp000000100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010010111.list =
    C ((2:ℤ)^78) * horner X vp000000100101111.list + horner X ep000000100101111.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100101111 : Branch 1 (-75261639/500000 : ℚ) vp00000010010111 := by
  apply branch_checked idp000000100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-75261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-75511639/250000 : ℚ) by norm_num]
  exact coverp000000100101111
theorem coverp00000010010111 : Covers (-75261639/500000 : ℚ) vp00000010010111 := join_branches bp000000100101110 bp000000100101111
private noncomputable def vp0000001001011011_0 : Blocks := edgeBlocks% "full/vectors/0000001001011011-V-0000.bin"
noncomputable def vp0000001001011011 : Blocks := vp0000001001011011_0
theorem coverp0000001001011011 : Covers (-75136639/125000 : ℚ) vp0000001001011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001011010_0 : Blocks := edgeBlocks% "full/vectors/0000001001011010-V-0000.bin"
noncomputable def vp0000001001011010 : Blocks := vp0000001001011010_0
theorem coverp0000001001011010 : Covers (-75011639/125000 : ℚ) vp0000001001011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100101101_0 : Blocks := edgeBlocks% "full/vectors/000000100101101-V-0000.bin"
noncomputable def vp000000100101101 : Blocks := vp000000100101101_0
private theorem bp0000001001011010 : Branch 0 (-75011639/250000 : ℚ) vp000000100101101 := by
  apply branch_left_normalized (c:=vp0000001001011010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-75011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-75011639/125000 : ℚ) by norm_num]
  exact coverp0000001001011010
private noncomputable def ep0000001001011011_0 : Blocks := edgeBlocks% "full/vectors/0000001001011011-E-0000.bin"
noncomputable def ep0000001001011011 : Blocks := ep0000001001011011_0
private theorem idp0000001001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100101101.list =
    C ((2:ℤ)^48) * horner X vp0000001001011011.list + horner X ep0000001001011011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001011011 : Branch 1 (-75011639/250000 : ℚ) vp000000100101101 := by
  apply branch_checked idp0000001001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-75011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-75136639/125000 : ℚ) by norm_num]
  exact coverp0000001001011011
theorem coverp000000100101101 : Covers (-75011639/250000 : ℚ) vp000000100101101 := join_branches bp0000001001011010 bp0000001001011011
private noncomputable def vp0000001001011001_0 : Blocks := edgeBlocks% "full/vectors/0000001001011001-V-0000.bin"
noncomputable def vp0000001001011001 : Blocks := vp0000001001011001_0
theorem coverp0000001001011001 : Covers (-74886639/125000 : ℚ) vp0000001001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001011000_0 : Blocks := edgeBlocks% "full/vectors/0000001001011000-V-0000.bin"
noncomputable def vp0000001001011000 : Blocks := vp0000001001011000_0
theorem coverp0000001001011000 : Covers (-74761639/125000 : ℚ) vp0000001001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100101100_0 : Blocks := edgeBlocks% "full/vectors/000000100101100-V-0000.bin"
noncomputable def vp000000100101100 : Blocks := vp000000100101100_0
private theorem bp0000001001011000 : Branch 0 (-74761639/250000 : ℚ) vp000000100101100 := by
  apply branch_left_normalized (c:=vp0000001001011000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-74761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-74761639/125000 : ℚ) by norm_num]
  exact coverp0000001001011000
private noncomputable def ep0000001001011001_0 : Blocks := edgeBlocks% "full/vectors/0000001001011001-E-0000.bin"
noncomputable def ep0000001001011001 : Blocks := ep0000001001011001_0
private theorem idp0000001001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100101100.list =
    C ((2:ℤ)^48) * horner X vp0000001001011001.list + horner X ep0000001001011001.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001011001 : Branch 1 (-74761639/250000 : ℚ) vp000000100101100 := by
  apply branch_checked idp0000001001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-74761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-74886639/125000 : ℚ) by norm_num]
  exact coverp0000001001011001
theorem coverp000000100101100 : Covers (-74761639/250000 : ℚ) vp000000100101100 := join_branches bp0000001001011000 bp0000001001011001
private noncomputable def vp00000010010110_0 : Blocks := edgeBlocks% "full/vectors/00000010010110-V-0000.bin"
noncomputable def vp00000010010110 : Blocks := vp00000010010110_0
private theorem bp000000100101100 : Branch 0 (-74761639/500000 : ℚ) vp00000010010110 := by
  apply branch_left_normalized (c:=vp000000100101100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-74761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-74761639/250000 : ℚ) by norm_num]
  exact coverp000000100101100
private noncomputable def ep000000100101101_0 : Blocks := edgeBlocks% "full/vectors/000000100101101-E-0000.bin"
noncomputable def ep000000100101101 : Blocks := ep000000100101101_0
private theorem idp000000100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010010110.list =
    C ((2:ℤ)^79) * horner X vp000000100101101.list + horner X ep000000100101101.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100101101 : Branch 1 (-74761639/500000 : ℚ) vp00000010010110 := by
  apply branch_checked idp000000100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-74761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-75011639/250000 : ℚ) by norm_num]
  exact coverp000000100101101
theorem coverp00000010010110 : Covers (-74761639/500000 : ℚ) vp00000010010110 := join_branches bp000000100101100 bp000000100101101
private noncomputable def vp0000001001011_0 : Blocks := edgeBlocks% "full/vectors/0000001001011-V-0000.bin"
private noncomputable def vp0000001001011_1 : Blocks := edgeBlocks% "full/vectors/0000001001011-V-0001.bin"
noncomputable def vp0000001001011 : Blocks := (Blocks.join vp0000001001011_0 vp0000001001011_1)
private theorem bp00000010010110 : Branch 0 (-74761639/1000000 : ℚ) vp0000001001011 := by
  apply branch_left_normalized (c:=vp00000010010110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-74761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-74761639/500000 : ℚ) by norm_num]
  exact coverp00000010010110
private noncomputable def ep00000010010111_0 : Blocks := edgeBlocks% "full/vectors/00000010010111-E-0000.bin"
private noncomputable def ep00000010010111_1 : Blocks := edgeBlocks% "full/vectors/00000010010111-E-0001.bin"
noncomputable def ep00000010010111 : Blocks := (Blocks.join ep00000010010111_0 ep00000010010111_1)
private theorem idp00000010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001001011.list =
    C ((2:ℤ)^137) * horner X vp00000010010111.list + horner X ep00000010010111.list := by
  exact edge_identity (B := (2:ℤ)^295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010010111 : Branch 1 (-74761639/1000000 : ℚ) vp0000001001011 := by
  apply branch_checked idp00000010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-74761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-75261639/500000 : ℚ) by norm_num]
  exact coverp00000010010111
theorem coverp0000001001011 : Covers (-74761639/1000000 : ℚ) vp0000001001011 := join_branches bp00000010010110 bp00000010010111
private noncomputable def vp0000001001010111_0 : Blocks := edgeBlocks% "full/vectors/0000001001010111-V-0000.bin"
noncomputable def vp0000001001010111 : Blocks := vp0000001001010111_0
theorem coverp0000001001010111 : Covers (-74636639/125000 : ℚ) vp0000001001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001010110_0 : Blocks := edgeBlocks% "full/vectors/0000001001010110-V-0000.bin"
noncomputable def vp0000001001010110 : Blocks := vp0000001001010110_0
theorem coverp0000001001010110 : Covers (-74511639/125000 : ℚ) vp0000001001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100101011_0 : Blocks := edgeBlocks% "full/vectors/000000100101011-V-0000.bin"
noncomputable def vp000000100101011 : Blocks := vp000000100101011_0
private theorem bp0000001001010110 : Branch 0 (-74511639/250000 : ℚ) vp000000100101011 := by
  apply branch_left_normalized (c:=vp0000001001010110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-74511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-74511639/125000 : ℚ) by norm_num]
  exact coverp0000001001010110
private noncomputable def ep0000001001010111_0 : Blocks := edgeBlocks% "full/vectors/0000001001010111-E-0000.bin"
noncomputable def ep0000001001010111 : Blocks := ep0000001001010111_0
private theorem idp0000001001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100101011.list =
    C ((2:ℤ)^49) * horner X vp0000001001010111.list + horner X ep0000001001010111.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001010111 : Branch 1 (-74511639/250000 : ℚ) vp000000100101011 := by
  apply branch_checked idp0000001001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-74511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-74636639/125000 : ℚ) by norm_num]
  exact coverp0000001001010111
theorem coverp000000100101011 : Covers (-74511639/250000 : ℚ) vp000000100101011 := join_branches bp0000001001010110 bp0000001001010111
private noncomputable def vp0000001001010101_0 : Blocks := edgeBlocks% "full/vectors/0000001001010101-V-0000.bin"
noncomputable def vp0000001001010101 : Blocks := vp0000001001010101_0
theorem coverp0000001001010101 : Covers (-74386639/125000 : ℚ) vp0000001001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001010100_0 : Blocks := edgeBlocks% "full/vectors/0000001001010100-V-0000.bin"
noncomputable def vp0000001001010100 : Blocks := vp0000001001010100_0
theorem coverp0000001001010100 : Covers (-74261639/125000 : ℚ) vp0000001001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100101010_0 : Blocks := edgeBlocks% "full/vectors/000000100101010-V-0000.bin"
noncomputable def vp000000100101010 : Blocks := vp000000100101010_0
private theorem bp0000001001010100 : Branch 0 (-74261639/250000 : ℚ) vp000000100101010 := by
  apply branch_left_normalized (c:=vp0000001001010100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-74261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-74261639/125000 : ℚ) by norm_num]
  exact coverp0000001001010100
private noncomputable def ep0000001001010101_0 : Blocks := edgeBlocks% "full/vectors/0000001001010101-E-0000.bin"
noncomputable def ep0000001001010101 : Blocks := ep0000001001010101_0
private theorem idp0000001001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100101010.list =
    C ((2:ℤ)^49) * horner X vp0000001001010101.list + horner X ep0000001001010101.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001010101 : Branch 1 (-74261639/250000 : ℚ) vp000000100101010 := by
  apply branch_checked idp0000001001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-74261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-74386639/125000 : ℚ) by norm_num]
  exact coverp0000001001010101
theorem coverp000000100101010 : Covers (-74261639/250000 : ℚ) vp000000100101010 := join_branches bp0000001001010100 bp0000001001010101
private noncomputable def vp00000010010101_0 : Blocks := edgeBlocks% "full/vectors/00000010010101-V-0000.bin"
noncomputable def vp00000010010101 : Blocks := vp00000010010101_0
private theorem bp000000100101010 : Branch 0 (-74261639/500000 : ℚ) vp00000010010101 := by
  apply branch_left_normalized (c:=vp000000100101010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-74261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-74261639/250000 : ℚ) by norm_num]
  exact coverp000000100101010
private noncomputable def ep000000100101011_0 : Blocks := edgeBlocks% "full/vectors/000000100101011-E-0000.bin"
noncomputable def ep000000100101011 : Blocks := ep000000100101011_0
private theorem idp000000100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010010101.list =
    C ((2:ℤ)^80) * horner X vp000000100101011.list + horner X ep000000100101011.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100101011 : Branch 1 (-74261639/500000 : ℚ) vp00000010010101 := by
  apply branch_checked idp000000100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-74261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-74511639/250000 : ℚ) by norm_num]
  exact coverp000000100101011
theorem coverp00000010010101 : Covers (-74261639/500000 : ℚ) vp00000010010101 := join_branches bp000000100101010 bp000000100101011
private noncomputable def vp0000001001010011_0 : Blocks := edgeBlocks% "full/vectors/0000001001010011-V-0000.bin"
noncomputable def vp0000001001010011 : Blocks := vp0000001001010011_0
theorem coverp0000001001010011 : Covers (-74136639/125000 : ℚ) vp0000001001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001010010_0 : Blocks := edgeBlocks% "full/vectors/0000001001010010-V-0000.bin"
noncomputable def vp0000001001010010 : Blocks := vp0000001001010010_0
theorem coverp0000001001010010 : Covers (-74011639/125000 : ℚ) vp0000001001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100101001_0 : Blocks := edgeBlocks% "full/vectors/000000100101001-V-0000.bin"
noncomputable def vp000000100101001 : Blocks := vp000000100101001_0
private theorem bp0000001001010010 : Branch 0 (-74011639/250000 : ℚ) vp000000100101001 := by
  apply branch_left_normalized (c:=vp0000001001010010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-74011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-74011639/125000 : ℚ) by norm_num]
  exact coverp0000001001010010
private noncomputable def ep0000001001010011_0 : Blocks := edgeBlocks% "full/vectors/0000001001010011-E-0000.bin"
noncomputable def ep0000001001010011 : Blocks := ep0000001001010011_0
private theorem idp0000001001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100101001.list =
    C ((2:ℤ)^50) * horner X vp0000001001010011.list + horner X ep0000001001010011.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001010011 : Branch 1 (-74011639/250000 : ℚ) vp000000100101001 := by
  apply branch_checked idp0000001001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-74011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-74136639/125000 : ℚ) by norm_num]
  exact coverp0000001001010011
theorem coverp000000100101001 : Covers (-74011639/250000 : ℚ) vp000000100101001 := join_branches bp0000001001010010 bp0000001001010011
private noncomputable def vp0000001001010001_0 : Blocks := edgeBlocks% "full/vectors/0000001001010001-V-0000.bin"
noncomputable def vp0000001001010001 : Blocks := vp0000001001010001_0
theorem coverp0000001001010001 : Covers (-73886639/125000 : ℚ) vp0000001001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001010000_0 : Blocks := edgeBlocks% "full/vectors/0000001001010000-V-0000.bin"
noncomputable def vp0000001001010000 : Blocks := vp0000001001010000_0
theorem coverp0000001001010000 : Covers (-73761639/125000 : ℚ) vp0000001001010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100101000_0 : Blocks := edgeBlocks% "full/vectors/000000100101000-V-0000.bin"
noncomputable def vp000000100101000 : Blocks := vp000000100101000_0
private theorem bp0000001001010000 : Branch 0 (-73761639/250000 : ℚ) vp000000100101000 := by
  apply branch_left_normalized (c:=vp0000001001010000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-73761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-73761639/125000 : ℚ) by norm_num]
  exact coverp0000001001010000
private noncomputable def ep0000001001010001_0 : Blocks := edgeBlocks% "full/vectors/0000001001010001-E-0000.bin"
noncomputable def ep0000001001010001 : Blocks := ep0000001001010001_0
private theorem idp0000001001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100101000.list =
    C ((2:ℤ)^50) * horner X vp0000001001010001.list + horner X ep0000001001010001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001010001 : Branch 1 (-73761639/250000 : ℚ) vp000000100101000 := by
  apply branch_checked idp0000001001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-73761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-73886639/125000 : ℚ) by norm_num]
  exact coverp0000001001010001
theorem coverp000000100101000 : Covers (-73761639/250000 : ℚ) vp000000100101000 := join_branches bp0000001001010000 bp0000001001010001
private noncomputable def vp00000010010100_0 : Blocks := edgeBlocks% "full/vectors/00000010010100-V-0000.bin"
noncomputable def vp00000010010100 : Blocks := vp00000010010100_0
private theorem bp000000100101000 : Branch 0 (-73761639/500000 : ℚ) vp00000010010100 := by
  apply branch_left_normalized (c:=vp000000100101000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-73761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-73761639/250000 : ℚ) by norm_num]
  exact coverp000000100101000
private noncomputable def ep000000100101001_0 : Blocks := edgeBlocks% "full/vectors/000000100101001-E-0000.bin"
noncomputable def ep000000100101001 : Blocks := ep000000100101001_0
private theorem idp000000100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010010100.list =
    C ((2:ℤ)^81) * horner X vp000000100101001.list + horner X ep000000100101001.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100101001 : Branch 1 (-73761639/500000 : ℚ) vp00000010010100 := by
  apply branch_checked idp000000100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-73761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-74011639/250000 : ℚ) by norm_num]
  exact coverp000000100101001
theorem coverp00000010010100 : Covers (-73761639/500000 : ℚ) vp00000010010100 := join_branches bp000000100101000 bp000000100101001
private noncomputable def vp0000001001010_0 : Blocks := edgeBlocks% "full/vectors/0000001001010-V-0000.bin"
private noncomputable def vp0000001001010_1 : Blocks := edgeBlocks% "full/vectors/0000001001010-V-0001.bin"
noncomputable def vp0000001001010 : Blocks := (Blocks.join vp0000001001010_0 vp0000001001010_1)
private theorem bp00000010010100 : Branch 0 (-73761639/1000000 : ℚ) vp0000001001010 := by
  apply branch_left_normalized (c:=vp00000010010100) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-73761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-73761639/500000 : ℚ) by norm_num]
  exact coverp00000010010100
private noncomputable def ep00000010010101_0 : Blocks := edgeBlocks% "full/vectors/00000010010101-E-0000.bin"
private noncomputable def ep00000010010101_1 : Blocks := edgeBlocks% "full/vectors/00000010010101-E-0001.bin"
noncomputable def ep00000010010101 : Blocks := (Blocks.join ep00000010010101_0 ep00000010010101_1)
private theorem idp00000010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001001010.list =
    C ((2:ℤ)^143) * horner X vp00000010010101.list + horner X ep00000010010101.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010010101 : Branch 1 (-73761639/1000000 : ℚ) vp0000001001010 := by
  apply branch_checked idp00000010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-73761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-74261639/500000 : ℚ) by norm_num]
  exact coverp00000010010101
theorem coverp0000001001010 : Covers (-73761639/1000000 : ℚ) vp0000001001010 := join_branches bp00000010010100 bp00000010010101
private noncomputable def vp000000100101_0 : Blocks := edgeBlocks% "full/vectors/000000100101-V-0000.bin"
private noncomputable def vp000000100101_1 : Blocks := edgeBlocks% "full/vectors/000000100101-V-0001.bin"
noncomputable def vp000000100101 : Blocks := (Blocks.join vp000000100101_0 vp000000100101_1)
private theorem bp0000001001010 : Branch 0 (-73761639/2000000 : ℚ) vp000000100101 := by
  apply branch_left_normalized (c:=vp0000001001010) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-73761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-73761639/1000000 : ℚ) by norm_num]
  exact coverp0000001001010
private noncomputable def ep0000001001011_0 : Blocks := edgeBlocks% "full/vectors/0000001001011-E-0000.bin"
private noncomputable def ep0000001001011_1 : Blocks := edgeBlocks% "full/vectors/0000001001011-E-0001.bin"
noncomputable def ep0000001001011 : Blocks := (Blocks.join ep0000001001011_0 ep0000001001011_1)
private theorem idp0000001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100101.list =
    C ((2:ℤ)^262) * horner X vp0000001001011.list + horner X ep0000001001011.list := by
  exact edge_identity (B := (2:ℤ)^478) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001011 : Branch 1 (-73761639/2000000 : ℚ) vp000000100101 := by
  apply branch_checked idp0000001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-73761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-74761639/1000000 : ℚ) by norm_num]
  exact coverp0000001001011
theorem coverp000000100101 : Covers (-73761639/2000000 : ℚ) vp000000100101 := join_branches bp0000001001010 bp0000001001011
private noncomputable def vp0000001001001111_0 : Blocks := edgeBlocks% "full/vectors/0000001001001111-V-0000.bin"
noncomputable def vp0000001001001111 : Blocks := vp0000001001001111_0
theorem coverp0000001001001111 : Covers (-73636639/125000 : ℚ) vp0000001001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001001110_0 : Blocks := edgeBlocks% "full/vectors/0000001001001110-V-0000.bin"
noncomputable def vp0000001001001110 : Blocks := vp0000001001001110_0
theorem coverp0000001001001110 : Covers (-73511639/125000 : ℚ) vp0000001001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100100111_0 : Blocks := edgeBlocks% "full/vectors/000000100100111-V-0000.bin"
noncomputable def vp000000100100111 : Blocks := vp000000100100111_0
private theorem bp0000001001001110 : Branch 0 (-73511639/250000 : ℚ) vp000000100100111 := by
  apply branch_left_normalized (c:=vp0000001001001110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-73511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-73511639/125000 : ℚ) by norm_num]
  exact coverp0000001001001110
private noncomputable def ep0000001001001111_0 : Blocks := edgeBlocks% "full/vectors/0000001001001111-E-0000.bin"
noncomputable def ep0000001001001111 : Blocks := ep0000001001001111_0
private theorem idp0000001001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100100111.list =
    C ((2:ℤ)^48) * horner X vp0000001001001111.list + horner X ep0000001001001111.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001001111 : Branch 1 (-73511639/250000 : ℚ) vp000000100100111 := by
  apply branch_checked idp0000001001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-73511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-73636639/125000 : ℚ) by norm_num]
  exact coverp0000001001001111
theorem coverp000000100100111 : Covers (-73511639/250000 : ℚ) vp000000100100111 := join_branches bp0000001001001110 bp0000001001001111
private noncomputable def vp0000001001001101_0 : Blocks := edgeBlocks% "full/vectors/0000001001001101-V-0000.bin"
noncomputable def vp0000001001001101 : Blocks := vp0000001001001101_0
theorem coverp0000001001001101 : Covers (-73386639/125000 : ℚ) vp0000001001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001001100_0 : Blocks := edgeBlocks% "full/vectors/0000001001001100-V-0000.bin"
noncomputable def vp0000001001001100 : Blocks := vp0000001001001100_0
theorem coverp0000001001001100 : Covers (-73261639/125000 : ℚ) vp0000001001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100100110_0 : Blocks := edgeBlocks% "full/vectors/000000100100110-V-0000.bin"
noncomputable def vp000000100100110 : Blocks := vp000000100100110_0
private theorem bp0000001001001100 : Branch 0 (-73261639/250000 : ℚ) vp000000100100110 := by
  apply branch_left_normalized (c:=vp0000001001001100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-73261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-73261639/125000 : ℚ) by norm_num]
  exact coverp0000001001001100
private noncomputable def ep0000001001001101_0 : Blocks := edgeBlocks% "full/vectors/0000001001001101-E-0000.bin"
noncomputable def ep0000001001001101 : Blocks := ep0000001001001101_0
private theorem idp0000001001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100100110.list =
    C ((2:ℤ)^48) * horner X vp0000001001001101.list + horner X ep0000001001001101.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001001101 : Branch 1 (-73261639/250000 : ℚ) vp000000100100110 := by
  apply branch_checked idp0000001001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-73261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-73386639/125000 : ℚ) by norm_num]
  exact coverp0000001001001101
theorem coverp000000100100110 : Covers (-73261639/250000 : ℚ) vp000000100100110 := join_branches bp0000001001001100 bp0000001001001101
private noncomputable def vp00000010010011_0 : Blocks := edgeBlocks% "full/vectors/00000010010011-V-0000.bin"
noncomputable def vp00000010010011 : Blocks := vp00000010010011_0
private theorem bp000000100100110 : Branch 0 (-73261639/500000 : ℚ) vp00000010010011 := by
  apply branch_left_normalized (c:=vp000000100100110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-73261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-73261639/250000 : ℚ) by norm_num]
  exact coverp000000100100110
private noncomputable def ep000000100100111_0 : Blocks := edgeBlocks% "full/vectors/000000100100111-E-0000.bin"
noncomputable def ep000000100100111 : Blocks := ep000000100100111_0
private theorem idp000000100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010010011.list =
    C ((2:ℤ)^78) * horner X vp000000100100111.list + horner X ep000000100100111.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100100111 : Branch 1 (-73261639/500000 : ℚ) vp00000010010011 := by
  apply branch_checked idp000000100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-73261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-73511639/250000 : ℚ) by norm_num]
  exact coverp000000100100111
theorem coverp00000010010011 : Covers (-73261639/500000 : ℚ) vp00000010010011 := join_branches bp000000100100110 bp000000100100111
private noncomputable def vp0000001001001011_0 : Blocks := edgeBlocks% "full/vectors/0000001001001011-V-0000.bin"
noncomputable def vp0000001001001011 : Blocks := vp0000001001001011_0
theorem coverp0000001001001011 : Covers (-73136639/125000 : ℚ) vp0000001001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001001010_0 : Blocks := edgeBlocks% "full/vectors/0000001001001010-V-0000.bin"
noncomputable def vp0000001001001010 : Blocks := vp0000001001001010_0
theorem coverp0000001001001010 : Covers (-73011639/125000 : ℚ) vp0000001001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100100101_0 : Blocks := edgeBlocks% "full/vectors/000000100100101-V-0000.bin"
noncomputable def vp000000100100101 : Blocks := vp000000100100101_0
private theorem bp0000001001001010 : Branch 0 (-73011639/250000 : ℚ) vp000000100100101 := by
  apply branch_left_normalized (c:=vp0000001001001010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-73011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-73011639/125000 : ℚ) by norm_num]
  exact coverp0000001001001010
private noncomputable def ep0000001001001011_0 : Blocks := edgeBlocks% "full/vectors/0000001001001011-E-0000.bin"
noncomputable def ep0000001001001011 : Blocks := ep0000001001001011_0
private theorem idp0000001001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100100101.list =
    C ((2:ℤ)^49) * horner X vp0000001001001011.list + horner X ep0000001001001011.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001001011 : Branch 1 (-73011639/250000 : ℚ) vp000000100100101 := by
  apply branch_checked idp0000001001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-73011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-73136639/125000 : ℚ) by norm_num]
  exact coverp0000001001001011
theorem coverp000000100100101 : Covers (-73011639/250000 : ℚ) vp000000100100101 := join_branches bp0000001001001010 bp0000001001001011
private noncomputable def vp0000001001001001_0 : Blocks := edgeBlocks% "full/vectors/0000001001001001-V-0000.bin"
noncomputable def vp0000001001001001 : Blocks := vp0000001001001001_0
theorem coverp0000001001001001 : Covers (-72886639/125000 : ℚ) vp0000001001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001001000_0 : Blocks := edgeBlocks% "full/vectors/0000001001001000-V-0000.bin"
noncomputable def vp0000001001001000 : Blocks := vp0000001001001000_0
theorem coverp0000001001001000 : Covers (-72761639/125000 : ℚ) vp0000001001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100100100_0 : Blocks := edgeBlocks% "full/vectors/000000100100100-V-0000.bin"
noncomputable def vp000000100100100 : Blocks := vp000000100100100_0
private theorem bp0000001001001000 : Branch 0 (-72761639/250000 : ℚ) vp000000100100100 := by
  apply branch_left_normalized (c:=vp0000001001001000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-72761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-72761639/125000 : ℚ) by norm_num]
  exact coverp0000001001001000
private noncomputable def ep0000001001001001_0 : Blocks := edgeBlocks% "full/vectors/0000001001001001-E-0000.bin"
noncomputable def ep0000001001001001 : Blocks := ep0000001001001001_0
private theorem idp0000001001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100100100.list =
    C ((2:ℤ)^49) * horner X vp0000001001001001.list + horner X ep0000001001001001.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001001001 : Branch 1 (-72761639/250000 : ℚ) vp000000100100100 := by
  apply branch_checked idp0000001001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-72761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-72886639/125000 : ℚ) by norm_num]
  exact coverp0000001001001001
theorem coverp000000100100100 : Covers (-72761639/250000 : ℚ) vp000000100100100 := join_branches bp0000001001001000 bp0000001001001001
private noncomputable def vp00000010010010_0 : Blocks := edgeBlocks% "full/vectors/00000010010010-V-0000.bin"
noncomputable def vp00000010010010 : Blocks := vp00000010010010_0
private theorem bp000000100100100 : Branch 0 (-72761639/500000 : ℚ) vp00000010010010 := by
  apply branch_left_normalized (c:=vp000000100100100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-72761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-72761639/250000 : ℚ) by norm_num]
  exact coverp000000100100100
private noncomputable def ep000000100100101_0 : Blocks := edgeBlocks% "full/vectors/000000100100101-E-0000.bin"
noncomputable def ep000000100100101 : Blocks := ep000000100100101_0
private theorem idp000000100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010010010.list =
    C ((2:ℤ)^79) * horner X vp000000100100101.list + horner X ep000000100100101.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100100101 : Branch 1 (-72761639/500000 : ℚ) vp00000010010010 := by
  apply branch_checked idp000000100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-72761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-73011639/250000 : ℚ) by norm_num]
  exact coverp000000100100101
theorem coverp00000010010010 : Covers (-72761639/500000 : ℚ) vp00000010010010 := join_branches bp000000100100100 bp000000100100101
private noncomputable def vp0000001001001_0 : Blocks := edgeBlocks% "full/vectors/0000001001001-V-0000.bin"
private noncomputable def vp0000001001001_1 : Blocks := edgeBlocks% "full/vectors/0000001001001-V-0001.bin"
noncomputable def vp0000001001001 : Blocks := (Blocks.join vp0000001001001_0 vp0000001001001_1)
private theorem bp00000010010010 : Branch 0 (-72761639/1000000 : ℚ) vp0000001001001 := by
  apply branch_left_normalized (c:=vp00000010010010) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-72761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-72761639/500000 : ℚ) by norm_num]
  exact coverp00000010010010
private noncomputable def ep00000010010011_0 : Blocks := edgeBlocks% "full/vectors/00000010010011-E-0000.bin"
private noncomputable def ep00000010010011_1 : Blocks := edgeBlocks% "full/vectors/00000010010011-E-0001.bin"
noncomputable def ep00000010010011 : Blocks := (Blocks.join ep00000010010011_0 ep00000010010011_1)
private theorem idp00000010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001001001.list =
    C ((2:ℤ)^139) * horner X vp00000010010011.list + horner X ep00000010010011.list := by
  exact edge_identity (B := (2:ℤ)^298) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010010011 : Branch 1 (-72761639/1000000 : ℚ) vp0000001001001 := by
  apply branch_checked idp00000010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-72761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-73261639/500000 : ℚ) by norm_num]
  exact coverp00000010010011
theorem coverp0000001001001 : Covers (-72761639/1000000 : ℚ) vp0000001001001 := join_branches bp00000010010010 bp00000010010011
private noncomputable def vp0000001001000111_0 : Blocks := edgeBlocks% "full/vectors/0000001001000111-V-0000.bin"
noncomputable def vp0000001001000111 : Blocks := vp0000001001000111_0
theorem coverp0000001001000111 : Covers (-72636639/125000 : ℚ) vp0000001001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001000110_0 : Blocks := edgeBlocks% "full/vectors/0000001001000110-V-0000.bin"
noncomputable def vp0000001001000110 : Blocks := vp0000001001000110_0
theorem coverp0000001001000110 : Covers (-72511639/125000 : ℚ) vp0000001001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100100011_0 : Blocks := edgeBlocks% "full/vectors/000000100100011-V-0000.bin"
noncomputable def vp000000100100011 : Blocks := vp000000100100011_0
private theorem bp0000001001000110 : Branch 0 (-72511639/250000 : ℚ) vp000000100100011 := by
  apply branch_left_normalized (c:=vp0000001001000110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-72511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-72511639/125000 : ℚ) by norm_num]
  exact coverp0000001001000110
private noncomputable def ep0000001001000111_0 : Blocks := edgeBlocks% "full/vectors/0000001001000111-E-0000.bin"
noncomputable def ep0000001001000111 : Blocks := ep0000001001000111_0
private theorem idp0000001001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100100011.list =
    C ((2:ℤ)^49) * horner X vp0000001001000111.list + horner X ep0000001001000111.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001000111 : Branch 1 (-72511639/250000 : ℚ) vp000000100100011 := by
  apply branch_checked idp0000001001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-72511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-72636639/125000 : ℚ) by norm_num]
  exact coverp0000001001000111
theorem coverp000000100100011 : Covers (-72511639/250000 : ℚ) vp000000100100011 := join_branches bp0000001001000110 bp0000001001000111
private noncomputable def vp0000001001000101_0 : Blocks := edgeBlocks% "full/vectors/0000001001000101-V-0000.bin"
noncomputable def vp0000001001000101 : Blocks := vp0000001001000101_0
theorem coverp0000001001000101 : Covers (-72386639/125000 : ℚ) vp0000001001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001000100_0 : Blocks := edgeBlocks% "full/vectors/0000001001000100-V-0000.bin"
noncomputable def vp0000001001000100 : Blocks := vp0000001001000100_0
theorem coverp0000001001000100 : Covers (-72261639/125000 : ℚ) vp0000001001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100100010_0 : Blocks := edgeBlocks% "full/vectors/000000100100010-V-0000.bin"
noncomputable def vp000000100100010 : Blocks := vp000000100100010_0
private theorem bp0000001001000100 : Branch 0 (-72261639/250000 : ℚ) vp000000100100010 := by
  apply branch_left_normalized (c:=vp0000001001000100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-72261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-72261639/125000 : ℚ) by norm_num]
  exact coverp0000001001000100
private noncomputable def ep0000001001000101_0 : Blocks := edgeBlocks% "full/vectors/0000001001000101-E-0000.bin"
noncomputable def ep0000001001000101 : Blocks := ep0000001001000101_0
private theorem idp0000001001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100100010.list =
    C ((2:ℤ)^49) * horner X vp0000001001000101.list + horner X ep0000001001000101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001000101 : Branch 1 (-72261639/250000 : ℚ) vp000000100100010 := by
  apply branch_checked idp0000001001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-72261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-72386639/125000 : ℚ) by norm_num]
  exact coverp0000001001000101
theorem coverp000000100100010 : Covers (-72261639/250000 : ℚ) vp000000100100010 := join_branches bp0000001001000100 bp0000001001000101
private noncomputable def vp00000010010001_0 : Blocks := edgeBlocks% "full/vectors/00000010010001-V-0000.bin"
noncomputable def vp00000010010001 : Blocks := vp00000010010001_0
private theorem bp000000100100010 : Branch 0 (-72261639/500000 : ℚ) vp00000010010001 := by
  apply branch_left_normalized (c:=vp000000100100010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-72261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-72261639/250000 : ℚ) by norm_num]
  exact coverp000000100100010
private noncomputable def ep000000100100011_0 : Blocks := edgeBlocks% "full/vectors/000000100100011-E-0000.bin"
noncomputable def ep000000100100011 : Blocks := ep000000100100011_0
private theorem idp000000100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010010001.list =
    C ((2:ℤ)^79) * horner X vp000000100100011.list + horner X ep000000100100011.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100100011 : Branch 1 (-72261639/500000 : ℚ) vp00000010010001 := by
  apply branch_checked idp000000100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-72261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-72511639/250000 : ℚ) by norm_num]
  exact coverp000000100100011
theorem coverp00000010010001 : Covers (-72261639/500000 : ℚ) vp00000010010001 := join_branches bp000000100100010 bp000000100100011
private noncomputable def vp0000001001000011_0 : Blocks := edgeBlocks% "full/vectors/0000001001000011-V-0000.bin"
noncomputable def vp0000001001000011 : Blocks := vp0000001001000011_0
theorem coverp0000001001000011 : Covers (-72136639/125000 : ℚ) vp0000001001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001000010_0 : Blocks := edgeBlocks% "full/vectors/0000001001000010-V-0000.bin"
noncomputable def vp0000001001000010 : Blocks := vp0000001001000010_0
theorem coverp0000001001000010 : Covers (-72011639/125000 : ℚ) vp0000001001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100100001_0 : Blocks := edgeBlocks% "full/vectors/000000100100001-V-0000.bin"
noncomputable def vp000000100100001 : Blocks := vp000000100100001_0
private theorem bp0000001001000010 : Branch 0 (-72011639/250000 : ℚ) vp000000100100001 := by
  apply branch_left_normalized (c:=vp0000001001000010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-72011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-72011639/125000 : ℚ) by norm_num]
  exact coverp0000001001000010
private noncomputable def ep0000001001000011_0 : Blocks := edgeBlocks% "full/vectors/0000001001000011-E-0000.bin"
noncomputable def ep0000001001000011 : Blocks := ep0000001001000011_0
private theorem idp0000001001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100100001.list =
    C ((2:ℤ)^49) * horner X vp0000001001000011.list + horner X ep0000001001000011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001000011 : Branch 1 (-72011639/250000 : ℚ) vp000000100100001 := by
  apply branch_checked idp0000001001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-72011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-72136639/125000 : ℚ) by norm_num]
  exact coverp0000001001000011
theorem coverp000000100100001 : Covers (-72011639/250000 : ℚ) vp000000100100001 := join_branches bp0000001001000010 bp0000001001000011
private noncomputable def vp0000001001000001_0 : Blocks := edgeBlocks% "full/vectors/0000001001000001-V-0000.bin"
noncomputable def vp0000001001000001 : Blocks := vp0000001001000001_0
theorem coverp0000001001000001 : Covers (-71886639/125000 : ℚ) vp0000001001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001001000000_0 : Blocks := edgeBlocks% "full/vectors/0000001001000000-V-0000.bin"
noncomputable def vp0000001001000000 : Blocks := vp0000001001000000_0
theorem coverp0000001001000000 : Covers (-71761639/125000 : ℚ) vp0000001001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100100000_0 : Blocks := edgeBlocks% "full/vectors/000000100100000-V-0000.bin"
noncomputable def vp000000100100000 : Blocks := vp000000100100000_0
private theorem bp0000001001000000 : Branch 0 (-71761639/250000 : ℚ) vp000000100100000 := by
  apply branch_left_normalized (c:=vp0000001001000000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-71761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-71761639/125000 : ℚ) by norm_num]
  exact coverp0000001001000000
private noncomputable def ep0000001001000001_0 : Blocks := edgeBlocks% "full/vectors/0000001001000001-E-0000.bin"
noncomputable def ep0000001001000001 : Blocks := ep0000001001000001_0
private theorem idp0000001001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100100000.list =
    C ((2:ℤ)^51) * horner X vp0000001001000001.list + horner X ep0000001001000001.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001000001 : Branch 1 (-71761639/250000 : ℚ) vp000000100100000 := by
  apply branch_checked idp0000001001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-71761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-71886639/125000 : ℚ) by norm_num]
  exact coverp0000001001000001
theorem coverp000000100100000 : Covers (-71761639/250000 : ℚ) vp000000100100000 := join_branches bp0000001001000000 bp0000001001000001
private noncomputable def vp00000010010000_0 : Blocks := edgeBlocks% "full/vectors/00000010010000-V-0000.bin"
noncomputable def vp00000010010000 : Blocks := vp00000010010000_0
private theorem bp000000100100000 : Branch 0 (-71761639/500000 : ℚ) vp00000010010000 := by
  apply branch_left_normalized (c:=vp000000100100000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-71761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-71761639/250000 : ℚ) by norm_num]
  exact coverp000000100100000
private noncomputable def ep000000100100001_0 : Blocks := edgeBlocks% "full/vectors/000000100100001-E-0000.bin"
noncomputable def ep000000100100001 : Blocks := ep000000100100001_0
private theorem idp000000100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010010000.list =
    C ((2:ℤ)^83) * horner X vp000000100100001.list + horner X ep000000100100001.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100100001 : Branch 1 (-71761639/500000 : ℚ) vp00000010010000 := by
  apply branch_checked idp000000100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-71761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-72011639/250000 : ℚ) by norm_num]
  exact coverp000000100100001
theorem coverp00000010010000 : Covers (-71761639/500000 : ℚ) vp00000010010000 := join_branches bp000000100100000 bp000000100100001
private noncomputable def vp0000001001000_0 : Blocks := edgeBlocks% "full/vectors/0000001001000-V-0000.bin"
private noncomputable def vp0000001001000_1 : Blocks := edgeBlocks% "full/vectors/0000001001000-V-0001.bin"
noncomputable def vp0000001001000 : Blocks := (Blocks.join vp0000001001000_0 vp0000001001000_1)
private theorem bp00000010010000 : Branch 0 (-71761639/1000000 : ℚ) vp0000001001000 := by
  apply branch_left_normalized (c:=vp00000010010000) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-71761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-71761639/500000 : ℚ) by norm_num]
  exact coverp00000010010000
private noncomputable def ep00000010010001_0 : Blocks := edgeBlocks% "full/vectors/00000010010001-E-0000.bin"
private noncomputable def ep00000010010001_1 : Blocks := edgeBlocks% "full/vectors/00000010010001-E-0001.bin"
noncomputable def ep00000010010001 : Blocks := (Blocks.join ep00000010010001_0 ep00000010010001_1)
private theorem idp00000010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001001000.list =
    C ((2:ℤ)^144) * horner X vp00000010010001.list + horner X ep00000010010001.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010010001 : Branch 1 (-71761639/1000000 : ℚ) vp0000001001000 := by
  apply branch_checked idp00000010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-71761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-72261639/500000 : ℚ) by norm_num]
  exact coverp00000010010001
theorem coverp0000001001000 : Covers (-71761639/1000000 : ℚ) vp0000001001000 := join_branches bp00000010010000 bp00000010010001
private noncomputable def vp000000100100_0 : Blocks := edgeBlocks% "full/vectors/000000100100-V-0000.bin"
private noncomputable def vp000000100100_1 : Blocks := edgeBlocks% "full/vectors/000000100100-V-0001.bin"
noncomputable def vp000000100100 : Blocks := (Blocks.join vp000000100100_0 vp000000100100_1)
private theorem bp0000001001000 : Branch 0 (-71761639/2000000 : ℚ) vp000000100100 := by
  apply branch_left_normalized (c:=vp0000001001000) (k:=0) (m:=138) (by decide +kernel)
  rw [show 2*(-71761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-71761639/1000000 : ℚ) by norm_num]
  exact coverp0000001001000
private noncomputable def ep0000001001001_0 : Blocks := edgeBlocks% "full/vectors/0000001001001-E-0000.bin"
private noncomputable def ep0000001001001_1 : Blocks := edgeBlocks% "full/vectors/0000001001001-E-0001.bin"
noncomputable def ep0000001001001 : Blocks := (Blocks.join ep0000001001001_0 ep0000001001001_1)
private theorem idp0000001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100100.list =
    C ((2:ℤ)^262) * horner X vp0000001001001.list + horner X ep0000001001001.list := by
  exact edge_identity (B := (2:ℤ)^479) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001001 : Branch 1 (-71761639/2000000 : ℚ) vp000000100100 := by
  apply branch_checked idp0000001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-71761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-72761639/1000000 : ℚ) by norm_num]
  exact coverp0000001001001
theorem coverp000000100100 : Covers (-71761639/2000000 : ℚ) vp000000100100 := join_branches bp0000001001000 bp0000001001001
private noncomputable def vp00000010010_0 : Blocks := edgeBlocks% "full/vectors/00000010010-V-0000.bin"
private noncomputable def vp00000010010_1 : Blocks := edgeBlocks% "full/vectors/00000010010-V-0001.bin"
private noncomputable def vp00000010010_2 : Blocks := edgeBlocks% "full/vectors/00000010010-V-0002.bin"
private noncomputable def vp00000010010_3 : Blocks := edgeBlocks% "full/vectors/00000010010-V-0003.bin"
noncomputable def vp00000010010 : Blocks := (Blocks.join (Blocks.join vp00000010010_0 vp00000010010_1) (Blocks.join vp00000010010_2 vp00000010010_3))
private theorem bp000000100100 : Branch 0 (-71761639/4000000 : ℚ) vp00000010010 := by
  apply branch_left_normalized (c:=vp000000100100) (k:=0) (m:=253) (by decide +kernel)
  rw [show 2*(-71761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-71761639/2000000 : ℚ) by norm_num]
  exact coverp000000100100
private noncomputable def ep000000100101_0 : Blocks := edgeBlocks% "full/vectors/000000100101-E-0000.bin"
private noncomputable def ep000000100101_1 : Blocks := edgeBlocks% "full/vectors/000000100101-E-0001.bin"
private noncomputable def ep000000100101_2 : Blocks := edgeBlocks% "full/vectors/000000100101-E-0002.bin"
private noncomputable def ep000000100101_3 : Blocks := edgeBlocks% "full/vectors/000000100101-E-0003.bin"
noncomputable def ep000000100101 : Blocks := (Blocks.join (Blocks.join ep000000100101_0 ep000000100101_1) (Blocks.join ep000000100101_2 ep000000100101_3))
private theorem idp000000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010010.list =
    C ((2:ℤ)^495) * horner X vp000000100101.list + horner X ep000000100101.list := by
  exact edge_identity (B := (2:ℤ)^832) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100101 : Branch 1 (-71761639/4000000 : ℚ) vp00000010010 := by
  apply branch_checked idp000000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-71761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-73761639/2000000 : ℚ) by norm_num]
  exact coverp000000100101
theorem coverp00000010010 : Covers (-71761639/4000000 : ℚ) vp00000010010 := join_branches bp000000100100 bp000000100101
private noncomputable def vp0000001001_0 : Blocks := edgeBlocks% "full/vectors/0000001001-V-0000.bin"
private noncomputable def vp0000001001_1 : Blocks := edgeBlocks% "full/vectors/0000001001-V-0001.bin"
private noncomputable def vp0000001001_2 : Blocks := edgeBlocks% "full/vectors/0000001001-V-0002.bin"
private noncomputable def vp0000001001_3 : Blocks := edgeBlocks% "full/vectors/0000001001-V-0003.bin"
private noncomputable def vp0000001001_4 : Blocks := edgeBlocks% "full/vectors/0000001001-V-0004.bin"
private noncomputable def vp0000001001_5 : Blocks := edgeBlocks% "full/vectors/0000001001-V-0005.bin"
private noncomputable def vp0000001001_6 : Blocks := edgeBlocks% "full/vectors/0000001001-V-0006.bin"
private noncomputable def vp0000001001_7 : Blocks := edgeBlocks% "full/vectors/0000001001-V-0007.bin"
noncomputable def vp0000001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0000001001_0 vp0000001001_1) (Blocks.join vp0000001001_2 vp0000001001_3)) (Blocks.join (Blocks.join vp0000001001_4 vp0000001001_5) (Blocks.join vp0000001001_6 vp0000001001_7)))
private theorem bp00000010010 : Branch 0 (-71761639/8000000 : ℚ) vp0000001001 := by
  apply branch_left_normalized (c:=vp00000010010) (k:=0) (m:=484) (by decide +kernel)
  rw [show 2*(-71761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-71761639/4000000 : ℚ) by norm_num]
  exact coverp00000010010
private noncomputable def ep00000010011_0 : Blocks := edgeBlocks% "full/vectors/00000010011-E-0000.bin"
private noncomputable def ep00000010011_1 : Blocks := edgeBlocks% "full/vectors/00000010011-E-0001.bin"
private noncomputable def ep00000010011_2 : Blocks := edgeBlocks% "full/vectors/00000010011-E-0002.bin"
private noncomputable def ep00000010011_3 : Blocks := edgeBlocks% "full/vectors/00000010011-E-0003.bin"
private noncomputable def ep00000010011_4 : Blocks := edgeBlocks% "full/vectors/00000010011-E-0004.bin"
private noncomputable def ep00000010011_5 : Blocks := edgeBlocks% "full/vectors/00000010011-E-0005.bin"
private noncomputable def ep00000010011_6 : Blocks := edgeBlocks% "full/vectors/00000010011-E-0006.bin"
private noncomputable def ep00000010011_7 : Blocks := edgeBlocks% "full/vectors/00000010011-E-0007.bin"
noncomputable def ep00000010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00000010011_0 ep00000010011_1) (Blocks.join ep00000010011_2 ep00000010011_3)) (Blocks.join (Blocks.join ep00000010011_4 ep00000010011_5) (Blocks.join ep00000010011_6 ep00000010011_7)))
private theorem idp00000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001001.list =
    C ((2:ℤ)^960) * horner X vp00000010011.list + horner X ep00000010011.list := by
  exact edge_identity (B := (2:ℤ)^1530) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010011 : Branch 1 (-71761639/8000000 : ℚ) vp0000001001 := by
  apply branch_checked idp00000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-71761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-75761639/4000000 : ℚ) by norm_num]
  exact coverp00000010011
theorem coverp0000001001 : Covers (-71761639/8000000 : ℚ) vp0000001001 := join_branches bp00000010010 bp00000010011
end NextProof.EdgeFull

