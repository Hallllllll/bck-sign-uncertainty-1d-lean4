import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00054

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000010100111111_0 : Blocks := edgeBlocks% "full/vectors/000010100111111-V-0000.bin"
noncomputable def vp000010100111111 : Blocks := vp000010100111111_0
theorem coverp000010100111111 : Covers (-335511639/250000 : ℚ) vp000010100111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100111110_0 : Blocks := edgeBlocks% "full/vectors/000010100111110-V-0000.bin"
noncomputable def vp000010100111110 : Blocks := vp000010100111110_0
theorem coverp000010100111110 : Covers (-335261639/250000 : ℚ) vp000010100111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010011111_0 : Blocks := edgeBlocks% "full/vectors/00001010011111-V-0000.bin"
noncomputable def vp00001010011111 : Blocks := vp00001010011111_0
private theorem bp000010100111110 : Branch 0 (-335261639/500000 : ℚ) vp00001010011111 := by
  apply branch_left_normalized (c:=vp000010100111110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-335261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-335261639/250000 : ℚ) by norm_num]
  exact coverp000010100111110
private noncomputable def ep000010100111111_0 : Blocks := edgeBlocks% "full/vectors/000010100111111-E-0000.bin"
noncomputable def ep000010100111111 : Blocks := ep000010100111111_0
private theorem idp000010100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010011111.list =
    C ((2:ℤ)^49) * horner X vp000010100111111.list + horner X ep000010100111111.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100111111 : Branch 1 (-335261639/500000 : ℚ) vp00001010011111 := by
  apply branch_checked idp000010100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-335261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-335511639/250000 : ℚ) by norm_num]
  exact coverp000010100111111
theorem coverp00001010011111 : Covers (-335261639/500000 : ℚ) vp00001010011111 := join_branches bp000010100111110 bp000010100111111
private noncomputable def vp000010100111101_0 : Blocks := edgeBlocks% "full/vectors/000010100111101-V-0000.bin"
noncomputable def vp000010100111101 : Blocks := vp000010100111101_0
theorem coverp000010100111101 : Covers (-335011639/250000 : ℚ) vp000010100111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100111100_0 : Blocks := edgeBlocks% "full/vectors/000010100111100-V-0000.bin"
noncomputable def vp000010100111100 : Blocks := vp000010100111100_0
theorem coverp000010100111100 : Covers (-334761639/250000 : ℚ) vp000010100111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010011110_0 : Blocks := edgeBlocks% "full/vectors/00001010011110-V-0000.bin"
noncomputable def vp00001010011110 : Blocks := vp00001010011110_0
private theorem bp000010100111100 : Branch 0 (-334761639/500000 : ℚ) vp00001010011110 := by
  apply branch_left_normalized (c:=vp000010100111100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-334761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-334761639/250000 : ℚ) by norm_num]
  exact coverp000010100111100
private noncomputable def ep000010100111101_0 : Blocks := edgeBlocks% "full/vectors/000010100111101-E-0000.bin"
noncomputable def ep000010100111101 : Blocks := ep000010100111101_0
private theorem idp000010100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010011110.list =
    C ((2:ℤ)^49) * horner X vp000010100111101.list + horner X ep000010100111101.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100111101 : Branch 1 (-334761639/500000 : ℚ) vp00001010011110 := by
  apply branch_checked idp000010100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-334761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-335011639/250000 : ℚ) by norm_num]
  exact coverp000010100111101
theorem coverp00001010011110 : Covers (-334761639/500000 : ℚ) vp00001010011110 := join_branches bp000010100111100 bp000010100111101
private noncomputable def vp0000101001111_0 : Blocks := edgeBlocks% "full/vectors/0000101001111-V-0000.bin"
noncomputable def vp0000101001111 : Blocks := vp0000101001111_0
private theorem bp00001010011110 : Branch 0 (-334761639/1000000 : ℚ) vp0000101001111 := by
  apply branch_left_normalized (c:=vp00001010011110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-334761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-334761639/500000 : ℚ) by norm_num]
  exact coverp00001010011110
private noncomputable def ep00001010011111_0 : Blocks := edgeBlocks% "full/vectors/00001010011111-E-0000.bin"
noncomputable def ep00001010011111 : Blocks := ep00001010011111_0
private theorem idp00001010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101001111.list =
    C ((2:ℤ)^79) * horner X vp00001010011111.list + horner X ep00001010011111.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010011111 : Branch 1 (-334761639/1000000 : ℚ) vp0000101001111 := by
  apply branch_checked idp00001010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-334761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-335261639/500000 : ℚ) by norm_num]
  exact coverp00001010011111
theorem coverp0000101001111 : Covers (-334761639/1000000 : ℚ) vp0000101001111 := join_branches bp00001010011110 bp00001010011111
private noncomputable def vp000010100111011_0 : Blocks := edgeBlocks% "full/vectors/000010100111011-V-0000.bin"
noncomputable def vp000010100111011 : Blocks := vp000010100111011_0
theorem coverp000010100111011 : Covers (-334511639/250000 : ℚ) vp000010100111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100111010_0 : Blocks := edgeBlocks% "full/vectors/000010100111010-V-0000.bin"
noncomputable def vp000010100111010 : Blocks := vp000010100111010_0
theorem coverp000010100111010 : Covers (-334261639/250000 : ℚ) vp000010100111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010011101_0 : Blocks := edgeBlocks% "full/vectors/00001010011101-V-0000.bin"
noncomputable def vp00001010011101 : Blocks := vp00001010011101_0
private theorem bp000010100111010 : Branch 0 (-334261639/500000 : ℚ) vp00001010011101 := by
  apply branch_left_normalized (c:=vp000010100111010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-334261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-334261639/250000 : ℚ) by norm_num]
  exact coverp000010100111010
private noncomputable def ep000010100111011_0 : Blocks := edgeBlocks% "full/vectors/000010100111011-E-0000.bin"
noncomputable def ep000010100111011 : Blocks := ep000010100111011_0
private theorem idp000010100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010011101.list =
    C ((2:ℤ)^49) * horner X vp000010100111011.list + horner X ep000010100111011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100111011 : Branch 1 (-334261639/500000 : ℚ) vp00001010011101 := by
  apply branch_checked idp000010100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-334261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-334511639/250000 : ℚ) by norm_num]
  exact coverp000010100111011
theorem coverp00001010011101 : Covers (-334261639/500000 : ℚ) vp00001010011101 := join_branches bp000010100111010 bp000010100111011
private noncomputable def vp000010100111001_0 : Blocks := edgeBlocks% "full/vectors/000010100111001-V-0000.bin"
noncomputable def vp000010100111001 : Blocks := vp000010100111001_0
theorem coverp000010100111001 : Covers (-334011639/250000 : ℚ) vp000010100111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100111000_0 : Blocks := edgeBlocks% "full/vectors/000010100111000-V-0000.bin"
noncomputable def vp000010100111000 : Blocks := vp000010100111000_0
theorem coverp000010100111000 : Covers (-333761639/250000 : ℚ) vp000010100111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010011100_0 : Blocks := edgeBlocks% "full/vectors/00001010011100-V-0000.bin"
noncomputable def vp00001010011100 : Blocks := vp00001010011100_0
private theorem bp000010100111000 : Branch 0 (-333761639/500000 : ℚ) vp00001010011100 := by
  apply branch_left_normalized (c:=vp000010100111000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-333761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-333761639/250000 : ℚ) by norm_num]
  exact coverp000010100111000
private noncomputable def ep000010100111001_0 : Blocks := edgeBlocks% "full/vectors/000010100111001-E-0000.bin"
noncomputable def ep000010100111001 : Blocks := ep000010100111001_0
private theorem idp000010100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010011100.list =
    C ((2:ℤ)^49) * horner X vp000010100111001.list + horner X ep000010100111001.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100111001 : Branch 1 (-333761639/500000 : ℚ) vp00001010011100 := by
  apply branch_checked idp000010100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-333761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-334011639/250000 : ℚ) by norm_num]
  exact coverp000010100111001
theorem coverp00001010011100 : Covers (-333761639/500000 : ℚ) vp00001010011100 := join_branches bp000010100111000 bp000010100111001
private noncomputable def vp0000101001110_0 : Blocks := edgeBlocks% "full/vectors/0000101001110-V-0000.bin"
noncomputable def vp0000101001110 : Blocks := vp0000101001110_0
private theorem bp00001010011100 : Branch 0 (-333761639/1000000 : ℚ) vp0000101001110 := by
  apply branch_left_normalized (c:=vp00001010011100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-333761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-333761639/500000 : ℚ) by norm_num]
  exact coverp00001010011100
private noncomputable def ep00001010011101_0 : Blocks := edgeBlocks% "full/vectors/00001010011101-E-0000.bin"
noncomputable def ep00001010011101 : Blocks := ep00001010011101_0
private theorem idp00001010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101001110.list =
    C ((2:ℤ)^79) * horner X vp00001010011101.list + horner X ep00001010011101.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010011101 : Branch 1 (-333761639/1000000 : ℚ) vp0000101001110 := by
  apply branch_checked idp00001010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-333761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-334261639/500000 : ℚ) by norm_num]
  exact coverp00001010011101
theorem coverp0000101001110 : Covers (-333761639/1000000 : ℚ) vp0000101001110 := join_branches bp00001010011100 bp00001010011101
private noncomputable def vp000010100111_0 : Blocks := edgeBlocks% "full/vectors/000010100111-V-0000.bin"
private noncomputable def vp000010100111_1 : Blocks := edgeBlocks% "full/vectors/000010100111-V-0001.bin"
noncomputable def vp000010100111 : Blocks := (Blocks.join vp000010100111_0 vp000010100111_1)
private theorem bp0000101001110 : Branch 0 (-333761639/2000000 : ℚ) vp000010100111 := by
  apply branch_left_normalized (c:=vp0000101001110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-333761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-333761639/1000000 : ℚ) by norm_num]
  exact coverp0000101001110
private noncomputable def ep0000101001111_0 : Blocks := edgeBlocks% "full/vectors/0000101001111-E-0000.bin"
private noncomputable def ep0000101001111_1 : Blocks := edgeBlocks% "full/vectors/0000101001111-E-0001.bin"
noncomputable def ep0000101001111 : Blocks := (Blocks.join ep0000101001111_0 ep0000101001111_1)
private theorem idp0000101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010100111.list =
    C ((2:ℤ)^137) * horner X vp0000101001111.list + horner X ep0000101001111.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101001111 : Branch 1 (-333761639/2000000 : ℚ) vp000010100111 := by
  apply branch_checked idp0000101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-333761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-334761639/1000000 : ℚ) by norm_num]
  exact coverp0000101001111
theorem coverp000010100111 : Covers (-333761639/2000000 : ℚ) vp000010100111 := join_branches bp0000101001110 bp0000101001111
private noncomputable def vp000010100110111_0 : Blocks := edgeBlocks% "full/vectors/000010100110111-V-0000.bin"
noncomputable def vp000010100110111 : Blocks := vp000010100110111_0
theorem coverp000010100110111 : Covers (-333511639/250000 : ℚ) vp000010100110111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100110110_0 : Blocks := edgeBlocks% "full/vectors/000010100110110-V-0000.bin"
noncomputable def vp000010100110110 : Blocks := vp000010100110110_0
theorem coverp000010100110110 : Covers (-333261639/250000 : ℚ) vp000010100110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010011011_0 : Blocks := edgeBlocks% "full/vectors/00001010011011-V-0000.bin"
noncomputable def vp00001010011011 : Blocks := vp00001010011011_0
private theorem bp000010100110110 : Branch 0 (-333261639/500000 : ℚ) vp00001010011011 := by
  apply branch_left_normalized (c:=vp000010100110110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-333261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-333261639/250000 : ℚ) by norm_num]
  exact coverp000010100110110
private noncomputable def ep000010100110111_0 : Blocks := edgeBlocks% "full/vectors/000010100110111-E-0000.bin"
noncomputable def ep000010100110111 : Blocks := ep000010100110111_0
private theorem idp000010100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010011011.list =
    C ((2:ℤ)^48) * horner X vp000010100110111.list + horner X ep000010100110111.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100110111 : Branch 1 (-333261639/500000 : ℚ) vp00001010011011 := by
  apply branch_checked idp000010100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-333261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-333511639/250000 : ℚ) by norm_num]
  exact coverp000010100110111
theorem coverp00001010011011 : Covers (-333261639/500000 : ℚ) vp00001010011011 := join_branches bp000010100110110 bp000010100110111
private noncomputable def vp000010100110101_0 : Blocks := edgeBlocks% "full/vectors/000010100110101-V-0000.bin"
noncomputable def vp000010100110101 : Blocks := vp000010100110101_0
theorem coverp000010100110101 : Covers (-333011639/250000 : ℚ) vp000010100110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100110100_0 : Blocks := edgeBlocks% "full/vectors/000010100110100-V-0000.bin"
noncomputable def vp000010100110100 : Blocks := vp000010100110100_0
theorem coverp000010100110100 : Covers (-332761639/250000 : ℚ) vp000010100110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010011010_0 : Blocks := edgeBlocks% "full/vectors/00001010011010-V-0000.bin"
noncomputable def vp00001010011010 : Blocks := vp00001010011010_0
private theorem bp000010100110100 : Branch 0 (-332761639/500000 : ℚ) vp00001010011010 := by
  apply branch_left_normalized (c:=vp000010100110100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-332761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-332761639/250000 : ℚ) by norm_num]
  exact coverp000010100110100
private noncomputable def ep000010100110101_0 : Blocks := edgeBlocks% "full/vectors/000010100110101-E-0000.bin"
noncomputable def ep000010100110101 : Blocks := ep000010100110101_0
private theorem idp000010100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010011010.list =
    C ((2:ℤ)^48) * horner X vp000010100110101.list + horner X ep000010100110101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100110101 : Branch 1 (-332761639/500000 : ℚ) vp00001010011010 := by
  apply branch_checked idp000010100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-332761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-333011639/250000 : ℚ) by norm_num]
  exact coverp000010100110101
theorem coverp00001010011010 : Covers (-332761639/500000 : ℚ) vp00001010011010 := join_branches bp000010100110100 bp000010100110101
private noncomputable def vp0000101001101_0 : Blocks := edgeBlocks% "full/vectors/0000101001101-V-0000.bin"
noncomputable def vp0000101001101 : Blocks := vp0000101001101_0
private theorem bp00001010011010 : Branch 0 (-332761639/1000000 : ℚ) vp0000101001101 := by
  apply branch_left_normalized (c:=vp00001010011010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-332761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-332761639/500000 : ℚ) by norm_num]
  exact coverp00001010011010
private noncomputable def ep00001010011011_0 : Blocks := edgeBlocks% "full/vectors/00001010011011-E-0000.bin"
noncomputable def ep00001010011011 : Blocks := ep00001010011011_0
private theorem idp00001010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101001101.list =
    C ((2:ℤ)^78) * horner X vp00001010011011.list + horner X ep00001010011011.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010011011 : Branch 1 (-332761639/1000000 : ℚ) vp0000101001101 := by
  apply branch_checked idp00001010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-332761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-333261639/500000 : ℚ) by norm_num]
  exact coverp00001010011011
theorem coverp0000101001101 : Covers (-332761639/1000000 : ℚ) vp0000101001101 := join_branches bp00001010011010 bp00001010011011
private noncomputable def vp000010100110011_0 : Blocks := edgeBlocks% "full/vectors/000010100110011-V-0000.bin"
noncomputable def vp000010100110011 : Blocks := vp000010100110011_0
theorem coverp000010100110011 : Covers (-332511639/250000 : ℚ) vp000010100110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100110010_0 : Blocks := edgeBlocks% "full/vectors/000010100110010-V-0000.bin"
noncomputable def vp000010100110010 : Blocks := vp000010100110010_0
theorem coverp000010100110010 : Covers (-332261639/250000 : ℚ) vp000010100110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010011001_0 : Blocks := edgeBlocks% "full/vectors/00001010011001-V-0000.bin"
noncomputable def vp00001010011001 : Blocks := vp00001010011001_0
private theorem bp000010100110010 : Branch 0 (-332261639/500000 : ℚ) vp00001010011001 := by
  apply branch_left_normalized (c:=vp000010100110010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-332261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-332261639/250000 : ℚ) by norm_num]
  exact coverp000010100110010
private noncomputable def ep000010100110011_0 : Blocks := edgeBlocks% "full/vectors/000010100110011-E-0000.bin"
noncomputable def ep000010100110011 : Blocks := ep000010100110011_0
private theorem idp000010100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010011001.list =
    C ((2:ℤ)^48) * horner X vp000010100110011.list + horner X ep000010100110011.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100110011 : Branch 1 (-332261639/500000 : ℚ) vp00001010011001 := by
  apply branch_checked idp000010100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-332261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-332511639/250000 : ℚ) by norm_num]
  exact coverp000010100110011
theorem coverp00001010011001 : Covers (-332261639/500000 : ℚ) vp00001010011001 := join_branches bp000010100110010 bp000010100110011
private noncomputable def vp00001010011000_0 : Blocks := edgeBlocks% "full/vectors/00001010011000-V-0000.bin"
noncomputable def vp00001010011000 : Blocks := vp00001010011000_0
theorem coverp00001010011000 : Covers (-331761639/500000 : ℚ) vp00001010011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101001100_0 : Blocks := edgeBlocks% "full/vectors/0000101001100-V-0000.bin"
noncomputable def vp0000101001100 : Blocks := vp0000101001100_0
private theorem bp00001010011000 : Branch 0 (-331761639/1000000 : ℚ) vp0000101001100 := by
  apply branch_left_normalized (c:=vp00001010011000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-331761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-331761639/500000 : ℚ) by norm_num]
  exact coverp00001010011000
private noncomputable def ep00001010011001_0 : Blocks := edgeBlocks% "full/vectors/00001010011001-E-0000.bin"
noncomputable def ep00001010011001 : Blocks := ep00001010011001_0
private theorem idp00001010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101001100.list =
    C ((2:ℤ)^78) * horner X vp00001010011001.list + horner X ep00001010011001.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010011001 : Branch 1 (-331761639/1000000 : ℚ) vp0000101001100 := by
  apply branch_checked idp00001010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-331761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-332261639/500000 : ℚ) by norm_num]
  exact coverp00001010011001
theorem coverp0000101001100 : Covers (-331761639/1000000 : ℚ) vp0000101001100 := join_branches bp00001010011000 bp00001010011001
private noncomputable def vp000010100110_0 : Blocks := edgeBlocks% "full/vectors/000010100110-V-0000.bin"
private noncomputable def vp000010100110_1 : Blocks := edgeBlocks% "full/vectors/000010100110-V-0001.bin"
noncomputable def vp000010100110 : Blocks := (Blocks.join vp000010100110_0 vp000010100110_1)
private theorem bp0000101001100 : Branch 0 (-331761639/2000000 : ℚ) vp000010100110 := by
  apply branch_left_normalized (c:=vp0000101001100) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-331761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-331761639/1000000 : ℚ) by norm_num]
  exact coverp0000101001100
private noncomputable def ep0000101001101_0 : Blocks := edgeBlocks% "full/vectors/0000101001101-E-0000.bin"
private noncomputable def ep0000101001101_1 : Blocks := edgeBlocks% "full/vectors/0000101001101-E-0001.bin"
noncomputable def ep0000101001101 : Blocks := (Blocks.join ep0000101001101_0 ep0000101001101_1)
private theorem idp0000101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010100110.list =
    C ((2:ℤ)^135) * horner X vp0000101001101.list + horner X ep0000101001101.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101001101 : Branch 1 (-331761639/2000000 : ℚ) vp000010100110 := by
  apply branch_checked idp0000101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-331761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-332761639/1000000 : ℚ) by norm_num]
  exact coverp0000101001101
theorem coverp000010100110 : Covers (-331761639/2000000 : ℚ) vp000010100110 := join_branches bp0000101001100 bp0000101001101
private noncomputable def vp00001010011_0 : Blocks := edgeBlocks% "full/vectors/00001010011-V-0000.bin"
private noncomputable def vp00001010011_1 : Blocks := edgeBlocks% "full/vectors/00001010011-V-0001.bin"
noncomputable def vp00001010011 : Blocks := (Blocks.join vp00001010011_0 vp00001010011_1)
private theorem bp000010100110 : Branch 0 (-331761639/4000000 : ℚ) vp00001010011 := by
  apply branch_left_normalized (c:=vp000010100110) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-331761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-331761639/2000000 : ℚ) by norm_num]
  exact coverp000010100110
private noncomputable def ep000010100111_0 : Blocks := edgeBlocks% "full/vectors/000010100111-E-0000.bin"
private noncomputable def ep000010100111_1 : Blocks := edgeBlocks% "full/vectors/000010100111-E-0001.bin"
noncomputable def ep000010100111 : Blocks := (Blocks.join ep000010100111_0 ep000010100111_1)
private theorem idp000010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010011.list =
    C ((2:ℤ)^249) * horner X vp000010100111.list + horner X ep000010100111.list := by
  exact edge_identity (B := (2:ℤ)^455) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100111 : Branch 1 (-331761639/4000000 : ℚ) vp00001010011 := by
  apply branch_checked idp000010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-331761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-333761639/2000000 : ℚ) by norm_num]
  exact coverp000010100111
theorem coverp00001010011 : Covers (-331761639/4000000 : ℚ) vp00001010011 := join_branches bp000010100110 bp000010100111
private noncomputable def vp00001010010111_0 : Blocks := edgeBlocks% "full/vectors/00001010010111-V-0000.bin"
noncomputable def vp00001010010111 : Blocks := vp00001010010111_0
theorem coverp00001010010111 : Covers (-331261639/500000 : ℚ) vp00001010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010010110_0 : Blocks := edgeBlocks% "full/vectors/00001010010110-V-0000.bin"
noncomputable def vp00001010010110 : Blocks := vp00001010010110_0
theorem coverp00001010010110 : Covers (-330761639/500000 : ℚ) vp00001010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101001011_0 : Blocks := edgeBlocks% "full/vectors/0000101001011-V-0000.bin"
noncomputable def vp0000101001011 : Blocks := vp0000101001011_0
private theorem bp00001010010110 : Branch 0 (-330761639/1000000 : ℚ) vp0000101001011 := by
  apply branch_left_normalized (c:=vp00001010010110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-330761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-330761639/500000 : ℚ) by norm_num]
  exact coverp00001010010110
private noncomputable def ep00001010010111_0 : Blocks := edgeBlocks% "full/vectors/00001010010111-E-0000.bin"
noncomputable def ep00001010010111 : Blocks := ep00001010010111_0
private theorem idp00001010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101001011.list =
    C ((2:ℤ)^78) * horner X vp00001010010111.list + horner X ep00001010010111.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010010111 : Branch 1 (-330761639/1000000 : ℚ) vp0000101001011 := by
  apply branch_checked idp00001010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-330761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-331261639/500000 : ℚ) by norm_num]
  exact coverp00001010010111
theorem coverp0000101001011 : Covers (-330761639/1000000 : ℚ) vp0000101001011 := join_branches bp00001010010110 bp00001010010111
private noncomputable def vp000010100101011_0 : Blocks := edgeBlocks% "full/vectors/000010100101011-V-0000.bin"
noncomputable def vp000010100101011 : Blocks := vp000010100101011_0
theorem coverp000010100101011 : Covers (-330511639/250000 : ℚ) vp000010100101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100101010_0 : Blocks := edgeBlocks% "full/vectors/000010100101010-V-0000.bin"
noncomputable def vp000010100101010 : Blocks := vp000010100101010_0
theorem coverp000010100101010 : Covers (-330261639/250000 : ℚ) vp000010100101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010010101_0 : Blocks := edgeBlocks% "full/vectors/00001010010101-V-0000.bin"
noncomputable def vp00001010010101 : Blocks := vp00001010010101_0
private theorem bp000010100101010 : Branch 0 (-330261639/500000 : ℚ) vp00001010010101 := by
  apply branch_left_normalized (c:=vp000010100101010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-330261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-330261639/250000 : ℚ) by norm_num]
  exact coverp000010100101010
private noncomputable def ep000010100101011_0 : Blocks := edgeBlocks% "full/vectors/000010100101011-E-0000.bin"
noncomputable def ep000010100101011 : Blocks := ep000010100101011_0
private theorem idp000010100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010010101.list =
    C ((2:ℤ)^48) * horner X vp000010100101011.list + horner X ep000010100101011.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100101011 : Branch 1 (-330261639/500000 : ℚ) vp00001010010101 := by
  apply branch_checked idp000010100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-330261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-330511639/250000 : ℚ) by norm_num]
  exact coverp000010100101011
theorem coverp00001010010101 : Covers (-330261639/500000 : ℚ) vp00001010010101 := join_branches bp000010100101010 bp000010100101011
private noncomputable def vp000010100101001_0 : Blocks := edgeBlocks% "full/vectors/000010100101001-V-0000.bin"
noncomputable def vp000010100101001 : Blocks := vp000010100101001_0
theorem coverp000010100101001 : Covers (-330011639/250000 : ℚ) vp000010100101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100101000_0 : Blocks := edgeBlocks% "full/vectors/000010100101000-V-0000.bin"
noncomputable def vp000010100101000 : Blocks := vp000010100101000_0
theorem coverp000010100101000 : Covers (-329761639/250000 : ℚ) vp000010100101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010010100_0 : Blocks := edgeBlocks% "full/vectors/00001010010100-V-0000.bin"
noncomputable def vp00001010010100 : Blocks := vp00001010010100_0
private theorem bp000010100101000 : Branch 0 (-329761639/500000 : ℚ) vp00001010010100 := by
  apply branch_left_normalized (c:=vp000010100101000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-329761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-329761639/250000 : ℚ) by norm_num]
  exact coverp000010100101000
private noncomputable def ep000010100101001_0 : Blocks := edgeBlocks% "full/vectors/000010100101001-E-0000.bin"
noncomputable def ep000010100101001 : Blocks := ep000010100101001_0
private theorem idp000010100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010010100.list =
    C ((2:ℤ)^48) * horner X vp000010100101001.list + horner X ep000010100101001.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100101001 : Branch 1 (-329761639/500000 : ℚ) vp00001010010100 := by
  apply branch_checked idp000010100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-329761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-330011639/250000 : ℚ) by norm_num]
  exact coverp000010100101001
theorem coverp00001010010100 : Covers (-329761639/500000 : ℚ) vp00001010010100 := join_branches bp000010100101000 bp000010100101001
private noncomputable def vp0000101001010_0 : Blocks := edgeBlocks% "full/vectors/0000101001010-V-0000.bin"
noncomputable def vp0000101001010 : Blocks := vp0000101001010_0
private theorem bp00001010010100 : Branch 0 (-329761639/1000000 : ℚ) vp0000101001010 := by
  apply branch_left_normalized (c:=vp00001010010100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-329761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-329761639/500000 : ℚ) by norm_num]
  exact coverp00001010010100
private noncomputable def ep00001010010101_0 : Blocks := edgeBlocks% "full/vectors/00001010010101-E-0000.bin"
noncomputable def ep00001010010101 : Blocks := ep00001010010101_0
private theorem idp00001010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101001010.list =
    C ((2:ℤ)^79) * horner X vp00001010010101.list + horner X ep00001010010101.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010010101 : Branch 1 (-329761639/1000000 : ℚ) vp0000101001010 := by
  apply branch_checked idp00001010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-329761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-330261639/500000 : ℚ) by norm_num]
  exact coverp00001010010101
theorem coverp0000101001010 : Covers (-329761639/1000000 : ℚ) vp0000101001010 := join_branches bp00001010010100 bp00001010010101
private noncomputable def vp000010100101_0 : Blocks := edgeBlocks% "full/vectors/000010100101-V-0000.bin"
private noncomputable def vp000010100101_1 : Blocks := edgeBlocks% "full/vectors/000010100101-V-0001.bin"
noncomputable def vp000010100101 : Blocks := (Blocks.join vp000010100101_0 vp000010100101_1)
private theorem bp0000101001010 : Branch 0 (-329761639/2000000 : ℚ) vp000010100101 := by
  apply branch_left_normalized (c:=vp0000101001010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-329761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-329761639/1000000 : ℚ) by norm_num]
  exact coverp0000101001010
private noncomputable def ep0000101001011_0 : Blocks := edgeBlocks% "full/vectors/0000101001011-E-0000.bin"
private noncomputable def ep0000101001011_1 : Blocks := edgeBlocks% "full/vectors/0000101001011-E-0001.bin"
noncomputable def ep0000101001011 : Blocks := (Blocks.join ep0000101001011_0 ep0000101001011_1)
private theorem idp0000101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010100101.list =
    C ((2:ℤ)^137) * horner X vp0000101001011.list + horner X ep0000101001011.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101001011 : Branch 1 (-329761639/2000000 : ℚ) vp000010100101 := by
  apply branch_checked idp0000101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-329761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-330761639/1000000 : ℚ) by norm_num]
  exact coverp0000101001011
theorem coverp000010100101 : Covers (-329761639/2000000 : ℚ) vp000010100101 := join_branches bp0000101001010 bp0000101001011
private noncomputable def vp000010100100111_0 : Blocks := edgeBlocks% "full/vectors/000010100100111-V-0000.bin"
noncomputable def vp000010100100111 : Blocks := vp000010100100111_0
theorem coverp000010100100111 : Covers (-329511639/250000 : ℚ) vp000010100100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100100110_0 : Blocks := edgeBlocks% "full/vectors/000010100100110-V-0000.bin"
noncomputable def vp000010100100110 : Blocks := vp000010100100110_0
theorem coverp000010100100110 : Covers (-329261639/250000 : ℚ) vp000010100100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010010011_0 : Blocks := edgeBlocks% "full/vectors/00001010010011-V-0000.bin"
noncomputable def vp00001010010011 : Blocks := vp00001010010011_0
private theorem bp000010100100110 : Branch 0 (-329261639/500000 : ℚ) vp00001010010011 := by
  apply branch_left_normalized (c:=vp000010100100110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-329261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-329261639/250000 : ℚ) by norm_num]
  exact coverp000010100100110
private noncomputable def ep000010100100111_0 : Blocks := edgeBlocks% "full/vectors/000010100100111-E-0000.bin"
noncomputable def ep000010100100111 : Blocks := ep000010100100111_0
private theorem idp000010100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010010011.list =
    C ((2:ℤ)^49) * horner X vp000010100100111.list + horner X ep000010100100111.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100100111 : Branch 1 (-329261639/500000 : ℚ) vp00001010010011 := by
  apply branch_checked idp000010100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-329261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-329511639/250000 : ℚ) by norm_num]
  exact coverp000010100100111
theorem coverp00001010010011 : Covers (-329261639/500000 : ℚ) vp00001010010011 := join_branches bp000010100100110 bp000010100100111
private noncomputable def vp000010100100101_0 : Blocks := edgeBlocks% "full/vectors/000010100100101-V-0000.bin"
noncomputable def vp000010100100101 : Blocks := vp000010100100101_0
theorem coverp000010100100101 : Covers (-329011639/250000 : ℚ) vp000010100100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100100100_0 : Blocks := edgeBlocks% "full/vectors/000010100100100-V-0000.bin"
noncomputable def vp000010100100100 : Blocks := vp000010100100100_0
theorem coverp000010100100100 : Covers (-328761639/250000 : ℚ) vp000010100100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010010010_0 : Blocks := edgeBlocks% "full/vectors/00001010010010-V-0000.bin"
noncomputable def vp00001010010010 : Blocks := vp00001010010010_0
private theorem bp000010100100100 : Branch 0 (-328761639/500000 : ℚ) vp00001010010010 := by
  apply branch_left_normalized (c:=vp000010100100100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-328761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-328761639/250000 : ℚ) by norm_num]
  exact coverp000010100100100
private noncomputable def ep000010100100101_0 : Blocks := edgeBlocks% "full/vectors/000010100100101-E-0000.bin"
noncomputable def ep000010100100101 : Blocks := ep000010100100101_0
private theorem idp000010100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010010010.list =
    C ((2:ℤ)^48) * horner X vp000010100100101.list + horner X ep000010100100101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100100101 : Branch 1 (-328761639/500000 : ℚ) vp00001010010010 := by
  apply branch_checked idp000010100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-328761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-329011639/250000 : ℚ) by norm_num]
  exact coverp000010100100101
theorem coverp00001010010010 : Covers (-328761639/500000 : ℚ) vp00001010010010 := join_branches bp000010100100100 bp000010100100101
private noncomputable def vp0000101001001_0 : Blocks := edgeBlocks% "full/vectors/0000101001001-V-0000.bin"
noncomputable def vp0000101001001 : Blocks := vp0000101001001_0
private theorem bp00001010010010 : Branch 0 (-328761639/1000000 : ℚ) vp0000101001001 := by
  apply branch_left_normalized (c:=vp00001010010010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-328761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-328761639/500000 : ℚ) by norm_num]
  exact coverp00001010010010
private noncomputable def ep00001010010011_0 : Blocks := edgeBlocks% "full/vectors/00001010010011-E-0000.bin"
noncomputable def ep00001010010011 : Blocks := ep00001010010011_0
private theorem idp00001010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101001001.list =
    C ((2:ℤ)^78) * horner X vp00001010010011.list + horner X ep00001010010011.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010010011 : Branch 1 (-328761639/1000000 : ℚ) vp0000101001001 := by
  apply branch_checked idp00001010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-328761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-329261639/500000 : ℚ) by norm_num]
  exact coverp00001010010011
theorem coverp0000101001001 : Covers (-328761639/1000000 : ℚ) vp0000101001001 := join_branches bp00001010010010 bp00001010010011
private noncomputable def vp000010100100011_0 : Blocks := edgeBlocks% "full/vectors/000010100100011-V-0000.bin"
noncomputable def vp000010100100011 : Blocks := vp000010100100011_0
theorem coverp000010100100011 : Covers (-328511639/250000 : ℚ) vp000010100100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100100010_0 : Blocks := edgeBlocks% "full/vectors/000010100100010-V-0000.bin"
noncomputable def vp000010100100010 : Blocks := vp000010100100010_0
theorem coverp000010100100010 : Covers (-328261639/250000 : ℚ) vp000010100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010010001_0 : Blocks := edgeBlocks% "full/vectors/00001010010001-V-0000.bin"
noncomputable def vp00001010010001 : Blocks := vp00001010010001_0
private theorem bp000010100100010 : Branch 0 (-328261639/500000 : ℚ) vp00001010010001 := by
  apply branch_left_normalized (c:=vp000010100100010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-328261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-328261639/250000 : ℚ) by norm_num]
  exact coverp000010100100010
private noncomputable def ep000010100100011_0 : Blocks := edgeBlocks% "full/vectors/000010100100011-E-0000.bin"
noncomputable def ep000010100100011 : Blocks := ep000010100100011_0
private theorem idp000010100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010010001.list =
    C ((2:ℤ)^48) * horner X vp000010100100011.list + horner X ep000010100100011.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100100011 : Branch 1 (-328261639/500000 : ℚ) vp00001010010001 := by
  apply branch_checked idp000010100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-328261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-328511639/250000 : ℚ) by norm_num]
  exact coverp000010100100011
theorem coverp00001010010001 : Covers (-328261639/500000 : ℚ) vp00001010010001 := join_branches bp000010100100010 bp000010100100011
private noncomputable def vp000010100100001_0 : Blocks := edgeBlocks% "full/vectors/000010100100001-V-0000.bin"
noncomputable def vp000010100100001 : Blocks := vp000010100100001_0
theorem coverp000010100100001 : Covers (-328011639/250000 : ℚ) vp000010100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100100000_0 : Blocks := edgeBlocks% "full/vectors/000010100100000-V-0000.bin"
noncomputable def vp000010100100000 : Blocks := vp000010100100000_0
theorem coverp000010100100000 : Covers (-327761639/250000 : ℚ) vp000010100100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010010000_0 : Blocks := edgeBlocks% "full/vectors/00001010010000-V-0000.bin"
noncomputable def vp00001010010000 : Blocks := vp00001010010000_0
private theorem bp000010100100000 : Branch 0 (-327761639/500000 : ℚ) vp00001010010000 := by
  apply branch_left_normalized (c:=vp000010100100000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-327761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-327761639/250000 : ℚ) by norm_num]
  exact coverp000010100100000
private noncomputable def ep000010100100001_0 : Blocks := edgeBlocks% "full/vectors/000010100100001-E-0000.bin"
noncomputable def ep000010100100001 : Blocks := ep000010100100001_0
private theorem idp000010100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010010000.list =
    C ((2:ℤ)^48) * horner X vp000010100100001.list + horner X ep000010100100001.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100100001 : Branch 1 (-327761639/500000 : ℚ) vp00001010010000 := by
  apply branch_checked idp000010100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-327761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-328011639/250000 : ℚ) by norm_num]
  exact coverp000010100100001
theorem coverp00001010010000 : Covers (-327761639/500000 : ℚ) vp00001010010000 := join_branches bp000010100100000 bp000010100100001
private noncomputable def vp0000101001000_0 : Blocks := edgeBlocks% "full/vectors/0000101001000-V-0000.bin"
noncomputable def vp0000101001000 : Blocks := vp0000101001000_0
private theorem bp00001010010000 : Branch 0 (-327761639/1000000 : ℚ) vp0000101001000 := by
  apply branch_left_normalized (c:=vp00001010010000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-327761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-327761639/500000 : ℚ) by norm_num]
  exact coverp00001010010000
private noncomputable def ep00001010010001_0 : Blocks := edgeBlocks% "full/vectors/00001010010001-E-0000.bin"
noncomputable def ep00001010010001 : Blocks := ep00001010010001_0
private theorem idp00001010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101001000.list =
    C ((2:ℤ)^77) * horner X vp00001010010001.list + horner X ep00001010010001.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010010001 : Branch 1 (-327761639/1000000 : ℚ) vp0000101001000 := by
  apply branch_checked idp00001010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-327761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-328261639/500000 : ℚ) by norm_num]
  exact coverp00001010010001
theorem coverp0000101001000 : Covers (-327761639/1000000 : ℚ) vp0000101001000 := join_branches bp00001010010000 bp00001010010001
private noncomputable def vp000010100100_0 : Blocks := edgeBlocks% "full/vectors/000010100100-V-0000.bin"
private noncomputable def vp000010100100_1 : Blocks := edgeBlocks% "full/vectors/000010100100-V-0001.bin"
noncomputable def vp000010100100 : Blocks := (Blocks.join vp000010100100_0 vp000010100100_1)
private theorem bp0000101001000 : Branch 0 (-327761639/2000000 : ℚ) vp000010100100 := by
  apply branch_left_normalized (c:=vp0000101001000) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-327761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-327761639/1000000 : ℚ) by norm_num]
  exact coverp0000101001000
private noncomputable def ep0000101001001_0 : Blocks := edgeBlocks% "full/vectors/0000101001001-E-0000.bin"
private noncomputable def ep0000101001001_1 : Blocks := edgeBlocks% "full/vectors/0000101001001-E-0001.bin"
noncomputable def ep0000101001001 : Blocks := (Blocks.join ep0000101001001_0 ep0000101001001_1)
private theorem idp0000101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010100100.list =
    C ((2:ℤ)^134) * horner X vp0000101001001.list + horner X ep0000101001001.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101001001 : Branch 1 (-327761639/2000000 : ℚ) vp000010100100 := by
  apply branch_checked idp0000101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-327761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-328761639/1000000 : ℚ) by norm_num]
  exact coverp0000101001001
theorem coverp000010100100 : Covers (-327761639/2000000 : ℚ) vp000010100100 := join_branches bp0000101001000 bp0000101001001
private noncomputable def vp00001010010_0 : Blocks := edgeBlocks% "full/vectors/00001010010-V-0000.bin"
private noncomputable def vp00001010010_1 : Blocks := edgeBlocks% "full/vectors/00001010010-V-0001.bin"
noncomputable def vp00001010010 : Blocks := (Blocks.join vp00001010010_0 vp00001010010_1)
private theorem bp000010100100 : Branch 0 (-327761639/4000000 : ℚ) vp00001010010 := by
  apply branch_left_normalized (c:=vp000010100100) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-327761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-327761639/2000000 : ℚ) by norm_num]
  exact coverp000010100100
private noncomputable def ep000010100101_0 : Blocks := edgeBlocks% "full/vectors/000010100101-E-0000.bin"
private noncomputable def ep000010100101_1 : Blocks := edgeBlocks% "full/vectors/000010100101-E-0001.bin"
noncomputable def ep000010100101 : Blocks := (Blocks.join ep000010100101_0 ep000010100101_1)
private theorem idp000010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010010.list =
    C ((2:ℤ)^249) * horner X vp000010100101.list + horner X ep000010100101.list := by
  exact edge_identity (B := (2:ℤ)^454) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100101 : Branch 1 (-327761639/4000000 : ℚ) vp00001010010 := by
  apply branch_checked idp000010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-327761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-329761639/2000000 : ℚ) by norm_num]
  exact coverp000010100101
theorem coverp00001010010 : Covers (-327761639/4000000 : ℚ) vp00001010010 := join_branches bp000010100100 bp000010100101
private noncomputable def vp0000101001_0 : Blocks := edgeBlocks% "full/vectors/0000101001-V-0000.bin"
private noncomputable def vp0000101001_1 : Blocks := edgeBlocks% "full/vectors/0000101001-V-0001.bin"
private noncomputable def vp0000101001_2 : Blocks := edgeBlocks% "full/vectors/0000101001-V-0002.bin"
private noncomputable def vp0000101001_3 : Blocks := edgeBlocks% "full/vectors/0000101001-V-0003.bin"
noncomputable def vp0000101001 : Blocks := (Blocks.join (Blocks.join vp0000101001_0 vp0000101001_1) (Blocks.join vp0000101001_2 vp0000101001_3))
private theorem bp00001010010 : Branch 0 (-327761639/8000000 : ℚ) vp0000101001 := by
  apply branch_left_normalized (c:=vp00001010010) (k:=0) (m:=238) (by decide +kernel)
  rw [show 2*(-327761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-327761639/4000000 : ℚ) by norm_num]
  exact coverp00001010010
private noncomputable def ep00001010011_0 : Blocks := edgeBlocks% "full/vectors/00001010011-E-0000.bin"
private noncomputable def ep00001010011_1 : Blocks := edgeBlocks% "full/vectors/00001010011-E-0001.bin"
private noncomputable def ep00001010011_2 : Blocks := edgeBlocks% "full/vectors/00001010011-E-0002.bin"
private noncomputable def ep00001010011_3 : Blocks := edgeBlocks% "full/vectors/00001010011-E-0003.bin"
noncomputable def ep00001010011 : Blocks := (Blocks.join (Blocks.join ep00001010011_0 ep00001010011_1) (Blocks.join ep00001010011_2 ep00001010011_3))
private theorem idp00001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101001.list =
    C ((2:ℤ)^477) * horner X vp00001010011.list + horner X ep00001010011.list := by
  exact edge_identity (B := (2:ℤ)^785) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010011 : Branch 1 (-327761639/8000000 : ℚ) vp0000101001 := by
  apply branch_checked idp00001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-327761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-331761639/4000000 : ℚ) by norm_num]
  exact coverp00001010011
theorem coverp0000101001 : Covers (-327761639/8000000 : ℚ) vp0000101001 := join_branches bp00001010010 bp00001010011
private noncomputable def vp00001010001111_0 : Blocks := edgeBlocks% "full/vectors/00001010001111-V-0000.bin"
noncomputable def vp00001010001111 : Blocks := vp00001010001111_0
theorem coverp00001010001111 : Covers (-327261639/500000 : ℚ) vp00001010001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010001110_0 : Blocks := edgeBlocks% "full/vectors/00001010001110-V-0000.bin"
noncomputable def vp00001010001110 : Blocks := vp00001010001110_0
theorem coverp00001010001110 : Covers (-326761639/500000 : ℚ) vp00001010001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101000111_0 : Blocks := edgeBlocks% "full/vectors/0000101000111-V-0000.bin"
noncomputable def vp0000101000111 : Blocks := vp0000101000111_0
private theorem bp00001010001110 : Branch 0 (-326761639/1000000 : ℚ) vp0000101000111 := by
  apply branch_left_normalized (c:=vp00001010001110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-326761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-326761639/500000 : ℚ) by norm_num]
  exact coverp00001010001110
private noncomputable def ep00001010001111_0 : Blocks := edgeBlocks% "full/vectors/00001010001111-E-0000.bin"
noncomputable def ep00001010001111 : Blocks := ep00001010001111_0
private theorem idp00001010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101000111.list =
    C ((2:ℤ)^77) * horner X vp00001010001111.list + horner X ep00001010001111.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010001111 : Branch 1 (-326761639/1000000 : ℚ) vp0000101000111 := by
  apply branch_checked idp00001010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-326761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-327261639/500000 : ℚ) by norm_num]
  exact coverp00001010001111
theorem coverp0000101000111 : Covers (-326761639/1000000 : ℚ) vp0000101000111 := join_branches bp00001010001110 bp00001010001111
private noncomputable def vp00001010001101_0 : Blocks := edgeBlocks% "full/vectors/00001010001101-V-0000.bin"
noncomputable def vp00001010001101 : Blocks := vp00001010001101_0
theorem coverp00001010001101 : Covers (-326261639/500000 : ℚ) vp00001010001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010001100_0 : Blocks := edgeBlocks% "full/vectors/00001010001100-V-0000.bin"
noncomputable def vp00001010001100 : Blocks := vp00001010001100_0
theorem coverp00001010001100 : Covers (-325761639/500000 : ℚ) vp00001010001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101000110_0 : Blocks := edgeBlocks% "full/vectors/0000101000110-V-0000.bin"
noncomputable def vp0000101000110 : Blocks := vp0000101000110_0
private theorem bp00001010001100 : Branch 0 (-325761639/1000000 : ℚ) vp0000101000110 := by
  apply branch_left_normalized (c:=vp00001010001100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-325761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-325761639/500000 : ℚ) by norm_num]
  exact coverp00001010001100
private noncomputable def ep00001010001101_0 : Blocks := edgeBlocks% "full/vectors/00001010001101-E-0000.bin"
noncomputable def ep00001010001101 : Blocks := ep00001010001101_0
private theorem idp00001010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101000110.list =
    C ((2:ℤ)^78) * horner X vp00001010001101.list + horner X ep00001010001101.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010001101 : Branch 1 (-325761639/1000000 : ℚ) vp0000101000110 := by
  apply branch_checked idp00001010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-325761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-326261639/500000 : ℚ) by norm_num]
  exact coverp00001010001101
theorem coverp0000101000110 : Covers (-325761639/1000000 : ℚ) vp0000101000110 := join_branches bp00001010001100 bp00001010001101
private noncomputable def vp000010100011_0 : Blocks := edgeBlocks% "full/vectors/000010100011-V-0000.bin"
private noncomputable def vp000010100011_1 : Blocks := edgeBlocks% "full/vectors/000010100011-V-0001.bin"
noncomputable def vp000010100011 : Blocks := (Blocks.join vp000010100011_0 vp000010100011_1)
private theorem bp0000101000110 : Branch 0 (-325761639/2000000 : ℚ) vp000010100011 := by
  apply branch_left_normalized (c:=vp0000101000110) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-325761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-325761639/1000000 : ℚ) by norm_num]
  exact coverp0000101000110
private noncomputable def ep0000101000111_0 : Blocks := edgeBlocks% "full/vectors/0000101000111-E-0000.bin"
private noncomputable def ep0000101000111_1 : Blocks := edgeBlocks% "full/vectors/0000101000111-E-0001.bin"
noncomputable def ep0000101000111 : Blocks := (Blocks.join ep0000101000111_0 ep0000101000111_1)
private theorem idp0000101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010100011.list =
    C ((2:ℤ)^136) * horner X vp0000101000111.list + horner X ep0000101000111.list := by
  exact edge_identity (B := (2:ℤ)^287) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101000111 : Branch 1 (-325761639/2000000 : ℚ) vp000010100011 := by
  apply branch_checked idp0000101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-325761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-326761639/1000000 : ℚ) by norm_num]
  exact coverp0000101000111
theorem coverp000010100011 : Covers (-325761639/2000000 : ℚ) vp000010100011 := join_branches bp0000101000110 bp0000101000111
private noncomputable def vp00001010001011_0 : Blocks := edgeBlocks% "full/vectors/00001010001011-V-0000.bin"
noncomputable def vp00001010001011 : Blocks := vp00001010001011_0
theorem coverp00001010001011 : Covers (-325261639/500000 : ℚ) vp00001010001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010001010_0 : Blocks := edgeBlocks% "full/vectors/00001010001010-V-0000.bin"
noncomputable def vp00001010001010 : Blocks := vp00001010001010_0
theorem coverp00001010001010 : Covers (-324761639/500000 : ℚ) vp00001010001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101000101_0 : Blocks := edgeBlocks% "full/vectors/0000101000101-V-0000.bin"
noncomputable def vp0000101000101 : Blocks := vp0000101000101_0
private theorem bp00001010001010 : Branch 0 (-324761639/1000000 : ℚ) vp0000101000101 := by
  apply branch_left_normalized (c:=vp00001010001010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-324761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-324761639/500000 : ℚ) by norm_num]
  exact coverp00001010001010
private noncomputable def ep00001010001011_0 : Blocks := edgeBlocks% "full/vectors/00001010001011-E-0000.bin"
noncomputable def ep00001010001011 : Blocks := ep00001010001011_0
private theorem idp00001010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101000101.list =
    C ((2:ℤ)^80) * horner X vp00001010001011.list + horner X ep00001010001011.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010001011 : Branch 1 (-324761639/1000000 : ℚ) vp0000101000101 := by
  apply branch_checked idp00001010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-324761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-325261639/500000 : ℚ) by norm_num]
  exact coverp00001010001011
theorem coverp0000101000101 : Covers (-324761639/1000000 : ℚ) vp0000101000101 := join_branches bp00001010001010 bp00001010001011
private noncomputable def vp00001010001001_0 : Blocks := edgeBlocks% "full/vectors/00001010001001-V-0000.bin"
noncomputable def vp00001010001001 : Blocks := vp00001010001001_0
theorem coverp00001010001001 : Covers (-324261639/500000 : ℚ) vp00001010001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100010001_0 : Blocks := edgeBlocks% "full/vectors/000010100010001-V-0000.bin"
noncomputable def vp000010100010001 : Blocks := vp000010100010001_0
theorem coverp000010100010001 : Covers (-324011639/250000 : ℚ) vp000010100010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100010000_0 : Blocks := edgeBlocks% "full/vectors/000010100010000-V-0000.bin"
noncomputable def vp000010100010000 : Blocks := vp000010100010000_0
theorem coverp000010100010000 : Covers (-323761639/250000 : ℚ) vp000010100010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010001000_0 : Blocks := edgeBlocks% "full/vectors/00001010001000-V-0000.bin"
noncomputable def vp00001010001000 : Blocks := vp00001010001000_0
private theorem bp000010100010000 : Branch 0 (-323761639/500000 : ℚ) vp00001010001000 := by
  apply branch_left_normalized (c:=vp000010100010000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-323761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-323761639/250000 : ℚ) by norm_num]
  exact coverp000010100010000
private noncomputable def ep000010100010001_0 : Blocks := edgeBlocks% "full/vectors/000010100010001-E-0000.bin"
noncomputable def ep000010100010001 : Blocks := ep000010100010001_0
private theorem idp000010100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010001000.list =
    C ((2:ℤ)^47) * horner X vp000010100010001.list + horner X ep000010100010001.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100010001 : Branch 1 (-323761639/500000 : ℚ) vp00001010001000 := by
  apply branch_checked idp000010100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-323761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-324011639/250000 : ℚ) by norm_num]
  exact coverp000010100010001
theorem coverp00001010001000 : Covers (-323761639/500000 : ℚ) vp00001010001000 := join_branches bp000010100010000 bp000010100010001
private noncomputable def vp0000101000100_0 : Blocks := edgeBlocks% "full/vectors/0000101000100-V-0000.bin"
noncomputable def vp0000101000100 : Blocks := vp0000101000100_0
private theorem bp00001010001000 : Branch 0 (-323761639/1000000 : ℚ) vp0000101000100 := by
  apply branch_left_normalized (c:=vp00001010001000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-323761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-323761639/500000 : ℚ) by norm_num]
  exact coverp00001010001000
private noncomputable def ep00001010001001_0 : Blocks := edgeBlocks% "full/vectors/00001010001001-E-0000.bin"
noncomputable def ep00001010001001 : Blocks := ep00001010001001_0
private theorem idp00001010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101000100.list =
    C ((2:ℤ)^78) * horner X vp00001010001001.list + horner X ep00001010001001.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010001001 : Branch 1 (-323761639/1000000 : ℚ) vp0000101000100 := by
  apply branch_checked idp00001010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-323761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-324261639/500000 : ℚ) by norm_num]
  exact coverp00001010001001
theorem coverp0000101000100 : Covers (-323761639/1000000 : ℚ) vp0000101000100 := join_branches bp00001010001000 bp00001010001001
private noncomputable def vp000010100010_0 : Blocks := edgeBlocks% "full/vectors/000010100010-V-0000.bin"
private noncomputable def vp000010100010_1 : Blocks := edgeBlocks% "full/vectors/000010100010-V-0001.bin"
noncomputable def vp000010100010 : Blocks := (Blocks.join vp000010100010_0 vp000010100010_1)
private theorem bp0000101000100 : Branch 0 (-323761639/2000000 : ℚ) vp000010100010 := by
  apply branch_left_normalized (c:=vp0000101000100) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-323761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-323761639/1000000 : ℚ) by norm_num]
  exact coverp0000101000100
private noncomputable def ep0000101000101_0 : Blocks := edgeBlocks% "full/vectors/0000101000101-E-0000.bin"
private noncomputable def ep0000101000101_1 : Blocks := edgeBlocks% "full/vectors/0000101000101-E-0001.bin"
noncomputable def ep0000101000101 : Blocks := (Blocks.join ep0000101000101_0 ep0000101000101_1)
private theorem idp0000101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010100010.list =
    C ((2:ℤ)^138) * horner X vp0000101000101.list + horner X ep0000101000101.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101000101 : Branch 1 (-323761639/2000000 : ℚ) vp000010100010 := by
  apply branch_checked idp0000101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-323761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-324761639/1000000 : ℚ) by norm_num]
  exact coverp0000101000101
theorem coverp000010100010 : Covers (-323761639/2000000 : ℚ) vp000010100010 := join_branches bp0000101000100 bp0000101000101
private noncomputable def vp00001010001_0 : Blocks := edgeBlocks% "full/vectors/00001010001-V-0000.bin"
private noncomputable def vp00001010001_1 : Blocks := edgeBlocks% "full/vectors/00001010001-V-0001.bin"
noncomputable def vp00001010001 : Blocks := (Blocks.join vp00001010001_0 vp00001010001_1)
private theorem bp000010100010 : Branch 0 (-323761639/4000000 : ℚ) vp00001010001 := by
  apply branch_left_normalized (c:=vp000010100010) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-323761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-323761639/2000000 : ℚ) by norm_num]
  exact coverp000010100010
private noncomputable def ep000010100011_0 : Blocks := edgeBlocks% "full/vectors/000010100011-E-0000.bin"
private noncomputable def ep000010100011_1 : Blocks := edgeBlocks% "full/vectors/000010100011-E-0001.bin"
noncomputable def ep000010100011 : Blocks := (Blocks.join ep000010100011_0 ep000010100011_1)
private theorem idp000010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010001.list =
    C ((2:ℤ)^254) * horner X vp000010100011.list + horner X ep000010100011.list := by
  exact edge_identity (B := (2:ℤ)^458) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100011 : Branch 1 (-323761639/4000000 : ℚ) vp00001010001 := by
  apply branch_checked idp000010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-323761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-325761639/2000000 : ℚ) by norm_num]
  exact coverp000010100011
theorem coverp00001010001 : Covers (-323761639/4000000 : ℚ) vp00001010001 := join_branches bp000010100010 bp000010100011
private noncomputable def vp000010100001111_0 : Blocks := edgeBlocks% "full/vectors/000010100001111-V-0000.bin"
noncomputable def vp000010100001111 : Blocks := vp000010100001111_0
theorem coverp000010100001111 : Covers (-323511639/250000 : ℚ) vp000010100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010100001110_0 : Blocks := edgeBlocks% "full/vectors/000010100001110-V-0000.bin"
noncomputable def vp000010100001110 : Blocks := vp000010100001110_0
theorem coverp000010100001110 : Covers (-323261639/250000 : ℚ) vp000010100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010000111_0 : Blocks := edgeBlocks% "full/vectors/00001010000111-V-0000.bin"
noncomputable def vp00001010000111 : Blocks := vp00001010000111_0
private theorem bp000010100001110 : Branch 0 (-323261639/500000 : ℚ) vp00001010000111 := by
  apply branch_left_normalized (c:=vp000010100001110) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-323261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-323261639/250000 : ℚ) by norm_num]
  exact coverp000010100001110
private noncomputable def ep000010100001111_0 : Blocks := edgeBlocks% "full/vectors/000010100001111-E-0000.bin"
noncomputable def ep000010100001111 : Blocks := ep000010100001111_0
private theorem idp000010100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010000111.list =
    C ((2:ℤ)^47) * horner X vp000010100001111.list + horner X ep000010100001111.list := by
  exact edge_identity (B := (2:ℤ)^160) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100001111 : Branch 1 (-323261639/500000 : ℚ) vp00001010000111 := by
  apply branch_checked idp000010100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-323261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-323511639/250000 : ℚ) by norm_num]
  exact coverp000010100001111
theorem coverp00001010000111 : Covers (-323261639/500000 : ℚ) vp00001010000111 := join_branches bp000010100001110 bp000010100001111
private noncomputable def vp00001010000110_0 : Blocks := edgeBlocks% "full/vectors/00001010000110-V-0000.bin"
noncomputable def vp00001010000110 : Blocks := vp00001010000110_0
theorem coverp00001010000110 : Covers (-322761639/500000 : ℚ) vp00001010000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101000011_0 : Blocks := edgeBlocks% "full/vectors/0000101000011-V-0000.bin"
noncomputable def vp0000101000011 : Blocks := vp0000101000011_0
private theorem bp00001010000110 : Branch 0 (-322761639/1000000 : ℚ) vp0000101000011 := by
  apply branch_left_normalized (c:=vp00001010000110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-322761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-322761639/500000 : ℚ) by norm_num]
  exact coverp00001010000110
private noncomputable def ep00001010000111_0 : Blocks := edgeBlocks% "full/vectors/00001010000111-E-0000.bin"
noncomputable def ep00001010000111 : Blocks := ep00001010000111_0
private theorem idp00001010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101000011.list =
    C ((2:ℤ)^75) * horner X vp00001010000111.list + horner X ep00001010000111.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010000111 : Branch 1 (-322761639/1000000 : ℚ) vp0000101000011 := by
  apply branch_checked idp00001010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-322761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-323261639/500000 : ℚ) by norm_num]
  exact coverp00001010000111
theorem coverp0000101000011 : Covers (-322761639/1000000 : ℚ) vp0000101000011 := join_branches bp00001010000110 bp00001010000111
private noncomputable def vp00001010000101_0 : Blocks := edgeBlocks% "full/vectors/00001010000101-V-0000.bin"
noncomputable def vp00001010000101 : Blocks := vp00001010000101_0
theorem coverp00001010000101 : Covers (-322261639/500000 : ℚ) vp00001010000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010000100_0 : Blocks := edgeBlocks% "full/vectors/00001010000100-V-0000.bin"
noncomputable def vp00001010000100 : Blocks := vp00001010000100_0
theorem coverp00001010000100 : Covers (-321761639/500000 : ℚ) vp00001010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101000010_0 : Blocks := edgeBlocks% "full/vectors/0000101000010-V-0000.bin"
noncomputable def vp0000101000010 : Blocks := vp0000101000010_0
private theorem bp00001010000100 : Branch 0 (-321761639/1000000 : ℚ) vp0000101000010 := by
  apply branch_left_normalized (c:=vp00001010000100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-321761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-321761639/500000 : ℚ) by norm_num]
  exact coverp00001010000100
private noncomputable def ep00001010000101_0 : Blocks := edgeBlocks% "full/vectors/00001010000101-E-0000.bin"
noncomputable def ep00001010000101 : Blocks := ep00001010000101_0
private theorem idp00001010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101000010.list =
    C ((2:ℤ)^75) * horner X vp00001010000101.list + horner X ep00001010000101.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010000101 : Branch 1 (-321761639/1000000 : ℚ) vp0000101000010 := by
  apply branch_checked idp00001010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-321761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-322261639/500000 : ℚ) by norm_num]
  exact coverp00001010000101
theorem coverp0000101000010 : Covers (-321761639/1000000 : ℚ) vp0000101000010 := join_branches bp00001010000100 bp00001010000101
private noncomputable def vp000010100001_0 : Blocks := edgeBlocks% "full/vectors/000010100001-V-0000.bin"
noncomputable def vp000010100001 : Blocks := vp000010100001_0
private theorem bp0000101000010 : Branch 0 (-321761639/2000000 : ℚ) vp000010100001 := by
  apply branch_left_normalized (c:=vp0000101000010) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-321761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-321761639/1000000 : ℚ) by norm_num]
  exact coverp0000101000010
private noncomputable def ep0000101000011_0 : Blocks := edgeBlocks% "full/vectors/0000101000011-E-0000.bin"
noncomputable def ep0000101000011 : Blocks := ep0000101000011_0
private theorem idp0000101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010100001.list =
    C ((2:ℤ)^132) * horner X vp0000101000011.list + horner X ep0000101000011.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101000011 : Branch 1 (-321761639/2000000 : ℚ) vp000010100001 := by
  apply branch_checked idp0000101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-321761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-322761639/1000000 : ℚ) by norm_num]
  exact coverp0000101000011
theorem coverp000010100001 : Covers (-321761639/2000000 : ℚ) vp000010100001 := join_branches bp0000101000010 bp0000101000011
private noncomputable def vp00001010000011_0 : Blocks := edgeBlocks% "full/vectors/00001010000011-V-0000.bin"
noncomputable def vp00001010000011 : Blocks := vp00001010000011_0
theorem coverp00001010000011 : Covers (-321261639/500000 : ℚ) vp00001010000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010000010_0 : Blocks := edgeBlocks% "full/vectors/00001010000010-V-0000.bin"
noncomputable def vp00001010000010 : Blocks := vp00001010000010_0
theorem coverp00001010000010 : Covers (-320761639/500000 : ℚ) vp00001010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101000001_0 : Blocks := edgeBlocks% "full/vectors/0000101000001-V-0000.bin"
noncomputable def vp0000101000001 : Blocks := vp0000101000001_0
private theorem bp00001010000010 : Branch 0 (-320761639/1000000 : ℚ) vp0000101000001 := by
  apply branch_left_normalized (c:=vp00001010000010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-320761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-320761639/500000 : ℚ) by norm_num]
  exact coverp00001010000010
private noncomputable def ep00001010000011_0 : Blocks := edgeBlocks% "full/vectors/00001010000011-E-0000.bin"
noncomputable def ep00001010000011 : Blocks := ep00001010000011_0
private theorem idp00001010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101000001.list =
    C ((2:ℤ)^74) * horner X vp00001010000011.list + horner X ep00001010000011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010000011 : Branch 1 (-320761639/1000000 : ℚ) vp0000101000001 := by
  apply branch_checked idp00001010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-320761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-321261639/500000 : ℚ) by norm_num]
  exact coverp00001010000011
theorem coverp0000101000001 : Covers (-320761639/1000000 : ℚ) vp0000101000001 := join_branches bp00001010000010 bp00001010000011
private noncomputable def vp00001010000001_0 : Blocks := edgeBlocks% "full/vectors/00001010000001-V-0000.bin"
noncomputable def vp00001010000001 : Blocks := vp00001010000001_0
theorem coverp00001010000001 : Covers (-320261639/500000 : ℚ) vp00001010000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010000000_0 : Blocks := edgeBlocks% "full/vectors/00001010000000-V-0000.bin"
noncomputable def vp00001010000000 : Blocks := vp00001010000000_0
theorem coverp00001010000000 : Covers (-319761639/500000 : ℚ) vp00001010000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101000000_0 : Blocks := edgeBlocks% "full/vectors/0000101000000-V-0000.bin"
noncomputable def vp0000101000000 : Blocks := vp0000101000000_0
private theorem bp00001010000000 : Branch 0 (-319761639/1000000 : ℚ) vp0000101000000 := by
  apply branch_left_normalized (c:=vp00001010000000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-319761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-319761639/500000 : ℚ) by norm_num]
  exact coverp00001010000000
private noncomputable def ep00001010000001_0 : Blocks := edgeBlocks% "full/vectors/00001010000001-E-0000.bin"
noncomputable def ep00001010000001 : Blocks := ep00001010000001_0
private theorem idp00001010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101000000.list =
    C ((2:ℤ)^75) * horner X vp00001010000001.list + horner X ep00001010000001.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010000001 : Branch 1 (-319761639/1000000 : ℚ) vp0000101000000 := by
  apply branch_checked idp00001010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-319761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-320261639/500000 : ℚ) by norm_num]
  exact coverp00001010000001
theorem coverp0000101000000 : Covers (-319761639/1000000 : ℚ) vp0000101000000 := join_branches bp00001010000000 bp00001010000001
private noncomputable def vp000010100000_0 : Blocks := edgeBlocks% "full/vectors/000010100000-V-0000.bin"
noncomputable def vp000010100000 : Blocks := vp000010100000_0
private theorem bp0000101000000 : Branch 0 (-319761639/2000000 : ℚ) vp000010100000 := by
  apply branch_left_normalized (c:=vp0000101000000) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-319761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-319761639/1000000 : ℚ) by norm_num]
  exact coverp0000101000000
private noncomputable def ep0000101000001_0 : Blocks := edgeBlocks% "full/vectors/0000101000001-E-0000.bin"
noncomputable def ep0000101000001 : Blocks := ep0000101000001_0
private theorem idp0000101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010100000.list =
    C ((2:ℤ)^132) * horner X vp0000101000001.list + horner X ep0000101000001.list := by
  exact edge_identity (B := (2:ℤ)^278) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101000001 : Branch 1 (-319761639/2000000 : ℚ) vp000010100000 := by
  apply branch_checked idp0000101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-319761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-320761639/1000000 : ℚ) by norm_num]
  exact coverp0000101000001
theorem coverp000010100000 : Covers (-319761639/2000000 : ℚ) vp000010100000 := join_branches bp0000101000000 bp0000101000001
private noncomputable def vp00001010000_0 : Blocks := edgeBlocks% "full/vectors/00001010000-V-0000.bin"
private noncomputable def vp00001010000_1 : Blocks := edgeBlocks% "full/vectors/00001010000-V-0001.bin"
noncomputable def vp00001010000 : Blocks := (Blocks.join vp00001010000_0 vp00001010000_1)
private theorem bp000010100000 : Branch 0 (-319761639/4000000 : ℚ) vp00001010000 := by
  apply branch_left_normalized (c:=vp000010100000) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-319761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-319761639/2000000 : ℚ) by norm_num]
  exact coverp000010100000
private noncomputable def ep000010100001_0 : Blocks := edgeBlocks% "full/vectors/000010100001-E-0000.bin"
private noncomputable def ep000010100001_1 : Blocks := edgeBlocks% "full/vectors/000010100001-E-0001.bin"
noncomputable def ep000010100001 : Blocks := (Blocks.join ep000010100001_0 ep000010100001_1)
private theorem idp000010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010000.list =
    C ((2:ℤ)^246) * horner X vp000010100001.list + horner X ep000010100001.list := by
  exact edge_identity (B := (2:ℤ)^446) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010100001 : Branch 1 (-319761639/4000000 : ℚ) vp00001010000 := by
  apply branch_checked idp000010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-319761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-321761639/2000000 : ℚ) by norm_num]
  exact coverp000010100001
theorem coverp00001010000 : Covers (-319761639/4000000 : ℚ) vp00001010000 := join_branches bp000010100000 bp000010100001
private noncomputable def vp0000101000_0 : Blocks := edgeBlocks% "full/vectors/0000101000-V-0000.bin"
private noncomputable def vp0000101000_1 : Blocks := edgeBlocks% "full/vectors/0000101000-V-0001.bin"
private noncomputable def vp0000101000_2 : Blocks := edgeBlocks% "full/vectors/0000101000-V-0002.bin"
private noncomputable def vp0000101000_3 : Blocks := edgeBlocks% "full/vectors/0000101000-V-0003.bin"
noncomputable def vp0000101000 : Blocks := (Blocks.join (Blocks.join vp0000101000_0 vp0000101000_1) (Blocks.join vp0000101000_2 vp0000101000_3))
private theorem bp00001010000 : Branch 0 (-319761639/8000000 : ℚ) vp0000101000 := by
  apply branch_left_normalized (c:=vp00001010000) (k:=0) (m:=236) (by decide +kernel)
  rw [show 2*(-319761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-319761639/4000000 : ℚ) by norm_num]
  exact coverp00001010000
private noncomputable def ep00001010001_0 : Blocks := edgeBlocks% "full/vectors/00001010001-E-0000.bin"
private noncomputable def ep00001010001_1 : Blocks := edgeBlocks% "full/vectors/00001010001-E-0001.bin"
private noncomputable def ep00001010001_2 : Blocks := edgeBlocks% "full/vectors/00001010001-E-0002.bin"
private noncomputable def ep00001010001_3 : Blocks := edgeBlocks% "full/vectors/00001010001-E-0003.bin"
noncomputable def ep00001010001 : Blocks := (Blocks.join (Blocks.join ep00001010001_0 ep00001010001_1) (Blocks.join ep00001010001_2 ep00001010001_3))
private theorem idp00001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101000.list =
    C ((2:ℤ)^470) * horner X vp00001010001.list + horner X ep00001010001.list := by
  exact edge_identity (B := (2:ℤ)^781) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010001 : Branch 1 (-319761639/8000000 : ℚ) vp0000101000 := by
  apply branch_checked idp00001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-319761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-323761639/4000000 : ℚ) by norm_num]
  exact coverp00001010001
theorem coverp0000101000 : Covers (-319761639/8000000 : ℚ) vp0000101000 := join_branches bp00001010000 bp00001010001
private noncomputable def vp000010100_0 : Blocks := edgeBlocks% "full/vectors/000010100-V-0000.bin"
private noncomputable def vp000010100_1 : Blocks := edgeBlocks% "full/vectors/000010100-V-0001.bin"
private noncomputable def vp000010100_2 : Blocks := edgeBlocks% "full/vectors/000010100-V-0002.bin"
private noncomputable def vp000010100_3 : Blocks := edgeBlocks% "full/vectors/000010100-V-0003.bin"
private noncomputable def vp000010100_4 : Blocks := edgeBlocks% "full/vectors/000010100-V-0004.bin"
private noncomputable def vp000010100_5 : Blocks := edgeBlocks% "full/vectors/000010100-V-0005.bin"
private noncomputable def vp000010100_6 : Blocks := edgeBlocks% "full/vectors/000010100-V-0006.bin"
noncomputable def vp000010100 : Blocks := (Blocks.join (Blocks.join vp000010100_0 (Blocks.join vp000010100_1 vp000010100_2)) (Blocks.join (Blocks.join vp000010100_3 vp000010100_4) (Blocks.join vp000010100_5 vp000010100_6)))
private theorem bp0000101000 : Branch 0 (-319761639/16000000 : ℚ) vp000010100 := by
  apply branch_left_normalized (c:=vp0000101000) (k:=0) (m:=454) (by decide +kernel)
  rw [show 2*(-319761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-319761639/8000000 : ℚ) by norm_num]
  exact coverp0000101000
private noncomputable def ep0000101001_0 : Blocks := edgeBlocks% "full/vectors/0000101001-E-0000.bin"
private noncomputable def ep0000101001_1 : Blocks := edgeBlocks% "full/vectors/0000101001-E-0001.bin"
private noncomputable def ep0000101001_2 : Blocks := edgeBlocks% "full/vectors/0000101001-E-0002.bin"
private noncomputable def ep0000101001_3 : Blocks := edgeBlocks% "full/vectors/0000101001-E-0003.bin"
private noncomputable def ep0000101001_4 : Blocks := edgeBlocks% "full/vectors/0000101001-E-0004.bin"
private noncomputable def ep0000101001_5 : Blocks := edgeBlocks% "full/vectors/0000101001-E-0005.bin"
private noncomputable def ep0000101001_6 : Blocks := edgeBlocks% "full/vectors/0000101001-E-0006.bin"
noncomputable def ep0000101001 : Blocks := (Blocks.join (Blocks.join ep0000101001_0 (Blocks.join ep0000101001_1 ep0000101001_2)) (Blocks.join (Blocks.join ep0000101001_3 ep0000101001_4) (Blocks.join ep0000101001_5 ep0000101001_6)))
private theorem idp0000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010100.list =
    C ((2:ℤ)^925) * horner X vp0000101001.list + horner X ep0000101001.list := by
  exact edge_identity (B := (2:ℤ)^1444) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101001 : Branch 1 (-319761639/16000000 : ℚ) vp000010100 := by
  apply branch_checked idp0000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-319761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-327761639/8000000 : ℚ) by norm_num]
  exact coverp0000101001
theorem coverp000010100 : Covers (-319761639/16000000 : ℚ) vp000010100 := join_branches bp0000101000 bp0000101001
private noncomputable def vp00001010_0 : Blocks := edgeBlocks% "full/vectors/00001010-V-0000.bin"
private noncomputable def vp00001010_1 : Blocks := edgeBlocks% "full/vectors/00001010-V-0001.bin"
private noncomputable def vp00001010_2 : Blocks := edgeBlocks% "full/vectors/00001010-V-0002.bin"
private noncomputable def vp00001010_3 : Blocks := edgeBlocks% "full/vectors/00001010-V-0003.bin"
private noncomputable def vp00001010_4 : Blocks := edgeBlocks% "full/vectors/00001010-V-0004.bin"
private noncomputable def vp00001010_5 : Blocks := edgeBlocks% "full/vectors/00001010-V-0005.bin"
private noncomputable def vp00001010_6 : Blocks := edgeBlocks% "full/vectors/00001010-V-0006.bin"
private noncomputable def vp00001010_7 : Blocks := edgeBlocks% "full/vectors/00001010-V-0007.bin"
private noncomputable def vp00001010_8 : Blocks := edgeBlocks% "full/vectors/00001010-V-0008.bin"
private noncomputable def vp00001010_9 : Blocks := edgeBlocks% "full/vectors/00001010-V-0009.bin"
private noncomputable def vp00001010_10 : Blocks := edgeBlocks% "full/vectors/00001010-V-0010.bin"
private noncomputable def vp00001010_11 : Blocks := edgeBlocks% "full/vectors/00001010-V-0011.bin"
private noncomputable def vp00001010_12 : Blocks := edgeBlocks% "full/vectors/00001010-V-0012.bin"
private noncomputable def vp00001010_13 : Blocks := edgeBlocks% "full/vectors/00001010-V-0013.bin"
noncomputable def vp00001010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00001010_0 (Blocks.join vp00001010_1 vp00001010_2)) (Blocks.join (Blocks.join vp00001010_3 vp00001010_4) (Blocks.join vp00001010_5 vp00001010_6))) (Blocks.join (Blocks.join vp00001010_7 (Blocks.join vp00001010_8 vp00001010_9)) (Blocks.join (Blocks.join vp00001010_10 vp00001010_11) (Blocks.join vp00001010_12 vp00001010_13))))
private theorem bp000010100 : Branch 0 (-319761639/32000000 : ℚ) vp00001010 := by
  apply branch_left_normalized (c:=vp000010100) (k:=0) (m:=885) (by decide +kernel)
  rw [show 2*(-319761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-319761639/16000000 : ℚ) by norm_num]
  exact coverp000010100
private noncomputable def ep000010101_0 : Blocks := edgeBlocks% "full/vectors/000010101-E-0000.bin"
private noncomputable def ep000010101_1 : Blocks := edgeBlocks% "full/vectors/000010101-E-0001.bin"
private noncomputable def ep000010101_2 : Blocks := edgeBlocks% "full/vectors/000010101-E-0002.bin"
private noncomputable def ep000010101_3 : Blocks := edgeBlocks% "full/vectors/000010101-E-0003.bin"
private noncomputable def ep000010101_4 : Blocks := edgeBlocks% "full/vectors/000010101-E-0004.bin"
private noncomputable def ep000010101_5 : Blocks := edgeBlocks% "full/vectors/000010101-E-0005.bin"
private noncomputable def ep000010101_6 : Blocks := edgeBlocks% "full/vectors/000010101-E-0006.bin"
private noncomputable def ep000010101_7 : Blocks := edgeBlocks% "full/vectors/000010101-E-0007.bin"
private noncomputable def ep000010101_8 : Blocks := edgeBlocks% "full/vectors/000010101-E-0008.bin"
private noncomputable def ep000010101_9 : Blocks := edgeBlocks% "full/vectors/000010101-E-0009.bin"
private noncomputable def ep000010101_10 : Blocks := edgeBlocks% "full/vectors/000010101-E-0010.bin"
private noncomputable def ep000010101_11 : Blocks := edgeBlocks% "full/vectors/000010101-E-0011.bin"
private noncomputable def ep000010101_12 : Blocks := edgeBlocks% "full/vectors/000010101-E-0012.bin"
private noncomputable def ep000010101_13 : Blocks := edgeBlocks% "full/vectors/000010101-E-0013.bin"
noncomputable def ep000010101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000010101_0 (Blocks.join ep000010101_1 ep000010101_2)) (Blocks.join (Blocks.join ep000010101_3 ep000010101_4) (Blocks.join ep000010101_5 ep000010101_6))) (Blocks.join (Blocks.join ep000010101_7 (Blocks.join ep000010101_8 ep000010101_9)) (Blocks.join (Blocks.join ep000010101_10 ep000010101_11) (Blocks.join ep000010101_12 ep000010101_13))))
private theorem idp000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010.list =
    C ((2:ℤ)^1813) * horner X vp000010101.list + horner X ep000010101.list := by
  exact edge_identity (B := (2:ℤ)^2748) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101 : Branch 1 (-319761639/32000000 : ℚ) vp00001010 := by
  apply branch_checked idp000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-319761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-335761639/16000000 : ℚ) by norm_num]
  exact coverp000010101
theorem coverp00001010 : Covers (-319761639/32000000 : ℚ) vp00001010 := join_branches bp000010100 bp000010101
end NextProof.EdgeFull

