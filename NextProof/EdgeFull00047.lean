import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00046

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000001110111111_0 : Blocks := edgeBlocks% "full/vectors/000001110111111-V-0000.bin"
noncomputable def vp000001110111111 : Blocks := vp000001110111111_0
theorem coverp000001110111111 : Covers (-239511639/250000 : ℚ) vp000001110111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110111110_0 : Blocks := edgeBlocks% "full/vectors/000001110111110-V-0000.bin"
noncomputable def vp000001110111110 : Blocks := vp000001110111110_0
theorem coverp000001110111110 : Covers (-239261639/250000 : ℚ) vp000001110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111011111_0 : Blocks := edgeBlocks% "full/vectors/00000111011111-V-0000.bin"
noncomputable def vp00000111011111 : Blocks := vp00000111011111_0
private theorem bp000001110111110 : Branch 0 (-239261639/500000 : ℚ) vp00000111011111 := by
  apply branch_left_normalized (c:=vp000001110111110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-239261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-239261639/250000 : ℚ) by norm_num]
  exact coverp000001110111110
private noncomputable def ep000001110111111_0 : Blocks := edgeBlocks% "full/vectors/000001110111111-E-0000.bin"
noncomputable def ep000001110111111 : Blocks := ep000001110111111_0
private theorem idp000001110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111011111.list =
    C ((2:ℤ)^53) * horner X vp000001110111111.list + horner X ep000001110111111.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110111111 : Branch 1 (-239261639/500000 : ℚ) vp00000111011111 := by
  apply branch_checked idp000001110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-239261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-239511639/250000 : ℚ) by norm_num]
  exact coverp000001110111111
theorem coverp00000111011111 : Covers (-239261639/500000 : ℚ) vp00000111011111 := join_branches bp000001110111110 bp000001110111111
private noncomputable def vp000001110111101_0 : Blocks := edgeBlocks% "full/vectors/000001110111101-V-0000.bin"
noncomputable def vp000001110111101 : Blocks := vp000001110111101_0
theorem coverp000001110111101 : Covers (-239011639/250000 : ℚ) vp000001110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110111100_0 : Blocks := edgeBlocks% "full/vectors/000001110111100-V-0000.bin"
noncomputable def vp000001110111100 : Blocks := vp000001110111100_0
theorem coverp000001110111100 : Covers (-238761639/250000 : ℚ) vp000001110111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111011110_0 : Blocks := edgeBlocks% "full/vectors/00000111011110-V-0000.bin"
noncomputable def vp00000111011110 : Blocks := vp00000111011110_0
private theorem bp000001110111100 : Branch 0 (-238761639/500000 : ℚ) vp00000111011110 := by
  apply branch_left_normalized (c:=vp000001110111100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-238761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-238761639/250000 : ℚ) by norm_num]
  exact coverp000001110111100
private noncomputable def ep000001110111101_0 : Blocks := edgeBlocks% "full/vectors/000001110111101-E-0000.bin"
noncomputable def ep000001110111101 : Blocks := ep000001110111101_0
private theorem idp000001110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111011110.list =
    C ((2:ℤ)^53) * horner X vp000001110111101.list + horner X ep000001110111101.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110111101 : Branch 1 (-238761639/500000 : ℚ) vp00000111011110 := by
  apply branch_checked idp000001110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-238761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-239011639/250000 : ℚ) by norm_num]
  exact coverp000001110111101
theorem coverp00000111011110 : Covers (-238761639/500000 : ℚ) vp00000111011110 := join_branches bp000001110111100 bp000001110111101
private noncomputable def vp0000011101111_0 : Blocks := edgeBlocks% "full/vectors/0000011101111-V-0000.bin"
noncomputable def vp0000011101111 : Blocks := vp0000011101111_0
private theorem bp00000111011110 : Branch 0 (-238761639/1000000 : ℚ) vp0000011101111 := by
  apply branch_left_normalized (c:=vp00000111011110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-238761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-238761639/500000 : ℚ) by norm_num]
  exact coverp00000111011110
private noncomputable def ep00000111011111_0 : Blocks := edgeBlocks% "full/vectors/00000111011111-E-0000.bin"
noncomputable def ep00000111011111 : Blocks := ep00000111011111_0
private theorem idp00000111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011101111.list =
    C ((2:ℤ)^88) * horner X vp00000111011111.list + horner X ep00000111011111.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111011111 : Branch 1 (-238761639/1000000 : ℚ) vp0000011101111 := by
  apply branch_checked idp00000111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-238761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-239261639/500000 : ℚ) by norm_num]
  exact coverp00000111011111
theorem coverp0000011101111 : Covers (-238761639/1000000 : ℚ) vp0000011101111 := join_branches bp00000111011110 bp00000111011111
private noncomputable def vp000001110111011_0 : Blocks := edgeBlocks% "full/vectors/000001110111011-V-0000.bin"
noncomputable def vp000001110111011 : Blocks := vp000001110111011_0
theorem coverp000001110111011 : Covers (-238511639/250000 : ℚ) vp000001110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110111010_0 : Blocks := edgeBlocks% "full/vectors/000001110111010-V-0000.bin"
noncomputable def vp000001110111010 : Blocks := vp000001110111010_0
theorem coverp000001110111010 : Covers (-238261639/250000 : ℚ) vp000001110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111011101_0 : Blocks := edgeBlocks% "full/vectors/00000111011101-V-0000.bin"
noncomputable def vp00000111011101 : Blocks := vp00000111011101_0
private theorem bp000001110111010 : Branch 0 (-238261639/500000 : ℚ) vp00000111011101 := by
  apply branch_left_normalized (c:=vp000001110111010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-238261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-238261639/250000 : ℚ) by norm_num]
  exact coverp000001110111010
private noncomputable def ep000001110111011_0 : Blocks := edgeBlocks% "full/vectors/000001110111011-E-0000.bin"
noncomputable def ep000001110111011 : Blocks := ep000001110111011_0
private theorem idp000001110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111011101.list =
    C ((2:ℤ)^53) * horner X vp000001110111011.list + horner X ep000001110111011.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110111011 : Branch 1 (-238261639/500000 : ℚ) vp00000111011101 := by
  apply branch_checked idp000001110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-238261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-238511639/250000 : ℚ) by norm_num]
  exact coverp000001110111011
theorem coverp00000111011101 : Covers (-238261639/500000 : ℚ) vp00000111011101 := join_branches bp000001110111010 bp000001110111011
private noncomputable def vp000001110111001_0 : Blocks := edgeBlocks% "full/vectors/000001110111001-V-0000.bin"
noncomputable def vp000001110111001 : Blocks := vp000001110111001_0
theorem coverp000001110111001 : Covers (-238011639/250000 : ℚ) vp000001110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110111000_0 : Blocks := edgeBlocks% "full/vectors/000001110111000-V-0000.bin"
noncomputable def vp000001110111000 : Blocks := vp000001110111000_0
theorem coverp000001110111000 : Covers (-237761639/250000 : ℚ) vp000001110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111011100_0 : Blocks := edgeBlocks% "full/vectors/00000111011100-V-0000.bin"
noncomputable def vp00000111011100 : Blocks := vp00000111011100_0
private theorem bp000001110111000 : Branch 0 (-237761639/500000 : ℚ) vp00000111011100 := by
  apply branch_left_normalized (c:=vp000001110111000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-237761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-237761639/250000 : ℚ) by norm_num]
  exact coverp000001110111000
private noncomputable def ep000001110111001_0 : Blocks := edgeBlocks% "full/vectors/000001110111001-E-0000.bin"
noncomputable def ep000001110111001 : Blocks := ep000001110111001_0
private theorem idp000001110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111011100.list =
    C ((2:ℤ)^54) * horner X vp000001110111001.list + horner X ep000001110111001.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110111001 : Branch 1 (-237761639/500000 : ℚ) vp00000111011100 := by
  apply branch_checked idp000001110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-237761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-238011639/250000 : ℚ) by norm_num]
  exact coverp000001110111001
theorem coverp00000111011100 : Covers (-237761639/500000 : ℚ) vp00000111011100 := join_branches bp000001110111000 bp000001110111001
private noncomputable def vp0000011101110_0 : Blocks := edgeBlocks% "full/vectors/0000011101110-V-0000.bin"
noncomputable def vp0000011101110 : Blocks := vp0000011101110_0
private theorem bp00000111011100 : Branch 0 (-237761639/1000000 : ℚ) vp0000011101110 := by
  apply branch_left_normalized (c:=vp00000111011100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-237761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-237761639/500000 : ℚ) by norm_num]
  exact coverp00000111011100
private noncomputable def ep00000111011101_0 : Blocks := edgeBlocks% "full/vectors/00000111011101-E-0000.bin"
noncomputable def ep00000111011101 : Blocks := ep00000111011101_0
private theorem idp00000111011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011101110.list =
    C ((2:ℤ)^89) * horner X vp00000111011101.list + horner X ep00000111011101.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111011101 : Branch 1 (-237761639/1000000 : ℚ) vp0000011101110 := by
  apply branch_checked idp00000111011101 (by positivity) (by decide +kernel)
  rw [show 2*(-237761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-238261639/500000 : ℚ) by norm_num]
  exact coverp00000111011101
theorem coverp0000011101110 : Covers (-237761639/1000000 : ℚ) vp0000011101110 := join_branches bp00000111011100 bp00000111011101
private noncomputable def vp000001110111_0 : Blocks := edgeBlocks% "full/vectors/000001110111-V-0000.bin"
private noncomputable def vp000001110111_1 : Blocks := edgeBlocks% "full/vectors/000001110111-V-0001.bin"
noncomputable def vp000001110111 : Blocks := (Blocks.join vp000001110111_0 vp000001110111_1)
private theorem bp0000011101110 : Branch 0 (-237761639/2000000 : ℚ) vp000001110111 := by
  apply branch_left_normalized (c:=vp0000011101110) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-237761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-237761639/1000000 : ℚ) by norm_num]
  exact coverp0000011101110
private noncomputable def ep0000011101111_0 : Blocks := edgeBlocks% "full/vectors/0000011101111-E-0000.bin"
private noncomputable def ep0000011101111_1 : Blocks := edgeBlocks% "full/vectors/0000011101111-E-0001.bin"
noncomputable def ep0000011101111 : Blocks := (Blocks.join ep0000011101111_0 ep0000011101111_1)
private theorem idp0000011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001110111.list =
    C ((2:ℤ)^156) * horner X vp0000011101111.list + horner X ep0000011101111.list := by
  exact edge_identity (B := (2:ℤ)^319) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011101111 : Branch 1 (-237761639/2000000 : ℚ) vp000001110111 := by
  apply branch_checked idp0000011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-237761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-238761639/1000000 : ℚ) by norm_num]
  exact coverp0000011101111
theorem coverp000001110111 : Covers (-237761639/2000000 : ℚ) vp000001110111 := join_branches bp0000011101110 bp0000011101111
private noncomputable def vp000001110110111_0 : Blocks := edgeBlocks% "full/vectors/000001110110111-V-0000.bin"
noncomputable def vp000001110110111 : Blocks := vp000001110110111_0
theorem coverp000001110110111 : Covers (-237511639/250000 : ℚ) vp000001110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110110110_0 : Blocks := edgeBlocks% "full/vectors/000001110110110-V-0000.bin"
noncomputable def vp000001110110110 : Blocks := vp000001110110110_0
theorem coverp000001110110110 : Covers (-237261639/250000 : ℚ) vp000001110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111011011_0 : Blocks := edgeBlocks% "full/vectors/00000111011011-V-0000.bin"
noncomputable def vp00000111011011 : Blocks := vp00000111011011_0
private theorem bp000001110110110 : Branch 0 (-237261639/500000 : ℚ) vp00000111011011 := by
  apply branch_left_normalized (c:=vp000001110110110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-237261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-237261639/250000 : ℚ) by norm_num]
  exact coverp000001110110110
private noncomputable def ep000001110110111_0 : Blocks := edgeBlocks% "full/vectors/000001110110111-E-0000.bin"
noncomputable def ep000001110110111 : Blocks := ep000001110110111_0
private theorem idp000001110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111011011.list =
    C ((2:ℤ)^54) * horner X vp000001110110111.list + horner X ep000001110110111.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110110111 : Branch 1 (-237261639/500000 : ℚ) vp00000111011011 := by
  apply branch_checked idp000001110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-237261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-237511639/250000 : ℚ) by norm_num]
  exact coverp000001110110111
theorem coverp00000111011011 : Covers (-237261639/500000 : ℚ) vp00000111011011 := join_branches bp000001110110110 bp000001110110111
private noncomputable def vp000001110110101_0 : Blocks := edgeBlocks% "full/vectors/000001110110101-V-0000.bin"
noncomputable def vp000001110110101 : Blocks := vp000001110110101_0
theorem coverp000001110110101 : Covers (-237011639/250000 : ℚ) vp000001110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110110100_0 : Blocks := edgeBlocks% "full/vectors/000001110110100-V-0000.bin"
noncomputable def vp000001110110100 : Blocks := vp000001110110100_0
theorem coverp000001110110100 : Covers (-236761639/250000 : ℚ) vp000001110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111011010_0 : Blocks := edgeBlocks% "full/vectors/00000111011010-V-0000.bin"
noncomputable def vp00000111011010 : Blocks := vp00000111011010_0
private theorem bp000001110110100 : Branch 0 (-236761639/500000 : ℚ) vp00000111011010 := by
  apply branch_left_normalized (c:=vp000001110110100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-236761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-236761639/250000 : ℚ) by norm_num]
  exact coverp000001110110100
private noncomputable def ep000001110110101_0 : Blocks := edgeBlocks% "full/vectors/000001110110101-E-0000.bin"
noncomputable def ep000001110110101 : Blocks := ep000001110110101_0
private theorem idp000001110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111011010.list =
    C ((2:ℤ)^54) * horner X vp000001110110101.list + horner X ep000001110110101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110110101 : Branch 1 (-236761639/500000 : ℚ) vp00000111011010 := by
  apply branch_checked idp000001110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-236761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-237011639/250000 : ℚ) by norm_num]
  exact coverp000001110110101
theorem coverp00000111011010 : Covers (-236761639/500000 : ℚ) vp00000111011010 := join_branches bp000001110110100 bp000001110110101
private noncomputable def vp0000011101101_0 : Blocks := edgeBlocks% "full/vectors/0000011101101-V-0000.bin"
noncomputable def vp0000011101101 : Blocks := vp0000011101101_0
private theorem bp00000111011010 : Branch 0 (-236761639/1000000 : ℚ) vp0000011101101 := by
  apply branch_left_normalized (c:=vp00000111011010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-236761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-236761639/500000 : ℚ) by norm_num]
  exact coverp00000111011010
private noncomputable def ep00000111011011_0 : Blocks := edgeBlocks% "full/vectors/00000111011011-E-0000.bin"
noncomputable def ep00000111011011 : Blocks := ep00000111011011_0
private theorem idp00000111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011101101.list =
    C ((2:ℤ)^89) * horner X vp00000111011011.list + horner X ep00000111011011.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111011011 : Branch 1 (-236761639/1000000 : ℚ) vp0000011101101 := by
  apply branch_checked idp00000111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-236761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-237261639/500000 : ℚ) by norm_num]
  exact coverp00000111011011
theorem coverp0000011101101 : Covers (-236761639/1000000 : ℚ) vp0000011101101 := join_branches bp00000111011010 bp00000111011011
private noncomputable def vp000001110110011_0 : Blocks := edgeBlocks% "full/vectors/000001110110011-V-0000.bin"
noncomputable def vp000001110110011 : Blocks := vp000001110110011_0
theorem coverp000001110110011 : Covers (-236511639/250000 : ℚ) vp000001110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110110010_0 : Blocks := edgeBlocks% "full/vectors/000001110110010-V-0000.bin"
noncomputable def vp000001110110010 : Blocks := vp000001110110010_0
theorem coverp000001110110010 : Covers (-236261639/250000 : ℚ) vp000001110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111011001_0 : Blocks := edgeBlocks% "full/vectors/00000111011001-V-0000.bin"
noncomputable def vp00000111011001 : Blocks := vp00000111011001_0
private theorem bp000001110110010 : Branch 0 (-236261639/500000 : ℚ) vp00000111011001 := by
  apply branch_left_normalized (c:=vp000001110110010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-236261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-236261639/250000 : ℚ) by norm_num]
  exact coverp000001110110010
private noncomputable def ep000001110110011_0 : Blocks := edgeBlocks% "full/vectors/000001110110011-E-0000.bin"
noncomputable def ep000001110110011 : Blocks := ep000001110110011_0
private theorem idp000001110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111011001.list =
    C ((2:ℤ)^54) * horner X vp000001110110011.list + horner X ep000001110110011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110110011 : Branch 1 (-236261639/500000 : ℚ) vp00000111011001 := by
  apply branch_checked idp000001110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-236261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-236511639/250000 : ℚ) by norm_num]
  exact coverp000001110110011
theorem coverp00000111011001 : Covers (-236261639/500000 : ℚ) vp00000111011001 := join_branches bp000001110110010 bp000001110110011
private noncomputable def vp000001110110001_0 : Blocks := edgeBlocks% "full/vectors/000001110110001-V-0000.bin"
noncomputable def vp000001110110001 : Blocks := vp000001110110001_0
theorem coverp000001110110001 : Covers (-236011639/250000 : ℚ) vp000001110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110110000_0 : Blocks := edgeBlocks% "full/vectors/000001110110000-V-0000.bin"
noncomputable def vp000001110110000 : Blocks := vp000001110110000_0
theorem coverp000001110110000 : Covers (-235761639/250000 : ℚ) vp000001110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111011000_0 : Blocks := edgeBlocks% "full/vectors/00000111011000-V-0000.bin"
noncomputable def vp00000111011000 : Blocks := vp00000111011000_0
private theorem bp000001110110000 : Branch 0 (-235761639/500000 : ℚ) vp00000111011000 := by
  apply branch_left_normalized (c:=vp000001110110000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-235761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-235761639/250000 : ℚ) by norm_num]
  exact coverp000001110110000
private noncomputable def ep000001110110001_0 : Blocks := edgeBlocks% "full/vectors/000001110110001-E-0000.bin"
noncomputable def ep000001110110001 : Blocks := ep000001110110001_0
private theorem idp000001110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111011000.list =
    C ((2:ℤ)^53) * horner X vp000001110110001.list + horner X ep000001110110001.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110110001 : Branch 1 (-235761639/500000 : ℚ) vp00000111011000 := by
  apply branch_checked idp000001110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-235761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-236011639/250000 : ℚ) by norm_num]
  exact coverp000001110110001
theorem coverp00000111011000 : Covers (-235761639/500000 : ℚ) vp00000111011000 := join_branches bp000001110110000 bp000001110110001
private noncomputable def vp0000011101100_0 : Blocks := edgeBlocks% "full/vectors/0000011101100-V-0000.bin"
noncomputable def vp0000011101100 : Blocks := vp0000011101100_0
private theorem bp00000111011000 : Branch 0 (-235761639/1000000 : ℚ) vp0000011101100 := by
  apply branch_left_normalized (c:=vp00000111011000) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-235761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-235761639/500000 : ℚ) by norm_num]
  exact coverp00000111011000
private noncomputable def ep00000111011001_0 : Blocks := edgeBlocks% "full/vectors/00000111011001-E-0000.bin"
noncomputable def ep00000111011001 : Blocks := ep00000111011001_0
private theorem idp00000111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011101100.list =
    C ((2:ℤ)^89) * horner X vp00000111011001.list + horner X ep00000111011001.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111011001 : Branch 1 (-235761639/1000000 : ℚ) vp0000011101100 := by
  apply branch_checked idp00000111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-235761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-236261639/500000 : ℚ) by norm_num]
  exact coverp00000111011001
theorem coverp0000011101100 : Covers (-235761639/1000000 : ℚ) vp0000011101100 := join_branches bp00000111011000 bp00000111011001
private noncomputable def vp000001110110_0 : Blocks := edgeBlocks% "full/vectors/000001110110-V-0000.bin"
private noncomputable def vp000001110110_1 : Blocks := edgeBlocks% "full/vectors/000001110110-V-0001.bin"
noncomputable def vp000001110110 : Blocks := (Blocks.join vp000001110110_0 vp000001110110_1)
private theorem bp0000011101100 : Branch 0 (-235761639/2000000 : ℚ) vp000001110110 := by
  apply branch_left_normalized (c:=vp0000011101100) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-235761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-235761639/1000000 : ℚ) by norm_num]
  exact coverp0000011101100
private noncomputable def ep0000011101101_0 : Blocks := edgeBlocks% "full/vectors/0000011101101-E-0000.bin"
private noncomputable def ep0000011101101_1 : Blocks := edgeBlocks% "full/vectors/0000011101101-E-0001.bin"
noncomputable def ep0000011101101 : Blocks := (Blocks.join ep0000011101101_0 ep0000011101101_1)
private theorem idp0000011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001110110.list =
    C ((2:ℤ)^157) * horner X vp0000011101101.list + horner X ep0000011101101.list := by
  exact edge_identity (B := (2:ℤ)^321) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011101101 : Branch 1 (-235761639/2000000 : ℚ) vp000001110110 := by
  apply branch_checked idp0000011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-235761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-236761639/1000000 : ℚ) by norm_num]
  exact coverp0000011101101
theorem coverp000001110110 : Covers (-235761639/2000000 : ℚ) vp000001110110 := join_branches bp0000011101100 bp0000011101101
private noncomputable def vp00000111011_0 : Blocks := edgeBlocks% "full/vectors/00000111011-V-0000.bin"
private noncomputable def vp00000111011_1 : Blocks := edgeBlocks% "full/vectors/00000111011-V-0001.bin"
private noncomputable def vp00000111011_2 : Blocks := edgeBlocks% "full/vectors/00000111011-V-0002.bin"
noncomputable def vp00000111011 : Blocks := (Blocks.join vp00000111011_0 (Blocks.join vp00000111011_1 vp00000111011_2))
private theorem bp000001110110 : Branch 0 (-235761639/4000000 : ℚ) vp00000111011 := by
  apply branch_left_normalized (c:=vp000001110110) (k:=0) (m:=150) (by decide +kernel)
  rw [show 2*(-235761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-235761639/2000000 : ℚ) by norm_num]
  exact coverp000001110110
private noncomputable def ep000001110111_0 : Blocks := edgeBlocks% "full/vectors/000001110111-E-0000.bin"
private noncomputable def ep000001110111_1 : Blocks := edgeBlocks% "full/vectors/000001110111-E-0001.bin"
private noncomputable def ep000001110111_2 : Blocks := edgeBlocks% "full/vectors/000001110111-E-0002.bin"
noncomputable def ep000001110111 : Blocks := (Blocks.join ep000001110111_0 (Blocks.join ep000001110111_1 ep000001110111_2))
private theorem idp000001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111011.list =
    C ((2:ℤ)^291) * horner X vp000001110111.list + horner X ep000001110111.list := by
  exact edge_identity (B := (2:ℤ)^517) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110111 : Branch 1 (-235761639/4000000 : ℚ) vp00000111011 := by
  apply branch_checked idp000001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-235761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-237761639/2000000 : ℚ) by norm_num]
  exact coverp000001110111
theorem coverp00000111011 : Covers (-235761639/4000000 : ℚ) vp00000111011 := join_branches bp000001110110 bp000001110111
private noncomputable def vp000001110101111_0 : Blocks := edgeBlocks% "full/vectors/000001110101111-V-0000.bin"
noncomputable def vp000001110101111 : Blocks := vp000001110101111_0
theorem coverp000001110101111 : Covers (-235511639/250000 : ℚ) vp000001110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110101110_0 : Blocks := edgeBlocks% "full/vectors/000001110101110-V-0000.bin"
noncomputable def vp000001110101110 : Blocks := vp000001110101110_0
theorem coverp000001110101110 : Covers (-235261639/250000 : ℚ) vp000001110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111010111_0 : Blocks := edgeBlocks% "full/vectors/00000111010111-V-0000.bin"
noncomputable def vp00000111010111 : Blocks := vp00000111010111_0
private theorem bp000001110101110 : Branch 0 (-235261639/500000 : ℚ) vp00000111010111 := by
  apply branch_left_normalized (c:=vp000001110101110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-235261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-235261639/250000 : ℚ) by norm_num]
  exact coverp000001110101110
private noncomputable def ep000001110101111_0 : Blocks := edgeBlocks% "full/vectors/000001110101111-E-0000.bin"
noncomputable def ep000001110101111 : Blocks := ep000001110101111_0
private theorem idp000001110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111010111.list =
    C ((2:ℤ)^53) * horner X vp000001110101111.list + horner X ep000001110101111.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110101111 : Branch 1 (-235261639/500000 : ℚ) vp00000111010111 := by
  apply branch_checked idp000001110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-235261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-235511639/250000 : ℚ) by norm_num]
  exact coverp000001110101111
theorem coverp00000111010111 : Covers (-235261639/500000 : ℚ) vp00000111010111 := join_branches bp000001110101110 bp000001110101111
private noncomputable def vp000001110101101_0 : Blocks := edgeBlocks% "full/vectors/000001110101101-V-0000.bin"
noncomputable def vp000001110101101 : Blocks := vp000001110101101_0
theorem coverp000001110101101 : Covers (-235011639/250000 : ℚ) vp000001110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110101100_0 : Blocks := edgeBlocks% "full/vectors/000001110101100-V-0000.bin"
noncomputable def vp000001110101100 : Blocks := vp000001110101100_0
theorem coverp000001110101100 : Covers (-234761639/250000 : ℚ) vp000001110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111010110_0 : Blocks := edgeBlocks% "full/vectors/00000111010110-V-0000.bin"
noncomputable def vp00000111010110 : Blocks := vp00000111010110_0
private theorem bp000001110101100 : Branch 0 (-234761639/500000 : ℚ) vp00000111010110 := by
  apply branch_left_normalized (c:=vp000001110101100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-234761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-234761639/250000 : ℚ) by norm_num]
  exact coverp000001110101100
private noncomputable def ep000001110101101_0 : Blocks := edgeBlocks% "full/vectors/000001110101101-E-0000.bin"
noncomputable def ep000001110101101 : Blocks := ep000001110101101_0
private theorem idp000001110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111010110.list =
    C ((2:ℤ)^54) * horner X vp000001110101101.list + horner X ep000001110101101.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110101101 : Branch 1 (-234761639/500000 : ℚ) vp00000111010110 := by
  apply branch_checked idp000001110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-234761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-235011639/250000 : ℚ) by norm_num]
  exact coverp000001110101101
theorem coverp00000111010110 : Covers (-234761639/500000 : ℚ) vp00000111010110 := join_branches bp000001110101100 bp000001110101101
private noncomputable def vp0000011101011_0 : Blocks := edgeBlocks% "full/vectors/0000011101011-V-0000.bin"
noncomputable def vp0000011101011 : Blocks := vp0000011101011_0
private theorem bp00000111010110 : Branch 0 (-234761639/1000000 : ℚ) vp0000011101011 := by
  apply branch_left_normalized (c:=vp00000111010110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-234761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-234761639/500000 : ℚ) by norm_num]
  exact coverp00000111010110
private noncomputable def ep00000111010111_0 : Blocks := edgeBlocks% "full/vectors/00000111010111-E-0000.bin"
noncomputable def ep00000111010111 : Blocks := ep00000111010111_0
private theorem idp00000111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011101011.list =
    C ((2:ℤ)^89) * horner X vp00000111010111.list + horner X ep00000111010111.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111010111 : Branch 1 (-234761639/1000000 : ℚ) vp0000011101011 := by
  apply branch_checked idp00000111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-234761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-235261639/500000 : ℚ) by norm_num]
  exact coverp00000111010111
theorem coverp0000011101011 : Covers (-234761639/1000000 : ℚ) vp0000011101011 := join_branches bp00000111010110 bp00000111010111
private noncomputable def vp000001110101011_0 : Blocks := edgeBlocks% "full/vectors/000001110101011-V-0000.bin"
noncomputable def vp000001110101011 : Blocks := vp000001110101011_0
theorem coverp000001110101011 : Covers (-234511639/250000 : ℚ) vp000001110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110101010_0 : Blocks := edgeBlocks% "full/vectors/000001110101010-V-0000.bin"
noncomputable def vp000001110101010 : Blocks := vp000001110101010_0
theorem coverp000001110101010 : Covers (-234261639/250000 : ℚ) vp000001110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111010101_0 : Blocks := edgeBlocks% "full/vectors/00000111010101-V-0000.bin"
noncomputable def vp00000111010101 : Blocks := vp00000111010101_0
private theorem bp000001110101010 : Branch 0 (-234261639/500000 : ℚ) vp00000111010101 := by
  apply branch_left_normalized (c:=vp000001110101010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-234261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-234261639/250000 : ℚ) by norm_num]
  exact coverp000001110101010
private noncomputable def ep000001110101011_0 : Blocks := edgeBlocks% "full/vectors/000001110101011-E-0000.bin"
noncomputable def ep000001110101011 : Blocks := ep000001110101011_0
private theorem idp000001110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111010101.list =
    C ((2:ℤ)^53) * horner X vp000001110101011.list + horner X ep000001110101011.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110101011 : Branch 1 (-234261639/500000 : ℚ) vp00000111010101 := by
  apply branch_checked idp000001110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-234261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-234511639/250000 : ℚ) by norm_num]
  exact coverp000001110101011
theorem coverp00000111010101 : Covers (-234261639/500000 : ℚ) vp00000111010101 := join_branches bp000001110101010 bp000001110101011
private noncomputable def vp000001110101001_0 : Blocks := edgeBlocks% "full/vectors/000001110101001-V-0000.bin"
noncomputable def vp000001110101001 : Blocks := vp000001110101001_0
theorem coverp000001110101001 : Covers (-234011639/250000 : ℚ) vp000001110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110101000_0 : Blocks := edgeBlocks% "full/vectors/000001110101000-V-0000.bin"
noncomputable def vp000001110101000 : Blocks := vp000001110101000_0
theorem coverp000001110101000 : Covers (-233761639/250000 : ℚ) vp000001110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111010100_0 : Blocks := edgeBlocks% "full/vectors/00000111010100-V-0000.bin"
noncomputable def vp00000111010100 : Blocks := vp00000111010100_0
private theorem bp000001110101000 : Branch 0 (-233761639/500000 : ℚ) vp00000111010100 := by
  apply branch_left_normalized (c:=vp000001110101000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-233761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-233761639/250000 : ℚ) by norm_num]
  exact coverp000001110101000
private noncomputable def ep000001110101001_0 : Blocks := edgeBlocks% "full/vectors/000001110101001-E-0000.bin"
noncomputable def ep000001110101001 : Blocks := ep000001110101001_0
private theorem idp000001110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111010100.list =
    C ((2:ℤ)^53) * horner X vp000001110101001.list + horner X ep000001110101001.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110101001 : Branch 1 (-233761639/500000 : ℚ) vp00000111010100 := by
  apply branch_checked idp000001110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-233761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-234011639/250000 : ℚ) by norm_num]
  exact coverp000001110101001
theorem coverp00000111010100 : Covers (-233761639/500000 : ℚ) vp00000111010100 := join_branches bp000001110101000 bp000001110101001
private noncomputable def vp0000011101010_0 : Blocks := edgeBlocks% "full/vectors/0000011101010-V-0000.bin"
noncomputable def vp0000011101010 : Blocks := vp0000011101010_0
private theorem bp00000111010100 : Branch 0 (-233761639/1000000 : ℚ) vp0000011101010 := by
  apply branch_left_normalized (c:=vp00000111010100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-233761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-233761639/500000 : ℚ) by norm_num]
  exact coverp00000111010100
private noncomputable def ep00000111010101_0 : Blocks := edgeBlocks% "full/vectors/00000111010101-E-0000.bin"
noncomputable def ep00000111010101 : Blocks := ep00000111010101_0
private theorem idp00000111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011101010.list =
    C ((2:ℤ)^88) * horner X vp00000111010101.list + horner X ep00000111010101.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111010101 : Branch 1 (-233761639/1000000 : ℚ) vp0000011101010 := by
  apply branch_checked idp00000111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-233761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-234261639/500000 : ℚ) by norm_num]
  exact coverp00000111010101
theorem coverp0000011101010 : Covers (-233761639/1000000 : ℚ) vp0000011101010 := join_branches bp00000111010100 bp00000111010101
private noncomputable def vp000001110101_0 : Blocks := edgeBlocks% "full/vectors/000001110101-V-0000.bin"
private noncomputable def vp000001110101_1 : Blocks := edgeBlocks% "full/vectors/000001110101-V-0001.bin"
noncomputable def vp000001110101 : Blocks := (Blocks.join vp000001110101_0 vp000001110101_1)
private theorem bp0000011101010 : Branch 0 (-233761639/2000000 : ℚ) vp000001110101 := by
  apply branch_left_normalized (c:=vp0000011101010) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-233761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-233761639/1000000 : ℚ) by norm_num]
  exact coverp0000011101010
private noncomputable def ep0000011101011_0 : Blocks := edgeBlocks% "full/vectors/0000011101011-E-0000.bin"
private noncomputable def ep0000011101011_1 : Blocks := edgeBlocks% "full/vectors/0000011101011-E-0001.bin"
noncomputable def ep0000011101011 : Blocks := (Blocks.join ep0000011101011_0 ep0000011101011_1)
private theorem idp0000011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001110101.list =
    C ((2:ℤ)^156) * horner X vp0000011101011.list + horner X ep0000011101011.list := by
  exact edge_identity (B := (2:ℤ)^320) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011101011 : Branch 1 (-233761639/2000000 : ℚ) vp000001110101 := by
  apply branch_checked idp0000011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-233761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-234761639/1000000 : ℚ) by norm_num]
  exact coverp0000011101011
theorem coverp000001110101 : Covers (-233761639/2000000 : ℚ) vp000001110101 := join_branches bp0000011101010 bp0000011101011
private noncomputable def vp000001110100111_0 : Blocks := edgeBlocks% "full/vectors/000001110100111-V-0000.bin"
noncomputable def vp000001110100111 : Blocks := vp000001110100111_0
theorem coverp000001110100111 : Covers (-233511639/250000 : ℚ) vp000001110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110100110_0 : Blocks := edgeBlocks% "full/vectors/000001110100110-V-0000.bin"
noncomputable def vp000001110100110 : Blocks := vp000001110100110_0
theorem coverp000001110100110 : Covers (-233261639/250000 : ℚ) vp000001110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111010011_0 : Blocks := edgeBlocks% "full/vectors/00000111010011-V-0000.bin"
noncomputable def vp00000111010011 : Blocks := vp00000111010011_0
private theorem bp000001110100110 : Branch 0 (-233261639/500000 : ℚ) vp00000111010011 := by
  apply branch_left_normalized (c:=vp000001110100110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-233261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-233261639/250000 : ℚ) by norm_num]
  exact coverp000001110100110
private noncomputable def ep000001110100111_0 : Blocks := edgeBlocks% "full/vectors/000001110100111-E-0000.bin"
noncomputable def ep000001110100111 : Blocks := ep000001110100111_0
private theorem idp000001110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111010011.list =
    C ((2:ℤ)^53) * horner X vp000001110100111.list + horner X ep000001110100111.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110100111 : Branch 1 (-233261639/500000 : ℚ) vp00000111010011 := by
  apply branch_checked idp000001110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-233261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-233511639/250000 : ℚ) by norm_num]
  exact coverp000001110100111
theorem coverp00000111010011 : Covers (-233261639/500000 : ℚ) vp00000111010011 := join_branches bp000001110100110 bp000001110100111
private noncomputable def vp000001110100101_0 : Blocks := edgeBlocks% "full/vectors/000001110100101-V-0000.bin"
noncomputable def vp000001110100101 : Blocks := vp000001110100101_0
theorem coverp000001110100101 : Covers (-233011639/250000 : ℚ) vp000001110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110100100_0 : Blocks := edgeBlocks% "full/vectors/000001110100100-V-0000.bin"
noncomputable def vp000001110100100 : Blocks := vp000001110100100_0
theorem coverp000001110100100 : Covers (-232761639/250000 : ℚ) vp000001110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111010010_0 : Blocks := edgeBlocks% "full/vectors/00000111010010-V-0000.bin"
noncomputable def vp00000111010010 : Blocks := vp00000111010010_0
private theorem bp000001110100100 : Branch 0 (-232761639/500000 : ℚ) vp00000111010010 := by
  apply branch_left_normalized (c:=vp000001110100100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-232761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-232761639/250000 : ℚ) by norm_num]
  exact coverp000001110100100
private noncomputable def ep000001110100101_0 : Blocks := edgeBlocks% "full/vectors/000001110100101-E-0000.bin"
noncomputable def ep000001110100101 : Blocks := ep000001110100101_0
private theorem idp000001110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111010010.list =
    C ((2:ℤ)^55) * horner X vp000001110100101.list + horner X ep000001110100101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110100101 : Branch 1 (-232761639/500000 : ℚ) vp00000111010010 := by
  apply branch_checked idp000001110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-232761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-233011639/250000 : ℚ) by norm_num]
  exact coverp000001110100101
theorem coverp00000111010010 : Covers (-232761639/500000 : ℚ) vp00000111010010 := join_branches bp000001110100100 bp000001110100101
private noncomputable def vp0000011101001_0 : Blocks := edgeBlocks% "full/vectors/0000011101001-V-0000.bin"
noncomputable def vp0000011101001 : Blocks := vp0000011101001_0
private theorem bp00000111010010 : Branch 0 (-232761639/1000000 : ℚ) vp0000011101001 := by
  apply branch_left_normalized (c:=vp00000111010010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-232761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-232761639/500000 : ℚ) by norm_num]
  exact coverp00000111010010
private noncomputable def ep00000111010011_0 : Blocks := edgeBlocks% "full/vectors/00000111010011-E-0000.bin"
noncomputable def ep00000111010011 : Blocks := ep00000111010011_0
private theorem idp00000111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011101001.list =
    C ((2:ℤ)^90) * horner X vp00000111010011.list + horner X ep00000111010011.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111010011 : Branch 1 (-232761639/1000000 : ℚ) vp0000011101001 := by
  apply branch_checked idp00000111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-232761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-233261639/500000 : ℚ) by norm_num]
  exact coverp00000111010011
theorem coverp0000011101001 : Covers (-232761639/1000000 : ℚ) vp0000011101001 := join_branches bp00000111010010 bp00000111010011
private noncomputable def vp000001110100011_0 : Blocks := edgeBlocks% "full/vectors/000001110100011-V-0000.bin"
noncomputable def vp000001110100011 : Blocks := vp000001110100011_0
theorem coverp000001110100011 : Covers (-232511639/250000 : ℚ) vp000001110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110100010_0 : Blocks := edgeBlocks% "full/vectors/000001110100010-V-0000.bin"
noncomputable def vp000001110100010 : Blocks := vp000001110100010_0
theorem coverp000001110100010 : Covers (-232261639/250000 : ℚ) vp000001110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111010001_0 : Blocks := edgeBlocks% "full/vectors/00000111010001-V-0000.bin"
noncomputable def vp00000111010001 : Blocks := vp00000111010001_0
private theorem bp000001110100010 : Branch 0 (-232261639/500000 : ℚ) vp00000111010001 := by
  apply branch_left_normalized (c:=vp000001110100010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-232261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-232261639/250000 : ℚ) by norm_num]
  exact coverp000001110100010
private noncomputable def ep000001110100011_0 : Blocks := edgeBlocks% "full/vectors/000001110100011-E-0000.bin"
noncomputable def ep000001110100011 : Blocks := ep000001110100011_0
private theorem idp000001110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111010001.list =
    C ((2:ℤ)^54) * horner X vp000001110100011.list + horner X ep000001110100011.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110100011 : Branch 1 (-232261639/500000 : ℚ) vp00000111010001 := by
  apply branch_checked idp000001110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-232261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-232511639/250000 : ℚ) by norm_num]
  exact coverp000001110100011
theorem coverp00000111010001 : Covers (-232261639/500000 : ℚ) vp00000111010001 := join_branches bp000001110100010 bp000001110100011
private noncomputable def vp000001110100001_0 : Blocks := edgeBlocks% "full/vectors/000001110100001-V-0000.bin"
noncomputable def vp000001110100001 : Blocks := vp000001110100001_0
theorem coverp000001110100001 : Covers (-232011639/250000 : ℚ) vp000001110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110100000_0 : Blocks := edgeBlocks% "full/vectors/000001110100000-V-0000.bin"
noncomputable def vp000001110100000 : Blocks := vp000001110100000_0
theorem coverp000001110100000 : Covers (-231761639/250000 : ℚ) vp000001110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111010000_0 : Blocks := edgeBlocks% "full/vectors/00000111010000-V-0000.bin"
noncomputable def vp00000111010000 : Blocks := vp00000111010000_0
private theorem bp000001110100000 : Branch 0 (-231761639/500000 : ℚ) vp00000111010000 := by
  apply branch_left_normalized (c:=vp000001110100000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-231761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-231761639/250000 : ℚ) by norm_num]
  exact coverp000001110100000
private noncomputable def ep000001110100001_0 : Blocks := edgeBlocks% "full/vectors/000001110100001-E-0000.bin"
noncomputable def ep000001110100001 : Blocks := ep000001110100001_0
private theorem idp000001110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111010000.list =
    C ((2:ℤ)^54) * horner X vp000001110100001.list + horner X ep000001110100001.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110100001 : Branch 1 (-231761639/500000 : ℚ) vp00000111010000 := by
  apply branch_checked idp000001110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-231761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-232011639/250000 : ℚ) by norm_num]
  exact coverp000001110100001
theorem coverp00000111010000 : Covers (-231761639/500000 : ℚ) vp00000111010000 := join_branches bp000001110100000 bp000001110100001
private noncomputable def vp0000011101000_0 : Blocks := edgeBlocks% "full/vectors/0000011101000-V-0000.bin"
noncomputable def vp0000011101000 : Blocks := vp0000011101000_0
private theorem bp00000111010000 : Branch 0 (-231761639/1000000 : ℚ) vp0000011101000 := by
  apply branch_left_normalized (c:=vp00000111010000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-231761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-231761639/500000 : ℚ) by norm_num]
  exact coverp00000111010000
private noncomputable def ep00000111010001_0 : Blocks := edgeBlocks% "full/vectors/00000111010001-E-0000.bin"
noncomputable def ep00000111010001 : Blocks := ep00000111010001_0
private theorem idp00000111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011101000.list =
    C ((2:ℤ)^90) * horner X vp00000111010001.list + horner X ep00000111010001.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111010001 : Branch 1 (-231761639/1000000 : ℚ) vp0000011101000 := by
  apply branch_checked idp00000111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-231761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-232261639/500000 : ℚ) by norm_num]
  exact coverp00000111010001
theorem coverp0000011101000 : Covers (-231761639/1000000 : ℚ) vp0000011101000 := join_branches bp00000111010000 bp00000111010001
private noncomputable def vp000001110100_0 : Blocks := edgeBlocks% "full/vectors/000001110100-V-0000.bin"
private noncomputable def vp000001110100_1 : Blocks := edgeBlocks% "full/vectors/000001110100-V-0001.bin"
noncomputable def vp000001110100 : Blocks := (Blocks.join vp000001110100_0 vp000001110100_1)
private theorem bp0000011101000 : Branch 0 (-231761639/2000000 : ℚ) vp000001110100 := by
  apply branch_left_normalized (c:=vp0000011101000) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-231761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-231761639/1000000 : ℚ) by norm_num]
  exact coverp0000011101000
private noncomputable def ep0000011101001_0 : Blocks := edgeBlocks% "full/vectors/0000011101001-E-0000.bin"
private noncomputable def ep0000011101001_1 : Blocks := edgeBlocks% "full/vectors/0000011101001-E-0001.bin"
noncomputable def ep0000011101001 : Blocks := (Blocks.join ep0000011101001_0 ep0000011101001_1)
private theorem idp0000011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001110100.list =
    C ((2:ℤ)^159) * horner X vp0000011101001.list + horner X ep0000011101001.list := by
  exact edge_identity (B := (2:ℤ)^324) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011101001 : Branch 1 (-231761639/2000000 : ℚ) vp000001110100 := by
  apply branch_checked idp0000011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-231761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-232761639/1000000 : ℚ) by norm_num]
  exact coverp0000011101001
theorem coverp000001110100 : Covers (-231761639/2000000 : ℚ) vp000001110100 := join_branches bp0000011101000 bp0000011101001
private noncomputable def vp00000111010_0 : Blocks := edgeBlocks% "full/vectors/00000111010-V-0000.bin"
private noncomputable def vp00000111010_1 : Blocks := edgeBlocks% "full/vectors/00000111010-V-0001.bin"
private noncomputable def vp00000111010_2 : Blocks := edgeBlocks% "full/vectors/00000111010-V-0002.bin"
noncomputable def vp00000111010 : Blocks := (Blocks.join vp00000111010_0 (Blocks.join vp00000111010_1 vp00000111010_2))
private theorem bp000001110100 : Branch 0 (-231761639/4000000 : ℚ) vp00000111010 := by
  apply branch_left_normalized (c:=vp000001110100) (k:=0) (m:=152) (by decide +kernel)
  rw [show 2*(-231761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-231761639/2000000 : ℚ) by norm_num]
  exact coverp000001110100
private noncomputable def ep000001110101_0 : Blocks := edgeBlocks% "full/vectors/000001110101-E-0000.bin"
private noncomputable def ep000001110101_1 : Blocks := edgeBlocks% "full/vectors/000001110101-E-0001.bin"
private noncomputable def ep000001110101_2 : Blocks := edgeBlocks% "full/vectors/000001110101-E-0002.bin"
noncomputable def ep000001110101 : Blocks := (Blocks.join ep000001110101_0 (Blocks.join ep000001110101_1 ep000001110101_2))
private theorem idp000001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111010.list =
    C ((2:ℤ)^295) * horner X vp000001110101.list + horner X ep000001110101.list := by
  exact edge_identity (B := (2:ℤ)^521) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110101 : Branch 1 (-231761639/4000000 : ℚ) vp00000111010 := by
  apply branch_checked idp000001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-231761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-233761639/2000000 : ℚ) by norm_num]
  exact coverp000001110101
theorem coverp00000111010 : Covers (-231761639/4000000 : ℚ) vp00000111010 := join_branches bp000001110100 bp000001110101
private noncomputable def vp0000011101_0 : Blocks := edgeBlocks% "full/vectors/0000011101-V-0000.bin"
private noncomputable def vp0000011101_1 : Blocks := edgeBlocks% "full/vectors/0000011101-V-0001.bin"
private noncomputable def vp0000011101_2 : Blocks := edgeBlocks% "full/vectors/0000011101-V-0002.bin"
private noncomputable def vp0000011101_3 : Blocks := edgeBlocks% "full/vectors/0000011101-V-0003.bin"
private noncomputable def vp0000011101_4 : Blocks := edgeBlocks% "full/vectors/0000011101-V-0004.bin"
noncomputable def vp0000011101 : Blocks := (Blocks.join (Blocks.join vp0000011101_0 vp0000011101_1) (Blocks.join vp0000011101_2 (Blocks.join vp0000011101_3 vp0000011101_4)))
private theorem bp00000111010 : Branch 0 (-231761639/8000000 : ℚ) vp0000011101 := by
  apply branch_left_normalized (c:=vp00000111010) (k:=0) (m:=281) (by decide +kernel)
  rw [show 2*(-231761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-231761639/4000000 : ℚ) by norm_num]
  exact coverp00000111010
private noncomputable def ep00000111011_0 : Blocks := edgeBlocks% "full/vectors/00000111011-E-0000.bin"
private noncomputable def ep00000111011_1 : Blocks := edgeBlocks% "full/vectors/00000111011-E-0001.bin"
private noncomputable def ep00000111011_2 : Blocks := edgeBlocks% "full/vectors/00000111011-E-0002.bin"
private noncomputable def ep00000111011_3 : Blocks := edgeBlocks% "full/vectors/00000111011-E-0003.bin"
private noncomputable def ep00000111011_4 : Blocks := edgeBlocks% "full/vectors/00000111011-E-0004.bin"
noncomputable def ep00000111011 : Blocks := (Blocks.join (Blocks.join ep00000111011_0 ep00000111011_1) (Blocks.join ep00000111011_2 (Blocks.join ep00000111011_3 ep00000111011_4)))
private theorem idp00000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011101.list =
    C ((2:ℤ)^560) * horner X vp00000111011.list + horner X ep00000111011.list := by
  exact edge_identity (B := (2:ℤ)^913) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111011 : Branch 1 (-231761639/8000000 : ℚ) vp0000011101 := by
  apply branch_checked idp00000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-231761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-235761639/4000000 : ℚ) by norm_num]
  exact coverp00000111011
theorem coverp0000011101 : Covers (-231761639/8000000 : ℚ) vp0000011101 := join_branches bp00000111010 bp00000111011
private noncomputable def vp000001110011111_0 : Blocks := edgeBlocks% "full/vectors/000001110011111-V-0000.bin"
noncomputable def vp000001110011111 : Blocks := vp000001110011111_0
theorem coverp000001110011111 : Covers (-231511639/250000 : ℚ) vp000001110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110011110_0 : Blocks := edgeBlocks% "full/vectors/000001110011110-V-0000.bin"
noncomputable def vp000001110011110 : Blocks := vp000001110011110_0
theorem coverp000001110011110 : Covers (-231261639/250000 : ℚ) vp000001110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111001111_0 : Blocks := edgeBlocks% "full/vectors/00000111001111-V-0000.bin"
noncomputable def vp00000111001111 : Blocks := vp00000111001111_0
private theorem bp000001110011110 : Branch 0 (-231261639/500000 : ℚ) vp00000111001111 := by
  apply branch_left_normalized (c:=vp000001110011110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-231261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-231261639/250000 : ℚ) by norm_num]
  exact coverp000001110011110
private noncomputable def ep000001110011111_0 : Blocks := edgeBlocks% "full/vectors/000001110011111-E-0000.bin"
noncomputable def ep000001110011111 : Blocks := ep000001110011111_0
private theorem idp000001110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111001111.list =
    C ((2:ℤ)^54) * horner X vp000001110011111.list + horner X ep000001110011111.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110011111 : Branch 1 (-231261639/500000 : ℚ) vp00000111001111 := by
  apply branch_checked idp000001110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-231261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-231511639/250000 : ℚ) by norm_num]
  exact coverp000001110011111
theorem coverp00000111001111 : Covers (-231261639/500000 : ℚ) vp00000111001111 := join_branches bp000001110011110 bp000001110011111
private noncomputable def vp000001110011101_0 : Blocks := edgeBlocks% "full/vectors/000001110011101-V-0000.bin"
noncomputable def vp000001110011101 : Blocks := vp000001110011101_0
theorem coverp000001110011101 : Covers (-231011639/250000 : ℚ) vp000001110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110011100_0 : Blocks := edgeBlocks% "full/vectors/000001110011100-V-0000.bin"
noncomputable def vp000001110011100 : Blocks := vp000001110011100_0
theorem coverp000001110011100 : Covers (-230761639/250000 : ℚ) vp000001110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111001110_0 : Blocks := edgeBlocks% "full/vectors/00000111001110-V-0000.bin"
noncomputable def vp00000111001110 : Blocks := vp00000111001110_0
private theorem bp000001110011100 : Branch 0 (-230761639/500000 : ℚ) vp00000111001110 := by
  apply branch_left_normalized (c:=vp000001110011100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-230761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-230761639/250000 : ℚ) by norm_num]
  exact coverp000001110011100
private noncomputable def ep000001110011101_0 : Blocks := edgeBlocks% "full/vectors/000001110011101-E-0000.bin"
noncomputable def ep000001110011101 : Blocks := ep000001110011101_0
private theorem idp000001110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111001110.list =
    C ((2:ℤ)^53) * horner X vp000001110011101.list + horner X ep000001110011101.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110011101 : Branch 1 (-230761639/500000 : ℚ) vp00000111001110 := by
  apply branch_checked idp000001110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-230761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-231011639/250000 : ℚ) by norm_num]
  exact coverp000001110011101
theorem coverp00000111001110 : Covers (-230761639/500000 : ℚ) vp00000111001110 := join_branches bp000001110011100 bp000001110011101
private noncomputable def vp0000011100111_0 : Blocks := edgeBlocks% "full/vectors/0000011100111-V-0000.bin"
noncomputable def vp0000011100111 : Blocks := vp0000011100111_0
private theorem bp00000111001110 : Branch 0 (-230761639/1000000 : ℚ) vp0000011100111 := by
  apply branch_left_normalized (c:=vp00000111001110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-230761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-230761639/500000 : ℚ) by norm_num]
  exact coverp00000111001110
private noncomputable def ep00000111001111_0 : Blocks := edgeBlocks% "full/vectors/00000111001111-E-0000.bin"
noncomputable def ep00000111001111 : Blocks := ep00000111001111_0
private theorem idp00000111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011100111.list =
    C ((2:ℤ)^88) * horner X vp00000111001111.list + horner X ep00000111001111.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111001111 : Branch 1 (-230761639/1000000 : ℚ) vp0000011100111 := by
  apply branch_checked idp00000111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-230761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-231261639/500000 : ℚ) by norm_num]
  exact coverp00000111001111
theorem coverp0000011100111 : Covers (-230761639/1000000 : ℚ) vp0000011100111 := join_branches bp00000111001110 bp00000111001111
private noncomputable def vp000001110011011_0 : Blocks := edgeBlocks% "full/vectors/000001110011011-V-0000.bin"
noncomputable def vp000001110011011 : Blocks := vp000001110011011_0
theorem coverp000001110011011 : Covers (-230511639/250000 : ℚ) vp000001110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110011010_0 : Blocks := edgeBlocks% "full/vectors/000001110011010-V-0000.bin"
noncomputable def vp000001110011010 : Blocks := vp000001110011010_0
theorem coverp000001110011010 : Covers (-230261639/250000 : ℚ) vp000001110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111001101_0 : Blocks := edgeBlocks% "full/vectors/00000111001101-V-0000.bin"
noncomputable def vp00000111001101 : Blocks := vp00000111001101_0
private theorem bp000001110011010 : Branch 0 (-230261639/500000 : ℚ) vp00000111001101 := by
  apply branch_left_normalized (c:=vp000001110011010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-230261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-230261639/250000 : ℚ) by norm_num]
  exact coverp000001110011010
private noncomputable def ep000001110011011_0 : Blocks := edgeBlocks% "full/vectors/000001110011011-E-0000.bin"
noncomputable def ep000001110011011 : Blocks := ep000001110011011_0
private theorem idp000001110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111001101.list =
    C ((2:ℤ)^54) * horner X vp000001110011011.list + horner X ep000001110011011.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110011011 : Branch 1 (-230261639/500000 : ℚ) vp00000111001101 := by
  apply branch_checked idp000001110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-230261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-230511639/250000 : ℚ) by norm_num]
  exact coverp000001110011011
theorem coverp00000111001101 : Covers (-230261639/500000 : ℚ) vp00000111001101 := join_branches bp000001110011010 bp000001110011011
private noncomputable def vp000001110011001_0 : Blocks := edgeBlocks% "full/vectors/000001110011001-V-0000.bin"
noncomputable def vp000001110011001 : Blocks := vp000001110011001_0
theorem coverp000001110011001 : Covers (-230011639/250000 : ℚ) vp000001110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110011000_0 : Blocks := edgeBlocks% "full/vectors/000001110011000-V-0000.bin"
noncomputable def vp000001110011000 : Blocks := vp000001110011000_0
theorem coverp000001110011000 : Covers (-229761639/250000 : ℚ) vp000001110011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111001100_0 : Blocks := edgeBlocks% "full/vectors/00000111001100-V-0000.bin"
noncomputable def vp00000111001100 : Blocks := vp00000111001100_0
private theorem bp000001110011000 : Branch 0 (-229761639/500000 : ℚ) vp00000111001100 := by
  apply branch_left_normalized (c:=vp000001110011000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-229761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-229761639/250000 : ℚ) by norm_num]
  exact coverp000001110011000
private noncomputable def ep000001110011001_0 : Blocks := edgeBlocks% "full/vectors/000001110011001-E-0000.bin"
noncomputable def ep000001110011001 : Blocks := ep000001110011001_0
private theorem idp000001110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111001100.list =
    C ((2:ℤ)^54) * horner X vp000001110011001.list + horner X ep000001110011001.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110011001 : Branch 1 (-229761639/500000 : ℚ) vp00000111001100 := by
  apply branch_checked idp000001110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-229761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-230011639/250000 : ℚ) by norm_num]
  exact coverp000001110011001
theorem coverp00000111001100 : Covers (-229761639/500000 : ℚ) vp00000111001100 := join_branches bp000001110011000 bp000001110011001
private noncomputable def vp0000011100110_0 : Blocks := edgeBlocks% "full/vectors/0000011100110-V-0000.bin"
noncomputable def vp0000011100110 : Blocks := vp0000011100110_0
private theorem bp00000111001100 : Branch 0 (-229761639/1000000 : ℚ) vp0000011100110 := by
  apply branch_left_normalized (c:=vp00000111001100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-229761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-229761639/500000 : ℚ) by norm_num]
  exact coverp00000111001100
private noncomputable def ep00000111001101_0 : Blocks := edgeBlocks% "full/vectors/00000111001101-E-0000.bin"
noncomputable def ep00000111001101 : Blocks := ep00000111001101_0
private theorem idp00000111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011100110.list =
    C ((2:ℤ)^89) * horner X vp00000111001101.list + horner X ep00000111001101.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111001101 : Branch 1 (-229761639/1000000 : ℚ) vp0000011100110 := by
  apply branch_checked idp00000111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-229761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-230261639/500000 : ℚ) by norm_num]
  exact coverp00000111001101
theorem coverp0000011100110 : Covers (-229761639/1000000 : ℚ) vp0000011100110 := join_branches bp00000111001100 bp00000111001101
private noncomputable def vp000001110011_0 : Blocks := edgeBlocks% "full/vectors/000001110011-V-0000.bin"
private noncomputable def vp000001110011_1 : Blocks := edgeBlocks% "full/vectors/000001110011-V-0001.bin"
noncomputable def vp000001110011 : Blocks := (Blocks.join vp000001110011_0 vp000001110011_1)
private theorem bp0000011100110 : Branch 0 (-229761639/2000000 : ℚ) vp000001110011 := by
  apply branch_left_normalized (c:=vp0000011100110) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-229761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-229761639/1000000 : ℚ) by norm_num]
  exact coverp0000011100110
private noncomputable def ep0000011100111_0 : Blocks := edgeBlocks% "full/vectors/0000011100111-E-0000.bin"
private noncomputable def ep0000011100111_1 : Blocks := edgeBlocks% "full/vectors/0000011100111-E-0001.bin"
noncomputable def ep0000011100111 : Blocks := (Blocks.join ep0000011100111_0 ep0000011100111_1)
private theorem idp0000011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001110011.list =
    C ((2:ℤ)^157) * horner X vp0000011100111.list + horner X ep0000011100111.list := by
  exact edge_identity (B := (2:ℤ)^321) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011100111 : Branch 1 (-229761639/2000000 : ℚ) vp000001110011 := by
  apply branch_checked idp0000011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-229761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-230761639/1000000 : ℚ) by norm_num]
  exact coverp0000011100111
theorem coverp000001110011 : Covers (-229761639/2000000 : ℚ) vp000001110011 := join_branches bp0000011100110 bp0000011100111
private noncomputable def vp000001110010111_0 : Blocks := edgeBlocks% "full/vectors/000001110010111-V-0000.bin"
noncomputable def vp000001110010111 : Blocks := vp000001110010111_0
theorem coverp000001110010111 : Covers (-229511639/250000 : ℚ) vp000001110010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110010110_0 : Blocks := edgeBlocks% "full/vectors/000001110010110-V-0000.bin"
noncomputable def vp000001110010110 : Blocks := vp000001110010110_0
theorem coverp000001110010110 : Covers (-229261639/250000 : ℚ) vp000001110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111001011_0 : Blocks := edgeBlocks% "full/vectors/00000111001011-V-0000.bin"
noncomputable def vp00000111001011 : Blocks := vp00000111001011_0
private theorem bp000001110010110 : Branch 0 (-229261639/500000 : ℚ) vp00000111001011 := by
  apply branch_left_normalized (c:=vp000001110010110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-229261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-229261639/250000 : ℚ) by norm_num]
  exact coverp000001110010110
private noncomputable def ep000001110010111_0 : Blocks := edgeBlocks% "full/vectors/000001110010111-E-0000.bin"
noncomputable def ep000001110010111 : Blocks := ep000001110010111_0
private theorem idp000001110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111001011.list =
    C ((2:ℤ)^54) * horner X vp000001110010111.list + horner X ep000001110010111.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110010111 : Branch 1 (-229261639/500000 : ℚ) vp00000111001011 := by
  apply branch_checked idp000001110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-229261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-229511639/250000 : ℚ) by norm_num]
  exact coverp000001110010111
theorem coverp00000111001011 : Covers (-229261639/500000 : ℚ) vp00000111001011 := join_branches bp000001110010110 bp000001110010111
private noncomputable def vp000001110010101_0 : Blocks := edgeBlocks% "full/vectors/000001110010101-V-0000.bin"
noncomputable def vp000001110010101 : Blocks := vp000001110010101_0
theorem coverp000001110010101 : Covers (-229011639/250000 : ℚ) vp000001110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110010100_0 : Blocks := edgeBlocks% "full/vectors/000001110010100-V-0000.bin"
noncomputable def vp000001110010100 : Blocks := vp000001110010100_0
theorem coverp000001110010100 : Covers (-228761639/250000 : ℚ) vp000001110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111001010_0 : Blocks := edgeBlocks% "full/vectors/00000111001010-V-0000.bin"
noncomputable def vp00000111001010 : Blocks := vp00000111001010_0
private theorem bp000001110010100 : Branch 0 (-228761639/500000 : ℚ) vp00000111001010 := by
  apply branch_left_normalized (c:=vp000001110010100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-228761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-228761639/250000 : ℚ) by norm_num]
  exact coverp000001110010100
private noncomputable def ep000001110010101_0 : Blocks := edgeBlocks% "full/vectors/000001110010101-E-0000.bin"
noncomputable def ep000001110010101 : Blocks := ep000001110010101_0
private theorem idp000001110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111001010.list =
    C ((2:ℤ)^55) * horner X vp000001110010101.list + horner X ep000001110010101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110010101 : Branch 1 (-228761639/500000 : ℚ) vp00000111001010 := by
  apply branch_checked idp000001110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-228761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-229011639/250000 : ℚ) by norm_num]
  exact coverp000001110010101
theorem coverp00000111001010 : Covers (-228761639/500000 : ℚ) vp00000111001010 := join_branches bp000001110010100 bp000001110010101
private noncomputable def vp0000011100101_0 : Blocks := edgeBlocks% "full/vectors/0000011100101-V-0000.bin"
noncomputable def vp0000011100101 : Blocks := vp0000011100101_0
private theorem bp00000111001010 : Branch 0 (-228761639/1000000 : ℚ) vp0000011100101 := by
  apply branch_left_normalized (c:=vp00000111001010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-228761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-228761639/500000 : ℚ) by norm_num]
  exact coverp00000111001010
private noncomputable def ep00000111001011_0 : Blocks := edgeBlocks% "full/vectors/00000111001011-E-0000.bin"
noncomputable def ep00000111001011 : Blocks := ep00000111001011_0
private theorem idp00000111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011100101.list =
    C ((2:ℤ)^91) * horner X vp00000111001011.list + horner X ep00000111001011.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111001011 : Branch 1 (-228761639/1000000 : ℚ) vp0000011100101 := by
  apply branch_checked idp00000111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-228761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-229261639/500000 : ℚ) by norm_num]
  exact coverp00000111001011
theorem coverp0000011100101 : Covers (-228761639/1000000 : ℚ) vp0000011100101 := join_branches bp00000111001010 bp00000111001011
private noncomputable def vp000001110010011_0 : Blocks := edgeBlocks% "full/vectors/000001110010011-V-0000.bin"
noncomputable def vp000001110010011 : Blocks := vp000001110010011_0
theorem coverp000001110010011 : Covers (-228511639/250000 : ℚ) vp000001110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110010010_0 : Blocks := edgeBlocks% "full/vectors/000001110010010-V-0000.bin"
noncomputable def vp000001110010010 : Blocks := vp000001110010010_0
theorem coverp000001110010010 : Covers (-228261639/250000 : ℚ) vp000001110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111001001_0 : Blocks := edgeBlocks% "full/vectors/00000111001001-V-0000.bin"
noncomputable def vp00000111001001 : Blocks := vp00000111001001_0
private theorem bp000001110010010 : Branch 0 (-228261639/500000 : ℚ) vp00000111001001 := by
  apply branch_left_normalized (c:=vp000001110010010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-228261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-228261639/250000 : ℚ) by norm_num]
  exact coverp000001110010010
private noncomputable def ep000001110010011_0 : Blocks := edgeBlocks% "full/vectors/000001110010011-E-0000.bin"
noncomputable def ep000001110010011 : Blocks := ep000001110010011_0
private theorem idp000001110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111001001.list =
    C ((2:ℤ)^54) * horner X vp000001110010011.list + horner X ep000001110010011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110010011 : Branch 1 (-228261639/500000 : ℚ) vp00000111001001 := by
  apply branch_checked idp000001110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-228261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-228511639/250000 : ℚ) by norm_num]
  exact coverp000001110010011
theorem coverp00000111001001 : Covers (-228261639/500000 : ℚ) vp00000111001001 := join_branches bp000001110010010 bp000001110010011
private noncomputable def vp000001110010001_0 : Blocks := edgeBlocks% "full/vectors/000001110010001-V-0000.bin"
noncomputable def vp000001110010001 : Blocks := vp000001110010001_0
theorem coverp000001110010001 : Covers (-228011639/250000 : ℚ) vp000001110010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110010000_0 : Blocks := edgeBlocks% "full/vectors/000001110010000-V-0000.bin"
noncomputable def vp000001110010000 : Blocks := vp000001110010000_0
theorem coverp000001110010000 : Covers (-227761639/250000 : ℚ) vp000001110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111001000_0 : Blocks := edgeBlocks% "full/vectors/00000111001000-V-0000.bin"
noncomputable def vp00000111001000 : Blocks := vp00000111001000_0
private theorem bp000001110010000 : Branch 0 (-227761639/500000 : ℚ) vp00000111001000 := by
  apply branch_left_normalized (c:=vp000001110010000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-227761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-227761639/250000 : ℚ) by norm_num]
  exact coverp000001110010000
private noncomputable def ep000001110010001_0 : Blocks := edgeBlocks% "full/vectors/000001110010001-E-0000.bin"
noncomputable def ep000001110010001 : Blocks := ep000001110010001_0
private theorem idp000001110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111001000.list =
    C ((2:ℤ)^54) * horner X vp000001110010001.list + horner X ep000001110010001.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110010001 : Branch 1 (-227761639/500000 : ℚ) vp00000111001000 := by
  apply branch_checked idp000001110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-227761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-228011639/250000 : ℚ) by norm_num]
  exact coverp000001110010001
theorem coverp00000111001000 : Covers (-227761639/500000 : ℚ) vp00000111001000 := join_branches bp000001110010000 bp000001110010001
private noncomputable def vp0000011100100_0 : Blocks := edgeBlocks% "full/vectors/0000011100100-V-0000.bin"
noncomputable def vp0000011100100 : Blocks := vp0000011100100_0
private theorem bp00000111001000 : Branch 0 (-227761639/1000000 : ℚ) vp0000011100100 := by
  apply branch_left_normalized (c:=vp00000111001000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-227761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-227761639/500000 : ℚ) by norm_num]
  exact coverp00000111001000
private noncomputable def ep00000111001001_0 : Blocks := edgeBlocks% "full/vectors/00000111001001-E-0000.bin"
noncomputable def ep00000111001001 : Blocks := ep00000111001001_0
private theorem idp00000111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011100100.list =
    C ((2:ℤ)^90) * horner X vp00000111001001.list + horner X ep00000111001001.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111001001 : Branch 1 (-227761639/1000000 : ℚ) vp0000011100100 := by
  apply branch_checked idp00000111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-227761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-228261639/500000 : ℚ) by norm_num]
  exact coverp00000111001001
theorem coverp0000011100100 : Covers (-227761639/1000000 : ℚ) vp0000011100100 := join_branches bp00000111001000 bp00000111001001
private noncomputable def vp000001110010_0 : Blocks := edgeBlocks% "full/vectors/000001110010-V-0000.bin"
private noncomputable def vp000001110010_1 : Blocks := edgeBlocks% "full/vectors/000001110010-V-0001.bin"
noncomputable def vp000001110010 : Blocks := (Blocks.join vp000001110010_0 vp000001110010_1)
private theorem bp0000011100100 : Branch 0 (-227761639/2000000 : ℚ) vp000001110010 := by
  apply branch_left_normalized (c:=vp0000011100100) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-227761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-227761639/1000000 : ℚ) by norm_num]
  exact coverp0000011100100
private noncomputable def ep0000011100101_0 : Blocks := edgeBlocks% "full/vectors/0000011100101-E-0000.bin"
private noncomputable def ep0000011100101_1 : Blocks := edgeBlocks% "full/vectors/0000011100101-E-0001.bin"
noncomputable def ep0000011100101 : Blocks := (Blocks.join ep0000011100101_0 ep0000011100101_1)
private theorem idp0000011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001110010.list =
    C ((2:ℤ)^160) * horner X vp0000011100101.list + horner X ep0000011100101.list := by
  exact edge_identity (B := (2:ℤ)^325) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011100101 : Branch 1 (-227761639/2000000 : ℚ) vp000001110010 := by
  apply branch_checked idp0000011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-227761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-228761639/1000000 : ℚ) by norm_num]
  exact coverp0000011100101
theorem coverp000001110010 : Covers (-227761639/2000000 : ℚ) vp000001110010 := join_branches bp0000011100100 bp0000011100101
private noncomputable def vp00000111001_0 : Blocks := edgeBlocks% "full/vectors/00000111001-V-0000.bin"
private noncomputable def vp00000111001_1 : Blocks := edgeBlocks% "full/vectors/00000111001-V-0001.bin"
private noncomputable def vp00000111001_2 : Blocks := edgeBlocks% "full/vectors/00000111001-V-0002.bin"
noncomputable def vp00000111001 : Blocks := (Blocks.join vp00000111001_0 (Blocks.join vp00000111001_1 vp00000111001_2))
private theorem bp000001110010 : Branch 0 (-227761639/4000000 : ℚ) vp00000111001 := by
  apply branch_left_normalized (c:=vp000001110010) (k:=0) (m:=153) (by decide +kernel)
  rw [show 2*(-227761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-227761639/2000000 : ℚ) by norm_num]
  exact coverp000001110010
private noncomputable def ep000001110011_0 : Blocks := edgeBlocks% "full/vectors/000001110011-E-0000.bin"
private noncomputable def ep000001110011_1 : Blocks := edgeBlocks% "full/vectors/000001110011-E-0001.bin"
private noncomputable def ep000001110011_2 : Blocks := edgeBlocks% "full/vectors/000001110011-E-0002.bin"
noncomputable def ep000001110011 : Blocks := (Blocks.join ep000001110011_0 (Blocks.join ep000001110011_1 ep000001110011_2))
private theorem idp000001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111001.list =
    C ((2:ℤ)^297) * horner X vp000001110011.list + horner X ep000001110011.list := by
  exact edge_identity (B := (2:ℤ)^524) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110011 : Branch 1 (-227761639/4000000 : ℚ) vp00000111001 := by
  apply branch_checked idp000001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-227761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-229761639/2000000 : ℚ) by norm_num]
  exact coverp000001110011
theorem coverp00000111001 : Covers (-227761639/4000000 : ℚ) vp00000111001 := join_branches bp000001110010 bp000001110011
private noncomputable def vp000001110001111_0 : Blocks := edgeBlocks% "full/vectors/000001110001111-V-0000.bin"
noncomputable def vp000001110001111 : Blocks := vp000001110001111_0
theorem coverp000001110001111 : Covers (-227511639/250000 : ℚ) vp000001110001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110001110_0 : Blocks := edgeBlocks% "full/vectors/000001110001110-V-0000.bin"
noncomputable def vp000001110001110 : Blocks := vp000001110001110_0
theorem coverp000001110001110 : Covers (-227261639/250000 : ℚ) vp000001110001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111000111_0 : Blocks := edgeBlocks% "full/vectors/00000111000111-V-0000.bin"
noncomputable def vp00000111000111 : Blocks := vp00000111000111_0
private theorem bp000001110001110 : Branch 0 (-227261639/500000 : ℚ) vp00000111000111 := by
  apply branch_left_normalized (c:=vp000001110001110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-227261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-227261639/250000 : ℚ) by norm_num]
  exact coverp000001110001110
private noncomputable def ep000001110001111_0 : Blocks := edgeBlocks% "full/vectors/000001110001111-E-0000.bin"
noncomputable def ep000001110001111 : Blocks := ep000001110001111_0
private theorem idp000001110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111000111.list =
    C ((2:ℤ)^54) * horner X vp000001110001111.list + horner X ep000001110001111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110001111 : Branch 1 (-227261639/500000 : ℚ) vp00000111000111 := by
  apply branch_checked idp000001110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-227261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-227511639/250000 : ℚ) by norm_num]
  exact coverp000001110001111
theorem coverp00000111000111 : Covers (-227261639/500000 : ℚ) vp00000111000111 := join_branches bp000001110001110 bp000001110001111
private noncomputable def vp000001110001101_0 : Blocks := edgeBlocks% "full/vectors/000001110001101-V-0000.bin"
noncomputable def vp000001110001101 : Blocks := vp000001110001101_0
theorem coverp000001110001101 : Covers (-227011639/250000 : ℚ) vp000001110001101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110001100_0 : Blocks := edgeBlocks% "full/vectors/000001110001100-V-0000.bin"
noncomputable def vp000001110001100 : Blocks := vp000001110001100_0
theorem coverp000001110001100 : Covers (-226761639/250000 : ℚ) vp000001110001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111000110_0 : Blocks := edgeBlocks% "full/vectors/00000111000110-V-0000.bin"
noncomputable def vp00000111000110 : Blocks := vp00000111000110_0
private theorem bp000001110001100 : Branch 0 (-226761639/500000 : ℚ) vp00000111000110 := by
  apply branch_left_normalized (c:=vp000001110001100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-226761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-226761639/250000 : ℚ) by norm_num]
  exact coverp000001110001100
private noncomputable def ep000001110001101_0 : Blocks := edgeBlocks% "full/vectors/000001110001101-E-0000.bin"
noncomputable def ep000001110001101 : Blocks := ep000001110001101_0
private theorem idp000001110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111000110.list =
    C ((2:ℤ)^53) * horner X vp000001110001101.list + horner X ep000001110001101.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110001101 : Branch 1 (-226761639/500000 : ℚ) vp00000111000110 := by
  apply branch_checked idp000001110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-226761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-227011639/250000 : ℚ) by norm_num]
  exact coverp000001110001101
theorem coverp00000111000110 : Covers (-226761639/500000 : ℚ) vp00000111000110 := join_branches bp000001110001100 bp000001110001101
private noncomputable def vp0000011100011_0 : Blocks := edgeBlocks% "full/vectors/0000011100011-V-0000.bin"
noncomputable def vp0000011100011 : Blocks := vp0000011100011_0
private theorem bp00000111000110 : Branch 0 (-226761639/1000000 : ℚ) vp0000011100011 := by
  apply branch_left_normalized (c:=vp00000111000110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-226761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-226761639/500000 : ℚ) by norm_num]
  exact coverp00000111000110
private noncomputable def ep00000111000111_0 : Blocks := edgeBlocks% "full/vectors/00000111000111-E-0000.bin"
noncomputable def ep00000111000111 : Blocks := ep00000111000111_0
private theorem idp00000111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011100011.list =
    C ((2:ℤ)^88) * horner X vp00000111000111.list + horner X ep00000111000111.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111000111 : Branch 1 (-226761639/1000000 : ℚ) vp0000011100011 := by
  apply branch_checked idp00000111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-226761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-227261639/500000 : ℚ) by norm_num]
  exact coverp00000111000111
theorem coverp0000011100011 : Covers (-226761639/1000000 : ℚ) vp0000011100011 := join_branches bp00000111000110 bp00000111000111
private noncomputable def vp000001110001011_0 : Blocks := edgeBlocks% "full/vectors/000001110001011-V-0000.bin"
noncomputable def vp000001110001011 : Blocks := vp000001110001011_0
theorem coverp000001110001011 : Covers (-226511639/250000 : ℚ) vp000001110001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110001010_0 : Blocks := edgeBlocks% "full/vectors/000001110001010-V-0000.bin"
noncomputable def vp000001110001010 : Blocks := vp000001110001010_0
theorem coverp000001110001010 : Covers (-226261639/250000 : ℚ) vp000001110001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111000101_0 : Blocks := edgeBlocks% "full/vectors/00000111000101-V-0000.bin"
noncomputable def vp00000111000101 : Blocks := vp00000111000101_0
private theorem bp000001110001010 : Branch 0 (-226261639/500000 : ℚ) vp00000111000101 := by
  apply branch_left_normalized (c:=vp000001110001010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-226261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-226261639/250000 : ℚ) by norm_num]
  exact coverp000001110001010
private noncomputable def ep000001110001011_0 : Blocks := edgeBlocks% "full/vectors/000001110001011-E-0000.bin"
noncomputable def ep000001110001011 : Blocks := ep000001110001011_0
private theorem idp000001110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111000101.list =
    C ((2:ℤ)^54) * horner X vp000001110001011.list + horner X ep000001110001011.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110001011 : Branch 1 (-226261639/500000 : ℚ) vp00000111000101 := by
  apply branch_checked idp000001110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-226261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-226511639/250000 : ℚ) by norm_num]
  exact coverp000001110001011
theorem coverp00000111000101 : Covers (-226261639/500000 : ℚ) vp00000111000101 := join_branches bp000001110001010 bp000001110001011
private noncomputable def vp000001110001001_0 : Blocks := edgeBlocks% "full/vectors/000001110001001-V-0000.bin"
noncomputable def vp000001110001001 : Blocks := vp000001110001001_0
theorem coverp000001110001001 : Covers (-226011639/250000 : ℚ) vp000001110001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110001000_0 : Blocks := edgeBlocks% "full/vectors/000001110001000-V-0000.bin"
noncomputable def vp000001110001000 : Blocks := vp000001110001000_0
theorem coverp000001110001000 : Covers (-225761639/250000 : ℚ) vp000001110001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111000100_0 : Blocks := edgeBlocks% "full/vectors/00000111000100-V-0000.bin"
noncomputable def vp00000111000100 : Blocks := vp00000111000100_0
private theorem bp000001110001000 : Branch 0 (-225761639/500000 : ℚ) vp00000111000100 := by
  apply branch_left_normalized (c:=vp000001110001000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-225761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-225761639/250000 : ℚ) by norm_num]
  exact coverp000001110001000
private noncomputable def ep000001110001001_0 : Blocks := edgeBlocks% "full/vectors/000001110001001-E-0000.bin"
noncomputable def ep000001110001001 : Blocks := ep000001110001001_0
private theorem idp000001110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111000100.list =
    C ((2:ℤ)^53) * horner X vp000001110001001.list + horner X ep000001110001001.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110001001 : Branch 1 (-225761639/500000 : ℚ) vp00000111000100 := by
  apply branch_checked idp000001110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-225761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-226011639/250000 : ℚ) by norm_num]
  exact coverp000001110001001
theorem coverp00000111000100 : Covers (-225761639/500000 : ℚ) vp00000111000100 := join_branches bp000001110001000 bp000001110001001
private noncomputable def vp0000011100010_0 : Blocks := edgeBlocks% "full/vectors/0000011100010-V-0000.bin"
noncomputable def vp0000011100010 : Blocks := vp0000011100010_0
private theorem bp00000111000100 : Branch 0 (-225761639/1000000 : ℚ) vp0000011100010 := by
  apply branch_left_normalized (c:=vp00000111000100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-225761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-225761639/500000 : ℚ) by norm_num]
  exact coverp00000111000100
private noncomputable def ep00000111000101_0 : Blocks := edgeBlocks% "full/vectors/00000111000101-E-0000.bin"
noncomputable def ep00000111000101 : Blocks := ep00000111000101_0
private theorem idp00000111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011100010.list =
    C ((2:ℤ)^88) * horner X vp00000111000101.list + horner X ep00000111000101.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111000101 : Branch 1 (-225761639/1000000 : ℚ) vp0000011100010 := by
  apply branch_checked idp00000111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-225761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-226261639/500000 : ℚ) by norm_num]
  exact coverp00000111000101
theorem coverp0000011100010 : Covers (-225761639/1000000 : ℚ) vp0000011100010 := join_branches bp00000111000100 bp00000111000101
private noncomputable def vp000001110001_0 : Blocks := edgeBlocks% "full/vectors/000001110001-V-0000.bin"
private noncomputable def vp000001110001_1 : Blocks := edgeBlocks% "full/vectors/000001110001-V-0001.bin"
noncomputable def vp000001110001 : Blocks := (Blocks.join vp000001110001_0 vp000001110001_1)
private theorem bp0000011100010 : Branch 0 (-225761639/2000000 : ℚ) vp000001110001 := by
  apply branch_left_normalized (c:=vp0000011100010) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-225761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-225761639/1000000 : ℚ) by norm_num]
  exact coverp0000011100010
private noncomputable def ep0000011100011_0 : Blocks := edgeBlocks% "full/vectors/0000011100011-E-0000.bin"
private noncomputable def ep0000011100011_1 : Blocks := edgeBlocks% "full/vectors/0000011100011-E-0001.bin"
noncomputable def ep0000011100011 : Blocks := (Blocks.join ep0000011100011_0 ep0000011100011_1)
private theorem idp0000011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001110001.list =
    C ((2:ℤ)^158) * horner X vp0000011100011.list + horner X ep0000011100011.list := by
  exact edge_identity (B := (2:ℤ)^322) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011100011 : Branch 1 (-225761639/2000000 : ℚ) vp000001110001 := by
  apply branch_checked idp0000011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-225761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-226761639/1000000 : ℚ) by norm_num]
  exact coverp0000011100011
theorem coverp000001110001 : Covers (-225761639/2000000 : ℚ) vp000001110001 := join_branches bp0000011100010 bp0000011100011
private noncomputable def vp000001110000111_0 : Blocks := edgeBlocks% "full/vectors/000001110000111-V-0000.bin"
noncomputable def vp000001110000111 : Blocks := vp000001110000111_0
theorem coverp000001110000111 : Covers (-225511639/250000 : ℚ) vp000001110000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110000110_0 : Blocks := edgeBlocks% "full/vectors/000001110000110-V-0000.bin"
noncomputable def vp000001110000110 : Blocks := vp000001110000110_0
theorem coverp000001110000110 : Covers (-225261639/250000 : ℚ) vp000001110000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111000011_0 : Blocks := edgeBlocks% "full/vectors/00000111000011-V-0000.bin"
noncomputable def vp00000111000011 : Blocks := vp00000111000011_0
private theorem bp000001110000110 : Branch 0 (-225261639/500000 : ℚ) vp00000111000011 := by
  apply branch_left_normalized (c:=vp000001110000110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-225261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-225261639/250000 : ℚ) by norm_num]
  exact coverp000001110000110
private noncomputable def ep000001110000111_0 : Blocks := edgeBlocks% "full/vectors/000001110000111-E-0000.bin"
noncomputable def ep000001110000111 : Blocks := ep000001110000111_0
private theorem idp000001110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111000011.list =
    C ((2:ℤ)^53) * horner X vp000001110000111.list + horner X ep000001110000111.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110000111 : Branch 1 (-225261639/500000 : ℚ) vp00000111000011 := by
  apply branch_checked idp000001110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-225261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-225511639/250000 : ℚ) by norm_num]
  exact coverp000001110000111
theorem coverp00000111000011 : Covers (-225261639/500000 : ℚ) vp00000111000011 := join_branches bp000001110000110 bp000001110000111
private noncomputable def vp000001110000101_0 : Blocks := edgeBlocks% "full/vectors/000001110000101-V-0000.bin"
noncomputable def vp000001110000101 : Blocks := vp000001110000101_0
theorem coverp000001110000101 : Covers (-225011639/250000 : ℚ) vp000001110000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110000100_0 : Blocks := edgeBlocks% "full/vectors/000001110000100-V-0000.bin"
noncomputable def vp000001110000100 : Blocks := vp000001110000100_0
theorem coverp000001110000100 : Covers (-224761639/250000 : ℚ) vp000001110000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111000010_0 : Blocks := edgeBlocks% "full/vectors/00000111000010-V-0000.bin"
noncomputable def vp00000111000010 : Blocks := vp00000111000010_0
private theorem bp000001110000100 : Branch 0 (-224761639/500000 : ℚ) vp00000111000010 := by
  apply branch_left_normalized (c:=vp000001110000100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-224761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-224761639/250000 : ℚ) by norm_num]
  exact coverp000001110000100
private noncomputable def ep000001110000101_0 : Blocks := edgeBlocks% "full/vectors/000001110000101-E-0000.bin"
noncomputable def ep000001110000101 : Blocks := ep000001110000101_0
private theorem idp000001110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111000010.list =
    C ((2:ℤ)^55) * horner X vp000001110000101.list + horner X ep000001110000101.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110000101 : Branch 1 (-224761639/500000 : ℚ) vp00000111000010 := by
  apply branch_checked idp000001110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-224761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-225011639/250000 : ℚ) by norm_num]
  exact coverp000001110000101
theorem coverp00000111000010 : Covers (-224761639/500000 : ℚ) vp00000111000010 := join_branches bp000001110000100 bp000001110000101
private noncomputable def vp0000011100001_0 : Blocks := edgeBlocks% "full/vectors/0000011100001-V-0000.bin"
noncomputable def vp0000011100001 : Blocks := vp0000011100001_0
private theorem bp00000111000010 : Branch 0 (-224761639/1000000 : ℚ) vp0000011100001 := by
  apply branch_left_normalized (c:=vp00000111000010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-224761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-224761639/500000 : ℚ) by norm_num]
  exact coverp00000111000010
private noncomputable def ep00000111000011_0 : Blocks := edgeBlocks% "full/vectors/00000111000011-E-0000.bin"
noncomputable def ep00000111000011 : Blocks := ep00000111000011_0
private theorem idp00000111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011100001.list =
    C ((2:ℤ)^90) * horner X vp00000111000011.list + horner X ep00000111000011.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111000011 : Branch 1 (-224761639/1000000 : ℚ) vp0000011100001 := by
  apply branch_checked idp00000111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-224761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-225261639/500000 : ℚ) by norm_num]
  exact coverp00000111000011
theorem coverp0000011100001 : Covers (-224761639/1000000 : ℚ) vp0000011100001 := join_branches bp00000111000010 bp00000111000011
private noncomputable def vp000001110000011_0 : Blocks := edgeBlocks% "full/vectors/000001110000011-V-0000.bin"
noncomputable def vp000001110000011 : Blocks := vp000001110000011_0
theorem coverp000001110000011 : Covers (-224511639/250000 : ℚ) vp000001110000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110000010_0 : Blocks := edgeBlocks% "full/vectors/000001110000010-V-0000.bin"
noncomputable def vp000001110000010 : Blocks := vp000001110000010_0
theorem coverp000001110000010 : Covers (-224261639/250000 : ℚ) vp000001110000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111000001_0 : Blocks := edgeBlocks% "full/vectors/00000111000001-V-0000.bin"
noncomputable def vp00000111000001 : Blocks := vp00000111000001_0
private theorem bp000001110000010 : Branch 0 (-224261639/500000 : ℚ) vp00000111000001 := by
  apply branch_left_normalized (c:=vp000001110000010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-224261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-224261639/250000 : ℚ) by norm_num]
  exact coverp000001110000010
private noncomputable def ep000001110000011_0 : Blocks := edgeBlocks% "full/vectors/000001110000011-E-0000.bin"
noncomputable def ep000001110000011 : Blocks := ep000001110000011_0
private theorem idp000001110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111000001.list =
    C ((2:ℤ)^55) * horner X vp000001110000011.list + horner X ep000001110000011.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110000011 : Branch 1 (-224261639/500000 : ℚ) vp00000111000001 := by
  apply branch_checked idp000001110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-224261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-224511639/250000 : ℚ) by norm_num]
  exact coverp000001110000011
theorem coverp00000111000001 : Covers (-224261639/500000 : ℚ) vp00000111000001 := join_branches bp000001110000010 bp000001110000011
private noncomputable def vp000001110000001_0 : Blocks := edgeBlocks% "full/vectors/000001110000001-V-0000.bin"
noncomputable def vp000001110000001 : Blocks := vp000001110000001_0
theorem coverp000001110000001 : Covers (-224011639/250000 : ℚ) vp000001110000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001110000000_0 : Blocks := edgeBlocks% "full/vectors/000001110000000-V-0000.bin"
noncomputable def vp000001110000000 : Blocks := vp000001110000000_0
theorem coverp000001110000000 : Covers (-223761639/250000 : ℚ) vp000001110000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000111000000_0 : Blocks := edgeBlocks% "full/vectors/00000111000000-V-0000.bin"
noncomputable def vp00000111000000 : Blocks := vp00000111000000_0
private theorem bp000001110000000 : Branch 0 (-223761639/500000 : ℚ) vp00000111000000 := by
  apply branch_left_normalized (c:=vp000001110000000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-223761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-223761639/250000 : ℚ) by norm_num]
  exact coverp000001110000000
private noncomputable def ep000001110000001_0 : Blocks := edgeBlocks% "full/vectors/000001110000001-E-0000.bin"
noncomputable def ep000001110000001 : Blocks := ep000001110000001_0
private theorem idp000001110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111000000.list =
    C ((2:ℤ)^56) * horner X vp000001110000001.list + horner X ep000001110000001.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110000001 : Branch 1 (-223761639/500000 : ℚ) vp00000111000000 := by
  apply branch_checked idp000001110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-223761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-224011639/250000 : ℚ) by norm_num]
  exact coverp000001110000001
theorem coverp00000111000000 : Covers (-223761639/500000 : ℚ) vp00000111000000 := join_branches bp000001110000000 bp000001110000001
private noncomputable def vp0000011100000_0 : Blocks := edgeBlocks% "full/vectors/0000011100000-V-0000.bin"
noncomputable def vp0000011100000 : Blocks := vp0000011100000_0
private theorem bp00000111000000 : Branch 0 (-223761639/1000000 : ℚ) vp0000011100000 := by
  apply branch_left_normalized (c:=vp00000111000000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-223761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-223761639/500000 : ℚ) by norm_num]
  exact coverp00000111000000
private noncomputable def ep00000111000001_0 : Blocks := edgeBlocks% "full/vectors/00000111000001-E-0000.bin"
noncomputable def ep00000111000001 : Blocks := ep00000111000001_0
private theorem idp00000111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011100000.list =
    C ((2:ℤ)^93) * horner X vp00000111000001.list + horner X ep00000111000001.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111000001 : Branch 1 (-223761639/1000000 : ℚ) vp0000011100000 := by
  apply branch_checked idp00000111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-223761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-224261639/500000 : ℚ) by norm_num]
  exact coverp00000111000001
theorem coverp0000011100000 : Covers (-223761639/1000000 : ℚ) vp0000011100000 := join_branches bp00000111000000 bp00000111000001
private noncomputable def vp000001110000_0 : Blocks := edgeBlocks% "full/vectors/000001110000-V-0000.bin"
private noncomputable def vp000001110000_1 : Blocks := edgeBlocks% "full/vectors/000001110000-V-0001.bin"
noncomputable def vp000001110000 : Blocks := (Blocks.join vp000001110000_0 vp000001110000_1)
private theorem bp0000011100000 : Branch 0 (-223761639/2000000 : ℚ) vp000001110000 := by
  apply branch_left_normalized (c:=vp0000011100000) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-223761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-223761639/1000000 : ℚ) by norm_num]
  exact coverp0000011100000
private noncomputable def ep0000011100001_0 : Blocks := edgeBlocks% "full/vectors/0000011100001-E-0000.bin"
private noncomputable def ep0000011100001_1 : Blocks := edgeBlocks% "full/vectors/0000011100001-E-0001.bin"
noncomputable def ep0000011100001 : Blocks := (Blocks.join ep0000011100001_0 ep0000011100001_1)
private theorem idp0000011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001110000.list =
    C ((2:ℤ)^162) * horner X vp0000011100001.list + horner X ep0000011100001.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011100001 : Branch 1 (-223761639/2000000 : ℚ) vp000001110000 := by
  apply branch_checked idp0000011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-223761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-224761639/1000000 : ℚ) by norm_num]
  exact coverp0000011100001
theorem coverp000001110000 : Covers (-223761639/2000000 : ℚ) vp000001110000 := join_branches bp0000011100000 bp0000011100001
private noncomputable def vp00000111000_0 : Blocks := edgeBlocks% "full/vectors/00000111000-V-0000.bin"
private noncomputable def vp00000111000_1 : Blocks := edgeBlocks% "full/vectors/00000111000-V-0001.bin"
private noncomputable def vp00000111000_2 : Blocks := edgeBlocks% "full/vectors/00000111000-V-0002.bin"
noncomputable def vp00000111000 : Blocks := (Blocks.join vp00000111000_0 (Blocks.join vp00000111000_1 vp00000111000_2))
private theorem bp000001110000 : Branch 0 (-223761639/4000000 : ℚ) vp00000111000 := by
  apply branch_left_normalized (c:=vp000001110000) (k:=0) (m:=153) (by decide +kernel)
  rw [show 2*(-223761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-223761639/2000000 : ℚ) by norm_num]
  exact coverp000001110000
private noncomputable def ep000001110001_0 : Blocks := edgeBlocks% "full/vectors/000001110001-E-0000.bin"
private noncomputable def ep000001110001_1 : Blocks := edgeBlocks% "full/vectors/000001110001-E-0001.bin"
private noncomputable def ep000001110001_2 : Blocks := edgeBlocks% "full/vectors/000001110001-E-0002.bin"
noncomputable def ep000001110001 : Blocks := (Blocks.join ep000001110001_0 (Blocks.join ep000001110001_1 ep000001110001_2))
private theorem idp000001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111000.list =
    C ((2:ℤ)^301) * horner X vp000001110001.list + horner X ep000001110001.list := by
  exact edge_identity (B := (2:ℤ)^528) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001110001 : Branch 1 (-223761639/4000000 : ℚ) vp00000111000 := by
  apply branch_checked idp000001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-223761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-225761639/2000000 : ℚ) by norm_num]
  exact coverp000001110001
theorem coverp00000111000 : Covers (-223761639/4000000 : ℚ) vp00000111000 := join_branches bp000001110000 bp000001110001
private noncomputable def vp0000011100_0 : Blocks := edgeBlocks% "full/vectors/0000011100-V-0000.bin"
private noncomputable def vp0000011100_1 : Blocks := edgeBlocks% "full/vectors/0000011100-V-0001.bin"
private noncomputable def vp0000011100_2 : Blocks := edgeBlocks% "full/vectors/0000011100-V-0002.bin"
private noncomputable def vp0000011100_3 : Blocks := edgeBlocks% "full/vectors/0000011100-V-0003.bin"
private noncomputable def vp0000011100_4 : Blocks := edgeBlocks% "full/vectors/0000011100-V-0004.bin"
noncomputable def vp0000011100 : Blocks := (Blocks.join (Blocks.join vp0000011100_0 vp0000011100_1) (Blocks.join vp0000011100_2 (Blocks.join vp0000011100_3 vp0000011100_4)))
private theorem bp00000111000 : Branch 0 (-223761639/8000000 : ℚ) vp0000011100 := by
  apply branch_left_normalized (c:=vp00000111000) (k:=0) (m:=285) (by decide +kernel)
  rw [show 2*(-223761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-223761639/4000000 : ℚ) by norm_num]
  exact coverp00000111000
private noncomputable def ep00000111001_0 : Blocks := edgeBlocks% "full/vectors/00000111001-E-0000.bin"
private noncomputable def ep00000111001_1 : Blocks := edgeBlocks% "full/vectors/00000111001-E-0001.bin"
private noncomputable def ep00000111001_2 : Blocks := edgeBlocks% "full/vectors/00000111001-E-0002.bin"
private noncomputable def ep00000111001_3 : Blocks := edgeBlocks% "full/vectors/00000111001-E-0003.bin"
private noncomputable def ep00000111001_4 : Blocks := edgeBlocks% "full/vectors/00000111001-E-0004.bin"
noncomputable def ep00000111001 : Blocks := (Blocks.join (Blocks.join ep00000111001_0 ep00000111001_1) (Blocks.join ep00000111001_2 (Blocks.join ep00000111001_3 ep00000111001_4)))
private theorem idp00000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011100.list =
    C ((2:ℤ)^570) * horner X vp00000111001.list + horner X ep00000111001.list := by
  exact edge_identity (B := (2:ℤ)^927) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000111001 : Branch 1 (-223761639/8000000 : ℚ) vp0000011100 := by
  apply branch_checked idp00000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-223761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-227761639/4000000 : ℚ) by norm_num]
  exact coverp00000111001
theorem coverp0000011100 : Covers (-223761639/8000000 : ℚ) vp0000011100 := join_branches bp00000111000 bp00000111001
private noncomputable def vp000001110_0 : Blocks := edgeBlocks% "full/vectors/000001110-V-0000.bin"
private noncomputable def vp000001110_1 : Blocks := edgeBlocks% "full/vectors/000001110-V-0001.bin"
private noncomputable def vp000001110_2 : Blocks := edgeBlocks% "full/vectors/000001110-V-0002.bin"
private noncomputable def vp000001110_3 : Blocks := edgeBlocks% "full/vectors/000001110-V-0003.bin"
private noncomputable def vp000001110_4 : Blocks := edgeBlocks% "full/vectors/000001110-V-0004.bin"
private noncomputable def vp000001110_5 : Blocks := edgeBlocks% "full/vectors/000001110-V-0005.bin"
private noncomputable def vp000001110_6 : Blocks := edgeBlocks% "full/vectors/000001110-V-0006.bin"
private noncomputable def vp000001110_7 : Blocks := edgeBlocks% "full/vectors/000001110-V-0007.bin"
private noncomputable def vp000001110_8 : Blocks := edgeBlocks% "full/vectors/000001110-V-0008.bin"
noncomputable def vp000001110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000001110_0 vp000001110_1) (Blocks.join vp000001110_2 vp000001110_3)) (Blocks.join (Blocks.join vp000001110_4 vp000001110_5) (Blocks.join vp000001110_6 (Blocks.join vp000001110_7 vp000001110_8))))
private theorem bp0000011100 : Branch 0 (-223761639/16000000 : ℚ) vp000001110 := by
  apply branch_left_normalized (c:=vp0000011100) (k:=0) (m:=545) (by decide +kernel)
  rw [show 2*(-223761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-223761639/8000000 : ℚ) by norm_num]
  exact coverp0000011100
private noncomputable def ep0000011101_0 : Blocks := edgeBlocks% "full/vectors/0000011101-E-0000.bin"
private noncomputable def ep0000011101_1 : Blocks := edgeBlocks% "full/vectors/0000011101-E-0001.bin"
private noncomputable def ep0000011101_2 : Blocks := edgeBlocks% "full/vectors/0000011101-E-0002.bin"
private noncomputable def ep0000011101_3 : Blocks := edgeBlocks% "full/vectors/0000011101-E-0003.bin"
private noncomputable def ep0000011101_4 : Blocks := edgeBlocks% "full/vectors/0000011101-E-0004.bin"
private noncomputable def ep0000011101_5 : Blocks := edgeBlocks% "full/vectors/0000011101-E-0005.bin"
private noncomputable def ep0000011101_6 : Blocks := edgeBlocks% "full/vectors/0000011101-E-0006.bin"
private noncomputable def ep0000011101_7 : Blocks := edgeBlocks% "full/vectors/0000011101-E-0007.bin"
private noncomputable def ep0000011101_8 : Blocks := edgeBlocks% "full/vectors/0000011101-E-0008.bin"
noncomputable def ep0000011101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000011101_0 ep0000011101_1) (Blocks.join ep0000011101_2 ep0000011101_3)) (Blocks.join (Blocks.join ep0000011101_4 ep0000011101_5) (Blocks.join ep0000011101_6 (Blocks.join ep0000011101_7 ep0000011101_8))))
private theorem idp0000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001110.list =
    C ((2:ℤ)^1106) * horner X vp0000011101.list + horner X ep0000011101.list := by
  exact edge_identity (B := (2:ℤ)^1717) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011101 : Branch 1 (-223761639/16000000 : ℚ) vp000001110 := by
  apply branch_checked idp0000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-223761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-231761639/8000000 : ℚ) by norm_num]
  exact coverp0000011101
theorem coverp000001110 : Covers (-223761639/16000000 : ℚ) vp000001110 := join_branches bp0000011100 bp0000011101
private noncomputable def vp00000111_0 : Blocks := edgeBlocks% "full/vectors/00000111-V-0000.bin"
private noncomputable def vp00000111_1 : Blocks := edgeBlocks% "full/vectors/00000111-V-0001.bin"
private noncomputable def vp00000111_2 : Blocks := edgeBlocks% "full/vectors/00000111-V-0002.bin"
private noncomputable def vp00000111_3 : Blocks := edgeBlocks% "full/vectors/00000111-V-0003.bin"
private noncomputable def vp00000111_4 : Blocks := edgeBlocks% "full/vectors/00000111-V-0004.bin"
private noncomputable def vp00000111_5 : Blocks := edgeBlocks% "full/vectors/00000111-V-0005.bin"
private noncomputable def vp00000111_6 : Blocks := edgeBlocks% "full/vectors/00000111-V-0006.bin"
private noncomputable def vp00000111_7 : Blocks := edgeBlocks% "full/vectors/00000111-V-0007.bin"
private noncomputable def vp00000111_8 : Blocks := edgeBlocks% "full/vectors/00000111-V-0008.bin"
private noncomputable def vp00000111_9 : Blocks := edgeBlocks% "full/vectors/00000111-V-0009.bin"
private noncomputable def vp00000111_10 : Blocks := edgeBlocks% "full/vectors/00000111-V-0010.bin"
private noncomputable def vp00000111_11 : Blocks := edgeBlocks% "full/vectors/00000111-V-0011.bin"
private noncomputable def vp00000111_12 : Blocks := edgeBlocks% "full/vectors/00000111-V-0012.bin"
private noncomputable def vp00000111_13 : Blocks := edgeBlocks% "full/vectors/00000111-V-0013.bin"
private noncomputable def vp00000111_14 : Blocks := edgeBlocks% "full/vectors/00000111-V-0014.bin"
private noncomputable def vp00000111_15 : Blocks := edgeBlocks% "full/vectors/00000111-V-0015.bin"
private noncomputable def vp00000111_16 : Blocks := edgeBlocks% "full/vectors/00000111-V-0016.bin"
noncomputable def vp00000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00000111_0 vp00000111_1) (Blocks.join vp00000111_2 vp00000111_3)) (Blocks.join (Blocks.join vp00000111_4 vp00000111_5) (Blocks.join vp00000111_6 vp00000111_7))) (Blocks.join (Blocks.join (Blocks.join vp00000111_8 vp00000111_9) (Blocks.join vp00000111_10 vp00000111_11)) (Blocks.join (Blocks.join vp00000111_12 vp00000111_13) (Blocks.join vp00000111_14 (Blocks.join vp00000111_15 vp00000111_16)))))
private theorem bp000001110 : Branch 0 (-223761639/32000000 : ℚ) vp00000111 := by
  apply branch_left_normalized (c:=vp000001110) (k:=0) (m:=1058) (by decide +kernel)
  rw [show 2*(-223761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-223761639/16000000 : ℚ) by norm_num]
  exact coverp000001110
private noncomputable def ep000001111_0 : Blocks := edgeBlocks% "full/vectors/000001111-E-0000.bin"
private noncomputable def ep000001111_1 : Blocks := edgeBlocks% "full/vectors/000001111-E-0001.bin"
private noncomputable def ep000001111_2 : Blocks := edgeBlocks% "full/vectors/000001111-E-0002.bin"
private noncomputable def ep000001111_3 : Blocks := edgeBlocks% "full/vectors/000001111-E-0003.bin"
private noncomputable def ep000001111_4 : Blocks := edgeBlocks% "full/vectors/000001111-E-0004.bin"
private noncomputable def ep000001111_5 : Blocks := edgeBlocks% "full/vectors/000001111-E-0005.bin"
private noncomputable def ep000001111_6 : Blocks := edgeBlocks% "full/vectors/000001111-E-0006.bin"
private noncomputable def ep000001111_7 : Blocks := edgeBlocks% "full/vectors/000001111-E-0007.bin"
private noncomputable def ep000001111_8 : Blocks := edgeBlocks% "full/vectors/000001111-E-0008.bin"
private noncomputable def ep000001111_9 : Blocks := edgeBlocks% "full/vectors/000001111-E-0009.bin"
private noncomputable def ep000001111_10 : Blocks := edgeBlocks% "full/vectors/000001111-E-0010.bin"
private noncomputable def ep000001111_11 : Blocks := edgeBlocks% "full/vectors/000001111-E-0011.bin"
private noncomputable def ep000001111_12 : Blocks := edgeBlocks% "full/vectors/000001111-E-0012.bin"
private noncomputable def ep000001111_13 : Blocks := edgeBlocks% "full/vectors/000001111-E-0013.bin"
private noncomputable def ep000001111_14 : Blocks := edgeBlocks% "full/vectors/000001111-E-0014.bin"
private noncomputable def ep000001111_15 : Blocks := edgeBlocks% "full/vectors/000001111-E-0015.bin"
private noncomputable def ep000001111_16 : Blocks := edgeBlocks% "full/vectors/000001111-E-0016.bin"
noncomputable def ep000001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep000001111_0 ep000001111_1) (Blocks.join ep000001111_2 ep000001111_3)) (Blocks.join (Blocks.join ep000001111_4 ep000001111_5) (Blocks.join ep000001111_6 ep000001111_7))) (Blocks.join (Blocks.join (Blocks.join ep000001111_8 ep000001111_9) (Blocks.join ep000001111_10 ep000001111_11)) (Blocks.join (Blocks.join ep000001111_12 ep000001111_13) (Blocks.join ep000001111_14 (Blocks.join ep000001111_15 ep000001111_16)))))
private theorem idp000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000111.list =
    C ((2:ℤ)^2153) * horner X vp000001111.list + horner X ep000001111.list := by
  exact edge_identity (B := (2:ℤ)^3267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001111 : Branch 1 (-223761639/32000000 : ℚ) vp00000111 := by
  apply branch_checked idp000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-223761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-239761639/16000000 : ℚ) by norm_num]
  exact coverp000001111
theorem coverp00000111 : Covers (-223761639/32000000 : ℚ) vp00000111 := join_branches bp000001110 bp000001111
end NextProof.EdgeFull

