import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00078

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0001101011111_0 : Blocks := edgeBlocks% "full/vectors/0001101011111-V-0000.bin"
noncomputable def vp0001101011111 : Blocks := vp0001101011111_0
theorem coverp0001101011111 : Covers (-862761639/1000000 : ℚ) vp0001101011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101011110_0 : Blocks := edgeBlocks% "full/vectors/0001101011110-V-0000.bin"
noncomputable def vp0001101011110 : Blocks := vp0001101011110_0
theorem coverp0001101011110 : Covers (-861761639/1000000 : ℚ) vp0001101011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000110101111_0 : Blocks := edgeBlocks% "full/vectors/000110101111-V-0000.bin"
noncomputable def vp000110101111 : Blocks := vp000110101111_0
private theorem bp0001101011110 : Branch 0 (-861761639/2000000 : ℚ) vp000110101111 := by
  apply branch_left_normalized (c:=vp0001101011110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-861761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-861761639/1000000 : ℚ) by norm_num]
  exact coverp0001101011110
private noncomputable def ep0001101011111_0 : Blocks := edgeBlocks% "full/vectors/0001101011111-E-0000.bin"
noncomputable def ep0001101011111 : Blocks := ep0001101011111_0
private theorem idp0001101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110101111.list =
    C ((2:ℤ)^95) * horner X vp0001101011111.list + horner X ep0001101011111.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101011111 : Branch 1 (-861761639/2000000 : ℚ) vp000110101111 := by
  apply branch_checked idp0001101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-861761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-862761639/1000000 : ℚ) by norm_num]
  exact coverp0001101011111
theorem coverp000110101111 : Covers (-861761639/2000000 : ℚ) vp000110101111 := join_branches bp0001101011110 bp0001101011111
private noncomputable def vp00011010111011_0 : Blocks := edgeBlocks% "full/vectors/00011010111011-V-0000.bin"
noncomputable def vp00011010111011 : Blocks := vp00011010111011_0
theorem coverp00011010111011 : Covers (-861261639/500000 : ℚ) vp00011010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011010111010_0 : Blocks := edgeBlocks% "full/vectors/00011010111010-V-0000.bin"
noncomputable def vp00011010111010 : Blocks := vp00011010111010_0
theorem coverp00011010111010 : Covers (-860761639/500000 : ℚ) vp00011010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101011101_0 : Blocks := edgeBlocks% "full/vectors/0001101011101-V-0000.bin"
noncomputable def vp0001101011101 : Blocks := vp0001101011101_0
private theorem bp00011010111010 : Branch 0 (-860761639/1000000 : ℚ) vp0001101011101 := by
  apply branch_left_normalized (c:=vp00011010111010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-860761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-860761639/500000 : ℚ) by norm_num]
  exact coverp00011010111010
private noncomputable def ep00011010111011_0 : Blocks := edgeBlocks% "full/vectors/00011010111011-E-0000.bin"
noncomputable def ep00011010111011 : Blocks := ep00011010111011_0
private theorem idp00011010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101011101.list =
    C ((2:ℤ)^57) * horner X vp00011010111011.list + horner X ep00011010111011.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011010111011 : Branch 1 (-860761639/1000000 : ℚ) vp0001101011101 := by
  apply branch_checked idp00011010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-860761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-861261639/500000 : ℚ) by norm_num]
  exact coverp00011010111011
theorem coverp0001101011101 : Covers (-860761639/1000000 : ℚ) vp0001101011101 := join_branches bp00011010111010 bp00011010111011
private noncomputable def vp00011010111001_0 : Blocks := edgeBlocks% "full/vectors/00011010111001-V-0000.bin"
noncomputable def vp00011010111001 : Blocks := vp00011010111001_0
theorem coverp00011010111001 : Covers (-860261639/500000 : ℚ) vp00011010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011010111000_0 : Blocks := edgeBlocks% "full/vectors/00011010111000-V-0000.bin"
noncomputable def vp00011010111000 : Blocks := vp00011010111000_0
theorem coverp00011010111000 : Covers (-859761639/500000 : ℚ) vp00011010111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101011100_0 : Blocks := edgeBlocks% "full/vectors/0001101011100-V-0000.bin"
noncomputable def vp0001101011100 : Blocks := vp0001101011100_0
private theorem bp00011010111000 : Branch 0 (-859761639/1000000 : ℚ) vp0001101011100 := by
  apply branch_left_normalized (c:=vp00011010111000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-859761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-859761639/500000 : ℚ) by norm_num]
  exact coverp00011010111000
private noncomputable def ep00011010111001_0 : Blocks := edgeBlocks% "full/vectors/00011010111001-E-0000.bin"
noncomputable def ep00011010111001 : Blocks := ep00011010111001_0
private theorem idp00011010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101011100.list =
    C ((2:ℤ)^56) * horner X vp00011010111001.list + horner X ep00011010111001.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011010111001 : Branch 1 (-859761639/1000000 : ℚ) vp0001101011100 := by
  apply branch_checked idp00011010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-859761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-860261639/500000 : ℚ) by norm_num]
  exact coverp00011010111001
theorem coverp0001101011100 : Covers (-859761639/1000000 : ℚ) vp0001101011100 := join_branches bp00011010111000 bp00011010111001
private noncomputable def vp000110101110_0 : Blocks := edgeBlocks% "full/vectors/000110101110-V-0000.bin"
noncomputable def vp000110101110 : Blocks := vp000110101110_0
private theorem bp0001101011100 : Branch 0 (-859761639/2000000 : ℚ) vp000110101110 := by
  apply branch_left_normalized (c:=vp0001101011100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-859761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-859761639/1000000 : ℚ) by norm_num]
  exact coverp0001101011100
private noncomputable def ep0001101011101_0 : Blocks := edgeBlocks% "full/vectors/0001101011101-E-0000.bin"
noncomputable def ep0001101011101 : Blocks := ep0001101011101_0
private theorem idp0001101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110101110.list =
    C ((2:ℤ)^95) * horner X vp0001101011101.list + horner X ep0001101011101.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101011101 : Branch 1 (-859761639/2000000 : ℚ) vp000110101110 := by
  apply branch_checked idp0001101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-859761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-860761639/1000000 : ℚ) by norm_num]
  exact coverp0001101011101
theorem coverp000110101110 : Covers (-859761639/2000000 : ℚ) vp000110101110 := join_branches bp0001101011100 bp0001101011101
private noncomputable def vp00011010111_0 : Blocks := edgeBlocks% "full/vectors/00011010111-V-0000.bin"
private noncomputable def vp00011010111_1 : Blocks := edgeBlocks% "full/vectors/00011010111-V-0001.bin"
noncomputable def vp00011010111 : Blocks := (Blocks.join vp00011010111_0 vp00011010111_1)
private theorem bp000110101110 : Branch 0 (-859761639/4000000 : ℚ) vp00011010111 := by
  apply branch_left_normalized (c:=vp000110101110) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-859761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-859761639/2000000 : ℚ) by norm_num]
  exact coverp000110101110
private noncomputable def ep000110101111_0 : Blocks := edgeBlocks% "full/vectors/000110101111-E-0000.bin"
private noncomputable def ep000110101111_1 : Blocks := edgeBlocks% "full/vectors/000110101111-E-0001.bin"
noncomputable def ep000110101111 : Blocks := (Blocks.join ep000110101111_0 ep000110101111_1)
private theorem idp000110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011010111.list =
    C ((2:ℤ)^169) * horner X vp000110101111.list + horner X ep000110101111.list := by
  exact edge_identity (B := (2:ℤ)^330) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110101111 : Branch 1 (-859761639/4000000 : ℚ) vp00011010111 := by
  apply branch_checked idp000110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-859761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-861761639/2000000 : ℚ) by norm_num]
  exact coverp000110101111
theorem coverp00011010111 : Covers (-859761639/4000000 : ℚ) vp00011010111 := join_branches bp000110101110 bp000110101111
private noncomputable def vp00011010110111_0 : Blocks := edgeBlocks% "full/vectors/00011010110111-V-0000.bin"
noncomputable def vp00011010110111 : Blocks := vp00011010110111_0
theorem coverp00011010110111 : Covers (-859261639/500000 : ℚ) vp00011010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011010110110_0 : Blocks := edgeBlocks% "full/vectors/00011010110110-V-0000.bin"
noncomputable def vp00011010110110 : Blocks := vp00011010110110_0
theorem coverp00011010110110 : Covers (-858761639/500000 : ℚ) vp00011010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101011011_0 : Blocks := edgeBlocks% "full/vectors/0001101011011-V-0000.bin"
noncomputable def vp0001101011011 : Blocks := vp0001101011011_0
private theorem bp00011010110110 : Branch 0 (-858761639/1000000 : ℚ) vp0001101011011 := by
  apply branch_left_normalized (c:=vp00011010110110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-858761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-858761639/500000 : ℚ) by norm_num]
  exact coverp00011010110110
private noncomputable def ep00011010110111_0 : Blocks := edgeBlocks% "full/vectors/00011010110111-E-0000.bin"
noncomputable def ep00011010110111 : Blocks := ep00011010110111_0
private theorem idp00011010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101011011.list =
    C ((2:ℤ)^56) * horner X vp00011010110111.list + horner X ep00011010110111.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011010110111 : Branch 1 (-858761639/1000000 : ℚ) vp0001101011011 := by
  apply branch_checked idp00011010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-858761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-859261639/500000 : ℚ) by norm_num]
  exact coverp00011010110111
theorem coverp0001101011011 : Covers (-858761639/1000000 : ℚ) vp0001101011011 := join_branches bp00011010110110 bp00011010110111
private noncomputable def vp00011010110101_0 : Blocks := edgeBlocks% "full/vectors/00011010110101-V-0000.bin"
noncomputable def vp00011010110101 : Blocks := vp00011010110101_0
theorem coverp00011010110101 : Covers (-858261639/500000 : ℚ) vp00011010110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011010110100_0 : Blocks := edgeBlocks% "full/vectors/00011010110100-V-0000.bin"
noncomputable def vp00011010110100 : Blocks := vp00011010110100_0
theorem coverp00011010110100 : Covers (-857761639/500000 : ℚ) vp00011010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101011010_0 : Blocks := edgeBlocks% "full/vectors/0001101011010-V-0000.bin"
noncomputable def vp0001101011010 : Blocks := vp0001101011010_0
private theorem bp00011010110100 : Branch 0 (-857761639/1000000 : ℚ) vp0001101011010 := by
  apply branch_left_normalized (c:=vp00011010110100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-857761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-857761639/500000 : ℚ) by norm_num]
  exact coverp00011010110100
private noncomputable def ep00011010110101_0 : Blocks := edgeBlocks% "full/vectors/00011010110101-E-0000.bin"
noncomputable def ep00011010110101 : Blocks := ep00011010110101_0
private theorem idp00011010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101011010.list =
    C ((2:ℤ)^55) * horner X vp00011010110101.list + horner X ep00011010110101.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011010110101 : Branch 1 (-857761639/1000000 : ℚ) vp0001101011010 := by
  apply branch_checked idp00011010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-857761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-858261639/500000 : ℚ) by norm_num]
  exact coverp00011010110101
theorem coverp0001101011010 : Covers (-857761639/1000000 : ℚ) vp0001101011010 := join_branches bp00011010110100 bp00011010110101
private noncomputable def vp000110101101_0 : Blocks := edgeBlocks% "full/vectors/000110101101-V-0000.bin"
noncomputable def vp000110101101 : Blocks := vp000110101101_0
private theorem bp0001101011010 : Branch 0 (-857761639/2000000 : ℚ) vp000110101101 := by
  apply branch_left_normalized (c:=vp0001101011010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-857761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-857761639/1000000 : ℚ) by norm_num]
  exact coverp0001101011010
private noncomputable def ep0001101011011_0 : Blocks := edgeBlocks% "full/vectors/0001101011011-E-0000.bin"
noncomputable def ep0001101011011 : Blocks := ep0001101011011_0
private theorem idp0001101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110101101.list =
    C ((2:ℤ)^93) * horner X vp0001101011011.list + horner X ep0001101011011.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101011011 : Branch 1 (-857761639/2000000 : ℚ) vp000110101101 := by
  apply branch_checked idp0001101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-857761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-858761639/1000000 : ℚ) by norm_num]
  exact coverp0001101011011
theorem coverp000110101101 : Covers (-857761639/2000000 : ℚ) vp000110101101 := join_branches bp0001101011010 bp0001101011011
private noncomputable def vp0001101011001_0 : Blocks := edgeBlocks% "full/vectors/0001101011001-V-0000.bin"
noncomputable def vp0001101011001 : Blocks := vp0001101011001_0
theorem coverp0001101011001 : Covers (-856761639/1000000 : ℚ) vp0001101011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101011000_0 : Blocks := edgeBlocks% "full/vectors/0001101011000-V-0000.bin"
noncomputable def vp0001101011000 : Blocks := vp0001101011000_0
theorem coverp0001101011000 : Covers (-855761639/1000000 : ℚ) vp0001101011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000110101100_0 : Blocks := edgeBlocks% "full/vectors/000110101100-V-0000.bin"
noncomputable def vp000110101100 : Blocks := vp000110101100_0
private theorem bp0001101011000 : Branch 0 (-855761639/2000000 : ℚ) vp000110101100 := by
  apply branch_left_normalized (c:=vp0001101011000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-855761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-855761639/1000000 : ℚ) by norm_num]
  exact coverp0001101011000
private noncomputable def ep0001101011001_0 : Blocks := edgeBlocks% "full/vectors/0001101011001-E-0000.bin"
noncomputable def ep0001101011001 : Blocks := ep0001101011001_0
private theorem idp0001101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110101100.list =
    C ((2:ℤ)^94) * horner X vp0001101011001.list + horner X ep0001101011001.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101011001 : Branch 1 (-855761639/2000000 : ℚ) vp000110101100 := by
  apply branch_checked idp0001101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-855761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-856761639/1000000 : ℚ) by norm_num]
  exact coverp0001101011001
theorem coverp000110101100 : Covers (-855761639/2000000 : ℚ) vp000110101100 := join_branches bp0001101011000 bp0001101011001
private noncomputable def vp00011010110_0 : Blocks := edgeBlocks% "full/vectors/00011010110-V-0000.bin"
private noncomputable def vp00011010110_1 : Blocks := edgeBlocks% "full/vectors/00011010110-V-0001.bin"
noncomputable def vp00011010110 : Blocks := (Blocks.join vp00011010110_0 vp00011010110_1)
private theorem bp000110101100 : Branch 0 (-855761639/4000000 : ℚ) vp00011010110 := by
  apply branch_left_normalized (c:=vp000110101100) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-855761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-855761639/2000000 : ℚ) by norm_num]
  exact coverp000110101100
private noncomputable def ep000110101101_0 : Blocks := edgeBlocks% "full/vectors/000110101101-E-0000.bin"
private noncomputable def ep000110101101_1 : Blocks := edgeBlocks% "full/vectors/000110101101-E-0001.bin"
noncomputable def ep000110101101 : Blocks := (Blocks.join ep000110101101_0 ep000110101101_1)
private theorem idp000110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011010110.list =
    C ((2:ℤ)^167) * horner X vp000110101101.list + horner X ep000110101101.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110101101 : Branch 1 (-855761639/4000000 : ℚ) vp00011010110 := by
  apply branch_checked idp000110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-855761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-857761639/2000000 : ℚ) by norm_num]
  exact coverp000110101101
theorem coverp00011010110 : Covers (-855761639/4000000 : ℚ) vp00011010110 := join_branches bp000110101100 bp000110101101
private noncomputable def vp0001101011_0 : Blocks := edgeBlocks% "full/vectors/0001101011-V-0000.bin"
private noncomputable def vp0001101011_1 : Blocks := edgeBlocks% "full/vectors/0001101011-V-0001.bin"
private noncomputable def vp0001101011_2 : Blocks := edgeBlocks% "full/vectors/0001101011-V-0002.bin"
noncomputable def vp0001101011 : Blocks := (Blocks.join vp0001101011_0 (Blocks.join vp0001101011_1 vp0001101011_2))
private theorem bp00011010110 : Branch 0 (-855761639/8000000 : ℚ) vp0001101011 := by
  apply branch_left_normalized (c:=vp00011010110) (k:=0) (m:=155) (by decide +kernel)
  rw [show 2*(-855761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-855761639/4000000 : ℚ) by norm_num]
  exact coverp00011010110
private noncomputable def ep00011010111_0 : Blocks := edgeBlocks% "full/vectors/00011010111-E-0000.bin"
private noncomputable def ep00011010111_1 : Blocks := edgeBlocks% "full/vectors/00011010111-E-0001.bin"
private noncomputable def ep00011010111_2 : Blocks := edgeBlocks% "full/vectors/00011010111-E-0002.bin"
noncomputable def ep00011010111 : Blocks := (Blocks.join ep00011010111_0 (Blocks.join ep00011010111_1 ep00011010111_2))
private theorem idp00011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101011.list =
    C ((2:ℤ)^310) * horner X vp00011010111.list + horner X ep00011010111.list := by
  exact edge_identity (B := (2:ℤ)^531) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011010111 : Branch 1 (-855761639/8000000 : ℚ) vp0001101011 := by
  apply branch_checked idp00011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-855761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-859761639/4000000 : ℚ) by norm_num]
  exact coverp00011010111
theorem coverp0001101011 : Covers (-855761639/8000000 : ℚ) vp0001101011 := join_branches bp00011010110 bp00011010111
private noncomputable def vp0001101010111_0 : Blocks := edgeBlocks% "full/vectors/0001101010111-V-0000.bin"
noncomputable def vp0001101010111 : Blocks := vp0001101010111_0
theorem coverp0001101010111 : Covers (-854761639/1000000 : ℚ) vp0001101010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101010110_0 : Blocks := edgeBlocks% "full/vectors/0001101010110-V-0000.bin"
noncomputable def vp0001101010110 : Blocks := vp0001101010110_0
theorem coverp0001101010110 : Covers (-853761639/1000000 : ℚ) vp0001101010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000110101011_0 : Blocks := edgeBlocks% "full/vectors/000110101011-V-0000.bin"
noncomputable def vp000110101011 : Blocks := vp000110101011_0
private theorem bp0001101010110 : Branch 0 (-853761639/2000000 : ℚ) vp000110101011 := by
  apply branch_left_normalized (c:=vp0001101010110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-853761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-853761639/1000000 : ℚ) by norm_num]
  exact coverp0001101010110
private noncomputable def ep0001101010111_0 : Blocks := edgeBlocks% "full/vectors/0001101010111-E-0000.bin"
noncomputable def ep0001101010111 : Blocks := ep0001101010111_0
private theorem idp0001101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110101011.list =
    C ((2:ℤ)^94) * horner X vp0001101010111.list + horner X ep0001101010111.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101010111 : Branch 1 (-853761639/2000000 : ℚ) vp000110101011 := by
  apply branch_checked idp0001101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-853761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-854761639/1000000 : ℚ) by norm_num]
  exact coverp0001101010111
theorem coverp000110101011 : Covers (-853761639/2000000 : ℚ) vp000110101011 := join_branches bp0001101010110 bp0001101010111
private noncomputable def vp0001101010101_0 : Blocks := edgeBlocks% "full/vectors/0001101010101-V-0000.bin"
noncomputable def vp0001101010101 : Blocks := vp0001101010101_0
theorem coverp0001101010101 : Covers (-852761639/1000000 : ℚ) vp0001101010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101010100_0 : Blocks := edgeBlocks% "full/vectors/0001101010100-V-0000.bin"
noncomputable def vp0001101010100 : Blocks := vp0001101010100_0
theorem coverp0001101010100 : Covers (-851761639/1000000 : ℚ) vp0001101010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000110101010_0 : Blocks := edgeBlocks% "full/vectors/000110101010-V-0000.bin"
noncomputable def vp000110101010 : Blocks := vp000110101010_0
private theorem bp0001101010100 : Branch 0 (-851761639/2000000 : ℚ) vp000110101010 := by
  apply branch_left_normalized (c:=vp0001101010100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-851761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-851761639/1000000 : ℚ) by norm_num]
  exact coverp0001101010100
private noncomputable def ep0001101010101_0 : Blocks := edgeBlocks% "full/vectors/0001101010101-E-0000.bin"
noncomputable def ep0001101010101 : Blocks := ep0001101010101_0
private theorem idp0001101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110101010.list =
    C ((2:ℤ)^92) * horner X vp0001101010101.list + horner X ep0001101010101.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101010101 : Branch 1 (-851761639/2000000 : ℚ) vp000110101010 := by
  apply branch_checked idp0001101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-851761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-852761639/1000000 : ℚ) by norm_num]
  exact coverp0001101010101
theorem coverp000110101010 : Covers (-851761639/2000000 : ℚ) vp000110101010 := join_branches bp0001101010100 bp0001101010101
private noncomputable def vp00011010101_0 : Blocks := edgeBlocks% "full/vectors/00011010101-V-0000.bin"
private noncomputable def vp00011010101_1 : Blocks := edgeBlocks% "full/vectors/00011010101-V-0001.bin"
noncomputable def vp00011010101 : Blocks := (Blocks.join vp00011010101_0 vp00011010101_1)
private theorem bp000110101010 : Branch 0 (-851761639/4000000 : ℚ) vp00011010101 := by
  apply branch_left_normalized (c:=vp000110101010) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-851761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-851761639/2000000 : ℚ) by norm_num]
  exact coverp000110101010
private noncomputable def ep000110101011_0 : Blocks := edgeBlocks% "full/vectors/000110101011-E-0000.bin"
private noncomputable def ep000110101011_1 : Blocks := edgeBlocks% "full/vectors/000110101011-E-0001.bin"
noncomputable def ep000110101011 : Blocks := (Blocks.join ep000110101011_0 ep000110101011_1)
private theorem idp000110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011010101.list =
    C ((2:ℤ)^165) * horner X vp000110101011.list + horner X ep000110101011.list := by
  exact edge_identity (B := (2:ℤ)^324) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110101011 : Branch 1 (-851761639/4000000 : ℚ) vp00011010101 := by
  apply branch_checked idp000110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-851761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-853761639/2000000 : ℚ) by norm_num]
  exact coverp000110101011
theorem coverp00011010101 : Covers (-851761639/4000000 : ℚ) vp00011010101 := join_branches bp000110101010 bp000110101011
private noncomputable def vp0001101010011_0 : Blocks := edgeBlocks% "full/vectors/0001101010011-V-0000.bin"
noncomputable def vp0001101010011 : Blocks := vp0001101010011_0
theorem coverp0001101010011 : Covers (-850761639/1000000 : ℚ) vp0001101010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101010010_0 : Blocks := edgeBlocks% "full/vectors/0001101010010-V-0000.bin"
noncomputable def vp0001101010010 : Blocks := vp0001101010010_0
theorem coverp0001101010010 : Covers (-849761639/1000000 : ℚ) vp0001101010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000110101001_0 : Blocks := edgeBlocks% "full/vectors/000110101001-V-0000.bin"
noncomputable def vp000110101001 : Blocks := vp000110101001_0
private theorem bp0001101010010 : Branch 0 (-849761639/2000000 : ℚ) vp000110101001 := by
  apply branch_left_normalized (c:=vp0001101010010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-849761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-849761639/1000000 : ℚ) by norm_num]
  exact coverp0001101010010
private noncomputable def ep0001101010011_0 : Blocks := edgeBlocks% "full/vectors/0001101010011-E-0000.bin"
noncomputable def ep0001101010011 : Blocks := ep0001101010011_0
private theorem idp0001101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110101001.list =
    C ((2:ℤ)^90) * horner X vp0001101010011.list + horner X ep0001101010011.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101010011 : Branch 1 (-849761639/2000000 : ℚ) vp000110101001 := by
  apply branch_checked idp0001101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-849761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-850761639/1000000 : ℚ) by norm_num]
  exact coverp0001101010011
theorem coverp000110101001 : Covers (-849761639/2000000 : ℚ) vp000110101001 := join_branches bp0001101010010 bp0001101010011
private noncomputable def vp0001101010001_0 : Blocks := edgeBlocks% "full/vectors/0001101010001-V-0000.bin"
noncomputable def vp0001101010001 : Blocks := vp0001101010001_0
theorem coverp0001101010001 : Covers (-848761639/1000000 : ℚ) vp0001101010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101010000_0 : Blocks := edgeBlocks% "full/vectors/0001101010000-V-0000.bin"
noncomputable def vp0001101010000 : Blocks := vp0001101010000_0
theorem coverp0001101010000 : Covers (-847761639/1000000 : ℚ) vp0001101010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000110101000_0 : Blocks := edgeBlocks% "full/vectors/000110101000-V-0000.bin"
noncomputable def vp000110101000 : Blocks := vp000110101000_0
private theorem bp0001101010000 : Branch 0 (-847761639/2000000 : ℚ) vp000110101000 := by
  apply branch_left_normalized (c:=vp0001101010000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-847761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-847761639/1000000 : ℚ) by norm_num]
  exact coverp0001101010000
private noncomputable def ep0001101010001_0 : Blocks := edgeBlocks% "full/vectors/0001101010001-E-0000.bin"
noncomputable def ep0001101010001 : Blocks := ep0001101010001_0
private theorem idp0001101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110101000.list =
    C ((2:ℤ)^90) * horner X vp0001101010001.list + horner X ep0001101010001.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101010001 : Branch 1 (-847761639/2000000 : ℚ) vp000110101000 := by
  apply branch_checked idp0001101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-847761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-848761639/1000000 : ℚ) by norm_num]
  exact coverp0001101010001
theorem coverp000110101000 : Covers (-847761639/2000000 : ℚ) vp000110101000 := join_branches bp0001101010000 bp0001101010001
private noncomputable def vp00011010100_0 : Blocks := edgeBlocks% "full/vectors/00011010100-V-0000.bin"
private noncomputable def vp00011010100_1 : Blocks := edgeBlocks% "full/vectors/00011010100-V-0001.bin"
noncomputable def vp00011010100 : Blocks := (Blocks.join vp00011010100_0 vp00011010100_1)
private theorem bp000110101000 : Branch 0 (-847761639/4000000 : ℚ) vp00011010100 := by
  apply branch_left_normalized (c:=vp000110101000) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-847761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-847761639/2000000 : ℚ) by norm_num]
  exact coverp000110101000
private noncomputable def ep000110101001_0 : Blocks := edgeBlocks% "full/vectors/000110101001-E-0000.bin"
private noncomputable def ep000110101001_1 : Blocks := edgeBlocks% "full/vectors/000110101001-E-0001.bin"
noncomputable def ep000110101001 : Blocks := (Blocks.join ep000110101001_0 ep000110101001_1)
private theorem idp000110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011010100.list =
    C ((2:ℤ)^163) * horner X vp000110101001.list + horner X ep000110101001.list := by
  exact edge_identity (B := (2:ℤ)^318) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110101001 : Branch 1 (-847761639/4000000 : ℚ) vp00011010100 := by
  apply branch_checked idp000110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-847761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-849761639/2000000 : ℚ) by norm_num]
  exact coverp000110101001
theorem coverp00011010100 : Covers (-847761639/4000000 : ℚ) vp00011010100 := join_branches bp000110101000 bp000110101001
private noncomputable def vp0001101010_0 : Blocks := edgeBlocks% "full/vectors/0001101010-V-0000.bin"
private noncomputable def vp0001101010_1 : Blocks := edgeBlocks% "full/vectors/0001101010-V-0001.bin"
private noncomputable def vp0001101010_2 : Blocks := edgeBlocks% "full/vectors/0001101010-V-0002.bin"
noncomputable def vp0001101010 : Blocks := (Blocks.join vp0001101010_0 (Blocks.join vp0001101010_1 vp0001101010_2))
private theorem bp00011010100 : Branch 0 (-847761639/8000000 : ℚ) vp0001101010 := by
  apply branch_left_normalized (c:=vp00011010100) (k:=0) (m:=152) (by decide +kernel)
  rw [show 2*(-847761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-847761639/4000000 : ℚ) by norm_num]
  exact coverp00011010100
private noncomputable def ep00011010101_0 : Blocks := edgeBlocks% "full/vectors/00011010101-E-0000.bin"
private noncomputable def ep00011010101_1 : Blocks := edgeBlocks% "full/vectors/00011010101-E-0001.bin"
private noncomputable def ep00011010101_2 : Blocks := edgeBlocks% "full/vectors/00011010101-E-0002.bin"
noncomputable def ep00011010101 : Blocks := (Blocks.join ep00011010101_0 (Blocks.join ep00011010101_1 ep00011010101_2))
private theorem idp00011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101010.list =
    C ((2:ℤ)^307) * horner X vp00011010101.list + horner X ep00011010101.list := by
  exact edge_identity (B := (2:ℤ)^524) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011010101 : Branch 1 (-847761639/8000000 : ℚ) vp0001101010 := by
  apply branch_checked idp00011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-847761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-851761639/4000000 : ℚ) by norm_num]
  exact coverp00011010101
theorem coverp0001101010 : Covers (-847761639/8000000 : ℚ) vp0001101010 := join_branches bp00011010100 bp00011010101
private noncomputable def vp000110101_0 : Blocks := edgeBlocks% "full/vectors/000110101-V-0000.bin"
private noncomputable def vp000110101_1 : Blocks := edgeBlocks% "full/vectors/000110101-V-0001.bin"
private noncomputable def vp000110101_2 : Blocks := edgeBlocks% "full/vectors/000110101-V-0002.bin"
private noncomputable def vp000110101_3 : Blocks := edgeBlocks% "full/vectors/000110101-V-0003.bin"
private noncomputable def vp000110101_4 : Blocks := edgeBlocks% "full/vectors/000110101-V-0004.bin"
noncomputable def vp000110101 : Blocks := (Blocks.join (Blocks.join vp000110101_0 vp000110101_1) (Blocks.join vp000110101_2 (Blocks.join vp000110101_3 vp000110101_4)))
private theorem bp0001101010 : Branch 0 (-847761639/16000000 : ℚ) vp000110101 := by
  apply branch_left_normalized (c:=vp0001101010) (k:=0) (m:=287) (by decide +kernel)
  rw [show 2*(-847761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-847761639/8000000 : ℚ) by norm_num]
  exact coverp0001101010
private noncomputable def ep0001101011_0 : Blocks := edgeBlocks% "full/vectors/0001101011-E-0000.bin"
private noncomputable def ep0001101011_1 : Blocks := edgeBlocks% "full/vectors/0001101011-E-0001.bin"
private noncomputable def ep0001101011_2 : Blocks := edgeBlocks% "full/vectors/0001101011-E-0002.bin"
private noncomputable def ep0001101011_3 : Blocks := edgeBlocks% "full/vectors/0001101011-E-0003.bin"
private noncomputable def ep0001101011_4 : Blocks := edgeBlocks% "full/vectors/0001101011-E-0004.bin"
noncomputable def ep0001101011 : Blocks := (Blocks.join (Blocks.join ep0001101011_0 ep0001101011_1) (Blocks.join ep0001101011_2 (Blocks.join ep0001101011_3 ep0001101011_4)))
private theorem idp0001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110101.list =
    C ((2:ℤ)^595) * horner X vp0001101011.list + horner X ep0001101011.list := by
  exact edge_identity (B := (2:ℤ)^934) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101011 : Branch 1 (-847761639/16000000 : ℚ) vp000110101 := by
  apply branch_checked idp0001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-847761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-855761639/8000000 : ℚ) by norm_num]
  exact coverp0001101011
theorem coverp000110101 : Covers (-847761639/16000000 : ℚ) vp000110101 := join_branches bp0001101010 bp0001101011
private noncomputable def vp0001101001111_0 : Blocks := edgeBlocks% "full/vectors/0001101001111-V-0000.bin"
noncomputable def vp0001101001111 : Blocks := vp0001101001111_0
theorem coverp0001101001111 : Covers (-846761639/1000000 : ℚ) vp0001101001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101001110_0 : Blocks := edgeBlocks% "full/vectors/0001101001110-V-0000.bin"
noncomputable def vp0001101001110 : Blocks := vp0001101001110_0
theorem coverp0001101001110 : Covers (-845761639/1000000 : ℚ) vp0001101001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000110100111_0 : Blocks := edgeBlocks% "full/vectors/000110100111-V-0000.bin"
noncomputable def vp000110100111 : Blocks := vp000110100111_0
private theorem bp0001101001110 : Branch 0 (-845761639/2000000 : ℚ) vp000110100111 := by
  apply branch_left_normalized (c:=vp0001101001110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-845761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-845761639/1000000 : ℚ) by norm_num]
  exact coverp0001101001110
private noncomputable def ep0001101001111_0 : Blocks := edgeBlocks% "full/vectors/0001101001111-E-0000.bin"
noncomputable def ep0001101001111 : Blocks := ep0001101001111_0
private theorem idp0001101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110100111.list =
    C ((2:ℤ)^89) * horner X vp0001101001111.list + horner X ep0001101001111.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101001111 : Branch 1 (-845761639/2000000 : ℚ) vp000110100111 := by
  apply branch_checked idp0001101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-845761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-846761639/1000000 : ℚ) by norm_num]
  exact coverp0001101001111
theorem coverp000110100111 : Covers (-845761639/2000000 : ℚ) vp000110100111 := join_branches bp0001101001110 bp0001101001111
private noncomputable def vp0001101001101_0 : Blocks := edgeBlocks% "full/vectors/0001101001101-V-0000.bin"
noncomputable def vp0001101001101 : Blocks := vp0001101001101_0
theorem coverp0001101001101 : Covers (-844761639/1000000 : ℚ) vp0001101001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101001100_0 : Blocks := edgeBlocks% "full/vectors/0001101001100-V-0000.bin"
noncomputable def vp0001101001100 : Blocks := vp0001101001100_0
theorem coverp0001101001100 : Covers (-843761639/1000000 : ℚ) vp0001101001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000110100110_0 : Blocks := edgeBlocks% "full/vectors/000110100110-V-0000.bin"
noncomputable def vp000110100110 : Blocks := vp000110100110_0
private theorem bp0001101001100 : Branch 0 (-843761639/2000000 : ℚ) vp000110100110 := by
  apply branch_left_normalized (c:=vp0001101001100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-843761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-843761639/1000000 : ℚ) by norm_num]
  exact coverp0001101001100
private noncomputable def ep0001101001101_0 : Blocks := edgeBlocks% "full/vectors/0001101001101-E-0000.bin"
noncomputable def ep0001101001101 : Blocks := ep0001101001101_0
private theorem idp0001101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110100110.list =
    C ((2:ℤ)^89) * horner X vp0001101001101.list + horner X ep0001101001101.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101001101 : Branch 1 (-843761639/2000000 : ℚ) vp000110100110 := by
  apply branch_checked idp0001101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-843761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-844761639/1000000 : ℚ) by norm_num]
  exact coverp0001101001101
theorem coverp000110100110 : Covers (-843761639/2000000 : ℚ) vp000110100110 := join_branches bp0001101001100 bp0001101001101
private noncomputable def vp00011010011_0 : Blocks := edgeBlocks% "full/vectors/00011010011-V-0000.bin"
private noncomputable def vp00011010011_1 : Blocks := edgeBlocks% "full/vectors/00011010011-V-0001.bin"
noncomputable def vp00011010011 : Blocks := (Blocks.join vp00011010011_0 vp00011010011_1)
private theorem bp000110100110 : Branch 0 (-843761639/4000000 : ℚ) vp00011010011 := by
  apply branch_left_normalized (c:=vp000110100110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-843761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-843761639/2000000 : ℚ) by norm_num]
  exact coverp000110100110
private noncomputable def ep000110100111_0 : Blocks := edgeBlocks% "full/vectors/000110100111-E-0000.bin"
private noncomputable def ep000110100111_1 : Blocks := edgeBlocks% "full/vectors/000110100111-E-0001.bin"
noncomputable def ep000110100111 : Blocks := (Blocks.join ep000110100111_0 ep000110100111_1)
private theorem idp000110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011010011.list =
    C ((2:ℤ)^163) * horner X vp000110100111.list + horner X ep000110100111.list := by
  exact edge_identity (B := (2:ℤ)^315) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110100111 : Branch 1 (-843761639/4000000 : ℚ) vp00011010011 := by
  apply branch_checked idp000110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-843761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-845761639/2000000 : ℚ) by norm_num]
  exact coverp000110100111
theorem coverp00011010011 : Covers (-843761639/4000000 : ℚ) vp00011010011 := join_branches bp000110100110 bp000110100111
private noncomputable def vp0001101001011_0 : Blocks := edgeBlocks% "full/vectors/0001101001011-V-0000.bin"
noncomputable def vp0001101001011 : Blocks := vp0001101001011_0
theorem coverp0001101001011 : Covers (-842761639/1000000 : ℚ) vp0001101001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101001010_0 : Blocks := edgeBlocks% "full/vectors/0001101001010-V-0000.bin"
noncomputable def vp0001101001010 : Blocks := vp0001101001010_0
theorem coverp0001101001010 : Covers (-841761639/1000000 : ℚ) vp0001101001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000110100101_0 : Blocks := edgeBlocks% "full/vectors/000110100101-V-0000.bin"
noncomputable def vp000110100101 : Blocks := vp000110100101_0
private theorem bp0001101001010 : Branch 0 (-841761639/2000000 : ℚ) vp000110100101 := by
  apply branch_left_normalized (c:=vp0001101001010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-841761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-841761639/1000000 : ℚ) by norm_num]
  exact coverp0001101001010
private noncomputable def ep0001101001011_0 : Blocks := edgeBlocks% "full/vectors/0001101001011-E-0000.bin"
noncomputable def ep0001101001011 : Blocks := ep0001101001011_0
private theorem idp0001101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110100101.list =
    C ((2:ℤ)^90) * horner X vp0001101001011.list + horner X ep0001101001011.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101001011 : Branch 1 (-841761639/2000000 : ℚ) vp000110100101 := by
  apply branch_checked idp0001101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-841761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-842761639/1000000 : ℚ) by norm_num]
  exact coverp0001101001011
theorem coverp000110100101 : Covers (-841761639/2000000 : ℚ) vp000110100101 := join_branches bp0001101001010 bp0001101001011
private noncomputable def vp0001101001001_0 : Blocks := edgeBlocks% "full/vectors/0001101001001-V-0000.bin"
noncomputable def vp0001101001001 : Blocks := vp0001101001001_0
theorem coverp0001101001001 : Covers (-840761639/1000000 : ℚ) vp0001101001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101001000_0 : Blocks := edgeBlocks% "full/vectors/0001101001000-V-0000.bin"
noncomputable def vp0001101001000 : Blocks := vp0001101001000_0
theorem coverp0001101001000 : Covers (-839761639/1000000 : ℚ) vp0001101001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000110100100_0 : Blocks := edgeBlocks% "full/vectors/000110100100-V-0000.bin"
noncomputable def vp000110100100 : Blocks := vp000110100100_0
private theorem bp0001101001000 : Branch 0 (-839761639/2000000 : ℚ) vp000110100100 := by
  apply branch_left_normalized (c:=vp0001101001000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-839761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-839761639/1000000 : ℚ) by norm_num]
  exact coverp0001101001000
private noncomputable def ep0001101001001_0 : Blocks := edgeBlocks% "full/vectors/0001101001001-E-0000.bin"
noncomputable def ep0001101001001 : Blocks := ep0001101001001_0
private theorem idp0001101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110100100.list =
    C ((2:ℤ)^89) * horner X vp0001101001001.list + horner X ep0001101001001.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101001001 : Branch 1 (-839761639/2000000 : ℚ) vp000110100100 := by
  apply branch_checked idp0001101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-839761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-840761639/1000000 : ℚ) by norm_num]
  exact coverp0001101001001
theorem coverp000110100100 : Covers (-839761639/2000000 : ℚ) vp000110100100 := join_branches bp0001101001000 bp0001101001001
private noncomputable def vp00011010010_0 : Blocks := edgeBlocks% "full/vectors/00011010010-V-0000.bin"
private noncomputable def vp00011010010_1 : Blocks := edgeBlocks% "full/vectors/00011010010-V-0001.bin"
noncomputable def vp00011010010 : Blocks := (Blocks.join vp00011010010_0 vp00011010010_1)
private theorem bp000110100100 : Branch 0 (-839761639/4000000 : ℚ) vp00011010010 := by
  apply branch_left_normalized (c:=vp000110100100) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-839761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-839761639/2000000 : ℚ) by norm_num]
  exact coverp000110100100
private noncomputable def ep000110100101_0 : Blocks := edgeBlocks% "full/vectors/000110100101-E-0000.bin"
private noncomputable def ep000110100101_1 : Blocks := edgeBlocks% "full/vectors/000110100101-E-0001.bin"
noncomputable def ep000110100101 : Blocks := (Blocks.join ep000110100101_0 ep000110100101_1)
private theorem idp000110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011010010.list =
    C ((2:ℤ)^163) * horner X vp000110100101.list + horner X ep000110100101.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110100101 : Branch 1 (-839761639/4000000 : ℚ) vp00011010010 := by
  apply branch_checked idp000110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-839761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-841761639/2000000 : ℚ) by norm_num]
  exact coverp000110100101
theorem coverp00011010010 : Covers (-839761639/4000000 : ℚ) vp00011010010 := join_branches bp000110100100 bp000110100101
private noncomputable def vp0001101001_0 : Blocks := edgeBlocks% "full/vectors/0001101001-V-0000.bin"
private noncomputable def vp0001101001_1 : Blocks := edgeBlocks% "full/vectors/0001101001-V-0001.bin"
private noncomputable def vp0001101001_2 : Blocks := edgeBlocks% "full/vectors/0001101001-V-0002.bin"
noncomputable def vp0001101001 : Blocks := (Blocks.join vp0001101001_0 (Blocks.join vp0001101001_1 vp0001101001_2))
private theorem bp00011010010 : Branch 0 (-839761639/8000000 : ℚ) vp0001101001 := by
  apply branch_left_normalized (c:=vp00011010010) (k:=0) (m:=151) (by decide +kernel)
  rw [show 2*(-839761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-839761639/4000000 : ℚ) by norm_num]
  exact coverp00011010010
private noncomputable def ep00011010011_0 : Blocks := edgeBlocks% "full/vectors/00011010011-E-0000.bin"
private noncomputable def ep00011010011_1 : Blocks := edgeBlocks% "full/vectors/00011010011-E-0001.bin"
private noncomputable def ep00011010011_2 : Blocks := edgeBlocks% "full/vectors/00011010011-E-0002.bin"
noncomputable def ep00011010011 : Blocks := (Blocks.join ep00011010011_0 (Blocks.join ep00011010011_1 ep00011010011_2))
private theorem idp00011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101001.list =
    C ((2:ℤ)^308) * horner X vp00011010011.list + horner X ep00011010011.list := by
  exact edge_identity (B := (2:ℤ)^520) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011010011 : Branch 1 (-839761639/8000000 : ℚ) vp0001101001 := by
  apply branch_checked idp00011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-839761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-843761639/4000000 : ℚ) by norm_num]
  exact coverp00011010011
theorem coverp0001101001 : Covers (-839761639/8000000 : ℚ) vp0001101001 := join_branches bp00011010010 bp00011010011
private noncomputable def vp0001101000111_0 : Blocks := edgeBlocks% "full/vectors/0001101000111-V-0000.bin"
noncomputable def vp0001101000111 : Blocks := vp0001101000111_0
theorem coverp0001101000111 : Covers (-838761639/1000000 : ℚ) vp0001101000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101000110_0 : Blocks := edgeBlocks% "full/vectors/0001101000110-V-0000.bin"
noncomputable def vp0001101000110 : Blocks := vp0001101000110_0
theorem coverp0001101000110 : Covers (-837761639/1000000 : ℚ) vp0001101000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000110100011_0 : Blocks := edgeBlocks% "full/vectors/000110100011-V-0000.bin"
noncomputable def vp000110100011 : Blocks := vp000110100011_0
private theorem bp0001101000110 : Branch 0 (-837761639/2000000 : ℚ) vp000110100011 := by
  apply branch_left_normalized (c:=vp0001101000110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-837761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-837761639/1000000 : ℚ) by norm_num]
  exact coverp0001101000110
private noncomputable def ep0001101000111_0 : Blocks := edgeBlocks% "full/vectors/0001101000111-E-0000.bin"
noncomputable def ep0001101000111 : Blocks := ep0001101000111_0
private theorem idp0001101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110100011.list =
    C ((2:ℤ)^90) * horner X vp0001101000111.list + horner X ep0001101000111.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101000111 : Branch 1 (-837761639/2000000 : ℚ) vp000110100011 := by
  apply branch_checked idp0001101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-837761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-838761639/1000000 : ℚ) by norm_num]
  exact coverp0001101000111
theorem coverp000110100011 : Covers (-837761639/2000000 : ℚ) vp000110100011 := join_branches bp0001101000110 bp0001101000111
private noncomputable def vp0001101000101_0 : Blocks := edgeBlocks% "full/vectors/0001101000101-V-0000.bin"
noncomputable def vp0001101000101 : Blocks := vp0001101000101_0
theorem coverp0001101000101 : Covers (-836761639/1000000 : ℚ) vp0001101000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101000100_0 : Blocks := edgeBlocks% "full/vectors/0001101000100-V-0000.bin"
noncomputable def vp0001101000100 : Blocks := vp0001101000100_0
theorem coverp0001101000100 : Covers (-835761639/1000000 : ℚ) vp0001101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000110100010_0 : Blocks := edgeBlocks% "full/vectors/000110100010-V-0000.bin"
noncomputable def vp000110100010 : Blocks := vp000110100010_0
private theorem bp0001101000100 : Branch 0 (-835761639/2000000 : ℚ) vp000110100010 := by
  apply branch_left_normalized (c:=vp0001101000100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-835761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-835761639/1000000 : ℚ) by norm_num]
  exact coverp0001101000100
private noncomputable def ep0001101000101_0 : Blocks := edgeBlocks% "full/vectors/0001101000101-E-0000.bin"
noncomputable def ep0001101000101 : Blocks := ep0001101000101_0
private theorem idp0001101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110100010.list =
    C ((2:ℤ)^89) * horner X vp0001101000101.list + horner X ep0001101000101.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101000101 : Branch 1 (-835761639/2000000 : ℚ) vp000110100010 := by
  apply branch_checked idp0001101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-835761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-836761639/1000000 : ℚ) by norm_num]
  exact coverp0001101000101
theorem coverp000110100010 : Covers (-835761639/2000000 : ℚ) vp000110100010 := join_branches bp0001101000100 bp0001101000101
private noncomputable def vp00011010001_0 : Blocks := edgeBlocks% "full/vectors/00011010001-V-0000.bin"
private noncomputable def vp00011010001_1 : Blocks := edgeBlocks% "full/vectors/00011010001-V-0001.bin"
noncomputable def vp00011010001 : Blocks := (Blocks.join vp00011010001_0 vp00011010001_1)
private theorem bp000110100010 : Branch 0 (-835761639/4000000 : ℚ) vp00011010001 := by
  apply branch_left_normalized (c:=vp000110100010) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-835761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-835761639/2000000 : ℚ) by norm_num]
  exact coverp000110100010
private noncomputable def ep000110100011_0 : Blocks := edgeBlocks% "full/vectors/000110100011-E-0000.bin"
private noncomputable def ep000110100011_1 : Blocks := edgeBlocks% "full/vectors/000110100011-E-0001.bin"
noncomputable def ep000110100011 : Blocks := (Blocks.join ep000110100011_0 ep000110100011_1)
private theorem idp000110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011010001.list =
    C ((2:ℤ)^163) * horner X vp000110100011.list + horner X ep000110100011.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110100011 : Branch 1 (-835761639/4000000 : ℚ) vp00011010001 := by
  apply branch_checked idp000110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-835761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-837761639/2000000 : ℚ) by norm_num]
  exact coverp000110100011
theorem coverp00011010001 : Covers (-835761639/4000000 : ℚ) vp00011010001 := join_branches bp000110100010 bp000110100011
private noncomputable def vp0001101000011_0 : Blocks := edgeBlocks% "full/vectors/0001101000011-V-0000.bin"
noncomputable def vp0001101000011 : Blocks := vp0001101000011_0
theorem coverp0001101000011 : Covers (-834761639/1000000 : ℚ) vp0001101000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101000010_0 : Blocks := edgeBlocks% "full/vectors/0001101000010-V-0000.bin"
noncomputable def vp0001101000010 : Blocks := vp0001101000010_0
theorem coverp0001101000010 : Covers (-833761639/1000000 : ℚ) vp0001101000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000110100001_0 : Blocks := edgeBlocks% "full/vectors/000110100001-V-0000.bin"
noncomputable def vp000110100001 : Blocks := vp000110100001_0
private theorem bp0001101000010 : Branch 0 (-833761639/2000000 : ℚ) vp000110100001 := by
  apply branch_left_normalized (c:=vp0001101000010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-833761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-833761639/1000000 : ℚ) by norm_num]
  exact coverp0001101000010
private noncomputable def ep0001101000011_0 : Blocks := edgeBlocks% "full/vectors/0001101000011-E-0000.bin"
noncomputable def ep0001101000011 : Blocks := ep0001101000011_0
private theorem idp0001101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110100001.list =
    C ((2:ℤ)^90) * horner X vp0001101000011.list + horner X ep0001101000011.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101000011 : Branch 1 (-833761639/2000000 : ℚ) vp000110100001 := by
  apply branch_checked idp0001101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-833761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-834761639/1000000 : ℚ) by norm_num]
  exact coverp0001101000011
theorem coverp000110100001 : Covers (-833761639/2000000 : ℚ) vp000110100001 := join_branches bp0001101000010 bp0001101000011
private noncomputable def vp0001101000001_0 : Blocks := edgeBlocks% "full/vectors/0001101000001-V-0000.bin"
noncomputable def vp0001101000001 : Blocks := vp0001101000001_0
theorem coverp0001101000001 : Covers (-832761639/1000000 : ℚ) vp0001101000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101000000_0 : Blocks := edgeBlocks% "full/vectors/0001101000000-V-0000.bin"
noncomputable def vp0001101000000 : Blocks := vp0001101000000_0
theorem coverp0001101000000 : Covers (-831761639/1000000 : ℚ) vp0001101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000110100000_0 : Blocks := edgeBlocks% "full/vectors/000110100000-V-0000.bin"
noncomputable def vp000110100000 : Blocks := vp000110100000_0
private theorem bp0001101000000 : Branch 0 (-831761639/2000000 : ℚ) vp000110100000 := by
  apply branch_left_normalized (c:=vp0001101000000) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-831761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-831761639/1000000 : ℚ) by norm_num]
  exact coverp0001101000000
private noncomputable def ep0001101000001_0 : Blocks := edgeBlocks% "full/vectors/0001101000001-E-0000.bin"
noncomputable def ep0001101000001 : Blocks := ep0001101000001_0
private theorem idp0001101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110100000.list =
    C ((2:ℤ)^90) * horner X vp0001101000001.list + horner X ep0001101000001.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101000001 : Branch 1 (-831761639/2000000 : ℚ) vp000110100000 := by
  apply branch_checked idp0001101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-831761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-832761639/1000000 : ℚ) by norm_num]
  exact coverp0001101000001
theorem coverp000110100000 : Covers (-831761639/2000000 : ℚ) vp000110100000 := join_branches bp0001101000000 bp0001101000001
private noncomputable def vp00011010000_0 : Blocks := edgeBlocks% "full/vectors/00011010000-V-0000.bin"
private noncomputable def vp00011010000_1 : Blocks := edgeBlocks% "full/vectors/00011010000-V-0001.bin"
noncomputable def vp00011010000 : Blocks := (Blocks.join vp00011010000_0 vp00011010000_1)
private theorem bp000110100000 : Branch 0 (-831761639/4000000 : ℚ) vp00011010000 := by
  apply branch_left_normalized (c:=vp000110100000) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-831761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-831761639/2000000 : ℚ) by norm_num]
  exact coverp000110100000
private noncomputable def ep000110100001_0 : Blocks := edgeBlocks% "full/vectors/000110100001-E-0000.bin"
private noncomputable def ep000110100001_1 : Blocks := edgeBlocks% "full/vectors/000110100001-E-0001.bin"
noncomputable def ep000110100001 : Blocks := (Blocks.join ep000110100001_0 ep000110100001_1)
private theorem idp000110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011010000.list =
    C ((2:ℤ)^165) * horner X vp000110100001.list + horner X ep000110100001.list := by
  exact edge_identity (B := (2:ℤ)^316) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110100001 : Branch 1 (-831761639/4000000 : ℚ) vp00011010000 := by
  apply branch_checked idp000110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-831761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-833761639/2000000 : ℚ) by norm_num]
  exact coverp000110100001
theorem coverp00011010000 : Covers (-831761639/4000000 : ℚ) vp00011010000 := join_branches bp000110100000 bp000110100001
private noncomputable def vp0001101000_0 : Blocks := edgeBlocks% "full/vectors/0001101000-V-0000.bin"
private noncomputable def vp0001101000_1 : Blocks := edgeBlocks% "full/vectors/0001101000-V-0001.bin"
private noncomputable def vp0001101000_2 : Blocks := edgeBlocks% "full/vectors/0001101000-V-0002.bin"
noncomputable def vp0001101000 : Blocks := (Blocks.join vp0001101000_0 (Blocks.join vp0001101000_1 vp0001101000_2))
private theorem bp00011010000 : Branch 0 (-831761639/8000000 : ℚ) vp0001101000 := by
  apply branch_left_normalized (c:=vp00011010000) (k:=0) (m:=152) (by decide +kernel)
  rw [show 2*(-831761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-831761639/4000000 : ℚ) by norm_num]
  exact coverp00011010000
private noncomputable def ep00011010001_0 : Blocks := edgeBlocks% "full/vectors/00011010001-E-0000.bin"
private noncomputable def ep00011010001_1 : Blocks := edgeBlocks% "full/vectors/00011010001-E-0001.bin"
private noncomputable def ep00011010001_2 : Blocks := edgeBlocks% "full/vectors/00011010001-E-0002.bin"
noncomputable def ep00011010001 : Blocks := (Blocks.join ep00011010001_0 (Blocks.join ep00011010001_1 ep00011010001_2))
private theorem idp00011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101000.list =
    C ((2:ℤ)^312) * horner X vp00011010001.list + horner X ep00011010001.list := by
  exact edge_identity (B := (2:ℤ)^523) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011010001 : Branch 1 (-831761639/8000000 : ℚ) vp0001101000 := by
  apply branch_checked idp00011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-831761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-835761639/4000000 : ℚ) by norm_num]
  exact coverp00011010001
theorem coverp0001101000 : Covers (-831761639/8000000 : ℚ) vp0001101000 := join_branches bp00011010000 bp00011010001
private noncomputable def vp000110100_0 : Blocks := edgeBlocks% "full/vectors/000110100-V-0000.bin"
private noncomputable def vp000110100_1 : Blocks := edgeBlocks% "full/vectors/000110100-V-0001.bin"
private noncomputable def vp000110100_2 : Blocks := edgeBlocks% "full/vectors/000110100-V-0002.bin"
private noncomputable def vp000110100_3 : Blocks := edgeBlocks% "full/vectors/000110100-V-0003.bin"
private noncomputable def vp000110100_4 : Blocks := edgeBlocks% "full/vectors/000110100-V-0004.bin"
noncomputable def vp000110100 : Blocks := (Blocks.join (Blocks.join vp000110100_0 vp000110100_1) (Blocks.join vp000110100_2 (Blocks.join vp000110100_3 vp000110100_4)))
private theorem bp0001101000 : Branch 0 (-831761639/16000000 : ℚ) vp000110100 := by
  apply branch_left_normalized (c:=vp0001101000) (k:=0) (m:=287) (by decide +kernel)
  rw [show 2*(-831761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-831761639/8000000 : ℚ) by norm_num]
  exact coverp0001101000
private noncomputable def ep0001101001_0 : Blocks := edgeBlocks% "full/vectors/0001101001-E-0000.bin"
private noncomputable def ep0001101001_1 : Blocks := edgeBlocks% "full/vectors/0001101001-E-0001.bin"
private noncomputable def ep0001101001_2 : Blocks := edgeBlocks% "full/vectors/0001101001-E-0002.bin"
private noncomputable def ep0001101001_3 : Blocks := edgeBlocks% "full/vectors/0001101001-E-0003.bin"
private noncomputable def ep0001101001_4 : Blocks := edgeBlocks% "full/vectors/0001101001-E-0004.bin"
noncomputable def ep0001101001 : Blocks := (Blocks.join (Blocks.join ep0001101001_0 ep0001101001_1) (Blocks.join ep0001101001_2 (Blocks.join ep0001101001_3 ep0001101001_4)))
private theorem idp0001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110100.list =
    C ((2:ℤ)^604) * horner X vp0001101001.list + horner X ep0001101001.list := by
  exact edge_identity (B := (2:ℤ)^937) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101001 : Branch 1 (-831761639/16000000 : ℚ) vp000110100 := by
  apply branch_checked idp0001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-831761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-839761639/8000000 : ℚ) by norm_num]
  exact coverp0001101001
theorem coverp000110100 : Covers (-831761639/16000000 : ℚ) vp000110100 := join_branches bp0001101000 bp0001101001
private noncomputable def vp00011010_0 : Blocks := edgeBlocks% "full/vectors/00011010-V-0000.bin"
private noncomputable def vp00011010_1 : Blocks := edgeBlocks% "full/vectors/00011010-V-0001.bin"
private noncomputable def vp00011010_2 : Blocks := edgeBlocks% "full/vectors/00011010-V-0002.bin"
private noncomputable def vp00011010_3 : Blocks := edgeBlocks% "full/vectors/00011010-V-0003.bin"
private noncomputable def vp00011010_4 : Blocks := edgeBlocks% "full/vectors/00011010-V-0004.bin"
private noncomputable def vp00011010_5 : Blocks := edgeBlocks% "full/vectors/00011010-V-0005.bin"
private noncomputable def vp00011010_6 : Blocks := edgeBlocks% "full/vectors/00011010-V-0006.bin"
private noncomputable def vp00011010_7 : Blocks := edgeBlocks% "full/vectors/00011010-V-0007.bin"
private noncomputable def vp00011010_8 : Blocks := edgeBlocks% "full/vectors/00011010-V-0008.bin"
noncomputable def vp00011010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00011010_0 vp00011010_1) (Blocks.join vp00011010_2 vp00011010_3)) (Blocks.join (Blocks.join vp00011010_4 vp00011010_5) (Blocks.join vp00011010_6 (Blocks.join vp00011010_7 vp00011010_8))))
private theorem bp000110100 : Branch 0 (-831761639/32000000 : ℚ) vp00011010 := by
  apply branch_left_normalized (c:=vp000110100) (k:=0) (m:=556) (by decide +kernel)
  rw [show 2*(-831761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-831761639/16000000 : ℚ) by norm_num]
  exact coverp000110100
private noncomputable def ep000110101_0 : Blocks := edgeBlocks% "full/vectors/000110101-E-0000.bin"
private noncomputable def ep000110101_1 : Blocks := edgeBlocks% "full/vectors/000110101-E-0001.bin"
private noncomputable def ep000110101_2 : Blocks := edgeBlocks% "full/vectors/000110101-E-0002.bin"
private noncomputable def ep000110101_3 : Blocks := edgeBlocks% "full/vectors/000110101-E-0003.bin"
private noncomputable def ep000110101_4 : Blocks := edgeBlocks% "full/vectors/000110101-E-0004.bin"
private noncomputable def ep000110101_5 : Blocks := edgeBlocks% "full/vectors/000110101-E-0005.bin"
private noncomputable def ep000110101_6 : Blocks := edgeBlocks% "full/vectors/000110101-E-0006.bin"
private noncomputable def ep000110101_7 : Blocks := edgeBlocks% "full/vectors/000110101-E-0007.bin"
private noncomputable def ep000110101_8 : Blocks := edgeBlocks% "full/vectors/000110101-E-0008.bin"
noncomputable def ep000110101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000110101_0 ep000110101_1) (Blocks.join ep000110101_2 ep000110101_3)) (Blocks.join (Blocks.join ep000110101_4 ep000110101_5) (Blocks.join ep000110101_6 (Blocks.join ep000110101_7 ep000110101_8))))
private theorem idp000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011010.list =
    C ((2:ℤ)^1180) * horner X vp000110101.list + horner X ep000110101.list := by
  exact edge_identity (B := (2:ℤ)^1757) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110101 : Branch 1 (-831761639/32000000 : ℚ) vp00011010 := by
  apply branch_checked idp000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-831761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-847761639/16000000 : ℚ) by norm_num]
  exact coverp000110101
theorem coverp00011010 : Covers (-831761639/32000000 : ℚ) vp00011010 := join_branches bp000110100 bp000110101
private noncomputable def vp0001101_0 : Blocks := edgeBlocks% "full/vectors/0001101-V-0000.bin"
private noncomputable def vp0001101_1 : Blocks := edgeBlocks% "full/vectors/0001101-V-0001.bin"
private noncomputable def vp0001101_2 : Blocks := edgeBlocks% "full/vectors/0001101-V-0002.bin"
private noncomputable def vp0001101_3 : Blocks := edgeBlocks% "full/vectors/0001101-V-0003.bin"
private noncomputable def vp0001101_4 : Blocks := edgeBlocks% "full/vectors/0001101-V-0004.bin"
private noncomputable def vp0001101_5 : Blocks := edgeBlocks% "full/vectors/0001101-V-0005.bin"
private noncomputable def vp0001101_6 : Blocks := edgeBlocks% "full/vectors/0001101-V-0006.bin"
private noncomputable def vp0001101_7 : Blocks := edgeBlocks% "full/vectors/0001101-V-0007.bin"
private noncomputable def vp0001101_8 : Blocks := edgeBlocks% "full/vectors/0001101-V-0008.bin"
private noncomputable def vp0001101_9 : Blocks := edgeBlocks% "full/vectors/0001101-V-0009.bin"
private noncomputable def vp0001101_10 : Blocks := edgeBlocks% "full/vectors/0001101-V-0010.bin"
private noncomputable def vp0001101_11 : Blocks := edgeBlocks% "full/vectors/0001101-V-0011.bin"
private noncomputable def vp0001101_12 : Blocks := edgeBlocks% "full/vectors/0001101-V-0012.bin"
private noncomputable def vp0001101_13 : Blocks := edgeBlocks% "full/vectors/0001101-V-0013.bin"
private noncomputable def vp0001101_14 : Blocks := edgeBlocks% "full/vectors/0001101-V-0014.bin"
private noncomputable def vp0001101_15 : Blocks := edgeBlocks% "full/vectors/0001101-V-0015.bin"
private noncomputable def vp0001101_16 : Blocks := edgeBlocks% "full/vectors/0001101-V-0016.bin"
noncomputable def vp0001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0001101_0 vp0001101_1) (Blocks.join vp0001101_2 vp0001101_3)) (Blocks.join (Blocks.join vp0001101_4 vp0001101_5) (Blocks.join vp0001101_6 vp0001101_7))) (Blocks.join (Blocks.join (Blocks.join vp0001101_8 vp0001101_9) (Blocks.join vp0001101_10 vp0001101_11)) (Blocks.join (Blocks.join vp0001101_12 vp0001101_13) (Blocks.join vp0001101_14 (Blocks.join vp0001101_15 vp0001101_16)))))
private theorem bp00011010 : Branch 0 (-831761639/64000000 : ℚ) vp0001101 := by
  apply branch_left_normalized (c:=vp00011010) (k:=0) (m:=1089) (by decide +kernel)
  rw [show 2*(-831761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-831761639/32000000 : ℚ) by norm_num]
  exact coverp00011010
private noncomputable def ep00011011_0 : Blocks := edgeBlocks% "full/vectors/00011011-E-0000.bin"
private noncomputable def ep00011011_1 : Blocks := edgeBlocks% "full/vectors/00011011-E-0001.bin"
private noncomputable def ep00011011_2 : Blocks := edgeBlocks% "full/vectors/00011011-E-0002.bin"
private noncomputable def ep00011011_3 : Blocks := edgeBlocks% "full/vectors/00011011-E-0003.bin"
private noncomputable def ep00011011_4 : Blocks := edgeBlocks% "full/vectors/00011011-E-0004.bin"
private noncomputable def ep00011011_5 : Blocks := edgeBlocks% "full/vectors/00011011-E-0005.bin"
private noncomputable def ep00011011_6 : Blocks := edgeBlocks% "full/vectors/00011011-E-0006.bin"
private noncomputable def ep00011011_7 : Blocks := edgeBlocks% "full/vectors/00011011-E-0007.bin"
private noncomputable def ep00011011_8 : Blocks := edgeBlocks% "full/vectors/00011011-E-0008.bin"
private noncomputable def ep00011011_9 : Blocks := edgeBlocks% "full/vectors/00011011-E-0009.bin"
private noncomputable def ep00011011_10 : Blocks := edgeBlocks% "full/vectors/00011011-E-0010.bin"
private noncomputable def ep00011011_11 : Blocks := edgeBlocks% "full/vectors/00011011-E-0011.bin"
private noncomputable def ep00011011_12 : Blocks := edgeBlocks% "full/vectors/00011011-E-0012.bin"
private noncomputable def ep00011011_13 : Blocks := edgeBlocks% "full/vectors/00011011-E-0013.bin"
private noncomputable def ep00011011_14 : Blocks := edgeBlocks% "full/vectors/00011011-E-0014.bin"
private noncomputable def ep00011011_15 : Blocks := edgeBlocks% "full/vectors/00011011-E-0015.bin"
private noncomputable def ep00011011_16 : Blocks := edgeBlocks% "full/vectors/00011011-E-0016.bin"
noncomputable def ep00011011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00011011_0 ep00011011_1) (Blocks.join ep00011011_2 ep00011011_3)) (Blocks.join (Blocks.join ep00011011_4 ep00011011_5) (Blocks.join ep00011011_6 ep00011011_7))) (Blocks.join (Blocks.join (Blocks.join ep00011011_8 ep00011011_9) (Blocks.join ep00011011_10 ep00011011_11)) (Blocks.join (Blocks.join ep00011011_12 ep00011011_13) (Blocks.join ep00011011_14 (Blocks.join ep00011011_15 ep00011011_16)))))
private theorem idp00011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101.list =
    C ((2:ℤ)^2302) * horner X vp00011011.list + horner X ep00011011.list := by
  exact edge_identity (B := (2:ℤ)^3363) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011 : Branch 1 (-831761639/64000000 : ℚ) vp0001101 := by
  apply branch_checked idp00011011 (by positivity) (by decide +kernel)
  rw [show 2*(-831761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-863761639/32000000 : ℚ) by norm_num]
  exact coverp00011011
theorem coverp0001101 : Covers (-831761639/64000000 : ℚ) vp0001101 := join_branches bp00011010 bp00011011
end NextProof.EdgeFull

