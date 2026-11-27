import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00041

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000001010111111_0 : Blocks := edgeBlocks% "full/vectors/000001010111111-V-0000.bin"
noncomputable def vp000001010111111 : Blocks := vp000001010111111_0
theorem coverp000001010111111 : Covers (-175511639/250000 : ℚ) vp000001010111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001010111110_0 : Blocks := edgeBlocks% "full/vectors/000001010111110-V-0000.bin"
noncomputable def vp000001010111110 : Blocks := vp000001010111110_0
theorem coverp000001010111110 : Covers (-175261639/250000 : ℚ) vp000001010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101011111_0 : Blocks := edgeBlocks% "full/vectors/00000101011111-V-0000.bin"
noncomputable def vp00000101011111 : Blocks := vp00000101011111_0
private theorem bp000001010111110 : Branch 0 (-175261639/500000 : ℚ) vp00000101011111 := by
  apply branch_left_normalized (c:=vp000001010111110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-175261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-175261639/250000 : ℚ) by norm_num]
  exact coverp000001010111110
private noncomputable def ep000001010111111_0 : Blocks := edgeBlocks% "full/vectors/000001010111111-E-0000.bin"
noncomputable def ep000001010111111 : Blocks := ep000001010111111_0
private theorem idp000001010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101011111.list =
    C ((2:ℤ)^57) * horner X vp000001010111111.list + horner X ep000001010111111.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001010111111 : Branch 1 (-175261639/500000 : ℚ) vp00000101011111 := by
  apply branch_checked idp000001010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-175261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-175511639/250000 : ℚ) by norm_num]
  exact coverp000001010111111
theorem coverp00000101011111 : Covers (-175261639/500000 : ℚ) vp00000101011111 := join_branches bp000001010111110 bp000001010111111
private noncomputable def vp000001010111101_0 : Blocks := edgeBlocks% "full/vectors/000001010111101-V-0000.bin"
noncomputable def vp000001010111101 : Blocks := vp000001010111101_0
theorem coverp000001010111101 : Covers (-175011639/250000 : ℚ) vp000001010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001010111100_0 : Blocks := edgeBlocks% "full/vectors/000001010111100-V-0000.bin"
noncomputable def vp000001010111100 : Blocks := vp000001010111100_0
theorem coverp000001010111100 : Covers (-174761639/250000 : ℚ) vp000001010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101011110_0 : Blocks := edgeBlocks% "full/vectors/00000101011110-V-0000.bin"
noncomputable def vp00000101011110 : Blocks := vp00000101011110_0
private theorem bp000001010111100 : Branch 0 (-174761639/500000 : ℚ) vp00000101011110 := by
  apply branch_left_normalized (c:=vp000001010111100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-174761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-174761639/250000 : ℚ) by norm_num]
  exact coverp000001010111100
private noncomputable def ep000001010111101_0 : Blocks := edgeBlocks% "full/vectors/000001010111101-E-0000.bin"
noncomputable def ep000001010111101 : Blocks := ep000001010111101_0
private theorem idp000001010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101011110.list =
    C ((2:ℤ)^59) * horner X vp000001010111101.list + horner X ep000001010111101.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001010111101 : Branch 1 (-174761639/500000 : ℚ) vp00000101011110 := by
  apply branch_checked idp000001010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-174761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-175011639/250000 : ℚ) by norm_num]
  exact coverp000001010111101
theorem coverp00000101011110 : Covers (-174761639/500000 : ℚ) vp00000101011110 := join_branches bp000001010111100 bp000001010111101
private noncomputable def vp0000010101111_0 : Blocks := edgeBlocks% "full/vectors/0000010101111-V-0000.bin"
noncomputable def vp0000010101111 : Blocks := vp0000010101111_0
private theorem bp00000101011110 : Branch 0 (-174761639/1000000 : ℚ) vp0000010101111 := by
  apply branch_left_normalized (c:=vp00000101011110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-174761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-174761639/500000 : ℚ) by norm_num]
  exact coverp00000101011110
private noncomputable def ep00000101011111_0 : Blocks := edgeBlocks% "full/vectors/00000101011111-E-0000.bin"
noncomputable def ep00000101011111 : Blocks := ep00000101011111_0
private theorem idp00000101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010101111.list =
    C ((2:ℤ)^100) * horner X vp00000101011111.list + horner X ep00000101011111.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101011111 : Branch 1 (-174761639/1000000 : ℚ) vp0000010101111 := by
  apply branch_checked idp00000101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-174761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-175261639/500000 : ℚ) by norm_num]
  exact coverp00000101011111
theorem coverp0000010101111 : Covers (-174761639/1000000 : ℚ) vp0000010101111 := join_branches bp00000101011110 bp00000101011111
private noncomputable def vp000001010111011_0 : Blocks := edgeBlocks% "full/vectors/000001010111011-V-0000.bin"
noncomputable def vp000001010111011 : Blocks := vp000001010111011_0
theorem coverp000001010111011 : Covers (-174511639/250000 : ℚ) vp000001010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001010111010_0 : Blocks := edgeBlocks% "full/vectors/000001010111010-V-0000.bin"
noncomputable def vp000001010111010 : Blocks := vp000001010111010_0
theorem coverp000001010111010 : Covers (-174261639/250000 : ℚ) vp000001010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101011101_0 : Blocks := edgeBlocks% "full/vectors/00000101011101-V-0000.bin"
noncomputable def vp00000101011101 : Blocks := vp00000101011101_0
private theorem bp000001010111010 : Branch 0 (-174261639/500000 : ℚ) vp00000101011101 := by
  apply branch_left_normalized (c:=vp000001010111010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-174261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-174261639/250000 : ℚ) by norm_num]
  exact coverp000001010111010
private noncomputable def ep000001010111011_0 : Blocks := edgeBlocks% "full/vectors/000001010111011-E-0000.bin"
noncomputable def ep000001010111011 : Blocks := ep000001010111011_0
private theorem idp000001010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101011101.list =
    C ((2:ℤ)^59) * horner X vp000001010111011.list + horner X ep000001010111011.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001010111011 : Branch 1 (-174261639/500000 : ℚ) vp00000101011101 := by
  apply branch_checked idp000001010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-174261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-174511639/250000 : ℚ) by norm_num]
  exact coverp000001010111011
theorem coverp00000101011101 : Covers (-174261639/500000 : ℚ) vp00000101011101 := join_branches bp000001010111010 bp000001010111011
private noncomputable def vp000001010111001_0 : Blocks := edgeBlocks% "full/vectors/000001010111001-V-0000.bin"
noncomputable def vp000001010111001 : Blocks := vp000001010111001_0
theorem coverp000001010111001 : Covers (-174011639/250000 : ℚ) vp000001010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001010111000_0 : Blocks := edgeBlocks% "full/vectors/000001010111000-V-0000.bin"
noncomputable def vp000001010111000 : Blocks := vp000001010111000_0
theorem coverp000001010111000 : Covers (-173761639/250000 : ℚ) vp000001010111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101011100_0 : Blocks := edgeBlocks% "full/vectors/00000101011100-V-0000.bin"
noncomputable def vp00000101011100 : Blocks := vp00000101011100_0
private theorem bp000001010111000 : Branch 0 (-173761639/500000 : ℚ) vp00000101011100 := by
  apply branch_left_normalized (c:=vp000001010111000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-173761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-173761639/250000 : ℚ) by norm_num]
  exact coverp000001010111000
private noncomputable def ep000001010111001_0 : Blocks := edgeBlocks% "full/vectors/000001010111001-E-0000.bin"
noncomputable def ep000001010111001 : Blocks := ep000001010111001_0
private theorem idp000001010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101011100.list =
    C ((2:ℤ)^56) * horner X vp000001010111001.list + horner X ep000001010111001.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001010111001 : Branch 1 (-173761639/500000 : ℚ) vp00000101011100 := by
  apply branch_checked idp000001010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-173761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-174011639/250000 : ℚ) by norm_num]
  exact coverp000001010111001
theorem coverp00000101011100 : Covers (-173761639/500000 : ℚ) vp00000101011100 := join_branches bp000001010111000 bp000001010111001
private noncomputable def vp0000010101110_0 : Blocks := edgeBlocks% "full/vectors/0000010101110-V-0000.bin"
noncomputable def vp0000010101110 : Blocks := vp0000010101110_0
private theorem bp00000101011100 : Branch 0 (-173761639/1000000 : ℚ) vp0000010101110 := by
  apply branch_left_normalized (c:=vp00000101011100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-173761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-173761639/500000 : ℚ) by norm_num]
  exact coverp00000101011100
private noncomputable def ep00000101011101_0 : Blocks := edgeBlocks% "full/vectors/00000101011101-E-0000.bin"
noncomputable def ep00000101011101 : Blocks := ep00000101011101_0
private theorem idp00000101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010101110.list =
    C ((2:ℤ)^95) * horner X vp00000101011101.list + horner X ep00000101011101.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101011101 : Branch 1 (-173761639/1000000 : ℚ) vp0000010101110 := by
  apply branch_checked idp00000101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-173761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-174261639/500000 : ℚ) by norm_num]
  exact coverp00000101011101
theorem coverp0000010101110 : Covers (-173761639/1000000 : ℚ) vp0000010101110 := join_branches bp00000101011100 bp00000101011101
private noncomputable def vp000001010111_0 : Blocks := edgeBlocks% "full/vectors/000001010111-V-0000.bin"
private noncomputable def vp000001010111_1 : Blocks := edgeBlocks% "full/vectors/000001010111-V-0001.bin"
noncomputable def vp000001010111 : Blocks := (Blocks.join vp000001010111_0 vp000001010111_1)
private theorem bp0000010101110 : Branch 0 (-173761639/2000000 : ℚ) vp000001010111 := by
  apply branch_left_normalized (c:=vp0000010101110) (k:=0) (m:=94) (by decide +kernel)
  rw [show 2*(-173761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-173761639/1000000 : ℚ) by norm_num]
  exact coverp0000010101110
private noncomputable def ep0000010101111_0 : Blocks := edgeBlocks% "full/vectors/0000010101111-E-0000.bin"
private noncomputable def ep0000010101111_1 : Blocks := edgeBlocks% "full/vectors/0000010101111-E-0001.bin"
noncomputable def ep0000010101111 : Blocks := (Blocks.join ep0000010101111_0 ep0000010101111_1)
private theorem idp0000010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001010111.list =
    C ((2:ℤ)^174) * horner X vp0000010101111.list + horner X ep0000010101111.list := by
  exact edge_identity (B := (2:ℤ)^347) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010101111 : Branch 1 (-173761639/2000000 : ℚ) vp000001010111 := by
  apply branch_checked idp0000010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-173761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-174761639/1000000 : ℚ) by norm_num]
  exact coverp0000010101111
theorem coverp000001010111 : Covers (-173761639/2000000 : ℚ) vp000001010111 := join_branches bp0000010101110 bp0000010101111
private noncomputable def vp000001010110111_0 : Blocks := edgeBlocks% "full/vectors/000001010110111-V-0000.bin"
noncomputable def vp000001010110111 : Blocks := vp000001010110111_0
theorem coverp000001010110111 : Covers (-173511639/250000 : ℚ) vp000001010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001010110110_0 : Blocks := edgeBlocks% "full/vectors/000001010110110-V-0000.bin"
noncomputable def vp000001010110110 : Blocks := vp000001010110110_0
theorem coverp000001010110110 : Covers (-173261639/250000 : ℚ) vp000001010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101011011_0 : Blocks := edgeBlocks% "full/vectors/00000101011011-V-0000.bin"
noncomputable def vp00000101011011 : Blocks := vp00000101011011_0
private theorem bp000001010110110 : Branch 0 (-173261639/500000 : ℚ) vp00000101011011 := by
  apply branch_left_normalized (c:=vp000001010110110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-173261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-173261639/250000 : ℚ) by norm_num]
  exact coverp000001010110110
private noncomputable def ep000001010110111_0 : Blocks := edgeBlocks% "full/vectors/000001010110111-E-0000.bin"
noncomputable def ep000001010110111 : Blocks := ep000001010110111_0
private theorem idp000001010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101011011.list =
    C ((2:ℤ)^55) * horner X vp000001010110111.list + horner X ep000001010110111.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001010110111 : Branch 1 (-173261639/500000 : ℚ) vp00000101011011 := by
  apply branch_checked idp000001010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-173261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-173511639/250000 : ℚ) by norm_num]
  exact coverp000001010110111
theorem coverp00000101011011 : Covers (-173261639/500000 : ℚ) vp00000101011011 := join_branches bp000001010110110 bp000001010110111
private noncomputable def vp00000101011010_0 : Blocks := edgeBlocks% "full/vectors/00000101011010-V-0000.bin"
noncomputable def vp00000101011010 : Blocks := vp00000101011010_0
theorem coverp00000101011010 : Covers (-172761639/500000 : ℚ) vp00000101011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010101101_0 : Blocks := edgeBlocks% "full/vectors/0000010101101-V-0000.bin"
noncomputable def vp0000010101101 : Blocks := vp0000010101101_0
private theorem bp00000101011010 : Branch 0 (-172761639/1000000 : ℚ) vp0000010101101 := by
  apply branch_left_normalized (c:=vp00000101011010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-172761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-172761639/500000 : ℚ) by norm_num]
  exact coverp00000101011010
private noncomputable def ep00000101011011_0 : Blocks := edgeBlocks% "full/vectors/00000101011011-E-0000.bin"
noncomputable def ep00000101011011 : Blocks := ep00000101011011_0
private theorem idp00000101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010101101.list =
    C ((2:ℤ)^94) * horner X vp00000101011011.list + horner X ep00000101011011.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101011011 : Branch 1 (-172761639/1000000 : ℚ) vp0000010101101 := by
  apply branch_checked idp00000101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-172761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-173261639/500000 : ℚ) by norm_num]
  exact coverp00000101011011
theorem coverp0000010101101 : Covers (-172761639/1000000 : ℚ) vp0000010101101 := join_branches bp00000101011010 bp00000101011011
private noncomputable def vp00000101011001_0 : Blocks := edgeBlocks% "full/vectors/00000101011001-V-0000.bin"
noncomputable def vp00000101011001 : Blocks := vp00000101011001_0
theorem coverp00000101011001 : Covers (-172261639/500000 : ℚ) vp00000101011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101011000_0 : Blocks := edgeBlocks% "full/vectors/00000101011000-V-0000.bin"
noncomputable def vp00000101011000 : Blocks := vp00000101011000_0
theorem coverp00000101011000 : Covers (-171761639/500000 : ℚ) vp00000101011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010101100_0 : Blocks := edgeBlocks% "full/vectors/0000010101100-V-0000.bin"
noncomputable def vp0000010101100 : Blocks := vp0000010101100_0
private theorem bp00000101011000 : Branch 0 (-171761639/1000000 : ℚ) vp0000010101100 := by
  apply branch_left_normalized (c:=vp00000101011000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-171761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-171761639/500000 : ℚ) by norm_num]
  exact coverp00000101011000
private noncomputable def ep00000101011001_0 : Blocks := edgeBlocks% "full/vectors/00000101011001-E-0000.bin"
noncomputable def ep00000101011001 : Blocks := ep00000101011001_0
private theorem idp00000101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010101100.list =
    C ((2:ℤ)^94) * horner X vp00000101011001.list + horner X ep00000101011001.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101011001 : Branch 1 (-171761639/1000000 : ℚ) vp0000010101100 := by
  apply branch_checked idp00000101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-171761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-172261639/500000 : ℚ) by norm_num]
  exact coverp00000101011001
theorem coverp0000010101100 : Covers (-171761639/1000000 : ℚ) vp0000010101100 := join_branches bp00000101011000 bp00000101011001
private noncomputable def vp000001010110_0 : Blocks := edgeBlocks% "full/vectors/000001010110-V-0000.bin"
private noncomputable def vp000001010110_1 : Blocks := edgeBlocks% "full/vectors/000001010110-V-0001.bin"
noncomputable def vp000001010110 : Blocks := (Blocks.join vp000001010110_0 vp000001010110_1)
private theorem bp0000010101100 : Branch 0 (-171761639/2000000 : ℚ) vp000001010110 := by
  apply branch_left_normalized (c:=vp0000010101100) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-171761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-171761639/1000000 : ℚ) by norm_num]
  exact coverp0000010101100
private noncomputable def ep0000010101101_0 : Blocks := edgeBlocks% "full/vectors/0000010101101-E-0000.bin"
private noncomputable def ep0000010101101_1 : Blocks := edgeBlocks% "full/vectors/0000010101101-E-0001.bin"
noncomputable def ep0000010101101 : Blocks := (Blocks.join ep0000010101101_0 ep0000010101101_1)
private theorem idp0000010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001010110.list =
    C ((2:ℤ)^172) * horner X vp0000010101101.list + horner X ep0000010101101.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010101101 : Branch 1 (-171761639/2000000 : ℚ) vp000001010110 := by
  apply branch_checked idp0000010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-171761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-172761639/1000000 : ℚ) by norm_num]
  exact coverp0000010101101
theorem coverp000001010110 : Covers (-171761639/2000000 : ℚ) vp000001010110 := join_branches bp0000010101100 bp0000010101101
private noncomputable def vp00000101011_0 : Blocks := edgeBlocks% "full/vectors/00000101011-V-0000.bin"
private noncomputable def vp00000101011_1 : Blocks := edgeBlocks% "full/vectors/00000101011-V-0001.bin"
private noncomputable def vp00000101011_2 : Blocks := edgeBlocks% "full/vectors/00000101011-V-0002.bin"
noncomputable def vp00000101011 : Blocks := (Blocks.join vp00000101011_0 (Blocks.join vp00000101011_1 vp00000101011_2))
private theorem bp000001010110 : Branch 0 (-171761639/4000000 : ℚ) vp00000101011 := by
  apply branch_left_normalized (c:=vp000001010110) (k:=0) (m:=167) (by decide +kernel)
  rw [show 2*(-171761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-171761639/2000000 : ℚ) by norm_num]
  exact coverp000001010110
private noncomputable def ep000001010111_0 : Blocks := edgeBlocks% "full/vectors/000001010111-E-0000.bin"
private noncomputable def ep000001010111_1 : Blocks := edgeBlocks% "full/vectors/000001010111-E-0001.bin"
private noncomputable def ep000001010111_2 : Blocks := edgeBlocks% "full/vectors/000001010111-E-0002.bin"
noncomputable def ep000001010111 : Blocks := (Blocks.join ep000001010111_0 (Blocks.join ep000001010111_1 ep000001010111_2))
private theorem idp000001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101011.list =
    C ((2:ℤ)^323) * horner X vp000001010111.list + horner X ep000001010111.list := by
  exact edge_identity (B := (2:ℤ)^568) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001010111 : Branch 1 (-171761639/4000000 : ℚ) vp00000101011 := by
  apply branch_checked idp000001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-171761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-173761639/2000000 : ℚ) by norm_num]
  exact coverp000001010111
theorem coverp00000101011 : Covers (-171761639/4000000 : ℚ) vp00000101011 := join_branches bp000001010110 bp000001010111
private noncomputable def vp00000101010111_0 : Blocks := edgeBlocks% "full/vectors/00000101010111-V-0000.bin"
noncomputable def vp00000101010111 : Blocks := vp00000101010111_0
theorem coverp00000101010111 : Covers (-171261639/500000 : ℚ) vp00000101010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101010110_0 : Blocks := edgeBlocks% "full/vectors/00000101010110-V-0000.bin"
noncomputable def vp00000101010110 : Blocks := vp00000101010110_0
theorem coverp00000101010110 : Covers (-170761639/500000 : ℚ) vp00000101010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010101011_0 : Blocks := edgeBlocks% "full/vectors/0000010101011-V-0000.bin"
noncomputable def vp0000010101011 : Blocks := vp0000010101011_0
private theorem bp00000101010110 : Branch 0 (-170761639/1000000 : ℚ) vp0000010101011 := by
  apply branch_left_normalized (c:=vp00000101010110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-170761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-170761639/500000 : ℚ) by norm_num]
  exact coverp00000101010110
private noncomputable def ep00000101010111_0 : Blocks := edgeBlocks% "full/vectors/00000101010111-E-0000.bin"
noncomputable def ep00000101010111 : Blocks := ep00000101010111_0
private theorem idp00000101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010101011.list =
    C ((2:ℤ)^93) * horner X vp00000101010111.list + horner X ep00000101010111.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101010111 : Branch 1 (-170761639/1000000 : ℚ) vp0000010101011 := by
  apply branch_checked idp00000101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-170761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-171261639/500000 : ℚ) by norm_num]
  exact coverp00000101010111
theorem coverp0000010101011 : Covers (-170761639/1000000 : ℚ) vp0000010101011 := join_branches bp00000101010110 bp00000101010111
private noncomputable def vp00000101010101_0 : Blocks := edgeBlocks% "full/vectors/00000101010101-V-0000.bin"
noncomputable def vp00000101010101 : Blocks := vp00000101010101_0
theorem coverp00000101010101 : Covers (-170261639/500000 : ℚ) vp00000101010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101010100_0 : Blocks := edgeBlocks% "full/vectors/00000101010100-V-0000.bin"
noncomputable def vp00000101010100 : Blocks := vp00000101010100_0
theorem coverp00000101010100 : Covers (-169761639/500000 : ℚ) vp00000101010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010101010_0 : Blocks := edgeBlocks% "full/vectors/0000010101010-V-0000.bin"
noncomputable def vp0000010101010 : Blocks := vp0000010101010_0
private theorem bp00000101010100 : Branch 0 (-169761639/1000000 : ℚ) vp0000010101010 := by
  apply branch_left_normalized (c:=vp00000101010100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-169761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-169761639/500000 : ℚ) by norm_num]
  exact coverp00000101010100
private noncomputable def ep00000101010101_0 : Blocks := edgeBlocks% "full/vectors/00000101010101-E-0000.bin"
noncomputable def ep00000101010101 : Blocks := ep00000101010101_0
private theorem idp00000101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010101010.list =
    C ((2:ℤ)^94) * horner X vp00000101010101.list + horner X ep00000101010101.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101010101 : Branch 1 (-169761639/1000000 : ℚ) vp0000010101010 := by
  apply branch_checked idp00000101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-169761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-170261639/500000 : ℚ) by norm_num]
  exact coverp00000101010101
theorem coverp0000010101010 : Covers (-169761639/1000000 : ℚ) vp0000010101010 := join_branches bp00000101010100 bp00000101010101
private noncomputable def vp000001010101_0 : Blocks := edgeBlocks% "full/vectors/000001010101-V-0000.bin"
private noncomputable def vp000001010101_1 : Blocks := edgeBlocks% "full/vectors/000001010101-V-0001.bin"
noncomputable def vp000001010101 : Blocks := (Blocks.join vp000001010101_0 vp000001010101_1)
private theorem bp0000010101010 : Branch 0 (-169761639/2000000 : ℚ) vp000001010101 := by
  apply branch_left_normalized (c:=vp0000010101010) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-169761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-169761639/1000000 : ℚ) by norm_num]
  exact coverp0000010101010
private noncomputable def ep0000010101011_0 : Blocks := edgeBlocks% "full/vectors/0000010101011-E-0000.bin"
private noncomputable def ep0000010101011_1 : Blocks := edgeBlocks% "full/vectors/0000010101011-E-0001.bin"
noncomputable def ep0000010101011 : Blocks := (Blocks.join ep0000010101011_0 ep0000010101011_1)
private theorem idp0000010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001010101.list =
    C ((2:ℤ)^172) * horner X vp0000010101011.list + horner X ep0000010101011.list := by
  exact edge_identity (B := (2:ℤ)^338) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010101011 : Branch 1 (-169761639/2000000 : ℚ) vp000001010101 := by
  apply branch_checked idp0000010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-169761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-170761639/1000000 : ℚ) by norm_num]
  exact coverp0000010101011
theorem coverp000001010101 : Covers (-169761639/2000000 : ℚ) vp000001010101 := join_branches bp0000010101010 bp0000010101011
private noncomputable def vp00000101010011_0 : Blocks := edgeBlocks% "full/vectors/00000101010011-V-0000.bin"
noncomputable def vp00000101010011 : Blocks := vp00000101010011_0
theorem coverp00000101010011 : Covers (-169261639/500000 : ℚ) vp00000101010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101010010_0 : Blocks := edgeBlocks% "full/vectors/00000101010010-V-0000.bin"
noncomputable def vp00000101010010 : Blocks := vp00000101010010_0
theorem coverp00000101010010 : Covers (-168761639/500000 : ℚ) vp00000101010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010101001_0 : Blocks := edgeBlocks% "full/vectors/0000010101001-V-0000.bin"
noncomputable def vp0000010101001 : Blocks := vp0000010101001_0
private theorem bp00000101010010 : Branch 0 (-168761639/1000000 : ℚ) vp0000010101001 := by
  apply branch_left_normalized (c:=vp00000101010010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-168761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-168761639/500000 : ℚ) by norm_num]
  exact coverp00000101010010
private noncomputable def ep00000101010011_0 : Blocks := edgeBlocks% "full/vectors/00000101010011-E-0000.bin"
noncomputable def ep00000101010011 : Blocks := ep00000101010011_0
private theorem idp00000101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010101001.list =
    C ((2:ℤ)^94) * horner X vp00000101010011.list + horner X ep00000101010011.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101010011 : Branch 1 (-168761639/1000000 : ℚ) vp0000010101001 := by
  apply branch_checked idp00000101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-168761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-169261639/500000 : ℚ) by norm_num]
  exact coverp00000101010011
theorem coverp0000010101001 : Covers (-168761639/1000000 : ℚ) vp0000010101001 := join_branches bp00000101010010 bp00000101010011
private noncomputable def vp00000101010001_0 : Blocks := edgeBlocks% "full/vectors/00000101010001-V-0000.bin"
noncomputable def vp00000101010001 : Blocks := vp00000101010001_0
theorem coverp00000101010001 : Covers (-168261639/500000 : ℚ) vp00000101010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101010000_0 : Blocks := edgeBlocks% "full/vectors/00000101010000-V-0000.bin"
noncomputable def vp00000101010000 : Blocks := vp00000101010000_0
theorem coverp00000101010000 : Covers (-167761639/500000 : ℚ) vp00000101010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010101000_0 : Blocks := edgeBlocks% "full/vectors/0000010101000-V-0000.bin"
noncomputable def vp0000010101000 : Blocks := vp0000010101000_0
private theorem bp00000101010000 : Branch 0 (-167761639/1000000 : ℚ) vp0000010101000 := by
  apply branch_left_normalized (c:=vp00000101010000) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-167761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-167761639/500000 : ℚ) by norm_num]
  exact coverp00000101010000
private noncomputable def ep00000101010001_0 : Blocks := edgeBlocks% "full/vectors/00000101010001-E-0000.bin"
noncomputable def ep00000101010001 : Blocks := ep00000101010001_0
private theorem idp00000101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010101000.list =
    C ((2:ℤ)^93) * horner X vp00000101010001.list + horner X ep00000101010001.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101010001 : Branch 1 (-167761639/1000000 : ℚ) vp0000010101000 := by
  apply branch_checked idp00000101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-167761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-168261639/500000 : ℚ) by norm_num]
  exact coverp00000101010001
theorem coverp0000010101000 : Covers (-167761639/1000000 : ℚ) vp0000010101000 := join_branches bp00000101010000 bp00000101010001
private noncomputable def vp000001010100_0 : Blocks := edgeBlocks% "full/vectors/000001010100-V-0000.bin"
private noncomputable def vp000001010100_1 : Blocks := edgeBlocks% "full/vectors/000001010100-V-0001.bin"
noncomputable def vp000001010100 : Blocks := (Blocks.join vp000001010100_0 vp000001010100_1)
private theorem bp0000010101000 : Branch 0 (-167761639/2000000 : ℚ) vp000001010100 := by
  apply branch_left_normalized (c:=vp0000010101000) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-167761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-167761639/1000000 : ℚ) by norm_num]
  exact coverp0000010101000
private noncomputable def ep0000010101001_0 : Blocks := edgeBlocks% "full/vectors/0000010101001-E-0000.bin"
private noncomputable def ep0000010101001_1 : Blocks := edgeBlocks% "full/vectors/0000010101001-E-0001.bin"
noncomputable def ep0000010101001 : Blocks := (Blocks.join ep0000010101001_0 ep0000010101001_1)
private theorem idp0000010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001010100.list =
    C ((2:ℤ)^172) * horner X vp0000010101001.list + horner X ep0000010101001.list := by
  exact edge_identity (B := (2:ℤ)^337) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010101001 : Branch 1 (-167761639/2000000 : ℚ) vp000001010100 := by
  apply branch_checked idp0000010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-167761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-168761639/1000000 : ℚ) by norm_num]
  exact coverp0000010101001
theorem coverp000001010100 : Covers (-167761639/2000000 : ℚ) vp000001010100 := join_branches bp0000010101000 bp0000010101001
private noncomputable def vp00000101010_0 : Blocks := edgeBlocks% "full/vectors/00000101010-V-0000.bin"
private noncomputable def vp00000101010_1 : Blocks := edgeBlocks% "full/vectors/00000101010-V-0001.bin"
private noncomputable def vp00000101010_2 : Blocks := edgeBlocks% "full/vectors/00000101010-V-0002.bin"
noncomputable def vp00000101010 : Blocks := (Blocks.join vp00000101010_0 (Blocks.join vp00000101010_1 vp00000101010_2))
private theorem bp000001010100 : Branch 0 (-167761639/4000000 : ℚ) vp00000101010 := by
  apply branch_left_normalized (c:=vp000001010100) (k:=0) (m:=166) (by decide +kernel)
  rw [show 2*(-167761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-167761639/2000000 : ℚ) by norm_num]
  exact coverp000001010100
private noncomputable def ep000001010101_0 : Blocks := edgeBlocks% "full/vectors/000001010101-E-0000.bin"
private noncomputable def ep000001010101_1 : Blocks := edgeBlocks% "full/vectors/000001010101-E-0001.bin"
private noncomputable def ep000001010101_2 : Blocks := edgeBlocks% "full/vectors/000001010101-E-0002.bin"
noncomputable def ep000001010101 : Blocks := (Blocks.join ep000001010101_0 (Blocks.join ep000001010101_1 ep000001010101_2))
private theorem idp000001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101010.list =
    C ((2:ℤ)^328) * horner X vp000001010101.list + horner X ep000001010101.list := by
  exact edge_identity (B := (2:ℤ)^568) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001010101 : Branch 1 (-167761639/4000000 : ℚ) vp00000101010 := by
  apply branch_checked idp000001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-167761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-169761639/2000000 : ℚ) by norm_num]
  exact coverp000001010101
theorem coverp00000101010 : Covers (-167761639/4000000 : ℚ) vp00000101010 := join_branches bp000001010100 bp000001010101
private noncomputable def vp0000010101_0 : Blocks := edgeBlocks% "full/vectors/0000010101-V-0000.bin"
private noncomputable def vp0000010101_1 : Blocks := edgeBlocks% "full/vectors/0000010101-V-0001.bin"
private noncomputable def vp0000010101_2 : Blocks := edgeBlocks% "full/vectors/0000010101-V-0002.bin"
private noncomputable def vp0000010101_3 : Blocks := edgeBlocks% "full/vectors/0000010101-V-0003.bin"
private noncomputable def vp0000010101_4 : Blocks := edgeBlocks% "full/vectors/0000010101-V-0004.bin"
noncomputable def vp0000010101 : Blocks := (Blocks.join (Blocks.join vp0000010101_0 vp0000010101_1) (Blocks.join vp0000010101_2 (Blocks.join vp0000010101_3 vp0000010101_4)))
private theorem bp00000101010 : Branch 0 (-167761639/8000000 : ℚ) vp0000010101 := by
  apply branch_left_normalized (c:=vp00000101010) (k:=0) (m:=317) (by decide +kernel)
  rw [show 2*(-167761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-167761639/4000000 : ℚ) by norm_num]
  exact coverp00000101010
private noncomputable def ep00000101011_0 : Blocks := edgeBlocks% "full/vectors/00000101011-E-0000.bin"
private noncomputable def ep00000101011_1 : Blocks := edgeBlocks% "full/vectors/00000101011-E-0001.bin"
private noncomputable def ep00000101011_2 : Blocks := edgeBlocks% "full/vectors/00000101011-E-0002.bin"
private noncomputable def ep00000101011_3 : Blocks := edgeBlocks% "full/vectors/00000101011-E-0003.bin"
private noncomputable def ep00000101011_4 : Blocks := edgeBlocks% "full/vectors/00000101011-E-0004.bin"
noncomputable def ep00000101011 : Blocks := (Blocks.join (Blocks.join ep00000101011_0 ep00000101011_1) (Blocks.join ep00000101011_2 (Blocks.join ep00000101011_3 ep00000101011_4)))
private theorem idp00000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010101.list =
    C ((2:ℤ)^637) * horner X vp00000101011.list + horner X ep00000101011.list := by
  exact edge_identity (B := (2:ℤ)^1027) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101011 : Branch 1 (-167761639/8000000 : ℚ) vp0000010101 := by
  apply branch_checked idp00000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-167761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-171761639/4000000 : ℚ) by norm_num]
  exact coverp00000101011
theorem coverp0000010101 : Covers (-167761639/8000000 : ℚ) vp0000010101 := join_branches bp00000101010 bp00000101011
private noncomputable def vp00000101001111_0 : Blocks := edgeBlocks% "full/vectors/00000101001111-V-0000.bin"
noncomputable def vp00000101001111 : Blocks := vp00000101001111_0
theorem coverp00000101001111 : Covers (-167261639/500000 : ℚ) vp00000101001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101001110_0 : Blocks := edgeBlocks% "full/vectors/00000101001110-V-0000.bin"
noncomputable def vp00000101001110 : Blocks := vp00000101001110_0
theorem coverp00000101001110 : Covers (-166761639/500000 : ℚ) vp00000101001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010100111_0 : Blocks := edgeBlocks% "full/vectors/0000010100111-V-0000.bin"
noncomputable def vp0000010100111 : Blocks := vp0000010100111_0
private theorem bp00000101001110 : Branch 0 (-166761639/1000000 : ℚ) vp0000010100111 := by
  apply branch_left_normalized (c:=vp00000101001110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-166761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-166761639/500000 : ℚ) by norm_num]
  exact coverp00000101001110
private noncomputable def ep00000101001111_0 : Blocks := edgeBlocks% "full/vectors/00000101001111-E-0000.bin"
noncomputable def ep00000101001111 : Blocks := ep00000101001111_0
private theorem idp00000101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010100111.list =
    C ((2:ℤ)^94) * horner X vp00000101001111.list + horner X ep00000101001111.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101001111 : Branch 1 (-166761639/1000000 : ℚ) vp0000010100111 := by
  apply branch_checked idp00000101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-166761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-167261639/500000 : ℚ) by norm_num]
  exact coverp00000101001111
theorem coverp0000010100111 : Covers (-166761639/1000000 : ℚ) vp0000010100111 := join_branches bp00000101001110 bp00000101001111
private noncomputable def vp00000101001101_0 : Blocks := edgeBlocks% "full/vectors/00000101001101-V-0000.bin"
noncomputable def vp00000101001101 : Blocks := vp00000101001101_0
theorem coverp00000101001101 : Covers (-166261639/500000 : ℚ) vp00000101001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101001100_0 : Blocks := edgeBlocks% "full/vectors/00000101001100-V-0000.bin"
noncomputable def vp00000101001100 : Blocks := vp00000101001100_0
theorem coverp00000101001100 : Covers (-165761639/500000 : ℚ) vp00000101001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010100110_0 : Blocks := edgeBlocks% "full/vectors/0000010100110-V-0000.bin"
noncomputable def vp0000010100110 : Blocks := vp0000010100110_0
private theorem bp00000101001100 : Branch 0 (-165761639/1000000 : ℚ) vp0000010100110 := by
  apply branch_left_normalized (c:=vp00000101001100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-165761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-165761639/500000 : ℚ) by norm_num]
  exact coverp00000101001100
private noncomputable def ep00000101001101_0 : Blocks := edgeBlocks% "full/vectors/00000101001101-E-0000.bin"
noncomputable def ep00000101001101 : Blocks := ep00000101001101_0
private theorem idp00000101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010100110.list =
    C ((2:ℤ)^94) * horner X vp00000101001101.list + horner X ep00000101001101.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101001101 : Branch 1 (-165761639/1000000 : ℚ) vp0000010100110 := by
  apply branch_checked idp00000101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-165761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-166261639/500000 : ℚ) by norm_num]
  exact coverp00000101001101
theorem coverp0000010100110 : Covers (-165761639/1000000 : ℚ) vp0000010100110 := join_branches bp00000101001100 bp00000101001101
private noncomputable def vp000001010011_0 : Blocks := edgeBlocks% "full/vectors/000001010011-V-0000.bin"
private noncomputable def vp000001010011_1 : Blocks := edgeBlocks% "full/vectors/000001010011-V-0001.bin"
noncomputable def vp000001010011 : Blocks := (Blocks.join vp000001010011_0 vp000001010011_1)
private theorem bp0000010100110 : Branch 0 (-165761639/2000000 : ℚ) vp000001010011 := by
  apply branch_left_normalized (c:=vp0000010100110) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-165761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-165761639/1000000 : ℚ) by norm_num]
  exact coverp0000010100110
private noncomputable def ep0000010100111_0 : Blocks := edgeBlocks% "full/vectors/0000010100111-E-0000.bin"
private noncomputable def ep0000010100111_1 : Blocks := edgeBlocks% "full/vectors/0000010100111-E-0001.bin"
noncomputable def ep0000010100111 : Blocks := (Blocks.join ep0000010100111_0 ep0000010100111_1)
private theorem idp0000010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001010011.list =
    C ((2:ℤ)^173) * horner X vp0000010100111.list + horner X ep0000010100111.list := by
  exact edge_identity (B := (2:ℤ)^338) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010100111 : Branch 1 (-165761639/2000000 : ℚ) vp000001010011 := by
  apply branch_checked idp0000010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-165761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-166761639/1000000 : ℚ) by norm_num]
  exact coverp0000010100111
theorem coverp000001010011 : Covers (-165761639/2000000 : ℚ) vp000001010011 := join_branches bp0000010100110 bp0000010100111
private noncomputable def vp00000101001011_0 : Blocks := edgeBlocks% "full/vectors/00000101001011-V-0000.bin"
noncomputable def vp00000101001011 : Blocks := vp00000101001011_0
theorem coverp00000101001011 : Covers (-165261639/500000 : ℚ) vp00000101001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101001010_0 : Blocks := edgeBlocks% "full/vectors/00000101001010-V-0000.bin"
noncomputable def vp00000101001010 : Blocks := vp00000101001010_0
theorem coverp00000101001010 : Covers (-164761639/500000 : ℚ) vp00000101001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010100101_0 : Blocks := edgeBlocks% "full/vectors/0000010100101-V-0000.bin"
noncomputable def vp0000010100101 : Blocks := vp0000010100101_0
private theorem bp00000101001010 : Branch 0 (-164761639/1000000 : ℚ) vp0000010100101 := by
  apply branch_left_normalized (c:=vp00000101001010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-164761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-164761639/500000 : ℚ) by norm_num]
  exact coverp00000101001010
private noncomputable def ep00000101001011_0 : Blocks := edgeBlocks% "full/vectors/00000101001011-E-0000.bin"
noncomputable def ep00000101001011 : Blocks := ep00000101001011_0
private theorem idp00000101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010100101.list =
    C ((2:ℤ)^94) * horner X vp00000101001011.list + horner X ep00000101001011.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101001011 : Branch 1 (-164761639/1000000 : ℚ) vp0000010100101 := by
  apply branch_checked idp00000101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-164761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-165261639/500000 : ℚ) by norm_num]
  exact coverp00000101001011
theorem coverp0000010100101 : Covers (-164761639/1000000 : ℚ) vp0000010100101 := join_branches bp00000101001010 bp00000101001011
private noncomputable def vp00000101001001_0 : Blocks := edgeBlocks% "full/vectors/00000101001001-V-0000.bin"
noncomputable def vp00000101001001 : Blocks := vp00000101001001_0
theorem coverp00000101001001 : Covers (-164261639/500000 : ℚ) vp00000101001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101001000_0 : Blocks := edgeBlocks% "full/vectors/00000101001000-V-0000.bin"
noncomputable def vp00000101001000 : Blocks := vp00000101001000_0
theorem coverp00000101001000 : Covers (-163761639/500000 : ℚ) vp00000101001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010100100_0 : Blocks := edgeBlocks% "full/vectors/0000010100100-V-0000.bin"
noncomputable def vp0000010100100 : Blocks := vp0000010100100_0
private theorem bp00000101001000 : Branch 0 (-163761639/1000000 : ℚ) vp0000010100100 := by
  apply branch_left_normalized (c:=vp00000101001000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-163761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-163761639/500000 : ℚ) by norm_num]
  exact coverp00000101001000
private noncomputable def ep00000101001001_0 : Blocks := edgeBlocks% "full/vectors/00000101001001-E-0000.bin"
noncomputable def ep00000101001001 : Blocks := ep00000101001001_0
private theorem idp00000101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010100100.list =
    C ((2:ℤ)^95) * horner X vp00000101001001.list + horner X ep00000101001001.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101001001 : Branch 1 (-163761639/1000000 : ℚ) vp0000010100100 := by
  apply branch_checked idp00000101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-163761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-164261639/500000 : ℚ) by norm_num]
  exact coverp00000101001001
theorem coverp0000010100100 : Covers (-163761639/1000000 : ℚ) vp0000010100100 := join_branches bp00000101001000 bp00000101001001
private noncomputable def vp000001010010_0 : Blocks := edgeBlocks% "full/vectors/000001010010-V-0000.bin"
private noncomputable def vp000001010010_1 : Blocks := edgeBlocks% "full/vectors/000001010010-V-0001.bin"
noncomputable def vp000001010010 : Blocks := (Blocks.join vp000001010010_0 vp000001010010_1)
private theorem bp0000010100100 : Branch 0 (-163761639/2000000 : ℚ) vp000001010010 := by
  apply branch_left_normalized (c:=vp0000010100100) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-163761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-163761639/1000000 : ℚ) by norm_num]
  exact coverp0000010100100
private noncomputable def ep0000010100101_0 : Blocks := edgeBlocks% "full/vectors/0000010100101-E-0000.bin"
private noncomputable def ep0000010100101_1 : Blocks := edgeBlocks% "full/vectors/0000010100101-E-0001.bin"
noncomputable def ep0000010100101 : Blocks := (Blocks.join ep0000010100101_0 ep0000010100101_1)
private theorem idp0000010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001010010.list =
    C ((2:ℤ)^175) * horner X vp0000010100101.list + horner X ep0000010100101.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010100101 : Branch 1 (-163761639/2000000 : ℚ) vp000001010010 := by
  apply branch_checked idp0000010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-163761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-164761639/1000000 : ℚ) by norm_num]
  exact coverp0000010100101
theorem coverp000001010010 : Covers (-163761639/2000000 : ℚ) vp000001010010 := join_branches bp0000010100100 bp0000010100101
private noncomputable def vp00000101001_0 : Blocks := edgeBlocks% "full/vectors/00000101001-V-0000.bin"
private noncomputable def vp00000101001_1 : Blocks := edgeBlocks% "full/vectors/00000101001-V-0001.bin"
private noncomputable def vp00000101001_2 : Blocks := edgeBlocks% "full/vectors/00000101001-V-0002.bin"
noncomputable def vp00000101001 : Blocks := (Blocks.join vp00000101001_0 (Blocks.join vp00000101001_1 vp00000101001_2))
private theorem bp000001010010 : Branch 0 (-163761639/4000000 : ℚ) vp00000101001 := by
  apply branch_left_normalized (c:=vp000001010010) (k:=0) (m:=168) (by decide +kernel)
  rw [show 2*(-163761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-163761639/2000000 : ℚ) by norm_num]
  exact coverp000001010010
private noncomputable def ep000001010011_0 : Blocks := edgeBlocks% "full/vectors/000001010011-E-0000.bin"
private noncomputable def ep000001010011_1 : Blocks := edgeBlocks% "full/vectors/000001010011-E-0001.bin"
private noncomputable def ep000001010011_2 : Blocks := edgeBlocks% "full/vectors/000001010011-E-0002.bin"
noncomputable def ep000001010011 : Blocks := (Blocks.join ep000001010011_0 (Blocks.join ep000001010011_1 ep000001010011_2))
private theorem idp000001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101001.list =
    C ((2:ℤ)^333) * horner X vp000001010011.list + horner X ep000001010011.list := by
  exact edge_identity (B := (2:ℤ)^574) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001010011 : Branch 1 (-163761639/4000000 : ℚ) vp00000101001 := by
  apply branch_checked idp000001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-163761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-165761639/2000000 : ℚ) by norm_num]
  exact coverp000001010011
theorem coverp00000101001 : Covers (-163761639/4000000 : ℚ) vp00000101001 := join_branches bp000001010010 bp000001010011
private noncomputable def vp00000101000111_0 : Blocks := edgeBlocks% "full/vectors/00000101000111-V-0000.bin"
noncomputable def vp00000101000111 : Blocks := vp00000101000111_0
theorem coverp00000101000111 : Covers (-163261639/500000 : ℚ) vp00000101000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101000110_0 : Blocks := edgeBlocks% "full/vectors/00000101000110-V-0000.bin"
noncomputable def vp00000101000110 : Blocks := vp00000101000110_0
theorem coverp00000101000110 : Covers (-162761639/500000 : ℚ) vp00000101000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010100011_0 : Blocks := edgeBlocks% "full/vectors/0000010100011-V-0000.bin"
noncomputable def vp0000010100011 : Blocks := vp0000010100011_0
private theorem bp00000101000110 : Branch 0 (-162761639/1000000 : ℚ) vp0000010100011 := by
  apply branch_left_normalized (c:=vp00000101000110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-162761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-162761639/500000 : ℚ) by norm_num]
  exact coverp00000101000110
private noncomputable def ep00000101000111_0 : Blocks := edgeBlocks% "full/vectors/00000101000111-E-0000.bin"
noncomputable def ep00000101000111 : Blocks := ep00000101000111_0
private theorem idp00000101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010100011.list =
    C ((2:ℤ)^96) * horner X vp00000101000111.list + horner X ep00000101000111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101000111 : Branch 1 (-162761639/1000000 : ℚ) vp0000010100011 := by
  apply branch_checked idp00000101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-162761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-163261639/500000 : ℚ) by norm_num]
  exact coverp00000101000111
theorem coverp0000010100011 : Covers (-162761639/1000000 : ℚ) vp0000010100011 := join_branches bp00000101000110 bp00000101000111
private noncomputable def vp00000101000101_0 : Blocks := edgeBlocks% "full/vectors/00000101000101-V-0000.bin"
noncomputable def vp00000101000101 : Blocks := vp00000101000101_0
theorem coverp00000101000101 : Covers (-162261639/500000 : ℚ) vp00000101000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101000100_0 : Blocks := edgeBlocks% "full/vectors/00000101000100-V-0000.bin"
noncomputable def vp00000101000100 : Blocks := vp00000101000100_0
theorem coverp00000101000100 : Covers (-161761639/500000 : ℚ) vp00000101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010100010_0 : Blocks := edgeBlocks% "full/vectors/0000010100010-V-0000.bin"
noncomputable def vp0000010100010 : Blocks := vp0000010100010_0
private theorem bp00000101000100 : Branch 0 (-161761639/1000000 : ℚ) vp0000010100010 := by
  apply branch_left_normalized (c:=vp00000101000100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-161761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-161761639/500000 : ℚ) by norm_num]
  exact coverp00000101000100
private noncomputable def ep00000101000101_0 : Blocks := edgeBlocks% "full/vectors/00000101000101-E-0000.bin"
noncomputable def ep00000101000101 : Blocks := ep00000101000101_0
private theorem idp00000101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010100010.list =
    C ((2:ℤ)^96) * horner X vp00000101000101.list + horner X ep00000101000101.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101000101 : Branch 1 (-161761639/1000000 : ℚ) vp0000010100010 := by
  apply branch_checked idp00000101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-161761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-162261639/500000 : ℚ) by norm_num]
  exact coverp00000101000101
theorem coverp0000010100010 : Covers (-161761639/1000000 : ℚ) vp0000010100010 := join_branches bp00000101000100 bp00000101000101
private noncomputable def vp000001010001_0 : Blocks := edgeBlocks% "full/vectors/000001010001-V-0000.bin"
private noncomputable def vp000001010001_1 : Blocks := edgeBlocks% "full/vectors/000001010001-V-0001.bin"
noncomputable def vp000001010001 : Blocks := (Blocks.join vp000001010001_0 vp000001010001_1)
private theorem bp0000010100010 : Branch 0 (-161761639/2000000 : ℚ) vp000001010001 := by
  apply branch_left_normalized (c:=vp0000010100010) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-161761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-161761639/1000000 : ℚ) by norm_num]
  exact coverp0000010100010
private noncomputable def ep0000010100011_0 : Blocks := edgeBlocks% "full/vectors/0000010100011-E-0000.bin"
private noncomputable def ep0000010100011_1 : Blocks := edgeBlocks% "full/vectors/0000010100011-E-0001.bin"
noncomputable def ep0000010100011 : Blocks := (Blocks.join ep0000010100011_0 ep0000010100011_1)
private theorem idp0000010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001010001.list =
    C ((2:ℤ)^177) * horner X vp0000010100011.list + horner X ep0000010100011.list := by
  exact edge_identity (B := (2:ℤ)^344) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010100011 : Branch 1 (-161761639/2000000 : ℚ) vp000001010001 := by
  apply branch_checked idp0000010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-161761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-162761639/1000000 : ℚ) by norm_num]
  exact coverp0000010100011
theorem coverp000001010001 : Covers (-161761639/2000000 : ℚ) vp000001010001 := join_branches bp0000010100010 bp0000010100011
private noncomputable def vp00000101000011_0 : Blocks := edgeBlocks% "full/vectors/00000101000011-V-0000.bin"
noncomputable def vp00000101000011 : Blocks := vp00000101000011_0
theorem coverp00000101000011 : Covers (-161261639/500000 : ℚ) vp00000101000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101000010_0 : Blocks := edgeBlocks% "full/vectors/00000101000010-V-0000.bin"
noncomputable def vp00000101000010 : Blocks := vp00000101000010_0
theorem coverp00000101000010 : Covers (-160761639/500000 : ℚ) vp00000101000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010100001_0 : Blocks := edgeBlocks% "full/vectors/0000010100001-V-0000.bin"
noncomputable def vp0000010100001 : Blocks := vp0000010100001_0
private theorem bp00000101000010 : Branch 0 (-160761639/1000000 : ℚ) vp0000010100001 := by
  apply branch_left_normalized (c:=vp00000101000010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-160761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-160761639/500000 : ℚ) by norm_num]
  exact coverp00000101000010
private noncomputable def ep00000101000011_0 : Blocks := edgeBlocks% "full/vectors/00000101000011-E-0000.bin"
noncomputable def ep00000101000011 : Blocks := ep00000101000011_0
private theorem idp00000101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010100001.list =
    C ((2:ℤ)^97) * horner X vp00000101000011.list + horner X ep00000101000011.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101000011 : Branch 1 (-160761639/1000000 : ℚ) vp0000010100001 := by
  apply branch_checked idp00000101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-160761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-161261639/500000 : ℚ) by norm_num]
  exact coverp00000101000011
theorem coverp0000010100001 : Covers (-160761639/1000000 : ℚ) vp0000010100001 := join_branches bp00000101000010 bp00000101000011
private noncomputable def vp00000101000001_0 : Blocks := edgeBlocks% "full/vectors/00000101000001-V-0000.bin"
noncomputable def vp00000101000001 : Blocks := vp00000101000001_0
theorem coverp00000101000001 : Covers (-160261639/500000 : ℚ) vp00000101000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000101000000_0 : Blocks := edgeBlocks% "full/vectors/00000101000000-V-0000.bin"
noncomputable def vp00000101000000 : Blocks := vp00000101000000_0
theorem coverp00000101000000 : Covers (-159761639/500000 : ℚ) vp00000101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010100000_0 : Blocks := edgeBlocks% "full/vectors/0000010100000-V-0000.bin"
noncomputable def vp0000010100000 : Blocks := vp0000010100000_0
private theorem bp00000101000000 : Branch 0 (-159761639/1000000 : ℚ) vp0000010100000 := by
  apply branch_left_normalized (c:=vp00000101000000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-159761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-159761639/500000 : ℚ) by norm_num]
  exact coverp00000101000000
private noncomputable def ep00000101000001_0 : Blocks := edgeBlocks% "full/vectors/00000101000001-E-0000.bin"
noncomputable def ep00000101000001 : Blocks := ep00000101000001_0
private theorem idp00000101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010100000.list =
    C ((2:ℤ)^97) * horner X vp00000101000001.list + horner X ep00000101000001.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101000001 : Branch 1 (-159761639/1000000 : ℚ) vp0000010100000 := by
  apply branch_checked idp00000101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-159761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-160261639/500000 : ℚ) by norm_num]
  exact coverp00000101000001
theorem coverp0000010100000 : Covers (-159761639/1000000 : ℚ) vp0000010100000 := join_branches bp00000101000000 bp00000101000001
private noncomputable def vp000001010000_0 : Blocks := edgeBlocks% "full/vectors/000001010000-V-0000.bin"
private noncomputable def vp000001010000_1 : Blocks := edgeBlocks% "full/vectors/000001010000-V-0001.bin"
noncomputable def vp000001010000 : Blocks := (Blocks.join vp000001010000_0 vp000001010000_1)
private theorem bp0000010100000 : Branch 0 (-159761639/2000000 : ℚ) vp000001010000 := by
  apply branch_left_normalized (c:=vp0000010100000) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-159761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-159761639/1000000 : ℚ) by norm_num]
  exact coverp0000010100000
private noncomputable def ep0000010100001_0 : Blocks := edgeBlocks% "full/vectors/0000010100001-E-0000.bin"
private noncomputable def ep0000010100001_1 : Blocks := edgeBlocks% "full/vectors/0000010100001-E-0001.bin"
noncomputable def ep0000010100001 : Blocks := (Blocks.join ep0000010100001_0 ep0000010100001_1)
private theorem idp0000010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001010000.list =
    C ((2:ℤ)^180) * horner X vp0000010100001.list + horner X ep0000010100001.list := by
  exact edge_identity (B := (2:ℤ)^347) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010100001 : Branch 1 (-159761639/2000000 : ℚ) vp000001010000 := by
  apply branch_checked idp0000010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-159761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-160761639/1000000 : ℚ) by norm_num]
  exact coverp0000010100001
theorem coverp000001010000 : Covers (-159761639/2000000 : ℚ) vp000001010000 := join_branches bp0000010100000 bp0000010100001
private noncomputable def vp00000101000_0 : Blocks := edgeBlocks% "full/vectors/00000101000-V-0000.bin"
private noncomputable def vp00000101000_1 : Blocks := edgeBlocks% "full/vectors/00000101000-V-0001.bin"
private noncomputable def vp00000101000_2 : Blocks := edgeBlocks% "full/vectors/00000101000-V-0002.bin"
noncomputable def vp00000101000 : Blocks := (Blocks.join vp00000101000_0 (Blocks.join vp00000101000_1 vp00000101000_2))
private theorem bp000001010000 : Branch 0 (-159761639/4000000 : ℚ) vp00000101000 := by
  apply branch_left_normalized (c:=vp000001010000) (k:=0) (m:=172) (by decide +kernel)
  rw [show 2*(-159761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-159761639/2000000 : ℚ) by norm_num]
  exact coverp000001010000
private noncomputable def ep000001010001_0 : Blocks := edgeBlocks% "full/vectors/000001010001-E-0000.bin"
private noncomputable def ep000001010001_1 : Blocks := edgeBlocks% "full/vectors/000001010001-E-0001.bin"
private noncomputable def ep000001010001_2 : Blocks := edgeBlocks% "full/vectors/000001010001-E-0002.bin"
noncomputable def ep000001010001 : Blocks := (Blocks.join ep000001010001_0 (Blocks.join ep000001010001_1 ep000001010001_2))
private theorem idp000001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101000.list =
    C ((2:ℤ)^341) * horner X vp000001010001.list + horner X ep000001010001.list := by
  exact edge_identity (B := (2:ℤ)^585) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001010001 : Branch 1 (-159761639/4000000 : ℚ) vp00000101000 := by
  apply branch_checked idp000001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-159761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-161761639/2000000 : ℚ) by norm_num]
  exact coverp000001010001
theorem coverp00000101000 : Covers (-159761639/4000000 : ℚ) vp00000101000 := join_branches bp000001010000 bp000001010001
private noncomputable def vp0000010100_0 : Blocks := edgeBlocks% "full/vectors/0000010100-V-0000.bin"
private noncomputable def vp0000010100_1 : Blocks := edgeBlocks% "full/vectors/0000010100-V-0001.bin"
private noncomputable def vp0000010100_2 : Blocks := edgeBlocks% "full/vectors/0000010100-V-0002.bin"
private noncomputable def vp0000010100_3 : Blocks := edgeBlocks% "full/vectors/0000010100-V-0003.bin"
private noncomputable def vp0000010100_4 : Blocks := edgeBlocks% "full/vectors/0000010100-V-0004.bin"
noncomputable def vp0000010100 : Blocks := (Blocks.join (Blocks.join vp0000010100_0 vp0000010100_1) (Blocks.join vp0000010100_2 (Blocks.join vp0000010100_3 vp0000010100_4)))
private theorem bp00000101000 : Branch 0 (-159761639/8000000 : ℚ) vp0000010100 := by
  apply branch_left_normalized (c:=vp00000101000) (k:=0) (m:=327) (by decide +kernel)
  rw [show 2*(-159761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-159761639/4000000 : ℚ) by norm_num]
  exact coverp00000101000
private noncomputable def ep00000101001_0 : Blocks := edgeBlocks% "full/vectors/00000101001-E-0000.bin"
private noncomputable def ep00000101001_1 : Blocks := edgeBlocks% "full/vectors/00000101001-E-0001.bin"
private noncomputable def ep00000101001_2 : Blocks := edgeBlocks% "full/vectors/00000101001-E-0002.bin"
private noncomputable def ep00000101001_3 : Blocks := edgeBlocks% "full/vectors/00000101001-E-0003.bin"
private noncomputable def ep00000101001_4 : Blocks := edgeBlocks% "full/vectors/00000101001-E-0004.bin"
noncomputable def ep00000101001 : Blocks := (Blocks.join (Blocks.join ep00000101001_0 ep00000101001_1) (Blocks.join ep00000101001_2 (Blocks.join ep00000101001_3 ep00000101001_4)))
private theorem idp00000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010100.list =
    C ((2:ℤ)^660) * horner X vp00000101001.list + horner X ep00000101001.list := by
  exact edge_identity (B := (2:ℤ)^1055) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000101001 : Branch 1 (-159761639/8000000 : ℚ) vp0000010100 := by
  apply branch_checked idp00000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-159761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-163761639/4000000 : ℚ) by norm_num]
  exact coverp00000101001
theorem coverp0000010100 : Covers (-159761639/8000000 : ℚ) vp0000010100 := join_branches bp00000101000 bp00000101001
private noncomputable def vp000001010_0 : Blocks := edgeBlocks% "full/vectors/000001010-V-0000.bin"
private noncomputable def vp000001010_1 : Blocks := edgeBlocks% "full/vectors/000001010-V-0001.bin"
private noncomputable def vp000001010_2 : Blocks := edgeBlocks% "full/vectors/000001010-V-0002.bin"
private noncomputable def vp000001010_3 : Blocks := edgeBlocks% "full/vectors/000001010-V-0003.bin"
private noncomputable def vp000001010_4 : Blocks := edgeBlocks% "full/vectors/000001010-V-0004.bin"
private noncomputable def vp000001010_5 : Blocks := edgeBlocks% "full/vectors/000001010-V-0005.bin"
private noncomputable def vp000001010_6 : Blocks := edgeBlocks% "full/vectors/000001010-V-0006.bin"
private noncomputable def vp000001010_7 : Blocks := edgeBlocks% "full/vectors/000001010-V-0007.bin"
private noncomputable def vp000001010_8 : Blocks := edgeBlocks% "full/vectors/000001010-V-0008.bin"
private noncomputable def vp000001010_9 : Blocks := edgeBlocks% "full/vectors/000001010-V-0009.bin"
noncomputable def vp000001010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000001010_0 vp000001010_1) (Blocks.join vp000001010_2 (Blocks.join vp000001010_3 vp000001010_4))) (Blocks.join (Blocks.join vp000001010_5 vp000001010_6) (Blocks.join vp000001010_7 (Blocks.join vp000001010_8 vp000001010_9))))
private theorem bp0000010100 : Branch 0 (-159761639/16000000 : ℚ) vp000001010 := by
  apply branch_left_normalized (c:=vp0000010100) (k:=0) (m:=633) (by decide +kernel)
  rw [show 2*(-159761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-159761639/8000000 : ℚ) by norm_num]
  exact coverp0000010100
private noncomputable def ep0000010101_0 : Blocks := edgeBlocks% "full/vectors/0000010101-E-0000.bin"
private noncomputable def ep0000010101_1 : Blocks := edgeBlocks% "full/vectors/0000010101-E-0001.bin"
private noncomputable def ep0000010101_2 : Blocks := edgeBlocks% "full/vectors/0000010101-E-0002.bin"
private noncomputable def ep0000010101_3 : Blocks := edgeBlocks% "full/vectors/0000010101-E-0003.bin"
private noncomputable def ep0000010101_4 : Blocks := edgeBlocks% "full/vectors/0000010101-E-0004.bin"
private noncomputable def ep0000010101_5 : Blocks := edgeBlocks% "full/vectors/0000010101-E-0005.bin"
private noncomputable def ep0000010101_6 : Blocks := edgeBlocks% "full/vectors/0000010101-E-0006.bin"
private noncomputable def ep0000010101_7 : Blocks := edgeBlocks% "full/vectors/0000010101-E-0007.bin"
private noncomputable def ep0000010101_8 : Blocks := edgeBlocks% "full/vectors/0000010101-E-0008.bin"
private noncomputable def ep0000010101_9 : Blocks := edgeBlocks% "full/vectors/0000010101-E-0009.bin"
noncomputable def ep0000010101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000010101_0 ep0000010101_1) (Blocks.join ep0000010101_2 (Blocks.join ep0000010101_3 ep0000010101_4))) (Blocks.join (Blocks.join ep0000010101_5 ep0000010101_6) (Blocks.join ep0000010101_7 (Blocks.join ep0000010101_8 ep0000010101_9))))
private theorem idp0000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001010.list =
    C ((2:ℤ)^1287) * horner X vp0000010101.list + horner X ep0000010101.list := by
  exact edge_identity (B := (2:ℤ)^1986) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010101 : Branch 1 (-159761639/16000000 : ℚ) vp000001010 := by
  apply branch_checked idp0000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-159761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-167761639/8000000 : ℚ) by norm_num]
  exact coverp0000010101
theorem coverp000001010 : Covers (-159761639/16000000 : ℚ) vp000001010 := join_branches bp0000010100 bp0000010101
private noncomputable def vp00000101_0 : Blocks := edgeBlocks% "full/vectors/00000101-V-0000.bin"
private noncomputable def vp00000101_1 : Blocks := edgeBlocks% "full/vectors/00000101-V-0001.bin"
private noncomputable def vp00000101_2 : Blocks := edgeBlocks% "full/vectors/00000101-V-0002.bin"
private noncomputable def vp00000101_3 : Blocks := edgeBlocks% "full/vectors/00000101-V-0003.bin"
private noncomputable def vp00000101_4 : Blocks := edgeBlocks% "full/vectors/00000101-V-0004.bin"
private noncomputable def vp00000101_5 : Blocks := edgeBlocks% "full/vectors/00000101-V-0005.bin"
private noncomputable def vp00000101_6 : Blocks := edgeBlocks% "full/vectors/00000101-V-0006.bin"
private noncomputable def vp00000101_7 : Blocks := edgeBlocks% "full/vectors/00000101-V-0007.bin"
private noncomputable def vp00000101_8 : Blocks := edgeBlocks% "full/vectors/00000101-V-0008.bin"
private noncomputable def vp00000101_9 : Blocks := edgeBlocks% "full/vectors/00000101-V-0009.bin"
private noncomputable def vp00000101_10 : Blocks := edgeBlocks% "full/vectors/00000101-V-0010.bin"
private noncomputable def vp00000101_11 : Blocks := edgeBlocks% "full/vectors/00000101-V-0011.bin"
private noncomputable def vp00000101_12 : Blocks := edgeBlocks% "full/vectors/00000101-V-0012.bin"
private noncomputable def vp00000101_13 : Blocks := edgeBlocks% "full/vectors/00000101-V-0013.bin"
private noncomputable def vp00000101_14 : Blocks := edgeBlocks% "full/vectors/00000101-V-0014.bin"
private noncomputable def vp00000101_15 : Blocks := edgeBlocks% "full/vectors/00000101-V-0015.bin"
private noncomputable def vp00000101_16 : Blocks := edgeBlocks% "full/vectors/00000101-V-0016.bin"
private noncomputable def vp00000101_17 : Blocks := edgeBlocks% "full/vectors/00000101-V-0017.bin"
private noncomputable def vp00000101_18 : Blocks := edgeBlocks% "full/vectors/00000101-V-0018.bin"
noncomputable def vp00000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00000101_0 vp00000101_1) (Blocks.join vp00000101_2 vp00000101_3)) (Blocks.join (Blocks.join vp00000101_4 vp00000101_5) (Blocks.join vp00000101_6 (Blocks.join vp00000101_7 vp00000101_8)))) (Blocks.join (Blocks.join (Blocks.join vp00000101_9 vp00000101_10) (Blocks.join vp00000101_11 (Blocks.join vp00000101_12 vp00000101_13))) (Blocks.join (Blocks.join vp00000101_14 vp00000101_15) (Blocks.join vp00000101_16 (Blocks.join vp00000101_17 vp00000101_18)))))
private theorem bp000001010 : Branch 0 (-159761639/32000000 : ℚ) vp00000101 := by
  apply branch_left_normalized (c:=vp000001010) (k:=0) (m:=1237) (by decide +kernel)
  rw [show 2*(-159761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-159761639/16000000 : ℚ) by norm_num]
  exact coverp000001010
private noncomputable def ep000001011_0 : Blocks := edgeBlocks% "full/vectors/000001011-E-0000.bin"
private noncomputable def ep000001011_1 : Blocks := edgeBlocks% "full/vectors/000001011-E-0001.bin"
private noncomputable def ep000001011_2 : Blocks := edgeBlocks% "full/vectors/000001011-E-0002.bin"
private noncomputable def ep000001011_3 : Blocks := edgeBlocks% "full/vectors/000001011-E-0003.bin"
private noncomputable def ep000001011_4 : Blocks := edgeBlocks% "full/vectors/000001011-E-0004.bin"
private noncomputable def ep000001011_5 : Blocks := edgeBlocks% "full/vectors/000001011-E-0005.bin"
private noncomputable def ep000001011_6 : Blocks := edgeBlocks% "full/vectors/000001011-E-0006.bin"
private noncomputable def ep000001011_7 : Blocks := edgeBlocks% "full/vectors/000001011-E-0007.bin"
private noncomputable def ep000001011_8 : Blocks := edgeBlocks% "full/vectors/000001011-E-0008.bin"
private noncomputable def ep000001011_9 : Blocks := edgeBlocks% "full/vectors/000001011-E-0009.bin"
private noncomputable def ep000001011_10 : Blocks := edgeBlocks% "full/vectors/000001011-E-0010.bin"
private noncomputable def ep000001011_11 : Blocks := edgeBlocks% "full/vectors/000001011-E-0011.bin"
private noncomputable def ep000001011_12 : Blocks := edgeBlocks% "full/vectors/000001011-E-0012.bin"
private noncomputable def ep000001011_13 : Blocks := edgeBlocks% "full/vectors/000001011-E-0013.bin"
private noncomputable def ep000001011_14 : Blocks := edgeBlocks% "full/vectors/000001011-E-0014.bin"
private noncomputable def ep000001011_15 : Blocks := edgeBlocks% "full/vectors/000001011-E-0015.bin"
private noncomputable def ep000001011_16 : Blocks := edgeBlocks% "full/vectors/000001011-E-0016.bin"
private noncomputable def ep000001011_17 : Blocks := edgeBlocks% "full/vectors/000001011-E-0017.bin"
private noncomputable def ep000001011_18 : Blocks := edgeBlocks% "full/vectors/000001011-E-0018.bin"
noncomputable def ep000001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep000001011_0 ep000001011_1) (Blocks.join ep000001011_2 ep000001011_3)) (Blocks.join (Blocks.join ep000001011_4 ep000001011_5) (Blocks.join ep000001011_6 (Blocks.join ep000001011_7 ep000001011_8)))) (Blocks.join (Blocks.join (Blocks.join ep000001011_9 ep000001011_10) (Blocks.join ep000001011_11 (Blocks.join ep000001011_12 ep000001011_13))) (Blocks.join (Blocks.join ep000001011_14 ep000001011_15) (Blocks.join ep000001011_16 (Blocks.join ep000001011_17 ep000001011_18)))))
private theorem idp000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000101.list =
    C ((2:ℤ)^2498) * horner X vp000001011.list + horner X ep000001011.list := by
  exact edge_identity (B := (2:ℤ)^3807) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001011 : Branch 1 (-159761639/32000000 : ℚ) vp00000101 := by
  apply branch_checked idp000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-159761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-175761639/16000000 : ℚ) by norm_num]
  exact coverp000001011
theorem coverp00000101 : Covers (-159761639/32000000 : ℚ) vp00000101 := join_branches bp000001010 bp000001011
end NextProof.EdgeFull

