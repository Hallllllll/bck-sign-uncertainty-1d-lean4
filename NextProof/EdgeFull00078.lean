import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00011011111111_0 : Blocks := edgeBlocks% "full/vectors/00011011111111-V-0000.bin"
noncomputable def vp00011011111111 : Blocks := vp00011011111111_0
theorem coverp00011011111111 : Covers (-895261639/500000 : ℚ) vp00011011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011111110_0 : Blocks := edgeBlocks% "full/vectors/00011011111110-V-0000.bin"
noncomputable def vp00011011111110 : Blocks := vp00011011111110_0
theorem coverp00011011111110 : Covers (-894761639/500000 : ℚ) vp00011011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101111111_0 : Blocks := edgeBlocks% "full/vectors/0001101111111-V-0000.bin"
noncomputable def vp0001101111111 : Blocks := vp0001101111111_0
private theorem bp00011011111110 : Branch 0 (-894761639/1000000 : ℚ) vp0001101111111 := by
  apply branch_left_normalized (c:=vp00011011111110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-894761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-894761639/500000 : ℚ) by norm_num]
  exact coverp00011011111110
private noncomputable def ep00011011111111_0 : Blocks := edgeBlocks% "full/vectors/00011011111111-E-0000.bin"
noncomputable def ep00011011111111 : Blocks := ep00011011111111_0
private theorem idp00011011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101111111.list =
    C ((2:ℤ)^56) * horner X vp00011011111111.list + horner X ep00011011111111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011111111 : Branch 1 (-894761639/1000000 : ℚ) vp0001101111111 := by
  apply branch_checked idp00011011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-894761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-895261639/500000 : ℚ) by norm_num]
  exact coverp00011011111111
theorem coverp0001101111111 : Covers (-894761639/1000000 : ℚ) vp0001101111111 := join_branches bp00011011111110 bp00011011111111
private noncomputable def vp00011011111101_0 : Blocks := edgeBlocks% "full/vectors/00011011111101-V-0000.bin"
noncomputable def vp00011011111101 : Blocks := vp00011011111101_0
theorem coverp00011011111101 : Covers (-894261639/500000 : ℚ) vp00011011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011111100_0 : Blocks := edgeBlocks% "full/vectors/00011011111100-V-0000.bin"
noncomputable def vp00011011111100 : Blocks := vp00011011111100_0
theorem coverp00011011111100 : Covers (-893761639/500000 : ℚ) vp00011011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101111110_0 : Blocks := edgeBlocks% "full/vectors/0001101111110-V-0000.bin"
noncomputable def vp0001101111110 : Blocks := vp0001101111110_0
private theorem bp00011011111100 : Branch 0 (-893761639/1000000 : ℚ) vp0001101111110 := by
  apply branch_left_normalized (c:=vp00011011111100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-893761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-893761639/500000 : ℚ) by norm_num]
  exact coverp00011011111100
private noncomputable def ep00011011111101_0 : Blocks := edgeBlocks% "full/vectors/00011011111101-E-0000.bin"
noncomputable def ep00011011111101 : Blocks := ep00011011111101_0
private theorem idp00011011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101111110.list =
    C ((2:ℤ)^56) * horner X vp00011011111101.list + horner X ep00011011111101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011111101 : Branch 1 (-893761639/1000000 : ℚ) vp0001101111110 := by
  apply branch_checked idp00011011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-893761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-894261639/500000 : ℚ) by norm_num]
  exact coverp00011011111101
theorem coverp0001101111110 : Covers (-893761639/1000000 : ℚ) vp0001101111110 := join_branches bp00011011111100 bp00011011111101
private noncomputable def vp000110111111_0 : Blocks := edgeBlocks% "full/vectors/000110111111-V-0000.bin"
noncomputable def vp000110111111 : Blocks := vp000110111111_0
private theorem bp0001101111110 : Branch 0 (-893761639/2000000 : ℚ) vp000110111111 := by
  apply branch_left_normalized (c:=vp0001101111110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-893761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-893761639/1000000 : ℚ) by norm_num]
  exact coverp0001101111110
private noncomputable def ep0001101111111_0 : Blocks := edgeBlocks% "full/vectors/0001101111111-E-0000.bin"
noncomputable def ep0001101111111 : Blocks := ep0001101111111_0
private theorem idp0001101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110111111.list =
    C ((2:ℤ)^94) * horner X vp0001101111111.list + horner X ep0001101111111.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101111111 : Branch 1 (-893761639/2000000 : ℚ) vp000110111111 := by
  apply branch_checked idp0001101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-893761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-894761639/1000000 : ℚ) by norm_num]
  exact coverp0001101111111
theorem coverp000110111111 : Covers (-893761639/2000000 : ℚ) vp000110111111 := join_branches bp0001101111110 bp0001101111111
private noncomputable def vp0001101111101_0 : Blocks := edgeBlocks% "full/vectors/0001101111101-V-0000.bin"
noncomputable def vp0001101111101 : Blocks := vp0001101111101_0
theorem coverp0001101111101 : Covers (-892761639/1000000 : ℚ) vp0001101111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011111001_0 : Blocks := edgeBlocks% "full/vectors/00011011111001-V-0000.bin"
noncomputable def vp00011011111001 : Blocks := vp00011011111001_0
theorem coverp00011011111001 : Covers (-892261639/500000 : ℚ) vp00011011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011111000_0 : Blocks := edgeBlocks% "full/vectors/00011011111000-V-0000.bin"
noncomputable def vp00011011111000 : Blocks := vp00011011111000_0
theorem coverp00011011111000 : Covers (-891761639/500000 : ℚ) vp00011011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101111100_0 : Blocks := edgeBlocks% "full/vectors/0001101111100-V-0000.bin"
noncomputable def vp0001101111100 : Blocks := vp0001101111100_0
private theorem bp00011011111000 : Branch 0 (-891761639/1000000 : ℚ) vp0001101111100 := by
  apply branch_left_normalized (c:=vp00011011111000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-891761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-891761639/500000 : ℚ) by norm_num]
  exact coverp00011011111000
private noncomputable def ep00011011111001_0 : Blocks := edgeBlocks% "full/vectors/00011011111001-E-0000.bin"
noncomputable def ep00011011111001 : Blocks := ep00011011111001_0
private theorem idp00011011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101111100.list =
    C ((2:ℤ)^56) * horner X vp00011011111001.list + horner X ep00011011111001.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011111001 : Branch 1 (-891761639/1000000 : ℚ) vp0001101111100 := by
  apply branch_checked idp00011011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-891761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-892261639/500000 : ℚ) by norm_num]
  exact coverp00011011111001
theorem coverp0001101111100 : Covers (-891761639/1000000 : ℚ) vp0001101111100 := join_branches bp00011011111000 bp00011011111001
private noncomputable def vp000110111110_0 : Blocks := edgeBlocks% "full/vectors/000110111110-V-0000.bin"
noncomputable def vp000110111110 : Blocks := vp000110111110_0
private theorem bp0001101111100 : Branch 0 (-891761639/2000000 : ℚ) vp000110111110 := by
  apply branch_left_normalized (c:=vp0001101111100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-891761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-891761639/1000000 : ℚ) by norm_num]
  exact coverp0001101111100
private noncomputable def ep0001101111101_0 : Blocks := edgeBlocks% "full/vectors/0001101111101-E-0000.bin"
noncomputable def ep0001101111101 : Blocks := ep0001101111101_0
private theorem idp0001101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110111110.list =
    C ((2:ℤ)^93) * horner X vp0001101111101.list + horner X ep0001101111101.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101111101 : Branch 1 (-891761639/2000000 : ℚ) vp000110111110 := by
  apply branch_checked idp0001101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-891761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-892761639/1000000 : ℚ) by norm_num]
  exact coverp0001101111101
theorem coverp000110111110 : Covers (-891761639/2000000 : ℚ) vp000110111110 := join_branches bp0001101111100 bp0001101111101
private noncomputable def vp00011011111_0 : Blocks := edgeBlocks% "full/vectors/00011011111-V-0000.bin"
private noncomputable def vp00011011111_1 : Blocks := edgeBlocks% "full/vectors/00011011111-V-0001.bin"
noncomputable def vp00011011111 : Blocks := (Blocks.join vp00011011111_0 vp00011011111_1)
private theorem bp000110111110 : Branch 0 (-891761639/4000000 : ℚ) vp00011011111 := by
  apply branch_left_normalized (c:=vp000110111110) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-891761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-891761639/2000000 : ℚ) by norm_num]
  exact coverp000110111110
private noncomputable def ep000110111111_0 : Blocks := edgeBlocks% "full/vectors/000110111111-E-0000.bin"
private noncomputable def ep000110111111_1 : Blocks := edgeBlocks% "full/vectors/000110111111-E-0001.bin"
noncomputable def ep000110111111 : Blocks := (Blocks.join ep000110111111_0 ep000110111111_1)
private theorem idp000110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011011111.list =
    C ((2:ℤ)^167) * horner X vp000110111111.list + horner X ep000110111111.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110111111 : Branch 1 (-891761639/4000000 : ℚ) vp00011011111 := by
  apply branch_checked idp000110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-891761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-893761639/2000000 : ℚ) by norm_num]
  exact coverp000110111111
theorem coverp00011011111 : Covers (-891761639/4000000 : ℚ) vp00011011111 := join_branches bp000110111110 bp000110111111
private noncomputable def vp00011011110111_0 : Blocks := edgeBlocks% "full/vectors/00011011110111-V-0000.bin"
noncomputable def vp00011011110111 : Blocks := vp00011011110111_0
theorem coverp00011011110111 : Covers (-891261639/500000 : ℚ) vp00011011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011110110_0 : Blocks := edgeBlocks% "full/vectors/00011011110110-V-0000.bin"
noncomputable def vp00011011110110 : Blocks := vp00011011110110_0
theorem coverp00011011110110 : Covers (-890761639/500000 : ℚ) vp00011011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101111011_0 : Blocks := edgeBlocks% "full/vectors/0001101111011-V-0000.bin"
noncomputable def vp0001101111011 : Blocks := vp0001101111011_0
private theorem bp00011011110110 : Branch 0 (-890761639/1000000 : ℚ) vp0001101111011 := by
  apply branch_left_normalized (c:=vp00011011110110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-890761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-890761639/500000 : ℚ) by norm_num]
  exact coverp00011011110110
private noncomputable def ep00011011110111_0 : Blocks := edgeBlocks% "full/vectors/00011011110111-E-0000.bin"
noncomputable def ep00011011110111 : Blocks := ep00011011110111_0
private theorem idp00011011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101111011.list =
    C ((2:ℤ)^56) * horner X vp00011011110111.list + horner X ep00011011110111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011110111 : Branch 1 (-890761639/1000000 : ℚ) vp0001101111011 := by
  apply branch_checked idp00011011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-890761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-891261639/500000 : ℚ) by norm_num]
  exact coverp00011011110111
theorem coverp0001101111011 : Covers (-890761639/1000000 : ℚ) vp0001101111011 := join_branches bp00011011110110 bp00011011110111
private noncomputable def vp00011011110101_0 : Blocks := edgeBlocks% "full/vectors/00011011110101-V-0000.bin"
noncomputable def vp00011011110101 : Blocks := vp00011011110101_0
theorem coverp00011011110101 : Covers (-890261639/500000 : ℚ) vp00011011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011110100_0 : Blocks := edgeBlocks% "full/vectors/00011011110100-V-0000.bin"
noncomputable def vp00011011110100 : Blocks := vp00011011110100_0
theorem coverp00011011110100 : Covers (-889761639/500000 : ℚ) vp00011011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101111010_0 : Blocks := edgeBlocks% "full/vectors/0001101111010-V-0000.bin"
noncomputable def vp0001101111010 : Blocks := vp0001101111010_0
private theorem bp00011011110100 : Branch 0 (-889761639/1000000 : ℚ) vp0001101111010 := by
  apply branch_left_normalized (c:=vp00011011110100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-889761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-889761639/500000 : ℚ) by norm_num]
  exact coverp00011011110100
private noncomputable def ep00011011110101_0 : Blocks := edgeBlocks% "full/vectors/00011011110101-E-0000.bin"
noncomputable def ep00011011110101 : Blocks := ep00011011110101_0
private theorem idp00011011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101111010.list =
    C ((2:ℤ)^56) * horner X vp00011011110101.list + horner X ep00011011110101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011110101 : Branch 1 (-889761639/1000000 : ℚ) vp0001101111010 := by
  apply branch_checked idp00011011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-889761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-890261639/500000 : ℚ) by norm_num]
  exact coverp00011011110101
theorem coverp0001101111010 : Covers (-889761639/1000000 : ℚ) vp0001101111010 := join_branches bp00011011110100 bp00011011110101
private noncomputable def vp000110111101_0 : Blocks := edgeBlocks% "full/vectors/000110111101-V-0000.bin"
noncomputable def vp000110111101 : Blocks := vp000110111101_0
private theorem bp0001101111010 : Branch 0 (-889761639/2000000 : ℚ) vp000110111101 := by
  apply branch_left_normalized (c:=vp0001101111010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-889761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-889761639/1000000 : ℚ) by norm_num]
  exact coverp0001101111010
private noncomputable def ep0001101111011_0 : Blocks := edgeBlocks% "full/vectors/0001101111011-E-0000.bin"
noncomputable def ep0001101111011 : Blocks := ep0001101111011_0
private theorem idp0001101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110111101.list =
    C ((2:ℤ)^94) * horner X vp0001101111011.list + horner X ep0001101111011.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101111011 : Branch 1 (-889761639/2000000 : ℚ) vp000110111101 := by
  apply branch_checked idp0001101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-889761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-890761639/1000000 : ℚ) by norm_num]
  exact coverp0001101111011
theorem coverp000110111101 : Covers (-889761639/2000000 : ℚ) vp000110111101 := join_branches bp0001101111010 bp0001101111011
private noncomputable def vp00011011110011_0 : Blocks := edgeBlocks% "full/vectors/00011011110011-V-0000.bin"
noncomputable def vp00011011110011 : Blocks := vp00011011110011_0
theorem coverp00011011110011 : Covers (-889261639/500000 : ℚ) vp00011011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011110010_0 : Blocks := edgeBlocks% "full/vectors/00011011110010-V-0000.bin"
noncomputable def vp00011011110010 : Blocks := vp00011011110010_0
theorem coverp00011011110010 : Covers (-888761639/500000 : ℚ) vp00011011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101111001_0 : Blocks := edgeBlocks% "full/vectors/0001101111001-V-0000.bin"
noncomputable def vp0001101111001 : Blocks := vp0001101111001_0
private theorem bp00011011110010 : Branch 0 (-888761639/1000000 : ℚ) vp0001101111001 := by
  apply branch_left_normalized (c:=vp00011011110010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-888761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-888761639/500000 : ℚ) by norm_num]
  exact coverp00011011110010
private noncomputable def ep00011011110011_0 : Blocks := edgeBlocks% "full/vectors/00011011110011-E-0000.bin"
noncomputable def ep00011011110011 : Blocks := ep00011011110011_0
private theorem idp00011011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101111001.list =
    C ((2:ℤ)^56) * horner X vp00011011110011.list + horner X ep00011011110011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011110011 : Branch 1 (-888761639/1000000 : ℚ) vp0001101111001 := by
  apply branch_checked idp00011011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-888761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-889261639/500000 : ℚ) by norm_num]
  exact coverp00011011110011
theorem coverp0001101111001 : Covers (-888761639/1000000 : ℚ) vp0001101111001 := join_branches bp00011011110010 bp00011011110011
private noncomputable def vp00011011110001_0 : Blocks := edgeBlocks% "full/vectors/00011011110001-V-0000.bin"
noncomputable def vp00011011110001 : Blocks := vp00011011110001_0
theorem coverp00011011110001 : Covers (-888261639/500000 : ℚ) vp00011011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011110000_0 : Blocks := edgeBlocks% "full/vectors/00011011110000-V-0000.bin"
noncomputable def vp00011011110000 : Blocks := vp00011011110000_0
theorem coverp00011011110000 : Covers (-887761639/500000 : ℚ) vp00011011110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101111000_0 : Blocks := edgeBlocks% "full/vectors/0001101111000-V-0000.bin"
noncomputable def vp0001101111000 : Blocks := vp0001101111000_0
private theorem bp00011011110000 : Branch 0 (-887761639/1000000 : ℚ) vp0001101111000 := by
  apply branch_left_normalized (c:=vp00011011110000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-887761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-887761639/500000 : ℚ) by norm_num]
  exact coverp00011011110000
private noncomputable def ep00011011110001_0 : Blocks := edgeBlocks% "full/vectors/00011011110001-E-0000.bin"
noncomputable def ep00011011110001 : Blocks := ep00011011110001_0
private theorem idp00011011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101111000.list =
    C ((2:ℤ)^55) * horner X vp00011011110001.list + horner X ep00011011110001.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011110001 : Branch 1 (-887761639/1000000 : ℚ) vp0001101111000 := by
  apply branch_checked idp00011011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-887761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-888261639/500000 : ℚ) by norm_num]
  exact coverp00011011110001
theorem coverp0001101111000 : Covers (-887761639/1000000 : ℚ) vp0001101111000 := join_branches bp00011011110000 bp00011011110001
private noncomputable def vp000110111100_0 : Blocks := edgeBlocks% "full/vectors/000110111100-V-0000.bin"
noncomputable def vp000110111100 : Blocks := vp000110111100_0
private theorem bp0001101111000 : Branch 0 (-887761639/2000000 : ℚ) vp000110111100 := by
  apply branch_left_normalized (c:=vp0001101111000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-887761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-887761639/1000000 : ℚ) by norm_num]
  exact coverp0001101111000
private noncomputable def ep0001101111001_0 : Blocks := edgeBlocks% "full/vectors/0001101111001-E-0000.bin"
noncomputable def ep0001101111001 : Blocks := ep0001101111001_0
private theorem idp0001101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110111100.list =
    C ((2:ℤ)^93) * horner X vp0001101111001.list + horner X ep0001101111001.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101111001 : Branch 1 (-887761639/2000000 : ℚ) vp000110111100 := by
  apply branch_checked idp0001101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-887761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-888761639/1000000 : ℚ) by norm_num]
  exact coverp0001101111001
theorem coverp000110111100 : Covers (-887761639/2000000 : ℚ) vp000110111100 := join_branches bp0001101111000 bp0001101111001
private noncomputable def vp00011011110_0 : Blocks := edgeBlocks% "full/vectors/00011011110-V-0000.bin"
private noncomputable def vp00011011110_1 : Blocks := edgeBlocks% "full/vectors/00011011110-V-0001.bin"
noncomputable def vp00011011110 : Blocks := (Blocks.join vp00011011110_0 vp00011011110_1)
private theorem bp000110111100 : Branch 0 (-887761639/4000000 : ℚ) vp00011011110 := by
  apply branch_left_normalized (c:=vp000110111100) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-887761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-887761639/2000000 : ℚ) by norm_num]
  exact coverp000110111100
private noncomputable def ep000110111101_0 : Blocks := edgeBlocks% "full/vectors/000110111101-E-0000.bin"
private noncomputable def ep000110111101_1 : Blocks := edgeBlocks% "full/vectors/000110111101-E-0001.bin"
noncomputable def ep000110111101 : Blocks := (Blocks.join ep000110111101_0 ep000110111101_1)
private theorem idp000110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011011110.list =
    C ((2:ℤ)^165) * horner X vp000110111101.list + horner X ep000110111101.list := by
  exact edge_identity (B := (2:ℤ)^325) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110111101 : Branch 1 (-887761639/4000000 : ℚ) vp00011011110 := by
  apply branch_checked idp000110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-887761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-889761639/2000000 : ℚ) by norm_num]
  exact coverp000110111101
theorem coverp00011011110 : Covers (-887761639/4000000 : ℚ) vp00011011110 := join_branches bp000110111100 bp000110111101
private noncomputable def vp0001101111_0 : Blocks := edgeBlocks% "full/vectors/0001101111-V-0000.bin"
private noncomputable def vp0001101111_1 : Blocks := edgeBlocks% "full/vectors/0001101111-V-0001.bin"
private noncomputable def vp0001101111_2 : Blocks := edgeBlocks% "full/vectors/0001101111-V-0002.bin"
noncomputable def vp0001101111 : Blocks := (Blocks.join vp0001101111_0 (Blocks.join vp0001101111_1 vp0001101111_2))
private theorem bp00011011110 : Branch 0 (-887761639/8000000 : ℚ) vp0001101111 := by
  apply branch_left_normalized (c:=vp00011011110) (k:=0) (m:=153) (by decide +kernel)
  rw [show 2*(-887761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-887761639/4000000 : ℚ) by norm_num]
  exact coverp00011011110
private noncomputable def ep00011011111_0 : Blocks := edgeBlocks% "full/vectors/00011011111-E-0000.bin"
private noncomputable def ep00011011111_1 : Blocks := edgeBlocks% "full/vectors/00011011111-E-0001.bin"
private noncomputable def ep00011011111_2 : Blocks := edgeBlocks% "full/vectors/00011011111-E-0002.bin"
noncomputable def ep00011011111 : Blocks := (Blocks.join ep00011011111_0 (Blocks.join ep00011011111_1 ep00011011111_2))
private theorem idp00011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101111.list =
    C ((2:ℤ)^309) * horner X vp00011011111.list + horner X ep00011011111.list := by
  exact edge_identity (B := (2:ℤ)^528) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011111 : Branch 1 (-887761639/8000000 : ℚ) vp0001101111 := by
  apply branch_checked idp00011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-887761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-891761639/4000000 : ℚ) by norm_num]
  exact coverp00011011111
theorem coverp0001101111 : Covers (-887761639/8000000 : ℚ) vp0001101111 := join_branches bp00011011110 bp00011011111
private noncomputable def vp00011011101111_0 : Blocks := edgeBlocks% "full/vectors/00011011101111-V-0000.bin"
noncomputable def vp00011011101111 : Blocks := vp00011011101111_0
theorem coverp00011011101111 : Covers (-887261639/500000 : ℚ) vp00011011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011101110_0 : Blocks := edgeBlocks% "full/vectors/00011011101110-V-0000.bin"
noncomputable def vp00011011101110 : Blocks := vp00011011101110_0
theorem coverp00011011101110 : Covers (-886761639/500000 : ℚ) vp00011011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101110111_0 : Blocks := edgeBlocks% "full/vectors/0001101110111-V-0000.bin"
noncomputable def vp0001101110111 : Blocks := vp0001101110111_0
private theorem bp00011011101110 : Branch 0 (-886761639/1000000 : ℚ) vp0001101110111 := by
  apply branch_left_normalized (c:=vp00011011101110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-886761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-886761639/500000 : ℚ) by norm_num]
  exact coverp00011011101110
private noncomputable def ep00011011101111_0 : Blocks := edgeBlocks% "full/vectors/00011011101111-E-0000.bin"
noncomputable def ep00011011101111 : Blocks := ep00011011101111_0
private theorem idp00011011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101110111.list =
    C ((2:ℤ)^56) * horner X vp00011011101111.list + horner X ep00011011101111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011101111 : Branch 1 (-886761639/1000000 : ℚ) vp0001101110111 := by
  apply branch_checked idp00011011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-886761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-887261639/500000 : ℚ) by norm_num]
  exact coverp00011011101111
theorem coverp0001101110111 : Covers (-886761639/1000000 : ℚ) vp0001101110111 := join_branches bp00011011101110 bp00011011101111
private noncomputable def vp00011011101101_0 : Blocks := edgeBlocks% "full/vectors/00011011101101-V-0000.bin"
noncomputable def vp00011011101101 : Blocks := vp00011011101101_0
theorem coverp00011011101101 : Covers (-886261639/500000 : ℚ) vp00011011101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011101100_0 : Blocks := edgeBlocks% "full/vectors/00011011101100-V-0000.bin"
noncomputable def vp00011011101100 : Blocks := vp00011011101100_0
theorem coverp00011011101100 : Covers (-885761639/500000 : ℚ) vp00011011101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101110110_0 : Blocks := edgeBlocks% "full/vectors/0001101110110-V-0000.bin"
noncomputable def vp0001101110110 : Blocks := vp0001101110110_0
private theorem bp00011011101100 : Branch 0 (-885761639/1000000 : ℚ) vp0001101110110 := by
  apply branch_left_normalized (c:=vp00011011101100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-885761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-885761639/500000 : ℚ) by norm_num]
  exact coverp00011011101100
private noncomputable def ep00011011101101_0 : Blocks := edgeBlocks% "full/vectors/00011011101101-E-0000.bin"
noncomputable def ep00011011101101 : Blocks := ep00011011101101_0
private theorem idp00011011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101110110.list =
    C ((2:ℤ)^56) * horner X vp00011011101101.list + horner X ep00011011101101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011101101 : Branch 1 (-885761639/1000000 : ℚ) vp0001101110110 := by
  apply branch_checked idp00011011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-885761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-886261639/500000 : ℚ) by norm_num]
  exact coverp00011011101101
theorem coverp0001101110110 : Covers (-885761639/1000000 : ℚ) vp0001101110110 := join_branches bp00011011101100 bp00011011101101
private noncomputable def vp000110111011_0 : Blocks := edgeBlocks% "full/vectors/000110111011-V-0000.bin"
noncomputable def vp000110111011 : Blocks := vp000110111011_0
private theorem bp0001101110110 : Branch 0 (-885761639/2000000 : ℚ) vp000110111011 := by
  apply branch_left_normalized (c:=vp0001101110110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-885761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-885761639/1000000 : ℚ) by norm_num]
  exact coverp0001101110110
private noncomputable def ep0001101110111_0 : Blocks := edgeBlocks% "full/vectors/0001101110111-E-0000.bin"
noncomputable def ep0001101110111 : Blocks := ep0001101110111_0
private theorem idp0001101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110111011.list =
    C ((2:ℤ)^94) * horner X vp0001101110111.list + horner X ep0001101110111.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101110111 : Branch 1 (-885761639/2000000 : ℚ) vp000110111011 := by
  apply branch_checked idp0001101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-885761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-886761639/1000000 : ℚ) by norm_num]
  exact coverp0001101110111
theorem coverp000110111011 : Covers (-885761639/2000000 : ℚ) vp000110111011 := join_branches bp0001101110110 bp0001101110111
private noncomputable def vp00011011101011_0 : Blocks := edgeBlocks% "full/vectors/00011011101011-V-0000.bin"
noncomputable def vp00011011101011 : Blocks := vp00011011101011_0
theorem coverp00011011101011 : Covers (-885261639/500000 : ℚ) vp00011011101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011101010_0 : Blocks := edgeBlocks% "full/vectors/00011011101010-V-0000.bin"
noncomputable def vp00011011101010 : Blocks := vp00011011101010_0
theorem coverp00011011101010 : Covers (-884761639/500000 : ℚ) vp00011011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101110101_0 : Blocks := edgeBlocks% "full/vectors/0001101110101-V-0000.bin"
noncomputable def vp0001101110101 : Blocks := vp0001101110101_0
private theorem bp00011011101010 : Branch 0 (-884761639/1000000 : ℚ) vp0001101110101 := by
  apply branch_left_normalized (c:=vp00011011101010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-884761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-884761639/500000 : ℚ) by norm_num]
  exact coverp00011011101010
private noncomputable def ep00011011101011_0 : Blocks := edgeBlocks% "full/vectors/00011011101011-E-0000.bin"
noncomputable def ep00011011101011 : Blocks := ep00011011101011_0
private theorem idp00011011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101110101.list =
    C ((2:ℤ)^56) * horner X vp00011011101011.list + horner X ep00011011101011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011101011 : Branch 1 (-884761639/1000000 : ℚ) vp0001101110101 := by
  apply branch_checked idp00011011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-884761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-885261639/500000 : ℚ) by norm_num]
  exact coverp00011011101011
theorem coverp0001101110101 : Covers (-884761639/1000000 : ℚ) vp0001101110101 := join_branches bp00011011101010 bp00011011101011
private noncomputable def vp00011011101001_0 : Blocks := edgeBlocks% "full/vectors/00011011101001-V-0000.bin"
noncomputable def vp00011011101001 : Blocks := vp00011011101001_0
theorem coverp00011011101001 : Covers (-884261639/500000 : ℚ) vp00011011101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011101000_0 : Blocks := edgeBlocks% "full/vectors/00011011101000-V-0000.bin"
noncomputable def vp00011011101000 : Blocks := vp00011011101000_0
theorem coverp00011011101000 : Covers (-883761639/500000 : ℚ) vp00011011101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101110100_0 : Blocks := edgeBlocks% "full/vectors/0001101110100-V-0000.bin"
noncomputable def vp0001101110100 : Blocks := vp0001101110100_0
private theorem bp00011011101000 : Branch 0 (-883761639/1000000 : ℚ) vp0001101110100 := by
  apply branch_left_normalized (c:=vp00011011101000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-883761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-883761639/500000 : ℚ) by norm_num]
  exact coverp00011011101000
private noncomputable def ep00011011101001_0 : Blocks := edgeBlocks% "full/vectors/00011011101001-E-0000.bin"
noncomputable def ep00011011101001 : Blocks := ep00011011101001_0
private theorem idp00011011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101110100.list =
    C ((2:ℤ)^57) * horner X vp00011011101001.list + horner X ep00011011101001.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011101001 : Branch 1 (-883761639/1000000 : ℚ) vp0001101110100 := by
  apply branch_checked idp00011011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-883761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-884261639/500000 : ℚ) by norm_num]
  exact coverp00011011101001
theorem coverp0001101110100 : Covers (-883761639/1000000 : ℚ) vp0001101110100 := join_branches bp00011011101000 bp00011011101001
private noncomputable def vp000110111010_0 : Blocks := edgeBlocks% "full/vectors/000110111010-V-0000.bin"
noncomputable def vp000110111010 : Blocks := vp000110111010_0
private theorem bp0001101110100 : Branch 0 (-883761639/2000000 : ℚ) vp000110111010 := by
  apply branch_left_normalized (c:=vp0001101110100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-883761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-883761639/1000000 : ℚ) by norm_num]
  exact coverp0001101110100
private noncomputable def ep0001101110101_0 : Blocks := edgeBlocks% "full/vectors/0001101110101-E-0000.bin"
noncomputable def ep0001101110101 : Blocks := ep0001101110101_0
private theorem idp0001101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110111010.list =
    C ((2:ℤ)^94) * horner X vp0001101110101.list + horner X ep0001101110101.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101110101 : Branch 1 (-883761639/2000000 : ℚ) vp000110111010 := by
  apply branch_checked idp0001101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-883761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-884761639/1000000 : ℚ) by norm_num]
  exact coverp0001101110101
theorem coverp000110111010 : Covers (-883761639/2000000 : ℚ) vp000110111010 := join_branches bp0001101110100 bp0001101110101
private noncomputable def vp00011011101_0 : Blocks := edgeBlocks% "full/vectors/00011011101-V-0000.bin"
private noncomputable def vp00011011101_1 : Blocks := edgeBlocks% "full/vectors/00011011101-V-0001.bin"
noncomputable def vp00011011101 : Blocks := (Blocks.join vp00011011101_0 vp00011011101_1)
private theorem bp000110111010 : Branch 0 (-883761639/4000000 : ℚ) vp00011011101 := by
  apply branch_left_normalized (c:=vp000110111010) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-883761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-883761639/2000000 : ℚ) by norm_num]
  exact coverp000110111010
private noncomputable def ep000110111011_0 : Blocks := edgeBlocks% "full/vectors/000110111011-E-0000.bin"
private noncomputable def ep000110111011_1 : Blocks := edgeBlocks% "full/vectors/000110111011-E-0001.bin"
noncomputable def ep000110111011 : Blocks := (Blocks.join ep000110111011_0 ep000110111011_1)
private theorem idp000110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011011101.list =
    C ((2:ℤ)^167) * horner X vp000110111011.list + horner X ep000110111011.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110111011 : Branch 1 (-883761639/4000000 : ℚ) vp00011011101 := by
  apply branch_checked idp000110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-883761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-885761639/2000000 : ℚ) by norm_num]
  exact coverp000110111011
theorem coverp00011011101 : Covers (-883761639/4000000 : ℚ) vp00011011101 := join_branches bp000110111010 bp000110111011
private noncomputable def vp00011011100111_0 : Blocks := edgeBlocks% "full/vectors/00011011100111-V-0000.bin"
noncomputable def vp00011011100111 : Blocks := vp00011011100111_0
theorem coverp00011011100111 : Covers (-883261639/500000 : ℚ) vp00011011100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011100110_0 : Blocks := edgeBlocks% "full/vectors/00011011100110-V-0000.bin"
noncomputable def vp00011011100110 : Blocks := vp00011011100110_0
theorem coverp00011011100110 : Covers (-882761639/500000 : ℚ) vp00011011100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101110011_0 : Blocks := edgeBlocks% "full/vectors/0001101110011-V-0000.bin"
noncomputable def vp0001101110011 : Blocks := vp0001101110011_0
private theorem bp00011011100110 : Branch 0 (-882761639/1000000 : ℚ) vp0001101110011 := by
  apply branch_left_normalized (c:=vp00011011100110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-882761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-882761639/500000 : ℚ) by norm_num]
  exact coverp00011011100110
private noncomputable def ep00011011100111_0 : Blocks := edgeBlocks% "full/vectors/00011011100111-E-0000.bin"
noncomputable def ep00011011100111 : Blocks := ep00011011100111_0
private theorem idp00011011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101110011.list =
    C ((2:ℤ)^56) * horner X vp00011011100111.list + horner X ep00011011100111.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011100111 : Branch 1 (-882761639/1000000 : ℚ) vp0001101110011 := by
  apply branch_checked idp00011011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-882761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-883261639/500000 : ℚ) by norm_num]
  exact coverp00011011100111
theorem coverp0001101110011 : Covers (-882761639/1000000 : ℚ) vp0001101110011 := join_branches bp00011011100110 bp00011011100111
private noncomputable def vp00011011100101_0 : Blocks := edgeBlocks% "full/vectors/00011011100101-V-0000.bin"
noncomputable def vp00011011100101 : Blocks := vp00011011100101_0
theorem coverp00011011100101 : Covers (-882261639/500000 : ℚ) vp00011011100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011100100_0 : Blocks := edgeBlocks% "full/vectors/00011011100100-V-0000.bin"
noncomputable def vp00011011100100 : Blocks := vp00011011100100_0
theorem coverp00011011100100 : Covers (-881761639/500000 : ℚ) vp00011011100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101110010_0 : Blocks := edgeBlocks% "full/vectors/0001101110010-V-0000.bin"
noncomputable def vp0001101110010 : Blocks := vp0001101110010_0
private theorem bp00011011100100 : Branch 0 (-881761639/1000000 : ℚ) vp0001101110010 := by
  apply branch_left_normalized (c:=vp00011011100100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-881761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-881761639/500000 : ℚ) by norm_num]
  exact coverp00011011100100
private noncomputable def ep00011011100101_0 : Blocks := edgeBlocks% "full/vectors/00011011100101-E-0000.bin"
noncomputable def ep00011011100101 : Blocks := ep00011011100101_0
private theorem idp00011011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101110010.list =
    C ((2:ℤ)^56) * horner X vp00011011100101.list + horner X ep00011011100101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011100101 : Branch 1 (-881761639/1000000 : ℚ) vp0001101110010 := by
  apply branch_checked idp00011011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-881761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-882261639/500000 : ℚ) by norm_num]
  exact coverp00011011100101
theorem coverp0001101110010 : Covers (-881761639/1000000 : ℚ) vp0001101110010 := join_branches bp00011011100100 bp00011011100101
private noncomputable def vp000110111001_0 : Blocks := edgeBlocks% "full/vectors/000110111001-V-0000.bin"
noncomputable def vp000110111001 : Blocks := vp000110111001_0
private theorem bp0001101110010 : Branch 0 (-881761639/2000000 : ℚ) vp000110111001 := by
  apply branch_left_normalized (c:=vp0001101110010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-881761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-881761639/1000000 : ℚ) by norm_num]
  exact coverp0001101110010
private noncomputable def ep0001101110011_0 : Blocks := edgeBlocks% "full/vectors/0001101110011-E-0000.bin"
noncomputable def ep0001101110011 : Blocks := ep0001101110011_0
private theorem idp0001101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110111001.list =
    C ((2:ℤ)^93) * horner X vp0001101110011.list + horner X ep0001101110011.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101110011 : Branch 1 (-881761639/2000000 : ℚ) vp000110111001 := by
  apply branch_checked idp0001101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-881761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-882761639/1000000 : ℚ) by norm_num]
  exact coverp0001101110011
theorem coverp000110111001 : Covers (-881761639/2000000 : ℚ) vp000110111001 := join_branches bp0001101110010 bp0001101110011
private noncomputable def vp00011011100011_0 : Blocks := edgeBlocks% "full/vectors/00011011100011-V-0000.bin"
noncomputable def vp00011011100011 : Blocks := vp00011011100011_0
theorem coverp00011011100011 : Covers (-881261639/500000 : ℚ) vp00011011100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011100010_0 : Blocks := edgeBlocks% "full/vectors/00011011100010-V-0000.bin"
noncomputable def vp00011011100010 : Blocks := vp00011011100010_0
theorem coverp00011011100010 : Covers (-880761639/500000 : ℚ) vp00011011100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101110001_0 : Blocks := edgeBlocks% "full/vectors/0001101110001-V-0000.bin"
noncomputable def vp0001101110001 : Blocks := vp0001101110001_0
private theorem bp00011011100010 : Branch 0 (-880761639/1000000 : ℚ) vp0001101110001 := by
  apply branch_left_normalized (c:=vp00011011100010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-880761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-880761639/500000 : ℚ) by norm_num]
  exact coverp00011011100010
private noncomputable def ep00011011100011_0 : Blocks := edgeBlocks% "full/vectors/00011011100011-E-0000.bin"
noncomputable def ep00011011100011 : Blocks := ep00011011100011_0
private theorem idp00011011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101110001.list =
    C ((2:ℤ)^57) * horner X vp00011011100011.list + horner X ep00011011100011.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011100011 : Branch 1 (-880761639/1000000 : ℚ) vp0001101110001 := by
  apply branch_checked idp00011011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-880761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-881261639/500000 : ℚ) by norm_num]
  exact coverp00011011100011
theorem coverp0001101110001 : Covers (-880761639/1000000 : ℚ) vp0001101110001 := join_branches bp00011011100010 bp00011011100011
private noncomputable def vp00011011100001_0 : Blocks := edgeBlocks% "full/vectors/00011011100001-V-0000.bin"
noncomputable def vp00011011100001 : Blocks := vp00011011100001_0
theorem coverp00011011100001 : Covers (-880261639/500000 : ℚ) vp00011011100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011100000_0 : Blocks := edgeBlocks% "full/vectors/00011011100000-V-0000.bin"
noncomputable def vp00011011100000 : Blocks := vp00011011100000_0
theorem coverp00011011100000 : Covers (-879761639/500000 : ℚ) vp00011011100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101110000_0 : Blocks := edgeBlocks% "full/vectors/0001101110000-V-0000.bin"
noncomputable def vp0001101110000 : Blocks := vp0001101110000_0
private theorem bp00011011100000 : Branch 0 (-879761639/1000000 : ℚ) vp0001101110000 := by
  apply branch_left_normalized (c:=vp00011011100000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-879761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-879761639/500000 : ℚ) by norm_num]
  exact coverp00011011100000
private noncomputable def ep00011011100001_0 : Blocks := edgeBlocks% "full/vectors/00011011100001-E-0000.bin"
noncomputable def ep00011011100001 : Blocks := ep00011011100001_0
private theorem idp00011011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101110000.list =
    C ((2:ℤ)^56) * horner X vp00011011100001.list + horner X ep00011011100001.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011100001 : Branch 1 (-879761639/1000000 : ℚ) vp0001101110000 := by
  apply branch_checked idp00011011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-879761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-880261639/500000 : ℚ) by norm_num]
  exact coverp00011011100001
theorem coverp0001101110000 : Covers (-879761639/1000000 : ℚ) vp0001101110000 := join_branches bp00011011100000 bp00011011100001
private noncomputable def vp000110111000_0 : Blocks := edgeBlocks% "full/vectors/000110111000-V-0000.bin"
noncomputable def vp000110111000 : Blocks := vp000110111000_0
private theorem bp0001101110000 : Branch 0 (-879761639/2000000 : ℚ) vp000110111000 := by
  apply branch_left_normalized (c:=vp0001101110000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-879761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-879761639/1000000 : ℚ) by norm_num]
  exact coverp0001101110000
private noncomputable def ep0001101110001_0 : Blocks := edgeBlocks% "full/vectors/0001101110001-E-0000.bin"
noncomputable def ep0001101110001 : Blocks := ep0001101110001_0
private theorem idp0001101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110111000.list =
    C ((2:ℤ)^94) * horner X vp0001101110001.list + horner X ep0001101110001.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101110001 : Branch 1 (-879761639/2000000 : ℚ) vp000110111000 := by
  apply branch_checked idp0001101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-879761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-880761639/1000000 : ℚ) by norm_num]
  exact coverp0001101110001
theorem coverp000110111000 : Covers (-879761639/2000000 : ℚ) vp000110111000 := join_branches bp0001101110000 bp0001101110001
private noncomputable def vp00011011100_0 : Blocks := edgeBlocks% "full/vectors/00011011100-V-0000.bin"
private noncomputable def vp00011011100_1 : Blocks := edgeBlocks% "full/vectors/00011011100-V-0001.bin"
noncomputable def vp00011011100 : Blocks := (Blocks.join vp00011011100_0 vp00011011100_1)
private theorem bp000110111000 : Branch 0 (-879761639/4000000 : ℚ) vp00011011100 := by
  apply branch_left_normalized (c:=vp000110111000) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-879761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-879761639/2000000 : ℚ) by norm_num]
  exact coverp000110111000
private noncomputable def ep000110111001_0 : Blocks := edgeBlocks% "full/vectors/000110111001-E-0000.bin"
private noncomputable def ep000110111001_1 : Blocks := edgeBlocks% "full/vectors/000110111001-E-0001.bin"
noncomputable def ep000110111001 : Blocks := (Blocks.join ep000110111001_0 ep000110111001_1)
private theorem idp000110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011011100.list =
    C ((2:ℤ)^167) * horner X vp000110111001.list + horner X ep000110111001.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110111001 : Branch 1 (-879761639/4000000 : ℚ) vp00011011100 := by
  apply branch_checked idp000110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-879761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-881761639/2000000 : ℚ) by norm_num]
  exact coverp000110111001
theorem coverp00011011100 : Covers (-879761639/4000000 : ℚ) vp00011011100 := join_branches bp000110111000 bp000110111001
private noncomputable def vp0001101110_0 : Blocks := edgeBlocks% "full/vectors/0001101110-V-0000.bin"
private noncomputable def vp0001101110_1 : Blocks := edgeBlocks% "full/vectors/0001101110-V-0001.bin"
private noncomputable def vp0001101110_2 : Blocks := edgeBlocks% "full/vectors/0001101110-V-0002.bin"
noncomputable def vp0001101110 : Blocks := (Blocks.join vp0001101110_0 (Blocks.join vp0001101110_1 vp0001101110_2))
private theorem bp00011011100 : Branch 0 (-879761639/8000000 : ℚ) vp0001101110 := by
  apply branch_left_normalized (c:=vp00011011100) (k:=0) (m:=154) (by decide +kernel)
  rw [show 2*(-879761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-879761639/4000000 : ℚ) by norm_num]
  exact coverp00011011100
private noncomputable def ep00011011101_0 : Blocks := edgeBlocks% "full/vectors/00011011101-E-0000.bin"
private noncomputable def ep00011011101_1 : Blocks := edgeBlocks% "full/vectors/00011011101-E-0001.bin"
private noncomputable def ep00011011101_2 : Blocks := edgeBlocks% "full/vectors/00011011101-E-0002.bin"
noncomputable def ep00011011101 : Blocks := (Blocks.join ep00011011101_0 (Blocks.join ep00011011101_1 ep00011011101_2))
private theorem idp00011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101110.list =
    C ((2:ℤ)^311) * horner X vp00011011101.list + horner X ep00011011101.list := by
  exact edge_identity (B := (2:ℤ)^530) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011101 : Branch 1 (-879761639/8000000 : ℚ) vp0001101110 := by
  apply branch_checked idp00011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-879761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-883761639/4000000 : ℚ) by norm_num]
  exact coverp00011011101
theorem coverp0001101110 : Covers (-879761639/8000000 : ℚ) vp0001101110 := join_branches bp00011011100 bp00011011101
private noncomputable def vp000110111_0 : Blocks := edgeBlocks% "full/vectors/000110111-V-0000.bin"
private noncomputable def vp000110111_1 : Blocks := edgeBlocks% "full/vectors/000110111-V-0001.bin"
private noncomputable def vp000110111_2 : Blocks := edgeBlocks% "full/vectors/000110111-V-0002.bin"
private noncomputable def vp000110111_3 : Blocks := edgeBlocks% "full/vectors/000110111-V-0003.bin"
private noncomputable def vp000110111_4 : Blocks := edgeBlocks% "full/vectors/000110111-V-0004.bin"
noncomputable def vp000110111 : Blocks := (Blocks.join (Blocks.join vp000110111_0 vp000110111_1) (Blocks.join vp000110111_2 (Blocks.join vp000110111_3 vp000110111_4)))
private theorem bp0001101110 : Branch 0 (-879761639/16000000 : ℚ) vp000110111 := by
  apply branch_left_normalized (c:=vp0001101110) (k:=0) (m:=287) (by decide +kernel)
  rw [show 2*(-879761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-879761639/8000000 : ℚ) by norm_num]
  exact coverp0001101110
private noncomputable def ep0001101111_0 : Blocks := edgeBlocks% "full/vectors/0001101111-E-0000.bin"
private noncomputable def ep0001101111_1 : Blocks := edgeBlocks% "full/vectors/0001101111-E-0001.bin"
private noncomputable def ep0001101111_2 : Blocks := edgeBlocks% "full/vectors/0001101111-E-0002.bin"
private noncomputable def ep0001101111_3 : Blocks := edgeBlocks% "full/vectors/0001101111-E-0003.bin"
private noncomputable def ep0001101111_4 : Blocks := edgeBlocks% "full/vectors/0001101111-E-0004.bin"
noncomputable def ep0001101111 : Blocks := (Blocks.join (Blocks.join ep0001101111_0 ep0001101111_1) (Blocks.join ep0001101111_2 (Blocks.join ep0001101111_3 ep0001101111_4)))
private theorem idp0001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110111.list =
    C ((2:ℤ)^596) * horner X vp0001101111.list + horner X ep0001101111.list := by
  exact edge_identity (B := (2:ℤ)^932) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101111 : Branch 1 (-879761639/16000000 : ℚ) vp000110111 := by
  apply branch_checked idp0001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-879761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-887761639/8000000 : ℚ) by norm_num]
  exact coverp0001101111
theorem coverp000110111 : Covers (-879761639/16000000 : ℚ) vp000110111 := join_branches bp0001101110 bp0001101111
private noncomputable def vp00011011011111_0 : Blocks := edgeBlocks% "full/vectors/00011011011111-V-0000.bin"
noncomputable def vp00011011011111 : Blocks := vp00011011011111_0
theorem coverp00011011011111 : Covers (-879261639/500000 : ℚ) vp00011011011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011011110_0 : Blocks := edgeBlocks% "full/vectors/00011011011110-V-0000.bin"
noncomputable def vp00011011011110 : Blocks := vp00011011011110_0
theorem coverp00011011011110 : Covers (-878761639/500000 : ℚ) vp00011011011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101101111_0 : Blocks := edgeBlocks% "full/vectors/0001101101111-V-0000.bin"
noncomputable def vp0001101101111 : Blocks := vp0001101101111_0
private theorem bp00011011011110 : Branch 0 (-878761639/1000000 : ℚ) vp0001101101111 := by
  apply branch_left_normalized (c:=vp00011011011110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-878761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-878761639/500000 : ℚ) by norm_num]
  exact coverp00011011011110
private noncomputable def ep00011011011111_0 : Blocks := edgeBlocks% "full/vectors/00011011011111-E-0000.bin"
noncomputable def ep00011011011111 : Blocks := ep00011011011111_0
private theorem idp00011011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101101111.list =
    C ((2:ℤ)^56) * horner X vp00011011011111.list + horner X ep00011011011111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011011111 : Branch 1 (-878761639/1000000 : ℚ) vp0001101101111 := by
  apply branch_checked idp00011011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-878761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-879261639/500000 : ℚ) by norm_num]
  exact coverp00011011011111
theorem coverp0001101101111 : Covers (-878761639/1000000 : ℚ) vp0001101101111 := join_branches bp00011011011110 bp00011011011111
private noncomputable def vp00011011011101_0 : Blocks := edgeBlocks% "full/vectors/00011011011101-V-0000.bin"
noncomputable def vp00011011011101 : Blocks := vp00011011011101_0
theorem coverp00011011011101 : Covers (-878261639/500000 : ℚ) vp00011011011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011011100_0 : Blocks := edgeBlocks% "full/vectors/00011011011100-V-0000.bin"
noncomputable def vp00011011011100 : Blocks := vp00011011011100_0
theorem coverp00011011011100 : Covers (-877761639/500000 : ℚ) vp00011011011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101101110_0 : Blocks := edgeBlocks% "full/vectors/0001101101110-V-0000.bin"
noncomputable def vp0001101101110 : Blocks := vp0001101101110_0
private theorem bp00011011011100 : Branch 0 (-877761639/1000000 : ℚ) vp0001101101110 := by
  apply branch_left_normalized (c:=vp00011011011100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-877761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-877761639/500000 : ℚ) by norm_num]
  exact coverp00011011011100
private noncomputable def ep00011011011101_0 : Blocks := edgeBlocks% "full/vectors/00011011011101-E-0000.bin"
noncomputable def ep00011011011101 : Blocks := ep00011011011101_0
private theorem idp00011011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101101110.list =
    C ((2:ℤ)^57) * horner X vp00011011011101.list + horner X ep00011011011101.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011011101 : Branch 1 (-877761639/1000000 : ℚ) vp0001101101110 := by
  apply branch_checked idp00011011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-877761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-878261639/500000 : ℚ) by norm_num]
  exact coverp00011011011101
theorem coverp0001101101110 : Covers (-877761639/1000000 : ℚ) vp0001101101110 := join_branches bp00011011011100 bp00011011011101
private noncomputable def vp000110110111_0 : Blocks := edgeBlocks% "full/vectors/000110110111-V-0000.bin"
noncomputable def vp000110110111 : Blocks := vp000110110111_0
private theorem bp0001101101110 : Branch 0 (-877761639/2000000 : ℚ) vp000110110111 := by
  apply branch_left_normalized (c:=vp0001101101110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-877761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-877761639/1000000 : ℚ) by norm_num]
  exact coverp0001101101110
private noncomputable def ep0001101101111_0 : Blocks := edgeBlocks% "full/vectors/0001101101111-E-0000.bin"
noncomputable def ep0001101101111 : Blocks := ep0001101101111_0
private theorem idp0001101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110110111.list =
    C ((2:ℤ)^94) * horner X vp0001101101111.list + horner X ep0001101101111.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101101111 : Branch 1 (-877761639/2000000 : ℚ) vp000110110111 := by
  apply branch_checked idp0001101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-877761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-878761639/1000000 : ℚ) by norm_num]
  exact coverp0001101101111
theorem coverp000110110111 : Covers (-877761639/2000000 : ℚ) vp000110110111 := join_branches bp0001101101110 bp0001101101111
private noncomputable def vp00011011011011_0 : Blocks := edgeBlocks% "full/vectors/00011011011011-V-0000.bin"
noncomputable def vp00011011011011 : Blocks := vp00011011011011_0
theorem coverp00011011011011 : Covers (-877261639/500000 : ℚ) vp00011011011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011011010_0 : Blocks := edgeBlocks% "full/vectors/00011011011010-V-0000.bin"
noncomputable def vp00011011011010 : Blocks := vp00011011011010_0
theorem coverp00011011011010 : Covers (-876761639/500000 : ℚ) vp00011011011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101101101_0 : Blocks := edgeBlocks% "full/vectors/0001101101101-V-0000.bin"
noncomputable def vp0001101101101 : Blocks := vp0001101101101_0
private theorem bp00011011011010 : Branch 0 (-876761639/1000000 : ℚ) vp0001101101101 := by
  apply branch_left_normalized (c:=vp00011011011010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-876761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-876761639/500000 : ℚ) by norm_num]
  exact coverp00011011011010
private noncomputable def ep00011011011011_0 : Blocks := edgeBlocks% "full/vectors/00011011011011-E-0000.bin"
noncomputable def ep00011011011011 : Blocks := ep00011011011011_0
private theorem idp00011011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101101101.list =
    C ((2:ℤ)^56) * horner X vp00011011011011.list + horner X ep00011011011011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011011011 : Branch 1 (-876761639/1000000 : ℚ) vp0001101101101 := by
  apply branch_checked idp00011011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-876761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-877261639/500000 : ℚ) by norm_num]
  exact coverp00011011011011
theorem coverp0001101101101 : Covers (-876761639/1000000 : ℚ) vp0001101101101 := join_branches bp00011011011010 bp00011011011011
private noncomputable def vp00011011011001_0 : Blocks := edgeBlocks% "full/vectors/00011011011001-V-0000.bin"
noncomputable def vp00011011011001 : Blocks := vp00011011011001_0
theorem coverp00011011011001 : Covers (-876261639/500000 : ℚ) vp00011011011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011011000_0 : Blocks := edgeBlocks% "full/vectors/00011011011000-V-0000.bin"
noncomputable def vp00011011011000 : Blocks := vp00011011011000_0
theorem coverp00011011011000 : Covers (-875761639/500000 : ℚ) vp00011011011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101101100_0 : Blocks := edgeBlocks% "full/vectors/0001101101100-V-0000.bin"
noncomputable def vp0001101101100 : Blocks := vp0001101101100_0
private theorem bp00011011011000 : Branch 0 (-875761639/1000000 : ℚ) vp0001101101100 := by
  apply branch_left_normalized (c:=vp00011011011000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-875761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-875761639/500000 : ℚ) by norm_num]
  exact coverp00011011011000
private noncomputable def ep00011011011001_0 : Blocks := edgeBlocks% "full/vectors/00011011011001-E-0000.bin"
noncomputable def ep00011011011001 : Blocks := ep00011011011001_0
private theorem idp00011011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101101100.list =
    C ((2:ℤ)^57) * horner X vp00011011011001.list + horner X ep00011011011001.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011011001 : Branch 1 (-875761639/1000000 : ℚ) vp0001101101100 := by
  apply branch_checked idp00011011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-875761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-876261639/500000 : ℚ) by norm_num]
  exact coverp00011011011001
theorem coverp0001101101100 : Covers (-875761639/1000000 : ℚ) vp0001101101100 := join_branches bp00011011011000 bp00011011011001
private noncomputable def vp000110110110_0 : Blocks := edgeBlocks% "full/vectors/000110110110-V-0000.bin"
noncomputable def vp000110110110 : Blocks := vp000110110110_0
private theorem bp0001101101100 : Branch 0 (-875761639/2000000 : ℚ) vp000110110110 := by
  apply branch_left_normalized (c:=vp0001101101100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-875761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-875761639/1000000 : ℚ) by norm_num]
  exact coverp0001101101100
private noncomputable def ep0001101101101_0 : Blocks := edgeBlocks% "full/vectors/0001101101101-E-0000.bin"
noncomputable def ep0001101101101 : Blocks := ep0001101101101_0
private theorem idp0001101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110110110.list =
    C ((2:ℤ)^94) * horner X vp0001101101101.list + horner X ep0001101101101.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101101101 : Branch 1 (-875761639/2000000 : ℚ) vp000110110110 := by
  apply branch_checked idp0001101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-875761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-876761639/1000000 : ℚ) by norm_num]
  exact coverp0001101101101
theorem coverp000110110110 : Covers (-875761639/2000000 : ℚ) vp000110110110 := join_branches bp0001101101100 bp0001101101101
private noncomputable def vp00011011011_0 : Blocks := edgeBlocks% "full/vectors/00011011011-V-0000.bin"
private noncomputable def vp00011011011_1 : Blocks := edgeBlocks% "full/vectors/00011011011-V-0001.bin"
noncomputable def vp00011011011 : Blocks := (Blocks.join vp00011011011_0 vp00011011011_1)
private theorem bp000110110110 : Branch 0 (-875761639/4000000 : ℚ) vp00011011011 := by
  apply branch_left_normalized (c:=vp000110110110) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-875761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-875761639/2000000 : ℚ) by norm_num]
  exact coverp000110110110
private noncomputable def ep000110110111_0 : Blocks := edgeBlocks% "full/vectors/000110110111-E-0000.bin"
private noncomputable def ep000110110111_1 : Blocks := edgeBlocks% "full/vectors/000110110111-E-0001.bin"
noncomputable def ep000110110111 : Blocks := (Blocks.join ep000110110111_0 ep000110110111_1)
private theorem idp000110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011011011.list =
    C ((2:ℤ)^168) * horner X vp000110110111.list + horner X ep000110110111.list := by
  exact edge_identity (B := (2:ℤ)^328) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110110111 : Branch 1 (-875761639/4000000 : ℚ) vp00011011011 := by
  apply branch_checked idp000110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-875761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-877761639/2000000 : ℚ) by norm_num]
  exact coverp000110110111
theorem coverp00011011011 : Covers (-875761639/4000000 : ℚ) vp00011011011 := join_branches bp000110110110 bp000110110111
private noncomputable def vp00011011010111_0 : Blocks := edgeBlocks% "full/vectors/00011011010111-V-0000.bin"
noncomputable def vp00011011010111 : Blocks := vp00011011010111_0
theorem coverp00011011010111 : Covers (-875261639/500000 : ℚ) vp00011011010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011010110_0 : Blocks := edgeBlocks% "full/vectors/00011011010110-V-0000.bin"
noncomputable def vp00011011010110 : Blocks := vp00011011010110_0
theorem coverp00011011010110 : Covers (-874761639/500000 : ℚ) vp00011011010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101101011_0 : Blocks := edgeBlocks% "full/vectors/0001101101011-V-0000.bin"
noncomputable def vp0001101101011 : Blocks := vp0001101101011_0
private theorem bp00011011010110 : Branch 0 (-874761639/1000000 : ℚ) vp0001101101011 := by
  apply branch_left_normalized (c:=vp00011011010110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-874761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-874761639/500000 : ℚ) by norm_num]
  exact coverp00011011010110
private noncomputable def ep00011011010111_0 : Blocks := edgeBlocks% "full/vectors/00011011010111-E-0000.bin"
noncomputable def ep00011011010111 : Blocks := ep00011011010111_0
private theorem idp00011011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101101011.list =
    C ((2:ℤ)^57) * horner X vp00011011010111.list + horner X ep00011011010111.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011010111 : Branch 1 (-874761639/1000000 : ℚ) vp0001101101011 := by
  apply branch_checked idp00011011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-874761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-875261639/500000 : ℚ) by norm_num]
  exact coverp00011011010111
theorem coverp0001101101011 : Covers (-874761639/1000000 : ℚ) vp0001101101011 := join_branches bp00011011010110 bp00011011010111
private noncomputable def vp00011011010101_0 : Blocks := edgeBlocks% "full/vectors/00011011010101-V-0000.bin"
noncomputable def vp00011011010101 : Blocks := vp00011011010101_0
theorem coverp00011011010101 : Covers (-874261639/500000 : ℚ) vp00011011010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011010100_0 : Blocks := edgeBlocks% "full/vectors/00011011010100-V-0000.bin"
noncomputable def vp00011011010100 : Blocks := vp00011011010100_0
theorem coverp00011011010100 : Covers (-873761639/500000 : ℚ) vp00011011010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101101010_0 : Blocks := edgeBlocks% "full/vectors/0001101101010-V-0000.bin"
noncomputable def vp0001101101010 : Blocks := vp0001101101010_0
private theorem bp00011011010100 : Branch 0 (-873761639/1000000 : ℚ) vp0001101101010 := by
  apply branch_left_normalized (c:=vp00011011010100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-873761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-873761639/500000 : ℚ) by norm_num]
  exact coverp00011011010100
private noncomputable def ep00011011010101_0 : Blocks := edgeBlocks% "full/vectors/00011011010101-E-0000.bin"
noncomputable def ep00011011010101 : Blocks := ep00011011010101_0
private theorem idp00011011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101101010.list =
    C ((2:ℤ)^55) * horner X vp00011011010101.list + horner X ep00011011010101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011010101 : Branch 1 (-873761639/1000000 : ℚ) vp0001101101010 := by
  apply branch_checked idp00011011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-873761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-874261639/500000 : ℚ) by norm_num]
  exact coverp00011011010101
theorem coverp0001101101010 : Covers (-873761639/1000000 : ℚ) vp0001101101010 := join_branches bp00011011010100 bp00011011010101
private noncomputable def vp000110110101_0 : Blocks := edgeBlocks% "full/vectors/000110110101-V-0000.bin"
noncomputable def vp000110110101 : Blocks := vp000110110101_0
private theorem bp0001101101010 : Branch 0 (-873761639/2000000 : ℚ) vp000110110101 := by
  apply branch_left_normalized (c:=vp0001101101010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-873761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-873761639/1000000 : ℚ) by norm_num]
  exact coverp0001101101010
private noncomputable def ep0001101101011_0 : Blocks := edgeBlocks% "full/vectors/0001101101011-E-0000.bin"
noncomputable def ep0001101101011 : Blocks := ep0001101101011_0
private theorem idp0001101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110110101.list =
    C ((2:ℤ)^94) * horner X vp0001101101011.list + horner X ep0001101101011.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101101011 : Branch 1 (-873761639/2000000 : ℚ) vp000110110101 := by
  apply branch_checked idp0001101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-873761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-874761639/1000000 : ℚ) by norm_num]
  exact coverp0001101101011
theorem coverp000110110101 : Covers (-873761639/2000000 : ℚ) vp000110110101 := join_branches bp0001101101010 bp0001101101011
private noncomputable def vp00011011010011_0 : Blocks := edgeBlocks% "full/vectors/00011011010011-V-0000.bin"
noncomputable def vp00011011010011 : Blocks := vp00011011010011_0
theorem coverp00011011010011 : Covers (-873261639/500000 : ℚ) vp00011011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011010010_0 : Blocks := edgeBlocks% "full/vectors/00011011010010-V-0000.bin"
noncomputable def vp00011011010010 : Blocks := vp00011011010010_0
theorem coverp00011011010010 : Covers (-872761639/500000 : ℚ) vp00011011010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101101001_0 : Blocks := edgeBlocks% "full/vectors/0001101101001-V-0000.bin"
noncomputable def vp0001101101001 : Blocks := vp0001101101001_0
private theorem bp00011011010010 : Branch 0 (-872761639/1000000 : ℚ) vp0001101101001 := by
  apply branch_left_normalized (c:=vp00011011010010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-872761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-872761639/500000 : ℚ) by norm_num]
  exact coverp00011011010010
private noncomputable def ep00011011010011_0 : Blocks := edgeBlocks% "full/vectors/00011011010011-E-0000.bin"
noncomputable def ep00011011010011 : Blocks := ep00011011010011_0
private theorem idp00011011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101101001.list =
    C ((2:ℤ)^56) * horner X vp00011011010011.list + horner X ep00011011010011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011010011 : Branch 1 (-872761639/1000000 : ℚ) vp0001101101001 := by
  apply branch_checked idp00011011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-872761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-873261639/500000 : ℚ) by norm_num]
  exact coverp00011011010011
theorem coverp0001101101001 : Covers (-872761639/1000000 : ℚ) vp0001101101001 := join_branches bp00011011010010 bp00011011010011
private noncomputable def vp00011011010001_0 : Blocks := edgeBlocks% "full/vectors/00011011010001-V-0000.bin"
noncomputable def vp00011011010001 : Blocks := vp00011011010001_0
theorem coverp00011011010001 : Covers (-872261639/500000 : ℚ) vp00011011010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011010000_0 : Blocks := edgeBlocks% "full/vectors/00011011010000-V-0000.bin"
noncomputable def vp00011011010000 : Blocks := vp00011011010000_0
theorem coverp00011011010000 : Covers (-871761639/500000 : ℚ) vp00011011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101101000_0 : Blocks := edgeBlocks% "full/vectors/0001101101000-V-0000.bin"
noncomputable def vp0001101101000 : Blocks := vp0001101101000_0
private theorem bp00011011010000 : Branch 0 (-871761639/1000000 : ℚ) vp0001101101000 := by
  apply branch_left_normalized (c:=vp00011011010000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-871761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-871761639/500000 : ℚ) by norm_num]
  exact coverp00011011010000
private noncomputable def ep00011011010001_0 : Blocks := edgeBlocks% "full/vectors/00011011010001-E-0000.bin"
noncomputable def ep00011011010001 : Blocks := ep00011011010001_0
private theorem idp00011011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101101000.list =
    C ((2:ℤ)^57) * horner X vp00011011010001.list + horner X ep00011011010001.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011010001 : Branch 1 (-871761639/1000000 : ℚ) vp0001101101000 := by
  apply branch_checked idp00011011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-871761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-872261639/500000 : ℚ) by norm_num]
  exact coverp00011011010001
theorem coverp0001101101000 : Covers (-871761639/1000000 : ℚ) vp0001101101000 := join_branches bp00011011010000 bp00011011010001
private noncomputable def vp000110110100_0 : Blocks := edgeBlocks% "full/vectors/000110110100-V-0000.bin"
noncomputable def vp000110110100 : Blocks := vp000110110100_0
private theorem bp0001101101000 : Branch 0 (-871761639/2000000 : ℚ) vp000110110100 := by
  apply branch_left_normalized (c:=vp0001101101000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-871761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-871761639/1000000 : ℚ) by norm_num]
  exact coverp0001101101000
private noncomputable def ep0001101101001_0 : Blocks := edgeBlocks% "full/vectors/0001101101001-E-0000.bin"
noncomputable def ep0001101101001 : Blocks := ep0001101101001_0
private theorem idp0001101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110110100.list =
    C ((2:ℤ)^95) * horner X vp0001101101001.list + horner X ep0001101101001.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101101001 : Branch 1 (-871761639/2000000 : ℚ) vp000110110100 := by
  apply branch_checked idp0001101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-871761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-872761639/1000000 : ℚ) by norm_num]
  exact coverp0001101101001
theorem coverp000110110100 : Covers (-871761639/2000000 : ℚ) vp000110110100 := join_branches bp0001101101000 bp0001101101001
private noncomputable def vp00011011010_0 : Blocks := edgeBlocks% "full/vectors/00011011010-V-0000.bin"
private noncomputable def vp00011011010_1 : Blocks := edgeBlocks% "full/vectors/00011011010-V-0001.bin"
noncomputable def vp00011011010 : Blocks := (Blocks.join vp00011011010_0 vp00011011010_1)
private theorem bp000110110100 : Branch 0 (-871761639/4000000 : ℚ) vp00011011010 := by
  apply branch_left_normalized (c:=vp000110110100) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-871761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-871761639/2000000 : ℚ) by norm_num]
  exact coverp000110110100
private noncomputable def ep000110110101_0 : Blocks := edgeBlocks% "full/vectors/000110110101-E-0000.bin"
private noncomputable def ep000110110101_1 : Blocks := edgeBlocks% "full/vectors/000110110101-E-0001.bin"
noncomputable def ep000110110101 : Blocks := (Blocks.join ep000110110101_0 ep000110110101_1)
private theorem idp000110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011011010.list =
    C ((2:ℤ)^168) * horner X vp000110110101.list + horner X ep000110110101.list := by
  exact edge_identity (B := (2:ℤ)^328) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110110101 : Branch 1 (-871761639/4000000 : ℚ) vp00011011010 := by
  apply branch_checked idp000110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-871761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-873761639/2000000 : ℚ) by norm_num]
  exact coverp000110110101
theorem coverp00011011010 : Covers (-871761639/4000000 : ℚ) vp00011011010 := join_branches bp000110110100 bp000110110101
private noncomputable def vp0001101101_0 : Blocks := edgeBlocks% "full/vectors/0001101101-V-0000.bin"
private noncomputable def vp0001101101_1 : Blocks := edgeBlocks% "full/vectors/0001101101-V-0001.bin"
private noncomputable def vp0001101101_2 : Blocks := edgeBlocks% "full/vectors/0001101101-V-0002.bin"
noncomputable def vp0001101101 : Blocks := (Blocks.join vp0001101101_0 (Blocks.join vp0001101101_1 vp0001101101_2))
private theorem bp00011011010 : Branch 0 (-871761639/8000000 : ℚ) vp0001101101 := by
  apply branch_left_normalized (c:=vp00011011010) (k:=0) (m:=155) (by decide +kernel)
  rw [show 2*(-871761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-871761639/4000000 : ℚ) by norm_num]
  exact coverp00011011010
private noncomputable def ep00011011011_0 : Blocks := edgeBlocks% "full/vectors/00011011011-E-0000.bin"
private noncomputable def ep00011011011_1 : Blocks := edgeBlocks% "full/vectors/00011011011-E-0001.bin"
private noncomputable def ep00011011011_2 : Blocks := edgeBlocks% "full/vectors/00011011011-E-0002.bin"
noncomputable def ep00011011011 : Blocks := (Blocks.join ep00011011011_0 (Blocks.join ep00011011011_1 ep00011011011_2))
private theorem idp00011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101101.list =
    C ((2:ℤ)^312) * horner X vp00011011011.list + horner X ep00011011011.list := by
  exact edge_identity (B := (2:ℤ)^532) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011011 : Branch 1 (-871761639/8000000 : ℚ) vp0001101101 := by
  apply branch_checked idp00011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-871761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-875761639/4000000 : ℚ) by norm_num]
  exact coverp00011011011
theorem coverp0001101101 : Covers (-871761639/8000000 : ℚ) vp0001101101 := join_branches bp00011011010 bp00011011011
private noncomputable def vp00011011001111_0 : Blocks := edgeBlocks% "full/vectors/00011011001111-V-0000.bin"
noncomputable def vp00011011001111 : Blocks := vp00011011001111_0
theorem coverp00011011001111 : Covers (-871261639/500000 : ℚ) vp00011011001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011001110_0 : Blocks := edgeBlocks% "full/vectors/00011011001110-V-0000.bin"
noncomputable def vp00011011001110 : Blocks := vp00011011001110_0
theorem coverp00011011001110 : Covers (-870761639/500000 : ℚ) vp00011011001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101100111_0 : Blocks := edgeBlocks% "full/vectors/0001101100111-V-0000.bin"
noncomputable def vp0001101100111 : Blocks := vp0001101100111_0
private theorem bp00011011001110 : Branch 0 (-870761639/1000000 : ℚ) vp0001101100111 := by
  apply branch_left_normalized (c:=vp00011011001110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-870761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-870761639/500000 : ℚ) by norm_num]
  exact coverp00011011001110
private noncomputable def ep00011011001111_0 : Blocks := edgeBlocks% "full/vectors/00011011001111-E-0000.bin"
noncomputable def ep00011011001111 : Blocks := ep00011011001111_0
private theorem idp00011011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101100111.list =
    C ((2:ℤ)^57) * horner X vp00011011001111.list + horner X ep00011011001111.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011001111 : Branch 1 (-870761639/1000000 : ℚ) vp0001101100111 := by
  apply branch_checked idp00011011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-870761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-871261639/500000 : ℚ) by norm_num]
  exact coverp00011011001111
theorem coverp0001101100111 : Covers (-870761639/1000000 : ℚ) vp0001101100111 := join_branches bp00011011001110 bp00011011001111
private noncomputable def vp00011011001101_0 : Blocks := edgeBlocks% "full/vectors/00011011001101-V-0000.bin"
noncomputable def vp00011011001101 : Blocks := vp00011011001101_0
theorem coverp00011011001101 : Covers (-870261639/500000 : ℚ) vp00011011001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011001100_0 : Blocks := edgeBlocks% "full/vectors/00011011001100-V-0000.bin"
noncomputable def vp00011011001100 : Blocks := vp00011011001100_0
theorem coverp00011011001100 : Covers (-869761639/500000 : ℚ) vp00011011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101100110_0 : Blocks := edgeBlocks% "full/vectors/0001101100110-V-0000.bin"
noncomputable def vp0001101100110 : Blocks := vp0001101100110_0
private theorem bp00011011001100 : Branch 0 (-869761639/1000000 : ℚ) vp0001101100110 := by
  apply branch_left_normalized (c:=vp00011011001100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-869761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-869761639/500000 : ℚ) by norm_num]
  exact coverp00011011001100
private noncomputable def ep00011011001101_0 : Blocks := edgeBlocks% "full/vectors/00011011001101-E-0000.bin"
noncomputable def ep00011011001101 : Blocks := ep00011011001101_0
private theorem idp00011011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101100110.list =
    C ((2:ℤ)^56) * horner X vp00011011001101.list + horner X ep00011011001101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011001101 : Branch 1 (-869761639/1000000 : ℚ) vp0001101100110 := by
  apply branch_checked idp00011011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-869761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-870261639/500000 : ℚ) by norm_num]
  exact coverp00011011001101
theorem coverp0001101100110 : Covers (-869761639/1000000 : ℚ) vp0001101100110 := join_branches bp00011011001100 bp00011011001101
private noncomputable def vp000110110011_0 : Blocks := edgeBlocks% "full/vectors/000110110011-V-0000.bin"
noncomputable def vp000110110011 : Blocks := vp000110110011_0
private theorem bp0001101100110 : Branch 0 (-869761639/2000000 : ℚ) vp000110110011 := by
  apply branch_left_normalized (c:=vp0001101100110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-869761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-869761639/1000000 : ℚ) by norm_num]
  exact coverp0001101100110
private noncomputable def ep0001101100111_0 : Blocks := edgeBlocks% "full/vectors/0001101100111-E-0000.bin"
noncomputable def ep0001101100111 : Blocks := ep0001101100111_0
private theorem idp0001101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110110011.list =
    C ((2:ℤ)^93) * horner X vp0001101100111.list + horner X ep0001101100111.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101100111 : Branch 1 (-869761639/2000000 : ℚ) vp000110110011 := by
  apply branch_checked idp0001101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-869761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-870761639/1000000 : ℚ) by norm_num]
  exact coverp0001101100111
theorem coverp000110110011 : Covers (-869761639/2000000 : ℚ) vp000110110011 := join_branches bp0001101100110 bp0001101100111
private noncomputable def vp00011011001011_0 : Blocks := edgeBlocks% "full/vectors/00011011001011-V-0000.bin"
noncomputable def vp00011011001011 : Blocks := vp00011011001011_0
theorem coverp00011011001011 : Covers (-869261639/500000 : ℚ) vp00011011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011001010_0 : Blocks := edgeBlocks% "full/vectors/00011011001010-V-0000.bin"
noncomputable def vp00011011001010 : Blocks := vp00011011001010_0
theorem coverp00011011001010 : Covers (-868761639/500000 : ℚ) vp00011011001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101100101_0 : Blocks := edgeBlocks% "full/vectors/0001101100101-V-0000.bin"
noncomputable def vp0001101100101 : Blocks := vp0001101100101_0
private theorem bp00011011001010 : Branch 0 (-868761639/1000000 : ℚ) vp0001101100101 := by
  apply branch_left_normalized (c:=vp00011011001010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-868761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-868761639/500000 : ℚ) by norm_num]
  exact coverp00011011001010
private noncomputable def ep00011011001011_0 : Blocks := edgeBlocks% "full/vectors/00011011001011-E-0000.bin"
noncomputable def ep00011011001011 : Blocks := ep00011011001011_0
private theorem idp00011011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101100101.list =
    C ((2:ℤ)^57) * horner X vp00011011001011.list + horner X ep00011011001011.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011001011 : Branch 1 (-868761639/1000000 : ℚ) vp0001101100101 := by
  apply branch_checked idp00011011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-868761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-869261639/500000 : ℚ) by norm_num]
  exact coverp00011011001011
theorem coverp0001101100101 : Covers (-868761639/1000000 : ℚ) vp0001101100101 := join_branches bp00011011001010 bp00011011001011
private noncomputable def vp00011011001001_0 : Blocks := edgeBlocks% "full/vectors/00011011001001-V-0000.bin"
noncomputable def vp00011011001001 : Blocks := vp00011011001001_0
theorem coverp00011011001001 : Covers (-868261639/500000 : ℚ) vp00011011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011001000_0 : Blocks := edgeBlocks% "full/vectors/00011011001000-V-0000.bin"
noncomputable def vp00011011001000 : Blocks := vp00011011001000_0
theorem coverp00011011001000 : Covers (-867761639/500000 : ℚ) vp00011011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101100100_0 : Blocks := edgeBlocks% "full/vectors/0001101100100-V-0000.bin"
noncomputable def vp0001101100100 : Blocks := vp0001101100100_0
private theorem bp00011011001000 : Branch 0 (-867761639/1000000 : ℚ) vp0001101100100 := by
  apply branch_left_normalized (c:=vp00011011001000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-867761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-867761639/500000 : ℚ) by norm_num]
  exact coverp00011011001000
private noncomputable def ep00011011001001_0 : Blocks := edgeBlocks% "full/vectors/00011011001001-E-0000.bin"
noncomputable def ep00011011001001 : Blocks := ep00011011001001_0
private theorem idp00011011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101100100.list =
    C ((2:ℤ)^57) * horner X vp00011011001001.list + horner X ep00011011001001.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011001001 : Branch 1 (-867761639/1000000 : ℚ) vp0001101100100 := by
  apply branch_checked idp00011011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-867761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-868261639/500000 : ℚ) by norm_num]
  exact coverp00011011001001
theorem coverp0001101100100 : Covers (-867761639/1000000 : ℚ) vp0001101100100 := join_branches bp00011011001000 bp00011011001001
private noncomputable def vp000110110010_0 : Blocks := edgeBlocks% "full/vectors/000110110010-V-0000.bin"
noncomputable def vp000110110010 : Blocks := vp000110110010_0
private theorem bp0001101100100 : Branch 0 (-867761639/2000000 : ℚ) vp000110110010 := by
  apply branch_left_normalized (c:=vp0001101100100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-867761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-867761639/1000000 : ℚ) by norm_num]
  exact coverp0001101100100
private noncomputable def ep0001101100101_0 : Blocks := edgeBlocks% "full/vectors/0001101100101-E-0000.bin"
noncomputable def ep0001101100101 : Blocks := ep0001101100101_0
private theorem idp0001101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110110010.list =
    C ((2:ℤ)^95) * horner X vp0001101100101.list + horner X ep0001101100101.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101100101 : Branch 1 (-867761639/2000000 : ℚ) vp000110110010 := by
  apply branch_checked idp0001101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-867761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-868761639/1000000 : ℚ) by norm_num]
  exact coverp0001101100101
theorem coverp000110110010 : Covers (-867761639/2000000 : ℚ) vp000110110010 := join_branches bp0001101100100 bp0001101100101
private noncomputable def vp00011011001_0 : Blocks := edgeBlocks% "full/vectors/00011011001-V-0000.bin"
private noncomputable def vp00011011001_1 : Blocks := edgeBlocks% "full/vectors/00011011001-V-0001.bin"
noncomputable def vp00011011001 : Blocks := (Blocks.join vp00011011001_0 vp00011011001_1)
private theorem bp000110110010 : Branch 0 (-867761639/4000000 : ℚ) vp00011011001 := by
  apply branch_left_normalized (c:=vp000110110010) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-867761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-867761639/2000000 : ℚ) by norm_num]
  exact coverp000110110010
private noncomputable def ep000110110011_0 : Blocks := edgeBlocks% "full/vectors/000110110011-E-0000.bin"
private noncomputable def ep000110110011_1 : Blocks := edgeBlocks% "full/vectors/000110110011-E-0001.bin"
noncomputable def ep000110110011 : Blocks := (Blocks.join ep000110110011_0 ep000110110011_1)
private theorem idp000110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011011001.list =
    C ((2:ℤ)^169) * horner X vp000110110011.list + horner X ep000110110011.list := by
  exact edge_identity (B := (2:ℤ)^329) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110110011 : Branch 1 (-867761639/4000000 : ℚ) vp00011011001 := by
  apply branch_checked idp000110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-867761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-869761639/2000000 : ℚ) by norm_num]
  exact coverp000110110011
theorem coverp00011011001 : Covers (-867761639/4000000 : ℚ) vp00011011001 := join_branches bp000110110010 bp000110110011
private noncomputable def vp00011011000111_0 : Blocks := edgeBlocks% "full/vectors/00011011000111-V-0000.bin"
noncomputable def vp00011011000111 : Blocks := vp00011011000111_0
theorem coverp00011011000111 : Covers (-867261639/500000 : ℚ) vp00011011000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011000110_0 : Blocks := edgeBlocks% "full/vectors/00011011000110-V-0000.bin"
noncomputable def vp00011011000110 : Blocks := vp00011011000110_0
theorem coverp00011011000110 : Covers (-866761639/500000 : ℚ) vp00011011000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101100011_0 : Blocks := edgeBlocks% "full/vectors/0001101100011-V-0000.bin"
noncomputable def vp0001101100011 : Blocks := vp0001101100011_0
private theorem bp00011011000110 : Branch 0 (-866761639/1000000 : ℚ) vp0001101100011 := by
  apply branch_left_normalized (c:=vp00011011000110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-866761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-866761639/500000 : ℚ) by norm_num]
  exact coverp00011011000110
private noncomputable def ep00011011000111_0 : Blocks := edgeBlocks% "full/vectors/00011011000111-E-0000.bin"
noncomputable def ep00011011000111 : Blocks := ep00011011000111_0
private theorem idp00011011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101100011.list =
    C ((2:ℤ)^56) * horner X vp00011011000111.list + horner X ep00011011000111.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011000111 : Branch 1 (-866761639/1000000 : ℚ) vp0001101100011 := by
  apply branch_checked idp00011011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-866761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-867261639/500000 : ℚ) by norm_num]
  exact coverp00011011000111
theorem coverp0001101100011 : Covers (-866761639/1000000 : ℚ) vp0001101100011 := join_branches bp00011011000110 bp00011011000111
private noncomputable def vp00011011000101_0 : Blocks := edgeBlocks% "full/vectors/00011011000101-V-0000.bin"
noncomputable def vp00011011000101 : Blocks := vp00011011000101_0
theorem coverp00011011000101 : Covers (-866261639/500000 : ℚ) vp00011011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011000100_0 : Blocks := edgeBlocks% "full/vectors/00011011000100-V-0000.bin"
noncomputable def vp00011011000100 : Blocks := vp00011011000100_0
theorem coverp00011011000100 : Covers (-865761639/500000 : ℚ) vp00011011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101100010_0 : Blocks := edgeBlocks% "full/vectors/0001101100010-V-0000.bin"
noncomputable def vp0001101100010 : Blocks := vp0001101100010_0
private theorem bp00011011000100 : Branch 0 (-865761639/1000000 : ℚ) vp0001101100010 := by
  apply branch_left_normalized (c:=vp00011011000100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-865761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-865761639/500000 : ℚ) by norm_num]
  exact coverp00011011000100
private noncomputable def ep00011011000101_0 : Blocks := edgeBlocks% "full/vectors/00011011000101-E-0000.bin"
noncomputable def ep00011011000101 : Blocks := ep00011011000101_0
private theorem idp00011011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101100010.list =
    C ((2:ℤ)^57) * horner X vp00011011000101.list + horner X ep00011011000101.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011000101 : Branch 1 (-865761639/1000000 : ℚ) vp0001101100010 := by
  apply branch_checked idp00011011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-865761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-866261639/500000 : ℚ) by norm_num]
  exact coverp00011011000101
theorem coverp0001101100010 : Covers (-865761639/1000000 : ℚ) vp0001101100010 := join_branches bp00011011000100 bp00011011000101
private noncomputable def vp000110110001_0 : Blocks := edgeBlocks% "full/vectors/000110110001-V-0000.bin"
noncomputable def vp000110110001 : Blocks := vp000110110001_0
private theorem bp0001101100010 : Branch 0 (-865761639/2000000 : ℚ) vp000110110001 := by
  apply branch_left_normalized (c:=vp0001101100010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-865761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-865761639/1000000 : ℚ) by norm_num]
  exact coverp0001101100010
private noncomputable def ep0001101100011_0 : Blocks := edgeBlocks% "full/vectors/0001101100011-E-0000.bin"
noncomputable def ep0001101100011 : Blocks := ep0001101100011_0
private theorem idp0001101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110110001.list =
    C ((2:ℤ)^93) * horner X vp0001101100011.list + horner X ep0001101100011.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101100011 : Branch 1 (-865761639/2000000 : ℚ) vp000110110001 := by
  apply branch_checked idp0001101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-865761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-866761639/1000000 : ℚ) by norm_num]
  exact coverp0001101100011
theorem coverp000110110001 : Covers (-865761639/2000000 : ℚ) vp000110110001 := join_branches bp0001101100010 bp0001101100011
private noncomputable def vp00011011000011_0 : Blocks := edgeBlocks% "full/vectors/00011011000011-V-0000.bin"
noncomputable def vp00011011000011 : Blocks := vp00011011000011_0
theorem coverp00011011000011 : Covers (-865261639/500000 : ℚ) vp00011011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011011000010_0 : Blocks := edgeBlocks% "full/vectors/00011011000010-V-0000.bin"
noncomputable def vp00011011000010 : Blocks := vp00011011000010_0
theorem coverp00011011000010 : Covers (-864761639/500000 : ℚ) vp00011011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001101100001_0 : Blocks := edgeBlocks% "full/vectors/0001101100001-V-0000.bin"
noncomputable def vp0001101100001 : Blocks := vp0001101100001_0
private theorem bp00011011000010 : Branch 0 (-864761639/1000000 : ℚ) vp0001101100001 := by
  apply branch_left_normalized (c:=vp00011011000010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-864761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-864761639/500000 : ℚ) by norm_num]
  exact coverp00011011000010
private noncomputable def ep00011011000011_0 : Blocks := edgeBlocks% "full/vectors/00011011000011-E-0000.bin"
noncomputable def ep00011011000011 : Blocks := ep00011011000011_0
private theorem idp00011011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101100001.list =
    C ((2:ℤ)^55) * horner X vp00011011000011.list + horner X ep00011011000011.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011000011 : Branch 1 (-864761639/1000000 : ℚ) vp0001101100001 := by
  apply branch_checked idp00011011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-864761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-865261639/500000 : ℚ) by norm_num]
  exact coverp00011011000011
theorem coverp0001101100001 : Covers (-864761639/1000000 : ℚ) vp0001101100001 := join_branches bp00011011000010 bp00011011000011
private noncomputable def vp0001101100000_0 : Blocks := edgeBlocks% "full/vectors/0001101100000-V-0000.bin"
noncomputable def vp0001101100000 : Blocks := vp0001101100000_0
theorem coverp0001101100000 : Covers (-863761639/1000000 : ℚ) vp0001101100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000110110000_0 : Blocks := edgeBlocks% "full/vectors/000110110000-V-0000.bin"
noncomputable def vp000110110000 : Blocks := vp000110110000_0
private theorem bp0001101100000 : Branch 0 (-863761639/2000000 : ℚ) vp000110110000 := by
  apply branch_left_normalized (c:=vp0001101100000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-863761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-863761639/1000000 : ℚ) by norm_num]
  exact coverp0001101100000
private noncomputable def ep0001101100001_0 : Blocks := edgeBlocks% "full/vectors/0001101100001-E-0000.bin"
noncomputable def ep0001101100001 : Blocks := ep0001101100001_0
private theorem idp0001101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110110000.list =
    C ((2:ℤ)^94) * horner X vp0001101100001.list + horner X ep0001101100001.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101100001 : Branch 1 (-863761639/2000000 : ℚ) vp000110110000 := by
  apply branch_checked idp0001101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-863761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-864761639/1000000 : ℚ) by norm_num]
  exact coverp0001101100001
theorem coverp000110110000 : Covers (-863761639/2000000 : ℚ) vp000110110000 := join_branches bp0001101100000 bp0001101100001
private noncomputable def vp00011011000_0 : Blocks := edgeBlocks% "full/vectors/00011011000-V-0000.bin"
private noncomputable def vp00011011000_1 : Blocks := edgeBlocks% "full/vectors/00011011000-V-0001.bin"
noncomputable def vp00011011000 : Blocks := (Blocks.join vp00011011000_0 vp00011011000_1)
private theorem bp000110110000 : Branch 0 (-863761639/4000000 : ℚ) vp00011011000 := by
  apply branch_left_normalized (c:=vp000110110000) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-863761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-863761639/2000000 : ℚ) by norm_num]
  exact coverp000110110000
private noncomputable def ep000110110001_0 : Blocks := edgeBlocks% "full/vectors/000110110001-E-0000.bin"
private noncomputable def ep000110110001_1 : Blocks := edgeBlocks% "full/vectors/000110110001-E-0001.bin"
noncomputable def ep000110110001 : Blocks := (Blocks.join ep000110110001_0 ep000110110001_1)
private theorem idp000110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011011000.list =
    C ((2:ℤ)^167) * horner X vp000110110001.list + horner X ep000110110001.list := by
  exact edge_identity (B := (2:ℤ)^328) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110110001 : Branch 1 (-863761639/4000000 : ℚ) vp00011011000 := by
  apply branch_checked idp000110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-863761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-865761639/2000000 : ℚ) by norm_num]
  exact coverp000110110001
theorem coverp00011011000 : Covers (-863761639/4000000 : ℚ) vp00011011000 := join_branches bp000110110000 bp000110110001
private noncomputable def vp0001101100_0 : Blocks := edgeBlocks% "full/vectors/0001101100-V-0000.bin"
private noncomputable def vp0001101100_1 : Blocks := edgeBlocks% "full/vectors/0001101100-V-0001.bin"
private noncomputable def vp0001101100_2 : Blocks := edgeBlocks% "full/vectors/0001101100-V-0002.bin"
noncomputable def vp0001101100 : Blocks := (Blocks.join vp0001101100_0 (Blocks.join vp0001101100_1 vp0001101100_2))
private theorem bp00011011000 : Branch 0 (-863761639/8000000 : ℚ) vp0001101100 := by
  apply branch_left_normalized (c:=vp00011011000) (k:=0) (m:=155) (by decide +kernel)
  rw [show 2*(-863761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-863761639/4000000 : ℚ) by norm_num]
  exact coverp00011011000
private noncomputable def ep00011011001_0 : Blocks := edgeBlocks% "full/vectors/00011011001-E-0000.bin"
private noncomputable def ep00011011001_1 : Blocks := edgeBlocks% "full/vectors/00011011001-E-0001.bin"
private noncomputable def ep00011011001_2 : Blocks := edgeBlocks% "full/vectors/00011011001-E-0002.bin"
noncomputable def ep00011011001 : Blocks := (Blocks.join ep00011011001_0 (Blocks.join ep00011011001_1 ep00011011001_2))
private theorem idp00011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001101100.list =
    C ((2:ℤ)^312) * horner X vp00011011001.list + horner X ep00011011001.list := by
  exact edge_identity (B := (2:ℤ)^532) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011011001 : Branch 1 (-863761639/8000000 : ℚ) vp0001101100 := by
  apply branch_checked idp00011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-863761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-867761639/4000000 : ℚ) by norm_num]
  exact coverp00011011001
theorem coverp0001101100 : Covers (-863761639/8000000 : ℚ) vp0001101100 := join_branches bp00011011000 bp00011011001
private noncomputable def vp000110110_0 : Blocks := edgeBlocks% "full/vectors/000110110-V-0000.bin"
private noncomputable def vp000110110_1 : Blocks := edgeBlocks% "full/vectors/000110110-V-0001.bin"
private noncomputable def vp000110110_2 : Blocks := edgeBlocks% "full/vectors/000110110-V-0002.bin"
private noncomputable def vp000110110_3 : Blocks := edgeBlocks% "full/vectors/000110110-V-0003.bin"
private noncomputable def vp000110110_4 : Blocks := edgeBlocks% "full/vectors/000110110-V-0004.bin"
noncomputable def vp000110110 : Blocks := (Blocks.join (Blocks.join vp000110110_0 vp000110110_1) (Blocks.join vp000110110_2 (Blocks.join vp000110110_3 vp000110110_4)))
private theorem bp0001101100 : Branch 0 (-863761639/16000000 : ℚ) vp000110110 := by
  apply branch_left_normalized (c:=vp0001101100) (k:=0) (m:=289) (by decide +kernel)
  rw [show 2*(-863761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-863761639/8000000 : ℚ) by norm_num]
  exact coverp0001101100
private noncomputable def ep0001101101_0 : Blocks := edgeBlocks% "full/vectors/0001101101-E-0000.bin"
private noncomputable def ep0001101101_1 : Blocks := edgeBlocks% "full/vectors/0001101101-E-0001.bin"
private noncomputable def ep0001101101_2 : Blocks := edgeBlocks% "full/vectors/0001101101-E-0002.bin"
private noncomputable def ep0001101101_3 : Blocks := edgeBlocks% "full/vectors/0001101101-E-0003.bin"
private noncomputable def ep0001101101_4 : Blocks := edgeBlocks% "full/vectors/0001101101-E-0004.bin"
noncomputable def ep0001101101 : Blocks := (Blocks.join (Blocks.join ep0001101101_0 ep0001101101_1) (Blocks.join ep0001101101_2 (Blocks.join ep0001101101_3 ep0001101101_4)))
private theorem idp0001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110110.list =
    C ((2:ℤ)^599) * horner X vp0001101101.list + horner X ep0001101101.list := by
  exact edge_identity (B := (2:ℤ)^938) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001101101 : Branch 1 (-863761639/16000000 : ℚ) vp000110110 := by
  apply branch_checked idp0001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-863761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-871761639/8000000 : ℚ) by norm_num]
  exact coverp0001101101
theorem coverp000110110 : Covers (-863761639/16000000 : ℚ) vp000110110 := join_branches bp0001101100 bp0001101101
private noncomputable def vp00011011_0 : Blocks := edgeBlocks% "full/vectors/00011011-V-0000.bin"
private noncomputable def vp00011011_1 : Blocks := edgeBlocks% "full/vectors/00011011-V-0001.bin"
private noncomputable def vp00011011_2 : Blocks := edgeBlocks% "full/vectors/00011011-V-0002.bin"
private noncomputable def vp00011011_3 : Blocks := edgeBlocks% "full/vectors/00011011-V-0003.bin"
private noncomputable def vp00011011_4 : Blocks := edgeBlocks% "full/vectors/00011011-V-0004.bin"
private noncomputable def vp00011011_5 : Blocks := edgeBlocks% "full/vectors/00011011-V-0005.bin"
private noncomputable def vp00011011_6 : Blocks := edgeBlocks% "full/vectors/00011011-V-0006.bin"
private noncomputable def vp00011011_7 : Blocks := edgeBlocks% "full/vectors/00011011-V-0007.bin"
private noncomputable def vp00011011_8 : Blocks := edgeBlocks% "full/vectors/00011011-V-0008.bin"
noncomputable def vp00011011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00011011_0 vp00011011_1) (Blocks.join vp00011011_2 vp00011011_3)) (Blocks.join (Blocks.join vp00011011_4 vp00011011_5) (Blocks.join vp00011011_6 (Blocks.join vp00011011_7 vp00011011_8))))
private theorem bp000110110 : Branch 0 (-863761639/32000000 : ℚ) vp00011011 := by
  apply branch_left_normalized (c:=vp000110110) (k:=0) (m:=553) (by decide +kernel)
  rw [show 2*(-863761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-863761639/16000000 : ℚ) by norm_num]
  exact coverp000110110
private noncomputable def ep000110111_0 : Blocks := edgeBlocks% "full/vectors/000110111-E-0000.bin"
private noncomputable def ep000110111_1 : Blocks := edgeBlocks% "full/vectors/000110111-E-0001.bin"
private noncomputable def ep000110111_2 : Blocks := edgeBlocks% "full/vectors/000110111-E-0002.bin"
private noncomputable def ep000110111_3 : Blocks := edgeBlocks% "full/vectors/000110111-E-0003.bin"
private noncomputable def ep000110111_4 : Blocks := edgeBlocks% "full/vectors/000110111-E-0004.bin"
private noncomputable def ep000110111_5 : Blocks := edgeBlocks% "full/vectors/000110111-E-0005.bin"
private noncomputable def ep000110111_6 : Blocks := edgeBlocks% "full/vectors/000110111-E-0006.bin"
private noncomputable def ep000110111_7 : Blocks := edgeBlocks% "full/vectors/000110111-E-0007.bin"
private noncomputable def ep000110111_8 : Blocks := edgeBlocks% "full/vectors/000110111-E-0008.bin"
noncomputable def ep000110111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000110111_0 ep000110111_1) (Blocks.join ep000110111_2 ep000110111_3)) (Blocks.join (Blocks.join ep000110111_4 ep000110111_5) (Blocks.join ep000110111_6 (Blocks.join ep000110111_7 ep000110111_8))))
private theorem idp000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011011.list =
    C ((2:ℤ)^1167) * horner X vp000110111.list + horner X ep000110111.list := by
  exact edge_identity (B := (2:ℤ)^1742) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110111 : Branch 1 (-863761639/32000000 : ℚ) vp00011011 := by
  apply branch_checked idp000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-863761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-879761639/16000000 : ℚ) by norm_num]
  exact coverp000110111
theorem coverp00011011 : Covers (-863761639/32000000 : ℚ) vp00011011 := join_branches bp000110110 bp000110111
end NextProof.EdgeFull

