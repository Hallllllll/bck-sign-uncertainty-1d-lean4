import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00033

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000000101111111_0 : Blocks := edgeBlocks% "full/vectors/000000101111111-V-0000.bin"
noncomputable def vp000000101111111 : Blocks := vp000000101111111_0
theorem coverp000000101111111 : Covers (-95511639/250000 : ℚ) vp000000101111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101111110_0 : Blocks := edgeBlocks% "full/vectors/000000101111110-V-0000.bin"
noncomputable def vp000000101111110 : Blocks := vp000000101111110_0
theorem coverp000000101111110 : Covers (-95261639/250000 : ℚ) vp000000101111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010111111_0 : Blocks := edgeBlocks% "full/vectors/00000010111111-V-0000.bin"
noncomputable def vp00000010111111 : Blocks := vp00000010111111_0
private theorem bp000000101111110 : Branch 0 (-95261639/500000 : ℚ) vp00000010111111 := by
  apply branch_left_normalized (c:=vp000000101111110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-95261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-95261639/250000 : ℚ) by norm_num]
  exact coverp000000101111110
private noncomputable def ep000000101111111_0 : Blocks := edgeBlocks% "full/vectors/000000101111111-E-0000.bin"
noncomputable def ep000000101111111 : Blocks := ep000000101111111_0
private theorem idp000000101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010111111.list =
    C ((2:ℤ)^67) * horner X vp000000101111111.list + horner X ep000000101111111.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101111111 : Branch 1 (-95261639/500000 : ℚ) vp00000010111111 := by
  apply branch_checked idp000000101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-95261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-95511639/250000 : ℚ) by norm_num]
  exact coverp000000101111111
theorem coverp00000010111111 : Covers (-95261639/500000 : ℚ) vp00000010111111 := join_branches bp000000101111110 bp000000101111111
private noncomputable def vp000000101111101_0 : Blocks := edgeBlocks% "full/vectors/000000101111101-V-0000.bin"
noncomputable def vp000000101111101 : Blocks := vp000000101111101_0
theorem coverp000000101111101 : Covers (-95011639/250000 : ℚ) vp000000101111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101111100_0 : Blocks := edgeBlocks% "full/vectors/000000101111100-V-0000.bin"
noncomputable def vp000000101111100 : Blocks := vp000000101111100_0
theorem coverp000000101111100 : Covers (-94761639/250000 : ℚ) vp000000101111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010111110_0 : Blocks := edgeBlocks% "full/vectors/00000010111110-V-0000.bin"
noncomputable def vp00000010111110 : Blocks := vp00000010111110_0
private theorem bp000000101111100 : Branch 0 (-94761639/500000 : ℚ) vp00000010111110 := by
  apply branch_left_normalized (c:=vp000000101111100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-94761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-94761639/250000 : ℚ) by norm_num]
  exact coverp000000101111100
private noncomputable def ep000000101111101_0 : Blocks := edgeBlocks% "full/vectors/000000101111101-E-0000.bin"
noncomputable def ep000000101111101 : Blocks := ep000000101111101_0
private theorem idp000000101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010111110.list =
    C ((2:ℤ)^66) * horner X vp000000101111101.list + horner X ep000000101111101.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101111101 : Branch 1 (-94761639/500000 : ℚ) vp00000010111110 := by
  apply branch_checked idp000000101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-94761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-95011639/250000 : ℚ) by norm_num]
  exact coverp000000101111101
theorem coverp00000010111110 : Covers (-94761639/500000 : ℚ) vp00000010111110 := join_branches bp000000101111100 bp000000101111101
private noncomputable def vp0000001011111_0 : Blocks := edgeBlocks% "full/vectors/0000001011111-V-0000.bin"
noncomputable def vp0000001011111 : Blocks := vp0000001011111_0
private theorem bp00000010111110 : Branch 0 (-94761639/1000000 : ℚ) vp0000001011111 := by
  apply branch_left_normalized (c:=vp00000010111110) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-94761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-94761639/500000 : ℚ) by norm_num]
  exact coverp00000010111110
private noncomputable def ep00000010111111_0 : Blocks := edgeBlocks% "full/vectors/00000010111111-E-0000.bin"
noncomputable def ep00000010111111 : Blocks := ep00000010111111_0
private theorem idp00000010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001011111.list =
    C ((2:ℤ)^119) * horner X vp00000010111111.list + horner X ep00000010111111.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010111111 : Branch 1 (-94761639/1000000 : ℚ) vp0000001011111 := by
  apply branch_checked idp00000010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-94761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-95261639/500000 : ℚ) by norm_num]
  exact coverp00000010111111
theorem coverp0000001011111 : Covers (-94761639/1000000 : ℚ) vp0000001011111 := join_branches bp00000010111110 bp00000010111111
private noncomputable def vp000000101111011_0 : Blocks := edgeBlocks% "full/vectors/000000101111011-V-0000.bin"
noncomputable def vp000000101111011 : Blocks := vp000000101111011_0
theorem coverp000000101111011 : Covers (-94511639/250000 : ℚ) vp000000101111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101111010_0 : Blocks := edgeBlocks% "full/vectors/000000101111010-V-0000.bin"
noncomputable def vp000000101111010 : Blocks := vp000000101111010_0
theorem coverp000000101111010 : Covers (-94261639/250000 : ℚ) vp000000101111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010111101_0 : Blocks := edgeBlocks% "full/vectors/00000010111101-V-0000.bin"
noncomputable def vp00000010111101 : Blocks := vp00000010111101_0
private theorem bp000000101111010 : Branch 0 (-94261639/500000 : ℚ) vp00000010111101 := by
  apply branch_left_normalized (c:=vp000000101111010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-94261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-94261639/250000 : ℚ) by norm_num]
  exact coverp000000101111010
private noncomputable def ep000000101111011_0 : Blocks := edgeBlocks% "full/vectors/000000101111011-E-0000.bin"
noncomputable def ep000000101111011 : Blocks := ep000000101111011_0
private theorem idp000000101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010111101.list =
    C ((2:ℤ)^67) * horner X vp000000101111011.list + horner X ep000000101111011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101111011 : Branch 1 (-94261639/500000 : ℚ) vp00000010111101 := by
  apply branch_checked idp000000101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-94261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-94511639/250000 : ℚ) by norm_num]
  exact coverp000000101111011
theorem coverp00000010111101 : Covers (-94261639/500000 : ℚ) vp00000010111101 := join_branches bp000000101111010 bp000000101111011
private noncomputable def vp00000010111100_0 : Blocks := edgeBlocks% "full/vectors/00000010111100-V-0000.bin"
noncomputable def vp00000010111100 : Blocks := vp00000010111100_0
theorem coverp00000010111100 : Covers (-93761639/500000 : ℚ) vp00000010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001011110_0 : Blocks := edgeBlocks% "full/vectors/0000001011110-V-0000.bin"
noncomputable def vp0000001011110 : Blocks := vp0000001011110_0
private theorem bp00000010111100 : Branch 0 (-93761639/1000000 : ℚ) vp0000001011110 := by
  apply branch_left_normalized (c:=vp00000010111100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-93761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-93761639/500000 : ℚ) by norm_num]
  exact coverp00000010111100
private noncomputable def ep00000010111101_0 : Blocks := edgeBlocks% "full/vectors/00000010111101-E-0000.bin"
noncomputable def ep00000010111101 : Blocks := ep00000010111101_0
private theorem idp00000010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001011110.list =
    C ((2:ℤ)^119) * horner X vp00000010111101.list + horner X ep00000010111101.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010111101 : Branch 1 (-93761639/1000000 : ℚ) vp0000001011110 := by
  apply branch_checked idp00000010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-93761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-94261639/500000 : ℚ) by norm_num]
  exact coverp00000010111101
theorem coverp0000001011110 : Covers (-93761639/1000000 : ℚ) vp0000001011110 := join_branches bp00000010111100 bp00000010111101
private noncomputable def vp000000101111_0 : Blocks := edgeBlocks% "full/vectors/000000101111-V-0000.bin"
private noncomputable def vp000000101111_1 : Blocks := edgeBlocks% "full/vectors/000000101111-V-0001.bin"
noncomputable def vp000000101111 : Blocks := (Blocks.join vp000000101111_0 vp000000101111_1)
private theorem bp0000001011110 : Branch 0 (-93761639/2000000 : ℚ) vp000000101111 := by
  apply branch_left_normalized (c:=vp0000001011110) (k:=0) (m:=116) (by decide +kernel)
  rw [show 2*(-93761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-93761639/1000000 : ℚ) by norm_num]
  exact coverp0000001011110
private noncomputable def ep0000001011111_0 : Blocks := edgeBlocks% "full/vectors/0000001011111-E-0000.bin"
private noncomputable def ep0000001011111_1 : Blocks := edgeBlocks% "full/vectors/0000001011111-E-0001.bin"
noncomputable def ep0000001011111 : Blocks := (Blocks.join ep0000001011111_0 ep0000001011111_1)
private theorem idp0000001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101111.list =
    C ((2:ℤ)^223) * horner X vp0000001011111.list + horner X ep0000001011111.list := by
  exact edge_identity (B := (2:ℤ)^414) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001011111 : Branch 1 (-93761639/2000000 : ℚ) vp000000101111 := by
  apply branch_checked idp0000001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-93761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-94761639/1000000 : ℚ) by norm_num]
  exact coverp0000001011111
theorem coverp000000101111 : Covers (-93761639/2000000 : ℚ) vp000000101111 := join_branches bp0000001011110 bp0000001011111
private noncomputable def vp00000010111011_0 : Blocks := edgeBlocks% "full/vectors/00000010111011-V-0000.bin"
noncomputable def vp00000010111011 : Blocks := vp00000010111011_0
theorem coverp00000010111011 : Covers (-93261639/500000 : ℚ) vp00000010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010111010_0 : Blocks := edgeBlocks% "full/vectors/00000010111010-V-0000.bin"
noncomputable def vp00000010111010 : Blocks := vp00000010111010_0
theorem coverp00000010111010 : Covers (-92761639/500000 : ℚ) vp00000010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001011101_0 : Blocks := edgeBlocks% "full/vectors/0000001011101-V-0000.bin"
noncomputable def vp0000001011101 : Blocks := vp0000001011101_0
private theorem bp00000010111010 : Branch 0 (-92761639/1000000 : ℚ) vp0000001011101 := by
  apply branch_left_normalized (c:=vp00000010111010) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-92761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-92761639/500000 : ℚ) by norm_num]
  exact coverp00000010111010
private noncomputable def ep00000010111011_0 : Blocks := edgeBlocks% "full/vectors/00000010111011-E-0000.bin"
noncomputable def ep00000010111011 : Blocks := ep00000010111011_0
private theorem idp00000010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001011101.list =
    C ((2:ℤ)^120) * horner X vp00000010111011.list + horner X ep00000010111011.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010111011 : Branch 1 (-92761639/1000000 : ℚ) vp0000001011101 := by
  apply branch_checked idp00000010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-92761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-93261639/500000 : ℚ) by norm_num]
  exact coverp00000010111011
theorem coverp0000001011101 : Covers (-92761639/1000000 : ℚ) vp0000001011101 := join_branches bp00000010111010 bp00000010111011
private noncomputable def vp00000010111001_0 : Blocks := edgeBlocks% "full/vectors/00000010111001-V-0000.bin"
noncomputable def vp00000010111001 : Blocks := vp00000010111001_0
theorem coverp00000010111001 : Covers (-92261639/500000 : ℚ) vp00000010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010111000_0 : Blocks := edgeBlocks% "full/vectors/00000010111000-V-0000.bin"
noncomputable def vp00000010111000 : Blocks := vp00000010111000_0
theorem coverp00000010111000 : Covers (-91761639/500000 : ℚ) vp00000010111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001011100_0 : Blocks := edgeBlocks% "full/vectors/0000001011100-V-0000.bin"
noncomputable def vp0000001011100 : Blocks := vp0000001011100_0
private theorem bp00000010111000 : Branch 0 (-91761639/1000000 : ℚ) vp0000001011100 := by
  apply branch_left_normalized (c:=vp00000010111000) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-91761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-91761639/500000 : ℚ) by norm_num]
  exact coverp00000010111000
private noncomputable def ep00000010111001_0 : Blocks := edgeBlocks% "full/vectors/00000010111001-E-0000.bin"
noncomputable def ep00000010111001 : Blocks := ep00000010111001_0
private theorem idp00000010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001011100.list =
    C ((2:ℤ)^121) * horner X vp00000010111001.list + horner X ep00000010111001.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010111001 : Branch 1 (-91761639/1000000 : ℚ) vp0000001011100 := by
  apply branch_checked idp00000010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-91761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-92261639/500000 : ℚ) by norm_num]
  exact coverp00000010111001
theorem coverp0000001011100 : Covers (-91761639/1000000 : ℚ) vp0000001011100 := join_branches bp00000010111000 bp00000010111001
private noncomputable def vp000000101110_0 : Blocks := edgeBlocks% "full/vectors/000000101110-V-0000.bin"
private noncomputable def vp000000101110_1 : Blocks := edgeBlocks% "full/vectors/000000101110-V-0001.bin"
noncomputable def vp000000101110 : Blocks := (Blocks.join vp000000101110_0 vp000000101110_1)
private theorem bp0000001011100 : Branch 0 (-91761639/2000000 : ℚ) vp000000101110 := by
  apply branch_left_normalized (c:=vp0000001011100) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-91761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-91761639/1000000 : ℚ) by norm_num]
  exact coverp0000001011100
private noncomputable def ep0000001011101_0 : Blocks := edgeBlocks% "full/vectors/0000001011101-E-0000.bin"
private noncomputable def ep0000001011101_1 : Blocks := edgeBlocks% "full/vectors/0000001011101-E-0001.bin"
noncomputable def ep0000001011101 : Blocks := (Blocks.join ep0000001011101_0 ep0000001011101_1)
private theorem idp0000001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101110.list =
    C ((2:ℤ)^226) * horner X vp0000001011101.list + horner X ep0000001011101.list := by
  exact edge_identity (B := (2:ℤ)^418) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001011101 : Branch 1 (-91761639/2000000 : ℚ) vp000000101110 := by
  apply branch_checked idp0000001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-91761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-92761639/1000000 : ℚ) by norm_num]
  exact coverp0000001011101
theorem coverp000000101110 : Covers (-91761639/2000000 : ℚ) vp000000101110 := join_branches bp0000001011100 bp0000001011101
private noncomputable def vp00000010111_0 : Blocks := edgeBlocks% "full/vectors/00000010111-V-0000.bin"
private noncomputable def vp00000010111_1 : Blocks := edgeBlocks% "full/vectors/00000010111-V-0001.bin"
private noncomputable def vp00000010111_2 : Blocks := edgeBlocks% "full/vectors/00000010111-V-0002.bin"
private noncomputable def vp00000010111_3 : Blocks := edgeBlocks% "full/vectors/00000010111-V-0003.bin"
noncomputable def vp00000010111 : Blocks := (Blocks.join (Blocks.join vp00000010111_0 vp00000010111_1) (Blocks.join vp00000010111_2 vp00000010111_3))
private theorem bp000000101110 : Branch 0 (-91761639/4000000 : ℚ) vp00000010111 := by
  apply branch_left_normalized (c:=vp000000101110) (k:=0) (m:=219) (by decide +kernel)
  rw [show 2*(-91761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-91761639/2000000 : ℚ) by norm_num]
  exact coverp000000101110
private noncomputable def ep000000101111_0 : Blocks := edgeBlocks% "full/vectors/000000101111-E-0000.bin"
private noncomputable def ep000000101111_1 : Blocks := edgeBlocks% "full/vectors/000000101111-E-0001.bin"
private noncomputable def ep000000101111_2 : Blocks := edgeBlocks% "full/vectors/000000101111-E-0002.bin"
private noncomputable def ep000000101111_3 : Blocks := edgeBlocks% "full/vectors/000000101111-E-0003.bin"
noncomputable def ep000000101111 : Blocks := (Blocks.join (Blocks.join ep000000101111_0 ep000000101111_1) (Blocks.join ep000000101111_2 ep000000101111_3))
private theorem idp000000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010111.list =
    C ((2:ℤ)^435) * horner X vp000000101111.list + horner X ep000000101111.list := by
  exact edge_identity (B := (2:ℤ)^729) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101111 : Branch 1 (-91761639/4000000 : ℚ) vp00000010111 := by
  apply branch_checked idp000000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-91761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-93761639/2000000 : ℚ) by norm_num]
  exact coverp000000101111
theorem coverp00000010111 : Covers (-91761639/4000000 : ℚ) vp00000010111 := join_branches bp000000101110 bp000000101111
private noncomputable def vp00000010110111_0 : Blocks := edgeBlocks% "full/vectors/00000010110111-V-0000.bin"
noncomputable def vp00000010110111 : Blocks := vp00000010110111_0
theorem coverp00000010110111 : Covers (-91261639/500000 : ℚ) vp00000010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010110110_0 : Blocks := edgeBlocks% "full/vectors/00000010110110-V-0000.bin"
noncomputable def vp00000010110110 : Blocks := vp00000010110110_0
theorem coverp00000010110110 : Covers (-90761639/500000 : ℚ) vp00000010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001011011_0 : Blocks := edgeBlocks% "full/vectors/0000001011011-V-0000.bin"
noncomputable def vp0000001011011 : Blocks := vp0000001011011_0
private theorem bp00000010110110 : Branch 0 (-90761639/1000000 : ℚ) vp0000001011011 := by
  apply branch_left_normalized (c:=vp00000010110110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-90761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-90761639/500000 : ℚ) by norm_num]
  exact coverp00000010110110
private noncomputable def ep00000010110111_0 : Blocks := edgeBlocks% "full/vectors/00000010110111-E-0000.bin"
noncomputable def ep00000010110111 : Blocks := ep00000010110111_0
private theorem idp00000010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001011011.list =
    C ((2:ℤ)^121) * horner X vp00000010110111.list + horner X ep00000010110111.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010110111 : Branch 1 (-90761639/1000000 : ℚ) vp0000001011011 := by
  apply branch_checked idp00000010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-90761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-91261639/500000 : ℚ) by norm_num]
  exact coverp00000010110111
theorem coverp0000001011011 : Covers (-90761639/1000000 : ℚ) vp0000001011011 := join_branches bp00000010110110 bp00000010110111
private noncomputable def vp000000101101011_0 : Blocks := edgeBlocks% "full/vectors/000000101101011-V-0000.bin"
noncomputable def vp000000101101011 : Blocks := vp000000101101011_0
theorem coverp000000101101011 : Covers (-90511639/250000 : ℚ) vp000000101101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101101010_0 : Blocks := edgeBlocks% "full/vectors/000000101101010-V-0000.bin"
noncomputable def vp000000101101010 : Blocks := vp000000101101010_0
theorem coverp000000101101010 : Covers (-90261639/250000 : ℚ) vp000000101101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010110101_0 : Blocks := edgeBlocks% "full/vectors/00000010110101-V-0000.bin"
noncomputable def vp00000010110101 : Blocks := vp00000010110101_0
private theorem bp000000101101010 : Branch 0 (-90261639/500000 : ℚ) vp00000010110101 := by
  apply branch_left_normalized (c:=vp000000101101010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-90261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-90261639/250000 : ℚ) by norm_num]
  exact coverp000000101101010
private noncomputable def ep000000101101011_0 : Blocks := edgeBlocks% "full/vectors/000000101101011-E-0000.bin"
noncomputable def ep000000101101011 : Blocks := ep000000101101011_0
private theorem idp000000101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010110101.list =
    C ((2:ℤ)^69) * horner X vp000000101101011.list + horner X ep000000101101011.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101101011 : Branch 1 (-90261639/500000 : ℚ) vp00000010110101 := by
  apply branch_checked idp000000101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-90261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-90511639/250000 : ℚ) by norm_num]
  exact coverp000000101101011
theorem coverp00000010110101 : Covers (-90261639/500000 : ℚ) vp00000010110101 := join_branches bp000000101101010 bp000000101101011
private noncomputable def vp000000101101001_0 : Blocks := edgeBlocks% "full/vectors/000000101101001-V-0000.bin"
noncomputable def vp000000101101001 : Blocks := vp000000101101001_0
theorem coverp000000101101001 : Covers (-90011639/250000 : ℚ) vp000000101101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101101000_0 : Blocks := edgeBlocks% "full/vectors/000000101101000-V-0000.bin"
noncomputable def vp000000101101000 : Blocks := vp000000101101000_0
theorem coverp000000101101000 : Covers (-89761639/250000 : ℚ) vp000000101101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010110100_0 : Blocks := edgeBlocks% "full/vectors/00000010110100-V-0000.bin"
noncomputable def vp00000010110100 : Blocks := vp00000010110100_0
private theorem bp000000101101000 : Branch 0 (-89761639/500000 : ℚ) vp00000010110100 := by
  apply branch_left_normalized (c:=vp000000101101000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-89761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-89761639/250000 : ℚ) by norm_num]
  exact coverp000000101101000
private noncomputable def ep000000101101001_0 : Blocks := edgeBlocks% "full/vectors/000000101101001-E-0000.bin"
noncomputable def ep000000101101001 : Blocks := ep000000101101001_0
private theorem idp000000101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010110100.list =
    C ((2:ℤ)^68) * horner X vp000000101101001.list + horner X ep000000101101001.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101101001 : Branch 1 (-89761639/500000 : ℚ) vp00000010110100 := by
  apply branch_checked idp000000101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-89761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-90011639/250000 : ℚ) by norm_num]
  exact coverp000000101101001
theorem coverp00000010110100 : Covers (-89761639/500000 : ℚ) vp00000010110100 := join_branches bp000000101101000 bp000000101101001
private noncomputable def vp0000001011010_0 : Blocks := edgeBlocks% "full/vectors/0000001011010-V-0000.bin"
noncomputable def vp0000001011010 : Blocks := vp0000001011010_0
private theorem bp00000010110100 : Branch 0 (-89761639/1000000 : ℚ) vp0000001011010 := by
  apply branch_left_normalized (c:=vp00000010110100) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-89761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-89761639/500000 : ℚ) by norm_num]
  exact coverp00000010110100
private noncomputable def ep00000010110101_0 : Blocks := edgeBlocks% "full/vectors/00000010110101-E-0000.bin"
noncomputable def ep00000010110101 : Blocks := ep00000010110101_0
private theorem idp00000010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001011010.list =
    C ((2:ℤ)^121) * horner X vp00000010110101.list + horner X ep00000010110101.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010110101 : Branch 1 (-89761639/1000000 : ℚ) vp0000001011010 := by
  apply branch_checked idp00000010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-89761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-90261639/500000 : ℚ) by norm_num]
  exact coverp00000010110101
theorem coverp0000001011010 : Covers (-89761639/1000000 : ℚ) vp0000001011010 := join_branches bp00000010110100 bp00000010110101
private noncomputable def vp000000101101_0 : Blocks := edgeBlocks% "full/vectors/000000101101-V-0000.bin"
private noncomputable def vp000000101101_1 : Blocks := edgeBlocks% "full/vectors/000000101101-V-0001.bin"
noncomputable def vp000000101101 : Blocks := (Blocks.join vp000000101101_0 vp000000101101_1)
private theorem bp0000001011010 : Branch 0 (-89761639/2000000 : ℚ) vp000000101101 := by
  apply branch_left_normalized (c:=vp0000001011010) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-89761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-89761639/1000000 : ℚ) by norm_num]
  exact coverp0000001011010
private noncomputable def ep0000001011011_0 : Blocks := edgeBlocks% "full/vectors/0000001011011-E-0000.bin"
private noncomputable def ep0000001011011_1 : Blocks := edgeBlocks% "full/vectors/0000001011011-E-0001.bin"
noncomputable def ep0000001011011 : Blocks := (Blocks.join ep0000001011011_0 ep0000001011011_1)
private theorem idp0000001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101101.list =
    C ((2:ℤ)^229) * horner X vp0000001011011.list + horner X ep0000001011011.list := by
  exact edge_identity (B := (2:ℤ)^422) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001011011 : Branch 1 (-89761639/2000000 : ℚ) vp000000101101 := by
  apply branch_checked idp0000001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-89761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-90761639/1000000 : ℚ) by norm_num]
  exact coverp0000001011011
theorem coverp000000101101 : Covers (-89761639/2000000 : ℚ) vp000000101101 := join_branches bp0000001011010 bp0000001011011
private noncomputable def vp000000101100111_0 : Blocks := edgeBlocks% "full/vectors/000000101100111-V-0000.bin"
noncomputable def vp000000101100111 : Blocks := vp000000101100111_0
theorem coverp000000101100111 : Covers (-89511639/250000 : ℚ) vp000000101100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101100110_0 : Blocks := edgeBlocks% "full/vectors/000000101100110-V-0000.bin"
noncomputable def vp000000101100110 : Blocks := vp000000101100110_0
theorem coverp000000101100110 : Covers (-89261639/250000 : ℚ) vp000000101100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010110011_0 : Blocks := edgeBlocks% "full/vectors/00000010110011-V-0000.bin"
noncomputable def vp00000010110011 : Blocks := vp00000010110011_0
private theorem bp000000101100110 : Branch 0 (-89261639/500000 : ℚ) vp00000010110011 := by
  apply branch_left_normalized (c:=vp000000101100110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-89261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-89261639/250000 : ℚ) by norm_num]
  exact coverp000000101100110
private noncomputable def ep000000101100111_0 : Blocks := edgeBlocks% "full/vectors/000000101100111-E-0000.bin"
noncomputable def ep000000101100111 : Blocks := ep000000101100111_0
private theorem idp000000101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010110011.list =
    C ((2:ℤ)^68) * horner X vp000000101100111.list + horner X ep000000101100111.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101100111 : Branch 1 (-89261639/500000 : ℚ) vp00000010110011 := by
  apply branch_checked idp000000101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-89261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-89511639/250000 : ℚ) by norm_num]
  exact coverp000000101100111
theorem coverp00000010110011 : Covers (-89261639/500000 : ℚ) vp00000010110011 := join_branches bp000000101100110 bp000000101100111
private noncomputable def vp000000101100101_0 : Blocks := edgeBlocks% "full/vectors/000000101100101-V-0000.bin"
noncomputable def vp000000101100101 : Blocks := vp000000101100101_0
theorem coverp000000101100101 : Covers (-89011639/250000 : ℚ) vp000000101100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101100100_0 : Blocks := edgeBlocks% "full/vectors/000000101100100-V-0000.bin"
noncomputable def vp000000101100100 : Blocks := vp000000101100100_0
theorem coverp000000101100100 : Covers (-88761639/250000 : ℚ) vp000000101100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010110010_0 : Blocks := edgeBlocks% "full/vectors/00000010110010-V-0000.bin"
noncomputable def vp00000010110010 : Blocks := vp00000010110010_0
private theorem bp000000101100100 : Branch 0 (-88761639/500000 : ℚ) vp00000010110010 := by
  apply branch_left_normalized (c:=vp000000101100100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-88761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-88761639/250000 : ℚ) by norm_num]
  exact coverp000000101100100
private noncomputable def ep000000101100101_0 : Blocks := edgeBlocks% "full/vectors/000000101100101-E-0000.bin"
noncomputable def ep000000101100101 : Blocks := ep000000101100101_0
private theorem idp000000101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010110010.list =
    C ((2:ℤ)^69) * horner X vp000000101100101.list + horner X ep000000101100101.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101100101 : Branch 1 (-88761639/500000 : ℚ) vp00000010110010 := by
  apply branch_checked idp000000101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-88761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-89011639/250000 : ℚ) by norm_num]
  exact coverp000000101100101
theorem coverp00000010110010 : Covers (-88761639/500000 : ℚ) vp00000010110010 := join_branches bp000000101100100 bp000000101100101
private noncomputable def vp0000001011001_0 : Blocks := edgeBlocks% "full/vectors/0000001011001-V-0000.bin"
noncomputable def vp0000001011001 : Blocks := vp0000001011001_0
private theorem bp00000010110010 : Branch 0 (-88761639/1000000 : ℚ) vp0000001011001 := by
  apply branch_left_normalized (c:=vp00000010110010) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-88761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-88761639/500000 : ℚ) by norm_num]
  exact coverp00000010110010
private noncomputable def ep00000010110011_0 : Blocks := edgeBlocks% "full/vectors/00000010110011-E-0000.bin"
noncomputable def ep00000010110011 : Blocks := ep00000010110011_0
private theorem idp00000010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001011001.list =
    C ((2:ℤ)^124) * horner X vp00000010110011.list + horner X ep00000010110011.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010110011 : Branch 1 (-88761639/1000000 : ℚ) vp0000001011001 := by
  apply branch_checked idp00000010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-88761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-89261639/500000 : ℚ) by norm_num]
  exact coverp00000010110011
theorem coverp0000001011001 : Covers (-88761639/1000000 : ℚ) vp0000001011001 := join_branches bp00000010110010 bp00000010110011
private noncomputable def vp000000101100011_0 : Blocks := edgeBlocks% "full/vectors/000000101100011-V-0000.bin"
noncomputable def vp000000101100011 : Blocks := vp000000101100011_0
theorem coverp000000101100011 : Covers (-88511639/250000 : ℚ) vp000000101100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101100010_0 : Blocks := edgeBlocks% "full/vectors/000000101100010-V-0000.bin"
noncomputable def vp000000101100010 : Blocks := vp000000101100010_0
theorem coverp000000101100010 : Covers (-88261639/250000 : ℚ) vp000000101100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010110001_0 : Blocks := edgeBlocks% "full/vectors/00000010110001-V-0000.bin"
noncomputable def vp00000010110001 : Blocks := vp00000010110001_0
private theorem bp000000101100010 : Branch 0 (-88261639/500000 : ℚ) vp00000010110001 := by
  apply branch_left_normalized (c:=vp000000101100010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-88261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-88261639/250000 : ℚ) by norm_num]
  exact coverp000000101100010
private noncomputable def ep000000101100011_0 : Blocks := edgeBlocks% "full/vectors/000000101100011-E-0000.bin"
noncomputable def ep000000101100011 : Blocks := ep000000101100011_0
private theorem idp000000101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010110001.list =
    C ((2:ℤ)^70) * horner X vp000000101100011.list + horner X ep000000101100011.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101100011 : Branch 1 (-88261639/500000 : ℚ) vp00000010110001 := by
  apply branch_checked idp000000101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-88261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-88511639/250000 : ℚ) by norm_num]
  exact coverp000000101100011
theorem coverp00000010110001 : Covers (-88261639/500000 : ℚ) vp00000010110001 := join_branches bp000000101100010 bp000000101100011
private noncomputable def vp000000101100001_0 : Blocks := edgeBlocks% "full/vectors/000000101100001-V-0000.bin"
noncomputable def vp000000101100001 : Blocks := vp000000101100001_0
theorem coverp000000101100001 : Covers (-88011639/250000 : ℚ) vp000000101100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101100000_0 : Blocks := edgeBlocks% "full/vectors/000000101100000-V-0000.bin"
noncomputable def vp000000101100000 : Blocks := vp000000101100000_0
theorem coverp000000101100000 : Covers (-87761639/250000 : ℚ) vp000000101100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010110000_0 : Blocks := edgeBlocks% "full/vectors/00000010110000-V-0000.bin"
noncomputable def vp00000010110000 : Blocks := vp00000010110000_0
private theorem bp000000101100000 : Branch 0 (-87761639/500000 : ℚ) vp00000010110000 := by
  apply branch_left_normalized (c:=vp000000101100000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-87761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-87761639/250000 : ℚ) by norm_num]
  exact coverp000000101100000
private noncomputable def ep000000101100001_0 : Blocks := edgeBlocks% "full/vectors/000000101100001-E-0000.bin"
noncomputable def ep000000101100001 : Blocks := ep000000101100001_0
private theorem idp000000101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010110000.list =
    C ((2:ℤ)^71) * horner X vp000000101100001.list + horner X ep000000101100001.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101100001 : Branch 1 (-87761639/500000 : ℚ) vp00000010110000 := by
  apply branch_checked idp000000101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-87761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-88011639/250000 : ℚ) by norm_num]
  exact coverp000000101100001
theorem coverp00000010110000 : Covers (-87761639/500000 : ℚ) vp00000010110000 := join_branches bp000000101100000 bp000000101100001
private noncomputable def vp0000001011000_0 : Blocks := edgeBlocks% "full/vectors/0000001011000-V-0000.bin"
noncomputable def vp0000001011000 : Blocks := vp0000001011000_0
private theorem bp00000010110000 : Branch 0 (-87761639/1000000 : ℚ) vp0000001011000 := by
  apply branch_left_normalized (c:=vp00000010110000) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-87761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-87761639/500000 : ℚ) by norm_num]
  exact coverp00000010110000
private noncomputable def ep00000010110001_0 : Blocks := edgeBlocks% "full/vectors/00000010110001-E-0000.bin"
noncomputable def ep00000010110001 : Blocks := ep00000010110001_0
private theorem idp00000010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001011000.list =
    C ((2:ℤ)^125) * horner X vp00000010110001.list + horner X ep00000010110001.list := by
  exact edge_identity (B := (2:ℤ)^269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010110001 : Branch 1 (-87761639/1000000 : ℚ) vp0000001011000 := by
  apply branch_checked idp00000010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-87761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-88261639/500000 : ℚ) by norm_num]
  exact coverp00000010110001
theorem coverp0000001011000 : Covers (-87761639/1000000 : ℚ) vp0000001011000 := join_branches bp00000010110000 bp00000010110001
private noncomputable def vp000000101100_0 : Blocks := edgeBlocks% "full/vectors/000000101100-V-0000.bin"
private noncomputable def vp000000101100_1 : Blocks := edgeBlocks% "full/vectors/000000101100-V-0001.bin"
noncomputable def vp000000101100 : Blocks := (Blocks.join vp000000101100_0 vp000000101100_1)
private theorem bp0000001011000 : Branch 0 (-87761639/2000000 : ℚ) vp000000101100 := by
  apply branch_left_normalized (c:=vp0000001011000) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-87761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-87761639/1000000 : ℚ) by norm_num]
  exact coverp0000001011000
private noncomputable def ep0000001011001_0 : Blocks := edgeBlocks% "full/vectors/0000001011001-E-0000.bin"
private noncomputable def ep0000001011001_1 : Blocks := edgeBlocks% "full/vectors/0000001011001-E-0001.bin"
noncomputable def ep0000001011001 : Blocks := (Blocks.join ep0000001011001_0 ep0000001011001_1)
private theorem idp0000001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101100.list =
    C ((2:ℤ)^233) * horner X vp0000001011001.list + horner X ep0000001011001.list := by
  exact edge_identity (B := (2:ℤ)^429) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001011001 : Branch 1 (-87761639/2000000 : ℚ) vp000000101100 := by
  apply branch_checked idp0000001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-87761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-88761639/1000000 : ℚ) by norm_num]
  exact coverp0000001011001
theorem coverp000000101100 : Covers (-87761639/2000000 : ℚ) vp000000101100 := join_branches bp0000001011000 bp0000001011001
private noncomputable def vp00000010110_0 : Blocks := edgeBlocks% "full/vectors/00000010110-V-0000.bin"
private noncomputable def vp00000010110_1 : Blocks := edgeBlocks% "full/vectors/00000010110-V-0001.bin"
private noncomputable def vp00000010110_2 : Blocks := edgeBlocks% "full/vectors/00000010110-V-0002.bin"
private noncomputable def vp00000010110_3 : Blocks := edgeBlocks% "full/vectors/00000010110-V-0003.bin"
noncomputable def vp00000010110 : Blocks := (Blocks.join (Blocks.join vp00000010110_0 vp00000010110_1) (Blocks.join vp00000010110_2 vp00000010110_3))
private theorem bp000000101100 : Branch 0 (-87761639/4000000 : ℚ) vp00000010110 := by
  apply branch_left_normalized (c:=vp000000101100) (k:=0) (m:=225) (by decide +kernel)
  rw [show 2*(-87761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-87761639/2000000 : ℚ) by norm_num]
  exact coverp000000101100
private noncomputable def ep000000101101_0 : Blocks := edgeBlocks% "full/vectors/000000101101-E-0000.bin"
private noncomputable def ep000000101101_1 : Blocks := edgeBlocks% "full/vectors/000000101101-E-0001.bin"
private noncomputable def ep000000101101_2 : Blocks := edgeBlocks% "full/vectors/000000101101-E-0002.bin"
private noncomputable def ep000000101101_3 : Blocks := edgeBlocks% "full/vectors/000000101101-E-0003.bin"
noncomputable def ep000000101101 : Blocks := (Blocks.join (Blocks.join ep000000101101_0 ep000000101101_1) (Blocks.join ep000000101101_2 ep000000101101_3))
private theorem idp000000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010110.list =
    C ((2:ℤ)^448) * horner X vp000000101101.list + horner X ep000000101101.list := by
  exact edge_identity (B := (2:ℤ)^748) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101101 : Branch 1 (-87761639/4000000 : ℚ) vp00000010110 := by
  apply branch_checked idp000000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-87761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-89761639/2000000 : ℚ) by norm_num]
  exact coverp000000101101
theorem coverp00000010110 : Covers (-87761639/4000000 : ℚ) vp00000010110 := join_branches bp000000101100 bp000000101101
private noncomputable def vp0000001011_0 : Blocks := edgeBlocks% "full/vectors/0000001011-V-0000.bin"
private noncomputable def vp0000001011_1 : Blocks := edgeBlocks% "full/vectors/0000001011-V-0001.bin"
private noncomputable def vp0000001011_2 : Blocks := edgeBlocks% "full/vectors/0000001011-V-0002.bin"
private noncomputable def vp0000001011_3 : Blocks := edgeBlocks% "full/vectors/0000001011-V-0003.bin"
private noncomputable def vp0000001011_4 : Blocks := edgeBlocks% "full/vectors/0000001011-V-0004.bin"
private noncomputable def vp0000001011_5 : Blocks := edgeBlocks% "full/vectors/0000001011-V-0005.bin"
private noncomputable def vp0000001011_6 : Blocks := edgeBlocks% "full/vectors/0000001011-V-0006.bin"
noncomputable def vp0000001011 : Blocks := (Blocks.join (Blocks.join vp0000001011_0 (Blocks.join vp0000001011_1 vp0000001011_2)) (Blocks.join (Blocks.join vp0000001011_3 vp0000001011_4) (Blocks.join vp0000001011_5 vp0000001011_6)))
private theorem bp00000010110 : Branch 0 (-87761639/8000000 : ℚ) vp0000001011 := by
  apply branch_left_normalized (c:=vp00000010110) (k:=0) (m:=433) (by decide +kernel)
  rw [show 2*(-87761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-87761639/4000000 : ℚ) by norm_num]
  exact coverp00000010110
private noncomputable def ep00000010111_0 : Blocks := edgeBlocks% "full/vectors/00000010111-E-0000.bin"
private noncomputable def ep00000010111_1 : Blocks := edgeBlocks% "full/vectors/00000010111-E-0001.bin"
private noncomputable def ep00000010111_2 : Blocks := edgeBlocks% "full/vectors/00000010111-E-0002.bin"
private noncomputable def ep00000010111_3 : Blocks := edgeBlocks% "full/vectors/00000010111-E-0003.bin"
private noncomputable def ep00000010111_4 : Blocks := edgeBlocks% "full/vectors/00000010111-E-0004.bin"
private noncomputable def ep00000010111_5 : Blocks := edgeBlocks% "full/vectors/00000010111-E-0005.bin"
private noncomputable def ep00000010111_6 : Blocks := edgeBlocks% "full/vectors/00000010111-E-0006.bin"
noncomputable def ep00000010111 : Blocks := (Blocks.join (Blocks.join ep00000010111_0 (Blocks.join ep00000010111_1 ep00000010111_2)) (Blocks.join (Blocks.join ep00000010111_3 ep00000010111_4) (Blocks.join ep00000010111_5 ep00000010111_6)))
private theorem idp00000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001011.list =
    C ((2:ℤ)^872) * horner X vp00000010111.list + horner X ep00000010111.list := by
  exact edge_identity (B := (2:ℤ)^1381) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010111 : Branch 1 (-87761639/8000000 : ℚ) vp0000001011 := by
  apply branch_checked idp00000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-87761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-91761639/4000000 : ℚ) by norm_num]
  exact coverp00000010111
theorem coverp0000001011 : Covers (-87761639/8000000 : ℚ) vp0000001011 := join_branches bp00000010110 bp00000010111
private noncomputable def vp000000101011111_0 : Blocks := edgeBlocks% "full/vectors/000000101011111-V-0000.bin"
noncomputable def vp000000101011111 : Blocks := vp000000101011111_0
theorem coverp000000101011111 : Covers (-87511639/250000 : ℚ) vp000000101011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101011110_0 : Blocks := edgeBlocks% "full/vectors/000000101011110-V-0000.bin"
noncomputable def vp000000101011110 : Blocks := vp000000101011110_0
theorem coverp000000101011110 : Covers (-87261639/250000 : ℚ) vp000000101011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010101111_0 : Blocks := edgeBlocks% "full/vectors/00000010101111-V-0000.bin"
noncomputable def vp00000010101111 : Blocks := vp00000010101111_0
private theorem bp000000101011110 : Branch 0 (-87261639/500000 : ℚ) vp00000010101111 := by
  apply branch_left_normalized (c:=vp000000101011110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-87261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-87261639/250000 : ℚ) by norm_num]
  exact coverp000000101011110
private noncomputable def ep000000101011111_0 : Blocks := edgeBlocks% "full/vectors/000000101011111-E-0000.bin"
noncomputable def ep000000101011111 : Blocks := ep000000101011111_0
private theorem idp000000101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010101111.list =
    C ((2:ℤ)^71) * horner X vp000000101011111.list + horner X ep000000101011111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101011111 : Branch 1 (-87261639/500000 : ℚ) vp00000010101111 := by
  apply branch_checked idp000000101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-87261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-87511639/250000 : ℚ) by norm_num]
  exact coverp000000101011111
theorem coverp00000010101111 : Covers (-87261639/500000 : ℚ) vp00000010101111 := join_branches bp000000101011110 bp000000101011111
private noncomputable def vp000000101011101_0 : Blocks := edgeBlocks% "full/vectors/000000101011101-V-0000.bin"
noncomputable def vp000000101011101 : Blocks := vp000000101011101_0
theorem coverp000000101011101 : Covers (-87011639/250000 : ℚ) vp000000101011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101011100_0 : Blocks := edgeBlocks% "full/vectors/000000101011100-V-0000.bin"
noncomputable def vp000000101011100 : Blocks := vp000000101011100_0
theorem coverp000000101011100 : Covers (-86761639/250000 : ℚ) vp000000101011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010101110_0 : Blocks := edgeBlocks% "full/vectors/00000010101110-V-0000.bin"
noncomputable def vp00000010101110 : Blocks := vp00000010101110_0
private theorem bp000000101011100 : Branch 0 (-86761639/500000 : ℚ) vp00000010101110 := by
  apply branch_left_normalized (c:=vp000000101011100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-86761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-86761639/250000 : ℚ) by norm_num]
  exact coverp000000101011100
private noncomputable def ep000000101011101_0 : Blocks := edgeBlocks% "full/vectors/000000101011101-E-0000.bin"
noncomputable def ep000000101011101 : Blocks := ep000000101011101_0
private theorem idp000000101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010101110.list =
    C ((2:ℤ)^72) * horner X vp000000101011101.list + horner X ep000000101011101.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101011101 : Branch 1 (-86761639/500000 : ℚ) vp00000010101110 := by
  apply branch_checked idp000000101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-86761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-87011639/250000 : ℚ) by norm_num]
  exact coverp000000101011101
theorem coverp00000010101110 : Covers (-86761639/500000 : ℚ) vp00000010101110 := join_branches bp000000101011100 bp000000101011101
private noncomputable def vp0000001010111_0 : Blocks := edgeBlocks% "full/vectors/0000001010111-V-0000.bin"
noncomputable def vp0000001010111 : Blocks := vp0000001010111_0
private theorem bp00000010101110 : Branch 0 (-86761639/1000000 : ℚ) vp0000001010111 := by
  apply branch_left_normalized (c:=vp00000010101110) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-86761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-86761639/500000 : ℚ) by norm_num]
  exact coverp00000010101110
private noncomputable def ep00000010101111_0 : Blocks := edgeBlocks% "full/vectors/00000010101111-E-0000.bin"
noncomputable def ep00000010101111 : Blocks := ep00000010101111_0
private theorem idp00000010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001010111.list =
    C ((2:ℤ)^127) * horner X vp00000010101111.list + horner X ep00000010101111.list := by
  exact edge_identity (B := (2:ℤ)^273) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010101111 : Branch 1 (-86761639/1000000 : ℚ) vp0000001010111 := by
  apply branch_checked idp00000010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-86761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-87261639/500000 : ℚ) by norm_num]
  exact coverp00000010101111
theorem coverp0000001010111 : Covers (-86761639/1000000 : ℚ) vp0000001010111 := join_branches bp00000010101110 bp00000010101111
private noncomputable def vp000000101011011_0 : Blocks := edgeBlocks% "full/vectors/000000101011011-V-0000.bin"
noncomputable def vp000000101011011 : Blocks := vp000000101011011_0
theorem coverp000000101011011 : Covers (-86511639/250000 : ℚ) vp000000101011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101011010_0 : Blocks := edgeBlocks% "full/vectors/000000101011010-V-0000.bin"
noncomputable def vp000000101011010 : Blocks := vp000000101011010_0
theorem coverp000000101011010 : Covers (-86261639/250000 : ℚ) vp000000101011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010101101_0 : Blocks := edgeBlocks% "full/vectors/00000010101101-V-0000.bin"
noncomputable def vp00000010101101 : Blocks := vp00000010101101_0
private theorem bp000000101011010 : Branch 0 (-86261639/500000 : ℚ) vp00000010101101 := by
  apply branch_left_normalized (c:=vp000000101011010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-86261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-86261639/250000 : ℚ) by norm_num]
  exact coverp000000101011010
private noncomputable def ep000000101011011_0 : Blocks := edgeBlocks% "full/vectors/000000101011011-E-0000.bin"
noncomputable def ep000000101011011 : Blocks := ep000000101011011_0
private theorem idp000000101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010101101.list =
    C ((2:ℤ)^73) * horner X vp000000101011011.list + horner X ep000000101011011.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101011011 : Branch 1 (-86261639/500000 : ℚ) vp00000010101101 := by
  apply branch_checked idp000000101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-86261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-86511639/250000 : ℚ) by norm_num]
  exact coverp000000101011011
theorem coverp00000010101101 : Covers (-86261639/500000 : ℚ) vp00000010101101 := join_branches bp000000101011010 bp000000101011011
private noncomputable def vp000000101011001_0 : Blocks := edgeBlocks% "full/vectors/000000101011001-V-0000.bin"
noncomputable def vp000000101011001 : Blocks := vp000000101011001_0
theorem coverp000000101011001 : Covers (-86011639/250000 : ℚ) vp000000101011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101011000_0 : Blocks := edgeBlocks% "full/vectors/000000101011000-V-0000.bin"
noncomputable def vp000000101011000 : Blocks := vp000000101011000_0
theorem coverp000000101011000 : Covers (-85761639/250000 : ℚ) vp000000101011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010101100_0 : Blocks := edgeBlocks% "full/vectors/00000010101100-V-0000.bin"
noncomputable def vp00000010101100 : Blocks := vp00000010101100_0
private theorem bp000000101011000 : Branch 0 (-85761639/500000 : ℚ) vp00000010101100 := by
  apply branch_left_normalized (c:=vp000000101011000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-85761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-85761639/250000 : ℚ) by norm_num]
  exact coverp000000101011000
private noncomputable def ep000000101011001_0 : Blocks := edgeBlocks% "full/vectors/000000101011001-E-0000.bin"
noncomputable def ep000000101011001 : Blocks := ep000000101011001_0
private theorem idp000000101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010101100.list =
    C ((2:ℤ)^77) * horner X vp000000101011001.list + horner X ep000000101011001.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101011001 : Branch 1 (-85761639/500000 : ℚ) vp00000010101100 := by
  apply branch_checked idp000000101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-85761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-86011639/250000 : ℚ) by norm_num]
  exact coverp000000101011001
theorem coverp00000010101100 : Covers (-85761639/500000 : ℚ) vp00000010101100 := join_branches bp000000101011000 bp000000101011001
private noncomputable def vp0000001010110_0 : Blocks := edgeBlocks% "full/vectors/0000001010110-V-0000.bin"
noncomputable def vp0000001010110 : Blocks := vp0000001010110_0
private theorem bp00000010101100 : Branch 0 (-85761639/1000000 : ℚ) vp0000001010110 := by
  apply branch_left_normalized (c:=vp00000010101100) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-85761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-85761639/500000 : ℚ) by norm_num]
  exact coverp00000010101100
private noncomputable def ep00000010101101_0 : Blocks := edgeBlocks% "full/vectors/00000010101101-E-0000.bin"
noncomputable def ep00000010101101 : Blocks := ep00000010101101_0
private theorem idp00000010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001010110.list =
    C ((2:ℤ)^133) * horner X vp00000010101101.list + horner X ep00000010101101.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010101101 : Branch 1 (-85761639/1000000 : ℚ) vp0000001010110 := by
  apply branch_checked idp00000010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-85761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-86261639/500000 : ℚ) by norm_num]
  exact coverp00000010101101
theorem coverp0000001010110 : Covers (-85761639/1000000 : ℚ) vp0000001010110 := join_branches bp00000010101100 bp00000010101101
private noncomputable def vp000000101011_0 : Blocks := edgeBlocks% "full/vectors/000000101011-V-0000.bin"
private noncomputable def vp000000101011_1 : Blocks := edgeBlocks% "full/vectors/000000101011-V-0001.bin"
noncomputable def vp000000101011 : Blocks := (Blocks.join vp000000101011_0 vp000000101011_1)
private theorem bp0000001010110 : Branch 0 (-85761639/2000000 : ℚ) vp000000101011 := by
  apply branch_left_normalized (c:=vp0000001010110) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-85761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-85761639/1000000 : ℚ) by norm_num]
  exact coverp0000001010110
private noncomputable def ep0000001010111_0 : Blocks := edgeBlocks% "full/vectors/0000001010111-E-0000.bin"
private noncomputable def ep0000001010111_1 : Blocks := edgeBlocks% "full/vectors/0000001010111-E-0001.bin"
noncomputable def ep0000001010111 : Blocks := (Blocks.join ep0000001010111_0 ep0000001010111_1)
private theorem idp0000001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101011.list =
    C ((2:ℤ)^244) * horner X vp0000001010111.list + horner X ep0000001010111.list := by
  exact edge_identity (B := (2:ℤ)^445) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010111 : Branch 1 (-85761639/2000000 : ℚ) vp000000101011 := by
  apply branch_checked idp0000001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-85761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-86761639/1000000 : ℚ) by norm_num]
  exact coverp0000001010111
theorem coverp000000101011 : Covers (-85761639/2000000 : ℚ) vp000000101011 := join_branches bp0000001010110 bp0000001010111
private noncomputable def vp000000101010111_0 : Blocks := edgeBlocks% "full/vectors/000000101010111-V-0000.bin"
noncomputable def vp000000101010111 : Blocks := vp000000101010111_0
theorem coverp000000101010111 : Covers (-85511639/250000 : ℚ) vp000000101010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010101101_0 : Blocks := edgeBlocks% "full/vectors/0000001010101101-V-0000.bin"
noncomputable def vp0000001010101101 : Blocks := vp0000001010101101_0
theorem coverp0000001010101101 : Covers (-85386639/125000 : ℚ) vp0000001010101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010101100_0 : Blocks := edgeBlocks% "full/vectors/0000001010101100-V-0000.bin"
noncomputable def vp0000001010101100 : Blocks := vp0000001010101100_0
theorem coverp0000001010101100 : Covers (-85261639/125000 : ℚ) vp0000001010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101010110_0 : Blocks := edgeBlocks% "full/vectors/000000101010110-V-0000.bin"
noncomputable def vp000000101010110 : Blocks := vp000000101010110_0
private theorem bp0000001010101100 : Branch 0 (-85261639/250000 : ℚ) vp000000101010110 := by
  apply branch_left_normalized (c:=vp0000001010101100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-85261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-85261639/125000 : ℚ) by norm_num]
  exact coverp0000001010101100
private noncomputable def ep0000001010101101_0 : Blocks := edgeBlocks% "full/vectors/0000001010101101-E-0000.bin"
noncomputable def ep0000001010101101 : Blocks := ep0000001010101101_0
private theorem idp0000001010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101010110.list =
    C ((2:ℤ)^46) * horner X vp0000001010101101.list + horner X ep0000001010101101.list := by
  exact edge_identity (B := (2:ℤ)^161) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010101101 : Branch 1 (-85261639/250000 : ℚ) vp000000101010110 := by
  apply branch_checked idp0000001010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-85261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-85386639/125000 : ℚ) by norm_num]
  exact coverp0000001010101101
theorem coverp000000101010110 : Covers (-85261639/250000 : ℚ) vp000000101010110 := join_branches bp0000001010101100 bp0000001010101101
private noncomputable def vp00000010101011_0 : Blocks := edgeBlocks% "full/vectors/00000010101011-V-0000.bin"
noncomputable def vp00000010101011 : Blocks := vp00000010101011_0
private theorem bp000000101010110 : Branch 0 (-85261639/500000 : ℚ) vp00000010101011 := by
  apply branch_left_normalized (c:=vp000000101010110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-85261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-85261639/250000 : ℚ) by norm_num]
  exact coverp000000101010110
private noncomputable def ep000000101010111_0 : Blocks := edgeBlocks% "full/vectors/000000101010111-E-0000.bin"
noncomputable def ep000000101010111 : Blocks := ep000000101010111_0
private theorem idp000000101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010101011.list =
    C ((2:ℤ)^74) * horner X vp000000101010111.list + horner X ep000000101010111.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101010111 : Branch 1 (-85261639/500000 : ℚ) vp00000010101011 := by
  apply branch_checked idp000000101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-85261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-85511639/250000 : ℚ) by norm_num]
  exact coverp000000101010111
theorem coverp00000010101011 : Covers (-85261639/500000 : ℚ) vp00000010101011 := join_branches bp000000101010110 bp000000101010111
private noncomputable def vp0000001010101011_0 : Blocks := edgeBlocks% "full/vectors/0000001010101011-V-0000.bin"
noncomputable def vp0000001010101011 : Blocks := vp0000001010101011_0
theorem coverp0000001010101011 : Covers (-85136639/125000 : ℚ) vp0000001010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010101010_0 : Blocks := edgeBlocks% "full/vectors/0000001010101010-V-0000.bin"
noncomputable def vp0000001010101010 : Blocks := vp0000001010101010_0
theorem coverp0000001010101010 : Covers (-85011639/125000 : ℚ) vp0000001010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101010101_0 : Blocks := edgeBlocks% "full/vectors/000000101010101-V-0000.bin"
noncomputable def vp000000101010101 : Blocks := vp000000101010101_0
private theorem bp0000001010101010 : Branch 0 (-85011639/250000 : ℚ) vp000000101010101 := by
  apply branch_left_normalized (c:=vp0000001010101010) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-85011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-85011639/125000 : ℚ) by norm_num]
  exact coverp0000001010101010
private noncomputable def ep0000001010101011_0 : Blocks := edgeBlocks% "full/vectors/0000001010101011-E-0000.bin"
noncomputable def ep0000001010101011 : Blocks := ep0000001010101011_0
private theorem idp0000001010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101010101.list =
    C ((2:ℤ)^45) * horner X vp0000001010101011.list + horner X ep0000001010101011.list := by
  exact edge_identity (B := (2:ℤ)^159) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010101011 : Branch 1 (-85011639/250000 : ℚ) vp000000101010101 := by
  apply branch_checked idp0000001010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-85011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-85136639/125000 : ℚ) by norm_num]
  exact coverp0000001010101011
theorem coverp000000101010101 : Covers (-85011639/250000 : ℚ) vp000000101010101 := join_branches bp0000001010101010 bp0000001010101011
private noncomputable def vp000000101010100_0 : Blocks := edgeBlocks% "full/vectors/000000101010100-V-0000.bin"
noncomputable def vp000000101010100 : Blocks := vp000000101010100_0
theorem coverp000000101010100 : Covers (-84761639/250000 : ℚ) vp000000101010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010101010_0 : Blocks := edgeBlocks% "full/vectors/00000010101010-V-0000.bin"
noncomputable def vp00000010101010 : Blocks := vp00000010101010_0
private theorem bp000000101010100 : Branch 0 (-84761639/500000 : ℚ) vp00000010101010 := by
  apply branch_left_normalized (c:=vp000000101010100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-84761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-84761639/250000 : ℚ) by norm_num]
  exact coverp000000101010100
private noncomputable def ep000000101010101_0 : Blocks := edgeBlocks% "full/vectors/000000101010101-E-0000.bin"
noncomputable def ep000000101010101 : Blocks := ep000000101010101_0
private theorem idp000000101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010101010.list =
    C ((2:ℤ)^74) * horner X vp000000101010101.list + horner X ep000000101010101.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101010101 : Branch 1 (-84761639/500000 : ℚ) vp00000010101010 := by
  apply branch_checked idp000000101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-84761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-85011639/250000 : ℚ) by norm_num]
  exact coverp000000101010101
theorem coverp00000010101010 : Covers (-84761639/500000 : ℚ) vp00000010101010 := join_branches bp000000101010100 bp000000101010101
private noncomputable def vp0000001010101_0 : Blocks := edgeBlocks% "full/vectors/0000001010101-V-0000.bin"
noncomputable def vp0000001010101 : Blocks := vp0000001010101_0
private theorem bp00000010101010 : Branch 0 (-84761639/1000000 : ℚ) vp0000001010101 := by
  apply branch_left_normalized (c:=vp00000010101010) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-84761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-84761639/500000 : ℚ) by norm_num]
  exact coverp00000010101010
private noncomputable def ep00000010101011_0 : Blocks := edgeBlocks% "full/vectors/00000010101011-E-0000.bin"
noncomputable def ep00000010101011 : Blocks := ep00000010101011_0
private theorem idp00000010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001010101.list =
    C ((2:ℤ)^128) * horner X vp00000010101011.list + horner X ep00000010101011.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010101011 : Branch 1 (-84761639/1000000 : ℚ) vp0000001010101 := by
  apply branch_checked idp00000010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-84761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-85261639/500000 : ℚ) by norm_num]
  exact coverp00000010101011
theorem coverp0000001010101 : Covers (-84761639/1000000 : ℚ) vp0000001010101 := join_branches bp00000010101010 bp00000010101011
private noncomputable def vp000000101010011_0 : Blocks := edgeBlocks% "full/vectors/000000101010011-V-0000.bin"
noncomputable def vp000000101010011 : Blocks := vp000000101010011_0
theorem coverp000000101010011 : Covers (-84511639/250000 : ℚ) vp000000101010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101010010_0 : Blocks := edgeBlocks% "full/vectors/000000101010010-V-0000.bin"
noncomputable def vp000000101010010 : Blocks := vp000000101010010_0
theorem coverp000000101010010 : Covers (-84261639/250000 : ℚ) vp000000101010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010101001_0 : Blocks := edgeBlocks% "full/vectors/00000010101001-V-0000.bin"
noncomputable def vp00000010101001 : Blocks := vp00000010101001_0
private theorem bp000000101010010 : Branch 0 (-84261639/500000 : ℚ) vp00000010101001 := by
  apply branch_left_normalized (c:=vp000000101010010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-84261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-84261639/250000 : ℚ) by norm_num]
  exact coverp000000101010010
private noncomputable def ep000000101010011_0 : Blocks := edgeBlocks% "full/vectors/000000101010011-E-0000.bin"
noncomputable def ep000000101010011 : Blocks := ep000000101010011_0
private theorem idp000000101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010101001.list =
    C ((2:ℤ)^74) * horner X vp000000101010011.list + horner X ep000000101010011.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101010011 : Branch 1 (-84261639/500000 : ℚ) vp00000010101001 := by
  apply branch_checked idp000000101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-84261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-84511639/250000 : ℚ) by norm_num]
  exact coverp000000101010011
theorem coverp00000010101001 : Covers (-84261639/500000 : ℚ) vp00000010101001 := join_branches bp000000101010010 bp000000101010011
private noncomputable def vp000000101010001_0 : Blocks := edgeBlocks% "full/vectors/000000101010001-V-0000.bin"
noncomputable def vp000000101010001 : Blocks := vp000000101010001_0
theorem coverp000000101010001 : Covers (-84011639/250000 : ℚ) vp000000101010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101010000_0 : Blocks := edgeBlocks% "full/vectors/000000101010000-V-0000.bin"
noncomputable def vp000000101010000 : Blocks := vp000000101010000_0
theorem coverp000000101010000 : Covers (-83761639/250000 : ℚ) vp000000101010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010101000_0 : Blocks := edgeBlocks% "full/vectors/00000010101000-V-0000.bin"
noncomputable def vp00000010101000 : Blocks := vp00000010101000_0
private theorem bp000000101010000 : Branch 0 (-83761639/500000 : ℚ) vp00000010101000 := by
  apply branch_left_normalized (c:=vp000000101010000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-83761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-83761639/250000 : ℚ) by norm_num]
  exact coverp000000101010000
private noncomputable def ep000000101010001_0 : Blocks := edgeBlocks% "full/vectors/000000101010001-E-0000.bin"
noncomputable def ep000000101010001 : Blocks := ep000000101010001_0
private theorem idp000000101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010101000.list =
    C ((2:ℤ)^76) * horner X vp000000101010001.list + horner X ep000000101010001.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101010001 : Branch 1 (-83761639/500000 : ℚ) vp00000010101000 := by
  apply branch_checked idp000000101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-83761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-84011639/250000 : ℚ) by norm_num]
  exact coverp000000101010001
theorem coverp00000010101000 : Covers (-83761639/500000 : ℚ) vp00000010101000 := join_branches bp000000101010000 bp000000101010001
private noncomputable def vp0000001010100_0 : Blocks := edgeBlocks% "full/vectors/0000001010100-V-0000.bin"
noncomputable def vp0000001010100 : Blocks := vp0000001010100_0
private theorem bp00000010101000 : Branch 0 (-83761639/1000000 : ℚ) vp0000001010100 := by
  apply branch_left_normalized (c:=vp00000010101000) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-83761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-83761639/500000 : ℚ) by norm_num]
  exact coverp00000010101000
private noncomputable def ep00000010101001_0 : Blocks := edgeBlocks% "full/vectors/00000010101001-E-0000.bin"
noncomputable def ep00000010101001 : Blocks := ep00000010101001_0
private theorem idp00000010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001010100.list =
    C ((2:ℤ)^132) * horner X vp00000010101001.list + horner X ep00000010101001.list := by
  exact edge_identity (B := (2:ℤ)^284) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010101001 : Branch 1 (-83761639/1000000 : ℚ) vp0000001010100 := by
  apply branch_checked idp00000010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-83761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-84261639/500000 : ℚ) by norm_num]
  exact coverp00000010101001
theorem coverp0000001010100 : Covers (-83761639/1000000 : ℚ) vp0000001010100 := join_branches bp00000010101000 bp00000010101001
private noncomputable def vp000000101010_0 : Blocks := edgeBlocks% "full/vectors/000000101010-V-0000.bin"
private noncomputable def vp000000101010_1 : Blocks := edgeBlocks% "full/vectors/000000101010-V-0001.bin"
noncomputable def vp000000101010 : Blocks := (Blocks.join vp000000101010_0 vp000000101010_1)
private theorem bp0000001010100 : Branch 0 (-83761639/2000000 : ℚ) vp000000101010 := by
  apply branch_left_normalized (c:=vp0000001010100) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-83761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-83761639/1000000 : ℚ) by norm_num]
  exact coverp0000001010100
private noncomputable def ep0000001010101_0 : Blocks := edgeBlocks% "full/vectors/0000001010101-E-0000.bin"
private noncomputable def ep0000001010101_1 : Blocks := edgeBlocks% "full/vectors/0000001010101-E-0001.bin"
noncomputable def ep0000001010101 : Blocks := (Blocks.join ep0000001010101_0 ep0000001010101_1)
private theorem idp0000001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101010.list =
    C ((2:ℤ)^242) * horner X vp0000001010101.list + horner X ep0000001010101.list := by
  exact edge_identity (B := (2:ℤ)^449) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010101 : Branch 1 (-83761639/2000000 : ℚ) vp000000101010 := by
  apply branch_checked idp0000001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-83761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-84761639/1000000 : ℚ) by norm_num]
  exact coverp0000001010101
theorem coverp000000101010 : Covers (-83761639/2000000 : ℚ) vp000000101010 := join_branches bp0000001010100 bp0000001010101
private noncomputable def vp00000010101_0 : Blocks := edgeBlocks% "full/vectors/00000010101-V-0000.bin"
private noncomputable def vp00000010101_1 : Blocks := edgeBlocks% "full/vectors/00000010101-V-0001.bin"
private noncomputable def vp00000010101_2 : Blocks := edgeBlocks% "full/vectors/00000010101-V-0002.bin"
private noncomputable def vp00000010101_3 : Blocks := edgeBlocks% "full/vectors/00000010101-V-0003.bin"
noncomputable def vp00000010101 : Blocks := (Blocks.join (Blocks.join vp00000010101_0 vp00000010101_1) (Blocks.join vp00000010101_2 vp00000010101_3))
private theorem bp000000101010 : Branch 0 (-83761639/4000000 : ℚ) vp00000010101 := by
  apply branch_left_normalized (c:=vp000000101010) (k:=0) (m:=235) (by decide +kernel)
  rw [show 2*(-83761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-83761639/2000000 : ℚ) by norm_num]
  exact coverp000000101010
private noncomputable def ep000000101011_0 : Blocks := edgeBlocks% "full/vectors/000000101011-E-0000.bin"
private noncomputable def ep000000101011_1 : Blocks := edgeBlocks% "full/vectors/000000101011-E-0001.bin"
private noncomputable def ep000000101011_2 : Blocks := edgeBlocks% "full/vectors/000000101011-E-0002.bin"
private noncomputable def ep000000101011_3 : Blocks := edgeBlocks% "full/vectors/000000101011-E-0003.bin"
noncomputable def ep000000101011 : Blocks := (Blocks.join (Blocks.join ep000000101011_0 ep000000101011_1) (Blocks.join ep000000101011_2 ep000000101011_3))
private theorem idp000000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010101.list =
    C ((2:ℤ)^460) * horner X vp000000101011.list + horner X ep000000101011.list := by
  exact edge_identity (B := (2:ℤ)^775) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101011 : Branch 1 (-83761639/4000000 : ℚ) vp00000010101 := by
  apply branch_checked idp000000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-83761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-85761639/2000000 : ℚ) by norm_num]
  exact coverp000000101011
theorem coverp00000010101 : Covers (-83761639/4000000 : ℚ) vp00000010101 := join_branches bp000000101010 bp000000101011
private noncomputable def vp000000101001111_0 : Blocks := edgeBlocks% "full/vectors/000000101001111-V-0000.bin"
noncomputable def vp000000101001111 : Blocks := vp000000101001111_0
theorem coverp000000101001111 : Covers (-83511639/250000 : ℚ) vp000000101001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101001110_0 : Blocks := edgeBlocks% "full/vectors/000000101001110-V-0000.bin"
noncomputable def vp000000101001110 : Blocks := vp000000101001110_0
theorem coverp000000101001110 : Covers (-83261639/250000 : ℚ) vp000000101001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010100111_0 : Blocks := edgeBlocks% "full/vectors/00000010100111-V-0000.bin"
noncomputable def vp00000010100111 : Blocks := vp00000010100111_0
private theorem bp000000101001110 : Branch 0 (-83261639/500000 : ℚ) vp00000010100111 := by
  apply branch_left_normalized (c:=vp000000101001110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-83261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-83261639/250000 : ℚ) by norm_num]
  exact coverp000000101001110
private noncomputable def ep000000101001111_0 : Blocks := edgeBlocks% "full/vectors/000000101001111-E-0000.bin"
noncomputable def ep000000101001111 : Blocks := ep000000101001111_0
private theorem idp000000101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010100111.list =
    C ((2:ℤ)^77) * horner X vp000000101001111.list + horner X ep000000101001111.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101001111 : Branch 1 (-83261639/500000 : ℚ) vp00000010100111 := by
  apply branch_checked idp000000101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-83261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-83511639/250000 : ℚ) by norm_num]
  exact coverp000000101001111
theorem coverp00000010100111 : Covers (-83261639/500000 : ℚ) vp00000010100111 := join_branches bp000000101001110 bp000000101001111
private noncomputable def vp0000001010011011_0 : Blocks := edgeBlocks% "full/vectors/0000001010011011-V-0000.bin"
noncomputable def vp0000001010011011 : Blocks := vp0000001010011011_0
theorem coverp0000001010011011 : Covers (-83136639/125000 : ℚ) vp0000001010011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010011010_0 : Blocks := edgeBlocks% "full/vectors/0000001010011010-V-0000.bin"
noncomputable def vp0000001010011010 : Blocks := vp0000001010011010_0
theorem coverp0000001010011010 : Covers (-83011639/125000 : ℚ) vp0000001010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101001101_0 : Blocks := edgeBlocks% "full/vectors/000000101001101-V-0000.bin"
noncomputable def vp000000101001101 : Blocks := vp000000101001101_0
private theorem bp0000001010011010 : Branch 0 (-83011639/250000 : ℚ) vp000000101001101 := by
  apply branch_left_normalized (c:=vp0000001010011010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-83011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-83011639/125000 : ℚ) by norm_num]
  exact coverp0000001010011010
private noncomputable def ep0000001010011011_0 : Blocks := edgeBlocks% "full/vectors/0000001010011011-E-0000.bin"
noncomputable def ep0000001010011011 : Blocks := ep0000001010011011_0
private theorem idp0000001010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101001101.list =
    C ((2:ℤ)^48) * horner X vp0000001010011011.list + horner X ep0000001010011011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010011011 : Branch 1 (-83011639/250000 : ℚ) vp000000101001101 := by
  apply branch_checked idp0000001010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-83011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-83136639/125000 : ℚ) by norm_num]
  exact coverp0000001010011011
theorem coverp000000101001101 : Covers (-83011639/250000 : ℚ) vp000000101001101 := join_branches bp0000001010011010 bp0000001010011011
private noncomputable def vp0000001010011001_0 : Blocks := edgeBlocks% "full/vectors/0000001010011001-V-0000.bin"
noncomputable def vp0000001010011001 : Blocks := vp0000001010011001_0
theorem coverp0000001010011001 : Covers (-82886639/125000 : ℚ) vp0000001010011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010011000_0 : Blocks := edgeBlocks% "full/vectors/0000001010011000-V-0000.bin"
noncomputable def vp0000001010011000 : Blocks := vp0000001010011000_0
theorem coverp0000001010011000 : Covers (-82761639/125000 : ℚ) vp0000001010011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101001100_0 : Blocks := edgeBlocks% "full/vectors/000000101001100-V-0000.bin"
noncomputable def vp000000101001100 : Blocks := vp000000101001100_0
private theorem bp0000001010011000 : Branch 0 (-82761639/250000 : ℚ) vp000000101001100 := by
  apply branch_left_normalized (c:=vp0000001010011000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-82761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-82761639/125000 : ℚ) by norm_num]
  exact coverp0000001010011000
private noncomputable def ep0000001010011001_0 : Blocks := edgeBlocks% "full/vectors/0000001010011001-E-0000.bin"
noncomputable def ep0000001010011001 : Blocks := ep0000001010011001_0
private theorem idp0000001010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101001100.list =
    C ((2:ℤ)^48) * horner X vp0000001010011001.list + horner X ep0000001010011001.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010011001 : Branch 1 (-82761639/250000 : ℚ) vp000000101001100 := by
  apply branch_checked idp0000001010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-82761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-82886639/125000 : ℚ) by norm_num]
  exact coverp0000001010011001
theorem coverp000000101001100 : Covers (-82761639/250000 : ℚ) vp000000101001100 := join_branches bp0000001010011000 bp0000001010011001
private noncomputable def vp00000010100110_0 : Blocks := edgeBlocks% "full/vectors/00000010100110-V-0000.bin"
noncomputable def vp00000010100110 : Blocks := vp00000010100110_0
private theorem bp000000101001100 : Branch 0 (-82761639/500000 : ℚ) vp00000010100110 := by
  apply branch_left_normalized (c:=vp000000101001100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-82761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-82761639/250000 : ℚ) by norm_num]
  exact coverp000000101001100
private noncomputable def ep000000101001101_0 : Blocks := edgeBlocks% "full/vectors/000000101001101-E-0000.bin"
noncomputable def ep000000101001101 : Blocks := ep000000101001101_0
private theorem idp000000101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010100110.list =
    C ((2:ℤ)^78) * horner X vp000000101001101.list + horner X ep000000101001101.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101001101 : Branch 1 (-82761639/500000 : ℚ) vp00000010100110 := by
  apply branch_checked idp000000101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-82761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-83011639/250000 : ℚ) by norm_num]
  exact coverp000000101001101
theorem coverp00000010100110 : Covers (-82761639/500000 : ℚ) vp00000010100110 := join_branches bp000000101001100 bp000000101001101
private noncomputable def vp0000001010011_0 : Blocks := edgeBlocks% "full/vectors/0000001010011-V-0000.bin"
private noncomputable def vp0000001010011_1 : Blocks := edgeBlocks% "full/vectors/0000001010011-V-0001.bin"
noncomputable def vp0000001010011 : Blocks := (Blocks.join vp0000001010011_0 vp0000001010011_1)
private theorem bp00000010100110 : Branch 0 (-82761639/1000000 : ℚ) vp0000001010011 := by
  apply branch_left_normalized (c:=vp00000010100110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-82761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-82761639/500000 : ℚ) by norm_num]
  exact coverp00000010100110
private noncomputable def ep00000010100111_0 : Blocks := edgeBlocks% "full/vectors/00000010100111-E-0000.bin"
private noncomputable def ep00000010100111_1 : Blocks := edgeBlocks% "full/vectors/00000010100111-E-0001.bin"
noncomputable def ep00000010100111 : Blocks := (Blocks.join ep00000010100111_0 ep00000010100111_1)
private theorem idp00000010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001010011.list =
    C ((2:ℤ)^136) * horner X vp00000010100111.list + horner X ep00000010100111.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010100111 : Branch 1 (-82761639/1000000 : ℚ) vp0000001010011 := by
  apply branch_checked idp00000010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-82761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-83261639/500000 : ℚ) by norm_num]
  exact coverp00000010100111
theorem coverp0000001010011 : Covers (-82761639/1000000 : ℚ) vp0000001010011 := join_branches bp00000010100110 bp00000010100111
private noncomputable def vp0000001010010111_0 : Blocks := edgeBlocks% "full/vectors/0000001010010111-V-0000.bin"
noncomputable def vp0000001010010111 : Blocks := vp0000001010010111_0
theorem coverp0000001010010111 : Covers (-82636639/125000 : ℚ) vp0000001010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010010110_0 : Blocks := edgeBlocks% "full/vectors/0000001010010110-V-0000.bin"
noncomputable def vp0000001010010110 : Blocks := vp0000001010010110_0
theorem coverp0000001010010110 : Covers (-82511639/125000 : ℚ) vp0000001010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101001011_0 : Blocks := edgeBlocks% "full/vectors/000000101001011-V-0000.bin"
noncomputable def vp000000101001011 : Blocks := vp000000101001011_0
private theorem bp0000001010010110 : Branch 0 (-82511639/250000 : ℚ) vp000000101001011 := by
  apply branch_left_normalized (c:=vp0000001010010110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-82511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-82511639/125000 : ℚ) by norm_num]
  exact coverp0000001010010110
private noncomputable def ep0000001010010111_0 : Blocks := edgeBlocks% "full/vectors/0000001010010111-E-0000.bin"
noncomputable def ep0000001010010111 : Blocks := ep0000001010010111_0
private theorem idp0000001010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101001011.list =
    C ((2:ℤ)^47) * horner X vp0000001010010111.list + horner X ep0000001010010111.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010010111 : Branch 1 (-82511639/250000 : ℚ) vp000000101001011 := by
  apply branch_checked idp0000001010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-82511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-82636639/125000 : ℚ) by norm_num]
  exact coverp0000001010010111
theorem coverp000000101001011 : Covers (-82511639/250000 : ℚ) vp000000101001011 := join_branches bp0000001010010110 bp0000001010010111
private noncomputable def vp0000001010010101_0 : Blocks := edgeBlocks% "full/vectors/0000001010010101-V-0000.bin"
noncomputable def vp0000001010010101 : Blocks := vp0000001010010101_0
theorem coverp0000001010010101 : Covers (-82386639/125000 : ℚ) vp0000001010010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010010100_0 : Blocks := edgeBlocks% "full/vectors/0000001010010100-V-0000.bin"
noncomputable def vp0000001010010100 : Blocks := vp0000001010010100_0
theorem coverp0000001010010100 : Covers (-82261639/125000 : ℚ) vp0000001010010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101001010_0 : Blocks := edgeBlocks% "full/vectors/000000101001010-V-0000.bin"
noncomputable def vp000000101001010 : Blocks := vp000000101001010_0
private theorem bp0000001010010100 : Branch 0 (-82261639/250000 : ℚ) vp000000101001010 := by
  apply branch_left_normalized (c:=vp0000001010010100) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-82261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-82261639/125000 : ℚ) by norm_num]
  exact coverp0000001010010100
private noncomputable def ep0000001010010101_0 : Blocks := edgeBlocks% "full/vectors/0000001010010101-E-0000.bin"
noncomputable def ep0000001010010101 : Blocks := ep0000001010010101_0
private theorem idp0000001010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101001010.list =
    C ((2:ℤ)^48) * horner X vp0000001010010101.list + horner X ep0000001010010101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010010101 : Branch 1 (-82261639/250000 : ℚ) vp000000101001010 := by
  apply branch_checked idp0000001010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-82261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-82386639/125000 : ℚ) by norm_num]
  exact coverp0000001010010101
theorem coverp000000101001010 : Covers (-82261639/250000 : ℚ) vp000000101001010 := join_branches bp0000001010010100 bp0000001010010101
private noncomputable def vp00000010100101_0 : Blocks := edgeBlocks% "full/vectors/00000010100101-V-0000.bin"
noncomputable def vp00000010100101 : Blocks := vp00000010100101_0
private theorem bp000000101001010 : Branch 0 (-82261639/500000 : ℚ) vp00000010100101 := by
  apply branch_left_normalized (c:=vp000000101001010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-82261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-82261639/250000 : ℚ) by norm_num]
  exact coverp000000101001010
private noncomputable def ep000000101001011_0 : Blocks := edgeBlocks% "full/vectors/000000101001011-E-0000.bin"
noncomputable def ep000000101001011 : Blocks := ep000000101001011_0
private theorem idp000000101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010100101.list =
    C ((2:ℤ)^76) * horner X vp000000101001011.list + horner X ep000000101001011.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101001011 : Branch 1 (-82261639/500000 : ℚ) vp00000010100101 := by
  apply branch_checked idp000000101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-82261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-82511639/250000 : ℚ) by norm_num]
  exact coverp000000101001011
theorem coverp00000010100101 : Covers (-82261639/500000 : ℚ) vp00000010100101 := join_branches bp000000101001010 bp000000101001011
private noncomputable def vp0000001010010011_0 : Blocks := edgeBlocks% "full/vectors/0000001010010011-V-0000.bin"
noncomputable def vp0000001010010011 : Blocks := vp0000001010010011_0
theorem coverp0000001010010011 : Covers (-82136639/125000 : ℚ) vp0000001010010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010010010_0 : Blocks := edgeBlocks% "full/vectors/0000001010010010-V-0000.bin"
noncomputable def vp0000001010010010 : Blocks := vp0000001010010010_0
theorem coverp0000001010010010 : Covers (-82011639/125000 : ℚ) vp0000001010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101001001_0 : Blocks := edgeBlocks% "full/vectors/000000101001001-V-0000.bin"
noncomputable def vp000000101001001 : Blocks := vp000000101001001_0
private theorem bp0000001010010010 : Branch 0 (-82011639/250000 : ℚ) vp000000101001001 := by
  apply branch_left_normalized (c:=vp0000001010010010) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-82011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-82011639/125000 : ℚ) by norm_num]
  exact coverp0000001010010010
private noncomputable def ep0000001010010011_0 : Blocks := edgeBlocks% "full/vectors/0000001010010011-E-0000.bin"
noncomputable def ep0000001010010011 : Blocks := ep0000001010010011_0
private theorem idp0000001010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101001001.list =
    C ((2:ℤ)^48) * horner X vp0000001010010011.list + horner X ep0000001010010011.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010010011 : Branch 1 (-82011639/250000 : ℚ) vp000000101001001 := by
  apply branch_checked idp0000001010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-82011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-82136639/125000 : ℚ) by norm_num]
  exact coverp0000001010010011
theorem coverp000000101001001 : Covers (-82011639/250000 : ℚ) vp000000101001001 := join_branches bp0000001010010010 bp0000001010010011
private noncomputable def vp0000001010010001_0 : Blocks := edgeBlocks% "full/vectors/0000001010010001-V-0000.bin"
noncomputable def vp0000001010010001 : Blocks := vp0000001010010001_0
theorem coverp0000001010010001 : Covers (-81886639/125000 : ℚ) vp0000001010010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010010000_0 : Blocks := edgeBlocks% "full/vectors/0000001010010000-V-0000.bin"
noncomputable def vp0000001010010000 : Blocks := vp0000001010010000_0
theorem coverp0000001010010000 : Covers (-81761639/125000 : ℚ) vp0000001010010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101001000_0 : Blocks := edgeBlocks% "full/vectors/000000101001000-V-0000.bin"
noncomputable def vp000000101001000 : Blocks := vp000000101001000_0
private theorem bp0000001010010000 : Branch 0 (-81761639/250000 : ℚ) vp000000101001000 := by
  apply branch_left_normalized (c:=vp0000001010010000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-81761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-81761639/125000 : ℚ) by norm_num]
  exact coverp0000001010010000
private noncomputable def ep0000001010010001_0 : Blocks := edgeBlocks% "full/vectors/0000001010010001-E-0000.bin"
noncomputable def ep0000001010010001 : Blocks := ep0000001010010001_0
private theorem idp0000001010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101001000.list =
    C ((2:ℤ)^47) * horner X vp0000001010010001.list + horner X ep0000001010010001.list := by
  exact edge_identity (B := (2:ℤ)^161) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010010001 : Branch 1 (-81761639/250000 : ℚ) vp000000101001000 := by
  apply branch_checked idp0000001010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-81761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-81886639/125000 : ℚ) by norm_num]
  exact coverp0000001010010001
theorem coverp000000101001000 : Covers (-81761639/250000 : ℚ) vp000000101001000 := join_branches bp0000001010010000 bp0000001010010001
private noncomputable def vp00000010100100_0 : Blocks := edgeBlocks% "full/vectors/00000010100100-V-0000.bin"
noncomputable def vp00000010100100 : Blocks := vp00000010100100_0
private theorem bp000000101001000 : Branch 0 (-81761639/500000 : ℚ) vp00000010100100 := by
  apply branch_left_normalized (c:=vp000000101001000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-81761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-81761639/250000 : ℚ) by norm_num]
  exact coverp000000101001000
private noncomputable def ep000000101001001_0 : Blocks := edgeBlocks% "full/vectors/000000101001001-E-0000.bin"
noncomputable def ep000000101001001 : Blocks := ep000000101001001_0
private theorem idp000000101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010100100.list =
    C ((2:ℤ)^76) * horner X vp000000101001001.list + horner X ep000000101001001.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101001001 : Branch 1 (-81761639/500000 : ℚ) vp00000010100100 := by
  apply branch_checked idp000000101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-81761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-82011639/250000 : ℚ) by norm_num]
  exact coverp000000101001001
theorem coverp00000010100100 : Covers (-81761639/500000 : ℚ) vp00000010100100 := join_branches bp000000101001000 bp000000101001001
private noncomputable def vp0000001010010_0 : Blocks := edgeBlocks% "full/vectors/0000001010010-V-0000.bin"
private noncomputable def vp0000001010010_1 : Blocks := edgeBlocks% "full/vectors/0000001010010-V-0001.bin"
noncomputable def vp0000001010010 : Blocks := (Blocks.join vp0000001010010_0 vp0000001010010_1)
private theorem bp00000010100100 : Branch 0 (-81761639/1000000 : ℚ) vp0000001010010 := by
  apply branch_left_normalized (c:=vp00000010100100) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-81761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-81761639/500000 : ℚ) by norm_num]
  exact coverp00000010100100
private noncomputable def ep00000010100101_0 : Blocks := edgeBlocks% "full/vectors/00000010100101-E-0000.bin"
private noncomputable def ep00000010100101_1 : Blocks := edgeBlocks% "full/vectors/00000010100101-E-0001.bin"
noncomputable def ep00000010100101 : Blocks := (Blocks.join ep00000010100101_0 ep00000010100101_1)
private theorem idp00000010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001010010.list =
    C ((2:ℤ)^132) * horner X vp00000010100101.list + horner X ep00000010100101.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010100101 : Branch 1 (-81761639/1000000 : ℚ) vp0000001010010 := by
  apply branch_checked idp00000010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-81761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-82261639/500000 : ℚ) by norm_num]
  exact coverp00000010100101
theorem coverp0000001010010 : Covers (-81761639/1000000 : ℚ) vp0000001010010 := join_branches bp00000010100100 bp00000010100101
private noncomputable def vp000000101001_0 : Blocks := edgeBlocks% "full/vectors/000000101001-V-0000.bin"
private noncomputable def vp000000101001_1 : Blocks := edgeBlocks% "full/vectors/000000101001-V-0001.bin"
noncomputable def vp000000101001 : Blocks := (Blocks.join vp000000101001_0 vp000000101001_1)
private theorem bp0000001010010 : Branch 0 (-81761639/2000000 : ℚ) vp000000101001 := by
  apply branch_left_normalized (c:=vp0000001010010) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-81761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-81761639/1000000 : ℚ) by norm_num]
  exact coverp0000001010010
private noncomputable def ep0000001010011_0 : Blocks := edgeBlocks% "full/vectors/0000001010011-E-0000.bin"
private noncomputable def ep0000001010011_1 : Blocks := edgeBlocks% "full/vectors/0000001010011-E-0001.bin"
noncomputable def ep0000001010011 : Blocks := (Blocks.join ep0000001010011_0 ep0000001010011_1)
private theorem idp0000001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101001.list =
    C ((2:ℤ)^242) * horner X vp0000001010011.list + horner X ep0000001010011.list := by
  exact edge_identity (B := (2:ℤ)^455) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010011 : Branch 1 (-81761639/2000000 : ℚ) vp000000101001 := by
  apply branch_checked idp0000001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-81761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-82761639/1000000 : ℚ) by norm_num]
  exact coverp0000001010011
theorem coverp000000101001 : Covers (-81761639/2000000 : ℚ) vp000000101001 := join_branches bp0000001010010 bp0000001010011
private noncomputable def vp0000001010001111_0 : Blocks := edgeBlocks% "full/vectors/0000001010001111-V-0000.bin"
noncomputable def vp0000001010001111 : Blocks := vp0000001010001111_0
theorem coverp0000001010001111 : Covers (-81636639/125000 : ℚ) vp0000001010001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010001110_0 : Blocks := edgeBlocks% "full/vectors/0000001010001110-V-0000.bin"
noncomputable def vp0000001010001110 : Blocks := vp0000001010001110_0
theorem coverp0000001010001110 : Covers (-81511639/125000 : ℚ) vp0000001010001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101000111_0 : Blocks := edgeBlocks% "full/vectors/000000101000111-V-0000.bin"
noncomputable def vp000000101000111 : Blocks := vp000000101000111_0
private theorem bp0000001010001110 : Branch 0 (-81511639/250000 : ℚ) vp000000101000111 := by
  apply branch_left_normalized (c:=vp0000001010001110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-81511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-81511639/125000 : ℚ) by norm_num]
  exact coverp0000001010001110
private noncomputable def ep0000001010001111_0 : Blocks := edgeBlocks% "full/vectors/0000001010001111-E-0000.bin"
noncomputable def ep0000001010001111 : Blocks := ep0000001010001111_0
private theorem idp0000001010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101000111.list =
    C ((2:ℤ)^47) * horner X vp0000001010001111.list + horner X ep0000001010001111.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010001111 : Branch 1 (-81511639/250000 : ℚ) vp000000101000111 := by
  apply branch_checked idp0000001010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-81511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-81636639/125000 : ℚ) by norm_num]
  exact coverp0000001010001111
theorem coverp000000101000111 : Covers (-81511639/250000 : ℚ) vp000000101000111 := join_branches bp0000001010001110 bp0000001010001111
private noncomputable def vp0000001010001101_0 : Blocks := edgeBlocks% "full/vectors/0000001010001101-V-0000.bin"
noncomputable def vp0000001010001101 : Blocks := vp0000001010001101_0
theorem coverp0000001010001101 : Covers (-81386639/125000 : ℚ) vp0000001010001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010001100_0 : Blocks := edgeBlocks% "full/vectors/0000001010001100-V-0000.bin"
noncomputable def vp0000001010001100 : Blocks := vp0000001010001100_0
theorem coverp0000001010001100 : Covers (-81261639/125000 : ℚ) vp0000001010001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101000110_0 : Blocks := edgeBlocks% "full/vectors/000000101000110-V-0000.bin"
noncomputable def vp000000101000110 : Blocks := vp000000101000110_0
private theorem bp0000001010001100 : Branch 0 (-81261639/250000 : ℚ) vp000000101000110 := by
  apply branch_left_normalized (c:=vp0000001010001100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-81261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-81261639/125000 : ℚ) by norm_num]
  exact coverp0000001010001100
private noncomputable def ep0000001010001101_0 : Blocks := edgeBlocks% "full/vectors/0000001010001101-E-0000.bin"
noncomputable def ep0000001010001101 : Blocks := ep0000001010001101_0
private theorem idp0000001010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101000110.list =
    C ((2:ℤ)^47) * horner X vp0000001010001101.list + horner X ep0000001010001101.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010001101 : Branch 1 (-81261639/250000 : ℚ) vp000000101000110 := by
  apply branch_checked idp0000001010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-81261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-81386639/125000 : ℚ) by norm_num]
  exact coverp0000001010001101
theorem coverp000000101000110 : Covers (-81261639/250000 : ℚ) vp000000101000110 := join_branches bp0000001010001100 bp0000001010001101
private noncomputable def vp00000010100011_0 : Blocks := edgeBlocks% "full/vectors/00000010100011-V-0000.bin"
noncomputable def vp00000010100011 : Blocks := vp00000010100011_0
private theorem bp000000101000110 : Branch 0 (-81261639/500000 : ℚ) vp00000010100011 := by
  apply branch_left_normalized (c:=vp000000101000110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-81261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-81261639/250000 : ℚ) by norm_num]
  exact coverp000000101000110
private noncomputable def ep000000101000111_0 : Blocks := edgeBlocks% "full/vectors/000000101000111-E-0000.bin"
noncomputable def ep000000101000111 : Blocks := ep000000101000111_0
private theorem idp000000101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010100011.list =
    C ((2:ℤ)^78) * horner X vp000000101000111.list + horner X ep000000101000111.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101000111 : Branch 1 (-81261639/500000 : ℚ) vp00000010100011 := by
  apply branch_checked idp000000101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-81261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-81511639/250000 : ℚ) by norm_num]
  exact coverp000000101000111
theorem coverp00000010100011 : Covers (-81261639/500000 : ℚ) vp00000010100011 := join_branches bp000000101000110 bp000000101000111
private noncomputable def vp0000001010001011_0 : Blocks := edgeBlocks% "full/vectors/0000001010001011-V-0000.bin"
noncomputable def vp0000001010001011 : Blocks := vp0000001010001011_0
theorem coverp0000001010001011 : Covers (-81136639/125000 : ℚ) vp0000001010001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010001010_0 : Blocks := edgeBlocks% "full/vectors/0000001010001010-V-0000.bin"
noncomputable def vp0000001010001010 : Blocks := vp0000001010001010_0
theorem coverp0000001010001010 : Covers (-81011639/125000 : ℚ) vp0000001010001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101000101_0 : Blocks := edgeBlocks% "full/vectors/000000101000101-V-0000.bin"
noncomputable def vp000000101000101 : Blocks := vp000000101000101_0
private theorem bp0000001010001010 : Branch 0 (-81011639/250000 : ℚ) vp000000101000101 := by
  apply branch_left_normalized (c:=vp0000001010001010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-81011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-81011639/125000 : ℚ) by norm_num]
  exact coverp0000001010001010
private noncomputable def ep0000001010001011_0 : Blocks := edgeBlocks% "full/vectors/0000001010001011-E-0000.bin"
noncomputable def ep0000001010001011 : Blocks := ep0000001010001011_0
private theorem idp0000001010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101000101.list =
    C ((2:ℤ)^48) * horner X vp0000001010001011.list + horner X ep0000001010001011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010001011 : Branch 1 (-81011639/250000 : ℚ) vp000000101000101 := by
  apply branch_checked idp0000001010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-81011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-81136639/125000 : ℚ) by norm_num]
  exact coverp0000001010001011
theorem coverp000000101000101 : Covers (-81011639/250000 : ℚ) vp000000101000101 := join_branches bp0000001010001010 bp0000001010001011
private noncomputable def vp0000001010001001_0 : Blocks := edgeBlocks% "full/vectors/0000001010001001-V-0000.bin"
noncomputable def vp0000001010001001 : Blocks := vp0000001010001001_0
theorem coverp0000001010001001 : Covers (-80886639/125000 : ℚ) vp0000001010001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010001000_0 : Blocks := edgeBlocks% "full/vectors/0000001010001000-V-0000.bin"
noncomputable def vp0000001010001000 : Blocks := vp0000001010001000_0
theorem coverp0000001010001000 : Covers (-80761639/125000 : ℚ) vp0000001010001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101000100_0 : Blocks := edgeBlocks% "full/vectors/000000101000100-V-0000.bin"
noncomputable def vp000000101000100 : Blocks := vp000000101000100_0
private theorem bp0000001010001000 : Branch 0 (-80761639/250000 : ℚ) vp000000101000100 := by
  apply branch_left_normalized (c:=vp0000001010001000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-80761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-80761639/125000 : ℚ) by norm_num]
  exact coverp0000001010001000
private noncomputable def ep0000001010001001_0 : Blocks := edgeBlocks% "full/vectors/0000001010001001-E-0000.bin"
noncomputable def ep0000001010001001 : Blocks := ep0000001010001001_0
private theorem idp0000001010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101000100.list =
    C ((2:ℤ)^48) * horner X vp0000001010001001.list + horner X ep0000001010001001.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010001001 : Branch 1 (-80761639/250000 : ℚ) vp000000101000100 := by
  apply branch_checked idp0000001010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-80761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-80886639/125000 : ℚ) by norm_num]
  exact coverp0000001010001001
theorem coverp000000101000100 : Covers (-80761639/250000 : ℚ) vp000000101000100 := join_branches bp0000001010001000 bp0000001010001001
private noncomputable def vp00000010100010_0 : Blocks := edgeBlocks% "full/vectors/00000010100010-V-0000.bin"
noncomputable def vp00000010100010 : Blocks := vp00000010100010_0
private theorem bp000000101000100 : Branch 0 (-80761639/500000 : ℚ) vp00000010100010 := by
  apply branch_left_normalized (c:=vp000000101000100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-80761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-80761639/250000 : ℚ) by norm_num]
  exact coverp000000101000100
private noncomputable def ep000000101000101_0 : Blocks := edgeBlocks% "full/vectors/000000101000101-E-0000.bin"
noncomputable def ep000000101000101 : Blocks := ep000000101000101_0
private theorem idp000000101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010100010.list =
    C ((2:ℤ)^80) * horner X vp000000101000101.list + horner X ep000000101000101.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101000101 : Branch 1 (-80761639/500000 : ℚ) vp00000010100010 := by
  apply branch_checked idp000000101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-80761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-81011639/250000 : ℚ) by norm_num]
  exact coverp000000101000101
theorem coverp00000010100010 : Covers (-80761639/500000 : ℚ) vp00000010100010 := join_branches bp000000101000100 bp000000101000101
private noncomputable def vp0000001010001_0 : Blocks := edgeBlocks% "full/vectors/0000001010001-V-0000.bin"
private noncomputable def vp0000001010001_1 : Blocks := edgeBlocks% "full/vectors/0000001010001-V-0001.bin"
noncomputable def vp0000001010001 : Blocks := (Blocks.join vp0000001010001_0 vp0000001010001_1)
private theorem bp00000010100010 : Branch 0 (-80761639/1000000 : ℚ) vp0000001010001 := by
  apply branch_left_normalized (c:=vp00000010100010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-80761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-80761639/500000 : ℚ) by norm_num]
  exact coverp00000010100010
private noncomputable def ep00000010100011_0 : Blocks := edgeBlocks% "full/vectors/00000010100011-E-0000.bin"
private noncomputable def ep00000010100011_1 : Blocks := edgeBlocks% "full/vectors/00000010100011-E-0001.bin"
noncomputable def ep00000010100011 : Blocks := (Blocks.join ep00000010100011_0 ep00000010100011_1)
private theorem idp00000010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001010001.list =
    C ((2:ℤ)^138) * horner X vp00000010100011.list + horner X ep00000010100011.list := by
  exact edge_identity (B := (2:ℤ)^295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010100011 : Branch 1 (-80761639/1000000 : ℚ) vp0000001010001 := by
  apply branch_checked idp00000010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-80761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-81261639/500000 : ℚ) by norm_num]
  exact coverp00000010100011
theorem coverp0000001010001 : Covers (-80761639/1000000 : ℚ) vp0000001010001 := join_branches bp00000010100010 bp00000010100011
private noncomputable def vp0000001010000111_0 : Blocks := edgeBlocks% "full/vectors/0000001010000111-V-0000.bin"
noncomputable def vp0000001010000111 : Blocks := vp0000001010000111_0
theorem coverp0000001010000111 : Covers (-80636639/125000 : ℚ) vp0000001010000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010000110_0 : Blocks := edgeBlocks% "full/vectors/0000001010000110-V-0000.bin"
noncomputable def vp0000001010000110 : Blocks := vp0000001010000110_0
theorem coverp0000001010000110 : Covers (-80511639/125000 : ℚ) vp0000001010000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101000011_0 : Blocks := edgeBlocks% "full/vectors/000000101000011-V-0000.bin"
noncomputable def vp000000101000011 : Blocks := vp000000101000011_0
private theorem bp0000001010000110 : Branch 0 (-80511639/250000 : ℚ) vp000000101000011 := by
  apply branch_left_normalized (c:=vp0000001010000110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-80511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-80511639/125000 : ℚ) by norm_num]
  exact coverp0000001010000110
private noncomputable def ep0000001010000111_0 : Blocks := edgeBlocks% "full/vectors/0000001010000111-E-0000.bin"
noncomputable def ep0000001010000111 : Blocks := ep0000001010000111_0
private theorem idp0000001010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101000011.list =
    C ((2:ℤ)^48) * horner X vp0000001010000111.list + horner X ep0000001010000111.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010000111 : Branch 1 (-80511639/250000 : ℚ) vp000000101000011 := by
  apply branch_checked idp0000001010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-80511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-80636639/125000 : ℚ) by norm_num]
  exact coverp0000001010000111
theorem coverp000000101000011 : Covers (-80511639/250000 : ℚ) vp000000101000011 := join_branches bp0000001010000110 bp0000001010000111
private noncomputable def vp0000001010000101_0 : Blocks := edgeBlocks% "full/vectors/0000001010000101-V-0000.bin"
noncomputable def vp0000001010000101 : Blocks := vp0000001010000101_0
theorem coverp0000001010000101 : Covers (-80386639/125000 : ℚ) vp0000001010000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010000100_0 : Blocks := edgeBlocks% "full/vectors/0000001010000100-V-0000.bin"
noncomputable def vp0000001010000100 : Blocks := vp0000001010000100_0
theorem coverp0000001010000100 : Covers (-80261639/125000 : ℚ) vp0000001010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101000010_0 : Blocks := edgeBlocks% "full/vectors/000000101000010-V-0000.bin"
noncomputable def vp000000101000010 : Blocks := vp000000101000010_0
private theorem bp0000001010000100 : Branch 0 (-80261639/250000 : ℚ) vp000000101000010 := by
  apply branch_left_normalized (c:=vp0000001010000100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-80261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-80261639/125000 : ℚ) by norm_num]
  exact coverp0000001010000100
private noncomputable def ep0000001010000101_0 : Blocks := edgeBlocks% "full/vectors/0000001010000101-E-0000.bin"
noncomputable def ep0000001010000101 : Blocks := ep0000001010000101_0
private theorem idp0000001010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101000010.list =
    C ((2:ℤ)^47) * horner X vp0000001010000101.list + horner X ep0000001010000101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010000101 : Branch 1 (-80261639/250000 : ℚ) vp000000101000010 := by
  apply branch_checked idp0000001010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-80261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-80386639/125000 : ℚ) by norm_num]
  exact coverp0000001010000101
theorem coverp000000101000010 : Covers (-80261639/250000 : ℚ) vp000000101000010 := join_branches bp0000001010000100 bp0000001010000101
private noncomputable def vp00000010100001_0 : Blocks := edgeBlocks% "full/vectors/00000010100001-V-0000.bin"
noncomputable def vp00000010100001 : Blocks := vp00000010100001_0
private theorem bp000000101000010 : Branch 0 (-80261639/500000 : ℚ) vp00000010100001 := by
  apply branch_left_normalized (c:=vp000000101000010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-80261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-80261639/250000 : ℚ) by norm_num]
  exact coverp000000101000010
private noncomputable def ep000000101000011_0 : Blocks := edgeBlocks% "full/vectors/000000101000011-E-0000.bin"
noncomputable def ep000000101000011 : Blocks := ep000000101000011_0
private theorem idp000000101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010100001.list =
    C ((2:ℤ)^77) * horner X vp000000101000011.list + horner X ep000000101000011.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101000011 : Branch 1 (-80261639/500000 : ℚ) vp00000010100001 := by
  apply branch_checked idp000000101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-80261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-80511639/250000 : ℚ) by norm_num]
  exact coverp000000101000011
theorem coverp00000010100001 : Covers (-80261639/500000 : ℚ) vp00000010100001 := join_branches bp000000101000010 bp000000101000011
private noncomputable def vp0000001010000011_0 : Blocks := edgeBlocks% "full/vectors/0000001010000011-V-0000.bin"
noncomputable def vp0000001010000011 : Blocks := vp0000001010000011_0
theorem coverp0000001010000011 : Covers (-80136639/125000 : ℚ) vp0000001010000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010000010_0 : Blocks := edgeBlocks% "full/vectors/0000001010000010-V-0000.bin"
noncomputable def vp0000001010000010 : Blocks := vp0000001010000010_0
theorem coverp0000001010000010 : Covers (-80011639/125000 : ℚ) vp0000001010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101000001_0 : Blocks := edgeBlocks% "full/vectors/000000101000001-V-0000.bin"
noncomputable def vp000000101000001 : Blocks := vp000000101000001_0
private theorem bp0000001010000010 : Branch 0 (-80011639/250000 : ℚ) vp000000101000001 := by
  apply branch_left_normalized (c:=vp0000001010000010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-80011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-80011639/125000 : ℚ) by norm_num]
  exact coverp0000001010000010
private noncomputable def ep0000001010000011_0 : Blocks := edgeBlocks% "full/vectors/0000001010000011-E-0000.bin"
noncomputable def ep0000001010000011 : Blocks := ep0000001010000011_0
private theorem idp0000001010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101000001.list =
    C ((2:ℤ)^47) * horner X vp0000001010000011.list + horner X ep0000001010000011.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010000011 : Branch 1 (-80011639/250000 : ℚ) vp000000101000001 := by
  apply branch_checked idp0000001010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-80011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-80136639/125000 : ℚ) by norm_num]
  exact coverp0000001010000011
theorem coverp000000101000001 : Covers (-80011639/250000 : ℚ) vp000000101000001 := join_branches bp0000001010000010 bp0000001010000011
private noncomputable def vp0000001010000001_0 : Blocks := edgeBlocks% "full/vectors/0000001010000001-V-0000.bin"
noncomputable def vp0000001010000001 : Blocks := vp0000001010000001_0
theorem coverp0000001010000001 : Covers (-79886639/125000 : ℚ) vp0000001010000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001010000000_0 : Blocks := edgeBlocks% "full/vectors/0000001010000000-V-0000.bin"
noncomputable def vp0000001010000000 : Blocks := vp0000001010000000_0
theorem coverp0000001010000000 : Covers (-79761639/125000 : ℚ) vp0000001010000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000101000000_0 : Blocks := edgeBlocks% "full/vectors/000000101000000-V-0000.bin"
noncomputable def vp000000101000000 : Blocks := vp000000101000000_0
private theorem bp0000001010000000 : Branch 0 (-79761639/250000 : ℚ) vp000000101000000 := by
  apply branch_left_normalized (c:=vp0000001010000000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-79761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-79761639/125000 : ℚ) by norm_num]
  exact coverp0000001010000000
private noncomputable def ep0000001010000001_0 : Blocks := edgeBlocks% "full/vectors/0000001010000001-E-0000.bin"
noncomputable def ep0000001010000001 : Blocks := ep0000001010000001_0
private theorem idp0000001010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101000000.list =
    C ((2:ℤ)^48) * horner X vp0000001010000001.list + horner X ep0000001010000001.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010000001 : Branch 1 (-79761639/250000 : ℚ) vp000000101000000 := by
  apply branch_checked idp0000001010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-79761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-79886639/125000 : ℚ) by norm_num]
  exact coverp0000001010000001
theorem coverp000000101000000 : Covers (-79761639/250000 : ℚ) vp000000101000000 := join_branches bp0000001010000000 bp0000001010000001
private noncomputable def vp00000010100000_0 : Blocks := edgeBlocks% "full/vectors/00000010100000-V-0000.bin"
noncomputable def vp00000010100000 : Blocks := vp00000010100000_0
private theorem bp000000101000000 : Branch 0 (-79761639/500000 : ℚ) vp00000010100000 := by
  apply branch_left_normalized (c:=vp000000101000000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-79761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-79761639/250000 : ℚ) by norm_num]
  exact coverp000000101000000
private noncomputable def ep000000101000001_0 : Blocks := edgeBlocks% "full/vectors/000000101000001-E-0000.bin"
noncomputable def ep000000101000001 : Blocks := ep000000101000001_0
private theorem idp000000101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010100000.list =
    C ((2:ℤ)^77) * horner X vp000000101000001.list + horner X ep000000101000001.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101000001 : Branch 1 (-79761639/500000 : ℚ) vp00000010100000 := by
  apply branch_checked idp000000101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-79761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-80011639/250000 : ℚ) by norm_num]
  exact coverp000000101000001
theorem coverp00000010100000 : Covers (-79761639/500000 : ℚ) vp00000010100000 := join_branches bp000000101000000 bp000000101000001
private noncomputable def vp0000001010000_0 : Blocks := edgeBlocks% "full/vectors/0000001010000-V-0000.bin"
private noncomputable def vp0000001010000_1 : Blocks := edgeBlocks% "full/vectors/0000001010000-V-0001.bin"
noncomputable def vp0000001010000 : Blocks := (Blocks.join vp0000001010000_0 vp0000001010000_1)
private theorem bp00000010100000 : Branch 0 (-79761639/1000000 : ℚ) vp0000001010000 := by
  apply branch_left_normalized (c:=vp00000010100000) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-79761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-79761639/500000 : ℚ) by norm_num]
  exact coverp00000010100000
private noncomputable def ep00000010100001_0 : Blocks := edgeBlocks% "full/vectors/00000010100001-E-0000.bin"
private noncomputable def ep00000010100001_1 : Blocks := edgeBlocks% "full/vectors/00000010100001-E-0001.bin"
noncomputable def ep00000010100001 : Blocks := (Blocks.join ep00000010100001_0 ep00000010100001_1)
private theorem idp00000010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001010000.list =
    C ((2:ℤ)^133) * horner X vp00000010100001.list + horner X ep00000010100001.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010100001 : Branch 1 (-79761639/1000000 : ℚ) vp0000001010000 := by
  apply branch_checked idp00000010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-79761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-80261639/500000 : ℚ) by norm_num]
  exact coverp00000010100001
theorem coverp0000001010000 : Covers (-79761639/1000000 : ℚ) vp0000001010000 := join_branches bp00000010100000 bp00000010100001
private noncomputable def vp000000101000_0 : Blocks := edgeBlocks% "full/vectors/000000101000-V-0000.bin"
private noncomputable def vp000000101000_1 : Blocks := edgeBlocks% "full/vectors/000000101000-V-0001.bin"
noncomputable def vp000000101000 : Blocks := (Blocks.join vp000000101000_0 vp000000101000_1)
private theorem bp0000001010000 : Branch 0 (-79761639/2000000 : ℚ) vp000000101000 := by
  apply branch_left_normalized (c:=vp0000001010000) (k:=0) (m:=130) (by decide +kernel)
  rw [show 2*(-79761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-79761639/1000000 : ℚ) by norm_num]
  exact coverp0000001010000
private noncomputable def ep0000001010001_0 : Blocks := edgeBlocks% "full/vectors/0000001010001-E-0000.bin"
private noncomputable def ep0000001010001_1 : Blocks := edgeBlocks% "full/vectors/0000001010001-E-0001.bin"
noncomputable def ep0000001010001 : Blocks := (Blocks.join ep0000001010001_0 ep0000001010001_1)
private theorem idp0000001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101000.list =
    C ((2:ℤ)^245) * horner X vp0000001010001.list + horner X ep0000001010001.list := by
  exact edge_identity (B := (2:ℤ)^459) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001010001 : Branch 1 (-79761639/2000000 : ℚ) vp000000101000 := by
  apply branch_checked idp0000001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-79761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-80761639/1000000 : ℚ) by norm_num]
  exact coverp0000001010001
theorem coverp000000101000 : Covers (-79761639/2000000 : ℚ) vp000000101000 := join_branches bp0000001010000 bp0000001010001
private noncomputable def vp00000010100_0 : Blocks := edgeBlocks% "full/vectors/00000010100-V-0000.bin"
private noncomputable def vp00000010100_1 : Blocks := edgeBlocks% "full/vectors/00000010100-V-0001.bin"
private noncomputable def vp00000010100_2 : Blocks := edgeBlocks% "full/vectors/00000010100-V-0002.bin"
private noncomputable def vp00000010100_3 : Blocks := edgeBlocks% "full/vectors/00000010100-V-0003.bin"
noncomputable def vp00000010100 : Blocks := (Blocks.join (Blocks.join vp00000010100_0 vp00000010100_1) (Blocks.join vp00000010100_2 vp00000010100_3))
private theorem bp000000101000 : Branch 0 (-79761639/4000000 : ℚ) vp00000010100 := by
  apply branch_left_normalized (c:=vp000000101000) (k:=0) (m:=241) (by decide +kernel)
  rw [show 2*(-79761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-79761639/2000000 : ℚ) by norm_num]
  exact coverp000000101000
private noncomputable def ep000000101001_0 : Blocks := edgeBlocks% "full/vectors/000000101001-E-0000.bin"
private noncomputable def ep000000101001_1 : Blocks := edgeBlocks% "full/vectors/000000101001-E-0001.bin"
private noncomputable def ep000000101001_2 : Blocks := edgeBlocks% "full/vectors/000000101001-E-0002.bin"
private noncomputable def ep000000101001_3 : Blocks := edgeBlocks% "full/vectors/000000101001-E-0003.bin"
noncomputable def ep000000101001 : Blocks := (Blocks.join (Blocks.join ep000000101001_0 ep000000101001_1) (Blocks.join ep000000101001_2 ep000000101001_3))
private theorem idp000000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010100.list =
    C ((2:ℤ)^472) * horner X vp000000101001.list + horner X ep000000101001.list := by
  exact edge_identity (B := (2:ℤ)^794) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000101001 : Branch 1 (-79761639/4000000 : ℚ) vp00000010100 := by
  apply branch_checked idp000000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-79761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-81761639/2000000 : ℚ) by norm_num]
  exact coverp000000101001
theorem coverp00000010100 : Covers (-79761639/4000000 : ℚ) vp00000010100 := join_branches bp000000101000 bp000000101001
private noncomputable def vp0000001010_0 : Blocks := edgeBlocks% "full/vectors/0000001010-V-0000.bin"
private noncomputable def vp0000001010_1 : Blocks := edgeBlocks% "full/vectors/0000001010-V-0001.bin"
private noncomputable def vp0000001010_2 : Blocks := edgeBlocks% "full/vectors/0000001010-V-0002.bin"
private noncomputable def vp0000001010_3 : Blocks := edgeBlocks% "full/vectors/0000001010-V-0003.bin"
private noncomputable def vp0000001010_4 : Blocks := edgeBlocks% "full/vectors/0000001010-V-0004.bin"
private noncomputable def vp0000001010_5 : Blocks := edgeBlocks% "full/vectors/0000001010-V-0005.bin"
private noncomputable def vp0000001010_6 : Blocks := edgeBlocks% "full/vectors/0000001010-V-0006.bin"
noncomputable def vp0000001010 : Blocks := (Blocks.join (Blocks.join vp0000001010_0 (Blocks.join vp0000001010_1 vp0000001010_2)) (Blocks.join (Blocks.join vp0000001010_3 vp0000001010_4) (Blocks.join vp0000001010_5 vp0000001010_6)))
private theorem bp00000010100 : Branch 0 (-79761639/8000000 : ℚ) vp0000001010 := by
  apply branch_left_normalized (c:=vp00000010100) (k:=0) (m:=459) (by decide +kernel)
  rw [show 2*(-79761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-79761639/4000000 : ℚ) by norm_num]
  exact coverp00000010100
private noncomputable def ep00000010101_0 : Blocks := edgeBlocks% "full/vectors/00000010101-E-0000.bin"
private noncomputable def ep00000010101_1 : Blocks := edgeBlocks% "full/vectors/00000010101-E-0001.bin"
private noncomputable def ep00000010101_2 : Blocks := edgeBlocks% "full/vectors/00000010101-E-0002.bin"
private noncomputable def ep00000010101_3 : Blocks := edgeBlocks% "full/vectors/00000010101-E-0003.bin"
private noncomputable def ep00000010101_4 : Blocks := edgeBlocks% "full/vectors/00000010101-E-0004.bin"
private noncomputable def ep00000010101_5 : Blocks := edgeBlocks% "full/vectors/00000010101-E-0005.bin"
private noncomputable def ep00000010101_6 : Blocks := edgeBlocks% "full/vectors/00000010101-E-0006.bin"
noncomputable def ep00000010101 : Blocks := (Blocks.join (Blocks.join ep00000010101_0 (Blocks.join ep00000010101_1 ep00000010101_2)) (Blocks.join (Blocks.join ep00000010101_3 ep00000010101_4) (Blocks.join ep00000010101_5 ep00000010101_6)))
private theorem idp00000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001010.list =
    C ((2:ℤ)^916) * horner X vp00000010101.list + horner X ep00000010101.list := by
  exact edge_identity (B := (2:ℤ)^1457) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010101 : Branch 1 (-79761639/8000000 : ℚ) vp0000001010 := by
  apply branch_checked idp00000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-79761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-83761639/4000000 : ℚ) by norm_num]
  exact coverp00000010101
theorem coverp0000001010 : Covers (-79761639/8000000 : ℚ) vp0000001010 := join_branches bp00000010100 bp00000010101
private noncomputable def vp000000101_0 : Blocks := edgeBlocks% "full/vectors/000000101-V-0000.bin"
private noncomputable def vp000000101_1 : Blocks := edgeBlocks% "full/vectors/000000101-V-0001.bin"
private noncomputable def vp000000101_2 : Blocks := edgeBlocks% "full/vectors/000000101-V-0002.bin"
private noncomputable def vp000000101_3 : Blocks := edgeBlocks% "full/vectors/000000101-V-0003.bin"
private noncomputable def vp000000101_4 : Blocks := edgeBlocks% "full/vectors/000000101-V-0004.bin"
private noncomputable def vp000000101_5 : Blocks := edgeBlocks% "full/vectors/000000101-V-0005.bin"
private noncomputable def vp000000101_6 : Blocks := edgeBlocks% "full/vectors/000000101-V-0006.bin"
private noncomputable def vp000000101_7 : Blocks := edgeBlocks% "full/vectors/000000101-V-0007.bin"
private noncomputable def vp000000101_8 : Blocks := edgeBlocks% "full/vectors/000000101-V-0008.bin"
private noncomputable def vp000000101_9 : Blocks := edgeBlocks% "full/vectors/000000101-V-0009.bin"
private noncomputable def vp000000101_10 : Blocks := edgeBlocks% "full/vectors/000000101-V-0010.bin"
private noncomputable def vp000000101_11 : Blocks := edgeBlocks% "full/vectors/000000101-V-0011.bin"
private noncomputable def vp000000101_12 : Blocks := edgeBlocks% "full/vectors/000000101-V-0012.bin"
private noncomputable def vp000000101_13 : Blocks := edgeBlocks% "full/vectors/000000101-V-0013.bin"
noncomputable def vp000000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000000101_0 (Blocks.join vp000000101_1 vp000000101_2)) (Blocks.join (Blocks.join vp000000101_3 vp000000101_4) (Blocks.join vp000000101_5 vp000000101_6))) (Blocks.join (Blocks.join vp000000101_7 (Blocks.join vp000000101_8 vp000000101_9)) (Blocks.join (Blocks.join vp000000101_10 vp000000101_11) (Blocks.join vp000000101_12 vp000000101_13))))
private theorem bp0000001010 : Branch 0 (-79761639/16000000 : ℚ) vp000000101 := by
  apply branch_left_normalized (c:=vp0000001010) (k:=0) (m:=890) (by decide +kernel)
  rw [show 2*(-79761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-79761639/8000000 : ℚ) by norm_num]
  exact coverp0000001010
private noncomputable def ep0000001011_0 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0000.bin"
private noncomputable def ep0000001011_1 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0001.bin"
private noncomputable def ep0000001011_2 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0002.bin"
private noncomputable def ep0000001011_3 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0003.bin"
private noncomputable def ep0000001011_4 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0004.bin"
private noncomputable def ep0000001011_5 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0005.bin"
private noncomputable def ep0000001011_6 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0006.bin"
private noncomputable def ep0000001011_7 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0007.bin"
private noncomputable def ep0000001011_8 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0008.bin"
private noncomputable def ep0000001011_9 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0009.bin"
private noncomputable def ep0000001011_10 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0010.bin"
private noncomputable def ep0000001011_11 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0011.bin"
private noncomputable def ep0000001011_12 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0012.bin"
private noncomputable def ep0000001011_13 : Blocks := edgeBlocks% "full/vectors/0000001011-E-0013.bin"
noncomputable def ep0000001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000001011_0 (Blocks.join ep0000001011_1 ep0000001011_2)) (Blocks.join (Blocks.join ep0000001011_3 ep0000001011_4) (Blocks.join ep0000001011_5 ep0000001011_6))) (Blocks.join (Blocks.join ep0000001011_7 (Blocks.join ep0000001011_8 ep0000001011_9)) (Blocks.join (Blocks.join ep0000001011_10 ep0000001011_11) (Blocks.join ep0000001011_12 ep0000001011_13))))
private theorem idp0000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000101.list =
    C ((2:ℤ)^1791) * horner X vp0000001011.list + horner X ep0000001011.list := by
  exact edge_identity (B := (2:ℤ)^2762) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001011 : Branch 1 (-79761639/16000000 : ℚ) vp000000101 := by
  apply branch_checked idp0000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-79761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-87761639/8000000 : ℚ) by norm_num]
  exact coverp0000001011
theorem coverp000000101 : Covers (-79761639/16000000 : ℚ) vp000000101 := join_branches bp0000001010 bp0000001011
private noncomputable def vp00000010_0 : Blocks := edgeBlocks% "full/vectors/00000010-V-0000.bin"
private noncomputable def vp00000010_1 : Blocks := edgeBlocks% "full/vectors/00000010-V-0001.bin"
private noncomputable def vp00000010_2 : Blocks := edgeBlocks% "full/vectors/00000010-V-0002.bin"
private noncomputable def vp00000010_3 : Blocks := edgeBlocks% "full/vectors/00000010-V-0003.bin"
private noncomputable def vp00000010_4 : Blocks := edgeBlocks% "full/vectors/00000010-V-0004.bin"
private noncomputable def vp00000010_5 : Blocks := edgeBlocks% "full/vectors/00000010-V-0005.bin"
private noncomputable def vp00000010_6 : Blocks := edgeBlocks% "full/vectors/00000010-V-0006.bin"
private noncomputable def vp00000010_7 : Blocks := edgeBlocks% "full/vectors/00000010-V-0007.bin"
private noncomputable def vp00000010_8 : Blocks := edgeBlocks% "full/vectors/00000010-V-0008.bin"
private noncomputable def vp00000010_9 : Blocks := edgeBlocks% "full/vectors/00000010-V-0009.bin"
private noncomputable def vp00000010_10 : Blocks := edgeBlocks% "full/vectors/00000010-V-0010.bin"
private noncomputable def vp00000010_11 : Blocks := edgeBlocks% "full/vectors/00000010-V-0011.bin"
private noncomputable def vp00000010_12 : Blocks := edgeBlocks% "full/vectors/00000010-V-0012.bin"
private noncomputable def vp00000010_13 : Blocks := edgeBlocks% "full/vectors/00000010-V-0013.bin"
private noncomputable def vp00000010_14 : Blocks := edgeBlocks% "full/vectors/00000010-V-0014.bin"
private noncomputable def vp00000010_15 : Blocks := edgeBlocks% "full/vectors/00000010-V-0015.bin"
private noncomputable def vp00000010_16 : Blocks := edgeBlocks% "full/vectors/00000010-V-0016.bin"
private noncomputable def vp00000010_17 : Blocks := edgeBlocks% "full/vectors/00000010-V-0017.bin"
private noncomputable def vp00000010_18 : Blocks := edgeBlocks% "full/vectors/00000010-V-0018.bin"
private noncomputable def vp00000010_19 : Blocks := edgeBlocks% "full/vectors/00000010-V-0019.bin"
private noncomputable def vp00000010_20 : Blocks := edgeBlocks% "full/vectors/00000010-V-0020.bin"
private noncomputable def vp00000010_21 : Blocks := edgeBlocks% "full/vectors/00000010-V-0021.bin"
private noncomputable def vp00000010_22 : Blocks := edgeBlocks% "full/vectors/00000010-V-0022.bin"
private noncomputable def vp00000010_23 : Blocks := edgeBlocks% "full/vectors/00000010-V-0023.bin"
private noncomputable def vp00000010_24 : Blocks := edgeBlocks% "full/vectors/00000010-V-0024.bin"
private noncomputable def vp00000010_25 : Blocks := edgeBlocks% "full/vectors/00000010-V-0025.bin"
private noncomputable def vp00000010_26 : Blocks := edgeBlocks% "full/vectors/00000010-V-0026.bin"
private noncomputable def vp00000010_27 : Blocks := edgeBlocks% "full/vectors/00000010-V-0027.bin"
private noncomputable def vp00000010_28 : Blocks := edgeBlocks% "full/vectors/00000010-V-0028.bin"
private noncomputable def vp00000010_29 : Blocks := edgeBlocks% "full/vectors/00000010-V-0029.bin"
noncomputable def vp00000010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00000010_0 (Blocks.join vp00000010_1 vp00000010_2)) (Blocks.join (Blocks.join vp00000010_3 vp00000010_4) (Blocks.join vp00000010_5 vp00000010_6))) (Blocks.join (Blocks.join (Blocks.join vp00000010_7 vp00000010_8) (Blocks.join vp00000010_9 vp00000010_10)) (Blocks.join (Blocks.join vp00000010_11 vp00000010_12) (Blocks.join vp00000010_13 vp00000010_14)))) (Blocks.join (Blocks.join (Blocks.join vp00000010_15 (Blocks.join vp00000010_16 vp00000010_17)) (Blocks.join (Blocks.join vp00000010_18 vp00000010_19) (Blocks.join vp00000010_20 vp00000010_21))) (Blocks.join (Blocks.join (Blocks.join vp00000010_22 vp00000010_23) (Blocks.join vp00000010_24 vp00000010_25)) (Blocks.join (Blocks.join vp00000010_26 vp00000010_27) (Blocks.join vp00000010_28 vp00000010_29)))))
private theorem bp000000100 : Branch 0 (-63761639/32000000 : ℚ) vp00000010 := by
  apply branch_left_normalized (c:=vp000000100) (k:=0) (m:=1923) (by decide +kernel)
  rw [show 2*(-63761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-63761639/16000000 : ℚ) by norm_num]
  exact coverp000000100
private noncomputable def ep000000101_0 : Blocks := edgeBlocks% "full/vectors/000000101-E-0000.bin"
private noncomputable def ep000000101_1 : Blocks := edgeBlocks% "full/vectors/000000101-E-0001.bin"
private noncomputable def ep000000101_2 : Blocks := edgeBlocks% "full/vectors/000000101-E-0002.bin"
private noncomputable def ep000000101_3 : Blocks := edgeBlocks% "full/vectors/000000101-E-0003.bin"
private noncomputable def ep000000101_4 : Blocks := edgeBlocks% "full/vectors/000000101-E-0004.bin"
private noncomputable def ep000000101_5 : Blocks := edgeBlocks% "full/vectors/000000101-E-0005.bin"
private noncomputable def ep000000101_6 : Blocks := edgeBlocks% "full/vectors/000000101-E-0006.bin"
private noncomputable def ep000000101_7 : Blocks := edgeBlocks% "full/vectors/000000101-E-0007.bin"
private noncomputable def ep000000101_8 : Blocks := edgeBlocks% "full/vectors/000000101-E-0008.bin"
private noncomputable def ep000000101_9 : Blocks := edgeBlocks% "full/vectors/000000101-E-0009.bin"
private noncomputable def ep000000101_10 : Blocks := edgeBlocks% "full/vectors/000000101-E-0010.bin"
private noncomputable def ep000000101_11 : Blocks := edgeBlocks% "full/vectors/000000101-E-0011.bin"
private noncomputable def ep000000101_12 : Blocks := edgeBlocks% "full/vectors/000000101-E-0012.bin"
private noncomputable def ep000000101_13 : Blocks := edgeBlocks% "full/vectors/000000101-E-0013.bin"
private noncomputable def ep000000101_14 : Blocks := edgeBlocks% "full/vectors/000000101-E-0014.bin"
private noncomputable def ep000000101_15 : Blocks := edgeBlocks% "full/vectors/000000101-E-0015.bin"
private noncomputable def ep000000101_16 : Blocks := edgeBlocks% "full/vectors/000000101-E-0016.bin"
private noncomputable def ep000000101_17 : Blocks := edgeBlocks% "full/vectors/000000101-E-0017.bin"
private noncomputable def ep000000101_18 : Blocks := edgeBlocks% "full/vectors/000000101-E-0018.bin"
private noncomputable def ep000000101_19 : Blocks := edgeBlocks% "full/vectors/000000101-E-0019.bin"
private noncomputable def ep000000101_20 : Blocks := edgeBlocks% "full/vectors/000000101-E-0020.bin"
private noncomputable def ep000000101_21 : Blocks := edgeBlocks% "full/vectors/000000101-E-0021.bin"
private noncomputable def ep000000101_22 : Blocks := edgeBlocks% "full/vectors/000000101-E-0022.bin"
private noncomputable def ep000000101_23 : Blocks := edgeBlocks% "full/vectors/000000101-E-0023.bin"
private noncomputable def ep000000101_24 : Blocks := edgeBlocks% "full/vectors/000000101-E-0024.bin"
private noncomputable def ep000000101_25 : Blocks := edgeBlocks% "full/vectors/000000101-E-0025.bin"
private noncomputable def ep000000101_26 : Blocks := edgeBlocks% "full/vectors/000000101-E-0026.bin"
private noncomputable def ep000000101_27 : Blocks := edgeBlocks% "full/vectors/000000101-E-0027.bin"
private noncomputable def ep000000101_28 : Blocks := edgeBlocks% "full/vectors/000000101-E-0028.bin"
private noncomputable def ep000000101_29 : Blocks := edgeBlocks% "full/vectors/000000101-E-0029.bin"
noncomputable def ep000000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep000000101_0 (Blocks.join ep000000101_1 ep000000101_2)) (Blocks.join (Blocks.join ep000000101_3 ep000000101_4) (Blocks.join ep000000101_5 ep000000101_6))) (Blocks.join (Blocks.join (Blocks.join ep000000101_7 ep000000101_8) (Blocks.join ep000000101_9 ep000000101_10)) (Blocks.join (Blocks.join ep000000101_11 ep000000101_12) (Blocks.join ep000000101_13 ep000000101_14)))) (Blocks.join (Blocks.join (Blocks.join ep000000101_15 (Blocks.join ep000000101_16 ep000000101_17)) (Blocks.join (Blocks.join ep000000101_18 ep000000101_19) (Blocks.join ep000000101_20 ep000000101_21))) (Blocks.join (Blocks.join (Blocks.join ep000000101_22 ep000000101_23) (Blocks.join ep000000101_24 ep000000101_25)) (Blocks.join (Blocks.join ep000000101_26 ep000000101_27) (Blocks.join ep000000101_28 ep000000101_29)))))
private def ptsp000000101 : List ℤ := [((2:ℤ)^3229+0),((2:ℤ)^3229+1)]
private theorem boundp000000101 : 2^vp00000010.size*absSum vp00000010.list + ((2:ℤ)^3796*absSum vp000000101.list+absSum ep000000101.list) < (2:ℤ)^5848 := by decide +kernel
private theorem pointp000000101_0 : fastHom 1 ((2:ℤ)^3229+0) vp00000010 = ((2:ℤ)^3796)*vp000000101.subst ((2:ℤ)^3229+0)+ep000000101.subst ((2:ℤ)^3229+0) := by decide +kernel
private theorem pointp000000101_1 : fastHom 1 ((2:ℤ)^3229+1) vp00000010 = ((2:ℤ)^3796)*vp000000101.subst ((2:ℤ)^3229+1)+ep000000101.subst ((2:ℤ)^3229+1) := by decide +kernel
private theorem checkp000000101 (x:ℤ) (hx:x ∈ ptsp000000101) : fastHom 1 x vp00000010 = ((2:ℤ)^3796)*vp000000101.subst x+ep000000101.subst x := by
  simp only [ptsp000000101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp000000101_0
  · exact pointp000000101_1
private theorem idp000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010.list =
    C ((2:ℤ)^3796) * horner X vp000000101.list + horner X ep000000101.list := by
  apply edge_identity (B := (2:ℤ)^5848) (by decide) (by positivity) (by positivity) boundp000000101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp000000101 (by decide +kernel)
  · have h : ptsp000000101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp000000101.trans_le (by decide +kernel)
  · exact checkp000000101
private theorem bp000000101 : Branch 1 (-63761639/32000000 : ℚ) vp00000010 := by
  apply branch_checked idp000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-63761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-79761639/16000000 : ℚ) by norm_num]
  exact coverp000000101
theorem coverp00000010 : Covers (-63761639/32000000 : ℚ) vp00000010 := join_branches bp000000100 bp000000101
end NextProof.EdgeFull

