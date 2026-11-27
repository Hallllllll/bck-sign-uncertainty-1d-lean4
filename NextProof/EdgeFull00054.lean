import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000010101111111_0 : Blocks := edgeBlocks% "full/vectors/000010101111111-V-0000.bin"
noncomputable def vp000010101111111 : Blocks := vp000010101111111_0
theorem coverp000010101111111 : Covers (-351511639/250000 : ℚ) vp000010101111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101111110_0 : Blocks := edgeBlocks% "full/vectors/000010101111110-V-0000.bin"
noncomputable def vp000010101111110 : Blocks := vp000010101111110_0
theorem coverp000010101111110 : Covers (-351261639/250000 : ℚ) vp000010101111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010111111_0 : Blocks := edgeBlocks% "full/vectors/00001010111111-V-0000.bin"
noncomputable def vp00001010111111 : Blocks := vp00001010111111_0
private theorem bp000010101111110 : Branch 0 (-351261639/500000 : ℚ) vp00001010111111 := by
  apply branch_left_normalized (c:=vp000010101111110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-351261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-351261639/250000 : ℚ) by norm_num]
  exact coverp000010101111110
private noncomputable def ep000010101111111_0 : Blocks := edgeBlocks% "full/vectors/000010101111111-E-0000.bin"
noncomputable def ep000010101111111 : Blocks := ep000010101111111_0
private theorem idp000010101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010111111.list =
    C ((2:ℤ)^47) * horner X vp000010101111111.list + horner X ep000010101111111.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101111111 : Branch 1 (-351261639/500000 : ℚ) vp00001010111111 := by
  apply branch_checked idp000010101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-351261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-351511639/250000 : ℚ) by norm_num]
  exact coverp000010101111111
theorem coverp00001010111111 : Covers (-351261639/500000 : ℚ) vp00001010111111 := join_branches bp000010101111110 bp000010101111111
private noncomputable def vp00001010111110_0 : Blocks := edgeBlocks% "full/vectors/00001010111110-V-0000.bin"
noncomputable def vp00001010111110 : Blocks := vp00001010111110_0
theorem coverp00001010111110 : Covers (-350761639/500000 : ℚ) vp00001010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101011111_0 : Blocks := edgeBlocks% "full/vectors/0000101011111-V-0000.bin"
noncomputable def vp0000101011111 : Blocks := vp0000101011111_0
private theorem bp00001010111110 : Branch 0 (-350761639/1000000 : ℚ) vp0000101011111 := by
  apply branch_left_normalized (c:=vp00001010111110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-350761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-350761639/500000 : ℚ) by norm_num]
  exact coverp00001010111110
private noncomputable def ep00001010111111_0 : Blocks := edgeBlocks% "full/vectors/00001010111111-E-0000.bin"
noncomputable def ep00001010111111 : Blocks := ep00001010111111_0
private theorem idp00001010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101011111.list =
    C ((2:ℤ)^77) * horner X vp00001010111111.list + horner X ep00001010111111.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010111111 : Branch 1 (-350761639/1000000 : ℚ) vp0000101011111 := by
  apply branch_checked idp00001010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-350761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-351261639/500000 : ℚ) by norm_num]
  exact coverp00001010111111
theorem coverp0000101011111 : Covers (-350761639/1000000 : ℚ) vp0000101011111 := join_branches bp00001010111110 bp00001010111111
private noncomputable def vp00001010111101_0 : Blocks := edgeBlocks% "full/vectors/00001010111101-V-0000.bin"
noncomputable def vp00001010111101 : Blocks := vp00001010111101_0
theorem coverp00001010111101 : Covers (-350261639/500000 : ℚ) vp00001010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010111100_0 : Blocks := edgeBlocks% "full/vectors/00001010111100-V-0000.bin"
noncomputable def vp00001010111100 : Blocks := vp00001010111100_0
theorem coverp00001010111100 : Covers (-349761639/500000 : ℚ) vp00001010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101011110_0 : Blocks := edgeBlocks% "full/vectors/0000101011110-V-0000.bin"
noncomputable def vp0000101011110 : Blocks := vp0000101011110_0
private theorem bp00001010111100 : Branch 0 (-349761639/1000000 : ℚ) vp0000101011110 := by
  apply branch_left_normalized (c:=vp00001010111100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-349761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-349761639/500000 : ℚ) by norm_num]
  exact coverp00001010111100
private noncomputable def ep00001010111101_0 : Blocks := edgeBlocks% "full/vectors/00001010111101-E-0000.bin"
noncomputable def ep00001010111101 : Blocks := ep00001010111101_0
private theorem idp00001010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101011110.list =
    C ((2:ℤ)^77) * horner X vp00001010111101.list + horner X ep00001010111101.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010111101 : Branch 1 (-349761639/1000000 : ℚ) vp0000101011110 := by
  apply branch_checked idp00001010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-349761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-350261639/500000 : ℚ) by norm_num]
  exact coverp00001010111101
theorem coverp0000101011110 : Covers (-349761639/1000000 : ℚ) vp0000101011110 := join_branches bp00001010111100 bp00001010111101
private noncomputable def vp000010101111_0 : Blocks := edgeBlocks% "full/vectors/000010101111-V-0000.bin"
noncomputable def vp000010101111 : Blocks := vp000010101111_0
private theorem bp0000101011110 : Branch 0 (-349761639/2000000 : ℚ) vp000010101111 := by
  apply branch_left_normalized (c:=vp0000101011110) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-349761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-349761639/1000000 : ℚ) by norm_num]
  exact coverp0000101011110
private noncomputable def ep0000101011111_0 : Blocks := edgeBlocks% "full/vectors/0000101011111-E-0000.bin"
noncomputable def ep0000101011111 : Blocks := ep0000101011111_0
private theorem idp0000101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010101111.list =
    C ((2:ℤ)^134) * horner X vp0000101011111.list + horner X ep0000101011111.list := by
  exact edge_identity (B := (2:ℤ)^286) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101011111 : Branch 1 (-349761639/2000000 : ℚ) vp000010101111 := by
  apply branch_checked idp0000101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-349761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-350761639/1000000 : ℚ) by norm_num]
  exact coverp0000101011111
theorem coverp000010101111 : Covers (-349761639/2000000 : ℚ) vp000010101111 := join_branches bp0000101011110 bp0000101011111
private noncomputable def vp00001010111011_0 : Blocks := edgeBlocks% "full/vectors/00001010111011-V-0000.bin"
noncomputable def vp00001010111011 : Blocks := vp00001010111011_0
theorem coverp00001010111011 : Covers (-349261639/500000 : ℚ) vp00001010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010111010_0 : Blocks := edgeBlocks% "full/vectors/00001010111010-V-0000.bin"
noncomputable def vp00001010111010 : Blocks := vp00001010111010_0
theorem coverp00001010111010 : Covers (-348761639/500000 : ℚ) vp00001010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101011101_0 : Blocks := edgeBlocks% "full/vectors/0000101011101-V-0000.bin"
noncomputable def vp0000101011101 : Blocks := vp0000101011101_0
private theorem bp00001010111010 : Branch 0 (-348761639/1000000 : ℚ) vp0000101011101 := by
  apply branch_left_normalized (c:=vp00001010111010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-348761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-348761639/500000 : ℚ) by norm_num]
  exact coverp00001010111010
private noncomputable def ep00001010111011_0 : Blocks := edgeBlocks% "full/vectors/00001010111011-E-0000.bin"
noncomputable def ep00001010111011 : Blocks := ep00001010111011_0
private theorem idp00001010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101011101.list =
    C ((2:ℤ)^77) * horner X vp00001010111011.list + horner X ep00001010111011.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010111011 : Branch 1 (-348761639/1000000 : ℚ) vp0000101011101 := by
  apply branch_checked idp00001010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-348761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-349261639/500000 : ℚ) by norm_num]
  exact coverp00001010111011
theorem coverp0000101011101 : Covers (-348761639/1000000 : ℚ) vp0000101011101 := join_branches bp00001010111010 bp00001010111011
private noncomputable def vp000010101110011_0 : Blocks := edgeBlocks% "full/vectors/000010101110011-V-0000.bin"
noncomputable def vp000010101110011 : Blocks := vp000010101110011_0
theorem coverp000010101110011 : Covers (-348511639/250000 : ℚ) vp000010101110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101110010_0 : Blocks := edgeBlocks% "full/vectors/000010101110010-V-0000.bin"
noncomputable def vp000010101110010 : Blocks := vp000010101110010_0
theorem coverp000010101110010 : Covers (-348261639/250000 : ℚ) vp000010101110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010111001_0 : Blocks := edgeBlocks% "full/vectors/00001010111001-V-0000.bin"
noncomputable def vp00001010111001 : Blocks := vp00001010111001_0
private theorem bp000010101110010 : Branch 0 (-348261639/500000 : ℚ) vp00001010111001 := by
  apply branch_left_normalized (c:=vp000010101110010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-348261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-348261639/250000 : ℚ) by norm_num]
  exact coverp000010101110010
private noncomputable def ep000010101110011_0 : Blocks := edgeBlocks% "full/vectors/000010101110011-E-0000.bin"
noncomputable def ep000010101110011 : Blocks := ep000010101110011_0
private theorem idp000010101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010111001.list =
    C ((2:ℤ)^48) * horner X vp000010101110011.list + horner X ep000010101110011.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101110011 : Branch 1 (-348261639/500000 : ℚ) vp00001010111001 := by
  apply branch_checked idp000010101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-348261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-348511639/250000 : ℚ) by norm_num]
  exact coverp000010101110011
theorem coverp00001010111001 : Covers (-348261639/500000 : ℚ) vp00001010111001 := join_branches bp000010101110010 bp000010101110011
private noncomputable def vp000010101110001_0 : Blocks := edgeBlocks% "full/vectors/000010101110001-V-0000.bin"
noncomputable def vp000010101110001 : Blocks := vp000010101110001_0
theorem coverp000010101110001 : Covers (-348011639/250000 : ℚ) vp000010101110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101110000_0 : Blocks := edgeBlocks% "full/vectors/000010101110000-V-0000.bin"
noncomputable def vp000010101110000 : Blocks := vp000010101110000_0
theorem coverp000010101110000 : Covers (-347761639/250000 : ℚ) vp000010101110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010111000_0 : Blocks := edgeBlocks% "full/vectors/00001010111000-V-0000.bin"
noncomputable def vp00001010111000 : Blocks := vp00001010111000_0
private theorem bp000010101110000 : Branch 0 (-347761639/500000 : ℚ) vp00001010111000 := by
  apply branch_left_normalized (c:=vp000010101110000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-347761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-347761639/250000 : ℚ) by norm_num]
  exact coverp000010101110000
private noncomputable def ep000010101110001_0 : Blocks := edgeBlocks% "full/vectors/000010101110001-E-0000.bin"
noncomputable def ep000010101110001 : Blocks := ep000010101110001_0
private theorem idp000010101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010111000.list =
    C ((2:ℤ)^48) * horner X vp000010101110001.list + horner X ep000010101110001.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101110001 : Branch 1 (-347761639/500000 : ℚ) vp00001010111000 := by
  apply branch_checked idp000010101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-347761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-348011639/250000 : ℚ) by norm_num]
  exact coverp000010101110001
theorem coverp00001010111000 : Covers (-347761639/500000 : ℚ) vp00001010111000 := join_branches bp000010101110000 bp000010101110001
private noncomputable def vp0000101011100_0 : Blocks := edgeBlocks% "full/vectors/0000101011100-V-0000.bin"
noncomputable def vp0000101011100 : Blocks := vp0000101011100_0
private theorem bp00001010111000 : Branch 0 (-347761639/1000000 : ℚ) vp0000101011100 := by
  apply branch_left_normalized (c:=vp00001010111000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-347761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-347761639/500000 : ℚ) by norm_num]
  exact coverp00001010111000
private noncomputable def ep00001010111001_0 : Blocks := edgeBlocks% "full/vectors/00001010111001-E-0000.bin"
noncomputable def ep00001010111001 : Blocks := ep00001010111001_0
private theorem idp00001010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101011100.list =
    C ((2:ℤ)^78) * horner X vp00001010111001.list + horner X ep00001010111001.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010111001 : Branch 1 (-347761639/1000000 : ℚ) vp0000101011100 := by
  apply branch_checked idp00001010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-347761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-348261639/500000 : ℚ) by norm_num]
  exact coverp00001010111001
theorem coverp0000101011100 : Covers (-347761639/1000000 : ℚ) vp0000101011100 := join_branches bp00001010111000 bp00001010111001
private noncomputable def vp000010101110_0 : Blocks := edgeBlocks% "full/vectors/000010101110-V-0000.bin"
noncomputable def vp000010101110 : Blocks := vp000010101110_0
private theorem bp0000101011100 : Branch 0 (-347761639/2000000 : ℚ) vp000010101110 := by
  apply branch_left_normalized (c:=vp0000101011100) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-347761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-347761639/1000000 : ℚ) by norm_num]
  exact coverp0000101011100
private noncomputable def ep0000101011101_0 : Blocks := edgeBlocks% "full/vectors/0000101011101-E-0000.bin"
noncomputable def ep0000101011101 : Blocks := ep0000101011101_0
private theorem idp0000101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010101110.list =
    C ((2:ℤ)^134) * horner X vp0000101011101.list + horner X ep0000101011101.list := by
  exact edge_identity (B := (2:ℤ)^286) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101011101 : Branch 1 (-347761639/2000000 : ℚ) vp000010101110 := by
  apply branch_checked idp0000101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-347761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-348761639/1000000 : ℚ) by norm_num]
  exact coverp0000101011101
theorem coverp000010101110 : Covers (-347761639/2000000 : ℚ) vp000010101110 := join_branches bp0000101011100 bp0000101011101
private noncomputable def vp00001010111_0 : Blocks := edgeBlocks% "full/vectors/00001010111-V-0000.bin"
private noncomputable def vp00001010111_1 : Blocks := edgeBlocks% "full/vectors/00001010111-V-0001.bin"
noncomputable def vp00001010111 : Blocks := (Blocks.join vp00001010111_0 vp00001010111_1)
private theorem bp000010101110 : Branch 0 (-347761639/4000000 : ℚ) vp00001010111 := by
  apply branch_left_normalized (c:=vp000010101110) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-347761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-347761639/2000000 : ℚ) by norm_num]
  exact coverp000010101110
private noncomputable def ep000010101111_0 : Blocks := edgeBlocks% "full/vectors/000010101111-E-0000.bin"
private noncomputable def ep000010101111_1 : Blocks := edgeBlocks% "full/vectors/000010101111-E-0001.bin"
noncomputable def ep000010101111 : Blocks := (Blocks.join ep000010101111_0 ep000010101111_1)
private theorem idp000010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010111.list =
    C ((2:ℤ)^246) * horner X vp000010101111.list + horner X ep000010101111.list := by
  exact edge_identity (B := (2:ℤ)^448) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101111 : Branch 1 (-347761639/4000000 : ℚ) vp00001010111 := by
  apply branch_checked idp000010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-347761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-349761639/2000000 : ℚ) by norm_num]
  exact coverp000010101111
theorem coverp00001010111 : Covers (-347761639/4000000 : ℚ) vp00001010111 := join_branches bp000010101110 bp000010101111
private noncomputable def vp000010101101111_0 : Blocks := edgeBlocks% "full/vectors/000010101101111-V-0000.bin"
noncomputable def vp000010101101111 : Blocks := vp000010101101111_0
theorem coverp000010101101111 : Covers (-347511639/250000 : ℚ) vp000010101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101101110_0 : Blocks := edgeBlocks% "full/vectors/000010101101110-V-0000.bin"
noncomputable def vp000010101101110 : Blocks := vp000010101101110_0
theorem coverp000010101101110 : Covers (-347261639/250000 : ℚ) vp000010101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010110111_0 : Blocks := edgeBlocks% "full/vectors/00001010110111-V-0000.bin"
noncomputable def vp00001010110111 : Blocks := vp00001010110111_0
private theorem bp000010101101110 : Branch 0 (-347261639/500000 : ℚ) vp00001010110111 := by
  apply branch_left_normalized (c:=vp000010101101110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-347261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-347261639/250000 : ℚ) by norm_num]
  exact coverp000010101101110
private noncomputable def ep000010101101111_0 : Blocks := edgeBlocks% "full/vectors/000010101101111-E-0000.bin"
noncomputable def ep000010101101111 : Blocks := ep000010101101111_0
private theorem idp000010101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010110111.list =
    C ((2:ℤ)^48) * horner X vp000010101101111.list + horner X ep000010101101111.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101101111 : Branch 1 (-347261639/500000 : ℚ) vp00001010110111 := by
  apply branch_checked idp000010101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-347261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-347511639/250000 : ℚ) by norm_num]
  exact coverp000010101101111
theorem coverp00001010110111 : Covers (-347261639/500000 : ℚ) vp00001010110111 := join_branches bp000010101101110 bp000010101101111
private noncomputable def vp000010101101101_0 : Blocks := edgeBlocks% "full/vectors/000010101101101-V-0000.bin"
noncomputable def vp000010101101101 : Blocks := vp000010101101101_0
theorem coverp000010101101101 : Covers (-347011639/250000 : ℚ) vp000010101101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101101100_0 : Blocks := edgeBlocks% "full/vectors/000010101101100-V-0000.bin"
noncomputable def vp000010101101100 : Blocks := vp000010101101100_0
theorem coverp000010101101100 : Covers (-346761639/250000 : ℚ) vp000010101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010110110_0 : Blocks := edgeBlocks% "full/vectors/00001010110110-V-0000.bin"
noncomputable def vp00001010110110 : Blocks := vp00001010110110_0
private theorem bp000010101101100 : Branch 0 (-346761639/500000 : ℚ) vp00001010110110 := by
  apply branch_left_normalized (c:=vp000010101101100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-346761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-346761639/250000 : ℚ) by norm_num]
  exact coverp000010101101100
private noncomputable def ep000010101101101_0 : Blocks := edgeBlocks% "full/vectors/000010101101101-E-0000.bin"
noncomputable def ep000010101101101 : Blocks := ep000010101101101_0
private theorem idp000010101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010110110.list =
    C ((2:ℤ)^48) * horner X vp000010101101101.list + horner X ep000010101101101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101101101 : Branch 1 (-346761639/500000 : ℚ) vp00001010110110 := by
  apply branch_checked idp000010101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-346761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-347011639/250000 : ℚ) by norm_num]
  exact coverp000010101101101
theorem coverp00001010110110 : Covers (-346761639/500000 : ℚ) vp00001010110110 := join_branches bp000010101101100 bp000010101101101
private noncomputable def vp0000101011011_0 : Blocks := edgeBlocks% "full/vectors/0000101011011-V-0000.bin"
noncomputable def vp0000101011011 : Blocks := vp0000101011011_0
private theorem bp00001010110110 : Branch 0 (-346761639/1000000 : ℚ) vp0000101011011 := by
  apply branch_left_normalized (c:=vp00001010110110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-346761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-346761639/500000 : ℚ) by norm_num]
  exact coverp00001010110110
private noncomputable def ep00001010110111_0 : Blocks := edgeBlocks% "full/vectors/00001010110111-E-0000.bin"
noncomputable def ep00001010110111 : Blocks := ep00001010110111_0
private theorem idp00001010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101011011.list =
    C ((2:ℤ)^78) * horner X vp00001010110111.list + horner X ep00001010110111.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010110111 : Branch 1 (-346761639/1000000 : ℚ) vp0000101011011 := by
  apply branch_checked idp00001010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-346761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-347261639/500000 : ℚ) by norm_num]
  exact coverp00001010110111
theorem coverp0000101011011 : Covers (-346761639/1000000 : ℚ) vp0000101011011 := join_branches bp00001010110110 bp00001010110111
private noncomputable def vp000010101101011_0 : Blocks := edgeBlocks% "full/vectors/000010101101011-V-0000.bin"
noncomputable def vp000010101101011 : Blocks := vp000010101101011_0
theorem coverp000010101101011 : Covers (-346511639/250000 : ℚ) vp000010101101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101101010_0 : Blocks := edgeBlocks% "full/vectors/000010101101010-V-0000.bin"
noncomputable def vp000010101101010 : Blocks := vp000010101101010_0
theorem coverp000010101101010 : Covers (-346261639/250000 : ℚ) vp000010101101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010110101_0 : Blocks := edgeBlocks% "full/vectors/00001010110101-V-0000.bin"
noncomputable def vp00001010110101 : Blocks := vp00001010110101_0
private theorem bp000010101101010 : Branch 0 (-346261639/500000 : ℚ) vp00001010110101 := by
  apply branch_left_normalized (c:=vp000010101101010) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-346261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-346261639/250000 : ℚ) by norm_num]
  exact coverp000010101101010
private noncomputable def ep000010101101011_0 : Blocks := edgeBlocks% "full/vectors/000010101101011-E-0000.bin"
noncomputable def ep000010101101011 : Blocks := ep000010101101011_0
private theorem idp000010101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010110101.list =
    C ((2:ℤ)^47) * horner X vp000010101101011.list + horner X ep000010101101011.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101101011 : Branch 1 (-346261639/500000 : ℚ) vp00001010110101 := by
  apply branch_checked idp000010101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-346261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-346511639/250000 : ℚ) by norm_num]
  exact coverp000010101101011
theorem coverp00001010110101 : Covers (-346261639/500000 : ℚ) vp00001010110101 := join_branches bp000010101101010 bp000010101101011
private noncomputable def vp000010101101001_0 : Blocks := edgeBlocks% "full/vectors/000010101101001-V-0000.bin"
noncomputable def vp000010101101001 : Blocks := vp000010101101001_0
theorem coverp000010101101001 : Covers (-346011639/250000 : ℚ) vp000010101101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101101000_0 : Blocks := edgeBlocks% "full/vectors/000010101101000-V-0000.bin"
noncomputable def vp000010101101000 : Blocks := vp000010101101000_0
theorem coverp000010101101000 : Covers (-345761639/250000 : ℚ) vp000010101101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010110100_0 : Blocks := edgeBlocks% "full/vectors/00001010110100-V-0000.bin"
noncomputable def vp00001010110100 : Blocks := vp00001010110100_0
private theorem bp000010101101000 : Branch 0 (-345761639/500000 : ℚ) vp00001010110100 := by
  apply branch_left_normalized (c:=vp000010101101000) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-345761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-345761639/250000 : ℚ) by norm_num]
  exact coverp000010101101000
private noncomputable def ep000010101101001_0 : Blocks := edgeBlocks% "full/vectors/000010101101001-E-0000.bin"
noncomputable def ep000010101101001 : Blocks := ep000010101101001_0
private theorem idp000010101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010110100.list =
    C ((2:ℤ)^47) * horner X vp000010101101001.list + horner X ep000010101101001.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101101001 : Branch 1 (-345761639/500000 : ℚ) vp00001010110100 := by
  apply branch_checked idp000010101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-345761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-346011639/250000 : ℚ) by norm_num]
  exact coverp000010101101001
theorem coverp00001010110100 : Covers (-345761639/500000 : ℚ) vp00001010110100 := join_branches bp000010101101000 bp000010101101001
private noncomputable def vp0000101011010_0 : Blocks := edgeBlocks% "full/vectors/0000101011010-V-0000.bin"
noncomputable def vp0000101011010 : Blocks := vp0000101011010_0
private theorem bp00001010110100 : Branch 0 (-345761639/1000000 : ℚ) vp0000101011010 := by
  apply branch_left_normalized (c:=vp00001010110100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-345761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-345761639/500000 : ℚ) by norm_num]
  exact coverp00001010110100
private noncomputable def ep00001010110101_0 : Blocks := edgeBlocks% "full/vectors/00001010110101-E-0000.bin"
noncomputable def ep00001010110101 : Blocks := ep00001010110101_0
private theorem idp00001010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101011010.list =
    C ((2:ℤ)^77) * horner X vp00001010110101.list + horner X ep00001010110101.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010110101 : Branch 1 (-345761639/1000000 : ℚ) vp0000101011010 := by
  apply branch_checked idp00001010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-345761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-346261639/500000 : ℚ) by norm_num]
  exact coverp00001010110101
theorem coverp0000101011010 : Covers (-345761639/1000000 : ℚ) vp0000101011010 := join_branches bp00001010110100 bp00001010110101
private noncomputable def vp000010101101_0 : Blocks := edgeBlocks% "full/vectors/000010101101-V-0000.bin"
private noncomputable def vp000010101101_1 : Blocks := edgeBlocks% "full/vectors/000010101101-V-0001.bin"
noncomputable def vp000010101101 : Blocks := (Blocks.join vp000010101101_0 vp000010101101_1)
private theorem bp0000101011010 : Branch 0 (-345761639/2000000 : ℚ) vp000010101101 := by
  apply branch_left_normalized (c:=vp0000101011010) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-345761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-345761639/1000000 : ℚ) by norm_num]
  exact coverp0000101011010
private noncomputable def ep0000101011011_0 : Blocks := edgeBlocks% "full/vectors/0000101011011-E-0000.bin"
private noncomputable def ep0000101011011_1 : Blocks := edgeBlocks% "full/vectors/0000101011011-E-0001.bin"
noncomputable def ep0000101011011 : Blocks := (Blocks.join ep0000101011011_0 ep0000101011011_1)
private theorem idp0000101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010101101.list =
    C ((2:ℤ)^134) * horner X vp0000101011011.list + horner X ep0000101011011.list := by
  exact edge_identity (B := (2:ℤ)^287) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101011011 : Branch 1 (-345761639/2000000 : ℚ) vp000010101101 := by
  apply branch_checked idp0000101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-345761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-346761639/1000000 : ℚ) by norm_num]
  exact coverp0000101011011
theorem coverp000010101101 : Covers (-345761639/2000000 : ℚ) vp000010101101 := join_branches bp0000101011010 bp0000101011011
private noncomputable def vp000010101100111_0 : Blocks := edgeBlocks% "full/vectors/000010101100111-V-0000.bin"
noncomputable def vp000010101100111 : Blocks := vp000010101100111_0
theorem coverp000010101100111 : Covers (-345511639/250000 : ℚ) vp000010101100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101100110_0 : Blocks := edgeBlocks% "full/vectors/000010101100110-V-0000.bin"
noncomputable def vp000010101100110 : Blocks := vp000010101100110_0
theorem coverp000010101100110 : Covers (-345261639/250000 : ℚ) vp000010101100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010110011_0 : Blocks := edgeBlocks% "full/vectors/00001010110011-V-0000.bin"
noncomputable def vp00001010110011 : Blocks := vp00001010110011_0
private theorem bp000010101100110 : Branch 0 (-345261639/500000 : ℚ) vp00001010110011 := by
  apply branch_left_normalized (c:=vp000010101100110) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-345261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-345261639/250000 : ℚ) by norm_num]
  exact coverp000010101100110
private noncomputable def ep000010101100111_0 : Blocks := edgeBlocks% "full/vectors/000010101100111-E-0000.bin"
noncomputable def ep000010101100111 : Blocks := ep000010101100111_0
private theorem idp000010101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010110011.list =
    C ((2:ℤ)^47) * horner X vp000010101100111.list + horner X ep000010101100111.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101100111 : Branch 1 (-345261639/500000 : ℚ) vp00001010110011 := by
  apply branch_checked idp000010101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-345261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-345511639/250000 : ℚ) by norm_num]
  exact coverp000010101100111
theorem coverp00001010110011 : Covers (-345261639/500000 : ℚ) vp00001010110011 := join_branches bp000010101100110 bp000010101100111
private noncomputable def vp00001010110010_0 : Blocks := edgeBlocks% "full/vectors/00001010110010-V-0000.bin"
noncomputable def vp00001010110010 : Blocks := vp00001010110010_0
theorem coverp00001010110010 : Covers (-344761639/500000 : ℚ) vp00001010110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000101011001_0 : Blocks := edgeBlocks% "full/vectors/0000101011001-V-0000.bin"
noncomputable def vp0000101011001 : Blocks := vp0000101011001_0
private theorem bp00001010110010 : Branch 0 (-344761639/1000000 : ℚ) vp0000101011001 := by
  apply branch_left_normalized (c:=vp00001010110010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-344761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-344761639/500000 : ℚ) by norm_num]
  exact coverp00001010110010
private noncomputable def ep00001010110011_0 : Blocks := edgeBlocks% "full/vectors/00001010110011-E-0000.bin"
noncomputable def ep00001010110011 : Blocks := ep00001010110011_0
private theorem idp00001010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101011001.list =
    C ((2:ℤ)^77) * horner X vp00001010110011.list + horner X ep00001010110011.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010110011 : Branch 1 (-344761639/1000000 : ℚ) vp0000101011001 := by
  apply branch_checked idp00001010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-344761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-345261639/500000 : ℚ) by norm_num]
  exact coverp00001010110011
theorem coverp0000101011001 : Covers (-344761639/1000000 : ℚ) vp0000101011001 := join_branches bp00001010110010 bp00001010110011
private noncomputable def vp000010101100011_0 : Blocks := edgeBlocks% "full/vectors/000010101100011-V-0000.bin"
noncomputable def vp000010101100011 : Blocks := vp000010101100011_0
theorem coverp000010101100011 : Covers (-344511639/250000 : ℚ) vp000010101100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101100010_0 : Blocks := edgeBlocks% "full/vectors/000010101100010-V-0000.bin"
noncomputable def vp000010101100010 : Blocks := vp000010101100010_0
theorem coverp000010101100010 : Covers (-344261639/250000 : ℚ) vp000010101100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010110001_0 : Blocks := edgeBlocks% "full/vectors/00001010110001-V-0000.bin"
noncomputable def vp00001010110001 : Blocks := vp00001010110001_0
private theorem bp000010101100010 : Branch 0 (-344261639/500000 : ℚ) vp00001010110001 := by
  apply branch_left_normalized (c:=vp000010101100010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-344261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-344261639/250000 : ℚ) by norm_num]
  exact coverp000010101100010
private noncomputable def ep000010101100011_0 : Blocks := edgeBlocks% "full/vectors/000010101100011-E-0000.bin"
noncomputable def ep000010101100011 : Blocks := ep000010101100011_0
private theorem idp000010101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010110001.list =
    C ((2:ℤ)^48) * horner X vp000010101100011.list + horner X ep000010101100011.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101100011 : Branch 1 (-344261639/500000 : ℚ) vp00001010110001 := by
  apply branch_checked idp000010101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-344261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-344511639/250000 : ℚ) by norm_num]
  exact coverp000010101100011
theorem coverp00001010110001 : Covers (-344261639/500000 : ℚ) vp00001010110001 := join_branches bp000010101100010 bp000010101100011
private noncomputable def vp000010101100001_0 : Blocks := edgeBlocks% "full/vectors/000010101100001-V-0000.bin"
noncomputable def vp000010101100001 : Blocks := vp000010101100001_0
theorem coverp000010101100001 : Covers (-344011639/250000 : ℚ) vp000010101100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101100000_0 : Blocks := edgeBlocks% "full/vectors/000010101100000-V-0000.bin"
noncomputable def vp000010101100000 : Blocks := vp000010101100000_0
theorem coverp000010101100000 : Covers (-343761639/250000 : ℚ) vp000010101100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010110000_0 : Blocks := edgeBlocks% "full/vectors/00001010110000-V-0000.bin"
noncomputable def vp00001010110000 : Blocks := vp00001010110000_0
private theorem bp000010101100000 : Branch 0 (-343761639/500000 : ℚ) vp00001010110000 := by
  apply branch_left_normalized (c:=vp000010101100000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-343761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-343761639/250000 : ℚ) by norm_num]
  exact coverp000010101100000
private noncomputable def ep000010101100001_0 : Blocks := edgeBlocks% "full/vectors/000010101100001-E-0000.bin"
noncomputable def ep000010101100001 : Blocks := ep000010101100001_0
private theorem idp000010101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010110000.list =
    C ((2:ℤ)^48) * horner X vp000010101100001.list + horner X ep000010101100001.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101100001 : Branch 1 (-343761639/500000 : ℚ) vp00001010110000 := by
  apply branch_checked idp000010101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-343761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-344011639/250000 : ℚ) by norm_num]
  exact coverp000010101100001
theorem coverp00001010110000 : Covers (-343761639/500000 : ℚ) vp00001010110000 := join_branches bp000010101100000 bp000010101100001
private noncomputable def vp0000101011000_0 : Blocks := edgeBlocks% "full/vectors/0000101011000-V-0000.bin"
noncomputable def vp0000101011000 : Blocks := vp0000101011000_0
private theorem bp00001010110000 : Branch 0 (-343761639/1000000 : ℚ) vp0000101011000 := by
  apply branch_left_normalized (c:=vp00001010110000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-343761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-343761639/500000 : ℚ) by norm_num]
  exact coverp00001010110000
private noncomputable def ep00001010110001_0 : Blocks := edgeBlocks% "full/vectors/00001010110001-E-0000.bin"
noncomputable def ep00001010110001 : Blocks := ep00001010110001_0
private theorem idp00001010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101011000.list =
    C ((2:ℤ)^77) * horner X vp00001010110001.list + horner X ep00001010110001.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010110001 : Branch 1 (-343761639/1000000 : ℚ) vp0000101011000 := by
  apply branch_checked idp00001010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-343761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-344261639/500000 : ℚ) by norm_num]
  exact coverp00001010110001
theorem coverp0000101011000 : Covers (-343761639/1000000 : ℚ) vp0000101011000 := join_branches bp00001010110000 bp00001010110001
private noncomputable def vp000010101100_0 : Blocks := edgeBlocks% "full/vectors/000010101100-V-0000.bin"
private noncomputable def vp000010101100_1 : Blocks := edgeBlocks% "full/vectors/000010101100-V-0001.bin"
noncomputable def vp000010101100 : Blocks := (Blocks.join vp000010101100_0 vp000010101100_1)
private theorem bp0000101011000 : Branch 0 (-343761639/2000000 : ℚ) vp000010101100 := by
  apply branch_left_normalized (c:=vp0000101011000) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-343761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-343761639/1000000 : ℚ) by norm_num]
  exact coverp0000101011000
private noncomputable def ep0000101011001_0 : Blocks := edgeBlocks% "full/vectors/0000101011001-E-0000.bin"
private noncomputable def ep0000101011001_1 : Blocks := edgeBlocks% "full/vectors/0000101011001-E-0001.bin"
noncomputable def ep0000101011001 : Blocks := (Blocks.join ep0000101011001_0 ep0000101011001_1)
private theorem idp0000101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010101100.list =
    C ((2:ℤ)^135) * horner X vp0000101011001.list + horner X ep0000101011001.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101011001 : Branch 1 (-343761639/2000000 : ℚ) vp000010101100 := by
  apply branch_checked idp0000101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-343761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-344761639/1000000 : ℚ) by norm_num]
  exact coverp0000101011001
theorem coverp000010101100 : Covers (-343761639/2000000 : ℚ) vp000010101100 := join_branches bp0000101011000 bp0000101011001
private noncomputable def vp00001010110_0 : Blocks := edgeBlocks% "full/vectors/00001010110-V-0000.bin"
private noncomputable def vp00001010110_1 : Blocks := edgeBlocks% "full/vectors/00001010110-V-0001.bin"
noncomputable def vp00001010110 : Blocks := (Blocks.join vp00001010110_0 vp00001010110_1)
private theorem bp000010101100 : Branch 0 (-343761639/4000000 : ℚ) vp00001010110 := by
  apply branch_left_normalized (c:=vp000010101100) (k:=0) (m:=128) (by decide +kernel)
  rw [show 2*(-343761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-343761639/2000000 : ℚ) by norm_num]
  exact coverp000010101100
private noncomputable def ep000010101101_0 : Blocks := edgeBlocks% "full/vectors/000010101101-E-0000.bin"
private noncomputable def ep000010101101_1 : Blocks := edgeBlocks% "full/vectors/000010101101-E-0001.bin"
noncomputable def ep000010101101 : Blocks := (Blocks.join ep000010101101_0 ep000010101101_1)
private theorem idp000010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010110.list =
    C ((2:ℤ)^248) * horner X vp000010101101.list + horner X ep000010101101.list := by
  exact edge_identity (B := (2:ℤ)^451) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101101 : Branch 1 (-343761639/4000000 : ℚ) vp00001010110 := by
  apply branch_checked idp000010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-343761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-345761639/2000000 : ℚ) by norm_num]
  exact coverp000010101101
theorem coverp00001010110 : Covers (-343761639/4000000 : ℚ) vp00001010110 := join_branches bp000010101100 bp000010101101
private noncomputable def vp0000101011_0 : Blocks := edgeBlocks% "full/vectors/0000101011-V-0000.bin"
private noncomputable def vp0000101011_1 : Blocks := edgeBlocks% "full/vectors/0000101011-V-0001.bin"
private noncomputable def vp0000101011_2 : Blocks := edgeBlocks% "full/vectors/0000101011-V-0002.bin"
private noncomputable def vp0000101011_3 : Blocks := edgeBlocks% "full/vectors/0000101011-V-0003.bin"
noncomputable def vp0000101011 : Blocks := (Blocks.join (Blocks.join vp0000101011_0 vp0000101011_1) (Blocks.join vp0000101011_2 vp0000101011_3))
private theorem bp00001010110 : Branch 0 (-343761639/8000000 : ℚ) vp0000101011 := by
  apply branch_left_normalized (c:=vp00001010110) (k:=0) (m:=235) (by decide +kernel)
  rw [show 2*(-343761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-343761639/4000000 : ℚ) by norm_num]
  exact coverp00001010110
private noncomputable def ep00001010111_0 : Blocks := edgeBlocks% "full/vectors/00001010111-E-0000.bin"
private noncomputable def ep00001010111_1 : Blocks := edgeBlocks% "full/vectors/00001010111-E-0001.bin"
private noncomputable def ep00001010111_2 : Blocks := edgeBlocks% "full/vectors/00001010111-E-0002.bin"
private noncomputable def ep00001010111_3 : Blocks := edgeBlocks% "full/vectors/00001010111-E-0003.bin"
noncomputable def ep00001010111 : Blocks := (Blocks.join (Blocks.join ep00001010111_0 ep00001010111_1) (Blocks.join ep00001010111_2 ep00001010111_3))
private theorem idp00001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101011.list =
    C ((2:ℤ)^469) * horner X vp00001010111.list + horner X ep00001010111.list := by
  exact edge_identity (B := (2:ℤ)^773) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010111 : Branch 1 (-343761639/8000000 : ℚ) vp0000101011 := by
  apply branch_checked idp00001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-343761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-347761639/4000000 : ℚ) by norm_num]
  exact coverp00001010111
theorem coverp0000101011 : Covers (-343761639/8000000 : ℚ) vp0000101011 := join_branches bp00001010110 bp00001010111
private noncomputable def vp000010101011111_0 : Blocks := edgeBlocks% "full/vectors/000010101011111-V-0000.bin"
noncomputable def vp000010101011111 : Blocks := vp000010101011111_0
theorem coverp000010101011111 : Covers (-343511639/250000 : ℚ) vp000010101011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101011110_0 : Blocks := edgeBlocks% "full/vectors/000010101011110-V-0000.bin"
noncomputable def vp000010101011110 : Blocks := vp000010101011110_0
theorem coverp000010101011110 : Covers (-343261639/250000 : ℚ) vp000010101011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010101111_0 : Blocks := edgeBlocks% "full/vectors/00001010101111-V-0000.bin"
noncomputable def vp00001010101111 : Blocks := vp00001010101111_0
private theorem bp000010101011110 : Branch 0 (-343261639/500000 : ℚ) vp00001010101111 := by
  apply branch_left_normalized (c:=vp000010101011110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-343261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-343261639/250000 : ℚ) by norm_num]
  exact coverp000010101011110
private noncomputable def ep000010101011111_0 : Blocks := edgeBlocks% "full/vectors/000010101011111-E-0000.bin"
noncomputable def ep000010101011111 : Blocks := ep000010101011111_0
private theorem idp000010101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010101111.list =
    C ((2:ℤ)^48) * horner X vp000010101011111.list + horner X ep000010101011111.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101011111 : Branch 1 (-343261639/500000 : ℚ) vp00001010101111 := by
  apply branch_checked idp000010101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-343261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-343511639/250000 : ℚ) by norm_num]
  exact coverp000010101011111
theorem coverp00001010101111 : Covers (-343261639/500000 : ℚ) vp00001010101111 := join_branches bp000010101011110 bp000010101011111
private noncomputable def vp000010101011101_0 : Blocks := edgeBlocks% "full/vectors/000010101011101-V-0000.bin"
noncomputable def vp000010101011101 : Blocks := vp000010101011101_0
theorem coverp000010101011101 : Covers (-343011639/250000 : ℚ) vp000010101011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101011100_0 : Blocks := edgeBlocks% "full/vectors/000010101011100-V-0000.bin"
noncomputable def vp000010101011100 : Blocks := vp000010101011100_0
theorem coverp000010101011100 : Covers (-342761639/250000 : ℚ) vp000010101011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010101110_0 : Blocks := edgeBlocks% "full/vectors/00001010101110-V-0000.bin"
noncomputable def vp00001010101110 : Blocks := vp00001010101110_0
private theorem bp000010101011100 : Branch 0 (-342761639/500000 : ℚ) vp00001010101110 := by
  apply branch_left_normalized (c:=vp000010101011100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-342761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-342761639/250000 : ℚ) by norm_num]
  exact coverp000010101011100
private noncomputable def ep000010101011101_0 : Blocks := edgeBlocks% "full/vectors/000010101011101-E-0000.bin"
noncomputable def ep000010101011101 : Blocks := ep000010101011101_0
private theorem idp000010101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010101110.list =
    C ((2:ℤ)^49) * horner X vp000010101011101.list + horner X ep000010101011101.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101011101 : Branch 1 (-342761639/500000 : ℚ) vp00001010101110 := by
  apply branch_checked idp000010101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-342761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-343011639/250000 : ℚ) by norm_num]
  exact coverp000010101011101
theorem coverp00001010101110 : Covers (-342761639/500000 : ℚ) vp00001010101110 := join_branches bp000010101011100 bp000010101011101
private noncomputable def vp0000101010111_0 : Blocks := edgeBlocks% "full/vectors/0000101010111-V-0000.bin"
noncomputable def vp0000101010111 : Blocks := vp0000101010111_0
private theorem bp00001010101110 : Branch 0 (-342761639/1000000 : ℚ) vp0000101010111 := by
  apply branch_left_normalized (c:=vp00001010101110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-342761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-342761639/500000 : ℚ) by norm_num]
  exact coverp00001010101110
private noncomputable def ep00001010101111_0 : Blocks := edgeBlocks% "full/vectors/00001010101111-E-0000.bin"
noncomputable def ep00001010101111 : Blocks := ep00001010101111_0
private theorem idp00001010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101010111.list =
    C ((2:ℤ)^77) * horner X vp00001010101111.list + horner X ep00001010101111.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010101111 : Branch 1 (-342761639/1000000 : ℚ) vp0000101010111 := by
  apply branch_checked idp00001010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-342761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-343261639/500000 : ℚ) by norm_num]
  exact coverp00001010101111
theorem coverp0000101010111 : Covers (-342761639/1000000 : ℚ) vp0000101010111 := join_branches bp00001010101110 bp00001010101111
private noncomputable def vp000010101011011_0 : Blocks := edgeBlocks% "full/vectors/000010101011011-V-0000.bin"
noncomputable def vp000010101011011 : Blocks := vp000010101011011_0
theorem coverp000010101011011 : Covers (-342511639/250000 : ℚ) vp000010101011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101011010_0 : Blocks := edgeBlocks% "full/vectors/000010101011010-V-0000.bin"
noncomputable def vp000010101011010 : Blocks := vp000010101011010_0
theorem coverp000010101011010 : Covers (-342261639/250000 : ℚ) vp000010101011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010101101_0 : Blocks := edgeBlocks% "full/vectors/00001010101101-V-0000.bin"
noncomputable def vp00001010101101 : Blocks := vp00001010101101_0
private theorem bp000010101011010 : Branch 0 (-342261639/500000 : ℚ) vp00001010101101 := by
  apply branch_left_normalized (c:=vp000010101011010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-342261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-342261639/250000 : ℚ) by norm_num]
  exact coverp000010101011010
private noncomputable def ep000010101011011_0 : Blocks := edgeBlocks% "full/vectors/000010101011011-E-0000.bin"
noncomputable def ep000010101011011 : Blocks := ep000010101011011_0
private theorem idp000010101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010101101.list =
    C ((2:ℤ)^49) * horner X vp000010101011011.list + horner X ep000010101011011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101011011 : Branch 1 (-342261639/500000 : ℚ) vp00001010101101 := by
  apply branch_checked idp000010101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-342261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-342511639/250000 : ℚ) by norm_num]
  exact coverp000010101011011
theorem coverp00001010101101 : Covers (-342261639/500000 : ℚ) vp00001010101101 := join_branches bp000010101011010 bp000010101011011
private noncomputable def vp000010101011001_0 : Blocks := edgeBlocks% "full/vectors/000010101011001-V-0000.bin"
noncomputable def vp000010101011001 : Blocks := vp000010101011001_0
theorem coverp000010101011001 : Covers (-342011639/250000 : ℚ) vp000010101011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101011000_0 : Blocks := edgeBlocks% "full/vectors/000010101011000-V-0000.bin"
noncomputable def vp000010101011000 : Blocks := vp000010101011000_0
theorem coverp000010101011000 : Covers (-341761639/250000 : ℚ) vp000010101011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010101100_0 : Blocks := edgeBlocks% "full/vectors/00001010101100-V-0000.bin"
noncomputable def vp00001010101100 : Blocks := vp00001010101100_0
private theorem bp000010101011000 : Branch 0 (-341761639/500000 : ℚ) vp00001010101100 := by
  apply branch_left_normalized (c:=vp000010101011000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-341761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-341761639/250000 : ℚ) by norm_num]
  exact coverp000010101011000
private noncomputable def ep000010101011001_0 : Blocks := edgeBlocks% "full/vectors/000010101011001-E-0000.bin"
noncomputable def ep000010101011001 : Blocks := ep000010101011001_0
private theorem idp000010101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010101100.list =
    C ((2:ℤ)^48) * horner X vp000010101011001.list + horner X ep000010101011001.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101011001 : Branch 1 (-341761639/500000 : ℚ) vp00001010101100 := by
  apply branch_checked idp000010101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-341761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-342011639/250000 : ℚ) by norm_num]
  exact coverp000010101011001
theorem coverp00001010101100 : Covers (-341761639/500000 : ℚ) vp00001010101100 := join_branches bp000010101011000 bp000010101011001
private noncomputable def vp0000101010110_0 : Blocks := edgeBlocks% "full/vectors/0000101010110-V-0000.bin"
noncomputable def vp0000101010110 : Blocks := vp0000101010110_0
private theorem bp00001010101100 : Branch 0 (-341761639/1000000 : ℚ) vp0000101010110 := by
  apply branch_left_normalized (c:=vp00001010101100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-341761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-341761639/500000 : ℚ) by norm_num]
  exact coverp00001010101100
private noncomputable def ep00001010101101_0 : Blocks := edgeBlocks% "full/vectors/00001010101101-E-0000.bin"
noncomputable def ep00001010101101 : Blocks := ep00001010101101_0
private theorem idp00001010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101010110.list =
    C ((2:ℤ)^77) * horner X vp00001010101101.list + horner X ep00001010101101.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010101101 : Branch 1 (-341761639/1000000 : ℚ) vp0000101010110 := by
  apply branch_checked idp00001010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-341761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-342261639/500000 : ℚ) by norm_num]
  exact coverp00001010101101
theorem coverp0000101010110 : Covers (-341761639/1000000 : ℚ) vp0000101010110 := join_branches bp00001010101100 bp00001010101101
private noncomputable def vp000010101011_0 : Blocks := edgeBlocks% "full/vectors/000010101011-V-0000.bin"
private noncomputable def vp000010101011_1 : Blocks := edgeBlocks% "full/vectors/000010101011-V-0001.bin"
noncomputable def vp000010101011 : Blocks := (Blocks.join vp000010101011_0 vp000010101011_1)
private theorem bp0000101010110 : Branch 0 (-341761639/2000000 : ℚ) vp000010101011 := by
  apply branch_left_normalized (c:=vp0000101010110) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-341761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-341761639/1000000 : ℚ) by norm_num]
  exact coverp0000101010110
private noncomputable def ep0000101010111_0 : Blocks := edgeBlocks% "full/vectors/0000101010111-E-0000.bin"
private noncomputable def ep0000101010111_1 : Blocks := edgeBlocks% "full/vectors/0000101010111-E-0001.bin"
noncomputable def ep0000101010111 : Blocks := (Blocks.join ep0000101010111_0 ep0000101010111_1)
private theorem idp0000101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010101011.list =
    C ((2:ℤ)^134) * horner X vp0000101010111.list + horner X ep0000101010111.list := by
  exact edge_identity (B := (2:ℤ)^287) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101010111 : Branch 1 (-341761639/2000000 : ℚ) vp000010101011 := by
  apply branch_checked idp0000101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-341761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-342761639/1000000 : ℚ) by norm_num]
  exact coverp0000101010111
theorem coverp000010101011 : Covers (-341761639/2000000 : ℚ) vp000010101011 := join_branches bp0000101010110 bp0000101010111
private noncomputable def vp000010101010111_0 : Blocks := edgeBlocks% "full/vectors/000010101010111-V-0000.bin"
noncomputable def vp000010101010111 : Blocks := vp000010101010111_0
theorem coverp000010101010111 : Covers (-341511639/250000 : ℚ) vp000010101010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101010110_0 : Blocks := edgeBlocks% "full/vectors/000010101010110-V-0000.bin"
noncomputable def vp000010101010110 : Blocks := vp000010101010110_0
theorem coverp000010101010110 : Covers (-341261639/250000 : ℚ) vp000010101010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010101011_0 : Blocks := edgeBlocks% "full/vectors/00001010101011-V-0000.bin"
noncomputable def vp00001010101011 : Blocks := vp00001010101011_0
private theorem bp000010101010110 : Branch 0 (-341261639/500000 : ℚ) vp00001010101011 := by
  apply branch_left_normalized (c:=vp000010101010110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-341261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-341261639/250000 : ℚ) by norm_num]
  exact coverp000010101010110
private noncomputable def ep000010101010111_0 : Blocks := edgeBlocks% "full/vectors/000010101010111-E-0000.bin"
noncomputable def ep000010101010111 : Blocks := ep000010101010111_0
private theorem idp000010101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010101011.list =
    C ((2:ℤ)^48) * horner X vp000010101010111.list + horner X ep000010101010111.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101010111 : Branch 1 (-341261639/500000 : ℚ) vp00001010101011 := by
  apply branch_checked idp000010101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-341261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-341511639/250000 : ℚ) by norm_num]
  exact coverp000010101010111
theorem coverp00001010101011 : Covers (-341261639/500000 : ℚ) vp00001010101011 := join_branches bp000010101010110 bp000010101010111
private noncomputable def vp000010101010101_0 : Blocks := edgeBlocks% "full/vectors/000010101010101-V-0000.bin"
noncomputable def vp000010101010101 : Blocks := vp000010101010101_0
theorem coverp000010101010101 : Covers (-341011639/250000 : ℚ) vp000010101010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101010100_0 : Blocks := edgeBlocks% "full/vectors/000010101010100-V-0000.bin"
noncomputable def vp000010101010100 : Blocks := vp000010101010100_0
theorem coverp000010101010100 : Covers (-340761639/250000 : ℚ) vp000010101010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010101010_0 : Blocks := edgeBlocks% "full/vectors/00001010101010-V-0000.bin"
noncomputable def vp00001010101010 : Blocks := vp00001010101010_0
private theorem bp000010101010100 : Branch 0 (-340761639/500000 : ℚ) vp00001010101010 := by
  apply branch_left_normalized (c:=vp000010101010100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-340761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-340761639/250000 : ℚ) by norm_num]
  exact coverp000010101010100
private noncomputable def ep000010101010101_0 : Blocks := edgeBlocks% "full/vectors/000010101010101-E-0000.bin"
noncomputable def ep000010101010101 : Blocks := ep000010101010101_0
private theorem idp000010101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010101010.list =
    C ((2:ℤ)^49) * horner X vp000010101010101.list + horner X ep000010101010101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101010101 : Branch 1 (-340761639/500000 : ℚ) vp00001010101010 := by
  apply branch_checked idp000010101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-340761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-341011639/250000 : ℚ) by norm_num]
  exact coverp000010101010101
theorem coverp00001010101010 : Covers (-340761639/500000 : ℚ) vp00001010101010 := join_branches bp000010101010100 bp000010101010101
private noncomputable def vp0000101010101_0 : Blocks := edgeBlocks% "full/vectors/0000101010101-V-0000.bin"
noncomputable def vp0000101010101 : Blocks := vp0000101010101_0
private theorem bp00001010101010 : Branch 0 (-340761639/1000000 : ℚ) vp0000101010101 := by
  apply branch_left_normalized (c:=vp00001010101010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-340761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-340761639/500000 : ℚ) by norm_num]
  exact coverp00001010101010
private noncomputable def ep00001010101011_0 : Blocks := edgeBlocks% "full/vectors/00001010101011-E-0000.bin"
noncomputable def ep00001010101011 : Blocks := ep00001010101011_0
private theorem idp00001010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101010101.list =
    C ((2:ℤ)^78) * horner X vp00001010101011.list + horner X ep00001010101011.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010101011 : Branch 1 (-340761639/1000000 : ℚ) vp0000101010101 := by
  apply branch_checked idp00001010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-340761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-341261639/500000 : ℚ) by norm_num]
  exact coverp00001010101011
theorem coverp0000101010101 : Covers (-340761639/1000000 : ℚ) vp0000101010101 := join_branches bp00001010101010 bp00001010101011
private noncomputable def vp000010101010011_0 : Blocks := edgeBlocks% "full/vectors/000010101010011-V-0000.bin"
noncomputable def vp000010101010011 : Blocks := vp000010101010011_0
theorem coverp000010101010011 : Covers (-340511639/250000 : ℚ) vp000010101010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101010010_0 : Blocks := edgeBlocks% "full/vectors/000010101010010-V-0000.bin"
noncomputable def vp000010101010010 : Blocks := vp000010101010010_0
theorem coverp000010101010010 : Covers (-340261639/250000 : ℚ) vp000010101010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010101001_0 : Blocks := edgeBlocks% "full/vectors/00001010101001-V-0000.bin"
noncomputable def vp00001010101001 : Blocks := vp00001010101001_0
private theorem bp000010101010010 : Branch 0 (-340261639/500000 : ℚ) vp00001010101001 := by
  apply branch_left_normalized (c:=vp000010101010010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-340261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-340261639/250000 : ℚ) by norm_num]
  exact coverp000010101010010
private noncomputable def ep000010101010011_0 : Blocks := edgeBlocks% "full/vectors/000010101010011-E-0000.bin"
noncomputable def ep000010101010011 : Blocks := ep000010101010011_0
private theorem idp000010101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010101001.list =
    C ((2:ℤ)^49) * horner X vp000010101010011.list + horner X ep000010101010011.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101010011 : Branch 1 (-340261639/500000 : ℚ) vp00001010101001 := by
  apply branch_checked idp000010101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-340261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-340511639/250000 : ℚ) by norm_num]
  exact coverp000010101010011
theorem coverp00001010101001 : Covers (-340261639/500000 : ℚ) vp00001010101001 := join_branches bp000010101010010 bp000010101010011
private noncomputable def vp000010101010001_0 : Blocks := edgeBlocks% "full/vectors/000010101010001-V-0000.bin"
noncomputable def vp000010101010001 : Blocks := vp000010101010001_0
theorem coverp000010101010001 : Covers (-340011639/250000 : ℚ) vp000010101010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101010000_0 : Blocks := edgeBlocks% "full/vectors/000010101010000-V-0000.bin"
noncomputable def vp000010101010000 : Blocks := vp000010101010000_0
theorem coverp000010101010000 : Covers (-339761639/250000 : ℚ) vp000010101010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010101000_0 : Blocks := edgeBlocks% "full/vectors/00001010101000-V-0000.bin"
noncomputable def vp00001010101000 : Blocks := vp00001010101000_0
private theorem bp000010101010000 : Branch 0 (-339761639/500000 : ℚ) vp00001010101000 := by
  apply branch_left_normalized (c:=vp000010101010000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-339761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-339761639/250000 : ℚ) by norm_num]
  exact coverp000010101010000
private noncomputable def ep000010101010001_0 : Blocks := edgeBlocks% "full/vectors/000010101010001-E-0000.bin"
noncomputable def ep000010101010001 : Blocks := ep000010101010001_0
private theorem idp000010101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010101000.list =
    C ((2:ℤ)^49) * horner X vp000010101010001.list + horner X ep000010101010001.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101010001 : Branch 1 (-339761639/500000 : ℚ) vp00001010101000 := by
  apply branch_checked idp000010101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-339761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-340011639/250000 : ℚ) by norm_num]
  exact coverp000010101010001
theorem coverp00001010101000 : Covers (-339761639/500000 : ℚ) vp00001010101000 := join_branches bp000010101010000 bp000010101010001
private noncomputable def vp0000101010100_0 : Blocks := edgeBlocks% "full/vectors/0000101010100-V-0000.bin"
noncomputable def vp0000101010100 : Blocks := vp0000101010100_0
private theorem bp00001010101000 : Branch 0 (-339761639/1000000 : ℚ) vp0000101010100 := by
  apply branch_left_normalized (c:=vp00001010101000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-339761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-339761639/500000 : ℚ) by norm_num]
  exact coverp00001010101000
private noncomputable def ep00001010101001_0 : Blocks := edgeBlocks% "full/vectors/00001010101001-E-0000.bin"
noncomputable def ep00001010101001 : Blocks := ep00001010101001_0
private theorem idp00001010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101010100.list =
    C ((2:ℤ)^78) * horner X vp00001010101001.list + horner X ep00001010101001.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010101001 : Branch 1 (-339761639/1000000 : ℚ) vp0000101010100 := by
  apply branch_checked idp00001010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-339761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-340261639/500000 : ℚ) by norm_num]
  exact coverp00001010101001
theorem coverp0000101010100 : Covers (-339761639/1000000 : ℚ) vp0000101010100 := join_branches bp00001010101000 bp00001010101001
private noncomputable def vp000010101010_0 : Blocks := edgeBlocks% "full/vectors/000010101010-V-0000.bin"
private noncomputable def vp000010101010_1 : Blocks := edgeBlocks% "full/vectors/000010101010-V-0001.bin"
noncomputable def vp000010101010 : Blocks := (Blocks.join vp000010101010_0 vp000010101010_1)
private theorem bp0000101010100 : Branch 0 (-339761639/2000000 : ℚ) vp000010101010 := by
  apply branch_left_normalized (c:=vp0000101010100) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-339761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-339761639/1000000 : ℚ) by norm_num]
  exact coverp0000101010100
private noncomputable def ep0000101010101_0 : Blocks := edgeBlocks% "full/vectors/0000101010101-E-0000.bin"
private noncomputable def ep0000101010101_1 : Blocks := edgeBlocks% "full/vectors/0000101010101-E-0001.bin"
noncomputable def ep0000101010101 : Blocks := (Blocks.join ep0000101010101_0 ep0000101010101_1)
private theorem idp0000101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010101010.list =
    C ((2:ℤ)^136) * horner X vp0000101010101.list + horner X ep0000101010101.list := by
  exact edge_identity (B := (2:ℤ)^289) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101010101 : Branch 1 (-339761639/2000000 : ℚ) vp000010101010 := by
  apply branch_checked idp0000101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-339761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-340761639/1000000 : ℚ) by norm_num]
  exact coverp0000101010101
theorem coverp000010101010 : Covers (-339761639/2000000 : ℚ) vp000010101010 := join_branches bp0000101010100 bp0000101010101
private noncomputable def vp00001010101_0 : Blocks := edgeBlocks% "full/vectors/00001010101-V-0000.bin"
private noncomputable def vp00001010101_1 : Blocks := edgeBlocks% "full/vectors/00001010101-V-0001.bin"
noncomputable def vp00001010101 : Blocks := (Blocks.join vp00001010101_0 vp00001010101_1)
private theorem bp000010101010 : Branch 0 (-339761639/4000000 : ℚ) vp00001010101 := by
  apply branch_left_normalized (c:=vp000010101010) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-339761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-339761639/2000000 : ℚ) by norm_num]
  exact coverp000010101010
private noncomputable def ep000010101011_0 : Blocks := edgeBlocks% "full/vectors/000010101011-E-0000.bin"
private noncomputable def ep000010101011_1 : Blocks := edgeBlocks% "full/vectors/000010101011-E-0001.bin"
noncomputable def ep000010101011 : Blocks := (Blocks.join ep000010101011_0 ep000010101011_1)
private theorem idp000010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010101.list =
    C ((2:ℤ)^249) * horner X vp000010101011.list + horner X ep000010101011.list := by
  exact edge_identity (B := (2:ℤ)^452) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101011 : Branch 1 (-339761639/4000000 : ℚ) vp00001010101 := by
  apply branch_checked idp000010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-339761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-341761639/2000000 : ℚ) by norm_num]
  exact coverp000010101011
theorem coverp00001010101 : Covers (-339761639/4000000 : ℚ) vp00001010101 := join_branches bp000010101010 bp000010101011
private noncomputable def vp000010101001111_0 : Blocks := edgeBlocks% "full/vectors/000010101001111-V-0000.bin"
noncomputable def vp000010101001111 : Blocks := vp000010101001111_0
theorem coverp000010101001111 : Covers (-339511639/250000 : ℚ) vp000010101001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101001110_0 : Blocks := edgeBlocks% "full/vectors/000010101001110-V-0000.bin"
noncomputable def vp000010101001110 : Blocks := vp000010101001110_0
theorem coverp000010101001110 : Covers (-339261639/250000 : ℚ) vp000010101001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010100111_0 : Blocks := edgeBlocks% "full/vectors/00001010100111-V-0000.bin"
noncomputable def vp00001010100111 : Blocks := vp00001010100111_0
private theorem bp000010101001110 : Branch 0 (-339261639/500000 : ℚ) vp00001010100111 := by
  apply branch_left_normalized (c:=vp000010101001110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-339261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-339261639/250000 : ℚ) by norm_num]
  exact coverp000010101001110
private noncomputable def ep000010101001111_0 : Blocks := edgeBlocks% "full/vectors/000010101001111-E-0000.bin"
noncomputable def ep000010101001111 : Blocks := ep000010101001111_0
private theorem idp000010101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010100111.list =
    C ((2:ℤ)^49) * horner X vp000010101001111.list + horner X ep000010101001111.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101001111 : Branch 1 (-339261639/500000 : ℚ) vp00001010100111 := by
  apply branch_checked idp000010101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-339261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-339511639/250000 : ℚ) by norm_num]
  exact coverp000010101001111
theorem coverp00001010100111 : Covers (-339261639/500000 : ℚ) vp00001010100111 := join_branches bp000010101001110 bp000010101001111
private noncomputable def vp000010101001101_0 : Blocks := edgeBlocks% "full/vectors/000010101001101-V-0000.bin"
noncomputable def vp000010101001101 : Blocks := vp000010101001101_0
theorem coverp000010101001101 : Covers (-339011639/250000 : ℚ) vp000010101001101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101001100_0 : Blocks := edgeBlocks% "full/vectors/000010101001100-V-0000.bin"
noncomputable def vp000010101001100 : Blocks := vp000010101001100_0
theorem coverp000010101001100 : Covers (-338761639/250000 : ℚ) vp000010101001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010100110_0 : Blocks := edgeBlocks% "full/vectors/00001010100110-V-0000.bin"
noncomputable def vp00001010100110 : Blocks := vp00001010100110_0
private theorem bp000010101001100 : Branch 0 (-338761639/500000 : ℚ) vp00001010100110 := by
  apply branch_left_normalized (c:=vp000010101001100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-338761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-338761639/250000 : ℚ) by norm_num]
  exact coverp000010101001100
private noncomputable def ep000010101001101_0 : Blocks := edgeBlocks% "full/vectors/000010101001101-E-0000.bin"
noncomputable def ep000010101001101 : Blocks := ep000010101001101_0
private theorem idp000010101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010100110.list =
    C ((2:ℤ)^49) * horner X vp000010101001101.list + horner X ep000010101001101.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101001101 : Branch 1 (-338761639/500000 : ℚ) vp00001010100110 := by
  apply branch_checked idp000010101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-338761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-339011639/250000 : ℚ) by norm_num]
  exact coverp000010101001101
theorem coverp00001010100110 : Covers (-338761639/500000 : ℚ) vp00001010100110 := join_branches bp000010101001100 bp000010101001101
private noncomputable def vp0000101010011_0 : Blocks := edgeBlocks% "full/vectors/0000101010011-V-0000.bin"
noncomputable def vp0000101010011 : Blocks := vp0000101010011_0
private theorem bp00001010100110 : Branch 0 (-338761639/1000000 : ℚ) vp0000101010011 := by
  apply branch_left_normalized (c:=vp00001010100110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-338761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-338761639/500000 : ℚ) by norm_num]
  exact coverp00001010100110
private noncomputable def ep00001010100111_0 : Blocks := edgeBlocks% "full/vectors/00001010100111-E-0000.bin"
noncomputable def ep00001010100111 : Blocks := ep00001010100111_0
private theorem idp00001010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101010011.list =
    C ((2:ℤ)^78) * horner X vp00001010100111.list + horner X ep00001010100111.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010100111 : Branch 1 (-338761639/1000000 : ℚ) vp0000101010011 := by
  apply branch_checked idp00001010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-338761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-339261639/500000 : ℚ) by norm_num]
  exact coverp00001010100111
theorem coverp0000101010011 : Covers (-338761639/1000000 : ℚ) vp0000101010011 := join_branches bp00001010100110 bp00001010100111
private noncomputable def vp000010101001011_0 : Blocks := edgeBlocks% "full/vectors/000010101001011-V-0000.bin"
noncomputable def vp000010101001011 : Blocks := vp000010101001011_0
theorem coverp000010101001011 : Covers (-338511639/250000 : ℚ) vp000010101001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101001010_0 : Blocks := edgeBlocks% "full/vectors/000010101001010-V-0000.bin"
noncomputable def vp000010101001010 : Blocks := vp000010101001010_0
theorem coverp000010101001010 : Covers (-338261639/250000 : ℚ) vp000010101001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010100101_0 : Blocks := edgeBlocks% "full/vectors/00001010100101-V-0000.bin"
noncomputable def vp00001010100101 : Blocks := vp00001010100101_0
private theorem bp000010101001010 : Branch 0 (-338261639/500000 : ℚ) vp00001010100101 := by
  apply branch_left_normalized (c:=vp000010101001010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-338261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-338261639/250000 : ℚ) by norm_num]
  exact coverp000010101001010
private noncomputable def ep000010101001011_0 : Blocks := edgeBlocks% "full/vectors/000010101001011-E-0000.bin"
noncomputable def ep000010101001011 : Blocks := ep000010101001011_0
private theorem idp000010101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010100101.list =
    C ((2:ℤ)^49) * horner X vp000010101001011.list + horner X ep000010101001011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101001011 : Branch 1 (-338261639/500000 : ℚ) vp00001010100101 := by
  apply branch_checked idp000010101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-338261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-338511639/250000 : ℚ) by norm_num]
  exact coverp000010101001011
theorem coverp00001010100101 : Covers (-338261639/500000 : ℚ) vp00001010100101 := join_branches bp000010101001010 bp000010101001011
private noncomputable def vp000010101001001_0 : Blocks := edgeBlocks% "full/vectors/000010101001001-V-0000.bin"
noncomputable def vp000010101001001 : Blocks := vp000010101001001_0
theorem coverp000010101001001 : Covers (-338011639/250000 : ℚ) vp000010101001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101001000_0 : Blocks := edgeBlocks% "full/vectors/000010101001000-V-0000.bin"
noncomputable def vp000010101001000 : Blocks := vp000010101001000_0
theorem coverp000010101001000 : Covers (-337761639/250000 : ℚ) vp000010101001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010100100_0 : Blocks := edgeBlocks% "full/vectors/00001010100100-V-0000.bin"
noncomputable def vp00001010100100 : Blocks := vp00001010100100_0
private theorem bp000010101001000 : Branch 0 (-337761639/500000 : ℚ) vp00001010100100 := by
  apply branch_left_normalized (c:=vp000010101001000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-337761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-337761639/250000 : ℚ) by norm_num]
  exact coverp000010101001000
private noncomputable def ep000010101001001_0 : Blocks := edgeBlocks% "full/vectors/000010101001001-E-0000.bin"
noncomputable def ep000010101001001 : Blocks := ep000010101001001_0
private theorem idp000010101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010100100.list =
    C ((2:ℤ)^49) * horner X vp000010101001001.list + horner X ep000010101001001.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101001001 : Branch 1 (-337761639/500000 : ℚ) vp00001010100100 := by
  apply branch_checked idp000010101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-337761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-338011639/250000 : ℚ) by norm_num]
  exact coverp000010101001001
theorem coverp00001010100100 : Covers (-337761639/500000 : ℚ) vp00001010100100 := join_branches bp000010101001000 bp000010101001001
private noncomputable def vp0000101010010_0 : Blocks := edgeBlocks% "full/vectors/0000101010010-V-0000.bin"
noncomputable def vp0000101010010 : Blocks := vp0000101010010_0
private theorem bp00001010100100 : Branch 0 (-337761639/1000000 : ℚ) vp0000101010010 := by
  apply branch_left_normalized (c:=vp00001010100100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-337761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-337761639/500000 : ℚ) by norm_num]
  exact coverp00001010100100
private noncomputable def ep00001010100101_0 : Blocks := edgeBlocks% "full/vectors/00001010100101-E-0000.bin"
noncomputable def ep00001010100101 : Blocks := ep00001010100101_0
private theorem idp00001010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101010010.list =
    C ((2:ℤ)^78) * horner X vp00001010100101.list + horner X ep00001010100101.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010100101 : Branch 1 (-337761639/1000000 : ℚ) vp0000101010010 := by
  apply branch_checked idp00001010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-337761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-338261639/500000 : ℚ) by norm_num]
  exact coverp00001010100101
theorem coverp0000101010010 : Covers (-337761639/1000000 : ℚ) vp0000101010010 := join_branches bp00001010100100 bp00001010100101
private noncomputable def vp000010101001_0 : Blocks := edgeBlocks% "full/vectors/000010101001-V-0000.bin"
private noncomputable def vp000010101001_1 : Blocks := edgeBlocks% "full/vectors/000010101001-V-0001.bin"
noncomputable def vp000010101001 : Blocks := (Blocks.join vp000010101001_0 vp000010101001_1)
private theorem bp0000101010010 : Branch 0 (-337761639/2000000 : ℚ) vp000010101001 := by
  apply branch_left_normalized (c:=vp0000101010010) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-337761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-337761639/1000000 : ℚ) by norm_num]
  exact coverp0000101010010
private noncomputable def ep0000101010011_0 : Blocks := edgeBlocks% "full/vectors/0000101010011-E-0000.bin"
private noncomputable def ep0000101010011_1 : Blocks := edgeBlocks% "full/vectors/0000101010011-E-0001.bin"
noncomputable def ep0000101010011 : Blocks := (Blocks.join ep0000101010011_0 ep0000101010011_1)
private theorem idp0000101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010101001.list =
    C ((2:ℤ)^136) * horner X vp0000101010011.list + horner X ep0000101010011.list := by
  exact edge_identity (B := (2:ℤ)^289) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101010011 : Branch 1 (-337761639/2000000 : ℚ) vp000010101001 := by
  apply branch_checked idp0000101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-337761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-338761639/1000000 : ℚ) by norm_num]
  exact coverp0000101010011
theorem coverp000010101001 : Covers (-337761639/2000000 : ℚ) vp000010101001 := join_branches bp0000101010010 bp0000101010011
private noncomputable def vp000010101000111_0 : Blocks := edgeBlocks% "full/vectors/000010101000111-V-0000.bin"
noncomputable def vp000010101000111 : Blocks := vp000010101000111_0
theorem coverp000010101000111 : Covers (-337511639/250000 : ℚ) vp000010101000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101000110_0 : Blocks := edgeBlocks% "full/vectors/000010101000110-V-0000.bin"
noncomputable def vp000010101000110 : Blocks := vp000010101000110_0
theorem coverp000010101000110 : Covers (-337261639/250000 : ℚ) vp000010101000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010100011_0 : Blocks := edgeBlocks% "full/vectors/00001010100011-V-0000.bin"
noncomputable def vp00001010100011 : Blocks := vp00001010100011_0
private theorem bp000010101000110 : Branch 0 (-337261639/500000 : ℚ) vp00001010100011 := by
  apply branch_left_normalized (c:=vp000010101000110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-337261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-337261639/250000 : ℚ) by norm_num]
  exact coverp000010101000110
private noncomputable def ep000010101000111_0 : Blocks := edgeBlocks% "full/vectors/000010101000111-E-0000.bin"
noncomputable def ep000010101000111 : Blocks := ep000010101000111_0
private theorem idp000010101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010100011.list =
    C ((2:ℤ)^48) * horner X vp000010101000111.list + horner X ep000010101000111.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101000111 : Branch 1 (-337261639/500000 : ℚ) vp00001010100011 := by
  apply branch_checked idp000010101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-337261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-337511639/250000 : ℚ) by norm_num]
  exact coverp000010101000111
theorem coverp00001010100011 : Covers (-337261639/500000 : ℚ) vp00001010100011 := join_branches bp000010101000110 bp000010101000111
private noncomputable def vp000010101000101_0 : Blocks := edgeBlocks% "full/vectors/000010101000101-V-0000.bin"
noncomputable def vp000010101000101 : Blocks := vp000010101000101_0
theorem coverp000010101000101 : Covers (-337011639/250000 : ℚ) vp000010101000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101000100_0 : Blocks := edgeBlocks% "full/vectors/000010101000100-V-0000.bin"
noncomputable def vp000010101000100 : Blocks := vp000010101000100_0
theorem coverp000010101000100 : Covers (-336761639/250000 : ℚ) vp000010101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010100010_0 : Blocks := edgeBlocks% "full/vectors/00001010100010-V-0000.bin"
noncomputable def vp00001010100010 : Blocks := vp00001010100010_0
private theorem bp000010101000100 : Branch 0 (-336761639/500000 : ℚ) vp00001010100010 := by
  apply branch_left_normalized (c:=vp000010101000100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-336761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-336761639/250000 : ℚ) by norm_num]
  exact coverp000010101000100
private noncomputable def ep000010101000101_0 : Blocks := edgeBlocks% "full/vectors/000010101000101-E-0000.bin"
noncomputable def ep000010101000101 : Blocks := ep000010101000101_0
private theorem idp000010101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010100010.list =
    C ((2:ℤ)^47) * horner X vp000010101000101.list + horner X ep000010101000101.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101000101 : Branch 1 (-336761639/500000 : ℚ) vp00001010100010 := by
  apply branch_checked idp000010101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-336761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-337011639/250000 : ℚ) by norm_num]
  exact coverp000010101000101
theorem coverp00001010100010 : Covers (-336761639/500000 : ℚ) vp00001010100010 := join_branches bp000010101000100 bp000010101000101
private noncomputable def vp0000101010001_0 : Blocks := edgeBlocks% "full/vectors/0000101010001-V-0000.bin"
noncomputable def vp0000101010001 : Blocks := vp0000101010001_0
private theorem bp00001010100010 : Branch 0 (-336761639/1000000 : ℚ) vp0000101010001 := by
  apply branch_left_normalized (c:=vp00001010100010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-336761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-336761639/500000 : ℚ) by norm_num]
  exact coverp00001010100010
private noncomputable def ep00001010100011_0 : Blocks := edgeBlocks% "full/vectors/00001010100011-E-0000.bin"
noncomputable def ep00001010100011 : Blocks := ep00001010100011_0
private theorem idp00001010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101010001.list =
    C ((2:ℤ)^78) * horner X vp00001010100011.list + horner X ep00001010100011.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010100011 : Branch 1 (-336761639/1000000 : ℚ) vp0000101010001 := by
  apply branch_checked idp00001010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-336761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-337261639/500000 : ℚ) by norm_num]
  exact coverp00001010100011
theorem coverp0000101010001 : Covers (-336761639/1000000 : ℚ) vp0000101010001 := join_branches bp00001010100010 bp00001010100011
private noncomputable def vp000010101000011_0 : Blocks := edgeBlocks% "full/vectors/000010101000011-V-0000.bin"
noncomputable def vp000010101000011 : Blocks := vp000010101000011_0
theorem coverp000010101000011 : Covers (-336511639/250000 : ℚ) vp000010101000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101000010_0 : Blocks := edgeBlocks% "full/vectors/000010101000010-V-0000.bin"
noncomputable def vp000010101000010 : Blocks := vp000010101000010_0
theorem coverp000010101000010 : Covers (-336261639/250000 : ℚ) vp000010101000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010100001_0 : Blocks := edgeBlocks% "full/vectors/00001010100001-V-0000.bin"
noncomputable def vp00001010100001 : Blocks := vp00001010100001_0
private theorem bp000010101000010 : Branch 0 (-336261639/500000 : ℚ) vp00001010100001 := by
  apply branch_left_normalized (c:=vp000010101000010) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-336261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-336261639/250000 : ℚ) by norm_num]
  exact coverp000010101000010
private noncomputable def ep000010101000011_0 : Blocks := edgeBlocks% "full/vectors/000010101000011-E-0000.bin"
noncomputable def ep000010101000011 : Blocks := ep000010101000011_0
private theorem idp000010101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010100001.list =
    C ((2:ℤ)^48) * horner X vp000010101000011.list + horner X ep000010101000011.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101000011 : Branch 1 (-336261639/500000 : ℚ) vp00001010100001 := by
  apply branch_checked idp000010101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-336261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-336511639/250000 : ℚ) by norm_num]
  exact coverp000010101000011
theorem coverp00001010100001 : Covers (-336261639/500000 : ℚ) vp00001010100001 := join_branches bp000010101000010 bp000010101000011
private noncomputable def vp000010101000001_0 : Blocks := edgeBlocks% "full/vectors/000010101000001-V-0000.bin"
noncomputable def vp000010101000001 : Blocks := vp000010101000001_0
theorem coverp000010101000001 : Covers (-336011639/250000 : ℚ) vp000010101000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000010101000000_0 : Blocks := edgeBlocks% "full/vectors/000010101000000-V-0000.bin"
noncomputable def vp000010101000000 : Blocks := vp000010101000000_0
theorem coverp000010101000000 : Covers (-335761639/250000 : ℚ) vp000010101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00001010100000_0 : Blocks := edgeBlocks% "full/vectors/00001010100000-V-0000.bin"
noncomputable def vp00001010100000 : Blocks := vp00001010100000_0
private theorem bp000010101000000 : Branch 0 (-335761639/500000 : ℚ) vp00001010100000 := by
  apply branch_left_normalized (c:=vp000010101000000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-335761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-335761639/250000 : ℚ) by norm_num]
  exact coverp000010101000000
private noncomputable def ep000010101000001_0 : Blocks := edgeBlocks% "full/vectors/000010101000001-E-0000.bin"
noncomputable def ep000010101000001 : Blocks := ep000010101000001_0
private theorem idp000010101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010100000.list =
    C ((2:ℤ)^48) * horner X vp000010101000001.list + horner X ep000010101000001.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101000001 : Branch 1 (-335761639/500000 : ℚ) vp00001010100000 := by
  apply branch_checked idp000010101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-335761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-336011639/250000 : ℚ) by norm_num]
  exact coverp000010101000001
theorem coverp00001010100000 : Covers (-335761639/500000 : ℚ) vp00001010100000 := join_branches bp000010101000000 bp000010101000001
private noncomputable def vp0000101010000_0 : Blocks := edgeBlocks% "full/vectors/0000101010000-V-0000.bin"
noncomputable def vp0000101010000 : Blocks := vp0000101010000_0
private theorem bp00001010100000 : Branch 0 (-335761639/1000000 : ℚ) vp0000101010000 := by
  apply branch_left_normalized (c:=vp00001010100000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-335761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-335761639/500000 : ℚ) by norm_num]
  exact coverp00001010100000
private noncomputable def ep00001010100001_0 : Blocks := edgeBlocks% "full/vectors/00001010100001-E-0000.bin"
noncomputable def ep00001010100001 : Blocks := ep00001010100001_0
private theorem idp00001010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101010000.list =
    C ((2:ℤ)^78) * horner X vp00001010100001.list + horner X ep00001010100001.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010100001 : Branch 1 (-335761639/1000000 : ℚ) vp0000101010000 := by
  apply branch_checked idp00001010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-335761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-336261639/500000 : ℚ) by norm_num]
  exact coverp00001010100001
theorem coverp0000101010000 : Covers (-335761639/1000000 : ℚ) vp0000101010000 := join_branches bp00001010100000 bp00001010100001
private noncomputable def vp000010101000_0 : Blocks := edgeBlocks% "full/vectors/000010101000-V-0000.bin"
private noncomputable def vp000010101000_1 : Blocks := edgeBlocks% "full/vectors/000010101000-V-0001.bin"
noncomputable def vp000010101000 : Blocks := (Blocks.join vp000010101000_0 vp000010101000_1)
private theorem bp0000101010000 : Branch 0 (-335761639/2000000 : ℚ) vp000010101000 := by
  apply branch_left_normalized (c:=vp0000101010000) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-335761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-335761639/1000000 : ℚ) by norm_num]
  exact coverp0000101010000
private noncomputable def ep0000101010001_0 : Blocks := edgeBlocks% "full/vectors/0000101010001-E-0000.bin"
private noncomputable def ep0000101010001_1 : Blocks := edgeBlocks% "full/vectors/0000101010001-E-0001.bin"
noncomputable def ep0000101010001 : Blocks := (Blocks.join ep0000101010001_0 ep0000101010001_1)
private theorem idp0000101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010101000.list =
    C ((2:ℤ)^136) * horner X vp0000101010001.list + horner X ep0000101010001.list := by
  exact edge_identity (B := (2:ℤ)^289) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101010001 : Branch 1 (-335761639/2000000 : ℚ) vp000010101000 := by
  apply branch_checked idp0000101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-335761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-336761639/1000000 : ℚ) by norm_num]
  exact coverp0000101010001
theorem coverp000010101000 : Covers (-335761639/2000000 : ℚ) vp000010101000 := join_branches bp0000101010000 bp0000101010001
private noncomputable def vp00001010100_0 : Blocks := edgeBlocks% "full/vectors/00001010100-V-0000.bin"
private noncomputable def vp00001010100_1 : Blocks := edgeBlocks% "full/vectors/00001010100-V-0001.bin"
noncomputable def vp00001010100 : Blocks := (Blocks.join vp00001010100_0 vp00001010100_1)
private theorem bp000010101000 : Branch 0 (-335761639/4000000 : ℚ) vp00001010100 := by
  apply branch_left_normalized (c:=vp000010101000) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-335761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-335761639/2000000 : ℚ) by norm_num]
  exact coverp000010101000
private noncomputable def ep000010101001_0 : Blocks := edgeBlocks% "full/vectors/000010101001-E-0000.bin"
private noncomputable def ep000010101001_1 : Blocks := edgeBlocks% "full/vectors/000010101001-E-0001.bin"
noncomputable def ep000010101001 : Blocks := (Blocks.join ep000010101001_0 ep000010101001_1)
private theorem idp000010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001010100.list =
    C ((2:ℤ)^249) * horner X vp000010101001.list + horner X ep000010101001.list := by
  exact edge_identity (B := (2:ℤ)^454) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010101001 : Branch 1 (-335761639/4000000 : ℚ) vp00001010100 := by
  apply branch_checked idp000010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-335761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-337761639/2000000 : ℚ) by norm_num]
  exact coverp000010101001
theorem coverp00001010100 : Covers (-335761639/4000000 : ℚ) vp00001010100 := join_branches bp000010101000 bp000010101001
private noncomputable def vp0000101010_0 : Blocks := edgeBlocks% "full/vectors/0000101010-V-0000.bin"
private noncomputable def vp0000101010_1 : Blocks := edgeBlocks% "full/vectors/0000101010-V-0001.bin"
private noncomputable def vp0000101010_2 : Blocks := edgeBlocks% "full/vectors/0000101010-V-0002.bin"
private noncomputable def vp0000101010_3 : Blocks := edgeBlocks% "full/vectors/0000101010-V-0003.bin"
noncomputable def vp0000101010 : Blocks := (Blocks.join (Blocks.join vp0000101010_0 vp0000101010_1) (Blocks.join vp0000101010_2 vp0000101010_3))
private theorem bp00001010100 : Branch 0 (-335761639/8000000 : ℚ) vp0000101010 := by
  apply branch_left_normalized (c:=vp00001010100) (k:=0) (m:=237) (by decide +kernel)
  rw [show 2*(-335761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-335761639/4000000 : ℚ) by norm_num]
  exact coverp00001010100
private noncomputable def ep00001010101_0 : Blocks := edgeBlocks% "full/vectors/00001010101-E-0000.bin"
private noncomputable def ep00001010101_1 : Blocks := edgeBlocks% "full/vectors/00001010101-E-0001.bin"
private noncomputable def ep00001010101_2 : Blocks := edgeBlocks% "full/vectors/00001010101-E-0002.bin"
private noncomputable def ep00001010101_3 : Blocks := edgeBlocks% "full/vectors/00001010101-E-0003.bin"
noncomputable def ep00001010101 : Blocks := (Blocks.join (Blocks.join ep00001010101_0 ep00001010101_1) (Blocks.join ep00001010101_2 ep00001010101_3))
private theorem idp00001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000101010.list =
    C ((2:ℤ)^473) * horner X vp00001010101.list + horner X ep00001010101.list := by
  exact edge_identity (B := (2:ℤ)^780) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001010101 : Branch 1 (-335761639/8000000 : ℚ) vp0000101010 := by
  apply branch_checked idp00001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-335761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-339761639/4000000 : ℚ) by norm_num]
  exact coverp00001010101
theorem coverp0000101010 : Covers (-335761639/8000000 : ℚ) vp0000101010 := join_branches bp00001010100 bp00001010101
private noncomputable def vp000010101_0 : Blocks := edgeBlocks% "full/vectors/000010101-V-0000.bin"
private noncomputable def vp000010101_1 : Blocks := edgeBlocks% "full/vectors/000010101-V-0001.bin"
private noncomputable def vp000010101_2 : Blocks := edgeBlocks% "full/vectors/000010101-V-0002.bin"
private noncomputable def vp000010101_3 : Blocks := edgeBlocks% "full/vectors/000010101-V-0003.bin"
private noncomputable def vp000010101_4 : Blocks := edgeBlocks% "full/vectors/000010101-V-0004.bin"
private noncomputable def vp000010101_5 : Blocks := edgeBlocks% "full/vectors/000010101-V-0005.bin"
private noncomputable def vp000010101_6 : Blocks := edgeBlocks% "full/vectors/000010101-V-0006.bin"
noncomputable def vp000010101 : Blocks := (Blocks.join (Blocks.join vp000010101_0 (Blocks.join vp000010101_1 vp000010101_2)) (Blocks.join (Blocks.join vp000010101_3 vp000010101_4) (Blocks.join vp000010101_5 vp000010101_6)))
private theorem bp0000101010 : Branch 0 (-335761639/16000000 : ℚ) vp000010101 := by
  apply branch_left_normalized (c:=vp0000101010) (k:=0) (m:=449) (by decide +kernel)
  rw [show 2*(-335761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-335761639/8000000 : ℚ) by norm_num]
  exact coverp0000101010
private noncomputable def ep0000101011_0 : Blocks := edgeBlocks% "full/vectors/0000101011-E-0000.bin"
private noncomputable def ep0000101011_1 : Blocks := edgeBlocks% "full/vectors/0000101011-E-0001.bin"
private noncomputable def ep0000101011_2 : Blocks := edgeBlocks% "full/vectors/0000101011-E-0002.bin"
private noncomputable def ep0000101011_3 : Blocks := edgeBlocks% "full/vectors/0000101011-E-0003.bin"
private noncomputable def ep0000101011_4 : Blocks := edgeBlocks% "full/vectors/0000101011-E-0004.bin"
private noncomputable def ep0000101011_5 : Blocks := edgeBlocks% "full/vectors/0000101011-E-0005.bin"
private noncomputable def ep0000101011_6 : Blocks := edgeBlocks% "full/vectors/0000101011-E-0006.bin"
noncomputable def ep0000101011 : Blocks := (Blocks.join (Blocks.join ep0000101011_0 (Blocks.join ep0000101011_1 ep0000101011_2)) (Blocks.join (Blocks.join ep0000101011_3 ep0000101011_4) (Blocks.join ep0000101011_5 ep0000101011_6)))
private theorem idp0000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010101.list =
    C ((2:ℤ)^918) * horner X vp0000101011.list + horner X ep0000101011.list := by
  exact edge_identity (B := (2:ℤ)^1428) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000101011 : Branch 1 (-335761639/16000000 : ℚ) vp000010101 := by
  apply branch_checked idp0000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-335761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-343761639/8000000 : ℚ) by norm_num]
  exact coverp0000101011
theorem coverp000010101 : Covers (-335761639/16000000 : ℚ) vp000010101 := join_branches bp0000101010 bp0000101011
end NextProof.EdgeFull

