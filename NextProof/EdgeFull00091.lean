import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0010101111111_0 : Blocks := edgeBlocks% "full/vectors/0010101111111-V-0000.bin"
noncomputable def vp0010101111111 : Blocks := vp0010101111111_0
theorem coverp0010101111111 : Covers (-1406761639/1000000 : ℚ) vp0010101111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101111110_0 : Blocks := edgeBlocks% "full/vectors/0010101111110-V-0000.bin"
noncomputable def vp0010101111110 : Blocks := vp0010101111110_0
theorem coverp0010101111110 : Covers (-1405761639/1000000 : ℚ) vp0010101111110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010111111_0 : Blocks := edgeBlocks% "full/vectors/001010111111-V-0000.bin"
noncomputable def vp001010111111 : Blocks := vp001010111111_0
private theorem bp0010101111110 : Branch 0 (-1405761639/2000000 : ℚ) vp001010111111 := by
  apply branch_left_normalized (c:=vp0010101111110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1405761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1405761639/1000000 : ℚ) by norm_num]
  exact coverp0010101111110
private noncomputable def ep0010101111111_0 : Blocks := edgeBlocks% "full/vectors/0010101111111-E-0000.bin"
noncomputable def ep0010101111111 : Blocks := ep0010101111111_0
private theorem idp0010101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010111111.list =
    C ((2:ℤ)^80) * horner X vp0010101111111.list + horner X ep0010101111111.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101111111 : Branch 1 (-1405761639/2000000 : ℚ) vp001010111111 := by
  apply branch_checked idp0010101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1405761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1406761639/1000000 : ℚ) by norm_num]
  exact coverp0010101111111
theorem coverp001010111111 : Covers (-1405761639/2000000 : ℚ) vp001010111111 := join_branches bp0010101111110 bp0010101111111
private noncomputable def vp0010101111101_0 : Blocks := edgeBlocks% "full/vectors/0010101111101-V-0000.bin"
noncomputable def vp0010101111101 : Blocks := vp0010101111101_0
theorem coverp0010101111101 : Covers (-1404761639/1000000 : ℚ) vp0010101111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101111100_0 : Blocks := edgeBlocks% "full/vectors/0010101111100-V-0000.bin"
noncomputable def vp0010101111100 : Blocks := vp0010101111100_0
theorem coverp0010101111100 : Covers (-1403761639/1000000 : ℚ) vp0010101111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010111110_0 : Blocks := edgeBlocks% "full/vectors/001010111110-V-0000.bin"
noncomputable def vp001010111110 : Blocks := vp001010111110_0
private theorem bp0010101111100 : Branch 0 (-1403761639/2000000 : ℚ) vp001010111110 := by
  apply branch_left_normalized (c:=vp0010101111100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1403761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1403761639/1000000 : ℚ) by norm_num]
  exact coverp0010101111100
private noncomputable def ep0010101111101_0 : Blocks := edgeBlocks% "full/vectors/0010101111101-E-0000.bin"
noncomputable def ep0010101111101 : Blocks := ep0010101111101_0
private theorem idp0010101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010111110.list =
    C ((2:ℤ)^79) * horner X vp0010101111101.list + horner X ep0010101111101.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101111101 : Branch 1 (-1403761639/2000000 : ℚ) vp001010111110 := by
  apply branch_checked idp0010101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1403761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1404761639/1000000 : ℚ) by norm_num]
  exact coverp0010101111101
theorem coverp001010111110 : Covers (-1403761639/2000000 : ℚ) vp001010111110 := join_branches bp0010101111100 bp0010101111101
private noncomputable def vp00101011111_0 : Blocks := edgeBlocks% "full/vectors/00101011111-V-0000.bin"
noncomputable def vp00101011111 : Blocks := vp00101011111_0
private theorem bp001010111110 : Branch 0 (-1403761639/4000000 : ℚ) vp00101011111 := by
  apply branch_left_normalized (c:=vp001010111110) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-1403761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1403761639/2000000 : ℚ) by norm_num]
  exact coverp001010111110
private noncomputable def ep001010111111_0 : Blocks := edgeBlocks% "full/vectors/001010111111-E-0000.bin"
noncomputable def ep001010111111 : Blocks := ep001010111111_0
private theorem idp001010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101011111.list =
    C ((2:ℤ)^137) * horner X vp001010111111.list + horner X ep001010111111.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010111111 : Branch 1 (-1403761639/4000000 : ℚ) vp00101011111 := by
  apply branch_checked idp001010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1403761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1405761639/2000000 : ℚ) by norm_num]
  exact coverp001010111111
theorem coverp00101011111 : Covers (-1403761639/4000000 : ℚ) vp00101011111 := join_branches bp001010111110 bp001010111111
private noncomputable def vp0010101111011_0 : Blocks := edgeBlocks% "full/vectors/0010101111011-V-0000.bin"
noncomputable def vp0010101111011 : Blocks := vp0010101111011_0
theorem coverp0010101111011 : Covers (-1402761639/1000000 : ℚ) vp0010101111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101111010_0 : Blocks := edgeBlocks% "full/vectors/0010101111010-V-0000.bin"
noncomputable def vp0010101111010 : Blocks := vp0010101111010_0
theorem coverp0010101111010 : Covers (-1401761639/1000000 : ℚ) vp0010101111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010111101_0 : Blocks := edgeBlocks% "full/vectors/001010111101-V-0000.bin"
noncomputable def vp001010111101 : Blocks := vp001010111101_0
private theorem bp0010101111010 : Branch 0 (-1401761639/2000000 : ℚ) vp001010111101 := by
  apply branch_left_normalized (c:=vp0010101111010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1401761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1401761639/1000000 : ℚ) by norm_num]
  exact coverp0010101111010
private noncomputable def ep0010101111011_0 : Blocks := edgeBlocks% "full/vectors/0010101111011-E-0000.bin"
noncomputable def ep0010101111011 : Blocks := ep0010101111011_0
private theorem idp0010101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010111101.list =
    C ((2:ℤ)^79) * horner X vp0010101111011.list + horner X ep0010101111011.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101111011 : Branch 1 (-1401761639/2000000 : ℚ) vp001010111101 := by
  apply branch_checked idp0010101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1401761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1402761639/1000000 : ℚ) by norm_num]
  exact coverp0010101111011
theorem coverp001010111101 : Covers (-1401761639/2000000 : ℚ) vp001010111101 := join_branches bp0010101111010 bp0010101111011
private noncomputable def vp0010101111001_0 : Blocks := edgeBlocks% "full/vectors/0010101111001-V-0000.bin"
noncomputable def vp0010101111001 : Blocks := vp0010101111001_0
theorem coverp0010101111001 : Covers (-1400761639/1000000 : ℚ) vp0010101111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101111000_0 : Blocks := edgeBlocks% "full/vectors/0010101111000-V-0000.bin"
noncomputable def vp0010101111000 : Blocks := vp0010101111000_0
theorem coverp0010101111000 : Covers (-1399761639/1000000 : ℚ) vp0010101111000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010111100_0 : Blocks := edgeBlocks% "full/vectors/001010111100-V-0000.bin"
noncomputable def vp001010111100 : Blocks := vp001010111100_0
private theorem bp0010101111000 : Branch 0 (-1399761639/2000000 : ℚ) vp001010111100 := by
  apply branch_left_normalized (c:=vp0010101111000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1399761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1399761639/1000000 : ℚ) by norm_num]
  exact coverp0010101111000
private noncomputable def ep0010101111001_0 : Blocks := edgeBlocks% "full/vectors/0010101111001-E-0000.bin"
noncomputable def ep0010101111001 : Blocks := ep0010101111001_0
private theorem idp0010101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010111100.list =
    C ((2:ℤ)^78) * horner X vp0010101111001.list + horner X ep0010101111001.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101111001 : Branch 1 (-1399761639/2000000 : ℚ) vp001010111100 := by
  apply branch_checked idp0010101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1399761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1400761639/1000000 : ℚ) by norm_num]
  exact coverp0010101111001
theorem coverp001010111100 : Covers (-1399761639/2000000 : ℚ) vp001010111100 := join_branches bp0010101111000 bp0010101111001
private noncomputable def vp00101011110_0 : Blocks := edgeBlocks% "full/vectors/00101011110-V-0000.bin"
noncomputable def vp00101011110 : Blocks := vp00101011110_0
private theorem bp001010111100 : Branch 0 (-1399761639/4000000 : ℚ) vp00101011110 := by
  apply branch_left_normalized (c:=vp001010111100) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-1399761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1399761639/2000000 : ℚ) by norm_num]
  exact coverp001010111100
private noncomputable def ep001010111101_0 : Blocks := edgeBlocks% "full/vectors/001010111101-E-0000.bin"
noncomputable def ep001010111101 : Blocks := ep001010111101_0
private theorem idp001010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101011110.list =
    C ((2:ℤ)^137) * horner X vp001010111101.list + horner X ep001010111101.list := by
  exact edge_identity (B := (2:ℤ)^281) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010111101 : Branch 1 (-1399761639/4000000 : ℚ) vp00101011110 := by
  apply branch_checked idp001010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1399761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1401761639/2000000 : ℚ) by norm_num]
  exact coverp001010111101
theorem coverp00101011110 : Covers (-1399761639/4000000 : ℚ) vp00101011110 := join_branches bp001010111100 bp001010111101
private noncomputable def vp0010101111_0 : Blocks := edgeBlocks% "full/vectors/0010101111-V-0000.bin"
private noncomputable def vp0010101111_1 : Blocks := edgeBlocks% "full/vectors/0010101111-V-0001.bin"
noncomputable def vp0010101111 : Blocks := (Blocks.join vp0010101111_0 vp0010101111_1)
private theorem bp00101011110 : Branch 0 (-1399761639/8000000 : ℚ) vp0010101111 := by
  apply branch_left_normalized (c:=vp00101011110) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-1399761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1399761639/4000000 : ℚ) by norm_num]
  exact coverp00101011110
private noncomputable def ep00101011111_0 : Blocks := edgeBlocks% "full/vectors/00101011111-E-0000.bin"
private noncomputable def ep00101011111_1 : Blocks := edgeBlocks% "full/vectors/00101011111-E-0001.bin"
noncomputable def ep00101011111 : Blocks := (Blocks.join ep00101011111_0 ep00101011111_1)
private theorem idp00101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010101111.list =
    C ((2:ℤ)^254) * horner X vp00101011111.list + horner X ep00101011111.list := by
  exact edge_identity (B := (2:ℤ)^443) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101011111 : Branch 1 (-1399761639/8000000 : ℚ) vp0010101111 := by
  apply branch_checked idp00101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1399761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1403761639/4000000 : ℚ) by norm_num]
  exact coverp00101011111
theorem coverp0010101111 : Covers (-1399761639/8000000 : ℚ) vp0010101111 := join_branches bp00101011110 bp00101011111
private noncomputable def vp0010101110111_0 : Blocks := edgeBlocks% "full/vectors/0010101110111-V-0000.bin"
noncomputable def vp0010101110111 : Blocks := vp0010101110111_0
theorem coverp0010101110111 : Covers (-1398761639/1000000 : ℚ) vp0010101110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101110110_0 : Blocks := edgeBlocks% "full/vectors/0010101110110-V-0000.bin"
noncomputable def vp0010101110110 : Blocks := vp0010101110110_0
theorem coverp0010101110110 : Covers (-1397761639/1000000 : ℚ) vp0010101110110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010111011_0 : Blocks := edgeBlocks% "full/vectors/001010111011-V-0000.bin"
noncomputable def vp001010111011 : Blocks := vp001010111011_0
private theorem bp0010101110110 : Branch 0 (-1397761639/2000000 : ℚ) vp001010111011 := by
  apply branch_left_normalized (c:=vp0010101110110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1397761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1397761639/1000000 : ℚ) by norm_num]
  exact coverp0010101110110
private noncomputable def ep0010101110111_0 : Blocks := edgeBlocks% "full/vectors/0010101110111-E-0000.bin"
noncomputable def ep0010101110111 : Blocks := ep0010101110111_0
private theorem idp0010101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010111011.list =
    C ((2:ℤ)^79) * horner X vp0010101110111.list + horner X ep0010101110111.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101110111 : Branch 1 (-1397761639/2000000 : ℚ) vp001010111011 := by
  apply branch_checked idp0010101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1397761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1398761639/1000000 : ℚ) by norm_num]
  exact coverp0010101110111
theorem coverp001010111011 : Covers (-1397761639/2000000 : ℚ) vp001010111011 := join_branches bp0010101110110 bp0010101110111
private noncomputable def vp0010101110101_0 : Blocks := edgeBlocks% "full/vectors/0010101110101-V-0000.bin"
noncomputable def vp0010101110101 : Blocks := vp0010101110101_0
theorem coverp0010101110101 : Covers (-1396761639/1000000 : ℚ) vp0010101110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101110100_0 : Blocks := edgeBlocks% "full/vectors/0010101110100-V-0000.bin"
noncomputable def vp0010101110100 : Blocks := vp0010101110100_0
theorem coverp0010101110100 : Covers (-1395761639/1000000 : ℚ) vp0010101110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010111010_0 : Blocks := edgeBlocks% "full/vectors/001010111010-V-0000.bin"
noncomputable def vp001010111010 : Blocks := vp001010111010_0
private theorem bp0010101110100 : Branch 0 (-1395761639/2000000 : ℚ) vp001010111010 := by
  apply branch_left_normalized (c:=vp0010101110100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1395761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1395761639/1000000 : ℚ) by norm_num]
  exact coverp0010101110100
private noncomputable def ep0010101110101_0 : Blocks := edgeBlocks% "full/vectors/0010101110101-E-0000.bin"
noncomputable def ep0010101110101 : Blocks := ep0010101110101_0
private theorem idp0010101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010111010.list =
    C ((2:ℤ)^81) * horner X vp0010101110101.list + horner X ep0010101110101.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101110101 : Branch 1 (-1395761639/2000000 : ℚ) vp001010111010 := by
  apply branch_checked idp0010101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1395761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1396761639/1000000 : ℚ) by norm_num]
  exact coverp0010101110101
theorem coverp001010111010 : Covers (-1395761639/2000000 : ℚ) vp001010111010 := join_branches bp0010101110100 bp0010101110101
private noncomputable def vp00101011101_0 : Blocks := edgeBlocks% "full/vectors/00101011101-V-0000.bin"
noncomputable def vp00101011101 : Blocks := vp00101011101_0
private theorem bp001010111010 : Branch 0 (-1395761639/4000000 : ℚ) vp00101011101 := by
  apply branch_left_normalized (c:=vp001010111010) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-1395761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1395761639/2000000 : ℚ) by norm_num]
  exact coverp001010111010
private noncomputable def ep001010111011_0 : Blocks := edgeBlocks% "full/vectors/001010111011-E-0000.bin"
noncomputable def ep001010111011 : Blocks := ep001010111011_0
private theorem idp001010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101011101.list =
    C ((2:ℤ)^140) * horner X vp001010111011.list + horner X ep001010111011.list := by
  exact edge_identity (B := (2:ℤ)^284) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010111011 : Branch 1 (-1395761639/4000000 : ℚ) vp00101011101 := by
  apply branch_checked idp001010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1395761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1397761639/2000000 : ℚ) by norm_num]
  exact coverp001010111011
theorem coverp00101011101 : Covers (-1395761639/4000000 : ℚ) vp00101011101 := join_branches bp001010111010 bp001010111011
private noncomputable def vp0010101110011_0 : Blocks := edgeBlocks% "full/vectors/0010101110011-V-0000.bin"
noncomputable def vp0010101110011 : Blocks := vp0010101110011_0
theorem coverp0010101110011 : Covers (-1394761639/1000000 : ℚ) vp0010101110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101110010_0 : Blocks := edgeBlocks% "full/vectors/0010101110010-V-0000.bin"
noncomputable def vp0010101110010 : Blocks := vp0010101110010_0
theorem coverp0010101110010 : Covers (-1393761639/1000000 : ℚ) vp0010101110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010111001_0 : Blocks := edgeBlocks% "full/vectors/001010111001-V-0000.bin"
noncomputable def vp001010111001 : Blocks := vp001010111001_0
private theorem bp0010101110010 : Branch 0 (-1393761639/2000000 : ℚ) vp001010111001 := by
  apply branch_left_normalized (c:=vp0010101110010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1393761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1393761639/1000000 : ℚ) by norm_num]
  exact coverp0010101110010
private noncomputable def ep0010101110011_0 : Blocks := edgeBlocks% "full/vectors/0010101110011-E-0000.bin"
noncomputable def ep0010101110011 : Blocks := ep0010101110011_0
private theorem idp0010101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010111001.list =
    C ((2:ℤ)^79) * horner X vp0010101110011.list + horner X ep0010101110011.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101110011 : Branch 1 (-1393761639/2000000 : ℚ) vp001010111001 := by
  apply branch_checked idp0010101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1393761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1394761639/1000000 : ℚ) by norm_num]
  exact coverp0010101110011
theorem coverp001010111001 : Covers (-1393761639/2000000 : ℚ) vp001010111001 := join_branches bp0010101110010 bp0010101110011
private noncomputable def vp0010101110001_0 : Blocks := edgeBlocks% "full/vectors/0010101110001-V-0000.bin"
noncomputable def vp0010101110001 : Blocks := vp0010101110001_0
theorem coverp0010101110001 : Covers (-1392761639/1000000 : ℚ) vp0010101110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101110000_0 : Blocks := edgeBlocks% "full/vectors/0010101110000-V-0000.bin"
noncomputable def vp0010101110000 : Blocks := vp0010101110000_0
theorem coverp0010101110000 : Covers (-1391761639/1000000 : ℚ) vp0010101110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010111000_0 : Blocks := edgeBlocks% "full/vectors/001010111000-V-0000.bin"
noncomputable def vp001010111000 : Blocks := vp001010111000_0
private theorem bp0010101110000 : Branch 0 (-1391761639/2000000 : ℚ) vp001010111000 := by
  apply branch_left_normalized (c:=vp0010101110000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1391761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1391761639/1000000 : ℚ) by norm_num]
  exact coverp0010101110000
private noncomputable def ep0010101110001_0 : Blocks := edgeBlocks% "full/vectors/0010101110001-E-0000.bin"
noncomputable def ep0010101110001 : Blocks := ep0010101110001_0
private theorem idp0010101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010111000.list =
    C ((2:ℤ)^78) * horner X vp0010101110001.list + horner X ep0010101110001.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101110001 : Branch 1 (-1391761639/2000000 : ℚ) vp001010111000 := by
  apply branch_checked idp0010101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1391761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1392761639/1000000 : ℚ) by norm_num]
  exact coverp0010101110001
theorem coverp001010111000 : Covers (-1391761639/2000000 : ℚ) vp001010111000 := join_branches bp0010101110000 bp0010101110001
private noncomputable def vp00101011100_0 : Blocks := edgeBlocks% "full/vectors/00101011100-V-0000.bin"
noncomputable def vp00101011100 : Blocks := vp00101011100_0
private theorem bp001010111000 : Branch 0 (-1391761639/4000000 : ℚ) vp00101011100 := by
  apply branch_left_normalized (c:=vp001010111000) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1391761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1391761639/2000000 : ℚ) by norm_num]
  exact coverp001010111000
private noncomputable def ep001010111001_0 : Blocks := edgeBlocks% "full/vectors/001010111001-E-0000.bin"
noncomputable def ep001010111001 : Blocks := ep001010111001_0
private theorem idp001010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101011100.list =
    C ((2:ℤ)^136) * horner X vp001010111001.list + horner X ep001010111001.list := by
  exact edge_identity (B := (2:ℤ)^281) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010111001 : Branch 1 (-1391761639/4000000 : ℚ) vp00101011100 := by
  apply branch_checked idp001010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1391761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1393761639/2000000 : ℚ) by norm_num]
  exact coverp001010111001
theorem coverp00101011100 : Covers (-1391761639/4000000 : ℚ) vp00101011100 := join_branches bp001010111000 bp001010111001
private noncomputable def vp0010101110_0 : Blocks := edgeBlocks% "full/vectors/0010101110-V-0000.bin"
private noncomputable def vp0010101110_1 : Blocks := edgeBlocks% "full/vectors/0010101110-V-0001.bin"
noncomputable def vp0010101110 : Blocks := (Blocks.join vp0010101110_0 vp0010101110_1)
private theorem bp00101011100 : Branch 0 (-1391761639/8000000 : ℚ) vp0010101110 := by
  apply branch_left_normalized (c:=vp00101011100) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-1391761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1391761639/4000000 : ℚ) by norm_num]
  exact coverp00101011100
private noncomputable def ep00101011101_0 : Blocks := edgeBlocks% "full/vectors/00101011101-E-0000.bin"
private noncomputable def ep00101011101_1 : Blocks := edgeBlocks% "full/vectors/00101011101-E-0001.bin"
noncomputable def ep00101011101 : Blocks := (Blocks.join ep00101011101_0 ep00101011101_1)
private theorem idp00101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010101110.list =
    C ((2:ℤ)^252) * horner X vp00101011101.list + horner X ep00101011101.list := by
  exact edge_identity (B := (2:ℤ)^442) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101011101 : Branch 1 (-1391761639/8000000 : ℚ) vp0010101110 := by
  apply branch_checked idp00101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1391761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1395761639/4000000 : ℚ) by norm_num]
  exact coverp00101011101
theorem coverp0010101110 : Covers (-1391761639/8000000 : ℚ) vp0010101110 := join_branches bp00101011100 bp00101011101
private noncomputable def vp001010111_0 : Blocks := edgeBlocks% "full/vectors/001010111-V-0000.bin"
private noncomputable def vp001010111_1 : Blocks := edgeBlocks% "full/vectors/001010111-V-0001.bin"
private noncomputable def vp001010111_2 : Blocks := edgeBlocks% "full/vectors/001010111-V-0002.bin"
private noncomputable def vp001010111_3 : Blocks := edgeBlocks% "full/vectors/001010111-V-0003.bin"
noncomputable def vp001010111 : Blocks := (Blocks.join (Blocks.join vp001010111_0 vp001010111_1) (Blocks.join vp001010111_2 vp001010111_3))
private theorem bp0010101110 : Branch 0 (-1391761639/16000000 : ℚ) vp001010111 := by
  apply branch_left_normalized (c:=vp0010101110) (k:=0) (m:=231) (by decide +kernel)
  rw [show 2*(-1391761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1391761639/8000000 : ℚ) by norm_num]
  exact coverp0010101110
private noncomputable def ep0010101111_0 : Blocks := edgeBlocks% "full/vectors/0010101111-E-0000.bin"
private noncomputable def ep0010101111_1 : Blocks := edgeBlocks% "full/vectors/0010101111-E-0001.bin"
private noncomputable def ep0010101111_2 : Blocks := edgeBlocks% "full/vectors/0010101111-E-0002.bin"
private noncomputable def ep0010101111_3 : Blocks := edgeBlocks% "full/vectors/0010101111-E-0003.bin"
noncomputable def ep0010101111 : Blocks := (Blocks.join (Blocks.join ep0010101111_0 ep0010101111_1) (Blocks.join ep0010101111_2 ep0010101111_3))
private theorem idp0010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010111.list =
    C ((2:ℤ)^486) * horner X vp0010101111.list + horner X ep0010101111.list := by
  exact edge_identity (B := (2:ℤ)^763) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101111 : Branch 1 (-1391761639/16000000 : ℚ) vp001010111 := by
  apply branch_checked idp0010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1391761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1399761639/8000000 : ℚ) by norm_num]
  exact coverp0010101111
theorem coverp001010111 : Covers (-1391761639/16000000 : ℚ) vp001010111 := join_branches bp0010101110 bp0010101111
private noncomputable def vp0010101101111_0 : Blocks := edgeBlocks% "full/vectors/0010101101111-V-0000.bin"
noncomputable def vp0010101101111 : Blocks := vp0010101101111_0
theorem coverp0010101101111 : Covers (-1390761639/1000000 : ℚ) vp0010101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101101110_0 : Blocks := edgeBlocks% "full/vectors/0010101101110-V-0000.bin"
noncomputable def vp0010101101110 : Blocks := vp0010101101110_0
theorem coverp0010101101110 : Covers (-1389761639/1000000 : ℚ) vp0010101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010110111_0 : Blocks := edgeBlocks% "full/vectors/001010110111-V-0000.bin"
noncomputable def vp001010110111 : Blocks := vp001010110111_0
private theorem bp0010101101110 : Branch 0 (-1389761639/2000000 : ℚ) vp001010110111 := by
  apply branch_left_normalized (c:=vp0010101101110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1389761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1389761639/1000000 : ℚ) by norm_num]
  exact coverp0010101101110
private noncomputable def ep0010101101111_0 : Blocks := edgeBlocks% "full/vectors/0010101101111-E-0000.bin"
noncomputable def ep0010101101111 : Blocks := ep0010101101111_0
private theorem idp0010101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010110111.list =
    C ((2:ℤ)^77) * horner X vp0010101101111.list + horner X ep0010101101111.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101101111 : Branch 1 (-1389761639/2000000 : ℚ) vp001010110111 := by
  apply branch_checked idp0010101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1389761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1390761639/1000000 : ℚ) by norm_num]
  exact coverp0010101101111
theorem coverp001010110111 : Covers (-1389761639/2000000 : ℚ) vp001010110111 := join_branches bp0010101101110 bp0010101101111
private noncomputable def vp0010101101101_0 : Blocks := edgeBlocks% "full/vectors/0010101101101-V-0000.bin"
noncomputable def vp0010101101101 : Blocks := vp0010101101101_0
theorem coverp0010101101101 : Covers (-1388761639/1000000 : ℚ) vp0010101101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101101100_0 : Blocks := edgeBlocks% "full/vectors/0010101101100-V-0000.bin"
noncomputable def vp0010101101100 : Blocks := vp0010101101100_0
theorem coverp0010101101100 : Covers (-1387761639/1000000 : ℚ) vp0010101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010110110_0 : Blocks := edgeBlocks% "full/vectors/001010110110-V-0000.bin"
noncomputable def vp001010110110 : Blocks := vp001010110110_0
private theorem bp0010101101100 : Branch 0 (-1387761639/2000000 : ℚ) vp001010110110 := by
  apply branch_left_normalized (c:=vp0010101101100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1387761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1387761639/1000000 : ℚ) by norm_num]
  exact coverp0010101101100
private noncomputable def ep0010101101101_0 : Blocks := edgeBlocks% "full/vectors/0010101101101-E-0000.bin"
noncomputable def ep0010101101101 : Blocks := ep0010101101101_0
private theorem idp0010101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010110110.list =
    C ((2:ℤ)^80) * horner X vp0010101101101.list + horner X ep0010101101101.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101101101 : Branch 1 (-1387761639/2000000 : ℚ) vp001010110110 := by
  apply branch_checked idp0010101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1387761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1388761639/1000000 : ℚ) by norm_num]
  exact coverp0010101101101
theorem coverp001010110110 : Covers (-1387761639/2000000 : ℚ) vp001010110110 := join_branches bp0010101101100 bp0010101101101
private noncomputable def vp00101011011_0 : Blocks := edgeBlocks% "full/vectors/00101011011-V-0000.bin"
noncomputable def vp00101011011 : Blocks := vp00101011011_0
private theorem bp001010110110 : Branch 0 (-1387761639/4000000 : ℚ) vp00101011011 := by
  apply branch_left_normalized (c:=vp001010110110) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1387761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1387761639/2000000 : ℚ) by norm_num]
  exact coverp001010110110
private noncomputable def ep001010110111_0 : Blocks := edgeBlocks% "full/vectors/001010110111-E-0000.bin"
noncomputable def ep001010110111 : Blocks := ep001010110111_0
private theorem idp001010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101011011.list =
    C ((2:ℤ)^139) * horner X vp001010110111.list + horner X ep001010110111.list := by
  exact edge_identity (B := (2:ℤ)^281) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010110111 : Branch 1 (-1387761639/4000000 : ℚ) vp00101011011 := by
  apply branch_checked idp001010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1387761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1389761639/2000000 : ℚ) by norm_num]
  exact coverp001010110111
theorem coverp00101011011 : Covers (-1387761639/4000000 : ℚ) vp00101011011 := join_branches bp001010110110 bp001010110111
private noncomputable def vp0010101101011_0 : Blocks := edgeBlocks% "full/vectors/0010101101011-V-0000.bin"
noncomputable def vp0010101101011 : Blocks := vp0010101101011_0
theorem coverp0010101101011 : Covers (-1386761639/1000000 : ℚ) vp0010101101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101101010_0 : Blocks := edgeBlocks% "full/vectors/0010101101010-V-0000.bin"
noncomputable def vp0010101101010 : Blocks := vp0010101101010_0
theorem coverp0010101101010 : Covers (-1385761639/1000000 : ℚ) vp0010101101010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010110101_0 : Blocks := edgeBlocks% "full/vectors/001010110101-V-0000.bin"
noncomputable def vp001010110101 : Blocks := vp001010110101_0
private theorem bp0010101101010 : Branch 0 (-1385761639/2000000 : ℚ) vp001010110101 := by
  apply branch_left_normalized (c:=vp0010101101010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1385761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1385761639/1000000 : ℚ) by norm_num]
  exact coverp0010101101010
private noncomputable def ep0010101101011_0 : Blocks := edgeBlocks% "full/vectors/0010101101011-E-0000.bin"
noncomputable def ep0010101101011 : Blocks := ep0010101101011_0
private theorem idp0010101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010110101.list =
    C ((2:ℤ)^81) * horner X vp0010101101011.list + horner X ep0010101101011.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101101011 : Branch 1 (-1385761639/2000000 : ℚ) vp001010110101 := by
  apply branch_checked idp0010101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1385761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1386761639/1000000 : ℚ) by norm_num]
  exact coverp0010101101011
theorem coverp001010110101 : Covers (-1385761639/2000000 : ℚ) vp001010110101 := join_branches bp0010101101010 bp0010101101011
private noncomputable def vp0010101101001_0 : Blocks := edgeBlocks% "full/vectors/0010101101001-V-0000.bin"
noncomputable def vp0010101101001 : Blocks := vp0010101101001_0
theorem coverp0010101101001 : Covers (-1384761639/1000000 : ℚ) vp0010101101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101101000_0 : Blocks := edgeBlocks% "full/vectors/0010101101000-V-0000.bin"
noncomputable def vp0010101101000 : Blocks := vp0010101101000_0
theorem coverp0010101101000 : Covers (-1383761639/1000000 : ℚ) vp0010101101000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010110100_0 : Blocks := edgeBlocks% "full/vectors/001010110100-V-0000.bin"
noncomputable def vp001010110100 : Blocks := vp001010110100_0
private theorem bp0010101101000 : Branch 0 (-1383761639/2000000 : ℚ) vp001010110100 := by
  apply branch_left_normalized (c:=vp0010101101000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1383761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1383761639/1000000 : ℚ) by norm_num]
  exact coverp0010101101000
private noncomputable def ep0010101101001_0 : Blocks := edgeBlocks% "full/vectors/0010101101001-E-0000.bin"
noncomputable def ep0010101101001 : Blocks := ep0010101101001_0
private theorem idp0010101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010110100.list =
    C ((2:ℤ)^76) * horner X vp0010101101001.list + horner X ep0010101101001.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101101001 : Branch 1 (-1383761639/2000000 : ℚ) vp001010110100 := by
  apply branch_checked idp0010101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1383761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1384761639/1000000 : ℚ) by norm_num]
  exact coverp0010101101001
theorem coverp001010110100 : Covers (-1383761639/2000000 : ℚ) vp001010110100 := join_branches bp0010101101000 bp0010101101001
private noncomputable def vp00101011010_0 : Blocks := edgeBlocks% "full/vectors/00101011010-V-0000.bin"
noncomputable def vp00101011010 : Blocks := vp00101011010_0
private theorem bp001010110100 : Branch 0 (-1383761639/4000000 : ℚ) vp00101011010 := by
  apply branch_left_normalized (c:=vp001010110100) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-1383761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1383761639/2000000 : ℚ) by norm_num]
  exact coverp001010110100
private noncomputable def ep001010110101_0 : Blocks := edgeBlocks% "full/vectors/001010110101-E-0000.bin"
noncomputable def ep001010110101 : Blocks := ep001010110101_0
private theorem idp001010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101011010.list =
    C ((2:ℤ)^133) * horner X vp001010110101.list + horner X ep001010110101.list := by
  exact edge_identity (B := (2:ℤ)^279) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010110101 : Branch 1 (-1383761639/4000000 : ℚ) vp00101011010 := by
  apply branch_checked idp001010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1383761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1385761639/2000000 : ℚ) by norm_num]
  exact coverp001010110101
theorem coverp00101011010 : Covers (-1383761639/4000000 : ℚ) vp00101011010 := join_branches bp001010110100 bp001010110101
private noncomputable def vp0010101101_0 : Blocks := edgeBlocks% "full/vectors/0010101101-V-0000.bin"
private noncomputable def vp0010101101_1 : Blocks := edgeBlocks% "full/vectors/0010101101-V-0001.bin"
noncomputable def vp0010101101 : Blocks := (Blocks.join vp0010101101_0 vp0010101101_1)
private theorem bp00101011010 : Branch 0 (-1383761639/8000000 : ℚ) vp0010101101 := by
  apply branch_left_normalized (c:=vp00101011010) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-1383761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1383761639/4000000 : ℚ) by norm_num]
  exact coverp00101011010
private noncomputable def ep00101011011_0 : Blocks := edgeBlocks% "full/vectors/00101011011-E-0000.bin"
private noncomputable def ep00101011011_1 : Blocks := edgeBlocks% "full/vectors/00101011011-E-0001.bin"
noncomputable def ep00101011011 : Blocks := (Blocks.join ep00101011011_0 ep00101011011_1)
private theorem idp00101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010101101.list =
    C ((2:ℤ)^253) * horner X vp00101011011.list + horner X ep00101011011.list := by
  exact edge_identity (B := (2:ℤ)^441) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101011011 : Branch 1 (-1383761639/8000000 : ℚ) vp0010101101 := by
  apply branch_checked idp00101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1383761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1387761639/4000000 : ℚ) by norm_num]
  exact coverp00101011011
theorem coverp0010101101 : Covers (-1383761639/8000000 : ℚ) vp0010101101 := join_branches bp00101011010 bp00101011011
private noncomputable def vp0010101100111_0 : Blocks := edgeBlocks% "full/vectors/0010101100111-V-0000.bin"
noncomputable def vp0010101100111 : Blocks := vp0010101100111_0
theorem coverp0010101100111 : Covers (-1382761639/1000000 : ℚ) vp0010101100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101100110_0 : Blocks := edgeBlocks% "full/vectors/0010101100110-V-0000.bin"
noncomputable def vp0010101100110 : Blocks := vp0010101100110_0
theorem coverp0010101100110 : Covers (-1381761639/1000000 : ℚ) vp0010101100110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010110011_0 : Blocks := edgeBlocks% "full/vectors/001010110011-V-0000.bin"
noncomputable def vp001010110011 : Blocks := vp001010110011_0
private theorem bp0010101100110 : Branch 0 (-1381761639/2000000 : ℚ) vp001010110011 := by
  apply branch_left_normalized (c:=vp0010101100110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1381761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1381761639/1000000 : ℚ) by norm_num]
  exact coverp0010101100110
private noncomputable def ep0010101100111_0 : Blocks := edgeBlocks% "full/vectors/0010101100111-E-0000.bin"
noncomputable def ep0010101100111 : Blocks := ep0010101100111_0
private theorem idp0010101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010110011.list =
    C ((2:ℤ)^76) * horner X vp0010101100111.list + horner X ep0010101100111.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101100111 : Branch 1 (-1381761639/2000000 : ℚ) vp001010110011 := by
  apply branch_checked idp0010101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1381761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1382761639/1000000 : ℚ) by norm_num]
  exact coverp0010101100111
theorem coverp001010110011 : Covers (-1381761639/2000000 : ℚ) vp001010110011 := join_branches bp0010101100110 bp0010101100111
private noncomputable def vp001010110010_0 : Blocks := edgeBlocks% "full/vectors/001010110010-V-0000.bin"
noncomputable def vp001010110010 : Blocks := vp001010110010_0
theorem coverp001010110010 : Covers (-1379761639/2000000 : ℚ) vp001010110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00101011001_0 : Blocks := edgeBlocks% "full/vectors/00101011001-V-0000.bin"
noncomputable def vp00101011001 : Blocks := vp00101011001_0
private theorem bp001010110010 : Branch 0 (-1379761639/4000000 : ℚ) vp00101011001 := by
  apply branch_left_normalized (c:=vp001010110010) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-1379761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1379761639/2000000 : ℚ) by norm_num]
  exact coverp001010110010
private noncomputable def ep001010110011_0 : Blocks := edgeBlocks% "full/vectors/001010110011-E-0000.bin"
noncomputable def ep001010110011 : Blocks := ep001010110011_0
private theorem idp001010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101011001.list =
    C ((2:ℤ)^134) * horner X vp001010110011.list + horner X ep001010110011.list := by
  exact edge_identity (B := (2:ℤ)^273) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010110011 : Branch 1 (-1379761639/4000000 : ℚ) vp00101011001 := by
  apply branch_checked idp001010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1379761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1381761639/2000000 : ℚ) by norm_num]
  exact coverp001010110011
theorem coverp00101011001 : Covers (-1379761639/4000000 : ℚ) vp00101011001 := join_branches bp001010110010 bp001010110011
private noncomputable def vp001010110001_0 : Blocks := edgeBlocks% "full/vectors/001010110001-V-0000.bin"
noncomputable def vp001010110001 : Blocks := vp001010110001_0
theorem coverp001010110001 : Covers (-1377761639/2000000 : ℚ) vp001010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp001010110000_0 : Blocks := edgeBlocks% "full/vectors/001010110000-V-0000.bin"
noncomputable def vp001010110000 : Blocks := vp001010110000_0
theorem coverp001010110000 : Covers (-1375761639/2000000 : ℚ) vp001010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00101011000_0 : Blocks := edgeBlocks% "full/vectors/00101011000-V-0000.bin"
noncomputable def vp00101011000 : Blocks := vp00101011000_0
private theorem bp001010110000 : Branch 0 (-1375761639/4000000 : ℚ) vp00101011000 := by
  apply branch_left_normalized (c:=vp001010110000) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1375761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1375761639/2000000 : ℚ) by norm_num]
  exact coverp001010110000
private noncomputable def ep001010110001_0 : Blocks := edgeBlocks% "full/vectors/001010110001-E-0000.bin"
noncomputable def ep001010110001 : Blocks := ep001010110001_0
private theorem idp001010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101011000.list =
    C ((2:ℤ)^133) * horner X vp001010110001.list + horner X ep001010110001.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010110001 : Branch 1 (-1375761639/4000000 : ℚ) vp00101011000 := by
  apply branch_checked idp001010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1375761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1377761639/2000000 : ℚ) by norm_num]
  exact coverp001010110001
theorem coverp00101011000 : Covers (-1375761639/4000000 : ℚ) vp00101011000 := join_branches bp001010110000 bp001010110001
private noncomputable def vp0010101100_0 : Blocks := edgeBlocks% "full/vectors/0010101100-V-0000.bin"
private noncomputable def vp0010101100_1 : Blocks := edgeBlocks% "full/vectors/0010101100-V-0001.bin"
noncomputable def vp0010101100 : Blocks := (Blocks.join vp0010101100_0 vp0010101100_1)
private theorem bp00101011000 : Branch 0 (-1375761639/8000000 : ℚ) vp0010101100 := by
  apply branch_left_normalized (c:=vp00101011000) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-1375761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1375761639/4000000 : ℚ) by norm_num]
  exact coverp00101011000
private noncomputable def ep00101011001_0 : Blocks := edgeBlocks% "full/vectors/00101011001-E-0000.bin"
private noncomputable def ep00101011001_1 : Blocks := edgeBlocks% "full/vectors/00101011001-E-0001.bin"
noncomputable def ep00101011001 : Blocks := (Blocks.join ep00101011001_0 ep00101011001_1)
private theorem idp00101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010101100.list =
    C ((2:ℤ)^250) * horner X vp00101011001.list + horner X ep00101011001.list := by
  exact edge_identity (B := (2:ℤ)^432) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101011001 : Branch 1 (-1375761639/8000000 : ℚ) vp0010101100 := by
  apply branch_checked idp00101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1375761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1379761639/4000000 : ℚ) by norm_num]
  exact coverp00101011001
theorem coverp0010101100 : Covers (-1375761639/8000000 : ℚ) vp0010101100 := join_branches bp00101011000 bp00101011001
private noncomputable def vp001010110_0 : Blocks := edgeBlocks% "full/vectors/001010110-V-0000.bin"
private noncomputable def vp001010110_1 : Blocks := edgeBlocks% "full/vectors/001010110-V-0001.bin"
private noncomputable def vp001010110_2 : Blocks := edgeBlocks% "full/vectors/001010110-V-0002.bin"
private noncomputable def vp001010110_3 : Blocks := edgeBlocks% "full/vectors/001010110-V-0003.bin"
noncomputable def vp001010110 : Blocks := (Blocks.join (Blocks.join vp001010110_0 vp001010110_1) (Blocks.join vp001010110_2 vp001010110_3))
private theorem bp0010101100 : Branch 0 (-1375761639/16000000 : ℚ) vp001010110 := by
  apply branch_left_normalized (c:=vp0010101100) (k:=0) (m:=228) (by decide +kernel)
  rw [show 2*(-1375761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1375761639/8000000 : ℚ) by norm_num]
  exact coverp0010101100
private noncomputable def ep0010101101_0 : Blocks := edgeBlocks% "full/vectors/0010101101-E-0000.bin"
private noncomputable def ep0010101101_1 : Blocks := edgeBlocks% "full/vectors/0010101101-E-0001.bin"
private noncomputable def ep0010101101_2 : Blocks := edgeBlocks% "full/vectors/0010101101-E-0002.bin"
private noncomputable def ep0010101101_3 : Blocks := edgeBlocks% "full/vectors/0010101101-E-0003.bin"
noncomputable def ep0010101101 : Blocks := (Blocks.join (Blocks.join ep0010101101_0 ep0010101101_1) (Blocks.join ep0010101101_2 ep0010101101_3))
private theorem idp0010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010110.list =
    C ((2:ℤ)^478) * horner X vp0010101101.list + horner X ep0010101101.list := by
  exact edge_identity (B := (2:ℤ)^754) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101101 : Branch 1 (-1375761639/16000000 : ℚ) vp001010110 := by
  apply branch_checked idp0010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1375761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1383761639/8000000 : ℚ) by norm_num]
  exact coverp0010101101
theorem coverp001010110 : Covers (-1375761639/16000000 : ℚ) vp001010110 := join_branches bp0010101100 bp0010101101
private noncomputable def vp00101011_0 : Blocks := edgeBlocks% "full/vectors/00101011-V-0000.bin"
private noncomputable def vp00101011_1 : Blocks := edgeBlocks% "full/vectors/00101011-V-0001.bin"
private noncomputable def vp00101011_2 : Blocks := edgeBlocks% "full/vectors/00101011-V-0002.bin"
private noncomputable def vp00101011_3 : Blocks := edgeBlocks% "full/vectors/00101011-V-0003.bin"
private noncomputable def vp00101011_4 : Blocks := edgeBlocks% "full/vectors/00101011-V-0004.bin"
private noncomputable def vp00101011_5 : Blocks := edgeBlocks% "full/vectors/00101011-V-0005.bin"
private noncomputable def vp00101011_6 : Blocks := edgeBlocks% "full/vectors/00101011-V-0006.bin"
noncomputable def vp00101011 : Blocks := (Blocks.join (Blocks.join vp00101011_0 (Blocks.join vp00101011_1 vp00101011_2)) (Blocks.join (Blocks.join vp00101011_3 vp00101011_4) (Blocks.join vp00101011_5 vp00101011_6)))
private theorem bp001010110 : Branch 0 (-1375761639/32000000 : ℚ) vp00101011 := by
  apply branch_left_normalized (c:=vp001010110) (k:=0) (m:=437) (by decide +kernel)
  rw [show 2*(-1375761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1375761639/16000000 : ℚ) by norm_num]
  exact coverp001010110
private noncomputable def ep001010111_0 : Blocks := edgeBlocks% "full/vectors/001010111-E-0000.bin"
private noncomputable def ep001010111_1 : Blocks := edgeBlocks% "full/vectors/001010111-E-0001.bin"
private noncomputable def ep001010111_2 : Blocks := edgeBlocks% "full/vectors/001010111-E-0002.bin"
private noncomputable def ep001010111_3 : Blocks := edgeBlocks% "full/vectors/001010111-E-0003.bin"
private noncomputable def ep001010111_4 : Blocks := edgeBlocks% "full/vectors/001010111-E-0004.bin"
private noncomputable def ep001010111_5 : Blocks := edgeBlocks% "full/vectors/001010111-E-0005.bin"
private noncomputable def ep001010111_6 : Blocks := edgeBlocks% "full/vectors/001010111-E-0006.bin"
noncomputable def ep001010111 : Blocks := (Blocks.join (Blocks.join ep001010111_0 (Blocks.join ep001010111_1 ep001010111_2)) (Blocks.join (Blocks.join ep001010111_3 ep001010111_4) (Blocks.join ep001010111_5 ep001010111_6)))
private theorem idp001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101011.list =
    C ((2:ℤ)^940) * horner X vp001010111.list + horner X ep001010111.list := by
  exact edge_identity (B := (2:ℤ)^1394) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010111 : Branch 1 (-1375761639/32000000 : ℚ) vp00101011 := by
  apply branch_checked idp001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1375761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1391761639/16000000 : ℚ) by norm_num]
  exact coverp001010111
theorem coverp00101011 : Covers (-1375761639/32000000 : ℚ) vp00101011 := join_branches bp001010110 bp001010111
private noncomputable def vp001010101111_0 : Blocks := edgeBlocks% "full/vectors/001010101111-V-0000.bin"
noncomputable def vp001010101111 : Blocks := vp001010101111_0
theorem coverp001010101111 : Covers (-1373761639/2000000 : ℚ) vp001010101111 := cover_leaf (by decide +kernel)
private noncomputable def vp001010101110_0 : Blocks := edgeBlocks% "full/vectors/001010101110-V-0000.bin"
noncomputable def vp001010101110 : Blocks := vp001010101110_0
theorem coverp001010101110 : Covers (-1371761639/2000000 : ℚ) vp001010101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00101010111_0 : Blocks := edgeBlocks% "full/vectors/00101010111-V-0000.bin"
noncomputable def vp00101010111 : Blocks := vp00101010111_0
private theorem bp001010101110 : Branch 0 (-1371761639/4000000 : ℚ) vp00101010111 := by
  apply branch_left_normalized (c:=vp001010101110) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1371761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1371761639/2000000 : ℚ) by norm_num]
  exact coverp001010101110
private noncomputable def ep001010101111_0 : Blocks := edgeBlocks% "full/vectors/001010101111-E-0000.bin"
noncomputable def ep001010101111 : Blocks := ep001010101111_0
private theorem idp001010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101010111.list =
    C ((2:ℤ)^135) * horner X vp001010101111.list + horner X ep001010101111.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010101111 : Branch 1 (-1371761639/4000000 : ℚ) vp00101010111 := by
  apply branch_checked idp001010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1371761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1373761639/2000000 : ℚ) by norm_num]
  exact coverp001010101111
theorem coverp00101010111 : Covers (-1371761639/4000000 : ℚ) vp00101010111 := join_branches bp001010101110 bp001010101111
private noncomputable def vp001010101101_0 : Blocks := edgeBlocks% "full/vectors/001010101101-V-0000.bin"
noncomputable def vp001010101101 : Blocks := vp001010101101_0
theorem coverp001010101101 : Covers (-1369761639/2000000 : ℚ) vp001010101101 := cover_leaf (by decide +kernel)
private noncomputable def vp001010101100_0 : Blocks := edgeBlocks% "full/vectors/001010101100-V-0000.bin"
noncomputable def vp001010101100 : Blocks := vp001010101100_0
theorem coverp001010101100 : Covers (-1367761639/2000000 : ℚ) vp001010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00101010110_0 : Blocks := edgeBlocks% "full/vectors/00101010110-V-0000.bin"
noncomputable def vp00101010110 : Blocks := vp00101010110_0
private theorem bp001010101100 : Branch 0 (-1367761639/4000000 : ℚ) vp00101010110 := by
  apply branch_left_normalized (c:=vp001010101100) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1367761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1367761639/2000000 : ℚ) by norm_num]
  exact coverp001010101100
private noncomputable def ep001010101101_0 : Blocks := edgeBlocks% "full/vectors/001010101101-E-0000.bin"
noncomputable def ep001010101101 : Blocks := ep001010101101_0
private theorem idp001010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101010110.list =
    C ((2:ℤ)^134) * horner X vp001010101101.list + horner X ep001010101101.list := by
  exact edge_identity (B := (2:ℤ)^269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010101101 : Branch 1 (-1367761639/4000000 : ℚ) vp00101010110 := by
  apply branch_checked idp001010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1367761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1369761639/2000000 : ℚ) by norm_num]
  exact coverp001010101101
theorem coverp00101010110 : Covers (-1367761639/4000000 : ℚ) vp00101010110 := join_branches bp001010101100 bp001010101101
private noncomputable def vp0010101011_0 : Blocks := edgeBlocks% "full/vectors/0010101011-V-0000.bin"
private noncomputable def vp0010101011_1 : Blocks := edgeBlocks% "full/vectors/0010101011-V-0001.bin"
noncomputable def vp0010101011 : Blocks := (Blocks.join vp0010101011_0 vp0010101011_1)
private theorem bp00101010110 : Branch 0 (-1367761639/8000000 : ℚ) vp0010101011 := by
  apply branch_left_normalized (c:=vp00101010110) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-1367761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1367761639/4000000 : ℚ) by norm_num]
  exact coverp00101010110
private noncomputable def ep00101010111_0 : Blocks := edgeBlocks% "full/vectors/00101010111-E-0000.bin"
private noncomputable def ep00101010111_1 : Blocks := edgeBlocks% "full/vectors/00101010111-E-0001.bin"
noncomputable def ep00101010111 : Blocks := (Blocks.join ep00101010111_0 ep00101010111_1)
private theorem idp00101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010101011.list =
    C ((2:ℤ)^251) * horner X vp00101010111.list + horner X ep00101010111.list := by
  exact edge_identity (B := (2:ℤ)^432) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101010111 : Branch 1 (-1367761639/8000000 : ℚ) vp0010101011 := by
  apply branch_checked idp00101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1367761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1371761639/4000000 : ℚ) by norm_num]
  exact coverp00101010111
theorem coverp0010101011 : Covers (-1367761639/8000000 : ℚ) vp0010101011 := join_branches bp00101010110 bp00101010111
private noncomputable def vp001010101011_0 : Blocks := edgeBlocks% "full/vectors/001010101011-V-0000.bin"
noncomputable def vp001010101011 : Blocks := vp001010101011_0
theorem coverp001010101011 : Covers (-1365761639/2000000 : ℚ) vp001010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp001010101010_0 : Blocks := edgeBlocks% "full/vectors/001010101010-V-0000.bin"
noncomputable def vp001010101010 : Blocks := vp001010101010_0
theorem coverp001010101010 : Covers (-1363761639/2000000 : ℚ) vp001010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00101010101_0 : Blocks := edgeBlocks% "full/vectors/00101010101-V-0000.bin"
noncomputable def vp00101010101 : Blocks := vp00101010101_0
private theorem bp001010101010 : Branch 0 (-1363761639/4000000 : ℚ) vp00101010101 := by
  apply branch_left_normalized (c:=vp001010101010) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1363761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1363761639/2000000 : ℚ) by norm_num]
  exact coverp001010101010
private noncomputable def ep001010101011_0 : Blocks := edgeBlocks% "full/vectors/001010101011-E-0000.bin"
noncomputable def ep001010101011 : Blocks := ep001010101011_0
private theorem idp001010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101010101.list =
    C ((2:ℤ)^135) * horner X vp001010101011.list + horner X ep001010101011.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010101011 : Branch 1 (-1363761639/4000000 : ℚ) vp00101010101 := by
  apply branch_checked idp001010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1363761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1365761639/2000000 : ℚ) by norm_num]
  exact coverp001010101011
theorem coverp00101010101 : Covers (-1363761639/4000000 : ℚ) vp00101010101 := join_branches bp001010101010 bp001010101011
private noncomputable def vp001010101001_0 : Blocks := edgeBlocks% "full/vectors/001010101001-V-0000.bin"
noncomputable def vp001010101001 : Blocks := vp001010101001_0
theorem coverp001010101001 : Covers (-1361761639/2000000 : ℚ) vp001010101001 := cover_leaf (by decide +kernel)
private noncomputable def vp001010101000_0 : Blocks := edgeBlocks% "full/vectors/001010101000-V-0000.bin"
noncomputable def vp001010101000 : Blocks := vp001010101000_0
theorem coverp001010101000 : Covers (-1359761639/2000000 : ℚ) vp001010101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00101010100_0 : Blocks := edgeBlocks% "full/vectors/00101010100-V-0000.bin"
noncomputable def vp00101010100 : Blocks := vp00101010100_0
private theorem bp001010101000 : Branch 0 (-1359761639/4000000 : ℚ) vp00101010100 := by
  apply branch_left_normalized (c:=vp001010101000) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1359761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1359761639/2000000 : ℚ) by norm_num]
  exact coverp001010101000
private noncomputable def ep001010101001_0 : Blocks := edgeBlocks% "full/vectors/001010101001-E-0000.bin"
noncomputable def ep001010101001 : Blocks := ep001010101001_0
private theorem idp001010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101010100.list =
    C ((2:ℤ)^135) * horner X vp001010101001.list + horner X ep001010101001.list := by
  exact edge_identity (B := (2:ℤ)^271) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010101001 : Branch 1 (-1359761639/4000000 : ℚ) vp00101010100 := by
  apply branch_checked idp001010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1359761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1361761639/2000000 : ℚ) by norm_num]
  exact coverp001010101001
theorem coverp00101010100 : Covers (-1359761639/4000000 : ℚ) vp00101010100 := join_branches bp001010101000 bp001010101001
private noncomputable def vp0010101010_0 : Blocks := edgeBlocks% "full/vectors/0010101010-V-0000.bin"
private noncomputable def vp0010101010_1 : Blocks := edgeBlocks% "full/vectors/0010101010-V-0001.bin"
noncomputable def vp0010101010 : Blocks := (Blocks.join vp0010101010_0 vp0010101010_1)
private theorem bp00101010100 : Branch 0 (-1359761639/8000000 : ℚ) vp0010101010 := by
  apply branch_left_normalized (c:=vp00101010100) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-1359761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1359761639/4000000 : ℚ) by norm_num]
  exact coverp00101010100
private noncomputable def ep00101010101_0 : Blocks := edgeBlocks% "full/vectors/00101010101-E-0000.bin"
private noncomputable def ep00101010101_1 : Blocks := edgeBlocks% "full/vectors/00101010101-E-0001.bin"
noncomputable def ep00101010101 : Blocks := (Blocks.join ep00101010101_0 ep00101010101_1)
private theorem idp00101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010101010.list =
    C ((2:ℤ)^254) * horner X vp00101010101.list + horner X ep00101010101.list := by
  exact edge_identity (B := (2:ℤ)^435) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101010101 : Branch 1 (-1359761639/8000000 : ℚ) vp0010101010 := by
  apply branch_checked idp00101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1359761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1363761639/4000000 : ℚ) by norm_num]
  exact coverp00101010101
theorem coverp0010101010 : Covers (-1359761639/8000000 : ℚ) vp0010101010 := join_branches bp00101010100 bp00101010101
private noncomputable def vp001010101_0 : Blocks := edgeBlocks% "full/vectors/001010101-V-0000.bin"
private noncomputable def vp001010101_1 : Blocks := edgeBlocks% "full/vectors/001010101-V-0001.bin"
private noncomputable def vp001010101_2 : Blocks := edgeBlocks% "full/vectors/001010101-V-0002.bin"
private noncomputable def vp001010101_3 : Blocks := edgeBlocks% "full/vectors/001010101-V-0003.bin"
noncomputable def vp001010101 : Blocks := (Blocks.join (Blocks.join vp001010101_0 vp001010101_1) (Blocks.join vp001010101_2 vp001010101_3))
private theorem bp0010101010 : Branch 0 (-1359761639/16000000 : ℚ) vp001010101 := by
  apply branch_left_normalized (c:=vp0010101010) (k:=0) (m:=229) (by decide +kernel)
  rw [show 2*(-1359761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1359761639/8000000 : ℚ) by norm_num]
  exact coverp0010101010
private noncomputable def ep0010101011_0 : Blocks := edgeBlocks% "full/vectors/0010101011-E-0000.bin"
private noncomputable def ep0010101011_1 : Blocks := edgeBlocks% "full/vectors/0010101011-E-0001.bin"
private noncomputable def ep0010101011_2 : Blocks := edgeBlocks% "full/vectors/0010101011-E-0002.bin"
private noncomputable def ep0010101011_3 : Blocks := edgeBlocks% "full/vectors/0010101011-E-0003.bin"
noncomputable def ep0010101011 : Blocks := (Blocks.join (Blocks.join ep0010101011_0 ep0010101011_1) (Blocks.join ep0010101011_2 ep0010101011_3))
private theorem idp0010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010101.list =
    C ((2:ℤ)^488) * horner X vp0010101011.list + horner X ep0010101011.list := by
  exact edge_identity (B := (2:ℤ)^759) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101011 : Branch 1 (-1359761639/16000000 : ℚ) vp001010101 := by
  apply branch_checked idp0010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1359761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1367761639/8000000 : ℚ) by norm_num]
  exact coverp0010101011
theorem coverp001010101 : Covers (-1359761639/16000000 : ℚ) vp001010101 := join_branches bp0010101010 bp0010101011
private noncomputable def vp001010100111_0 : Blocks := edgeBlocks% "full/vectors/001010100111-V-0000.bin"
noncomputable def vp001010100111 : Blocks := vp001010100111_0
theorem coverp001010100111 : Covers (-1357761639/2000000 : ℚ) vp001010100111 := cover_leaf (by decide +kernel)
private noncomputable def vp001010100110_0 : Blocks := edgeBlocks% "full/vectors/001010100110-V-0000.bin"
noncomputable def vp001010100110 : Blocks := vp001010100110_0
theorem coverp001010100110 : Covers (-1355761639/2000000 : ℚ) vp001010100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00101010011_0 : Blocks := edgeBlocks% "full/vectors/00101010011-V-0000.bin"
noncomputable def vp00101010011 : Blocks := vp00101010011_0
private theorem bp001010100110 : Branch 0 (-1355761639/4000000 : ℚ) vp00101010011 := by
  apply branch_left_normalized (c:=vp001010100110) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1355761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1355761639/2000000 : ℚ) by norm_num]
  exact coverp001010100110
private noncomputable def ep001010100111_0 : Blocks := edgeBlocks% "full/vectors/001010100111-E-0000.bin"
noncomputable def ep001010100111 : Blocks := ep001010100111_0
private theorem idp001010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101010011.list =
    C ((2:ℤ)^137) * horner X vp001010100111.list + horner X ep001010100111.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010100111 : Branch 1 (-1355761639/4000000 : ℚ) vp00101010011 := by
  apply branch_checked idp001010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1355761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1357761639/2000000 : ℚ) by norm_num]
  exact coverp001010100111
theorem coverp00101010011 : Covers (-1355761639/4000000 : ℚ) vp00101010011 := join_branches bp001010100110 bp001010100111
private noncomputable def vp001010100101_0 : Blocks := edgeBlocks% "full/vectors/001010100101-V-0000.bin"
noncomputable def vp001010100101 : Blocks := vp001010100101_0
theorem coverp001010100101 : Covers (-1353761639/2000000 : ℚ) vp001010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp001010100100_0 : Blocks := edgeBlocks% "full/vectors/001010100100-V-0000.bin"
noncomputable def vp001010100100 : Blocks := vp001010100100_0
theorem coverp001010100100 : Covers (-1351761639/2000000 : ℚ) vp001010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00101010010_0 : Blocks := edgeBlocks% "full/vectors/00101010010-V-0000.bin"
private noncomputable def vp00101010010_1 : Blocks := edgeBlocks% "full/vectors/00101010010-V-0001.bin"
noncomputable def vp00101010010 : Blocks := (Blocks.join vp00101010010_0 vp00101010010_1)
private theorem bp001010100100 : Branch 0 (-1351761639/4000000 : ℚ) vp00101010010 := by
  apply branch_left_normalized (c:=vp001010100100) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-1351761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1351761639/2000000 : ℚ) by norm_num]
  exact coverp001010100100
private noncomputable def ep001010100101_0 : Blocks := edgeBlocks% "full/vectors/001010100101-E-0000.bin"
private noncomputable def ep001010100101_1 : Blocks := edgeBlocks% "full/vectors/001010100101-E-0001.bin"
noncomputable def ep001010100101 : Blocks := (Blocks.join ep001010100101_0 ep001010100101_1)
private theorem idp001010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101010010.list =
    C ((2:ℤ)^145) * horner X vp001010100101.list + horner X ep001010100101.list := by
  exact edge_identity (B := (2:ℤ)^286) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010100101 : Branch 1 (-1351761639/4000000 : ℚ) vp00101010010 := by
  apply branch_checked idp001010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1351761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1353761639/2000000 : ℚ) by norm_num]
  exact coverp001010100101
theorem coverp00101010010 : Covers (-1351761639/4000000 : ℚ) vp00101010010 := join_branches bp001010100100 bp001010100101
private noncomputable def vp0010101001_0 : Blocks := edgeBlocks% "full/vectors/0010101001-V-0000.bin"
private noncomputable def vp0010101001_1 : Blocks := edgeBlocks% "full/vectors/0010101001-V-0001.bin"
noncomputable def vp0010101001 : Blocks := (Blocks.join vp0010101001_0 vp0010101001_1)
private theorem bp00101010010 : Branch 0 (-1351761639/8000000 : ℚ) vp0010101001 := by
  apply branch_left_normalized (c:=vp00101010010) (k:=0) (m:=128) (by decide +kernel)
  rw [show 2*(-1351761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1351761639/4000000 : ℚ) by norm_num]
  exact coverp00101010010
private noncomputable def ep00101010011_0 : Blocks := edgeBlocks% "full/vectors/00101010011-E-0000.bin"
private noncomputable def ep00101010011_1 : Blocks := edgeBlocks% "full/vectors/00101010011-E-0001.bin"
noncomputable def ep00101010011 : Blocks := (Blocks.join ep00101010011_0 ep00101010011_1)
private theorem idp00101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010101001.list =
    C ((2:ℤ)^266) * horner X vp00101010011.list + horner X ep00101010011.list := by
  exact edge_identity (B := (2:ℤ)^450) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101010011 : Branch 1 (-1351761639/8000000 : ℚ) vp0010101001 := by
  apply branch_checked idp00101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1351761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1355761639/4000000 : ℚ) by norm_num]
  exact coverp00101010011
theorem coverp0010101001 : Covers (-1351761639/8000000 : ℚ) vp0010101001 := join_branches bp00101010010 bp00101010011
private noncomputable def vp0010101000111_0 : Blocks := edgeBlocks% "full/vectors/0010101000111-V-0000.bin"
noncomputable def vp0010101000111 : Blocks := vp0010101000111_0
theorem coverp0010101000111 : Covers (-1350761639/1000000 : ℚ) vp0010101000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101000110_0 : Blocks := edgeBlocks% "full/vectors/0010101000110-V-0000.bin"
noncomputable def vp0010101000110 : Blocks := vp0010101000110_0
theorem coverp0010101000110 : Covers (-1349761639/1000000 : ℚ) vp0010101000110 := cover_leaf (by decide +kernel)
private noncomputable def vp001010100011_0 : Blocks := edgeBlocks% "full/vectors/001010100011-V-0000.bin"
noncomputable def vp001010100011 : Blocks := vp001010100011_0
private theorem bp0010101000110 : Branch 0 (-1349761639/2000000 : ℚ) vp001010100011 := by
  apply branch_left_normalized (c:=vp0010101000110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1349761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1349761639/1000000 : ℚ) by norm_num]
  exact coverp0010101000110
private noncomputable def ep0010101000111_0 : Blocks := edgeBlocks% "full/vectors/0010101000111-E-0000.bin"
noncomputable def ep0010101000111 : Blocks := ep0010101000111_0
private theorem idp0010101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010100011.list =
    C ((2:ℤ)^77) * horner X vp0010101000111.list + horner X ep0010101000111.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101000111 : Branch 1 (-1349761639/2000000 : ℚ) vp001010100011 := by
  apply branch_checked idp0010101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1349761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1350761639/1000000 : ℚ) by norm_num]
  exact coverp0010101000111
theorem coverp001010100011 : Covers (-1349761639/2000000 : ℚ) vp001010100011 := join_branches bp0010101000110 bp0010101000111
private noncomputable def vp0010101000101_0 : Blocks := edgeBlocks% "full/vectors/0010101000101-V-0000.bin"
noncomputable def vp0010101000101 : Blocks := vp0010101000101_0
theorem coverp0010101000101 : Covers (-1348761639/1000000 : ℚ) vp0010101000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101000100_0 : Blocks := edgeBlocks% "full/vectors/0010101000100-V-0000.bin"
noncomputable def vp0010101000100 : Blocks := vp0010101000100_0
theorem coverp0010101000100 : Covers (-1347761639/1000000 : ℚ) vp0010101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp001010100010_0 : Blocks := edgeBlocks% "full/vectors/001010100010-V-0000.bin"
noncomputable def vp001010100010 : Blocks := vp001010100010_0
private theorem bp0010101000100 : Branch 0 (-1347761639/2000000 : ℚ) vp001010100010 := by
  apply branch_left_normalized (c:=vp0010101000100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1347761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1347761639/1000000 : ℚ) by norm_num]
  exact coverp0010101000100
private noncomputable def ep0010101000101_0 : Blocks := edgeBlocks% "full/vectors/0010101000101-E-0000.bin"
noncomputable def ep0010101000101 : Blocks := ep0010101000101_0
private theorem idp0010101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010100010.list =
    C ((2:ℤ)^78) * horner X vp0010101000101.list + horner X ep0010101000101.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101000101 : Branch 1 (-1347761639/2000000 : ℚ) vp001010100010 := by
  apply branch_checked idp0010101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1347761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1348761639/1000000 : ℚ) by norm_num]
  exact coverp0010101000101
theorem coverp001010100010 : Covers (-1347761639/2000000 : ℚ) vp001010100010 := join_branches bp0010101000100 bp0010101000101
private noncomputable def vp00101010001_0 : Blocks := edgeBlocks% "full/vectors/00101010001-V-0000.bin"
noncomputable def vp00101010001 : Blocks := vp00101010001_0
private theorem bp001010100010 : Branch 0 (-1347761639/4000000 : ℚ) vp00101010001 := by
  apply branch_left_normalized (c:=vp001010100010) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1347761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1347761639/2000000 : ℚ) by norm_num]
  exact coverp001010100010
private noncomputable def ep001010100011_0 : Blocks := edgeBlocks% "full/vectors/001010100011-E-0000.bin"
noncomputable def ep001010100011 : Blocks := ep001010100011_0
private theorem idp001010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101010001.list =
    C ((2:ℤ)^137) * horner X vp001010100011.list + horner X ep001010100011.list := by
  exact edge_identity (B := (2:ℤ)^281) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010100011 : Branch 1 (-1347761639/4000000 : ℚ) vp00101010001 := by
  apply branch_checked idp001010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1347761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1349761639/2000000 : ℚ) by norm_num]
  exact coverp001010100011
theorem coverp00101010001 : Covers (-1347761639/4000000 : ℚ) vp00101010001 := join_branches bp001010100010 bp001010100011
private noncomputable def vp0010101000011_0 : Blocks := edgeBlocks% "full/vectors/0010101000011-V-0000.bin"
noncomputable def vp0010101000011 : Blocks := vp0010101000011_0
theorem coverp0010101000011 : Covers (-1346761639/1000000 : ℚ) vp0010101000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101000010_0 : Blocks := edgeBlocks% "full/vectors/0010101000010-V-0000.bin"
noncomputable def vp0010101000010 : Blocks := vp0010101000010_0
theorem coverp0010101000010 : Covers (-1345761639/1000000 : ℚ) vp0010101000010 := cover_leaf (by decide +kernel)
private noncomputable def vp001010100001_0 : Blocks := edgeBlocks% "full/vectors/001010100001-V-0000.bin"
noncomputable def vp001010100001 : Blocks := vp001010100001_0
private theorem bp0010101000010 : Branch 0 (-1345761639/2000000 : ℚ) vp001010100001 := by
  apply branch_left_normalized (c:=vp0010101000010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1345761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1345761639/1000000 : ℚ) by norm_num]
  exact coverp0010101000010
private noncomputable def ep0010101000011_0 : Blocks := edgeBlocks% "full/vectors/0010101000011-E-0000.bin"
noncomputable def ep0010101000011 : Blocks := ep0010101000011_0
private theorem idp0010101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010100001.list =
    C ((2:ℤ)^78) * horner X vp0010101000011.list + horner X ep0010101000011.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101000011 : Branch 1 (-1345761639/2000000 : ℚ) vp001010100001 := by
  apply branch_checked idp0010101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1345761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1346761639/1000000 : ℚ) by norm_num]
  exact coverp0010101000011
theorem coverp001010100001 : Covers (-1345761639/2000000 : ℚ) vp001010100001 := join_branches bp0010101000010 bp0010101000011
private noncomputable def vp0010101000001_0 : Blocks := edgeBlocks% "full/vectors/0010101000001-V-0000.bin"
noncomputable def vp0010101000001 : Blocks := vp0010101000001_0
theorem coverp0010101000001 : Covers (-1344761639/1000000 : ℚ) vp0010101000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010101000000_0 : Blocks := edgeBlocks% "full/vectors/0010101000000-V-0000.bin"
noncomputable def vp0010101000000 : Blocks := vp0010101000000_0
theorem coverp0010101000000 : Covers (-1343761639/1000000 : ℚ) vp0010101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001010100000_0 : Blocks := edgeBlocks% "full/vectors/001010100000-V-0000.bin"
noncomputable def vp001010100000 : Blocks := vp001010100000_0
private theorem bp0010101000000 : Branch 0 (-1343761639/2000000 : ℚ) vp001010100000 := by
  apply branch_left_normalized (c:=vp0010101000000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1343761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1343761639/1000000 : ℚ) by norm_num]
  exact coverp0010101000000
private noncomputable def ep0010101000001_0 : Blocks := edgeBlocks% "full/vectors/0010101000001-E-0000.bin"
noncomputable def ep0010101000001 : Blocks := ep0010101000001_0
private theorem idp0010101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010100000.list =
    C ((2:ℤ)^80) * horner X vp0010101000001.list + horner X ep0010101000001.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101000001 : Branch 1 (-1343761639/2000000 : ℚ) vp001010100000 := by
  apply branch_checked idp0010101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1343761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1344761639/1000000 : ℚ) by norm_num]
  exact coverp0010101000001
theorem coverp001010100000 : Covers (-1343761639/2000000 : ℚ) vp001010100000 := join_branches bp0010101000000 bp0010101000001
private noncomputable def vp00101010000_0 : Blocks := edgeBlocks% "full/vectors/00101010000-V-0000.bin"
noncomputable def vp00101010000 : Blocks := vp00101010000_0
private theorem bp001010100000 : Branch 0 (-1343761639/4000000 : ℚ) vp00101010000 := by
  apply branch_left_normalized (c:=vp001010100000) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-1343761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1343761639/2000000 : ℚ) by norm_num]
  exact coverp001010100000
private noncomputable def ep001010100001_0 : Blocks := edgeBlocks% "full/vectors/001010100001-E-0000.bin"
noncomputable def ep001010100001 : Blocks := ep001010100001_0
private theorem idp001010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101010000.list =
    C ((2:ℤ)^140) * horner X vp001010100001.list + horner X ep001010100001.list := by
  exact edge_identity (B := (2:ℤ)^283) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010100001 : Branch 1 (-1343761639/4000000 : ℚ) vp00101010000 := by
  apply branch_checked idp001010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1343761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1345761639/2000000 : ℚ) by norm_num]
  exact coverp001010100001
theorem coverp00101010000 : Covers (-1343761639/4000000 : ℚ) vp00101010000 := join_branches bp001010100000 bp001010100001
private noncomputable def vp0010101000_0 : Blocks := edgeBlocks% "full/vectors/0010101000-V-0000.bin"
private noncomputable def vp0010101000_1 : Blocks := edgeBlocks% "full/vectors/0010101000-V-0001.bin"
noncomputable def vp0010101000 : Blocks := (Blocks.join vp0010101000_0 vp0010101000_1)
private theorem bp00101010000 : Branch 0 (-1343761639/8000000 : ℚ) vp0010101000 := by
  apply branch_left_normalized (c:=vp00101010000) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-1343761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1343761639/4000000 : ℚ) by norm_num]
  exact coverp00101010000
private noncomputable def ep00101010001_0 : Blocks := edgeBlocks% "full/vectors/00101010001-E-0000.bin"
private noncomputable def ep00101010001_1 : Blocks := edgeBlocks% "full/vectors/00101010001-E-0001.bin"
noncomputable def ep00101010001 : Blocks := (Blocks.join ep00101010001_0 ep00101010001_1)
private theorem idp00101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010101000.list =
    C ((2:ℤ)^260) * horner X vp00101010001.list + horner X ep00101010001.list := by
  exact edge_identity (B := (2:ℤ)^448) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101010001 : Branch 1 (-1343761639/8000000 : ℚ) vp0010101000 := by
  apply branch_checked idp00101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1343761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1347761639/4000000 : ℚ) by norm_num]
  exact coverp00101010001
theorem coverp0010101000 : Covers (-1343761639/8000000 : ℚ) vp0010101000 := join_branches bp00101010000 bp00101010001
private noncomputable def vp001010100_0 : Blocks := edgeBlocks% "full/vectors/001010100-V-0000.bin"
private noncomputable def vp001010100_1 : Blocks := edgeBlocks% "full/vectors/001010100-V-0001.bin"
private noncomputable def vp001010100_2 : Blocks := edgeBlocks% "full/vectors/001010100-V-0002.bin"
private noncomputable def vp001010100_3 : Blocks := edgeBlocks% "full/vectors/001010100-V-0003.bin"
noncomputable def vp001010100 : Blocks := (Blocks.join (Blocks.join vp001010100_0 vp001010100_1) (Blocks.join vp001010100_2 vp001010100_3))
private theorem bp0010101000 : Branch 0 (-1343761639/16000000 : ℚ) vp001010100 := by
  apply branch_left_normalized (c:=vp0010101000) (k:=0) (m:=235) (by decide +kernel)
  rw [show 2*(-1343761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1343761639/8000000 : ℚ) by norm_num]
  exact coverp0010101000
private noncomputable def ep0010101001_0 : Blocks := edgeBlocks% "full/vectors/0010101001-E-0000.bin"
private noncomputable def ep0010101001_1 : Blocks := edgeBlocks% "full/vectors/0010101001-E-0001.bin"
private noncomputable def ep0010101001_2 : Blocks := edgeBlocks% "full/vectors/0010101001-E-0002.bin"
private noncomputable def ep0010101001_3 : Blocks := edgeBlocks% "full/vectors/0010101001-E-0003.bin"
noncomputable def ep0010101001 : Blocks := (Blocks.join (Blocks.join ep0010101001_0 ep0010101001_1) (Blocks.join ep0010101001_2 ep0010101001_3))
private theorem idp0010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001010100.list =
    C ((2:ℤ)^492) * horner X vp0010101001.list + horner X ep0010101001.list := by
  exact edge_identity (B := (2:ℤ)^774) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010101001 : Branch 1 (-1343761639/16000000 : ℚ) vp001010100 := by
  apply branch_checked idp0010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1343761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1351761639/8000000 : ℚ) by norm_num]
  exact coverp0010101001
theorem coverp001010100 : Covers (-1343761639/16000000 : ℚ) vp001010100 := join_branches bp0010101000 bp0010101001
private noncomputable def vp00101010_0 : Blocks := edgeBlocks% "full/vectors/00101010-V-0000.bin"
private noncomputable def vp00101010_1 : Blocks := edgeBlocks% "full/vectors/00101010-V-0001.bin"
private noncomputable def vp00101010_2 : Blocks := edgeBlocks% "full/vectors/00101010-V-0002.bin"
private noncomputable def vp00101010_3 : Blocks := edgeBlocks% "full/vectors/00101010-V-0003.bin"
private noncomputable def vp00101010_4 : Blocks := edgeBlocks% "full/vectors/00101010-V-0004.bin"
private noncomputable def vp00101010_5 : Blocks := edgeBlocks% "full/vectors/00101010-V-0005.bin"
private noncomputable def vp00101010_6 : Blocks := edgeBlocks% "full/vectors/00101010-V-0006.bin"
noncomputable def vp00101010 : Blocks := (Blocks.join (Blocks.join vp00101010_0 (Blocks.join vp00101010_1 vp00101010_2)) (Blocks.join (Blocks.join vp00101010_3 vp00101010_4) (Blocks.join vp00101010_5 vp00101010_6)))
private theorem bp001010100 : Branch 0 (-1343761639/32000000 : ℚ) vp00101010 := by
  apply branch_left_normalized (c:=vp001010100) (k:=0) (m:=447) (by decide +kernel)
  rw [show 2*(-1343761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1343761639/16000000 : ℚ) by norm_num]
  exact coverp001010100
private noncomputable def ep001010101_0 : Blocks := edgeBlocks% "full/vectors/001010101-E-0000.bin"
private noncomputable def ep001010101_1 : Blocks := edgeBlocks% "full/vectors/001010101-E-0001.bin"
private noncomputable def ep001010101_2 : Blocks := edgeBlocks% "full/vectors/001010101-E-0002.bin"
private noncomputable def ep001010101_3 : Blocks := edgeBlocks% "full/vectors/001010101-E-0003.bin"
private noncomputable def ep001010101_4 : Blocks := edgeBlocks% "full/vectors/001010101-E-0004.bin"
private noncomputable def ep001010101_5 : Blocks := edgeBlocks% "full/vectors/001010101-E-0005.bin"
private noncomputable def ep001010101_6 : Blocks := edgeBlocks% "full/vectors/001010101-E-0006.bin"
noncomputable def ep001010101 : Blocks := (Blocks.join (Blocks.join ep001010101_0 (Blocks.join ep001010101_1 ep001010101_2)) (Blocks.join (Blocks.join ep001010101_3 ep001010101_4) (Blocks.join ep001010101_5 ep001010101_6)))
private theorem idp001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101010.list =
    C ((2:ℤ)^968) * horner X vp001010101.list + horner X ep001010101.list := by
  exact edge_identity (B := (2:ℤ)^1421) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001010101 : Branch 1 (-1343761639/32000000 : ℚ) vp00101010 := by
  apply branch_checked idp001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1343761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1359761639/16000000 : ℚ) by norm_num]
  exact coverp001010101
theorem coverp00101010 : Covers (-1343761639/32000000 : ℚ) vp00101010 := join_branches bp001010100 bp001010101
private noncomputable def vp0010101_0 : Blocks := edgeBlocks% "full/vectors/0010101-V-0000.bin"
private noncomputable def vp0010101_1 : Blocks := edgeBlocks% "full/vectors/0010101-V-0001.bin"
private noncomputable def vp0010101_2 : Blocks := edgeBlocks% "full/vectors/0010101-V-0002.bin"
private noncomputable def vp0010101_3 : Blocks := edgeBlocks% "full/vectors/0010101-V-0003.bin"
private noncomputable def vp0010101_4 : Blocks := edgeBlocks% "full/vectors/0010101-V-0004.bin"
private noncomputable def vp0010101_5 : Blocks := edgeBlocks% "full/vectors/0010101-V-0005.bin"
private noncomputable def vp0010101_6 : Blocks := edgeBlocks% "full/vectors/0010101-V-0006.bin"
private noncomputable def vp0010101_7 : Blocks := edgeBlocks% "full/vectors/0010101-V-0007.bin"
private noncomputable def vp0010101_8 : Blocks := edgeBlocks% "full/vectors/0010101-V-0008.bin"
private noncomputable def vp0010101_9 : Blocks := edgeBlocks% "full/vectors/0010101-V-0009.bin"
private noncomputable def vp0010101_10 : Blocks := edgeBlocks% "full/vectors/0010101-V-0010.bin"
private noncomputable def vp0010101_11 : Blocks := edgeBlocks% "full/vectors/0010101-V-0011.bin"
private noncomputable def vp0010101_12 : Blocks := edgeBlocks% "full/vectors/0010101-V-0012.bin"
private noncomputable def vp0010101_13 : Blocks := edgeBlocks% "full/vectors/0010101-V-0013.bin"
noncomputable def vp0010101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0010101_0 (Blocks.join vp0010101_1 vp0010101_2)) (Blocks.join (Blocks.join vp0010101_3 vp0010101_4) (Blocks.join vp0010101_5 vp0010101_6))) (Blocks.join (Blocks.join vp0010101_7 (Blocks.join vp0010101_8 vp0010101_9)) (Blocks.join (Blocks.join vp0010101_10 vp0010101_11) (Blocks.join vp0010101_12 vp0010101_13))))
private theorem bp00101010 : Branch 0 (-1343761639/64000000 : ℚ) vp0010101 := by
  apply branch_left_normalized (c:=vp00101010) (k:=0) (m:=868) (by decide +kernel)
  rw [show 2*(-1343761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1343761639/32000000 : ℚ) by norm_num]
  exact coverp00101010
private noncomputable def ep00101011_0 : Blocks := edgeBlocks% "full/vectors/00101011-E-0000.bin"
private noncomputable def ep00101011_1 : Blocks := edgeBlocks% "full/vectors/00101011-E-0001.bin"
private noncomputable def ep00101011_2 : Blocks := edgeBlocks% "full/vectors/00101011-E-0002.bin"
private noncomputable def ep00101011_3 : Blocks := edgeBlocks% "full/vectors/00101011-E-0003.bin"
private noncomputable def ep00101011_4 : Blocks := edgeBlocks% "full/vectors/00101011-E-0004.bin"
private noncomputable def ep00101011_5 : Blocks := edgeBlocks% "full/vectors/00101011-E-0005.bin"
private noncomputable def ep00101011_6 : Blocks := edgeBlocks% "full/vectors/00101011-E-0006.bin"
private noncomputable def ep00101011_7 : Blocks := edgeBlocks% "full/vectors/00101011-E-0007.bin"
private noncomputable def ep00101011_8 : Blocks := edgeBlocks% "full/vectors/00101011-E-0008.bin"
private noncomputable def ep00101011_9 : Blocks := edgeBlocks% "full/vectors/00101011-E-0009.bin"
private noncomputable def ep00101011_10 : Blocks := edgeBlocks% "full/vectors/00101011-E-0010.bin"
private noncomputable def ep00101011_11 : Blocks := edgeBlocks% "full/vectors/00101011-E-0011.bin"
private noncomputable def ep00101011_12 : Blocks := edgeBlocks% "full/vectors/00101011-E-0012.bin"
private noncomputable def ep00101011_13 : Blocks := edgeBlocks% "full/vectors/00101011-E-0013.bin"
noncomputable def ep00101011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00101011_0 (Blocks.join ep00101011_1 ep00101011_2)) (Blocks.join (Blocks.join ep00101011_3 ep00101011_4) (Blocks.join ep00101011_5 ep00101011_6))) (Blocks.join (Blocks.join ep00101011_7 (Blocks.join ep00101011_8 ep00101011_9)) (Blocks.join (Blocks.join ep00101011_10 ep00101011_11) (Blocks.join ep00101011_12 ep00101011_13))))
private theorem idp00101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010101.list =
    C ((2:ℤ)^1886) * horner X vp00101011.list + horner X ep00101011.list := by
  exact edge_identity (B := (2:ℤ)^2695) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101011 : Branch 1 (-1343761639/64000000 : ℚ) vp0010101 := by
  apply branch_checked idp00101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1343761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1375761639/32000000 : ℚ) by norm_num]
  exact coverp00101011
theorem coverp0010101 : Covers (-1343761639/64000000 : ℚ) vp0010101 := join_branches bp00101010 bp00101011
end NextProof.EdgeFull

