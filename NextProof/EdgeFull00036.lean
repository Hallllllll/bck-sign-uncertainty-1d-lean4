import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00035

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000000110111111_0 : Blocks := edgeBlocks% "full/vectors/000000110111111-V-0000.bin"
noncomputable def vp000000110111111 : Blocks := vp000000110111111_0
theorem coverp000000110111111 : Covers (-111511639/250000 : ℚ) vp000000110111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110111110_0 : Blocks := edgeBlocks% "full/vectors/000000110111110-V-0000.bin"
noncomputable def vp000000110111110 : Blocks := vp000000110111110_0
theorem coverp000000110111110 : Covers (-111261639/250000 : ℚ) vp000000110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011011111_0 : Blocks := edgeBlocks% "full/vectors/00000011011111-V-0000.bin"
noncomputable def vp00000011011111 : Blocks := vp00000011011111_0
private theorem bp000000110111110 : Branch 0 (-111261639/500000 : ℚ) vp00000011011111 := by
  apply branch_left_normalized (c:=vp000000110111110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-111261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-111261639/250000 : ℚ) by norm_num]
  exact coverp000000110111110
private noncomputable def ep000000110111111_0 : Blocks := edgeBlocks% "full/vectors/000000110111111-E-0000.bin"
noncomputable def ep000000110111111 : Blocks := ep000000110111111_0
private theorem idp000000110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011011111.list =
    C ((2:ℤ)^70) * horner X vp000000110111111.list + horner X ep000000110111111.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110111111 : Branch 1 (-111261639/500000 : ℚ) vp00000011011111 := by
  apply branch_checked idp000000110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-111261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-111511639/250000 : ℚ) by norm_num]
  exact coverp000000110111111
theorem coverp00000011011111 : Covers (-111261639/500000 : ℚ) vp00000011011111 := join_branches bp000000110111110 bp000000110111111
private noncomputable def vp000000110111101_0 : Blocks := edgeBlocks% "full/vectors/000000110111101-V-0000.bin"
noncomputable def vp000000110111101 : Blocks := vp000000110111101_0
theorem coverp000000110111101 : Covers (-111011639/250000 : ℚ) vp000000110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101111001_0 : Blocks := edgeBlocks% "full/vectors/0000001101111001-V-0000.bin"
noncomputable def vp0000001101111001 : Blocks := vp0000001101111001_0
theorem coverp0000001101111001 : Covers (-110886639/125000 : ℚ) vp0000001101111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101111000_0 : Blocks := edgeBlocks% "full/vectors/0000001101111000-V-0000.bin"
noncomputable def vp0000001101111000 : Blocks := vp0000001101111000_0
theorem coverp0000001101111000 : Covers (-110761639/125000 : ℚ) vp0000001101111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110111100_0 : Blocks := edgeBlocks% "full/vectors/000000110111100-V-0000.bin"
noncomputable def vp000000110111100 : Blocks := vp000000110111100_0
private theorem bp0000001101111000 : Branch 0 (-110761639/250000 : ℚ) vp000000110111100 := by
  apply branch_left_normalized (c:=vp0000001101111000) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-110761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-110761639/125000 : ℚ) by norm_num]
  exact coverp0000001101111000
private noncomputable def ep0000001101111001_0 : Blocks := edgeBlocks% "full/vectors/0000001101111001-E-0000.bin"
noncomputable def ep0000001101111001 : Blocks := ep0000001101111001_0
private theorem idp0000001101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110111100.list =
    C ((2:ℤ)^44) * horner X vp0000001101111001.list + horner X ep0000001101111001.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101111001 : Branch 1 (-110761639/250000 : ℚ) vp000000110111100 := by
  apply branch_checked idp0000001101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-110761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-110886639/125000 : ℚ) by norm_num]
  exact coverp0000001101111001
theorem coverp000000110111100 : Covers (-110761639/250000 : ℚ) vp000000110111100 := join_branches bp0000001101111000 bp0000001101111001
private noncomputable def vp00000011011110_0 : Blocks := edgeBlocks% "full/vectors/00000011011110-V-0000.bin"
noncomputable def vp00000011011110 : Blocks := vp00000011011110_0
private theorem bp000000110111100 : Branch 0 (-110761639/500000 : ℚ) vp00000011011110 := by
  apply branch_left_normalized (c:=vp000000110111100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-110761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-110761639/250000 : ℚ) by norm_num]
  exact coverp000000110111100
private noncomputable def ep000000110111101_0 : Blocks := edgeBlocks% "full/vectors/000000110111101-E-0000.bin"
noncomputable def ep000000110111101 : Blocks := ep000000110111101_0
private theorem idp000000110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011011110.list =
    C ((2:ℤ)^70) * horner X vp000000110111101.list + horner X ep000000110111101.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110111101 : Branch 1 (-110761639/500000 : ℚ) vp00000011011110 := by
  apply branch_checked idp000000110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-110761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-111011639/250000 : ℚ) by norm_num]
  exact coverp000000110111101
theorem coverp00000011011110 : Covers (-110761639/500000 : ℚ) vp00000011011110 := join_branches bp000000110111100 bp000000110111101
private noncomputable def vp0000001101111_0 : Blocks := edgeBlocks% "full/vectors/0000001101111-V-0000.bin"
noncomputable def vp0000001101111 : Blocks := vp0000001101111_0
private theorem bp00000011011110 : Branch 0 (-110761639/1000000 : ℚ) vp0000001101111 := by
  apply branch_left_normalized (c:=vp00000011011110) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-110761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-110761639/500000 : ℚ) by norm_num]
  exact coverp00000011011110
private noncomputable def ep00000011011111_0 : Blocks := edgeBlocks% "full/vectors/00000011011111-E-0000.bin"
noncomputable def ep00000011011111 : Blocks := ep00000011011111_0
private theorem idp00000011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001101111.list =
    C ((2:ℤ)^120) * horner X vp00000011011111.list + horner X ep00000011011111.list := by
  exact edge_identity (B := (2:ℤ)^268) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011011111 : Branch 1 (-110761639/1000000 : ℚ) vp0000001101111 := by
  apply branch_checked idp00000011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-110761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-111261639/500000 : ℚ) by norm_num]
  exact coverp00000011011111
theorem coverp0000001101111 : Covers (-110761639/1000000 : ℚ) vp0000001101111 := join_branches bp00000011011110 bp00000011011111
private noncomputable def vp0000001101110111_0 : Blocks := edgeBlocks% "full/vectors/0000001101110111-V-0000.bin"
noncomputable def vp0000001101110111 : Blocks := vp0000001101110111_0
theorem coverp0000001101110111 : Covers (-110636639/125000 : ℚ) vp0000001101110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101110110_0 : Blocks := edgeBlocks% "full/vectors/0000001101110110-V-0000.bin"
noncomputable def vp0000001101110110 : Blocks := vp0000001101110110_0
theorem coverp0000001101110110 : Covers (-110511639/125000 : ℚ) vp0000001101110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110111011_0 : Blocks := edgeBlocks% "full/vectors/000000110111011-V-0000.bin"
noncomputable def vp000000110111011 : Blocks := vp000000110111011_0
private theorem bp0000001101110110 : Branch 0 (-110511639/250000 : ℚ) vp000000110111011 := by
  apply branch_left_normalized (c:=vp0000001101110110) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-110511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-110511639/125000 : ℚ) by norm_num]
  exact coverp0000001101110110
private noncomputable def ep0000001101110111_0 : Blocks := edgeBlocks% "full/vectors/0000001101110111-E-0000.bin"
noncomputable def ep0000001101110111 : Blocks := ep0000001101110111_0
private theorem idp0000001101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110111011.list =
    C ((2:ℤ)^44) * horner X vp0000001101110111.list + horner X ep0000001101110111.list := by
  exact edge_identity (B := (2:ℤ)^159) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101110111 : Branch 1 (-110511639/250000 : ℚ) vp000000110111011 := by
  apply branch_checked idp0000001101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-110511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-110636639/125000 : ℚ) by norm_num]
  exact coverp0000001101110111
theorem coverp000000110111011 : Covers (-110511639/250000 : ℚ) vp000000110111011 := join_branches bp0000001101110110 bp0000001101110111
private noncomputable def vp0000001101110101_0 : Blocks := edgeBlocks% "full/vectors/0000001101110101-V-0000.bin"
noncomputable def vp0000001101110101 : Blocks := vp0000001101110101_0
theorem coverp0000001101110101 : Covers (-110386639/125000 : ℚ) vp0000001101110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101110100_0 : Blocks := edgeBlocks% "full/vectors/0000001101110100-V-0000.bin"
noncomputable def vp0000001101110100 : Blocks := vp0000001101110100_0
theorem coverp0000001101110100 : Covers (-110261639/125000 : ℚ) vp0000001101110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110111010_0 : Blocks := edgeBlocks% "full/vectors/000000110111010-V-0000.bin"
noncomputable def vp000000110111010 : Blocks := vp000000110111010_0
private theorem bp0000001101110100 : Branch 0 (-110261639/250000 : ℚ) vp000000110111010 := by
  apply branch_left_normalized (c:=vp0000001101110100) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-110261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-110261639/125000 : ℚ) by norm_num]
  exact coverp0000001101110100
private noncomputable def ep0000001101110101_0 : Blocks := edgeBlocks% "full/vectors/0000001101110101-E-0000.bin"
noncomputable def ep0000001101110101 : Blocks := ep0000001101110101_0
private theorem idp0000001101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110111010.list =
    C ((2:ℤ)^43) * horner X vp0000001101110101.list + horner X ep0000001101110101.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101110101 : Branch 1 (-110261639/250000 : ℚ) vp000000110111010 := by
  apply branch_checked idp0000001101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-110261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-110386639/125000 : ℚ) by norm_num]
  exact coverp0000001101110101
theorem coverp000000110111010 : Covers (-110261639/250000 : ℚ) vp000000110111010 := join_branches bp0000001101110100 bp0000001101110101
private noncomputable def vp00000011011101_0 : Blocks := edgeBlocks% "full/vectors/00000011011101-V-0000.bin"
noncomputable def vp00000011011101 : Blocks := vp00000011011101_0
private theorem bp000000110111010 : Branch 0 (-110261639/500000 : ℚ) vp00000011011101 := by
  apply branch_left_normalized (c:=vp000000110111010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-110261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-110261639/250000 : ℚ) by norm_num]
  exact coverp000000110111010
private noncomputable def ep000000110111011_0 : Blocks := edgeBlocks% "full/vectors/000000110111011-E-0000.bin"
noncomputable def ep000000110111011 : Blocks := ep000000110111011_0
private theorem idp000000110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011011101.list =
    C ((2:ℤ)^69) * horner X vp000000110111011.list + horner X ep000000110111011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110111011 : Branch 1 (-110261639/500000 : ℚ) vp00000011011101 := by
  apply branch_checked idp000000110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-110261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-110511639/250000 : ℚ) by norm_num]
  exact coverp000000110111011
theorem coverp00000011011101 : Covers (-110261639/500000 : ℚ) vp00000011011101 := join_branches bp000000110111010 bp000000110111011
private noncomputable def vp0000001101110011_0 : Blocks := edgeBlocks% "full/vectors/0000001101110011-V-0000.bin"
noncomputable def vp0000001101110011 : Blocks := vp0000001101110011_0
theorem coverp0000001101110011 : Covers (-110136639/125000 : ℚ) vp0000001101110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101110010_0 : Blocks := edgeBlocks% "full/vectors/0000001101110010-V-0000.bin"
noncomputable def vp0000001101110010 : Blocks := vp0000001101110010_0
theorem coverp0000001101110010 : Covers (-110011639/125000 : ℚ) vp0000001101110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110111001_0 : Blocks := edgeBlocks% "full/vectors/000000110111001-V-0000.bin"
noncomputable def vp000000110111001 : Blocks := vp000000110111001_0
private theorem bp0000001101110010 : Branch 0 (-110011639/250000 : ℚ) vp000000110111001 := by
  apply branch_left_normalized (c:=vp0000001101110010) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-110011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-110011639/125000 : ℚ) by norm_num]
  exact coverp0000001101110010
private noncomputable def ep0000001101110011_0 : Blocks := edgeBlocks% "full/vectors/0000001101110011-E-0000.bin"
noncomputable def ep0000001101110011 : Blocks := ep0000001101110011_0
private theorem idp0000001101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110111001.list =
    C ((2:ℤ)^44) * horner X vp0000001101110011.list + horner X ep0000001101110011.list := by
  exact edge_identity (B := (2:ℤ)^159) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101110011 : Branch 1 (-110011639/250000 : ℚ) vp000000110111001 := by
  apply branch_checked idp0000001101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-110011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-110136639/125000 : ℚ) by norm_num]
  exact coverp0000001101110011
theorem coverp000000110111001 : Covers (-110011639/250000 : ℚ) vp000000110111001 := join_branches bp0000001101110010 bp0000001101110011
private noncomputable def vp0000001101110001_0 : Blocks := edgeBlocks% "full/vectors/0000001101110001-V-0000.bin"
noncomputable def vp0000001101110001 : Blocks := vp0000001101110001_0
theorem coverp0000001101110001 : Covers (-109886639/125000 : ℚ) vp0000001101110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101110000_0 : Blocks := edgeBlocks% "full/vectors/0000001101110000-V-0000.bin"
noncomputable def vp0000001101110000 : Blocks := vp0000001101110000_0
theorem coverp0000001101110000 : Covers (-109761639/125000 : ℚ) vp0000001101110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110111000_0 : Blocks := edgeBlocks% "full/vectors/000000110111000-V-0000.bin"
noncomputable def vp000000110111000 : Blocks := vp000000110111000_0
private theorem bp0000001101110000 : Branch 0 (-109761639/250000 : ℚ) vp000000110111000 := by
  apply branch_left_normalized (c:=vp0000001101110000) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-109761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-109761639/125000 : ℚ) by norm_num]
  exact coverp0000001101110000
private noncomputable def ep0000001101110001_0 : Blocks := edgeBlocks% "full/vectors/0000001101110001-E-0000.bin"
noncomputable def ep0000001101110001 : Blocks := ep0000001101110001_0
private theorem idp0000001101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110111000.list =
    C ((2:ℤ)^43) * horner X vp0000001101110001.list + horner X ep0000001101110001.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101110001 : Branch 1 (-109761639/250000 : ℚ) vp000000110111000 := by
  apply branch_checked idp0000001101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-109761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-109886639/125000 : ℚ) by norm_num]
  exact coverp0000001101110001
theorem coverp000000110111000 : Covers (-109761639/250000 : ℚ) vp000000110111000 := join_branches bp0000001101110000 bp0000001101110001
private noncomputable def vp00000011011100_0 : Blocks := edgeBlocks% "full/vectors/00000011011100-V-0000.bin"
noncomputable def vp00000011011100 : Blocks := vp00000011011100_0
private theorem bp000000110111000 : Branch 0 (-109761639/500000 : ℚ) vp00000011011100 := by
  apply branch_left_normalized (c:=vp000000110111000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-109761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-109761639/250000 : ℚ) by norm_num]
  exact coverp000000110111000
private noncomputable def ep000000110111001_0 : Blocks := edgeBlocks% "full/vectors/000000110111001-E-0000.bin"
noncomputable def ep000000110111001 : Blocks := ep000000110111001_0
private theorem idp000000110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011011100.list =
    C ((2:ℤ)^68) * horner X vp000000110111001.list + horner X ep000000110111001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110111001 : Branch 1 (-109761639/500000 : ℚ) vp00000011011100 := by
  apply branch_checked idp000000110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-109761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-110011639/250000 : ℚ) by norm_num]
  exact coverp000000110111001
theorem coverp00000011011100 : Covers (-109761639/500000 : ℚ) vp00000011011100 := join_branches bp000000110111000 bp000000110111001
private noncomputable def vp0000001101110_0 : Blocks := edgeBlocks% "full/vectors/0000001101110-V-0000.bin"
noncomputable def vp0000001101110 : Blocks := vp0000001101110_0
private theorem bp00000011011100 : Branch 0 (-109761639/1000000 : ℚ) vp0000001101110 := by
  apply branch_left_normalized (c:=vp00000011011100) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-109761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-109761639/500000 : ℚ) by norm_num]
  exact coverp00000011011100
private noncomputable def ep00000011011101_0 : Blocks := edgeBlocks% "full/vectors/00000011011101-E-0000.bin"
noncomputable def ep00000011011101 : Blocks := ep00000011011101_0
private theorem idp00000011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001101110.list =
    C ((2:ℤ)^118) * horner X vp00000011011101.list + horner X ep00000011011101.list := by
  exact edge_identity (B := (2:ℤ)^267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011011101 : Branch 1 (-109761639/1000000 : ℚ) vp0000001101110 := by
  apply branch_checked idp00000011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-109761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-110261639/500000 : ℚ) by norm_num]
  exact coverp00000011011101
theorem coverp0000001101110 : Covers (-109761639/1000000 : ℚ) vp0000001101110 := join_branches bp00000011011100 bp00000011011101
private noncomputable def vp000000110111_0 : Blocks := edgeBlocks% "full/vectors/000000110111-V-0000.bin"
private noncomputable def vp000000110111_1 : Blocks := edgeBlocks% "full/vectors/000000110111-V-0001.bin"
noncomputable def vp000000110111 : Blocks := (Blocks.join vp000000110111_0 vp000000110111_1)
private theorem bp0000001101110 : Branch 0 (-109761639/2000000 : ℚ) vp000000110111 := by
  apply branch_left_normalized (c:=vp0000001101110) (k:=0) (m:=115) (by decide +kernel)
  rw [show 2*(-109761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-109761639/1000000 : ℚ) by norm_num]
  exact coverp0000001101110
private noncomputable def ep0000001101111_0 : Blocks := edgeBlocks% "full/vectors/0000001101111-E-0000.bin"
private noncomputable def ep0000001101111_1 : Blocks := edgeBlocks% "full/vectors/0000001101111-E-0001.bin"
noncomputable def ep0000001101111 : Blocks := (Blocks.join ep0000001101111_0 ep0000001101111_1)
private theorem idp0000001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110111.list =
    C ((2:ℤ)^216) * horner X vp0000001101111.list + horner X ep0000001101111.list := by
  exact edge_identity (B := (2:ℤ)^412) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101111 : Branch 1 (-109761639/2000000 : ℚ) vp000000110111 := by
  apply branch_checked idp0000001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-109761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-110761639/1000000 : ℚ) by norm_num]
  exact coverp0000001101111
theorem coverp000000110111 : Covers (-109761639/2000000 : ℚ) vp000000110111 := join_branches bp0000001101110 bp0000001101111
private noncomputable def vp0000001101101111_0 : Blocks := edgeBlocks% "full/vectors/0000001101101111-V-0000.bin"
noncomputable def vp0000001101101111 : Blocks := vp0000001101101111_0
theorem coverp0000001101101111 : Covers (-109636639/125000 : ℚ) vp0000001101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101101110_0 : Blocks := edgeBlocks% "full/vectors/0000001101101110-V-0000.bin"
noncomputable def vp0000001101101110 : Blocks := vp0000001101101110_0
theorem coverp0000001101101110 : Covers (-109511639/125000 : ℚ) vp0000001101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110110111_0 : Blocks := edgeBlocks% "full/vectors/000000110110111-V-0000.bin"
noncomputable def vp000000110110111 : Blocks := vp000000110110111_0
private theorem bp0000001101101110 : Branch 0 (-109511639/250000 : ℚ) vp000000110110111 := by
  apply branch_left_normalized (c:=vp0000001101101110) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-109511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-109511639/125000 : ℚ) by norm_num]
  exact coverp0000001101101110
private noncomputable def ep0000001101101111_0 : Blocks := edgeBlocks% "full/vectors/0000001101101111-E-0000.bin"
noncomputable def ep0000001101101111 : Blocks := ep0000001101101111_0
private theorem idp0000001101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110110111.list =
    C ((2:ℤ)^43) * horner X vp0000001101101111.list + horner X ep0000001101101111.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101101111 : Branch 1 (-109511639/250000 : ℚ) vp000000110110111 := by
  apply branch_checked idp0000001101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-109511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-109636639/125000 : ℚ) by norm_num]
  exact coverp0000001101101111
theorem coverp000000110110111 : Covers (-109511639/250000 : ℚ) vp000000110110111 := join_branches bp0000001101101110 bp0000001101101111
private noncomputable def vp0000001101101101_0 : Blocks := edgeBlocks% "full/vectors/0000001101101101-V-0000.bin"
noncomputable def vp0000001101101101 : Blocks := vp0000001101101101_0
theorem coverp0000001101101101 : Covers (-109386639/125000 : ℚ) vp0000001101101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101101100_0 : Blocks := edgeBlocks% "full/vectors/0000001101101100-V-0000.bin"
noncomputable def vp0000001101101100 : Blocks := vp0000001101101100_0
theorem coverp0000001101101100 : Covers (-109261639/125000 : ℚ) vp0000001101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110110110_0 : Blocks := edgeBlocks% "full/vectors/000000110110110-V-0000.bin"
noncomputable def vp000000110110110 : Blocks := vp000000110110110_0
private theorem bp0000001101101100 : Branch 0 (-109261639/250000 : ℚ) vp000000110110110 := by
  apply branch_left_normalized (c:=vp0000001101101100) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-109261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-109261639/125000 : ℚ) by norm_num]
  exact coverp0000001101101100
private noncomputable def ep0000001101101101_0 : Blocks := edgeBlocks% "full/vectors/0000001101101101-E-0000.bin"
noncomputable def ep0000001101101101 : Blocks := ep0000001101101101_0
private theorem idp0000001101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110110110.list =
    C ((2:ℤ)^42) * horner X vp0000001101101101.list + horner X ep0000001101101101.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101101101 : Branch 1 (-109261639/250000 : ℚ) vp000000110110110 := by
  apply branch_checked idp0000001101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-109261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-109386639/125000 : ℚ) by norm_num]
  exact coverp0000001101101101
theorem coverp000000110110110 : Covers (-109261639/250000 : ℚ) vp000000110110110 := join_branches bp0000001101101100 bp0000001101101101
private noncomputable def vp00000011011011_0 : Blocks := edgeBlocks% "full/vectors/00000011011011-V-0000.bin"
noncomputable def vp00000011011011 : Blocks := vp00000011011011_0
private theorem bp000000110110110 : Branch 0 (-109261639/500000 : ℚ) vp00000011011011 := by
  apply branch_left_normalized (c:=vp000000110110110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-109261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-109261639/250000 : ℚ) by norm_num]
  exact coverp000000110110110
private noncomputable def ep000000110110111_0 : Blocks := edgeBlocks% "full/vectors/000000110110111-E-0000.bin"
noncomputable def ep000000110110111 : Blocks := ep000000110110111_0
private theorem idp000000110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011011011.list =
    C ((2:ℤ)^69) * horner X vp000000110110111.list + horner X ep000000110110111.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110110111 : Branch 1 (-109261639/500000 : ℚ) vp00000011011011 := by
  apply branch_checked idp000000110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-109261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-109511639/250000 : ℚ) by norm_num]
  exact coverp000000110110111
theorem coverp00000011011011 : Covers (-109261639/500000 : ℚ) vp00000011011011 := join_branches bp000000110110110 bp000000110110111
private noncomputable def vp000000110110101_0 : Blocks := edgeBlocks% "full/vectors/000000110110101-V-0000.bin"
noncomputable def vp000000110110101 : Blocks := vp000000110110101_0
theorem coverp000000110110101 : Covers (-109011639/250000 : ℚ) vp000000110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110110100_0 : Blocks := edgeBlocks% "full/vectors/000000110110100-V-0000.bin"
noncomputable def vp000000110110100 : Blocks := vp000000110110100_0
theorem coverp000000110110100 : Covers (-108761639/250000 : ℚ) vp000000110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011011010_0 : Blocks := edgeBlocks% "full/vectors/00000011011010-V-0000.bin"
noncomputable def vp00000011011010 : Blocks := vp00000011011010_0
private theorem bp000000110110100 : Branch 0 (-108761639/500000 : ℚ) vp00000011011010 := by
  apply branch_left_normalized (c:=vp000000110110100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-108761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-108761639/250000 : ℚ) by norm_num]
  exact coverp000000110110100
private noncomputable def ep000000110110101_0 : Blocks := edgeBlocks% "full/vectors/000000110110101-E-0000.bin"
noncomputable def ep000000110110101 : Blocks := ep000000110110101_0
private theorem idp000000110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011011010.list =
    C ((2:ℤ)^69) * horner X vp000000110110101.list + horner X ep000000110110101.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110110101 : Branch 1 (-108761639/500000 : ℚ) vp00000011011010 := by
  apply branch_checked idp000000110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-108761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-109011639/250000 : ℚ) by norm_num]
  exact coverp000000110110101
theorem coverp00000011011010 : Covers (-108761639/500000 : ℚ) vp00000011011010 := join_branches bp000000110110100 bp000000110110101
private noncomputable def vp0000001101101_0 : Blocks := edgeBlocks% "full/vectors/0000001101101-V-0000.bin"
noncomputable def vp0000001101101 : Blocks := vp0000001101101_0
private theorem bp00000011011010 : Branch 0 (-108761639/1000000 : ℚ) vp0000001101101 := by
  apply branch_left_normalized (c:=vp00000011011010) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-108761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-108761639/500000 : ℚ) by norm_num]
  exact coverp00000011011010
private noncomputable def ep00000011011011_0 : Blocks := edgeBlocks% "full/vectors/00000011011011-E-0000.bin"
noncomputable def ep00000011011011 : Blocks := ep00000011011011_0
private theorem idp00000011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001101101.list =
    C ((2:ℤ)^119) * horner X vp00000011011011.list + horner X ep00000011011011.list := by
  exact edge_identity (B := (2:ℤ)^267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011011011 : Branch 1 (-108761639/1000000 : ℚ) vp0000001101101 := by
  apply branch_checked idp00000011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-108761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-109261639/500000 : ℚ) by norm_num]
  exact coverp00000011011011
theorem coverp0000001101101 : Covers (-108761639/1000000 : ℚ) vp0000001101101 := join_branches bp00000011011010 bp00000011011011
private noncomputable def vp000000110110011_0 : Blocks := edgeBlocks% "full/vectors/000000110110011-V-0000.bin"
noncomputable def vp000000110110011 : Blocks := vp000000110110011_0
theorem coverp000000110110011 : Covers (-108511639/250000 : ℚ) vp000000110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110110010_0 : Blocks := edgeBlocks% "full/vectors/000000110110010-V-0000.bin"
noncomputable def vp000000110110010 : Blocks := vp000000110110010_0
theorem coverp000000110110010 : Covers (-108261639/250000 : ℚ) vp000000110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011011001_0 : Blocks := edgeBlocks% "full/vectors/00000011011001-V-0000.bin"
noncomputable def vp00000011011001 : Blocks := vp00000011011001_0
private theorem bp000000110110010 : Branch 0 (-108261639/500000 : ℚ) vp00000011011001 := by
  apply branch_left_normalized (c:=vp000000110110010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-108261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-108261639/250000 : ℚ) by norm_num]
  exact coverp000000110110010
private noncomputable def ep000000110110011_0 : Blocks := edgeBlocks% "full/vectors/000000110110011-E-0000.bin"
noncomputable def ep000000110110011 : Blocks := ep000000110110011_0
private theorem idp000000110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011011001.list =
    C ((2:ℤ)^69) * horner X vp000000110110011.list + horner X ep000000110110011.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110110011 : Branch 1 (-108261639/500000 : ℚ) vp00000011011001 := by
  apply branch_checked idp000000110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-108261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-108511639/250000 : ℚ) by norm_num]
  exact coverp000000110110011
theorem coverp00000011011001 : Covers (-108261639/500000 : ℚ) vp00000011011001 := join_branches bp000000110110010 bp000000110110011
private noncomputable def vp000000110110001_0 : Blocks := edgeBlocks% "full/vectors/000000110110001-V-0000.bin"
noncomputable def vp000000110110001 : Blocks := vp000000110110001_0
theorem coverp000000110110001 : Covers (-108011639/250000 : ℚ) vp000000110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101100001_0 : Blocks := edgeBlocks% "full/vectors/0000001101100001-V-0000.bin"
noncomputable def vp0000001101100001 : Blocks := vp0000001101100001_0
theorem coverp0000001101100001 : Covers (-107886639/125000 : ℚ) vp0000001101100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101100000_0 : Blocks := edgeBlocks% "full/vectors/0000001101100000-V-0000.bin"
noncomputable def vp0000001101100000 : Blocks := vp0000001101100000_0
theorem coverp0000001101100000 : Covers (-107761639/125000 : ℚ) vp0000001101100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110110000_0 : Blocks := edgeBlocks% "full/vectors/000000110110000-V-0000.bin"
noncomputable def vp000000110110000 : Blocks := vp000000110110000_0
private theorem bp0000001101100000 : Branch 0 (-107761639/250000 : ℚ) vp000000110110000 := by
  apply branch_left_normalized (c:=vp0000001101100000) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-107761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-107761639/125000 : ℚ) by norm_num]
  exact coverp0000001101100000
private noncomputable def ep0000001101100001_0 : Blocks := edgeBlocks% "full/vectors/0000001101100001-E-0000.bin"
noncomputable def ep0000001101100001 : Blocks := ep0000001101100001_0
private theorem idp0000001101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110110000.list =
    C ((2:ℤ)^44) * horner X vp0000001101100001.list + horner X ep0000001101100001.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101100001 : Branch 1 (-107761639/250000 : ℚ) vp000000110110000 := by
  apply branch_checked idp0000001101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-107761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-107886639/125000 : ℚ) by norm_num]
  exact coverp0000001101100001
theorem coverp000000110110000 : Covers (-107761639/250000 : ℚ) vp000000110110000 := join_branches bp0000001101100000 bp0000001101100001
private noncomputable def vp00000011011000_0 : Blocks := edgeBlocks% "full/vectors/00000011011000-V-0000.bin"
noncomputable def vp00000011011000 : Blocks := vp00000011011000_0
private theorem bp000000110110000 : Branch 0 (-107761639/500000 : ℚ) vp00000011011000 := by
  apply branch_left_normalized (c:=vp000000110110000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-107761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-107761639/250000 : ℚ) by norm_num]
  exact coverp000000110110000
private noncomputable def ep000000110110001_0 : Blocks := edgeBlocks% "full/vectors/000000110110001-E-0000.bin"
noncomputable def ep000000110110001 : Blocks := ep000000110110001_0
private theorem idp000000110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011011000.list =
    C ((2:ℤ)^71) * horner X vp000000110110001.list + horner X ep000000110110001.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110110001 : Branch 1 (-107761639/500000 : ℚ) vp00000011011000 := by
  apply branch_checked idp000000110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-107761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-108011639/250000 : ℚ) by norm_num]
  exact coverp000000110110001
theorem coverp00000011011000 : Covers (-107761639/500000 : ℚ) vp00000011011000 := join_branches bp000000110110000 bp000000110110001
private noncomputable def vp0000001101100_0 : Blocks := edgeBlocks% "full/vectors/0000001101100-V-0000.bin"
noncomputable def vp0000001101100 : Blocks := vp0000001101100_0
private theorem bp00000011011000 : Branch 0 (-107761639/1000000 : ℚ) vp0000001101100 := by
  apply branch_left_normalized (c:=vp00000011011000) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-107761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-107761639/500000 : ℚ) by norm_num]
  exact coverp00000011011000
private noncomputable def ep00000011011001_0 : Blocks := edgeBlocks% "full/vectors/00000011011001-E-0000.bin"
noncomputable def ep00000011011001 : Blocks := ep00000011011001_0
private theorem idp00000011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001101100.list =
    C ((2:ℤ)^122) * horner X vp00000011011001.list + horner X ep00000011011001.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011011001 : Branch 1 (-107761639/1000000 : ℚ) vp0000001101100 := by
  apply branch_checked idp00000011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-107761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-108261639/500000 : ℚ) by norm_num]
  exact coverp00000011011001
theorem coverp0000001101100 : Covers (-107761639/1000000 : ℚ) vp0000001101100 := join_branches bp00000011011000 bp00000011011001
private noncomputable def vp000000110110_0 : Blocks := edgeBlocks% "full/vectors/000000110110-V-0000.bin"
private noncomputable def vp000000110110_1 : Blocks := edgeBlocks% "full/vectors/000000110110-V-0001.bin"
noncomputable def vp000000110110 : Blocks := (Blocks.join vp000000110110_0 vp000000110110_1)
private theorem bp0000001101100 : Branch 0 (-107761639/2000000 : ℚ) vp000000110110 := by
  apply branch_left_normalized (c:=vp0000001101100) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-107761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-107761639/1000000 : ℚ) by norm_num]
  exact coverp0000001101100
private noncomputable def ep0000001101101_0 : Blocks := edgeBlocks% "full/vectors/0000001101101-E-0000.bin"
private noncomputable def ep0000001101101_1 : Blocks := edgeBlocks% "full/vectors/0000001101101-E-0001.bin"
noncomputable def ep0000001101101 : Blocks := (Blocks.join ep0000001101101_0 ep0000001101101_1)
private theorem idp0000001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110110.list =
    C ((2:ℤ)^220) * horner X vp0000001101101.list + horner X ep0000001101101.list := by
  exact edge_identity (B := (2:ℤ)^416) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101101 : Branch 1 (-107761639/2000000 : ℚ) vp000000110110 := by
  apply branch_checked idp0000001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-107761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-108761639/1000000 : ℚ) by norm_num]
  exact coverp0000001101101
theorem coverp000000110110 : Covers (-107761639/2000000 : ℚ) vp000000110110 := join_branches bp0000001101100 bp0000001101101
private noncomputable def vp00000011011_0 : Blocks := edgeBlocks% "full/vectors/00000011011-V-0000.bin"
private noncomputable def vp00000011011_1 : Blocks := edgeBlocks% "full/vectors/00000011011-V-0001.bin"
private noncomputable def vp00000011011_2 : Blocks := edgeBlocks% "full/vectors/00000011011-V-0002.bin"
private noncomputable def vp00000011011_3 : Blocks := edgeBlocks% "full/vectors/00000011011-V-0003.bin"
noncomputable def vp00000011011 : Blocks := (Blocks.join (Blocks.join vp00000011011_0 vp00000011011_1) (Blocks.join vp00000011011_2 vp00000011011_3))
private theorem bp000000110110 : Branch 0 (-107761639/4000000 : ℚ) vp00000011011 := by
  apply branch_left_normalized (c:=vp000000110110) (k:=0) (m:=212) (by decide +kernel)
  rw [show 2*(-107761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-107761639/2000000 : ℚ) by norm_num]
  exact coverp000000110110
private noncomputable def ep000000110111_0 : Blocks := edgeBlocks% "full/vectors/000000110111-E-0000.bin"
private noncomputable def ep000000110111_1 : Blocks := edgeBlocks% "full/vectors/000000110111-E-0001.bin"
private noncomputable def ep000000110111_2 : Blocks := edgeBlocks% "full/vectors/000000110111-E-0002.bin"
private noncomputable def ep000000110111_3 : Blocks := edgeBlocks% "full/vectors/000000110111-E-0003.bin"
noncomputable def ep000000110111 : Blocks := (Blocks.join (Blocks.join ep000000110111_0 ep000000110111_1) (Blocks.join ep000000110111_2 ep000000110111_3))
private theorem idp000000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011011.list =
    C ((2:ℤ)^413) * horner X vp000000110111.list + horner X ep000000110111.list := by
  exact edge_identity (B := (2:ℤ)^704) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110111 : Branch 1 (-107761639/4000000 : ℚ) vp00000011011 := by
  apply branch_checked idp000000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-107761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-109761639/2000000 : ℚ) by norm_num]
  exact coverp000000110111
theorem coverp00000011011 : Covers (-107761639/4000000 : ℚ) vp00000011011 := join_branches bp000000110110 bp000000110111
private noncomputable def vp0000001101011111_0 : Blocks := edgeBlocks% "full/vectors/0000001101011111-V-0000.bin"
noncomputable def vp0000001101011111 : Blocks := vp0000001101011111_0
theorem coverp0000001101011111 : Covers (-107636639/125000 : ℚ) vp0000001101011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101011110_0 : Blocks := edgeBlocks% "full/vectors/0000001101011110-V-0000.bin"
noncomputable def vp0000001101011110 : Blocks := vp0000001101011110_0
theorem coverp0000001101011110 : Covers (-107511639/125000 : ℚ) vp0000001101011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110101111_0 : Blocks := edgeBlocks% "full/vectors/000000110101111-V-0000.bin"
noncomputable def vp000000110101111 : Blocks := vp000000110101111_0
private theorem bp0000001101011110 : Branch 0 (-107511639/250000 : ℚ) vp000000110101111 := by
  apply branch_left_normalized (c:=vp0000001101011110) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-107511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-107511639/125000 : ℚ) by norm_num]
  exact coverp0000001101011110
private noncomputable def ep0000001101011111_0 : Blocks := edgeBlocks% "full/vectors/0000001101011111-E-0000.bin"
noncomputable def ep0000001101011111 : Blocks := ep0000001101011111_0
private theorem idp0000001101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110101111.list =
    C ((2:ℤ)^45) * horner X vp0000001101011111.list + horner X ep0000001101011111.list := by
  exact edge_identity (B := (2:ℤ)^159) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101011111 : Branch 1 (-107511639/250000 : ℚ) vp000000110101111 := by
  apply branch_checked idp0000001101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-107511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-107636639/125000 : ℚ) by norm_num]
  exact coverp0000001101011111
theorem coverp000000110101111 : Covers (-107511639/250000 : ℚ) vp000000110101111 := join_branches bp0000001101011110 bp0000001101011111
private noncomputable def vp0000001101011101_0 : Blocks := edgeBlocks% "full/vectors/0000001101011101-V-0000.bin"
noncomputable def vp0000001101011101 : Blocks := vp0000001101011101_0
theorem coverp0000001101011101 : Covers (-107386639/125000 : ℚ) vp0000001101011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101011100_0 : Blocks := edgeBlocks% "full/vectors/0000001101011100-V-0000.bin"
noncomputable def vp0000001101011100 : Blocks := vp0000001101011100_0
theorem coverp0000001101011100 : Covers (-107261639/125000 : ℚ) vp0000001101011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110101110_0 : Blocks := edgeBlocks% "full/vectors/000000110101110-V-0000.bin"
noncomputable def vp000000110101110 : Blocks := vp000000110101110_0
private theorem bp0000001101011100 : Branch 0 (-107261639/250000 : ℚ) vp000000110101110 := by
  apply branch_left_normalized (c:=vp0000001101011100) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-107261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-107261639/125000 : ℚ) by norm_num]
  exact coverp0000001101011100
private noncomputable def ep0000001101011101_0 : Blocks := edgeBlocks% "full/vectors/0000001101011101-E-0000.bin"
noncomputable def ep0000001101011101 : Blocks := ep0000001101011101_0
private theorem idp0000001101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110101110.list =
    C ((2:ℤ)^45) * horner X vp0000001101011101.list + horner X ep0000001101011101.list := by
  exact edge_identity (B := (2:ℤ)^160) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101011101 : Branch 1 (-107261639/250000 : ℚ) vp000000110101110 := by
  apply branch_checked idp0000001101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-107261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-107386639/125000 : ℚ) by norm_num]
  exact coverp0000001101011101
theorem coverp000000110101110 : Covers (-107261639/250000 : ℚ) vp000000110101110 := join_branches bp0000001101011100 bp0000001101011101
private noncomputable def vp00000011010111_0 : Blocks := edgeBlocks% "full/vectors/00000011010111-V-0000.bin"
noncomputable def vp00000011010111 : Blocks := vp00000011010111_0
private theorem bp000000110101110 : Branch 0 (-107261639/500000 : ℚ) vp00000011010111 := by
  apply branch_left_normalized (c:=vp000000110101110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-107261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-107261639/250000 : ℚ) by norm_num]
  exact coverp000000110101110
private noncomputable def ep000000110101111_0 : Blocks := edgeBlocks% "full/vectors/000000110101111-E-0000.bin"
noncomputable def ep000000110101111 : Blocks := ep000000110101111_0
private theorem idp000000110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011010111.list =
    C ((2:ℤ)^72) * horner X vp000000110101111.list + horner X ep000000110101111.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110101111 : Branch 1 (-107261639/500000 : ℚ) vp00000011010111 := by
  apply branch_checked idp000000110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-107261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-107511639/250000 : ℚ) by norm_num]
  exact coverp000000110101111
theorem coverp00000011010111 : Covers (-107261639/500000 : ℚ) vp00000011010111 := join_branches bp000000110101110 bp000000110101111
private noncomputable def vp0000001101011011_0 : Blocks := edgeBlocks% "full/vectors/0000001101011011-V-0000.bin"
noncomputable def vp0000001101011011 : Blocks := vp0000001101011011_0
theorem coverp0000001101011011 : Covers (-107136639/125000 : ℚ) vp0000001101011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101011010_0 : Blocks := edgeBlocks% "full/vectors/0000001101011010-V-0000.bin"
noncomputable def vp0000001101011010 : Blocks := vp0000001101011010_0
theorem coverp0000001101011010 : Covers (-107011639/125000 : ℚ) vp0000001101011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110101101_0 : Blocks := edgeBlocks% "full/vectors/000000110101101-V-0000.bin"
noncomputable def vp000000110101101 : Blocks := vp000000110101101_0
private theorem bp0000001101011010 : Branch 0 (-107011639/250000 : ℚ) vp000000110101101 := by
  apply branch_left_normalized (c:=vp0000001101011010) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-107011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-107011639/125000 : ℚ) by norm_num]
  exact coverp0000001101011010
private noncomputable def ep0000001101011011_0 : Blocks := edgeBlocks% "full/vectors/0000001101011011-E-0000.bin"
noncomputable def ep0000001101011011 : Blocks := ep0000001101011011_0
private theorem idp0000001101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110101101.list =
    C ((2:ℤ)^45) * horner X vp0000001101011011.list + horner X ep0000001101011011.list := by
  exact edge_identity (B := (2:ℤ)^160) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101011011 : Branch 1 (-107011639/250000 : ℚ) vp000000110101101 := by
  apply branch_checked idp0000001101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-107011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-107136639/125000 : ℚ) by norm_num]
  exact coverp0000001101011011
theorem coverp000000110101101 : Covers (-107011639/250000 : ℚ) vp000000110101101 := join_branches bp0000001101011010 bp0000001101011011
private noncomputable def vp0000001101011001_0 : Blocks := edgeBlocks% "full/vectors/0000001101011001-V-0000.bin"
noncomputable def vp0000001101011001 : Blocks := vp0000001101011001_0
theorem coverp0000001101011001 : Covers (-106886639/125000 : ℚ) vp0000001101011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101011000_0 : Blocks := edgeBlocks% "full/vectors/0000001101011000-V-0000.bin"
noncomputable def vp0000001101011000 : Blocks := vp0000001101011000_0
theorem coverp0000001101011000 : Covers (-106761639/125000 : ℚ) vp0000001101011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110101100_0 : Blocks := edgeBlocks% "full/vectors/000000110101100-V-0000.bin"
noncomputable def vp000000110101100 : Blocks := vp000000110101100_0
private theorem bp0000001101011000 : Branch 0 (-106761639/250000 : ℚ) vp000000110101100 := by
  apply branch_left_normalized (c:=vp0000001101011000) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-106761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-106761639/125000 : ℚ) by norm_num]
  exact coverp0000001101011000
private noncomputable def ep0000001101011001_0 : Blocks := edgeBlocks% "full/vectors/0000001101011001-E-0000.bin"
noncomputable def ep0000001101011001 : Blocks := ep0000001101011001_0
private theorem idp0000001101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110101100.list =
    C ((2:ℤ)^44) * horner X vp0000001101011001.list + horner X ep0000001101011001.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101011001 : Branch 1 (-106761639/250000 : ℚ) vp000000110101100 := by
  apply branch_checked idp0000001101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-106761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-106886639/125000 : ℚ) by norm_num]
  exact coverp0000001101011001
theorem coverp000000110101100 : Covers (-106761639/250000 : ℚ) vp000000110101100 := join_branches bp0000001101011000 bp0000001101011001
private noncomputable def vp00000011010110_0 : Blocks := edgeBlocks% "full/vectors/00000011010110-V-0000.bin"
noncomputable def vp00000011010110 : Blocks := vp00000011010110_0
private theorem bp000000110101100 : Branch 0 (-106761639/500000 : ℚ) vp00000011010110 := by
  apply branch_left_normalized (c:=vp000000110101100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-106761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-106761639/250000 : ℚ) by norm_num]
  exact coverp000000110101100
private noncomputable def ep000000110101101_0 : Blocks := edgeBlocks% "full/vectors/000000110101101-E-0000.bin"
noncomputable def ep000000110101101 : Blocks := ep000000110101101_0
private theorem idp000000110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011010110.list =
    C ((2:ℤ)^70) * horner X vp000000110101101.list + horner X ep000000110101101.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110101101 : Branch 1 (-106761639/500000 : ℚ) vp00000011010110 := by
  apply branch_checked idp000000110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-106761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-107011639/250000 : ℚ) by norm_num]
  exact coverp000000110101101
theorem coverp00000011010110 : Covers (-106761639/500000 : ℚ) vp00000011010110 := join_branches bp000000110101100 bp000000110101101
private noncomputable def vp0000001101011_0 : Blocks := edgeBlocks% "full/vectors/0000001101011-V-0000.bin"
noncomputable def vp0000001101011 : Blocks := vp0000001101011_0
private theorem bp00000011010110 : Branch 0 (-106761639/1000000 : ℚ) vp0000001101011 := by
  apply branch_left_normalized (c:=vp00000011010110) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-106761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-106761639/500000 : ℚ) by norm_num]
  exact coverp00000011010110
private noncomputable def ep00000011010111_0 : Blocks := edgeBlocks% "full/vectors/00000011010111-E-0000.bin"
noncomputable def ep00000011010111 : Blocks := ep00000011010111_0
private theorem idp00000011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001101011.list =
    C ((2:ℤ)^120) * horner X vp00000011010111.list + horner X ep00000011010111.list := by
  exact edge_identity (B := (2:ℤ)^271) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011010111 : Branch 1 (-106761639/1000000 : ℚ) vp0000001101011 := by
  apply branch_checked idp00000011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-106761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-107261639/500000 : ℚ) by norm_num]
  exact coverp00000011010111
theorem coverp0000001101011 : Covers (-106761639/1000000 : ℚ) vp0000001101011 := join_branches bp00000011010110 bp00000011010111
private noncomputable def vp0000001101010111_0 : Blocks := edgeBlocks% "full/vectors/0000001101010111-V-0000.bin"
noncomputable def vp0000001101010111 : Blocks := vp0000001101010111_0
theorem coverp0000001101010111 : Covers (-106636639/125000 : ℚ) vp0000001101010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101010110_0 : Blocks := edgeBlocks% "full/vectors/0000001101010110-V-0000.bin"
noncomputable def vp0000001101010110 : Blocks := vp0000001101010110_0
theorem coverp0000001101010110 : Covers (-106511639/125000 : ℚ) vp0000001101010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110101011_0 : Blocks := edgeBlocks% "full/vectors/000000110101011-V-0000.bin"
noncomputable def vp000000110101011 : Blocks := vp000000110101011_0
private theorem bp0000001101010110 : Branch 0 (-106511639/250000 : ℚ) vp000000110101011 := by
  apply branch_left_normalized (c:=vp0000001101010110) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-106511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-106511639/125000 : ℚ) by norm_num]
  exact coverp0000001101010110
private noncomputable def ep0000001101010111_0 : Blocks := edgeBlocks% "full/vectors/0000001101010111-E-0000.bin"
noncomputable def ep0000001101010111 : Blocks := ep0000001101010111_0
private theorem idp0000001101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110101011.list =
    C ((2:ℤ)^44) * horner X vp0000001101010111.list + horner X ep0000001101010111.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101010111 : Branch 1 (-106511639/250000 : ℚ) vp000000110101011 := by
  apply branch_checked idp0000001101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-106511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-106636639/125000 : ℚ) by norm_num]
  exact coverp0000001101010111
theorem coverp000000110101011 : Covers (-106511639/250000 : ℚ) vp000000110101011 := join_branches bp0000001101010110 bp0000001101010111
private noncomputable def vp000000110101010_0 : Blocks := edgeBlocks% "full/vectors/000000110101010-V-0000.bin"
noncomputable def vp000000110101010 : Blocks := vp000000110101010_0
theorem coverp000000110101010 : Covers (-106261639/250000 : ℚ) vp000000110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011010101_0 : Blocks := edgeBlocks% "full/vectors/00000011010101-V-0000.bin"
noncomputable def vp00000011010101 : Blocks := vp00000011010101_0
private theorem bp000000110101010 : Branch 0 (-106261639/500000 : ℚ) vp00000011010101 := by
  apply branch_left_normalized (c:=vp000000110101010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-106261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-106261639/250000 : ℚ) by norm_num]
  exact coverp000000110101010
private noncomputable def ep000000110101011_0 : Blocks := edgeBlocks% "full/vectors/000000110101011-E-0000.bin"
noncomputable def ep000000110101011 : Blocks := ep000000110101011_0
private theorem idp000000110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011010101.list =
    C ((2:ℤ)^69) * horner X vp000000110101011.list + horner X ep000000110101011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110101011 : Branch 1 (-106261639/500000 : ℚ) vp00000011010101 := by
  apply branch_checked idp000000110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-106261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-106511639/250000 : ℚ) by norm_num]
  exact coverp000000110101011
theorem coverp00000011010101 : Covers (-106261639/500000 : ℚ) vp00000011010101 := join_branches bp000000110101010 bp000000110101011
private noncomputable def vp000000110101001_0 : Blocks := edgeBlocks% "full/vectors/000000110101001-V-0000.bin"
noncomputable def vp000000110101001 : Blocks := vp000000110101001_0
theorem coverp000000110101001 : Covers (-106011639/250000 : ℚ) vp000000110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110101000_0 : Blocks := edgeBlocks% "full/vectors/000000110101000-V-0000.bin"
noncomputable def vp000000110101000 : Blocks := vp000000110101000_0
theorem coverp000000110101000 : Covers (-105761639/250000 : ℚ) vp000000110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011010100_0 : Blocks := edgeBlocks% "full/vectors/00000011010100-V-0000.bin"
noncomputable def vp00000011010100 : Blocks := vp00000011010100_0
private theorem bp000000110101000 : Branch 0 (-105761639/500000 : ℚ) vp00000011010100 := by
  apply branch_left_normalized (c:=vp000000110101000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-105761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-105761639/250000 : ℚ) by norm_num]
  exact coverp000000110101000
private noncomputable def ep000000110101001_0 : Blocks := edgeBlocks% "full/vectors/000000110101001-E-0000.bin"
noncomputable def ep000000110101001 : Blocks := ep000000110101001_0
private theorem idp000000110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011010100.list =
    C ((2:ℤ)^70) * horner X vp000000110101001.list + horner X ep000000110101001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110101001 : Branch 1 (-105761639/500000 : ℚ) vp00000011010100 := by
  apply branch_checked idp000000110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-105761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-106011639/250000 : ℚ) by norm_num]
  exact coverp000000110101001
theorem coverp00000011010100 : Covers (-105761639/500000 : ℚ) vp00000011010100 := join_branches bp000000110101000 bp000000110101001
private noncomputable def vp0000001101010_0 : Blocks := edgeBlocks% "full/vectors/0000001101010-V-0000.bin"
noncomputable def vp0000001101010 : Blocks := vp0000001101010_0
private theorem bp00000011010100 : Branch 0 (-105761639/1000000 : ℚ) vp0000001101010 := by
  apply branch_left_normalized (c:=vp00000011010100) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-105761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-105761639/500000 : ℚ) by norm_num]
  exact coverp00000011010100
private noncomputable def ep00000011010101_0 : Blocks := edgeBlocks% "full/vectors/00000011010101-E-0000.bin"
noncomputable def ep00000011010101 : Blocks := ep00000011010101_0
private theorem idp00000011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001101010.list =
    C ((2:ℤ)^120) * horner X vp00000011010101.list + horner X ep00000011010101.list := by
  exact edge_identity (B := (2:ℤ)^269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011010101 : Branch 1 (-105761639/1000000 : ℚ) vp0000001101010 := by
  apply branch_checked idp00000011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-105761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-106261639/500000 : ℚ) by norm_num]
  exact coverp00000011010101
theorem coverp0000001101010 : Covers (-105761639/1000000 : ℚ) vp0000001101010 := join_branches bp00000011010100 bp00000011010101
private noncomputable def vp000000110101_0 : Blocks := edgeBlocks% "full/vectors/000000110101-V-0000.bin"
private noncomputable def vp000000110101_1 : Blocks := edgeBlocks% "full/vectors/000000110101-V-0001.bin"
noncomputable def vp000000110101 : Blocks := (Blocks.join vp000000110101_0 vp000000110101_1)
private theorem bp0000001101010 : Branch 0 (-105761639/2000000 : ℚ) vp000000110101 := by
  apply branch_left_normalized (c:=vp0000001101010) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-105761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-105761639/1000000 : ℚ) by norm_num]
  exact coverp0000001101010
private noncomputable def ep0000001101011_0 : Blocks := edgeBlocks% "full/vectors/0000001101011-E-0000.bin"
private noncomputable def ep0000001101011_1 : Blocks := edgeBlocks% "full/vectors/0000001101011-E-0001.bin"
noncomputable def ep0000001101011 : Blocks := (Blocks.join ep0000001101011_0 ep0000001101011_1)
private theorem idp0000001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110101.list =
    C ((2:ℤ)^218) * horner X vp0000001101011.list + horner X ep0000001101011.list := by
  exact edge_identity (B := (2:ℤ)^416) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101011 : Branch 1 (-105761639/2000000 : ℚ) vp000000110101 := by
  apply branch_checked idp0000001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-105761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-106761639/1000000 : ℚ) by norm_num]
  exact coverp0000001101011
theorem coverp000000110101 : Covers (-105761639/2000000 : ℚ) vp000000110101 := join_branches bp0000001101010 bp0000001101011
private noncomputable def vp000000110100111_0 : Blocks := edgeBlocks% "full/vectors/000000110100111-V-0000.bin"
noncomputable def vp000000110100111 : Blocks := vp000000110100111_0
theorem coverp000000110100111 : Covers (-105511639/250000 : ℚ) vp000000110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110100110_0 : Blocks := edgeBlocks% "full/vectors/000000110100110-V-0000.bin"
noncomputable def vp000000110100110 : Blocks := vp000000110100110_0
theorem coverp000000110100110 : Covers (-105261639/250000 : ℚ) vp000000110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011010011_0 : Blocks := edgeBlocks% "full/vectors/00000011010011-V-0000.bin"
noncomputable def vp00000011010011 : Blocks := vp00000011010011_0
private theorem bp000000110100110 : Branch 0 (-105261639/500000 : ℚ) vp00000011010011 := by
  apply branch_left_normalized (c:=vp000000110100110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-105261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-105261639/250000 : ℚ) by norm_num]
  exact coverp000000110100110
private noncomputable def ep000000110100111_0 : Blocks := edgeBlocks% "full/vectors/000000110100111-E-0000.bin"
noncomputable def ep000000110100111 : Blocks := ep000000110100111_0
private theorem idp000000110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011010011.list =
    C ((2:ℤ)^71) * horner X vp000000110100111.list + horner X ep000000110100111.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110100111 : Branch 1 (-105261639/500000 : ℚ) vp00000011010011 := by
  apply branch_checked idp000000110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-105261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-105511639/250000 : ℚ) by norm_num]
  exact coverp000000110100111
theorem coverp00000011010011 : Covers (-105261639/500000 : ℚ) vp00000011010011 := join_branches bp000000110100110 bp000000110100111
private noncomputable def vp0000001101001011_0 : Blocks := edgeBlocks% "full/vectors/0000001101001011-V-0000.bin"
noncomputable def vp0000001101001011 : Blocks := vp0000001101001011_0
theorem coverp0000001101001011 : Covers (-105136639/125000 : ℚ) vp0000001101001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101001010_0 : Blocks := edgeBlocks% "full/vectors/0000001101001010-V-0000.bin"
noncomputable def vp0000001101001010 : Blocks := vp0000001101001010_0
theorem coverp0000001101001010 : Covers (-105011639/125000 : ℚ) vp0000001101001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110100101_0 : Blocks := edgeBlocks% "full/vectors/000000110100101-V-0000.bin"
noncomputable def vp000000110100101 : Blocks := vp000000110100101_0
private theorem bp0000001101001010 : Branch 0 (-105011639/250000 : ℚ) vp000000110100101 := by
  apply branch_left_normalized (c:=vp0000001101001010) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-105011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-105011639/125000 : ℚ) by norm_num]
  exact coverp0000001101001010
private noncomputable def ep0000001101001011_0 : Blocks := edgeBlocks% "full/vectors/0000001101001011-E-0000.bin"
noncomputable def ep0000001101001011 : Blocks := ep0000001101001011_0
private theorem idp0000001101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110100101.list =
    C ((2:ℤ)^45) * horner X vp0000001101001011.list + horner X ep0000001101001011.list := by
  exact edge_identity (B := (2:ℤ)^159) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101001011 : Branch 1 (-105011639/250000 : ℚ) vp000000110100101 := by
  apply branch_checked idp0000001101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-105011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-105136639/125000 : ℚ) by norm_num]
  exact coverp0000001101001011
theorem coverp000000110100101 : Covers (-105011639/250000 : ℚ) vp000000110100101 := join_branches bp0000001101001010 bp0000001101001011
private noncomputable def vp0000001101001001_0 : Blocks := edgeBlocks% "full/vectors/0000001101001001-V-0000.bin"
noncomputable def vp0000001101001001 : Blocks := vp0000001101001001_0
theorem coverp0000001101001001 : Covers (-104886639/125000 : ℚ) vp0000001101001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101001000_0 : Blocks := edgeBlocks% "full/vectors/0000001101001000-V-0000.bin"
noncomputable def vp0000001101001000 : Blocks := vp0000001101001000_0
theorem coverp0000001101001000 : Covers (-104761639/125000 : ℚ) vp0000001101001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110100100_0 : Blocks := edgeBlocks% "full/vectors/000000110100100-V-0000.bin"
noncomputable def vp000000110100100 : Blocks := vp000000110100100_0
private theorem bp0000001101001000 : Branch 0 (-104761639/250000 : ℚ) vp000000110100100 := by
  apply branch_left_normalized (c:=vp0000001101001000) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-104761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-104761639/125000 : ℚ) by norm_num]
  exact coverp0000001101001000
private noncomputable def ep0000001101001001_0 : Blocks := edgeBlocks% "full/vectors/0000001101001001-E-0000.bin"
noncomputable def ep0000001101001001 : Blocks := ep0000001101001001_0
private theorem idp0000001101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110100100.list =
    C ((2:ℤ)^45) * horner X vp0000001101001001.list + horner X ep0000001101001001.list := by
  exact edge_identity (B := (2:ℤ)^160) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101001001 : Branch 1 (-104761639/250000 : ℚ) vp000000110100100 := by
  apply branch_checked idp0000001101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-104761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-104886639/125000 : ℚ) by norm_num]
  exact coverp0000001101001001
theorem coverp000000110100100 : Covers (-104761639/250000 : ℚ) vp000000110100100 := join_branches bp0000001101001000 bp0000001101001001
private noncomputable def vp00000011010010_0 : Blocks := edgeBlocks% "full/vectors/00000011010010-V-0000.bin"
noncomputable def vp00000011010010 : Blocks := vp00000011010010_0
private theorem bp000000110100100 : Branch 0 (-104761639/500000 : ℚ) vp00000011010010 := by
  apply branch_left_normalized (c:=vp000000110100100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-104761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-104761639/250000 : ℚ) by norm_num]
  exact coverp000000110100100
private noncomputable def ep000000110100101_0 : Blocks := edgeBlocks% "full/vectors/000000110100101-E-0000.bin"
noncomputable def ep000000110100101 : Blocks := ep000000110100101_0
private theorem idp000000110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011010010.list =
    C ((2:ℤ)^72) * horner X vp000000110100101.list + horner X ep000000110100101.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110100101 : Branch 1 (-104761639/500000 : ℚ) vp00000011010010 := by
  apply branch_checked idp000000110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-104761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-105011639/250000 : ℚ) by norm_num]
  exact coverp000000110100101
theorem coverp00000011010010 : Covers (-104761639/500000 : ℚ) vp00000011010010 := join_branches bp000000110100100 bp000000110100101
private noncomputable def vp0000001101001_0 : Blocks := edgeBlocks% "full/vectors/0000001101001-V-0000.bin"
noncomputable def vp0000001101001 : Blocks := vp0000001101001_0
private theorem bp00000011010010 : Branch 0 (-104761639/1000000 : ℚ) vp0000001101001 := by
  apply branch_left_normalized (c:=vp00000011010010) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-104761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-104761639/500000 : ℚ) by norm_num]
  exact coverp00000011010010
private noncomputable def ep00000011010011_0 : Blocks := edgeBlocks% "full/vectors/00000011010011-E-0000.bin"
noncomputable def ep00000011010011 : Blocks := ep00000011010011_0
private theorem idp00000011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001101001.list =
    C ((2:ℤ)^123) * horner X vp00000011010011.list + horner X ep00000011010011.list := by
  exact edge_identity (B := (2:ℤ)^273) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011010011 : Branch 1 (-104761639/1000000 : ℚ) vp0000001101001 := by
  apply branch_checked idp00000011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-104761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-105261639/500000 : ℚ) by norm_num]
  exact coverp00000011010011
theorem coverp0000001101001 : Covers (-104761639/1000000 : ℚ) vp0000001101001 := join_branches bp00000011010010 bp00000011010011
private noncomputable def vp0000001101000111_0 : Blocks := edgeBlocks% "full/vectors/0000001101000111-V-0000.bin"
noncomputable def vp0000001101000111 : Blocks := vp0000001101000111_0
theorem coverp0000001101000111 : Covers (-104636639/125000 : ℚ) vp0000001101000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101000110_0 : Blocks := edgeBlocks% "full/vectors/0000001101000110-V-0000.bin"
noncomputable def vp0000001101000110 : Blocks := vp0000001101000110_0
theorem coverp0000001101000110 : Covers (-104511639/125000 : ℚ) vp0000001101000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110100011_0 : Blocks := edgeBlocks% "full/vectors/000000110100011-V-0000.bin"
noncomputable def vp000000110100011 : Blocks := vp000000110100011_0
private theorem bp0000001101000110 : Branch 0 (-104511639/250000 : ℚ) vp000000110100011 := by
  apply branch_left_normalized (c:=vp0000001101000110) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-104511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-104511639/125000 : ℚ) by norm_num]
  exact coverp0000001101000110
private noncomputable def ep0000001101000111_0 : Blocks := edgeBlocks% "full/vectors/0000001101000111-E-0000.bin"
noncomputable def ep0000001101000111 : Blocks := ep0000001101000111_0
private theorem idp0000001101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110100011.list =
    C ((2:ℤ)^43) * horner X vp0000001101000111.list + horner X ep0000001101000111.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101000111 : Branch 1 (-104511639/250000 : ℚ) vp000000110100011 := by
  apply branch_checked idp0000001101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-104511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-104636639/125000 : ℚ) by norm_num]
  exact coverp0000001101000111
theorem coverp000000110100011 : Covers (-104511639/250000 : ℚ) vp000000110100011 := join_branches bp0000001101000110 bp0000001101000111
private noncomputable def vp0000001101000101_0 : Blocks := edgeBlocks% "full/vectors/0000001101000101-V-0000.bin"
noncomputable def vp0000001101000101 : Blocks := vp0000001101000101_0
theorem coverp0000001101000101 : Covers (-104386639/125000 : ℚ) vp0000001101000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101000100_0 : Blocks := edgeBlocks% "full/vectors/0000001101000100-V-0000.bin"
noncomputable def vp0000001101000100 : Blocks := vp0000001101000100_0
theorem coverp0000001101000100 : Covers (-104261639/125000 : ℚ) vp0000001101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110100010_0 : Blocks := edgeBlocks% "full/vectors/000000110100010-V-0000.bin"
noncomputable def vp000000110100010 : Blocks := vp000000110100010_0
private theorem bp0000001101000100 : Branch 0 (-104261639/250000 : ℚ) vp000000110100010 := by
  apply branch_left_normalized (c:=vp0000001101000100) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-104261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-104261639/125000 : ℚ) by norm_num]
  exact coverp0000001101000100
private noncomputable def ep0000001101000101_0 : Blocks := edgeBlocks% "full/vectors/0000001101000101-E-0000.bin"
noncomputable def ep0000001101000101 : Blocks := ep0000001101000101_0
private theorem idp0000001101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110100010.list =
    C ((2:ℤ)^43) * horner X vp0000001101000101.list + horner X ep0000001101000101.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101000101 : Branch 1 (-104261639/250000 : ℚ) vp000000110100010 := by
  apply branch_checked idp0000001101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-104261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-104386639/125000 : ℚ) by norm_num]
  exact coverp0000001101000101
theorem coverp000000110100010 : Covers (-104261639/250000 : ℚ) vp000000110100010 := join_branches bp0000001101000100 bp0000001101000101
private noncomputable def vp00000011010001_0 : Blocks := edgeBlocks% "full/vectors/00000011010001-V-0000.bin"
noncomputable def vp00000011010001 : Blocks := vp00000011010001_0
private theorem bp000000110100010 : Branch 0 (-104261639/500000 : ℚ) vp00000011010001 := by
  apply branch_left_normalized (c:=vp000000110100010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-104261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-104261639/250000 : ℚ) by norm_num]
  exact coverp000000110100010
private noncomputable def ep000000110100011_0 : Blocks := edgeBlocks% "full/vectors/000000110100011-E-0000.bin"
noncomputable def ep000000110100011 : Blocks := ep000000110100011_0
private theorem idp000000110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011010001.list =
    C ((2:ℤ)^69) * horner X vp000000110100011.list + horner X ep000000110100011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110100011 : Branch 1 (-104261639/500000 : ℚ) vp00000011010001 := by
  apply branch_checked idp000000110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-104261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-104511639/250000 : ℚ) by norm_num]
  exact coverp000000110100011
theorem coverp00000011010001 : Covers (-104261639/500000 : ℚ) vp00000011010001 := join_branches bp000000110100010 bp000000110100011
private noncomputable def vp0000001101000011_0 : Blocks := edgeBlocks% "full/vectors/0000001101000011-V-0000.bin"
noncomputable def vp0000001101000011 : Blocks := vp0000001101000011_0
theorem coverp0000001101000011 : Covers (-104136639/125000 : ℚ) vp0000001101000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001101000010_0 : Blocks := edgeBlocks% "full/vectors/0000001101000010-V-0000.bin"
noncomputable def vp0000001101000010 : Blocks := vp0000001101000010_0
theorem coverp0000001101000010 : Covers (-104011639/125000 : ℚ) vp0000001101000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110100001_0 : Blocks := edgeBlocks% "full/vectors/000000110100001-V-0000.bin"
noncomputable def vp000000110100001 : Blocks := vp000000110100001_0
private theorem bp0000001101000010 : Branch 0 (-104011639/250000 : ℚ) vp000000110100001 := by
  apply branch_left_normalized (c:=vp0000001101000010) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-104011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-104011639/125000 : ℚ) by norm_num]
  exact coverp0000001101000010
private noncomputable def ep0000001101000011_0 : Blocks := edgeBlocks% "full/vectors/0000001101000011-E-0000.bin"
noncomputable def ep0000001101000011 : Blocks := ep0000001101000011_0
private theorem idp0000001101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110100001.list =
    C ((2:ℤ)^43) * horner X vp0000001101000011.list + horner X ep0000001101000011.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101000011 : Branch 1 (-104011639/250000 : ℚ) vp000000110100001 := by
  apply branch_checked idp0000001101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-104011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-104136639/125000 : ℚ) by norm_num]
  exact coverp0000001101000011
theorem coverp000000110100001 : Covers (-104011639/250000 : ℚ) vp000000110100001 := join_branches bp0000001101000010 bp0000001101000011
private noncomputable def vp000000110100000_0 : Blocks := edgeBlocks% "full/vectors/000000110100000-V-0000.bin"
noncomputable def vp000000110100000 : Blocks := vp000000110100000_0
theorem coverp000000110100000 : Covers (-103761639/250000 : ℚ) vp000000110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011010000_0 : Blocks := edgeBlocks% "full/vectors/00000011010000-V-0000.bin"
noncomputable def vp00000011010000 : Blocks := vp00000011010000_0
private theorem bp000000110100000 : Branch 0 (-103761639/500000 : ℚ) vp00000011010000 := by
  apply branch_left_normalized (c:=vp000000110100000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-103761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-103761639/250000 : ℚ) by norm_num]
  exact coverp000000110100000
private noncomputable def ep000000110100001_0 : Blocks := edgeBlocks% "full/vectors/000000110100001-E-0000.bin"
noncomputable def ep000000110100001 : Blocks := ep000000110100001_0
private theorem idp000000110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011010000.list =
    C ((2:ℤ)^70) * horner X vp000000110100001.list + horner X ep000000110100001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110100001 : Branch 1 (-103761639/500000 : ℚ) vp00000011010000 := by
  apply branch_checked idp000000110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-103761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-104011639/250000 : ℚ) by norm_num]
  exact coverp000000110100001
theorem coverp00000011010000 : Covers (-103761639/500000 : ℚ) vp00000011010000 := join_branches bp000000110100000 bp000000110100001
private noncomputable def vp0000001101000_0 : Blocks := edgeBlocks% "full/vectors/0000001101000-V-0000.bin"
noncomputable def vp0000001101000 : Blocks := vp0000001101000_0
private theorem bp00000011010000 : Branch 0 (-103761639/1000000 : ℚ) vp0000001101000 := by
  apply branch_left_normalized (c:=vp00000011010000) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-103761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-103761639/500000 : ℚ) by norm_num]
  exact coverp00000011010000
private noncomputable def ep00000011010001_0 : Blocks := edgeBlocks% "full/vectors/00000011010001-E-0000.bin"
noncomputable def ep00000011010001 : Blocks := ep00000011010001_0
private theorem idp00000011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001101000.list =
    C ((2:ℤ)^120) * horner X vp00000011010001.list + horner X ep00000011010001.list := by
  exact edge_identity (B := (2:ℤ)^269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011010001 : Branch 1 (-103761639/1000000 : ℚ) vp0000001101000 := by
  apply branch_checked idp00000011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-103761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-104261639/500000 : ℚ) by norm_num]
  exact coverp00000011010001
theorem coverp0000001101000 : Covers (-103761639/1000000 : ℚ) vp0000001101000 := join_branches bp00000011010000 bp00000011010001
private noncomputable def vp000000110100_0 : Blocks := edgeBlocks% "full/vectors/000000110100-V-0000.bin"
private noncomputable def vp000000110100_1 : Blocks := edgeBlocks% "full/vectors/000000110100-V-0001.bin"
noncomputable def vp000000110100 : Blocks := (Blocks.join vp000000110100_0 vp000000110100_1)
private theorem bp0000001101000 : Branch 0 (-103761639/2000000 : ℚ) vp000000110100 := by
  apply branch_left_normalized (c:=vp0000001101000) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-103761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-103761639/1000000 : ℚ) by norm_num]
  exact coverp0000001101000
private noncomputable def ep0000001101001_0 : Blocks := edgeBlocks% "full/vectors/0000001101001-E-0000.bin"
private noncomputable def ep0000001101001_1 : Blocks := edgeBlocks% "full/vectors/0000001101001-E-0001.bin"
noncomputable def ep0000001101001 : Blocks := (Blocks.join ep0000001101001_0 ep0000001101001_1)
private theorem idp0000001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110100.list =
    C ((2:ℤ)^218) * horner X vp0000001101001.list + horner X ep0000001101001.list := by
  exact edge_identity (B := (2:ℤ)^417) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101001 : Branch 1 (-103761639/2000000 : ℚ) vp000000110100 := by
  apply branch_checked idp0000001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-103761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-104761639/1000000 : ℚ) by norm_num]
  exact coverp0000001101001
theorem coverp000000110100 : Covers (-103761639/2000000 : ℚ) vp000000110100 := join_branches bp0000001101000 bp0000001101001
private noncomputable def vp00000011010_0 : Blocks := edgeBlocks% "full/vectors/00000011010-V-0000.bin"
private noncomputable def vp00000011010_1 : Blocks := edgeBlocks% "full/vectors/00000011010-V-0001.bin"
private noncomputable def vp00000011010_2 : Blocks := edgeBlocks% "full/vectors/00000011010-V-0002.bin"
private noncomputable def vp00000011010_3 : Blocks := edgeBlocks% "full/vectors/00000011010-V-0003.bin"
noncomputable def vp00000011010 : Blocks := (Blocks.join (Blocks.join vp00000011010_0 vp00000011010_1) (Blocks.join vp00000011010_2 vp00000011010_3))
private theorem bp000000110100 : Branch 0 (-103761639/4000000 : ℚ) vp00000011010 := by
  apply branch_left_normalized (c:=vp000000110100) (k:=0) (m:=214) (by decide +kernel)
  rw [show 2*(-103761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-103761639/2000000 : ℚ) by norm_num]
  exact coverp000000110100
private noncomputable def ep000000110101_0 : Blocks := edgeBlocks% "full/vectors/000000110101-E-0000.bin"
private noncomputable def ep000000110101_1 : Blocks := edgeBlocks% "full/vectors/000000110101-E-0001.bin"
private noncomputable def ep000000110101_2 : Blocks := edgeBlocks% "full/vectors/000000110101-E-0002.bin"
private noncomputable def ep000000110101_3 : Blocks := edgeBlocks% "full/vectors/000000110101-E-0003.bin"
noncomputable def ep000000110101 : Blocks := (Blocks.join (Blocks.join ep000000110101_0 ep000000110101_1) (Blocks.join ep000000110101_2 ep000000110101_3))
private theorem idp000000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011010.list =
    C ((2:ℤ)^416) * horner X vp000000110101.list + horner X ep000000110101.list := by
  exact edge_identity (B := (2:ℤ)^710) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110101 : Branch 1 (-103761639/4000000 : ℚ) vp00000011010 := by
  apply branch_checked idp000000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-103761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-105761639/2000000 : ℚ) by norm_num]
  exact coverp000000110101
theorem coverp00000011010 : Covers (-103761639/4000000 : ℚ) vp00000011010 := join_branches bp000000110100 bp000000110101
private noncomputable def vp0000001101_0 : Blocks := edgeBlocks% "full/vectors/0000001101-V-0000.bin"
private noncomputable def vp0000001101_1 : Blocks := edgeBlocks% "full/vectors/0000001101-V-0001.bin"
private noncomputable def vp0000001101_2 : Blocks := edgeBlocks% "full/vectors/0000001101-V-0002.bin"
private noncomputable def vp0000001101_3 : Blocks := edgeBlocks% "full/vectors/0000001101-V-0003.bin"
private noncomputable def vp0000001101_4 : Blocks := edgeBlocks% "full/vectors/0000001101-V-0004.bin"
private noncomputable def vp0000001101_5 : Blocks := edgeBlocks% "full/vectors/0000001101-V-0005.bin"
private noncomputable def vp0000001101_6 : Blocks := edgeBlocks% "full/vectors/0000001101-V-0006.bin"
noncomputable def vp0000001101 : Blocks := (Blocks.join (Blocks.join vp0000001101_0 (Blocks.join vp0000001101_1 vp0000001101_2)) (Blocks.join (Blocks.join vp0000001101_3 vp0000001101_4) (Blocks.join vp0000001101_5 vp0000001101_6)))
private theorem bp00000011010 : Branch 0 (-103761639/8000000 : ℚ) vp0000001101 := by
  apply branch_left_normalized (c:=vp00000011010) (k:=0) (m:=404) (by decide +kernel)
  rw [show 2*(-103761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-103761639/4000000 : ℚ) by norm_num]
  exact coverp00000011010
private noncomputable def ep00000011011_0 : Blocks := edgeBlocks% "full/vectors/00000011011-E-0000.bin"
private noncomputable def ep00000011011_1 : Blocks := edgeBlocks% "full/vectors/00000011011-E-0001.bin"
private noncomputable def ep00000011011_2 : Blocks := edgeBlocks% "full/vectors/00000011011-E-0002.bin"
private noncomputable def ep00000011011_3 : Blocks := edgeBlocks% "full/vectors/00000011011-E-0003.bin"
private noncomputable def ep00000011011_4 : Blocks := edgeBlocks% "full/vectors/00000011011-E-0004.bin"
private noncomputable def ep00000011011_5 : Blocks := edgeBlocks% "full/vectors/00000011011-E-0005.bin"
private noncomputable def ep00000011011_6 : Blocks := edgeBlocks% "full/vectors/00000011011-E-0006.bin"
noncomputable def ep00000011011 : Blocks := (Blocks.join (Blocks.join ep00000011011_0 (Blocks.join ep00000011011_1 ep00000011011_2)) (Blocks.join (Blocks.join ep00000011011_3 ep00000011011_4) (Blocks.join ep00000011011_5 ep00000011011_6)))
private theorem idp00000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001101.list =
    C ((2:ℤ)^806) * horner X vp00000011011.list + horner X ep00000011011.list := by
  exact edge_identity (B := (2:ℤ)^1293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011011 : Branch 1 (-103761639/8000000 : ℚ) vp0000001101 := by
  apply branch_checked idp00000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-103761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-107761639/4000000 : ℚ) by norm_num]
  exact coverp00000011011
theorem coverp0000001101 : Covers (-103761639/8000000 : ℚ) vp0000001101 := join_branches bp00000011010 bp00000011011
private noncomputable def vp000000110011111_0 : Blocks := edgeBlocks% "full/vectors/000000110011111-V-0000.bin"
noncomputable def vp000000110011111 : Blocks := vp000000110011111_0
theorem coverp000000110011111 : Covers (-103511639/250000 : ℚ) vp000000110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110011110_0 : Blocks := edgeBlocks% "full/vectors/000000110011110-V-0000.bin"
noncomputable def vp000000110011110 : Blocks := vp000000110011110_0
theorem coverp000000110011110 : Covers (-103261639/250000 : ℚ) vp000000110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011001111_0 : Blocks := edgeBlocks% "full/vectors/00000011001111-V-0000.bin"
noncomputable def vp00000011001111 : Blocks := vp00000011001111_0
private theorem bp000000110011110 : Branch 0 (-103261639/500000 : ℚ) vp00000011001111 := by
  apply branch_left_normalized (c:=vp000000110011110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-103261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-103261639/250000 : ℚ) by norm_num]
  exact coverp000000110011110
private noncomputable def ep000000110011111_0 : Blocks := edgeBlocks% "full/vectors/000000110011111-E-0000.bin"
noncomputable def ep000000110011111 : Blocks := ep000000110011111_0
private theorem idp000000110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011001111.list =
    C ((2:ℤ)^70) * horner X vp000000110011111.list + horner X ep000000110011111.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110011111 : Branch 1 (-103261639/500000 : ℚ) vp00000011001111 := by
  apply branch_checked idp000000110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-103261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-103511639/250000 : ℚ) by norm_num]
  exact coverp000000110011111
theorem coverp00000011001111 : Covers (-103261639/500000 : ℚ) vp00000011001111 := join_branches bp000000110011110 bp000000110011111
private noncomputable def vp000000110011101_0 : Blocks := edgeBlocks% "full/vectors/000000110011101-V-0000.bin"
noncomputable def vp000000110011101 : Blocks := vp000000110011101_0
theorem coverp000000110011101 : Covers (-103011639/250000 : ℚ) vp000000110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110011100_0 : Blocks := edgeBlocks% "full/vectors/000000110011100-V-0000.bin"
noncomputable def vp000000110011100 : Blocks := vp000000110011100_0
theorem coverp000000110011100 : Covers (-102761639/250000 : ℚ) vp000000110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011001110_0 : Blocks := edgeBlocks% "full/vectors/00000011001110-V-0000.bin"
noncomputable def vp00000011001110 : Blocks := vp00000011001110_0
private theorem bp000000110011100 : Branch 0 (-102761639/500000 : ℚ) vp00000011001110 := by
  apply branch_left_normalized (c:=vp000000110011100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-102761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-102761639/250000 : ℚ) by norm_num]
  exact coverp000000110011100
private noncomputable def ep000000110011101_0 : Blocks := edgeBlocks% "full/vectors/000000110011101-E-0000.bin"
noncomputable def ep000000110011101 : Blocks := ep000000110011101_0
private theorem idp000000110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011001110.list =
    C ((2:ℤ)^69) * horner X vp000000110011101.list + horner X ep000000110011101.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110011101 : Branch 1 (-102761639/500000 : ℚ) vp00000011001110 := by
  apply branch_checked idp000000110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-102761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-103011639/250000 : ℚ) by norm_num]
  exact coverp000000110011101
theorem coverp00000011001110 : Covers (-102761639/500000 : ℚ) vp00000011001110 := join_branches bp000000110011100 bp000000110011101
private noncomputable def vp0000001100111_0 : Blocks := edgeBlocks% "full/vectors/0000001100111-V-0000.bin"
noncomputable def vp0000001100111 : Blocks := vp0000001100111_0
private theorem bp00000011001110 : Branch 0 (-102761639/1000000 : ℚ) vp0000001100111 := by
  apply branch_left_normalized (c:=vp00000011001110) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-102761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-102761639/500000 : ℚ) by norm_num]
  exact coverp00000011001110
private noncomputable def ep00000011001111_0 : Blocks := edgeBlocks% "full/vectors/00000011001111-E-0000.bin"
noncomputable def ep00000011001111 : Blocks := ep00000011001111_0
private theorem idp00000011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001100111.list =
    C ((2:ℤ)^121) * horner X vp00000011001111.list + horner X ep00000011001111.list := by
  exact edge_identity (B := (2:ℤ)^269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011001111 : Branch 1 (-102761639/1000000 : ℚ) vp0000001100111 := by
  apply branch_checked idp00000011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-102761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-103261639/500000 : ℚ) by norm_num]
  exact coverp00000011001111
theorem coverp0000001100111 : Covers (-102761639/1000000 : ℚ) vp0000001100111 := join_branches bp00000011001110 bp00000011001111
private noncomputable def vp000000110011011_0 : Blocks := edgeBlocks% "full/vectors/000000110011011-V-0000.bin"
noncomputable def vp000000110011011 : Blocks := vp000000110011011_0
theorem coverp000000110011011 : Covers (-102511639/250000 : ℚ) vp000000110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110011010_0 : Blocks := edgeBlocks% "full/vectors/000000110011010-V-0000.bin"
noncomputable def vp000000110011010 : Blocks := vp000000110011010_0
theorem coverp000000110011010 : Covers (-102261639/250000 : ℚ) vp000000110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011001101_0 : Blocks := edgeBlocks% "full/vectors/00000011001101-V-0000.bin"
noncomputable def vp00000011001101 : Blocks := vp00000011001101_0
private theorem bp000000110011010 : Branch 0 (-102261639/500000 : ℚ) vp00000011001101 := by
  apply branch_left_normalized (c:=vp000000110011010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-102261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-102261639/250000 : ℚ) by norm_num]
  exact coverp000000110011010
private noncomputable def ep000000110011011_0 : Blocks := edgeBlocks% "full/vectors/000000110011011-E-0000.bin"
noncomputable def ep000000110011011 : Blocks := ep000000110011011_0
private theorem idp000000110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011001101.list =
    C ((2:ℤ)^73) * horner X vp000000110011011.list + horner X ep000000110011011.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110011011 : Branch 1 (-102261639/500000 : ℚ) vp00000011001101 := by
  apply branch_checked idp000000110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-102261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-102511639/250000 : ℚ) by norm_num]
  exact coverp000000110011011
theorem coverp00000011001101 : Covers (-102261639/500000 : ℚ) vp00000011001101 := join_branches bp000000110011010 bp000000110011011
private noncomputable def vp000000110011001_0 : Blocks := edgeBlocks% "full/vectors/000000110011001-V-0000.bin"
noncomputable def vp000000110011001 : Blocks := vp000000110011001_0
theorem coverp000000110011001 : Covers (-102011639/250000 : ℚ) vp000000110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001100110001_0 : Blocks := edgeBlocks% "full/vectors/0000001100110001-V-0000.bin"
noncomputable def vp0000001100110001 : Blocks := vp0000001100110001_0
theorem coverp0000001100110001 : Covers (-101886639/125000 : ℚ) vp0000001100110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001100110000_0 : Blocks := edgeBlocks% "full/vectors/0000001100110000-V-0000.bin"
noncomputable def vp0000001100110000 : Blocks := vp0000001100110000_0
theorem coverp0000001100110000 : Covers (-101761639/125000 : ℚ) vp0000001100110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110011000_0 : Blocks := edgeBlocks% "full/vectors/000000110011000-V-0000.bin"
noncomputable def vp000000110011000 : Blocks := vp000000110011000_0
private theorem bp0000001100110000 : Branch 0 (-101761639/250000 : ℚ) vp000000110011000 := by
  apply branch_left_normalized (c:=vp0000001100110000) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-101761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-101761639/125000 : ℚ) by norm_num]
  exact coverp0000001100110000
private noncomputable def ep0000001100110001_0 : Blocks := edgeBlocks% "full/vectors/0000001100110001-E-0000.bin"
noncomputable def ep0000001100110001 : Blocks := ep0000001100110001_0
private theorem idp0000001100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110011000.list =
    C ((2:ℤ)^43) * horner X vp0000001100110001.list + horner X ep0000001100110001.list := by
  exact edge_identity (B := (2:ℤ)^159) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001100110001 : Branch 1 (-101761639/250000 : ℚ) vp000000110011000 := by
  apply branch_checked idp0000001100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-101761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-101886639/125000 : ℚ) by norm_num]
  exact coverp0000001100110001
theorem coverp000000110011000 : Covers (-101761639/250000 : ℚ) vp000000110011000 := join_branches bp0000001100110000 bp0000001100110001
private noncomputable def vp00000011001100_0 : Blocks := edgeBlocks% "full/vectors/00000011001100-V-0000.bin"
noncomputable def vp00000011001100 : Blocks := vp00000011001100_0
private theorem bp000000110011000 : Branch 0 (-101761639/500000 : ℚ) vp00000011001100 := by
  apply branch_left_normalized (c:=vp000000110011000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-101761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-101761639/250000 : ℚ) by norm_num]
  exact coverp000000110011000
private noncomputable def ep000000110011001_0 : Blocks := edgeBlocks% "full/vectors/000000110011001-E-0000.bin"
noncomputable def ep000000110011001 : Blocks := ep000000110011001_0
private theorem idp000000110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011001100.list =
    C ((2:ℤ)^71) * horner X vp000000110011001.list + horner X ep000000110011001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110011001 : Branch 1 (-101761639/500000 : ℚ) vp00000011001100 := by
  apply branch_checked idp000000110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-101761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-102011639/250000 : ℚ) by norm_num]
  exact coverp000000110011001
theorem coverp00000011001100 : Covers (-101761639/500000 : ℚ) vp00000011001100 := join_branches bp000000110011000 bp000000110011001
private noncomputable def vp0000001100110_0 : Blocks := edgeBlocks% "full/vectors/0000001100110-V-0000.bin"
noncomputable def vp0000001100110 : Blocks := vp0000001100110_0
private theorem bp00000011001100 : Branch 0 (-101761639/1000000 : ℚ) vp0000001100110 := by
  apply branch_left_normalized (c:=vp00000011001100) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-101761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-101761639/500000 : ℚ) by norm_num]
  exact coverp00000011001100
private noncomputable def ep00000011001101_0 : Blocks := edgeBlocks% "full/vectors/00000011001101-E-0000.bin"
noncomputable def ep00000011001101 : Blocks := ep00000011001101_0
private theorem idp00000011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001100110.list =
    C ((2:ℤ)^124) * horner X vp00000011001101.list + horner X ep00000011001101.list := by
  exact edge_identity (B := (2:ℤ)^274) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011001101 : Branch 1 (-101761639/1000000 : ℚ) vp0000001100110 := by
  apply branch_checked idp00000011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-101761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-102261639/500000 : ℚ) by norm_num]
  exact coverp00000011001101
theorem coverp0000001100110 : Covers (-101761639/1000000 : ℚ) vp0000001100110 := join_branches bp00000011001100 bp00000011001101
private noncomputable def vp000000110011_0 : Blocks := edgeBlocks% "full/vectors/000000110011-V-0000.bin"
private noncomputable def vp000000110011_1 : Blocks := edgeBlocks% "full/vectors/000000110011-V-0001.bin"
noncomputable def vp000000110011 : Blocks := (Blocks.join vp000000110011_0 vp000000110011_1)
private theorem bp0000001100110 : Branch 0 (-101761639/2000000 : ℚ) vp000000110011 := by
  apply branch_left_normalized (c:=vp0000001100110) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-101761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-101761639/1000000 : ℚ) by norm_num]
  exact coverp0000001100110
private noncomputable def ep0000001100111_0 : Blocks := edgeBlocks% "full/vectors/0000001100111-E-0000.bin"
private noncomputable def ep0000001100111_1 : Blocks := edgeBlocks% "full/vectors/0000001100111-E-0001.bin"
noncomputable def ep0000001100111 : Blocks := (Blocks.join ep0000001100111_0 ep0000001100111_1)
private theorem idp0000001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110011.list =
    C ((2:ℤ)^227) * horner X vp0000001100111.list + horner X ep0000001100111.list := by
  exact edge_identity (B := (2:ℤ)^424) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001100111 : Branch 1 (-101761639/2000000 : ℚ) vp000000110011 := by
  apply branch_checked idp0000001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-101761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-102761639/1000000 : ℚ) by norm_num]
  exact coverp0000001100111
theorem coverp000000110011 : Covers (-101761639/2000000 : ℚ) vp000000110011 := join_branches bp0000001100110 bp0000001100111
private noncomputable def vp0000001100101111_0 : Blocks := edgeBlocks% "full/vectors/0000001100101111-V-0000.bin"
noncomputable def vp0000001100101111 : Blocks := vp0000001100101111_0
theorem coverp0000001100101111 : Covers (-101636639/125000 : ℚ) vp0000001100101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001100101110_0 : Blocks := edgeBlocks% "full/vectors/0000001100101110-V-0000.bin"
noncomputable def vp0000001100101110 : Blocks := vp0000001100101110_0
theorem coverp0000001100101110 : Covers (-101511639/125000 : ℚ) vp0000001100101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110010111_0 : Blocks := edgeBlocks% "full/vectors/000000110010111-V-0000.bin"
noncomputable def vp000000110010111 : Blocks := vp000000110010111_0
private theorem bp0000001100101110 : Branch 0 (-101511639/250000 : ℚ) vp000000110010111 := by
  apply branch_left_normalized (c:=vp0000001100101110) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-101511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-101511639/125000 : ℚ) by norm_num]
  exact coverp0000001100101110
private noncomputable def ep0000001100101111_0 : Blocks := edgeBlocks% "full/vectors/0000001100101111-E-0000.bin"
noncomputable def ep0000001100101111 : Blocks := ep0000001100101111_0
private theorem idp0000001100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110010111.list =
    C ((2:ℤ)^43) * horner X vp0000001100101111.list + horner X ep0000001100101111.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001100101111 : Branch 1 (-101511639/250000 : ℚ) vp000000110010111 := by
  apply branch_checked idp0000001100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-101511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-101636639/125000 : ℚ) by norm_num]
  exact coverp0000001100101111
theorem coverp000000110010111 : Covers (-101511639/250000 : ℚ) vp000000110010111 := join_branches bp0000001100101110 bp0000001100101111
private noncomputable def vp000000110010110_0 : Blocks := edgeBlocks% "full/vectors/000000110010110-V-0000.bin"
noncomputable def vp000000110010110 : Blocks := vp000000110010110_0
theorem coverp000000110010110 : Covers (-101261639/250000 : ℚ) vp000000110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011001011_0 : Blocks := edgeBlocks% "full/vectors/00000011001011-V-0000.bin"
noncomputable def vp00000011001011 : Blocks := vp00000011001011_0
private theorem bp000000110010110 : Branch 0 (-101261639/500000 : ℚ) vp00000011001011 := by
  apply branch_left_normalized (c:=vp000000110010110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-101261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-101261639/250000 : ℚ) by norm_num]
  exact coverp000000110010110
private noncomputable def ep000000110010111_0 : Blocks := edgeBlocks% "full/vectors/000000110010111-E-0000.bin"
noncomputable def ep000000110010111 : Blocks := ep000000110010111_0
private theorem idp000000110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011001011.list =
    C ((2:ℤ)^68) * horner X vp000000110010111.list + horner X ep000000110010111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110010111 : Branch 1 (-101261639/500000 : ℚ) vp00000011001011 := by
  apply branch_checked idp000000110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-101261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-101511639/250000 : ℚ) by norm_num]
  exact coverp000000110010111
theorem coverp00000011001011 : Covers (-101261639/500000 : ℚ) vp00000011001011 := join_branches bp000000110010110 bp000000110010111
private noncomputable def vp000000110010101_0 : Blocks := edgeBlocks% "full/vectors/000000110010101-V-0000.bin"
noncomputable def vp000000110010101 : Blocks := vp000000110010101_0
theorem coverp000000110010101 : Covers (-101011639/250000 : ℚ) vp000000110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110010100_0 : Blocks := edgeBlocks% "full/vectors/000000110010100-V-0000.bin"
noncomputable def vp000000110010100 : Blocks := vp000000110010100_0
theorem coverp000000110010100 : Covers (-100761639/250000 : ℚ) vp000000110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011001010_0 : Blocks := edgeBlocks% "full/vectors/00000011001010-V-0000.bin"
noncomputable def vp00000011001010 : Blocks := vp00000011001010_0
private theorem bp000000110010100 : Branch 0 (-100761639/500000 : ℚ) vp00000011001010 := by
  apply branch_left_normalized (c:=vp000000110010100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-100761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-100761639/250000 : ℚ) by norm_num]
  exact coverp000000110010100
private noncomputable def ep000000110010101_0 : Blocks := edgeBlocks% "full/vectors/000000110010101-E-0000.bin"
noncomputable def ep000000110010101 : Blocks := ep000000110010101_0
private theorem idp000000110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011001010.list =
    C ((2:ℤ)^68) * horner X vp000000110010101.list + horner X ep000000110010101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110010101 : Branch 1 (-100761639/500000 : ℚ) vp00000011001010 := by
  apply branch_checked idp000000110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-100761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-101011639/250000 : ℚ) by norm_num]
  exact coverp000000110010101
theorem coverp00000011001010 : Covers (-100761639/500000 : ℚ) vp00000011001010 := join_branches bp000000110010100 bp000000110010101
private noncomputable def vp0000001100101_0 : Blocks := edgeBlocks% "full/vectors/0000001100101-V-0000.bin"
noncomputable def vp0000001100101 : Blocks := vp0000001100101_0
private theorem bp00000011001010 : Branch 0 (-100761639/1000000 : ℚ) vp0000001100101 := by
  apply branch_left_normalized (c:=vp00000011001010) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-100761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-100761639/500000 : ℚ) by norm_num]
  exact coverp00000011001010
private noncomputable def ep00000011001011_0 : Blocks := edgeBlocks% "full/vectors/00000011001011-E-0000.bin"
noncomputable def ep00000011001011 : Blocks := ep00000011001011_0
private theorem idp00000011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001100101.list =
    C ((2:ℤ)^119) * horner X vp00000011001011.list + horner X ep00000011001011.list := by
  exact edge_identity (B := (2:ℤ)^267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011001011 : Branch 1 (-100761639/1000000 : ℚ) vp0000001100101 := by
  apply branch_checked idp00000011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-100761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-101261639/500000 : ℚ) by norm_num]
  exact coverp00000011001011
theorem coverp0000001100101 : Covers (-100761639/1000000 : ℚ) vp0000001100101 := join_branches bp00000011001010 bp00000011001011
private noncomputable def vp000000110010011_0 : Blocks := edgeBlocks% "full/vectors/000000110010011-V-0000.bin"
noncomputable def vp000000110010011 : Blocks := vp000000110010011_0
theorem coverp000000110010011 : Covers (-100511639/250000 : ℚ) vp000000110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110010010_0 : Blocks := edgeBlocks% "full/vectors/000000110010010-V-0000.bin"
noncomputable def vp000000110010010 : Blocks := vp000000110010010_0
theorem coverp000000110010010 : Covers (-100261639/250000 : ℚ) vp000000110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011001001_0 : Blocks := edgeBlocks% "full/vectors/00000011001001-V-0000.bin"
noncomputable def vp00000011001001 : Blocks := vp00000011001001_0
private theorem bp000000110010010 : Branch 0 (-100261639/500000 : ℚ) vp00000011001001 := by
  apply branch_left_normalized (c:=vp000000110010010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-100261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-100261639/250000 : ℚ) by norm_num]
  exact coverp000000110010010
private noncomputable def ep000000110010011_0 : Blocks := edgeBlocks% "full/vectors/000000110010011-E-0000.bin"
noncomputable def ep000000110010011 : Blocks := ep000000110010011_0
private theorem idp000000110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011001001.list =
    C ((2:ℤ)^69) * horner X vp000000110010011.list + horner X ep000000110010011.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110010011 : Branch 1 (-100261639/500000 : ℚ) vp00000011001001 := by
  apply branch_checked idp000000110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-100261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-100511639/250000 : ℚ) by norm_num]
  exact coverp000000110010011
theorem coverp00000011001001 : Covers (-100261639/500000 : ℚ) vp00000011001001 := join_branches bp000000110010010 bp000000110010011
private noncomputable def vp000000110010001_0 : Blocks := edgeBlocks% "full/vectors/000000110010001-V-0000.bin"
noncomputable def vp000000110010001 : Blocks := vp000000110010001_0
theorem coverp000000110010001 : Covers (-100011639/250000 : ℚ) vp000000110010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110010000_0 : Blocks := edgeBlocks% "full/vectors/000000110010000-V-0000.bin"
noncomputable def vp000000110010000 : Blocks := vp000000110010000_0
theorem coverp000000110010000 : Covers (-99761639/250000 : ℚ) vp000000110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011001000_0 : Blocks := edgeBlocks% "full/vectors/00000011001000-V-0000.bin"
noncomputable def vp00000011001000 : Blocks := vp00000011001000_0
private theorem bp000000110010000 : Branch 0 (-99761639/500000 : ℚ) vp00000011001000 := by
  apply branch_left_normalized (c:=vp000000110010000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-99761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-99761639/250000 : ℚ) by norm_num]
  exact coverp000000110010000
private noncomputable def ep000000110010001_0 : Blocks := edgeBlocks% "full/vectors/000000110010001-E-0000.bin"
noncomputable def ep000000110010001 : Blocks := ep000000110010001_0
private theorem idp000000110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011001000.list =
    C ((2:ℤ)^70) * horner X vp000000110010001.list + horner X ep000000110010001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110010001 : Branch 1 (-99761639/500000 : ℚ) vp00000011001000 := by
  apply branch_checked idp000000110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-99761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-100011639/250000 : ℚ) by norm_num]
  exact coverp000000110010001
theorem coverp00000011001000 : Covers (-99761639/500000 : ℚ) vp00000011001000 := join_branches bp000000110010000 bp000000110010001
private noncomputable def vp0000001100100_0 : Blocks := edgeBlocks% "full/vectors/0000001100100-V-0000.bin"
noncomputable def vp0000001100100 : Blocks := vp0000001100100_0
private theorem bp00000011001000 : Branch 0 (-99761639/1000000 : ℚ) vp0000001100100 := by
  apply branch_left_normalized (c:=vp00000011001000) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-99761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-99761639/500000 : ℚ) by norm_num]
  exact coverp00000011001000
private noncomputable def ep00000011001001_0 : Blocks := edgeBlocks% "full/vectors/00000011001001-E-0000.bin"
noncomputable def ep00000011001001 : Blocks := ep00000011001001_0
private theorem idp00000011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001100100.list =
    C ((2:ℤ)^121) * horner X vp00000011001001.list + horner X ep00000011001001.list := by
  exact edge_identity (B := (2:ℤ)^267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011001001 : Branch 1 (-99761639/1000000 : ℚ) vp0000001100100 := by
  apply branch_checked idp00000011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-99761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-100261639/500000 : ℚ) by norm_num]
  exact coverp00000011001001
theorem coverp0000001100100 : Covers (-99761639/1000000 : ℚ) vp0000001100100 := join_branches bp00000011001000 bp00000011001001
private noncomputable def vp000000110010_0 : Blocks := edgeBlocks% "full/vectors/000000110010-V-0000.bin"
private noncomputable def vp000000110010_1 : Blocks := edgeBlocks% "full/vectors/000000110010-V-0001.bin"
noncomputable def vp000000110010 : Blocks := (Blocks.join vp000000110010_0 vp000000110010_1)
private theorem bp0000001100100 : Branch 0 (-99761639/2000000 : ℚ) vp000000110010 := by
  apply branch_left_normalized (c:=vp0000001100100) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-99761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-99761639/1000000 : ℚ) by norm_num]
  exact coverp0000001100100
private noncomputable def ep0000001100101_0 : Blocks := edgeBlocks% "full/vectors/0000001100101-E-0000.bin"
private noncomputable def ep0000001100101_1 : Blocks := edgeBlocks% "full/vectors/0000001100101-E-0001.bin"
noncomputable def ep0000001100101 : Blocks := (Blocks.join ep0000001100101_0 ep0000001100101_1)
private theorem idp0000001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110010.list =
    C ((2:ℤ)^223) * horner X vp0000001100101.list + horner X ep0000001100101.list := by
  exact edge_identity (B := (2:ℤ)^418) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001100101 : Branch 1 (-99761639/2000000 : ℚ) vp000000110010 := by
  apply branch_checked idp0000001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-99761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-100761639/1000000 : ℚ) by norm_num]
  exact coverp0000001100101
theorem coverp000000110010 : Covers (-99761639/2000000 : ℚ) vp000000110010 := join_branches bp0000001100100 bp0000001100101
private noncomputable def vp00000011001_0 : Blocks := edgeBlocks% "full/vectors/00000011001-V-0000.bin"
private noncomputable def vp00000011001_1 : Blocks := edgeBlocks% "full/vectors/00000011001-V-0001.bin"
private noncomputable def vp00000011001_2 : Blocks := edgeBlocks% "full/vectors/00000011001-V-0002.bin"
private noncomputable def vp00000011001_3 : Blocks := edgeBlocks% "full/vectors/00000011001-V-0003.bin"
noncomputable def vp00000011001 : Blocks := (Blocks.join (Blocks.join vp00000011001_0 vp00000011001_1) (Blocks.join vp00000011001_2 vp00000011001_3))
private theorem bp000000110010 : Branch 0 (-99761639/4000000 : ℚ) vp00000011001 := by
  apply branch_left_normalized (c:=vp000000110010) (k:=0) (m:=216) (by decide +kernel)
  rw [show 2*(-99761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-99761639/2000000 : ℚ) by norm_num]
  exact coverp000000110010
private noncomputable def ep000000110011_0 : Blocks := edgeBlocks% "full/vectors/000000110011-E-0000.bin"
private noncomputable def ep000000110011_1 : Blocks := edgeBlocks% "full/vectors/000000110011-E-0001.bin"
private noncomputable def ep000000110011_2 : Blocks := edgeBlocks% "full/vectors/000000110011-E-0002.bin"
private noncomputable def ep000000110011_3 : Blocks := edgeBlocks% "full/vectors/000000110011-E-0003.bin"
noncomputable def ep000000110011 : Blocks := (Blocks.join (Blocks.join ep000000110011_0 ep000000110011_1) (Blocks.join ep000000110011_2 ep000000110011_3))
private theorem idp000000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011001.list =
    C ((2:ℤ)^418) * horner X vp000000110011.list + horner X ep000000110011.list := by
  exact edge_identity (B := (2:ℤ)^718) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110011 : Branch 1 (-99761639/4000000 : ℚ) vp00000011001 := by
  apply branch_checked idp000000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-99761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-101761639/2000000 : ℚ) by norm_num]
  exact coverp000000110011
theorem coverp00000011001 : Covers (-99761639/4000000 : ℚ) vp00000011001 := join_branches bp000000110010 bp000000110011
private noncomputable def vp000000110001111_0 : Blocks := edgeBlocks% "full/vectors/000000110001111-V-0000.bin"
noncomputable def vp000000110001111 : Blocks := vp000000110001111_0
theorem coverp000000110001111 : Covers (-99511639/250000 : ℚ) vp000000110001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110001110_0 : Blocks := edgeBlocks% "full/vectors/000000110001110-V-0000.bin"
noncomputable def vp000000110001110 : Blocks := vp000000110001110_0
theorem coverp000000110001110 : Covers (-99261639/250000 : ℚ) vp000000110001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011000111_0 : Blocks := edgeBlocks% "full/vectors/00000011000111-V-0000.bin"
noncomputable def vp00000011000111 : Blocks := vp00000011000111_0
private theorem bp000000110001110 : Branch 0 (-99261639/500000 : ℚ) vp00000011000111 := by
  apply branch_left_normalized (c:=vp000000110001110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-99261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-99261639/250000 : ℚ) by norm_num]
  exact coverp000000110001110
private noncomputable def ep000000110001111_0 : Blocks := edgeBlocks% "full/vectors/000000110001111-E-0000.bin"
noncomputable def ep000000110001111 : Blocks := ep000000110001111_0
private theorem idp000000110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011000111.list =
    C ((2:ℤ)^71) * horner X vp000000110001111.list + horner X ep000000110001111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110001111 : Branch 1 (-99261639/500000 : ℚ) vp00000011000111 := by
  apply branch_checked idp000000110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-99261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-99511639/250000 : ℚ) by norm_num]
  exact coverp000000110001111
theorem coverp00000011000111 : Covers (-99261639/500000 : ℚ) vp00000011000111 := join_branches bp000000110001110 bp000000110001111
private noncomputable def vp000000110001101_0 : Blocks := edgeBlocks% "full/vectors/000000110001101-V-0000.bin"
noncomputable def vp000000110001101 : Blocks := vp000000110001101_0
theorem coverp000000110001101 : Covers (-99011639/250000 : ℚ) vp000000110001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001100011001_0 : Blocks := edgeBlocks% "full/vectors/0000001100011001-V-0000.bin"
noncomputable def vp0000001100011001 : Blocks := vp0000001100011001_0
theorem coverp0000001100011001 : Covers (-98886639/125000 : ℚ) vp0000001100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011000110001_0 : Blocks := edgeBlocks% "full/vectors/00000011000110001-V-0000.bin"
noncomputable def vp00000011000110001 : Blocks := vp00000011000110001_0
theorem coverp00000011000110001 : Covers (-98824139/62500 : ℚ) vp00000011000110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011000110000_0 : Blocks := edgeBlocks% "full/vectors/00000011000110000-V-0000.bin"
noncomputable def vp00000011000110000 : Blocks := vp00000011000110000_0
theorem coverp00000011000110000 : Covers (-98761639/62500 : ℚ) vp00000011000110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001100011000_0 : Blocks := edgeBlocks% "full/vectors/0000001100011000-V-0000.bin"
noncomputable def vp0000001100011000 : Blocks := vp0000001100011000_0
private theorem bp00000011000110000 : Branch 0 (-98761639/125000 : ℚ) vp0000001100011000 := by
  apply branch_left_normalized (c:=vp00000011000110000) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-98761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-98761639/62500 : ℚ) by norm_num]
  exact coverp00000011000110000
private noncomputable def ep00000011000110001_0 : Blocks := edgeBlocks% "full/vectors/00000011000110001-E-0000.bin"
noncomputable def ep00000011000110001 : Blocks := ep00000011000110001_0
private theorem idp00000011000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001100011000.list =
    C ((2:ℤ)^30) * horner X vp00000011000110001.list + horner X ep00000011000110001.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011000110001 : Branch 1 (-98761639/125000 : ℚ) vp0000001100011000 := by
  apply branch_checked idp00000011000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-98761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-98824139/62500 : ℚ) by norm_num]
  exact coverp00000011000110001
theorem coverp0000001100011000 : Covers (-98761639/125000 : ℚ) vp0000001100011000 := join_branches bp00000011000110000 bp00000011000110001
private noncomputable def vp000000110001100_0 : Blocks := edgeBlocks% "full/vectors/000000110001100-V-0000.bin"
noncomputable def vp000000110001100 : Blocks := vp000000110001100_0
private theorem bp0000001100011000 : Branch 0 (-98761639/250000 : ℚ) vp000000110001100 := by
  apply branch_left_normalized (c:=vp0000001100011000) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-98761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-98761639/125000 : ℚ) by norm_num]
  exact coverp0000001100011000
private noncomputable def ep0000001100011001_0 : Blocks := edgeBlocks% "full/vectors/0000001100011001-E-0000.bin"
noncomputable def ep0000001100011001 : Blocks := ep0000001100011001_0
private theorem idp0000001100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110001100.list =
    C ((2:ℤ)^44) * horner X vp0000001100011001.list + horner X ep0000001100011001.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001100011001 : Branch 1 (-98761639/250000 : ℚ) vp000000110001100 := by
  apply branch_checked idp0000001100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-98761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-98886639/125000 : ℚ) by norm_num]
  exact coverp0000001100011001
theorem coverp000000110001100 : Covers (-98761639/250000 : ℚ) vp000000110001100 := join_branches bp0000001100011000 bp0000001100011001
private noncomputable def vp00000011000110_0 : Blocks := edgeBlocks% "full/vectors/00000011000110-V-0000.bin"
noncomputable def vp00000011000110 : Blocks := vp00000011000110_0
private theorem bp000000110001100 : Branch 0 (-98761639/500000 : ℚ) vp00000011000110 := by
  apply branch_left_normalized (c:=vp000000110001100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-98761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-98761639/250000 : ℚ) by norm_num]
  exact coverp000000110001100
private noncomputable def ep000000110001101_0 : Blocks := edgeBlocks% "full/vectors/000000110001101-E-0000.bin"
noncomputable def ep000000110001101 : Blocks := ep000000110001101_0
private theorem idp000000110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011000110.list =
    C ((2:ℤ)^71) * horner X vp000000110001101.list + horner X ep000000110001101.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110001101 : Branch 1 (-98761639/500000 : ℚ) vp00000011000110 := by
  apply branch_checked idp000000110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-98761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-99011639/250000 : ℚ) by norm_num]
  exact coverp000000110001101
theorem coverp00000011000110 : Covers (-98761639/500000 : ℚ) vp00000011000110 := join_branches bp000000110001100 bp000000110001101
private noncomputable def vp0000001100011_0 : Blocks := edgeBlocks% "full/vectors/0000001100011-V-0000.bin"
noncomputable def vp0000001100011 : Blocks := vp0000001100011_0
private theorem bp00000011000110 : Branch 0 (-98761639/1000000 : ℚ) vp0000001100011 := by
  apply branch_left_normalized (c:=vp00000011000110) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-98761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-98761639/500000 : ℚ) by norm_num]
  exact coverp00000011000110
private noncomputable def ep00000011000111_0 : Blocks := edgeBlocks% "full/vectors/00000011000111-E-0000.bin"
noncomputable def ep00000011000111 : Blocks := ep00000011000111_0
private theorem idp00000011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001100011.list =
    C ((2:ℤ)^125) * horner X vp00000011000111.list + horner X ep00000011000111.list := by
  exact edge_identity (B := (2:ℤ)^273) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011000111 : Branch 1 (-98761639/1000000 : ℚ) vp0000001100011 := by
  apply branch_checked idp00000011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-98761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-99261639/500000 : ℚ) by norm_num]
  exact coverp00000011000111
theorem coverp0000001100011 : Covers (-98761639/1000000 : ℚ) vp0000001100011 := join_branches bp00000011000110 bp00000011000111
private noncomputable def vp0000001100010111_0 : Blocks := edgeBlocks% "full/vectors/0000001100010111-V-0000.bin"
noncomputable def vp0000001100010111 : Blocks := vp0000001100010111_0
theorem coverp0000001100010111 : Covers (-98636639/125000 : ℚ) vp0000001100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001100010110_0 : Blocks := edgeBlocks% "full/vectors/0000001100010110-V-0000.bin"
noncomputable def vp0000001100010110 : Blocks := vp0000001100010110_0
theorem coverp0000001100010110 : Covers (-98511639/125000 : ℚ) vp0000001100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110001011_0 : Blocks := edgeBlocks% "full/vectors/000000110001011-V-0000.bin"
noncomputable def vp000000110001011 : Blocks := vp000000110001011_0
private theorem bp0000001100010110 : Branch 0 (-98511639/250000 : ℚ) vp000000110001011 := by
  apply branch_left_normalized (c:=vp0000001100010110) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-98511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-98511639/125000 : ℚ) by norm_num]
  exact coverp0000001100010110
private noncomputable def ep0000001100010111_0 : Blocks := edgeBlocks% "full/vectors/0000001100010111-E-0000.bin"
noncomputable def ep0000001100010111 : Blocks := ep0000001100010111_0
private theorem idp0000001100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110001011.list =
    C ((2:ℤ)^43) * horner X vp0000001100010111.list + horner X ep0000001100010111.list := by
  exact edge_identity (B := (2:ℤ)^154) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001100010111 : Branch 1 (-98511639/250000 : ℚ) vp000000110001011 := by
  apply branch_checked idp0000001100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-98511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-98636639/125000 : ℚ) by norm_num]
  exact coverp0000001100010111
theorem coverp000000110001011 : Covers (-98511639/250000 : ℚ) vp000000110001011 := join_branches bp0000001100010110 bp0000001100010111
private noncomputable def vp000000110001010_0 : Blocks := edgeBlocks% "full/vectors/000000110001010-V-0000.bin"
noncomputable def vp000000110001010 : Blocks := vp000000110001010_0
theorem coverp000000110001010 : Covers (-98261639/250000 : ℚ) vp000000110001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011000101_0 : Blocks := edgeBlocks% "full/vectors/00000011000101-V-0000.bin"
noncomputable def vp00000011000101 : Blocks := vp00000011000101_0
private theorem bp000000110001010 : Branch 0 (-98261639/500000 : ℚ) vp00000011000101 := by
  apply branch_left_normalized (c:=vp000000110001010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-98261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-98261639/250000 : ℚ) by norm_num]
  exact coverp000000110001010
private noncomputable def ep000000110001011_0 : Blocks := edgeBlocks% "full/vectors/000000110001011-E-0000.bin"
noncomputable def ep000000110001011 : Blocks := ep000000110001011_0
private theorem idp000000110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011000101.list =
    C ((2:ℤ)^68) * horner X vp000000110001011.list + horner X ep000000110001011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110001011 : Branch 1 (-98261639/500000 : ℚ) vp00000011000101 := by
  apply branch_checked idp000000110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-98261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-98511639/250000 : ℚ) by norm_num]
  exact coverp000000110001011
theorem coverp00000011000101 : Covers (-98261639/500000 : ℚ) vp00000011000101 := join_branches bp000000110001010 bp000000110001011
private noncomputable def vp000000110001001_0 : Blocks := edgeBlocks% "full/vectors/000000110001001-V-0000.bin"
noncomputable def vp000000110001001 : Blocks := vp000000110001001_0
theorem coverp000000110001001 : Covers (-98011639/250000 : ℚ) vp000000110001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110001000_0 : Blocks := edgeBlocks% "full/vectors/000000110001000-V-0000.bin"
noncomputable def vp000000110001000 : Blocks := vp000000110001000_0
theorem coverp000000110001000 : Covers (-97761639/250000 : ℚ) vp000000110001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011000100_0 : Blocks := edgeBlocks% "full/vectors/00000011000100-V-0000.bin"
noncomputable def vp00000011000100 : Blocks := vp00000011000100_0
private theorem bp000000110001000 : Branch 0 (-97761639/500000 : ℚ) vp00000011000100 := by
  apply branch_left_normalized (c:=vp000000110001000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-97761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-97761639/250000 : ℚ) by norm_num]
  exact coverp000000110001000
private noncomputable def ep000000110001001_0 : Blocks := edgeBlocks% "full/vectors/000000110001001-E-0000.bin"
noncomputable def ep000000110001001 : Blocks := ep000000110001001_0
private theorem idp000000110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011000100.list =
    C ((2:ℤ)^66) * horner X vp000000110001001.list + horner X ep000000110001001.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110001001 : Branch 1 (-97761639/500000 : ℚ) vp00000011000100 := by
  apply branch_checked idp000000110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-97761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-98011639/250000 : ℚ) by norm_num]
  exact coverp000000110001001
theorem coverp00000011000100 : Covers (-97761639/500000 : ℚ) vp00000011000100 := join_branches bp000000110001000 bp000000110001001
private noncomputable def vp0000001100010_0 : Blocks := edgeBlocks% "full/vectors/0000001100010-V-0000.bin"
noncomputable def vp0000001100010 : Blocks := vp0000001100010_0
private theorem bp00000011000100 : Branch 0 (-97761639/1000000 : ℚ) vp0000001100010 := by
  apply branch_left_normalized (c:=vp00000011000100) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-97761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-97761639/500000 : ℚ) by norm_num]
  exact coverp00000011000100
private noncomputable def ep00000011000101_0 : Blocks := edgeBlocks% "full/vectors/00000011000101-E-0000.bin"
noncomputable def ep00000011000101 : Blocks := ep00000011000101_0
private theorem idp00000011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001100010.list =
    C ((2:ℤ)^118) * horner X vp00000011000101.list + horner X ep00000011000101.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011000101 : Branch 1 (-97761639/1000000 : ℚ) vp0000001100010 := by
  apply branch_checked idp00000011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-97761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-98261639/500000 : ℚ) by norm_num]
  exact coverp00000011000101
theorem coverp0000001100010 : Covers (-97761639/1000000 : ℚ) vp0000001100010 := join_branches bp00000011000100 bp00000011000101
private noncomputable def vp000000110001_0 : Blocks := edgeBlocks% "full/vectors/000000110001-V-0000.bin"
private noncomputable def vp000000110001_1 : Blocks := edgeBlocks% "full/vectors/000000110001-V-0001.bin"
noncomputable def vp000000110001 : Blocks := (Blocks.join vp000000110001_0 vp000000110001_1)
private theorem bp0000001100010 : Branch 0 (-97761639/2000000 : ℚ) vp000000110001 := by
  apply branch_left_normalized (c:=vp0000001100010) (k:=0) (m:=116) (by decide +kernel)
  rw [show 2*(-97761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-97761639/1000000 : ℚ) by norm_num]
  exact coverp0000001100010
private noncomputable def ep0000001100011_0 : Blocks := edgeBlocks% "full/vectors/0000001100011-E-0000.bin"
private noncomputable def ep0000001100011_1 : Blocks := edgeBlocks% "full/vectors/0000001100011-E-0001.bin"
noncomputable def ep0000001100011 : Blocks := (Blocks.join ep0000001100011_0 ep0000001100011_1)
private theorem idp0000001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110001.list =
    C ((2:ℤ)^217) * horner X vp0000001100011.list + horner X ep0000001100011.list := by
  exact edge_identity (B := (2:ℤ)^416) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001100011 : Branch 1 (-97761639/2000000 : ℚ) vp000000110001 := by
  apply branch_checked idp0000001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-97761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-98761639/1000000 : ℚ) by norm_num]
  exact coverp0000001100011
theorem coverp000000110001 : Covers (-97761639/2000000 : ℚ) vp000000110001 := join_branches bp0000001100010 bp0000001100011
private noncomputable def vp000000110000111_0 : Blocks := edgeBlocks% "full/vectors/000000110000111-V-0000.bin"
noncomputable def vp000000110000111 : Blocks := vp000000110000111_0
theorem coverp000000110000111 : Covers (-97511639/250000 : ℚ) vp000000110000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110000110_0 : Blocks := edgeBlocks% "full/vectors/000000110000110-V-0000.bin"
noncomputable def vp000000110000110 : Blocks := vp000000110000110_0
theorem coverp000000110000110 : Covers (-97261639/250000 : ℚ) vp000000110000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011000011_0 : Blocks := edgeBlocks% "full/vectors/00000011000011-V-0000.bin"
noncomputable def vp00000011000011 : Blocks := vp00000011000011_0
private theorem bp000000110000110 : Branch 0 (-97261639/500000 : ℚ) vp00000011000011 := by
  apply branch_left_normalized (c:=vp000000110000110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-97261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-97261639/250000 : ℚ) by norm_num]
  exact coverp000000110000110
private noncomputable def ep000000110000111_0 : Blocks := edgeBlocks% "full/vectors/000000110000111-E-0000.bin"
noncomputable def ep000000110000111 : Blocks := ep000000110000111_0
private theorem idp000000110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011000011.list =
    C ((2:ℤ)^67) * horner X vp000000110000111.list + horner X ep000000110000111.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110000111 : Branch 1 (-97261639/500000 : ℚ) vp00000011000011 := by
  apply branch_checked idp000000110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-97261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-97511639/250000 : ℚ) by norm_num]
  exact coverp000000110000111
theorem coverp00000011000011 : Covers (-97261639/500000 : ℚ) vp00000011000011 := join_branches bp000000110000110 bp000000110000111
private noncomputable def vp000000110000101_0 : Blocks := edgeBlocks% "full/vectors/000000110000101-V-0000.bin"
noncomputable def vp000000110000101 : Blocks := vp000000110000101_0
theorem coverp000000110000101 : Covers (-97011639/250000 : ℚ) vp000000110000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110000100_0 : Blocks := edgeBlocks% "full/vectors/000000110000100-V-0000.bin"
noncomputable def vp000000110000100 : Blocks := vp000000110000100_0
theorem coverp000000110000100 : Covers (-96761639/250000 : ℚ) vp000000110000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011000010_0 : Blocks := edgeBlocks% "full/vectors/00000011000010-V-0000.bin"
noncomputable def vp00000011000010 : Blocks := vp00000011000010_0
private theorem bp000000110000100 : Branch 0 (-96761639/500000 : ℚ) vp00000011000010 := by
  apply branch_left_normalized (c:=vp000000110000100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-96761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-96761639/250000 : ℚ) by norm_num]
  exact coverp000000110000100
private noncomputable def ep000000110000101_0 : Blocks := edgeBlocks% "full/vectors/000000110000101-E-0000.bin"
noncomputable def ep000000110000101 : Blocks := ep000000110000101_0
private theorem idp000000110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011000010.list =
    C ((2:ℤ)^67) * horner X vp000000110000101.list + horner X ep000000110000101.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110000101 : Branch 1 (-96761639/500000 : ℚ) vp00000011000010 := by
  apply branch_checked idp000000110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-96761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-97011639/250000 : ℚ) by norm_num]
  exact coverp000000110000101
theorem coverp00000011000010 : Covers (-96761639/500000 : ℚ) vp00000011000010 := join_branches bp000000110000100 bp000000110000101
private noncomputable def vp0000001100001_0 : Blocks := edgeBlocks% "full/vectors/0000001100001-V-0000.bin"
noncomputable def vp0000001100001 : Blocks := vp0000001100001_0
private theorem bp00000011000010 : Branch 0 (-96761639/1000000 : ℚ) vp0000001100001 := by
  apply branch_left_normalized (c:=vp00000011000010) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-96761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-96761639/500000 : ℚ) by norm_num]
  exact coverp00000011000010
private noncomputable def ep00000011000011_0 : Blocks := edgeBlocks% "full/vectors/00000011000011-E-0000.bin"
noncomputable def ep00000011000011 : Blocks := ep00000011000011_0
private theorem idp00000011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001100001.list =
    C ((2:ℤ)^118) * horner X vp00000011000011.list + horner X ep00000011000011.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011000011 : Branch 1 (-96761639/1000000 : ℚ) vp0000001100001 := by
  apply branch_checked idp00000011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-96761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-97261639/500000 : ℚ) by norm_num]
  exact coverp00000011000011
theorem coverp0000001100001 : Covers (-96761639/1000000 : ℚ) vp0000001100001 := join_branches bp00000011000010 bp00000011000011
private noncomputable def vp000000110000011_0 : Blocks := edgeBlocks% "full/vectors/000000110000011-V-0000.bin"
noncomputable def vp000000110000011 : Blocks := vp000000110000011_0
theorem coverp000000110000011 : Covers (-96511639/250000 : ℚ) vp000000110000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110000010_0 : Blocks := edgeBlocks% "full/vectors/000000110000010-V-0000.bin"
noncomputable def vp000000110000010 : Blocks := vp000000110000010_0
theorem coverp000000110000010 : Covers (-96261639/250000 : ℚ) vp000000110000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011000001_0 : Blocks := edgeBlocks% "full/vectors/00000011000001-V-0000.bin"
noncomputable def vp00000011000001 : Blocks := vp00000011000001_0
private theorem bp000000110000010 : Branch 0 (-96261639/500000 : ℚ) vp00000011000001 := by
  apply branch_left_normalized (c:=vp000000110000010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-96261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-96261639/250000 : ℚ) by norm_num]
  exact coverp000000110000010
private noncomputable def ep000000110000011_0 : Blocks := edgeBlocks% "full/vectors/000000110000011-E-0000.bin"
noncomputable def ep000000110000011 : Blocks := ep000000110000011_0
private theorem idp000000110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011000001.list =
    C ((2:ℤ)^66) * horner X vp000000110000011.list + horner X ep000000110000011.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110000011 : Branch 1 (-96261639/500000 : ℚ) vp00000011000001 := by
  apply branch_checked idp000000110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-96261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-96511639/250000 : ℚ) by norm_num]
  exact coverp000000110000011
theorem coverp00000011000001 : Covers (-96261639/500000 : ℚ) vp00000011000001 := join_branches bp000000110000010 bp000000110000011
private noncomputable def vp000000110000001_0 : Blocks := edgeBlocks% "full/vectors/000000110000001-V-0000.bin"
noncomputable def vp000000110000001 : Blocks := vp000000110000001_0
theorem coverp000000110000001 : Covers (-96011639/250000 : ℚ) vp000000110000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000110000000_0 : Blocks := edgeBlocks% "full/vectors/000000110000000-V-0000.bin"
noncomputable def vp000000110000000 : Blocks := vp000000110000000_0
theorem coverp000000110000000 : Covers (-95761639/250000 : ℚ) vp000000110000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000011000000_0 : Blocks := edgeBlocks% "full/vectors/00000011000000-V-0000.bin"
noncomputable def vp00000011000000 : Blocks := vp00000011000000_0
private theorem bp000000110000000 : Branch 0 (-95761639/500000 : ℚ) vp00000011000000 := by
  apply branch_left_normalized (c:=vp000000110000000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-95761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-95761639/250000 : ℚ) by norm_num]
  exact coverp000000110000000
private noncomputable def ep000000110000001_0 : Blocks := edgeBlocks% "full/vectors/000000110000001-E-0000.bin"
noncomputable def ep000000110000001 : Blocks := ep000000110000001_0
private theorem idp000000110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011000000.list =
    C ((2:ℤ)^67) * horner X vp000000110000001.list + horner X ep000000110000001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110000001 : Branch 1 (-95761639/500000 : ℚ) vp00000011000000 := by
  apply branch_checked idp000000110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-95761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-96011639/250000 : ℚ) by norm_num]
  exact coverp000000110000001
theorem coverp00000011000000 : Covers (-95761639/500000 : ℚ) vp00000011000000 := join_branches bp000000110000000 bp000000110000001
private noncomputable def vp0000001100000_0 : Blocks := edgeBlocks% "full/vectors/0000001100000-V-0000.bin"
noncomputable def vp0000001100000 : Blocks := vp0000001100000_0
private theorem bp00000011000000 : Branch 0 (-95761639/1000000 : ℚ) vp0000001100000 := by
  apply branch_left_normalized (c:=vp00000011000000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-95761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-95761639/500000 : ℚ) by norm_num]
  exact coverp00000011000000
private noncomputable def ep00000011000001_0 : Blocks := edgeBlocks% "full/vectors/00000011000001-E-0000.bin"
noncomputable def ep00000011000001 : Blocks := ep00000011000001_0
private theorem idp00000011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001100000.list =
    C ((2:ℤ)^118) * horner X vp00000011000001.list + horner X ep00000011000001.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011000001 : Branch 1 (-95761639/1000000 : ℚ) vp0000001100000 := by
  apply branch_checked idp00000011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-95761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-96261639/500000 : ℚ) by norm_num]
  exact coverp00000011000001
theorem coverp0000001100000 : Covers (-95761639/1000000 : ℚ) vp0000001100000 := join_branches bp00000011000000 bp00000011000001
private noncomputable def vp000000110000_0 : Blocks := edgeBlocks% "full/vectors/000000110000-V-0000.bin"
private noncomputable def vp000000110000_1 : Blocks := edgeBlocks% "full/vectors/000000110000-V-0001.bin"
noncomputable def vp000000110000 : Blocks := (Blocks.join vp000000110000_0 vp000000110000_1)
private theorem bp0000001100000 : Branch 0 (-95761639/2000000 : ℚ) vp000000110000 := by
  apply branch_left_normalized (c:=vp0000001100000) (k:=0) (m:=115) (by decide +kernel)
  rw [show 2*(-95761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-95761639/1000000 : ℚ) by norm_num]
  exact coverp0000001100000
private noncomputable def ep0000001100001_0 : Blocks := edgeBlocks% "full/vectors/0000001100001-E-0000.bin"
private noncomputable def ep0000001100001_1 : Blocks := edgeBlocks% "full/vectors/0000001100001-E-0001.bin"
noncomputable def ep0000001100001 : Blocks := (Blocks.join ep0000001100001_0 ep0000001100001_1)
private theorem idp0000001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110000.list =
    C ((2:ℤ)^221) * horner X vp0000001100001.list + horner X ep0000001100001.list := by
  exact edge_identity (B := (2:ℤ)^413) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001100001 : Branch 1 (-95761639/2000000 : ℚ) vp000000110000 := by
  apply branch_checked idp0000001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-95761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-96761639/1000000 : ℚ) by norm_num]
  exact coverp0000001100001
theorem coverp000000110000 : Covers (-95761639/2000000 : ℚ) vp000000110000 := join_branches bp0000001100000 bp0000001100001
private noncomputable def vp00000011000_0 : Blocks := edgeBlocks% "full/vectors/00000011000-V-0000.bin"
private noncomputable def vp00000011000_1 : Blocks := edgeBlocks% "full/vectors/00000011000-V-0001.bin"
private noncomputable def vp00000011000_2 : Blocks := edgeBlocks% "full/vectors/00000011000-V-0002.bin"
private noncomputable def vp00000011000_3 : Blocks := edgeBlocks% "full/vectors/00000011000-V-0003.bin"
noncomputable def vp00000011000 : Blocks := (Blocks.join (Blocks.join vp00000011000_0 vp00000011000_1) (Blocks.join vp00000011000_2 vp00000011000_3))
private theorem bp000000110000 : Branch 0 (-95761639/4000000 : ℚ) vp00000011000 := by
  apply branch_left_normalized (c:=vp000000110000) (k:=0) (m:=216) (by decide +kernel)
  rw [show 2*(-95761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-95761639/2000000 : ℚ) by norm_num]
  exact coverp000000110000
private noncomputable def ep000000110001_0 : Blocks := edgeBlocks% "full/vectors/000000110001-E-0000.bin"
private noncomputable def ep000000110001_1 : Blocks := edgeBlocks% "full/vectors/000000110001-E-0001.bin"
private noncomputable def ep000000110001_2 : Blocks := edgeBlocks% "full/vectors/000000110001-E-0002.bin"
private noncomputable def ep000000110001_3 : Blocks := edgeBlocks% "full/vectors/000000110001-E-0003.bin"
noncomputable def ep000000110001 : Blocks := (Blocks.join (Blocks.join ep000000110001_0 ep000000110001_1) (Blocks.join ep000000110001_2 ep000000110001_3))
private theorem idp000000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011000.list =
    C ((2:ℤ)^423) * horner X vp000000110001.list + horner X ep000000110001.list := by
  exact edge_identity (B := (2:ℤ)^718) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000110001 : Branch 1 (-95761639/4000000 : ℚ) vp00000011000 := by
  apply branch_checked idp000000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-95761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-97761639/2000000 : ℚ) by norm_num]
  exact coverp000000110001
theorem coverp00000011000 : Covers (-95761639/4000000 : ℚ) vp00000011000 := join_branches bp000000110000 bp000000110001
private noncomputable def vp0000001100_0 : Blocks := edgeBlocks% "full/vectors/0000001100-V-0000.bin"
private noncomputable def vp0000001100_1 : Blocks := edgeBlocks% "full/vectors/0000001100-V-0001.bin"
private noncomputable def vp0000001100_2 : Blocks := edgeBlocks% "full/vectors/0000001100-V-0002.bin"
private noncomputable def vp0000001100_3 : Blocks := edgeBlocks% "full/vectors/0000001100-V-0003.bin"
private noncomputable def vp0000001100_4 : Blocks := edgeBlocks% "full/vectors/0000001100-V-0004.bin"
private noncomputable def vp0000001100_5 : Blocks := edgeBlocks% "full/vectors/0000001100-V-0005.bin"
private noncomputable def vp0000001100_6 : Blocks := edgeBlocks% "full/vectors/0000001100-V-0006.bin"
noncomputable def vp0000001100 : Blocks := (Blocks.join (Blocks.join vp0000001100_0 (Blocks.join vp0000001100_1 vp0000001100_2)) (Blocks.join (Blocks.join vp0000001100_3 vp0000001100_4) (Blocks.join vp0000001100_5 vp0000001100_6)))
private theorem bp00000011000 : Branch 0 (-95761639/8000000 : ℚ) vp0000001100 := by
  apply branch_left_normalized (c:=vp00000011000) (k:=0) (m:=414) (by decide +kernel)
  rw [show 2*(-95761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-95761639/4000000 : ℚ) by norm_num]
  exact coverp00000011000
private noncomputable def ep00000011001_0 : Blocks := edgeBlocks% "full/vectors/00000011001-E-0000.bin"
private noncomputable def ep00000011001_1 : Blocks := edgeBlocks% "full/vectors/00000011001-E-0001.bin"
private noncomputable def ep00000011001_2 : Blocks := edgeBlocks% "full/vectors/00000011001-E-0002.bin"
private noncomputable def ep00000011001_3 : Blocks := edgeBlocks% "full/vectors/00000011001-E-0003.bin"
private noncomputable def ep00000011001_4 : Blocks := edgeBlocks% "full/vectors/00000011001-E-0004.bin"
private noncomputable def ep00000011001_5 : Blocks := edgeBlocks% "full/vectors/00000011001-E-0005.bin"
private noncomputable def ep00000011001_6 : Blocks := edgeBlocks% "full/vectors/00000011001-E-0006.bin"
noncomputable def ep00000011001 : Blocks := (Blocks.join (Blocks.join ep00000011001_0 (Blocks.join ep00000011001_1 ep00000011001_2)) (Blocks.join (Blocks.join ep00000011001_3 ep00000011001_4) (Blocks.join ep00000011001_5 ep00000011001_6)))
private theorem idp00000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001100.list =
    C ((2:ℤ)^825) * horner X vp00000011001.list + horner X ep00000011001.list := by
  exact edge_identity (B := (2:ℤ)^1324) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000011001 : Branch 1 (-95761639/8000000 : ℚ) vp0000001100 := by
  apply branch_checked idp00000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-95761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-99761639/4000000 : ℚ) by norm_num]
  exact coverp00000011001
theorem coverp0000001100 : Covers (-95761639/8000000 : ℚ) vp0000001100 := join_branches bp00000011000 bp00000011001
private noncomputable def vp000000110_0 : Blocks := edgeBlocks% "full/vectors/000000110-V-0000.bin"
private noncomputable def vp000000110_1 : Blocks := edgeBlocks% "full/vectors/000000110-V-0001.bin"
private noncomputable def vp000000110_2 : Blocks := edgeBlocks% "full/vectors/000000110-V-0002.bin"
private noncomputable def vp000000110_3 : Blocks := edgeBlocks% "full/vectors/000000110-V-0003.bin"
private noncomputable def vp000000110_4 : Blocks := edgeBlocks% "full/vectors/000000110-V-0004.bin"
private noncomputable def vp000000110_5 : Blocks := edgeBlocks% "full/vectors/000000110-V-0005.bin"
private noncomputable def vp000000110_6 : Blocks := edgeBlocks% "full/vectors/000000110-V-0006.bin"
private noncomputable def vp000000110_7 : Blocks := edgeBlocks% "full/vectors/000000110-V-0007.bin"
private noncomputable def vp000000110_8 : Blocks := edgeBlocks% "full/vectors/000000110-V-0008.bin"
private noncomputable def vp000000110_9 : Blocks := edgeBlocks% "full/vectors/000000110-V-0009.bin"
private noncomputable def vp000000110_10 : Blocks := edgeBlocks% "full/vectors/000000110-V-0010.bin"
private noncomputable def vp000000110_11 : Blocks := edgeBlocks% "full/vectors/000000110-V-0011.bin"
private noncomputable def vp000000110_12 : Blocks := edgeBlocks% "full/vectors/000000110-V-0012.bin"
noncomputable def vp000000110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000000110_0 (Blocks.join vp000000110_1 vp000000110_2)) (Blocks.join vp000000110_3 (Blocks.join vp000000110_4 vp000000110_5))) (Blocks.join (Blocks.join vp000000110_6 (Blocks.join vp000000110_7 vp000000110_8)) (Blocks.join (Blocks.join vp000000110_9 vp000000110_10) (Blocks.join vp000000110_11 vp000000110_12))))
private theorem bp0000001100 : Branch 0 (-95761639/16000000 : ℚ) vp000000110 := by
  apply branch_left_normalized (c:=vp0000001100) (k:=0) (m:=808) (by decide +kernel)
  rw [show 2*(-95761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-95761639/8000000 : ℚ) by norm_num]
  exact coverp0000001100
private noncomputable def ep0000001101_0 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0000.bin"
private noncomputable def ep0000001101_1 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0001.bin"
private noncomputable def ep0000001101_2 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0002.bin"
private noncomputable def ep0000001101_3 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0003.bin"
private noncomputable def ep0000001101_4 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0004.bin"
private noncomputable def ep0000001101_5 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0005.bin"
private noncomputable def ep0000001101_6 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0006.bin"
private noncomputable def ep0000001101_7 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0007.bin"
private noncomputable def ep0000001101_8 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0008.bin"
private noncomputable def ep0000001101_9 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0009.bin"
private noncomputable def ep0000001101_10 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0010.bin"
private noncomputable def ep0000001101_11 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0011.bin"
private noncomputable def ep0000001101_12 : Blocks := edgeBlocks% "full/vectors/0000001101-E-0012.bin"
noncomputable def ep0000001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000001101_0 (Blocks.join ep0000001101_1 ep0000001101_2)) (Blocks.join ep0000001101_3 (Blocks.join ep0000001101_4 ep0000001101_5))) (Blocks.join (Blocks.join ep0000001101_6 (Blocks.join ep0000001101_7 ep0000001101_8)) (Blocks.join (Blocks.join ep0000001101_9 ep0000001101_10) (Blocks.join ep0000001101_11 ep0000001101_12))))
private theorem idp0000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000110.list =
    C ((2:ℤ)^1619) * horner X vp0000001101.list + horner X ep0000001101.list := by
  exact edge_identity (B := (2:ℤ)^2518) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001101 : Branch 1 (-95761639/16000000 : ℚ) vp000000110 := by
  apply branch_checked idp0000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-95761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-103761639/8000000 : ℚ) by norm_num]
  exact coverp0000001101
theorem coverp000000110 : Covers (-95761639/16000000 : ℚ) vp000000110 := join_branches bp0000001100 bp0000001101
private noncomputable def vp00000011_0 : Blocks := edgeBlocks% "full/vectors/00000011-V-0000.bin"
private noncomputable def vp00000011_1 : Blocks := edgeBlocks% "full/vectors/00000011-V-0001.bin"
private noncomputable def vp00000011_2 : Blocks := edgeBlocks% "full/vectors/00000011-V-0002.bin"
private noncomputable def vp00000011_3 : Blocks := edgeBlocks% "full/vectors/00000011-V-0003.bin"
private noncomputable def vp00000011_4 : Blocks := edgeBlocks% "full/vectors/00000011-V-0004.bin"
private noncomputable def vp00000011_5 : Blocks := edgeBlocks% "full/vectors/00000011-V-0005.bin"
private noncomputable def vp00000011_6 : Blocks := edgeBlocks% "full/vectors/00000011-V-0006.bin"
private noncomputable def vp00000011_7 : Blocks := edgeBlocks% "full/vectors/00000011-V-0007.bin"
private noncomputable def vp00000011_8 : Blocks := edgeBlocks% "full/vectors/00000011-V-0008.bin"
private noncomputable def vp00000011_9 : Blocks := edgeBlocks% "full/vectors/00000011-V-0009.bin"
private noncomputable def vp00000011_10 : Blocks := edgeBlocks% "full/vectors/00000011-V-0010.bin"
private noncomputable def vp00000011_11 : Blocks := edgeBlocks% "full/vectors/00000011-V-0011.bin"
private noncomputable def vp00000011_12 : Blocks := edgeBlocks% "full/vectors/00000011-V-0012.bin"
private noncomputable def vp00000011_13 : Blocks := edgeBlocks% "full/vectors/00000011-V-0013.bin"
private noncomputable def vp00000011_14 : Blocks := edgeBlocks% "full/vectors/00000011-V-0014.bin"
private noncomputable def vp00000011_15 : Blocks := edgeBlocks% "full/vectors/00000011-V-0015.bin"
private noncomputable def vp00000011_16 : Blocks := edgeBlocks% "full/vectors/00000011-V-0016.bin"
private noncomputable def vp00000011_17 : Blocks := edgeBlocks% "full/vectors/00000011-V-0017.bin"
private noncomputable def vp00000011_18 : Blocks := edgeBlocks% "full/vectors/00000011-V-0018.bin"
private noncomputable def vp00000011_19 : Blocks := edgeBlocks% "full/vectors/00000011-V-0019.bin"
private noncomputable def vp00000011_20 : Blocks := edgeBlocks% "full/vectors/00000011-V-0020.bin"
private noncomputable def vp00000011_21 : Blocks := edgeBlocks% "full/vectors/00000011-V-0021.bin"
private noncomputable def vp00000011_22 : Blocks := edgeBlocks% "full/vectors/00000011-V-0022.bin"
private noncomputable def vp00000011_23 : Blocks := edgeBlocks% "full/vectors/00000011-V-0023.bin"
private noncomputable def vp00000011_24 : Blocks := edgeBlocks% "full/vectors/00000011-V-0024.bin"
noncomputable def vp00000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00000011_0 (Blocks.join vp00000011_1 vp00000011_2)) (Blocks.join vp00000011_3 (Blocks.join vp00000011_4 vp00000011_5))) (Blocks.join (Blocks.join vp00000011_6 (Blocks.join vp00000011_7 vp00000011_8)) (Blocks.join vp00000011_9 (Blocks.join vp00000011_10 vp00000011_11)))) (Blocks.join (Blocks.join (Blocks.join vp00000011_12 (Blocks.join vp00000011_13 vp00000011_14)) (Blocks.join vp00000011_15 (Blocks.join vp00000011_16 vp00000011_17))) (Blocks.join (Blocks.join vp00000011_18 (Blocks.join vp00000011_19 vp00000011_20)) (Blocks.join (Blocks.join vp00000011_21 vp00000011_22) (Blocks.join vp00000011_23 vp00000011_24)))))
private theorem bp000000110 : Branch 0 (-95761639/32000000 : ℚ) vp00000011 := by
  apply branch_left_normalized (c:=vp000000110) (k:=0) (m:=1582) (by decide +kernel)
  rw [show 2*(-95761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-95761639/16000000 : ℚ) by norm_num]
  exact coverp000000110
private noncomputable def ep000000111_0 : Blocks := edgeBlocks% "full/vectors/000000111-E-0000.bin"
private noncomputable def ep000000111_1 : Blocks := edgeBlocks% "full/vectors/000000111-E-0001.bin"
private noncomputable def ep000000111_2 : Blocks := edgeBlocks% "full/vectors/000000111-E-0002.bin"
private noncomputable def ep000000111_3 : Blocks := edgeBlocks% "full/vectors/000000111-E-0003.bin"
private noncomputable def ep000000111_4 : Blocks := edgeBlocks% "full/vectors/000000111-E-0004.bin"
private noncomputable def ep000000111_5 : Blocks := edgeBlocks% "full/vectors/000000111-E-0005.bin"
private noncomputable def ep000000111_6 : Blocks := edgeBlocks% "full/vectors/000000111-E-0006.bin"
private noncomputable def ep000000111_7 : Blocks := edgeBlocks% "full/vectors/000000111-E-0007.bin"
private noncomputable def ep000000111_8 : Blocks := edgeBlocks% "full/vectors/000000111-E-0008.bin"
private noncomputable def ep000000111_9 : Blocks := edgeBlocks% "full/vectors/000000111-E-0009.bin"
private noncomputable def ep000000111_10 : Blocks := edgeBlocks% "full/vectors/000000111-E-0010.bin"
private noncomputable def ep000000111_11 : Blocks := edgeBlocks% "full/vectors/000000111-E-0011.bin"
private noncomputable def ep000000111_12 : Blocks := edgeBlocks% "full/vectors/000000111-E-0012.bin"
private noncomputable def ep000000111_13 : Blocks := edgeBlocks% "full/vectors/000000111-E-0013.bin"
private noncomputable def ep000000111_14 : Blocks := edgeBlocks% "full/vectors/000000111-E-0014.bin"
private noncomputable def ep000000111_15 : Blocks := edgeBlocks% "full/vectors/000000111-E-0015.bin"
private noncomputable def ep000000111_16 : Blocks := edgeBlocks% "full/vectors/000000111-E-0016.bin"
private noncomputable def ep000000111_17 : Blocks := edgeBlocks% "full/vectors/000000111-E-0017.bin"
private noncomputable def ep000000111_18 : Blocks := edgeBlocks% "full/vectors/000000111-E-0018.bin"
private noncomputable def ep000000111_19 : Blocks := edgeBlocks% "full/vectors/000000111-E-0019.bin"
private noncomputable def ep000000111_20 : Blocks := edgeBlocks% "full/vectors/000000111-E-0020.bin"
private noncomputable def ep000000111_21 : Blocks := edgeBlocks% "full/vectors/000000111-E-0021.bin"
private noncomputable def ep000000111_22 : Blocks := edgeBlocks% "full/vectors/000000111-E-0022.bin"
private noncomputable def ep000000111_23 : Blocks := edgeBlocks% "full/vectors/000000111-E-0023.bin"
private noncomputable def ep000000111_24 : Blocks := edgeBlocks% "full/vectors/000000111-E-0024.bin"
noncomputable def ep000000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep000000111_0 (Blocks.join ep000000111_1 ep000000111_2)) (Blocks.join ep000000111_3 (Blocks.join ep000000111_4 ep000000111_5))) (Blocks.join (Blocks.join ep000000111_6 (Blocks.join ep000000111_7 ep000000111_8)) (Blocks.join ep000000111_9 (Blocks.join ep000000111_10 ep000000111_11)))) (Blocks.join (Blocks.join (Blocks.join ep000000111_12 (Blocks.join ep000000111_13 ep000000111_14)) (Blocks.join ep000000111_15 (Blocks.join ep000000111_16 ep000000111_17))) (Blocks.join (Blocks.join ep000000111_18 (Blocks.join ep000000111_19 ep000000111_20)) (Blocks.join (Blocks.join ep000000111_21 ep000000111_22) (Blocks.join ep000000111_23 ep000000111_24)))))
private def ptsp000000111 : List ℤ := [((2:ℤ)^3904+0),((2:ℤ)^3904+1)]
private theorem boundp000000111 : 2^vp00000011.size*absSum vp00000011.list + ((2:ℤ)^3154*absSum vp000000111.list+absSum ep000000111.list) < (2:ℤ)^4838 := by decide +kernel
private theorem pointp000000111_0 : fastHom 1 ((2:ℤ)^3904+0) vp00000011 = ((2:ℤ)^3154)*vp000000111.subst ((2:ℤ)^3904+0)+ep000000111.subst ((2:ℤ)^3904+0) := by decide +kernel
private theorem pointp000000111_1 : fastHom 1 ((2:ℤ)^3904+1) vp00000011 = ((2:ℤ)^3154)*vp000000111.subst ((2:ℤ)^3904+1)+ep000000111.subst ((2:ℤ)^3904+1) := by decide +kernel
private theorem checkp000000111 (x:ℤ) (hx:x ∈ ptsp000000111) : fastHom 1 x vp00000011 = ((2:ℤ)^3154)*vp000000111.subst x+ep000000111.subst x := by
  simp only [ptsp000000111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp000000111_0
  · exact pointp000000111_1
private theorem idp000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000011.list =
    C ((2:ℤ)^3154) * horner X vp000000111.list + horner X ep000000111.list := by
  apply edge_identity (B := (2:ℤ)^4838) (by decide) (by positivity) (by positivity) boundp000000111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp000000111 (by decide +kernel)
  · have h : ptsp000000111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp000000111.trans_le (by decide +kernel)
  · exact checkp000000111
private theorem bp000000111 : Branch 1 (-95761639/32000000 : ℚ) vp00000011 := by
  apply branch_checked idp000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-95761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-111761639/16000000 : ℚ) by norm_num]
  exact coverp000000111
theorem coverp00000011 : Covers (-95761639/32000000 : ℚ) vp00000011 := join_branches bp000000110 bp000000111
end NextProof.EdgeFull

