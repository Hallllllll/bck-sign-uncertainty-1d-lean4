import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00028

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000000110111111_0 : Blocks := edgeBlocks% "full/vectors/0000000110111111-V-0000.bin"
noncomputable def vp0000000110111111 : Blocks := vp0000000110111111_0
theorem coverp0000000110111111 : Covers (-55636639/125000 : ℚ) vp0000000110111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110111110_0 : Blocks := edgeBlocks% "full/vectors/0000000110111110-V-0000.bin"
noncomputable def vp0000000110111110 : Blocks := vp0000000110111110_0
theorem coverp0000000110111110 : Covers (-55511639/125000 : ℚ) vp0000000110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011011111_0 : Blocks := edgeBlocks% "full/vectors/000000011011111-V-0000.bin"
noncomputable def vp000000011011111 : Blocks := vp000000011011111_0
private theorem bp0000000110111110 : Branch 0 (-55511639/250000 : ℚ) vp000000011011111 := by
  apply branch_left_normalized (c:=vp0000000110111110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-55511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-55511639/125000 : ℚ) by norm_num]
  exact coverp0000000110111110
private noncomputable def ep0000000110111111_0 : Blocks := edgeBlocks% "full/vectors/0000000110111111-E-0000.bin"
noncomputable def ep0000000110111111 : Blocks := ep0000000110111111_0
private theorem idp0000000110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011011111.list =
    C ((2:ℤ)^53) * horner X vp0000000110111111.list + horner X ep0000000110111111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110111111 : Branch 1 (-55511639/250000 : ℚ) vp000000011011111 := by
  apply branch_checked idp0000000110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-55511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-55636639/125000 : ℚ) by norm_num]
  exact coverp0000000110111111
theorem coverp000000011011111 : Covers (-55511639/250000 : ℚ) vp000000011011111 := join_branches bp0000000110111110 bp0000000110111111
private noncomputable def vp0000000110111101_0 : Blocks := edgeBlocks% "full/vectors/0000000110111101-V-0000.bin"
noncomputable def vp0000000110111101 : Blocks := vp0000000110111101_0
theorem coverp0000000110111101 : Covers (-55386639/125000 : ℚ) vp0000000110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110111100_0 : Blocks := edgeBlocks% "full/vectors/0000000110111100-V-0000.bin"
noncomputable def vp0000000110111100 : Blocks := vp0000000110111100_0
theorem coverp0000000110111100 : Covers (-55261639/125000 : ℚ) vp0000000110111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011011110_0 : Blocks := edgeBlocks% "full/vectors/000000011011110-V-0000.bin"
noncomputable def vp000000011011110 : Blocks := vp000000011011110_0
private theorem bp0000000110111100 : Branch 0 (-55261639/250000 : ℚ) vp000000011011110 := by
  apply branch_left_normalized (c:=vp0000000110111100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-55261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-55261639/125000 : ℚ) by norm_num]
  exact coverp0000000110111100
private noncomputable def ep0000000110111101_0 : Blocks := edgeBlocks% "full/vectors/0000000110111101-E-0000.bin"
noncomputable def ep0000000110111101 : Blocks := ep0000000110111101_0
private theorem idp0000000110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011011110.list =
    C ((2:ℤ)^54) * horner X vp0000000110111101.list + horner X ep0000000110111101.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110111101 : Branch 1 (-55261639/250000 : ℚ) vp000000011011110 := by
  apply branch_checked idp0000000110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-55261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-55386639/125000 : ℚ) by norm_num]
  exact coverp0000000110111101
theorem coverp000000011011110 : Covers (-55261639/250000 : ℚ) vp000000011011110 := join_branches bp0000000110111100 bp0000000110111101
private noncomputable def vp00000001101111_0 : Blocks := edgeBlocks% "full/vectors/00000001101111-V-0000.bin"
noncomputable def vp00000001101111 : Blocks := vp00000001101111_0
private theorem bp000000011011110 : Branch 0 (-55261639/500000 : ℚ) vp00000001101111 := by
  apply branch_left_normalized (c:=vp000000011011110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-55261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-55261639/250000 : ℚ) by norm_num]
  exact coverp000000011011110
private noncomputable def ep000000011011111_0 : Blocks := edgeBlocks% "full/vectors/000000011011111-E-0000.bin"
noncomputable def ep000000011011111 : Blocks := ep000000011011111_0
private theorem idp000000011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001101111.list =
    C ((2:ℤ)^88) * horner X vp000000011011111.list + horner X ep000000011011111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011011111 : Branch 1 (-55261639/500000 : ℚ) vp00000001101111 := by
  apply branch_checked idp000000011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-55261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-55511639/250000 : ℚ) by norm_num]
  exact coverp000000011011111
theorem coverp00000001101111 : Covers (-55261639/500000 : ℚ) vp00000001101111 := join_branches bp000000011011110 bp000000011011111
private noncomputable def vp0000000110111011_0 : Blocks := edgeBlocks% "full/vectors/0000000110111011-V-0000.bin"
noncomputable def vp0000000110111011 : Blocks := vp0000000110111011_0
theorem coverp0000000110111011 : Covers (-55136639/125000 : ℚ) vp0000000110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110111010_0 : Blocks := edgeBlocks% "full/vectors/0000000110111010-V-0000.bin"
noncomputable def vp0000000110111010 : Blocks := vp0000000110111010_0
theorem coverp0000000110111010 : Covers (-55011639/125000 : ℚ) vp0000000110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011011101_0 : Blocks := edgeBlocks% "full/vectors/000000011011101-V-0000.bin"
noncomputable def vp000000011011101 : Blocks := vp000000011011101_0
private theorem bp0000000110111010 : Branch 0 (-55011639/250000 : ℚ) vp000000011011101 := by
  apply branch_left_normalized (c:=vp0000000110111010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-55011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-55011639/125000 : ℚ) by norm_num]
  exact coverp0000000110111010
private noncomputable def ep0000000110111011_0 : Blocks := edgeBlocks% "full/vectors/0000000110111011-E-0000.bin"
noncomputable def ep0000000110111011 : Blocks := ep0000000110111011_0
private theorem idp0000000110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011011101.list =
    C ((2:ℤ)^53) * horner X vp0000000110111011.list + horner X ep0000000110111011.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110111011 : Branch 1 (-55011639/250000 : ℚ) vp000000011011101 := by
  apply branch_checked idp0000000110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-55011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-55136639/125000 : ℚ) by norm_num]
  exact coverp0000000110111011
theorem coverp000000011011101 : Covers (-55011639/250000 : ℚ) vp000000011011101 := join_branches bp0000000110111010 bp0000000110111011
private noncomputable def vp0000000110111001_0 : Blocks := edgeBlocks% "full/vectors/0000000110111001-V-0000.bin"
noncomputable def vp0000000110111001 : Blocks := vp0000000110111001_0
theorem coverp0000000110111001 : Covers (-54886639/125000 : ℚ) vp0000000110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110111000_0 : Blocks := edgeBlocks% "full/vectors/0000000110111000-V-0000.bin"
noncomputable def vp0000000110111000 : Blocks := vp0000000110111000_0
theorem coverp0000000110111000 : Covers (-54761639/125000 : ℚ) vp0000000110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011011100_0 : Blocks := edgeBlocks% "full/vectors/000000011011100-V-0000.bin"
noncomputable def vp000000011011100 : Blocks := vp000000011011100_0
private theorem bp0000000110111000 : Branch 0 (-54761639/250000 : ℚ) vp000000011011100 := by
  apply branch_left_normalized (c:=vp0000000110111000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-54761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-54761639/125000 : ℚ) by norm_num]
  exact coverp0000000110111000
private noncomputable def ep0000000110111001_0 : Blocks := edgeBlocks% "full/vectors/0000000110111001-E-0000.bin"
noncomputable def ep0000000110111001 : Blocks := ep0000000110111001_0
private theorem idp0000000110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011011100.list =
    C ((2:ℤ)^54) * horner X vp0000000110111001.list + horner X ep0000000110111001.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110111001 : Branch 1 (-54761639/250000 : ℚ) vp000000011011100 := by
  apply branch_checked idp0000000110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-54761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-54886639/125000 : ℚ) by norm_num]
  exact coverp0000000110111001
theorem coverp000000011011100 : Covers (-54761639/250000 : ℚ) vp000000011011100 := join_branches bp0000000110111000 bp0000000110111001
private noncomputable def vp00000001101110_0 : Blocks := edgeBlocks% "full/vectors/00000001101110-V-0000.bin"
noncomputable def vp00000001101110 : Blocks := vp00000001101110_0
private theorem bp000000011011100 : Branch 0 (-54761639/500000 : ℚ) vp00000001101110 := by
  apply branch_left_normalized (c:=vp000000011011100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-54761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-54761639/250000 : ℚ) by norm_num]
  exact coverp000000011011100
private noncomputable def ep000000011011101_0 : Blocks := edgeBlocks% "full/vectors/000000011011101-E-0000.bin"
noncomputable def ep000000011011101 : Blocks := ep000000011011101_0
private theorem idp000000011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001101110.list =
    C ((2:ℤ)^89) * horner X vp000000011011101.list + horner X ep000000011011101.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011011101 : Branch 1 (-54761639/500000 : ℚ) vp00000001101110 := by
  apply branch_checked idp000000011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-54761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-55011639/250000 : ℚ) by norm_num]
  exact coverp000000011011101
theorem coverp00000001101110 : Covers (-54761639/500000 : ℚ) vp00000001101110 := join_branches bp000000011011100 bp000000011011101
private noncomputable def vp0000000110111_0 : Blocks := edgeBlocks% "full/vectors/0000000110111-V-0000.bin"
private noncomputable def vp0000000110111_1 : Blocks := edgeBlocks% "full/vectors/0000000110111-V-0001.bin"
noncomputable def vp0000000110111 : Blocks := (Blocks.join vp0000000110111_0 vp0000000110111_1)
private theorem bp00000001101110 : Branch 0 (-54761639/1000000 : ℚ) vp0000000110111 := by
  apply branch_left_normalized (c:=vp00000001101110) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-54761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-54761639/500000 : ℚ) by norm_num]
  exact coverp00000001101110
private noncomputable def ep00000001101111_0 : Blocks := edgeBlocks% "full/vectors/00000001101111-E-0000.bin"
private noncomputable def ep00000001101111_1 : Blocks := edgeBlocks% "full/vectors/00000001101111-E-0001.bin"
noncomputable def ep00000001101111 : Blocks := (Blocks.join ep00000001101111_0 ep00000001101111_1)
private theorem idp00000001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000110111.list =
    C ((2:ℤ)^158) * horner X vp00000001101111.list + horner X ep00000001101111.list := by
  exact edge_identity (B := (2:ℤ)^326) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001101111 : Branch 1 (-54761639/1000000 : ℚ) vp0000000110111 := by
  apply branch_checked idp00000001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-54761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-55261639/500000 : ℚ) by norm_num]
  exact coverp00000001101111
theorem coverp0000000110111 : Covers (-54761639/1000000 : ℚ) vp0000000110111 := join_branches bp00000001101110 bp00000001101111
private noncomputable def vp0000000110110111_0 : Blocks := edgeBlocks% "full/vectors/0000000110110111-V-0000.bin"
noncomputable def vp0000000110110111 : Blocks := vp0000000110110111_0
theorem coverp0000000110110111 : Covers (-54636639/125000 : ℚ) vp0000000110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110110110_0 : Blocks := edgeBlocks% "full/vectors/0000000110110110-V-0000.bin"
noncomputable def vp0000000110110110 : Blocks := vp0000000110110110_0
theorem coverp0000000110110110 : Covers (-54511639/125000 : ℚ) vp0000000110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011011011_0 : Blocks := edgeBlocks% "full/vectors/000000011011011-V-0000.bin"
noncomputable def vp000000011011011 : Blocks := vp000000011011011_0
private theorem bp0000000110110110 : Branch 0 (-54511639/250000 : ℚ) vp000000011011011 := by
  apply branch_left_normalized (c:=vp0000000110110110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-54511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-54511639/125000 : ℚ) by norm_num]
  exact coverp0000000110110110
private noncomputable def ep0000000110110111_0 : Blocks := edgeBlocks% "full/vectors/0000000110110111-E-0000.bin"
noncomputable def ep0000000110110111 : Blocks := ep0000000110110111_0
private theorem idp0000000110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011011011.list =
    C ((2:ℤ)^54) * horner X vp0000000110110111.list + horner X ep0000000110110111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110110111 : Branch 1 (-54511639/250000 : ℚ) vp000000011011011 := by
  apply branch_checked idp0000000110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-54511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-54636639/125000 : ℚ) by norm_num]
  exact coverp0000000110110111
theorem coverp000000011011011 : Covers (-54511639/250000 : ℚ) vp000000011011011 := join_branches bp0000000110110110 bp0000000110110111
private noncomputable def vp0000000110110101_0 : Blocks := edgeBlocks% "full/vectors/0000000110110101-V-0000.bin"
noncomputable def vp0000000110110101 : Blocks := vp0000000110110101_0
theorem coverp0000000110110101 : Covers (-54386639/125000 : ℚ) vp0000000110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110110100_0 : Blocks := edgeBlocks% "full/vectors/0000000110110100-V-0000.bin"
noncomputable def vp0000000110110100 : Blocks := vp0000000110110100_0
theorem coverp0000000110110100 : Covers (-54261639/125000 : ℚ) vp0000000110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011011010_0 : Blocks := edgeBlocks% "full/vectors/000000011011010-V-0000.bin"
noncomputable def vp000000011011010 : Blocks := vp000000011011010_0
private theorem bp0000000110110100 : Branch 0 (-54261639/250000 : ℚ) vp000000011011010 := by
  apply branch_left_normalized (c:=vp0000000110110100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-54261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-54261639/125000 : ℚ) by norm_num]
  exact coverp0000000110110100
private noncomputable def ep0000000110110101_0 : Blocks := edgeBlocks% "full/vectors/0000000110110101-E-0000.bin"
noncomputable def ep0000000110110101 : Blocks := ep0000000110110101_0
private theorem idp0000000110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011011010.list =
    C ((2:ℤ)^55) * horner X vp0000000110110101.list + horner X ep0000000110110101.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110110101 : Branch 1 (-54261639/250000 : ℚ) vp000000011011010 := by
  apply branch_checked idp0000000110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-54261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-54386639/125000 : ℚ) by norm_num]
  exact coverp0000000110110101
theorem coverp000000011011010 : Covers (-54261639/250000 : ℚ) vp000000011011010 := join_branches bp0000000110110100 bp0000000110110101
private noncomputable def vp00000001101101_0 : Blocks := edgeBlocks% "full/vectors/00000001101101-V-0000.bin"
noncomputable def vp00000001101101 : Blocks := vp00000001101101_0
private theorem bp000000011011010 : Branch 0 (-54261639/500000 : ℚ) vp00000001101101 := by
  apply branch_left_normalized (c:=vp000000011011010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-54261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-54261639/250000 : ℚ) by norm_num]
  exact coverp000000011011010
private noncomputable def ep000000011011011_0 : Blocks := edgeBlocks% "full/vectors/000000011011011-E-0000.bin"
noncomputable def ep000000011011011 : Blocks := ep000000011011011_0
private theorem idp000000011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001101101.list =
    C ((2:ℤ)^91) * horner X vp000000011011011.list + horner X ep000000011011011.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011011011 : Branch 1 (-54261639/500000 : ℚ) vp00000001101101 := by
  apply branch_checked idp000000011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-54261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-54511639/250000 : ℚ) by norm_num]
  exact coverp000000011011011
theorem coverp00000001101101 : Covers (-54261639/500000 : ℚ) vp00000001101101 := join_branches bp000000011011010 bp000000011011011
private noncomputable def vp0000000110110011_0 : Blocks := edgeBlocks% "full/vectors/0000000110110011-V-0000.bin"
noncomputable def vp0000000110110011 : Blocks := vp0000000110110011_0
theorem coverp0000000110110011 : Covers (-54136639/125000 : ℚ) vp0000000110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110110010_0 : Blocks := edgeBlocks% "full/vectors/0000000110110010-V-0000.bin"
noncomputable def vp0000000110110010 : Blocks := vp0000000110110010_0
theorem coverp0000000110110010 : Covers (-54011639/125000 : ℚ) vp0000000110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011011001_0 : Blocks := edgeBlocks% "full/vectors/000000011011001-V-0000.bin"
noncomputable def vp000000011011001 : Blocks := vp000000011011001_0
private theorem bp0000000110110010 : Branch 0 (-54011639/250000 : ℚ) vp000000011011001 := by
  apply branch_left_normalized (c:=vp0000000110110010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-54011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-54011639/125000 : ℚ) by norm_num]
  exact coverp0000000110110010
private noncomputable def ep0000000110110011_0 : Blocks := edgeBlocks% "full/vectors/0000000110110011-E-0000.bin"
noncomputable def ep0000000110110011 : Blocks := ep0000000110110011_0
private theorem idp0000000110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011011001.list =
    C ((2:ℤ)^56) * horner X vp0000000110110011.list + horner X ep0000000110110011.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110110011 : Branch 1 (-54011639/250000 : ℚ) vp000000011011001 := by
  apply branch_checked idp0000000110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-54011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-54136639/125000 : ℚ) by norm_num]
  exact coverp0000000110110011
theorem coverp000000011011001 : Covers (-54011639/250000 : ℚ) vp000000011011001 := join_branches bp0000000110110010 bp0000000110110011
private noncomputable def vp0000000110110001_0 : Blocks := edgeBlocks% "full/vectors/0000000110110001-V-0000.bin"
noncomputable def vp0000000110110001 : Blocks := vp0000000110110001_0
theorem coverp0000000110110001 : Covers (-53886639/125000 : ℚ) vp0000000110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110110000_0 : Blocks := edgeBlocks% "full/vectors/0000000110110000-V-0000.bin"
noncomputable def vp0000000110110000 : Blocks := vp0000000110110000_0
theorem coverp0000000110110000 : Covers (-53761639/125000 : ℚ) vp0000000110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011011000_0 : Blocks := edgeBlocks% "full/vectors/000000011011000-V-0000.bin"
noncomputable def vp000000011011000 : Blocks := vp000000011011000_0
private theorem bp0000000110110000 : Branch 0 (-53761639/250000 : ℚ) vp000000011011000 := by
  apply branch_left_normalized (c:=vp0000000110110000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-53761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-53761639/125000 : ℚ) by norm_num]
  exact coverp0000000110110000
private noncomputable def ep0000000110110001_0 : Blocks := edgeBlocks% "full/vectors/0000000110110001-E-0000.bin"
noncomputable def ep0000000110110001 : Blocks := ep0000000110110001_0
private theorem idp0000000110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011011000.list =
    C ((2:ℤ)^55) * horner X vp0000000110110001.list + horner X ep0000000110110001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110110001 : Branch 1 (-53761639/250000 : ℚ) vp000000011011000 := by
  apply branch_checked idp0000000110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-53761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-53886639/125000 : ℚ) by norm_num]
  exact coverp0000000110110001
theorem coverp000000011011000 : Covers (-53761639/250000 : ℚ) vp000000011011000 := join_branches bp0000000110110000 bp0000000110110001
private noncomputable def vp00000001101100_0 : Blocks := edgeBlocks% "full/vectors/00000001101100-V-0000.bin"
noncomputable def vp00000001101100 : Blocks := vp00000001101100_0
private theorem bp000000011011000 : Branch 0 (-53761639/500000 : ℚ) vp00000001101100 := by
  apply branch_left_normalized (c:=vp000000011011000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-53761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-53761639/250000 : ℚ) by norm_num]
  exact coverp000000011011000
private noncomputable def ep000000011011001_0 : Blocks := edgeBlocks% "full/vectors/000000011011001-E-0000.bin"
noncomputable def ep000000011011001 : Blocks := ep000000011011001_0
private theorem idp000000011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001101100.list =
    C ((2:ℤ)^91) * horner X vp000000011011001.list + horner X ep000000011011001.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011011001 : Branch 1 (-53761639/500000 : ℚ) vp00000001101100 := by
  apply branch_checked idp000000011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-53761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-54011639/250000 : ℚ) by norm_num]
  exact coverp000000011011001
theorem coverp00000001101100 : Covers (-53761639/500000 : ℚ) vp00000001101100 := join_branches bp000000011011000 bp000000011011001
private noncomputable def vp0000000110110_0 : Blocks := edgeBlocks% "full/vectors/0000000110110-V-0000.bin"
private noncomputable def vp0000000110110_1 : Blocks := edgeBlocks% "full/vectors/0000000110110-V-0001.bin"
noncomputable def vp0000000110110 : Blocks := (Blocks.join vp0000000110110_0 vp0000000110110_1)
private theorem bp00000001101100 : Branch 0 (-53761639/1000000 : ℚ) vp0000000110110 := by
  apply branch_left_normalized (c:=vp00000001101100) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-53761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-53761639/500000 : ℚ) by norm_num]
  exact coverp00000001101100
private noncomputable def ep00000001101101_0 : Blocks := edgeBlocks% "full/vectors/00000001101101-E-0000.bin"
private noncomputable def ep00000001101101_1 : Blocks := edgeBlocks% "full/vectors/00000001101101-E-0001.bin"
noncomputable def ep00000001101101 : Blocks := (Blocks.join ep00000001101101_0 ep00000001101101_1)
private theorem idp00000001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000110110.list =
    C ((2:ℤ)^161) * horner X vp00000001101101.list + horner X ep00000001101101.list := by
  exact edge_identity (B := (2:ℤ)^331) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001101101 : Branch 1 (-53761639/1000000 : ℚ) vp0000000110110 := by
  apply branch_checked idp00000001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-53761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-54261639/500000 : ℚ) by norm_num]
  exact coverp00000001101101
theorem coverp0000000110110 : Covers (-53761639/1000000 : ℚ) vp0000000110110 := join_branches bp00000001101100 bp00000001101101
private noncomputable def vp000000011011_0 : Blocks := edgeBlocks% "full/vectors/000000011011-V-0000.bin"
private noncomputable def vp000000011011_1 : Blocks := edgeBlocks% "full/vectors/000000011011-V-0001.bin"
private noncomputable def vp000000011011_2 : Blocks := edgeBlocks% "full/vectors/000000011011-V-0002.bin"
noncomputable def vp000000011011 : Blocks := (Blocks.join vp000000011011_0 (Blocks.join vp000000011011_1 vp000000011011_2))
private theorem bp0000000110110 : Branch 0 (-53761639/2000000 : ℚ) vp000000011011 := by
  apply branch_left_normalized (c:=vp0000000110110) (k:=0) (m:=156) (by decide +kernel)
  rw [show 2*(-53761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-53761639/1000000 : ℚ) by norm_num]
  exact coverp0000000110110
private noncomputable def ep0000000110111_0 : Blocks := edgeBlocks% "full/vectors/0000000110111-E-0000.bin"
private noncomputable def ep0000000110111_1 : Blocks := edgeBlocks% "full/vectors/0000000110111-E-0001.bin"
private noncomputable def ep0000000110111_2 : Blocks := edgeBlocks% "full/vectors/0000000110111-E-0002.bin"
noncomputable def ep0000000110111 : Blocks := (Blocks.join ep0000000110111_0 (Blocks.join ep0000000110111_1 ep0000000110111_2))
private theorem idp0000000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011011.list =
    C ((2:ℤ)^300) * horner X vp0000000110111.list + horner X ep0000000110111.list := by
  exact edge_identity (B := (2:ℤ)^537) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110111 : Branch 1 (-53761639/2000000 : ℚ) vp000000011011 := by
  apply branch_checked idp0000000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-53761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-54761639/1000000 : ℚ) by norm_num]
  exact coverp0000000110111
theorem coverp000000011011 : Covers (-53761639/2000000 : ℚ) vp000000011011 := join_branches bp0000000110110 bp0000000110111
private noncomputable def vp0000000110101111_0 : Blocks := edgeBlocks% "full/vectors/0000000110101111-V-0000.bin"
noncomputable def vp0000000110101111 : Blocks := vp0000000110101111_0
theorem coverp0000000110101111 : Covers (-53636639/125000 : ℚ) vp0000000110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110101110_0 : Blocks := edgeBlocks% "full/vectors/0000000110101110-V-0000.bin"
noncomputable def vp0000000110101110 : Blocks := vp0000000110101110_0
theorem coverp0000000110101110 : Covers (-53511639/125000 : ℚ) vp0000000110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011010111_0 : Blocks := edgeBlocks% "full/vectors/000000011010111-V-0000.bin"
noncomputable def vp000000011010111 : Blocks := vp000000011010111_0
private theorem bp0000000110101110 : Branch 0 (-53511639/250000 : ℚ) vp000000011010111 := by
  apply branch_left_normalized (c:=vp0000000110101110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-53511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-53511639/125000 : ℚ) by norm_num]
  exact coverp0000000110101110
private noncomputable def ep0000000110101111_0 : Blocks := edgeBlocks% "full/vectors/0000000110101111-E-0000.bin"
noncomputable def ep0000000110101111 : Blocks := ep0000000110101111_0
private theorem idp0000000110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011010111.list =
    C ((2:ℤ)^54) * horner X vp0000000110101111.list + horner X ep0000000110101111.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110101111 : Branch 1 (-53511639/250000 : ℚ) vp000000011010111 := by
  apply branch_checked idp0000000110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-53511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-53636639/125000 : ℚ) by norm_num]
  exact coverp0000000110101111
theorem coverp000000011010111 : Covers (-53511639/250000 : ℚ) vp000000011010111 := join_branches bp0000000110101110 bp0000000110101111
private noncomputable def vp0000000110101101_0 : Blocks := edgeBlocks% "full/vectors/0000000110101101-V-0000.bin"
noncomputable def vp0000000110101101 : Blocks := vp0000000110101101_0
theorem coverp0000000110101101 : Covers (-53386639/125000 : ℚ) vp0000000110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110101100_0 : Blocks := edgeBlocks% "full/vectors/0000000110101100-V-0000.bin"
noncomputable def vp0000000110101100 : Blocks := vp0000000110101100_0
theorem coverp0000000110101100 : Covers (-53261639/125000 : ℚ) vp0000000110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011010110_0 : Blocks := edgeBlocks% "full/vectors/000000011010110-V-0000.bin"
noncomputable def vp000000011010110 : Blocks := vp000000011010110_0
private theorem bp0000000110101100 : Branch 0 (-53261639/250000 : ℚ) vp000000011010110 := by
  apply branch_left_normalized (c:=vp0000000110101100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-53261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-53261639/125000 : ℚ) by norm_num]
  exact coverp0000000110101100
private noncomputable def ep0000000110101101_0 : Blocks := edgeBlocks% "full/vectors/0000000110101101-E-0000.bin"
noncomputable def ep0000000110101101 : Blocks := ep0000000110101101_0
private theorem idp0000000110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011010110.list =
    C ((2:ℤ)^55) * horner X vp0000000110101101.list + horner X ep0000000110101101.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110101101 : Branch 1 (-53261639/250000 : ℚ) vp000000011010110 := by
  apply branch_checked idp0000000110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-53261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-53386639/125000 : ℚ) by norm_num]
  exact coverp0000000110101101
theorem coverp000000011010110 : Covers (-53261639/250000 : ℚ) vp000000011010110 := join_branches bp0000000110101100 bp0000000110101101
private noncomputable def vp00000001101011_0 : Blocks := edgeBlocks% "full/vectors/00000001101011-V-0000.bin"
noncomputable def vp00000001101011 : Blocks := vp00000001101011_0
private theorem bp000000011010110 : Branch 0 (-53261639/500000 : ℚ) vp00000001101011 := by
  apply branch_left_normalized (c:=vp000000011010110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-53261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-53261639/250000 : ℚ) by norm_num]
  exact coverp000000011010110
private noncomputable def ep000000011010111_0 : Blocks := edgeBlocks% "full/vectors/000000011010111-E-0000.bin"
noncomputable def ep000000011010111 : Blocks := ep000000011010111_0
private theorem idp000000011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001101011.list =
    C ((2:ℤ)^90) * horner X vp000000011010111.list + horner X ep000000011010111.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011010111 : Branch 1 (-53261639/500000 : ℚ) vp00000001101011 := by
  apply branch_checked idp000000011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-53261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-53511639/250000 : ℚ) by norm_num]
  exact coverp000000011010111
theorem coverp00000001101011 : Covers (-53261639/500000 : ℚ) vp00000001101011 := join_branches bp000000011010110 bp000000011010111
private noncomputable def vp0000000110101011_0 : Blocks := edgeBlocks% "full/vectors/0000000110101011-V-0000.bin"
noncomputable def vp0000000110101011 : Blocks := vp0000000110101011_0
theorem coverp0000000110101011 : Covers (-53136639/125000 : ℚ) vp0000000110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110101010_0 : Blocks := edgeBlocks% "full/vectors/0000000110101010-V-0000.bin"
noncomputable def vp0000000110101010 : Blocks := vp0000000110101010_0
theorem coverp0000000110101010 : Covers (-53011639/125000 : ℚ) vp0000000110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011010101_0 : Blocks := edgeBlocks% "full/vectors/000000011010101-V-0000.bin"
noncomputable def vp000000011010101 : Blocks := vp000000011010101_0
private theorem bp0000000110101010 : Branch 0 (-53011639/250000 : ℚ) vp000000011010101 := by
  apply branch_left_normalized (c:=vp0000000110101010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-53011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-53011639/125000 : ℚ) by norm_num]
  exact coverp0000000110101010
private noncomputable def ep0000000110101011_0 : Blocks := edgeBlocks% "full/vectors/0000000110101011-E-0000.bin"
noncomputable def ep0000000110101011 : Blocks := ep0000000110101011_0
private theorem idp0000000110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011010101.list =
    C ((2:ℤ)^55) * horner X vp0000000110101011.list + horner X ep0000000110101011.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110101011 : Branch 1 (-53011639/250000 : ℚ) vp000000011010101 := by
  apply branch_checked idp0000000110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-53011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-53136639/125000 : ℚ) by norm_num]
  exact coverp0000000110101011
theorem coverp000000011010101 : Covers (-53011639/250000 : ℚ) vp000000011010101 := join_branches bp0000000110101010 bp0000000110101011
private noncomputable def vp0000000110101001_0 : Blocks := edgeBlocks% "full/vectors/0000000110101001-V-0000.bin"
noncomputable def vp0000000110101001 : Blocks := vp0000000110101001_0
theorem coverp0000000110101001 : Covers (-52886639/125000 : ℚ) vp0000000110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110101000_0 : Blocks := edgeBlocks% "full/vectors/0000000110101000-V-0000.bin"
noncomputable def vp0000000110101000 : Blocks := vp0000000110101000_0
theorem coverp0000000110101000 : Covers (-52761639/125000 : ℚ) vp0000000110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011010100_0 : Blocks := edgeBlocks% "full/vectors/000000011010100-V-0000.bin"
noncomputable def vp000000011010100 : Blocks := vp000000011010100_0
private theorem bp0000000110101000 : Branch 0 (-52761639/250000 : ℚ) vp000000011010100 := by
  apply branch_left_normalized (c:=vp0000000110101000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-52761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-52761639/125000 : ℚ) by norm_num]
  exact coverp0000000110101000
private noncomputable def ep0000000110101001_0 : Blocks := edgeBlocks% "full/vectors/0000000110101001-E-0000.bin"
noncomputable def ep0000000110101001 : Blocks := ep0000000110101001_0
private theorem idp0000000110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011010100.list =
    C ((2:ℤ)^55) * horner X vp0000000110101001.list + horner X ep0000000110101001.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110101001 : Branch 1 (-52761639/250000 : ℚ) vp000000011010100 := by
  apply branch_checked idp0000000110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-52761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-52886639/125000 : ℚ) by norm_num]
  exact coverp0000000110101001
theorem coverp000000011010100 : Covers (-52761639/250000 : ℚ) vp000000011010100 := join_branches bp0000000110101000 bp0000000110101001
private noncomputable def vp00000001101010_0 : Blocks := edgeBlocks% "full/vectors/00000001101010-V-0000.bin"
noncomputable def vp00000001101010 : Blocks := vp00000001101010_0
private theorem bp000000011010100 : Branch 0 (-52761639/500000 : ℚ) vp00000001101010 := by
  apply branch_left_normalized (c:=vp000000011010100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-52761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-52761639/250000 : ℚ) by norm_num]
  exact coverp000000011010100
private noncomputable def ep000000011010101_0 : Blocks := edgeBlocks% "full/vectors/000000011010101-E-0000.bin"
noncomputable def ep000000011010101 : Blocks := ep000000011010101_0
private theorem idp000000011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001101010.list =
    C ((2:ℤ)^92) * horner X vp000000011010101.list + horner X ep000000011010101.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011010101 : Branch 1 (-52761639/500000 : ℚ) vp00000001101010 := by
  apply branch_checked idp000000011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-52761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-53011639/250000 : ℚ) by norm_num]
  exact coverp000000011010101
theorem coverp00000001101010 : Covers (-52761639/500000 : ℚ) vp00000001101010 := join_branches bp000000011010100 bp000000011010101
private noncomputable def vp0000000110101_0 : Blocks := edgeBlocks% "full/vectors/0000000110101-V-0000.bin"
private noncomputable def vp0000000110101_1 : Blocks := edgeBlocks% "full/vectors/0000000110101-V-0001.bin"
noncomputable def vp0000000110101 : Blocks := (Blocks.join vp0000000110101_0 vp0000000110101_1)
private theorem bp00000001101010 : Branch 0 (-52761639/1000000 : ℚ) vp0000000110101 := by
  apply branch_left_normalized (c:=vp00000001101010) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-52761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-52761639/500000 : ℚ) by norm_num]
  exact coverp00000001101010
private noncomputable def ep00000001101011_0 : Blocks := edgeBlocks% "full/vectors/00000001101011-E-0000.bin"
private noncomputable def ep00000001101011_1 : Blocks := edgeBlocks% "full/vectors/00000001101011-E-0001.bin"
noncomputable def ep00000001101011 : Blocks := (Blocks.join ep00000001101011_0 ep00000001101011_1)
private theorem idp00000001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000110101.list =
    C ((2:ℤ)^161) * horner X vp00000001101011.list + horner X ep00000001101011.list := by
  exact edge_identity (B := (2:ℤ)^332) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001101011 : Branch 1 (-52761639/1000000 : ℚ) vp0000000110101 := by
  apply branch_checked idp00000001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-52761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-53261639/500000 : ℚ) by norm_num]
  exact coverp00000001101011
theorem coverp0000000110101 : Covers (-52761639/1000000 : ℚ) vp0000000110101 := join_branches bp00000001101010 bp00000001101011
private noncomputable def vp0000000110100111_0 : Blocks := edgeBlocks% "full/vectors/0000000110100111-V-0000.bin"
noncomputable def vp0000000110100111 : Blocks := vp0000000110100111_0
theorem coverp0000000110100111 : Covers (-52636639/125000 : ℚ) vp0000000110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110100110_0 : Blocks := edgeBlocks% "full/vectors/0000000110100110-V-0000.bin"
noncomputable def vp0000000110100110 : Blocks := vp0000000110100110_0
theorem coverp0000000110100110 : Covers (-52511639/125000 : ℚ) vp0000000110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011010011_0 : Blocks := edgeBlocks% "full/vectors/000000011010011-V-0000.bin"
noncomputable def vp000000011010011 : Blocks := vp000000011010011_0
private theorem bp0000000110100110 : Branch 0 (-52511639/250000 : ℚ) vp000000011010011 := by
  apply branch_left_normalized (c:=vp0000000110100110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-52511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-52511639/125000 : ℚ) by norm_num]
  exact coverp0000000110100110
private noncomputable def ep0000000110100111_0 : Blocks := edgeBlocks% "full/vectors/0000000110100111-E-0000.bin"
noncomputable def ep0000000110100111 : Blocks := ep0000000110100111_0
private theorem idp0000000110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011010011.list =
    C ((2:ℤ)^55) * horner X vp0000000110100111.list + horner X ep0000000110100111.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110100111 : Branch 1 (-52511639/250000 : ℚ) vp000000011010011 := by
  apply branch_checked idp0000000110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-52511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-52636639/125000 : ℚ) by norm_num]
  exact coverp0000000110100111
theorem coverp000000011010011 : Covers (-52511639/250000 : ℚ) vp000000011010011 := join_branches bp0000000110100110 bp0000000110100111
private noncomputable def vp0000000110100101_0 : Blocks := edgeBlocks% "full/vectors/0000000110100101-V-0000.bin"
noncomputable def vp0000000110100101 : Blocks := vp0000000110100101_0
theorem coverp0000000110100101 : Covers (-52386639/125000 : ℚ) vp0000000110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110100100_0 : Blocks := edgeBlocks% "full/vectors/0000000110100100-V-0000.bin"
noncomputable def vp0000000110100100 : Blocks := vp0000000110100100_0
theorem coverp0000000110100100 : Covers (-52261639/125000 : ℚ) vp0000000110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011010010_0 : Blocks := edgeBlocks% "full/vectors/000000011010010-V-0000.bin"
noncomputable def vp000000011010010 : Blocks := vp000000011010010_0
private theorem bp0000000110100100 : Branch 0 (-52261639/250000 : ℚ) vp000000011010010 := by
  apply branch_left_normalized (c:=vp0000000110100100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-52261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-52261639/125000 : ℚ) by norm_num]
  exact coverp0000000110100100
private noncomputable def ep0000000110100101_0 : Blocks := edgeBlocks% "full/vectors/0000000110100101-E-0000.bin"
noncomputable def ep0000000110100101 : Blocks := ep0000000110100101_0
private theorem idp0000000110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011010010.list =
    C ((2:ℤ)^55) * horner X vp0000000110100101.list + horner X ep0000000110100101.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110100101 : Branch 1 (-52261639/250000 : ℚ) vp000000011010010 := by
  apply branch_checked idp0000000110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-52261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-52386639/125000 : ℚ) by norm_num]
  exact coverp0000000110100101
theorem coverp000000011010010 : Covers (-52261639/250000 : ℚ) vp000000011010010 := join_branches bp0000000110100100 bp0000000110100101
private noncomputable def vp00000001101001_0 : Blocks := edgeBlocks% "full/vectors/00000001101001-V-0000.bin"
noncomputable def vp00000001101001 : Blocks := vp00000001101001_0
private theorem bp000000011010010 : Branch 0 (-52261639/500000 : ℚ) vp00000001101001 := by
  apply branch_left_normalized (c:=vp000000011010010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-52261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-52261639/250000 : ℚ) by norm_num]
  exact coverp000000011010010
private noncomputable def ep000000011010011_0 : Blocks := edgeBlocks% "full/vectors/000000011010011-E-0000.bin"
noncomputable def ep000000011010011 : Blocks := ep000000011010011_0
private theorem idp000000011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001101001.list =
    C ((2:ℤ)^94) * horner X vp000000011010011.list + horner X ep000000011010011.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011010011 : Branch 1 (-52261639/500000 : ℚ) vp00000001101001 := by
  apply branch_checked idp000000011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-52261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-52511639/250000 : ℚ) by norm_num]
  exact coverp000000011010011
theorem coverp00000001101001 : Covers (-52261639/500000 : ℚ) vp00000001101001 := join_branches bp000000011010010 bp000000011010011
private noncomputable def vp0000000110100011_0 : Blocks := edgeBlocks% "full/vectors/0000000110100011-V-0000.bin"
noncomputable def vp0000000110100011 : Blocks := vp0000000110100011_0
theorem coverp0000000110100011 : Covers (-52136639/125000 : ℚ) vp0000000110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110100010_0 : Blocks := edgeBlocks% "full/vectors/0000000110100010-V-0000.bin"
noncomputable def vp0000000110100010 : Blocks := vp0000000110100010_0
theorem coverp0000000110100010 : Covers (-52011639/125000 : ℚ) vp0000000110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011010001_0 : Blocks := edgeBlocks% "full/vectors/000000011010001-V-0000.bin"
noncomputable def vp000000011010001 : Blocks := vp000000011010001_0
private theorem bp0000000110100010 : Branch 0 (-52011639/250000 : ℚ) vp000000011010001 := by
  apply branch_left_normalized (c:=vp0000000110100010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-52011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-52011639/125000 : ℚ) by norm_num]
  exact coverp0000000110100010
private noncomputable def ep0000000110100011_0 : Blocks := edgeBlocks% "full/vectors/0000000110100011-E-0000.bin"
noncomputable def ep0000000110100011 : Blocks := ep0000000110100011_0
private theorem idp0000000110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011010001.list =
    C ((2:ℤ)^56) * horner X vp0000000110100011.list + horner X ep0000000110100011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110100011 : Branch 1 (-52011639/250000 : ℚ) vp000000011010001 := by
  apply branch_checked idp0000000110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-52011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-52136639/125000 : ℚ) by norm_num]
  exact coverp0000000110100011
theorem coverp000000011010001 : Covers (-52011639/250000 : ℚ) vp000000011010001 := join_branches bp0000000110100010 bp0000000110100011
private noncomputable def vp0000000110100001_0 : Blocks := edgeBlocks% "full/vectors/0000000110100001-V-0000.bin"
noncomputable def vp0000000110100001 : Blocks := vp0000000110100001_0
theorem coverp0000000110100001 : Covers (-51886639/125000 : ℚ) vp0000000110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110100000_0 : Blocks := edgeBlocks% "full/vectors/0000000110100000-V-0000.bin"
noncomputable def vp0000000110100000 : Blocks := vp0000000110100000_0
theorem coverp0000000110100000 : Covers (-51761639/125000 : ℚ) vp0000000110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011010000_0 : Blocks := edgeBlocks% "full/vectors/000000011010000-V-0000.bin"
noncomputable def vp000000011010000 : Blocks := vp000000011010000_0
private theorem bp0000000110100000 : Branch 0 (-51761639/250000 : ℚ) vp000000011010000 := by
  apply branch_left_normalized (c:=vp0000000110100000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-51761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-51761639/125000 : ℚ) by norm_num]
  exact coverp0000000110100000
private noncomputable def ep0000000110100001_0 : Blocks := edgeBlocks% "full/vectors/0000000110100001-E-0000.bin"
noncomputable def ep0000000110100001 : Blocks := ep0000000110100001_0
private theorem idp0000000110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011010000.list =
    C ((2:ℤ)^56) * horner X vp0000000110100001.list + horner X ep0000000110100001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110100001 : Branch 1 (-51761639/250000 : ℚ) vp000000011010000 := by
  apply branch_checked idp0000000110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-51761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-51886639/125000 : ℚ) by norm_num]
  exact coverp0000000110100001
theorem coverp000000011010000 : Covers (-51761639/250000 : ℚ) vp000000011010000 := join_branches bp0000000110100000 bp0000000110100001
private noncomputable def vp00000001101000_0 : Blocks := edgeBlocks% "full/vectors/00000001101000-V-0000.bin"
noncomputable def vp00000001101000 : Blocks := vp00000001101000_0
private theorem bp000000011010000 : Branch 0 (-51761639/500000 : ℚ) vp00000001101000 := by
  apply branch_left_normalized (c:=vp000000011010000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-51761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-51761639/250000 : ℚ) by norm_num]
  exact coverp000000011010000
private noncomputable def ep000000011010001_0 : Blocks := edgeBlocks% "full/vectors/000000011010001-E-0000.bin"
noncomputable def ep000000011010001 : Blocks := ep000000011010001_0
private theorem idp000000011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001101000.list =
    C ((2:ℤ)^92) * horner X vp000000011010001.list + horner X ep000000011010001.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011010001 : Branch 1 (-51761639/500000 : ℚ) vp00000001101000 := by
  apply branch_checked idp000000011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-51761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-52011639/250000 : ℚ) by norm_num]
  exact coverp000000011010001
theorem coverp00000001101000 : Covers (-51761639/500000 : ℚ) vp00000001101000 := join_branches bp000000011010000 bp000000011010001
private noncomputable def vp0000000110100_0 : Blocks := edgeBlocks% "full/vectors/0000000110100-V-0000.bin"
private noncomputable def vp0000000110100_1 : Blocks := edgeBlocks% "full/vectors/0000000110100-V-0001.bin"
noncomputable def vp0000000110100 : Blocks := (Blocks.join vp0000000110100_0 vp0000000110100_1)
private theorem bp00000001101000 : Branch 0 (-51761639/1000000 : ℚ) vp0000000110100 := by
  apply branch_left_normalized (c:=vp00000001101000) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-51761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-51761639/500000 : ℚ) by norm_num]
  exact coverp00000001101000
private noncomputable def ep00000001101001_0 : Blocks := edgeBlocks% "full/vectors/00000001101001-E-0000.bin"
private noncomputable def ep00000001101001_1 : Blocks := edgeBlocks% "full/vectors/00000001101001-E-0001.bin"
noncomputable def ep00000001101001 : Blocks := (Blocks.join ep00000001101001_0 ep00000001101001_1)
private theorem idp00000001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000110100.list =
    C ((2:ℤ)^163) * horner X vp00000001101001.list + horner X ep00000001101001.list := by
  exact edge_identity (B := (2:ℤ)^336) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001101001 : Branch 1 (-51761639/1000000 : ℚ) vp0000000110100 := by
  apply branch_checked idp00000001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-51761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-52261639/500000 : ℚ) by norm_num]
  exact coverp00000001101001
theorem coverp0000000110100 : Covers (-51761639/1000000 : ℚ) vp0000000110100 := join_branches bp00000001101000 bp00000001101001
private noncomputable def vp000000011010_0 : Blocks := edgeBlocks% "full/vectors/000000011010-V-0000.bin"
private noncomputable def vp000000011010_1 : Blocks := edgeBlocks% "full/vectors/000000011010-V-0001.bin"
private noncomputable def vp000000011010_2 : Blocks := edgeBlocks% "full/vectors/000000011010-V-0002.bin"
noncomputable def vp000000011010 : Blocks := (Blocks.join vp000000011010_0 (Blocks.join vp000000011010_1 vp000000011010_2))
private theorem bp0000000110100 : Branch 0 (-51761639/2000000 : ℚ) vp000000011010 := by
  apply branch_left_normalized (c:=vp0000000110100) (k:=0) (m:=159) (by decide +kernel)
  rw [show 2*(-51761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-51761639/1000000 : ℚ) by norm_num]
  exact coverp0000000110100
private noncomputable def ep0000000110101_0 : Blocks := edgeBlocks% "full/vectors/0000000110101-E-0000.bin"
private noncomputable def ep0000000110101_1 : Blocks := edgeBlocks% "full/vectors/0000000110101-E-0001.bin"
private noncomputable def ep0000000110101_2 : Blocks := edgeBlocks% "full/vectors/0000000110101-E-0002.bin"
noncomputable def ep0000000110101 : Blocks := (Blocks.join ep0000000110101_0 (Blocks.join ep0000000110101_1 ep0000000110101_2))
private theorem idp0000000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011010.list =
    C ((2:ℤ)^304) * horner X vp0000000110101.list + horner X ep0000000110101.list := by
  exact edge_identity (B := (2:ℤ)^545) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110101 : Branch 1 (-51761639/2000000 : ℚ) vp000000011010 := by
  apply branch_checked idp0000000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-51761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-52761639/1000000 : ℚ) by norm_num]
  exact coverp0000000110101
theorem coverp000000011010 : Covers (-51761639/2000000 : ℚ) vp000000011010 := join_branches bp0000000110100 bp0000000110101
private noncomputable def vp00000001101_0 : Blocks := edgeBlocks% "full/vectors/00000001101-V-0000.bin"
private noncomputable def vp00000001101_1 : Blocks := edgeBlocks% "full/vectors/00000001101-V-0001.bin"
private noncomputable def vp00000001101_2 : Blocks := edgeBlocks% "full/vectors/00000001101-V-0002.bin"
private noncomputable def vp00000001101_3 : Blocks := edgeBlocks% "full/vectors/00000001101-V-0003.bin"
private noncomputable def vp00000001101_4 : Blocks := edgeBlocks% "full/vectors/00000001101-V-0004.bin"
noncomputable def vp00000001101 : Blocks := (Blocks.join (Blocks.join vp00000001101_0 vp00000001101_1) (Blocks.join vp00000001101_2 (Blocks.join vp00000001101_3 vp00000001101_4)))
private theorem bp000000011010 : Branch 0 (-51761639/4000000 : ℚ) vp00000001101 := by
  apply branch_left_normalized (c:=vp000000011010) (k:=0) (m:=296) (by decide +kernel)
  rw [show 2*(-51761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-51761639/2000000 : ℚ) by norm_num]
  exact coverp000000011010
private noncomputable def ep000000011011_0 : Blocks := edgeBlocks% "full/vectors/000000011011-E-0000.bin"
private noncomputable def ep000000011011_1 : Blocks := edgeBlocks% "full/vectors/000000011011-E-0001.bin"
private noncomputable def ep000000011011_2 : Blocks := edgeBlocks% "full/vectors/000000011011-E-0002.bin"
private noncomputable def ep000000011011_3 : Blocks := edgeBlocks% "full/vectors/000000011011-E-0003.bin"
private noncomputable def ep000000011011_4 : Blocks := edgeBlocks% "full/vectors/000000011011-E-0004.bin"
noncomputable def ep000000011011 : Blocks := (Blocks.join (Blocks.join ep000000011011_0 ep000000011011_1) (Blocks.join ep000000011011_2 (Blocks.join ep000000011011_3 ep000000011011_4)))
private theorem idp000000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001101.list =
    C ((2:ℤ)^578) * horner X vp000000011011.list + horner X ep000000011011.list := by
  exact edge_identity (B := (2:ℤ)^958) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011011 : Branch 1 (-51761639/4000000 : ℚ) vp00000001101 := by
  apply branch_checked idp000000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-51761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-53761639/2000000 : ℚ) by norm_num]
  exact coverp000000011011
theorem coverp00000001101 : Covers (-51761639/4000000 : ℚ) vp00000001101 := join_branches bp000000011010 bp000000011011
private noncomputable def vp0000000110011111_0 : Blocks := edgeBlocks% "full/vectors/0000000110011111-V-0000.bin"
noncomputable def vp0000000110011111 : Blocks := vp0000000110011111_0
theorem coverp0000000110011111 : Covers (-51636639/125000 : ℚ) vp0000000110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110011110_0 : Blocks := edgeBlocks% "full/vectors/0000000110011110-V-0000.bin"
noncomputable def vp0000000110011110 : Blocks := vp0000000110011110_0
theorem coverp0000000110011110 : Covers (-51511639/125000 : ℚ) vp0000000110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011001111_0 : Blocks := edgeBlocks% "full/vectors/000000011001111-V-0000.bin"
noncomputable def vp000000011001111 : Blocks := vp000000011001111_0
private theorem bp0000000110011110 : Branch 0 (-51511639/250000 : ℚ) vp000000011001111 := by
  apply branch_left_normalized (c:=vp0000000110011110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-51511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-51511639/125000 : ℚ) by norm_num]
  exact coverp0000000110011110
private noncomputable def ep0000000110011111_0 : Blocks := edgeBlocks% "full/vectors/0000000110011111-E-0000.bin"
noncomputable def ep0000000110011111 : Blocks := ep0000000110011111_0
private theorem idp0000000110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011001111.list =
    C ((2:ℤ)^55) * horner X vp0000000110011111.list + horner X ep0000000110011111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110011111 : Branch 1 (-51511639/250000 : ℚ) vp000000011001111 := by
  apply branch_checked idp0000000110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-51511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-51636639/125000 : ℚ) by norm_num]
  exact coverp0000000110011111
theorem coverp000000011001111 : Covers (-51511639/250000 : ℚ) vp000000011001111 := join_branches bp0000000110011110 bp0000000110011111
private noncomputable def vp0000000110011101_0 : Blocks := edgeBlocks% "full/vectors/0000000110011101-V-0000.bin"
noncomputable def vp0000000110011101 : Blocks := vp0000000110011101_0
theorem coverp0000000110011101 : Covers (-51386639/125000 : ℚ) vp0000000110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110011100_0 : Blocks := edgeBlocks% "full/vectors/0000000110011100-V-0000.bin"
noncomputable def vp0000000110011100 : Blocks := vp0000000110011100_0
theorem coverp0000000110011100 : Covers (-51261639/125000 : ℚ) vp0000000110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011001110_0 : Blocks := edgeBlocks% "full/vectors/000000011001110-V-0000.bin"
noncomputable def vp000000011001110 : Blocks := vp000000011001110_0
private theorem bp0000000110011100 : Branch 0 (-51261639/250000 : ℚ) vp000000011001110 := by
  apply branch_left_normalized (c:=vp0000000110011100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-51261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-51261639/125000 : ℚ) by norm_num]
  exact coverp0000000110011100
private noncomputable def ep0000000110011101_0 : Blocks := edgeBlocks% "full/vectors/0000000110011101-E-0000.bin"
noncomputable def ep0000000110011101 : Blocks := ep0000000110011101_0
private theorem idp0000000110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011001110.list =
    C ((2:ℤ)^56) * horner X vp0000000110011101.list + horner X ep0000000110011101.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110011101 : Branch 1 (-51261639/250000 : ℚ) vp000000011001110 := by
  apply branch_checked idp0000000110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-51261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-51386639/125000 : ℚ) by norm_num]
  exact coverp0000000110011101
theorem coverp000000011001110 : Covers (-51261639/250000 : ℚ) vp000000011001110 := join_branches bp0000000110011100 bp0000000110011101
private noncomputable def vp00000001100111_0 : Blocks := edgeBlocks% "full/vectors/00000001100111-V-0000.bin"
noncomputable def vp00000001100111 : Blocks := vp00000001100111_0
private theorem bp000000011001110 : Branch 0 (-51261639/500000 : ℚ) vp00000001100111 := by
  apply branch_left_normalized (c:=vp000000011001110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-51261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-51261639/250000 : ℚ) by norm_num]
  exact coverp000000011001110
private noncomputable def ep000000011001111_0 : Blocks := edgeBlocks% "full/vectors/000000011001111-E-0000.bin"
noncomputable def ep000000011001111 : Blocks := ep000000011001111_0
private theorem idp000000011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001100111.list =
    C ((2:ℤ)^93) * horner X vp000000011001111.list + horner X ep000000011001111.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011001111 : Branch 1 (-51261639/500000 : ℚ) vp00000001100111 := by
  apply branch_checked idp000000011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-51261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-51511639/250000 : ℚ) by norm_num]
  exact coverp000000011001111
theorem coverp00000001100111 : Covers (-51261639/500000 : ℚ) vp00000001100111 := join_branches bp000000011001110 bp000000011001111
private noncomputable def vp0000000110011011_0 : Blocks := edgeBlocks% "full/vectors/0000000110011011-V-0000.bin"
noncomputable def vp0000000110011011 : Blocks := vp0000000110011011_0
theorem coverp0000000110011011 : Covers (-51136639/125000 : ℚ) vp0000000110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110011010_0 : Blocks := edgeBlocks% "full/vectors/0000000110011010-V-0000.bin"
noncomputable def vp0000000110011010 : Blocks := vp0000000110011010_0
theorem coverp0000000110011010 : Covers (-51011639/125000 : ℚ) vp0000000110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011001101_0 : Blocks := edgeBlocks% "full/vectors/000000011001101-V-0000.bin"
noncomputable def vp000000011001101 : Blocks := vp000000011001101_0
private theorem bp0000000110011010 : Branch 0 (-51011639/250000 : ℚ) vp000000011001101 := by
  apply branch_left_normalized (c:=vp0000000110011010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-51011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-51011639/125000 : ℚ) by norm_num]
  exact coverp0000000110011010
private noncomputable def ep0000000110011011_0 : Blocks := edgeBlocks% "full/vectors/0000000110011011-E-0000.bin"
noncomputable def ep0000000110011011 : Blocks := ep0000000110011011_0
private theorem idp0000000110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011001101.list =
    C ((2:ℤ)^56) * horner X vp0000000110011011.list + horner X ep0000000110011011.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110011011 : Branch 1 (-51011639/250000 : ℚ) vp000000011001101 := by
  apply branch_checked idp0000000110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-51011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-51136639/125000 : ℚ) by norm_num]
  exact coverp0000000110011011
theorem coverp000000011001101 : Covers (-51011639/250000 : ℚ) vp000000011001101 := join_branches bp0000000110011010 bp0000000110011011
private noncomputable def vp0000000110011001_0 : Blocks := edgeBlocks% "full/vectors/0000000110011001-V-0000.bin"
noncomputable def vp0000000110011001 : Blocks := vp0000000110011001_0
theorem coverp0000000110011001 : Covers (-50886639/125000 : ℚ) vp0000000110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110011000_0 : Blocks := edgeBlocks% "full/vectors/0000000110011000-V-0000.bin"
noncomputable def vp0000000110011000 : Blocks := vp0000000110011000_0
theorem coverp0000000110011000 : Covers (-50761639/125000 : ℚ) vp0000000110011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011001100_0 : Blocks := edgeBlocks% "full/vectors/000000011001100-V-0000.bin"
noncomputable def vp000000011001100 : Blocks := vp000000011001100_0
private theorem bp0000000110011000 : Branch 0 (-50761639/250000 : ℚ) vp000000011001100 := by
  apply branch_left_normalized (c:=vp0000000110011000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-50761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-50761639/125000 : ℚ) by norm_num]
  exact coverp0000000110011000
private noncomputable def ep0000000110011001_0 : Blocks := edgeBlocks% "full/vectors/0000000110011001-E-0000.bin"
noncomputable def ep0000000110011001 : Blocks := ep0000000110011001_0
private theorem idp0000000110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011001100.list =
    C ((2:ℤ)^56) * horner X vp0000000110011001.list + horner X ep0000000110011001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110011001 : Branch 1 (-50761639/250000 : ℚ) vp000000011001100 := by
  apply branch_checked idp0000000110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-50761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-50886639/125000 : ℚ) by norm_num]
  exact coverp0000000110011001
theorem coverp000000011001100 : Covers (-50761639/250000 : ℚ) vp000000011001100 := join_branches bp0000000110011000 bp0000000110011001
private noncomputable def vp00000001100110_0 : Blocks := edgeBlocks% "full/vectors/00000001100110-V-0000.bin"
noncomputable def vp00000001100110 : Blocks := vp00000001100110_0
private theorem bp000000011001100 : Branch 0 (-50761639/500000 : ℚ) vp00000001100110 := by
  apply branch_left_normalized (c:=vp000000011001100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-50761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-50761639/250000 : ℚ) by norm_num]
  exact coverp000000011001100
private noncomputable def ep000000011001101_0 : Blocks := edgeBlocks% "full/vectors/000000011001101-E-0000.bin"
noncomputable def ep000000011001101 : Blocks := ep000000011001101_0
private theorem idp000000011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001100110.list =
    C ((2:ℤ)^93) * horner X vp000000011001101.list + horner X ep000000011001101.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011001101 : Branch 1 (-50761639/500000 : ℚ) vp00000001100110 := by
  apply branch_checked idp000000011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-50761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-51011639/250000 : ℚ) by norm_num]
  exact coverp000000011001101
theorem coverp00000001100110 : Covers (-50761639/500000 : ℚ) vp00000001100110 := join_branches bp000000011001100 bp000000011001101
private noncomputable def vp0000000110011_0 : Blocks := edgeBlocks% "full/vectors/0000000110011-V-0000.bin"
private noncomputable def vp0000000110011_1 : Blocks := edgeBlocks% "full/vectors/0000000110011-V-0001.bin"
noncomputable def vp0000000110011 : Blocks := (Blocks.join vp0000000110011_0 vp0000000110011_1)
private theorem bp00000001100110 : Branch 0 (-50761639/1000000 : ℚ) vp0000000110011 := by
  apply branch_left_normalized (c:=vp00000001100110) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-50761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-50761639/500000 : ℚ) by norm_num]
  exact coverp00000001100110
private noncomputable def ep00000001100111_0 : Blocks := edgeBlocks% "full/vectors/00000001100111-E-0000.bin"
private noncomputable def ep00000001100111_1 : Blocks := edgeBlocks% "full/vectors/00000001100111-E-0001.bin"
noncomputable def ep00000001100111 : Blocks := (Blocks.join ep00000001100111_0 ep00000001100111_1)
private theorem idp00000001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000110011.list =
    C ((2:ℤ)^164) * horner X vp00000001100111.list + horner X ep00000001100111.list := by
  exact edge_identity (B := (2:ℤ)^337) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001100111 : Branch 1 (-50761639/1000000 : ℚ) vp0000000110011 := by
  apply branch_checked idp00000001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-50761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-51261639/500000 : ℚ) by norm_num]
  exact coverp00000001100111
theorem coverp0000000110011 : Covers (-50761639/1000000 : ℚ) vp0000000110011 := join_branches bp00000001100110 bp00000001100111
private noncomputable def vp0000000110010111_0 : Blocks := edgeBlocks% "full/vectors/0000000110010111-V-0000.bin"
noncomputable def vp0000000110010111 : Blocks := vp0000000110010111_0
theorem coverp0000000110010111 : Covers (-50636639/125000 : ℚ) vp0000000110010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110010110_0 : Blocks := edgeBlocks% "full/vectors/0000000110010110-V-0000.bin"
noncomputable def vp0000000110010110 : Blocks := vp0000000110010110_0
theorem coverp0000000110010110 : Covers (-50511639/125000 : ℚ) vp0000000110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011001011_0 : Blocks := edgeBlocks% "full/vectors/000000011001011-V-0000.bin"
noncomputable def vp000000011001011 : Blocks := vp000000011001011_0
private theorem bp0000000110010110 : Branch 0 (-50511639/250000 : ℚ) vp000000011001011 := by
  apply branch_left_normalized (c:=vp0000000110010110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-50511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-50511639/125000 : ℚ) by norm_num]
  exact coverp0000000110010110
private noncomputable def ep0000000110010111_0 : Blocks := edgeBlocks% "full/vectors/0000000110010111-E-0000.bin"
noncomputable def ep0000000110010111 : Blocks := ep0000000110010111_0
private theorem idp0000000110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011001011.list =
    C ((2:ℤ)^57) * horner X vp0000000110010111.list + horner X ep0000000110010111.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110010111 : Branch 1 (-50511639/250000 : ℚ) vp000000011001011 := by
  apply branch_checked idp0000000110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-50511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-50636639/125000 : ℚ) by norm_num]
  exact coverp0000000110010111
theorem coverp000000011001011 : Covers (-50511639/250000 : ℚ) vp000000011001011 := join_branches bp0000000110010110 bp0000000110010111
private noncomputable def vp0000000110010101_0 : Blocks := edgeBlocks% "full/vectors/0000000110010101-V-0000.bin"
noncomputable def vp0000000110010101 : Blocks := vp0000000110010101_0
theorem coverp0000000110010101 : Covers (-50386639/125000 : ℚ) vp0000000110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110010100_0 : Blocks := edgeBlocks% "full/vectors/0000000110010100-V-0000.bin"
noncomputable def vp0000000110010100 : Blocks := vp0000000110010100_0
theorem coverp0000000110010100 : Covers (-50261639/125000 : ℚ) vp0000000110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011001010_0 : Blocks := edgeBlocks% "full/vectors/000000011001010-V-0000.bin"
noncomputable def vp000000011001010 : Blocks := vp000000011001010_0
private theorem bp0000000110010100 : Branch 0 (-50261639/250000 : ℚ) vp000000011001010 := by
  apply branch_left_normalized (c:=vp0000000110010100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-50261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-50261639/125000 : ℚ) by norm_num]
  exact coverp0000000110010100
private noncomputable def ep0000000110010101_0 : Blocks := edgeBlocks% "full/vectors/0000000110010101-E-0000.bin"
noncomputable def ep0000000110010101 : Blocks := ep0000000110010101_0
private theorem idp0000000110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011001010.list =
    C ((2:ℤ)^57) * horner X vp0000000110010101.list + horner X ep0000000110010101.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110010101 : Branch 1 (-50261639/250000 : ℚ) vp000000011001010 := by
  apply branch_checked idp0000000110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-50261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-50386639/125000 : ℚ) by norm_num]
  exact coverp0000000110010101
theorem coverp000000011001010 : Covers (-50261639/250000 : ℚ) vp000000011001010 := join_branches bp0000000110010100 bp0000000110010101
private noncomputable def vp00000001100101_0 : Blocks := edgeBlocks% "full/vectors/00000001100101-V-0000.bin"
noncomputable def vp00000001100101 : Blocks := vp00000001100101_0
private theorem bp000000011001010 : Branch 0 (-50261639/500000 : ℚ) vp00000001100101 := by
  apply branch_left_normalized (c:=vp000000011001010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-50261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-50261639/250000 : ℚ) by norm_num]
  exact coverp000000011001010
private noncomputable def ep000000011001011_0 : Blocks := edgeBlocks% "full/vectors/000000011001011-E-0000.bin"
noncomputable def ep000000011001011 : Blocks := ep000000011001011_0
private theorem idp000000011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001100101.list =
    C ((2:ℤ)^94) * horner X vp000000011001011.list + horner X ep000000011001011.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011001011 : Branch 1 (-50261639/500000 : ℚ) vp00000001100101 := by
  apply branch_checked idp000000011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-50261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-50511639/250000 : ℚ) by norm_num]
  exact coverp000000011001011
theorem coverp00000001100101 : Covers (-50261639/500000 : ℚ) vp00000001100101 := join_branches bp000000011001010 bp000000011001011
private noncomputable def vp0000000110010011_0 : Blocks := edgeBlocks% "full/vectors/0000000110010011-V-0000.bin"
noncomputable def vp0000000110010011 : Blocks := vp0000000110010011_0
theorem coverp0000000110010011 : Covers (-50136639/125000 : ℚ) vp0000000110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110010010_0 : Blocks := edgeBlocks% "full/vectors/0000000110010010-V-0000.bin"
noncomputable def vp0000000110010010 : Blocks := vp0000000110010010_0
theorem coverp0000000110010010 : Covers (-50011639/125000 : ℚ) vp0000000110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011001001_0 : Blocks := edgeBlocks% "full/vectors/000000011001001-V-0000.bin"
noncomputable def vp000000011001001 : Blocks := vp000000011001001_0
private theorem bp0000000110010010 : Branch 0 (-50011639/250000 : ℚ) vp000000011001001 := by
  apply branch_left_normalized (c:=vp0000000110010010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-50011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-50011639/125000 : ℚ) by norm_num]
  exact coverp0000000110010010
private noncomputable def ep0000000110010011_0 : Blocks := edgeBlocks% "full/vectors/0000000110010011-E-0000.bin"
noncomputable def ep0000000110010011 : Blocks := ep0000000110010011_0
private theorem idp0000000110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011001001.list =
    C ((2:ℤ)^56) * horner X vp0000000110010011.list + horner X ep0000000110010011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110010011 : Branch 1 (-50011639/250000 : ℚ) vp000000011001001 := by
  apply branch_checked idp0000000110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-50011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-50136639/125000 : ℚ) by norm_num]
  exact coverp0000000110010011
theorem coverp000000011001001 : Covers (-50011639/250000 : ℚ) vp000000011001001 := join_branches bp0000000110010010 bp0000000110010011
private noncomputable def vp0000000110010001_0 : Blocks := edgeBlocks% "full/vectors/0000000110010001-V-0000.bin"
noncomputable def vp0000000110010001 : Blocks := vp0000000110010001_0
theorem coverp0000000110010001 : Covers (-49886639/125000 : ℚ) vp0000000110010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110010000_0 : Blocks := edgeBlocks% "full/vectors/0000000110010000-V-0000.bin"
noncomputable def vp0000000110010000 : Blocks := vp0000000110010000_0
theorem coverp0000000110010000 : Covers (-49761639/125000 : ℚ) vp0000000110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011001000_0 : Blocks := edgeBlocks% "full/vectors/000000011001000-V-0000.bin"
noncomputable def vp000000011001000 : Blocks := vp000000011001000_0
private theorem bp0000000110010000 : Branch 0 (-49761639/250000 : ℚ) vp000000011001000 := by
  apply branch_left_normalized (c:=vp0000000110010000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-49761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-49761639/125000 : ℚ) by norm_num]
  exact coverp0000000110010000
private noncomputable def ep0000000110010001_0 : Blocks := edgeBlocks% "full/vectors/0000000110010001-E-0000.bin"
noncomputable def ep0000000110010001 : Blocks := ep0000000110010001_0
private theorem idp0000000110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011001000.list =
    C ((2:ℤ)^56) * horner X vp0000000110010001.list + horner X ep0000000110010001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110010001 : Branch 1 (-49761639/250000 : ℚ) vp000000011001000 := by
  apply branch_checked idp0000000110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-49761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-49886639/125000 : ℚ) by norm_num]
  exact coverp0000000110010001
theorem coverp000000011001000 : Covers (-49761639/250000 : ℚ) vp000000011001000 := join_branches bp0000000110010000 bp0000000110010001
private noncomputable def vp00000001100100_0 : Blocks := edgeBlocks% "full/vectors/00000001100100-V-0000.bin"
noncomputable def vp00000001100100 : Blocks := vp00000001100100_0
private theorem bp000000011001000 : Branch 0 (-49761639/500000 : ℚ) vp00000001100100 := by
  apply branch_left_normalized (c:=vp000000011001000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-49761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-49761639/250000 : ℚ) by norm_num]
  exact coverp000000011001000
private noncomputable def ep000000011001001_0 : Blocks := edgeBlocks% "full/vectors/000000011001001-E-0000.bin"
noncomputable def ep000000011001001 : Blocks := ep000000011001001_0
private theorem idp000000011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001100100.list =
    C ((2:ℤ)^93) * horner X vp000000011001001.list + horner X ep000000011001001.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011001001 : Branch 1 (-49761639/500000 : ℚ) vp00000001100100 := by
  apply branch_checked idp000000011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-49761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-50011639/250000 : ℚ) by norm_num]
  exact coverp000000011001001
theorem coverp00000001100100 : Covers (-49761639/500000 : ℚ) vp00000001100100 := join_branches bp000000011001000 bp000000011001001
private noncomputable def vp0000000110010_0 : Blocks := edgeBlocks% "full/vectors/0000000110010-V-0000.bin"
private noncomputable def vp0000000110010_1 : Blocks := edgeBlocks% "full/vectors/0000000110010-V-0001.bin"
noncomputable def vp0000000110010 : Blocks := (Blocks.join vp0000000110010_0 vp0000000110010_1)
private theorem bp00000001100100 : Branch 0 (-49761639/1000000 : ℚ) vp0000000110010 := by
  apply branch_left_normalized (c:=vp00000001100100) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-49761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-49761639/500000 : ℚ) by norm_num]
  exact coverp00000001100100
private noncomputable def ep00000001100101_0 : Blocks := edgeBlocks% "full/vectors/00000001100101-E-0000.bin"
private noncomputable def ep00000001100101_1 : Blocks := edgeBlocks% "full/vectors/00000001100101-E-0001.bin"
noncomputable def ep00000001100101 : Blocks := (Blocks.join ep00000001100101_0 ep00000001100101_1)
private theorem idp00000001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000110010.list =
    C ((2:ℤ)^163) * horner X vp00000001100101.list + horner X ep00000001100101.list := by
  exact edge_identity (B := (2:ℤ)^338) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001100101 : Branch 1 (-49761639/1000000 : ℚ) vp0000000110010 := by
  apply branch_checked idp00000001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-49761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-50261639/500000 : ℚ) by norm_num]
  exact coverp00000001100101
theorem coverp0000000110010 : Covers (-49761639/1000000 : ℚ) vp0000000110010 := join_branches bp00000001100100 bp00000001100101
private noncomputable def vp000000011001_0 : Blocks := edgeBlocks% "full/vectors/000000011001-V-0000.bin"
private noncomputable def vp000000011001_1 : Blocks := edgeBlocks% "full/vectors/000000011001-V-0001.bin"
private noncomputable def vp000000011001_2 : Blocks := edgeBlocks% "full/vectors/000000011001-V-0002.bin"
noncomputable def vp000000011001 : Blocks := (Blocks.join vp000000011001_0 (Blocks.join vp000000011001_1 vp000000011001_2))
private theorem bp0000000110010 : Branch 0 (-49761639/2000000 : ℚ) vp000000011001 := by
  apply branch_left_normalized (c:=vp0000000110010) (k:=0) (m:=161) (by decide +kernel)
  rw [show 2*(-49761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-49761639/1000000 : ℚ) by norm_num]
  exact coverp0000000110010
private noncomputable def ep0000000110011_0 : Blocks := edgeBlocks% "full/vectors/0000000110011-E-0000.bin"
private noncomputable def ep0000000110011_1 : Blocks := edgeBlocks% "full/vectors/0000000110011-E-0001.bin"
private noncomputable def ep0000000110011_2 : Blocks := edgeBlocks% "full/vectors/0000000110011-E-0002.bin"
noncomputable def ep0000000110011 : Blocks := (Blocks.join ep0000000110011_0 (Blocks.join ep0000000110011_1 ep0000000110011_2))
private theorem idp0000000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011001.list =
    C ((2:ℤ)^306) * horner X vp0000000110011.list + horner X ep0000000110011.list := by
  exact edge_identity (B := (2:ℤ)^550) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110011 : Branch 1 (-49761639/2000000 : ℚ) vp000000011001 := by
  apply branch_checked idp0000000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-49761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-50761639/1000000 : ℚ) by norm_num]
  exact coverp0000000110011
theorem coverp000000011001 : Covers (-49761639/2000000 : ℚ) vp000000011001 := join_branches bp0000000110010 bp0000000110011
private noncomputable def vp0000000110001111_0 : Blocks := edgeBlocks% "full/vectors/0000000110001111-V-0000.bin"
noncomputable def vp0000000110001111 : Blocks := vp0000000110001111_0
theorem coverp0000000110001111 : Covers (-49636639/125000 : ℚ) vp0000000110001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110001110_0 : Blocks := edgeBlocks% "full/vectors/0000000110001110-V-0000.bin"
noncomputable def vp0000000110001110 : Blocks := vp0000000110001110_0
theorem coverp0000000110001110 : Covers (-49511639/125000 : ℚ) vp0000000110001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011000111_0 : Blocks := edgeBlocks% "full/vectors/000000011000111-V-0000.bin"
noncomputable def vp000000011000111 : Blocks := vp000000011000111_0
private theorem bp0000000110001110 : Branch 0 (-49511639/250000 : ℚ) vp000000011000111 := by
  apply branch_left_normalized (c:=vp0000000110001110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-49511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-49511639/125000 : ℚ) by norm_num]
  exact coverp0000000110001110
private noncomputable def ep0000000110001111_0 : Blocks := edgeBlocks% "full/vectors/0000000110001111-E-0000.bin"
noncomputable def ep0000000110001111 : Blocks := ep0000000110001111_0
private theorem idp0000000110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011000111.list =
    C ((2:ℤ)^56) * horner X vp0000000110001111.list + horner X ep0000000110001111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110001111 : Branch 1 (-49511639/250000 : ℚ) vp000000011000111 := by
  apply branch_checked idp0000000110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-49511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-49636639/125000 : ℚ) by norm_num]
  exact coverp0000000110001111
theorem coverp000000011000111 : Covers (-49511639/250000 : ℚ) vp000000011000111 := join_branches bp0000000110001110 bp0000000110001111
private noncomputable def vp0000000110001101_0 : Blocks := edgeBlocks% "full/vectors/0000000110001101-V-0000.bin"
noncomputable def vp0000000110001101 : Blocks := vp0000000110001101_0
theorem coverp0000000110001101 : Covers (-49386639/125000 : ℚ) vp0000000110001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110001100_0 : Blocks := edgeBlocks% "full/vectors/0000000110001100-V-0000.bin"
noncomputable def vp0000000110001100 : Blocks := vp0000000110001100_0
theorem coverp0000000110001100 : Covers (-49261639/125000 : ℚ) vp0000000110001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011000110_0 : Blocks := edgeBlocks% "full/vectors/000000011000110-V-0000.bin"
noncomputable def vp000000011000110 : Blocks := vp000000011000110_0
private theorem bp0000000110001100 : Branch 0 (-49261639/250000 : ℚ) vp000000011000110 := by
  apply branch_left_normalized (c:=vp0000000110001100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-49261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-49261639/125000 : ℚ) by norm_num]
  exact coverp0000000110001100
private noncomputable def ep0000000110001101_0 : Blocks := edgeBlocks% "full/vectors/0000000110001101-E-0000.bin"
noncomputable def ep0000000110001101 : Blocks := ep0000000110001101_0
private theorem idp0000000110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011000110.list =
    C ((2:ℤ)^55) * horner X vp0000000110001101.list + horner X ep0000000110001101.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110001101 : Branch 1 (-49261639/250000 : ℚ) vp000000011000110 := by
  apply branch_checked idp0000000110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-49261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-49386639/125000 : ℚ) by norm_num]
  exact coverp0000000110001101
theorem coverp000000011000110 : Covers (-49261639/250000 : ℚ) vp000000011000110 := join_branches bp0000000110001100 bp0000000110001101
private noncomputable def vp00000001100011_0 : Blocks := edgeBlocks% "full/vectors/00000001100011-V-0000.bin"
noncomputable def vp00000001100011 : Blocks := vp00000001100011_0
private theorem bp000000011000110 : Branch 0 (-49261639/500000 : ℚ) vp00000001100011 := by
  apply branch_left_normalized (c:=vp000000011000110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-49261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-49261639/250000 : ℚ) by norm_num]
  exact coverp000000011000110
private noncomputable def ep000000011000111_0 : Blocks := edgeBlocks% "full/vectors/000000011000111-E-0000.bin"
noncomputable def ep000000011000111 : Blocks := ep000000011000111_0
private theorem idp000000011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001100011.list =
    C ((2:ℤ)^93) * horner X vp000000011000111.list + horner X ep000000011000111.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011000111 : Branch 1 (-49261639/500000 : ℚ) vp00000001100011 := by
  apply branch_checked idp000000011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-49261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-49511639/250000 : ℚ) by norm_num]
  exact coverp000000011000111
theorem coverp00000001100011 : Covers (-49261639/500000 : ℚ) vp00000001100011 := join_branches bp000000011000110 bp000000011000111
private noncomputable def vp0000000110001011_0 : Blocks := edgeBlocks% "full/vectors/0000000110001011-V-0000.bin"
noncomputable def vp0000000110001011 : Blocks := vp0000000110001011_0
theorem coverp0000000110001011 : Covers (-49136639/125000 : ℚ) vp0000000110001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110001010_0 : Blocks := edgeBlocks% "full/vectors/0000000110001010-V-0000.bin"
noncomputable def vp0000000110001010 : Blocks := vp0000000110001010_0
theorem coverp0000000110001010 : Covers (-49011639/125000 : ℚ) vp0000000110001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011000101_0 : Blocks := edgeBlocks% "full/vectors/000000011000101-V-0000.bin"
noncomputable def vp000000011000101 : Blocks := vp000000011000101_0
private theorem bp0000000110001010 : Branch 0 (-49011639/250000 : ℚ) vp000000011000101 := by
  apply branch_left_normalized (c:=vp0000000110001010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-49011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-49011639/125000 : ℚ) by norm_num]
  exact coverp0000000110001010
private noncomputable def ep0000000110001011_0 : Blocks := edgeBlocks% "full/vectors/0000000110001011-E-0000.bin"
noncomputable def ep0000000110001011 : Blocks := ep0000000110001011_0
private theorem idp0000000110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011000101.list =
    C ((2:ℤ)^56) * horner X vp0000000110001011.list + horner X ep0000000110001011.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110001011 : Branch 1 (-49011639/250000 : ℚ) vp000000011000101 := by
  apply branch_checked idp0000000110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-49011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-49136639/125000 : ℚ) by norm_num]
  exact coverp0000000110001011
theorem coverp000000011000101 : Covers (-49011639/250000 : ℚ) vp000000011000101 := join_branches bp0000000110001010 bp0000000110001011
private noncomputable def vp0000000110001001_0 : Blocks := edgeBlocks% "full/vectors/0000000110001001-V-0000.bin"
noncomputable def vp0000000110001001 : Blocks := vp0000000110001001_0
theorem coverp0000000110001001 : Covers (-48886639/125000 : ℚ) vp0000000110001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110001000_0 : Blocks := edgeBlocks% "full/vectors/0000000110001000-V-0000.bin"
noncomputable def vp0000000110001000 : Blocks := vp0000000110001000_0
theorem coverp0000000110001000 : Covers (-48761639/125000 : ℚ) vp0000000110001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011000100_0 : Blocks := edgeBlocks% "full/vectors/000000011000100-V-0000.bin"
noncomputable def vp000000011000100 : Blocks := vp000000011000100_0
private theorem bp0000000110001000 : Branch 0 (-48761639/250000 : ℚ) vp000000011000100 := by
  apply branch_left_normalized (c:=vp0000000110001000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-48761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-48761639/125000 : ℚ) by norm_num]
  exact coverp0000000110001000
private noncomputable def ep0000000110001001_0 : Blocks := edgeBlocks% "full/vectors/0000000110001001-E-0000.bin"
noncomputable def ep0000000110001001 : Blocks := ep0000000110001001_0
private theorem idp0000000110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011000100.list =
    C ((2:ℤ)^57) * horner X vp0000000110001001.list + horner X ep0000000110001001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110001001 : Branch 1 (-48761639/250000 : ℚ) vp000000011000100 := by
  apply branch_checked idp0000000110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-48761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-48886639/125000 : ℚ) by norm_num]
  exact coverp0000000110001001
theorem coverp000000011000100 : Covers (-48761639/250000 : ℚ) vp000000011000100 := join_branches bp0000000110001000 bp0000000110001001
private noncomputable def vp00000001100010_0 : Blocks := edgeBlocks% "full/vectors/00000001100010-V-0000.bin"
noncomputable def vp00000001100010 : Blocks := vp00000001100010_0
private theorem bp000000011000100 : Branch 0 (-48761639/500000 : ℚ) vp00000001100010 := by
  apply branch_left_normalized (c:=vp000000011000100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-48761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-48761639/250000 : ℚ) by norm_num]
  exact coverp000000011000100
private noncomputable def ep000000011000101_0 : Blocks := edgeBlocks% "full/vectors/000000011000101-E-0000.bin"
noncomputable def ep000000011000101 : Blocks := ep000000011000101_0
private theorem idp000000011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001100010.list =
    C ((2:ℤ)^95) * horner X vp000000011000101.list + horner X ep000000011000101.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011000101 : Branch 1 (-48761639/500000 : ℚ) vp00000001100010 := by
  apply branch_checked idp000000011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-48761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-49011639/250000 : ℚ) by norm_num]
  exact coverp000000011000101
theorem coverp00000001100010 : Covers (-48761639/500000 : ℚ) vp00000001100010 := join_branches bp000000011000100 bp000000011000101
private noncomputable def vp0000000110001_0 : Blocks := edgeBlocks% "full/vectors/0000000110001-V-0000.bin"
private noncomputable def vp0000000110001_1 : Blocks := edgeBlocks% "full/vectors/0000000110001-V-0001.bin"
noncomputable def vp0000000110001 : Blocks := (Blocks.join vp0000000110001_0 vp0000000110001_1)
private theorem bp00000001100010 : Branch 0 (-48761639/1000000 : ℚ) vp0000000110001 := by
  apply branch_left_normalized (c:=vp00000001100010) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-48761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-48761639/500000 : ℚ) by norm_num]
  exact coverp00000001100010
private noncomputable def ep00000001100011_0 : Blocks := edgeBlocks% "full/vectors/00000001100011-E-0000.bin"
private noncomputable def ep00000001100011_1 : Blocks := edgeBlocks% "full/vectors/00000001100011-E-0001.bin"
noncomputable def ep00000001100011 : Blocks := (Blocks.join ep00000001100011_0 ep00000001100011_1)
private theorem idp00000001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000110001.list =
    C ((2:ℤ)^168) * horner X vp00000001100011.list + horner X ep00000001100011.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001100011 : Branch 1 (-48761639/1000000 : ℚ) vp0000000110001 := by
  apply branch_checked idp00000001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-48761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-49261639/500000 : ℚ) by norm_num]
  exact coverp00000001100011
theorem coverp0000000110001 : Covers (-48761639/1000000 : ℚ) vp0000000110001 := join_branches bp00000001100010 bp00000001100011
private noncomputable def vp0000000110000111_0 : Blocks := edgeBlocks% "full/vectors/0000000110000111-V-0000.bin"
noncomputable def vp0000000110000111 : Blocks := vp0000000110000111_0
theorem coverp0000000110000111 : Covers (-48636639/125000 : ℚ) vp0000000110000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110000110_0 : Blocks := edgeBlocks% "full/vectors/0000000110000110-V-0000.bin"
noncomputable def vp0000000110000110 : Blocks := vp0000000110000110_0
theorem coverp0000000110000110 : Covers (-48511639/125000 : ℚ) vp0000000110000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011000011_0 : Blocks := edgeBlocks% "full/vectors/000000011000011-V-0000.bin"
noncomputable def vp000000011000011 : Blocks := vp000000011000011_0
private theorem bp0000000110000110 : Branch 0 (-48511639/250000 : ℚ) vp000000011000011 := by
  apply branch_left_normalized (c:=vp0000000110000110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-48511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-48511639/125000 : ℚ) by norm_num]
  exact coverp0000000110000110
private noncomputable def ep0000000110000111_0 : Blocks := edgeBlocks% "full/vectors/0000000110000111-E-0000.bin"
noncomputable def ep0000000110000111 : Blocks := ep0000000110000111_0
private theorem idp0000000110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011000011.list =
    C ((2:ℤ)^58) * horner X vp0000000110000111.list + horner X ep0000000110000111.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110000111 : Branch 1 (-48511639/250000 : ℚ) vp000000011000011 := by
  apply branch_checked idp0000000110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-48511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-48636639/125000 : ℚ) by norm_num]
  exact coverp0000000110000111
theorem coverp000000011000011 : Covers (-48511639/250000 : ℚ) vp000000011000011 := join_branches bp0000000110000110 bp0000000110000111
private noncomputable def vp0000000110000101_0 : Blocks := edgeBlocks% "full/vectors/0000000110000101-V-0000.bin"
noncomputable def vp0000000110000101 : Blocks := vp0000000110000101_0
theorem coverp0000000110000101 : Covers (-48386639/125000 : ℚ) vp0000000110000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110000100_0 : Blocks := edgeBlocks% "full/vectors/0000000110000100-V-0000.bin"
noncomputable def vp0000000110000100 : Blocks := vp0000000110000100_0
theorem coverp0000000110000100 : Covers (-48261639/125000 : ℚ) vp0000000110000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011000010_0 : Blocks := edgeBlocks% "full/vectors/000000011000010-V-0000.bin"
noncomputable def vp000000011000010 : Blocks := vp000000011000010_0
private theorem bp0000000110000100 : Branch 0 (-48261639/250000 : ℚ) vp000000011000010 := by
  apply branch_left_normalized (c:=vp0000000110000100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-48261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-48261639/125000 : ℚ) by norm_num]
  exact coverp0000000110000100
private noncomputable def ep0000000110000101_0 : Blocks := edgeBlocks% "full/vectors/0000000110000101-E-0000.bin"
noncomputable def ep0000000110000101 : Blocks := ep0000000110000101_0
private theorem idp0000000110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011000010.list =
    C ((2:ℤ)^57) * horner X vp0000000110000101.list + horner X ep0000000110000101.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110000101 : Branch 1 (-48261639/250000 : ℚ) vp000000011000010 := by
  apply branch_checked idp0000000110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-48261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-48386639/125000 : ℚ) by norm_num]
  exact coverp0000000110000101
theorem coverp000000011000010 : Covers (-48261639/250000 : ℚ) vp000000011000010 := join_branches bp0000000110000100 bp0000000110000101
private noncomputable def vp00000001100001_0 : Blocks := edgeBlocks% "full/vectors/00000001100001-V-0000.bin"
noncomputable def vp00000001100001 : Blocks := vp00000001100001_0
private theorem bp000000011000010 : Branch 0 (-48261639/500000 : ℚ) vp00000001100001 := by
  apply branch_left_normalized (c:=vp000000011000010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-48261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-48261639/250000 : ℚ) by norm_num]
  exact coverp000000011000010
private noncomputable def ep000000011000011_0 : Blocks := edgeBlocks% "full/vectors/000000011000011-E-0000.bin"
noncomputable def ep000000011000011 : Blocks := ep000000011000011_0
private theorem idp000000011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001100001.list =
    C ((2:ℤ)^94) * horner X vp000000011000011.list + horner X ep000000011000011.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011000011 : Branch 1 (-48261639/500000 : ℚ) vp00000001100001 := by
  apply branch_checked idp000000011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-48261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-48511639/250000 : ℚ) by norm_num]
  exact coverp000000011000011
theorem coverp00000001100001 : Covers (-48261639/500000 : ℚ) vp00000001100001 := join_branches bp000000011000010 bp000000011000011
private noncomputable def vp0000000110000011_0 : Blocks := edgeBlocks% "full/vectors/0000000110000011-V-0000.bin"
noncomputable def vp0000000110000011 : Blocks := vp0000000110000011_0
theorem coverp0000000110000011 : Covers (-48136639/125000 : ℚ) vp0000000110000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110000010_0 : Blocks := edgeBlocks% "full/vectors/0000000110000010-V-0000.bin"
noncomputable def vp0000000110000010 : Blocks := vp0000000110000010_0
theorem coverp0000000110000010 : Covers (-48011639/125000 : ℚ) vp0000000110000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011000001_0 : Blocks := edgeBlocks% "full/vectors/000000011000001-V-0000.bin"
noncomputable def vp000000011000001 : Blocks := vp000000011000001_0
private theorem bp0000000110000010 : Branch 0 (-48011639/250000 : ℚ) vp000000011000001 := by
  apply branch_left_normalized (c:=vp0000000110000010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-48011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-48011639/125000 : ℚ) by norm_num]
  exact coverp0000000110000010
private noncomputable def ep0000000110000011_0 : Blocks := edgeBlocks% "full/vectors/0000000110000011-E-0000.bin"
noncomputable def ep0000000110000011 : Blocks := ep0000000110000011_0
private theorem idp0000000110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011000001.list =
    C ((2:ℤ)^56) * horner X vp0000000110000011.list + horner X ep0000000110000011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110000011 : Branch 1 (-48011639/250000 : ℚ) vp000000011000001 := by
  apply branch_checked idp0000000110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-48011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-48136639/125000 : ℚ) by norm_num]
  exact coverp0000000110000011
theorem coverp000000011000001 : Covers (-48011639/250000 : ℚ) vp000000011000001 := join_branches bp0000000110000010 bp0000000110000011
private noncomputable def vp0000000110000001_0 : Blocks := edgeBlocks% "full/vectors/0000000110000001-V-0000.bin"
noncomputable def vp0000000110000001 : Blocks := vp0000000110000001_0
theorem coverp0000000110000001 : Covers (-47886639/125000 : ℚ) vp0000000110000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000110000000_0 : Blocks := edgeBlocks% "full/vectors/0000000110000000-V-0000.bin"
noncomputable def vp0000000110000000 : Blocks := vp0000000110000000_0
theorem coverp0000000110000000 : Covers (-47761639/125000 : ℚ) vp0000000110000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011000000_0 : Blocks := edgeBlocks% "full/vectors/000000011000000-V-0000.bin"
noncomputable def vp000000011000000 : Blocks := vp000000011000000_0
private theorem bp0000000110000000 : Branch 0 (-47761639/250000 : ℚ) vp000000011000000 := by
  apply branch_left_normalized (c:=vp0000000110000000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-47761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-47761639/125000 : ℚ) by norm_num]
  exact coverp0000000110000000
private noncomputable def ep0000000110000001_0 : Blocks := edgeBlocks% "full/vectors/0000000110000001-E-0000.bin"
noncomputable def ep0000000110000001 : Blocks := ep0000000110000001_0
private theorem idp0000000110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011000000.list =
    C ((2:ℤ)^56) * horner X vp0000000110000001.list + horner X ep0000000110000001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110000001 : Branch 1 (-47761639/250000 : ℚ) vp000000011000000 := by
  apply branch_checked idp0000000110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-47761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-47886639/125000 : ℚ) by norm_num]
  exact coverp0000000110000001
theorem coverp000000011000000 : Covers (-47761639/250000 : ℚ) vp000000011000000 := join_branches bp0000000110000000 bp0000000110000001
private noncomputable def vp00000001100000_0 : Blocks := edgeBlocks% "full/vectors/00000001100000-V-0000.bin"
noncomputable def vp00000001100000 : Blocks := vp00000001100000_0
private theorem bp000000011000000 : Branch 0 (-47761639/500000 : ℚ) vp00000001100000 := by
  apply branch_left_normalized (c:=vp000000011000000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-47761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-47761639/250000 : ℚ) by norm_num]
  exact coverp000000011000000
private noncomputable def ep000000011000001_0 : Blocks := edgeBlocks% "full/vectors/000000011000001-E-0000.bin"
noncomputable def ep000000011000001 : Blocks := ep000000011000001_0
private theorem idp000000011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001100000.list =
    C ((2:ℤ)^94) * horner X vp000000011000001.list + horner X ep000000011000001.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011000001 : Branch 1 (-47761639/500000 : ℚ) vp00000001100000 := by
  apply branch_checked idp000000011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-47761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-48011639/250000 : ℚ) by norm_num]
  exact coverp000000011000001
theorem coverp00000001100000 : Covers (-47761639/500000 : ℚ) vp00000001100000 := join_branches bp000000011000000 bp000000011000001
private noncomputable def vp0000000110000_0 : Blocks := edgeBlocks% "full/vectors/0000000110000-V-0000.bin"
private noncomputable def vp0000000110000_1 : Blocks := edgeBlocks% "full/vectors/0000000110000-V-0001.bin"
noncomputable def vp0000000110000 : Blocks := (Blocks.join vp0000000110000_0 vp0000000110000_1)
private theorem bp00000001100000 : Branch 0 (-47761639/1000000 : ℚ) vp0000000110000 := by
  apply branch_left_normalized (c:=vp00000001100000) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-47761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-47761639/500000 : ℚ) by norm_num]
  exact coverp00000001100000
private noncomputable def ep00000001100001_0 : Blocks := edgeBlocks% "full/vectors/00000001100001-E-0000.bin"
private noncomputable def ep00000001100001_1 : Blocks := edgeBlocks% "full/vectors/00000001100001-E-0001.bin"
noncomputable def ep00000001100001 : Blocks := (Blocks.join ep00000001100001_0 ep00000001100001_1)
private theorem idp00000001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000110000.list =
    C ((2:ℤ)^166) * horner X vp00000001100001.list + horner X ep00000001100001.list := by
  exact edge_identity (B := (2:ℤ)^342) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001100001 : Branch 1 (-47761639/1000000 : ℚ) vp0000000110000 := by
  apply branch_checked idp00000001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-47761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-48261639/500000 : ℚ) by norm_num]
  exact coverp00000001100001
theorem coverp0000000110000 : Covers (-47761639/1000000 : ℚ) vp0000000110000 := join_branches bp00000001100000 bp00000001100001
private noncomputable def vp000000011000_0 : Blocks := edgeBlocks% "full/vectors/000000011000-V-0000.bin"
private noncomputable def vp000000011000_1 : Blocks := edgeBlocks% "full/vectors/000000011000-V-0001.bin"
private noncomputable def vp000000011000_2 : Blocks := edgeBlocks% "full/vectors/000000011000-V-0002.bin"
noncomputable def vp000000011000 : Blocks := (Blocks.join vp000000011000_0 (Blocks.join vp000000011000_1 vp000000011000_2))
private theorem bp0000000110000 : Branch 0 (-47761639/2000000 : ℚ) vp000000011000 := by
  apply branch_left_normalized (c:=vp0000000110000) (k:=0) (m:=164) (by decide +kernel)
  rw [show 2*(-47761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-47761639/1000000 : ℚ) by norm_num]
  exact coverp0000000110000
private noncomputable def ep0000000110001_0 : Blocks := edgeBlocks% "full/vectors/0000000110001-E-0000.bin"
private noncomputable def ep0000000110001_1 : Blocks := edgeBlocks% "full/vectors/0000000110001-E-0001.bin"
private noncomputable def ep0000000110001_2 : Blocks := edgeBlocks% "full/vectors/0000000110001-E-0002.bin"
noncomputable def ep0000000110001 : Blocks := (Blocks.join ep0000000110001_0 (Blocks.join ep0000000110001_1 ep0000000110001_2))
private theorem idp0000000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011000.list =
    C ((2:ℤ)^311) * horner X vp0000000110001.list + horner X ep0000000110001.list := by
  exact edge_identity (B := (2:ℤ)^558) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000110001 : Branch 1 (-47761639/2000000 : ℚ) vp000000011000 := by
  apply branch_checked idp0000000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-47761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-48761639/1000000 : ℚ) by norm_num]
  exact coverp0000000110001
theorem coverp000000011000 : Covers (-47761639/2000000 : ℚ) vp000000011000 := join_branches bp0000000110000 bp0000000110001
private noncomputable def vp00000001100_0 : Blocks := edgeBlocks% "full/vectors/00000001100-V-0000.bin"
private noncomputable def vp00000001100_1 : Blocks := edgeBlocks% "full/vectors/00000001100-V-0001.bin"
private noncomputable def vp00000001100_2 : Blocks := edgeBlocks% "full/vectors/00000001100-V-0002.bin"
private noncomputable def vp00000001100_3 : Blocks := edgeBlocks% "full/vectors/00000001100-V-0003.bin"
private noncomputable def vp00000001100_4 : Blocks := edgeBlocks% "full/vectors/00000001100-V-0004.bin"
noncomputable def vp00000001100 : Blocks := (Blocks.join (Blocks.join vp00000001100_0 vp00000001100_1) (Blocks.join vp00000001100_2 (Blocks.join vp00000001100_3 vp00000001100_4)))
private theorem bp000000011000 : Branch 0 (-47761639/4000000 : ℚ) vp00000001100 := by
  apply branch_left_normalized (c:=vp000000011000) (k:=0) (m:=305) (by decide +kernel)
  rw [show 2*(-47761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-47761639/2000000 : ℚ) by norm_num]
  exact coverp000000011000
private noncomputable def ep000000011001_0 : Blocks := edgeBlocks% "full/vectors/000000011001-E-0000.bin"
private noncomputable def ep000000011001_1 : Blocks := edgeBlocks% "full/vectors/000000011001-E-0001.bin"
private noncomputable def ep000000011001_2 : Blocks := edgeBlocks% "full/vectors/000000011001-E-0002.bin"
private noncomputable def ep000000011001_3 : Blocks := edgeBlocks% "full/vectors/000000011001-E-0003.bin"
private noncomputable def ep000000011001_4 : Blocks := edgeBlocks% "full/vectors/000000011001-E-0004.bin"
noncomputable def ep000000011001 : Blocks := (Blocks.join (Blocks.join ep000000011001_0 ep000000011001_1) (Blocks.join ep000000011001_2 (Blocks.join ep000000011001_3 ep000000011001_4)))
private theorem idp000000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001100.list =
    C ((2:ℤ)^597) * horner X vp000000011001.list + horner X ep000000011001.list := by
  exact edge_identity (B := (2:ℤ)^988) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011001 : Branch 1 (-47761639/4000000 : ℚ) vp00000001100 := by
  apply branch_checked idp000000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-47761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-49761639/2000000 : ℚ) by norm_num]
  exact coverp000000011001
theorem coverp00000001100 : Covers (-47761639/4000000 : ℚ) vp00000001100 := join_branches bp000000011000 bp000000011001
private noncomputable def vp0000000110_0 : Blocks := edgeBlocks% "full/vectors/0000000110-V-0000.bin"
private noncomputable def vp0000000110_1 : Blocks := edgeBlocks% "full/vectors/0000000110-V-0001.bin"
private noncomputable def vp0000000110_2 : Blocks := edgeBlocks% "full/vectors/0000000110-V-0002.bin"
private noncomputable def vp0000000110_3 : Blocks := edgeBlocks% "full/vectors/0000000110-V-0003.bin"
private noncomputable def vp0000000110_4 : Blocks := edgeBlocks% "full/vectors/0000000110-V-0004.bin"
private noncomputable def vp0000000110_5 : Blocks := edgeBlocks% "full/vectors/0000000110-V-0005.bin"
private noncomputable def vp0000000110_6 : Blocks := edgeBlocks% "full/vectors/0000000110-V-0006.bin"
private noncomputable def vp0000000110_7 : Blocks := edgeBlocks% "full/vectors/0000000110-V-0007.bin"
private noncomputable def vp0000000110_8 : Blocks := edgeBlocks% "full/vectors/0000000110-V-0008.bin"
noncomputable def vp0000000110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0000000110_0 vp0000000110_1) (Blocks.join vp0000000110_2 vp0000000110_3)) (Blocks.join (Blocks.join vp0000000110_4 vp0000000110_5) (Blocks.join vp0000000110_6 (Blocks.join vp0000000110_7 vp0000000110_8))))
private theorem bp00000001100 : Branch 0 (-47761639/8000000 : ℚ) vp0000000110 := by
  apply branch_left_normalized (c:=vp00000001100) (k:=0) (m:=585) (by decide +kernel)
  rw [show 2*(-47761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-47761639/4000000 : ℚ) by norm_num]
  exact coverp00000001100
private noncomputable def ep00000001101_0 : Blocks := edgeBlocks% "full/vectors/00000001101-E-0000.bin"
private noncomputable def ep00000001101_1 : Blocks := edgeBlocks% "full/vectors/00000001101-E-0001.bin"
private noncomputable def ep00000001101_2 : Blocks := edgeBlocks% "full/vectors/00000001101-E-0002.bin"
private noncomputable def ep00000001101_3 : Blocks := edgeBlocks% "full/vectors/00000001101-E-0003.bin"
private noncomputable def ep00000001101_4 : Blocks := edgeBlocks% "full/vectors/00000001101-E-0004.bin"
private noncomputable def ep00000001101_5 : Blocks := edgeBlocks% "full/vectors/00000001101-E-0005.bin"
private noncomputable def ep00000001101_6 : Blocks := edgeBlocks% "full/vectors/00000001101-E-0006.bin"
private noncomputable def ep00000001101_7 : Blocks := edgeBlocks% "full/vectors/00000001101-E-0007.bin"
private noncomputable def ep00000001101_8 : Blocks := edgeBlocks% "full/vectors/00000001101-E-0008.bin"
noncomputable def ep00000001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00000001101_0 ep00000001101_1) (Blocks.join ep00000001101_2 ep00000001101_3)) (Blocks.join (Blocks.join ep00000001101_4 ep00000001101_5) (Blocks.join ep00000001101_6 (Blocks.join ep00000001101_7 ep00000001101_8))))
private theorem idp00000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000110.list =
    C ((2:ℤ)^1161) * horner X vp00000001101.list + horner X ep00000001101.list := by
  exact edge_identity (B := (2:ℤ)^1841) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001101 : Branch 1 (-47761639/8000000 : ℚ) vp0000000110 := by
  apply branch_checked idp00000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-47761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-51761639/4000000 : ℚ) by norm_num]
  exact coverp00000001101
theorem coverp0000000110 : Covers (-47761639/8000000 : ℚ) vp0000000110 := join_branches bp00000001100 bp00000001101
private noncomputable def vp000000011_0 : Blocks := edgeBlocks% "full/vectors/000000011-V-0000.bin"
private noncomputable def vp000000011_1 : Blocks := edgeBlocks% "full/vectors/000000011-V-0001.bin"
private noncomputable def vp000000011_2 : Blocks := edgeBlocks% "full/vectors/000000011-V-0002.bin"
private noncomputable def vp000000011_3 : Blocks := edgeBlocks% "full/vectors/000000011-V-0003.bin"
private noncomputable def vp000000011_4 : Blocks := edgeBlocks% "full/vectors/000000011-V-0004.bin"
private noncomputable def vp000000011_5 : Blocks := edgeBlocks% "full/vectors/000000011-V-0005.bin"
private noncomputable def vp000000011_6 : Blocks := edgeBlocks% "full/vectors/000000011-V-0006.bin"
private noncomputable def vp000000011_7 : Blocks := edgeBlocks% "full/vectors/000000011-V-0007.bin"
private noncomputable def vp000000011_8 : Blocks := edgeBlocks% "full/vectors/000000011-V-0008.bin"
private noncomputable def vp000000011_9 : Blocks := edgeBlocks% "full/vectors/000000011-V-0009.bin"
private noncomputable def vp000000011_10 : Blocks := edgeBlocks% "full/vectors/000000011-V-0010.bin"
private noncomputable def vp000000011_11 : Blocks := edgeBlocks% "full/vectors/000000011-V-0011.bin"
private noncomputable def vp000000011_12 : Blocks := edgeBlocks% "full/vectors/000000011-V-0012.bin"
private noncomputable def vp000000011_13 : Blocks := edgeBlocks% "full/vectors/000000011-V-0013.bin"
private noncomputable def vp000000011_14 : Blocks := edgeBlocks% "full/vectors/000000011-V-0014.bin"
private noncomputable def vp000000011_15 : Blocks := edgeBlocks% "full/vectors/000000011-V-0015.bin"
private noncomputable def vp000000011_16 : Blocks := edgeBlocks% "full/vectors/000000011-V-0016.bin"
private noncomputable def vp000000011_17 : Blocks := edgeBlocks% "full/vectors/000000011-V-0017.bin"
noncomputable def vp000000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000000011_0 vp000000011_1) (Blocks.join vp000000011_2 vp000000011_3)) (Blocks.join (Blocks.join vp000000011_4 vp000000011_5) (Blocks.join vp000000011_6 (Blocks.join vp000000011_7 vp000000011_8)))) (Blocks.join (Blocks.join (Blocks.join vp000000011_9 vp000000011_10) (Blocks.join vp000000011_11 vp000000011_12)) (Blocks.join (Blocks.join vp000000011_13 vp000000011_14) (Blocks.join vp000000011_15 (Blocks.join vp000000011_16 vp000000011_17)))))
private theorem bp0000000110 : Branch 0 (-47761639/16000000 : ℚ) vp000000011 := by
  apply branch_left_normalized (c:=vp0000000110) (k:=0) (m:=1139) (by decide +kernel)
  rw [show 2*(-47761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-47761639/8000000 : ℚ) by norm_num]
  exact coverp0000000110
private noncomputable def ep0000000111_0 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0000.bin"
private noncomputable def ep0000000111_1 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0001.bin"
private noncomputable def ep0000000111_2 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0002.bin"
private noncomputable def ep0000000111_3 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0003.bin"
private noncomputable def ep0000000111_4 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0004.bin"
private noncomputable def ep0000000111_5 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0005.bin"
private noncomputable def ep0000000111_6 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0006.bin"
private noncomputable def ep0000000111_7 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0007.bin"
private noncomputable def ep0000000111_8 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0008.bin"
private noncomputable def ep0000000111_9 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0009.bin"
private noncomputable def ep0000000111_10 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0010.bin"
private noncomputable def ep0000000111_11 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0011.bin"
private noncomputable def ep0000000111_12 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0012.bin"
private noncomputable def ep0000000111_13 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0013.bin"
private noncomputable def ep0000000111_14 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0014.bin"
private noncomputable def ep0000000111_15 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0015.bin"
private noncomputable def ep0000000111_16 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0016.bin"
private noncomputable def ep0000000111_17 : Blocks := edgeBlocks% "full/vectors/0000000111-E-0017.bin"
noncomputable def ep0000000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000000111_0 ep0000000111_1) (Blocks.join ep0000000111_2 ep0000000111_3)) (Blocks.join (Blocks.join ep0000000111_4 ep0000000111_5) (Blocks.join ep0000000111_6 (Blocks.join ep0000000111_7 ep0000000111_8)))) (Blocks.join (Blocks.join (Blocks.join ep0000000111_9 ep0000000111_10) (Blocks.join ep0000000111_11 ep0000000111_12)) (Blocks.join (Blocks.join ep0000000111_13 ep0000000111_14) (Blocks.join ep0000000111_15 (Blocks.join ep0000000111_16 ep0000000111_17)))))
private theorem idp0000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011.list =
    C ((2:ℤ)^2262) * horner X vp0000000111.list + horner X ep0000000111.list := by
  exact edge_identity (B := (2:ℤ)^3509) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111 : Branch 1 (-47761639/16000000 : ℚ) vp000000011 := by
  apply branch_checked idp0000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-47761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-55761639/8000000 : ℚ) by norm_num]
  exact coverp0000000111
theorem coverp000000011 : Covers (-47761639/16000000 : ℚ) vp000000011 := join_branches bp0000000110 bp0000000111
end NextProof.EdgeFull

