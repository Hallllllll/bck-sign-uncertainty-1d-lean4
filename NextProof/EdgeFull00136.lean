import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp1010111111_0 : Blocks := edgeBlocks% "full/vectors/1010111111-V-0000.bin"
noncomputable def vp1010111111 : Blocks := vp1010111111_0
theorem coverp1010111111 : Covers (-5623761639/8000000 : ℚ) vp1010111111 := cover_leaf (by decide +kernel)
private noncomputable def vp1010111110_0 : Blocks := edgeBlocks% "full/vectors/1010111110-V-0000.bin"
noncomputable def vp1010111110 : Blocks := vp1010111110_0
theorem coverp1010111110 : Covers (-5615761639/8000000 : ℚ) vp1010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp101011111_0 : Blocks := edgeBlocks% "full/vectors/101011111-V-0000.bin"
private noncomputable def vp101011111_1 : Blocks := edgeBlocks% "full/vectors/101011111-V-0001.bin"
noncomputable def vp101011111 : Blocks := (Blocks.join vp101011111_0 vp101011111_1)
private theorem bp1010111110 : Branch 0 (-5615761639/16000000 : ℚ) vp101011111 := by
  apply branch_left_normalized (c:=vp1010111110) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-5615761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5615761639/8000000 : ℚ) by norm_num]
  exact coverp1010111110
private noncomputable def ep1010111111_0 : Blocks := edgeBlocks% "full/vectors/1010111111-E-0000.bin"
private noncomputable def ep1010111111_1 : Blocks := edgeBlocks% "full/vectors/1010111111-E-0001.bin"
noncomputable def ep1010111111 : Blocks := (Blocks.join ep1010111111_0 ep1010111111_1)
private theorem idp1010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101011111.list =
    C ((2:ℤ)^280) * horner X vp1010111111.list + horner X ep1010111111.list := by
  exact edge_identity (B := (2:ℤ)^446) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010111111 : Branch 1 (-5615761639/16000000 : ℚ) vp101011111 := by
  apply branch_checked idp1010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-5615761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5623761639/8000000 : ℚ) by norm_num]
  exact coverp1010111111
theorem coverp101011111 : Covers (-5615761639/16000000 : ℚ) vp101011111 := join_branches bp1010111110 bp1010111111
private noncomputable def vp1010111101_0 : Blocks := edgeBlocks% "full/vectors/1010111101-V-0000.bin"
noncomputable def vp1010111101 : Blocks := vp1010111101_0
theorem coverp1010111101 : Covers (-5607761639/8000000 : ℚ) vp1010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp1010111100_0 : Blocks := edgeBlocks% "full/vectors/1010111100-V-0000.bin"
noncomputable def vp1010111100 : Blocks := vp1010111100_0
theorem coverp1010111100 : Covers (-5599761639/8000000 : ℚ) vp1010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp101011110_0 : Blocks := edgeBlocks% "full/vectors/101011110-V-0000.bin"
private noncomputable def vp101011110_1 : Blocks := edgeBlocks% "full/vectors/101011110-V-0001.bin"
noncomputable def vp101011110 : Blocks := (Blocks.join vp101011110_0 vp101011110_1)
private theorem bp1010111100 : Branch 0 (-5599761639/16000000 : ℚ) vp101011110 := by
  apply branch_left_normalized (c:=vp1010111100) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-5599761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5599761639/8000000 : ℚ) by norm_num]
  exact coverp1010111100
private noncomputable def ep1010111101_0 : Blocks := edgeBlocks% "full/vectors/1010111101-E-0000.bin"
private noncomputable def ep1010111101_1 : Blocks := edgeBlocks% "full/vectors/1010111101-E-0001.bin"
noncomputable def ep1010111101 : Blocks := (Blocks.join ep1010111101_0 ep1010111101_1)
private theorem idp1010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101011110.list =
    C ((2:ℤ)^279) * horner X vp1010111101.list + horner X ep1010111101.list := by
  exact edge_identity (B := (2:ℤ)^446) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010111101 : Branch 1 (-5599761639/16000000 : ℚ) vp101011110 := by
  apply branch_checked idp1010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-5599761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5607761639/8000000 : ℚ) by norm_num]
  exact coverp1010111101
theorem coverp101011110 : Covers (-5599761639/16000000 : ℚ) vp101011110 := join_branches bp1010111100 bp1010111101
private noncomputable def vp10101111_0 : Blocks := edgeBlocks% "full/vectors/10101111-V-0000.bin"
private noncomputable def vp10101111_1 : Blocks := edgeBlocks% "full/vectors/10101111-V-0001.bin"
private noncomputable def vp10101111_2 : Blocks := edgeBlocks% "full/vectors/10101111-V-0002.bin"
private noncomputable def vp10101111_3 : Blocks := edgeBlocks% "full/vectors/10101111-V-0003.bin"
noncomputable def vp10101111 : Blocks := (Blocks.join (Blocks.join vp10101111_0 vp10101111_1) (Blocks.join vp10101111_2 vp10101111_3))
private theorem bp101011110 : Branch 0 (-5599761639/32000000 : ℚ) vp10101111 := by
  apply branch_left_normalized (c:=vp101011110) (k:=0) (m:=232) (by decide +kernel)
  rw [show 2*(-5599761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5599761639/16000000 : ℚ) by norm_num]
  exact coverp101011110
private noncomputable def ep101011111_0 : Blocks := edgeBlocks% "full/vectors/101011111-E-0000.bin"
private noncomputable def ep101011111_1 : Blocks := edgeBlocks% "full/vectors/101011111-E-0001.bin"
private noncomputable def ep101011111_2 : Blocks := edgeBlocks% "full/vectors/101011111-E-0002.bin"
private noncomputable def ep101011111_3 : Blocks := edgeBlocks% "full/vectors/101011111-E-0003.bin"
noncomputable def ep101011111 : Blocks := (Blocks.join (Blocks.join ep101011111_0 ep101011111_1) (Blocks.join ep101011111_2 ep101011111_3))
private theorem idp101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10101111.list =
    C ((2:ℤ)^533) * horner X vp101011111.list + horner X ep101011111.list := by
  exact edge_identity (B := (2:ℤ)^766) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101011111 : Branch 1 (-5599761639/32000000 : ℚ) vp10101111 := by
  apply branch_checked idp101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-5599761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5615761639/16000000 : ℚ) by norm_num]
  exact coverp101011111
theorem coverp10101111 : Covers (-5599761639/32000000 : ℚ) vp10101111 := join_branches bp101011110 bp101011111
private noncomputable def vp1010111011_0 : Blocks := edgeBlocks% "full/vectors/1010111011-V-0000.bin"
noncomputable def vp1010111011 : Blocks := vp1010111011_0
theorem coverp1010111011 : Covers (-5591761639/8000000 : ℚ) vp1010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp1010111010_0 : Blocks := edgeBlocks% "full/vectors/1010111010-V-0000.bin"
noncomputable def vp1010111010 : Blocks := vp1010111010_0
theorem coverp1010111010 : Covers (-5583761639/8000000 : ℚ) vp1010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp101011101_0 : Blocks := edgeBlocks% "full/vectors/101011101-V-0000.bin"
private noncomputable def vp101011101_1 : Blocks := edgeBlocks% "full/vectors/101011101-V-0001.bin"
noncomputable def vp101011101 : Blocks := (Blocks.join vp101011101_0 vp101011101_1)
private theorem bp1010111010 : Branch 0 (-5583761639/16000000 : ℚ) vp101011101 := by
  apply branch_left_normalized (c:=vp1010111010) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-5583761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5583761639/8000000 : ℚ) by norm_num]
  exact coverp1010111010
private noncomputable def ep1010111011_0 : Blocks := edgeBlocks% "full/vectors/1010111011-E-0000.bin"
private noncomputable def ep1010111011_1 : Blocks := edgeBlocks% "full/vectors/1010111011-E-0001.bin"
noncomputable def ep1010111011 : Blocks := (Blocks.join ep1010111011_0 ep1010111011_1)
private theorem idp1010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101011101.list =
    C ((2:ℤ)^279) * horner X vp1010111011.list + horner X ep1010111011.list := by
  exact edge_identity (B := (2:ℤ)^446) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010111011 : Branch 1 (-5583761639/16000000 : ℚ) vp101011101 := by
  apply branch_checked idp1010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-5583761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5591761639/8000000 : ℚ) by norm_num]
  exact coverp1010111011
theorem coverp101011101 : Covers (-5583761639/16000000 : ℚ) vp101011101 := join_branches bp1010111010 bp1010111011
private noncomputable def vp1010111001_0 : Blocks := edgeBlocks% "full/vectors/1010111001-V-0000.bin"
noncomputable def vp1010111001 : Blocks := vp1010111001_0
theorem coverp1010111001 : Covers (-5575761639/8000000 : ℚ) vp1010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp1010111000_0 : Blocks := edgeBlocks% "full/vectors/1010111000-V-0000.bin"
noncomputable def vp1010111000 : Blocks := vp1010111000_0
theorem coverp1010111000 : Covers (-5567761639/8000000 : ℚ) vp1010111000 := cover_leaf (by decide +kernel)
private noncomputable def vp101011100_0 : Blocks := edgeBlocks% "full/vectors/101011100-V-0000.bin"
private noncomputable def vp101011100_1 : Blocks := edgeBlocks% "full/vectors/101011100-V-0001.bin"
noncomputable def vp101011100 : Blocks := (Blocks.join vp101011100_0 vp101011100_1)
private theorem bp1010111000 : Branch 0 (-5567761639/16000000 : ℚ) vp101011100 := by
  apply branch_left_normalized (c:=vp1010111000) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-5567761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5567761639/8000000 : ℚ) by norm_num]
  exact coverp1010111000
private noncomputable def ep1010111001_0 : Blocks := edgeBlocks% "full/vectors/1010111001-E-0000.bin"
private noncomputable def ep1010111001_1 : Blocks := edgeBlocks% "full/vectors/1010111001-E-0001.bin"
noncomputable def ep1010111001 : Blocks := (Blocks.join ep1010111001_0 ep1010111001_1)
private theorem idp1010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101011100.list =
    C ((2:ℤ)^280) * horner X vp1010111001.list + horner X ep1010111001.list := by
  exact edge_identity (B := (2:ℤ)^447) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010111001 : Branch 1 (-5567761639/16000000 : ℚ) vp101011100 := by
  apply branch_checked idp1010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-5567761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5575761639/8000000 : ℚ) by norm_num]
  exact coverp1010111001
theorem coverp101011100 : Covers (-5567761639/16000000 : ℚ) vp101011100 := join_branches bp1010111000 bp1010111001
private noncomputable def vp10101110_0 : Blocks := edgeBlocks% "full/vectors/10101110-V-0000.bin"
private noncomputable def vp10101110_1 : Blocks := edgeBlocks% "full/vectors/10101110-V-0001.bin"
private noncomputable def vp10101110_2 : Blocks := edgeBlocks% "full/vectors/10101110-V-0002.bin"
private noncomputable def vp10101110_3 : Blocks := edgeBlocks% "full/vectors/10101110-V-0003.bin"
noncomputable def vp10101110 : Blocks := (Blocks.join (Blocks.join vp10101110_0 vp10101110_1) (Blocks.join vp10101110_2 vp10101110_3))
private theorem bp101011100 : Branch 0 (-5567761639/32000000 : ℚ) vp10101110 := by
  apply branch_left_normalized (c:=vp101011100) (k:=0) (m:=233) (by decide +kernel)
  rw [show 2*(-5567761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5567761639/16000000 : ℚ) by norm_num]
  exact coverp101011100
private noncomputable def ep101011101_0 : Blocks := edgeBlocks% "full/vectors/101011101-E-0000.bin"
private noncomputable def ep101011101_1 : Blocks := edgeBlocks% "full/vectors/101011101-E-0001.bin"
private noncomputable def ep101011101_2 : Blocks := edgeBlocks% "full/vectors/101011101-E-0002.bin"
private noncomputable def ep101011101_3 : Blocks := edgeBlocks% "full/vectors/101011101-E-0003.bin"
noncomputable def ep101011101 : Blocks := (Blocks.join (Blocks.join ep101011101_0 ep101011101_1) (Blocks.join ep101011101_2 ep101011101_3))
private theorem idp101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10101110.list =
    C ((2:ℤ)^534) * horner X vp101011101.list + horner X ep101011101.list := by
  exact edge_identity (B := (2:ℤ)^766) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101011101 : Branch 1 (-5567761639/32000000 : ℚ) vp10101110 := by
  apply branch_checked idp101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-5567761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5583761639/16000000 : ℚ) by norm_num]
  exact coverp101011101
theorem coverp10101110 : Covers (-5567761639/32000000 : ℚ) vp10101110 := join_branches bp101011100 bp101011101
private noncomputable def vp1010111_0 : Blocks := edgeBlocks% "full/vectors/1010111-V-0000.bin"
private noncomputable def vp1010111_1 : Blocks := edgeBlocks% "full/vectors/1010111-V-0001.bin"
private noncomputable def vp1010111_2 : Blocks := edgeBlocks% "full/vectors/1010111-V-0002.bin"
private noncomputable def vp1010111_3 : Blocks := edgeBlocks% "full/vectors/1010111-V-0003.bin"
private noncomputable def vp1010111_4 : Blocks := edgeBlocks% "full/vectors/1010111-V-0004.bin"
private noncomputable def vp1010111_5 : Blocks := edgeBlocks% "full/vectors/1010111-V-0005.bin"
private noncomputable def vp1010111_6 : Blocks := edgeBlocks% "full/vectors/1010111-V-0006.bin"
noncomputable def vp1010111 : Blocks := (Blocks.join (Blocks.join vp1010111_0 (Blocks.join vp1010111_1 vp1010111_2)) (Blocks.join (Blocks.join vp1010111_3 vp1010111_4) (Blocks.join vp1010111_5 vp1010111_6)))
private theorem bp10101110 : Branch 0 (-5567761639/64000000 : ℚ) vp1010111 := by
  apply branch_left_normalized (c:=vp10101110) (k:=0) (m:=441) (by decide +kernel)
  rw [show 2*(-5567761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5567761639/32000000 : ℚ) by norm_num]
  exact coverp10101110
private noncomputable def ep10101111_0 : Blocks := edgeBlocks% "full/vectors/10101111-E-0000.bin"
private noncomputable def ep10101111_1 : Blocks := edgeBlocks% "full/vectors/10101111-E-0001.bin"
private noncomputable def ep10101111_2 : Blocks := edgeBlocks% "full/vectors/10101111-E-0002.bin"
private noncomputable def ep10101111_3 : Blocks := edgeBlocks% "full/vectors/10101111-E-0003.bin"
private noncomputable def ep10101111_4 : Blocks := edgeBlocks% "full/vectors/10101111-E-0004.bin"
private noncomputable def ep10101111_5 : Blocks := edgeBlocks% "full/vectors/10101111-E-0005.bin"
private noncomputable def ep10101111_6 : Blocks := edgeBlocks% "full/vectors/10101111-E-0006.bin"
noncomputable def ep10101111 : Blocks := (Blocks.join (Blocks.join ep10101111_0 (Blocks.join ep10101111_1 ep10101111_2)) (Blocks.join (Blocks.join ep10101111_3 ep10101111_4) (Blocks.join ep10101111_5 ep10101111_6)))
private theorem idp10101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010111.list =
    C ((2:ℤ)^1041) * horner X vp10101111.list + horner X ep10101111.list := by
  exact edge_identity (B := (2:ℤ)^1404) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10101111 : Branch 1 (-5567761639/64000000 : ℚ) vp1010111 := by
  apply branch_checked idp10101111 (by positivity) (by decide +kernel)
  rw [show 2*(-5567761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5599761639/32000000 : ℚ) by norm_num]
  exact coverp10101111
theorem coverp1010111 : Covers (-5567761639/64000000 : ℚ) vp1010111 := join_branches bp10101110 bp10101111
private noncomputable def vp1010110111_0 : Blocks := edgeBlocks% "full/vectors/1010110111-V-0000.bin"
noncomputable def vp1010110111 : Blocks := vp1010110111_0
theorem coverp1010110111 : Covers (-5559761639/8000000 : ℚ) vp1010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp1010110110_0 : Blocks := edgeBlocks% "full/vectors/1010110110-V-0000.bin"
noncomputable def vp1010110110 : Blocks := vp1010110110_0
theorem coverp1010110110 : Covers (-5551761639/8000000 : ℚ) vp1010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp101011011_0 : Blocks := edgeBlocks% "full/vectors/101011011-V-0000.bin"
private noncomputable def vp101011011_1 : Blocks := edgeBlocks% "full/vectors/101011011-V-0001.bin"
noncomputable def vp101011011 : Blocks := (Blocks.join vp101011011_0 vp101011011_1)
private theorem bp1010110110 : Branch 0 (-5551761639/16000000 : ℚ) vp101011011 := by
  apply branch_left_normalized (c:=vp1010110110) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-5551761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5551761639/8000000 : ℚ) by norm_num]
  exact coverp1010110110
private noncomputable def ep1010110111_0 : Blocks := edgeBlocks% "full/vectors/1010110111-E-0000.bin"
private noncomputable def ep1010110111_1 : Blocks := edgeBlocks% "full/vectors/1010110111-E-0001.bin"
noncomputable def ep1010110111 : Blocks := (Blocks.join ep1010110111_0 ep1010110111_1)
private theorem idp1010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101011011.list =
    C ((2:ℤ)^280) * horner X vp1010110111.list + horner X ep1010110111.list := by
  exact edge_identity (B := (2:ℤ)^448) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010110111 : Branch 1 (-5551761639/16000000 : ℚ) vp101011011 := by
  apply branch_checked idp1010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-5551761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5559761639/8000000 : ℚ) by norm_num]
  exact coverp1010110111
theorem coverp101011011 : Covers (-5551761639/16000000 : ℚ) vp101011011 := join_branches bp1010110110 bp1010110111
private noncomputable def vp1010110101_0 : Blocks := edgeBlocks% "full/vectors/1010110101-V-0000.bin"
noncomputable def vp1010110101 : Blocks := vp1010110101_0
theorem coverp1010110101 : Covers (-5543761639/8000000 : ℚ) vp1010110101 := cover_leaf (by decide +kernel)
private noncomputable def vp1010110100_0 : Blocks := edgeBlocks% "full/vectors/1010110100-V-0000.bin"
noncomputable def vp1010110100 : Blocks := vp1010110100_0
theorem coverp1010110100 : Covers (-5535761639/8000000 : ℚ) vp1010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp101011010_0 : Blocks := edgeBlocks% "full/vectors/101011010-V-0000.bin"
private noncomputable def vp101011010_1 : Blocks := edgeBlocks% "full/vectors/101011010-V-0001.bin"
noncomputable def vp101011010 : Blocks := (Blocks.join vp101011010_0 vp101011010_1)
private theorem bp1010110100 : Branch 0 (-5535761639/16000000 : ℚ) vp101011010 := by
  apply branch_left_normalized (c:=vp1010110100) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-5535761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5535761639/8000000 : ℚ) by norm_num]
  exact coverp1010110100
private noncomputable def ep1010110101_0 : Blocks := edgeBlocks% "full/vectors/1010110101-E-0000.bin"
private noncomputable def ep1010110101_1 : Blocks := edgeBlocks% "full/vectors/1010110101-E-0001.bin"
noncomputable def ep1010110101 : Blocks := (Blocks.join ep1010110101_0 ep1010110101_1)
private theorem idp1010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101011010.list =
    C ((2:ℤ)^281) * horner X vp1010110101.list + horner X ep1010110101.list := by
  exact edge_identity (B := (2:ℤ)^449) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010110101 : Branch 1 (-5535761639/16000000 : ℚ) vp101011010 := by
  apply branch_checked idp1010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-5535761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5543761639/8000000 : ℚ) by norm_num]
  exact coverp1010110101
theorem coverp101011010 : Covers (-5535761639/16000000 : ℚ) vp101011010 := join_branches bp1010110100 bp1010110101
private noncomputable def vp10101101_0 : Blocks := edgeBlocks% "full/vectors/10101101-V-0000.bin"
private noncomputable def vp10101101_1 : Blocks := edgeBlocks% "full/vectors/10101101-V-0001.bin"
private noncomputable def vp10101101_2 : Blocks := edgeBlocks% "full/vectors/10101101-V-0002.bin"
private noncomputable def vp10101101_3 : Blocks := edgeBlocks% "full/vectors/10101101-V-0003.bin"
noncomputable def vp10101101 : Blocks := (Blocks.join (Blocks.join vp10101101_0 vp10101101_1) (Blocks.join vp10101101_2 vp10101101_3))
private theorem bp101011010 : Branch 0 (-5535761639/32000000 : ℚ) vp10101101 := by
  apply branch_left_normalized (c:=vp101011010) (k:=0) (m:=234) (by decide +kernel)
  rw [show 2*(-5535761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5535761639/16000000 : ℚ) by norm_num]
  exact coverp101011010
private noncomputable def ep101011011_0 : Blocks := edgeBlocks% "full/vectors/101011011-E-0000.bin"
private noncomputable def ep101011011_1 : Blocks := edgeBlocks% "full/vectors/101011011-E-0001.bin"
private noncomputable def ep101011011_2 : Blocks := edgeBlocks% "full/vectors/101011011-E-0002.bin"
private noncomputable def ep101011011_3 : Blocks := edgeBlocks% "full/vectors/101011011-E-0003.bin"
noncomputable def ep101011011 : Blocks := (Blocks.join (Blocks.join ep101011011_0 ep101011011_1) (Blocks.join ep101011011_2 ep101011011_3))
private theorem idp101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10101101.list =
    C ((2:ℤ)^536) * horner X vp101011011.list + horner X ep101011011.list := by
  exact edge_identity (B := (2:ℤ)^769) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101011011 : Branch 1 (-5535761639/32000000 : ℚ) vp10101101 := by
  apply branch_checked idp101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-5535761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5551761639/16000000 : ℚ) by norm_num]
  exact coverp101011011
theorem coverp10101101 : Covers (-5535761639/32000000 : ℚ) vp10101101 := join_branches bp101011010 bp101011011
private noncomputable def vp1010110011_0 : Blocks := edgeBlocks% "full/vectors/1010110011-V-0000.bin"
noncomputable def vp1010110011 : Blocks := vp1010110011_0
theorem coverp1010110011 : Covers (-5527761639/8000000 : ℚ) vp1010110011 := cover_leaf (by decide +kernel)
private noncomputable def vp1010110010_0 : Blocks := edgeBlocks% "full/vectors/1010110010-V-0000.bin"
noncomputable def vp1010110010 : Blocks := vp1010110010_0
theorem coverp1010110010 : Covers (-5519761639/8000000 : ℚ) vp1010110010 := cover_leaf (by decide +kernel)
private noncomputable def vp101011001_0 : Blocks := edgeBlocks% "full/vectors/101011001-V-0000.bin"
private noncomputable def vp101011001_1 : Blocks := edgeBlocks% "full/vectors/101011001-V-0001.bin"
noncomputable def vp101011001 : Blocks := (Blocks.join vp101011001_0 vp101011001_1)
private theorem bp1010110010 : Branch 0 (-5519761639/16000000 : ℚ) vp101011001 := by
  apply branch_left_normalized (c:=vp1010110010) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-5519761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5519761639/8000000 : ℚ) by norm_num]
  exact coverp1010110010
private noncomputable def ep1010110011_0 : Blocks := edgeBlocks% "full/vectors/1010110011-E-0000.bin"
private noncomputable def ep1010110011_1 : Blocks := edgeBlocks% "full/vectors/1010110011-E-0001.bin"
noncomputable def ep1010110011 : Blocks := (Blocks.join ep1010110011_0 ep1010110011_1)
private theorem idp1010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101011001.list =
    C ((2:ℤ)^281) * horner X vp1010110011.list + horner X ep1010110011.list := by
  exact edge_identity (B := (2:ℤ)^448) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010110011 : Branch 1 (-5519761639/16000000 : ℚ) vp101011001 := by
  apply branch_checked idp1010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-5519761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5527761639/8000000 : ℚ) by norm_num]
  exact coverp1010110011
theorem coverp101011001 : Covers (-5519761639/16000000 : ℚ) vp101011001 := join_branches bp1010110010 bp1010110011
private noncomputable def vp1010110001_0 : Blocks := edgeBlocks% "full/vectors/1010110001-V-0000.bin"
noncomputable def vp1010110001 : Blocks := vp1010110001_0
theorem coverp1010110001 : Covers (-5511761639/8000000 : ℚ) vp1010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp1010110000_0 : Blocks := edgeBlocks% "full/vectors/1010110000-V-0000.bin"
noncomputable def vp1010110000 : Blocks := vp1010110000_0
theorem coverp1010110000 : Covers (-5503761639/8000000 : ℚ) vp1010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp101011000_0 : Blocks := edgeBlocks% "full/vectors/101011000-V-0000.bin"
private noncomputable def vp101011000_1 : Blocks := edgeBlocks% "full/vectors/101011000-V-0001.bin"
noncomputable def vp101011000 : Blocks := (Blocks.join vp101011000_0 vp101011000_1)
private theorem bp1010110000 : Branch 0 (-5503761639/16000000 : ℚ) vp101011000 := by
  apply branch_left_normalized (c:=vp1010110000) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-5503761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5503761639/8000000 : ℚ) by norm_num]
  exact coverp1010110000
private noncomputable def ep1010110001_0 : Blocks := edgeBlocks% "full/vectors/1010110001-E-0000.bin"
private noncomputable def ep1010110001_1 : Blocks := edgeBlocks% "full/vectors/1010110001-E-0001.bin"
noncomputable def ep1010110001 : Blocks := (Blocks.join ep1010110001_0 ep1010110001_1)
private theorem idp1010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101011000.list =
    C ((2:ℤ)^281) * horner X vp1010110001.list + horner X ep1010110001.list := by
  exact edge_identity (B := (2:ℤ)^449) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010110001 : Branch 1 (-5503761639/16000000 : ℚ) vp101011000 := by
  apply branch_checked idp1010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-5503761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5511761639/8000000 : ℚ) by norm_num]
  exact coverp1010110001
theorem coverp101011000 : Covers (-5503761639/16000000 : ℚ) vp101011000 := join_branches bp1010110000 bp1010110001
private noncomputable def vp10101100_0 : Blocks := edgeBlocks% "full/vectors/10101100-V-0000.bin"
private noncomputable def vp10101100_1 : Blocks := edgeBlocks% "full/vectors/10101100-V-0001.bin"
private noncomputable def vp10101100_2 : Blocks := edgeBlocks% "full/vectors/10101100-V-0002.bin"
private noncomputable def vp10101100_3 : Blocks := edgeBlocks% "full/vectors/10101100-V-0003.bin"
noncomputable def vp10101100 : Blocks := (Blocks.join (Blocks.join vp10101100_0 vp10101100_1) (Blocks.join vp10101100_2 vp10101100_3))
private theorem bp101011000 : Branch 0 (-5503761639/32000000 : ℚ) vp10101100 := by
  apply branch_left_normalized (c:=vp101011000) (k:=0) (m:=234) (by decide +kernel)
  rw [show 2*(-5503761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5503761639/16000000 : ℚ) by norm_num]
  exact coverp101011000
private noncomputable def ep101011001_0 : Blocks := edgeBlocks% "full/vectors/101011001-E-0000.bin"
private noncomputable def ep101011001_1 : Blocks := edgeBlocks% "full/vectors/101011001-E-0001.bin"
private noncomputable def ep101011001_2 : Blocks := edgeBlocks% "full/vectors/101011001-E-0002.bin"
private noncomputable def ep101011001_3 : Blocks := edgeBlocks% "full/vectors/101011001-E-0003.bin"
noncomputable def ep101011001 : Blocks := (Blocks.join (Blocks.join ep101011001_0 ep101011001_1) (Blocks.join ep101011001_2 ep101011001_3))
private theorem idp101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10101100.list =
    C ((2:ℤ)^538) * horner X vp101011001.list + horner X ep101011001.list := by
  exact edge_identity (B := (2:ℤ)^771) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101011001 : Branch 1 (-5503761639/32000000 : ℚ) vp10101100 := by
  apply branch_checked idp101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-5503761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5519761639/16000000 : ℚ) by norm_num]
  exact coverp101011001
theorem coverp10101100 : Covers (-5503761639/32000000 : ℚ) vp10101100 := join_branches bp101011000 bp101011001
private noncomputable def vp1010110_0 : Blocks := edgeBlocks% "full/vectors/1010110-V-0000.bin"
private noncomputable def vp1010110_1 : Blocks := edgeBlocks% "full/vectors/1010110-V-0001.bin"
private noncomputable def vp1010110_2 : Blocks := edgeBlocks% "full/vectors/1010110-V-0002.bin"
private noncomputable def vp1010110_3 : Blocks := edgeBlocks% "full/vectors/1010110-V-0003.bin"
private noncomputable def vp1010110_4 : Blocks := edgeBlocks% "full/vectors/1010110-V-0004.bin"
private noncomputable def vp1010110_5 : Blocks := edgeBlocks% "full/vectors/1010110-V-0005.bin"
private noncomputable def vp1010110_6 : Blocks := edgeBlocks% "full/vectors/1010110-V-0006.bin"
noncomputable def vp1010110 : Blocks := (Blocks.join (Blocks.join vp1010110_0 (Blocks.join vp1010110_1 vp1010110_2)) (Blocks.join (Blocks.join vp1010110_3 vp1010110_4) (Blocks.join vp1010110_5 vp1010110_6)))
private theorem bp10101100 : Branch 0 (-5503761639/64000000 : ℚ) vp1010110 := by
  apply branch_left_normalized (c:=vp10101100) (k:=0) (m:=444) (by decide +kernel)
  rw [show 2*(-5503761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5503761639/32000000 : ℚ) by norm_num]
  exact coverp10101100
private noncomputable def ep10101101_0 : Blocks := edgeBlocks% "full/vectors/10101101-E-0000.bin"
private noncomputable def ep10101101_1 : Blocks := edgeBlocks% "full/vectors/10101101-E-0001.bin"
private noncomputable def ep10101101_2 : Blocks := edgeBlocks% "full/vectors/10101101-E-0002.bin"
private noncomputable def ep10101101_3 : Blocks := edgeBlocks% "full/vectors/10101101-E-0003.bin"
private noncomputable def ep10101101_4 : Blocks := edgeBlocks% "full/vectors/10101101-E-0004.bin"
private noncomputable def ep10101101_5 : Blocks := edgeBlocks% "full/vectors/10101101-E-0005.bin"
private noncomputable def ep10101101_6 : Blocks := edgeBlocks% "full/vectors/10101101-E-0006.bin"
noncomputable def ep10101101 : Blocks := (Blocks.join (Blocks.join ep10101101_0 (Blocks.join ep10101101_1 ep10101101_2)) (Blocks.join (Blocks.join ep10101101_3 ep10101101_4) (Blocks.join ep10101101_5 ep10101101_6)))
private theorem idp10101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010110.list =
    C ((2:ℤ)^1046) * horner X vp10101101.list + horner X ep10101101.list := by
  exact edge_identity (B := (2:ℤ)^1411) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10101101 : Branch 1 (-5503761639/64000000 : ℚ) vp1010110 := by
  apply branch_checked idp10101101 (by positivity) (by decide +kernel)
  rw [show 2*(-5503761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5535761639/32000000 : ℚ) by norm_num]
  exact coverp10101101
theorem coverp1010110 : Covers (-5503761639/64000000 : ℚ) vp1010110 := join_branches bp10101100 bp10101101
private noncomputable def vp101011_0 : Blocks := edgeBlocks% "full/vectors/101011-V-0000.bin"
private noncomputable def vp101011_1 : Blocks := edgeBlocks% "full/vectors/101011-V-0001.bin"
private noncomputable def vp101011_2 : Blocks := edgeBlocks% "full/vectors/101011-V-0002.bin"
private noncomputable def vp101011_3 : Blocks := edgeBlocks% "full/vectors/101011-V-0003.bin"
private noncomputable def vp101011_4 : Blocks := edgeBlocks% "full/vectors/101011-V-0004.bin"
private noncomputable def vp101011_5 : Blocks := edgeBlocks% "full/vectors/101011-V-0005.bin"
private noncomputable def vp101011_6 : Blocks := edgeBlocks% "full/vectors/101011-V-0006.bin"
private noncomputable def vp101011_7 : Blocks := edgeBlocks% "full/vectors/101011-V-0007.bin"
private noncomputable def vp101011_8 : Blocks := edgeBlocks% "full/vectors/101011-V-0008.bin"
private noncomputable def vp101011_9 : Blocks := edgeBlocks% "full/vectors/101011-V-0009.bin"
private noncomputable def vp101011_10 : Blocks := edgeBlocks% "full/vectors/101011-V-0010.bin"
private noncomputable def vp101011_11 : Blocks := edgeBlocks% "full/vectors/101011-V-0011.bin"
private noncomputable def vp101011_12 : Blocks := edgeBlocks% "full/vectors/101011-V-0012.bin"
private noncomputable def vp101011_13 : Blocks := edgeBlocks% "full/vectors/101011-V-0013.bin"
noncomputable def vp101011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp101011_0 (Blocks.join vp101011_1 vp101011_2)) (Blocks.join (Blocks.join vp101011_3 vp101011_4) (Blocks.join vp101011_5 vp101011_6))) (Blocks.join (Blocks.join vp101011_7 (Blocks.join vp101011_8 vp101011_9)) (Blocks.join (Blocks.join vp101011_10 vp101011_11) (Blocks.join vp101011_12 vp101011_13))))
private theorem bp1010110 : Branch 0 (-5503761639/128000000 : ℚ) vp101011 := by
  apply branch_left_normalized (c:=vp1010110) (k:=0) (m:=860) (by decide +kernel)
  rw [show 2*(-5503761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-5503761639/64000000 : ℚ) by norm_num]
  exact coverp1010110
private noncomputable def ep1010111_0 : Blocks := edgeBlocks% "full/vectors/1010111-E-0000.bin"
private noncomputable def ep1010111_1 : Blocks := edgeBlocks% "full/vectors/1010111-E-0001.bin"
private noncomputable def ep1010111_2 : Blocks := edgeBlocks% "full/vectors/1010111-E-0002.bin"
private noncomputable def ep1010111_3 : Blocks := edgeBlocks% "full/vectors/1010111-E-0003.bin"
private noncomputable def ep1010111_4 : Blocks := edgeBlocks% "full/vectors/1010111-E-0004.bin"
private noncomputable def ep1010111_5 : Blocks := edgeBlocks% "full/vectors/1010111-E-0005.bin"
private noncomputable def ep1010111_6 : Blocks := edgeBlocks% "full/vectors/1010111-E-0006.bin"
private noncomputable def ep1010111_7 : Blocks := edgeBlocks% "full/vectors/1010111-E-0007.bin"
private noncomputable def ep1010111_8 : Blocks := edgeBlocks% "full/vectors/1010111-E-0008.bin"
private noncomputable def ep1010111_9 : Blocks := edgeBlocks% "full/vectors/1010111-E-0009.bin"
private noncomputable def ep1010111_10 : Blocks := edgeBlocks% "full/vectors/1010111-E-0010.bin"
private noncomputable def ep1010111_11 : Blocks := edgeBlocks% "full/vectors/1010111-E-0011.bin"
private noncomputable def ep1010111_12 : Blocks := edgeBlocks% "full/vectors/1010111-E-0012.bin"
private noncomputable def ep1010111_13 : Blocks := edgeBlocks% "full/vectors/1010111-E-0013.bin"
noncomputable def ep1010111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1010111_0 (Blocks.join ep1010111_1 ep1010111_2)) (Blocks.join (Blocks.join ep1010111_3 ep1010111_4) (Blocks.join ep1010111_5 ep1010111_6))) (Blocks.join (Blocks.join ep1010111_7 (Blocks.join ep1010111_8 ep1010111_9)) (Blocks.join (Blocks.join ep1010111_10 ep1010111_11) (Blocks.join ep1010111_12 ep1010111_13))))
private theorem idp1010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101011.list =
    C ((2:ℤ)^2046) * horner X vp1010111.list + horner X ep1010111.list := by
  exact edge_identity (B := (2:ℤ)^2670) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010111 : Branch 1 (-5503761639/128000000 : ℚ) vp101011 := by
  apply branch_checked idp1010111 (by positivity) (by decide +kernel)
  rw [show 2*(-5503761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-5567761639/64000000 : ℚ) by norm_num]
  exact coverp1010111
theorem coverp101011 : Covers (-5503761639/128000000 : ℚ) vp101011 := join_branches bp1010110 bp1010111
private noncomputable def vp1010101111_0 : Blocks := edgeBlocks% "full/vectors/1010101111-V-0000.bin"
noncomputable def vp1010101111 : Blocks := vp1010101111_0
theorem coverp1010101111 : Covers (-5495761639/8000000 : ℚ) vp1010101111 := cover_leaf (by decide +kernel)
private noncomputable def vp1010101110_0 : Blocks := edgeBlocks% "full/vectors/1010101110-V-0000.bin"
noncomputable def vp1010101110 : Blocks := vp1010101110_0
theorem coverp1010101110 : Covers (-5487761639/8000000 : ℚ) vp1010101110 := cover_leaf (by decide +kernel)
private noncomputable def vp101010111_0 : Blocks := edgeBlocks% "full/vectors/101010111-V-0000.bin"
private noncomputable def vp101010111_1 : Blocks := edgeBlocks% "full/vectors/101010111-V-0001.bin"
noncomputable def vp101010111 : Blocks := (Blocks.join vp101010111_0 vp101010111_1)
private theorem bp1010101110 : Branch 0 (-5487761639/16000000 : ℚ) vp101010111 := by
  apply branch_left_normalized (c:=vp1010101110) (k:=0) (m:=127) (by decide +kernel)
  rw [show 2*(-5487761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5487761639/8000000 : ℚ) by norm_num]
  exact coverp1010101110
private noncomputable def ep1010101111_0 : Blocks := edgeBlocks% "full/vectors/1010101111-E-0000.bin"
private noncomputable def ep1010101111_1 : Blocks := edgeBlocks% "full/vectors/1010101111-E-0001.bin"
noncomputable def ep1010101111 : Blocks := (Blocks.join ep1010101111_0 ep1010101111_1)
private theorem idp1010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101010111.list =
    C ((2:ℤ)^281) * horner X vp1010101111.list + horner X ep1010101111.list := by
  exact edge_identity (B := (2:ℤ)^449) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010101111 : Branch 1 (-5487761639/16000000 : ℚ) vp101010111 := by
  apply branch_checked idp1010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-5487761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5495761639/8000000 : ℚ) by norm_num]
  exact coverp1010101111
theorem coverp101010111 : Covers (-5487761639/16000000 : ℚ) vp101010111 := join_branches bp1010101110 bp1010101111
private noncomputable def vp1010101101_0 : Blocks := edgeBlocks% "full/vectors/1010101101-V-0000.bin"
private noncomputable def vp1010101101_1 : Blocks := edgeBlocks% "full/vectors/1010101101-V-0001.bin"
noncomputable def vp1010101101 : Blocks := (Blocks.join vp1010101101_0 vp1010101101_1)
theorem coverp1010101101 : Covers (-5479761639/8000000 : ℚ) vp1010101101 := cover_leaf (by decide +kernel)
private noncomputable def vp1010101100_0 : Blocks := edgeBlocks% "full/vectors/1010101100-V-0000.bin"
private noncomputable def vp1010101100_1 : Blocks := edgeBlocks% "full/vectors/1010101100-V-0001.bin"
noncomputable def vp1010101100 : Blocks := (Blocks.join vp1010101100_0 vp1010101100_1)
theorem coverp1010101100 : Covers (-5471761639/8000000 : ℚ) vp1010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp101010110_0 : Blocks := edgeBlocks% "full/vectors/101010110-V-0000.bin"
private noncomputable def vp101010110_1 : Blocks := edgeBlocks% "full/vectors/101010110-V-0001.bin"
noncomputable def vp101010110 : Blocks := (Blocks.join vp101010110_0 vp101010110_1)
private theorem bp1010101100 : Branch 0 (-5471761639/16000000 : ℚ) vp101010110 := by
  apply branch_left_normalized (c:=vp1010101100) (k:=0) (m:=128) (by decide +kernel)
  rw [show 2*(-5471761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5471761639/8000000 : ℚ) by norm_num]
  exact coverp1010101100
private noncomputable def ep1010101101_0 : Blocks := edgeBlocks% "full/vectors/1010101101-E-0000.bin"
private noncomputable def ep1010101101_1 : Blocks := edgeBlocks% "full/vectors/1010101101-E-0001.bin"
noncomputable def ep1010101101 : Blocks := (Blocks.join ep1010101101_0 ep1010101101_1)
private theorem idp1010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101010110.list =
    C ((2:ℤ)^282) * horner X vp1010101101.list + horner X ep1010101101.list := by
  exact edge_identity (B := (2:ℤ)^450) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010101101 : Branch 1 (-5471761639/16000000 : ℚ) vp101010110 := by
  apply branch_checked idp1010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-5471761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5479761639/8000000 : ℚ) by norm_num]
  exact coverp1010101101
theorem coverp101010110 : Covers (-5471761639/16000000 : ℚ) vp101010110 := join_branches bp1010101100 bp1010101101
private noncomputable def vp10101011_0 : Blocks := edgeBlocks% "full/vectors/10101011-V-0000.bin"
private noncomputable def vp10101011_1 : Blocks := edgeBlocks% "full/vectors/10101011-V-0001.bin"
private noncomputable def vp10101011_2 : Blocks := edgeBlocks% "full/vectors/10101011-V-0002.bin"
private noncomputable def vp10101011_3 : Blocks := edgeBlocks% "full/vectors/10101011-V-0003.bin"
noncomputable def vp10101011 : Blocks := (Blocks.join (Blocks.join vp10101011_0 vp10101011_1) (Blocks.join vp10101011_2 vp10101011_3))
private theorem bp101010110 : Branch 0 (-5471761639/32000000 : ℚ) vp10101011 := by
  apply branch_left_normalized (c:=vp101010110) (k:=0) (m:=235) (by decide +kernel)
  rw [show 2*(-5471761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5471761639/16000000 : ℚ) by norm_num]
  exact coverp101010110
private noncomputable def ep101010111_0 : Blocks := edgeBlocks% "full/vectors/101010111-E-0000.bin"
private noncomputable def ep101010111_1 : Blocks := edgeBlocks% "full/vectors/101010111-E-0001.bin"
private noncomputable def ep101010111_2 : Blocks := edgeBlocks% "full/vectors/101010111-E-0002.bin"
private noncomputable def ep101010111_3 : Blocks := edgeBlocks% "full/vectors/101010111-E-0003.bin"
noncomputable def ep101010111 : Blocks := (Blocks.join (Blocks.join ep101010111_0 ep101010111_1) (Blocks.join ep101010111_2 ep101010111_3))
private theorem idp101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10101011.list =
    C ((2:ℤ)^539) * horner X vp101010111.list + horner X ep101010111.list := by
  exact edge_identity (B := (2:ℤ)^773) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101010111 : Branch 1 (-5471761639/32000000 : ℚ) vp10101011 := by
  apply branch_checked idp101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-5471761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5487761639/16000000 : ℚ) by norm_num]
  exact coverp101010111
theorem coverp10101011 : Covers (-5471761639/32000000 : ℚ) vp10101011 := join_branches bp101010110 bp101010111
private noncomputable def vp1010101011_0 : Blocks := edgeBlocks% "full/vectors/1010101011-V-0000.bin"
private noncomputable def vp1010101011_1 : Blocks := edgeBlocks% "full/vectors/1010101011-V-0001.bin"
noncomputable def vp1010101011 : Blocks := (Blocks.join vp1010101011_0 vp1010101011_1)
theorem coverp1010101011 : Covers (-5463761639/8000000 : ℚ) vp1010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp1010101010_0 : Blocks := edgeBlocks% "full/vectors/1010101010-V-0000.bin"
private noncomputable def vp1010101010_1 : Blocks := edgeBlocks% "full/vectors/1010101010-V-0001.bin"
noncomputable def vp1010101010 : Blocks := (Blocks.join vp1010101010_0 vp1010101010_1)
theorem coverp1010101010 : Covers (-5455761639/8000000 : ℚ) vp1010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp101010101_0 : Blocks := edgeBlocks% "full/vectors/101010101-V-0000.bin"
private noncomputable def vp101010101_1 : Blocks := edgeBlocks% "full/vectors/101010101-V-0001.bin"
noncomputable def vp101010101 : Blocks := (Blocks.join vp101010101_0 vp101010101_1)
private theorem bp1010101010 : Branch 0 (-5455761639/16000000 : ℚ) vp101010101 := by
  apply branch_left_normalized (c:=vp1010101010) (k:=0) (m:=128) (by decide +kernel)
  rw [show 2*(-5455761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5455761639/8000000 : ℚ) by norm_num]
  exact coverp1010101010
private noncomputable def ep1010101011_0 : Blocks := edgeBlocks% "full/vectors/1010101011-E-0000.bin"
private noncomputable def ep1010101011_1 : Blocks := edgeBlocks% "full/vectors/1010101011-E-0001.bin"
noncomputable def ep1010101011 : Blocks := (Blocks.join ep1010101011_0 ep1010101011_1)
private theorem idp1010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101010101.list =
    C ((2:ℤ)^282) * horner X vp1010101011.list + horner X ep1010101011.list := by
  exact edge_identity (B := (2:ℤ)^451) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010101011 : Branch 1 (-5455761639/16000000 : ℚ) vp101010101 := by
  apply branch_checked idp1010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-5455761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5463761639/8000000 : ℚ) by norm_num]
  exact coverp1010101011
theorem coverp101010101 : Covers (-5455761639/16000000 : ℚ) vp101010101 := join_branches bp1010101010 bp1010101011
private noncomputable def vp1010101001_0 : Blocks := edgeBlocks% "full/vectors/1010101001-V-0000.bin"
private noncomputable def vp1010101001_1 : Blocks := edgeBlocks% "full/vectors/1010101001-V-0001.bin"
noncomputable def vp1010101001 : Blocks := (Blocks.join vp1010101001_0 vp1010101001_1)
theorem coverp1010101001 : Covers (-5447761639/8000000 : ℚ) vp1010101001 := cover_leaf (by decide +kernel)
private noncomputable def vp1010101000_0 : Blocks := edgeBlocks% "full/vectors/1010101000-V-0000.bin"
private noncomputable def vp1010101000_1 : Blocks := edgeBlocks% "full/vectors/1010101000-V-0001.bin"
noncomputable def vp1010101000 : Blocks := (Blocks.join vp1010101000_0 vp1010101000_1)
theorem coverp1010101000 : Covers (-5439761639/8000000 : ℚ) vp1010101000 := cover_leaf (by decide +kernel)
private noncomputable def vp101010100_0 : Blocks := edgeBlocks% "full/vectors/101010100-V-0000.bin"
private noncomputable def vp101010100_1 : Blocks := edgeBlocks% "full/vectors/101010100-V-0001.bin"
noncomputable def vp101010100 : Blocks := (Blocks.join vp101010100_0 vp101010100_1)
private theorem bp1010101000 : Branch 0 (-5439761639/16000000 : ℚ) vp101010100 := by
  apply branch_left_normalized (c:=vp1010101000) (k:=0) (m:=128) (by decide +kernel)
  rw [show 2*(-5439761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5439761639/8000000 : ℚ) by norm_num]
  exact coverp1010101000
private noncomputable def ep1010101001_0 : Blocks := edgeBlocks% "full/vectors/1010101001-E-0000.bin"
private noncomputable def ep1010101001_1 : Blocks := edgeBlocks% "full/vectors/1010101001-E-0001.bin"
noncomputable def ep1010101001 : Blocks := (Blocks.join ep1010101001_0 ep1010101001_1)
private theorem idp1010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101010100.list =
    C ((2:ℤ)^282) * horner X vp1010101001.list + horner X ep1010101001.list := by
  exact edge_identity (B := (2:ℤ)^450) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010101001 : Branch 1 (-5439761639/16000000 : ℚ) vp101010100 := by
  apply branch_checked idp1010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-5439761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5447761639/8000000 : ℚ) by norm_num]
  exact coverp1010101001
theorem coverp101010100 : Covers (-5439761639/16000000 : ℚ) vp101010100 := join_branches bp1010101000 bp1010101001
private noncomputable def vp10101010_0 : Blocks := edgeBlocks% "full/vectors/10101010-V-0000.bin"
private noncomputable def vp10101010_1 : Blocks := edgeBlocks% "full/vectors/10101010-V-0001.bin"
private noncomputable def vp10101010_2 : Blocks := edgeBlocks% "full/vectors/10101010-V-0002.bin"
private noncomputable def vp10101010_3 : Blocks := edgeBlocks% "full/vectors/10101010-V-0003.bin"
noncomputable def vp10101010 : Blocks := (Blocks.join (Blocks.join vp10101010_0 vp10101010_1) (Blocks.join vp10101010_2 vp10101010_3))
private theorem bp101010100 : Branch 0 (-5439761639/32000000 : ℚ) vp10101010 := by
  apply branch_left_normalized (c:=vp101010100) (k:=0) (m:=235) (by decide +kernel)
  rw [show 2*(-5439761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5439761639/16000000 : ℚ) by norm_num]
  exact coverp101010100
private noncomputable def ep101010101_0 : Blocks := edgeBlocks% "full/vectors/101010101-E-0000.bin"
private noncomputable def ep101010101_1 : Blocks := edgeBlocks% "full/vectors/101010101-E-0001.bin"
private noncomputable def ep101010101_2 : Blocks := edgeBlocks% "full/vectors/101010101-E-0002.bin"
private noncomputable def ep101010101_3 : Blocks := edgeBlocks% "full/vectors/101010101-E-0003.bin"
noncomputable def ep101010101 : Blocks := (Blocks.join (Blocks.join ep101010101_0 ep101010101_1) (Blocks.join ep101010101_2 ep101010101_3))
private theorem idp101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10101010.list =
    C ((2:ℤ)^540) * horner X vp101010101.list + horner X ep101010101.list := by
  exact edge_identity (B := (2:ℤ)^775) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101010101 : Branch 1 (-5439761639/32000000 : ℚ) vp10101010 := by
  apply branch_checked idp101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-5439761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5455761639/16000000 : ℚ) by norm_num]
  exact coverp101010101
theorem coverp10101010 : Covers (-5439761639/32000000 : ℚ) vp10101010 := join_branches bp101010100 bp101010101
private noncomputable def vp1010101_0 : Blocks := edgeBlocks% "full/vectors/1010101-V-0000.bin"
private noncomputable def vp1010101_1 : Blocks := edgeBlocks% "full/vectors/1010101-V-0001.bin"
private noncomputable def vp1010101_2 : Blocks := edgeBlocks% "full/vectors/1010101-V-0002.bin"
private noncomputable def vp1010101_3 : Blocks := edgeBlocks% "full/vectors/1010101-V-0003.bin"
private noncomputable def vp1010101_4 : Blocks := edgeBlocks% "full/vectors/1010101-V-0004.bin"
private noncomputable def vp1010101_5 : Blocks := edgeBlocks% "full/vectors/1010101-V-0005.bin"
private noncomputable def vp1010101_6 : Blocks := edgeBlocks% "full/vectors/1010101-V-0006.bin"
noncomputable def vp1010101 : Blocks := (Blocks.join (Blocks.join vp1010101_0 (Blocks.join vp1010101_1 vp1010101_2)) (Blocks.join (Blocks.join vp1010101_3 vp1010101_4) (Blocks.join vp1010101_5 vp1010101_6)))
private theorem bp10101010 : Branch 0 (-5439761639/64000000 : ℚ) vp1010101 := by
  apply branch_left_normalized (c:=vp10101010) (k:=0) (m:=447) (by decide +kernel)
  rw [show 2*(-5439761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5439761639/32000000 : ℚ) by norm_num]
  exact coverp10101010
private noncomputable def ep10101011_0 : Blocks := edgeBlocks% "full/vectors/10101011-E-0000.bin"
private noncomputable def ep10101011_1 : Blocks := edgeBlocks% "full/vectors/10101011-E-0001.bin"
private noncomputable def ep10101011_2 : Blocks := edgeBlocks% "full/vectors/10101011-E-0002.bin"
private noncomputable def ep10101011_3 : Blocks := edgeBlocks% "full/vectors/10101011-E-0003.bin"
private noncomputable def ep10101011_4 : Blocks := edgeBlocks% "full/vectors/10101011-E-0004.bin"
private noncomputable def ep10101011_5 : Blocks := edgeBlocks% "full/vectors/10101011-E-0005.bin"
private noncomputable def ep10101011_6 : Blocks := edgeBlocks% "full/vectors/10101011-E-0006.bin"
noncomputable def ep10101011 : Blocks := (Blocks.join (Blocks.join ep10101011_0 (Blocks.join ep10101011_1 ep10101011_2)) (Blocks.join (Blocks.join ep10101011_3 ep10101011_4) (Blocks.join ep10101011_5 ep10101011_6)))
private theorem idp10101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010101.list =
    C ((2:ℤ)^1051) * horner X vp10101011.list + horner X ep10101011.list := by
  exact edge_identity (B := (2:ℤ)^1418) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10101011 : Branch 1 (-5439761639/64000000 : ℚ) vp1010101 := by
  apply branch_checked idp10101011 (by positivity) (by decide +kernel)
  rw [show 2*(-5439761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5471761639/32000000 : ℚ) by norm_num]
  exact coverp10101011
theorem coverp1010101 : Covers (-5439761639/64000000 : ℚ) vp1010101 := join_branches bp10101010 bp10101011
private noncomputable def vp1010100111_0 : Blocks := edgeBlocks% "full/vectors/1010100111-V-0000.bin"
private noncomputable def vp1010100111_1 : Blocks := edgeBlocks% "full/vectors/1010100111-V-0001.bin"
noncomputable def vp1010100111 : Blocks := (Blocks.join vp1010100111_0 vp1010100111_1)
theorem coverp1010100111 : Covers (-5431761639/8000000 : ℚ) vp1010100111 := cover_leaf (by decide +kernel)
private noncomputable def vp1010100110_0 : Blocks := edgeBlocks% "full/vectors/1010100110-V-0000.bin"
private noncomputable def vp1010100110_1 : Blocks := edgeBlocks% "full/vectors/1010100110-V-0001.bin"
noncomputable def vp1010100110 : Blocks := (Blocks.join vp1010100110_0 vp1010100110_1)
theorem coverp1010100110 : Covers (-5423761639/8000000 : ℚ) vp1010100110 := cover_leaf (by decide +kernel)
private noncomputable def vp101010011_0 : Blocks := edgeBlocks% "full/vectors/101010011-V-0000.bin"
private noncomputable def vp101010011_1 : Blocks := edgeBlocks% "full/vectors/101010011-V-0001.bin"
noncomputable def vp101010011 : Blocks := (Blocks.join vp101010011_0 vp101010011_1)
private theorem bp1010100110 : Branch 0 (-5423761639/16000000 : ℚ) vp101010011 := by
  apply branch_left_normalized (c:=vp1010100110) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-5423761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5423761639/8000000 : ℚ) by norm_num]
  exact coverp1010100110
private noncomputable def ep1010100111_0 : Blocks := edgeBlocks% "full/vectors/1010100111-E-0000.bin"
private noncomputable def ep1010100111_1 : Blocks := edgeBlocks% "full/vectors/1010100111-E-0001.bin"
noncomputable def ep1010100111 : Blocks := (Blocks.join ep1010100111_0 ep1010100111_1)
private theorem idp1010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101010011.list =
    C ((2:ℤ)^282) * horner X vp1010100111.list + horner X ep1010100111.list := by
  exact edge_identity (B := (2:ℤ)^450) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010100111 : Branch 1 (-5423761639/16000000 : ℚ) vp101010011 := by
  apply branch_checked idp1010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-5423761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5431761639/8000000 : ℚ) by norm_num]
  exact coverp1010100111
theorem coverp101010011 : Covers (-5423761639/16000000 : ℚ) vp101010011 := join_branches bp1010100110 bp1010100111
private noncomputable def vp1010100101_0 : Blocks := edgeBlocks% "full/vectors/1010100101-V-0000.bin"
private noncomputable def vp1010100101_1 : Blocks := edgeBlocks% "full/vectors/1010100101-V-0001.bin"
noncomputable def vp1010100101 : Blocks := (Blocks.join vp1010100101_0 vp1010100101_1)
theorem coverp1010100101 : Covers (-5415761639/8000000 : ℚ) vp1010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp1010100100_0 : Blocks := edgeBlocks% "full/vectors/1010100100-V-0000.bin"
private noncomputable def vp1010100100_1 : Blocks := edgeBlocks% "full/vectors/1010100100-V-0001.bin"
noncomputable def vp1010100100 : Blocks := (Blocks.join vp1010100100_0 vp1010100100_1)
theorem coverp1010100100 : Covers (-5407761639/8000000 : ℚ) vp1010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp101010010_0 : Blocks := edgeBlocks% "full/vectors/101010010-V-0000.bin"
private noncomputable def vp101010010_1 : Blocks := edgeBlocks% "full/vectors/101010010-V-0001.bin"
noncomputable def vp101010010 : Blocks := (Blocks.join vp101010010_0 vp101010010_1)
private theorem bp1010100100 : Branch 0 (-5407761639/16000000 : ℚ) vp101010010 := by
  apply branch_left_normalized (c:=vp1010100100) (k:=0) (m:=128) (by decide +kernel)
  rw [show 2*(-5407761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5407761639/8000000 : ℚ) by norm_num]
  exact coverp1010100100
private noncomputable def ep1010100101_0 : Blocks := edgeBlocks% "full/vectors/1010100101-E-0000.bin"
private noncomputable def ep1010100101_1 : Blocks := edgeBlocks% "full/vectors/1010100101-E-0001.bin"
noncomputable def ep1010100101 : Blocks := (Blocks.join ep1010100101_0 ep1010100101_1)
private theorem idp1010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101010010.list =
    C ((2:ℤ)^283) * horner X vp1010100101.list + horner X ep1010100101.list := by
  exact edge_identity (B := (2:ℤ)^452) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010100101 : Branch 1 (-5407761639/16000000 : ℚ) vp101010010 := by
  apply branch_checked idp1010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-5407761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5415761639/8000000 : ℚ) by norm_num]
  exact coverp1010100101
theorem coverp101010010 : Covers (-5407761639/16000000 : ℚ) vp101010010 := join_branches bp1010100100 bp1010100101
private noncomputable def vp10101001_0 : Blocks := edgeBlocks% "full/vectors/10101001-V-0000.bin"
private noncomputable def vp10101001_1 : Blocks := edgeBlocks% "full/vectors/10101001-V-0001.bin"
private noncomputable def vp10101001_2 : Blocks := edgeBlocks% "full/vectors/10101001-V-0002.bin"
private noncomputable def vp10101001_3 : Blocks := edgeBlocks% "full/vectors/10101001-V-0003.bin"
noncomputable def vp10101001 : Blocks := (Blocks.join (Blocks.join vp10101001_0 vp10101001_1) (Blocks.join vp10101001_2 vp10101001_3))
private theorem bp101010010 : Branch 0 (-5407761639/32000000 : ℚ) vp10101001 := by
  apply branch_left_normalized (c:=vp101010010) (k:=0) (m:=236) (by decide +kernel)
  rw [show 2*(-5407761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5407761639/16000000 : ℚ) by norm_num]
  exact coverp101010010
private noncomputable def ep101010011_0 : Blocks := edgeBlocks% "full/vectors/101010011-E-0000.bin"
private noncomputable def ep101010011_1 : Blocks := edgeBlocks% "full/vectors/101010011-E-0001.bin"
private noncomputable def ep101010011_2 : Blocks := edgeBlocks% "full/vectors/101010011-E-0002.bin"
private noncomputable def ep101010011_3 : Blocks := edgeBlocks% "full/vectors/101010011-E-0003.bin"
noncomputable def ep101010011 : Blocks := (Blocks.join (Blocks.join ep101010011_0 ep101010011_1) (Blocks.join ep101010011_2 ep101010011_3))
private theorem idp101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10101001.list =
    C ((2:ℤ)^541) * horner X vp101010011.list + horner X ep101010011.list := by
  exact edge_identity (B := (2:ℤ)^776) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101010011 : Branch 1 (-5407761639/32000000 : ℚ) vp10101001 := by
  apply branch_checked idp101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-5407761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5423761639/16000000 : ℚ) by norm_num]
  exact coverp101010011
theorem coverp10101001 : Covers (-5407761639/32000000 : ℚ) vp10101001 := join_branches bp101010010 bp101010011
private noncomputable def vp1010100011_0 : Blocks := edgeBlocks% "full/vectors/1010100011-V-0000.bin"
private noncomputable def vp1010100011_1 : Blocks := edgeBlocks% "full/vectors/1010100011-V-0001.bin"
noncomputable def vp1010100011 : Blocks := (Blocks.join vp1010100011_0 vp1010100011_1)
theorem coverp1010100011 : Covers (-5399761639/8000000 : ℚ) vp1010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp1010100010_0 : Blocks := edgeBlocks% "full/vectors/1010100010-V-0000.bin"
private noncomputable def vp1010100010_1 : Blocks := edgeBlocks% "full/vectors/1010100010-V-0001.bin"
noncomputable def vp1010100010 : Blocks := (Blocks.join vp1010100010_0 vp1010100010_1)
theorem coverp1010100010 : Covers (-5391761639/8000000 : ℚ) vp1010100010 := cover_leaf (by decide +kernel)
private noncomputable def vp101010001_0 : Blocks := edgeBlocks% "full/vectors/101010001-V-0000.bin"
private noncomputable def vp101010001_1 : Blocks := edgeBlocks% "full/vectors/101010001-V-0001.bin"
noncomputable def vp101010001 : Blocks := (Blocks.join vp101010001_0 vp101010001_1)
private theorem bp1010100010 : Branch 0 (-5391761639/16000000 : ℚ) vp101010001 := by
  apply branch_left_normalized (c:=vp1010100010) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-5391761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5391761639/8000000 : ℚ) by norm_num]
  exact coverp1010100010
private noncomputable def ep1010100011_0 : Blocks := edgeBlocks% "full/vectors/1010100011-E-0000.bin"
private noncomputable def ep1010100011_1 : Blocks := edgeBlocks% "full/vectors/1010100011-E-0001.bin"
noncomputable def ep1010100011 : Blocks := (Blocks.join ep1010100011_0 ep1010100011_1)
private theorem idp1010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101010001.list =
    C ((2:ℤ)^283) * horner X vp1010100011.list + horner X ep1010100011.list := by
  exact edge_identity (B := (2:ℤ)^452) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010100011 : Branch 1 (-5391761639/16000000 : ℚ) vp101010001 := by
  apply branch_checked idp1010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-5391761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5399761639/8000000 : ℚ) by norm_num]
  exact coverp1010100011
theorem coverp101010001 : Covers (-5391761639/16000000 : ℚ) vp101010001 := join_branches bp1010100010 bp1010100011
private noncomputable def vp1010100001_0 : Blocks := edgeBlocks% "full/vectors/1010100001-V-0000.bin"
private noncomputable def vp1010100001_1 : Blocks := edgeBlocks% "full/vectors/1010100001-V-0001.bin"
noncomputable def vp1010100001 : Blocks := (Blocks.join vp1010100001_0 vp1010100001_1)
theorem coverp1010100001 : Covers (-5383761639/8000000 : ℚ) vp1010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp1010100000_0 : Blocks := edgeBlocks% "full/vectors/1010100000-V-0000.bin"
private noncomputable def vp1010100000_1 : Blocks := edgeBlocks% "full/vectors/1010100000-V-0001.bin"
noncomputable def vp1010100000 : Blocks := (Blocks.join vp1010100000_0 vp1010100000_1)
theorem coverp1010100000 : Covers (-5375761639/8000000 : ℚ) vp1010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp101010000_0 : Blocks := edgeBlocks% "full/vectors/101010000-V-0000.bin"
private noncomputable def vp101010000_1 : Blocks := edgeBlocks% "full/vectors/101010000-V-0001.bin"
noncomputable def vp101010000 : Blocks := (Blocks.join vp101010000_0 vp101010000_1)
private theorem bp1010100000 : Branch 0 (-5375761639/16000000 : ℚ) vp101010000 := by
  apply branch_left_normalized (c:=vp1010100000) (k:=0) (m:=128) (by decide +kernel)
  rw [show 2*(-5375761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5375761639/8000000 : ℚ) by norm_num]
  exact coverp1010100000
private noncomputable def ep1010100001_0 : Blocks := edgeBlocks% "full/vectors/1010100001-E-0000.bin"
private noncomputable def ep1010100001_1 : Blocks := edgeBlocks% "full/vectors/1010100001-E-0001.bin"
noncomputable def ep1010100001 : Blocks := (Blocks.join ep1010100001_0 ep1010100001_1)
private theorem idp1010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101010000.list =
    C ((2:ℤ)^284) * horner X vp1010100001.list + horner X ep1010100001.list := by
  exact edge_identity (B := (2:ℤ)^453) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010100001 : Branch 1 (-5375761639/16000000 : ℚ) vp101010000 := by
  apply branch_checked idp1010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-5375761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5383761639/8000000 : ℚ) by norm_num]
  exact coverp1010100001
theorem coverp101010000 : Covers (-5375761639/16000000 : ℚ) vp101010000 := join_branches bp1010100000 bp1010100001
private noncomputable def vp10101000_0 : Blocks := edgeBlocks% "full/vectors/10101000-V-0000.bin"
private noncomputable def vp10101000_1 : Blocks := edgeBlocks% "full/vectors/10101000-V-0001.bin"
private noncomputable def vp10101000_2 : Blocks := edgeBlocks% "full/vectors/10101000-V-0002.bin"
private noncomputable def vp10101000_3 : Blocks := edgeBlocks% "full/vectors/10101000-V-0003.bin"
noncomputable def vp10101000 : Blocks := (Blocks.join (Blocks.join vp10101000_0 vp10101000_1) (Blocks.join vp10101000_2 vp10101000_3))
private theorem bp101010000 : Branch 0 (-5375761639/32000000 : ℚ) vp10101000 := by
  apply branch_left_normalized (c:=vp101010000) (k:=0) (m:=237) (by decide +kernel)
  rw [show 2*(-5375761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5375761639/16000000 : ℚ) by norm_num]
  exact coverp101010000
private noncomputable def ep101010001_0 : Blocks := edgeBlocks% "full/vectors/101010001-E-0000.bin"
private noncomputable def ep101010001_1 : Blocks := edgeBlocks% "full/vectors/101010001-E-0001.bin"
private noncomputable def ep101010001_2 : Blocks := edgeBlocks% "full/vectors/101010001-E-0002.bin"
private noncomputable def ep101010001_3 : Blocks := edgeBlocks% "full/vectors/101010001-E-0003.bin"
noncomputable def ep101010001 : Blocks := (Blocks.join (Blocks.join ep101010001_0 ep101010001_1) (Blocks.join ep101010001_2 ep101010001_3))
private theorem idp101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10101000.list =
    C ((2:ℤ)^542) * horner X vp101010001.list + horner X ep101010001.list := by
  exact edge_identity (B := (2:ℤ)^778) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101010001 : Branch 1 (-5375761639/32000000 : ℚ) vp10101000 := by
  apply branch_checked idp101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-5375761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5391761639/16000000 : ℚ) by norm_num]
  exact coverp101010001
theorem coverp10101000 : Covers (-5375761639/32000000 : ℚ) vp10101000 := join_branches bp101010000 bp101010001
private noncomputable def vp1010100_0 : Blocks := edgeBlocks% "full/vectors/1010100-V-0000.bin"
private noncomputable def vp1010100_1 : Blocks := edgeBlocks% "full/vectors/1010100-V-0001.bin"
private noncomputable def vp1010100_2 : Blocks := edgeBlocks% "full/vectors/1010100-V-0002.bin"
private noncomputable def vp1010100_3 : Blocks := edgeBlocks% "full/vectors/1010100-V-0003.bin"
private noncomputable def vp1010100_4 : Blocks := edgeBlocks% "full/vectors/1010100-V-0004.bin"
private noncomputable def vp1010100_5 : Blocks := edgeBlocks% "full/vectors/1010100-V-0005.bin"
private noncomputable def vp1010100_6 : Blocks := edgeBlocks% "full/vectors/1010100-V-0006.bin"
noncomputable def vp1010100 : Blocks := (Blocks.join (Blocks.join vp1010100_0 (Blocks.join vp1010100_1 vp1010100_2)) (Blocks.join (Blocks.join vp1010100_3 vp1010100_4) (Blocks.join vp1010100_5 vp1010100_6)))
private theorem bp10101000 : Branch 0 (-5375761639/64000000 : ℚ) vp1010100 := by
  apply branch_left_normalized (c:=vp10101000) (k:=0) (m:=449) (by decide +kernel)
  rw [show 2*(-5375761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5375761639/32000000 : ℚ) by norm_num]
  exact coverp10101000
private noncomputable def ep10101001_0 : Blocks := edgeBlocks% "full/vectors/10101001-E-0000.bin"
private noncomputable def ep10101001_1 : Blocks := edgeBlocks% "full/vectors/10101001-E-0001.bin"
private noncomputable def ep10101001_2 : Blocks := edgeBlocks% "full/vectors/10101001-E-0002.bin"
private noncomputable def ep10101001_3 : Blocks := edgeBlocks% "full/vectors/10101001-E-0003.bin"
private noncomputable def ep10101001_4 : Blocks := edgeBlocks% "full/vectors/10101001-E-0004.bin"
private noncomputable def ep10101001_5 : Blocks := edgeBlocks% "full/vectors/10101001-E-0005.bin"
private noncomputable def ep10101001_6 : Blocks := edgeBlocks% "full/vectors/10101001-E-0006.bin"
noncomputable def ep10101001 : Blocks := (Blocks.join (Blocks.join ep10101001_0 (Blocks.join ep10101001_1 ep10101001_2)) (Blocks.join (Blocks.join ep10101001_3 ep10101001_4) (Blocks.join ep10101001_5 ep10101001_6)))
private theorem idp10101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010100.list =
    C ((2:ℤ)^1055) * horner X vp10101001.list + horner X ep10101001.list := by
  exact edge_identity (B := (2:ℤ)^1426) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10101001 : Branch 1 (-5375761639/64000000 : ℚ) vp1010100 := by
  apply branch_checked idp10101001 (by positivity) (by decide +kernel)
  rw [show 2*(-5375761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5407761639/32000000 : ℚ) by norm_num]
  exact coverp10101001
theorem coverp1010100 : Covers (-5375761639/64000000 : ℚ) vp1010100 := join_branches bp10101000 bp10101001
private noncomputable def vp101010_0 : Blocks := edgeBlocks% "full/vectors/101010-V-0000.bin"
private noncomputable def vp101010_1 : Blocks := edgeBlocks% "full/vectors/101010-V-0001.bin"
private noncomputable def vp101010_2 : Blocks := edgeBlocks% "full/vectors/101010-V-0002.bin"
private noncomputable def vp101010_3 : Blocks := edgeBlocks% "full/vectors/101010-V-0003.bin"
private noncomputable def vp101010_4 : Blocks := edgeBlocks% "full/vectors/101010-V-0004.bin"
private noncomputable def vp101010_5 : Blocks := edgeBlocks% "full/vectors/101010-V-0005.bin"
private noncomputable def vp101010_6 : Blocks := edgeBlocks% "full/vectors/101010-V-0006.bin"
private noncomputable def vp101010_7 : Blocks := edgeBlocks% "full/vectors/101010-V-0007.bin"
private noncomputable def vp101010_8 : Blocks := edgeBlocks% "full/vectors/101010-V-0008.bin"
private noncomputable def vp101010_9 : Blocks := edgeBlocks% "full/vectors/101010-V-0009.bin"
private noncomputable def vp101010_10 : Blocks := edgeBlocks% "full/vectors/101010-V-0010.bin"
private noncomputable def vp101010_11 : Blocks := edgeBlocks% "full/vectors/101010-V-0011.bin"
private noncomputable def vp101010_12 : Blocks := edgeBlocks% "full/vectors/101010-V-0012.bin"
private noncomputable def vp101010_13 : Blocks := edgeBlocks% "full/vectors/101010-V-0013.bin"
noncomputable def vp101010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp101010_0 (Blocks.join vp101010_1 vp101010_2)) (Blocks.join (Blocks.join vp101010_3 vp101010_4) (Blocks.join vp101010_5 vp101010_6))) (Blocks.join (Blocks.join vp101010_7 (Blocks.join vp101010_8 vp101010_9)) (Blocks.join (Blocks.join vp101010_10 vp101010_11) (Blocks.join vp101010_12 vp101010_13))))
private theorem bp1010100 : Branch 0 (-5375761639/128000000 : ℚ) vp101010 := by
  apply branch_left_normalized (c:=vp1010100) (k:=0) (m:=870) (by decide +kernel)
  rw [show 2*(-5375761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-5375761639/64000000 : ℚ) by norm_num]
  exact coverp1010100
private noncomputable def ep1010101_0 : Blocks := edgeBlocks% "full/vectors/1010101-E-0000.bin"
private noncomputable def ep1010101_1 : Blocks := edgeBlocks% "full/vectors/1010101-E-0001.bin"
private noncomputable def ep1010101_2 : Blocks := edgeBlocks% "full/vectors/1010101-E-0002.bin"
private noncomputable def ep1010101_3 : Blocks := edgeBlocks% "full/vectors/1010101-E-0003.bin"
private noncomputable def ep1010101_4 : Blocks := edgeBlocks% "full/vectors/1010101-E-0004.bin"
private noncomputable def ep1010101_5 : Blocks := edgeBlocks% "full/vectors/1010101-E-0005.bin"
private noncomputable def ep1010101_6 : Blocks := edgeBlocks% "full/vectors/1010101-E-0006.bin"
private noncomputable def ep1010101_7 : Blocks := edgeBlocks% "full/vectors/1010101-E-0007.bin"
private noncomputable def ep1010101_8 : Blocks := edgeBlocks% "full/vectors/1010101-E-0008.bin"
private noncomputable def ep1010101_9 : Blocks := edgeBlocks% "full/vectors/1010101-E-0009.bin"
private noncomputable def ep1010101_10 : Blocks := edgeBlocks% "full/vectors/1010101-E-0010.bin"
private noncomputable def ep1010101_11 : Blocks := edgeBlocks% "full/vectors/1010101-E-0011.bin"
private noncomputable def ep1010101_12 : Blocks := edgeBlocks% "full/vectors/1010101-E-0012.bin"
private noncomputable def ep1010101_13 : Blocks := edgeBlocks% "full/vectors/1010101-E-0013.bin"
noncomputable def ep1010101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1010101_0 (Blocks.join ep1010101_1 ep1010101_2)) (Blocks.join (Blocks.join ep1010101_3 ep1010101_4) (Blocks.join ep1010101_5 ep1010101_6))) (Blocks.join (Blocks.join ep1010101_7 (Blocks.join ep1010101_8 ep1010101_9)) (Blocks.join (Blocks.join ep1010101_10 ep1010101_11) (Blocks.join ep1010101_12 ep1010101_13))))
private theorem idp1010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101010.list =
    C ((2:ℤ)^2065) * horner X vp1010101.list + horner X ep1010101.list := by
  exact edge_identity (B := (2:ℤ)^2700) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010101 : Branch 1 (-5375761639/128000000 : ℚ) vp101010 := by
  apply branch_checked idp1010101 (by positivity) (by decide +kernel)
  rw [show 2*(-5375761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-5439761639/64000000 : ℚ) by norm_num]
  exact coverp1010101
theorem coverp101010 : Covers (-5375761639/128000000 : ℚ) vp101010 := join_branches bp1010100 bp1010101
private noncomputable def vp10101_0 : Blocks := edgeBlocks% "full/vectors/10101-V-0000.bin"
private noncomputable def vp10101_1 : Blocks := edgeBlocks% "full/vectors/10101-V-0001.bin"
private noncomputable def vp10101_2 : Blocks := edgeBlocks% "full/vectors/10101-V-0002.bin"
private noncomputable def vp10101_3 : Blocks := edgeBlocks% "full/vectors/10101-V-0003.bin"
private noncomputable def vp10101_4 : Blocks := edgeBlocks% "full/vectors/10101-V-0004.bin"
private noncomputable def vp10101_5 : Blocks := edgeBlocks% "full/vectors/10101-V-0005.bin"
private noncomputable def vp10101_6 : Blocks := edgeBlocks% "full/vectors/10101-V-0006.bin"
private noncomputable def vp10101_7 : Blocks := edgeBlocks% "full/vectors/10101-V-0007.bin"
private noncomputable def vp10101_8 : Blocks := edgeBlocks% "full/vectors/10101-V-0008.bin"
private noncomputable def vp10101_9 : Blocks := edgeBlocks% "full/vectors/10101-V-0009.bin"
private noncomputable def vp10101_10 : Blocks := edgeBlocks% "full/vectors/10101-V-0010.bin"
private noncomputable def vp10101_11 : Blocks := edgeBlocks% "full/vectors/10101-V-0011.bin"
private noncomputable def vp10101_12 : Blocks := edgeBlocks% "full/vectors/10101-V-0012.bin"
private noncomputable def vp10101_13 : Blocks := edgeBlocks% "full/vectors/10101-V-0013.bin"
private noncomputable def vp10101_14 : Blocks := edgeBlocks% "full/vectors/10101-V-0014.bin"
private noncomputable def vp10101_15 : Blocks := edgeBlocks% "full/vectors/10101-V-0015.bin"
private noncomputable def vp10101_16 : Blocks := edgeBlocks% "full/vectors/10101-V-0016.bin"
private noncomputable def vp10101_17 : Blocks := edgeBlocks% "full/vectors/10101-V-0017.bin"
private noncomputable def vp10101_18 : Blocks := edgeBlocks% "full/vectors/10101-V-0018.bin"
private noncomputable def vp10101_19 : Blocks := edgeBlocks% "full/vectors/10101-V-0019.bin"
private noncomputable def vp10101_20 : Blocks := edgeBlocks% "full/vectors/10101-V-0020.bin"
private noncomputable def vp10101_21 : Blocks := edgeBlocks% "full/vectors/10101-V-0021.bin"
private noncomputable def vp10101_22 : Blocks := edgeBlocks% "full/vectors/10101-V-0022.bin"
private noncomputable def vp10101_23 : Blocks := edgeBlocks% "full/vectors/10101-V-0023.bin"
private noncomputable def vp10101_24 : Blocks := edgeBlocks% "full/vectors/10101-V-0024.bin"
private noncomputable def vp10101_25 : Blocks := edgeBlocks% "full/vectors/10101-V-0025.bin"
noncomputable def vp10101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp10101_0 (Blocks.join vp10101_1 vp10101_2)) (Blocks.join vp10101_3 (Blocks.join vp10101_4 vp10101_5))) (Blocks.join (Blocks.join vp10101_6 (Blocks.join vp10101_7 vp10101_8)) (Blocks.join (Blocks.join vp10101_9 vp10101_10) (Blocks.join vp10101_11 vp10101_12)))) (Blocks.join (Blocks.join (Blocks.join vp10101_13 (Blocks.join vp10101_14 vp10101_15)) (Blocks.join vp10101_16 (Blocks.join vp10101_17 vp10101_18))) (Blocks.join (Blocks.join vp10101_19 (Blocks.join vp10101_20 vp10101_21)) (Blocks.join (Blocks.join vp10101_22 vp10101_23) (Blocks.join vp10101_24 vp10101_25)))))
private theorem bp101010 : Branch 0 (-5375761639/256000000 : ℚ) vp10101 := by
  apply branch_left_normalized (c:=vp101010) (k:=0) (m:=1695) (by decide +kernel)
  rw [show 2*(-5375761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-5375761639/128000000 : ℚ) by norm_num]
  exact coverp101010
private noncomputable def ep101011_0 : Blocks := edgeBlocks% "full/vectors/101011-E-0000.bin"
private noncomputable def ep101011_1 : Blocks := edgeBlocks% "full/vectors/101011-E-0001.bin"
private noncomputable def ep101011_2 : Blocks := edgeBlocks% "full/vectors/101011-E-0002.bin"
private noncomputable def ep101011_3 : Blocks := edgeBlocks% "full/vectors/101011-E-0003.bin"
private noncomputable def ep101011_4 : Blocks := edgeBlocks% "full/vectors/101011-E-0004.bin"
private noncomputable def ep101011_5 : Blocks := edgeBlocks% "full/vectors/101011-E-0005.bin"
private noncomputable def ep101011_6 : Blocks := edgeBlocks% "full/vectors/101011-E-0006.bin"
private noncomputable def ep101011_7 : Blocks := edgeBlocks% "full/vectors/101011-E-0007.bin"
private noncomputable def ep101011_8 : Blocks := edgeBlocks% "full/vectors/101011-E-0008.bin"
private noncomputable def ep101011_9 : Blocks := edgeBlocks% "full/vectors/101011-E-0009.bin"
private noncomputable def ep101011_10 : Blocks := edgeBlocks% "full/vectors/101011-E-0010.bin"
private noncomputable def ep101011_11 : Blocks := edgeBlocks% "full/vectors/101011-E-0011.bin"
private noncomputable def ep101011_12 : Blocks := edgeBlocks% "full/vectors/101011-E-0012.bin"
private noncomputable def ep101011_13 : Blocks := edgeBlocks% "full/vectors/101011-E-0013.bin"
private noncomputable def ep101011_14 : Blocks := edgeBlocks% "full/vectors/101011-E-0014.bin"
private noncomputable def ep101011_15 : Blocks := edgeBlocks% "full/vectors/101011-E-0015.bin"
private noncomputable def ep101011_16 : Blocks := edgeBlocks% "full/vectors/101011-E-0016.bin"
private noncomputable def ep101011_17 : Blocks := edgeBlocks% "full/vectors/101011-E-0017.bin"
private noncomputable def ep101011_18 : Blocks := edgeBlocks% "full/vectors/101011-E-0018.bin"
private noncomputable def ep101011_19 : Blocks := edgeBlocks% "full/vectors/101011-E-0019.bin"
private noncomputable def ep101011_20 : Blocks := edgeBlocks% "full/vectors/101011-E-0020.bin"
private noncomputable def ep101011_21 : Blocks := edgeBlocks% "full/vectors/101011-E-0021.bin"
private noncomputable def ep101011_22 : Blocks := edgeBlocks% "full/vectors/101011-E-0022.bin"
private noncomputable def ep101011_23 : Blocks := edgeBlocks% "full/vectors/101011-E-0023.bin"
private noncomputable def ep101011_24 : Blocks := edgeBlocks% "full/vectors/101011-E-0024.bin"
private noncomputable def ep101011_25 : Blocks := edgeBlocks% "full/vectors/101011-E-0025.bin"
noncomputable def ep101011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep101011_0 (Blocks.join ep101011_1 ep101011_2)) (Blocks.join ep101011_3 (Blocks.join ep101011_4 ep101011_5))) (Blocks.join (Blocks.join ep101011_6 (Blocks.join ep101011_7 ep101011_8)) (Blocks.join (Blocks.join ep101011_9 ep101011_10) (Blocks.join ep101011_11 ep101011_12)))) (Blocks.join (Blocks.join (Blocks.join ep101011_13 (Blocks.join ep101011_14 ep101011_15)) (Blocks.join ep101011_16 (Blocks.join ep101011_17 ep101011_18))) (Blocks.join (Blocks.join ep101011_19 (Blocks.join ep101011_20 ep101011_21)) (Blocks.join (Blocks.join ep101011_22 ep101011_23) (Blocks.join ep101011_24 ep101011_25)))))
private def ptsp101011 : List ℤ := [((2:ℤ)^3658+0),((2:ℤ)^3658+1)]
private theorem boundp101011 : 2^vp10101.size*absSum vp10101.list + ((2:ℤ)^4018*absSum vp101011.list+absSum ep101011.list) < (2:ℤ)^5170 := by decide +kernel
private theorem pointp101011_0 : fastHom 1 ((2:ℤ)^3658+0) vp10101 = ((2:ℤ)^4018)*vp101011.subst ((2:ℤ)^3658+0)+ep101011.subst ((2:ℤ)^3658+0) := by decide +kernel
private theorem pointp101011_1 : fastHom 1 ((2:ℤ)^3658+1) vp10101 = ((2:ℤ)^4018)*vp101011.subst ((2:ℤ)^3658+1)+ep101011.subst ((2:ℤ)^3658+1) := by decide +kernel
private theorem checkp101011 (x:ℤ) (hx:x ∈ ptsp101011) : fastHom 1 x vp10101 = ((2:ℤ)^4018)*vp101011.subst x+ep101011.subst x := by
  simp only [ptsp101011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp101011_0
  · exact pointp101011_1
private theorem idp101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10101.list =
    C ((2:ℤ)^4018) * horner X vp101011.list + horner X ep101011.list := by
  apply edge_identity (B := (2:ℤ)^5170) (by decide) (by positivity) (by positivity) boundp101011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp101011 (by decide +kernel)
  · have h : ptsp101011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp101011.trans_le (by decide +kernel)
  · exact checkp101011
private theorem bp101011 : Branch 1 (-5375761639/256000000 : ℚ) vp10101 := by
  apply branch_checked idp101011 (by positivity) (by decide +kernel)
  rw [show 2*(-5375761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-5503761639/128000000 : ℚ) by norm_num]
  exact coverp101011
theorem coverp10101 : Covers (-5375761639/256000000 : ℚ) vp10101 := join_branches bp101010 bp101011
private noncomputable def vp1010011111_0 : Blocks := edgeBlocks% "full/vectors/1010011111-V-0000.bin"
private noncomputable def vp1010011111_1 : Blocks := edgeBlocks% "full/vectors/1010011111-V-0001.bin"
noncomputable def vp1010011111 : Blocks := (Blocks.join vp1010011111_0 vp1010011111_1)
theorem coverp1010011111 : Covers (-5367761639/8000000 : ℚ) vp1010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp1010011110_0 : Blocks := edgeBlocks% "full/vectors/1010011110-V-0000.bin"
private noncomputable def vp1010011110_1 : Blocks := edgeBlocks% "full/vectors/1010011110-V-0001.bin"
noncomputable def vp1010011110 : Blocks := (Blocks.join vp1010011110_0 vp1010011110_1)
theorem coverp1010011110 : Covers (-5359761639/8000000 : ℚ) vp1010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp101001111_0 : Blocks := edgeBlocks% "full/vectors/101001111-V-0000.bin"
private noncomputable def vp101001111_1 : Blocks := edgeBlocks% "full/vectors/101001111-V-0001.bin"
noncomputable def vp101001111 : Blocks := (Blocks.join vp101001111_0 vp101001111_1)
private theorem bp1010011110 : Branch 0 (-5359761639/16000000 : ℚ) vp101001111 := by
  apply branch_left_normalized (c:=vp1010011110) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-5359761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5359761639/8000000 : ℚ) by norm_num]
  exact coverp1010011110
private noncomputable def ep1010011111_0 : Blocks := edgeBlocks% "full/vectors/1010011111-E-0000.bin"
private noncomputable def ep1010011111_1 : Blocks := edgeBlocks% "full/vectors/1010011111-E-0001.bin"
noncomputable def ep1010011111 : Blocks := (Blocks.join ep1010011111_0 ep1010011111_1)
private theorem idp1010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101001111.list =
    C ((2:ℤ)^283) * horner X vp1010011111.list + horner X ep1010011111.list := by
  exact edge_identity (B := (2:ℤ)^453) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010011111 : Branch 1 (-5359761639/16000000 : ℚ) vp101001111 := by
  apply branch_checked idp1010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-5359761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5367761639/8000000 : ℚ) by norm_num]
  exact coverp1010011111
theorem coverp101001111 : Covers (-5359761639/16000000 : ℚ) vp101001111 := join_branches bp1010011110 bp1010011111
private noncomputable def vp1010011101_0 : Blocks := edgeBlocks% "full/vectors/1010011101-V-0000.bin"
private noncomputable def vp1010011101_1 : Blocks := edgeBlocks% "full/vectors/1010011101-V-0001.bin"
noncomputable def vp1010011101 : Blocks := (Blocks.join vp1010011101_0 vp1010011101_1)
theorem coverp1010011101 : Covers (-5351761639/8000000 : ℚ) vp1010011101 := cover_leaf (by decide +kernel)
private noncomputable def vp10100111001_0 : Blocks := edgeBlocks% "full/vectors/10100111001-V-0000.bin"
noncomputable def vp10100111001 : Blocks := vp10100111001_0
theorem coverp10100111001 : Covers (-5347761639/4000000 : ℚ) vp10100111001 := cover_leaf (by decide +kernel)
private noncomputable def vp10100111000_0 : Blocks := edgeBlocks% "full/vectors/10100111000-V-0000.bin"
noncomputable def vp10100111000 : Blocks := vp10100111000_0
theorem coverp10100111000 : Covers (-5343761639/4000000 : ℚ) vp10100111000 := cover_leaf (by decide +kernel)
private noncomputable def vp1010011100_0 : Blocks := edgeBlocks% "full/vectors/1010011100-V-0000.bin"
private noncomputable def vp1010011100_1 : Blocks := edgeBlocks% "full/vectors/1010011100-V-0001.bin"
noncomputable def vp1010011100 : Blocks := (Blocks.join vp1010011100_0 vp1010011100_1)
private theorem bp10100111000 : Branch 0 (-5343761639/8000000 : ℚ) vp1010011100 := by
  apply branch_left_normalized (c:=vp10100111000) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-5343761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5343761639/4000000 : ℚ) by norm_num]
  exact coverp10100111000
private noncomputable def ep10100111001_0 : Blocks := edgeBlocks% "full/vectors/10100111001-E-0000.bin"
private noncomputable def ep10100111001_1 : Blocks := edgeBlocks% "full/vectors/10100111001-E-0001.bin"
noncomputable def ep10100111001 : Blocks := (Blocks.join ep10100111001_0 ep10100111001_1)
private theorem idp10100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010011100.list =
    C ((2:ℤ)^153) * horner X vp10100111001.list + horner X ep10100111001.list := by
  exact edge_identity (B := (2:ℤ)^289) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100111001 : Branch 1 (-5343761639/8000000 : ℚ) vp1010011100 := by
  apply branch_checked idp10100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-5343761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5347761639/4000000 : ℚ) by norm_num]
  exact coverp10100111001
theorem coverp1010011100 : Covers (-5343761639/8000000 : ℚ) vp1010011100 := join_branches bp10100111000 bp10100111001
private noncomputable def vp101001110_0 : Blocks := edgeBlocks% "full/vectors/101001110-V-0000.bin"
private noncomputable def vp101001110_1 : Blocks := edgeBlocks% "full/vectors/101001110-V-0001.bin"
noncomputable def vp101001110 : Blocks := (Blocks.join vp101001110_0 vp101001110_1)
private theorem bp1010011100 : Branch 0 (-5343761639/16000000 : ℚ) vp101001110 := by
  apply branch_left_normalized (c:=vp1010011100) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-5343761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5343761639/8000000 : ℚ) by norm_num]
  exact coverp1010011100
private noncomputable def ep1010011101_0 : Blocks := edgeBlocks% "full/vectors/1010011101-E-0000.bin"
private noncomputable def ep1010011101_1 : Blocks := edgeBlocks% "full/vectors/1010011101-E-0001.bin"
noncomputable def ep1010011101 : Blocks := (Blocks.join ep1010011101_0 ep1010011101_1)
private theorem idp1010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101001110.list =
    C ((2:ℤ)^284) * horner X vp1010011101.list + horner X ep1010011101.list := by
  exact edge_identity (B := (2:ℤ)^453) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010011101 : Branch 1 (-5343761639/16000000 : ℚ) vp101001110 := by
  apply branch_checked idp1010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-5343761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5351761639/8000000 : ℚ) by norm_num]
  exact coverp1010011101
theorem coverp101001110 : Covers (-5343761639/16000000 : ℚ) vp101001110 := join_branches bp1010011100 bp1010011101
private noncomputable def vp10100111_0 : Blocks := edgeBlocks% "full/vectors/10100111-V-0000.bin"
private noncomputable def vp10100111_1 : Blocks := edgeBlocks% "full/vectors/10100111-V-0001.bin"
private noncomputable def vp10100111_2 : Blocks := edgeBlocks% "full/vectors/10100111-V-0002.bin"
private noncomputable def vp10100111_3 : Blocks := edgeBlocks% "full/vectors/10100111-V-0003.bin"
noncomputable def vp10100111 : Blocks := (Blocks.join (Blocks.join vp10100111_0 vp10100111_1) (Blocks.join vp10100111_2 vp10100111_3))
private theorem bp101001110 : Branch 0 (-5343761639/32000000 : ℚ) vp10100111 := by
  apply branch_left_normalized (c:=vp101001110) (k:=0) (m:=237) (by decide +kernel)
  rw [show 2*(-5343761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5343761639/16000000 : ℚ) by norm_num]
  exact coverp101001110
private noncomputable def ep101001111_0 : Blocks := edgeBlocks% "full/vectors/101001111-E-0000.bin"
private noncomputable def ep101001111_1 : Blocks := edgeBlocks% "full/vectors/101001111-E-0001.bin"
private noncomputable def ep101001111_2 : Blocks := edgeBlocks% "full/vectors/101001111-E-0002.bin"
private noncomputable def ep101001111_3 : Blocks := edgeBlocks% "full/vectors/101001111-E-0003.bin"
noncomputable def ep101001111 : Blocks := (Blocks.join (Blocks.join ep101001111_0 ep101001111_1) (Blocks.join ep101001111_2 ep101001111_3))
private theorem idp101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10100111.list =
    C ((2:ℤ)^543) * horner X vp101001111.list + horner X ep101001111.list := by
  exact edge_identity (B := (2:ℤ)^780) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101001111 : Branch 1 (-5343761639/32000000 : ℚ) vp10100111 := by
  apply branch_checked idp101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-5343761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5359761639/16000000 : ℚ) by norm_num]
  exact coverp101001111
theorem coverp10100111 : Covers (-5343761639/32000000 : ℚ) vp10100111 := join_branches bp101001110 bp101001111
private noncomputable def vp1010011011_0 : Blocks := edgeBlocks% "full/vectors/1010011011-V-0000.bin"
private noncomputable def vp1010011011_1 : Blocks := edgeBlocks% "full/vectors/1010011011-V-0001.bin"
noncomputable def vp1010011011 : Blocks := (Blocks.join vp1010011011_0 vp1010011011_1)
theorem coverp1010011011 : Covers (-5335761639/8000000 : ℚ) vp1010011011 := cover_leaf (by decide +kernel)
private noncomputable def vp1010011010_0 : Blocks := edgeBlocks% "full/vectors/1010011010-V-0000.bin"
private noncomputable def vp1010011010_1 : Blocks := edgeBlocks% "full/vectors/1010011010-V-0001.bin"
noncomputable def vp1010011010 : Blocks := (Blocks.join vp1010011010_0 vp1010011010_1)
theorem coverp1010011010 : Covers (-5327761639/8000000 : ℚ) vp1010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp101001101_0 : Blocks := edgeBlocks% "full/vectors/101001101-V-0000.bin"
private noncomputable def vp101001101_1 : Blocks := edgeBlocks% "full/vectors/101001101-V-0001.bin"
noncomputable def vp101001101 : Blocks := (Blocks.join vp101001101_0 vp101001101_1)
private theorem bp1010011010 : Branch 0 (-5327761639/16000000 : ℚ) vp101001101 := by
  apply branch_left_normalized (c:=vp1010011010) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-5327761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5327761639/8000000 : ℚ) by norm_num]
  exact coverp1010011010
private noncomputable def ep1010011011_0 : Blocks := edgeBlocks% "full/vectors/1010011011-E-0000.bin"
private noncomputable def ep1010011011_1 : Blocks := edgeBlocks% "full/vectors/1010011011-E-0001.bin"
noncomputable def ep1010011011 : Blocks := (Blocks.join ep1010011011_0 ep1010011011_1)
private theorem idp1010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101001101.list =
    C ((2:ℤ)^285) * horner X vp1010011011.list + horner X ep1010011011.list := by
  exact edge_identity (B := (2:ℤ)^454) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010011011 : Branch 1 (-5327761639/16000000 : ℚ) vp101001101 := by
  apply branch_checked idp1010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-5327761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5335761639/8000000 : ℚ) by norm_num]
  exact coverp1010011011
theorem coverp101001101 : Covers (-5327761639/16000000 : ℚ) vp101001101 := join_branches bp1010011010 bp1010011011
private noncomputable def vp10100110011_0 : Blocks := edgeBlocks% "full/vectors/10100110011-V-0000.bin"
noncomputable def vp10100110011 : Blocks := vp10100110011_0
theorem coverp10100110011 : Covers (-5323761639/4000000 : ℚ) vp10100110011 := cover_leaf (by decide +kernel)
private noncomputable def vp10100110010_0 : Blocks := edgeBlocks% "full/vectors/10100110010-V-0000.bin"
noncomputable def vp10100110010 : Blocks := vp10100110010_0
theorem coverp10100110010 : Covers (-5319761639/4000000 : ℚ) vp10100110010 := cover_leaf (by decide +kernel)
private noncomputable def vp1010011001_0 : Blocks := edgeBlocks% "full/vectors/1010011001-V-0000.bin"
private noncomputable def vp1010011001_1 : Blocks := edgeBlocks% "full/vectors/1010011001-V-0001.bin"
noncomputable def vp1010011001 : Blocks := (Blocks.join vp1010011001_0 vp1010011001_1)
private theorem bp10100110010 : Branch 0 (-5319761639/8000000 : ℚ) vp1010011001 := by
  apply branch_left_normalized (c:=vp10100110010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5319761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5319761639/4000000 : ℚ) by norm_num]
  exact coverp10100110010
private noncomputable def ep10100110011_0 : Blocks := edgeBlocks% "full/vectors/10100110011-E-0000.bin"
private noncomputable def ep10100110011_1 : Blocks := edgeBlocks% "full/vectors/10100110011-E-0001.bin"
noncomputable def ep10100110011 : Blocks := (Blocks.join ep10100110011_0 ep10100110011_1)
private theorem idp10100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010011001.list =
    C ((2:ℤ)^154) * horner X vp10100110011.list + horner X ep10100110011.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100110011 : Branch 1 (-5319761639/8000000 : ℚ) vp1010011001 := by
  apply branch_checked idp10100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-5319761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5323761639/4000000 : ℚ) by norm_num]
  exact coverp10100110011
theorem coverp1010011001 : Covers (-5319761639/8000000 : ℚ) vp1010011001 := join_branches bp10100110010 bp10100110011
private noncomputable def vp10100110001_0 : Blocks := edgeBlocks% "full/vectors/10100110001-V-0000.bin"
noncomputable def vp10100110001 : Blocks := vp10100110001_0
theorem coverp10100110001 : Covers (-5315761639/4000000 : ℚ) vp10100110001 := cover_leaf (by decide +kernel)
private noncomputable def vp10100110000_0 : Blocks := edgeBlocks% "full/vectors/10100110000-V-0000.bin"
noncomputable def vp10100110000 : Blocks := vp10100110000_0
theorem coverp10100110000 : Covers (-5311761639/4000000 : ℚ) vp10100110000 := cover_leaf (by decide +kernel)
private noncomputable def vp1010011000_0 : Blocks := edgeBlocks% "full/vectors/1010011000-V-0000.bin"
private noncomputable def vp1010011000_1 : Blocks := edgeBlocks% "full/vectors/1010011000-V-0001.bin"
noncomputable def vp1010011000 : Blocks := (Blocks.join vp1010011000_0 vp1010011000_1)
private theorem bp10100110000 : Branch 0 (-5311761639/8000000 : ℚ) vp1010011000 := by
  apply branch_left_normalized (c:=vp10100110000) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-5311761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5311761639/4000000 : ℚ) by norm_num]
  exact coverp10100110000
private noncomputable def ep10100110001_0 : Blocks := edgeBlocks% "full/vectors/10100110001-E-0000.bin"
private noncomputable def ep10100110001_1 : Blocks := edgeBlocks% "full/vectors/10100110001-E-0001.bin"
noncomputable def ep10100110001 : Blocks := (Blocks.join ep10100110001_0 ep10100110001_1)
private theorem idp10100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010011000.list =
    C ((2:ℤ)^153) * horner X vp10100110001.list + horner X ep10100110001.list := by
  exact edge_identity (B := (2:ℤ)^289) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100110001 : Branch 1 (-5311761639/8000000 : ℚ) vp1010011000 := by
  apply branch_checked idp10100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-5311761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5315761639/4000000 : ℚ) by norm_num]
  exact coverp10100110001
theorem coverp1010011000 : Covers (-5311761639/8000000 : ℚ) vp1010011000 := join_branches bp10100110000 bp10100110001
private noncomputable def vp101001100_0 : Blocks := edgeBlocks% "full/vectors/101001100-V-0000.bin"
private noncomputable def vp101001100_1 : Blocks := edgeBlocks% "full/vectors/101001100-V-0001.bin"
noncomputable def vp101001100 : Blocks := (Blocks.join vp101001100_0 vp101001100_1)
private theorem bp1010011000 : Branch 0 (-5311761639/16000000 : ℚ) vp101001100 := by
  apply branch_left_normalized (c:=vp1010011000) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-5311761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5311761639/8000000 : ℚ) by norm_num]
  exact coverp1010011000
private noncomputable def ep1010011001_0 : Blocks := edgeBlocks% "full/vectors/1010011001-E-0000.bin"
private noncomputable def ep1010011001_1 : Blocks := edgeBlocks% "full/vectors/1010011001-E-0001.bin"
noncomputable def ep1010011001 : Blocks := (Blocks.join ep1010011001_0 ep1010011001_1)
private theorem idp1010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101001100.list =
    C ((2:ℤ)^284) * horner X vp1010011001.list + horner X ep1010011001.list := by
  exact edge_identity (B := (2:ℤ)^454) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010011001 : Branch 1 (-5311761639/16000000 : ℚ) vp101001100 := by
  apply branch_checked idp1010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-5311761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5319761639/8000000 : ℚ) by norm_num]
  exact coverp1010011001
theorem coverp101001100 : Covers (-5311761639/16000000 : ℚ) vp101001100 := join_branches bp1010011000 bp1010011001
private noncomputable def vp10100110_0 : Blocks := edgeBlocks% "full/vectors/10100110-V-0000.bin"
private noncomputable def vp10100110_1 : Blocks := edgeBlocks% "full/vectors/10100110-V-0001.bin"
private noncomputable def vp10100110_2 : Blocks := edgeBlocks% "full/vectors/10100110-V-0002.bin"
private noncomputable def vp10100110_3 : Blocks := edgeBlocks% "full/vectors/10100110-V-0003.bin"
noncomputable def vp10100110 : Blocks := (Blocks.join (Blocks.join vp10100110_0 vp10100110_1) (Blocks.join vp10100110_2 vp10100110_3))
private theorem bp101001100 : Branch 0 (-5311761639/32000000 : ℚ) vp10100110 := by
  apply branch_left_normalized (c:=vp101001100) (k:=0) (m:=237) (by decide +kernel)
  rw [show 2*(-5311761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5311761639/16000000 : ℚ) by norm_num]
  exact coverp101001100
private noncomputable def ep101001101_0 : Blocks := edgeBlocks% "full/vectors/101001101-E-0000.bin"
private noncomputable def ep101001101_1 : Blocks := edgeBlocks% "full/vectors/101001101-E-0001.bin"
private noncomputable def ep101001101_2 : Blocks := edgeBlocks% "full/vectors/101001101-E-0002.bin"
private noncomputable def ep101001101_3 : Blocks := edgeBlocks% "full/vectors/101001101-E-0003.bin"
noncomputable def ep101001101 : Blocks := (Blocks.join (Blocks.join ep101001101_0 ep101001101_1) (Blocks.join ep101001101_2 ep101001101_3))
private theorem idp101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10100110.list =
    C ((2:ℤ)^546) * horner X vp101001101.list + horner X ep101001101.list := by
  exact edge_identity (B := (2:ℤ)^783) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101001101 : Branch 1 (-5311761639/32000000 : ℚ) vp10100110 := by
  apply branch_checked idp101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-5311761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5327761639/16000000 : ℚ) by norm_num]
  exact coverp101001101
theorem coverp10100110 : Covers (-5311761639/32000000 : ℚ) vp10100110 := join_branches bp101001100 bp101001101
private noncomputable def vp1010011_0 : Blocks := edgeBlocks% "full/vectors/1010011-V-0000.bin"
private noncomputable def vp1010011_1 : Blocks := edgeBlocks% "full/vectors/1010011-V-0001.bin"
private noncomputable def vp1010011_2 : Blocks := edgeBlocks% "full/vectors/1010011-V-0002.bin"
private noncomputable def vp1010011_3 : Blocks := edgeBlocks% "full/vectors/1010011-V-0003.bin"
private noncomputable def vp1010011_4 : Blocks := edgeBlocks% "full/vectors/1010011-V-0004.bin"
private noncomputable def vp1010011_5 : Blocks := edgeBlocks% "full/vectors/1010011-V-0005.bin"
private noncomputable def vp1010011_6 : Blocks := edgeBlocks% "full/vectors/1010011-V-0006.bin"
noncomputable def vp1010011 : Blocks := (Blocks.join (Blocks.join vp1010011_0 (Blocks.join vp1010011_1 vp1010011_2)) (Blocks.join (Blocks.join vp1010011_3 vp1010011_4) (Blocks.join vp1010011_5 vp1010011_6)))
private theorem bp10100110 : Branch 0 (-5311761639/64000000 : ℚ) vp1010011 := by
  apply branch_left_normalized (c:=vp10100110) (k:=0) (m:=452) (by decide +kernel)
  rw [show 2*(-5311761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5311761639/32000000 : ℚ) by norm_num]
  exact coverp10100110
private noncomputable def ep10100111_0 : Blocks := edgeBlocks% "full/vectors/10100111-E-0000.bin"
private noncomputable def ep10100111_1 : Blocks := edgeBlocks% "full/vectors/10100111-E-0001.bin"
private noncomputable def ep10100111_2 : Blocks := edgeBlocks% "full/vectors/10100111-E-0002.bin"
private noncomputable def ep10100111_3 : Blocks := edgeBlocks% "full/vectors/10100111-E-0003.bin"
private noncomputable def ep10100111_4 : Blocks := edgeBlocks% "full/vectors/10100111-E-0004.bin"
private noncomputable def ep10100111_5 : Blocks := edgeBlocks% "full/vectors/10100111-E-0005.bin"
private noncomputable def ep10100111_6 : Blocks := edgeBlocks% "full/vectors/10100111-E-0006.bin"
noncomputable def ep10100111 : Blocks := (Blocks.join (Blocks.join ep10100111_0 (Blocks.join ep10100111_1 ep10100111_2)) (Blocks.join (Blocks.join ep10100111_3 ep10100111_4) (Blocks.join ep10100111_5 ep10100111_6)))
private theorem idp10100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010011.list =
    C ((2:ℤ)^1061) * horner X vp10100111.list + horner X ep10100111.list := by
  exact edge_identity (B := (2:ℤ)^1434) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100111 : Branch 1 (-5311761639/64000000 : ℚ) vp1010011 := by
  apply branch_checked idp10100111 (by positivity) (by decide +kernel)
  rw [show 2*(-5311761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5343761639/32000000 : ℚ) by norm_num]
  exact coverp10100111
theorem coverp1010011 : Covers (-5311761639/64000000 : ℚ) vp1010011 := join_branches bp10100110 bp10100111
private noncomputable def vp1010010111_0 : Blocks := edgeBlocks% "full/vectors/1010010111-V-0000.bin"
private noncomputable def vp1010010111_1 : Blocks := edgeBlocks% "full/vectors/1010010111-V-0001.bin"
noncomputable def vp1010010111 : Blocks := (Blocks.join vp1010010111_0 vp1010010111_1)
theorem coverp1010010111 : Covers (-5303761639/8000000 : ℚ) vp1010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp10100101101_0 : Blocks := edgeBlocks% "full/vectors/10100101101-V-0000.bin"
noncomputable def vp10100101101 : Blocks := vp10100101101_0
theorem coverp10100101101 : Covers (-5299761639/4000000 : ℚ) vp10100101101 := cover_leaf (by decide +kernel)
private noncomputable def vp10100101100_0 : Blocks := edgeBlocks% "full/vectors/10100101100-V-0000.bin"
noncomputable def vp10100101100 : Blocks := vp10100101100_0
theorem coverp10100101100 : Covers (-5295761639/4000000 : ℚ) vp10100101100 := cover_leaf (by decide +kernel)
private noncomputable def vp1010010110_0 : Blocks := edgeBlocks% "full/vectors/1010010110-V-0000.bin"
private noncomputable def vp1010010110_1 : Blocks := edgeBlocks% "full/vectors/1010010110-V-0001.bin"
noncomputable def vp1010010110 : Blocks := (Blocks.join vp1010010110_0 vp1010010110_1)
private theorem bp10100101100 : Branch 0 (-5295761639/8000000 : ℚ) vp1010010110 := by
  apply branch_left_normalized (c:=vp10100101100) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-5295761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5295761639/4000000 : ℚ) by norm_num]
  exact coverp10100101100
private noncomputable def ep10100101101_0 : Blocks := edgeBlocks% "full/vectors/10100101101-E-0000.bin"
private noncomputable def ep10100101101_1 : Blocks := edgeBlocks% "full/vectors/10100101101-E-0001.bin"
noncomputable def ep10100101101 : Blocks := (Blocks.join ep10100101101_0 ep10100101101_1)
private theorem idp10100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010010110.list =
    C ((2:ℤ)^153) * horner X vp10100101101.list + horner X ep10100101101.list := by
  exact edge_identity (B := (2:ℤ)^289) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100101101 : Branch 1 (-5295761639/8000000 : ℚ) vp1010010110 := by
  apply branch_checked idp10100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-5295761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5299761639/4000000 : ℚ) by norm_num]
  exact coverp10100101101
theorem coverp1010010110 : Covers (-5295761639/8000000 : ℚ) vp1010010110 := join_branches bp10100101100 bp10100101101
private noncomputable def vp101001011_0 : Blocks := edgeBlocks% "full/vectors/101001011-V-0000.bin"
private noncomputable def vp101001011_1 : Blocks := edgeBlocks% "full/vectors/101001011-V-0001.bin"
noncomputable def vp101001011 : Blocks := (Blocks.join vp101001011_0 vp101001011_1)
private theorem bp1010010110 : Branch 0 (-5295761639/16000000 : ℚ) vp101001011 := by
  apply branch_left_normalized (c:=vp1010010110) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-5295761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5295761639/8000000 : ℚ) by norm_num]
  exact coverp1010010110
private noncomputable def ep1010010111_0 : Blocks := edgeBlocks% "full/vectors/1010010111-E-0000.bin"
private noncomputable def ep1010010111_1 : Blocks := edgeBlocks% "full/vectors/1010010111-E-0001.bin"
noncomputable def ep1010010111 : Blocks := (Blocks.join ep1010010111_0 ep1010010111_1)
private theorem idp1010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101001011.list =
    C ((2:ℤ)^285) * horner X vp1010010111.list + horner X ep1010010111.list := by
  exact edge_identity (B := (2:ℤ)^455) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010010111 : Branch 1 (-5295761639/16000000 : ℚ) vp101001011 := by
  apply branch_checked idp1010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-5295761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5303761639/8000000 : ℚ) by norm_num]
  exact coverp1010010111
theorem coverp101001011 : Covers (-5295761639/16000000 : ℚ) vp101001011 := join_branches bp1010010110 bp1010010111
private noncomputable def vp10100101011_0 : Blocks := edgeBlocks% "full/vectors/10100101011-V-0000.bin"
noncomputable def vp10100101011 : Blocks := vp10100101011_0
theorem coverp10100101011 : Covers (-5291761639/4000000 : ℚ) vp10100101011 := cover_leaf (by decide +kernel)
private noncomputable def vp10100101010_0 : Blocks := edgeBlocks% "full/vectors/10100101010-V-0000.bin"
noncomputable def vp10100101010 : Blocks := vp10100101010_0
theorem coverp10100101010 : Covers (-5287761639/4000000 : ℚ) vp10100101010 := cover_leaf (by decide +kernel)
private noncomputable def vp1010010101_0 : Blocks := edgeBlocks% "full/vectors/1010010101-V-0000.bin"
private noncomputable def vp1010010101_1 : Blocks := edgeBlocks% "full/vectors/1010010101-V-0001.bin"
noncomputable def vp1010010101 : Blocks := (Blocks.join vp1010010101_0 vp1010010101_1)
private theorem bp10100101010 : Branch 0 (-5287761639/8000000 : ℚ) vp1010010101 := by
  apply branch_left_normalized (c:=vp10100101010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5287761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5287761639/4000000 : ℚ) by norm_num]
  exact coverp10100101010
private noncomputable def ep10100101011_0 : Blocks := edgeBlocks% "full/vectors/10100101011-E-0000.bin"
private noncomputable def ep10100101011_1 : Blocks := edgeBlocks% "full/vectors/10100101011-E-0001.bin"
noncomputable def ep10100101011 : Blocks := (Blocks.join ep10100101011_0 ep10100101011_1)
private theorem idp10100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010010101.list =
    C ((2:ℤ)^154) * horner X vp10100101011.list + horner X ep10100101011.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100101011 : Branch 1 (-5287761639/8000000 : ℚ) vp1010010101 := by
  apply branch_checked idp10100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-5287761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5291761639/4000000 : ℚ) by norm_num]
  exact coverp10100101011
theorem coverp1010010101 : Covers (-5287761639/8000000 : ℚ) vp1010010101 := join_branches bp10100101010 bp10100101011
private noncomputable def vp10100101001_0 : Blocks := edgeBlocks% "full/vectors/10100101001-V-0000.bin"
noncomputable def vp10100101001 : Blocks := vp10100101001_0
theorem coverp10100101001 : Covers (-5283761639/4000000 : ℚ) vp10100101001 := cover_leaf (by decide +kernel)
private noncomputable def vp10100101000_0 : Blocks := edgeBlocks% "full/vectors/10100101000-V-0000.bin"
noncomputable def vp10100101000 : Blocks := vp10100101000_0
theorem coverp10100101000 : Covers (-5279761639/4000000 : ℚ) vp10100101000 := cover_leaf (by decide +kernel)
private noncomputable def vp1010010100_0 : Blocks := edgeBlocks% "full/vectors/1010010100-V-0000.bin"
private noncomputable def vp1010010100_1 : Blocks := edgeBlocks% "full/vectors/1010010100-V-0001.bin"
noncomputable def vp1010010100 : Blocks := (Blocks.join vp1010010100_0 vp1010010100_1)
private theorem bp10100101000 : Branch 0 (-5279761639/8000000 : ℚ) vp1010010100 := by
  apply branch_left_normalized (c:=vp10100101000) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-5279761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5279761639/4000000 : ℚ) by norm_num]
  exact coverp10100101000
private noncomputable def ep10100101001_0 : Blocks := edgeBlocks% "full/vectors/10100101001-E-0000.bin"
private noncomputable def ep10100101001_1 : Blocks := edgeBlocks% "full/vectors/10100101001-E-0001.bin"
noncomputable def ep10100101001 : Blocks := (Blocks.join ep10100101001_0 ep10100101001_1)
private theorem idp10100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010010100.list =
    C ((2:ℤ)^153) * horner X vp10100101001.list + horner X ep10100101001.list := by
  exact edge_identity (B := (2:ℤ)^289) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100101001 : Branch 1 (-5279761639/8000000 : ℚ) vp1010010100 := by
  apply branch_checked idp10100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-5279761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5283761639/4000000 : ℚ) by norm_num]
  exact coverp10100101001
theorem coverp1010010100 : Covers (-5279761639/8000000 : ℚ) vp1010010100 := join_branches bp10100101000 bp10100101001
private noncomputable def vp101001010_0 : Blocks := edgeBlocks% "full/vectors/101001010-V-0000.bin"
private noncomputable def vp101001010_1 : Blocks := edgeBlocks% "full/vectors/101001010-V-0001.bin"
noncomputable def vp101001010 : Blocks := (Blocks.join vp101001010_0 vp101001010_1)
private theorem bp1010010100 : Branch 0 (-5279761639/16000000 : ℚ) vp101001010 := by
  apply branch_left_normalized (c:=vp1010010100) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-5279761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5279761639/8000000 : ℚ) by norm_num]
  exact coverp1010010100
private noncomputable def ep1010010101_0 : Blocks := edgeBlocks% "full/vectors/1010010101-E-0000.bin"
private noncomputable def ep1010010101_1 : Blocks := edgeBlocks% "full/vectors/1010010101-E-0001.bin"
noncomputable def ep1010010101 : Blocks := (Blocks.join ep1010010101_0 ep1010010101_1)
private theorem idp1010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101001010.list =
    C ((2:ℤ)^285) * horner X vp1010010101.list + horner X ep1010010101.list := by
  exact edge_identity (B := (2:ℤ)^455) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010010101 : Branch 1 (-5279761639/16000000 : ℚ) vp101001010 := by
  apply branch_checked idp1010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-5279761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5287761639/8000000 : ℚ) by norm_num]
  exact coverp1010010101
theorem coverp101001010 : Covers (-5279761639/16000000 : ℚ) vp101001010 := join_branches bp1010010100 bp1010010101
private noncomputable def vp10100101_0 : Blocks := edgeBlocks% "full/vectors/10100101-V-0000.bin"
private noncomputable def vp10100101_1 : Blocks := edgeBlocks% "full/vectors/10100101-V-0001.bin"
private noncomputable def vp10100101_2 : Blocks := edgeBlocks% "full/vectors/10100101-V-0002.bin"
private noncomputable def vp10100101_3 : Blocks := edgeBlocks% "full/vectors/10100101-V-0003.bin"
noncomputable def vp10100101 : Blocks := (Blocks.join (Blocks.join vp10100101_0 vp10100101_1) (Blocks.join vp10100101_2 vp10100101_3))
private theorem bp101001010 : Branch 0 (-5279761639/32000000 : ℚ) vp10100101 := by
  apply branch_left_normalized (c:=vp101001010) (k:=0) (m:=238) (by decide +kernel)
  rw [show 2*(-5279761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5279761639/16000000 : ℚ) by norm_num]
  exact coverp101001010
private noncomputable def ep101001011_0 : Blocks := edgeBlocks% "full/vectors/101001011-E-0000.bin"
private noncomputable def ep101001011_1 : Blocks := edgeBlocks% "full/vectors/101001011-E-0001.bin"
private noncomputable def ep101001011_2 : Blocks := edgeBlocks% "full/vectors/101001011-E-0002.bin"
private noncomputable def ep101001011_3 : Blocks := edgeBlocks% "full/vectors/101001011-E-0003.bin"
noncomputable def ep101001011 : Blocks := (Blocks.join (Blocks.join ep101001011_0 ep101001011_1) (Blocks.join ep101001011_2 ep101001011_3))
private theorem idp101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10100101.list =
    C ((2:ℤ)^546) * horner X vp101001011.list + horner X ep101001011.list := by
  exact edge_identity (B := (2:ℤ)^784) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101001011 : Branch 1 (-5279761639/32000000 : ℚ) vp10100101 := by
  apply branch_checked idp101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-5279761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5295761639/16000000 : ℚ) by norm_num]
  exact coverp101001011
theorem coverp10100101 : Covers (-5279761639/32000000 : ℚ) vp10100101 := join_branches bp101001010 bp101001011
private noncomputable def vp10100100111_0 : Blocks := edgeBlocks% "full/vectors/10100100111-V-0000.bin"
noncomputable def vp10100100111 : Blocks := vp10100100111_0
theorem coverp10100100111 : Covers (-5275761639/4000000 : ℚ) vp10100100111 := cover_leaf (by decide +kernel)
private noncomputable def vp10100100110_0 : Blocks := edgeBlocks% "full/vectors/10100100110-V-0000.bin"
noncomputable def vp10100100110 : Blocks := vp10100100110_0
theorem coverp10100100110 : Covers (-5271761639/4000000 : ℚ) vp10100100110 := cover_leaf (by decide +kernel)
private noncomputable def vp1010010011_0 : Blocks := edgeBlocks% "full/vectors/1010010011-V-0000.bin"
private noncomputable def vp1010010011_1 : Blocks := edgeBlocks% "full/vectors/1010010011-V-0001.bin"
noncomputable def vp1010010011 : Blocks := (Blocks.join vp1010010011_0 vp1010010011_1)
private theorem bp10100100110 : Branch 0 (-5271761639/8000000 : ℚ) vp1010010011 := by
  apply branch_left_normalized (c:=vp10100100110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5271761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5271761639/4000000 : ℚ) by norm_num]
  exact coverp10100100110
private noncomputable def ep10100100111_0 : Blocks := edgeBlocks% "full/vectors/10100100111-E-0000.bin"
private noncomputable def ep10100100111_1 : Blocks := edgeBlocks% "full/vectors/10100100111-E-0001.bin"
noncomputable def ep10100100111 : Blocks := (Blocks.join ep10100100111_0 ep10100100111_1)
private theorem idp10100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010010011.list =
    C ((2:ℤ)^154) * horner X vp10100100111.list + horner X ep10100100111.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100100111 : Branch 1 (-5271761639/8000000 : ℚ) vp1010010011 := by
  apply branch_checked idp10100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-5271761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5275761639/4000000 : ℚ) by norm_num]
  exact coverp10100100111
theorem coverp1010010011 : Covers (-5271761639/8000000 : ℚ) vp1010010011 := join_branches bp10100100110 bp10100100111
private noncomputable def vp10100100101_0 : Blocks := edgeBlocks% "full/vectors/10100100101-V-0000.bin"
noncomputable def vp10100100101 : Blocks := vp10100100101_0
theorem coverp10100100101 : Covers (-5267761639/4000000 : ℚ) vp10100100101 := cover_leaf (by decide +kernel)
private noncomputable def vp10100100100_0 : Blocks := edgeBlocks% "full/vectors/10100100100-V-0000.bin"
noncomputable def vp10100100100 : Blocks := vp10100100100_0
theorem coverp10100100100 : Covers (-5263761639/4000000 : ℚ) vp10100100100 := cover_leaf (by decide +kernel)
private noncomputable def vp1010010010_0 : Blocks := edgeBlocks% "full/vectors/1010010010-V-0000.bin"
private noncomputable def vp1010010010_1 : Blocks := edgeBlocks% "full/vectors/1010010010-V-0001.bin"
noncomputable def vp1010010010 : Blocks := (Blocks.join vp1010010010_0 vp1010010010_1)
private theorem bp10100100100 : Branch 0 (-5263761639/8000000 : ℚ) vp1010010010 := by
  apply branch_left_normalized (c:=vp10100100100) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5263761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5263761639/4000000 : ℚ) by norm_num]
  exact coverp10100100100
private noncomputable def ep10100100101_0 : Blocks := edgeBlocks% "full/vectors/10100100101-E-0000.bin"
private noncomputable def ep10100100101_1 : Blocks := edgeBlocks% "full/vectors/10100100101-E-0001.bin"
noncomputable def ep10100100101 : Blocks := (Blocks.join ep10100100101_0 ep10100100101_1)
private theorem idp10100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010010010.list =
    C ((2:ℤ)^153) * horner X vp10100100101.list + horner X ep10100100101.list := by
  exact edge_identity (B := (2:ℤ)^289) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100100101 : Branch 1 (-5263761639/8000000 : ℚ) vp1010010010 := by
  apply branch_checked idp10100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-5263761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5267761639/4000000 : ℚ) by norm_num]
  exact coverp10100100101
theorem coverp1010010010 : Covers (-5263761639/8000000 : ℚ) vp1010010010 := join_branches bp10100100100 bp10100100101
private noncomputable def vp101001001_0 : Blocks := edgeBlocks% "full/vectors/101001001-V-0000.bin"
private noncomputable def vp101001001_1 : Blocks := edgeBlocks% "full/vectors/101001001-V-0001.bin"
noncomputable def vp101001001 : Blocks := (Blocks.join vp101001001_0 vp101001001_1)
private theorem bp1010010010 : Branch 0 (-5263761639/16000000 : ℚ) vp101001001 := by
  apply branch_left_normalized (c:=vp1010010010) (k:=0) (m:=129) (by decide +kernel)
  rw [show 2*(-5263761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5263761639/8000000 : ℚ) by norm_num]
  exact coverp1010010010
private noncomputable def ep1010010011_0 : Blocks := edgeBlocks% "full/vectors/1010010011-E-0000.bin"
private noncomputable def ep1010010011_1 : Blocks := edgeBlocks% "full/vectors/1010010011-E-0001.bin"
noncomputable def ep1010010011 : Blocks := (Blocks.join ep1010010011_0 ep1010010011_1)
private theorem idp1010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101001001.list =
    C ((2:ℤ)^286) * horner X vp1010010011.list + horner X ep1010010011.list := by
  exact edge_identity (B := (2:ℤ)^457) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010010011 : Branch 1 (-5263761639/16000000 : ℚ) vp101001001 := by
  apply branch_checked idp1010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-5263761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5271761639/8000000 : ℚ) by norm_num]
  exact coverp1010010011
theorem coverp101001001 : Covers (-5263761639/16000000 : ℚ) vp101001001 := join_branches bp1010010010 bp1010010011
private noncomputable def vp10100100011_0 : Blocks := edgeBlocks% "full/vectors/10100100011-V-0000.bin"
noncomputable def vp10100100011 : Blocks := vp10100100011_0
theorem coverp10100100011 : Covers (-5259761639/4000000 : ℚ) vp10100100011 := cover_leaf (by decide +kernel)
private noncomputable def vp10100100010_0 : Blocks := edgeBlocks% "full/vectors/10100100010-V-0000.bin"
noncomputable def vp10100100010 : Blocks := vp10100100010_0
theorem coverp10100100010 : Covers (-5255761639/4000000 : ℚ) vp10100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp1010010001_0 : Blocks := edgeBlocks% "full/vectors/1010010001-V-0000.bin"
private noncomputable def vp1010010001_1 : Blocks := edgeBlocks% "full/vectors/1010010001-V-0001.bin"
noncomputable def vp1010010001 : Blocks := (Blocks.join vp1010010001_0 vp1010010001_1)
private theorem bp10100100010 : Branch 0 (-5255761639/8000000 : ℚ) vp1010010001 := by
  apply branch_left_normalized (c:=vp10100100010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5255761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5255761639/4000000 : ℚ) by norm_num]
  exact coverp10100100010
private noncomputable def ep10100100011_0 : Blocks := edgeBlocks% "full/vectors/10100100011-E-0000.bin"
private noncomputable def ep10100100011_1 : Blocks := edgeBlocks% "full/vectors/10100100011-E-0001.bin"
noncomputable def ep10100100011 : Blocks := (Blocks.join ep10100100011_0 ep10100100011_1)
private theorem idp10100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010010001.list =
    C ((2:ℤ)^154) * horner X vp10100100011.list + horner X ep10100100011.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100100011 : Branch 1 (-5255761639/8000000 : ℚ) vp1010010001 := by
  apply branch_checked idp10100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-5255761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5259761639/4000000 : ℚ) by norm_num]
  exact coverp10100100011
theorem coverp1010010001 : Covers (-5255761639/8000000 : ℚ) vp1010010001 := join_branches bp10100100010 bp10100100011
private noncomputable def vp10100100001_0 : Blocks := edgeBlocks% "full/vectors/10100100001-V-0000.bin"
noncomputable def vp10100100001 : Blocks := vp10100100001_0
theorem coverp10100100001 : Covers (-5251761639/4000000 : ℚ) vp10100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp10100100000_0 : Blocks := edgeBlocks% "full/vectors/10100100000-V-0000.bin"
noncomputable def vp10100100000 : Blocks := vp10100100000_0
theorem coverp10100100000 : Covers (-5247761639/4000000 : ℚ) vp10100100000 := cover_leaf (by decide +kernel)
private noncomputable def vp1010010000_0 : Blocks := edgeBlocks% "full/vectors/1010010000-V-0000.bin"
private noncomputable def vp1010010000_1 : Blocks := edgeBlocks% "full/vectors/1010010000-V-0001.bin"
noncomputable def vp1010010000 : Blocks := (Blocks.join vp1010010000_0 vp1010010000_1)
private theorem bp10100100000 : Branch 0 (-5247761639/8000000 : ℚ) vp1010010000 := by
  apply branch_left_normalized (c:=vp10100100000) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5247761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5247761639/4000000 : ℚ) by norm_num]
  exact coverp10100100000
private noncomputable def ep10100100001_0 : Blocks := edgeBlocks% "full/vectors/10100100001-E-0000.bin"
private noncomputable def ep10100100001_1 : Blocks := edgeBlocks% "full/vectors/10100100001-E-0001.bin"
noncomputable def ep10100100001 : Blocks := (Blocks.join ep10100100001_0 ep10100100001_1)
private theorem idp10100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010010000.list =
    C ((2:ℤ)^154) * horner X vp10100100001.list + horner X ep10100100001.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100100001 : Branch 1 (-5247761639/8000000 : ℚ) vp1010010000 := by
  apply branch_checked idp10100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-5247761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5251761639/4000000 : ℚ) by norm_num]
  exact coverp10100100001
theorem coverp1010010000 : Covers (-5247761639/8000000 : ℚ) vp1010010000 := join_branches bp10100100000 bp10100100001
private noncomputable def vp101001000_0 : Blocks := edgeBlocks% "full/vectors/101001000-V-0000.bin"
private noncomputable def vp101001000_1 : Blocks := edgeBlocks% "full/vectors/101001000-V-0001.bin"
noncomputable def vp101001000 : Blocks := (Blocks.join vp101001000_0 vp101001000_1)
private theorem bp1010010000 : Branch 0 (-5247761639/16000000 : ℚ) vp101001000 := by
  apply branch_left_normalized (c:=vp1010010000) (k:=0) (m:=130) (by decide +kernel)
  rw [show 2*(-5247761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5247761639/8000000 : ℚ) by norm_num]
  exact coverp1010010000
private noncomputable def ep1010010001_0 : Blocks := edgeBlocks% "full/vectors/1010010001-E-0000.bin"
private noncomputable def ep1010010001_1 : Blocks := edgeBlocks% "full/vectors/1010010001-E-0001.bin"
noncomputable def ep1010010001 : Blocks := (Blocks.join ep1010010001_0 ep1010010001_1)
private theorem idp1010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101001000.list =
    C ((2:ℤ)^286) * horner X vp1010010001.list + horner X ep1010010001.list := by
  exact edge_identity (B := (2:ℤ)^456) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010010001 : Branch 1 (-5247761639/16000000 : ℚ) vp101001000 := by
  apply branch_checked idp1010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-5247761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5255761639/8000000 : ℚ) by norm_num]
  exact coverp1010010001
theorem coverp101001000 : Covers (-5247761639/16000000 : ℚ) vp101001000 := join_branches bp1010010000 bp1010010001
private noncomputable def vp10100100_0 : Blocks := edgeBlocks% "full/vectors/10100100-V-0000.bin"
private noncomputable def vp10100100_1 : Blocks := edgeBlocks% "full/vectors/10100100-V-0001.bin"
private noncomputable def vp10100100_2 : Blocks := edgeBlocks% "full/vectors/10100100-V-0002.bin"
private noncomputable def vp10100100_3 : Blocks := edgeBlocks% "full/vectors/10100100-V-0003.bin"
noncomputable def vp10100100 : Blocks := (Blocks.join (Blocks.join vp10100100_0 vp10100100_1) (Blocks.join vp10100100_2 vp10100100_3))
private theorem bp101001000 : Branch 0 (-5247761639/32000000 : ℚ) vp10100100 := by
  apply branch_left_normalized (c:=vp101001000) (k:=0) (m:=239) (by decide +kernel)
  rw [show 2*(-5247761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5247761639/16000000 : ℚ) by norm_num]
  exact coverp101001000
private noncomputable def ep101001001_0 : Blocks := edgeBlocks% "full/vectors/101001001-E-0000.bin"
private noncomputable def ep101001001_1 : Blocks := edgeBlocks% "full/vectors/101001001-E-0001.bin"
private noncomputable def ep101001001_2 : Blocks := edgeBlocks% "full/vectors/101001001-E-0002.bin"
private noncomputable def ep101001001_3 : Blocks := edgeBlocks% "full/vectors/101001001-E-0003.bin"
noncomputable def ep101001001 : Blocks := (Blocks.join (Blocks.join ep101001001_0 ep101001001_1) (Blocks.join ep101001001_2 ep101001001_3))
private theorem idp101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10100100.list =
    C ((2:ℤ)^547) * horner X vp101001001.list + horner X ep101001001.list := by
  exact edge_identity (B := (2:ℤ)^786) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101001001 : Branch 1 (-5247761639/32000000 : ℚ) vp10100100 := by
  apply branch_checked idp101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-5247761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5263761639/16000000 : ℚ) by norm_num]
  exact coverp101001001
theorem coverp10100100 : Covers (-5247761639/32000000 : ℚ) vp10100100 := join_branches bp101001000 bp101001001
private noncomputable def vp1010010_0 : Blocks := edgeBlocks% "full/vectors/1010010-V-0000.bin"
private noncomputable def vp1010010_1 : Blocks := edgeBlocks% "full/vectors/1010010-V-0001.bin"
private noncomputable def vp1010010_2 : Blocks := edgeBlocks% "full/vectors/1010010-V-0002.bin"
private noncomputable def vp1010010_3 : Blocks := edgeBlocks% "full/vectors/1010010-V-0003.bin"
private noncomputable def vp1010010_4 : Blocks := edgeBlocks% "full/vectors/1010010-V-0004.bin"
private noncomputable def vp1010010_5 : Blocks := edgeBlocks% "full/vectors/1010010-V-0005.bin"
private noncomputable def vp1010010_6 : Blocks := edgeBlocks% "full/vectors/1010010-V-0006.bin"
noncomputable def vp1010010 : Blocks := (Blocks.join (Blocks.join vp1010010_0 (Blocks.join vp1010010_1 vp1010010_2)) (Blocks.join (Blocks.join vp1010010_3 vp1010010_4) (Blocks.join vp1010010_5 vp1010010_6)))
private theorem bp10100100 : Branch 0 (-5247761639/64000000 : ℚ) vp1010010 := by
  apply branch_left_normalized (c:=vp10100100) (k:=0) (m:=454) (by decide +kernel)
  rw [show 2*(-5247761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5247761639/32000000 : ℚ) by norm_num]
  exact coverp10100100
private noncomputable def ep10100101_0 : Blocks := edgeBlocks% "full/vectors/10100101-E-0000.bin"
private noncomputable def ep10100101_1 : Blocks := edgeBlocks% "full/vectors/10100101-E-0001.bin"
private noncomputable def ep10100101_2 : Blocks := edgeBlocks% "full/vectors/10100101-E-0002.bin"
private noncomputable def ep10100101_3 : Blocks := edgeBlocks% "full/vectors/10100101-E-0003.bin"
private noncomputable def ep10100101_4 : Blocks := edgeBlocks% "full/vectors/10100101-E-0004.bin"
private noncomputable def ep10100101_5 : Blocks := edgeBlocks% "full/vectors/10100101-E-0005.bin"
private noncomputable def ep10100101_6 : Blocks := edgeBlocks% "full/vectors/10100101-E-0006.bin"
noncomputable def ep10100101 : Blocks := (Blocks.join (Blocks.join ep10100101_0 (Blocks.join ep10100101_1 ep10100101_2)) (Blocks.join (Blocks.join ep10100101_3 ep10100101_4) (Blocks.join ep10100101_5 ep10100101_6)))
private theorem idp10100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010010.list =
    C ((2:ℤ)^1067) * horner X vp10100101.list + horner X ep10100101.list := by
  exact edge_identity (B := (2:ℤ)^1442) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100101 : Branch 1 (-5247761639/64000000 : ℚ) vp1010010 := by
  apply branch_checked idp10100101 (by positivity) (by decide +kernel)
  rw [show 2*(-5247761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5279761639/32000000 : ℚ) by norm_num]
  exact coverp10100101
theorem coverp1010010 : Covers (-5247761639/64000000 : ℚ) vp1010010 := join_branches bp10100100 bp10100101
private noncomputable def vp101001_0 : Blocks := edgeBlocks% "full/vectors/101001-V-0000.bin"
private noncomputable def vp101001_1 : Blocks := edgeBlocks% "full/vectors/101001-V-0001.bin"
private noncomputable def vp101001_2 : Blocks := edgeBlocks% "full/vectors/101001-V-0002.bin"
private noncomputable def vp101001_3 : Blocks := edgeBlocks% "full/vectors/101001-V-0003.bin"
private noncomputable def vp101001_4 : Blocks := edgeBlocks% "full/vectors/101001-V-0004.bin"
private noncomputable def vp101001_5 : Blocks := edgeBlocks% "full/vectors/101001-V-0005.bin"
private noncomputable def vp101001_6 : Blocks := edgeBlocks% "full/vectors/101001-V-0006.bin"
private noncomputable def vp101001_7 : Blocks := edgeBlocks% "full/vectors/101001-V-0007.bin"
private noncomputable def vp101001_8 : Blocks := edgeBlocks% "full/vectors/101001-V-0008.bin"
private noncomputable def vp101001_9 : Blocks := edgeBlocks% "full/vectors/101001-V-0009.bin"
private noncomputable def vp101001_10 : Blocks := edgeBlocks% "full/vectors/101001-V-0010.bin"
private noncomputable def vp101001_11 : Blocks := edgeBlocks% "full/vectors/101001-V-0011.bin"
private noncomputable def vp101001_12 : Blocks := edgeBlocks% "full/vectors/101001-V-0012.bin"
private noncomputable def vp101001_13 : Blocks := edgeBlocks% "full/vectors/101001-V-0013.bin"
noncomputable def vp101001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp101001_0 (Blocks.join vp101001_1 vp101001_2)) (Blocks.join (Blocks.join vp101001_3 vp101001_4) (Blocks.join vp101001_5 vp101001_6))) (Blocks.join (Blocks.join vp101001_7 (Blocks.join vp101001_8 vp101001_9)) (Blocks.join (Blocks.join vp101001_10 vp101001_11) (Blocks.join vp101001_12 vp101001_13))))
private theorem bp1010010 : Branch 0 (-5247761639/128000000 : ℚ) vp101001 := by
  apply branch_left_normalized (c:=vp1010010) (k:=0) (m:=881) (by decide +kernel)
  rw [show 2*(-5247761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-5247761639/64000000 : ℚ) by norm_num]
  exact coverp1010010
private noncomputable def ep1010011_0 : Blocks := edgeBlocks% "full/vectors/1010011-E-0000.bin"
private noncomputable def ep1010011_1 : Blocks := edgeBlocks% "full/vectors/1010011-E-0001.bin"
private noncomputable def ep1010011_2 : Blocks := edgeBlocks% "full/vectors/1010011-E-0002.bin"
private noncomputable def ep1010011_3 : Blocks := edgeBlocks% "full/vectors/1010011-E-0003.bin"
private noncomputable def ep1010011_4 : Blocks := edgeBlocks% "full/vectors/1010011-E-0004.bin"
private noncomputable def ep1010011_5 : Blocks := edgeBlocks% "full/vectors/1010011-E-0005.bin"
private noncomputable def ep1010011_6 : Blocks := edgeBlocks% "full/vectors/1010011-E-0006.bin"
private noncomputable def ep1010011_7 : Blocks := edgeBlocks% "full/vectors/1010011-E-0007.bin"
private noncomputable def ep1010011_8 : Blocks := edgeBlocks% "full/vectors/1010011-E-0008.bin"
private noncomputable def ep1010011_9 : Blocks := edgeBlocks% "full/vectors/1010011-E-0009.bin"
private noncomputable def ep1010011_10 : Blocks := edgeBlocks% "full/vectors/1010011-E-0010.bin"
private noncomputable def ep1010011_11 : Blocks := edgeBlocks% "full/vectors/1010011-E-0011.bin"
private noncomputable def ep1010011_12 : Blocks := edgeBlocks% "full/vectors/1010011-E-0012.bin"
private noncomputable def ep1010011_13 : Blocks := edgeBlocks% "full/vectors/1010011-E-0013.bin"
noncomputable def ep1010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1010011_0 (Blocks.join ep1010011_1 ep1010011_2)) (Blocks.join (Blocks.join ep1010011_3 ep1010011_4) (Blocks.join ep1010011_5 ep1010011_6))) (Blocks.join (Blocks.join ep1010011_7 (Blocks.join ep1010011_8 ep1010011_9)) (Blocks.join (Blocks.join ep1010011_10 ep1010011_11) (Blocks.join ep1010011_12 ep1010011_13))))
private theorem idp1010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101001.list =
    C ((2:ℤ)^2085) * horner X vp1010011.list + horner X ep1010011.list := by
  exact edge_identity (B := (2:ℤ)^2731) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010011 : Branch 1 (-5247761639/128000000 : ℚ) vp101001 := by
  apply branch_checked idp1010011 (by positivity) (by decide +kernel)
  rw [show 2*(-5247761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-5311761639/64000000 : ℚ) by norm_num]
  exact coverp1010011
theorem coverp101001 : Covers (-5247761639/128000000 : ℚ) vp101001 := join_branches bp1010010 bp1010011
private noncomputable def vp10100011111_0 : Blocks := edgeBlocks% "full/vectors/10100011111-V-0000.bin"
noncomputable def vp10100011111 : Blocks := vp10100011111_0
theorem coverp10100011111 : Covers (-5243761639/4000000 : ℚ) vp10100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp10100011110_0 : Blocks := edgeBlocks% "full/vectors/10100011110-V-0000.bin"
noncomputable def vp10100011110 : Blocks := vp10100011110_0
theorem coverp10100011110 : Covers (-5239761639/4000000 : ℚ) vp10100011110 := cover_leaf (by decide +kernel)
private noncomputable def vp1010001111_0 : Blocks := edgeBlocks% "full/vectors/1010001111-V-0000.bin"
private noncomputable def vp1010001111_1 : Blocks := edgeBlocks% "full/vectors/1010001111-V-0001.bin"
noncomputable def vp1010001111 : Blocks := (Blocks.join vp1010001111_0 vp1010001111_1)
private theorem bp10100011110 : Branch 0 (-5239761639/8000000 : ℚ) vp1010001111 := by
  apply branch_left_normalized (c:=vp10100011110) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-5239761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5239761639/4000000 : ℚ) by norm_num]
  exact coverp10100011110
private noncomputable def ep10100011111_0 : Blocks := edgeBlocks% "full/vectors/10100011111-E-0000.bin"
private noncomputable def ep10100011111_1 : Blocks := edgeBlocks% "full/vectors/10100011111-E-0001.bin"
noncomputable def ep10100011111 : Blocks := (Blocks.join ep10100011111_0 ep10100011111_1)
private theorem idp10100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010001111.list =
    C ((2:ℤ)^155) * horner X vp10100011111.list + horner X ep10100011111.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100011111 : Branch 1 (-5239761639/8000000 : ℚ) vp1010001111 := by
  apply branch_checked idp10100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-5239761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5243761639/4000000 : ℚ) by norm_num]
  exact coverp10100011111
theorem coverp1010001111 : Covers (-5239761639/8000000 : ℚ) vp1010001111 := join_branches bp10100011110 bp10100011111
private noncomputable def vp10100011101_0 : Blocks := edgeBlocks% "full/vectors/10100011101-V-0000.bin"
noncomputable def vp10100011101 : Blocks := vp10100011101_0
theorem coverp10100011101 : Covers (-5235761639/4000000 : ℚ) vp10100011101 := cover_leaf (by decide +kernel)
private noncomputable def vp10100011100_0 : Blocks := edgeBlocks% "full/vectors/10100011100-V-0000.bin"
noncomputable def vp10100011100 : Blocks := vp10100011100_0
theorem coverp10100011100 : Covers (-5231761639/4000000 : ℚ) vp10100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp1010001110_0 : Blocks := edgeBlocks% "full/vectors/1010001110-V-0000.bin"
private noncomputable def vp1010001110_1 : Blocks := edgeBlocks% "full/vectors/1010001110-V-0001.bin"
noncomputable def vp1010001110 : Blocks := (Blocks.join vp1010001110_0 vp1010001110_1)
private theorem bp10100011100 : Branch 0 (-5231761639/8000000 : ℚ) vp1010001110 := by
  apply branch_left_normalized (c:=vp10100011100) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5231761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5231761639/4000000 : ℚ) by norm_num]
  exact coverp10100011100
private noncomputable def ep10100011101_0 : Blocks := edgeBlocks% "full/vectors/10100011101-E-0000.bin"
private noncomputable def ep10100011101_1 : Blocks := edgeBlocks% "full/vectors/10100011101-E-0001.bin"
noncomputable def ep10100011101 : Blocks := (Blocks.join ep10100011101_0 ep10100011101_1)
private theorem idp10100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010001110.list =
    C ((2:ℤ)^154) * horner X vp10100011101.list + horner X ep10100011101.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100011101 : Branch 1 (-5231761639/8000000 : ℚ) vp1010001110 := by
  apply branch_checked idp10100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-5231761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5235761639/4000000 : ℚ) by norm_num]
  exact coverp10100011101
theorem coverp1010001110 : Covers (-5231761639/8000000 : ℚ) vp1010001110 := join_branches bp10100011100 bp10100011101
private noncomputable def vp101000111_0 : Blocks := edgeBlocks% "full/vectors/101000111-V-0000.bin"
private noncomputable def vp101000111_1 : Blocks := edgeBlocks% "full/vectors/101000111-V-0001.bin"
noncomputable def vp101000111 : Blocks := (Blocks.join vp101000111_0 vp101000111_1)
private theorem bp1010001110 : Branch 0 (-5231761639/16000000 : ℚ) vp101000111 := by
  apply branch_left_normalized (c:=vp1010001110) (k:=0) (m:=130) (by decide +kernel)
  rw [show 2*(-5231761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5231761639/8000000 : ℚ) by norm_num]
  exact coverp1010001110
private noncomputable def ep1010001111_0 : Blocks := edgeBlocks% "full/vectors/1010001111-E-0000.bin"
private noncomputable def ep1010001111_1 : Blocks := edgeBlocks% "full/vectors/1010001111-E-0001.bin"
noncomputable def ep1010001111 : Blocks := (Blocks.join ep1010001111_0 ep1010001111_1)
private theorem idp1010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101000111.list =
    C ((2:ℤ)^286) * horner X vp1010001111.list + horner X ep1010001111.list := by
  exact edge_identity (B := (2:ℤ)^456) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010001111 : Branch 1 (-5231761639/16000000 : ℚ) vp101000111 := by
  apply branch_checked idp1010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-5231761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5239761639/8000000 : ℚ) by norm_num]
  exact coverp1010001111
theorem coverp101000111 : Covers (-5231761639/16000000 : ℚ) vp101000111 := join_branches bp1010001110 bp1010001111
private noncomputable def vp10100011011_0 : Blocks := edgeBlocks% "full/vectors/10100011011-V-0000.bin"
noncomputable def vp10100011011 : Blocks := vp10100011011_0
theorem coverp10100011011 : Covers (-5227761639/4000000 : ℚ) vp10100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp10100011010_0 : Blocks := edgeBlocks% "full/vectors/10100011010-V-0000.bin"
noncomputable def vp10100011010 : Blocks := vp10100011010_0
theorem coverp10100011010 : Covers (-5223761639/4000000 : ℚ) vp10100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp1010001101_0 : Blocks := edgeBlocks% "full/vectors/1010001101-V-0000.bin"
private noncomputable def vp1010001101_1 : Blocks := edgeBlocks% "full/vectors/1010001101-V-0001.bin"
noncomputable def vp1010001101 : Blocks := (Blocks.join vp1010001101_0 vp1010001101_1)
private theorem bp10100011010 : Branch 0 (-5223761639/8000000 : ℚ) vp1010001101 := by
  apply branch_left_normalized (c:=vp10100011010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5223761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5223761639/4000000 : ℚ) by norm_num]
  exact coverp10100011010
private noncomputable def ep10100011011_0 : Blocks := edgeBlocks% "full/vectors/10100011011-E-0000.bin"
private noncomputable def ep10100011011_1 : Blocks := edgeBlocks% "full/vectors/10100011011-E-0001.bin"
noncomputable def ep10100011011 : Blocks := (Blocks.join ep10100011011_0 ep10100011011_1)
private theorem idp10100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010001101.list =
    C ((2:ℤ)^154) * horner X vp10100011011.list + horner X ep10100011011.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100011011 : Branch 1 (-5223761639/8000000 : ℚ) vp1010001101 := by
  apply branch_checked idp10100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-5223761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5227761639/4000000 : ℚ) by norm_num]
  exact coverp10100011011
theorem coverp1010001101 : Covers (-5223761639/8000000 : ℚ) vp1010001101 := join_branches bp10100011010 bp10100011011
private noncomputable def vp10100011001_0 : Blocks := edgeBlocks% "full/vectors/10100011001-V-0000.bin"
noncomputable def vp10100011001 : Blocks := vp10100011001_0
theorem coverp10100011001 : Covers (-5219761639/4000000 : ℚ) vp10100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp10100011000_0 : Blocks := edgeBlocks% "full/vectors/10100011000-V-0000.bin"
noncomputable def vp10100011000 : Blocks := vp10100011000_0
theorem coverp10100011000 : Covers (-5215761639/4000000 : ℚ) vp10100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp1010001100_0 : Blocks := edgeBlocks% "full/vectors/1010001100-V-0000.bin"
private noncomputable def vp1010001100_1 : Blocks := edgeBlocks% "full/vectors/1010001100-V-0001.bin"
noncomputable def vp1010001100 : Blocks := (Blocks.join vp1010001100_0 vp1010001100_1)
private theorem bp10100011000 : Branch 0 (-5215761639/8000000 : ℚ) vp1010001100 := by
  apply branch_left_normalized (c:=vp10100011000) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-5215761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5215761639/4000000 : ℚ) by norm_num]
  exact coverp10100011000
private noncomputable def ep10100011001_0 : Blocks := edgeBlocks% "full/vectors/10100011001-E-0000.bin"
private noncomputable def ep10100011001_1 : Blocks := edgeBlocks% "full/vectors/10100011001-E-0001.bin"
noncomputable def ep10100011001 : Blocks := (Blocks.join ep10100011001_0 ep10100011001_1)
private theorem idp10100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010001100.list =
    C ((2:ℤ)^155) * horner X vp10100011001.list + horner X ep10100011001.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100011001 : Branch 1 (-5215761639/8000000 : ℚ) vp1010001100 := by
  apply branch_checked idp10100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-5215761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5219761639/4000000 : ℚ) by norm_num]
  exact coverp10100011001
theorem coverp1010001100 : Covers (-5215761639/8000000 : ℚ) vp1010001100 := join_branches bp10100011000 bp10100011001
private noncomputable def vp101000110_0 : Blocks := edgeBlocks% "full/vectors/101000110-V-0000.bin"
private noncomputable def vp101000110_1 : Blocks := edgeBlocks% "full/vectors/101000110-V-0001.bin"
noncomputable def vp101000110 : Blocks := (Blocks.join vp101000110_0 vp101000110_1)
private theorem bp1010001100 : Branch 0 (-5215761639/16000000 : ℚ) vp101000110 := by
  apply branch_left_normalized (c:=vp1010001100) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-5215761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5215761639/8000000 : ℚ) by norm_num]
  exact coverp1010001100
private noncomputable def ep1010001101_0 : Blocks := edgeBlocks% "full/vectors/1010001101-E-0000.bin"
private noncomputable def ep1010001101_1 : Blocks := edgeBlocks% "full/vectors/1010001101-E-0001.bin"
noncomputable def ep1010001101 : Blocks := (Blocks.join ep1010001101_0 ep1010001101_1)
private theorem idp1010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101000110.list =
    C ((2:ℤ)^286) * horner X vp1010001101.list + horner X ep1010001101.list := by
  exact edge_identity (B := (2:ℤ)^457) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010001101 : Branch 1 (-5215761639/16000000 : ℚ) vp101000110 := by
  apply branch_checked idp1010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-5215761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5223761639/8000000 : ℚ) by norm_num]
  exact coverp1010001101
theorem coverp101000110 : Covers (-5215761639/16000000 : ℚ) vp101000110 := join_branches bp1010001100 bp1010001101
private noncomputable def vp10100011_0 : Blocks := edgeBlocks% "full/vectors/10100011-V-0000.bin"
private noncomputable def vp10100011_1 : Blocks := edgeBlocks% "full/vectors/10100011-V-0001.bin"
private noncomputable def vp10100011_2 : Blocks := edgeBlocks% "full/vectors/10100011-V-0002.bin"
private noncomputable def vp10100011_3 : Blocks := edgeBlocks% "full/vectors/10100011-V-0003.bin"
noncomputable def vp10100011 : Blocks := (Blocks.join (Blocks.join vp10100011_0 vp10100011_1) (Blocks.join vp10100011_2 vp10100011_3))
private theorem bp101000110 : Branch 0 (-5215761639/32000000 : ℚ) vp10100011 := by
  apply branch_left_normalized (c:=vp101000110) (k:=0) (m:=239) (by decide +kernel)
  rw [show 2*(-5215761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5215761639/16000000 : ℚ) by norm_num]
  exact coverp101000110
private noncomputable def ep101000111_0 : Blocks := edgeBlocks% "full/vectors/101000111-E-0000.bin"
private noncomputable def ep101000111_1 : Blocks := edgeBlocks% "full/vectors/101000111-E-0001.bin"
private noncomputable def ep101000111_2 : Blocks := edgeBlocks% "full/vectors/101000111-E-0002.bin"
private noncomputable def ep101000111_3 : Blocks := edgeBlocks% "full/vectors/101000111-E-0003.bin"
noncomputable def ep101000111 : Blocks := (Blocks.join (Blocks.join ep101000111_0 ep101000111_1) (Blocks.join ep101000111_2 ep101000111_3))
private theorem idp101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10100011.list =
    C ((2:ℤ)^550) * horner X vp101000111.list + horner X ep101000111.list := by
  exact edge_identity (B := (2:ℤ)^789) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101000111 : Branch 1 (-5215761639/32000000 : ℚ) vp10100011 := by
  apply branch_checked idp101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-5215761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5231761639/16000000 : ℚ) by norm_num]
  exact coverp101000111
theorem coverp10100011 : Covers (-5215761639/32000000 : ℚ) vp10100011 := join_branches bp101000110 bp101000111
private noncomputable def vp10100010111_0 : Blocks := edgeBlocks% "full/vectors/10100010111-V-0000.bin"
noncomputable def vp10100010111 : Blocks := vp10100010111_0
theorem coverp10100010111 : Covers (-5211761639/4000000 : ℚ) vp10100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp10100010110_0 : Blocks := edgeBlocks% "full/vectors/10100010110-V-0000.bin"
noncomputable def vp10100010110 : Blocks := vp10100010110_0
theorem coverp10100010110 : Covers (-5207761639/4000000 : ℚ) vp10100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp1010001011_0 : Blocks := edgeBlocks% "full/vectors/1010001011-V-0000.bin"
private noncomputable def vp1010001011_1 : Blocks := edgeBlocks% "full/vectors/1010001011-V-0001.bin"
noncomputable def vp1010001011 : Blocks := (Blocks.join vp1010001011_0 vp1010001011_1)
private theorem bp10100010110 : Branch 0 (-5207761639/8000000 : ℚ) vp1010001011 := by
  apply branch_left_normalized (c:=vp10100010110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5207761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5207761639/4000000 : ℚ) by norm_num]
  exact coverp10100010110
private noncomputable def ep10100010111_0 : Blocks := edgeBlocks% "full/vectors/10100010111-E-0000.bin"
private noncomputable def ep10100010111_1 : Blocks := edgeBlocks% "full/vectors/10100010111-E-0001.bin"
noncomputable def ep10100010111 : Blocks := (Blocks.join ep10100010111_0 ep10100010111_1)
private theorem idp10100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010001011.list =
    C ((2:ℤ)^154) * horner X vp10100010111.list + horner X ep10100010111.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100010111 : Branch 1 (-5207761639/8000000 : ℚ) vp1010001011 := by
  apply branch_checked idp10100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-5207761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5211761639/4000000 : ℚ) by norm_num]
  exact coverp10100010111
theorem coverp1010001011 : Covers (-5207761639/8000000 : ℚ) vp1010001011 := join_branches bp10100010110 bp10100010111
private noncomputable def vp10100010101_0 : Blocks := edgeBlocks% "full/vectors/10100010101-V-0000.bin"
noncomputable def vp10100010101 : Blocks := vp10100010101_0
theorem coverp10100010101 : Covers (-5203761639/4000000 : ℚ) vp10100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp10100010100_0 : Blocks := edgeBlocks% "full/vectors/10100010100-V-0000.bin"
noncomputable def vp10100010100 : Blocks := vp10100010100_0
theorem coverp10100010100 : Covers (-5199761639/4000000 : ℚ) vp10100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp1010001010_0 : Blocks := edgeBlocks% "full/vectors/1010001010-V-0000.bin"
private noncomputable def vp1010001010_1 : Blocks := edgeBlocks% "full/vectors/1010001010-V-0001.bin"
noncomputable def vp1010001010 : Blocks := (Blocks.join vp1010001010_0 vp1010001010_1)
private theorem bp10100010100 : Branch 0 (-5199761639/8000000 : ℚ) vp1010001010 := by
  apply branch_left_normalized (c:=vp10100010100) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5199761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5199761639/4000000 : ℚ) by norm_num]
  exact coverp10100010100
private noncomputable def ep10100010101_0 : Blocks := edgeBlocks% "full/vectors/10100010101-E-0000.bin"
private noncomputable def ep10100010101_1 : Blocks := edgeBlocks% "full/vectors/10100010101-E-0001.bin"
noncomputable def ep10100010101 : Blocks := (Blocks.join ep10100010101_0 ep10100010101_1)
private theorem idp10100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010001010.list =
    C ((2:ℤ)^155) * horner X vp10100010101.list + horner X ep10100010101.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100010101 : Branch 1 (-5199761639/8000000 : ℚ) vp1010001010 := by
  apply branch_checked idp10100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-5199761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5203761639/4000000 : ℚ) by norm_num]
  exact coverp10100010101
theorem coverp1010001010 : Covers (-5199761639/8000000 : ℚ) vp1010001010 := join_branches bp10100010100 bp10100010101
private noncomputable def vp101000101_0 : Blocks := edgeBlocks% "full/vectors/101000101-V-0000.bin"
private noncomputable def vp101000101_1 : Blocks := edgeBlocks% "full/vectors/101000101-V-0001.bin"
noncomputable def vp101000101 : Blocks := (Blocks.join vp101000101_0 vp101000101_1)
private theorem bp1010001010 : Branch 0 (-5199761639/16000000 : ℚ) vp101000101 := by
  apply branch_left_normalized (c:=vp1010001010) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-5199761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5199761639/8000000 : ℚ) by norm_num]
  exact coverp1010001010
private noncomputable def ep1010001011_0 : Blocks := edgeBlocks% "full/vectors/1010001011-E-0000.bin"
private noncomputable def ep1010001011_1 : Blocks := edgeBlocks% "full/vectors/1010001011-E-0001.bin"
noncomputable def ep1010001011 : Blocks := (Blocks.join ep1010001011_0 ep1010001011_1)
private theorem idp1010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101000101.list =
    C ((2:ℤ)^287) * horner X vp1010001011.list + horner X ep1010001011.list := by
  exact edge_identity (B := (2:ℤ)^458) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010001011 : Branch 1 (-5199761639/16000000 : ℚ) vp101000101 := by
  apply branch_checked idp1010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-5199761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5207761639/8000000 : ℚ) by norm_num]
  exact coverp1010001011
theorem coverp101000101 : Covers (-5199761639/16000000 : ℚ) vp101000101 := join_branches bp1010001010 bp1010001011
private noncomputable def vp10100010011_0 : Blocks := edgeBlocks% "full/vectors/10100010011-V-0000.bin"
noncomputable def vp10100010011 : Blocks := vp10100010011_0
theorem coverp10100010011 : Covers (-5195761639/4000000 : ℚ) vp10100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp10100010010_0 : Blocks := edgeBlocks% "full/vectors/10100010010-V-0000.bin"
noncomputable def vp10100010010 : Blocks := vp10100010010_0
theorem coverp10100010010 : Covers (-5191761639/4000000 : ℚ) vp10100010010 := cover_leaf (by decide +kernel)
private noncomputable def vp1010001001_0 : Blocks := edgeBlocks% "full/vectors/1010001001-V-0000.bin"
private noncomputable def vp1010001001_1 : Blocks := edgeBlocks% "full/vectors/1010001001-V-0001.bin"
noncomputable def vp1010001001 : Blocks := (Blocks.join vp1010001001_0 vp1010001001_1)
private theorem bp10100010010 : Branch 0 (-5191761639/8000000 : ℚ) vp1010001001 := by
  apply branch_left_normalized (c:=vp10100010010) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-5191761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5191761639/4000000 : ℚ) by norm_num]
  exact coverp10100010010
private noncomputable def ep10100010011_0 : Blocks := edgeBlocks% "full/vectors/10100010011-E-0000.bin"
private noncomputable def ep10100010011_1 : Blocks := edgeBlocks% "full/vectors/10100010011-E-0001.bin"
noncomputable def ep10100010011 : Blocks := (Blocks.join ep10100010011_0 ep10100010011_1)
private theorem idp10100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010001001.list =
    C ((2:ℤ)^155) * horner X vp10100010011.list + horner X ep10100010011.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100010011 : Branch 1 (-5191761639/8000000 : ℚ) vp1010001001 := by
  apply branch_checked idp10100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-5191761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5195761639/4000000 : ℚ) by norm_num]
  exact coverp10100010011
theorem coverp1010001001 : Covers (-5191761639/8000000 : ℚ) vp1010001001 := join_branches bp10100010010 bp10100010011
private noncomputable def vp10100010001_0 : Blocks := edgeBlocks% "full/vectors/10100010001-V-0000.bin"
noncomputable def vp10100010001 : Blocks := vp10100010001_0
theorem coverp10100010001 : Covers (-5187761639/4000000 : ℚ) vp10100010001 := cover_leaf (by decide +kernel)
private noncomputable def vp10100010000_0 : Blocks := edgeBlocks% "full/vectors/10100010000-V-0000.bin"
noncomputable def vp10100010000 : Blocks := vp10100010000_0
theorem coverp10100010000 : Covers (-5183761639/4000000 : ℚ) vp10100010000 := cover_leaf (by decide +kernel)
private noncomputable def vp1010001000_0 : Blocks := edgeBlocks% "full/vectors/1010001000-V-0000.bin"
private noncomputable def vp1010001000_1 : Blocks := edgeBlocks% "full/vectors/1010001000-V-0001.bin"
noncomputable def vp1010001000 : Blocks := (Blocks.join vp1010001000_0 vp1010001000_1)
private theorem bp10100010000 : Branch 0 (-5183761639/8000000 : ℚ) vp1010001000 := by
  apply branch_left_normalized (c:=vp10100010000) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5183761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5183761639/4000000 : ℚ) by norm_num]
  exact coverp10100010000
private noncomputable def ep10100010001_0 : Blocks := edgeBlocks% "full/vectors/10100010001-E-0000.bin"
private noncomputable def ep10100010001_1 : Blocks := edgeBlocks% "full/vectors/10100010001-E-0001.bin"
noncomputable def ep10100010001 : Blocks := (Blocks.join ep10100010001_0 ep10100010001_1)
private theorem idp10100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010001000.list =
    C ((2:ℤ)^155) * horner X vp10100010001.list + horner X ep10100010001.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100010001 : Branch 1 (-5183761639/8000000 : ℚ) vp1010001000 := by
  apply branch_checked idp10100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-5183761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5187761639/4000000 : ℚ) by norm_num]
  exact coverp10100010001
theorem coverp1010001000 : Covers (-5183761639/8000000 : ℚ) vp1010001000 := join_branches bp10100010000 bp10100010001
private noncomputable def vp101000100_0 : Blocks := edgeBlocks% "full/vectors/101000100-V-0000.bin"
private noncomputable def vp101000100_1 : Blocks := edgeBlocks% "full/vectors/101000100-V-0001.bin"
noncomputable def vp101000100 : Blocks := (Blocks.join vp101000100_0 vp101000100_1)
private theorem bp1010001000 : Branch 0 (-5183761639/16000000 : ℚ) vp101000100 := by
  apply branch_left_normalized (c:=vp1010001000) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-5183761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5183761639/8000000 : ℚ) by norm_num]
  exact coverp1010001000
private noncomputable def ep1010001001_0 : Blocks := edgeBlocks% "full/vectors/1010001001-E-0000.bin"
private noncomputable def ep1010001001_1 : Blocks := edgeBlocks% "full/vectors/1010001001-E-0001.bin"
noncomputable def ep1010001001 : Blocks := (Blocks.join ep1010001001_0 ep1010001001_1)
private theorem idp1010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101000100.list =
    C ((2:ℤ)^287) * horner X vp1010001001.list + horner X ep1010001001.list := by
  exact edge_identity (B := (2:ℤ)^458) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010001001 : Branch 1 (-5183761639/16000000 : ℚ) vp101000100 := by
  apply branch_checked idp1010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-5183761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5191761639/8000000 : ℚ) by norm_num]
  exact coverp1010001001
theorem coverp101000100 : Covers (-5183761639/16000000 : ℚ) vp101000100 := join_branches bp1010001000 bp1010001001
private noncomputable def vp10100010_0 : Blocks := edgeBlocks% "full/vectors/10100010-V-0000.bin"
private noncomputable def vp10100010_1 : Blocks := edgeBlocks% "full/vectors/10100010-V-0001.bin"
private noncomputable def vp10100010_2 : Blocks := edgeBlocks% "full/vectors/10100010-V-0002.bin"
private noncomputable def vp10100010_3 : Blocks := edgeBlocks% "full/vectors/10100010-V-0003.bin"
noncomputable def vp10100010 : Blocks := (Blocks.join (Blocks.join vp10100010_0 vp10100010_1) (Blocks.join vp10100010_2 vp10100010_3))
private theorem bp101000100 : Branch 0 (-5183761639/32000000 : ℚ) vp10100010 := by
  apply branch_left_normalized (c:=vp101000100) (k:=0) (m:=240) (by decide +kernel)
  rw [show 2*(-5183761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5183761639/16000000 : ℚ) by norm_num]
  exact coverp101000100
private noncomputable def ep101000101_0 : Blocks := edgeBlocks% "full/vectors/101000101-E-0000.bin"
private noncomputable def ep101000101_1 : Blocks := edgeBlocks% "full/vectors/101000101-E-0001.bin"
private noncomputable def ep101000101_2 : Blocks := edgeBlocks% "full/vectors/101000101-E-0002.bin"
private noncomputable def ep101000101_3 : Blocks := edgeBlocks% "full/vectors/101000101-E-0003.bin"
noncomputable def ep101000101 : Blocks := (Blocks.join (Blocks.join ep101000101_0 ep101000101_1) (Blocks.join ep101000101_2 ep101000101_3))
private theorem idp101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10100010.list =
    C ((2:ℤ)^550) * horner X vp101000101.list + horner X ep101000101.list := by
  exact edge_identity (B := (2:ℤ)^790) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101000101 : Branch 1 (-5183761639/32000000 : ℚ) vp10100010 := by
  apply branch_checked idp101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-5183761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5199761639/16000000 : ℚ) by norm_num]
  exact coverp101000101
theorem coverp10100010 : Covers (-5183761639/32000000 : ℚ) vp10100010 := join_branches bp101000100 bp101000101
private noncomputable def vp1010001_0 : Blocks := edgeBlocks% "full/vectors/1010001-V-0000.bin"
private noncomputable def vp1010001_1 : Blocks := edgeBlocks% "full/vectors/1010001-V-0001.bin"
private noncomputable def vp1010001_2 : Blocks := edgeBlocks% "full/vectors/1010001-V-0002.bin"
private noncomputable def vp1010001_3 : Blocks := edgeBlocks% "full/vectors/1010001-V-0003.bin"
private noncomputable def vp1010001_4 : Blocks := edgeBlocks% "full/vectors/1010001-V-0004.bin"
private noncomputable def vp1010001_5 : Blocks := edgeBlocks% "full/vectors/1010001-V-0005.bin"
private noncomputable def vp1010001_6 : Blocks := edgeBlocks% "full/vectors/1010001-V-0006.bin"
noncomputable def vp1010001 : Blocks := (Blocks.join (Blocks.join vp1010001_0 (Blocks.join vp1010001_1 vp1010001_2)) (Blocks.join (Blocks.join vp1010001_3 vp1010001_4) (Blocks.join vp1010001_5 vp1010001_6)))
private theorem bp10100010 : Branch 0 (-5183761639/64000000 : ℚ) vp1010001 := by
  apply branch_left_normalized (c:=vp10100010) (k:=0) (m:=457) (by decide +kernel)
  rw [show 2*(-5183761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5183761639/32000000 : ℚ) by norm_num]
  exact coverp10100010
private noncomputable def ep10100011_0 : Blocks := edgeBlocks% "full/vectors/10100011-E-0000.bin"
private noncomputable def ep10100011_1 : Blocks := edgeBlocks% "full/vectors/10100011-E-0001.bin"
private noncomputable def ep10100011_2 : Blocks := edgeBlocks% "full/vectors/10100011-E-0002.bin"
private noncomputable def ep10100011_3 : Blocks := edgeBlocks% "full/vectors/10100011-E-0003.bin"
private noncomputable def ep10100011_4 : Blocks := edgeBlocks% "full/vectors/10100011-E-0004.bin"
private noncomputable def ep10100011_5 : Blocks := edgeBlocks% "full/vectors/10100011-E-0005.bin"
private noncomputable def ep10100011_6 : Blocks := edgeBlocks% "full/vectors/10100011-E-0006.bin"
noncomputable def ep10100011 : Blocks := (Blocks.join (Blocks.join ep10100011_0 (Blocks.join ep10100011_1 ep10100011_2)) (Blocks.join (Blocks.join ep10100011_3 ep10100011_4) (Blocks.join ep10100011_5 ep10100011_6)))
private theorem idp10100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010001.list =
    C ((2:ℤ)^1070) * horner X vp10100011.list + horner X ep10100011.list := by
  exact edge_identity (B := (2:ℤ)^1449) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100011 : Branch 1 (-5183761639/64000000 : ℚ) vp1010001 := by
  apply branch_checked idp10100011 (by positivity) (by decide +kernel)
  rw [show 2*(-5183761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5215761639/32000000 : ℚ) by norm_num]
  exact coverp10100011
theorem coverp1010001 : Covers (-5183761639/64000000 : ℚ) vp1010001 := join_branches bp10100010 bp10100011
private noncomputable def vp10100001111_0 : Blocks := edgeBlocks% "full/vectors/10100001111-V-0000.bin"
noncomputable def vp10100001111 : Blocks := vp10100001111_0
theorem coverp10100001111 : Covers (-5179761639/4000000 : ℚ) vp10100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp10100001110_0 : Blocks := edgeBlocks% "full/vectors/10100001110-V-0000.bin"
noncomputable def vp10100001110 : Blocks := vp10100001110_0
theorem coverp10100001110 : Covers (-5175761639/4000000 : ℚ) vp10100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp1010000111_0 : Blocks := edgeBlocks% "full/vectors/1010000111-V-0000.bin"
private noncomputable def vp1010000111_1 : Blocks := edgeBlocks% "full/vectors/1010000111-V-0001.bin"
noncomputable def vp1010000111 : Blocks := (Blocks.join vp1010000111_0 vp1010000111_1)
private theorem bp10100001110 : Branch 0 (-5175761639/8000000 : ℚ) vp1010000111 := by
  apply branch_left_normalized (c:=vp10100001110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5175761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5175761639/4000000 : ℚ) by norm_num]
  exact coverp10100001110
private noncomputable def ep10100001111_0 : Blocks := edgeBlocks% "full/vectors/10100001111-E-0000.bin"
private noncomputable def ep10100001111_1 : Blocks := edgeBlocks% "full/vectors/10100001111-E-0001.bin"
noncomputable def ep10100001111 : Blocks := (Blocks.join ep10100001111_0 ep10100001111_1)
private theorem idp10100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010000111.list =
    C ((2:ℤ)^156) * horner X vp10100001111.list + horner X ep10100001111.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100001111 : Branch 1 (-5175761639/8000000 : ℚ) vp1010000111 := by
  apply branch_checked idp10100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-5175761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5179761639/4000000 : ℚ) by norm_num]
  exact coverp10100001111
theorem coverp1010000111 : Covers (-5175761639/8000000 : ℚ) vp1010000111 := join_branches bp10100001110 bp10100001111
private noncomputable def vp10100001101_0 : Blocks := edgeBlocks% "full/vectors/10100001101-V-0000.bin"
noncomputable def vp10100001101 : Blocks := vp10100001101_0
theorem coverp10100001101 : Covers (-5171761639/4000000 : ℚ) vp10100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp10100001100_0 : Blocks := edgeBlocks% "full/vectors/10100001100-V-0000.bin"
noncomputable def vp10100001100 : Blocks := vp10100001100_0
theorem coverp10100001100 : Covers (-5167761639/4000000 : ℚ) vp10100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp1010000110_0 : Blocks := edgeBlocks% "full/vectors/1010000110-V-0000.bin"
private noncomputable def vp1010000110_1 : Blocks := edgeBlocks% "full/vectors/1010000110-V-0001.bin"
noncomputable def vp1010000110 : Blocks := (Blocks.join vp1010000110_0 vp1010000110_1)
private theorem bp10100001100 : Branch 0 (-5167761639/8000000 : ℚ) vp1010000110 := by
  apply branch_left_normalized (c:=vp10100001100) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5167761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5167761639/4000000 : ℚ) by norm_num]
  exact coverp10100001100
private noncomputable def ep10100001101_0 : Blocks := edgeBlocks% "full/vectors/10100001101-E-0000.bin"
private noncomputable def ep10100001101_1 : Blocks := edgeBlocks% "full/vectors/10100001101-E-0001.bin"
noncomputable def ep10100001101 : Blocks := (Blocks.join ep10100001101_0 ep10100001101_1)
private theorem idp10100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010000110.list =
    C ((2:ℤ)^155) * horner X vp10100001101.list + horner X ep10100001101.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100001101 : Branch 1 (-5167761639/8000000 : ℚ) vp1010000110 := by
  apply branch_checked idp10100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-5167761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5171761639/4000000 : ℚ) by norm_num]
  exact coverp10100001101
theorem coverp1010000110 : Covers (-5167761639/8000000 : ℚ) vp1010000110 := join_branches bp10100001100 bp10100001101
private noncomputable def vp101000011_0 : Blocks := edgeBlocks% "full/vectors/101000011-V-0000.bin"
private noncomputable def vp101000011_1 : Blocks := edgeBlocks% "full/vectors/101000011-V-0001.bin"
noncomputable def vp101000011 : Blocks := (Blocks.join vp101000011_0 vp101000011_1)
private theorem bp1010000110 : Branch 0 (-5167761639/16000000 : ℚ) vp101000011 := by
  apply branch_left_normalized (c:=vp1010000110) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-5167761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5167761639/8000000 : ℚ) by norm_num]
  exact coverp1010000110
private noncomputable def ep1010000111_0 : Blocks := edgeBlocks% "full/vectors/1010000111-E-0000.bin"
private noncomputable def ep1010000111_1 : Blocks := edgeBlocks% "full/vectors/1010000111-E-0001.bin"
noncomputable def ep1010000111 : Blocks := (Blocks.join ep1010000111_0 ep1010000111_1)
private theorem idp1010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101000011.list =
    C ((2:ℤ)^288) * horner X vp1010000111.list + horner X ep1010000111.list := by
  exact edge_identity (B := (2:ℤ)^460) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010000111 : Branch 1 (-5167761639/16000000 : ℚ) vp101000011 := by
  apply branch_checked idp1010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-5167761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5175761639/8000000 : ℚ) by norm_num]
  exact coverp1010000111
theorem coverp101000011 : Covers (-5167761639/16000000 : ℚ) vp101000011 := join_branches bp1010000110 bp1010000111
private noncomputable def vp10100001011_0 : Blocks := edgeBlocks% "full/vectors/10100001011-V-0000.bin"
noncomputable def vp10100001011 : Blocks := vp10100001011_0
theorem coverp10100001011 : Covers (-5163761639/4000000 : ℚ) vp10100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp10100001010_0 : Blocks := edgeBlocks% "full/vectors/10100001010-V-0000.bin"
noncomputable def vp10100001010 : Blocks := vp10100001010_0
theorem coverp10100001010 : Covers (-5159761639/4000000 : ℚ) vp10100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp1010000101_0 : Blocks := edgeBlocks% "full/vectors/1010000101-V-0000.bin"
private noncomputable def vp1010000101_1 : Blocks := edgeBlocks% "full/vectors/1010000101-V-0001.bin"
noncomputable def vp1010000101 : Blocks := (Blocks.join vp1010000101_0 vp1010000101_1)
private theorem bp10100001010 : Branch 0 (-5159761639/8000000 : ℚ) vp1010000101 := by
  apply branch_left_normalized (c:=vp10100001010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5159761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5159761639/4000000 : ℚ) by norm_num]
  exact coverp10100001010
private noncomputable def ep10100001011_0 : Blocks := edgeBlocks% "full/vectors/10100001011-E-0000.bin"
private noncomputable def ep10100001011_1 : Blocks := edgeBlocks% "full/vectors/10100001011-E-0001.bin"
noncomputable def ep10100001011 : Blocks := (Blocks.join ep10100001011_0 ep10100001011_1)
private theorem idp10100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010000101.list =
    C ((2:ℤ)^155) * horner X vp10100001011.list + horner X ep10100001011.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100001011 : Branch 1 (-5159761639/8000000 : ℚ) vp1010000101 := by
  apply branch_checked idp10100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-5159761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5163761639/4000000 : ℚ) by norm_num]
  exact coverp10100001011
theorem coverp1010000101 : Covers (-5159761639/8000000 : ℚ) vp1010000101 := join_branches bp10100001010 bp10100001011
private noncomputable def vp10100001001_0 : Blocks := edgeBlocks% "full/vectors/10100001001-V-0000.bin"
noncomputable def vp10100001001 : Blocks := vp10100001001_0
theorem coverp10100001001 : Covers (-5155761639/4000000 : ℚ) vp10100001001 := cover_leaf (by decide +kernel)
private noncomputable def vp10100001000_0 : Blocks := edgeBlocks% "full/vectors/10100001000-V-0000.bin"
noncomputable def vp10100001000 : Blocks := vp10100001000_0
theorem coverp10100001000 : Covers (-5151761639/4000000 : ℚ) vp10100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp1010000100_0 : Blocks := edgeBlocks% "full/vectors/1010000100-V-0000.bin"
private noncomputable def vp1010000100_1 : Blocks := edgeBlocks% "full/vectors/1010000100-V-0001.bin"
noncomputable def vp1010000100 : Blocks := (Blocks.join vp1010000100_0 vp1010000100_1)
private theorem bp10100001000 : Branch 0 (-5151761639/8000000 : ℚ) vp1010000100 := by
  apply branch_left_normalized (c:=vp10100001000) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5151761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5151761639/4000000 : ℚ) by norm_num]
  exact coverp10100001000
private noncomputable def ep10100001001_0 : Blocks := edgeBlocks% "full/vectors/10100001001-E-0000.bin"
private noncomputable def ep10100001001_1 : Blocks := edgeBlocks% "full/vectors/10100001001-E-0001.bin"
noncomputable def ep10100001001 : Blocks := (Blocks.join ep10100001001_0 ep10100001001_1)
private theorem idp10100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010000100.list =
    C ((2:ℤ)^155) * horner X vp10100001001.list + horner X ep10100001001.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100001001 : Branch 1 (-5151761639/8000000 : ℚ) vp1010000100 := by
  apply branch_checked idp10100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-5151761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5155761639/4000000 : ℚ) by norm_num]
  exact coverp10100001001
theorem coverp1010000100 : Covers (-5151761639/8000000 : ℚ) vp1010000100 := join_branches bp10100001000 bp10100001001
private noncomputable def vp101000010_0 : Blocks := edgeBlocks% "full/vectors/101000010-V-0000.bin"
private noncomputable def vp101000010_1 : Blocks := edgeBlocks% "full/vectors/101000010-V-0001.bin"
noncomputable def vp101000010 : Blocks := (Blocks.join vp101000010_0 vp101000010_1)
private theorem bp1010000100 : Branch 0 (-5151761639/16000000 : ℚ) vp101000010 := by
  apply branch_left_normalized (c:=vp1010000100) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-5151761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5151761639/8000000 : ℚ) by norm_num]
  exact coverp1010000100
private noncomputable def ep1010000101_0 : Blocks := edgeBlocks% "full/vectors/1010000101-E-0000.bin"
private noncomputable def ep1010000101_1 : Blocks := edgeBlocks% "full/vectors/1010000101-E-0001.bin"
noncomputable def ep1010000101 : Blocks := (Blocks.join ep1010000101_0 ep1010000101_1)
private theorem idp1010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101000010.list =
    C ((2:ℤ)^288) * horner X vp1010000101.list + horner X ep1010000101.list := by
  exact edge_identity (B := (2:ℤ)^460) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010000101 : Branch 1 (-5151761639/16000000 : ℚ) vp101000010 := by
  apply branch_checked idp1010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-5151761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5159761639/8000000 : ℚ) by norm_num]
  exact coverp1010000101
theorem coverp101000010 : Covers (-5151761639/16000000 : ℚ) vp101000010 := join_branches bp1010000100 bp1010000101
private noncomputable def vp10100001_0 : Blocks := edgeBlocks% "full/vectors/10100001-V-0000.bin"
private noncomputable def vp10100001_1 : Blocks := edgeBlocks% "full/vectors/10100001-V-0001.bin"
private noncomputable def vp10100001_2 : Blocks := edgeBlocks% "full/vectors/10100001-V-0002.bin"
private noncomputable def vp10100001_3 : Blocks := edgeBlocks% "full/vectors/10100001-V-0003.bin"
noncomputable def vp10100001 : Blocks := (Blocks.join (Blocks.join vp10100001_0 vp10100001_1) (Blocks.join vp10100001_2 vp10100001_3))
private theorem bp101000010 : Branch 0 (-5151761639/32000000 : ℚ) vp10100001 := by
  apply branch_left_normalized (c:=vp101000010) (k:=0) (m:=241) (by decide +kernel)
  rw [show 2*(-5151761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5151761639/16000000 : ℚ) by norm_num]
  exact coverp101000010
private noncomputable def ep101000011_0 : Blocks := edgeBlocks% "full/vectors/101000011-E-0000.bin"
private noncomputable def ep101000011_1 : Blocks := edgeBlocks% "full/vectors/101000011-E-0001.bin"
private noncomputable def ep101000011_2 : Blocks := edgeBlocks% "full/vectors/101000011-E-0002.bin"
private noncomputable def ep101000011_3 : Blocks := edgeBlocks% "full/vectors/101000011-E-0003.bin"
noncomputable def ep101000011 : Blocks := (Blocks.join (Blocks.join ep101000011_0 ep101000011_1) (Blocks.join ep101000011_2 ep101000011_3))
private theorem idp101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10100001.list =
    C ((2:ℤ)^551) * horner X vp101000011.list + horner X ep101000011.list := by
  exact edge_identity (B := (2:ℤ)^793) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101000011 : Branch 1 (-5151761639/32000000 : ℚ) vp10100001 := by
  apply branch_checked idp101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-5151761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5167761639/16000000 : ℚ) by norm_num]
  exact coverp101000011
theorem coverp10100001 : Covers (-5151761639/32000000 : ℚ) vp10100001 := join_branches bp101000010 bp101000011
private noncomputable def vp10100000111_0 : Blocks := edgeBlocks% "full/vectors/10100000111-V-0000.bin"
noncomputable def vp10100000111 : Blocks := vp10100000111_0
theorem coverp10100000111 : Covers (-5147761639/4000000 : ℚ) vp10100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp10100000110_0 : Blocks := edgeBlocks% "full/vectors/10100000110-V-0000.bin"
noncomputable def vp10100000110 : Blocks := vp10100000110_0
theorem coverp10100000110 : Covers (-5143761639/4000000 : ℚ) vp10100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp1010000011_0 : Blocks := edgeBlocks% "full/vectors/1010000011-V-0000.bin"
private noncomputable def vp1010000011_1 : Blocks := edgeBlocks% "full/vectors/1010000011-V-0001.bin"
noncomputable def vp1010000011 : Blocks := (Blocks.join vp1010000011_0 vp1010000011_1)
private theorem bp10100000110 : Branch 0 (-5143761639/8000000 : ℚ) vp1010000011 := by
  apply branch_left_normalized (c:=vp10100000110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5143761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5143761639/4000000 : ℚ) by norm_num]
  exact coverp10100000110
private noncomputable def ep10100000111_0 : Blocks := edgeBlocks% "full/vectors/10100000111-E-0000.bin"
private noncomputable def ep10100000111_1 : Blocks := edgeBlocks% "full/vectors/10100000111-E-0001.bin"
noncomputable def ep10100000111 : Blocks := (Blocks.join ep10100000111_0 ep10100000111_1)
private theorem idp10100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010000011.list =
    C ((2:ℤ)^154) * horner X vp10100000111.list + horner X ep10100000111.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100000111 : Branch 1 (-5143761639/8000000 : ℚ) vp1010000011 := by
  apply branch_checked idp10100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-5143761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5147761639/4000000 : ℚ) by norm_num]
  exact coverp10100000111
theorem coverp1010000011 : Covers (-5143761639/8000000 : ℚ) vp1010000011 := join_branches bp10100000110 bp10100000111
private noncomputable def vp10100000101_0 : Blocks := edgeBlocks% "full/vectors/10100000101-V-0000.bin"
noncomputable def vp10100000101 : Blocks := vp10100000101_0
theorem coverp10100000101 : Covers (-5139761639/4000000 : ℚ) vp10100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp10100000100_0 : Blocks := edgeBlocks% "full/vectors/10100000100-V-0000.bin"
noncomputable def vp10100000100 : Blocks := vp10100000100_0
theorem coverp10100000100 : Covers (-5135761639/4000000 : ℚ) vp10100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp1010000010_0 : Blocks := edgeBlocks% "full/vectors/1010000010-V-0000.bin"
private noncomputable def vp1010000010_1 : Blocks := edgeBlocks% "full/vectors/1010000010-V-0001.bin"
noncomputable def vp1010000010 : Blocks := (Blocks.join vp1010000010_0 vp1010000010_1)
private theorem bp10100000100 : Branch 0 (-5135761639/8000000 : ℚ) vp1010000010 := by
  apply branch_left_normalized (c:=vp10100000100) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5135761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5135761639/4000000 : ℚ) by norm_num]
  exact coverp10100000100
private noncomputable def ep10100000101_0 : Blocks := edgeBlocks% "full/vectors/10100000101-E-0000.bin"
private noncomputable def ep10100000101_1 : Blocks := edgeBlocks% "full/vectors/10100000101-E-0001.bin"
noncomputable def ep10100000101 : Blocks := (Blocks.join ep10100000101_0 ep10100000101_1)
private theorem idp10100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010000010.list =
    C ((2:ℤ)^156) * horner X vp10100000101.list + horner X ep10100000101.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100000101 : Branch 1 (-5135761639/8000000 : ℚ) vp1010000010 := by
  apply branch_checked idp10100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-5135761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5139761639/4000000 : ℚ) by norm_num]
  exact coverp10100000101
theorem coverp1010000010 : Covers (-5135761639/8000000 : ℚ) vp1010000010 := join_branches bp10100000100 bp10100000101
private noncomputable def vp101000001_0 : Blocks := edgeBlocks% "full/vectors/101000001-V-0000.bin"
private noncomputable def vp101000001_1 : Blocks := edgeBlocks% "full/vectors/101000001-V-0001.bin"
noncomputable def vp101000001 : Blocks := (Blocks.join vp101000001_0 vp101000001_1)
private theorem bp1010000010 : Branch 0 (-5135761639/16000000 : ℚ) vp101000001 := by
  apply branch_left_normalized (c:=vp1010000010) (k:=0) (m:=132) (by decide +kernel)
  rw [show 2*(-5135761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5135761639/8000000 : ℚ) by norm_num]
  exact coverp1010000010
private noncomputable def ep1010000011_0 : Blocks := edgeBlocks% "full/vectors/1010000011-E-0000.bin"
private noncomputable def ep1010000011_1 : Blocks := edgeBlocks% "full/vectors/1010000011-E-0001.bin"
noncomputable def ep1010000011 : Blocks := (Blocks.join ep1010000011_0 ep1010000011_1)
private theorem idp1010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101000001.list =
    C ((2:ℤ)^289) * horner X vp1010000011.list + horner X ep1010000011.list := by
  exact edge_identity (B := (2:ℤ)^460) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010000011 : Branch 1 (-5135761639/16000000 : ℚ) vp101000001 := by
  apply branch_checked idp1010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-5135761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5143761639/8000000 : ℚ) by norm_num]
  exact coverp1010000011
theorem coverp101000001 : Covers (-5135761639/16000000 : ℚ) vp101000001 := join_branches bp1010000010 bp1010000011
private noncomputable def vp10100000011_0 : Blocks := edgeBlocks% "full/vectors/10100000011-V-0000.bin"
noncomputable def vp10100000011 : Blocks := vp10100000011_0
theorem coverp10100000011 : Covers (-5131761639/4000000 : ℚ) vp10100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp10100000010_0 : Blocks := edgeBlocks% "full/vectors/10100000010-V-0000.bin"
noncomputable def vp10100000010 : Blocks := vp10100000010_0
theorem coverp10100000010 : Covers (-5127761639/4000000 : ℚ) vp10100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp1010000001_0 : Blocks := edgeBlocks% "full/vectors/1010000001-V-0000.bin"
private noncomputable def vp1010000001_1 : Blocks := edgeBlocks% "full/vectors/1010000001-V-0001.bin"
noncomputable def vp1010000001 : Blocks := (Blocks.join vp1010000001_0 vp1010000001_1)
private theorem bp10100000010 : Branch 0 (-5127761639/8000000 : ℚ) vp1010000001 := by
  apply branch_left_normalized (c:=vp10100000010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5127761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5127761639/4000000 : ℚ) by norm_num]
  exact coverp10100000010
private noncomputable def ep10100000011_0 : Blocks := edgeBlocks% "full/vectors/10100000011-E-0000.bin"
private noncomputable def ep10100000011_1 : Blocks := edgeBlocks% "full/vectors/10100000011-E-0001.bin"
noncomputable def ep10100000011 : Blocks := (Blocks.join ep10100000011_0 ep10100000011_1)
private theorem idp10100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010000001.list =
    C ((2:ℤ)^156) * horner X vp10100000011.list + horner X ep10100000011.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100000011 : Branch 1 (-5127761639/8000000 : ℚ) vp1010000001 := by
  apply branch_checked idp10100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-5127761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5131761639/4000000 : ℚ) by norm_num]
  exact coverp10100000011
theorem coverp1010000001 : Covers (-5127761639/8000000 : ℚ) vp1010000001 := join_branches bp10100000010 bp10100000011
private noncomputable def vp10100000001_0 : Blocks := edgeBlocks% "full/vectors/10100000001-V-0000.bin"
noncomputable def vp10100000001 : Blocks := vp10100000001_0
theorem coverp10100000001 : Covers (-5123761639/4000000 : ℚ) vp10100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp10100000000_0 : Blocks := edgeBlocks% "full/vectors/10100000000-V-0000.bin"
noncomputable def vp10100000000 : Blocks := vp10100000000_0
theorem coverp10100000000 : Covers (-5119761639/4000000 : ℚ) vp10100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp1010000000_0 : Blocks := edgeBlocks% "full/vectors/1010000000-V-0000.bin"
private noncomputable def vp1010000000_1 : Blocks := edgeBlocks% "full/vectors/1010000000-V-0001.bin"
noncomputable def vp1010000000 : Blocks := (Blocks.join vp1010000000_0 vp1010000000_1)
private theorem bp10100000000 : Branch 0 (-5119761639/8000000 : ℚ) vp1010000000 := by
  apply branch_left_normalized (c:=vp10100000000) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5119761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-5119761639/4000000 : ℚ) by norm_num]
  exact coverp10100000000
private noncomputable def ep10100000001_0 : Blocks := edgeBlocks% "full/vectors/10100000001-E-0000.bin"
private noncomputable def ep10100000001_1 : Blocks := edgeBlocks% "full/vectors/10100000001-E-0001.bin"
noncomputable def ep10100000001 : Blocks := (Blocks.join ep10100000001_0 ep10100000001_1)
private theorem idp10100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010000000.list =
    C ((2:ℤ)^155) * horner X vp10100000001.list + horner X ep10100000001.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100000001 : Branch 1 (-5119761639/8000000 : ℚ) vp1010000000 := by
  apply branch_checked idp10100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-5119761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-5123761639/4000000 : ℚ) by norm_num]
  exact coverp10100000001
theorem coverp1010000000 : Covers (-5119761639/8000000 : ℚ) vp1010000000 := join_branches bp10100000000 bp10100000001
private noncomputable def vp101000000_0 : Blocks := edgeBlocks% "full/vectors/101000000-V-0000.bin"
private noncomputable def vp101000000_1 : Blocks := edgeBlocks% "full/vectors/101000000-V-0001.bin"
noncomputable def vp101000000 : Blocks := (Blocks.join vp101000000_0 vp101000000_1)
private theorem bp1010000000 : Branch 0 (-5119761639/16000000 : ℚ) vp101000000 := by
  apply branch_left_normalized (c:=vp1010000000) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-5119761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5119761639/8000000 : ℚ) by norm_num]
  exact coverp1010000000
private noncomputable def ep1010000001_0 : Blocks := edgeBlocks% "full/vectors/1010000001-E-0000.bin"
private noncomputable def ep1010000001_1 : Blocks := edgeBlocks% "full/vectors/1010000001-E-0001.bin"
noncomputable def ep1010000001 : Blocks := (Blocks.join ep1010000001_0 ep1010000001_1)
private theorem idp1010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101000000.list =
    C ((2:ℤ)^288) * horner X vp1010000001.list + horner X ep1010000001.list := by
  exact edge_identity (B := (2:ℤ)^460) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010000001 : Branch 1 (-5119761639/16000000 : ℚ) vp101000000 := by
  apply branch_checked idp1010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-5119761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5127761639/8000000 : ℚ) by norm_num]
  exact coverp1010000001
theorem coverp101000000 : Covers (-5119761639/16000000 : ℚ) vp101000000 := join_branches bp1010000000 bp1010000001
private noncomputable def vp10100000_0 : Blocks := edgeBlocks% "full/vectors/10100000-V-0000.bin"
private noncomputable def vp10100000_1 : Blocks := edgeBlocks% "full/vectors/10100000-V-0001.bin"
private noncomputable def vp10100000_2 : Blocks := edgeBlocks% "full/vectors/10100000-V-0002.bin"
private noncomputable def vp10100000_3 : Blocks := edgeBlocks% "full/vectors/10100000-V-0003.bin"
noncomputable def vp10100000 : Blocks := (Blocks.join (Blocks.join vp10100000_0 vp10100000_1) (Blocks.join vp10100000_2 vp10100000_3))
private theorem bp101000000 : Branch 0 (-5119761639/32000000 : ℚ) vp10100000 := by
  apply branch_left_normalized (c:=vp101000000) (k:=0) (m:=241) (by decide +kernel)
  rw [show 2*(-5119761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5119761639/16000000 : ℚ) by norm_num]
  exact coverp101000000
private noncomputable def ep101000001_0 : Blocks := edgeBlocks% "full/vectors/101000001-E-0000.bin"
private noncomputable def ep101000001_1 : Blocks := edgeBlocks% "full/vectors/101000001-E-0001.bin"
private noncomputable def ep101000001_2 : Blocks := edgeBlocks% "full/vectors/101000001-E-0002.bin"
private noncomputable def ep101000001_3 : Blocks := edgeBlocks% "full/vectors/101000001-E-0003.bin"
noncomputable def ep101000001 : Blocks := (Blocks.join (Blocks.join ep101000001_0 ep101000001_1) (Blocks.join ep101000001_2 ep101000001_3))
private theorem idp101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10100000.list =
    C ((2:ℤ)^554) * horner X vp101000001.list + horner X ep101000001.list := by
  exact edge_identity (B := (2:ℤ)^796) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101000001 : Branch 1 (-5119761639/32000000 : ℚ) vp10100000 := by
  apply branch_checked idp101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-5119761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5135761639/16000000 : ℚ) by norm_num]
  exact coverp101000001
theorem coverp10100000 : Covers (-5119761639/32000000 : ℚ) vp10100000 := join_branches bp101000000 bp101000001
private noncomputable def vp1010000_0 : Blocks := edgeBlocks% "full/vectors/1010000-V-0000.bin"
private noncomputable def vp1010000_1 : Blocks := edgeBlocks% "full/vectors/1010000-V-0001.bin"
private noncomputable def vp1010000_2 : Blocks := edgeBlocks% "full/vectors/1010000-V-0002.bin"
private noncomputable def vp1010000_3 : Blocks := edgeBlocks% "full/vectors/1010000-V-0003.bin"
private noncomputable def vp1010000_4 : Blocks := edgeBlocks% "full/vectors/1010000-V-0004.bin"
private noncomputable def vp1010000_5 : Blocks := edgeBlocks% "full/vectors/1010000-V-0005.bin"
private noncomputable def vp1010000_6 : Blocks := edgeBlocks% "full/vectors/1010000-V-0006.bin"
noncomputable def vp1010000 : Blocks := (Blocks.join (Blocks.join vp1010000_0 (Blocks.join vp1010000_1 vp1010000_2)) (Blocks.join (Blocks.join vp1010000_3 vp1010000_4) (Blocks.join vp1010000_5 vp1010000_6)))
private theorem bp10100000 : Branch 0 (-5119761639/64000000 : ℚ) vp1010000 := by
  apply branch_left_normalized (c:=vp10100000) (k:=0) (m:=460) (by decide +kernel)
  rw [show 2*(-5119761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5119761639/32000000 : ℚ) by norm_num]
  exact coverp10100000
private noncomputable def ep10100001_0 : Blocks := edgeBlocks% "full/vectors/10100001-E-0000.bin"
private noncomputable def ep10100001_1 : Blocks := edgeBlocks% "full/vectors/10100001-E-0001.bin"
private noncomputable def ep10100001_2 : Blocks := edgeBlocks% "full/vectors/10100001-E-0002.bin"
private noncomputable def ep10100001_3 : Blocks := edgeBlocks% "full/vectors/10100001-E-0003.bin"
private noncomputable def ep10100001_4 : Blocks := edgeBlocks% "full/vectors/10100001-E-0004.bin"
private noncomputable def ep10100001_5 : Blocks := edgeBlocks% "full/vectors/10100001-E-0005.bin"
private noncomputable def ep10100001_6 : Blocks := edgeBlocks% "full/vectors/10100001-E-0006.bin"
noncomputable def ep10100001 : Blocks := (Blocks.join (Blocks.join ep10100001_0 (Blocks.join ep10100001_1 ep10100001_2)) (Blocks.join (Blocks.join ep10100001_3 ep10100001_4) (Blocks.join ep10100001_5 ep10100001_6)))
private theorem idp10100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010000.list =
    C ((2:ℤ)^1076) * horner X vp10100001.list + horner X ep10100001.list := by
  exact edge_identity (B := (2:ℤ)^1457) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10100001 : Branch 1 (-5119761639/64000000 : ℚ) vp1010000 := by
  apply branch_checked idp10100001 (by positivity) (by decide +kernel)
  rw [show 2*(-5119761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5151761639/32000000 : ℚ) by norm_num]
  exact coverp10100001
theorem coverp1010000 : Covers (-5119761639/64000000 : ℚ) vp1010000 := join_branches bp10100000 bp10100001
private noncomputable def vp101000_0 : Blocks := edgeBlocks% "full/vectors/101000-V-0000.bin"
private noncomputable def vp101000_1 : Blocks := edgeBlocks% "full/vectors/101000-V-0001.bin"
private noncomputable def vp101000_2 : Blocks := edgeBlocks% "full/vectors/101000-V-0002.bin"
private noncomputable def vp101000_3 : Blocks := edgeBlocks% "full/vectors/101000-V-0003.bin"
private noncomputable def vp101000_4 : Blocks := edgeBlocks% "full/vectors/101000-V-0004.bin"
private noncomputable def vp101000_5 : Blocks := edgeBlocks% "full/vectors/101000-V-0005.bin"
private noncomputable def vp101000_6 : Blocks := edgeBlocks% "full/vectors/101000-V-0006.bin"
private noncomputable def vp101000_7 : Blocks := edgeBlocks% "full/vectors/101000-V-0007.bin"
private noncomputable def vp101000_8 : Blocks := edgeBlocks% "full/vectors/101000-V-0008.bin"
private noncomputable def vp101000_9 : Blocks := edgeBlocks% "full/vectors/101000-V-0009.bin"
private noncomputable def vp101000_10 : Blocks := edgeBlocks% "full/vectors/101000-V-0010.bin"
private noncomputable def vp101000_11 : Blocks := edgeBlocks% "full/vectors/101000-V-0011.bin"
private noncomputable def vp101000_12 : Blocks := edgeBlocks% "full/vectors/101000-V-0012.bin"
private noncomputable def vp101000_13 : Blocks := edgeBlocks% "full/vectors/101000-V-0013.bin"
noncomputable def vp101000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp101000_0 (Blocks.join vp101000_1 vp101000_2)) (Blocks.join (Blocks.join vp101000_3 vp101000_4) (Blocks.join vp101000_5 vp101000_6))) (Blocks.join (Blocks.join vp101000_7 (Blocks.join vp101000_8 vp101000_9)) (Blocks.join (Blocks.join vp101000_10 vp101000_11) (Blocks.join vp101000_12 vp101000_13))))
private theorem bp1010000 : Branch 0 (-5119761639/128000000 : ℚ) vp101000 := by
  apply branch_left_normalized (c:=vp1010000) (k:=0) (m:=890) (by decide +kernel)
  rw [show 2*(-5119761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-5119761639/64000000 : ℚ) by norm_num]
  exact coverp1010000
private noncomputable def ep1010001_0 : Blocks := edgeBlocks% "full/vectors/1010001-E-0000.bin"
private noncomputable def ep1010001_1 : Blocks := edgeBlocks% "full/vectors/1010001-E-0001.bin"
private noncomputable def ep1010001_2 : Blocks := edgeBlocks% "full/vectors/1010001-E-0002.bin"
private noncomputable def ep1010001_3 : Blocks := edgeBlocks% "full/vectors/1010001-E-0003.bin"
private noncomputable def ep1010001_4 : Blocks := edgeBlocks% "full/vectors/1010001-E-0004.bin"
private noncomputable def ep1010001_5 : Blocks := edgeBlocks% "full/vectors/1010001-E-0005.bin"
private noncomputable def ep1010001_6 : Blocks := edgeBlocks% "full/vectors/1010001-E-0006.bin"
private noncomputable def ep1010001_7 : Blocks := edgeBlocks% "full/vectors/1010001-E-0007.bin"
private noncomputable def ep1010001_8 : Blocks := edgeBlocks% "full/vectors/1010001-E-0008.bin"
private noncomputable def ep1010001_9 : Blocks := edgeBlocks% "full/vectors/1010001-E-0009.bin"
private noncomputable def ep1010001_10 : Blocks := edgeBlocks% "full/vectors/1010001-E-0010.bin"
private noncomputable def ep1010001_11 : Blocks := edgeBlocks% "full/vectors/1010001-E-0011.bin"
private noncomputable def ep1010001_12 : Blocks := edgeBlocks% "full/vectors/1010001-E-0012.bin"
private noncomputable def ep1010001_13 : Blocks := edgeBlocks% "full/vectors/1010001-E-0013.bin"
noncomputable def ep1010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1010001_0 (Blocks.join ep1010001_1 ep1010001_2)) (Blocks.join (Blocks.join ep1010001_3 ep1010001_4) (Blocks.join ep1010001_5 ep1010001_6))) (Blocks.join (Blocks.join ep1010001_7 (Blocks.join ep1010001_8 ep1010001_9)) (Blocks.join (Blocks.join ep1010001_10 ep1010001_11) (Blocks.join ep1010001_12 ep1010001_13))))
private theorem idp1010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101000.list =
    C ((2:ℤ)^2106) * horner X vp1010001.list + horner X ep1010001.list := by
  exact edge_identity (B := (2:ℤ)^2763) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1010001 : Branch 1 (-5119761639/128000000 : ℚ) vp101000 := by
  apply branch_checked idp1010001 (by positivity) (by decide +kernel)
  rw [show 2*(-5119761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-5183761639/64000000 : ℚ) by norm_num]
  exact coverp1010001
theorem coverp101000 : Covers (-5119761639/128000000 : ℚ) vp101000 := join_branches bp1010000 bp1010001
private noncomputable def vp10100_0 : Blocks := edgeBlocks% "full/vectors/10100-V-0000.bin"
private noncomputable def vp10100_1 : Blocks := edgeBlocks% "full/vectors/10100-V-0001.bin"
private noncomputable def vp10100_2 : Blocks := edgeBlocks% "full/vectors/10100-V-0002.bin"
private noncomputable def vp10100_3 : Blocks := edgeBlocks% "full/vectors/10100-V-0003.bin"
private noncomputable def vp10100_4 : Blocks := edgeBlocks% "full/vectors/10100-V-0004.bin"
private noncomputable def vp10100_5 : Blocks := edgeBlocks% "full/vectors/10100-V-0005.bin"
private noncomputable def vp10100_6 : Blocks := edgeBlocks% "full/vectors/10100-V-0006.bin"
private noncomputable def vp10100_7 : Blocks := edgeBlocks% "full/vectors/10100-V-0007.bin"
private noncomputable def vp10100_8 : Blocks := edgeBlocks% "full/vectors/10100-V-0008.bin"
private noncomputable def vp10100_9 : Blocks := edgeBlocks% "full/vectors/10100-V-0009.bin"
private noncomputable def vp10100_10 : Blocks := edgeBlocks% "full/vectors/10100-V-0010.bin"
private noncomputable def vp10100_11 : Blocks := edgeBlocks% "full/vectors/10100-V-0011.bin"
private noncomputable def vp10100_12 : Blocks := edgeBlocks% "full/vectors/10100-V-0012.bin"
private noncomputable def vp10100_13 : Blocks := edgeBlocks% "full/vectors/10100-V-0013.bin"
private noncomputable def vp10100_14 : Blocks := edgeBlocks% "full/vectors/10100-V-0014.bin"
private noncomputable def vp10100_15 : Blocks := edgeBlocks% "full/vectors/10100-V-0015.bin"
private noncomputable def vp10100_16 : Blocks := edgeBlocks% "full/vectors/10100-V-0016.bin"
private noncomputable def vp10100_17 : Blocks := edgeBlocks% "full/vectors/10100-V-0017.bin"
private noncomputable def vp10100_18 : Blocks := edgeBlocks% "full/vectors/10100-V-0018.bin"
private noncomputable def vp10100_19 : Blocks := edgeBlocks% "full/vectors/10100-V-0019.bin"
private noncomputable def vp10100_20 : Blocks := edgeBlocks% "full/vectors/10100-V-0020.bin"
private noncomputable def vp10100_21 : Blocks := edgeBlocks% "full/vectors/10100-V-0021.bin"
private noncomputable def vp10100_22 : Blocks := edgeBlocks% "full/vectors/10100-V-0022.bin"
private noncomputable def vp10100_23 : Blocks := edgeBlocks% "full/vectors/10100-V-0023.bin"
private noncomputable def vp10100_24 : Blocks := edgeBlocks% "full/vectors/10100-V-0024.bin"
private noncomputable def vp10100_25 : Blocks := edgeBlocks% "full/vectors/10100-V-0025.bin"
private noncomputable def vp10100_26 : Blocks := edgeBlocks% "full/vectors/10100-V-0026.bin"
noncomputable def vp10100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp10100_0 (Blocks.join vp10100_1 vp10100_2)) (Blocks.join vp10100_3 (Blocks.join vp10100_4 vp10100_5))) (Blocks.join (Blocks.join vp10100_6 (Blocks.join vp10100_7 vp10100_8)) (Blocks.join (Blocks.join vp10100_9 vp10100_10) (Blocks.join vp10100_11 vp10100_12)))) (Blocks.join (Blocks.join (Blocks.join vp10100_13 (Blocks.join vp10100_14 vp10100_15)) (Blocks.join (Blocks.join vp10100_16 vp10100_17) (Blocks.join vp10100_18 vp10100_19))) (Blocks.join (Blocks.join vp10100_20 (Blocks.join vp10100_21 vp10100_22)) (Blocks.join (Blocks.join vp10100_23 vp10100_24) (Blocks.join vp10100_25 vp10100_26)))))
private theorem bp101000 : Branch 0 (-5119761639/256000000 : ℚ) vp10100 := by
  apply branch_left_normalized (c:=vp101000) (k:=0) (m:=1735) (by decide +kernel)
  rw [show 2*(-5119761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-5119761639/128000000 : ℚ) by norm_num]
  exact coverp101000
private noncomputable def ep101001_0 : Blocks := edgeBlocks% "full/vectors/101001-E-0000.bin"
private noncomputable def ep101001_1 : Blocks := edgeBlocks% "full/vectors/101001-E-0001.bin"
private noncomputable def ep101001_2 : Blocks := edgeBlocks% "full/vectors/101001-E-0002.bin"
private noncomputable def ep101001_3 : Blocks := edgeBlocks% "full/vectors/101001-E-0003.bin"
private noncomputable def ep101001_4 : Blocks := edgeBlocks% "full/vectors/101001-E-0004.bin"
private noncomputable def ep101001_5 : Blocks := edgeBlocks% "full/vectors/101001-E-0005.bin"
private noncomputable def ep101001_6 : Blocks := edgeBlocks% "full/vectors/101001-E-0006.bin"
private noncomputable def ep101001_7 : Blocks := edgeBlocks% "full/vectors/101001-E-0007.bin"
private noncomputable def ep101001_8 : Blocks := edgeBlocks% "full/vectors/101001-E-0008.bin"
private noncomputable def ep101001_9 : Blocks := edgeBlocks% "full/vectors/101001-E-0009.bin"
private noncomputable def ep101001_10 : Blocks := edgeBlocks% "full/vectors/101001-E-0010.bin"
private noncomputable def ep101001_11 : Blocks := edgeBlocks% "full/vectors/101001-E-0011.bin"
private noncomputable def ep101001_12 : Blocks := edgeBlocks% "full/vectors/101001-E-0012.bin"
private noncomputable def ep101001_13 : Blocks := edgeBlocks% "full/vectors/101001-E-0013.bin"
private noncomputable def ep101001_14 : Blocks := edgeBlocks% "full/vectors/101001-E-0014.bin"
private noncomputable def ep101001_15 : Blocks := edgeBlocks% "full/vectors/101001-E-0015.bin"
private noncomputable def ep101001_16 : Blocks := edgeBlocks% "full/vectors/101001-E-0016.bin"
private noncomputable def ep101001_17 : Blocks := edgeBlocks% "full/vectors/101001-E-0017.bin"
private noncomputable def ep101001_18 : Blocks := edgeBlocks% "full/vectors/101001-E-0018.bin"
private noncomputable def ep101001_19 : Blocks := edgeBlocks% "full/vectors/101001-E-0019.bin"
private noncomputable def ep101001_20 : Blocks := edgeBlocks% "full/vectors/101001-E-0020.bin"
private noncomputable def ep101001_21 : Blocks := edgeBlocks% "full/vectors/101001-E-0021.bin"
private noncomputable def ep101001_22 : Blocks := edgeBlocks% "full/vectors/101001-E-0022.bin"
private noncomputable def ep101001_23 : Blocks := edgeBlocks% "full/vectors/101001-E-0023.bin"
private noncomputable def ep101001_24 : Blocks := edgeBlocks% "full/vectors/101001-E-0024.bin"
private noncomputable def ep101001_25 : Blocks := edgeBlocks% "full/vectors/101001-E-0025.bin"
private noncomputable def ep101001_26 : Blocks := edgeBlocks% "full/vectors/101001-E-0026.bin"
noncomputable def ep101001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep101001_0 (Blocks.join ep101001_1 ep101001_2)) (Blocks.join ep101001_3 (Blocks.join ep101001_4 ep101001_5))) (Blocks.join (Blocks.join ep101001_6 (Blocks.join ep101001_7 ep101001_8)) (Blocks.join (Blocks.join ep101001_9 ep101001_10) (Blocks.join ep101001_11 ep101001_12)))) (Blocks.join (Blocks.join (Blocks.join ep101001_13 (Blocks.join ep101001_14 ep101001_15)) (Blocks.join (Blocks.join ep101001_16 ep101001_17) (Blocks.join ep101001_18 ep101001_19))) (Blocks.join (Blocks.join ep101001_20 (Blocks.join ep101001_21 ep101001_22)) (Blocks.join (Blocks.join ep101001_23 ep101001_24) (Blocks.join ep101001_25 ep101001_26)))))
private def ptsp101001 : List ℤ := [((2:ℤ)^3575+0),((2:ℤ)^3575+1)]
private theorem boundp101001 : 2^vp10100.size*absSum vp10100.list + ((2:ℤ)^4095*absSum vp101001.list+absSum ep101001.list) < (2:ℤ)^5290 := by decide +kernel
private theorem pointp101001_0 : fastHom 1 ((2:ℤ)^3575+0) vp10100 = ((2:ℤ)^4095)*vp101001.subst ((2:ℤ)^3575+0)+ep101001.subst ((2:ℤ)^3575+0) := by decide +kernel
private theorem pointp101001_1 : fastHom 1 ((2:ℤ)^3575+1) vp10100 = ((2:ℤ)^4095)*vp101001.subst ((2:ℤ)^3575+1)+ep101001.subst ((2:ℤ)^3575+1) := by decide +kernel
private theorem checkp101001 (x:ℤ) (hx:x ∈ ptsp101001) : fastHom 1 x vp10100 = ((2:ℤ)^4095)*vp101001.subst x+ep101001.subst x := by
  simp only [ptsp101001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp101001_0
  · exact pointp101001_1
private theorem idp101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10100.list =
    C ((2:ℤ)^4095) * horner X vp101001.list + horner X ep101001.list := by
  apply edge_identity (B := (2:ℤ)^5290) (by decide) (by positivity) (by positivity) boundp101001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp101001 (by decide +kernel)
  · have h : ptsp101001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp101001.trans_le (by decide +kernel)
  · exact checkp101001
private theorem bp101001 : Branch 1 (-5119761639/256000000 : ℚ) vp10100 := by
  apply branch_checked idp101001 (by positivity) (by decide +kernel)
  rw [show 2*(-5119761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-5247761639/128000000 : ℚ) by norm_num]
  exact coverp101001
theorem coverp10100 : Covers (-5119761639/256000000 : ℚ) vp10100 := join_branches bp101000 bp101001
private noncomputable def vp1010_0 : Blocks := edgeBlocks% "full/vectors/1010-V-0000.bin"
private noncomputable def vp1010_1 : Blocks := edgeBlocks% "full/vectors/1010-V-0001.bin"
private noncomputable def vp1010_2 : Blocks := edgeBlocks% "full/vectors/1010-V-0002.bin"
private noncomputable def vp1010_3 : Blocks := edgeBlocks% "full/vectors/1010-V-0003.bin"
private noncomputable def vp1010_4 : Blocks := edgeBlocks% "full/vectors/1010-V-0004.bin"
private noncomputable def vp1010_5 : Blocks := edgeBlocks% "full/vectors/1010-V-0005.bin"
private noncomputable def vp1010_6 : Blocks := edgeBlocks% "full/vectors/1010-V-0006.bin"
private noncomputable def vp1010_7 : Blocks := edgeBlocks% "full/vectors/1010-V-0007.bin"
private noncomputable def vp1010_8 : Blocks := edgeBlocks% "full/vectors/1010-V-0008.bin"
private noncomputable def vp1010_9 : Blocks := edgeBlocks% "full/vectors/1010-V-0009.bin"
private noncomputable def vp1010_10 : Blocks := edgeBlocks% "full/vectors/1010-V-0010.bin"
private noncomputable def vp1010_11 : Blocks := edgeBlocks% "full/vectors/1010-V-0011.bin"
private noncomputable def vp1010_12 : Blocks := edgeBlocks% "full/vectors/1010-V-0012.bin"
private noncomputable def vp1010_13 : Blocks := edgeBlocks% "full/vectors/1010-V-0013.bin"
private noncomputable def vp1010_14 : Blocks := edgeBlocks% "full/vectors/1010-V-0014.bin"
private noncomputable def vp1010_15 : Blocks := edgeBlocks% "full/vectors/1010-V-0015.bin"
private noncomputable def vp1010_16 : Blocks := edgeBlocks% "full/vectors/1010-V-0016.bin"
private noncomputable def vp1010_17 : Blocks := edgeBlocks% "full/vectors/1010-V-0017.bin"
private noncomputable def vp1010_18 : Blocks := edgeBlocks% "full/vectors/1010-V-0018.bin"
private noncomputable def vp1010_19 : Blocks := edgeBlocks% "full/vectors/1010-V-0019.bin"
private noncomputable def vp1010_20 : Blocks := edgeBlocks% "full/vectors/1010-V-0020.bin"
private noncomputable def vp1010_21 : Blocks := edgeBlocks% "full/vectors/1010-V-0021.bin"
private noncomputable def vp1010_22 : Blocks := edgeBlocks% "full/vectors/1010-V-0022.bin"
private noncomputable def vp1010_23 : Blocks := edgeBlocks% "full/vectors/1010-V-0023.bin"
private noncomputable def vp1010_24 : Blocks := edgeBlocks% "full/vectors/1010-V-0024.bin"
private noncomputable def vp1010_25 : Blocks := edgeBlocks% "full/vectors/1010-V-0025.bin"
private noncomputable def vp1010_26 : Blocks := edgeBlocks% "full/vectors/1010-V-0026.bin"
private noncomputable def vp1010_27 : Blocks := edgeBlocks% "full/vectors/1010-V-0027.bin"
private noncomputable def vp1010_28 : Blocks := edgeBlocks% "full/vectors/1010-V-0028.bin"
private noncomputable def vp1010_29 : Blocks := edgeBlocks% "full/vectors/1010-V-0029.bin"
private noncomputable def vp1010_30 : Blocks := edgeBlocks% "full/vectors/1010-V-0030.bin"
private noncomputable def vp1010_31 : Blocks := edgeBlocks% "full/vectors/1010-V-0031.bin"
private noncomputable def vp1010_32 : Blocks := edgeBlocks% "full/vectors/1010-V-0032.bin"
private noncomputable def vp1010_33 : Blocks := edgeBlocks% "full/vectors/1010-V-0033.bin"
private noncomputable def vp1010_34 : Blocks := edgeBlocks% "full/vectors/1010-V-0034.bin"
private noncomputable def vp1010_35 : Blocks := edgeBlocks% "full/vectors/1010-V-0035.bin"
private noncomputable def vp1010_36 : Blocks := edgeBlocks% "full/vectors/1010-V-0036.bin"
private noncomputable def vp1010_37 : Blocks := edgeBlocks% "full/vectors/1010-V-0037.bin"
private noncomputable def vp1010_38 : Blocks := edgeBlocks% "full/vectors/1010-V-0038.bin"
private noncomputable def vp1010_39 : Blocks := edgeBlocks% "full/vectors/1010-V-0039.bin"
private noncomputable def vp1010_40 : Blocks := edgeBlocks% "full/vectors/1010-V-0040.bin"
private noncomputable def vp1010_41 : Blocks := edgeBlocks% "full/vectors/1010-V-0041.bin"
private noncomputable def vp1010_42 : Blocks := edgeBlocks% "full/vectors/1010-V-0042.bin"
private noncomputable def vp1010_43 : Blocks := edgeBlocks% "full/vectors/1010-V-0043.bin"
private noncomputable def vp1010_44 : Blocks := edgeBlocks% "full/vectors/1010-V-0044.bin"
private noncomputable def vp1010_45 : Blocks := edgeBlocks% "full/vectors/1010-V-0045.bin"
private noncomputable def vp1010_46 : Blocks := edgeBlocks% "full/vectors/1010-V-0046.bin"
private noncomputable def vp1010_47 : Blocks := edgeBlocks% "full/vectors/1010-V-0047.bin"
private noncomputable def vp1010_48 : Blocks := edgeBlocks% "full/vectors/1010-V-0048.bin"
private noncomputable def vp1010_49 : Blocks := edgeBlocks% "full/vectors/1010-V-0049.bin"
noncomputable def vp1010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1010_0 (Blocks.join vp1010_1 vp1010_2)) (Blocks.join vp1010_3 (Blocks.join vp1010_4 vp1010_5))) (Blocks.join (Blocks.join vp1010_6 (Blocks.join vp1010_7 vp1010_8)) (Blocks.join vp1010_9 (Blocks.join vp1010_10 vp1010_11)))) (Blocks.join (Blocks.join (Blocks.join vp1010_12 (Blocks.join vp1010_13 vp1010_14)) (Blocks.join vp1010_15 (Blocks.join vp1010_16 vp1010_17))) (Blocks.join (Blocks.join vp1010_18 (Blocks.join vp1010_19 vp1010_20)) (Blocks.join (Blocks.join vp1010_21 vp1010_22) (Blocks.join vp1010_23 vp1010_24))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1010_25 (Blocks.join vp1010_26 vp1010_27)) (Blocks.join vp1010_28 (Blocks.join vp1010_29 vp1010_30))) (Blocks.join (Blocks.join vp1010_31 (Blocks.join vp1010_32 vp1010_33)) (Blocks.join vp1010_34 (Blocks.join vp1010_35 vp1010_36)))) (Blocks.join (Blocks.join (Blocks.join vp1010_37 (Blocks.join vp1010_38 vp1010_39)) (Blocks.join vp1010_40 (Blocks.join vp1010_41 vp1010_42))) (Blocks.join (Blocks.join vp1010_43 (Blocks.join vp1010_44 vp1010_45)) (Blocks.join (Blocks.join vp1010_46 vp1010_47) (Blocks.join vp1010_48 vp1010_49))))))
private theorem bp10100 : Branch 0 (-5119761639/512000000 : ℚ) vp1010 := by
  apply branch_left_normalized (c:=vp10100) (k:=0) (m:=3355) (by decide +kernel)
  rw [show 2*(-5119761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-5119761639/256000000 : ℚ) by norm_num]
  exact coverp10100
private noncomputable def ep10101_0 : Blocks := edgeBlocks% "full/vectors/10101-E-0000.bin"
private noncomputable def ep10101_1 : Blocks := edgeBlocks% "full/vectors/10101-E-0001.bin"
private noncomputable def ep10101_2 : Blocks := edgeBlocks% "full/vectors/10101-E-0002.bin"
private noncomputable def ep10101_3 : Blocks := edgeBlocks% "full/vectors/10101-E-0003.bin"
private noncomputable def ep10101_4 : Blocks := edgeBlocks% "full/vectors/10101-E-0004.bin"
private noncomputable def ep10101_5 : Blocks := edgeBlocks% "full/vectors/10101-E-0005.bin"
private noncomputable def ep10101_6 : Blocks := edgeBlocks% "full/vectors/10101-E-0006.bin"
private noncomputable def ep10101_7 : Blocks := edgeBlocks% "full/vectors/10101-E-0007.bin"
private noncomputable def ep10101_8 : Blocks := edgeBlocks% "full/vectors/10101-E-0008.bin"
private noncomputable def ep10101_9 : Blocks := edgeBlocks% "full/vectors/10101-E-0009.bin"
private noncomputable def ep10101_10 : Blocks := edgeBlocks% "full/vectors/10101-E-0010.bin"
private noncomputable def ep10101_11 : Blocks := edgeBlocks% "full/vectors/10101-E-0011.bin"
private noncomputable def ep10101_12 : Blocks := edgeBlocks% "full/vectors/10101-E-0012.bin"
private noncomputable def ep10101_13 : Blocks := edgeBlocks% "full/vectors/10101-E-0013.bin"
private noncomputable def ep10101_14 : Blocks := edgeBlocks% "full/vectors/10101-E-0014.bin"
private noncomputable def ep10101_15 : Blocks := edgeBlocks% "full/vectors/10101-E-0015.bin"
private noncomputable def ep10101_16 : Blocks := edgeBlocks% "full/vectors/10101-E-0016.bin"
private noncomputable def ep10101_17 : Blocks := edgeBlocks% "full/vectors/10101-E-0017.bin"
private noncomputable def ep10101_18 : Blocks := edgeBlocks% "full/vectors/10101-E-0018.bin"
private noncomputable def ep10101_19 : Blocks := edgeBlocks% "full/vectors/10101-E-0019.bin"
private noncomputable def ep10101_20 : Blocks := edgeBlocks% "full/vectors/10101-E-0020.bin"
private noncomputable def ep10101_21 : Blocks := edgeBlocks% "full/vectors/10101-E-0021.bin"
private noncomputable def ep10101_22 : Blocks := edgeBlocks% "full/vectors/10101-E-0022.bin"
private noncomputable def ep10101_23 : Blocks := edgeBlocks% "full/vectors/10101-E-0023.bin"
private noncomputable def ep10101_24 : Blocks := edgeBlocks% "full/vectors/10101-E-0024.bin"
private noncomputable def ep10101_25 : Blocks := edgeBlocks% "full/vectors/10101-E-0025.bin"
private noncomputable def ep10101_26 : Blocks := edgeBlocks% "full/vectors/10101-E-0026.bin"
private noncomputable def ep10101_27 : Blocks := edgeBlocks% "full/vectors/10101-E-0027.bin"
private noncomputable def ep10101_28 : Blocks := edgeBlocks% "full/vectors/10101-E-0028.bin"
private noncomputable def ep10101_29 : Blocks := edgeBlocks% "full/vectors/10101-E-0029.bin"
private noncomputable def ep10101_30 : Blocks := edgeBlocks% "full/vectors/10101-E-0030.bin"
private noncomputable def ep10101_31 : Blocks := edgeBlocks% "full/vectors/10101-E-0031.bin"
private noncomputable def ep10101_32 : Blocks := edgeBlocks% "full/vectors/10101-E-0032.bin"
private noncomputable def ep10101_33 : Blocks := edgeBlocks% "full/vectors/10101-E-0033.bin"
private noncomputable def ep10101_34 : Blocks := edgeBlocks% "full/vectors/10101-E-0034.bin"
private noncomputable def ep10101_35 : Blocks := edgeBlocks% "full/vectors/10101-E-0035.bin"
private noncomputable def ep10101_36 : Blocks := edgeBlocks% "full/vectors/10101-E-0036.bin"
private noncomputable def ep10101_37 : Blocks := edgeBlocks% "full/vectors/10101-E-0037.bin"
private noncomputable def ep10101_38 : Blocks := edgeBlocks% "full/vectors/10101-E-0038.bin"
private noncomputable def ep10101_39 : Blocks := edgeBlocks% "full/vectors/10101-E-0039.bin"
private noncomputable def ep10101_40 : Blocks := edgeBlocks% "full/vectors/10101-E-0040.bin"
private noncomputable def ep10101_41 : Blocks := edgeBlocks% "full/vectors/10101-E-0041.bin"
private noncomputable def ep10101_42 : Blocks := edgeBlocks% "full/vectors/10101-E-0042.bin"
private noncomputable def ep10101_43 : Blocks := edgeBlocks% "full/vectors/10101-E-0043.bin"
private noncomputable def ep10101_44 : Blocks := edgeBlocks% "full/vectors/10101-E-0044.bin"
private noncomputable def ep10101_45 : Blocks := edgeBlocks% "full/vectors/10101-E-0045.bin"
private noncomputable def ep10101_46 : Blocks := edgeBlocks% "full/vectors/10101-E-0046.bin"
private noncomputable def ep10101_47 : Blocks := edgeBlocks% "full/vectors/10101-E-0047.bin"
private noncomputable def ep10101_48 : Blocks := edgeBlocks% "full/vectors/10101-E-0048.bin"
private noncomputable def ep10101_49 : Blocks := edgeBlocks% "full/vectors/10101-E-0049.bin"
noncomputable def ep10101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep10101_0 (Blocks.join ep10101_1 ep10101_2)) (Blocks.join ep10101_3 (Blocks.join ep10101_4 ep10101_5))) (Blocks.join (Blocks.join ep10101_6 (Blocks.join ep10101_7 ep10101_8)) (Blocks.join ep10101_9 (Blocks.join ep10101_10 ep10101_11)))) (Blocks.join (Blocks.join (Blocks.join ep10101_12 (Blocks.join ep10101_13 ep10101_14)) (Blocks.join ep10101_15 (Blocks.join ep10101_16 ep10101_17))) (Blocks.join (Blocks.join ep10101_18 (Blocks.join ep10101_19 ep10101_20)) (Blocks.join (Blocks.join ep10101_21 ep10101_22) (Blocks.join ep10101_23 ep10101_24))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep10101_25 (Blocks.join ep10101_26 ep10101_27)) (Blocks.join ep10101_28 (Blocks.join ep10101_29 ep10101_30))) (Blocks.join (Blocks.join ep10101_31 (Blocks.join ep10101_32 ep10101_33)) (Blocks.join ep10101_34 (Blocks.join ep10101_35 ep10101_36)))) (Blocks.join (Blocks.join (Blocks.join ep10101_37 (Blocks.join ep10101_38 ep10101_39)) (Blocks.join ep10101_40 (Blocks.join ep10101_41 ep10101_42))) (Blocks.join (Blocks.join ep10101_43 (Blocks.join ep10101_44 ep10101_45)) (Blocks.join (Blocks.join ep10101_46 ep10101_47) (Blocks.join ep10101_48 ep10101_49))))))
private def ptsp10101 : List ℤ := [((2:ℤ)^1899+0),((2:ℤ)^1899+1),((2:ℤ)^1899+2),((2:ℤ)^1899+3),((2:ℤ)^1899+4),((2:ℤ)^1899+5)]
private theorem boundp10101 : 2^vp1010.size*absSum vp1010.list + ((2:ℤ)^7797*absSum vp10101.list+absSum ep10101.list) < (2:ℤ)^10014 := by decide +kernel
private theorem pointp10101_0 : fastHom 1 ((2:ℤ)^1899+0) vp1010 = ((2:ℤ)^7797)*vp10101.subst ((2:ℤ)^1899+0)+ep10101.subst ((2:ℤ)^1899+0) := by decide +kernel
private theorem pointp10101_1 : fastHom 1 ((2:ℤ)^1899+1) vp1010 = ((2:ℤ)^7797)*vp10101.subst ((2:ℤ)^1899+1)+ep10101.subst ((2:ℤ)^1899+1) := by decide +kernel
private theorem pointp10101_2 : fastHom 1 ((2:ℤ)^1899+2) vp1010 = ((2:ℤ)^7797)*vp10101.subst ((2:ℤ)^1899+2)+ep10101.subst ((2:ℤ)^1899+2) := by decide +kernel
private theorem pointp10101_3 : fastHom 1 ((2:ℤ)^1899+3) vp1010 = ((2:ℤ)^7797)*vp10101.subst ((2:ℤ)^1899+3)+ep10101.subst ((2:ℤ)^1899+3) := by decide +kernel
private theorem pointp10101_4 : fastHom 1 ((2:ℤ)^1899+4) vp1010 = ((2:ℤ)^7797)*vp10101.subst ((2:ℤ)^1899+4)+ep10101.subst ((2:ℤ)^1899+4) := by decide +kernel
private theorem pointp10101_5 : fastHom 1 ((2:ℤ)^1899+5) vp1010 = ((2:ℤ)^7797)*vp10101.subst ((2:ℤ)^1899+5)+ep10101.subst ((2:ℤ)^1899+5) := by decide +kernel
private theorem checkp10101 (x:ℤ) (hx:x ∈ ptsp10101) : fastHom 1 x vp1010 = ((2:ℤ)^7797)*vp10101.subst x+ep10101.subst x := by
  simp only [ptsp10101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp10101_0
  · exact pointp10101_1
  · exact pointp10101_2
  · exact pointp10101_3
  · exact pointp10101_4
  · exact pointp10101_5
private theorem idp10101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1010.list =
    C ((2:ℤ)^7797) * horner X vp10101.list + horner X ep10101.list := by
  apply edge_identity (B := (2:ℤ)^10014) (by decide) (by positivity) (by positivity) boundp10101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp10101 (by decide +kernel)
  · have h : ptsp10101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp10101.trans_le (by decide +kernel)
  · exact checkp10101
private theorem bp10101 : Branch 1 (-5119761639/512000000 : ℚ) vp1010 := by
  apply branch_checked idp10101 (by positivity) (by decide +kernel)
  rw [show 2*(-5119761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-5375761639/256000000 : ℚ) by norm_num]
  exact coverp10101
theorem coverp1010 : Covers (-5119761639/512000000 : ℚ) vp1010 := join_branches bp10100 bp10101
end NextProof.EdgeFull

