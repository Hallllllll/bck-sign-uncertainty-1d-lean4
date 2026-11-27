import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00133

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp10010111111_0 : Blocks := edgeBlocks% "full/vectors/10010111111-V-0000.bin"
noncomputable def vp10010111111 : Blocks := vp10010111111_0
theorem coverp10010111111 : Covers (-4859761639/4000000 : ℚ) vp10010111111 := cover_leaf (by decide +kernel)
private noncomputable def vp10010111110_0 : Blocks := edgeBlocks% "full/vectors/10010111110-V-0000.bin"
noncomputable def vp10010111110 : Blocks := vp10010111110_0
theorem coverp10010111110 : Covers (-4855761639/4000000 : ℚ) vp10010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001011111_0 : Blocks := edgeBlocks% "full/vectors/1001011111-V-0000.bin"
private noncomputable def vp1001011111_1 : Blocks := edgeBlocks% "full/vectors/1001011111-V-0001.bin"
noncomputable def vp1001011111 : Blocks := (Blocks.join vp1001011111_0 vp1001011111_1)
private theorem bp10010111110 : Branch 0 (-4855761639/8000000 : ℚ) vp1001011111 := by
  apply branch_left_normalized (c:=vp10010111110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4855761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4855761639/4000000 : ℚ) by norm_num]
  exact coverp10010111110
private noncomputable def ep10010111111_0 : Blocks := edgeBlocks% "full/vectors/10010111111-E-0000.bin"
private noncomputable def ep10010111111_1 : Blocks := edgeBlocks% "full/vectors/10010111111-E-0001.bin"
noncomputable def ep10010111111 : Blocks := (Blocks.join ep10010111111_0 ep10010111111_1)
private theorem idp10010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001011111.list =
    C ((2:ℤ)^159) * horner X vp10010111111.list + horner X ep10010111111.list := by
  exact edge_identity (B := (2:ℤ)^297) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010111111 : Branch 1 (-4855761639/8000000 : ℚ) vp1001011111 := by
  apply branch_checked idp10010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-4855761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4859761639/4000000 : ℚ) by norm_num]
  exact coverp10010111111
theorem coverp1001011111 : Covers (-4855761639/8000000 : ℚ) vp1001011111 := join_branches bp10010111110 bp10010111111
private noncomputable def vp10010111101_0 : Blocks := edgeBlocks% "full/vectors/10010111101-V-0000.bin"
noncomputable def vp10010111101 : Blocks := vp10010111101_0
theorem coverp10010111101 : Covers (-4851761639/4000000 : ℚ) vp10010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp10010111100_0 : Blocks := edgeBlocks% "full/vectors/10010111100-V-0000.bin"
noncomputable def vp10010111100 : Blocks := vp10010111100_0
theorem coverp10010111100 : Covers (-4847761639/4000000 : ℚ) vp10010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp1001011110_0 : Blocks := edgeBlocks% "full/vectors/1001011110-V-0000.bin"
private noncomputable def vp1001011110_1 : Blocks := edgeBlocks% "full/vectors/1001011110-V-0001.bin"
noncomputable def vp1001011110 : Blocks := (Blocks.join vp1001011110_0 vp1001011110_1)
private theorem bp10010111100 : Branch 0 (-4847761639/8000000 : ℚ) vp1001011110 := by
  apply branch_left_normalized (c:=vp10010111100) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4847761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4847761639/4000000 : ℚ) by norm_num]
  exact coverp10010111100
private noncomputable def ep10010111101_0 : Blocks := edgeBlocks% "full/vectors/10010111101-E-0000.bin"
private noncomputable def ep10010111101_1 : Blocks := edgeBlocks% "full/vectors/10010111101-E-0001.bin"
noncomputable def ep10010111101 : Blocks := (Blocks.join ep10010111101_0 ep10010111101_1)
private theorem idp10010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001011110.list =
    C ((2:ℤ)^158) * horner X vp10010111101.list + horner X ep10010111101.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010111101 : Branch 1 (-4847761639/8000000 : ℚ) vp1001011110 := by
  apply branch_checked idp10010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-4847761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4851761639/4000000 : ℚ) by norm_num]
  exact coverp10010111101
theorem coverp1001011110 : Covers (-4847761639/8000000 : ℚ) vp1001011110 := join_branches bp10010111100 bp10010111101
private noncomputable def vp100101111_0 : Blocks := edgeBlocks% "full/vectors/100101111-V-0000.bin"
private noncomputable def vp100101111_1 : Blocks := edgeBlocks% "full/vectors/100101111-V-0001.bin"
noncomputable def vp100101111 : Blocks := (Blocks.join vp100101111_0 vp100101111_1)
private theorem bp1001011110 : Branch 0 (-4847761639/16000000 : ℚ) vp100101111 := by
  apply branch_left_normalized (c:=vp1001011110) (k:=0) (m:=134) (by decide +kernel)
  rw [show 2*(-4847761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4847761639/8000000 : ℚ) by norm_num]
  exact coverp1001011110
private noncomputable def ep1001011111_0 : Blocks := edgeBlocks% "full/vectors/1001011111-E-0000.bin"
private noncomputable def ep1001011111_1 : Blocks := edgeBlocks% "full/vectors/1001011111-E-0001.bin"
noncomputable def ep1001011111 : Blocks := (Blocks.join ep1001011111_0 ep1001011111_1)
private theorem idp1001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100101111.list =
    C ((2:ℤ)^294) * horner X vp1001011111.list + horner X ep1001011111.list := by
  exact edge_identity (B := (2:ℤ)^469) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001011111 : Branch 1 (-4847761639/16000000 : ℚ) vp100101111 := by
  apply branch_checked idp1001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-4847761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4855761639/8000000 : ℚ) by norm_num]
  exact coverp1001011111
theorem coverp100101111 : Covers (-4847761639/16000000 : ℚ) vp100101111 := join_branches bp1001011110 bp1001011111
private noncomputable def vp10010111011_0 : Blocks := edgeBlocks% "full/vectors/10010111011-V-0000.bin"
noncomputable def vp10010111011 : Blocks := vp10010111011_0
theorem coverp10010111011 : Covers (-4843761639/4000000 : ℚ) vp10010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp10010111010_0 : Blocks := edgeBlocks% "full/vectors/10010111010-V-0000.bin"
noncomputable def vp10010111010 : Blocks := vp10010111010_0
theorem coverp10010111010 : Covers (-4839761639/4000000 : ℚ) vp10010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001011101_0 : Blocks := edgeBlocks% "full/vectors/1001011101-V-0000.bin"
private noncomputable def vp1001011101_1 : Blocks := edgeBlocks% "full/vectors/1001011101-V-0001.bin"
noncomputable def vp1001011101 : Blocks := (Blocks.join vp1001011101_0 vp1001011101_1)
private theorem bp10010111010 : Branch 0 (-4839761639/8000000 : ℚ) vp1001011101 := by
  apply branch_left_normalized (c:=vp10010111010) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4839761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4839761639/4000000 : ℚ) by norm_num]
  exact coverp10010111010
private noncomputable def ep10010111011_0 : Blocks := edgeBlocks% "full/vectors/10010111011-E-0000.bin"
private noncomputable def ep10010111011_1 : Blocks := edgeBlocks% "full/vectors/10010111011-E-0001.bin"
noncomputable def ep10010111011 : Blocks := (Blocks.join ep10010111011_0 ep10010111011_1)
private theorem idp10010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001011101.list =
    C ((2:ℤ)^160) * horner X vp10010111011.list + horner X ep10010111011.list := by
  exact edge_identity (B := (2:ℤ)^298) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010111011 : Branch 1 (-4839761639/8000000 : ℚ) vp1001011101 := by
  apply branch_checked idp10010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-4839761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4843761639/4000000 : ℚ) by norm_num]
  exact coverp10010111011
theorem coverp1001011101 : Covers (-4839761639/8000000 : ℚ) vp1001011101 := join_branches bp10010111010 bp10010111011
private noncomputable def vp10010111001_0 : Blocks := edgeBlocks% "full/vectors/10010111001-V-0000.bin"
noncomputable def vp10010111001 : Blocks := vp10010111001_0
theorem coverp10010111001 : Covers (-4835761639/4000000 : ℚ) vp10010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp10010111000_0 : Blocks := edgeBlocks% "full/vectors/10010111000-V-0000.bin"
noncomputable def vp10010111000 : Blocks := vp10010111000_0
theorem coverp10010111000 : Covers (-4831761639/4000000 : ℚ) vp10010111000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001011100_0 : Blocks := edgeBlocks% "full/vectors/1001011100-V-0000.bin"
private noncomputable def vp1001011100_1 : Blocks := edgeBlocks% "full/vectors/1001011100-V-0001.bin"
noncomputable def vp1001011100 : Blocks := (Blocks.join vp1001011100_0 vp1001011100_1)
private theorem bp10010111000 : Branch 0 (-4831761639/8000000 : ℚ) vp1001011100 := by
  apply branch_left_normalized (c:=vp10010111000) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4831761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4831761639/4000000 : ℚ) by norm_num]
  exact coverp10010111000
private noncomputable def ep10010111001_0 : Blocks := edgeBlocks% "full/vectors/10010111001-E-0000.bin"
private noncomputable def ep10010111001_1 : Blocks := edgeBlocks% "full/vectors/10010111001-E-0001.bin"
noncomputable def ep10010111001 : Blocks := (Blocks.join ep10010111001_0 ep10010111001_1)
private theorem idp10010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001011100.list =
    C ((2:ℤ)^158) * horner X vp10010111001.list + horner X ep10010111001.list := by
  exact edge_identity (B := (2:ℤ)^297) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010111001 : Branch 1 (-4831761639/8000000 : ℚ) vp1001011100 := by
  apply branch_checked idp10010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-4831761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4835761639/4000000 : ℚ) by norm_num]
  exact coverp10010111001
theorem coverp1001011100 : Covers (-4831761639/8000000 : ℚ) vp1001011100 := join_branches bp10010111000 bp10010111001
private noncomputable def vp100101110_0 : Blocks := edgeBlocks% "full/vectors/100101110-V-0000.bin"
private noncomputable def vp100101110_1 : Blocks := edgeBlocks% "full/vectors/100101110-V-0001.bin"
noncomputable def vp100101110 : Blocks := (Blocks.join vp100101110_0 vp100101110_1)
private theorem bp1001011100 : Branch 0 (-4831761639/16000000 : ℚ) vp100101110 := by
  apply branch_left_normalized (c:=vp1001011100) (k:=0) (m:=134) (by decide +kernel)
  rw [show 2*(-4831761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4831761639/8000000 : ℚ) by norm_num]
  exact coverp1001011100
private noncomputable def ep1001011101_0 : Blocks := edgeBlocks% "full/vectors/1001011101-E-0000.bin"
private noncomputable def ep1001011101_1 : Blocks := edgeBlocks% "full/vectors/1001011101-E-0001.bin"
noncomputable def ep1001011101 : Blocks := (Blocks.join ep1001011101_0 ep1001011101_1)
private theorem idp1001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100101110.list =
    C ((2:ℤ)^294) * horner X vp1001011101.list + horner X ep1001011101.list := by
  exact edge_identity (B := (2:ℤ)^470) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001011101 : Branch 1 (-4831761639/16000000 : ℚ) vp100101110 := by
  apply branch_checked idp1001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-4831761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4839761639/8000000 : ℚ) by norm_num]
  exact coverp1001011101
theorem coverp100101110 : Covers (-4831761639/16000000 : ℚ) vp100101110 := join_branches bp1001011100 bp1001011101
private noncomputable def vp10010111_0 : Blocks := edgeBlocks% "full/vectors/10010111-V-0000.bin"
private noncomputable def vp10010111_1 : Blocks := edgeBlocks% "full/vectors/10010111-V-0001.bin"
private noncomputable def vp10010111_2 : Blocks := edgeBlocks% "full/vectors/10010111-V-0002.bin"
private noncomputable def vp10010111_3 : Blocks := edgeBlocks% "full/vectors/10010111-V-0003.bin"
noncomputable def vp10010111 : Blocks := (Blocks.join (Blocks.join vp10010111_0 vp10010111_1) (Blocks.join vp10010111_2 vp10010111_3))
private theorem bp100101110 : Branch 0 (-4831761639/32000000 : ℚ) vp10010111 := by
  apply branch_left_normalized (c:=vp100101110) (k:=0) (m:=247) (by decide +kernel)
  rw [show 2*(-4831761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4831761639/16000000 : ℚ) by norm_num]
  exact coverp100101110
private noncomputable def ep100101111_0 : Blocks := edgeBlocks% "full/vectors/100101111-E-0000.bin"
private noncomputable def ep100101111_1 : Blocks := edgeBlocks% "full/vectors/100101111-E-0001.bin"
private noncomputable def ep100101111_2 : Blocks := edgeBlocks% "full/vectors/100101111-E-0002.bin"
private noncomputable def ep100101111_3 : Blocks := edgeBlocks% "full/vectors/100101111-E-0003.bin"
noncomputable def ep100101111 : Blocks := (Blocks.join (Blocks.join ep100101111_0 ep100101111_1) (Blocks.join ep100101111_2 ep100101111_3))
private theorem idp100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10010111.list =
    C ((2:ℤ)^566) * horner X vp100101111.list + horner X ep100101111.list := by
  exact edge_identity (B := (2:ℤ)^814) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100101111 : Branch 1 (-4831761639/32000000 : ℚ) vp10010111 := by
  apply branch_checked idp100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-4831761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4847761639/16000000 : ℚ) by norm_num]
  exact coverp100101111
theorem coverp10010111 : Covers (-4831761639/32000000 : ℚ) vp10010111 := join_branches bp100101110 bp100101111
private noncomputable def vp10010110111_0 : Blocks := edgeBlocks% "full/vectors/10010110111-V-0000.bin"
noncomputable def vp10010110111 : Blocks := vp10010110111_0
theorem coverp10010110111 : Covers (-4827761639/4000000 : ℚ) vp10010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp10010110110_0 : Blocks := edgeBlocks% "full/vectors/10010110110-V-0000.bin"
noncomputable def vp10010110110 : Blocks := vp10010110110_0
theorem coverp10010110110 : Covers (-4823761639/4000000 : ℚ) vp10010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001011011_0 : Blocks := edgeBlocks% "full/vectors/1001011011-V-0000.bin"
private noncomputable def vp1001011011_1 : Blocks := edgeBlocks% "full/vectors/1001011011-V-0001.bin"
noncomputable def vp1001011011 : Blocks := (Blocks.join vp1001011011_0 vp1001011011_1)
private theorem bp10010110110 : Branch 0 (-4823761639/8000000 : ℚ) vp1001011011 := by
  apply branch_left_normalized (c:=vp10010110110) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-4823761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4823761639/4000000 : ℚ) by norm_num]
  exact coverp10010110110
private noncomputable def ep10010110111_0 : Blocks := edgeBlocks% "full/vectors/10010110111-E-0000.bin"
private noncomputable def ep10010110111_1 : Blocks := edgeBlocks% "full/vectors/10010110111-E-0001.bin"
noncomputable def ep10010110111 : Blocks := (Blocks.join ep10010110111_0 ep10010110111_1)
private theorem idp10010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001011011.list =
    C ((2:ℤ)^157) * horner X vp10010110111.list + horner X ep10010110111.list := by
  exact edge_identity (B := (2:ℤ)^295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010110111 : Branch 1 (-4823761639/8000000 : ℚ) vp1001011011 := by
  apply branch_checked idp10010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-4823761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4827761639/4000000 : ℚ) by norm_num]
  exact coverp10010110111
theorem coverp1001011011 : Covers (-4823761639/8000000 : ℚ) vp1001011011 := join_branches bp10010110110 bp10010110111
private noncomputable def vp10010110101_0 : Blocks := edgeBlocks% "full/vectors/10010110101-V-0000.bin"
noncomputable def vp10010110101 : Blocks := vp10010110101_0
theorem coverp10010110101 : Covers (-4819761639/4000000 : ℚ) vp10010110101 := cover_leaf (by decide +kernel)
private noncomputable def vp10010110100_0 : Blocks := edgeBlocks% "full/vectors/10010110100-V-0000.bin"
noncomputable def vp10010110100 : Blocks := vp10010110100_0
theorem coverp10010110100 : Covers (-4815761639/4000000 : ℚ) vp10010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp1001011010_0 : Blocks := edgeBlocks% "full/vectors/1001011010-V-0000.bin"
private noncomputable def vp1001011010_1 : Blocks := edgeBlocks% "full/vectors/1001011010-V-0001.bin"
noncomputable def vp1001011010 : Blocks := (Blocks.join vp1001011010_0 vp1001011010_1)
private theorem bp10010110100 : Branch 0 (-4815761639/8000000 : ℚ) vp1001011010 := by
  apply branch_left_normalized (c:=vp10010110100) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-4815761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4815761639/4000000 : ℚ) by norm_num]
  exact coverp10010110100
private noncomputable def ep10010110101_0 : Blocks := edgeBlocks% "full/vectors/10010110101-E-0000.bin"
private noncomputable def ep10010110101_1 : Blocks := edgeBlocks% "full/vectors/10010110101-E-0001.bin"
noncomputable def ep10010110101 : Blocks := (Blocks.join ep10010110101_0 ep10010110101_1)
private theorem idp10010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001011010.list =
    C ((2:ℤ)^156) * horner X vp10010110101.list + horner X ep10010110101.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010110101 : Branch 1 (-4815761639/8000000 : ℚ) vp1001011010 := by
  apply branch_checked idp10010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-4815761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4819761639/4000000 : ℚ) by norm_num]
  exact coverp10010110101
theorem coverp1001011010 : Covers (-4815761639/8000000 : ℚ) vp1001011010 := join_branches bp10010110100 bp10010110101
private noncomputable def vp100101101_0 : Blocks := edgeBlocks% "full/vectors/100101101-V-0000.bin"
private noncomputable def vp100101101_1 : Blocks := edgeBlocks% "full/vectors/100101101-V-0001.bin"
noncomputable def vp100101101 : Blocks := (Blocks.join vp100101101_0 vp100101101_1)
private theorem bp1001011010 : Branch 0 (-4815761639/16000000 : ℚ) vp100101101 := by
  apply branch_left_normalized (c:=vp1001011010) (k:=0) (m:=133) (by decide +kernel)
  rw [show 2*(-4815761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4815761639/8000000 : ℚ) by norm_num]
  exact coverp1001011010
private noncomputable def ep1001011011_0 : Blocks := edgeBlocks% "full/vectors/1001011011-E-0000.bin"
private noncomputable def ep1001011011_1 : Blocks := edgeBlocks% "full/vectors/1001011011-E-0001.bin"
noncomputable def ep1001011011 : Blocks := (Blocks.join ep1001011011_0 ep1001011011_1)
private theorem idp1001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100101101.list =
    C ((2:ℤ)^291) * horner X vp1001011011.list + horner X ep1001011011.list := by
  exact edge_identity (B := (2:ℤ)^464) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001011011 : Branch 1 (-4815761639/16000000 : ℚ) vp100101101 := by
  apply branch_checked idp1001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-4815761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4823761639/8000000 : ℚ) by norm_num]
  exact coverp1001011011
theorem coverp100101101 : Covers (-4815761639/16000000 : ℚ) vp100101101 := join_branches bp1001011010 bp1001011011
private noncomputable def vp1001011001_0 : Blocks := edgeBlocks% "full/vectors/1001011001-V-0000.bin"
private noncomputable def vp1001011001_1 : Blocks := edgeBlocks% "full/vectors/1001011001-V-0001.bin"
noncomputable def vp1001011001 : Blocks := (Blocks.join vp1001011001_0 vp1001011001_1)
theorem coverp1001011001 : Covers (-4807761639/8000000 : ℚ) vp1001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp1001011000_0 : Blocks := edgeBlocks% "full/vectors/1001011000-V-0000.bin"
private noncomputable def vp1001011000_1 : Blocks := edgeBlocks% "full/vectors/1001011000-V-0001.bin"
noncomputable def vp1001011000 : Blocks := (Blocks.join vp1001011000_0 vp1001011000_1)
theorem coverp1001011000 : Covers (-4799761639/8000000 : ℚ) vp1001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp100101100_0 : Blocks := edgeBlocks% "full/vectors/100101100-V-0000.bin"
private noncomputable def vp100101100_1 : Blocks := edgeBlocks% "full/vectors/100101100-V-0001.bin"
noncomputable def vp100101100 : Blocks := (Blocks.join vp100101100_0 vp100101100_1)
private theorem bp1001011000 : Branch 0 (-4799761639/16000000 : ℚ) vp100101100 := by
  apply branch_left_normalized (c:=vp1001011000) (k:=0) (m:=132) (by decide +kernel)
  rw [show 2*(-4799761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4799761639/8000000 : ℚ) by norm_num]
  exact coverp1001011000
private noncomputable def ep1001011001_0 : Blocks := edgeBlocks% "full/vectors/1001011001-E-0000.bin"
private noncomputable def ep1001011001_1 : Blocks := edgeBlocks% "full/vectors/1001011001-E-0001.bin"
noncomputable def ep1001011001 : Blocks := (Blocks.join ep1001011001_0 ep1001011001_1)
private theorem idp1001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100101100.list =
    C ((2:ℤ)^291) * horner X vp1001011001.list + horner X ep1001011001.list := by
  exact edge_identity (B := (2:ℤ)^461) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001011001 : Branch 1 (-4799761639/16000000 : ℚ) vp100101100 := by
  apply branch_checked idp1001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-4799761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4807761639/8000000 : ℚ) by norm_num]
  exact coverp1001011001
theorem coverp100101100 : Covers (-4799761639/16000000 : ℚ) vp100101100 := join_branches bp1001011000 bp1001011001
private noncomputable def vp10010110_0 : Blocks := edgeBlocks% "full/vectors/10010110-V-0000.bin"
private noncomputable def vp10010110_1 : Blocks := edgeBlocks% "full/vectors/10010110-V-0001.bin"
private noncomputable def vp10010110_2 : Blocks := edgeBlocks% "full/vectors/10010110-V-0002.bin"
private noncomputable def vp10010110_3 : Blocks := edgeBlocks% "full/vectors/10010110-V-0003.bin"
noncomputable def vp10010110 : Blocks := (Blocks.join (Blocks.join vp10010110_0 vp10010110_1) (Blocks.join vp10010110_2 vp10010110_3))
private theorem bp100101100 : Branch 0 (-4799761639/32000000 : ℚ) vp10010110 := by
  apply branch_left_normalized (c:=vp100101100) (k:=0) (m:=245) (by decide +kernel)
  rw [show 2*(-4799761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4799761639/16000000 : ℚ) by norm_num]
  exact coverp100101100
private noncomputable def ep100101101_0 : Blocks := edgeBlocks% "full/vectors/100101101-E-0000.bin"
private noncomputable def ep100101101_1 : Blocks := edgeBlocks% "full/vectors/100101101-E-0001.bin"
private noncomputable def ep100101101_2 : Blocks := edgeBlocks% "full/vectors/100101101-E-0002.bin"
private noncomputable def ep100101101_3 : Blocks := edgeBlocks% "full/vectors/100101101-E-0003.bin"
noncomputable def ep100101101 : Blocks := (Blocks.join (Blocks.join ep100101101_0 ep100101101_1) (Blocks.join ep100101101_2 ep100101101_3))
private theorem idp100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10010110.list =
    C ((2:ℤ)^561) * horner X vp100101101.list + horner X ep100101101.list := by
  exact edge_identity (B := (2:ℤ)^807) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100101101 : Branch 1 (-4799761639/32000000 : ℚ) vp10010110 := by
  apply branch_checked idp100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-4799761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4815761639/16000000 : ℚ) by norm_num]
  exact coverp100101101
theorem coverp10010110 : Covers (-4799761639/32000000 : ℚ) vp10010110 := join_branches bp100101100 bp100101101
private noncomputable def vp1001011_0 : Blocks := edgeBlocks% "full/vectors/1001011-V-0000.bin"
private noncomputable def vp1001011_1 : Blocks := edgeBlocks% "full/vectors/1001011-V-0001.bin"
private noncomputable def vp1001011_2 : Blocks := edgeBlocks% "full/vectors/1001011-V-0002.bin"
private noncomputable def vp1001011_3 : Blocks := edgeBlocks% "full/vectors/1001011-V-0003.bin"
private noncomputable def vp1001011_4 : Blocks := edgeBlocks% "full/vectors/1001011-V-0004.bin"
private noncomputable def vp1001011_5 : Blocks := edgeBlocks% "full/vectors/1001011-V-0005.bin"
private noncomputable def vp1001011_6 : Blocks := edgeBlocks% "full/vectors/1001011-V-0006.bin"
private noncomputable def vp1001011_7 : Blocks := edgeBlocks% "full/vectors/1001011-V-0007.bin"
noncomputable def vp1001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1001011_0 vp1001011_1) (Blocks.join vp1001011_2 vp1001011_3)) (Blocks.join (Blocks.join vp1001011_4 vp1001011_5) (Blocks.join vp1001011_6 vp1001011_7)))
private theorem bp10010110 : Branch 0 (-4799761639/64000000 : ℚ) vp1001011 := by
  apply branch_left_normalized (c:=vp10010110) (k:=0) (m:=470) (by decide +kernel)
  rw [show 2*(-4799761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4799761639/32000000 : ℚ) by norm_num]
  exact coverp10010110
private noncomputable def ep10010111_0 : Blocks := edgeBlocks% "full/vectors/10010111-E-0000.bin"
private noncomputable def ep10010111_1 : Blocks := edgeBlocks% "full/vectors/10010111-E-0001.bin"
private noncomputable def ep10010111_2 : Blocks := edgeBlocks% "full/vectors/10010111-E-0002.bin"
private noncomputable def ep10010111_3 : Blocks := edgeBlocks% "full/vectors/10010111-E-0003.bin"
private noncomputable def ep10010111_4 : Blocks := edgeBlocks% "full/vectors/10010111-E-0004.bin"
private noncomputable def ep10010111_5 : Blocks := edgeBlocks% "full/vectors/10010111-E-0005.bin"
private noncomputable def ep10010111_6 : Blocks := edgeBlocks% "full/vectors/10010111-E-0006.bin"
private noncomputable def ep10010111_7 : Blocks := edgeBlocks% "full/vectors/10010111-E-0007.bin"
noncomputable def ep10010111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10010111_0 ep10010111_1) (Blocks.join ep10010111_2 ep10010111_3)) (Blocks.join (Blocks.join ep10010111_4 ep10010111_5) (Blocks.join ep10010111_6 ep10010111_7)))
private theorem idp10010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001011.list =
    C ((2:ℤ)^1093) * horner X vp10010111.list + horner X ep10010111.list := by
  exact edge_identity (B := (2:ℤ)^1490) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010111 : Branch 1 (-4799761639/64000000 : ℚ) vp1001011 := by
  apply branch_checked idp10010111 (by positivity) (by decide +kernel)
  rw [show 2*(-4799761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4831761639/32000000 : ℚ) by norm_num]
  exact coverp10010111
theorem coverp1001011 : Covers (-4799761639/64000000 : ℚ) vp1001011 := join_branches bp10010110 bp10010111
private noncomputable def vp1001010111_0 : Blocks := edgeBlocks% "full/vectors/1001010111-V-0000.bin"
private noncomputable def vp1001010111_1 : Blocks := edgeBlocks% "full/vectors/1001010111-V-0001.bin"
noncomputable def vp1001010111 : Blocks := (Blocks.join vp1001010111_0 vp1001010111_1)
theorem coverp1001010111 : Covers (-4791761639/8000000 : ℚ) vp1001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp1001010110_0 : Blocks := edgeBlocks% "full/vectors/1001010110-V-0000.bin"
private noncomputable def vp1001010110_1 : Blocks := edgeBlocks% "full/vectors/1001010110-V-0001.bin"
noncomputable def vp1001010110 : Blocks := (Blocks.join vp1001010110_0 vp1001010110_1)
theorem coverp1001010110 : Covers (-4783761639/8000000 : ℚ) vp1001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp100101011_0 : Blocks := edgeBlocks% "full/vectors/100101011-V-0000.bin"
private noncomputable def vp100101011_1 : Blocks := edgeBlocks% "full/vectors/100101011-V-0001.bin"
noncomputable def vp100101011 : Blocks := (Blocks.join vp100101011_0 vp100101011_1)
private theorem bp1001010110 : Branch 0 (-4783761639/16000000 : ℚ) vp100101011 := by
  apply branch_left_normalized (c:=vp1001010110) (k:=0) (m:=131) (by decide +kernel)
  rw [show 2*(-4783761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4783761639/8000000 : ℚ) by norm_num]
  exact coverp1001010110
private noncomputable def ep1001010111_0 : Blocks := edgeBlocks% "full/vectors/1001010111-E-0000.bin"
private noncomputable def ep1001010111_1 : Blocks := edgeBlocks% "full/vectors/1001010111-E-0001.bin"
noncomputable def ep1001010111 : Blocks := (Blocks.join ep1001010111_0 ep1001010111_1)
private theorem idp1001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100101011.list =
    C ((2:ℤ)^292) * horner X vp1001010111.list + horner X ep1001010111.list := by
  exact edge_identity (B := (2:ℤ)^461) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001010111 : Branch 1 (-4783761639/16000000 : ℚ) vp100101011 := by
  apply branch_checked idp1001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-4783761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4791761639/8000000 : ℚ) by norm_num]
  exact coverp1001010111
theorem coverp100101011 : Covers (-4783761639/16000000 : ℚ) vp100101011 := join_branches bp1001010110 bp1001010111
private noncomputable def vp1001010101_0 : Blocks := edgeBlocks% "full/vectors/1001010101-V-0000.bin"
private noncomputable def vp1001010101_1 : Blocks := edgeBlocks% "full/vectors/1001010101-V-0001.bin"
noncomputable def vp1001010101 : Blocks := (Blocks.join vp1001010101_0 vp1001010101_1)
theorem coverp1001010101 : Covers (-4775761639/8000000 : ℚ) vp1001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp1001010100_0 : Blocks := edgeBlocks% "full/vectors/1001010100-V-0000.bin"
private noncomputable def vp1001010100_1 : Blocks := edgeBlocks% "full/vectors/1001010100-V-0001.bin"
noncomputable def vp1001010100 : Blocks := (Blocks.join vp1001010100_0 vp1001010100_1)
theorem coverp1001010100 : Covers (-4767761639/8000000 : ℚ) vp1001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp100101010_0 : Blocks := edgeBlocks% "full/vectors/100101010-V-0000.bin"
private noncomputable def vp100101010_1 : Blocks := edgeBlocks% "full/vectors/100101010-V-0001.bin"
noncomputable def vp100101010 : Blocks := (Blocks.join vp100101010_0 vp100101010_1)
private theorem bp1001010100 : Branch 0 (-4767761639/16000000 : ℚ) vp100101010 := by
  apply branch_left_normalized (c:=vp1001010100) (k:=0) (m:=132) (by decide +kernel)
  rw [show 2*(-4767761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4767761639/8000000 : ℚ) by norm_num]
  exact coverp1001010100
private noncomputable def ep1001010101_0 : Blocks := edgeBlocks% "full/vectors/1001010101-E-0000.bin"
private noncomputable def ep1001010101_1 : Blocks := edgeBlocks% "full/vectors/1001010101-E-0001.bin"
noncomputable def ep1001010101 : Blocks := (Blocks.join ep1001010101_0 ep1001010101_1)
private theorem idp1001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100101010.list =
    C ((2:ℤ)^294) * horner X vp1001010101.list + horner X ep1001010101.list := by
  exact edge_identity (B := (2:ℤ)^463) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001010101 : Branch 1 (-4767761639/16000000 : ℚ) vp100101010 := by
  apply branch_checked idp1001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4767761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4775761639/8000000 : ℚ) by norm_num]
  exact coverp1001010101
theorem coverp100101010 : Covers (-4767761639/16000000 : ℚ) vp100101010 := join_branches bp1001010100 bp1001010101
private noncomputable def vp10010101_0 : Blocks := edgeBlocks% "full/vectors/10010101-V-0000.bin"
private noncomputable def vp10010101_1 : Blocks := edgeBlocks% "full/vectors/10010101-V-0001.bin"
private noncomputable def vp10010101_2 : Blocks := edgeBlocks% "full/vectors/10010101-V-0002.bin"
private noncomputable def vp10010101_3 : Blocks := edgeBlocks% "full/vectors/10010101-V-0003.bin"
noncomputable def vp10010101 : Blocks := (Blocks.join (Blocks.join vp10010101_0 vp10010101_1) (Blocks.join vp10010101_2 vp10010101_3))
private theorem bp100101010 : Branch 0 (-4767761639/32000000 : ℚ) vp10010101 := by
  apply branch_left_normalized (c:=vp100101010) (k:=0) (m:=246) (by decide +kernel)
  rw [show 2*(-4767761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4767761639/16000000 : ℚ) by norm_num]
  exact coverp100101010
private noncomputable def ep100101011_0 : Blocks := edgeBlocks% "full/vectors/100101011-E-0000.bin"
private noncomputable def ep100101011_1 : Blocks := edgeBlocks% "full/vectors/100101011-E-0001.bin"
private noncomputable def ep100101011_2 : Blocks := edgeBlocks% "full/vectors/100101011-E-0002.bin"
private noncomputable def ep100101011_3 : Blocks := edgeBlocks% "full/vectors/100101011-E-0003.bin"
noncomputable def ep100101011 : Blocks := (Blocks.join (Blocks.join ep100101011_0 ep100101011_1) (Blocks.join ep100101011_2 ep100101011_3))
private theorem idp100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10010101.list =
    C ((2:ℤ)^566) * horner X vp100101011.list + horner X ep100101011.list := by
  exact edge_identity (B := (2:ℤ)^810) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100101011 : Branch 1 (-4767761639/32000000 : ℚ) vp10010101 := by
  apply branch_checked idp100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-4767761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4783761639/16000000 : ℚ) by norm_num]
  exact coverp100101011
theorem coverp10010101 : Covers (-4767761639/32000000 : ℚ) vp10010101 := join_branches bp100101010 bp100101011
private noncomputable def vp1001010011_0 : Blocks := edgeBlocks% "full/vectors/1001010011-V-0000.bin"
private noncomputable def vp1001010011_1 : Blocks := edgeBlocks% "full/vectors/1001010011-V-0001.bin"
noncomputable def vp1001010011 : Blocks := (Blocks.join vp1001010011_0 vp1001010011_1)
theorem coverp1001010011 : Covers (-4759761639/8000000 : ℚ) vp1001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp1001010010_0 : Blocks := edgeBlocks% "full/vectors/1001010010-V-0000.bin"
private noncomputable def vp1001010010_1 : Blocks := edgeBlocks% "full/vectors/1001010010-V-0001.bin"
noncomputable def vp1001010010 : Blocks := (Blocks.join vp1001010010_0 vp1001010010_1)
theorem coverp1001010010 : Covers (-4751761639/8000000 : ℚ) vp1001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp100101001_0 : Blocks := edgeBlocks% "full/vectors/100101001-V-0000.bin"
private noncomputable def vp100101001_1 : Blocks := edgeBlocks% "full/vectors/100101001-V-0001.bin"
noncomputable def vp100101001 : Blocks := (Blocks.join vp100101001_0 vp100101001_1)
private theorem bp1001010010 : Branch 0 (-4751761639/16000000 : ℚ) vp100101001 := by
  apply branch_left_normalized (c:=vp1001010010) (k:=0) (m:=135) (by decide +kernel)
  rw [show 2*(-4751761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4751761639/8000000 : ℚ) by norm_num]
  exact coverp1001010010
private noncomputable def ep1001010011_0 : Blocks := edgeBlocks% "full/vectors/1001010011-E-0000.bin"
private noncomputable def ep1001010011_1 : Blocks := edgeBlocks% "full/vectors/1001010011-E-0001.bin"
noncomputable def ep1001010011 : Blocks := (Blocks.join ep1001010011_0 ep1001010011_1)
private theorem idp1001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100101001.list =
    C ((2:ℤ)^299) * horner X vp1001010011.list + horner X ep1001010011.list := by
  exact edge_identity (B := (2:ℤ)^471) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001010011 : Branch 1 (-4751761639/16000000 : ℚ) vp100101001 := by
  apply branch_checked idp1001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4751761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4759761639/8000000 : ℚ) by norm_num]
  exact coverp1001010011
theorem coverp100101001 : Covers (-4751761639/16000000 : ℚ) vp100101001 := join_branches bp1001010010 bp1001010011
private noncomputable def vp10010100011_0 : Blocks := edgeBlocks% "full/vectors/10010100011-V-0000.bin"
noncomputable def vp10010100011 : Blocks := vp10010100011_0
theorem coverp10010100011 : Covers (-4747761639/4000000 : ℚ) vp10010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp10010100010_0 : Blocks := edgeBlocks% "full/vectors/10010100010-V-0000.bin"
noncomputable def vp10010100010 : Blocks := vp10010100010_0
theorem coverp10010100010 : Covers (-4743761639/4000000 : ℚ) vp10010100010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001010001_0 : Blocks := edgeBlocks% "full/vectors/1001010001-V-0000.bin"
private noncomputable def vp1001010001_1 : Blocks := edgeBlocks% "full/vectors/1001010001-V-0001.bin"
noncomputable def vp1001010001 : Blocks := (Blocks.join vp1001010001_0 vp1001010001_1)
private theorem bp10010100010 : Branch 0 (-4743761639/8000000 : ℚ) vp1001010001 := by
  apply branch_left_normalized (c:=vp10010100010) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4743761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4743761639/4000000 : ℚ) by norm_num]
  exact coverp10010100010
private noncomputable def ep10010100011_0 : Blocks := edgeBlocks% "full/vectors/10010100011-E-0000.bin"
private noncomputable def ep10010100011_1 : Blocks := edgeBlocks% "full/vectors/10010100011-E-0001.bin"
noncomputable def ep10010100011 : Blocks := (Blocks.join ep10010100011_0 ep10010100011_1)
private theorem idp10010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001010001.list =
    C ((2:ℤ)^161) * horner X vp10010100011.list + horner X ep10010100011.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010100011 : Branch 1 (-4743761639/8000000 : ℚ) vp1001010001 := by
  apply branch_checked idp10010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-4743761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4747761639/4000000 : ℚ) by norm_num]
  exact coverp10010100011
theorem coverp1001010001 : Covers (-4743761639/8000000 : ℚ) vp1001010001 := join_branches bp10010100010 bp10010100011
private noncomputable def vp10010100001_0 : Blocks := edgeBlocks% "full/vectors/10010100001-V-0000.bin"
noncomputable def vp10010100001 : Blocks := vp10010100001_0
theorem coverp10010100001 : Covers (-4739761639/4000000 : ℚ) vp10010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp10010100000_0 : Blocks := edgeBlocks% "full/vectors/10010100000-V-0000.bin"
noncomputable def vp10010100000 : Blocks := vp10010100000_0
theorem coverp10010100000 : Covers (-4735761639/4000000 : ℚ) vp10010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001010000_0 : Blocks := edgeBlocks% "full/vectors/1001010000-V-0000.bin"
private noncomputable def vp1001010000_1 : Blocks := edgeBlocks% "full/vectors/1001010000-V-0001.bin"
noncomputable def vp1001010000 : Blocks := (Blocks.join vp1001010000_0 vp1001010000_1)
private theorem bp10010100000 : Branch 0 (-4735761639/8000000 : ℚ) vp1001010000 := by
  apply branch_left_normalized (c:=vp10010100000) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4735761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4735761639/4000000 : ℚ) by norm_num]
  exact coverp10010100000
private noncomputable def ep10010100001_0 : Blocks := edgeBlocks% "full/vectors/10010100001-E-0000.bin"
private noncomputable def ep10010100001_1 : Blocks := edgeBlocks% "full/vectors/10010100001-E-0001.bin"
noncomputable def ep10010100001 : Blocks := (Blocks.join ep10010100001_0 ep10010100001_1)
private theorem idp10010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001010000.list =
    C ((2:ℤ)^161) * horner X vp10010100001.list + horner X ep10010100001.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010100001 : Branch 1 (-4735761639/8000000 : ℚ) vp1001010000 := by
  apply branch_checked idp10010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-4735761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4739761639/4000000 : ℚ) by norm_num]
  exact coverp10010100001
theorem coverp1001010000 : Covers (-4735761639/8000000 : ℚ) vp1001010000 := join_branches bp10010100000 bp10010100001
private noncomputable def vp100101000_0 : Blocks := edgeBlocks% "full/vectors/100101000-V-0000.bin"
private noncomputable def vp100101000_1 : Blocks := edgeBlocks% "full/vectors/100101000-V-0001.bin"
noncomputable def vp100101000 : Blocks := (Blocks.join vp100101000_0 vp100101000_1)
private theorem bp1001010000 : Branch 0 (-4735761639/16000000 : ℚ) vp100101000 := by
  apply branch_left_normalized (c:=vp1001010000) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-4735761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4735761639/8000000 : ℚ) by norm_num]
  exact coverp1001010000
private noncomputable def ep1001010001_0 : Blocks := edgeBlocks% "full/vectors/1001010001-E-0000.bin"
private noncomputable def ep1001010001_1 : Blocks := edgeBlocks% "full/vectors/1001010001-E-0001.bin"
noncomputable def ep1001010001 : Blocks := (Blocks.join ep1001010001_0 ep1001010001_1)
private theorem idp1001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100101000.list =
    C ((2:ℤ)^297) * horner X vp1001010001.list + horner X ep1001010001.list := by
  exact edge_identity (B := (2:ℤ)^474) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001010001 : Branch 1 (-4735761639/16000000 : ℚ) vp100101000 := by
  apply branch_checked idp1001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4735761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4743761639/8000000 : ℚ) by norm_num]
  exact coverp1001010001
theorem coverp100101000 : Covers (-4735761639/16000000 : ℚ) vp100101000 := join_branches bp1001010000 bp1001010001
private noncomputable def vp10010100_0 : Blocks := edgeBlocks% "full/vectors/10010100-V-0000.bin"
private noncomputable def vp10010100_1 : Blocks := edgeBlocks% "full/vectors/10010100-V-0001.bin"
private noncomputable def vp10010100_2 : Blocks := edgeBlocks% "full/vectors/10010100-V-0002.bin"
private noncomputable def vp10010100_3 : Blocks := edgeBlocks% "full/vectors/10010100-V-0003.bin"
noncomputable def vp10010100 : Blocks := (Blocks.join (Blocks.join vp10010100_0 vp10010100_1) (Blocks.join vp10010100_2 vp10010100_3))
private theorem bp100101000 : Branch 0 (-4735761639/32000000 : ℚ) vp10010100 := by
  apply branch_left_normalized (c:=vp100101000) (k:=0) (m:=250) (by decide +kernel)
  rw [show 2*(-4735761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4735761639/16000000 : ℚ) by norm_num]
  exact coverp100101000
private noncomputable def ep100101001_0 : Blocks := edgeBlocks% "full/vectors/100101001-E-0000.bin"
private noncomputable def ep100101001_1 : Blocks := edgeBlocks% "full/vectors/100101001-E-0001.bin"
private noncomputable def ep100101001_2 : Blocks := edgeBlocks% "full/vectors/100101001-E-0002.bin"
private noncomputable def ep100101001_3 : Blocks := edgeBlocks% "full/vectors/100101001-E-0003.bin"
noncomputable def ep100101001 : Blocks := (Blocks.join (Blocks.join ep100101001_0 ep100101001_1) (Blocks.join ep100101001_2 ep100101001_3))
private theorem idp100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10010100.list =
    C ((2:ℤ)^572) * horner X vp100101001.list + horner X ep100101001.list := by
  exact edge_identity (B := (2:ℤ)^822) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100101001 : Branch 1 (-4735761639/32000000 : ℚ) vp10010100 := by
  apply branch_checked idp100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-4735761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4751761639/16000000 : ℚ) by norm_num]
  exact coverp100101001
theorem coverp10010100 : Covers (-4735761639/32000000 : ℚ) vp10010100 := join_branches bp100101000 bp100101001
private noncomputable def vp1001010_0 : Blocks := edgeBlocks% "full/vectors/1001010-V-0000.bin"
private noncomputable def vp1001010_1 : Blocks := edgeBlocks% "full/vectors/1001010-V-0001.bin"
private noncomputable def vp1001010_2 : Blocks := edgeBlocks% "full/vectors/1001010-V-0002.bin"
private noncomputable def vp1001010_3 : Blocks := edgeBlocks% "full/vectors/1001010-V-0003.bin"
private noncomputable def vp1001010_4 : Blocks := edgeBlocks% "full/vectors/1001010-V-0004.bin"
private noncomputable def vp1001010_5 : Blocks := edgeBlocks% "full/vectors/1001010-V-0005.bin"
private noncomputable def vp1001010_6 : Blocks := edgeBlocks% "full/vectors/1001010-V-0006.bin"
private noncomputable def vp1001010_7 : Blocks := edgeBlocks% "full/vectors/1001010-V-0007.bin"
noncomputable def vp1001010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1001010_0 vp1001010_1) (Blocks.join vp1001010_2 vp1001010_3)) (Blocks.join (Blocks.join vp1001010_4 vp1001010_5) (Blocks.join vp1001010_6 vp1001010_7)))
private theorem bp10010100 : Branch 0 (-4735761639/64000000 : ℚ) vp1001010 := by
  apply branch_left_normalized (c:=vp10010100) (k:=0) (m:=477) (by decide +kernel)
  rw [show 2*(-4735761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4735761639/32000000 : ℚ) by norm_num]
  exact coverp10010100
private noncomputable def ep10010101_0 : Blocks := edgeBlocks% "full/vectors/10010101-E-0000.bin"
private noncomputable def ep10010101_1 : Blocks := edgeBlocks% "full/vectors/10010101-E-0001.bin"
private noncomputable def ep10010101_2 : Blocks := edgeBlocks% "full/vectors/10010101-E-0002.bin"
private noncomputable def ep10010101_3 : Blocks := edgeBlocks% "full/vectors/10010101-E-0003.bin"
private noncomputable def ep10010101_4 : Blocks := edgeBlocks% "full/vectors/10010101-E-0004.bin"
private noncomputable def ep10010101_5 : Blocks := edgeBlocks% "full/vectors/10010101-E-0005.bin"
private noncomputable def ep10010101_6 : Blocks := edgeBlocks% "full/vectors/10010101-E-0006.bin"
private noncomputable def ep10010101_7 : Blocks := edgeBlocks% "full/vectors/10010101-E-0007.bin"
noncomputable def ep10010101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10010101_0 ep10010101_1) (Blocks.join ep10010101_2 ep10010101_3)) (Blocks.join (Blocks.join ep10010101_4 ep10010101_5) (Blocks.join ep10010101_6 ep10010101_7)))
private theorem idp10010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001010.list =
    C ((2:ℤ)^1117) * horner X vp10010101.list + horner X ep10010101.list := by
  exact edge_identity (B := (2:ℤ)^1511) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010101 : Branch 1 (-4735761639/64000000 : ℚ) vp1001010 := by
  apply branch_checked idp10010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4735761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4767761639/32000000 : ℚ) by norm_num]
  exact coverp10010101
theorem coverp1001010 : Covers (-4735761639/64000000 : ℚ) vp1001010 := join_branches bp10010100 bp10010101
private noncomputable def vp100101_0 : Blocks := edgeBlocks% "full/vectors/100101-V-0000.bin"
private noncomputable def vp100101_1 : Blocks := edgeBlocks% "full/vectors/100101-V-0001.bin"
private noncomputable def vp100101_2 : Blocks := edgeBlocks% "full/vectors/100101-V-0002.bin"
private noncomputable def vp100101_3 : Blocks := edgeBlocks% "full/vectors/100101-V-0003.bin"
private noncomputable def vp100101_4 : Blocks := edgeBlocks% "full/vectors/100101-V-0004.bin"
private noncomputable def vp100101_5 : Blocks := edgeBlocks% "full/vectors/100101-V-0005.bin"
private noncomputable def vp100101_6 : Blocks := edgeBlocks% "full/vectors/100101-V-0006.bin"
private noncomputable def vp100101_7 : Blocks := edgeBlocks% "full/vectors/100101-V-0007.bin"
private noncomputable def vp100101_8 : Blocks := edgeBlocks% "full/vectors/100101-V-0008.bin"
private noncomputable def vp100101_9 : Blocks := edgeBlocks% "full/vectors/100101-V-0009.bin"
private noncomputable def vp100101_10 : Blocks := edgeBlocks% "full/vectors/100101-V-0010.bin"
private noncomputable def vp100101_11 : Blocks := edgeBlocks% "full/vectors/100101-V-0011.bin"
private noncomputable def vp100101_12 : Blocks := edgeBlocks% "full/vectors/100101-V-0012.bin"
private noncomputable def vp100101_13 : Blocks := edgeBlocks% "full/vectors/100101-V-0013.bin"
private noncomputable def vp100101_14 : Blocks := edgeBlocks% "full/vectors/100101-V-0014.bin"
noncomputable def vp100101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp100101_0 (Blocks.join vp100101_1 vp100101_2)) (Blocks.join (Blocks.join vp100101_3 vp100101_4) (Blocks.join vp100101_5 vp100101_6))) (Blocks.join (Blocks.join (Blocks.join vp100101_7 vp100101_8) (Blocks.join vp100101_9 vp100101_10)) (Blocks.join (Blocks.join vp100101_11 vp100101_12) (Blocks.join vp100101_13 vp100101_14))))
private theorem bp1001010 : Branch 0 (-4735761639/128000000 : ℚ) vp100101 := by
  apply branch_left_normalized (c:=vp1001010) (k:=0) (m:=925) (by decide +kernel)
  rw [show 2*(-4735761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-4735761639/64000000 : ℚ) by norm_num]
  exact coverp1001010
private noncomputable def ep1001011_0 : Blocks := edgeBlocks% "full/vectors/1001011-E-0000.bin"
private noncomputable def ep1001011_1 : Blocks := edgeBlocks% "full/vectors/1001011-E-0001.bin"
private noncomputable def ep1001011_2 : Blocks := edgeBlocks% "full/vectors/1001011-E-0002.bin"
private noncomputable def ep1001011_3 : Blocks := edgeBlocks% "full/vectors/1001011-E-0003.bin"
private noncomputable def ep1001011_4 : Blocks := edgeBlocks% "full/vectors/1001011-E-0004.bin"
private noncomputable def ep1001011_5 : Blocks := edgeBlocks% "full/vectors/1001011-E-0005.bin"
private noncomputable def ep1001011_6 : Blocks := edgeBlocks% "full/vectors/1001011-E-0006.bin"
private noncomputable def ep1001011_7 : Blocks := edgeBlocks% "full/vectors/1001011-E-0007.bin"
private noncomputable def ep1001011_8 : Blocks := edgeBlocks% "full/vectors/1001011-E-0008.bin"
private noncomputable def ep1001011_9 : Blocks := edgeBlocks% "full/vectors/1001011-E-0009.bin"
private noncomputable def ep1001011_10 : Blocks := edgeBlocks% "full/vectors/1001011-E-0010.bin"
private noncomputable def ep1001011_11 : Blocks := edgeBlocks% "full/vectors/1001011-E-0011.bin"
private noncomputable def ep1001011_12 : Blocks := edgeBlocks% "full/vectors/1001011-E-0012.bin"
private noncomputable def ep1001011_13 : Blocks := edgeBlocks% "full/vectors/1001011-E-0013.bin"
private noncomputable def ep1001011_14 : Blocks := edgeBlocks% "full/vectors/1001011-E-0014.bin"
noncomputable def ep1001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1001011_0 (Blocks.join ep1001011_1 ep1001011_2)) (Blocks.join (Blocks.join ep1001011_3 ep1001011_4) (Blocks.join ep1001011_5 ep1001011_6))) (Blocks.join (Blocks.join (Blocks.join ep1001011_7 ep1001011_8) (Blocks.join ep1001011_9 ep1001011_10)) (Blocks.join (Blocks.join ep1001011_11 ep1001011_12) (Blocks.join ep1001011_13 ep1001011_14))))
private theorem idp1001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100101.list =
    C ((2:ℤ)^2178) * horner X vp1001011.list + horner X ep1001011.list := by
  exact edge_identity (B := (2:ℤ)^2865) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001011 : Branch 1 (-4735761639/128000000 : ℚ) vp100101 := by
  apply branch_checked idp1001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4735761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-4799761639/64000000 : ℚ) by norm_num]
  exact coverp1001011
theorem coverp100101 : Covers (-4735761639/128000000 : ℚ) vp100101 := join_branches bp1001010 bp1001011
private noncomputable def vp10010011111_0 : Blocks := edgeBlocks% "full/vectors/10010011111-V-0000.bin"
noncomputable def vp10010011111 : Blocks := vp10010011111_0
theorem coverp10010011111 : Covers (-4731761639/4000000 : ℚ) vp10010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp10010011110_0 : Blocks := edgeBlocks% "full/vectors/10010011110-V-0000.bin"
noncomputable def vp10010011110 : Blocks := vp10010011110_0
theorem coverp10010011110 : Covers (-4727761639/4000000 : ℚ) vp10010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001001111_0 : Blocks := edgeBlocks% "full/vectors/1001001111-V-0000.bin"
private noncomputable def vp1001001111_1 : Blocks := edgeBlocks% "full/vectors/1001001111-V-0001.bin"
noncomputable def vp1001001111 : Blocks := (Blocks.join vp1001001111_0 vp1001001111_1)
private theorem bp10010011110 : Branch 0 (-4727761639/8000000 : ℚ) vp1001001111 := by
  apply branch_left_normalized (c:=vp10010011110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4727761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4727761639/4000000 : ℚ) by norm_num]
  exact coverp10010011110
private noncomputable def ep10010011111_0 : Blocks := edgeBlocks% "full/vectors/10010011111-E-0000.bin"
private noncomputable def ep10010011111_1 : Blocks := edgeBlocks% "full/vectors/10010011111-E-0001.bin"
noncomputable def ep10010011111 : Blocks := (Blocks.join ep10010011111_0 ep10010011111_1)
private theorem idp10010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001001111.list =
    C ((2:ℤ)^159) * horner X vp10010011111.list + horner X ep10010011111.list := by
  exact edge_identity (B := (2:ℤ)^298) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010011111 : Branch 1 (-4727761639/8000000 : ℚ) vp1001001111 := by
  apply branch_checked idp10010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-4727761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4731761639/4000000 : ℚ) by norm_num]
  exact coverp10010011111
theorem coverp1001001111 : Covers (-4727761639/8000000 : ℚ) vp1001001111 := join_branches bp10010011110 bp10010011111
private noncomputable def vp10010011101_0 : Blocks := edgeBlocks% "full/vectors/10010011101-V-0000.bin"
noncomputable def vp10010011101 : Blocks := vp10010011101_0
theorem coverp10010011101 : Covers (-4723761639/4000000 : ℚ) vp10010011101 := cover_leaf (by decide +kernel)
private noncomputable def vp10010011100_0 : Blocks := edgeBlocks% "full/vectors/10010011100-V-0000.bin"
noncomputable def vp10010011100 : Blocks := vp10010011100_0
theorem coverp10010011100 : Covers (-4719761639/4000000 : ℚ) vp10010011100 := cover_leaf (by decide +kernel)
private noncomputable def vp1001001110_0 : Blocks := edgeBlocks% "full/vectors/1001001110-V-0000.bin"
private noncomputable def vp1001001110_1 : Blocks := edgeBlocks% "full/vectors/1001001110-V-0001.bin"
noncomputable def vp1001001110 : Blocks := (Blocks.join vp1001001110_0 vp1001001110_1)
private theorem bp10010011100 : Branch 0 (-4719761639/8000000 : ℚ) vp1001001110 := by
  apply branch_left_normalized (c:=vp10010011100) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4719761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4719761639/4000000 : ℚ) by norm_num]
  exact coverp10010011100
private noncomputable def ep10010011101_0 : Blocks := edgeBlocks% "full/vectors/10010011101-E-0000.bin"
private noncomputable def ep10010011101_1 : Blocks := edgeBlocks% "full/vectors/10010011101-E-0001.bin"
noncomputable def ep10010011101 : Blocks := (Blocks.join ep10010011101_0 ep10010011101_1)
private theorem idp10010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001001110.list =
    C ((2:ℤ)^160) * horner X vp10010011101.list + horner X ep10010011101.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010011101 : Branch 1 (-4719761639/8000000 : ℚ) vp1001001110 := by
  apply branch_checked idp10010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-4719761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4723761639/4000000 : ℚ) by norm_num]
  exact coverp10010011101
theorem coverp1001001110 : Covers (-4719761639/8000000 : ℚ) vp1001001110 := join_branches bp10010011100 bp10010011101
private noncomputable def vp100100111_0 : Blocks := edgeBlocks% "full/vectors/100100111-V-0000.bin"
private noncomputable def vp100100111_1 : Blocks := edgeBlocks% "full/vectors/100100111-V-0001.bin"
noncomputable def vp100100111 : Blocks := (Blocks.join vp100100111_0 vp100100111_1)
private theorem bp1001001110 : Branch 0 (-4719761639/16000000 : ℚ) vp100100111 := by
  apply branch_left_normalized (c:=vp1001001110) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-4719761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4719761639/8000000 : ℚ) by norm_num]
  exact coverp1001001110
private noncomputable def ep1001001111_0 : Blocks := edgeBlocks% "full/vectors/1001001111-E-0000.bin"
private noncomputable def ep1001001111_1 : Blocks := edgeBlocks% "full/vectors/1001001111-E-0001.bin"
noncomputable def ep1001001111 : Blocks := (Blocks.join ep1001001111_0 ep1001001111_1)
private theorem idp1001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100100111.list =
    C ((2:ℤ)^298) * horner X vp1001001111.list + horner X ep1001001111.list := by
  exact edge_identity (B := (2:ℤ)^475) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001001111 : Branch 1 (-4719761639/16000000 : ℚ) vp100100111 := by
  apply branch_checked idp1001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4719761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4727761639/8000000 : ℚ) by norm_num]
  exact coverp1001001111
theorem coverp100100111 : Covers (-4719761639/16000000 : ℚ) vp100100111 := join_branches bp1001001110 bp1001001111
private noncomputable def vp10010011011_0 : Blocks := edgeBlocks% "full/vectors/10010011011-V-0000.bin"
noncomputable def vp10010011011 : Blocks := vp10010011011_0
theorem coverp10010011011 : Covers (-4715761639/4000000 : ℚ) vp10010011011 := cover_leaf (by decide +kernel)
private noncomputable def vp10010011010_0 : Blocks := edgeBlocks% "full/vectors/10010011010-V-0000.bin"
noncomputable def vp10010011010 : Blocks := vp10010011010_0
theorem coverp10010011010 : Covers (-4711761639/4000000 : ℚ) vp10010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001001101_0 : Blocks := edgeBlocks% "full/vectors/1001001101-V-0000.bin"
private noncomputable def vp1001001101_1 : Blocks := edgeBlocks% "full/vectors/1001001101-V-0001.bin"
noncomputable def vp1001001101 : Blocks := (Blocks.join vp1001001101_0 vp1001001101_1)
private theorem bp10010011010 : Branch 0 (-4711761639/8000000 : ℚ) vp1001001101 := by
  apply branch_left_normalized (c:=vp10010011010) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4711761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4711761639/4000000 : ℚ) by norm_num]
  exact coverp10010011010
private noncomputable def ep10010011011_0 : Blocks := edgeBlocks% "full/vectors/10010011011-E-0000.bin"
private noncomputable def ep10010011011_1 : Blocks := edgeBlocks% "full/vectors/10010011011-E-0001.bin"
noncomputable def ep10010011011 : Blocks := (Blocks.join ep10010011011_0 ep10010011011_1)
private theorem idp10010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001001101.list =
    C ((2:ℤ)^160) * horner X vp10010011011.list + horner X ep10010011011.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010011011 : Branch 1 (-4711761639/8000000 : ℚ) vp1001001101 := by
  apply branch_checked idp10010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-4711761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4715761639/4000000 : ℚ) by norm_num]
  exact coverp10010011011
theorem coverp1001001101 : Covers (-4711761639/8000000 : ℚ) vp1001001101 := join_branches bp10010011010 bp10010011011
private noncomputable def vp10010011001_0 : Blocks := edgeBlocks% "full/vectors/10010011001-V-0000.bin"
noncomputable def vp10010011001 : Blocks := vp10010011001_0
theorem coverp10010011001 : Covers (-4707761639/4000000 : ℚ) vp10010011001 := cover_leaf (by decide +kernel)
private noncomputable def vp10010011000_0 : Blocks := edgeBlocks% "full/vectors/10010011000-V-0000.bin"
noncomputable def vp10010011000 : Blocks := vp10010011000_0
theorem coverp10010011000 : Covers (-4703761639/4000000 : ℚ) vp10010011000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001001100_0 : Blocks := edgeBlocks% "full/vectors/1001001100-V-0000.bin"
private noncomputable def vp1001001100_1 : Blocks := edgeBlocks% "full/vectors/1001001100-V-0001.bin"
noncomputable def vp1001001100 : Blocks := (Blocks.join vp1001001100_0 vp1001001100_1)
private theorem bp10010011000 : Branch 0 (-4703761639/8000000 : ℚ) vp1001001100 := by
  apply branch_left_normalized (c:=vp10010011000) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4703761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4703761639/4000000 : ℚ) by norm_num]
  exact coverp10010011000
private noncomputable def ep10010011001_0 : Blocks := edgeBlocks% "full/vectors/10010011001-E-0000.bin"
private noncomputable def ep10010011001_1 : Blocks := edgeBlocks% "full/vectors/10010011001-E-0001.bin"
noncomputable def ep10010011001 : Blocks := (Blocks.join ep10010011001_0 ep10010011001_1)
private theorem idp10010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001001100.list =
    C ((2:ℤ)^160) * horner X vp10010011001.list + horner X ep10010011001.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010011001 : Branch 1 (-4703761639/8000000 : ℚ) vp1001001100 := by
  apply branch_checked idp10010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-4703761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4707761639/4000000 : ℚ) by norm_num]
  exact coverp10010011001
theorem coverp1001001100 : Covers (-4703761639/8000000 : ℚ) vp1001001100 := join_branches bp10010011000 bp10010011001
private noncomputable def vp100100110_0 : Blocks := edgeBlocks% "full/vectors/100100110-V-0000.bin"
private noncomputable def vp100100110_1 : Blocks := edgeBlocks% "full/vectors/100100110-V-0001.bin"
noncomputable def vp100100110 : Blocks := (Blocks.join vp100100110_0 vp100100110_1)
private theorem bp1001001100 : Branch 0 (-4703761639/16000000 : ℚ) vp100100110 := by
  apply branch_left_normalized (c:=vp1001001100) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-4703761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4703761639/8000000 : ℚ) by norm_num]
  exact coverp1001001100
private noncomputable def ep1001001101_0 : Blocks := edgeBlocks% "full/vectors/1001001101-E-0000.bin"
private noncomputable def ep1001001101_1 : Blocks := edgeBlocks% "full/vectors/1001001101-E-0001.bin"
noncomputable def ep1001001101 : Blocks := (Blocks.join ep1001001101_0 ep1001001101_1)
private theorem idp1001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100100110.list =
    C ((2:ℤ)^298) * horner X vp1001001101.list + horner X ep1001001101.list := by
  exact edge_identity (B := (2:ℤ)^475) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001001101 : Branch 1 (-4703761639/16000000 : ℚ) vp100100110 := by
  apply branch_checked idp1001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4703761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4711761639/8000000 : ℚ) by norm_num]
  exact coverp1001001101
theorem coverp100100110 : Covers (-4703761639/16000000 : ℚ) vp100100110 := join_branches bp1001001100 bp1001001101
private noncomputable def vp10010011_0 : Blocks := edgeBlocks% "full/vectors/10010011-V-0000.bin"
private noncomputable def vp10010011_1 : Blocks := edgeBlocks% "full/vectors/10010011-V-0001.bin"
private noncomputable def vp10010011_2 : Blocks := edgeBlocks% "full/vectors/10010011-V-0002.bin"
private noncomputable def vp10010011_3 : Blocks := edgeBlocks% "full/vectors/10010011-V-0003.bin"
noncomputable def vp10010011 : Blocks := (Blocks.join (Blocks.join vp10010011_0 vp10010011_1) (Blocks.join vp10010011_2 vp10010011_3))
private theorem bp100100110 : Branch 0 (-4703761639/32000000 : ℚ) vp10010011 := by
  apply branch_left_normalized (c:=vp100100110) (k:=0) (m:=251) (by decide +kernel)
  rw [show 2*(-4703761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4703761639/16000000 : ℚ) by norm_num]
  exact coverp100100110
private noncomputable def ep100100111_0 : Blocks := edgeBlocks% "full/vectors/100100111-E-0000.bin"
private noncomputable def ep100100111_1 : Blocks := edgeBlocks% "full/vectors/100100111-E-0001.bin"
private noncomputable def ep100100111_2 : Blocks := edgeBlocks% "full/vectors/100100111-E-0002.bin"
private noncomputable def ep100100111_3 : Blocks := edgeBlocks% "full/vectors/100100111-E-0003.bin"
noncomputable def ep100100111 : Blocks := (Blocks.join (Blocks.join ep100100111_0 ep100100111_1) (Blocks.join ep100100111_2 ep100100111_3))
private theorem idp100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10010011.list =
    C ((2:ℤ)^572) * horner X vp100100111.list + horner X ep100100111.list := by
  exact edge_identity (B := (2:ℤ)^824) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100100111 : Branch 1 (-4703761639/32000000 : ℚ) vp10010011 := by
  apply branch_checked idp100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-4703761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4719761639/16000000 : ℚ) by norm_num]
  exact coverp100100111
theorem coverp10010011 : Covers (-4703761639/32000000 : ℚ) vp10010011 := join_branches bp100100110 bp100100111
private noncomputable def vp10010010111_0 : Blocks := edgeBlocks% "full/vectors/10010010111-V-0000.bin"
noncomputable def vp10010010111 : Blocks := vp10010010111_0
theorem coverp10010010111 : Covers (-4699761639/4000000 : ℚ) vp10010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp10010010110_0 : Blocks := edgeBlocks% "full/vectors/10010010110-V-0000.bin"
noncomputable def vp10010010110 : Blocks := vp10010010110_0
theorem coverp10010010110 : Covers (-4695761639/4000000 : ℚ) vp10010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001001011_0 : Blocks := edgeBlocks% "full/vectors/1001001011-V-0000.bin"
private noncomputable def vp1001001011_1 : Blocks := edgeBlocks% "full/vectors/1001001011-V-0001.bin"
noncomputable def vp1001001011 : Blocks := (Blocks.join vp1001001011_0 vp1001001011_1)
private theorem bp10010010110 : Branch 0 (-4695761639/8000000 : ℚ) vp1001001011 := by
  apply branch_left_normalized (c:=vp10010010110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4695761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4695761639/4000000 : ℚ) by norm_num]
  exact coverp10010010110
private noncomputable def ep10010010111_0 : Blocks := edgeBlocks% "full/vectors/10010010111-E-0000.bin"
private noncomputable def ep10010010111_1 : Blocks := edgeBlocks% "full/vectors/10010010111-E-0001.bin"
noncomputable def ep10010010111 : Blocks := (Blocks.join ep10010010111_0 ep10010010111_1)
private theorem idp10010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001001011.list =
    C ((2:ℤ)^162) * horner X vp10010010111.list + horner X ep10010010111.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010010111 : Branch 1 (-4695761639/8000000 : ℚ) vp1001001011 := by
  apply branch_checked idp10010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-4695761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4699761639/4000000 : ℚ) by norm_num]
  exact coverp10010010111
theorem coverp1001001011 : Covers (-4695761639/8000000 : ℚ) vp1001001011 := join_branches bp10010010110 bp10010010111
private noncomputable def vp10010010101_0 : Blocks := edgeBlocks% "full/vectors/10010010101-V-0000.bin"
noncomputable def vp10010010101 : Blocks := vp10010010101_0
theorem coverp10010010101 : Covers (-4691761639/4000000 : ℚ) vp10010010101 := cover_leaf (by decide +kernel)
private noncomputable def vp10010010100_0 : Blocks := edgeBlocks% "full/vectors/10010010100-V-0000.bin"
noncomputable def vp10010010100 : Blocks := vp10010010100_0
theorem coverp10010010100 : Covers (-4687761639/4000000 : ℚ) vp10010010100 := cover_leaf (by decide +kernel)
private noncomputable def vp1001001010_0 : Blocks := edgeBlocks% "full/vectors/1001001010-V-0000.bin"
private noncomputable def vp1001001010_1 : Blocks := edgeBlocks% "full/vectors/1001001010-V-0001.bin"
noncomputable def vp1001001010 : Blocks := (Blocks.join vp1001001010_0 vp1001001010_1)
private theorem bp10010010100 : Branch 0 (-4687761639/8000000 : ℚ) vp1001001010 := by
  apply branch_left_normalized (c:=vp10010010100) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4687761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4687761639/4000000 : ℚ) by norm_num]
  exact coverp10010010100
private noncomputable def ep10010010101_0 : Blocks := edgeBlocks% "full/vectors/10010010101-E-0000.bin"
private noncomputable def ep10010010101_1 : Blocks := edgeBlocks% "full/vectors/10010010101-E-0001.bin"
noncomputable def ep10010010101 : Blocks := (Blocks.join ep10010010101_0 ep10010010101_1)
private theorem idp10010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001001010.list =
    C ((2:ℤ)^161) * horner X vp10010010101.list + horner X ep10010010101.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010010101 : Branch 1 (-4687761639/8000000 : ℚ) vp1001001010 := by
  apply branch_checked idp10010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4687761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4691761639/4000000 : ℚ) by norm_num]
  exact coverp10010010101
theorem coverp1001001010 : Covers (-4687761639/8000000 : ℚ) vp1001001010 := join_branches bp10010010100 bp10010010101
private noncomputable def vp100100101_0 : Blocks := edgeBlocks% "full/vectors/100100101-V-0000.bin"
private noncomputable def vp100100101_1 : Blocks := edgeBlocks% "full/vectors/100100101-V-0001.bin"
noncomputable def vp100100101 : Blocks := (Blocks.join vp100100101_0 vp100100101_1)
private theorem bp1001001010 : Branch 0 (-4687761639/16000000 : ℚ) vp100100101 := by
  apply branch_left_normalized (c:=vp1001001010) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-4687761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4687761639/8000000 : ℚ) by norm_num]
  exact coverp1001001010
private noncomputable def ep1001001011_0 : Blocks := edgeBlocks% "full/vectors/1001001011-E-0000.bin"
private noncomputable def ep1001001011_1 : Blocks := edgeBlocks% "full/vectors/1001001011-E-0001.bin"
noncomputable def ep1001001011 : Blocks := (Blocks.join ep1001001011_0 ep1001001011_1)
private theorem idp1001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100100101.list =
    C ((2:ℤ)^299) * horner X vp1001001011.list + horner X ep1001001011.list := by
  exact edge_identity (B := (2:ℤ)^476) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001001011 : Branch 1 (-4687761639/16000000 : ℚ) vp100100101 := by
  apply branch_checked idp1001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4687761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4695761639/8000000 : ℚ) by norm_num]
  exact coverp1001001011
theorem coverp100100101 : Covers (-4687761639/16000000 : ℚ) vp100100101 := join_branches bp1001001010 bp1001001011
private noncomputable def vp10010010011_0 : Blocks := edgeBlocks% "full/vectors/10010010011-V-0000.bin"
noncomputable def vp10010010011 : Blocks := vp10010010011_0
theorem coverp10010010011 : Covers (-4683761639/4000000 : ℚ) vp10010010011 := cover_leaf (by decide +kernel)
private noncomputable def vp10010010010_0 : Blocks := edgeBlocks% "full/vectors/10010010010-V-0000.bin"
noncomputable def vp10010010010 : Blocks := vp10010010010_0
theorem coverp10010010010 : Covers (-4679761639/4000000 : ℚ) vp10010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001001001_0 : Blocks := edgeBlocks% "full/vectors/1001001001-V-0000.bin"
private noncomputable def vp1001001001_1 : Blocks := edgeBlocks% "full/vectors/1001001001-V-0001.bin"
noncomputable def vp1001001001 : Blocks := (Blocks.join vp1001001001_0 vp1001001001_1)
private theorem bp10010010010 : Branch 0 (-4679761639/8000000 : ℚ) vp1001001001 := by
  apply branch_left_normalized (c:=vp10010010010) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4679761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4679761639/4000000 : ℚ) by norm_num]
  exact coverp10010010010
private noncomputable def ep10010010011_0 : Blocks := edgeBlocks% "full/vectors/10010010011-E-0000.bin"
private noncomputable def ep10010010011_1 : Blocks := edgeBlocks% "full/vectors/10010010011-E-0001.bin"
noncomputable def ep10010010011 : Blocks := (Blocks.join ep10010010011_0 ep10010010011_1)
private theorem idp10010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001001001.list =
    C ((2:ℤ)^160) * horner X vp10010010011.list + horner X ep10010010011.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010010011 : Branch 1 (-4679761639/8000000 : ℚ) vp1001001001 := by
  apply branch_checked idp10010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4679761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4683761639/4000000 : ℚ) by norm_num]
  exact coverp10010010011
theorem coverp1001001001 : Covers (-4679761639/8000000 : ℚ) vp1001001001 := join_branches bp10010010010 bp10010010011
private noncomputable def vp10010010001_0 : Blocks := edgeBlocks% "full/vectors/10010010001-V-0000.bin"
noncomputable def vp10010010001 : Blocks := vp10010010001_0
theorem coverp10010010001 : Covers (-4675761639/4000000 : ℚ) vp10010010001 := cover_leaf (by decide +kernel)
private noncomputable def vp10010010000_0 : Blocks := edgeBlocks% "full/vectors/10010010000-V-0000.bin"
noncomputable def vp10010010000 : Blocks := vp10010010000_0
theorem coverp10010010000 : Covers (-4671761639/4000000 : ℚ) vp10010010000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001001000_0 : Blocks := edgeBlocks% "full/vectors/1001001000-V-0000.bin"
private noncomputable def vp1001001000_1 : Blocks := edgeBlocks% "full/vectors/1001001000-V-0001.bin"
noncomputable def vp1001001000 : Blocks := (Blocks.join vp1001001000_0 vp1001001000_1)
private theorem bp10010010000 : Branch 0 (-4671761639/8000000 : ℚ) vp1001001000 := by
  apply branch_left_normalized (c:=vp10010010000) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4671761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4671761639/4000000 : ℚ) by norm_num]
  exact coverp10010010000
private noncomputable def ep10010010001_0 : Blocks := edgeBlocks% "full/vectors/10010010001-E-0000.bin"
private noncomputable def ep10010010001_1 : Blocks := edgeBlocks% "full/vectors/10010010001-E-0001.bin"
noncomputable def ep10010010001 : Blocks := (Blocks.join ep10010010001_0 ep10010010001_1)
private theorem idp10010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001001000.list =
    C ((2:ℤ)^160) * horner X vp10010010001.list + horner X ep10010010001.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010010001 : Branch 1 (-4671761639/8000000 : ℚ) vp1001001000 := by
  apply branch_checked idp10010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4671761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4675761639/4000000 : ℚ) by norm_num]
  exact coverp10010010001
theorem coverp1001001000 : Covers (-4671761639/8000000 : ℚ) vp1001001000 := join_branches bp10010010000 bp10010010001
private noncomputable def vp100100100_0 : Blocks := edgeBlocks% "full/vectors/100100100-V-0000.bin"
private noncomputable def vp100100100_1 : Blocks := edgeBlocks% "full/vectors/100100100-V-0001.bin"
noncomputable def vp100100100 : Blocks := (Blocks.join vp100100100_0 vp100100100_1)
private theorem bp1001001000 : Branch 0 (-4671761639/16000000 : ℚ) vp100100100 := by
  apply branch_left_normalized (c:=vp1001001000) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-4671761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4671761639/8000000 : ℚ) by norm_num]
  exact coverp1001001000
private noncomputable def ep1001001001_0 : Blocks := edgeBlocks% "full/vectors/1001001001-E-0000.bin"
private noncomputable def ep1001001001_1 : Blocks := edgeBlocks% "full/vectors/1001001001-E-0001.bin"
noncomputable def ep1001001001 : Blocks := (Blocks.join ep1001001001_0 ep1001001001_1)
private theorem idp1001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100100100.list =
    C ((2:ℤ)^299) * horner X vp1001001001.list + horner X ep1001001001.list := by
  exact edge_identity (B := (2:ℤ)^476) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001001001 : Branch 1 (-4671761639/16000000 : ℚ) vp100100100 := by
  apply branch_checked idp1001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4671761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4679761639/8000000 : ℚ) by norm_num]
  exact coverp1001001001
theorem coverp100100100 : Covers (-4671761639/16000000 : ℚ) vp100100100 := join_branches bp1001001000 bp1001001001
private noncomputable def vp10010010_0 : Blocks := edgeBlocks% "full/vectors/10010010-V-0000.bin"
private noncomputable def vp10010010_1 : Blocks := edgeBlocks% "full/vectors/10010010-V-0001.bin"
private noncomputable def vp10010010_2 : Blocks := edgeBlocks% "full/vectors/10010010-V-0002.bin"
private noncomputable def vp10010010_3 : Blocks := edgeBlocks% "full/vectors/10010010-V-0003.bin"
noncomputable def vp10010010 : Blocks := (Blocks.join (Blocks.join vp10010010_0 vp10010010_1) (Blocks.join vp10010010_2 vp10010010_3))
private theorem bp100100100 : Branch 0 (-4671761639/32000000 : ℚ) vp10010010 := by
  apply branch_left_normalized (c:=vp100100100) (k:=0) (m:=252) (by decide +kernel)
  rw [show 2*(-4671761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4671761639/16000000 : ℚ) by norm_num]
  exact coverp100100100
private noncomputable def ep100100101_0 : Blocks := edgeBlocks% "full/vectors/100100101-E-0000.bin"
private noncomputable def ep100100101_1 : Blocks := edgeBlocks% "full/vectors/100100101-E-0001.bin"
private noncomputable def ep100100101_2 : Blocks := edgeBlocks% "full/vectors/100100101-E-0002.bin"
private noncomputable def ep100100101_3 : Blocks := edgeBlocks% "full/vectors/100100101-E-0003.bin"
noncomputable def ep100100101 : Blocks := (Blocks.join (Blocks.join ep100100101_0 ep100100101_1) (Blocks.join ep100100101_2 ep100100101_3))
private theorem idp100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10010010.list =
    C ((2:ℤ)^572) * horner X vp100100101.list + horner X ep100100101.list := by
  exact edge_identity (B := (2:ℤ)^825) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100100101 : Branch 1 (-4671761639/32000000 : ℚ) vp10010010 := by
  apply branch_checked idp100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-4671761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4687761639/16000000 : ℚ) by norm_num]
  exact coverp100100101
theorem coverp10010010 : Covers (-4671761639/32000000 : ℚ) vp10010010 := join_branches bp100100100 bp100100101
private noncomputable def vp1001001_0 : Blocks := edgeBlocks% "full/vectors/1001001-V-0000.bin"
private noncomputable def vp1001001_1 : Blocks := edgeBlocks% "full/vectors/1001001-V-0001.bin"
private noncomputable def vp1001001_2 : Blocks := edgeBlocks% "full/vectors/1001001-V-0002.bin"
private noncomputable def vp1001001_3 : Blocks := edgeBlocks% "full/vectors/1001001-V-0003.bin"
private noncomputable def vp1001001_4 : Blocks := edgeBlocks% "full/vectors/1001001-V-0004.bin"
private noncomputable def vp1001001_5 : Blocks := edgeBlocks% "full/vectors/1001001-V-0005.bin"
private noncomputable def vp1001001_6 : Blocks := edgeBlocks% "full/vectors/1001001-V-0006.bin"
private noncomputable def vp1001001_7 : Blocks := edgeBlocks% "full/vectors/1001001-V-0007.bin"
noncomputable def vp1001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1001001_0 vp1001001_1) (Blocks.join vp1001001_2 vp1001001_3)) (Blocks.join (Blocks.join vp1001001_4 vp1001001_5) (Blocks.join vp1001001_6 vp1001001_7)))
private theorem bp10010010 : Branch 0 (-4671761639/64000000 : ℚ) vp1001001 := by
  apply branch_left_normalized (c:=vp10010010) (k:=0) (m:=479) (by decide +kernel)
  rw [show 2*(-4671761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4671761639/32000000 : ℚ) by norm_num]
  exact coverp10010010
private noncomputable def ep10010011_0 : Blocks := edgeBlocks% "full/vectors/10010011-E-0000.bin"
private noncomputable def ep10010011_1 : Blocks := edgeBlocks% "full/vectors/10010011-E-0001.bin"
private noncomputable def ep10010011_2 : Blocks := edgeBlocks% "full/vectors/10010011-E-0002.bin"
private noncomputable def ep10010011_3 : Blocks := edgeBlocks% "full/vectors/10010011-E-0003.bin"
private noncomputable def ep10010011_4 : Blocks := edgeBlocks% "full/vectors/10010011-E-0004.bin"
private noncomputable def ep10010011_5 : Blocks := edgeBlocks% "full/vectors/10010011-E-0005.bin"
private noncomputable def ep10010011_6 : Blocks := edgeBlocks% "full/vectors/10010011-E-0006.bin"
private noncomputable def ep10010011_7 : Blocks := edgeBlocks% "full/vectors/10010011-E-0007.bin"
noncomputable def ep10010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10010011_0 ep10010011_1) (Blocks.join ep10010011_2 ep10010011_3)) (Blocks.join (Blocks.join ep10010011_4 ep10010011_5) (Blocks.join ep10010011_6 ep10010011_7)))
private theorem idp10010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001001.list =
    C ((2:ℤ)^1116) * horner X vp10010011.list + horner X ep10010011.list := by
  exact edge_identity (B := (2:ℤ)^1519) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010011 : Branch 1 (-4671761639/64000000 : ℚ) vp1001001 := by
  apply branch_checked idp10010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4671761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4703761639/32000000 : ℚ) by norm_num]
  exact coverp10010011
theorem coverp1001001 : Covers (-4671761639/64000000 : ℚ) vp1001001 := join_branches bp10010010 bp10010011
private noncomputable def vp10010001111_0 : Blocks := edgeBlocks% "full/vectors/10010001111-V-0000.bin"
noncomputable def vp10010001111 : Blocks := vp10010001111_0
theorem coverp10010001111 : Covers (-4667761639/4000000 : ℚ) vp10010001111 := cover_leaf (by decide +kernel)
private noncomputable def vp10010001110_0 : Blocks := edgeBlocks% "full/vectors/10010001110-V-0000.bin"
noncomputable def vp10010001110 : Blocks := vp10010001110_0
theorem coverp10010001110 : Covers (-4663761639/4000000 : ℚ) vp10010001110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001000111_0 : Blocks := edgeBlocks% "full/vectors/1001000111-V-0000.bin"
private noncomputable def vp1001000111_1 : Blocks := edgeBlocks% "full/vectors/1001000111-V-0001.bin"
noncomputable def vp1001000111 : Blocks := (Blocks.join vp1001000111_0 vp1001000111_1)
private theorem bp10010001110 : Branch 0 (-4663761639/8000000 : ℚ) vp1001000111 := by
  apply branch_left_normalized (c:=vp10010001110) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4663761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4663761639/4000000 : ℚ) by norm_num]
  exact coverp10010001110
private noncomputable def ep10010001111_0 : Blocks := edgeBlocks% "full/vectors/10010001111-E-0000.bin"
private noncomputable def ep10010001111_1 : Blocks := edgeBlocks% "full/vectors/10010001111-E-0001.bin"
noncomputable def ep10010001111 : Blocks := (Blocks.join ep10010001111_0 ep10010001111_1)
private theorem idp10010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001000111.list =
    C ((2:ℤ)^161) * horner X vp10010001111.list + horner X ep10010001111.list := by
  exact edge_identity (B := (2:ℤ)^300) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010001111 : Branch 1 (-4663761639/8000000 : ℚ) vp1001000111 := by
  apply branch_checked idp10010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4663761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4667761639/4000000 : ℚ) by norm_num]
  exact coverp10010001111
theorem coverp1001000111 : Covers (-4663761639/8000000 : ℚ) vp1001000111 := join_branches bp10010001110 bp10010001111
private noncomputable def vp10010001101_0 : Blocks := edgeBlocks% "full/vectors/10010001101-V-0000.bin"
noncomputable def vp10010001101 : Blocks := vp10010001101_0
theorem coverp10010001101 : Covers (-4659761639/4000000 : ℚ) vp10010001101 := cover_leaf (by decide +kernel)
private noncomputable def vp10010001100_0 : Blocks := edgeBlocks% "full/vectors/10010001100-V-0000.bin"
noncomputable def vp10010001100 : Blocks := vp10010001100_0
theorem coverp10010001100 : Covers (-4655761639/4000000 : ℚ) vp10010001100 := cover_leaf (by decide +kernel)
private noncomputable def vp1001000110_0 : Blocks := edgeBlocks% "full/vectors/1001000110-V-0000.bin"
private noncomputable def vp1001000110_1 : Blocks := edgeBlocks% "full/vectors/1001000110-V-0001.bin"
noncomputable def vp1001000110 : Blocks := (Blocks.join vp1001000110_0 vp1001000110_1)
private theorem bp10010001100 : Branch 0 (-4655761639/8000000 : ℚ) vp1001000110 := by
  apply branch_left_normalized (c:=vp10010001100) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4655761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4655761639/4000000 : ℚ) by norm_num]
  exact coverp10010001100
private noncomputable def ep10010001101_0 : Blocks := edgeBlocks% "full/vectors/10010001101-E-0000.bin"
private noncomputable def ep10010001101_1 : Blocks := edgeBlocks% "full/vectors/10010001101-E-0001.bin"
noncomputable def ep10010001101 : Blocks := (Blocks.join ep10010001101_0 ep10010001101_1)
private theorem idp10010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001000110.list =
    C ((2:ℤ)^161) * horner X vp10010001101.list + horner X ep10010001101.list := by
  exact edge_identity (B := (2:ℤ)^300) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010001101 : Branch 1 (-4655761639/8000000 : ℚ) vp1001000110 := by
  apply branch_checked idp10010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4655761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4659761639/4000000 : ℚ) by norm_num]
  exact coverp10010001101
theorem coverp1001000110 : Covers (-4655761639/8000000 : ℚ) vp1001000110 := join_branches bp10010001100 bp10010001101
private noncomputable def vp100100011_0 : Blocks := edgeBlocks% "full/vectors/100100011-V-0000.bin"
private noncomputable def vp100100011_1 : Blocks := edgeBlocks% "full/vectors/100100011-V-0001.bin"
noncomputable def vp100100011 : Blocks := (Blocks.join vp100100011_0 vp100100011_1)
private theorem bp1001000110 : Branch 0 (-4655761639/16000000 : ℚ) vp100100011 := by
  apply branch_left_normalized (c:=vp1001000110) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-4655761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4655761639/8000000 : ℚ) by norm_num]
  exact coverp1001000110
private noncomputable def ep1001000111_0 : Blocks := edgeBlocks% "full/vectors/1001000111-E-0000.bin"
private noncomputable def ep1001000111_1 : Blocks := edgeBlocks% "full/vectors/1001000111-E-0001.bin"
noncomputable def ep1001000111 : Blocks := (Blocks.join ep1001000111_0 ep1001000111_1)
private theorem idp1001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100100011.list =
    C ((2:ℤ)^299) * horner X vp1001000111.list + horner X ep1001000111.list := by
  exact edge_identity (B := (2:ℤ)^476) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001000111 : Branch 1 (-4655761639/16000000 : ℚ) vp100100011 := by
  apply branch_checked idp1001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4655761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4663761639/8000000 : ℚ) by norm_num]
  exact coverp1001000111
theorem coverp100100011 : Covers (-4655761639/16000000 : ℚ) vp100100011 := join_branches bp1001000110 bp1001000111
private noncomputable def vp10010001011_0 : Blocks := edgeBlocks% "full/vectors/10010001011-V-0000.bin"
noncomputable def vp10010001011 : Blocks := vp10010001011_0
theorem coverp10010001011 : Covers (-4651761639/4000000 : ℚ) vp10010001011 := cover_leaf (by decide +kernel)
private noncomputable def vp10010001010_0 : Blocks := edgeBlocks% "full/vectors/10010001010-V-0000.bin"
noncomputable def vp10010001010 : Blocks := vp10010001010_0
theorem coverp10010001010 : Covers (-4647761639/4000000 : ℚ) vp10010001010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001000101_0 : Blocks := edgeBlocks% "full/vectors/1001000101-V-0000.bin"
private noncomputable def vp1001000101_1 : Blocks := edgeBlocks% "full/vectors/1001000101-V-0001.bin"
noncomputable def vp1001000101 : Blocks := (Blocks.join vp1001000101_0 vp1001000101_1)
private theorem bp10010001010 : Branch 0 (-4647761639/8000000 : ℚ) vp1001000101 := by
  apply branch_left_normalized (c:=vp10010001010) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4647761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4647761639/4000000 : ℚ) by norm_num]
  exact coverp10010001010
private noncomputable def ep10010001011_0 : Blocks := edgeBlocks% "full/vectors/10010001011-E-0000.bin"
private noncomputable def ep10010001011_1 : Blocks := edgeBlocks% "full/vectors/10010001011-E-0001.bin"
noncomputable def ep10010001011 : Blocks := (Blocks.join ep10010001011_0 ep10010001011_1)
private theorem idp10010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001000101.list =
    C ((2:ℤ)^162) * horner X vp10010001011.list + horner X ep10010001011.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010001011 : Branch 1 (-4647761639/8000000 : ℚ) vp1001000101 := by
  apply branch_checked idp10010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4647761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4651761639/4000000 : ℚ) by norm_num]
  exact coverp10010001011
theorem coverp1001000101 : Covers (-4647761639/8000000 : ℚ) vp1001000101 := join_branches bp10010001010 bp10010001011
private noncomputable def vp10010001001_0 : Blocks := edgeBlocks% "full/vectors/10010001001-V-0000.bin"
noncomputable def vp10010001001 : Blocks := vp10010001001_0
theorem coverp10010001001 : Covers (-4643761639/4000000 : ℚ) vp10010001001 := cover_leaf (by decide +kernel)
private noncomputable def vp10010001000_0 : Blocks := edgeBlocks% "full/vectors/10010001000-V-0000.bin"
noncomputable def vp10010001000 : Blocks := vp10010001000_0
theorem coverp10010001000 : Covers (-4639761639/4000000 : ℚ) vp10010001000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001000100_0 : Blocks := edgeBlocks% "full/vectors/1001000100-V-0000.bin"
private noncomputable def vp1001000100_1 : Blocks := edgeBlocks% "full/vectors/1001000100-V-0001.bin"
noncomputable def vp1001000100 : Blocks := (Blocks.join vp1001000100_0 vp1001000100_1)
private theorem bp10010001000 : Branch 0 (-4639761639/8000000 : ℚ) vp1001000100 := by
  apply branch_left_normalized (c:=vp10010001000) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4639761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4639761639/4000000 : ℚ) by norm_num]
  exact coverp10010001000
private noncomputable def ep10010001001_0 : Blocks := edgeBlocks% "full/vectors/10010001001-E-0000.bin"
private noncomputable def ep10010001001_1 : Blocks := edgeBlocks% "full/vectors/10010001001-E-0001.bin"
noncomputable def ep10010001001 : Blocks := (Blocks.join ep10010001001_0 ep10010001001_1)
private theorem idp10010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001000100.list =
    C ((2:ℤ)^161) * horner X vp10010001001.list + horner X ep10010001001.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010001001 : Branch 1 (-4639761639/8000000 : ℚ) vp1001000100 := by
  apply branch_checked idp10010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4639761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4643761639/4000000 : ℚ) by norm_num]
  exact coverp10010001001
theorem coverp1001000100 : Covers (-4639761639/8000000 : ℚ) vp1001000100 := join_branches bp10010001000 bp10010001001
private noncomputable def vp100100010_0 : Blocks := edgeBlocks% "full/vectors/100100010-V-0000.bin"
private noncomputable def vp100100010_1 : Blocks := edgeBlocks% "full/vectors/100100010-V-0001.bin"
noncomputable def vp100100010 : Blocks := (Blocks.join vp100100010_0 vp100100010_1)
private theorem bp1001000100 : Branch 0 (-4639761639/16000000 : ℚ) vp100100010 := by
  apply branch_left_normalized (c:=vp1001000100) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-4639761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4639761639/8000000 : ℚ) by norm_num]
  exact coverp1001000100
private noncomputable def ep1001000101_0 : Blocks := edgeBlocks% "full/vectors/1001000101-E-0000.bin"
private noncomputable def ep1001000101_1 : Blocks := edgeBlocks% "full/vectors/1001000101-E-0001.bin"
noncomputable def ep1001000101 : Blocks := (Blocks.join ep1001000101_0 ep1001000101_1)
private theorem idp1001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100100010.list =
    C ((2:ℤ)^300) * horner X vp1001000101.list + horner X ep1001000101.list := by
  exact edge_identity (B := (2:ℤ)^478) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001000101 : Branch 1 (-4639761639/16000000 : ℚ) vp100100010 := by
  apply branch_checked idp1001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4639761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4647761639/8000000 : ℚ) by norm_num]
  exact coverp1001000101
theorem coverp100100010 : Covers (-4639761639/16000000 : ℚ) vp100100010 := join_branches bp1001000100 bp1001000101
private noncomputable def vp10010001_0 : Blocks := edgeBlocks% "full/vectors/10010001-V-0000.bin"
private noncomputable def vp10010001_1 : Blocks := edgeBlocks% "full/vectors/10010001-V-0001.bin"
private noncomputable def vp10010001_2 : Blocks := edgeBlocks% "full/vectors/10010001-V-0002.bin"
private noncomputable def vp10010001_3 : Blocks := edgeBlocks% "full/vectors/10010001-V-0003.bin"
noncomputable def vp10010001 : Blocks := (Blocks.join (Blocks.join vp10010001_0 vp10010001_1) (Blocks.join vp10010001_2 vp10010001_3))
private theorem bp100100010 : Branch 0 (-4639761639/32000000 : ℚ) vp10010001 := by
  apply branch_left_normalized (c:=vp100100010) (k:=0) (m:=253) (by decide +kernel)
  rw [show 2*(-4639761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4639761639/16000000 : ℚ) by norm_num]
  exact coverp100100010
private noncomputable def ep100100011_0 : Blocks := edgeBlocks% "full/vectors/100100011-E-0000.bin"
private noncomputable def ep100100011_1 : Blocks := edgeBlocks% "full/vectors/100100011-E-0001.bin"
private noncomputable def ep100100011_2 : Blocks := edgeBlocks% "full/vectors/100100011-E-0002.bin"
private noncomputable def ep100100011_3 : Blocks := edgeBlocks% "full/vectors/100100011-E-0003.bin"
noncomputable def ep100100011 : Blocks := (Blocks.join (Blocks.join ep100100011_0 ep100100011_1) (Blocks.join ep100100011_2 ep100100011_3))
private theorem idp100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10010001.list =
    C ((2:ℤ)^576) * horner X vp100100011.list + horner X ep100100011.list := by
  exact edge_identity (B := (2:ℤ)^829) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100100011 : Branch 1 (-4639761639/32000000 : ℚ) vp10010001 := by
  apply branch_checked idp100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-4639761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4655761639/16000000 : ℚ) by norm_num]
  exact coverp100100011
theorem coverp10010001 : Covers (-4639761639/32000000 : ℚ) vp10010001 := join_branches bp100100010 bp100100011
private noncomputable def vp10010000111_0 : Blocks := edgeBlocks% "full/vectors/10010000111-V-0000.bin"
noncomputable def vp10010000111 : Blocks := vp10010000111_0
theorem coverp10010000111 : Covers (-4635761639/4000000 : ℚ) vp10010000111 := cover_leaf (by decide +kernel)
private noncomputable def vp10010000110_0 : Blocks := edgeBlocks% "full/vectors/10010000110-V-0000.bin"
noncomputable def vp10010000110 : Blocks := vp10010000110_0
theorem coverp10010000110 : Covers (-4631761639/4000000 : ℚ) vp10010000110 := cover_leaf (by decide +kernel)
private noncomputable def vp1001000011_0 : Blocks := edgeBlocks% "full/vectors/1001000011-V-0000.bin"
private noncomputable def vp1001000011_1 : Blocks := edgeBlocks% "full/vectors/1001000011-V-0001.bin"
noncomputable def vp1001000011 : Blocks := (Blocks.join vp1001000011_0 vp1001000011_1)
private theorem bp10010000110 : Branch 0 (-4631761639/8000000 : ℚ) vp1001000011 := by
  apply branch_left_normalized (c:=vp10010000110) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4631761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4631761639/4000000 : ℚ) by norm_num]
  exact coverp10010000110
private noncomputable def ep10010000111_0 : Blocks := edgeBlocks% "full/vectors/10010000111-E-0000.bin"
private noncomputable def ep10010000111_1 : Blocks := edgeBlocks% "full/vectors/10010000111-E-0001.bin"
noncomputable def ep10010000111 : Blocks := (Blocks.join ep10010000111_0 ep10010000111_1)
private theorem idp10010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001000011.list =
    C ((2:ℤ)^161) * horner X vp10010000111.list + horner X ep10010000111.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010000111 : Branch 1 (-4631761639/8000000 : ℚ) vp1001000011 := by
  apply branch_checked idp10010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4631761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4635761639/4000000 : ℚ) by norm_num]
  exact coverp10010000111
theorem coverp1001000011 : Covers (-4631761639/8000000 : ℚ) vp1001000011 := join_branches bp10010000110 bp10010000111
private noncomputable def vp10010000101_0 : Blocks := edgeBlocks% "full/vectors/10010000101-V-0000.bin"
noncomputable def vp10010000101 : Blocks := vp10010000101_0
theorem coverp10010000101 : Covers (-4627761639/4000000 : ℚ) vp10010000101 := cover_leaf (by decide +kernel)
private noncomputable def vp10010000100_0 : Blocks := edgeBlocks% "full/vectors/10010000100-V-0000.bin"
noncomputable def vp10010000100 : Blocks := vp10010000100_0
theorem coverp10010000100 : Covers (-4623761639/4000000 : ℚ) vp10010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp1001000010_0 : Blocks := edgeBlocks% "full/vectors/1001000010-V-0000.bin"
private noncomputable def vp1001000010_1 : Blocks := edgeBlocks% "full/vectors/1001000010-V-0001.bin"
noncomputable def vp1001000010 : Blocks := (Blocks.join vp1001000010_0 vp1001000010_1)
private theorem bp10010000100 : Branch 0 (-4623761639/8000000 : ℚ) vp1001000010 := by
  apply branch_left_normalized (c:=vp10010000100) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4623761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4623761639/4000000 : ℚ) by norm_num]
  exact coverp10010000100
private noncomputable def ep10010000101_0 : Blocks := edgeBlocks% "full/vectors/10010000101-E-0000.bin"
private noncomputable def ep10010000101_1 : Blocks := edgeBlocks% "full/vectors/10010000101-E-0001.bin"
noncomputable def ep10010000101 : Blocks := (Blocks.join ep10010000101_0 ep10010000101_1)
private theorem idp10010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001000010.list =
    C ((2:ℤ)^161) * horner X vp10010000101.list + horner X ep10010000101.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010000101 : Branch 1 (-4623761639/8000000 : ℚ) vp1001000010 := by
  apply branch_checked idp10010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4623761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4627761639/4000000 : ℚ) by norm_num]
  exact coverp10010000101
theorem coverp1001000010 : Covers (-4623761639/8000000 : ℚ) vp1001000010 := join_branches bp10010000100 bp10010000101
private noncomputable def vp100100001_0 : Blocks := edgeBlocks% "full/vectors/100100001-V-0000.bin"
private noncomputable def vp100100001_1 : Blocks := edgeBlocks% "full/vectors/100100001-V-0001.bin"
noncomputable def vp100100001 : Blocks := (Blocks.join vp100100001_0 vp100100001_1)
private theorem bp1001000010 : Branch 0 (-4623761639/16000000 : ℚ) vp100100001 := by
  apply branch_left_normalized (c:=vp1001000010) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-4623761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4623761639/8000000 : ℚ) by norm_num]
  exact coverp1001000010
private noncomputable def ep1001000011_0 : Blocks := edgeBlocks% "full/vectors/1001000011-E-0000.bin"
private noncomputable def ep1001000011_1 : Blocks := edgeBlocks% "full/vectors/1001000011-E-0001.bin"
noncomputable def ep1001000011 : Blocks := (Blocks.join ep1001000011_0 ep1001000011_1)
private theorem idp1001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100100001.list =
    C ((2:ℤ)^300) * horner X vp1001000011.list + horner X ep1001000011.list := by
  exact edge_identity (B := (2:ℤ)^478) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001000011 : Branch 1 (-4623761639/16000000 : ℚ) vp100100001 := by
  apply branch_checked idp1001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-4623761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4631761639/8000000 : ℚ) by norm_num]
  exact coverp1001000011
theorem coverp100100001 : Covers (-4623761639/16000000 : ℚ) vp100100001 := join_branches bp1001000010 bp1001000011
private noncomputable def vp10010000011_0 : Blocks := edgeBlocks% "full/vectors/10010000011-V-0000.bin"
noncomputable def vp10010000011 : Blocks := vp10010000011_0
theorem coverp10010000011 : Covers (-4619761639/4000000 : ℚ) vp10010000011 := cover_leaf (by decide +kernel)
private noncomputable def vp10010000010_0 : Blocks := edgeBlocks% "full/vectors/10010000010-V-0000.bin"
noncomputable def vp10010000010 : Blocks := vp10010000010_0
theorem coverp10010000010 : Covers (-4615761639/4000000 : ℚ) vp10010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp1001000001_0 : Blocks := edgeBlocks% "full/vectors/1001000001-V-0000.bin"
private noncomputable def vp1001000001_1 : Blocks := edgeBlocks% "full/vectors/1001000001-V-0001.bin"
noncomputable def vp1001000001 : Blocks := (Blocks.join vp1001000001_0 vp1001000001_1)
private theorem bp10010000010 : Branch 0 (-4615761639/8000000 : ℚ) vp1001000001 := by
  apply branch_left_normalized (c:=vp10010000010) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4615761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4615761639/4000000 : ℚ) by norm_num]
  exact coverp10010000010
private noncomputable def ep10010000011_0 : Blocks := edgeBlocks% "full/vectors/10010000011-E-0000.bin"
private noncomputable def ep10010000011_1 : Blocks := edgeBlocks% "full/vectors/10010000011-E-0001.bin"
noncomputable def ep10010000011 : Blocks := (Blocks.join ep10010000011_0 ep10010000011_1)
private theorem idp10010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001000001.list =
    C ((2:ℤ)^160) * horner X vp10010000011.list + horner X ep10010000011.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010000011 : Branch 1 (-4615761639/8000000 : ℚ) vp1001000001 := by
  apply branch_checked idp10010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-4615761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4619761639/4000000 : ℚ) by norm_num]
  exact coverp10010000011
theorem coverp1001000001 : Covers (-4615761639/8000000 : ℚ) vp1001000001 := join_branches bp10010000010 bp10010000011
private noncomputable def vp10010000001_0 : Blocks := edgeBlocks% "full/vectors/10010000001-V-0000.bin"
noncomputable def vp10010000001 : Blocks := vp10010000001_0
theorem coverp10010000001 : Covers (-4611761639/4000000 : ℚ) vp10010000001 := cover_leaf (by decide +kernel)
private noncomputable def vp10010000000_0 : Blocks := edgeBlocks% "full/vectors/10010000000-V-0000.bin"
noncomputable def vp10010000000 : Blocks := vp10010000000_0
theorem coverp10010000000 : Covers (-4607761639/4000000 : ℚ) vp10010000000 := cover_leaf (by decide +kernel)
private noncomputable def vp1001000000_0 : Blocks := edgeBlocks% "full/vectors/1001000000-V-0000.bin"
private noncomputable def vp1001000000_1 : Blocks := edgeBlocks% "full/vectors/1001000000-V-0001.bin"
noncomputable def vp1001000000 : Blocks := (Blocks.join vp1001000000_0 vp1001000000_1)
private theorem bp10010000000 : Branch 0 (-4607761639/8000000 : ℚ) vp1001000000 := by
  apply branch_left_normalized (c:=vp10010000000) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4607761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4607761639/4000000 : ℚ) by norm_num]
  exact coverp10010000000
private noncomputable def ep10010000001_0 : Blocks := edgeBlocks% "full/vectors/10010000001-E-0000.bin"
private noncomputable def ep10010000001_1 : Blocks := edgeBlocks% "full/vectors/10010000001-E-0001.bin"
noncomputable def ep10010000001 : Blocks := (Blocks.join ep10010000001_0 ep10010000001_1)
private theorem idp10010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001000000.list =
    C ((2:ℤ)^162) * horner X vp10010000001.list + horner X ep10010000001.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010000001 : Branch 1 (-4607761639/8000000 : ℚ) vp1001000000 := by
  apply branch_checked idp10010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-4607761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4611761639/4000000 : ℚ) by norm_num]
  exact coverp10010000001
theorem coverp1001000000 : Covers (-4607761639/8000000 : ℚ) vp1001000000 := join_branches bp10010000000 bp10010000001
private noncomputable def vp100100000_0 : Blocks := edgeBlocks% "full/vectors/100100000-V-0000.bin"
private noncomputable def vp100100000_1 : Blocks := edgeBlocks% "full/vectors/100100000-V-0001.bin"
noncomputable def vp100100000 : Blocks := (Blocks.join vp100100000_0 vp100100000_1)
private theorem bp1001000000 : Branch 0 (-4607761639/16000000 : ℚ) vp100100000 := by
  apply branch_left_normalized (c:=vp1001000000) (k:=0) (m:=138) (by decide +kernel)
  rw [show 2*(-4607761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4607761639/8000000 : ℚ) by norm_num]
  exact coverp1001000000
private noncomputable def ep1001000001_0 : Blocks := edgeBlocks% "full/vectors/1001000001-E-0000.bin"
private noncomputable def ep1001000001_1 : Blocks := edgeBlocks% "full/vectors/1001000001-E-0001.bin"
noncomputable def ep1001000001 : Blocks := (Blocks.join ep1001000001_0 ep1001000001_1)
private theorem idp1001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100100000.list =
    C ((2:ℤ)^300) * horner X vp1001000001.list + horner X ep1001000001.list := by
  exact edge_identity (B := (2:ℤ)^478) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001000001 : Branch 1 (-4607761639/16000000 : ℚ) vp100100000 := by
  apply branch_checked idp1001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-4607761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4615761639/8000000 : ℚ) by norm_num]
  exact coverp1001000001
theorem coverp100100000 : Covers (-4607761639/16000000 : ℚ) vp100100000 := join_branches bp1001000000 bp1001000001
private noncomputable def vp10010000_0 : Blocks := edgeBlocks% "full/vectors/10010000-V-0000.bin"
private noncomputable def vp10010000_1 : Blocks := edgeBlocks% "full/vectors/10010000-V-0001.bin"
private noncomputable def vp10010000_2 : Blocks := edgeBlocks% "full/vectors/10010000-V-0002.bin"
private noncomputable def vp10010000_3 : Blocks := edgeBlocks% "full/vectors/10010000-V-0003.bin"
noncomputable def vp10010000 : Blocks := (Blocks.join (Blocks.join vp10010000_0 vp10010000_1) (Blocks.join vp10010000_2 vp10010000_3))
private theorem bp100100000 : Branch 0 (-4607761639/32000000 : ℚ) vp10010000 := by
  apply branch_left_normalized (c:=vp100100000) (k:=0) (m:=253) (by decide +kernel)
  rw [show 2*(-4607761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4607761639/16000000 : ℚ) by norm_num]
  exact coverp100100000
private noncomputable def ep100100001_0 : Blocks := edgeBlocks% "full/vectors/100100001-E-0000.bin"
private noncomputable def ep100100001_1 : Blocks := edgeBlocks% "full/vectors/100100001-E-0001.bin"
private noncomputable def ep100100001_2 : Blocks := edgeBlocks% "full/vectors/100100001-E-0002.bin"
private noncomputable def ep100100001_3 : Blocks := edgeBlocks% "full/vectors/100100001-E-0003.bin"
noncomputable def ep100100001 : Blocks := (Blocks.join (Blocks.join ep100100001_0 ep100100001_1) (Blocks.join ep100100001_2 ep100100001_3))
private theorem idp100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10010000.list =
    C ((2:ℤ)^576) * horner X vp100100001.list + horner X ep100100001.list := by
  exact edge_identity (B := (2:ℤ)^830) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100100001 : Branch 1 (-4607761639/32000000 : ℚ) vp10010000 := by
  apply branch_checked idp100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-4607761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4623761639/16000000 : ℚ) by norm_num]
  exact coverp100100001
theorem coverp10010000 : Covers (-4607761639/32000000 : ℚ) vp10010000 := join_branches bp100100000 bp100100001
private noncomputable def vp1001000_0 : Blocks := edgeBlocks% "full/vectors/1001000-V-0000.bin"
private noncomputable def vp1001000_1 : Blocks := edgeBlocks% "full/vectors/1001000-V-0001.bin"
private noncomputable def vp1001000_2 : Blocks := edgeBlocks% "full/vectors/1001000-V-0002.bin"
private noncomputable def vp1001000_3 : Blocks := edgeBlocks% "full/vectors/1001000-V-0003.bin"
private noncomputable def vp1001000_4 : Blocks := edgeBlocks% "full/vectors/1001000-V-0004.bin"
private noncomputable def vp1001000_5 : Blocks := edgeBlocks% "full/vectors/1001000-V-0005.bin"
private noncomputable def vp1001000_6 : Blocks := edgeBlocks% "full/vectors/1001000-V-0006.bin"
private noncomputable def vp1001000_7 : Blocks := edgeBlocks% "full/vectors/1001000-V-0007.bin"
noncomputable def vp1001000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1001000_0 vp1001000_1) (Blocks.join vp1001000_2 vp1001000_3)) (Blocks.join (Blocks.join vp1001000_4 vp1001000_5) (Blocks.join vp1001000_6 vp1001000_7)))
private theorem bp10010000 : Branch 0 (-4607761639/64000000 : ℚ) vp1001000 := by
  apply branch_left_normalized (c:=vp10010000) (k:=0) (m:=483) (by decide +kernel)
  rw [show 2*(-4607761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4607761639/32000000 : ℚ) by norm_num]
  exact coverp10010000
private noncomputable def ep10010001_0 : Blocks := edgeBlocks% "full/vectors/10010001-E-0000.bin"
private noncomputable def ep10010001_1 : Blocks := edgeBlocks% "full/vectors/10010001-E-0001.bin"
private noncomputable def ep10010001_2 : Blocks := edgeBlocks% "full/vectors/10010001-E-0002.bin"
private noncomputable def ep10010001_3 : Blocks := edgeBlocks% "full/vectors/10010001-E-0003.bin"
private noncomputable def ep10010001_4 : Blocks := edgeBlocks% "full/vectors/10010001-E-0004.bin"
private noncomputable def ep10010001_5 : Blocks := edgeBlocks% "full/vectors/10010001-E-0005.bin"
private noncomputable def ep10010001_6 : Blocks := edgeBlocks% "full/vectors/10010001-E-0006.bin"
private noncomputable def ep10010001_7 : Blocks := edgeBlocks% "full/vectors/10010001-E-0007.bin"
noncomputable def ep10010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10010001_0 ep10010001_1) (Blocks.join ep10010001_2 ep10010001_3)) (Blocks.join (Blocks.join ep10010001_4 ep10010001_5) (Blocks.join ep10010001_6 ep10010001_7)))
private theorem idp10010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001000.list =
    C ((2:ℤ)^1122) * horner X vp10010001.list + horner X ep10010001.list := by
  exact edge_identity (B := (2:ℤ)^1529) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10010001 : Branch 1 (-4607761639/64000000 : ℚ) vp1001000 := by
  apply branch_checked idp10010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4607761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4639761639/32000000 : ℚ) by norm_num]
  exact coverp10010001
theorem coverp1001000 : Covers (-4607761639/64000000 : ℚ) vp1001000 := join_branches bp10010000 bp10010001
private noncomputable def vp100100_0 : Blocks := edgeBlocks% "full/vectors/100100-V-0000.bin"
private noncomputable def vp100100_1 : Blocks := edgeBlocks% "full/vectors/100100-V-0001.bin"
private noncomputable def vp100100_2 : Blocks := edgeBlocks% "full/vectors/100100-V-0002.bin"
private noncomputable def vp100100_3 : Blocks := edgeBlocks% "full/vectors/100100-V-0003.bin"
private noncomputable def vp100100_4 : Blocks := edgeBlocks% "full/vectors/100100-V-0004.bin"
private noncomputable def vp100100_5 : Blocks := edgeBlocks% "full/vectors/100100-V-0005.bin"
private noncomputable def vp100100_6 : Blocks := edgeBlocks% "full/vectors/100100-V-0006.bin"
private noncomputable def vp100100_7 : Blocks := edgeBlocks% "full/vectors/100100-V-0007.bin"
private noncomputable def vp100100_8 : Blocks := edgeBlocks% "full/vectors/100100-V-0008.bin"
private noncomputable def vp100100_9 : Blocks := edgeBlocks% "full/vectors/100100-V-0009.bin"
private noncomputable def vp100100_10 : Blocks := edgeBlocks% "full/vectors/100100-V-0010.bin"
private noncomputable def vp100100_11 : Blocks := edgeBlocks% "full/vectors/100100-V-0011.bin"
private noncomputable def vp100100_12 : Blocks := edgeBlocks% "full/vectors/100100-V-0012.bin"
private noncomputable def vp100100_13 : Blocks := edgeBlocks% "full/vectors/100100-V-0013.bin"
private noncomputable def vp100100_14 : Blocks := edgeBlocks% "full/vectors/100100-V-0014.bin"
noncomputable def vp100100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp100100_0 (Blocks.join vp100100_1 vp100100_2)) (Blocks.join (Blocks.join vp100100_3 vp100100_4) (Blocks.join vp100100_5 vp100100_6))) (Blocks.join (Blocks.join (Blocks.join vp100100_7 vp100100_8) (Blocks.join vp100100_9 vp100100_10)) (Blocks.join (Blocks.join vp100100_11 vp100100_12) (Blocks.join vp100100_13 vp100100_14))))
private theorem bp1001000 : Branch 0 (-4607761639/128000000 : ℚ) vp100100 := by
  apply branch_left_normalized (c:=vp1001000) (k:=0) (m:=937) (by decide +kernel)
  rw [show 2*(-4607761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-4607761639/64000000 : ℚ) by norm_num]
  exact coverp1001000
private noncomputable def ep1001001_0 : Blocks := edgeBlocks% "full/vectors/1001001-E-0000.bin"
private noncomputable def ep1001001_1 : Blocks := edgeBlocks% "full/vectors/1001001-E-0001.bin"
private noncomputable def ep1001001_2 : Blocks := edgeBlocks% "full/vectors/1001001-E-0002.bin"
private noncomputable def ep1001001_3 : Blocks := edgeBlocks% "full/vectors/1001001-E-0003.bin"
private noncomputable def ep1001001_4 : Blocks := edgeBlocks% "full/vectors/1001001-E-0004.bin"
private noncomputable def ep1001001_5 : Blocks := edgeBlocks% "full/vectors/1001001-E-0005.bin"
private noncomputable def ep1001001_6 : Blocks := edgeBlocks% "full/vectors/1001001-E-0006.bin"
private noncomputable def ep1001001_7 : Blocks := edgeBlocks% "full/vectors/1001001-E-0007.bin"
private noncomputable def ep1001001_8 : Blocks := edgeBlocks% "full/vectors/1001001-E-0008.bin"
private noncomputable def ep1001001_9 : Blocks := edgeBlocks% "full/vectors/1001001-E-0009.bin"
private noncomputable def ep1001001_10 : Blocks := edgeBlocks% "full/vectors/1001001-E-0010.bin"
private noncomputable def ep1001001_11 : Blocks := edgeBlocks% "full/vectors/1001001-E-0011.bin"
private noncomputable def ep1001001_12 : Blocks := edgeBlocks% "full/vectors/1001001-E-0012.bin"
private noncomputable def ep1001001_13 : Blocks := edgeBlocks% "full/vectors/1001001-E-0013.bin"
private noncomputable def ep1001001_14 : Blocks := edgeBlocks% "full/vectors/1001001-E-0014.bin"
noncomputable def ep1001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1001001_0 (Blocks.join ep1001001_1 ep1001001_2)) (Blocks.join (Blocks.join ep1001001_3 ep1001001_4) (Blocks.join ep1001001_5 ep1001001_6))) (Blocks.join (Blocks.join (Blocks.join ep1001001_7 ep1001001_8) (Blocks.join ep1001001_9 ep1001001_10)) (Blocks.join (Blocks.join ep1001001_11 ep1001001_12) (Blocks.join ep1001001_13 ep1001001_14))))
private theorem idp1001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100100.list =
    C ((2:ℤ)^2195) * horner X vp1001001.list + horner X ep1001001.list := by
  exact edge_identity (B := (2:ℤ)^2902) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1001001 : Branch 1 (-4607761639/128000000 : ℚ) vp100100 := by
  apply branch_checked idp1001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4607761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-4671761639/64000000 : ℚ) by norm_num]
  exact coverp1001001
theorem coverp100100 : Covers (-4607761639/128000000 : ℚ) vp100100 := join_branches bp1001000 bp1001001
private noncomputable def vp10010_0 : Blocks := edgeBlocks% "full/vectors/10010-V-0000.bin"
private noncomputable def vp10010_1 : Blocks := edgeBlocks% "full/vectors/10010-V-0001.bin"
private noncomputable def vp10010_2 : Blocks := edgeBlocks% "full/vectors/10010-V-0002.bin"
private noncomputable def vp10010_3 : Blocks := edgeBlocks% "full/vectors/10010-V-0003.bin"
private noncomputable def vp10010_4 : Blocks := edgeBlocks% "full/vectors/10010-V-0004.bin"
private noncomputable def vp10010_5 : Blocks := edgeBlocks% "full/vectors/10010-V-0005.bin"
private noncomputable def vp10010_6 : Blocks := edgeBlocks% "full/vectors/10010-V-0006.bin"
private noncomputable def vp10010_7 : Blocks := edgeBlocks% "full/vectors/10010-V-0007.bin"
private noncomputable def vp10010_8 : Blocks := edgeBlocks% "full/vectors/10010-V-0008.bin"
private noncomputable def vp10010_9 : Blocks := edgeBlocks% "full/vectors/10010-V-0009.bin"
private noncomputable def vp10010_10 : Blocks := edgeBlocks% "full/vectors/10010-V-0010.bin"
private noncomputable def vp10010_11 : Blocks := edgeBlocks% "full/vectors/10010-V-0011.bin"
private noncomputable def vp10010_12 : Blocks := edgeBlocks% "full/vectors/10010-V-0012.bin"
private noncomputable def vp10010_13 : Blocks := edgeBlocks% "full/vectors/10010-V-0013.bin"
private noncomputable def vp10010_14 : Blocks := edgeBlocks% "full/vectors/10010-V-0014.bin"
private noncomputable def vp10010_15 : Blocks := edgeBlocks% "full/vectors/10010-V-0015.bin"
private noncomputable def vp10010_16 : Blocks := edgeBlocks% "full/vectors/10010-V-0016.bin"
private noncomputable def vp10010_17 : Blocks := edgeBlocks% "full/vectors/10010-V-0017.bin"
private noncomputable def vp10010_18 : Blocks := edgeBlocks% "full/vectors/10010-V-0018.bin"
private noncomputable def vp10010_19 : Blocks := edgeBlocks% "full/vectors/10010-V-0019.bin"
private noncomputable def vp10010_20 : Blocks := edgeBlocks% "full/vectors/10010-V-0020.bin"
private noncomputable def vp10010_21 : Blocks := edgeBlocks% "full/vectors/10010-V-0021.bin"
private noncomputable def vp10010_22 : Blocks := edgeBlocks% "full/vectors/10010-V-0022.bin"
private noncomputable def vp10010_23 : Blocks := edgeBlocks% "full/vectors/10010-V-0023.bin"
private noncomputable def vp10010_24 : Blocks := edgeBlocks% "full/vectors/10010-V-0024.bin"
private noncomputable def vp10010_25 : Blocks := edgeBlocks% "full/vectors/10010-V-0025.bin"
private noncomputable def vp10010_26 : Blocks := edgeBlocks% "full/vectors/10010-V-0026.bin"
private noncomputable def vp10010_27 : Blocks := edgeBlocks% "full/vectors/10010-V-0027.bin"
noncomputable def vp10010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp10010_0 (Blocks.join vp10010_1 vp10010_2)) (Blocks.join (Blocks.join vp10010_3 vp10010_4) (Blocks.join vp10010_5 vp10010_6))) (Blocks.join (Blocks.join vp10010_7 (Blocks.join vp10010_8 vp10010_9)) (Blocks.join (Blocks.join vp10010_10 vp10010_11) (Blocks.join vp10010_12 vp10010_13)))) (Blocks.join (Blocks.join (Blocks.join vp10010_14 (Blocks.join vp10010_15 vp10010_16)) (Blocks.join (Blocks.join vp10010_17 vp10010_18) (Blocks.join vp10010_19 vp10010_20))) (Blocks.join (Blocks.join vp10010_21 (Blocks.join vp10010_22 vp10010_23)) (Blocks.join (Blocks.join vp10010_24 vp10010_25) (Blocks.join vp10010_26 vp10010_27)))))
private theorem bp100100 : Branch 0 (-4607761639/256000000 : ℚ) vp10010 := by
  apply branch_left_normalized (c:=vp100100) (k:=0) (m:=1825) (by decide +kernel)
  rw [show 2*(-4607761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-4607761639/128000000 : ℚ) by norm_num]
  exact coverp100100
private noncomputable def ep100101_0 : Blocks := edgeBlocks% "full/vectors/100101-E-0000.bin"
private noncomputable def ep100101_1 : Blocks := edgeBlocks% "full/vectors/100101-E-0001.bin"
private noncomputable def ep100101_2 : Blocks := edgeBlocks% "full/vectors/100101-E-0002.bin"
private noncomputable def ep100101_3 : Blocks := edgeBlocks% "full/vectors/100101-E-0003.bin"
private noncomputable def ep100101_4 : Blocks := edgeBlocks% "full/vectors/100101-E-0004.bin"
private noncomputable def ep100101_5 : Blocks := edgeBlocks% "full/vectors/100101-E-0005.bin"
private noncomputable def ep100101_6 : Blocks := edgeBlocks% "full/vectors/100101-E-0006.bin"
private noncomputable def ep100101_7 : Blocks := edgeBlocks% "full/vectors/100101-E-0007.bin"
private noncomputable def ep100101_8 : Blocks := edgeBlocks% "full/vectors/100101-E-0008.bin"
private noncomputable def ep100101_9 : Blocks := edgeBlocks% "full/vectors/100101-E-0009.bin"
private noncomputable def ep100101_10 : Blocks := edgeBlocks% "full/vectors/100101-E-0010.bin"
private noncomputable def ep100101_11 : Blocks := edgeBlocks% "full/vectors/100101-E-0011.bin"
private noncomputable def ep100101_12 : Blocks := edgeBlocks% "full/vectors/100101-E-0012.bin"
private noncomputable def ep100101_13 : Blocks := edgeBlocks% "full/vectors/100101-E-0013.bin"
private noncomputable def ep100101_14 : Blocks := edgeBlocks% "full/vectors/100101-E-0014.bin"
private noncomputable def ep100101_15 : Blocks := edgeBlocks% "full/vectors/100101-E-0015.bin"
private noncomputable def ep100101_16 : Blocks := edgeBlocks% "full/vectors/100101-E-0016.bin"
private noncomputable def ep100101_17 : Blocks := edgeBlocks% "full/vectors/100101-E-0017.bin"
private noncomputable def ep100101_18 : Blocks := edgeBlocks% "full/vectors/100101-E-0018.bin"
private noncomputable def ep100101_19 : Blocks := edgeBlocks% "full/vectors/100101-E-0019.bin"
private noncomputable def ep100101_20 : Blocks := edgeBlocks% "full/vectors/100101-E-0020.bin"
private noncomputable def ep100101_21 : Blocks := edgeBlocks% "full/vectors/100101-E-0021.bin"
private noncomputable def ep100101_22 : Blocks := edgeBlocks% "full/vectors/100101-E-0022.bin"
private noncomputable def ep100101_23 : Blocks := edgeBlocks% "full/vectors/100101-E-0023.bin"
private noncomputable def ep100101_24 : Blocks := edgeBlocks% "full/vectors/100101-E-0024.bin"
private noncomputable def ep100101_25 : Blocks := edgeBlocks% "full/vectors/100101-E-0025.bin"
private noncomputable def ep100101_26 : Blocks := edgeBlocks% "full/vectors/100101-E-0026.bin"
private noncomputable def ep100101_27 : Blocks := edgeBlocks% "full/vectors/100101-E-0027.bin"
noncomputable def ep100101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep100101_0 (Blocks.join ep100101_1 ep100101_2)) (Blocks.join (Blocks.join ep100101_3 ep100101_4) (Blocks.join ep100101_5 ep100101_6))) (Blocks.join (Blocks.join ep100101_7 (Blocks.join ep100101_8 ep100101_9)) (Blocks.join (Blocks.join ep100101_10 ep100101_11) (Blocks.join ep100101_12 ep100101_13)))) (Blocks.join (Blocks.join (Blocks.join ep100101_14 (Blocks.join ep100101_15 ep100101_16)) (Blocks.join (Blocks.join ep100101_17 ep100101_18) (Blocks.join ep100101_19 ep100101_20))) (Blocks.join (Blocks.join ep100101_21 (Blocks.join ep100101_22 ep100101_23)) (Blocks.join (Blocks.join ep100101_24 ep100101_25) (Blocks.join ep100101_26 ep100101_27)))))
private def ptsp100101 : List ℤ := [((2:ℤ)^3404+0),((2:ℤ)^3404+1)]
private theorem boundp100101 : 2^vp10010.size*absSum vp10010.list + ((2:ℤ)^4263*absSum vp100101.list+absSum ep100101.list) < (2:ℤ)^5555 := by decide +kernel
private theorem pointp100101_0 : fastHom 1 ((2:ℤ)^3404+0) vp10010 = ((2:ℤ)^4263)*vp100101.subst ((2:ℤ)^3404+0)+ep100101.subst ((2:ℤ)^3404+0) := by decide +kernel
private theorem pointp100101_1 : fastHom 1 ((2:ℤ)^3404+1) vp10010 = ((2:ℤ)^4263)*vp100101.subst ((2:ℤ)^3404+1)+ep100101.subst ((2:ℤ)^3404+1) := by decide +kernel
private theorem checkp100101 (x:ℤ) (hx:x ∈ ptsp100101) : fastHom 1 x vp10010 = ((2:ℤ)^4263)*vp100101.subst x+ep100101.subst x := by
  simp only [ptsp100101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp100101_0
  · exact pointp100101_1
private theorem idp100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10010.list =
    C ((2:ℤ)^4263) * horner X vp100101.list + horner X ep100101.list := by
  apply edge_identity (B := (2:ℤ)^5555) (by decide) (by positivity) (by positivity) boundp100101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp100101 (by decide +kernel)
  · have h : ptsp100101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp100101.trans_le (by decide +kernel)
  · exact checkp100101
private theorem bp100101 : Branch 1 (-4607761639/256000000 : ℚ) vp10010 := by
  apply branch_checked idp100101 (by positivity) (by decide +kernel)
  rw [show 2*(-4607761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-4735761639/128000000 : ℚ) by norm_num]
  exact coverp100101
theorem coverp10010 : Covers (-4607761639/256000000 : ℚ) vp10010 := join_branches bp100100 bp100101
private noncomputable def vp1001_0 : Blocks := edgeBlocks% "full/vectors/1001-V-0000.bin"
private noncomputable def vp1001_1 : Blocks := edgeBlocks% "full/vectors/1001-V-0001.bin"
private noncomputable def vp1001_2 : Blocks := edgeBlocks% "full/vectors/1001-V-0002.bin"
private noncomputable def vp1001_3 : Blocks := edgeBlocks% "full/vectors/1001-V-0003.bin"
private noncomputable def vp1001_4 : Blocks := edgeBlocks% "full/vectors/1001-V-0004.bin"
private noncomputable def vp1001_5 : Blocks := edgeBlocks% "full/vectors/1001-V-0005.bin"
private noncomputable def vp1001_6 : Blocks := edgeBlocks% "full/vectors/1001-V-0006.bin"
private noncomputable def vp1001_7 : Blocks := edgeBlocks% "full/vectors/1001-V-0007.bin"
private noncomputable def vp1001_8 : Blocks := edgeBlocks% "full/vectors/1001-V-0008.bin"
private noncomputable def vp1001_9 : Blocks := edgeBlocks% "full/vectors/1001-V-0009.bin"
private noncomputable def vp1001_10 : Blocks := edgeBlocks% "full/vectors/1001-V-0010.bin"
private noncomputable def vp1001_11 : Blocks := edgeBlocks% "full/vectors/1001-V-0011.bin"
private noncomputable def vp1001_12 : Blocks := edgeBlocks% "full/vectors/1001-V-0012.bin"
private noncomputable def vp1001_13 : Blocks := edgeBlocks% "full/vectors/1001-V-0013.bin"
private noncomputable def vp1001_14 : Blocks := edgeBlocks% "full/vectors/1001-V-0014.bin"
private noncomputable def vp1001_15 : Blocks := edgeBlocks% "full/vectors/1001-V-0015.bin"
private noncomputable def vp1001_16 : Blocks := edgeBlocks% "full/vectors/1001-V-0016.bin"
private noncomputable def vp1001_17 : Blocks := edgeBlocks% "full/vectors/1001-V-0017.bin"
private noncomputable def vp1001_18 : Blocks := edgeBlocks% "full/vectors/1001-V-0018.bin"
private noncomputable def vp1001_19 : Blocks := edgeBlocks% "full/vectors/1001-V-0019.bin"
private noncomputable def vp1001_20 : Blocks := edgeBlocks% "full/vectors/1001-V-0020.bin"
private noncomputable def vp1001_21 : Blocks := edgeBlocks% "full/vectors/1001-V-0021.bin"
private noncomputable def vp1001_22 : Blocks := edgeBlocks% "full/vectors/1001-V-0022.bin"
private noncomputable def vp1001_23 : Blocks := edgeBlocks% "full/vectors/1001-V-0023.bin"
private noncomputable def vp1001_24 : Blocks := edgeBlocks% "full/vectors/1001-V-0024.bin"
private noncomputable def vp1001_25 : Blocks := edgeBlocks% "full/vectors/1001-V-0025.bin"
private noncomputable def vp1001_26 : Blocks := edgeBlocks% "full/vectors/1001-V-0026.bin"
private noncomputable def vp1001_27 : Blocks := edgeBlocks% "full/vectors/1001-V-0027.bin"
private noncomputable def vp1001_28 : Blocks := edgeBlocks% "full/vectors/1001-V-0028.bin"
private noncomputable def vp1001_29 : Blocks := edgeBlocks% "full/vectors/1001-V-0029.bin"
private noncomputable def vp1001_30 : Blocks := edgeBlocks% "full/vectors/1001-V-0030.bin"
private noncomputable def vp1001_31 : Blocks := edgeBlocks% "full/vectors/1001-V-0031.bin"
private noncomputable def vp1001_32 : Blocks := edgeBlocks% "full/vectors/1001-V-0032.bin"
private noncomputable def vp1001_33 : Blocks := edgeBlocks% "full/vectors/1001-V-0033.bin"
private noncomputable def vp1001_34 : Blocks := edgeBlocks% "full/vectors/1001-V-0034.bin"
private noncomputable def vp1001_35 : Blocks := edgeBlocks% "full/vectors/1001-V-0035.bin"
private noncomputable def vp1001_36 : Blocks := edgeBlocks% "full/vectors/1001-V-0036.bin"
private noncomputable def vp1001_37 : Blocks := edgeBlocks% "full/vectors/1001-V-0037.bin"
private noncomputable def vp1001_38 : Blocks := edgeBlocks% "full/vectors/1001-V-0038.bin"
private noncomputable def vp1001_39 : Blocks := edgeBlocks% "full/vectors/1001-V-0039.bin"
private noncomputable def vp1001_40 : Blocks := edgeBlocks% "full/vectors/1001-V-0040.bin"
private noncomputable def vp1001_41 : Blocks := edgeBlocks% "full/vectors/1001-V-0041.bin"
private noncomputable def vp1001_42 : Blocks := edgeBlocks% "full/vectors/1001-V-0042.bin"
private noncomputable def vp1001_43 : Blocks := edgeBlocks% "full/vectors/1001-V-0043.bin"
private noncomputable def vp1001_44 : Blocks := edgeBlocks% "full/vectors/1001-V-0044.bin"
private noncomputable def vp1001_45 : Blocks := edgeBlocks% "full/vectors/1001-V-0045.bin"
private noncomputable def vp1001_46 : Blocks := edgeBlocks% "full/vectors/1001-V-0046.bin"
private noncomputable def vp1001_47 : Blocks := edgeBlocks% "full/vectors/1001-V-0047.bin"
private noncomputable def vp1001_48 : Blocks := edgeBlocks% "full/vectors/1001-V-0048.bin"
private noncomputable def vp1001_49 : Blocks := edgeBlocks% "full/vectors/1001-V-0049.bin"
private noncomputable def vp1001_50 : Blocks := edgeBlocks% "full/vectors/1001-V-0050.bin"
private noncomputable def vp1001_51 : Blocks := edgeBlocks% "full/vectors/1001-V-0051.bin"
noncomputable def vp1001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1001_0 (Blocks.join vp1001_1 vp1001_2)) (Blocks.join vp1001_3 (Blocks.join vp1001_4 vp1001_5))) (Blocks.join (Blocks.join vp1001_6 (Blocks.join vp1001_7 vp1001_8)) (Blocks.join (Blocks.join vp1001_9 vp1001_10) (Blocks.join vp1001_11 vp1001_12)))) (Blocks.join (Blocks.join (Blocks.join vp1001_13 (Blocks.join vp1001_14 vp1001_15)) (Blocks.join vp1001_16 (Blocks.join vp1001_17 vp1001_18))) (Blocks.join (Blocks.join vp1001_19 (Blocks.join vp1001_20 vp1001_21)) (Blocks.join (Blocks.join vp1001_22 vp1001_23) (Blocks.join vp1001_24 vp1001_25))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1001_26 (Blocks.join vp1001_27 vp1001_28)) (Blocks.join vp1001_29 (Blocks.join vp1001_30 vp1001_31))) (Blocks.join (Blocks.join vp1001_32 (Blocks.join vp1001_33 vp1001_34)) (Blocks.join (Blocks.join vp1001_35 vp1001_36) (Blocks.join vp1001_37 vp1001_38)))) (Blocks.join (Blocks.join (Blocks.join vp1001_39 (Blocks.join vp1001_40 vp1001_41)) (Blocks.join vp1001_42 (Blocks.join vp1001_43 vp1001_44))) (Blocks.join (Blocks.join vp1001_45 (Blocks.join vp1001_46 vp1001_47)) (Blocks.join (Blocks.join vp1001_48 vp1001_49) (Blocks.join vp1001_50 vp1001_51))))))
private theorem bp10010 : Branch 0 (-4607761639/512000000 : ℚ) vp1001 := by
  apply branch_left_normalized (c:=vp10010) (k:=0) (m:=3524) (by decide +kernel)
  rw [show 2*(-4607761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-4607761639/256000000 : ℚ) by norm_num]
  exact coverp10010
private noncomputable def ep10011_0 : Blocks := edgeBlocks% "full/vectors/10011-E-0000.bin"
private noncomputable def ep10011_1 : Blocks := edgeBlocks% "full/vectors/10011-E-0001.bin"
private noncomputable def ep10011_2 : Blocks := edgeBlocks% "full/vectors/10011-E-0002.bin"
private noncomputable def ep10011_3 : Blocks := edgeBlocks% "full/vectors/10011-E-0003.bin"
private noncomputable def ep10011_4 : Blocks := edgeBlocks% "full/vectors/10011-E-0004.bin"
private noncomputable def ep10011_5 : Blocks := edgeBlocks% "full/vectors/10011-E-0005.bin"
private noncomputable def ep10011_6 : Blocks := edgeBlocks% "full/vectors/10011-E-0006.bin"
private noncomputable def ep10011_7 : Blocks := edgeBlocks% "full/vectors/10011-E-0007.bin"
private noncomputable def ep10011_8 : Blocks := edgeBlocks% "full/vectors/10011-E-0008.bin"
private noncomputable def ep10011_9 : Blocks := edgeBlocks% "full/vectors/10011-E-0009.bin"
private noncomputable def ep10011_10 : Blocks := edgeBlocks% "full/vectors/10011-E-0010.bin"
private noncomputable def ep10011_11 : Blocks := edgeBlocks% "full/vectors/10011-E-0011.bin"
private noncomputable def ep10011_12 : Blocks := edgeBlocks% "full/vectors/10011-E-0012.bin"
private noncomputable def ep10011_13 : Blocks := edgeBlocks% "full/vectors/10011-E-0013.bin"
private noncomputable def ep10011_14 : Blocks := edgeBlocks% "full/vectors/10011-E-0014.bin"
private noncomputable def ep10011_15 : Blocks := edgeBlocks% "full/vectors/10011-E-0015.bin"
private noncomputable def ep10011_16 : Blocks := edgeBlocks% "full/vectors/10011-E-0016.bin"
private noncomputable def ep10011_17 : Blocks := edgeBlocks% "full/vectors/10011-E-0017.bin"
private noncomputable def ep10011_18 : Blocks := edgeBlocks% "full/vectors/10011-E-0018.bin"
private noncomputable def ep10011_19 : Blocks := edgeBlocks% "full/vectors/10011-E-0019.bin"
private noncomputable def ep10011_20 : Blocks := edgeBlocks% "full/vectors/10011-E-0020.bin"
private noncomputable def ep10011_21 : Blocks := edgeBlocks% "full/vectors/10011-E-0021.bin"
private noncomputable def ep10011_22 : Blocks := edgeBlocks% "full/vectors/10011-E-0022.bin"
private noncomputable def ep10011_23 : Blocks := edgeBlocks% "full/vectors/10011-E-0023.bin"
private noncomputable def ep10011_24 : Blocks := edgeBlocks% "full/vectors/10011-E-0024.bin"
private noncomputable def ep10011_25 : Blocks := edgeBlocks% "full/vectors/10011-E-0025.bin"
private noncomputable def ep10011_26 : Blocks := edgeBlocks% "full/vectors/10011-E-0026.bin"
private noncomputable def ep10011_27 : Blocks := edgeBlocks% "full/vectors/10011-E-0027.bin"
private noncomputable def ep10011_28 : Blocks := edgeBlocks% "full/vectors/10011-E-0028.bin"
private noncomputable def ep10011_29 : Blocks := edgeBlocks% "full/vectors/10011-E-0029.bin"
private noncomputable def ep10011_30 : Blocks := edgeBlocks% "full/vectors/10011-E-0030.bin"
private noncomputable def ep10011_31 : Blocks := edgeBlocks% "full/vectors/10011-E-0031.bin"
private noncomputable def ep10011_32 : Blocks := edgeBlocks% "full/vectors/10011-E-0032.bin"
private noncomputable def ep10011_33 : Blocks := edgeBlocks% "full/vectors/10011-E-0033.bin"
private noncomputable def ep10011_34 : Blocks := edgeBlocks% "full/vectors/10011-E-0034.bin"
private noncomputable def ep10011_35 : Blocks := edgeBlocks% "full/vectors/10011-E-0035.bin"
private noncomputable def ep10011_36 : Blocks := edgeBlocks% "full/vectors/10011-E-0036.bin"
private noncomputable def ep10011_37 : Blocks := edgeBlocks% "full/vectors/10011-E-0037.bin"
private noncomputable def ep10011_38 : Blocks := edgeBlocks% "full/vectors/10011-E-0038.bin"
private noncomputable def ep10011_39 : Blocks := edgeBlocks% "full/vectors/10011-E-0039.bin"
private noncomputable def ep10011_40 : Blocks := edgeBlocks% "full/vectors/10011-E-0040.bin"
private noncomputable def ep10011_41 : Blocks := edgeBlocks% "full/vectors/10011-E-0041.bin"
private noncomputable def ep10011_42 : Blocks := edgeBlocks% "full/vectors/10011-E-0042.bin"
private noncomputable def ep10011_43 : Blocks := edgeBlocks% "full/vectors/10011-E-0043.bin"
private noncomputable def ep10011_44 : Blocks := edgeBlocks% "full/vectors/10011-E-0044.bin"
private noncomputable def ep10011_45 : Blocks := edgeBlocks% "full/vectors/10011-E-0045.bin"
private noncomputable def ep10011_46 : Blocks := edgeBlocks% "full/vectors/10011-E-0046.bin"
private noncomputable def ep10011_47 : Blocks := edgeBlocks% "full/vectors/10011-E-0047.bin"
private noncomputable def ep10011_48 : Blocks := edgeBlocks% "full/vectors/10011-E-0048.bin"
private noncomputable def ep10011_49 : Blocks := edgeBlocks% "full/vectors/10011-E-0049.bin"
private noncomputable def ep10011_50 : Blocks := edgeBlocks% "full/vectors/10011-E-0050.bin"
private noncomputable def ep10011_51 : Blocks := edgeBlocks% "full/vectors/10011-E-0051.bin"
noncomputable def ep10011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep10011_0 (Blocks.join ep10011_1 ep10011_2)) (Blocks.join ep10011_3 (Blocks.join ep10011_4 ep10011_5))) (Blocks.join (Blocks.join ep10011_6 (Blocks.join ep10011_7 ep10011_8)) (Blocks.join (Blocks.join ep10011_9 ep10011_10) (Blocks.join ep10011_11 ep10011_12)))) (Blocks.join (Blocks.join (Blocks.join ep10011_13 (Blocks.join ep10011_14 ep10011_15)) (Blocks.join ep10011_16 (Blocks.join ep10011_17 ep10011_18))) (Blocks.join (Blocks.join ep10011_19 (Blocks.join ep10011_20 ep10011_21)) (Blocks.join (Blocks.join ep10011_22 ep10011_23) (Blocks.join ep10011_24 ep10011_25))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep10011_26 (Blocks.join ep10011_27 ep10011_28)) (Blocks.join ep10011_29 (Blocks.join ep10011_30 ep10011_31))) (Blocks.join (Blocks.join ep10011_32 (Blocks.join ep10011_33 ep10011_34)) (Blocks.join (Blocks.join ep10011_35 ep10011_36) (Blocks.join ep10011_37 ep10011_38)))) (Blocks.join (Blocks.join (Blocks.join ep10011_39 (Blocks.join ep10011_40 ep10011_41)) (Blocks.join ep10011_42 (Blocks.join ep10011_43 ep10011_44))) (Blocks.join (Blocks.join ep10011_45 (Blocks.join ep10011_46 ep10011_47)) (Blocks.join (Blocks.join ep10011_48 ep10011_49) (Blocks.join ep10011_50 ep10011_51))))))
private def ptsp10011 : List ℤ := [((2:ℤ)^1813+0),((2:ℤ)^1813+1),((2:ℤ)^1813+2),((2:ℤ)^1813+3),((2:ℤ)^1813+4),((2:ℤ)^1813+5)]
private theorem boundp10011 : 2^vp1001.size*absSum vp1001.list + ((2:ℤ)^8095*absSum vp10011.list+absSum ep10011.list) < (2:ℤ)^10499 := by decide +kernel
private theorem pointp10011_0 : fastHom 1 ((2:ℤ)^1813+0) vp1001 = ((2:ℤ)^8095)*vp10011.subst ((2:ℤ)^1813+0)+ep10011.subst ((2:ℤ)^1813+0) := by decide +kernel
private theorem pointp10011_1 : fastHom 1 ((2:ℤ)^1813+1) vp1001 = ((2:ℤ)^8095)*vp10011.subst ((2:ℤ)^1813+1)+ep10011.subst ((2:ℤ)^1813+1) := by decide +kernel
private theorem pointp10011_2 : fastHom 1 ((2:ℤ)^1813+2) vp1001 = ((2:ℤ)^8095)*vp10011.subst ((2:ℤ)^1813+2)+ep10011.subst ((2:ℤ)^1813+2) := by decide +kernel
private theorem pointp10011_3 : fastHom 1 ((2:ℤ)^1813+3) vp1001 = ((2:ℤ)^8095)*vp10011.subst ((2:ℤ)^1813+3)+ep10011.subst ((2:ℤ)^1813+3) := by decide +kernel
private theorem pointp10011_4 : fastHom 1 ((2:ℤ)^1813+4) vp1001 = ((2:ℤ)^8095)*vp10011.subst ((2:ℤ)^1813+4)+ep10011.subst ((2:ℤ)^1813+4) := by decide +kernel
private theorem pointp10011_5 : fastHom 1 ((2:ℤ)^1813+5) vp1001 = ((2:ℤ)^8095)*vp10011.subst ((2:ℤ)^1813+5)+ep10011.subst ((2:ℤ)^1813+5) := by decide +kernel
private theorem checkp10011 (x:ℤ) (hx:x ∈ ptsp10011) : fastHom 1 x vp1001 = ((2:ℤ)^8095)*vp10011.subst x+ep10011.subst x := by
  simp only [ptsp10011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp10011_0
  · exact pointp10011_1
  · exact pointp10011_2
  · exact pointp10011_3
  · exact pointp10011_4
  · exact pointp10011_5
private theorem idp10011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1001.list =
    C ((2:ℤ)^8095) * horner X vp10011.list + horner X ep10011.list := by
  apply edge_identity (B := (2:ℤ)^10499) (by decide) (by positivity) (by positivity) boundp10011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp10011 (by decide +kernel)
  · have h : ptsp10011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp10011.trans_le (by decide +kernel)
  · exact checkp10011
private theorem bp10011 : Branch 1 (-4607761639/512000000 : ℚ) vp1001 := by
  apply branch_checked idp10011 (by positivity) (by decide +kernel)
  rw [show 2*(-4607761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-4863761639/256000000 : ℚ) by norm_num]
  exact coverp10011
theorem coverp1001 : Covers (-4607761639/512000000 : ℚ) vp1001 := join_branches bp10010 bp10011
end NextProof.EdgeFull

