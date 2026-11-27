import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp1011111111_0 : Blocks := edgeBlocks% "full/vectors/1011111111-V-0000.bin"
noncomputable def vp1011111111 : Blocks := vp1011111111_0
theorem coverp1011111111 : Covers (-6135761639/8000000 : ℚ) vp1011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp1011111110_0 : Blocks := edgeBlocks% "full/vectors/1011111110-V-0000.bin"
noncomputable def vp1011111110 : Blocks := vp1011111110_0
theorem coverp1011111110 : Covers (-6127761639/8000000 : ℚ) vp1011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp101111111_0 : Blocks := edgeBlocks% "full/vectors/101111111-V-0000.bin"
private noncomputable def vp101111111_1 : Blocks := edgeBlocks% "full/vectors/101111111-V-0001.bin"
noncomputable def vp101111111 : Blocks := (Blocks.join vp101111111_0 vp101111111_1)
private theorem bp1011111110 : Branch 0 (-6127761639/16000000 : ℚ) vp101111111 := by
  apply branch_left_normalized (c:=vp1011111110) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-6127761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6127761639/8000000 : ℚ) by norm_num]
  exact coverp1011111110
private noncomputable def ep1011111111_0 : Blocks := edgeBlocks% "full/vectors/1011111111-E-0000.bin"
private noncomputable def ep1011111111_1 : Blocks := edgeBlocks% "full/vectors/1011111111-E-0001.bin"
noncomputable def ep1011111111 : Blocks := (Blocks.join ep1011111111_0 ep1011111111_1)
private theorem idp1011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101111111.list =
    C ((2:ℤ)^270) * horner X vp1011111111.list + horner X ep1011111111.list := by
  exact edge_identity (B := (2:ℤ)^433) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011111111 : Branch 1 (-6127761639/16000000 : ℚ) vp101111111 := by
  apply branch_checked idp1011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-6127761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6135761639/8000000 : ℚ) by norm_num]
  exact coverp1011111111
theorem coverp101111111 : Covers (-6127761639/16000000 : ℚ) vp101111111 := join_branches bp1011111110 bp1011111111
private noncomputable def vp1011111101_0 : Blocks := edgeBlocks% "full/vectors/1011111101-V-0000.bin"
noncomputable def vp1011111101 : Blocks := vp1011111101_0
theorem coverp1011111101 : Covers (-6119761639/8000000 : ℚ) vp1011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp1011111100_0 : Blocks := edgeBlocks% "full/vectors/1011111100-V-0000.bin"
noncomputable def vp1011111100 : Blocks := vp1011111100_0
theorem coverp1011111100 : Covers (-6111761639/8000000 : ℚ) vp1011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp101111110_0 : Blocks := edgeBlocks% "full/vectors/101111110-V-0000.bin"
private noncomputable def vp101111110_1 : Blocks := edgeBlocks% "full/vectors/101111110-V-0001.bin"
noncomputable def vp101111110 : Blocks := (Blocks.join vp101111110_0 vp101111110_1)
private theorem bp1011111100 : Branch 0 (-6111761639/16000000 : ℚ) vp101111110 := by
  apply branch_left_normalized (c:=vp1011111100) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-6111761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6111761639/8000000 : ℚ) by norm_num]
  exact coverp1011111100
private noncomputable def ep1011111101_0 : Blocks := edgeBlocks% "full/vectors/1011111101-E-0000.bin"
private noncomputable def ep1011111101_1 : Blocks := edgeBlocks% "full/vectors/1011111101-E-0001.bin"
noncomputable def ep1011111101 : Blocks := (Blocks.join ep1011111101_0 ep1011111101_1)
private theorem idp1011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101111110.list =
    C ((2:ℤ)^270) * horner X vp1011111101.list + horner X ep1011111101.list := by
  exact edge_identity (B := (2:ℤ)^432) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011111101 : Branch 1 (-6111761639/16000000 : ℚ) vp101111110 := by
  apply branch_checked idp1011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-6111761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6119761639/8000000 : ℚ) by norm_num]
  exact coverp1011111101
theorem coverp101111110 : Covers (-6111761639/16000000 : ℚ) vp101111110 := join_branches bp1011111100 bp1011111101
private noncomputable def vp10111111_0 : Blocks := edgeBlocks% "full/vectors/10111111-V-0000.bin"
private noncomputable def vp10111111_1 : Blocks := edgeBlocks% "full/vectors/10111111-V-0001.bin"
private noncomputable def vp10111111_2 : Blocks := edgeBlocks% "full/vectors/10111111-V-0002.bin"
private noncomputable def vp10111111_3 : Blocks := edgeBlocks% "full/vectors/10111111-V-0003.bin"
noncomputable def vp10111111 : Blocks := (Blocks.join (Blocks.join vp10111111_0 vp10111111_1) (Blocks.join vp10111111_2 vp10111111_3))
private theorem bp101111110 : Branch 0 (-6111761639/32000000 : ℚ) vp10111111 := by
  apply branch_left_normalized (c:=vp101111110) (k:=0) (m:=223) (by decide +kernel)
  rw [show 2*(-6111761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6111761639/16000000 : ℚ) by norm_num]
  exact coverp101111110
private noncomputable def ep101111111_0 : Blocks := edgeBlocks% "full/vectors/101111111-E-0000.bin"
private noncomputable def ep101111111_1 : Blocks := edgeBlocks% "full/vectors/101111111-E-0001.bin"
private noncomputable def ep101111111_2 : Blocks := edgeBlocks% "full/vectors/101111111-E-0002.bin"
private noncomputable def ep101111111_3 : Blocks := edgeBlocks% "full/vectors/101111111-E-0003.bin"
noncomputable def ep101111111 : Blocks := (Blocks.join (Blocks.join ep101111111_0 ep101111111_1) (Blocks.join ep101111111_2 ep101111111_3))
private theorem idp101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10111111.list =
    C ((2:ℤ)^515) * horner X vp101111111.list + horner X ep101111111.list := by
  exact edge_identity (B := (2:ℤ)^738) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101111111 : Branch 1 (-6111761639/32000000 : ℚ) vp10111111 := by
  apply branch_checked idp101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-6111761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6127761639/16000000 : ℚ) by norm_num]
  exact coverp101111111
theorem coverp10111111 : Covers (-6111761639/32000000 : ℚ) vp10111111 := join_branches bp101111110 bp101111111
private noncomputable def vp1011111011_0 : Blocks := edgeBlocks% "full/vectors/1011111011-V-0000.bin"
noncomputable def vp1011111011 : Blocks := vp1011111011_0
theorem coverp1011111011 : Covers (-6103761639/8000000 : ℚ) vp1011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp1011111010_0 : Blocks := edgeBlocks% "full/vectors/1011111010-V-0000.bin"
noncomputable def vp1011111010 : Blocks := vp1011111010_0
theorem coverp1011111010 : Covers (-6095761639/8000000 : ℚ) vp1011111010 := cover_leaf (by decide +kernel)
private noncomputable def vp101111101_0 : Blocks := edgeBlocks% "full/vectors/101111101-V-0000.bin"
private noncomputable def vp101111101_1 : Blocks := edgeBlocks% "full/vectors/101111101-V-0001.bin"
noncomputable def vp101111101 : Blocks := (Blocks.join vp101111101_0 vp101111101_1)
private theorem bp1011111010 : Branch 0 (-6095761639/16000000 : ℚ) vp101111101 := by
  apply branch_left_normalized (c:=vp1011111010) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-6095761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6095761639/8000000 : ℚ) by norm_num]
  exact coverp1011111010
private noncomputable def ep1011111011_0 : Blocks := edgeBlocks% "full/vectors/1011111011-E-0000.bin"
private noncomputable def ep1011111011_1 : Blocks := edgeBlocks% "full/vectors/1011111011-E-0001.bin"
noncomputable def ep1011111011 : Blocks := (Blocks.join ep1011111011_0 ep1011111011_1)
private theorem idp1011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101111101.list =
    C ((2:ℤ)^271) * horner X vp1011111011.list + horner X ep1011111011.list := by
  exact edge_identity (B := (2:ℤ)^433) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011111011 : Branch 1 (-6095761639/16000000 : ℚ) vp101111101 := by
  apply branch_checked idp1011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-6095761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6103761639/8000000 : ℚ) by norm_num]
  exact coverp1011111011
theorem coverp101111101 : Covers (-6095761639/16000000 : ℚ) vp101111101 := join_branches bp1011111010 bp1011111011
private noncomputable def vp1011111001_0 : Blocks := edgeBlocks% "full/vectors/1011111001-V-0000.bin"
noncomputable def vp1011111001 : Blocks := vp1011111001_0
theorem coverp1011111001 : Covers (-6087761639/8000000 : ℚ) vp1011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp1011111000_0 : Blocks := edgeBlocks% "full/vectors/1011111000-V-0000.bin"
noncomputable def vp1011111000 : Blocks := vp1011111000_0
theorem coverp1011111000 : Covers (-6079761639/8000000 : ℚ) vp1011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp101111100_0 : Blocks := edgeBlocks% "full/vectors/101111100-V-0000.bin"
private noncomputable def vp101111100_1 : Blocks := edgeBlocks% "full/vectors/101111100-V-0001.bin"
noncomputable def vp101111100 : Blocks := (Blocks.join vp101111100_0 vp101111100_1)
private theorem bp1011111000 : Branch 0 (-6079761639/16000000 : ℚ) vp101111100 := by
  apply branch_left_normalized (c:=vp1011111000) (k:=0) (m:=123) (by decide +kernel)
  rw [show 2*(-6079761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6079761639/8000000 : ℚ) by norm_num]
  exact coverp1011111000
private noncomputable def ep1011111001_0 : Blocks := edgeBlocks% "full/vectors/1011111001-E-0000.bin"
private noncomputable def ep1011111001_1 : Blocks := edgeBlocks% "full/vectors/1011111001-E-0001.bin"
noncomputable def ep1011111001 : Blocks := (Blocks.join ep1011111001_0 ep1011111001_1)
private theorem idp1011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101111100.list =
    C ((2:ℤ)^271) * horner X vp1011111001.list + horner X ep1011111001.list := by
  exact edge_identity (B := (2:ℤ)^434) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011111001 : Branch 1 (-6079761639/16000000 : ℚ) vp101111100 := by
  apply branch_checked idp1011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-6079761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6087761639/8000000 : ℚ) by norm_num]
  exact coverp1011111001
theorem coverp101111100 : Covers (-6079761639/16000000 : ℚ) vp101111100 := join_branches bp1011111000 bp1011111001
private noncomputable def vp10111110_0 : Blocks := edgeBlocks% "full/vectors/10111110-V-0000.bin"
private noncomputable def vp10111110_1 : Blocks := edgeBlocks% "full/vectors/10111110-V-0001.bin"
private noncomputable def vp10111110_2 : Blocks := edgeBlocks% "full/vectors/10111110-V-0002.bin"
private noncomputable def vp10111110_3 : Blocks := edgeBlocks% "full/vectors/10111110-V-0003.bin"
noncomputable def vp10111110 : Blocks := (Blocks.join (Blocks.join vp10111110_0 vp10111110_1) (Blocks.join vp10111110_2 vp10111110_3))
private theorem bp101111100 : Branch 0 (-6079761639/32000000 : ℚ) vp10111110 := by
  apply branch_left_normalized (c:=vp101111100) (k:=0) (m:=224) (by decide +kernel)
  rw [show 2*(-6079761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6079761639/16000000 : ℚ) by norm_num]
  exact coverp101111100
private noncomputable def ep101111101_0 : Blocks := edgeBlocks% "full/vectors/101111101-E-0000.bin"
private noncomputable def ep101111101_1 : Blocks := edgeBlocks% "full/vectors/101111101-E-0001.bin"
private noncomputable def ep101111101_2 : Blocks := edgeBlocks% "full/vectors/101111101-E-0002.bin"
private noncomputable def ep101111101_3 : Blocks := edgeBlocks% "full/vectors/101111101-E-0003.bin"
noncomputable def ep101111101 : Blocks := (Blocks.join (Blocks.join ep101111101_0 ep101111101_1) (Blocks.join ep101111101_2 ep101111101_3))
private theorem idp101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10111110.list =
    C ((2:ℤ)^517) * horner X vp101111101.list + horner X ep101111101.list := by
  exact edge_identity (B := (2:ℤ)^741) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101111101 : Branch 1 (-6079761639/32000000 : ℚ) vp10111110 := by
  apply branch_checked idp101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-6079761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6095761639/16000000 : ℚ) by norm_num]
  exact coverp101111101
theorem coverp10111110 : Covers (-6079761639/32000000 : ℚ) vp10111110 := join_branches bp101111100 bp101111101
private noncomputable def vp1011111_0 : Blocks := edgeBlocks% "full/vectors/1011111-V-0000.bin"
private noncomputable def vp1011111_1 : Blocks := edgeBlocks% "full/vectors/1011111-V-0001.bin"
private noncomputable def vp1011111_2 : Blocks := edgeBlocks% "full/vectors/1011111-V-0002.bin"
private noncomputable def vp1011111_3 : Blocks := edgeBlocks% "full/vectors/1011111-V-0003.bin"
private noncomputable def vp1011111_4 : Blocks := edgeBlocks% "full/vectors/1011111-V-0004.bin"
private noncomputable def vp1011111_5 : Blocks := edgeBlocks% "full/vectors/1011111-V-0005.bin"
private noncomputable def vp1011111_6 : Blocks := edgeBlocks% "full/vectors/1011111-V-0006.bin"
noncomputable def vp1011111 : Blocks := (Blocks.join (Blocks.join vp1011111_0 (Blocks.join vp1011111_1 vp1011111_2)) (Blocks.join (Blocks.join vp1011111_3 vp1011111_4) (Blocks.join vp1011111_5 vp1011111_6)))
private theorem bp10111110 : Branch 0 (-6079761639/64000000 : ℚ) vp1011111 := by
  apply branch_left_normalized (c:=vp10111110) (k:=0) (m:=424) (by decide +kernel)
  rw [show 2*(-6079761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6079761639/32000000 : ℚ) by norm_num]
  exact coverp10111110
private noncomputable def ep10111111_0 : Blocks := edgeBlocks% "full/vectors/10111111-E-0000.bin"
private noncomputable def ep10111111_1 : Blocks := edgeBlocks% "full/vectors/10111111-E-0001.bin"
private noncomputable def ep10111111_2 : Blocks := edgeBlocks% "full/vectors/10111111-E-0002.bin"
private noncomputable def ep10111111_3 : Blocks := edgeBlocks% "full/vectors/10111111-E-0003.bin"
private noncomputable def ep10111111_4 : Blocks := edgeBlocks% "full/vectors/10111111-E-0004.bin"
private noncomputable def ep10111111_5 : Blocks := edgeBlocks% "full/vectors/10111111-E-0005.bin"
private noncomputable def ep10111111_6 : Blocks := edgeBlocks% "full/vectors/10111111-E-0006.bin"
noncomputable def ep10111111 : Blocks := (Blocks.join (Blocks.join ep10111111_0 (Blocks.join ep10111111_1 ep10111111_2)) (Blocks.join (Blocks.join ep10111111_3 ep10111111_4) (Blocks.join ep10111111_5 ep10111111_6)))
private theorem idp10111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1011111.list =
    C ((2:ℤ)^1006) * horner X vp10111111.list + horner X ep10111111.list := by
  exact edge_identity (B := (2:ℤ)^1350) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10111111 : Branch 1 (-6079761639/64000000 : ℚ) vp1011111 := by
  apply branch_checked idp10111111 (by positivity) (by decide +kernel)
  rw [show 2*(-6079761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6111761639/32000000 : ℚ) by norm_num]
  exact coverp10111111
theorem coverp1011111 : Covers (-6079761639/64000000 : ℚ) vp1011111 := join_branches bp10111110 bp10111111
private noncomputable def vp1011110111_0 : Blocks := edgeBlocks% "full/vectors/1011110111-V-0000.bin"
noncomputable def vp1011110111 : Blocks := vp1011110111_0
theorem coverp1011110111 : Covers (-6071761639/8000000 : ℚ) vp1011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp1011110110_0 : Blocks := edgeBlocks% "full/vectors/1011110110-V-0000.bin"
noncomputable def vp1011110110 : Blocks := vp1011110110_0
theorem coverp1011110110 : Covers (-6063761639/8000000 : ℚ) vp1011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp101111011_0 : Blocks := edgeBlocks% "full/vectors/101111011-V-0000.bin"
private noncomputable def vp101111011_1 : Blocks := edgeBlocks% "full/vectors/101111011-V-0001.bin"
noncomputable def vp101111011 : Blocks := (Blocks.join vp101111011_0 vp101111011_1)
private theorem bp1011110110 : Branch 0 (-6063761639/16000000 : ℚ) vp101111011 := by
  apply branch_left_normalized (c:=vp1011110110) (k:=0) (m:=123) (by decide +kernel)
  rw [show 2*(-6063761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6063761639/8000000 : ℚ) by norm_num]
  exact coverp1011110110
private noncomputable def ep1011110111_0 : Blocks := edgeBlocks% "full/vectors/1011110111-E-0000.bin"
private noncomputable def ep1011110111_1 : Blocks := edgeBlocks% "full/vectors/1011110111-E-0001.bin"
noncomputable def ep1011110111 : Blocks := (Blocks.join ep1011110111_0 ep1011110111_1)
private theorem idp1011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101111011.list =
    C ((2:ℤ)^271) * horner X vp1011110111.list + horner X ep1011110111.list := by
  exact edge_identity (B := (2:ℤ)^434) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011110111 : Branch 1 (-6063761639/16000000 : ℚ) vp101111011 := by
  apply branch_checked idp1011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-6063761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6071761639/8000000 : ℚ) by norm_num]
  exact coverp1011110111
theorem coverp101111011 : Covers (-6063761639/16000000 : ℚ) vp101111011 := join_branches bp1011110110 bp1011110111
private noncomputable def vp1011110101_0 : Blocks := edgeBlocks% "full/vectors/1011110101-V-0000.bin"
noncomputable def vp1011110101 : Blocks := vp1011110101_0
theorem coverp1011110101 : Covers (-6055761639/8000000 : ℚ) vp1011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp1011110100_0 : Blocks := edgeBlocks% "full/vectors/1011110100-V-0000.bin"
noncomputable def vp1011110100 : Blocks := vp1011110100_0
theorem coverp1011110100 : Covers (-6047761639/8000000 : ℚ) vp1011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp101111010_0 : Blocks := edgeBlocks% "full/vectors/101111010-V-0000.bin"
private noncomputable def vp101111010_1 : Blocks := edgeBlocks% "full/vectors/101111010-V-0001.bin"
noncomputable def vp101111010 : Blocks := (Blocks.join vp101111010_0 vp101111010_1)
private theorem bp1011110100 : Branch 0 (-6047761639/16000000 : ℚ) vp101111010 := by
  apply branch_left_normalized (c:=vp1011110100) (k:=0) (m:=123) (by decide +kernel)
  rw [show 2*(-6047761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6047761639/8000000 : ℚ) by norm_num]
  exact coverp1011110100
private noncomputable def ep1011110101_0 : Blocks := edgeBlocks% "full/vectors/1011110101-E-0000.bin"
private noncomputable def ep1011110101_1 : Blocks := edgeBlocks% "full/vectors/1011110101-E-0001.bin"
noncomputable def ep1011110101 : Blocks := (Blocks.join ep1011110101_0 ep1011110101_1)
private theorem idp1011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101111010.list =
    C ((2:ℤ)^273) * horner X vp1011110101.list + horner X ep1011110101.list := by
  exact edge_identity (B := (2:ℤ)^435) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011110101 : Branch 1 (-6047761639/16000000 : ℚ) vp101111010 := by
  apply branch_checked idp1011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-6047761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6055761639/8000000 : ℚ) by norm_num]
  exact coverp1011110101
theorem coverp101111010 : Covers (-6047761639/16000000 : ℚ) vp101111010 := join_branches bp1011110100 bp1011110101
private noncomputable def vp10111101_0 : Blocks := edgeBlocks% "full/vectors/10111101-V-0000.bin"
private noncomputable def vp10111101_1 : Blocks := edgeBlocks% "full/vectors/10111101-V-0001.bin"
private noncomputable def vp10111101_2 : Blocks := edgeBlocks% "full/vectors/10111101-V-0002.bin"
private noncomputable def vp10111101_3 : Blocks := edgeBlocks% "full/vectors/10111101-V-0003.bin"
noncomputable def vp10111101 : Blocks := (Blocks.join (Blocks.join vp10111101_0 vp10111101_1) (Blocks.join vp10111101_2 vp10111101_3))
private theorem bp101111010 : Branch 0 (-6047761639/32000000 : ℚ) vp10111101 := by
  apply branch_left_normalized (c:=vp101111010) (k:=0) (m:=225) (by decide +kernel)
  rw [show 2*(-6047761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6047761639/16000000 : ℚ) by norm_num]
  exact coverp101111010
private noncomputable def ep101111011_0 : Blocks := edgeBlocks% "full/vectors/101111011-E-0000.bin"
private noncomputable def ep101111011_1 : Blocks := edgeBlocks% "full/vectors/101111011-E-0001.bin"
private noncomputable def ep101111011_2 : Blocks := edgeBlocks% "full/vectors/101111011-E-0002.bin"
private noncomputable def ep101111011_3 : Blocks := edgeBlocks% "full/vectors/101111011-E-0003.bin"
noncomputable def ep101111011 : Blocks := (Blocks.join (Blocks.join ep101111011_0 ep101111011_1) (Blocks.join ep101111011_2 ep101111011_3))
private theorem idp101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10111101.list =
    C ((2:ℤ)^519) * horner X vp101111011.list + horner X ep101111011.list := by
  exact edge_identity (B := (2:ℤ)^743) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101111011 : Branch 1 (-6047761639/32000000 : ℚ) vp10111101 := by
  apply branch_checked idp101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-6047761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6063761639/16000000 : ℚ) by norm_num]
  exact coverp101111011
theorem coverp10111101 : Covers (-6047761639/32000000 : ℚ) vp10111101 := join_branches bp101111010 bp101111011
private noncomputable def vp1011110011_0 : Blocks := edgeBlocks% "full/vectors/1011110011-V-0000.bin"
noncomputable def vp1011110011 : Blocks := vp1011110011_0
theorem coverp1011110011 : Covers (-6039761639/8000000 : ℚ) vp1011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp1011110010_0 : Blocks := edgeBlocks% "full/vectors/1011110010-V-0000.bin"
noncomputable def vp1011110010 : Blocks := vp1011110010_0
theorem coverp1011110010 : Covers (-6031761639/8000000 : ℚ) vp1011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp101111001_0 : Blocks := edgeBlocks% "full/vectors/101111001-V-0000.bin"
private noncomputable def vp101111001_1 : Blocks := edgeBlocks% "full/vectors/101111001-V-0001.bin"
noncomputable def vp101111001 : Blocks := (Blocks.join vp101111001_0 vp101111001_1)
private theorem bp1011110010 : Branch 0 (-6031761639/16000000 : ℚ) vp101111001 := by
  apply branch_left_normalized (c:=vp1011110010) (k:=0) (m:=123) (by decide +kernel)
  rw [show 2*(-6031761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6031761639/8000000 : ℚ) by norm_num]
  exact coverp1011110010
private noncomputable def ep1011110011_0 : Blocks := edgeBlocks% "full/vectors/1011110011-E-0000.bin"
private noncomputable def ep1011110011_1 : Blocks := edgeBlocks% "full/vectors/1011110011-E-0001.bin"
noncomputable def ep1011110011 : Blocks := (Blocks.join ep1011110011_0 ep1011110011_1)
private theorem idp1011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101111001.list =
    C ((2:ℤ)^272) * horner X vp1011110011.list + horner X ep1011110011.list := by
  exact edge_identity (B := (2:ℤ)^435) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011110011 : Branch 1 (-6031761639/16000000 : ℚ) vp101111001 := by
  apply branch_checked idp1011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-6031761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6039761639/8000000 : ℚ) by norm_num]
  exact coverp1011110011
theorem coverp101111001 : Covers (-6031761639/16000000 : ℚ) vp101111001 := join_branches bp1011110010 bp1011110011
private noncomputable def vp1011110001_0 : Blocks := edgeBlocks% "full/vectors/1011110001-V-0000.bin"
noncomputable def vp1011110001 : Blocks := vp1011110001_0
theorem coverp1011110001 : Covers (-6023761639/8000000 : ℚ) vp1011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp1011110000_0 : Blocks := edgeBlocks% "full/vectors/1011110000-V-0000.bin"
noncomputable def vp1011110000 : Blocks := vp1011110000_0
theorem coverp1011110000 : Covers (-6015761639/8000000 : ℚ) vp1011110000 := cover_leaf (by decide +kernel)
private noncomputable def vp101111000_0 : Blocks := edgeBlocks% "full/vectors/101111000-V-0000.bin"
private noncomputable def vp101111000_1 : Blocks := edgeBlocks% "full/vectors/101111000-V-0001.bin"
noncomputable def vp101111000 : Blocks := (Blocks.join vp101111000_0 vp101111000_1)
private theorem bp1011110000 : Branch 0 (-6015761639/16000000 : ℚ) vp101111000 := by
  apply branch_left_normalized (c:=vp1011110000) (k:=0) (m:=123) (by decide +kernel)
  rw [show 2*(-6015761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6015761639/8000000 : ℚ) by norm_num]
  exact coverp1011110000
private noncomputable def ep1011110001_0 : Blocks := edgeBlocks% "full/vectors/1011110001-E-0000.bin"
private noncomputable def ep1011110001_1 : Blocks := edgeBlocks% "full/vectors/1011110001-E-0001.bin"
noncomputable def ep1011110001 : Blocks := (Blocks.join ep1011110001_0 ep1011110001_1)
private theorem idp1011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101111000.list =
    C ((2:ℤ)^272) * horner X vp1011110001.list + horner X ep1011110001.list := by
  exact edge_identity (B := (2:ℤ)^435) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011110001 : Branch 1 (-6015761639/16000000 : ℚ) vp101111000 := by
  apply branch_checked idp1011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-6015761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6023761639/8000000 : ℚ) by norm_num]
  exact coverp1011110001
theorem coverp101111000 : Covers (-6015761639/16000000 : ℚ) vp101111000 := join_branches bp1011110000 bp1011110001
private noncomputable def vp10111100_0 : Blocks := edgeBlocks% "full/vectors/10111100-V-0000.bin"
private noncomputable def vp10111100_1 : Blocks := edgeBlocks% "full/vectors/10111100-V-0001.bin"
private noncomputable def vp10111100_2 : Blocks := edgeBlocks% "full/vectors/10111100-V-0002.bin"
private noncomputable def vp10111100_3 : Blocks := edgeBlocks% "full/vectors/10111100-V-0003.bin"
noncomputable def vp10111100 : Blocks := (Blocks.join (Blocks.join vp10111100_0 vp10111100_1) (Blocks.join vp10111100_2 vp10111100_3))
private theorem bp101111000 : Branch 0 (-6015761639/32000000 : ℚ) vp10111100 := by
  apply branch_left_normalized (c:=vp101111000) (k:=0) (m:=225) (by decide +kernel)
  rw [show 2*(-6015761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6015761639/16000000 : ℚ) by norm_num]
  exact coverp101111000
private noncomputable def ep101111001_0 : Blocks := edgeBlocks% "full/vectors/101111001-E-0000.bin"
private noncomputable def ep101111001_1 : Blocks := edgeBlocks% "full/vectors/101111001-E-0001.bin"
private noncomputable def ep101111001_2 : Blocks := edgeBlocks% "full/vectors/101111001-E-0002.bin"
private noncomputable def ep101111001_3 : Blocks := edgeBlocks% "full/vectors/101111001-E-0003.bin"
noncomputable def ep101111001 : Blocks := (Blocks.join (Blocks.join ep101111001_0 ep101111001_1) (Blocks.join ep101111001_2 ep101111001_3))
private theorem idp101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10111100.list =
    C ((2:ℤ)^519) * horner X vp101111001.list + horner X ep101111001.list := by
  exact edge_identity (B := (2:ℤ)^743) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101111001 : Branch 1 (-6015761639/32000000 : ℚ) vp10111100 := by
  apply branch_checked idp101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-6015761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6031761639/16000000 : ℚ) by norm_num]
  exact coverp101111001
theorem coverp10111100 : Covers (-6015761639/32000000 : ℚ) vp10111100 := join_branches bp101111000 bp101111001
private noncomputable def vp1011110_0 : Blocks := edgeBlocks% "full/vectors/1011110-V-0000.bin"
private noncomputable def vp1011110_1 : Blocks := edgeBlocks% "full/vectors/1011110-V-0001.bin"
private noncomputable def vp1011110_2 : Blocks := edgeBlocks% "full/vectors/1011110-V-0002.bin"
private noncomputable def vp1011110_3 : Blocks := edgeBlocks% "full/vectors/1011110-V-0003.bin"
private noncomputable def vp1011110_4 : Blocks := edgeBlocks% "full/vectors/1011110-V-0004.bin"
private noncomputable def vp1011110_5 : Blocks := edgeBlocks% "full/vectors/1011110-V-0005.bin"
private noncomputable def vp1011110_6 : Blocks := edgeBlocks% "full/vectors/1011110-V-0006.bin"
noncomputable def vp1011110 : Blocks := (Blocks.join (Blocks.join vp1011110_0 (Blocks.join vp1011110_1 vp1011110_2)) (Blocks.join (Blocks.join vp1011110_3 vp1011110_4) (Blocks.join vp1011110_5 vp1011110_6)))
private theorem bp10111100 : Branch 0 (-6015761639/64000000 : ℚ) vp1011110 := by
  apply branch_left_normalized (c:=vp10111100) (k:=0) (m:=426) (by decide +kernel)
  rw [show 2*(-6015761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6015761639/32000000 : ℚ) by norm_num]
  exact coverp10111100
private noncomputable def ep10111101_0 : Blocks := edgeBlocks% "full/vectors/10111101-E-0000.bin"
private noncomputable def ep10111101_1 : Blocks := edgeBlocks% "full/vectors/10111101-E-0001.bin"
private noncomputable def ep10111101_2 : Blocks := edgeBlocks% "full/vectors/10111101-E-0002.bin"
private noncomputable def ep10111101_3 : Blocks := edgeBlocks% "full/vectors/10111101-E-0003.bin"
private noncomputable def ep10111101_4 : Blocks := edgeBlocks% "full/vectors/10111101-E-0004.bin"
private noncomputable def ep10111101_5 : Blocks := edgeBlocks% "full/vectors/10111101-E-0005.bin"
private noncomputable def ep10111101_6 : Blocks := edgeBlocks% "full/vectors/10111101-E-0006.bin"
noncomputable def ep10111101 : Blocks := (Blocks.join (Blocks.join ep10111101_0 (Blocks.join ep10111101_1 ep10111101_2)) (Blocks.join (Blocks.join ep10111101_3 ep10111101_4) (Blocks.join ep10111101_5 ep10111101_6)))
private theorem idp10111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1011110.list =
    C ((2:ℤ)^1010) * horner X vp10111101.list + horner X ep10111101.list := by
  exact edge_identity (B := (2:ℤ)^1357) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10111101 : Branch 1 (-6015761639/64000000 : ℚ) vp1011110 := by
  apply branch_checked idp10111101 (by positivity) (by decide +kernel)
  rw [show 2*(-6015761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6047761639/32000000 : ℚ) by norm_num]
  exact coverp10111101
theorem coverp1011110 : Covers (-6015761639/64000000 : ℚ) vp1011110 := join_branches bp10111100 bp10111101
private noncomputable def vp101111_0 : Blocks := edgeBlocks% "full/vectors/101111-V-0000.bin"
private noncomputable def vp101111_1 : Blocks := edgeBlocks% "full/vectors/101111-V-0001.bin"
private noncomputable def vp101111_2 : Blocks := edgeBlocks% "full/vectors/101111-V-0002.bin"
private noncomputable def vp101111_3 : Blocks := edgeBlocks% "full/vectors/101111-V-0003.bin"
private noncomputable def vp101111_4 : Blocks := edgeBlocks% "full/vectors/101111-V-0004.bin"
private noncomputable def vp101111_5 : Blocks := edgeBlocks% "full/vectors/101111-V-0005.bin"
private noncomputable def vp101111_6 : Blocks := edgeBlocks% "full/vectors/101111-V-0006.bin"
private noncomputable def vp101111_7 : Blocks := edgeBlocks% "full/vectors/101111-V-0007.bin"
private noncomputable def vp101111_8 : Blocks := edgeBlocks% "full/vectors/101111-V-0008.bin"
private noncomputable def vp101111_9 : Blocks := edgeBlocks% "full/vectors/101111-V-0009.bin"
private noncomputable def vp101111_10 : Blocks := edgeBlocks% "full/vectors/101111-V-0010.bin"
private noncomputable def vp101111_11 : Blocks := edgeBlocks% "full/vectors/101111-V-0011.bin"
private noncomputable def vp101111_12 : Blocks := edgeBlocks% "full/vectors/101111-V-0012.bin"
noncomputable def vp101111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp101111_0 (Blocks.join vp101111_1 vp101111_2)) (Blocks.join vp101111_3 (Blocks.join vp101111_4 vp101111_5))) (Blocks.join (Blocks.join vp101111_6 (Blocks.join vp101111_7 vp101111_8)) (Blocks.join (Blocks.join vp101111_9 vp101111_10) (Blocks.join vp101111_11 vp101111_12))))
private theorem bp1011110 : Branch 0 (-6015761639/128000000 : ℚ) vp101111 := by
  apply branch_left_normalized (c:=vp1011110) (k:=0) (m:=825) (by decide +kernel)
  rw [show 2*(-6015761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-6015761639/64000000 : ℚ) by norm_num]
  exact coverp1011110
private noncomputable def ep1011111_0 : Blocks := edgeBlocks% "full/vectors/1011111-E-0000.bin"
private noncomputable def ep1011111_1 : Blocks := edgeBlocks% "full/vectors/1011111-E-0001.bin"
private noncomputable def ep1011111_2 : Blocks := edgeBlocks% "full/vectors/1011111-E-0002.bin"
private noncomputable def ep1011111_3 : Blocks := edgeBlocks% "full/vectors/1011111-E-0003.bin"
private noncomputable def ep1011111_4 : Blocks := edgeBlocks% "full/vectors/1011111-E-0004.bin"
private noncomputable def ep1011111_5 : Blocks := edgeBlocks% "full/vectors/1011111-E-0005.bin"
private noncomputable def ep1011111_6 : Blocks := edgeBlocks% "full/vectors/1011111-E-0006.bin"
private noncomputable def ep1011111_7 : Blocks := edgeBlocks% "full/vectors/1011111-E-0007.bin"
private noncomputable def ep1011111_8 : Blocks := edgeBlocks% "full/vectors/1011111-E-0008.bin"
private noncomputable def ep1011111_9 : Blocks := edgeBlocks% "full/vectors/1011111-E-0009.bin"
private noncomputable def ep1011111_10 : Blocks := edgeBlocks% "full/vectors/1011111-E-0010.bin"
private noncomputable def ep1011111_11 : Blocks := edgeBlocks% "full/vectors/1011111-E-0011.bin"
private noncomputable def ep1011111_12 : Blocks := edgeBlocks% "full/vectors/1011111-E-0012.bin"
noncomputable def ep1011111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1011111_0 (Blocks.join ep1011111_1 ep1011111_2)) (Blocks.join ep1011111_3 (Blocks.join ep1011111_4 ep1011111_5))) (Blocks.join (Blocks.join ep1011111_6 (Blocks.join ep1011111_7 ep1011111_8)) (Blocks.join (Blocks.join ep1011111_9 ep1011111_10) (Blocks.join ep1011111_11 ep1011111_12))))
private theorem idp1011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101111.list =
    C ((2:ℤ)^1977) * horner X vp1011111.list + horner X ep1011111.list := by
  exact edge_identity (B := (2:ℤ)^2564) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011111 : Branch 1 (-6015761639/128000000 : ℚ) vp101111 := by
  apply branch_checked idp1011111 (by positivity) (by decide +kernel)
  rw [show 2*(-6015761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-6079761639/64000000 : ℚ) by norm_num]
  exact coverp1011111
theorem coverp101111 : Covers (-6015761639/128000000 : ℚ) vp101111 := join_branches bp1011110 bp1011111
private noncomputable def vp1011101111_0 : Blocks := edgeBlocks% "full/vectors/1011101111-V-0000.bin"
noncomputable def vp1011101111 : Blocks := vp1011101111_0
theorem coverp1011101111 : Covers (-6007761639/8000000 : ℚ) vp1011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp1011101110_0 : Blocks := edgeBlocks% "full/vectors/1011101110-V-0000.bin"
noncomputable def vp1011101110 : Blocks := vp1011101110_0
theorem coverp1011101110 : Covers (-5999761639/8000000 : ℚ) vp1011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp101110111_0 : Blocks := edgeBlocks% "full/vectors/101110111-V-0000.bin"
private noncomputable def vp101110111_1 : Blocks := edgeBlocks% "full/vectors/101110111-V-0001.bin"
noncomputable def vp101110111 : Blocks := (Blocks.join vp101110111_0 vp101110111_1)
private theorem bp1011101110 : Branch 0 (-5999761639/16000000 : ℚ) vp101110111 := by
  apply branch_left_normalized (c:=vp1011101110) (k:=0) (m:=123) (by decide +kernel)
  rw [show 2*(-5999761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5999761639/8000000 : ℚ) by norm_num]
  exact coverp1011101110
private noncomputable def ep1011101111_0 : Blocks := edgeBlocks% "full/vectors/1011101111-E-0000.bin"
private noncomputable def ep1011101111_1 : Blocks := edgeBlocks% "full/vectors/1011101111-E-0001.bin"
noncomputable def ep1011101111 : Blocks := (Blocks.join ep1011101111_0 ep1011101111_1)
private theorem idp1011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101110111.list =
    C ((2:ℤ)^273) * horner X vp1011101111.list + horner X ep1011101111.list := by
  exact edge_identity (B := (2:ℤ)^436) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011101111 : Branch 1 (-5999761639/16000000 : ℚ) vp101110111 := by
  apply branch_checked idp1011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-5999761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6007761639/8000000 : ℚ) by norm_num]
  exact coverp1011101111
theorem coverp101110111 : Covers (-5999761639/16000000 : ℚ) vp101110111 := join_branches bp1011101110 bp1011101111
private noncomputable def vp1011101101_0 : Blocks := edgeBlocks% "full/vectors/1011101101-V-0000.bin"
noncomputable def vp1011101101 : Blocks := vp1011101101_0
theorem coverp1011101101 : Covers (-5991761639/8000000 : ℚ) vp1011101101 := cover_leaf (by decide +kernel)
private noncomputable def vp1011101100_0 : Blocks := edgeBlocks% "full/vectors/1011101100-V-0000.bin"
noncomputable def vp1011101100 : Blocks := vp1011101100_0
theorem coverp1011101100 : Covers (-5983761639/8000000 : ℚ) vp1011101100 := cover_leaf (by decide +kernel)
private noncomputable def vp101110110_0 : Blocks := edgeBlocks% "full/vectors/101110110-V-0000.bin"
private noncomputable def vp101110110_1 : Blocks := edgeBlocks% "full/vectors/101110110-V-0001.bin"
noncomputable def vp101110110 : Blocks := (Blocks.join vp101110110_0 vp101110110_1)
private theorem bp1011101100 : Branch 0 (-5983761639/16000000 : ℚ) vp101110110 := by
  apply branch_left_normalized (c:=vp1011101100) (k:=0) (m:=123) (by decide +kernel)
  rw [show 2*(-5983761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5983761639/8000000 : ℚ) by norm_num]
  exact coverp1011101100
private noncomputable def ep1011101101_0 : Blocks := edgeBlocks% "full/vectors/1011101101-E-0000.bin"
private noncomputable def ep1011101101_1 : Blocks := edgeBlocks% "full/vectors/1011101101-E-0001.bin"
noncomputable def ep1011101101 : Blocks := (Blocks.join ep1011101101_0 ep1011101101_1)
private theorem idp1011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101110110.list =
    C ((2:ℤ)^273) * horner X vp1011101101.list + horner X ep1011101101.list := by
  exact edge_identity (B := (2:ℤ)^437) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011101101 : Branch 1 (-5983761639/16000000 : ℚ) vp101110110 := by
  apply branch_checked idp1011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-5983761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5991761639/8000000 : ℚ) by norm_num]
  exact coverp1011101101
theorem coverp101110110 : Covers (-5983761639/16000000 : ℚ) vp101110110 := join_branches bp1011101100 bp1011101101
private noncomputable def vp10111011_0 : Blocks := edgeBlocks% "full/vectors/10111011-V-0000.bin"
private noncomputable def vp10111011_1 : Blocks := edgeBlocks% "full/vectors/10111011-V-0001.bin"
private noncomputable def vp10111011_2 : Blocks := edgeBlocks% "full/vectors/10111011-V-0002.bin"
private noncomputable def vp10111011_3 : Blocks := edgeBlocks% "full/vectors/10111011-V-0003.bin"
noncomputable def vp10111011 : Blocks := (Blocks.join (Blocks.join vp10111011_0 vp10111011_1) (Blocks.join vp10111011_2 vp10111011_3))
private theorem bp101110110 : Branch 0 (-5983761639/32000000 : ℚ) vp10111011 := by
  apply branch_left_normalized (c:=vp101110110) (k:=0) (m:=226) (by decide +kernel)
  rw [show 2*(-5983761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5983761639/16000000 : ℚ) by norm_num]
  exact coverp101110110
private noncomputable def ep101110111_0 : Blocks := edgeBlocks% "full/vectors/101110111-E-0000.bin"
private noncomputable def ep101110111_1 : Blocks := edgeBlocks% "full/vectors/101110111-E-0001.bin"
private noncomputable def ep101110111_2 : Blocks := edgeBlocks% "full/vectors/101110111-E-0002.bin"
private noncomputable def ep101110111_3 : Blocks := edgeBlocks% "full/vectors/101110111-E-0003.bin"
noncomputable def ep101110111 : Blocks := (Blocks.join (Blocks.join ep101110111_0 ep101110111_1) (Blocks.join ep101110111_2 ep101110111_3))
private theorem idp101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10111011.list =
    C ((2:ℤ)^519) * horner X vp101110111.list + horner X ep101110111.list := by
  exact edge_identity (B := (2:ℤ)^744) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101110111 : Branch 1 (-5983761639/32000000 : ℚ) vp10111011 := by
  apply branch_checked idp101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-5983761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5999761639/16000000 : ℚ) by norm_num]
  exact coverp101110111
theorem coverp10111011 : Covers (-5983761639/32000000 : ℚ) vp10111011 := join_branches bp101110110 bp101110111
private noncomputable def vp1011101011_0 : Blocks := edgeBlocks% "full/vectors/1011101011-V-0000.bin"
noncomputable def vp1011101011 : Blocks := vp1011101011_0
theorem coverp1011101011 : Covers (-5975761639/8000000 : ℚ) vp1011101011 := cover_leaf (by decide +kernel)
private noncomputable def vp1011101010_0 : Blocks := edgeBlocks% "full/vectors/1011101010-V-0000.bin"
noncomputable def vp1011101010 : Blocks := vp1011101010_0
theorem coverp1011101010 : Covers (-5967761639/8000000 : ℚ) vp1011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp101110101_0 : Blocks := edgeBlocks% "full/vectors/101110101-V-0000.bin"
private noncomputable def vp101110101_1 : Blocks := edgeBlocks% "full/vectors/101110101-V-0001.bin"
noncomputable def vp101110101 : Blocks := (Blocks.join vp101110101_0 vp101110101_1)
private theorem bp1011101010 : Branch 0 (-5967761639/16000000 : ℚ) vp101110101 := by
  apply branch_left_normalized (c:=vp1011101010) (k:=0) (m:=124) (by decide +kernel)
  rw [show 2*(-5967761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5967761639/8000000 : ℚ) by norm_num]
  exact coverp1011101010
private noncomputable def ep1011101011_0 : Blocks := edgeBlocks% "full/vectors/1011101011-E-0000.bin"
private noncomputable def ep1011101011_1 : Blocks := edgeBlocks% "full/vectors/1011101011-E-0001.bin"
noncomputable def ep1011101011 : Blocks := (Blocks.join ep1011101011_0 ep1011101011_1)
private theorem idp1011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101110101.list =
    C ((2:ℤ)^273) * horner X vp1011101011.list + horner X ep1011101011.list := by
  exact edge_identity (B := (2:ℤ)^437) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011101011 : Branch 1 (-5967761639/16000000 : ℚ) vp101110101 := by
  apply branch_checked idp1011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-5967761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5975761639/8000000 : ℚ) by norm_num]
  exact coverp1011101011
theorem coverp101110101 : Covers (-5967761639/16000000 : ℚ) vp101110101 := join_branches bp1011101010 bp1011101011
private noncomputable def vp1011101001_0 : Blocks := edgeBlocks% "full/vectors/1011101001-V-0000.bin"
noncomputable def vp1011101001 : Blocks := vp1011101001_0
theorem coverp1011101001 : Covers (-5959761639/8000000 : ℚ) vp1011101001 := cover_leaf (by decide +kernel)
private noncomputable def vp1011101000_0 : Blocks := edgeBlocks% "full/vectors/1011101000-V-0000.bin"
noncomputable def vp1011101000 : Blocks := vp1011101000_0
theorem coverp1011101000 : Covers (-5951761639/8000000 : ℚ) vp1011101000 := cover_leaf (by decide +kernel)
private noncomputable def vp101110100_0 : Blocks := edgeBlocks% "full/vectors/101110100-V-0000.bin"
private noncomputable def vp101110100_1 : Blocks := edgeBlocks% "full/vectors/101110100-V-0001.bin"
noncomputable def vp101110100 : Blocks := (Blocks.join vp101110100_0 vp101110100_1)
private theorem bp1011101000 : Branch 0 (-5951761639/16000000 : ℚ) vp101110100 := by
  apply branch_left_normalized (c:=vp1011101000) (k:=0) (m:=123) (by decide +kernel)
  rw [show 2*(-5951761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5951761639/8000000 : ℚ) by norm_num]
  exact coverp1011101000
private noncomputable def ep1011101001_0 : Blocks := edgeBlocks% "full/vectors/1011101001-E-0000.bin"
private noncomputable def ep1011101001_1 : Blocks := edgeBlocks% "full/vectors/1011101001-E-0001.bin"
noncomputable def ep1011101001 : Blocks := (Blocks.join ep1011101001_0 ep1011101001_1)
private theorem idp1011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101110100.list =
    C ((2:ℤ)^273) * horner X vp1011101001.list + horner X ep1011101001.list := by
  exact edge_identity (B := (2:ℤ)^436) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011101001 : Branch 1 (-5951761639/16000000 : ℚ) vp101110100 := by
  apply branch_checked idp1011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-5951761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5959761639/8000000 : ℚ) by norm_num]
  exact coverp1011101001
theorem coverp101110100 : Covers (-5951761639/16000000 : ℚ) vp101110100 := join_branches bp1011101000 bp1011101001
private noncomputable def vp10111010_0 : Blocks := edgeBlocks% "full/vectors/10111010-V-0000.bin"
private noncomputable def vp10111010_1 : Blocks := edgeBlocks% "full/vectors/10111010-V-0001.bin"
private noncomputable def vp10111010_2 : Blocks := edgeBlocks% "full/vectors/10111010-V-0002.bin"
private noncomputable def vp10111010_3 : Blocks := edgeBlocks% "full/vectors/10111010-V-0003.bin"
noncomputable def vp10111010 : Blocks := (Blocks.join (Blocks.join vp10111010_0 vp10111010_1) (Blocks.join vp10111010_2 vp10111010_3))
private theorem bp101110100 : Branch 0 (-5951761639/32000000 : ℚ) vp10111010 := by
  apply branch_left_normalized (c:=vp101110100) (k:=0) (m:=225) (by decide +kernel)
  rw [show 2*(-5951761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5951761639/16000000 : ℚ) by norm_num]
  exact coverp101110100
private noncomputable def ep101110101_0 : Blocks := edgeBlocks% "full/vectors/101110101-E-0000.bin"
private noncomputable def ep101110101_1 : Blocks := edgeBlocks% "full/vectors/101110101-E-0001.bin"
private noncomputable def ep101110101_2 : Blocks := edgeBlocks% "full/vectors/101110101-E-0002.bin"
private noncomputable def ep101110101_3 : Blocks := edgeBlocks% "full/vectors/101110101-E-0003.bin"
noncomputable def ep101110101 : Blocks := (Blocks.join (Blocks.join ep101110101_0 ep101110101_1) (Blocks.join ep101110101_2 ep101110101_3))
private theorem idp101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10111010.list =
    C ((2:ℤ)^522) * horner X vp101110101.list + horner X ep101110101.list := by
  exact edge_identity (B := (2:ℤ)^747) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101110101 : Branch 1 (-5951761639/32000000 : ℚ) vp10111010 := by
  apply branch_checked idp101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-5951761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5967761639/16000000 : ℚ) by norm_num]
  exact coverp101110101
theorem coverp10111010 : Covers (-5951761639/32000000 : ℚ) vp10111010 := join_branches bp101110100 bp101110101
private noncomputable def vp1011101_0 : Blocks := edgeBlocks% "full/vectors/1011101-V-0000.bin"
private noncomputable def vp1011101_1 : Blocks := edgeBlocks% "full/vectors/1011101-V-0001.bin"
private noncomputable def vp1011101_2 : Blocks := edgeBlocks% "full/vectors/1011101-V-0002.bin"
private noncomputable def vp1011101_3 : Blocks := edgeBlocks% "full/vectors/1011101-V-0003.bin"
private noncomputable def vp1011101_4 : Blocks := edgeBlocks% "full/vectors/1011101-V-0004.bin"
private noncomputable def vp1011101_5 : Blocks := edgeBlocks% "full/vectors/1011101-V-0005.bin"
private noncomputable def vp1011101_6 : Blocks := edgeBlocks% "full/vectors/1011101-V-0006.bin"
noncomputable def vp1011101 : Blocks := (Blocks.join (Blocks.join vp1011101_0 (Blocks.join vp1011101_1 vp1011101_2)) (Blocks.join (Blocks.join vp1011101_3 vp1011101_4) (Blocks.join vp1011101_5 vp1011101_6)))
private theorem bp10111010 : Branch 0 (-5951761639/64000000 : ℚ) vp1011101 := by
  apply branch_left_normalized (c:=vp10111010) (k:=0) (m:=428) (by decide +kernel)
  rw [show 2*(-5951761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5951761639/32000000 : ℚ) by norm_num]
  exact coverp10111010
private noncomputable def ep10111011_0 : Blocks := edgeBlocks% "full/vectors/10111011-E-0000.bin"
private noncomputable def ep10111011_1 : Blocks := edgeBlocks% "full/vectors/10111011-E-0001.bin"
private noncomputable def ep10111011_2 : Blocks := edgeBlocks% "full/vectors/10111011-E-0002.bin"
private noncomputable def ep10111011_3 : Blocks := edgeBlocks% "full/vectors/10111011-E-0003.bin"
private noncomputable def ep10111011_4 : Blocks := edgeBlocks% "full/vectors/10111011-E-0004.bin"
private noncomputable def ep10111011_5 : Blocks := edgeBlocks% "full/vectors/10111011-E-0005.bin"
private noncomputable def ep10111011_6 : Blocks := edgeBlocks% "full/vectors/10111011-E-0006.bin"
noncomputable def ep10111011 : Blocks := (Blocks.join (Blocks.join ep10111011_0 (Blocks.join ep10111011_1 ep10111011_2)) (Blocks.join (Blocks.join ep10111011_3 ep10111011_4) (Blocks.join ep10111011_5 ep10111011_6)))
private theorem idp10111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1011101.list =
    C ((2:ℤ)^1014) * horner X vp10111011.list + horner X ep10111011.list := by
  exact edge_identity (B := (2:ℤ)^1362) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10111011 : Branch 1 (-5951761639/64000000 : ℚ) vp1011101 := by
  apply branch_checked idp10111011 (by positivity) (by decide +kernel)
  rw [show 2*(-5951761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5983761639/32000000 : ℚ) by norm_num]
  exact coverp10111011
theorem coverp1011101 : Covers (-5951761639/64000000 : ℚ) vp1011101 := join_branches bp10111010 bp10111011
private noncomputable def vp1011100111_0 : Blocks := edgeBlocks% "full/vectors/1011100111-V-0000.bin"
noncomputable def vp1011100111 : Blocks := vp1011100111_0
theorem coverp1011100111 : Covers (-5943761639/8000000 : ℚ) vp1011100111 := cover_leaf (by decide +kernel)
private noncomputable def vp1011100110_0 : Blocks := edgeBlocks% "full/vectors/1011100110-V-0000.bin"
noncomputable def vp1011100110 : Blocks := vp1011100110_0
theorem coverp1011100110 : Covers (-5935761639/8000000 : ℚ) vp1011100110 := cover_leaf (by decide +kernel)
private noncomputable def vp101110011_0 : Blocks := edgeBlocks% "full/vectors/101110011-V-0000.bin"
private noncomputable def vp101110011_1 : Blocks := edgeBlocks% "full/vectors/101110011-V-0001.bin"
noncomputable def vp101110011 : Blocks := (Blocks.join vp101110011_0 vp101110011_1)
private theorem bp1011100110 : Branch 0 (-5935761639/16000000 : ℚ) vp101110011 := by
  apply branch_left_normalized (c:=vp1011100110) (k:=0) (m:=124) (by decide +kernel)
  rw [show 2*(-5935761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5935761639/8000000 : ℚ) by norm_num]
  exact coverp1011100110
private noncomputable def ep1011100111_0 : Blocks := edgeBlocks% "full/vectors/1011100111-E-0000.bin"
private noncomputable def ep1011100111_1 : Blocks := edgeBlocks% "full/vectors/1011100111-E-0001.bin"
noncomputable def ep1011100111 : Blocks := (Blocks.join ep1011100111_0 ep1011100111_1)
private theorem idp1011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101110011.list =
    C ((2:ℤ)^273) * horner X vp1011100111.list + horner X ep1011100111.list := by
  exact edge_identity (B := (2:ℤ)^437) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011100111 : Branch 1 (-5935761639/16000000 : ℚ) vp101110011 := by
  apply branch_checked idp1011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-5935761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5943761639/8000000 : ℚ) by norm_num]
  exact coverp1011100111
theorem coverp101110011 : Covers (-5935761639/16000000 : ℚ) vp101110011 := join_branches bp1011100110 bp1011100111
private noncomputable def vp1011100101_0 : Blocks := edgeBlocks% "full/vectors/1011100101-V-0000.bin"
noncomputable def vp1011100101 : Blocks := vp1011100101_0
theorem coverp1011100101 : Covers (-5927761639/8000000 : ℚ) vp1011100101 := cover_leaf (by decide +kernel)
private noncomputable def vp1011100100_0 : Blocks := edgeBlocks% "full/vectors/1011100100-V-0000.bin"
noncomputable def vp1011100100 : Blocks := vp1011100100_0
theorem coverp1011100100 : Covers (-5919761639/8000000 : ℚ) vp1011100100 := cover_leaf (by decide +kernel)
private noncomputable def vp101110010_0 : Blocks := edgeBlocks% "full/vectors/101110010-V-0000.bin"
private noncomputable def vp101110010_1 : Blocks := edgeBlocks% "full/vectors/101110010-V-0001.bin"
noncomputable def vp101110010 : Blocks := (Blocks.join vp101110010_0 vp101110010_1)
private theorem bp1011100100 : Branch 0 (-5919761639/16000000 : ℚ) vp101110010 := by
  apply branch_left_normalized (c:=vp1011100100) (k:=0) (m:=124) (by decide +kernel)
  rw [show 2*(-5919761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5919761639/8000000 : ℚ) by norm_num]
  exact coverp1011100100
private noncomputable def ep1011100101_0 : Blocks := edgeBlocks% "full/vectors/1011100101-E-0000.bin"
private noncomputable def ep1011100101_1 : Blocks := edgeBlocks% "full/vectors/1011100101-E-0001.bin"
noncomputable def ep1011100101 : Blocks := (Blocks.join ep1011100101_0 ep1011100101_1)
private theorem idp1011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101110010.list =
    C ((2:ℤ)^274) * horner X vp1011100101.list + horner X ep1011100101.list := by
  exact edge_identity (B := (2:ℤ)^438) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011100101 : Branch 1 (-5919761639/16000000 : ℚ) vp101110010 := by
  apply branch_checked idp1011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-5919761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5927761639/8000000 : ℚ) by norm_num]
  exact coverp1011100101
theorem coverp101110010 : Covers (-5919761639/16000000 : ℚ) vp101110010 := join_branches bp1011100100 bp1011100101
private noncomputable def vp10111001_0 : Blocks := edgeBlocks% "full/vectors/10111001-V-0000.bin"
private noncomputable def vp10111001_1 : Blocks := edgeBlocks% "full/vectors/10111001-V-0001.bin"
private noncomputable def vp10111001_2 : Blocks := edgeBlocks% "full/vectors/10111001-V-0002.bin"
private noncomputable def vp10111001_3 : Blocks := edgeBlocks% "full/vectors/10111001-V-0003.bin"
noncomputable def vp10111001 : Blocks := (Blocks.join (Blocks.join vp10111001_0 vp10111001_1) (Blocks.join vp10111001_2 vp10111001_3))
private theorem bp101110010 : Branch 0 (-5919761639/32000000 : ℚ) vp10111001 := by
  apply branch_left_normalized (c:=vp101110010) (k:=0) (m:=227) (by decide +kernel)
  rw [show 2*(-5919761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5919761639/16000000 : ℚ) by norm_num]
  exact coverp101110010
private noncomputable def ep101110011_0 : Blocks := edgeBlocks% "full/vectors/101110011-E-0000.bin"
private noncomputable def ep101110011_1 : Blocks := edgeBlocks% "full/vectors/101110011-E-0001.bin"
private noncomputable def ep101110011_2 : Blocks := edgeBlocks% "full/vectors/101110011-E-0002.bin"
private noncomputable def ep101110011_3 : Blocks := edgeBlocks% "full/vectors/101110011-E-0003.bin"
noncomputable def ep101110011 : Blocks := (Blocks.join (Blocks.join ep101110011_0 ep101110011_1) (Blocks.join ep101110011_2 ep101110011_3))
private theorem idp101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10111001.list =
    C ((2:ℤ)^522) * horner X vp101110011.list + horner X ep101110011.list := by
  exact edge_identity (B := (2:ℤ)^748) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101110011 : Branch 1 (-5919761639/32000000 : ℚ) vp10111001 := by
  apply branch_checked idp101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-5919761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5935761639/16000000 : ℚ) by norm_num]
  exact coverp101110011
theorem coverp10111001 : Covers (-5919761639/32000000 : ℚ) vp10111001 := join_branches bp101110010 bp101110011
private noncomputable def vp1011100011_0 : Blocks := edgeBlocks% "full/vectors/1011100011-V-0000.bin"
noncomputable def vp1011100011 : Blocks := vp1011100011_0
theorem coverp1011100011 : Covers (-5911761639/8000000 : ℚ) vp1011100011 := cover_leaf (by decide +kernel)
private noncomputable def vp1011100010_0 : Blocks := edgeBlocks% "full/vectors/1011100010-V-0000.bin"
noncomputable def vp1011100010 : Blocks := vp1011100010_0
theorem coverp1011100010 : Covers (-5903761639/8000000 : ℚ) vp1011100010 := cover_leaf (by decide +kernel)
private noncomputable def vp101110001_0 : Blocks := edgeBlocks% "full/vectors/101110001-V-0000.bin"
private noncomputable def vp101110001_1 : Blocks := edgeBlocks% "full/vectors/101110001-V-0001.bin"
noncomputable def vp101110001 : Blocks := (Blocks.join vp101110001_0 vp101110001_1)
private theorem bp1011100010 : Branch 0 (-5903761639/16000000 : ℚ) vp101110001 := by
  apply branch_left_normalized (c:=vp1011100010) (k:=0) (m:=124) (by decide +kernel)
  rw [show 2*(-5903761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5903761639/8000000 : ℚ) by norm_num]
  exact coverp1011100010
private noncomputable def ep1011100011_0 : Blocks := edgeBlocks% "full/vectors/1011100011-E-0000.bin"
private noncomputable def ep1011100011_1 : Blocks := edgeBlocks% "full/vectors/1011100011-E-0001.bin"
noncomputable def ep1011100011 : Blocks := (Blocks.join ep1011100011_0 ep1011100011_1)
private theorem idp1011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101110001.list =
    C ((2:ℤ)^275) * horner X vp1011100011.list + horner X ep1011100011.list := by
  exact edge_identity (B := (2:ℤ)^439) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011100011 : Branch 1 (-5903761639/16000000 : ℚ) vp101110001 := by
  apply branch_checked idp1011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-5903761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5911761639/8000000 : ℚ) by norm_num]
  exact coverp1011100011
theorem coverp101110001 : Covers (-5903761639/16000000 : ℚ) vp101110001 := join_branches bp1011100010 bp1011100011
private noncomputable def vp1011100001_0 : Blocks := edgeBlocks% "full/vectors/1011100001-V-0000.bin"
noncomputable def vp1011100001 : Blocks := vp1011100001_0
theorem coverp1011100001 : Covers (-5895761639/8000000 : ℚ) vp1011100001 := cover_leaf (by decide +kernel)
private noncomputable def vp1011100000_0 : Blocks := edgeBlocks% "full/vectors/1011100000-V-0000.bin"
noncomputable def vp1011100000 : Blocks := vp1011100000_0
theorem coverp1011100000 : Covers (-5887761639/8000000 : ℚ) vp1011100000 := cover_leaf (by decide +kernel)
private noncomputable def vp101110000_0 : Blocks := edgeBlocks% "full/vectors/101110000-V-0000.bin"
private noncomputable def vp101110000_1 : Blocks := edgeBlocks% "full/vectors/101110000-V-0001.bin"
noncomputable def vp101110000 : Blocks := (Blocks.join vp101110000_0 vp101110000_1)
private theorem bp1011100000 : Branch 0 (-5887761639/16000000 : ℚ) vp101110000 := by
  apply branch_left_normalized (c:=vp1011100000) (k:=0) (m:=123) (by decide +kernel)
  rw [show 2*(-5887761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5887761639/8000000 : ℚ) by norm_num]
  exact coverp1011100000
private noncomputable def ep1011100001_0 : Blocks := edgeBlocks% "full/vectors/1011100001-E-0000.bin"
private noncomputable def ep1011100001_1 : Blocks := edgeBlocks% "full/vectors/1011100001-E-0001.bin"
noncomputable def ep1011100001 : Blocks := (Blocks.join ep1011100001_0 ep1011100001_1)
private theorem idp1011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101110000.list =
    C ((2:ℤ)^274) * horner X vp1011100001.list + horner X ep1011100001.list := by
  exact edge_identity (B := (2:ℤ)^439) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011100001 : Branch 1 (-5887761639/16000000 : ℚ) vp101110000 := by
  apply branch_checked idp1011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-5887761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5895761639/8000000 : ℚ) by norm_num]
  exact coverp1011100001
theorem coverp101110000 : Covers (-5887761639/16000000 : ℚ) vp101110000 := join_branches bp1011100000 bp1011100001
private noncomputable def vp10111000_0 : Blocks := edgeBlocks% "full/vectors/10111000-V-0000.bin"
private noncomputable def vp10111000_1 : Blocks := edgeBlocks% "full/vectors/10111000-V-0001.bin"
private noncomputable def vp10111000_2 : Blocks := edgeBlocks% "full/vectors/10111000-V-0002.bin"
private noncomputable def vp10111000_3 : Blocks := edgeBlocks% "full/vectors/10111000-V-0003.bin"
noncomputable def vp10111000 : Blocks := (Blocks.join (Blocks.join vp10111000_0 vp10111000_1) (Blocks.join vp10111000_2 vp10111000_3))
private theorem bp101110000 : Branch 0 (-5887761639/32000000 : ℚ) vp10111000 := by
  apply branch_left_normalized (c:=vp101110000) (k:=0) (m:=227) (by decide +kernel)
  rw [show 2*(-5887761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5887761639/16000000 : ℚ) by norm_num]
  exact coverp101110000
private noncomputable def ep101110001_0 : Blocks := edgeBlocks% "full/vectors/101110001-E-0000.bin"
private noncomputable def ep101110001_1 : Blocks := edgeBlocks% "full/vectors/101110001-E-0001.bin"
private noncomputable def ep101110001_2 : Blocks := edgeBlocks% "full/vectors/101110001-E-0002.bin"
private noncomputable def ep101110001_3 : Blocks := edgeBlocks% "full/vectors/101110001-E-0003.bin"
noncomputable def ep101110001 : Blocks := (Blocks.join (Blocks.join ep101110001_0 ep101110001_1) (Blocks.join ep101110001_2 ep101110001_3))
private theorem idp101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10111000.list =
    C ((2:ℤ)^524) * horner X vp101110001.list + horner X ep101110001.list := by
  exact edge_identity (B := (2:ℤ)^751) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101110001 : Branch 1 (-5887761639/32000000 : ℚ) vp10111000 := by
  apply branch_checked idp101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-5887761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5903761639/16000000 : ℚ) by norm_num]
  exact coverp101110001
theorem coverp10111000 : Covers (-5887761639/32000000 : ℚ) vp10111000 := join_branches bp101110000 bp101110001
private noncomputable def vp1011100_0 : Blocks := edgeBlocks% "full/vectors/1011100-V-0000.bin"
private noncomputable def vp1011100_1 : Blocks := edgeBlocks% "full/vectors/1011100-V-0001.bin"
private noncomputable def vp1011100_2 : Blocks := edgeBlocks% "full/vectors/1011100-V-0002.bin"
private noncomputable def vp1011100_3 : Blocks := edgeBlocks% "full/vectors/1011100-V-0003.bin"
private noncomputable def vp1011100_4 : Blocks := edgeBlocks% "full/vectors/1011100-V-0004.bin"
private noncomputable def vp1011100_5 : Blocks := edgeBlocks% "full/vectors/1011100-V-0005.bin"
private noncomputable def vp1011100_6 : Blocks := edgeBlocks% "full/vectors/1011100-V-0006.bin"
noncomputable def vp1011100 : Blocks := (Blocks.join (Blocks.join vp1011100_0 (Blocks.join vp1011100_1 vp1011100_2)) (Blocks.join (Blocks.join vp1011100_3 vp1011100_4) (Blocks.join vp1011100_5 vp1011100_6)))
private theorem bp10111000 : Branch 0 (-5887761639/64000000 : ℚ) vp1011100 := by
  apply branch_left_normalized (c:=vp10111000) (k:=0) (m:=431) (by decide +kernel)
  rw [show 2*(-5887761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5887761639/32000000 : ℚ) by norm_num]
  exact coverp10111000
private noncomputable def ep10111001_0 : Blocks := edgeBlocks% "full/vectors/10111001-E-0000.bin"
private noncomputable def ep10111001_1 : Blocks := edgeBlocks% "full/vectors/10111001-E-0001.bin"
private noncomputable def ep10111001_2 : Blocks := edgeBlocks% "full/vectors/10111001-E-0002.bin"
private noncomputable def ep10111001_3 : Blocks := edgeBlocks% "full/vectors/10111001-E-0003.bin"
private noncomputable def ep10111001_4 : Blocks := edgeBlocks% "full/vectors/10111001-E-0004.bin"
private noncomputable def ep10111001_5 : Blocks := edgeBlocks% "full/vectors/10111001-E-0005.bin"
private noncomputable def ep10111001_6 : Blocks := edgeBlocks% "full/vectors/10111001-E-0006.bin"
noncomputable def ep10111001 : Blocks := (Blocks.join (Blocks.join ep10111001_0 (Blocks.join ep10111001_1 ep10111001_2)) (Blocks.join (Blocks.join ep10111001_3 ep10111001_4) (Blocks.join ep10111001_5 ep10111001_6)))
private theorem idp10111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1011100.list =
    C ((2:ℤ)^1019) * horner X vp10111001.list + horner X ep10111001.list := by
  exact edge_identity (B := (2:ℤ)^1369) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10111001 : Branch 1 (-5887761639/64000000 : ℚ) vp1011100 := by
  apply branch_checked idp10111001 (by positivity) (by decide +kernel)
  rw [show 2*(-5887761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5919761639/32000000 : ℚ) by norm_num]
  exact coverp10111001
theorem coverp1011100 : Covers (-5887761639/64000000 : ℚ) vp1011100 := join_branches bp10111000 bp10111001
private noncomputable def vp101110_0 : Blocks := edgeBlocks% "full/vectors/101110-V-0000.bin"
private noncomputable def vp101110_1 : Blocks := edgeBlocks% "full/vectors/101110-V-0001.bin"
private noncomputable def vp101110_2 : Blocks := edgeBlocks% "full/vectors/101110-V-0002.bin"
private noncomputable def vp101110_3 : Blocks := edgeBlocks% "full/vectors/101110-V-0003.bin"
private noncomputable def vp101110_4 : Blocks := edgeBlocks% "full/vectors/101110-V-0004.bin"
private noncomputable def vp101110_5 : Blocks := edgeBlocks% "full/vectors/101110-V-0005.bin"
private noncomputable def vp101110_6 : Blocks := edgeBlocks% "full/vectors/101110-V-0006.bin"
private noncomputable def vp101110_7 : Blocks := edgeBlocks% "full/vectors/101110-V-0007.bin"
private noncomputable def vp101110_8 : Blocks := edgeBlocks% "full/vectors/101110-V-0008.bin"
private noncomputable def vp101110_9 : Blocks := edgeBlocks% "full/vectors/101110-V-0009.bin"
private noncomputable def vp101110_10 : Blocks := edgeBlocks% "full/vectors/101110-V-0010.bin"
private noncomputable def vp101110_11 : Blocks := edgeBlocks% "full/vectors/101110-V-0011.bin"
private noncomputable def vp101110_12 : Blocks := edgeBlocks% "full/vectors/101110-V-0012.bin"
noncomputable def vp101110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp101110_0 (Blocks.join vp101110_1 vp101110_2)) (Blocks.join vp101110_3 (Blocks.join vp101110_4 vp101110_5))) (Blocks.join (Blocks.join vp101110_6 (Blocks.join vp101110_7 vp101110_8)) (Blocks.join (Blocks.join vp101110_9 vp101110_10) (Blocks.join vp101110_11 vp101110_12))))
private theorem bp1011100 : Branch 0 (-5887761639/128000000 : ℚ) vp101110 := by
  apply branch_left_normalized (c:=vp1011100) (k:=0) (m:=833) (by decide +kernel)
  rw [show 2*(-5887761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-5887761639/64000000 : ℚ) by norm_num]
  exact coverp1011100
private noncomputable def ep1011101_0 : Blocks := edgeBlocks% "full/vectors/1011101-E-0000.bin"
private noncomputable def ep1011101_1 : Blocks := edgeBlocks% "full/vectors/1011101-E-0001.bin"
private noncomputable def ep1011101_2 : Blocks := edgeBlocks% "full/vectors/1011101-E-0002.bin"
private noncomputable def ep1011101_3 : Blocks := edgeBlocks% "full/vectors/1011101-E-0003.bin"
private noncomputable def ep1011101_4 : Blocks := edgeBlocks% "full/vectors/1011101-E-0004.bin"
private noncomputable def ep1011101_5 : Blocks := edgeBlocks% "full/vectors/1011101-E-0005.bin"
private noncomputable def ep1011101_6 : Blocks := edgeBlocks% "full/vectors/1011101-E-0006.bin"
private noncomputable def ep1011101_7 : Blocks := edgeBlocks% "full/vectors/1011101-E-0007.bin"
private noncomputable def ep1011101_8 : Blocks := edgeBlocks% "full/vectors/1011101-E-0008.bin"
private noncomputable def ep1011101_9 : Blocks := edgeBlocks% "full/vectors/1011101-E-0009.bin"
private noncomputable def ep1011101_10 : Blocks := edgeBlocks% "full/vectors/1011101-E-0010.bin"
private noncomputable def ep1011101_11 : Blocks := edgeBlocks% "full/vectors/1011101-E-0011.bin"
private noncomputable def ep1011101_12 : Blocks := edgeBlocks% "full/vectors/1011101-E-0012.bin"
noncomputable def ep1011101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1011101_0 (Blocks.join ep1011101_1 ep1011101_2)) (Blocks.join ep1011101_3 (Blocks.join ep1011101_4 ep1011101_5))) (Blocks.join (Blocks.join ep1011101_6 (Blocks.join ep1011101_7 ep1011101_8)) (Blocks.join (Blocks.join ep1011101_9 ep1011101_10) (Blocks.join ep1011101_11 ep1011101_12))))
private theorem idp1011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101110.list =
    C ((2:ℤ)^1993) * horner X vp1011101.list + horner X ep1011101.list := by
  exact edge_identity (B := (2:ℤ)^2589) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011101 : Branch 1 (-5887761639/128000000 : ℚ) vp101110 := by
  apply branch_checked idp1011101 (by positivity) (by decide +kernel)
  rw [show 2*(-5887761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-5951761639/64000000 : ℚ) by norm_num]
  exact coverp1011101
theorem coverp101110 : Covers (-5887761639/128000000 : ℚ) vp101110 := join_branches bp1011100 bp1011101
private noncomputable def vp10111_0 : Blocks := edgeBlocks% "full/vectors/10111-V-0000.bin"
private noncomputable def vp10111_1 : Blocks := edgeBlocks% "full/vectors/10111-V-0001.bin"
private noncomputable def vp10111_2 : Blocks := edgeBlocks% "full/vectors/10111-V-0002.bin"
private noncomputable def vp10111_3 : Blocks := edgeBlocks% "full/vectors/10111-V-0003.bin"
private noncomputable def vp10111_4 : Blocks := edgeBlocks% "full/vectors/10111-V-0004.bin"
private noncomputable def vp10111_5 : Blocks := edgeBlocks% "full/vectors/10111-V-0005.bin"
private noncomputable def vp10111_6 : Blocks := edgeBlocks% "full/vectors/10111-V-0006.bin"
private noncomputable def vp10111_7 : Blocks := edgeBlocks% "full/vectors/10111-V-0007.bin"
private noncomputable def vp10111_8 : Blocks := edgeBlocks% "full/vectors/10111-V-0008.bin"
private noncomputable def vp10111_9 : Blocks := edgeBlocks% "full/vectors/10111-V-0009.bin"
private noncomputable def vp10111_10 : Blocks := edgeBlocks% "full/vectors/10111-V-0010.bin"
private noncomputable def vp10111_11 : Blocks := edgeBlocks% "full/vectors/10111-V-0011.bin"
private noncomputable def vp10111_12 : Blocks := edgeBlocks% "full/vectors/10111-V-0012.bin"
private noncomputable def vp10111_13 : Blocks := edgeBlocks% "full/vectors/10111-V-0013.bin"
private noncomputable def vp10111_14 : Blocks := edgeBlocks% "full/vectors/10111-V-0014.bin"
private noncomputable def vp10111_15 : Blocks := edgeBlocks% "full/vectors/10111-V-0015.bin"
private noncomputable def vp10111_16 : Blocks := edgeBlocks% "full/vectors/10111-V-0016.bin"
private noncomputable def vp10111_17 : Blocks := edgeBlocks% "full/vectors/10111-V-0017.bin"
private noncomputable def vp10111_18 : Blocks := edgeBlocks% "full/vectors/10111-V-0018.bin"
private noncomputable def vp10111_19 : Blocks := edgeBlocks% "full/vectors/10111-V-0019.bin"
private noncomputable def vp10111_20 : Blocks := edgeBlocks% "full/vectors/10111-V-0020.bin"
private noncomputable def vp10111_21 : Blocks := edgeBlocks% "full/vectors/10111-V-0021.bin"
private noncomputable def vp10111_22 : Blocks := edgeBlocks% "full/vectors/10111-V-0022.bin"
private noncomputable def vp10111_23 : Blocks := edgeBlocks% "full/vectors/10111-V-0023.bin"
private noncomputable def vp10111_24 : Blocks := edgeBlocks% "full/vectors/10111-V-0024.bin"
noncomputable def vp10111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp10111_0 (Blocks.join vp10111_1 vp10111_2)) (Blocks.join vp10111_3 (Blocks.join vp10111_4 vp10111_5))) (Blocks.join (Blocks.join vp10111_6 (Blocks.join vp10111_7 vp10111_8)) (Blocks.join vp10111_9 (Blocks.join vp10111_10 vp10111_11)))) (Blocks.join (Blocks.join (Blocks.join vp10111_12 (Blocks.join vp10111_13 vp10111_14)) (Blocks.join vp10111_15 (Blocks.join vp10111_16 vp10111_17))) (Blocks.join (Blocks.join vp10111_18 (Blocks.join vp10111_19 vp10111_20)) (Blocks.join (Blocks.join vp10111_21 vp10111_22) (Blocks.join vp10111_23 vp10111_24)))))
private theorem bp101110 : Branch 0 (-5887761639/256000000 : ℚ) vp10111 := by
  apply branch_left_normalized (c:=vp101110) (k:=0) (m:=1623) (by decide +kernel)
  rw [show 2*(-5887761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-5887761639/128000000 : ℚ) by norm_num]
  exact coverp101110
private noncomputable def ep101111_0 : Blocks := edgeBlocks% "full/vectors/101111-E-0000.bin"
private noncomputable def ep101111_1 : Blocks := edgeBlocks% "full/vectors/101111-E-0001.bin"
private noncomputable def ep101111_2 : Blocks := edgeBlocks% "full/vectors/101111-E-0002.bin"
private noncomputable def ep101111_3 : Blocks := edgeBlocks% "full/vectors/101111-E-0003.bin"
private noncomputable def ep101111_4 : Blocks := edgeBlocks% "full/vectors/101111-E-0004.bin"
private noncomputable def ep101111_5 : Blocks := edgeBlocks% "full/vectors/101111-E-0005.bin"
private noncomputable def ep101111_6 : Blocks := edgeBlocks% "full/vectors/101111-E-0006.bin"
private noncomputable def ep101111_7 : Blocks := edgeBlocks% "full/vectors/101111-E-0007.bin"
private noncomputable def ep101111_8 : Blocks := edgeBlocks% "full/vectors/101111-E-0008.bin"
private noncomputable def ep101111_9 : Blocks := edgeBlocks% "full/vectors/101111-E-0009.bin"
private noncomputable def ep101111_10 : Blocks := edgeBlocks% "full/vectors/101111-E-0010.bin"
private noncomputable def ep101111_11 : Blocks := edgeBlocks% "full/vectors/101111-E-0011.bin"
private noncomputable def ep101111_12 : Blocks := edgeBlocks% "full/vectors/101111-E-0012.bin"
private noncomputable def ep101111_13 : Blocks := edgeBlocks% "full/vectors/101111-E-0013.bin"
private noncomputable def ep101111_14 : Blocks := edgeBlocks% "full/vectors/101111-E-0014.bin"
private noncomputable def ep101111_15 : Blocks := edgeBlocks% "full/vectors/101111-E-0015.bin"
private noncomputable def ep101111_16 : Blocks := edgeBlocks% "full/vectors/101111-E-0016.bin"
private noncomputable def ep101111_17 : Blocks := edgeBlocks% "full/vectors/101111-E-0017.bin"
private noncomputable def ep101111_18 : Blocks := edgeBlocks% "full/vectors/101111-E-0018.bin"
private noncomputable def ep101111_19 : Blocks := edgeBlocks% "full/vectors/101111-E-0019.bin"
private noncomputable def ep101111_20 : Blocks := edgeBlocks% "full/vectors/101111-E-0020.bin"
private noncomputable def ep101111_21 : Blocks := edgeBlocks% "full/vectors/101111-E-0021.bin"
private noncomputable def ep101111_22 : Blocks := edgeBlocks% "full/vectors/101111-E-0022.bin"
private noncomputable def ep101111_23 : Blocks := edgeBlocks% "full/vectors/101111-E-0023.bin"
private noncomputable def ep101111_24 : Blocks := edgeBlocks% "full/vectors/101111-E-0024.bin"
noncomputable def ep101111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep101111_0 (Blocks.join ep101111_1 ep101111_2)) (Blocks.join ep101111_3 (Blocks.join ep101111_4 ep101111_5))) (Blocks.join (Blocks.join ep101111_6 (Blocks.join ep101111_7 ep101111_8)) (Blocks.join ep101111_9 (Blocks.join ep101111_10 ep101111_11)))) (Blocks.join (Blocks.join (Blocks.join ep101111_12 (Blocks.join ep101111_13 ep101111_14)) (Blocks.join ep101111_15 (Blocks.join ep101111_16 ep101111_17))) (Blocks.join (Blocks.join ep101111_18 (Blocks.join ep101111_19 ep101111_20)) (Blocks.join (Blocks.join ep101111_21 ep101111_22) (Blocks.join ep101111_23 ep101111_24)))))
private def ptsp101111 : List ℤ := [((2:ℤ)^3818+0),((2:ℤ)^3818+1)]
private theorem boundp101111 : 2^vp10111.size*absSum vp10111.list + ((2:ℤ)^3882*absSum vp101111.list+absSum ep101111.list) < (2:ℤ)^4956 := by decide +kernel
private theorem pointp101111_0 : fastHom 1 ((2:ℤ)^3818+0) vp10111 = ((2:ℤ)^3882)*vp101111.subst ((2:ℤ)^3818+0)+ep101111.subst ((2:ℤ)^3818+0) := by decide +kernel
private theorem pointp101111_1 : fastHom 1 ((2:ℤ)^3818+1) vp10111 = ((2:ℤ)^3882)*vp101111.subst ((2:ℤ)^3818+1)+ep101111.subst ((2:ℤ)^3818+1) := by decide +kernel
private theorem checkp101111 (x:ℤ) (hx:x ∈ ptsp101111) : fastHom 1 x vp10111 = ((2:ℤ)^3882)*vp101111.subst x+ep101111.subst x := by
  simp only [ptsp101111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp101111_0
  · exact pointp101111_1
private theorem idp101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10111.list =
    C ((2:ℤ)^3882) * horner X vp101111.list + horner X ep101111.list := by
  apply edge_identity (B := (2:ℤ)^4956) (by decide) (by positivity) (by positivity) boundp101111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp101111 (by decide +kernel)
  · have h : ptsp101111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp101111.trans_le (by decide +kernel)
  · exact checkp101111
private theorem bp101111 : Branch 1 (-5887761639/256000000 : ℚ) vp10111 := by
  apply branch_checked idp101111 (by positivity) (by decide +kernel)
  rw [show 2*(-5887761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-6015761639/128000000 : ℚ) by norm_num]
  exact coverp101111
theorem coverp10111 : Covers (-5887761639/256000000 : ℚ) vp10111 := join_branches bp101110 bp101111
private noncomputable def vp1011011111_0 : Blocks := edgeBlocks% "full/vectors/1011011111-V-0000.bin"
noncomputable def vp1011011111 : Blocks := vp1011011111_0
theorem coverp1011011111 : Covers (-5879761639/8000000 : ℚ) vp1011011111 := cover_leaf (by decide +kernel)
private noncomputable def vp1011011110_0 : Blocks := edgeBlocks% "full/vectors/1011011110-V-0000.bin"
noncomputable def vp1011011110 : Blocks := vp1011011110_0
theorem coverp1011011110 : Covers (-5871761639/8000000 : ℚ) vp1011011110 := cover_leaf (by decide +kernel)
private noncomputable def vp101101111_0 : Blocks := edgeBlocks% "full/vectors/101101111-V-0000.bin"
private noncomputable def vp101101111_1 : Blocks := edgeBlocks% "full/vectors/101101111-V-0001.bin"
noncomputable def vp101101111 : Blocks := (Blocks.join vp101101111_0 vp101101111_1)
private theorem bp1011011110 : Branch 0 (-5871761639/16000000 : ℚ) vp101101111 := by
  apply branch_left_normalized (c:=vp1011011110) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-5871761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5871761639/8000000 : ℚ) by norm_num]
  exact coverp1011011110
private noncomputable def ep1011011111_0 : Blocks := edgeBlocks% "full/vectors/1011011111-E-0000.bin"
private noncomputable def ep1011011111_1 : Blocks := edgeBlocks% "full/vectors/1011011111-E-0001.bin"
noncomputable def ep1011011111 : Blocks := (Blocks.join ep1011011111_0 ep1011011111_1)
private theorem idp1011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101101111.list =
    C ((2:ℤ)^274) * horner X vp1011011111.list + horner X ep1011011111.list := by
  exact edge_identity (B := (2:ℤ)^438) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011011111 : Branch 1 (-5871761639/16000000 : ℚ) vp101101111 := by
  apply branch_checked idp1011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-5871761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5879761639/8000000 : ℚ) by norm_num]
  exact coverp1011011111
theorem coverp101101111 : Covers (-5871761639/16000000 : ℚ) vp101101111 := join_branches bp1011011110 bp1011011111
private noncomputable def vp1011011101_0 : Blocks := edgeBlocks% "full/vectors/1011011101-V-0000.bin"
noncomputable def vp1011011101 : Blocks := vp1011011101_0
theorem coverp1011011101 : Covers (-5863761639/8000000 : ℚ) vp1011011101 := cover_leaf (by decide +kernel)
private noncomputable def vp1011011100_0 : Blocks := edgeBlocks% "full/vectors/1011011100-V-0000.bin"
noncomputable def vp1011011100 : Blocks := vp1011011100_0
theorem coverp1011011100 : Covers (-5855761639/8000000 : ℚ) vp1011011100 := cover_leaf (by decide +kernel)
private noncomputable def vp101101110_0 : Blocks := edgeBlocks% "full/vectors/101101110-V-0000.bin"
private noncomputable def vp101101110_1 : Blocks := edgeBlocks% "full/vectors/101101110-V-0001.bin"
noncomputable def vp101101110 : Blocks := (Blocks.join vp101101110_0 vp101101110_1)
private theorem bp1011011100 : Branch 0 (-5855761639/16000000 : ℚ) vp101101110 := by
  apply branch_left_normalized (c:=vp1011011100) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-5855761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5855761639/8000000 : ℚ) by norm_num]
  exact coverp1011011100
private noncomputable def ep1011011101_0 : Blocks := edgeBlocks% "full/vectors/1011011101-E-0000.bin"
private noncomputable def ep1011011101_1 : Blocks := edgeBlocks% "full/vectors/1011011101-E-0001.bin"
noncomputable def ep1011011101 : Blocks := (Blocks.join ep1011011101_0 ep1011011101_1)
private theorem idp1011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101101110.list =
    C ((2:ℤ)^275) * horner X vp1011011101.list + horner X ep1011011101.list := by
  exact edge_identity (B := (2:ℤ)^439) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011011101 : Branch 1 (-5855761639/16000000 : ℚ) vp101101110 := by
  apply branch_checked idp1011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-5855761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5863761639/8000000 : ℚ) by norm_num]
  exact coverp1011011101
theorem coverp101101110 : Covers (-5855761639/16000000 : ℚ) vp101101110 := join_branches bp1011011100 bp1011011101
private noncomputable def vp10110111_0 : Blocks := edgeBlocks% "full/vectors/10110111-V-0000.bin"
private noncomputable def vp10110111_1 : Blocks := edgeBlocks% "full/vectors/10110111-V-0001.bin"
private noncomputable def vp10110111_2 : Blocks := edgeBlocks% "full/vectors/10110111-V-0002.bin"
private noncomputable def vp10110111_3 : Blocks := edgeBlocks% "full/vectors/10110111-V-0003.bin"
noncomputable def vp10110111 : Blocks := (Blocks.join (Blocks.join vp10110111_0 vp10110111_1) (Blocks.join vp10110111_2 vp10110111_3))
private theorem bp101101110 : Branch 0 (-5855761639/32000000 : ℚ) vp10110111 := by
  apply branch_left_normalized (c:=vp101101110) (k:=0) (m:=227) (by decide +kernel)
  rw [show 2*(-5855761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5855761639/16000000 : ℚ) by norm_num]
  exact coverp101101110
private noncomputable def ep101101111_0 : Blocks := edgeBlocks% "full/vectors/101101111-E-0000.bin"
private noncomputable def ep101101111_1 : Blocks := edgeBlocks% "full/vectors/101101111-E-0001.bin"
private noncomputable def ep101101111_2 : Blocks := edgeBlocks% "full/vectors/101101111-E-0002.bin"
private noncomputable def ep101101111_3 : Blocks := edgeBlocks% "full/vectors/101101111-E-0003.bin"
noncomputable def ep101101111 : Blocks := (Blocks.join (Blocks.join ep101101111_0 ep101101111_1) (Blocks.join ep101101111_2 ep101101111_3))
private theorem idp101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10110111.list =
    C ((2:ℤ)^526) * horner X vp101101111.list + horner X ep101101111.list := by
  exact edge_identity (B := (2:ℤ)^753) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101101111 : Branch 1 (-5855761639/32000000 : ℚ) vp10110111 := by
  apply branch_checked idp101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-5855761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5871761639/16000000 : ℚ) by norm_num]
  exact coverp101101111
theorem coverp10110111 : Covers (-5855761639/32000000 : ℚ) vp10110111 := join_branches bp101101110 bp101101111
private noncomputable def vp1011011011_0 : Blocks := edgeBlocks% "full/vectors/1011011011-V-0000.bin"
noncomputable def vp1011011011 : Blocks := vp1011011011_0
theorem coverp1011011011 : Covers (-5847761639/8000000 : ℚ) vp1011011011 := cover_leaf (by decide +kernel)
private noncomputable def vp1011011010_0 : Blocks := edgeBlocks% "full/vectors/1011011010-V-0000.bin"
noncomputable def vp1011011010 : Blocks := vp1011011010_0
theorem coverp1011011010 : Covers (-5839761639/8000000 : ℚ) vp1011011010 := cover_leaf (by decide +kernel)
private noncomputable def vp101101101_0 : Blocks := edgeBlocks% "full/vectors/101101101-V-0000.bin"
private noncomputable def vp101101101_1 : Blocks := edgeBlocks% "full/vectors/101101101-V-0001.bin"
noncomputable def vp101101101 : Blocks := (Blocks.join vp101101101_0 vp101101101_1)
private theorem bp1011011010 : Branch 0 (-5839761639/16000000 : ℚ) vp101101101 := by
  apply branch_left_normalized (c:=vp1011011010) (k:=0) (m:=124) (by decide +kernel)
  rw [show 2*(-5839761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5839761639/8000000 : ℚ) by norm_num]
  exact coverp1011011010
private noncomputable def ep1011011011_0 : Blocks := edgeBlocks% "full/vectors/1011011011-E-0000.bin"
private noncomputable def ep1011011011_1 : Blocks := edgeBlocks% "full/vectors/1011011011-E-0001.bin"
noncomputable def ep1011011011 : Blocks := (Blocks.join ep1011011011_0 ep1011011011_1)
private theorem idp1011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101101101.list =
    C ((2:ℤ)^275) * horner X vp1011011011.list + horner X ep1011011011.list := by
  exact edge_identity (B := (2:ℤ)^440) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011011011 : Branch 1 (-5839761639/16000000 : ℚ) vp101101101 := by
  apply branch_checked idp1011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-5839761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5847761639/8000000 : ℚ) by norm_num]
  exact coverp1011011011
theorem coverp101101101 : Covers (-5839761639/16000000 : ℚ) vp101101101 := join_branches bp1011011010 bp1011011011
private noncomputable def vp1011011001_0 : Blocks := edgeBlocks% "full/vectors/1011011001-V-0000.bin"
noncomputable def vp1011011001 : Blocks := vp1011011001_0
theorem coverp1011011001 : Covers (-5831761639/8000000 : ℚ) vp1011011001 := cover_leaf (by decide +kernel)
private noncomputable def vp1011011000_0 : Blocks := edgeBlocks% "full/vectors/1011011000-V-0000.bin"
noncomputable def vp1011011000 : Blocks := vp1011011000_0
theorem coverp1011011000 : Covers (-5823761639/8000000 : ℚ) vp1011011000 := cover_leaf (by decide +kernel)
private noncomputable def vp101101100_0 : Blocks := edgeBlocks% "full/vectors/101101100-V-0000.bin"
private noncomputable def vp101101100_1 : Blocks := edgeBlocks% "full/vectors/101101100-V-0001.bin"
noncomputable def vp101101100 : Blocks := (Blocks.join vp101101100_0 vp101101100_1)
private theorem bp1011011000 : Branch 0 (-5823761639/16000000 : ℚ) vp101101100 := by
  apply branch_left_normalized (c:=vp1011011000) (k:=0) (m:=124) (by decide +kernel)
  rw [show 2*(-5823761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5823761639/8000000 : ℚ) by norm_num]
  exact coverp1011011000
private noncomputable def ep1011011001_0 : Blocks := edgeBlocks% "full/vectors/1011011001-E-0000.bin"
private noncomputable def ep1011011001_1 : Blocks := edgeBlocks% "full/vectors/1011011001-E-0001.bin"
noncomputable def ep1011011001 : Blocks := (Blocks.join ep1011011001_0 ep1011011001_1)
private theorem idp1011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101101100.list =
    C ((2:ℤ)^275) * horner X vp1011011001.list + horner X ep1011011001.list := by
  exact edge_identity (B := (2:ℤ)^440) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011011001 : Branch 1 (-5823761639/16000000 : ℚ) vp101101100 := by
  apply branch_checked idp1011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-5823761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5831761639/8000000 : ℚ) by norm_num]
  exact coverp1011011001
theorem coverp101101100 : Covers (-5823761639/16000000 : ℚ) vp101101100 := join_branches bp1011011000 bp1011011001
private noncomputable def vp10110110_0 : Blocks := edgeBlocks% "full/vectors/10110110-V-0000.bin"
private noncomputable def vp10110110_1 : Blocks := edgeBlocks% "full/vectors/10110110-V-0001.bin"
private noncomputable def vp10110110_2 : Blocks := edgeBlocks% "full/vectors/10110110-V-0002.bin"
private noncomputable def vp10110110_3 : Blocks := edgeBlocks% "full/vectors/10110110-V-0003.bin"
noncomputable def vp10110110 : Blocks := (Blocks.join (Blocks.join vp10110110_0 vp10110110_1) (Blocks.join vp10110110_2 vp10110110_3))
private theorem bp101101100 : Branch 0 (-5823761639/32000000 : ℚ) vp10110110 := by
  apply branch_left_normalized (c:=vp101101100) (k:=0) (m:=228) (by decide +kernel)
  rw [show 2*(-5823761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5823761639/16000000 : ℚ) by norm_num]
  exact coverp101101100
private noncomputable def ep101101101_0 : Blocks := edgeBlocks% "full/vectors/101101101-E-0000.bin"
private noncomputable def ep101101101_1 : Blocks := edgeBlocks% "full/vectors/101101101-E-0001.bin"
private noncomputable def ep101101101_2 : Blocks := edgeBlocks% "full/vectors/101101101-E-0002.bin"
private noncomputable def ep101101101_3 : Blocks := edgeBlocks% "full/vectors/101101101-E-0003.bin"
noncomputable def ep101101101 : Blocks := (Blocks.join (Blocks.join ep101101101_0 ep101101101_1) (Blocks.join ep101101101_2 ep101101101_3))
private theorem idp101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10110110.list =
    C ((2:ℤ)^526) * horner X vp101101101.list + horner X ep101101101.list := by
  exact edge_identity (B := (2:ℤ)^754) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101101101 : Branch 1 (-5823761639/32000000 : ℚ) vp10110110 := by
  apply branch_checked idp101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-5823761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5839761639/16000000 : ℚ) by norm_num]
  exact coverp101101101
theorem coverp10110110 : Covers (-5823761639/32000000 : ℚ) vp10110110 := join_branches bp101101100 bp101101101
private noncomputable def vp1011011_0 : Blocks := edgeBlocks% "full/vectors/1011011-V-0000.bin"
private noncomputable def vp1011011_1 : Blocks := edgeBlocks% "full/vectors/1011011-V-0001.bin"
private noncomputable def vp1011011_2 : Blocks := edgeBlocks% "full/vectors/1011011-V-0002.bin"
private noncomputable def vp1011011_3 : Blocks := edgeBlocks% "full/vectors/1011011-V-0003.bin"
private noncomputable def vp1011011_4 : Blocks := edgeBlocks% "full/vectors/1011011-V-0004.bin"
private noncomputable def vp1011011_5 : Blocks := edgeBlocks% "full/vectors/1011011-V-0005.bin"
private noncomputable def vp1011011_6 : Blocks := edgeBlocks% "full/vectors/1011011-V-0006.bin"
noncomputable def vp1011011 : Blocks := (Blocks.join (Blocks.join vp1011011_0 (Blocks.join vp1011011_1 vp1011011_2)) (Blocks.join (Blocks.join vp1011011_3 vp1011011_4) (Blocks.join vp1011011_5 vp1011011_6)))
private theorem bp10110110 : Branch 0 (-5823761639/64000000 : ℚ) vp1011011 := by
  apply branch_left_normalized (c:=vp10110110) (k:=0) (m:=433) (by decide +kernel)
  rw [show 2*(-5823761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5823761639/32000000 : ℚ) by norm_num]
  exact coverp10110110
private noncomputable def ep10110111_0 : Blocks := edgeBlocks% "full/vectors/10110111-E-0000.bin"
private noncomputable def ep10110111_1 : Blocks := edgeBlocks% "full/vectors/10110111-E-0001.bin"
private noncomputable def ep10110111_2 : Blocks := edgeBlocks% "full/vectors/10110111-E-0002.bin"
private noncomputable def ep10110111_3 : Blocks := edgeBlocks% "full/vectors/10110111-E-0003.bin"
private noncomputable def ep10110111_4 : Blocks := edgeBlocks% "full/vectors/10110111-E-0004.bin"
private noncomputable def ep10110111_5 : Blocks := edgeBlocks% "full/vectors/10110111-E-0005.bin"
private noncomputable def ep10110111_6 : Blocks := edgeBlocks% "full/vectors/10110111-E-0006.bin"
noncomputable def ep10110111 : Blocks := (Blocks.join (Blocks.join ep10110111_0 (Blocks.join ep10110111_1 ep10110111_2)) (Blocks.join (Blocks.join ep10110111_3 ep10110111_4) (Blocks.join ep10110111_5 ep10110111_6)))
private theorem idp10110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1011011.list =
    C ((2:ℤ)^1023) * horner X vp10110111.list + horner X ep10110111.list := by
  exact edge_identity (B := (2:ℤ)^1376) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10110111 : Branch 1 (-5823761639/64000000 : ℚ) vp1011011 := by
  apply branch_checked idp10110111 (by positivity) (by decide +kernel)
  rw [show 2*(-5823761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5855761639/32000000 : ℚ) by norm_num]
  exact coverp10110111
theorem coverp1011011 : Covers (-5823761639/64000000 : ℚ) vp1011011 := join_branches bp10110110 bp10110111
private noncomputable def vp1011010111_0 : Blocks := edgeBlocks% "full/vectors/1011010111-V-0000.bin"
noncomputable def vp1011010111 : Blocks := vp1011010111_0
theorem coverp1011010111 : Covers (-5815761639/8000000 : ℚ) vp1011010111 := cover_leaf (by decide +kernel)
private noncomputable def vp1011010110_0 : Blocks := edgeBlocks% "full/vectors/1011010110-V-0000.bin"
noncomputable def vp1011010110 : Blocks := vp1011010110_0
theorem coverp1011010110 : Covers (-5807761639/8000000 : ℚ) vp1011010110 := cover_leaf (by decide +kernel)
private noncomputable def vp101101011_0 : Blocks := edgeBlocks% "full/vectors/101101011-V-0000.bin"
private noncomputable def vp101101011_1 : Blocks := edgeBlocks% "full/vectors/101101011-V-0001.bin"
noncomputable def vp101101011 : Blocks := (Blocks.join vp101101011_0 vp101101011_1)
private theorem bp1011010110 : Branch 0 (-5807761639/16000000 : ℚ) vp101101011 := by
  apply branch_left_normalized (c:=vp1011010110) (k:=0) (m:=124) (by decide +kernel)
  rw [show 2*(-5807761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5807761639/8000000 : ℚ) by norm_num]
  exact coverp1011010110
private noncomputable def ep1011010111_0 : Blocks := edgeBlocks% "full/vectors/1011010111-E-0000.bin"
private noncomputable def ep1011010111_1 : Blocks := edgeBlocks% "full/vectors/1011010111-E-0001.bin"
noncomputable def ep1011010111 : Blocks := (Blocks.join ep1011010111_0 ep1011010111_1)
private theorem idp1011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101101011.list =
    C ((2:ℤ)^276) * horner X vp1011010111.list + horner X ep1011010111.list := by
  exact edge_identity (B := (2:ℤ)^441) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011010111 : Branch 1 (-5807761639/16000000 : ℚ) vp101101011 := by
  apply branch_checked idp1011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-5807761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5815761639/8000000 : ℚ) by norm_num]
  exact coverp1011010111
theorem coverp101101011 : Covers (-5807761639/16000000 : ℚ) vp101101011 := join_branches bp1011010110 bp1011010111
private noncomputable def vp1011010101_0 : Blocks := edgeBlocks% "full/vectors/1011010101-V-0000.bin"
noncomputable def vp1011010101 : Blocks := vp1011010101_0
theorem coverp1011010101 : Covers (-5799761639/8000000 : ℚ) vp1011010101 := cover_leaf (by decide +kernel)
private noncomputable def vp1011010100_0 : Blocks := edgeBlocks% "full/vectors/1011010100-V-0000.bin"
noncomputable def vp1011010100 : Blocks := vp1011010100_0
theorem coverp1011010100 : Covers (-5791761639/8000000 : ℚ) vp1011010100 := cover_leaf (by decide +kernel)
private noncomputable def vp101101010_0 : Blocks := edgeBlocks% "full/vectors/101101010-V-0000.bin"
private noncomputable def vp101101010_1 : Blocks := edgeBlocks% "full/vectors/101101010-V-0001.bin"
noncomputable def vp101101010 : Blocks := (Blocks.join vp101101010_0 vp101101010_1)
private theorem bp1011010100 : Branch 0 (-5791761639/16000000 : ℚ) vp101101010 := by
  apply branch_left_normalized (c:=vp1011010100) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-5791761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5791761639/8000000 : ℚ) by norm_num]
  exact coverp1011010100
private noncomputable def ep1011010101_0 : Blocks := edgeBlocks% "full/vectors/1011010101-E-0000.bin"
private noncomputable def ep1011010101_1 : Blocks := edgeBlocks% "full/vectors/1011010101-E-0001.bin"
noncomputable def ep1011010101 : Blocks := (Blocks.join ep1011010101_0 ep1011010101_1)
private theorem idp1011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101101010.list =
    C ((2:ℤ)^275) * horner X vp1011010101.list + horner X ep1011010101.list := by
  exact edge_identity (B := (2:ℤ)^440) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011010101 : Branch 1 (-5791761639/16000000 : ℚ) vp101101010 := by
  apply branch_checked idp1011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-5791761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5799761639/8000000 : ℚ) by norm_num]
  exact coverp1011010101
theorem coverp101101010 : Covers (-5791761639/16000000 : ℚ) vp101101010 := join_branches bp1011010100 bp1011010101
private noncomputable def vp10110101_0 : Blocks := edgeBlocks% "full/vectors/10110101-V-0000.bin"
private noncomputable def vp10110101_1 : Blocks := edgeBlocks% "full/vectors/10110101-V-0001.bin"
private noncomputable def vp10110101_2 : Blocks := edgeBlocks% "full/vectors/10110101-V-0002.bin"
private noncomputable def vp10110101_3 : Blocks := edgeBlocks% "full/vectors/10110101-V-0003.bin"
noncomputable def vp10110101 : Blocks := (Blocks.join (Blocks.join vp10110101_0 vp10110101_1) (Blocks.join vp10110101_2 vp10110101_3))
private theorem bp101101010 : Branch 0 (-5791761639/32000000 : ℚ) vp10110101 := by
  apply branch_left_normalized (c:=vp101101010) (k:=0) (m:=228) (by decide +kernel)
  rw [show 2*(-5791761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5791761639/16000000 : ℚ) by norm_num]
  exact coverp101101010
private noncomputable def ep101101011_0 : Blocks := edgeBlocks% "full/vectors/101101011-E-0000.bin"
private noncomputable def ep101101011_1 : Blocks := edgeBlocks% "full/vectors/101101011-E-0001.bin"
private noncomputable def ep101101011_2 : Blocks := edgeBlocks% "full/vectors/101101011-E-0002.bin"
private noncomputable def ep101101011_3 : Blocks := edgeBlocks% "full/vectors/101101011-E-0003.bin"
noncomputable def ep101101011 : Blocks := (Blocks.join (Blocks.join ep101101011_0 ep101101011_1) (Blocks.join ep101101011_2 ep101101011_3))
private theorem idp101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10110101.list =
    C ((2:ℤ)^526) * horner X vp101101011.list + horner X ep101101011.list := by
  exact edge_identity (B := (2:ℤ)^755) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101101011 : Branch 1 (-5791761639/32000000 : ℚ) vp10110101 := by
  apply branch_checked idp101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-5791761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5807761639/16000000 : ℚ) by norm_num]
  exact coverp101101011
theorem coverp10110101 : Covers (-5791761639/32000000 : ℚ) vp10110101 := join_branches bp101101010 bp101101011
private noncomputable def vp1011010011_0 : Blocks := edgeBlocks% "full/vectors/1011010011-V-0000.bin"
noncomputable def vp1011010011 : Blocks := vp1011010011_0
theorem coverp1011010011 : Covers (-5783761639/8000000 : ℚ) vp1011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp1011010010_0 : Blocks := edgeBlocks% "full/vectors/1011010010-V-0000.bin"
noncomputable def vp1011010010 : Blocks := vp1011010010_0
theorem coverp1011010010 : Covers (-5775761639/8000000 : ℚ) vp1011010010 := cover_leaf (by decide +kernel)
private noncomputable def vp101101001_0 : Blocks := edgeBlocks% "full/vectors/101101001-V-0000.bin"
private noncomputable def vp101101001_1 : Blocks := edgeBlocks% "full/vectors/101101001-V-0001.bin"
noncomputable def vp101101001 : Blocks := (Blocks.join vp101101001_0 vp101101001_1)
private theorem bp1011010010 : Branch 0 (-5775761639/16000000 : ℚ) vp101101001 := by
  apply branch_left_normalized (c:=vp1011010010) (k:=0) (m:=124) (by decide +kernel)
  rw [show 2*(-5775761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5775761639/8000000 : ℚ) by norm_num]
  exact coverp1011010010
private noncomputable def ep1011010011_0 : Blocks := edgeBlocks% "full/vectors/1011010011-E-0000.bin"
private noncomputable def ep1011010011_1 : Blocks := edgeBlocks% "full/vectors/1011010011-E-0001.bin"
noncomputable def ep1011010011 : Blocks := (Blocks.join ep1011010011_0 ep1011010011_1)
private theorem idp1011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101101001.list =
    C ((2:ℤ)^275) * horner X vp1011010011.list + horner X ep1011010011.list := by
  exact edge_identity (B := (2:ℤ)^440) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011010011 : Branch 1 (-5775761639/16000000 : ℚ) vp101101001 := by
  apply branch_checked idp1011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-5775761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5783761639/8000000 : ℚ) by norm_num]
  exact coverp1011010011
theorem coverp101101001 : Covers (-5775761639/16000000 : ℚ) vp101101001 := join_branches bp1011010010 bp1011010011
private noncomputable def vp1011010001_0 : Blocks := edgeBlocks% "full/vectors/1011010001-V-0000.bin"
noncomputable def vp1011010001 : Blocks := vp1011010001_0
theorem coverp1011010001 : Covers (-5767761639/8000000 : ℚ) vp1011010001 := cover_leaf (by decide +kernel)
private noncomputable def vp1011010000_0 : Blocks := edgeBlocks% "full/vectors/1011010000-V-0000.bin"
noncomputable def vp1011010000 : Blocks := vp1011010000_0
theorem coverp1011010000 : Covers (-5759761639/8000000 : ℚ) vp1011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp101101000_0 : Blocks := edgeBlocks% "full/vectors/101101000-V-0000.bin"
private noncomputable def vp101101000_1 : Blocks := edgeBlocks% "full/vectors/101101000-V-0001.bin"
noncomputable def vp101101000 : Blocks := (Blocks.join vp101101000_0 vp101101000_1)
private theorem bp1011010000 : Branch 0 (-5759761639/16000000 : ℚ) vp101101000 := by
  apply branch_left_normalized (c:=vp1011010000) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-5759761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5759761639/8000000 : ℚ) by norm_num]
  exact coverp1011010000
private noncomputable def ep1011010001_0 : Blocks := edgeBlocks% "full/vectors/1011010001-E-0000.bin"
private noncomputable def ep1011010001_1 : Blocks := edgeBlocks% "full/vectors/1011010001-E-0001.bin"
noncomputable def ep1011010001 : Blocks := (Blocks.join ep1011010001_0 ep1011010001_1)
private theorem idp1011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101101000.list =
    C ((2:ℤ)^277) * horner X vp1011010001.list + horner X ep1011010001.list := by
  exact edge_identity (B := (2:ℤ)^442) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011010001 : Branch 1 (-5759761639/16000000 : ℚ) vp101101000 := by
  apply branch_checked idp1011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-5759761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5767761639/8000000 : ℚ) by norm_num]
  exact coverp1011010001
theorem coverp101101000 : Covers (-5759761639/16000000 : ℚ) vp101101000 := join_branches bp1011010000 bp1011010001
private noncomputable def vp10110100_0 : Blocks := edgeBlocks% "full/vectors/10110100-V-0000.bin"
private noncomputable def vp10110100_1 : Blocks := edgeBlocks% "full/vectors/10110100-V-0001.bin"
private noncomputable def vp10110100_2 : Blocks := edgeBlocks% "full/vectors/10110100-V-0002.bin"
private noncomputable def vp10110100_3 : Blocks := edgeBlocks% "full/vectors/10110100-V-0003.bin"
noncomputable def vp10110100 : Blocks := (Blocks.join (Blocks.join vp10110100_0 vp10110100_1) (Blocks.join vp10110100_2 vp10110100_3))
private theorem bp101101000 : Branch 0 (-5759761639/32000000 : ℚ) vp10110100 := by
  apply branch_left_normalized (c:=vp101101000) (k:=0) (m:=229) (by decide +kernel)
  rw [show 2*(-5759761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5759761639/16000000 : ℚ) by norm_num]
  exact coverp101101000
private noncomputable def ep101101001_0 : Blocks := edgeBlocks% "full/vectors/101101001-E-0000.bin"
private noncomputable def ep101101001_1 : Blocks := edgeBlocks% "full/vectors/101101001-E-0001.bin"
private noncomputable def ep101101001_2 : Blocks := edgeBlocks% "full/vectors/101101001-E-0002.bin"
private noncomputable def ep101101001_3 : Blocks := edgeBlocks% "full/vectors/101101001-E-0003.bin"
noncomputable def ep101101001 : Blocks := (Blocks.join (Blocks.join ep101101001_0 ep101101001_1) (Blocks.join ep101101001_2 ep101101001_3))
private theorem idp101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10110100.list =
    C ((2:ℤ)^529) * horner X vp101101001.list + horner X ep101101001.list := by
  exact edge_identity (B := (2:ℤ)^758) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101101001 : Branch 1 (-5759761639/32000000 : ℚ) vp10110100 := by
  apply branch_checked idp101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-5759761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5775761639/16000000 : ℚ) by norm_num]
  exact coverp101101001
theorem coverp10110100 : Covers (-5759761639/32000000 : ℚ) vp10110100 := join_branches bp101101000 bp101101001
private noncomputable def vp1011010_0 : Blocks := edgeBlocks% "full/vectors/1011010-V-0000.bin"
private noncomputable def vp1011010_1 : Blocks := edgeBlocks% "full/vectors/1011010-V-0001.bin"
private noncomputable def vp1011010_2 : Blocks := edgeBlocks% "full/vectors/1011010-V-0002.bin"
private noncomputable def vp1011010_3 : Blocks := edgeBlocks% "full/vectors/1011010-V-0003.bin"
private noncomputable def vp1011010_4 : Blocks := edgeBlocks% "full/vectors/1011010-V-0004.bin"
private noncomputable def vp1011010_5 : Blocks := edgeBlocks% "full/vectors/1011010-V-0005.bin"
private noncomputable def vp1011010_6 : Blocks := edgeBlocks% "full/vectors/1011010-V-0006.bin"
noncomputable def vp1011010 : Blocks := (Blocks.join (Blocks.join vp1011010_0 (Blocks.join vp1011010_1 vp1011010_2)) (Blocks.join (Blocks.join vp1011010_3 vp1011010_4) (Blocks.join vp1011010_5 vp1011010_6)))
private theorem bp10110100 : Branch 0 (-5759761639/64000000 : ℚ) vp1011010 := by
  apply branch_left_normalized (c:=vp10110100) (k:=0) (m:=435) (by decide +kernel)
  rw [show 2*(-5759761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5759761639/32000000 : ℚ) by norm_num]
  exact coverp10110100
private noncomputable def ep10110101_0 : Blocks := edgeBlocks% "full/vectors/10110101-E-0000.bin"
private noncomputable def ep10110101_1 : Blocks := edgeBlocks% "full/vectors/10110101-E-0001.bin"
private noncomputable def ep10110101_2 : Blocks := edgeBlocks% "full/vectors/10110101-E-0002.bin"
private noncomputable def ep10110101_3 : Blocks := edgeBlocks% "full/vectors/10110101-E-0003.bin"
private noncomputable def ep10110101_4 : Blocks := edgeBlocks% "full/vectors/10110101-E-0004.bin"
private noncomputable def ep10110101_5 : Blocks := edgeBlocks% "full/vectors/10110101-E-0005.bin"
private noncomputable def ep10110101_6 : Blocks := edgeBlocks% "full/vectors/10110101-E-0006.bin"
noncomputable def ep10110101 : Blocks := (Blocks.join (Blocks.join ep10110101_0 (Blocks.join ep10110101_1 ep10110101_2)) (Blocks.join (Blocks.join ep10110101_3 ep10110101_4) (Blocks.join ep10110101_5 ep10110101_6)))
private theorem idp10110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1011010.list =
    C ((2:ℤ)^1028) * horner X vp10110101.list + horner X ep10110101.list := by
  exact edge_identity (B := (2:ℤ)^1383) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10110101 : Branch 1 (-5759761639/64000000 : ℚ) vp1011010 := by
  apply branch_checked idp10110101 (by positivity) (by decide +kernel)
  rw [show 2*(-5759761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5791761639/32000000 : ℚ) by norm_num]
  exact coverp10110101
theorem coverp1011010 : Covers (-5759761639/64000000 : ℚ) vp1011010 := join_branches bp10110100 bp10110101
private noncomputable def vp101101_0 : Blocks := edgeBlocks% "full/vectors/101101-V-0000.bin"
private noncomputable def vp101101_1 : Blocks := edgeBlocks% "full/vectors/101101-V-0001.bin"
private noncomputable def vp101101_2 : Blocks := edgeBlocks% "full/vectors/101101-V-0002.bin"
private noncomputable def vp101101_3 : Blocks := edgeBlocks% "full/vectors/101101-V-0003.bin"
private noncomputable def vp101101_4 : Blocks := edgeBlocks% "full/vectors/101101-V-0004.bin"
private noncomputable def vp101101_5 : Blocks := edgeBlocks% "full/vectors/101101-V-0005.bin"
private noncomputable def vp101101_6 : Blocks := edgeBlocks% "full/vectors/101101-V-0006.bin"
private noncomputable def vp101101_7 : Blocks := edgeBlocks% "full/vectors/101101-V-0007.bin"
private noncomputable def vp101101_8 : Blocks := edgeBlocks% "full/vectors/101101-V-0008.bin"
private noncomputable def vp101101_9 : Blocks := edgeBlocks% "full/vectors/101101-V-0009.bin"
private noncomputable def vp101101_10 : Blocks := edgeBlocks% "full/vectors/101101-V-0010.bin"
private noncomputable def vp101101_11 : Blocks := edgeBlocks% "full/vectors/101101-V-0011.bin"
private noncomputable def vp101101_12 : Blocks := edgeBlocks% "full/vectors/101101-V-0012.bin"
noncomputable def vp101101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp101101_0 (Blocks.join vp101101_1 vp101101_2)) (Blocks.join vp101101_3 (Blocks.join vp101101_4 vp101101_5))) (Blocks.join (Blocks.join vp101101_6 (Blocks.join vp101101_7 vp101101_8)) (Blocks.join (Blocks.join vp101101_9 vp101101_10) (Blocks.join vp101101_11 vp101101_12))))
private theorem bp1011010 : Branch 0 (-5759761639/128000000 : ℚ) vp101101 := by
  apply branch_left_normalized (c:=vp1011010) (k:=0) (m:=842) (by decide +kernel)
  rw [show 2*(-5759761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-5759761639/64000000 : ℚ) by norm_num]
  exact coverp1011010
private noncomputable def ep1011011_0 : Blocks := edgeBlocks% "full/vectors/1011011-E-0000.bin"
private noncomputable def ep1011011_1 : Blocks := edgeBlocks% "full/vectors/1011011-E-0001.bin"
private noncomputable def ep1011011_2 : Blocks := edgeBlocks% "full/vectors/1011011-E-0002.bin"
private noncomputable def ep1011011_3 : Blocks := edgeBlocks% "full/vectors/1011011-E-0003.bin"
private noncomputable def ep1011011_4 : Blocks := edgeBlocks% "full/vectors/1011011-E-0004.bin"
private noncomputable def ep1011011_5 : Blocks := edgeBlocks% "full/vectors/1011011-E-0005.bin"
private noncomputable def ep1011011_6 : Blocks := edgeBlocks% "full/vectors/1011011-E-0006.bin"
private noncomputable def ep1011011_7 : Blocks := edgeBlocks% "full/vectors/1011011-E-0007.bin"
private noncomputable def ep1011011_8 : Blocks := edgeBlocks% "full/vectors/1011011-E-0008.bin"
private noncomputable def ep1011011_9 : Blocks := edgeBlocks% "full/vectors/1011011-E-0009.bin"
private noncomputable def ep1011011_10 : Blocks := edgeBlocks% "full/vectors/1011011-E-0010.bin"
private noncomputable def ep1011011_11 : Blocks := edgeBlocks% "full/vectors/1011011-E-0011.bin"
private noncomputable def ep1011011_12 : Blocks := edgeBlocks% "full/vectors/1011011-E-0012.bin"
noncomputable def ep1011011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1011011_0 (Blocks.join ep1011011_1 ep1011011_2)) (Blocks.join ep1011011_3 (Blocks.join ep1011011_4 ep1011011_5))) (Blocks.join (Blocks.join ep1011011_6 (Blocks.join ep1011011_7 ep1011011_8)) (Blocks.join (Blocks.join ep1011011_9 ep1011011_10) (Blocks.join ep1011011_11 ep1011011_12))))
private theorem idp1011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101101.list =
    C ((2:ℤ)^2011) * horner X vp1011011.list + horner X ep1011011.list := by
  exact edge_identity (B := (2:ℤ)^2616) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011011 : Branch 1 (-5759761639/128000000 : ℚ) vp101101 := by
  apply branch_checked idp1011011 (by positivity) (by decide +kernel)
  rw [show 2*(-5759761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-5823761639/64000000 : ℚ) by norm_num]
  exact coverp1011011
theorem coverp101101 : Covers (-5759761639/128000000 : ℚ) vp101101 := join_branches bp1011010 bp1011011
private noncomputable def vp1011001111_0 : Blocks := edgeBlocks% "full/vectors/1011001111-V-0000.bin"
noncomputable def vp1011001111 : Blocks := vp1011001111_0
theorem coverp1011001111 : Covers (-5751761639/8000000 : ℚ) vp1011001111 := cover_leaf (by decide +kernel)
private noncomputable def vp1011001110_0 : Blocks := edgeBlocks% "full/vectors/1011001110-V-0000.bin"
noncomputable def vp1011001110 : Blocks := vp1011001110_0
theorem coverp1011001110 : Covers (-5743761639/8000000 : ℚ) vp1011001110 := cover_leaf (by decide +kernel)
private noncomputable def vp101100111_0 : Blocks := edgeBlocks% "full/vectors/101100111-V-0000.bin"
private noncomputable def vp101100111_1 : Blocks := edgeBlocks% "full/vectors/101100111-V-0001.bin"
noncomputable def vp101100111 : Blocks := (Blocks.join vp101100111_0 vp101100111_1)
private theorem bp1011001110 : Branch 0 (-5743761639/16000000 : ℚ) vp101100111 := by
  apply branch_left_normalized (c:=vp1011001110) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-5743761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5743761639/8000000 : ℚ) by norm_num]
  exact coverp1011001110
private noncomputable def ep1011001111_0 : Blocks := edgeBlocks% "full/vectors/1011001111-E-0000.bin"
private noncomputable def ep1011001111_1 : Blocks := edgeBlocks% "full/vectors/1011001111-E-0001.bin"
noncomputable def ep1011001111 : Blocks := (Blocks.join ep1011001111_0 ep1011001111_1)
private theorem idp1011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101100111.list =
    C ((2:ℤ)^276) * horner X vp1011001111.list + horner X ep1011001111.list := by
  exact edge_identity (B := (2:ℤ)^442) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011001111 : Branch 1 (-5743761639/16000000 : ℚ) vp101100111 := by
  apply branch_checked idp1011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-5743761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5751761639/8000000 : ℚ) by norm_num]
  exact coverp1011001111
theorem coverp101100111 : Covers (-5743761639/16000000 : ℚ) vp101100111 := join_branches bp1011001110 bp1011001111
private noncomputable def vp1011001101_0 : Blocks := edgeBlocks% "full/vectors/1011001101-V-0000.bin"
noncomputable def vp1011001101 : Blocks := vp1011001101_0
theorem coverp1011001101 : Covers (-5735761639/8000000 : ℚ) vp1011001101 := cover_leaf (by decide +kernel)
private noncomputable def vp1011001100_0 : Blocks := edgeBlocks% "full/vectors/1011001100-V-0000.bin"
noncomputable def vp1011001100 : Blocks := vp1011001100_0
theorem coverp1011001100 : Covers (-5727761639/8000000 : ℚ) vp1011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp101100110_0 : Blocks := edgeBlocks% "full/vectors/101100110-V-0000.bin"
private noncomputable def vp101100110_1 : Blocks := edgeBlocks% "full/vectors/101100110-V-0001.bin"
noncomputable def vp101100110 : Blocks := (Blocks.join vp101100110_0 vp101100110_1)
private theorem bp1011001100 : Branch 0 (-5727761639/16000000 : ℚ) vp101100110 := by
  apply branch_left_normalized (c:=vp1011001100) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-5727761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5727761639/8000000 : ℚ) by norm_num]
  exact coverp1011001100
private noncomputable def ep1011001101_0 : Blocks := edgeBlocks% "full/vectors/1011001101-E-0000.bin"
private noncomputable def ep1011001101_1 : Blocks := edgeBlocks% "full/vectors/1011001101-E-0001.bin"
noncomputable def ep1011001101 : Blocks := (Blocks.join ep1011001101_0 ep1011001101_1)
private theorem idp1011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101100110.list =
    C ((2:ℤ)^277) * horner X vp1011001101.list + horner X ep1011001101.list := by
  exact edge_identity (B := (2:ℤ)^443) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011001101 : Branch 1 (-5727761639/16000000 : ℚ) vp101100110 := by
  apply branch_checked idp1011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-5727761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5735761639/8000000 : ℚ) by norm_num]
  exact coverp1011001101
theorem coverp101100110 : Covers (-5727761639/16000000 : ℚ) vp101100110 := join_branches bp1011001100 bp1011001101
private noncomputable def vp10110011_0 : Blocks := edgeBlocks% "full/vectors/10110011-V-0000.bin"
private noncomputable def vp10110011_1 : Blocks := edgeBlocks% "full/vectors/10110011-V-0001.bin"
private noncomputable def vp10110011_2 : Blocks := edgeBlocks% "full/vectors/10110011-V-0002.bin"
private noncomputable def vp10110011_3 : Blocks := edgeBlocks% "full/vectors/10110011-V-0003.bin"
noncomputable def vp10110011 : Blocks := (Blocks.join (Blocks.join vp10110011_0 vp10110011_1) (Blocks.join vp10110011_2 vp10110011_3))
private theorem bp101100110 : Branch 0 (-5727761639/32000000 : ℚ) vp10110011 := by
  apply branch_left_normalized (c:=vp101100110) (k:=0) (m:=230) (by decide +kernel)
  rw [show 2*(-5727761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5727761639/16000000 : ℚ) by norm_num]
  exact coverp101100110
private noncomputable def ep101100111_0 : Blocks := edgeBlocks% "full/vectors/101100111-E-0000.bin"
private noncomputable def ep101100111_1 : Blocks := edgeBlocks% "full/vectors/101100111-E-0001.bin"
private noncomputable def ep101100111_2 : Blocks := edgeBlocks% "full/vectors/101100111-E-0002.bin"
private noncomputable def ep101100111_3 : Blocks := edgeBlocks% "full/vectors/101100111-E-0003.bin"
noncomputable def ep101100111 : Blocks := (Blocks.join (Blocks.join ep101100111_0 ep101100111_1) (Blocks.join ep101100111_2 ep101100111_3))
private theorem idp101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10110011.list =
    C ((2:ℤ)^529) * horner X vp101100111.list + horner X ep101100111.list := by
  exact edge_identity (B := (2:ℤ)^759) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101100111 : Branch 1 (-5727761639/32000000 : ℚ) vp10110011 := by
  apply branch_checked idp101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-5727761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5743761639/16000000 : ℚ) by norm_num]
  exact coverp101100111
theorem coverp10110011 : Covers (-5727761639/32000000 : ℚ) vp10110011 := join_branches bp101100110 bp101100111
private noncomputable def vp1011001011_0 : Blocks := edgeBlocks% "full/vectors/1011001011-V-0000.bin"
noncomputable def vp1011001011 : Blocks := vp1011001011_0
theorem coverp1011001011 : Covers (-5719761639/8000000 : ℚ) vp1011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp1011001010_0 : Blocks := edgeBlocks% "full/vectors/1011001010-V-0000.bin"
noncomputable def vp1011001010 : Blocks := vp1011001010_0
theorem coverp1011001010 : Covers (-5711761639/8000000 : ℚ) vp1011001010 := cover_leaf (by decide +kernel)
private noncomputable def vp101100101_0 : Blocks := edgeBlocks% "full/vectors/101100101-V-0000.bin"
private noncomputable def vp101100101_1 : Blocks := edgeBlocks% "full/vectors/101100101-V-0001.bin"
noncomputable def vp101100101 : Blocks := (Blocks.join vp101100101_0 vp101100101_1)
private theorem bp1011001010 : Branch 0 (-5711761639/16000000 : ℚ) vp101100101 := by
  apply branch_left_normalized (c:=vp1011001010) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-5711761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5711761639/8000000 : ℚ) by norm_num]
  exact coverp1011001010
private noncomputable def ep1011001011_0 : Blocks := edgeBlocks% "full/vectors/1011001011-E-0000.bin"
private noncomputable def ep1011001011_1 : Blocks := edgeBlocks% "full/vectors/1011001011-E-0001.bin"
noncomputable def ep1011001011 : Blocks := (Blocks.join ep1011001011_0 ep1011001011_1)
private theorem idp1011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101100101.list =
    C ((2:ℤ)^278) * horner X vp1011001011.list + horner X ep1011001011.list := by
  exact edge_identity (B := (2:ℤ)^443) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011001011 : Branch 1 (-5711761639/16000000 : ℚ) vp101100101 := by
  apply branch_checked idp1011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-5711761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5719761639/8000000 : ℚ) by norm_num]
  exact coverp1011001011
theorem coverp101100101 : Covers (-5711761639/16000000 : ℚ) vp101100101 := join_branches bp1011001010 bp1011001011
private noncomputable def vp1011001001_0 : Blocks := edgeBlocks% "full/vectors/1011001001-V-0000.bin"
noncomputable def vp1011001001 : Blocks := vp1011001001_0
theorem coverp1011001001 : Covers (-5703761639/8000000 : ℚ) vp1011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp1011001000_0 : Blocks := edgeBlocks% "full/vectors/1011001000-V-0000.bin"
noncomputable def vp1011001000 : Blocks := vp1011001000_0
theorem coverp1011001000 : Covers (-5695761639/8000000 : ℚ) vp1011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp101100100_0 : Blocks := edgeBlocks% "full/vectors/101100100-V-0000.bin"
private noncomputable def vp101100100_1 : Blocks := edgeBlocks% "full/vectors/101100100-V-0001.bin"
noncomputable def vp101100100 : Blocks := (Blocks.join vp101100100_0 vp101100100_1)
private theorem bp1011001000 : Branch 0 (-5695761639/16000000 : ℚ) vp101100100 := by
  apply branch_left_normalized (c:=vp1011001000) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-5695761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5695761639/8000000 : ℚ) by norm_num]
  exact coverp1011001000
private noncomputable def ep1011001001_0 : Blocks := edgeBlocks% "full/vectors/1011001001-E-0000.bin"
private noncomputable def ep1011001001_1 : Blocks := edgeBlocks% "full/vectors/1011001001-E-0001.bin"
noncomputable def ep1011001001 : Blocks := (Blocks.join ep1011001001_0 ep1011001001_1)
private theorem idp1011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101100100.list =
    C ((2:ℤ)^278) * horner X vp1011001001.list + horner X ep1011001001.list := by
  exact edge_identity (B := (2:ℤ)^444) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011001001 : Branch 1 (-5695761639/16000000 : ℚ) vp101100100 := by
  apply branch_checked idp1011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-5695761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5703761639/8000000 : ℚ) by norm_num]
  exact coverp1011001001
theorem coverp101100100 : Covers (-5695761639/16000000 : ℚ) vp101100100 := join_branches bp1011001000 bp1011001001
private noncomputable def vp10110010_0 : Blocks := edgeBlocks% "full/vectors/10110010-V-0000.bin"
private noncomputable def vp10110010_1 : Blocks := edgeBlocks% "full/vectors/10110010-V-0001.bin"
private noncomputable def vp10110010_2 : Blocks := edgeBlocks% "full/vectors/10110010-V-0002.bin"
private noncomputable def vp10110010_3 : Blocks := edgeBlocks% "full/vectors/10110010-V-0003.bin"
noncomputable def vp10110010 : Blocks := (Blocks.join (Blocks.join vp10110010_0 vp10110010_1) (Blocks.join vp10110010_2 vp10110010_3))
private theorem bp101100100 : Branch 0 (-5695761639/32000000 : ℚ) vp10110010 := by
  apply branch_left_normalized (c:=vp101100100) (k:=0) (m:=231) (by decide +kernel)
  rw [show 2*(-5695761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5695761639/16000000 : ℚ) by norm_num]
  exact coverp101100100
private noncomputable def ep101100101_0 : Blocks := edgeBlocks% "full/vectors/101100101-E-0000.bin"
private noncomputable def ep101100101_1 : Blocks := edgeBlocks% "full/vectors/101100101-E-0001.bin"
private noncomputable def ep101100101_2 : Blocks := edgeBlocks% "full/vectors/101100101-E-0002.bin"
private noncomputable def ep101100101_3 : Blocks := edgeBlocks% "full/vectors/101100101-E-0003.bin"
noncomputable def ep101100101 : Blocks := (Blocks.join (Blocks.join ep101100101_0 ep101100101_1) (Blocks.join ep101100101_2 ep101100101_3))
private theorem idp101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10110010.list =
    C ((2:ℤ)^530) * horner X vp101100101.list + horner X ep101100101.list := by
  exact edge_identity (B := (2:ℤ)^761) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101100101 : Branch 1 (-5695761639/32000000 : ℚ) vp10110010 := by
  apply branch_checked idp101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-5695761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5711761639/16000000 : ℚ) by norm_num]
  exact coverp101100101
theorem coverp10110010 : Covers (-5695761639/32000000 : ℚ) vp10110010 := join_branches bp101100100 bp101100101
private noncomputable def vp1011001_0 : Blocks := edgeBlocks% "full/vectors/1011001-V-0000.bin"
private noncomputable def vp1011001_1 : Blocks := edgeBlocks% "full/vectors/1011001-V-0001.bin"
private noncomputable def vp1011001_2 : Blocks := edgeBlocks% "full/vectors/1011001-V-0002.bin"
private noncomputable def vp1011001_3 : Blocks := edgeBlocks% "full/vectors/1011001-V-0003.bin"
private noncomputable def vp1011001_4 : Blocks := edgeBlocks% "full/vectors/1011001-V-0004.bin"
private noncomputable def vp1011001_5 : Blocks := edgeBlocks% "full/vectors/1011001-V-0005.bin"
private noncomputable def vp1011001_6 : Blocks := edgeBlocks% "full/vectors/1011001-V-0006.bin"
noncomputable def vp1011001 : Blocks := (Blocks.join (Blocks.join vp1011001_0 (Blocks.join vp1011001_1 vp1011001_2)) (Blocks.join (Blocks.join vp1011001_3 vp1011001_4) (Blocks.join vp1011001_5 vp1011001_6)))
private theorem bp10110010 : Branch 0 (-5695761639/64000000 : ℚ) vp1011001 := by
  apply branch_left_normalized (c:=vp10110010) (k:=0) (m:=437) (by decide +kernel)
  rw [show 2*(-5695761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5695761639/32000000 : ℚ) by norm_num]
  exact coverp10110010
private noncomputable def ep10110011_0 : Blocks := edgeBlocks% "full/vectors/10110011-E-0000.bin"
private noncomputable def ep10110011_1 : Blocks := edgeBlocks% "full/vectors/10110011-E-0001.bin"
private noncomputable def ep10110011_2 : Blocks := edgeBlocks% "full/vectors/10110011-E-0002.bin"
private noncomputable def ep10110011_3 : Blocks := edgeBlocks% "full/vectors/10110011-E-0003.bin"
private noncomputable def ep10110011_4 : Blocks := edgeBlocks% "full/vectors/10110011-E-0004.bin"
private noncomputable def ep10110011_5 : Blocks := edgeBlocks% "full/vectors/10110011-E-0005.bin"
private noncomputable def ep10110011_6 : Blocks := edgeBlocks% "full/vectors/10110011-E-0006.bin"
noncomputable def ep10110011 : Blocks := (Blocks.join (Blocks.join ep10110011_0 (Blocks.join ep10110011_1 ep10110011_2)) (Blocks.join (Blocks.join ep10110011_3 ep10110011_4) (Blocks.join ep10110011_5 ep10110011_6)))
private theorem idp10110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1011001.list =
    C ((2:ℤ)^1033) * horner X vp10110011.list + horner X ep10110011.list := by
  exact edge_identity (B := (2:ℤ)^1391) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10110011 : Branch 1 (-5695761639/64000000 : ℚ) vp1011001 := by
  apply branch_checked idp10110011 (by positivity) (by decide +kernel)
  rw [show 2*(-5695761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5727761639/32000000 : ℚ) by norm_num]
  exact coverp10110011
theorem coverp1011001 : Covers (-5695761639/64000000 : ℚ) vp1011001 := join_branches bp10110010 bp10110011
private noncomputable def vp1011000111_0 : Blocks := edgeBlocks% "full/vectors/1011000111-V-0000.bin"
noncomputable def vp1011000111 : Blocks := vp1011000111_0
theorem coverp1011000111 : Covers (-5687761639/8000000 : ℚ) vp1011000111 := cover_leaf (by decide +kernel)
private noncomputable def vp1011000110_0 : Blocks := edgeBlocks% "full/vectors/1011000110-V-0000.bin"
noncomputable def vp1011000110 : Blocks := vp1011000110_0
theorem coverp1011000110 : Covers (-5679761639/8000000 : ℚ) vp1011000110 := cover_leaf (by decide +kernel)
private noncomputable def vp101100011_0 : Blocks := edgeBlocks% "full/vectors/101100011-V-0000.bin"
private noncomputable def vp101100011_1 : Blocks := edgeBlocks% "full/vectors/101100011-V-0001.bin"
noncomputable def vp101100011 : Blocks := (Blocks.join vp101100011_0 vp101100011_1)
private theorem bp1011000110 : Branch 0 (-5679761639/16000000 : ℚ) vp101100011 := by
  apply branch_left_normalized (c:=vp1011000110) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-5679761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5679761639/8000000 : ℚ) by norm_num]
  exact coverp1011000110
private noncomputable def ep1011000111_0 : Blocks := edgeBlocks% "full/vectors/1011000111-E-0000.bin"
private noncomputable def ep1011000111_1 : Blocks := edgeBlocks% "full/vectors/1011000111-E-0001.bin"
noncomputable def ep1011000111 : Blocks := (Blocks.join ep1011000111_0 ep1011000111_1)
private theorem idp1011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101100011.list =
    C ((2:ℤ)^277) * horner X vp1011000111.list + horner X ep1011000111.list := by
  exact edge_identity (B := (2:ℤ)^443) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011000111 : Branch 1 (-5679761639/16000000 : ℚ) vp101100011 := by
  apply branch_checked idp1011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-5679761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5687761639/8000000 : ℚ) by norm_num]
  exact coverp1011000111
theorem coverp101100011 : Covers (-5679761639/16000000 : ℚ) vp101100011 := join_branches bp1011000110 bp1011000111
private noncomputable def vp1011000101_0 : Blocks := edgeBlocks% "full/vectors/1011000101-V-0000.bin"
noncomputable def vp1011000101 : Blocks := vp1011000101_0
theorem coverp1011000101 : Covers (-5671761639/8000000 : ℚ) vp1011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp1011000100_0 : Blocks := edgeBlocks% "full/vectors/1011000100-V-0000.bin"
noncomputable def vp1011000100 : Blocks := vp1011000100_0
theorem coverp1011000100 : Covers (-5663761639/8000000 : ℚ) vp1011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp101100010_0 : Blocks := edgeBlocks% "full/vectors/101100010-V-0000.bin"
private noncomputable def vp101100010_1 : Blocks := edgeBlocks% "full/vectors/101100010-V-0001.bin"
noncomputable def vp101100010 : Blocks := (Blocks.join vp101100010_0 vp101100010_1)
private theorem bp1011000100 : Branch 0 (-5663761639/16000000 : ℚ) vp101100010 := by
  apply branch_left_normalized (c:=vp1011000100) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-5663761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5663761639/8000000 : ℚ) by norm_num]
  exact coverp1011000100
private noncomputable def ep1011000101_0 : Blocks := edgeBlocks% "full/vectors/1011000101-E-0000.bin"
private noncomputable def ep1011000101_1 : Blocks := edgeBlocks% "full/vectors/1011000101-E-0001.bin"
noncomputable def ep1011000101 : Blocks := (Blocks.join ep1011000101_0 ep1011000101_1)
private theorem idp1011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101100010.list =
    C ((2:ℤ)^279) * horner X vp1011000101.list + horner X ep1011000101.list := by
  exact edge_identity (B := (2:ℤ)^445) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011000101 : Branch 1 (-5663761639/16000000 : ℚ) vp101100010 := by
  apply branch_checked idp1011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-5663761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5671761639/8000000 : ℚ) by norm_num]
  exact coverp1011000101
theorem coverp101100010 : Covers (-5663761639/16000000 : ℚ) vp101100010 := join_branches bp1011000100 bp1011000101
private noncomputable def vp10110001_0 : Blocks := edgeBlocks% "full/vectors/10110001-V-0000.bin"
private noncomputable def vp10110001_1 : Blocks := edgeBlocks% "full/vectors/10110001-V-0001.bin"
private noncomputable def vp10110001_2 : Blocks := edgeBlocks% "full/vectors/10110001-V-0002.bin"
private noncomputable def vp10110001_3 : Blocks := edgeBlocks% "full/vectors/10110001-V-0003.bin"
noncomputable def vp10110001 : Blocks := (Blocks.join (Blocks.join vp10110001_0 vp10110001_1) (Blocks.join vp10110001_2 vp10110001_3))
private theorem bp101100010 : Branch 0 (-5663761639/32000000 : ℚ) vp10110001 := by
  apply branch_left_normalized (c:=vp101100010) (k:=0) (m:=231) (by decide +kernel)
  rw [show 2*(-5663761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5663761639/16000000 : ℚ) by norm_num]
  exact coverp101100010
private noncomputable def ep101100011_0 : Blocks := edgeBlocks% "full/vectors/101100011-E-0000.bin"
private noncomputable def ep101100011_1 : Blocks := edgeBlocks% "full/vectors/101100011-E-0001.bin"
private noncomputable def ep101100011_2 : Blocks := edgeBlocks% "full/vectors/101100011-E-0002.bin"
private noncomputable def ep101100011_3 : Blocks := edgeBlocks% "full/vectors/101100011-E-0003.bin"
noncomputable def ep101100011 : Blocks := (Blocks.join (Blocks.join ep101100011_0 ep101100011_1) (Blocks.join ep101100011_2 ep101100011_3))
private theorem idp101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10110001.list =
    C ((2:ℤ)^533) * horner X vp101100011.list + horner X ep101100011.list := by
  exact edge_identity (B := (2:ℤ)^764) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101100011 : Branch 1 (-5663761639/32000000 : ℚ) vp10110001 := by
  apply branch_checked idp101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-5663761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5679761639/16000000 : ℚ) by norm_num]
  exact coverp101100011
theorem coverp10110001 : Covers (-5663761639/32000000 : ℚ) vp10110001 := join_branches bp101100010 bp101100011
private noncomputable def vp1011000011_0 : Blocks := edgeBlocks% "full/vectors/1011000011-V-0000.bin"
noncomputable def vp1011000011 : Blocks := vp1011000011_0
theorem coverp1011000011 : Covers (-5655761639/8000000 : ℚ) vp1011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp1011000010_0 : Blocks := edgeBlocks% "full/vectors/1011000010-V-0000.bin"
noncomputable def vp1011000010 : Blocks := vp1011000010_0
theorem coverp1011000010 : Covers (-5647761639/8000000 : ℚ) vp1011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp101100001_0 : Blocks := edgeBlocks% "full/vectors/101100001-V-0000.bin"
private noncomputable def vp101100001_1 : Blocks := edgeBlocks% "full/vectors/101100001-V-0001.bin"
noncomputable def vp101100001 : Blocks := (Blocks.join vp101100001_0 vp101100001_1)
private theorem bp1011000010 : Branch 0 (-5647761639/16000000 : ℚ) vp101100001 := by
  apply branch_left_normalized (c:=vp1011000010) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-5647761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5647761639/8000000 : ℚ) by norm_num]
  exact coverp1011000010
private noncomputable def ep1011000011_0 : Blocks := edgeBlocks% "full/vectors/1011000011-E-0000.bin"
private noncomputable def ep1011000011_1 : Blocks := edgeBlocks% "full/vectors/1011000011-E-0001.bin"
noncomputable def ep1011000011 : Blocks := (Blocks.join ep1011000011_0 ep1011000011_1)
private theorem idp1011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101100001.list =
    C ((2:ℤ)^279) * horner X vp1011000011.list + horner X ep1011000011.list := by
  exact edge_identity (B := (2:ℤ)^446) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011000011 : Branch 1 (-5647761639/16000000 : ℚ) vp101100001 := by
  apply branch_checked idp1011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-5647761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5655761639/8000000 : ℚ) by norm_num]
  exact coverp1011000011
theorem coverp101100001 : Covers (-5647761639/16000000 : ℚ) vp101100001 := join_branches bp1011000010 bp1011000011
private noncomputable def vp1011000001_0 : Blocks := edgeBlocks% "full/vectors/1011000001-V-0000.bin"
noncomputable def vp1011000001 : Blocks := vp1011000001_0
theorem coverp1011000001 : Covers (-5639761639/8000000 : ℚ) vp1011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp1011000000_0 : Blocks := edgeBlocks% "full/vectors/1011000000-V-0000.bin"
noncomputable def vp1011000000 : Blocks := vp1011000000_0
theorem coverp1011000000 : Covers (-5631761639/8000000 : ℚ) vp1011000000 := cover_leaf (by decide +kernel)
private noncomputable def vp101100000_0 : Blocks := edgeBlocks% "full/vectors/101100000-V-0000.bin"
private noncomputable def vp101100000_1 : Blocks := edgeBlocks% "full/vectors/101100000-V-0001.bin"
noncomputable def vp101100000 : Blocks := (Blocks.join vp101100000_0 vp101100000_1)
private theorem bp1011000000 : Branch 0 (-5631761639/16000000 : ℚ) vp101100000 := by
  apply branch_left_normalized (c:=vp1011000000) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-5631761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-5631761639/8000000 : ℚ) by norm_num]
  exact coverp1011000000
private noncomputable def ep1011000001_0 : Blocks := edgeBlocks% "full/vectors/1011000001-E-0000.bin"
private noncomputable def ep1011000001_1 : Blocks := edgeBlocks% "full/vectors/1011000001-E-0001.bin"
noncomputable def ep1011000001 : Blocks := (Blocks.join ep1011000001_0 ep1011000001_1)
private theorem idp1011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101100000.list =
    C ((2:ℤ)^278) * horner X vp1011000001.list + horner X ep1011000001.list := by
  exact edge_identity (B := (2:ℤ)^445) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011000001 : Branch 1 (-5631761639/16000000 : ℚ) vp101100000 := by
  apply branch_checked idp1011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-5631761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-5639761639/8000000 : ℚ) by norm_num]
  exact coverp1011000001
theorem coverp101100000 : Covers (-5631761639/16000000 : ℚ) vp101100000 := join_branches bp1011000000 bp1011000001
private noncomputable def vp10110000_0 : Blocks := edgeBlocks% "full/vectors/10110000-V-0000.bin"
private noncomputable def vp10110000_1 : Blocks := edgeBlocks% "full/vectors/10110000-V-0001.bin"
private noncomputable def vp10110000_2 : Blocks := edgeBlocks% "full/vectors/10110000-V-0002.bin"
private noncomputable def vp10110000_3 : Blocks := edgeBlocks% "full/vectors/10110000-V-0003.bin"
noncomputable def vp10110000 : Blocks := (Blocks.join (Blocks.join vp10110000_0 vp10110000_1) (Blocks.join vp10110000_2 vp10110000_3))
private theorem bp101100000 : Branch 0 (-5631761639/32000000 : ℚ) vp10110000 := by
  apply branch_left_normalized (c:=vp101100000) (k:=0) (m:=231) (by decide +kernel)
  rw [show 2*(-5631761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-5631761639/16000000 : ℚ) by norm_num]
  exact coverp101100000
private noncomputable def ep101100001_0 : Blocks := edgeBlocks% "full/vectors/101100001-E-0000.bin"
private noncomputable def ep101100001_1 : Blocks := edgeBlocks% "full/vectors/101100001-E-0001.bin"
private noncomputable def ep101100001_2 : Blocks := edgeBlocks% "full/vectors/101100001-E-0002.bin"
private noncomputable def ep101100001_3 : Blocks := edgeBlocks% "full/vectors/101100001-E-0003.bin"
noncomputable def ep101100001 : Blocks := (Blocks.join (Blocks.join ep101100001_0 ep101100001_1) (Blocks.join ep101100001_2 ep101100001_3))
private theorem idp101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10110000.list =
    C ((2:ℤ)^532) * horner X vp101100001.list + horner X ep101100001.list := by
  exact edge_identity (B := (2:ℤ)^764) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp101100001 : Branch 1 (-5631761639/32000000 : ℚ) vp10110000 := by
  apply branch_checked idp101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-5631761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-5647761639/16000000 : ℚ) by norm_num]
  exact coverp101100001
theorem coverp10110000 : Covers (-5631761639/32000000 : ℚ) vp10110000 := join_branches bp101100000 bp101100001
private noncomputable def vp1011000_0 : Blocks := edgeBlocks% "full/vectors/1011000-V-0000.bin"
private noncomputable def vp1011000_1 : Blocks := edgeBlocks% "full/vectors/1011000-V-0001.bin"
private noncomputable def vp1011000_2 : Blocks := edgeBlocks% "full/vectors/1011000-V-0002.bin"
private noncomputable def vp1011000_3 : Blocks := edgeBlocks% "full/vectors/1011000-V-0003.bin"
private noncomputable def vp1011000_4 : Blocks := edgeBlocks% "full/vectors/1011000-V-0004.bin"
private noncomputable def vp1011000_5 : Blocks := edgeBlocks% "full/vectors/1011000-V-0005.bin"
private noncomputable def vp1011000_6 : Blocks := edgeBlocks% "full/vectors/1011000-V-0006.bin"
noncomputable def vp1011000 : Blocks := (Blocks.join (Blocks.join vp1011000_0 (Blocks.join vp1011000_1 vp1011000_2)) (Blocks.join (Blocks.join vp1011000_3 vp1011000_4) (Blocks.join vp1011000_5 vp1011000_6)))
private theorem bp10110000 : Branch 0 (-5631761639/64000000 : ℚ) vp1011000 := by
  apply branch_left_normalized (c:=vp10110000) (k:=0) (m:=439) (by decide +kernel)
  rw [show 2*(-5631761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-5631761639/32000000 : ℚ) by norm_num]
  exact coverp10110000
private noncomputable def ep10110001_0 : Blocks := edgeBlocks% "full/vectors/10110001-E-0000.bin"
private noncomputable def ep10110001_1 : Blocks := edgeBlocks% "full/vectors/10110001-E-0001.bin"
private noncomputable def ep10110001_2 : Blocks := edgeBlocks% "full/vectors/10110001-E-0002.bin"
private noncomputable def ep10110001_3 : Blocks := edgeBlocks% "full/vectors/10110001-E-0003.bin"
private noncomputable def ep10110001_4 : Blocks := edgeBlocks% "full/vectors/10110001-E-0004.bin"
private noncomputable def ep10110001_5 : Blocks := edgeBlocks% "full/vectors/10110001-E-0005.bin"
private noncomputable def ep10110001_6 : Blocks := edgeBlocks% "full/vectors/10110001-E-0006.bin"
noncomputable def ep10110001 : Blocks := (Blocks.join (Blocks.join ep10110001_0 (Blocks.join ep10110001_1 ep10110001_2)) (Blocks.join (Blocks.join ep10110001_3 ep10110001_4) (Blocks.join ep10110001_5 ep10110001_6)))
private theorem idp10110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1011000.list =
    C ((2:ℤ)^1036) * horner X vp10110001.list + horner X ep10110001.list := by
  exact edge_identity (B := (2:ℤ)^1397) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10110001 : Branch 1 (-5631761639/64000000 : ℚ) vp1011000 := by
  apply branch_checked idp10110001 (by positivity) (by decide +kernel)
  rw [show 2*(-5631761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-5663761639/32000000 : ℚ) by norm_num]
  exact coverp10110001
theorem coverp1011000 : Covers (-5631761639/64000000 : ℚ) vp1011000 := join_branches bp10110000 bp10110001
private noncomputable def vp101100_0 : Blocks := edgeBlocks% "full/vectors/101100-V-0000.bin"
private noncomputable def vp101100_1 : Blocks := edgeBlocks% "full/vectors/101100-V-0001.bin"
private noncomputable def vp101100_2 : Blocks := edgeBlocks% "full/vectors/101100-V-0002.bin"
private noncomputable def vp101100_3 : Blocks := edgeBlocks% "full/vectors/101100-V-0003.bin"
private noncomputable def vp101100_4 : Blocks := edgeBlocks% "full/vectors/101100-V-0004.bin"
private noncomputable def vp101100_5 : Blocks := edgeBlocks% "full/vectors/101100-V-0005.bin"
private noncomputable def vp101100_6 : Blocks := edgeBlocks% "full/vectors/101100-V-0006.bin"
private noncomputable def vp101100_7 : Blocks := edgeBlocks% "full/vectors/101100-V-0007.bin"
private noncomputable def vp101100_8 : Blocks := edgeBlocks% "full/vectors/101100-V-0008.bin"
private noncomputable def vp101100_9 : Blocks := edgeBlocks% "full/vectors/101100-V-0009.bin"
private noncomputable def vp101100_10 : Blocks := edgeBlocks% "full/vectors/101100-V-0010.bin"
private noncomputable def vp101100_11 : Blocks := edgeBlocks% "full/vectors/101100-V-0011.bin"
private noncomputable def vp101100_12 : Blocks := edgeBlocks% "full/vectors/101100-V-0012.bin"
noncomputable def vp101100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp101100_0 (Blocks.join vp101100_1 vp101100_2)) (Blocks.join vp101100_3 (Blocks.join vp101100_4 vp101100_5))) (Blocks.join (Blocks.join vp101100_6 (Blocks.join vp101100_7 vp101100_8)) (Blocks.join (Blocks.join vp101100_9 vp101100_10) (Blocks.join vp101100_11 vp101100_12))))
private theorem bp1011000 : Branch 0 (-5631761639/128000000 : ℚ) vp101100 := by
  apply branch_left_normalized (c:=vp1011000) (k:=0) (m:=851) (by decide +kernel)
  rw [show 2*(-5631761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-5631761639/64000000 : ℚ) by norm_num]
  exact coverp1011000
private noncomputable def ep1011001_0 : Blocks := edgeBlocks% "full/vectors/1011001-E-0000.bin"
private noncomputable def ep1011001_1 : Blocks := edgeBlocks% "full/vectors/1011001-E-0001.bin"
private noncomputable def ep1011001_2 : Blocks := edgeBlocks% "full/vectors/1011001-E-0002.bin"
private noncomputable def ep1011001_3 : Blocks := edgeBlocks% "full/vectors/1011001-E-0003.bin"
private noncomputable def ep1011001_4 : Blocks := edgeBlocks% "full/vectors/1011001-E-0004.bin"
private noncomputable def ep1011001_5 : Blocks := edgeBlocks% "full/vectors/1011001-E-0005.bin"
private noncomputable def ep1011001_6 : Blocks := edgeBlocks% "full/vectors/1011001-E-0006.bin"
private noncomputable def ep1011001_7 : Blocks := edgeBlocks% "full/vectors/1011001-E-0007.bin"
private noncomputable def ep1011001_8 : Blocks := edgeBlocks% "full/vectors/1011001-E-0008.bin"
private noncomputable def ep1011001_9 : Blocks := edgeBlocks% "full/vectors/1011001-E-0009.bin"
private noncomputable def ep1011001_10 : Blocks := edgeBlocks% "full/vectors/1011001-E-0010.bin"
private noncomputable def ep1011001_11 : Blocks := edgeBlocks% "full/vectors/1011001-E-0011.bin"
private noncomputable def ep1011001_12 : Blocks := edgeBlocks% "full/vectors/1011001-E-0012.bin"
noncomputable def ep1011001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1011001_0 (Blocks.join ep1011001_1 ep1011001_2)) (Blocks.join ep1011001_3 (Blocks.join ep1011001_4 ep1011001_5))) (Blocks.join (Blocks.join ep1011001_6 (Blocks.join ep1011001_7 ep1011001_8)) (Blocks.join (Blocks.join ep1011001_9 ep1011001_10) (Blocks.join ep1011001_11 ep1011001_12))))
private theorem idp1011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp101100.list =
    C ((2:ℤ)^2028) * horner X vp1011001.list + horner X ep1011001.list := by
  exact edge_identity (B := (2:ℤ)^2643) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1011001 : Branch 1 (-5631761639/128000000 : ℚ) vp101100 := by
  apply branch_checked idp1011001 (by positivity) (by decide +kernel)
  rw [show 2*(-5631761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-5695761639/64000000 : ℚ) by norm_num]
  exact coverp1011001
theorem coverp101100 : Covers (-5631761639/128000000 : ℚ) vp101100 := join_branches bp1011000 bp1011001
private noncomputable def vp10110_0 : Blocks := edgeBlocks% "full/vectors/10110-V-0000.bin"
private noncomputable def vp10110_1 : Blocks := edgeBlocks% "full/vectors/10110-V-0001.bin"
private noncomputable def vp10110_2 : Blocks := edgeBlocks% "full/vectors/10110-V-0002.bin"
private noncomputable def vp10110_3 : Blocks := edgeBlocks% "full/vectors/10110-V-0003.bin"
private noncomputable def vp10110_4 : Blocks := edgeBlocks% "full/vectors/10110-V-0004.bin"
private noncomputable def vp10110_5 : Blocks := edgeBlocks% "full/vectors/10110-V-0005.bin"
private noncomputable def vp10110_6 : Blocks := edgeBlocks% "full/vectors/10110-V-0006.bin"
private noncomputable def vp10110_7 : Blocks := edgeBlocks% "full/vectors/10110-V-0007.bin"
private noncomputable def vp10110_8 : Blocks := edgeBlocks% "full/vectors/10110-V-0008.bin"
private noncomputable def vp10110_9 : Blocks := edgeBlocks% "full/vectors/10110-V-0009.bin"
private noncomputable def vp10110_10 : Blocks := edgeBlocks% "full/vectors/10110-V-0010.bin"
private noncomputable def vp10110_11 : Blocks := edgeBlocks% "full/vectors/10110-V-0011.bin"
private noncomputable def vp10110_12 : Blocks := edgeBlocks% "full/vectors/10110-V-0012.bin"
private noncomputable def vp10110_13 : Blocks := edgeBlocks% "full/vectors/10110-V-0013.bin"
private noncomputable def vp10110_14 : Blocks := edgeBlocks% "full/vectors/10110-V-0014.bin"
private noncomputable def vp10110_15 : Blocks := edgeBlocks% "full/vectors/10110-V-0015.bin"
private noncomputable def vp10110_16 : Blocks := edgeBlocks% "full/vectors/10110-V-0016.bin"
private noncomputable def vp10110_17 : Blocks := edgeBlocks% "full/vectors/10110-V-0017.bin"
private noncomputable def vp10110_18 : Blocks := edgeBlocks% "full/vectors/10110-V-0018.bin"
private noncomputable def vp10110_19 : Blocks := edgeBlocks% "full/vectors/10110-V-0019.bin"
private noncomputable def vp10110_20 : Blocks := edgeBlocks% "full/vectors/10110-V-0020.bin"
private noncomputable def vp10110_21 : Blocks := edgeBlocks% "full/vectors/10110-V-0021.bin"
private noncomputable def vp10110_22 : Blocks := edgeBlocks% "full/vectors/10110-V-0022.bin"
private noncomputable def vp10110_23 : Blocks := edgeBlocks% "full/vectors/10110-V-0023.bin"
private noncomputable def vp10110_24 : Blocks := edgeBlocks% "full/vectors/10110-V-0024.bin"
private noncomputable def vp10110_25 : Blocks := edgeBlocks% "full/vectors/10110-V-0025.bin"
noncomputable def vp10110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp10110_0 (Blocks.join vp10110_1 vp10110_2)) (Blocks.join vp10110_3 (Blocks.join vp10110_4 vp10110_5))) (Blocks.join (Blocks.join vp10110_6 (Blocks.join vp10110_7 vp10110_8)) (Blocks.join (Blocks.join vp10110_9 vp10110_10) (Blocks.join vp10110_11 vp10110_12)))) (Blocks.join (Blocks.join (Blocks.join vp10110_13 (Blocks.join vp10110_14 vp10110_15)) (Blocks.join vp10110_16 (Blocks.join vp10110_17 vp10110_18))) (Blocks.join (Blocks.join vp10110_19 (Blocks.join vp10110_20 vp10110_21)) (Blocks.join (Blocks.join vp10110_22 vp10110_23) (Blocks.join vp10110_24 vp10110_25)))))
private theorem bp101100 : Branch 0 (-5631761639/256000000 : ℚ) vp10110 := by
  apply branch_left_normalized (c:=vp101100) (k:=0) (m:=1658) (by decide +kernel)
  rw [show 2*(-5631761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-5631761639/128000000 : ℚ) by norm_num]
  exact coverp101100
private noncomputable def ep101101_0 : Blocks := edgeBlocks% "full/vectors/101101-E-0000.bin"
private noncomputable def ep101101_1 : Blocks := edgeBlocks% "full/vectors/101101-E-0001.bin"
private noncomputable def ep101101_2 : Blocks := edgeBlocks% "full/vectors/101101-E-0002.bin"
private noncomputable def ep101101_3 : Blocks := edgeBlocks% "full/vectors/101101-E-0003.bin"
private noncomputable def ep101101_4 : Blocks := edgeBlocks% "full/vectors/101101-E-0004.bin"
private noncomputable def ep101101_5 : Blocks := edgeBlocks% "full/vectors/101101-E-0005.bin"
private noncomputable def ep101101_6 : Blocks := edgeBlocks% "full/vectors/101101-E-0006.bin"
private noncomputable def ep101101_7 : Blocks := edgeBlocks% "full/vectors/101101-E-0007.bin"
private noncomputable def ep101101_8 : Blocks := edgeBlocks% "full/vectors/101101-E-0008.bin"
private noncomputable def ep101101_9 : Blocks := edgeBlocks% "full/vectors/101101-E-0009.bin"
private noncomputable def ep101101_10 : Blocks := edgeBlocks% "full/vectors/101101-E-0010.bin"
private noncomputable def ep101101_11 : Blocks := edgeBlocks% "full/vectors/101101-E-0011.bin"
private noncomputable def ep101101_12 : Blocks := edgeBlocks% "full/vectors/101101-E-0012.bin"
private noncomputable def ep101101_13 : Blocks := edgeBlocks% "full/vectors/101101-E-0013.bin"
private noncomputable def ep101101_14 : Blocks := edgeBlocks% "full/vectors/101101-E-0014.bin"
private noncomputable def ep101101_15 : Blocks := edgeBlocks% "full/vectors/101101-E-0015.bin"
private noncomputable def ep101101_16 : Blocks := edgeBlocks% "full/vectors/101101-E-0016.bin"
private noncomputable def ep101101_17 : Blocks := edgeBlocks% "full/vectors/101101-E-0017.bin"
private noncomputable def ep101101_18 : Blocks := edgeBlocks% "full/vectors/101101-E-0018.bin"
private noncomputable def ep101101_19 : Blocks := edgeBlocks% "full/vectors/101101-E-0019.bin"
private noncomputable def ep101101_20 : Blocks := edgeBlocks% "full/vectors/101101-E-0020.bin"
private noncomputable def ep101101_21 : Blocks := edgeBlocks% "full/vectors/101101-E-0021.bin"
private noncomputable def ep101101_22 : Blocks := edgeBlocks% "full/vectors/101101-E-0022.bin"
private noncomputable def ep101101_23 : Blocks := edgeBlocks% "full/vectors/101101-E-0023.bin"
private noncomputable def ep101101_24 : Blocks := edgeBlocks% "full/vectors/101101-E-0024.bin"
private noncomputable def ep101101_25 : Blocks := edgeBlocks% "full/vectors/101101-E-0025.bin"
noncomputable def ep101101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep101101_0 (Blocks.join ep101101_1 ep101101_2)) (Blocks.join ep101101_3 (Blocks.join ep101101_4 ep101101_5))) (Blocks.join (Blocks.join ep101101_6 (Blocks.join ep101101_7 ep101101_8)) (Blocks.join (Blocks.join ep101101_9 ep101101_10) (Blocks.join ep101101_11 ep101101_12)))) (Blocks.join (Blocks.join (Blocks.join ep101101_13 (Blocks.join ep101101_14 ep101101_15)) (Blocks.join ep101101_16 (Blocks.join ep101101_17 ep101101_18))) (Blocks.join (Blocks.join ep101101_19 (Blocks.join ep101101_20 ep101101_21)) (Blocks.join (Blocks.join ep101101_22 ep101101_23) (Blocks.join ep101101_24 ep101101_25)))))
private def ptsp101101 : List ℤ := [((2:ℤ)^3739+0),((2:ℤ)^3739+1)]
private theorem boundp101101 : 2^vp10110.size*absSum vp10110.list + ((2:ℤ)^3947*absSum vp101101.list+absSum ep101101.list) < (2:ℤ)^5059 := by decide +kernel
private theorem pointp101101_0 : fastHom 1 ((2:ℤ)^3739+0) vp10110 = ((2:ℤ)^3947)*vp101101.subst ((2:ℤ)^3739+0)+ep101101.subst ((2:ℤ)^3739+0) := by decide +kernel
private theorem pointp101101_1 : fastHom 1 ((2:ℤ)^3739+1) vp10110 = ((2:ℤ)^3947)*vp101101.subst ((2:ℤ)^3739+1)+ep101101.subst ((2:ℤ)^3739+1) := by decide +kernel
private theorem checkp101101 (x:ℤ) (hx:x ∈ ptsp101101) : fastHom 1 x vp10110 = ((2:ℤ)^3947)*vp101101.subst x+ep101101.subst x := by
  simp only [ptsp101101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp101101_0
  · exact pointp101101_1
private theorem idp101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10110.list =
    C ((2:ℤ)^3947) * horner X vp101101.list + horner X ep101101.list := by
  apply edge_identity (B := (2:ℤ)^5059) (by decide) (by positivity) (by positivity) boundp101101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp101101 (by decide +kernel)
  · have h : ptsp101101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp101101.trans_le (by decide +kernel)
  · exact checkp101101
private theorem bp101101 : Branch 1 (-5631761639/256000000 : ℚ) vp10110 := by
  apply branch_checked idp101101 (by positivity) (by decide +kernel)
  rw [show 2*(-5631761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-5759761639/128000000 : ℚ) by norm_num]
  exact coverp101101
theorem coverp10110 : Covers (-5631761639/256000000 : ℚ) vp10110 := join_branches bp101100 bp101101
private noncomputable def vp1011_0 : Blocks := edgeBlocks% "full/vectors/1011-V-0000.bin"
private noncomputable def vp1011_1 : Blocks := edgeBlocks% "full/vectors/1011-V-0001.bin"
private noncomputable def vp1011_2 : Blocks := edgeBlocks% "full/vectors/1011-V-0002.bin"
private noncomputable def vp1011_3 : Blocks := edgeBlocks% "full/vectors/1011-V-0003.bin"
private noncomputable def vp1011_4 : Blocks := edgeBlocks% "full/vectors/1011-V-0004.bin"
private noncomputable def vp1011_5 : Blocks := edgeBlocks% "full/vectors/1011-V-0005.bin"
private noncomputable def vp1011_6 : Blocks := edgeBlocks% "full/vectors/1011-V-0006.bin"
private noncomputable def vp1011_7 : Blocks := edgeBlocks% "full/vectors/1011-V-0007.bin"
private noncomputable def vp1011_8 : Blocks := edgeBlocks% "full/vectors/1011-V-0008.bin"
private noncomputable def vp1011_9 : Blocks := edgeBlocks% "full/vectors/1011-V-0009.bin"
private noncomputable def vp1011_10 : Blocks := edgeBlocks% "full/vectors/1011-V-0010.bin"
private noncomputable def vp1011_11 : Blocks := edgeBlocks% "full/vectors/1011-V-0011.bin"
private noncomputable def vp1011_12 : Blocks := edgeBlocks% "full/vectors/1011-V-0012.bin"
private noncomputable def vp1011_13 : Blocks := edgeBlocks% "full/vectors/1011-V-0013.bin"
private noncomputable def vp1011_14 : Blocks := edgeBlocks% "full/vectors/1011-V-0014.bin"
private noncomputable def vp1011_15 : Blocks := edgeBlocks% "full/vectors/1011-V-0015.bin"
private noncomputable def vp1011_16 : Blocks := edgeBlocks% "full/vectors/1011-V-0016.bin"
private noncomputable def vp1011_17 : Blocks := edgeBlocks% "full/vectors/1011-V-0017.bin"
private noncomputable def vp1011_18 : Blocks := edgeBlocks% "full/vectors/1011-V-0018.bin"
private noncomputable def vp1011_19 : Blocks := edgeBlocks% "full/vectors/1011-V-0019.bin"
private noncomputable def vp1011_20 : Blocks := edgeBlocks% "full/vectors/1011-V-0020.bin"
private noncomputable def vp1011_21 : Blocks := edgeBlocks% "full/vectors/1011-V-0021.bin"
private noncomputable def vp1011_22 : Blocks := edgeBlocks% "full/vectors/1011-V-0022.bin"
private noncomputable def vp1011_23 : Blocks := edgeBlocks% "full/vectors/1011-V-0023.bin"
private noncomputable def vp1011_24 : Blocks := edgeBlocks% "full/vectors/1011-V-0024.bin"
private noncomputable def vp1011_25 : Blocks := edgeBlocks% "full/vectors/1011-V-0025.bin"
private noncomputable def vp1011_26 : Blocks := edgeBlocks% "full/vectors/1011-V-0026.bin"
private noncomputable def vp1011_27 : Blocks := edgeBlocks% "full/vectors/1011-V-0027.bin"
private noncomputable def vp1011_28 : Blocks := edgeBlocks% "full/vectors/1011-V-0028.bin"
private noncomputable def vp1011_29 : Blocks := edgeBlocks% "full/vectors/1011-V-0029.bin"
private noncomputable def vp1011_30 : Blocks := edgeBlocks% "full/vectors/1011-V-0030.bin"
private noncomputable def vp1011_31 : Blocks := edgeBlocks% "full/vectors/1011-V-0031.bin"
private noncomputable def vp1011_32 : Blocks := edgeBlocks% "full/vectors/1011-V-0032.bin"
private noncomputable def vp1011_33 : Blocks := edgeBlocks% "full/vectors/1011-V-0033.bin"
private noncomputable def vp1011_34 : Blocks := edgeBlocks% "full/vectors/1011-V-0034.bin"
private noncomputable def vp1011_35 : Blocks := edgeBlocks% "full/vectors/1011-V-0035.bin"
private noncomputable def vp1011_36 : Blocks := edgeBlocks% "full/vectors/1011-V-0036.bin"
private noncomputable def vp1011_37 : Blocks := edgeBlocks% "full/vectors/1011-V-0037.bin"
private noncomputable def vp1011_38 : Blocks := edgeBlocks% "full/vectors/1011-V-0038.bin"
private noncomputable def vp1011_39 : Blocks := edgeBlocks% "full/vectors/1011-V-0039.bin"
private noncomputable def vp1011_40 : Blocks := edgeBlocks% "full/vectors/1011-V-0040.bin"
private noncomputable def vp1011_41 : Blocks := edgeBlocks% "full/vectors/1011-V-0041.bin"
private noncomputable def vp1011_42 : Blocks := edgeBlocks% "full/vectors/1011-V-0042.bin"
private noncomputable def vp1011_43 : Blocks := edgeBlocks% "full/vectors/1011-V-0043.bin"
private noncomputable def vp1011_44 : Blocks := edgeBlocks% "full/vectors/1011-V-0044.bin"
private noncomputable def vp1011_45 : Blocks := edgeBlocks% "full/vectors/1011-V-0045.bin"
private noncomputable def vp1011_46 : Blocks := edgeBlocks% "full/vectors/1011-V-0046.bin"
private noncomputable def vp1011_47 : Blocks := edgeBlocks% "full/vectors/1011-V-0047.bin"
noncomputable def vp1011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1011_0 (Blocks.join vp1011_1 vp1011_2)) (Blocks.join vp1011_3 (Blocks.join vp1011_4 vp1011_5))) (Blocks.join (Blocks.join vp1011_6 (Blocks.join vp1011_7 vp1011_8)) (Blocks.join vp1011_9 (Blocks.join vp1011_10 vp1011_11)))) (Blocks.join (Blocks.join (Blocks.join vp1011_12 (Blocks.join vp1011_13 vp1011_14)) (Blocks.join vp1011_15 (Blocks.join vp1011_16 vp1011_17))) (Blocks.join (Blocks.join vp1011_18 (Blocks.join vp1011_19 vp1011_20)) (Blocks.join vp1011_21 (Blocks.join vp1011_22 vp1011_23))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1011_24 (Blocks.join vp1011_25 vp1011_26)) (Blocks.join vp1011_27 (Blocks.join vp1011_28 vp1011_29))) (Blocks.join (Blocks.join vp1011_30 (Blocks.join vp1011_31 vp1011_32)) (Blocks.join vp1011_33 (Blocks.join vp1011_34 vp1011_35)))) (Blocks.join (Blocks.join (Blocks.join vp1011_36 (Blocks.join vp1011_37 vp1011_38)) (Blocks.join vp1011_39 (Blocks.join vp1011_40 vp1011_41))) (Blocks.join (Blocks.join vp1011_42 (Blocks.join vp1011_43 vp1011_44)) (Blocks.join vp1011_45 (Blocks.join vp1011_46 vp1011_47))))))
private theorem bp10110 : Branch 0 (-5631761639/512000000 : ℚ) vp1011 := by
  apply branch_left_normalized (c:=vp10110) (k:=0) (m:=3208) (by decide +kernel)
  rw [show 2*(-5631761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-5631761639/256000000 : ℚ) by norm_num]
  exact coverp10110
private noncomputable def ep10111_0 : Blocks := edgeBlocks% "full/vectors/10111-E-0000.bin"
private noncomputable def ep10111_1 : Blocks := edgeBlocks% "full/vectors/10111-E-0001.bin"
private noncomputable def ep10111_2 : Blocks := edgeBlocks% "full/vectors/10111-E-0002.bin"
private noncomputable def ep10111_3 : Blocks := edgeBlocks% "full/vectors/10111-E-0003.bin"
private noncomputable def ep10111_4 : Blocks := edgeBlocks% "full/vectors/10111-E-0004.bin"
private noncomputable def ep10111_5 : Blocks := edgeBlocks% "full/vectors/10111-E-0005.bin"
private noncomputable def ep10111_6 : Blocks := edgeBlocks% "full/vectors/10111-E-0006.bin"
private noncomputable def ep10111_7 : Blocks := edgeBlocks% "full/vectors/10111-E-0007.bin"
private noncomputable def ep10111_8 : Blocks := edgeBlocks% "full/vectors/10111-E-0008.bin"
private noncomputable def ep10111_9 : Blocks := edgeBlocks% "full/vectors/10111-E-0009.bin"
private noncomputable def ep10111_10 : Blocks := edgeBlocks% "full/vectors/10111-E-0010.bin"
private noncomputable def ep10111_11 : Blocks := edgeBlocks% "full/vectors/10111-E-0011.bin"
private noncomputable def ep10111_12 : Blocks := edgeBlocks% "full/vectors/10111-E-0012.bin"
private noncomputable def ep10111_13 : Blocks := edgeBlocks% "full/vectors/10111-E-0013.bin"
private noncomputable def ep10111_14 : Blocks := edgeBlocks% "full/vectors/10111-E-0014.bin"
private noncomputable def ep10111_15 : Blocks := edgeBlocks% "full/vectors/10111-E-0015.bin"
private noncomputable def ep10111_16 : Blocks := edgeBlocks% "full/vectors/10111-E-0016.bin"
private noncomputable def ep10111_17 : Blocks := edgeBlocks% "full/vectors/10111-E-0017.bin"
private noncomputable def ep10111_18 : Blocks := edgeBlocks% "full/vectors/10111-E-0018.bin"
private noncomputable def ep10111_19 : Blocks := edgeBlocks% "full/vectors/10111-E-0019.bin"
private noncomputable def ep10111_20 : Blocks := edgeBlocks% "full/vectors/10111-E-0020.bin"
private noncomputable def ep10111_21 : Blocks := edgeBlocks% "full/vectors/10111-E-0021.bin"
private noncomputable def ep10111_22 : Blocks := edgeBlocks% "full/vectors/10111-E-0022.bin"
private noncomputable def ep10111_23 : Blocks := edgeBlocks% "full/vectors/10111-E-0023.bin"
private noncomputable def ep10111_24 : Blocks := edgeBlocks% "full/vectors/10111-E-0024.bin"
private noncomputable def ep10111_25 : Blocks := edgeBlocks% "full/vectors/10111-E-0025.bin"
private noncomputable def ep10111_26 : Blocks := edgeBlocks% "full/vectors/10111-E-0026.bin"
private noncomputable def ep10111_27 : Blocks := edgeBlocks% "full/vectors/10111-E-0027.bin"
private noncomputable def ep10111_28 : Blocks := edgeBlocks% "full/vectors/10111-E-0028.bin"
private noncomputable def ep10111_29 : Blocks := edgeBlocks% "full/vectors/10111-E-0029.bin"
private noncomputable def ep10111_30 : Blocks := edgeBlocks% "full/vectors/10111-E-0030.bin"
private noncomputable def ep10111_31 : Blocks := edgeBlocks% "full/vectors/10111-E-0031.bin"
private noncomputable def ep10111_32 : Blocks := edgeBlocks% "full/vectors/10111-E-0032.bin"
private noncomputable def ep10111_33 : Blocks := edgeBlocks% "full/vectors/10111-E-0033.bin"
private noncomputable def ep10111_34 : Blocks := edgeBlocks% "full/vectors/10111-E-0034.bin"
private noncomputable def ep10111_35 : Blocks := edgeBlocks% "full/vectors/10111-E-0035.bin"
private noncomputable def ep10111_36 : Blocks := edgeBlocks% "full/vectors/10111-E-0036.bin"
private noncomputable def ep10111_37 : Blocks := edgeBlocks% "full/vectors/10111-E-0037.bin"
private noncomputable def ep10111_38 : Blocks := edgeBlocks% "full/vectors/10111-E-0038.bin"
private noncomputable def ep10111_39 : Blocks := edgeBlocks% "full/vectors/10111-E-0039.bin"
private noncomputable def ep10111_40 : Blocks := edgeBlocks% "full/vectors/10111-E-0040.bin"
private noncomputable def ep10111_41 : Blocks := edgeBlocks% "full/vectors/10111-E-0041.bin"
private noncomputable def ep10111_42 : Blocks := edgeBlocks% "full/vectors/10111-E-0042.bin"
private noncomputable def ep10111_43 : Blocks := edgeBlocks% "full/vectors/10111-E-0043.bin"
private noncomputable def ep10111_44 : Blocks := edgeBlocks% "full/vectors/10111-E-0044.bin"
private noncomputable def ep10111_45 : Blocks := edgeBlocks% "full/vectors/10111-E-0045.bin"
private noncomputable def ep10111_46 : Blocks := edgeBlocks% "full/vectors/10111-E-0046.bin"
private noncomputable def ep10111_47 : Blocks := edgeBlocks% "full/vectors/10111-E-0047.bin"
noncomputable def ep10111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep10111_0 (Blocks.join ep10111_1 ep10111_2)) (Blocks.join ep10111_3 (Blocks.join ep10111_4 ep10111_5))) (Blocks.join (Blocks.join ep10111_6 (Blocks.join ep10111_7 ep10111_8)) (Blocks.join ep10111_9 (Blocks.join ep10111_10 ep10111_11)))) (Blocks.join (Blocks.join (Blocks.join ep10111_12 (Blocks.join ep10111_13 ep10111_14)) (Blocks.join ep10111_15 (Blocks.join ep10111_16 ep10111_17))) (Blocks.join (Blocks.join ep10111_18 (Blocks.join ep10111_19 ep10111_20)) (Blocks.join ep10111_21 (Blocks.join ep10111_22 ep10111_23))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep10111_24 (Blocks.join ep10111_25 ep10111_26)) (Blocks.join ep10111_27 (Blocks.join ep10111_28 ep10111_29))) (Blocks.join (Blocks.join ep10111_30 (Blocks.join ep10111_31 ep10111_32)) (Blocks.join ep10111_33 (Blocks.join ep10111_34 ep10111_35)))) (Blocks.join (Blocks.join (Blocks.join ep10111_36 (Blocks.join ep10111_37 ep10111_38)) (Blocks.join ep10111_39 (Blocks.join ep10111_40 ep10111_41))) (Blocks.join (Blocks.join ep10111_42 (Blocks.join ep10111_43 ep10111_44)) (Blocks.join ep10111_45 (Blocks.join ep10111_46 ep10111_47))))))
private def ptsp10111 : List ℤ := [((2:ℤ)^1980+0),((2:ℤ)^1980+1),((2:ℤ)^1980+2),((2:ℤ)^1980+3),((2:ℤ)^1980+4)]
private theorem boundp10111 : 2^vp1011.size*absSum vp1011.list + ((2:ℤ)^7536*absSum vp10111.list+absSum ep10111.list) < (2:ℤ)^9593 := by decide +kernel
private theorem pointp10111_0 : fastHom 1 ((2:ℤ)^1980+0) vp1011 = ((2:ℤ)^7536)*vp10111.subst ((2:ℤ)^1980+0)+ep10111.subst ((2:ℤ)^1980+0) := by decide +kernel
private theorem pointp10111_1 : fastHom 1 ((2:ℤ)^1980+1) vp1011 = ((2:ℤ)^7536)*vp10111.subst ((2:ℤ)^1980+1)+ep10111.subst ((2:ℤ)^1980+1) := by decide +kernel
private theorem pointp10111_2 : fastHom 1 ((2:ℤ)^1980+2) vp1011 = ((2:ℤ)^7536)*vp10111.subst ((2:ℤ)^1980+2)+ep10111.subst ((2:ℤ)^1980+2) := by decide +kernel
private theorem pointp10111_3 : fastHom 1 ((2:ℤ)^1980+3) vp1011 = ((2:ℤ)^7536)*vp10111.subst ((2:ℤ)^1980+3)+ep10111.subst ((2:ℤ)^1980+3) := by decide +kernel
private theorem pointp10111_4 : fastHom 1 ((2:ℤ)^1980+4) vp1011 = ((2:ℤ)^7536)*vp10111.subst ((2:ℤ)^1980+4)+ep10111.subst ((2:ℤ)^1980+4) := by decide +kernel
private theorem checkp10111 (x:ℤ) (hx:x ∈ ptsp10111) : fastHom 1 x vp1011 = ((2:ℤ)^7536)*vp10111.subst x+ep10111.subst x := by
  simp only [ptsp10111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pointp10111_0
  · exact pointp10111_1
  · exact pointp10111_2
  · exact pointp10111_3
  · exact pointp10111_4
private theorem idp10111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1011.list =
    C ((2:ℤ)^7536) * horner X vp10111.list + horner X ep10111.list := by
  apply edge_identity (B := (2:ℤ)^9593) (by decide) (by positivity) (by positivity) boundp10111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp10111 (by decide +kernel)
  · have h : ptsp10111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp10111.trans_le (by decide +kernel)
  · exact checkp10111
private theorem bp10111 : Branch 1 (-5631761639/512000000 : ℚ) vp1011 := by
  apply branch_checked idp10111 (by positivity) (by decide +kernel)
  rw [show 2*(-5631761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-5887761639/256000000 : ℚ) by norm_num]
  exact coverp10111
theorem coverp1011 : Covers (-5631761639/512000000 : ℚ) vp1011 := join_branches bp10110 bp10111
end NextProof.EdgeFull

