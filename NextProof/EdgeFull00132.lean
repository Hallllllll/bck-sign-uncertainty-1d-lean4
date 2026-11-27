import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00131

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp1000011111_0 : Blocks := edgeBlocks% "full/vectors/1000011111-V-0000.bin"
private noncomputable def vp1000011111_1 : Blocks := edgeBlocks% "full/vectors/1000011111-V-0001.bin"
noncomputable def vp1000011111 : Blocks := (Blocks.join vp1000011111_0 vp1000011111_1)
theorem coverp1000011111 : Covers (-4343761639/8000000 : ℚ) vp1000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp1000011110_0 : Blocks := edgeBlocks% "full/vectors/1000011110-V-0000.bin"
private noncomputable def vp1000011110_1 : Blocks := edgeBlocks% "full/vectors/1000011110-V-0001.bin"
noncomputable def vp1000011110 : Blocks := (Blocks.join vp1000011110_0 vp1000011110_1)
theorem coverp1000011110 : Covers (-4335761639/8000000 : ℚ) vp1000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp100001111_0 : Blocks := edgeBlocks% "full/vectors/100001111-V-0000.bin"
private noncomputable def vp100001111_1 : Blocks := edgeBlocks% "full/vectors/100001111-V-0001.bin"
private noncomputable def vp100001111_2 : Blocks := edgeBlocks% "full/vectors/100001111-V-0002.bin"
noncomputable def vp100001111 : Blocks := (Blocks.join vp100001111_0 (Blocks.join vp100001111_1 vp100001111_2))
private theorem bp1000011110 : Branch 0 (-4335761639/16000000 : ℚ) vp100001111 := by
  apply branch_left_normalized (c:=vp1000011110) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-4335761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4335761639/8000000 : ℚ) by norm_num]
  exact coverp1000011110
private noncomputable def ep1000011111_0 : Blocks := edgeBlocks% "full/vectors/1000011111-E-0000.bin"
private noncomputable def ep1000011111_1 : Blocks := edgeBlocks% "full/vectors/1000011111-E-0001.bin"
private noncomputable def ep1000011111_2 : Blocks := edgeBlocks% "full/vectors/1000011111-E-0002.bin"
noncomputable def ep1000011111 : Blocks := (Blocks.join ep1000011111_0 (Blocks.join ep1000011111_1 ep1000011111_2))
private theorem idp1000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100001111.list =
    C ((2:ℤ)^304) * horner X vp1000011111.list + horner X ep1000011111.list := by
  exact edge_identity (B := (2:ℤ)^478) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000011111 : Branch 1 (-4335761639/16000000 : ℚ) vp100001111 := by
  apply branch_checked idp1000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-4335761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4343761639/8000000 : ℚ) by norm_num]
  exact coverp1000011111
theorem coverp100001111 : Covers (-4335761639/16000000 : ℚ) vp100001111 := join_branches bp1000011110 bp1000011111
private noncomputable def vp1000011101_0 : Blocks := edgeBlocks% "full/vectors/1000011101-V-0000.bin"
private noncomputable def vp1000011101_1 : Blocks := edgeBlocks% "full/vectors/1000011101-V-0001.bin"
noncomputable def vp1000011101 : Blocks := (Blocks.join vp1000011101_0 vp1000011101_1)
theorem coverp1000011101 : Covers (-4327761639/8000000 : ℚ) vp1000011101 := cover_leaf (by decide +kernel)
private noncomputable def vp10000111001_0 : Blocks := edgeBlocks% "full/vectors/10000111001-V-0000.bin"
noncomputable def vp10000111001 : Blocks := vp10000111001_0
theorem coverp10000111001 : Covers (-4323761639/4000000 : ℚ) vp10000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp10000111000_0 : Blocks := edgeBlocks% "full/vectors/10000111000-V-0000.bin"
noncomputable def vp10000111000 : Blocks := vp10000111000_0
theorem coverp10000111000 : Covers (-4319761639/4000000 : ℚ) vp10000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000011100_0 : Blocks := edgeBlocks% "full/vectors/1000011100-V-0000.bin"
private noncomputable def vp1000011100_1 : Blocks := edgeBlocks% "full/vectors/1000011100-V-0001.bin"
noncomputable def vp1000011100 : Blocks := (Blocks.join vp1000011100_0 vp1000011100_1)
private theorem bp10000111000 : Branch 0 (-4319761639/8000000 : ℚ) vp1000011100 := by
  apply branch_left_normalized (c:=vp10000111000) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4319761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4319761639/4000000 : ℚ) by norm_num]
  exact coverp10000111000
private noncomputable def ep10000111001_0 : Blocks := edgeBlocks% "full/vectors/10000111001-E-0000.bin"
private noncomputable def ep10000111001_1 : Blocks := edgeBlocks% "full/vectors/10000111001-E-0001.bin"
noncomputable def ep10000111001 : Blocks := (Blocks.join ep10000111001_0 ep10000111001_1)
private theorem idp10000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000011100.list =
    C ((2:ℤ)^166) * horner X vp10000111001.list + horner X ep10000111001.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000111001 : Branch 1 (-4319761639/8000000 : ℚ) vp1000011100 := by
  apply branch_checked idp10000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-4319761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4323761639/4000000 : ℚ) by norm_num]
  exact coverp10000111001
theorem coverp1000011100 : Covers (-4319761639/8000000 : ℚ) vp1000011100 := join_branches bp10000111000 bp10000111001
private noncomputable def vp100001110_0 : Blocks := edgeBlocks% "full/vectors/100001110-V-0000.bin"
private noncomputable def vp100001110_1 : Blocks := edgeBlocks% "full/vectors/100001110-V-0001.bin"
private noncomputable def vp100001110_2 : Blocks := edgeBlocks% "full/vectors/100001110-V-0002.bin"
noncomputable def vp100001110 : Blocks := (Blocks.join vp100001110_0 (Blocks.join vp100001110_1 vp100001110_2))
private theorem bp1000011100 : Branch 0 (-4319761639/16000000 : ℚ) vp100001110 := by
  apply branch_left_normalized (c:=vp1000011100) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-4319761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4319761639/8000000 : ℚ) by norm_num]
  exact coverp1000011100
private noncomputable def ep1000011101_0 : Blocks := edgeBlocks% "full/vectors/1000011101-E-0000.bin"
private noncomputable def ep1000011101_1 : Blocks := edgeBlocks% "full/vectors/1000011101-E-0001.bin"
private noncomputable def ep1000011101_2 : Blocks := edgeBlocks% "full/vectors/1000011101-E-0002.bin"
noncomputable def ep1000011101 : Blocks := (Blocks.join ep1000011101_0 (Blocks.join ep1000011101_1 ep1000011101_2))
private theorem idp1000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100001110.list =
    C ((2:ℤ)^309) * horner X vp1000011101.list + horner X ep1000011101.list := by
  exact edge_identity (B := (2:ℤ)^486) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000011101 : Branch 1 (-4319761639/16000000 : ℚ) vp100001110 := by
  apply branch_checked idp1000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-4319761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4327761639/8000000 : ℚ) by norm_num]
  exact coverp1000011101
theorem coverp100001110 : Covers (-4319761639/16000000 : ℚ) vp100001110 := join_branches bp1000011100 bp1000011101
private noncomputable def vp10000111_0 : Blocks := edgeBlocks% "full/vectors/10000111-V-0000.bin"
private noncomputable def vp10000111_1 : Blocks := edgeBlocks% "full/vectors/10000111-V-0001.bin"
private noncomputable def vp10000111_2 : Blocks := edgeBlocks% "full/vectors/10000111-V-0002.bin"
private noncomputable def vp10000111_3 : Blocks := edgeBlocks% "full/vectors/10000111-V-0003.bin"
noncomputable def vp10000111 : Blocks := (Blocks.join (Blocks.join vp10000111_0 vp10000111_1) (Blocks.join vp10000111_2 vp10000111_3))
private theorem bp100001110 : Branch 0 (-4319761639/32000000 : ℚ) vp10000111 := by
  apply branch_left_normalized (c:=vp100001110) (k:=0) (m:=259) (by decide +kernel)
  rw [show 2*(-4319761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4319761639/16000000 : ℚ) by norm_num]
  exact coverp100001110
private noncomputable def ep100001111_0 : Blocks := edgeBlocks% "full/vectors/100001111-E-0000.bin"
private noncomputable def ep100001111_1 : Blocks := edgeBlocks% "full/vectors/100001111-E-0001.bin"
private noncomputable def ep100001111_2 : Blocks := edgeBlocks% "full/vectors/100001111-E-0002.bin"
private noncomputable def ep100001111_3 : Blocks := edgeBlocks% "full/vectors/100001111-E-0003.bin"
noncomputable def ep100001111 : Blocks := (Blocks.join (Blocks.join ep100001111_0 ep100001111_1) (Blocks.join ep100001111_2 ep100001111_3))
private theorem idp100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10000111.list =
    C ((2:ℤ)^595) * horner X vp100001111.list + horner X ep100001111.list := by
  exact edge_identity (B := (2:ℤ)^850) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100001111 : Branch 1 (-4319761639/32000000 : ℚ) vp10000111 := by
  apply branch_checked idp100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4319761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4335761639/16000000 : ℚ) by norm_num]
  exact coverp100001111
theorem coverp10000111 : Covers (-4319761639/32000000 : ℚ) vp10000111 := join_branches bp100001110 bp100001111
private noncomputable def vp10000110111_0 : Blocks := edgeBlocks% "full/vectors/10000110111-V-0000.bin"
noncomputable def vp10000110111 : Blocks := vp10000110111_0
theorem coverp10000110111 : Covers (-4315761639/4000000 : ℚ) vp10000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp10000110110_0 : Blocks := edgeBlocks% "full/vectors/10000110110-V-0000.bin"
noncomputable def vp10000110110 : Blocks := vp10000110110_0
theorem coverp10000110110 : Covers (-4311761639/4000000 : ℚ) vp10000110110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000011011_0 : Blocks := edgeBlocks% "full/vectors/1000011011-V-0000.bin"
private noncomputable def vp1000011011_1 : Blocks := edgeBlocks% "full/vectors/1000011011-V-0001.bin"
noncomputable def vp1000011011 : Blocks := (Blocks.join vp1000011011_0 vp1000011011_1)
private theorem bp10000110110 : Branch 0 (-4311761639/8000000 : ℚ) vp1000011011 := by
  apply branch_left_normalized (c:=vp10000110110) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4311761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4311761639/4000000 : ℚ) by norm_num]
  exact coverp10000110110
private noncomputable def ep10000110111_0 : Blocks := edgeBlocks% "full/vectors/10000110111-E-0000.bin"
private noncomputable def ep10000110111_1 : Blocks := edgeBlocks% "full/vectors/10000110111-E-0001.bin"
noncomputable def ep10000110111 : Blocks := (Blocks.join ep10000110111_0 ep10000110111_1)
private theorem idp10000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000011011.list =
    C ((2:ℤ)^166) * horner X vp10000110111.list + horner X ep10000110111.list := by
  exact edge_identity (B := (2:ℤ)^307) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000110111 : Branch 1 (-4311761639/8000000 : ℚ) vp1000011011 := by
  apply branch_checked idp10000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-4311761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4315761639/4000000 : ℚ) by norm_num]
  exact coverp10000110111
theorem coverp1000011011 : Covers (-4311761639/8000000 : ℚ) vp1000011011 := join_branches bp10000110110 bp10000110111
private noncomputable def vp10000110101_0 : Blocks := edgeBlocks% "full/vectors/10000110101-V-0000.bin"
noncomputable def vp10000110101 : Blocks := vp10000110101_0
theorem coverp10000110101 : Covers (-4307761639/4000000 : ℚ) vp10000110101 := cover_leaf (by decide +kernel)
private noncomputable def vp10000110100_0 : Blocks := edgeBlocks% "full/vectors/10000110100-V-0000.bin"
noncomputable def vp10000110100 : Blocks := vp10000110100_0
theorem coverp10000110100 : Covers (-4303761639/4000000 : ℚ) vp10000110100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000011010_0 : Blocks := edgeBlocks% "full/vectors/1000011010-V-0000.bin"
private noncomputable def vp1000011010_1 : Blocks := edgeBlocks% "full/vectors/1000011010-V-0001.bin"
noncomputable def vp1000011010 : Blocks := (Blocks.join vp1000011010_0 vp1000011010_1)
private theorem bp10000110100 : Branch 0 (-4303761639/8000000 : ℚ) vp1000011010 := by
  apply branch_left_normalized (c:=vp10000110100) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4303761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4303761639/4000000 : ℚ) by norm_num]
  exact coverp10000110100
private noncomputable def ep10000110101_0 : Blocks := edgeBlocks% "full/vectors/10000110101-E-0000.bin"
private noncomputable def ep10000110101_1 : Blocks := edgeBlocks% "full/vectors/10000110101-E-0001.bin"
noncomputable def ep10000110101 : Blocks := (Blocks.join ep10000110101_0 ep10000110101_1)
private theorem idp10000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000011010.list =
    C ((2:ℤ)^166) * horner X vp10000110101.list + horner X ep10000110101.list := by
  exact edge_identity (B := (2:ℤ)^308) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000110101 : Branch 1 (-4303761639/8000000 : ℚ) vp1000011010 := by
  apply branch_checked idp10000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-4303761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4307761639/4000000 : ℚ) by norm_num]
  exact coverp10000110101
theorem coverp1000011010 : Covers (-4303761639/8000000 : ℚ) vp1000011010 := join_branches bp10000110100 bp10000110101
private noncomputable def vp100001101_0 : Blocks := edgeBlocks% "full/vectors/100001101-V-0000.bin"
private noncomputable def vp100001101_1 : Blocks := edgeBlocks% "full/vectors/100001101-V-0001.bin"
private noncomputable def vp100001101_2 : Blocks := edgeBlocks% "full/vectors/100001101-V-0002.bin"
noncomputable def vp100001101 : Blocks := (Blocks.join vp100001101_0 (Blocks.join vp100001101_1 vp100001101_2))
private theorem bp1000011010 : Branch 0 (-4303761639/16000000 : ℚ) vp100001101 := by
  apply branch_left_normalized (c:=vp1000011010) (k:=0) (m:=142) (by decide +kernel)
  rw [show 2*(-4303761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4303761639/8000000 : ℚ) by norm_num]
  exact coverp1000011010
private noncomputable def ep1000011011_0 : Blocks := edgeBlocks% "full/vectors/1000011011-E-0000.bin"
private noncomputable def ep1000011011_1 : Blocks := edgeBlocks% "full/vectors/1000011011-E-0001.bin"
private noncomputable def ep1000011011_2 : Blocks := edgeBlocks% "full/vectors/1000011011-E-0002.bin"
noncomputable def ep1000011011 : Blocks := (Blocks.join ep1000011011_0 (Blocks.join ep1000011011_1 ep1000011011_2))
private theorem idp1000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100001101.list =
    C ((2:ℤ)^309) * horner X vp1000011011.list + horner X ep1000011011.list := by
  exact edge_identity (B := (2:ℤ)^492) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000011011 : Branch 1 (-4303761639/16000000 : ℚ) vp100001101 := by
  apply branch_checked idp1000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-4303761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4311761639/8000000 : ℚ) by norm_num]
  exact coverp1000011011
theorem coverp100001101 : Covers (-4303761639/16000000 : ℚ) vp100001101 := join_branches bp1000011010 bp1000011011
private noncomputable def vp10000110011_0 : Blocks := edgeBlocks% "full/vectors/10000110011-V-0000.bin"
noncomputable def vp10000110011 : Blocks := vp10000110011_0
theorem coverp10000110011 : Covers (-4299761639/4000000 : ℚ) vp10000110011 := cover_leaf (by decide +kernel)
private noncomputable def vp10000110010_0 : Blocks := edgeBlocks% "full/vectors/10000110010-V-0000.bin"
noncomputable def vp10000110010 : Blocks := vp10000110010_0
theorem coverp10000110010 : Covers (-4295761639/4000000 : ℚ) vp10000110010 := cover_leaf (by decide +kernel)
private noncomputable def vp1000011001_0 : Blocks := edgeBlocks% "full/vectors/1000011001-V-0000.bin"
private noncomputable def vp1000011001_1 : Blocks := edgeBlocks% "full/vectors/1000011001-V-0001.bin"
noncomputable def vp1000011001 : Blocks := (Blocks.join vp1000011001_0 vp1000011001_1)
private theorem bp10000110010 : Branch 0 (-4295761639/8000000 : ℚ) vp1000011001 := by
  apply branch_left_normalized (c:=vp10000110010) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-4295761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4295761639/4000000 : ℚ) by norm_num]
  exact coverp10000110010
private noncomputable def ep10000110011_0 : Blocks := edgeBlocks% "full/vectors/10000110011-E-0000.bin"
private noncomputable def ep10000110011_1 : Blocks := edgeBlocks% "full/vectors/10000110011-E-0001.bin"
noncomputable def ep10000110011 : Blocks := (Blocks.join ep10000110011_0 ep10000110011_1)
private theorem idp10000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000011001.list =
    C ((2:ℤ)^165) * horner X vp10000110011.list + horner X ep10000110011.list := by
  exact edge_identity (B := (2:ℤ)^307) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000110011 : Branch 1 (-4295761639/8000000 : ℚ) vp1000011001 := by
  apply branch_checked idp10000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-4295761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4299761639/4000000 : ℚ) by norm_num]
  exact coverp10000110011
theorem coverp1000011001 : Covers (-4295761639/8000000 : ℚ) vp1000011001 := join_branches bp10000110010 bp10000110011
private noncomputable def vp10000110001_0 : Blocks := edgeBlocks% "full/vectors/10000110001-V-0000.bin"
noncomputable def vp10000110001 : Blocks := vp10000110001_0
theorem coverp10000110001 : Covers (-4291761639/4000000 : ℚ) vp10000110001 := cover_leaf (by decide +kernel)
private noncomputable def vp10000110000_0 : Blocks := edgeBlocks% "full/vectors/10000110000-V-0000.bin"
noncomputable def vp10000110000 : Blocks := vp10000110000_0
theorem coverp10000110000 : Covers (-4287761639/4000000 : ℚ) vp10000110000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000011000_0 : Blocks := edgeBlocks% "full/vectors/1000011000-V-0000.bin"
private noncomputable def vp1000011000_1 : Blocks := edgeBlocks% "full/vectors/1000011000-V-0001.bin"
noncomputable def vp1000011000 : Blocks := (Blocks.join vp1000011000_0 vp1000011000_1)
private theorem bp10000110000 : Branch 0 (-4287761639/8000000 : ℚ) vp1000011000 := by
  apply branch_left_normalized (c:=vp10000110000) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4287761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4287761639/4000000 : ℚ) by norm_num]
  exact coverp10000110000
private noncomputable def ep10000110001_0 : Blocks := edgeBlocks% "full/vectors/10000110001-E-0000.bin"
private noncomputable def ep10000110001_1 : Blocks := edgeBlocks% "full/vectors/10000110001-E-0001.bin"
noncomputable def ep10000110001 : Blocks := (Blocks.join ep10000110001_0 ep10000110001_1)
private theorem idp10000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000011000.list =
    C ((2:ℤ)^165) * horner X vp10000110001.list + horner X ep10000110001.list := by
  exact edge_identity (B := (2:ℤ)^307) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000110001 : Branch 1 (-4287761639/8000000 : ℚ) vp1000011000 := by
  apply branch_checked idp10000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-4287761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4291761639/4000000 : ℚ) by norm_num]
  exact coverp10000110001
theorem coverp1000011000 : Covers (-4287761639/8000000 : ℚ) vp1000011000 := join_branches bp10000110000 bp10000110001
private noncomputable def vp100001100_0 : Blocks := edgeBlocks% "full/vectors/100001100-V-0000.bin"
private noncomputable def vp100001100_1 : Blocks := edgeBlocks% "full/vectors/100001100-V-0001.bin"
private noncomputable def vp100001100_2 : Blocks := edgeBlocks% "full/vectors/100001100-V-0002.bin"
noncomputable def vp100001100 : Blocks := (Blocks.join vp100001100_0 (Blocks.join vp100001100_1 vp100001100_2))
private theorem bp1000011000 : Branch 0 (-4287761639/16000000 : ℚ) vp100001100 := by
  apply branch_left_normalized (c:=vp1000011000) (k:=0) (m:=141) (by decide +kernel)
  rw [show 2*(-4287761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4287761639/8000000 : ℚ) by norm_num]
  exact coverp1000011000
private noncomputable def ep1000011001_0 : Blocks := edgeBlocks% "full/vectors/1000011001-E-0000.bin"
private noncomputable def ep1000011001_1 : Blocks := edgeBlocks% "full/vectors/1000011001-E-0001.bin"
private noncomputable def ep1000011001_2 : Blocks := edgeBlocks% "full/vectors/1000011001-E-0002.bin"
noncomputable def ep1000011001 : Blocks := (Blocks.join ep1000011001_0 (Blocks.join ep1000011001_1 ep1000011001_2))
private theorem idp1000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100001100.list =
    C ((2:ℤ)^309) * horner X vp1000011001.list + horner X ep1000011001.list := by
  exact edge_identity (B := (2:ℤ)^492) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000011001 : Branch 1 (-4287761639/16000000 : ℚ) vp100001100 := by
  apply branch_checked idp1000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-4287761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4295761639/8000000 : ℚ) by norm_num]
  exact coverp1000011001
theorem coverp100001100 : Covers (-4287761639/16000000 : ℚ) vp100001100 := join_branches bp1000011000 bp1000011001
private noncomputable def vp10000110_0 : Blocks := edgeBlocks% "full/vectors/10000110-V-0000.bin"
private noncomputable def vp10000110_1 : Blocks := edgeBlocks% "full/vectors/10000110-V-0001.bin"
private noncomputable def vp10000110_2 : Blocks := edgeBlocks% "full/vectors/10000110-V-0002.bin"
private noncomputable def vp10000110_3 : Blocks := edgeBlocks% "full/vectors/10000110-V-0003.bin"
noncomputable def vp10000110 : Blocks := (Blocks.join (Blocks.join vp10000110_0 vp10000110_1) (Blocks.join vp10000110_2 vp10000110_3))
private theorem bp100001100 : Branch 0 (-4287761639/32000000 : ℚ) vp10000110 := by
  apply branch_left_normalized (c:=vp100001100) (k:=0) (m:=262) (by decide +kernel)
  rw [show 2*(-4287761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4287761639/16000000 : ℚ) by norm_num]
  exact coverp100001100
private noncomputable def ep100001101_0 : Blocks := edgeBlocks% "full/vectors/100001101-E-0000.bin"
private noncomputable def ep100001101_1 : Blocks := edgeBlocks% "full/vectors/100001101-E-0001.bin"
private noncomputable def ep100001101_2 : Blocks := edgeBlocks% "full/vectors/100001101-E-0002.bin"
private noncomputable def ep100001101_3 : Blocks := edgeBlocks% "full/vectors/100001101-E-0003.bin"
noncomputable def ep100001101 : Blocks := (Blocks.join (Blocks.join ep100001101_0 ep100001101_1) (Blocks.join ep100001101_2 ep100001101_3))
private theorem idp100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10000110.list =
    C ((2:ℤ)^592) * horner X vp100001101.list + horner X ep100001101.list := by
  exact edge_identity (B := (2:ℤ)^856) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100001101 : Branch 1 (-4287761639/32000000 : ℚ) vp10000110 := by
  apply branch_checked idp100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4287761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4303761639/16000000 : ℚ) by norm_num]
  exact coverp100001101
theorem coverp10000110 : Covers (-4287761639/32000000 : ℚ) vp10000110 := join_branches bp100001100 bp100001101
private noncomputable def vp1000011_0 : Blocks := edgeBlocks% "full/vectors/1000011-V-0000.bin"
private noncomputable def vp1000011_1 : Blocks := edgeBlocks% "full/vectors/1000011-V-0001.bin"
private noncomputable def vp1000011_2 : Blocks := edgeBlocks% "full/vectors/1000011-V-0002.bin"
private noncomputable def vp1000011_3 : Blocks := edgeBlocks% "full/vectors/1000011-V-0003.bin"
private noncomputable def vp1000011_4 : Blocks := edgeBlocks% "full/vectors/1000011-V-0004.bin"
private noncomputable def vp1000011_5 : Blocks := edgeBlocks% "full/vectors/1000011-V-0005.bin"
private noncomputable def vp1000011_6 : Blocks := edgeBlocks% "full/vectors/1000011-V-0006.bin"
private noncomputable def vp1000011_7 : Blocks := edgeBlocks% "full/vectors/1000011-V-0007.bin"
noncomputable def vp1000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1000011_0 vp1000011_1) (Blocks.join vp1000011_2 vp1000011_3)) (Blocks.join (Blocks.join vp1000011_4 vp1000011_5) (Blocks.join vp1000011_6 vp1000011_7)))
private theorem bp10000110 : Branch 0 (-4287761639/64000000 : ℚ) vp1000011 := by
  apply branch_left_normalized (c:=vp10000110) (k:=0) (m:=499) (by decide +kernel)
  rw [show 2*(-4287761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4287761639/32000000 : ℚ) by norm_num]
  exact coverp10000110
private noncomputable def ep10000111_0 : Blocks := edgeBlocks% "full/vectors/10000111-E-0000.bin"
private noncomputable def ep10000111_1 : Blocks := edgeBlocks% "full/vectors/10000111-E-0001.bin"
private noncomputable def ep10000111_2 : Blocks := edgeBlocks% "full/vectors/10000111-E-0002.bin"
private noncomputable def ep10000111_3 : Blocks := edgeBlocks% "full/vectors/10000111-E-0003.bin"
private noncomputable def ep10000111_4 : Blocks := edgeBlocks% "full/vectors/10000111-E-0004.bin"
private noncomputable def ep10000111_5 : Blocks := edgeBlocks% "full/vectors/10000111-E-0005.bin"
private noncomputable def ep10000111_6 : Blocks := edgeBlocks% "full/vectors/10000111-E-0006.bin"
private noncomputable def ep10000111_7 : Blocks := edgeBlocks% "full/vectors/10000111-E-0007.bin"
noncomputable def ep10000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10000111_0 ep10000111_1) (Blocks.join ep10000111_2 ep10000111_3)) (Blocks.join (Blocks.join ep10000111_4 ep10000111_5) (Blocks.join ep10000111_6 ep10000111_7)))
private theorem idp10000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000011.list =
    C ((2:ℤ)^1158) * horner X vp10000111.list + horner X ep10000111.list := by
  exact edge_identity (B := (2:ℤ)^1580) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000111 : Branch 1 (-4287761639/64000000 : ℚ) vp1000011 := by
  apply branch_checked idp10000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4287761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4319761639/32000000 : ℚ) by norm_num]
  exact coverp10000111
theorem coverp1000011 : Covers (-4287761639/64000000 : ℚ) vp1000011 := join_branches bp10000110 bp10000111
private noncomputable def vp10000101111_0 : Blocks := edgeBlocks% "full/vectors/10000101111-V-0000.bin"
noncomputable def vp10000101111 : Blocks := vp10000101111_0
theorem coverp10000101111 : Covers (-4283761639/4000000 : ℚ) vp10000101111 := cover_leaf (by decide +kernel)
private noncomputable def vp10000101110_0 : Blocks := edgeBlocks% "full/vectors/10000101110-V-0000.bin"
noncomputable def vp10000101110 : Blocks := vp10000101110_0
theorem coverp10000101110 : Covers (-4279761639/4000000 : ℚ) vp10000101110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000010111_0 : Blocks := edgeBlocks% "full/vectors/1000010111-V-0000.bin"
private noncomputable def vp1000010111_1 : Blocks := edgeBlocks% "full/vectors/1000010111-V-0001.bin"
noncomputable def vp1000010111 : Blocks := (Blocks.join vp1000010111_0 vp1000010111_1)
private theorem bp10000101110 : Branch 0 (-4279761639/8000000 : ℚ) vp1000010111 := by
  apply branch_left_normalized (c:=vp10000101110) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4279761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4279761639/4000000 : ℚ) by norm_num]
  exact coverp10000101110
private noncomputable def ep10000101111_0 : Blocks := edgeBlocks% "full/vectors/10000101111-E-0000.bin"
private noncomputable def ep10000101111_1 : Blocks := edgeBlocks% "full/vectors/10000101111-E-0001.bin"
noncomputable def ep10000101111 : Blocks := (Blocks.join ep10000101111_0 ep10000101111_1)
private theorem idp10000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000010111.list =
    C ((2:ℤ)^166) * horner X vp10000101111.list + horner X ep10000101111.list := by
  exact edge_identity (B := (2:ℤ)^308) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000101111 : Branch 1 (-4279761639/8000000 : ℚ) vp1000010111 := by
  apply branch_checked idp10000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-4279761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4283761639/4000000 : ℚ) by norm_num]
  exact coverp10000101111
theorem coverp1000010111 : Covers (-4279761639/8000000 : ℚ) vp1000010111 := join_branches bp10000101110 bp10000101111
private noncomputable def vp10000101101_0 : Blocks := edgeBlocks% "full/vectors/10000101101-V-0000.bin"
noncomputable def vp10000101101 : Blocks := vp10000101101_0
theorem coverp10000101101 : Covers (-4275761639/4000000 : ℚ) vp10000101101 := cover_leaf (by decide +kernel)
private noncomputable def vp10000101100_0 : Blocks := edgeBlocks% "full/vectors/10000101100-V-0000.bin"
noncomputable def vp10000101100 : Blocks := vp10000101100_0
theorem coverp10000101100 : Covers (-4271761639/4000000 : ℚ) vp10000101100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000010110_0 : Blocks := edgeBlocks% "full/vectors/1000010110-V-0000.bin"
private noncomputable def vp1000010110_1 : Blocks := edgeBlocks% "full/vectors/1000010110-V-0001.bin"
noncomputable def vp1000010110 : Blocks := (Blocks.join vp1000010110_0 vp1000010110_1)
private theorem bp10000101100 : Branch 0 (-4271761639/8000000 : ℚ) vp1000010110 := by
  apply branch_left_normalized (c:=vp10000101100) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-4271761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4271761639/4000000 : ℚ) by norm_num]
  exact coverp10000101100
private noncomputable def ep10000101101_0 : Blocks := edgeBlocks% "full/vectors/10000101101-E-0000.bin"
private noncomputable def ep10000101101_1 : Blocks := edgeBlocks% "full/vectors/10000101101-E-0001.bin"
noncomputable def ep10000101101 : Blocks := (Blocks.join ep10000101101_0 ep10000101101_1)
private theorem idp10000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000010110.list =
    C ((2:ℤ)^166) * horner X vp10000101101.list + horner X ep10000101101.list := by
  exact edge_identity (B := (2:ℤ)^308) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000101101 : Branch 1 (-4271761639/8000000 : ℚ) vp1000010110 := by
  apply branch_checked idp10000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-4271761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4275761639/4000000 : ℚ) by norm_num]
  exact coverp10000101101
theorem coverp1000010110 : Covers (-4271761639/8000000 : ℚ) vp1000010110 := join_branches bp10000101100 bp10000101101
private noncomputable def vp100001011_0 : Blocks := edgeBlocks% "full/vectors/100001011-V-0000.bin"
private noncomputable def vp100001011_1 : Blocks := edgeBlocks% "full/vectors/100001011-V-0001.bin"
private noncomputable def vp100001011_2 : Blocks := edgeBlocks% "full/vectors/100001011-V-0002.bin"
noncomputable def vp100001011 : Blocks := (Blocks.join vp100001011_0 (Blocks.join vp100001011_1 vp100001011_2))
private theorem bp1000010110 : Branch 0 (-4271761639/16000000 : ℚ) vp100001011 := by
  apply branch_left_normalized (c:=vp1000010110) (k:=0) (m:=142) (by decide +kernel)
  rw [show 2*(-4271761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4271761639/8000000 : ℚ) by norm_num]
  exact coverp1000010110
private noncomputable def ep1000010111_0 : Blocks := edgeBlocks% "full/vectors/1000010111-E-0000.bin"
private noncomputable def ep1000010111_1 : Blocks := edgeBlocks% "full/vectors/1000010111-E-0001.bin"
private noncomputable def ep1000010111_2 : Blocks := edgeBlocks% "full/vectors/1000010111-E-0002.bin"
noncomputable def ep1000010111 : Blocks := (Blocks.join ep1000010111_0 (Blocks.join ep1000010111_1 ep1000010111_2))
private theorem idp1000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100001011.list =
    C ((2:ℤ)^309) * horner X vp1000010111.list + horner X ep1000010111.list := by
  exact edge_identity (B := (2:ℤ)^492) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000010111 : Branch 1 (-4271761639/16000000 : ℚ) vp100001011 := by
  apply branch_checked idp1000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-4271761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4279761639/8000000 : ℚ) by norm_num]
  exact coverp1000010111
theorem coverp100001011 : Covers (-4271761639/16000000 : ℚ) vp100001011 := join_branches bp1000010110 bp1000010111
private noncomputable def vp10000101011_0 : Blocks := edgeBlocks% "full/vectors/10000101011-V-0000.bin"
noncomputable def vp10000101011 : Blocks := vp10000101011_0
theorem coverp10000101011 : Covers (-4267761639/4000000 : ℚ) vp10000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp10000101010_0 : Blocks := edgeBlocks% "full/vectors/10000101010-V-0000.bin"
noncomputable def vp10000101010 : Blocks := vp10000101010_0
theorem coverp10000101010 : Covers (-4263761639/4000000 : ℚ) vp10000101010 := cover_leaf (by decide +kernel)
private noncomputable def vp1000010101_0 : Blocks := edgeBlocks% "full/vectors/1000010101-V-0000.bin"
private noncomputable def vp1000010101_1 : Blocks := edgeBlocks% "full/vectors/1000010101-V-0001.bin"
noncomputable def vp1000010101 : Blocks := (Blocks.join vp1000010101_0 vp1000010101_1)
private theorem bp10000101010 : Branch 0 (-4263761639/8000000 : ℚ) vp1000010101 := by
  apply branch_left_normalized (c:=vp10000101010) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4263761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4263761639/4000000 : ℚ) by norm_num]
  exact coverp10000101010
private noncomputable def ep10000101011_0 : Blocks := edgeBlocks% "full/vectors/10000101011-E-0000.bin"
private noncomputable def ep10000101011_1 : Blocks := edgeBlocks% "full/vectors/10000101011-E-0001.bin"
noncomputable def ep10000101011 : Blocks := (Blocks.join ep10000101011_0 ep10000101011_1)
private theorem idp10000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000010101.list =
    C ((2:ℤ)^166) * horner X vp10000101011.list + horner X ep10000101011.list := by
  exact edge_identity (B := (2:ℤ)^308) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000101011 : Branch 1 (-4263761639/8000000 : ℚ) vp1000010101 := by
  apply branch_checked idp10000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-4263761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4267761639/4000000 : ℚ) by norm_num]
  exact coverp10000101011
theorem coverp1000010101 : Covers (-4263761639/8000000 : ℚ) vp1000010101 := join_branches bp10000101010 bp10000101011
private noncomputable def vp10000101001_0 : Blocks := edgeBlocks% "full/vectors/10000101001-V-0000.bin"
noncomputable def vp10000101001 : Blocks := vp10000101001_0
theorem coverp10000101001 : Covers (-4259761639/4000000 : ℚ) vp10000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp10000101000_0 : Blocks := edgeBlocks% "full/vectors/10000101000-V-0000.bin"
noncomputable def vp10000101000 : Blocks := vp10000101000_0
theorem coverp10000101000 : Covers (-4255761639/4000000 : ℚ) vp10000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000010100_0 : Blocks := edgeBlocks% "full/vectors/1000010100-V-0000.bin"
private noncomputable def vp1000010100_1 : Blocks := edgeBlocks% "full/vectors/1000010100-V-0001.bin"
noncomputable def vp1000010100 : Blocks := (Blocks.join vp1000010100_0 vp1000010100_1)
private theorem bp10000101000 : Branch 0 (-4255761639/8000000 : ℚ) vp1000010100 := by
  apply branch_left_normalized (c:=vp10000101000) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4255761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4255761639/4000000 : ℚ) by norm_num]
  exact coverp10000101000
private noncomputable def ep10000101001_0 : Blocks := edgeBlocks% "full/vectors/10000101001-E-0000.bin"
private noncomputable def ep10000101001_1 : Blocks := edgeBlocks% "full/vectors/10000101001-E-0001.bin"
noncomputable def ep10000101001 : Blocks := (Blocks.join ep10000101001_0 ep10000101001_1)
private theorem idp10000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000010100.list =
    C ((2:ℤ)^166) * horner X vp10000101001.list + horner X ep10000101001.list := by
  exact edge_identity (B := (2:ℤ)^309) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000101001 : Branch 1 (-4255761639/8000000 : ℚ) vp1000010100 := by
  apply branch_checked idp10000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-4255761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4259761639/4000000 : ℚ) by norm_num]
  exact coverp10000101001
theorem coverp1000010100 : Covers (-4255761639/8000000 : ℚ) vp1000010100 := join_branches bp10000101000 bp10000101001
private noncomputable def vp100001010_0 : Blocks := edgeBlocks% "full/vectors/100001010-V-0000.bin"
private noncomputable def vp100001010_1 : Blocks := edgeBlocks% "full/vectors/100001010-V-0001.bin"
private noncomputable def vp100001010_2 : Blocks := edgeBlocks% "full/vectors/100001010-V-0002.bin"
noncomputable def vp100001010 : Blocks := (Blocks.join vp100001010_0 (Blocks.join vp100001010_1 vp100001010_2))
private theorem bp1000010100 : Branch 0 (-4255761639/16000000 : ℚ) vp100001010 := by
  apply branch_left_normalized (c:=vp1000010100) (k:=0) (m:=142) (by decide +kernel)
  rw [show 2*(-4255761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4255761639/8000000 : ℚ) by norm_num]
  exact coverp1000010100
private noncomputable def ep1000010101_0 : Blocks := edgeBlocks% "full/vectors/1000010101-E-0000.bin"
private noncomputable def ep1000010101_1 : Blocks := edgeBlocks% "full/vectors/1000010101-E-0001.bin"
private noncomputable def ep1000010101_2 : Blocks := edgeBlocks% "full/vectors/1000010101-E-0002.bin"
noncomputable def ep1000010101 : Blocks := (Blocks.join ep1000010101_0 (Blocks.join ep1000010101_1 ep1000010101_2))
private theorem idp1000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100001010.list =
    C ((2:ℤ)^310) * horner X vp1000010101.list + horner X ep1000010101.list := by
  exact edge_identity (B := (2:ℤ)^493) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000010101 : Branch 1 (-4255761639/16000000 : ℚ) vp100001010 := by
  apply branch_checked idp1000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4255761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4263761639/8000000 : ℚ) by norm_num]
  exact coverp1000010101
theorem coverp100001010 : Covers (-4255761639/16000000 : ℚ) vp100001010 := join_branches bp1000010100 bp1000010101
private noncomputable def vp10000101_0 : Blocks := edgeBlocks% "full/vectors/10000101-V-0000.bin"
private noncomputable def vp10000101_1 : Blocks := edgeBlocks% "full/vectors/10000101-V-0001.bin"
private noncomputable def vp10000101_2 : Blocks := edgeBlocks% "full/vectors/10000101-V-0002.bin"
private noncomputable def vp10000101_3 : Blocks := edgeBlocks% "full/vectors/10000101-V-0003.bin"
noncomputable def vp10000101 : Blocks := (Blocks.join (Blocks.join vp10000101_0 vp10000101_1) (Blocks.join vp10000101_2 vp10000101_3))
private theorem bp100001010 : Branch 0 (-4255761639/32000000 : ℚ) vp10000101 := by
  apply branch_left_normalized (c:=vp100001010) (k:=0) (m:=263) (by decide +kernel)
  rw [show 2*(-4255761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4255761639/16000000 : ℚ) by norm_num]
  exact coverp100001010
private noncomputable def ep100001011_0 : Blocks := edgeBlocks% "full/vectors/100001011-E-0000.bin"
private noncomputable def ep100001011_1 : Blocks := edgeBlocks% "full/vectors/100001011-E-0001.bin"
private noncomputable def ep100001011_2 : Blocks := edgeBlocks% "full/vectors/100001011-E-0002.bin"
private noncomputable def ep100001011_3 : Blocks := edgeBlocks% "full/vectors/100001011-E-0003.bin"
noncomputable def ep100001011 : Blocks := (Blocks.join (Blocks.join ep100001011_0 ep100001011_1) (Blocks.join ep100001011_2 ep100001011_3))
private theorem idp100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10000101.list =
    C ((2:ℤ)^595) * horner X vp100001011.list + horner X ep100001011.list := by
  exact edge_identity (B := (2:ℤ)^859) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100001011 : Branch 1 (-4255761639/32000000 : ℚ) vp10000101 := by
  apply branch_checked idp100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4255761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4271761639/16000000 : ℚ) by norm_num]
  exact coverp100001011
theorem coverp10000101 : Covers (-4255761639/32000000 : ℚ) vp10000101 := join_branches bp100001010 bp100001011
private noncomputable def vp10000100111_0 : Blocks := edgeBlocks% "full/vectors/10000100111-V-0000.bin"
noncomputable def vp10000100111 : Blocks := vp10000100111_0
theorem coverp10000100111 : Covers (-4251761639/4000000 : ℚ) vp10000100111 := cover_leaf (by decide +kernel)
private noncomputable def vp10000100110_0 : Blocks := edgeBlocks% "full/vectors/10000100110-V-0000.bin"
noncomputable def vp10000100110 : Blocks := vp10000100110_0
theorem coverp10000100110 : Covers (-4247761639/4000000 : ℚ) vp10000100110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000010011_0 : Blocks := edgeBlocks% "full/vectors/1000010011-V-0000.bin"
private noncomputable def vp1000010011_1 : Blocks := edgeBlocks% "full/vectors/1000010011-V-0001.bin"
noncomputable def vp1000010011 : Blocks := (Blocks.join vp1000010011_0 vp1000010011_1)
private theorem bp10000100110 : Branch 0 (-4247761639/8000000 : ℚ) vp1000010011 := by
  apply branch_left_normalized (c:=vp10000100110) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4247761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4247761639/4000000 : ℚ) by norm_num]
  exact coverp10000100110
private noncomputable def ep10000100111_0 : Blocks := edgeBlocks% "full/vectors/10000100111-E-0000.bin"
private noncomputable def ep10000100111_1 : Blocks := edgeBlocks% "full/vectors/10000100111-E-0001.bin"
noncomputable def ep10000100111 : Blocks := (Blocks.join ep10000100111_0 ep10000100111_1)
private theorem idp10000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000010011.list =
    C ((2:ℤ)^166) * horner X vp10000100111.list + horner X ep10000100111.list := by
  exact edge_identity (B := (2:ℤ)^308) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000100111 : Branch 1 (-4247761639/8000000 : ℚ) vp1000010011 := by
  apply branch_checked idp10000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-4247761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4251761639/4000000 : ℚ) by norm_num]
  exact coverp10000100111
theorem coverp1000010011 : Covers (-4247761639/8000000 : ℚ) vp1000010011 := join_branches bp10000100110 bp10000100111
private noncomputable def vp10000100101_0 : Blocks := edgeBlocks% "full/vectors/10000100101-V-0000.bin"
noncomputable def vp10000100101 : Blocks := vp10000100101_0
theorem coverp10000100101 : Covers (-4243761639/4000000 : ℚ) vp10000100101 := cover_leaf (by decide +kernel)
private noncomputable def vp10000100100_0 : Blocks := edgeBlocks% "full/vectors/10000100100-V-0000.bin"
noncomputable def vp10000100100 : Blocks := vp10000100100_0
theorem coverp10000100100 : Covers (-4239761639/4000000 : ℚ) vp10000100100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000010010_0 : Blocks := edgeBlocks% "full/vectors/1000010010-V-0000.bin"
private noncomputable def vp1000010010_1 : Blocks := edgeBlocks% "full/vectors/1000010010-V-0001.bin"
noncomputable def vp1000010010 : Blocks := (Blocks.join vp1000010010_0 vp1000010010_1)
private theorem bp10000100100 : Branch 0 (-4239761639/8000000 : ℚ) vp1000010010 := by
  apply branch_left_normalized (c:=vp10000100100) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4239761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4239761639/4000000 : ℚ) by norm_num]
  exact coverp10000100100
private noncomputable def ep10000100101_0 : Blocks := edgeBlocks% "full/vectors/10000100101-E-0000.bin"
private noncomputable def ep10000100101_1 : Blocks := edgeBlocks% "full/vectors/10000100101-E-0001.bin"
noncomputable def ep10000100101 : Blocks := (Blocks.join ep10000100101_0 ep10000100101_1)
private theorem idp10000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000010010.list =
    C ((2:ℤ)^166) * horner X vp10000100101.list + horner X ep10000100101.list := by
  exact edge_identity (B := (2:ℤ)^308) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000100101 : Branch 1 (-4239761639/8000000 : ℚ) vp1000010010 := by
  apply branch_checked idp10000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-4239761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4243761639/4000000 : ℚ) by norm_num]
  exact coverp10000100101
theorem coverp1000010010 : Covers (-4239761639/8000000 : ℚ) vp1000010010 := join_branches bp10000100100 bp10000100101
private noncomputable def vp100001001_0 : Blocks := edgeBlocks% "full/vectors/100001001-V-0000.bin"
private noncomputable def vp100001001_1 : Blocks := edgeBlocks% "full/vectors/100001001-V-0001.bin"
private noncomputable def vp100001001_2 : Blocks := edgeBlocks% "full/vectors/100001001-V-0002.bin"
noncomputable def vp100001001 : Blocks := (Blocks.join vp100001001_0 (Blocks.join vp100001001_1 vp100001001_2))
private theorem bp1000010010 : Branch 0 (-4239761639/16000000 : ℚ) vp100001001 := by
  apply branch_left_normalized (c:=vp1000010010) (k:=0) (m:=142) (by decide +kernel)
  rw [show 2*(-4239761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4239761639/8000000 : ℚ) by norm_num]
  exact coverp1000010010
private noncomputable def ep1000010011_0 : Blocks := edgeBlocks% "full/vectors/1000010011-E-0000.bin"
private noncomputable def ep1000010011_1 : Blocks := edgeBlocks% "full/vectors/1000010011-E-0001.bin"
private noncomputable def ep1000010011_2 : Blocks := edgeBlocks% "full/vectors/1000010011-E-0002.bin"
noncomputable def ep1000010011 : Blocks := (Blocks.join ep1000010011_0 (Blocks.join ep1000010011_1 ep1000010011_2))
private theorem idp1000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100001001.list =
    C ((2:ℤ)^310) * horner X vp1000010011.list + horner X ep1000010011.list := by
  exact edge_identity (B := (2:ℤ)^493) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000010011 : Branch 1 (-4239761639/16000000 : ℚ) vp100001001 := by
  apply branch_checked idp1000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4239761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4247761639/8000000 : ℚ) by norm_num]
  exact coverp1000010011
theorem coverp100001001 : Covers (-4239761639/16000000 : ℚ) vp100001001 := join_branches bp1000010010 bp1000010011
private noncomputable def vp10000100011_0 : Blocks := edgeBlocks% "full/vectors/10000100011-V-0000.bin"
noncomputable def vp10000100011 : Blocks := vp10000100011_0
theorem coverp10000100011 : Covers (-4235761639/4000000 : ℚ) vp10000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp10000100010_0 : Blocks := edgeBlocks% "full/vectors/10000100010-V-0000.bin"
noncomputable def vp10000100010 : Blocks := vp10000100010_0
theorem coverp10000100010 : Covers (-4231761639/4000000 : ℚ) vp10000100010 := cover_leaf (by decide +kernel)
private noncomputable def vp1000010001_0 : Blocks := edgeBlocks% "full/vectors/1000010001-V-0000.bin"
private noncomputable def vp1000010001_1 : Blocks := edgeBlocks% "full/vectors/1000010001-V-0001.bin"
noncomputable def vp1000010001 : Blocks := (Blocks.join vp1000010001_0 vp1000010001_1)
private theorem bp10000100010 : Branch 0 (-4231761639/8000000 : ℚ) vp1000010001 := by
  apply branch_left_normalized (c:=vp10000100010) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-4231761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4231761639/4000000 : ℚ) by norm_num]
  exact coverp10000100010
private noncomputable def ep10000100011_0 : Blocks := edgeBlocks% "full/vectors/10000100011-E-0000.bin"
private noncomputable def ep10000100011_1 : Blocks := edgeBlocks% "full/vectors/10000100011-E-0001.bin"
noncomputable def ep10000100011 : Blocks := (Blocks.join ep10000100011_0 ep10000100011_1)
private theorem idp10000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000010001.list =
    C ((2:ℤ)^166) * horner X vp10000100011.list + horner X ep10000100011.list := by
  exact edge_identity (B := (2:ℤ)^308) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000100011 : Branch 1 (-4231761639/8000000 : ℚ) vp1000010001 := by
  apply branch_checked idp10000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-4231761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4235761639/4000000 : ℚ) by norm_num]
  exact coverp10000100011
theorem coverp1000010001 : Covers (-4231761639/8000000 : ℚ) vp1000010001 := join_branches bp10000100010 bp10000100011
private noncomputable def vp10000100001_0 : Blocks := edgeBlocks% "full/vectors/10000100001-V-0000.bin"
noncomputable def vp10000100001 : Blocks := vp10000100001_0
theorem coverp10000100001 : Covers (-4227761639/4000000 : ℚ) vp10000100001 := cover_leaf (by decide +kernel)
private noncomputable def vp10000100000_0 : Blocks := edgeBlocks% "full/vectors/10000100000-V-0000.bin"
noncomputable def vp10000100000 : Blocks := vp10000100000_0
theorem coverp10000100000 : Covers (-4223761639/4000000 : ℚ) vp10000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000010000_0 : Blocks := edgeBlocks% "full/vectors/1000010000-V-0000.bin"
private noncomputable def vp1000010000_1 : Blocks := edgeBlocks% "full/vectors/1000010000-V-0001.bin"
noncomputable def vp1000010000 : Blocks := (Blocks.join vp1000010000_0 vp1000010000_1)
private theorem bp10000100000 : Branch 0 (-4223761639/8000000 : ℚ) vp1000010000 := by
  apply branch_left_normalized (c:=vp10000100000) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4223761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4223761639/4000000 : ℚ) by norm_num]
  exact coverp10000100000
private noncomputable def ep10000100001_0 : Blocks := edgeBlocks% "full/vectors/10000100001-E-0000.bin"
private noncomputable def ep10000100001_1 : Blocks := edgeBlocks% "full/vectors/10000100001-E-0001.bin"
noncomputable def ep10000100001 : Blocks := (Blocks.join ep10000100001_0 ep10000100001_1)
private theorem idp10000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000010000.list =
    C ((2:ℤ)^167) * horner X vp10000100001.list + horner X ep10000100001.list := by
  exact edge_identity (B := (2:ℤ)^309) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000100001 : Branch 1 (-4223761639/8000000 : ℚ) vp1000010000 := by
  apply branch_checked idp10000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-4223761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4227761639/4000000 : ℚ) by norm_num]
  exact coverp10000100001
theorem coverp1000010000 : Covers (-4223761639/8000000 : ℚ) vp1000010000 := join_branches bp10000100000 bp10000100001
private noncomputable def vp100001000_0 : Blocks := edgeBlocks% "full/vectors/100001000-V-0000.bin"
private noncomputable def vp100001000_1 : Blocks := edgeBlocks% "full/vectors/100001000-V-0001.bin"
private noncomputable def vp100001000_2 : Blocks := edgeBlocks% "full/vectors/100001000-V-0002.bin"
noncomputable def vp100001000 : Blocks := (Blocks.join vp100001000_0 (Blocks.join vp100001000_1 vp100001000_2))
private theorem bp1000010000 : Branch 0 (-4223761639/16000000 : ℚ) vp100001000 := by
  apply branch_left_normalized (c:=vp1000010000) (k:=0) (m:=143) (by decide +kernel)
  rw [show 2*(-4223761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4223761639/8000000 : ℚ) by norm_num]
  exact coverp1000010000
private noncomputable def ep1000010001_0 : Blocks := edgeBlocks% "full/vectors/1000010001-E-0000.bin"
private noncomputable def ep1000010001_1 : Blocks := edgeBlocks% "full/vectors/1000010001-E-0001.bin"
private noncomputable def ep1000010001_2 : Blocks := edgeBlocks% "full/vectors/1000010001-E-0002.bin"
noncomputable def ep1000010001 : Blocks := (Blocks.join ep1000010001_0 (Blocks.join ep1000010001_1 ep1000010001_2))
private theorem idp1000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100001000.list =
    C ((2:ℤ)^310) * horner X vp1000010001.list + horner X ep1000010001.list := by
  exact edge_identity (B := (2:ℤ)^493) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000010001 : Branch 1 (-4223761639/16000000 : ℚ) vp100001000 := by
  apply branch_checked idp1000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4223761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4231761639/8000000 : ℚ) by norm_num]
  exact coverp1000010001
theorem coverp100001000 : Covers (-4223761639/16000000 : ℚ) vp100001000 := join_branches bp1000010000 bp1000010001
private noncomputable def vp10000100_0 : Blocks := edgeBlocks% "full/vectors/10000100-V-0000.bin"
private noncomputable def vp10000100_1 : Blocks := edgeBlocks% "full/vectors/10000100-V-0001.bin"
private noncomputable def vp10000100_2 : Blocks := edgeBlocks% "full/vectors/10000100-V-0002.bin"
private noncomputable def vp10000100_3 : Blocks := edgeBlocks% "full/vectors/10000100-V-0003.bin"
noncomputable def vp10000100 : Blocks := (Blocks.join (Blocks.join vp10000100_0 vp10000100_1) (Blocks.join vp10000100_2 vp10000100_3))
private theorem bp100001000 : Branch 0 (-4223761639/32000000 : ℚ) vp10000100 := by
  apply branch_left_normalized (c:=vp100001000) (k:=0) (m:=263) (by decide +kernel)
  rw [show 2*(-4223761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4223761639/16000000 : ℚ) by norm_num]
  exact coverp100001000
private noncomputable def ep100001001_0 : Blocks := edgeBlocks% "full/vectors/100001001-E-0000.bin"
private noncomputable def ep100001001_1 : Blocks := edgeBlocks% "full/vectors/100001001-E-0001.bin"
private noncomputable def ep100001001_2 : Blocks := edgeBlocks% "full/vectors/100001001-E-0002.bin"
private noncomputable def ep100001001_3 : Blocks := edgeBlocks% "full/vectors/100001001-E-0003.bin"
noncomputable def ep100001001 : Blocks := (Blocks.join (Blocks.join ep100001001_0 ep100001001_1) (Blocks.join ep100001001_2 ep100001001_3))
private theorem idp100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10000100.list =
    C ((2:ℤ)^596) * horner X vp100001001.list + horner X ep100001001.list := by
  exact edge_identity (B := (2:ℤ)^861) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100001001 : Branch 1 (-4223761639/32000000 : ℚ) vp10000100 := by
  apply branch_checked idp100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4223761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4239761639/16000000 : ℚ) by norm_num]
  exact coverp100001001
theorem coverp10000100 : Covers (-4223761639/32000000 : ℚ) vp10000100 := join_branches bp100001000 bp100001001
private noncomputable def vp1000010_0 : Blocks := edgeBlocks% "full/vectors/1000010-V-0000.bin"
private noncomputable def vp1000010_1 : Blocks := edgeBlocks% "full/vectors/1000010-V-0001.bin"
private noncomputable def vp1000010_2 : Blocks := edgeBlocks% "full/vectors/1000010-V-0002.bin"
private noncomputable def vp1000010_3 : Blocks := edgeBlocks% "full/vectors/1000010-V-0003.bin"
private noncomputable def vp1000010_4 : Blocks := edgeBlocks% "full/vectors/1000010-V-0004.bin"
private noncomputable def vp1000010_5 : Blocks := edgeBlocks% "full/vectors/1000010-V-0005.bin"
private noncomputable def vp1000010_6 : Blocks := edgeBlocks% "full/vectors/1000010-V-0006.bin"
private noncomputable def vp1000010_7 : Blocks := edgeBlocks% "full/vectors/1000010-V-0007.bin"
noncomputable def vp1000010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1000010_0 vp1000010_1) (Blocks.join vp1000010_2 vp1000010_3)) (Blocks.join (Blocks.join vp1000010_4 vp1000010_5) (Blocks.join vp1000010_6 vp1000010_7)))
private theorem bp10000100 : Branch 0 (-4223761639/64000000 : ℚ) vp1000010 := by
  apply branch_left_normalized (c:=vp10000100) (k:=0) (m:=503) (by decide +kernel)
  rw [show 2*(-4223761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4223761639/32000000 : ℚ) by norm_num]
  exact coverp10000100
private noncomputable def ep10000101_0 : Blocks := edgeBlocks% "full/vectors/10000101-E-0000.bin"
private noncomputable def ep10000101_1 : Blocks := edgeBlocks% "full/vectors/10000101-E-0001.bin"
private noncomputable def ep10000101_2 : Blocks := edgeBlocks% "full/vectors/10000101-E-0002.bin"
private noncomputable def ep10000101_3 : Blocks := edgeBlocks% "full/vectors/10000101-E-0003.bin"
private noncomputable def ep10000101_4 : Blocks := edgeBlocks% "full/vectors/10000101-E-0004.bin"
private noncomputable def ep10000101_5 : Blocks := edgeBlocks% "full/vectors/10000101-E-0005.bin"
private noncomputable def ep10000101_6 : Blocks := edgeBlocks% "full/vectors/10000101-E-0006.bin"
private noncomputable def ep10000101_7 : Blocks := edgeBlocks% "full/vectors/10000101-E-0007.bin"
noncomputable def ep10000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10000101_0 ep10000101_1) (Blocks.join ep10000101_2 ep10000101_3)) (Blocks.join (Blocks.join ep10000101_4 ep10000101_5) (Blocks.join ep10000101_6 ep10000101_7)))
private theorem idp10000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000010.list =
    C ((2:ℤ)^1162) * horner X vp10000101.list + horner X ep10000101.list := by
  exact edge_identity (B := (2:ℤ)^1590) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000101 : Branch 1 (-4223761639/64000000 : ℚ) vp1000010 := by
  apply branch_checked idp10000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4223761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4255761639/32000000 : ℚ) by norm_num]
  exact coverp10000101
theorem coverp1000010 : Covers (-4223761639/64000000 : ℚ) vp1000010 := join_branches bp10000100 bp10000101
private noncomputable def vp100001_0 : Blocks := edgeBlocks% "full/vectors/100001-V-0000.bin"
private noncomputable def vp100001_1 : Blocks := edgeBlocks% "full/vectors/100001-V-0001.bin"
private noncomputable def vp100001_2 : Blocks := edgeBlocks% "full/vectors/100001-V-0002.bin"
private noncomputable def vp100001_3 : Blocks := edgeBlocks% "full/vectors/100001-V-0003.bin"
private noncomputable def vp100001_4 : Blocks := edgeBlocks% "full/vectors/100001-V-0004.bin"
private noncomputable def vp100001_5 : Blocks := edgeBlocks% "full/vectors/100001-V-0005.bin"
private noncomputable def vp100001_6 : Blocks := edgeBlocks% "full/vectors/100001-V-0006.bin"
private noncomputable def vp100001_7 : Blocks := edgeBlocks% "full/vectors/100001-V-0007.bin"
private noncomputable def vp100001_8 : Blocks := edgeBlocks% "full/vectors/100001-V-0008.bin"
private noncomputable def vp100001_9 : Blocks := edgeBlocks% "full/vectors/100001-V-0009.bin"
private noncomputable def vp100001_10 : Blocks := edgeBlocks% "full/vectors/100001-V-0010.bin"
private noncomputable def vp100001_11 : Blocks := edgeBlocks% "full/vectors/100001-V-0011.bin"
private noncomputable def vp100001_12 : Blocks := edgeBlocks% "full/vectors/100001-V-0012.bin"
private noncomputable def vp100001_13 : Blocks := edgeBlocks% "full/vectors/100001-V-0013.bin"
private noncomputable def vp100001_14 : Blocks := edgeBlocks% "full/vectors/100001-V-0014.bin"
noncomputable def vp100001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp100001_0 (Blocks.join vp100001_1 vp100001_2)) (Blocks.join (Blocks.join vp100001_3 vp100001_4) (Blocks.join vp100001_5 vp100001_6))) (Blocks.join (Blocks.join (Blocks.join vp100001_7 vp100001_8) (Blocks.join vp100001_9 vp100001_10)) (Blocks.join (Blocks.join vp100001_11 vp100001_12) (Blocks.join vp100001_13 vp100001_14))))
private theorem bp1000010 : Branch 0 (-4223761639/128000000 : ℚ) vp100001 := by
  apply branch_left_normalized (c:=vp1000010) (k:=0) (m:=977) (by decide +kernel)
  rw [show 2*(-4223761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-4223761639/64000000 : ℚ) by norm_num]
  exact coverp1000010
private noncomputable def ep1000011_0 : Blocks := edgeBlocks% "full/vectors/1000011-E-0000.bin"
private noncomputable def ep1000011_1 : Blocks := edgeBlocks% "full/vectors/1000011-E-0001.bin"
private noncomputable def ep1000011_2 : Blocks := edgeBlocks% "full/vectors/1000011-E-0002.bin"
private noncomputable def ep1000011_3 : Blocks := edgeBlocks% "full/vectors/1000011-E-0003.bin"
private noncomputable def ep1000011_4 : Blocks := edgeBlocks% "full/vectors/1000011-E-0004.bin"
private noncomputable def ep1000011_5 : Blocks := edgeBlocks% "full/vectors/1000011-E-0005.bin"
private noncomputable def ep1000011_6 : Blocks := edgeBlocks% "full/vectors/1000011-E-0006.bin"
private noncomputable def ep1000011_7 : Blocks := edgeBlocks% "full/vectors/1000011-E-0007.bin"
private noncomputable def ep1000011_8 : Blocks := edgeBlocks% "full/vectors/1000011-E-0008.bin"
private noncomputable def ep1000011_9 : Blocks := edgeBlocks% "full/vectors/1000011-E-0009.bin"
private noncomputable def ep1000011_10 : Blocks := edgeBlocks% "full/vectors/1000011-E-0010.bin"
private noncomputable def ep1000011_11 : Blocks := edgeBlocks% "full/vectors/1000011-E-0011.bin"
private noncomputable def ep1000011_12 : Blocks := edgeBlocks% "full/vectors/1000011-E-0012.bin"
private noncomputable def ep1000011_13 : Blocks := edgeBlocks% "full/vectors/1000011-E-0013.bin"
private noncomputable def ep1000011_14 : Blocks := edgeBlocks% "full/vectors/1000011-E-0014.bin"
noncomputable def ep1000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1000011_0 (Blocks.join ep1000011_1 ep1000011_2)) (Blocks.join (Blocks.join ep1000011_3 ep1000011_4) (Blocks.join ep1000011_5 ep1000011_6))) (Blocks.join (Blocks.join (Blocks.join ep1000011_7 ep1000011_8) (Blocks.join ep1000011_9 ep1000011_10)) (Blocks.join (Blocks.join ep1000011_11 ep1000011_12) (Blocks.join ep1000011_13 ep1000011_14))))
private theorem idp1000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100001.list =
    C ((2:ℤ)^2273) * horner X vp1000011.list + horner X ep1000011.list := by
  exact edge_identity (B := (2:ℤ)^3022) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000011 : Branch 1 (-4223761639/128000000 : ℚ) vp100001 := by
  apply branch_checked idp1000011 (by positivity) (by decide +kernel)
  rw [show 2*(-4223761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-4287761639/64000000 : ℚ) by norm_num]
  exact coverp1000011
theorem coverp100001 : Covers (-4223761639/128000000 : ℚ) vp100001 := join_branches bp1000010 bp1000011
private noncomputable def vp10000011111_0 : Blocks := edgeBlocks% "full/vectors/10000011111-V-0000.bin"
noncomputable def vp10000011111 : Blocks := vp10000011111_0
theorem coverp10000011111 : Covers (-4219761639/4000000 : ℚ) vp10000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp10000011110_0 : Blocks := edgeBlocks% "full/vectors/10000011110-V-0000.bin"
noncomputable def vp10000011110 : Blocks := vp10000011110_0
theorem coverp10000011110 : Covers (-4215761639/4000000 : ℚ) vp10000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000001111_0 : Blocks := edgeBlocks% "full/vectors/1000001111-V-0000.bin"
private noncomputable def vp1000001111_1 : Blocks := edgeBlocks% "full/vectors/1000001111-V-0001.bin"
noncomputable def vp1000001111 : Blocks := (Blocks.join vp1000001111_0 vp1000001111_1)
private theorem bp10000011110 : Branch 0 (-4215761639/8000000 : ℚ) vp1000001111 := by
  apply branch_left_normalized (c:=vp10000011110) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4215761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4215761639/4000000 : ℚ) by norm_num]
  exact coverp10000011110
private noncomputable def ep10000011111_0 : Blocks := edgeBlocks% "full/vectors/10000011111-E-0000.bin"
private noncomputable def ep10000011111_1 : Blocks := edgeBlocks% "full/vectors/10000011111-E-0001.bin"
noncomputable def ep10000011111 : Blocks := (Blocks.join ep10000011111_0 ep10000011111_1)
private theorem idp10000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000001111.list =
    C ((2:ℤ)^168) * horner X vp10000011111.list + horner X ep10000011111.list := by
  exact edge_identity (B := (2:ℤ)^310) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000011111 : Branch 1 (-4215761639/8000000 : ℚ) vp1000001111 := by
  apply branch_checked idp10000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-4215761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4219761639/4000000 : ℚ) by norm_num]
  exact coverp10000011111
theorem coverp1000001111 : Covers (-4215761639/8000000 : ℚ) vp1000001111 := join_branches bp10000011110 bp10000011111
private noncomputable def vp10000011101_0 : Blocks := edgeBlocks% "full/vectors/10000011101-V-0000.bin"
noncomputable def vp10000011101 : Blocks := vp10000011101_0
theorem coverp10000011101 : Covers (-4211761639/4000000 : ℚ) vp10000011101 := cover_leaf (by decide +kernel)
private noncomputable def vp10000011100_0 : Blocks := edgeBlocks% "full/vectors/10000011100-V-0000.bin"
noncomputable def vp10000011100 : Blocks := vp10000011100_0
theorem coverp10000011100 : Covers (-4207761639/4000000 : ℚ) vp10000011100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000001110_0 : Blocks := edgeBlocks% "full/vectors/1000001110-V-0000.bin"
private noncomputable def vp1000001110_1 : Blocks := edgeBlocks% "full/vectors/1000001110-V-0001.bin"
noncomputable def vp1000001110 : Blocks := (Blocks.join vp1000001110_0 vp1000001110_1)
private theorem bp10000011100 : Branch 0 (-4207761639/8000000 : ℚ) vp1000001110 := by
  apply branch_left_normalized (c:=vp10000011100) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4207761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4207761639/4000000 : ℚ) by norm_num]
  exact coverp10000011100
private noncomputable def ep10000011101_0 : Blocks := edgeBlocks% "full/vectors/10000011101-E-0000.bin"
private noncomputable def ep10000011101_1 : Blocks := edgeBlocks% "full/vectors/10000011101-E-0001.bin"
noncomputable def ep10000011101 : Blocks := (Blocks.join ep10000011101_0 ep10000011101_1)
private theorem idp10000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000001110.list =
    C ((2:ℤ)^167) * horner X vp10000011101.list + horner X ep10000011101.list := by
  exact edge_identity (B := (2:ℤ)^310) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000011101 : Branch 1 (-4207761639/8000000 : ℚ) vp1000001110 := by
  apply branch_checked idp10000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-4207761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4211761639/4000000 : ℚ) by norm_num]
  exact coverp10000011101
theorem coverp1000001110 : Covers (-4207761639/8000000 : ℚ) vp1000001110 := join_branches bp10000011100 bp10000011101
private noncomputable def vp100000111_0 : Blocks := edgeBlocks% "full/vectors/100000111-V-0000.bin"
private noncomputable def vp100000111_1 : Blocks := edgeBlocks% "full/vectors/100000111-V-0001.bin"
private noncomputable def vp100000111_2 : Blocks := edgeBlocks% "full/vectors/100000111-V-0002.bin"
noncomputable def vp100000111 : Blocks := (Blocks.join vp100000111_0 (Blocks.join vp100000111_1 vp100000111_2))
private theorem bp1000001110 : Branch 0 (-4207761639/16000000 : ℚ) vp100000111 := by
  apply branch_left_normalized (c:=vp1000001110) (k:=0) (m:=143) (by decide +kernel)
  rw [show 2*(-4207761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4207761639/8000000 : ℚ) by norm_num]
  exact coverp1000001110
private noncomputable def ep1000001111_0 : Blocks := edgeBlocks% "full/vectors/1000001111-E-0000.bin"
private noncomputable def ep1000001111_1 : Blocks := edgeBlocks% "full/vectors/1000001111-E-0001.bin"
private noncomputable def ep1000001111_2 : Blocks := edgeBlocks% "full/vectors/1000001111-E-0002.bin"
noncomputable def ep1000001111 : Blocks := (Blocks.join ep1000001111_0 (Blocks.join ep1000001111_1 ep1000001111_2))
private theorem idp1000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100000111.list =
    C ((2:ℤ)^311) * horner X vp1000001111.list + horner X ep1000001111.list := by
  exact edge_identity (B := (2:ℤ)^495) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000001111 : Branch 1 (-4207761639/16000000 : ℚ) vp100000111 := by
  apply branch_checked idp1000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4207761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4215761639/8000000 : ℚ) by norm_num]
  exact coverp1000001111
theorem coverp100000111 : Covers (-4207761639/16000000 : ℚ) vp100000111 := join_branches bp1000001110 bp1000001111
private noncomputable def vp10000011011_0 : Blocks := edgeBlocks% "full/vectors/10000011011-V-0000.bin"
noncomputable def vp10000011011 : Blocks := vp10000011011_0
theorem coverp10000011011 : Covers (-4203761639/4000000 : ℚ) vp10000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp10000011010_0 : Blocks := edgeBlocks% "full/vectors/10000011010-V-0000.bin"
noncomputable def vp10000011010 : Blocks := vp10000011010_0
theorem coverp10000011010 : Covers (-4199761639/4000000 : ℚ) vp10000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp1000001101_0 : Blocks := edgeBlocks% "full/vectors/1000001101-V-0000.bin"
private noncomputable def vp1000001101_1 : Blocks := edgeBlocks% "full/vectors/1000001101-V-0001.bin"
noncomputable def vp1000001101 : Blocks := (Blocks.join vp1000001101_0 vp1000001101_1)
private theorem bp10000011010 : Branch 0 (-4199761639/8000000 : ℚ) vp1000001101 := by
  apply branch_left_normalized (c:=vp10000011010) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4199761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4199761639/4000000 : ℚ) by norm_num]
  exact coverp10000011010
private noncomputable def ep10000011011_0 : Blocks := edgeBlocks% "full/vectors/10000011011-E-0000.bin"
private noncomputable def ep10000011011_1 : Blocks := edgeBlocks% "full/vectors/10000011011-E-0001.bin"
noncomputable def ep10000011011 : Blocks := (Blocks.join ep10000011011_0 ep10000011011_1)
private theorem idp10000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000001101.list =
    C ((2:ℤ)^167) * horner X vp10000011011.list + horner X ep10000011011.list := by
  exact edge_identity (B := (2:ℤ)^310) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000011011 : Branch 1 (-4199761639/8000000 : ℚ) vp1000001101 := by
  apply branch_checked idp10000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-4199761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4203761639/4000000 : ℚ) by norm_num]
  exact coverp10000011011
theorem coverp1000001101 : Covers (-4199761639/8000000 : ℚ) vp1000001101 := join_branches bp10000011010 bp10000011011
private noncomputable def vp10000011001_0 : Blocks := edgeBlocks% "full/vectors/10000011001-V-0000.bin"
noncomputable def vp10000011001 : Blocks := vp10000011001_0
theorem coverp10000011001 : Covers (-4195761639/4000000 : ℚ) vp10000011001 := cover_leaf (by decide +kernel)
private noncomputable def vp10000011000_0 : Blocks := edgeBlocks% "full/vectors/10000011000-V-0000.bin"
noncomputable def vp10000011000 : Blocks := vp10000011000_0
theorem coverp10000011000 : Covers (-4191761639/4000000 : ℚ) vp10000011000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000001100_0 : Blocks := edgeBlocks% "full/vectors/1000001100-V-0000.bin"
private noncomputable def vp1000001100_1 : Blocks := edgeBlocks% "full/vectors/1000001100-V-0001.bin"
noncomputable def vp1000001100 : Blocks := (Blocks.join vp1000001100_0 vp1000001100_1)
private theorem bp10000011000 : Branch 0 (-4191761639/8000000 : ℚ) vp1000001100 := by
  apply branch_left_normalized (c:=vp10000011000) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4191761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4191761639/4000000 : ℚ) by norm_num]
  exact coverp10000011000
private noncomputable def ep10000011001_0 : Blocks := edgeBlocks% "full/vectors/10000011001-E-0000.bin"
private noncomputable def ep10000011001_1 : Blocks := edgeBlocks% "full/vectors/10000011001-E-0001.bin"
noncomputable def ep10000011001 : Blocks := (Blocks.join ep10000011001_0 ep10000011001_1)
private theorem idp10000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000001100.list =
    C ((2:ℤ)^167) * horner X vp10000011001.list + horner X ep10000011001.list := by
  exact edge_identity (B := (2:ℤ)^310) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000011001 : Branch 1 (-4191761639/8000000 : ℚ) vp1000001100 := by
  apply branch_checked idp10000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-4191761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4195761639/4000000 : ℚ) by norm_num]
  exact coverp10000011001
theorem coverp1000001100 : Covers (-4191761639/8000000 : ℚ) vp1000001100 := join_branches bp10000011000 bp10000011001
private noncomputable def vp100000110_0 : Blocks := edgeBlocks% "full/vectors/100000110-V-0000.bin"
private noncomputable def vp100000110_1 : Blocks := edgeBlocks% "full/vectors/100000110-V-0001.bin"
private noncomputable def vp100000110_2 : Blocks := edgeBlocks% "full/vectors/100000110-V-0002.bin"
noncomputable def vp100000110 : Blocks := (Blocks.join vp100000110_0 (Blocks.join vp100000110_1 vp100000110_2))
private theorem bp1000001100 : Branch 0 (-4191761639/16000000 : ℚ) vp100000110 := by
  apply branch_left_normalized (c:=vp1000001100) (k:=0) (m:=143) (by decide +kernel)
  rw [show 2*(-4191761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4191761639/8000000 : ℚ) by norm_num]
  exact coverp1000001100
private noncomputable def ep1000001101_0 : Blocks := edgeBlocks% "full/vectors/1000001101-E-0000.bin"
private noncomputable def ep1000001101_1 : Blocks := edgeBlocks% "full/vectors/1000001101-E-0001.bin"
private noncomputable def ep1000001101_2 : Blocks := edgeBlocks% "full/vectors/1000001101-E-0002.bin"
noncomputable def ep1000001101 : Blocks := (Blocks.join ep1000001101_0 (Blocks.join ep1000001101_1 ep1000001101_2))
private theorem idp1000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100000110.list =
    C ((2:ℤ)^311) * horner X vp1000001101.list + horner X ep1000001101.list := by
  exact edge_identity (B := (2:ℤ)^495) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000001101 : Branch 1 (-4191761639/16000000 : ℚ) vp100000110 := by
  apply branch_checked idp1000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4191761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4199761639/8000000 : ℚ) by norm_num]
  exact coverp1000001101
theorem coverp100000110 : Covers (-4191761639/16000000 : ℚ) vp100000110 := join_branches bp1000001100 bp1000001101
private noncomputable def vp10000011_0 : Blocks := edgeBlocks% "full/vectors/10000011-V-0000.bin"
private noncomputable def vp10000011_1 : Blocks := edgeBlocks% "full/vectors/10000011-V-0001.bin"
private noncomputable def vp10000011_2 : Blocks := edgeBlocks% "full/vectors/10000011-V-0002.bin"
private noncomputable def vp10000011_3 : Blocks := edgeBlocks% "full/vectors/10000011-V-0003.bin"
noncomputable def vp10000011 : Blocks := (Blocks.join (Blocks.join vp10000011_0 vp10000011_1) (Blocks.join vp10000011_2 vp10000011_3))
private theorem bp100000110 : Branch 0 (-4191761639/32000000 : ℚ) vp10000011 := by
  apply branch_left_normalized (c:=vp100000110) (k:=0) (m:=264) (by decide +kernel)
  rw [show 2*(-4191761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4191761639/16000000 : ℚ) by norm_num]
  exact coverp100000110
private noncomputable def ep100000111_0 : Blocks := edgeBlocks% "full/vectors/100000111-E-0000.bin"
private noncomputable def ep100000111_1 : Blocks := edgeBlocks% "full/vectors/100000111-E-0001.bin"
private noncomputable def ep100000111_2 : Blocks := edgeBlocks% "full/vectors/100000111-E-0002.bin"
private noncomputable def ep100000111_3 : Blocks := edgeBlocks% "full/vectors/100000111-E-0003.bin"
noncomputable def ep100000111 : Blocks := (Blocks.join (Blocks.join ep100000111_0 ep100000111_1) (Blocks.join ep100000111_2 ep100000111_3))
private theorem idp100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10000011.list =
    C ((2:ℤ)^597) * horner X vp100000111.list + horner X ep100000111.list := by
  exact edge_identity (B := (2:ℤ)^864) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100000111 : Branch 1 (-4191761639/32000000 : ℚ) vp10000011 := by
  apply branch_checked idp100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4191761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4207761639/16000000 : ℚ) by norm_num]
  exact coverp100000111
theorem coverp10000011 : Covers (-4191761639/32000000 : ℚ) vp10000011 := join_branches bp100000110 bp100000111
private noncomputable def vp10000010111_0 : Blocks := edgeBlocks% "full/vectors/10000010111-V-0000.bin"
noncomputable def vp10000010111 : Blocks := vp10000010111_0
theorem coverp10000010111 : Covers (-4187761639/4000000 : ℚ) vp10000010111 := cover_leaf (by decide +kernel)
private noncomputable def vp10000010110_0 : Blocks := edgeBlocks% "full/vectors/10000010110-V-0000.bin"
noncomputable def vp10000010110 : Blocks := vp10000010110_0
theorem coverp10000010110 : Covers (-4183761639/4000000 : ℚ) vp10000010110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000001011_0 : Blocks := edgeBlocks% "full/vectors/1000001011-V-0000.bin"
private noncomputable def vp1000001011_1 : Blocks := edgeBlocks% "full/vectors/1000001011-V-0001.bin"
noncomputable def vp1000001011 : Blocks := (Blocks.join vp1000001011_0 vp1000001011_1)
private theorem bp10000010110 : Branch 0 (-4183761639/8000000 : ℚ) vp1000001011 := by
  apply branch_left_normalized (c:=vp10000010110) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4183761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4183761639/4000000 : ℚ) by norm_num]
  exact coverp10000010110
private noncomputable def ep10000010111_0 : Blocks := edgeBlocks% "full/vectors/10000010111-E-0000.bin"
private noncomputable def ep10000010111_1 : Blocks := edgeBlocks% "full/vectors/10000010111-E-0001.bin"
noncomputable def ep10000010111 : Blocks := (Blocks.join ep10000010111_0 ep10000010111_1)
private theorem idp10000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000001011.list =
    C ((2:ℤ)^166) * horner X vp10000010111.list + horner X ep10000010111.list := by
  exact edge_identity (B := (2:ℤ)^309) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000010111 : Branch 1 (-4183761639/8000000 : ℚ) vp1000001011 := by
  apply branch_checked idp10000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-4183761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4187761639/4000000 : ℚ) by norm_num]
  exact coverp10000010111
theorem coverp1000001011 : Covers (-4183761639/8000000 : ℚ) vp1000001011 := join_branches bp10000010110 bp10000010111
private noncomputable def vp10000010101_0 : Blocks := edgeBlocks% "full/vectors/10000010101-V-0000.bin"
noncomputable def vp10000010101 : Blocks := vp10000010101_0
theorem coverp10000010101 : Covers (-4179761639/4000000 : ℚ) vp10000010101 := cover_leaf (by decide +kernel)
private noncomputable def vp10000010100_0 : Blocks := edgeBlocks% "full/vectors/10000010100-V-0000.bin"
noncomputable def vp10000010100 : Blocks := vp10000010100_0
theorem coverp10000010100 : Covers (-4175761639/4000000 : ℚ) vp10000010100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000001010_0 : Blocks := edgeBlocks% "full/vectors/1000001010-V-0000.bin"
private noncomputable def vp1000001010_1 : Blocks := edgeBlocks% "full/vectors/1000001010-V-0001.bin"
noncomputable def vp1000001010 : Blocks := (Blocks.join vp1000001010_0 vp1000001010_1)
private theorem bp10000010100 : Branch 0 (-4175761639/8000000 : ℚ) vp1000001010 := by
  apply branch_left_normalized (c:=vp10000010100) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4175761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4175761639/4000000 : ℚ) by norm_num]
  exact coverp10000010100
private noncomputable def ep10000010101_0 : Blocks := edgeBlocks% "full/vectors/10000010101-E-0000.bin"
private noncomputable def ep10000010101_1 : Blocks := edgeBlocks% "full/vectors/10000010101-E-0001.bin"
noncomputable def ep10000010101 : Blocks := (Blocks.join ep10000010101_0 ep10000010101_1)
private theorem idp10000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000001010.list =
    C ((2:ℤ)^165) * horner X vp10000010101.list + horner X ep10000010101.list := by
  exact edge_identity (B := (2:ℤ)^307) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000010101 : Branch 1 (-4175761639/8000000 : ℚ) vp1000001010 := by
  apply branch_checked idp10000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4175761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4179761639/4000000 : ℚ) by norm_num]
  exact coverp10000010101
theorem coverp1000001010 : Covers (-4175761639/8000000 : ℚ) vp1000001010 := join_branches bp10000010100 bp10000010101
private noncomputable def vp100000101_0 : Blocks := edgeBlocks% "full/vectors/100000101-V-0000.bin"
private noncomputable def vp100000101_1 : Blocks := edgeBlocks% "full/vectors/100000101-V-0001.bin"
private noncomputable def vp100000101_2 : Blocks := edgeBlocks% "full/vectors/100000101-V-0002.bin"
noncomputable def vp100000101 : Blocks := (Blocks.join vp100000101_0 (Blocks.join vp100000101_1 vp100000101_2))
private theorem bp1000001010 : Branch 0 (-4175761639/16000000 : ℚ) vp100000101 := by
  apply branch_left_normalized (c:=vp1000001010) (k:=0) (m:=142) (by decide +kernel)
  rw [show 2*(-4175761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4175761639/8000000 : ℚ) by norm_num]
  exact coverp1000001010
private noncomputable def ep1000001011_0 : Blocks := edgeBlocks% "full/vectors/1000001011-E-0000.bin"
private noncomputable def ep1000001011_1 : Blocks := edgeBlocks% "full/vectors/1000001011-E-0001.bin"
private noncomputable def ep1000001011_2 : Blocks := edgeBlocks% "full/vectors/1000001011-E-0002.bin"
noncomputable def ep1000001011 : Blocks := (Blocks.join ep1000001011_0 (Blocks.join ep1000001011_1 ep1000001011_2))
private theorem idp1000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100000101.list =
    C ((2:ℤ)^310) * horner X vp1000001011.list + horner X ep1000001011.list := by
  exact edge_identity (B := (2:ℤ)^494) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000001011 : Branch 1 (-4175761639/16000000 : ℚ) vp100000101 := by
  apply branch_checked idp1000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4175761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4183761639/8000000 : ℚ) by norm_num]
  exact coverp1000001011
theorem coverp100000101 : Covers (-4175761639/16000000 : ℚ) vp100000101 := join_branches bp1000001010 bp1000001011
private noncomputable def vp10000010011_0 : Blocks := edgeBlocks% "full/vectors/10000010011-V-0000.bin"
noncomputable def vp10000010011 : Blocks := vp10000010011_0
theorem coverp10000010011 : Covers (-4171761639/4000000 : ℚ) vp10000010011 := cover_leaf (by decide +kernel)
private noncomputable def vp10000010010_0 : Blocks := edgeBlocks% "full/vectors/10000010010-V-0000.bin"
noncomputable def vp10000010010 : Blocks := vp10000010010_0
theorem coverp10000010010 : Covers (-4167761639/4000000 : ℚ) vp10000010010 := cover_leaf (by decide +kernel)
private noncomputable def vp1000001001_0 : Blocks := edgeBlocks% "full/vectors/1000001001-V-0000.bin"
private noncomputable def vp1000001001_1 : Blocks := edgeBlocks% "full/vectors/1000001001-V-0001.bin"
noncomputable def vp1000001001 : Blocks := (Blocks.join vp1000001001_0 vp1000001001_1)
private theorem bp10000010010 : Branch 0 (-4167761639/8000000 : ℚ) vp1000001001 := by
  apply branch_left_normalized (c:=vp10000010010) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4167761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4167761639/4000000 : ℚ) by norm_num]
  exact coverp10000010010
private noncomputable def ep10000010011_0 : Blocks := edgeBlocks% "full/vectors/10000010011-E-0000.bin"
private noncomputable def ep10000010011_1 : Blocks := edgeBlocks% "full/vectors/10000010011-E-0001.bin"
noncomputable def ep10000010011 : Blocks := (Blocks.join ep10000010011_0 ep10000010011_1)
private theorem idp10000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000001001.list =
    C ((2:ℤ)^164) * horner X vp10000010011.list + horner X ep10000010011.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000010011 : Branch 1 (-4167761639/8000000 : ℚ) vp1000001001 := by
  apply branch_checked idp10000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4167761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4171761639/4000000 : ℚ) by norm_num]
  exact coverp10000010011
theorem coverp1000001001 : Covers (-4167761639/8000000 : ℚ) vp1000001001 := join_branches bp10000010010 bp10000010011
private noncomputable def vp10000010001_0 : Blocks := edgeBlocks% "full/vectors/10000010001-V-0000.bin"
noncomputable def vp10000010001 : Blocks := vp10000010001_0
theorem coverp10000010001 : Covers (-4163761639/4000000 : ℚ) vp10000010001 := cover_leaf (by decide +kernel)
private noncomputable def vp10000010000_0 : Blocks := edgeBlocks% "full/vectors/10000010000-V-0000.bin"
noncomputable def vp10000010000 : Blocks := vp10000010000_0
theorem coverp10000010000 : Covers (-4159761639/4000000 : ℚ) vp10000010000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000001000_0 : Blocks := edgeBlocks% "full/vectors/1000001000-V-0000.bin"
private noncomputable def vp1000001000_1 : Blocks := edgeBlocks% "full/vectors/1000001000-V-0001.bin"
noncomputable def vp1000001000 : Blocks := (Blocks.join vp1000001000_0 vp1000001000_1)
private theorem bp10000010000 : Branch 0 (-4159761639/8000000 : ℚ) vp1000001000 := by
  apply branch_left_normalized (c:=vp10000010000) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4159761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4159761639/4000000 : ℚ) by norm_num]
  exact coverp10000010000
private noncomputable def ep10000010001_0 : Blocks := edgeBlocks% "full/vectors/10000010001-E-0000.bin"
private noncomputable def ep10000010001_1 : Blocks := edgeBlocks% "full/vectors/10000010001-E-0001.bin"
noncomputable def ep10000010001 : Blocks := (Blocks.join ep10000010001_0 ep10000010001_1)
private theorem idp10000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000001000.list =
    C ((2:ℤ)^163) * horner X vp10000010001.list + horner X ep10000010001.list := by
  exact edge_identity (B := (2:ℤ)^300) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000010001 : Branch 1 (-4159761639/8000000 : ℚ) vp1000001000 := by
  apply branch_checked idp10000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4159761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4163761639/4000000 : ℚ) by norm_num]
  exact coverp10000010001
theorem coverp1000001000 : Covers (-4159761639/8000000 : ℚ) vp1000001000 := join_branches bp10000010000 bp10000010001
private noncomputable def vp100000100_0 : Blocks := edgeBlocks% "full/vectors/100000100-V-0000.bin"
private noncomputable def vp100000100_1 : Blocks := edgeBlocks% "full/vectors/100000100-V-0001.bin"
private noncomputable def vp100000100_2 : Blocks := edgeBlocks% "full/vectors/100000100-V-0002.bin"
noncomputable def vp100000100 : Blocks := (Blocks.join vp100000100_0 (Blocks.join vp100000100_1 vp100000100_2))
private theorem bp1000001000 : Branch 0 (-4159761639/16000000 : ℚ) vp100000100 := by
  apply branch_left_normalized (c:=vp1000001000) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-4159761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4159761639/8000000 : ℚ) by norm_num]
  exact coverp1000001000
private noncomputable def ep1000001001_0 : Blocks := edgeBlocks% "full/vectors/1000001001-E-0000.bin"
private noncomputable def ep1000001001_1 : Blocks := edgeBlocks% "full/vectors/1000001001-E-0001.bin"
private noncomputable def ep1000001001_2 : Blocks := edgeBlocks% "full/vectors/1000001001-E-0002.bin"
noncomputable def ep1000001001 : Blocks := (Blocks.join ep1000001001_0 (Blocks.join ep1000001001_1 ep1000001001_2))
private theorem idp1000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100000100.list =
    C ((2:ℤ)^306) * horner X vp1000001001.list + horner X ep1000001001.list := by
  exact edge_identity (B := (2:ℤ)^486) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000001001 : Branch 1 (-4159761639/16000000 : ℚ) vp100000100 := by
  apply branch_checked idp1000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4159761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4167761639/8000000 : ℚ) by norm_num]
  exact coverp1000001001
theorem coverp100000100 : Covers (-4159761639/16000000 : ℚ) vp100000100 := join_branches bp1000001000 bp1000001001
private noncomputable def vp10000010_0 : Blocks := edgeBlocks% "full/vectors/10000010-V-0000.bin"
private noncomputable def vp10000010_1 : Blocks := edgeBlocks% "full/vectors/10000010-V-0001.bin"
private noncomputable def vp10000010_2 : Blocks := edgeBlocks% "full/vectors/10000010-V-0002.bin"
private noncomputable def vp10000010_3 : Blocks := edgeBlocks% "full/vectors/10000010-V-0003.bin"
noncomputable def vp10000010 : Blocks := (Blocks.join (Blocks.join vp10000010_0 vp10000010_1) (Blocks.join vp10000010_2 vp10000010_3))
private theorem bp100000100 : Branch 0 (-4159761639/32000000 : ℚ) vp10000010 := by
  apply branch_left_normalized (c:=vp100000100) (k:=0) (m:=261) (by decide +kernel)
  rw [show 2*(-4159761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4159761639/16000000 : ℚ) by norm_num]
  exact coverp100000100
private noncomputable def ep100000101_0 : Blocks := edgeBlocks% "full/vectors/100000101-E-0000.bin"
private noncomputable def ep100000101_1 : Blocks := edgeBlocks% "full/vectors/100000101-E-0001.bin"
private noncomputable def ep100000101_2 : Blocks := edgeBlocks% "full/vectors/100000101-E-0002.bin"
private noncomputable def ep100000101_3 : Blocks := edgeBlocks% "full/vectors/100000101-E-0003.bin"
noncomputable def ep100000101 : Blocks := (Blocks.join (Blocks.join ep100000101_0 ep100000101_1) (Blocks.join ep100000101_2 ep100000101_3))
private theorem idp100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10000010.list =
    C ((2:ℤ)^591) * horner X vp100000101.list + horner X ep100000101.list := by
  exact edge_identity (B := (2:ℤ)^857) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100000101 : Branch 1 (-4159761639/32000000 : ℚ) vp10000010 := by
  apply branch_checked idp100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4159761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4175761639/16000000 : ℚ) by norm_num]
  exact coverp100000101
theorem coverp10000010 : Covers (-4159761639/32000000 : ℚ) vp10000010 := join_branches bp100000100 bp100000101
private noncomputable def vp1000001_0 : Blocks := edgeBlocks% "full/vectors/1000001-V-0000.bin"
private noncomputable def vp1000001_1 : Blocks := edgeBlocks% "full/vectors/1000001-V-0001.bin"
private noncomputable def vp1000001_2 : Blocks := edgeBlocks% "full/vectors/1000001-V-0002.bin"
private noncomputable def vp1000001_3 : Blocks := edgeBlocks% "full/vectors/1000001-V-0003.bin"
private noncomputable def vp1000001_4 : Blocks := edgeBlocks% "full/vectors/1000001-V-0004.bin"
private noncomputable def vp1000001_5 : Blocks := edgeBlocks% "full/vectors/1000001-V-0005.bin"
private noncomputable def vp1000001_6 : Blocks := edgeBlocks% "full/vectors/1000001-V-0006.bin"
private noncomputable def vp1000001_7 : Blocks := edgeBlocks% "full/vectors/1000001-V-0007.bin"
noncomputable def vp1000001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1000001_0 vp1000001_1) (Blocks.join vp1000001_2 vp1000001_3)) (Blocks.join (Blocks.join vp1000001_4 vp1000001_5) (Blocks.join vp1000001_6 vp1000001_7)))
private theorem bp10000010 : Branch 0 (-4159761639/64000000 : ℚ) vp1000001 := by
  apply branch_left_normalized (c:=vp10000010) (k:=0) (m:=503) (by decide +kernel)
  rw [show 2*(-4159761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4159761639/32000000 : ℚ) by norm_num]
  exact coverp10000010
private noncomputable def ep10000011_0 : Blocks := edgeBlocks% "full/vectors/10000011-E-0000.bin"
private noncomputable def ep10000011_1 : Blocks := edgeBlocks% "full/vectors/10000011-E-0001.bin"
private noncomputable def ep10000011_2 : Blocks := edgeBlocks% "full/vectors/10000011-E-0002.bin"
private noncomputable def ep10000011_3 : Blocks := edgeBlocks% "full/vectors/10000011-E-0003.bin"
private noncomputable def ep10000011_4 : Blocks := edgeBlocks% "full/vectors/10000011-E-0004.bin"
private noncomputable def ep10000011_5 : Blocks := edgeBlocks% "full/vectors/10000011-E-0005.bin"
private noncomputable def ep10000011_6 : Blocks := edgeBlocks% "full/vectors/10000011-E-0006.bin"
private noncomputable def ep10000011_7 : Blocks := edgeBlocks% "full/vectors/10000011-E-0007.bin"
noncomputable def ep10000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10000011_0 ep10000011_1) (Blocks.join ep10000011_2 ep10000011_3)) (Blocks.join (Blocks.join ep10000011_4 ep10000011_5) (Blocks.join ep10000011_6 ep10000011_7)))
private theorem idp10000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000001.list =
    C ((2:ℤ)^1159) * horner X vp10000011.list + horner X ep10000011.list := by
  exact edge_identity (B := (2:ℤ)^1591) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000011 : Branch 1 (-4159761639/64000000 : ℚ) vp1000001 := by
  apply branch_checked idp10000011 (by positivity) (by decide +kernel)
  rw [show 2*(-4159761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4191761639/32000000 : ℚ) by norm_num]
  exact coverp10000011
theorem coverp1000001 : Covers (-4159761639/64000000 : ℚ) vp1000001 := join_branches bp10000010 bp10000011
private noncomputable def vp10000001111_0 : Blocks := edgeBlocks% "full/vectors/10000001111-V-0000.bin"
noncomputable def vp10000001111 : Blocks := vp10000001111_0
theorem coverp10000001111 : Covers (-4155761639/4000000 : ℚ) vp10000001111 := cover_leaf (by decide +kernel)
private noncomputable def vp10000001110_0 : Blocks := edgeBlocks% "full/vectors/10000001110-V-0000.bin"
noncomputable def vp10000001110 : Blocks := vp10000001110_0
theorem coverp10000001110 : Covers (-4151761639/4000000 : ℚ) vp10000001110 := cover_leaf (by decide +kernel)
private noncomputable def vp1000000111_0 : Blocks := edgeBlocks% "full/vectors/1000000111-V-0000.bin"
private noncomputable def vp1000000111_1 : Blocks := edgeBlocks% "full/vectors/1000000111-V-0001.bin"
noncomputable def vp1000000111 : Blocks := (Blocks.join vp1000000111_0 vp1000000111_1)
private theorem bp10000001110 : Branch 0 (-4151761639/8000000 : ℚ) vp1000000111 := by
  apply branch_left_normalized (c:=vp10000001110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4151761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4151761639/4000000 : ℚ) by norm_num]
  exact coverp10000001110
private noncomputable def ep10000001111_0 : Blocks := edgeBlocks% "full/vectors/10000001111-E-0000.bin"
private noncomputable def ep10000001111_1 : Blocks := edgeBlocks% "full/vectors/10000001111-E-0001.bin"
noncomputable def ep10000001111 : Blocks := (Blocks.join ep10000001111_0 ep10000001111_1)
private theorem idp10000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000000111.list =
    C ((2:ℤ)^163) * horner X vp10000001111.list + horner X ep10000001111.list := by
  exact edge_identity (B := (2:ℤ)^298) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000001111 : Branch 1 (-4151761639/8000000 : ℚ) vp1000000111 := by
  apply branch_checked idp10000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4151761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4155761639/4000000 : ℚ) by norm_num]
  exact coverp10000001111
theorem coverp1000000111 : Covers (-4151761639/8000000 : ℚ) vp1000000111 := join_branches bp10000001110 bp10000001111
private noncomputable def vp1000000110_0 : Blocks := edgeBlocks% "full/vectors/1000000110-V-0000.bin"
private noncomputable def vp1000000110_1 : Blocks := edgeBlocks% "full/vectors/1000000110-V-0001.bin"
noncomputable def vp1000000110 : Blocks := (Blocks.join vp1000000110_0 vp1000000110_1)
theorem coverp1000000110 : Covers (-4143761639/8000000 : ℚ) vp1000000110 := cover_leaf (by decide +kernel)
private noncomputable def vp100000011_0 : Blocks := edgeBlocks% "full/vectors/100000011-V-0000.bin"
private noncomputable def vp100000011_1 : Blocks := edgeBlocks% "full/vectors/100000011-V-0001.bin"
private noncomputable def vp100000011_2 : Blocks := edgeBlocks% "full/vectors/100000011-V-0002.bin"
noncomputable def vp100000011 : Blocks := (Blocks.join vp100000011_0 (Blocks.join vp100000011_1 vp100000011_2))
private theorem bp1000000110 : Branch 0 (-4143761639/16000000 : ℚ) vp100000011 := by
  apply branch_left_normalized (c:=vp1000000110) (k:=0) (m:=138) (by decide +kernel)
  rw [show 2*(-4143761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4143761639/8000000 : ℚ) by norm_num]
  exact coverp1000000110
private noncomputable def ep1000000111_0 : Blocks := edgeBlocks% "full/vectors/1000000111-E-0000.bin"
private noncomputable def ep1000000111_1 : Blocks := edgeBlocks% "full/vectors/1000000111-E-0001.bin"
private noncomputable def ep1000000111_2 : Blocks := edgeBlocks% "full/vectors/1000000111-E-0002.bin"
noncomputable def ep1000000111 : Blocks := (Blocks.join ep1000000111_0 (Blocks.join ep1000000111_1 ep1000000111_2))
private theorem idp1000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100000011.list =
    C ((2:ℤ)^308) * horner X vp1000000111.list + horner X ep1000000111.list := by
  exact edge_identity (B := (2:ℤ)^485) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000000111 : Branch 1 (-4143761639/16000000 : ℚ) vp100000011 := by
  apply branch_checked idp1000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4143761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4151761639/8000000 : ℚ) by norm_num]
  exact coverp1000000111
theorem coverp100000011 : Covers (-4143761639/16000000 : ℚ) vp100000011 := join_branches bp1000000110 bp1000000111
private noncomputable def vp1000000101_0 : Blocks := edgeBlocks% "full/vectors/1000000101-V-0000.bin"
private noncomputable def vp1000000101_1 : Blocks := edgeBlocks% "full/vectors/1000000101-V-0001.bin"
noncomputable def vp1000000101 : Blocks := (Blocks.join vp1000000101_0 vp1000000101_1)
theorem coverp1000000101 : Covers (-4135761639/8000000 : ℚ) vp1000000101 := cover_leaf (by decide +kernel)
private noncomputable def vp1000000100_0 : Blocks := edgeBlocks% "full/vectors/1000000100-V-0000.bin"
private noncomputable def vp1000000100_1 : Blocks := edgeBlocks% "full/vectors/1000000100-V-0001.bin"
noncomputable def vp1000000100 : Blocks := (Blocks.join vp1000000100_0 vp1000000100_1)
theorem coverp1000000100 : Covers (-4127761639/8000000 : ℚ) vp1000000100 := cover_leaf (by decide +kernel)
private noncomputable def vp100000010_0 : Blocks := edgeBlocks% "full/vectors/100000010-V-0000.bin"
private noncomputable def vp100000010_1 : Blocks := edgeBlocks% "full/vectors/100000010-V-0001.bin"
private noncomputable def vp100000010_2 : Blocks := edgeBlocks% "full/vectors/100000010-V-0002.bin"
noncomputable def vp100000010 : Blocks := (Blocks.join vp100000010_0 (Blocks.join vp100000010_1 vp100000010_2))
private theorem bp1000000100 : Branch 0 (-4127761639/16000000 : ℚ) vp100000010 := by
  apply branch_left_normalized (c:=vp1000000100) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-4127761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4127761639/8000000 : ℚ) by norm_num]
  exact coverp1000000100
private noncomputable def ep1000000101_0 : Blocks := edgeBlocks% "full/vectors/1000000101-E-0000.bin"
private noncomputable def ep1000000101_1 : Blocks := edgeBlocks% "full/vectors/1000000101-E-0001.bin"
private noncomputable def ep1000000101_2 : Blocks := edgeBlocks% "full/vectors/1000000101-E-0002.bin"
noncomputable def ep1000000101 : Blocks := (Blocks.join ep1000000101_0 (Blocks.join ep1000000101_1 ep1000000101_2))
private theorem idp1000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100000010.list =
    C ((2:ℤ)^310) * horner X vp1000000101.list + horner X ep1000000101.list := by
  exact edge_identity (B := (2:ℤ)^487) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000000101 : Branch 1 (-4127761639/16000000 : ℚ) vp100000010 := by
  apply branch_checked idp1000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4127761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4135761639/8000000 : ℚ) by norm_num]
  exact coverp1000000101
theorem coverp100000010 : Covers (-4127761639/16000000 : ℚ) vp100000010 := join_branches bp1000000100 bp1000000101
private noncomputable def vp10000001_0 : Blocks := edgeBlocks% "full/vectors/10000001-V-0000.bin"
private noncomputable def vp10000001_1 : Blocks := edgeBlocks% "full/vectors/10000001-V-0001.bin"
private noncomputable def vp10000001_2 : Blocks := edgeBlocks% "full/vectors/10000001-V-0002.bin"
private noncomputable def vp10000001_3 : Blocks := edgeBlocks% "full/vectors/10000001-V-0003.bin"
noncomputable def vp10000001 : Blocks := (Blocks.join (Blocks.join vp10000001_0 vp10000001_1) (Blocks.join vp10000001_2 vp10000001_3))
private theorem bp100000010 : Branch 0 (-4127761639/32000000 : ℚ) vp10000001 := by
  apply branch_left_normalized (c:=vp100000010) (k:=0) (m:=262) (by decide +kernel)
  rw [show 2*(-4127761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4127761639/16000000 : ℚ) by norm_num]
  exact coverp100000010
private noncomputable def ep100000011_0 : Blocks := edgeBlocks% "full/vectors/100000011-E-0000.bin"
private noncomputable def ep100000011_1 : Blocks := edgeBlocks% "full/vectors/100000011-E-0001.bin"
private noncomputable def ep100000011_2 : Blocks := edgeBlocks% "full/vectors/100000011-E-0002.bin"
private noncomputable def ep100000011_3 : Blocks := edgeBlocks% "full/vectors/100000011-E-0003.bin"
noncomputable def ep100000011 : Blocks := (Blocks.join (Blocks.join ep100000011_0 ep100000011_1) (Blocks.join ep100000011_2 ep100000011_3))
private theorem idp100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10000001.list =
    C ((2:ℤ)^598) * horner X vp100000011.list + horner X ep100000011.list := by
  exact edge_identity (B := (2:ℤ)^858) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100000011 : Branch 1 (-4127761639/32000000 : ℚ) vp10000001 := by
  apply branch_checked idp100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-4127761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4143761639/16000000 : ℚ) by norm_num]
  exact coverp100000011
theorem coverp10000001 : Covers (-4127761639/32000000 : ℚ) vp10000001 := join_branches bp100000010 bp100000011
private noncomputable def vp1000000011_0 : Blocks := edgeBlocks% "full/vectors/1000000011-V-0000.bin"
private noncomputable def vp1000000011_1 : Blocks := edgeBlocks% "full/vectors/1000000011-V-0001.bin"
noncomputable def vp1000000011 : Blocks := (Blocks.join vp1000000011_0 vp1000000011_1)
theorem coverp1000000011 : Covers (-4119761639/8000000 : ℚ) vp1000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp10000000101_0 : Blocks := edgeBlocks% "full/vectors/10000000101-V-0000.bin"
noncomputable def vp10000000101 : Blocks := vp10000000101_0
theorem coverp10000000101 : Covers (-4115761639/4000000 : ℚ) vp10000000101 := cover_leaf (by decide +kernel)
private noncomputable def vp10000000100_0 : Blocks := edgeBlocks% "full/vectors/10000000100-V-0000.bin"
noncomputable def vp10000000100 : Blocks := vp10000000100_0
theorem coverp10000000100 : Covers (-4111761639/4000000 : ℚ) vp10000000100 := cover_leaf (by decide +kernel)
private noncomputable def vp1000000010_0 : Blocks := edgeBlocks% "full/vectors/1000000010-V-0000.bin"
private noncomputable def vp1000000010_1 : Blocks := edgeBlocks% "full/vectors/1000000010-V-0001.bin"
noncomputable def vp1000000010 : Blocks := (Blocks.join vp1000000010_0 vp1000000010_1)
private theorem bp10000000100 : Branch 0 (-4111761639/8000000 : ℚ) vp1000000010 := by
  apply branch_left_normalized (c:=vp10000000100) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-4111761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4111761639/4000000 : ℚ) by norm_num]
  exact coverp10000000100
private noncomputable def ep10000000101_0 : Blocks := edgeBlocks% "full/vectors/10000000101-E-0000.bin"
private noncomputable def ep10000000101_1 : Blocks := edgeBlocks% "full/vectors/10000000101-E-0001.bin"
noncomputable def ep10000000101 : Blocks := (Blocks.join ep10000000101_0 ep10000000101_1)
private theorem idp10000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000000010.list =
    C ((2:ℤ)^168) * horner X vp10000000101.list + horner X ep10000000101.list := by
  exact edge_identity (B := (2:ℤ)^307) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000000101 : Branch 1 (-4111761639/8000000 : ℚ) vp1000000010 := by
  apply branch_checked idp10000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4111761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4115761639/4000000 : ℚ) by norm_num]
  exact coverp10000000101
theorem coverp1000000010 : Covers (-4111761639/8000000 : ℚ) vp1000000010 := join_branches bp10000000100 bp10000000101
private noncomputable def vp100000001_0 : Blocks := edgeBlocks% "full/vectors/100000001-V-0000.bin"
private noncomputable def vp100000001_1 : Blocks := edgeBlocks% "full/vectors/100000001-V-0001.bin"
private noncomputable def vp100000001_2 : Blocks := edgeBlocks% "full/vectors/100000001-V-0002.bin"
noncomputable def vp100000001 : Blocks := (Blocks.join vp100000001_0 (Blocks.join vp100000001_1 vp100000001_2))
private theorem bp1000000010 : Branch 0 (-4111761639/16000000 : ℚ) vp100000001 := by
  apply branch_left_normalized (c:=vp1000000010) (k:=0) (m:=142) (by decide +kernel)
  rw [show 2*(-4111761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4111761639/8000000 : ℚ) by norm_num]
  exact coverp1000000010
private noncomputable def ep1000000011_0 : Blocks := edgeBlocks% "full/vectors/1000000011-E-0000.bin"
private noncomputable def ep1000000011_1 : Blocks := edgeBlocks% "full/vectors/1000000011-E-0001.bin"
private noncomputable def ep1000000011_2 : Blocks := edgeBlocks% "full/vectors/1000000011-E-0002.bin"
noncomputable def ep1000000011 : Blocks := (Blocks.join ep1000000011_0 (Blocks.join ep1000000011_1 ep1000000011_2))
private theorem idp1000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100000001.list =
    C ((2:ℤ)^315) * horner X vp1000000011.list + horner X ep1000000011.list := by
  exact edge_identity (B := (2:ℤ)^495) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000000011 : Branch 1 (-4111761639/16000000 : ℚ) vp100000001 := by
  apply branch_checked idp1000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-4111761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4119761639/8000000 : ℚ) by norm_num]
  exact coverp1000000011
theorem coverp100000001 : Covers (-4111761639/16000000 : ℚ) vp100000001 := join_branches bp1000000010 bp1000000011
private noncomputable def vp10000000011_0 : Blocks := edgeBlocks% "full/vectors/10000000011-V-0000.bin"
noncomputable def vp10000000011 : Blocks := vp10000000011_0
theorem coverp10000000011 : Covers (-4107761639/4000000 : ℚ) vp10000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp10000000010_0 : Blocks := edgeBlocks% "full/vectors/10000000010-V-0000.bin"
noncomputable def vp10000000010 : Blocks := vp10000000010_0
theorem coverp10000000010 : Covers (-4103761639/4000000 : ℚ) vp10000000010 := cover_leaf (by decide +kernel)
private noncomputable def vp1000000001_0 : Blocks := edgeBlocks% "full/vectors/1000000001-V-0000.bin"
private noncomputable def vp1000000001_1 : Blocks := edgeBlocks% "full/vectors/1000000001-V-0001.bin"
noncomputable def vp1000000001 : Blocks := (Blocks.join vp1000000001_0 vp1000000001_1)
private theorem bp10000000010 : Branch 0 (-4103761639/8000000 : ℚ) vp1000000001 := by
  apply branch_left_normalized (c:=vp10000000010) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-4103761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4103761639/4000000 : ℚ) by norm_num]
  exact coverp10000000010
private noncomputable def ep10000000011_0 : Blocks := edgeBlocks% "full/vectors/10000000011-E-0000.bin"
private noncomputable def ep10000000011_1 : Blocks := edgeBlocks% "full/vectors/10000000011-E-0001.bin"
noncomputable def ep10000000011 : Blocks := (Blocks.join ep10000000011_0 ep10000000011_1)
private theorem idp10000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000000001.list =
    C ((2:ℤ)^169) * horner X vp10000000011.list + horner X ep10000000011.list := by
  exact edge_identity (B := (2:ℤ)^311) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000000011 : Branch 1 (-4103761639/8000000 : ℚ) vp1000000001 := by
  apply branch_checked idp10000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-4103761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4107761639/4000000 : ℚ) by norm_num]
  exact coverp10000000011
theorem coverp1000000001 : Covers (-4103761639/8000000 : ℚ) vp1000000001 := join_branches bp10000000010 bp10000000011
private noncomputable def vp10000000001_0 : Blocks := edgeBlocks% "full/vectors/10000000001-V-0000.bin"
noncomputable def vp10000000001 : Blocks := vp10000000001_0
theorem coverp10000000001 : Covers (-4099761639/4000000 : ℚ) vp10000000001 := cover_leaf (by decide +kernel)
private noncomputable def vp10000000000_0 : Blocks := edgeBlocks% "full/vectors/10000000000-V-0000.bin"
noncomputable def vp10000000000 : Blocks := vp10000000000_0
theorem coverp10000000000 : Covers (-4095761639/4000000 : ℚ) vp10000000000 := cover_leaf (by decide +kernel)
private noncomputable def vp1000000000_0 : Blocks := edgeBlocks% "full/vectors/1000000000-V-0000.bin"
private noncomputable def vp1000000000_1 : Blocks := edgeBlocks% "full/vectors/1000000000-V-0001.bin"
noncomputable def vp1000000000 : Blocks := (Blocks.join vp1000000000_0 vp1000000000_1)
private theorem bp10000000000 : Branch 0 (-4095761639/8000000 : ℚ) vp1000000000 := by
  apply branch_left_normalized (c:=vp10000000000) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-4095761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4095761639/4000000 : ℚ) by norm_num]
  exact coverp10000000000
private noncomputable def ep10000000001_0 : Blocks := edgeBlocks% "full/vectors/10000000001-E-0000.bin"
private noncomputable def ep10000000001_1 : Blocks := edgeBlocks% "full/vectors/10000000001-E-0001.bin"
noncomputable def ep10000000001 : Blocks := (Blocks.join ep10000000001_0 ep10000000001_1)
private theorem idp10000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000000000.list =
    C ((2:ℤ)^168) * horner X vp10000000001.list + horner X ep10000000001.list := by
  exact edge_identity (B := (2:ℤ)^311) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000000001 : Branch 1 (-4095761639/8000000 : ℚ) vp1000000000 := by
  apply branch_checked idp10000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-4095761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4099761639/4000000 : ℚ) by norm_num]
  exact coverp10000000001
theorem coverp1000000000 : Covers (-4095761639/8000000 : ℚ) vp1000000000 := join_branches bp10000000000 bp10000000001
private noncomputable def vp100000000_0 : Blocks := edgeBlocks% "full/vectors/100000000-V-0000.bin"
private noncomputable def vp100000000_1 : Blocks := edgeBlocks% "full/vectors/100000000-V-0001.bin"
private noncomputable def vp100000000_2 : Blocks := edgeBlocks% "full/vectors/100000000-V-0002.bin"
noncomputable def vp100000000 : Blocks := (Blocks.join vp100000000_0 (Blocks.join vp100000000_1 vp100000000_2))
private theorem bp1000000000 : Branch 0 (-4095761639/16000000 : ℚ) vp100000000 := by
  apply branch_left_normalized (c:=vp1000000000) (k:=0) (m:=144) (by decide +kernel)
  rw [show 2*(-4095761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4095761639/8000000 : ℚ) by norm_num]
  exact coverp1000000000
private noncomputable def ep1000000001_0 : Blocks := edgeBlocks% "full/vectors/1000000001-E-0000.bin"
private noncomputable def ep1000000001_1 : Blocks := edgeBlocks% "full/vectors/1000000001-E-0001.bin"
private noncomputable def ep1000000001_2 : Blocks := edgeBlocks% "full/vectors/1000000001-E-0002.bin"
noncomputable def ep1000000001 : Blocks := (Blocks.join ep1000000001_0 (Blocks.join ep1000000001_1 ep1000000001_2))
private theorem idp1000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100000000.list =
    C ((2:ℤ)^314) * horner X vp1000000001.list + horner X ep1000000001.list := by
  exact edge_identity (B := (2:ℤ)^500) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000000001 : Branch 1 (-4095761639/16000000 : ℚ) vp100000000 := by
  apply branch_checked idp1000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-4095761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4103761639/8000000 : ℚ) by norm_num]
  exact coverp1000000001
theorem coverp100000000 : Covers (-4095761639/16000000 : ℚ) vp100000000 := join_branches bp1000000000 bp1000000001
private noncomputable def vp10000000_0 : Blocks := edgeBlocks% "full/vectors/10000000-V-0000.bin"
private noncomputable def vp10000000_1 : Blocks := edgeBlocks% "full/vectors/10000000-V-0001.bin"
private noncomputable def vp10000000_2 : Blocks := edgeBlocks% "full/vectors/10000000-V-0002.bin"
private noncomputable def vp10000000_3 : Blocks := edgeBlocks% "full/vectors/10000000-V-0003.bin"
noncomputable def vp10000000 : Blocks := (Blocks.join (Blocks.join vp10000000_0 vp10000000_1) (Blocks.join vp10000000_2 vp10000000_3))
private theorem bp100000000 : Branch 0 (-4095761639/32000000 : ℚ) vp10000000 := by
  apply branch_left_normalized (c:=vp100000000) (k:=0) (m:=267) (by decide +kernel)
  rw [show 2*(-4095761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4095761639/16000000 : ℚ) by norm_num]
  exact coverp100000000
private noncomputable def ep100000001_0 : Blocks := edgeBlocks% "full/vectors/100000001-E-0000.bin"
private noncomputable def ep100000001_1 : Blocks := edgeBlocks% "full/vectors/100000001-E-0001.bin"
private noncomputable def ep100000001_2 : Blocks := edgeBlocks% "full/vectors/100000001-E-0002.bin"
private noncomputable def ep100000001_3 : Blocks := edgeBlocks% "full/vectors/100000001-E-0003.bin"
noncomputable def ep100000001 : Blocks := (Blocks.join (Blocks.join ep100000001_0 ep100000001_1) (Blocks.join ep100000001_2 ep100000001_3))
private theorem idp100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10000000.list =
    C ((2:ℤ)^607) * horner X vp100000001.list + horner X ep100000001.list := by
  exact edge_identity (B := (2:ℤ)^874) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp100000001 : Branch 1 (-4095761639/32000000 : ℚ) vp10000000 := by
  apply branch_checked idp100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-4095761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4111761639/16000000 : ℚ) by norm_num]
  exact coverp100000001
theorem coverp10000000 : Covers (-4095761639/32000000 : ℚ) vp10000000 := join_branches bp100000000 bp100000001
private noncomputable def vp1000000_0 : Blocks := edgeBlocks% "full/vectors/1000000-V-0000.bin"
private noncomputable def vp1000000_1 : Blocks := edgeBlocks% "full/vectors/1000000-V-0001.bin"
private noncomputable def vp1000000_2 : Blocks := edgeBlocks% "full/vectors/1000000-V-0002.bin"
private noncomputable def vp1000000_3 : Blocks := edgeBlocks% "full/vectors/1000000-V-0003.bin"
private noncomputable def vp1000000_4 : Blocks := edgeBlocks% "full/vectors/1000000-V-0004.bin"
private noncomputable def vp1000000_5 : Blocks := edgeBlocks% "full/vectors/1000000-V-0005.bin"
private noncomputable def vp1000000_6 : Blocks := edgeBlocks% "full/vectors/1000000-V-0006.bin"
private noncomputable def vp1000000_7 : Blocks := edgeBlocks% "full/vectors/1000000-V-0007.bin"
noncomputable def vp1000000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp1000000_0 vp1000000_1) (Blocks.join vp1000000_2 vp1000000_3)) (Blocks.join (Blocks.join vp1000000_4 vp1000000_5) (Blocks.join vp1000000_6 vp1000000_7)))
private theorem bp10000000 : Branch 0 (-4095761639/64000000 : ℚ) vp1000000 := by
  apply branch_left_normalized (c:=vp10000000) (k:=0) (m:=511) (by decide +kernel)
  rw [show 2*(-4095761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4095761639/32000000 : ℚ) by norm_num]
  exact coverp10000000
private noncomputable def ep10000001_0 : Blocks := edgeBlocks% "full/vectors/10000001-E-0000.bin"
private noncomputable def ep10000001_1 : Blocks := edgeBlocks% "full/vectors/10000001-E-0001.bin"
private noncomputable def ep10000001_2 : Blocks := edgeBlocks% "full/vectors/10000001-E-0002.bin"
private noncomputable def ep10000001_3 : Blocks := edgeBlocks% "full/vectors/10000001-E-0003.bin"
private noncomputable def ep10000001_4 : Blocks := edgeBlocks% "full/vectors/10000001-E-0004.bin"
private noncomputable def ep10000001_5 : Blocks := edgeBlocks% "full/vectors/10000001-E-0005.bin"
private noncomputable def ep10000001_6 : Blocks := edgeBlocks% "full/vectors/10000001-E-0006.bin"
private noncomputable def ep10000001_7 : Blocks := edgeBlocks% "full/vectors/10000001-E-0007.bin"
noncomputable def ep10000001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep10000001_0 ep10000001_1) (Blocks.join ep10000001_2 ep10000001_3)) (Blocks.join (Blocks.join ep10000001_4 ep10000001_5) (Blocks.join ep10000001_6 ep10000001_7)))
private theorem idp10000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000000.list =
    C ((2:ℤ)^1184) * horner X vp10000001.list + horner X ep10000001.list := by
  exact edge_identity (B := (2:ℤ)^1613) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp10000001 : Branch 1 (-4095761639/64000000 : ℚ) vp1000000 := by
  apply branch_checked idp10000001 (by positivity) (by decide +kernel)
  rw [show 2*(-4095761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4127761639/32000000 : ℚ) by norm_num]
  exact coverp10000001
theorem coverp1000000 : Covers (-4095761639/64000000 : ℚ) vp1000000 := join_branches bp10000000 bp10000001
private noncomputable def vp100000_0 : Blocks := edgeBlocks% "full/vectors/100000-V-0000.bin"
private noncomputable def vp100000_1 : Blocks := edgeBlocks% "full/vectors/100000-V-0001.bin"
private noncomputable def vp100000_2 : Blocks := edgeBlocks% "full/vectors/100000-V-0002.bin"
private noncomputable def vp100000_3 : Blocks := edgeBlocks% "full/vectors/100000-V-0003.bin"
private noncomputable def vp100000_4 : Blocks := edgeBlocks% "full/vectors/100000-V-0004.bin"
private noncomputable def vp100000_5 : Blocks := edgeBlocks% "full/vectors/100000-V-0005.bin"
private noncomputable def vp100000_6 : Blocks := edgeBlocks% "full/vectors/100000-V-0006.bin"
private noncomputable def vp100000_7 : Blocks := edgeBlocks% "full/vectors/100000-V-0007.bin"
private noncomputable def vp100000_8 : Blocks := edgeBlocks% "full/vectors/100000-V-0008.bin"
private noncomputable def vp100000_9 : Blocks := edgeBlocks% "full/vectors/100000-V-0009.bin"
private noncomputable def vp100000_10 : Blocks := edgeBlocks% "full/vectors/100000-V-0010.bin"
private noncomputable def vp100000_11 : Blocks := edgeBlocks% "full/vectors/100000-V-0011.bin"
private noncomputable def vp100000_12 : Blocks := edgeBlocks% "full/vectors/100000-V-0012.bin"
private noncomputable def vp100000_13 : Blocks := edgeBlocks% "full/vectors/100000-V-0013.bin"
private noncomputable def vp100000_14 : Blocks := edgeBlocks% "full/vectors/100000-V-0014.bin"
private noncomputable def vp100000_15 : Blocks := edgeBlocks% "full/vectors/100000-V-0015.bin"
noncomputable def vp100000 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp100000_0 vp100000_1) (Blocks.join vp100000_2 vp100000_3)) (Blocks.join (Blocks.join vp100000_4 vp100000_5) (Blocks.join vp100000_6 vp100000_7))) (Blocks.join (Blocks.join (Blocks.join vp100000_8 vp100000_9) (Blocks.join vp100000_10 vp100000_11)) (Blocks.join (Blocks.join vp100000_12 vp100000_13) (Blocks.join vp100000_14 vp100000_15))))
private theorem bp1000000 : Branch 0 (-4095761639/128000000 : ℚ) vp100000 := by
  apply branch_left_normalized (c:=vp1000000) (k:=0) (m:=991) (by decide +kernel)
  rw [show 2*(-4095761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-4095761639/64000000 : ℚ) by norm_num]
  exact coverp1000000
private noncomputable def ep1000001_0 : Blocks := edgeBlocks% "full/vectors/1000001-E-0000.bin"
private noncomputable def ep1000001_1 : Blocks := edgeBlocks% "full/vectors/1000001-E-0001.bin"
private noncomputable def ep1000001_2 : Blocks := edgeBlocks% "full/vectors/1000001-E-0002.bin"
private noncomputable def ep1000001_3 : Blocks := edgeBlocks% "full/vectors/1000001-E-0003.bin"
private noncomputable def ep1000001_4 : Blocks := edgeBlocks% "full/vectors/1000001-E-0004.bin"
private noncomputable def ep1000001_5 : Blocks := edgeBlocks% "full/vectors/1000001-E-0005.bin"
private noncomputable def ep1000001_6 : Blocks := edgeBlocks% "full/vectors/1000001-E-0006.bin"
private noncomputable def ep1000001_7 : Blocks := edgeBlocks% "full/vectors/1000001-E-0007.bin"
private noncomputable def ep1000001_8 : Blocks := edgeBlocks% "full/vectors/1000001-E-0008.bin"
private noncomputable def ep1000001_9 : Blocks := edgeBlocks% "full/vectors/1000001-E-0009.bin"
private noncomputable def ep1000001_10 : Blocks := edgeBlocks% "full/vectors/1000001-E-0010.bin"
private noncomputable def ep1000001_11 : Blocks := edgeBlocks% "full/vectors/1000001-E-0011.bin"
private noncomputable def ep1000001_12 : Blocks := edgeBlocks% "full/vectors/1000001-E-0012.bin"
private noncomputable def ep1000001_13 : Blocks := edgeBlocks% "full/vectors/1000001-E-0013.bin"
private noncomputable def ep1000001_14 : Blocks := edgeBlocks% "full/vectors/1000001-E-0014.bin"
private noncomputable def ep1000001_15 : Blocks := edgeBlocks% "full/vectors/1000001-E-0015.bin"
noncomputable def ep1000001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1000001_0 ep1000001_1) (Blocks.join ep1000001_2 ep1000001_3)) (Blocks.join (Blocks.join ep1000001_4 ep1000001_5) (Blocks.join ep1000001_6 ep1000001_7))) (Blocks.join (Blocks.join (Blocks.join ep1000001_8 ep1000001_9) (Blocks.join ep1000001_10 ep1000001_11)) (Blocks.join (Blocks.join ep1000001_12 ep1000001_13) (Blocks.join ep1000001_14 ep1000001_15))))
private theorem idp1000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp100000.list =
    C ((2:ℤ)^2308) * horner X vp1000001.list + horner X ep1000001.list := by
  exact edge_identity (B := (2:ℤ)^3066) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1000001 : Branch 1 (-4095761639/128000000 : ℚ) vp100000 := by
  apply branch_checked idp1000001 (by positivity) (by decide +kernel)
  rw [show 2*(-4095761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-4159761639/64000000 : ℚ) by norm_num]
  exact coverp1000001
theorem coverp100000 : Covers (-4095761639/128000000 : ℚ) vp100000 := join_branches bp1000000 bp1000001
private noncomputable def vp10000_0 : Blocks := edgeBlocks% "full/vectors/10000-V-0000.bin"
private noncomputable def vp10000_1 : Blocks := edgeBlocks% "full/vectors/10000-V-0001.bin"
private noncomputable def vp10000_2 : Blocks := edgeBlocks% "full/vectors/10000-V-0002.bin"
private noncomputable def vp10000_3 : Blocks := edgeBlocks% "full/vectors/10000-V-0003.bin"
private noncomputable def vp10000_4 : Blocks := edgeBlocks% "full/vectors/10000-V-0004.bin"
private noncomputable def vp10000_5 : Blocks := edgeBlocks% "full/vectors/10000-V-0005.bin"
private noncomputable def vp10000_6 : Blocks := edgeBlocks% "full/vectors/10000-V-0006.bin"
private noncomputable def vp10000_7 : Blocks := edgeBlocks% "full/vectors/10000-V-0007.bin"
private noncomputable def vp10000_8 : Blocks := edgeBlocks% "full/vectors/10000-V-0008.bin"
private noncomputable def vp10000_9 : Blocks := edgeBlocks% "full/vectors/10000-V-0009.bin"
private noncomputable def vp10000_10 : Blocks := edgeBlocks% "full/vectors/10000-V-0010.bin"
private noncomputable def vp10000_11 : Blocks := edgeBlocks% "full/vectors/10000-V-0011.bin"
private noncomputable def vp10000_12 : Blocks := edgeBlocks% "full/vectors/10000-V-0012.bin"
private noncomputable def vp10000_13 : Blocks := edgeBlocks% "full/vectors/10000-V-0013.bin"
private noncomputable def vp10000_14 : Blocks := edgeBlocks% "full/vectors/10000-V-0014.bin"
private noncomputable def vp10000_15 : Blocks := edgeBlocks% "full/vectors/10000-V-0015.bin"
private noncomputable def vp10000_16 : Blocks := edgeBlocks% "full/vectors/10000-V-0016.bin"
private noncomputable def vp10000_17 : Blocks := edgeBlocks% "full/vectors/10000-V-0017.bin"
private noncomputable def vp10000_18 : Blocks := edgeBlocks% "full/vectors/10000-V-0018.bin"
private noncomputable def vp10000_19 : Blocks := edgeBlocks% "full/vectors/10000-V-0019.bin"
private noncomputable def vp10000_20 : Blocks := edgeBlocks% "full/vectors/10000-V-0020.bin"
private noncomputable def vp10000_21 : Blocks := edgeBlocks% "full/vectors/10000-V-0021.bin"
private noncomputable def vp10000_22 : Blocks := edgeBlocks% "full/vectors/10000-V-0022.bin"
private noncomputable def vp10000_23 : Blocks := edgeBlocks% "full/vectors/10000-V-0023.bin"
private noncomputable def vp10000_24 : Blocks := edgeBlocks% "full/vectors/10000-V-0024.bin"
private noncomputable def vp10000_25 : Blocks := edgeBlocks% "full/vectors/10000-V-0025.bin"
private noncomputable def vp10000_26 : Blocks := edgeBlocks% "full/vectors/10000-V-0026.bin"
private noncomputable def vp10000_27 : Blocks := edgeBlocks% "full/vectors/10000-V-0027.bin"
private noncomputable def vp10000_28 : Blocks := edgeBlocks% "full/vectors/10000-V-0028.bin"
private noncomputable def vp10000_29 : Blocks := edgeBlocks% "full/vectors/10000-V-0029.bin"
noncomputable def vp10000 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp10000_0 (Blocks.join vp10000_1 vp10000_2)) (Blocks.join (Blocks.join vp10000_3 vp10000_4) (Blocks.join vp10000_5 vp10000_6))) (Blocks.join (Blocks.join (Blocks.join vp10000_7 vp10000_8) (Blocks.join vp10000_9 vp10000_10)) (Blocks.join (Blocks.join vp10000_11 vp10000_12) (Blocks.join vp10000_13 vp10000_14)))) (Blocks.join (Blocks.join (Blocks.join vp10000_15 (Blocks.join vp10000_16 vp10000_17)) (Blocks.join (Blocks.join vp10000_18 vp10000_19) (Blocks.join vp10000_20 vp10000_21))) (Blocks.join (Blocks.join (Blocks.join vp10000_22 vp10000_23) (Blocks.join vp10000_24 vp10000_25)) (Blocks.join (Blocks.join vp10000_26 vp10000_27) (Blocks.join vp10000_28 vp10000_29)))))
private theorem bp100000 : Branch 0 (-4095761639/256000000 : ℚ) vp10000 := by
  apply branch_left_normalized (c:=vp100000) (k:=0) (m:=1931) (by decide +kernel)
  rw [show 2*(-4095761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-4095761639/128000000 : ℚ) by norm_num]
  exact coverp100000
private noncomputable def ep100001_0 : Blocks := edgeBlocks% "full/vectors/100001-E-0000.bin"
private noncomputable def ep100001_1 : Blocks := edgeBlocks% "full/vectors/100001-E-0001.bin"
private noncomputable def ep100001_2 : Blocks := edgeBlocks% "full/vectors/100001-E-0002.bin"
private noncomputable def ep100001_3 : Blocks := edgeBlocks% "full/vectors/100001-E-0003.bin"
private noncomputable def ep100001_4 : Blocks := edgeBlocks% "full/vectors/100001-E-0004.bin"
private noncomputable def ep100001_5 : Blocks := edgeBlocks% "full/vectors/100001-E-0005.bin"
private noncomputable def ep100001_6 : Blocks := edgeBlocks% "full/vectors/100001-E-0006.bin"
private noncomputable def ep100001_7 : Blocks := edgeBlocks% "full/vectors/100001-E-0007.bin"
private noncomputable def ep100001_8 : Blocks := edgeBlocks% "full/vectors/100001-E-0008.bin"
private noncomputable def ep100001_9 : Blocks := edgeBlocks% "full/vectors/100001-E-0009.bin"
private noncomputable def ep100001_10 : Blocks := edgeBlocks% "full/vectors/100001-E-0010.bin"
private noncomputable def ep100001_11 : Blocks := edgeBlocks% "full/vectors/100001-E-0011.bin"
private noncomputable def ep100001_12 : Blocks := edgeBlocks% "full/vectors/100001-E-0012.bin"
private noncomputable def ep100001_13 : Blocks := edgeBlocks% "full/vectors/100001-E-0013.bin"
private noncomputable def ep100001_14 : Blocks := edgeBlocks% "full/vectors/100001-E-0014.bin"
private noncomputable def ep100001_15 : Blocks := edgeBlocks% "full/vectors/100001-E-0015.bin"
private noncomputable def ep100001_16 : Blocks := edgeBlocks% "full/vectors/100001-E-0016.bin"
private noncomputable def ep100001_17 : Blocks := edgeBlocks% "full/vectors/100001-E-0017.bin"
private noncomputable def ep100001_18 : Blocks := edgeBlocks% "full/vectors/100001-E-0018.bin"
private noncomputable def ep100001_19 : Blocks := edgeBlocks% "full/vectors/100001-E-0019.bin"
private noncomputable def ep100001_20 : Blocks := edgeBlocks% "full/vectors/100001-E-0020.bin"
private noncomputable def ep100001_21 : Blocks := edgeBlocks% "full/vectors/100001-E-0021.bin"
private noncomputable def ep100001_22 : Blocks := edgeBlocks% "full/vectors/100001-E-0022.bin"
private noncomputable def ep100001_23 : Blocks := edgeBlocks% "full/vectors/100001-E-0023.bin"
private noncomputable def ep100001_24 : Blocks := edgeBlocks% "full/vectors/100001-E-0024.bin"
private noncomputable def ep100001_25 : Blocks := edgeBlocks% "full/vectors/100001-E-0025.bin"
private noncomputable def ep100001_26 : Blocks := edgeBlocks% "full/vectors/100001-E-0026.bin"
private noncomputable def ep100001_27 : Blocks := edgeBlocks% "full/vectors/100001-E-0027.bin"
private noncomputable def ep100001_28 : Blocks := edgeBlocks% "full/vectors/100001-E-0028.bin"
private noncomputable def ep100001_29 : Blocks := edgeBlocks% "full/vectors/100001-E-0029.bin"
noncomputable def ep100001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep100001_0 (Blocks.join ep100001_1 ep100001_2)) (Blocks.join (Blocks.join ep100001_3 ep100001_4) (Blocks.join ep100001_5 ep100001_6))) (Blocks.join (Blocks.join (Blocks.join ep100001_7 ep100001_8) (Blocks.join ep100001_9 ep100001_10)) (Blocks.join (Blocks.join ep100001_11 ep100001_12) (Blocks.join ep100001_13 ep100001_14)))) (Blocks.join (Blocks.join (Blocks.join ep100001_15 (Blocks.join ep100001_16 ep100001_17)) (Blocks.join (Blocks.join ep100001_18 ep100001_19) (Blocks.join ep100001_20 ep100001_21))) (Blocks.join (Blocks.join (Blocks.join ep100001_22 ep100001_23) (Blocks.join ep100001_24 ep100001_25)) (Blocks.join (Blocks.join ep100001_26 ep100001_27) (Blocks.join ep100001_28 ep100001_29)))))
private def ptsp100001 : List ℤ := [((2:ℤ)^3222+0),((2:ℤ)^3222+1)]
private theorem boundp100001 : 2^vp10000.size*absSum vp10000.list + ((2:ℤ)^4463*absSum vp100001.list+absSum ep100001.list) < (2:ℤ)^5869 := by decide +kernel
private theorem pointp100001_0 : fastHom 1 ((2:ℤ)^3222+0) vp10000 = ((2:ℤ)^4463)*vp100001.subst ((2:ℤ)^3222+0)+ep100001.subst ((2:ℤ)^3222+0) := by decide +kernel
private theorem pointp100001_1 : fastHom 1 ((2:ℤ)^3222+1) vp10000 = ((2:ℤ)^4463)*vp100001.subst ((2:ℤ)^3222+1)+ep100001.subst ((2:ℤ)^3222+1) := by decide +kernel
private theorem checkp100001 (x:ℤ) (hx:x ∈ ptsp100001) : fastHom 1 x vp10000 = ((2:ℤ)^4463)*vp100001.subst x+ep100001.subst x := by
  simp only [ptsp100001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp100001_0
  · exact pointp100001_1
private theorem idp100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp10000.list =
    C ((2:ℤ)^4463) * horner X vp100001.list + horner X ep100001.list := by
  apply edge_identity (B := (2:ℤ)^5869) (by decide) (by positivity) (by positivity) boundp100001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp100001 (by decide +kernel)
  · have h : ptsp100001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp100001.trans_le (by decide +kernel)
  · exact checkp100001
private theorem bp100001 : Branch 1 (-4095761639/256000000 : ℚ) vp10000 := by
  apply branch_checked idp100001 (by positivity) (by decide +kernel)
  rw [show 2*(-4095761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-4223761639/128000000 : ℚ) by norm_num]
  exact coverp100001
theorem coverp10000 : Covers (-4095761639/256000000 : ℚ) vp10000 := join_branches bp100000 bp100001
private noncomputable def vp1000_0 : Blocks := edgeBlocks% "full/vectors/1000-V-0000.bin"
private noncomputable def vp1000_1 : Blocks := edgeBlocks% "full/vectors/1000-V-0001.bin"
private noncomputable def vp1000_2 : Blocks := edgeBlocks% "full/vectors/1000-V-0002.bin"
private noncomputable def vp1000_3 : Blocks := edgeBlocks% "full/vectors/1000-V-0003.bin"
private noncomputable def vp1000_4 : Blocks := edgeBlocks% "full/vectors/1000-V-0004.bin"
private noncomputable def vp1000_5 : Blocks := edgeBlocks% "full/vectors/1000-V-0005.bin"
private noncomputable def vp1000_6 : Blocks := edgeBlocks% "full/vectors/1000-V-0006.bin"
private noncomputable def vp1000_7 : Blocks := edgeBlocks% "full/vectors/1000-V-0007.bin"
private noncomputable def vp1000_8 : Blocks := edgeBlocks% "full/vectors/1000-V-0008.bin"
private noncomputable def vp1000_9 : Blocks := edgeBlocks% "full/vectors/1000-V-0009.bin"
private noncomputable def vp1000_10 : Blocks := edgeBlocks% "full/vectors/1000-V-0010.bin"
private noncomputable def vp1000_11 : Blocks := edgeBlocks% "full/vectors/1000-V-0011.bin"
private noncomputable def vp1000_12 : Blocks := edgeBlocks% "full/vectors/1000-V-0012.bin"
private noncomputable def vp1000_13 : Blocks := edgeBlocks% "full/vectors/1000-V-0013.bin"
private noncomputable def vp1000_14 : Blocks := edgeBlocks% "full/vectors/1000-V-0014.bin"
private noncomputable def vp1000_15 : Blocks := edgeBlocks% "full/vectors/1000-V-0015.bin"
private noncomputable def vp1000_16 : Blocks := edgeBlocks% "full/vectors/1000-V-0016.bin"
private noncomputable def vp1000_17 : Blocks := edgeBlocks% "full/vectors/1000-V-0017.bin"
private noncomputable def vp1000_18 : Blocks := edgeBlocks% "full/vectors/1000-V-0018.bin"
private noncomputable def vp1000_19 : Blocks := edgeBlocks% "full/vectors/1000-V-0019.bin"
private noncomputable def vp1000_20 : Blocks := edgeBlocks% "full/vectors/1000-V-0020.bin"
private noncomputable def vp1000_21 : Blocks := edgeBlocks% "full/vectors/1000-V-0021.bin"
private noncomputable def vp1000_22 : Blocks := edgeBlocks% "full/vectors/1000-V-0022.bin"
private noncomputable def vp1000_23 : Blocks := edgeBlocks% "full/vectors/1000-V-0023.bin"
private noncomputable def vp1000_24 : Blocks := edgeBlocks% "full/vectors/1000-V-0024.bin"
private noncomputable def vp1000_25 : Blocks := edgeBlocks% "full/vectors/1000-V-0025.bin"
private noncomputable def vp1000_26 : Blocks := edgeBlocks% "full/vectors/1000-V-0026.bin"
private noncomputable def vp1000_27 : Blocks := edgeBlocks% "full/vectors/1000-V-0027.bin"
private noncomputable def vp1000_28 : Blocks := edgeBlocks% "full/vectors/1000-V-0028.bin"
private noncomputable def vp1000_29 : Blocks := edgeBlocks% "full/vectors/1000-V-0029.bin"
private noncomputable def vp1000_30 : Blocks := edgeBlocks% "full/vectors/1000-V-0030.bin"
private noncomputable def vp1000_31 : Blocks := edgeBlocks% "full/vectors/1000-V-0031.bin"
private noncomputable def vp1000_32 : Blocks := edgeBlocks% "full/vectors/1000-V-0032.bin"
private noncomputable def vp1000_33 : Blocks := edgeBlocks% "full/vectors/1000-V-0033.bin"
private noncomputable def vp1000_34 : Blocks := edgeBlocks% "full/vectors/1000-V-0034.bin"
private noncomputable def vp1000_35 : Blocks := edgeBlocks% "full/vectors/1000-V-0035.bin"
private noncomputable def vp1000_36 : Blocks := edgeBlocks% "full/vectors/1000-V-0036.bin"
private noncomputable def vp1000_37 : Blocks := edgeBlocks% "full/vectors/1000-V-0037.bin"
private noncomputable def vp1000_38 : Blocks := edgeBlocks% "full/vectors/1000-V-0038.bin"
private noncomputable def vp1000_39 : Blocks := edgeBlocks% "full/vectors/1000-V-0039.bin"
private noncomputable def vp1000_40 : Blocks := edgeBlocks% "full/vectors/1000-V-0040.bin"
private noncomputable def vp1000_41 : Blocks := edgeBlocks% "full/vectors/1000-V-0041.bin"
private noncomputable def vp1000_42 : Blocks := edgeBlocks% "full/vectors/1000-V-0042.bin"
private noncomputable def vp1000_43 : Blocks := edgeBlocks% "full/vectors/1000-V-0043.bin"
private noncomputable def vp1000_44 : Blocks := edgeBlocks% "full/vectors/1000-V-0044.bin"
private noncomputable def vp1000_45 : Blocks := edgeBlocks% "full/vectors/1000-V-0045.bin"
private noncomputable def vp1000_46 : Blocks := edgeBlocks% "full/vectors/1000-V-0046.bin"
private noncomputable def vp1000_47 : Blocks := edgeBlocks% "full/vectors/1000-V-0047.bin"
private noncomputable def vp1000_48 : Blocks := edgeBlocks% "full/vectors/1000-V-0048.bin"
private noncomputable def vp1000_49 : Blocks := edgeBlocks% "full/vectors/1000-V-0049.bin"
private noncomputable def vp1000_50 : Blocks := edgeBlocks% "full/vectors/1000-V-0050.bin"
private noncomputable def vp1000_51 : Blocks := edgeBlocks% "full/vectors/1000-V-0051.bin"
private noncomputable def vp1000_52 : Blocks := edgeBlocks% "full/vectors/1000-V-0052.bin"
private noncomputable def vp1000_53 : Blocks := edgeBlocks% "full/vectors/1000-V-0053.bin"
private noncomputable def vp1000_54 : Blocks := edgeBlocks% "full/vectors/1000-V-0054.bin"
noncomputable def vp1000 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1000_0 (Blocks.join vp1000_1 vp1000_2)) (Blocks.join vp1000_3 (Blocks.join vp1000_4 vp1000_5))) (Blocks.join (Blocks.join vp1000_6 (Blocks.join vp1000_7 vp1000_8)) (Blocks.join (Blocks.join vp1000_9 vp1000_10) (Blocks.join vp1000_11 vp1000_12)))) (Blocks.join (Blocks.join (Blocks.join vp1000_13 (Blocks.join vp1000_14 vp1000_15)) (Blocks.join (Blocks.join vp1000_16 vp1000_17) (Blocks.join vp1000_18 vp1000_19))) (Blocks.join (Blocks.join vp1000_20 (Blocks.join vp1000_21 vp1000_22)) (Blocks.join (Blocks.join vp1000_23 vp1000_24) (Blocks.join vp1000_25 vp1000_26))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1000_27 (Blocks.join vp1000_28 vp1000_29)) (Blocks.join (Blocks.join vp1000_30 vp1000_31) (Blocks.join vp1000_32 vp1000_33))) (Blocks.join (Blocks.join vp1000_34 (Blocks.join vp1000_35 vp1000_36)) (Blocks.join (Blocks.join vp1000_37 vp1000_38) (Blocks.join vp1000_39 vp1000_40)))) (Blocks.join (Blocks.join (Blocks.join vp1000_41 (Blocks.join vp1000_42 vp1000_43)) (Blocks.join (Blocks.join vp1000_44 vp1000_45) (Blocks.join vp1000_46 vp1000_47))) (Blocks.join (Blocks.join vp1000_48 (Blocks.join vp1000_49 vp1000_50)) (Blocks.join (Blocks.join vp1000_51 vp1000_52) (Blocks.join vp1000_53 vp1000_54))))))
private theorem bp10000 : Branch 0 (-4095761639/512000000 : ℚ) vp1000 := by
  apply branch_left_normalized (c:=vp10000) (k:=0) (m:=3723) (by decide +kernel)
  rw [show 2*(-4095761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-4095761639/256000000 : ℚ) by norm_num]
  exact coverp10000
private noncomputable def ep10001_0 : Blocks := edgeBlocks% "full/vectors/10001-E-0000.bin"
private noncomputable def ep10001_1 : Blocks := edgeBlocks% "full/vectors/10001-E-0001.bin"
private noncomputable def ep10001_2 : Blocks := edgeBlocks% "full/vectors/10001-E-0002.bin"
private noncomputable def ep10001_3 : Blocks := edgeBlocks% "full/vectors/10001-E-0003.bin"
private noncomputable def ep10001_4 : Blocks := edgeBlocks% "full/vectors/10001-E-0004.bin"
private noncomputable def ep10001_5 : Blocks := edgeBlocks% "full/vectors/10001-E-0005.bin"
private noncomputable def ep10001_6 : Blocks := edgeBlocks% "full/vectors/10001-E-0006.bin"
private noncomputable def ep10001_7 : Blocks := edgeBlocks% "full/vectors/10001-E-0007.bin"
private noncomputable def ep10001_8 : Blocks := edgeBlocks% "full/vectors/10001-E-0008.bin"
private noncomputable def ep10001_9 : Blocks := edgeBlocks% "full/vectors/10001-E-0009.bin"
private noncomputable def ep10001_10 : Blocks := edgeBlocks% "full/vectors/10001-E-0010.bin"
private noncomputable def ep10001_11 : Blocks := edgeBlocks% "full/vectors/10001-E-0011.bin"
private noncomputable def ep10001_12 : Blocks := edgeBlocks% "full/vectors/10001-E-0012.bin"
private noncomputable def ep10001_13 : Blocks := edgeBlocks% "full/vectors/10001-E-0013.bin"
private noncomputable def ep10001_14 : Blocks := edgeBlocks% "full/vectors/10001-E-0014.bin"
private noncomputable def ep10001_15 : Blocks := edgeBlocks% "full/vectors/10001-E-0015.bin"
private noncomputable def ep10001_16 : Blocks := edgeBlocks% "full/vectors/10001-E-0016.bin"
private noncomputable def ep10001_17 : Blocks := edgeBlocks% "full/vectors/10001-E-0017.bin"
private noncomputable def ep10001_18 : Blocks := edgeBlocks% "full/vectors/10001-E-0018.bin"
private noncomputable def ep10001_19 : Blocks := edgeBlocks% "full/vectors/10001-E-0019.bin"
private noncomputable def ep10001_20 : Blocks := edgeBlocks% "full/vectors/10001-E-0020.bin"
private noncomputable def ep10001_21 : Blocks := edgeBlocks% "full/vectors/10001-E-0021.bin"
private noncomputable def ep10001_22 : Blocks := edgeBlocks% "full/vectors/10001-E-0022.bin"
private noncomputable def ep10001_23 : Blocks := edgeBlocks% "full/vectors/10001-E-0023.bin"
private noncomputable def ep10001_24 : Blocks := edgeBlocks% "full/vectors/10001-E-0024.bin"
private noncomputable def ep10001_25 : Blocks := edgeBlocks% "full/vectors/10001-E-0025.bin"
private noncomputable def ep10001_26 : Blocks := edgeBlocks% "full/vectors/10001-E-0026.bin"
private noncomputable def ep10001_27 : Blocks := edgeBlocks% "full/vectors/10001-E-0027.bin"
private noncomputable def ep10001_28 : Blocks := edgeBlocks% "full/vectors/10001-E-0028.bin"
private noncomputable def ep10001_29 : Blocks := edgeBlocks% "full/vectors/10001-E-0029.bin"
private noncomputable def ep10001_30 : Blocks := edgeBlocks% "full/vectors/10001-E-0030.bin"
private noncomputable def ep10001_31 : Blocks := edgeBlocks% "full/vectors/10001-E-0031.bin"
private noncomputable def ep10001_32 : Blocks := edgeBlocks% "full/vectors/10001-E-0032.bin"
private noncomputable def ep10001_33 : Blocks := edgeBlocks% "full/vectors/10001-E-0033.bin"
private noncomputable def ep10001_34 : Blocks := edgeBlocks% "full/vectors/10001-E-0034.bin"
private noncomputable def ep10001_35 : Blocks := edgeBlocks% "full/vectors/10001-E-0035.bin"
private noncomputable def ep10001_36 : Blocks := edgeBlocks% "full/vectors/10001-E-0036.bin"
private noncomputable def ep10001_37 : Blocks := edgeBlocks% "full/vectors/10001-E-0037.bin"
private noncomputable def ep10001_38 : Blocks := edgeBlocks% "full/vectors/10001-E-0038.bin"
private noncomputable def ep10001_39 : Blocks := edgeBlocks% "full/vectors/10001-E-0039.bin"
private noncomputable def ep10001_40 : Blocks := edgeBlocks% "full/vectors/10001-E-0040.bin"
private noncomputable def ep10001_41 : Blocks := edgeBlocks% "full/vectors/10001-E-0041.bin"
private noncomputable def ep10001_42 : Blocks := edgeBlocks% "full/vectors/10001-E-0042.bin"
private noncomputable def ep10001_43 : Blocks := edgeBlocks% "full/vectors/10001-E-0043.bin"
private noncomputable def ep10001_44 : Blocks := edgeBlocks% "full/vectors/10001-E-0044.bin"
private noncomputable def ep10001_45 : Blocks := edgeBlocks% "full/vectors/10001-E-0045.bin"
private noncomputable def ep10001_46 : Blocks := edgeBlocks% "full/vectors/10001-E-0046.bin"
private noncomputable def ep10001_47 : Blocks := edgeBlocks% "full/vectors/10001-E-0047.bin"
private noncomputable def ep10001_48 : Blocks := edgeBlocks% "full/vectors/10001-E-0048.bin"
private noncomputable def ep10001_49 : Blocks := edgeBlocks% "full/vectors/10001-E-0049.bin"
private noncomputable def ep10001_50 : Blocks := edgeBlocks% "full/vectors/10001-E-0050.bin"
private noncomputable def ep10001_51 : Blocks := edgeBlocks% "full/vectors/10001-E-0051.bin"
private noncomputable def ep10001_52 : Blocks := edgeBlocks% "full/vectors/10001-E-0052.bin"
private noncomputable def ep10001_53 : Blocks := edgeBlocks% "full/vectors/10001-E-0053.bin"
private noncomputable def ep10001_54 : Blocks := edgeBlocks% "full/vectors/10001-E-0054.bin"
noncomputable def ep10001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep10001_0 (Blocks.join ep10001_1 ep10001_2)) (Blocks.join ep10001_3 (Blocks.join ep10001_4 ep10001_5))) (Blocks.join (Blocks.join ep10001_6 (Blocks.join ep10001_7 ep10001_8)) (Blocks.join (Blocks.join ep10001_9 ep10001_10) (Blocks.join ep10001_11 ep10001_12)))) (Blocks.join (Blocks.join (Blocks.join ep10001_13 (Blocks.join ep10001_14 ep10001_15)) (Blocks.join (Blocks.join ep10001_16 ep10001_17) (Blocks.join ep10001_18 ep10001_19))) (Blocks.join (Blocks.join ep10001_20 (Blocks.join ep10001_21 ep10001_22)) (Blocks.join (Blocks.join ep10001_23 ep10001_24) (Blocks.join ep10001_25 ep10001_26))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep10001_27 (Blocks.join ep10001_28 ep10001_29)) (Blocks.join (Blocks.join ep10001_30 ep10001_31) (Blocks.join ep10001_32 ep10001_33))) (Blocks.join (Blocks.join ep10001_34 (Blocks.join ep10001_35 ep10001_36)) (Blocks.join (Blocks.join ep10001_37 ep10001_38) (Blocks.join ep10001_39 ep10001_40)))) (Blocks.join (Blocks.join (Blocks.join ep10001_41 (Blocks.join ep10001_42 ep10001_43)) (Blocks.join (Blocks.join ep10001_44 ep10001_45) (Blocks.join ep10001_46 ep10001_47))) (Blocks.join (Blocks.join ep10001_48 (Blocks.join ep10001_49 ep10001_50)) (Blocks.join (Blocks.join ep10001_51 ep10001_52) (Blocks.join ep10001_53 ep10001_54))))))
private def ptsp10001 : List ℤ := [((2:ℤ)^1722+0),((2:ℤ)^1722+1),((2:ℤ)^1722+2),((2:ℤ)^1722+3),((2:ℤ)^1722+4),((2:ℤ)^1722+5),((2:ℤ)^1722+6)]
private theorem boundp10001 : 2^vp1000.size*absSum vp1000.list + ((2:ℤ)^8451*absSum vp10001.list+absSum ep10001.list) < (2:ℤ)^11067 := by decide +kernel
private theorem pointp10001_0 : fastHom 1 ((2:ℤ)^1722+0) vp1000 = ((2:ℤ)^8451)*vp10001.subst ((2:ℤ)^1722+0)+ep10001.subst ((2:ℤ)^1722+0) := by decide +kernel
private theorem pointp10001_1 : fastHom 1 ((2:ℤ)^1722+1) vp1000 = ((2:ℤ)^8451)*vp10001.subst ((2:ℤ)^1722+1)+ep10001.subst ((2:ℤ)^1722+1) := by decide +kernel
private theorem pointp10001_2 : fastHom 1 ((2:ℤ)^1722+2) vp1000 = ((2:ℤ)^8451)*vp10001.subst ((2:ℤ)^1722+2)+ep10001.subst ((2:ℤ)^1722+2) := by decide +kernel
private theorem pointp10001_3 : fastHom 1 ((2:ℤ)^1722+3) vp1000 = ((2:ℤ)^8451)*vp10001.subst ((2:ℤ)^1722+3)+ep10001.subst ((2:ℤ)^1722+3) := by decide +kernel
private theorem pointp10001_4 : fastHom 1 ((2:ℤ)^1722+4) vp1000 = ((2:ℤ)^8451)*vp10001.subst ((2:ℤ)^1722+4)+ep10001.subst ((2:ℤ)^1722+4) := by decide +kernel
private theorem pointp10001_5 : fastHom 1 ((2:ℤ)^1722+5) vp1000 = ((2:ℤ)^8451)*vp10001.subst ((2:ℤ)^1722+5)+ep10001.subst ((2:ℤ)^1722+5) := by decide +kernel
private theorem pointp10001_6 : fastHom 1 ((2:ℤ)^1722+6) vp1000 = ((2:ℤ)^8451)*vp10001.subst ((2:ℤ)^1722+6)+ep10001.subst ((2:ℤ)^1722+6) := by decide +kernel
private theorem checkp10001 (x:ℤ) (hx:x ∈ ptsp10001) : fastHom 1 x vp1000 = ((2:ℤ)^8451)*vp10001.subst x+ep10001.subst x := by
  simp only [ptsp10001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp10001_0
  · exact pointp10001_1
  · exact pointp10001_2
  · exact pointp10001_3
  · exact pointp10001_4
  · exact pointp10001_5
  · exact pointp10001_6
private theorem idp10001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1000.list =
    C ((2:ℤ)^8451) * horner X vp10001.list + horner X ep10001.list := by
  apply edge_identity (B := (2:ℤ)^11067) (by decide) (by positivity) (by positivity) boundp10001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp10001 (by decide +kernel)
  · have h : ptsp10001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp10001.trans_le (by decide +kernel)
  · exact checkp10001
private theorem bp10001 : Branch 1 (-4095761639/512000000 : ℚ) vp1000 := by
  apply branch_checked idp10001 (by positivity) (by decide +kernel)
  rw [show 2*(-4095761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-4351761639/256000000 : ℚ) by norm_num]
  exact coverp10001
theorem coverp1000 : Covers (-4095761639/512000000 : ℚ) vp1000 := join_branches bp10000 bp10001
end NextProof.EdgeFull

