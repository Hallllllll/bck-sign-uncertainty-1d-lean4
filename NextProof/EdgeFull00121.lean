import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp01100111111_0 : Blocks := edgeBlocks% "full/vectors/01100111111-V-0000.bin"
noncomputable def vp01100111111 : Blocks := vp01100111111_0
theorem coverp01100111111 : Covers (-3323761639/4000000 : ℚ) vp01100111111 := cover_leaf (by decide +kernel)
private noncomputable def vp011001111101_0 : Blocks := edgeBlocks% "full/vectors/011001111101-V-0000.bin"
noncomputable def vp011001111101 : Blocks := vp011001111101_0
theorem coverp011001111101 : Covers (-3321761639/2000000 : ℚ) vp011001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp011001111100_0 : Blocks := edgeBlocks% "full/vectors/011001111100-V-0000.bin"
noncomputable def vp011001111100 : Blocks := vp011001111100_0
theorem coverp011001111100 : Covers (-3319761639/2000000 : ℚ) vp011001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100111110_0 : Blocks := edgeBlocks% "full/vectors/01100111110-V-0000.bin"
noncomputable def vp01100111110 : Blocks := vp01100111110_0
private theorem bp011001111100 : Branch 0 (-3319761639/4000000 : ℚ) vp01100111110 := by
  apply branch_left_normalized (c:=vp011001111100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3319761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3319761639/2000000 : ℚ) by norm_num]
  exact coverp011001111100
private noncomputable def ep011001111101_0 : Blocks := edgeBlocks% "full/vectors/011001111101-E-0000.bin"
noncomputable def ep011001111101 : Blocks := ep011001111101_0
private theorem idp011001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100111110.list =
    C ((2:ℤ)^102) * horner X vp011001111101.list + horner X ep011001111101.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001111101 : Branch 1 (-3319761639/4000000 : ℚ) vp01100111110 := by
  apply branch_checked idp011001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3319761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3321761639/2000000 : ℚ) by norm_num]
  exact coverp011001111101
theorem coverp01100111110 : Covers (-3319761639/4000000 : ℚ) vp01100111110 := join_branches bp011001111100 bp011001111101
private noncomputable def vp0110011111_0 : Blocks := edgeBlocks% "full/vectors/0110011111-V-0000.bin"
private noncomputable def vp0110011111_1 : Blocks := edgeBlocks% "full/vectors/0110011111-V-0001.bin"
noncomputable def vp0110011111 : Blocks := (Blocks.join vp0110011111_0 vp0110011111_1)
private theorem bp01100111110 : Branch 0 (-3319761639/8000000 : ℚ) vp0110011111 := by
  apply branch_left_normalized (c:=vp01100111110) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-3319761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3319761639/4000000 : ℚ) by norm_num]
  exact coverp01100111110
private noncomputable def ep01100111111_0 : Blocks := edgeBlocks% "full/vectors/01100111111-E-0000.bin"
private noncomputable def ep01100111111_1 : Blocks := edgeBlocks% "full/vectors/01100111111-E-0001.bin"
noncomputable def ep01100111111 : Blocks := (Blocks.join ep01100111111_0 ep01100111111_1)
private theorem idp01100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110011111.list =
    C ((2:ℤ)^182) * horner X vp01100111111.list + horner X ep01100111111.list := by
  exact edge_identity (B := (2:ℤ)^332) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100111111 : Branch 1 (-3319761639/8000000 : ℚ) vp0110011111 := by
  apply branch_checked idp01100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3319761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3323761639/4000000 : ℚ) by norm_num]
  exact coverp01100111111
theorem coverp0110011111 : Covers (-3319761639/8000000 : ℚ) vp0110011111 := join_branches bp01100111110 bp01100111111
private noncomputable def vp011001111011_0 : Blocks := edgeBlocks% "full/vectors/011001111011-V-0000.bin"
noncomputable def vp011001111011 : Blocks := vp011001111011_0
theorem coverp011001111011 : Covers (-3317761639/2000000 : ℚ) vp011001111011 := cover_leaf (by decide +kernel)
private noncomputable def vp011001111010_0 : Blocks := edgeBlocks% "full/vectors/011001111010-V-0000.bin"
noncomputable def vp011001111010 : Blocks := vp011001111010_0
theorem coverp011001111010 : Covers (-3315761639/2000000 : ℚ) vp011001111010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100111101_0 : Blocks := edgeBlocks% "full/vectors/01100111101-V-0000.bin"
noncomputable def vp01100111101 : Blocks := vp01100111101_0
private theorem bp011001111010 : Branch 0 (-3315761639/4000000 : ℚ) vp01100111101 := by
  apply branch_left_normalized (c:=vp011001111010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3315761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3315761639/2000000 : ℚ) by norm_num]
  exact coverp011001111010
private noncomputable def ep011001111011_0 : Blocks := edgeBlocks% "full/vectors/011001111011-E-0000.bin"
noncomputable def ep011001111011 : Blocks := ep011001111011_0
private theorem idp011001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100111101.list =
    C ((2:ℤ)^101) * horner X vp011001111011.list + horner X ep011001111011.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001111011 : Branch 1 (-3315761639/4000000 : ℚ) vp01100111101 := by
  apply branch_checked idp011001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3315761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3317761639/2000000 : ℚ) by norm_num]
  exact coverp011001111011
theorem coverp01100111101 : Covers (-3315761639/4000000 : ℚ) vp01100111101 := join_branches bp011001111010 bp011001111011
private noncomputable def vp011001111001_0 : Blocks := edgeBlocks% "full/vectors/011001111001-V-0000.bin"
noncomputable def vp011001111001 : Blocks := vp011001111001_0
theorem coverp011001111001 : Covers (-3313761639/2000000 : ℚ) vp011001111001 := cover_leaf (by decide +kernel)
private noncomputable def vp011001111000_0 : Blocks := edgeBlocks% "full/vectors/011001111000-V-0000.bin"
noncomputable def vp011001111000 : Blocks := vp011001111000_0
theorem coverp011001111000 : Covers (-3311761639/2000000 : ℚ) vp011001111000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100111100_0 : Blocks := edgeBlocks% "full/vectors/01100111100-V-0000.bin"
noncomputable def vp01100111100 : Blocks := vp01100111100_0
private theorem bp011001111000 : Branch 0 (-3311761639/4000000 : ℚ) vp01100111100 := by
  apply branch_left_normalized (c:=vp011001111000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3311761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3311761639/2000000 : ℚ) by norm_num]
  exact coverp011001111000
private noncomputable def ep011001111001_0 : Blocks := edgeBlocks% "full/vectors/011001111001-E-0000.bin"
noncomputable def ep011001111001 : Blocks := ep011001111001_0
private theorem idp011001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100111100.list =
    C ((2:ℤ)^102) * horner X vp011001111001.list + horner X ep011001111001.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001111001 : Branch 1 (-3311761639/4000000 : ℚ) vp01100111100 := by
  apply branch_checked idp011001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3311761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3313761639/2000000 : ℚ) by norm_num]
  exact coverp011001111001
theorem coverp01100111100 : Covers (-3311761639/4000000 : ℚ) vp01100111100 := join_branches bp011001111000 bp011001111001
private noncomputable def vp0110011110_0 : Blocks := edgeBlocks% "full/vectors/0110011110-V-0000.bin"
private noncomputable def vp0110011110_1 : Blocks := edgeBlocks% "full/vectors/0110011110-V-0001.bin"
noncomputable def vp0110011110 : Blocks := (Blocks.join vp0110011110_0 vp0110011110_1)
private theorem bp01100111100 : Branch 0 (-3311761639/8000000 : ℚ) vp0110011110 := by
  apply branch_left_normalized (c:=vp01100111100) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-3311761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3311761639/4000000 : ℚ) by norm_num]
  exact coverp01100111100
private noncomputable def ep01100111101_0 : Blocks := edgeBlocks% "full/vectors/01100111101-E-0000.bin"
private noncomputable def ep01100111101_1 : Blocks := edgeBlocks% "full/vectors/01100111101-E-0001.bin"
noncomputable def ep01100111101 : Blocks := (Blocks.join ep01100111101_0 ep01100111101_1)
private theorem idp01100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110011110.list =
    C ((2:ℤ)^182) * horner X vp01100111101.list + horner X ep01100111101.list := by
  exact edge_identity (B := (2:ℤ)^332) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100111101 : Branch 1 (-3311761639/8000000 : ℚ) vp0110011110 := by
  apply branch_checked idp01100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3311761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3315761639/4000000 : ℚ) by norm_num]
  exact coverp01100111101
theorem coverp0110011110 : Covers (-3311761639/8000000 : ℚ) vp0110011110 := join_branches bp01100111100 bp01100111101
private noncomputable def vp011001111_0 : Blocks := edgeBlocks% "full/vectors/011001111-V-0000.bin"
private noncomputable def vp011001111_1 : Blocks := edgeBlocks% "full/vectors/011001111-V-0001.bin"
private noncomputable def vp011001111_2 : Blocks := edgeBlocks% "full/vectors/011001111-V-0002.bin"
noncomputable def vp011001111 : Blocks := (Blocks.join vp011001111_0 (Blocks.join vp011001111_1 vp011001111_2))
private theorem bp0110011110 : Branch 0 (-3311761639/16000000 : ℚ) vp011001111 := by
  apply branch_left_normalized (c:=vp0110011110) (k:=0) (m:=158) (by decide +kernel)
  rw [show 2*(-3311761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3311761639/8000000 : ℚ) by norm_num]
  exact coverp0110011110
private noncomputable def ep0110011111_0 : Blocks := edgeBlocks% "full/vectors/0110011111-E-0000.bin"
private noncomputable def ep0110011111_1 : Blocks := edgeBlocks% "full/vectors/0110011111-E-0001.bin"
private noncomputable def ep0110011111_2 : Blocks := edgeBlocks% "full/vectors/0110011111-E-0002.bin"
noncomputable def ep0110011111 : Blocks := (Blocks.join ep0110011111_0 (Blocks.join ep0110011111_1 ep0110011111_2))
private theorem idp0110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011001111.list =
    C ((2:ℤ)^342) * horner X vp0110011111.list + horner X ep0110011111.list := by
  exact edge_identity (B := (2:ℤ)^542) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110011111 : Branch 1 (-3311761639/16000000 : ℚ) vp011001111 := by
  apply branch_checked idp0110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3311761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3319761639/8000000 : ℚ) by norm_num]
  exact coverp0110011111
theorem coverp011001111 : Covers (-3311761639/16000000 : ℚ) vp011001111 := join_branches bp0110011110 bp0110011111
private noncomputable def vp011001110111_0 : Blocks := edgeBlocks% "full/vectors/011001110111-V-0000.bin"
noncomputable def vp011001110111 : Blocks := vp011001110111_0
theorem coverp011001110111 : Covers (-3309761639/2000000 : ℚ) vp011001110111 := cover_leaf (by decide +kernel)
private noncomputable def vp011001110110_0 : Blocks := edgeBlocks% "full/vectors/011001110110-V-0000.bin"
noncomputable def vp011001110110 : Blocks := vp011001110110_0
theorem coverp011001110110 : Covers (-3307761639/2000000 : ℚ) vp011001110110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100111011_0 : Blocks := edgeBlocks% "full/vectors/01100111011-V-0000.bin"
noncomputable def vp01100111011 : Blocks := vp01100111011_0
private theorem bp011001110110 : Branch 0 (-3307761639/4000000 : ℚ) vp01100111011 := by
  apply branch_left_normalized (c:=vp011001110110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3307761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3307761639/2000000 : ℚ) by norm_num]
  exact coverp011001110110
private noncomputable def ep011001110111_0 : Blocks := edgeBlocks% "full/vectors/011001110111-E-0000.bin"
noncomputable def ep011001110111 : Blocks := ep011001110111_0
private theorem idp011001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100111011.list =
    C ((2:ℤ)^101) * horner X vp011001110111.list + horner X ep011001110111.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001110111 : Branch 1 (-3307761639/4000000 : ℚ) vp01100111011 := by
  apply branch_checked idp011001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3307761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3309761639/2000000 : ℚ) by norm_num]
  exact coverp011001110111
theorem coverp01100111011 : Covers (-3307761639/4000000 : ℚ) vp01100111011 := join_branches bp011001110110 bp011001110111
private noncomputable def vp011001110101_0 : Blocks := edgeBlocks% "full/vectors/011001110101-V-0000.bin"
noncomputable def vp011001110101 : Blocks := vp011001110101_0
theorem coverp011001110101 : Covers (-3305761639/2000000 : ℚ) vp011001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp011001110100_0 : Blocks := edgeBlocks% "full/vectors/011001110100-V-0000.bin"
noncomputable def vp011001110100 : Blocks := vp011001110100_0
theorem coverp011001110100 : Covers (-3303761639/2000000 : ℚ) vp011001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100111010_0 : Blocks := edgeBlocks% "full/vectors/01100111010-V-0000.bin"
noncomputable def vp01100111010 : Blocks := vp01100111010_0
private theorem bp011001110100 : Branch 0 (-3303761639/4000000 : ℚ) vp01100111010 := by
  apply branch_left_normalized (c:=vp011001110100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3303761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3303761639/2000000 : ℚ) by norm_num]
  exact coverp011001110100
private noncomputable def ep011001110101_0 : Blocks := edgeBlocks% "full/vectors/011001110101-E-0000.bin"
noncomputable def ep011001110101 : Blocks := ep011001110101_0
private theorem idp011001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100111010.list =
    C ((2:ℤ)^101) * horner X vp011001110101.list + horner X ep011001110101.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001110101 : Branch 1 (-3303761639/4000000 : ℚ) vp01100111010 := by
  apply branch_checked idp011001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3303761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3305761639/2000000 : ℚ) by norm_num]
  exact coverp011001110101
theorem coverp01100111010 : Covers (-3303761639/4000000 : ℚ) vp01100111010 := join_branches bp011001110100 bp011001110101
private noncomputable def vp0110011101_0 : Blocks := edgeBlocks% "full/vectors/0110011101-V-0000.bin"
private noncomputable def vp0110011101_1 : Blocks := edgeBlocks% "full/vectors/0110011101-V-0001.bin"
noncomputable def vp0110011101 : Blocks := (Blocks.join vp0110011101_0 vp0110011101_1)
private theorem bp01100111010 : Branch 0 (-3303761639/8000000 : ℚ) vp0110011101 := by
  apply branch_left_normalized (c:=vp01100111010) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-3303761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3303761639/4000000 : ℚ) by norm_num]
  exact coverp01100111010
private noncomputable def ep01100111011_0 : Blocks := edgeBlocks% "full/vectors/01100111011-E-0000.bin"
private noncomputable def ep01100111011_1 : Blocks := edgeBlocks% "full/vectors/01100111011-E-0001.bin"
noncomputable def ep01100111011 : Blocks := (Blocks.join ep01100111011_0 ep01100111011_1)
private theorem idp01100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110011101.list =
    C ((2:ℤ)^182) * horner X vp01100111011.list + horner X ep01100111011.list := by
  exact edge_identity (B := (2:ℤ)^332) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100111011 : Branch 1 (-3303761639/8000000 : ℚ) vp0110011101 := by
  apply branch_checked idp01100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3303761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3307761639/4000000 : ℚ) by norm_num]
  exact coverp01100111011
theorem coverp0110011101 : Covers (-3303761639/8000000 : ℚ) vp0110011101 := join_branches bp01100111010 bp01100111011
private noncomputable def vp011001110011_0 : Blocks := edgeBlocks% "full/vectors/011001110011-V-0000.bin"
noncomputable def vp011001110011 : Blocks := vp011001110011_0
theorem coverp011001110011 : Covers (-3301761639/2000000 : ℚ) vp011001110011 := cover_leaf (by decide +kernel)
private noncomputable def vp011001110010_0 : Blocks := edgeBlocks% "full/vectors/011001110010-V-0000.bin"
noncomputable def vp011001110010 : Blocks := vp011001110010_0
theorem coverp011001110010 : Covers (-3299761639/2000000 : ℚ) vp011001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100111001_0 : Blocks := edgeBlocks% "full/vectors/01100111001-V-0000.bin"
noncomputable def vp01100111001 : Blocks := vp01100111001_0
private theorem bp011001110010 : Branch 0 (-3299761639/4000000 : ℚ) vp01100111001 := by
  apply branch_left_normalized (c:=vp011001110010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3299761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3299761639/2000000 : ℚ) by norm_num]
  exact coverp011001110010
private noncomputable def ep011001110011_0 : Blocks := edgeBlocks% "full/vectors/011001110011-E-0000.bin"
noncomputable def ep011001110011 : Blocks := ep011001110011_0
private theorem idp011001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100111001.list =
    C ((2:ℤ)^101) * horner X vp011001110011.list + horner X ep011001110011.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001110011 : Branch 1 (-3299761639/4000000 : ℚ) vp01100111001 := by
  apply branch_checked idp011001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3299761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3301761639/2000000 : ℚ) by norm_num]
  exact coverp011001110011
theorem coverp01100111001 : Covers (-3299761639/4000000 : ℚ) vp01100111001 := join_branches bp011001110010 bp011001110011
private noncomputable def vp011001110001_0 : Blocks := edgeBlocks% "full/vectors/011001110001-V-0000.bin"
noncomputable def vp011001110001 : Blocks := vp011001110001_0
theorem coverp011001110001 : Covers (-3297761639/2000000 : ℚ) vp011001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp011001110000_0 : Blocks := edgeBlocks% "full/vectors/011001110000-V-0000.bin"
noncomputable def vp011001110000 : Blocks := vp011001110000_0
theorem coverp011001110000 : Covers (-3295761639/2000000 : ℚ) vp011001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100111000_0 : Blocks := edgeBlocks% "full/vectors/01100111000-V-0000.bin"
noncomputable def vp01100111000 : Blocks := vp01100111000_0
private theorem bp011001110000 : Branch 0 (-3295761639/4000000 : ℚ) vp01100111000 := by
  apply branch_left_normalized (c:=vp011001110000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3295761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3295761639/2000000 : ℚ) by norm_num]
  exact coverp011001110000
private noncomputable def ep011001110001_0 : Blocks := edgeBlocks% "full/vectors/011001110001-E-0000.bin"
noncomputable def ep011001110001 : Blocks := ep011001110001_0
private theorem idp011001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100111000.list =
    C ((2:ℤ)^103) * horner X vp011001110001.list + horner X ep011001110001.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001110001 : Branch 1 (-3295761639/4000000 : ℚ) vp01100111000 := by
  apply branch_checked idp011001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3295761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3297761639/2000000 : ℚ) by norm_num]
  exact coverp011001110001
theorem coverp01100111000 : Covers (-3295761639/4000000 : ℚ) vp01100111000 := join_branches bp011001110000 bp011001110001
private noncomputable def vp0110011100_0 : Blocks := edgeBlocks% "full/vectors/0110011100-V-0000.bin"
private noncomputable def vp0110011100_1 : Blocks := edgeBlocks% "full/vectors/0110011100-V-0001.bin"
noncomputable def vp0110011100 : Blocks := (Blocks.join vp0110011100_0 vp0110011100_1)
private theorem bp01100111000 : Branch 0 (-3295761639/8000000 : ℚ) vp0110011100 := by
  apply branch_left_normalized (c:=vp01100111000) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3295761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3295761639/4000000 : ℚ) by norm_num]
  exact coverp01100111000
private noncomputable def ep01100111001_0 : Blocks := edgeBlocks% "full/vectors/01100111001-E-0000.bin"
private noncomputable def ep01100111001_1 : Blocks := edgeBlocks% "full/vectors/01100111001-E-0001.bin"
noncomputable def ep01100111001 : Blocks := (Blocks.join ep01100111001_0 ep01100111001_1)
private theorem idp01100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110011100.list =
    C ((2:ℤ)^183) * horner X vp01100111001.list + horner X ep01100111001.list := by
  exact edge_identity (B := (2:ℤ)^333) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100111001 : Branch 1 (-3295761639/8000000 : ℚ) vp0110011100 := by
  apply branch_checked idp01100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3295761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3299761639/4000000 : ℚ) by norm_num]
  exact coverp01100111001
theorem coverp0110011100 : Covers (-3295761639/8000000 : ℚ) vp0110011100 := join_branches bp01100111000 bp01100111001
private noncomputable def vp011001110_0 : Blocks := edgeBlocks% "full/vectors/011001110-V-0000.bin"
private noncomputable def vp011001110_1 : Blocks := edgeBlocks% "full/vectors/011001110-V-0001.bin"
private noncomputable def vp011001110_2 : Blocks := edgeBlocks% "full/vectors/011001110-V-0002.bin"
noncomputable def vp011001110 : Blocks := (Blocks.join vp011001110_0 (Blocks.join vp011001110_1 vp011001110_2))
private theorem bp0110011100 : Branch 0 (-3295761639/16000000 : ℚ) vp011001110 := by
  apply branch_left_normalized (c:=vp0110011100) (k:=0) (m:=158) (by decide +kernel)
  rw [show 2*(-3295761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3295761639/8000000 : ℚ) by norm_num]
  exact coverp0110011100
private noncomputable def ep0110011101_0 : Blocks := edgeBlocks% "full/vectors/0110011101-E-0000.bin"
private noncomputable def ep0110011101_1 : Blocks := edgeBlocks% "full/vectors/0110011101-E-0001.bin"
private noncomputable def ep0110011101_2 : Blocks := edgeBlocks% "full/vectors/0110011101-E-0002.bin"
noncomputable def ep0110011101 : Blocks := (Blocks.join ep0110011101_0 (Blocks.join ep0110011101_1 ep0110011101_2))
private theorem idp0110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011001110.list =
    C ((2:ℤ)^344) * horner X vp0110011101.list + horner X ep0110011101.list := by
  exact edge_identity (B := (2:ℤ)^544) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110011101 : Branch 1 (-3295761639/16000000 : ℚ) vp011001110 := by
  apply branch_checked idp0110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3295761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3303761639/8000000 : ℚ) by norm_num]
  exact coverp0110011101
theorem coverp011001110 : Covers (-3295761639/16000000 : ℚ) vp011001110 := join_branches bp0110011100 bp0110011101
private noncomputable def vp01100111_0 : Blocks := edgeBlocks% "full/vectors/01100111-V-0000.bin"
private noncomputable def vp01100111_1 : Blocks := edgeBlocks% "full/vectors/01100111-V-0001.bin"
private noncomputable def vp01100111_2 : Blocks := edgeBlocks% "full/vectors/01100111-V-0002.bin"
private noncomputable def vp01100111_3 : Blocks := edgeBlocks% "full/vectors/01100111-V-0003.bin"
private noncomputable def vp01100111_4 : Blocks := edgeBlocks% "full/vectors/01100111-V-0004.bin"
noncomputable def vp01100111 : Blocks := (Blocks.join (Blocks.join vp01100111_0 vp01100111_1) (Blocks.join vp01100111_2 (Blocks.join vp01100111_3 vp01100111_4)))
private theorem bp011001110 : Branch 0 (-3295761639/32000000 : ℚ) vp01100111 := by
  apply branch_left_normalized (c:=vp011001110) (k:=0) (m:=296) (by decide +kernel)
  rw [show 2*(-3295761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3295761639/16000000 : ℚ) by norm_num]
  exact coverp011001110
private noncomputable def ep011001111_0 : Blocks := edgeBlocks% "full/vectors/011001111-E-0000.bin"
private noncomputable def ep011001111_1 : Blocks := edgeBlocks% "full/vectors/011001111-E-0001.bin"
private noncomputable def ep011001111_2 : Blocks := edgeBlocks% "full/vectors/011001111-E-0002.bin"
private noncomputable def ep011001111_3 : Blocks := edgeBlocks% "full/vectors/011001111-E-0003.bin"
private noncomputable def ep011001111_4 : Blocks := edgeBlocks% "full/vectors/011001111-E-0004.bin"
noncomputable def ep011001111 : Blocks := (Blocks.join (Blocks.join ep011001111_0 ep011001111_1) (Blocks.join ep011001111_2 (Blocks.join ep011001111_3 ep011001111_4)))
private theorem idp011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100111.list =
    C ((2:ℤ)^660) * horner X vp011001111.list + horner X ep011001111.list := by
  exact edge_identity (B := (2:ℤ)^959) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001111 : Branch 1 (-3295761639/32000000 : ℚ) vp01100111 := by
  apply branch_checked idp011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3295761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3311761639/16000000 : ℚ) by norm_num]
  exact coverp011001111
theorem coverp01100111 : Covers (-3295761639/32000000 : ℚ) vp01100111 := join_branches bp011001110 bp011001111
private noncomputable def vp011001101111_0 : Blocks := edgeBlocks% "full/vectors/011001101111-V-0000.bin"
noncomputable def vp011001101111 : Blocks := vp011001101111_0
theorem coverp011001101111 : Covers (-3293761639/2000000 : ℚ) vp011001101111 := cover_leaf (by decide +kernel)
private noncomputable def vp011001101110_0 : Blocks := edgeBlocks% "full/vectors/011001101110-V-0000.bin"
noncomputable def vp011001101110 : Blocks := vp011001101110_0
theorem coverp011001101110 : Covers (-3291761639/2000000 : ℚ) vp011001101110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100110111_0 : Blocks := edgeBlocks% "full/vectors/01100110111-V-0000.bin"
noncomputable def vp01100110111 : Blocks := vp01100110111_0
private theorem bp011001101110 : Branch 0 (-3291761639/4000000 : ℚ) vp01100110111 := by
  apply branch_left_normalized (c:=vp011001101110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3291761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3291761639/2000000 : ℚ) by norm_num]
  exact coverp011001101110
private noncomputable def ep011001101111_0 : Blocks := edgeBlocks% "full/vectors/011001101111-E-0000.bin"
noncomputable def ep011001101111 : Blocks := ep011001101111_0
private theorem idp011001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100110111.list =
    C ((2:ℤ)^102) * horner X vp011001101111.list + horner X ep011001101111.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001101111 : Branch 1 (-3291761639/4000000 : ℚ) vp01100110111 := by
  apply branch_checked idp011001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3291761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3293761639/2000000 : ℚ) by norm_num]
  exact coverp011001101111
theorem coverp01100110111 : Covers (-3291761639/4000000 : ℚ) vp01100110111 := join_branches bp011001101110 bp011001101111
private noncomputable def vp011001101101_0 : Blocks := edgeBlocks% "full/vectors/011001101101-V-0000.bin"
noncomputable def vp011001101101 : Blocks := vp011001101101_0
theorem coverp011001101101 : Covers (-3289761639/2000000 : ℚ) vp011001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp011001101100_0 : Blocks := edgeBlocks% "full/vectors/011001101100-V-0000.bin"
noncomputable def vp011001101100 : Blocks := vp011001101100_0
theorem coverp011001101100 : Covers (-3287761639/2000000 : ℚ) vp011001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100110110_0 : Blocks := edgeBlocks% "full/vectors/01100110110-V-0000.bin"
noncomputable def vp01100110110 : Blocks := vp01100110110_0
private theorem bp011001101100 : Branch 0 (-3287761639/4000000 : ℚ) vp01100110110 := by
  apply branch_left_normalized (c:=vp011001101100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3287761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3287761639/2000000 : ℚ) by norm_num]
  exact coverp011001101100
private noncomputable def ep011001101101_0 : Blocks := edgeBlocks% "full/vectors/011001101101-E-0000.bin"
noncomputable def ep011001101101 : Blocks := ep011001101101_0
private theorem idp011001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100110110.list =
    C ((2:ℤ)^102) * horner X vp011001101101.list + horner X ep011001101101.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001101101 : Branch 1 (-3287761639/4000000 : ℚ) vp01100110110 := by
  apply branch_checked idp011001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-3287761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3289761639/2000000 : ℚ) by norm_num]
  exact coverp011001101101
theorem coverp01100110110 : Covers (-3287761639/4000000 : ℚ) vp01100110110 := join_branches bp011001101100 bp011001101101
private noncomputable def vp0110011011_0 : Blocks := edgeBlocks% "full/vectors/0110011011-V-0000.bin"
private noncomputable def vp0110011011_1 : Blocks := edgeBlocks% "full/vectors/0110011011-V-0001.bin"
noncomputable def vp0110011011 : Blocks := (Blocks.join vp0110011011_0 vp0110011011_1)
private theorem bp01100110110 : Branch 0 (-3287761639/8000000 : ℚ) vp0110011011 := by
  apply branch_left_normalized (c:=vp01100110110) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-3287761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3287761639/4000000 : ℚ) by norm_num]
  exact coverp01100110110
private noncomputable def ep01100110111_0 : Blocks := edgeBlocks% "full/vectors/01100110111-E-0000.bin"
private noncomputable def ep01100110111_1 : Blocks := edgeBlocks% "full/vectors/01100110111-E-0001.bin"
noncomputable def ep01100110111 : Blocks := (Blocks.join ep01100110111_0 ep01100110111_1)
private theorem idp01100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110011011.list =
    C ((2:ℤ)^183) * horner X vp01100110111.list + horner X ep01100110111.list := by
  exact edge_identity (B := (2:ℤ)^334) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100110111 : Branch 1 (-3287761639/8000000 : ℚ) vp0110011011 := by
  apply branch_checked idp01100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3287761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3291761639/4000000 : ℚ) by norm_num]
  exact coverp01100110111
theorem coverp0110011011 : Covers (-3287761639/8000000 : ℚ) vp0110011011 := join_branches bp01100110110 bp01100110111
private noncomputable def vp011001101011_0 : Blocks := edgeBlocks% "full/vectors/011001101011-V-0000.bin"
noncomputable def vp011001101011 : Blocks := vp011001101011_0
theorem coverp011001101011 : Covers (-3285761639/2000000 : ℚ) vp011001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp011001101010_0 : Blocks := edgeBlocks% "full/vectors/011001101010-V-0000.bin"
noncomputable def vp011001101010 : Blocks := vp011001101010_0
theorem coverp011001101010 : Covers (-3283761639/2000000 : ℚ) vp011001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100110101_0 : Blocks := edgeBlocks% "full/vectors/01100110101-V-0000.bin"
noncomputable def vp01100110101 : Blocks := vp01100110101_0
private theorem bp011001101010 : Branch 0 (-3283761639/4000000 : ℚ) vp01100110101 := by
  apply branch_left_normalized (c:=vp011001101010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3283761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3283761639/2000000 : ℚ) by norm_num]
  exact coverp011001101010
private noncomputable def ep011001101011_0 : Blocks := edgeBlocks% "full/vectors/011001101011-E-0000.bin"
noncomputable def ep011001101011 : Blocks := ep011001101011_0
private theorem idp011001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100110101.list =
    C ((2:ℤ)^102) * horner X vp011001101011.list + horner X ep011001101011.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001101011 : Branch 1 (-3283761639/4000000 : ℚ) vp01100110101 := by
  apply branch_checked idp011001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-3283761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3285761639/2000000 : ℚ) by norm_num]
  exact coverp011001101011
theorem coverp01100110101 : Covers (-3283761639/4000000 : ℚ) vp01100110101 := join_branches bp011001101010 bp011001101011
private noncomputable def vp011001101001_0 : Blocks := edgeBlocks% "full/vectors/011001101001-V-0000.bin"
noncomputable def vp011001101001 : Blocks := vp011001101001_0
theorem coverp011001101001 : Covers (-3281761639/2000000 : ℚ) vp011001101001 := cover_leaf (by decide +kernel)
private noncomputable def vp011001101000_0 : Blocks := edgeBlocks% "full/vectors/011001101000-V-0000.bin"
noncomputable def vp011001101000 : Blocks := vp011001101000_0
theorem coverp011001101000 : Covers (-3279761639/2000000 : ℚ) vp011001101000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100110100_0 : Blocks := edgeBlocks% "full/vectors/01100110100-V-0000.bin"
noncomputable def vp01100110100 : Blocks := vp01100110100_0
private theorem bp011001101000 : Branch 0 (-3279761639/4000000 : ℚ) vp01100110100 := by
  apply branch_left_normalized (c:=vp011001101000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3279761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3279761639/2000000 : ℚ) by norm_num]
  exact coverp011001101000
private noncomputable def ep011001101001_0 : Blocks := edgeBlocks% "full/vectors/011001101001-E-0000.bin"
noncomputable def ep011001101001 : Blocks := ep011001101001_0
private theorem idp011001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100110100.list =
    C ((2:ℤ)^103) * horner X vp011001101001.list + horner X ep011001101001.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001101001 : Branch 1 (-3279761639/4000000 : ℚ) vp01100110100 := by
  apply branch_checked idp011001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-3279761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3281761639/2000000 : ℚ) by norm_num]
  exact coverp011001101001
theorem coverp01100110100 : Covers (-3279761639/4000000 : ℚ) vp01100110100 := join_branches bp011001101000 bp011001101001
private noncomputable def vp0110011010_0 : Blocks := edgeBlocks% "full/vectors/0110011010-V-0000.bin"
private noncomputable def vp0110011010_1 : Blocks := edgeBlocks% "full/vectors/0110011010-V-0001.bin"
noncomputable def vp0110011010 : Blocks := (Blocks.join vp0110011010_0 vp0110011010_1)
private theorem bp01100110100 : Branch 0 (-3279761639/8000000 : ℚ) vp0110011010 := by
  apply branch_left_normalized (c:=vp01100110100) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3279761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3279761639/4000000 : ℚ) by norm_num]
  exact coverp01100110100
private noncomputable def ep01100110101_0 : Blocks := edgeBlocks% "full/vectors/01100110101-E-0000.bin"
private noncomputable def ep01100110101_1 : Blocks := edgeBlocks% "full/vectors/01100110101-E-0001.bin"
noncomputable def ep01100110101 : Blocks := (Blocks.join ep01100110101_0 ep01100110101_1)
private theorem idp01100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110011010.list =
    C ((2:ℤ)^183) * horner X vp01100110101.list + horner X ep01100110101.list := by
  exact edge_identity (B := (2:ℤ)^334) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100110101 : Branch 1 (-3279761639/8000000 : ℚ) vp0110011010 := by
  apply branch_checked idp01100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3279761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3283761639/4000000 : ℚ) by norm_num]
  exact coverp01100110101
theorem coverp0110011010 : Covers (-3279761639/8000000 : ℚ) vp0110011010 := join_branches bp01100110100 bp01100110101
private noncomputable def vp011001101_0 : Blocks := edgeBlocks% "full/vectors/011001101-V-0000.bin"
private noncomputable def vp011001101_1 : Blocks := edgeBlocks% "full/vectors/011001101-V-0001.bin"
private noncomputable def vp011001101_2 : Blocks := edgeBlocks% "full/vectors/011001101-V-0002.bin"
noncomputable def vp011001101 : Blocks := (Blocks.join vp011001101_0 (Blocks.join vp011001101_1 vp011001101_2))
private theorem bp0110011010 : Branch 0 (-3279761639/16000000 : ℚ) vp011001101 := by
  apply branch_left_normalized (c:=vp0110011010) (k:=0) (m:=159) (by decide +kernel)
  rw [show 2*(-3279761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3279761639/8000000 : ℚ) by norm_num]
  exact coverp0110011010
private noncomputable def ep0110011011_0 : Blocks := edgeBlocks% "full/vectors/0110011011-E-0000.bin"
private noncomputable def ep0110011011_1 : Blocks := edgeBlocks% "full/vectors/0110011011-E-0001.bin"
private noncomputable def ep0110011011_2 : Blocks := edgeBlocks% "full/vectors/0110011011-E-0002.bin"
noncomputable def ep0110011011 : Blocks := (Blocks.join ep0110011011_0 (Blocks.join ep0110011011_1 ep0110011011_2))
private theorem idp0110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011001101.list =
    C ((2:ℤ)^343) * horner X vp0110011011.list + horner X ep0110011011.list := by
  exact edge_identity (B := (2:ℤ)^544) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110011011 : Branch 1 (-3279761639/16000000 : ℚ) vp011001101 := by
  apply branch_checked idp0110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3279761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3287761639/8000000 : ℚ) by norm_num]
  exact coverp0110011011
theorem coverp011001101 : Covers (-3279761639/16000000 : ℚ) vp011001101 := join_branches bp0110011010 bp0110011011
private noncomputable def vp011001100111_0 : Blocks := edgeBlocks% "full/vectors/011001100111-V-0000.bin"
noncomputable def vp011001100111 : Blocks := vp011001100111_0
theorem coverp011001100111 : Covers (-3277761639/2000000 : ℚ) vp011001100111 := cover_leaf (by decide +kernel)
private noncomputable def vp011001100110_0 : Blocks := edgeBlocks% "full/vectors/011001100110-V-0000.bin"
noncomputable def vp011001100110 : Blocks := vp011001100110_0
theorem coverp011001100110 : Covers (-3275761639/2000000 : ℚ) vp011001100110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100110011_0 : Blocks := edgeBlocks% "full/vectors/01100110011-V-0000.bin"
noncomputable def vp01100110011 : Blocks := vp01100110011_0
private theorem bp011001100110 : Branch 0 (-3275761639/4000000 : ℚ) vp01100110011 := by
  apply branch_left_normalized (c:=vp011001100110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3275761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3275761639/2000000 : ℚ) by norm_num]
  exact coverp011001100110
private noncomputable def ep011001100111_0 : Blocks := edgeBlocks% "full/vectors/011001100111-E-0000.bin"
noncomputable def ep011001100111 : Blocks := ep011001100111_0
private theorem idp011001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100110011.list =
    C ((2:ℤ)^102) * horner X vp011001100111.list + horner X ep011001100111.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001100111 : Branch 1 (-3275761639/4000000 : ℚ) vp01100110011 := by
  apply branch_checked idp011001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3275761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3277761639/2000000 : ℚ) by norm_num]
  exact coverp011001100111
theorem coverp01100110011 : Covers (-3275761639/4000000 : ℚ) vp01100110011 := join_branches bp011001100110 bp011001100111
private noncomputable def vp011001100101_0 : Blocks := edgeBlocks% "full/vectors/011001100101-V-0000.bin"
noncomputable def vp011001100101 : Blocks := vp011001100101_0
theorem coverp011001100101 : Covers (-3273761639/2000000 : ℚ) vp011001100101 := cover_leaf (by decide +kernel)
private noncomputable def vp011001100100_0 : Blocks := edgeBlocks% "full/vectors/011001100100-V-0000.bin"
noncomputable def vp011001100100 : Blocks := vp011001100100_0
theorem coverp011001100100 : Covers (-3271761639/2000000 : ℚ) vp011001100100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100110010_0 : Blocks := edgeBlocks% "full/vectors/01100110010-V-0000.bin"
noncomputable def vp01100110010 : Blocks := vp01100110010_0
private theorem bp011001100100 : Branch 0 (-3271761639/4000000 : ℚ) vp01100110010 := by
  apply branch_left_normalized (c:=vp011001100100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3271761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3271761639/2000000 : ℚ) by norm_num]
  exact coverp011001100100
private noncomputable def ep011001100101_0 : Blocks := edgeBlocks% "full/vectors/011001100101-E-0000.bin"
noncomputable def ep011001100101 : Blocks := ep011001100101_0
private theorem idp011001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100110010.list =
    C ((2:ℤ)^101) * horner X vp011001100101.list + horner X ep011001100101.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001100101 : Branch 1 (-3271761639/4000000 : ℚ) vp01100110010 := by
  apply branch_checked idp011001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3271761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3273761639/2000000 : ℚ) by norm_num]
  exact coverp011001100101
theorem coverp01100110010 : Covers (-3271761639/4000000 : ℚ) vp01100110010 := join_branches bp011001100100 bp011001100101
private noncomputable def vp0110011001_0 : Blocks := edgeBlocks% "full/vectors/0110011001-V-0000.bin"
private noncomputable def vp0110011001_1 : Blocks := edgeBlocks% "full/vectors/0110011001-V-0001.bin"
noncomputable def vp0110011001 : Blocks := (Blocks.join vp0110011001_0 vp0110011001_1)
private theorem bp01100110010 : Branch 0 (-3271761639/8000000 : ℚ) vp0110011001 := by
  apply branch_left_normalized (c:=vp01100110010) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-3271761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3271761639/4000000 : ℚ) by norm_num]
  exact coverp01100110010
private noncomputable def ep01100110011_0 : Blocks := edgeBlocks% "full/vectors/01100110011-E-0000.bin"
private noncomputable def ep01100110011_1 : Blocks := edgeBlocks% "full/vectors/01100110011-E-0001.bin"
noncomputable def ep01100110011 : Blocks := (Blocks.join ep01100110011_0 ep01100110011_1)
private theorem idp01100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110011001.list =
    C ((2:ℤ)^183) * horner X vp01100110011.list + horner X ep01100110011.list := by
  exact edge_identity (B := (2:ℤ)^334) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100110011 : Branch 1 (-3271761639/8000000 : ℚ) vp0110011001 := by
  apply branch_checked idp01100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3271761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3275761639/4000000 : ℚ) by norm_num]
  exact coverp01100110011
theorem coverp0110011001 : Covers (-3271761639/8000000 : ℚ) vp0110011001 := join_branches bp01100110010 bp01100110011
private noncomputable def vp011001100011_0 : Blocks := edgeBlocks% "full/vectors/011001100011-V-0000.bin"
noncomputable def vp011001100011 : Blocks := vp011001100011_0
theorem coverp011001100011 : Covers (-3269761639/2000000 : ℚ) vp011001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp011001100010_0 : Blocks := edgeBlocks% "full/vectors/011001100010-V-0000.bin"
noncomputable def vp011001100010 : Blocks := vp011001100010_0
theorem coverp011001100010 : Covers (-3267761639/2000000 : ℚ) vp011001100010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100110001_0 : Blocks := edgeBlocks% "full/vectors/01100110001-V-0000.bin"
noncomputable def vp01100110001 : Blocks := vp01100110001_0
private theorem bp011001100010 : Branch 0 (-3267761639/4000000 : ℚ) vp01100110001 := by
  apply branch_left_normalized (c:=vp011001100010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3267761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3267761639/2000000 : ℚ) by norm_num]
  exact coverp011001100010
private noncomputable def ep011001100011_0 : Blocks := edgeBlocks% "full/vectors/011001100011-E-0000.bin"
noncomputable def ep011001100011 : Blocks := ep011001100011_0
private theorem idp011001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100110001.list =
    C ((2:ℤ)^101) * horner X vp011001100011.list + horner X ep011001100011.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001100011 : Branch 1 (-3267761639/4000000 : ℚ) vp01100110001 := by
  apply branch_checked idp011001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-3267761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3269761639/2000000 : ℚ) by norm_num]
  exact coverp011001100011
theorem coverp01100110001 : Covers (-3267761639/4000000 : ℚ) vp01100110001 := join_branches bp011001100010 bp011001100011
private noncomputable def vp011001100001_0 : Blocks := edgeBlocks% "full/vectors/011001100001-V-0000.bin"
noncomputable def vp011001100001 : Blocks := vp011001100001_0
theorem coverp011001100001 : Covers (-3265761639/2000000 : ℚ) vp011001100001 := cover_leaf (by decide +kernel)
private noncomputable def vp011001100000_0 : Blocks := edgeBlocks% "full/vectors/011001100000-V-0000.bin"
noncomputable def vp011001100000 : Blocks := vp011001100000_0
theorem coverp011001100000 : Covers (-3263761639/2000000 : ℚ) vp011001100000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100110000_0 : Blocks := edgeBlocks% "full/vectors/01100110000-V-0000.bin"
noncomputable def vp01100110000 : Blocks := vp01100110000_0
private theorem bp011001100000 : Branch 0 (-3263761639/4000000 : ℚ) vp01100110000 := by
  apply branch_left_normalized (c:=vp011001100000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3263761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3263761639/2000000 : ℚ) by norm_num]
  exact coverp011001100000
private noncomputable def ep011001100001_0 : Blocks := edgeBlocks% "full/vectors/011001100001-E-0000.bin"
noncomputable def ep011001100001 : Blocks := ep011001100001_0
private theorem idp011001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100110000.list =
    C ((2:ℤ)^102) * horner X vp011001100001.list + horner X ep011001100001.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001100001 : Branch 1 (-3263761639/4000000 : ℚ) vp01100110000 := by
  apply branch_checked idp011001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3263761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3265761639/2000000 : ℚ) by norm_num]
  exact coverp011001100001
theorem coverp01100110000 : Covers (-3263761639/4000000 : ℚ) vp01100110000 := join_branches bp011001100000 bp011001100001
private noncomputable def vp0110011000_0 : Blocks := edgeBlocks% "full/vectors/0110011000-V-0000.bin"
private noncomputable def vp0110011000_1 : Blocks := edgeBlocks% "full/vectors/0110011000-V-0001.bin"
noncomputable def vp0110011000 : Blocks := (Blocks.join vp0110011000_0 vp0110011000_1)
private theorem bp01100110000 : Branch 0 (-3263761639/8000000 : ℚ) vp0110011000 := by
  apply branch_left_normalized (c:=vp01100110000) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3263761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3263761639/4000000 : ℚ) by norm_num]
  exact coverp01100110000
private noncomputable def ep01100110001_0 : Blocks := edgeBlocks% "full/vectors/01100110001-E-0000.bin"
private noncomputable def ep01100110001_1 : Blocks := edgeBlocks% "full/vectors/01100110001-E-0001.bin"
noncomputable def ep01100110001 : Blocks := (Blocks.join ep01100110001_0 ep01100110001_1)
private theorem idp01100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110011000.list =
    C ((2:ℤ)^184) * horner X vp01100110001.list + horner X ep01100110001.list := by
  exact edge_identity (B := (2:ℤ)^335) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100110001 : Branch 1 (-3263761639/8000000 : ℚ) vp0110011000 := by
  apply branch_checked idp01100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3263761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3267761639/4000000 : ℚ) by norm_num]
  exact coverp01100110001
theorem coverp0110011000 : Covers (-3263761639/8000000 : ℚ) vp0110011000 := join_branches bp01100110000 bp01100110001
private noncomputable def vp011001100_0 : Blocks := edgeBlocks% "full/vectors/011001100-V-0000.bin"
private noncomputable def vp011001100_1 : Blocks := edgeBlocks% "full/vectors/011001100-V-0001.bin"
private noncomputable def vp011001100_2 : Blocks := edgeBlocks% "full/vectors/011001100-V-0002.bin"
noncomputable def vp011001100 : Blocks := (Blocks.join vp011001100_0 (Blocks.join vp011001100_1 vp011001100_2))
private theorem bp0110011000 : Branch 0 (-3263761639/16000000 : ℚ) vp011001100 := by
  apply branch_left_normalized (c:=vp0110011000) (k:=0) (m:=160) (by decide +kernel)
  rw [show 2*(-3263761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3263761639/8000000 : ℚ) by norm_num]
  exact coverp0110011000
private noncomputable def ep0110011001_0 : Blocks := edgeBlocks% "full/vectors/0110011001-E-0000.bin"
private noncomputable def ep0110011001_1 : Blocks := edgeBlocks% "full/vectors/0110011001-E-0001.bin"
private noncomputable def ep0110011001_2 : Blocks := edgeBlocks% "full/vectors/0110011001-E-0002.bin"
noncomputable def ep0110011001 : Blocks := (Blocks.join ep0110011001_0 (Blocks.join ep0110011001_1 ep0110011001_2))
private theorem idp0110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011001100.list =
    C ((2:ℤ)^344) * horner X vp0110011001.list + horner X ep0110011001.list := by
  exact edge_identity (B := (2:ℤ)^545) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110011001 : Branch 1 (-3263761639/16000000 : ℚ) vp011001100 := by
  apply branch_checked idp0110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3263761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3271761639/8000000 : ℚ) by norm_num]
  exact coverp0110011001
theorem coverp011001100 : Covers (-3263761639/16000000 : ℚ) vp011001100 := join_branches bp0110011000 bp0110011001
private noncomputable def vp01100110_0 : Blocks := edgeBlocks% "full/vectors/01100110-V-0000.bin"
private noncomputable def vp01100110_1 : Blocks := edgeBlocks% "full/vectors/01100110-V-0001.bin"
private noncomputable def vp01100110_2 : Blocks := edgeBlocks% "full/vectors/01100110-V-0002.bin"
private noncomputable def vp01100110_3 : Blocks := edgeBlocks% "full/vectors/01100110-V-0003.bin"
private noncomputable def vp01100110_4 : Blocks := edgeBlocks% "full/vectors/01100110-V-0004.bin"
noncomputable def vp01100110 : Blocks := (Blocks.join (Blocks.join vp01100110_0 vp01100110_1) (Blocks.join vp01100110_2 (Blocks.join vp01100110_3 vp01100110_4)))
private theorem bp011001100 : Branch 0 (-3263761639/32000000 : ℚ) vp01100110 := by
  apply branch_left_normalized (c:=vp011001100) (k:=0) (m:=297) (by decide +kernel)
  rw [show 2*(-3263761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3263761639/16000000 : ℚ) by norm_num]
  exact coverp011001100
private noncomputable def ep011001101_0 : Blocks := edgeBlocks% "full/vectors/011001101-E-0000.bin"
private noncomputable def ep011001101_1 : Blocks := edgeBlocks% "full/vectors/011001101-E-0001.bin"
private noncomputable def ep011001101_2 : Blocks := edgeBlocks% "full/vectors/011001101-E-0002.bin"
private noncomputable def ep011001101_3 : Blocks := edgeBlocks% "full/vectors/011001101-E-0003.bin"
private noncomputable def ep011001101_4 : Blocks := edgeBlocks% "full/vectors/011001101-E-0004.bin"
noncomputable def ep011001101 : Blocks := (Blocks.join (Blocks.join ep011001101_0 ep011001101_1) (Blocks.join ep011001101_2 (Blocks.join ep011001101_3 ep011001101_4)))
private theorem idp011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100110.list =
    C ((2:ℤ)^662) * horner X vp011001101.list + horner X ep011001101.list := by
  exact edge_identity (B := (2:ℤ)^962) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001101 : Branch 1 (-3263761639/32000000 : ℚ) vp01100110 := by
  apply branch_checked idp011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3263761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3279761639/16000000 : ℚ) by norm_num]
  exact coverp011001101
theorem coverp01100110 : Covers (-3263761639/32000000 : ℚ) vp01100110 := join_branches bp011001100 bp011001101
private noncomputable def vp0110011_0 : Blocks := edgeBlocks% "full/vectors/0110011-V-0000.bin"
private noncomputable def vp0110011_1 : Blocks := edgeBlocks% "full/vectors/0110011-V-0001.bin"
private noncomputable def vp0110011_2 : Blocks := edgeBlocks% "full/vectors/0110011-V-0002.bin"
private noncomputable def vp0110011_3 : Blocks := edgeBlocks% "full/vectors/0110011-V-0003.bin"
private noncomputable def vp0110011_4 : Blocks := edgeBlocks% "full/vectors/0110011-V-0004.bin"
private noncomputable def vp0110011_5 : Blocks := edgeBlocks% "full/vectors/0110011-V-0005.bin"
private noncomputable def vp0110011_6 : Blocks := edgeBlocks% "full/vectors/0110011-V-0006.bin"
private noncomputable def vp0110011_7 : Blocks := edgeBlocks% "full/vectors/0110011-V-0007.bin"
private noncomputable def vp0110011_8 : Blocks := edgeBlocks% "full/vectors/0110011-V-0008.bin"
noncomputable def vp0110011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0110011_0 vp0110011_1) (Blocks.join vp0110011_2 vp0110011_3)) (Blocks.join (Blocks.join vp0110011_4 vp0110011_5) (Blocks.join vp0110011_6 (Blocks.join vp0110011_7 vp0110011_8))))
private theorem bp01100110 : Branch 0 (-3263761639/64000000 : ℚ) vp0110011 := by
  apply branch_left_normalized (c:=vp01100110) (k:=0) (m:=569) (by decide +kernel)
  rw [show 2*(-3263761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3263761639/32000000 : ℚ) by norm_num]
  exact coverp01100110
private noncomputable def ep01100111_0 : Blocks := edgeBlocks% "full/vectors/01100111-E-0000.bin"
private noncomputable def ep01100111_1 : Blocks := edgeBlocks% "full/vectors/01100111-E-0001.bin"
private noncomputable def ep01100111_2 : Blocks := edgeBlocks% "full/vectors/01100111-E-0002.bin"
private noncomputable def ep01100111_3 : Blocks := edgeBlocks% "full/vectors/01100111-E-0003.bin"
private noncomputable def ep01100111_4 : Blocks := edgeBlocks% "full/vectors/01100111-E-0004.bin"
private noncomputable def ep01100111_5 : Blocks := edgeBlocks% "full/vectors/01100111-E-0005.bin"
private noncomputable def ep01100111_6 : Blocks := edgeBlocks% "full/vectors/01100111-E-0006.bin"
private noncomputable def ep01100111_7 : Blocks := edgeBlocks% "full/vectors/01100111-E-0007.bin"
private noncomputable def ep01100111_8 : Blocks := edgeBlocks% "full/vectors/01100111-E-0008.bin"
noncomputable def ep01100111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01100111_0 ep01100111_1) (Blocks.join ep01100111_2 ep01100111_3)) (Blocks.join (Blocks.join ep01100111_4 ep01100111_5) (Blocks.join ep01100111_6 (Blocks.join ep01100111_7 ep01100111_8))))
private theorem idp01100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110011.list =
    C ((2:ℤ)^1290) * horner X vp01100111.list + horner X ep01100111.list := by
  exact edge_identity (B := (2:ℤ)^1788) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100111 : Branch 1 (-3263761639/64000000 : ℚ) vp0110011 := by
  apply branch_checked idp01100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3263761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3295761639/32000000 : ℚ) by norm_num]
  exact coverp01100111
theorem coverp0110011 : Covers (-3263761639/64000000 : ℚ) vp0110011 := join_branches bp01100110 bp01100111
private noncomputable def vp011001011111_0 : Blocks := edgeBlocks% "full/vectors/011001011111-V-0000.bin"
noncomputable def vp011001011111 : Blocks := vp011001011111_0
theorem coverp011001011111 : Covers (-3261761639/2000000 : ℚ) vp011001011111 := cover_leaf (by decide +kernel)
private noncomputable def vp011001011110_0 : Blocks := edgeBlocks% "full/vectors/011001011110-V-0000.bin"
noncomputable def vp011001011110 : Blocks := vp011001011110_0
theorem coverp011001011110 : Covers (-3259761639/2000000 : ℚ) vp011001011110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100101111_0 : Blocks := edgeBlocks% "full/vectors/01100101111-V-0000.bin"
noncomputable def vp01100101111 : Blocks := vp01100101111_0
private theorem bp011001011110 : Branch 0 (-3259761639/4000000 : ℚ) vp01100101111 := by
  apply branch_left_normalized (c:=vp011001011110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3259761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3259761639/2000000 : ℚ) by norm_num]
  exact coverp011001011110
private noncomputable def ep011001011111_0 : Blocks := edgeBlocks% "full/vectors/011001011111-E-0000.bin"
noncomputable def ep011001011111 : Blocks := ep011001011111_0
private theorem idp011001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100101111.list =
    C ((2:ℤ)^102) * horner X vp011001011111.list + horner X ep011001011111.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001011111 : Branch 1 (-3259761639/4000000 : ℚ) vp01100101111 := by
  apply branch_checked idp011001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3259761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3261761639/2000000 : ℚ) by norm_num]
  exact coverp011001011111
theorem coverp01100101111 : Covers (-3259761639/4000000 : ℚ) vp01100101111 := join_branches bp011001011110 bp011001011111
private noncomputable def vp011001011101_0 : Blocks := edgeBlocks% "full/vectors/011001011101-V-0000.bin"
noncomputable def vp011001011101 : Blocks := vp011001011101_0
theorem coverp011001011101 : Covers (-3257761639/2000000 : ℚ) vp011001011101 := cover_leaf (by decide +kernel)
private noncomputable def vp011001011100_0 : Blocks := edgeBlocks% "full/vectors/011001011100-V-0000.bin"
noncomputable def vp011001011100 : Blocks := vp011001011100_0
theorem coverp011001011100 : Covers (-3255761639/2000000 : ℚ) vp011001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100101110_0 : Blocks := edgeBlocks% "full/vectors/01100101110-V-0000.bin"
noncomputable def vp01100101110 : Blocks := vp01100101110_0
private theorem bp011001011100 : Branch 0 (-3255761639/4000000 : ℚ) vp01100101110 := by
  apply branch_left_normalized (c:=vp011001011100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3255761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3255761639/2000000 : ℚ) by norm_num]
  exact coverp011001011100
private noncomputable def ep011001011101_0 : Blocks := edgeBlocks% "full/vectors/011001011101-E-0000.bin"
noncomputable def ep011001011101 : Blocks := ep011001011101_0
private theorem idp011001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100101110.list =
    C ((2:ℤ)^102) * horner X vp011001011101.list + horner X ep011001011101.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001011101 : Branch 1 (-3255761639/4000000 : ℚ) vp01100101110 := by
  apply branch_checked idp011001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3255761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3257761639/2000000 : ℚ) by norm_num]
  exact coverp011001011101
theorem coverp01100101110 : Covers (-3255761639/4000000 : ℚ) vp01100101110 := join_branches bp011001011100 bp011001011101
private noncomputable def vp0110010111_0 : Blocks := edgeBlocks% "full/vectors/0110010111-V-0000.bin"
private noncomputable def vp0110010111_1 : Blocks := edgeBlocks% "full/vectors/0110010111-V-0001.bin"
noncomputable def vp0110010111 : Blocks := (Blocks.join vp0110010111_0 vp0110010111_1)
private theorem bp01100101110 : Branch 0 (-3255761639/8000000 : ℚ) vp0110010111 := by
  apply branch_left_normalized (c:=vp01100101110) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3255761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3255761639/4000000 : ℚ) by norm_num]
  exact coverp01100101110
private noncomputable def ep01100101111_0 : Blocks := edgeBlocks% "full/vectors/01100101111-E-0000.bin"
private noncomputable def ep01100101111_1 : Blocks := edgeBlocks% "full/vectors/01100101111-E-0001.bin"
noncomputable def ep01100101111 : Blocks := (Blocks.join ep01100101111_0 ep01100101111_1)
private theorem idp01100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110010111.list =
    C ((2:ℤ)^183) * horner X vp01100101111.list + horner X ep01100101111.list := by
  exact edge_identity (B := (2:ℤ)^334) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100101111 : Branch 1 (-3255761639/8000000 : ℚ) vp0110010111 := by
  apply branch_checked idp01100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3255761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3259761639/4000000 : ℚ) by norm_num]
  exact coverp01100101111
theorem coverp0110010111 : Covers (-3255761639/8000000 : ℚ) vp0110010111 := join_branches bp01100101110 bp01100101111
private noncomputable def vp011001011011_0 : Blocks := edgeBlocks% "full/vectors/011001011011-V-0000.bin"
noncomputable def vp011001011011 : Blocks := vp011001011011_0
theorem coverp011001011011 : Covers (-3253761639/2000000 : ℚ) vp011001011011 := cover_leaf (by decide +kernel)
private noncomputable def vp011001011010_0 : Blocks := edgeBlocks% "full/vectors/011001011010-V-0000.bin"
noncomputable def vp011001011010 : Blocks := vp011001011010_0
theorem coverp011001011010 : Covers (-3251761639/2000000 : ℚ) vp011001011010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100101101_0 : Blocks := edgeBlocks% "full/vectors/01100101101-V-0000.bin"
noncomputable def vp01100101101 : Blocks := vp01100101101_0
private theorem bp011001011010 : Branch 0 (-3251761639/4000000 : ℚ) vp01100101101 := by
  apply branch_left_normalized (c:=vp011001011010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3251761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3251761639/2000000 : ℚ) by norm_num]
  exact coverp011001011010
private noncomputable def ep011001011011_0 : Blocks := edgeBlocks% "full/vectors/011001011011-E-0000.bin"
noncomputable def ep011001011011 : Blocks := ep011001011011_0
private theorem idp011001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100101101.list =
    C ((2:ℤ)^102) * horner X vp011001011011.list + horner X ep011001011011.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001011011 : Branch 1 (-3251761639/4000000 : ℚ) vp01100101101 := by
  apply branch_checked idp011001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3251761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3253761639/2000000 : ℚ) by norm_num]
  exact coverp011001011011
theorem coverp01100101101 : Covers (-3251761639/4000000 : ℚ) vp01100101101 := join_branches bp011001011010 bp011001011011
private noncomputable def vp011001011001_0 : Blocks := edgeBlocks% "full/vectors/011001011001-V-0000.bin"
noncomputable def vp011001011001 : Blocks := vp011001011001_0
theorem coverp011001011001 : Covers (-3249761639/2000000 : ℚ) vp011001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp011001011000_0 : Blocks := edgeBlocks% "full/vectors/011001011000-V-0000.bin"
noncomputable def vp011001011000 : Blocks := vp011001011000_0
theorem coverp011001011000 : Covers (-3247761639/2000000 : ℚ) vp011001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100101100_0 : Blocks := edgeBlocks% "full/vectors/01100101100-V-0000.bin"
noncomputable def vp01100101100 : Blocks := vp01100101100_0
private theorem bp011001011000 : Branch 0 (-3247761639/4000000 : ℚ) vp01100101100 := by
  apply branch_left_normalized (c:=vp011001011000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3247761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3247761639/2000000 : ℚ) by norm_num]
  exact coverp011001011000
private noncomputable def ep011001011001_0 : Blocks := edgeBlocks% "full/vectors/011001011001-E-0000.bin"
noncomputable def ep011001011001 : Blocks := ep011001011001_0
private theorem idp011001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100101100.list =
    C ((2:ℤ)^103) * horner X vp011001011001.list + horner X ep011001011001.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001011001 : Branch 1 (-3247761639/4000000 : ℚ) vp01100101100 := by
  apply branch_checked idp011001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3247761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3249761639/2000000 : ℚ) by norm_num]
  exact coverp011001011001
theorem coverp01100101100 : Covers (-3247761639/4000000 : ℚ) vp01100101100 := join_branches bp011001011000 bp011001011001
private noncomputable def vp0110010110_0 : Blocks := edgeBlocks% "full/vectors/0110010110-V-0000.bin"
private noncomputable def vp0110010110_1 : Blocks := edgeBlocks% "full/vectors/0110010110-V-0001.bin"
noncomputable def vp0110010110 : Blocks := (Blocks.join vp0110010110_0 vp0110010110_1)
private theorem bp01100101100 : Branch 0 (-3247761639/8000000 : ℚ) vp0110010110 := by
  apply branch_left_normalized (c:=vp01100101100) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3247761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3247761639/4000000 : ℚ) by norm_num]
  exact coverp01100101100
private noncomputable def ep01100101101_0 : Blocks := edgeBlocks% "full/vectors/01100101101-E-0000.bin"
private noncomputable def ep01100101101_1 : Blocks := edgeBlocks% "full/vectors/01100101101-E-0001.bin"
noncomputable def ep01100101101 : Blocks := (Blocks.join ep01100101101_0 ep01100101101_1)
private theorem idp01100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110010110.list =
    C ((2:ℤ)^184) * horner X vp01100101101.list + horner X ep01100101101.list := by
  exact edge_identity (B := (2:ℤ)^336) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100101101 : Branch 1 (-3247761639/8000000 : ℚ) vp0110010110 := by
  apply branch_checked idp01100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-3247761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3251761639/4000000 : ℚ) by norm_num]
  exact coverp01100101101
theorem coverp0110010110 : Covers (-3247761639/8000000 : ℚ) vp0110010110 := join_branches bp01100101100 bp01100101101
private noncomputable def vp011001011_0 : Blocks := edgeBlocks% "full/vectors/011001011-V-0000.bin"
private noncomputable def vp011001011_1 : Blocks := edgeBlocks% "full/vectors/011001011-V-0001.bin"
private noncomputable def vp011001011_2 : Blocks := edgeBlocks% "full/vectors/011001011-V-0002.bin"
noncomputable def vp011001011 : Blocks := (Blocks.join vp011001011_0 (Blocks.join vp011001011_1 vp011001011_2))
private theorem bp0110010110 : Branch 0 (-3247761639/16000000 : ℚ) vp011001011 := by
  apply branch_left_normalized (c:=vp0110010110) (k:=0) (m:=160) (by decide +kernel)
  rw [show 2*(-3247761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3247761639/8000000 : ℚ) by norm_num]
  exact coverp0110010110
private noncomputable def ep0110010111_0 : Blocks := edgeBlocks% "full/vectors/0110010111-E-0000.bin"
private noncomputable def ep0110010111_1 : Blocks := edgeBlocks% "full/vectors/0110010111-E-0001.bin"
private noncomputable def ep0110010111_2 : Blocks := edgeBlocks% "full/vectors/0110010111-E-0002.bin"
noncomputable def ep0110010111 : Blocks := (Blocks.join ep0110010111_0 (Blocks.join ep0110010111_1 ep0110010111_2))
private theorem idp0110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011001011.list =
    C ((2:ℤ)^346) * horner X vp0110010111.list + horner X ep0110010111.list := by
  exact edge_identity (B := (2:ℤ)^547) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110010111 : Branch 1 (-3247761639/16000000 : ℚ) vp011001011 := by
  apply branch_checked idp0110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-3247761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3255761639/8000000 : ℚ) by norm_num]
  exact coverp0110010111
theorem coverp011001011 : Covers (-3247761639/16000000 : ℚ) vp011001011 := join_branches bp0110010110 bp0110010111
private noncomputable def vp011001010111_0 : Blocks := edgeBlocks% "full/vectors/011001010111-V-0000.bin"
noncomputable def vp011001010111 : Blocks := vp011001010111_0
theorem coverp011001010111 : Covers (-3245761639/2000000 : ℚ) vp011001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp011001010110_0 : Blocks := edgeBlocks% "full/vectors/011001010110-V-0000.bin"
noncomputable def vp011001010110 : Blocks := vp011001010110_0
theorem coverp011001010110 : Covers (-3243761639/2000000 : ℚ) vp011001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100101011_0 : Blocks := edgeBlocks% "full/vectors/01100101011-V-0000.bin"
noncomputable def vp01100101011 : Blocks := vp01100101011_0
private theorem bp011001010110 : Branch 0 (-3243761639/4000000 : ℚ) vp01100101011 := by
  apply branch_left_normalized (c:=vp011001010110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3243761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3243761639/2000000 : ℚ) by norm_num]
  exact coverp011001010110
private noncomputable def ep011001010111_0 : Blocks := edgeBlocks% "full/vectors/011001010111-E-0000.bin"
noncomputable def ep011001010111 : Blocks := ep011001010111_0
private theorem idp011001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100101011.list =
    C ((2:ℤ)^103) * horner X vp011001010111.list + horner X ep011001010111.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001010111 : Branch 1 (-3243761639/4000000 : ℚ) vp01100101011 := by
  apply branch_checked idp011001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-3243761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3245761639/2000000 : ℚ) by norm_num]
  exact coverp011001010111
theorem coverp01100101011 : Covers (-3243761639/4000000 : ℚ) vp01100101011 := join_branches bp011001010110 bp011001010111
private noncomputable def vp011001010101_0 : Blocks := edgeBlocks% "full/vectors/011001010101-V-0000.bin"
noncomputable def vp011001010101 : Blocks := vp011001010101_0
theorem coverp011001010101 : Covers (-3241761639/2000000 : ℚ) vp011001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp011001010100_0 : Blocks := edgeBlocks% "full/vectors/011001010100-V-0000.bin"
noncomputable def vp011001010100 : Blocks := vp011001010100_0
theorem coverp011001010100 : Covers (-3239761639/2000000 : ℚ) vp011001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100101010_0 : Blocks := edgeBlocks% "full/vectors/01100101010-V-0000.bin"
noncomputable def vp01100101010 : Blocks := vp01100101010_0
private theorem bp011001010100 : Branch 0 (-3239761639/4000000 : ℚ) vp01100101010 := by
  apply branch_left_normalized (c:=vp011001010100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3239761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3239761639/2000000 : ℚ) by norm_num]
  exact coverp011001010100
private noncomputable def ep011001010101_0 : Blocks := edgeBlocks% "full/vectors/011001010101-E-0000.bin"
noncomputable def ep011001010101 : Blocks := ep011001010101_0
private theorem idp011001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100101010.list =
    C ((2:ℤ)^103) * horner X vp011001010101.list + horner X ep011001010101.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001010101 : Branch 1 (-3239761639/4000000 : ℚ) vp01100101010 := by
  apply branch_checked idp011001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-3239761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3241761639/2000000 : ℚ) by norm_num]
  exact coverp011001010101
theorem coverp01100101010 : Covers (-3239761639/4000000 : ℚ) vp01100101010 := join_branches bp011001010100 bp011001010101
private noncomputable def vp0110010101_0 : Blocks := edgeBlocks% "full/vectors/0110010101-V-0000.bin"
private noncomputable def vp0110010101_1 : Blocks := edgeBlocks% "full/vectors/0110010101-V-0001.bin"
noncomputable def vp0110010101 : Blocks := (Blocks.join vp0110010101_0 vp0110010101_1)
private theorem bp01100101010 : Branch 0 (-3239761639/8000000 : ℚ) vp0110010101 := by
  apply branch_left_normalized (c:=vp01100101010) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3239761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3239761639/4000000 : ℚ) by norm_num]
  exact coverp01100101010
private noncomputable def ep01100101011_0 : Blocks := edgeBlocks% "full/vectors/01100101011-E-0000.bin"
private noncomputable def ep01100101011_1 : Blocks := edgeBlocks% "full/vectors/01100101011-E-0001.bin"
noncomputable def ep01100101011 : Blocks := (Blocks.join ep01100101011_0 ep01100101011_1)
private theorem idp01100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110010101.list =
    C ((2:ℤ)^183) * horner X vp01100101011.list + horner X ep01100101011.list := by
  exact edge_identity (B := (2:ℤ)^335) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100101011 : Branch 1 (-3239761639/8000000 : ℚ) vp0110010101 := by
  apply branch_checked idp01100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-3239761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3243761639/4000000 : ℚ) by norm_num]
  exact coverp01100101011
theorem coverp0110010101 : Covers (-3239761639/8000000 : ℚ) vp0110010101 := join_branches bp01100101010 bp01100101011
private noncomputable def vp011001010011_0 : Blocks := edgeBlocks% "full/vectors/011001010011-V-0000.bin"
noncomputable def vp011001010011 : Blocks := vp011001010011_0
theorem coverp011001010011 : Covers (-3237761639/2000000 : ℚ) vp011001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp011001010010_0 : Blocks := edgeBlocks% "full/vectors/011001010010-V-0000.bin"
noncomputable def vp011001010010 : Blocks := vp011001010010_0
theorem coverp011001010010 : Covers (-3235761639/2000000 : ℚ) vp011001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100101001_0 : Blocks := edgeBlocks% "full/vectors/01100101001-V-0000.bin"
noncomputable def vp01100101001 : Blocks := vp01100101001_0
private theorem bp011001010010 : Branch 0 (-3235761639/4000000 : ℚ) vp01100101001 := by
  apply branch_left_normalized (c:=vp011001010010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3235761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3235761639/2000000 : ℚ) by norm_num]
  exact coverp011001010010
private noncomputable def ep011001010011_0 : Blocks := edgeBlocks% "full/vectors/011001010011-E-0000.bin"
noncomputable def ep011001010011 : Blocks := ep011001010011_0
private theorem idp011001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100101001.list =
    C ((2:ℤ)^103) * horner X vp011001010011.list + horner X ep011001010011.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001010011 : Branch 1 (-3235761639/4000000 : ℚ) vp01100101001 := by
  apply branch_checked idp011001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-3235761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3237761639/2000000 : ℚ) by norm_num]
  exact coverp011001010011
theorem coverp01100101001 : Covers (-3235761639/4000000 : ℚ) vp01100101001 := join_branches bp011001010010 bp011001010011
private noncomputable def vp011001010001_0 : Blocks := edgeBlocks% "full/vectors/011001010001-V-0000.bin"
noncomputable def vp011001010001 : Blocks := vp011001010001_0
theorem coverp011001010001 : Covers (-3233761639/2000000 : ℚ) vp011001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp011001010000_0 : Blocks := edgeBlocks% "full/vectors/011001010000-V-0000.bin"
noncomputable def vp011001010000 : Blocks := vp011001010000_0
theorem coverp011001010000 : Covers (-3231761639/2000000 : ℚ) vp011001010000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100101000_0 : Blocks := edgeBlocks% "full/vectors/01100101000-V-0000.bin"
noncomputable def vp01100101000 : Blocks := vp01100101000_0
private theorem bp011001010000 : Branch 0 (-3231761639/4000000 : ℚ) vp01100101000 := by
  apply branch_left_normalized (c:=vp011001010000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3231761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3231761639/2000000 : ℚ) by norm_num]
  exact coverp011001010000
private noncomputable def ep011001010001_0 : Blocks := edgeBlocks% "full/vectors/011001010001-E-0000.bin"
noncomputable def ep011001010001 : Blocks := ep011001010001_0
private theorem idp011001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100101000.list =
    C ((2:ℤ)^103) * horner X vp011001010001.list + horner X ep011001010001.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001010001 : Branch 1 (-3231761639/4000000 : ℚ) vp01100101000 := by
  apply branch_checked idp011001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3231761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3233761639/2000000 : ℚ) by norm_num]
  exact coverp011001010001
theorem coverp01100101000 : Covers (-3231761639/4000000 : ℚ) vp01100101000 := join_branches bp011001010000 bp011001010001
private noncomputable def vp0110010100_0 : Blocks := edgeBlocks% "full/vectors/0110010100-V-0000.bin"
private noncomputable def vp0110010100_1 : Blocks := edgeBlocks% "full/vectors/0110010100-V-0001.bin"
noncomputable def vp0110010100 : Blocks := (Blocks.join vp0110010100_0 vp0110010100_1)
private theorem bp01100101000 : Branch 0 (-3231761639/8000000 : ℚ) vp0110010100 := by
  apply branch_left_normalized (c:=vp01100101000) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3231761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3231761639/4000000 : ℚ) by norm_num]
  exact coverp01100101000
private noncomputable def ep01100101001_0 : Blocks := edgeBlocks% "full/vectors/01100101001-E-0000.bin"
private noncomputable def ep01100101001_1 : Blocks := edgeBlocks% "full/vectors/01100101001-E-0001.bin"
noncomputable def ep01100101001 : Blocks := (Blocks.join ep01100101001_0 ep01100101001_1)
private theorem idp01100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110010100.list =
    C ((2:ℤ)^184) * horner X vp01100101001.list + horner X ep01100101001.list := by
  exact edge_identity (B := (2:ℤ)^336) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100101001 : Branch 1 (-3231761639/8000000 : ℚ) vp0110010100 := by
  apply branch_checked idp01100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-3231761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3235761639/4000000 : ℚ) by norm_num]
  exact coverp01100101001
theorem coverp0110010100 : Covers (-3231761639/8000000 : ℚ) vp0110010100 := join_branches bp01100101000 bp01100101001
private noncomputable def vp011001010_0 : Blocks := edgeBlocks% "full/vectors/011001010-V-0000.bin"
private noncomputable def vp011001010_1 : Blocks := edgeBlocks% "full/vectors/011001010-V-0001.bin"
private noncomputable def vp011001010_2 : Blocks := edgeBlocks% "full/vectors/011001010-V-0002.bin"
noncomputable def vp011001010 : Blocks := (Blocks.join vp011001010_0 (Blocks.join vp011001010_1 vp011001010_2))
private theorem bp0110010100 : Branch 0 (-3231761639/16000000 : ℚ) vp011001010 := by
  apply branch_left_normalized (c:=vp0110010100) (k:=0) (m:=160) (by decide +kernel)
  rw [show 2*(-3231761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3231761639/8000000 : ℚ) by norm_num]
  exact coverp0110010100
private noncomputable def ep0110010101_0 : Blocks := edgeBlocks% "full/vectors/0110010101-E-0000.bin"
private noncomputable def ep0110010101_1 : Blocks := edgeBlocks% "full/vectors/0110010101-E-0001.bin"
private noncomputable def ep0110010101_2 : Blocks := edgeBlocks% "full/vectors/0110010101-E-0002.bin"
noncomputable def ep0110010101 : Blocks := (Blocks.join ep0110010101_0 (Blocks.join ep0110010101_1 ep0110010101_2))
private theorem idp0110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011001010.list =
    C ((2:ℤ)^345) * horner X vp0110010101.list + horner X ep0110010101.list := by
  exact edge_identity (B := (2:ℤ)^547) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110010101 : Branch 1 (-3231761639/16000000 : ℚ) vp011001010 := by
  apply branch_checked idp0110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-3231761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3239761639/8000000 : ℚ) by norm_num]
  exact coverp0110010101
theorem coverp011001010 : Covers (-3231761639/16000000 : ℚ) vp011001010 := join_branches bp0110010100 bp0110010101
private noncomputable def vp01100101_0 : Blocks := edgeBlocks% "full/vectors/01100101-V-0000.bin"
private noncomputable def vp01100101_1 : Blocks := edgeBlocks% "full/vectors/01100101-V-0001.bin"
private noncomputable def vp01100101_2 : Blocks := edgeBlocks% "full/vectors/01100101-V-0002.bin"
private noncomputable def vp01100101_3 : Blocks := edgeBlocks% "full/vectors/01100101-V-0003.bin"
private noncomputable def vp01100101_4 : Blocks := edgeBlocks% "full/vectors/01100101-V-0004.bin"
noncomputable def vp01100101 : Blocks := (Blocks.join (Blocks.join vp01100101_0 vp01100101_1) (Blocks.join vp01100101_2 (Blocks.join vp01100101_3 vp01100101_4)))
private theorem bp011001010 : Branch 0 (-3231761639/32000000 : ℚ) vp01100101 := by
  apply branch_left_normalized (c:=vp011001010) (k:=0) (m:=298) (by decide +kernel)
  rw [show 2*(-3231761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3231761639/16000000 : ℚ) by norm_num]
  exact coverp011001010
private noncomputable def ep011001011_0 : Blocks := edgeBlocks% "full/vectors/011001011-E-0000.bin"
private noncomputable def ep011001011_1 : Blocks := edgeBlocks% "full/vectors/011001011-E-0001.bin"
private noncomputable def ep011001011_2 : Blocks := edgeBlocks% "full/vectors/011001011-E-0002.bin"
private noncomputable def ep011001011_3 : Blocks := edgeBlocks% "full/vectors/011001011-E-0003.bin"
private noncomputable def ep011001011_4 : Blocks := edgeBlocks% "full/vectors/011001011-E-0004.bin"
noncomputable def ep011001011 : Blocks := (Blocks.join (Blocks.join ep011001011_0 ep011001011_1) (Blocks.join ep011001011_2 (Blocks.join ep011001011_3 ep011001011_4)))
private theorem idp011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100101.list =
    C ((2:ℤ)^665) * horner X vp011001011.list + horner X ep011001011.list := by
  exact edge_identity (B := (2:ℤ)^967) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001011 : Branch 1 (-3231761639/32000000 : ℚ) vp01100101 := by
  apply branch_checked idp011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3231761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3247761639/16000000 : ℚ) by norm_num]
  exact coverp011001011
theorem coverp01100101 : Covers (-3231761639/32000000 : ℚ) vp01100101 := join_branches bp011001010 bp011001011
private noncomputable def vp011001001111_0 : Blocks := edgeBlocks% "full/vectors/011001001111-V-0000.bin"
noncomputable def vp011001001111 : Blocks := vp011001001111_0
theorem coverp011001001111 : Covers (-3229761639/2000000 : ℚ) vp011001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp011001001110_0 : Blocks := edgeBlocks% "full/vectors/011001001110-V-0000.bin"
noncomputable def vp011001001110 : Blocks := vp011001001110_0
theorem coverp011001001110 : Covers (-3227761639/2000000 : ℚ) vp011001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100100111_0 : Blocks := edgeBlocks% "full/vectors/01100100111-V-0000.bin"
noncomputable def vp01100100111 : Blocks := vp01100100111_0
private theorem bp011001001110 : Branch 0 (-3227761639/4000000 : ℚ) vp01100100111 := by
  apply branch_left_normalized (c:=vp011001001110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3227761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3227761639/2000000 : ℚ) by norm_num]
  exact coverp011001001110
private noncomputable def ep011001001111_0 : Blocks := edgeBlocks% "full/vectors/011001001111-E-0000.bin"
noncomputable def ep011001001111 : Blocks := ep011001001111_0
private theorem idp011001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100100111.list =
    C ((2:ℤ)^102) * horner X vp011001001111.list + horner X ep011001001111.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001001111 : Branch 1 (-3227761639/4000000 : ℚ) vp01100100111 := by
  apply branch_checked idp011001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3227761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3229761639/2000000 : ℚ) by norm_num]
  exact coverp011001001111
theorem coverp01100100111 : Covers (-3227761639/4000000 : ℚ) vp01100100111 := join_branches bp011001001110 bp011001001111
private noncomputable def vp011001001101_0 : Blocks := edgeBlocks% "full/vectors/011001001101-V-0000.bin"
noncomputable def vp011001001101 : Blocks := vp011001001101_0
theorem coverp011001001101 : Covers (-3225761639/2000000 : ℚ) vp011001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp011001001100_0 : Blocks := edgeBlocks% "full/vectors/011001001100-V-0000.bin"
noncomputable def vp011001001100 : Blocks := vp011001001100_0
theorem coverp011001001100 : Covers (-3223761639/2000000 : ℚ) vp011001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100100110_0 : Blocks := edgeBlocks% "full/vectors/01100100110-V-0000.bin"
noncomputable def vp01100100110 : Blocks := vp01100100110_0
private theorem bp011001001100 : Branch 0 (-3223761639/4000000 : ℚ) vp01100100110 := by
  apply branch_left_normalized (c:=vp011001001100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3223761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3223761639/2000000 : ℚ) by norm_num]
  exact coverp011001001100
private noncomputable def ep011001001101_0 : Blocks := edgeBlocks% "full/vectors/011001001101-E-0000.bin"
noncomputable def ep011001001101 : Blocks := ep011001001101_0
private theorem idp011001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100100110.list =
    C ((2:ℤ)^102) * horner X vp011001001101.list + horner X ep011001001101.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001001101 : Branch 1 (-3223761639/4000000 : ℚ) vp01100100110 := by
  apply branch_checked idp011001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3223761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3225761639/2000000 : ℚ) by norm_num]
  exact coverp011001001101
theorem coverp01100100110 : Covers (-3223761639/4000000 : ℚ) vp01100100110 := join_branches bp011001001100 bp011001001101
private noncomputable def vp0110010011_0 : Blocks := edgeBlocks% "full/vectors/0110010011-V-0000.bin"
private noncomputable def vp0110010011_1 : Blocks := edgeBlocks% "full/vectors/0110010011-V-0001.bin"
noncomputable def vp0110010011 : Blocks := (Blocks.join vp0110010011_0 vp0110010011_1)
private theorem bp01100100110 : Branch 0 (-3223761639/8000000 : ℚ) vp0110010011 := by
  apply branch_left_normalized (c:=vp01100100110) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-3223761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3223761639/4000000 : ℚ) by norm_num]
  exact coverp01100100110
private noncomputable def ep01100100111_0 : Blocks := edgeBlocks% "full/vectors/01100100111-E-0000.bin"
private noncomputable def ep01100100111_1 : Blocks := edgeBlocks% "full/vectors/01100100111-E-0001.bin"
noncomputable def ep01100100111 : Blocks := (Blocks.join ep01100100111_0 ep01100100111_1)
private theorem idp01100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110010011.list =
    C ((2:ℤ)^184) * horner X vp01100100111.list + horner X ep01100100111.list := by
  exact edge_identity (B := (2:ℤ)^336) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100100111 : Branch 1 (-3223761639/8000000 : ℚ) vp0110010011 := by
  apply branch_checked idp01100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3223761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3227761639/4000000 : ℚ) by norm_num]
  exact coverp01100100111
theorem coverp0110010011 : Covers (-3223761639/8000000 : ℚ) vp0110010011 := join_branches bp01100100110 bp01100100111
private noncomputable def vp011001001011_0 : Blocks := edgeBlocks% "full/vectors/011001001011-V-0000.bin"
noncomputable def vp011001001011 : Blocks := vp011001001011_0
theorem coverp011001001011 : Covers (-3221761639/2000000 : ℚ) vp011001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp011001001010_0 : Blocks := edgeBlocks% "full/vectors/011001001010-V-0000.bin"
noncomputable def vp011001001010 : Blocks := vp011001001010_0
theorem coverp011001001010 : Covers (-3219761639/2000000 : ℚ) vp011001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100100101_0 : Blocks := edgeBlocks% "full/vectors/01100100101-V-0000.bin"
noncomputable def vp01100100101 : Blocks := vp01100100101_0
private theorem bp011001001010 : Branch 0 (-3219761639/4000000 : ℚ) vp01100100101 := by
  apply branch_left_normalized (c:=vp011001001010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3219761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3219761639/2000000 : ℚ) by norm_num]
  exact coverp011001001010
private noncomputable def ep011001001011_0 : Blocks := edgeBlocks% "full/vectors/011001001011-E-0000.bin"
noncomputable def ep011001001011 : Blocks := ep011001001011_0
private theorem idp011001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100100101.list =
    C ((2:ℤ)^103) * horner X vp011001001011.list + horner X ep011001001011.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001001011 : Branch 1 (-3219761639/4000000 : ℚ) vp01100100101 := by
  apply branch_checked idp011001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3219761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3221761639/2000000 : ℚ) by norm_num]
  exact coverp011001001011
theorem coverp01100100101 : Covers (-3219761639/4000000 : ℚ) vp01100100101 := join_branches bp011001001010 bp011001001011
private noncomputable def vp011001001001_0 : Blocks := edgeBlocks% "full/vectors/011001001001-V-0000.bin"
noncomputable def vp011001001001 : Blocks := vp011001001001_0
theorem coverp011001001001 : Covers (-3217761639/2000000 : ℚ) vp011001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp011001001000_0 : Blocks := edgeBlocks% "full/vectors/011001001000-V-0000.bin"
noncomputable def vp011001001000 : Blocks := vp011001001000_0
theorem coverp011001001000 : Covers (-3215761639/2000000 : ℚ) vp011001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100100100_0 : Blocks := edgeBlocks% "full/vectors/01100100100-V-0000.bin"
noncomputable def vp01100100100 : Blocks := vp01100100100_0
private theorem bp011001001000 : Branch 0 (-3215761639/4000000 : ℚ) vp01100100100 := by
  apply branch_left_normalized (c:=vp011001001000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3215761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3215761639/2000000 : ℚ) by norm_num]
  exact coverp011001001000
private noncomputable def ep011001001001_0 : Blocks := edgeBlocks% "full/vectors/011001001001-E-0000.bin"
noncomputable def ep011001001001 : Blocks := ep011001001001_0
private theorem idp011001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100100100.list =
    C ((2:ℤ)^102) * horner X vp011001001001.list + horner X ep011001001001.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001001001 : Branch 1 (-3215761639/4000000 : ℚ) vp01100100100 := by
  apply branch_checked idp011001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3215761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3217761639/2000000 : ℚ) by norm_num]
  exact coverp011001001001
theorem coverp01100100100 : Covers (-3215761639/4000000 : ℚ) vp01100100100 := join_branches bp011001001000 bp011001001001
private noncomputable def vp0110010010_0 : Blocks := edgeBlocks% "full/vectors/0110010010-V-0000.bin"
private noncomputable def vp0110010010_1 : Blocks := edgeBlocks% "full/vectors/0110010010-V-0001.bin"
noncomputable def vp0110010010 : Blocks := (Blocks.join vp0110010010_0 vp0110010010_1)
private theorem bp01100100100 : Branch 0 (-3215761639/8000000 : ℚ) vp0110010010 := by
  apply branch_left_normalized (c:=vp01100100100) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3215761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3215761639/4000000 : ℚ) by norm_num]
  exact coverp01100100100
private noncomputable def ep01100100101_0 : Blocks := edgeBlocks% "full/vectors/01100100101-E-0000.bin"
private noncomputable def ep01100100101_1 : Blocks := edgeBlocks% "full/vectors/01100100101-E-0001.bin"
noncomputable def ep01100100101 : Blocks := (Blocks.join ep01100100101_0 ep01100100101_1)
private theorem idp01100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110010010.list =
    C ((2:ℤ)^185) * horner X vp01100100101.list + horner X ep01100100101.list := by
  exact edge_identity (B := (2:ℤ)^336) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100100101 : Branch 1 (-3215761639/8000000 : ℚ) vp0110010010 := by
  apply branch_checked idp01100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3215761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3219761639/4000000 : ℚ) by norm_num]
  exact coverp01100100101
theorem coverp0110010010 : Covers (-3215761639/8000000 : ℚ) vp0110010010 := join_branches bp01100100100 bp01100100101
private noncomputable def vp011001001_0 : Blocks := edgeBlocks% "full/vectors/011001001-V-0000.bin"
private noncomputable def vp011001001_1 : Blocks := edgeBlocks% "full/vectors/011001001-V-0001.bin"
private noncomputable def vp011001001_2 : Blocks := edgeBlocks% "full/vectors/011001001-V-0002.bin"
noncomputable def vp011001001 : Blocks := (Blocks.join vp011001001_0 (Blocks.join vp011001001_1 vp011001001_2))
private theorem bp0110010010 : Branch 0 (-3215761639/16000000 : ℚ) vp011001001 := by
  apply branch_left_normalized (c:=vp0110010010) (k:=0) (m:=161) (by decide +kernel)
  rw [show 2*(-3215761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3215761639/8000000 : ℚ) by norm_num]
  exact coverp0110010010
private noncomputable def ep0110010011_0 : Blocks := edgeBlocks% "full/vectors/0110010011-E-0000.bin"
private noncomputable def ep0110010011_1 : Blocks := edgeBlocks% "full/vectors/0110010011-E-0001.bin"
private noncomputable def ep0110010011_2 : Blocks := edgeBlocks% "full/vectors/0110010011-E-0002.bin"
noncomputable def ep0110010011 : Blocks := (Blocks.join ep0110010011_0 (Blocks.join ep0110010011_1 ep0110010011_2))
private theorem idp0110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011001001.list =
    C ((2:ℤ)^346) * horner X vp0110010011.list + horner X ep0110010011.list := by
  exact edge_identity (B := (2:ℤ)^548) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110010011 : Branch 1 (-3215761639/16000000 : ℚ) vp011001001 := by
  apply branch_checked idp0110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-3215761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3223761639/8000000 : ℚ) by norm_num]
  exact coverp0110010011
theorem coverp011001001 : Covers (-3215761639/16000000 : ℚ) vp011001001 := join_branches bp0110010010 bp0110010011
private noncomputable def vp011001000111_0 : Blocks := edgeBlocks% "full/vectors/011001000111-V-0000.bin"
noncomputable def vp011001000111 : Blocks := vp011001000111_0
theorem coverp011001000111 : Covers (-3213761639/2000000 : ℚ) vp011001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp011001000110_0 : Blocks := edgeBlocks% "full/vectors/011001000110-V-0000.bin"
noncomputable def vp011001000110 : Blocks := vp011001000110_0
theorem coverp011001000110 : Covers (-3211761639/2000000 : ℚ) vp011001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp01100100011_0 : Blocks := edgeBlocks% "full/vectors/01100100011-V-0000.bin"
noncomputable def vp01100100011 : Blocks := vp01100100011_0
private theorem bp011001000110 : Branch 0 (-3211761639/4000000 : ℚ) vp01100100011 := by
  apply branch_left_normalized (c:=vp011001000110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3211761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3211761639/2000000 : ℚ) by norm_num]
  exact coverp011001000110
private noncomputable def ep011001000111_0 : Blocks := edgeBlocks% "full/vectors/011001000111-E-0000.bin"
noncomputable def ep011001000111 : Blocks := ep011001000111_0
private theorem idp011001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100100011.list =
    C ((2:ℤ)^101) * horner X vp011001000111.list + horner X ep011001000111.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001000111 : Branch 1 (-3211761639/4000000 : ℚ) vp01100100011 := by
  apply branch_checked idp011001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3211761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3213761639/2000000 : ℚ) by norm_num]
  exact coverp011001000111
theorem coverp01100100011 : Covers (-3211761639/4000000 : ℚ) vp01100100011 := join_branches bp011001000110 bp011001000111
private noncomputable def vp011001000101_0 : Blocks := edgeBlocks% "full/vectors/011001000101-V-0000.bin"
noncomputable def vp011001000101 : Blocks := vp011001000101_0
theorem coverp011001000101 : Covers (-3209761639/2000000 : ℚ) vp011001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp011001000100_0 : Blocks := edgeBlocks% "full/vectors/011001000100-V-0000.bin"
noncomputable def vp011001000100 : Blocks := vp011001000100_0
theorem coverp011001000100 : Covers (-3207761639/2000000 : ℚ) vp011001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp01100100010_0 : Blocks := edgeBlocks% "full/vectors/01100100010-V-0000.bin"
noncomputable def vp01100100010 : Blocks := vp01100100010_0
private theorem bp011001000100 : Branch 0 (-3207761639/4000000 : ℚ) vp01100100010 := by
  apply branch_left_normalized (c:=vp011001000100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3207761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3207761639/2000000 : ℚ) by norm_num]
  exact coverp011001000100
private noncomputable def ep011001000101_0 : Blocks := edgeBlocks% "full/vectors/011001000101-E-0000.bin"
noncomputable def ep011001000101 : Blocks := ep011001000101_0
private theorem idp011001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100100010.list =
    C ((2:ℤ)^102) * horner X vp011001000101.list + horner X ep011001000101.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001000101 : Branch 1 (-3207761639/4000000 : ℚ) vp01100100010 := by
  apply branch_checked idp011001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3207761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3209761639/2000000 : ℚ) by norm_num]
  exact coverp011001000101
theorem coverp01100100010 : Covers (-3207761639/4000000 : ℚ) vp01100100010 := join_branches bp011001000100 bp011001000101
private noncomputable def vp0110010001_0 : Blocks := edgeBlocks% "full/vectors/0110010001-V-0000.bin"
private noncomputable def vp0110010001_1 : Blocks := edgeBlocks% "full/vectors/0110010001-V-0001.bin"
noncomputable def vp0110010001 : Blocks := (Blocks.join vp0110010001_0 vp0110010001_1)
private theorem bp01100100010 : Branch 0 (-3207761639/8000000 : ℚ) vp0110010001 := by
  apply branch_left_normalized (c:=vp01100100010) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-3207761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3207761639/4000000 : ℚ) by norm_num]
  exact coverp01100100010
private noncomputable def ep01100100011_0 : Blocks := edgeBlocks% "full/vectors/01100100011-E-0000.bin"
private noncomputable def ep01100100011_1 : Blocks := edgeBlocks% "full/vectors/01100100011-E-0001.bin"
noncomputable def ep01100100011 : Blocks := (Blocks.join ep01100100011_0 ep01100100011_1)
private theorem idp01100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110010001.list =
    C ((2:ℤ)^183) * horner X vp01100100011.list + horner X ep01100100011.list := by
  exact edge_identity (B := (2:ℤ)^334) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100100011 : Branch 1 (-3207761639/8000000 : ℚ) vp0110010001 := by
  apply branch_checked idp01100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-3207761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3211761639/4000000 : ℚ) by norm_num]
  exact coverp01100100011
theorem coverp0110010001 : Covers (-3207761639/8000000 : ℚ) vp0110010001 := join_branches bp01100100010 bp01100100011
private noncomputable def vp011001000011_0 : Blocks := edgeBlocks% "full/vectors/011001000011-V-0000.bin"
noncomputable def vp011001000011 : Blocks := vp011001000011_0
theorem coverp011001000011 : Covers (-3205761639/2000000 : ℚ) vp011001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp011001000010_0 : Blocks := edgeBlocks% "full/vectors/011001000010-V-0000.bin"
noncomputable def vp011001000010 : Blocks := vp011001000010_0
theorem coverp011001000010 : Covers (-3203761639/2000000 : ℚ) vp011001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp01100100001_0 : Blocks := edgeBlocks% "full/vectors/01100100001-V-0000.bin"
noncomputable def vp01100100001 : Blocks := vp01100100001_0
private theorem bp011001000010 : Branch 0 (-3203761639/4000000 : ℚ) vp01100100001 := by
  apply branch_left_normalized (c:=vp011001000010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3203761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3203761639/2000000 : ℚ) by norm_num]
  exact coverp011001000010
private noncomputable def ep011001000011_0 : Blocks := edgeBlocks% "full/vectors/011001000011-E-0000.bin"
noncomputable def ep011001000011 : Blocks := ep011001000011_0
private theorem idp011001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100100001.list =
    C ((2:ℤ)^103) * horner X vp011001000011.list + horner X ep011001000011.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001000011 : Branch 1 (-3203761639/4000000 : ℚ) vp01100100001 := by
  apply branch_checked idp011001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3203761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3205761639/2000000 : ℚ) by norm_num]
  exact coverp011001000011
theorem coverp01100100001 : Covers (-3203761639/4000000 : ℚ) vp01100100001 := join_branches bp011001000010 bp011001000011
private noncomputable def vp011001000001_0 : Blocks := edgeBlocks% "full/vectors/011001000001-V-0000.bin"
noncomputable def vp011001000001 : Blocks := vp011001000001_0
theorem coverp011001000001 : Covers (-3201761639/2000000 : ℚ) vp011001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp011001000000_0 : Blocks := edgeBlocks% "full/vectors/011001000000-V-0000.bin"
noncomputable def vp011001000000 : Blocks := vp011001000000_0
theorem coverp011001000000 : Covers (-3199761639/2000000 : ℚ) vp011001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp01100100000_0 : Blocks := edgeBlocks% "full/vectors/01100100000-V-0000.bin"
noncomputable def vp01100100000 : Blocks := vp01100100000_0
private theorem bp011001000000 : Branch 0 (-3199761639/4000000 : ℚ) vp01100100000 := by
  apply branch_left_normalized (c:=vp011001000000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-3199761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3199761639/2000000 : ℚ) by norm_num]
  exact coverp011001000000
private noncomputable def ep011001000001_0 : Blocks := edgeBlocks% "full/vectors/011001000001-E-0000.bin"
noncomputable def ep011001000001 : Blocks := ep011001000001_0
private theorem idp011001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100100000.list =
    C ((2:ℤ)^101) * horner X vp011001000001.list + horner X ep011001000001.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001000001 : Branch 1 (-3199761639/4000000 : ℚ) vp01100100000 := by
  apply branch_checked idp011001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3199761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3201761639/2000000 : ℚ) by norm_num]
  exact coverp011001000001
theorem coverp01100100000 : Covers (-3199761639/4000000 : ℚ) vp01100100000 := join_branches bp011001000000 bp011001000001
private noncomputable def vp0110010000_0 : Blocks := edgeBlocks% "full/vectors/0110010000-V-0000.bin"
private noncomputable def vp0110010000_1 : Blocks := edgeBlocks% "full/vectors/0110010000-V-0001.bin"
noncomputable def vp0110010000 : Blocks := (Blocks.join vp0110010000_0 vp0110010000_1)
private theorem bp01100100000 : Branch 0 (-3199761639/8000000 : ℚ) vp0110010000 := by
  apply branch_left_normalized (c:=vp01100100000) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-3199761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3199761639/4000000 : ℚ) by norm_num]
  exact coverp01100100000
private noncomputable def ep01100100001_0 : Blocks := edgeBlocks% "full/vectors/01100100001-E-0000.bin"
private noncomputable def ep01100100001_1 : Blocks := edgeBlocks% "full/vectors/01100100001-E-0001.bin"
noncomputable def ep01100100001 : Blocks := (Blocks.join ep01100100001_0 ep01100100001_1)
private theorem idp01100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110010000.list =
    C ((2:ℤ)^185) * horner X vp01100100001.list + horner X ep01100100001.list := by
  exact edge_identity (B := (2:ℤ)^336) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100100001 : Branch 1 (-3199761639/8000000 : ℚ) vp0110010000 := by
  apply branch_checked idp01100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3199761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3203761639/4000000 : ℚ) by norm_num]
  exact coverp01100100001
theorem coverp0110010000 : Covers (-3199761639/8000000 : ℚ) vp0110010000 := join_branches bp01100100000 bp01100100001
private noncomputable def vp011001000_0 : Blocks := edgeBlocks% "full/vectors/011001000-V-0000.bin"
private noncomputable def vp011001000_1 : Blocks := edgeBlocks% "full/vectors/011001000-V-0001.bin"
private noncomputable def vp011001000_2 : Blocks := edgeBlocks% "full/vectors/011001000-V-0002.bin"
noncomputable def vp011001000 : Blocks := (Blocks.join vp011001000_0 (Blocks.join vp011001000_1 vp011001000_2))
private theorem bp0110010000 : Branch 0 (-3199761639/16000000 : ℚ) vp011001000 := by
  apply branch_left_normalized (c:=vp0110010000) (k:=0) (m:=161) (by decide +kernel)
  rw [show 2*(-3199761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3199761639/8000000 : ℚ) by norm_num]
  exact coverp0110010000
private noncomputable def ep0110010001_0 : Blocks := edgeBlocks% "full/vectors/0110010001-E-0000.bin"
private noncomputable def ep0110010001_1 : Blocks := edgeBlocks% "full/vectors/0110010001-E-0001.bin"
private noncomputable def ep0110010001_2 : Blocks := edgeBlocks% "full/vectors/0110010001-E-0002.bin"
noncomputable def ep0110010001 : Blocks := (Blocks.join ep0110010001_0 (Blocks.join ep0110010001_1 ep0110010001_2))
private theorem idp0110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011001000.list =
    C ((2:ℤ)^347) * horner X vp0110010001.list + horner X ep0110010001.list := by
  exact edge_identity (B := (2:ℤ)^548) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110010001 : Branch 1 (-3199761639/16000000 : ℚ) vp011001000 := by
  apply branch_checked idp0110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3199761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3207761639/8000000 : ℚ) by norm_num]
  exact coverp0110010001
theorem coverp011001000 : Covers (-3199761639/16000000 : ℚ) vp011001000 := join_branches bp0110010000 bp0110010001
private noncomputable def vp01100100_0 : Blocks := edgeBlocks% "full/vectors/01100100-V-0000.bin"
private noncomputable def vp01100100_1 : Blocks := edgeBlocks% "full/vectors/01100100-V-0001.bin"
private noncomputable def vp01100100_2 : Blocks := edgeBlocks% "full/vectors/01100100-V-0002.bin"
private noncomputable def vp01100100_3 : Blocks := edgeBlocks% "full/vectors/01100100-V-0003.bin"
private noncomputable def vp01100100_4 : Blocks := edgeBlocks% "full/vectors/01100100-V-0004.bin"
noncomputable def vp01100100 : Blocks := (Blocks.join (Blocks.join vp01100100_0 vp01100100_1) (Blocks.join vp01100100_2 (Blocks.join vp01100100_3 vp01100100_4)))
private theorem bp011001000 : Branch 0 (-3199761639/32000000 : ℚ) vp01100100 := by
  apply branch_left_normalized (c:=vp011001000) (k:=0) (m:=299) (by decide +kernel)
  rw [show 2*(-3199761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3199761639/16000000 : ℚ) by norm_num]
  exact coverp011001000
private noncomputable def ep011001001_0 : Blocks := edgeBlocks% "full/vectors/011001001-E-0000.bin"
private noncomputable def ep011001001_1 : Blocks := edgeBlocks% "full/vectors/011001001-E-0001.bin"
private noncomputable def ep011001001_2 : Blocks := edgeBlocks% "full/vectors/011001001-E-0002.bin"
private noncomputable def ep011001001_3 : Blocks := edgeBlocks% "full/vectors/011001001-E-0003.bin"
private noncomputable def ep011001001_4 : Blocks := edgeBlocks% "full/vectors/011001001-E-0004.bin"
noncomputable def ep011001001 : Blocks := (Blocks.join (Blocks.join ep011001001_0 ep011001001_1) (Blocks.join ep011001001_2 (Blocks.join ep011001001_3 ep011001001_4)))
private theorem idp011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01100100.list =
    C ((2:ℤ)^667) * horner X vp011001001.list + horner X ep011001001.list := by
  exact edge_identity (B := (2:ℤ)^970) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011001001 : Branch 1 (-3199761639/32000000 : ℚ) vp01100100 := by
  apply branch_checked idp011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3199761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3215761639/16000000 : ℚ) by norm_num]
  exact coverp011001001
theorem coverp01100100 : Covers (-3199761639/32000000 : ℚ) vp01100100 := join_branches bp011001000 bp011001001
private noncomputable def vp0110010_0 : Blocks := edgeBlocks% "full/vectors/0110010-V-0000.bin"
private noncomputable def vp0110010_1 : Blocks := edgeBlocks% "full/vectors/0110010-V-0001.bin"
private noncomputable def vp0110010_2 : Blocks := edgeBlocks% "full/vectors/0110010-V-0002.bin"
private noncomputable def vp0110010_3 : Blocks := edgeBlocks% "full/vectors/0110010-V-0003.bin"
private noncomputable def vp0110010_4 : Blocks := edgeBlocks% "full/vectors/0110010-V-0004.bin"
private noncomputable def vp0110010_5 : Blocks := edgeBlocks% "full/vectors/0110010-V-0005.bin"
private noncomputable def vp0110010_6 : Blocks := edgeBlocks% "full/vectors/0110010-V-0006.bin"
private noncomputable def vp0110010_7 : Blocks := edgeBlocks% "full/vectors/0110010-V-0007.bin"
private noncomputable def vp0110010_8 : Blocks := edgeBlocks% "full/vectors/0110010-V-0008.bin"
noncomputable def vp0110010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0110010_0 vp0110010_1) (Blocks.join vp0110010_2 vp0110010_3)) (Blocks.join (Blocks.join vp0110010_4 vp0110010_5) (Blocks.join vp0110010_6 (Blocks.join vp0110010_7 vp0110010_8))))
private theorem bp01100100 : Branch 0 (-3199761639/64000000 : ℚ) vp0110010 := by
  apply branch_left_normalized (c:=vp01100100) (k:=0) (m:=574) (by decide +kernel)
  rw [show 2*(-3199761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3199761639/32000000 : ℚ) by norm_num]
  exact coverp01100100
private noncomputable def ep01100101_0 : Blocks := edgeBlocks% "full/vectors/01100101-E-0000.bin"
private noncomputable def ep01100101_1 : Blocks := edgeBlocks% "full/vectors/01100101-E-0001.bin"
private noncomputable def ep01100101_2 : Blocks := edgeBlocks% "full/vectors/01100101-E-0002.bin"
private noncomputable def ep01100101_3 : Blocks := edgeBlocks% "full/vectors/01100101-E-0003.bin"
private noncomputable def ep01100101_4 : Blocks := edgeBlocks% "full/vectors/01100101-E-0004.bin"
private noncomputable def ep01100101_5 : Blocks := edgeBlocks% "full/vectors/01100101-E-0005.bin"
private noncomputable def ep01100101_6 : Blocks := edgeBlocks% "full/vectors/01100101-E-0006.bin"
private noncomputable def ep01100101_7 : Blocks := edgeBlocks% "full/vectors/01100101-E-0007.bin"
private noncomputable def ep01100101_8 : Blocks := edgeBlocks% "full/vectors/01100101-E-0008.bin"
noncomputable def ep01100101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01100101_0 ep01100101_1) (Blocks.join ep01100101_2 ep01100101_3)) (Blocks.join (Blocks.join ep01100101_4 ep01100101_5) (Blocks.join ep01100101_6 (Blocks.join ep01100101_7 ep01100101_8))))
private theorem idp01100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110010.list =
    C ((2:ℤ)^1301) * horner X vp01100101.list + horner X ep01100101.list := by
  exact edge_identity (B := (2:ℤ)^1805) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01100101 : Branch 1 (-3199761639/64000000 : ℚ) vp0110010 := by
  apply branch_checked idp01100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3199761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3231761639/32000000 : ℚ) by norm_num]
  exact coverp01100101
theorem coverp0110010 : Covers (-3199761639/64000000 : ℚ) vp0110010 := join_branches bp01100100 bp01100101
private noncomputable def vp011001_0 : Blocks := edgeBlocks% "full/vectors/011001-V-0000.bin"
private noncomputable def vp011001_1 : Blocks := edgeBlocks% "full/vectors/011001-V-0001.bin"
private noncomputable def vp011001_2 : Blocks := edgeBlocks% "full/vectors/011001-V-0002.bin"
private noncomputable def vp011001_3 : Blocks := edgeBlocks% "full/vectors/011001-V-0003.bin"
private noncomputable def vp011001_4 : Blocks := edgeBlocks% "full/vectors/011001-V-0004.bin"
private noncomputable def vp011001_5 : Blocks := edgeBlocks% "full/vectors/011001-V-0005.bin"
private noncomputable def vp011001_6 : Blocks := edgeBlocks% "full/vectors/011001-V-0006.bin"
private noncomputable def vp011001_7 : Blocks := edgeBlocks% "full/vectors/011001-V-0007.bin"
private noncomputable def vp011001_8 : Blocks := edgeBlocks% "full/vectors/011001-V-0008.bin"
private noncomputable def vp011001_9 : Blocks := edgeBlocks% "full/vectors/011001-V-0009.bin"
private noncomputable def vp011001_10 : Blocks := edgeBlocks% "full/vectors/011001-V-0010.bin"
private noncomputable def vp011001_11 : Blocks := edgeBlocks% "full/vectors/011001-V-0011.bin"
private noncomputable def vp011001_12 : Blocks := edgeBlocks% "full/vectors/011001-V-0012.bin"
private noncomputable def vp011001_13 : Blocks := edgeBlocks% "full/vectors/011001-V-0013.bin"
private noncomputable def vp011001_14 : Blocks := edgeBlocks% "full/vectors/011001-V-0014.bin"
private noncomputable def vp011001_15 : Blocks := edgeBlocks% "full/vectors/011001-V-0015.bin"
private noncomputable def vp011001_16 : Blocks := edgeBlocks% "full/vectors/011001-V-0016.bin"
noncomputable def vp011001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp011001_0 vp011001_1) (Blocks.join vp011001_2 vp011001_3)) (Blocks.join (Blocks.join vp011001_4 vp011001_5) (Blocks.join vp011001_6 vp011001_7))) (Blocks.join (Blocks.join (Blocks.join vp011001_8 vp011001_9) (Blocks.join vp011001_10 vp011001_11)) (Blocks.join (Blocks.join vp011001_12 vp011001_13) (Blocks.join vp011001_14 (Blocks.join vp011001_15 vp011001_16)))))
private theorem bp0110010 : Branch 0 (-3199761639/128000000 : ℚ) vp011001 := by
  apply branch_left_normalized (c:=vp0110010) (k:=0) (m:=1116) (by decide +kernel)
  rw [show 2*(-3199761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-3199761639/64000000 : ℚ) by norm_num]
  exact coverp0110010
private noncomputable def ep0110011_0 : Blocks := edgeBlocks% "full/vectors/0110011-E-0000.bin"
private noncomputable def ep0110011_1 : Blocks := edgeBlocks% "full/vectors/0110011-E-0001.bin"
private noncomputable def ep0110011_2 : Blocks := edgeBlocks% "full/vectors/0110011-E-0002.bin"
private noncomputable def ep0110011_3 : Blocks := edgeBlocks% "full/vectors/0110011-E-0003.bin"
private noncomputable def ep0110011_4 : Blocks := edgeBlocks% "full/vectors/0110011-E-0004.bin"
private noncomputable def ep0110011_5 : Blocks := edgeBlocks% "full/vectors/0110011-E-0005.bin"
private noncomputable def ep0110011_6 : Blocks := edgeBlocks% "full/vectors/0110011-E-0006.bin"
private noncomputable def ep0110011_7 : Blocks := edgeBlocks% "full/vectors/0110011-E-0007.bin"
private noncomputable def ep0110011_8 : Blocks := edgeBlocks% "full/vectors/0110011-E-0008.bin"
private noncomputable def ep0110011_9 : Blocks := edgeBlocks% "full/vectors/0110011-E-0009.bin"
private noncomputable def ep0110011_10 : Blocks := edgeBlocks% "full/vectors/0110011-E-0010.bin"
private noncomputable def ep0110011_11 : Blocks := edgeBlocks% "full/vectors/0110011-E-0011.bin"
private noncomputable def ep0110011_12 : Blocks := edgeBlocks% "full/vectors/0110011-E-0012.bin"
private noncomputable def ep0110011_13 : Blocks := edgeBlocks% "full/vectors/0110011-E-0013.bin"
private noncomputable def ep0110011_14 : Blocks := edgeBlocks% "full/vectors/0110011-E-0014.bin"
private noncomputable def ep0110011_15 : Blocks := edgeBlocks% "full/vectors/0110011-E-0015.bin"
private noncomputable def ep0110011_16 : Blocks := edgeBlocks% "full/vectors/0110011-E-0016.bin"
noncomputable def ep0110011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0110011_0 ep0110011_1) (Blocks.join ep0110011_2 ep0110011_3)) (Blocks.join (Blocks.join ep0110011_4 ep0110011_5) (Blocks.join ep0110011_6 ep0110011_7))) (Blocks.join (Blocks.join (Blocks.join ep0110011_8 ep0110011_9) (Blocks.join ep0110011_10 ep0110011_11)) (Blocks.join (Blocks.join ep0110011_12 ep0110011_13) (Blocks.join ep0110011_14 (Blocks.join ep0110011_15 ep0110011_16)))))
private theorem idp0110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011001.list =
    C ((2:ℤ)^2543) * horner X vp0110011.list + horner X ep0110011.list := by
  exact edge_identity (B := (2:ℤ)^3442) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110011 : Branch 1 (-3199761639/128000000 : ℚ) vp011001 := by
  apply branch_checked idp0110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3199761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-3263761639/64000000 : ℚ) by norm_num]
  exact coverp0110011
theorem coverp011001 : Covers (-3199761639/128000000 : ℚ) vp011001 := join_branches bp0110010 bp0110011
end NextProof.EdgeFull

