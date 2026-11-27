import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp011011111111_0 : Blocks := edgeBlocks% "full/vectors/011011111111-V-0000.bin"
noncomputable def vp011011111111 : Blocks := vp011011111111_0
theorem coverp011011111111 : Covers (-3581761639/2000000 : ℚ) vp011011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp011011111110_0 : Blocks := edgeBlocks% "full/vectors/011011111110-V-0000.bin"
noncomputable def vp011011111110 : Blocks := vp011011111110_0
theorem coverp011011111110 : Covers (-3579761639/2000000 : ℚ) vp011011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp01101111111_0 : Blocks := edgeBlocks% "full/vectors/01101111111-V-0000.bin"
noncomputable def vp01101111111 : Blocks := vp01101111111_0
private theorem bp011011111110 : Branch 0 (-3579761639/4000000 : ℚ) vp01101111111 := by
  apply branch_left_normalized (c:=vp011011111110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3579761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3579761639/2000000 : ℚ) by norm_num]
  exact coverp011011111110
private noncomputable def ep011011111111_0 : Blocks := edgeBlocks% "full/vectors/011011111111-E-0000.bin"
noncomputable def ep011011111111 : Blocks := ep011011111111_0
private theorem idp011011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101111111.list =
    C ((2:ℤ)^99) * horner X vp011011111111.list + horner X ep011011111111.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011111111 : Branch 1 (-3579761639/4000000 : ℚ) vp01101111111 := by
  apply branch_checked idp011011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3579761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3581761639/2000000 : ℚ) by norm_num]
  exact coverp011011111111
theorem coverp01101111111 : Covers (-3579761639/4000000 : ℚ) vp01101111111 := join_branches bp011011111110 bp011011111111
private noncomputable def vp011011111101_0 : Blocks := edgeBlocks% "full/vectors/011011111101-V-0000.bin"
noncomputable def vp011011111101 : Blocks := vp011011111101_0
theorem coverp011011111101 : Covers (-3577761639/2000000 : ℚ) vp011011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp011011111100_0 : Blocks := edgeBlocks% "full/vectors/011011111100-V-0000.bin"
noncomputable def vp011011111100 : Blocks := vp011011111100_0
theorem coverp011011111100 : Covers (-3575761639/2000000 : ℚ) vp011011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp01101111110_0 : Blocks := edgeBlocks% "full/vectors/01101111110-V-0000.bin"
noncomputable def vp01101111110 : Blocks := vp01101111110_0
private theorem bp011011111100 : Branch 0 (-3575761639/4000000 : ℚ) vp01101111110 := by
  apply branch_left_normalized (c:=vp011011111100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3575761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3575761639/2000000 : ℚ) by norm_num]
  exact coverp011011111100
private noncomputable def ep011011111101_0 : Blocks := edgeBlocks% "full/vectors/011011111101-E-0000.bin"
noncomputable def ep011011111101 : Blocks := ep011011111101_0
private theorem idp011011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101111110.list =
    C ((2:ℤ)^97) * horner X vp011011111101.list + horner X ep011011111101.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011111101 : Branch 1 (-3575761639/4000000 : ℚ) vp01101111110 := by
  apply branch_checked idp011011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3575761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3577761639/2000000 : ℚ) by norm_num]
  exact coverp011011111101
theorem coverp01101111110 : Covers (-3575761639/4000000 : ℚ) vp01101111110 := join_branches bp011011111100 bp011011111101
private noncomputable def vp0110111111_0 : Blocks := edgeBlocks% "full/vectors/0110111111-V-0000.bin"
private noncomputable def vp0110111111_1 : Blocks := edgeBlocks% "full/vectors/0110111111-V-0001.bin"
noncomputable def vp0110111111 : Blocks := (Blocks.join vp0110111111_0 vp0110111111_1)
private theorem bp01101111110 : Branch 0 (-3575761639/8000000 : ℚ) vp0110111111 := by
  apply branch_left_normalized (c:=vp01101111110) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3575761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3575761639/4000000 : ℚ) by norm_num]
  exact coverp01101111110
private noncomputable def ep01101111111_0 : Blocks := edgeBlocks% "full/vectors/01101111111-E-0000.bin"
private noncomputable def ep01101111111_1 : Blocks := edgeBlocks% "full/vectors/01101111111-E-0001.bin"
noncomputable def ep01101111111 : Blocks := (Blocks.join ep01101111111_0 ep01101111111_1)
private theorem idp01101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110111111.list =
    C ((2:ℤ)^175) * horner X vp01101111111.list + horner X ep01101111111.list := by
  exact edge_identity (B := (2:ℤ)^323) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101111111 : Branch 1 (-3575761639/8000000 : ℚ) vp0110111111 := by
  apply branch_checked idp01101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3575761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3579761639/4000000 : ℚ) by norm_num]
  exact coverp01101111111
theorem coverp0110111111 : Covers (-3575761639/8000000 : ℚ) vp0110111111 := join_branches bp01101111110 bp01101111111
private noncomputable def vp01101111101_0 : Blocks := edgeBlocks% "full/vectors/01101111101-V-0000.bin"
noncomputable def vp01101111101 : Blocks := vp01101111101_0
theorem coverp01101111101 : Covers (-3571761639/4000000 : ℚ) vp01101111101 := cover_leaf (by decide +kernel)
private noncomputable def vp01101111100_0 : Blocks := edgeBlocks% "full/vectors/01101111100-V-0000.bin"
noncomputable def vp01101111100 : Blocks := vp01101111100_0
theorem coverp01101111100 : Covers (-3567761639/4000000 : ℚ) vp01101111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0110111110_0 : Blocks := edgeBlocks% "full/vectors/0110111110-V-0000.bin"
private noncomputable def vp0110111110_1 : Blocks := edgeBlocks% "full/vectors/0110111110-V-0001.bin"
noncomputable def vp0110111110 : Blocks := (Blocks.join vp0110111110_0 vp0110111110_1)
private theorem bp01101111100 : Branch 0 (-3567761639/8000000 : ℚ) vp0110111110 := by
  apply branch_left_normalized (c:=vp01101111100) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3567761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3567761639/4000000 : ℚ) by norm_num]
  exact coverp01101111100
private noncomputable def ep01101111101_0 : Blocks := edgeBlocks% "full/vectors/01101111101-E-0000.bin"
private noncomputable def ep01101111101_1 : Blocks := edgeBlocks% "full/vectors/01101111101-E-0001.bin"
noncomputable def ep01101111101 : Blocks := (Blocks.join ep01101111101_0 ep01101111101_1)
private theorem idp01101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110111110.list =
    C ((2:ℤ)^172) * horner X vp01101111101.list + horner X ep01101111101.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101111101 : Branch 1 (-3567761639/8000000 : ℚ) vp0110111110 := by
  apply branch_checked idp01101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3567761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3571761639/4000000 : ℚ) by norm_num]
  exact coverp01101111101
theorem coverp0110111110 : Covers (-3567761639/8000000 : ℚ) vp0110111110 := join_branches bp01101111100 bp01101111101
private noncomputable def vp011011111_0 : Blocks := edgeBlocks% "full/vectors/011011111-V-0000.bin"
private noncomputable def vp011011111_1 : Blocks := edgeBlocks% "full/vectors/011011111-V-0001.bin"
private noncomputable def vp011011111_2 : Blocks := edgeBlocks% "full/vectors/011011111-V-0002.bin"
noncomputable def vp011011111 : Blocks := (Blocks.join vp011011111_0 (Blocks.join vp011011111_1 vp011011111_2))
private theorem bp0110111110 : Branch 0 (-3567761639/16000000 : ℚ) vp011011111 := by
  apply branch_left_normalized (c:=vp0110111110) (k:=0) (m:=150) (by decide +kernel)
  rw [show 2*(-3567761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3567761639/8000000 : ℚ) by norm_num]
  exact coverp0110111110
private noncomputable def ep0110111111_0 : Blocks := edgeBlocks% "full/vectors/0110111111-E-0000.bin"
private noncomputable def ep0110111111_1 : Blocks := edgeBlocks% "full/vectors/0110111111-E-0001.bin"
private noncomputable def ep0110111111_2 : Blocks := edgeBlocks% "full/vectors/0110111111-E-0002.bin"
noncomputable def ep0110111111 : Blocks := (Blocks.join ep0110111111_0 (Blocks.join ep0110111111_1 ep0110111111_2))
private theorem idp0110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011011111.list =
    C ((2:ℤ)^325) * horner X vp0110111111.list + horner X ep0110111111.list := by
  exact edge_identity (B := (2:ℤ)^519) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110111111 : Branch 1 (-3567761639/16000000 : ℚ) vp011011111 := by
  apply branch_checked idp0110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3567761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3575761639/8000000 : ℚ) by norm_num]
  exact coverp0110111111
theorem coverp011011111 : Covers (-3567761639/16000000 : ℚ) vp011011111 := join_branches bp0110111110 bp0110111111
private noncomputable def vp01101111011_0 : Blocks := edgeBlocks% "full/vectors/01101111011-V-0000.bin"
noncomputable def vp01101111011 : Blocks := vp01101111011_0
theorem coverp01101111011 : Covers (-3563761639/4000000 : ℚ) vp01101111011 := cover_leaf (by decide +kernel)
private noncomputable def vp01101111010_0 : Blocks := edgeBlocks% "full/vectors/01101111010-V-0000.bin"
noncomputable def vp01101111010 : Blocks := vp01101111010_0
theorem coverp01101111010 : Covers (-3559761639/4000000 : ℚ) vp01101111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0110111101_0 : Blocks := edgeBlocks% "full/vectors/0110111101-V-0000.bin"
private noncomputable def vp0110111101_1 : Blocks := edgeBlocks% "full/vectors/0110111101-V-0001.bin"
noncomputable def vp0110111101 : Blocks := (Blocks.join vp0110111101_0 vp0110111101_1)
private theorem bp01101111010 : Branch 0 (-3559761639/8000000 : ℚ) vp0110111101 := by
  apply branch_left_normalized (c:=vp01101111010) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-3559761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3559761639/4000000 : ℚ) by norm_num]
  exact coverp01101111010
private noncomputable def ep01101111011_0 : Blocks := edgeBlocks% "full/vectors/01101111011-E-0000.bin"
private noncomputable def ep01101111011_1 : Blocks := edgeBlocks% "full/vectors/01101111011-E-0001.bin"
noncomputable def ep01101111011 : Blocks := (Blocks.join ep01101111011_0 ep01101111011_1)
private theorem idp01101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110111101.list =
    C ((2:ℤ)^172) * horner X vp01101111011.list + horner X ep01101111011.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101111011 : Branch 1 (-3559761639/8000000 : ℚ) vp0110111101 := by
  apply branch_checked idp01101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3559761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3563761639/4000000 : ℚ) by norm_num]
  exact coverp01101111011
theorem coverp0110111101 : Covers (-3559761639/8000000 : ℚ) vp0110111101 := join_branches bp01101111010 bp01101111011
private noncomputable def vp01101111001_0 : Blocks := edgeBlocks% "full/vectors/01101111001-V-0000.bin"
noncomputable def vp01101111001 : Blocks := vp01101111001_0
theorem coverp01101111001 : Covers (-3555761639/4000000 : ℚ) vp01101111001 := cover_leaf (by decide +kernel)
private noncomputable def vp01101111000_0 : Blocks := edgeBlocks% "full/vectors/01101111000-V-0000.bin"
noncomputable def vp01101111000 : Blocks := vp01101111000_0
theorem coverp01101111000 : Covers (-3551761639/4000000 : ℚ) vp01101111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0110111100_0 : Blocks := edgeBlocks% "full/vectors/0110111100-V-0000.bin"
private noncomputable def vp0110111100_1 : Blocks := edgeBlocks% "full/vectors/0110111100-V-0001.bin"
noncomputable def vp0110111100 : Blocks := (Blocks.join vp0110111100_0 vp0110111100_1)
private theorem bp01101111000 : Branch 0 (-3551761639/8000000 : ℚ) vp0110111100 := by
  apply branch_left_normalized (c:=vp01101111000) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-3551761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3551761639/4000000 : ℚ) by norm_num]
  exact coverp01101111000
private noncomputable def ep01101111001_0 : Blocks := edgeBlocks% "full/vectors/01101111001-E-0000.bin"
private noncomputable def ep01101111001_1 : Blocks := edgeBlocks% "full/vectors/01101111001-E-0001.bin"
noncomputable def ep01101111001 : Blocks := (Blocks.join ep01101111001_0 ep01101111001_1)
private theorem idp01101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110111100.list =
    C ((2:ℤ)^173) * horner X vp01101111001.list + horner X ep01101111001.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101111001 : Branch 1 (-3551761639/8000000 : ℚ) vp0110111100 := by
  apply branch_checked idp01101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3551761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3555761639/4000000 : ℚ) by norm_num]
  exact coverp01101111001
theorem coverp0110111100 : Covers (-3551761639/8000000 : ℚ) vp0110111100 := join_branches bp01101111000 bp01101111001
private noncomputable def vp011011110_0 : Blocks := edgeBlocks% "full/vectors/011011110-V-0000.bin"
private noncomputable def vp011011110_1 : Blocks := edgeBlocks% "full/vectors/011011110-V-0001.bin"
private noncomputable def vp011011110_2 : Blocks := edgeBlocks% "full/vectors/011011110-V-0002.bin"
noncomputable def vp011011110 : Blocks := (Blocks.join vp011011110_0 (Blocks.join vp011011110_1 vp011011110_2))
private theorem bp0110111100 : Branch 0 (-3551761639/16000000 : ℚ) vp011011110 := by
  apply branch_left_normalized (c:=vp0110111100) (k:=0) (m:=149) (by decide +kernel)
  rw [show 2*(-3551761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3551761639/8000000 : ℚ) by norm_num]
  exact coverp0110111100
private noncomputable def ep0110111101_0 : Blocks := edgeBlocks% "full/vectors/0110111101-E-0000.bin"
private noncomputable def ep0110111101_1 : Blocks := edgeBlocks% "full/vectors/0110111101-E-0001.bin"
private noncomputable def ep0110111101_2 : Blocks := edgeBlocks% "full/vectors/0110111101-E-0002.bin"
noncomputable def ep0110111101 : Blocks := (Blocks.join ep0110111101_0 (Blocks.join ep0110111101_1 ep0110111101_2))
private theorem idp0110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011011110.list =
    C ((2:ℤ)^326) * horner X vp0110111101.list + horner X ep0110111101.list := by
  exact edge_identity (B := (2:ℤ)^514) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110111101 : Branch 1 (-3551761639/16000000 : ℚ) vp011011110 := by
  apply branch_checked idp0110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3551761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3559761639/8000000 : ℚ) by norm_num]
  exact coverp0110111101
theorem coverp011011110 : Covers (-3551761639/16000000 : ℚ) vp011011110 := join_branches bp0110111100 bp0110111101
private noncomputable def vp01101111_0 : Blocks := edgeBlocks% "full/vectors/01101111-V-0000.bin"
private noncomputable def vp01101111_1 : Blocks := edgeBlocks% "full/vectors/01101111-V-0001.bin"
private noncomputable def vp01101111_2 : Blocks := edgeBlocks% "full/vectors/01101111-V-0002.bin"
private noncomputable def vp01101111_3 : Blocks := edgeBlocks% "full/vectors/01101111-V-0003.bin"
private noncomputable def vp01101111_4 : Blocks := edgeBlocks% "full/vectors/01101111-V-0004.bin"
noncomputable def vp01101111 : Blocks := (Blocks.join (Blocks.join vp01101111_0 vp01101111_1) (Blocks.join vp01101111_2 (Blocks.join vp01101111_3 vp01101111_4)))
private theorem bp011011110 : Branch 0 (-3551761639/32000000 : ℚ) vp01101111 := by
  apply branch_left_normalized (c:=vp011011110) (k:=0) (m:=280) (by decide +kernel)
  rw [show 2*(-3551761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3551761639/16000000 : ℚ) by norm_num]
  exact coverp011011110
private noncomputable def ep011011111_0 : Blocks := edgeBlocks% "full/vectors/011011111-E-0000.bin"
private noncomputable def ep011011111_1 : Blocks := edgeBlocks% "full/vectors/011011111-E-0001.bin"
private noncomputable def ep011011111_2 : Blocks := edgeBlocks% "full/vectors/011011111-E-0002.bin"
private noncomputable def ep011011111_3 : Blocks := edgeBlocks% "full/vectors/011011111-E-0003.bin"
private noncomputable def ep011011111_4 : Blocks := edgeBlocks% "full/vectors/011011111-E-0004.bin"
noncomputable def ep011011111 : Blocks := (Blocks.join (Blocks.join ep011011111_0 ep011011111_1) (Blocks.join ep011011111_2 (Blocks.join ep011011111_3 ep011011111_4)))
private theorem idp011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101111.list =
    C ((2:ℤ)^631) * horner X vp011011111.list + horner X ep011011111.list := by
  exact edge_identity (B := (2:ℤ)^914) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011111 : Branch 1 (-3551761639/32000000 : ℚ) vp01101111 := by
  apply branch_checked idp011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3551761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3567761639/16000000 : ℚ) by norm_num]
  exact coverp011011111
theorem coverp01101111 : Covers (-3551761639/32000000 : ℚ) vp01101111 := join_branches bp011011110 bp011011111
private noncomputable def vp01101110111_0 : Blocks := edgeBlocks% "full/vectors/01101110111-V-0000.bin"
noncomputable def vp01101110111 : Blocks := vp01101110111_0
theorem coverp01101110111 : Covers (-3547761639/4000000 : ℚ) vp01101110111 := cover_leaf (by decide +kernel)
private noncomputable def vp01101110110_0 : Blocks := edgeBlocks% "full/vectors/01101110110-V-0000.bin"
noncomputable def vp01101110110 : Blocks := vp01101110110_0
theorem coverp01101110110 : Covers (-3543761639/4000000 : ℚ) vp01101110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0110111011_0 : Blocks := edgeBlocks% "full/vectors/0110111011-V-0000.bin"
private noncomputable def vp0110111011_1 : Blocks := edgeBlocks% "full/vectors/0110111011-V-0001.bin"
noncomputable def vp0110111011 : Blocks := (Blocks.join vp0110111011_0 vp0110111011_1)
private theorem bp01101110110 : Branch 0 (-3543761639/8000000 : ℚ) vp0110111011 := by
  apply branch_left_normalized (c:=vp01101110110) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-3543761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3543761639/4000000 : ℚ) by norm_num]
  exact coverp01101110110
private noncomputable def ep01101110111_0 : Blocks := edgeBlocks% "full/vectors/01101110111-E-0000.bin"
private noncomputable def ep01101110111_1 : Blocks := edgeBlocks% "full/vectors/01101110111-E-0001.bin"
noncomputable def ep01101110111 : Blocks := (Blocks.join ep01101110111_0 ep01101110111_1)
private theorem idp01101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110111011.list =
    C ((2:ℤ)^172) * horner X vp01101110111.list + horner X ep01101110111.list := by
  exact edge_identity (B := (2:ℤ)^311) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101110111 : Branch 1 (-3543761639/8000000 : ℚ) vp0110111011 := by
  apply branch_checked idp01101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3543761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3547761639/4000000 : ℚ) by norm_num]
  exact coverp01101110111
theorem coverp0110111011 : Covers (-3543761639/8000000 : ℚ) vp0110111011 := join_branches bp01101110110 bp01101110111
private noncomputable def vp01101110101_0 : Blocks := edgeBlocks% "full/vectors/01101110101-V-0000.bin"
noncomputable def vp01101110101 : Blocks := vp01101110101_0
theorem coverp01101110101 : Covers (-3539761639/4000000 : ℚ) vp01101110101 := cover_leaf (by decide +kernel)
private noncomputable def vp01101110100_0 : Blocks := edgeBlocks% "full/vectors/01101110100-V-0000.bin"
noncomputable def vp01101110100 : Blocks := vp01101110100_0
theorem coverp01101110100 : Covers (-3535761639/4000000 : ℚ) vp01101110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0110111010_0 : Blocks := edgeBlocks% "full/vectors/0110111010-V-0000.bin"
private noncomputable def vp0110111010_1 : Blocks := edgeBlocks% "full/vectors/0110111010-V-0001.bin"
noncomputable def vp0110111010 : Blocks := (Blocks.join vp0110111010_0 vp0110111010_1)
private theorem bp01101110100 : Branch 0 (-3535761639/8000000 : ℚ) vp0110111010 := by
  apply branch_left_normalized (c:=vp01101110100) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-3535761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3535761639/4000000 : ℚ) by norm_num]
  exact coverp01101110100
private noncomputable def ep01101110101_0 : Blocks := edgeBlocks% "full/vectors/01101110101-E-0000.bin"
private noncomputable def ep01101110101_1 : Blocks := edgeBlocks% "full/vectors/01101110101-E-0001.bin"
noncomputable def ep01101110101 : Blocks := (Blocks.join ep01101110101_0 ep01101110101_1)
private theorem idp01101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110111010.list =
    C ((2:ℤ)^172) * horner X vp01101110101.list + horner X ep01101110101.list := by
  exact edge_identity (B := (2:ℤ)^312) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101110101 : Branch 1 (-3535761639/8000000 : ℚ) vp0110111010 := by
  apply branch_checked idp01101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3535761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3539761639/4000000 : ℚ) by norm_num]
  exact coverp01101110101
theorem coverp0110111010 : Covers (-3535761639/8000000 : ℚ) vp0110111010 := join_branches bp01101110100 bp01101110101
private noncomputable def vp011011101_0 : Blocks := edgeBlocks% "full/vectors/011011101-V-0000.bin"
private noncomputable def vp011011101_1 : Blocks := edgeBlocks% "full/vectors/011011101-V-0001.bin"
private noncomputable def vp011011101_2 : Blocks := edgeBlocks% "full/vectors/011011101-V-0002.bin"
noncomputable def vp011011101 : Blocks := (Blocks.join vp011011101_0 (Blocks.join vp011011101_1 vp011011101_2))
private theorem bp0110111010 : Branch 0 (-3535761639/16000000 : ℚ) vp011011101 := by
  apply branch_left_normalized (c:=vp0110111010) (k:=0) (m:=148) (by decide +kernel)
  rw [show 2*(-3535761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3535761639/8000000 : ℚ) by norm_num]
  exact coverp0110111010
private noncomputable def ep0110111011_0 : Blocks := edgeBlocks% "full/vectors/0110111011-E-0000.bin"
private noncomputable def ep0110111011_1 : Blocks := edgeBlocks% "full/vectors/0110111011-E-0001.bin"
private noncomputable def ep0110111011_2 : Blocks := edgeBlocks% "full/vectors/0110111011-E-0002.bin"
noncomputable def ep0110111011 : Blocks := (Blocks.join ep0110111011_0 (Blocks.join ep0110111011_1 ep0110111011_2))
private theorem idp0110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011011101.list =
    C ((2:ℤ)^328) * horner X vp0110111011.list + horner X ep0110111011.list := by
  exact edge_identity (B := (2:ℤ)^514) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110111011 : Branch 1 (-3535761639/16000000 : ℚ) vp011011101 := by
  apply branch_checked idp0110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3535761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3543761639/8000000 : ℚ) by norm_num]
  exact coverp0110111011
theorem coverp011011101 : Covers (-3535761639/16000000 : ℚ) vp011011101 := join_branches bp0110111010 bp0110111011
private noncomputable def vp01101110011_0 : Blocks := edgeBlocks% "full/vectors/01101110011-V-0000.bin"
noncomputable def vp01101110011 : Blocks := vp01101110011_0
theorem coverp01101110011 : Covers (-3531761639/4000000 : ℚ) vp01101110011 := cover_leaf (by decide +kernel)
private noncomputable def vp01101110010_0 : Blocks := edgeBlocks% "full/vectors/01101110010-V-0000.bin"
noncomputable def vp01101110010 : Blocks := vp01101110010_0
theorem coverp01101110010 : Covers (-3527761639/4000000 : ℚ) vp01101110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0110111001_0 : Blocks := edgeBlocks% "full/vectors/0110111001-V-0000.bin"
private noncomputable def vp0110111001_1 : Blocks := edgeBlocks% "full/vectors/0110111001-V-0001.bin"
noncomputable def vp0110111001 : Blocks := (Blocks.join vp0110111001_0 vp0110111001_1)
private theorem bp01101110010 : Branch 0 (-3527761639/8000000 : ℚ) vp0110111001 := by
  apply branch_left_normalized (c:=vp01101110010) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3527761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3527761639/4000000 : ℚ) by norm_num]
  exact coverp01101110010
private noncomputable def ep01101110011_0 : Blocks := edgeBlocks% "full/vectors/01101110011-E-0000.bin"
private noncomputable def ep01101110011_1 : Blocks := edgeBlocks% "full/vectors/01101110011-E-0001.bin"
noncomputable def ep01101110011 : Blocks := (Blocks.join ep01101110011_0 ep01101110011_1)
private theorem idp01101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110111001.list =
    C ((2:ℤ)^174) * horner X vp01101110011.list + horner X ep01101110011.list := by
  exact edge_identity (B := (2:ℤ)^315) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101110011 : Branch 1 (-3527761639/8000000 : ℚ) vp0110111001 := by
  apply branch_checked idp01101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3527761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3531761639/4000000 : ℚ) by norm_num]
  exact coverp01101110011
theorem coverp0110111001 : Covers (-3527761639/8000000 : ℚ) vp0110111001 := join_branches bp01101110010 bp01101110011
private noncomputable def vp01101110001_0 : Blocks := edgeBlocks% "full/vectors/01101110001-V-0000.bin"
noncomputable def vp01101110001 : Blocks := vp01101110001_0
theorem coverp01101110001 : Covers (-3523761639/4000000 : ℚ) vp01101110001 := cover_leaf (by decide +kernel)
private noncomputable def vp01101110000_0 : Blocks := edgeBlocks% "full/vectors/01101110000-V-0000.bin"
noncomputable def vp01101110000 : Blocks := vp01101110000_0
theorem coverp01101110000 : Covers (-3519761639/4000000 : ℚ) vp01101110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0110111000_0 : Blocks := edgeBlocks% "full/vectors/0110111000-V-0000.bin"
private noncomputable def vp0110111000_1 : Blocks := edgeBlocks% "full/vectors/0110111000-V-0001.bin"
noncomputable def vp0110111000 : Blocks := (Blocks.join vp0110111000_0 vp0110111000_1)
private theorem bp01101110000 : Branch 0 (-3519761639/8000000 : ℚ) vp0110111000 := by
  apply branch_left_normalized (c:=vp01101110000) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3519761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3519761639/4000000 : ℚ) by norm_num]
  exact coverp01101110000
private noncomputable def ep01101110001_0 : Blocks := edgeBlocks% "full/vectors/01101110001-E-0000.bin"
private noncomputable def ep01101110001_1 : Blocks := edgeBlocks% "full/vectors/01101110001-E-0001.bin"
noncomputable def ep01101110001 : Blocks := (Blocks.join ep01101110001_0 ep01101110001_1)
private theorem idp01101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110111000.list =
    C ((2:ℤ)^176) * horner X vp01101110001.list + horner X ep01101110001.list := by
  exact edge_identity (B := (2:ℤ)^319) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101110001 : Branch 1 (-3519761639/8000000 : ℚ) vp0110111000 := by
  apply branch_checked idp01101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3519761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3523761639/4000000 : ℚ) by norm_num]
  exact coverp01101110001
theorem coverp0110111000 : Covers (-3519761639/8000000 : ℚ) vp0110111000 := join_branches bp01101110000 bp01101110001
private noncomputable def vp011011100_0 : Blocks := edgeBlocks% "full/vectors/011011100-V-0000.bin"
private noncomputable def vp011011100_1 : Blocks := edgeBlocks% "full/vectors/011011100-V-0001.bin"
private noncomputable def vp011011100_2 : Blocks := edgeBlocks% "full/vectors/011011100-V-0002.bin"
noncomputable def vp011011100 : Blocks := (Blocks.join vp011011100_0 (Blocks.join vp011011100_1 vp011011100_2))
private theorem bp0110111000 : Branch 0 (-3519761639/16000000 : ℚ) vp011011100 := by
  apply branch_left_normalized (c:=vp0110111000) (k:=0) (m:=151) (by decide +kernel)
  rw [show 2*(-3519761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3519761639/8000000 : ℚ) by norm_num]
  exact coverp0110111000
private noncomputable def ep0110111001_0 : Blocks := edgeBlocks% "full/vectors/0110111001-E-0000.bin"
private noncomputable def ep0110111001_1 : Blocks := edgeBlocks% "full/vectors/0110111001-E-0001.bin"
private noncomputable def ep0110111001_2 : Blocks := edgeBlocks% "full/vectors/0110111001-E-0002.bin"
noncomputable def ep0110111001 : Blocks := (Blocks.join ep0110111001_0 (Blocks.join ep0110111001_1 ep0110111001_2))
private theorem idp0110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011011100.list =
    C ((2:ℤ)^334) * horner X vp0110111001.list + horner X ep0110111001.list := by
  exact edge_identity (B := (2:ℤ)^522) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110111001 : Branch 1 (-3519761639/16000000 : ℚ) vp011011100 := by
  apply branch_checked idp0110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3519761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3527761639/8000000 : ℚ) by norm_num]
  exact coverp0110111001
theorem coverp011011100 : Covers (-3519761639/16000000 : ℚ) vp011011100 := join_branches bp0110111000 bp0110111001
private noncomputable def vp01101110_0 : Blocks := edgeBlocks% "full/vectors/01101110-V-0000.bin"
private noncomputable def vp01101110_1 : Blocks := edgeBlocks% "full/vectors/01101110-V-0001.bin"
private noncomputable def vp01101110_2 : Blocks := edgeBlocks% "full/vectors/01101110-V-0002.bin"
private noncomputable def vp01101110_3 : Blocks := edgeBlocks% "full/vectors/01101110-V-0003.bin"
private noncomputable def vp01101110_4 : Blocks := edgeBlocks% "full/vectors/01101110-V-0004.bin"
noncomputable def vp01101110 : Blocks := (Blocks.join (Blocks.join vp01101110_0 vp01101110_1) (Blocks.join vp01101110_2 (Blocks.join vp01101110_3 vp01101110_4)))
private theorem bp011011100 : Branch 0 (-3519761639/32000000 : ℚ) vp01101110 := by
  apply branch_left_normalized (c:=vp011011100) (k:=0) (m:=284) (by decide +kernel)
  rw [show 2*(-3519761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3519761639/16000000 : ℚ) by norm_num]
  exact coverp011011100
private noncomputable def ep011011101_0 : Blocks := edgeBlocks% "full/vectors/011011101-E-0000.bin"
private noncomputable def ep011011101_1 : Blocks := edgeBlocks% "full/vectors/011011101-E-0001.bin"
private noncomputable def ep011011101_2 : Blocks := edgeBlocks% "full/vectors/011011101-E-0002.bin"
private noncomputable def ep011011101_3 : Blocks := edgeBlocks% "full/vectors/011011101-E-0003.bin"
private noncomputable def ep011011101_4 : Blocks := edgeBlocks% "full/vectors/011011101-E-0004.bin"
noncomputable def ep011011101 : Blocks := (Blocks.join (Blocks.join ep011011101_0 ep011011101_1) (Blocks.join ep011011101_2 (Blocks.join ep011011101_3 ep011011101_4)))
private theorem idp011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101110.list =
    C ((2:ℤ)^642) * horner X vp011011101.list + horner X ep011011101.list := by
  exact edge_identity (B := (2:ℤ)^923) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011101 : Branch 1 (-3519761639/32000000 : ℚ) vp01101110 := by
  apply branch_checked idp011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3519761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3535761639/16000000 : ℚ) by norm_num]
  exact coverp011011101
theorem coverp01101110 : Covers (-3519761639/32000000 : ℚ) vp01101110 := join_branches bp011011100 bp011011101
private noncomputable def vp0110111_0 : Blocks := edgeBlocks% "full/vectors/0110111-V-0000.bin"
private noncomputable def vp0110111_1 : Blocks := edgeBlocks% "full/vectors/0110111-V-0001.bin"
private noncomputable def vp0110111_2 : Blocks := edgeBlocks% "full/vectors/0110111-V-0002.bin"
private noncomputable def vp0110111_3 : Blocks := edgeBlocks% "full/vectors/0110111-V-0003.bin"
private noncomputable def vp0110111_4 : Blocks := edgeBlocks% "full/vectors/0110111-V-0004.bin"
private noncomputable def vp0110111_5 : Blocks := edgeBlocks% "full/vectors/0110111-V-0005.bin"
private noncomputable def vp0110111_6 : Blocks := edgeBlocks% "full/vectors/0110111-V-0006.bin"
private noncomputable def vp0110111_7 : Blocks := edgeBlocks% "full/vectors/0110111-V-0007.bin"
private noncomputable def vp0110111_8 : Blocks := edgeBlocks% "full/vectors/0110111-V-0008.bin"
noncomputable def vp0110111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0110111_0 vp0110111_1) (Blocks.join vp0110111_2 vp0110111_3)) (Blocks.join (Blocks.join vp0110111_4 vp0110111_5) (Blocks.join vp0110111_6 (Blocks.join vp0110111_7 vp0110111_8))))
private theorem bp01101110 : Branch 0 (-3519761639/64000000 : ℚ) vp0110111 := by
  apply branch_left_normalized (c:=vp01101110) (k:=0) (m:=545) (by decide +kernel)
  rw [show 2*(-3519761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3519761639/32000000 : ℚ) by norm_num]
  exact coverp01101110
private noncomputable def ep01101111_0 : Blocks := edgeBlocks% "full/vectors/01101111-E-0000.bin"
private noncomputable def ep01101111_1 : Blocks := edgeBlocks% "full/vectors/01101111-E-0001.bin"
private noncomputable def ep01101111_2 : Blocks := edgeBlocks% "full/vectors/01101111-E-0002.bin"
private noncomputable def ep01101111_3 : Blocks := edgeBlocks% "full/vectors/01101111-E-0003.bin"
private noncomputable def ep01101111_4 : Blocks := edgeBlocks% "full/vectors/01101111-E-0004.bin"
private noncomputable def ep01101111_5 : Blocks := edgeBlocks% "full/vectors/01101111-E-0005.bin"
private noncomputable def ep01101111_6 : Blocks := edgeBlocks% "full/vectors/01101111-E-0006.bin"
private noncomputable def ep01101111_7 : Blocks := edgeBlocks% "full/vectors/01101111-E-0007.bin"
private noncomputable def ep01101111_8 : Blocks := edgeBlocks% "full/vectors/01101111-E-0008.bin"
noncomputable def ep01101111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01101111_0 ep01101111_1) (Blocks.join ep01101111_2 ep01101111_3)) (Blocks.join (Blocks.join ep01101111_4 ep01101111_5) (Blocks.join ep01101111_6 (Blocks.join ep01101111_7 ep01101111_8))))
private theorem idp01101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110111.list =
    C ((2:ℤ)^1252) * horner X vp01101111.list + horner X ep01101111.list := by
  exact edge_identity (B := (2:ℤ)^1720) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101111 : Branch 1 (-3519761639/64000000 : ℚ) vp0110111 := by
  apply branch_checked idp01101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3519761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3551761639/32000000 : ℚ) by norm_num]
  exact coverp01101111
theorem coverp0110111 : Covers (-3519761639/64000000 : ℚ) vp0110111 := join_branches bp01101110 bp01101111
private noncomputable def vp01101101111_0 : Blocks := edgeBlocks% "full/vectors/01101101111-V-0000.bin"
noncomputable def vp01101101111 : Blocks := vp01101101111_0
theorem coverp01101101111 : Covers (-3515761639/4000000 : ℚ) vp01101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp01101101110_0 : Blocks := edgeBlocks% "full/vectors/01101101110-V-0000.bin"
noncomputable def vp01101101110 : Blocks := vp01101101110_0
theorem coverp01101101110 : Covers (-3511761639/4000000 : ℚ) vp01101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0110110111_0 : Blocks := edgeBlocks% "full/vectors/0110110111-V-0000.bin"
private noncomputable def vp0110110111_1 : Blocks := edgeBlocks% "full/vectors/0110110111-V-0001.bin"
noncomputable def vp0110110111 : Blocks := (Blocks.join vp0110110111_0 vp0110110111_1)
private theorem bp01101101110 : Branch 0 (-3511761639/8000000 : ℚ) vp0110110111 := by
  apply branch_left_normalized (c:=vp01101101110) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-3511761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3511761639/4000000 : ℚ) by norm_num]
  exact coverp01101101110
private noncomputable def ep01101101111_0 : Blocks := edgeBlocks% "full/vectors/01101101111-E-0000.bin"
private noncomputable def ep01101101111_1 : Blocks := edgeBlocks% "full/vectors/01101101111-E-0001.bin"
noncomputable def ep01101101111 : Blocks := (Blocks.join ep01101101111_0 ep01101101111_1)
private theorem idp01101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110110111.list =
    C ((2:ℤ)^181) * horner X vp01101101111.list + horner X ep01101101111.list := by
  exact edge_identity (B := (2:ℤ)^326) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101101111 : Branch 1 (-3511761639/8000000 : ℚ) vp0110110111 := by
  apply branch_checked idp01101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3511761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3515761639/4000000 : ℚ) by norm_num]
  exact coverp01101101111
theorem coverp0110110111 : Covers (-3511761639/8000000 : ℚ) vp0110110111 := join_branches bp01101101110 bp01101101111
private noncomputable def vp011011011011_0 : Blocks := edgeBlocks% "full/vectors/011011011011-V-0000.bin"
noncomputable def vp011011011011 : Blocks := vp011011011011_0
theorem coverp011011011011 : Covers (-3509761639/2000000 : ℚ) vp011011011011 := cover_leaf (by decide +kernel)
private noncomputable def vp011011011010_0 : Blocks := edgeBlocks% "full/vectors/011011011010-V-0000.bin"
noncomputable def vp011011011010 : Blocks := vp011011011010_0
theorem coverp011011011010 : Covers (-3507761639/2000000 : ℚ) vp011011011010 := cover_leaf (by decide +kernel)
private noncomputable def vp01101101101_0 : Blocks := edgeBlocks% "full/vectors/01101101101-V-0000.bin"
noncomputable def vp01101101101 : Blocks := vp01101101101_0
private theorem bp011011011010 : Branch 0 (-3507761639/4000000 : ℚ) vp01101101101 := by
  apply branch_left_normalized (c:=vp011011011010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3507761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3507761639/2000000 : ℚ) by norm_num]
  exact coverp011011011010
private noncomputable def ep011011011011_0 : Blocks := edgeBlocks% "full/vectors/011011011011-E-0000.bin"
noncomputable def ep011011011011 : Blocks := ep011011011011_0
private theorem idp011011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101101101.list =
    C ((2:ℤ)^99) * horner X vp011011011011.list + horner X ep011011011011.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011011011 : Branch 1 (-3507761639/4000000 : ℚ) vp01101101101 := by
  apply branch_checked idp011011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3507761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3509761639/2000000 : ℚ) by norm_num]
  exact coverp011011011011
theorem coverp01101101101 : Covers (-3507761639/4000000 : ℚ) vp01101101101 := join_branches bp011011011010 bp011011011011
private noncomputable def vp011011011001_0 : Blocks := edgeBlocks% "full/vectors/011011011001-V-0000.bin"
noncomputable def vp011011011001 : Blocks := vp011011011001_0
theorem coverp011011011001 : Covers (-3505761639/2000000 : ℚ) vp011011011001 := cover_leaf (by decide +kernel)
private noncomputable def vp011011011000_0 : Blocks := edgeBlocks% "full/vectors/011011011000-V-0000.bin"
noncomputable def vp011011011000 : Blocks := vp011011011000_0
theorem coverp011011011000 : Covers (-3503761639/2000000 : ℚ) vp011011011000 := cover_leaf (by decide +kernel)
private noncomputable def vp01101101100_0 : Blocks := edgeBlocks% "full/vectors/01101101100-V-0000.bin"
noncomputable def vp01101101100 : Blocks := vp01101101100_0
private theorem bp011011011000 : Branch 0 (-3503761639/4000000 : ℚ) vp01101101100 := by
  apply branch_left_normalized (c:=vp011011011000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3503761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3503761639/2000000 : ℚ) by norm_num]
  exact coverp011011011000
private noncomputable def ep011011011001_0 : Blocks := edgeBlocks% "full/vectors/011011011001-E-0000.bin"
noncomputable def ep011011011001 : Blocks := ep011011011001_0
private theorem idp011011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101101100.list =
    C ((2:ℤ)^99) * horner X vp011011011001.list + horner X ep011011011001.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011011001 : Branch 1 (-3503761639/4000000 : ℚ) vp01101101100 := by
  apply branch_checked idp011011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3503761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3505761639/2000000 : ℚ) by norm_num]
  exact coverp011011011001
theorem coverp01101101100 : Covers (-3503761639/4000000 : ℚ) vp01101101100 := join_branches bp011011011000 bp011011011001
private noncomputable def vp0110110110_0 : Blocks := edgeBlocks% "full/vectors/0110110110-V-0000.bin"
private noncomputable def vp0110110110_1 : Blocks := edgeBlocks% "full/vectors/0110110110-V-0001.bin"
noncomputable def vp0110110110 : Blocks := (Blocks.join vp0110110110_0 vp0110110110_1)
private theorem bp01101101100 : Branch 0 (-3503761639/8000000 : ℚ) vp0110110110 := by
  apply branch_left_normalized (c:=vp01101101100) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-3503761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3503761639/4000000 : ℚ) by norm_num]
  exact coverp01101101100
private noncomputable def ep01101101101_0 : Blocks := edgeBlocks% "full/vectors/01101101101-E-0000.bin"
private noncomputable def ep01101101101_1 : Blocks := edgeBlocks% "full/vectors/01101101101-E-0001.bin"
noncomputable def ep01101101101 : Blocks := (Blocks.join ep01101101101_0 ep01101101101_1)
private theorem idp01101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110110110.list =
    C ((2:ℤ)^178) * horner X vp01101101101.list + horner X ep01101101101.list := by
  exact edge_identity (B := (2:ℤ)^326) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101101101 : Branch 1 (-3503761639/8000000 : ℚ) vp0110110110 := by
  apply branch_checked idp01101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-3503761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3507761639/4000000 : ℚ) by norm_num]
  exact coverp01101101101
theorem coverp0110110110 : Covers (-3503761639/8000000 : ℚ) vp0110110110 := join_branches bp01101101100 bp01101101101
private noncomputable def vp011011011_0 : Blocks := edgeBlocks% "full/vectors/011011011-V-0000.bin"
private noncomputable def vp011011011_1 : Blocks := edgeBlocks% "full/vectors/011011011-V-0001.bin"
private noncomputable def vp011011011_2 : Blocks := edgeBlocks% "full/vectors/011011011-V-0002.bin"
noncomputable def vp011011011 : Blocks := (Blocks.join vp011011011_0 (Blocks.join vp011011011_1 vp011011011_2))
private theorem bp0110110110 : Branch 0 (-3503761639/16000000 : ℚ) vp011011011 := by
  apply branch_left_normalized (c:=vp0110110110) (k:=0) (m:=154) (by decide +kernel)
  rw [show 2*(-3503761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3503761639/8000000 : ℚ) by norm_num]
  exact coverp0110110110
private noncomputable def ep0110110111_0 : Blocks := edgeBlocks% "full/vectors/0110110111-E-0000.bin"
private noncomputable def ep0110110111_1 : Blocks := edgeBlocks% "full/vectors/0110110111-E-0001.bin"
private noncomputable def ep0110110111_2 : Blocks := edgeBlocks% "full/vectors/0110110111-E-0002.bin"
noncomputable def ep0110110111 : Blocks := (Blocks.join ep0110110111_0 (Blocks.join ep0110110111_1 ep0110110111_2))
private theorem idp0110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011011011.list =
    C ((2:ℤ)^333) * horner X vp0110110111.list + horner X ep0110110111.list := by
  exact edge_identity (B := (2:ℤ)^529) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110110111 : Branch 1 (-3503761639/16000000 : ℚ) vp011011011 := by
  apply branch_checked idp0110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3503761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3511761639/8000000 : ℚ) by norm_num]
  exact coverp0110110111
theorem coverp011011011 : Covers (-3503761639/16000000 : ℚ) vp011011011 := join_branches bp0110110110 bp0110110111
private noncomputable def vp011011010111_0 : Blocks := edgeBlocks% "full/vectors/011011010111-V-0000.bin"
noncomputable def vp011011010111 : Blocks := vp011011010111_0
theorem coverp011011010111 : Covers (-3501761639/2000000 : ℚ) vp011011010111 := cover_leaf (by decide +kernel)
private noncomputable def vp011011010110_0 : Blocks := edgeBlocks% "full/vectors/011011010110-V-0000.bin"
noncomputable def vp011011010110 : Blocks := vp011011010110_0
theorem coverp011011010110 : Covers (-3499761639/2000000 : ℚ) vp011011010110 := cover_leaf (by decide +kernel)
private noncomputable def vp01101101011_0 : Blocks := edgeBlocks% "full/vectors/01101101011-V-0000.bin"
noncomputable def vp01101101011 : Blocks := vp01101101011_0
private theorem bp011011010110 : Branch 0 (-3499761639/4000000 : ℚ) vp01101101011 := by
  apply branch_left_normalized (c:=vp011011010110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3499761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3499761639/2000000 : ℚ) by norm_num]
  exact coverp011011010110
private noncomputable def ep011011010111_0 : Blocks := edgeBlocks% "full/vectors/011011010111-E-0000.bin"
noncomputable def ep011011010111 : Blocks := ep011011010111_0
private theorem idp011011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101101011.list =
    C ((2:ℤ)^99) * horner X vp011011010111.list + horner X ep011011010111.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011010111 : Branch 1 (-3499761639/4000000 : ℚ) vp01101101011 := by
  apply branch_checked idp011011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-3499761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3501761639/2000000 : ℚ) by norm_num]
  exact coverp011011010111
theorem coverp01101101011 : Covers (-3499761639/4000000 : ℚ) vp01101101011 := join_branches bp011011010110 bp011011010111
private noncomputable def vp011011010101_0 : Blocks := edgeBlocks% "full/vectors/011011010101-V-0000.bin"
noncomputable def vp011011010101 : Blocks := vp011011010101_0
theorem coverp011011010101 : Covers (-3497761639/2000000 : ℚ) vp011011010101 := cover_leaf (by decide +kernel)
private noncomputable def vp011011010100_0 : Blocks := edgeBlocks% "full/vectors/011011010100-V-0000.bin"
noncomputable def vp011011010100 : Blocks := vp011011010100_0
theorem coverp011011010100 : Covers (-3495761639/2000000 : ℚ) vp011011010100 := cover_leaf (by decide +kernel)
private noncomputable def vp01101101010_0 : Blocks := edgeBlocks% "full/vectors/01101101010-V-0000.bin"
noncomputable def vp01101101010 : Blocks := vp01101101010_0
private theorem bp011011010100 : Branch 0 (-3495761639/4000000 : ℚ) vp01101101010 := by
  apply branch_left_normalized (c:=vp011011010100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3495761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3495761639/2000000 : ℚ) by norm_num]
  exact coverp011011010100
private noncomputable def ep011011010101_0 : Blocks := edgeBlocks% "full/vectors/011011010101-E-0000.bin"
noncomputable def ep011011010101 : Blocks := ep011011010101_0
private theorem idp011011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101101010.list =
    C ((2:ℤ)^99) * horner X vp011011010101.list + horner X ep011011010101.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011010101 : Branch 1 (-3495761639/4000000 : ℚ) vp01101101010 := by
  apply branch_checked idp011011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-3495761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3497761639/2000000 : ℚ) by norm_num]
  exact coverp011011010101
theorem coverp01101101010 : Covers (-3495761639/4000000 : ℚ) vp01101101010 := join_branches bp011011010100 bp011011010101
private noncomputable def vp0110110101_0 : Blocks := edgeBlocks% "full/vectors/0110110101-V-0000.bin"
private noncomputable def vp0110110101_1 : Blocks := edgeBlocks% "full/vectors/0110110101-V-0001.bin"
noncomputable def vp0110110101 : Blocks := (Blocks.join vp0110110101_0 vp0110110101_1)
private theorem bp01101101010 : Branch 0 (-3495761639/8000000 : ℚ) vp0110110101 := by
  apply branch_left_normalized (c:=vp01101101010) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-3495761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3495761639/4000000 : ℚ) by norm_num]
  exact coverp01101101010
private noncomputable def ep01101101011_0 : Blocks := edgeBlocks% "full/vectors/01101101011-E-0000.bin"
private noncomputable def ep01101101011_1 : Blocks := edgeBlocks% "full/vectors/01101101011-E-0001.bin"
noncomputable def ep01101101011 : Blocks := (Blocks.join ep01101101011_0 ep01101101011_1)
private theorem idp01101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110110101.list =
    C ((2:ℤ)^179) * horner X vp01101101011.list + horner X ep01101101011.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101101011 : Branch 1 (-3495761639/8000000 : ℚ) vp0110110101 := by
  apply branch_checked idp01101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-3495761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3499761639/4000000 : ℚ) by norm_num]
  exact coverp01101101011
theorem coverp0110110101 : Covers (-3495761639/8000000 : ℚ) vp0110110101 := join_branches bp01101101010 bp01101101011
private noncomputable def vp011011010011_0 : Blocks := edgeBlocks% "full/vectors/011011010011-V-0000.bin"
noncomputable def vp011011010011 : Blocks := vp011011010011_0
theorem coverp011011010011 : Covers (-3493761639/2000000 : ℚ) vp011011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp011011010010_0 : Blocks := edgeBlocks% "full/vectors/011011010010-V-0000.bin"
noncomputable def vp011011010010 : Blocks := vp011011010010_0
theorem coverp011011010010 : Covers (-3491761639/2000000 : ℚ) vp011011010010 := cover_leaf (by decide +kernel)
private noncomputable def vp01101101001_0 : Blocks := edgeBlocks% "full/vectors/01101101001-V-0000.bin"
noncomputable def vp01101101001 : Blocks := vp01101101001_0
private theorem bp011011010010 : Branch 0 (-3491761639/4000000 : ℚ) vp01101101001 := by
  apply branch_left_normalized (c:=vp011011010010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3491761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3491761639/2000000 : ℚ) by norm_num]
  exact coverp011011010010
private noncomputable def ep011011010011_0 : Blocks := edgeBlocks% "full/vectors/011011010011-E-0000.bin"
noncomputable def ep011011010011 : Blocks := ep011011010011_0
private theorem idp011011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101101001.list =
    C ((2:ℤ)^100) * horner X vp011011010011.list + horner X ep011011010011.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011010011 : Branch 1 (-3491761639/4000000 : ℚ) vp01101101001 := by
  apply branch_checked idp011011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-3491761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3493761639/2000000 : ℚ) by norm_num]
  exact coverp011011010011
theorem coverp01101101001 : Covers (-3491761639/4000000 : ℚ) vp01101101001 := join_branches bp011011010010 bp011011010011
private noncomputable def vp011011010001_0 : Blocks := edgeBlocks% "full/vectors/011011010001-V-0000.bin"
noncomputable def vp011011010001 : Blocks := vp011011010001_0
theorem coverp011011010001 : Covers (-3489761639/2000000 : ℚ) vp011011010001 := cover_leaf (by decide +kernel)
private noncomputable def vp011011010000_0 : Blocks := edgeBlocks% "full/vectors/011011010000-V-0000.bin"
noncomputable def vp011011010000 : Blocks := vp011011010000_0
theorem coverp011011010000 : Covers (-3487761639/2000000 : ℚ) vp011011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp01101101000_0 : Blocks := edgeBlocks% "full/vectors/01101101000-V-0000.bin"
noncomputable def vp01101101000 : Blocks := vp01101101000_0
private theorem bp011011010000 : Branch 0 (-3487761639/4000000 : ℚ) vp01101101000 := by
  apply branch_left_normalized (c:=vp011011010000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3487761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3487761639/2000000 : ℚ) by norm_num]
  exact coverp011011010000
private noncomputable def ep011011010001_0 : Blocks := edgeBlocks% "full/vectors/011011010001-E-0000.bin"
noncomputable def ep011011010001 : Blocks := ep011011010001_0
private theorem idp011011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101101000.list =
    C ((2:ℤ)^100) * horner X vp011011010001.list + horner X ep011011010001.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011010001 : Branch 1 (-3487761639/4000000 : ℚ) vp01101101000 := by
  apply branch_checked idp011011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3487761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3489761639/2000000 : ℚ) by norm_num]
  exact coverp011011010001
theorem coverp01101101000 : Covers (-3487761639/4000000 : ℚ) vp01101101000 := join_branches bp011011010000 bp011011010001
private noncomputable def vp0110110100_0 : Blocks := edgeBlocks% "full/vectors/0110110100-V-0000.bin"
private noncomputable def vp0110110100_1 : Blocks := edgeBlocks% "full/vectors/0110110100-V-0001.bin"
noncomputable def vp0110110100 : Blocks := (Blocks.join vp0110110100_0 vp0110110100_1)
private theorem bp01101101000 : Branch 0 (-3487761639/8000000 : ℚ) vp0110110100 := by
  apply branch_left_normalized (c:=vp01101101000) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-3487761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3487761639/4000000 : ℚ) by norm_num]
  exact coverp01101101000
private noncomputable def ep01101101001_0 : Blocks := edgeBlocks% "full/vectors/01101101001-E-0000.bin"
private noncomputable def ep01101101001_1 : Blocks := edgeBlocks% "full/vectors/01101101001-E-0001.bin"
noncomputable def ep01101101001 : Blocks := (Blocks.join ep01101101001_0 ep01101101001_1)
private theorem idp01101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110110100.list =
    C ((2:ℤ)^179) * horner X vp01101101001.list + horner X ep01101101001.list := by
  exact edge_identity (B := (2:ℤ)^328) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101101001 : Branch 1 (-3487761639/8000000 : ℚ) vp0110110100 := by
  apply branch_checked idp01101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-3487761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3491761639/4000000 : ℚ) by norm_num]
  exact coverp01101101001
theorem coverp0110110100 : Covers (-3487761639/8000000 : ℚ) vp0110110100 := join_branches bp01101101000 bp01101101001
private noncomputable def vp011011010_0 : Blocks := edgeBlocks% "full/vectors/011011010-V-0000.bin"
private noncomputable def vp011011010_1 : Blocks := edgeBlocks% "full/vectors/011011010-V-0001.bin"
private noncomputable def vp011011010_2 : Blocks := edgeBlocks% "full/vectors/011011010-V-0002.bin"
noncomputable def vp011011010 : Blocks := (Blocks.join vp011011010_0 (Blocks.join vp011011010_1 vp011011010_2))
private theorem bp0110110100 : Branch 0 (-3487761639/16000000 : ℚ) vp011011010 := by
  apply branch_left_normalized (c:=vp0110110100) (k:=0) (m:=155) (by decide +kernel)
  rw [show 2*(-3487761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3487761639/8000000 : ℚ) by norm_num]
  exact coverp0110110100
private noncomputable def ep0110110101_0 : Blocks := edgeBlocks% "full/vectors/0110110101-E-0000.bin"
private noncomputable def ep0110110101_1 : Blocks := edgeBlocks% "full/vectors/0110110101-E-0001.bin"
private noncomputable def ep0110110101_2 : Blocks := edgeBlocks% "full/vectors/0110110101-E-0002.bin"
noncomputable def ep0110110101 : Blocks := (Blocks.join ep0110110101_0 (Blocks.join ep0110110101_1 ep0110110101_2))
private theorem idp0110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011011010.list =
    C ((2:ℤ)^335) * horner X vp0110110101.list + horner X ep0110110101.list := by
  exact edge_identity (B := (2:ℤ)^531) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110110101 : Branch 1 (-3487761639/16000000 : ℚ) vp011011010 := by
  apply branch_checked idp0110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3487761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3495761639/8000000 : ℚ) by norm_num]
  exact coverp0110110101
theorem coverp011011010 : Covers (-3487761639/16000000 : ℚ) vp011011010 := join_branches bp0110110100 bp0110110101
private noncomputable def vp01101101_0 : Blocks := edgeBlocks% "full/vectors/01101101-V-0000.bin"
private noncomputable def vp01101101_1 : Blocks := edgeBlocks% "full/vectors/01101101-V-0001.bin"
private noncomputable def vp01101101_2 : Blocks := edgeBlocks% "full/vectors/01101101-V-0002.bin"
private noncomputable def vp01101101_3 : Blocks := edgeBlocks% "full/vectors/01101101-V-0003.bin"
private noncomputable def vp01101101_4 : Blocks := edgeBlocks% "full/vectors/01101101-V-0004.bin"
noncomputable def vp01101101 : Blocks := (Blocks.join (Blocks.join vp01101101_0 vp01101101_1) (Blocks.join vp01101101_2 (Blocks.join vp01101101_3 vp01101101_4)))
private theorem bp011011010 : Branch 0 (-3487761639/32000000 : ℚ) vp01101101 := by
  apply branch_left_normalized (c:=vp011011010) (k:=0) (m:=287) (by decide +kernel)
  rw [show 2*(-3487761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3487761639/16000000 : ℚ) by norm_num]
  exact coverp011011010
private noncomputable def ep011011011_0 : Blocks := edgeBlocks% "full/vectors/011011011-E-0000.bin"
private noncomputable def ep011011011_1 : Blocks := edgeBlocks% "full/vectors/011011011-E-0001.bin"
private noncomputable def ep011011011_2 : Blocks := edgeBlocks% "full/vectors/011011011-E-0002.bin"
private noncomputable def ep011011011_3 : Blocks := edgeBlocks% "full/vectors/011011011-E-0003.bin"
private noncomputable def ep011011011_4 : Blocks := edgeBlocks% "full/vectors/011011011-E-0004.bin"
noncomputable def ep011011011 : Blocks := (Blocks.join (Blocks.join ep011011011_0 ep011011011_1) (Blocks.join ep011011011_2 (Blocks.join ep011011011_3 ep011011011_4)))
private theorem idp011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101101.list =
    C ((2:ℤ)^645) * horner X vp011011011.list + horner X ep011011011.list := by
  exact edge_identity (B := (2:ℤ)^936) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011011 : Branch 1 (-3487761639/32000000 : ℚ) vp01101101 := by
  apply branch_checked idp011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3487761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3503761639/16000000 : ℚ) by norm_num]
  exact coverp011011011
theorem coverp01101101 : Covers (-3487761639/32000000 : ℚ) vp01101101 := join_branches bp011011010 bp011011011
private noncomputable def vp011011001111_0 : Blocks := edgeBlocks% "full/vectors/011011001111-V-0000.bin"
noncomputable def vp011011001111 : Blocks := vp011011001111_0
theorem coverp011011001111 : Covers (-3485761639/2000000 : ℚ) vp011011001111 := cover_leaf (by decide +kernel)
private noncomputable def vp011011001110_0 : Blocks := edgeBlocks% "full/vectors/011011001110-V-0000.bin"
noncomputable def vp011011001110 : Blocks := vp011011001110_0
theorem coverp011011001110 : Covers (-3483761639/2000000 : ℚ) vp011011001110 := cover_leaf (by decide +kernel)
private noncomputable def vp01101100111_0 : Blocks := edgeBlocks% "full/vectors/01101100111-V-0000.bin"
noncomputable def vp01101100111 : Blocks := vp01101100111_0
private theorem bp011011001110 : Branch 0 (-3483761639/4000000 : ℚ) vp01101100111 := by
  apply branch_left_normalized (c:=vp011011001110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3483761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3483761639/2000000 : ℚ) by norm_num]
  exact coverp011011001110
private noncomputable def ep011011001111_0 : Blocks := edgeBlocks% "full/vectors/011011001111-E-0000.bin"
noncomputable def ep011011001111 : Blocks := ep011011001111_0
private theorem idp011011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101100111.list =
    C ((2:ℤ)^100) * horner X vp011011001111.list + horner X ep011011001111.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011001111 : Branch 1 (-3483761639/4000000 : ℚ) vp01101100111 := by
  apply branch_checked idp011011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3483761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3485761639/2000000 : ℚ) by norm_num]
  exact coverp011011001111
theorem coverp01101100111 : Covers (-3483761639/4000000 : ℚ) vp01101100111 := join_branches bp011011001110 bp011011001111
private noncomputable def vp011011001101_0 : Blocks := edgeBlocks% "full/vectors/011011001101-V-0000.bin"
noncomputable def vp011011001101 : Blocks := vp011011001101_0
theorem coverp011011001101 : Covers (-3481761639/2000000 : ℚ) vp011011001101 := cover_leaf (by decide +kernel)
private noncomputable def vp011011001100_0 : Blocks := edgeBlocks% "full/vectors/011011001100-V-0000.bin"
noncomputable def vp011011001100 : Blocks := vp011011001100_0
theorem coverp011011001100 : Covers (-3479761639/2000000 : ℚ) vp011011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp01101100110_0 : Blocks := edgeBlocks% "full/vectors/01101100110-V-0000.bin"
noncomputable def vp01101100110 : Blocks := vp01101100110_0
private theorem bp011011001100 : Branch 0 (-3479761639/4000000 : ℚ) vp01101100110 := by
  apply branch_left_normalized (c:=vp011011001100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-3479761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3479761639/2000000 : ℚ) by norm_num]
  exact coverp011011001100
private noncomputable def ep011011001101_0 : Blocks := edgeBlocks% "full/vectors/011011001101-E-0000.bin"
noncomputable def ep011011001101 : Blocks := ep011011001101_0
private theorem idp011011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101100110.list =
    C ((2:ℤ)^101) * horner X vp011011001101.list + horner X ep011011001101.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011001101 : Branch 1 (-3479761639/4000000 : ℚ) vp01101100110 := by
  apply branch_checked idp011011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3479761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3481761639/2000000 : ℚ) by norm_num]
  exact coverp011011001101
theorem coverp01101100110 : Covers (-3479761639/4000000 : ℚ) vp01101100110 := join_branches bp011011001100 bp011011001101
private noncomputable def vp0110110011_0 : Blocks := edgeBlocks% "full/vectors/0110110011-V-0000.bin"
private noncomputable def vp0110110011_1 : Blocks := edgeBlocks% "full/vectors/0110110011-V-0001.bin"
noncomputable def vp0110110011 : Blocks := (Blocks.join vp0110110011_0 vp0110110011_1)
private theorem bp01101100110 : Branch 0 (-3479761639/8000000 : ℚ) vp0110110011 := by
  apply branch_left_normalized (c:=vp01101100110) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3479761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3479761639/4000000 : ℚ) by norm_num]
  exact coverp01101100110
private noncomputable def ep01101100111_0 : Blocks := edgeBlocks% "full/vectors/01101100111-E-0000.bin"
private noncomputable def ep01101100111_1 : Blocks := edgeBlocks% "full/vectors/01101100111-E-0001.bin"
noncomputable def ep01101100111 : Blocks := (Blocks.join ep01101100111_0 ep01101100111_1)
private theorem idp01101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110110011.list =
    C ((2:ℤ)^179) * horner X vp01101100111.list + horner X ep01101100111.list := by
  exact edge_identity (B := (2:ℤ)^328) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101100111 : Branch 1 (-3479761639/8000000 : ℚ) vp0110110011 := by
  apply branch_checked idp01101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3479761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3483761639/4000000 : ℚ) by norm_num]
  exact coverp01101100111
theorem coverp0110110011 : Covers (-3479761639/8000000 : ℚ) vp0110110011 := join_branches bp01101100110 bp01101100111
private noncomputable def vp011011001011_0 : Blocks := edgeBlocks% "full/vectors/011011001011-V-0000.bin"
noncomputable def vp011011001011 : Blocks := vp011011001011_0
theorem coverp011011001011 : Covers (-3477761639/2000000 : ℚ) vp011011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp011011001010_0 : Blocks := edgeBlocks% "full/vectors/011011001010-V-0000.bin"
noncomputable def vp011011001010 : Blocks := vp011011001010_0
theorem coverp011011001010 : Covers (-3475761639/2000000 : ℚ) vp011011001010 := cover_leaf (by decide +kernel)
private noncomputable def vp01101100101_0 : Blocks := edgeBlocks% "full/vectors/01101100101-V-0000.bin"
noncomputable def vp01101100101 : Blocks := vp01101100101_0
private theorem bp011011001010 : Branch 0 (-3475761639/4000000 : ℚ) vp01101100101 := by
  apply branch_left_normalized (c:=vp011011001010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3475761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3475761639/2000000 : ℚ) by norm_num]
  exact coverp011011001010
private noncomputable def ep011011001011_0 : Blocks := edgeBlocks% "full/vectors/011011001011-E-0000.bin"
noncomputable def ep011011001011 : Blocks := ep011011001011_0
private theorem idp011011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101100101.list =
    C ((2:ℤ)^101) * horner X vp011011001011.list + horner X ep011011001011.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011001011 : Branch 1 (-3475761639/4000000 : ℚ) vp01101100101 := by
  apply branch_checked idp011011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3475761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3477761639/2000000 : ℚ) by norm_num]
  exact coverp011011001011
theorem coverp01101100101 : Covers (-3475761639/4000000 : ℚ) vp01101100101 := join_branches bp011011001010 bp011011001011
private noncomputable def vp011011001001_0 : Blocks := edgeBlocks% "full/vectors/011011001001-V-0000.bin"
noncomputable def vp011011001001 : Blocks := vp011011001001_0
theorem coverp011011001001 : Covers (-3473761639/2000000 : ℚ) vp011011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp011011001000_0 : Blocks := edgeBlocks% "full/vectors/011011001000-V-0000.bin"
noncomputable def vp011011001000 : Blocks := vp011011001000_0
theorem coverp011011001000 : Covers (-3471761639/2000000 : ℚ) vp011011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp01101100100_0 : Blocks := edgeBlocks% "full/vectors/01101100100-V-0000.bin"
noncomputable def vp01101100100 : Blocks := vp01101100100_0
private theorem bp011011001000 : Branch 0 (-3471761639/4000000 : ℚ) vp01101100100 := by
  apply branch_left_normalized (c:=vp011011001000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3471761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3471761639/2000000 : ℚ) by norm_num]
  exact coverp011011001000
private noncomputable def ep011011001001_0 : Blocks := edgeBlocks% "full/vectors/011011001001-E-0000.bin"
noncomputable def ep011011001001 : Blocks := ep011011001001_0
private theorem idp011011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101100100.list =
    C ((2:ℤ)^101) * horner X vp011011001001.list + horner X ep011011001001.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011001001 : Branch 1 (-3471761639/4000000 : ℚ) vp01101100100 := by
  apply branch_checked idp011011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3471761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3473761639/2000000 : ℚ) by norm_num]
  exact coverp011011001001
theorem coverp01101100100 : Covers (-3471761639/4000000 : ℚ) vp01101100100 := join_branches bp011011001000 bp011011001001
private noncomputable def vp0110110010_0 : Blocks := edgeBlocks% "full/vectors/0110110010-V-0000.bin"
private noncomputable def vp0110110010_1 : Blocks := edgeBlocks% "full/vectors/0110110010-V-0001.bin"
noncomputable def vp0110110010 : Blocks := (Blocks.join vp0110110010_0 vp0110110010_1)
private theorem bp01101100100 : Branch 0 (-3471761639/8000000 : ℚ) vp0110110010 := by
  apply branch_left_normalized (c:=vp01101100100) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3471761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3471761639/4000000 : ℚ) by norm_num]
  exact coverp01101100100
private noncomputable def ep01101100101_0 : Blocks := edgeBlocks% "full/vectors/01101100101-E-0000.bin"
private noncomputable def ep01101100101_1 : Blocks := edgeBlocks% "full/vectors/01101100101-E-0001.bin"
noncomputable def ep01101100101 : Blocks := (Blocks.join ep01101100101_0 ep01101100101_1)
private theorem idp01101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110110010.list =
    C ((2:ℤ)^179) * horner X vp01101100101.list + horner X ep01101100101.list := by
  exact edge_identity (B := (2:ℤ)^328) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101100101 : Branch 1 (-3471761639/8000000 : ℚ) vp0110110010 := by
  apply branch_checked idp01101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3471761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3475761639/4000000 : ℚ) by norm_num]
  exact coverp01101100101
theorem coverp0110110010 : Covers (-3471761639/8000000 : ℚ) vp0110110010 := join_branches bp01101100100 bp01101100101
private noncomputable def vp011011001_0 : Blocks := edgeBlocks% "full/vectors/011011001-V-0000.bin"
private noncomputable def vp011011001_1 : Blocks := edgeBlocks% "full/vectors/011011001-V-0001.bin"
private noncomputable def vp011011001_2 : Blocks := edgeBlocks% "full/vectors/011011001-V-0002.bin"
noncomputable def vp011011001 : Blocks := (Blocks.join vp011011001_0 (Blocks.join vp011011001_1 vp011011001_2))
private theorem bp0110110010 : Branch 0 (-3471761639/16000000 : ℚ) vp011011001 := by
  apply branch_left_normalized (c:=vp0110110010) (k:=0) (m:=155) (by decide +kernel)
  rw [show 2*(-3471761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3471761639/8000000 : ℚ) by norm_num]
  exact coverp0110110010
private noncomputable def ep0110110011_0 : Blocks := edgeBlocks% "full/vectors/0110110011-E-0000.bin"
private noncomputable def ep0110110011_1 : Blocks := edgeBlocks% "full/vectors/0110110011-E-0001.bin"
private noncomputable def ep0110110011_2 : Blocks := edgeBlocks% "full/vectors/0110110011-E-0002.bin"
noncomputable def ep0110110011 : Blocks := (Blocks.join ep0110110011_0 (Blocks.join ep0110110011_1 ep0110110011_2))
private theorem idp0110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011011001.list =
    C ((2:ℤ)^336) * horner X vp0110110011.list + horner X ep0110110011.list := by
  exact edge_identity (B := (2:ℤ)^533) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110110011 : Branch 1 (-3471761639/16000000 : ℚ) vp011011001 := by
  apply branch_checked idp0110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3471761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3479761639/8000000 : ℚ) by norm_num]
  exact coverp0110110011
theorem coverp011011001 : Covers (-3471761639/16000000 : ℚ) vp011011001 := join_branches bp0110110010 bp0110110011
private noncomputable def vp011011000111_0 : Blocks := edgeBlocks% "full/vectors/011011000111-V-0000.bin"
noncomputable def vp011011000111 : Blocks := vp011011000111_0
theorem coverp011011000111 : Covers (-3469761639/2000000 : ℚ) vp011011000111 := cover_leaf (by decide +kernel)
private noncomputable def vp011011000110_0 : Blocks := edgeBlocks% "full/vectors/011011000110-V-0000.bin"
noncomputable def vp011011000110 : Blocks := vp011011000110_0
theorem coverp011011000110 : Covers (-3467761639/2000000 : ℚ) vp011011000110 := cover_leaf (by decide +kernel)
private noncomputable def vp01101100011_0 : Blocks := edgeBlocks% "full/vectors/01101100011-V-0000.bin"
noncomputable def vp01101100011 : Blocks := vp01101100011_0
private theorem bp011011000110 : Branch 0 (-3467761639/4000000 : ℚ) vp01101100011 := by
  apply branch_left_normalized (c:=vp011011000110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3467761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3467761639/2000000 : ℚ) by norm_num]
  exact coverp011011000110
private noncomputable def ep011011000111_0 : Blocks := edgeBlocks% "full/vectors/011011000111-E-0000.bin"
noncomputable def ep011011000111 : Blocks := ep011011000111_0
private theorem idp011011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101100011.list =
    C ((2:ℤ)^100) * horner X vp011011000111.list + horner X ep011011000111.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011000111 : Branch 1 (-3467761639/4000000 : ℚ) vp01101100011 := by
  apply branch_checked idp011011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3467761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3469761639/2000000 : ℚ) by norm_num]
  exact coverp011011000111
theorem coverp01101100011 : Covers (-3467761639/4000000 : ℚ) vp01101100011 := join_branches bp011011000110 bp011011000111
private noncomputable def vp011011000101_0 : Blocks := edgeBlocks% "full/vectors/011011000101-V-0000.bin"
noncomputable def vp011011000101 : Blocks := vp011011000101_0
theorem coverp011011000101 : Covers (-3465761639/2000000 : ℚ) vp011011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp011011000100_0 : Blocks := edgeBlocks% "full/vectors/011011000100-V-0000.bin"
noncomputable def vp011011000100 : Blocks := vp011011000100_0
theorem coverp011011000100 : Covers (-3463761639/2000000 : ℚ) vp011011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp01101100010_0 : Blocks := edgeBlocks% "full/vectors/01101100010-V-0000.bin"
noncomputable def vp01101100010 : Blocks := vp01101100010_0
private theorem bp011011000100 : Branch 0 (-3463761639/4000000 : ℚ) vp01101100010 := by
  apply branch_left_normalized (c:=vp011011000100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3463761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3463761639/2000000 : ℚ) by norm_num]
  exact coverp011011000100
private noncomputable def ep011011000101_0 : Blocks := edgeBlocks% "full/vectors/011011000101-E-0000.bin"
noncomputable def ep011011000101 : Blocks := ep011011000101_0
private theorem idp011011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101100010.list =
    C ((2:ℤ)^100) * horner X vp011011000101.list + horner X ep011011000101.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011000101 : Branch 1 (-3463761639/4000000 : ℚ) vp01101100010 := by
  apply branch_checked idp011011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3463761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3465761639/2000000 : ℚ) by norm_num]
  exact coverp011011000101
theorem coverp01101100010 : Covers (-3463761639/4000000 : ℚ) vp01101100010 := join_branches bp011011000100 bp011011000101
private noncomputable def vp0110110001_0 : Blocks := edgeBlocks% "full/vectors/0110110001-V-0000.bin"
private noncomputable def vp0110110001_1 : Blocks := edgeBlocks% "full/vectors/0110110001-V-0001.bin"
noncomputable def vp0110110001 : Blocks := (Blocks.join vp0110110001_0 vp0110110001_1)
private theorem bp01101100010 : Branch 0 (-3463761639/8000000 : ℚ) vp0110110001 := by
  apply branch_left_normalized (c:=vp01101100010) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3463761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3463761639/4000000 : ℚ) by norm_num]
  exact coverp01101100010
private noncomputable def ep01101100011_0 : Blocks := edgeBlocks% "full/vectors/01101100011-E-0000.bin"
private noncomputable def ep01101100011_1 : Blocks := edgeBlocks% "full/vectors/01101100011-E-0001.bin"
noncomputable def ep01101100011 : Blocks := (Blocks.join ep01101100011_0 ep01101100011_1)
private theorem idp01101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110110001.list =
    C ((2:ℤ)^179) * horner X vp01101100011.list + horner X ep01101100011.list := by
  exact edge_identity (B := (2:ℤ)^328) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101100011 : Branch 1 (-3463761639/8000000 : ℚ) vp0110110001 := by
  apply branch_checked idp01101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-3463761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3467761639/4000000 : ℚ) by norm_num]
  exact coverp01101100011
theorem coverp0110110001 : Covers (-3463761639/8000000 : ℚ) vp0110110001 := join_branches bp01101100010 bp01101100011
private noncomputable def vp011011000011_0 : Blocks := edgeBlocks% "full/vectors/011011000011-V-0000.bin"
noncomputable def vp011011000011 : Blocks := vp011011000011_0
theorem coverp011011000011 : Covers (-3461761639/2000000 : ℚ) vp011011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp011011000010_0 : Blocks := edgeBlocks% "full/vectors/011011000010-V-0000.bin"
noncomputable def vp011011000010 : Blocks := vp011011000010_0
theorem coverp011011000010 : Covers (-3459761639/2000000 : ℚ) vp011011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp01101100001_0 : Blocks := edgeBlocks% "full/vectors/01101100001-V-0000.bin"
noncomputable def vp01101100001 : Blocks := vp01101100001_0
private theorem bp011011000010 : Branch 0 (-3459761639/4000000 : ℚ) vp01101100001 := by
  apply branch_left_normalized (c:=vp011011000010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3459761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3459761639/2000000 : ℚ) by norm_num]
  exact coverp011011000010
private noncomputable def ep011011000011_0 : Blocks := edgeBlocks% "full/vectors/011011000011-E-0000.bin"
noncomputable def ep011011000011 : Blocks := ep011011000011_0
private theorem idp011011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101100001.list =
    C ((2:ℤ)^100) * horner X vp011011000011.list + horner X ep011011000011.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011000011 : Branch 1 (-3459761639/4000000 : ℚ) vp01101100001 := by
  apply branch_checked idp011011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3459761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3461761639/2000000 : ℚ) by norm_num]
  exact coverp011011000011
theorem coverp01101100001 : Covers (-3459761639/4000000 : ℚ) vp01101100001 := join_branches bp011011000010 bp011011000011
private noncomputable def vp011011000001_0 : Blocks := edgeBlocks% "full/vectors/011011000001-V-0000.bin"
noncomputable def vp011011000001 : Blocks := vp011011000001_0
theorem coverp011011000001 : Covers (-3457761639/2000000 : ℚ) vp011011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp011011000000_0 : Blocks := edgeBlocks% "full/vectors/011011000000-V-0000.bin"
noncomputable def vp011011000000 : Blocks := vp011011000000_0
theorem coverp011011000000 : Covers (-3455761639/2000000 : ℚ) vp011011000000 := cover_leaf (by decide +kernel)
private noncomputable def vp01101100000_0 : Blocks := edgeBlocks% "full/vectors/01101100000-V-0000.bin"
noncomputable def vp01101100000 : Blocks := vp01101100000_0
private theorem bp011011000000 : Branch 0 (-3455761639/4000000 : ℚ) vp01101100000 := by
  apply branch_left_normalized (c:=vp011011000000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3455761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3455761639/2000000 : ℚ) by norm_num]
  exact coverp011011000000
private noncomputable def ep011011000001_0 : Blocks := edgeBlocks% "full/vectors/011011000001-E-0000.bin"
noncomputable def ep011011000001 : Blocks := ep011011000001_0
private theorem idp011011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101100000.list =
    C ((2:ℤ)^100) * horner X vp011011000001.list + horner X ep011011000001.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011000001 : Branch 1 (-3455761639/4000000 : ℚ) vp01101100000 := by
  apply branch_checked idp011011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3455761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3457761639/2000000 : ℚ) by norm_num]
  exact coverp011011000001
theorem coverp01101100000 : Covers (-3455761639/4000000 : ℚ) vp01101100000 := join_branches bp011011000000 bp011011000001
private noncomputable def vp0110110000_0 : Blocks := edgeBlocks% "full/vectors/0110110000-V-0000.bin"
private noncomputable def vp0110110000_1 : Blocks := edgeBlocks% "full/vectors/0110110000-V-0001.bin"
noncomputable def vp0110110000 : Blocks := (Blocks.join vp0110110000_0 vp0110110000_1)
private theorem bp01101100000 : Branch 0 (-3455761639/8000000 : ℚ) vp0110110000 := by
  apply branch_left_normalized (c:=vp01101100000) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-3455761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3455761639/4000000 : ℚ) by norm_num]
  exact coverp01101100000
private noncomputable def ep01101100001_0 : Blocks := edgeBlocks% "full/vectors/01101100001-E-0000.bin"
private noncomputable def ep01101100001_1 : Blocks := edgeBlocks% "full/vectors/01101100001-E-0001.bin"
noncomputable def ep01101100001 : Blocks := (Blocks.join ep01101100001_0 ep01101100001_1)
private theorem idp01101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110110000.list =
    C ((2:ℤ)^180) * horner X vp01101100001.list + horner X ep01101100001.list := by
  exact edge_identity (B := (2:ℤ)^329) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101100001 : Branch 1 (-3455761639/8000000 : ℚ) vp0110110000 := by
  apply branch_checked idp01101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3455761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3459761639/4000000 : ℚ) by norm_num]
  exact coverp01101100001
theorem coverp0110110000 : Covers (-3455761639/8000000 : ℚ) vp0110110000 := join_branches bp01101100000 bp01101100001
private noncomputable def vp011011000_0 : Blocks := edgeBlocks% "full/vectors/011011000-V-0000.bin"
private noncomputable def vp011011000_1 : Blocks := edgeBlocks% "full/vectors/011011000-V-0001.bin"
private noncomputable def vp011011000_2 : Blocks := edgeBlocks% "full/vectors/011011000-V-0002.bin"
noncomputable def vp011011000 : Blocks := (Blocks.join vp011011000_0 (Blocks.join vp011011000_1 vp011011000_2))
private theorem bp0110110000 : Branch 0 (-3455761639/16000000 : ℚ) vp011011000 := by
  apply branch_left_normalized (c:=vp0110110000) (k:=0) (m:=156) (by decide +kernel)
  rw [show 2*(-3455761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3455761639/8000000 : ℚ) by norm_num]
  exact coverp0110110000
private noncomputable def ep0110110001_0 : Blocks := edgeBlocks% "full/vectors/0110110001-E-0000.bin"
private noncomputable def ep0110110001_1 : Blocks := edgeBlocks% "full/vectors/0110110001-E-0001.bin"
private noncomputable def ep0110110001_2 : Blocks := edgeBlocks% "full/vectors/0110110001-E-0002.bin"
noncomputable def ep0110110001 : Blocks := (Blocks.join ep0110110001_0 (Blocks.join ep0110110001_1 ep0110110001_2))
private theorem idp0110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011011000.list =
    C ((2:ℤ)^335) * horner X vp0110110001.list + horner X ep0110110001.list := by
  exact edge_identity (B := (2:ℤ)^532) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110110001 : Branch 1 (-3455761639/16000000 : ℚ) vp011011000 := by
  apply branch_checked idp0110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3455761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3463761639/8000000 : ℚ) by norm_num]
  exact coverp0110110001
theorem coverp011011000 : Covers (-3455761639/16000000 : ℚ) vp011011000 := join_branches bp0110110000 bp0110110001
private noncomputable def vp01101100_0 : Blocks := edgeBlocks% "full/vectors/01101100-V-0000.bin"
private noncomputable def vp01101100_1 : Blocks := edgeBlocks% "full/vectors/01101100-V-0001.bin"
private noncomputable def vp01101100_2 : Blocks := edgeBlocks% "full/vectors/01101100-V-0002.bin"
private noncomputable def vp01101100_3 : Blocks := edgeBlocks% "full/vectors/01101100-V-0003.bin"
private noncomputable def vp01101100_4 : Blocks := edgeBlocks% "full/vectors/01101100-V-0004.bin"
noncomputable def vp01101100 : Blocks := (Blocks.join (Blocks.join vp01101100_0 vp01101100_1) (Blocks.join vp01101100_2 (Blocks.join vp01101100_3 vp01101100_4)))
private theorem bp011011000 : Branch 0 (-3455761639/32000000 : ℚ) vp01101100 := by
  apply branch_left_normalized (c:=vp011011000) (k:=0) (m:=288) (by decide +kernel)
  rw [show 2*(-3455761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3455761639/16000000 : ℚ) by norm_num]
  exact coverp011011000
private noncomputable def ep011011001_0 : Blocks := edgeBlocks% "full/vectors/011011001-E-0000.bin"
private noncomputable def ep011011001_1 : Blocks := edgeBlocks% "full/vectors/011011001-E-0001.bin"
private noncomputable def ep011011001_2 : Blocks := edgeBlocks% "full/vectors/011011001-E-0002.bin"
private noncomputable def ep011011001_3 : Blocks := edgeBlocks% "full/vectors/011011001-E-0003.bin"
private noncomputable def ep011011001_4 : Blocks := edgeBlocks% "full/vectors/011011001-E-0004.bin"
noncomputable def ep011011001 : Blocks := (Blocks.join (Blocks.join ep011011001_0 ep011011001_1) (Blocks.join ep011011001_2 (Blocks.join ep011011001_3 ep011011001_4)))
private theorem idp011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01101100.list =
    C ((2:ℤ)^646) * horner X vp011011001.list + horner X ep011011001.list := by
  exact edge_identity (B := (2:ℤ)^938) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011011001 : Branch 1 (-3455761639/32000000 : ℚ) vp01101100 := by
  apply branch_checked idp011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3455761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3471761639/16000000 : ℚ) by norm_num]
  exact coverp011011001
theorem coverp01101100 : Covers (-3455761639/32000000 : ℚ) vp01101100 := join_branches bp011011000 bp011011001
private noncomputable def vp0110110_0 : Blocks := edgeBlocks% "full/vectors/0110110-V-0000.bin"
private noncomputable def vp0110110_1 : Blocks := edgeBlocks% "full/vectors/0110110-V-0001.bin"
private noncomputable def vp0110110_2 : Blocks := edgeBlocks% "full/vectors/0110110-V-0002.bin"
private noncomputable def vp0110110_3 : Blocks := edgeBlocks% "full/vectors/0110110-V-0003.bin"
private noncomputable def vp0110110_4 : Blocks := edgeBlocks% "full/vectors/0110110-V-0004.bin"
private noncomputable def vp0110110_5 : Blocks := edgeBlocks% "full/vectors/0110110-V-0005.bin"
private noncomputable def vp0110110_6 : Blocks := edgeBlocks% "full/vectors/0110110-V-0006.bin"
private noncomputable def vp0110110_7 : Blocks := edgeBlocks% "full/vectors/0110110-V-0007.bin"
private noncomputable def vp0110110_8 : Blocks := edgeBlocks% "full/vectors/0110110-V-0008.bin"
noncomputable def vp0110110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0110110_0 vp0110110_1) (Blocks.join vp0110110_2 vp0110110_3)) (Blocks.join (Blocks.join vp0110110_4 vp0110110_5) (Blocks.join vp0110110_6 (Blocks.join vp0110110_7 vp0110110_8))))
private theorem bp01101100 : Branch 0 (-3455761639/64000000 : ℚ) vp0110110 := by
  apply branch_left_normalized (c:=vp01101100) (k:=0) (m:=553) (by decide +kernel)
  rw [show 2*(-3455761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3455761639/32000000 : ℚ) by norm_num]
  exact coverp01101100
private noncomputable def ep01101101_0 : Blocks := edgeBlocks% "full/vectors/01101101-E-0000.bin"
private noncomputable def ep01101101_1 : Blocks := edgeBlocks% "full/vectors/01101101-E-0001.bin"
private noncomputable def ep01101101_2 : Blocks := edgeBlocks% "full/vectors/01101101-E-0002.bin"
private noncomputable def ep01101101_3 : Blocks := edgeBlocks% "full/vectors/01101101-E-0003.bin"
private noncomputable def ep01101101_4 : Blocks := edgeBlocks% "full/vectors/01101101-E-0004.bin"
private noncomputable def ep01101101_5 : Blocks := edgeBlocks% "full/vectors/01101101-E-0005.bin"
private noncomputable def ep01101101_6 : Blocks := edgeBlocks% "full/vectors/01101101-E-0006.bin"
private noncomputable def ep01101101_7 : Blocks := edgeBlocks% "full/vectors/01101101-E-0007.bin"
private noncomputable def ep01101101_8 : Blocks := edgeBlocks% "full/vectors/01101101-E-0008.bin"
noncomputable def ep01101101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01101101_0 ep01101101_1) (Blocks.join ep01101101_2 ep01101101_3)) (Blocks.join (Blocks.join ep01101101_4 ep01101101_5) (Blocks.join ep01101101_6 (Blocks.join ep01101101_7 ep01101101_8))))
private theorem idp01101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0110110.list =
    C ((2:ℤ)^1261) * horner X vp01101101.list + horner X ep01101101.list := by
  exact edge_identity (B := (2:ℤ)^1743) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01101101 : Branch 1 (-3455761639/64000000 : ℚ) vp0110110 := by
  apply branch_checked idp01101101 (by positivity) (by decide +kernel)
  rw [show 2*(-3455761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3487761639/32000000 : ℚ) by norm_num]
  exact coverp01101101
theorem coverp0110110 : Covers (-3455761639/64000000 : ℚ) vp0110110 := join_branches bp01101100 bp01101101
private noncomputable def vp011011_0 : Blocks := edgeBlocks% "full/vectors/011011-V-0000.bin"
private noncomputable def vp011011_1 : Blocks := edgeBlocks% "full/vectors/011011-V-0001.bin"
private noncomputable def vp011011_2 : Blocks := edgeBlocks% "full/vectors/011011-V-0002.bin"
private noncomputable def vp011011_3 : Blocks := edgeBlocks% "full/vectors/011011-V-0003.bin"
private noncomputable def vp011011_4 : Blocks := edgeBlocks% "full/vectors/011011-V-0004.bin"
private noncomputable def vp011011_5 : Blocks := edgeBlocks% "full/vectors/011011-V-0005.bin"
private noncomputable def vp011011_6 : Blocks := edgeBlocks% "full/vectors/011011-V-0006.bin"
private noncomputable def vp011011_7 : Blocks := edgeBlocks% "full/vectors/011011-V-0007.bin"
private noncomputable def vp011011_8 : Blocks := edgeBlocks% "full/vectors/011011-V-0008.bin"
private noncomputable def vp011011_9 : Blocks := edgeBlocks% "full/vectors/011011-V-0009.bin"
private noncomputable def vp011011_10 : Blocks := edgeBlocks% "full/vectors/011011-V-0010.bin"
private noncomputable def vp011011_11 : Blocks := edgeBlocks% "full/vectors/011011-V-0011.bin"
private noncomputable def vp011011_12 : Blocks := edgeBlocks% "full/vectors/011011-V-0012.bin"
private noncomputable def vp011011_13 : Blocks := edgeBlocks% "full/vectors/011011-V-0013.bin"
private noncomputable def vp011011_14 : Blocks := edgeBlocks% "full/vectors/011011-V-0014.bin"
private noncomputable def vp011011_15 : Blocks := edgeBlocks% "full/vectors/011011-V-0015.bin"
private noncomputable def vp011011_16 : Blocks := edgeBlocks% "full/vectors/011011-V-0016.bin"
noncomputable def vp011011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp011011_0 vp011011_1) (Blocks.join vp011011_2 vp011011_3)) (Blocks.join (Blocks.join vp011011_4 vp011011_5) (Blocks.join vp011011_6 vp011011_7))) (Blocks.join (Blocks.join (Blocks.join vp011011_8 vp011011_9) (Blocks.join vp011011_10 vp011011_11)) (Blocks.join (Blocks.join vp011011_12 vp011011_13) (Blocks.join vp011011_14 (Blocks.join vp011011_15 vp011011_16)))))
private theorem bp0110110 : Branch 0 (-3455761639/128000000 : ℚ) vp011011 := by
  apply branch_left_normalized (c:=vp0110110) (k:=0) (m:=1076) (by decide +kernel)
  rw [show 2*(-3455761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-3455761639/64000000 : ℚ) by norm_num]
  exact coverp0110110
private noncomputable def ep0110111_0 : Blocks := edgeBlocks% "full/vectors/0110111-E-0000.bin"
private noncomputable def ep0110111_1 : Blocks := edgeBlocks% "full/vectors/0110111-E-0001.bin"
private noncomputable def ep0110111_2 : Blocks := edgeBlocks% "full/vectors/0110111-E-0002.bin"
private noncomputable def ep0110111_3 : Blocks := edgeBlocks% "full/vectors/0110111-E-0003.bin"
private noncomputable def ep0110111_4 : Blocks := edgeBlocks% "full/vectors/0110111-E-0004.bin"
private noncomputable def ep0110111_5 : Blocks := edgeBlocks% "full/vectors/0110111-E-0005.bin"
private noncomputable def ep0110111_6 : Blocks := edgeBlocks% "full/vectors/0110111-E-0006.bin"
private noncomputable def ep0110111_7 : Blocks := edgeBlocks% "full/vectors/0110111-E-0007.bin"
private noncomputable def ep0110111_8 : Blocks := edgeBlocks% "full/vectors/0110111-E-0008.bin"
private noncomputable def ep0110111_9 : Blocks := edgeBlocks% "full/vectors/0110111-E-0009.bin"
private noncomputable def ep0110111_10 : Blocks := edgeBlocks% "full/vectors/0110111-E-0010.bin"
private noncomputable def ep0110111_11 : Blocks := edgeBlocks% "full/vectors/0110111-E-0011.bin"
private noncomputable def ep0110111_12 : Blocks := edgeBlocks% "full/vectors/0110111-E-0012.bin"
private noncomputable def ep0110111_13 : Blocks := edgeBlocks% "full/vectors/0110111-E-0013.bin"
private noncomputable def ep0110111_14 : Blocks := edgeBlocks% "full/vectors/0110111-E-0014.bin"
private noncomputable def ep0110111_15 : Blocks := edgeBlocks% "full/vectors/0110111-E-0015.bin"
private noncomputable def ep0110111_16 : Blocks := edgeBlocks% "full/vectors/0110111-E-0016.bin"
noncomputable def ep0110111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0110111_0 ep0110111_1) (Blocks.join ep0110111_2 ep0110111_3)) (Blocks.join (Blocks.join ep0110111_4 ep0110111_5) (Blocks.join ep0110111_6 ep0110111_7))) (Blocks.join (Blocks.join (Blocks.join ep0110111_8 ep0110111_9) (Blocks.join ep0110111_10 ep0110111_11)) (Blocks.join (Blocks.join ep0110111_12 ep0110111_13) (Blocks.join ep0110111_14 (Blocks.join ep0110111_15 ep0110111_16)))))
private theorem idp0110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011011.list =
    C ((2:ℤ)^2470) * horner X vp0110111.list + horner X ep0110111.list := by
  exact edge_identity (B := (2:ℤ)^3321) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0110111 : Branch 1 (-3455761639/128000000 : ℚ) vp011011 := by
  apply branch_checked idp0110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3455761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-3519761639/64000000 : ℚ) by norm_num]
  exact coverp0110111
theorem coverp011011 : Covers (-3455761639/128000000 : ℚ) vp011011 := join_branches bp0110110 bp0110111
end NextProof.EdgeFull

