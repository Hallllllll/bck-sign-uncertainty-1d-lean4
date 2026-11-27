import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00126

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp01110111111_0 : Blocks := edgeBlocks% "full/vectors/01110111111-V-0000.bin"
noncomputable def vp01110111111 : Blocks := vp01110111111_0
theorem coverp01110111111 : Covers (-3835761639/4000000 : ℚ) vp01110111111 := cover_leaf (by decide +kernel)
private noncomputable def vp01110111110_0 : Blocks := edgeBlocks% "full/vectors/01110111110-V-0000.bin"
noncomputable def vp01110111110 : Blocks := vp01110111110_0
theorem coverp01110111110 : Covers (-3831761639/4000000 : ℚ) vp01110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111011111_0 : Blocks := edgeBlocks% "full/vectors/0111011111-V-0000.bin"
private noncomputable def vp0111011111_1 : Blocks := edgeBlocks% "full/vectors/0111011111-V-0001.bin"
noncomputable def vp0111011111 : Blocks := (Blocks.join vp0111011111_0 vp0111011111_1)
private theorem bp01110111110 : Branch 0 (-3831761639/8000000 : ℚ) vp0111011111 := by
  apply branch_left_normalized (c:=vp01110111110) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3831761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3831761639/4000000 : ℚ) by norm_num]
  exact coverp01110111110
private noncomputable def ep01110111111_0 : Blocks := edgeBlocks% "full/vectors/01110111111-E-0000.bin"
private noncomputable def ep01110111111_1 : Blocks := edgeBlocks% "full/vectors/01110111111-E-0001.bin"
noncomputable def ep01110111111 : Blocks := (Blocks.join ep01110111111_0 ep01110111111_1)
private theorem idp01110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111011111.list =
    C ((2:ℤ)^174) * horner X vp01110111111.list + horner X ep01110111111.list := by
  exact edge_identity (B := (2:ℤ)^319) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110111111 : Branch 1 (-3831761639/8000000 : ℚ) vp0111011111 := by
  apply branch_checked idp01110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3831761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3835761639/4000000 : ℚ) by norm_num]
  exact coverp01110111111
theorem coverp0111011111 : Covers (-3831761639/8000000 : ℚ) vp0111011111 := join_branches bp01110111110 bp01110111111
private noncomputable def vp01110111101_0 : Blocks := edgeBlocks% "full/vectors/01110111101-V-0000.bin"
noncomputable def vp01110111101 : Blocks := vp01110111101_0
theorem coverp01110111101 : Covers (-3827761639/4000000 : ℚ) vp01110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp01110111100_0 : Blocks := edgeBlocks% "full/vectors/01110111100-V-0000.bin"
noncomputable def vp01110111100 : Blocks := vp01110111100_0
theorem coverp01110111100 : Covers (-3823761639/4000000 : ℚ) vp01110111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111011110_0 : Blocks := edgeBlocks% "full/vectors/0111011110-V-0000.bin"
private noncomputable def vp0111011110_1 : Blocks := edgeBlocks% "full/vectors/0111011110-V-0001.bin"
noncomputable def vp0111011110 : Blocks := (Blocks.join vp0111011110_0 vp0111011110_1)
private theorem bp01110111100 : Branch 0 (-3823761639/8000000 : ℚ) vp0111011110 := by
  apply branch_left_normalized (c:=vp01110111100) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3823761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3823761639/4000000 : ℚ) by norm_num]
  exact coverp01110111100
private noncomputable def ep01110111101_0 : Blocks := edgeBlocks% "full/vectors/01110111101-E-0000.bin"
private noncomputable def ep01110111101_1 : Blocks := edgeBlocks% "full/vectors/01110111101-E-0001.bin"
noncomputable def ep01110111101 : Blocks := (Blocks.join ep01110111101_0 ep01110111101_1)
private theorem idp01110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111011110.list =
    C ((2:ℤ)^173) * horner X vp01110111101.list + horner X ep01110111101.list := by
  exact edge_identity (B := (2:ℤ)^319) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110111101 : Branch 1 (-3823761639/8000000 : ℚ) vp0111011110 := by
  apply branch_checked idp01110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3823761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3827761639/4000000 : ℚ) by norm_num]
  exact coverp01110111101
theorem coverp0111011110 : Covers (-3823761639/8000000 : ℚ) vp0111011110 := join_branches bp01110111100 bp01110111101
private noncomputable def vp011101111_0 : Blocks := edgeBlocks% "full/vectors/011101111-V-0000.bin"
private noncomputable def vp011101111_1 : Blocks := edgeBlocks% "full/vectors/011101111-V-0001.bin"
private noncomputable def vp011101111_2 : Blocks := edgeBlocks% "full/vectors/011101111-V-0002.bin"
noncomputable def vp011101111 : Blocks := (Blocks.join vp011101111_0 (Blocks.join vp011101111_1 vp011101111_2))
private theorem bp0111011110 : Branch 0 (-3823761639/16000000 : ℚ) vp011101111 := by
  apply branch_left_normalized (c:=vp0111011110) (k:=0) (m:=149) (by decide +kernel)
  rw [show 2*(-3823761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3823761639/8000000 : ℚ) by norm_num]
  exact coverp0111011110
private noncomputable def ep0111011111_0 : Blocks := edgeBlocks% "full/vectors/0111011111-E-0000.bin"
private noncomputable def ep0111011111_1 : Blocks := edgeBlocks% "full/vectors/0111011111-E-0001.bin"
private noncomputable def ep0111011111_2 : Blocks := edgeBlocks% "full/vectors/0111011111-E-0002.bin"
noncomputable def ep0111011111 : Blocks := (Blocks.join ep0111011111_0 (Blocks.join ep0111011111_1 ep0111011111_2))
private theorem idp0111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011101111.list =
    C ((2:ℤ)^323) * horner X vp0111011111.list + horner X ep0111011111.list := by
  exact edge_identity (B := (2:ℤ)^513) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111011111 : Branch 1 (-3823761639/16000000 : ℚ) vp011101111 := by
  apply branch_checked idp0111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3823761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3831761639/8000000 : ℚ) by norm_num]
  exact coverp0111011111
theorem coverp011101111 : Covers (-3823761639/16000000 : ℚ) vp011101111 := join_branches bp0111011110 bp0111011111
private noncomputable def vp01110111011_0 : Blocks := edgeBlocks% "full/vectors/01110111011-V-0000.bin"
noncomputable def vp01110111011 : Blocks := vp01110111011_0
theorem coverp01110111011 : Covers (-3819761639/4000000 : ℚ) vp01110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp01110111010_0 : Blocks := edgeBlocks% "full/vectors/01110111010-V-0000.bin"
noncomputable def vp01110111010 : Blocks := vp01110111010_0
theorem coverp01110111010 : Covers (-3815761639/4000000 : ℚ) vp01110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111011101_0 : Blocks := edgeBlocks% "full/vectors/0111011101-V-0000.bin"
private noncomputable def vp0111011101_1 : Blocks := edgeBlocks% "full/vectors/0111011101-V-0001.bin"
noncomputable def vp0111011101 : Blocks := (Blocks.join vp0111011101_0 vp0111011101_1)
private theorem bp01110111010 : Branch 0 (-3815761639/8000000 : ℚ) vp0111011101 := by
  apply branch_left_normalized (c:=vp01110111010) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3815761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3815761639/4000000 : ℚ) by norm_num]
  exact coverp01110111010
private noncomputable def ep01110111011_0 : Blocks := edgeBlocks% "full/vectors/01110111011-E-0000.bin"
private noncomputable def ep01110111011_1 : Blocks := edgeBlocks% "full/vectors/01110111011-E-0001.bin"
noncomputable def ep01110111011 : Blocks := (Blocks.join ep01110111011_0 ep01110111011_1)
private theorem idp01110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111011101.list =
    C ((2:ℤ)^173) * horner X vp01110111011.list + horner X ep01110111011.list := by
  exact edge_identity (B := (2:ℤ)^319) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110111011 : Branch 1 (-3815761639/8000000 : ℚ) vp0111011101 := by
  apply branch_checked idp01110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3815761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3819761639/4000000 : ℚ) by norm_num]
  exact coverp01110111011
theorem coverp0111011101 : Covers (-3815761639/8000000 : ℚ) vp0111011101 := join_branches bp01110111010 bp01110111011
private noncomputable def vp01110111001_0 : Blocks := edgeBlocks% "full/vectors/01110111001-V-0000.bin"
noncomputable def vp01110111001 : Blocks := vp01110111001_0
theorem coverp01110111001 : Covers (-3811761639/4000000 : ℚ) vp01110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp01110111000_0 : Blocks := edgeBlocks% "full/vectors/01110111000-V-0000.bin"
noncomputable def vp01110111000 : Blocks := vp01110111000_0
theorem coverp01110111000 : Covers (-3807761639/4000000 : ℚ) vp01110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111011100_0 : Blocks := edgeBlocks% "full/vectors/0111011100-V-0000.bin"
private noncomputable def vp0111011100_1 : Blocks := edgeBlocks% "full/vectors/0111011100-V-0001.bin"
noncomputable def vp0111011100 : Blocks := (Blocks.join vp0111011100_0 vp0111011100_1)
private theorem bp01110111000 : Branch 0 (-3807761639/8000000 : ℚ) vp0111011100 := by
  apply branch_left_normalized (c:=vp01110111000) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3807761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3807761639/4000000 : ℚ) by norm_num]
  exact coverp01110111000
private noncomputable def ep01110111001_0 : Blocks := edgeBlocks% "full/vectors/01110111001-E-0000.bin"
private noncomputable def ep01110111001_1 : Blocks := edgeBlocks% "full/vectors/01110111001-E-0001.bin"
noncomputable def ep01110111001 : Blocks := (Blocks.join ep01110111001_0 ep01110111001_1)
private theorem idp01110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111011100.list =
    C ((2:ℤ)^173) * horner X vp01110111001.list + horner X ep01110111001.list := by
  exact edge_identity (B := (2:ℤ)^319) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110111001 : Branch 1 (-3807761639/8000000 : ℚ) vp0111011100 := by
  apply branch_checked idp01110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3807761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3811761639/4000000 : ℚ) by norm_num]
  exact coverp01110111001
theorem coverp0111011100 : Covers (-3807761639/8000000 : ℚ) vp0111011100 := join_branches bp01110111000 bp01110111001
private noncomputable def vp011101110_0 : Blocks := edgeBlocks% "full/vectors/011101110-V-0000.bin"
private noncomputable def vp011101110_1 : Blocks := edgeBlocks% "full/vectors/011101110-V-0001.bin"
private noncomputable def vp011101110_2 : Blocks := edgeBlocks% "full/vectors/011101110-V-0002.bin"
noncomputable def vp011101110 : Blocks := (Blocks.join vp011101110_0 (Blocks.join vp011101110_1 vp011101110_2))
private theorem bp0111011100 : Branch 0 (-3807761639/16000000 : ℚ) vp011101110 := by
  apply branch_left_normalized (c:=vp0111011100) (k:=0) (m:=149) (by decide +kernel)
  rw [show 2*(-3807761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3807761639/8000000 : ℚ) by norm_num]
  exact coverp0111011100
private noncomputable def ep0111011101_0 : Blocks := edgeBlocks% "full/vectors/0111011101-E-0000.bin"
private noncomputable def ep0111011101_1 : Blocks := edgeBlocks% "full/vectors/0111011101-E-0001.bin"
private noncomputable def ep0111011101_2 : Blocks := edgeBlocks% "full/vectors/0111011101-E-0002.bin"
noncomputable def ep0111011101 : Blocks := (Blocks.join ep0111011101_0 (Blocks.join ep0111011101_1 ep0111011101_2))
private theorem idp0111011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011101110.list =
    C ((2:ℤ)^324) * horner X vp0111011101.list + horner X ep0111011101.list := by
  exact edge_identity (B := (2:ℤ)^514) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111011101 : Branch 1 (-3807761639/16000000 : ℚ) vp011101110 := by
  apply branch_checked idp0111011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3807761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3815761639/8000000 : ℚ) by norm_num]
  exact coverp0111011101
theorem coverp011101110 : Covers (-3807761639/16000000 : ℚ) vp011101110 := join_branches bp0111011100 bp0111011101
private noncomputable def vp01110111_0 : Blocks := edgeBlocks% "full/vectors/01110111-V-0000.bin"
private noncomputable def vp01110111_1 : Blocks := edgeBlocks% "full/vectors/01110111-V-0001.bin"
private noncomputable def vp01110111_2 : Blocks := edgeBlocks% "full/vectors/01110111-V-0002.bin"
private noncomputable def vp01110111_3 : Blocks := edgeBlocks% "full/vectors/01110111-V-0003.bin"
private noncomputable def vp01110111_4 : Blocks := edgeBlocks% "full/vectors/01110111-V-0004.bin"
noncomputable def vp01110111 : Blocks := (Blocks.join (Blocks.join vp01110111_0 vp01110111_1) (Blocks.join vp01110111_2 (Blocks.join vp01110111_3 vp01110111_4)))
private theorem bp011101110 : Branch 0 (-3807761639/32000000 : ℚ) vp01110111 := by
  apply branch_left_normalized (c:=vp011101110) (k:=0) (m:=277) (by decide +kernel)
  rw [show 2*(-3807761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3807761639/16000000 : ℚ) by norm_num]
  exact coverp011101110
private noncomputable def ep011101111_0 : Blocks := edgeBlocks% "full/vectors/011101111-E-0000.bin"
private noncomputable def ep011101111_1 : Blocks := edgeBlocks% "full/vectors/011101111-E-0001.bin"
private noncomputable def ep011101111_2 : Blocks := edgeBlocks% "full/vectors/011101111-E-0002.bin"
private noncomputable def ep011101111_3 : Blocks := edgeBlocks% "full/vectors/011101111-E-0003.bin"
private noncomputable def ep011101111_4 : Blocks := edgeBlocks% "full/vectors/011101111-E-0004.bin"
noncomputable def ep011101111 : Blocks := (Blocks.join (Blocks.join ep011101111_0 ep011101111_1) (Blocks.join ep011101111_2 (Blocks.join ep011101111_3 ep011101111_4)))
private theorem idp011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110111.list =
    C ((2:ℤ)^622) * horner X vp011101111.list + horner X ep011101111.list := by
  exact edge_identity (B := (2:ℤ)^901) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011101111 : Branch 1 (-3807761639/32000000 : ℚ) vp01110111 := by
  apply branch_checked idp011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3807761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3823761639/16000000 : ℚ) by norm_num]
  exact coverp011101111
theorem coverp01110111 : Covers (-3807761639/32000000 : ℚ) vp01110111 := join_branches bp011101110 bp011101111
private noncomputable def vp01110110111_0 : Blocks := edgeBlocks% "full/vectors/01110110111-V-0000.bin"
noncomputable def vp01110110111 : Blocks := vp01110110111_0
theorem coverp01110110111 : Covers (-3803761639/4000000 : ℚ) vp01110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp01110110110_0 : Blocks := edgeBlocks% "full/vectors/01110110110-V-0000.bin"
noncomputable def vp01110110110 : Blocks := vp01110110110_0
theorem coverp01110110110 : Covers (-3799761639/4000000 : ℚ) vp01110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111011011_0 : Blocks := edgeBlocks% "full/vectors/0111011011-V-0000.bin"
private noncomputable def vp0111011011_1 : Blocks := edgeBlocks% "full/vectors/0111011011-V-0001.bin"
noncomputable def vp0111011011 : Blocks := (Blocks.join vp0111011011_0 vp0111011011_1)
private theorem bp01110110110 : Branch 0 (-3799761639/8000000 : ℚ) vp0111011011 := by
  apply branch_left_normalized (c:=vp01110110110) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3799761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3799761639/4000000 : ℚ) by norm_num]
  exact coverp01110110110
private noncomputable def ep01110110111_0 : Blocks := edgeBlocks% "full/vectors/01110110111-E-0000.bin"
private noncomputable def ep01110110111_1 : Blocks := edgeBlocks% "full/vectors/01110110111-E-0001.bin"
noncomputable def ep01110110111 : Blocks := (Blocks.join ep01110110111_0 ep01110110111_1)
private theorem idp01110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111011011.list =
    C ((2:ℤ)^173) * horner X vp01110110111.list + horner X ep01110110111.list := by
  exact edge_identity (B := (2:ℤ)^319) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110110111 : Branch 1 (-3799761639/8000000 : ℚ) vp0111011011 := by
  apply branch_checked idp01110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3799761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3803761639/4000000 : ℚ) by norm_num]
  exact coverp01110110111
theorem coverp0111011011 : Covers (-3799761639/8000000 : ℚ) vp0111011011 := join_branches bp01110110110 bp01110110111
private noncomputable def vp01110110101_0 : Blocks := edgeBlocks% "full/vectors/01110110101-V-0000.bin"
noncomputable def vp01110110101 : Blocks := vp01110110101_0
theorem coverp01110110101 : Covers (-3795761639/4000000 : ℚ) vp01110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp01110110100_0 : Blocks := edgeBlocks% "full/vectors/01110110100-V-0000.bin"
noncomputable def vp01110110100 : Blocks := vp01110110100_0
theorem coverp01110110100 : Covers (-3791761639/4000000 : ℚ) vp01110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111011010_0 : Blocks := edgeBlocks% "full/vectors/0111011010-V-0000.bin"
private noncomputable def vp0111011010_1 : Blocks := edgeBlocks% "full/vectors/0111011010-V-0001.bin"
noncomputable def vp0111011010 : Blocks := (Blocks.join vp0111011010_0 vp0111011010_1)
private theorem bp01110110100 : Branch 0 (-3791761639/8000000 : ℚ) vp0111011010 := by
  apply branch_left_normalized (c:=vp01110110100) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3791761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3791761639/4000000 : ℚ) by norm_num]
  exact coverp01110110100
private noncomputable def ep01110110101_0 : Blocks := edgeBlocks% "full/vectors/01110110101-E-0000.bin"
private noncomputable def ep01110110101_1 : Blocks := edgeBlocks% "full/vectors/01110110101-E-0001.bin"
noncomputable def ep01110110101 : Blocks := (Blocks.join ep01110110101_0 ep01110110101_1)
private theorem idp01110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111011010.list =
    C ((2:ℤ)^172) * horner X vp01110110101.list + horner X ep01110110101.list := by
  exact edge_identity (B := (2:ℤ)^318) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110110101 : Branch 1 (-3791761639/8000000 : ℚ) vp0111011010 := by
  apply branch_checked idp01110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3791761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3795761639/4000000 : ℚ) by norm_num]
  exact coverp01110110101
theorem coverp0111011010 : Covers (-3791761639/8000000 : ℚ) vp0111011010 := join_branches bp01110110100 bp01110110101
private noncomputable def vp011101101_0 : Blocks := edgeBlocks% "full/vectors/011101101-V-0000.bin"
private noncomputable def vp011101101_1 : Blocks := edgeBlocks% "full/vectors/011101101-V-0001.bin"
private noncomputable def vp011101101_2 : Blocks := edgeBlocks% "full/vectors/011101101-V-0002.bin"
noncomputable def vp011101101 : Blocks := (Blocks.join vp011101101_0 (Blocks.join vp011101101_1 vp011101101_2))
private theorem bp0111011010 : Branch 0 (-3791761639/16000000 : ℚ) vp011101101 := by
  apply branch_left_normalized (c:=vp0111011010) (k:=0) (m:=148) (by decide +kernel)
  rw [show 2*(-3791761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3791761639/8000000 : ℚ) by norm_num]
  exact coverp0111011010
private noncomputable def ep0111011011_0 : Blocks := edgeBlocks% "full/vectors/0111011011-E-0000.bin"
private noncomputable def ep0111011011_1 : Blocks := edgeBlocks% "full/vectors/0111011011-E-0001.bin"
private noncomputable def ep0111011011_2 : Blocks := edgeBlocks% "full/vectors/0111011011-E-0002.bin"
noncomputable def ep0111011011 : Blocks := (Blocks.join ep0111011011_0 (Blocks.join ep0111011011_1 ep0111011011_2))
private theorem idp0111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011101101.list =
    C ((2:ℤ)^324) * horner X vp0111011011.list + horner X ep0111011011.list := by
  exact edge_identity (B := (2:ℤ)^514) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111011011 : Branch 1 (-3791761639/16000000 : ℚ) vp011101101 := by
  apply branch_checked idp0111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3791761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3799761639/8000000 : ℚ) by norm_num]
  exact coverp0111011011
theorem coverp011101101 : Covers (-3791761639/16000000 : ℚ) vp011101101 := join_branches bp0111011010 bp0111011011
private noncomputable def vp01110110011_0 : Blocks := edgeBlocks% "full/vectors/01110110011-V-0000.bin"
noncomputable def vp01110110011 : Blocks := vp01110110011_0
theorem coverp01110110011 : Covers (-3787761639/4000000 : ℚ) vp01110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp01110110010_0 : Blocks := edgeBlocks% "full/vectors/01110110010-V-0000.bin"
noncomputable def vp01110110010 : Blocks := vp01110110010_0
theorem coverp01110110010 : Covers (-3783761639/4000000 : ℚ) vp01110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111011001_0 : Blocks := edgeBlocks% "full/vectors/0111011001-V-0000.bin"
private noncomputable def vp0111011001_1 : Blocks := edgeBlocks% "full/vectors/0111011001-V-0001.bin"
noncomputable def vp0111011001 : Blocks := (Blocks.join vp0111011001_0 vp0111011001_1)
private theorem bp01110110010 : Branch 0 (-3783761639/8000000 : ℚ) vp0111011001 := by
  apply branch_left_normalized (c:=vp01110110010) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3783761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3783761639/4000000 : ℚ) by norm_num]
  exact coverp01110110010
private noncomputable def ep01110110011_0 : Blocks := edgeBlocks% "full/vectors/01110110011-E-0000.bin"
private noncomputable def ep01110110011_1 : Blocks := edgeBlocks% "full/vectors/01110110011-E-0001.bin"
noncomputable def ep01110110011 : Blocks := (Blocks.join ep01110110011_0 ep01110110011_1)
private theorem idp01110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111011001.list =
    C ((2:ℤ)^175) * horner X vp01110110011.list + horner X ep01110110011.list := by
  exact edge_identity (B := (2:ℤ)^321) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110110011 : Branch 1 (-3783761639/8000000 : ℚ) vp0111011001 := by
  apply branch_checked idp01110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3783761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3787761639/4000000 : ℚ) by norm_num]
  exact coverp01110110011
theorem coverp0111011001 : Covers (-3783761639/8000000 : ℚ) vp0111011001 := join_branches bp01110110010 bp01110110011
private noncomputable def vp01110110001_0 : Blocks := edgeBlocks% "full/vectors/01110110001-V-0000.bin"
noncomputable def vp01110110001 : Blocks := vp01110110001_0
theorem coverp01110110001 : Covers (-3779761639/4000000 : ℚ) vp01110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp01110110000_0 : Blocks := edgeBlocks% "full/vectors/01110110000-V-0000.bin"
noncomputable def vp01110110000 : Blocks := vp01110110000_0
theorem coverp01110110000 : Covers (-3775761639/4000000 : ℚ) vp01110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111011000_0 : Blocks := edgeBlocks% "full/vectors/0111011000-V-0000.bin"
private noncomputable def vp0111011000_1 : Blocks := edgeBlocks% "full/vectors/0111011000-V-0001.bin"
noncomputable def vp0111011000 : Blocks := (Blocks.join vp0111011000_0 vp0111011000_1)
private theorem bp01110110000 : Branch 0 (-3775761639/8000000 : ℚ) vp0111011000 := by
  apply branch_left_normalized (c:=vp01110110000) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3775761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3775761639/4000000 : ℚ) by norm_num]
  exact coverp01110110000
private noncomputable def ep01110110001_0 : Blocks := edgeBlocks% "full/vectors/01110110001-E-0000.bin"
private noncomputable def ep01110110001_1 : Blocks := edgeBlocks% "full/vectors/01110110001-E-0001.bin"
noncomputable def ep01110110001 : Blocks := (Blocks.join ep01110110001_0 ep01110110001_1)
private theorem idp01110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111011000.list =
    C ((2:ℤ)^175) * horner X vp01110110001.list + horner X ep01110110001.list := by
  exact edge_identity (B := (2:ℤ)^320) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110110001 : Branch 1 (-3775761639/8000000 : ℚ) vp0111011000 := by
  apply branch_checked idp01110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3775761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3779761639/4000000 : ℚ) by norm_num]
  exact coverp01110110001
theorem coverp0111011000 : Covers (-3775761639/8000000 : ℚ) vp0111011000 := join_branches bp01110110000 bp01110110001
private noncomputable def vp011101100_0 : Blocks := edgeBlocks% "full/vectors/011101100-V-0000.bin"
private noncomputable def vp011101100_1 : Blocks := edgeBlocks% "full/vectors/011101100-V-0001.bin"
private noncomputable def vp011101100_2 : Blocks := edgeBlocks% "full/vectors/011101100-V-0002.bin"
noncomputable def vp011101100 : Blocks := (Blocks.join vp011101100_0 (Blocks.join vp011101100_1 vp011101100_2))
private theorem bp0111011000 : Branch 0 (-3775761639/16000000 : ℚ) vp011101100 := by
  apply branch_left_normalized (c:=vp0111011000) (k:=0) (m:=150) (by decide +kernel)
  rw [show 2*(-3775761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3775761639/8000000 : ℚ) by norm_num]
  exact coverp0111011000
private noncomputable def ep0111011001_0 : Blocks := edgeBlocks% "full/vectors/0111011001-E-0000.bin"
private noncomputable def ep0111011001_1 : Blocks := edgeBlocks% "full/vectors/0111011001-E-0001.bin"
private noncomputable def ep0111011001_2 : Blocks := edgeBlocks% "full/vectors/0111011001-E-0002.bin"
noncomputable def ep0111011001 : Blocks := (Blocks.join ep0111011001_0 (Blocks.join ep0111011001_1 ep0111011001_2))
private theorem idp0111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011101100.list =
    C ((2:ℤ)^324) * horner X vp0111011001.list + horner X ep0111011001.list := by
  exact edge_identity (B := (2:ℤ)^515) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111011001 : Branch 1 (-3775761639/16000000 : ℚ) vp011101100 := by
  apply branch_checked idp0111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3775761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3783761639/8000000 : ℚ) by norm_num]
  exact coverp0111011001
theorem coverp011101100 : Covers (-3775761639/16000000 : ℚ) vp011101100 := join_branches bp0111011000 bp0111011001
private noncomputable def vp01110110_0 : Blocks := edgeBlocks% "full/vectors/01110110-V-0000.bin"
private noncomputable def vp01110110_1 : Blocks := edgeBlocks% "full/vectors/01110110-V-0001.bin"
private noncomputable def vp01110110_2 : Blocks := edgeBlocks% "full/vectors/01110110-V-0002.bin"
private noncomputable def vp01110110_3 : Blocks := edgeBlocks% "full/vectors/01110110-V-0003.bin"
private noncomputable def vp01110110_4 : Blocks := edgeBlocks% "full/vectors/01110110-V-0004.bin"
noncomputable def vp01110110 : Blocks := (Blocks.join (Blocks.join vp01110110_0 vp01110110_1) (Blocks.join vp01110110_2 (Blocks.join vp01110110_3 vp01110110_4)))
private theorem bp011101100 : Branch 0 (-3775761639/32000000 : ℚ) vp01110110 := by
  apply branch_left_normalized (c:=vp011101100) (k:=0) (m:=277) (by decide +kernel)
  rw [show 2*(-3775761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3775761639/16000000 : ℚ) by norm_num]
  exact coverp011101100
private noncomputable def ep011101101_0 : Blocks := edgeBlocks% "full/vectors/011101101-E-0000.bin"
private noncomputable def ep011101101_1 : Blocks := edgeBlocks% "full/vectors/011101101-E-0001.bin"
private noncomputable def ep011101101_2 : Blocks := edgeBlocks% "full/vectors/011101101-E-0002.bin"
private noncomputable def ep011101101_3 : Blocks := edgeBlocks% "full/vectors/011101101-E-0003.bin"
private noncomputable def ep011101101_4 : Blocks := edgeBlocks% "full/vectors/011101101-E-0004.bin"
noncomputable def ep011101101 : Blocks := (Blocks.join (Blocks.join ep011101101_0 ep011101101_1) (Blocks.join ep011101101_2 (Blocks.join ep011101101_3 ep011101101_4)))
private theorem idp011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110110.list =
    C ((2:ℤ)^625) * horner X vp011101101.list + horner X ep011101101.list := by
  exact edge_identity (B := (2:ℤ)^905) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011101101 : Branch 1 (-3775761639/32000000 : ℚ) vp01110110 := by
  apply branch_checked idp011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-3775761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3791761639/16000000 : ℚ) by norm_num]
  exact coverp011101101
theorem coverp01110110 : Covers (-3775761639/32000000 : ℚ) vp01110110 := join_branches bp011101100 bp011101101
private noncomputable def vp0111011_0 : Blocks := edgeBlocks% "full/vectors/0111011-V-0000.bin"
private noncomputable def vp0111011_1 : Blocks := edgeBlocks% "full/vectors/0111011-V-0001.bin"
private noncomputable def vp0111011_2 : Blocks := edgeBlocks% "full/vectors/0111011-V-0002.bin"
private noncomputable def vp0111011_3 : Blocks := edgeBlocks% "full/vectors/0111011-V-0003.bin"
private noncomputable def vp0111011_4 : Blocks := edgeBlocks% "full/vectors/0111011-V-0004.bin"
private noncomputable def vp0111011_5 : Blocks := edgeBlocks% "full/vectors/0111011-V-0005.bin"
private noncomputable def vp0111011_6 : Blocks := edgeBlocks% "full/vectors/0111011-V-0006.bin"
private noncomputable def vp0111011_7 : Blocks := edgeBlocks% "full/vectors/0111011-V-0007.bin"
private noncomputable def vp0111011_8 : Blocks := edgeBlocks% "full/vectors/0111011-V-0008.bin"
noncomputable def vp0111011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0111011_0 vp0111011_1) (Blocks.join vp0111011_2 vp0111011_3)) (Blocks.join (Blocks.join vp0111011_4 vp0111011_5) (Blocks.join vp0111011_6 (Blocks.join vp0111011_7 vp0111011_8))))
private theorem bp01110110 : Branch 0 (-3775761639/64000000 : ℚ) vp0111011 := by
  apply branch_left_normalized (c:=vp01110110) (k:=0) (m:=531) (by decide +kernel)
  rw [show 2*(-3775761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3775761639/32000000 : ℚ) by norm_num]
  exact coverp01110110
private noncomputable def ep01110111_0 : Blocks := edgeBlocks% "full/vectors/01110111-E-0000.bin"
private noncomputable def ep01110111_1 : Blocks := edgeBlocks% "full/vectors/01110111-E-0001.bin"
private noncomputable def ep01110111_2 : Blocks := edgeBlocks% "full/vectors/01110111-E-0002.bin"
private noncomputable def ep01110111_3 : Blocks := edgeBlocks% "full/vectors/01110111-E-0003.bin"
private noncomputable def ep01110111_4 : Blocks := edgeBlocks% "full/vectors/01110111-E-0004.bin"
private noncomputable def ep01110111_5 : Blocks := edgeBlocks% "full/vectors/01110111-E-0005.bin"
private noncomputable def ep01110111_6 : Blocks := edgeBlocks% "full/vectors/01110111-E-0006.bin"
private noncomputable def ep01110111_7 : Blocks := edgeBlocks% "full/vectors/01110111-E-0007.bin"
private noncomputable def ep01110111_8 : Blocks := edgeBlocks% "full/vectors/01110111-E-0008.bin"
noncomputable def ep01110111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01110111_0 ep01110111_1) (Blocks.join ep01110111_2 ep01110111_3)) (Blocks.join (Blocks.join ep01110111_4 ep01110111_5) (Blocks.join ep01110111_6 (Blocks.join ep01110111_7 ep01110111_8))))
private theorem idp01110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111011.list =
    C ((2:ℤ)^1217) * horner X vp01110111.list + horner X ep01110111.list := by
  exact edge_identity (B := (2:ℤ)^1674) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110111 : Branch 1 (-3775761639/64000000 : ℚ) vp0111011 := by
  apply branch_checked idp01110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3775761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3807761639/32000000 : ℚ) by norm_num]
  exact coverp01110111
theorem coverp0111011 : Covers (-3775761639/64000000 : ℚ) vp0111011 := join_branches bp01110110 bp01110111
private noncomputable def vp01110101111_0 : Blocks := edgeBlocks% "full/vectors/01110101111-V-0000.bin"
noncomputable def vp01110101111 : Blocks := vp01110101111_0
theorem coverp01110101111 : Covers (-3771761639/4000000 : ℚ) vp01110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp01110101110_0 : Blocks := edgeBlocks% "full/vectors/01110101110-V-0000.bin"
noncomputable def vp01110101110 : Blocks := vp01110101110_0
theorem coverp01110101110 : Covers (-3767761639/4000000 : ℚ) vp01110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111010111_0 : Blocks := edgeBlocks% "full/vectors/0111010111-V-0000.bin"
private noncomputable def vp0111010111_1 : Blocks := edgeBlocks% "full/vectors/0111010111-V-0001.bin"
noncomputable def vp0111010111 : Blocks := (Blocks.join vp0111010111_0 vp0111010111_1)
private theorem bp01110101110 : Branch 0 (-3767761639/8000000 : ℚ) vp0111010111 := by
  apply branch_left_normalized (c:=vp01110101110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3767761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3767761639/4000000 : ℚ) by norm_num]
  exact coverp01110101110
private noncomputable def ep01110101111_0 : Blocks := edgeBlocks% "full/vectors/01110101111-E-0000.bin"
private noncomputable def ep01110101111_1 : Blocks := edgeBlocks% "full/vectors/01110101111-E-0001.bin"
noncomputable def ep01110101111 : Blocks := (Blocks.join ep01110101111_0 ep01110101111_1)
private theorem idp01110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111010111.list =
    C ((2:ℤ)^170) * horner X vp01110101111.list + horner X ep01110101111.list := by
  exact edge_identity (B := (2:ℤ)^315) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110101111 : Branch 1 (-3767761639/8000000 : ℚ) vp0111010111 := by
  apply branch_checked idp01110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3767761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3771761639/4000000 : ℚ) by norm_num]
  exact coverp01110101111
theorem coverp0111010111 : Covers (-3767761639/8000000 : ℚ) vp0111010111 := join_branches bp01110101110 bp01110101111
private noncomputable def vp01110101101_0 : Blocks := edgeBlocks% "full/vectors/01110101101-V-0000.bin"
noncomputable def vp01110101101 : Blocks := vp01110101101_0
theorem coverp01110101101 : Covers (-3763761639/4000000 : ℚ) vp01110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp01110101100_0 : Blocks := edgeBlocks% "full/vectors/01110101100-V-0000.bin"
noncomputable def vp01110101100 : Blocks := vp01110101100_0
theorem coverp01110101100 : Covers (-3759761639/4000000 : ℚ) vp01110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111010110_0 : Blocks := edgeBlocks% "full/vectors/0111010110-V-0000.bin"
private noncomputable def vp0111010110_1 : Blocks := edgeBlocks% "full/vectors/0111010110-V-0001.bin"
noncomputable def vp0111010110 : Blocks := (Blocks.join vp0111010110_0 vp0111010110_1)
private theorem bp01110101100 : Branch 0 (-3759761639/8000000 : ℚ) vp0111010110 := by
  apply branch_left_normalized (c:=vp01110101100) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-3759761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3759761639/4000000 : ℚ) by norm_num]
  exact coverp01110101100
private noncomputable def ep01110101101_0 : Blocks := edgeBlocks% "full/vectors/01110101101-E-0000.bin"
private noncomputable def ep01110101101_1 : Blocks := edgeBlocks% "full/vectors/01110101101-E-0001.bin"
noncomputable def ep01110101101 : Blocks := (Blocks.join ep01110101101_0 ep01110101101_1)
private theorem idp01110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111010110.list =
    C ((2:ℤ)^169) * horner X vp01110101101.list + horner X ep01110101101.list := by
  exact edge_identity (B := (2:ℤ)^311) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110101101 : Branch 1 (-3759761639/8000000 : ℚ) vp0111010110 := by
  apply branch_checked idp01110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-3759761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3763761639/4000000 : ℚ) by norm_num]
  exact coverp01110101101
theorem coverp0111010110 : Covers (-3759761639/8000000 : ℚ) vp0111010110 := join_branches bp01110101100 bp01110101101
private noncomputable def vp011101011_0 : Blocks := edgeBlocks% "full/vectors/011101011-V-0000.bin"
private noncomputable def vp011101011_1 : Blocks := edgeBlocks% "full/vectors/011101011-V-0001.bin"
private noncomputable def vp011101011_2 : Blocks := edgeBlocks% "full/vectors/011101011-V-0002.bin"
noncomputable def vp011101011 : Blocks := (Blocks.join vp011101011_0 (Blocks.join vp011101011_1 vp011101011_2))
private theorem bp0111010110 : Branch 0 (-3759761639/16000000 : ℚ) vp011101011 := by
  apply branch_left_normalized (c:=vp0111010110) (k:=0) (m:=147) (by decide +kernel)
  rw [show 2*(-3759761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3759761639/8000000 : ℚ) by norm_num]
  exact coverp0111010110
private noncomputable def ep0111010111_0 : Blocks := edgeBlocks% "full/vectors/0111010111-E-0000.bin"
private noncomputable def ep0111010111_1 : Blocks := edgeBlocks% "full/vectors/0111010111-E-0001.bin"
private noncomputable def ep0111010111_2 : Blocks := edgeBlocks% "full/vectors/0111010111-E-0002.bin"
noncomputable def ep0111010111 : Blocks := (Blocks.join ep0111010111_0 (Blocks.join ep0111010111_1 ep0111010111_2))
private theorem idp0111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011101011.list =
    C ((2:ℤ)^318) * horner X vp0111010111.list + horner X ep0111010111.list := by
  exact edge_identity (B := (2:ℤ)^506) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111010111 : Branch 1 (-3759761639/16000000 : ℚ) vp011101011 := by
  apply branch_checked idp0111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-3759761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3767761639/8000000 : ℚ) by norm_num]
  exact coverp0111010111
theorem coverp011101011 : Covers (-3759761639/16000000 : ℚ) vp011101011 := join_branches bp0111010110 bp0111010111
private noncomputable def vp01110101011_0 : Blocks := edgeBlocks% "full/vectors/01110101011-V-0000.bin"
noncomputable def vp01110101011 : Blocks := vp01110101011_0
theorem coverp01110101011 : Covers (-3755761639/4000000 : ℚ) vp01110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp01110101010_0 : Blocks := edgeBlocks% "full/vectors/01110101010-V-0000.bin"
noncomputable def vp01110101010 : Blocks := vp01110101010_0
theorem coverp01110101010 : Covers (-3751761639/4000000 : ℚ) vp01110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111010101_0 : Blocks := edgeBlocks% "full/vectors/0111010101-V-0000.bin"
private noncomputable def vp0111010101_1 : Blocks := edgeBlocks% "full/vectors/0111010101-V-0001.bin"
noncomputable def vp0111010101 : Blocks := (Blocks.join vp0111010101_0 vp0111010101_1)
private theorem bp01110101010 : Branch 0 (-3751761639/8000000 : ℚ) vp0111010101 := by
  apply branch_left_normalized (c:=vp01110101010) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-3751761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3751761639/4000000 : ℚ) by norm_num]
  exact coverp01110101010
private noncomputable def ep01110101011_0 : Blocks := edgeBlocks% "full/vectors/01110101011-E-0000.bin"
private noncomputable def ep01110101011_1 : Blocks := edgeBlocks% "full/vectors/01110101011-E-0001.bin"
noncomputable def ep01110101011 : Blocks := (Blocks.join ep01110101011_0 ep01110101011_1)
private theorem idp01110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111010101.list =
    C ((2:ℤ)^169) * horner X vp01110101011.list + horner X ep01110101011.list := by
  exact edge_identity (B := (2:ℤ)^308) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110101011 : Branch 1 (-3751761639/8000000 : ℚ) vp0111010101 := by
  apply branch_checked idp01110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-3751761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3755761639/4000000 : ℚ) by norm_num]
  exact coverp01110101011
theorem coverp0111010101 : Covers (-3751761639/8000000 : ℚ) vp0111010101 := join_branches bp01110101010 bp01110101011
private noncomputable def vp01110101001_0 : Blocks := edgeBlocks% "full/vectors/01110101001-V-0000.bin"
noncomputable def vp01110101001 : Blocks := vp01110101001_0
theorem coverp01110101001 : Covers (-3747761639/4000000 : ℚ) vp01110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp01110101000_0 : Blocks := edgeBlocks% "full/vectors/01110101000-V-0000.bin"
noncomputable def vp01110101000 : Blocks := vp01110101000_0
theorem coverp01110101000 : Covers (-3743761639/4000000 : ℚ) vp01110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111010100_0 : Blocks := edgeBlocks% "full/vectors/0111010100-V-0000.bin"
private noncomputable def vp0111010100_1 : Blocks := edgeBlocks% "full/vectors/0111010100-V-0001.bin"
noncomputable def vp0111010100 : Blocks := (Blocks.join vp0111010100_0 vp0111010100_1)
private theorem bp01110101000 : Branch 0 (-3743761639/8000000 : ℚ) vp0111010100 := by
  apply branch_left_normalized (c:=vp01110101000) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-3743761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3743761639/4000000 : ℚ) by norm_num]
  exact coverp01110101000
private noncomputable def ep01110101001_0 : Blocks := edgeBlocks% "full/vectors/01110101001-E-0000.bin"
private noncomputable def ep01110101001_1 : Blocks := edgeBlocks% "full/vectors/01110101001-E-0001.bin"
noncomputable def ep01110101001 : Blocks := (Blocks.join ep01110101001_0 ep01110101001_1)
private theorem idp01110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111010100.list =
    C ((2:ℤ)^168) * horner X vp01110101001.list + horner X ep01110101001.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110101001 : Branch 1 (-3743761639/8000000 : ℚ) vp0111010100 := by
  apply branch_checked idp01110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-3743761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3747761639/4000000 : ℚ) by norm_num]
  exact coverp01110101001
theorem coverp0111010100 : Covers (-3743761639/8000000 : ℚ) vp0111010100 := join_branches bp01110101000 bp01110101001
private noncomputable def vp011101010_0 : Blocks := edgeBlocks% "full/vectors/011101010-V-0000.bin"
private noncomputable def vp011101010_1 : Blocks := edgeBlocks% "full/vectors/011101010-V-0001.bin"
private noncomputable def vp011101010_2 : Blocks := edgeBlocks% "full/vectors/011101010-V-0002.bin"
noncomputable def vp011101010 : Blocks := (Blocks.join vp011101010_0 (Blocks.join vp011101010_1 vp011101010_2))
private theorem bp0111010100 : Branch 0 (-3743761639/16000000 : ℚ) vp011101010 := by
  apply branch_left_normalized (c:=vp0111010100) (k:=0) (m:=144) (by decide +kernel)
  rw [show 2*(-3743761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3743761639/8000000 : ℚ) by norm_num]
  exact coverp0111010100
private noncomputable def ep0111010101_0 : Blocks := edgeBlocks% "full/vectors/0111010101-E-0000.bin"
private noncomputable def ep0111010101_1 : Blocks := edgeBlocks% "full/vectors/0111010101-E-0001.bin"
private noncomputable def ep0111010101_2 : Blocks := edgeBlocks% "full/vectors/0111010101-E-0002.bin"
noncomputable def ep0111010101 : Blocks := (Blocks.join ep0111010101_0 (Blocks.join ep0111010101_1 ep0111010101_2))
private theorem idp0111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011101010.list =
    C ((2:ℤ)^320) * horner X vp0111010101.list + horner X ep0111010101.list := by
  exact edge_identity (B := (2:ℤ)^503) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111010101 : Branch 1 (-3743761639/16000000 : ℚ) vp011101010 := by
  apply branch_checked idp0111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-3743761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3751761639/8000000 : ℚ) by norm_num]
  exact coverp0111010101
theorem coverp011101010 : Covers (-3743761639/16000000 : ℚ) vp011101010 := join_branches bp0111010100 bp0111010101
private noncomputable def vp01110101_0 : Blocks := edgeBlocks% "full/vectors/01110101-V-0000.bin"
private noncomputable def vp01110101_1 : Blocks := edgeBlocks% "full/vectors/01110101-V-0001.bin"
private noncomputable def vp01110101_2 : Blocks := edgeBlocks% "full/vectors/01110101-V-0002.bin"
private noncomputable def vp01110101_3 : Blocks := edgeBlocks% "full/vectors/01110101-V-0003.bin"
private noncomputable def vp01110101_4 : Blocks := edgeBlocks% "full/vectors/01110101-V-0004.bin"
noncomputable def vp01110101 : Blocks := (Blocks.join (Blocks.join vp01110101_0 vp01110101_1) (Blocks.join vp01110101_2 (Blocks.join vp01110101_3 vp01110101_4)))
private theorem bp011101010 : Branch 0 (-3743761639/32000000 : ℚ) vp01110101 := by
  apply branch_left_normalized (c:=vp011101010) (k:=0) (m:=273) (by decide +kernel)
  rw [show 2*(-3743761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3743761639/16000000 : ℚ) by norm_num]
  exact coverp011101010
private noncomputable def ep011101011_0 : Blocks := edgeBlocks% "full/vectors/011101011-E-0000.bin"
private noncomputable def ep011101011_1 : Blocks := edgeBlocks% "full/vectors/011101011-E-0001.bin"
private noncomputable def ep011101011_2 : Blocks := edgeBlocks% "full/vectors/011101011-E-0002.bin"
private noncomputable def ep011101011_3 : Blocks := edgeBlocks% "full/vectors/011101011-E-0003.bin"
private noncomputable def ep011101011_4 : Blocks := edgeBlocks% "full/vectors/011101011-E-0004.bin"
noncomputable def ep011101011 : Blocks := (Blocks.join (Blocks.join ep011101011_0 ep011101011_1) (Blocks.join ep011101011_2 (Blocks.join ep011101011_3 ep011101011_4)))
private theorem idp011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110101.list =
    C ((2:ℤ)^618) * horner X vp011101011.list + horner X ep011101011.list := by
  exact edge_identity (B := (2:ℤ)^893) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011101011 : Branch 1 (-3743761639/32000000 : ℚ) vp01110101 := by
  apply branch_checked idp011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-3743761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3759761639/16000000 : ℚ) by norm_num]
  exact coverp011101011
theorem coverp01110101 : Covers (-3743761639/32000000 : ℚ) vp01110101 := join_branches bp011101010 bp011101011
private noncomputable def vp01110100111_0 : Blocks := edgeBlocks% "full/vectors/01110100111-V-0000.bin"
noncomputable def vp01110100111 : Blocks := vp01110100111_0
theorem coverp01110100111 : Covers (-3739761639/4000000 : ℚ) vp01110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp01110100110_0 : Blocks := edgeBlocks% "full/vectors/01110100110-V-0000.bin"
noncomputable def vp01110100110 : Blocks := vp01110100110_0
theorem coverp01110100110 : Covers (-3735761639/4000000 : ℚ) vp01110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111010011_0 : Blocks := edgeBlocks% "full/vectors/0111010011-V-0000.bin"
private noncomputable def vp0111010011_1 : Blocks := edgeBlocks% "full/vectors/0111010011-V-0001.bin"
noncomputable def vp0111010011 : Blocks := (Blocks.join vp0111010011_0 vp0111010011_1)
private theorem bp01110100110 : Branch 0 (-3735761639/8000000 : ℚ) vp0111010011 := by
  apply branch_left_normalized (c:=vp01110100110) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-3735761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3735761639/4000000 : ℚ) by norm_num]
  exact coverp01110100110
private noncomputable def ep01110100111_0 : Blocks := edgeBlocks% "full/vectors/01110100111-E-0000.bin"
private noncomputable def ep01110100111_1 : Blocks := edgeBlocks% "full/vectors/01110100111-E-0001.bin"
noncomputable def ep01110100111 : Blocks := (Blocks.join ep01110100111_0 ep01110100111_1)
private theorem idp01110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111010011.list =
    C ((2:ℤ)^168) * horner X vp01110100111.list + horner X ep01110100111.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110100111 : Branch 1 (-3735761639/8000000 : ℚ) vp0111010011 := by
  apply branch_checked idp01110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3735761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3739761639/4000000 : ℚ) by norm_num]
  exact coverp01110100111
theorem coverp0111010011 : Covers (-3735761639/8000000 : ℚ) vp0111010011 := join_branches bp01110100110 bp01110100111
private noncomputable def vp01110100101_0 : Blocks := edgeBlocks% "full/vectors/01110100101-V-0000.bin"
noncomputable def vp01110100101 : Blocks := vp01110100101_0
theorem coverp01110100101 : Covers (-3731761639/4000000 : ℚ) vp01110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp01110100100_0 : Blocks := edgeBlocks% "full/vectors/01110100100-V-0000.bin"
noncomputable def vp01110100100 : Blocks := vp01110100100_0
theorem coverp01110100100 : Covers (-3727761639/4000000 : ℚ) vp01110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111010010_0 : Blocks := edgeBlocks% "full/vectors/0111010010-V-0000.bin"
private noncomputable def vp0111010010_1 : Blocks := edgeBlocks% "full/vectors/0111010010-V-0001.bin"
noncomputable def vp0111010010 : Blocks := (Blocks.join vp0111010010_0 vp0111010010_1)
private theorem bp01110100100 : Branch 0 (-3727761639/8000000 : ℚ) vp0111010010 := by
  apply branch_left_normalized (c:=vp01110100100) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-3727761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3727761639/4000000 : ℚ) by norm_num]
  exact coverp01110100100
private noncomputable def ep01110100101_0 : Blocks := edgeBlocks% "full/vectors/01110100101-E-0000.bin"
private noncomputable def ep01110100101_1 : Blocks := edgeBlocks% "full/vectors/01110100101-E-0001.bin"
noncomputable def ep01110100101 : Blocks := (Blocks.join ep01110100101_0 ep01110100101_1)
private theorem idp01110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111010010.list =
    C ((2:ℤ)^169) * horner X vp01110100101.list + horner X ep01110100101.list := by
  exact edge_identity (B := (2:ℤ)^307) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110100101 : Branch 1 (-3727761639/8000000 : ℚ) vp0111010010 := by
  apply branch_checked idp01110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3727761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3731761639/4000000 : ℚ) by norm_num]
  exact coverp01110100101
theorem coverp0111010010 : Covers (-3727761639/8000000 : ℚ) vp0111010010 := join_branches bp01110100100 bp01110100101
private noncomputable def vp011101001_0 : Blocks := edgeBlocks% "full/vectors/011101001-V-0000.bin"
private noncomputable def vp011101001_1 : Blocks := edgeBlocks% "full/vectors/011101001-V-0001.bin"
private noncomputable def vp011101001_2 : Blocks := edgeBlocks% "full/vectors/011101001-V-0002.bin"
noncomputable def vp011101001 : Blocks := (Blocks.join vp011101001_0 (Blocks.join vp011101001_1 vp011101001_2))
private theorem bp0111010010 : Branch 0 (-3727761639/16000000 : ℚ) vp011101001 := by
  apply branch_left_normalized (c:=vp0111010010) (k:=0) (m:=145) (by decide +kernel)
  rw [show 2*(-3727761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3727761639/8000000 : ℚ) by norm_num]
  exact coverp0111010010
private noncomputable def ep0111010011_0 : Blocks := edgeBlocks% "full/vectors/0111010011-E-0000.bin"
private noncomputable def ep0111010011_1 : Blocks := edgeBlocks% "full/vectors/0111010011-E-0001.bin"
private noncomputable def ep0111010011_2 : Blocks := edgeBlocks% "full/vectors/0111010011-E-0002.bin"
noncomputable def ep0111010011 : Blocks := (Blocks.join ep0111010011_0 (Blocks.join ep0111010011_1 ep0111010011_2))
private theorem idp0111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011101001.list =
    C ((2:ℤ)^320) * horner X vp0111010011.list + horner X ep0111010011.list := by
  exact edge_identity (B := (2:ℤ)^503) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111010011 : Branch 1 (-3727761639/16000000 : ℚ) vp011101001 := by
  apply branch_checked idp0111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-3727761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3735761639/8000000 : ℚ) by norm_num]
  exact coverp0111010011
theorem coverp011101001 : Covers (-3727761639/16000000 : ℚ) vp011101001 := join_branches bp0111010010 bp0111010011
private noncomputable def vp01110100011_0 : Blocks := edgeBlocks% "full/vectors/01110100011-V-0000.bin"
noncomputable def vp01110100011 : Blocks := vp01110100011_0
theorem coverp01110100011 : Covers (-3723761639/4000000 : ℚ) vp01110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp01110100010_0 : Blocks := edgeBlocks% "full/vectors/01110100010-V-0000.bin"
noncomputable def vp01110100010 : Blocks := vp01110100010_0
theorem coverp01110100010 : Covers (-3719761639/4000000 : ℚ) vp01110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111010001_0 : Blocks := edgeBlocks% "full/vectors/0111010001-V-0000.bin"
private noncomputable def vp0111010001_1 : Blocks := edgeBlocks% "full/vectors/0111010001-V-0001.bin"
noncomputable def vp0111010001 : Blocks := (Blocks.join vp0111010001_0 vp0111010001_1)
private theorem bp01110100010 : Branch 0 (-3719761639/8000000 : ℚ) vp0111010001 := by
  apply branch_left_normalized (c:=vp01110100010) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-3719761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3719761639/4000000 : ℚ) by norm_num]
  exact coverp01110100010
private noncomputable def ep01110100011_0 : Blocks := edgeBlocks% "full/vectors/01110100011-E-0000.bin"
private noncomputable def ep01110100011_1 : Blocks := edgeBlocks% "full/vectors/01110100011-E-0001.bin"
noncomputable def ep01110100011 : Blocks := (Blocks.join ep01110100011_0 ep01110100011_1)
private theorem idp01110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111010001.list =
    C ((2:ℤ)^172) * horner X vp01110100011.list + horner X ep01110100011.list := by
  exact edge_identity (B := (2:ℤ)^311) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110100011 : Branch 1 (-3719761639/8000000 : ℚ) vp0111010001 := by
  apply branch_checked idp01110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-3719761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3723761639/4000000 : ℚ) by norm_num]
  exact coverp01110100011
theorem coverp0111010001 : Covers (-3719761639/8000000 : ℚ) vp0111010001 := join_branches bp01110100010 bp01110100011
private noncomputable def vp01110100001_0 : Blocks := edgeBlocks% "full/vectors/01110100001-V-0000.bin"
noncomputable def vp01110100001 : Blocks := vp01110100001_0
theorem coverp01110100001 : Covers (-3715761639/4000000 : ℚ) vp01110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp01110100000_0 : Blocks := edgeBlocks% "full/vectors/01110100000-V-0000.bin"
noncomputable def vp01110100000 : Blocks := vp01110100000_0
theorem coverp01110100000 : Covers (-3711761639/4000000 : ℚ) vp01110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111010000_0 : Blocks := edgeBlocks% "full/vectors/0111010000-V-0000.bin"
private noncomputable def vp0111010000_1 : Blocks := edgeBlocks% "full/vectors/0111010000-V-0001.bin"
noncomputable def vp0111010000 : Blocks := (Blocks.join vp0111010000_0 vp0111010000_1)
private theorem bp01110100000 : Branch 0 (-3711761639/8000000 : ℚ) vp0111010000 := by
  apply branch_left_normalized (c:=vp01110100000) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3711761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3711761639/4000000 : ℚ) by norm_num]
  exact coverp01110100000
private noncomputable def ep01110100001_0 : Blocks := edgeBlocks% "full/vectors/01110100001-E-0000.bin"
private noncomputable def ep01110100001_1 : Blocks := edgeBlocks% "full/vectors/01110100001-E-0001.bin"
noncomputable def ep01110100001 : Blocks := (Blocks.join ep01110100001_0 ep01110100001_1)
private theorem idp01110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111010000.list =
    C ((2:ℤ)^174) * horner X vp01110100001.list + horner X ep01110100001.list := by
  exact edge_identity (B := (2:ℤ)^315) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110100001 : Branch 1 (-3711761639/8000000 : ℚ) vp0111010000 := by
  apply branch_checked idp01110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3711761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3715761639/4000000 : ℚ) by norm_num]
  exact coverp01110100001
theorem coverp0111010000 : Covers (-3711761639/8000000 : ℚ) vp0111010000 := join_branches bp01110100000 bp01110100001
private noncomputable def vp011101000_0 : Blocks := edgeBlocks% "full/vectors/011101000-V-0000.bin"
private noncomputable def vp011101000_1 : Blocks := edgeBlocks% "full/vectors/011101000-V-0001.bin"
private noncomputable def vp011101000_2 : Blocks := edgeBlocks% "full/vectors/011101000-V-0002.bin"
noncomputable def vp011101000 : Blocks := (Blocks.join vp011101000_0 (Blocks.join vp011101000_1 vp011101000_2))
private theorem bp0111010000 : Branch 0 (-3711761639/16000000 : ℚ) vp011101000 := by
  apply branch_left_normalized (c:=vp0111010000) (k:=0) (m:=148) (by decide +kernel)
  rw [show 2*(-3711761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3711761639/8000000 : ℚ) by norm_num]
  exact coverp0111010000
private noncomputable def ep0111010001_0 : Blocks := edgeBlocks% "full/vectors/0111010001-E-0000.bin"
private noncomputable def ep0111010001_1 : Blocks := edgeBlocks% "full/vectors/0111010001-E-0001.bin"
private noncomputable def ep0111010001_2 : Blocks := edgeBlocks% "full/vectors/0111010001-E-0002.bin"
noncomputable def ep0111010001 : Blocks := (Blocks.join ep0111010001_0 (Blocks.join ep0111010001_1 ep0111010001_2))
private theorem idp0111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011101000.list =
    C ((2:ℤ)^327) * horner X vp0111010001.list + horner X ep0111010001.list := by
  exact edge_identity (B := (2:ℤ)^512) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111010001 : Branch 1 (-3711761639/16000000 : ℚ) vp011101000 := by
  apply branch_checked idp0111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3711761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3719761639/8000000 : ℚ) by norm_num]
  exact coverp0111010001
theorem coverp011101000 : Covers (-3711761639/16000000 : ℚ) vp011101000 := join_branches bp0111010000 bp0111010001
private noncomputable def vp01110100_0 : Blocks := edgeBlocks% "full/vectors/01110100-V-0000.bin"
private noncomputable def vp01110100_1 : Blocks := edgeBlocks% "full/vectors/01110100-V-0001.bin"
private noncomputable def vp01110100_2 : Blocks := edgeBlocks% "full/vectors/01110100-V-0002.bin"
private noncomputable def vp01110100_3 : Blocks := edgeBlocks% "full/vectors/01110100-V-0003.bin"
private noncomputable def vp01110100_4 : Blocks := edgeBlocks% "full/vectors/01110100-V-0004.bin"
noncomputable def vp01110100 : Blocks := (Blocks.join (Blocks.join vp01110100_0 vp01110100_1) (Blocks.join vp01110100_2 (Blocks.join vp01110100_3 vp01110100_4)))
private theorem bp011101000 : Branch 0 (-3711761639/32000000 : ℚ) vp01110100 := by
  apply branch_left_normalized (c:=vp011101000) (k:=0) (m:=277) (by decide +kernel)
  rw [show 2*(-3711761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3711761639/16000000 : ℚ) by norm_num]
  exact coverp011101000
private noncomputable def ep011101001_0 : Blocks := edgeBlocks% "full/vectors/011101001-E-0000.bin"
private noncomputable def ep011101001_1 : Blocks := edgeBlocks% "full/vectors/011101001-E-0001.bin"
private noncomputable def ep011101001_2 : Blocks := edgeBlocks% "full/vectors/011101001-E-0002.bin"
private noncomputable def ep011101001_3 : Blocks := edgeBlocks% "full/vectors/011101001-E-0003.bin"
private noncomputable def ep011101001_4 : Blocks := edgeBlocks% "full/vectors/011101001-E-0004.bin"
noncomputable def ep011101001 : Blocks := (Blocks.join (Blocks.join ep011101001_0 ep011101001_1) (Blocks.join ep011101001_2 (Blocks.join ep011101001_3 ep011101001_4)))
private theorem idp011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110100.list =
    C ((2:ℤ)^631) * horner X vp011101001.list + horner X ep011101001.list := by
  exact edge_identity (B := (2:ℤ)^905) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011101001 : Branch 1 (-3711761639/32000000 : ℚ) vp01110100 := by
  apply branch_checked idp011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-3711761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3727761639/16000000 : ℚ) by norm_num]
  exact coverp011101001
theorem coverp01110100 : Covers (-3711761639/32000000 : ℚ) vp01110100 := join_branches bp011101000 bp011101001
private noncomputable def vp0111010_0 : Blocks := edgeBlocks% "full/vectors/0111010-V-0000.bin"
private noncomputable def vp0111010_1 : Blocks := edgeBlocks% "full/vectors/0111010-V-0001.bin"
private noncomputable def vp0111010_2 : Blocks := edgeBlocks% "full/vectors/0111010-V-0002.bin"
private noncomputable def vp0111010_3 : Blocks := edgeBlocks% "full/vectors/0111010-V-0003.bin"
private noncomputable def vp0111010_4 : Blocks := edgeBlocks% "full/vectors/0111010-V-0004.bin"
private noncomputable def vp0111010_5 : Blocks := edgeBlocks% "full/vectors/0111010-V-0005.bin"
private noncomputable def vp0111010_6 : Blocks := edgeBlocks% "full/vectors/0111010-V-0006.bin"
private noncomputable def vp0111010_7 : Blocks := edgeBlocks% "full/vectors/0111010-V-0007.bin"
private noncomputable def vp0111010_8 : Blocks := edgeBlocks% "full/vectors/0111010-V-0008.bin"
noncomputable def vp0111010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0111010_0 vp0111010_1) (Blocks.join vp0111010_2 vp0111010_3)) (Blocks.join (Blocks.join vp0111010_4 vp0111010_5) (Blocks.join vp0111010_6 (Blocks.join vp0111010_7 vp0111010_8))))
private theorem bp01110100 : Branch 0 (-3711761639/64000000 : ℚ) vp0111010 := by
  apply branch_left_normalized (c:=vp01110100) (k:=0) (m:=533) (by decide +kernel)
  rw [show 2*(-3711761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3711761639/32000000 : ℚ) by norm_num]
  exact coverp01110100
private noncomputable def ep01110101_0 : Blocks := edgeBlocks% "full/vectors/01110101-E-0000.bin"
private noncomputable def ep01110101_1 : Blocks := edgeBlocks% "full/vectors/01110101-E-0001.bin"
private noncomputable def ep01110101_2 : Blocks := edgeBlocks% "full/vectors/01110101-E-0002.bin"
private noncomputable def ep01110101_3 : Blocks := edgeBlocks% "full/vectors/01110101-E-0003.bin"
private noncomputable def ep01110101_4 : Blocks := edgeBlocks% "full/vectors/01110101-E-0004.bin"
private noncomputable def ep01110101_5 : Blocks := edgeBlocks% "full/vectors/01110101-E-0005.bin"
private noncomputable def ep01110101_6 : Blocks := edgeBlocks% "full/vectors/01110101-E-0006.bin"
private noncomputable def ep01110101_7 : Blocks := edgeBlocks% "full/vectors/01110101-E-0007.bin"
private noncomputable def ep01110101_8 : Blocks := edgeBlocks% "full/vectors/01110101-E-0008.bin"
noncomputable def ep01110101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01110101_0 ep01110101_1) (Blocks.join ep01110101_2 ep01110101_3)) (Blocks.join (Blocks.join ep01110101_4 ep01110101_5) (Blocks.join ep01110101_6 (Blocks.join ep01110101_7 ep01110101_8))))
private theorem idp01110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111010.list =
    C ((2:ℤ)^1227) * horner X vp01110101.list + horner X ep01110101.list := by
  exact edge_identity (B := (2:ℤ)^1681) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110101 : Branch 1 (-3711761639/64000000 : ℚ) vp0111010 := by
  apply branch_checked idp01110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3711761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3743761639/32000000 : ℚ) by norm_num]
  exact coverp01110101
theorem coverp0111010 : Covers (-3711761639/64000000 : ℚ) vp0111010 := join_branches bp01110100 bp01110101
private noncomputable def vp011101_0 : Blocks := edgeBlocks% "full/vectors/011101-V-0000.bin"
private noncomputable def vp011101_1 : Blocks := edgeBlocks% "full/vectors/011101-V-0001.bin"
private noncomputable def vp011101_2 : Blocks := edgeBlocks% "full/vectors/011101-V-0002.bin"
private noncomputable def vp011101_3 : Blocks := edgeBlocks% "full/vectors/011101-V-0003.bin"
private noncomputable def vp011101_4 : Blocks := edgeBlocks% "full/vectors/011101-V-0004.bin"
private noncomputable def vp011101_5 : Blocks := edgeBlocks% "full/vectors/011101-V-0005.bin"
private noncomputable def vp011101_6 : Blocks := edgeBlocks% "full/vectors/011101-V-0006.bin"
private noncomputable def vp011101_7 : Blocks := edgeBlocks% "full/vectors/011101-V-0007.bin"
private noncomputable def vp011101_8 : Blocks := edgeBlocks% "full/vectors/011101-V-0008.bin"
private noncomputable def vp011101_9 : Blocks := edgeBlocks% "full/vectors/011101-V-0009.bin"
private noncomputable def vp011101_10 : Blocks := edgeBlocks% "full/vectors/011101-V-0010.bin"
private noncomputable def vp011101_11 : Blocks := edgeBlocks% "full/vectors/011101-V-0011.bin"
private noncomputable def vp011101_12 : Blocks := edgeBlocks% "full/vectors/011101-V-0012.bin"
private noncomputable def vp011101_13 : Blocks := edgeBlocks% "full/vectors/011101-V-0013.bin"
private noncomputable def vp011101_14 : Blocks := edgeBlocks% "full/vectors/011101-V-0014.bin"
private noncomputable def vp011101_15 : Blocks := edgeBlocks% "full/vectors/011101-V-0015.bin"
noncomputable def vp011101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp011101_0 vp011101_1) (Blocks.join vp011101_2 vp011101_3)) (Blocks.join (Blocks.join vp011101_4 vp011101_5) (Blocks.join vp011101_6 vp011101_7))) (Blocks.join (Blocks.join (Blocks.join vp011101_8 vp011101_9) (Blocks.join vp011101_10 vp011101_11)) (Blocks.join (Blocks.join vp011101_12 vp011101_13) (Blocks.join vp011101_14 vp011101_15))))
private theorem bp0111010 : Branch 0 (-3711761639/128000000 : ℚ) vp011101 := by
  apply branch_left_normalized (c:=vp0111010) (k:=0) (m:=1037) (by decide +kernel)
  rw [show 2*(-3711761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-3711761639/64000000 : ℚ) by norm_num]
  exact coverp0111010
private noncomputable def ep0111011_0 : Blocks := edgeBlocks% "full/vectors/0111011-E-0000.bin"
private noncomputable def ep0111011_1 : Blocks := edgeBlocks% "full/vectors/0111011-E-0001.bin"
private noncomputable def ep0111011_2 : Blocks := edgeBlocks% "full/vectors/0111011-E-0002.bin"
private noncomputable def ep0111011_3 : Blocks := edgeBlocks% "full/vectors/0111011-E-0003.bin"
private noncomputable def ep0111011_4 : Blocks := edgeBlocks% "full/vectors/0111011-E-0004.bin"
private noncomputable def ep0111011_5 : Blocks := edgeBlocks% "full/vectors/0111011-E-0005.bin"
private noncomputable def ep0111011_6 : Blocks := edgeBlocks% "full/vectors/0111011-E-0006.bin"
private noncomputable def ep0111011_7 : Blocks := edgeBlocks% "full/vectors/0111011-E-0007.bin"
private noncomputable def ep0111011_8 : Blocks := edgeBlocks% "full/vectors/0111011-E-0008.bin"
private noncomputable def ep0111011_9 : Blocks := edgeBlocks% "full/vectors/0111011-E-0009.bin"
private noncomputable def ep0111011_10 : Blocks := edgeBlocks% "full/vectors/0111011-E-0010.bin"
private noncomputable def ep0111011_11 : Blocks := edgeBlocks% "full/vectors/0111011-E-0011.bin"
private noncomputable def ep0111011_12 : Blocks := edgeBlocks% "full/vectors/0111011-E-0012.bin"
private noncomputable def ep0111011_13 : Blocks := edgeBlocks% "full/vectors/0111011-E-0013.bin"
private noncomputable def ep0111011_14 : Blocks := edgeBlocks% "full/vectors/0111011-E-0014.bin"
private noncomputable def ep0111011_15 : Blocks := edgeBlocks% "full/vectors/0111011-E-0015.bin"
noncomputable def ep0111011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0111011_0 ep0111011_1) (Blocks.join ep0111011_2 ep0111011_3)) (Blocks.join (Blocks.join ep0111011_4 ep0111011_5) (Blocks.join ep0111011_6 ep0111011_7))) (Blocks.join (Blocks.join (Blocks.join ep0111011_8 ep0111011_9) (Blocks.join ep0111011_10 ep0111011_11)) (Blocks.join (Blocks.join ep0111011_12 ep0111011_13) (Blocks.join ep0111011_14 ep0111011_15))))
private theorem idp0111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011101.list =
    C ((2:ℤ)^2388) * horner X vp0111011.list + horner X ep0111011.list := by
  exact edge_identity (B := (2:ℤ)^3205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111011 : Branch 1 (-3711761639/128000000 : ℚ) vp011101 := by
  apply branch_checked idp0111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3711761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-3775761639/64000000 : ℚ) by norm_num]
  exact coverp0111011
theorem coverp011101 : Covers (-3711761639/128000000 : ℚ) vp011101 := join_branches bp0111010 bp0111011
private noncomputable def vp01110011111_0 : Blocks := edgeBlocks% "full/vectors/01110011111-V-0000.bin"
noncomputable def vp01110011111 : Blocks := vp01110011111_0
theorem coverp01110011111 : Covers (-3707761639/4000000 : ℚ) vp01110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp01110011110_0 : Blocks := edgeBlocks% "full/vectors/01110011110-V-0000.bin"
noncomputable def vp01110011110 : Blocks := vp01110011110_0
theorem coverp01110011110 : Covers (-3703761639/4000000 : ℚ) vp01110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111001111_0 : Blocks := edgeBlocks% "full/vectors/0111001111-V-0000.bin"
private noncomputable def vp0111001111_1 : Blocks := edgeBlocks% "full/vectors/0111001111-V-0001.bin"
noncomputable def vp0111001111 : Blocks := (Blocks.join vp0111001111_0 vp0111001111_1)
private theorem bp01110011110 : Branch 0 (-3703761639/8000000 : ℚ) vp0111001111 := by
  apply branch_left_normalized (c:=vp01110011110) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3703761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3703761639/4000000 : ℚ) by norm_num]
  exact coverp01110011110
private noncomputable def ep01110011111_0 : Blocks := edgeBlocks% "full/vectors/01110011111-E-0000.bin"
private noncomputable def ep01110011111_1 : Blocks := edgeBlocks% "full/vectors/01110011111-E-0001.bin"
noncomputable def ep01110011111 : Blocks := (Blocks.join ep01110011111_0 ep01110011111_1)
private theorem idp01110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111001111.list =
    C ((2:ℤ)^176) * horner X vp01110011111.list + horner X ep01110011111.list := by
  exact edge_identity (B := (2:ℤ)^321) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110011111 : Branch 1 (-3703761639/8000000 : ℚ) vp0111001111 := by
  apply branch_checked idp01110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3703761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3707761639/4000000 : ℚ) by norm_num]
  exact coverp01110011111
theorem coverp0111001111 : Covers (-3703761639/8000000 : ℚ) vp0111001111 := join_branches bp01110011110 bp01110011111
private noncomputable def vp01110011101_0 : Blocks := edgeBlocks% "full/vectors/01110011101-V-0000.bin"
noncomputable def vp01110011101 : Blocks := vp01110011101_0
theorem coverp01110011101 : Covers (-3699761639/4000000 : ℚ) vp01110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp01110011100_0 : Blocks := edgeBlocks% "full/vectors/01110011100-V-0000.bin"
noncomputable def vp01110011100 : Blocks := vp01110011100_0
theorem coverp01110011100 : Covers (-3695761639/4000000 : ℚ) vp01110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111001110_0 : Blocks := edgeBlocks% "full/vectors/0111001110-V-0000.bin"
private noncomputable def vp0111001110_1 : Blocks := edgeBlocks% "full/vectors/0111001110-V-0001.bin"
noncomputable def vp0111001110 : Blocks := (Blocks.join vp0111001110_0 vp0111001110_1)
private theorem bp01110011100 : Branch 0 (-3695761639/8000000 : ℚ) vp0111001110 := by
  apply branch_left_normalized (c:=vp01110011100) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3695761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3695761639/4000000 : ℚ) by norm_num]
  exact coverp01110011100
private noncomputable def ep01110011101_0 : Blocks := edgeBlocks% "full/vectors/01110011101-E-0000.bin"
private noncomputable def ep01110011101_1 : Blocks := edgeBlocks% "full/vectors/01110011101-E-0001.bin"
noncomputable def ep01110011101 : Blocks := (Blocks.join ep01110011101_0 ep01110011101_1)
private theorem idp01110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111001110.list =
    C ((2:ℤ)^174) * horner X vp01110011101.list + horner X ep01110011101.list := by
  exact edge_identity (B := (2:ℤ)^320) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110011101 : Branch 1 (-3695761639/8000000 : ℚ) vp0111001110 := by
  apply branch_checked idp01110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3695761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3699761639/4000000 : ℚ) by norm_num]
  exact coverp01110011101
theorem coverp0111001110 : Covers (-3695761639/8000000 : ℚ) vp0111001110 := join_branches bp01110011100 bp01110011101
private noncomputable def vp011100111_0 : Blocks := edgeBlocks% "full/vectors/011100111-V-0000.bin"
private noncomputable def vp011100111_1 : Blocks := edgeBlocks% "full/vectors/011100111-V-0001.bin"
private noncomputable def vp011100111_2 : Blocks := edgeBlocks% "full/vectors/011100111-V-0002.bin"
noncomputable def vp011100111 : Blocks := (Blocks.join vp011100111_0 (Blocks.join vp011100111_1 vp011100111_2))
private theorem bp0111001110 : Branch 0 (-3695761639/16000000 : ℚ) vp011100111 := by
  apply branch_left_normalized (c:=vp0111001110) (k:=0) (m:=150) (by decide +kernel)
  rw [show 2*(-3695761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3695761639/8000000 : ℚ) by norm_num]
  exact coverp0111001110
private noncomputable def ep0111001111_0 : Blocks := edgeBlocks% "full/vectors/0111001111-E-0000.bin"
private noncomputable def ep0111001111_1 : Blocks := edgeBlocks% "full/vectors/0111001111-E-0001.bin"
private noncomputable def ep0111001111_2 : Blocks := edgeBlocks% "full/vectors/0111001111-E-0002.bin"
noncomputable def ep0111001111 : Blocks := (Blocks.join ep0111001111_0 (Blocks.join ep0111001111_1 ep0111001111_2))
private theorem idp0111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011100111.list =
    C ((2:ℤ)^327) * horner X vp0111001111.list + horner X ep0111001111.list := by
  exact edge_identity (B := (2:ℤ)^519) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111001111 : Branch 1 (-3695761639/16000000 : ℚ) vp011100111 := by
  apply branch_checked idp0111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3695761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3703761639/8000000 : ℚ) by norm_num]
  exact coverp0111001111
theorem coverp011100111 : Covers (-3695761639/16000000 : ℚ) vp011100111 := join_branches bp0111001110 bp0111001111
private noncomputable def vp01110011011_0 : Blocks := edgeBlocks% "full/vectors/01110011011-V-0000.bin"
noncomputable def vp01110011011 : Blocks := vp01110011011_0
theorem coverp01110011011 : Covers (-3691761639/4000000 : ℚ) vp01110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp01110011010_0 : Blocks := edgeBlocks% "full/vectors/01110011010-V-0000.bin"
noncomputable def vp01110011010 : Blocks := vp01110011010_0
theorem coverp01110011010 : Covers (-3687761639/4000000 : ℚ) vp01110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111001101_0 : Blocks := edgeBlocks% "full/vectors/0111001101-V-0000.bin"
private noncomputable def vp0111001101_1 : Blocks := edgeBlocks% "full/vectors/0111001101-V-0001.bin"
noncomputable def vp0111001101 : Blocks := (Blocks.join vp0111001101_0 vp0111001101_1)
private theorem bp01110011010 : Branch 0 (-3687761639/8000000 : ℚ) vp0111001101 := by
  apply branch_left_normalized (c:=vp01110011010) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3687761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3687761639/4000000 : ℚ) by norm_num]
  exact coverp01110011010
private noncomputable def ep01110011011_0 : Blocks := edgeBlocks% "full/vectors/01110011011-E-0000.bin"
private noncomputable def ep01110011011_1 : Blocks := edgeBlocks% "full/vectors/01110011011-E-0001.bin"
noncomputable def ep01110011011 : Blocks := (Blocks.join ep01110011011_0 ep01110011011_1)
private theorem idp01110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111001101.list =
    C ((2:ℤ)^176) * horner X vp01110011011.list + horner X ep01110011011.list := by
  exact edge_identity (B := (2:ℤ)^322) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110011011 : Branch 1 (-3687761639/8000000 : ℚ) vp0111001101 := by
  apply branch_checked idp01110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3687761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3691761639/4000000 : ℚ) by norm_num]
  exact coverp01110011011
theorem coverp0111001101 : Covers (-3687761639/8000000 : ℚ) vp0111001101 := join_branches bp01110011010 bp01110011011
private noncomputable def vp01110011001_0 : Blocks := edgeBlocks% "full/vectors/01110011001-V-0000.bin"
noncomputable def vp01110011001 : Blocks := vp01110011001_0
theorem coverp01110011001 : Covers (-3683761639/4000000 : ℚ) vp01110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp01110011000_0 : Blocks := edgeBlocks% "full/vectors/01110011000-V-0000.bin"
noncomputable def vp01110011000 : Blocks := vp01110011000_0
theorem coverp01110011000 : Covers (-3679761639/4000000 : ℚ) vp01110011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111001100_0 : Blocks := edgeBlocks% "full/vectors/0111001100-V-0000.bin"
private noncomputable def vp0111001100_1 : Blocks := edgeBlocks% "full/vectors/0111001100-V-0001.bin"
noncomputable def vp0111001100 : Blocks := (Blocks.join vp0111001100_0 vp0111001100_1)
private theorem bp01110011000 : Branch 0 (-3679761639/8000000 : ℚ) vp0111001100 := by
  apply branch_left_normalized (c:=vp01110011000) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3679761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3679761639/4000000 : ℚ) by norm_num]
  exact coverp01110011000
private noncomputable def ep01110011001_0 : Blocks := edgeBlocks% "full/vectors/01110011001-E-0000.bin"
private noncomputable def ep01110011001_1 : Blocks := edgeBlocks% "full/vectors/01110011001-E-0001.bin"
noncomputable def ep01110011001 : Blocks := (Blocks.join ep01110011001_0 ep01110011001_1)
private theorem idp01110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111001100.list =
    C ((2:ℤ)^175) * horner X vp01110011001.list + horner X ep01110011001.list := by
  exact edge_identity (B := (2:ℤ)^322) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110011001 : Branch 1 (-3679761639/8000000 : ℚ) vp0111001100 := by
  apply branch_checked idp01110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3679761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3683761639/4000000 : ℚ) by norm_num]
  exact coverp01110011001
theorem coverp0111001100 : Covers (-3679761639/8000000 : ℚ) vp0111001100 := join_branches bp01110011000 bp01110011001
private noncomputable def vp011100110_0 : Blocks := edgeBlocks% "full/vectors/011100110-V-0000.bin"
private noncomputable def vp011100110_1 : Blocks := edgeBlocks% "full/vectors/011100110-V-0001.bin"
private noncomputable def vp011100110_2 : Blocks := edgeBlocks% "full/vectors/011100110-V-0002.bin"
noncomputable def vp011100110 : Blocks := (Blocks.join vp011100110_0 (Blocks.join vp011100110_1 vp011100110_2))
private theorem bp0111001100 : Branch 0 (-3679761639/16000000 : ℚ) vp011100110 := by
  apply branch_left_normalized (c:=vp0111001100) (k:=0) (m:=151) (by decide +kernel)
  rw [show 2*(-3679761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3679761639/8000000 : ℚ) by norm_num]
  exact coverp0111001100
private noncomputable def ep0111001101_0 : Blocks := edgeBlocks% "full/vectors/0111001101-E-0000.bin"
private noncomputable def ep0111001101_1 : Blocks := edgeBlocks% "full/vectors/0111001101-E-0001.bin"
private noncomputable def ep0111001101_2 : Blocks := edgeBlocks% "full/vectors/0111001101-E-0002.bin"
noncomputable def ep0111001101 : Blocks := (Blocks.join ep0111001101_0 (Blocks.join ep0111001101_1 ep0111001101_2))
private theorem idp0111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011100110.list =
    C ((2:ℤ)^327) * horner X vp0111001101.list + horner X ep0111001101.list := by
  exact edge_identity (B := (2:ℤ)^520) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111001101 : Branch 1 (-3679761639/16000000 : ℚ) vp011100110 := by
  apply branch_checked idp0111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3679761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3687761639/8000000 : ℚ) by norm_num]
  exact coverp0111001101
theorem coverp011100110 : Covers (-3679761639/16000000 : ℚ) vp011100110 := join_branches bp0111001100 bp0111001101
private noncomputable def vp01110011_0 : Blocks := edgeBlocks% "full/vectors/01110011-V-0000.bin"
private noncomputable def vp01110011_1 : Blocks := edgeBlocks% "full/vectors/01110011-V-0001.bin"
private noncomputable def vp01110011_2 : Blocks := edgeBlocks% "full/vectors/01110011-V-0002.bin"
private noncomputable def vp01110011_3 : Blocks := edgeBlocks% "full/vectors/01110011-V-0003.bin"
private noncomputable def vp01110011_4 : Blocks := edgeBlocks% "full/vectors/01110011-V-0004.bin"
noncomputable def vp01110011 : Blocks := (Blocks.join (Blocks.join vp01110011_0 vp01110011_1) (Blocks.join vp01110011_2 (Blocks.join vp01110011_3 vp01110011_4)))
private theorem bp011100110 : Branch 0 (-3679761639/32000000 : ℚ) vp01110011 := by
  apply branch_left_normalized (c:=vp011100110) (k:=0) (m:=280) (by decide +kernel)
  rw [show 2*(-3679761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3679761639/16000000 : ℚ) by norm_num]
  exact coverp011100110
private noncomputable def ep011100111_0 : Blocks := edgeBlocks% "full/vectors/011100111-E-0000.bin"
private noncomputable def ep011100111_1 : Blocks := edgeBlocks% "full/vectors/011100111-E-0001.bin"
private noncomputable def ep011100111_2 : Blocks := edgeBlocks% "full/vectors/011100111-E-0002.bin"
private noncomputable def ep011100111_3 : Blocks := edgeBlocks% "full/vectors/011100111-E-0003.bin"
private noncomputable def ep011100111_4 : Blocks := edgeBlocks% "full/vectors/011100111-E-0004.bin"
noncomputable def ep011100111 : Blocks := (Blocks.join (Blocks.join ep011100111_0 ep011100111_1) (Blocks.join ep011100111_2 (Blocks.join ep011100111_3 ep011100111_4)))
private theorem idp011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110011.list =
    C ((2:ℤ)^632) * horner X vp011100111.list + horner X ep011100111.list := by
  exact edge_identity (B := (2:ℤ)^915) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100111 : Branch 1 (-3679761639/32000000 : ℚ) vp01110011 := by
  apply branch_checked idp011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3679761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3695761639/16000000 : ℚ) by norm_num]
  exact coverp011100111
theorem coverp01110011 : Covers (-3679761639/32000000 : ℚ) vp01110011 := join_branches bp011100110 bp011100111
private noncomputable def vp01110010111_0 : Blocks := edgeBlocks% "full/vectors/01110010111-V-0000.bin"
noncomputable def vp01110010111 : Blocks := vp01110010111_0
theorem coverp01110010111 : Covers (-3675761639/4000000 : ℚ) vp01110010111 := cover_leaf (by decide +kernel)
private noncomputable def vp01110010110_0 : Blocks := edgeBlocks% "full/vectors/01110010110-V-0000.bin"
noncomputable def vp01110010110 : Blocks := vp01110010110_0
theorem coverp01110010110 : Covers (-3671761639/4000000 : ℚ) vp01110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111001011_0 : Blocks := edgeBlocks% "full/vectors/0111001011-V-0000.bin"
private noncomputable def vp0111001011_1 : Blocks := edgeBlocks% "full/vectors/0111001011-V-0001.bin"
noncomputable def vp0111001011 : Blocks := (Blocks.join vp0111001011_0 vp0111001011_1)
private theorem bp01110010110 : Branch 0 (-3671761639/8000000 : ℚ) vp0111001011 := by
  apply branch_left_normalized (c:=vp01110010110) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3671761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3671761639/4000000 : ℚ) by norm_num]
  exact coverp01110010110
private noncomputable def ep01110010111_0 : Blocks := edgeBlocks% "full/vectors/01110010111-E-0000.bin"
private noncomputable def ep01110010111_1 : Blocks := edgeBlocks% "full/vectors/01110010111-E-0001.bin"
noncomputable def ep01110010111 : Blocks := (Blocks.join ep01110010111_0 ep01110010111_1)
private theorem idp01110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111001011.list =
    C ((2:ℤ)^176) * horner X vp01110010111.list + horner X ep01110010111.list := by
  exact edge_identity (B := (2:ℤ)^323) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110010111 : Branch 1 (-3671761639/8000000 : ℚ) vp0111001011 := by
  apply branch_checked idp01110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-3671761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3675761639/4000000 : ℚ) by norm_num]
  exact coverp01110010111
theorem coverp0111001011 : Covers (-3671761639/8000000 : ℚ) vp0111001011 := join_branches bp01110010110 bp01110010111
private noncomputable def vp01110010101_0 : Blocks := edgeBlocks% "full/vectors/01110010101-V-0000.bin"
noncomputable def vp01110010101 : Blocks := vp01110010101_0
theorem coverp01110010101 : Covers (-3667761639/4000000 : ℚ) vp01110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp01110010100_0 : Blocks := edgeBlocks% "full/vectors/01110010100-V-0000.bin"
noncomputable def vp01110010100 : Blocks := vp01110010100_0
theorem coverp01110010100 : Covers (-3663761639/4000000 : ℚ) vp01110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111001010_0 : Blocks := edgeBlocks% "full/vectors/0111001010-V-0000.bin"
private noncomputable def vp0111001010_1 : Blocks := edgeBlocks% "full/vectors/0111001010-V-0001.bin"
noncomputable def vp0111001010 : Blocks := (Blocks.join vp0111001010_0 vp0111001010_1)
private theorem bp01110010100 : Branch 0 (-3663761639/8000000 : ℚ) vp0111001010 := by
  apply branch_left_normalized (c:=vp01110010100) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3663761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3663761639/4000000 : ℚ) by norm_num]
  exact coverp01110010100
private noncomputable def ep01110010101_0 : Blocks := edgeBlocks% "full/vectors/01110010101-E-0000.bin"
private noncomputable def ep01110010101_1 : Blocks := edgeBlocks% "full/vectors/01110010101-E-0001.bin"
noncomputable def ep01110010101 : Blocks := (Blocks.join ep01110010101_0 ep01110010101_1)
private theorem idp01110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111001010.list =
    C ((2:ℤ)^176) * horner X vp01110010101.list + horner X ep01110010101.list := by
  exact edge_identity (B := (2:ℤ)^323) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110010101 : Branch 1 (-3663761639/8000000 : ℚ) vp0111001010 := by
  apply branch_checked idp01110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-3663761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3667761639/4000000 : ℚ) by norm_num]
  exact coverp01110010101
theorem coverp0111001010 : Covers (-3663761639/8000000 : ℚ) vp0111001010 := join_branches bp01110010100 bp01110010101
private noncomputable def vp011100101_0 : Blocks := edgeBlocks% "full/vectors/011100101-V-0000.bin"
private noncomputable def vp011100101_1 : Blocks := edgeBlocks% "full/vectors/011100101-V-0001.bin"
private noncomputable def vp011100101_2 : Blocks := edgeBlocks% "full/vectors/011100101-V-0002.bin"
noncomputable def vp011100101 : Blocks := (Blocks.join vp011100101_0 (Blocks.join vp011100101_1 vp011100101_2))
private theorem bp0111001010 : Branch 0 (-3663761639/16000000 : ℚ) vp011100101 := by
  apply branch_left_normalized (c:=vp0111001010) (k:=0) (m:=152) (by decide +kernel)
  rw [show 2*(-3663761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3663761639/8000000 : ℚ) by norm_num]
  exact coverp0111001010
private noncomputable def ep0111001011_0 : Blocks := edgeBlocks% "full/vectors/0111001011-E-0000.bin"
private noncomputable def ep0111001011_1 : Blocks := edgeBlocks% "full/vectors/0111001011-E-0001.bin"
private noncomputable def ep0111001011_2 : Blocks := edgeBlocks% "full/vectors/0111001011-E-0002.bin"
noncomputable def ep0111001011 : Blocks := (Blocks.join ep0111001011_0 (Blocks.join ep0111001011_1 ep0111001011_2))
private theorem idp0111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011100101.list =
    C ((2:ℤ)^328) * horner X vp0111001011.list + horner X ep0111001011.list := by
  exact edge_identity (B := (2:ℤ)^521) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111001011 : Branch 1 (-3663761639/16000000 : ℚ) vp011100101 := by
  apply branch_checked idp0111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3663761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3671761639/8000000 : ℚ) by norm_num]
  exact coverp0111001011
theorem coverp011100101 : Covers (-3663761639/16000000 : ℚ) vp011100101 := join_branches bp0111001010 bp0111001011
private noncomputable def vp011100100111_0 : Blocks := edgeBlocks% "full/vectors/011100100111-V-0000.bin"
noncomputable def vp011100100111 : Blocks := vp011100100111_0
theorem coverp011100100111 : Covers (-3661761639/2000000 : ℚ) vp011100100111 := cover_leaf (by decide +kernel)
private noncomputable def vp011100100110_0 : Blocks := edgeBlocks% "full/vectors/011100100110-V-0000.bin"
noncomputable def vp011100100110 : Blocks := vp011100100110_0
theorem coverp011100100110 : Covers (-3659761639/2000000 : ℚ) vp011100100110 := cover_leaf (by decide +kernel)
private noncomputable def vp01110010011_0 : Blocks := edgeBlocks% "full/vectors/01110010011-V-0000.bin"
noncomputable def vp01110010011 : Blocks := vp01110010011_0
private theorem bp011100100110 : Branch 0 (-3659761639/4000000 : ℚ) vp01110010011 := by
  apply branch_left_normalized (c:=vp011100100110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-3659761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3659761639/2000000 : ℚ) by norm_num]
  exact coverp011100100110
private noncomputable def ep011100100111_0 : Blocks := edgeBlocks% "full/vectors/011100100111-E-0000.bin"
noncomputable def ep011100100111 : Blocks := ep011100100111_0
private theorem idp011100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110010011.list =
    C ((2:ℤ)^97) * horner X vp011100100111.list + horner X ep011100100111.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100100111 : Branch 1 (-3659761639/4000000 : ℚ) vp01110010011 := by
  apply branch_checked idp011100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3659761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3661761639/2000000 : ℚ) by norm_num]
  exact coverp011100100111
theorem coverp01110010011 : Covers (-3659761639/4000000 : ℚ) vp01110010011 := join_branches bp011100100110 bp011100100111
private noncomputable def vp011100100101_0 : Blocks := edgeBlocks% "full/vectors/011100100101-V-0000.bin"
noncomputable def vp011100100101 : Blocks := vp011100100101_0
theorem coverp011100100101 : Covers (-3657761639/2000000 : ℚ) vp011100100101 := cover_leaf (by decide +kernel)
private noncomputable def vp011100100100_0 : Blocks := edgeBlocks% "full/vectors/011100100100-V-0000.bin"
noncomputable def vp011100100100 : Blocks := vp011100100100_0
theorem coverp011100100100 : Covers (-3655761639/2000000 : ℚ) vp011100100100 := cover_leaf (by decide +kernel)
private noncomputable def vp01110010010_0 : Blocks := edgeBlocks% "full/vectors/01110010010-V-0000.bin"
noncomputable def vp01110010010 : Blocks := vp01110010010_0
private theorem bp011100100100 : Branch 0 (-3655761639/4000000 : ℚ) vp01110010010 := by
  apply branch_left_normalized (c:=vp011100100100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3655761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3655761639/2000000 : ℚ) by norm_num]
  exact coverp011100100100
private noncomputable def ep011100100101_0 : Blocks := edgeBlocks% "full/vectors/011100100101-E-0000.bin"
noncomputable def ep011100100101 : Blocks := ep011100100101_0
private theorem idp011100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110010010.list =
    C ((2:ℤ)^98) * horner X vp011100100101.list + horner X ep011100100101.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100100101 : Branch 1 (-3655761639/4000000 : ℚ) vp01110010010 := by
  apply branch_checked idp011100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3655761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3657761639/2000000 : ℚ) by norm_num]
  exact coverp011100100101
theorem coverp01110010010 : Covers (-3655761639/4000000 : ℚ) vp01110010010 := join_branches bp011100100100 bp011100100101
private noncomputable def vp0111001001_0 : Blocks := edgeBlocks% "full/vectors/0111001001-V-0000.bin"
private noncomputable def vp0111001001_1 : Blocks := edgeBlocks% "full/vectors/0111001001-V-0001.bin"
noncomputable def vp0111001001 : Blocks := (Blocks.join vp0111001001_0 vp0111001001_1)
private theorem bp01110010010 : Branch 0 (-3655761639/8000000 : ℚ) vp0111001001 := by
  apply branch_left_normalized (c:=vp01110010010) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3655761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3655761639/4000000 : ℚ) by norm_num]
  exact coverp01110010010
private noncomputable def ep01110010011_0 : Blocks := edgeBlocks% "full/vectors/01110010011-E-0000.bin"
private noncomputable def ep01110010011_1 : Blocks := edgeBlocks% "full/vectors/01110010011-E-0001.bin"
noncomputable def ep01110010011 : Blocks := (Blocks.join ep01110010011_0 ep01110010011_1)
private theorem idp01110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111001001.list =
    C ((2:ℤ)^175) * horner X vp01110010011.list + horner X ep01110010011.list := by
  exact edge_identity (B := (2:ℤ)^322) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110010011 : Branch 1 (-3655761639/8000000 : ℚ) vp0111001001 := by
  apply branch_checked idp01110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-3655761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3659761639/4000000 : ℚ) by norm_num]
  exact coverp01110010011
theorem coverp0111001001 : Covers (-3655761639/8000000 : ℚ) vp0111001001 := join_branches bp01110010010 bp01110010011
private noncomputable def vp01110010001_0 : Blocks := edgeBlocks% "full/vectors/01110010001-V-0000.bin"
noncomputable def vp01110010001 : Blocks := vp01110010001_0
theorem coverp01110010001 : Covers (-3651761639/4000000 : ℚ) vp01110010001 := cover_leaf (by decide +kernel)
private noncomputable def vp01110010000_0 : Blocks := edgeBlocks% "full/vectors/01110010000-V-0000.bin"
noncomputable def vp01110010000 : Blocks := vp01110010000_0
theorem coverp01110010000 : Covers (-3647761639/4000000 : ℚ) vp01110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111001000_0 : Blocks := edgeBlocks% "full/vectors/0111001000-V-0000.bin"
private noncomputable def vp0111001000_1 : Blocks := edgeBlocks% "full/vectors/0111001000-V-0001.bin"
noncomputable def vp0111001000 : Blocks := (Blocks.join vp0111001000_0 vp0111001000_1)
private theorem bp01110010000 : Branch 0 (-3647761639/8000000 : ℚ) vp0111001000 := by
  apply branch_left_normalized (c:=vp01110010000) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-3647761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3647761639/4000000 : ℚ) by norm_num]
  exact coverp01110010000
private noncomputable def ep01110010001_0 : Blocks := edgeBlocks% "full/vectors/01110010001-E-0000.bin"
private noncomputable def ep01110010001_1 : Blocks := edgeBlocks% "full/vectors/01110010001-E-0001.bin"
noncomputable def ep01110010001 : Blocks := (Blocks.join ep01110010001_0 ep01110010001_1)
private theorem idp01110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111001000.list =
    C ((2:ℤ)^176) * horner X vp01110010001.list + horner X ep01110010001.list := by
  exact edge_identity (B := (2:ℤ)^323) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110010001 : Branch 1 (-3647761639/8000000 : ℚ) vp0111001000 := by
  apply branch_checked idp01110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3647761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3651761639/4000000 : ℚ) by norm_num]
  exact coverp01110010001
theorem coverp0111001000 : Covers (-3647761639/8000000 : ℚ) vp0111001000 := join_branches bp01110010000 bp01110010001
private noncomputable def vp011100100_0 : Blocks := edgeBlocks% "full/vectors/011100100-V-0000.bin"
private noncomputable def vp011100100_1 : Blocks := edgeBlocks% "full/vectors/011100100-V-0001.bin"
private noncomputable def vp011100100_2 : Blocks := edgeBlocks% "full/vectors/011100100-V-0002.bin"
noncomputable def vp011100100 : Blocks := (Blocks.join vp011100100_0 (Blocks.join vp011100100_1 vp011100100_2))
private theorem bp0111001000 : Branch 0 (-3647761639/16000000 : ℚ) vp011100100 := by
  apply branch_left_normalized (c:=vp0111001000) (k:=0) (m:=152) (by decide +kernel)
  rw [show 2*(-3647761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3647761639/8000000 : ℚ) by norm_num]
  exact coverp0111001000
private noncomputable def ep0111001001_0 : Blocks := edgeBlocks% "full/vectors/0111001001-E-0000.bin"
private noncomputable def ep0111001001_1 : Blocks := edgeBlocks% "full/vectors/0111001001-E-0001.bin"
private noncomputable def ep0111001001_2 : Blocks := edgeBlocks% "full/vectors/0111001001-E-0002.bin"
noncomputable def ep0111001001 : Blocks := (Blocks.join ep0111001001_0 (Blocks.join ep0111001001_1 ep0111001001_2))
private theorem idp0111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011100100.list =
    C ((2:ℤ)^329) * horner X vp0111001001.list + horner X ep0111001001.list := by
  exact edge_identity (B := (2:ℤ)^522) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111001001 : Branch 1 (-3647761639/16000000 : ℚ) vp011100100 := by
  apply branch_checked idp0111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3647761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3655761639/8000000 : ℚ) by norm_num]
  exact coverp0111001001
theorem coverp011100100 : Covers (-3647761639/16000000 : ℚ) vp011100100 := join_branches bp0111001000 bp0111001001
private noncomputable def vp01110010_0 : Blocks := edgeBlocks% "full/vectors/01110010-V-0000.bin"
private noncomputable def vp01110010_1 : Blocks := edgeBlocks% "full/vectors/01110010-V-0001.bin"
private noncomputable def vp01110010_2 : Blocks := edgeBlocks% "full/vectors/01110010-V-0002.bin"
private noncomputable def vp01110010_3 : Blocks := edgeBlocks% "full/vectors/01110010-V-0003.bin"
private noncomputable def vp01110010_4 : Blocks := edgeBlocks% "full/vectors/01110010-V-0004.bin"
noncomputable def vp01110010 : Blocks := (Blocks.join (Blocks.join vp01110010_0 vp01110010_1) (Blocks.join vp01110010_2 (Blocks.join vp01110010_3 vp01110010_4)))
private theorem bp011100100 : Branch 0 (-3647761639/32000000 : ℚ) vp01110010 := by
  apply branch_left_normalized (c:=vp011100100) (k:=0) (m:=282) (by decide +kernel)
  rw [show 2*(-3647761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3647761639/16000000 : ℚ) by norm_num]
  exact coverp011100100
private noncomputable def ep011100101_0 : Blocks := edgeBlocks% "full/vectors/011100101-E-0000.bin"
private noncomputable def ep011100101_1 : Blocks := edgeBlocks% "full/vectors/011100101-E-0001.bin"
private noncomputable def ep011100101_2 : Blocks := edgeBlocks% "full/vectors/011100101-E-0002.bin"
private noncomputable def ep011100101_3 : Blocks := edgeBlocks% "full/vectors/011100101-E-0003.bin"
private noncomputable def ep011100101_4 : Blocks := edgeBlocks% "full/vectors/011100101-E-0004.bin"
noncomputable def ep011100101 : Blocks := (Blocks.join (Blocks.join ep011100101_0 ep011100101_1) (Blocks.join ep011100101_2 (Blocks.join ep011100101_3 ep011100101_4)))
private theorem idp011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110010.list =
    C ((2:ℤ)^633) * horner X vp011100101.list + horner X ep011100101.list := by
  exact edge_identity (B := (2:ℤ)^918) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100101 : Branch 1 (-3647761639/32000000 : ℚ) vp01110010 := by
  apply branch_checked idp011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3647761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3663761639/16000000 : ℚ) by norm_num]
  exact coverp011100101
theorem coverp01110010 : Covers (-3647761639/32000000 : ℚ) vp01110010 := join_branches bp011100100 bp011100101
private noncomputable def vp0111001_0 : Blocks := edgeBlocks% "full/vectors/0111001-V-0000.bin"
private noncomputable def vp0111001_1 : Blocks := edgeBlocks% "full/vectors/0111001-V-0001.bin"
private noncomputable def vp0111001_2 : Blocks := edgeBlocks% "full/vectors/0111001-V-0002.bin"
private noncomputable def vp0111001_3 : Blocks := edgeBlocks% "full/vectors/0111001-V-0003.bin"
private noncomputable def vp0111001_4 : Blocks := edgeBlocks% "full/vectors/0111001-V-0004.bin"
private noncomputable def vp0111001_5 : Blocks := edgeBlocks% "full/vectors/0111001-V-0005.bin"
private noncomputable def vp0111001_6 : Blocks := edgeBlocks% "full/vectors/0111001-V-0006.bin"
private noncomputable def vp0111001_7 : Blocks := edgeBlocks% "full/vectors/0111001-V-0007.bin"
private noncomputable def vp0111001_8 : Blocks := edgeBlocks% "full/vectors/0111001-V-0008.bin"
noncomputable def vp0111001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0111001_0 vp0111001_1) (Blocks.join vp0111001_2 vp0111001_3)) (Blocks.join (Blocks.join vp0111001_4 vp0111001_5) (Blocks.join vp0111001_6 (Blocks.join vp0111001_7 vp0111001_8))))
private theorem bp01110010 : Branch 0 (-3647761639/64000000 : ℚ) vp0111001 := by
  apply branch_left_normalized (c:=vp01110010) (k:=0) (m:=540) (by decide +kernel)
  rw [show 2*(-3647761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3647761639/32000000 : ℚ) by norm_num]
  exact coverp01110010
private noncomputable def ep01110011_0 : Blocks := edgeBlocks% "full/vectors/01110011-E-0000.bin"
private noncomputable def ep01110011_1 : Blocks := edgeBlocks% "full/vectors/01110011-E-0001.bin"
private noncomputable def ep01110011_2 : Blocks := edgeBlocks% "full/vectors/01110011-E-0002.bin"
private noncomputable def ep01110011_3 : Blocks := edgeBlocks% "full/vectors/01110011-E-0003.bin"
private noncomputable def ep01110011_4 : Blocks := edgeBlocks% "full/vectors/01110011-E-0004.bin"
private noncomputable def ep01110011_5 : Blocks := edgeBlocks% "full/vectors/01110011-E-0005.bin"
private noncomputable def ep01110011_6 : Blocks := edgeBlocks% "full/vectors/01110011-E-0006.bin"
private noncomputable def ep01110011_7 : Blocks := edgeBlocks% "full/vectors/01110011-E-0007.bin"
private noncomputable def ep01110011_8 : Blocks := edgeBlocks% "full/vectors/01110011-E-0008.bin"
noncomputable def ep01110011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01110011_0 ep01110011_1) (Blocks.join ep01110011_2 ep01110011_3)) (Blocks.join (Blocks.join ep01110011_4 ep01110011_5) (Blocks.join ep01110011_6 (Blocks.join ep01110011_7 ep01110011_8))))
private theorem idp01110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111001.list =
    C ((2:ℤ)^1233) * horner X vp01110011.list + horner X ep01110011.list := by
  exact edge_identity (B := (2:ℤ)^1700) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110011 : Branch 1 (-3647761639/64000000 : ℚ) vp0111001 := by
  apply branch_checked idp01110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3647761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3679761639/32000000 : ℚ) by norm_num]
  exact coverp01110011
theorem coverp0111001 : Covers (-3647761639/64000000 : ℚ) vp0111001 := join_branches bp01110010 bp01110011
private noncomputable def vp01110001111_0 : Blocks := edgeBlocks% "full/vectors/01110001111-V-0000.bin"
noncomputable def vp01110001111 : Blocks := vp01110001111_0
theorem coverp01110001111 : Covers (-3643761639/4000000 : ℚ) vp01110001111 := cover_leaf (by decide +kernel)
private noncomputable def vp011100011101_0 : Blocks := edgeBlocks% "full/vectors/011100011101-V-0000.bin"
noncomputable def vp011100011101 : Blocks := vp011100011101_0
theorem coverp011100011101 : Covers (-3641761639/2000000 : ℚ) vp011100011101 := cover_leaf (by decide +kernel)
private noncomputable def vp011100011100_0 : Blocks := edgeBlocks% "full/vectors/011100011100-V-0000.bin"
noncomputable def vp011100011100 : Blocks := vp011100011100_0
theorem coverp011100011100 : Covers (-3639761639/2000000 : ℚ) vp011100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp01110001110_0 : Blocks := edgeBlocks% "full/vectors/01110001110-V-0000.bin"
noncomputable def vp01110001110 : Blocks := vp01110001110_0
private theorem bp011100011100 : Branch 0 (-3639761639/4000000 : ℚ) vp01110001110 := by
  apply branch_left_normalized (c:=vp011100011100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3639761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3639761639/2000000 : ℚ) by norm_num]
  exact coverp011100011100
private noncomputable def ep011100011101_0 : Blocks := edgeBlocks% "full/vectors/011100011101-E-0000.bin"
noncomputable def ep011100011101 : Blocks := ep011100011101_0
private theorem idp011100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110001110.list =
    C ((2:ℤ)^99) * horner X vp011100011101.list + horner X ep011100011101.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100011101 : Branch 1 (-3639761639/4000000 : ℚ) vp01110001110 := by
  apply branch_checked idp011100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3639761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3641761639/2000000 : ℚ) by norm_num]
  exact coverp011100011101
theorem coverp01110001110 : Covers (-3639761639/4000000 : ℚ) vp01110001110 := join_branches bp011100011100 bp011100011101
private noncomputable def vp0111000111_0 : Blocks := edgeBlocks% "full/vectors/0111000111-V-0000.bin"
private noncomputable def vp0111000111_1 : Blocks := edgeBlocks% "full/vectors/0111000111-V-0001.bin"
noncomputable def vp0111000111 : Blocks := (Blocks.join vp0111000111_0 vp0111000111_1)
private theorem bp01110001110 : Branch 0 (-3639761639/8000000 : ℚ) vp0111000111 := by
  apply branch_left_normalized (c:=vp01110001110) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3639761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3639761639/4000000 : ℚ) by norm_num]
  exact coverp01110001110
private noncomputable def ep01110001111_0 : Blocks := edgeBlocks% "full/vectors/01110001111-E-0000.bin"
private noncomputable def ep01110001111_1 : Blocks := edgeBlocks% "full/vectors/01110001111-E-0001.bin"
noncomputable def ep01110001111 : Blocks := (Blocks.join ep01110001111_0 ep01110001111_1)
private theorem idp01110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111000111.list =
    C ((2:ℤ)^177) * horner X vp01110001111.list + horner X ep01110001111.list := by
  exact edge_identity (B := (2:ℤ)^324) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110001111 : Branch 1 (-3639761639/8000000 : ℚ) vp0111000111 := by
  apply branch_checked idp01110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3639761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3643761639/4000000 : ℚ) by norm_num]
  exact coverp01110001111
theorem coverp0111000111 : Covers (-3639761639/8000000 : ℚ) vp0111000111 := join_branches bp01110001110 bp01110001111
private noncomputable def vp011100011011_0 : Blocks := edgeBlocks% "full/vectors/011100011011-V-0000.bin"
noncomputable def vp011100011011 : Blocks := vp011100011011_0
theorem coverp011100011011 : Covers (-3637761639/2000000 : ℚ) vp011100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp011100011010_0 : Blocks := edgeBlocks% "full/vectors/011100011010-V-0000.bin"
noncomputable def vp011100011010 : Blocks := vp011100011010_0
theorem coverp011100011010 : Covers (-3635761639/2000000 : ℚ) vp011100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp01110001101_0 : Blocks := edgeBlocks% "full/vectors/01110001101-V-0000.bin"
noncomputable def vp01110001101 : Blocks := vp01110001101_0
private theorem bp011100011010 : Branch 0 (-3635761639/4000000 : ℚ) vp01110001101 := by
  apply branch_left_normalized (c:=vp011100011010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3635761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3635761639/2000000 : ℚ) by norm_num]
  exact coverp011100011010
private noncomputable def ep011100011011_0 : Blocks := edgeBlocks% "full/vectors/011100011011-E-0000.bin"
noncomputable def ep011100011011 : Blocks := ep011100011011_0
private theorem idp011100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110001101.list =
    C ((2:ℤ)^99) * horner X vp011100011011.list + horner X ep011100011011.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100011011 : Branch 1 (-3635761639/4000000 : ℚ) vp01110001101 := by
  apply branch_checked idp011100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3635761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3637761639/2000000 : ℚ) by norm_num]
  exact coverp011100011011
theorem coverp01110001101 : Covers (-3635761639/4000000 : ℚ) vp01110001101 := join_branches bp011100011010 bp011100011011
private noncomputable def vp011100011001_0 : Blocks := edgeBlocks% "full/vectors/011100011001-V-0000.bin"
noncomputable def vp011100011001 : Blocks := vp011100011001_0
theorem coverp011100011001 : Covers (-3633761639/2000000 : ℚ) vp011100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp011100011000_0 : Blocks := edgeBlocks% "full/vectors/011100011000-V-0000.bin"
noncomputable def vp011100011000 : Blocks := vp011100011000_0
theorem coverp011100011000 : Covers (-3631761639/2000000 : ℚ) vp011100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp01110001100_0 : Blocks := edgeBlocks% "full/vectors/01110001100-V-0000.bin"
noncomputable def vp01110001100 : Blocks := vp01110001100_0
private theorem bp011100011000 : Branch 0 (-3631761639/4000000 : ℚ) vp01110001100 := by
  apply branch_left_normalized (c:=vp011100011000) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-3631761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3631761639/2000000 : ℚ) by norm_num]
  exact coverp011100011000
private noncomputable def ep011100011001_0 : Blocks := edgeBlocks% "full/vectors/011100011001-E-0000.bin"
noncomputable def ep011100011001 : Blocks := ep011100011001_0
private theorem idp011100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110001100.list =
    C ((2:ℤ)^99) * horner X vp011100011001.list + horner X ep011100011001.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100011001 : Branch 1 (-3631761639/4000000 : ℚ) vp01110001100 := by
  apply branch_checked idp011100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3631761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3633761639/2000000 : ℚ) by norm_num]
  exact coverp011100011001
theorem coverp01110001100 : Covers (-3631761639/4000000 : ℚ) vp01110001100 := join_branches bp011100011000 bp011100011001
private noncomputable def vp0111000110_0 : Blocks := edgeBlocks% "full/vectors/0111000110-V-0000.bin"
private noncomputable def vp0111000110_1 : Blocks := edgeBlocks% "full/vectors/0111000110-V-0001.bin"
noncomputable def vp0111000110 : Blocks := (Blocks.join vp0111000110_0 vp0111000110_1)
private theorem bp01110001100 : Branch 0 (-3631761639/8000000 : ℚ) vp0111000110 := by
  apply branch_left_normalized (c:=vp01110001100) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3631761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3631761639/4000000 : ℚ) by norm_num]
  exact coverp01110001100
private noncomputable def ep01110001101_0 : Blocks := edgeBlocks% "full/vectors/01110001101-E-0000.bin"
private noncomputable def ep01110001101_1 : Blocks := edgeBlocks% "full/vectors/01110001101-E-0001.bin"
noncomputable def ep01110001101 : Blocks := (Blocks.join ep01110001101_0 ep01110001101_1)
private theorem idp01110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111000110.list =
    C ((2:ℤ)^176) * horner X vp01110001101.list + horner X ep01110001101.list := by
  exact edge_identity (B := (2:ℤ)^324) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110001101 : Branch 1 (-3631761639/8000000 : ℚ) vp0111000110 := by
  apply branch_checked idp01110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3631761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3635761639/4000000 : ℚ) by norm_num]
  exact coverp01110001101
theorem coverp0111000110 : Covers (-3631761639/8000000 : ℚ) vp0111000110 := join_branches bp01110001100 bp01110001101
private noncomputable def vp011100011_0 : Blocks := edgeBlocks% "full/vectors/011100011-V-0000.bin"
private noncomputable def vp011100011_1 : Blocks := edgeBlocks% "full/vectors/011100011-V-0001.bin"
private noncomputable def vp011100011_2 : Blocks := edgeBlocks% "full/vectors/011100011-V-0002.bin"
noncomputable def vp011100011 : Blocks := (Blocks.join vp011100011_0 (Blocks.join vp011100011_1 vp011100011_2))
private theorem bp0111000110 : Branch 0 (-3631761639/16000000 : ℚ) vp011100011 := by
  apply branch_left_normalized (c:=vp0111000110) (k:=0) (m:=152) (by decide +kernel)
  rw [show 2*(-3631761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3631761639/8000000 : ℚ) by norm_num]
  exact coverp0111000110
private noncomputable def ep0111000111_0 : Blocks := edgeBlocks% "full/vectors/0111000111-E-0000.bin"
private noncomputable def ep0111000111_1 : Blocks := edgeBlocks% "full/vectors/0111000111-E-0001.bin"
private noncomputable def ep0111000111_2 : Blocks := edgeBlocks% "full/vectors/0111000111-E-0002.bin"
noncomputable def ep0111000111 : Blocks := (Blocks.join ep0111000111_0 (Blocks.join ep0111000111_1 ep0111000111_2))
private theorem idp0111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011100011.list =
    C ((2:ℤ)^329) * horner X vp0111000111.list + horner X ep0111000111.list := by
  exact edge_identity (B := (2:ℤ)^523) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111000111 : Branch 1 (-3631761639/16000000 : ℚ) vp011100011 := by
  apply branch_checked idp0111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3631761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3639761639/8000000 : ℚ) by norm_num]
  exact coverp0111000111
theorem coverp011100011 : Covers (-3631761639/16000000 : ℚ) vp011100011 := join_branches bp0111000110 bp0111000111
private noncomputable def vp011100010111_0 : Blocks := edgeBlocks% "full/vectors/011100010111-V-0000.bin"
noncomputable def vp011100010111 : Blocks := vp011100010111_0
theorem coverp011100010111 : Covers (-3629761639/2000000 : ℚ) vp011100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp011100010110_0 : Blocks := edgeBlocks% "full/vectors/011100010110-V-0000.bin"
noncomputable def vp011100010110 : Blocks := vp011100010110_0
theorem coverp011100010110 : Covers (-3627761639/2000000 : ℚ) vp011100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp01110001011_0 : Blocks := edgeBlocks% "full/vectors/01110001011-V-0000.bin"
noncomputable def vp01110001011 : Blocks := vp01110001011_0
private theorem bp011100010110 : Branch 0 (-3627761639/4000000 : ℚ) vp01110001011 := by
  apply branch_left_normalized (c:=vp011100010110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3627761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3627761639/2000000 : ℚ) by norm_num]
  exact coverp011100010110
private noncomputable def ep011100010111_0 : Blocks := edgeBlocks% "full/vectors/011100010111-E-0000.bin"
noncomputable def ep011100010111 : Blocks := ep011100010111_0
private theorem idp011100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110001011.list =
    C ((2:ℤ)^99) * horner X vp011100010111.list + horner X ep011100010111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100010111 : Branch 1 (-3627761639/4000000 : ℚ) vp01110001011 := by
  apply branch_checked idp011100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-3627761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3629761639/2000000 : ℚ) by norm_num]
  exact coverp011100010111
theorem coverp01110001011 : Covers (-3627761639/4000000 : ℚ) vp01110001011 := join_branches bp011100010110 bp011100010111
private noncomputable def vp01110001010_0 : Blocks := edgeBlocks% "full/vectors/01110001010-V-0000.bin"
noncomputable def vp01110001010 : Blocks := vp01110001010_0
theorem coverp01110001010 : Covers (-3623761639/4000000 : ℚ) vp01110001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111000101_0 : Blocks := edgeBlocks% "full/vectors/0111000101-V-0000.bin"
private noncomputable def vp0111000101_1 : Blocks := edgeBlocks% "full/vectors/0111000101-V-0001.bin"
noncomputable def vp0111000101 : Blocks := (Blocks.join vp0111000101_0 vp0111000101_1)
private theorem bp01110001010 : Branch 0 (-3623761639/8000000 : ℚ) vp0111000101 := by
  apply branch_left_normalized (c:=vp01110001010) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3623761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3623761639/4000000 : ℚ) by norm_num]
  exact coverp01110001010
private noncomputable def ep01110001011_0 : Blocks := edgeBlocks% "full/vectors/01110001011-E-0000.bin"
private noncomputable def ep01110001011_1 : Blocks := edgeBlocks% "full/vectors/01110001011-E-0001.bin"
noncomputable def ep01110001011 : Blocks := (Blocks.join ep01110001011_0 ep01110001011_1)
private theorem idp01110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111000101.list =
    C ((2:ℤ)^176) * horner X vp01110001011.list + horner X ep01110001011.list := by
  exact edge_identity (B := (2:ℤ)^324) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110001011 : Branch 1 (-3623761639/8000000 : ℚ) vp0111000101 := by
  apply branch_checked idp01110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3623761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3627761639/4000000 : ℚ) by norm_num]
  exact coverp01110001011
theorem coverp0111000101 : Covers (-3623761639/8000000 : ℚ) vp0111000101 := join_branches bp01110001010 bp01110001011
private noncomputable def vp01110001001_0 : Blocks := edgeBlocks% "full/vectors/01110001001-V-0000.bin"
noncomputable def vp01110001001 : Blocks := vp01110001001_0
theorem coverp01110001001 : Covers (-3619761639/4000000 : ℚ) vp01110001001 := cover_leaf (by decide +kernel)
private noncomputable def vp011100010001_0 : Blocks := edgeBlocks% "full/vectors/011100010001-V-0000.bin"
noncomputable def vp011100010001 : Blocks := vp011100010001_0
theorem coverp011100010001 : Covers (-3617761639/2000000 : ℚ) vp011100010001 := cover_leaf (by decide +kernel)
private noncomputable def vp011100010000_0 : Blocks := edgeBlocks% "full/vectors/011100010000-V-0000.bin"
noncomputable def vp011100010000 : Blocks := vp011100010000_0
theorem coverp011100010000 : Covers (-3615761639/2000000 : ℚ) vp011100010000 := cover_leaf (by decide +kernel)
private noncomputable def vp01110001000_0 : Blocks := edgeBlocks% "full/vectors/01110001000-V-0000.bin"
noncomputable def vp01110001000 : Blocks := vp01110001000_0
private theorem bp011100010000 : Branch 0 (-3615761639/4000000 : ℚ) vp01110001000 := by
  apply branch_left_normalized (c:=vp011100010000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3615761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3615761639/2000000 : ℚ) by norm_num]
  exact coverp011100010000
private noncomputable def ep011100010001_0 : Blocks := edgeBlocks% "full/vectors/011100010001-E-0000.bin"
noncomputable def ep011100010001 : Blocks := ep011100010001_0
private theorem idp011100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110001000.list =
    C ((2:ℤ)^99) * horner X vp011100010001.list + horner X ep011100010001.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100010001 : Branch 1 (-3615761639/4000000 : ℚ) vp01110001000 := by
  apply branch_checked idp011100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3615761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3617761639/2000000 : ℚ) by norm_num]
  exact coverp011100010001
theorem coverp01110001000 : Covers (-3615761639/4000000 : ℚ) vp01110001000 := join_branches bp011100010000 bp011100010001
private noncomputable def vp0111000100_0 : Blocks := edgeBlocks% "full/vectors/0111000100-V-0000.bin"
private noncomputable def vp0111000100_1 : Blocks := edgeBlocks% "full/vectors/0111000100-V-0001.bin"
noncomputable def vp0111000100 : Blocks := (Blocks.join vp0111000100_0 vp0111000100_1)
private theorem bp01110001000 : Branch 0 (-3615761639/8000000 : ℚ) vp0111000100 := by
  apply branch_left_normalized (c:=vp01110001000) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3615761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3615761639/4000000 : ℚ) by norm_num]
  exact coverp01110001000
private noncomputable def ep01110001001_0 : Blocks := edgeBlocks% "full/vectors/01110001001-E-0000.bin"
private noncomputable def ep01110001001_1 : Blocks := edgeBlocks% "full/vectors/01110001001-E-0001.bin"
noncomputable def ep01110001001 : Blocks := (Blocks.join ep01110001001_0 ep01110001001_1)
private theorem idp01110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111000100.list =
    C ((2:ℤ)^177) * horner X vp01110001001.list + horner X ep01110001001.list := by
  exact edge_identity (B := (2:ℤ)^325) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110001001 : Branch 1 (-3615761639/8000000 : ℚ) vp0111000100 := by
  apply branch_checked idp01110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3615761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3619761639/4000000 : ℚ) by norm_num]
  exact coverp01110001001
theorem coverp0111000100 : Covers (-3615761639/8000000 : ℚ) vp0111000100 := join_branches bp01110001000 bp01110001001
private noncomputable def vp011100010_0 : Blocks := edgeBlocks% "full/vectors/011100010-V-0000.bin"
private noncomputable def vp011100010_1 : Blocks := edgeBlocks% "full/vectors/011100010-V-0001.bin"
private noncomputable def vp011100010_2 : Blocks := edgeBlocks% "full/vectors/011100010-V-0002.bin"
noncomputable def vp011100010 : Blocks := (Blocks.join vp011100010_0 (Blocks.join vp011100010_1 vp011100010_2))
private theorem bp0111000100 : Branch 0 (-3615761639/16000000 : ℚ) vp011100010 := by
  apply branch_left_normalized (c:=vp0111000100) (k:=0) (m:=153) (by decide +kernel)
  rw [show 2*(-3615761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3615761639/8000000 : ℚ) by norm_num]
  exact coverp0111000100
private noncomputable def ep0111000101_0 : Blocks := edgeBlocks% "full/vectors/0111000101-E-0000.bin"
private noncomputable def ep0111000101_1 : Blocks := edgeBlocks% "full/vectors/0111000101-E-0001.bin"
private noncomputable def ep0111000101_2 : Blocks := edgeBlocks% "full/vectors/0111000101-E-0002.bin"
noncomputable def ep0111000101 : Blocks := (Blocks.join ep0111000101_0 (Blocks.join ep0111000101_1 ep0111000101_2))
private theorem idp0111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011100010.list =
    C ((2:ℤ)^330) * horner X vp0111000101.list + horner X ep0111000101.list := by
  exact edge_identity (B := (2:ℤ)^524) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111000101 : Branch 1 (-3615761639/16000000 : ℚ) vp011100010 := by
  apply branch_checked idp0111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3615761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3623761639/8000000 : ℚ) by norm_num]
  exact coverp0111000101
theorem coverp011100010 : Covers (-3615761639/16000000 : ℚ) vp011100010 := join_branches bp0111000100 bp0111000101
private noncomputable def vp01110001_0 : Blocks := edgeBlocks% "full/vectors/01110001-V-0000.bin"
private noncomputable def vp01110001_1 : Blocks := edgeBlocks% "full/vectors/01110001-V-0001.bin"
private noncomputable def vp01110001_2 : Blocks := edgeBlocks% "full/vectors/01110001-V-0002.bin"
private noncomputable def vp01110001_3 : Blocks := edgeBlocks% "full/vectors/01110001-V-0003.bin"
private noncomputable def vp01110001_4 : Blocks := edgeBlocks% "full/vectors/01110001-V-0004.bin"
noncomputable def vp01110001 : Blocks := (Blocks.join (Blocks.join vp01110001_0 vp01110001_1) (Blocks.join vp01110001_2 (Blocks.join vp01110001_3 vp01110001_4)))
private theorem bp011100010 : Branch 0 (-3615761639/32000000 : ℚ) vp01110001 := by
  apply branch_left_normalized (c:=vp011100010) (k:=0) (m:=283) (by decide +kernel)
  rw [show 2*(-3615761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3615761639/16000000 : ℚ) by norm_num]
  exact coverp011100010
private noncomputable def ep011100011_0 : Blocks := edgeBlocks% "full/vectors/011100011-E-0000.bin"
private noncomputable def ep011100011_1 : Blocks := edgeBlocks% "full/vectors/011100011-E-0001.bin"
private noncomputable def ep011100011_2 : Blocks := edgeBlocks% "full/vectors/011100011-E-0002.bin"
private noncomputable def ep011100011_3 : Blocks := edgeBlocks% "full/vectors/011100011-E-0003.bin"
private noncomputable def ep011100011_4 : Blocks := edgeBlocks% "full/vectors/011100011-E-0004.bin"
noncomputable def ep011100011 : Blocks := (Blocks.join (Blocks.join ep011100011_0 ep011100011_1) (Blocks.join ep011100011_2 (Blocks.join ep011100011_3 ep011100011_4)))
private theorem idp011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110001.list =
    C ((2:ℤ)^635) * horner X vp011100011.list + horner X ep011100011.list := by
  exact edge_identity (B := (2:ℤ)^921) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100011 : Branch 1 (-3615761639/32000000 : ℚ) vp01110001 := by
  apply branch_checked idp011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-3615761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3631761639/16000000 : ℚ) by norm_num]
  exact coverp011100011
theorem coverp01110001 : Covers (-3615761639/32000000 : ℚ) vp01110001 := join_branches bp011100010 bp011100011
private noncomputable def vp011100001111_0 : Blocks := edgeBlocks% "full/vectors/011100001111-V-0000.bin"
noncomputable def vp011100001111 : Blocks := vp011100001111_0
theorem coverp011100001111 : Covers (-3613761639/2000000 : ℚ) vp011100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp011100001110_0 : Blocks := edgeBlocks% "full/vectors/011100001110-V-0000.bin"
noncomputable def vp011100001110 : Blocks := vp011100001110_0
theorem coverp011100001110 : Covers (-3611761639/2000000 : ℚ) vp011100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp01110000111_0 : Blocks := edgeBlocks% "full/vectors/01110000111-V-0000.bin"
noncomputable def vp01110000111 : Blocks := vp01110000111_0
private theorem bp011100001110 : Branch 0 (-3611761639/4000000 : ℚ) vp01110000111 := by
  apply branch_left_normalized (c:=vp011100001110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3611761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3611761639/2000000 : ℚ) by norm_num]
  exact coverp011100001110
private noncomputable def ep011100001111_0 : Blocks := edgeBlocks% "full/vectors/011100001111-E-0000.bin"
noncomputable def ep011100001111 : Blocks := ep011100001111_0
private theorem idp011100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110000111.list =
    C ((2:ℤ)^98) * horner X vp011100001111.list + horner X ep011100001111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100001111 : Branch 1 (-3611761639/4000000 : ℚ) vp01110000111 := by
  apply branch_checked idp011100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3611761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3613761639/2000000 : ℚ) by norm_num]
  exact coverp011100001111
theorem coverp01110000111 : Covers (-3611761639/4000000 : ℚ) vp01110000111 := join_branches bp011100001110 bp011100001111
private noncomputable def vp011100001101_0 : Blocks := edgeBlocks% "full/vectors/011100001101-V-0000.bin"
noncomputable def vp011100001101 : Blocks := vp011100001101_0
theorem coverp011100001101 : Covers (-3609761639/2000000 : ℚ) vp011100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp011100001100_0 : Blocks := edgeBlocks% "full/vectors/011100001100-V-0000.bin"
noncomputable def vp011100001100 : Blocks := vp011100001100_0
theorem coverp011100001100 : Covers (-3607761639/2000000 : ℚ) vp011100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp01110000110_0 : Blocks := edgeBlocks% "full/vectors/01110000110-V-0000.bin"
noncomputable def vp01110000110 : Blocks := vp01110000110_0
private theorem bp011100001100 : Branch 0 (-3607761639/4000000 : ℚ) vp01110000110 := by
  apply branch_left_normalized (c:=vp011100001100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3607761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3607761639/2000000 : ℚ) by norm_num]
  exact coverp011100001100
private noncomputable def ep011100001101_0 : Blocks := edgeBlocks% "full/vectors/011100001101-E-0000.bin"
noncomputable def ep011100001101 : Blocks := ep011100001101_0
private theorem idp011100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110000110.list =
    C ((2:ℤ)^98) * horner X vp011100001101.list + horner X ep011100001101.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100001101 : Branch 1 (-3607761639/4000000 : ℚ) vp01110000110 := by
  apply branch_checked idp011100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3607761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3609761639/2000000 : ℚ) by norm_num]
  exact coverp011100001101
theorem coverp01110000110 : Covers (-3607761639/4000000 : ℚ) vp01110000110 := join_branches bp011100001100 bp011100001101
private noncomputable def vp0111000011_0 : Blocks := edgeBlocks% "full/vectors/0111000011-V-0000.bin"
private noncomputable def vp0111000011_1 : Blocks := edgeBlocks% "full/vectors/0111000011-V-0001.bin"
noncomputable def vp0111000011 : Blocks := (Blocks.join vp0111000011_0 vp0111000011_1)
private theorem bp01110000110 : Branch 0 (-3607761639/8000000 : ℚ) vp0111000011 := by
  apply branch_left_normalized (c:=vp01110000110) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3607761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3607761639/4000000 : ℚ) by norm_num]
  exact coverp01110000110
private noncomputable def ep01110000111_0 : Blocks := edgeBlocks% "full/vectors/01110000111-E-0000.bin"
private noncomputable def ep01110000111_1 : Blocks := edgeBlocks% "full/vectors/01110000111-E-0001.bin"
noncomputable def ep01110000111 : Blocks := (Blocks.join ep01110000111_0 ep01110000111_1)
private theorem idp01110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111000011.list =
    C ((2:ℤ)^176) * horner X vp01110000111.list + horner X ep01110000111.list := by
  exact edge_identity (B := (2:ℤ)^323) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110000111 : Branch 1 (-3607761639/8000000 : ℚ) vp0111000011 := by
  apply branch_checked idp01110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3607761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3611761639/4000000 : ℚ) by norm_num]
  exact coverp01110000111
theorem coverp0111000011 : Covers (-3607761639/8000000 : ℚ) vp0111000011 := join_branches bp01110000110 bp01110000111
private noncomputable def vp011100001011_0 : Blocks := edgeBlocks% "full/vectors/011100001011-V-0000.bin"
noncomputable def vp011100001011 : Blocks := vp011100001011_0
theorem coverp011100001011 : Covers (-3605761639/2000000 : ℚ) vp011100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp011100001010_0 : Blocks := edgeBlocks% "full/vectors/011100001010-V-0000.bin"
noncomputable def vp011100001010 : Blocks := vp011100001010_0
theorem coverp011100001010 : Covers (-3603761639/2000000 : ℚ) vp011100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp01110000101_0 : Blocks := edgeBlocks% "full/vectors/01110000101-V-0000.bin"
noncomputable def vp01110000101 : Blocks := vp01110000101_0
private theorem bp011100001010 : Branch 0 (-3603761639/4000000 : ℚ) vp01110000101 := by
  apply branch_left_normalized (c:=vp011100001010) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-3603761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3603761639/2000000 : ℚ) by norm_num]
  exact coverp011100001010
private noncomputable def ep011100001011_0 : Blocks := edgeBlocks% "full/vectors/011100001011-E-0000.bin"
noncomputable def ep011100001011 : Blocks := ep011100001011_0
private theorem idp011100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110000101.list =
    C ((2:ℤ)^98) * horner X vp011100001011.list + horner X ep011100001011.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100001011 : Branch 1 (-3603761639/4000000 : ℚ) vp01110000101 := by
  apply branch_checked idp011100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3603761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3605761639/2000000 : ℚ) by norm_num]
  exact coverp011100001011
theorem coverp01110000101 : Covers (-3603761639/4000000 : ℚ) vp01110000101 := join_branches bp011100001010 bp011100001011
private noncomputable def vp011100001001_0 : Blocks := edgeBlocks% "full/vectors/011100001001-V-0000.bin"
noncomputable def vp011100001001 : Blocks := vp011100001001_0
theorem coverp011100001001 : Covers (-3601761639/2000000 : ℚ) vp011100001001 := cover_leaf (by decide +kernel)
private noncomputable def vp011100001000_0 : Blocks := edgeBlocks% "full/vectors/011100001000-V-0000.bin"
noncomputable def vp011100001000 : Blocks := vp011100001000_0
theorem coverp011100001000 : Covers (-3599761639/2000000 : ℚ) vp011100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp01110000100_0 : Blocks := edgeBlocks% "full/vectors/01110000100-V-0000.bin"
noncomputable def vp01110000100 : Blocks := vp01110000100_0
private theorem bp011100001000 : Branch 0 (-3599761639/4000000 : ℚ) vp01110000100 := by
  apply branch_left_normalized (c:=vp011100001000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3599761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3599761639/2000000 : ℚ) by norm_num]
  exact coverp011100001000
private noncomputable def ep011100001001_0 : Blocks := edgeBlocks% "full/vectors/011100001001-E-0000.bin"
noncomputable def ep011100001001 : Blocks := ep011100001001_0
private theorem idp011100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110000100.list =
    C ((2:ℤ)^98) * horner X vp011100001001.list + horner X ep011100001001.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100001001 : Branch 1 (-3599761639/4000000 : ℚ) vp01110000100 := by
  apply branch_checked idp011100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3599761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3601761639/2000000 : ℚ) by norm_num]
  exact coverp011100001001
theorem coverp01110000100 : Covers (-3599761639/4000000 : ℚ) vp01110000100 := join_branches bp011100001000 bp011100001001
private noncomputable def vp0111000010_0 : Blocks := edgeBlocks% "full/vectors/0111000010-V-0000.bin"
private noncomputable def vp0111000010_1 : Blocks := edgeBlocks% "full/vectors/0111000010-V-0001.bin"
noncomputable def vp0111000010 : Blocks := (Blocks.join vp0111000010_0 vp0111000010_1)
private theorem bp01110000100 : Branch 0 (-3599761639/8000000 : ℚ) vp0111000010 := by
  apply branch_left_normalized (c:=vp01110000100) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3599761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3599761639/4000000 : ℚ) by norm_num]
  exact coverp01110000100
private noncomputable def ep01110000101_0 : Blocks := edgeBlocks% "full/vectors/01110000101-E-0000.bin"
private noncomputable def ep01110000101_1 : Blocks := edgeBlocks% "full/vectors/01110000101-E-0001.bin"
noncomputable def ep01110000101 : Blocks := (Blocks.join ep01110000101_0 ep01110000101_1)
private theorem idp01110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111000010.list =
    C ((2:ℤ)^177) * horner X vp01110000101.list + horner X ep01110000101.list := by
  exact edge_identity (B := (2:ℤ)^324) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110000101 : Branch 1 (-3599761639/8000000 : ℚ) vp0111000010 := by
  apply branch_checked idp01110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3599761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3603761639/4000000 : ℚ) by norm_num]
  exact coverp01110000101
theorem coverp0111000010 : Covers (-3599761639/8000000 : ℚ) vp0111000010 := join_branches bp01110000100 bp01110000101
private noncomputable def vp011100001_0 : Blocks := edgeBlocks% "full/vectors/011100001-V-0000.bin"
private noncomputable def vp011100001_1 : Blocks := edgeBlocks% "full/vectors/011100001-V-0001.bin"
private noncomputable def vp011100001_2 : Blocks := edgeBlocks% "full/vectors/011100001-V-0002.bin"
noncomputable def vp011100001 : Blocks := (Blocks.join vp011100001_0 (Blocks.join vp011100001_1 vp011100001_2))
private theorem bp0111000010 : Branch 0 (-3599761639/16000000 : ℚ) vp011100001 := by
  apply branch_left_normalized (c:=vp0111000010) (k:=0) (m:=153) (by decide +kernel)
  rw [show 2*(-3599761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3599761639/8000000 : ℚ) by norm_num]
  exact coverp0111000010
private noncomputable def ep0111000011_0 : Blocks := edgeBlocks% "full/vectors/0111000011-E-0000.bin"
private noncomputable def ep0111000011_1 : Blocks := edgeBlocks% "full/vectors/0111000011-E-0001.bin"
private noncomputable def ep0111000011_2 : Blocks := edgeBlocks% "full/vectors/0111000011-E-0002.bin"
noncomputable def ep0111000011 : Blocks := (Blocks.join ep0111000011_0 (Blocks.join ep0111000011_1 ep0111000011_2))
private theorem idp0111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011100001.list =
    C ((2:ℤ)^330) * horner X vp0111000011.list + horner X ep0111000011.list := by
  exact edge_identity (B := (2:ℤ)^524) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111000011 : Branch 1 (-3599761639/16000000 : ℚ) vp011100001 := by
  apply branch_checked idp0111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3599761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3607761639/8000000 : ℚ) by norm_num]
  exact coverp0111000011
theorem coverp011100001 : Covers (-3599761639/16000000 : ℚ) vp011100001 := join_branches bp0111000010 bp0111000011
private noncomputable def vp011100000111_0 : Blocks := edgeBlocks% "full/vectors/011100000111-V-0000.bin"
noncomputable def vp011100000111 : Blocks := vp011100000111_0
theorem coverp011100000111 : Covers (-3597761639/2000000 : ℚ) vp011100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp011100000110_0 : Blocks := edgeBlocks% "full/vectors/011100000110-V-0000.bin"
noncomputable def vp011100000110 : Blocks := vp011100000110_0
theorem coverp011100000110 : Covers (-3595761639/2000000 : ℚ) vp011100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp01110000011_0 : Blocks := edgeBlocks% "full/vectors/01110000011-V-0000.bin"
noncomputable def vp01110000011 : Blocks := vp01110000011_0
private theorem bp011100000110 : Branch 0 (-3595761639/4000000 : ℚ) vp01110000011 := by
  apply branch_left_normalized (c:=vp011100000110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3595761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3595761639/2000000 : ℚ) by norm_num]
  exact coverp011100000110
private noncomputable def ep011100000111_0 : Blocks := edgeBlocks% "full/vectors/011100000111-E-0000.bin"
noncomputable def ep011100000111 : Blocks := ep011100000111_0
private theorem idp011100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110000011.list =
    C ((2:ℤ)^98) * horner X vp011100000111.list + horner X ep011100000111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100000111 : Branch 1 (-3595761639/4000000 : ℚ) vp01110000011 := by
  apply branch_checked idp011100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3595761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3597761639/2000000 : ℚ) by norm_num]
  exact coverp011100000111
theorem coverp01110000011 : Covers (-3595761639/4000000 : ℚ) vp01110000011 := join_branches bp011100000110 bp011100000111
private noncomputable def vp01110000010_0 : Blocks := edgeBlocks% "full/vectors/01110000010-V-0000.bin"
noncomputable def vp01110000010 : Blocks := vp01110000010_0
theorem coverp01110000010 : Covers (-3591761639/4000000 : ℚ) vp01110000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111000001_0 : Blocks := edgeBlocks% "full/vectors/0111000001-V-0000.bin"
private noncomputable def vp0111000001_1 : Blocks := edgeBlocks% "full/vectors/0111000001-V-0001.bin"
noncomputable def vp0111000001 : Blocks := (Blocks.join vp0111000001_0 vp0111000001_1)
private theorem bp01110000010 : Branch 0 (-3591761639/8000000 : ℚ) vp0111000001 := by
  apply branch_left_normalized (c:=vp01110000010) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3591761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3591761639/4000000 : ℚ) by norm_num]
  exact coverp01110000010
private noncomputable def ep01110000011_0 : Blocks := edgeBlocks% "full/vectors/01110000011-E-0000.bin"
private noncomputable def ep01110000011_1 : Blocks := edgeBlocks% "full/vectors/01110000011-E-0001.bin"
noncomputable def ep01110000011 : Blocks := (Blocks.join ep01110000011_0 ep01110000011_1)
private theorem idp01110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111000001.list =
    C ((2:ℤ)^177) * horner X vp01110000011.list + horner X ep01110000011.list := by
  exact edge_identity (B := (2:ℤ)^324) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110000011 : Branch 1 (-3591761639/8000000 : ℚ) vp0111000001 := by
  apply branch_checked idp01110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3591761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3595761639/4000000 : ℚ) by norm_num]
  exact coverp01110000011
theorem coverp0111000001 : Covers (-3591761639/8000000 : ℚ) vp0111000001 := join_branches bp01110000010 bp01110000011
private noncomputable def vp011100000011_0 : Blocks := edgeBlocks% "full/vectors/011100000011-V-0000.bin"
noncomputable def vp011100000011 : Blocks := vp011100000011_0
theorem coverp011100000011 : Covers (-3589761639/2000000 : ℚ) vp011100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp011100000010_0 : Blocks := edgeBlocks% "full/vectors/011100000010-V-0000.bin"
noncomputable def vp011100000010 : Blocks := vp011100000010_0
theorem coverp011100000010 : Covers (-3587761639/2000000 : ℚ) vp011100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp01110000001_0 : Blocks := edgeBlocks% "full/vectors/01110000001-V-0000.bin"
noncomputable def vp01110000001 : Blocks := vp01110000001_0
private theorem bp011100000010 : Branch 0 (-3587761639/4000000 : ℚ) vp01110000001 := by
  apply branch_left_normalized (c:=vp011100000010) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-3587761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3587761639/2000000 : ℚ) by norm_num]
  exact coverp011100000010
private noncomputable def ep011100000011_0 : Blocks := edgeBlocks% "full/vectors/011100000011-E-0000.bin"
noncomputable def ep011100000011 : Blocks := ep011100000011_0
private theorem idp011100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110000001.list =
    C ((2:ℤ)^99) * horner X vp011100000011.list + horner X ep011100000011.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100000011 : Branch 1 (-3587761639/4000000 : ℚ) vp01110000001 := by
  apply branch_checked idp011100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3587761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3589761639/2000000 : ℚ) by norm_num]
  exact coverp011100000011
theorem coverp01110000001 : Covers (-3587761639/4000000 : ℚ) vp01110000001 := join_branches bp011100000010 bp011100000011
private noncomputable def vp011100000001_0 : Blocks := edgeBlocks% "full/vectors/011100000001-V-0000.bin"
noncomputable def vp011100000001 : Blocks := vp011100000001_0
theorem coverp011100000001 : Covers (-3585761639/2000000 : ℚ) vp011100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp011100000000_0 : Blocks := edgeBlocks% "full/vectors/011100000000-V-0000.bin"
noncomputable def vp011100000000 : Blocks := vp011100000000_0
theorem coverp011100000000 : Covers (-3583761639/2000000 : ℚ) vp011100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp01110000000_0 : Blocks := edgeBlocks% "full/vectors/01110000000-V-0000.bin"
noncomputable def vp01110000000 : Blocks := vp01110000000_0
private theorem bp011100000000 : Branch 0 (-3583761639/4000000 : ℚ) vp01110000000 := by
  apply branch_left_normalized (c:=vp011100000000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-3583761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3583761639/2000000 : ℚ) by norm_num]
  exact coverp011100000000
private noncomputable def ep011100000001_0 : Blocks := edgeBlocks% "full/vectors/011100000001-E-0000.bin"
noncomputable def ep011100000001 : Blocks := ep011100000001_0
private theorem idp011100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110000000.list =
    C ((2:ℤ)^98) * horner X vp011100000001.list + horner X ep011100000001.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100000001 : Branch 1 (-3583761639/4000000 : ℚ) vp01110000000 := by
  apply branch_checked idp011100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3583761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-3585761639/2000000 : ℚ) by norm_num]
  exact coverp011100000001
theorem coverp01110000000 : Covers (-3583761639/4000000 : ℚ) vp01110000000 := join_branches bp011100000000 bp011100000001
private noncomputable def vp0111000000_0 : Blocks := edgeBlocks% "full/vectors/0111000000-V-0000.bin"
private noncomputable def vp0111000000_1 : Blocks := edgeBlocks% "full/vectors/0111000000-V-0001.bin"
noncomputable def vp0111000000 : Blocks := (Blocks.join vp0111000000_0 vp0111000000_1)
private theorem bp01110000000 : Branch 0 (-3583761639/8000000 : ℚ) vp0111000000 := by
  apply branch_left_normalized (c:=vp01110000000) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-3583761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3583761639/4000000 : ℚ) by norm_num]
  exact coverp01110000000
private noncomputable def ep01110000001_0 : Blocks := edgeBlocks% "full/vectors/01110000001-E-0000.bin"
private noncomputable def ep01110000001_1 : Blocks := edgeBlocks% "full/vectors/01110000001-E-0001.bin"
noncomputable def ep01110000001 : Blocks := (Blocks.join ep01110000001_0 ep01110000001_1)
private theorem idp01110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111000000.list =
    C ((2:ℤ)^177) * horner X vp01110000001.list + horner X ep01110000001.list := by
  exact edge_identity (B := (2:ℤ)^324) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110000001 : Branch 1 (-3583761639/8000000 : ℚ) vp0111000000 := by
  apply branch_checked idp01110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3583761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3587761639/4000000 : ℚ) by norm_num]
  exact coverp01110000001
theorem coverp0111000000 : Covers (-3583761639/8000000 : ℚ) vp0111000000 := join_branches bp01110000000 bp01110000001
private noncomputable def vp011100000_0 : Blocks := edgeBlocks% "full/vectors/011100000-V-0000.bin"
private noncomputable def vp011100000_1 : Blocks := edgeBlocks% "full/vectors/011100000-V-0001.bin"
private noncomputable def vp011100000_2 : Blocks := edgeBlocks% "full/vectors/011100000-V-0002.bin"
noncomputable def vp011100000 : Blocks := (Blocks.join vp011100000_0 (Blocks.join vp011100000_1 vp011100000_2))
private theorem bp0111000000 : Branch 0 (-3583761639/16000000 : ℚ) vp011100000 := by
  apply branch_left_normalized (c:=vp0111000000) (k:=0) (m:=153) (by decide +kernel)
  rw [show 2*(-3583761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3583761639/8000000 : ℚ) by norm_num]
  exact coverp0111000000
private noncomputable def ep0111000001_0 : Blocks := edgeBlocks% "full/vectors/0111000001-E-0000.bin"
private noncomputable def ep0111000001_1 : Blocks := edgeBlocks% "full/vectors/0111000001-E-0001.bin"
private noncomputable def ep0111000001_2 : Blocks := edgeBlocks% "full/vectors/0111000001-E-0002.bin"
noncomputable def ep0111000001 : Blocks := (Blocks.join ep0111000001_0 (Blocks.join ep0111000001_1 ep0111000001_2))
private theorem idp0111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011100000.list =
    C ((2:ℤ)^329) * horner X vp0111000001.list + horner X ep0111000001.list := by
  exact edge_identity (B := (2:ℤ)^524) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111000001 : Branch 1 (-3583761639/16000000 : ℚ) vp011100000 := by
  apply branch_checked idp0111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3583761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3591761639/8000000 : ℚ) by norm_num]
  exact coverp0111000001
theorem coverp011100000 : Covers (-3583761639/16000000 : ℚ) vp011100000 := join_branches bp0111000000 bp0111000001
private noncomputable def vp01110000_0 : Blocks := edgeBlocks% "full/vectors/01110000-V-0000.bin"
private noncomputable def vp01110000_1 : Blocks := edgeBlocks% "full/vectors/01110000-V-0001.bin"
private noncomputable def vp01110000_2 : Blocks := edgeBlocks% "full/vectors/01110000-V-0002.bin"
private noncomputable def vp01110000_3 : Blocks := edgeBlocks% "full/vectors/01110000-V-0003.bin"
private noncomputable def vp01110000_4 : Blocks := edgeBlocks% "full/vectors/01110000-V-0004.bin"
noncomputable def vp01110000 : Blocks := (Blocks.join (Blocks.join vp01110000_0 vp01110000_1) (Blocks.join vp01110000_2 (Blocks.join vp01110000_3 vp01110000_4)))
private theorem bp011100000 : Branch 0 (-3583761639/32000000 : ℚ) vp01110000 := by
  apply branch_left_normalized (c:=vp011100000) (k:=0) (m:=283) (by decide +kernel)
  rw [show 2*(-3583761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3583761639/16000000 : ℚ) by norm_num]
  exact coverp011100000
private noncomputable def ep011100001_0 : Blocks := edgeBlocks% "full/vectors/011100001-E-0000.bin"
private noncomputable def ep011100001_1 : Blocks := edgeBlocks% "full/vectors/011100001-E-0001.bin"
private noncomputable def ep011100001_2 : Blocks := edgeBlocks% "full/vectors/011100001-E-0002.bin"
private noncomputable def ep011100001_3 : Blocks := edgeBlocks% "full/vectors/011100001-E-0003.bin"
private noncomputable def ep011100001_4 : Blocks := edgeBlocks% "full/vectors/011100001-E-0004.bin"
noncomputable def ep011100001 : Blocks := (Blocks.join (Blocks.join ep011100001_0 ep011100001_1) (Blocks.join ep011100001_2 (Blocks.join ep011100001_3 ep011100001_4)))
private theorem idp011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110000.list =
    C ((2:ℤ)^637) * horner X vp011100001.list + horner X ep011100001.list := by
  exact edge_identity (B := (2:ℤ)^924) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011100001 : Branch 1 (-3583761639/32000000 : ℚ) vp01110000 := by
  apply branch_checked idp011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3583761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3599761639/16000000 : ℚ) by norm_num]
  exact coverp011100001
theorem coverp01110000 : Covers (-3583761639/32000000 : ℚ) vp01110000 := join_branches bp011100000 bp011100001
private noncomputable def vp0111000_0 : Blocks := edgeBlocks% "full/vectors/0111000-V-0000.bin"
private noncomputable def vp0111000_1 : Blocks := edgeBlocks% "full/vectors/0111000-V-0001.bin"
private noncomputable def vp0111000_2 : Blocks := edgeBlocks% "full/vectors/0111000-V-0002.bin"
private noncomputable def vp0111000_3 : Blocks := edgeBlocks% "full/vectors/0111000-V-0003.bin"
private noncomputable def vp0111000_4 : Blocks := edgeBlocks% "full/vectors/0111000-V-0004.bin"
private noncomputable def vp0111000_5 : Blocks := edgeBlocks% "full/vectors/0111000-V-0005.bin"
private noncomputable def vp0111000_6 : Blocks := edgeBlocks% "full/vectors/0111000-V-0006.bin"
private noncomputable def vp0111000_7 : Blocks := edgeBlocks% "full/vectors/0111000-V-0007.bin"
private noncomputable def vp0111000_8 : Blocks := edgeBlocks% "full/vectors/0111000-V-0008.bin"
noncomputable def vp0111000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0111000_0 vp0111000_1) (Blocks.join vp0111000_2 vp0111000_3)) (Blocks.join (Blocks.join vp0111000_4 vp0111000_5) (Blocks.join vp0111000_6 (Blocks.join vp0111000_7 vp0111000_8))))
private theorem bp01110000 : Branch 0 (-3583761639/64000000 : ℚ) vp0111000 := by
  apply branch_left_normalized (c:=vp01110000) (k:=0) (m:=544) (by decide +kernel)
  rw [show 2*(-3583761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3583761639/32000000 : ℚ) by norm_num]
  exact coverp01110000
private noncomputable def ep01110001_0 : Blocks := edgeBlocks% "full/vectors/01110001-E-0000.bin"
private noncomputable def ep01110001_1 : Blocks := edgeBlocks% "full/vectors/01110001-E-0001.bin"
private noncomputable def ep01110001_2 : Blocks := edgeBlocks% "full/vectors/01110001-E-0002.bin"
private noncomputable def ep01110001_3 : Blocks := edgeBlocks% "full/vectors/01110001-E-0003.bin"
private noncomputable def ep01110001_4 : Blocks := edgeBlocks% "full/vectors/01110001-E-0004.bin"
private noncomputable def ep01110001_5 : Blocks := edgeBlocks% "full/vectors/01110001-E-0005.bin"
private noncomputable def ep01110001_6 : Blocks := edgeBlocks% "full/vectors/01110001-E-0006.bin"
private noncomputable def ep01110001_7 : Blocks := edgeBlocks% "full/vectors/01110001-E-0007.bin"
private noncomputable def ep01110001_8 : Blocks := edgeBlocks% "full/vectors/01110001-E-0008.bin"
noncomputable def ep01110001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01110001_0 ep01110001_1) (Blocks.join ep01110001_2 ep01110001_3)) (Blocks.join (Blocks.join ep01110001_4 ep01110001_5) (Blocks.join ep01110001_6 (Blocks.join ep01110001_7 ep01110001_8))))
private theorem idp01110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111000.list =
    C ((2:ℤ)^1242) * horner X vp01110001.list + horner X ep01110001.list := by
  exact edge_identity (B := (2:ℤ)^1714) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01110001 : Branch 1 (-3583761639/64000000 : ℚ) vp0111000 := by
  apply branch_checked idp01110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3583761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3615761639/32000000 : ℚ) by norm_num]
  exact coverp01110001
theorem coverp0111000 : Covers (-3583761639/64000000 : ℚ) vp0111000 := join_branches bp01110000 bp01110001
private noncomputable def vp011100_0 : Blocks := edgeBlocks% "full/vectors/011100-V-0000.bin"
private noncomputable def vp011100_1 : Blocks := edgeBlocks% "full/vectors/011100-V-0001.bin"
private noncomputable def vp011100_2 : Blocks := edgeBlocks% "full/vectors/011100-V-0002.bin"
private noncomputable def vp011100_3 : Blocks := edgeBlocks% "full/vectors/011100-V-0003.bin"
private noncomputable def vp011100_4 : Blocks := edgeBlocks% "full/vectors/011100-V-0004.bin"
private noncomputable def vp011100_5 : Blocks := edgeBlocks% "full/vectors/011100-V-0005.bin"
private noncomputable def vp011100_6 : Blocks := edgeBlocks% "full/vectors/011100-V-0006.bin"
private noncomputable def vp011100_7 : Blocks := edgeBlocks% "full/vectors/011100-V-0007.bin"
private noncomputable def vp011100_8 : Blocks := edgeBlocks% "full/vectors/011100-V-0008.bin"
private noncomputable def vp011100_9 : Blocks := edgeBlocks% "full/vectors/011100-V-0009.bin"
private noncomputable def vp011100_10 : Blocks := edgeBlocks% "full/vectors/011100-V-0010.bin"
private noncomputable def vp011100_11 : Blocks := edgeBlocks% "full/vectors/011100-V-0011.bin"
private noncomputable def vp011100_12 : Blocks := edgeBlocks% "full/vectors/011100-V-0012.bin"
private noncomputable def vp011100_13 : Blocks := edgeBlocks% "full/vectors/011100-V-0013.bin"
private noncomputable def vp011100_14 : Blocks := edgeBlocks% "full/vectors/011100-V-0014.bin"
private noncomputable def vp011100_15 : Blocks := edgeBlocks% "full/vectors/011100-V-0015.bin"
private noncomputable def vp011100_16 : Blocks := edgeBlocks% "full/vectors/011100-V-0016.bin"
noncomputable def vp011100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp011100_0 vp011100_1) (Blocks.join vp011100_2 vp011100_3)) (Blocks.join (Blocks.join vp011100_4 vp011100_5) (Blocks.join vp011100_6 vp011100_7))) (Blocks.join (Blocks.join (Blocks.join vp011100_8 vp011100_9) (Blocks.join vp011100_10 vp011100_11)) (Blocks.join (Blocks.join vp011100_12 vp011100_13) (Blocks.join vp011100_14 (Blocks.join vp011100_15 vp011100_16)))))
private theorem bp0111000 : Branch 0 (-3583761639/128000000 : ℚ) vp011100 := by
  apply branch_left_normalized (c:=vp0111000) (k:=0) (m:=1057) (by decide +kernel)
  rw [show 2*(-3583761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-3583761639/64000000 : ℚ) by norm_num]
  exact coverp0111000
private noncomputable def ep0111001_0 : Blocks := edgeBlocks% "full/vectors/0111001-E-0000.bin"
private noncomputable def ep0111001_1 : Blocks := edgeBlocks% "full/vectors/0111001-E-0001.bin"
private noncomputable def ep0111001_2 : Blocks := edgeBlocks% "full/vectors/0111001-E-0002.bin"
private noncomputable def ep0111001_3 : Blocks := edgeBlocks% "full/vectors/0111001-E-0003.bin"
private noncomputable def ep0111001_4 : Blocks := edgeBlocks% "full/vectors/0111001-E-0004.bin"
private noncomputable def ep0111001_5 : Blocks := edgeBlocks% "full/vectors/0111001-E-0005.bin"
private noncomputable def ep0111001_6 : Blocks := edgeBlocks% "full/vectors/0111001-E-0006.bin"
private noncomputable def ep0111001_7 : Blocks := edgeBlocks% "full/vectors/0111001-E-0007.bin"
private noncomputable def ep0111001_8 : Blocks := edgeBlocks% "full/vectors/0111001-E-0008.bin"
private noncomputable def ep0111001_9 : Blocks := edgeBlocks% "full/vectors/0111001-E-0009.bin"
private noncomputable def ep0111001_10 : Blocks := edgeBlocks% "full/vectors/0111001-E-0010.bin"
private noncomputable def ep0111001_11 : Blocks := edgeBlocks% "full/vectors/0111001-E-0011.bin"
private noncomputable def ep0111001_12 : Blocks := edgeBlocks% "full/vectors/0111001-E-0012.bin"
private noncomputable def ep0111001_13 : Blocks := edgeBlocks% "full/vectors/0111001-E-0013.bin"
private noncomputable def ep0111001_14 : Blocks := edgeBlocks% "full/vectors/0111001-E-0014.bin"
private noncomputable def ep0111001_15 : Blocks := edgeBlocks% "full/vectors/0111001-E-0015.bin"
private noncomputable def ep0111001_16 : Blocks := edgeBlocks% "full/vectors/0111001-E-0016.bin"
noncomputable def ep0111001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0111001_0 ep0111001_1) (Blocks.join ep0111001_2 ep0111001_3)) (Blocks.join (Blocks.join ep0111001_4 ep0111001_5) (Blocks.join ep0111001_6 ep0111001_7))) (Blocks.join (Blocks.join (Blocks.join ep0111001_8 ep0111001_9) (Blocks.join ep0111001_10 ep0111001_11)) (Blocks.join (Blocks.join ep0111001_12 ep0111001_13) (Blocks.join ep0111001_14 (Blocks.join ep0111001_15 ep0111001_16)))))
private theorem idp0111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011100.list =
    C ((2:ℤ)^2429) * horner X vp0111001.list + horner X ep0111001.list := by
  exact edge_identity (B := (2:ℤ)^3264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111001 : Branch 1 (-3583761639/128000000 : ℚ) vp011100 := by
  apply branch_checked idp0111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3583761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-3647761639/64000000 : ℚ) by norm_num]
  exact coverp0111001
theorem coverp011100 : Covers (-3583761639/128000000 : ℚ) vp011100 := join_branches bp0111000 bp0111001
private noncomputable def vp01110_0 : Blocks := edgeBlocks% "full/vectors/01110-V-0000.bin"
private noncomputable def vp01110_1 : Blocks := edgeBlocks% "full/vectors/01110-V-0001.bin"
private noncomputable def vp01110_2 : Blocks := edgeBlocks% "full/vectors/01110-V-0002.bin"
private noncomputable def vp01110_3 : Blocks := edgeBlocks% "full/vectors/01110-V-0003.bin"
private noncomputable def vp01110_4 : Blocks := edgeBlocks% "full/vectors/01110-V-0004.bin"
private noncomputable def vp01110_5 : Blocks := edgeBlocks% "full/vectors/01110-V-0005.bin"
private noncomputable def vp01110_6 : Blocks := edgeBlocks% "full/vectors/01110-V-0006.bin"
private noncomputable def vp01110_7 : Blocks := edgeBlocks% "full/vectors/01110-V-0007.bin"
private noncomputable def vp01110_8 : Blocks := edgeBlocks% "full/vectors/01110-V-0008.bin"
private noncomputable def vp01110_9 : Blocks := edgeBlocks% "full/vectors/01110-V-0009.bin"
private noncomputable def vp01110_10 : Blocks := edgeBlocks% "full/vectors/01110-V-0010.bin"
private noncomputable def vp01110_11 : Blocks := edgeBlocks% "full/vectors/01110-V-0011.bin"
private noncomputable def vp01110_12 : Blocks := edgeBlocks% "full/vectors/01110-V-0012.bin"
private noncomputable def vp01110_13 : Blocks := edgeBlocks% "full/vectors/01110-V-0013.bin"
private noncomputable def vp01110_14 : Blocks := edgeBlocks% "full/vectors/01110-V-0014.bin"
private noncomputable def vp01110_15 : Blocks := edgeBlocks% "full/vectors/01110-V-0015.bin"
private noncomputable def vp01110_16 : Blocks := edgeBlocks% "full/vectors/01110-V-0016.bin"
private noncomputable def vp01110_17 : Blocks := edgeBlocks% "full/vectors/01110-V-0017.bin"
private noncomputable def vp01110_18 : Blocks := edgeBlocks% "full/vectors/01110-V-0018.bin"
private noncomputable def vp01110_19 : Blocks := edgeBlocks% "full/vectors/01110-V-0019.bin"
private noncomputable def vp01110_20 : Blocks := edgeBlocks% "full/vectors/01110-V-0020.bin"
private noncomputable def vp01110_21 : Blocks := edgeBlocks% "full/vectors/01110-V-0021.bin"
private noncomputable def vp01110_22 : Blocks := edgeBlocks% "full/vectors/01110-V-0022.bin"
private noncomputable def vp01110_23 : Blocks := edgeBlocks% "full/vectors/01110-V-0023.bin"
private noncomputable def vp01110_24 : Blocks := edgeBlocks% "full/vectors/01110-V-0024.bin"
private noncomputable def vp01110_25 : Blocks := edgeBlocks% "full/vectors/01110-V-0025.bin"
private noncomputable def vp01110_26 : Blocks := edgeBlocks% "full/vectors/01110-V-0026.bin"
private noncomputable def vp01110_27 : Blocks := edgeBlocks% "full/vectors/01110-V-0027.bin"
private noncomputable def vp01110_28 : Blocks := edgeBlocks% "full/vectors/01110-V-0028.bin"
private noncomputable def vp01110_29 : Blocks := edgeBlocks% "full/vectors/01110-V-0029.bin"
private noncomputable def vp01110_30 : Blocks := edgeBlocks% "full/vectors/01110-V-0030.bin"
noncomputable def vp01110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01110_0 (Blocks.join vp01110_1 vp01110_2)) (Blocks.join (Blocks.join vp01110_3 vp01110_4) (Blocks.join vp01110_5 vp01110_6))) (Blocks.join (Blocks.join (Blocks.join vp01110_7 vp01110_8) (Blocks.join vp01110_9 vp01110_10)) (Blocks.join (Blocks.join vp01110_11 vp01110_12) (Blocks.join vp01110_13 vp01110_14)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01110_15 vp01110_16) (Blocks.join vp01110_17 vp01110_18)) (Blocks.join (Blocks.join vp01110_19 vp01110_20) (Blocks.join vp01110_21 vp01110_22))) (Blocks.join (Blocks.join (Blocks.join vp01110_23 vp01110_24) (Blocks.join vp01110_25 vp01110_26)) (Blocks.join (Blocks.join vp01110_27 vp01110_28) (Blocks.join vp01110_29 vp01110_30)))))
private theorem bp011100 : Branch 0 (-3583761639/256000000 : ℚ) vp01110 := by
  apply branch_left_normalized (c:=vp011100) (k:=0) (m:=2059) (by decide +kernel)
  rw [show 2*(-3583761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-3583761639/128000000 : ℚ) by norm_num]
  exact coverp011100
private noncomputable def ep011101_0 : Blocks := edgeBlocks% "full/vectors/011101-E-0000.bin"
private noncomputable def ep011101_1 : Blocks := edgeBlocks% "full/vectors/011101-E-0001.bin"
private noncomputable def ep011101_2 : Blocks := edgeBlocks% "full/vectors/011101-E-0002.bin"
private noncomputable def ep011101_3 : Blocks := edgeBlocks% "full/vectors/011101-E-0003.bin"
private noncomputable def ep011101_4 : Blocks := edgeBlocks% "full/vectors/011101-E-0004.bin"
private noncomputable def ep011101_5 : Blocks := edgeBlocks% "full/vectors/011101-E-0005.bin"
private noncomputable def ep011101_6 : Blocks := edgeBlocks% "full/vectors/011101-E-0006.bin"
private noncomputable def ep011101_7 : Blocks := edgeBlocks% "full/vectors/011101-E-0007.bin"
private noncomputable def ep011101_8 : Blocks := edgeBlocks% "full/vectors/011101-E-0008.bin"
private noncomputable def ep011101_9 : Blocks := edgeBlocks% "full/vectors/011101-E-0009.bin"
private noncomputable def ep011101_10 : Blocks := edgeBlocks% "full/vectors/011101-E-0010.bin"
private noncomputable def ep011101_11 : Blocks := edgeBlocks% "full/vectors/011101-E-0011.bin"
private noncomputable def ep011101_12 : Blocks := edgeBlocks% "full/vectors/011101-E-0012.bin"
private noncomputable def ep011101_13 : Blocks := edgeBlocks% "full/vectors/011101-E-0013.bin"
private noncomputable def ep011101_14 : Blocks := edgeBlocks% "full/vectors/011101-E-0014.bin"
private noncomputable def ep011101_15 : Blocks := edgeBlocks% "full/vectors/011101-E-0015.bin"
private noncomputable def ep011101_16 : Blocks := edgeBlocks% "full/vectors/011101-E-0016.bin"
private noncomputable def ep011101_17 : Blocks := edgeBlocks% "full/vectors/011101-E-0017.bin"
private noncomputable def ep011101_18 : Blocks := edgeBlocks% "full/vectors/011101-E-0018.bin"
private noncomputable def ep011101_19 : Blocks := edgeBlocks% "full/vectors/011101-E-0019.bin"
private noncomputable def ep011101_20 : Blocks := edgeBlocks% "full/vectors/011101-E-0020.bin"
private noncomputable def ep011101_21 : Blocks := edgeBlocks% "full/vectors/011101-E-0021.bin"
private noncomputable def ep011101_22 : Blocks := edgeBlocks% "full/vectors/011101-E-0022.bin"
private noncomputable def ep011101_23 : Blocks := edgeBlocks% "full/vectors/011101-E-0023.bin"
private noncomputable def ep011101_24 : Blocks := edgeBlocks% "full/vectors/011101-E-0024.bin"
private noncomputable def ep011101_25 : Blocks := edgeBlocks% "full/vectors/011101-E-0025.bin"
private noncomputable def ep011101_26 : Blocks := edgeBlocks% "full/vectors/011101-E-0026.bin"
private noncomputable def ep011101_27 : Blocks := edgeBlocks% "full/vectors/011101-E-0027.bin"
private noncomputable def ep011101_28 : Blocks := edgeBlocks% "full/vectors/011101-E-0028.bin"
private noncomputable def ep011101_29 : Blocks := edgeBlocks% "full/vectors/011101-E-0029.bin"
private noncomputable def ep011101_30 : Blocks := edgeBlocks% "full/vectors/011101-E-0030.bin"
noncomputable def ep011101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep011101_0 (Blocks.join ep011101_1 ep011101_2)) (Blocks.join (Blocks.join ep011101_3 ep011101_4) (Blocks.join ep011101_5 ep011101_6))) (Blocks.join (Blocks.join (Blocks.join ep011101_7 ep011101_8) (Blocks.join ep011101_9 ep011101_10)) (Blocks.join (Blocks.join ep011101_11 ep011101_12) (Blocks.join ep011101_13 ep011101_14)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep011101_15 ep011101_16) (Blocks.join ep011101_17 ep011101_18)) (Blocks.join (Blocks.join ep011101_19 ep011101_20) (Blocks.join ep011101_21 ep011101_22))) (Blocks.join (Blocks.join (Blocks.join ep011101_23 ep011101_24) (Blocks.join ep011101_25 ep011101_26)) (Blocks.join (Blocks.join ep011101_27 ep011101_28) (Blocks.join ep011101_29 ep011101_30)))))
private def ptsp011101 : List ℤ := [((2:ℤ)^3028+0),((2:ℤ)^3028+1),((2:ℤ)^3028+2)]
private theorem boundp011101 : 2^vp01110.size*absSum vp01110.list + ((2:ℤ)^4704*absSum vp011101.list+absSum ep011101.list) < (2:ℤ)^6244 := by decide +kernel
private theorem pointp011101_0 : fastHom 1 ((2:ℤ)^3028+0) vp01110 = ((2:ℤ)^4704)*vp011101.subst ((2:ℤ)^3028+0)+ep011101.subst ((2:ℤ)^3028+0) := by decide +kernel
private theorem pointp011101_1 : fastHom 1 ((2:ℤ)^3028+1) vp01110 = ((2:ℤ)^4704)*vp011101.subst ((2:ℤ)^3028+1)+ep011101.subst ((2:ℤ)^3028+1) := by decide +kernel
private theorem pointp011101_2 : fastHom 1 ((2:ℤ)^3028+2) vp01110 = ((2:ℤ)^4704)*vp011101.subst ((2:ℤ)^3028+2)+ep011101.subst ((2:ℤ)^3028+2) := by decide +kernel
private theorem checkp011101 (x:ℤ) (hx:x ∈ ptsp011101) : fastHom 1 x vp01110 = ((2:ℤ)^4704)*vp011101.subst x+ep011101.subst x := by
  simp only [ptsp011101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact pointp011101_0
  · exact pointp011101_1
  · exact pointp011101_2
private theorem idp011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01110.list =
    C ((2:ℤ)^4704) * horner X vp011101.list + horner X ep011101.list := by
  apply edge_identity (B := (2:ℤ)^6244) (by decide) (by positivity) (by positivity) boundp011101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp011101 (by decide +kernel)
  · have h : ptsp011101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp011101.trans_le (by decide +kernel)
  · exact checkp011101
private theorem bp011101 : Branch 1 (-3583761639/256000000 : ℚ) vp01110 := by
  apply branch_checked idp011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3583761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-3711761639/128000000 : ℚ) by norm_num]
  exact coverp011101
theorem coverp01110 : Covers (-3583761639/256000000 : ℚ) vp01110 := join_branches bp011100 bp011101
private noncomputable def vp0111_0 : Blocks := edgeBlocks% "full/vectors/0111-V-0000.bin"
private noncomputable def vp0111_1 : Blocks := edgeBlocks% "full/vectors/0111-V-0001.bin"
private noncomputable def vp0111_2 : Blocks := edgeBlocks% "full/vectors/0111-V-0002.bin"
private noncomputable def vp0111_3 : Blocks := edgeBlocks% "full/vectors/0111-V-0003.bin"
private noncomputable def vp0111_4 : Blocks := edgeBlocks% "full/vectors/0111-V-0004.bin"
private noncomputable def vp0111_5 : Blocks := edgeBlocks% "full/vectors/0111-V-0005.bin"
private noncomputable def vp0111_6 : Blocks := edgeBlocks% "full/vectors/0111-V-0006.bin"
private noncomputable def vp0111_7 : Blocks := edgeBlocks% "full/vectors/0111-V-0007.bin"
private noncomputable def vp0111_8 : Blocks := edgeBlocks% "full/vectors/0111-V-0008.bin"
private noncomputable def vp0111_9 : Blocks := edgeBlocks% "full/vectors/0111-V-0009.bin"
private noncomputable def vp0111_10 : Blocks := edgeBlocks% "full/vectors/0111-V-0010.bin"
private noncomputable def vp0111_11 : Blocks := edgeBlocks% "full/vectors/0111-V-0011.bin"
private noncomputable def vp0111_12 : Blocks := edgeBlocks% "full/vectors/0111-V-0012.bin"
private noncomputable def vp0111_13 : Blocks := edgeBlocks% "full/vectors/0111-V-0013.bin"
private noncomputable def vp0111_14 : Blocks := edgeBlocks% "full/vectors/0111-V-0014.bin"
private noncomputable def vp0111_15 : Blocks := edgeBlocks% "full/vectors/0111-V-0015.bin"
private noncomputable def vp0111_16 : Blocks := edgeBlocks% "full/vectors/0111-V-0016.bin"
private noncomputable def vp0111_17 : Blocks := edgeBlocks% "full/vectors/0111-V-0017.bin"
private noncomputable def vp0111_18 : Blocks := edgeBlocks% "full/vectors/0111-V-0018.bin"
private noncomputable def vp0111_19 : Blocks := edgeBlocks% "full/vectors/0111-V-0019.bin"
private noncomputable def vp0111_20 : Blocks := edgeBlocks% "full/vectors/0111-V-0020.bin"
private noncomputable def vp0111_21 : Blocks := edgeBlocks% "full/vectors/0111-V-0021.bin"
private noncomputable def vp0111_22 : Blocks := edgeBlocks% "full/vectors/0111-V-0022.bin"
private noncomputable def vp0111_23 : Blocks := edgeBlocks% "full/vectors/0111-V-0023.bin"
private noncomputable def vp0111_24 : Blocks := edgeBlocks% "full/vectors/0111-V-0024.bin"
private noncomputable def vp0111_25 : Blocks := edgeBlocks% "full/vectors/0111-V-0025.bin"
private noncomputable def vp0111_26 : Blocks := edgeBlocks% "full/vectors/0111-V-0026.bin"
private noncomputable def vp0111_27 : Blocks := edgeBlocks% "full/vectors/0111-V-0027.bin"
private noncomputable def vp0111_28 : Blocks := edgeBlocks% "full/vectors/0111-V-0028.bin"
private noncomputable def vp0111_29 : Blocks := edgeBlocks% "full/vectors/0111-V-0029.bin"
private noncomputable def vp0111_30 : Blocks := edgeBlocks% "full/vectors/0111-V-0030.bin"
private noncomputable def vp0111_31 : Blocks := edgeBlocks% "full/vectors/0111-V-0031.bin"
private noncomputable def vp0111_32 : Blocks := edgeBlocks% "full/vectors/0111-V-0032.bin"
private noncomputable def vp0111_33 : Blocks := edgeBlocks% "full/vectors/0111-V-0033.bin"
private noncomputable def vp0111_34 : Blocks := edgeBlocks% "full/vectors/0111-V-0034.bin"
private noncomputable def vp0111_35 : Blocks := edgeBlocks% "full/vectors/0111-V-0035.bin"
private noncomputable def vp0111_36 : Blocks := edgeBlocks% "full/vectors/0111-V-0036.bin"
private noncomputable def vp0111_37 : Blocks := edgeBlocks% "full/vectors/0111-V-0037.bin"
private noncomputable def vp0111_38 : Blocks := edgeBlocks% "full/vectors/0111-V-0038.bin"
private noncomputable def vp0111_39 : Blocks := edgeBlocks% "full/vectors/0111-V-0039.bin"
private noncomputable def vp0111_40 : Blocks := edgeBlocks% "full/vectors/0111-V-0040.bin"
private noncomputable def vp0111_41 : Blocks := edgeBlocks% "full/vectors/0111-V-0041.bin"
private noncomputable def vp0111_42 : Blocks := edgeBlocks% "full/vectors/0111-V-0042.bin"
private noncomputable def vp0111_43 : Blocks := edgeBlocks% "full/vectors/0111-V-0043.bin"
private noncomputable def vp0111_44 : Blocks := edgeBlocks% "full/vectors/0111-V-0044.bin"
private noncomputable def vp0111_45 : Blocks := edgeBlocks% "full/vectors/0111-V-0045.bin"
private noncomputable def vp0111_46 : Blocks := edgeBlocks% "full/vectors/0111-V-0046.bin"
private noncomputable def vp0111_47 : Blocks := edgeBlocks% "full/vectors/0111-V-0047.bin"
private noncomputable def vp0111_48 : Blocks := edgeBlocks% "full/vectors/0111-V-0048.bin"
private noncomputable def vp0111_49 : Blocks := edgeBlocks% "full/vectors/0111-V-0049.bin"
private noncomputable def vp0111_50 : Blocks := edgeBlocks% "full/vectors/0111-V-0050.bin"
private noncomputable def vp0111_51 : Blocks := edgeBlocks% "full/vectors/0111-V-0051.bin"
private noncomputable def vp0111_52 : Blocks := edgeBlocks% "full/vectors/0111-V-0052.bin"
private noncomputable def vp0111_53 : Blocks := edgeBlocks% "full/vectors/0111-V-0053.bin"
private noncomputable def vp0111_54 : Blocks := edgeBlocks% "full/vectors/0111-V-0054.bin"
private noncomputable def vp0111_55 : Blocks := edgeBlocks% "full/vectors/0111-V-0055.bin"
private noncomputable def vp0111_56 : Blocks := edgeBlocks% "full/vectors/0111-V-0056.bin"
private noncomputable def vp0111_57 : Blocks := edgeBlocks% "full/vectors/0111-V-0057.bin"
noncomputable def vp0111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0111_0 (Blocks.join vp0111_1 vp0111_2)) (Blocks.join (Blocks.join vp0111_3 vp0111_4) (Blocks.join vp0111_5 vp0111_6))) (Blocks.join (Blocks.join vp0111_7 (Blocks.join vp0111_8 vp0111_9)) (Blocks.join (Blocks.join vp0111_10 vp0111_11) (Blocks.join vp0111_12 vp0111_13)))) (Blocks.join (Blocks.join (Blocks.join vp0111_14 (Blocks.join vp0111_15 vp0111_16)) (Blocks.join (Blocks.join vp0111_17 vp0111_18) (Blocks.join vp0111_19 vp0111_20))) (Blocks.join (Blocks.join (Blocks.join vp0111_21 vp0111_22) (Blocks.join vp0111_23 vp0111_24)) (Blocks.join (Blocks.join vp0111_25 vp0111_26) (Blocks.join vp0111_27 vp0111_28))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0111_29 (Blocks.join vp0111_30 vp0111_31)) (Blocks.join (Blocks.join vp0111_32 vp0111_33) (Blocks.join vp0111_34 vp0111_35))) (Blocks.join (Blocks.join vp0111_36 (Blocks.join vp0111_37 vp0111_38)) (Blocks.join (Blocks.join vp0111_39 vp0111_40) (Blocks.join vp0111_41 vp0111_42)))) (Blocks.join (Blocks.join (Blocks.join vp0111_43 (Blocks.join vp0111_44 vp0111_45)) (Blocks.join (Blocks.join vp0111_46 vp0111_47) (Blocks.join vp0111_48 vp0111_49))) (Blocks.join (Blocks.join (Blocks.join vp0111_50 vp0111_51) (Blocks.join vp0111_52 vp0111_53)) (Blocks.join (Blocks.join vp0111_54 vp0111_55) (Blocks.join vp0111_56 vp0111_57))))))
private theorem bp01110 : Branch 0 (-3583761639/512000000 : ℚ) vp0111 := by
  apply branch_left_normalized (c:=vp01110) (k:=0) (m:=3961) (by decide +kernel)
  rw [show 2*(-3583761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-3583761639/256000000 : ℚ) by norm_num]
  exact coverp01110
private noncomputable def ep01111_0 : Blocks := edgeBlocks% "full/vectors/01111-E-0000.bin"
private noncomputable def ep01111_1 : Blocks := edgeBlocks% "full/vectors/01111-E-0001.bin"
private noncomputable def ep01111_2 : Blocks := edgeBlocks% "full/vectors/01111-E-0002.bin"
private noncomputable def ep01111_3 : Blocks := edgeBlocks% "full/vectors/01111-E-0003.bin"
private noncomputable def ep01111_4 : Blocks := edgeBlocks% "full/vectors/01111-E-0004.bin"
private noncomputable def ep01111_5 : Blocks := edgeBlocks% "full/vectors/01111-E-0005.bin"
private noncomputable def ep01111_6 : Blocks := edgeBlocks% "full/vectors/01111-E-0006.bin"
private noncomputable def ep01111_7 : Blocks := edgeBlocks% "full/vectors/01111-E-0007.bin"
private noncomputable def ep01111_8 : Blocks := edgeBlocks% "full/vectors/01111-E-0008.bin"
private noncomputable def ep01111_9 : Blocks := edgeBlocks% "full/vectors/01111-E-0009.bin"
private noncomputable def ep01111_10 : Blocks := edgeBlocks% "full/vectors/01111-E-0010.bin"
private noncomputable def ep01111_11 : Blocks := edgeBlocks% "full/vectors/01111-E-0011.bin"
private noncomputable def ep01111_12 : Blocks := edgeBlocks% "full/vectors/01111-E-0012.bin"
private noncomputable def ep01111_13 : Blocks := edgeBlocks% "full/vectors/01111-E-0013.bin"
private noncomputable def ep01111_14 : Blocks := edgeBlocks% "full/vectors/01111-E-0014.bin"
private noncomputable def ep01111_15 : Blocks := edgeBlocks% "full/vectors/01111-E-0015.bin"
private noncomputable def ep01111_16 : Blocks := edgeBlocks% "full/vectors/01111-E-0016.bin"
private noncomputable def ep01111_17 : Blocks := edgeBlocks% "full/vectors/01111-E-0017.bin"
private noncomputable def ep01111_18 : Blocks := edgeBlocks% "full/vectors/01111-E-0018.bin"
private noncomputable def ep01111_19 : Blocks := edgeBlocks% "full/vectors/01111-E-0019.bin"
private noncomputable def ep01111_20 : Blocks := edgeBlocks% "full/vectors/01111-E-0020.bin"
private noncomputable def ep01111_21 : Blocks := edgeBlocks% "full/vectors/01111-E-0021.bin"
private noncomputable def ep01111_22 : Blocks := edgeBlocks% "full/vectors/01111-E-0022.bin"
private noncomputable def ep01111_23 : Blocks := edgeBlocks% "full/vectors/01111-E-0023.bin"
private noncomputable def ep01111_24 : Blocks := edgeBlocks% "full/vectors/01111-E-0024.bin"
private noncomputable def ep01111_25 : Blocks := edgeBlocks% "full/vectors/01111-E-0025.bin"
private noncomputable def ep01111_26 : Blocks := edgeBlocks% "full/vectors/01111-E-0026.bin"
private noncomputable def ep01111_27 : Blocks := edgeBlocks% "full/vectors/01111-E-0027.bin"
private noncomputable def ep01111_28 : Blocks := edgeBlocks% "full/vectors/01111-E-0028.bin"
private noncomputable def ep01111_29 : Blocks := edgeBlocks% "full/vectors/01111-E-0029.bin"
private noncomputable def ep01111_30 : Blocks := edgeBlocks% "full/vectors/01111-E-0030.bin"
private noncomputable def ep01111_31 : Blocks := edgeBlocks% "full/vectors/01111-E-0031.bin"
private noncomputable def ep01111_32 : Blocks := edgeBlocks% "full/vectors/01111-E-0032.bin"
private noncomputable def ep01111_33 : Blocks := edgeBlocks% "full/vectors/01111-E-0033.bin"
private noncomputable def ep01111_34 : Blocks := edgeBlocks% "full/vectors/01111-E-0034.bin"
private noncomputable def ep01111_35 : Blocks := edgeBlocks% "full/vectors/01111-E-0035.bin"
private noncomputable def ep01111_36 : Blocks := edgeBlocks% "full/vectors/01111-E-0036.bin"
private noncomputable def ep01111_37 : Blocks := edgeBlocks% "full/vectors/01111-E-0037.bin"
private noncomputable def ep01111_38 : Blocks := edgeBlocks% "full/vectors/01111-E-0038.bin"
private noncomputable def ep01111_39 : Blocks := edgeBlocks% "full/vectors/01111-E-0039.bin"
private noncomputable def ep01111_40 : Blocks := edgeBlocks% "full/vectors/01111-E-0040.bin"
private noncomputable def ep01111_41 : Blocks := edgeBlocks% "full/vectors/01111-E-0041.bin"
private noncomputable def ep01111_42 : Blocks := edgeBlocks% "full/vectors/01111-E-0042.bin"
private noncomputable def ep01111_43 : Blocks := edgeBlocks% "full/vectors/01111-E-0043.bin"
private noncomputable def ep01111_44 : Blocks := edgeBlocks% "full/vectors/01111-E-0044.bin"
private noncomputable def ep01111_45 : Blocks := edgeBlocks% "full/vectors/01111-E-0045.bin"
private noncomputable def ep01111_46 : Blocks := edgeBlocks% "full/vectors/01111-E-0046.bin"
private noncomputable def ep01111_47 : Blocks := edgeBlocks% "full/vectors/01111-E-0047.bin"
private noncomputable def ep01111_48 : Blocks := edgeBlocks% "full/vectors/01111-E-0048.bin"
private noncomputable def ep01111_49 : Blocks := edgeBlocks% "full/vectors/01111-E-0049.bin"
private noncomputable def ep01111_50 : Blocks := edgeBlocks% "full/vectors/01111-E-0050.bin"
private noncomputable def ep01111_51 : Blocks := edgeBlocks% "full/vectors/01111-E-0051.bin"
private noncomputable def ep01111_52 : Blocks := edgeBlocks% "full/vectors/01111-E-0052.bin"
private noncomputable def ep01111_53 : Blocks := edgeBlocks% "full/vectors/01111-E-0053.bin"
private noncomputable def ep01111_54 : Blocks := edgeBlocks% "full/vectors/01111-E-0054.bin"
private noncomputable def ep01111_55 : Blocks := edgeBlocks% "full/vectors/01111-E-0055.bin"
private noncomputable def ep01111_56 : Blocks := edgeBlocks% "full/vectors/01111-E-0056.bin"
private noncomputable def ep01111_57 : Blocks := edgeBlocks% "full/vectors/01111-E-0057.bin"
noncomputable def ep01111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01111_0 (Blocks.join ep01111_1 ep01111_2)) (Blocks.join (Blocks.join ep01111_3 ep01111_4) (Blocks.join ep01111_5 ep01111_6))) (Blocks.join (Blocks.join ep01111_7 (Blocks.join ep01111_8 ep01111_9)) (Blocks.join (Blocks.join ep01111_10 ep01111_11) (Blocks.join ep01111_12 ep01111_13)))) (Blocks.join (Blocks.join (Blocks.join ep01111_14 (Blocks.join ep01111_15 ep01111_16)) (Blocks.join (Blocks.join ep01111_17 ep01111_18) (Blocks.join ep01111_19 ep01111_20))) (Blocks.join (Blocks.join (Blocks.join ep01111_21 ep01111_22) (Blocks.join ep01111_23 ep01111_24)) (Blocks.join (Blocks.join ep01111_25 ep01111_26) (Blocks.join ep01111_27 ep01111_28))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep01111_29 (Blocks.join ep01111_30 ep01111_31)) (Blocks.join (Blocks.join ep01111_32 ep01111_33) (Blocks.join ep01111_34 ep01111_35))) (Blocks.join (Blocks.join ep01111_36 (Blocks.join ep01111_37 ep01111_38)) (Blocks.join (Blocks.join ep01111_39 ep01111_40) (Blocks.join ep01111_41 ep01111_42)))) (Blocks.join (Blocks.join (Blocks.join ep01111_43 (Blocks.join ep01111_44 ep01111_45)) (Blocks.join (Blocks.join ep01111_46 ep01111_47) (Blocks.join ep01111_48 ep01111_49))) (Blocks.join (Blocks.join (Blocks.join ep01111_50 ep01111_51) (Blocks.join ep01111_52 ep01111_53)) (Blocks.join (Blocks.join ep01111_54 ep01111_55) (Blocks.join ep01111_56 ep01111_57))))))
private def ptsp01111 : List ℤ := [((2:ℤ)^1626+0),((2:ℤ)^1626+1),((2:ℤ)^1626+2),((2:ℤ)^1626+3),((2:ℤ)^1626+4),((2:ℤ)^1626+5),((2:ℤ)^1626+6),((2:ℤ)^1626+7)]
private theorem boundp01111 : 2^vp0111.size*absSum vp0111.list + ((2:ℤ)^8856*absSum vp01111.list+absSum ep01111.list) < (2:ℤ)^11742 := by decide +kernel
private theorem pointp01111_0 : fastHom 1 ((2:ℤ)^1626+0) vp0111 = ((2:ℤ)^8856)*vp01111.subst ((2:ℤ)^1626+0)+ep01111.subst ((2:ℤ)^1626+0) := by decide +kernel
private theorem pointp01111_1 : fastHom 1 ((2:ℤ)^1626+1) vp0111 = ((2:ℤ)^8856)*vp01111.subst ((2:ℤ)^1626+1)+ep01111.subst ((2:ℤ)^1626+1) := by decide +kernel
private theorem pointp01111_2 : fastHom 1 ((2:ℤ)^1626+2) vp0111 = ((2:ℤ)^8856)*vp01111.subst ((2:ℤ)^1626+2)+ep01111.subst ((2:ℤ)^1626+2) := by decide +kernel
private theorem pointp01111_3 : fastHom 1 ((2:ℤ)^1626+3) vp0111 = ((2:ℤ)^8856)*vp01111.subst ((2:ℤ)^1626+3)+ep01111.subst ((2:ℤ)^1626+3) := by decide +kernel
private theorem pointp01111_4 : fastHom 1 ((2:ℤ)^1626+4) vp0111 = ((2:ℤ)^8856)*vp01111.subst ((2:ℤ)^1626+4)+ep01111.subst ((2:ℤ)^1626+4) := by decide +kernel
private theorem pointp01111_5 : fastHom 1 ((2:ℤ)^1626+5) vp0111 = ((2:ℤ)^8856)*vp01111.subst ((2:ℤ)^1626+5)+ep01111.subst ((2:ℤ)^1626+5) := by decide +kernel
private theorem pointp01111_6 : fastHom 1 ((2:ℤ)^1626+6) vp0111 = ((2:ℤ)^8856)*vp01111.subst ((2:ℤ)^1626+6)+ep01111.subst ((2:ℤ)^1626+6) := by decide +kernel
private theorem pointp01111_7 : fastHom 1 ((2:ℤ)^1626+7) vp0111 = ((2:ℤ)^8856)*vp01111.subst ((2:ℤ)^1626+7)+ep01111.subst ((2:ℤ)^1626+7) := by decide +kernel
private theorem checkp01111 (x:ℤ) (hx:x ∈ ptsp01111) : fastHom 1 x vp0111 = ((2:ℤ)^8856)*vp01111.subst x+ep01111.subst x := by
  simp only [ptsp01111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp01111_0
  · exact pointp01111_1
  · exact pointp01111_2
  · exact pointp01111_3
  · exact pointp01111_4
  · exact pointp01111_5
  · exact pointp01111_6
  · exact pointp01111_7
private theorem idp01111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111.list =
    C ((2:ℤ)^8856) * horner X vp01111.list + horner X ep01111.list := by
  apply edge_identity (B := (2:ℤ)^11742) (by decide) (by positivity) (by positivity) boundp01111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp01111 (by decide +kernel)
  · have h : ptsp01111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp01111.trans_le (by decide +kernel)
  · exact checkp01111
private theorem bp01111 : Branch 1 (-3583761639/512000000 : ℚ) vp0111 := by
  apply branch_checked idp01111 (by positivity) (by decide +kernel)
  rw [show 2*(-3583761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-3839761639/256000000 : ℚ) by norm_num]
  exact coverp01111
theorem coverp0111 : Covers (-3583761639/512000000 : ℚ) vp0111 := join_branches bp01110 bp01111
end NextProof.EdgeFull

