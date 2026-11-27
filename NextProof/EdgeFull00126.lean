import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp01111111111_0 : Blocks := edgeBlocks% "full/vectors/01111111111-V-0000.bin"
noncomputable def vp01111111111 : Blocks := vp01111111111_0
theorem coverp01111111111 : Covers (-4091761639/4000000 : ℚ) vp01111111111 := cover_leaf (by decide +kernel)
private noncomputable def vp01111111110_0 : Blocks := edgeBlocks% "full/vectors/01111111110-V-0000.bin"
noncomputable def vp01111111110 : Blocks := vp01111111110_0
theorem coverp01111111110 : Covers (-4087761639/4000000 : ℚ) vp01111111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111111111_0 : Blocks := edgeBlocks% "full/vectors/0111111111-V-0000.bin"
private noncomputable def vp0111111111_1 : Blocks := edgeBlocks% "full/vectors/0111111111-V-0001.bin"
noncomputable def vp0111111111 : Blocks := (Blocks.join vp0111111111_0 vp0111111111_1)
private theorem bp01111111110 : Branch 0 (-4087761639/8000000 : ℚ) vp0111111111 := by
  apply branch_left_normalized (c:=vp01111111110) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-4087761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4087761639/4000000 : ℚ) by norm_num]
  exact coverp01111111110
private noncomputable def ep01111111111_0 : Blocks := edgeBlocks% "full/vectors/01111111111-E-0000.bin"
private noncomputable def ep01111111111_1 : Blocks := edgeBlocks% "full/vectors/01111111111-E-0001.bin"
noncomputable def ep01111111111 : Blocks := (Blocks.join ep01111111111_0 ep01111111111_1)
private theorem idp01111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111111111.list =
    C ((2:ℤ)^168) * horner X vp01111111111.list + horner X ep01111111111.list := by
  exact edge_identity (B := (2:ℤ)^311) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111111111 : Branch 1 (-4087761639/8000000 : ℚ) vp0111111111 := by
  apply branch_checked idp01111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-4087761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4091761639/4000000 : ℚ) by norm_num]
  exact coverp01111111111
theorem coverp0111111111 : Covers (-4087761639/8000000 : ℚ) vp0111111111 := join_branches bp01111111110 bp01111111111
private noncomputable def vp01111111101_0 : Blocks := edgeBlocks% "full/vectors/01111111101-V-0000.bin"
noncomputable def vp01111111101 : Blocks := vp01111111101_0
theorem coverp01111111101 : Covers (-4083761639/4000000 : ℚ) vp01111111101 := cover_leaf (by decide +kernel)
private noncomputable def vp01111111100_0 : Blocks := edgeBlocks% "full/vectors/01111111100-V-0000.bin"
noncomputable def vp01111111100 : Blocks := vp01111111100_0
theorem coverp01111111100 : Covers (-4079761639/4000000 : ℚ) vp01111111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111111110_0 : Blocks := edgeBlocks% "full/vectors/0111111110-V-0000.bin"
private noncomputable def vp0111111110_1 : Blocks := edgeBlocks% "full/vectors/0111111110-V-0001.bin"
noncomputable def vp0111111110 : Blocks := (Blocks.join vp0111111110_0 vp0111111110_1)
private theorem bp01111111100 : Branch 0 (-4079761639/8000000 : ℚ) vp0111111110 := by
  apply branch_left_normalized (c:=vp01111111100) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-4079761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4079761639/4000000 : ℚ) by norm_num]
  exact coverp01111111100
private noncomputable def ep01111111101_0 : Blocks := edgeBlocks% "full/vectors/01111111101-E-0000.bin"
private noncomputable def ep01111111101_1 : Blocks := edgeBlocks% "full/vectors/01111111101-E-0001.bin"
noncomputable def ep01111111101 : Blocks := (Blocks.join ep01111111101_0 ep01111111101_1)
private theorem idp01111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111111110.list =
    C ((2:ℤ)^169) * horner X vp01111111101.list + horner X ep01111111101.list := by
  exact edge_identity (B := (2:ℤ)^312) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111111101 : Branch 1 (-4079761639/8000000 : ℚ) vp0111111110 := by
  apply branch_checked idp01111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-4079761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4083761639/4000000 : ℚ) by norm_num]
  exact coverp01111111101
theorem coverp0111111110 : Covers (-4079761639/8000000 : ℚ) vp0111111110 := join_branches bp01111111100 bp01111111101
private noncomputable def vp011111111_0 : Blocks := edgeBlocks% "full/vectors/011111111-V-0000.bin"
private noncomputable def vp011111111_1 : Blocks := edgeBlocks% "full/vectors/011111111-V-0001.bin"
private noncomputable def vp011111111_2 : Blocks := edgeBlocks% "full/vectors/011111111-V-0002.bin"
noncomputable def vp011111111 : Blocks := (Blocks.join vp011111111_0 (Blocks.join vp011111111_1 vp011111111_2))
private theorem bp0111111110 : Branch 0 (-4079761639/16000000 : ℚ) vp011111111 := by
  apply branch_left_normalized (c:=vp0111111110) (k:=0) (m:=145) (by decide +kernel)
  rw [show 2*(-4079761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4079761639/8000000 : ℚ) by norm_num]
  exact coverp0111111110
private noncomputable def ep0111111111_0 : Blocks := edgeBlocks% "full/vectors/0111111111-E-0000.bin"
private noncomputable def ep0111111111_1 : Blocks := edgeBlocks% "full/vectors/0111111111-E-0001.bin"
private noncomputable def ep0111111111_2 : Blocks := edgeBlocks% "full/vectors/0111111111-E-0002.bin"
noncomputable def ep0111111111 : Blocks := (Blocks.join ep0111111111_0 (Blocks.join ep0111111111_1 ep0111111111_2))
private theorem idp0111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011111111.list =
    C ((2:ℤ)^315) * horner X vp0111111111.list + horner X ep0111111111.list := by
  exact edge_identity (B := (2:ℤ)^500) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111111111 : Branch 1 (-4079761639/16000000 : ℚ) vp011111111 := by
  apply branch_checked idp0111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-4079761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4087761639/8000000 : ℚ) by norm_num]
  exact coverp0111111111
theorem coverp011111111 : Covers (-4079761639/16000000 : ℚ) vp011111111 := join_branches bp0111111110 bp0111111111
private noncomputable def vp01111111011_0 : Blocks := edgeBlocks% "full/vectors/01111111011-V-0000.bin"
noncomputable def vp01111111011 : Blocks := vp01111111011_0
theorem coverp01111111011 : Covers (-4075761639/4000000 : ℚ) vp01111111011 := cover_leaf (by decide +kernel)
private noncomputable def vp01111111010_0 : Blocks := edgeBlocks% "full/vectors/01111111010-V-0000.bin"
noncomputable def vp01111111010 : Blocks := vp01111111010_0
theorem coverp01111111010 : Covers (-4071761639/4000000 : ℚ) vp01111111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111111101_0 : Blocks := edgeBlocks% "full/vectors/0111111101-V-0000.bin"
private noncomputable def vp0111111101_1 : Blocks := edgeBlocks% "full/vectors/0111111101-V-0001.bin"
noncomputable def vp0111111101 : Blocks := (Blocks.join vp0111111101_0 vp0111111101_1)
private theorem bp01111111010 : Branch 0 (-4071761639/8000000 : ℚ) vp0111111101 := by
  apply branch_left_normalized (c:=vp01111111010) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-4071761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4071761639/4000000 : ℚ) by norm_num]
  exact coverp01111111010
private noncomputable def ep01111111011_0 : Blocks := edgeBlocks% "full/vectors/01111111011-E-0000.bin"
private noncomputable def ep01111111011_1 : Blocks := edgeBlocks% "full/vectors/01111111011-E-0001.bin"
noncomputable def ep01111111011 : Blocks := (Blocks.join ep01111111011_0 ep01111111011_1)
private theorem idp01111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111111101.list =
    C ((2:ℤ)^170) * horner X vp01111111011.list + horner X ep01111111011.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111111011 : Branch 1 (-4071761639/8000000 : ℚ) vp0111111101 := by
  apply branch_checked idp01111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-4071761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4075761639/4000000 : ℚ) by norm_num]
  exact coverp01111111011
theorem coverp0111111101 : Covers (-4071761639/8000000 : ℚ) vp0111111101 := join_branches bp01111111010 bp01111111011
private noncomputable def vp01111111001_0 : Blocks := edgeBlocks% "full/vectors/01111111001-V-0000.bin"
noncomputable def vp01111111001 : Blocks := vp01111111001_0
theorem coverp01111111001 : Covers (-4067761639/4000000 : ℚ) vp01111111001 := cover_leaf (by decide +kernel)
private noncomputable def vp01111111000_0 : Blocks := edgeBlocks% "full/vectors/01111111000-V-0000.bin"
noncomputable def vp01111111000 : Blocks := vp01111111000_0
theorem coverp01111111000 : Covers (-4063761639/4000000 : ℚ) vp01111111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111111100_0 : Blocks := edgeBlocks% "full/vectors/0111111100-V-0000.bin"
private noncomputable def vp0111111100_1 : Blocks := edgeBlocks% "full/vectors/0111111100-V-0001.bin"
noncomputable def vp0111111100 : Blocks := (Blocks.join vp0111111100_0 vp0111111100_1)
private theorem bp01111111000 : Branch 0 (-4063761639/8000000 : ℚ) vp0111111100 := by
  apply branch_left_normalized (c:=vp01111111000) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-4063761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4063761639/4000000 : ℚ) by norm_num]
  exact coverp01111111000
private noncomputable def ep01111111001_0 : Blocks := edgeBlocks% "full/vectors/01111111001-E-0000.bin"
private noncomputable def ep01111111001_1 : Blocks := edgeBlocks% "full/vectors/01111111001-E-0001.bin"
noncomputable def ep01111111001 : Blocks := (Blocks.join ep01111111001_0 ep01111111001_1)
private theorem idp01111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111111100.list =
    C ((2:ℤ)^169) * horner X vp01111111001.list + horner X ep01111111001.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111111001 : Branch 1 (-4063761639/8000000 : ℚ) vp0111111100 := by
  apply branch_checked idp01111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-4063761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4067761639/4000000 : ℚ) by norm_num]
  exact coverp01111111001
theorem coverp0111111100 : Covers (-4063761639/8000000 : ℚ) vp0111111100 := join_branches bp01111111000 bp01111111001
private noncomputable def vp011111110_0 : Blocks := edgeBlocks% "full/vectors/011111110-V-0000.bin"
private noncomputable def vp011111110_1 : Blocks := edgeBlocks% "full/vectors/011111110-V-0001.bin"
private noncomputable def vp011111110_2 : Blocks := edgeBlocks% "full/vectors/011111110-V-0002.bin"
noncomputable def vp011111110 : Blocks := (Blocks.join vp011111110_0 (Blocks.join vp011111110_1 vp011111110_2))
private theorem bp0111111100 : Branch 0 (-4063761639/16000000 : ℚ) vp011111110 := by
  apply branch_left_normalized (c:=vp0111111100) (k:=0) (m:=145) (by decide +kernel)
  rw [show 2*(-4063761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4063761639/8000000 : ℚ) by norm_num]
  exact coverp0111111100
private noncomputable def ep0111111101_0 : Blocks := edgeBlocks% "full/vectors/0111111101-E-0000.bin"
private noncomputable def ep0111111101_1 : Blocks := edgeBlocks% "full/vectors/0111111101-E-0001.bin"
private noncomputable def ep0111111101_2 : Blocks := edgeBlocks% "full/vectors/0111111101-E-0002.bin"
noncomputable def ep0111111101 : Blocks := (Blocks.join ep0111111101_0 (Blocks.join ep0111111101_1 ep0111111101_2))
private theorem idp0111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011111110.list =
    C ((2:ℤ)^316) * horner X vp0111111101.list + horner X ep0111111101.list := by
  exact edge_identity (B := (2:ℤ)^502) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111111101 : Branch 1 (-4063761639/16000000 : ℚ) vp011111110 := by
  apply branch_checked idp0111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-4063761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4071761639/8000000 : ℚ) by norm_num]
  exact coverp0111111101
theorem coverp011111110 : Covers (-4063761639/16000000 : ℚ) vp011111110 := join_branches bp0111111100 bp0111111101
private noncomputable def vp01111111_0 : Blocks := edgeBlocks% "full/vectors/01111111-V-0000.bin"
private noncomputable def vp01111111_1 : Blocks := edgeBlocks% "full/vectors/01111111-V-0001.bin"
private noncomputable def vp01111111_2 : Blocks := edgeBlocks% "full/vectors/01111111-V-0002.bin"
private noncomputable def vp01111111_3 : Blocks := edgeBlocks% "full/vectors/01111111-V-0003.bin"
private noncomputable def vp01111111_4 : Blocks := edgeBlocks% "full/vectors/01111111-V-0004.bin"
noncomputable def vp01111111 : Blocks := (Blocks.join (Blocks.join vp01111111_0 vp01111111_1) (Blocks.join vp01111111_2 (Blocks.join vp01111111_3 vp01111111_4)))
private theorem bp011111110 : Branch 0 (-4063761639/32000000 : ℚ) vp01111111 := by
  apply branch_left_normalized (c:=vp011111110) (k:=0) (m:=269) (by decide +kernel)
  rw [show 2*(-4063761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4063761639/16000000 : ℚ) by norm_num]
  exact coverp011111110
private noncomputable def ep011111111_0 : Blocks := edgeBlocks% "full/vectors/011111111-E-0000.bin"
private noncomputable def ep011111111_1 : Blocks := edgeBlocks% "full/vectors/011111111-E-0001.bin"
private noncomputable def ep011111111_2 : Blocks := edgeBlocks% "full/vectors/011111111-E-0002.bin"
private noncomputable def ep011111111_3 : Blocks := edgeBlocks% "full/vectors/011111111-E-0003.bin"
private noncomputable def ep011111111_4 : Blocks := edgeBlocks% "full/vectors/011111111-E-0004.bin"
noncomputable def ep011111111 : Blocks := (Blocks.join (Blocks.join ep011111111_0 ep011111111_1) (Blocks.join ep011111111_2 (Blocks.join ep011111111_3 ep011111111_4)))
private theorem idp011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01111111.list =
    C ((2:ℤ)^606) * horner X vp011111111.list + horner X ep011111111.list := by
  exact edge_identity (B := (2:ℤ)^876) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011111111 : Branch 1 (-4063761639/32000000 : ℚ) vp01111111 := by
  apply branch_checked idp011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-4063761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4079761639/16000000 : ℚ) by norm_num]
  exact coverp011111111
theorem coverp01111111 : Covers (-4063761639/32000000 : ℚ) vp01111111 := join_branches bp011111110 bp011111111
private noncomputable def vp01111110111_0 : Blocks := edgeBlocks% "full/vectors/01111110111-V-0000.bin"
noncomputable def vp01111110111 : Blocks := vp01111110111_0
theorem coverp01111110111 : Covers (-4059761639/4000000 : ℚ) vp01111110111 := cover_leaf (by decide +kernel)
private noncomputable def vp01111110110_0 : Blocks := edgeBlocks% "full/vectors/01111110110-V-0000.bin"
noncomputable def vp01111110110 : Blocks := vp01111110110_0
theorem coverp01111110110 : Covers (-4055761639/4000000 : ℚ) vp01111110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111111011_0 : Blocks := edgeBlocks% "full/vectors/0111111011-V-0000.bin"
private noncomputable def vp0111111011_1 : Blocks := edgeBlocks% "full/vectors/0111111011-V-0001.bin"
noncomputable def vp0111111011 : Blocks := (Blocks.join vp0111111011_0 vp0111111011_1)
private theorem bp01111110110 : Branch 0 (-4055761639/8000000 : ℚ) vp0111111011 := by
  apply branch_left_normalized (c:=vp01111110110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-4055761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4055761639/4000000 : ℚ) by norm_num]
  exact coverp01111110110
private noncomputable def ep01111110111_0 : Blocks := edgeBlocks% "full/vectors/01111110111-E-0000.bin"
private noncomputable def ep01111110111_1 : Blocks := edgeBlocks% "full/vectors/01111110111-E-0001.bin"
noncomputable def ep01111110111 : Blocks := (Blocks.join ep01111110111_0 ep01111110111_1)
private theorem idp01111110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111111011.list =
    C ((2:ℤ)^169) * horner X vp01111110111.list + horner X ep01111110111.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111110111 : Branch 1 (-4055761639/8000000 : ℚ) vp0111111011 := by
  apply branch_checked idp01111110111 (by positivity) (by decide +kernel)
  rw [show 2*(-4055761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4059761639/4000000 : ℚ) by norm_num]
  exact coverp01111110111
theorem coverp0111111011 : Covers (-4055761639/8000000 : ℚ) vp0111111011 := join_branches bp01111110110 bp01111110111
private noncomputable def vp01111110101_0 : Blocks := edgeBlocks% "full/vectors/01111110101-V-0000.bin"
noncomputable def vp01111110101 : Blocks := vp01111110101_0
theorem coverp01111110101 : Covers (-4051761639/4000000 : ℚ) vp01111110101 := cover_leaf (by decide +kernel)
private noncomputable def vp01111110100_0 : Blocks := edgeBlocks% "full/vectors/01111110100-V-0000.bin"
noncomputable def vp01111110100 : Blocks := vp01111110100_0
theorem coverp01111110100 : Covers (-4047761639/4000000 : ℚ) vp01111110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111111010_0 : Blocks := edgeBlocks% "full/vectors/0111111010-V-0000.bin"
private noncomputable def vp0111111010_1 : Blocks := edgeBlocks% "full/vectors/0111111010-V-0001.bin"
noncomputable def vp0111111010 : Blocks := (Blocks.join vp0111111010_0 vp0111111010_1)
private theorem bp01111110100 : Branch 0 (-4047761639/8000000 : ℚ) vp0111111010 := by
  apply branch_left_normalized (c:=vp01111110100) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-4047761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4047761639/4000000 : ℚ) by norm_num]
  exact coverp01111110100
private noncomputable def ep01111110101_0 : Blocks := edgeBlocks% "full/vectors/01111110101-E-0000.bin"
private noncomputable def ep01111110101_1 : Blocks := edgeBlocks% "full/vectors/01111110101-E-0001.bin"
noncomputable def ep01111110101 : Blocks := (Blocks.join ep01111110101_0 ep01111110101_1)
private theorem idp01111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111111010.list =
    C ((2:ℤ)^169) * horner X vp01111110101.list + horner X ep01111110101.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111110101 : Branch 1 (-4047761639/8000000 : ℚ) vp0111111010 := by
  apply branch_checked idp01111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-4047761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4051761639/4000000 : ℚ) by norm_num]
  exact coverp01111110101
theorem coverp0111111010 : Covers (-4047761639/8000000 : ℚ) vp0111111010 := join_branches bp01111110100 bp01111110101
private noncomputable def vp011111101_0 : Blocks := edgeBlocks% "full/vectors/011111101-V-0000.bin"
private noncomputable def vp011111101_1 : Blocks := edgeBlocks% "full/vectors/011111101-V-0001.bin"
private noncomputable def vp011111101_2 : Blocks := edgeBlocks% "full/vectors/011111101-V-0002.bin"
noncomputable def vp011111101 : Blocks := (Blocks.join vp011111101_0 (Blocks.join vp011111101_1 vp011111101_2))
private theorem bp0111111010 : Branch 0 (-4047761639/16000000 : ℚ) vp011111101 := by
  apply branch_left_normalized (c:=vp0111111010) (k:=0) (m:=145) (by decide +kernel)
  rw [show 2*(-4047761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4047761639/8000000 : ℚ) by norm_num]
  exact coverp0111111010
private noncomputable def ep0111111011_0 : Blocks := edgeBlocks% "full/vectors/0111111011-E-0000.bin"
private noncomputable def ep0111111011_1 : Blocks := edgeBlocks% "full/vectors/0111111011-E-0001.bin"
private noncomputable def ep0111111011_2 : Blocks := edgeBlocks% "full/vectors/0111111011-E-0002.bin"
noncomputable def ep0111111011 : Blocks := (Blocks.join ep0111111011_0 (Blocks.join ep0111111011_1 ep0111111011_2))
private theorem idp0111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011111101.list =
    C ((2:ℤ)^316) * horner X vp0111111011.list + horner X ep0111111011.list := by
  exact edge_identity (B := (2:ℤ)^502) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111111011 : Branch 1 (-4047761639/16000000 : ℚ) vp011111101 := by
  apply branch_checked idp0111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-4047761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4055761639/8000000 : ℚ) by norm_num]
  exact coverp0111111011
theorem coverp011111101 : Covers (-4047761639/16000000 : ℚ) vp011111101 := join_branches bp0111111010 bp0111111011
private noncomputable def vp01111110011_0 : Blocks := edgeBlocks% "full/vectors/01111110011-V-0000.bin"
noncomputable def vp01111110011 : Blocks := vp01111110011_0
theorem coverp01111110011 : Covers (-4043761639/4000000 : ℚ) vp01111110011 := cover_leaf (by decide +kernel)
private noncomputable def vp01111110010_0 : Blocks := edgeBlocks% "full/vectors/01111110010-V-0000.bin"
noncomputable def vp01111110010 : Blocks := vp01111110010_0
theorem coverp01111110010 : Covers (-4039761639/4000000 : ℚ) vp01111110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111111001_0 : Blocks := edgeBlocks% "full/vectors/0111111001-V-0000.bin"
private noncomputable def vp0111111001_1 : Blocks := edgeBlocks% "full/vectors/0111111001-V-0001.bin"
noncomputable def vp0111111001 : Blocks := (Blocks.join vp0111111001_0 vp0111111001_1)
private theorem bp01111110010 : Branch 0 (-4039761639/8000000 : ℚ) vp0111111001 := by
  apply branch_left_normalized (c:=vp01111110010) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-4039761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4039761639/4000000 : ℚ) by norm_num]
  exact coverp01111110010
private noncomputable def ep01111110011_0 : Blocks := edgeBlocks% "full/vectors/01111110011-E-0000.bin"
private noncomputable def ep01111110011_1 : Blocks := edgeBlocks% "full/vectors/01111110011-E-0001.bin"
noncomputable def ep01111110011 : Blocks := (Blocks.join ep01111110011_0 ep01111110011_1)
private theorem idp01111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111111001.list =
    C ((2:ℤ)^169) * horner X vp01111110011.list + horner X ep01111110011.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111110011 : Branch 1 (-4039761639/8000000 : ℚ) vp0111111001 := by
  apply branch_checked idp01111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-4039761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4043761639/4000000 : ℚ) by norm_num]
  exact coverp01111110011
theorem coverp0111111001 : Covers (-4039761639/8000000 : ℚ) vp0111111001 := join_branches bp01111110010 bp01111110011
private noncomputable def vp01111110001_0 : Blocks := edgeBlocks% "full/vectors/01111110001-V-0000.bin"
noncomputable def vp01111110001 : Blocks := vp01111110001_0
theorem coverp01111110001 : Covers (-4035761639/4000000 : ℚ) vp01111110001 := cover_leaf (by decide +kernel)
private noncomputable def vp01111110000_0 : Blocks := edgeBlocks% "full/vectors/01111110000-V-0000.bin"
noncomputable def vp01111110000 : Blocks := vp01111110000_0
theorem coverp01111110000 : Covers (-4031761639/4000000 : ℚ) vp01111110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111111000_0 : Blocks := edgeBlocks% "full/vectors/0111111000-V-0000.bin"
private noncomputable def vp0111111000_1 : Blocks := edgeBlocks% "full/vectors/0111111000-V-0001.bin"
noncomputable def vp0111111000 : Blocks := (Blocks.join vp0111111000_0 vp0111111000_1)
private theorem bp01111110000 : Branch 0 (-4031761639/8000000 : ℚ) vp0111111000 := by
  apply branch_left_normalized (c:=vp01111110000) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-4031761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4031761639/4000000 : ℚ) by norm_num]
  exact coverp01111110000
private noncomputable def ep01111110001_0 : Blocks := edgeBlocks% "full/vectors/01111110001-E-0000.bin"
private noncomputable def ep01111110001_1 : Blocks := edgeBlocks% "full/vectors/01111110001-E-0001.bin"
noncomputable def ep01111110001 : Blocks := (Blocks.join ep01111110001_0 ep01111110001_1)
private theorem idp01111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111111000.list =
    C ((2:ℤ)^170) * horner X vp01111110001.list + horner X ep01111110001.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111110001 : Branch 1 (-4031761639/8000000 : ℚ) vp0111111000 := by
  apply branch_checked idp01111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-4031761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4035761639/4000000 : ℚ) by norm_num]
  exact coverp01111110001
theorem coverp0111111000 : Covers (-4031761639/8000000 : ℚ) vp0111111000 := join_branches bp01111110000 bp01111110001
private noncomputable def vp011111100_0 : Blocks := edgeBlocks% "full/vectors/011111100-V-0000.bin"
private noncomputable def vp011111100_1 : Blocks := edgeBlocks% "full/vectors/011111100-V-0001.bin"
private noncomputable def vp011111100_2 : Blocks := edgeBlocks% "full/vectors/011111100-V-0002.bin"
noncomputable def vp011111100 : Blocks := (Blocks.join vp011111100_0 (Blocks.join vp011111100_1 vp011111100_2))
private theorem bp0111111000 : Branch 0 (-4031761639/16000000 : ℚ) vp011111100 := by
  apply branch_left_normalized (c:=vp0111111000) (k:=0) (m:=146) (by decide +kernel)
  rw [show 2*(-4031761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4031761639/8000000 : ℚ) by norm_num]
  exact coverp0111111000
private noncomputable def ep0111111001_0 : Blocks := edgeBlocks% "full/vectors/0111111001-E-0000.bin"
private noncomputable def ep0111111001_1 : Blocks := edgeBlocks% "full/vectors/0111111001-E-0001.bin"
private noncomputable def ep0111111001_2 : Blocks := edgeBlocks% "full/vectors/0111111001-E-0002.bin"
noncomputable def ep0111111001 : Blocks := (Blocks.join ep0111111001_0 (Blocks.join ep0111111001_1 ep0111111001_2))
private theorem idp0111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011111100.list =
    C ((2:ℤ)^316) * horner X vp0111111001.list + horner X ep0111111001.list := by
  exact edge_identity (B := (2:ℤ)^502) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111111001 : Branch 1 (-4031761639/16000000 : ℚ) vp011111100 := by
  apply branch_checked idp0111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-4031761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4039761639/8000000 : ℚ) by norm_num]
  exact coverp0111111001
theorem coverp011111100 : Covers (-4031761639/16000000 : ℚ) vp011111100 := join_branches bp0111111000 bp0111111001
private noncomputable def vp01111110_0 : Blocks := edgeBlocks% "full/vectors/01111110-V-0000.bin"
private noncomputable def vp01111110_1 : Blocks := edgeBlocks% "full/vectors/01111110-V-0001.bin"
private noncomputable def vp01111110_2 : Blocks := edgeBlocks% "full/vectors/01111110-V-0002.bin"
private noncomputable def vp01111110_3 : Blocks := edgeBlocks% "full/vectors/01111110-V-0003.bin"
private noncomputable def vp01111110_4 : Blocks := edgeBlocks% "full/vectors/01111110-V-0004.bin"
noncomputable def vp01111110 : Blocks := (Blocks.join (Blocks.join vp01111110_0 vp01111110_1) (Blocks.join vp01111110_2 (Blocks.join vp01111110_3 vp01111110_4)))
private theorem bp011111100 : Branch 0 (-4031761639/32000000 : ℚ) vp01111110 := by
  apply branch_left_normalized (c:=vp011111100) (k:=0) (m:=269) (by decide +kernel)
  rw [show 2*(-4031761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-4031761639/16000000 : ℚ) by norm_num]
  exact coverp011111100
private noncomputable def ep011111101_0 : Blocks := edgeBlocks% "full/vectors/011111101-E-0000.bin"
private noncomputable def ep011111101_1 : Blocks := edgeBlocks% "full/vectors/011111101-E-0001.bin"
private noncomputable def ep011111101_2 : Blocks := edgeBlocks% "full/vectors/011111101-E-0002.bin"
private noncomputable def ep011111101_3 : Blocks := edgeBlocks% "full/vectors/011111101-E-0003.bin"
private noncomputable def ep011111101_4 : Blocks := edgeBlocks% "full/vectors/011111101-E-0004.bin"
noncomputable def ep011111101 : Blocks := (Blocks.join (Blocks.join ep011111101_0 ep011111101_1) (Blocks.join ep011111101_2 (Blocks.join ep011111101_3 ep011111101_4)))
private theorem idp011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01111110.list =
    C ((2:ℤ)^607) * horner X vp011111101.list + horner X ep011111101.list := by
  exact edge_identity (B := (2:ℤ)^878) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011111101 : Branch 1 (-4031761639/32000000 : ℚ) vp01111110 := by
  apply branch_checked idp011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-4031761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4047761639/16000000 : ℚ) by norm_num]
  exact coverp011111101
theorem coverp01111110 : Covers (-4031761639/32000000 : ℚ) vp01111110 := join_branches bp011111100 bp011111101
private noncomputable def vp0111111_0 : Blocks := edgeBlocks% "full/vectors/0111111-V-0000.bin"
private noncomputable def vp0111111_1 : Blocks := edgeBlocks% "full/vectors/0111111-V-0001.bin"
private noncomputable def vp0111111_2 : Blocks := edgeBlocks% "full/vectors/0111111-V-0002.bin"
private noncomputable def vp0111111_3 : Blocks := edgeBlocks% "full/vectors/0111111-V-0003.bin"
private noncomputable def vp0111111_4 : Blocks := edgeBlocks% "full/vectors/0111111-V-0004.bin"
private noncomputable def vp0111111_5 : Blocks := edgeBlocks% "full/vectors/0111111-V-0005.bin"
private noncomputable def vp0111111_6 : Blocks := edgeBlocks% "full/vectors/0111111-V-0006.bin"
private noncomputable def vp0111111_7 : Blocks := edgeBlocks% "full/vectors/0111111-V-0007.bin"
noncomputable def vp0111111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0111111_0 vp0111111_1) (Blocks.join vp0111111_2 vp0111111_3)) (Blocks.join (Blocks.join vp0111111_4 vp0111111_5) (Blocks.join vp0111111_6 vp0111111_7)))
private theorem bp01111110 : Branch 0 (-4031761639/64000000 : ℚ) vp0111111 := by
  apply branch_left_normalized (c:=vp01111110) (k:=0) (m:=514) (by decide +kernel)
  rw [show 2*(-4031761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-4031761639/32000000 : ℚ) by norm_num]
  exact coverp01111110
private noncomputable def ep01111111_0 : Blocks := edgeBlocks% "full/vectors/01111111-E-0000.bin"
private noncomputable def ep01111111_1 : Blocks := edgeBlocks% "full/vectors/01111111-E-0001.bin"
private noncomputable def ep01111111_2 : Blocks := edgeBlocks% "full/vectors/01111111-E-0002.bin"
private noncomputable def ep01111111_3 : Blocks := edgeBlocks% "full/vectors/01111111-E-0003.bin"
private noncomputable def ep01111111_4 : Blocks := edgeBlocks% "full/vectors/01111111-E-0004.bin"
private noncomputable def ep01111111_5 : Blocks := edgeBlocks% "full/vectors/01111111-E-0005.bin"
private noncomputable def ep01111111_6 : Blocks := edgeBlocks% "full/vectors/01111111-E-0006.bin"
private noncomputable def ep01111111_7 : Blocks := edgeBlocks% "full/vectors/01111111-E-0007.bin"
noncomputable def ep01111111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01111111_0 ep01111111_1) (Blocks.join ep01111111_2 ep01111111_3)) (Blocks.join (Blocks.join ep01111111_4 ep01111111_5) (Blocks.join ep01111111_6 ep01111111_7)))
private theorem idp01111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111111.list =
    C ((2:ℤ)^1183) * horner X vp01111111.list + horner X ep01111111.list := by
  exact edge_identity (B := (2:ℤ)^1623) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111111 : Branch 1 (-4031761639/64000000 : ℚ) vp0111111 := by
  apply branch_checked idp01111111 (by positivity) (by decide +kernel)
  rw [show 2*(-4031761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-4063761639/32000000 : ℚ) by norm_num]
  exact coverp01111111
theorem coverp0111111 : Covers (-4031761639/64000000 : ℚ) vp0111111 := join_branches bp01111110 bp01111111
private noncomputable def vp01111101111_0 : Blocks := edgeBlocks% "full/vectors/01111101111-V-0000.bin"
noncomputable def vp01111101111 : Blocks := vp01111101111_0
theorem coverp01111101111 : Covers (-4027761639/4000000 : ℚ) vp01111101111 := cover_leaf (by decide +kernel)
private noncomputable def vp01111101110_0 : Blocks := edgeBlocks% "full/vectors/01111101110-V-0000.bin"
noncomputable def vp01111101110 : Blocks := vp01111101110_0
theorem coverp01111101110 : Covers (-4023761639/4000000 : ℚ) vp01111101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111110111_0 : Blocks := edgeBlocks% "full/vectors/0111110111-V-0000.bin"
private noncomputable def vp0111110111_1 : Blocks := edgeBlocks% "full/vectors/0111110111-V-0001.bin"
noncomputable def vp0111110111 : Blocks := (Blocks.join vp0111110111_0 vp0111110111_1)
private theorem bp01111101110 : Branch 0 (-4023761639/8000000 : ℚ) vp0111110111 := by
  apply branch_left_normalized (c:=vp01111101110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-4023761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4023761639/4000000 : ℚ) by norm_num]
  exact coverp01111101110
private noncomputable def ep01111101111_0 : Blocks := edgeBlocks% "full/vectors/01111101111-E-0000.bin"
private noncomputable def ep01111101111_1 : Blocks := edgeBlocks% "full/vectors/01111101111-E-0001.bin"
noncomputable def ep01111101111 : Blocks := (Blocks.join ep01111101111_0 ep01111101111_1)
private theorem idp01111101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111110111.list =
    C ((2:ℤ)^171) * horner X vp01111101111.list + horner X ep01111101111.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111101111 : Branch 1 (-4023761639/8000000 : ℚ) vp0111110111 := by
  apply branch_checked idp01111101111 (by positivity) (by decide +kernel)
  rw [show 2*(-4023761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4027761639/4000000 : ℚ) by norm_num]
  exact coverp01111101111
theorem coverp0111110111 : Covers (-4023761639/8000000 : ℚ) vp0111110111 := join_branches bp01111101110 bp01111101111
private noncomputable def vp01111101101_0 : Blocks := edgeBlocks% "full/vectors/01111101101-V-0000.bin"
noncomputable def vp01111101101 : Blocks := vp01111101101_0
theorem coverp01111101101 : Covers (-4019761639/4000000 : ℚ) vp01111101101 := cover_leaf (by decide +kernel)
private noncomputable def vp01111101100_0 : Blocks := edgeBlocks% "full/vectors/01111101100-V-0000.bin"
noncomputable def vp01111101100 : Blocks := vp01111101100_0
theorem coverp01111101100 : Covers (-4015761639/4000000 : ℚ) vp01111101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111110110_0 : Blocks := edgeBlocks% "full/vectors/0111110110-V-0000.bin"
private noncomputable def vp0111110110_1 : Blocks := edgeBlocks% "full/vectors/0111110110-V-0001.bin"
noncomputable def vp0111110110 : Blocks := (Blocks.join vp0111110110_0 vp0111110110_1)
private theorem bp01111101100 : Branch 0 (-4015761639/8000000 : ℚ) vp0111110110 := by
  apply branch_left_normalized (c:=vp01111101100) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-4015761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4015761639/4000000 : ℚ) by norm_num]
  exact coverp01111101100
private noncomputable def ep01111101101_0 : Blocks := edgeBlocks% "full/vectors/01111101101-E-0000.bin"
private noncomputable def ep01111101101_1 : Blocks := edgeBlocks% "full/vectors/01111101101-E-0001.bin"
noncomputable def ep01111101101 : Blocks := (Blocks.join ep01111101101_0 ep01111101101_1)
private theorem idp01111101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111110110.list =
    C ((2:ℤ)^169) * horner X vp01111101101.list + horner X ep01111101101.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111101101 : Branch 1 (-4015761639/8000000 : ℚ) vp0111110110 := by
  apply branch_checked idp01111101101 (by positivity) (by decide +kernel)
  rw [show 2*(-4015761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4019761639/4000000 : ℚ) by norm_num]
  exact coverp01111101101
theorem coverp0111110110 : Covers (-4015761639/8000000 : ℚ) vp0111110110 := join_branches bp01111101100 bp01111101101
private noncomputable def vp011111011_0 : Blocks := edgeBlocks% "full/vectors/011111011-V-0000.bin"
private noncomputable def vp011111011_1 : Blocks := edgeBlocks% "full/vectors/011111011-V-0001.bin"
private noncomputable def vp011111011_2 : Blocks := edgeBlocks% "full/vectors/011111011-V-0002.bin"
noncomputable def vp011111011 : Blocks := (Blocks.join vp011111011_0 (Blocks.join vp011111011_1 vp011111011_2))
private theorem bp0111110110 : Branch 0 (-4015761639/16000000 : ℚ) vp011111011 := by
  apply branch_left_normalized (c:=vp0111110110) (k:=0) (m:=145) (by decide +kernel)
  rw [show 2*(-4015761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-4015761639/8000000 : ℚ) by norm_num]
  exact coverp0111110110
private noncomputable def ep0111110111_0 : Blocks := edgeBlocks% "full/vectors/0111110111-E-0000.bin"
private noncomputable def ep0111110111_1 : Blocks := edgeBlocks% "full/vectors/0111110111-E-0001.bin"
private noncomputable def ep0111110111_2 : Blocks := edgeBlocks% "full/vectors/0111110111-E-0002.bin"
noncomputable def ep0111110111 : Blocks := (Blocks.join ep0111110111_0 (Blocks.join ep0111110111_1 ep0111110111_2))
private theorem idp0111110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011111011.list =
    C ((2:ℤ)^317) * horner X vp0111110111.list + horner X ep0111110111.list := by
  exact edge_identity (B := (2:ℤ)^504) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111110111 : Branch 1 (-4015761639/16000000 : ℚ) vp011111011 := by
  apply branch_checked idp0111110111 (by positivity) (by decide +kernel)
  rw [show 2*(-4015761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4023761639/8000000 : ℚ) by norm_num]
  exact coverp0111110111
theorem coverp011111011 : Covers (-4015761639/16000000 : ℚ) vp011111011 := join_branches bp0111110110 bp0111110111
private noncomputable def vp01111101011_0 : Blocks := edgeBlocks% "full/vectors/01111101011-V-0000.bin"
noncomputable def vp01111101011 : Blocks := vp01111101011_0
theorem coverp01111101011 : Covers (-4011761639/4000000 : ℚ) vp01111101011 := cover_leaf (by decide +kernel)
private noncomputable def vp01111101010_0 : Blocks := edgeBlocks% "full/vectors/01111101010-V-0000.bin"
noncomputable def vp01111101010 : Blocks := vp01111101010_0
theorem coverp01111101010 : Covers (-4007761639/4000000 : ℚ) vp01111101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111110101_0 : Blocks := edgeBlocks% "full/vectors/0111110101-V-0000.bin"
private noncomputable def vp0111110101_1 : Blocks := edgeBlocks% "full/vectors/0111110101-V-0001.bin"
noncomputable def vp0111110101 : Blocks := (Blocks.join vp0111110101_0 vp0111110101_1)
private theorem bp01111101010 : Branch 0 (-4007761639/8000000 : ℚ) vp0111110101 := by
  apply branch_left_normalized (c:=vp01111101010) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-4007761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-4007761639/4000000 : ℚ) by norm_num]
  exact coverp01111101010
private noncomputable def ep01111101011_0 : Blocks := edgeBlocks% "full/vectors/01111101011-E-0000.bin"
private noncomputable def ep01111101011_1 : Blocks := edgeBlocks% "full/vectors/01111101011-E-0001.bin"
noncomputable def ep01111101011 : Blocks := (Blocks.join ep01111101011_0 ep01111101011_1)
private theorem idp01111101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111110101.list =
    C ((2:ℤ)^170) * horner X vp01111101011.list + horner X ep01111101011.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111101011 : Branch 1 (-4007761639/8000000 : ℚ) vp0111110101 := by
  apply branch_checked idp01111101011 (by positivity) (by decide +kernel)
  rw [show 2*(-4007761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4011761639/4000000 : ℚ) by norm_num]
  exact coverp01111101011
theorem coverp0111110101 : Covers (-4007761639/8000000 : ℚ) vp0111110101 := join_branches bp01111101010 bp01111101011
private noncomputable def vp01111101001_0 : Blocks := edgeBlocks% "full/vectors/01111101001-V-0000.bin"
noncomputable def vp01111101001 : Blocks := vp01111101001_0
theorem coverp01111101001 : Covers (-4003761639/4000000 : ℚ) vp01111101001 := cover_leaf (by decide +kernel)
private noncomputable def vp01111101000_0 : Blocks := edgeBlocks% "full/vectors/01111101000-V-0000.bin"
noncomputable def vp01111101000 : Blocks := vp01111101000_0
theorem coverp01111101000 : Covers (-3999761639/4000000 : ℚ) vp01111101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111110100_0 : Blocks := edgeBlocks% "full/vectors/0111110100-V-0000.bin"
private noncomputable def vp0111110100_1 : Blocks := edgeBlocks% "full/vectors/0111110100-V-0001.bin"
noncomputable def vp0111110100 : Blocks := (Blocks.join vp0111110100_0 vp0111110100_1)
private theorem bp01111101000 : Branch 0 (-3999761639/8000000 : ℚ) vp0111110100 := by
  apply branch_left_normalized (c:=vp01111101000) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3999761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3999761639/4000000 : ℚ) by norm_num]
  exact coverp01111101000
private noncomputable def ep01111101001_0 : Blocks := edgeBlocks% "full/vectors/01111101001-E-0000.bin"
private noncomputable def ep01111101001_1 : Blocks := edgeBlocks% "full/vectors/01111101001-E-0001.bin"
noncomputable def ep01111101001 : Blocks := (Blocks.join ep01111101001_0 ep01111101001_1)
private theorem idp01111101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111110100.list =
    C ((2:ℤ)^170) * horner X vp01111101001.list + horner X ep01111101001.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111101001 : Branch 1 (-3999761639/8000000 : ℚ) vp0111110100 := by
  apply branch_checked idp01111101001 (by positivity) (by decide +kernel)
  rw [show 2*(-3999761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-4003761639/4000000 : ℚ) by norm_num]
  exact coverp01111101001
theorem coverp0111110100 : Covers (-3999761639/8000000 : ℚ) vp0111110100 := join_branches bp01111101000 bp01111101001
private noncomputable def vp011111010_0 : Blocks := edgeBlocks% "full/vectors/011111010-V-0000.bin"
private noncomputable def vp011111010_1 : Blocks := edgeBlocks% "full/vectors/011111010-V-0001.bin"
private noncomputable def vp011111010_2 : Blocks := edgeBlocks% "full/vectors/011111010-V-0002.bin"
noncomputable def vp011111010 : Blocks := (Blocks.join vp011111010_0 (Blocks.join vp011111010_1 vp011111010_2))
private theorem bp0111110100 : Branch 0 (-3999761639/16000000 : ℚ) vp011111010 := by
  apply branch_left_normalized (c:=vp0111110100) (k:=0) (m:=146) (by decide +kernel)
  rw [show 2*(-3999761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3999761639/8000000 : ℚ) by norm_num]
  exact coverp0111110100
private noncomputable def ep0111110101_0 : Blocks := edgeBlocks% "full/vectors/0111110101-E-0000.bin"
private noncomputable def ep0111110101_1 : Blocks := edgeBlocks% "full/vectors/0111110101-E-0001.bin"
private noncomputable def ep0111110101_2 : Blocks := edgeBlocks% "full/vectors/0111110101-E-0002.bin"
noncomputable def ep0111110101 : Blocks := (Blocks.join ep0111110101_0 (Blocks.join ep0111110101_1 ep0111110101_2))
private theorem idp0111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011111010.list =
    C ((2:ℤ)^317) * horner X vp0111110101.list + horner X ep0111110101.list := by
  exact edge_identity (B := (2:ℤ)^504) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111110101 : Branch 1 (-3999761639/16000000 : ℚ) vp011111010 := by
  apply branch_checked idp0111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3999761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-4007761639/8000000 : ℚ) by norm_num]
  exact coverp0111110101
theorem coverp011111010 : Covers (-3999761639/16000000 : ℚ) vp011111010 := join_branches bp0111110100 bp0111110101
private noncomputable def vp01111101_0 : Blocks := edgeBlocks% "full/vectors/01111101-V-0000.bin"
private noncomputable def vp01111101_1 : Blocks := edgeBlocks% "full/vectors/01111101-V-0001.bin"
private noncomputable def vp01111101_2 : Blocks := edgeBlocks% "full/vectors/01111101-V-0002.bin"
private noncomputable def vp01111101_3 : Blocks := edgeBlocks% "full/vectors/01111101-V-0003.bin"
private noncomputable def vp01111101_4 : Blocks := edgeBlocks% "full/vectors/01111101-V-0004.bin"
noncomputable def vp01111101 : Blocks := (Blocks.join (Blocks.join vp01111101_0 vp01111101_1) (Blocks.join vp01111101_2 (Blocks.join vp01111101_3 vp01111101_4)))
private theorem bp011111010 : Branch 0 (-3999761639/32000000 : ℚ) vp01111101 := by
  apply branch_left_normalized (c:=vp011111010) (k:=0) (m:=270) (by decide +kernel)
  rw [show 2*(-3999761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3999761639/16000000 : ℚ) by norm_num]
  exact coverp011111010
private noncomputable def ep011111011_0 : Blocks := edgeBlocks% "full/vectors/011111011-E-0000.bin"
private noncomputable def ep011111011_1 : Blocks := edgeBlocks% "full/vectors/011111011-E-0001.bin"
private noncomputable def ep011111011_2 : Blocks := edgeBlocks% "full/vectors/011111011-E-0002.bin"
private noncomputable def ep011111011_3 : Blocks := edgeBlocks% "full/vectors/011111011-E-0003.bin"
private noncomputable def ep011111011_4 : Blocks := edgeBlocks% "full/vectors/011111011-E-0004.bin"
noncomputable def ep011111011 : Blocks := (Blocks.join (Blocks.join ep011111011_0 ep011111011_1) (Blocks.join ep011111011_2 (Blocks.join ep011111011_3 ep011111011_4)))
private theorem idp011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01111101.list =
    C ((2:ℤ)^610) * horner X vp011111011.list + horner X ep011111011.list := by
  exact edge_identity (B := (2:ℤ)^883) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011111011 : Branch 1 (-3999761639/32000000 : ℚ) vp01111101 := by
  apply branch_checked idp011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3999761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-4015761639/16000000 : ℚ) by norm_num]
  exact coverp011111011
theorem coverp01111101 : Covers (-3999761639/32000000 : ℚ) vp01111101 := join_branches bp011111010 bp011111011
private noncomputable def vp01111100111_0 : Blocks := edgeBlocks% "full/vectors/01111100111-V-0000.bin"
noncomputable def vp01111100111 : Blocks := vp01111100111_0
theorem coverp01111100111 : Covers (-3995761639/4000000 : ℚ) vp01111100111 := cover_leaf (by decide +kernel)
private noncomputable def vp01111100110_0 : Blocks := edgeBlocks% "full/vectors/01111100110-V-0000.bin"
noncomputable def vp01111100110 : Blocks := vp01111100110_0
theorem coverp01111100110 : Covers (-3991761639/4000000 : ℚ) vp01111100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111110011_0 : Blocks := edgeBlocks% "full/vectors/0111110011-V-0000.bin"
private noncomputable def vp0111110011_1 : Blocks := edgeBlocks% "full/vectors/0111110011-V-0001.bin"
noncomputable def vp0111110011 : Blocks := (Blocks.join vp0111110011_0 vp0111110011_1)
private theorem bp01111100110 : Branch 0 (-3991761639/8000000 : ℚ) vp0111110011 := by
  apply branch_left_normalized (c:=vp01111100110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3991761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3991761639/4000000 : ℚ) by norm_num]
  exact coverp01111100110
private noncomputable def ep01111100111_0 : Blocks := edgeBlocks% "full/vectors/01111100111-E-0000.bin"
private noncomputable def ep01111100111_1 : Blocks := edgeBlocks% "full/vectors/01111100111-E-0001.bin"
noncomputable def ep01111100111 : Blocks := (Blocks.join ep01111100111_0 ep01111100111_1)
private theorem idp01111100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111110011.list =
    C ((2:ℤ)^170) * horner X vp01111100111.list + horner X ep01111100111.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111100111 : Branch 1 (-3991761639/8000000 : ℚ) vp0111110011 := by
  apply branch_checked idp01111100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3991761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3995761639/4000000 : ℚ) by norm_num]
  exact coverp01111100111
theorem coverp0111110011 : Covers (-3991761639/8000000 : ℚ) vp0111110011 := join_branches bp01111100110 bp01111100111
private noncomputable def vp01111100101_0 : Blocks := edgeBlocks% "full/vectors/01111100101-V-0000.bin"
noncomputable def vp01111100101 : Blocks := vp01111100101_0
theorem coverp01111100101 : Covers (-3987761639/4000000 : ℚ) vp01111100101 := cover_leaf (by decide +kernel)
private noncomputable def vp01111100100_0 : Blocks := edgeBlocks% "full/vectors/01111100100-V-0000.bin"
noncomputable def vp01111100100 : Blocks := vp01111100100_0
theorem coverp01111100100 : Covers (-3983761639/4000000 : ℚ) vp01111100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111110010_0 : Blocks := edgeBlocks% "full/vectors/0111110010-V-0000.bin"
private noncomputable def vp0111110010_1 : Blocks := edgeBlocks% "full/vectors/0111110010-V-0001.bin"
noncomputable def vp0111110010 : Blocks := (Blocks.join vp0111110010_0 vp0111110010_1)
private theorem bp01111100100 : Branch 0 (-3983761639/8000000 : ℚ) vp0111110010 := by
  apply branch_left_normalized (c:=vp01111100100) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3983761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3983761639/4000000 : ℚ) by norm_num]
  exact coverp01111100100
private noncomputable def ep01111100101_0 : Blocks := edgeBlocks% "full/vectors/01111100101-E-0000.bin"
private noncomputable def ep01111100101_1 : Blocks := edgeBlocks% "full/vectors/01111100101-E-0001.bin"
noncomputable def ep01111100101 : Blocks := (Blocks.join ep01111100101_0 ep01111100101_1)
private theorem idp01111100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111110010.list =
    C ((2:ℤ)^170) * horner X vp01111100101.list + horner X ep01111100101.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111100101 : Branch 1 (-3983761639/8000000 : ℚ) vp0111110010 := by
  apply branch_checked idp01111100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3983761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3987761639/4000000 : ℚ) by norm_num]
  exact coverp01111100101
theorem coverp0111110010 : Covers (-3983761639/8000000 : ℚ) vp0111110010 := join_branches bp01111100100 bp01111100101
private noncomputable def vp011111001_0 : Blocks := edgeBlocks% "full/vectors/011111001-V-0000.bin"
private noncomputable def vp011111001_1 : Blocks := edgeBlocks% "full/vectors/011111001-V-0001.bin"
private noncomputable def vp011111001_2 : Blocks := edgeBlocks% "full/vectors/011111001-V-0002.bin"
noncomputable def vp011111001 : Blocks := (Blocks.join vp011111001_0 (Blocks.join vp011111001_1 vp011111001_2))
private theorem bp0111110010 : Branch 0 (-3983761639/16000000 : ℚ) vp011111001 := by
  apply branch_left_normalized (c:=vp0111110010) (k:=0) (m:=146) (by decide +kernel)
  rw [show 2*(-3983761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3983761639/8000000 : ℚ) by norm_num]
  exact coverp0111110010
private noncomputable def ep0111110011_0 : Blocks := edgeBlocks% "full/vectors/0111110011-E-0000.bin"
private noncomputable def ep0111110011_1 : Blocks := edgeBlocks% "full/vectors/0111110011-E-0001.bin"
private noncomputable def ep0111110011_2 : Blocks := edgeBlocks% "full/vectors/0111110011-E-0002.bin"
noncomputable def ep0111110011 : Blocks := (Blocks.join ep0111110011_0 (Blocks.join ep0111110011_1 ep0111110011_2))
private theorem idp0111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011111001.list =
    C ((2:ℤ)^318) * horner X vp0111110011.list + horner X ep0111110011.list := by
  exact edge_identity (B := (2:ℤ)^505) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111110011 : Branch 1 (-3983761639/16000000 : ℚ) vp011111001 := by
  apply branch_checked idp0111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3983761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3991761639/8000000 : ℚ) by norm_num]
  exact coverp0111110011
theorem coverp011111001 : Covers (-3983761639/16000000 : ℚ) vp011111001 := join_branches bp0111110010 bp0111110011
private noncomputable def vp01111100011_0 : Blocks := edgeBlocks% "full/vectors/01111100011-V-0000.bin"
noncomputable def vp01111100011 : Blocks := vp01111100011_0
theorem coverp01111100011 : Covers (-3979761639/4000000 : ℚ) vp01111100011 := cover_leaf (by decide +kernel)
private noncomputable def vp01111100010_0 : Blocks := edgeBlocks% "full/vectors/01111100010-V-0000.bin"
noncomputable def vp01111100010 : Blocks := vp01111100010_0
theorem coverp01111100010 : Covers (-3975761639/4000000 : ℚ) vp01111100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111110001_0 : Blocks := edgeBlocks% "full/vectors/0111110001-V-0000.bin"
private noncomputable def vp0111110001_1 : Blocks := edgeBlocks% "full/vectors/0111110001-V-0001.bin"
noncomputable def vp0111110001 : Blocks := (Blocks.join vp0111110001_0 vp0111110001_1)
private theorem bp01111100010 : Branch 0 (-3975761639/8000000 : ℚ) vp0111110001 := by
  apply branch_left_normalized (c:=vp01111100010) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-3975761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3975761639/4000000 : ℚ) by norm_num]
  exact coverp01111100010
private noncomputable def ep01111100011_0 : Blocks := edgeBlocks% "full/vectors/01111100011-E-0000.bin"
private noncomputable def ep01111100011_1 : Blocks := edgeBlocks% "full/vectors/01111100011-E-0001.bin"
noncomputable def ep01111100011 : Blocks := (Blocks.join ep01111100011_0 ep01111100011_1)
private theorem idp01111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111110001.list =
    C ((2:ℤ)^170) * horner X vp01111100011.list + horner X ep01111100011.list := by
  exact edge_identity (B := (2:ℤ)^314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111100011 : Branch 1 (-3975761639/8000000 : ℚ) vp0111110001 := by
  apply branch_checked idp01111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-3975761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3979761639/4000000 : ℚ) by norm_num]
  exact coverp01111100011
theorem coverp0111110001 : Covers (-3975761639/8000000 : ℚ) vp0111110001 := join_branches bp01111100010 bp01111100011
private noncomputable def vp01111100001_0 : Blocks := edgeBlocks% "full/vectors/01111100001-V-0000.bin"
noncomputable def vp01111100001 : Blocks := vp01111100001_0
theorem coverp01111100001 : Covers (-3971761639/4000000 : ℚ) vp01111100001 := cover_leaf (by decide +kernel)
private noncomputable def vp01111100000_0 : Blocks := edgeBlocks% "full/vectors/01111100000-V-0000.bin"
noncomputable def vp01111100000 : Blocks := vp01111100000_0
theorem coverp01111100000 : Covers (-3967761639/4000000 : ℚ) vp01111100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111110000_0 : Blocks := edgeBlocks% "full/vectors/0111110000-V-0000.bin"
private noncomputable def vp0111110000_1 : Blocks := edgeBlocks% "full/vectors/0111110000-V-0001.bin"
noncomputable def vp0111110000 : Blocks := (Blocks.join vp0111110000_0 vp0111110000_1)
private theorem bp01111100000 : Branch 0 (-3967761639/8000000 : ℚ) vp0111110000 := by
  apply branch_left_normalized (c:=vp01111100000) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-3967761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3967761639/4000000 : ℚ) by norm_num]
  exact coverp01111100000
private noncomputable def ep01111100001_0 : Blocks := edgeBlocks% "full/vectors/01111100001-E-0000.bin"
private noncomputable def ep01111100001_1 : Blocks := edgeBlocks% "full/vectors/01111100001-E-0001.bin"
noncomputable def ep01111100001 : Blocks := (Blocks.join ep01111100001_0 ep01111100001_1)
private theorem idp01111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111110000.list =
    C ((2:ℤ)^167) * horner X vp01111100001.list + horner X ep01111100001.list := by
  exact edge_identity (B := (2:ℤ)^311) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111100001 : Branch 1 (-3967761639/8000000 : ℚ) vp0111110000 := by
  apply branch_checked idp01111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3967761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3971761639/4000000 : ℚ) by norm_num]
  exact coverp01111100001
theorem coverp0111110000 : Covers (-3967761639/8000000 : ℚ) vp0111110000 := join_branches bp01111100000 bp01111100001
private noncomputable def vp011111000_0 : Blocks := edgeBlocks% "full/vectors/011111000-V-0000.bin"
private noncomputable def vp011111000_1 : Blocks := edgeBlocks% "full/vectors/011111000-V-0001.bin"
private noncomputable def vp011111000_2 : Blocks := edgeBlocks% "full/vectors/011111000-V-0002.bin"
noncomputable def vp011111000 : Blocks := (Blocks.join vp011111000_0 (Blocks.join vp011111000_1 vp011111000_2))
private theorem bp0111110000 : Branch 0 (-3967761639/16000000 : ℚ) vp011111000 := by
  apply branch_left_normalized (c:=vp0111110000) (k:=0) (m:=145) (by decide +kernel)
  rw [show 2*(-3967761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3967761639/8000000 : ℚ) by norm_num]
  exact coverp0111110000
private noncomputable def ep0111110001_0 : Blocks := edgeBlocks% "full/vectors/0111110001-E-0000.bin"
private noncomputable def ep0111110001_1 : Blocks := edgeBlocks% "full/vectors/0111110001-E-0001.bin"
private noncomputable def ep0111110001_2 : Blocks := edgeBlocks% "full/vectors/0111110001-E-0002.bin"
noncomputable def ep0111110001 : Blocks := (Blocks.join ep0111110001_0 (Blocks.join ep0111110001_1 ep0111110001_2))
private theorem idp0111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011111000.list =
    C ((2:ℤ)^315) * horner X vp0111110001.list + horner X ep0111110001.list := by
  exact edge_identity (B := (2:ℤ)^502) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111110001 : Branch 1 (-3967761639/16000000 : ℚ) vp011111000 := by
  apply branch_checked idp0111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3967761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3975761639/8000000 : ℚ) by norm_num]
  exact coverp0111110001
theorem coverp011111000 : Covers (-3967761639/16000000 : ℚ) vp011111000 := join_branches bp0111110000 bp0111110001
private noncomputable def vp01111100_0 : Blocks := edgeBlocks% "full/vectors/01111100-V-0000.bin"
private noncomputable def vp01111100_1 : Blocks := edgeBlocks% "full/vectors/01111100-V-0001.bin"
private noncomputable def vp01111100_2 : Blocks := edgeBlocks% "full/vectors/01111100-V-0002.bin"
private noncomputable def vp01111100_3 : Blocks := edgeBlocks% "full/vectors/01111100-V-0003.bin"
private noncomputable def vp01111100_4 : Blocks := edgeBlocks% "full/vectors/01111100-V-0004.bin"
noncomputable def vp01111100 : Blocks := (Blocks.join (Blocks.join vp01111100_0 vp01111100_1) (Blocks.join vp01111100_2 (Blocks.join vp01111100_3 vp01111100_4)))
private theorem bp011111000 : Branch 0 (-3967761639/32000000 : ℚ) vp01111100 := by
  apply branch_left_normalized (c:=vp011111000) (k:=0) (m:=270) (by decide +kernel)
  rw [show 2*(-3967761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3967761639/16000000 : ℚ) by norm_num]
  exact coverp011111000
private noncomputable def ep011111001_0 : Blocks := edgeBlocks% "full/vectors/011111001-E-0000.bin"
private noncomputable def ep011111001_1 : Blocks := edgeBlocks% "full/vectors/011111001-E-0001.bin"
private noncomputable def ep011111001_2 : Blocks := edgeBlocks% "full/vectors/011111001-E-0002.bin"
private noncomputable def ep011111001_3 : Blocks := edgeBlocks% "full/vectors/011111001-E-0003.bin"
private noncomputable def ep011111001_4 : Blocks := edgeBlocks% "full/vectors/011111001-E-0004.bin"
noncomputable def ep011111001 : Blocks := (Blocks.join (Blocks.join ep011111001_0 ep011111001_1) (Blocks.join ep011111001_2 (Blocks.join ep011111001_3 ep011111001_4)))
private theorem idp011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01111100.list =
    C ((2:ℤ)^608) * horner X vp011111001.list + horner X ep011111001.list := by
  exact edge_identity (B := (2:ℤ)^881) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011111001 : Branch 1 (-3967761639/32000000 : ℚ) vp01111100 := by
  apply branch_checked idp011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3967761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3983761639/16000000 : ℚ) by norm_num]
  exact coverp011111001
theorem coverp01111100 : Covers (-3967761639/32000000 : ℚ) vp01111100 := join_branches bp011111000 bp011111001
private noncomputable def vp0111110_0 : Blocks := edgeBlocks% "full/vectors/0111110-V-0000.bin"
private noncomputable def vp0111110_1 : Blocks := edgeBlocks% "full/vectors/0111110-V-0001.bin"
private noncomputable def vp0111110_2 : Blocks := edgeBlocks% "full/vectors/0111110-V-0002.bin"
private noncomputable def vp0111110_3 : Blocks := edgeBlocks% "full/vectors/0111110-V-0003.bin"
private noncomputable def vp0111110_4 : Blocks := edgeBlocks% "full/vectors/0111110-V-0004.bin"
private noncomputable def vp0111110_5 : Blocks := edgeBlocks% "full/vectors/0111110-V-0005.bin"
private noncomputable def vp0111110_6 : Blocks := edgeBlocks% "full/vectors/0111110-V-0006.bin"
private noncomputable def vp0111110_7 : Blocks := edgeBlocks% "full/vectors/0111110-V-0007.bin"
noncomputable def vp0111110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0111110_0 vp0111110_1) (Blocks.join vp0111110_2 vp0111110_3)) (Blocks.join (Blocks.join vp0111110_4 vp0111110_5) (Blocks.join vp0111110_6 vp0111110_7)))
private theorem bp01111100 : Branch 0 (-3967761639/64000000 : ℚ) vp0111110 := by
  apply branch_left_normalized (c:=vp01111100) (k:=0) (m:=517) (by decide +kernel)
  rw [show 2*(-3967761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3967761639/32000000 : ℚ) by norm_num]
  exact coverp01111100
private noncomputable def ep01111101_0 : Blocks := edgeBlocks% "full/vectors/01111101-E-0000.bin"
private noncomputable def ep01111101_1 : Blocks := edgeBlocks% "full/vectors/01111101-E-0001.bin"
private noncomputable def ep01111101_2 : Blocks := edgeBlocks% "full/vectors/01111101-E-0002.bin"
private noncomputable def ep01111101_3 : Blocks := edgeBlocks% "full/vectors/01111101-E-0003.bin"
private noncomputable def ep01111101_4 : Blocks := edgeBlocks% "full/vectors/01111101-E-0004.bin"
private noncomputable def ep01111101_5 : Blocks := edgeBlocks% "full/vectors/01111101-E-0005.bin"
private noncomputable def ep01111101_6 : Blocks := edgeBlocks% "full/vectors/01111101-E-0006.bin"
private noncomputable def ep01111101_7 : Blocks := edgeBlocks% "full/vectors/01111101-E-0007.bin"
noncomputable def ep01111101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01111101_0 ep01111101_1) (Blocks.join ep01111101_2 ep01111101_3)) (Blocks.join (Blocks.join ep01111101_4 ep01111101_5) (Blocks.join ep01111101_6 ep01111101_7)))
private theorem idp01111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111110.list =
    C ((2:ℤ)^1188) * horner X vp01111101.list + horner X ep01111101.list := by
  exact edge_identity (B := (2:ℤ)^1632) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111101 : Branch 1 (-3967761639/64000000 : ℚ) vp0111110 := by
  apply branch_checked idp01111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3967761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3999761639/32000000 : ℚ) by norm_num]
  exact coverp01111101
theorem coverp0111110 : Covers (-3967761639/64000000 : ℚ) vp0111110 := join_branches bp01111100 bp01111101
private noncomputable def vp011111_0 : Blocks := edgeBlocks% "full/vectors/011111-V-0000.bin"
private noncomputable def vp011111_1 : Blocks := edgeBlocks% "full/vectors/011111-V-0001.bin"
private noncomputable def vp011111_2 : Blocks := edgeBlocks% "full/vectors/011111-V-0002.bin"
private noncomputable def vp011111_3 : Blocks := edgeBlocks% "full/vectors/011111-V-0003.bin"
private noncomputable def vp011111_4 : Blocks := edgeBlocks% "full/vectors/011111-V-0004.bin"
private noncomputable def vp011111_5 : Blocks := edgeBlocks% "full/vectors/011111-V-0005.bin"
private noncomputable def vp011111_6 : Blocks := edgeBlocks% "full/vectors/011111-V-0006.bin"
private noncomputable def vp011111_7 : Blocks := edgeBlocks% "full/vectors/011111-V-0007.bin"
private noncomputable def vp011111_8 : Blocks := edgeBlocks% "full/vectors/011111-V-0008.bin"
private noncomputable def vp011111_9 : Blocks := edgeBlocks% "full/vectors/011111-V-0009.bin"
private noncomputable def vp011111_10 : Blocks := edgeBlocks% "full/vectors/011111-V-0010.bin"
private noncomputable def vp011111_11 : Blocks := edgeBlocks% "full/vectors/011111-V-0011.bin"
private noncomputable def vp011111_12 : Blocks := edgeBlocks% "full/vectors/011111-V-0012.bin"
private noncomputable def vp011111_13 : Blocks := edgeBlocks% "full/vectors/011111-V-0013.bin"
private noncomputable def vp011111_14 : Blocks := edgeBlocks% "full/vectors/011111-V-0014.bin"
private noncomputable def vp011111_15 : Blocks := edgeBlocks% "full/vectors/011111-V-0015.bin"
noncomputable def vp011111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp011111_0 vp011111_1) (Blocks.join vp011111_2 vp011111_3)) (Blocks.join (Blocks.join vp011111_4 vp011111_5) (Blocks.join vp011111_6 vp011111_7))) (Blocks.join (Blocks.join (Blocks.join vp011111_8 vp011111_9) (Blocks.join vp011111_10 vp011111_11)) (Blocks.join (Blocks.join vp011111_12 vp011111_13) (Blocks.join vp011111_14 vp011111_15))))
private theorem bp0111110 : Branch 0 (-3967761639/128000000 : ℚ) vp011111 := by
  apply branch_left_normalized (c:=vp0111110) (k:=0) (m:=1005) (by decide +kernel)
  rw [show 2*(-3967761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-3967761639/64000000 : ℚ) by norm_num]
  exact coverp0111110
private noncomputable def ep0111111_0 : Blocks := edgeBlocks% "full/vectors/0111111-E-0000.bin"
private noncomputable def ep0111111_1 : Blocks := edgeBlocks% "full/vectors/0111111-E-0001.bin"
private noncomputable def ep0111111_2 : Blocks := edgeBlocks% "full/vectors/0111111-E-0002.bin"
private noncomputable def ep0111111_3 : Blocks := edgeBlocks% "full/vectors/0111111-E-0003.bin"
private noncomputable def ep0111111_4 : Blocks := edgeBlocks% "full/vectors/0111111-E-0004.bin"
private noncomputable def ep0111111_5 : Blocks := edgeBlocks% "full/vectors/0111111-E-0005.bin"
private noncomputable def ep0111111_6 : Blocks := edgeBlocks% "full/vectors/0111111-E-0006.bin"
private noncomputable def ep0111111_7 : Blocks := edgeBlocks% "full/vectors/0111111-E-0007.bin"
private noncomputable def ep0111111_8 : Blocks := edgeBlocks% "full/vectors/0111111-E-0008.bin"
private noncomputable def ep0111111_9 : Blocks := edgeBlocks% "full/vectors/0111111-E-0009.bin"
private noncomputable def ep0111111_10 : Blocks := edgeBlocks% "full/vectors/0111111-E-0010.bin"
private noncomputable def ep0111111_11 : Blocks := edgeBlocks% "full/vectors/0111111-E-0011.bin"
private noncomputable def ep0111111_12 : Blocks := edgeBlocks% "full/vectors/0111111-E-0012.bin"
private noncomputable def ep0111111_13 : Blocks := edgeBlocks% "full/vectors/0111111-E-0013.bin"
private noncomputable def ep0111111_14 : Blocks := edgeBlocks% "full/vectors/0111111-E-0014.bin"
private noncomputable def ep0111111_15 : Blocks := edgeBlocks% "full/vectors/0111111-E-0015.bin"
noncomputable def ep0111111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0111111_0 ep0111111_1) (Blocks.join ep0111111_2 ep0111111_3)) (Blocks.join (Blocks.join ep0111111_4 ep0111111_5) (Blocks.join ep0111111_6 ep0111111_7))) (Blocks.join (Blocks.join (Blocks.join ep0111111_8 ep0111111_9) (Blocks.join ep0111111_10 ep0111111_11)) (Blocks.join (Blocks.join ep0111111_12 ep0111111_13) (Blocks.join ep0111111_14 ep0111111_15))))
private theorem idp0111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011111.list =
    C ((2:ℤ)^2326) * horner X vp0111111.list + horner X ep0111111.list := by
  exact edge_identity (B := (2:ℤ)^3107) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111111 : Branch 1 (-3967761639/128000000 : ℚ) vp011111 := by
  apply branch_checked idp0111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3967761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-4031761639/64000000 : ℚ) by norm_num]
  exact coverp0111111
theorem coverp011111 : Covers (-3967761639/128000000 : ℚ) vp011111 := join_branches bp0111110 bp0111111
private noncomputable def vp01111011111_0 : Blocks := edgeBlocks% "full/vectors/01111011111-V-0000.bin"
noncomputable def vp01111011111 : Blocks := vp01111011111_0
theorem coverp01111011111 : Covers (-3963761639/4000000 : ℚ) vp01111011111 := cover_leaf (by decide +kernel)
private noncomputable def vp01111011110_0 : Blocks := edgeBlocks% "full/vectors/01111011110-V-0000.bin"
noncomputable def vp01111011110 : Blocks := vp01111011110_0
theorem coverp01111011110 : Covers (-3959761639/4000000 : ℚ) vp01111011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111101111_0 : Blocks := edgeBlocks% "full/vectors/0111101111-V-0000.bin"
private noncomputable def vp0111101111_1 : Blocks := edgeBlocks% "full/vectors/0111101111-V-0001.bin"
noncomputable def vp0111101111 : Blocks := (Blocks.join vp0111101111_0 vp0111101111_1)
private theorem bp01111011110 : Branch 0 (-3959761639/8000000 : ℚ) vp0111101111 := by
  apply branch_left_normalized (c:=vp01111011110) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-3959761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3959761639/4000000 : ℚ) by norm_num]
  exact coverp01111011110
private noncomputable def ep01111011111_0 : Blocks := edgeBlocks% "full/vectors/01111011111-E-0000.bin"
private noncomputable def ep01111011111_1 : Blocks := edgeBlocks% "full/vectors/01111011111-E-0001.bin"
noncomputable def ep01111011111 : Blocks := (Blocks.join ep01111011111_0 ep01111011111_1)
private theorem idp01111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111101111.list =
    C ((2:ℤ)^165) * horner X vp01111011111.list + horner X ep01111011111.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111011111 : Branch 1 (-3959761639/8000000 : ℚ) vp0111101111 := by
  apply branch_checked idp01111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3959761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3963761639/4000000 : ℚ) by norm_num]
  exact coverp01111011111
theorem coverp0111101111 : Covers (-3959761639/8000000 : ℚ) vp0111101111 := join_branches bp01111011110 bp01111011111
private noncomputable def vp01111011101_0 : Blocks := edgeBlocks% "full/vectors/01111011101-V-0000.bin"
noncomputable def vp01111011101 : Blocks := vp01111011101_0
theorem coverp01111011101 : Covers (-3955761639/4000000 : ℚ) vp01111011101 := cover_leaf (by decide +kernel)
private noncomputable def vp01111011100_0 : Blocks := edgeBlocks% "full/vectors/01111011100-V-0000.bin"
noncomputable def vp01111011100 : Blocks := vp01111011100_0
theorem coverp01111011100 : Covers (-3951761639/4000000 : ℚ) vp01111011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111101110_0 : Blocks := edgeBlocks% "full/vectors/0111101110-V-0000.bin"
private noncomputable def vp0111101110_1 : Blocks := edgeBlocks% "full/vectors/0111101110-V-0001.bin"
noncomputable def vp0111101110 : Blocks := (Blocks.join vp0111101110_0 vp0111101110_1)
private theorem bp01111011100 : Branch 0 (-3951761639/8000000 : ℚ) vp0111101110 := by
  apply branch_left_normalized (c:=vp01111011100) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-3951761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3951761639/4000000 : ℚ) by norm_num]
  exact coverp01111011100
private noncomputable def ep01111011101_0 : Blocks := edgeBlocks% "full/vectors/01111011101-E-0000.bin"
private noncomputable def ep01111011101_1 : Blocks := edgeBlocks% "full/vectors/01111011101-E-0001.bin"
noncomputable def ep01111011101 : Blocks := (Blocks.join ep01111011101_0 ep01111011101_1)
private theorem idp01111011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111101110.list =
    C ((2:ℤ)^166) * horner X vp01111011101.list + horner X ep01111011101.list := by
  exact edge_identity (B := (2:ℤ)^304) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111011101 : Branch 1 (-3951761639/8000000 : ℚ) vp0111101110 := by
  apply branch_checked idp01111011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3951761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3955761639/4000000 : ℚ) by norm_num]
  exact coverp01111011101
theorem coverp0111101110 : Covers (-3951761639/8000000 : ℚ) vp0111101110 := join_branches bp01111011100 bp01111011101
private noncomputable def vp011110111_0 : Blocks := edgeBlocks% "full/vectors/011110111-V-0000.bin"
private noncomputable def vp011110111_1 : Blocks := edgeBlocks% "full/vectors/011110111-V-0001.bin"
private noncomputable def vp011110111_2 : Blocks := edgeBlocks% "full/vectors/011110111-V-0002.bin"
noncomputable def vp011110111 : Blocks := (Blocks.join vp011110111_0 (Blocks.join vp011110111_1 vp011110111_2))
private theorem bp0111101110 : Branch 0 (-3951761639/16000000 : ℚ) vp011110111 := by
  apply branch_left_normalized (c:=vp0111101110) (k:=0) (m:=142) (by decide +kernel)
  rw [show 2*(-3951761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3951761639/8000000 : ℚ) by norm_num]
  exact coverp0111101110
private noncomputable def ep0111101111_0 : Blocks := edgeBlocks% "full/vectors/0111101111-E-0000.bin"
private noncomputable def ep0111101111_1 : Blocks := edgeBlocks% "full/vectors/0111101111-E-0001.bin"
private noncomputable def ep0111101111_2 : Blocks := edgeBlocks% "full/vectors/0111101111-E-0002.bin"
noncomputable def ep0111101111 : Blocks := (Blocks.join ep0111101111_0 (Blocks.join ep0111101111_1 ep0111101111_2))
private theorem idp0111101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011110111.list =
    C ((2:ℤ)^313) * horner X vp0111101111.list + horner X ep0111101111.list := by
  exact edge_identity (B := (2:ℤ)^495) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111101111 : Branch 1 (-3951761639/16000000 : ℚ) vp011110111 := by
  apply branch_checked idp0111101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3951761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3959761639/8000000 : ℚ) by norm_num]
  exact coverp0111101111
theorem coverp011110111 : Covers (-3951761639/16000000 : ℚ) vp011110111 := join_branches bp0111101110 bp0111101111
private noncomputable def vp01111011011_0 : Blocks := edgeBlocks% "full/vectors/01111011011-V-0000.bin"
noncomputable def vp01111011011 : Blocks := vp01111011011_0
theorem coverp01111011011 : Covers (-3947761639/4000000 : ℚ) vp01111011011 := cover_leaf (by decide +kernel)
private noncomputable def vp01111011010_0 : Blocks := edgeBlocks% "full/vectors/01111011010-V-0000.bin"
noncomputable def vp01111011010 : Blocks := vp01111011010_0
theorem coverp01111011010 : Covers (-3943761639/4000000 : ℚ) vp01111011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111101101_0 : Blocks := edgeBlocks% "full/vectors/0111101101-V-0000.bin"
private noncomputable def vp0111101101_1 : Blocks := edgeBlocks% "full/vectors/0111101101-V-0001.bin"
noncomputable def vp0111101101 : Blocks := (Blocks.join vp0111101101_0 vp0111101101_1)
private theorem bp01111011010 : Branch 0 (-3943761639/8000000 : ℚ) vp0111101101 := by
  apply branch_left_normalized (c:=vp01111011010) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-3943761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3943761639/4000000 : ℚ) by norm_num]
  exact coverp01111011010
private noncomputable def ep01111011011_0 : Blocks := edgeBlocks% "full/vectors/01111011011-E-0000.bin"
private noncomputable def ep01111011011_1 : Blocks := edgeBlocks% "full/vectors/01111011011-E-0001.bin"
noncomputable def ep01111011011 : Blocks := (Blocks.join ep01111011011_0 ep01111011011_1)
private theorem idp01111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111101101.list =
    C ((2:ℤ)^165) * horner X vp01111011011.list + horner X ep01111011011.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111011011 : Branch 1 (-3943761639/8000000 : ℚ) vp0111101101 := by
  apply branch_checked idp01111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3943761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3947761639/4000000 : ℚ) by norm_num]
  exact coverp01111011011
theorem coverp0111101101 : Covers (-3943761639/8000000 : ℚ) vp0111101101 := join_branches bp01111011010 bp01111011011
private noncomputable def vp01111011001_0 : Blocks := edgeBlocks% "full/vectors/01111011001-V-0000.bin"
noncomputable def vp01111011001 : Blocks := vp01111011001_0
theorem coverp01111011001 : Covers (-3939761639/4000000 : ℚ) vp01111011001 := cover_leaf (by decide +kernel)
private noncomputable def vp01111011000_0 : Blocks := edgeBlocks% "full/vectors/01111011000-V-0000.bin"
noncomputable def vp01111011000 : Blocks := vp01111011000_0
theorem coverp01111011000 : Covers (-3935761639/4000000 : ℚ) vp01111011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111101100_0 : Blocks := edgeBlocks% "full/vectors/0111101100-V-0000.bin"
private noncomputable def vp0111101100_1 : Blocks := edgeBlocks% "full/vectors/0111101100-V-0001.bin"
noncomputable def vp0111101100 : Blocks := (Blocks.join vp0111101100_0 vp0111101100_1)
private theorem bp01111011000 : Branch 0 (-3935761639/8000000 : ℚ) vp0111101100 := by
  apply branch_left_normalized (c:=vp01111011000) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-3935761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3935761639/4000000 : ℚ) by norm_num]
  exact coverp01111011000
private noncomputable def ep01111011001_0 : Blocks := edgeBlocks% "full/vectors/01111011001-E-0000.bin"
private noncomputable def ep01111011001_1 : Blocks := edgeBlocks% "full/vectors/01111011001-E-0001.bin"
noncomputable def ep01111011001 : Blocks := (Blocks.join ep01111011001_0 ep01111011001_1)
private theorem idp01111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111101100.list =
    C ((2:ℤ)^166) * horner X vp01111011001.list + horner X ep01111011001.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111011001 : Branch 1 (-3935761639/8000000 : ℚ) vp0111101100 := by
  apply branch_checked idp01111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3935761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3939761639/4000000 : ℚ) by norm_num]
  exact coverp01111011001
theorem coverp0111101100 : Covers (-3935761639/8000000 : ℚ) vp0111101100 := join_branches bp01111011000 bp01111011001
private noncomputable def vp011110110_0 : Blocks := edgeBlocks% "full/vectors/011110110-V-0000.bin"
private noncomputable def vp011110110_1 : Blocks := edgeBlocks% "full/vectors/011110110-V-0001.bin"
private noncomputable def vp011110110_2 : Blocks := edgeBlocks% "full/vectors/011110110-V-0002.bin"
noncomputable def vp011110110 : Blocks := (Blocks.join vp011110110_0 (Blocks.join vp011110110_1 vp011110110_2))
private theorem bp0111101100 : Branch 0 (-3935761639/16000000 : ℚ) vp011110110 := by
  apply branch_left_normalized (c:=vp0111101100) (k:=0) (m:=142) (by decide +kernel)
  rw [show 2*(-3935761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3935761639/8000000 : ℚ) by norm_num]
  exact coverp0111101100
private noncomputable def ep0111101101_0 : Blocks := edgeBlocks% "full/vectors/0111101101-E-0000.bin"
private noncomputable def ep0111101101_1 : Blocks := edgeBlocks% "full/vectors/0111101101-E-0001.bin"
private noncomputable def ep0111101101_2 : Blocks := edgeBlocks% "full/vectors/0111101101-E-0002.bin"
noncomputable def ep0111101101 : Blocks := (Blocks.join ep0111101101_0 (Blocks.join ep0111101101_1 ep0111101101_2))
private theorem idp0111101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011110110.list =
    C ((2:ℤ)^314) * horner X vp0111101101.list + horner X ep0111101101.list := by
  exact edge_identity (B := (2:ℤ)^494) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111101101 : Branch 1 (-3935761639/16000000 : ℚ) vp011110110 := by
  apply branch_checked idp0111101101 (by positivity) (by decide +kernel)
  rw [show 2*(-3935761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3943761639/8000000 : ℚ) by norm_num]
  exact coverp0111101101
theorem coverp011110110 : Covers (-3935761639/16000000 : ℚ) vp011110110 := join_branches bp0111101100 bp0111101101
private noncomputable def vp01111011_0 : Blocks := edgeBlocks% "full/vectors/01111011-V-0000.bin"
private noncomputable def vp01111011_1 : Blocks := edgeBlocks% "full/vectors/01111011-V-0001.bin"
private noncomputable def vp01111011_2 : Blocks := edgeBlocks% "full/vectors/01111011-V-0002.bin"
private noncomputable def vp01111011_3 : Blocks := edgeBlocks% "full/vectors/01111011-V-0003.bin"
private noncomputable def vp01111011_4 : Blocks := edgeBlocks% "full/vectors/01111011-V-0004.bin"
noncomputable def vp01111011 : Blocks := (Blocks.join (Blocks.join vp01111011_0 vp01111011_1) (Blocks.join vp01111011_2 (Blocks.join vp01111011_3 vp01111011_4)))
private theorem bp011110110 : Branch 0 (-3935761639/32000000 : ℚ) vp01111011 := by
  apply branch_left_normalized (c:=vp011110110) (k:=0) (m:=267) (by decide +kernel)
  rw [show 2*(-3935761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3935761639/16000000 : ℚ) by norm_num]
  exact coverp011110110
private noncomputable def ep011110111_0 : Blocks := edgeBlocks% "full/vectors/011110111-E-0000.bin"
private noncomputable def ep011110111_1 : Blocks := edgeBlocks% "full/vectors/011110111-E-0001.bin"
private noncomputable def ep011110111_2 : Blocks := edgeBlocks% "full/vectors/011110111-E-0002.bin"
private noncomputable def ep011110111_3 : Blocks := edgeBlocks% "full/vectors/011110111-E-0003.bin"
private noncomputable def ep011110111_4 : Blocks := edgeBlocks% "full/vectors/011110111-E-0004.bin"
noncomputable def ep011110111 : Blocks := (Blocks.join (Blocks.join ep011110111_0 ep011110111_1) (Blocks.join ep011110111_2 (Blocks.join ep011110111_3 ep011110111_4)))
private theorem idp011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01111011.list =
    C ((2:ℤ)^606) * horner X vp011110111.list + horner X ep011110111.list := by
  exact edge_identity (B := (2:ℤ)^873) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011110111 : Branch 1 (-3935761639/32000000 : ℚ) vp01111011 := by
  apply branch_checked idp011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3935761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3951761639/16000000 : ℚ) by norm_num]
  exact coverp011110111
theorem coverp01111011 : Covers (-3935761639/32000000 : ℚ) vp01111011 := join_branches bp011110110 bp011110111
private noncomputable def vp0111101011_0 : Blocks := edgeBlocks% "full/vectors/0111101011-V-0000.bin"
private noncomputable def vp0111101011_1 : Blocks := edgeBlocks% "full/vectors/0111101011-V-0001.bin"
noncomputable def vp0111101011 : Blocks := (Blocks.join vp0111101011_0 vp0111101011_1)
theorem coverp0111101011 : Covers (-3927761639/8000000 : ℚ) vp0111101011 := cover_leaf (by decide +kernel)
private noncomputable def vp01111010101_0 : Blocks := edgeBlocks% "full/vectors/01111010101-V-0000.bin"
noncomputable def vp01111010101 : Blocks := vp01111010101_0
theorem coverp01111010101 : Covers (-3923761639/4000000 : ℚ) vp01111010101 := cover_leaf (by decide +kernel)
private noncomputable def vp01111010100_0 : Blocks := edgeBlocks% "full/vectors/01111010100-V-0000.bin"
noncomputable def vp01111010100 : Blocks := vp01111010100_0
theorem coverp01111010100 : Covers (-3919761639/4000000 : ℚ) vp01111010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111101010_0 : Blocks := edgeBlocks% "full/vectors/0111101010-V-0000.bin"
private noncomputable def vp0111101010_1 : Blocks := edgeBlocks% "full/vectors/0111101010-V-0001.bin"
noncomputable def vp0111101010 : Blocks := (Blocks.join vp0111101010_0 vp0111101010_1)
private theorem bp01111010100 : Branch 0 (-3919761639/8000000 : ℚ) vp0111101010 := by
  apply branch_left_normalized (c:=vp01111010100) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-3919761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3919761639/4000000 : ℚ) by norm_num]
  exact coverp01111010100
private noncomputable def ep01111010101_0 : Blocks := edgeBlocks% "full/vectors/01111010101-E-0000.bin"
private noncomputable def ep01111010101_1 : Blocks := edgeBlocks% "full/vectors/01111010101-E-0001.bin"
noncomputable def ep01111010101 : Blocks := (Blocks.join ep01111010101_0 ep01111010101_1)
private theorem idp01111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111101010.list =
    C ((2:ℤ)^168) * horner X vp01111010101.list + horner X ep01111010101.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111010101 : Branch 1 (-3919761639/8000000 : ℚ) vp0111101010 := by
  apply branch_checked idp01111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-3919761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3923761639/4000000 : ℚ) by norm_num]
  exact coverp01111010101
theorem coverp0111101010 : Covers (-3919761639/8000000 : ℚ) vp0111101010 := join_branches bp01111010100 bp01111010101
private noncomputable def vp011110101_0 : Blocks := edgeBlocks% "full/vectors/011110101-V-0000.bin"
private noncomputable def vp011110101_1 : Blocks := edgeBlocks% "full/vectors/011110101-V-0001.bin"
private noncomputable def vp011110101_2 : Blocks := edgeBlocks% "full/vectors/011110101-V-0002.bin"
noncomputable def vp011110101 : Blocks := (Blocks.join vp011110101_0 (Blocks.join vp011110101_1 vp011110101_2))
private theorem bp0111101010 : Branch 0 (-3919761639/16000000 : ℚ) vp011110101 := by
  apply branch_left_normalized (c:=vp0111101010) (k:=0) (m:=143) (by decide +kernel)
  rw [show 2*(-3919761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3919761639/8000000 : ℚ) by norm_num]
  exact coverp0111101010
private noncomputable def ep0111101011_0 : Blocks := edgeBlocks% "full/vectors/0111101011-E-0000.bin"
private noncomputable def ep0111101011_1 : Blocks := edgeBlocks% "full/vectors/0111101011-E-0001.bin"
private noncomputable def ep0111101011_2 : Blocks := edgeBlocks% "full/vectors/0111101011-E-0002.bin"
noncomputable def ep0111101011 : Blocks := (Blocks.join ep0111101011_0 (Blocks.join ep0111101011_1 ep0111101011_2))
private theorem idp0111101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011110101.list =
    C ((2:ℤ)^317) * horner X vp0111101011.list + horner X ep0111101011.list := by
  exact edge_identity (B := (2:ℤ)^497) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111101011 : Branch 1 (-3919761639/16000000 : ℚ) vp011110101 := by
  apply branch_checked idp0111101011 (by positivity) (by decide +kernel)
  rw [show 2*(-3919761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3927761639/8000000 : ℚ) by norm_num]
  exact coverp0111101011
theorem coverp011110101 : Covers (-3919761639/16000000 : ℚ) vp011110101 := join_branches bp0111101010 bp0111101011
private noncomputable def vp01111010011_0 : Blocks := edgeBlocks% "full/vectors/01111010011-V-0000.bin"
noncomputable def vp01111010011 : Blocks := vp01111010011_0
theorem coverp01111010011 : Covers (-3915761639/4000000 : ℚ) vp01111010011 := cover_leaf (by decide +kernel)
private noncomputable def vp01111010010_0 : Blocks := edgeBlocks% "full/vectors/01111010010-V-0000.bin"
noncomputable def vp01111010010 : Blocks := vp01111010010_0
theorem coverp01111010010 : Covers (-3911761639/4000000 : ℚ) vp01111010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111101001_0 : Blocks := edgeBlocks% "full/vectors/0111101001-V-0000.bin"
private noncomputable def vp0111101001_1 : Blocks := edgeBlocks% "full/vectors/0111101001-V-0001.bin"
noncomputable def vp0111101001 : Blocks := (Blocks.join vp0111101001_0 vp0111101001_1)
private theorem bp01111010010 : Branch 0 (-3911761639/8000000 : ℚ) vp0111101001 := by
  apply branch_left_normalized (c:=vp01111010010) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-3911761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3911761639/4000000 : ℚ) by norm_num]
  exact coverp01111010010
private noncomputable def ep01111010011_0 : Blocks := edgeBlocks% "full/vectors/01111010011-E-0000.bin"
private noncomputable def ep01111010011_1 : Blocks := edgeBlocks% "full/vectors/01111010011-E-0001.bin"
noncomputable def ep01111010011 : Blocks := (Blocks.join ep01111010011_0 ep01111010011_1)
private theorem idp01111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111101001.list =
    C ((2:ℤ)^170) * horner X vp01111010011.list + horner X ep01111010011.list := by
  exact edge_identity (B := (2:ℤ)^309) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111010011 : Branch 1 (-3911761639/8000000 : ℚ) vp0111101001 := by
  apply branch_checked idp01111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-3911761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3915761639/4000000 : ℚ) by norm_num]
  exact coverp01111010011
theorem coverp0111101001 : Covers (-3911761639/8000000 : ℚ) vp0111101001 := join_branches bp01111010010 bp01111010011
private noncomputable def vp01111010001_0 : Blocks := edgeBlocks% "full/vectors/01111010001-V-0000.bin"
noncomputable def vp01111010001 : Blocks := vp01111010001_0
theorem coverp01111010001 : Covers (-3907761639/4000000 : ℚ) vp01111010001 := cover_leaf (by decide +kernel)
private noncomputable def vp01111010000_0 : Blocks := edgeBlocks% "full/vectors/01111010000-V-0000.bin"
noncomputable def vp01111010000 : Blocks := vp01111010000_0
theorem coverp01111010000 : Covers (-3903761639/4000000 : ℚ) vp01111010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111101000_0 : Blocks := edgeBlocks% "full/vectors/0111101000-V-0000.bin"
private noncomputable def vp0111101000_1 : Blocks := edgeBlocks% "full/vectors/0111101000-V-0001.bin"
noncomputable def vp0111101000 : Blocks := (Blocks.join vp0111101000_0 vp0111101000_1)
private theorem bp01111010000 : Branch 0 (-3903761639/8000000 : ℚ) vp0111101000 := by
  apply branch_left_normalized (c:=vp01111010000) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3903761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3903761639/4000000 : ℚ) by norm_num]
  exact coverp01111010000
private noncomputable def ep01111010001_0 : Blocks := edgeBlocks% "full/vectors/01111010001-E-0000.bin"
private noncomputable def ep01111010001_1 : Blocks := edgeBlocks% "full/vectors/01111010001-E-0001.bin"
noncomputable def ep01111010001 : Blocks := (Blocks.join ep01111010001_0 ep01111010001_1)
private theorem idp01111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111101000.list =
    C ((2:ℤ)^174) * horner X vp01111010001.list + horner X ep01111010001.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111010001 : Branch 1 (-3903761639/8000000 : ℚ) vp0111101000 := by
  apply branch_checked idp01111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3903761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3907761639/4000000 : ℚ) by norm_num]
  exact coverp01111010001
theorem coverp0111101000 : Covers (-3903761639/8000000 : ℚ) vp0111101000 := join_branches bp01111010000 bp01111010001
private noncomputable def vp011110100_0 : Blocks := edgeBlocks% "full/vectors/011110100-V-0000.bin"
private noncomputable def vp011110100_1 : Blocks := edgeBlocks% "full/vectors/011110100-V-0001.bin"
private noncomputable def vp011110100_2 : Blocks := edgeBlocks% "full/vectors/011110100-V-0002.bin"
noncomputable def vp011110100 : Blocks := (Blocks.join vp011110100_0 (Blocks.join vp011110100_1 vp011110100_2))
private theorem bp0111101000 : Branch 0 (-3903761639/16000000 : ℚ) vp011110100 := by
  apply branch_left_normalized (c:=vp0111101000) (k:=0) (m:=148) (by decide +kernel)
  rw [show 2*(-3903761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3903761639/8000000 : ℚ) by norm_num]
  exact coverp0111101000
private noncomputable def ep0111101001_0 : Blocks := edgeBlocks% "full/vectors/0111101001-E-0000.bin"
private noncomputable def ep0111101001_1 : Blocks := edgeBlocks% "full/vectors/0111101001-E-0001.bin"
private noncomputable def ep0111101001_2 : Blocks := edgeBlocks% "full/vectors/0111101001-E-0002.bin"
noncomputable def ep0111101001 : Blocks := (Blocks.join ep0111101001_0 (Blocks.join ep0111101001_1 ep0111101001_2))
private theorem idp0111101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011110100.list =
    C ((2:ℤ)^325) * horner X vp0111101001.list + horner X ep0111101001.list := by
  exact edge_identity (B := (2:ℤ)^509) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111101001 : Branch 1 (-3903761639/16000000 : ℚ) vp011110100 := by
  apply branch_checked idp0111101001 (by positivity) (by decide +kernel)
  rw [show 2*(-3903761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3911761639/8000000 : ℚ) by norm_num]
  exact coverp0111101001
theorem coverp011110100 : Covers (-3903761639/16000000 : ℚ) vp011110100 := join_branches bp0111101000 bp0111101001
private noncomputable def vp01111010_0 : Blocks := edgeBlocks% "full/vectors/01111010-V-0000.bin"
private noncomputable def vp01111010_1 : Blocks := edgeBlocks% "full/vectors/01111010-V-0001.bin"
private noncomputable def vp01111010_2 : Blocks := edgeBlocks% "full/vectors/01111010-V-0002.bin"
private noncomputable def vp01111010_3 : Blocks := edgeBlocks% "full/vectors/01111010-V-0003.bin"
private noncomputable def vp01111010_4 : Blocks := edgeBlocks% "full/vectors/01111010-V-0004.bin"
noncomputable def vp01111010 : Blocks := (Blocks.join (Blocks.join vp01111010_0 vp01111010_1) (Blocks.join vp01111010_2 (Blocks.join vp01111010_3 vp01111010_4)))
private theorem bp011110100 : Branch 0 (-3903761639/32000000 : ℚ) vp01111010 := by
  apply branch_left_normalized (c:=vp011110100) (k:=0) (m:=273) (by decide +kernel)
  rw [show 2*(-3903761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3903761639/16000000 : ℚ) by norm_num]
  exact coverp011110100
private noncomputable def ep011110101_0 : Blocks := edgeBlocks% "full/vectors/011110101-E-0000.bin"
private noncomputable def ep011110101_1 : Blocks := edgeBlocks% "full/vectors/011110101-E-0001.bin"
private noncomputable def ep011110101_2 : Blocks := edgeBlocks% "full/vectors/011110101-E-0002.bin"
private noncomputable def ep011110101_3 : Blocks := edgeBlocks% "full/vectors/011110101-E-0003.bin"
private noncomputable def ep011110101_4 : Blocks := edgeBlocks% "full/vectors/011110101-E-0004.bin"
noncomputable def ep011110101 : Blocks := (Blocks.join (Blocks.join ep011110101_0 ep011110101_1) (Blocks.join ep011110101_2 (Blocks.join ep011110101_3 ep011110101_4)))
private theorem idp011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01111010.list =
    C ((2:ℤ)^623) * horner X vp011110101.list + horner X ep011110101.list := by
  exact edge_identity (B := (2:ℤ)^892) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011110101 : Branch 1 (-3903761639/32000000 : ℚ) vp01111010 := by
  apply branch_checked idp011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3903761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3919761639/16000000 : ℚ) by norm_num]
  exact coverp011110101
theorem coverp01111010 : Covers (-3903761639/32000000 : ℚ) vp01111010 := join_branches bp011110100 bp011110101
private noncomputable def vp0111101_0 : Blocks := edgeBlocks% "full/vectors/0111101-V-0000.bin"
private noncomputable def vp0111101_1 : Blocks := edgeBlocks% "full/vectors/0111101-V-0001.bin"
private noncomputable def vp0111101_2 : Blocks := edgeBlocks% "full/vectors/0111101-V-0002.bin"
private noncomputable def vp0111101_3 : Blocks := edgeBlocks% "full/vectors/0111101-V-0003.bin"
private noncomputable def vp0111101_4 : Blocks := edgeBlocks% "full/vectors/0111101-V-0004.bin"
private noncomputable def vp0111101_5 : Blocks := edgeBlocks% "full/vectors/0111101-V-0005.bin"
private noncomputable def vp0111101_6 : Blocks := edgeBlocks% "full/vectors/0111101-V-0006.bin"
private noncomputable def vp0111101_7 : Blocks := edgeBlocks% "full/vectors/0111101-V-0007.bin"
noncomputable def vp0111101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0111101_0 vp0111101_1) (Blocks.join vp0111101_2 vp0111101_3)) (Blocks.join (Blocks.join vp0111101_4 vp0111101_5) (Blocks.join vp0111101_6 vp0111101_7)))
private theorem bp01111010 : Branch 0 (-3903761639/64000000 : ℚ) vp0111101 := by
  apply branch_left_normalized (c:=vp01111010) (k:=0) (m:=523) (by decide +kernel)
  rw [show 2*(-3903761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3903761639/32000000 : ℚ) by norm_num]
  exact coverp01111010
private noncomputable def ep01111011_0 : Blocks := edgeBlocks% "full/vectors/01111011-E-0000.bin"
private noncomputable def ep01111011_1 : Blocks := edgeBlocks% "full/vectors/01111011-E-0001.bin"
private noncomputable def ep01111011_2 : Blocks := edgeBlocks% "full/vectors/01111011-E-0002.bin"
private noncomputable def ep01111011_3 : Blocks := edgeBlocks% "full/vectors/01111011-E-0003.bin"
private noncomputable def ep01111011_4 : Blocks := edgeBlocks% "full/vectors/01111011-E-0004.bin"
private noncomputable def ep01111011_5 : Blocks := edgeBlocks% "full/vectors/01111011-E-0005.bin"
private noncomputable def ep01111011_6 : Blocks := edgeBlocks% "full/vectors/01111011-E-0006.bin"
private noncomputable def ep01111011_7 : Blocks := edgeBlocks% "full/vectors/01111011-E-0007.bin"
noncomputable def ep01111011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01111011_0 ep01111011_1) (Blocks.join ep01111011_2 ep01111011_3)) (Blocks.join (Blocks.join ep01111011_4 ep01111011_5) (Blocks.join ep01111011_6 ep01111011_7)))
private theorem idp01111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111101.list =
    C ((2:ℤ)^1208) * horner X vp01111011.list + horner X ep01111011.list := by
  exact edge_identity (B := (2:ℤ)^1648) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111011 : Branch 1 (-3903761639/64000000 : ℚ) vp0111101 := by
  apply branch_checked idp01111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3903761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3935761639/32000000 : ℚ) by norm_num]
  exact coverp01111011
theorem coverp0111101 : Covers (-3903761639/64000000 : ℚ) vp0111101 := join_branches bp01111010 bp01111011
private noncomputable def vp01111001111_0 : Blocks := edgeBlocks% "full/vectors/01111001111-V-0000.bin"
noncomputable def vp01111001111 : Blocks := vp01111001111_0
theorem coverp01111001111 : Covers (-3899761639/4000000 : ℚ) vp01111001111 := cover_leaf (by decide +kernel)
private noncomputable def vp01111001110_0 : Blocks := edgeBlocks% "full/vectors/01111001110-V-0000.bin"
noncomputable def vp01111001110 : Blocks := vp01111001110_0
theorem coverp01111001110 : Covers (-3895761639/4000000 : ℚ) vp01111001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111100111_0 : Blocks := edgeBlocks% "full/vectors/0111100111-V-0000.bin"
private noncomputable def vp0111100111_1 : Blocks := edgeBlocks% "full/vectors/0111100111-V-0001.bin"
noncomputable def vp0111100111 : Blocks := (Blocks.join vp0111100111_0 vp0111100111_1)
private theorem bp01111001110 : Branch 0 (-3895761639/8000000 : ℚ) vp0111100111 := by
  apply branch_left_normalized (c:=vp01111001110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3895761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3895761639/4000000 : ℚ) by norm_num]
  exact coverp01111001110
private noncomputable def ep01111001111_0 : Blocks := edgeBlocks% "full/vectors/01111001111-E-0000.bin"
private noncomputable def ep01111001111_1 : Blocks := edgeBlocks% "full/vectors/01111001111-E-0001.bin"
noncomputable def ep01111001111 : Blocks := (Blocks.join ep01111001111_0 ep01111001111_1)
private theorem idp01111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111100111.list =
    C ((2:ℤ)^170) * horner X vp01111001111.list + horner X ep01111001111.list := by
  exact edge_identity (B := (2:ℤ)^315) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111001111 : Branch 1 (-3895761639/8000000 : ℚ) vp0111100111 := by
  apply branch_checked idp01111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3895761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3899761639/4000000 : ℚ) by norm_num]
  exact coverp01111001111
theorem coverp0111100111 : Covers (-3895761639/8000000 : ℚ) vp0111100111 := join_branches bp01111001110 bp01111001111
private noncomputable def vp01111001101_0 : Blocks := edgeBlocks% "full/vectors/01111001101-V-0000.bin"
noncomputable def vp01111001101 : Blocks := vp01111001101_0
theorem coverp01111001101 : Covers (-3891761639/4000000 : ℚ) vp01111001101 := cover_leaf (by decide +kernel)
private noncomputable def vp01111001100_0 : Blocks := edgeBlocks% "full/vectors/01111001100-V-0000.bin"
noncomputable def vp01111001100 : Blocks := vp01111001100_0
theorem coverp01111001100 : Covers (-3887761639/4000000 : ℚ) vp01111001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111100110_0 : Blocks := edgeBlocks% "full/vectors/0111100110-V-0000.bin"
private noncomputable def vp0111100110_1 : Blocks := edgeBlocks% "full/vectors/0111100110-V-0001.bin"
noncomputable def vp0111100110 : Blocks := (Blocks.join vp0111100110_0 vp0111100110_1)
private theorem bp01111001100 : Branch 0 (-3887761639/8000000 : ℚ) vp0111100110 := by
  apply branch_left_normalized (c:=vp01111001100) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3887761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3887761639/4000000 : ℚ) by norm_num]
  exact coverp01111001100
private noncomputable def ep01111001101_0 : Blocks := edgeBlocks% "full/vectors/01111001101-E-0000.bin"
private noncomputable def ep01111001101_1 : Blocks := edgeBlocks% "full/vectors/01111001101-E-0001.bin"
noncomputable def ep01111001101 : Blocks := (Blocks.join ep01111001101_0 ep01111001101_1)
private theorem idp01111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111100110.list =
    C ((2:ℤ)^172) * horner X vp01111001101.list + horner X ep01111001101.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111001101 : Branch 1 (-3887761639/8000000 : ℚ) vp0111100110 := by
  apply branch_checked idp01111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3887761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3891761639/4000000 : ℚ) by norm_num]
  exact coverp01111001101
theorem coverp0111100110 : Covers (-3887761639/8000000 : ℚ) vp0111100110 := join_branches bp01111001100 bp01111001101
private noncomputable def vp011110011_0 : Blocks := edgeBlocks% "full/vectors/011110011-V-0000.bin"
private noncomputable def vp011110011_1 : Blocks := edgeBlocks% "full/vectors/011110011-V-0001.bin"
private noncomputable def vp011110011_2 : Blocks := edgeBlocks% "full/vectors/011110011-V-0002.bin"
noncomputable def vp011110011 : Blocks := (Blocks.join vp011110011_0 (Blocks.join vp011110011_1 vp011110011_2))
private theorem bp0111100110 : Branch 0 (-3887761639/16000000 : ℚ) vp011110011 := by
  apply branch_left_normalized (c:=vp0111100110) (k:=0) (m:=148) (by decide +kernel)
  rw [show 2*(-3887761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3887761639/8000000 : ℚ) by norm_num]
  exact coverp0111100110
private noncomputable def ep0111100111_0 : Blocks := edgeBlocks% "full/vectors/0111100111-E-0000.bin"
private noncomputable def ep0111100111_1 : Blocks := edgeBlocks% "full/vectors/0111100111-E-0001.bin"
private noncomputable def ep0111100111_2 : Blocks := edgeBlocks% "full/vectors/0111100111-E-0002.bin"
noncomputable def ep0111100111 : Blocks := (Blocks.join ep0111100111_0 (Blocks.join ep0111100111_1 ep0111100111_2))
private theorem idp0111100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011110011.list =
    C ((2:ℤ)^322) * horner X vp0111100111.list + horner X ep0111100111.list := by
  exact edge_identity (B := (2:ℤ)^510) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111100111 : Branch 1 (-3887761639/16000000 : ℚ) vp011110011 := by
  apply branch_checked idp0111100111 (by positivity) (by decide +kernel)
  rw [show 2*(-3887761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3895761639/8000000 : ℚ) by norm_num]
  exact coverp0111100111
theorem coverp011110011 : Covers (-3887761639/16000000 : ℚ) vp011110011 := join_branches bp0111100110 bp0111100111
private noncomputable def vp01111001011_0 : Blocks := edgeBlocks% "full/vectors/01111001011-V-0000.bin"
noncomputable def vp01111001011 : Blocks := vp01111001011_0
theorem coverp01111001011 : Covers (-3883761639/4000000 : ℚ) vp01111001011 := cover_leaf (by decide +kernel)
private noncomputable def vp01111001010_0 : Blocks := edgeBlocks% "full/vectors/01111001010-V-0000.bin"
noncomputable def vp01111001010 : Blocks := vp01111001010_0
theorem coverp01111001010 : Covers (-3879761639/4000000 : ℚ) vp01111001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111100101_0 : Blocks := edgeBlocks% "full/vectors/0111100101-V-0000.bin"
private noncomputable def vp0111100101_1 : Blocks := edgeBlocks% "full/vectors/0111100101-V-0001.bin"
noncomputable def vp0111100101 : Blocks := (Blocks.join vp0111100101_0 vp0111100101_1)
private theorem bp01111001010 : Branch 0 (-3879761639/8000000 : ℚ) vp0111100101 := by
  apply branch_left_normalized (c:=vp01111001010) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-3879761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3879761639/4000000 : ℚ) by norm_num]
  exact coverp01111001010
private noncomputable def ep01111001011_0 : Blocks := edgeBlocks% "full/vectors/01111001011-E-0000.bin"
private noncomputable def ep01111001011_1 : Blocks := edgeBlocks% "full/vectors/01111001011-E-0001.bin"
noncomputable def ep01111001011 : Blocks := (Blocks.join ep01111001011_0 ep01111001011_1)
private theorem idp01111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111100101.list =
    C ((2:ℤ)^172) * horner X vp01111001011.list + horner X ep01111001011.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111001011 : Branch 1 (-3879761639/8000000 : ℚ) vp0111100101 := by
  apply branch_checked idp01111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3879761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3883761639/4000000 : ℚ) by norm_num]
  exact coverp01111001011
theorem coverp0111100101 : Covers (-3879761639/8000000 : ℚ) vp0111100101 := join_branches bp01111001010 bp01111001011
private noncomputable def vp01111001001_0 : Blocks := edgeBlocks% "full/vectors/01111001001-V-0000.bin"
noncomputable def vp01111001001 : Blocks := vp01111001001_0
theorem coverp01111001001 : Covers (-3875761639/4000000 : ℚ) vp01111001001 := cover_leaf (by decide +kernel)
private noncomputable def vp01111001000_0 : Blocks := edgeBlocks% "full/vectors/01111001000-V-0000.bin"
noncomputable def vp01111001000 : Blocks := vp01111001000_0
theorem coverp01111001000 : Covers (-3871761639/4000000 : ℚ) vp01111001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111100100_0 : Blocks := edgeBlocks% "full/vectors/0111100100-V-0000.bin"
private noncomputable def vp0111100100_1 : Blocks := edgeBlocks% "full/vectors/0111100100-V-0001.bin"
noncomputable def vp0111100100 : Blocks := (Blocks.join vp0111100100_0 vp0111100100_1)
private theorem bp01111001000 : Branch 0 (-3871761639/8000000 : ℚ) vp0111100100 := by
  apply branch_left_normalized (c:=vp01111001000) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3871761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3871761639/4000000 : ℚ) by norm_num]
  exact coverp01111001000
private noncomputable def ep01111001001_0 : Blocks := edgeBlocks% "full/vectors/01111001001-E-0000.bin"
private noncomputable def ep01111001001_1 : Blocks := edgeBlocks% "full/vectors/01111001001-E-0001.bin"
noncomputable def ep01111001001 : Blocks := (Blocks.join ep01111001001_0 ep01111001001_1)
private theorem idp01111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111100100.list =
    C ((2:ℤ)^172) * horner X vp01111001001.list + horner X ep01111001001.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111001001 : Branch 1 (-3871761639/8000000 : ℚ) vp0111100100 := by
  apply branch_checked idp01111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3871761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3875761639/4000000 : ℚ) by norm_num]
  exact coverp01111001001
theorem coverp0111100100 : Covers (-3871761639/8000000 : ℚ) vp0111100100 := join_branches bp01111001000 bp01111001001
private noncomputable def vp011110010_0 : Blocks := edgeBlocks% "full/vectors/011110010-V-0000.bin"
private noncomputable def vp011110010_1 : Blocks := edgeBlocks% "full/vectors/011110010-V-0001.bin"
private noncomputable def vp011110010_2 : Blocks := edgeBlocks% "full/vectors/011110010-V-0002.bin"
noncomputable def vp011110010 : Blocks := (Blocks.join vp011110010_0 (Blocks.join vp011110010_1 vp011110010_2))
private theorem bp0111100100 : Branch 0 (-3871761639/16000000 : ℚ) vp011110010 := by
  apply branch_left_normalized (c:=vp0111100100) (k:=0) (m:=147) (by decide +kernel)
  rw [show 2*(-3871761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3871761639/8000000 : ℚ) by norm_num]
  exact coverp0111100100
private noncomputable def ep0111100101_0 : Blocks := edgeBlocks% "full/vectors/0111100101-E-0000.bin"
private noncomputable def ep0111100101_1 : Blocks := edgeBlocks% "full/vectors/0111100101-E-0001.bin"
private noncomputable def ep0111100101_2 : Blocks := edgeBlocks% "full/vectors/0111100101-E-0002.bin"
noncomputable def ep0111100101 : Blocks := (Blocks.join ep0111100101_0 (Blocks.join ep0111100101_1 ep0111100101_2))
private theorem idp0111100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011110010.list =
    C ((2:ℤ)^322) * horner X vp0111100101.list + horner X ep0111100101.list := by
  exact edge_identity (B := (2:ℤ)^511) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111100101 : Branch 1 (-3871761639/16000000 : ℚ) vp011110010 := by
  apply branch_checked idp0111100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3871761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3879761639/8000000 : ℚ) by norm_num]
  exact coverp0111100101
theorem coverp011110010 : Covers (-3871761639/16000000 : ℚ) vp011110010 := join_branches bp0111100100 bp0111100101
private noncomputable def vp01111001_0 : Blocks := edgeBlocks% "full/vectors/01111001-V-0000.bin"
private noncomputable def vp01111001_1 : Blocks := edgeBlocks% "full/vectors/01111001-V-0001.bin"
private noncomputable def vp01111001_2 : Blocks := edgeBlocks% "full/vectors/01111001-V-0002.bin"
private noncomputable def vp01111001_3 : Blocks := edgeBlocks% "full/vectors/01111001-V-0003.bin"
private noncomputable def vp01111001_4 : Blocks := edgeBlocks% "full/vectors/01111001-V-0004.bin"
noncomputable def vp01111001 : Blocks := (Blocks.join (Blocks.join vp01111001_0 vp01111001_1) (Blocks.join vp01111001_2 (Blocks.join vp01111001_3 vp01111001_4)))
private theorem bp011110010 : Branch 0 (-3871761639/32000000 : ℚ) vp01111001 := by
  apply branch_left_normalized (c:=vp011110010) (k:=0) (m:=274) (by decide +kernel)
  rw [show 2*(-3871761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3871761639/16000000 : ℚ) by norm_num]
  exact coverp011110010
private noncomputable def ep011110011_0 : Blocks := edgeBlocks% "full/vectors/011110011-E-0000.bin"
private noncomputable def ep011110011_1 : Blocks := edgeBlocks% "full/vectors/011110011-E-0001.bin"
private noncomputable def ep011110011_2 : Blocks := edgeBlocks% "full/vectors/011110011-E-0002.bin"
private noncomputable def ep011110011_3 : Blocks := edgeBlocks% "full/vectors/011110011-E-0003.bin"
private noncomputable def ep011110011_4 : Blocks := edgeBlocks% "full/vectors/011110011-E-0004.bin"
noncomputable def ep011110011 : Blocks := (Blocks.join (Blocks.join ep011110011_0 ep011110011_1) (Blocks.join ep011110011_2 (Blocks.join ep011110011_3 ep011110011_4)))
private theorem idp011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01111001.list =
    C ((2:ℤ)^619) * horner X vp011110011.list + horner X ep011110011.list := by
  exact edge_identity (B := (2:ℤ)^895) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011110011 : Branch 1 (-3871761639/32000000 : ℚ) vp01111001 := by
  apply branch_checked idp011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3871761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3887761639/16000000 : ℚ) by norm_num]
  exact coverp011110011
theorem coverp01111001 : Covers (-3871761639/32000000 : ℚ) vp01111001 := join_branches bp011110010 bp011110011
private noncomputable def vp01111000111_0 : Blocks := edgeBlocks% "full/vectors/01111000111-V-0000.bin"
noncomputable def vp01111000111 : Blocks := vp01111000111_0
theorem coverp01111000111 : Covers (-3867761639/4000000 : ℚ) vp01111000111 := cover_leaf (by decide +kernel)
private noncomputable def vp01111000110_0 : Blocks := edgeBlocks% "full/vectors/01111000110-V-0000.bin"
noncomputable def vp01111000110 : Blocks := vp01111000110_0
theorem coverp01111000110 : Covers (-3863761639/4000000 : ℚ) vp01111000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0111100011_0 : Blocks := edgeBlocks% "full/vectors/0111100011-V-0000.bin"
private noncomputable def vp0111100011_1 : Blocks := edgeBlocks% "full/vectors/0111100011-V-0001.bin"
noncomputable def vp0111100011 : Blocks := (Blocks.join vp0111100011_0 vp0111100011_1)
private theorem bp01111000110 : Branch 0 (-3863761639/8000000 : ℚ) vp0111100011 := by
  apply branch_left_normalized (c:=vp01111000110) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3863761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3863761639/4000000 : ℚ) by norm_num]
  exact coverp01111000110
private noncomputable def ep01111000111_0 : Blocks := edgeBlocks% "full/vectors/01111000111-E-0000.bin"
private noncomputable def ep01111000111_1 : Blocks := edgeBlocks% "full/vectors/01111000111-E-0001.bin"
noncomputable def ep01111000111 : Blocks := (Blocks.join ep01111000111_0 ep01111000111_1)
private theorem idp01111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111100011.list =
    C ((2:ℤ)^172) * horner X vp01111000111.list + horner X ep01111000111.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111000111 : Branch 1 (-3863761639/8000000 : ℚ) vp0111100011 := by
  apply branch_checked idp01111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3863761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3867761639/4000000 : ℚ) by norm_num]
  exact coverp01111000111
theorem coverp0111100011 : Covers (-3863761639/8000000 : ℚ) vp0111100011 := join_branches bp01111000110 bp01111000111
private noncomputable def vp01111000101_0 : Blocks := edgeBlocks% "full/vectors/01111000101-V-0000.bin"
noncomputable def vp01111000101 : Blocks := vp01111000101_0
theorem coverp01111000101 : Covers (-3859761639/4000000 : ℚ) vp01111000101 := cover_leaf (by decide +kernel)
private noncomputable def vp01111000100_0 : Blocks := edgeBlocks% "full/vectors/01111000100-V-0000.bin"
noncomputable def vp01111000100 : Blocks := vp01111000100_0
theorem coverp01111000100 : Covers (-3855761639/4000000 : ℚ) vp01111000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0111100010_0 : Blocks := edgeBlocks% "full/vectors/0111100010-V-0000.bin"
private noncomputable def vp0111100010_1 : Blocks := edgeBlocks% "full/vectors/0111100010-V-0001.bin"
noncomputable def vp0111100010 : Blocks := (Blocks.join vp0111100010_0 vp0111100010_1)
private theorem bp01111000100 : Branch 0 (-3855761639/8000000 : ℚ) vp0111100010 := by
  apply branch_left_normalized (c:=vp01111000100) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3855761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3855761639/4000000 : ℚ) by norm_num]
  exact coverp01111000100
private noncomputable def ep01111000101_0 : Blocks := edgeBlocks% "full/vectors/01111000101-E-0000.bin"
private noncomputable def ep01111000101_1 : Blocks := edgeBlocks% "full/vectors/01111000101-E-0001.bin"
noncomputable def ep01111000101 : Blocks := (Blocks.join ep01111000101_0 ep01111000101_1)
private theorem idp01111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111100010.list =
    C ((2:ℤ)^172) * horner X vp01111000101.list + horner X ep01111000101.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111000101 : Branch 1 (-3855761639/8000000 : ℚ) vp0111100010 := by
  apply branch_checked idp01111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3855761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3859761639/4000000 : ℚ) by norm_num]
  exact coverp01111000101
theorem coverp0111100010 : Covers (-3855761639/8000000 : ℚ) vp0111100010 := join_branches bp01111000100 bp01111000101
private noncomputable def vp011110001_0 : Blocks := edgeBlocks% "full/vectors/011110001-V-0000.bin"
private noncomputable def vp011110001_1 : Blocks := edgeBlocks% "full/vectors/011110001-V-0001.bin"
private noncomputable def vp011110001_2 : Blocks := edgeBlocks% "full/vectors/011110001-V-0002.bin"
noncomputable def vp011110001 : Blocks := (Blocks.join vp011110001_0 (Blocks.join vp011110001_1 vp011110001_2))
private theorem bp0111100010 : Branch 0 (-3855761639/16000000 : ℚ) vp011110001 := by
  apply branch_left_normalized (c:=vp0111100010) (k:=0) (m:=148) (by decide +kernel)
  rw [show 2*(-3855761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3855761639/8000000 : ℚ) by norm_num]
  exact coverp0111100010
private noncomputable def ep0111100011_0 : Blocks := edgeBlocks% "full/vectors/0111100011-E-0000.bin"
private noncomputable def ep0111100011_1 : Blocks := edgeBlocks% "full/vectors/0111100011-E-0001.bin"
private noncomputable def ep0111100011_2 : Blocks := edgeBlocks% "full/vectors/0111100011-E-0002.bin"
noncomputable def ep0111100011 : Blocks := (Blocks.join ep0111100011_0 (Blocks.join ep0111100011_1 ep0111100011_2))
private theorem idp0111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011110001.list =
    C ((2:ℤ)^322) * horner X vp0111100011.list + horner X ep0111100011.list := by
  exact edge_identity (B := (2:ℤ)^512) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111100011 : Branch 1 (-3855761639/16000000 : ℚ) vp011110001 := by
  apply branch_checked idp0111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-3855761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3863761639/8000000 : ℚ) by norm_num]
  exact coverp0111100011
theorem coverp011110001 : Covers (-3855761639/16000000 : ℚ) vp011110001 := join_branches bp0111100010 bp0111100011
private noncomputable def vp01111000011_0 : Blocks := edgeBlocks% "full/vectors/01111000011-V-0000.bin"
noncomputable def vp01111000011 : Blocks := vp01111000011_0
theorem coverp01111000011 : Covers (-3851761639/4000000 : ℚ) vp01111000011 := cover_leaf (by decide +kernel)
private noncomputable def vp01111000010_0 : Blocks := edgeBlocks% "full/vectors/01111000010-V-0000.bin"
noncomputable def vp01111000010 : Blocks := vp01111000010_0
theorem coverp01111000010 : Covers (-3847761639/4000000 : ℚ) vp01111000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0111100001_0 : Blocks := edgeBlocks% "full/vectors/0111100001-V-0000.bin"
private noncomputable def vp0111100001_1 : Blocks := edgeBlocks% "full/vectors/0111100001-V-0001.bin"
noncomputable def vp0111100001 : Blocks := (Blocks.join vp0111100001_0 vp0111100001_1)
private theorem bp01111000010 : Branch 0 (-3847761639/8000000 : ℚ) vp0111100001 := by
  apply branch_left_normalized (c:=vp01111000010) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3847761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3847761639/4000000 : ℚ) by norm_num]
  exact coverp01111000010
private noncomputable def ep01111000011_0 : Blocks := edgeBlocks% "full/vectors/01111000011-E-0000.bin"
private noncomputable def ep01111000011_1 : Blocks := edgeBlocks% "full/vectors/01111000011-E-0001.bin"
noncomputable def ep01111000011 : Blocks := (Blocks.join ep01111000011_0 ep01111000011_1)
private theorem idp01111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111100001.list =
    C ((2:ℤ)^172) * horner X vp01111000011.list + horner X ep01111000011.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111000011 : Branch 1 (-3847761639/8000000 : ℚ) vp0111100001 := by
  apply branch_checked idp01111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3847761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3851761639/4000000 : ℚ) by norm_num]
  exact coverp01111000011
theorem coverp0111100001 : Covers (-3847761639/8000000 : ℚ) vp0111100001 := join_branches bp01111000010 bp01111000011
private noncomputable def vp01111000001_0 : Blocks := edgeBlocks% "full/vectors/01111000001-V-0000.bin"
noncomputable def vp01111000001 : Blocks := vp01111000001_0
theorem coverp01111000001 : Covers (-3843761639/4000000 : ℚ) vp01111000001 := cover_leaf (by decide +kernel)
private noncomputable def vp01111000000_0 : Blocks := edgeBlocks% "full/vectors/01111000000-V-0000.bin"
noncomputable def vp01111000000 : Blocks := vp01111000000_0
theorem coverp01111000000 : Covers (-3839761639/4000000 : ℚ) vp01111000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0111100000_0 : Blocks := edgeBlocks% "full/vectors/0111100000-V-0000.bin"
private noncomputable def vp0111100000_1 : Blocks := edgeBlocks% "full/vectors/0111100000-V-0001.bin"
noncomputable def vp0111100000 : Blocks := (Blocks.join vp0111100000_0 vp0111100000_1)
private theorem bp01111000000 : Branch 0 (-3839761639/8000000 : ℚ) vp0111100000 := by
  apply branch_left_normalized (c:=vp01111000000) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-3839761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-3839761639/4000000 : ℚ) by norm_num]
  exact coverp01111000000
private noncomputable def ep01111000001_0 : Blocks := edgeBlocks% "full/vectors/01111000001-E-0000.bin"
private noncomputable def ep01111000001_1 : Blocks := edgeBlocks% "full/vectors/01111000001-E-0001.bin"
noncomputable def ep01111000001 : Blocks := (Blocks.join ep01111000001_0 ep01111000001_1)
private theorem idp01111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111100000.list =
    C ((2:ℤ)^173) * horner X vp01111000001.list + horner X ep01111000001.list := by
  exact edge_identity (B := (2:ℤ)^318) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111000001 : Branch 1 (-3839761639/8000000 : ℚ) vp0111100000 := by
  apply branch_checked idp01111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3839761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-3843761639/4000000 : ℚ) by norm_num]
  exact coverp01111000001
theorem coverp0111100000 : Covers (-3839761639/8000000 : ℚ) vp0111100000 := join_branches bp01111000000 bp01111000001
private noncomputable def vp011110000_0 : Blocks := edgeBlocks% "full/vectors/011110000-V-0000.bin"
private noncomputable def vp011110000_1 : Blocks := edgeBlocks% "full/vectors/011110000-V-0001.bin"
private noncomputable def vp011110000_2 : Blocks := edgeBlocks% "full/vectors/011110000-V-0002.bin"
noncomputable def vp011110000 : Blocks := (Blocks.join vp011110000_0 (Blocks.join vp011110000_1 vp011110000_2))
private theorem bp0111100000 : Branch 0 (-3839761639/16000000 : ℚ) vp011110000 := by
  apply branch_left_normalized (c:=vp0111100000) (k:=0) (m:=149) (by decide +kernel)
  rw [show 2*(-3839761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-3839761639/8000000 : ℚ) by norm_num]
  exact coverp0111100000
private noncomputable def ep0111100001_0 : Blocks := edgeBlocks% "full/vectors/0111100001-E-0000.bin"
private noncomputable def ep0111100001_1 : Blocks := edgeBlocks% "full/vectors/0111100001-E-0001.bin"
private noncomputable def ep0111100001_2 : Blocks := edgeBlocks% "full/vectors/0111100001-E-0002.bin"
noncomputable def ep0111100001 : Blocks := (Blocks.join ep0111100001_0 (Blocks.join ep0111100001_1 ep0111100001_2))
private theorem idp0111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011110000.list =
    C ((2:ℤ)^322) * horner X vp0111100001.list + horner X ep0111100001.list := by
  exact edge_identity (B := (2:ℤ)^511) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111100001 : Branch 1 (-3839761639/16000000 : ℚ) vp011110000 := by
  apply branch_checked idp0111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3839761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-3847761639/8000000 : ℚ) by norm_num]
  exact coverp0111100001
theorem coverp011110000 : Covers (-3839761639/16000000 : ℚ) vp011110000 := join_branches bp0111100000 bp0111100001
private noncomputable def vp01111000_0 : Blocks := edgeBlocks% "full/vectors/01111000-V-0000.bin"
private noncomputable def vp01111000_1 : Blocks := edgeBlocks% "full/vectors/01111000-V-0001.bin"
private noncomputable def vp01111000_2 : Blocks := edgeBlocks% "full/vectors/01111000-V-0002.bin"
private noncomputable def vp01111000_3 : Blocks := edgeBlocks% "full/vectors/01111000-V-0003.bin"
private noncomputable def vp01111000_4 : Blocks := edgeBlocks% "full/vectors/01111000-V-0004.bin"
noncomputable def vp01111000 : Blocks := (Blocks.join (Blocks.join vp01111000_0 vp01111000_1) (Blocks.join vp01111000_2 (Blocks.join vp01111000_3 vp01111000_4)))
private theorem bp011110000 : Branch 0 (-3839761639/32000000 : ℚ) vp01111000 := by
  apply branch_left_normalized (c:=vp011110000) (k:=0) (m:=275) (by decide +kernel)
  rw [show 2*(-3839761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-3839761639/16000000 : ℚ) by norm_num]
  exact coverp011110000
private noncomputable def ep011110001_0 : Blocks := edgeBlocks% "full/vectors/011110001-E-0000.bin"
private noncomputable def ep011110001_1 : Blocks := edgeBlocks% "full/vectors/011110001-E-0001.bin"
private noncomputable def ep011110001_2 : Blocks := edgeBlocks% "full/vectors/011110001-E-0002.bin"
private noncomputable def ep011110001_3 : Blocks := edgeBlocks% "full/vectors/011110001-E-0003.bin"
private noncomputable def ep011110001_4 : Blocks := edgeBlocks% "full/vectors/011110001-E-0004.bin"
noncomputable def ep011110001 : Blocks := (Blocks.join (Blocks.join ep011110001_0 ep011110001_1) (Blocks.join ep011110001_2 (Blocks.join ep011110001_3 ep011110001_4)))
private theorem idp011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01111000.list =
    C ((2:ℤ)^620) * horner X vp011110001.list + horner X ep011110001.list := by
  exact edge_identity (B := (2:ℤ)^898) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp011110001 : Branch 1 (-3839761639/32000000 : ℚ) vp01111000 := by
  apply branch_checked idp011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3839761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-3855761639/16000000 : ℚ) by norm_num]
  exact coverp011110001
theorem coverp01111000 : Covers (-3839761639/32000000 : ℚ) vp01111000 := join_branches bp011110000 bp011110001
private noncomputable def vp0111100_0 : Blocks := edgeBlocks% "full/vectors/0111100-V-0000.bin"
private noncomputable def vp0111100_1 : Blocks := edgeBlocks% "full/vectors/0111100-V-0001.bin"
private noncomputable def vp0111100_2 : Blocks := edgeBlocks% "full/vectors/0111100-V-0002.bin"
private noncomputable def vp0111100_3 : Blocks := edgeBlocks% "full/vectors/0111100-V-0003.bin"
private noncomputable def vp0111100_4 : Blocks := edgeBlocks% "full/vectors/0111100-V-0004.bin"
private noncomputable def vp0111100_5 : Blocks := edgeBlocks% "full/vectors/0111100-V-0005.bin"
private noncomputable def vp0111100_6 : Blocks := edgeBlocks% "full/vectors/0111100-V-0006.bin"
private noncomputable def vp0111100_7 : Blocks := edgeBlocks% "full/vectors/0111100-V-0007.bin"
noncomputable def vp0111100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0111100_0 vp0111100_1) (Blocks.join vp0111100_2 vp0111100_3)) (Blocks.join (Blocks.join vp0111100_4 vp0111100_5) (Blocks.join vp0111100_6 vp0111100_7)))
private theorem bp01111000 : Branch 0 (-3839761639/64000000 : ℚ) vp0111100 := by
  apply branch_left_normalized (c:=vp01111000) (k:=0) (m:=527) (by decide +kernel)
  rw [show 2*(-3839761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-3839761639/32000000 : ℚ) by norm_num]
  exact coverp01111000
private noncomputable def ep01111001_0 : Blocks := edgeBlocks% "full/vectors/01111001-E-0000.bin"
private noncomputable def ep01111001_1 : Blocks := edgeBlocks% "full/vectors/01111001-E-0001.bin"
private noncomputable def ep01111001_2 : Blocks := edgeBlocks% "full/vectors/01111001-E-0002.bin"
private noncomputable def ep01111001_3 : Blocks := edgeBlocks% "full/vectors/01111001-E-0003.bin"
private noncomputable def ep01111001_4 : Blocks := edgeBlocks% "full/vectors/01111001-E-0004.bin"
private noncomputable def ep01111001_5 : Blocks := edgeBlocks% "full/vectors/01111001-E-0005.bin"
private noncomputable def ep01111001_6 : Blocks := edgeBlocks% "full/vectors/01111001-E-0006.bin"
private noncomputable def ep01111001_7 : Blocks := edgeBlocks% "full/vectors/01111001-E-0007.bin"
noncomputable def ep01111001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep01111001_0 ep01111001_1) (Blocks.join ep01111001_2 ep01111001_3)) (Blocks.join (Blocks.join ep01111001_4 ep01111001_5) (Blocks.join ep01111001_6 ep01111001_7)))
private theorem idp01111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0111100.list =
    C ((2:ℤ)^1208) * horner X vp01111001.list + horner X ep01111001.list := by
  exact edge_identity (B := (2:ℤ)^1661) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp01111001 : Branch 1 (-3839761639/64000000 : ℚ) vp0111100 := by
  apply branch_checked idp01111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3839761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-3871761639/32000000 : ℚ) by norm_num]
  exact coverp01111001
theorem coverp0111100 : Covers (-3839761639/64000000 : ℚ) vp0111100 := join_branches bp01111000 bp01111001
private noncomputable def vp011110_0 : Blocks := edgeBlocks% "full/vectors/011110-V-0000.bin"
private noncomputable def vp011110_1 : Blocks := edgeBlocks% "full/vectors/011110-V-0001.bin"
private noncomputable def vp011110_2 : Blocks := edgeBlocks% "full/vectors/011110-V-0002.bin"
private noncomputable def vp011110_3 : Blocks := edgeBlocks% "full/vectors/011110-V-0003.bin"
private noncomputable def vp011110_4 : Blocks := edgeBlocks% "full/vectors/011110-V-0004.bin"
private noncomputable def vp011110_5 : Blocks := edgeBlocks% "full/vectors/011110-V-0005.bin"
private noncomputable def vp011110_6 : Blocks := edgeBlocks% "full/vectors/011110-V-0006.bin"
private noncomputable def vp011110_7 : Blocks := edgeBlocks% "full/vectors/011110-V-0007.bin"
private noncomputable def vp011110_8 : Blocks := edgeBlocks% "full/vectors/011110-V-0008.bin"
private noncomputable def vp011110_9 : Blocks := edgeBlocks% "full/vectors/011110-V-0009.bin"
private noncomputable def vp011110_10 : Blocks := edgeBlocks% "full/vectors/011110-V-0010.bin"
private noncomputable def vp011110_11 : Blocks := edgeBlocks% "full/vectors/011110-V-0011.bin"
private noncomputable def vp011110_12 : Blocks := edgeBlocks% "full/vectors/011110-V-0012.bin"
private noncomputable def vp011110_13 : Blocks := edgeBlocks% "full/vectors/011110-V-0013.bin"
private noncomputable def vp011110_14 : Blocks := edgeBlocks% "full/vectors/011110-V-0014.bin"
private noncomputable def vp011110_15 : Blocks := edgeBlocks% "full/vectors/011110-V-0015.bin"
noncomputable def vp011110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp011110_0 vp011110_1) (Blocks.join vp011110_2 vp011110_3)) (Blocks.join (Blocks.join vp011110_4 vp011110_5) (Blocks.join vp011110_6 vp011110_7))) (Blocks.join (Blocks.join (Blocks.join vp011110_8 vp011110_9) (Blocks.join vp011110_10 vp011110_11)) (Blocks.join (Blocks.join vp011110_12 vp011110_13) (Blocks.join vp011110_14 vp011110_15))))
private theorem bp0111100 : Branch 0 (-3839761639/128000000 : ℚ) vp011110 := by
  apply branch_left_normalized (c:=vp0111100) (k:=0) (m:=1023) (by decide +kernel)
  rw [show 2*(-3839761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-3839761639/64000000 : ℚ) by norm_num]
  exact coverp0111100
private noncomputable def ep0111101_0 : Blocks := edgeBlocks% "full/vectors/0111101-E-0000.bin"
private noncomputable def ep0111101_1 : Blocks := edgeBlocks% "full/vectors/0111101-E-0001.bin"
private noncomputable def ep0111101_2 : Blocks := edgeBlocks% "full/vectors/0111101-E-0002.bin"
private noncomputable def ep0111101_3 : Blocks := edgeBlocks% "full/vectors/0111101-E-0003.bin"
private noncomputable def ep0111101_4 : Blocks := edgeBlocks% "full/vectors/0111101-E-0004.bin"
private noncomputable def ep0111101_5 : Blocks := edgeBlocks% "full/vectors/0111101-E-0005.bin"
private noncomputable def ep0111101_6 : Blocks := edgeBlocks% "full/vectors/0111101-E-0006.bin"
private noncomputable def ep0111101_7 : Blocks := edgeBlocks% "full/vectors/0111101-E-0007.bin"
private noncomputable def ep0111101_8 : Blocks := edgeBlocks% "full/vectors/0111101-E-0008.bin"
private noncomputable def ep0111101_9 : Blocks := edgeBlocks% "full/vectors/0111101-E-0009.bin"
private noncomputable def ep0111101_10 : Blocks := edgeBlocks% "full/vectors/0111101-E-0010.bin"
private noncomputable def ep0111101_11 : Blocks := edgeBlocks% "full/vectors/0111101-E-0011.bin"
private noncomputable def ep0111101_12 : Blocks := edgeBlocks% "full/vectors/0111101-E-0012.bin"
private noncomputable def ep0111101_13 : Blocks := edgeBlocks% "full/vectors/0111101-E-0013.bin"
private noncomputable def ep0111101_14 : Blocks := edgeBlocks% "full/vectors/0111101-E-0014.bin"
private noncomputable def ep0111101_15 : Blocks := edgeBlocks% "full/vectors/0111101-E-0015.bin"
noncomputable def ep0111101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0111101_0 ep0111101_1) (Blocks.join ep0111101_2 ep0111101_3)) (Blocks.join (Blocks.join ep0111101_4 ep0111101_5) (Blocks.join ep0111101_6 ep0111101_7))) (Blocks.join (Blocks.join (Blocks.join ep0111101_8 ep0111101_9) (Blocks.join ep0111101_10 ep0111101_11)) (Blocks.join (Blocks.join ep0111101_12 ep0111101_13) (Blocks.join ep0111101_14 ep0111101_15))))
private theorem idp0111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp011110.list =
    C ((2:ℤ)^2362) * horner X vp0111101.list + horner X ep0111101.list := by
  exact edge_identity (B := (2:ℤ)^3161) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0111101 : Branch 1 (-3839761639/128000000 : ℚ) vp011110 := by
  apply branch_checked idp0111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3839761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-3903761639/64000000 : ℚ) by norm_num]
  exact coverp0111101
theorem coverp011110 : Covers (-3839761639/128000000 : ℚ) vp011110 := join_branches bp0111100 bp0111101
private noncomputable def vp01111_0 : Blocks := edgeBlocks% "full/vectors/01111-V-0000.bin"
private noncomputable def vp01111_1 : Blocks := edgeBlocks% "full/vectors/01111-V-0001.bin"
private noncomputable def vp01111_2 : Blocks := edgeBlocks% "full/vectors/01111-V-0002.bin"
private noncomputable def vp01111_3 : Blocks := edgeBlocks% "full/vectors/01111-V-0003.bin"
private noncomputable def vp01111_4 : Blocks := edgeBlocks% "full/vectors/01111-V-0004.bin"
private noncomputable def vp01111_5 : Blocks := edgeBlocks% "full/vectors/01111-V-0005.bin"
private noncomputable def vp01111_6 : Blocks := edgeBlocks% "full/vectors/01111-V-0006.bin"
private noncomputable def vp01111_7 : Blocks := edgeBlocks% "full/vectors/01111-V-0007.bin"
private noncomputable def vp01111_8 : Blocks := edgeBlocks% "full/vectors/01111-V-0008.bin"
private noncomputable def vp01111_9 : Blocks := edgeBlocks% "full/vectors/01111-V-0009.bin"
private noncomputable def vp01111_10 : Blocks := edgeBlocks% "full/vectors/01111-V-0010.bin"
private noncomputable def vp01111_11 : Blocks := edgeBlocks% "full/vectors/01111-V-0011.bin"
private noncomputable def vp01111_12 : Blocks := edgeBlocks% "full/vectors/01111-V-0012.bin"
private noncomputable def vp01111_13 : Blocks := edgeBlocks% "full/vectors/01111-V-0013.bin"
private noncomputable def vp01111_14 : Blocks := edgeBlocks% "full/vectors/01111-V-0014.bin"
private noncomputable def vp01111_15 : Blocks := edgeBlocks% "full/vectors/01111-V-0015.bin"
private noncomputable def vp01111_16 : Blocks := edgeBlocks% "full/vectors/01111-V-0016.bin"
private noncomputable def vp01111_17 : Blocks := edgeBlocks% "full/vectors/01111-V-0017.bin"
private noncomputable def vp01111_18 : Blocks := edgeBlocks% "full/vectors/01111-V-0018.bin"
private noncomputable def vp01111_19 : Blocks := edgeBlocks% "full/vectors/01111-V-0019.bin"
private noncomputable def vp01111_20 : Blocks := edgeBlocks% "full/vectors/01111-V-0020.bin"
private noncomputable def vp01111_21 : Blocks := edgeBlocks% "full/vectors/01111-V-0021.bin"
private noncomputable def vp01111_22 : Blocks := edgeBlocks% "full/vectors/01111-V-0022.bin"
private noncomputable def vp01111_23 : Blocks := edgeBlocks% "full/vectors/01111-V-0023.bin"
private noncomputable def vp01111_24 : Blocks := edgeBlocks% "full/vectors/01111-V-0024.bin"
private noncomputable def vp01111_25 : Blocks := edgeBlocks% "full/vectors/01111-V-0025.bin"
private noncomputable def vp01111_26 : Blocks := edgeBlocks% "full/vectors/01111-V-0026.bin"
private noncomputable def vp01111_27 : Blocks := edgeBlocks% "full/vectors/01111-V-0027.bin"
private noncomputable def vp01111_28 : Blocks := edgeBlocks% "full/vectors/01111-V-0028.bin"
private noncomputable def vp01111_29 : Blocks := edgeBlocks% "full/vectors/01111-V-0029.bin"
noncomputable def vp01111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp01111_0 (Blocks.join vp01111_1 vp01111_2)) (Blocks.join (Blocks.join vp01111_3 vp01111_4) (Blocks.join vp01111_5 vp01111_6))) (Blocks.join (Blocks.join (Blocks.join vp01111_7 vp01111_8) (Blocks.join vp01111_9 vp01111_10)) (Blocks.join (Blocks.join vp01111_11 vp01111_12) (Blocks.join vp01111_13 vp01111_14)))) (Blocks.join (Blocks.join (Blocks.join vp01111_15 (Blocks.join vp01111_16 vp01111_17)) (Blocks.join (Blocks.join vp01111_18 vp01111_19) (Blocks.join vp01111_20 vp01111_21))) (Blocks.join (Blocks.join (Blocks.join vp01111_22 vp01111_23) (Blocks.join vp01111_24 vp01111_25)) (Blocks.join (Blocks.join vp01111_26 vp01111_27) (Blocks.join vp01111_28 vp01111_29)))))
private theorem bp011110 : Branch 0 (-3839761639/256000000 : ℚ) vp01111 := by
  apply branch_left_normalized (c:=vp011110) (k:=0) (m:=1992) (by decide +kernel)
  rw [show 2*(-3839761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-3839761639/128000000 : ℚ) by norm_num]
  exact coverp011110
private noncomputable def ep011111_0 : Blocks := edgeBlocks% "full/vectors/011111-E-0000.bin"
private noncomputable def ep011111_1 : Blocks := edgeBlocks% "full/vectors/011111-E-0001.bin"
private noncomputable def ep011111_2 : Blocks := edgeBlocks% "full/vectors/011111-E-0002.bin"
private noncomputable def ep011111_3 : Blocks := edgeBlocks% "full/vectors/011111-E-0003.bin"
private noncomputable def ep011111_4 : Blocks := edgeBlocks% "full/vectors/011111-E-0004.bin"
private noncomputable def ep011111_5 : Blocks := edgeBlocks% "full/vectors/011111-E-0005.bin"
private noncomputable def ep011111_6 : Blocks := edgeBlocks% "full/vectors/011111-E-0006.bin"
private noncomputable def ep011111_7 : Blocks := edgeBlocks% "full/vectors/011111-E-0007.bin"
private noncomputable def ep011111_8 : Blocks := edgeBlocks% "full/vectors/011111-E-0008.bin"
private noncomputable def ep011111_9 : Blocks := edgeBlocks% "full/vectors/011111-E-0009.bin"
private noncomputable def ep011111_10 : Blocks := edgeBlocks% "full/vectors/011111-E-0010.bin"
private noncomputable def ep011111_11 : Blocks := edgeBlocks% "full/vectors/011111-E-0011.bin"
private noncomputable def ep011111_12 : Blocks := edgeBlocks% "full/vectors/011111-E-0012.bin"
private noncomputable def ep011111_13 : Blocks := edgeBlocks% "full/vectors/011111-E-0013.bin"
private noncomputable def ep011111_14 : Blocks := edgeBlocks% "full/vectors/011111-E-0014.bin"
private noncomputable def ep011111_15 : Blocks := edgeBlocks% "full/vectors/011111-E-0015.bin"
private noncomputable def ep011111_16 : Blocks := edgeBlocks% "full/vectors/011111-E-0016.bin"
private noncomputable def ep011111_17 : Blocks := edgeBlocks% "full/vectors/011111-E-0017.bin"
private noncomputable def ep011111_18 : Blocks := edgeBlocks% "full/vectors/011111-E-0018.bin"
private noncomputable def ep011111_19 : Blocks := edgeBlocks% "full/vectors/011111-E-0019.bin"
private noncomputable def ep011111_20 : Blocks := edgeBlocks% "full/vectors/011111-E-0020.bin"
private noncomputable def ep011111_21 : Blocks := edgeBlocks% "full/vectors/011111-E-0021.bin"
private noncomputable def ep011111_22 : Blocks := edgeBlocks% "full/vectors/011111-E-0022.bin"
private noncomputable def ep011111_23 : Blocks := edgeBlocks% "full/vectors/011111-E-0023.bin"
private noncomputable def ep011111_24 : Blocks := edgeBlocks% "full/vectors/011111-E-0024.bin"
private noncomputable def ep011111_25 : Blocks := edgeBlocks% "full/vectors/011111-E-0025.bin"
private noncomputable def ep011111_26 : Blocks := edgeBlocks% "full/vectors/011111-E-0026.bin"
private noncomputable def ep011111_27 : Blocks := edgeBlocks% "full/vectors/011111-E-0027.bin"
private noncomputable def ep011111_28 : Blocks := edgeBlocks% "full/vectors/011111-E-0028.bin"
private noncomputable def ep011111_29 : Blocks := edgeBlocks% "full/vectors/011111-E-0029.bin"
noncomputable def ep011111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep011111_0 (Blocks.join ep011111_1 ep011111_2)) (Blocks.join (Blocks.join ep011111_3 ep011111_4) (Blocks.join ep011111_5 ep011111_6))) (Blocks.join (Blocks.join (Blocks.join ep011111_7 ep011111_8) (Blocks.join ep011111_9 ep011111_10)) (Blocks.join (Blocks.join ep011111_11 ep011111_12) (Blocks.join ep011111_13 ep011111_14)))) (Blocks.join (Blocks.join (Blocks.join ep011111_15 (Blocks.join ep011111_16 ep011111_17)) (Blocks.join (Blocks.join ep011111_18 ep011111_19) (Blocks.join ep011111_20 ep011111_21))) (Blocks.join (Blocks.join (Blocks.join ep011111_22 ep011111_23) (Blocks.join ep011111_24 ep011111_25)) (Blocks.join (Blocks.join ep011111_26 ep011111_27) (Blocks.join ep011111_28 ep011111_29)))))
private def ptsp011111 : List ℤ := [((2:ℤ)^3126+0),((2:ℤ)^3126+1)]
private theorem boundp011111 : 2^vp01111.size*absSum vp01111.list + ((2:ℤ)^4579*absSum vp011111.list+absSum ep011111.list) < (2:ℤ)^6048 := by decide +kernel
private theorem pointp011111_0 : fastHom 1 ((2:ℤ)^3126+0) vp01111 = ((2:ℤ)^4579)*vp011111.subst ((2:ℤ)^3126+0)+ep011111.subst ((2:ℤ)^3126+0) := by decide +kernel
private theorem pointp011111_1 : fastHom 1 ((2:ℤ)^3126+1) vp01111 = ((2:ℤ)^4579)*vp011111.subst ((2:ℤ)^3126+1)+ep011111.subst ((2:ℤ)^3126+1) := by decide +kernel
private theorem checkp011111 (x:ℤ) (hx:x ∈ ptsp011111) : fastHom 1 x vp01111 = ((2:ℤ)^4579)*vp011111.subst x+ep011111.subst x := by
  simp only [ptsp011111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp011111_0
  · exact pointp011111_1
private theorem idp011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp01111.list =
    C ((2:ℤ)^4579) * horner X vp011111.list + horner X ep011111.list := by
  apply edge_identity (B := (2:ℤ)^6048) (by decide) (by positivity) (by positivity) boundp011111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp011111 (by decide +kernel)
  · have h : ptsp011111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp011111.trans_le (by decide +kernel)
  · exact checkp011111
private theorem bp011111 : Branch 1 (-3839761639/256000000 : ℚ) vp01111 := by
  apply branch_checked idp011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3839761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-3967761639/128000000 : ℚ) by norm_num]
  exact coverp011111
theorem coverp01111 : Covers (-3839761639/256000000 : ℚ) vp01111 := join_branches bp011110 bp011111
end NextProof.EdgeFull

