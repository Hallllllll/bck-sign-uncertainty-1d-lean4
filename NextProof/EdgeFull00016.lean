import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000000011111111_0 : Blocks := edgeBlocks% "full/vectors/00000000011111111-V-0000.bin"
noncomputable def vp00000000011111111 : Blocks := vp00000000011111111_0
theorem coverp00000000011111111 : Covers (-15699139/62500 : ℚ) vp00000000011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011111110_0 : Blocks := edgeBlocks% "full/vectors/00000000011111110-V-0000.bin"
noncomputable def vp00000000011111110 : Blocks := vp00000000011111110_0
theorem coverp00000000011111110 : Covers (-15636639/62500 : ℚ) vp00000000011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001111111_0 : Blocks := edgeBlocks% "full/vectors/0000000001111111-V-0000.bin"
noncomputable def vp0000000001111111 : Blocks := vp0000000001111111_0
private theorem bp00000000011111110 : Branch 0 (-15636639/125000 : ℚ) vp0000000001111111 := by
  apply branch_left_normalized (c:=vp00000000011111110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-15636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-15636639/62500 : ℚ) by norm_num]
  exact coverp00000000011111110
private noncomputable def ep00000000011111111_0 : Blocks := edgeBlocks% "full/vectors/00000000011111111-E-0000.bin"
noncomputable def ep00000000011111111 : Blocks := ep00000000011111111_0
private theorem idp00000000011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001111111.list =
    C ((2:ℤ)^52) * horner X vp00000000011111111.list + horner X ep00000000011111111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011111111 : Branch 1 (-15636639/125000 : ℚ) vp0000000001111111 := by
  apply branch_checked idp00000000011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-15636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-15699139/62500 : ℚ) by norm_num]
  exact coverp00000000011111111
theorem coverp0000000001111111 : Covers (-15636639/125000 : ℚ) vp0000000001111111 := join_branches bp00000000011111110 bp00000000011111111
private noncomputable def vp00000000011111101_0 : Blocks := edgeBlocks% "full/vectors/00000000011111101-V-0000.bin"
noncomputable def vp00000000011111101 : Blocks := vp00000000011111101_0
theorem coverp00000000011111101 : Covers (-15574139/62500 : ℚ) vp00000000011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111111001_0 : Blocks := edgeBlocks% "full/vectors/000000000111111001-V-0000.bin"
noncomputable def vp000000000111111001 : Blocks := vp000000000111111001_0
theorem coverp000000000111111001 : Covers (-15542889/31250 : ℚ) vp000000000111111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111111000_0 : Blocks := edgeBlocks% "full/vectors/000000000111111000-V-0000.bin"
noncomputable def vp000000000111111000 : Blocks := vp000000000111111000_0
theorem coverp000000000111111000 : Covers (-15511639/31250 : ℚ) vp000000000111111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011111100_0 : Blocks := edgeBlocks% "full/vectors/00000000011111100-V-0000.bin"
noncomputable def vp00000000011111100 : Blocks := vp00000000011111100_0
private theorem bp000000000111111000 : Branch 0 (-15511639/62500 : ℚ) vp00000000011111100 := by
  apply branch_left_normalized (c:=vp000000000111111000) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-15511639/62500 : ℚ) - ((0:ℤ):ℚ) = (-15511639/31250 : ℚ) by norm_num]
  exact coverp000000000111111000
private noncomputable def ep000000000111111001_0 : Blocks := edgeBlocks% "full/vectors/000000000111111001-E-0000.bin"
noncomputable def ep000000000111111001 : Blocks := ep000000000111111001_0
private theorem idp000000000111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011111100.list =
    C ((2:ℤ)^34) * horner X vp000000000111111001.list + horner X ep000000000111111001.list := by
  exact edge_identity (B := (2:ℤ)^147) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111111001 : Branch 1 (-15511639/62500 : ℚ) vp00000000011111100 := by
  apply branch_checked idp000000000111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-15511639/62500 : ℚ) - ((1:ℤ):ℚ) = (-15542889/31250 : ℚ) by norm_num]
  exact coverp000000000111111001
theorem coverp00000000011111100 : Covers (-15511639/62500 : ℚ) vp00000000011111100 := join_branches bp000000000111111000 bp000000000111111001
private noncomputable def vp0000000001111110_0 : Blocks := edgeBlocks% "full/vectors/0000000001111110-V-0000.bin"
noncomputable def vp0000000001111110 : Blocks := vp0000000001111110_0
private theorem bp00000000011111100 : Branch 0 (-15511639/125000 : ℚ) vp0000000001111110 := by
  apply branch_left_normalized (c:=vp00000000011111100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-15511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-15511639/62500 : ℚ) by norm_num]
  exact coverp00000000011111100
private noncomputable def ep00000000011111101_0 : Blocks := edgeBlocks% "full/vectors/00000000011111101-E-0000.bin"
noncomputable def ep00000000011111101 : Blocks := ep00000000011111101_0
private theorem idp00000000011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001111110.list =
    C ((2:ℤ)^52) * horner X vp00000000011111101.list + horner X ep00000000011111101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011111101 : Branch 1 (-15511639/125000 : ℚ) vp0000000001111110 := by
  apply branch_checked idp00000000011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-15511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-15574139/62500 : ℚ) by norm_num]
  exact coverp00000000011111101
theorem coverp0000000001111110 : Covers (-15511639/125000 : ℚ) vp0000000001111110 := join_branches bp00000000011111100 bp00000000011111101
private noncomputable def vp000000000111111_0 : Blocks := edgeBlocks% "full/vectors/000000000111111-V-0000.bin"
noncomputable def vp000000000111111 : Blocks := vp000000000111111_0
private theorem bp0000000001111110 : Branch 0 (-15511639/250000 : ℚ) vp000000000111111 := by
  apply branch_left_normalized (c:=vp0000000001111110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-15511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-15511639/125000 : ℚ) by norm_num]
  exact coverp0000000001111110
private noncomputable def ep0000000001111111_0 : Blocks := edgeBlocks% "full/vectors/0000000001111111-E-0000.bin"
noncomputable def ep0000000001111111 : Blocks := ep0000000001111111_0
private theorem idp0000000001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111111.list =
    C ((2:ℤ)^85) * horner X vp0000000001111111.list + horner X ep0000000001111111.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001111111 : Branch 1 (-15511639/250000 : ℚ) vp000000000111111 := by
  apply branch_checked idp0000000001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-15511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-15636639/125000 : ℚ) by norm_num]
  exact coverp0000000001111111
theorem coverp000000000111111 : Covers (-15511639/250000 : ℚ) vp000000000111111 := join_branches bp0000000001111110 bp0000000001111111
private noncomputable def vp00000000011111011_0 : Blocks := edgeBlocks% "full/vectors/00000000011111011-V-0000.bin"
noncomputable def vp00000000011111011 : Blocks := vp00000000011111011_0
theorem coverp00000000011111011 : Covers (-15449139/62500 : ℚ) vp00000000011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011111010_0 : Blocks := edgeBlocks% "full/vectors/00000000011111010-V-0000.bin"
noncomputable def vp00000000011111010 : Blocks := vp00000000011111010_0
theorem coverp00000000011111010 : Covers (-15386639/62500 : ℚ) vp00000000011111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001111101_0 : Blocks := edgeBlocks% "full/vectors/0000000001111101-V-0000.bin"
noncomputable def vp0000000001111101 : Blocks := vp0000000001111101_0
private theorem bp00000000011111010 : Branch 0 (-15386639/125000 : ℚ) vp0000000001111101 := by
  apply branch_left_normalized (c:=vp00000000011111010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-15386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-15386639/62500 : ℚ) by norm_num]
  exact coverp00000000011111010
private noncomputable def ep00000000011111011_0 : Blocks := edgeBlocks% "full/vectors/00000000011111011-E-0000.bin"
noncomputable def ep00000000011111011 : Blocks := ep00000000011111011_0
private theorem idp00000000011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001111101.list =
    C ((2:ℤ)^52) * horner X vp00000000011111011.list + horner X ep00000000011111011.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011111011 : Branch 1 (-15386639/125000 : ℚ) vp0000000001111101 := by
  apply branch_checked idp00000000011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-15386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-15449139/62500 : ℚ) by norm_num]
  exact coverp00000000011111011
theorem coverp0000000001111101 : Covers (-15386639/125000 : ℚ) vp0000000001111101 := join_branches bp00000000011111010 bp00000000011111011
private noncomputable def vp00000000011111001_0 : Blocks := edgeBlocks% "full/vectors/00000000011111001-V-0000.bin"
noncomputable def vp00000000011111001 : Blocks := vp00000000011111001_0
theorem coverp00000000011111001 : Covers (-15324139/62500 : ℚ) vp00000000011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111110001_0 : Blocks := edgeBlocks% "full/vectors/000000000111110001-V-0000.bin"
noncomputable def vp000000000111110001 : Blocks := vp000000000111110001_0
theorem coverp000000000111110001 : Covers (-15292889/31250 : ℚ) vp000000000111110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111110000_0 : Blocks := edgeBlocks% "full/vectors/000000000111110000-V-0000.bin"
noncomputable def vp000000000111110000 : Blocks := vp000000000111110000_0
theorem coverp000000000111110000 : Covers (-15261639/31250 : ℚ) vp000000000111110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011111000_0 : Blocks := edgeBlocks% "full/vectors/00000000011111000-V-0000.bin"
noncomputable def vp00000000011111000 : Blocks := vp00000000011111000_0
private theorem bp000000000111110000 : Branch 0 (-15261639/62500 : ℚ) vp00000000011111000 := by
  apply branch_left_normalized (c:=vp000000000111110000) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-15261639/62500 : ℚ) - ((0:ℤ):ℚ) = (-15261639/31250 : ℚ) by norm_num]
  exact coverp000000000111110000
private noncomputable def ep000000000111110001_0 : Blocks := edgeBlocks% "full/vectors/000000000111110001-E-0000.bin"
noncomputable def ep000000000111110001 : Blocks := ep000000000111110001_0
private theorem idp000000000111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011111000.list =
    C ((2:ℤ)^35) * horner X vp000000000111110001.list + horner X ep000000000111110001.list := by
  exact edge_identity (B := (2:ℤ)^148) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111110001 : Branch 1 (-15261639/62500 : ℚ) vp00000000011111000 := by
  apply branch_checked idp000000000111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-15261639/62500 : ℚ) - ((1:ℤ):ℚ) = (-15292889/31250 : ℚ) by norm_num]
  exact coverp000000000111110001
theorem coverp00000000011111000 : Covers (-15261639/62500 : ℚ) vp00000000011111000 := join_branches bp000000000111110000 bp000000000111110001
private noncomputable def vp0000000001111100_0 : Blocks := edgeBlocks% "full/vectors/0000000001111100-V-0000.bin"
noncomputable def vp0000000001111100 : Blocks := vp0000000001111100_0
private theorem bp00000000011111000 : Branch 0 (-15261639/125000 : ℚ) vp0000000001111100 := by
  apply branch_left_normalized (c:=vp00000000011111000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-15261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-15261639/62500 : ℚ) by norm_num]
  exact coverp00000000011111000
private noncomputable def ep00000000011111001_0 : Blocks := edgeBlocks% "full/vectors/00000000011111001-E-0000.bin"
noncomputable def ep00000000011111001 : Blocks := ep00000000011111001_0
private theorem idp00000000011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001111100.list =
    C ((2:ℤ)^53) * horner X vp00000000011111001.list + horner X ep00000000011111001.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011111001 : Branch 1 (-15261639/125000 : ℚ) vp0000000001111100 := by
  apply branch_checked idp00000000011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-15261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-15324139/62500 : ℚ) by norm_num]
  exact coverp00000000011111001
theorem coverp0000000001111100 : Covers (-15261639/125000 : ℚ) vp0000000001111100 := join_branches bp00000000011111000 bp00000000011111001
private noncomputable def vp000000000111110_0 : Blocks := edgeBlocks% "full/vectors/000000000111110-V-0000.bin"
noncomputable def vp000000000111110 : Blocks := vp000000000111110_0
private theorem bp0000000001111100 : Branch 0 (-15261639/250000 : ℚ) vp000000000111110 := by
  apply branch_left_normalized (c:=vp0000000001111100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-15261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-15261639/125000 : ℚ) by norm_num]
  exact coverp0000000001111100
private noncomputable def ep0000000001111101_0 : Blocks := edgeBlocks% "full/vectors/0000000001111101-E-0000.bin"
noncomputable def ep0000000001111101 : Blocks := ep0000000001111101_0
private theorem idp0000000001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111110.list =
    C ((2:ℤ)^85) * horner X vp0000000001111101.list + horner X ep0000000001111101.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001111101 : Branch 1 (-15261639/250000 : ℚ) vp000000000111110 := by
  apply branch_checked idp0000000001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-15261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-15386639/125000 : ℚ) by norm_num]
  exact coverp0000000001111101
theorem coverp000000000111110 : Covers (-15261639/250000 : ℚ) vp000000000111110 := join_branches bp0000000001111100 bp0000000001111101
private noncomputable def vp00000000011111_0 : Blocks := edgeBlocks% "full/vectors/00000000011111-V-0000.bin"
private noncomputable def vp00000000011111_1 : Blocks := edgeBlocks% "full/vectors/00000000011111-V-0001.bin"
noncomputable def vp00000000011111 : Blocks := (Blocks.join vp00000000011111_0 vp00000000011111_1)
private theorem bp000000000111110 : Branch 0 (-15261639/500000 : ℚ) vp00000000011111 := by
  apply branch_left_normalized (c:=vp000000000111110) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-15261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-15261639/250000 : ℚ) by norm_num]
  exact coverp000000000111110
private noncomputable def ep000000000111111_0 : Blocks := edgeBlocks% "full/vectors/000000000111111-E-0000.bin"
private noncomputable def ep000000000111111_1 : Blocks := edgeBlocks% "full/vectors/000000000111111-E-0001.bin"
noncomputable def ep000000000111111 : Blocks := (Blocks.join ep000000000111111_0 ep000000000111111_1)
private theorem idp000000000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011111.list =
    C ((2:ℤ)^151) * horner X vp000000000111111.list + horner X ep000000000111111.list := by
  exact edge_identity (B := (2:ℤ)^319) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111111 : Branch 1 (-15261639/500000 : ℚ) vp00000000011111 := by
  apply branch_checked idp000000000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-15261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-15511639/250000 : ℚ) by norm_num]
  exact coverp000000000111111
theorem coverp00000000011111 : Covers (-15261639/500000 : ℚ) vp00000000011111 := join_branches bp000000000111110 bp000000000111111
private noncomputable def vp000000000111101111_0 : Blocks := edgeBlocks% "full/vectors/000000000111101111-V-0000.bin"
noncomputable def vp000000000111101111 : Blocks := vp000000000111101111_0
theorem coverp000000000111101111 : Covers (-15230389/31250 : ℚ) vp000000000111101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111101110_0 : Blocks := edgeBlocks% "full/vectors/000000000111101110-V-0000.bin"
noncomputable def vp000000000111101110 : Blocks := vp000000000111101110_0
theorem coverp000000000111101110 : Covers (-15199139/31250 : ℚ) vp000000000111101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011110111_0 : Blocks := edgeBlocks% "full/vectors/00000000011110111-V-0000.bin"
noncomputable def vp00000000011110111 : Blocks := vp00000000011110111_0
private theorem bp000000000111101110 : Branch 0 (-15199139/62500 : ℚ) vp00000000011110111 := by
  apply branch_left_normalized (c:=vp000000000111101110) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-15199139/62500 : ℚ) - ((0:ℤ):ℚ) = (-15199139/31250 : ℚ) by norm_num]
  exact coverp000000000111101110
private noncomputable def ep000000000111101111_0 : Blocks := edgeBlocks% "full/vectors/000000000111101111-E-0000.bin"
noncomputable def ep000000000111101111 : Blocks := ep000000000111101111_0
private theorem idp000000000111101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011110111.list =
    C ((2:ℤ)^35) * horner X vp000000000111101111.list + horner X ep000000000111101111.list := by
  exact edge_identity (B := (2:ℤ)^148) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111101111 : Branch 1 (-15199139/62500 : ℚ) vp00000000011110111 := by
  apply branch_checked idp000000000111101111 (by positivity) (by decide +kernel)
  rw [show 2*(-15199139/62500 : ℚ) - ((1:ℤ):ℚ) = (-15230389/31250 : ℚ) by norm_num]
  exact coverp000000000111101111
theorem coverp00000000011110111 : Covers (-15199139/62500 : ℚ) vp00000000011110111 := join_branches bp000000000111101110 bp000000000111101111
private noncomputable def vp00000000011110110_0 : Blocks := edgeBlocks% "full/vectors/00000000011110110-V-0000.bin"
noncomputable def vp00000000011110110 : Blocks := vp00000000011110110_0
theorem coverp00000000011110110 : Covers (-15136639/62500 : ℚ) vp00000000011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001111011_0 : Blocks := edgeBlocks% "full/vectors/0000000001111011-V-0000.bin"
noncomputable def vp0000000001111011 : Blocks := vp0000000001111011_0
private theorem bp00000000011110110 : Branch 0 (-15136639/125000 : ℚ) vp0000000001111011 := by
  apply branch_left_normalized (c:=vp00000000011110110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-15136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-15136639/62500 : ℚ) by norm_num]
  exact coverp00000000011110110
private noncomputable def ep00000000011110111_0 : Blocks := edgeBlocks% "full/vectors/00000000011110111-E-0000.bin"
noncomputable def ep00000000011110111 : Blocks := ep00000000011110111_0
private theorem idp00000000011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001111011.list =
    C ((2:ℤ)^52) * horner X vp00000000011110111.list + horner X ep00000000011110111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011110111 : Branch 1 (-15136639/125000 : ℚ) vp0000000001111011 := by
  apply branch_checked idp00000000011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-15136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-15199139/62500 : ℚ) by norm_num]
  exact coverp00000000011110111
theorem coverp0000000001111011 : Covers (-15136639/125000 : ℚ) vp0000000001111011 := join_branches bp00000000011110110 bp00000000011110111
private noncomputable def vp00000000011110101_0 : Blocks := edgeBlocks% "full/vectors/00000000011110101-V-0000.bin"
noncomputable def vp00000000011110101 : Blocks := vp00000000011110101_0
theorem coverp00000000011110101 : Covers (-15074139/62500 : ℚ) vp00000000011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011110100_0 : Blocks := edgeBlocks% "full/vectors/00000000011110100-V-0000.bin"
noncomputable def vp00000000011110100 : Blocks := vp00000000011110100_0
theorem coverp00000000011110100 : Covers (-15011639/62500 : ℚ) vp00000000011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001111010_0 : Blocks := edgeBlocks% "full/vectors/0000000001111010-V-0000.bin"
noncomputable def vp0000000001111010 : Blocks := vp0000000001111010_0
private theorem bp00000000011110100 : Branch 0 (-15011639/125000 : ℚ) vp0000000001111010 := by
  apply branch_left_normalized (c:=vp00000000011110100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-15011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-15011639/62500 : ℚ) by norm_num]
  exact coverp00000000011110100
private noncomputable def ep00000000011110101_0 : Blocks := edgeBlocks% "full/vectors/00000000011110101-E-0000.bin"
noncomputable def ep00000000011110101 : Blocks := ep00000000011110101_0
private theorem idp00000000011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001111010.list =
    C ((2:ℤ)^53) * horner X vp00000000011110101.list + horner X ep00000000011110101.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011110101 : Branch 1 (-15011639/125000 : ℚ) vp0000000001111010 := by
  apply branch_checked idp00000000011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-15011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-15074139/62500 : ℚ) by norm_num]
  exact coverp00000000011110101
theorem coverp0000000001111010 : Covers (-15011639/125000 : ℚ) vp0000000001111010 := join_branches bp00000000011110100 bp00000000011110101
private noncomputable def vp000000000111101_0 : Blocks := edgeBlocks% "full/vectors/000000000111101-V-0000.bin"
noncomputable def vp000000000111101 : Blocks := vp000000000111101_0
private theorem bp0000000001111010 : Branch 0 (-15011639/250000 : ℚ) vp000000000111101 := by
  apply branch_left_normalized (c:=vp0000000001111010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-15011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-15011639/125000 : ℚ) by norm_num]
  exact coverp0000000001111010
private noncomputable def ep0000000001111011_0 : Blocks := edgeBlocks% "full/vectors/0000000001111011-E-0000.bin"
noncomputable def ep0000000001111011 : Blocks := ep0000000001111011_0
private theorem idp0000000001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111101.list =
    C ((2:ℤ)^87) * horner X vp0000000001111011.list + horner X ep0000000001111011.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001111011 : Branch 1 (-15011639/250000 : ℚ) vp000000000111101 := by
  apply branch_checked idp0000000001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-15011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-15136639/125000 : ℚ) by norm_num]
  exact coverp0000000001111011
theorem coverp000000000111101 : Covers (-15011639/250000 : ℚ) vp000000000111101 := join_branches bp0000000001111010 bp0000000001111011
private noncomputable def vp000000000111100111_0 : Blocks := edgeBlocks% "full/vectors/000000000111100111-V-0000.bin"
noncomputable def vp000000000111100111 : Blocks := vp000000000111100111_0
theorem coverp000000000111100111 : Covers (-14980389/31250 : ℚ) vp000000000111100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111100110_0 : Blocks := edgeBlocks% "full/vectors/000000000111100110-V-0000.bin"
noncomputable def vp000000000111100110 : Blocks := vp000000000111100110_0
theorem coverp000000000111100110 : Covers (-14949139/31250 : ℚ) vp000000000111100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011110011_0 : Blocks := edgeBlocks% "full/vectors/00000000011110011-V-0000.bin"
noncomputable def vp00000000011110011 : Blocks := vp00000000011110011_0
private theorem bp000000000111100110 : Branch 0 (-14949139/62500 : ℚ) vp00000000011110011 := by
  apply branch_left_normalized (c:=vp000000000111100110) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-14949139/62500 : ℚ) - ((0:ℤ):ℚ) = (-14949139/31250 : ℚ) by norm_num]
  exact coverp000000000111100110
private noncomputable def ep000000000111100111_0 : Blocks := edgeBlocks% "full/vectors/000000000111100111-E-0000.bin"
noncomputable def ep000000000111100111 : Blocks := ep000000000111100111_0
private theorem idp000000000111100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011110011.list =
    C ((2:ℤ)^36) * horner X vp000000000111100111.list + horner X ep000000000111100111.list := by
  exact edge_identity (B := (2:ℤ)^150) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111100111 : Branch 1 (-14949139/62500 : ℚ) vp00000000011110011 := by
  apply branch_checked idp000000000111100111 (by positivity) (by decide +kernel)
  rw [show 2*(-14949139/62500 : ℚ) - ((1:ℤ):ℚ) = (-14980389/31250 : ℚ) by norm_num]
  exact coverp000000000111100111
theorem coverp00000000011110011 : Covers (-14949139/62500 : ℚ) vp00000000011110011 := join_branches bp000000000111100110 bp000000000111100111
private noncomputable def vp000000000111100101_0 : Blocks := edgeBlocks% "full/vectors/000000000111100101-V-0000.bin"
noncomputable def vp000000000111100101 : Blocks := vp000000000111100101_0
theorem coverp000000000111100101 : Covers (-14917889/31250 : ℚ) vp000000000111100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111100100_0 : Blocks := edgeBlocks% "full/vectors/000000000111100100-V-0000.bin"
noncomputable def vp000000000111100100 : Blocks := vp000000000111100100_0
theorem coverp000000000111100100 : Covers (-14886639/31250 : ℚ) vp000000000111100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011110010_0 : Blocks := edgeBlocks% "full/vectors/00000000011110010-V-0000.bin"
noncomputable def vp00000000011110010 : Blocks := vp00000000011110010_0
private theorem bp000000000111100100 : Branch 0 (-14886639/62500 : ℚ) vp00000000011110010 := by
  apply branch_left_normalized (c:=vp000000000111100100) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-14886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-14886639/31250 : ℚ) by norm_num]
  exact coverp000000000111100100
private noncomputable def ep000000000111100101_0 : Blocks := edgeBlocks% "full/vectors/000000000111100101-E-0000.bin"
noncomputable def ep000000000111100101 : Blocks := ep000000000111100101_0
private theorem idp000000000111100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011110010.list =
    C ((2:ℤ)^36) * horner X vp000000000111100101.list + horner X ep000000000111100101.list := by
  exact edge_identity (B := (2:ℤ)^150) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111100101 : Branch 1 (-14886639/62500 : ℚ) vp00000000011110010 := by
  apply branch_checked idp000000000111100101 (by positivity) (by decide +kernel)
  rw [show 2*(-14886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-14917889/31250 : ℚ) by norm_num]
  exact coverp000000000111100101
theorem coverp00000000011110010 : Covers (-14886639/62500 : ℚ) vp00000000011110010 := join_branches bp000000000111100100 bp000000000111100101
private noncomputable def vp0000000001111001_0 : Blocks := edgeBlocks% "full/vectors/0000000001111001-V-0000.bin"
noncomputable def vp0000000001111001 : Blocks := vp0000000001111001_0
private theorem bp00000000011110010 : Branch 0 (-14886639/125000 : ℚ) vp0000000001111001 := by
  apply branch_left_normalized (c:=vp00000000011110010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-14886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-14886639/62500 : ℚ) by norm_num]
  exact coverp00000000011110010
private noncomputable def ep00000000011110011_0 : Blocks := edgeBlocks% "full/vectors/00000000011110011-E-0000.bin"
noncomputable def ep00000000011110011 : Blocks := ep00000000011110011_0
private theorem idp00000000011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001111001.list =
    C ((2:ℤ)^53) * horner X vp00000000011110011.list + horner X ep00000000011110011.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011110011 : Branch 1 (-14886639/125000 : ℚ) vp0000000001111001 := by
  apply branch_checked idp00000000011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-14886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-14949139/62500 : ℚ) by norm_num]
  exact coverp00000000011110011
theorem coverp0000000001111001 : Covers (-14886639/125000 : ℚ) vp0000000001111001 := join_branches bp00000000011110010 bp00000000011110011
private noncomputable def vp000000000111100011_0 : Blocks := edgeBlocks% "full/vectors/000000000111100011-V-0000.bin"
noncomputable def vp000000000111100011 : Blocks := vp000000000111100011_0
theorem coverp000000000111100011 : Covers (-14855389/31250 : ℚ) vp000000000111100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111100010_0 : Blocks := edgeBlocks% "full/vectors/000000000111100010-V-0000.bin"
noncomputable def vp000000000111100010 : Blocks := vp000000000111100010_0
theorem coverp000000000111100010 : Covers (-14824139/31250 : ℚ) vp000000000111100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011110001_0 : Blocks := edgeBlocks% "full/vectors/00000000011110001-V-0000.bin"
noncomputable def vp00000000011110001 : Blocks := vp00000000011110001_0
private theorem bp000000000111100010 : Branch 0 (-14824139/62500 : ℚ) vp00000000011110001 := by
  apply branch_left_normalized (c:=vp000000000111100010) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-14824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-14824139/31250 : ℚ) by norm_num]
  exact coverp000000000111100010
private noncomputable def ep000000000111100011_0 : Blocks := edgeBlocks% "full/vectors/000000000111100011-E-0000.bin"
noncomputable def ep000000000111100011 : Blocks := ep000000000111100011_0
private theorem idp000000000111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011110001.list =
    C ((2:ℤ)^34) * horner X vp000000000111100011.list + horner X ep000000000111100011.list := by
  exact edge_identity (B := (2:ℤ)^148) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111100011 : Branch 1 (-14824139/62500 : ℚ) vp00000000011110001 := by
  apply branch_checked idp000000000111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-14824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-14855389/31250 : ℚ) by norm_num]
  exact coverp000000000111100011
theorem coverp00000000011110001 : Covers (-14824139/62500 : ℚ) vp00000000011110001 := join_branches bp000000000111100010 bp000000000111100011
private noncomputable def vp000000000111100001_0 : Blocks := edgeBlocks% "full/vectors/000000000111100001-V-0000.bin"
noncomputable def vp000000000111100001 : Blocks := vp000000000111100001_0
theorem coverp000000000111100001 : Covers (-14792889/31250 : ℚ) vp000000000111100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001111000001_0 : Blocks := edgeBlocks% "full/vectors/0000000001111000001-V-0000.bin"
noncomputable def vp0000000001111000001 : Blocks := vp0000000001111000001_0
theorem coverp0000000001111000001 : Covers (-14777264/15625 : ℚ) vp0000000001111000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001111000000_0 : Blocks := edgeBlocks% "full/vectors/0000000001111000000-V-0000.bin"
noncomputable def vp0000000001111000000 : Blocks := vp0000000001111000000_0
theorem coverp0000000001111000000 : Covers (-14761639/15625 : ℚ) vp0000000001111000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111100000_0 : Blocks := edgeBlocks% "full/vectors/000000000111100000-V-0000.bin"
noncomputable def vp000000000111100000 : Blocks := vp000000000111100000_0
private theorem bp0000000001111000000 : Branch 0 (-14761639/31250 : ℚ) vp000000000111100000 := by
  apply branch_left_normalized (c:=vp0000000001111000000) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-14761639/31250 : ℚ) - ((0:ℤ):ℚ) = (-14761639/15625 : ℚ) by norm_num]
  exact coverp0000000001111000000
private noncomputable def ep0000000001111000001_0 : Blocks := edgeBlocks% "full/vectors/0000000001111000001-E-0000.bin"
noncomputable def ep0000000001111000001 : Blocks := ep0000000001111000001_0
private theorem idp0000000001111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111100000.list =
    C ((2:ℤ)^24) * horner X vp0000000001111000001.list + horner X ep0000000001111000001.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001111000001 : Branch 1 (-14761639/31250 : ℚ) vp000000000111100000 := by
  apply branch_checked idp0000000001111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-14761639/31250 : ℚ) - ((1:ℤ):ℚ) = (-14777264/15625 : ℚ) by norm_num]
  exact coverp0000000001111000001
theorem coverp000000000111100000 : Covers (-14761639/31250 : ℚ) vp000000000111100000 := join_branches bp0000000001111000000 bp0000000001111000001
private noncomputable def vp00000000011110000_0 : Blocks := edgeBlocks% "full/vectors/00000000011110000-V-0000.bin"
noncomputable def vp00000000011110000 : Blocks := vp00000000011110000_0
private theorem bp000000000111100000 : Branch 0 (-14761639/62500 : ℚ) vp00000000011110000 := by
  apply branch_left_normalized (c:=vp000000000111100000) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-14761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-14761639/31250 : ℚ) by norm_num]
  exact coverp000000000111100000
private noncomputable def ep000000000111100001_0 : Blocks := edgeBlocks% "full/vectors/000000000111100001-E-0000.bin"
noncomputable def ep000000000111100001 : Blocks := ep000000000111100001_0
private theorem idp000000000111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011110000.list =
    C ((2:ℤ)^34) * horner X vp000000000111100001.list + horner X ep000000000111100001.list := by
  exact edge_identity (B := (2:ℤ)^149) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111100001 : Branch 1 (-14761639/62500 : ℚ) vp00000000011110000 := by
  apply branch_checked idp000000000111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-14761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-14792889/31250 : ℚ) by norm_num]
  exact coverp000000000111100001
theorem coverp00000000011110000 : Covers (-14761639/62500 : ℚ) vp00000000011110000 := join_branches bp000000000111100000 bp000000000111100001
private noncomputable def vp0000000001111000_0 : Blocks := edgeBlocks% "full/vectors/0000000001111000-V-0000.bin"
noncomputable def vp0000000001111000 : Blocks := vp0000000001111000_0
private theorem bp00000000011110000 : Branch 0 (-14761639/125000 : ℚ) vp0000000001111000 := by
  apply branch_left_normalized (c:=vp00000000011110000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-14761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-14761639/62500 : ℚ) by norm_num]
  exact coverp00000000011110000
private noncomputable def ep00000000011110001_0 : Blocks := edgeBlocks% "full/vectors/00000000011110001-E-0000.bin"
noncomputable def ep00000000011110001 : Blocks := ep00000000011110001_0
private theorem idp00000000011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001111000.list =
    C ((2:ℤ)^54) * horner X vp00000000011110001.list + horner X ep00000000011110001.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011110001 : Branch 1 (-14761639/125000 : ℚ) vp0000000001111000 := by
  apply branch_checked idp00000000011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-14761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-14824139/62500 : ℚ) by norm_num]
  exact coverp00000000011110001
theorem coverp0000000001111000 : Covers (-14761639/125000 : ℚ) vp0000000001111000 := join_branches bp00000000011110000 bp00000000011110001
private noncomputable def vp000000000111100_0 : Blocks := edgeBlocks% "full/vectors/000000000111100-V-0000.bin"
noncomputable def vp000000000111100 : Blocks := vp000000000111100_0
private theorem bp0000000001111000 : Branch 0 (-14761639/250000 : ℚ) vp000000000111100 := by
  apply branch_left_normalized (c:=vp0000000001111000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-14761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-14761639/125000 : ℚ) by norm_num]
  exact coverp0000000001111000
private noncomputable def ep0000000001111001_0 : Blocks := edgeBlocks% "full/vectors/0000000001111001-E-0000.bin"
noncomputable def ep0000000001111001 : Blocks := ep0000000001111001_0
private theorem idp0000000001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111100.list =
    C ((2:ℤ)^87) * horner X vp0000000001111001.list + horner X ep0000000001111001.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001111001 : Branch 1 (-14761639/250000 : ℚ) vp000000000111100 := by
  apply branch_checked idp0000000001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-14761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-14886639/125000 : ℚ) by norm_num]
  exact coverp0000000001111001
theorem coverp000000000111100 : Covers (-14761639/250000 : ℚ) vp000000000111100 := join_branches bp0000000001111000 bp0000000001111001
private noncomputable def vp00000000011110_0 : Blocks := edgeBlocks% "full/vectors/00000000011110-V-0000.bin"
private noncomputable def vp00000000011110_1 : Blocks := edgeBlocks% "full/vectors/00000000011110-V-0001.bin"
noncomputable def vp00000000011110 : Blocks := (Blocks.join vp00000000011110_0 vp00000000011110_1)
private theorem bp000000000111100 : Branch 0 (-14761639/500000 : ℚ) vp00000000011110 := by
  apply branch_left_normalized (c:=vp000000000111100) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-14761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-14761639/250000 : ℚ) by norm_num]
  exact coverp000000000111100
private noncomputable def ep000000000111101_0 : Blocks := edgeBlocks% "full/vectors/000000000111101-E-0000.bin"
private noncomputable def ep000000000111101_1 : Blocks := edgeBlocks% "full/vectors/000000000111101-E-0001.bin"
noncomputable def ep000000000111101 : Blocks := (Blocks.join ep000000000111101_0 ep000000000111101_1)
private theorem idp000000000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011110.list =
    C ((2:ℤ)^152) * horner X vp000000000111101.list + horner X ep000000000111101.list := by
  exact edge_identity (B := (2:ℤ)^322) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111101 : Branch 1 (-14761639/500000 : ℚ) vp00000000011110 := by
  apply branch_checked idp000000000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-14761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-15011639/250000 : ℚ) by norm_num]
  exact coverp000000000111101
theorem coverp00000000011110 : Covers (-14761639/500000 : ℚ) vp00000000011110 := join_branches bp000000000111100 bp000000000111101
private noncomputable def vp0000000001111_0 : Blocks := edgeBlocks% "full/vectors/0000000001111-V-0000.bin"
private noncomputable def vp0000000001111_1 : Blocks := edgeBlocks% "full/vectors/0000000001111-V-0001.bin"
private noncomputable def vp0000000001111_2 : Blocks := edgeBlocks% "full/vectors/0000000001111-V-0002.bin"
noncomputable def vp0000000001111 : Blocks := (Blocks.join vp0000000001111_0 (Blocks.join vp0000000001111_1 vp0000000001111_2))
private theorem bp00000000011110 : Branch 0 (-14761639/1000000 : ℚ) vp0000000001111 := by
  apply branch_left_normalized (c:=vp00000000011110) (k:=0) (m:=150) (by decide +kernel)
  rw [show 2*(-14761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-14761639/500000 : ℚ) by norm_num]
  exact coverp00000000011110
private noncomputable def ep00000000011111_0 : Blocks := edgeBlocks% "full/vectors/00000000011111-E-0000.bin"
private noncomputable def ep00000000011111_1 : Blocks := edgeBlocks% "full/vectors/00000000011111-E-0001.bin"
private noncomputable def ep00000000011111_2 : Blocks := edgeBlocks% "full/vectors/00000000011111-E-0002.bin"
noncomputable def ep00000000011111 : Blocks := (Blocks.join ep00000000011111_0 (Blocks.join ep00000000011111_1 ep00000000011111_2))
private theorem idp00000000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001111.list =
    C ((2:ℤ)^281) * horner X vp00000000011111.list + horner X ep00000000011111.list := by
  exact edge_identity (B := (2:ℤ)^517) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011111 : Branch 1 (-14761639/1000000 : ℚ) vp0000000001111 := by
  apply branch_checked idp00000000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-14761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-15261639/500000 : ℚ) by norm_num]
  exact coverp00000000011111
theorem coverp0000000001111 : Covers (-14761639/1000000 : ℚ) vp0000000001111 := join_branches bp00000000011110 bp00000000011111
private noncomputable def vp0000000001110111111_0 : Blocks := edgeBlocks% "full/vectors/0000000001110111111-V-0000.bin"
noncomputable def vp0000000001110111111 : Blocks := vp0000000001110111111_0
theorem coverp0000000001110111111 : Covers (-14746014/15625 : ℚ) vp0000000001110111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001110111110_0 : Blocks := edgeBlocks% "full/vectors/0000000001110111110-V-0000.bin"
noncomputable def vp0000000001110111110 : Blocks := vp0000000001110111110_0
theorem coverp0000000001110111110 : Covers (-14730389/15625 : ℚ) vp0000000001110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111011111_0 : Blocks := edgeBlocks% "full/vectors/000000000111011111-V-0000.bin"
noncomputable def vp000000000111011111 : Blocks := vp000000000111011111_0
private theorem bp0000000001110111110 : Branch 0 (-14730389/31250 : ℚ) vp000000000111011111 := by
  apply branch_left_normalized (c:=vp0000000001110111110) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-14730389/31250 : ℚ) - ((0:ℤ):ℚ) = (-14730389/15625 : ℚ) by norm_num]
  exact coverp0000000001110111110
private noncomputable def ep0000000001110111111_0 : Blocks := edgeBlocks% "full/vectors/0000000001110111111-E-0000.bin"
noncomputable def ep0000000001110111111 : Blocks := ep0000000001110111111_0
private theorem idp0000000001110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111011111.list =
    C ((2:ℤ)^24) * horner X vp0000000001110111111.list + horner X ep0000000001110111111.list := by
  exact edge_identity (B := (2:ℤ)^133) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001110111111 : Branch 1 (-14730389/31250 : ℚ) vp000000000111011111 := by
  apply branch_checked idp0000000001110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-14730389/31250 : ℚ) - ((1:ℤ):ℚ) = (-14746014/15625 : ℚ) by norm_num]
  exact coverp0000000001110111111
theorem coverp000000000111011111 : Covers (-14730389/31250 : ℚ) vp000000000111011111 := join_branches bp0000000001110111110 bp0000000001110111111
private noncomputable def vp000000000111011110_0 : Blocks := edgeBlocks% "full/vectors/000000000111011110-V-0000.bin"
noncomputable def vp000000000111011110 : Blocks := vp000000000111011110_0
theorem coverp000000000111011110 : Covers (-14699139/31250 : ℚ) vp000000000111011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011101111_0 : Blocks := edgeBlocks% "full/vectors/00000000011101111-V-0000.bin"
noncomputable def vp00000000011101111 : Blocks := vp00000000011101111_0
private theorem bp000000000111011110 : Branch 0 (-14699139/62500 : ℚ) vp00000000011101111 := by
  apply branch_left_normalized (c:=vp000000000111011110) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-14699139/62500 : ℚ) - ((0:ℤ):ℚ) = (-14699139/31250 : ℚ) by norm_num]
  exact coverp000000000111011110
private noncomputable def ep000000000111011111_0 : Blocks := edgeBlocks% "full/vectors/000000000111011111-E-0000.bin"
noncomputable def ep000000000111011111 : Blocks := ep000000000111011111_0
private theorem idp000000000111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011101111.list =
    C ((2:ℤ)^34) * horner X vp000000000111011111.list + horner X ep000000000111011111.list := by
  exact edge_identity (B := (2:ℤ)^145) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111011111 : Branch 1 (-14699139/62500 : ℚ) vp00000000011101111 := by
  apply branch_checked idp000000000111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-14699139/62500 : ℚ) - ((1:ℤ):ℚ) = (-14730389/31250 : ℚ) by norm_num]
  exact coverp000000000111011111
theorem coverp00000000011101111 : Covers (-14699139/62500 : ℚ) vp00000000011101111 := join_branches bp000000000111011110 bp000000000111011111
private noncomputable def vp00000000011101110_0 : Blocks := edgeBlocks% "full/vectors/00000000011101110-V-0000.bin"
noncomputable def vp00000000011101110 : Blocks := vp00000000011101110_0
theorem coverp00000000011101110 : Covers (-14636639/62500 : ℚ) vp00000000011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001110111_0 : Blocks := edgeBlocks% "full/vectors/0000000001110111-V-0000.bin"
noncomputable def vp0000000001110111 : Blocks := vp0000000001110111_0
private theorem bp00000000011101110 : Branch 0 (-14636639/125000 : ℚ) vp0000000001110111 := by
  apply branch_left_normalized (c:=vp00000000011101110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-14636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-14636639/62500 : ℚ) by norm_num]
  exact coverp00000000011101110
private noncomputable def ep00000000011101111_0 : Blocks := edgeBlocks% "full/vectors/00000000011101111-E-0000.bin"
noncomputable def ep00000000011101111 : Blocks := ep00000000011101111_0
private theorem idp00000000011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001110111.list =
    C ((2:ℤ)^53) * horner X vp00000000011101111.list + horner X ep00000000011101111.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011101111 : Branch 1 (-14636639/125000 : ℚ) vp0000000001110111 := by
  apply branch_checked idp00000000011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-14636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-14699139/62500 : ℚ) by norm_num]
  exact coverp00000000011101111
theorem coverp0000000001110111 : Covers (-14636639/125000 : ℚ) vp0000000001110111 := join_branches bp00000000011101110 bp00000000011101111
private noncomputable def vp000000000111011011_0 : Blocks := edgeBlocks% "full/vectors/000000000111011011-V-0000.bin"
noncomputable def vp000000000111011011 : Blocks := vp000000000111011011_0
theorem coverp000000000111011011 : Covers (-14605389/31250 : ℚ) vp000000000111011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111011010_0 : Blocks := edgeBlocks% "full/vectors/000000000111011010-V-0000.bin"
noncomputable def vp000000000111011010 : Blocks := vp000000000111011010_0
theorem coverp000000000111011010 : Covers (-14574139/31250 : ℚ) vp000000000111011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011101101_0 : Blocks := edgeBlocks% "full/vectors/00000000011101101-V-0000.bin"
noncomputable def vp00000000011101101 : Blocks := vp00000000011101101_0
private theorem bp000000000111011010 : Branch 0 (-14574139/62500 : ℚ) vp00000000011101101 := by
  apply branch_left_normalized (c:=vp000000000111011010) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-14574139/62500 : ℚ) - ((0:ℤ):ℚ) = (-14574139/31250 : ℚ) by norm_num]
  exact coverp000000000111011010
private noncomputable def ep000000000111011011_0 : Blocks := edgeBlocks% "full/vectors/000000000111011011-E-0000.bin"
noncomputable def ep000000000111011011 : Blocks := ep000000000111011011_0
private theorem idp000000000111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011101101.list =
    C ((2:ℤ)^35) * horner X vp000000000111011011.list + horner X ep000000000111011011.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111011011 : Branch 1 (-14574139/62500 : ℚ) vp00000000011101101 := by
  apply branch_checked idp000000000111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-14574139/62500 : ℚ) - ((1:ℤ):ℚ) = (-14605389/31250 : ℚ) by norm_num]
  exact coverp000000000111011011
theorem coverp00000000011101101 : Covers (-14574139/62500 : ℚ) vp00000000011101101 := join_branches bp000000000111011010 bp000000000111011011
private noncomputable def vp000000000111011001_0 : Blocks := edgeBlocks% "full/vectors/000000000111011001-V-0000.bin"
noncomputable def vp000000000111011001 : Blocks := vp000000000111011001_0
theorem coverp000000000111011001 : Covers (-14542889/31250 : ℚ) vp000000000111011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111011000_0 : Blocks := edgeBlocks% "full/vectors/000000000111011000-V-0000.bin"
noncomputable def vp000000000111011000 : Blocks := vp000000000111011000_0
theorem coverp000000000111011000 : Covers (-14511639/31250 : ℚ) vp000000000111011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011101100_0 : Blocks := edgeBlocks% "full/vectors/00000000011101100-V-0000.bin"
noncomputable def vp00000000011101100 : Blocks := vp00000000011101100_0
private theorem bp000000000111011000 : Branch 0 (-14511639/62500 : ℚ) vp00000000011101100 := by
  apply branch_left_normalized (c:=vp000000000111011000) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-14511639/62500 : ℚ) - ((0:ℤ):ℚ) = (-14511639/31250 : ℚ) by norm_num]
  exact coverp000000000111011000
private noncomputable def ep000000000111011001_0 : Blocks := edgeBlocks% "full/vectors/000000000111011001-E-0000.bin"
noncomputable def ep000000000111011001 : Blocks := ep000000000111011001_0
private theorem idp000000000111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011101100.list =
    C ((2:ℤ)^35) * horner X vp000000000111011001.list + horner X ep000000000111011001.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111011001 : Branch 1 (-14511639/62500 : ℚ) vp00000000011101100 := by
  apply branch_checked idp000000000111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-14511639/62500 : ℚ) - ((1:ℤ):ℚ) = (-14542889/31250 : ℚ) by norm_num]
  exact coverp000000000111011001
theorem coverp00000000011101100 : Covers (-14511639/62500 : ℚ) vp00000000011101100 := join_branches bp000000000111011000 bp000000000111011001
private noncomputable def vp0000000001110110_0 : Blocks := edgeBlocks% "full/vectors/0000000001110110-V-0000.bin"
noncomputable def vp0000000001110110 : Blocks := vp0000000001110110_0
private theorem bp00000000011101100 : Branch 0 (-14511639/125000 : ℚ) vp0000000001110110 := by
  apply branch_left_normalized (c:=vp00000000011101100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-14511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-14511639/62500 : ℚ) by norm_num]
  exact coverp00000000011101100
private noncomputable def ep00000000011101101_0 : Blocks := edgeBlocks% "full/vectors/00000000011101101-E-0000.bin"
noncomputable def ep00000000011101101 : Blocks := ep00000000011101101_0
private theorem idp00000000011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001110110.list =
    C ((2:ℤ)^53) * horner X vp00000000011101101.list + horner X ep00000000011101101.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011101101 : Branch 1 (-14511639/125000 : ℚ) vp0000000001110110 := by
  apply branch_checked idp00000000011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-14511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-14574139/62500 : ℚ) by norm_num]
  exact coverp00000000011101101
theorem coverp0000000001110110 : Covers (-14511639/125000 : ℚ) vp0000000001110110 := join_branches bp00000000011101100 bp00000000011101101
private noncomputable def vp000000000111011_0 : Blocks := edgeBlocks% "full/vectors/000000000111011-V-0000.bin"
noncomputable def vp000000000111011 : Blocks := vp000000000111011_0
private theorem bp0000000001110110 : Branch 0 (-14511639/250000 : ℚ) vp000000000111011 := by
  apply branch_left_normalized (c:=vp0000000001110110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-14511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-14511639/125000 : ℚ) by norm_num]
  exact coverp0000000001110110
private noncomputable def ep0000000001110111_0 : Blocks := edgeBlocks% "full/vectors/0000000001110111-E-0000.bin"
noncomputable def ep0000000001110111 : Blocks := ep0000000001110111_0
private theorem idp0000000001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111011.list =
    C ((2:ℤ)^88) * horner X vp0000000001110111.list + horner X ep0000000001110111.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001110111 : Branch 1 (-14511639/250000 : ℚ) vp000000000111011 := by
  apply branch_checked idp0000000001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-14511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-14636639/125000 : ℚ) by norm_num]
  exact coverp0000000001110111
theorem coverp000000000111011 : Covers (-14511639/250000 : ℚ) vp000000000111011 := join_branches bp0000000001110110 bp0000000001110111
private noncomputable def vp000000000111010111_0 : Blocks := edgeBlocks% "full/vectors/000000000111010111-V-0000.bin"
noncomputable def vp000000000111010111 : Blocks := vp000000000111010111_0
theorem coverp000000000111010111 : Covers (-14480389/31250 : ℚ) vp000000000111010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111010110_0 : Blocks := edgeBlocks% "full/vectors/000000000111010110-V-0000.bin"
noncomputable def vp000000000111010110 : Blocks := vp000000000111010110_0
theorem coverp000000000111010110 : Covers (-14449139/31250 : ℚ) vp000000000111010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011101011_0 : Blocks := edgeBlocks% "full/vectors/00000000011101011-V-0000.bin"
noncomputable def vp00000000011101011 : Blocks := vp00000000011101011_0
private theorem bp000000000111010110 : Branch 0 (-14449139/62500 : ℚ) vp00000000011101011 := by
  apply branch_left_normalized (c:=vp000000000111010110) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-14449139/62500 : ℚ) - ((0:ℤ):ℚ) = (-14449139/31250 : ℚ) by norm_num]
  exact coverp000000000111010110
private noncomputable def ep000000000111010111_0 : Blocks := edgeBlocks% "full/vectors/000000000111010111-E-0000.bin"
noncomputable def ep000000000111010111 : Blocks := ep000000000111010111_0
private theorem idp000000000111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011101011.list =
    C ((2:ℤ)^35) * horner X vp000000000111010111.list + horner X ep000000000111010111.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111010111 : Branch 1 (-14449139/62500 : ℚ) vp00000000011101011 := by
  apply branch_checked idp000000000111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-14449139/62500 : ℚ) - ((1:ℤ):ℚ) = (-14480389/31250 : ℚ) by norm_num]
  exact coverp000000000111010111
theorem coverp00000000011101011 : Covers (-14449139/62500 : ℚ) vp00000000011101011 := join_branches bp000000000111010110 bp000000000111010111
private noncomputable def vp000000000111010101_0 : Blocks := edgeBlocks% "full/vectors/000000000111010101-V-0000.bin"
noncomputable def vp000000000111010101 : Blocks := vp000000000111010101_0
theorem coverp000000000111010101 : Covers (-14417889/31250 : ℚ) vp000000000111010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111010100_0 : Blocks := edgeBlocks% "full/vectors/000000000111010100-V-0000.bin"
noncomputable def vp000000000111010100 : Blocks := vp000000000111010100_0
theorem coverp000000000111010100 : Covers (-14386639/31250 : ℚ) vp000000000111010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011101010_0 : Blocks := edgeBlocks% "full/vectors/00000000011101010-V-0000.bin"
noncomputable def vp00000000011101010 : Blocks := vp00000000011101010_0
private theorem bp000000000111010100 : Branch 0 (-14386639/62500 : ℚ) vp00000000011101010 := by
  apply branch_left_normalized (c:=vp000000000111010100) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-14386639/62500 : ℚ) - ((0:ℤ):ℚ) = (-14386639/31250 : ℚ) by norm_num]
  exact coverp000000000111010100
private noncomputable def ep000000000111010101_0 : Blocks := edgeBlocks% "full/vectors/000000000111010101-E-0000.bin"
noncomputable def ep000000000111010101 : Blocks := ep000000000111010101_0
private theorem idp000000000111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011101010.list =
    C ((2:ℤ)^35) * horner X vp000000000111010101.list + horner X ep000000000111010101.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111010101 : Branch 1 (-14386639/62500 : ℚ) vp00000000011101010 := by
  apply branch_checked idp000000000111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-14386639/62500 : ℚ) - ((1:ℤ):ℚ) = (-14417889/31250 : ℚ) by norm_num]
  exact coverp000000000111010101
theorem coverp00000000011101010 : Covers (-14386639/62500 : ℚ) vp00000000011101010 := join_branches bp000000000111010100 bp000000000111010101
private noncomputable def vp0000000001110101_0 : Blocks := edgeBlocks% "full/vectors/0000000001110101-V-0000.bin"
noncomputable def vp0000000001110101 : Blocks := vp0000000001110101_0
private theorem bp00000000011101010 : Branch 0 (-14386639/125000 : ℚ) vp0000000001110101 := by
  apply branch_left_normalized (c:=vp00000000011101010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-14386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-14386639/62500 : ℚ) by norm_num]
  exact coverp00000000011101010
private noncomputable def ep00000000011101011_0 : Blocks := edgeBlocks% "full/vectors/00000000011101011-E-0000.bin"
noncomputable def ep00000000011101011 : Blocks := ep00000000011101011_0
private theorem idp00000000011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001110101.list =
    C ((2:ℤ)^53) * horner X vp00000000011101011.list + horner X ep00000000011101011.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011101011 : Branch 1 (-14386639/125000 : ℚ) vp0000000001110101 := by
  apply branch_checked idp00000000011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-14386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-14449139/62500 : ℚ) by norm_num]
  exact coverp00000000011101011
theorem coverp0000000001110101 : Covers (-14386639/125000 : ℚ) vp0000000001110101 := join_branches bp00000000011101010 bp00000000011101011
private noncomputable def vp0000000001110100111_0 : Blocks := edgeBlocks% "full/vectors/0000000001110100111-V-0000.bin"
noncomputable def vp0000000001110100111 : Blocks := vp0000000001110100111_0
theorem coverp0000000001110100111 : Covers (-14371014/15625 : ℚ) vp0000000001110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011101001101_0 : Blocks := edgeBlocks% "full/vectors/00000000011101001101-V-0000.bin"
noncomputable def vp00000000011101001101 : Blocks := vp00000000011101001101_0
theorem coverp00000000011101001101 : Covers (-28726403/15625 : ℚ) vp00000000011101001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011101001100_0 : Blocks := edgeBlocks% "full/vectors/00000000011101001100-V-0000.bin"
noncomputable def vp00000000011101001100 : Blocks := vp00000000011101001100_0
theorem coverp00000000011101001100 : Covers (-28710778/15625 : ℚ) vp00000000011101001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001110100110_0 : Blocks := edgeBlocks% "full/vectors/0000000001110100110-V-0000.bin"
noncomputable def vp0000000001110100110 : Blocks := vp0000000001110100110_0
private theorem bp00000000011101001100 : Branch 0 (-14355389/15625 : ℚ) vp0000000001110100110 := by
  apply branch_left_normalized (c:=vp00000000011101001100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-14355389/15625 : ℚ) - ((0:ℤ):ℚ) = (-28710778/15625 : ℚ) by norm_num]
  exact coverp00000000011101001100
private noncomputable def ep00000000011101001101_0 : Blocks := edgeBlocks% "full/vectors/00000000011101001101-E-0000.bin"
noncomputable def ep00000000011101001101 : Blocks := ep00000000011101001101_0
private theorem idp00000000011101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001110100110.list =
    C ((2:ℤ)^18) * horner X vp00000000011101001101.list + horner X ep00000000011101001101.list := by
  exact edge_identity (B := (2:ℤ)^125) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011101001101 : Branch 1 (-14355389/15625 : ℚ) vp0000000001110100110 := by
  apply branch_checked idp00000000011101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-14355389/15625 : ℚ) - ((1:ℤ):ℚ) = (-28726403/15625 : ℚ) by norm_num]
  exact coverp00000000011101001101
theorem coverp0000000001110100110 : Covers (-14355389/15625 : ℚ) vp0000000001110100110 := join_branches bp00000000011101001100 bp00000000011101001101
private noncomputable def vp000000000111010011_0 : Blocks := edgeBlocks% "full/vectors/000000000111010011-V-0000.bin"
noncomputable def vp000000000111010011 : Blocks := vp000000000111010011_0
private theorem bp0000000001110100110 : Branch 0 (-14355389/31250 : ℚ) vp000000000111010011 := by
  apply branch_left_normalized (c:=vp0000000001110100110) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-14355389/31250 : ℚ) - ((0:ℤ):ℚ) = (-14355389/15625 : ℚ) by norm_num]
  exact coverp0000000001110100110
private noncomputable def ep0000000001110100111_0 : Blocks := edgeBlocks% "full/vectors/0000000001110100111-E-0000.bin"
noncomputable def ep0000000001110100111 : Blocks := ep0000000001110100111_0
private theorem idp0000000001110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111010011.list =
    C ((2:ℤ)^24) * horner X vp0000000001110100111.list + horner X ep0000000001110100111.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001110100111 : Branch 1 (-14355389/31250 : ℚ) vp000000000111010011 := by
  apply branch_checked idp0000000001110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-14355389/31250 : ℚ) - ((1:ℤ):ℚ) = (-14371014/15625 : ℚ) by norm_num]
  exact coverp0000000001110100111
theorem coverp000000000111010011 : Covers (-14355389/31250 : ℚ) vp000000000111010011 := join_branches bp0000000001110100110 bp0000000001110100111
private noncomputable def vp00000000011101001011_0 : Blocks := edgeBlocks% "full/vectors/00000000011101001011-V-0000.bin"
noncomputable def vp00000000011101001011 : Blocks := vp00000000011101001011_0
theorem coverp00000000011101001011 : Covers (-28695153/15625 : ℚ) vp00000000011101001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011101001010_0 : Blocks := edgeBlocks% "full/vectors/00000000011101001010-V-0000.bin"
noncomputable def vp00000000011101001010 : Blocks := vp00000000011101001010_0
theorem coverp00000000011101001010 : Covers (-28679528/15625 : ℚ) vp00000000011101001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001110100101_0 : Blocks := edgeBlocks% "full/vectors/0000000001110100101-V-0000.bin"
noncomputable def vp0000000001110100101 : Blocks := vp0000000001110100101_0
private theorem bp00000000011101001010 : Branch 0 (-14339764/15625 : ℚ) vp0000000001110100101 := by
  apply branch_left_normalized (c:=vp00000000011101001010) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-14339764/15625 : ℚ) - ((0:ℤ):ℚ) = (-28679528/15625 : ℚ) by norm_num]
  exact coverp00000000011101001010
private noncomputable def ep00000000011101001011_0 : Blocks := edgeBlocks% "full/vectors/00000000011101001011-E-0000.bin"
noncomputable def ep00000000011101001011 : Blocks := ep00000000011101001011_0
private theorem idp00000000011101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001110100101.list =
    C ((2:ℤ)^17) * horner X vp00000000011101001011.list + horner X ep00000000011101001011.list := by
  exact edge_identity (B := (2:ℤ)^125) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011101001011 : Branch 1 (-14339764/15625 : ℚ) vp0000000001110100101 := by
  apply branch_checked idp00000000011101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-14339764/15625 : ℚ) - ((1:ℤ):ℚ) = (-28695153/15625 : ℚ) by norm_num]
  exact coverp00000000011101001011
theorem coverp0000000001110100101 : Covers (-14339764/15625 : ℚ) vp0000000001110100101 := join_branches bp00000000011101001010 bp00000000011101001011
private noncomputable def vp0000000001110100100_0 : Blocks := edgeBlocks% "full/vectors/0000000001110100100-V-0000.bin"
noncomputable def vp0000000001110100100 : Blocks := vp0000000001110100100_0
theorem coverp0000000001110100100 : Covers (-14324139/15625 : ℚ) vp0000000001110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111010010_0 : Blocks := edgeBlocks% "full/vectors/000000000111010010-V-0000.bin"
noncomputable def vp000000000111010010 : Blocks := vp000000000111010010_0
private theorem bp0000000001110100100 : Branch 0 (-14324139/31250 : ℚ) vp000000000111010010 := by
  apply branch_left_normalized (c:=vp0000000001110100100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-14324139/31250 : ℚ) - ((0:ℤ):ℚ) = (-14324139/15625 : ℚ) by norm_num]
  exact coverp0000000001110100100
private noncomputable def ep0000000001110100101_0 : Blocks := edgeBlocks% "full/vectors/0000000001110100101-E-0000.bin"
noncomputable def ep0000000001110100101 : Blocks := ep0000000001110100101_0
private theorem idp0000000001110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111010010.list =
    C ((2:ℤ)^23) * horner X vp0000000001110100101.list + horner X ep0000000001110100101.list := by
  exact edge_identity (B := (2:ℤ)^133) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001110100101 : Branch 1 (-14324139/31250 : ℚ) vp000000000111010010 := by
  apply branch_checked idp0000000001110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-14324139/31250 : ℚ) - ((1:ℤ):ℚ) = (-14339764/15625 : ℚ) by norm_num]
  exact coverp0000000001110100101
theorem coverp000000000111010010 : Covers (-14324139/31250 : ℚ) vp000000000111010010 := join_branches bp0000000001110100100 bp0000000001110100101
private noncomputable def vp00000000011101001_0 : Blocks := edgeBlocks% "full/vectors/00000000011101001-V-0000.bin"
noncomputable def vp00000000011101001 : Blocks := vp00000000011101001_0
private theorem bp000000000111010010 : Branch 0 (-14324139/62500 : ℚ) vp00000000011101001 := by
  apply branch_left_normalized (c:=vp000000000111010010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-14324139/62500 : ℚ) - ((0:ℤ):ℚ) = (-14324139/31250 : ℚ) by norm_num]
  exact coverp000000000111010010
private noncomputable def ep000000000111010011_0 : Blocks := edgeBlocks% "full/vectors/000000000111010011-E-0000.bin"
noncomputable def ep000000000111010011 : Blocks := ep000000000111010011_0
private theorem idp000000000111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011101001.list =
    C ((2:ℤ)^33) * horner X vp000000000111010011.list + horner X ep000000000111010011.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111010011 : Branch 1 (-14324139/62500 : ℚ) vp00000000011101001 := by
  apply branch_checked idp000000000111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-14324139/62500 : ℚ) - ((1:ℤ):ℚ) = (-14355389/31250 : ℚ) by norm_num]
  exact coverp000000000111010011
theorem coverp00000000011101001 : Covers (-14324139/62500 : ℚ) vp00000000011101001 := join_branches bp000000000111010010 bp000000000111010011
private noncomputable def vp00000000011101000_0 : Blocks := edgeBlocks% "full/vectors/00000000011101000-V-0000.bin"
noncomputable def vp00000000011101000 : Blocks := vp00000000011101000_0
theorem coverp00000000011101000 : Covers (-14261639/62500 : ℚ) vp00000000011101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001110100_0 : Blocks := edgeBlocks% "full/vectors/0000000001110100-V-0000.bin"
noncomputable def vp0000000001110100 : Blocks := vp0000000001110100_0
private theorem bp00000000011101000 : Branch 0 (-14261639/125000 : ℚ) vp0000000001110100 := by
  apply branch_left_normalized (c:=vp00000000011101000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-14261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-14261639/62500 : ℚ) by norm_num]
  exact coverp00000000011101000
private noncomputable def ep00000000011101001_0 : Blocks := edgeBlocks% "full/vectors/00000000011101001-E-0000.bin"
noncomputable def ep00000000011101001 : Blocks := ep00000000011101001_0
private theorem idp00000000011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001110100.list =
    C ((2:ℤ)^50) * horner X vp00000000011101001.list + horner X ep00000000011101001.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011101001 : Branch 1 (-14261639/125000 : ℚ) vp0000000001110100 := by
  apply branch_checked idp00000000011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-14261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-14324139/62500 : ℚ) by norm_num]
  exact coverp00000000011101001
theorem coverp0000000001110100 : Covers (-14261639/125000 : ℚ) vp0000000001110100 := join_branches bp00000000011101000 bp00000000011101001
private noncomputable def vp000000000111010_0 : Blocks := edgeBlocks% "full/vectors/000000000111010-V-0000.bin"
noncomputable def vp000000000111010 : Blocks := vp000000000111010_0
private theorem bp0000000001110100 : Branch 0 (-14261639/250000 : ℚ) vp000000000111010 := by
  apply branch_left_normalized (c:=vp0000000001110100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-14261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-14261639/125000 : ℚ) by norm_num]
  exact coverp0000000001110100
private noncomputable def ep0000000001110101_0 : Blocks := edgeBlocks% "full/vectors/0000000001110101-E-0000.bin"
noncomputable def ep0000000001110101 : Blocks := ep0000000001110101_0
private theorem idp0000000001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111010.list =
    C ((2:ℤ)^84) * horner X vp0000000001110101.list + horner X ep0000000001110101.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001110101 : Branch 1 (-14261639/250000 : ℚ) vp000000000111010 := by
  apply branch_checked idp0000000001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-14261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-14386639/125000 : ℚ) by norm_num]
  exact coverp0000000001110101
theorem coverp000000000111010 : Covers (-14261639/250000 : ℚ) vp000000000111010 := join_branches bp0000000001110100 bp0000000001110101
private noncomputable def vp00000000011101_0 : Blocks := edgeBlocks% "full/vectors/00000000011101-V-0000.bin"
private noncomputable def vp00000000011101_1 : Blocks := edgeBlocks% "full/vectors/00000000011101-V-0001.bin"
noncomputable def vp00000000011101 : Blocks := (Blocks.join vp00000000011101_0 vp00000000011101_1)
private theorem bp000000000111010 : Branch 0 (-14261639/500000 : ℚ) vp00000000011101 := by
  apply branch_left_normalized (c:=vp000000000111010) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-14261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-14261639/250000 : ℚ) by norm_num]
  exact coverp000000000111010
private noncomputable def ep000000000111011_0 : Blocks := edgeBlocks% "full/vectors/000000000111011-E-0000.bin"
private noncomputable def ep000000000111011_1 : Blocks := edgeBlocks% "full/vectors/000000000111011-E-0001.bin"
noncomputable def ep000000000111011 : Blocks := (Blocks.join ep000000000111011_0 ep000000000111011_1)
private theorem idp000000000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011101.list =
    C ((2:ℤ)^149) * horner X vp000000000111011.list + horner X ep000000000111011.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111011 : Branch 1 (-14261639/500000 : ℚ) vp00000000011101 := by
  apply branch_checked idp000000000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-14261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-14511639/250000 : ℚ) by norm_num]
  exact coverp000000000111011
theorem coverp00000000011101 : Covers (-14261639/500000 : ℚ) vp00000000011101 := join_branches bp000000000111010 bp000000000111011
private noncomputable def vp00000000011100111_0 : Blocks := edgeBlocks% "full/vectors/00000000011100111-V-0000.bin"
noncomputable def vp00000000011100111 : Blocks := vp00000000011100111_0
theorem coverp00000000011100111 : Covers (-14199139/62500 : ℚ) vp00000000011100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011100110_0 : Blocks := edgeBlocks% "full/vectors/00000000011100110-V-0000.bin"
noncomputable def vp00000000011100110 : Blocks := vp00000000011100110_0
theorem coverp00000000011100110 : Covers (-14136639/62500 : ℚ) vp00000000011100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001110011_0 : Blocks := edgeBlocks% "full/vectors/0000000001110011-V-0000.bin"
noncomputable def vp0000000001110011 : Blocks := vp0000000001110011_0
private theorem bp00000000011100110 : Branch 0 (-14136639/125000 : ℚ) vp0000000001110011 := by
  apply branch_left_normalized (c:=vp00000000011100110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-14136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-14136639/62500 : ℚ) by norm_num]
  exact coverp00000000011100110
private noncomputable def ep00000000011100111_0 : Blocks := edgeBlocks% "full/vectors/00000000011100111-E-0000.bin"
noncomputable def ep00000000011100111 : Blocks := ep00000000011100111_0
private theorem idp00000000011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001110011.list =
    C ((2:ℤ)^51) * horner X vp00000000011100111.list + horner X ep00000000011100111.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011100111 : Branch 1 (-14136639/125000 : ℚ) vp0000000001110011 := by
  apply branch_checked idp00000000011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-14136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-14199139/62500 : ℚ) by norm_num]
  exact coverp00000000011100111
theorem coverp0000000001110011 : Covers (-14136639/125000 : ℚ) vp0000000001110011 := join_branches bp00000000011100110 bp00000000011100111
private noncomputable def vp0000000001110010_0 : Blocks := edgeBlocks% "full/vectors/0000000001110010-V-0000.bin"
noncomputable def vp0000000001110010 : Blocks := vp0000000001110010_0
theorem coverp0000000001110010 : Covers (-14011639/125000 : ℚ) vp0000000001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111001_0 : Blocks := edgeBlocks% "full/vectors/000000000111001-V-0000.bin"
noncomputable def vp000000000111001 : Blocks := vp000000000111001_0
private theorem bp0000000001110010 : Branch 0 (-14011639/250000 : ℚ) vp000000000111001 := by
  apply branch_left_normalized (c:=vp0000000001110010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-14011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-14011639/125000 : ℚ) by norm_num]
  exact coverp0000000001110010
private noncomputable def ep0000000001110011_0 : Blocks := edgeBlocks% "full/vectors/0000000001110011-E-0000.bin"
noncomputable def ep0000000001110011 : Blocks := ep0000000001110011_0
private theorem idp0000000001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111001.list =
    C ((2:ℤ)^87) * horner X vp0000000001110011.list + horner X ep0000000001110011.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001110011 : Branch 1 (-14011639/250000 : ℚ) vp000000000111001 := by
  apply branch_checked idp0000000001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-14011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-14136639/125000 : ℚ) by norm_num]
  exact coverp0000000001110011
theorem coverp000000000111001 : Covers (-14011639/250000 : ℚ) vp000000000111001 := join_branches bp0000000001110010 bp0000000001110011
private noncomputable def vp00000000011100011_0 : Blocks := edgeBlocks% "full/vectors/00000000011100011-V-0000.bin"
noncomputable def vp00000000011100011 : Blocks := vp00000000011100011_0
theorem coverp00000000011100011 : Covers (-13949139/62500 : ℚ) vp00000000011100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011100010_0 : Blocks := edgeBlocks% "full/vectors/00000000011100010-V-0000.bin"
noncomputable def vp00000000011100010 : Blocks := vp00000000011100010_0
theorem coverp00000000011100010 : Covers (-13886639/62500 : ℚ) vp00000000011100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001110001_0 : Blocks := edgeBlocks% "full/vectors/0000000001110001-V-0000.bin"
noncomputable def vp0000000001110001 : Blocks := vp0000000001110001_0
private theorem bp00000000011100010 : Branch 0 (-13886639/125000 : ℚ) vp0000000001110001 := by
  apply branch_left_normalized (c:=vp00000000011100010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-13886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-13886639/62500 : ℚ) by norm_num]
  exact coverp00000000011100010
private noncomputable def ep00000000011100011_0 : Blocks := edgeBlocks% "full/vectors/00000000011100011-E-0000.bin"
noncomputable def ep00000000011100011 : Blocks := ep00000000011100011_0
private theorem idp00000000011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001110001.list =
    C ((2:ℤ)^59) * horner X vp00000000011100011.list + horner X ep00000000011100011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011100011 : Branch 1 (-13886639/125000 : ℚ) vp0000000001110001 := by
  apply branch_checked idp00000000011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-13886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-13949139/62500 : ℚ) by norm_num]
  exact coverp00000000011100011
theorem coverp0000000001110001 : Covers (-13886639/125000 : ℚ) vp0000000001110001 := join_branches bp00000000011100010 bp00000000011100011
private noncomputable def vp000000000111000011_0 : Blocks := edgeBlocks% "full/vectors/000000000111000011-V-0000.bin"
noncomputable def vp000000000111000011 : Blocks := vp000000000111000011_0
theorem coverp000000000111000011 : Covers (-13855389/31250 : ℚ) vp000000000111000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000111000010_0 : Blocks := edgeBlocks% "full/vectors/000000000111000010-V-0000.bin"
noncomputable def vp000000000111000010 : Blocks := vp000000000111000010_0
theorem coverp000000000111000010 : Covers (-13824139/31250 : ℚ) vp000000000111000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011100001_0 : Blocks := edgeBlocks% "full/vectors/00000000011100001-V-0000.bin"
noncomputable def vp00000000011100001 : Blocks := vp00000000011100001_0
private theorem bp000000000111000010 : Branch 0 (-13824139/62500 : ℚ) vp00000000011100001 := by
  apply branch_left_normalized (c:=vp000000000111000010) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-13824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-13824139/31250 : ℚ) by norm_num]
  exact coverp000000000111000010
private noncomputable def ep000000000111000011_0 : Blocks := edgeBlocks% "full/vectors/000000000111000011-E-0000.bin"
noncomputable def ep000000000111000011 : Blocks := ep000000000111000011_0
private theorem idp000000000111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011100001.list =
    C ((2:ℤ)^36) * horner X vp000000000111000011.list + horner X ep000000000111000011.list := by
  exact edge_identity (B := (2:ℤ)^150) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111000011 : Branch 1 (-13824139/62500 : ℚ) vp00000000011100001 := by
  apply branch_checked idp000000000111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-13824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-13855389/31250 : ℚ) by norm_num]
  exact coverp000000000111000011
theorem coverp00000000011100001 : Covers (-13824139/62500 : ℚ) vp00000000011100001 := join_branches bp000000000111000010 bp000000000111000011
private noncomputable def vp000000000111000001_0 : Blocks := edgeBlocks% "full/vectors/000000000111000001-V-0000.bin"
noncomputable def vp000000000111000001 : Blocks := vp000000000111000001_0
theorem coverp000000000111000001 : Covers (-13792889/31250 : ℚ) vp000000000111000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001110000001_0 : Blocks := edgeBlocks% "full/vectors/0000000001110000001-V-0000.bin"
noncomputable def vp0000000001110000001 : Blocks := vp0000000001110000001_0
theorem coverp0000000001110000001 : Covers (-13777264/15625 : ℚ) vp0000000001110000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011100000001_0 : Blocks := edgeBlocks% "full/vectors/00000000011100000001-V-0000.bin"
noncomputable def vp00000000011100000001 : Blocks := vp00000000011100000001_0
theorem coverp00000000011100000001 : Covers (-27538903/15625 : ℚ) vp00000000011100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011100000000_0 : Blocks := edgeBlocks% "full/vectors/00000000011100000000-V-0000.bin"
noncomputable def vp00000000011100000000 : Blocks := vp00000000011100000000_0
theorem coverp00000000011100000000 : Covers (-27523278/15625 : ℚ) vp00000000011100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001110000000_0 : Blocks := edgeBlocks% "full/vectors/0000000001110000000-V-0000.bin"
noncomputable def vp0000000001110000000 : Blocks := vp0000000001110000000_0
private theorem bp00000000011100000000 : Branch 0 (-13761639/15625 : ℚ) vp0000000001110000000 := by
  apply branch_left_normalized (c:=vp00000000011100000000) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-13761639/15625 : ℚ) - ((0:ℤ):ℚ) = (-27523278/15625 : ℚ) by norm_num]
  exact coverp00000000011100000000
private noncomputable def ep00000000011100000001_0 : Blocks := edgeBlocks% "full/vectors/00000000011100000001-E-0000.bin"
noncomputable def ep00000000011100000001 : Blocks := ep00000000011100000001_0
private theorem idp00000000011100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001110000000.list =
    C ((2:ℤ)^18) * horner X vp00000000011100000001.list + horner X ep00000000011100000001.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011100000001 : Branch 1 (-13761639/15625 : ℚ) vp0000000001110000000 := by
  apply branch_checked idp00000000011100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-13761639/15625 : ℚ) - ((1:ℤ):ℚ) = (-27538903/15625 : ℚ) by norm_num]
  exact coverp00000000011100000001
theorem coverp0000000001110000000 : Covers (-13761639/15625 : ℚ) vp0000000001110000000 := join_branches bp00000000011100000000 bp00000000011100000001
private noncomputable def vp000000000111000000_0 : Blocks := edgeBlocks% "full/vectors/000000000111000000-V-0000.bin"
noncomputable def vp000000000111000000 : Blocks := vp000000000111000000_0
private theorem bp0000000001110000000 : Branch 0 (-13761639/31250 : ℚ) vp000000000111000000 := by
  apply branch_left_normalized (c:=vp0000000001110000000) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-13761639/31250 : ℚ) - ((0:ℤ):ℚ) = (-13761639/15625 : ℚ) by norm_num]
  exact coverp0000000001110000000
private noncomputable def ep0000000001110000001_0 : Blocks := edgeBlocks% "full/vectors/0000000001110000001-E-0000.bin"
noncomputable def ep0000000001110000001 : Blocks := ep0000000001110000001_0
private theorem idp0000000001110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111000000.list =
    C ((2:ℤ)^25) * horner X vp0000000001110000001.list + horner X ep0000000001110000001.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001110000001 : Branch 1 (-13761639/31250 : ℚ) vp000000000111000000 := by
  apply branch_checked idp0000000001110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-13761639/31250 : ℚ) - ((1:ℤ):ℚ) = (-13777264/15625 : ℚ) by norm_num]
  exact coverp0000000001110000001
theorem coverp000000000111000000 : Covers (-13761639/31250 : ℚ) vp000000000111000000 := join_branches bp0000000001110000000 bp0000000001110000001
private noncomputable def vp00000000011100000_0 : Blocks := edgeBlocks% "full/vectors/00000000011100000-V-0000.bin"
noncomputable def vp00000000011100000 : Blocks := vp00000000011100000_0
private theorem bp000000000111000000 : Branch 0 (-13761639/62500 : ℚ) vp00000000011100000 := by
  apply branch_left_normalized (c:=vp000000000111000000) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-13761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-13761639/31250 : ℚ) by norm_num]
  exact coverp000000000111000000
private noncomputable def ep000000000111000001_0 : Blocks := edgeBlocks% "full/vectors/000000000111000001-E-0000.bin"
noncomputable def ep000000000111000001 : Blocks := ep000000000111000001_0
private theorem idp000000000111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011100000.list =
    C ((2:ℤ)^36) * horner X vp000000000111000001.list + horner X ep000000000111000001.list := by
  exact edge_identity (B := (2:ℤ)^152) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111000001 : Branch 1 (-13761639/62500 : ℚ) vp00000000011100000 := by
  apply branch_checked idp000000000111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-13761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-13792889/31250 : ℚ) by norm_num]
  exact coverp000000000111000001
theorem coverp00000000011100000 : Covers (-13761639/62500 : ℚ) vp00000000011100000 := join_branches bp000000000111000000 bp000000000111000001
private noncomputable def vp0000000001110000_0 : Blocks := edgeBlocks% "full/vectors/0000000001110000-V-0000.bin"
noncomputable def vp0000000001110000 : Blocks := vp0000000001110000_0
private theorem bp00000000011100000 : Branch 0 (-13761639/125000 : ℚ) vp0000000001110000 := by
  apply branch_left_normalized (c:=vp00000000011100000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-13761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-13761639/62500 : ℚ) by norm_num]
  exact coverp00000000011100000
private noncomputable def ep00000000011100001_0 : Blocks := edgeBlocks% "full/vectors/00000000011100001-E-0000.bin"
noncomputable def ep00000000011100001 : Blocks := ep00000000011100001_0
private theorem idp00000000011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001110000.list =
    C ((2:ℤ)^54) * horner X vp00000000011100001.list + horner X ep00000000011100001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011100001 : Branch 1 (-13761639/125000 : ℚ) vp0000000001110000 := by
  apply branch_checked idp00000000011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-13761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-13824139/62500 : ℚ) by norm_num]
  exact coverp00000000011100001
theorem coverp0000000001110000 : Covers (-13761639/125000 : ℚ) vp0000000001110000 := join_branches bp00000000011100000 bp00000000011100001
private noncomputable def vp000000000111000_0 : Blocks := edgeBlocks% "full/vectors/000000000111000-V-0000.bin"
noncomputable def vp000000000111000 : Blocks := vp000000000111000_0
private theorem bp0000000001110000 : Branch 0 (-13761639/250000 : ℚ) vp000000000111000 := by
  apply branch_left_normalized (c:=vp0000000001110000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-13761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-13761639/125000 : ℚ) by norm_num]
  exact coverp0000000001110000
private noncomputable def ep0000000001110001_0 : Blocks := edgeBlocks% "full/vectors/0000000001110001-E-0000.bin"
noncomputable def ep0000000001110001 : Blocks := ep0000000001110001_0
private theorem idp0000000001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111000.list =
    C ((2:ℤ)^89) * horner X vp0000000001110001.list + horner X ep0000000001110001.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001110001 : Branch 1 (-13761639/250000 : ℚ) vp000000000111000 := by
  apply branch_checked idp0000000001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-13761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-13886639/125000 : ℚ) by norm_num]
  exact coverp0000000001110001
theorem coverp000000000111000 : Covers (-13761639/250000 : ℚ) vp000000000111000 := join_branches bp0000000001110000 bp0000000001110001
private noncomputable def vp00000000011100_0 : Blocks := edgeBlocks% "full/vectors/00000000011100-V-0000.bin"
private noncomputable def vp00000000011100_1 : Blocks := edgeBlocks% "full/vectors/00000000011100-V-0001.bin"
noncomputable def vp00000000011100 : Blocks := (Blocks.join vp00000000011100_0 vp00000000011100_1)
private theorem bp000000000111000 : Branch 0 (-13761639/500000 : ℚ) vp00000000011100 := by
  apply branch_left_normalized (c:=vp000000000111000) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-13761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-13761639/250000 : ℚ) by norm_num]
  exact coverp000000000111000
private noncomputable def ep000000000111001_0 : Blocks := edgeBlocks% "full/vectors/000000000111001-E-0000.bin"
private noncomputable def ep000000000111001_1 : Blocks := edgeBlocks% "full/vectors/000000000111001-E-0001.bin"
noncomputable def ep000000000111001 : Blocks := (Blocks.join ep000000000111001_0 ep000000000111001_1)
private theorem idp000000000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011100.list =
    C ((2:ℤ)^163) * horner X vp000000000111001.list + horner X ep000000000111001.list := by
  exact edge_identity (B := (2:ℤ)^329) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111001 : Branch 1 (-13761639/500000 : ℚ) vp00000000011100 := by
  apply branch_checked idp000000000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-13761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-14011639/250000 : ℚ) by norm_num]
  exact coverp000000000111001
theorem coverp00000000011100 : Covers (-13761639/500000 : ℚ) vp00000000011100 := join_branches bp000000000111000 bp000000000111001
private noncomputable def vp0000000001110_0 : Blocks := edgeBlocks% "full/vectors/0000000001110-V-0000.bin"
private noncomputable def vp0000000001110_1 : Blocks := edgeBlocks% "full/vectors/0000000001110-V-0001.bin"
private noncomputable def vp0000000001110_2 : Blocks := edgeBlocks% "full/vectors/0000000001110-V-0002.bin"
noncomputable def vp0000000001110 : Blocks := (Blocks.join vp0000000001110_0 (Blocks.join vp0000000001110_1 vp0000000001110_2))
private theorem bp00000000011100 : Branch 0 (-13761639/1000000 : ℚ) vp0000000001110 := by
  apply branch_left_normalized (c:=vp00000000011100) (k:=0) (m:=154) (by decide +kernel)
  rw [show 2*(-13761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-13761639/500000 : ℚ) by norm_num]
  exact coverp00000000011100
private noncomputable def ep00000000011101_0 : Blocks := edgeBlocks% "full/vectors/00000000011101-E-0000.bin"
private noncomputable def ep00000000011101_1 : Blocks := edgeBlocks% "full/vectors/00000000011101-E-0001.bin"
private noncomputable def ep00000000011101_2 : Blocks := edgeBlocks% "full/vectors/00000000011101-E-0002.bin"
noncomputable def ep00000000011101 : Blocks := (Blocks.join ep00000000011101_0 (Blocks.join ep00000000011101_1 ep00000000011101_2))
private theorem idp00000000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001110.list =
    C ((2:ℤ)^298) * horner X vp00000000011101.list + horner X ep00000000011101.list := by
  exact edge_identity (B := (2:ℤ)^530) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011101 : Branch 1 (-13761639/1000000 : ℚ) vp0000000001110 := by
  apply branch_checked idp00000000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-13761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-14261639/500000 : ℚ) by norm_num]
  exact coverp00000000011101
theorem coverp0000000001110 : Covers (-13761639/1000000 : ℚ) vp0000000001110 := join_branches bp00000000011100 bp00000000011101
private noncomputable def vp000000000111_0 : Blocks := edgeBlocks% "full/vectors/000000000111-V-0000.bin"
private noncomputable def vp000000000111_1 : Blocks := edgeBlocks% "full/vectors/000000000111-V-0001.bin"
private noncomputable def vp000000000111_2 : Blocks := edgeBlocks% "full/vectors/000000000111-V-0002.bin"
private noncomputable def vp000000000111_3 : Blocks := edgeBlocks% "full/vectors/000000000111-V-0003.bin"
private noncomputable def vp000000000111_4 : Blocks := edgeBlocks% "full/vectors/000000000111-V-0004.bin"
noncomputable def vp000000000111 : Blocks := (Blocks.join (Blocks.join vp000000000111_0 vp000000000111_1) (Blocks.join vp000000000111_2 (Blocks.join vp000000000111_3 vp000000000111_4)))
private theorem bp0000000001110 : Branch 0 (-13761639/2000000 : ℚ) vp000000000111 := by
  apply branch_left_normalized (c:=vp0000000001110) (k:=0) (m:=286) (by decide +kernel)
  rw [show 2*(-13761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-13761639/1000000 : ℚ) by norm_num]
  exact coverp0000000001110
private noncomputable def ep0000000001111_0 : Blocks := edgeBlocks% "full/vectors/0000000001111-E-0000.bin"
private noncomputable def ep0000000001111_1 : Blocks := edgeBlocks% "full/vectors/0000000001111-E-0001.bin"
private noncomputable def ep0000000001111_2 : Blocks := edgeBlocks% "full/vectors/0000000001111-E-0002.bin"
private noncomputable def ep0000000001111_3 : Blocks := edgeBlocks% "full/vectors/0000000001111-E-0003.bin"
private noncomputable def ep0000000001111_4 : Blocks := edgeBlocks% "full/vectors/0000000001111-E-0004.bin"
noncomputable def ep0000000001111 : Blocks := (Blocks.join (Blocks.join ep0000000001111_0 ep0000000001111_1) (Blocks.join ep0000000001111_2 (Blocks.join ep0000000001111_3 ep0000000001111_4)))
private theorem idp0000000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000111.list =
    C ((2:ℤ)^553) * horner X vp0000000001111.list + horner X ep0000000001111.list := by
  exact edge_identity (B := (2:ℤ)^930) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001111 : Branch 1 (-13761639/2000000 : ℚ) vp000000000111 := by
  apply branch_checked idp0000000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-13761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-14761639/1000000 : ℚ) by norm_num]
  exact coverp0000000001111
theorem coverp000000000111 : Covers (-13761639/2000000 : ℚ) vp000000000111 := join_branches bp0000000001110 bp0000000001111
end NextProof.EdgeFull

