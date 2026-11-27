import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00010

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000000001001111111_0 : Blocks := edgeBlocks% "full/vectors/00000000001001111111-V-0000.bin"
noncomputable def vp00000000001001111111 : Blocks := vp00000000001001111111_0
theorem coverp00000000001001111111 : Covers (-9507653/15625 : ℚ) vp00000000001001111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010011111101_0 : Blocks := edgeBlocks% "full/vectors/000000000010011111101-V-0000.bin"
noncomputable def vp000000000010011111101 : Blocks := vp000000000010011111101_0
theorem coverp000000000010011111101 : Covers (-18999681/15625 : ℚ) vp000000000010011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010011111100_0 : Blocks := edgeBlocks% "full/vectors/000000000010011111100-V-0000.bin"
noncomputable def vp000000000010011111100 : Blocks := vp000000000010011111100_0
theorem coverp000000000010011111100 : Covers (-18984056/15625 : ℚ) vp000000000010011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001111110_0 : Blocks := edgeBlocks% "full/vectors/00000000001001111110-V-0000.bin"
noncomputable def vp00000000001001111110 : Blocks := vp00000000001001111110_0
private theorem bp000000000010011111100 : Branch 0 (-9492028/15625 : ℚ) vp00000000001001111110 := by
  apply branch_left_normalized (c:=vp000000000010011111100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-9492028/15625 : ℚ) - ((0:ℤ):ℚ) = (-18984056/15625 : ℚ) by norm_num]
  exact coverp000000000010011111100
private noncomputable def ep000000000010011111101_0 : Blocks := edgeBlocks% "full/vectors/000000000010011111101-E-0000.bin"
noncomputable def ep000000000010011111101 : Blocks := ep000000000010011111101_0
private theorem idp000000000010011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001001111110.list =
    C ((2:ℤ)^17) * horner X vp000000000010011111101.list + horner X ep000000000010011111101.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010011111101 : Branch 1 (-9492028/15625 : ℚ) vp00000000001001111110 := by
  apply branch_checked idp000000000010011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-9492028/15625 : ℚ) - ((1:ℤ):ℚ) = (-18999681/15625 : ℚ) by norm_num]
  exact coverp000000000010011111101
theorem coverp00000000001001111110 : Covers (-9492028/15625 : ℚ) vp00000000001001111110 := join_branches bp000000000010011111100 bp000000000010011111101
private noncomputable def vp0000000000100111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111111-V-0000.bin"
noncomputable def vp0000000000100111111 : Blocks := vp0000000000100111111_0
private theorem bp00000000001001111110 : Branch 0 (-4746014/15625 : ℚ) vp0000000000100111111 := by
  apply branch_left_normalized (c:=vp00000000001001111110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4746014/15625 : ℚ) - ((0:ℤ):ℚ) = (-9492028/15625 : ℚ) by norm_num]
  exact coverp00000000001001111110
private noncomputable def ep00000000001001111111_0 : Blocks := edgeBlocks% "full/vectors/00000000001001111111-E-0000.bin"
noncomputable def ep00000000001001111111 : Blocks := ep00000000001001111111_0
private theorem idp00000000001001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100111111.list =
    C ((2:ℤ)^23) * horner X vp00000000001001111111.list + horner X ep00000000001001111111.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001111111 : Branch 1 (-4746014/15625 : ℚ) vp0000000000100111111 := by
  apply branch_checked idp00000000001001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-4746014/15625 : ℚ) - ((1:ℤ):ℚ) = (-9507653/15625 : ℚ) by norm_num]
  exact coverp00000000001001111111
theorem coverp0000000000100111111 : Covers (-4746014/15625 : ℚ) vp0000000000100111111 := join_branches bp00000000001001111110 bp00000000001001111111
private noncomputable def vp0000000000100111110_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111110-V-0000.bin"
noncomputable def vp0000000000100111110 : Blocks := vp0000000000100111110_0
theorem coverp0000000000100111110 : Covers (-4730389/15625 : ℚ) vp0000000000100111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010011111_0 : Blocks := edgeBlocks% "full/vectors/000000000010011111-V-0000.bin"
noncomputable def vp000000000010011111 : Blocks := vp000000000010011111_0
private theorem bp0000000000100111110 : Branch 0 (-4730389/31250 : ℚ) vp000000000010011111 := by
  apply branch_left_normalized (c:=vp0000000000100111110) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4730389/31250 : ℚ) - ((0:ℤ):ℚ) = (-4730389/15625 : ℚ) by norm_num]
  exact coverp0000000000100111110
private noncomputable def ep0000000000100111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111111-E-0000.bin"
noncomputable def ep0000000000100111111 : Blocks := ep0000000000100111111_0
private theorem idp0000000000100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010011111.list =
    C ((2:ℤ)^31) * horner X vp0000000000100111111.list + horner X ep0000000000100111111.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100111111 : Branch 1 (-4730389/31250 : ℚ) vp000000000010011111 := by
  apply branch_checked idp0000000000100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-4730389/31250 : ℚ) - ((1:ℤ):ℚ) = (-4746014/15625 : ℚ) by norm_num]
  exact coverp0000000000100111111
theorem coverp000000000010011111 : Covers (-4730389/31250 : ℚ) vp000000000010011111 := join_branches bp0000000000100111110 bp0000000000100111111
private noncomputable def vp0000000000100111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111101-V-0000.bin"
noncomputable def vp0000000000100111101 : Blocks := vp0000000000100111101_0
theorem coverp0000000000100111101 : Covers (-4714764/15625 : ℚ) vp0000000000100111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100111100_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111100-V-0000.bin"
noncomputable def vp0000000000100111100 : Blocks := vp0000000000100111100_0
theorem coverp0000000000100111100 : Covers (-4699139/15625 : ℚ) vp0000000000100111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010011110_0 : Blocks := edgeBlocks% "full/vectors/000000000010011110-V-0000.bin"
noncomputable def vp000000000010011110 : Blocks := vp000000000010011110_0
private theorem bp0000000000100111100 : Branch 0 (-4699139/31250 : ℚ) vp000000000010011110 := by
  apply branch_left_normalized (c:=vp0000000000100111100) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-4699139/31250 : ℚ) - ((0:ℤ):ℚ) = (-4699139/15625 : ℚ) by norm_num]
  exact coverp0000000000100111100
private noncomputable def ep0000000000100111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111101-E-0000.bin"
noncomputable def ep0000000000100111101 : Blocks := ep0000000000100111101_0
private theorem idp0000000000100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010011110.list =
    C ((2:ℤ)^32) * horner X vp0000000000100111101.list + horner X ep0000000000100111101.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100111101 : Branch 1 (-4699139/31250 : ℚ) vp000000000010011110 := by
  apply branch_checked idp0000000000100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-4699139/31250 : ℚ) - ((1:ℤ):ℚ) = (-4714764/15625 : ℚ) by norm_num]
  exact coverp0000000000100111101
theorem coverp000000000010011110 : Covers (-4699139/31250 : ℚ) vp000000000010011110 := join_branches bp0000000000100111100 bp0000000000100111101
private noncomputable def vp00000000001001111_0 : Blocks := edgeBlocks% "full/vectors/00000000001001111-V-0000.bin"
noncomputable def vp00000000001001111 : Blocks := vp00000000001001111_0
private theorem bp000000000010011110 : Branch 0 (-4699139/62500 : ℚ) vp00000000001001111 := by
  apply branch_left_normalized (c:=vp000000000010011110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-4699139/62500 : ℚ) - ((0:ℤ):ℚ) = (-4699139/31250 : ℚ) by norm_num]
  exact coverp000000000010011110
private noncomputable def ep000000000010011111_0 : Blocks := edgeBlocks% "full/vectors/000000000010011111-E-0000.bin"
noncomputable def ep000000000010011111 : Blocks := ep000000000010011111_0
private theorem idp000000000010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001001111.list =
    C ((2:ℤ)^49) * horner X vp000000000010011111.list + horner X ep000000000010011111.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010011111 : Branch 1 (-4699139/62500 : ℚ) vp00000000001001111 := by
  apply branch_checked idp000000000010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-4699139/62500 : ℚ) - ((1:ℤ):ℚ) = (-4730389/31250 : ℚ) by norm_num]
  exact coverp000000000010011111
theorem coverp00000000001001111 : Covers (-4699139/62500 : ℚ) vp00000000001001111 := join_branches bp000000000010011110 bp000000000010011111
private noncomputable def vp00000000001001110111_0 : Blocks := edgeBlocks% "full/vectors/00000000001001110111-V-0000.bin"
noncomputable def vp00000000001001110111 : Blocks := vp00000000001001110111_0
theorem coverp00000000001001110111 : Covers (-9382653/15625 : ℚ) vp00000000001001110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001110110_0 : Blocks := edgeBlocks% "full/vectors/00000000001001110110-V-0000.bin"
noncomputable def vp00000000001001110110 : Blocks := vp00000000001001110110_0
theorem coverp00000000001001110110 : Covers (-9367028/15625 : ℚ) vp00000000001001110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111011-V-0000.bin"
noncomputable def vp0000000000100111011 : Blocks := vp0000000000100111011_0
private theorem bp00000000001001110110 : Branch 0 (-4683514/15625 : ℚ) vp0000000000100111011 := by
  apply branch_left_normalized (c:=vp00000000001001110110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4683514/15625 : ℚ) - ((0:ℤ):ℚ) = (-9367028/15625 : ℚ) by norm_num]
  exact coverp00000000001001110110
private noncomputable def ep00000000001001110111_0 : Blocks := edgeBlocks% "full/vectors/00000000001001110111-E-0000.bin"
noncomputable def ep00000000001001110111 : Blocks := ep00000000001001110111_0
private theorem idp00000000001001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100111011.list =
    C ((2:ℤ)^23) * horner X vp00000000001001110111.list + horner X ep00000000001001110111.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001110111 : Branch 1 (-4683514/15625 : ℚ) vp0000000000100111011 := by
  apply branch_checked idp00000000001001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-4683514/15625 : ℚ) - ((1:ℤ):ℚ) = (-9382653/15625 : ℚ) by norm_num]
  exact coverp00000000001001110111
theorem coverp0000000000100111011 : Covers (-4683514/15625 : ℚ) vp0000000000100111011 := join_branches bp00000000001001110110 bp00000000001001110111
private noncomputable def vp0000000000100111010_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111010-V-0000.bin"
noncomputable def vp0000000000100111010 : Blocks := vp0000000000100111010_0
theorem coverp0000000000100111010 : Covers (-4667889/15625 : ℚ) vp0000000000100111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010011101_0 : Blocks := edgeBlocks% "full/vectors/000000000010011101-V-0000.bin"
noncomputable def vp000000000010011101 : Blocks := vp000000000010011101_0
private theorem bp0000000000100111010 : Branch 0 (-4667889/31250 : ℚ) vp000000000010011101 := by
  apply branch_left_normalized (c:=vp0000000000100111010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4667889/31250 : ℚ) - ((0:ℤ):ℚ) = (-4667889/15625 : ℚ) by norm_num]
  exact coverp0000000000100111010
private noncomputable def ep0000000000100111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111011-E-0000.bin"
noncomputable def ep0000000000100111011 : Blocks := ep0000000000100111011_0
private theorem idp0000000000100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010011101.list =
    C ((2:ℤ)^32) * horner X vp0000000000100111011.list + horner X ep0000000000100111011.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100111011 : Branch 1 (-4667889/31250 : ℚ) vp000000000010011101 := by
  apply branch_checked idp0000000000100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-4667889/31250 : ℚ) - ((1:ℤ):ℚ) = (-4683514/15625 : ℚ) by norm_num]
  exact coverp0000000000100111011
theorem coverp000000000010011101 : Covers (-4667889/31250 : ℚ) vp000000000010011101 := join_branches bp0000000000100111010 bp0000000000100111011
private noncomputable def vp0000000000100111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111001-V-0000.bin"
noncomputable def vp0000000000100111001 : Blocks := vp0000000000100111001_0
theorem coverp0000000000100111001 : Covers (-4652264/15625 : ℚ) vp0000000000100111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001110001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001110001-V-0000.bin"
noncomputable def vp00000000001001110001 : Blocks := vp00000000001001110001_0
theorem coverp00000000001001110001 : Covers (-9288903/15625 : ℚ) vp00000000001001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001110000_0 : Blocks := edgeBlocks% "full/vectors/00000000001001110000-V-0000.bin"
noncomputable def vp00000000001001110000 : Blocks := vp00000000001001110000_0
theorem coverp00000000001001110000 : Covers (-9273278/15625 : ℚ) vp00000000001001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100111000_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111000-V-0000.bin"
noncomputable def vp0000000000100111000 : Blocks := vp0000000000100111000_0
private theorem bp00000000001001110000 : Branch 0 (-4636639/15625 : ℚ) vp0000000000100111000 := by
  apply branch_left_normalized (c:=vp00000000001001110000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4636639/15625 : ℚ) - ((0:ℤ):ℚ) = (-9273278/15625 : ℚ) by norm_num]
  exact coverp00000000001001110000
private noncomputable def ep00000000001001110001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001110001-E-0000.bin"
noncomputable def ep00000000001001110001 : Blocks := ep00000000001001110001_0
private theorem idp00000000001001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100111000.list =
    C ((2:ℤ)^23) * horner X vp00000000001001110001.list + horner X ep00000000001001110001.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001110001 : Branch 1 (-4636639/15625 : ℚ) vp0000000000100111000 := by
  apply branch_checked idp00000000001001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-4636639/15625 : ℚ) - ((1:ℤ):ℚ) = (-9288903/15625 : ℚ) by norm_num]
  exact coverp00000000001001110001
theorem coverp0000000000100111000 : Covers (-4636639/15625 : ℚ) vp0000000000100111000 := join_branches bp00000000001001110000 bp00000000001001110001
private noncomputable def vp000000000010011100_0 : Blocks := edgeBlocks% "full/vectors/000000000010011100-V-0000.bin"
noncomputable def vp000000000010011100 : Blocks := vp000000000010011100_0
private theorem bp0000000000100111000 : Branch 0 (-4636639/31250 : ℚ) vp000000000010011100 := by
  apply branch_left_normalized (c:=vp0000000000100111000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4636639/31250 : ℚ) - ((0:ℤ):ℚ) = (-4636639/15625 : ℚ) by norm_num]
  exact coverp0000000000100111000
private noncomputable def ep0000000000100111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111001-E-0000.bin"
noncomputable def ep0000000000100111001 : Blocks := ep0000000000100111001_0
private theorem idp0000000000100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010011100.list =
    C ((2:ℤ)^33) * horner X vp0000000000100111001.list + horner X ep0000000000100111001.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100111001 : Branch 1 (-4636639/31250 : ℚ) vp000000000010011100 := by
  apply branch_checked idp0000000000100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-4636639/31250 : ℚ) - ((1:ℤ):ℚ) = (-4652264/15625 : ℚ) by norm_num]
  exact coverp0000000000100111001
theorem coverp000000000010011100 : Covers (-4636639/31250 : ℚ) vp000000000010011100 := join_branches bp0000000000100111000 bp0000000000100111001
private noncomputable def vp00000000001001110_0 : Blocks := edgeBlocks% "full/vectors/00000000001001110-V-0000.bin"
noncomputable def vp00000000001001110 : Blocks := vp00000000001001110_0
private theorem bp000000000010011100 : Branch 0 (-4636639/62500 : ℚ) vp00000000001001110 := by
  apply branch_left_normalized (c:=vp000000000010011100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-4636639/62500 : ℚ) - ((0:ℤ):ℚ) = (-4636639/31250 : ℚ) by norm_num]
  exact coverp000000000010011100
private noncomputable def ep000000000010011101_0 : Blocks := edgeBlocks% "full/vectors/000000000010011101-E-0000.bin"
noncomputable def ep000000000010011101 : Blocks := ep000000000010011101_0
private theorem idp000000000010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001001110.list =
    C ((2:ℤ)^49) * horner X vp000000000010011101.list + horner X ep000000000010011101.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010011101 : Branch 1 (-4636639/62500 : ℚ) vp00000000001001110 := by
  apply branch_checked idp000000000010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-4636639/62500 : ℚ) - ((1:ℤ):ℚ) = (-4667889/31250 : ℚ) by norm_num]
  exact coverp000000000010011101
theorem coverp00000000001001110 : Covers (-4636639/62500 : ℚ) vp00000000001001110 := join_branches bp000000000010011100 bp000000000010011101
private noncomputable def vp0000000000100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111-V-0000.bin"
noncomputable def vp0000000000100111 : Blocks := vp0000000000100111_0
private theorem bp00000000001001110 : Branch 0 (-4636639/125000 : ℚ) vp0000000000100111 := by
  apply branch_left_normalized (c:=vp00000000001001110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-4636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-4636639/62500 : ℚ) by norm_num]
  exact coverp00000000001001110
private noncomputable def ep00000000001001111_0 : Blocks := edgeBlocks% "full/vectors/00000000001001111-E-0000.bin"
noncomputable def ep00000000001001111 : Blocks := ep00000000001001111_0
private theorem idp00000000001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100111.list =
    C ((2:ℤ)^78) * horner X vp00000000001001111.list + horner X ep00000000001001111.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001111 : Branch 1 (-4636639/125000 : ℚ) vp0000000000100111 := by
  apply branch_checked idp00000000001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-4699139/62500 : ℚ) by norm_num]
  exact coverp00000000001001111
theorem coverp0000000000100111 : Covers (-4636639/125000 : ℚ) vp0000000000100111 := join_branches bp00000000001001110 bp00000000001001111
private noncomputable def vp0000000000100110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110111-V-0000.bin"
noncomputable def vp0000000000100110111 : Blocks := vp0000000000100110111_0
theorem coverp0000000000100110111 : Covers (-4621014/15625 : ℚ) vp0000000000100110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100110110_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110110-V-0000.bin"
noncomputable def vp0000000000100110110 : Blocks := vp0000000000100110110_0
theorem coverp0000000000100110110 : Covers (-4605389/15625 : ℚ) vp0000000000100110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010011011_0 : Blocks := edgeBlocks% "full/vectors/000000000010011011-V-0000.bin"
noncomputable def vp000000000010011011 : Blocks := vp000000000010011011_0
private theorem bp0000000000100110110 : Branch 0 (-4605389/31250 : ℚ) vp000000000010011011 := by
  apply branch_left_normalized (c:=vp0000000000100110110) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-4605389/31250 : ℚ) - ((0:ℤ):ℚ) = (-4605389/15625 : ℚ) by norm_num]
  exact coverp0000000000100110110
private noncomputable def ep0000000000100110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110111-E-0000.bin"
noncomputable def ep0000000000100110111 : Blocks := ep0000000000100110111_0
private theorem idp0000000000100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010011011.list =
    C ((2:ℤ)^33) * horner X vp0000000000100110111.list + horner X ep0000000000100110111.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100110111 : Branch 1 (-4605389/31250 : ℚ) vp000000000010011011 := by
  apply branch_checked idp0000000000100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-4605389/31250 : ℚ) - ((1:ℤ):ℚ) = (-4621014/15625 : ℚ) by norm_num]
  exact coverp0000000000100110111
theorem coverp000000000010011011 : Covers (-4605389/31250 : ℚ) vp000000000010011011 := join_branches bp0000000000100110110 bp0000000000100110111
private noncomputable def vp0000000000100110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110101-V-0000.bin"
noncomputable def vp0000000000100110101 : Blocks := vp0000000000100110101_0
theorem coverp0000000000100110101 : Covers (-4589764/15625 : ℚ) vp0000000000100110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100110100_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110100-V-0000.bin"
noncomputable def vp0000000000100110100 : Blocks := vp0000000000100110100_0
theorem coverp0000000000100110100 : Covers (-4574139/15625 : ℚ) vp0000000000100110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010011010_0 : Blocks := edgeBlocks% "full/vectors/000000000010011010-V-0000.bin"
noncomputable def vp000000000010011010 : Blocks := vp000000000010011010_0
private theorem bp0000000000100110100 : Branch 0 (-4574139/31250 : ℚ) vp000000000010011010 := by
  apply branch_left_normalized (c:=vp0000000000100110100) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4574139/31250 : ℚ) - ((0:ℤ):ℚ) = (-4574139/15625 : ℚ) by norm_num]
  exact coverp0000000000100110100
private noncomputable def ep0000000000100110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110101-E-0000.bin"
noncomputable def ep0000000000100110101 : Blocks := ep0000000000100110101_0
private theorem idp0000000000100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010011010.list =
    C ((2:ℤ)^33) * horner X vp0000000000100110101.list + horner X ep0000000000100110101.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100110101 : Branch 1 (-4574139/31250 : ℚ) vp000000000010011010 := by
  apply branch_checked idp0000000000100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-4574139/31250 : ℚ) - ((1:ℤ):ℚ) = (-4589764/15625 : ℚ) by norm_num]
  exact coverp0000000000100110101
theorem coverp000000000010011010 : Covers (-4574139/31250 : ℚ) vp000000000010011010 := join_branches bp0000000000100110100 bp0000000000100110101
private noncomputable def vp00000000001001101_0 : Blocks := edgeBlocks% "full/vectors/00000000001001101-V-0000.bin"
noncomputable def vp00000000001001101 : Blocks := vp00000000001001101_0
private theorem bp000000000010011010 : Branch 0 (-4574139/62500 : ℚ) vp00000000001001101 := by
  apply branch_left_normalized (c:=vp000000000010011010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-4574139/62500 : ℚ) - ((0:ℤ):ℚ) = (-4574139/31250 : ℚ) by norm_num]
  exact coverp000000000010011010
private noncomputable def ep000000000010011011_0 : Blocks := edgeBlocks% "full/vectors/000000000010011011-E-0000.bin"
noncomputable def ep000000000010011011 : Blocks := ep000000000010011011_0
private theorem idp000000000010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001001101.list =
    C ((2:ℤ)^49) * horner X vp000000000010011011.list + horner X ep000000000010011011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010011011 : Branch 1 (-4574139/62500 : ℚ) vp00000000001001101 := by
  apply branch_checked idp000000000010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-4574139/62500 : ℚ) - ((1:ℤ):ℚ) = (-4605389/31250 : ℚ) by norm_num]
  exact coverp000000000010011011
theorem coverp00000000001001101 : Covers (-4574139/62500 : ℚ) vp00000000001001101 := join_branches bp000000000010011010 bp000000000010011011
private noncomputable def vp00000000001001100111_0 : Blocks := edgeBlocks% "full/vectors/00000000001001100111-V-0000.bin"
noncomputable def vp00000000001001100111 : Blocks := vp00000000001001100111_0
theorem coverp00000000001001100111 : Covers (-9132653/15625 : ℚ) vp00000000001001100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001100110_0 : Blocks := edgeBlocks% "full/vectors/00000000001001100110-V-0000.bin"
noncomputable def vp00000000001001100110 : Blocks := vp00000000001001100110_0
theorem coverp00000000001001100110 : Covers (-9117028/15625 : ℚ) vp00000000001001100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100110011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110011-V-0000.bin"
noncomputable def vp0000000000100110011 : Blocks := vp0000000000100110011_0
private theorem bp00000000001001100110 : Branch 0 (-4558514/15625 : ℚ) vp0000000000100110011 := by
  apply branch_left_normalized (c:=vp00000000001001100110) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4558514/15625 : ℚ) - ((0:ℤ):ℚ) = (-9117028/15625 : ℚ) by norm_num]
  exact coverp00000000001001100110
private noncomputable def ep00000000001001100111_0 : Blocks := edgeBlocks% "full/vectors/00000000001001100111-E-0000.bin"
noncomputable def ep00000000001001100111 : Blocks := ep00000000001001100111_0
private theorem idp00000000001001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100110011.list =
    C ((2:ℤ)^23) * horner X vp00000000001001100111.list + horner X ep00000000001001100111.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001100111 : Branch 1 (-4558514/15625 : ℚ) vp0000000000100110011 := by
  apply branch_checked idp00000000001001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-4558514/15625 : ℚ) - ((1:ℤ):ℚ) = (-9132653/15625 : ℚ) by norm_num]
  exact coverp00000000001001100111
theorem coverp0000000000100110011 : Covers (-4558514/15625 : ℚ) vp0000000000100110011 := join_branches bp00000000001001100110 bp00000000001001100111
private noncomputable def vp0000000000100110010_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110010-V-0000.bin"
noncomputable def vp0000000000100110010 : Blocks := vp0000000000100110010_0
theorem coverp0000000000100110010 : Covers (-4542889/15625 : ℚ) vp0000000000100110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010011001_0 : Blocks := edgeBlocks% "full/vectors/000000000010011001-V-0000.bin"
noncomputable def vp000000000010011001 : Blocks := vp000000000010011001_0
private theorem bp0000000000100110010 : Branch 0 (-4542889/31250 : ℚ) vp000000000010011001 := by
  apply branch_left_normalized (c:=vp0000000000100110010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4542889/31250 : ℚ) - ((0:ℤ):ℚ) = (-4542889/15625 : ℚ) by norm_num]
  exact coverp0000000000100110010
private noncomputable def ep0000000000100110011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110011-E-0000.bin"
noncomputable def ep0000000000100110011 : Blocks := ep0000000000100110011_0
private theorem idp0000000000100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010011001.list =
    C ((2:ℤ)^32) * horner X vp0000000000100110011.list + horner X ep0000000000100110011.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100110011 : Branch 1 (-4542889/31250 : ℚ) vp000000000010011001 := by
  apply branch_checked idp0000000000100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-4542889/31250 : ℚ) - ((1:ℤ):ℚ) = (-4558514/15625 : ℚ) by norm_num]
  exact coverp0000000000100110011
theorem coverp000000000010011001 : Covers (-4542889/31250 : ℚ) vp000000000010011001 := join_branches bp0000000000100110010 bp0000000000100110011
private noncomputable def vp0000000000100110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110001-V-0000.bin"
noncomputable def vp0000000000100110001 : Blocks := vp0000000000100110001_0
theorem coverp0000000000100110001 : Covers (-4527264/15625 : ℚ) vp0000000000100110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100110000_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110000-V-0000.bin"
noncomputable def vp0000000000100110000 : Blocks := vp0000000000100110000_0
theorem coverp0000000000100110000 : Covers (-4511639/15625 : ℚ) vp0000000000100110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010011000_0 : Blocks := edgeBlocks% "full/vectors/000000000010011000-V-0000.bin"
noncomputable def vp000000000010011000 : Blocks := vp000000000010011000_0
private theorem bp0000000000100110000 : Branch 0 (-4511639/31250 : ℚ) vp000000000010011000 := by
  apply branch_left_normalized (c:=vp0000000000100110000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4511639/31250 : ℚ) - ((0:ℤ):ℚ) = (-4511639/15625 : ℚ) by norm_num]
  exact coverp0000000000100110000
private noncomputable def ep0000000000100110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110001-E-0000.bin"
noncomputable def ep0000000000100110001 : Blocks := ep0000000000100110001_0
private theorem idp0000000000100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010011000.list =
    C ((2:ℤ)^32) * horner X vp0000000000100110001.list + horner X ep0000000000100110001.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100110001 : Branch 1 (-4511639/31250 : ℚ) vp000000000010011000 := by
  apply branch_checked idp0000000000100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-4511639/31250 : ℚ) - ((1:ℤ):ℚ) = (-4527264/15625 : ℚ) by norm_num]
  exact coverp0000000000100110001
theorem coverp000000000010011000 : Covers (-4511639/31250 : ℚ) vp000000000010011000 := join_branches bp0000000000100110000 bp0000000000100110001
private noncomputable def vp00000000001001100_0 : Blocks := edgeBlocks% "full/vectors/00000000001001100-V-0000.bin"
noncomputable def vp00000000001001100 : Blocks := vp00000000001001100_0
private theorem bp000000000010011000 : Branch 0 (-4511639/62500 : ℚ) vp00000000001001100 := by
  apply branch_left_normalized (c:=vp000000000010011000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-4511639/62500 : ℚ) - ((0:ℤ):ℚ) = (-4511639/31250 : ℚ) by norm_num]
  exact coverp000000000010011000
private noncomputable def ep000000000010011001_0 : Blocks := edgeBlocks% "full/vectors/000000000010011001-E-0000.bin"
noncomputable def ep000000000010011001 : Blocks := ep000000000010011001_0
private theorem idp000000000010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001001100.list =
    C ((2:ℤ)^49) * horner X vp000000000010011001.list + horner X ep000000000010011001.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010011001 : Branch 1 (-4511639/62500 : ℚ) vp00000000001001100 := by
  apply branch_checked idp000000000010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-4511639/62500 : ℚ) - ((1:ℤ):ℚ) = (-4542889/31250 : ℚ) by norm_num]
  exact coverp000000000010011001
theorem coverp00000000001001100 : Covers (-4511639/62500 : ℚ) vp00000000001001100 := join_branches bp000000000010011000 bp000000000010011001
private noncomputable def vp0000000000100110_0 : Blocks := edgeBlocks% "full/vectors/0000000000100110-V-0000.bin"
noncomputable def vp0000000000100110 : Blocks := vp0000000000100110_0
private theorem bp00000000001001100 : Branch 0 (-4511639/125000 : ℚ) vp0000000000100110 := by
  apply branch_left_normalized (c:=vp00000000001001100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-4511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-4511639/62500 : ℚ) by norm_num]
  exact coverp00000000001001100
private noncomputable def ep00000000001001101_0 : Blocks := edgeBlocks% "full/vectors/00000000001001101-E-0000.bin"
noncomputable def ep00000000001001101 : Blocks := ep00000000001001101_0
private theorem idp00000000001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100110.list =
    C ((2:ℤ)^79) * horner X vp00000000001001101.list + horner X ep00000000001001101.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001101 : Branch 1 (-4511639/125000 : ℚ) vp0000000000100110 := by
  apply branch_checked idp00000000001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-4574139/62500 : ℚ) by norm_num]
  exact coverp00000000001001101
theorem coverp0000000000100110 : Covers (-4511639/125000 : ℚ) vp0000000000100110 := join_branches bp00000000001001100 bp00000000001001101
private noncomputable def vp000000000010011_0 : Blocks := edgeBlocks% "full/vectors/000000000010011-V-0000.bin"
private noncomputable def vp000000000010011_1 : Blocks := edgeBlocks% "full/vectors/000000000010011-V-0001.bin"
noncomputable def vp000000000010011 : Blocks := (Blocks.join vp000000000010011_0 vp000000000010011_1)
private theorem bp0000000000100110 : Branch 0 (-4511639/250000 : ℚ) vp000000000010011 := by
  apply branch_left_normalized (c:=vp0000000000100110) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-4511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-4511639/125000 : ℚ) by norm_num]
  exact coverp0000000000100110
private noncomputable def ep0000000000100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100111-E-0000.bin"
private noncomputable def ep0000000000100111_1 : Blocks := edgeBlocks% "full/vectors/0000000000100111-E-0001.bin"
noncomputable def ep0000000000100111 : Blocks := (Blocks.join ep0000000000100111_0 ep0000000000100111_1)
private theorem idp0000000000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010011.list =
    C ((2:ℤ)^144) * horner X vp0000000000100111.list + horner X ep0000000000100111.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100111 : Branch 1 (-4511639/250000 : ℚ) vp000000000010011 := by
  apply branch_checked idp0000000000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-4511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-4636639/125000 : ℚ) by norm_num]
  exact coverp0000000000100111
theorem coverp000000000010011 : Covers (-4511639/250000 : ℚ) vp000000000010011 := join_branches bp0000000000100110 bp0000000000100111
private noncomputable def vp0000000000100101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101111-V-0000.bin"
noncomputable def vp0000000000100101111 : Blocks := vp0000000000100101111_0
theorem coverp0000000000100101111 : Covers (-4496014/15625 : ℚ) vp0000000000100101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100101110_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101110-V-0000.bin"
noncomputable def vp0000000000100101110 : Blocks := vp0000000000100101110_0
theorem coverp0000000000100101110 : Covers (-4480389/15625 : ℚ) vp0000000000100101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010010111_0 : Blocks := edgeBlocks% "full/vectors/000000000010010111-V-0000.bin"
noncomputable def vp000000000010010111 : Blocks := vp000000000010010111_0
private theorem bp0000000000100101110 : Branch 0 (-4480389/31250 : ℚ) vp000000000010010111 := by
  apply branch_left_normalized (c:=vp0000000000100101110) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4480389/31250 : ℚ) - ((0:ℤ):ℚ) = (-4480389/15625 : ℚ) by norm_num]
  exact coverp0000000000100101110
private noncomputable def ep0000000000100101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101111-E-0000.bin"
noncomputable def ep0000000000100101111 : Blocks := ep0000000000100101111_0
private theorem idp0000000000100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010010111.list =
    C ((2:ℤ)^33) * horner X vp0000000000100101111.list + horner X ep0000000000100101111.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100101111 : Branch 1 (-4480389/31250 : ℚ) vp000000000010010111 := by
  apply branch_checked idp0000000000100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-4480389/31250 : ℚ) - ((1:ℤ):ℚ) = (-4496014/15625 : ℚ) by norm_num]
  exact coverp0000000000100101111
theorem coverp000000000010010111 : Covers (-4480389/31250 : ℚ) vp000000000010010111 := join_branches bp0000000000100101110 bp0000000000100101111
private noncomputable def vp0000000000100101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101101-V-0000.bin"
noncomputable def vp0000000000100101101 : Blocks := vp0000000000100101101_0
theorem coverp0000000000100101101 : Covers (-4464764/15625 : ℚ) vp0000000000100101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001011001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001011001-V-0000.bin"
noncomputable def vp00000000001001011001 : Blocks := vp00000000001001011001_0
theorem coverp00000000001001011001 : Covers (-8913903/15625 : ℚ) vp00000000001001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001011000_0 : Blocks := edgeBlocks% "full/vectors/00000000001001011000-V-0000.bin"
noncomputable def vp00000000001001011000 : Blocks := vp00000000001001011000_0
theorem coverp00000000001001011000 : Covers (-8898278/15625 : ℚ) vp00000000001001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100101100_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101100-V-0000.bin"
noncomputable def vp0000000000100101100 : Blocks := vp0000000000100101100_0
private theorem bp00000000001001011000 : Branch 0 (-4449139/15625 : ℚ) vp0000000000100101100 := by
  apply branch_left_normalized (c:=vp00000000001001011000) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4449139/15625 : ℚ) - ((0:ℤ):ℚ) = (-8898278/15625 : ℚ) by norm_num]
  exact coverp00000000001001011000
private noncomputable def ep00000000001001011001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001011001-E-0000.bin"
noncomputable def ep00000000001001011001 : Blocks := ep00000000001001011001_0
private theorem idp00000000001001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100101100.list =
    C ((2:ℤ)^23) * horner X vp00000000001001011001.list + horner X ep00000000001001011001.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001011001 : Branch 1 (-4449139/15625 : ℚ) vp0000000000100101100 := by
  apply branch_checked idp00000000001001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-4449139/15625 : ℚ) - ((1:ℤ):ℚ) = (-8913903/15625 : ℚ) by norm_num]
  exact coverp00000000001001011001
theorem coverp0000000000100101100 : Covers (-4449139/15625 : ℚ) vp0000000000100101100 := join_branches bp00000000001001011000 bp00000000001001011001
private noncomputable def vp000000000010010110_0 : Blocks := edgeBlocks% "full/vectors/000000000010010110-V-0000.bin"
noncomputable def vp000000000010010110 : Blocks := vp000000000010010110_0
private theorem bp0000000000100101100 : Branch 0 (-4449139/31250 : ℚ) vp000000000010010110 := by
  apply branch_left_normalized (c:=vp0000000000100101100) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4449139/31250 : ℚ) - ((0:ℤ):ℚ) = (-4449139/15625 : ℚ) by norm_num]
  exact coverp0000000000100101100
private noncomputable def ep0000000000100101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101101-E-0000.bin"
noncomputable def ep0000000000100101101 : Blocks := ep0000000000100101101_0
private theorem idp0000000000100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010010110.list =
    C ((2:ℤ)^32) * horner X vp0000000000100101101.list + horner X ep0000000000100101101.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100101101 : Branch 1 (-4449139/31250 : ℚ) vp000000000010010110 := by
  apply branch_checked idp0000000000100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-4449139/31250 : ℚ) - ((1:ℤ):ℚ) = (-4464764/15625 : ℚ) by norm_num]
  exact coverp0000000000100101101
theorem coverp000000000010010110 : Covers (-4449139/31250 : ℚ) vp000000000010010110 := join_branches bp0000000000100101100 bp0000000000100101101
private noncomputable def vp00000000001001011_0 : Blocks := edgeBlocks% "full/vectors/00000000001001011-V-0000.bin"
noncomputable def vp00000000001001011 : Blocks := vp00000000001001011_0
private theorem bp000000000010010110 : Branch 0 (-4449139/62500 : ℚ) vp00000000001001011 := by
  apply branch_left_normalized (c:=vp000000000010010110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-4449139/62500 : ℚ) - ((0:ℤ):ℚ) = (-4449139/31250 : ℚ) by norm_num]
  exact coverp000000000010010110
private noncomputable def ep000000000010010111_0 : Blocks := edgeBlocks% "full/vectors/000000000010010111-E-0000.bin"
noncomputable def ep000000000010010111 : Blocks := ep000000000010010111_0
private theorem idp000000000010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001001011.list =
    C ((2:ℤ)^49) * horner X vp000000000010010111.list + horner X ep000000000010010111.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010010111 : Branch 1 (-4449139/62500 : ℚ) vp00000000001001011 := by
  apply branch_checked idp000000000010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-4449139/62500 : ℚ) - ((1:ℤ):ℚ) = (-4480389/31250 : ℚ) by norm_num]
  exact coverp000000000010010111
theorem coverp00000000001001011 : Covers (-4449139/62500 : ℚ) vp00000000001001011 := join_branches bp000000000010010110 bp000000000010010111
private noncomputable def vp0000000000100101011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101011-V-0000.bin"
noncomputable def vp0000000000100101011 : Blocks := vp0000000000100101011_0
theorem coverp0000000000100101011 : Covers (-4433514/15625 : ℚ) vp0000000000100101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100101010_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101010-V-0000.bin"
noncomputable def vp0000000000100101010 : Blocks := vp0000000000100101010_0
theorem coverp0000000000100101010 : Covers (-4417889/15625 : ℚ) vp0000000000100101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010010101_0 : Blocks := edgeBlocks% "full/vectors/000000000010010101-V-0000.bin"
noncomputable def vp000000000010010101 : Blocks := vp000000000010010101_0
private theorem bp0000000000100101010 : Branch 0 (-4417889/31250 : ℚ) vp000000000010010101 := by
  apply branch_left_normalized (c:=vp0000000000100101010) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-4417889/31250 : ℚ) - ((0:ℤ):ℚ) = (-4417889/15625 : ℚ) by norm_num]
  exact coverp0000000000100101010
private noncomputable def ep0000000000100101011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101011-E-0000.bin"
noncomputable def ep0000000000100101011 : Blocks := ep0000000000100101011_0
private theorem idp0000000000100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010010101.list =
    C ((2:ℤ)^34) * horner X vp0000000000100101011.list + horner X ep0000000000100101011.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100101011 : Branch 1 (-4417889/31250 : ℚ) vp000000000010010101 := by
  apply branch_checked idp0000000000100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-4417889/31250 : ℚ) - ((1:ℤ):ℚ) = (-4433514/15625 : ℚ) by norm_num]
  exact coverp0000000000100101011
theorem coverp000000000010010101 : Covers (-4417889/31250 : ℚ) vp000000000010010101 := join_branches bp0000000000100101010 bp0000000000100101011
private noncomputable def vp00000000001001010011_0 : Blocks := edgeBlocks% "full/vectors/00000000001001010011-V-0000.bin"
noncomputable def vp00000000001001010011 : Blocks := vp00000000001001010011_0
theorem coverp00000000001001010011 : Covers (-8820153/15625 : ℚ) vp00000000001001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001010010_0 : Blocks := edgeBlocks% "full/vectors/00000000001001010010-V-0000.bin"
noncomputable def vp00000000001001010010 : Blocks := vp00000000001001010010_0
theorem coverp00000000001001010010 : Covers (-8804528/15625 : ℚ) vp00000000001001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101001-V-0000.bin"
noncomputable def vp0000000000100101001 : Blocks := vp0000000000100101001_0
private theorem bp00000000001001010010 : Branch 0 (-4402264/15625 : ℚ) vp0000000000100101001 := by
  apply branch_left_normalized (c:=vp00000000001001010010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4402264/15625 : ℚ) - ((0:ℤ):ℚ) = (-8804528/15625 : ℚ) by norm_num]
  exact coverp00000000001001010010
private noncomputable def ep00000000001001010011_0 : Blocks := edgeBlocks% "full/vectors/00000000001001010011-E-0000.bin"
noncomputable def ep00000000001001010011 : Blocks := ep00000000001001010011_0
private theorem idp00000000001001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100101001.list =
    C ((2:ℤ)^23) * horner X vp00000000001001010011.list + horner X ep00000000001001010011.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001010011 : Branch 1 (-4402264/15625 : ℚ) vp0000000000100101001 := by
  apply branch_checked idp00000000001001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4402264/15625 : ℚ) - ((1:ℤ):ℚ) = (-8820153/15625 : ℚ) by norm_num]
  exact coverp00000000001001010011
theorem coverp0000000000100101001 : Covers (-4402264/15625 : ℚ) vp0000000000100101001 := join_branches bp00000000001001010010 bp00000000001001010011
private noncomputable def vp0000000000100101000_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101000-V-0000.bin"
noncomputable def vp0000000000100101000 : Blocks := vp0000000000100101000_0
theorem coverp0000000000100101000 : Covers (-4386639/15625 : ℚ) vp0000000000100101000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010010100_0 : Blocks := edgeBlocks% "full/vectors/000000000010010100-V-0000.bin"
noncomputable def vp000000000010010100 : Blocks := vp000000000010010100_0
private theorem bp0000000000100101000 : Branch 0 (-4386639/31250 : ℚ) vp000000000010010100 := by
  apply branch_left_normalized (c:=vp0000000000100101000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4386639/31250 : ℚ) - ((0:ℤ):ℚ) = (-4386639/15625 : ℚ) by norm_num]
  exact coverp0000000000100101000
private noncomputable def ep0000000000100101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101001-E-0000.bin"
noncomputable def ep0000000000100101001 : Blocks := ep0000000000100101001_0
private theorem idp0000000000100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010010100.list =
    C ((2:ℤ)^33) * horner X vp0000000000100101001.list + horner X ep0000000000100101001.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100101001 : Branch 1 (-4386639/31250 : ℚ) vp000000000010010100 := by
  apply branch_checked idp0000000000100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-4386639/31250 : ℚ) - ((1:ℤ):ℚ) = (-4402264/15625 : ℚ) by norm_num]
  exact coverp0000000000100101001
theorem coverp000000000010010100 : Covers (-4386639/31250 : ℚ) vp000000000010010100 := join_branches bp0000000000100101000 bp0000000000100101001
private noncomputable def vp00000000001001010_0 : Blocks := edgeBlocks% "full/vectors/00000000001001010-V-0000.bin"
noncomputable def vp00000000001001010 : Blocks := vp00000000001001010_0
private theorem bp000000000010010100 : Branch 0 (-4386639/62500 : ℚ) vp00000000001001010 := by
  apply branch_left_normalized (c:=vp000000000010010100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-4386639/62500 : ℚ) - ((0:ℤ):ℚ) = (-4386639/31250 : ℚ) by norm_num]
  exact coverp000000000010010100
private noncomputable def ep000000000010010101_0 : Blocks := edgeBlocks% "full/vectors/000000000010010101-E-0000.bin"
noncomputable def ep000000000010010101 : Blocks := ep000000000010010101_0
private theorem idp000000000010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001001010.list =
    C ((2:ℤ)^49) * horner X vp000000000010010101.list + horner X ep000000000010010101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010010101 : Branch 1 (-4386639/62500 : ℚ) vp00000000001001010 := by
  apply branch_checked idp000000000010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4386639/62500 : ℚ) - ((1:ℤ):ℚ) = (-4417889/31250 : ℚ) by norm_num]
  exact coverp000000000010010101
theorem coverp00000000001001010 : Covers (-4386639/62500 : ℚ) vp00000000001001010 := join_branches bp000000000010010100 bp000000000010010101
private noncomputable def vp0000000000100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101-V-0000.bin"
noncomputable def vp0000000000100101 : Blocks := vp0000000000100101_0
private theorem bp00000000001001010 : Branch 0 (-4386639/125000 : ℚ) vp0000000000100101 := by
  apply branch_left_normalized (c:=vp00000000001001010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-4386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-4386639/62500 : ℚ) by norm_num]
  exact coverp00000000001001010
private noncomputable def ep00000000001001011_0 : Blocks := edgeBlocks% "full/vectors/00000000001001011-E-0000.bin"
noncomputable def ep00000000001001011 : Blocks := ep00000000001001011_0
private theorem idp00000000001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100101.list =
    C ((2:ℤ)^80) * horner X vp00000000001001011.list + horner X ep00000000001001011.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001011 : Branch 1 (-4386639/125000 : ℚ) vp0000000000100101 := by
  apply branch_checked idp00000000001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-4449139/62500 : ℚ) by norm_num]
  exact coverp00000000001001011
theorem coverp0000000000100101 : Covers (-4386639/125000 : ℚ) vp0000000000100101 := join_branches bp00000000001001010 bp00000000001001011
private noncomputable def vp0000000000100100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100111-V-0000.bin"
noncomputable def vp0000000000100100111 : Blocks := vp0000000000100100111_0
theorem coverp0000000000100100111 : Covers (-4371014/15625 : ℚ) vp0000000000100100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001001101_0 : Blocks := edgeBlocks% "full/vectors/00000000001001001101-V-0000.bin"
noncomputable def vp00000000001001001101 : Blocks := vp00000000001001001101_0
theorem coverp00000000001001001101 : Covers (-8726403/15625 : ℚ) vp00000000001001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001001100_0 : Blocks := edgeBlocks% "full/vectors/00000000001001001100-V-0000.bin"
noncomputable def vp00000000001001001100 : Blocks := vp00000000001001001100_0
theorem coverp00000000001001001100 : Covers (-8710778/15625 : ℚ) vp00000000001001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100100110_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100110-V-0000.bin"
noncomputable def vp0000000000100100110 : Blocks := vp0000000000100100110_0
private theorem bp00000000001001001100 : Branch 0 (-4355389/15625 : ℚ) vp0000000000100100110 := by
  apply branch_left_normalized (c:=vp00000000001001001100) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4355389/15625 : ℚ) - ((0:ℤ):ℚ) = (-8710778/15625 : ℚ) by norm_num]
  exact coverp00000000001001001100
private noncomputable def ep00000000001001001101_0 : Blocks := edgeBlocks% "full/vectors/00000000001001001101-E-0000.bin"
noncomputable def ep00000000001001001101 : Blocks := ep00000000001001001101_0
private theorem idp00000000001001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100100110.list =
    C ((2:ℤ)^23) * horner X vp00000000001001001101.list + horner X ep00000000001001001101.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001001101 : Branch 1 (-4355389/15625 : ℚ) vp0000000000100100110 := by
  apply branch_checked idp00000000001001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4355389/15625 : ℚ) - ((1:ℤ):ℚ) = (-8726403/15625 : ℚ) by norm_num]
  exact coverp00000000001001001101
theorem coverp0000000000100100110 : Covers (-4355389/15625 : ℚ) vp0000000000100100110 := join_branches bp00000000001001001100 bp00000000001001001101
private noncomputable def vp000000000010010011_0 : Blocks := edgeBlocks% "full/vectors/000000000010010011-V-0000.bin"
noncomputable def vp000000000010010011 : Blocks := vp000000000010010011_0
private theorem bp0000000000100100110 : Branch 0 (-4355389/31250 : ℚ) vp000000000010010011 := by
  apply branch_left_normalized (c:=vp0000000000100100110) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4355389/31250 : ℚ) - ((0:ℤ):ℚ) = (-4355389/15625 : ℚ) by norm_num]
  exact coverp0000000000100100110
private noncomputable def ep0000000000100100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100111-E-0000.bin"
noncomputable def ep0000000000100100111 : Blocks := ep0000000000100100111_0
private theorem idp0000000000100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010010011.list =
    C ((2:ℤ)^33) * horner X vp0000000000100100111.list + horner X ep0000000000100100111.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100100111 : Branch 1 (-4355389/31250 : ℚ) vp000000000010010011 := by
  apply branch_checked idp0000000000100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-4355389/31250 : ℚ) - ((1:ℤ):ℚ) = (-4371014/15625 : ℚ) by norm_num]
  exact coverp0000000000100100111
theorem coverp000000000010010011 : Covers (-4355389/31250 : ℚ) vp000000000010010011 := join_branches bp0000000000100100110 bp0000000000100100111
private noncomputable def vp0000000000100100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100101-V-0000.bin"
noncomputable def vp0000000000100100101 : Blocks := vp0000000000100100101_0
theorem coverp0000000000100100101 : Covers (-4339764/15625 : ℚ) vp0000000000100100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001001001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001001001-V-0000.bin"
noncomputable def vp00000000001001001001 : Blocks := vp00000000001001001001_0
theorem coverp00000000001001001001 : Covers (-8663903/15625 : ℚ) vp00000000001001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001001000_0 : Blocks := edgeBlocks% "full/vectors/00000000001001001000-V-0000.bin"
noncomputable def vp00000000001001001000 : Blocks := vp00000000001001001000_0
theorem coverp00000000001001001000 : Covers (-8648278/15625 : ℚ) vp00000000001001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100100100_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100100-V-0000.bin"
noncomputable def vp0000000000100100100 : Blocks := vp0000000000100100100_0
private theorem bp00000000001001001000 : Branch 0 (-4324139/15625 : ℚ) vp0000000000100100100 := by
  apply branch_left_normalized (c:=vp00000000001001001000) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4324139/15625 : ℚ) - ((0:ℤ):ℚ) = (-8648278/15625 : ℚ) by norm_num]
  exact coverp00000000001001001000
private noncomputable def ep00000000001001001001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001001001-E-0000.bin"
noncomputable def ep00000000001001001001 : Blocks := ep00000000001001001001_0
private theorem idp00000000001001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100100100.list =
    C ((2:ℤ)^24) * horner X vp00000000001001001001.list + horner X ep00000000001001001001.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001001001 : Branch 1 (-4324139/15625 : ℚ) vp0000000000100100100 := by
  apply branch_checked idp00000000001001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4324139/15625 : ℚ) - ((1:ℤ):ℚ) = (-8663903/15625 : ℚ) by norm_num]
  exact coverp00000000001001001001
theorem coverp0000000000100100100 : Covers (-4324139/15625 : ℚ) vp0000000000100100100 := join_branches bp00000000001001001000 bp00000000001001001001
private noncomputable def vp000000000010010010_0 : Blocks := edgeBlocks% "full/vectors/000000000010010010-V-0000.bin"
noncomputable def vp000000000010010010 : Blocks := vp000000000010010010_0
private theorem bp0000000000100100100 : Branch 0 (-4324139/31250 : ℚ) vp000000000010010010 := by
  apply branch_left_normalized (c:=vp0000000000100100100) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-4324139/31250 : ℚ) - ((0:ℤ):ℚ) = (-4324139/15625 : ℚ) by norm_num]
  exact coverp0000000000100100100
private noncomputable def ep0000000000100100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100101-E-0000.bin"
noncomputable def ep0000000000100100101 : Blocks := ep0000000000100100101_0
private theorem idp0000000000100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010010010.list =
    C ((2:ℤ)^34) * horner X vp0000000000100100101.list + horner X ep0000000000100100101.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100100101 : Branch 1 (-4324139/31250 : ℚ) vp000000000010010010 := by
  apply branch_checked idp0000000000100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-4324139/31250 : ℚ) - ((1:ℤ):ℚ) = (-4339764/15625 : ℚ) by norm_num]
  exact coverp0000000000100100101
theorem coverp000000000010010010 : Covers (-4324139/31250 : ℚ) vp000000000010010010 := join_branches bp0000000000100100100 bp0000000000100100101
private noncomputable def vp00000000001001001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001001-V-0000.bin"
noncomputable def vp00000000001001001 : Blocks := vp00000000001001001_0
private theorem bp000000000010010010 : Branch 0 (-4324139/62500 : ℚ) vp00000000001001001 := by
  apply branch_left_normalized (c:=vp000000000010010010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-4324139/62500 : ℚ) - ((0:ℤ):ℚ) = (-4324139/31250 : ℚ) by norm_num]
  exact coverp000000000010010010
private noncomputable def ep000000000010010011_0 : Blocks := edgeBlocks% "full/vectors/000000000010010011-E-0000.bin"
noncomputable def ep000000000010010011 : Blocks := ep000000000010010011_0
private theorem idp000000000010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001001001.list =
    C ((2:ℤ)^50) * horner X vp000000000010010011.list + horner X ep000000000010010011.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010010011 : Branch 1 (-4324139/62500 : ℚ) vp00000000001001001 := by
  apply branch_checked idp000000000010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4324139/62500 : ℚ) - ((1:ℤ):ℚ) = (-4355389/31250 : ℚ) by norm_num]
  exact coverp000000000010010011
theorem coverp00000000001001001 : Covers (-4324139/62500 : ℚ) vp00000000001001001 := join_branches bp000000000010010010 bp000000000010010011
private noncomputable def vp00000000001001000111_0 : Blocks := edgeBlocks% "full/vectors/00000000001001000111-V-0000.bin"
noncomputable def vp00000000001001000111 : Blocks := vp00000000001001000111_0
theorem coverp00000000001001000111 : Covers (-8632653/15625 : ℚ) vp00000000001001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001000110_0 : Blocks := edgeBlocks% "full/vectors/00000000001001000110-V-0000.bin"
noncomputable def vp00000000001001000110 : Blocks := vp00000000001001000110_0
theorem coverp00000000001001000110 : Covers (-8617028/15625 : ℚ) vp00000000001001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100011-V-0000.bin"
noncomputable def vp0000000000100100011 : Blocks := vp0000000000100100011_0
private theorem bp00000000001001000110 : Branch 0 (-4308514/15625 : ℚ) vp0000000000100100011 := by
  apply branch_left_normalized (c:=vp00000000001001000110) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4308514/15625 : ℚ) - ((0:ℤ):ℚ) = (-8617028/15625 : ℚ) by norm_num]
  exact coverp00000000001001000110
private noncomputable def ep00000000001001000111_0 : Blocks := edgeBlocks% "full/vectors/00000000001001000111-E-0000.bin"
noncomputable def ep00000000001001000111 : Blocks := ep00000000001001000111_0
private theorem idp00000000001001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100100011.list =
    C ((2:ℤ)^23) * horner X vp00000000001001000111.list + horner X ep00000000001001000111.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001000111 : Branch 1 (-4308514/15625 : ℚ) vp0000000000100100011 := by
  apply branch_checked idp00000000001001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4308514/15625 : ℚ) - ((1:ℤ):ℚ) = (-8632653/15625 : ℚ) by norm_num]
  exact coverp00000000001001000111
theorem coverp0000000000100100011 : Covers (-4308514/15625 : ℚ) vp0000000000100100011 := join_branches bp00000000001001000110 bp00000000001001000111
private noncomputable def vp0000000000100100010_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100010-V-0000.bin"
noncomputable def vp0000000000100100010 : Blocks := vp0000000000100100010_0
theorem coverp0000000000100100010 : Covers (-4292889/15625 : ℚ) vp0000000000100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010010001_0 : Blocks := edgeBlocks% "full/vectors/000000000010010001-V-0000.bin"
noncomputable def vp000000000010010001 : Blocks := vp000000000010010001_0
private theorem bp0000000000100100010 : Branch 0 (-4292889/31250 : ℚ) vp000000000010010001 := by
  apply branch_left_normalized (c:=vp0000000000100100010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4292889/31250 : ℚ) - ((0:ℤ):ℚ) = (-4292889/15625 : ℚ) by norm_num]
  exact coverp0000000000100100010
private noncomputable def ep0000000000100100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100011-E-0000.bin"
noncomputable def ep0000000000100100011 : Blocks := ep0000000000100100011_0
private theorem idp0000000000100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010010001.list =
    C ((2:ℤ)^33) * horner X vp0000000000100100011.list + horner X ep0000000000100100011.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100100011 : Branch 1 (-4292889/31250 : ℚ) vp000000000010010001 := by
  apply branch_checked idp0000000000100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-4292889/31250 : ℚ) - ((1:ℤ):ℚ) = (-4308514/15625 : ℚ) by norm_num]
  exact coverp0000000000100100011
theorem coverp000000000010010001 : Covers (-4292889/31250 : ℚ) vp000000000010010001 := join_branches bp0000000000100100010 bp0000000000100100011
private noncomputable def vp00000000001001000011_0 : Blocks := edgeBlocks% "full/vectors/00000000001001000011-V-0000.bin"
noncomputable def vp00000000001001000011 : Blocks := vp00000000001001000011_0
theorem coverp00000000001001000011 : Covers (-8570153/15625 : ℚ) vp00000000001001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001000010_0 : Blocks := edgeBlocks% "full/vectors/00000000001001000010-V-0000.bin"
noncomputable def vp00000000001001000010 : Blocks := vp00000000001001000010_0
theorem coverp00000000001001000010 : Covers (-8554528/15625 : ℚ) vp00000000001001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100001-V-0000.bin"
noncomputable def vp0000000000100100001 : Blocks := vp0000000000100100001_0
private theorem bp00000000001001000010 : Branch 0 (-4277264/15625 : ℚ) vp0000000000100100001 := by
  apply branch_left_normalized (c:=vp00000000001001000010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4277264/15625 : ℚ) - ((0:ℤ):ℚ) = (-8554528/15625 : ℚ) by norm_num]
  exact coverp00000000001001000010
private noncomputable def ep00000000001001000011_0 : Blocks := edgeBlocks% "full/vectors/00000000001001000011-E-0000.bin"
noncomputable def ep00000000001001000011 : Blocks := ep00000000001001000011_0
private theorem idp00000000001001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100100001.list =
    C ((2:ℤ)^24) * horner X vp00000000001001000011.list + horner X ep00000000001001000011.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001000011 : Branch 1 (-4277264/15625 : ℚ) vp0000000000100100001 := by
  apply branch_checked idp00000000001001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-4277264/15625 : ℚ) - ((1:ℤ):ℚ) = (-8570153/15625 : ℚ) by norm_num]
  exact coverp00000000001001000011
theorem coverp0000000000100100001 : Covers (-4277264/15625 : ℚ) vp0000000000100100001 := join_branches bp00000000001001000010 bp00000000001001000011
private noncomputable def vp00000000001001000001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001000001-V-0000.bin"
noncomputable def vp00000000001001000001 : Blocks := vp00000000001001000001_0
theorem coverp00000000001001000001 : Covers (-8538903/15625 : ℚ) vp00000000001001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001001000000_0 : Blocks := edgeBlocks% "full/vectors/00000000001001000000-V-0000.bin"
noncomputable def vp00000000001001000000 : Blocks := vp00000000001001000000_0
theorem coverp00000000001001000000 : Covers (-8523278/15625 : ℚ) vp00000000001001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100100000_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100000-V-0000.bin"
noncomputable def vp0000000000100100000 : Blocks := vp0000000000100100000_0
private theorem bp00000000001001000000 : Branch 0 (-4261639/15625 : ℚ) vp0000000000100100000 := by
  apply branch_left_normalized (c:=vp00000000001001000000) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4261639/15625 : ℚ) - ((0:ℤ):ℚ) = (-8523278/15625 : ℚ) by norm_num]
  exact coverp00000000001001000000
private noncomputable def ep00000000001001000001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001000001-E-0000.bin"
noncomputable def ep00000000001001000001 : Blocks := ep00000000001001000001_0
private theorem idp00000000001001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100100000.list =
    C ((2:ℤ)^23) * horner X vp00000000001001000001.list + horner X ep00000000001001000001.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001000001 : Branch 1 (-4261639/15625 : ℚ) vp0000000000100100000 := by
  apply branch_checked idp00000000001001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-4261639/15625 : ℚ) - ((1:ℤ):ℚ) = (-8538903/15625 : ℚ) by norm_num]
  exact coverp00000000001001000001
theorem coverp0000000000100100000 : Covers (-4261639/15625 : ℚ) vp0000000000100100000 := join_branches bp00000000001001000000 bp00000000001001000001
private noncomputable def vp000000000010010000_0 : Blocks := edgeBlocks% "full/vectors/000000000010010000-V-0000.bin"
noncomputable def vp000000000010010000 : Blocks := vp000000000010010000_0
private theorem bp0000000000100100000 : Branch 0 (-4261639/31250 : ℚ) vp000000000010010000 := by
  apply branch_left_normalized (c:=vp0000000000100100000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4261639/31250 : ℚ) - ((0:ℤ):ℚ) = (-4261639/15625 : ℚ) by norm_num]
  exact coverp0000000000100100000
private noncomputable def ep0000000000100100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100001-E-0000.bin"
noncomputable def ep0000000000100100001 : Blocks := ep0000000000100100001_0
private theorem idp0000000000100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010010000.list =
    C ((2:ℤ)^33) * horner X vp0000000000100100001.list + horner X ep0000000000100100001.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100100001 : Branch 1 (-4261639/31250 : ℚ) vp000000000010010000 := by
  apply branch_checked idp0000000000100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-4261639/31250 : ℚ) - ((1:ℤ):ℚ) = (-4277264/15625 : ℚ) by norm_num]
  exact coverp0000000000100100001
theorem coverp000000000010010000 : Covers (-4261639/31250 : ℚ) vp000000000010010000 := join_branches bp0000000000100100000 bp0000000000100100001
private noncomputable def vp00000000001001000_0 : Blocks := edgeBlocks% "full/vectors/00000000001001000-V-0000.bin"
noncomputable def vp00000000001001000 : Blocks := vp00000000001001000_0
private theorem bp000000000010010000 : Branch 0 (-4261639/62500 : ℚ) vp00000000001001000 := by
  apply branch_left_normalized (c:=vp000000000010010000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-4261639/62500 : ℚ) - ((0:ℤ):ℚ) = (-4261639/31250 : ℚ) by norm_num]
  exact coverp000000000010010000
private noncomputable def ep000000000010010001_0 : Blocks := edgeBlocks% "full/vectors/000000000010010001-E-0000.bin"
noncomputable def ep000000000010010001 : Blocks := ep000000000010010001_0
private theorem idp000000000010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001001000.list =
    C ((2:ℤ)^50) * horner X vp000000000010010001.list + horner X ep000000000010010001.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010010001 : Branch 1 (-4261639/62500 : ℚ) vp00000000001001000 := by
  apply branch_checked idp000000000010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4261639/62500 : ℚ) - ((1:ℤ):ℚ) = (-4292889/31250 : ℚ) by norm_num]
  exact coverp000000000010010001
theorem coverp00000000001001000 : Covers (-4261639/62500 : ℚ) vp00000000001001000 := join_branches bp000000000010010000 bp000000000010010001
private noncomputable def vp0000000000100100_0 : Blocks := edgeBlocks% "full/vectors/0000000000100100-V-0000.bin"
noncomputable def vp0000000000100100 : Blocks := vp0000000000100100_0
private theorem bp00000000001001000 : Branch 0 (-4261639/125000 : ℚ) vp0000000000100100 := by
  apply branch_left_normalized (c:=vp00000000001001000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-4261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-4261639/62500 : ℚ) by norm_num]
  exact coverp00000000001001000
private noncomputable def ep00000000001001001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001001-E-0000.bin"
noncomputable def ep00000000001001001 : Blocks := ep00000000001001001_0
private theorem idp00000000001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100100.list =
    C ((2:ℤ)^80) * horner X vp00000000001001001.list + horner X ep00000000001001001.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001001 : Branch 1 (-4261639/125000 : ℚ) vp0000000000100100 := by
  apply branch_checked idp00000000001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-4324139/62500 : ℚ) by norm_num]
  exact coverp00000000001001001
theorem coverp0000000000100100 : Covers (-4261639/125000 : ℚ) vp0000000000100100 := join_branches bp00000000001001000 bp00000000001001001
private noncomputable def vp000000000010010_0 : Blocks := edgeBlocks% "full/vectors/000000000010010-V-0000.bin"
private noncomputable def vp000000000010010_1 : Blocks := edgeBlocks% "full/vectors/000000000010010-V-0001.bin"
noncomputable def vp000000000010010 : Blocks := (Blocks.join vp000000000010010_0 vp000000000010010_1)
private theorem bp0000000000100100 : Branch 0 (-4261639/250000 : ℚ) vp000000000010010 := by
  apply branch_left_normalized (c:=vp0000000000100100) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-4261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-4261639/125000 : ℚ) by norm_num]
  exact coverp0000000000100100
private noncomputable def ep0000000000100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100101-E-0000.bin"
private noncomputable def ep0000000000100101_1 : Blocks := edgeBlocks% "full/vectors/0000000000100101-E-0001.bin"
noncomputable def ep0000000000100101 : Blocks := (Blocks.join ep0000000000100101_0 ep0000000000100101_1)
private theorem idp0000000000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010010.list =
    C ((2:ℤ)^140) * horner X vp0000000000100101.list + horner X ep0000000000100101.list := by
  exact edge_identity (B := (2:ℤ)^298) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100101 : Branch 1 (-4261639/250000 : ℚ) vp000000000010010 := by
  apply branch_checked idp0000000000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-4261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-4386639/125000 : ℚ) by norm_num]
  exact coverp0000000000100101
theorem coverp000000000010010 : Covers (-4261639/250000 : ℚ) vp000000000010010 := join_branches bp0000000000100100 bp0000000000100101
private noncomputable def vp00000000001001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001-V-0000.bin"
private noncomputable def vp00000000001001_1 : Blocks := edgeBlocks% "full/vectors/00000000001001-V-0001.bin"
private noncomputable def vp00000000001001_2 : Blocks := edgeBlocks% "full/vectors/00000000001001-V-0002.bin"
noncomputable def vp00000000001001 : Blocks := (Blocks.join vp00000000001001_0 (Blocks.join vp00000000001001_1 vp00000000001001_2))
private theorem bp000000000010010 : Branch 0 (-4261639/500000 : ℚ) vp00000000001001 := by
  apply branch_left_normalized (c:=vp000000000010010) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-4261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-4261639/250000 : ℚ) by norm_num]
  exact coverp000000000010010
private noncomputable def ep000000000010011_0 : Blocks := edgeBlocks% "full/vectors/000000000010011-E-0000.bin"
private noncomputable def ep000000000010011_1 : Blocks := edgeBlocks% "full/vectors/000000000010011-E-0001.bin"
private noncomputable def ep000000000010011_2 : Blocks := edgeBlocks% "full/vectors/000000000010011-E-0002.bin"
noncomputable def ep000000000010011 : Blocks := (Blocks.join ep000000000010011_0 (Blocks.join ep000000000010011_1 ep000000000010011_2))
private theorem idp000000000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001001.list =
    C ((2:ℤ)^279) * horner X vp000000000010011.list + horner X ep000000000010011.list := by
  exact edge_identity (B := (2:ℤ)^498) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010011 : Branch 1 (-4261639/500000 : ℚ) vp00000000001001 := by
  apply branch_checked idp000000000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-4511639/250000 : ℚ) by norm_num]
  exact coverp000000000010011
theorem coverp00000000001001 : Covers (-4261639/500000 : ℚ) vp00000000001001 := join_branches bp000000000010010 bp000000000010011
private noncomputable def vp0000000000100011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011111-V-0000.bin"
noncomputable def vp0000000000100011111 : Blocks := vp0000000000100011111_0
theorem coverp0000000000100011111 : Covers (-4246014/15625 : ℚ) vp0000000000100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000111101_0 : Blocks := edgeBlocks% "full/vectors/00000000001000111101-V-0000.bin"
noncomputable def vp00000000001000111101 : Blocks := vp00000000001000111101_0
theorem coverp00000000001000111101 : Covers (-8476403/15625 : ℚ) vp00000000001000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000111100_0 : Blocks := edgeBlocks% "full/vectors/00000000001000111100-V-0000.bin"
noncomputable def vp00000000001000111100 : Blocks := vp00000000001000111100_0
theorem coverp00000000001000111100 : Covers (-8460778/15625 : ℚ) vp00000000001000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100011110_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011110-V-0000.bin"
noncomputable def vp0000000000100011110 : Blocks := vp0000000000100011110_0
private theorem bp00000000001000111100 : Branch 0 (-4230389/15625 : ℚ) vp0000000000100011110 := by
  apply branch_left_normalized (c:=vp00000000001000111100) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4230389/15625 : ℚ) - ((0:ℤ):ℚ) = (-8460778/15625 : ℚ) by norm_num]
  exact coverp00000000001000111100
private noncomputable def ep00000000001000111101_0 : Blocks := edgeBlocks% "full/vectors/00000000001000111101-E-0000.bin"
noncomputable def ep00000000001000111101 : Blocks := ep00000000001000111101_0
private theorem idp00000000001000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100011110.list =
    C ((2:ℤ)^24) * horner X vp00000000001000111101.list + horner X ep00000000001000111101.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000111101 : Branch 1 (-4230389/15625 : ℚ) vp0000000000100011110 := by
  apply branch_checked idp00000000001000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-4230389/15625 : ℚ) - ((1:ℤ):ℚ) = (-8476403/15625 : ℚ) by norm_num]
  exact coverp00000000001000111101
theorem coverp0000000000100011110 : Covers (-4230389/15625 : ℚ) vp0000000000100011110 := join_branches bp00000000001000111100 bp00000000001000111101
private noncomputable def vp000000000010001111_0 : Blocks := edgeBlocks% "full/vectors/000000000010001111-V-0000.bin"
noncomputable def vp000000000010001111 : Blocks := vp000000000010001111_0
private theorem bp0000000000100011110 : Branch 0 (-4230389/31250 : ℚ) vp000000000010001111 := by
  apply branch_left_normalized (c:=vp0000000000100011110) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-4230389/31250 : ℚ) - ((0:ℤ):ℚ) = (-4230389/15625 : ℚ) by norm_num]
  exact coverp0000000000100011110
private noncomputable def ep0000000000100011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011111-E-0000.bin"
noncomputable def ep0000000000100011111 : Blocks := ep0000000000100011111_0
private theorem idp0000000000100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010001111.list =
    C ((2:ℤ)^34) * horner X vp0000000000100011111.list + horner X ep0000000000100011111.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100011111 : Branch 1 (-4230389/31250 : ℚ) vp000000000010001111 := by
  apply branch_checked idp0000000000100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-4230389/31250 : ℚ) - ((1:ℤ):ℚ) = (-4246014/15625 : ℚ) by norm_num]
  exact coverp0000000000100011111
theorem coverp000000000010001111 : Covers (-4230389/31250 : ℚ) vp000000000010001111 := join_branches bp0000000000100011110 bp0000000000100011111
private noncomputable def vp00000000001000111011_0 : Blocks := edgeBlocks% "full/vectors/00000000001000111011-V-0000.bin"
noncomputable def vp00000000001000111011 : Blocks := vp00000000001000111011_0
theorem coverp00000000001000111011 : Covers (-8445153/15625 : ℚ) vp00000000001000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000111010_0 : Blocks := edgeBlocks% "full/vectors/00000000001000111010-V-0000.bin"
noncomputable def vp00000000001000111010 : Blocks := vp00000000001000111010_0
theorem coverp00000000001000111010 : Covers (-8429528/15625 : ℚ) vp00000000001000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011101-V-0000.bin"
noncomputable def vp0000000000100011101 : Blocks := vp0000000000100011101_0
private theorem bp00000000001000111010 : Branch 0 (-4214764/15625 : ℚ) vp0000000000100011101 := by
  apply branch_left_normalized (c:=vp00000000001000111010) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4214764/15625 : ℚ) - ((0:ℤ):ℚ) = (-8429528/15625 : ℚ) by norm_num]
  exact coverp00000000001000111010
private noncomputable def ep00000000001000111011_0 : Blocks := edgeBlocks% "full/vectors/00000000001000111011-E-0000.bin"
noncomputable def ep00000000001000111011 : Blocks := ep00000000001000111011_0
private theorem idp00000000001000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100011101.list =
    C ((2:ℤ)^24) * horner X vp00000000001000111011.list + horner X ep00000000001000111011.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000111011 : Branch 1 (-4214764/15625 : ℚ) vp0000000000100011101 := by
  apply branch_checked idp00000000001000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-4214764/15625 : ℚ) - ((1:ℤ):ℚ) = (-8445153/15625 : ℚ) by norm_num]
  exact coverp00000000001000111011
theorem coverp0000000000100011101 : Covers (-4214764/15625 : ℚ) vp0000000000100011101 := join_branches bp00000000001000111010 bp00000000001000111011
private noncomputable def vp0000000000100011100_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011100-V-0000.bin"
noncomputable def vp0000000000100011100 : Blocks := vp0000000000100011100_0
theorem coverp0000000000100011100 : Covers (-4199139/15625 : ℚ) vp0000000000100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010001110_0 : Blocks := edgeBlocks% "full/vectors/000000000010001110-V-0000.bin"
noncomputable def vp000000000010001110 : Blocks := vp000000000010001110_0
private theorem bp0000000000100011100 : Branch 0 (-4199139/31250 : ℚ) vp000000000010001110 := by
  apply branch_left_normalized (c:=vp0000000000100011100) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4199139/31250 : ℚ) - ((0:ℤ):ℚ) = (-4199139/15625 : ℚ) by norm_num]
  exact coverp0000000000100011100
private noncomputable def ep0000000000100011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011101-E-0000.bin"
noncomputable def ep0000000000100011101 : Blocks := ep0000000000100011101_0
private theorem idp0000000000100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010001110.list =
    C ((2:ℤ)^33) * horner X vp0000000000100011101.list + horner X ep0000000000100011101.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100011101 : Branch 1 (-4199139/31250 : ℚ) vp000000000010001110 := by
  apply branch_checked idp0000000000100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-4199139/31250 : ℚ) - ((1:ℤ):ℚ) = (-4214764/15625 : ℚ) by norm_num]
  exact coverp0000000000100011101
theorem coverp000000000010001110 : Covers (-4199139/31250 : ℚ) vp000000000010001110 := join_branches bp0000000000100011100 bp0000000000100011101
private noncomputable def vp00000000001000111_0 : Blocks := edgeBlocks% "full/vectors/00000000001000111-V-0000.bin"
noncomputable def vp00000000001000111 : Blocks := vp00000000001000111_0
private theorem bp000000000010001110 : Branch 0 (-4199139/62500 : ℚ) vp00000000001000111 := by
  apply branch_left_normalized (c:=vp000000000010001110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-4199139/62500 : ℚ) - ((0:ℤ):ℚ) = (-4199139/31250 : ℚ) by norm_num]
  exact coverp000000000010001110
private noncomputable def ep000000000010001111_0 : Blocks := edgeBlocks% "full/vectors/000000000010001111-E-0000.bin"
noncomputable def ep000000000010001111 : Blocks := ep000000000010001111_0
private theorem idp000000000010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000111.list =
    C ((2:ℤ)^51) * horner X vp000000000010001111.list + horner X ep000000000010001111.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010001111 : Branch 1 (-4199139/62500 : ℚ) vp00000000001000111 := by
  apply branch_checked idp000000000010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4199139/62500 : ℚ) - ((1:ℤ):ℚ) = (-4230389/31250 : ℚ) by norm_num]
  exact coverp000000000010001111
theorem coverp00000000001000111 : Covers (-4199139/62500 : ℚ) vp00000000001000111 := join_branches bp000000000010001110 bp000000000010001111
private noncomputable def vp00000000001000110111_0 : Blocks := edgeBlocks% "full/vectors/00000000001000110111-V-0000.bin"
noncomputable def vp00000000001000110111 : Blocks := vp00000000001000110111_0
theorem coverp00000000001000110111 : Covers (-8382653/15625 : ℚ) vp00000000001000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000110110_0 : Blocks := edgeBlocks% "full/vectors/00000000001000110110-V-0000.bin"
noncomputable def vp00000000001000110110 : Blocks := vp00000000001000110110_0
theorem coverp00000000001000110110 : Covers (-8367028/15625 : ℚ) vp00000000001000110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011011-V-0000.bin"
noncomputable def vp0000000000100011011 : Blocks := vp0000000000100011011_0
private theorem bp00000000001000110110 : Branch 0 (-4183514/15625 : ℚ) vp0000000000100011011 := by
  apply branch_left_normalized (c:=vp00000000001000110110) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4183514/15625 : ℚ) - ((0:ℤ):ℚ) = (-8367028/15625 : ℚ) by norm_num]
  exact coverp00000000001000110110
private noncomputable def ep00000000001000110111_0 : Blocks := edgeBlocks% "full/vectors/00000000001000110111-E-0000.bin"
noncomputable def ep00000000001000110111 : Blocks := ep00000000001000110111_0
private theorem idp00000000001000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100011011.list =
    C ((2:ℤ)^24) * horner X vp00000000001000110111.list + horner X ep00000000001000110111.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000110111 : Branch 1 (-4183514/15625 : ℚ) vp0000000000100011011 := by
  apply branch_checked idp00000000001000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-4183514/15625 : ℚ) - ((1:ℤ):ℚ) = (-8382653/15625 : ℚ) by norm_num]
  exact coverp00000000001000110111
theorem coverp0000000000100011011 : Covers (-4183514/15625 : ℚ) vp0000000000100011011 := join_branches bp00000000001000110110 bp00000000001000110111
private noncomputable def vp0000000000100011010_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011010-V-0000.bin"
noncomputable def vp0000000000100011010 : Blocks := vp0000000000100011010_0
theorem coverp0000000000100011010 : Covers (-4167889/15625 : ℚ) vp0000000000100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010001101_0 : Blocks := edgeBlocks% "full/vectors/000000000010001101-V-0000.bin"
noncomputable def vp000000000010001101 : Blocks := vp000000000010001101_0
private theorem bp0000000000100011010 : Branch 0 (-4167889/31250 : ℚ) vp000000000010001101 := by
  apply branch_left_normalized (c:=vp0000000000100011010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4167889/31250 : ℚ) - ((0:ℤ):ℚ) = (-4167889/15625 : ℚ) by norm_num]
  exact coverp0000000000100011010
private noncomputable def ep0000000000100011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011011-E-0000.bin"
noncomputable def ep0000000000100011011 : Blocks := ep0000000000100011011_0
private theorem idp0000000000100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010001101.list =
    C ((2:ℤ)^33) * horner X vp0000000000100011011.list + horner X ep0000000000100011011.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100011011 : Branch 1 (-4167889/31250 : ℚ) vp000000000010001101 := by
  apply branch_checked idp0000000000100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-4167889/31250 : ℚ) - ((1:ℤ):ℚ) = (-4183514/15625 : ℚ) by norm_num]
  exact coverp0000000000100011011
theorem coverp000000000010001101 : Covers (-4167889/31250 : ℚ) vp000000000010001101 := join_branches bp0000000000100011010 bp0000000000100011011
private noncomputable def vp0000000000100011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011001-V-0000.bin"
noncomputable def vp0000000000100011001 : Blocks := vp0000000000100011001_0
theorem coverp0000000000100011001 : Covers (-4152264/15625 : ℚ) vp0000000000100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000110001_0 : Blocks := edgeBlocks% "full/vectors/00000000001000110001-V-0000.bin"
noncomputable def vp00000000001000110001 : Blocks := vp00000000001000110001_0
theorem coverp00000000001000110001 : Covers (-8288903/15625 : ℚ) vp00000000001000110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000110000_0 : Blocks := edgeBlocks% "full/vectors/00000000001000110000-V-0000.bin"
noncomputable def vp00000000001000110000 : Blocks := vp00000000001000110000_0
theorem coverp00000000001000110000 : Covers (-8273278/15625 : ℚ) vp00000000001000110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100011000_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011000-V-0000.bin"
noncomputable def vp0000000000100011000 : Blocks := vp0000000000100011000_0
private theorem bp00000000001000110000 : Branch 0 (-4136639/15625 : ℚ) vp0000000000100011000 := by
  apply branch_left_normalized (c:=vp00000000001000110000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4136639/15625 : ℚ) - ((0:ℤ):ℚ) = (-8273278/15625 : ℚ) by norm_num]
  exact coverp00000000001000110000
private noncomputable def ep00000000001000110001_0 : Blocks := edgeBlocks% "full/vectors/00000000001000110001-E-0000.bin"
noncomputable def ep00000000001000110001 : Blocks := ep00000000001000110001_0
private theorem idp00000000001000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100011000.list =
    C ((2:ℤ)^24) * horner X vp00000000001000110001.list + horner X ep00000000001000110001.list := by
  exact edge_identity (B := (2:ℤ)^127) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000110001 : Branch 1 (-4136639/15625 : ℚ) vp0000000000100011000 := by
  apply branch_checked idp00000000001000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-4136639/15625 : ℚ) - ((1:ℤ):ℚ) = (-8288903/15625 : ℚ) by norm_num]
  exact coverp00000000001000110001
theorem coverp0000000000100011000 : Covers (-4136639/15625 : ℚ) vp0000000000100011000 := join_branches bp00000000001000110000 bp00000000001000110001
private noncomputable def vp000000000010001100_0 : Blocks := edgeBlocks% "full/vectors/000000000010001100-V-0000.bin"
noncomputable def vp000000000010001100 : Blocks := vp000000000010001100_0
private theorem bp0000000000100011000 : Branch 0 (-4136639/31250 : ℚ) vp000000000010001100 := by
  apply branch_left_normalized (c:=vp0000000000100011000) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-4136639/31250 : ℚ) - ((0:ℤ):ℚ) = (-4136639/15625 : ℚ) by norm_num]
  exact coverp0000000000100011000
private noncomputable def ep0000000000100011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011001-E-0000.bin"
noncomputable def ep0000000000100011001 : Blocks := ep0000000000100011001_0
private theorem idp0000000000100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010001100.list =
    C ((2:ℤ)^34) * horner X vp0000000000100011001.list + horner X ep0000000000100011001.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100011001 : Branch 1 (-4136639/31250 : ℚ) vp000000000010001100 := by
  apply branch_checked idp0000000000100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-4136639/31250 : ℚ) - ((1:ℤ):ℚ) = (-4152264/15625 : ℚ) by norm_num]
  exact coverp0000000000100011001
theorem coverp000000000010001100 : Covers (-4136639/31250 : ℚ) vp000000000010001100 := join_branches bp0000000000100011000 bp0000000000100011001
private noncomputable def vp00000000001000110_0 : Blocks := edgeBlocks% "full/vectors/00000000001000110-V-0000.bin"
noncomputable def vp00000000001000110 : Blocks := vp00000000001000110_0
private theorem bp000000000010001100 : Branch 0 (-4136639/62500 : ℚ) vp00000000001000110 := by
  apply branch_left_normalized (c:=vp000000000010001100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-4136639/62500 : ℚ) - ((0:ℤ):ℚ) = (-4136639/31250 : ℚ) by norm_num]
  exact coverp000000000010001100
private noncomputable def ep000000000010001101_0 : Blocks := edgeBlocks% "full/vectors/000000000010001101-E-0000.bin"
noncomputable def ep000000000010001101 : Blocks := ep000000000010001101_0
private theorem idp000000000010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000110.list =
    C ((2:ℤ)^50) * horner X vp000000000010001101.list + horner X ep000000000010001101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010001101 : Branch 1 (-4136639/62500 : ℚ) vp00000000001000110 := by
  apply branch_checked idp000000000010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4136639/62500 : ℚ) - ((1:ℤ):ℚ) = (-4167889/31250 : ℚ) by norm_num]
  exact coverp000000000010001101
theorem coverp00000000001000110 : Covers (-4136639/62500 : ℚ) vp00000000001000110 := join_branches bp000000000010001100 bp000000000010001101
private noncomputable def vp0000000000100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011-V-0000.bin"
noncomputable def vp0000000000100011 : Blocks := vp0000000000100011_0
private theorem bp00000000001000110 : Branch 0 (-4136639/125000 : ℚ) vp0000000000100011 := by
  apply branch_left_normalized (c:=vp00000000001000110) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-4136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-4136639/62500 : ℚ) by norm_num]
  exact coverp00000000001000110
private noncomputable def ep00000000001000111_0 : Blocks := edgeBlocks% "full/vectors/00000000001000111-E-0000.bin"
noncomputable def ep00000000001000111 : Blocks := ep00000000001000111_0
private theorem idp00000000001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100011.list =
    C ((2:ℤ)^82) * horner X vp00000000001000111.list + horner X ep00000000001000111.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000111 : Branch 1 (-4136639/125000 : ℚ) vp0000000000100011 := by
  apply branch_checked idp00000000001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-4199139/62500 : ℚ) by norm_num]
  exact coverp00000000001000111
theorem coverp0000000000100011 : Covers (-4136639/125000 : ℚ) vp0000000000100011 := join_branches bp00000000001000110 bp00000000001000111
private noncomputable def vp0000000000100010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010111-V-0000.bin"
noncomputable def vp0000000000100010111 : Blocks := vp0000000000100010111_0
theorem coverp0000000000100010111 : Covers (-4121014/15625 : ℚ) vp0000000000100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000101101_0 : Blocks := edgeBlocks% "full/vectors/00000000001000101101-V-0000.bin"
noncomputable def vp00000000001000101101 : Blocks := vp00000000001000101101_0
theorem coverp00000000001000101101 : Covers (-8226403/15625 : ℚ) vp00000000001000101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010001011001_0 : Blocks := edgeBlocks% "full/vectors/000000000010001011001-V-0000.bin"
noncomputable def vp000000000010001011001 : Blocks := vp000000000010001011001_0
theorem coverp000000000010001011001 : Covers (-16437181/15625 : ℚ) vp000000000010001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010001011000_0 : Blocks := edgeBlocks% "full/vectors/000000000010001011000-V-0000.bin"
noncomputable def vp000000000010001011000 : Blocks := vp000000000010001011000_0
theorem coverp000000000010001011000 : Covers (-16421556/15625 : ℚ) vp000000000010001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000101100_0 : Blocks := edgeBlocks% "full/vectors/00000000001000101100-V-0000.bin"
noncomputable def vp00000000001000101100 : Blocks := vp00000000001000101100_0
private theorem bp000000000010001011000 : Branch 0 (-8210778/15625 : ℚ) vp00000000001000101100 := by
  apply branch_left_normalized (c:=vp000000000010001011000) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-8210778/15625 : ℚ) - ((0:ℤ):ℚ) = (-16421556/15625 : ℚ) by norm_num]
  exact coverp000000000010001011000
private noncomputable def ep000000000010001011001_0 : Blocks := edgeBlocks% "full/vectors/000000000010001011001-E-0000.bin"
noncomputable def ep000000000010001011001 : Blocks := ep000000000010001011001_0
private theorem idp000000000010001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000101100.list =
    C ((2:ℤ)^18) * horner X vp000000000010001011001.list + horner X ep000000000010001011001.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010001011001 : Branch 1 (-8210778/15625 : ℚ) vp00000000001000101100 := by
  apply branch_checked idp000000000010001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-8210778/15625 : ℚ) - ((1:ℤ):ℚ) = (-16437181/15625 : ℚ) by norm_num]
  exact coverp000000000010001011001
theorem coverp00000000001000101100 : Covers (-8210778/15625 : ℚ) vp00000000001000101100 := join_branches bp000000000010001011000 bp000000000010001011001
private noncomputable def vp0000000000100010110_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010110-V-0000.bin"
noncomputable def vp0000000000100010110 : Blocks := vp0000000000100010110_0
private theorem bp00000000001000101100 : Branch 0 (-4105389/15625 : ℚ) vp0000000000100010110 := by
  apply branch_left_normalized (c:=vp00000000001000101100) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4105389/15625 : ℚ) - ((0:ℤ):ℚ) = (-8210778/15625 : ℚ) by norm_num]
  exact coverp00000000001000101100
private noncomputable def ep00000000001000101101_0 : Blocks := edgeBlocks% "full/vectors/00000000001000101101-E-0000.bin"
noncomputable def ep00000000001000101101 : Blocks := ep00000000001000101101_0
private theorem idp00000000001000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100010110.list =
    C ((2:ℤ)^24) * horner X vp00000000001000101101.list + horner X ep00000000001000101101.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000101101 : Branch 1 (-4105389/15625 : ℚ) vp0000000000100010110 := by
  apply branch_checked idp00000000001000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-4105389/15625 : ℚ) - ((1:ℤ):ℚ) = (-8226403/15625 : ℚ) by norm_num]
  exact coverp00000000001000101101
theorem coverp0000000000100010110 : Covers (-4105389/15625 : ℚ) vp0000000000100010110 := join_branches bp00000000001000101100 bp00000000001000101101
private noncomputable def vp000000000010001011_0 : Blocks := edgeBlocks% "full/vectors/000000000010001011-V-0000.bin"
noncomputable def vp000000000010001011 : Blocks := vp000000000010001011_0
private theorem bp0000000000100010110 : Branch 0 (-4105389/31250 : ℚ) vp000000000010001011 := by
  apply branch_left_normalized (c:=vp0000000000100010110) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-4105389/31250 : ℚ) - ((0:ℤ):ℚ) = (-4105389/15625 : ℚ) by norm_num]
  exact coverp0000000000100010110
private noncomputable def ep0000000000100010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010111-E-0000.bin"
noncomputable def ep0000000000100010111 : Blocks := ep0000000000100010111_0
private theorem idp0000000000100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010001011.list =
    C ((2:ℤ)^33) * horner X vp0000000000100010111.list + horner X ep0000000000100010111.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100010111 : Branch 1 (-4105389/31250 : ℚ) vp000000000010001011 := by
  apply branch_checked idp0000000000100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-4105389/31250 : ℚ) - ((1:ℤ):ℚ) = (-4121014/15625 : ℚ) by norm_num]
  exact coverp0000000000100010111
theorem coverp000000000010001011 : Covers (-4105389/31250 : ℚ) vp000000000010001011 := join_branches bp0000000000100010110 bp0000000000100010111
private noncomputable def vp00000000001000101011_0 : Blocks := edgeBlocks% "full/vectors/00000000001000101011-V-0000.bin"
noncomputable def vp00000000001000101011 : Blocks := vp00000000001000101011_0
theorem coverp00000000001000101011 : Covers (-8195153/15625 : ℚ) vp00000000001000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000101010_0 : Blocks := edgeBlocks% "full/vectors/00000000001000101010-V-0000.bin"
noncomputable def vp00000000001000101010 : Blocks := vp00000000001000101010_0
theorem coverp00000000001000101010 : Covers (-8179528/15625 : ℚ) vp00000000001000101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010101-V-0000.bin"
noncomputable def vp0000000000100010101 : Blocks := vp0000000000100010101_0
private theorem bp00000000001000101010 : Branch 0 (-4089764/15625 : ℚ) vp0000000000100010101 := by
  apply branch_left_normalized (c:=vp00000000001000101010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4089764/15625 : ℚ) - ((0:ℤ):ℚ) = (-8179528/15625 : ℚ) by norm_num]
  exact coverp00000000001000101010
private noncomputable def ep00000000001000101011_0 : Blocks := edgeBlocks% "full/vectors/00000000001000101011-E-0000.bin"
noncomputable def ep00000000001000101011 : Blocks := ep00000000001000101011_0
private theorem idp00000000001000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100010101.list =
    C ((2:ℤ)^23) * horner X vp00000000001000101011.list + horner X ep00000000001000101011.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000101011 : Branch 1 (-4089764/15625 : ℚ) vp0000000000100010101 := by
  apply branch_checked idp00000000001000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-4089764/15625 : ℚ) - ((1:ℤ):ℚ) = (-8195153/15625 : ℚ) by norm_num]
  exact coverp00000000001000101011
theorem coverp0000000000100010101 : Covers (-4089764/15625 : ℚ) vp0000000000100010101 := join_branches bp00000000001000101010 bp00000000001000101011
private noncomputable def vp0000000000100010100_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010100-V-0000.bin"
noncomputable def vp0000000000100010100 : Blocks := vp0000000000100010100_0
theorem coverp0000000000100010100 : Covers (-4074139/15625 : ℚ) vp0000000000100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010001010_0 : Blocks := edgeBlocks% "full/vectors/000000000010001010-V-0000.bin"
noncomputable def vp000000000010001010 : Blocks := vp000000000010001010_0
private theorem bp0000000000100010100 : Branch 0 (-4074139/31250 : ℚ) vp000000000010001010 := by
  apply branch_left_normalized (c:=vp0000000000100010100) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4074139/31250 : ℚ) - ((0:ℤ):ℚ) = (-4074139/15625 : ℚ) by norm_num]
  exact coverp0000000000100010100
private noncomputable def ep0000000000100010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010101-E-0000.bin"
noncomputable def ep0000000000100010101 : Blocks := ep0000000000100010101_0
private theorem idp0000000000100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010001010.list =
    C ((2:ℤ)^33) * horner X vp0000000000100010101.list + horner X ep0000000000100010101.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100010101 : Branch 1 (-4074139/31250 : ℚ) vp000000000010001010 := by
  apply branch_checked idp0000000000100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4074139/31250 : ℚ) - ((1:ℤ):ℚ) = (-4089764/15625 : ℚ) by norm_num]
  exact coverp0000000000100010101
theorem coverp000000000010001010 : Covers (-4074139/31250 : ℚ) vp000000000010001010 := join_branches bp0000000000100010100 bp0000000000100010101
private noncomputable def vp00000000001000101_0 : Blocks := edgeBlocks% "full/vectors/00000000001000101-V-0000.bin"
noncomputable def vp00000000001000101 : Blocks := vp00000000001000101_0
private theorem bp000000000010001010 : Branch 0 (-4074139/62500 : ℚ) vp00000000001000101 := by
  apply branch_left_normalized (c:=vp000000000010001010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-4074139/62500 : ℚ) - ((0:ℤ):ℚ) = (-4074139/31250 : ℚ) by norm_num]
  exact coverp000000000010001010
private noncomputable def ep000000000010001011_0 : Blocks := edgeBlocks% "full/vectors/000000000010001011-E-0000.bin"
noncomputable def ep000000000010001011 : Blocks := ep000000000010001011_0
private theorem idp000000000010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000101.list =
    C ((2:ℤ)^49) * horner X vp000000000010001011.list + horner X ep000000000010001011.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010001011 : Branch 1 (-4074139/62500 : ℚ) vp00000000001000101 := by
  apply branch_checked idp000000000010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4074139/62500 : ℚ) - ((1:ℤ):ℚ) = (-4105389/31250 : ℚ) by norm_num]
  exact coverp000000000010001011
theorem coverp00000000001000101 : Covers (-4074139/62500 : ℚ) vp00000000001000101 := join_branches bp000000000010001010 bp000000000010001011
private noncomputable def vp0000000000100010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010011-V-0000.bin"
noncomputable def vp0000000000100010011 : Blocks := vp0000000000100010011_0
theorem coverp0000000000100010011 : Covers (-4058514/15625 : ℚ) vp0000000000100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010001001011_0 : Blocks := edgeBlocks% "full/vectors/000000000010001001011-V-0000.bin"
noncomputable def vp000000000010001001011 : Blocks := vp000000000010001001011_0
theorem coverp000000000010001001011 : Covers (-16218431/15625 : ℚ) vp000000000010001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010001001010_0 : Blocks := edgeBlocks% "full/vectors/000000000010001001010-V-0000.bin"
noncomputable def vp000000000010001001010 : Blocks := vp000000000010001001010_0
theorem coverp000000000010001001010 : Covers (-16202806/15625 : ℚ) vp000000000010001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000100101_0 : Blocks := edgeBlocks% "full/vectors/00000000001000100101-V-0000.bin"
noncomputable def vp00000000001000100101 : Blocks := vp00000000001000100101_0
private theorem bp000000000010001001010 : Branch 0 (-8101403/15625 : ℚ) vp00000000001000100101 := by
  apply branch_left_normalized (c:=vp000000000010001001010) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-8101403/15625 : ℚ) - ((0:ℤ):ℚ) = (-16202806/15625 : ℚ) by norm_num]
  exact coverp000000000010001001010
private noncomputable def ep000000000010001001011_0 : Blocks := edgeBlocks% "full/vectors/000000000010001001011-E-0000.bin"
noncomputable def ep000000000010001001011 : Blocks := ep000000000010001001011_0
private theorem idp000000000010001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000100101.list =
    C ((2:ℤ)^18) * horner X vp000000000010001001011.list + horner X ep000000000010001001011.list := by
  exact edge_identity (B := (2:ℤ)^121) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010001001011 : Branch 1 (-8101403/15625 : ℚ) vp00000000001000100101 := by
  apply branch_checked idp000000000010001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-8101403/15625 : ℚ) - ((1:ℤ):ℚ) = (-16218431/15625 : ℚ) by norm_num]
  exact coverp000000000010001001011
theorem coverp00000000001000100101 : Covers (-8101403/15625 : ℚ) vp00000000001000100101 := join_branches bp000000000010001001010 bp000000000010001001011
private noncomputable def vp00000000001000100100_0 : Blocks := edgeBlocks% "full/vectors/00000000001000100100-V-0000.bin"
noncomputable def vp00000000001000100100 : Blocks := vp00000000001000100100_0
theorem coverp00000000001000100100 : Covers (-8085778/15625 : ℚ) vp00000000001000100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100010010_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010010-V-0000.bin"
noncomputable def vp0000000000100010010 : Blocks := vp0000000000100010010_0
private theorem bp00000000001000100100 : Branch 0 (-4042889/15625 : ℚ) vp0000000000100010010 := by
  apply branch_left_normalized (c:=vp00000000001000100100) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4042889/15625 : ℚ) - ((0:ℤ):ℚ) = (-8085778/15625 : ℚ) by norm_num]
  exact coverp00000000001000100100
private noncomputable def ep00000000001000100101_0 : Blocks := edgeBlocks% "full/vectors/00000000001000100101-E-0000.bin"
noncomputable def ep00000000001000100101 : Blocks := ep00000000001000100101_0
private theorem idp00000000001000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100010010.list =
    C ((2:ℤ)^24) * horner X vp00000000001000100101.list + horner X ep00000000001000100101.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000100101 : Branch 1 (-4042889/15625 : ℚ) vp0000000000100010010 := by
  apply branch_checked idp00000000001000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-4042889/15625 : ℚ) - ((1:ℤ):ℚ) = (-8101403/15625 : ℚ) by norm_num]
  exact coverp00000000001000100101
theorem coverp0000000000100010010 : Covers (-4042889/15625 : ℚ) vp0000000000100010010 := join_branches bp00000000001000100100 bp00000000001000100101
private noncomputable def vp000000000010001001_0 : Blocks := edgeBlocks% "full/vectors/000000000010001001-V-0000.bin"
noncomputable def vp000000000010001001 : Blocks := vp000000000010001001_0
private theorem bp0000000000100010010 : Branch 0 (-4042889/31250 : ℚ) vp000000000010001001 := by
  apply branch_left_normalized (c:=vp0000000000100010010) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-4042889/31250 : ℚ) - ((0:ℤ):ℚ) = (-4042889/15625 : ℚ) by norm_num]
  exact coverp0000000000100010010
private noncomputable def ep0000000000100010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010011-E-0000.bin"
noncomputable def ep0000000000100010011 : Blocks := ep0000000000100010011_0
private theorem idp0000000000100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010001001.list =
    C ((2:ℤ)^33) * horner X vp0000000000100010011.list + horner X ep0000000000100010011.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100010011 : Branch 1 (-4042889/31250 : ℚ) vp000000000010001001 := by
  apply branch_checked idp0000000000100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4042889/31250 : ℚ) - ((1:ℤ):ℚ) = (-4058514/15625 : ℚ) by norm_num]
  exact coverp0000000000100010011
theorem coverp000000000010001001 : Covers (-4042889/31250 : ℚ) vp000000000010001001 := join_branches bp0000000000100010010 bp0000000000100010011
private noncomputable def vp0000000000100010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010001-V-0000.bin"
noncomputable def vp0000000000100010001 : Blocks := vp0000000000100010001_0
theorem coverp0000000000100010001 : Covers (-4027264/15625 : ℚ) vp0000000000100010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100010000_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010000-V-0000.bin"
noncomputable def vp0000000000100010000 : Blocks := vp0000000000100010000_0
theorem coverp0000000000100010000 : Covers (-4011639/15625 : ℚ) vp0000000000100010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010001000_0 : Blocks := edgeBlocks% "full/vectors/000000000010001000-V-0000.bin"
noncomputable def vp000000000010001000 : Blocks := vp000000000010001000_0
private theorem bp0000000000100010000 : Branch 0 (-4011639/31250 : ℚ) vp000000000010001000 := by
  apply branch_left_normalized (c:=vp0000000000100010000) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-4011639/31250 : ℚ) - ((0:ℤ):ℚ) = (-4011639/15625 : ℚ) by norm_num]
  exact coverp0000000000100010000
private noncomputable def ep0000000000100010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010001-E-0000.bin"
noncomputable def ep0000000000100010001 : Blocks := ep0000000000100010001_0
private theorem idp0000000000100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010001000.list =
    C ((2:ℤ)^34) * horner X vp0000000000100010001.list + horner X ep0000000000100010001.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100010001 : Branch 1 (-4011639/31250 : ℚ) vp000000000010001000 := by
  apply branch_checked idp0000000000100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4011639/31250 : ℚ) - ((1:ℤ):ℚ) = (-4027264/15625 : ℚ) by norm_num]
  exact coverp0000000000100010001
theorem coverp000000000010001000 : Covers (-4011639/31250 : ℚ) vp000000000010001000 := join_branches bp0000000000100010000 bp0000000000100010001
private noncomputable def vp00000000001000100_0 : Blocks := edgeBlocks% "full/vectors/00000000001000100-V-0000.bin"
noncomputable def vp00000000001000100 : Blocks := vp00000000001000100_0
private theorem bp000000000010001000 : Branch 0 (-4011639/62500 : ℚ) vp00000000001000100 := by
  apply branch_left_normalized (c:=vp000000000010001000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-4011639/62500 : ℚ) - ((0:ℤ):ℚ) = (-4011639/31250 : ℚ) by norm_num]
  exact coverp000000000010001000
private noncomputable def ep000000000010001001_0 : Blocks := edgeBlocks% "full/vectors/000000000010001001-E-0000.bin"
noncomputable def ep000000000010001001 : Blocks := ep000000000010001001_0
private theorem idp000000000010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000100.list =
    C ((2:ℤ)^52) * horner X vp000000000010001001.list + horner X ep000000000010001001.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010001001 : Branch 1 (-4011639/62500 : ℚ) vp00000000001000100 := by
  apply branch_checked idp000000000010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4011639/62500 : ℚ) - ((1:ℤ):ℚ) = (-4042889/31250 : ℚ) by norm_num]
  exact coverp000000000010001001
theorem coverp00000000001000100 : Covers (-4011639/62500 : ℚ) vp00000000001000100 := join_branches bp000000000010001000 bp000000000010001001
private noncomputable def vp0000000000100010_0 : Blocks := edgeBlocks% "full/vectors/0000000000100010-V-0000.bin"
noncomputable def vp0000000000100010 : Blocks := vp0000000000100010_0
private theorem bp00000000001000100 : Branch 0 (-4011639/125000 : ℚ) vp0000000000100010 := by
  apply branch_left_normalized (c:=vp00000000001000100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-4011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-4011639/62500 : ℚ) by norm_num]
  exact coverp00000000001000100
private noncomputable def ep00000000001000101_0 : Blocks := edgeBlocks% "full/vectors/00000000001000101-E-0000.bin"
noncomputable def ep00000000001000101 : Blocks := ep00000000001000101_0
private theorem idp00000000001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100010.list =
    C ((2:ℤ)^83) * horner X vp00000000001000101.list + horner X ep00000000001000101.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000101 : Branch 1 (-4011639/125000 : ℚ) vp0000000000100010 := by
  apply branch_checked idp00000000001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-4074139/62500 : ℚ) by norm_num]
  exact coverp00000000001000101
theorem coverp0000000000100010 : Covers (-4011639/125000 : ℚ) vp0000000000100010 := join_branches bp00000000001000100 bp00000000001000101
private noncomputable def vp000000000010001_0 : Blocks := edgeBlocks% "full/vectors/000000000010001-V-0000.bin"
private noncomputable def vp000000000010001_1 : Blocks := edgeBlocks% "full/vectors/000000000010001-V-0001.bin"
noncomputable def vp000000000010001 : Blocks := (Blocks.join vp000000000010001_0 vp000000000010001_1)
private theorem bp0000000000100010 : Branch 0 (-4011639/250000 : ℚ) vp000000000010001 := by
  apply branch_left_normalized (c:=vp0000000000100010) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-4011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-4011639/125000 : ℚ) by norm_num]
  exact coverp0000000000100010
private noncomputable def ep0000000000100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100011-E-0000.bin"
private noncomputable def ep0000000000100011_1 : Blocks := edgeBlocks% "full/vectors/0000000000100011-E-0001.bin"
noncomputable def ep0000000000100011 : Blocks := (Blocks.join ep0000000000100011_0 ep0000000000100011_1)
private theorem idp0000000000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010001.list =
    C ((2:ℤ)^152) * horner X vp0000000000100011.list + horner X ep0000000000100011.list := by
  exact edge_identity (B := (2:ℤ)^310) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100011 : Branch 1 (-4011639/250000 : ℚ) vp000000000010001 := by
  apply branch_checked idp0000000000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-4011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-4136639/125000 : ℚ) by norm_num]
  exact coverp0000000000100011
theorem coverp000000000010001 : Covers (-4011639/250000 : ℚ) vp000000000010001 := join_branches bp0000000000100010 bp0000000000100011
private noncomputable def vp000000000010000111111_0 : Blocks := edgeBlocks% "full/vectors/000000000010000111111-V-0000.bin"
noncomputable def vp000000000010000111111 : Blocks := vp000000000010000111111_0
theorem coverp000000000010000111111 : Covers (-16030931/15625 : ℚ) vp000000000010000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010000111110_0 : Blocks := edgeBlocks% "full/vectors/000000000010000111110-V-0000.bin"
noncomputable def vp000000000010000111110 : Blocks := vp000000000010000111110_0
theorem coverp000000000010000111110 : Covers (-16015306/15625 : ℚ) vp000000000010000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001000011111-V-0000.bin"
noncomputable def vp00000000001000011111 : Blocks := vp00000000001000011111_0
private theorem bp000000000010000111110 : Branch 0 (-8007653/15625 : ℚ) vp00000000001000011111 := by
  apply branch_left_normalized (c:=vp000000000010000111110) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-8007653/15625 : ℚ) - ((0:ℤ):ℚ) = (-16015306/15625 : ℚ) by norm_num]
  exact coverp000000000010000111110
private noncomputable def ep000000000010000111111_0 : Blocks := edgeBlocks% "full/vectors/000000000010000111111-E-0000.bin"
noncomputable def ep000000000010000111111 : Blocks := ep000000000010000111111_0
private theorem idp000000000010000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000011111.list =
    C ((2:ℤ)^18) * horner X vp000000000010000111111.list + horner X ep000000000010000111111.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010000111111 : Branch 1 (-8007653/15625 : ℚ) vp00000000001000011111 := by
  apply branch_checked idp000000000010000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-8007653/15625 : ℚ) - ((1:ℤ):ℚ) = (-16030931/15625 : ℚ) by norm_num]
  exact coverp000000000010000111111
theorem coverp00000000001000011111 : Covers (-8007653/15625 : ℚ) vp00000000001000011111 := join_branches bp000000000010000111110 bp000000000010000111111
private noncomputable def vp00000000001000011110_0 : Blocks := edgeBlocks% "full/vectors/00000000001000011110-V-0000.bin"
noncomputable def vp00000000001000011110 : Blocks := vp00000000001000011110_0
theorem coverp00000000001000011110 : Covers (-7992028/15625 : ℚ) vp00000000001000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001111-V-0000.bin"
noncomputable def vp0000000000100001111 : Blocks := vp0000000000100001111_0
private theorem bp00000000001000011110 : Branch 0 (-3996014/15625 : ℚ) vp0000000000100001111 := by
  apply branch_left_normalized (c:=vp00000000001000011110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-3996014/15625 : ℚ) - ((0:ℤ):ℚ) = (-7992028/15625 : ℚ) by norm_num]
  exact coverp00000000001000011110
private noncomputable def ep00000000001000011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001000011111-E-0000.bin"
noncomputable def ep00000000001000011111 : Blocks := ep00000000001000011111_0
private theorem idp00000000001000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100001111.list =
    C ((2:ℤ)^23) * horner X vp00000000001000011111.list + horner X ep00000000001000011111.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000011111 : Branch 1 (-3996014/15625 : ℚ) vp0000000000100001111 := by
  apply branch_checked idp00000000001000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3996014/15625 : ℚ) - ((1:ℤ):ℚ) = (-8007653/15625 : ℚ) by norm_num]
  exact coverp00000000001000011111
theorem coverp0000000000100001111 : Covers (-3996014/15625 : ℚ) vp0000000000100001111 := join_branches bp00000000001000011110 bp00000000001000011111
private noncomputable def vp0000000000100001110_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001110-V-0000.bin"
noncomputable def vp0000000000100001110 : Blocks := vp0000000000100001110_0
theorem coverp0000000000100001110 : Covers (-3980389/15625 : ℚ) vp0000000000100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010000111_0 : Blocks := edgeBlocks% "full/vectors/000000000010000111-V-0000.bin"
noncomputable def vp000000000010000111 : Blocks := vp000000000010000111_0
private theorem bp0000000000100001110 : Branch 0 (-3980389/31250 : ℚ) vp000000000010000111 := by
  apply branch_left_normalized (c:=vp0000000000100001110) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-3980389/31250 : ℚ) - ((0:ℤ):ℚ) = (-3980389/15625 : ℚ) by norm_num]
  exact coverp0000000000100001110
private noncomputable def ep0000000000100001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001111-E-0000.bin"
noncomputable def ep0000000000100001111 : Blocks := ep0000000000100001111_0
private theorem idp0000000000100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010000111.list =
    C ((2:ℤ)^33) * horner X vp0000000000100001111.list + horner X ep0000000000100001111.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100001111 : Branch 1 (-3980389/31250 : ℚ) vp000000000010000111 := by
  apply branch_checked idp0000000000100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3980389/31250 : ℚ) - ((1:ℤ):ℚ) = (-3996014/15625 : ℚ) by norm_num]
  exact coverp0000000000100001111
theorem coverp000000000010000111 : Covers (-3980389/31250 : ℚ) vp000000000010000111 := join_branches bp0000000000100001110 bp0000000000100001111
private noncomputable def vp00000000001000011011_0 : Blocks := edgeBlocks% "full/vectors/00000000001000011011-V-0000.bin"
noncomputable def vp00000000001000011011 : Blocks := vp00000000001000011011_0
theorem coverp00000000001000011011 : Covers (-7945153/15625 : ℚ) vp00000000001000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100001101011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001101011-V-0000.bin"
noncomputable def vp0000000000100001101011 : Blocks := vp0000000000100001101011_0
theorem coverp0000000000100001101011 : Covers (-31764987/15625 : ℚ) vp0000000000100001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100001101010_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001101010-V-0000.bin"
noncomputable def vp0000000000100001101010 : Blocks := vp0000000000100001101010_0
theorem coverp0000000000100001101010 : Covers (-31749362/15625 : ℚ) vp0000000000100001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010000110101_0 : Blocks := edgeBlocks% "full/vectors/000000000010000110101-V-0000.bin"
noncomputable def vp000000000010000110101 : Blocks := vp000000000010000110101_0
private theorem bp0000000000100001101010 : Branch 0 (-15874681/15625 : ℚ) vp000000000010000110101 := by
  apply branch_left_normalized (c:=vp0000000000100001101010) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-15874681/15625 : ℚ) - ((0:ℤ):ℚ) = (-31749362/15625 : ℚ) by norm_num]
  exact coverp0000000000100001101010
private noncomputable def ep0000000000100001101011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001101011-E-0000.bin"
noncomputable def ep0000000000100001101011 : Blocks := ep0000000000100001101011_0
private theorem idp0000000000100001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010000110101.list =
    C ((2:ℤ)^15) * horner X vp0000000000100001101011.list + horner X ep0000000000100001101011.list := by
  exact edge_identity (B := (2:ℤ)^117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100001101011 : Branch 1 (-15874681/15625 : ℚ) vp000000000010000110101 := by
  apply branch_checked idp0000000000100001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-15874681/15625 : ℚ) - ((1:ℤ):ℚ) = (-31764987/15625 : ℚ) by norm_num]
  exact coverp0000000000100001101011
theorem coverp000000000010000110101 : Covers (-15874681/15625 : ℚ) vp000000000010000110101 := join_branches bp0000000000100001101010 bp0000000000100001101011
private noncomputable def vp0000000000100001101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001101001-V-0000.bin"
noncomputable def vp0000000000100001101001 : Blocks := vp0000000000100001101001_0
theorem coverp0000000000100001101001 : Covers (-31733737/15625 : ℚ) vp0000000000100001101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100001101000_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001101000-V-0000.bin"
noncomputable def vp0000000000100001101000 : Blocks := vp0000000000100001101000_0
theorem coverp0000000000100001101000 : Covers (-31718112/15625 : ℚ) vp0000000000100001101000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010000110100_0 : Blocks := edgeBlocks% "full/vectors/000000000010000110100-V-0000.bin"
noncomputable def vp000000000010000110100 : Blocks := vp000000000010000110100_0
private theorem bp0000000000100001101000 : Branch 0 (-15859056/15625 : ℚ) vp000000000010000110100 := by
  apply branch_left_normalized (c:=vp0000000000100001101000) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-15859056/15625 : ℚ) - ((0:ℤ):ℚ) = (-31718112/15625 : ℚ) by norm_num]
  exact coverp0000000000100001101000
private noncomputable def ep0000000000100001101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001101001-E-0000.bin"
noncomputable def ep0000000000100001101001 : Blocks := ep0000000000100001101001_0
private theorem idp0000000000100001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010000110100.list =
    C ((2:ℤ)^14) * horner X vp0000000000100001101001.list + horner X ep0000000000100001101001.list := by
  exact edge_identity (B := (2:ℤ)^117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100001101001 : Branch 1 (-15859056/15625 : ℚ) vp000000000010000110100 := by
  apply branch_checked idp0000000000100001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-15859056/15625 : ℚ) - ((1:ℤ):ℚ) = (-31733737/15625 : ℚ) by norm_num]
  exact coverp0000000000100001101001
theorem coverp000000000010000110100 : Covers (-15859056/15625 : ℚ) vp000000000010000110100 := join_branches bp0000000000100001101000 bp0000000000100001101001
private noncomputable def vp00000000001000011010_0 : Blocks := edgeBlocks% "full/vectors/00000000001000011010-V-0000.bin"
noncomputable def vp00000000001000011010 : Blocks := vp00000000001000011010_0
private theorem bp000000000010000110100 : Branch 0 (-7929528/15625 : ℚ) vp00000000001000011010 := by
  apply branch_left_normalized (c:=vp000000000010000110100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-7929528/15625 : ℚ) - ((0:ℤ):ℚ) = (-15859056/15625 : ℚ) by norm_num]
  exact coverp000000000010000110100
private noncomputable def ep000000000010000110101_0 : Blocks := edgeBlocks% "full/vectors/000000000010000110101-E-0000.bin"
noncomputable def ep000000000010000110101 : Blocks := ep000000000010000110101_0
private theorem idp000000000010000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000011010.list =
    C ((2:ℤ)^18) * horner X vp000000000010000110101.list + horner X ep000000000010000110101.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010000110101 : Branch 1 (-7929528/15625 : ℚ) vp00000000001000011010 := by
  apply branch_checked idp000000000010000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-7929528/15625 : ℚ) - ((1:ℤ):ℚ) = (-15874681/15625 : ℚ) by norm_num]
  exact coverp000000000010000110101
theorem coverp00000000001000011010 : Covers (-7929528/15625 : ℚ) vp00000000001000011010 := join_branches bp000000000010000110100 bp000000000010000110101
private noncomputable def vp0000000000100001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001101-V-0000.bin"
noncomputable def vp0000000000100001101 : Blocks := vp0000000000100001101_0
private theorem bp00000000001000011010 : Branch 0 (-3964764/15625 : ℚ) vp0000000000100001101 := by
  apply branch_left_normalized (c:=vp00000000001000011010) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-3964764/15625 : ℚ) - ((0:ℤ):ℚ) = (-7929528/15625 : ℚ) by norm_num]
  exact coverp00000000001000011010
private noncomputable def ep00000000001000011011_0 : Blocks := edgeBlocks% "full/vectors/00000000001000011011-E-0000.bin"
noncomputable def ep00000000001000011011 : Blocks := ep00000000001000011011_0
private theorem idp00000000001000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100001101.list =
    C ((2:ℤ)^23) * horner X vp00000000001000011011.list + horner X ep00000000001000011011.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000011011 : Branch 1 (-3964764/15625 : ℚ) vp0000000000100001101 := by
  apply branch_checked idp00000000001000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3964764/15625 : ℚ) - ((1:ℤ):ℚ) = (-7945153/15625 : ℚ) by norm_num]
  exact coverp00000000001000011011
theorem coverp0000000000100001101 : Covers (-3964764/15625 : ℚ) vp0000000000100001101 := join_branches bp00000000001000011010 bp00000000001000011011
private noncomputable def vp000000000010000110011_0 : Blocks := edgeBlocks% "full/vectors/000000000010000110011-V-0000.bin"
noncomputable def vp000000000010000110011 : Blocks := vp000000000010000110011_0
theorem coverp000000000010000110011 : Covers (-15843431/15625 : ℚ) vp000000000010000110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010000110010_0 : Blocks := edgeBlocks% "full/vectors/000000000010000110010-V-0000.bin"
noncomputable def vp000000000010000110010 : Blocks := vp000000000010000110010_0
theorem coverp000000000010000110010 : Covers (-15827806/15625 : ℚ) vp000000000010000110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000011001_0 : Blocks := edgeBlocks% "full/vectors/00000000001000011001-V-0000.bin"
noncomputable def vp00000000001000011001 : Blocks := vp00000000001000011001_0
private theorem bp000000000010000110010 : Branch 0 (-7913903/15625 : ℚ) vp00000000001000011001 := by
  apply branch_left_normalized (c:=vp000000000010000110010) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-7913903/15625 : ℚ) - ((0:ℤ):ℚ) = (-15827806/15625 : ℚ) by norm_num]
  exact coverp000000000010000110010
private noncomputable def ep000000000010000110011_0 : Blocks := edgeBlocks% "full/vectors/000000000010000110011-E-0000.bin"
noncomputable def ep000000000010000110011 : Blocks := ep000000000010000110011_0
private theorem idp000000000010000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000011001.list =
    C ((2:ℤ)^17) * horner X vp000000000010000110011.list + horner X ep000000000010000110011.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010000110011 : Branch 1 (-7913903/15625 : ℚ) vp00000000001000011001 := by
  apply branch_checked idp000000000010000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-7913903/15625 : ℚ) - ((1:ℤ):ℚ) = (-15843431/15625 : ℚ) by norm_num]
  exact coverp000000000010000110011
theorem coverp00000000001000011001 : Covers (-7913903/15625 : ℚ) vp00000000001000011001 := join_branches bp000000000010000110010 bp000000000010000110011
private noncomputable def vp00000000001000011000_0 : Blocks := edgeBlocks% "full/vectors/00000000001000011000-V-0000.bin"
noncomputable def vp00000000001000011000 : Blocks := vp00000000001000011000_0
theorem coverp00000000001000011000 : Covers (-7898278/15625 : ℚ) vp00000000001000011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100001100_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001100-V-0000.bin"
noncomputable def vp0000000000100001100 : Blocks := vp0000000000100001100_0
private theorem bp00000000001000011000 : Branch 0 (-3949139/15625 : ℚ) vp0000000000100001100 := by
  apply branch_left_normalized (c:=vp00000000001000011000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-3949139/15625 : ℚ) - ((0:ℤ):ℚ) = (-7898278/15625 : ℚ) by norm_num]
  exact coverp00000000001000011000
private noncomputable def ep00000000001000011001_0 : Blocks := edgeBlocks% "full/vectors/00000000001000011001-E-0000.bin"
noncomputable def ep00000000001000011001 : Blocks := ep00000000001000011001_0
private theorem idp00000000001000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100001100.list =
    C ((2:ℤ)^23) * horner X vp00000000001000011001.list + horner X ep00000000001000011001.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000011001 : Branch 1 (-3949139/15625 : ℚ) vp0000000000100001100 := by
  apply branch_checked idp00000000001000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3949139/15625 : ℚ) - ((1:ℤ):ℚ) = (-7913903/15625 : ℚ) by norm_num]
  exact coverp00000000001000011001
theorem coverp0000000000100001100 : Covers (-3949139/15625 : ℚ) vp0000000000100001100 := join_branches bp00000000001000011000 bp00000000001000011001
private noncomputable def vp000000000010000110_0 : Blocks := edgeBlocks% "full/vectors/000000000010000110-V-0000.bin"
noncomputable def vp000000000010000110 : Blocks := vp000000000010000110_0
private theorem bp0000000000100001100 : Branch 0 (-3949139/31250 : ℚ) vp000000000010000110 := by
  apply branch_left_normalized (c:=vp0000000000100001100) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-3949139/31250 : ℚ) - ((0:ℤ):ℚ) = (-3949139/15625 : ℚ) by norm_num]
  exact coverp0000000000100001100
private noncomputable def ep0000000000100001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001101-E-0000.bin"
noncomputable def ep0000000000100001101 : Blocks := ep0000000000100001101_0
private theorem idp0000000000100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010000110.list =
    C ((2:ℤ)^32) * horner X vp0000000000100001101.list + horner X ep0000000000100001101.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100001101 : Branch 1 (-3949139/31250 : ℚ) vp000000000010000110 := by
  apply branch_checked idp0000000000100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-3949139/31250 : ℚ) - ((1:ℤ):ℚ) = (-3964764/15625 : ℚ) by norm_num]
  exact coverp0000000000100001101
theorem coverp000000000010000110 : Covers (-3949139/31250 : ℚ) vp000000000010000110 := join_branches bp0000000000100001100 bp0000000000100001101
private noncomputable def vp00000000001000011_0 : Blocks := edgeBlocks% "full/vectors/00000000001000011-V-0000.bin"
noncomputable def vp00000000001000011 : Blocks := vp00000000001000011_0
private theorem bp000000000010000110 : Branch 0 (-3949139/62500 : ℚ) vp00000000001000011 := by
  apply branch_left_normalized (c:=vp000000000010000110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-3949139/62500 : ℚ) - ((0:ℤ):ℚ) = (-3949139/31250 : ℚ) by norm_num]
  exact coverp000000000010000110
private noncomputable def ep000000000010000111_0 : Blocks := edgeBlocks% "full/vectors/000000000010000111-E-0000.bin"
noncomputable def ep000000000010000111 : Blocks := ep000000000010000111_0
private theorem idp000000000010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000011.list =
    C ((2:ℤ)^49) * horner X vp000000000010000111.list + horner X ep000000000010000111.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010000111 : Branch 1 (-3949139/62500 : ℚ) vp00000000001000011 := by
  apply branch_checked idp000000000010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3949139/62500 : ℚ) - ((1:ℤ):ℚ) = (-3980389/31250 : ℚ) by norm_num]
  exact coverp000000000010000111
theorem coverp00000000001000011 : Covers (-3949139/62500 : ℚ) vp00000000001000011 := join_branches bp000000000010000110 bp000000000010000111
private noncomputable def vp0000000000100001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001011-V-0000.bin"
noncomputable def vp0000000000100001011 : Blocks := vp0000000000100001011_0
theorem coverp0000000000100001011 : Covers (-3933514/15625 : ℚ) vp0000000000100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100001010_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001010-V-0000.bin"
noncomputable def vp0000000000100001010 : Blocks := vp0000000000100001010_0
theorem coverp0000000000100001010 : Covers (-3917889/15625 : ℚ) vp0000000000100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010000101_0 : Blocks := edgeBlocks% "full/vectors/000000000010000101-V-0000.bin"
noncomputable def vp000000000010000101 : Blocks := vp000000000010000101_0
private theorem bp0000000000100001010 : Branch 0 (-3917889/31250 : ℚ) vp000000000010000101 := by
  apply branch_left_normalized (c:=vp0000000000100001010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-3917889/31250 : ℚ) - ((0:ℤ):ℚ) = (-3917889/15625 : ℚ) by norm_num]
  exact coverp0000000000100001010
private noncomputable def ep0000000000100001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001011-E-0000.bin"
noncomputable def ep0000000000100001011 : Blocks := ep0000000000100001011_0
private theorem idp0000000000100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010000101.list =
    C ((2:ℤ)^32) * horner X vp0000000000100001011.list + horner X ep0000000000100001011.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100001011 : Branch 1 (-3917889/31250 : ℚ) vp000000000010000101 := by
  apply branch_checked idp0000000000100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-3917889/31250 : ℚ) - ((1:ℤ):ℚ) = (-3933514/15625 : ℚ) by norm_num]
  exact coverp0000000000100001011
theorem coverp000000000010000101 : Covers (-3917889/31250 : ℚ) vp000000000010000101 := join_branches bp0000000000100001010 bp0000000000100001011
private noncomputable def vp000000000010000100_0 : Blocks := edgeBlocks% "full/vectors/000000000010000100-V-0000.bin"
noncomputable def vp000000000010000100 : Blocks := vp000000000010000100_0
theorem coverp000000000010000100 : Covers (-3886639/31250 : ℚ) vp000000000010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000010_0 : Blocks := edgeBlocks% "full/vectors/00000000001000010-V-0000.bin"
noncomputable def vp00000000001000010 : Blocks := vp00000000001000010_0
private theorem bp000000000010000100 : Branch 0 (-3886639/62500 : ℚ) vp00000000001000010 := by
  apply branch_left_normalized (c:=vp000000000010000100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-3886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-3886639/31250 : ℚ) by norm_num]
  exact coverp000000000010000100
private noncomputable def ep000000000010000101_0 : Blocks := edgeBlocks% "full/vectors/000000000010000101-E-0000.bin"
noncomputable def ep000000000010000101 : Blocks := ep000000000010000101_0
private theorem idp000000000010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000010.list =
    C ((2:ℤ)^48) * horner X vp000000000010000101.list + horner X ep000000000010000101.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010000101 : Branch 1 (-3886639/62500 : ℚ) vp00000000001000010 := by
  apply branch_checked idp000000000010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-3917889/31250 : ℚ) by norm_num]
  exact coverp000000000010000101
theorem coverp00000000001000010 : Covers (-3886639/62500 : ℚ) vp00000000001000010 := join_branches bp000000000010000100 bp000000000010000101
private noncomputable def vp0000000000100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001-V-0000.bin"
noncomputable def vp0000000000100001 : Blocks := vp0000000000100001_0
private theorem bp00000000001000010 : Branch 0 (-3886639/125000 : ℚ) vp0000000000100001 := by
  apply branch_left_normalized (c:=vp00000000001000010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-3886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-3886639/62500 : ℚ) by norm_num]
  exact coverp00000000001000010
private noncomputable def ep00000000001000011_0 : Blocks := edgeBlocks% "full/vectors/00000000001000011-E-0000.bin"
noncomputable def ep00000000001000011 : Blocks := ep00000000001000011_0
private theorem idp00000000001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100001.list =
    C ((2:ℤ)^81) * horner X vp00000000001000011.list + horner X ep00000000001000011.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000011 : Branch 1 (-3886639/125000 : ℚ) vp0000000000100001 := by
  apply branch_checked idp00000000001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-3949139/62500 : ℚ) by norm_num]
  exact coverp00000000001000011
theorem coverp0000000000100001 : Covers (-3886639/125000 : ℚ) vp0000000000100001 := join_branches bp00000000001000010 bp00000000001000011
private noncomputable def vp0000000000100000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100000111-V-0000.bin"
noncomputable def vp0000000000100000111 : Blocks := vp0000000000100000111_0
theorem coverp0000000000100000111 : Covers (-3871014/15625 : ℚ) vp0000000000100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000100000110_0 : Blocks := edgeBlocks% "full/vectors/0000000000100000110-V-0000.bin"
noncomputable def vp0000000000100000110 : Blocks := vp0000000000100000110_0
theorem coverp0000000000100000110 : Covers (-3855389/15625 : ℚ) vp0000000000100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010000011_0 : Blocks := edgeBlocks% "full/vectors/000000000010000011-V-0000.bin"
noncomputable def vp000000000010000011 : Blocks := vp000000000010000011_0
private theorem bp0000000000100000110 : Branch 0 (-3855389/31250 : ℚ) vp000000000010000011 := by
  apply branch_left_normalized (c:=vp0000000000100000110) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-3855389/31250 : ℚ) - ((0:ℤ):ℚ) = (-3855389/15625 : ℚ) by norm_num]
  exact coverp0000000000100000110
private noncomputable def ep0000000000100000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000100000111-E-0000.bin"
noncomputable def ep0000000000100000111 : Blocks := ep0000000000100000111_0
private theorem idp0000000000100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010000011.list =
    C ((2:ℤ)^31) * horner X vp0000000000100000111.list + horner X ep0000000000100000111.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100000111 : Branch 1 (-3855389/31250 : ℚ) vp000000000010000011 := by
  apply branch_checked idp0000000000100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-3855389/31250 : ℚ) - ((1:ℤ):ℚ) = (-3871014/15625 : ℚ) by norm_num]
  exact coverp0000000000100000111
theorem coverp000000000010000011 : Covers (-3855389/31250 : ℚ) vp000000000010000011 := join_branches bp0000000000100000110 bp0000000000100000111
private noncomputable def vp000000000010000010_0 : Blocks := edgeBlocks% "full/vectors/000000000010000010-V-0000.bin"
noncomputable def vp000000000010000010 : Blocks := vp000000000010000010_0
theorem coverp000000000010000010 : Covers (-3824139/31250 : ℚ) vp000000000010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000001_0 : Blocks := edgeBlocks% "full/vectors/00000000001000001-V-0000.bin"
noncomputable def vp00000000001000001 : Blocks := vp00000000001000001_0
private theorem bp000000000010000010 : Branch 0 (-3824139/62500 : ℚ) vp00000000001000001 := by
  apply branch_left_normalized (c:=vp000000000010000010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-3824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-3824139/31250 : ℚ) by norm_num]
  exact coverp000000000010000010
private noncomputable def ep000000000010000011_0 : Blocks := edgeBlocks% "full/vectors/000000000010000011-E-0000.bin"
noncomputable def ep000000000010000011 : Blocks := ep000000000010000011_0
private theorem idp000000000010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000001.list =
    C ((2:ℤ)^47) * horner X vp000000000010000011.list + horner X ep000000000010000011.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010000011 : Branch 1 (-3824139/62500 : ℚ) vp00000000001000001 := by
  apply branch_checked idp000000000010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-3855389/31250 : ℚ) by norm_num]
  exact coverp000000000010000011
theorem coverp00000000001000001 : Covers (-3824139/62500 : ℚ) vp00000000001000001 := join_branches bp000000000010000010 bp000000000010000011
private noncomputable def vp000000000010000001_0 : Blocks := edgeBlocks% "full/vectors/000000000010000001-V-0000.bin"
noncomputable def vp000000000010000001 : Blocks := vp000000000010000001_0
theorem coverp000000000010000001 : Covers (-3792889/31250 : ℚ) vp000000000010000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010000000_0 : Blocks := edgeBlocks% "full/vectors/000000000010000000-V-0000.bin"
noncomputable def vp000000000010000000 : Blocks := vp000000000010000000_0
theorem coverp000000000010000000 : Covers (-3761639/31250 : ℚ) vp000000000010000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001000000_0 : Blocks := edgeBlocks% "full/vectors/00000000001000000-V-0000.bin"
noncomputable def vp00000000001000000 : Blocks := vp00000000001000000_0
private theorem bp000000000010000000 : Branch 0 (-3761639/62500 : ℚ) vp00000000001000000 := by
  apply branch_left_normalized (c:=vp000000000010000000) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-3761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-3761639/31250 : ℚ) by norm_num]
  exact coverp000000000010000000
private noncomputable def ep000000000010000001_0 : Blocks := edgeBlocks% "full/vectors/000000000010000001-E-0000.bin"
noncomputable def ep000000000010000001 : Blocks := ep000000000010000001_0
private theorem idp000000000010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000000.list =
    C ((2:ℤ)^47) * horner X vp000000000010000001.list + horner X ep000000000010000001.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010000001 : Branch 1 (-3761639/62500 : ℚ) vp00000000001000000 := by
  apply branch_checked idp000000000010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-3792889/31250 : ℚ) by norm_num]
  exact coverp000000000010000001
theorem coverp00000000001000000 : Covers (-3761639/62500 : ℚ) vp00000000001000000 := join_branches bp000000000010000000 bp000000000010000001
private noncomputable def vp0000000000100000_0 : Blocks := edgeBlocks% "full/vectors/0000000000100000-V-0000.bin"
noncomputable def vp0000000000100000 : Blocks := vp0000000000100000_0
private theorem bp00000000001000000 : Branch 0 (-3761639/125000 : ℚ) vp0000000000100000 := by
  apply branch_left_normalized (c:=vp00000000001000000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-3761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-3761639/62500 : ℚ) by norm_num]
  exact coverp00000000001000000
private noncomputable def ep00000000001000001_0 : Blocks := edgeBlocks% "full/vectors/00000000001000001-E-0000.bin"
noncomputable def ep00000000001000001 : Blocks := ep00000000001000001_0
private theorem idp00000000001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100000.list =
    C ((2:ℤ)^79) * horner X vp00000000001000001.list + horner X ep00000000001000001.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001000001 : Branch 1 (-3761639/125000 : ℚ) vp0000000000100000 := by
  apply branch_checked idp00000000001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-3761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-3824139/62500 : ℚ) by norm_num]
  exact coverp00000000001000001
theorem coverp0000000000100000 : Covers (-3761639/125000 : ℚ) vp0000000000100000 := join_branches bp00000000001000000 bp00000000001000001
private noncomputable def vp000000000010000_0 : Blocks := edgeBlocks% "full/vectors/000000000010000-V-0000.bin"
private noncomputable def vp000000000010000_1 : Blocks := edgeBlocks% "full/vectors/000000000010000-V-0001.bin"
noncomputable def vp000000000010000 : Blocks := (Blocks.join vp000000000010000_0 vp000000000010000_1)
private theorem bp0000000000100000 : Branch 0 (-3761639/250000 : ℚ) vp000000000010000 := by
  apply branch_left_normalized (c:=vp0000000000100000) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-3761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-3761639/125000 : ℚ) by norm_num]
  exact coverp0000000000100000
private noncomputable def ep0000000000100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000100001-E-0000.bin"
private noncomputable def ep0000000000100001_1 : Blocks := edgeBlocks% "full/vectors/0000000000100001-E-0001.bin"
noncomputable def ep0000000000100001 : Blocks := (Blocks.join ep0000000000100001_0 ep0000000000100001_1)
private theorem idp0000000000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010000.list =
    C ((2:ℤ)^141) * horner X vp0000000000100001.list + horner X ep0000000000100001.list := by
  exact edge_identity (B := (2:ℤ)^300) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000100001 : Branch 1 (-3761639/250000 : ℚ) vp000000000010000 := by
  apply branch_checked idp0000000000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-3886639/125000 : ℚ) by norm_num]
  exact coverp0000000000100001
theorem coverp000000000010000 : Covers (-3761639/250000 : ℚ) vp000000000010000 := join_branches bp0000000000100000 bp0000000000100001
private noncomputable def vp00000000001000_0 : Blocks := edgeBlocks% "full/vectors/00000000001000-V-0000.bin"
private noncomputable def vp00000000001000_1 : Blocks := edgeBlocks% "full/vectors/00000000001000-V-0001.bin"
private noncomputable def vp00000000001000_2 : Blocks := edgeBlocks% "full/vectors/00000000001000-V-0002.bin"
noncomputable def vp00000000001000 : Blocks := (Blocks.join vp00000000001000_0 (Blocks.join vp00000000001000_1 vp00000000001000_2))
private theorem bp000000000010000 : Branch 0 (-3761639/500000 : ℚ) vp00000000001000 := by
  apply branch_left_normalized (c:=vp000000000010000) (k:=0) (m:=140) (by decide +kernel)
  rw [show 2*(-3761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-3761639/250000 : ℚ) by norm_num]
  exact coverp000000000010000
private noncomputable def ep000000000010001_0 : Blocks := edgeBlocks% "full/vectors/000000000010001-E-0000.bin"
private noncomputable def ep000000000010001_1 : Blocks := edgeBlocks% "full/vectors/000000000010001-E-0001.bin"
private noncomputable def ep000000000010001_2 : Blocks := edgeBlocks% "full/vectors/000000000010001-E-0002.bin"
noncomputable def ep000000000010001 : Blocks := (Blocks.join ep000000000010001_0 (Blocks.join ep000000000010001_1 ep000000000010001_2))
private theorem idp000000000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001000.list =
    C ((2:ℤ)^264) * horner X vp000000000010001.list + horner X ep000000000010001.list := by
  exact edge_identity (B := (2:ℤ)^488) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010001 : Branch 1 (-3761639/500000 : ℚ) vp00000000001000 := by
  apply branch_checked idp000000000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-3761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-4011639/250000 : ℚ) by norm_num]
  exact coverp000000000010001
theorem coverp00000000001000 : Covers (-3761639/500000 : ℚ) vp00000000001000 := join_branches bp000000000010000 bp000000000010001
private noncomputable def vp0000000000100_0 : Blocks := edgeBlocks% "full/vectors/0000000000100-V-0000.bin"
private noncomputable def vp0000000000100_1 : Blocks := edgeBlocks% "full/vectors/0000000000100-V-0001.bin"
private noncomputable def vp0000000000100_2 : Blocks := edgeBlocks% "full/vectors/0000000000100-V-0002.bin"
private noncomputable def vp0000000000100_3 : Blocks := edgeBlocks% "full/vectors/0000000000100-V-0003.bin"
noncomputable def vp0000000000100 : Blocks := (Blocks.join (Blocks.join vp0000000000100_0 vp0000000000100_1) (Blocks.join vp0000000000100_2 vp0000000000100_3))
private theorem bp00000000001000 : Branch 0 (-3761639/1000000 : ℚ) vp0000000000100 := by
  apply branch_left_normalized (c:=vp00000000001000) (k:=0) (m:=263) (by decide +kernel)
  rw [show 2*(-3761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-3761639/500000 : ℚ) by norm_num]
  exact coverp00000000001000
private noncomputable def ep00000000001001_0 : Blocks := edgeBlocks% "full/vectors/00000000001001-E-0000.bin"
private noncomputable def ep00000000001001_1 : Blocks := edgeBlocks% "full/vectors/00000000001001-E-0001.bin"
private noncomputable def ep00000000001001_2 : Blocks := edgeBlocks% "full/vectors/00000000001001-E-0002.bin"
private noncomputable def ep00000000001001_3 : Blocks := edgeBlocks% "full/vectors/00000000001001-E-0003.bin"
noncomputable def ep00000000001001 : Blocks := (Blocks.join (Blocks.join ep00000000001001_0 ep00000000001001_1) (Blocks.join ep00000000001001_2 ep00000000001001_3))
private theorem idp00000000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000100.list =
    C ((2:ℤ)^506) * horner X vp00000000001001.list + horner X ep00000000001001.list := by
  exact edge_identity (B := (2:ℤ)^860) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001001 : Branch 1 (-3761639/1000000 : ℚ) vp0000000000100 := by
  apply branch_checked idp00000000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-4261639/500000 : ℚ) by norm_num]
  exact coverp00000000001001
theorem coverp0000000000100 : Covers (-3761639/1000000 : ℚ) vp0000000000100 := join_branches bp00000000001000 bp00000000001001
private noncomputable def vp000000000010_0 : Blocks := edgeBlocks% "full/vectors/000000000010-V-0000.bin"
private noncomputable def vp000000000010_1 : Blocks := edgeBlocks% "full/vectors/000000000010-V-0001.bin"
private noncomputable def vp000000000010_2 : Blocks := edgeBlocks% "full/vectors/000000000010-V-0002.bin"
private noncomputable def vp000000000010_3 : Blocks := edgeBlocks% "full/vectors/000000000010-V-0003.bin"
private noncomputable def vp000000000010_4 : Blocks := edgeBlocks% "full/vectors/000000000010-V-0004.bin"
private noncomputable def vp000000000010_5 : Blocks := edgeBlocks% "full/vectors/000000000010-V-0005.bin"
private noncomputable def vp000000000010_6 : Blocks := edgeBlocks% "full/vectors/000000000010-V-0006.bin"
private noncomputable def vp000000000010_7 : Blocks := edgeBlocks% "full/vectors/000000000010-V-0007.bin"
noncomputable def vp000000000010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000000000010_0 vp000000000010_1) (Blocks.join vp000000000010_2 vp000000000010_3)) (Blocks.join (Blocks.join vp000000000010_4 vp000000000010_5) (Blocks.join vp000000000010_6 vp000000000010_7)))
private theorem bp0000000000100 : Branch 0 (-3761639/2000000 : ℚ) vp000000000010 := by
  apply branch_left_normalized (c:=vp0000000000100) (k:=0) (m:=505) (by decide +kernel)
  rw [show 2*(-3761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-3761639/1000000 : ℚ) by norm_num]
  exact coverp0000000000100
private noncomputable def ep0000000000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101-E-0000.bin"
private noncomputable def ep0000000000101_1 : Blocks := edgeBlocks% "full/vectors/0000000000101-E-0001.bin"
private noncomputable def ep0000000000101_2 : Blocks := edgeBlocks% "full/vectors/0000000000101-E-0002.bin"
private noncomputable def ep0000000000101_3 : Blocks := edgeBlocks% "full/vectors/0000000000101-E-0003.bin"
private noncomputable def ep0000000000101_4 : Blocks := edgeBlocks% "full/vectors/0000000000101-E-0004.bin"
private noncomputable def ep0000000000101_5 : Blocks := edgeBlocks% "full/vectors/0000000000101-E-0005.bin"
private noncomputable def ep0000000000101_6 : Blocks := edgeBlocks% "full/vectors/0000000000101-E-0006.bin"
private noncomputable def ep0000000000101_7 : Blocks := edgeBlocks% "full/vectors/0000000000101-E-0007.bin"
noncomputable def ep0000000000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000000000101_0 ep0000000000101_1) (Blocks.join ep0000000000101_2 ep0000000000101_3)) (Blocks.join (Blocks.join ep0000000000101_4 ep0000000000101_5) (Blocks.join ep0000000000101_6 ep0000000000101_7)))
private theorem idp0000000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010.list =
    C ((2:ℤ)^988) * horner X vp0000000000101.list + horner X ep0000000000101.list := by
  exact edge_identity (B := (2:ℤ)^1601) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101 : Branch 1 (-3761639/2000000 : ℚ) vp000000000010 := by
  apply branch_checked idp0000000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-3761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-4761639/1000000 : ℚ) by norm_num]
  exact coverp0000000000101
theorem coverp000000000010 : Covers (-3761639/2000000 : ℚ) vp000000000010 := join_branches bp0000000000100 bp0000000000101
end NextProof.EdgeFull

