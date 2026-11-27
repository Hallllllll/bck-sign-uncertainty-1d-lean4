import NextProof.LeftKernel
import NextProof.OptEdge00008Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00007

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000000000001111111_0 : Blocks := edgeBlocks% "full/vectors/000000000001111111-V-0000.bin"
noncomputable def vp000000000001111111 : Blocks := vp000000000001111111_0
theorem coverp000000000001111111 : Covers (-3730389/31250 : ℚ) vp000000000001111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001111110_0 : Blocks := edgeBlocks% "full/vectors/000000000001111110-V-0000.bin"
noncomputable def vp000000000001111110 : Blocks := vp000000000001111110_0
theorem coverp000000000001111110 : Covers (-3699139/31250 : ℚ) vp000000000001111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111111_0 : Blocks := edgeBlocks% "full/vectors/00000000000111111-V-0000.bin"
noncomputable def vp00000000000111111 : Blocks := vp00000000000111111_0
private theorem bp000000000001111110 : Branch 0 (-3699139/62500 : ℚ) vp00000000000111111 := by
  apply branch_left_normalized (c:=vp000000000001111110) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-3699139/62500 : ℚ) - ((0:ℤ):ℚ) = (-3699139/31250 : ℚ) by norm_num]
  exact coverp000000000001111110
private noncomputable def ep000000000001111111_0 : Blocks := edgeBlocks% "full/vectors/000000000001111111-E-0000.bin"
noncomputable def ep000000000001111111 : Blocks := ep000000000001111111_0
private theorem idp000000000001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111111.list =
    C ((2:ℤ)^47) * horner X vp000000000001111111.list + horner X ep000000000001111111.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001111111 : Branch 1 (-3699139/62500 : ℚ) vp00000000000111111 := by
  apply branch_checked idp000000000001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3699139/62500 : ℚ) - ((1:ℤ):ℚ) = (-3730389/31250 : ℚ) by norm_num]
  exact coverp000000000001111111
theorem coverp00000000000111111 : Covers (-3699139/62500 : ℚ) vp00000000000111111 := join_branches bp000000000001111110 bp000000000001111111
private noncomputable def vp000000000001111101_0 : Blocks := edgeBlocks% "full/vectors/000000000001111101-V-0000.bin"
noncomputable def vp000000000001111101 : Blocks := vp000000000001111101_0
theorem coverp000000000001111101 : Covers (-3667889/31250 : ℚ) vp000000000001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001111100_0 : Blocks := edgeBlocks% "full/vectors/000000000001111100-V-0000.bin"
noncomputable def vp000000000001111100 : Blocks := vp000000000001111100_0
theorem coverp000000000001111100 : Covers (-3636639/31250 : ℚ) vp000000000001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111110_0 : Blocks := edgeBlocks% "full/vectors/00000000000111110-V-0000.bin"
noncomputable def vp00000000000111110 : Blocks := vp00000000000111110_0
private theorem bp000000000001111100 : Branch 0 (-3636639/62500 : ℚ) vp00000000000111110 := by
  apply branch_left_normalized (c:=vp000000000001111100) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-3636639/62500 : ℚ) - ((0:ℤ):ℚ) = (-3636639/31250 : ℚ) by norm_num]
  exact coverp000000000001111100
private noncomputable def ep000000000001111101_0 : Blocks := edgeBlocks% "full/vectors/000000000001111101-E-0000.bin"
noncomputable def ep000000000001111101 : Blocks := ep000000000001111101_0
private theorem idp000000000001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111110.list =
    C ((2:ℤ)^47) * horner X vp000000000001111101.list + horner X ep000000000001111101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001111101 : Branch 1 (-3636639/62500 : ℚ) vp00000000000111110 := by
  apply branch_checked idp000000000001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3636639/62500 : ℚ) - ((1:ℤ):ℚ) = (-3667889/31250 : ℚ) by norm_num]
  exact coverp000000000001111101
theorem coverp00000000000111110 : Covers (-3636639/62500 : ℚ) vp00000000000111110 := join_branches bp000000000001111100 bp000000000001111101
private noncomputable def vp0000000000011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000011111-V-0000.bin"
noncomputable def vp0000000000011111 : Blocks := vp0000000000011111_0
private theorem bp00000000000111110 : Branch 0 (-3636639/125000 : ℚ) vp0000000000011111 := by
  apply branch_left_normalized (c:=vp00000000000111110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-3636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-3636639/62500 : ℚ) by norm_num]
  exact coverp00000000000111110
private noncomputable def ep00000000000111111_0 : Blocks := edgeBlocks% "full/vectors/00000000000111111-E-0000.bin"
noncomputable def ep00000000000111111 : Blocks := ep00000000000111111_0
private theorem idp00000000000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011111.list =
    C ((2:ℤ)^80) * horner X vp00000000000111111.list + horner X ep00000000000111111.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111111 : Branch 1 (-3636639/125000 : ℚ) vp0000000000011111 := by
  apply branch_checked idp00000000000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-3636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-3699139/62500 : ℚ) by norm_num]
  exact coverp00000000000111111
theorem coverp0000000000011111 : Covers (-3636639/125000 : ℚ) vp0000000000011111 := join_branches bp00000000000111110 bp00000000000111111
private noncomputable def vp0000000000011110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110111-V-0000.bin"
noncomputable def vp0000000000011110111 : Blocks := vp0000000000011110111_0
theorem coverp0000000000011110111 : Covers (-3621014/15625 : ℚ) vp0000000000011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011110110_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110110-V-0000.bin"
noncomputable def vp0000000000011110110 : Blocks := vp0000000000011110110_0
theorem coverp0000000000011110110 : Covers (-3605389/15625 : ℚ) vp0000000000011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001111011_0 : Blocks := edgeBlocks% "full/vectors/000000000001111011-V-0000.bin"
noncomputable def vp000000000001111011 : Blocks := vp000000000001111011_0
private theorem bp0000000000011110110 : Branch 0 (-3605389/31250 : ℚ) vp000000000001111011 := by
  apply branch_left_normalized (c:=vp0000000000011110110) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-3605389/31250 : ℚ) - ((0:ℤ):ℚ) = (-3605389/15625 : ℚ) by norm_num]
  exact coverp0000000000011110110
private noncomputable def ep0000000000011110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110111-E-0000.bin"
noncomputable def ep0000000000011110111 : Blocks := ep0000000000011110111_0
private theorem idp0000000000011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001111011.list =
    C ((2:ℤ)^30) * horner X vp0000000000011110111.list + horner X ep0000000000011110111.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011110111 : Branch 1 (-3605389/31250 : ℚ) vp000000000001111011 := by
  apply branch_checked idp0000000000011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3605389/31250 : ℚ) - ((1:ℤ):ℚ) = (-3621014/15625 : ℚ) by norm_num]
  exact coverp0000000000011110111
theorem coverp000000000001111011 : Covers (-3605389/31250 : ℚ) vp000000000001111011 := join_branches bp0000000000011110110 bp0000000000011110111
private noncomputable def vp0000000000011110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110101-V-0000.bin"
noncomputable def vp0000000000011110101 : Blocks := vp0000000000011110101_0
theorem coverp0000000000011110101 : Covers (-3589764/15625 : ℚ) vp0000000000011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011110100_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110100-V-0000.bin"
noncomputable def vp0000000000011110100 : Blocks := vp0000000000011110100_0
theorem coverp0000000000011110100 : Covers (-3574139/15625 : ℚ) vp0000000000011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001111010_0 : Blocks := edgeBlocks% "full/vectors/000000000001111010-V-0000.bin"
noncomputable def vp000000000001111010 : Blocks := vp000000000001111010_0
private theorem bp0000000000011110100 : Branch 0 (-3574139/31250 : ℚ) vp000000000001111010 := by
  apply branch_left_normalized (c:=vp0000000000011110100) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-3574139/31250 : ℚ) - ((0:ℤ):ℚ) = (-3574139/15625 : ℚ) by norm_num]
  exact coverp0000000000011110100
private noncomputable def ep0000000000011110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110101-E-0000.bin"
noncomputable def ep0000000000011110101 : Blocks := ep0000000000011110101_0
private theorem idp0000000000011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001111010.list =
    C ((2:ℤ)^30) * horner X vp0000000000011110101.list + horner X ep0000000000011110101.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011110101 : Branch 1 (-3574139/31250 : ℚ) vp000000000001111010 := by
  apply branch_checked idp0000000000011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3574139/31250 : ℚ) - ((1:ℤ):ℚ) = (-3589764/15625 : ℚ) by norm_num]
  exact coverp0000000000011110101
theorem coverp000000000001111010 : Covers (-3574139/31250 : ℚ) vp000000000001111010 := join_branches bp0000000000011110100 bp0000000000011110101
private noncomputable def vp00000000000111101_0 : Blocks := edgeBlocks% "full/vectors/00000000000111101-V-0000.bin"
noncomputable def vp00000000000111101 : Blocks := vp00000000000111101_0
private theorem bp000000000001111010 : Branch 0 (-3574139/62500 : ℚ) vp00000000000111101 := by
  apply branch_left_normalized (c:=vp000000000001111010) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-3574139/62500 : ℚ) - ((0:ℤ):ℚ) = (-3574139/31250 : ℚ) by norm_num]
  exact coverp000000000001111010
private noncomputable def ep000000000001111011_0 : Blocks := edgeBlocks% "full/vectors/000000000001111011-E-0000.bin"
noncomputable def ep000000000001111011 : Blocks := ep000000000001111011_0
private theorem idp000000000001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111101.list =
    C ((2:ℤ)^46) * horner X vp000000000001111011.list + horner X ep000000000001111011.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001111011 : Branch 1 (-3574139/62500 : ℚ) vp00000000000111101 := by
  apply branch_checked idp000000000001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3574139/62500 : ℚ) - ((1:ℤ):ℚ) = (-3605389/31250 : ℚ) by norm_num]
  exact coverp000000000001111011
theorem coverp00000000000111101 : Covers (-3574139/62500 : ℚ) vp00000000000111101 := join_branches bp000000000001111010 bp000000000001111011
private noncomputable def vp000000000001111001_0 : Blocks := edgeBlocks% "full/vectors/000000000001111001-V-0000.bin"
noncomputable def vp000000000001111001 : Blocks := vp000000000001111001_0
theorem coverp000000000001111001 : Covers (-3542889/31250 : ℚ) vp000000000001111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110001-V-0000.bin"
noncomputable def vp0000000000011110001 : Blocks := vp0000000000011110001_0
theorem coverp0000000000011110001 : Covers (-3527264/15625 : ℚ) vp0000000000011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111100001111_0 : Blocks := edgeBlocks% "full/vectors/00000000000111100001111-V-0000.bin"
noncomputable def vp00000000000111100001111 : Blocks := vp00000000000111100001111_0
theorem coverp00000000000111100001111 : Covers (-56420599/15625 : ℚ) vp00000000000111100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011110000111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110000111011-V-0000.bin"
noncomputable def vp0000000000011110000111011 : Blocks := vp0000000000011110000111011_0
theorem coverp0000000000011110000111011 : Covers (-225666771/15625 : ℚ) vp0000000000011110000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011110000111010_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110000111010-V-0000.bin"
noncomputable def vp0000000000011110000111010 : Blocks := vp0000000000011110000111010_0
theorem coverp0000000000011110000111010 : Covers (-225651146/15625 : ℚ) vp0000000000011110000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001111000011101_0 : Blocks := edgeBlocks% "full/vectors/000000000001111000011101-V-0000.bin"
noncomputable def vp000000000001111000011101 : Blocks := vp000000000001111000011101_0
private theorem bp0000000000011110000111010 : Branch 0 (-112825573/15625 : ℚ) vp000000000001111000011101 := by
  apply branch_left_normalized (c:=vp0000000000011110000111010) (k:=0) (m:=8) (by decide +kernel)
  rw [show 2*(-112825573/15625 : ℚ) - ((0:ℤ):ℚ) = (-225651146/15625 : ℚ) by norm_num]
  exact coverp0000000000011110000111010
private noncomputable def ep0000000000011110000111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110000111011-E-0000.bin"
noncomputable def ep0000000000011110000111011 : Blocks := ep0000000000011110000111011_0
private theorem idp0000000000011110000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001111000011101.list =
    C ((2:ℤ)^9) * horner X vp0000000000011110000111011.list + horner X ep0000000000011110000111011.list := by
  exact edge_identity (B := (2:ℤ)^107) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011110000111011 : Branch 1 (-112825573/15625 : ℚ) vp000000000001111000011101 := by
  apply branch_checked idp0000000000011110000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-112825573/15625 : ℚ) - ((1:ℤ):ℚ) = (-225666771/15625 : ℚ) by norm_num]
  exact coverp0000000000011110000111011
theorem coverp000000000001111000011101 : Covers (-112825573/15625 : ℚ) vp000000000001111000011101 := join_branches bp0000000000011110000111010 bp0000000000011110000111011
private noncomputable def vp000000000001111000011100_0 : Blocks := edgeBlocks% "full/vectors/000000000001111000011100-V-0000.bin"
noncomputable def vp000000000001111000011100 : Blocks := vp000000000001111000011100_0
theorem coverp000000000001111000011100 : Covers (-112809948/15625 : ℚ) vp000000000001111000011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111100001110_0 : Blocks := edgeBlocks% "full/vectors/00000000000111100001110-V-0000.bin"
noncomputable def vp00000000000111100001110 : Blocks := vp00000000000111100001110_0
private theorem bp000000000001111000011100 : Branch 0 (-56404974/15625 : ℚ) vp00000000000111100001110 := by
  apply branch_left_normalized (c:=vp000000000001111000011100) (k:=0) (m:=8) (by decide +kernel)
  rw [show 2*(-56404974/15625 : ℚ) - ((0:ℤ):ℚ) = (-112809948/15625 : ℚ) by norm_num]
  exact coverp000000000001111000011100
private noncomputable def ep000000000001111000011101_0 : Blocks := edgeBlocks% "full/vectors/000000000001111000011101-E-0000.bin"
noncomputable def ep000000000001111000011101 : Blocks := ep000000000001111000011101_0
private theorem idp000000000001111000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111100001110.list =
    C ((2:ℤ)^11) * horner X vp000000000001111000011101.list + horner X ep000000000001111000011101.list := by
  exact edge_identity (B := (2:ℤ)^111) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001111000011101 : Branch 1 (-56404974/15625 : ℚ) vp00000000000111100001110 := by
  apply branch_checked idp000000000001111000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-56404974/15625 : ℚ) - ((1:ℤ):ℚ) = (-112825573/15625 : ℚ) by norm_num]
  exact coverp000000000001111000011101
theorem coverp00000000000111100001110 : Covers (-56404974/15625 : ℚ) vp00000000000111100001110 := join_branches bp000000000001111000011100 bp000000000001111000011101
private noncomputable def vp0000000000011110000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110000111-V-0000.bin"
noncomputable def vp0000000000011110000111 : Blocks := vp0000000000011110000111_0
private theorem bp00000000000111100001110 : Branch 0 (-28202487/15625 : ℚ) vp0000000000011110000111 := by
  apply branch_left_normalized (c:=vp00000000000111100001110) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-28202487/15625 : ℚ) - ((0:ℤ):ℚ) = (-56404974/15625 : ℚ) by norm_num]
  exact coverp00000000000111100001110
private noncomputable def ep00000000000111100001111_0 : Blocks := edgeBlocks% "full/vectors/00000000000111100001111-E-0000.bin"
noncomputable def ep00000000000111100001111 : Blocks := ep00000000000111100001111_0
private theorem idp00000000000111100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011110000111.list =
    C ((2:ℤ)^13) * horner X vp00000000000111100001111.list + horner X ep00000000000111100001111.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111100001111 : Branch 1 (-28202487/15625 : ℚ) vp0000000000011110000111 := by
  apply branch_checked idp00000000000111100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-28202487/15625 : ℚ) - ((1:ℤ):ℚ) = (-56420599/15625 : ℚ) by norm_num]
  exact coverp00000000000111100001111
theorem coverp0000000000011110000111 : Covers (-28202487/15625 : ℚ) vp0000000000011110000111 := join_branches bp00000000000111100001110 bp00000000000111100001111
private noncomputable def vp00000000000111100001101_0 : Blocks := edgeBlocks% "full/vectors/00000000000111100001101-V-0000.bin"
noncomputable def vp00000000000111100001101 : Blocks := vp00000000000111100001101_0
theorem coverp00000000000111100001101 : Covers (-56389349/15625 : ℚ) vp00000000000111100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111100001100_0 : Blocks := edgeBlocks% "full/vectors/00000000000111100001100-V-0000.bin"
noncomputable def vp00000000000111100001100 : Blocks := vp00000000000111100001100_0
theorem coverp00000000000111100001100 : Covers (-56373724/15625 : ℚ) vp00000000000111100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011110000110_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110000110-V-0000.bin"
noncomputable def vp0000000000011110000110 : Blocks := vp0000000000011110000110_0
private theorem bp00000000000111100001100 : Branch 0 (-28186862/15625 : ℚ) vp0000000000011110000110 := by
  apply branch_left_normalized (c:=vp00000000000111100001100) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-28186862/15625 : ℚ) - ((0:ℤ):ℚ) = (-56373724/15625 : ℚ) by norm_num]
  exact coverp00000000000111100001100
private noncomputable def ep00000000000111100001101_0 : Blocks := edgeBlocks% "full/vectors/00000000000111100001101-E-0000.bin"
noncomputable def ep00000000000111100001101 : Blocks := ep00000000000111100001101_0
private theorem idp00000000000111100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011110000110.list =
    C ((2:ℤ)^12) * horner X vp00000000000111100001101.list + horner X ep00000000000111100001101.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111100001101 : Branch 1 (-28186862/15625 : ℚ) vp0000000000011110000110 := by
  apply branch_checked idp00000000000111100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-28186862/15625 : ℚ) - ((1:ℤ):ℚ) = (-56389349/15625 : ℚ) by norm_num]
  exact coverp00000000000111100001101
theorem coverp0000000000011110000110 : Covers (-28186862/15625 : ℚ) vp0000000000011110000110 := join_branches bp00000000000111100001100 bp00000000000111100001101
private noncomputable def vp000000000001111000011_0 : Blocks := edgeBlocks% "full/vectors/000000000001111000011-V-0000.bin"
noncomputable def vp000000000001111000011 : Blocks := vp000000000001111000011_0
private theorem bp0000000000011110000110 : Branch 0 (-14093431/15625 : ℚ) vp000000000001111000011 := by
  apply branch_left_normalized (c:=vp0000000000011110000110) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-14093431/15625 : ℚ) - ((0:ℤ):ℚ) = (-28186862/15625 : ℚ) by norm_num]
  exact coverp0000000000011110000110
private noncomputable def ep0000000000011110000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110000111-E-0000.bin"
noncomputable def ep0000000000011110000111 : Blocks := ep0000000000011110000111_0
private theorem idp0000000000011110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001111000011.list =
    C ((2:ℤ)^15) * horner X vp0000000000011110000111.list + horner X ep0000000000011110000111.list := by
  exact edge_identity (B := (2:ℤ)^119) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011110000111 : Branch 1 (-14093431/15625 : ℚ) vp000000000001111000011 := by
  apply branch_checked idp0000000000011110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-14093431/15625 : ℚ) - ((1:ℤ):ℚ) = (-28202487/15625 : ℚ) by norm_num]
  exact coverp0000000000011110000111
theorem coverp000000000001111000011 : Covers (-14093431/15625 : ℚ) vp000000000001111000011 := join_branches bp0000000000011110000110 bp0000000000011110000111
private noncomputable def vp000000000001111000010_0 : Blocks := edgeBlocks% "full/vectors/000000000001111000010-V-0000.bin"
noncomputable def vp000000000001111000010 : Blocks := vp000000000001111000010_0
theorem coverp000000000001111000010 : Covers (-14077806/15625 : ℚ) vp000000000001111000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000111100001-V-0000.bin"
noncomputable def vp00000000000111100001 : Blocks := vp00000000000111100001_0
private theorem bp000000000001111000010 : Branch 0 (-7038903/15625 : ℚ) vp00000000000111100001 := by
  apply branch_left_normalized (c:=vp000000000001111000010) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-7038903/15625 : ℚ) - ((0:ℤ):ℚ) = (-14077806/15625 : ℚ) by norm_num]
  exact coverp000000000001111000010
private noncomputable def ep000000000001111000011_0 : Blocks := edgeBlocks% "full/vectors/000000000001111000011-E-0000.bin"
noncomputable def ep000000000001111000011 : Blocks := ep000000000001111000011_0
private theorem idp000000000001111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111100001.list =
    C ((2:ℤ)^18) * horner X vp000000000001111000011.list + horner X ep000000000001111000011.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001111000011 : Branch 1 (-7038903/15625 : ℚ) vp00000000000111100001 := by
  apply branch_checked idp000000000001111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-7038903/15625 : ℚ) - ((1:ℤ):ℚ) = (-14093431/15625 : ℚ) by norm_num]
  exact coverp000000000001111000011
theorem coverp00000000000111100001 : Covers (-7038903/15625 : ℚ) vp00000000000111100001 := join_branches bp000000000001111000010 bp000000000001111000011
private noncomputable def vp00000000000111100000_0 : Blocks := edgeBlocks% "full/vectors/00000000000111100000-V-0000.bin"
noncomputable def vp00000000000111100000 : Blocks := vp00000000000111100000_0
theorem coverp00000000000111100000 : Covers (-7023278/15625 : ℚ) vp00000000000111100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011110000_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110000-V-0000.bin"
noncomputable def vp0000000000011110000 : Blocks := vp0000000000011110000_0
private theorem bp00000000000111100000 : Branch 0 (-3511639/15625 : ℚ) vp0000000000011110000 := by
  apply branch_left_normalized (c:=vp00000000000111100000) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-3511639/15625 : ℚ) - ((0:ℤ):ℚ) = (-7023278/15625 : ℚ) by norm_num]
  exact coverp00000000000111100000
private noncomputable def ep00000000000111100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000111100001-E-0000.bin"
noncomputable def ep00000000000111100001 : Blocks := ep00000000000111100001_0
private theorem idp00000000000111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011110000.list =
    C ((2:ℤ)^23) * horner X vp00000000000111100001.list + horner X ep00000000000111100001.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111100001 : Branch 1 (-3511639/15625 : ℚ) vp0000000000011110000 := by
  apply branch_checked idp00000000000111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-3511639/15625 : ℚ) - ((1:ℤ):ℚ) = (-7038903/15625 : ℚ) by norm_num]
  exact coverp00000000000111100001
theorem coverp0000000000011110000 : Covers (-3511639/15625 : ℚ) vp0000000000011110000 := join_branches bp00000000000111100000 bp00000000000111100001
private noncomputable def vp000000000001111000_0 : Blocks := edgeBlocks% "full/vectors/000000000001111000-V-0000.bin"
noncomputable def vp000000000001111000 : Blocks := vp000000000001111000_0
private theorem bp0000000000011110000 : Branch 0 (-3511639/31250 : ℚ) vp000000000001111000 := by
  apply branch_left_normalized (c:=vp0000000000011110000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-3511639/31250 : ℚ) - ((0:ℤ):ℚ) = (-3511639/15625 : ℚ) by norm_num]
  exact coverp0000000000011110000
private noncomputable def ep0000000000011110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110001-E-0000.bin"
noncomputable def ep0000000000011110001 : Blocks := ep0000000000011110001_0
private theorem idp0000000000011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001111000.list =
    C ((2:ℤ)^32) * horner X vp0000000000011110001.list + horner X ep0000000000011110001.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011110001 : Branch 1 (-3511639/31250 : ℚ) vp000000000001111000 := by
  apply branch_checked idp0000000000011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-3511639/31250 : ℚ) - ((1:ℤ):ℚ) = (-3527264/15625 : ℚ) by norm_num]
  exact coverp0000000000011110001
theorem coverp000000000001111000 : Covers (-3511639/31250 : ℚ) vp000000000001111000 := join_branches bp0000000000011110000 bp0000000000011110001
private noncomputable def vp00000000000111100_0 : Blocks := edgeBlocks% "full/vectors/00000000000111100-V-0000.bin"
noncomputable def vp00000000000111100 : Blocks := vp00000000000111100_0
private theorem bp000000000001111000 : Branch 0 (-3511639/62500 : ℚ) vp00000000000111100 := by
  apply branch_left_normalized (c:=vp000000000001111000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-3511639/62500 : ℚ) - ((0:ℤ):ℚ) = (-3511639/31250 : ℚ) by norm_num]
  exact coverp000000000001111000
private noncomputable def ep000000000001111001_0 : Blocks := edgeBlocks% "full/vectors/000000000001111001-E-0000.bin"
noncomputable def ep000000000001111001 : Blocks := ep000000000001111001_0
private theorem idp000000000001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111100.list =
    C ((2:ℤ)^50) * horner X vp000000000001111001.list + horner X ep000000000001111001.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001111001 : Branch 1 (-3511639/62500 : ℚ) vp00000000000111100 := by
  apply branch_checked idp000000000001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3511639/62500 : ℚ) - ((1:ℤ):ℚ) = (-3542889/31250 : ℚ) by norm_num]
  exact coverp000000000001111001
theorem coverp00000000000111100 : Covers (-3511639/62500 : ℚ) vp00000000000111100 := join_branches bp000000000001111000 bp000000000001111001
private noncomputable def vp0000000000011110_0 : Blocks := edgeBlocks% "full/vectors/0000000000011110-V-0000.bin"
noncomputable def vp0000000000011110 : Blocks := vp0000000000011110_0
private theorem bp00000000000111100 : Branch 0 (-3511639/125000 : ℚ) vp0000000000011110 := by
  apply branch_left_normalized (c:=vp00000000000111100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-3511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-3511639/62500 : ℚ) by norm_num]
  exact coverp00000000000111100
private noncomputable def ep00000000000111101_0 : Blocks := edgeBlocks% "full/vectors/00000000000111101-E-0000.bin"
noncomputable def ep00000000000111101 : Blocks := ep00000000000111101_0
private theorem idp00000000000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011110.list =
    C ((2:ℤ)^84) * horner X vp00000000000111101.list + horner X ep00000000000111101.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111101 : Branch 1 (-3511639/125000 : ℚ) vp0000000000011110 := by
  apply branch_checked idp00000000000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-3511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-3574139/62500 : ℚ) by norm_num]
  exact coverp00000000000111101
theorem coverp0000000000011110 : Covers (-3511639/125000 : ℚ) vp0000000000011110 := join_branches bp00000000000111100 bp00000000000111101
private noncomputable def vp000000000001111_0 : Blocks := edgeBlocks% "full/vectors/000000000001111-V-0000.bin"
private noncomputable def vp000000000001111_1 : Blocks := edgeBlocks% "full/vectors/000000000001111-V-0001.bin"
noncomputable def vp000000000001111 : Blocks := (Blocks.join vp000000000001111_0 vp000000000001111_1)
private theorem bp0000000000011110 : Branch 0 (-3511639/250000 : ℚ) vp000000000001111 := by
  apply branch_left_normalized (c:=vp0000000000011110) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-3511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-3511639/125000 : ℚ) by norm_num]
  exact coverp0000000000011110
private noncomputable def ep0000000000011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000011111-E-0000.bin"
private noncomputable def ep0000000000011111_1 : Blocks := edgeBlocks% "full/vectors/0000000000011111-E-0001.bin"
noncomputable def ep0000000000011111 : Blocks := (Blocks.join ep0000000000011111_0 ep0000000000011111_1)
private theorem idp0000000000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001111.list =
    C ((2:ℤ)^155) * horner X vp0000000000011111.list + horner X ep0000000000011111.list := by
  exact edge_identity (B := (2:ℤ)^313) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011111 : Branch 1 (-3511639/250000 : ℚ) vp000000000001111 := by
  apply branch_checked idp0000000000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-3511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-3636639/125000 : ℚ) by norm_num]
  exact coverp0000000000011111
theorem coverp000000000001111 : Covers (-3511639/250000 : ℚ) vp000000000001111 := join_branches bp0000000000011110 bp0000000000011111
private noncomputable def vp0000000000011101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101111-V-0000.bin"
noncomputable def vp0000000000011101111 : Blocks := vp0000000000011101111_0
theorem coverp0000000000011101111 : Covers (-3496014/15625 : ℚ) vp0000000000011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110111011_0 : Blocks := edgeBlocks% "full/vectors/000000000001110111011-V-0000.bin"
noncomputable def vp000000000001110111011 : Blocks := vp000000000001110111011_0
theorem coverp000000000001110111011 : Covers (-13968431/15625 : ℚ) vp000000000001110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110111010111_0 : Blocks := edgeBlocks% "full/vectors/000000000001110111010111-V-0000.bin"
noncomputable def vp000000000001110111010111 : Blocks := vp000000000001110111010111_0
theorem coverp000000000001110111010111 : Covers (-111731823/15625 : ℚ) vp000000000001110111010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110111010110_0 : Blocks := edgeBlocks% "full/vectors/000000000001110111010110-V-0000.bin"
noncomputable def vp000000000001110111010110 : Blocks := vp000000000001110111010110_0
theorem coverp000000000001110111010110 : Covers (-111716198/15625 : ℚ) vp000000000001110111010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111011101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011101011-V-0000.bin"
noncomputable def vp00000000000111011101011 : Blocks := vp00000000000111011101011_0
private theorem bp000000000001110111010110 : Branch 0 (-55858099/15625 : ℚ) vp00000000000111011101011 := by
  apply branch_left_normalized (c:=vp000000000001110111010110) (k:=0) (m:=9) (by decide +kernel)
  rw [show 2*(-55858099/15625 : ℚ) - ((0:ℤ):ℚ) = (-111716198/15625 : ℚ) by norm_num]
  exact coverp000000000001110111010110
private noncomputable def ep000000000001110111010111_0 : Blocks := edgeBlocks% "full/vectors/000000000001110111010111-E-0000.bin"
noncomputable def ep000000000001110111010111 : Blocks := ep000000000001110111010111_0
private theorem idp000000000001110111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111011101011.list =
    C ((2:ℤ)^11) * horner X vp000000000001110111010111.list + horner X ep000000000001110111010111.list := by
  exact edge_identity (B := (2:ℤ)^110) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001110111010111 : Branch 1 (-55858099/15625 : ℚ) vp00000000000111011101011 := by
  apply branch_checked idp000000000001110111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-55858099/15625 : ℚ) - ((1:ℤ):ℚ) = (-111731823/15625 : ℚ) by norm_num]
  exact coverp000000000001110111010111
theorem coverp00000000000111011101011 : Covers (-55858099/15625 : ℚ) vp00000000000111011101011 := join_branches bp000000000001110111010110 bp000000000001110111010111
private noncomputable def vp00000000000111011101010_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011101010-V-0000.bin"
noncomputable def vp00000000000111011101010 : Blocks := vp00000000000111011101010_0
theorem coverp00000000000111011101010 : Covers (-55842474/15625 : ℚ) vp00000000000111011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011101110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101110101-V-0000.bin"
noncomputable def vp0000000000011101110101 : Blocks := vp0000000000011101110101_0
private theorem bp00000000000111011101010 : Branch 0 (-27921237/15625 : ℚ) vp0000000000011101110101 := by
  apply branch_left_normalized (c:=vp00000000000111011101010) (k:=0) (m:=9) (by decide +kernel)
  rw [show 2*(-27921237/15625 : ℚ) - ((0:ℤ):ℚ) = (-55842474/15625 : ℚ) by norm_num]
  exact coverp00000000000111011101010
private noncomputable def ep00000000000111011101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011101011-E-0000.bin"
noncomputable def ep00000000000111011101011 : Blocks := ep00000000000111011101011_0
private theorem idp00000000000111011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011101110101.list =
    C ((2:ℤ)^12) * horner X vp00000000000111011101011.list + horner X ep00000000000111011101011.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111011101011 : Branch 1 (-27921237/15625 : ℚ) vp0000000000011101110101 := by
  apply branch_checked idp00000000000111011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-27921237/15625 : ℚ) - ((1:ℤ):ℚ) = (-55858099/15625 : ℚ) by norm_num]
  exact coverp00000000000111011101011
theorem coverp0000000000011101110101 : Covers (-27921237/15625 : ℚ) vp0000000000011101110101 := join_branches bp00000000000111011101010 bp00000000000111011101011
private noncomputable def vp0000000000011101110100_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101110100-V-0000.bin"
noncomputable def vp0000000000011101110100 : Blocks := vp0000000000011101110100_0
theorem coverp0000000000011101110100 : Covers (-27905612/15625 : ℚ) vp0000000000011101110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110111010_0 : Blocks := edgeBlocks% "full/vectors/000000000001110111010-V-0000.bin"
noncomputable def vp000000000001110111010 : Blocks := vp000000000001110111010_0
private theorem bp0000000000011101110100 : Branch 0 (-13952806/15625 : ℚ) vp000000000001110111010 := by
  apply branch_left_normalized (c:=vp0000000000011101110100) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-13952806/15625 : ℚ) - ((0:ℤ):ℚ) = (-27905612/15625 : ℚ) by norm_num]
  exact coverp0000000000011101110100
private noncomputable def ep0000000000011101110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101110101-E-0000.bin"
noncomputable def ep0000000000011101110101 : Blocks := ep0000000000011101110101_0
private theorem idp0000000000011101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001110111010.list =
    C ((2:ℤ)^15) * horner X vp0000000000011101110101.list + horner X ep0000000000011101110101.list := by
  exact edge_identity (B := (2:ℤ)^117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011101110101 : Branch 1 (-13952806/15625 : ℚ) vp000000000001110111010 := by
  apply branch_checked idp0000000000011101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-13952806/15625 : ℚ) - ((1:ℤ):ℚ) = (-27921237/15625 : ℚ) by norm_num]
  exact coverp0000000000011101110101
theorem coverp000000000001110111010 : Covers (-13952806/15625 : ℚ) vp000000000001110111010 := join_branches bp0000000000011101110100 bp0000000000011101110101
private noncomputable def vp00000000000111011101_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011101-V-0000.bin"
noncomputable def vp00000000000111011101 : Blocks := vp00000000000111011101_0
private theorem bp000000000001110111010 : Branch 0 (-6976403/15625 : ℚ) vp00000000000111011101 := by
  apply branch_left_normalized (c:=vp000000000001110111010) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-6976403/15625 : ℚ) - ((0:ℤ):ℚ) = (-13952806/15625 : ℚ) by norm_num]
  exact coverp000000000001110111010
private noncomputable def ep000000000001110111011_0 : Blocks := edgeBlocks% "full/vectors/000000000001110111011-E-0000.bin"
noncomputable def ep000000000001110111011 : Blocks := ep000000000001110111011_0
private theorem idp000000000001110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111011101.list =
    C ((2:ℤ)^19) * horner X vp000000000001110111011.list + horner X ep000000000001110111011.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001110111011 : Branch 1 (-6976403/15625 : ℚ) vp00000000000111011101 := by
  apply branch_checked idp000000000001110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-6976403/15625 : ℚ) - ((1:ℤ):ℚ) = (-13968431/15625 : ℚ) by norm_num]
  exact coverp000000000001110111011
theorem coverp00000000000111011101 : Covers (-6976403/15625 : ℚ) vp00000000000111011101 := join_branches bp000000000001110111010 bp000000000001110111011
private noncomputable def vp000000000001110111001_0 : Blocks := edgeBlocks% "full/vectors/000000000001110111001-V-0000.bin"
noncomputable def vp000000000001110111001 : Blocks := vp000000000001110111001_0
theorem coverp000000000001110111001 : Covers (-13937181/15625 : ℚ) vp000000000001110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110111000_0 : Blocks := edgeBlocks% "full/vectors/000000000001110111000-V-0000.bin"
noncomputable def vp000000000001110111000 : Blocks := vp000000000001110111000_0
theorem coverp000000000001110111000 : Covers (-13921556/15625 : ℚ) vp000000000001110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111011100_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011100-V-0000.bin"
noncomputable def vp00000000000111011100 : Blocks := vp00000000000111011100_0
private theorem bp000000000001110111000 : Branch 0 (-6960778/15625 : ℚ) vp00000000000111011100 := by
  apply branch_left_normalized (c:=vp000000000001110111000) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-6960778/15625 : ℚ) - ((0:ℤ):ℚ) = (-13921556/15625 : ℚ) by norm_num]
  exact coverp000000000001110111000
private noncomputable def ep000000000001110111001_0 : Blocks := edgeBlocks% "full/vectors/000000000001110111001-E-0000.bin"
noncomputable def ep000000000001110111001 : Blocks := ep000000000001110111001_0
private theorem idp000000000001110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111011100.list =
    C ((2:ℤ)^18) * horner X vp000000000001110111001.list + horner X ep000000000001110111001.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001110111001 : Branch 1 (-6960778/15625 : ℚ) vp00000000000111011100 := by
  apply branch_checked idp000000000001110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-6960778/15625 : ℚ) - ((1:ℤ):ℚ) = (-13937181/15625 : ℚ) by norm_num]
  exact coverp000000000001110111001
theorem coverp00000000000111011100 : Covers (-6960778/15625 : ℚ) vp00000000000111011100 := join_branches bp000000000001110111000 bp000000000001110111001
private noncomputable def vp0000000000011101110_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101110-V-0000.bin"
noncomputable def vp0000000000011101110 : Blocks := vp0000000000011101110_0
private theorem bp00000000000111011100 : Branch 0 (-3480389/15625 : ℚ) vp0000000000011101110 := by
  apply branch_left_normalized (c:=vp00000000000111011100) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-3480389/15625 : ℚ) - ((0:ℤ):ℚ) = (-6960778/15625 : ℚ) by norm_num]
  exact coverp00000000000111011100
private noncomputable def ep00000000000111011101_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011101-E-0000.bin"
noncomputable def ep00000000000111011101 : Blocks := ep00000000000111011101_0
private theorem idp00000000000111011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011101110.list =
    C ((2:ℤ)^23) * horner X vp00000000000111011101.list + horner X ep00000000000111011101.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111011101 : Branch 1 (-3480389/15625 : ℚ) vp0000000000011101110 := by
  apply branch_checked idp00000000000111011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3480389/15625 : ℚ) - ((1:ℤ):ℚ) = (-6976403/15625 : ℚ) by norm_num]
  exact coverp00000000000111011101
theorem coverp0000000000011101110 : Covers (-3480389/15625 : ℚ) vp0000000000011101110 := join_branches bp00000000000111011100 bp00000000000111011101
private noncomputable def vp000000000001110111_0 : Blocks := edgeBlocks% "full/vectors/000000000001110111-V-0000.bin"
noncomputable def vp000000000001110111 : Blocks := vp000000000001110111_0
private theorem bp0000000000011101110 : Branch 0 (-3480389/31250 : ℚ) vp000000000001110111 := by
  apply branch_left_normalized (c:=vp0000000000011101110) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-3480389/31250 : ℚ) - ((0:ℤ):ℚ) = (-3480389/15625 : ℚ) by norm_num]
  exact coverp0000000000011101110
private noncomputable def ep0000000000011101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101111-E-0000.bin"
noncomputable def ep0000000000011101111 : Blocks := ep0000000000011101111_0
private theorem idp0000000000011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001110111.list =
    C ((2:ℤ)^33) * horner X vp0000000000011101111.list + horner X ep0000000000011101111.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011101111 : Branch 1 (-3480389/31250 : ℚ) vp000000000001110111 := by
  apply branch_checked idp0000000000011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3480389/31250 : ℚ) - ((1:ℤ):ℚ) = (-3496014/15625 : ℚ) by norm_num]
  exact coverp0000000000011101111
theorem coverp000000000001110111 : Covers (-3480389/31250 : ℚ) vp000000000001110111 := join_branches bp0000000000011101110 bp0000000000011101111
private noncomputable def vp0000000000011101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101101-V-0000.bin"
noncomputable def vp0000000000011101101 : Blocks := vp0000000000011101101_0
theorem coverp0000000000011101101 : Covers (-3464764/15625 : ℚ) vp0000000000011101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111011001_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011001-V-0000.bin"
noncomputable def vp00000000000111011001 : Blocks := vp00000000000111011001_0
theorem coverp00000000000111011001 : Covers (-6913903/15625 : ℚ) vp00000000000111011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110110001_0 : Blocks := edgeBlocks% "full/vectors/000000000001110110001-V-0000.bin"
noncomputable def vp000000000001110110001 : Blocks := vp000000000001110110001_0
theorem coverp000000000001110110001 : Covers (-13812181/15625 : ℚ) vp000000000001110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111011000011_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011000011-V-0000.bin"
noncomputable def vp00000000000111011000011 : Blocks := vp00000000000111011000011_0
theorem coverp00000000000111011000011 : Covers (-55233099/15625 : ℚ) vp00000000000111011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110110000101_0 : Blocks := edgeBlocks% "full/vectors/000000000001110110000101-V-0000.bin"
noncomputable def vp000000000001110110000101 : Blocks := vp000000000001110110000101_0
theorem coverp000000000001110110000101 : Covers (-110450573/15625 : ℚ) vp000000000001110110000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110110000100_0 : Blocks := edgeBlocks% "full/vectors/000000000001110110000100-V-0000.bin"
noncomputable def vp000000000001110110000100 : Blocks := vp000000000001110110000100_0
theorem coverp000000000001110110000100 : Covers (-110434948/15625 : ℚ) vp000000000001110110000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111011000010_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011000010-V-0000.bin"
noncomputable def vp00000000000111011000010 : Blocks := vp00000000000111011000010_0
private theorem bp000000000001110110000100 : Branch 0 (-55217474/15625 : ℚ) vp00000000000111011000010 := by
  apply branch_left_normalized (c:=vp000000000001110110000100) (k:=0) (m:=8) (by decide +kernel)
  rw [show 2*(-55217474/15625 : ℚ) - ((0:ℤ):ℚ) = (-110434948/15625 : ℚ) by norm_num]
  exact coverp000000000001110110000100
private noncomputable def ep000000000001110110000101_0 : Blocks := edgeBlocks% "full/vectors/000000000001110110000101-E-0000.bin"
noncomputable def ep000000000001110110000101 : Blocks := ep000000000001110110000101_0
private theorem idp000000000001110110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111011000010.list =
    C ((2:ℤ)^11) * horner X vp000000000001110110000101.list + horner X ep000000000001110110000101.list := by
  exact edge_identity (B := (2:ℤ)^110) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001110110000101 : Branch 1 (-55217474/15625 : ℚ) vp00000000000111011000010 := by
  apply branch_checked idp000000000001110110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-55217474/15625 : ℚ) - ((1:ℤ):ℚ) = (-110450573/15625 : ℚ) by norm_num]
  exact coverp000000000001110110000101
theorem coverp00000000000111011000010 : Covers (-55217474/15625 : ℚ) vp00000000000111011000010 := join_branches bp000000000001110110000100 bp000000000001110110000101
private noncomputable def vp0000000000011101100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101100001-V-0000.bin"
noncomputable def vp0000000000011101100001 : Blocks := vp0000000000011101100001_0
private theorem bp00000000000111011000010 : Branch 0 (-27608737/15625 : ℚ) vp0000000000011101100001 := by
  apply branch_left_normalized (c:=vp00000000000111011000010) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-27608737/15625 : ℚ) - ((0:ℤ):ℚ) = (-55217474/15625 : ℚ) by norm_num]
  exact coverp00000000000111011000010
private noncomputable def ep00000000000111011000011_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011000011-E-0000.bin"
noncomputable def ep00000000000111011000011 : Blocks := ep00000000000111011000011_0
private theorem idp00000000000111011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011101100001.list =
    C ((2:ℤ)^13) * horner X vp00000000000111011000011.list + horner X ep00000000000111011000011.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111011000011 : Branch 1 (-27608737/15625 : ℚ) vp0000000000011101100001 := by
  apply branch_checked idp00000000000111011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-27608737/15625 : ℚ) - ((1:ℤ):ℚ) = (-55233099/15625 : ℚ) by norm_num]
  exact coverp00000000000111011000011
theorem coverp0000000000011101100001 : Covers (-27608737/15625 : ℚ) vp0000000000011101100001 := join_branches bp00000000000111011000010 bp00000000000111011000011
private noncomputable def vp000000000001110110000011_0 : Blocks := edgeBlocks% "full/vectors/000000000001110110000011-V-0000.bin"
noncomputable def vp000000000001110110000011 : Blocks := vp000000000001110110000011_0
theorem coverp000000000001110110000011 : Covers (-110419323/15625 : ℚ) vp000000000001110110000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110110000010_0 : Blocks := edgeBlocks% "full/vectors/000000000001110110000010-V-0000.bin"
noncomputable def vp000000000001110110000010 : Blocks := vp000000000001110110000010_0
theorem coverp000000000001110110000010 : Covers (-110403698/15625 : ℚ) vp000000000001110110000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111011000001_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011000001-V-0000.bin"
noncomputable def vp00000000000111011000001 : Blocks := vp00000000000111011000001_0
private theorem bp000000000001110110000010 : Branch 0 (-55201849/15625 : ℚ) vp00000000000111011000001 := by
  apply branch_left_normalized (c:=vp000000000001110110000010) (k:=0) (m:=8) (by decide +kernel)
  rw [show 2*(-55201849/15625 : ℚ) - ((0:ℤ):ℚ) = (-110403698/15625 : ℚ) by norm_num]
  exact coverp000000000001110110000010
private noncomputable def ep000000000001110110000011_0 : Blocks := edgeBlocks% "full/vectors/000000000001110110000011-E-0000.bin"
noncomputable def ep000000000001110110000011 : Blocks := ep000000000001110110000011_0
private theorem idp000000000001110110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111011000001.list =
    C ((2:ℤ)^11) * horner X vp000000000001110110000011.list + horner X ep000000000001110110000011.list := by
  exact edge_identity (B := (2:ℤ)^111) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001110110000011 : Branch 1 (-55201849/15625 : ℚ) vp00000000000111011000001 := by
  apply branch_checked idp000000000001110110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-55201849/15625 : ℚ) - ((1:ℤ):ℚ) = (-110419323/15625 : ℚ) by norm_num]
  exact coverp000000000001110110000011
theorem coverp00000000000111011000001 : Covers (-55201849/15625 : ℚ) vp00000000000111011000001 := join_branches bp000000000001110110000010 bp000000000001110110000011
private noncomputable def vp00000000000111011000000_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011000000-V-0000.bin"
noncomputable def vp00000000000111011000000 : Blocks := vp00000000000111011000000_0
theorem coverp00000000000111011000000 : Covers (-55186224/15625 : ℚ) vp00000000000111011000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011101100000_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101100000-V-0000.bin"
noncomputable def vp0000000000011101100000 : Blocks := vp0000000000011101100000_0
private theorem bp00000000000111011000000 : Branch 0 (-27593112/15625 : ℚ) vp0000000000011101100000 := by
  apply branch_left_normalized (c:=vp00000000000111011000000) (k:=0) (m:=9) (by decide +kernel)
  rw [show 2*(-27593112/15625 : ℚ) - ((0:ℤ):ℚ) = (-55186224/15625 : ℚ) by norm_num]
  exact coverp00000000000111011000000
private noncomputable def ep00000000000111011000001_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011000001-E-0000.bin"
noncomputable def ep00000000000111011000001 : Blocks := ep00000000000111011000001_0
private theorem idp00000000000111011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011101100000.list =
    C ((2:ℤ)^12) * horner X vp00000000000111011000001.list + horner X ep00000000000111011000001.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111011000001 : Branch 1 (-27593112/15625 : ℚ) vp0000000000011101100000 := by
  apply branch_checked idp00000000000111011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-27593112/15625 : ℚ) - ((1:ℤ):ℚ) = (-55201849/15625 : ℚ) by norm_num]
  exact coverp00000000000111011000001
theorem coverp0000000000011101100000 : Covers (-27593112/15625 : ℚ) vp0000000000011101100000 := join_branches bp00000000000111011000000 bp00000000000111011000001
private noncomputable def vp000000000001110110000_0 : Blocks := edgeBlocks% "full/vectors/000000000001110110000-V-0000.bin"
noncomputable def vp000000000001110110000 : Blocks := vp000000000001110110000_0
private theorem bp0000000000011101100000 : Branch 0 (-13796556/15625 : ℚ) vp000000000001110110000 := by
  apply branch_left_normalized (c:=vp0000000000011101100000) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-13796556/15625 : ℚ) - ((0:ℤ):ℚ) = (-27593112/15625 : ℚ) by norm_num]
  exact coverp0000000000011101100000
private noncomputable def ep0000000000011101100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101100001-E-0000.bin"
noncomputable def ep0000000000011101100001 : Blocks := ep0000000000011101100001_0
private theorem idp0000000000011101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001110110000.list =
    C ((2:ℤ)^15) * horner X vp0000000000011101100001.list + horner X ep0000000000011101100001.list := by
  exact edge_identity (B := (2:ℤ)^117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011101100001 : Branch 1 (-13796556/15625 : ℚ) vp000000000001110110000 := by
  apply branch_checked idp0000000000011101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-13796556/15625 : ℚ) - ((1:ℤ):ℚ) = (-27608737/15625 : ℚ) by norm_num]
  exact coverp0000000000011101100001
theorem coverp000000000001110110000 : Covers (-13796556/15625 : ℚ) vp000000000001110110000 := join_branches bp0000000000011101100000 bp0000000000011101100001
private noncomputable def vp00000000000111011000_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011000-V-0000.bin"
noncomputable def vp00000000000111011000 : Blocks := vp00000000000111011000_0
private theorem bp000000000001110110000 : Branch 0 (-6898278/15625 : ℚ) vp00000000000111011000 := by
  apply branch_left_normalized (c:=vp000000000001110110000) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-6898278/15625 : ℚ) - ((0:ℤ):ℚ) = (-13796556/15625 : ℚ) by norm_num]
  exact coverp000000000001110110000
private noncomputable def ep000000000001110110001_0 : Blocks := edgeBlocks% "full/vectors/000000000001110110001-E-0000.bin"
noncomputable def ep000000000001110110001 : Blocks := ep000000000001110110001_0
private theorem idp000000000001110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111011000.list =
    C ((2:ℤ)^18) * horner X vp000000000001110110001.list + horner X ep000000000001110110001.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001110110001 : Branch 1 (-6898278/15625 : ℚ) vp00000000000111011000 := by
  apply branch_checked idp000000000001110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-6898278/15625 : ℚ) - ((1:ℤ):ℚ) = (-13812181/15625 : ℚ) by norm_num]
  exact coverp000000000001110110001
theorem coverp00000000000111011000 : Covers (-6898278/15625 : ℚ) vp00000000000111011000 := join_branches bp000000000001110110000 bp000000000001110110001
private noncomputable def vp0000000000011101100_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101100-V-0000.bin"
noncomputable def vp0000000000011101100 : Blocks := vp0000000000011101100_0
private theorem bp00000000000111011000 : Branch 0 (-3449139/15625 : ℚ) vp0000000000011101100 := by
  apply branch_left_normalized (c:=vp00000000000111011000) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-3449139/15625 : ℚ) - ((0:ℤ):ℚ) = (-6898278/15625 : ℚ) by norm_num]
  exact coverp00000000000111011000
private noncomputable def ep00000000000111011001_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011001-E-0000.bin"
noncomputable def ep00000000000111011001 : Blocks := ep00000000000111011001_0
private theorem idp00000000000111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011101100.list =
    C ((2:ℤ)^24) * horner X vp00000000000111011001.list + horner X ep00000000000111011001.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111011001 : Branch 1 (-3449139/15625 : ℚ) vp0000000000011101100 := by
  apply branch_checked idp00000000000111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-3449139/15625 : ℚ) - ((1:ℤ):ℚ) = (-6913903/15625 : ℚ) by norm_num]
  exact coverp00000000000111011001
theorem coverp0000000000011101100 : Covers (-3449139/15625 : ℚ) vp0000000000011101100 := join_branches bp00000000000111011000 bp00000000000111011001
private noncomputable def vp000000000001110110_0 : Blocks := edgeBlocks% "full/vectors/000000000001110110-V-0000.bin"
noncomputable def vp000000000001110110 : Blocks := vp000000000001110110_0
private theorem bp0000000000011101100 : Branch 0 (-3449139/31250 : ℚ) vp000000000001110110 := by
  apply branch_left_normalized (c:=vp0000000000011101100) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-3449139/31250 : ℚ) - ((0:ℤ):ℚ) = (-3449139/15625 : ℚ) by norm_num]
  exact coverp0000000000011101100
private noncomputable def ep0000000000011101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101101-E-0000.bin"
noncomputable def ep0000000000011101101 : Blocks := ep0000000000011101101_0
private theorem idp0000000000011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001110110.list =
    C ((2:ℤ)^33) * horner X vp0000000000011101101.list + horner X ep0000000000011101101.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011101101 : Branch 1 (-3449139/31250 : ℚ) vp000000000001110110 := by
  apply branch_checked idp0000000000011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-3449139/31250 : ℚ) - ((1:ℤ):ℚ) = (-3464764/15625 : ℚ) by norm_num]
  exact coverp0000000000011101101
theorem coverp000000000001110110 : Covers (-3449139/31250 : ℚ) vp000000000001110110 := join_branches bp0000000000011101100 bp0000000000011101101
private noncomputable def vp00000000000111011_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011-V-0000.bin"
noncomputable def vp00000000000111011 : Blocks := vp00000000000111011_0
private theorem bp000000000001110110 : Branch 0 (-3449139/62500 : ℚ) vp00000000000111011 := by
  apply branch_left_normalized (c:=vp000000000001110110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-3449139/62500 : ℚ) - ((0:ℤ):ℚ) = (-3449139/31250 : ℚ) by norm_num]
  exact coverp000000000001110110
private noncomputable def ep000000000001110111_0 : Blocks := edgeBlocks% "full/vectors/000000000001110111-E-0000.bin"
noncomputable def ep000000000001110111 : Blocks := ep000000000001110111_0
private theorem idp000000000001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111011.list =
    C ((2:ℤ)^53) * horner X vp000000000001110111.list + horner X ep000000000001110111.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001110111 : Branch 1 (-3449139/62500 : ℚ) vp00000000000111011 := by
  apply branch_checked idp000000000001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3449139/62500 : ℚ) - ((1:ℤ):ℚ) = (-3480389/31250 : ℚ) by norm_num]
  exact coverp000000000001110111
theorem coverp00000000000111011 : Covers (-3449139/62500 : ℚ) vp00000000000111011 := join_branches bp000000000001110110 bp000000000001110111
private noncomputable def vp0000000000011101011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101011111-V-0000.bin"
noncomputable def vp0000000000011101011111 : Blocks := vp0000000000011101011111_0
theorem coverp0000000000011101011111 : Covers (-27577487/15625 : ℚ) vp0000000000011101011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011101011110_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101011110-V-0000.bin"
noncomputable def vp0000000000011101011110 : Blocks := vp0000000000011101011110_0
theorem coverp0000000000011101011110 : Covers (-27561862/15625 : ℚ) vp0000000000011101011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110101111_0 : Blocks := edgeBlocks% "full/vectors/000000000001110101111-V-0000.bin"
noncomputable def vp000000000001110101111 : Blocks := vp000000000001110101111_0
private theorem bp0000000000011101011110 : Branch 0 (-13780931/15625 : ℚ) vp000000000001110101111 := by
  apply branch_left_normalized (c:=vp0000000000011101011110) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-13780931/15625 : ℚ) - ((0:ℤ):ℚ) = (-27561862/15625 : ℚ) by norm_num]
  exact coverp0000000000011101011110
private noncomputable def ep0000000000011101011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101011111-E-0000.bin"
noncomputable def ep0000000000011101011111 : Blocks := ep0000000000011101011111_0
private theorem idp0000000000011101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001110101111.list =
    C ((2:ℤ)^14) * horner X vp0000000000011101011111.list + horner X ep0000000000011101011111.list := by
  exact edge_identity (B := (2:ℤ)^118) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011101011111 : Branch 1 (-13780931/15625 : ℚ) vp000000000001110101111 := by
  apply branch_checked idp0000000000011101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-13780931/15625 : ℚ) - ((1:ℤ):ℚ) = (-27577487/15625 : ℚ) by norm_num]
  exact coverp0000000000011101011111
theorem coverp000000000001110101111 : Covers (-13780931/15625 : ℚ) vp000000000001110101111 := join_branches bp0000000000011101011110 bp0000000000011101011111
private noncomputable def vp000000000001110101110_0 : Blocks := edgeBlocks% "full/vectors/000000000001110101110-V-0000.bin"
noncomputable def vp000000000001110101110 : Blocks := vp000000000001110101110_0
theorem coverp000000000001110101110 : Covers (-13765306/15625 : ℚ) vp000000000001110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111010111_0 : Blocks := edgeBlocks% "full/vectors/00000000000111010111-V-0000.bin"
noncomputable def vp00000000000111010111 : Blocks := vp00000000000111010111_0
private theorem bp000000000001110101110 : Branch 0 (-6882653/15625 : ℚ) vp00000000000111010111 := by
  apply branch_left_normalized (c:=vp000000000001110101110) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-6882653/15625 : ℚ) - ((0:ℤ):ℚ) = (-13765306/15625 : ℚ) by norm_num]
  exact coverp000000000001110101110
private noncomputable def ep000000000001110101111_0 : Blocks := edgeBlocks% "full/vectors/000000000001110101111-E-0000.bin"
noncomputable def ep000000000001110101111 : Blocks := ep000000000001110101111_0
private theorem idp000000000001110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111010111.list =
    C ((2:ℤ)^17) * horner X vp000000000001110101111.list + horner X ep000000000001110101111.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001110101111 : Branch 1 (-6882653/15625 : ℚ) vp00000000000111010111 := by
  apply branch_checked idp000000000001110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-6882653/15625 : ℚ) - ((1:ℤ):ℚ) = (-13780931/15625 : ℚ) by norm_num]
  exact coverp000000000001110101111
theorem coverp00000000000111010111 : Covers (-6882653/15625 : ℚ) vp00000000000111010111 := join_branches bp000000000001110101110 bp000000000001110101111
private noncomputable def vp00000000000111010110_0 : Blocks := edgeBlocks% "full/vectors/00000000000111010110-V-0000.bin"
noncomputable def vp00000000000111010110 : Blocks := vp00000000000111010110_0
theorem coverp00000000000111010110 : Covers (-6867028/15625 : ℚ) vp00000000000111010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011101011_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101011-V-0000.bin"
noncomputable def vp0000000000011101011 : Blocks := vp0000000000011101011_0
private theorem bp00000000000111010110 : Branch 0 (-3433514/15625 : ℚ) vp0000000000011101011 := by
  apply branch_left_normalized (c:=vp00000000000111010110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-3433514/15625 : ℚ) - ((0:ℤ):ℚ) = (-6867028/15625 : ℚ) by norm_num]
  exact coverp00000000000111010110
private noncomputable def ep00000000000111010111_0 : Blocks := edgeBlocks% "full/vectors/00000000000111010111-E-0000.bin"
noncomputable def ep00000000000111010111 : Blocks := ep00000000000111010111_0
private theorem idp00000000000111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011101011.list =
    C ((2:ℤ)^22) * horner X vp00000000000111010111.list + horner X ep00000000000111010111.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111010111 : Branch 1 (-3433514/15625 : ℚ) vp0000000000011101011 := by
  apply branch_checked idp00000000000111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-3433514/15625 : ℚ) - ((1:ℤ):ℚ) = (-6882653/15625 : ℚ) by norm_num]
  exact coverp00000000000111010111
theorem coverp0000000000011101011 : Covers (-3433514/15625 : ℚ) vp0000000000011101011 := join_branches bp00000000000111010110 bp00000000000111010111
private noncomputable def vp0000000000011101010_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101010-V-0000.bin"
noncomputable def vp0000000000011101010 : Blocks := vp0000000000011101010_0
theorem coverp0000000000011101010 : Covers (-3417889/15625 : ℚ) vp0000000000011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110101_0 : Blocks := edgeBlocks% "full/vectors/000000000001110101-V-0000.bin"
noncomputable def vp000000000001110101 : Blocks := vp000000000001110101_0
private theorem bp0000000000011101010 : Branch 0 (-3417889/31250 : ℚ) vp000000000001110101 := by
  apply branch_left_normalized (c:=vp0000000000011101010) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-3417889/31250 : ℚ) - ((0:ℤ):ℚ) = (-3417889/15625 : ℚ) by norm_num]
  exact coverp0000000000011101010
private noncomputable def ep0000000000011101011_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101011-E-0000.bin"
noncomputable def ep0000000000011101011 : Blocks := ep0000000000011101011_0
private theorem idp0000000000011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001110101.list =
    C ((2:ℤ)^31) * horner X vp0000000000011101011.list + horner X ep0000000000011101011.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011101011 : Branch 1 (-3417889/31250 : ℚ) vp000000000001110101 := by
  apply branch_checked idp0000000000011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-3417889/31250 : ℚ) - ((1:ℤ):ℚ) = (-3433514/15625 : ℚ) by norm_num]
  exact coverp0000000000011101011
theorem coverp000000000001110101 : Covers (-3417889/31250 : ℚ) vp000000000001110101 := join_branches bp0000000000011101010 bp0000000000011101011
private noncomputable def vp000000000001110100_0 : Blocks := edgeBlocks% "full/vectors/000000000001110100-V-0000.bin"
noncomputable def vp000000000001110100 : Blocks := vp000000000001110100_0
theorem coverp000000000001110100 : Covers (-3386639/31250 : ℚ) vp000000000001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111010_0 : Blocks := edgeBlocks% "full/vectors/00000000000111010-V-0000.bin"
noncomputable def vp00000000000111010 : Blocks := vp00000000000111010_0
private theorem bp000000000001110100 : Branch 0 (-3386639/62500 : ℚ) vp00000000000111010 := by
  apply branch_left_normalized (c:=vp000000000001110100) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-3386639/62500 : ℚ) - ((0:ℤ):ℚ) = (-3386639/31250 : ℚ) by norm_num]
  exact coverp000000000001110100
private noncomputable def ep000000000001110101_0 : Blocks := edgeBlocks% "full/vectors/000000000001110101-E-0000.bin"
noncomputable def ep000000000001110101 : Blocks := ep000000000001110101_0
private theorem idp000000000001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111010.list =
    C ((2:ℤ)^48) * horner X vp000000000001110101.list + horner X ep000000000001110101.list := by
  exact edge_identity (B := (2:ℤ)^161) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001110101 : Branch 1 (-3386639/62500 : ℚ) vp00000000000111010 := by
  apply branch_checked idp000000000001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3386639/62500 : ℚ) - ((1:ℤ):ℚ) = (-3417889/31250 : ℚ) by norm_num]
  exact coverp000000000001110101
theorem coverp00000000000111010 : Covers (-3386639/62500 : ℚ) vp00000000000111010 := join_branches bp000000000001110100 bp000000000001110101
private noncomputable def vp0000000000011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101-V-0000.bin"
noncomputable def vp0000000000011101 : Blocks := vp0000000000011101_0
private theorem bp00000000000111010 : Branch 0 (-3386639/125000 : ℚ) vp0000000000011101 := by
  apply branch_left_normalized (c:=vp00000000000111010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-3386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-3386639/62500 : ℚ) by norm_num]
  exact coverp00000000000111010
private noncomputable def ep00000000000111011_0 : Blocks := edgeBlocks% "full/vectors/00000000000111011-E-0000.bin"
noncomputable def ep00000000000111011 : Blocks := ep00000000000111011_0
private theorem idp00000000000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011101.list =
    C ((2:ℤ)^80) * horner X vp00000000000111011.list + horner X ep00000000000111011.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111011 : Branch 1 (-3386639/125000 : ℚ) vp0000000000011101 := by
  apply branch_checked idp00000000000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-3386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-3449139/62500 : ℚ) by norm_num]
  exact coverp00000000000111011
theorem coverp0000000000011101 : Covers (-3386639/125000 : ℚ) vp0000000000011101 := join_branches bp00000000000111010 bp00000000000111011
private noncomputable def vp000000000001110011_0 : Blocks := edgeBlocks% "full/vectors/000000000001110011-V-0000.bin"
noncomputable def vp000000000001110011 : Blocks := vp000000000001110011_0
theorem coverp000000000001110011 : Covers (-3355389/31250 : ℚ) vp000000000001110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001110010_0 : Blocks := edgeBlocks% "full/vectors/000000000001110010-V-0000.bin"
noncomputable def vp000000000001110010 : Blocks := vp000000000001110010_0
theorem coverp000000000001110010 : Covers (-3324139/31250 : ℚ) vp000000000001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000111001_0 : Blocks := edgeBlocks% "full/vectors/00000000000111001-V-0000.bin"
noncomputable def vp00000000000111001 : Blocks := vp00000000000111001_0
private theorem bp000000000001110010 : Branch 0 (-3324139/62500 : ℚ) vp00000000000111001 := by
  apply branch_left_normalized (c:=vp000000000001110010) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-3324139/62500 : ℚ) - ((0:ℤ):ℚ) = (-3324139/31250 : ℚ) by norm_num]
  exact coverp000000000001110010
private noncomputable def ep000000000001110011_0 : Blocks := edgeBlocks% "full/vectors/000000000001110011-E-0000.bin"
noncomputable def ep000000000001110011 : Blocks := ep000000000001110011_0
private theorem idp000000000001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111001.list =
    C ((2:ℤ)^48) * horner X vp000000000001110011.list + horner X ep000000000001110011.list := by
  exact edge_identity (B := (2:ℤ)^161) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001110011 : Branch 1 (-3324139/62500 : ℚ) vp00000000000111001 := by
  apply branch_checked idp000000000001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-3324139/62500 : ℚ) - ((1:ℤ):ℚ) = (-3355389/31250 : ℚ) by norm_num]
  exact coverp000000000001110011
theorem coverp00000000000111001 : Covers (-3324139/62500 : ℚ) vp00000000000111001 := join_branches bp000000000001110010 bp000000000001110011
private noncomputable def vp00000000000111000_0 : Blocks := edgeBlocks% "full/vectors/00000000000111000-V-0000.bin"
noncomputable def vp00000000000111000 : Blocks := vp00000000000111000_0
theorem coverp00000000000111000 : Covers (-3261639/62500 : ℚ) vp00000000000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011100_0 : Blocks := edgeBlocks% "full/vectors/0000000000011100-V-0000.bin"
noncomputable def vp0000000000011100 : Blocks := vp0000000000011100_0
private theorem bp00000000000111000 : Branch 0 (-3261639/125000 : ℚ) vp0000000000011100 := by
  apply branch_left_normalized (c:=vp00000000000111000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-3261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-3261639/62500 : ℚ) by norm_num]
  exact coverp00000000000111000
private noncomputable def ep00000000000111001_0 : Blocks := edgeBlocks% "full/vectors/00000000000111001-E-0000.bin"
noncomputable def ep00000000000111001 : Blocks := ep00000000000111001_0
private theorem idp00000000000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011100.list =
    C ((2:ℤ)^81) * horner X vp00000000000111001.list + horner X ep00000000000111001.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111001 : Branch 1 (-3261639/125000 : ℚ) vp0000000000011100 := by
  apply branch_checked idp00000000000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-3261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-3324139/62500 : ℚ) by norm_num]
  exact coverp00000000000111001
theorem coverp0000000000011100 : Covers (-3261639/125000 : ℚ) vp0000000000011100 := join_branches bp00000000000111000 bp00000000000111001
private noncomputable def vp000000000001110_0 : Blocks := edgeBlocks% "full/vectors/000000000001110-V-0000.bin"
private noncomputable def vp000000000001110_1 : Blocks := edgeBlocks% "full/vectors/000000000001110-V-0001.bin"
noncomputable def vp000000000001110 : Blocks := (Blocks.join vp000000000001110_0 vp000000000001110_1)
private theorem bp0000000000011100 : Branch 0 (-3261639/250000 : ℚ) vp000000000001110 := by
  apply branch_left_normalized (c:=vp0000000000011100) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-3261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-3261639/125000 : ℚ) by norm_num]
  exact coverp0000000000011100
private noncomputable def ep0000000000011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000011101-E-0000.bin"
private noncomputable def ep0000000000011101_1 : Blocks := edgeBlocks% "full/vectors/0000000000011101-E-0001.bin"
noncomputable def ep0000000000011101 : Blocks := (Blocks.join ep0000000000011101_0 ep0000000000011101_1)
private theorem idp0000000000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001110.list =
    C ((2:ℤ)^147) * horner X vp0000000000011101.list + horner X ep0000000000011101.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011101 : Branch 1 (-3261639/250000 : ℚ) vp000000000001110 := by
  apply branch_checked idp0000000000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-3386639/125000 : ℚ) by norm_num]
  exact coverp0000000000011101
theorem coverp000000000001110 : Covers (-3261639/250000 : ℚ) vp000000000001110 := join_branches bp0000000000011100 bp0000000000011101
private noncomputable def vp00000000000111_0 : Blocks := edgeBlocks% "full/vectors/00000000000111-V-0000.bin"
private noncomputable def vp00000000000111_1 : Blocks := edgeBlocks% "full/vectors/00000000000111-V-0001.bin"
private noncomputable def vp00000000000111_2 : Blocks := edgeBlocks% "full/vectors/00000000000111-V-0002.bin"
noncomputable def vp00000000000111 : Blocks := (Blocks.join vp00000000000111_0 (Blocks.join vp00000000000111_1 vp00000000000111_2))
private theorem bp000000000001110 : Branch 0 (-3261639/500000 : ℚ) vp00000000000111 := by
  apply branch_left_normalized (c:=vp000000000001110) (k:=0) (m:=146) (by decide +kernel)
  rw [show 2*(-3261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-3261639/250000 : ℚ) by norm_num]
  exact coverp000000000001110
private noncomputable def ep000000000001111_0 : Blocks := edgeBlocks% "full/vectors/000000000001111-E-0000.bin"
private noncomputable def ep000000000001111_1 : Blocks := edgeBlocks% "full/vectors/000000000001111-E-0001.bin"
private noncomputable def ep000000000001111_2 : Blocks := edgeBlocks% "full/vectors/000000000001111-E-0002.bin"
noncomputable def ep000000000001111 : Blocks := (Blocks.join ep000000000001111_0 (Blocks.join ep000000000001111_1 ep000000000001111_2))
private theorem idp000000000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000111.list =
    C ((2:ℤ)^278) * horner X vp000000000001111.list + horner X ep000000000001111.list := by
  exact edge_identity (B := (2:ℤ)^507) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001111 : Branch 1 (-3261639/500000 : ℚ) vp00000000000111 := by
  apply branch_checked idp000000000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-3261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-3511639/250000 : ℚ) by norm_num]
  exact coverp000000000001111
theorem coverp00000000000111 : Covers (-3261639/500000 : ℚ) vp00000000000111 := join_branches bp000000000001110 bp000000000001111
private noncomputable def vp00000000000110111_0 : Blocks := edgeBlocks% "full/vectors/00000000000110111-V-0000.bin"
noncomputable def vp00000000000110111 : Blocks := vp00000000000110111_0
theorem coverp00000000000110111 : Covers (-3199139/62500 : ℚ) vp00000000000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000110110_0 : Blocks := edgeBlocks% "full/vectors/00000000000110110-V-0000.bin"
noncomputable def vp00000000000110110 : Blocks := vp00000000000110110_0
theorem coverp00000000000110110 : Covers (-3136639/62500 : ℚ) vp00000000000110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000011011-V-0000.bin"
noncomputable def vp0000000000011011 : Blocks := vp0000000000011011_0
private theorem bp00000000000110110 : Branch 0 (-3136639/125000 : ℚ) vp0000000000011011 := by
  apply branch_left_normalized (c:=vp00000000000110110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-3136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-3136639/62500 : ℚ) by norm_num]
  exact coverp00000000000110110
private noncomputable def ep00000000000110111_0 : Blocks := edgeBlocks% "full/vectors/00000000000110111-E-0000.bin"
noncomputable def ep00000000000110111 : Blocks := ep00000000000110111_0
private theorem idp00000000000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011011.list =
    C ((2:ℤ)^82) * horner X vp00000000000110111.list + horner X ep00000000000110111.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000110111 : Branch 1 (-3136639/125000 : ℚ) vp0000000000011011 := by
  apply branch_checked idp00000000000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-3199139/62500 : ℚ) by norm_num]
  exact coverp00000000000110111
theorem coverp0000000000011011 : Covers (-3136639/125000 : ℚ) vp0000000000011011 := join_branches bp00000000000110110 bp00000000000110111
private noncomputable def vp00000000000110101_0 : Blocks := edgeBlocks% "full/vectors/00000000000110101-V-0000.bin"
noncomputable def vp00000000000110101 : Blocks := vp00000000000110101_0
theorem coverp00000000000110101 : Covers (-3074139/62500 : ℚ) vp00000000000110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000110100_0 : Blocks := edgeBlocks% "full/vectors/00000000000110100-V-0000.bin"
noncomputable def vp00000000000110100 : Blocks := vp00000000000110100_0
theorem coverp00000000000110100 : Covers (-3011639/62500 : ℚ) vp00000000000110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011010_0 : Blocks := edgeBlocks% "full/vectors/0000000000011010-V-0000.bin"
noncomputable def vp0000000000011010 : Blocks := vp0000000000011010_0
private theorem bp00000000000110100 : Branch 0 (-3011639/125000 : ℚ) vp0000000000011010 := by
  apply branch_left_normalized (c:=vp00000000000110100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-3011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-3011639/62500 : ℚ) by norm_num]
  exact coverp00000000000110100
private noncomputable def ep00000000000110101_0 : Blocks := edgeBlocks% "full/vectors/00000000000110101-E-0000.bin"
noncomputable def ep00000000000110101 : Blocks := ep00000000000110101_0
private theorem idp00000000000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011010.list =
    C ((2:ℤ)^83) * horner X vp00000000000110101.list + horner X ep00000000000110101.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000110101 : Branch 1 (-3011639/125000 : ℚ) vp0000000000011010 := by
  apply branch_checked idp00000000000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-3011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-3074139/62500 : ℚ) by norm_num]
  exact coverp00000000000110101
theorem coverp0000000000011010 : Covers (-3011639/125000 : ℚ) vp0000000000011010 := join_branches bp00000000000110100 bp00000000000110101
private noncomputable def vp000000000001101_0 : Blocks := edgeBlocks% "full/vectors/000000000001101-V-0000.bin"
private noncomputable def vp000000000001101_1 : Blocks := edgeBlocks% "full/vectors/000000000001101-V-0001.bin"
noncomputable def vp000000000001101 : Blocks := (Blocks.join vp000000000001101_0 vp000000000001101_1)
private theorem bp0000000000011010 : Branch 0 (-3011639/250000 : ℚ) vp000000000001101 := by
  apply branch_left_normalized (c:=vp0000000000011010) (k:=0) (m:=82) (by decide +kernel)
  rw [show 2*(-3011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-3011639/125000 : ℚ) by norm_num]
  exact coverp0000000000011010
private noncomputable def ep0000000000011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000011011-E-0000.bin"
private noncomputable def ep0000000000011011_1 : Blocks := edgeBlocks% "full/vectors/0000000000011011-E-0001.bin"
noncomputable def ep0000000000011011 : Blocks := (Blocks.join ep0000000000011011_0 ep0000000000011011_1)
private theorem idp0000000000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001101.list =
    C ((2:ℤ)^152) * horner X vp0000000000011011.list + horner X ep0000000000011011.list := by
  exact edge_identity (B := (2:ℤ)^312) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011011 : Branch 1 (-3011639/250000 : ℚ) vp000000000001101 := by
  apply branch_checked idp0000000000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-3136639/125000 : ℚ) by norm_num]
  exact coverp0000000000011011
theorem coverp000000000001101 : Covers (-3011639/250000 : ℚ) vp000000000001101 := join_branches bp0000000000011010 bp0000000000011011
private noncomputable def vp00000000000110011_0 : Blocks := edgeBlocks% "full/vectors/00000000000110011-V-0000.bin"
noncomputable def vp00000000000110011 : Blocks := vp00000000000110011_0
theorem coverp00000000000110011 : Covers (-2949139/62500 : ℚ) vp00000000000110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000110010_0 : Blocks := edgeBlocks% "full/vectors/00000000000110010-V-0000.bin"
noncomputable def vp00000000000110010 : Blocks := vp00000000000110010_0
theorem coverp00000000000110010 : Covers (-2886639/62500 : ℚ) vp00000000000110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000011001-V-0000.bin"
noncomputable def vp0000000000011001 : Blocks := vp0000000000011001_0
private theorem bp00000000000110010 : Branch 0 (-2886639/125000 : ℚ) vp0000000000011001 := by
  apply branch_left_normalized (c:=vp00000000000110010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-2886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-2886639/62500 : ℚ) by norm_num]
  exact coverp00000000000110010
private noncomputable def ep00000000000110011_0 : Blocks := edgeBlocks% "full/vectors/00000000000110011-E-0000.bin"
noncomputable def ep00000000000110011 : Blocks := ep00000000000110011_0
private theorem idp00000000000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011001.list =
    C ((2:ℤ)^84) * horner X vp00000000000110011.list + horner X ep00000000000110011.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000110011 : Branch 1 (-2886639/125000 : ℚ) vp0000000000011001 := by
  apply branch_checked idp00000000000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-2949139/62500 : ℚ) by norm_num]
  exact coverp00000000000110011
theorem coverp0000000000011001 : Covers (-2886639/125000 : ℚ) vp0000000000011001 := join_branches bp00000000000110010 bp00000000000110011
private noncomputable def vp00000000000110001_0 : Blocks := edgeBlocks% "full/vectors/00000000000110001-V-0000.bin"
noncomputable def vp00000000000110001 : Blocks := vp00000000000110001_0
theorem coverp00000000000110001 : Covers (-2824139/62500 : ℚ) vp00000000000110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000110000_0 : Blocks := edgeBlocks% "full/vectors/00000000000110000-V-0000.bin"
noncomputable def vp00000000000110000 : Blocks := vp00000000000110000_0
theorem coverp00000000000110000 : Covers (-2761639/62500 : ℚ) vp00000000000110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000011000_0 : Blocks := edgeBlocks% "full/vectors/0000000000011000-V-0000.bin"
noncomputable def vp0000000000011000 : Blocks := vp0000000000011000_0
private theorem bp00000000000110000 : Branch 0 (-2761639/125000 : ℚ) vp0000000000011000 := by
  apply branch_left_normalized (c:=vp00000000000110000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-2761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-2761639/62500 : ℚ) by norm_num]
  exact coverp00000000000110000
private noncomputable def ep00000000000110001_0 : Blocks := edgeBlocks% "full/vectors/00000000000110001-E-0000.bin"
noncomputable def ep00000000000110001 : Blocks := ep00000000000110001_0
private theorem idp00000000000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011000.list =
    C ((2:ℤ)^86) * horner X vp00000000000110001.list + horner X ep00000000000110001.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000110001 : Branch 1 (-2761639/125000 : ℚ) vp0000000000011000 := by
  apply branch_checked idp00000000000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-2824139/62500 : ℚ) by norm_num]
  exact coverp00000000000110001
theorem coverp0000000000011000 : Covers (-2761639/125000 : ℚ) vp0000000000011000 := join_branches bp00000000000110000 bp00000000000110001
private noncomputable def vp000000000001100_0 : Blocks := edgeBlocks% "full/vectors/000000000001100-V-0000.bin"
private noncomputable def vp000000000001100_1 : Blocks := edgeBlocks% "full/vectors/000000000001100-V-0001.bin"
noncomputable def vp000000000001100 : Blocks := (Blocks.join vp000000000001100_0 vp000000000001100_1)
private theorem bp0000000000011000 : Branch 0 (-2761639/250000 : ℚ) vp000000000001100 := by
  apply branch_left_normalized (c:=vp0000000000011000) (k:=0) (m:=84) (by decide +kernel)
  rw [show 2*(-2761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-2761639/125000 : ℚ) by norm_num]
  exact coverp0000000000011000
private noncomputable def ep0000000000011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000011001-E-0000.bin"
private noncomputable def ep0000000000011001_1 : Blocks := edgeBlocks% "full/vectors/0000000000011001-E-0001.bin"
noncomputable def ep0000000000011001 : Blocks := (Blocks.join ep0000000000011001_0 ep0000000000011001_1)
private theorem idp0000000000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001100.list =
    C ((2:ℤ)^158) * horner X vp0000000000011001.list + horner X ep0000000000011001.list := by
  exact edge_identity (B := (2:ℤ)^321) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011001 : Branch 1 (-2761639/250000 : ℚ) vp000000000001100 := by
  apply branch_checked idp0000000000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-2761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-2886639/125000 : ℚ) by norm_num]
  exact coverp0000000000011001
theorem coverp000000000001100 : Covers (-2761639/250000 : ℚ) vp000000000001100 := join_branches bp0000000000011000 bp0000000000011001
private noncomputable def vp00000000000110_0 : Blocks := edgeBlocks% "full/vectors/00000000000110-V-0000.bin"
private noncomputable def vp00000000000110_1 : Blocks := edgeBlocks% "full/vectors/00000000000110-V-0001.bin"
private noncomputable def vp00000000000110_2 : Blocks := edgeBlocks% "full/vectors/00000000000110-V-0002.bin"
noncomputable def vp00000000000110 : Blocks := (Blocks.join vp00000000000110_0 (Blocks.join vp00000000000110_1 vp00000000000110_2))
private theorem bp000000000001100 : Branch 0 (-2761639/500000 : ℚ) vp00000000000110 := by
  apply branch_left_normalized (c:=vp000000000001100) (k:=0) (m:=156) (by decide +kernel)
  rw [show 2*(-2761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-2761639/250000 : ℚ) by norm_num]
  exact coverp000000000001100
private noncomputable def ep000000000001101_0 : Blocks := edgeBlocks% "full/vectors/000000000001101-E-0000.bin"
private noncomputable def ep000000000001101_1 : Blocks := edgeBlocks% "full/vectors/000000000001101-E-0001.bin"
private noncomputable def ep000000000001101_2 : Blocks := edgeBlocks% "full/vectors/000000000001101-E-0002.bin"
noncomputable def ep000000000001101 : Blocks := (Blocks.join ep000000000001101_0 (Blocks.join ep000000000001101_1 ep000000000001101_2))
private theorem idp000000000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000110.list =
    C ((2:ℤ)^299) * horner X vp000000000001101.list + horner X ep000000000001101.list := by
  exact edge_identity (B := (2:ℤ)^537) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001101 : Branch 1 (-2761639/500000 : ℚ) vp00000000000110 := by
  apply branch_checked idp000000000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-2761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-3011639/250000 : ℚ) by norm_num]
  exact coverp000000000001101
theorem coverp00000000000110 : Covers (-2761639/500000 : ℚ) vp00000000000110 := join_branches bp000000000001100 bp000000000001101
private noncomputable def vp0000000000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000011-V-0000.bin"
private noncomputable def vp0000000000011_1 : Blocks := edgeBlocks% "full/vectors/0000000000011-V-0001.bin"
private noncomputable def vp0000000000011_2 : Blocks := edgeBlocks% "full/vectors/0000000000011-V-0002.bin"
private noncomputable def vp0000000000011_3 : Blocks := edgeBlocks% "full/vectors/0000000000011-V-0003.bin"
private noncomputable def vp0000000000011_4 : Blocks := edgeBlocks% "full/vectors/0000000000011-V-0004.bin"
noncomputable def vp0000000000011 : Blocks := (Blocks.join (Blocks.join vp0000000000011_0 vp0000000000011_1) (Blocks.join vp0000000000011_2 (Blocks.join vp0000000000011_3 vp0000000000011_4)))
private theorem bp00000000000110 : Branch 0 (-2761639/1000000 : ℚ) vp0000000000011 := by
  apply branch_left_normalized (c:=vp00000000000110) (k:=0) (m:=297) (by decide +kernel)
  rw [show 2*(-2761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-2761639/500000 : ℚ) by norm_num]
  exact coverp00000000000110
private noncomputable def ep00000000000111_0 : Blocks := edgeBlocks% "full/vectors/00000000000111-E-0000.bin"
private noncomputable def ep00000000000111_1 : Blocks := edgeBlocks% "full/vectors/00000000000111-E-0001.bin"
private noncomputable def ep00000000000111_2 : Blocks := edgeBlocks% "full/vectors/00000000000111-E-0002.bin"
private noncomputable def ep00000000000111_3 : Blocks := edgeBlocks% "full/vectors/00000000000111-E-0003.bin"
private noncomputable def ep00000000000111_4 : Blocks := edgeBlocks% "full/vectors/00000000000111-E-0004.bin"
noncomputable def ep00000000000111 : Blocks := (Blocks.join (Blocks.join ep00000000000111_0 ep00000000000111_1) (Blocks.join ep00000000000111_2 (Blocks.join ep00000000000111_3 ep00000000000111_4)))
private theorem idp00000000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000011.list =
    C ((2:ℤ)^580) * horner X vp00000000000111.list + horner X ep00000000000111.list := by
  exact edge_identity (B := (2:ℤ)^967) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000111 : Branch 1 (-2761639/1000000 : ℚ) vp0000000000011 := by
  apply branch_checked idp00000000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-2761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-3261639/500000 : ℚ) by norm_num]
  exact coverp00000000000111
theorem coverp0000000000011 : Covers (-2761639/1000000 : ℚ) vp0000000000011 := join_branches bp00000000000110 bp00000000000111
private noncomputable def vp00000000000101111_0 : Blocks := edgeBlocks% "full/vectors/00000000000101111-V-0000.bin"
noncomputable def vp00000000000101111 : Blocks := vp00000000000101111_0
theorem coverp00000000000101111 : Covers (-2699139/62500 : ℚ) vp00000000000101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000101110_0 : Blocks := edgeBlocks% "full/vectors/00000000000101110-V-0000.bin"
noncomputable def vp00000000000101110 : Blocks := vp00000000000101110_0
theorem coverp00000000000101110 : Covers (-2636639/62500 : ℚ) vp00000000000101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000010111-V-0000.bin"
noncomputable def vp0000000000010111 : Blocks := vp0000000000010111_0
private theorem bp00000000000101110 : Branch 0 (-2636639/125000 : ℚ) vp0000000000010111 := by
  apply branch_left_normalized (c:=vp00000000000101110) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-2636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-2636639/62500 : ℚ) by norm_num]
  exact coverp00000000000101110
private noncomputable def ep00000000000101111_0 : Blocks := edgeBlocks% "full/vectors/00000000000101111-E-0000.bin"
noncomputable def ep00000000000101111 : Blocks := ep00000000000101111_0
private theorem idp00000000000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000010111.list =
    C ((2:ℤ)^87) * horner X vp00000000000101111.list + horner X ep00000000000101111.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000101111 : Branch 1 (-2636639/125000 : ℚ) vp0000000000010111 := by
  apply branch_checked idp00000000000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-2699139/62500 : ℚ) by norm_num]
  exact coverp00000000000101111
theorem coverp0000000000010111 : Covers (-2636639/125000 : ℚ) vp0000000000010111 := join_branches bp00000000000101110 bp00000000000101111
private noncomputable def vp00000000000101101_0 : Blocks := edgeBlocks% "full/vectors/00000000000101101-V-0000.bin"
noncomputable def vp00000000000101101 : Blocks := vp00000000000101101_0
theorem coverp00000000000101101 : Covers (-2574139/62500 : ℚ) vp00000000000101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000101100_0 : Blocks := edgeBlocks% "full/vectors/00000000000101100-V-0000.bin"
noncomputable def vp00000000000101100 : Blocks := vp00000000000101100_0
theorem coverp00000000000101100 : Covers (-2511639/62500 : ℚ) vp00000000000101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000010110_0 : Blocks := edgeBlocks% "full/vectors/0000000000010110-V-0000.bin"
noncomputable def vp0000000000010110 : Blocks := vp0000000000010110_0
private theorem bp00000000000101100 : Branch 0 (-2511639/125000 : ℚ) vp0000000000010110 := by
  apply branch_left_normalized (c:=vp00000000000101100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-2511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-2511639/62500 : ℚ) by norm_num]
  exact coverp00000000000101100
private noncomputable def ep00000000000101101_0 : Blocks := edgeBlocks% "full/vectors/00000000000101101-E-0000.bin"
noncomputable def ep00000000000101101 : Blocks := ep00000000000101101_0
private theorem idp00000000000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000010110.list =
    C ((2:ℤ)^90) * horner X vp00000000000101101.list + horner X ep00000000000101101.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000101101 : Branch 1 (-2511639/125000 : ℚ) vp0000000000010110 := by
  apply branch_checked idp00000000000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-2574139/62500 : ℚ) by norm_num]
  exact coverp00000000000101101
theorem coverp0000000000010110 : Covers (-2511639/125000 : ℚ) vp0000000000010110 := join_branches bp00000000000101100 bp00000000000101101
private noncomputable def vp000000000001011_0 : Blocks := edgeBlocks% "full/vectors/000000000001011-V-0000.bin"
private noncomputable def vp000000000001011_1 : Blocks := edgeBlocks% "full/vectors/000000000001011-V-0001.bin"
noncomputable def vp000000000001011 : Blocks := (Blocks.join vp000000000001011_0 vp000000000001011_1)
private theorem bp0000000000010110 : Branch 0 (-2511639/250000 : ℚ) vp000000000001011 := by
  apply branch_left_normalized (c:=vp0000000000010110) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-2511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-2511639/125000 : ℚ) by norm_num]
  exact coverp0000000000010110
private noncomputable def ep0000000000010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000010111-E-0000.bin"
private noncomputable def ep0000000000010111_1 : Blocks := edgeBlocks% "full/vectors/0000000000010111-E-0001.bin"
noncomputable def ep0000000000010111 : Blocks := (Blocks.join ep0000000000010111_0 ep0000000000010111_1)
private theorem idp0000000000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001011.list =
    C ((2:ℤ)^164) * horner X vp0000000000010111.list + horner X ep0000000000010111.list := by
  exact edge_identity (B := (2:ℤ)^330) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000010111 : Branch 1 (-2511639/250000 : ℚ) vp000000000001011 := by
  apply branch_checked idp0000000000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-2511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-2636639/125000 : ℚ) by norm_num]
  exact coverp0000000000010111
theorem coverp000000000001011 : Covers (-2511639/250000 : ℚ) vp000000000001011 := join_branches bp0000000000010110 bp0000000000010111
private noncomputable def vp00000000000101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000101011-V-0000.bin"
noncomputable def vp00000000000101011 : Blocks := vp00000000000101011_0
theorem coverp00000000000101011 : Covers (-2449139/62500 : ℚ) vp00000000000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000101010_0 : Blocks := edgeBlocks% "full/vectors/00000000000101010-V-0000.bin"
noncomputable def vp00000000000101010 : Blocks := vp00000000000101010_0
theorem coverp00000000000101010 : Covers (-2386639/62500 : ℚ) vp00000000000101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000010101-V-0000.bin"
noncomputable def vp0000000000010101 : Blocks := vp0000000000010101_0
private theorem bp00000000000101010 : Branch 0 (-2386639/125000 : ℚ) vp0000000000010101 := by
  apply branch_left_normalized (c:=vp00000000000101010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-2386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-2386639/62500 : ℚ) by norm_num]
  exact coverp00000000000101010
private noncomputable def ep00000000000101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000101011-E-0000.bin"
noncomputable def ep00000000000101011 : Blocks := ep00000000000101011_0
private theorem idp00000000000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000010101.list =
    C ((2:ℤ)^90) * horner X vp00000000000101011.list + horner X ep00000000000101011.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000101011 : Branch 1 (-2386639/125000 : ℚ) vp0000000000010101 := by
  apply branch_checked idp00000000000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-2449139/62500 : ℚ) by norm_num]
  exact coverp00000000000101011
theorem coverp0000000000010101 : Covers (-2386639/125000 : ℚ) vp0000000000010101 := join_branches bp00000000000101010 bp00000000000101011
private noncomputable def vp00000000000101001_0 : Blocks := edgeBlocks% "full/vectors/00000000000101001-V-0000.bin"
noncomputable def vp00000000000101001 : Blocks := vp00000000000101001_0
theorem coverp00000000000101001 : Covers (-2324139/62500 : ℚ) vp00000000000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000101000_0 : Blocks := edgeBlocks% "full/vectors/00000000000101000-V-0000.bin"
noncomputable def vp00000000000101000 : Blocks := vp00000000000101000_0
theorem coverp00000000000101000 : Covers (-2261639/62500 : ℚ) vp00000000000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000010100_0 : Blocks := edgeBlocks% "full/vectors/0000000000010100-V-0000.bin"
noncomputable def vp0000000000010100 : Blocks := vp0000000000010100_0
private theorem bp00000000000101000 : Branch 0 (-2261639/125000 : ℚ) vp0000000000010100 := by
  apply branch_left_normalized (c:=vp00000000000101000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-2261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-2261639/62500 : ℚ) by norm_num]
  exact coverp00000000000101000
private noncomputable def ep00000000000101001_0 : Blocks := edgeBlocks% "full/vectors/00000000000101001-E-0000.bin"
noncomputable def ep00000000000101001 : Blocks := ep00000000000101001_0
private theorem idp00000000000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000010100.list =
    C ((2:ℤ)^93) * horner X vp00000000000101001.list + horner X ep00000000000101001.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000101001 : Branch 1 (-2261639/125000 : ℚ) vp0000000000010100 := by
  apply branch_checked idp00000000000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-2324139/62500 : ℚ) by norm_num]
  exact coverp00000000000101001
theorem coverp0000000000010100 : Covers (-2261639/125000 : ℚ) vp0000000000010100 := join_branches bp00000000000101000 bp00000000000101001
private noncomputable def vp000000000001010_0 : Blocks := edgeBlocks% "full/vectors/000000000001010-V-0000.bin"
private noncomputable def vp000000000001010_1 : Blocks := edgeBlocks% "full/vectors/000000000001010-V-0001.bin"
noncomputable def vp000000000001010 : Blocks := (Blocks.join vp000000000001010_0 vp000000000001010_1)
private theorem bp0000000000010100 : Branch 0 (-2261639/250000 : ℚ) vp000000000001010 := by
  apply branch_left_normalized (c:=vp0000000000010100) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-2261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-2261639/125000 : ℚ) by norm_num]
  exact coverp0000000000010100
private noncomputable def ep0000000000010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000010101-E-0000.bin"
private noncomputable def ep0000000000010101_1 : Blocks := edgeBlocks% "full/vectors/0000000000010101-E-0001.bin"
noncomputable def ep0000000000010101 : Blocks := (Blocks.join ep0000000000010101_0 ep0000000000010101_1)
private theorem idp0000000000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001010.list =
    C ((2:ℤ)^170) * horner X vp0000000000010101.list + horner X ep0000000000010101.list := by
  exact edge_identity (B := (2:ℤ)^339) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000010101 : Branch 1 (-2261639/250000 : ℚ) vp000000000001010 := by
  apply branch_checked idp0000000000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-2386639/125000 : ℚ) by norm_num]
  exact coverp0000000000010101
theorem coverp000000000001010 : Covers (-2261639/250000 : ℚ) vp000000000001010 := join_branches bp0000000000010100 bp0000000000010101
private noncomputable def vp00000000000101_0 : Blocks := edgeBlocks% "full/vectors/00000000000101-V-0000.bin"
private noncomputable def vp00000000000101_1 : Blocks := edgeBlocks% "full/vectors/00000000000101-V-0001.bin"
private noncomputable def vp00000000000101_2 : Blocks := edgeBlocks% "full/vectors/00000000000101-V-0002.bin"
noncomputable def vp00000000000101 : Blocks := (Blocks.join vp00000000000101_0 (Blocks.join vp00000000000101_1 vp00000000000101_2))
private theorem bp000000000001010 : Branch 0 (-2261639/500000 : ℚ) vp00000000000101 := by
  apply branch_left_normalized (c:=vp000000000001010) (k:=0) (m:=168) (by decide +kernel)
  rw [show 2*(-2261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-2261639/250000 : ℚ) by norm_num]
  exact coverp000000000001010
private noncomputable def ep000000000001011_0 : Blocks := edgeBlocks% "full/vectors/000000000001011-E-0000.bin"
private noncomputable def ep000000000001011_1 : Blocks := edgeBlocks% "full/vectors/000000000001011-E-0001.bin"
private noncomputable def ep000000000001011_2 : Blocks := edgeBlocks% "full/vectors/000000000001011-E-0002.bin"
noncomputable def ep000000000001011 : Blocks := (Blocks.join ep000000000001011_0 (Blocks.join ep000000000001011_1 ep000000000001011_2))
private theorem idp000000000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000101.list =
    C ((2:ℤ)^325) * horner X vp000000000001011.list + horner X ep000000000001011.list := by
  exact edge_identity (B := (2:ℤ)^577) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001011 : Branch 1 (-2261639/500000 : ℚ) vp00000000000101 := by
  apply branch_checked idp000000000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-2511639/250000 : ℚ) by norm_num]
  exact coverp000000000001011
theorem coverp00000000000101 : Covers (-2261639/500000 : ℚ) vp00000000000101 := join_branches bp000000000001010 bp000000000001011
private noncomputable def vp00000000000100111_0 : Blocks := edgeBlocks% "full/vectors/00000000000100111-V-0000.bin"
noncomputable def vp00000000000100111 : Blocks := vp00000000000100111_0
theorem coverp00000000000100111 : Covers (-2199139/62500 : ℚ) vp00000000000100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000100110_0 : Blocks := edgeBlocks% "full/vectors/00000000000100110-V-0000.bin"
noncomputable def vp00000000000100110 : Blocks := vp00000000000100110_0
theorem coverp00000000000100110 : Covers (-2136639/62500 : ℚ) vp00000000000100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000010011-V-0000.bin"
noncomputable def vp0000000000010011 : Blocks := vp0000000000010011_0
private theorem bp00000000000100110 : Branch 0 (-2136639/125000 : ℚ) vp0000000000010011 := by
  apply branch_left_normalized (c:=vp00000000000100110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-2136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-2136639/62500 : ℚ) by norm_num]
  exact coverp00000000000100110
private noncomputable def ep00000000000100111_0 : Blocks := edgeBlocks% "full/vectors/00000000000100111-E-0000.bin"
noncomputable def ep00000000000100111 : Blocks := ep00000000000100111_0
private theorem idp00000000000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000010011.list =
    C ((2:ℤ)^94) * horner X vp00000000000100111.list + horner X ep00000000000100111.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000100111 : Branch 1 (-2136639/125000 : ℚ) vp0000000000010011 := by
  apply branch_checked idp00000000000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-2136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-2199139/62500 : ℚ) by norm_num]
  exact coverp00000000000100111
theorem coverp0000000000010011 : Covers (-2136639/125000 : ℚ) vp0000000000010011 := join_branches bp00000000000100110 bp00000000000100111
private noncomputable def vp00000000000100101_0 : Blocks := edgeBlocks% "full/vectors/00000000000100101-V-0000.bin"
noncomputable def vp00000000000100101 : Blocks := vp00000000000100101_0
theorem coverp00000000000100101 : Covers (-2074139/62500 : ℚ) vp00000000000100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001001001_0 : Blocks := edgeBlocks% "full/vectors/000000000001001001-V-0000.bin"
noncomputable def vp000000000001001001 : Blocks := vp000000000001001001_0
theorem coverp000000000001001001 : Covers (-2042889/31250 : ℚ) vp000000000001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001001000_0 : Blocks := edgeBlocks% "full/vectors/000000000001001000-V-0000.bin"
noncomputable def vp000000000001001000 : Blocks := vp000000000001001000_0
theorem coverp000000000001001000 : Covers (-2011639/31250 : ℚ) vp000000000001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000100100_0 : Blocks := edgeBlocks% "full/vectors/00000000000100100-V-0000.bin"
noncomputable def vp00000000000100100 : Blocks := vp00000000000100100_0
private theorem bp000000000001001000 : Branch 0 (-2011639/62500 : ℚ) vp00000000000100100 := by
  apply branch_left_normalized (c:=vp000000000001001000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-2011639/62500 : ℚ) - ((0:ℤ):ℚ) = (-2011639/31250 : ℚ) by norm_num]
  exact coverp000000000001001000
private noncomputable def ep000000000001001001_0 : Blocks := edgeBlocks% "full/vectors/000000000001001001-E-0000.bin"
noncomputable def ep000000000001001001 : Blocks := ep000000000001001001_0
private theorem idp000000000001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000100100.list =
    C ((2:ℤ)^55) * horner X vp000000000001001001.list + horner X ep000000000001001001.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001001001 : Branch 1 (-2011639/62500 : ℚ) vp00000000000100100 := by
  apply branch_checked idp000000000001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2011639/62500 : ℚ) - ((1:ℤ):ℚ) = (-2042889/31250 : ℚ) by norm_num]
  exact coverp000000000001001001
theorem coverp00000000000100100 : Covers (-2011639/62500 : ℚ) vp00000000000100100 := join_branches bp000000000001001000 bp000000000001001001
private noncomputable def vp0000000000010010_0 : Blocks := edgeBlocks% "full/vectors/0000000000010010-V-0000.bin"
noncomputable def vp0000000000010010 : Blocks := vp0000000000010010_0
private theorem bp00000000000100100 : Branch 0 (-2011639/125000 : ℚ) vp0000000000010010 := by
  apply branch_left_normalized (c:=vp00000000000100100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-2011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-2011639/62500 : ℚ) by norm_num]
  exact coverp00000000000100100
private noncomputable def ep00000000000100101_0 : Blocks := edgeBlocks% "full/vectors/00000000000100101-E-0000.bin"
noncomputable def ep00000000000100101 : Blocks := ep00000000000100101_0
private theorem idp00000000000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000010010.list =
    C ((2:ℤ)^97) * horner X vp00000000000100101.list + horner X ep00000000000100101.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000100101 : Branch 1 (-2011639/125000 : ℚ) vp0000000000010010 := by
  apply branch_checked idp00000000000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-2011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-2074139/62500 : ℚ) by norm_num]
  exact coverp00000000000100101
theorem coverp0000000000010010 : Covers (-2011639/125000 : ℚ) vp0000000000010010 := join_branches bp00000000000100100 bp00000000000100101
private noncomputable def vp000000000001001_0 : Blocks := edgeBlocks% "full/vectors/000000000001001-V-0000.bin"
private noncomputable def vp000000000001001_1 : Blocks := edgeBlocks% "full/vectors/000000000001001-V-0001.bin"
noncomputable def vp000000000001001 : Blocks := (Blocks.join vp000000000001001_0 vp000000000001001_1)
private theorem bp0000000000010010 : Branch 0 (-2011639/250000 : ℚ) vp000000000001001 := by
  apply branch_left_normalized (c:=vp0000000000010010) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-2011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-2011639/125000 : ℚ) by norm_num]
  exact coverp0000000000010010
private noncomputable def ep0000000000010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000010011-E-0000.bin"
private noncomputable def ep0000000000010011_1 : Blocks := edgeBlocks% "full/vectors/0000000000010011-E-0001.bin"
noncomputable def ep0000000000010011 : Blocks := (Blocks.join ep0000000000010011_0 ep0000000000010011_1)
private theorem idp0000000000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001001.list =
    C ((2:ℤ)^179) * horner X vp0000000000010011.list + horner X ep0000000000010011.list := by
  exact edge_identity (B := (2:ℤ)^353) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000010011 : Branch 1 (-2011639/250000 : ℚ) vp000000000001001 := by
  apply branch_checked idp0000000000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-2136639/125000 : ℚ) by norm_num]
  exact coverp0000000000010011
theorem coverp000000000001001 : Covers (-2011639/250000 : ℚ) vp000000000001001 := join_branches bp0000000000010010 bp0000000000010011
private noncomputable def vp000000000001000111_0 : Blocks := edgeBlocks% "full/vectors/000000000001000111-V-0000.bin"
noncomputable def vp000000000001000111 : Blocks := vp000000000001000111_0
theorem coverp000000000001000111 : Covers (-1980389/31250 : ℚ) vp000000000001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001000110_0 : Blocks := edgeBlocks% "full/vectors/000000000001000110-V-0000.bin"
noncomputable def vp000000000001000110 : Blocks := vp000000000001000110_0
theorem coverp000000000001000110 : Covers (-1949139/31250 : ℚ) vp000000000001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000100011_0 : Blocks := edgeBlocks% "full/vectors/00000000000100011-V-0000.bin"
noncomputable def vp00000000000100011 : Blocks := vp00000000000100011_0
private theorem bp000000000001000110 : Branch 0 (-1949139/62500 : ℚ) vp00000000000100011 := by
  apply branch_left_normalized (c:=vp000000000001000110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-1949139/62500 : ℚ) - ((0:ℤ):ℚ) = (-1949139/31250 : ℚ) by norm_num]
  exact coverp000000000001000110
private noncomputable def ep000000000001000111_0 : Blocks := edgeBlocks% "full/vectors/000000000001000111-E-0000.bin"
noncomputable def ep000000000001000111 : Blocks := ep000000000001000111_0
private theorem idp000000000001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000100011.list =
    C ((2:ℤ)^55) * horner X vp000000000001000111.list + horner X ep000000000001000111.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001000111 : Branch 1 (-1949139/62500 : ℚ) vp00000000000100011 := by
  apply branch_checked idp000000000001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1949139/62500 : ℚ) - ((1:ℤ):ℚ) = (-1980389/31250 : ℚ) by norm_num]
  exact coverp000000000001000111
theorem coverp00000000000100011 : Covers (-1949139/62500 : ℚ) vp00000000000100011 := join_branches bp000000000001000110 bp000000000001000111
private noncomputable def vp000000000001000101_0 : Blocks := edgeBlocks% "full/vectors/000000000001000101-V-0000.bin"
noncomputable def vp000000000001000101 : Blocks := vp000000000001000101_0
theorem coverp000000000001000101 : Covers (-1917889/31250 : ℚ) vp000000000001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001000100_0 : Blocks := edgeBlocks% "full/vectors/000000000001000100-V-0000.bin"
noncomputable def vp000000000001000100 : Blocks := vp000000000001000100_0
theorem coverp000000000001000100 : Covers (-1886639/31250 : ℚ) vp000000000001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000100010_0 : Blocks := edgeBlocks% "full/vectors/00000000000100010-V-0000.bin"
noncomputable def vp00000000000100010 : Blocks := vp00000000000100010_0
private theorem bp000000000001000100 : Branch 0 (-1886639/62500 : ℚ) vp00000000000100010 := by
  apply branch_left_normalized (c:=vp000000000001000100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-1886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-1886639/31250 : ℚ) by norm_num]
  exact coverp000000000001000100
private noncomputable def ep000000000001000101_0 : Blocks := edgeBlocks% "full/vectors/000000000001000101-E-0000.bin"
noncomputable def ep000000000001000101 : Blocks := ep000000000001000101_0
private theorem idp000000000001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000100010.list =
    C ((2:ℤ)^56) * horner X vp000000000001000101.list + horner X ep000000000001000101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001000101 : Branch 1 (-1886639/62500 : ℚ) vp00000000000100010 := by
  apply branch_checked idp000000000001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-1917889/31250 : ℚ) by norm_num]
  exact coverp000000000001000101
theorem coverp00000000000100010 : Covers (-1886639/62500 : ℚ) vp00000000000100010 := join_branches bp000000000001000100 bp000000000001000101
private noncomputable def vp0000000000010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000010001-V-0000.bin"
noncomputable def vp0000000000010001 : Blocks := vp0000000000010001_0
private theorem bp00000000000100010 : Branch 0 (-1886639/125000 : ℚ) vp0000000000010001 := by
  apply branch_left_normalized (c:=vp00000000000100010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-1886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-1886639/62500 : ℚ) by norm_num]
  exact coverp00000000000100010
private noncomputable def ep00000000000100011_0 : Blocks := edgeBlocks% "full/vectors/00000000000100011-E-0000.bin"
noncomputable def ep00000000000100011 : Blocks := ep00000000000100011_0
private theorem idp00000000000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000010001.list =
    C ((2:ℤ)^98) * horner X vp00000000000100011.list + horner X ep00000000000100011.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000100011 : Branch 1 (-1886639/125000 : ℚ) vp0000000000010001 := by
  apply branch_checked idp00000000000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-1949139/62500 : ℚ) by norm_num]
  exact coverp00000000000100011
theorem coverp0000000000010001 : Covers (-1886639/125000 : ℚ) vp0000000000010001 := join_branches bp00000000000100010 bp00000000000100011
private noncomputable def vp000000000001000011_0 : Blocks := edgeBlocks% "full/vectors/000000000001000011-V-0000.bin"
noncomputable def vp000000000001000011 : Blocks := vp000000000001000011_0
theorem coverp000000000001000011 : Covers (-1855389/31250 : ℚ) vp000000000001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001000010_0 : Blocks := edgeBlocks% "full/vectors/000000000001000010-V-0000.bin"
noncomputable def vp000000000001000010 : Blocks := vp000000000001000010_0
theorem coverp000000000001000010 : Covers (-1824139/31250 : ℚ) vp000000000001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000100001-V-0000.bin"
noncomputable def vp00000000000100001 : Blocks := vp00000000000100001_0
private theorem bp000000000001000010 : Branch 0 (-1824139/62500 : ℚ) vp00000000000100001 := by
  apply branch_left_normalized (c:=vp000000000001000010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-1824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-1824139/31250 : ℚ) by norm_num]
  exact coverp000000000001000010
private noncomputable def ep000000000001000011_0 : Blocks := edgeBlocks% "full/vectors/000000000001000011-E-0000.bin"
noncomputable def ep000000000001000011 : Blocks := ep000000000001000011_0
private theorem idp000000000001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000100001.list =
    C ((2:ℤ)^57) * horner X vp000000000001000011.list + horner X ep000000000001000011.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001000011 : Branch 1 (-1824139/62500 : ℚ) vp00000000000100001 := by
  apply branch_checked idp000000000001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-1855389/31250 : ℚ) by norm_num]
  exact coverp000000000001000011
theorem coverp00000000000100001 : Covers (-1824139/62500 : ℚ) vp00000000000100001 := join_branches bp000000000001000010 bp000000000001000011
private noncomputable def vp000000000001000001_0 : Blocks := edgeBlocks% "full/vectors/000000000001000001-V-0000.bin"
noncomputable def vp000000000001000001 : Blocks := vp000000000001000001_0
theorem coverp000000000001000001 : Covers (-1792889/31250 : ℚ) vp000000000001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000001000000_0 : Blocks := edgeBlocks% "full/vectors/000000000001000000-V-0000.bin"
noncomputable def vp000000000001000000 : Blocks := vp000000000001000000_0
theorem coverp000000000001000000 : Covers (-1761639/31250 : ℚ) vp000000000001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000100000_0 : Blocks := edgeBlocks% "full/vectors/00000000000100000-V-0000.bin"
noncomputable def vp00000000000100000 : Blocks := vp00000000000100000_0
private theorem bp000000000001000000 : Branch 0 (-1761639/62500 : ℚ) vp00000000000100000 := by
  apply branch_left_normalized (c:=vp000000000001000000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-1761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-1761639/31250 : ℚ) by norm_num]
  exact coverp000000000001000000
private noncomputable def ep000000000001000001_0 : Blocks := edgeBlocks% "full/vectors/000000000001000001-E-0000.bin"
noncomputable def ep000000000001000001 : Blocks := ep000000000001000001_0
private theorem idp000000000001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000100000.list =
    C ((2:ℤ)^57) * horner X vp000000000001000001.list + horner X ep000000000001000001.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001000001 : Branch 1 (-1761639/62500 : ℚ) vp00000000000100000 := by
  apply branch_checked idp000000000001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-1792889/31250 : ℚ) by norm_num]
  exact coverp000000000001000001
theorem coverp00000000000100000 : Covers (-1761639/62500 : ℚ) vp00000000000100000 := join_branches bp000000000001000000 bp000000000001000001
private noncomputable def vp0000000000010000_0 : Blocks := edgeBlocks% "full/vectors/0000000000010000-V-0000.bin"
noncomputable def vp0000000000010000 : Blocks := vp0000000000010000_0
private theorem bp00000000000100000 : Branch 0 (-1761639/125000 : ℚ) vp0000000000010000 := by
  apply branch_left_normalized (c:=vp00000000000100000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-1761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-1761639/62500 : ℚ) by norm_num]
  exact coverp00000000000100000
private noncomputable def ep00000000000100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000100001-E-0000.bin"
noncomputable def ep00000000000100001 : Blocks := ep00000000000100001_0
private theorem idp00000000000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000010000.list =
    C ((2:ℤ)^101) * horner X vp00000000000100001.list + horner X ep00000000000100001.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000100001 : Branch 1 (-1761639/125000 : ℚ) vp0000000000010000 := by
  apply branch_checked idp00000000000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-1824139/62500 : ℚ) by norm_num]
  exact coverp00000000000100001
theorem coverp0000000000010000 : Covers (-1761639/125000 : ℚ) vp0000000000010000 := join_branches bp00000000000100000 bp00000000000100001
private noncomputable def vp000000000001000_0 : Blocks := edgeBlocks% "full/vectors/000000000001000-V-0000.bin"
private noncomputable def vp000000000001000_1 : Blocks := edgeBlocks% "full/vectors/000000000001000-V-0001.bin"
noncomputable def vp000000000001000 : Blocks := (Blocks.join vp000000000001000_0 vp000000000001000_1)
private theorem bp0000000000010000 : Branch 0 (-1761639/250000 : ℚ) vp000000000001000 := by
  apply branch_left_normalized (c:=vp0000000000010000) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-1761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-1761639/125000 : ℚ) by norm_num]
  exact coverp0000000000010000
private noncomputable def ep0000000000010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000010001-E-0000.bin"
private noncomputable def ep0000000000010001_1 : Blocks := edgeBlocks% "full/vectors/0000000000010001-E-0001.bin"
noncomputable def ep0000000000010001 : Blocks := (Blocks.join ep0000000000010001_0 ep0000000000010001_1)
private theorem idp0000000000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001000.list =
    C ((2:ℤ)^188) * horner X vp0000000000010001.list + horner X ep0000000000010001.list := by
  exact edge_identity (B := (2:ℤ)^367) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000010001 : Branch 1 (-1761639/250000 : ℚ) vp000000000001000 := by
  apply branch_checked idp0000000000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-1886639/125000 : ℚ) by norm_num]
  exact coverp0000000000010001
theorem coverp000000000001000 : Covers (-1761639/250000 : ℚ) vp000000000001000 := join_branches bp0000000000010000 bp0000000000010001
private noncomputable def vp00000000000100_0 : Blocks := edgeBlocks% "full/vectors/00000000000100-V-0000.bin"
private noncomputable def vp00000000000100_1 : Blocks := edgeBlocks% "full/vectors/00000000000100-V-0001.bin"
private noncomputable def vp00000000000100_2 : Blocks := edgeBlocks% "full/vectors/00000000000100-V-0002.bin"
noncomputable def vp00000000000100 : Blocks := (Blocks.join vp00000000000100_0 (Blocks.join vp00000000000100_1 vp00000000000100_2))
private theorem bp000000000001000 : Branch 0 (-1761639/500000 : ℚ) vp00000000000100 := by
  apply branch_left_normalized (c:=vp000000000001000) (k:=0) (m:=186) (by decide +kernel)
  rw [show 2*(-1761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-1761639/250000 : ℚ) by norm_num]
  exact coverp000000000001000
private noncomputable def ep000000000001001_0 : Blocks := edgeBlocks% "full/vectors/000000000001001-E-0000.bin"
private noncomputable def ep000000000001001_1 : Blocks := edgeBlocks% "full/vectors/000000000001001-E-0001.bin"
private noncomputable def ep000000000001001_2 : Blocks := edgeBlocks% "full/vectors/000000000001001-E-0002.bin"
noncomputable def ep000000000001001 : Blocks := (Blocks.join ep000000000001001_0 (Blocks.join ep000000000001001_1 ep000000000001001_2))
private theorem idp000000000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000100.list =
    C ((2:ℤ)^362) * horner X vp000000000001001.list + horner X ep000000000001001.list := by
  exact edge_identity (B := (2:ℤ)^633) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000001001 : Branch 1 (-1761639/500000 : ℚ) vp00000000000100 := by
  apply branch_checked idp000000000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-2011639/250000 : ℚ) by norm_num]
  exact coverp000000000001001
theorem coverp00000000000100 : Covers (-1761639/500000 : ℚ) vp00000000000100 := join_branches bp000000000001000 bp000000000001001
private noncomputable def vp0000000000010_0 : Blocks := edgeBlocks% "full/vectors/0000000000010-V-0000.bin"
private noncomputable def vp0000000000010_1 : Blocks := edgeBlocks% "full/vectors/0000000000010-V-0001.bin"
private noncomputable def vp0000000000010_2 : Blocks := edgeBlocks% "full/vectors/0000000000010-V-0002.bin"
private noncomputable def vp0000000000010_3 : Blocks := edgeBlocks% "full/vectors/0000000000010-V-0003.bin"
private noncomputable def vp0000000000010_4 : Blocks := edgeBlocks% "full/vectors/0000000000010-V-0004.bin"
private noncomputable def vp0000000000010_5 : Blocks := edgeBlocks% "full/vectors/0000000000010-V-0005.bin"
noncomputable def vp0000000000010 : Blocks := (Blocks.join (Blocks.join vp0000000000010_0 (Blocks.join vp0000000000010_1 vp0000000000010_2)) (Blocks.join vp0000000000010_3 (Blocks.join vp0000000000010_4 vp0000000000010_5)))
private theorem bp00000000000100 : Branch 0 (-1761639/1000000 : ℚ) vp0000000000010 := by
  apply branch_left_normalized (c:=vp00000000000100) (k:=0) (m:=360) (by decide +kernel)
  rw [show 2*(-1761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-1761639/500000 : ℚ) by norm_num]
  exact coverp00000000000100
private noncomputable def ep00000000000101_0 : Blocks := edgeBlocks% "full/vectors/00000000000101-E-0000.bin"
private noncomputable def ep00000000000101_1 : Blocks := edgeBlocks% "full/vectors/00000000000101-E-0001.bin"
private noncomputable def ep00000000000101_2 : Blocks := edgeBlocks% "full/vectors/00000000000101-E-0002.bin"
private noncomputable def ep00000000000101_3 : Blocks := edgeBlocks% "full/vectors/00000000000101-E-0003.bin"
private noncomputable def ep00000000000101_4 : Blocks := edgeBlocks% "full/vectors/00000000000101-E-0004.bin"
private noncomputable def ep00000000000101_5 : Blocks := edgeBlocks% "full/vectors/00000000000101-E-0005.bin"
noncomputable def ep00000000000101 : Blocks := (Blocks.join (Blocks.join ep00000000000101_0 (Blocks.join ep00000000000101_1 ep00000000000101_2)) (Blocks.join ep00000000000101_3 (Blocks.join ep00000000000101_4 ep00000000000101_5)))
private theorem idp00000000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000010.list =
    C ((2:ℤ)^705) * horner X vp00000000000101.list + horner X ep00000000000101.list := by
  exact edge_identity (B := (2:ℤ)^1158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000101 : Branch 1 (-1761639/1000000 : ℚ) vp0000000000010 := by
  apply branch_checked idp00000000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-2261639/500000 : ℚ) by norm_num]
  exact coverp00000000000101
theorem coverp0000000000010 : Covers (-1761639/1000000 : ℚ) vp0000000000010 := join_branches bp00000000000100 bp00000000000101
noncomputable def vp000000000001 : Blocks := NextProof.EdgeRecovery.R000000000001.C.data
private theorem bp0000000000010 : Branch 0 (-1761639/2000000 : ℚ) vp000000000001 := by
  apply branch_left_normalized (c:=vp0000000000010) (k:=0) (m:=702) (by decide +kernel)
  rw [show 2*(-1761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1761639/1000000 : ℚ) by norm_num]
  exact coverp0000000000010
private noncomputable def ep0000000000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000011-E-0000.bin"
private noncomputable def ep0000000000011_1 : Blocks := edgeBlocks% "full/vectors/0000000000011-E-0001.bin"
private noncomputable def ep0000000000011_2 : Blocks := edgeBlocks% "full/vectors/0000000000011-E-0002.bin"
private noncomputable def ep0000000000011_3 : Blocks := edgeBlocks% "full/vectors/0000000000011-E-0003.bin"
private noncomputable def ep0000000000011_4 : Blocks := edgeBlocks% "full/vectors/0000000000011-E-0004.bin"
private noncomputable def ep0000000000011_5 : Blocks := edgeBlocks% "full/vectors/0000000000011-E-0005.bin"
private noncomputable def ep0000000000011_6 : Blocks := edgeBlocks% "full/vectors/0000000000011-E-0006.bin"
private noncomputable def ep0000000000011_7 : Blocks := edgeBlocks% "full/vectors/0000000000011-E-0007.bin"
private noncomputable def ep0000000000011_8 : Blocks := edgeBlocks% "full/vectors/0000000000011-E-0008.bin"
private noncomputable def ep0000000000011_9 : Blocks := edgeBlocks% "full/vectors/0000000000011-E-0009.bin"
noncomputable def ep0000000000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000000000011_0 ep0000000000011_1) (Blocks.join ep0000000000011_2 (Blocks.join ep0000000000011_3 ep0000000000011_4))) (Blocks.join (Blocks.join ep0000000000011_5 ep0000000000011_6) (Blocks.join ep0000000000011_7 (Blocks.join ep0000000000011_8 ep0000000000011_9))))
private theorem idp0000000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000001.list =
    C ((2:ℤ)^1260) * horner X vp0000000000011.list + horner X ep0000000000011.list := by
  exact edge_identity (B := (2:ℤ)^2076) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000011 : Branch 1 (-1761639/2000000 : ℚ) vp000000000001 := by
  apply branch_checked idp0000000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-2761639/1000000 : ℚ) by norm_num]
  exact coverp0000000000011
theorem coverp000000000001 : Covers (-1761639/2000000 : ℚ) vp000000000001 := join_branches bp0000000000010 bp0000000000011
noncomputable def vp00000000000 : Blocks := NextProof.EdgeRecovery.R000000000001.P.data
private theorem bp000000000000 : Branch 0 (1906884279970892581/32000000000000000000 : ℚ) vp00000000000 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp000000000000) (k:=0) (m:=14079) (by decide +kernel)
  rw [show 2*(1906884279970892581/32000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/16000000000000000000 : ℚ) by norm_num]
  exact coverp000000000000
noncomputable def ep000000000001 : Blocks := NextProof.EdgeRecovery.R000000000001.E.data
private theorem idp000000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000.list =
    C ((2:ℤ)^14341) * horner X vp000000000001.list + horner X ep000000000001.list := by
  exact NextProof.EdgeRecovery.R000000000001.identity
private theorem bp000000000001 : Branch 1 (1906884279970892581/32000000000000000000 : ℚ) vp00000000000 := by
  apply branch_checked idp000000000001 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/32000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-14093115720029107419/16000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp000000000001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp00000000000 : Covers (1906884279970892581/32000000000000000000 : ℚ) vp00000000000 := join_branches bp000000000000 bp000000000001
end NextProof.EdgeFull

