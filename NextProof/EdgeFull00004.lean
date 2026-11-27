import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000000000000111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000111111-V-0000.bin"
noncomputable def vp0000000000000111111 : Blocks := vp0000000000000111111_0
theorem coverp0000000000000111111 : Covers (-746014/15625 : ℚ) vp0000000000000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000111110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000111110-V-0000.bin"
noncomputable def vp0000000000000111110 : Blocks := vp0000000000000111110_0
theorem coverp0000000000000111110 : Covers (-730389/15625 : ℚ) vp0000000000000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011111_0 : Blocks := edgeBlocks% "full/vectors/000000000000011111-V-0000.bin"
noncomputable def vp000000000000011111 : Blocks := vp000000000000011111_0
private theorem bp0000000000000111110 : Branch 0 (-730389/31250 : ℚ) vp000000000000011111 := by
  apply branch_left_normalized (c:=vp0000000000000111110) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-730389/31250 : ℚ) - ((0:ℤ):ℚ) = (-730389/15625 : ℚ) by norm_num]
  exact coverp0000000000000111110
private noncomputable def ep0000000000000111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000111111-E-0000.bin"
noncomputable def ep0000000000000111111 : Blocks := ep0000000000000111111_0
private theorem idp0000000000000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011111.list =
    C ((2:ℤ)^45) * horner X vp0000000000000111111.list + horner X ep0000000000000111111.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000111111 : Branch 1 (-730389/31250 : ℚ) vp000000000000011111 := by
  apply branch_checked idp0000000000000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-730389/31250 : ℚ) - ((1:ℤ):ℚ) = (-746014/15625 : ℚ) by norm_num]
  exact coverp0000000000000111111
theorem coverp000000000000011111 : Covers (-730389/31250 : ℚ) vp000000000000011111 := join_branches bp0000000000000111110 bp0000000000000111111
private noncomputable def vp0000000000000111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000111101-V-0000.bin"
noncomputable def vp0000000000000111101 : Blocks := vp0000000000000111101_0
theorem coverp0000000000000111101 : Covers (-714764/15625 : ℚ) vp0000000000000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000111100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000111100-V-0000.bin"
noncomputable def vp0000000000000111100 : Blocks := vp0000000000000111100_0
theorem coverp0000000000000111100 : Covers (-699139/15625 : ℚ) vp0000000000000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011110_0 : Blocks := edgeBlocks% "full/vectors/000000000000011110-V-0000.bin"
noncomputable def vp000000000000011110 : Blocks := vp000000000000011110_0
private theorem bp0000000000000111100 : Branch 0 (-699139/31250 : ℚ) vp000000000000011110 := by
  apply branch_left_normalized (c:=vp0000000000000111100) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-699139/31250 : ℚ) - ((0:ℤ):ℚ) = (-699139/15625 : ℚ) by norm_num]
  exact coverp0000000000000111100
private noncomputable def ep0000000000000111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000111101-E-0000.bin"
noncomputable def ep0000000000000111101 : Blocks := ep0000000000000111101_0
private theorem idp0000000000000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011110.list =
    C ((2:ℤ)^45) * horner X vp0000000000000111101.list + horner X ep0000000000000111101.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000111101 : Branch 1 (-699139/31250 : ℚ) vp000000000000011110 := by
  apply branch_checked idp0000000000000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-699139/31250 : ℚ) - ((1:ℤ):ℚ) = (-714764/15625 : ℚ) by norm_num]
  exact coverp0000000000000111101
theorem coverp000000000000011110 : Covers (-699139/31250 : ℚ) vp000000000000011110 := join_branches bp0000000000000111100 bp0000000000000111101
private noncomputable def vp00000000000001111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001111-V-0000.bin"
noncomputable def vp00000000000001111 : Blocks := vp00000000000001111_0
private theorem bp000000000000011110 : Branch 0 (-699139/62500 : ℚ) vp00000000000001111 := by
  apply branch_left_normalized (c:=vp000000000000011110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-699139/62500 : ℚ) - ((0:ℤ):ℚ) = (-699139/31250 : ℚ) by norm_num]
  exact coverp000000000000011110
private noncomputable def ep000000000000011111_0 : Blocks := edgeBlocks% "full/vectors/000000000000011111-E-0000.bin"
noncomputable def ep000000000000011111 : Blocks := ep000000000000011111_0
private theorem idp000000000000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001111.list =
    C ((2:ℤ)^78) * horner X vp000000000000011111.list + horner X ep000000000000011111.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011111 : Branch 1 (-699139/62500 : ℚ) vp00000000000001111 := by
  apply branch_checked idp000000000000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-699139/62500 : ℚ) - ((1:ℤ):ℚ) = (-730389/31250 : ℚ) by norm_num]
  exact coverp000000000000011111
theorem coverp00000000000001111 : Covers (-699139/62500 : ℚ) vp00000000000001111 := join_branches bp000000000000011110 bp000000000000011111
private noncomputable def vp000000000000011101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011101-V-0000.bin"
noncomputable def vp000000000000011101 : Blocks := vp000000000000011101_0
theorem coverp000000000000011101 : Covers (-667889/31250 : ℚ) vp000000000000011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000111001-V-0000.bin"
noncomputable def vp0000000000000111001 : Blocks := vp0000000000000111001_0
theorem coverp0000000000000111001 : Covers (-652264/15625 : ℚ) vp0000000000000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000111000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000111000-V-0000.bin"
noncomputable def vp0000000000000111000 : Blocks := vp0000000000000111000_0
theorem coverp0000000000000111000 : Covers (-636639/15625 : ℚ) vp0000000000000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011100_0 : Blocks := edgeBlocks% "full/vectors/000000000000011100-V-0000.bin"
noncomputable def vp000000000000011100 : Blocks := vp000000000000011100_0
private theorem bp0000000000000111000 : Branch 0 (-636639/31250 : ℚ) vp000000000000011100 := by
  apply branch_left_normalized (c:=vp0000000000000111000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-636639/31250 : ℚ) - ((0:ℤ):ℚ) = (-636639/15625 : ℚ) by norm_num]
  exact coverp0000000000000111000
private noncomputable def ep0000000000000111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000111001-E-0000.bin"
noncomputable def ep0000000000000111001 : Blocks := ep0000000000000111001_0
private theorem idp0000000000000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011100.list =
    C ((2:ℤ)^48) * horner X vp0000000000000111001.list + horner X ep0000000000000111001.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000111001 : Branch 1 (-636639/31250 : ℚ) vp000000000000011100 := by
  apply branch_checked idp0000000000000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-636639/31250 : ℚ) - ((1:ℤ):ℚ) = (-652264/15625 : ℚ) by norm_num]
  exact coverp0000000000000111001
theorem coverp000000000000011100 : Covers (-636639/31250 : ℚ) vp000000000000011100 := join_branches bp0000000000000111000 bp0000000000000111001
private noncomputable def vp00000000000001110_0 : Blocks := edgeBlocks% "full/vectors/00000000000001110-V-0000.bin"
noncomputable def vp00000000000001110 : Blocks := vp00000000000001110_0
private theorem bp000000000000011100 : Branch 0 (-636639/62500 : ℚ) vp00000000000001110 := by
  apply branch_left_normalized (c:=vp000000000000011100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-636639/62500 : ℚ) - ((0:ℤ):ℚ) = (-636639/31250 : ℚ) by norm_num]
  exact coverp000000000000011100
private noncomputable def ep000000000000011101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011101-E-0000.bin"
noncomputable def ep000000000000011101 : Blocks := ep000000000000011101_0
private theorem idp000000000000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001110.list =
    C ((2:ℤ)^82) * horner X vp000000000000011101.list + horner X ep000000000000011101.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011101 : Branch 1 (-636639/62500 : ℚ) vp00000000000001110 := by
  apply branch_checked idp000000000000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-636639/62500 : ℚ) - ((1:ℤ):ℚ) = (-667889/31250 : ℚ) by norm_num]
  exact coverp000000000000011101
theorem coverp00000000000001110 : Covers (-636639/62500 : ℚ) vp00000000000001110 := join_branches bp000000000000011100 bp000000000000011101
private noncomputable def vp0000000000000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000111-V-0000.bin"
private noncomputable def vp0000000000000111_1 : Blocks := edgeBlocks% "full/vectors/0000000000000111-V-0001.bin"
noncomputable def vp0000000000000111 : Blocks := (Blocks.join vp0000000000000111_0 vp0000000000000111_1)
private theorem bp00000000000001110 : Branch 0 (-636639/125000 : ℚ) vp0000000000000111 := by
  apply branch_left_normalized (c:=vp00000000000001110) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-636639/62500 : ℚ) by norm_num]
  exact coverp00000000000001110
private noncomputable def ep00000000000001111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001111-E-0000.bin"
private noncomputable def ep00000000000001111_1 : Blocks := edgeBlocks% "full/vectors/00000000000001111-E-0001.bin"
noncomputable def ep00000000000001111 : Blocks := (Blocks.join ep00000000000001111_0 ep00000000000001111_1)
private theorem idp00000000000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000111.list =
    C ((2:ℤ)^149) * horner X vp00000000000001111.list + horner X ep00000000000001111.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001111 : Branch 1 (-636639/125000 : ℚ) vp0000000000000111 := by
  apply branch_checked idp00000000000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-699139/62500 : ℚ) by norm_num]
  exact coverp00000000000001111
theorem coverp0000000000000111 : Covers (-636639/125000 : ℚ) vp0000000000000111 := join_branches bp00000000000001110 bp00000000000001111
private noncomputable def vp0000000000000110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110111-V-0000.bin"
noncomputable def vp0000000000000110111 : Blocks := vp0000000000000110111_0
theorem coverp0000000000000110111 : Covers (-621014/15625 : ℚ) vp0000000000000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001101101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101101-V-0000.bin"
noncomputable def vp00000000000001101101 : Blocks := vp00000000000001101101_0
theorem coverp00000000000001101101 : Covers (-1226403/15625 : ℚ) vp00000000000001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011011001_0 : Blocks := edgeBlocks% "full/vectors/000000000000011011001-V-0000.bin"
noncomputable def vp000000000000011011001 : Blocks := vp000000000000011011001_0
theorem coverp000000000000011011001 : Covers (-2437181/15625 : ℚ) vp000000000000011011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001101100011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101100011-V-0000.bin"
noncomputable def vp00000000000001101100011 : Blocks := vp00000000000001101100011_0
theorem coverp00000000000001101100011 : Covers (-9733099/15625 : ℚ) vp00000000000001101100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011011000101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011011000101-V-0000.bin"
noncomputable def vp000000000000011011000101 : Blocks := vp000000000000011011000101_0
theorem coverp000000000000011011000101 : Covers (-19450573/15625 : ℚ) vp000000000000011011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011011000100_0 : Blocks := edgeBlocks% "full/vectors/000000000000011011000100-V-0000.bin"
noncomputable def vp000000000000011011000100 : Blocks := vp000000000000011011000100_0
theorem coverp000000000000011011000100 : Covers (-19434948/15625 : ℚ) vp000000000000011011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001101100010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101100010-V-0000.bin"
noncomputable def vp00000000000001101100010 : Blocks := vp00000000000001101100010_0
private theorem bp000000000000011011000100 : Branch 0 (-9717474/15625 : ℚ) vp00000000000001101100010 := by
  apply branch_left_normalized (c:=vp000000000000011011000100) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-9717474/15625 : ℚ) - ((0:ℤ):ℚ) = (-19434948/15625 : ℚ) by norm_num]
  exact coverp000000000000011011000100
private noncomputable def ep000000000000011011000101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011011000101-E-0000.bin"
noncomputable def ep000000000000011011000101 : Blocks := ep000000000000011011000101_0
private theorem idp000000000000011011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001101100010.list =
    C ((2:ℤ)^13) * horner X vp000000000000011011000101.list + horner X ep000000000000011011000101.list := by
  exact edge_identity (B := (2:ℤ)^107) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011011000101 : Branch 1 (-9717474/15625 : ℚ) vp00000000000001101100010 := by
  apply branch_checked idp000000000000011011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-9717474/15625 : ℚ) - ((1:ℤ):ℚ) = (-19450573/15625 : ℚ) by norm_num]
  exact coverp000000000000011011000101
theorem coverp00000000000001101100010 : Covers (-9717474/15625 : ℚ) vp00000000000001101100010 := join_branches bp000000000000011011000100 bp000000000000011011000101
private noncomputable def vp0000000000000110110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110110001-V-0000.bin"
noncomputable def vp0000000000000110110001 : Blocks := vp0000000000000110110001_0
private theorem bp00000000000001101100010 : Branch 0 (-4858737/15625 : ℚ) vp0000000000000110110001 := by
  apply branch_left_normalized (c:=vp00000000000001101100010) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-4858737/15625 : ℚ) - ((0:ℤ):ℚ) = (-9717474/15625 : ℚ) by norm_num]
  exact coverp00000000000001101100010
private noncomputable def ep00000000000001101100011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101100011-E-0000.bin"
noncomputable def ep00000000000001101100011 : Blocks := ep00000000000001101100011_0
private theorem idp00000000000001101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110110001.list =
    C ((2:ℤ)^16) * horner X vp00000000000001101100011.list + horner X ep00000000000001101100011.list := by
  exact edge_identity (B := (2:ℤ)^112) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001101100011 : Branch 1 (-4858737/15625 : ℚ) vp0000000000000110110001 := by
  apply branch_checked idp00000000000001101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-4858737/15625 : ℚ) - ((1:ℤ):ℚ) = (-9733099/15625 : ℚ) by norm_num]
  exact coverp00000000000001101100011
theorem coverp0000000000000110110001 : Covers (-4858737/15625 : ℚ) vp0000000000000110110001 := join_branches bp00000000000001101100010 bp00000000000001101100011
private noncomputable def vp000000000000011011000011_0 : Blocks := edgeBlocks% "full/vectors/000000000000011011000011-V-0000.bin"
noncomputable def vp000000000000011011000011 : Blocks := vp000000000000011011000011_0
theorem coverp000000000000011011000011 : Covers (-19419323/15625 : ℚ) vp000000000000011011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011011000010_0 : Blocks := edgeBlocks% "full/vectors/000000000000011011000010-V-0000.bin"
noncomputable def vp000000000000011011000010 : Blocks := vp000000000000011011000010_0
theorem coverp000000000000011011000010 : Covers (-19403698/15625 : ℚ) vp000000000000011011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001101100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101100001-V-0000.bin"
noncomputable def vp00000000000001101100001 : Blocks := vp00000000000001101100001_0
private theorem bp000000000000011011000010 : Branch 0 (-9701849/15625 : ℚ) vp00000000000001101100001 := by
  apply branch_left_normalized (c:=vp000000000000011011000010) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-9701849/15625 : ℚ) - ((0:ℤ):ℚ) = (-19403698/15625 : ℚ) by norm_num]
  exact coverp000000000000011011000010
private noncomputable def ep000000000000011011000011_0 : Blocks := edgeBlocks% "full/vectors/000000000000011011000011-E-0000.bin"
noncomputable def ep000000000000011011000011 : Blocks := ep000000000000011011000011_0
private theorem idp000000000000011011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001101100001.list =
    C ((2:ℤ)^13) * horner X vp000000000000011011000011.list + horner X ep000000000000011011000011.list := by
  exact edge_identity (B := (2:ℤ)^108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011011000011 : Branch 1 (-9701849/15625 : ℚ) vp00000000000001101100001 := by
  apply branch_checked idp000000000000011011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-9701849/15625 : ℚ) - ((1:ℤ):ℚ) = (-19419323/15625 : ℚ) by norm_num]
  exact coverp000000000000011011000011
theorem coverp00000000000001101100001 : Covers (-9701849/15625 : ℚ) vp00000000000001101100001 := join_branches bp000000000000011011000010 bp000000000000011011000011
private noncomputable def vp00000000000001101100000_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101100000-V-0000.bin"
noncomputable def vp00000000000001101100000 : Blocks := vp00000000000001101100000_0
theorem coverp00000000000001101100000 : Covers (-9686224/15625 : ℚ) vp00000000000001101100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000110110000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110110000-V-0000.bin"
noncomputable def vp0000000000000110110000 : Blocks := vp0000000000000110110000_0
private theorem bp00000000000001101100000 : Branch 0 (-4843112/15625 : ℚ) vp0000000000000110110000 := by
  apply branch_left_normalized (c:=vp00000000000001101100000) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-4843112/15625 : ℚ) - ((0:ℤ):ℚ) = (-9686224/15625 : ℚ) by norm_num]
  exact coverp00000000000001101100000
private noncomputable def ep00000000000001101100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101100001-E-0000.bin"
noncomputable def ep00000000000001101100001 : Blocks := ep00000000000001101100001_0
private theorem idp00000000000001101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110110000.list =
    C ((2:ℤ)^15) * horner X vp00000000000001101100001.list + horner X ep00000000000001101100001.list := by
  exact edge_identity (B := (2:ℤ)^111) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001101100001 : Branch 1 (-4843112/15625 : ℚ) vp0000000000000110110000 := by
  apply branch_checked idp00000000000001101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-4843112/15625 : ℚ) - ((1:ℤ):ℚ) = (-9701849/15625 : ℚ) by norm_num]
  exact coverp00000000000001101100001
theorem coverp0000000000000110110000 : Covers (-4843112/15625 : ℚ) vp0000000000000110110000 := join_branches bp00000000000001101100000 bp00000000000001101100001
private noncomputable def vp000000000000011011000_0 : Blocks := edgeBlocks% "full/vectors/000000000000011011000-V-0000.bin"
noncomputable def vp000000000000011011000 : Blocks := vp000000000000011011000_0
private theorem bp0000000000000110110000 : Branch 0 (-2421556/15625 : ℚ) vp000000000000011011000 := by
  apply branch_left_normalized (c:=vp0000000000000110110000) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-2421556/15625 : ℚ) - ((0:ℤ):ℚ) = (-4843112/15625 : ℚ) by norm_num]
  exact coverp0000000000000110110000
private noncomputable def ep0000000000000110110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110110001-E-0000.bin"
noncomputable def ep0000000000000110110001 : Blocks := ep0000000000000110110001_0
private theorem idp0000000000000110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011011000.list =
    C ((2:ℤ)^19) * horner X vp0000000000000110110001.list + horner X ep0000000000000110110001.list := by
  exact edge_identity (B := (2:ℤ)^116) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110110001 : Branch 1 (-2421556/15625 : ℚ) vp000000000000011011000 := by
  apply branch_checked idp0000000000000110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2421556/15625 : ℚ) - ((1:ℤ):ℚ) = (-4858737/15625 : ℚ) by norm_num]
  exact coverp0000000000000110110001
theorem coverp000000000000011011000 : Covers (-2421556/15625 : ℚ) vp000000000000011011000 := join_branches bp0000000000000110110000 bp0000000000000110110001
private noncomputable def vp00000000000001101100_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101100-V-0000.bin"
noncomputable def vp00000000000001101100 : Blocks := vp00000000000001101100_0
private theorem bp000000000000011011000 : Branch 0 (-1210778/15625 : ℚ) vp00000000000001101100 := by
  apply branch_left_normalized (c:=vp000000000000011011000) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-1210778/15625 : ℚ) - ((0:ℤ):ℚ) = (-2421556/15625 : ℚ) by norm_num]
  exact coverp000000000000011011000
private noncomputable def ep000000000000011011001_0 : Blocks := edgeBlocks% "full/vectors/000000000000011011001-E-0000.bin"
noncomputable def ep000000000000011011001 : Blocks := ep000000000000011011001_0
private theorem idp000000000000011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001101100.list =
    C ((2:ℤ)^24) * horner X vp000000000000011011001.list + horner X ep000000000000011011001.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011011001 : Branch 1 (-1210778/15625 : ℚ) vp00000000000001101100 := by
  apply branch_checked idp000000000000011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1210778/15625 : ℚ) - ((1:ℤ):ℚ) = (-2437181/15625 : ℚ) by norm_num]
  exact coverp000000000000011011001
theorem coverp00000000000001101100 : Covers (-1210778/15625 : ℚ) vp00000000000001101100 := join_branches bp000000000000011011000 bp000000000000011011001
private noncomputable def vp0000000000000110110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110110-V-0000.bin"
noncomputable def vp0000000000000110110 : Blocks := vp0000000000000110110_0
private theorem bp00000000000001101100 : Branch 0 (-605389/15625 : ℚ) vp0000000000000110110 := by
  apply branch_left_normalized (c:=vp00000000000001101100) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-605389/15625 : ℚ) - ((0:ℤ):ℚ) = (-1210778/15625 : ℚ) by norm_num]
  exact coverp00000000000001101100
private noncomputable def ep00000000000001101101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101101-E-0000.bin"
noncomputable def ep00000000000001101101 : Blocks := ep00000000000001101101_0
private theorem idp00000000000001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110110.list =
    C ((2:ℤ)^35) * horner X vp00000000000001101101.list + horner X ep00000000000001101101.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001101101 : Branch 1 (-605389/15625 : ℚ) vp0000000000000110110 := by
  apply branch_checked idp00000000000001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-605389/15625 : ℚ) - ((1:ℤ):ℚ) = (-1226403/15625 : ℚ) by norm_num]
  exact coverp00000000000001101101
theorem coverp0000000000000110110 : Covers (-605389/15625 : ℚ) vp0000000000000110110 := join_branches bp00000000000001101100 bp00000000000001101101
private noncomputable def vp000000000000011011_0 : Blocks := edgeBlocks% "full/vectors/000000000000011011-V-0000.bin"
noncomputable def vp000000000000011011 : Blocks := vp000000000000011011_0
private theorem bp0000000000000110110 : Branch 0 (-605389/31250 : ℚ) vp000000000000011011 := by
  apply branch_left_normalized (c:=vp0000000000000110110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-605389/31250 : ℚ) - ((0:ℤ):ℚ) = (-605389/15625 : ℚ) by norm_num]
  exact coverp0000000000000110110
private noncomputable def ep0000000000000110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110111-E-0000.bin"
noncomputable def ep0000000000000110111 : Blocks := ep0000000000000110111_0
private theorem idp0000000000000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011011.list =
    C ((2:ℤ)^54) * horner X vp0000000000000110111.list + horner X ep0000000000000110111.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110111 : Branch 1 (-605389/31250 : ℚ) vp000000000000011011 := by
  apply branch_checked idp0000000000000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-605389/31250 : ℚ) - ((1:ℤ):ℚ) = (-621014/15625 : ℚ) by norm_num]
  exact coverp0000000000000110111
theorem coverp000000000000011011 : Covers (-605389/31250 : ℚ) vp000000000000011011 := join_branches bp0000000000000110110 bp0000000000000110111
private noncomputable def vp000000000000011010111_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010111-V-0000.bin"
noncomputable def vp000000000000011010111 : Blocks := vp000000000000011010111_0
theorem coverp000000000000011010111 : Covers (-2405931/15625 : ℚ) vp000000000000011010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011010110_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010110-V-0000.bin"
noncomputable def vp000000000000011010110 : Blocks := vp000000000000011010110_0
theorem coverp000000000000011010110 : Covers (-2390306/15625 : ℚ) vp000000000000011010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101011-V-0000.bin"
noncomputable def vp00000000000001101011 : Blocks := vp00000000000001101011_0
private theorem bp000000000000011010110 : Branch 0 (-1195153/15625 : ℚ) vp00000000000001101011 := by
  apply branch_left_normalized (c:=vp000000000000011010110) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-1195153/15625 : ℚ) - ((0:ℤ):ℚ) = (-2390306/15625 : ℚ) by norm_num]
  exact coverp000000000000011010110
private noncomputable def ep000000000000011010111_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010111-E-0000.bin"
noncomputable def ep000000000000011010111 : Blocks := ep000000000000011010111_0
private theorem idp000000000000011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001101011.list =
    C ((2:ℤ)^24) * horner X vp000000000000011010111.list + horner X ep000000000000011010111.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011010111 : Branch 1 (-1195153/15625 : ℚ) vp00000000000001101011 := by
  apply branch_checked idp000000000000011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1195153/15625 : ℚ) - ((1:ℤ):ℚ) = (-2405931/15625 : ℚ) by norm_num]
  exact coverp000000000000011010111
theorem coverp00000000000001101011 : Covers (-1195153/15625 : ℚ) vp00000000000001101011 := join_branches bp000000000000011010110 bp000000000000011010111
private noncomputable def vp000000000000011010101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010101-V-0000.bin"
noncomputable def vp000000000000011010101 : Blocks := vp000000000000011010101_0
theorem coverp000000000000011010101 : Covers (-2374681/15625 : ℚ) vp000000000000011010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001101010011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101010011-V-0000.bin"
noncomputable def vp00000000000001101010011 : Blocks := vp00000000000001101010011_0
theorem coverp00000000000001101010011 : Covers (-9483099/15625 : ℚ) vp00000000000001101010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011010100101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010100101-V-0000.bin"
noncomputable def vp000000000000011010100101 : Blocks := vp000000000000011010100101_0
theorem coverp000000000000011010100101 : Covers (-18950573/15625 : ℚ) vp000000000000011010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011010100100_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010100100-V-0000.bin"
noncomputable def vp000000000000011010100100 : Blocks := vp000000000000011010100100_0
theorem coverp000000000000011010100100 : Covers (-18934948/15625 : ℚ) vp000000000000011010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001101010010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101010010-V-0000.bin"
noncomputable def vp00000000000001101010010 : Blocks := vp00000000000001101010010_0
private theorem bp000000000000011010100100 : Branch 0 (-9467474/15625 : ℚ) vp00000000000001101010010 := by
  apply branch_left_normalized (c:=vp000000000000011010100100) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-9467474/15625 : ℚ) - ((0:ℤ):ℚ) = (-18934948/15625 : ℚ) by norm_num]
  exact coverp000000000000011010100100
private noncomputable def ep000000000000011010100101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010100101-E-0000.bin"
noncomputable def ep000000000000011010100101 : Blocks := ep000000000000011010100101_0
private theorem idp000000000000011010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001101010010.list =
    C ((2:ℤ)^13) * horner X vp000000000000011010100101.list + horner X ep000000000000011010100101.list := by
  exact edge_identity (B := (2:ℤ)^106) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011010100101 : Branch 1 (-9467474/15625 : ℚ) vp00000000000001101010010 := by
  apply branch_checked idp000000000000011010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-9467474/15625 : ℚ) - ((1:ℤ):ℚ) = (-18950573/15625 : ℚ) by norm_num]
  exact coverp000000000000011010100101
theorem coverp00000000000001101010010 : Covers (-9467474/15625 : ℚ) vp00000000000001101010010 := join_branches bp000000000000011010100100 bp000000000000011010100101
private noncomputable def vp0000000000000110101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110101001-V-0000.bin"
noncomputable def vp0000000000000110101001 : Blocks := vp0000000000000110101001_0
private theorem bp00000000000001101010010 : Branch 0 (-4733737/15625 : ℚ) vp0000000000000110101001 := by
  apply branch_left_normalized (c:=vp00000000000001101010010) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-4733737/15625 : ℚ) - ((0:ℤ):ℚ) = (-9467474/15625 : ℚ) by norm_num]
  exact coverp00000000000001101010010
private noncomputable def ep00000000000001101010011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101010011-E-0000.bin"
noncomputable def ep00000000000001101010011 : Blocks := ep00000000000001101010011_0
private theorem idp00000000000001101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110101001.list =
    C ((2:ℤ)^16) * horner X vp00000000000001101010011.list + horner X ep00000000000001101010011.list := by
  exact edge_identity (B := (2:ℤ)^111) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001101010011 : Branch 1 (-4733737/15625 : ℚ) vp0000000000000110101001 := by
  apply branch_checked idp00000000000001101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4733737/15625 : ℚ) - ((1:ℤ):ℚ) = (-9483099/15625 : ℚ) by norm_num]
  exact coverp00000000000001101010011
theorem coverp0000000000000110101001 : Covers (-4733737/15625 : ℚ) vp0000000000000110101001 := join_branches bp00000000000001101010010 bp00000000000001101010011
private noncomputable def vp00000000000001101010001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101010001-V-0000.bin"
noncomputable def vp00000000000001101010001 : Blocks := vp00000000000001101010001_0
theorem coverp00000000000001101010001 : Covers (-9451849/15625 : ℚ) vp00000000000001101010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001101010000_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101010000-V-0000.bin"
noncomputable def vp00000000000001101010000 : Blocks := vp00000000000001101010000_0
theorem coverp00000000000001101010000 : Covers (-9436224/15625 : ℚ) vp00000000000001101010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000110101000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110101000-V-0000.bin"
noncomputable def vp0000000000000110101000 : Blocks := vp0000000000000110101000_0
private theorem bp00000000000001101010000 : Branch 0 (-4718112/15625 : ℚ) vp0000000000000110101000 := by
  apply branch_left_normalized (c:=vp00000000000001101010000) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-4718112/15625 : ℚ) - ((0:ℤ):ℚ) = (-9436224/15625 : ℚ) by norm_num]
  exact coverp00000000000001101010000
private noncomputable def ep00000000000001101010001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101010001-E-0000.bin"
noncomputable def ep00000000000001101010001 : Blocks := ep00000000000001101010001_0
private theorem idp00000000000001101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110101000.list =
    C ((2:ℤ)^15) * horner X vp00000000000001101010001.list + horner X ep00000000000001101010001.list := by
  exact edge_identity (B := (2:ℤ)^111) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001101010001 : Branch 1 (-4718112/15625 : ℚ) vp0000000000000110101000 := by
  apply branch_checked idp00000000000001101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4718112/15625 : ℚ) - ((1:ℤ):ℚ) = (-9451849/15625 : ℚ) by norm_num]
  exact coverp00000000000001101010001
theorem coverp0000000000000110101000 : Covers (-4718112/15625 : ℚ) vp0000000000000110101000 := join_branches bp00000000000001101010000 bp00000000000001101010001
private noncomputable def vp000000000000011010100_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010100-V-0000.bin"
noncomputable def vp000000000000011010100 : Blocks := vp000000000000011010100_0
private theorem bp0000000000000110101000 : Branch 0 (-2359056/15625 : ℚ) vp000000000000011010100 := by
  apply branch_left_normalized (c:=vp0000000000000110101000) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-2359056/15625 : ℚ) - ((0:ℤ):ℚ) = (-4718112/15625 : ℚ) by norm_num]
  exact coverp0000000000000110101000
private noncomputable def ep0000000000000110101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110101001-E-0000.bin"
noncomputable def ep0000000000000110101001 : Blocks := ep0000000000000110101001_0
private theorem idp0000000000000110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011010100.list =
    C ((2:ℤ)^19) * horner X vp0000000000000110101001.list + horner X ep0000000000000110101001.list := by
  exact edge_identity (B := (2:ℤ)^116) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110101001 : Branch 1 (-2359056/15625 : ℚ) vp000000000000011010100 := by
  apply branch_checked idp0000000000000110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-2359056/15625 : ℚ) - ((1:ℤ):ℚ) = (-4733737/15625 : ℚ) by norm_num]
  exact coverp0000000000000110101001
theorem coverp000000000000011010100 : Covers (-2359056/15625 : ℚ) vp000000000000011010100 := join_branches bp0000000000000110101000 bp0000000000000110101001
private noncomputable def vp00000000000001101010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101010-V-0000.bin"
noncomputable def vp00000000000001101010 : Blocks := vp00000000000001101010_0
private theorem bp000000000000011010100 : Branch 0 (-1179528/15625 : ℚ) vp00000000000001101010 := by
  apply branch_left_normalized (c:=vp000000000000011010100) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-1179528/15625 : ℚ) - ((0:ℤ):ℚ) = (-2359056/15625 : ℚ) by norm_num]
  exact coverp000000000000011010100
private noncomputable def ep000000000000011010101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010101-E-0000.bin"
noncomputable def ep000000000000011010101 : Blocks := ep000000000000011010101_0
private theorem idp000000000000011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001101010.list =
    C ((2:ℤ)^25) * horner X vp000000000000011010101.list + horner X ep000000000000011010101.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011010101 : Branch 1 (-1179528/15625 : ℚ) vp00000000000001101010 := by
  apply branch_checked idp000000000000011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1179528/15625 : ℚ) - ((1:ℤ):ℚ) = (-2374681/15625 : ℚ) by norm_num]
  exact coverp000000000000011010101
theorem coverp00000000000001101010 : Covers (-1179528/15625 : ℚ) vp00000000000001101010 := join_branches bp000000000000011010100 bp000000000000011010101
private noncomputable def vp0000000000000110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110101-V-0000.bin"
noncomputable def vp0000000000000110101 : Blocks := vp0000000000000110101_0
private theorem bp00000000000001101010 : Branch 0 (-589764/15625 : ℚ) vp0000000000000110101 := by
  apply branch_left_normalized (c:=vp00000000000001101010) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-589764/15625 : ℚ) - ((0:ℤ):ℚ) = (-1179528/15625 : ℚ) by norm_num]
  exact coverp00000000000001101010
private noncomputable def ep00000000000001101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101011-E-0000.bin"
noncomputable def ep00000000000001101011 : Blocks := ep00000000000001101011_0
private theorem idp00000000000001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110101.list =
    C ((2:ℤ)^35) * horner X vp00000000000001101011.list + horner X ep00000000000001101011.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001101011 : Branch 1 (-589764/15625 : ℚ) vp0000000000000110101 := by
  apply branch_checked idp00000000000001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-589764/15625 : ℚ) - ((1:ℤ):ℚ) = (-1195153/15625 : ℚ) by norm_num]
  exact coverp00000000000001101011
theorem coverp0000000000000110101 : Covers (-589764/15625 : ℚ) vp0000000000000110101 := join_branches bp00000000000001101010 bp00000000000001101011
private noncomputable def vp000000000000011010011_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010011-V-0000.bin"
noncomputable def vp000000000000011010011 : Blocks := vp000000000000011010011_0
theorem coverp000000000000011010011 : Covers (-2343431/15625 : ℚ) vp000000000000011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011010010_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010010-V-0000.bin"
noncomputable def vp000000000000011010010 : Blocks := vp000000000000011010010_0
theorem coverp000000000000011010010 : Covers (-2327806/15625 : ℚ) vp000000000000011010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001101001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101001-V-0000.bin"
noncomputable def vp00000000000001101001 : Blocks := vp00000000000001101001_0
private theorem bp000000000000011010010 : Branch 0 (-1163903/15625 : ℚ) vp00000000000001101001 := by
  apply branch_left_normalized (c:=vp000000000000011010010) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-1163903/15625 : ℚ) - ((0:ℤ):ℚ) = (-2327806/15625 : ℚ) by norm_num]
  exact coverp000000000000011010010
private noncomputable def ep000000000000011010011_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010011-E-0000.bin"
noncomputable def ep000000000000011010011 : Blocks := ep000000000000011010011_0
private theorem idp000000000000011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001101001.list =
    C ((2:ℤ)^23) * horner X vp000000000000011010011.list + horner X ep000000000000011010011.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011010011 : Branch 1 (-1163903/15625 : ℚ) vp00000000000001101001 := by
  apply branch_checked idp000000000000011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1163903/15625 : ℚ) - ((1:ℤ):ℚ) = (-2343431/15625 : ℚ) by norm_num]
  exact coverp000000000000011010011
theorem coverp00000000000001101001 : Covers (-1163903/15625 : ℚ) vp00000000000001101001 := join_branches bp000000000000011010010 bp000000000000011010011
private noncomputable def vp00000000000001101000_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101000-V-0000.bin"
noncomputable def vp00000000000001101000 : Blocks := vp00000000000001101000_0
theorem coverp00000000000001101000 : Covers (-1148278/15625 : ℚ) vp00000000000001101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000110100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110100-V-0000.bin"
noncomputable def vp0000000000000110100 : Blocks := vp0000000000000110100_0
private theorem bp00000000000001101000 : Branch 0 (-574139/15625 : ℚ) vp0000000000000110100 := by
  apply branch_left_normalized (c:=vp00000000000001101000) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-574139/15625 : ℚ) - ((0:ℤ):ℚ) = (-1148278/15625 : ℚ) by norm_num]
  exact coverp00000000000001101000
private noncomputable def ep00000000000001101001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101001-E-0000.bin"
noncomputable def ep00000000000001101001 : Blocks := ep00000000000001101001_0
private theorem idp00000000000001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110100.list =
    C ((2:ℤ)^35) * horner X vp00000000000001101001.list + horner X ep00000000000001101001.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001101001 : Branch 1 (-574139/15625 : ℚ) vp0000000000000110100 := by
  apply branch_checked idp00000000000001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-574139/15625 : ℚ) - ((1:ℤ):ℚ) = (-1163903/15625 : ℚ) by norm_num]
  exact coverp00000000000001101001
theorem coverp0000000000000110100 : Covers (-574139/15625 : ℚ) vp0000000000000110100 := join_branches bp00000000000001101000 bp00000000000001101001
private noncomputable def vp000000000000011010_0 : Blocks := edgeBlocks% "full/vectors/000000000000011010-V-0000.bin"
noncomputable def vp000000000000011010 : Blocks := vp000000000000011010_0
private theorem bp0000000000000110100 : Branch 0 (-574139/31250 : ℚ) vp000000000000011010 := by
  apply branch_left_normalized (c:=vp0000000000000110100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-574139/31250 : ℚ) - ((0:ℤ):ℚ) = (-574139/15625 : ℚ) by norm_num]
  exact coverp0000000000000110100
private noncomputable def ep0000000000000110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110101-E-0000.bin"
noncomputable def ep0000000000000110101 : Blocks := ep0000000000000110101_0
private theorem idp0000000000000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011010.list =
    C ((2:ℤ)^54) * horner X vp0000000000000110101.list + horner X ep0000000000000110101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110101 : Branch 1 (-574139/31250 : ℚ) vp000000000000011010 := by
  apply branch_checked idp0000000000000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-574139/31250 : ℚ) - ((1:ℤ):ℚ) = (-589764/15625 : ℚ) by norm_num]
  exact coverp0000000000000110101
theorem coverp000000000000011010 : Covers (-574139/31250 : ℚ) vp000000000000011010 := join_branches bp0000000000000110100 bp0000000000000110101
private noncomputable def vp00000000000001101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101-V-0000.bin"
noncomputable def vp00000000000001101 : Blocks := vp00000000000001101_0
private theorem bp000000000000011010 : Branch 0 (-574139/62500 : ℚ) vp00000000000001101 := by
  apply branch_left_normalized (c:=vp000000000000011010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-574139/62500 : ℚ) - ((0:ℤ):ℚ) = (-574139/31250 : ℚ) by norm_num]
  exact coverp000000000000011010
private noncomputable def ep000000000000011011_0 : Blocks := edgeBlocks% "full/vectors/000000000000011011-E-0000.bin"
noncomputable def ep000000000000011011 : Blocks := ep000000000000011011_0
private theorem idp000000000000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001101.list =
    C ((2:ℤ)^90) * horner X vp000000000000011011.list + horner X ep000000000000011011.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011011 : Branch 1 (-574139/62500 : ℚ) vp00000000000001101 := by
  apply branch_checked idp000000000000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-574139/62500 : ℚ) - ((1:ℤ):ℚ) = (-605389/31250 : ℚ) by norm_num]
  exact coverp000000000000011011
theorem coverp00000000000001101 : Covers (-574139/62500 : ℚ) vp00000000000001101 := join_branches bp000000000000011010 bp000000000000011011
private noncomputable def vp000000000000011001111_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001111-V-0000.bin"
noncomputable def vp000000000000011001111 : Blocks := vp000000000000011001111_0
theorem coverp000000000000011001111 : Covers (-2280931/15625 : ℚ) vp000000000000011001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001100111011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100111011-V-0000.bin"
noncomputable def vp00000000000001100111011 : Blocks := vp00000000000001100111011_0
theorem coverp00000000000001100111011 : Covers (-9108099/15625 : ℚ) vp00000000000001100111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001100111010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100111010-V-0000.bin"
noncomputable def vp00000000000001100111010 : Blocks := vp00000000000001100111010_0
theorem coverp00000000000001100111010 : Covers (-9092474/15625 : ℚ) vp00000000000001100111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000110011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110011101-V-0000.bin"
noncomputable def vp0000000000000110011101 : Blocks := vp0000000000000110011101_0
private theorem bp00000000000001100111010 : Branch 0 (-4546237/15625 : ℚ) vp0000000000000110011101 := by
  apply branch_left_normalized (c:=vp00000000000001100111010) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-4546237/15625 : ℚ) - ((0:ℤ):ℚ) = (-9092474/15625 : ℚ) by norm_num]
  exact coverp00000000000001100111010
private noncomputable def ep00000000000001100111011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100111011-E-0000.bin"
noncomputable def ep00000000000001100111011 : Blocks := ep00000000000001100111011_0
private theorem idp00000000000001100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110011101.list =
    C ((2:ℤ)^16) * horner X vp00000000000001100111011.list + horner X ep00000000000001100111011.list := by
  exact edge_identity (B := (2:ℤ)^110) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001100111011 : Branch 1 (-4546237/15625 : ℚ) vp0000000000000110011101 := by
  apply branch_checked idp00000000000001100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-4546237/15625 : ℚ) - ((1:ℤ):ℚ) = (-9108099/15625 : ℚ) by norm_num]
  exact coverp00000000000001100111011
theorem coverp0000000000000110011101 : Covers (-4546237/15625 : ℚ) vp0000000000000110011101 := join_branches bp00000000000001100111010 bp00000000000001100111011
private noncomputable def vp0000000000000110011100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110011100-V-0000.bin"
noncomputable def vp0000000000000110011100 : Blocks := vp0000000000000110011100_0
theorem coverp0000000000000110011100 : Covers (-4530612/15625 : ℚ) vp0000000000000110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011001110_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001110-V-0000.bin"
noncomputable def vp000000000000011001110 : Blocks := vp000000000000011001110_0
private theorem bp0000000000000110011100 : Branch 0 (-2265306/15625 : ℚ) vp000000000000011001110 := by
  apply branch_left_normalized (c:=vp0000000000000110011100) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-2265306/15625 : ℚ) - ((0:ℤ):ℚ) = (-4530612/15625 : ℚ) by norm_num]
  exact coverp0000000000000110011100
private noncomputable def ep0000000000000110011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110011101-E-0000.bin"
noncomputable def ep0000000000000110011101 : Blocks := ep0000000000000110011101_0
private theorem idp0000000000000110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011001110.list =
    C ((2:ℤ)^19) * horner X vp0000000000000110011101.list + horner X ep0000000000000110011101.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110011101 : Branch 1 (-2265306/15625 : ℚ) vp000000000000011001110 := by
  apply branch_checked idp0000000000000110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-2265306/15625 : ℚ) - ((1:ℤ):ℚ) = (-4546237/15625 : ℚ) by norm_num]
  exact coverp0000000000000110011101
theorem coverp000000000000011001110 : Covers (-2265306/15625 : ℚ) vp000000000000011001110 := join_branches bp0000000000000110011100 bp0000000000000110011101
private noncomputable def vp00000000000001100111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100111-V-0000.bin"
noncomputable def vp00000000000001100111 : Blocks := vp00000000000001100111_0
private theorem bp000000000000011001110 : Branch 0 (-1132653/15625 : ℚ) vp00000000000001100111 := by
  apply branch_left_normalized (c:=vp000000000000011001110) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-1132653/15625 : ℚ) - ((0:ℤ):ℚ) = (-2265306/15625 : ℚ) by norm_num]
  exact coverp000000000000011001110
private noncomputable def ep000000000000011001111_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001111-E-0000.bin"
noncomputable def ep000000000000011001111 : Blocks := ep000000000000011001111_0
private theorem idp000000000000011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001100111.list =
    C ((2:ℤ)^25) * horner X vp000000000000011001111.list + horner X ep000000000000011001111.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011001111 : Branch 1 (-1132653/15625 : ℚ) vp00000000000001100111 := by
  apply branch_checked idp000000000000011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1132653/15625 : ℚ) - ((1:ℤ):ℚ) = (-2280931/15625 : ℚ) by norm_num]
  exact coverp000000000000011001111
theorem coverp00000000000001100111 : Covers (-1132653/15625 : ℚ) vp00000000000001100111 := join_branches bp000000000000011001110 bp000000000000011001111
private noncomputable def vp000000000000011001101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001101-V-0000.bin"
noncomputable def vp000000000000011001101 : Blocks := vp000000000000011001101_0
theorem coverp000000000000011001101 : Covers (-2249681/15625 : ℚ) vp000000000000011001101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011001100_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001100-V-0000.bin"
noncomputable def vp000000000000011001100 : Blocks := vp000000000000011001100_0
theorem coverp000000000000011001100 : Covers (-2234056/15625 : ℚ) vp000000000000011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001100110_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100110-V-0000.bin"
noncomputable def vp00000000000001100110 : Blocks := vp00000000000001100110_0
private theorem bp000000000000011001100 : Branch 0 (-1117028/15625 : ℚ) vp00000000000001100110 := by
  apply branch_left_normalized (c:=vp000000000000011001100) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-1117028/15625 : ℚ) - ((0:ℤ):ℚ) = (-2234056/15625 : ℚ) by norm_num]
  exact coverp000000000000011001100
private noncomputable def ep000000000000011001101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001101-E-0000.bin"
noncomputable def ep000000000000011001101 : Blocks := ep000000000000011001101_0
private theorem idp000000000000011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001100110.list =
    C ((2:ℤ)^25) * horner X vp000000000000011001101.list + horner X ep000000000000011001101.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011001101 : Branch 1 (-1117028/15625 : ℚ) vp00000000000001100110 := by
  apply branch_checked idp000000000000011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1117028/15625 : ℚ) - ((1:ℤ):ℚ) = (-2249681/15625 : ℚ) by norm_num]
  exact coverp000000000000011001101
theorem coverp00000000000001100110 : Covers (-1117028/15625 : ℚ) vp00000000000001100110 := join_branches bp000000000000011001100 bp000000000000011001101
private noncomputable def vp0000000000000110011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110011-V-0000.bin"
noncomputable def vp0000000000000110011 : Blocks := vp0000000000000110011_0
private theorem bp00000000000001100110 : Branch 0 (-558514/15625 : ℚ) vp0000000000000110011 := by
  apply branch_left_normalized (c:=vp00000000000001100110) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-558514/15625 : ℚ) - ((0:ℤ):ℚ) = (-1117028/15625 : ℚ) by norm_num]
  exact coverp00000000000001100110
private noncomputable def ep00000000000001100111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100111-E-0000.bin"
noncomputable def ep00000000000001100111 : Blocks := ep00000000000001100111_0
private theorem idp00000000000001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110011.list =
    C ((2:ℤ)^36) * horner X vp00000000000001100111.list + horner X ep00000000000001100111.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001100111 : Branch 1 (-558514/15625 : ℚ) vp0000000000000110011 := by
  apply branch_checked idp00000000000001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-558514/15625 : ℚ) - ((1:ℤ):ℚ) = (-1132653/15625 : ℚ) by norm_num]
  exact coverp00000000000001100111
theorem coverp0000000000000110011 : Covers (-558514/15625 : ℚ) vp0000000000000110011 := join_branches bp00000000000001100110 bp00000000000001100111
private noncomputable def vp000000000000011001011_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001011-V-0000.bin"
noncomputable def vp000000000000011001011 : Blocks := vp000000000000011001011_0
theorem coverp000000000000011001011 : Covers (-2218431/15625 : ℚ) vp000000000000011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000110010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110010101-V-0000.bin"
noncomputable def vp0000000000000110010101 : Blocks := vp0000000000000110010101_0
theorem coverp0000000000000110010101 : Covers (-4421237/15625 : ℚ) vp0000000000000110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001100101001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100101001-V-0000.bin"
noncomputable def vp00000000000001100101001 : Blocks := vp00000000000001100101001_0
theorem coverp00000000000001100101001 : Covers (-8826849/15625 : ℚ) vp00000000000001100101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001100101000_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100101000-V-0000.bin"
noncomputable def vp00000000000001100101000 : Blocks := vp00000000000001100101000_0
theorem coverp00000000000001100101000 : Covers (-8811224/15625 : ℚ) vp00000000000001100101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000110010100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110010100-V-0000.bin"
noncomputable def vp0000000000000110010100 : Blocks := vp0000000000000110010100_0
private theorem bp00000000000001100101000 : Branch 0 (-4405612/15625 : ℚ) vp0000000000000110010100 := by
  apply branch_left_normalized (c:=vp00000000000001100101000) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-4405612/15625 : ℚ) - ((0:ℤ):ℚ) = (-8811224/15625 : ℚ) by norm_num]
  exact coverp00000000000001100101000
private noncomputable def ep00000000000001100101001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100101001-E-0000.bin"
noncomputable def ep00000000000001100101001 : Blocks := ep00000000000001100101001_0
private theorem idp00000000000001100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110010100.list =
    C ((2:ℤ)^15) * horner X vp00000000000001100101001.list + horner X ep00000000000001100101001.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001100101001 : Branch 1 (-4405612/15625 : ℚ) vp0000000000000110010100 := by
  apply branch_checked idp00000000000001100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-4405612/15625 : ℚ) - ((1:ℤ):ℚ) = (-8826849/15625 : ℚ) by norm_num]
  exact coverp00000000000001100101001
theorem coverp0000000000000110010100 : Covers (-4405612/15625 : ℚ) vp0000000000000110010100 := join_branches bp00000000000001100101000 bp00000000000001100101001
private noncomputable def vp000000000000011001010_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001010-V-0000.bin"
noncomputable def vp000000000000011001010 : Blocks := vp000000000000011001010_0
private theorem bp0000000000000110010100 : Branch 0 (-2202806/15625 : ℚ) vp000000000000011001010 := by
  apply branch_left_normalized (c:=vp0000000000000110010100) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-2202806/15625 : ℚ) - ((0:ℤ):ℚ) = (-4405612/15625 : ℚ) by norm_num]
  exact coverp0000000000000110010100
private noncomputable def ep0000000000000110010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110010101-E-0000.bin"
noncomputable def ep0000000000000110010101 : Blocks := ep0000000000000110010101_0
private theorem idp0000000000000110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011001010.list =
    C ((2:ℤ)^19) * horner X vp0000000000000110010101.list + horner X ep0000000000000110010101.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110010101 : Branch 1 (-2202806/15625 : ℚ) vp000000000000011001010 := by
  apply branch_checked idp0000000000000110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2202806/15625 : ℚ) - ((1:ℤ):ℚ) = (-4421237/15625 : ℚ) by norm_num]
  exact coverp0000000000000110010101
theorem coverp000000000000011001010 : Covers (-2202806/15625 : ℚ) vp000000000000011001010 := join_branches bp0000000000000110010100 bp0000000000000110010101
private noncomputable def vp00000000000001100101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100101-V-0000.bin"
noncomputable def vp00000000000001100101 : Blocks := vp00000000000001100101_0
private theorem bp000000000000011001010 : Branch 0 (-1101403/15625 : ℚ) vp00000000000001100101 := by
  apply branch_left_normalized (c:=vp000000000000011001010) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-1101403/15625 : ℚ) - ((0:ℤ):ℚ) = (-2202806/15625 : ℚ) by norm_num]
  exact coverp000000000000011001010
private noncomputable def ep000000000000011001011_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001011-E-0000.bin"
noncomputable def ep000000000000011001011 : Blocks := ep000000000000011001011_0
private theorem idp000000000000011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001100101.list =
    C ((2:ℤ)^26) * horner X vp000000000000011001011.list + horner X ep000000000000011001011.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011001011 : Branch 1 (-1101403/15625 : ℚ) vp00000000000001100101 := by
  apply branch_checked idp000000000000011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1101403/15625 : ℚ) - ((1:ℤ):ℚ) = (-2218431/15625 : ℚ) by norm_num]
  exact coverp000000000000011001011
theorem coverp00000000000001100101 : Covers (-1101403/15625 : ℚ) vp00000000000001100101 := join_branches bp000000000000011001010 bp000000000000011001011
private noncomputable def vp0000000000000110010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110010011-V-0000.bin"
noncomputable def vp0000000000000110010011 : Blocks := vp0000000000000110010011_0
theorem coverp0000000000000110010011 : Covers (-4389987/15625 : ℚ) vp0000000000000110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000110010010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110010010-V-0000.bin"
noncomputable def vp0000000000000110010010 : Blocks := vp0000000000000110010010_0
theorem coverp0000000000000110010010 : Covers (-4374362/15625 : ℚ) vp0000000000000110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011001001_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001001-V-0000.bin"
noncomputable def vp000000000000011001001 : Blocks := vp000000000000011001001_0
private theorem bp0000000000000110010010 : Branch 0 (-2187181/15625 : ℚ) vp000000000000011001001 := by
  apply branch_left_normalized (c:=vp0000000000000110010010) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-2187181/15625 : ℚ) - ((0:ℤ):ℚ) = (-4374362/15625 : ℚ) by norm_num]
  exact coverp0000000000000110010010
private noncomputable def ep0000000000000110010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110010011-E-0000.bin"
noncomputable def ep0000000000000110010011 : Blocks := ep0000000000000110010011_0
private theorem idp0000000000000110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011001001.list =
    C ((2:ℤ)^19) * horner X vp0000000000000110010011.list + horner X ep0000000000000110010011.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110010011 : Branch 1 (-2187181/15625 : ℚ) vp000000000000011001001 := by
  apply branch_checked idp0000000000000110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-2187181/15625 : ℚ) - ((1:ℤ):ℚ) = (-4389987/15625 : ℚ) by norm_num]
  exact coverp0000000000000110010011
theorem coverp000000000000011001001 : Covers (-2187181/15625 : ℚ) vp000000000000011001001 := join_branches bp0000000000000110010010 bp0000000000000110010011
private noncomputable def vp000000000000011001000_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001000-V-0000.bin"
noncomputable def vp000000000000011001000 : Blocks := vp000000000000011001000_0
theorem coverp000000000000011001000 : Covers (-2171556/15625 : ℚ) vp000000000000011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001100100_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100100-V-0000.bin"
noncomputable def vp00000000000001100100 : Blocks := vp00000000000001100100_0
private theorem bp000000000000011001000 : Branch 0 (-1085778/15625 : ℚ) vp00000000000001100100 := by
  apply branch_left_normalized (c:=vp000000000000011001000) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-1085778/15625 : ℚ) - ((0:ℤ):ℚ) = (-2171556/15625 : ℚ) by norm_num]
  exact coverp000000000000011001000
private noncomputable def ep000000000000011001001_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001001-E-0000.bin"
noncomputable def ep000000000000011001001 : Blocks := ep000000000000011001001_0
private theorem idp000000000000011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001100100.list =
    C ((2:ℤ)^24) * horner X vp000000000000011001001.list + horner X ep000000000000011001001.list := by
  exact edge_identity (B := (2:ℤ)^121) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011001001 : Branch 1 (-1085778/15625 : ℚ) vp00000000000001100100 := by
  apply branch_checked idp000000000000011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1085778/15625 : ℚ) - ((1:ℤ):ℚ) = (-2187181/15625 : ℚ) by norm_num]
  exact coverp000000000000011001001
theorem coverp00000000000001100100 : Covers (-1085778/15625 : ℚ) vp00000000000001100100 := join_branches bp000000000000011001000 bp000000000000011001001
private noncomputable def vp0000000000000110010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110010-V-0000.bin"
noncomputable def vp0000000000000110010 : Blocks := vp0000000000000110010_0
private theorem bp00000000000001100100 : Branch 0 (-542889/15625 : ℚ) vp0000000000000110010 := by
  apply branch_left_normalized (c:=vp00000000000001100100) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-542889/15625 : ℚ) - ((0:ℤ):ℚ) = (-1085778/15625 : ℚ) by norm_num]
  exact coverp00000000000001100100
private noncomputable def ep00000000000001100101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100101-E-0000.bin"
noncomputable def ep00000000000001100101 : Blocks := ep00000000000001100101_0
private theorem idp00000000000001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110010.list =
    C ((2:ℤ)^36) * horner X vp00000000000001100101.list + horner X ep00000000000001100101.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001100101 : Branch 1 (-542889/15625 : ℚ) vp0000000000000110010 := by
  apply branch_checked idp00000000000001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-542889/15625 : ℚ) - ((1:ℤ):ℚ) = (-1101403/15625 : ℚ) by norm_num]
  exact coverp00000000000001100101
theorem coverp0000000000000110010 : Covers (-542889/15625 : ℚ) vp0000000000000110010 := join_branches bp00000000000001100100 bp00000000000001100101
private noncomputable def vp000000000000011001_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001-V-0000.bin"
noncomputable def vp000000000000011001 : Blocks := vp000000000000011001_0
private theorem bp0000000000000110010 : Branch 0 (-542889/31250 : ℚ) vp000000000000011001 := by
  apply branch_left_normalized (c:=vp0000000000000110010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-542889/31250 : ℚ) - ((0:ℤ):ℚ) = (-542889/15625 : ℚ) by norm_num]
  exact coverp0000000000000110010
private noncomputable def ep0000000000000110011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110011-E-0000.bin"
noncomputable def ep0000000000000110011 : Blocks := ep0000000000000110011_0
private theorem idp0000000000000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011001.list =
    C ((2:ℤ)^55) * horner X vp0000000000000110011.list + horner X ep0000000000000110011.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110011 : Branch 1 (-542889/31250 : ℚ) vp000000000000011001 := by
  apply branch_checked idp0000000000000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-542889/31250 : ℚ) - ((1:ℤ):ℚ) = (-558514/15625 : ℚ) by norm_num]
  exact coverp0000000000000110011
theorem coverp000000000000011001 : Covers (-542889/31250 : ℚ) vp000000000000011001 := join_branches bp0000000000000110010 bp0000000000000110011
private noncomputable def vp00000000000001100011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100011-V-0000.bin"
noncomputable def vp00000000000001100011 : Blocks := vp00000000000001100011_0
theorem coverp00000000000001100011 : Covers (-1070153/15625 : ℚ) vp00000000000001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000110001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110001011-V-0000.bin"
noncomputable def vp0000000000000110001011 : Blocks := vp0000000000000110001011_0
theorem coverp0000000000000110001011 : Covers (-4264987/15625 : ℚ) vp0000000000000110001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001100010101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100010101-V-0000.bin"
noncomputable def vp00000000000001100010101 : Blocks := vp00000000000001100010101_0
theorem coverp00000000000001100010101 : Covers (-8514349/15625 : ℚ) vp00000000000001100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001100010100_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100010100-V-0000.bin"
noncomputable def vp00000000000001100010100 : Blocks := vp00000000000001100010100_0
theorem coverp00000000000001100010100 : Covers (-8498724/15625 : ℚ) vp00000000000001100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000110001010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110001010-V-0000.bin"
noncomputable def vp0000000000000110001010 : Blocks := vp0000000000000110001010_0
private theorem bp00000000000001100010100 : Branch 0 (-4249362/15625 : ℚ) vp0000000000000110001010 := by
  apply branch_left_normalized (c:=vp00000000000001100010100) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-4249362/15625 : ℚ) - ((0:ℤ):ℚ) = (-8498724/15625 : ℚ) by norm_num]
  exact coverp00000000000001100010100
private noncomputable def ep00000000000001100010101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100010101-E-0000.bin"
noncomputable def ep00000000000001100010101 : Blocks := ep00000000000001100010101_0
private theorem idp00000000000001100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110001010.list =
    C ((2:ℤ)^15) * horner X vp00000000000001100010101.list + horner X ep00000000000001100010101.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001100010101 : Branch 1 (-4249362/15625 : ℚ) vp0000000000000110001010 := by
  apply branch_checked idp00000000000001100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4249362/15625 : ℚ) - ((1:ℤ):ℚ) = (-8514349/15625 : ℚ) by norm_num]
  exact coverp00000000000001100010101
theorem coverp0000000000000110001010 : Covers (-4249362/15625 : ℚ) vp0000000000000110001010 := join_branches bp00000000000001100010100 bp00000000000001100010101
private noncomputable def vp000000000000011000101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011000101-V-0000.bin"
noncomputable def vp000000000000011000101 : Blocks := vp000000000000011000101_0
private theorem bp0000000000000110001010 : Branch 0 (-2124681/15625 : ℚ) vp000000000000011000101 := by
  apply branch_left_normalized (c:=vp0000000000000110001010) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-2124681/15625 : ℚ) - ((0:ℤ):ℚ) = (-4249362/15625 : ℚ) by norm_num]
  exact coverp0000000000000110001010
private noncomputable def ep0000000000000110001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110001011-E-0000.bin"
noncomputable def ep0000000000000110001011 : Blocks := ep0000000000000110001011_0
private theorem idp0000000000000110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011000101.list =
    C ((2:ℤ)^19) * horner X vp0000000000000110001011.list + horner X ep0000000000000110001011.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110001011 : Branch 1 (-2124681/15625 : ℚ) vp000000000000011000101 := by
  apply branch_checked idp0000000000000110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-2124681/15625 : ℚ) - ((1:ℤ):ℚ) = (-4264987/15625 : ℚ) by norm_num]
  exact coverp0000000000000110001011
theorem coverp000000000000011000101 : Covers (-2124681/15625 : ℚ) vp000000000000011000101 := join_branches bp0000000000000110001010 bp0000000000000110001011
private noncomputable def vp0000000000000110001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110001001-V-0000.bin"
noncomputable def vp0000000000000110001001 : Blocks := vp0000000000000110001001_0
theorem coverp0000000000000110001001 : Covers (-4233737/15625 : ℚ) vp0000000000000110001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000110001000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110001000-V-0000.bin"
noncomputable def vp0000000000000110001000 : Blocks := vp0000000000000110001000_0
theorem coverp0000000000000110001000 : Covers (-4218112/15625 : ℚ) vp0000000000000110001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011000100_0 : Blocks := edgeBlocks% "full/vectors/000000000000011000100-V-0000.bin"
noncomputable def vp000000000000011000100 : Blocks := vp000000000000011000100_0
private theorem bp0000000000000110001000 : Branch 0 (-2109056/15625 : ℚ) vp000000000000011000100 := by
  apply branch_left_normalized (c:=vp0000000000000110001000) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-2109056/15625 : ℚ) - ((0:ℤ):ℚ) = (-4218112/15625 : ℚ) by norm_num]
  exact coverp0000000000000110001000
private noncomputable def ep0000000000000110001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110001001-E-0000.bin"
noncomputable def ep0000000000000110001001 : Blocks := ep0000000000000110001001_0
private theorem idp0000000000000110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011000100.list =
    C ((2:ℤ)^19) * horner X vp0000000000000110001001.list + horner X ep0000000000000110001001.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110001001 : Branch 1 (-2109056/15625 : ℚ) vp000000000000011000100 := by
  apply branch_checked idp0000000000000110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-2109056/15625 : ℚ) - ((1:ℤ):ℚ) = (-4233737/15625 : ℚ) by norm_num]
  exact coverp0000000000000110001001
theorem coverp000000000000011000100 : Covers (-2109056/15625 : ℚ) vp000000000000011000100 := join_branches bp0000000000000110001000 bp0000000000000110001001
private noncomputable def vp00000000000001100010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100010-V-0000.bin"
noncomputable def vp00000000000001100010 : Blocks := vp00000000000001100010_0
private theorem bp000000000000011000100 : Branch 0 (-1054528/15625 : ℚ) vp00000000000001100010 := by
  apply branch_left_normalized (c:=vp000000000000011000100) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-1054528/15625 : ℚ) - ((0:ℤ):ℚ) = (-2109056/15625 : ℚ) by norm_num]
  exact coverp000000000000011000100
private noncomputable def ep000000000000011000101_0 : Blocks := edgeBlocks% "full/vectors/000000000000011000101-E-0000.bin"
noncomputable def ep000000000000011000101 : Blocks := ep000000000000011000101_0
private theorem idp000000000000011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001100010.list =
    C ((2:ℤ)^25) * horner X vp000000000000011000101.list + horner X ep000000000000011000101.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011000101 : Branch 1 (-1054528/15625 : ℚ) vp00000000000001100010 := by
  apply branch_checked idp000000000000011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1054528/15625 : ℚ) - ((1:ℤ):ℚ) = (-2124681/15625 : ℚ) by norm_num]
  exact coverp000000000000011000101
theorem coverp00000000000001100010 : Covers (-1054528/15625 : ℚ) vp00000000000001100010 := join_branches bp000000000000011000100 bp000000000000011000101
private noncomputable def vp0000000000000110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110001-V-0000.bin"
noncomputable def vp0000000000000110001 : Blocks := vp0000000000000110001_0
private theorem bp00000000000001100010 : Branch 0 (-527264/15625 : ℚ) vp0000000000000110001 := by
  apply branch_left_normalized (c:=vp00000000000001100010) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-527264/15625 : ℚ) - ((0:ℤ):ℚ) = (-1054528/15625 : ℚ) by norm_num]
  exact coverp00000000000001100010
private noncomputable def ep00000000000001100011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100011-E-0000.bin"
noncomputable def ep00000000000001100011 : Blocks := ep00000000000001100011_0
private theorem idp00000000000001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110001.list =
    C ((2:ℤ)^36) * horner X vp00000000000001100011.list + horner X ep00000000000001100011.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001100011 : Branch 1 (-527264/15625 : ℚ) vp0000000000000110001 := by
  apply branch_checked idp00000000000001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-527264/15625 : ℚ) - ((1:ℤ):ℚ) = (-1070153/15625 : ℚ) by norm_num]
  exact coverp00000000000001100011
theorem coverp0000000000000110001 : Covers (-527264/15625 : ℚ) vp0000000000000110001 := join_branches bp00000000000001100010 bp00000000000001100011
private noncomputable def vp00000000000001100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100001-V-0000.bin"
noncomputable def vp00000000000001100001 : Blocks := vp00000000000001100001_0
theorem coverp00000000000001100001 : Covers (-1038903/15625 : ℚ) vp00000000000001100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011000001_0 : Blocks := edgeBlocks% "full/vectors/000000000000011000001-V-0000.bin"
noncomputable def vp000000000000011000001 : Blocks := vp000000000000011000001_0
theorem coverp000000000000011000001 : Covers (-2062181/15625 : ℚ) vp000000000000011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001100000011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100000011-V-0000.bin"
noncomputable def vp00000000000001100000011 : Blocks := vp00000000000001100000011_0
theorem coverp00000000000001100000011 : Covers (-8233099/15625 : ℚ) vp00000000000001100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001100000010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100000010-V-0000.bin"
noncomputable def vp00000000000001100000010 : Blocks := vp00000000000001100000010_0
theorem coverp00000000000001100000010 : Covers (-8217474/15625 : ℚ) vp00000000000001100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000110000001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110000001-V-0000.bin"
noncomputable def vp0000000000000110000001 : Blocks := vp0000000000000110000001_0
private theorem bp00000000000001100000010 : Branch 0 (-4108737/15625 : ℚ) vp0000000000000110000001 := by
  apply branch_left_normalized (c:=vp00000000000001100000010) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-4108737/15625 : ℚ) - ((0:ℤ):ℚ) = (-8217474/15625 : ℚ) by norm_num]
  exact coverp00000000000001100000010
private noncomputable def ep00000000000001100000011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100000011-E-0000.bin"
noncomputable def ep00000000000001100000011 : Blocks := ep00000000000001100000011_0
private theorem idp00000000000001100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110000001.list =
    C ((2:ℤ)^15) * horner X vp00000000000001100000011.list + horner X ep00000000000001100000011.list := by
  exact edge_identity (B := (2:ℤ)^108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001100000011 : Branch 1 (-4108737/15625 : ℚ) vp0000000000000110000001 := by
  apply branch_checked idp00000000000001100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-4108737/15625 : ℚ) - ((1:ℤ):ℚ) = (-8233099/15625 : ℚ) by norm_num]
  exact coverp00000000000001100000011
theorem coverp0000000000000110000001 : Covers (-4108737/15625 : ℚ) vp0000000000000110000001 := join_branches bp00000000000001100000010 bp00000000000001100000011
private noncomputable def vp0000000000000110000000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110000000-V-0000.bin"
noncomputable def vp0000000000000110000000 : Blocks := vp0000000000000110000000_0
theorem coverp0000000000000110000000 : Covers (-4093112/15625 : ℚ) vp0000000000000110000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000011000000_0 : Blocks := edgeBlocks% "full/vectors/000000000000011000000-V-0000.bin"
noncomputable def vp000000000000011000000 : Blocks := vp000000000000011000000_0
private theorem bp0000000000000110000000 : Branch 0 (-2046556/15625 : ℚ) vp000000000000011000000 := by
  apply branch_left_normalized (c:=vp0000000000000110000000) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-2046556/15625 : ℚ) - ((0:ℤ):ℚ) = (-4093112/15625 : ℚ) by norm_num]
  exact coverp0000000000000110000000
private noncomputable def ep0000000000000110000001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110000001-E-0000.bin"
noncomputable def ep0000000000000110000001 : Blocks := ep0000000000000110000001_0
private theorem idp0000000000000110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011000000.list =
    C ((2:ℤ)^19) * horner X vp0000000000000110000001.list + horner X ep0000000000000110000001.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110000001 : Branch 1 (-2046556/15625 : ℚ) vp000000000000011000000 := by
  apply branch_checked idp0000000000000110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-2046556/15625 : ℚ) - ((1:ℤ):ℚ) = (-4108737/15625 : ℚ) by norm_num]
  exact coverp0000000000000110000001
theorem coverp000000000000011000000 : Covers (-2046556/15625 : ℚ) vp000000000000011000000 := join_branches bp0000000000000110000000 bp0000000000000110000001
private noncomputable def vp00000000000001100000_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100000-V-0000.bin"
noncomputable def vp00000000000001100000 : Blocks := vp00000000000001100000_0
private theorem bp000000000000011000000 : Branch 0 (-1023278/15625 : ℚ) vp00000000000001100000 := by
  apply branch_left_normalized (c:=vp000000000000011000000) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-1023278/15625 : ℚ) - ((0:ℤ):ℚ) = (-2046556/15625 : ℚ) by norm_num]
  exact coverp000000000000011000000
private noncomputable def ep000000000000011000001_0 : Blocks := edgeBlocks% "full/vectors/000000000000011000001-E-0000.bin"
noncomputable def ep000000000000011000001 : Blocks := ep000000000000011000001_0
private theorem idp000000000000011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001100000.list =
    C ((2:ℤ)^25) * horner X vp000000000000011000001.list + horner X ep000000000000011000001.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011000001 : Branch 1 (-1023278/15625 : ℚ) vp00000000000001100000 := by
  apply branch_checked idp000000000000011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1023278/15625 : ℚ) - ((1:ℤ):ℚ) = (-2062181/15625 : ℚ) by norm_num]
  exact coverp000000000000011000001
theorem coverp00000000000001100000 : Covers (-1023278/15625 : ℚ) vp00000000000001100000 := join_branches bp000000000000011000000 bp000000000000011000001
private noncomputable def vp0000000000000110000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110000-V-0000.bin"
noncomputable def vp0000000000000110000 : Blocks := vp0000000000000110000_0
private theorem bp00000000000001100000 : Branch 0 (-511639/15625 : ℚ) vp0000000000000110000 := by
  apply branch_left_normalized (c:=vp00000000000001100000) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-511639/15625 : ℚ) - ((0:ℤ):ℚ) = (-1023278/15625 : ℚ) by norm_num]
  exact coverp00000000000001100000
private noncomputable def ep00000000000001100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100001-E-0000.bin"
noncomputable def ep00000000000001100001 : Blocks := ep00000000000001100001_0
private theorem idp00000000000001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110000.list =
    C ((2:ℤ)^37) * horner X vp00000000000001100001.list + horner X ep00000000000001100001.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001100001 : Branch 1 (-511639/15625 : ℚ) vp0000000000000110000 := by
  apply branch_checked idp00000000000001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-511639/15625 : ℚ) - ((1:ℤ):ℚ) = (-1038903/15625 : ℚ) by norm_num]
  exact coverp00000000000001100001
theorem coverp0000000000000110000 : Covers (-511639/15625 : ℚ) vp0000000000000110000 := join_branches bp00000000000001100000 bp00000000000001100001
private noncomputable def vp000000000000011000_0 : Blocks := edgeBlocks% "full/vectors/000000000000011000-V-0000.bin"
noncomputable def vp000000000000011000 : Blocks := vp000000000000011000_0
private theorem bp0000000000000110000 : Branch 0 (-511639/31250 : ℚ) vp000000000000011000 := by
  apply branch_left_normalized (c:=vp0000000000000110000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-511639/31250 : ℚ) - ((0:ℤ):ℚ) = (-511639/15625 : ℚ) by norm_num]
  exact coverp0000000000000110000
private noncomputable def ep0000000000000110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110001-E-0000.bin"
noncomputable def ep0000000000000110001 : Blocks := ep0000000000000110001_0
private theorem idp0000000000000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011000.list =
    C ((2:ℤ)^57) * horner X vp0000000000000110001.list + horner X ep0000000000000110001.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000110001 : Branch 1 (-511639/31250 : ℚ) vp000000000000011000 := by
  apply branch_checked idp0000000000000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-511639/31250 : ℚ) - ((1:ℤ):ℚ) = (-527264/15625 : ℚ) by norm_num]
  exact coverp0000000000000110001
theorem coverp000000000000011000 : Covers (-511639/31250 : ℚ) vp000000000000011000 := join_branches bp0000000000000110000 bp0000000000000110001
private noncomputable def vp00000000000001100_0 : Blocks := edgeBlocks% "full/vectors/00000000000001100-V-0000.bin"
noncomputable def vp00000000000001100 : Blocks := vp00000000000001100_0
private theorem bp000000000000011000 : Branch 0 (-511639/62500 : ℚ) vp00000000000001100 := by
  apply branch_left_normalized (c:=vp000000000000011000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-511639/62500 : ℚ) - ((0:ℤ):ℚ) = (-511639/31250 : ℚ) by norm_num]
  exact coverp000000000000011000
private noncomputable def ep000000000000011001_0 : Blocks := edgeBlocks% "full/vectors/000000000000011001-E-0000.bin"
noncomputable def ep000000000000011001 : Blocks := ep000000000000011001_0
private theorem idp000000000000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001100.list =
    C ((2:ℤ)^93) * horner X vp000000000000011001.list + horner X ep000000000000011001.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011001 : Branch 1 (-511639/62500 : ℚ) vp00000000000001100 := by
  apply branch_checked idp000000000000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-511639/62500 : ℚ) - ((1:ℤ):ℚ) = (-542889/31250 : ℚ) by norm_num]
  exact coverp000000000000011001
theorem coverp00000000000001100 : Covers (-511639/62500 : ℚ) vp00000000000001100 := join_branches bp000000000000011000 bp000000000000011001
private noncomputable def vp0000000000000110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000110-V-0000.bin"
private noncomputable def vp0000000000000110_1 : Blocks := edgeBlocks% "full/vectors/0000000000000110-V-0001.bin"
noncomputable def vp0000000000000110 : Blocks := (Blocks.join vp0000000000000110_0 vp0000000000000110_1)
private theorem bp00000000000001100 : Branch 0 (-511639/125000 : ℚ) vp0000000000000110 := by
  apply branch_left_normalized (c:=vp00000000000001100) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-511639/62500 : ℚ) by norm_num]
  exact coverp00000000000001100
private noncomputable def ep00000000000001101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001101-E-0000.bin"
private noncomputable def ep00000000000001101_1 : Blocks := edgeBlocks% "full/vectors/00000000000001101-E-0001.bin"
noncomputable def ep00000000000001101 : Blocks := (Blocks.join ep00000000000001101_0 ep00000000000001101_1)
private theorem idp00000000000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000110.list =
    C ((2:ℤ)^166) * horner X vp00000000000001101.list + horner X ep00000000000001101.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001101 : Branch 1 (-511639/125000 : ℚ) vp0000000000000110 := by
  apply branch_checked idp00000000000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-574139/62500 : ℚ) by norm_num]
  exact coverp00000000000001101
theorem coverp0000000000000110 : Covers (-511639/125000 : ℚ) vp0000000000000110 := join_branches bp00000000000001100 bp00000000000001101
private noncomputable def vp000000000000011_0 : Blocks := edgeBlocks% "full/vectors/000000000000011-V-0000.bin"
private noncomputable def vp000000000000011_1 : Blocks := edgeBlocks% "full/vectors/000000000000011-V-0001.bin"
private noncomputable def vp000000000000011_2 : Blocks := edgeBlocks% "full/vectors/000000000000011-V-0002.bin"
noncomputable def vp000000000000011 : Blocks := (Blocks.join vp000000000000011_0 (Blocks.join vp000000000000011_1 vp000000000000011_2))
private theorem bp0000000000000110 : Branch 0 (-511639/250000 : ℚ) vp000000000000011 := by
  apply branch_left_normalized (c:=vp0000000000000110) (k:=0) (m:=165) (by decide +kernel)
  rw [show 2*(-511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-511639/125000 : ℚ) by norm_num]
  exact coverp0000000000000110
private noncomputable def ep0000000000000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000111-E-0000.bin"
private noncomputable def ep0000000000000111_1 : Blocks := edgeBlocks% "full/vectors/0000000000000111-E-0001.bin"
private noncomputable def ep0000000000000111_2 : Blocks := edgeBlocks% "full/vectors/0000000000000111-E-0002.bin"
noncomputable def ep0000000000000111 : Blocks := (Blocks.join ep0000000000000111_0 (Blocks.join ep0000000000000111_1 ep0000000000000111_2))
private theorem idp0000000000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000011.list =
    C ((2:ℤ)^308) * horner X vp0000000000000111.list + horner X ep0000000000000111.list := by
  exact edge_identity (B := (2:ℤ)^544) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000111 : Branch 1 (-511639/250000 : ℚ) vp000000000000011 := by
  apply branch_checked idp0000000000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-636639/125000 : ℚ) by norm_num]
  exact coverp0000000000000111
theorem coverp000000000000011 : Covers (-511639/250000 : ℚ) vp000000000000011 := join_branches bp0000000000000110 bp0000000000000111
end NextProof.EdgeFull

