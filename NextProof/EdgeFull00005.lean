import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00004

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000000000000010111111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010111111-V-0000.bin"
noncomputable def vp000000000000010111111 : Blocks := vp000000000000010111111_0
theorem coverp000000000000010111111 : Covers (-2030931/15625 : ℚ) vp000000000000010111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010111110_0 : Blocks := edgeBlocks% "full/vectors/000000000000010111110-V-0000.bin"
noncomputable def vp000000000000010111110 : Blocks := vp000000000000010111110_0
theorem coverp000000000000010111110 : Covers (-2015306/15625 : ℚ) vp000000000000010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001011111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011111-V-0000.bin"
noncomputable def vp00000000000001011111 : Blocks := vp00000000000001011111_0
private theorem bp000000000000010111110 : Branch 0 (-1007653/15625 : ℚ) vp00000000000001011111 := by
  apply branch_left_normalized (c:=vp000000000000010111110) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-1007653/15625 : ℚ) - ((0:ℤ):ℚ) = (-2015306/15625 : ℚ) by norm_num]
  exact coverp000000000000010111110
private noncomputable def ep000000000000010111111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010111111-E-0000.bin"
noncomputable def ep000000000000010111111 : Blocks := ep000000000000010111111_0
private theorem idp000000000000010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001011111.list =
    C ((2:ℤ)^25) * horner X vp000000000000010111111.list + horner X ep000000000000010111111.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010111111 : Branch 1 (-1007653/15625 : ℚ) vp00000000000001011111 := by
  apply branch_checked idp000000000000010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1007653/15625 : ℚ) - ((1:ℤ):ℚ) = (-2030931/15625 : ℚ) by norm_num]
  exact coverp000000000000010111111
theorem coverp00000000000001011111 : Covers (-1007653/15625 : ℚ) vp00000000000001011111 := join_branches bp000000000000010111110 bp000000000000010111111
private noncomputable def vp00000000000001011110_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011110-V-0000.bin"
noncomputable def vp00000000000001011110 : Blocks := vp00000000000001011110_0
theorem coverp00000000000001011110 : Covers (-992028/15625 : ℚ) vp00000000000001011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101111-V-0000.bin"
noncomputable def vp0000000000000101111 : Blocks := vp0000000000000101111_0
private theorem bp00000000000001011110 : Branch 0 (-496014/15625 : ℚ) vp0000000000000101111 := by
  apply branch_left_normalized (c:=vp00000000000001011110) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-496014/15625 : ℚ) - ((0:ℤ):ℚ) = (-992028/15625 : ℚ) by norm_num]
  exact coverp00000000000001011110
private noncomputable def ep00000000000001011111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011111-E-0000.bin"
noncomputable def ep00000000000001011111 : Blocks := ep00000000000001011111_0
private theorem idp00000000000001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101111.list =
    C ((2:ℤ)^38) * horner X vp00000000000001011111.list + horner X ep00000000000001011111.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001011111 : Branch 1 (-496014/15625 : ℚ) vp0000000000000101111 := by
  apply branch_checked idp00000000000001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-496014/15625 : ℚ) - ((1:ℤ):ℚ) = (-1007653/15625 : ℚ) by norm_num]
  exact coverp00000000000001011111
theorem coverp0000000000000101111 : Covers (-496014/15625 : ℚ) vp0000000000000101111 := join_branches bp00000000000001011110 bp00000000000001011111
private noncomputable def vp00000000000001011101111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011101111-V-0000.bin"
noncomputable def vp00000000000001011101111 : Blocks := vp00000000000001011101111_0
theorem coverp00000000000001011101111 : Covers (-7920599/15625 : ℚ) vp00000000000001011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001011101110_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011101110-V-0000.bin"
noncomputable def vp00000000000001011101110 : Blocks := vp00000000000001011101110_0
theorem coverp00000000000001011101110 : Covers (-7904974/15625 : ℚ) vp00000000000001011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101110111-V-0000.bin"
noncomputable def vp0000000000000101110111 : Blocks := vp0000000000000101110111_0
private theorem bp00000000000001011101110 : Branch 0 (-3952487/15625 : ℚ) vp0000000000000101110111 := by
  apply branch_left_normalized (c:=vp00000000000001011101110) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-3952487/15625 : ℚ) - ((0:ℤ):ℚ) = (-7904974/15625 : ℚ) by norm_num]
  exact coverp00000000000001011101110
private noncomputable def ep00000000000001011101111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011101111-E-0000.bin"
noncomputable def ep00000000000001011101111 : Blocks := ep00000000000001011101111_0
private theorem idp00000000000001011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101110111.list =
    C ((2:ℤ)^16) * horner X vp00000000000001011101111.list + horner X ep00000000000001011101111.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001011101111 : Branch 1 (-3952487/15625 : ℚ) vp0000000000000101110111 := by
  apply branch_checked idp00000000000001011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-3952487/15625 : ℚ) - ((1:ℤ):ℚ) = (-7920599/15625 : ℚ) by norm_num]
  exact coverp00000000000001011101111
theorem coverp0000000000000101110111 : Covers (-3952487/15625 : ℚ) vp0000000000000101110111 := join_branches bp00000000000001011101110 bp00000000000001011101111
private noncomputable def vp0000000000000101110110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101110110-V-0000.bin"
noncomputable def vp0000000000000101110110 : Blocks := vp0000000000000101110110_0
theorem coverp0000000000000101110110 : Covers (-3936862/15625 : ℚ) vp0000000000000101110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010111011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010111011-V-0000.bin"
noncomputable def vp000000000000010111011 : Blocks := vp000000000000010111011_0
private theorem bp0000000000000101110110 : Branch 0 (-1968431/15625 : ℚ) vp000000000000010111011 := by
  apply branch_left_normalized (c:=vp0000000000000101110110) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-1968431/15625 : ℚ) - ((0:ℤ):ℚ) = (-3936862/15625 : ℚ) by norm_num]
  exact coverp0000000000000101110110
private noncomputable def ep0000000000000101110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101110111-E-0000.bin"
noncomputable def ep0000000000000101110111 : Blocks := ep0000000000000101110111_0
private theorem idp0000000000000101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010111011.list =
    C ((2:ℤ)^20) * horner X vp0000000000000101110111.list + horner X ep0000000000000101110111.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101110111 : Branch 1 (-1968431/15625 : ℚ) vp000000000000010111011 := by
  apply branch_checked idp0000000000000101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1968431/15625 : ℚ) - ((1:ℤ):ℚ) = (-3952487/15625 : ℚ) by norm_num]
  exact coverp0000000000000101110111
theorem coverp000000000000010111011 : Covers (-1968431/15625 : ℚ) vp000000000000010111011 := join_branches bp0000000000000101110110 bp0000000000000101110111
private noncomputable def vp000000000000010111010_0 : Blocks := edgeBlocks% "full/vectors/000000000000010111010-V-0000.bin"
noncomputable def vp000000000000010111010 : Blocks := vp000000000000010111010_0
theorem coverp000000000000010111010 : Covers (-1952806/15625 : ℚ) vp000000000000010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001011101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011101-V-0000.bin"
noncomputable def vp00000000000001011101 : Blocks := vp00000000000001011101_0
private theorem bp000000000000010111010 : Branch 0 (-976403/15625 : ℚ) vp00000000000001011101 := by
  apply branch_left_normalized (c:=vp000000000000010111010) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-976403/15625 : ℚ) - ((0:ℤ):ℚ) = (-1952806/15625 : ℚ) by norm_num]
  exact coverp000000000000010111010
private noncomputable def ep000000000000010111011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010111011-E-0000.bin"
noncomputable def ep000000000000010111011 : Blocks := ep000000000000010111011_0
private theorem idp000000000000010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001011101.list =
    C ((2:ℤ)^25) * horner X vp000000000000010111011.list + horner X ep000000000000010111011.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010111011 : Branch 1 (-976403/15625 : ℚ) vp00000000000001011101 := by
  apply branch_checked idp000000000000010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-976403/15625 : ℚ) - ((1:ℤ):ℚ) = (-1968431/15625 : ℚ) by norm_num]
  exact coverp000000000000010111011
theorem coverp00000000000001011101 : Covers (-976403/15625 : ℚ) vp00000000000001011101 := join_branches bp000000000000010111010 bp000000000000010111011
private noncomputable def vp00000000000001011100_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011100-V-0000.bin"
noncomputable def vp00000000000001011100 : Blocks := vp00000000000001011100_0
theorem coverp00000000000001011100 : Covers (-960778/15625 : ℚ) vp00000000000001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101110-V-0000.bin"
noncomputable def vp0000000000000101110 : Blocks := vp0000000000000101110_0
private theorem bp00000000000001011100 : Branch 0 (-480389/15625 : ℚ) vp0000000000000101110 := by
  apply branch_left_normalized (c:=vp00000000000001011100) (k:=0) (m:=25) (by decide +kernel)
  rw [show 2*(-480389/15625 : ℚ) - ((0:ℤ):ℚ) = (-960778/15625 : ℚ) by norm_num]
  exact coverp00000000000001011100
private noncomputable def ep00000000000001011101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011101-E-0000.bin"
noncomputable def ep00000000000001011101 : Blocks := ep00000000000001011101_0
private theorem idp00000000000001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101110.list =
    C ((2:ℤ)^37) * horner X vp00000000000001011101.list + horner X ep00000000000001011101.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001011101 : Branch 1 (-480389/15625 : ℚ) vp0000000000000101110 := by
  apply branch_checked idp00000000000001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-480389/15625 : ℚ) - ((1:ℤ):ℚ) = (-976403/15625 : ℚ) by norm_num]
  exact coverp00000000000001011101
theorem coverp0000000000000101110 : Covers (-480389/15625 : ℚ) vp0000000000000101110 := join_branches bp00000000000001011100 bp00000000000001011101
private noncomputable def vp000000000000010111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010111-V-0000.bin"
noncomputable def vp000000000000010111 : Blocks := vp000000000000010111_0
private theorem bp0000000000000101110 : Branch 0 (-480389/31250 : ℚ) vp000000000000010111 := by
  apply branch_left_normalized (c:=vp0000000000000101110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-480389/31250 : ℚ) - ((0:ℤ):ℚ) = (-480389/15625 : ℚ) by norm_num]
  exact coverp0000000000000101110
private noncomputable def ep0000000000000101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101111-E-0000.bin"
noncomputable def ep0000000000000101111 : Blocks := ep0000000000000101111_0
private theorem idp0000000000000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010111.list =
    C ((2:ℤ)^58) * horner X vp0000000000000101111.list + horner X ep0000000000000101111.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101111 : Branch 1 (-480389/31250 : ℚ) vp000000000000010111 := by
  apply branch_checked idp0000000000000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-480389/31250 : ℚ) - ((1:ℤ):ℚ) = (-496014/15625 : ℚ) by norm_num]
  exact coverp0000000000000101111
theorem coverp000000000000010111 : Covers (-480389/31250 : ℚ) vp000000000000010111 := join_branches bp0000000000000101110 bp0000000000000101111
private noncomputable def vp0000000000000101101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101101111-V-0000.bin"
noncomputable def vp0000000000000101101111 : Blocks := vp0000000000000101101111_0
theorem coverp0000000000000101101111 : Covers (-3827487/15625 : ℚ) vp0000000000000101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001011011101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011011101-V-0000.bin"
noncomputable def vp00000000000001011011101 : Blocks := vp00000000000001011011101_0
theorem coverp00000000000001011011101 : Covers (-7639349/15625 : ℚ) vp00000000000001011011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001011011100_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011011100-V-0000.bin"
noncomputable def vp00000000000001011011100 : Blocks := vp00000000000001011011100_0
theorem coverp00000000000001011011100 : Covers (-7623724/15625 : ℚ) vp00000000000001011011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101101110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101101110-V-0000.bin"
noncomputable def vp0000000000000101101110 : Blocks := vp0000000000000101101110_0
private theorem bp00000000000001011011100 : Branch 0 (-3811862/15625 : ℚ) vp0000000000000101101110 := by
  apply branch_left_normalized (c:=vp00000000000001011011100) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-3811862/15625 : ℚ) - ((0:ℤ):ℚ) = (-7623724/15625 : ℚ) by norm_num]
  exact coverp00000000000001011011100
private noncomputable def ep00000000000001011011101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011011101-E-0000.bin"
noncomputable def ep00000000000001011011101 : Blocks := ep00000000000001011011101_0
private theorem idp00000000000001011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101101110.list =
    C ((2:ℤ)^16) * horner X vp00000000000001011011101.list + horner X ep00000000000001011011101.list := by
  exact edge_identity (B := (2:ℤ)^108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001011011101 : Branch 1 (-3811862/15625 : ℚ) vp0000000000000101101110 := by
  apply branch_checked idp00000000000001011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-3811862/15625 : ℚ) - ((1:ℤ):ℚ) = (-7639349/15625 : ℚ) by norm_num]
  exact coverp00000000000001011011101
theorem coverp0000000000000101101110 : Covers (-3811862/15625 : ℚ) vp0000000000000101101110 := join_branches bp00000000000001011011100 bp00000000000001011011101
private noncomputable def vp000000000000010110111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110111-V-0000.bin"
noncomputable def vp000000000000010110111 : Blocks := vp000000000000010110111_0
private theorem bp0000000000000101101110 : Branch 0 (-1905931/15625 : ℚ) vp000000000000010110111 := by
  apply branch_left_normalized (c:=vp0000000000000101101110) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1905931/15625 : ℚ) - ((0:ℤ):ℚ) = (-3811862/15625 : ℚ) by norm_num]
  exact coverp0000000000000101101110
private noncomputable def ep0000000000000101101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101101111-E-0000.bin"
noncomputable def ep0000000000000101101111 : Blocks := ep0000000000000101101111_0
private theorem idp0000000000000101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010110111.list =
    C ((2:ℤ)^20) * horner X vp0000000000000101101111.list + horner X ep0000000000000101101111.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101101111 : Branch 1 (-1905931/15625 : ℚ) vp000000000000010110111 := by
  apply branch_checked idp0000000000000101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1905931/15625 : ℚ) - ((1:ℤ):ℚ) = (-3827487/15625 : ℚ) by norm_num]
  exact coverp0000000000000101101111
theorem coverp000000000000010110111 : Covers (-1905931/15625 : ℚ) vp000000000000010110111 := join_branches bp0000000000000101101110 bp0000000000000101101111
private noncomputable def vp00000000000001011011011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011011011-V-0000.bin"
noncomputable def vp00000000000001011011011 : Blocks := vp00000000000001011011011_0
theorem coverp00000000000001011011011 : Covers (-7608099/15625 : ℚ) vp00000000000001011011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001011011010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011011010-V-0000.bin"
noncomputable def vp00000000000001011011010 : Blocks := vp00000000000001011011010_0
theorem coverp00000000000001011011010 : Covers (-7592474/15625 : ℚ) vp00000000000001011011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101101101-V-0000.bin"
noncomputable def vp0000000000000101101101 : Blocks := vp0000000000000101101101_0
private theorem bp00000000000001011011010 : Branch 0 (-3796237/15625 : ℚ) vp0000000000000101101101 := by
  apply branch_left_normalized (c:=vp00000000000001011011010) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-3796237/15625 : ℚ) - ((0:ℤ):ℚ) = (-7592474/15625 : ℚ) by norm_num]
  exact coverp00000000000001011011010
private noncomputable def ep00000000000001011011011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011011011-E-0000.bin"
noncomputable def ep00000000000001011011011 : Blocks := ep00000000000001011011011_0
private theorem idp00000000000001011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101101101.list =
    C ((2:ℤ)^16) * horner X vp00000000000001011011011.list + horner X ep00000000000001011011011.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001011011011 : Branch 1 (-3796237/15625 : ℚ) vp0000000000000101101101 := by
  apply branch_checked idp00000000000001011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-3796237/15625 : ℚ) - ((1:ℤ):ℚ) = (-7608099/15625 : ℚ) by norm_num]
  exact coverp00000000000001011011011
theorem coverp0000000000000101101101 : Covers (-3796237/15625 : ℚ) vp0000000000000101101101 := join_branches bp00000000000001011011010 bp00000000000001011011011
private noncomputable def vp0000000000000101101100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101101100-V-0000.bin"
noncomputable def vp0000000000000101101100 : Blocks := vp0000000000000101101100_0
theorem coverp0000000000000101101100 : Covers (-3780612/15625 : ℚ) vp0000000000000101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010110110_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110110-V-0000.bin"
noncomputable def vp000000000000010110110 : Blocks := vp000000000000010110110_0
private theorem bp0000000000000101101100 : Branch 0 (-1890306/15625 : ℚ) vp000000000000010110110 := by
  apply branch_left_normalized (c:=vp0000000000000101101100) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-1890306/15625 : ℚ) - ((0:ℤ):ℚ) = (-3780612/15625 : ℚ) by norm_num]
  exact coverp0000000000000101101100
private noncomputable def ep0000000000000101101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101101101-E-0000.bin"
noncomputable def ep0000000000000101101101 : Blocks := ep0000000000000101101101_0
private theorem idp0000000000000101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010110110.list =
    C ((2:ℤ)^19) * horner X vp0000000000000101101101.list + horner X ep0000000000000101101101.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101101101 : Branch 1 (-1890306/15625 : ℚ) vp000000000000010110110 := by
  apply branch_checked idp0000000000000101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1890306/15625 : ℚ) - ((1:ℤ):ℚ) = (-3796237/15625 : ℚ) by norm_num]
  exact coverp0000000000000101101101
theorem coverp000000000000010110110 : Covers (-1890306/15625 : ℚ) vp000000000000010110110 := join_branches bp0000000000000101101100 bp0000000000000101101101
private noncomputable def vp00000000000001011011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011011-V-0000.bin"
noncomputable def vp00000000000001011011 : Blocks := vp00000000000001011011_0
private theorem bp000000000000010110110 : Branch 0 (-945153/15625 : ℚ) vp00000000000001011011 := by
  apply branch_left_normalized (c:=vp000000000000010110110) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-945153/15625 : ℚ) - ((0:ℤ):ℚ) = (-1890306/15625 : ℚ) by norm_num]
  exact coverp000000000000010110110
private noncomputable def ep000000000000010110111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110111-E-0000.bin"
noncomputable def ep000000000000010110111 : Blocks := ep000000000000010110111_0
private theorem idp000000000000010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001011011.list =
    C ((2:ℤ)^25) * horner X vp000000000000010110111.list + horner X ep000000000000010110111.list := by
  exact edge_identity (B := (2:ℤ)^121) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010110111 : Branch 1 (-945153/15625 : ℚ) vp00000000000001011011 := by
  apply branch_checked idp000000000000010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-945153/15625 : ℚ) - ((1:ℤ):ℚ) = (-1905931/15625 : ℚ) by norm_num]
  exact coverp000000000000010110111
theorem coverp00000000000001011011 : Covers (-945153/15625 : ℚ) vp00000000000001011011 := join_branches bp000000000000010110110 bp000000000000010110111
private noncomputable def vp000000000000010110101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110101-V-0000.bin"
noncomputable def vp000000000000010110101 : Blocks := vp000000000000010110101_0
theorem coverp000000000000010110101 : Covers (-1874681/15625 : ℚ) vp000000000000010110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010110100_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110100-V-0000.bin"
noncomputable def vp000000000000010110100 : Blocks := vp000000000000010110100_0
theorem coverp000000000000010110100 : Covers (-1859056/15625 : ℚ) vp000000000000010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001011010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011010-V-0000.bin"
noncomputable def vp00000000000001011010 : Blocks := vp00000000000001011010_0
private theorem bp000000000000010110100 : Branch 0 (-929528/15625 : ℚ) vp00000000000001011010 := by
  apply branch_left_normalized (c:=vp000000000000010110100) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-929528/15625 : ℚ) - ((0:ℤ):ℚ) = (-1859056/15625 : ℚ) by norm_num]
  exact coverp000000000000010110100
private noncomputable def ep000000000000010110101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110101-E-0000.bin"
noncomputable def ep000000000000010110101 : Blocks := ep000000000000010110101_0
private theorem idp000000000000010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001011010.list =
    C ((2:ℤ)^25) * horner X vp000000000000010110101.list + horner X ep000000000000010110101.list := by
  exact edge_identity (B := (2:ℤ)^121) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010110101 : Branch 1 (-929528/15625 : ℚ) vp00000000000001011010 := by
  apply branch_checked idp000000000000010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-929528/15625 : ℚ) - ((1:ℤ):ℚ) = (-1874681/15625 : ℚ) by norm_num]
  exact coverp000000000000010110101
theorem coverp00000000000001011010 : Covers (-929528/15625 : ℚ) vp00000000000001011010 := join_branches bp000000000000010110100 bp000000000000010110101
private noncomputable def vp0000000000000101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101101-V-0000.bin"
noncomputable def vp0000000000000101101 : Blocks := vp0000000000000101101_0
private theorem bp00000000000001011010 : Branch 0 (-464764/15625 : ℚ) vp0000000000000101101 := by
  apply branch_left_normalized (c:=vp00000000000001011010) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-464764/15625 : ℚ) - ((0:ℤ):ℚ) = (-929528/15625 : ℚ) by norm_num]
  exact coverp00000000000001011010
private noncomputable def ep00000000000001011011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011011-E-0000.bin"
noncomputable def ep00000000000001011011 : Blocks := ep00000000000001011011_0
private theorem idp00000000000001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101101.list =
    C ((2:ℤ)^37) * horner X vp00000000000001011011.list + horner X ep00000000000001011011.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001011011 : Branch 1 (-464764/15625 : ℚ) vp0000000000000101101 := by
  apply branch_checked idp00000000000001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-464764/15625 : ℚ) - ((1:ℤ):ℚ) = (-945153/15625 : ℚ) by norm_num]
  exact coverp00000000000001011011
theorem coverp0000000000000101101 : Covers (-464764/15625 : ℚ) vp0000000000000101101 := join_branches bp00000000000001011010 bp00000000000001011011
private noncomputable def vp000000000000010110011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110011-V-0000.bin"
noncomputable def vp000000000000010110011 : Blocks := vp000000000000010110011_0
theorem coverp000000000000010110011 : Covers (-1843431/15625 : ℚ) vp000000000000010110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101100101-V-0000.bin"
noncomputable def vp0000000000000101100101 : Blocks := vp0000000000000101100101_0
theorem coverp0000000000000101100101 : Covers (-3671237/15625 : ℚ) vp0000000000000101100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001011001001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011001001-V-0000.bin"
noncomputable def vp00000000000001011001001 : Blocks := vp00000000000001011001001_0
theorem coverp00000000000001011001001 : Covers (-7326849/15625 : ℚ) vp00000000000001011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001011001000_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011001000-V-0000.bin"
noncomputable def vp00000000000001011001000 : Blocks := vp00000000000001011001000_0
theorem coverp00000000000001011001000 : Covers (-7311224/15625 : ℚ) vp00000000000001011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101100100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101100100-V-0000.bin"
noncomputable def vp0000000000000101100100 : Blocks := vp0000000000000101100100_0
private theorem bp00000000000001011001000 : Branch 0 (-3655612/15625 : ℚ) vp0000000000000101100100 := by
  apply branch_left_normalized (c:=vp00000000000001011001000) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-3655612/15625 : ℚ) - ((0:ℤ):ℚ) = (-7311224/15625 : ℚ) by norm_num]
  exact coverp00000000000001011001000
private noncomputable def ep00000000000001011001001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011001001-E-0000.bin"
noncomputable def ep00000000000001011001001 : Blocks := ep00000000000001011001001_0
private theorem idp00000000000001011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101100100.list =
    C ((2:ℤ)^15) * horner X vp00000000000001011001001.list + horner X ep00000000000001011001001.list := by
  exact edge_identity (B := (2:ℤ)^108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001011001001 : Branch 1 (-3655612/15625 : ℚ) vp0000000000000101100100 := by
  apply branch_checked idp00000000000001011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-3655612/15625 : ℚ) - ((1:ℤ):ℚ) = (-7326849/15625 : ℚ) by norm_num]
  exact coverp00000000000001011001001
theorem coverp0000000000000101100100 : Covers (-3655612/15625 : ℚ) vp0000000000000101100100 := join_branches bp00000000000001011001000 bp00000000000001011001001
private noncomputable def vp000000000000010110010_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110010-V-0000.bin"
noncomputable def vp000000000000010110010 : Blocks := vp000000000000010110010_0
private theorem bp0000000000000101100100 : Branch 0 (-1827806/15625 : ℚ) vp000000000000010110010 := by
  apply branch_left_normalized (c:=vp0000000000000101100100) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-1827806/15625 : ℚ) - ((0:ℤ):ℚ) = (-3655612/15625 : ℚ) by norm_num]
  exact coverp0000000000000101100100
private noncomputable def ep0000000000000101100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101100101-E-0000.bin"
noncomputable def ep0000000000000101100101 : Blocks := ep0000000000000101100101_0
private theorem idp0000000000000101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010110010.list =
    C ((2:ℤ)^19) * horner X vp0000000000000101100101.list + horner X ep0000000000000101100101.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101100101 : Branch 1 (-1827806/15625 : ℚ) vp000000000000010110010 := by
  apply branch_checked idp0000000000000101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1827806/15625 : ℚ) - ((1:ℤ):ℚ) = (-3671237/15625 : ℚ) by norm_num]
  exact coverp0000000000000101100101
theorem coverp000000000000010110010 : Covers (-1827806/15625 : ℚ) vp000000000000010110010 := join_branches bp0000000000000101100100 bp0000000000000101100101
private noncomputable def vp00000000000001011001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011001-V-0000.bin"
noncomputable def vp00000000000001011001 : Blocks := vp00000000000001011001_0
private theorem bp000000000000010110010 : Branch 0 (-913903/15625 : ℚ) vp00000000000001011001 := by
  apply branch_left_normalized (c:=vp000000000000010110010) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-913903/15625 : ℚ) - ((0:ℤ):ℚ) = (-1827806/15625 : ℚ) by norm_num]
  exact coverp000000000000010110010
private noncomputable def ep000000000000010110011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110011-E-0000.bin"
noncomputable def ep000000000000010110011 : Blocks := ep000000000000010110011_0
private theorem idp000000000000010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001011001.list =
    C ((2:ℤ)^27) * horner X vp000000000000010110011.list + horner X ep000000000000010110011.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010110011 : Branch 1 (-913903/15625 : ℚ) vp00000000000001011001 := by
  apply branch_checked idp000000000000010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-913903/15625 : ℚ) - ((1:ℤ):ℚ) = (-1843431/15625 : ℚ) by norm_num]
  exact coverp000000000000010110011
theorem coverp00000000000001011001 : Covers (-913903/15625 : ℚ) vp00000000000001011001 := join_branches bp000000000000010110010 bp000000000000010110011
private noncomputable def vp0000000000000101100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101100011-V-0000.bin"
noncomputable def vp0000000000000101100011 : Blocks := vp0000000000000101100011_0
theorem coverp0000000000000101100011 : Covers (-3639987/15625 : ℚ) vp0000000000000101100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101100010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101100010-V-0000.bin"
noncomputable def vp0000000000000101100010 : Blocks := vp0000000000000101100010_0
theorem coverp0000000000000101100010 : Covers (-3624362/15625 : ℚ) vp0000000000000101100010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010110001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110001-V-0000.bin"
noncomputable def vp000000000000010110001 : Blocks := vp000000000000010110001_0
private theorem bp0000000000000101100010 : Branch 0 (-1812181/15625 : ℚ) vp000000000000010110001 := by
  apply branch_left_normalized (c:=vp0000000000000101100010) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-1812181/15625 : ℚ) - ((0:ℤ):ℚ) = (-3624362/15625 : ℚ) by norm_num]
  exact coverp0000000000000101100010
private noncomputable def ep0000000000000101100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101100011-E-0000.bin"
noncomputable def ep0000000000000101100011 : Blocks := ep0000000000000101100011_0
private theorem idp0000000000000101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010110001.list =
    C ((2:ℤ)^18) * horner X vp0000000000000101100011.list + horner X ep0000000000000101100011.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101100011 : Branch 1 (-1812181/15625 : ℚ) vp000000000000010110001 := by
  apply branch_checked idp0000000000000101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1812181/15625 : ℚ) - ((1:ℤ):ℚ) = (-3639987/15625 : ℚ) by norm_num]
  exact coverp0000000000000101100011
theorem coverp000000000000010110001 : Covers (-1812181/15625 : ℚ) vp000000000000010110001 := join_branches bp0000000000000101100010 bp0000000000000101100011
private noncomputable def vp000000000000010110000_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110000-V-0000.bin"
noncomputable def vp000000000000010110000 : Blocks := vp000000000000010110000_0
theorem coverp000000000000010110000 : Covers (-1796556/15625 : ℚ) vp000000000000010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001011000_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011000-V-0000.bin"
noncomputable def vp00000000000001011000 : Blocks := vp00000000000001011000_0
private theorem bp000000000000010110000 : Branch 0 (-898278/15625 : ℚ) vp00000000000001011000 := by
  apply branch_left_normalized (c:=vp000000000000010110000) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-898278/15625 : ℚ) - ((0:ℤ):ℚ) = (-1796556/15625 : ℚ) by norm_num]
  exact coverp000000000000010110000
private noncomputable def ep000000000000010110001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110001-E-0000.bin"
noncomputable def ep000000000000010110001 : Blocks := ep000000000000010110001_0
private theorem idp000000000000010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001011000.list =
    C ((2:ℤ)^26) * horner X vp000000000000010110001.list + horner X ep000000000000010110001.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010110001 : Branch 1 (-898278/15625 : ℚ) vp00000000000001011000 := by
  apply branch_checked idp000000000000010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-898278/15625 : ℚ) - ((1:ℤ):ℚ) = (-1812181/15625 : ℚ) by norm_num]
  exact coverp000000000000010110001
theorem coverp00000000000001011000 : Covers (-898278/15625 : ℚ) vp00000000000001011000 := join_branches bp000000000000010110000 bp000000000000010110001
private noncomputable def vp0000000000000101100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101100-V-0000.bin"
noncomputable def vp0000000000000101100 : Blocks := vp0000000000000101100_0
private theorem bp00000000000001011000 : Branch 0 (-449139/15625 : ℚ) vp0000000000000101100 := by
  apply branch_left_normalized (c:=vp00000000000001011000) (k:=0) (m:=25) (by decide +kernel)
  rw [show 2*(-449139/15625 : ℚ) - ((0:ℤ):ℚ) = (-898278/15625 : ℚ) by norm_num]
  exact coverp00000000000001011000
private noncomputable def ep00000000000001011001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011001-E-0000.bin"
noncomputable def ep00000000000001011001 : Blocks := ep00000000000001011001_0
private theorem idp00000000000001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101100.list =
    C ((2:ℤ)^37) * horner X vp00000000000001011001.list + horner X ep00000000000001011001.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001011001 : Branch 1 (-449139/15625 : ℚ) vp0000000000000101100 := by
  apply branch_checked idp00000000000001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-449139/15625 : ℚ) - ((1:ℤ):ℚ) = (-913903/15625 : ℚ) by norm_num]
  exact coverp00000000000001011001
theorem coverp0000000000000101100 : Covers (-449139/15625 : ℚ) vp0000000000000101100 := join_branches bp00000000000001011000 bp00000000000001011001
private noncomputable def vp000000000000010110_0 : Blocks := edgeBlocks% "full/vectors/000000000000010110-V-0000.bin"
noncomputable def vp000000000000010110 : Blocks := vp000000000000010110_0
private theorem bp0000000000000101100 : Branch 0 (-449139/31250 : ℚ) vp000000000000010110 := by
  apply branch_left_normalized (c:=vp0000000000000101100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-449139/31250 : ℚ) - ((0:ℤ):ℚ) = (-449139/15625 : ℚ) by norm_num]
  exact coverp0000000000000101100
private noncomputable def ep0000000000000101101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101101-E-0000.bin"
noncomputable def ep0000000000000101101 : Blocks := ep0000000000000101101_0
private theorem idp0000000000000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010110.list =
    C ((2:ℤ)^58) * horner X vp0000000000000101101.list + horner X ep0000000000000101101.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101101 : Branch 1 (-449139/31250 : ℚ) vp000000000000010110 := by
  apply branch_checked idp0000000000000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-449139/31250 : ℚ) - ((1:ℤ):ℚ) = (-464764/15625 : ℚ) by norm_num]
  exact coverp0000000000000101101
theorem coverp000000000000010110 : Covers (-449139/31250 : ℚ) vp000000000000010110 := join_branches bp0000000000000101100 bp0000000000000101101
private noncomputable def vp00000000000001011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011-V-0000.bin"
noncomputable def vp00000000000001011 : Blocks := vp00000000000001011_0
private theorem bp000000000000010110 : Branch 0 (-449139/62500 : ℚ) vp00000000000001011 := by
  apply branch_left_normalized (c:=vp000000000000010110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-449139/62500 : ℚ) - ((0:ℤ):ℚ) = (-449139/31250 : ℚ) by norm_num]
  exact coverp000000000000010110
private noncomputable def ep000000000000010111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010111-E-0000.bin"
noncomputable def ep000000000000010111 : Blocks := ep000000000000010111_0
private theorem idp000000000000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001011.list =
    C ((2:ℤ)^97) * horner X vp000000000000010111.list + horner X ep000000000000010111.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010111 : Branch 1 (-449139/62500 : ℚ) vp00000000000001011 := by
  apply branch_checked idp000000000000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-449139/62500 : ℚ) - ((1:ℤ):ℚ) = (-480389/31250 : ℚ) by norm_num]
  exact coverp000000000000010111
theorem coverp00000000000001011 : Covers (-449139/62500 : ℚ) vp00000000000001011 := join_branches bp000000000000010110 bp000000000000010111
private noncomputable def vp00000000000001010111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010111-V-0000.bin"
noncomputable def vp00000000000001010111 : Blocks := vp00000000000001010111_0
theorem coverp00000000000001010111 : Covers (-882653/15625 : ℚ) vp00000000000001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001010110111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010110111-V-0000.bin"
noncomputable def vp00000000000001010110111 : Blocks := vp00000000000001010110111_0
theorem coverp00000000000001010110111 : Covers (-7045599/15625 : ℚ) vp00000000000001010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001010110110_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010110110-V-0000.bin"
noncomputable def vp00000000000001010110110 : Blocks := vp00000000000001010110110_0
theorem coverp00000000000001010110110 : Covers (-7029974/15625 : ℚ) vp00000000000001010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101011011-V-0000.bin"
noncomputable def vp0000000000000101011011 : Blocks := vp0000000000000101011011_0
private theorem bp00000000000001010110110 : Branch 0 (-3514987/15625 : ℚ) vp0000000000000101011011 := by
  apply branch_left_normalized (c:=vp00000000000001010110110) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-3514987/15625 : ℚ) - ((0:ℤ):ℚ) = (-7029974/15625 : ℚ) by norm_num]
  exact coverp00000000000001010110110
private noncomputable def ep00000000000001010110111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010110111-E-0000.bin"
noncomputable def ep00000000000001010110111 : Blocks := ep00000000000001010110111_0
private theorem idp00000000000001010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101011011.list =
    C ((2:ℤ)^15) * horner X vp00000000000001010110111.list + horner X ep00000000000001010110111.list := by
  exact edge_identity (B := (2:ℤ)^107) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001010110111 : Branch 1 (-3514987/15625 : ℚ) vp0000000000000101011011 := by
  apply branch_checked idp00000000000001010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-3514987/15625 : ℚ) - ((1:ℤ):ℚ) = (-7045599/15625 : ℚ) by norm_num]
  exact coverp00000000000001010110111
theorem coverp0000000000000101011011 : Covers (-3514987/15625 : ℚ) vp0000000000000101011011 := join_branches bp00000000000001010110110 bp00000000000001010110111
private noncomputable def vp0000000000000101011010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101011010-V-0000.bin"
noncomputable def vp0000000000000101011010 : Blocks := vp0000000000000101011010_0
theorem coverp0000000000000101011010 : Covers (-3499362/15625 : ℚ) vp0000000000000101011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010101101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010101101-V-0000.bin"
noncomputable def vp000000000000010101101 : Blocks := vp000000000000010101101_0
private theorem bp0000000000000101011010 : Branch 0 (-1749681/15625 : ℚ) vp000000000000010101101 := by
  apply branch_left_normalized (c:=vp0000000000000101011010) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-1749681/15625 : ℚ) - ((0:ℤ):ℚ) = (-3499362/15625 : ℚ) by norm_num]
  exact coverp0000000000000101011010
private noncomputable def ep0000000000000101011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101011011-E-0000.bin"
noncomputable def ep0000000000000101011011 : Blocks := ep0000000000000101011011_0
private theorem idp0000000000000101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010101101.list =
    C ((2:ℤ)^20) * horner X vp0000000000000101011011.list + horner X ep0000000000000101011011.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101011011 : Branch 1 (-1749681/15625 : ℚ) vp000000000000010101101 := by
  apply branch_checked idp0000000000000101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1749681/15625 : ℚ) - ((1:ℤ):ℚ) = (-3514987/15625 : ℚ) by norm_num]
  exact coverp0000000000000101011011
theorem coverp000000000000010101101 : Covers (-1749681/15625 : ℚ) vp000000000000010101101 := join_branches bp0000000000000101011010 bp0000000000000101011011
private noncomputable def vp000000000000010101100_0 : Blocks := edgeBlocks% "full/vectors/000000000000010101100-V-0000.bin"
noncomputable def vp000000000000010101100 : Blocks := vp000000000000010101100_0
theorem coverp000000000000010101100 : Covers (-1734056/15625 : ℚ) vp000000000000010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001010110_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010110-V-0000.bin"
noncomputable def vp00000000000001010110 : Blocks := vp00000000000001010110_0
private theorem bp000000000000010101100 : Branch 0 (-867028/15625 : ℚ) vp00000000000001010110 := by
  apply branch_left_normalized (c:=vp000000000000010101100) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-867028/15625 : ℚ) - ((0:ℤ):ℚ) = (-1734056/15625 : ℚ) by norm_num]
  exact coverp000000000000010101100
private noncomputable def ep000000000000010101101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010101101-E-0000.bin"
noncomputable def ep000000000000010101101 : Blocks := ep000000000000010101101_0
private theorem idp000000000000010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001010110.list =
    C ((2:ℤ)^26) * horner X vp000000000000010101101.list + horner X ep000000000000010101101.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010101101 : Branch 1 (-867028/15625 : ℚ) vp00000000000001010110 := by
  apply branch_checked idp000000000000010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-867028/15625 : ℚ) - ((1:ℤ):ℚ) = (-1749681/15625 : ℚ) by norm_num]
  exact coverp000000000000010101101
theorem coverp00000000000001010110 : Covers (-867028/15625 : ℚ) vp00000000000001010110 := join_branches bp000000000000010101100 bp000000000000010101101
private noncomputable def vp0000000000000101011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101011-V-0000.bin"
noncomputable def vp0000000000000101011 : Blocks := vp0000000000000101011_0
private theorem bp00000000000001010110 : Branch 0 (-433514/15625 : ℚ) vp0000000000000101011 := by
  apply branch_left_normalized (c:=vp00000000000001010110) (k:=0) (m:=25) (by decide +kernel)
  rw [show 2*(-433514/15625 : ℚ) - ((0:ℤ):ℚ) = (-867028/15625 : ℚ) by norm_num]
  exact coverp00000000000001010110
private noncomputable def ep00000000000001010111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010111-E-0000.bin"
noncomputable def ep00000000000001010111 : Blocks := ep00000000000001010111_0
private theorem idp00000000000001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101011.list =
    C ((2:ℤ)^38) * horner X vp00000000000001010111.list + horner X ep00000000000001010111.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001010111 : Branch 1 (-433514/15625 : ℚ) vp0000000000000101011 := by
  apply branch_checked idp00000000000001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-433514/15625 : ℚ) - ((1:ℤ):ℚ) = (-882653/15625 : ℚ) by norm_num]
  exact coverp00000000000001010111
theorem coverp0000000000000101011 : Covers (-433514/15625 : ℚ) vp0000000000000101011 := join_branches bp00000000000001010110 bp00000000000001010111
private noncomputable def vp00000000000001010101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010101-V-0000.bin"
noncomputable def vp00000000000001010101 : Blocks := vp00000000000001010101_0
theorem coverp00000000000001010101 : Covers (-851403/15625 : ℚ) vp00000000000001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101010011-V-0000.bin"
noncomputable def vp0000000000000101010011 : Blocks := vp0000000000000101010011_0
theorem coverp0000000000000101010011 : Covers (-3389987/15625 : ℚ) vp0000000000000101010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001010100101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010100101-V-0000.bin"
noncomputable def vp00000000000001010100101 : Blocks := vp00000000000001010100101_0
theorem coverp00000000000001010100101 : Covers (-6764349/15625 : ℚ) vp00000000000001010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001010100100_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010100100-V-0000.bin"
noncomputable def vp00000000000001010100100 : Blocks := vp00000000000001010100100_0
theorem coverp00000000000001010100100 : Covers (-6748724/15625 : ℚ) vp00000000000001010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101010010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101010010-V-0000.bin"
noncomputable def vp0000000000000101010010 : Blocks := vp0000000000000101010010_0
private theorem bp00000000000001010100100 : Branch 0 (-3374362/15625 : ℚ) vp0000000000000101010010 := by
  apply branch_left_normalized (c:=vp00000000000001010100100) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-3374362/15625 : ℚ) - ((0:ℤ):ℚ) = (-6748724/15625 : ℚ) by norm_num]
  exact coverp00000000000001010100100
private noncomputable def ep00000000000001010100101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010100101-E-0000.bin"
noncomputable def ep00000000000001010100101 : Blocks := ep00000000000001010100101_0
private theorem idp00000000000001010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101010010.list =
    C ((2:ℤ)^16) * horner X vp00000000000001010100101.list + horner X ep00000000000001010100101.list := by
  exact edge_identity (B := (2:ℤ)^108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001010100101 : Branch 1 (-3374362/15625 : ℚ) vp0000000000000101010010 := by
  apply branch_checked idp00000000000001010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-3374362/15625 : ℚ) - ((1:ℤ):ℚ) = (-6764349/15625 : ℚ) by norm_num]
  exact coverp00000000000001010100101
theorem coverp0000000000000101010010 : Covers (-3374362/15625 : ℚ) vp0000000000000101010010 := join_branches bp00000000000001010100100 bp00000000000001010100101
private noncomputable def vp000000000000010101001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010101001-V-0000.bin"
noncomputable def vp000000000000010101001 : Blocks := vp000000000000010101001_0
private theorem bp0000000000000101010010 : Branch 0 (-1687181/15625 : ℚ) vp000000000000010101001 := by
  apply branch_left_normalized (c:=vp0000000000000101010010) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1687181/15625 : ℚ) - ((0:ℤ):ℚ) = (-3374362/15625 : ℚ) by norm_num]
  exact coverp0000000000000101010010
private noncomputable def ep0000000000000101010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101010011-E-0000.bin"
noncomputable def ep0000000000000101010011 : Blocks := ep0000000000000101010011_0
private theorem idp0000000000000101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010101001.list =
    C ((2:ℤ)^20) * horner X vp0000000000000101010011.list + horner X ep0000000000000101010011.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101010011 : Branch 1 (-1687181/15625 : ℚ) vp000000000000010101001 := by
  apply branch_checked idp0000000000000101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1687181/15625 : ℚ) - ((1:ℤ):ℚ) = (-3389987/15625 : ℚ) by norm_num]
  exact coverp0000000000000101010011
theorem coverp000000000000010101001 : Covers (-1687181/15625 : ℚ) vp000000000000010101001 := join_branches bp0000000000000101010010 bp0000000000000101010011
private noncomputable def vp0000000000000101010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101010001-V-0000.bin"
noncomputable def vp0000000000000101010001 : Blocks := vp0000000000000101010001_0
theorem coverp0000000000000101010001 : Covers (-3358737/15625 : ℚ) vp0000000000000101010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101010000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101010000-V-0000.bin"
noncomputable def vp0000000000000101010000 : Blocks := vp0000000000000101010000_0
theorem coverp0000000000000101010000 : Covers (-3343112/15625 : ℚ) vp0000000000000101010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010101000_0 : Blocks := edgeBlocks% "full/vectors/000000000000010101000-V-0000.bin"
noncomputable def vp000000000000010101000 : Blocks := vp000000000000010101000_0
private theorem bp0000000000000101010000 : Branch 0 (-1671556/15625 : ℚ) vp000000000000010101000 := by
  apply branch_left_normalized (c:=vp0000000000000101010000) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-1671556/15625 : ℚ) - ((0:ℤ):ℚ) = (-3343112/15625 : ℚ) by norm_num]
  exact coverp0000000000000101010000
private noncomputable def ep0000000000000101010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101010001-E-0000.bin"
noncomputable def ep0000000000000101010001 : Blocks := ep0000000000000101010001_0
private theorem idp0000000000000101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010101000.list =
    C ((2:ℤ)^20) * horner X vp0000000000000101010001.list + horner X ep0000000000000101010001.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101010001 : Branch 1 (-1671556/15625 : ℚ) vp000000000000010101000 := by
  apply branch_checked idp0000000000000101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1671556/15625 : ℚ) - ((1:ℤ):ℚ) = (-3358737/15625 : ℚ) by norm_num]
  exact coverp0000000000000101010001
theorem coverp000000000000010101000 : Covers (-1671556/15625 : ℚ) vp000000000000010101000 := join_branches bp0000000000000101010000 bp0000000000000101010001
private noncomputable def vp00000000000001010100_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010100-V-0000.bin"
noncomputable def vp00000000000001010100 : Blocks := vp00000000000001010100_0
private theorem bp000000000000010101000 : Branch 0 (-835778/15625 : ℚ) vp00000000000001010100 := by
  apply branch_left_normalized (c:=vp000000000000010101000) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-835778/15625 : ℚ) - ((0:ℤ):ℚ) = (-1671556/15625 : ℚ) by norm_num]
  exact coverp000000000000010101000
private noncomputable def ep000000000000010101001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010101001-E-0000.bin"
noncomputable def ep000000000000010101001 : Blocks := ep000000000000010101001_0
private theorem idp000000000000010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001010100.list =
    C ((2:ℤ)^26) * horner X vp000000000000010101001.list + horner X ep000000000000010101001.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010101001 : Branch 1 (-835778/15625 : ℚ) vp00000000000001010100 := by
  apply branch_checked idp000000000000010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-835778/15625 : ℚ) - ((1:ℤ):ℚ) = (-1687181/15625 : ℚ) by norm_num]
  exact coverp000000000000010101001
theorem coverp00000000000001010100 : Covers (-835778/15625 : ℚ) vp00000000000001010100 := join_branches bp000000000000010101000 bp000000000000010101001
private noncomputable def vp0000000000000101010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101010-V-0000.bin"
noncomputable def vp0000000000000101010 : Blocks := vp0000000000000101010_0
private theorem bp00000000000001010100 : Branch 0 (-417889/15625 : ℚ) vp0000000000000101010 := by
  apply branch_left_normalized (c:=vp00000000000001010100) (k:=0) (m:=25) (by decide +kernel)
  rw [show 2*(-417889/15625 : ℚ) - ((0:ℤ):ℚ) = (-835778/15625 : ℚ) by norm_num]
  exact coverp00000000000001010100
private noncomputable def ep00000000000001010101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010101-E-0000.bin"
noncomputable def ep00000000000001010101 : Blocks := ep00000000000001010101_0
private theorem idp00000000000001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101010.list =
    C ((2:ℤ)^38) * horner X vp00000000000001010101.list + horner X ep00000000000001010101.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001010101 : Branch 1 (-417889/15625 : ℚ) vp0000000000000101010 := by
  apply branch_checked idp00000000000001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-417889/15625 : ℚ) - ((1:ℤ):ℚ) = (-851403/15625 : ℚ) by norm_num]
  exact coverp00000000000001010101
theorem coverp0000000000000101010 : Covers (-417889/15625 : ℚ) vp0000000000000101010 := join_branches bp00000000000001010100 bp00000000000001010101
private noncomputable def vp000000000000010101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010101-V-0000.bin"
noncomputable def vp000000000000010101 : Blocks := vp000000000000010101_0
private theorem bp0000000000000101010 : Branch 0 (-417889/31250 : ℚ) vp000000000000010101 := by
  apply branch_left_normalized (c:=vp0000000000000101010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-417889/31250 : ℚ) - ((0:ℤ):ℚ) = (-417889/15625 : ℚ) by norm_num]
  exact coverp0000000000000101010
private noncomputable def ep0000000000000101011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101011-E-0000.bin"
noncomputable def ep0000000000000101011 : Blocks := ep0000000000000101011_0
private theorem idp0000000000000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010101.list =
    C ((2:ℤ)^59) * horner X vp0000000000000101011.list + horner X ep0000000000000101011.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101011 : Branch 1 (-417889/31250 : ℚ) vp000000000000010101 := by
  apply branch_checked idp0000000000000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-417889/31250 : ℚ) - ((1:ℤ):ℚ) = (-433514/15625 : ℚ) by norm_num]
  exact coverp0000000000000101011
theorem coverp000000000000010101 : Covers (-417889/31250 : ℚ) vp000000000000010101 := join_branches bp0000000000000101010 bp0000000000000101011
private noncomputable def vp00000000000001010011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010011-V-0000.bin"
noncomputable def vp00000000000001010011 : Blocks := vp00000000000001010011_0
theorem coverp00000000000001010011 : Covers (-820153/15625 : ℚ) vp00000000000001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010100101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010100101-V-0000.bin"
noncomputable def vp000000000000010100101 : Blocks := vp000000000000010100101_0
theorem coverp000000000000010100101 : Covers (-1624681/15625 : ℚ) vp000000000000010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001010010011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010010011-V-0000.bin"
noncomputable def vp00000000000001010010011 : Blocks := vp00000000000001010010011_0
theorem coverp00000000000001010010011 : Covers (-6483099/15625 : ℚ) vp00000000000001010010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001010010010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010010010-V-0000.bin"
noncomputable def vp00000000000001010010010 : Blocks := vp00000000000001010010010_0
theorem coverp00000000000001010010010 : Covers (-6467474/15625 : ℚ) vp00000000000001010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101001001-V-0000.bin"
noncomputable def vp0000000000000101001001 : Blocks := vp0000000000000101001001_0
private theorem bp00000000000001010010010 : Branch 0 (-3233737/15625 : ℚ) vp0000000000000101001001 := by
  apply branch_left_normalized (c:=vp00000000000001010010010) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-3233737/15625 : ℚ) - ((0:ℤ):ℚ) = (-6467474/15625 : ℚ) by norm_num]
  exact coverp00000000000001010010010
private noncomputable def ep00000000000001010010011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010010011-E-0000.bin"
noncomputable def ep00000000000001010010011 : Blocks := ep00000000000001010010011_0
private theorem idp00000000000001010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101001001.list =
    C ((2:ℤ)^16) * horner X vp00000000000001010010011.list + horner X ep00000000000001010010011.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001010010011 : Branch 1 (-3233737/15625 : ℚ) vp0000000000000101001001 := by
  apply branch_checked idp00000000000001010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-3233737/15625 : ℚ) - ((1:ℤ):ℚ) = (-6483099/15625 : ℚ) by norm_num]
  exact coverp00000000000001010010011
theorem coverp0000000000000101001001 : Covers (-3233737/15625 : ℚ) vp0000000000000101001001 := join_branches bp00000000000001010010010 bp00000000000001010010011
private noncomputable def vp0000000000000101001000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101001000-V-0000.bin"
noncomputable def vp0000000000000101001000 : Blocks := vp0000000000000101001000_0
theorem coverp0000000000000101001000 : Covers (-3218112/15625 : ℚ) vp0000000000000101001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010100100_0 : Blocks := edgeBlocks% "full/vectors/000000000000010100100-V-0000.bin"
noncomputable def vp000000000000010100100 : Blocks := vp000000000000010100100_0
private theorem bp0000000000000101001000 : Branch 0 (-1609056/15625 : ℚ) vp000000000000010100100 := by
  apply branch_left_normalized (c:=vp0000000000000101001000) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-1609056/15625 : ℚ) - ((0:ℤ):ℚ) = (-3218112/15625 : ℚ) by norm_num]
  exact coverp0000000000000101001000
private noncomputable def ep0000000000000101001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101001001-E-0000.bin"
noncomputable def ep0000000000000101001001 : Blocks := ep0000000000000101001001_0
private theorem idp0000000000000101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010100100.list =
    C ((2:ℤ)^20) * horner X vp0000000000000101001001.list + horner X ep0000000000000101001001.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101001001 : Branch 1 (-1609056/15625 : ℚ) vp000000000000010100100 := by
  apply branch_checked idp0000000000000101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1609056/15625 : ℚ) - ((1:ℤ):ℚ) = (-3233737/15625 : ℚ) by norm_num]
  exact coverp0000000000000101001001
theorem coverp000000000000010100100 : Covers (-1609056/15625 : ℚ) vp000000000000010100100 := join_branches bp0000000000000101001000 bp0000000000000101001001
private noncomputable def vp00000000000001010010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010010-V-0000.bin"
noncomputable def vp00000000000001010010 : Blocks := vp00000000000001010010_0
private theorem bp000000000000010100100 : Branch 0 (-804528/15625 : ℚ) vp00000000000001010010 := by
  apply branch_left_normalized (c:=vp000000000000010100100) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-804528/15625 : ℚ) - ((0:ℤ):ℚ) = (-1609056/15625 : ℚ) by norm_num]
  exact coverp000000000000010100100
private noncomputable def ep000000000000010100101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010100101-E-0000.bin"
noncomputable def ep000000000000010100101 : Blocks := ep000000000000010100101_0
private theorem idp000000000000010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001010010.list =
    C ((2:ℤ)^27) * horner X vp000000000000010100101.list + horner X ep000000000000010100101.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010100101 : Branch 1 (-804528/15625 : ℚ) vp00000000000001010010 := by
  apply branch_checked idp000000000000010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-804528/15625 : ℚ) - ((1:ℤ):ℚ) = (-1624681/15625 : ℚ) by norm_num]
  exact coverp000000000000010100101
theorem coverp00000000000001010010 : Covers (-804528/15625 : ℚ) vp00000000000001010010 := join_branches bp000000000000010100100 bp000000000000010100101
private noncomputable def vp0000000000000101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101001-V-0000.bin"
noncomputable def vp0000000000000101001 : Blocks := vp0000000000000101001_0
private theorem bp00000000000001010010 : Branch 0 (-402264/15625 : ℚ) vp0000000000000101001 := by
  apply branch_left_normalized (c:=vp00000000000001010010) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-402264/15625 : ℚ) - ((0:ℤ):ℚ) = (-804528/15625 : ℚ) by norm_num]
  exact coverp00000000000001010010
private noncomputable def ep00000000000001010011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010011-E-0000.bin"
noncomputable def ep00000000000001010011 : Blocks := ep00000000000001010011_0
private theorem idp00000000000001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101001.list =
    C ((2:ℤ)^39) * horner X vp00000000000001010011.list + horner X ep00000000000001010011.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001010011 : Branch 1 (-402264/15625 : ℚ) vp0000000000000101001 := by
  apply branch_checked idp00000000000001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-402264/15625 : ℚ) - ((1:ℤ):ℚ) = (-820153/15625 : ℚ) by norm_num]
  exact coverp00000000000001010011
theorem coverp0000000000000101001 : Covers (-402264/15625 : ℚ) vp0000000000000101001 := join_branches bp00000000000001010010 bp00000000000001010011
private noncomputable def vp000000000000010100011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010100011-V-0000.bin"
noncomputable def vp000000000000010100011 : Blocks := vp000000000000010100011_0
theorem coverp000000000000010100011 : Covers (-1593431/15625 : ℚ) vp000000000000010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010100010_0 : Blocks := edgeBlocks% "full/vectors/000000000000010100010-V-0000.bin"
noncomputable def vp000000000000010100010 : Blocks := vp000000000000010100010_0
theorem coverp000000000000010100010 : Covers (-1577806/15625 : ℚ) vp000000000000010100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001010001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010001-V-0000.bin"
noncomputable def vp00000000000001010001 : Blocks := vp00000000000001010001_0
private theorem bp000000000000010100010 : Branch 0 (-788903/15625 : ℚ) vp00000000000001010001 := by
  apply branch_left_normalized (c:=vp000000000000010100010) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-788903/15625 : ℚ) - ((0:ℤ):ℚ) = (-1577806/15625 : ℚ) by norm_num]
  exact coverp000000000000010100010
private noncomputable def ep000000000000010100011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010100011-E-0000.bin"
noncomputable def ep000000000000010100011 : Blocks := ep000000000000010100011_0
private theorem idp000000000000010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001010001.list =
    C ((2:ℤ)^26) * horner X vp000000000000010100011.list + horner X ep000000000000010100011.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010100011 : Branch 1 (-788903/15625 : ℚ) vp00000000000001010001 := by
  apply branch_checked idp000000000000010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-788903/15625 : ℚ) - ((1:ℤ):ℚ) = (-1593431/15625 : ℚ) by norm_num]
  exact coverp000000000000010100011
theorem coverp00000000000001010001 : Covers (-788903/15625 : ℚ) vp00000000000001010001 := join_branches bp000000000000010100010 bp000000000000010100011
private noncomputable def vp000000000000010100001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010100001-V-0000.bin"
noncomputable def vp000000000000010100001 : Blocks := vp000000000000010100001_0
theorem coverp000000000000010100001 : Covers (-1562181/15625 : ℚ) vp000000000000010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101000001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101000001-V-0000.bin"
noncomputable def vp0000000000000101000001 : Blocks := vp0000000000000101000001_0
theorem coverp0000000000000101000001 : Covers (-3108737/15625 : ℚ) vp0000000000000101000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000101000000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101000000-V-0000.bin"
noncomputable def vp0000000000000101000000 : Blocks := vp0000000000000101000000_0
theorem coverp0000000000000101000000 : Covers (-3093112/15625 : ℚ) vp0000000000000101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010100000_0 : Blocks := edgeBlocks% "full/vectors/000000000000010100000-V-0000.bin"
noncomputable def vp000000000000010100000 : Blocks := vp000000000000010100000_0
private theorem bp0000000000000101000000 : Branch 0 (-1546556/15625 : ℚ) vp000000000000010100000 := by
  apply branch_left_normalized (c:=vp0000000000000101000000) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1546556/15625 : ℚ) - ((0:ℤ):ℚ) = (-3093112/15625 : ℚ) by norm_num]
  exact coverp0000000000000101000000
private noncomputable def ep0000000000000101000001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101000001-E-0000.bin"
noncomputable def ep0000000000000101000001 : Blocks := ep0000000000000101000001_0
private theorem idp0000000000000101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010100000.list =
    C ((2:ℤ)^20) * horner X vp0000000000000101000001.list + horner X ep0000000000000101000001.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101000001 : Branch 1 (-1546556/15625 : ℚ) vp000000000000010100000 := by
  apply branch_checked idp0000000000000101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1546556/15625 : ℚ) - ((1:ℤ):ℚ) = (-3108737/15625 : ℚ) by norm_num]
  exact coverp0000000000000101000001
theorem coverp000000000000010100000 : Covers (-1546556/15625 : ℚ) vp000000000000010100000 := join_branches bp0000000000000101000000 bp0000000000000101000001
private noncomputable def vp00000000000001010000_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010000-V-0000.bin"
noncomputable def vp00000000000001010000 : Blocks := vp00000000000001010000_0
private theorem bp000000000000010100000 : Branch 0 (-773278/15625 : ℚ) vp00000000000001010000 := by
  apply branch_left_normalized (c:=vp000000000000010100000) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-773278/15625 : ℚ) - ((0:ℤ):ℚ) = (-1546556/15625 : ℚ) by norm_num]
  exact coverp000000000000010100000
private noncomputable def ep000000000000010100001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010100001-E-0000.bin"
noncomputable def ep000000000000010100001 : Blocks := ep000000000000010100001_0
private theorem idp000000000000010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001010000.list =
    C ((2:ℤ)^27) * horner X vp000000000000010100001.list + horner X ep000000000000010100001.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010100001 : Branch 1 (-773278/15625 : ℚ) vp00000000000001010000 := by
  apply branch_checked idp000000000000010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-773278/15625 : ℚ) - ((1:ℤ):ℚ) = (-1562181/15625 : ℚ) by norm_num]
  exact coverp000000000000010100001
theorem coverp00000000000001010000 : Covers (-773278/15625 : ℚ) vp00000000000001010000 := join_branches bp000000000000010100000 bp000000000000010100001
private noncomputable def vp0000000000000101000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101000-V-0000.bin"
noncomputable def vp0000000000000101000 : Blocks := vp0000000000000101000_0
private theorem bp00000000000001010000 : Branch 0 (-386639/15625 : ℚ) vp0000000000000101000 := by
  apply branch_left_normalized (c:=vp00000000000001010000) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-386639/15625 : ℚ) - ((0:ℤ):ℚ) = (-773278/15625 : ℚ) by norm_num]
  exact coverp00000000000001010000
private noncomputable def ep00000000000001010001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010001-E-0000.bin"
noncomputable def ep00000000000001010001 : Blocks := ep00000000000001010001_0
private theorem idp00000000000001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101000.list =
    C ((2:ℤ)^39) * horner X vp00000000000001010001.list + horner X ep00000000000001010001.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001010001 : Branch 1 (-386639/15625 : ℚ) vp0000000000000101000 := by
  apply branch_checked idp00000000000001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-386639/15625 : ℚ) - ((1:ℤ):ℚ) = (-788903/15625 : ℚ) by norm_num]
  exact coverp00000000000001010001
theorem coverp0000000000000101000 : Covers (-386639/15625 : ℚ) vp0000000000000101000 := join_branches bp00000000000001010000 bp00000000000001010001
private noncomputable def vp000000000000010100_0 : Blocks := edgeBlocks% "full/vectors/000000000000010100-V-0000.bin"
noncomputable def vp000000000000010100 : Blocks := vp000000000000010100_0
private theorem bp0000000000000101000 : Branch 0 (-386639/31250 : ℚ) vp000000000000010100 := by
  apply branch_left_normalized (c:=vp0000000000000101000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-386639/31250 : ℚ) - ((0:ℤ):ℚ) = (-386639/15625 : ℚ) by norm_num]
  exact coverp0000000000000101000
private noncomputable def ep0000000000000101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101001-E-0000.bin"
noncomputable def ep0000000000000101001 : Blocks := ep0000000000000101001_0
private theorem idp0000000000000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010100.list =
    C ((2:ℤ)^62) * horner X vp0000000000000101001.list + horner X ep0000000000000101001.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101001 : Branch 1 (-386639/31250 : ℚ) vp000000000000010100 := by
  apply branch_checked idp0000000000000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-386639/31250 : ℚ) - ((1:ℤ):ℚ) = (-402264/15625 : ℚ) by norm_num]
  exact coverp0000000000000101001
theorem coverp000000000000010100 : Covers (-386639/31250 : ℚ) vp000000000000010100 := join_branches bp0000000000000101000 bp0000000000000101001
private noncomputable def vp00000000000001010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001010-V-0000.bin"
noncomputable def vp00000000000001010 : Blocks := vp00000000000001010_0
private theorem bp000000000000010100 : Branch 0 (-386639/62500 : ℚ) vp00000000000001010 := by
  apply branch_left_normalized (c:=vp000000000000010100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-386639/62500 : ℚ) - ((0:ℤ):ℚ) = (-386639/31250 : ℚ) by norm_num]
  exact coverp000000000000010100
private noncomputable def ep000000000000010101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010101-E-0000.bin"
noncomputable def ep000000000000010101 : Blocks := ep000000000000010101_0
private theorem idp000000000000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001010.list =
    C ((2:ℤ)^102) * horner X vp000000000000010101.list + horner X ep000000000000010101.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010101 : Branch 1 (-386639/62500 : ℚ) vp00000000000001010 := by
  apply branch_checked idp000000000000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-386639/62500 : ℚ) - ((1:ℤ):ℚ) = (-417889/31250 : ℚ) by norm_num]
  exact coverp000000000000010101
theorem coverp00000000000001010 : Covers (-386639/62500 : ℚ) vp00000000000001010 := join_branches bp000000000000010100 bp000000000000010101
private noncomputable def vp0000000000000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101-V-0000.bin"
private noncomputable def vp0000000000000101_1 : Blocks := edgeBlocks% "full/vectors/0000000000000101-V-0001.bin"
noncomputable def vp0000000000000101 : Blocks := (Blocks.join vp0000000000000101_0 vp0000000000000101_1)
private theorem bp00000000000001010 : Branch 0 (-386639/125000 : ℚ) vp0000000000000101 := by
  apply branch_left_normalized (c:=vp00000000000001010) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-386639/62500 : ℚ) by norm_num]
  exact coverp00000000000001010
private noncomputable def ep00000000000001011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001011-E-0000.bin"
private noncomputable def ep00000000000001011_1 : Blocks := edgeBlocks% "full/vectors/00000000000001011-E-0001.bin"
noncomputable def ep00000000000001011 : Blocks := (Blocks.join ep00000000000001011_0 ep00000000000001011_1)
private theorem idp00000000000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000101.list =
    C ((2:ℤ)^181) * horner X vp00000000000001011.list + horner X ep00000000000001011.list := by
  exact edge_identity (B := (2:ℤ)^349) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001011 : Branch 1 (-386639/125000 : ℚ) vp0000000000000101 := by
  apply branch_checked idp00000000000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-449139/62500 : ℚ) by norm_num]
  exact coverp00000000000001011
theorem coverp0000000000000101 : Covers (-386639/125000 : ℚ) vp0000000000000101 := join_branches bp00000000000001010 bp00000000000001011
private noncomputable def vp0000000000000100111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100111111-V-0000.bin"
noncomputable def vp0000000000000100111111 : Blocks := vp0000000000000100111111_0
theorem coverp0000000000000100111111 : Covers (-3077487/15625 : ℚ) vp0000000000000100111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100111110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100111110-V-0000.bin"
noncomputable def vp0000000000000100111110 : Blocks := vp0000000000000100111110_0
theorem coverp0000000000000100111110 : Covers (-3061862/15625 : ℚ) vp0000000000000100111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010011111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010011111-V-0000.bin"
noncomputable def vp000000000000010011111 : Blocks := vp000000000000010011111_0
private theorem bp0000000000000100111110 : Branch 0 (-1530931/15625 : ℚ) vp000000000000010011111 := by
  apply branch_left_normalized (c:=vp0000000000000100111110) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-1530931/15625 : ℚ) - ((0:ℤ):ℚ) = (-3061862/15625 : ℚ) by norm_num]
  exact coverp0000000000000100111110
private noncomputable def ep0000000000000100111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100111111-E-0000.bin"
noncomputable def ep0000000000000100111111 : Blocks := ep0000000000000100111111_0
private theorem idp0000000000000100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010011111.list =
    C ((2:ℤ)^19) * horner X vp0000000000000100111111.list + horner X ep0000000000000100111111.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100111111 : Branch 1 (-1530931/15625 : ℚ) vp000000000000010011111 := by
  apply branch_checked idp0000000000000100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1530931/15625 : ℚ) - ((1:ℤ):ℚ) = (-3077487/15625 : ℚ) by norm_num]
  exact coverp0000000000000100111111
theorem coverp000000000000010011111 : Covers (-1530931/15625 : ℚ) vp000000000000010011111 := join_branches bp0000000000000100111110 bp0000000000000100111111
private noncomputable def vp000000000000010011110_0 : Blocks := edgeBlocks% "full/vectors/000000000000010011110-V-0000.bin"
noncomputable def vp000000000000010011110 : Blocks := vp000000000000010011110_0
theorem coverp000000000000010011110 : Covers (-1515306/15625 : ℚ) vp000000000000010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001001111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001111-V-0000.bin"
noncomputable def vp00000000000001001111 : Blocks := vp00000000000001001111_0
private theorem bp000000000000010011110 : Branch 0 (-757653/15625 : ℚ) vp00000000000001001111 := by
  apply branch_left_normalized (c:=vp000000000000010011110) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-757653/15625 : ℚ) - ((0:ℤ):ℚ) = (-1515306/15625 : ℚ) by norm_num]
  exact coverp000000000000010011110
private noncomputable def ep000000000000010011111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010011111-E-0000.bin"
noncomputable def ep000000000000010011111 : Blocks := ep000000000000010011111_0
private theorem idp000000000000010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001001111.list =
    C ((2:ℤ)^27) * horner X vp000000000000010011111.list + horner X ep000000000000010011111.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010011111 : Branch 1 (-757653/15625 : ℚ) vp00000000000001001111 := by
  apply branch_checked idp000000000000010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-757653/15625 : ℚ) - ((1:ℤ):ℚ) = (-1530931/15625 : ℚ) by norm_num]
  exact coverp000000000000010011111
theorem coverp00000000000001001111 : Covers (-757653/15625 : ℚ) vp00000000000001001111 := join_branches bp000000000000010011110 bp000000000000010011111
private noncomputable def vp00000000000001001110_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001110-V-0000.bin"
noncomputable def vp00000000000001001110 : Blocks := vp00000000000001001110_0
theorem coverp00000000000001001110 : Covers (-742028/15625 : ℚ) vp00000000000001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100111-V-0000.bin"
noncomputable def vp0000000000000100111 : Blocks := vp0000000000000100111_0
private theorem bp00000000000001001110 : Branch 0 (-371014/15625 : ℚ) vp0000000000000100111 := by
  apply branch_left_normalized (c:=vp00000000000001001110) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-371014/15625 : ℚ) - ((0:ℤ):ℚ) = (-742028/15625 : ℚ) by norm_num]
  exact coverp00000000000001001110
private noncomputable def ep00000000000001001111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001111-E-0000.bin"
noncomputable def ep00000000000001001111 : Blocks := ep00000000000001001111_0
private theorem idp00000000000001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000100111.list =
    C ((2:ℤ)^40) * horner X vp00000000000001001111.list + horner X ep00000000000001001111.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001001111 : Branch 1 (-371014/15625 : ℚ) vp0000000000000100111 := by
  apply branch_checked idp00000000000001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-371014/15625 : ℚ) - ((1:ℤ):ℚ) = (-757653/15625 : ℚ) by norm_num]
  exact coverp00000000000001001111
theorem coverp0000000000000100111 : Covers (-371014/15625 : ℚ) vp0000000000000100111 := join_branches bp00000000000001001110 bp00000000000001001111
private noncomputable def vp0000000000000100110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100110111-V-0000.bin"
noncomputable def vp0000000000000100110111 : Blocks := vp0000000000000100110111_0
theorem coverp0000000000000100110111 : Covers (-2952487/15625 : ℚ) vp0000000000000100110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100110110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100110110-V-0000.bin"
noncomputable def vp0000000000000100110110 : Blocks := vp0000000000000100110110_0
theorem coverp0000000000000100110110 : Covers (-2936862/15625 : ℚ) vp0000000000000100110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010011011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010011011-V-0000.bin"
noncomputable def vp000000000000010011011 : Blocks := vp000000000000010011011_0
private theorem bp0000000000000100110110 : Branch 0 (-1468431/15625 : ℚ) vp000000000000010011011 := by
  apply branch_left_normalized (c:=vp0000000000000100110110) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1468431/15625 : ℚ) - ((0:ℤ):ℚ) = (-2936862/15625 : ℚ) by norm_num]
  exact coverp0000000000000100110110
private noncomputable def ep0000000000000100110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100110111-E-0000.bin"
noncomputable def ep0000000000000100110111 : Blocks := ep0000000000000100110111_0
private theorem idp0000000000000100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010011011.list =
    C ((2:ℤ)^20) * horner X vp0000000000000100110111.list + horner X ep0000000000000100110111.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100110111 : Branch 1 (-1468431/15625 : ℚ) vp000000000000010011011 := by
  apply branch_checked idp0000000000000100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1468431/15625 : ℚ) - ((1:ℤ):ℚ) = (-2952487/15625 : ℚ) by norm_num]
  exact coverp0000000000000100110111
theorem coverp000000000000010011011 : Covers (-1468431/15625 : ℚ) vp000000000000010011011 := join_branches bp0000000000000100110110 bp0000000000000100110111
private noncomputable def vp000000000000010011010_0 : Blocks := edgeBlocks% "full/vectors/000000000000010011010-V-0000.bin"
noncomputable def vp000000000000010011010 : Blocks := vp000000000000010011010_0
theorem coverp000000000000010011010 : Covers (-1452806/15625 : ℚ) vp000000000000010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001001101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001101-V-0000.bin"
noncomputable def vp00000000000001001101 : Blocks := vp00000000000001001101_0
private theorem bp000000000000010011010 : Branch 0 (-726403/15625 : ℚ) vp00000000000001001101 := by
  apply branch_left_normalized (c:=vp000000000000010011010) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-726403/15625 : ℚ) - ((0:ℤ):ℚ) = (-1452806/15625 : ℚ) by norm_num]
  exact coverp000000000000010011010
private noncomputable def ep000000000000010011011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010011011-E-0000.bin"
noncomputable def ep000000000000010011011 : Blocks := ep000000000000010011011_0
private theorem idp000000000000010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001001101.list =
    C ((2:ℤ)^27) * horner X vp000000000000010011011.list + horner X ep000000000000010011011.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010011011 : Branch 1 (-726403/15625 : ℚ) vp00000000000001001101 := by
  apply branch_checked idp000000000000010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-726403/15625 : ℚ) - ((1:ℤ):ℚ) = (-1468431/15625 : ℚ) by norm_num]
  exact coverp000000000000010011011
theorem coverp00000000000001001101 : Covers (-726403/15625 : ℚ) vp00000000000001001101 := join_branches bp000000000000010011010 bp000000000000010011011
private noncomputable def vp00000000000001001100_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001100-V-0000.bin"
noncomputable def vp00000000000001001100 : Blocks := vp00000000000001001100_0
theorem coverp00000000000001001100 : Covers (-710778/15625 : ℚ) vp00000000000001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100110-V-0000.bin"
noncomputable def vp0000000000000100110 : Blocks := vp0000000000000100110_0
private theorem bp00000000000001001100 : Branch 0 (-355389/15625 : ℚ) vp0000000000000100110 := by
  apply branch_left_normalized (c:=vp00000000000001001100) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-355389/15625 : ℚ) - ((0:ℤ):ℚ) = (-710778/15625 : ℚ) by norm_num]
  exact coverp00000000000001001100
private noncomputable def ep00000000000001001101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001101-E-0000.bin"
noncomputable def ep00000000000001001101 : Blocks := ep00000000000001001101_0
private theorem idp00000000000001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000100110.list =
    C ((2:ℤ)^40) * horner X vp00000000000001001101.list + horner X ep00000000000001001101.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001001101 : Branch 1 (-355389/15625 : ℚ) vp0000000000000100110 := by
  apply branch_checked idp00000000000001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-355389/15625 : ℚ) - ((1:ℤ):ℚ) = (-726403/15625 : ℚ) by norm_num]
  exact coverp00000000000001001101
theorem coverp0000000000000100110 : Covers (-355389/15625 : ℚ) vp0000000000000100110 := join_branches bp00000000000001001100 bp00000000000001001101
private noncomputable def vp000000000000010011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010011-V-0000.bin"
noncomputable def vp000000000000010011 : Blocks := vp000000000000010011_0
private theorem bp0000000000000100110 : Branch 0 (-355389/31250 : ℚ) vp000000000000010011 := by
  apply branch_left_normalized (c:=vp0000000000000100110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-355389/31250 : ℚ) - ((0:ℤ):ℚ) = (-355389/15625 : ℚ) by norm_num]
  exact coverp0000000000000100110
private noncomputable def ep0000000000000100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100111-E-0000.bin"
noncomputable def ep0000000000000100111 : Blocks := ep0000000000000100111_0
private theorem idp0000000000000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010011.list =
    C ((2:ℤ)^63) * horner X vp0000000000000100111.list + horner X ep0000000000000100111.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100111 : Branch 1 (-355389/31250 : ℚ) vp000000000000010011 := by
  apply branch_checked idp0000000000000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-355389/31250 : ℚ) - ((1:ℤ):ℚ) = (-371014/15625 : ℚ) by norm_num]
  exact coverp0000000000000100111
theorem coverp000000000000010011 : Covers (-355389/31250 : ℚ) vp000000000000010011 := join_branches bp0000000000000100110 bp0000000000000100111
private noncomputable def vp0000000000000100101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100101111-V-0000.bin"
noncomputable def vp0000000000000100101111 : Blocks := vp0000000000000100101111_0
theorem coverp0000000000000100101111 : Covers (-2827487/15625 : ℚ) vp0000000000000100101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100101110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100101110-V-0000.bin"
noncomputable def vp0000000000000100101110 : Blocks := vp0000000000000100101110_0
theorem coverp0000000000000100101110 : Covers (-2811862/15625 : ℚ) vp0000000000000100101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010010111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010010111-V-0000.bin"
noncomputable def vp000000000000010010111 : Blocks := vp000000000000010010111_0
private theorem bp0000000000000100101110 : Branch 0 (-1405931/15625 : ℚ) vp000000000000010010111 := by
  apply branch_left_normalized (c:=vp0000000000000100101110) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1405931/15625 : ℚ) - ((0:ℤ):ℚ) = (-2811862/15625 : ℚ) by norm_num]
  exact coverp0000000000000100101110
private noncomputable def ep0000000000000100101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100101111-E-0000.bin"
noncomputable def ep0000000000000100101111 : Blocks := ep0000000000000100101111_0
private theorem idp0000000000000100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010010111.list =
    C ((2:ℤ)^20) * horner X vp0000000000000100101111.list + horner X ep0000000000000100101111.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100101111 : Branch 1 (-1405931/15625 : ℚ) vp000000000000010010111 := by
  apply branch_checked idp0000000000000100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1405931/15625 : ℚ) - ((1:ℤ):ℚ) = (-2827487/15625 : ℚ) by norm_num]
  exact coverp0000000000000100101111
theorem coverp000000000000010010111 : Covers (-1405931/15625 : ℚ) vp000000000000010010111 := join_branches bp0000000000000100101110 bp0000000000000100101111
private noncomputable def vp000000000000010010110_0 : Blocks := edgeBlocks% "full/vectors/000000000000010010110-V-0000.bin"
noncomputable def vp000000000000010010110 : Blocks := vp000000000000010010110_0
theorem coverp000000000000010010110 : Covers (-1390306/15625 : ℚ) vp000000000000010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001001011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001011-V-0000.bin"
noncomputable def vp00000000000001001011 : Blocks := vp00000000000001001011_0
private theorem bp000000000000010010110 : Branch 0 (-695153/15625 : ℚ) vp00000000000001001011 := by
  apply branch_left_normalized (c:=vp000000000000010010110) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-695153/15625 : ℚ) - ((0:ℤ):ℚ) = (-1390306/15625 : ℚ) by norm_num]
  exact coverp000000000000010010110
private noncomputable def ep000000000000010010111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010010111-E-0000.bin"
noncomputable def ep000000000000010010111 : Blocks := ep000000000000010010111_0
private theorem idp000000000000010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001001011.list =
    C ((2:ℤ)^27) * horner X vp000000000000010010111.list + horner X ep000000000000010010111.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010010111 : Branch 1 (-695153/15625 : ℚ) vp00000000000001001011 := by
  apply branch_checked idp000000000000010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-695153/15625 : ℚ) - ((1:ℤ):ℚ) = (-1405931/15625 : ℚ) by norm_num]
  exact coverp000000000000010010111
theorem coverp00000000000001001011 : Covers (-695153/15625 : ℚ) vp00000000000001001011 := join_branches bp000000000000010010110 bp000000000000010010111
private noncomputable def vp00000000000001001010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001010-V-0000.bin"
noncomputable def vp00000000000001001010 : Blocks := vp00000000000001001010_0
theorem coverp00000000000001001010 : Covers (-679528/15625 : ℚ) vp00000000000001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100101-V-0000.bin"
noncomputable def vp0000000000000100101 : Blocks := vp0000000000000100101_0
private theorem bp00000000000001001010 : Branch 0 (-339764/15625 : ℚ) vp0000000000000100101 := by
  apply branch_left_normalized (c:=vp00000000000001001010) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-339764/15625 : ℚ) - ((0:ℤ):ℚ) = (-679528/15625 : ℚ) by norm_num]
  exact coverp00000000000001001010
private noncomputable def ep00000000000001001011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001011-E-0000.bin"
noncomputable def ep00000000000001001011 : Blocks := ep00000000000001001011_0
private theorem idp00000000000001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000100101.list =
    C ((2:ℤ)^41) * horner X vp00000000000001001011.list + horner X ep00000000000001001011.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001001011 : Branch 1 (-339764/15625 : ℚ) vp0000000000000100101 := by
  apply branch_checked idp00000000000001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-339764/15625 : ℚ) - ((1:ℤ):ℚ) = (-695153/15625 : ℚ) by norm_num]
  exact coverp00000000000001001011
theorem coverp0000000000000100101 : Covers (-339764/15625 : ℚ) vp0000000000000100101 := join_branches bp00000000000001001010 bp00000000000001001011
private noncomputable def vp0000000000000100100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100100111-V-0000.bin"
noncomputable def vp0000000000000100100111 : Blocks := vp0000000000000100100111_0
theorem coverp0000000000000100100111 : Covers (-2702487/15625 : ℚ) vp0000000000000100100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100100110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100100110-V-0000.bin"
noncomputable def vp0000000000000100100110 : Blocks := vp0000000000000100100110_0
theorem coverp0000000000000100100110 : Covers (-2686862/15625 : ℚ) vp0000000000000100100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010010011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010010011-V-0000.bin"
noncomputable def vp000000000000010010011 : Blocks := vp000000000000010010011_0
private theorem bp0000000000000100100110 : Branch 0 (-1343431/15625 : ℚ) vp000000000000010010011 := by
  apply branch_left_normalized (c:=vp0000000000000100100110) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1343431/15625 : ℚ) - ((0:ℤ):ℚ) = (-2686862/15625 : ℚ) by norm_num]
  exact coverp0000000000000100100110
private noncomputable def ep0000000000000100100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100100111-E-0000.bin"
noncomputable def ep0000000000000100100111 : Blocks := ep0000000000000100100111_0
private theorem idp0000000000000100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010010011.list =
    C ((2:ℤ)^20) * horner X vp0000000000000100100111.list + horner X ep0000000000000100100111.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100100111 : Branch 1 (-1343431/15625 : ℚ) vp000000000000010010011 := by
  apply branch_checked idp0000000000000100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1343431/15625 : ℚ) - ((1:ℤ):ℚ) = (-2702487/15625 : ℚ) by norm_num]
  exact coverp0000000000000100100111
theorem coverp000000000000010010011 : Covers (-1343431/15625 : ℚ) vp000000000000010010011 := join_branches bp0000000000000100100110 bp0000000000000100100111
private noncomputable def vp000000000000010010010_0 : Blocks := edgeBlocks% "full/vectors/000000000000010010010-V-0000.bin"
noncomputable def vp000000000000010010010 : Blocks := vp000000000000010010010_0
theorem coverp000000000000010010010 : Covers (-1327806/15625 : ℚ) vp000000000000010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001001001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001001-V-0000.bin"
noncomputable def vp00000000000001001001 : Blocks := vp00000000000001001001_0
private theorem bp000000000000010010010 : Branch 0 (-663903/15625 : ℚ) vp00000000000001001001 := by
  apply branch_left_normalized (c:=vp000000000000010010010) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-663903/15625 : ℚ) - ((0:ℤ):ℚ) = (-1327806/15625 : ℚ) by norm_num]
  exact coverp000000000000010010010
private noncomputable def ep000000000000010010011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010010011-E-0000.bin"
noncomputable def ep000000000000010010011 : Blocks := ep000000000000010010011_0
private theorem idp000000000000010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001001001.list =
    C ((2:ℤ)^27) * horner X vp000000000000010010011.list + horner X ep000000000000010010011.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010010011 : Branch 1 (-663903/15625 : ℚ) vp00000000000001001001 := by
  apply branch_checked idp000000000000010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-663903/15625 : ℚ) - ((1:ℤ):ℚ) = (-1343431/15625 : ℚ) by norm_num]
  exact coverp000000000000010010011
theorem coverp00000000000001001001 : Covers (-663903/15625 : ℚ) vp00000000000001001001 := join_branches bp000000000000010010010 bp000000000000010010011
private noncomputable def vp00000000000001001000_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001000-V-0000.bin"
noncomputable def vp00000000000001001000 : Blocks := vp00000000000001001000_0
theorem coverp00000000000001001000 : Covers (-648278/15625 : ℚ) vp00000000000001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100100-V-0000.bin"
noncomputable def vp0000000000000100100 : Blocks := vp0000000000000100100_0
private theorem bp00000000000001001000 : Branch 0 (-324139/15625 : ℚ) vp0000000000000100100 := by
  apply branch_left_normalized (c:=vp00000000000001001000) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-324139/15625 : ℚ) - ((0:ℤ):ℚ) = (-648278/15625 : ℚ) by norm_num]
  exact coverp00000000000001001000
private noncomputable def ep00000000000001001001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001001-E-0000.bin"
noncomputable def ep00000000000001001001 : Blocks := ep00000000000001001001_0
private theorem idp00000000000001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000100100.list =
    C ((2:ℤ)^41) * horner X vp00000000000001001001.list + horner X ep00000000000001001001.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001001001 : Branch 1 (-324139/15625 : ℚ) vp0000000000000100100 := by
  apply branch_checked idp00000000000001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-324139/15625 : ℚ) - ((1:ℤ):ℚ) = (-663903/15625 : ℚ) by norm_num]
  exact coverp00000000000001001001
theorem coverp0000000000000100100 : Covers (-324139/15625 : ℚ) vp0000000000000100100 := join_branches bp00000000000001001000 bp00000000000001001001
private noncomputable def vp000000000000010010_0 : Blocks := edgeBlocks% "full/vectors/000000000000010010-V-0000.bin"
noncomputable def vp000000000000010010 : Blocks := vp000000000000010010_0
private theorem bp0000000000000100100 : Branch 0 (-324139/31250 : ℚ) vp000000000000010010 := by
  apply branch_left_normalized (c:=vp0000000000000100100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-324139/31250 : ℚ) - ((0:ℤ):ℚ) = (-324139/15625 : ℚ) by norm_num]
  exact coverp0000000000000100100
private noncomputable def ep0000000000000100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100101-E-0000.bin"
noncomputable def ep0000000000000100101 : Blocks := ep0000000000000100101_0
private theorem idp0000000000000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010010.list =
    C ((2:ℤ)^64) * horner X vp0000000000000100101.list + horner X ep0000000000000100101.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100101 : Branch 1 (-324139/31250 : ℚ) vp000000000000010010 := by
  apply branch_checked idp0000000000000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-324139/31250 : ℚ) - ((1:ℤ):ℚ) = (-339764/15625 : ℚ) by norm_num]
  exact coverp0000000000000100101
theorem coverp000000000000010010 : Covers (-324139/31250 : ℚ) vp000000000000010010 := join_branches bp0000000000000100100 bp0000000000000100101
private noncomputable def vp00000000000001001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001-V-0000.bin"
noncomputable def vp00000000000001001 : Blocks := vp00000000000001001_0
private theorem bp000000000000010010 : Branch 0 (-324139/62500 : ℚ) vp00000000000001001 := by
  apply branch_left_normalized (c:=vp000000000000010010) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-324139/62500 : ℚ) - ((0:ℤ):ℚ) = (-324139/31250 : ℚ) by norm_num]
  exact coverp000000000000010010
private noncomputable def ep000000000000010011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010011-E-0000.bin"
noncomputable def ep000000000000010011 : Blocks := ep000000000000010011_0
private theorem idp000000000000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001001.list =
    C ((2:ℤ)^106) * horner X vp000000000000010011.list + horner X ep000000000000010011.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010011 : Branch 1 (-324139/62500 : ℚ) vp00000000000001001 := by
  apply branch_checked idp000000000000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-324139/62500 : ℚ) - ((1:ℤ):ℚ) = (-355389/31250 : ℚ) by norm_num]
  exact coverp000000000000010011
theorem coverp00000000000001001 : Covers (-324139/62500 : ℚ) vp00000000000001001 := join_branches bp000000000000010010 bp000000000000010011
private noncomputable def vp0000000000000100011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100011111-V-0000.bin"
noncomputable def vp0000000000000100011111 : Blocks := vp0000000000000100011111_0
theorem coverp0000000000000100011111 : Covers (-2577487/15625 : ℚ) vp0000000000000100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100011110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100011110-V-0000.bin"
noncomputable def vp0000000000000100011110 : Blocks := vp0000000000000100011110_0
theorem coverp0000000000000100011110 : Covers (-2561862/15625 : ℚ) vp0000000000000100011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010001111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001111-V-0000.bin"
noncomputable def vp000000000000010001111 : Blocks := vp000000000000010001111_0
private theorem bp0000000000000100011110 : Branch 0 (-1280931/15625 : ℚ) vp000000000000010001111 := by
  apply branch_left_normalized (c:=vp0000000000000100011110) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-1280931/15625 : ℚ) - ((0:ℤ):ℚ) = (-2561862/15625 : ℚ) by norm_num]
  exact coverp0000000000000100011110
private noncomputable def ep0000000000000100011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100011111-E-0000.bin"
noncomputable def ep0000000000000100011111 : Blocks := ep0000000000000100011111_0
private theorem idp0000000000000100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010001111.list =
    C ((2:ℤ)^20) * horner X vp0000000000000100011111.list + horner X ep0000000000000100011111.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100011111 : Branch 1 (-1280931/15625 : ℚ) vp000000000000010001111 := by
  apply branch_checked idp0000000000000100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1280931/15625 : ℚ) - ((1:ℤ):ℚ) = (-2577487/15625 : ℚ) by norm_num]
  exact coverp0000000000000100011111
theorem coverp000000000000010001111 : Covers (-1280931/15625 : ℚ) vp000000000000010001111 := join_branches bp0000000000000100011110 bp0000000000000100011111
private noncomputable def vp0000000000000100011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100011101-V-0000.bin"
noncomputable def vp0000000000000100011101 : Blocks := vp0000000000000100011101_0
theorem coverp0000000000000100011101 : Covers (-2546237/15625 : ℚ) vp0000000000000100011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100011100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100011100-V-0000.bin"
noncomputable def vp0000000000000100011100 : Blocks := vp0000000000000100011100_0
theorem coverp0000000000000100011100 : Covers (-2530612/15625 : ℚ) vp0000000000000100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010001110_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001110-V-0000.bin"
noncomputable def vp000000000000010001110 : Blocks := vp000000000000010001110_0
private theorem bp0000000000000100011100 : Branch 0 (-1265306/15625 : ℚ) vp000000000000010001110 := by
  apply branch_left_normalized (c:=vp0000000000000100011100) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-1265306/15625 : ℚ) - ((0:ℤ):ℚ) = (-2530612/15625 : ℚ) by norm_num]
  exact coverp0000000000000100011100
private noncomputable def ep0000000000000100011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100011101-E-0000.bin"
noncomputable def ep0000000000000100011101 : Blocks := ep0000000000000100011101_0
private theorem idp0000000000000100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010001110.list =
    C ((2:ℤ)^19) * horner X vp0000000000000100011101.list + horner X ep0000000000000100011101.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100011101 : Branch 1 (-1265306/15625 : ℚ) vp000000000000010001110 := by
  apply branch_checked idp0000000000000100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1265306/15625 : ℚ) - ((1:ℤ):ℚ) = (-2546237/15625 : ℚ) by norm_num]
  exact coverp0000000000000100011101
theorem coverp000000000000010001110 : Covers (-1265306/15625 : ℚ) vp000000000000010001110 := join_branches bp0000000000000100011100 bp0000000000000100011101
private noncomputable def vp00000000000001000111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000111-V-0000.bin"
noncomputable def vp00000000000001000111 : Blocks := vp00000000000001000111_0
private theorem bp000000000000010001110 : Branch 0 (-632653/15625 : ℚ) vp00000000000001000111 := by
  apply branch_left_normalized (c:=vp000000000000010001110) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-632653/15625 : ℚ) - ((0:ℤ):ℚ) = (-1265306/15625 : ℚ) by norm_num]
  exact coverp000000000000010001110
private noncomputable def ep000000000000010001111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001111-E-0000.bin"
noncomputable def ep000000000000010001111 : Blocks := ep000000000000010001111_0
private theorem idp000000000000010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001000111.list =
    C ((2:ℤ)^28) * horner X vp000000000000010001111.list + horner X ep000000000000010001111.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010001111 : Branch 1 (-632653/15625 : ℚ) vp00000000000001000111 := by
  apply branch_checked idp000000000000010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-632653/15625 : ℚ) - ((1:ℤ):ℚ) = (-1280931/15625 : ℚ) by norm_num]
  exact coverp000000000000010001111
theorem coverp00000000000001000111 : Covers (-632653/15625 : ℚ) vp00000000000001000111 := join_branches bp000000000000010001110 bp000000000000010001111
private noncomputable def vp000000000000010001101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001101-V-0000.bin"
noncomputable def vp000000000000010001101 : Blocks := vp000000000000010001101_0
theorem coverp000000000000010001101 : Covers (-1249681/15625 : ℚ) vp000000000000010001101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010001100_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001100-V-0000.bin"
noncomputable def vp000000000000010001100 : Blocks := vp000000000000010001100_0
theorem coverp000000000000010001100 : Covers (-1234056/15625 : ℚ) vp000000000000010001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001000110_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000110-V-0000.bin"
noncomputable def vp00000000000001000110 : Blocks := vp00000000000001000110_0
private theorem bp000000000000010001100 : Branch 0 (-617028/15625 : ℚ) vp00000000000001000110 := by
  apply branch_left_normalized (c:=vp000000000000010001100) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-617028/15625 : ℚ) - ((0:ℤ):ℚ) = (-1234056/15625 : ℚ) by norm_num]
  exact coverp000000000000010001100
private noncomputable def ep000000000000010001101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001101-E-0000.bin"
noncomputable def ep000000000000010001101 : Blocks := ep000000000000010001101_0
private theorem idp000000000000010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001000110.list =
    C ((2:ℤ)^28) * horner X vp000000000000010001101.list + horner X ep000000000000010001101.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010001101 : Branch 1 (-617028/15625 : ℚ) vp00000000000001000110 := by
  apply branch_checked idp000000000000010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-617028/15625 : ℚ) - ((1:ℤ):ℚ) = (-1249681/15625 : ℚ) by norm_num]
  exact coverp000000000000010001101
theorem coverp00000000000001000110 : Covers (-617028/15625 : ℚ) vp00000000000001000110 := join_branches bp000000000000010001100 bp000000000000010001101
private noncomputable def vp0000000000000100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100011-V-0000.bin"
noncomputable def vp0000000000000100011 : Blocks := vp0000000000000100011_0
private theorem bp00000000000001000110 : Branch 0 (-308514/15625 : ℚ) vp0000000000000100011 := by
  apply branch_left_normalized (c:=vp00000000000001000110) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-308514/15625 : ℚ) - ((0:ℤ):ℚ) = (-617028/15625 : ℚ) by norm_num]
  exact coverp00000000000001000110
private noncomputable def ep00000000000001000111_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000111-E-0000.bin"
noncomputable def ep00000000000001000111 : Blocks := ep00000000000001000111_0
private theorem idp00000000000001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000100011.list =
    C ((2:ℤ)^41) * horner X vp00000000000001000111.list + horner X ep00000000000001000111.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001000111 : Branch 1 (-308514/15625 : ℚ) vp0000000000000100011 := by
  apply branch_checked idp00000000000001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-308514/15625 : ℚ) - ((1:ℤ):ℚ) = (-632653/15625 : ℚ) by norm_num]
  exact coverp00000000000001000111
theorem coverp0000000000000100011 : Covers (-308514/15625 : ℚ) vp0000000000000100011 := join_branches bp00000000000001000110 bp00000000000001000111
private noncomputable def vp0000000000000100010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100010111-V-0000.bin"
noncomputable def vp0000000000000100010111 : Blocks := vp0000000000000100010111_0
theorem coverp0000000000000100010111 : Covers (-2452487/15625 : ℚ) vp0000000000000100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100010110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100010110-V-0000.bin"
noncomputable def vp0000000000000100010110 : Blocks := vp0000000000000100010110_0
theorem coverp0000000000000100010110 : Covers (-2436862/15625 : ℚ) vp0000000000000100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010001011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001011-V-0000.bin"
noncomputable def vp000000000000010001011 : Blocks := vp000000000000010001011_0
private theorem bp0000000000000100010110 : Branch 0 (-1218431/15625 : ℚ) vp000000000000010001011 := by
  apply branch_left_normalized (c:=vp0000000000000100010110) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1218431/15625 : ℚ) - ((0:ℤ):ℚ) = (-2436862/15625 : ℚ) by norm_num]
  exact coverp0000000000000100010110
private noncomputable def ep0000000000000100010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100010111-E-0000.bin"
noncomputable def ep0000000000000100010111 : Blocks := ep0000000000000100010111_0
private theorem idp0000000000000100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010001011.list =
    C ((2:ℤ)^21) * horner X vp0000000000000100010111.list + horner X ep0000000000000100010111.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100010111 : Branch 1 (-1218431/15625 : ℚ) vp000000000000010001011 := by
  apply branch_checked idp0000000000000100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1218431/15625 : ℚ) - ((1:ℤ):ℚ) = (-2452487/15625 : ℚ) by norm_num]
  exact coverp0000000000000100010111
theorem coverp000000000000010001011 : Covers (-1218431/15625 : ℚ) vp000000000000010001011 := join_branches bp0000000000000100010110 bp0000000000000100010111
private noncomputable def vp0000000000000100010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100010101-V-0000.bin"
noncomputable def vp0000000000000100010101 : Blocks := vp0000000000000100010101_0
theorem coverp0000000000000100010101 : Covers (-2421237/15625 : ℚ) vp0000000000000100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100010100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100010100-V-0000.bin"
noncomputable def vp0000000000000100010100 : Blocks := vp0000000000000100010100_0
theorem coverp0000000000000100010100 : Covers (-2405612/15625 : ℚ) vp0000000000000100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010001010_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001010-V-0000.bin"
noncomputable def vp000000000000010001010 : Blocks := vp000000000000010001010_0
private theorem bp0000000000000100010100 : Branch 0 (-1202806/15625 : ℚ) vp000000000000010001010 := by
  apply branch_left_normalized (c:=vp0000000000000100010100) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1202806/15625 : ℚ) - ((0:ℤ):ℚ) = (-2405612/15625 : ℚ) by norm_num]
  exact coverp0000000000000100010100
private noncomputable def ep0000000000000100010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100010101-E-0000.bin"
noncomputable def ep0000000000000100010101 : Blocks := ep0000000000000100010101_0
private theorem idp0000000000000100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010001010.list =
    C ((2:ℤ)^20) * horner X vp0000000000000100010101.list + horner X ep0000000000000100010101.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100010101 : Branch 1 (-1202806/15625 : ℚ) vp000000000000010001010 := by
  apply branch_checked idp0000000000000100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1202806/15625 : ℚ) - ((1:ℤ):ℚ) = (-2421237/15625 : ℚ) by norm_num]
  exact coverp0000000000000100010101
theorem coverp000000000000010001010 : Covers (-1202806/15625 : ℚ) vp000000000000010001010 := join_branches bp0000000000000100010100 bp0000000000000100010101
private noncomputable def vp00000000000001000101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000101-V-0000.bin"
noncomputable def vp00000000000001000101 : Blocks := vp00000000000001000101_0
private theorem bp000000000000010001010 : Branch 0 (-601403/15625 : ℚ) vp00000000000001000101 := by
  apply branch_left_normalized (c:=vp000000000000010001010) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-601403/15625 : ℚ) - ((0:ℤ):ℚ) = (-1202806/15625 : ℚ) by norm_num]
  exact coverp000000000000010001010
private noncomputable def ep000000000000010001011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001011-E-0000.bin"
noncomputable def ep000000000000010001011 : Blocks := ep000000000000010001011_0
private theorem idp000000000000010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001000101.list =
    C ((2:ℤ)^28) * horner X vp000000000000010001011.list + horner X ep000000000000010001011.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010001011 : Branch 1 (-601403/15625 : ℚ) vp00000000000001000101 := by
  apply branch_checked idp000000000000010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-601403/15625 : ℚ) - ((1:ℤ):ℚ) = (-1218431/15625 : ℚ) by norm_num]
  exact coverp000000000000010001011
theorem coverp00000000000001000101 : Covers (-601403/15625 : ℚ) vp00000000000001000101 := join_branches bp000000000000010001010 bp000000000000010001011
private noncomputable def vp000000000000010001001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001001-V-0000.bin"
noncomputable def vp000000000000010001001 : Blocks := vp000000000000010001001_0
theorem coverp000000000000010001001 : Covers (-1187181/15625 : ℚ) vp000000000000010001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010001000_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001000-V-0000.bin"
noncomputable def vp000000000000010001000 : Blocks := vp000000000000010001000_0
theorem coverp000000000000010001000 : Covers (-1171556/15625 : ℚ) vp000000000000010001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001000100_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000100-V-0000.bin"
noncomputable def vp00000000000001000100 : Blocks := vp00000000000001000100_0
private theorem bp000000000000010001000 : Branch 0 (-585778/15625 : ℚ) vp00000000000001000100 := by
  apply branch_left_normalized (c:=vp000000000000010001000) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-585778/15625 : ℚ) - ((0:ℤ):ℚ) = (-1171556/15625 : ℚ) by norm_num]
  exact coverp000000000000010001000
private noncomputable def ep000000000000010001001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001001-E-0000.bin"
noncomputable def ep000000000000010001001 : Blocks := ep000000000000010001001_0
private theorem idp000000000000010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001000100.list =
    C ((2:ℤ)^28) * horner X vp000000000000010001001.list + horner X ep000000000000010001001.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010001001 : Branch 1 (-585778/15625 : ℚ) vp00000000000001000100 := by
  apply branch_checked idp000000000000010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-585778/15625 : ℚ) - ((1:ℤ):ℚ) = (-1187181/15625 : ℚ) by norm_num]
  exact coverp000000000000010001001
theorem coverp00000000000001000100 : Covers (-585778/15625 : ℚ) vp00000000000001000100 := join_branches bp000000000000010001000 bp000000000000010001001
private noncomputable def vp0000000000000100010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100010-V-0000.bin"
noncomputable def vp0000000000000100010 : Blocks := vp0000000000000100010_0
private theorem bp00000000000001000100 : Branch 0 (-292889/15625 : ℚ) vp0000000000000100010 := by
  apply branch_left_normalized (c:=vp00000000000001000100) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-292889/15625 : ℚ) - ((0:ℤ):ℚ) = (-585778/15625 : ℚ) by norm_num]
  exact coverp00000000000001000100
private noncomputable def ep00000000000001000101_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000101-E-0000.bin"
noncomputable def ep00000000000001000101 : Blocks := ep00000000000001000101_0
private theorem idp00000000000001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000100010.list =
    C ((2:ℤ)^41) * horner X vp00000000000001000101.list + horner X ep00000000000001000101.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001000101 : Branch 1 (-292889/15625 : ℚ) vp0000000000000100010 := by
  apply branch_checked idp00000000000001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-292889/15625 : ℚ) - ((1:ℤ):ℚ) = (-601403/15625 : ℚ) by norm_num]
  exact coverp00000000000001000101
theorem coverp0000000000000100010 : Covers (-292889/15625 : ℚ) vp0000000000000100010 := join_branches bp00000000000001000100 bp00000000000001000101
private noncomputable def vp000000000000010001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001-V-0000.bin"
noncomputable def vp000000000000010001 : Blocks := vp000000000000010001_0
private theorem bp0000000000000100010 : Branch 0 (-292889/31250 : ℚ) vp000000000000010001 := by
  apply branch_left_normalized (c:=vp0000000000000100010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-292889/31250 : ℚ) - ((0:ℤ):ℚ) = (-292889/15625 : ℚ) by norm_num]
  exact coverp0000000000000100010
private noncomputable def ep0000000000000100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100011-E-0000.bin"
noncomputable def ep0000000000000100011 : Blocks := ep0000000000000100011_0
private theorem idp0000000000000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010001.list =
    C ((2:ℤ)^64) * horner X vp0000000000000100011.list + horner X ep0000000000000100011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100011 : Branch 1 (-292889/31250 : ℚ) vp000000000000010001 := by
  apply branch_checked idp0000000000000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-292889/31250 : ℚ) - ((1:ℤ):ℚ) = (-308514/15625 : ℚ) by norm_num]
  exact coverp0000000000000100011
theorem coverp000000000000010001 : Covers (-292889/31250 : ℚ) vp000000000000010001 := join_branches bp0000000000000100010 bp0000000000000100011
private noncomputable def vp0000000000000100001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100001111-V-0000.bin"
noncomputable def vp0000000000000100001111 : Blocks := vp0000000000000100001111_0
theorem coverp0000000000000100001111 : Covers (-2327487/15625 : ℚ) vp0000000000000100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100001110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100001110-V-0000.bin"
noncomputable def vp0000000000000100001110 : Blocks := vp0000000000000100001110_0
theorem coverp0000000000000100001110 : Covers (-2311862/15625 : ℚ) vp0000000000000100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010000111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000111-V-0000.bin"
noncomputable def vp000000000000010000111 : Blocks := vp000000000000010000111_0
private theorem bp0000000000000100001110 : Branch 0 (-1155931/15625 : ℚ) vp000000000000010000111 := by
  apply branch_left_normalized (c:=vp0000000000000100001110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-1155931/15625 : ℚ) - ((0:ℤ):ℚ) = (-2311862/15625 : ℚ) by norm_num]
  exact coverp0000000000000100001110
private noncomputable def ep0000000000000100001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100001111-E-0000.bin"
noncomputable def ep0000000000000100001111 : Blocks := ep0000000000000100001111_0
private theorem idp0000000000000100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010000111.list =
    C ((2:ℤ)^21) * horner X vp0000000000000100001111.list + horner X ep0000000000000100001111.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100001111 : Branch 1 (-1155931/15625 : ℚ) vp000000000000010000111 := by
  apply branch_checked idp0000000000000100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1155931/15625 : ℚ) - ((1:ℤ):ℚ) = (-2327487/15625 : ℚ) by norm_num]
  exact coverp0000000000000100001111
theorem coverp000000000000010000111 : Covers (-1155931/15625 : ℚ) vp000000000000010000111 := join_branches bp0000000000000100001110 bp0000000000000100001111
private noncomputable def vp0000000000000100001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100001101-V-0000.bin"
noncomputable def vp0000000000000100001101 : Blocks := vp0000000000000100001101_0
theorem coverp0000000000000100001101 : Covers (-2296237/15625 : ℚ) vp0000000000000100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100001100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100001100-V-0000.bin"
noncomputable def vp0000000000000100001100 : Blocks := vp0000000000000100001100_0
theorem coverp0000000000000100001100 : Covers (-2280612/15625 : ℚ) vp0000000000000100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010000110_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000110-V-0000.bin"
noncomputable def vp000000000000010000110 : Blocks := vp000000000000010000110_0
private theorem bp0000000000000100001100 : Branch 0 (-1140306/15625 : ℚ) vp000000000000010000110 := by
  apply branch_left_normalized (c:=vp0000000000000100001100) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1140306/15625 : ℚ) - ((0:ℤ):ℚ) = (-2280612/15625 : ℚ) by norm_num]
  exact coverp0000000000000100001100
private noncomputable def ep0000000000000100001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100001101-E-0000.bin"
noncomputable def ep0000000000000100001101 : Blocks := ep0000000000000100001101_0
private theorem idp0000000000000100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010000110.list =
    C ((2:ℤ)^20) * horner X vp0000000000000100001101.list + horner X ep0000000000000100001101.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100001101 : Branch 1 (-1140306/15625 : ℚ) vp000000000000010000110 := by
  apply branch_checked idp0000000000000100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1140306/15625 : ℚ) - ((1:ℤ):ℚ) = (-2296237/15625 : ℚ) by norm_num]
  exact coverp0000000000000100001101
theorem coverp000000000000010000110 : Covers (-1140306/15625 : ℚ) vp000000000000010000110 := join_branches bp0000000000000100001100 bp0000000000000100001101
private noncomputable def vp00000000000001000011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000011-V-0000.bin"
noncomputable def vp00000000000001000011 : Blocks := vp00000000000001000011_0
private theorem bp000000000000010000110 : Branch 0 (-570153/15625 : ℚ) vp00000000000001000011 := by
  apply branch_left_normalized (c:=vp000000000000010000110) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-570153/15625 : ℚ) - ((0:ℤ):ℚ) = (-1140306/15625 : ℚ) by norm_num]
  exact coverp000000000000010000110
private noncomputable def ep000000000000010000111_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000111-E-0000.bin"
noncomputable def ep000000000000010000111 : Blocks := ep000000000000010000111_0
private theorem idp000000000000010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001000011.list =
    C ((2:ℤ)^28) * horner X vp000000000000010000111.list + horner X ep000000000000010000111.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010000111 : Branch 1 (-570153/15625 : ℚ) vp00000000000001000011 := by
  apply branch_checked idp000000000000010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-570153/15625 : ℚ) - ((1:ℤ):ℚ) = (-1155931/15625 : ℚ) by norm_num]
  exact coverp000000000000010000111
theorem coverp00000000000001000011 : Covers (-570153/15625 : ℚ) vp00000000000001000011 := join_branches bp000000000000010000110 bp000000000000010000111
private noncomputable def vp000000000000010000101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000101-V-0000.bin"
noncomputable def vp000000000000010000101 : Blocks := vp000000000000010000101_0
theorem coverp000000000000010000101 : Covers (-1124681/15625 : ℚ) vp000000000000010000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010000100_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000100-V-0000.bin"
noncomputable def vp000000000000010000100 : Blocks := vp000000000000010000100_0
theorem coverp000000000000010000100 : Covers (-1109056/15625 : ℚ) vp000000000000010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001000010_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000010-V-0000.bin"
noncomputable def vp00000000000001000010 : Blocks := vp00000000000001000010_0
private theorem bp000000000000010000100 : Branch 0 (-554528/15625 : ℚ) vp00000000000001000010 := by
  apply branch_left_normalized (c:=vp000000000000010000100) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-554528/15625 : ℚ) - ((0:ℤ):ℚ) = (-1109056/15625 : ℚ) by norm_num]
  exact coverp000000000000010000100
private noncomputable def ep000000000000010000101_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000101-E-0000.bin"
noncomputable def ep000000000000010000101 : Blocks := ep000000000000010000101_0
private theorem idp000000000000010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001000010.list =
    C ((2:ℤ)^29) * horner X vp000000000000010000101.list + horner X ep000000000000010000101.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010000101 : Branch 1 (-554528/15625 : ℚ) vp00000000000001000010 := by
  apply branch_checked idp000000000000010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-554528/15625 : ℚ) - ((1:ℤ):ℚ) = (-1124681/15625 : ℚ) by norm_num]
  exact coverp000000000000010000101
theorem coverp00000000000001000010 : Covers (-554528/15625 : ℚ) vp00000000000001000010 := join_branches bp000000000000010000100 bp000000000000010000101
private noncomputable def vp0000000000000100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100001-V-0000.bin"
noncomputable def vp0000000000000100001 : Blocks := vp0000000000000100001_0
private theorem bp00000000000001000010 : Branch 0 (-277264/15625 : ℚ) vp0000000000000100001 := by
  apply branch_left_normalized (c:=vp00000000000001000010) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-277264/15625 : ℚ) - ((0:ℤ):ℚ) = (-554528/15625 : ℚ) by norm_num]
  exact coverp00000000000001000010
private noncomputable def ep00000000000001000011_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000011-E-0000.bin"
noncomputable def ep00000000000001000011 : Blocks := ep00000000000001000011_0
private theorem idp00000000000001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000100001.list =
    C ((2:ℤ)^42) * horner X vp00000000000001000011.list + horner X ep00000000000001000011.list := by
  exact edge_identity (B := (2:ℤ)^141) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001000011 : Branch 1 (-277264/15625 : ℚ) vp0000000000000100001 := by
  apply branch_checked idp00000000000001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-277264/15625 : ℚ) - ((1:ℤ):ℚ) = (-570153/15625 : ℚ) by norm_num]
  exact coverp00000000000001000011
theorem coverp0000000000000100001 : Covers (-277264/15625 : ℚ) vp0000000000000100001 := join_branches bp00000000000001000010 bp00000000000001000011
private noncomputable def vp0000000000000100000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100000111-V-0000.bin"
noncomputable def vp0000000000000100000111 : Blocks := vp0000000000000100000111_0
theorem coverp0000000000000100000111 : Covers (-2202487/15625 : ℚ) vp0000000000000100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100000110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100000110-V-0000.bin"
noncomputable def vp0000000000000100000110 : Blocks := vp0000000000000100000110_0
theorem coverp0000000000000100000110 : Covers (-2186862/15625 : ℚ) vp0000000000000100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010000011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000011-V-0000.bin"
noncomputable def vp000000000000010000011 : Blocks := vp000000000000010000011_0
private theorem bp0000000000000100000110 : Branch 0 (-1093431/15625 : ℚ) vp000000000000010000011 := by
  apply branch_left_normalized (c:=vp0000000000000100000110) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1093431/15625 : ℚ) - ((0:ℤ):ℚ) = (-2186862/15625 : ℚ) by norm_num]
  exact coverp0000000000000100000110
private noncomputable def ep0000000000000100000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100000111-E-0000.bin"
noncomputable def ep0000000000000100000111 : Blocks := ep0000000000000100000111_0
private theorem idp0000000000000100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010000011.list =
    C ((2:ℤ)^21) * horner X vp0000000000000100000111.list + horner X ep0000000000000100000111.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100000111 : Branch 1 (-1093431/15625 : ℚ) vp000000000000010000011 := by
  apply branch_checked idp0000000000000100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1093431/15625 : ℚ) - ((1:ℤ):ℚ) = (-2202487/15625 : ℚ) by norm_num]
  exact coverp0000000000000100000111
theorem coverp000000000000010000011 : Covers (-1093431/15625 : ℚ) vp000000000000010000011 := join_branches bp0000000000000100000110 bp0000000000000100000111
private noncomputable def vp0000000000000100000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100000101-V-0000.bin"
noncomputable def vp0000000000000100000101 : Blocks := vp0000000000000100000101_0
theorem coverp0000000000000100000101 : Covers (-2171237/15625 : ℚ) vp0000000000000100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000100000100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100000100-V-0000.bin"
noncomputable def vp0000000000000100000100 : Blocks := vp0000000000000100000100_0
theorem coverp0000000000000100000100 : Covers (-2155612/15625 : ℚ) vp0000000000000100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010000010_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000010-V-0000.bin"
noncomputable def vp000000000000010000010 : Blocks := vp000000000000010000010_0
private theorem bp0000000000000100000100 : Branch 0 (-1077806/15625 : ℚ) vp000000000000010000010 := by
  apply branch_left_normalized (c:=vp0000000000000100000100) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-1077806/15625 : ℚ) - ((0:ℤ):ℚ) = (-2155612/15625 : ℚ) by norm_num]
  exact coverp0000000000000100000100
private noncomputable def ep0000000000000100000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100000101-E-0000.bin"
noncomputable def ep0000000000000100000101 : Blocks := ep0000000000000100000101_0
private theorem idp0000000000000100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010000010.list =
    C ((2:ℤ)^21) * horner X vp0000000000000100000101.list + horner X ep0000000000000100000101.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100000101 : Branch 1 (-1077806/15625 : ℚ) vp000000000000010000010 := by
  apply branch_checked idp0000000000000100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1077806/15625 : ℚ) - ((1:ℤ):ℚ) = (-2171237/15625 : ℚ) by norm_num]
  exact coverp0000000000000100000101
theorem coverp000000000000010000010 : Covers (-1077806/15625 : ℚ) vp000000000000010000010 := join_branches bp0000000000000100000100 bp0000000000000100000101
private noncomputable def vp00000000000001000001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000001-V-0000.bin"
noncomputable def vp00000000000001000001 : Blocks := vp00000000000001000001_0
private theorem bp000000000000010000010 : Branch 0 (-538903/15625 : ℚ) vp00000000000001000001 := by
  apply branch_left_normalized (c:=vp000000000000010000010) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-538903/15625 : ℚ) - ((0:ℤ):ℚ) = (-1077806/15625 : ℚ) by norm_num]
  exact coverp000000000000010000010
private noncomputable def ep000000000000010000011_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000011-E-0000.bin"
noncomputable def ep000000000000010000011 : Blocks := ep000000000000010000011_0
private theorem idp000000000000010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001000001.list =
    C ((2:ℤ)^28) * horner X vp000000000000010000011.list + horner X ep000000000000010000011.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010000011 : Branch 1 (-538903/15625 : ℚ) vp00000000000001000001 := by
  apply branch_checked idp000000000000010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-538903/15625 : ℚ) - ((1:ℤ):ℚ) = (-1093431/15625 : ℚ) by norm_num]
  exact coverp000000000000010000011
theorem coverp00000000000001000001 : Covers (-538903/15625 : ℚ) vp00000000000001000001 := join_branches bp000000000000010000010 bp000000000000010000011
private noncomputable def vp000000000000010000001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000001-V-0000.bin"
noncomputable def vp000000000000010000001 : Blocks := vp000000000000010000001_0
theorem coverp000000000000010000001 : Covers (-1062181/15625 : ℚ) vp000000000000010000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000010000000_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000000-V-0000.bin"
noncomputable def vp000000000000010000000 : Blocks := vp000000000000010000000_0
theorem coverp000000000000010000000 : Covers (-1046556/15625 : ℚ) vp000000000000010000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000001000000_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000000-V-0000.bin"
noncomputable def vp00000000000001000000 : Blocks := vp00000000000001000000_0
private theorem bp000000000000010000000 : Branch 0 (-523278/15625 : ℚ) vp00000000000001000000 := by
  apply branch_left_normalized (c:=vp000000000000010000000) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-523278/15625 : ℚ) - ((0:ℤ):ℚ) = (-1046556/15625 : ℚ) by norm_num]
  exact coverp000000000000010000000
private noncomputable def ep000000000000010000001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000001-E-0000.bin"
noncomputable def ep000000000000010000001 : Blocks := ep000000000000010000001_0
private theorem idp000000000000010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001000000.list =
    C ((2:ℤ)^28) * horner X vp000000000000010000001.list + horner X ep000000000000010000001.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010000001 : Branch 1 (-523278/15625 : ℚ) vp00000000000001000000 := by
  apply branch_checked idp000000000000010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-523278/15625 : ℚ) - ((1:ℤ):ℚ) = (-1062181/15625 : ℚ) by norm_num]
  exact coverp000000000000010000001
theorem coverp00000000000001000000 : Covers (-523278/15625 : ℚ) vp00000000000001000000 := join_branches bp000000000000010000000 bp000000000000010000001
private noncomputable def vp0000000000000100000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100000-V-0000.bin"
noncomputable def vp0000000000000100000 : Blocks := vp0000000000000100000_0
private theorem bp00000000000001000000 : Branch 0 (-261639/15625 : ℚ) vp0000000000000100000 := by
  apply branch_left_normalized (c:=vp00000000000001000000) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-261639/15625 : ℚ) - ((0:ℤ):ℚ) = (-523278/15625 : ℚ) by norm_num]
  exact coverp00000000000001000000
private noncomputable def ep00000000000001000001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000001-E-0000.bin"
noncomputable def ep00000000000001000001 : Blocks := ep00000000000001000001_0
private theorem idp00000000000001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000100000.list =
    C ((2:ℤ)^41) * horner X vp00000000000001000001.list + horner X ep00000000000001000001.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001000001 : Branch 1 (-261639/15625 : ℚ) vp0000000000000100000 := by
  apply branch_checked idp00000000000001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-261639/15625 : ℚ) - ((1:ℤ):ℚ) = (-538903/15625 : ℚ) by norm_num]
  exact coverp00000000000001000001
theorem coverp0000000000000100000 : Covers (-261639/15625 : ℚ) vp0000000000000100000 := join_branches bp00000000000001000000 bp00000000000001000001
private noncomputable def vp000000000000010000_0 : Blocks := edgeBlocks% "full/vectors/000000000000010000-V-0000.bin"
noncomputable def vp000000000000010000 : Blocks := vp000000000000010000_0
private theorem bp0000000000000100000 : Branch 0 (-261639/31250 : ℚ) vp000000000000010000 := by
  apply branch_left_normalized (c:=vp0000000000000100000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-261639/31250 : ℚ) - ((0:ℤ):ℚ) = (-261639/15625 : ℚ) by norm_num]
  exact coverp0000000000000100000
private noncomputable def ep0000000000000100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100001-E-0000.bin"
noncomputable def ep0000000000000100001 : Blocks := ep0000000000000100001_0
private theorem idp0000000000000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010000.list =
    C ((2:ℤ)^66) * horner X vp0000000000000100001.list + horner X ep0000000000000100001.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000100001 : Branch 1 (-261639/31250 : ℚ) vp000000000000010000 := by
  apply branch_checked idp0000000000000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-261639/31250 : ℚ) - ((1:ℤ):ℚ) = (-277264/15625 : ℚ) by norm_num]
  exact coverp0000000000000100001
theorem coverp000000000000010000 : Covers (-261639/31250 : ℚ) vp000000000000010000 := join_branches bp0000000000000100000 bp0000000000000100001
private noncomputable def vp00000000000001000_0 : Blocks := edgeBlocks% "full/vectors/00000000000001000-V-0000.bin"
noncomputable def vp00000000000001000 : Blocks := vp00000000000001000_0
private theorem bp000000000000010000 : Branch 0 (-261639/62500 : ℚ) vp00000000000001000 := by
  apply branch_left_normalized (c:=vp000000000000010000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-261639/62500 : ℚ) - ((0:ℤ):ℚ) = (-261639/31250 : ℚ) by norm_num]
  exact coverp000000000000010000
private noncomputable def ep000000000000010001_0 : Blocks := edgeBlocks% "full/vectors/000000000000010001-E-0000.bin"
noncomputable def ep000000000000010001 : Blocks := ep000000000000010001_0
private theorem idp000000000000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001000.list =
    C ((2:ℤ)^111) * horner X vp000000000000010001.list + horner X ep000000000000010001.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000010001 : Branch 1 (-261639/62500 : ℚ) vp00000000000001000 := by
  apply branch_checked idp000000000000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-261639/62500 : ℚ) - ((1:ℤ):ℚ) = (-292889/31250 : ℚ) by norm_num]
  exact coverp000000000000010001
theorem coverp00000000000001000 : Covers (-261639/62500 : ℚ) vp00000000000001000 := join_branches bp000000000000010000 bp000000000000010001
private noncomputable def vp0000000000000100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000100-V-0000.bin"
private noncomputable def vp0000000000000100_1 : Blocks := edgeBlocks% "full/vectors/0000000000000100-V-0001.bin"
noncomputable def vp0000000000000100 : Blocks := (Blocks.join vp0000000000000100_0 vp0000000000000100_1)
private theorem bp00000000000001000 : Branch 0 (-261639/125000 : ℚ) vp0000000000000100 := by
  apply branch_left_normalized (c:=vp00000000000001000) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-261639/62500 : ℚ) by norm_num]
  exact coverp00000000000001000
private noncomputable def ep00000000000001001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001001-E-0000.bin"
private noncomputable def ep00000000000001001_1 : Blocks := edgeBlocks% "full/vectors/00000000000001001-E-0001.bin"
noncomputable def ep00000000000001001 : Blocks := (Blocks.join ep00000000000001001_0 ep00000000000001001_1)
private theorem idp00000000000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000100.list =
    C ((2:ℤ)^198) * horner X vp00000000000001001.list + horner X ep00000000000001001.list := by
  exact edge_identity (B := (2:ℤ)^375) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000001001 : Branch 1 (-261639/125000 : ℚ) vp0000000000000100 := by
  apply branch_checked idp00000000000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-324139/62500 : ℚ) by norm_num]
  exact coverp00000000000001001
theorem coverp0000000000000100 : Covers (-261639/125000 : ℚ) vp0000000000000100 := join_branches bp00000000000001000 bp00000000000001001
private noncomputable def vp000000000000010_0 : Blocks := edgeBlocks% "full/vectors/000000000000010-V-0000.bin"
private noncomputable def vp000000000000010_1 : Blocks := edgeBlocks% "full/vectors/000000000000010-V-0001.bin"
private noncomputable def vp000000000000010_2 : Blocks := edgeBlocks% "full/vectors/000000000000010-V-0002.bin"
noncomputable def vp000000000000010 : Blocks := (Blocks.join vp000000000000010_0 (Blocks.join vp000000000000010_1 vp000000000000010_2))
private theorem bp0000000000000100 : Branch 0 (-261639/250000 : ℚ) vp000000000000010 := by
  apply branch_left_normalized (c:=vp0000000000000100) (k:=0) (m:=197) (by decide +kernel)
  rw [show 2*(-261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-261639/125000 : ℚ) by norm_num]
  exact coverp0000000000000100
private noncomputable def ep0000000000000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000101-E-0000.bin"
private noncomputable def ep0000000000000101_1 : Blocks := edgeBlocks% "full/vectors/0000000000000101-E-0001.bin"
private noncomputable def ep0000000000000101_2 : Blocks := edgeBlocks% "full/vectors/0000000000000101-E-0002.bin"
noncomputable def ep0000000000000101 : Blocks := (Blocks.join ep0000000000000101_0 (Blocks.join ep0000000000000101_1 ep0000000000000101_2))
private theorem idp0000000000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000010.list =
    C ((2:ℤ)^371) * horner X vp0000000000000101.list + horner X ep0000000000000101.list := by
  exact edge_identity (B := (2:ℤ)^640) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000101 : Branch 1 (-261639/250000 : ℚ) vp000000000000010 := by
  apply branch_checked idp0000000000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-386639/125000 : ℚ) by norm_num]
  exact coverp0000000000000101
theorem coverp000000000000010 : Covers (-261639/250000 : ℚ) vp000000000000010 := join_branches bp0000000000000100 bp0000000000000101
private noncomputable def vp00000000000001_0 : Blocks := edgeBlocks% "full/vectors/00000000000001-V-0000.bin"
private noncomputable def vp00000000000001_1 : Blocks := edgeBlocks% "full/vectors/00000000000001-V-0001.bin"
private noncomputable def vp00000000000001_2 : Blocks := edgeBlocks% "full/vectors/00000000000001-V-0002.bin"
private noncomputable def vp00000000000001_3 : Blocks := edgeBlocks% "full/vectors/00000000000001-V-0003.bin"
private noncomputable def vp00000000000001_4 : Blocks := edgeBlocks% "full/vectors/00000000000001-V-0004.bin"
private noncomputable def vp00000000000001_5 : Blocks := edgeBlocks% "full/vectors/00000000000001-V-0005.bin"
noncomputable def vp00000000000001 : Blocks := (Blocks.join (Blocks.join vp00000000000001_0 (Blocks.join vp00000000000001_1 vp00000000000001_2)) (Blocks.join vp00000000000001_3 (Blocks.join vp00000000000001_4 vp00000000000001_5)))
private theorem bp000000000000010 : Branch 0 (-261639/500000 : ℚ) vp00000000000001 := by
  apply branch_left_normalized (c:=vp000000000000010) (k:=0) (m:=370) (by decide +kernel)
  rw [show 2*(-261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-261639/250000 : ℚ) by norm_num]
  exact coverp000000000000010
private noncomputable def ep000000000000011_0 : Blocks := edgeBlocks% "full/vectors/000000000000011-E-0000.bin"
private noncomputable def ep000000000000011_1 : Blocks := edgeBlocks% "full/vectors/000000000000011-E-0001.bin"
private noncomputable def ep000000000000011_2 : Blocks := edgeBlocks% "full/vectors/000000000000011-E-0002.bin"
private noncomputable def ep000000000000011_3 : Blocks := edgeBlocks% "full/vectors/000000000000011-E-0003.bin"
private noncomputable def ep000000000000011_4 : Blocks := edgeBlocks% "full/vectors/000000000000011-E-0004.bin"
private noncomputable def ep000000000000011_5 : Blocks := edgeBlocks% "full/vectors/000000000000011-E-0005.bin"
noncomputable def ep000000000000011 : Blocks := (Blocks.join (Blocks.join ep000000000000011_0 (Blocks.join ep000000000000011_1 ep000000000000011_2)) (Blocks.join ep000000000000011_3 (Blocks.join ep000000000000011_4 ep000000000000011_5)))
private theorem idp000000000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000001.list =
    C ((2:ℤ)^646) * horner X vp000000000000011.list + horner X ep000000000000011.list := by
  exact edge_identity (B := (2:ℤ)^1099) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000011 : Branch 1 (-261639/500000 : ℚ) vp00000000000001 := by
  apply branch_checked idp000000000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-511639/250000 : ℚ) by norm_num]
  exact coverp000000000000011
theorem coverp00000000000001 : Covers (-261639/500000 : ℚ) vp00000000000001 := join_branches bp000000000000010 bp000000000000011
end NextProof.EdgeFull

