import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00017

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000000001011111111_0 : Blocks := edgeBlocks% "full/vectors/0000000001011111111-V-0000.bin"
noncomputable def vp0000000001011111111 : Blocks := vp0000000001011111111_0
theorem coverp0000000001011111111 : Covers (-11746014/15625 : ℚ) vp0000000001011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001011111110_0 : Blocks := edgeBlocks% "full/vectors/0000000001011111110-V-0000.bin"
noncomputable def vp0000000001011111110 : Blocks := vp0000000001011111110_0
theorem coverp0000000001011111110 : Covers (-11730389/15625 : ℚ) vp0000000001011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000101111111_0 : Blocks := edgeBlocks% "full/vectors/000000000101111111-V-0000.bin"
noncomputable def vp000000000101111111 : Blocks := vp000000000101111111_0
private theorem bp0000000001011111110 : Branch 0 (-11730389/31250 : ℚ) vp000000000101111111 := by
  apply branch_left_normalized (c:=vp0000000001011111110) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-11730389/31250 : ℚ) - ((0:ℤ):ℚ) = (-11730389/15625 : ℚ) by norm_num]
  exact coverp0000000001011111110
private noncomputable def ep0000000001011111111_0 : Blocks := edgeBlocks% "full/vectors/0000000001011111111-E-0000.bin"
noncomputable def ep0000000001011111111 : Blocks := ep0000000001011111111_0
private theorem idp0000000001011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000101111111.list =
    C ((2:ℤ)^24) * horner X vp0000000001011111111.list + horner X ep0000000001011111111.list := by
  exact edge_identity (B := (2:ℤ)^133) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001011111111 : Branch 1 (-11730389/31250 : ℚ) vp000000000101111111 := by
  apply branch_checked idp0000000001011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-11730389/31250 : ℚ) - ((1:ℤ):ℚ) = (-11746014/15625 : ℚ) by norm_num]
  exact coverp0000000001011111111
theorem coverp000000000101111111 : Covers (-11730389/31250 : ℚ) vp000000000101111111 := join_branches bp0000000001011111110 bp0000000001011111111
private noncomputable def vp000000000101111110_0 : Blocks := edgeBlocks% "full/vectors/000000000101111110-V-0000.bin"
noncomputable def vp000000000101111110 : Blocks := vp000000000101111110_0
theorem coverp000000000101111110 : Covers (-11699139/31250 : ℚ) vp000000000101111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000010111111_0 : Blocks := edgeBlocks% "full/vectors/00000000010111111-V-0000.bin"
noncomputable def vp00000000010111111 : Blocks := vp00000000010111111_0
private theorem bp000000000101111110 : Branch 0 (-11699139/62500 : ℚ) vp00000000010111111 := by
  apply branch_left_normalized (c:=vp000000000101111110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-11699139/62500 : ℚ) - ((0:ℤ):ℚ) = (-11699139/31250 : ℚ) by norm_num]
  exact coverp000000000101111110
private noncomputable def ep000000000101111111_0 : Blocks := edgeBlocks% "full/vectors/000000000101111111-E-0000.bin"
noncomputable def ep000000000101111111 : Blocks := ep000000000101111111_0
private theorem idp000000000101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000010111111.list =
    C ((2:ℤ)^34) * horner X vp000000000101111111.list + horner X ep000000000101111111.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000101111111 : Branch 1 (-11699139/62500 : ℚ) vp00000000010111111 := by
  apply branch_checked idp000000000101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-11699139/62500 : ℚ) - ((1:ℤ):ℚ) = (-11730389/31250 : ℚ) by norm_num]
  exact coverp000000000101111111
theorem coverp00000000010111111 : Covers (-11699139/62500 : ℚ) vp00000000010111111 := join_branches bp000000000101111110 bp000000000101111111
private noncomputable def vp00000000010111110_0 : Blocks := edgeBlocks% "full/vectors/00000000010111110-V-0000.bin"
noncomputable def vp00000000010111110 : Blocks := vp00000000010111110_0
theorem coverp00000000010111110 : Covers (-11636639/62500 : ℚ) vp00000000010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001011111_0 : Blocks := edgeBlocks% "full/vectors/0000000001011111-V-0000.bin"
noncomputable def vp0000000001011111 : Blocks := vp0000000001011111_0
private theorem bp00000000010111110 : Branch 0 (-11636639/125000 : ℚ) vp0000000001011111 := by
  apply branch_left_normalized (c:=vp00000000010111110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-11636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-11636639/62500 : ℚ) by norm_num]
  exact coverp00000000010111110
private noncomputable def ep00000000010111111_0 : Blocks := edgeBlocks% "full/vectors/00000000010111111-E-0000.bin"
noncomputable def ep00000000010111111 : Blocks := ep00000000010111111_0
private theorem idp00000000010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001011111.list =
    C ((2:ℤ)^53) * horner X vp00000000010111111.list + horner X ep00000000010111111.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010111111 : Branch 1 (-11636639/125000 : ℚ) vp0000000001011111 := by
  apply branch_checked idp00000000010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-11636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-11699139/62500 : ℚ) by norm_num]
  exact coverp00000000010111111
theorem coverp0000000001011111 : Covers (-11636639/125000 : ℚ) vp0000000001011111 := join_branches bp00000000010111110 bp00000000010111111
private noncomputable def vp00000000010111101_0 : Blocks := edgeBlocks% "full/vectors/00000000010111101-V-0000.bin"
noncomputable def vp00000000010111101 : Blocks := vp00000000010111101_0
theorem coverp00000000010111101 : Covers (-11574139/62500 : ℚ) vp00000000010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000010111100_0 : Blocks := edgeBlocks% "full/vectors/00000000010111100-V-0000.bin"
noncomputable def vp00000000010111100 : Blocks := vp00000000010111100_0
theorem coverp00000000010111100 : Covers (-11511639/62500 : ℚ) vp00000000010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001011110_0 : Blocks := edgeBlocks% "full/vectors/0000000001011110-V-0000.bin"
noncomputable def vp0000000001011110 : Blocks := vp0000000001011110_0
private theorem bp00000000010111100 : Branch 0 (-11511639/125000 : ℚ) vp0000000001011110 := by
  apply branch_left_normalized (c:=vp00000000010111100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-11511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-11511639/62500 : ℚ) by norm_num]
  exact coverp00000000010111100
private noncomputable def ep00000000010111101_0 : Blocks := edgeBlocks% "full/vectors/00000000010111101-E-0000.bin"
noncomputable def ep00000000010111101 : Blocks := ep00000000010111101_0
private theorem idp00000000010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001011110.list =
    C ((2:ℤ)^53) * horner X vp00000000010111101.list + horner X ep00000000010111101.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010111101 : Branch 1 (-11511639/125000 : ℚ) vp0000000001011110 := by
  apply branch_checked idp00000000010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-11511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-11574139/62500 : ℚ) by norm_num]
  exact coverp00000000010111101
theorem coverp0000000001011110 : Covers (-11511639/125000 : ℚ) vp0000000001011110 := join_branches bp00000000010111100 bp00000000010111101
private noncomputable def vp000000000101111_0 : Blocks := edgeBlocks% "full/vectors/000000000101111-V-0000.bin"
noncomputable def vp000000000101111 : Blocks := vp000000000101111_0
private theorem bp0000000001011110 : Branch 0 (-11511639/250000 : ℚ) vp000000000101111 := by
  apply branch_left_normalized (c:=vp0000000001011110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-11511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-11511639/125000 : ℚ) by norm_num]
  exact coverp0000000001011110
private noncomputable def ep0000000001011111_0 : Blocks := edgeBlocks% "full/vectors/0000000001011111-E-0000.bin"
noncomputable def ep0000000001011111 : Blocks := ep0000000001011111_0
private theorem idp0000000001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000101111.list =
    C ((2:ℤ)^90) * horner X vp0000000001011111.list + horner X ep0000000001011111.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001011111 : Branch 1 (-11511639/250000 : ℚ) vp000000000101111 := by
  apply branch_checked idp0000000001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-11511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-11636639/125000 : ℚ) by norm_num]
  exact coverp0000000001011111
theorem coverp000000000101111 : Covers (-11511639/250000 : ℚ) vp000000000101111 := join_branches bp0000000001011110 bp0000000001011111
private noncomputable def vp000000000101110111_0 : Blocks := edgeBlocks% "full/vectors/000000000101110111-V-0000.bin"
noncomputable def vp000000000101110111 : Blocks := vp000000000101110111_0
theorem coverp000000000101110111 : Covers (-11480389/31250 : ℚ) vp000000000101110111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000101110110_0 : Blocks := edgeBlocks% "full/vectors/000000000101110110-V-0000.bin"
noncomputable def vp000000000101110110 : Blocks := vp000000000101110110_0
theorem coverp000000000101110110 : Covers (-11449139/31250 : ℚ) vp000000000101110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000010111011_0 : Blocks := edgeBlocks% "full/vectors/00000000010111011-V-0000.bin"
noncomputable def vp00000000010111011 : Blocks := vp00000000010111011_0
private theorem bp000000000101110110 : Branch 0 (-11449139/62500 : ℚ) vp00000000010111011 := by
  apply branch_left_normalized (c:=vp000000000101110110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-11449139/62500 : ℚ) - ((0:ℤ):ℚ) = (-11449139/31250 : ℚ) by norm_num]
  exact coverp000000000101110110
private noncomputable def ep000000000101110111_0 : Blocks := edgeBlocks% "full/vectors/000000000101110111-E-0000.bin"
noncomputable def ep000000000101110111 : Blocks := ep000000000101110111_0
private theorem idp000000000101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000010111011.list =
    C ((2:ℤ)^33) * horner X vp000000000101110111.list + horner X ep000000000101110111.list := by
  exact edge_identity (B := (2:ℤ)^145) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000101110111 : Branch 1 (-11449139/62500 : ℚ) vp00000000010111011 := by
  apply branch_checked idp000000000101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-11449139/62500 : ℚ) - ((1:ℤ):ℚ) = (-11480389/31250 : ℚ) by norm_num]
  exact coverp000000000101110111
theorem coverp00000000010111011 : Covers (-11449139/62500 : ℚ) vp00000000010111011 := join_branches bp000000000101110110 bp000000000101110111
private noncomputable def vp00000000010111010_0 : Blocks := edgeBlocks% "full/vectors/00000000010111010-V-0000.bin"
noncomputable def vp00000000010111010 : Blocks := vp00000000010111010_0
theorem coverp00000000010111010 : Covers (-11386639/62500 : ℚ) vp00000000010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001011101_0 : Blocks := edgeBlocks% "full/vectors/0000000001011101-V-0000.bin"
noncomputable def vp0000000001011101 : Blocks := vp0000000001011101_0
private theorem bp00000000010111010 : Branch 0 (-11386639/125000 : ℚ) vp0000000001011101 := by
  apply branch_left_normalized (c:=vp00000000010111010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-11386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-11386639/62500 : ℚ) by norm_num]
  exact coverp00000000010111010
private noncomputable def ep00000000010111011_0 : Blocks := edgeBlocks% "full/vectors/00000000010111011-E-0000.bin"
noncomputable def ep00000000010111011 : Blocks := ep00000000010111011_0
private theorem idp00000000010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001011101.list =
    C ((2:ℤ)^53) * horner X vp00000000010111011.list + horner X ep00000000010111011.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010111011 : Branch 1 (-11386639/125000 : ℚ) vp0000000001011101 := by
  apply branch_checked idp00000000010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-11386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-11449139/62500 : ℚ) by norm_num]
  exact coverp00000000010111011
theorem coverp0000000001011101 : Covers (-11386639/125000 : ℚ) vp0000000001011101 := join_branches bp00000000010111010 bp00000000010111011
private noncomputable def vp00000000010111001_0 : Blocks := edgeBlocks% "full/vectors/00000000010111001-V-0000.bin"
noncomputable def vp00000000010111001 : Blocks := vp00000000010111001_0
theorem coverp00000000010111001 : Covers (-11324139/62500 : ℚ) vp00000000010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000010111000_0 : Blocks := edgeBlocks% "full/vectors/00000000010111000-V-0000.bin"
noncomputable def vp00000000010111000 : Blocks := vp00000000010111000_0
theorem coverp00000000010111000 : Covers (-11261639/62500 : ℚ) vp00000000010111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001011100_0 : Blocks := edgeBlocks% "full/vectors/0000000001011100-V-0000.bin"
noncomputable def vp0000000001011100 : Blocks := vp0000000001011100_0
private theorem bp00000000010111000 : Branch 0 (-11261639/125000 : ℚ) vp0000000001011100 := by
  apply branch_left_normalized (c:=vp00000000010111000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-11261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-11261639/62500 : ℚ) by norm_num]
  exact coverp00000000010111000
private noncomputable def ep00000000010111001_0 : Blocks := edgeBlocks% "full/vectors/00000000010111001-E-0000.bin"
noncomputable def ep00000000010111001 : Blocks := ep00000000010111001_0
private theorem idp00000000010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001011100.list =
    C ((2:ℤ)^52) * horner X vp00000000010111001.list + horner X ep00000000010111001.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010111001 : Branch 1 (-11261639/125000 : ℚ) vp0000000001011100 := by
  apply branch_checked idp00000000010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-11261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-11324139/62500 : ℚ) by norm_num]
  exact coverp00000000010111001
theorem coverp0000000001011100 : Covers (-11261639/125000 : ℚ) vp0000000001011100 := join_branches bp00000000010111000 bp00000000010111001
private noncomputable def vp000000000101110_0 : Blocks := edgeBlocks% "full/vectors/000000000101110-V-0000.bin"
noncomputable def vp000000000101110 : Blocks := vp000000000101110_0
private theorem bp0000000001011100 : Branch 0 (-11261639/250000 : ℚ) vp000000000101110 := by
  apply branch_left_normalized (c:=vp0000000001011100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-11261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-11261639/125000 : ℚ) by norm_num]
  exact coverp0000000001011100
private noncomputable def ep0000000001011101_0 : Blocks := edgeBlocks% "full/vectors/0000000001011101-E-0000.bin"
noncomputable def ep0000000001011101 : Blocks := ep0000000001011101_0
private theorem idp0000000001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000101110.list =
    C ((2:ℤ)^90) * horner X vp0000000001011101.list + horner X ep0000000001011101.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001011101 : Branch 1 (-11261639/250000 : ℚ) vp000000000101110 := by
  apply branch_checked idp0000000001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-11261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-11386639/125000 : ℚ) by norm_num]
  exact coverp0000000001011101
theorem coverp000000000101110 : Covers (-11261639/250000 : ℚ) vp000000000101110 := join_branches bp0000000001011100 bp0000000001011101
private noncomputable def vp00000000010111_0 : Blocks := edgeBlocks% "full/vectors/00000000010111-V-0000.bin"
private noncomputable def vp00000000010111_1 : Blocks := edgeBlocks% "full/vectors/00000000010111-V-0001.bin"
noncomputable def vp00000000010111 : Blocks := (Blocks.join vp00000000010111_0 vp00000000010111_1)
private theorem bp000000000101110 : Branch 0 (-11261639/500000 : ℚ) vp00000000010111 := by
  apply branch_left_normalized (c:=vp000000000101110) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-11261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-11261639/250000 : ℚ) by norm_num]
  exact coverp000000000101110
private noncomputable def ep000000000101111_0 : Blocks := edgeBlocks% "full/vectors/000000000101111-E-0000.bin"
private noncomputable def ep000000000101111_1 : Blocks := edgeBlocks% "full/vectors/000000000101111-E-0001.bin"
noncomputable def ep000000000101111 : Blocks := (Blocks.join ep000000000101111_0 ep000000000101111_1)
private theorem idp000000000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000010111.list =
    C ((2:ℤ)^162) * horner X vp000000000101111.list + horner X ep000000000101111.list := by
  exact edge_identity (B := (2:ℤ)^331) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000101111 : Branch 1 (-11261639/500000 : ℚ) vp00000000010111 := by
  apply branch_checked idp000000000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-11261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-11511639/250000 : ℚ) by norm_num]
  exact coverp000000000101111
theorem coverp00000000010111 : Covers (-11261639/500000 : ℚ) vp00000000010111 := join_branches bp000000000101110 bp000000000101111
private noncomputable def vp0000000001011011_0 : Blocks := edgeBlocks% "full/vectors/0000000001011011-V-0000.bin"
noncomputable def vp0000000001011011 : Blocks := vp0000000001011011_0
theorem coverp0000000001011011 : Covers (-11136639/125000 : ℚ) vp0000000001011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001011010_0 : Blocks := edgeBlocks% "full/vectors/0000000001011010-V-0000.bin"
noncomputable def vp0000000001011010 : Blocks := vp0000000001011010_0
theorem coverp0000000001011010 : Covers (-11011639/125000 : ℚ) vp0000000001011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000101101_0 : Blocks := edgeBlocks% "full/vectors/000000000101101-V-0000.bin"
noncomputable def vp000000000101101 : Blocks := vp000000000101101_0
private theorem bp0000000001011010 : Branch 0 (-11011639/250000 : ℚ) vp000000000101101 := by
  apply branch_left_normalized (c:=vp0000000001011010) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-11011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-11011639/125000 : ℚ) by norm_num]
  exact coverp0000000001011010
private noncomputable def ep0000000001011011_0 : Blocks := edgeBlocks% "full/vectors/0000000001011011-E-0000.bin"
noncomputable def ep0000000001011011 : Blocks := ep0000000001011011_0
private theorem idp0000000001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000101101.list =
    C ((2:ℤ)^90) * horner X vp0000000001011011.list + horner X ep0000000001011011.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001011011 : Branch 1 (-11011639/250000 : ℚ) vp000000000101101 := by
  apply branch_checked idp0000000001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-11011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-11136639/125000 : ℚ) by norm_num]
  exact coverp0000000001011011
theorem coverp000000000101101 : Covers (-11011639/250000 : ℚ) vp000000000101101 := join_branches bp0000000001011010 bp0000000001011011
private noncomputable def vp0000000001011001_0 : Blocks := edgeBlocks% "full/vectors/0000000001011001-V-0000.bin"
noncomputable def vp0000000001011001 : Blocks := vp0000000001011001_0
theorem coverp0000000001011001 : Covers (-10886639/125000 : ℚ) vp0000000001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001011000_0 : Blocks := edgeBlocks% "full/vectors/0000000001011000-V-0000.bin"
noncomputable def vp0000000001011000 : Blocks := vp0000000001011000_0
theorem coverp0000000001011000 : Covers (-10761639/125000 : ℚ) vp0000000001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000101100_0 : Blocks := edgeBlocks% "full/vectors/000000000101100-V-0000.bin"
noncomputable def vp000000000101100 : Blocks := vp000000000101100_0
private theorem bp0000000001011000 : Branch 0 (-10761639/250000 : ℚ) vp000000000101100 := by
  apply branch_left_normalized (c:=vp0000000001011000) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-10761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-10761639/125000 : ℚ) by norm_num]
  exact coverp0000000001011000
private noncomputable def ep0000000001011001_0 : Blocks := edgeBlocks% "full/vectors/0000000001011001-E-0000.bin"
noncomputable def ep0000000001011001 : Blocks := ep0000000001011001_0
private theorem idp0000000001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000101100.list =
    C ((2:ℤ)^90) * horner X vp0000000001011001.list + horner X ep0000000001011001.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001011001 : Branch 1 (-10761639/250000 : ℚ) vp000000000101100 := by
  apply branch_checked idp0000000001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-10761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-10886639/125000 : ℚ) by norm_num]
  exact coverp0000000001011001
theorem coverp000000000101100 : Covers (-10761639/250000 : ℚ) vp000000000101100 := join_branches bp0000000001011000 bp0000000001011001
private noncomputable def vp00000000010110_0 : Blocks := edgeBlocks% "full/vectors/00000000010110-V-0000.bin"
private noncomputable def vp00000000010110_1 : Blocks := edgeBlocks% "full/vectors/00000000010110-V-0001.bin"
noncomputable def vp00000000010110 : Blocks := (Blocks.join vp00000000010110_0 vp00000000010110_1)
private theorem bp000000000101100 : Branch 0 (-10761639/500000 : ℚ) vp00000000010110 := by
  apply branch_left_normalized (c:=vp000000000101100) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-10761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-10761639/250000 : ℚ) by norm_num]
  exact coverp000000000101100
private noncomputable def ep000000000101101_0 : Blocks := edgeBlocks% "full/vectors/000000000101101-E-0000.bin"
private noncomputable def ep000000000101101_1 : Blocks := edgeBlocks% "full/vectors/000000000101101-E-0001.bin"
noncomputable def ep000000000101101 : Blocks := (Blocks.join ep000000000101101_0 ep000000000101101_1)
private theorem idp000000000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000010110.list =
    C ((2:ℤ)^164) * horner X vp000000000101101.list + horner X ep000000000101101.list := by
  exact edge_identity (B := (2:ℤ)^333) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000101101 : Branch 1 (-10761639/500000 : ℚ) vp00000000010110 := by
  apply branch_checked idp000000000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-10761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-11011639/250000 : ℚ) by norm_num]
  exact coverp000000000101101
theorem coverp00000000010110 : Covers (-10761639/500000 : ℚ) vp00000000010110 := join_branches bp000000000101100 bp000000000101101
private noncomputable def vp0000000001011_0 : Blocks := edgeBlocks% "full/vectors/0000000001011-V-0000.bin"
private noncomputable def vp0000000001011_1 : Blocks := edgeBlocks% "full/vectors/0000000001011-V-0001.bin"
private noncomputable def vp0000000001011_2 : Blocks := edgeBlocks% "full/vectors/0000000001011-V-0002.bin"
noncomputable def vp0000000001011 : Blocks := (Blocks.join vp0000000001011_0 (Blocks.join vp0000000001011_1 vp0000000001011_2))
private theorem bp00000000010110 : Branch 0 (-10761639/1000000 : ℚ) vp0000000001011 := by
  apply branch_left_normalized (c:=vp00000000010110) (k:=0) (m:=163) (by decide +kernel)
  rw [show 2*(-10761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-10761639/500000 : ℚ) by norm_num]
  exact coverp00000000010110
private noncomputable def ep00000000010111_0 : Blocks := edgeBlocks% "full/vectors/00000000010111-E-0000.bin"
private noncomputable def ep00000000010111_1 : Blocks := edgeBlocks% "full/vectors/00000000010111-E-0001.bin"
private noncomputable def ep00000000010111_2 : Blocks := edgeBlocks% "full/vectors/00000000010111-E-0002.bin"
noncomputable def ep00000000010111 : Blocks := (Blocks.join ep00000000010111_0 (Blocks.join ep00000000010111_1 ep00000000010111_2))
private theorem idp00000000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001011.list =
    C ((2:ℤ)^313) * horner X vp00000000010111.list + horner X ep00000000010111.list := by
  exact edge_identity (B := (2:ℤ)^559) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010111 : Branch 1 (-10761639/1000000 : ℚ) vp0000000001011 := by
  apply branch_checked idp00000000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-10761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-11261639/500000 : ℚ) by norm_num]
  exact coverp00000000010111
theorem coverp0000000001011 : Covers (-10761639/1000000 : ℚ) vp0000000001011 := join_branches bp00000000010110 bp00000000010111
private noncomputable def vp0000000001010111_0 : Blocks := edgeBlocks% "full/vectors/0000000001010111-V-0000.bin"
noncomputable def vp0000000001010111 : Blocks := vp0000000001010111_0
theorem coverp0000000001010111 : Covers (-10636639/125000 : ℚ) vp0000000001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001010110_0 : Blocks := edgeBlocks% "full/vectors/0000000001010110-V-0000.bin"
noncomputable def vp0000000001010110 : Blocks := vp0000000001010110_0
theorem coverp0000000001010110 : Covers (-10511639/125000 : ℚ) vp0000000001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000101011_0 : Blocks := edgeBlocks% "full/vectors/000000000101011-V-0000.bin"
noncomputable def vp000000000101011 : Blocks := vp000000000101011_0
private theorem bp0000000001010110 : Branch 0 (-10511639/250000 : ℚ) vp000000000101011 := by
  apply branch_left_normalized (c:=vp0000000001010110) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-10511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-10511639/125000 : ℚ) by norm_num]
  exact coverp0000000001010110
private noncomputable def ep0000000001010111_0 : Blocks := edgeBlocks% "full/vectors/0000000001010111-E-0000.bin"
noncomputable def ep0000000001010111 : Blocks := ep0000000001010111_0
private theorem idp0000000001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000101011.list =
    C ((2:ℤ)^91) * horner X vp0000000001010111.list + horner X ep0000000001010111.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001010111 : Branch 1 (-10511639/250000 : ℚ) vp000000000101011 := by
  apply branch_checked idp0000000001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-10511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-10636639/125000 : ℚ) by norm_num]
  exact coverp0000000001010111
theorem coverp000000000101011 : Covers (-10511639/250000 : ℚ) vp000000000101011 := join_branches bp0000000001010110 bp0000000001010111
private noncomputable def vp0000000001010101_0 : Blocks := edgeBlocks% "full/vectors/0000000001010101-V-0000.bin"
noncomputable def vp0000000001010101 : Blocks := vp0000000001010101_0
theorem coverp0000000001010101 : Covers (-10386639/125000 : ℚ) vp0000000001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001010100_0 : Blocks := edgeBlocks% "full/vectors/0000000001010100-V-0000.bin"
noncomputable def vp0000000001010100 : Blocks := vp0000000001010100_0
theorem coverp0000000001010100 : Covers (-10261639/125000 : ℚ) vp0000000001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000101010_0 : Blocks := edgeBlocks% "full/vectors/000000000101010-V-0000.bin"
noncomputable def vp000000000101010 : Blocks := vp000000000101010_0
private theorem bp0000000001010100 : Branch 0 (-10261639/250000 : ℚ) vp000000000101010 := by
  apply branch_left_normalized (c:=vp0000000001010100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-10261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-10261639/125000 : ℚ) by norm_num]
  exact coverp0000000001010100
private noncomputable def ep0000000001010101_0 : Blocks := edgeBlocks% "full/vectors/0000000001010101-E-0000.bin"
noncomputable def ep0000000001010101 : Blocks := ep0000000001010101_0
private theorem idp0000000001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000101010.list =
    C ((2:ℤ)^92) * horner X vp0000000001010101.list + horner X ep0000000001010101.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001010101 : Branch 1 (-10261639/250000 : ℚ) vp000000000101010 := by
  apply branch_checked idp0000000001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-10261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-10386639/125000 : ℚ) by norm_num]
  exact coverp0000000001010101
theorem coverp000000000101010 : Covers (-10261639/250000 : ℚ) vp000000000101010 := join_branches bp0000000001010100 bp0000000001010101
private noncomputable def vp00000000010101_0 : Blocks := edgeBlocks% "full/vectors/00000000010101-V-0000.bin"
private noncomputable def vp00000000010101_1 : Blocks := edgeBlocks% "full/vectors/00000000010101-V-0001.bin"
noncomputable def vp00000000010101 : Blocks := (Blocks.join vp00000000010101_0 vp00000000010101_1)
private theorem bp000000000101010 : Branch 0 (-10261639/500000 : ℚ) vp00000000010101 := by
  apply branch_left_normalized (c:=vp000000000101010) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-10261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-10261639/250000 : ℚ) by norm_num]
  exact coverp000000000101010
private noncomputable def ep000000000101011_0 : Blocks := edgeBlocks% "full/vectors/000000000101011-E-0000.bin"
private noncomputable def ep000000000101011_1 : Blocks := edgeBlocks% "full/vectors/000000000101011-E-0001.bin"
noncomputable def ep000000000101011 : Blocks := (Blocks.join ep000000000101011_0 ep000000000101011_1)
private theorem idp000000000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000010101.list =
    C ((2:ℤ)^168) * horner X vp000000000101011.list + horner X ep000000000101011.list := by
  exact edge_identity (B := (2:ℤ)^337) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000101011 : Branch 1 (-10261639/500000 : ℚ) vp00000000010101 := by
  apply branch_checked idp000000000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-10261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-10511639/250000 : ℚ) by norm_num]
  exact coverp000000000101011
theorem coverp00000000010101 : Covers (-10261639/500000 : ℚ) vp00000000010101 := join_branches bp000000000101010 bp000000000101011
private noncomputable def vp0000000001010011_0 : Blocks := edgeBlocks% "full/vectors/0000000001010011-V-0000.bin"
noncomputable def vp0000000001010011 : Blocks := vp0000000001010011_0
theorem coverp0000000001010011 : Covers (-10136639/125000 : ℚ) vp0000000001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001010010_0 : Blocks := edgeBlocks% "full/vectors/0000000001010010-V-0000.bin"
noncomputable def vp0000000001010010 : Blocks := vp0000000001010010_0
theorem coverp0000000001010010 : Covers (-10011639/125000 : ℚ) vp0000000001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000101001_0 : Blocks := edgeBlocks% "full/vectors/000000000101001-V-0000.bin"
noncomputable def vp000000000101001 : Blocks := vp000000000101001_0
private theorem bp0000000001010010 : Branch 0 (-10011639/250000 : ℚ) vp000000000101001 := by
  apply branch_left_normalized (c:=vp0000000001010010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-10011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-10011639/125000 : ℚ) by norm_num]
  exact coverp0000000001010010
private noncomputable def ep0000000001010011_0 : Blocks := edgeBlocks% "full/vectors/0000000001010011-E-0000.bin"
noncomputable def ep0000000001010011 : Blocks := ep0000000001010011_0
private theorem idp0000000001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000101001.list =
    C ((2:ℤ)^92) * horner X vp0000000001010011.list + horner X ep0000000001010011.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001010011 : Branch 1 (-10011639/250000 : ℚ) vp000000000101001 := by
  apply branch_checked idp0000000001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-10011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-10136639/125000 : ℚ) by norm_num]
  exact coverp0000000001010011
theorem coverp000000000101001 : Covers (-10011639/250000 : ℚ) vp000000000101001 := join_branches bp0000000001010010 bp0000000001010011
private noncomputable def vp0000000001010001_0 : Blocks := edgeBlocks% "full/vectors/0000000001010001-V-0000.bin"
noncomputable def vp0000000001010001 : Blocks := vp0000000001010001_0
theorem coverp0000000001010001 : Covers (-9886639/125000 : ℚ) vp0000000001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001010000_0 : Blocks := edgeBlocks% "full/vectors/0000000001010000-V-0000.bin"
noncomputable def vp0000000001010000 : Blocks := vp0000000001010000_0
theorem coverp0000000001010000 : Covers (-9761639/125000 : ℚ) vp0000000001010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000101000_0 : Blocks := edgeBlocks% "full/vectors/000000000101000-V-0000.bin"
noncomputable def vp000000000101000 : Blocks := vp000000000101000_0
private theorem bp0000000001010000 : Branch 0 (-9761639/250000 : ℚ) vp000000000101000 := by
  apply branch_left_normalized (c:=vp0000000001010000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-9761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-9761639/125000 : ℚ) by norm_num]
  exact coverp0000000001010000
private noncomputable def ep0000000001010001_0 : Blocks := edgeBlocks% "full/vectors/0000000001010001-E-0000.bin"
noncomputable def ep0000000001010001 : Blocks := ep0000000001010001_0
private theorem idp0000000001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000101000.list =
    C ((2:ℤ)^93) * horner X vp0000000001010001.list + horner X ep0000000001010001.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001010001 : Branch 1 (-9761639/250000 : ℚ) vp000000000101000 := by
  apply branch_checked idp0000000001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-9761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-9886639/125000 : ℚ) by norm_num]
  exact coverp0000000001010001
theorem coverp000000000101000 : Covers (-9761639/250000 : ℚ) vp000000000101000 := join_branches bp0000000001010000 bp0000000001010001
private noncomputable def vp00000000010100_0 : Blocks := edgeBlocks% "full/vectors/00000000010100-V-0000.bin"
private noncomputable def vp00000000010100_1 : Blocks := edgeBlocks% "full/vectors/00000000010100-V-0001.bin"
noncomputable def vp00000000010100 : Blocks := (Blocks.join vp00000000010100_0 vp00000000010100_1)
private theorem bp000000000101000 : Branch 0 (-9761639/500000 : ℚ) vp00000000010100 := by
  apply branch_left_normalized (c:=vp000000000101000) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-9761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-9761639/250000 : ℚ) by norm_num]
  exact coverp000000000101000
private noncomputable def ep000000000101001_0 : Blocks := edgeBlocks% "full/vectors/000000000101001-E-0000.bin"
private noncomputable def ep000000000101001_1 : Blocks := edgeBlocks% "full/vectors/000000000101001-E-0001.bin"
noncomputable def ep000000000101001 : Blocks := (Blocks.join ep000000000101001_0 ep000000000101001_1)
private theorem idp000000000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000010100.list =
    C ((2:ℤ)^171) * horner X vp000000000101001.list + horner X ep000000000101001.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000101001 : Branch 1 (-9761639/500000 : ℚ) vp00000000010100 := by
  apply branch_checked idp000000000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-9761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-10011639/250000 : ℚ) by norm_num]
  exact coverp000000000101001
theorem coverp00000000010100 : Covers (-9761639/500000 : ℚ) vp00000000010100 := join_branches bp000000000101000 bp000000000101001
private noncomputable def vp0000000001010_0 : Blocks := edgeBlocks% "full/vectors/0000000001010-V-0000.bin"
private noncomputable def vp0000000001010_1 : Blocks := edgeBlocks% "full/vectors/0000000001010-V-0001.bin"
private noncomputable def vp0000000001010_2 : Blocks := edgeBlocks% "full/vectors/0000000001010-V-0002.bin"
noncomputable def vp0000000001010 : Blocks := (Blocks.join vp0000000001010_0 (Blocks.join vp0000000001010_1 vp0000000001010_2))
private theorem bp00000000010100 : Branch 0 (-9761639/1000000 : ℚ) vp0000000001010 := by
  apply branch_left_normalized (c:=vp00000000010100) (k:=0) (m:=169) (by decide +kernel)
  rw [show 2*(-9761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-9761639/500000 : ℚ) by norm_num]
  exact coverp00000000010100
private noncomputable def ep00000000010101_0 : Blocks := edgeBlocks% "full/vectors/00000000010101-E-0000.bin"
private noncomputable def ep00000000010101_1 : Blocks := edgeBlocks% "full/vectors/00000000010101-E-0001.bin"
private noncomputable def ep00000000010101_2 : Blocks := edgeBlocks% "full/vectors/00000000010101-E-0002.bin"
noncomputable def ep00000000010101 : Blocks := (Blocks.join ep00000000010101_0 (Blocks.join ep00000000010101_1 ep00000000010101_2))
private theorem idp00000000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001010.list =
    C ((2:ℤ)^327) * horner X vp00000000010101.list + horner X ep00000000010101.list := by
  exact edge_identity (B := (2:ℤ)^578) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010101 : Branch 1 (-9761639/1000000 : ℚ) vp0000000001010 := by
  apply branch_checked idp00000000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-9761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-10261639/500000 : ℚ) by norm_num]
  exact coverp00000000010101
theorem coverp0000000001010 : Covers (-9761639/1000000 : ℚ) vp0000000001010 := join_branches bp00000000010100 bp00000000010101
private noncomputable def vp000000000101_0 : Blocks := edgeBlocks% "full/vectors/000000000101-V-0000.bin"
private noncomputable def vp000000000101_1 : Blocks := edgeBlocks% "full/vectors/000000000101-V-0001.bin"
private noncomputable def vp000000000101_2 : Blocks := edgeBlocks% "full/vectors/000000000101-V-0002.bin"
private noncomputable def vp000000000101_3 : Blocks := edgeBlocks% "full/vectors/000000000101-V-0003.bin"
private noncomputable def vp000000000101_4 : Blocks := edgeBlocks% "full/vectors/000000000101-V-0004.bin"
noncomputable def vp000000000101 : Blocks := (Blocks.join (Blocks.join vp000000000101_0 vp000000000101_1) (Blocks.join vp000000000101_2 (Blocks.join vp000000000101_3 vp000000000101_4)))
private theorem bp0000000001010 : Branch 0 (-9761639/2000000 : ℚ) vp000000000101 := by
  apply branch_left_normalized (c:=vp0000000001010) (k:=0) (m:=324) (by decide +kernel)
  rw [show 2*(-9761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-9761639/1000000 : ℚ) by norm_num]
  exact coverp0000000001010
private noncomputable def ep0000000001011_0 : Blocks := edgeBlocks% "full/vectors/0000000001011-E-0000.bin"
private noncomputable def ep0000000001011_1 : Blocks := edgeBlocks% "full/vectors/0000000001011-E-0001.bin"
private noncomputable def ep0000000001011_2 : Blocks := edgeBlocks% "full/vectors/0000000001011-E-0002.bin"
private noncomputable def ep0000000001011_3 : Blocks := edgeBlocks% "full/vectors/0000000001011-E-0003.bin"
private noncomputable def ep0000000001011_4 : Blocks := edgeBlocks% "full/vectors/0000000001011-E-0004.bin"
noncomputable def ep0000000001011 : Blocks := (Blocks.join (Blocks.join ep0000000001011_0 ep0000000001011_1) (Blocks.join ep0000000001011_2 (Blocks.join ep0000000001011_3 ep0000000001011_4)))
private theorem idp0000000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000101.list =
    C ((2:ℤ)^635) * horner X vp0000000001011.list + horner X ep0000000001011.list := by
  exact edge_identity (B := (2:ℤ)^1049) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001011 : Branch 1 (-9761639/2000000 : ℚ) vp000000000101 := by
  apply branch_checked idp0000000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-9761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-10761639/1000000 : ℚ) by norm_num]
  exact coverp0000000001011
theorem coverp000000000101 : Covers (-9761639/2000000 : ℚ) vp000000000101 := join_branches bp0000000001010 bp0000000001011
private noncomputable def vp0000000001001111_0 : Blocks := edgeBlocks% "full/vectors/0000000001001111-V-0000.bin"
noncomputable def vp0000000001001111 : Blocks := vp0000000001001111_0
theorem coverp0000000001001111 : Covers (-9636639/125000 : ℚ) vp0000000001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001001110_0 : Blocks := edgeBlocks% "full/vectors/0000000001001110-V-0000.bin"
noncomputable def vp0000000001001110 : Blocks := vp0000000001001110_0
theorem coverp0000000001001110 : Covers (-9511639/125000 : ℚ) vp0000000001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000100111_0 : Blocks := edgeBlocks% "full/vectors/000000000100111-V-0000.bin"
noncomputable def vp000000000100111 : Blocks := vp000000000100111_0
private theorem bp0000000001001110 : Branch 0 (-9511639/250000 : ℚ) vp000000000100111 := by
  apply branch_left_normalized (c:=vp0000000001001110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-9511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-9511639/125000 : ℚ) by norm_num]
  exact coverp0000000001001110
private noncomputable def ep0000000001001111_0 : Blocks := edgeBlocks% "full/vectors/0000000001001111-E-0000.bin"
noncomputable def ep0000000001001111 : Blocks := ep0000000001001111_0
private theorem idp0000000001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000100111.list =
    C ((2:ℤ)^94) * horner X vp0000000001001111.list + horner X ep0000000001001111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001001111 : Branch 1 (-9511639/250000 : ℚ) vp000000000100111 := by
  apply branch_checked idp0000000001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-9511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-9636639/125000 : ℚ) by norm_num]
  exact coverp0000000001001111
theorem coverp000000000100111 : Covers (-9511639/250000 : ℚ) vp000000000100111 := join_branches bp0000000001001110 bp0000000001001111
private noncomputable def vp0000000001001101_0 : Blocks := edgeBlocks% "full/vectors/0000000001001101-V-0000.bin"
noncomputable def vp0000000001001101 : Blocks := vp0000000001001101_0
theorem coverp0000000001001101 : Covers (-9386639/125000 : ℚ) vp0000000001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001001100_0 : Blocks := edgeBlocks% "full/vectors/0000000001001100-V-0000.bin"
noncomputable def vp0000000001001100 : Blocks := vp0000000001001100_0
theorem coverp0000000001001100 : Covers (-9261639/125000 : ℚ) vp0000000001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000100110_0 : Blocks := edgeBlocks% "full/vectors/000000000100110-V-0000.bin"
noncomputable def vp000000000100110 : Blocks := vp000000000100110_0
private theorem bp0000000001001100 : Branch 0 (-9261639/250000 : ℚ) vp000000000100110 := by
  apply branch_left_normalized (c:=vp0000000001001100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-9261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-9261639/125000 : ℚ) by norm_num]
  exact coverp0000000001001100
private noncomputable def ep0000000001001101_0 : Blocks := edgeBlocks% "full/vectors/0000000001001101-E-0000.bin"
noncomputable def ep0000000001001101 : Blocks := ep0000000001001101_0
private theorem idp0000000001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000100110.list =
    C ((2:ℤ)^94) * horner X vp0000000001001101.list + horner X ep0000000001001101.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001001101 : Branch 1 (-9261639/250000 : ℚ) vp000000000100110 := by
  apply branch_checked idp0000000001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-9261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-9386639/125000 : ℚ) by norm_num]
  exact coverp0000000001001101
theorem coverp000000000100110 : Covers (-9261639/250000 : ℚ) vp000000000100110 := join_branches bp0000000001001100 bp0000000001001101
private noncomputable def vp00000000010011_0 : Blocks := edgeBlocks% "full/vectors/00000000010011-V-0000.bin"
private noncomputable def vp00000000010011_1 : Blocks := edgeBlocks% "full/vectors/00000000010011-V-0001.bin"
noncomputable def vp00000000010011 : Blocks := (Blocks.join vp00000000010011_0 vp00000000010011_1)
private theorem bp000000000100110 : Branch 0 (-9261639/500000 : ℚ) vp00000000010011 := by
  apply branch_left_normalized (c:=vp000000000100110) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-9261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-9261639/250000 : ℚ) by norm_num]
  exact coverp000000000100110
private noncomputable def ep000000000100111_0 : Blocks := edgeBlocks% "full/vectors/000000000100111-E-0000.bin"
private noncomputable def ep000000000100111_1 : Blocks := edgeBlocks% "full/vectors/000000000100111-E-0001.bin"
noncomputable def ep000000000100111 : Blocks := (Blocks.join ep000000000100111_0 ep000000000100111_1)
private theorem idp000000000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000010011.list =
    C ((2:ℤ)^174) * horner X vp000000000100111.list + horner X ep000000000100111.list := by
  exact edge_identity (B := (2:ℤ)^345) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000100111 : Branch 1 (-9261639/500000 : ℚ) vp00000000010011 := by
  apply branch_checked idp000000000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-9261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-9511639/250000 : ℚ) by norm_num]
  exact coverp000000000100111
theorem coverp00000000010011 : Covers (-9261639/500000 : ℚ) vp00000000010011 := join_branches bp000000000100110 bp000000000100111
private noncomputable def vp0000000001001011_0 : Blocks := edgeBlocks% "full/vectors/0000000001001011-V-0000.bin"
noncomputable def vp0000000001001011 : Blocks := vp0000000001001011_0
theorem coverp0000000001001011 : Covers (-9136639/125000 : ℚ) vp0000000001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001001010_0 : Blocks := edgeBlocks% "full/vectors/0000000001001010-V-0000.bin"
noncomputable def vp0000000001001010 : Blocks := vp0000000001001010_0
theorem coverp0000000001001010 : Covers (-9011639/125000 : ℚ) vp0000000001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000100101_0 : Blocks := edgeBlocks% "full/vectors/000000000100101-V-0000.bin"
noncomputable def vp000000000100101 : Blocks := vp000000000100101_0
private theorem bp0000000001001010 : Branch 0 (-9011639/250000 : ℚ) vp000000000100101 := by
  apply branch_left_normalized (c:=vp0000000001001010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-9011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-9011639/125000 : ℚ) by norm_num]
  exact coverp0000000001001010
private noncomputable def ep0000000001001011_0 : Blocks := edgeBlocks% "full/vectors/0000000001001011-E-0000.bin"
noncomputable def ep0000000001001011 : Blocks := ep0000000001001011_0
private theorem idp0000000001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000100101.list =
    C ((2:ℤ)^96) * horner X vp0000000001001011.list + horner X ep0000000001001011.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001001011 : Branch 1 (-9011639/250000 : ℚ) vp000000000100101 := by
  apply branch_checked idp0000000001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-9011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-9136639/125000 : ℚ) by norm_num]
  exact coverp0000000001001011
theorem coverp000000000100101 : Covers (-9011639/250000 : ℚ) vp000000000100101 := join_branches bp0000000001001010 bp0000000001001011
private noncomputable def vp0000000001001001_0 : Blocks := edgeBlocks% "full/vectors/0000000001001001-V-0000.bin"
noncomputable def vp0000000001001001 : Blocks := vp0000000001001001_0
theorem coverp0000000001001001 : Covers (-8886639/125000 : ℚ) vp0000000001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001001000_0 : Blocks := edgeBlocks% "full/vectors/0000000001001000-V-0000.bin"
noncomputable def vp0000000001001000 : Blocks := vp0000000001001000_0
theorem coverp0000000001001000 : Covers (-8761639/125000 : ℚ) vp0000000001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000100100_0 : Blocks := edgeBlocks% "full/vectors/000000000100100-V-0000.bin"
noncomputable def vp000000000100100 : Blocks := vp000000000100100_0
private theorem bp0000000001001000 : Branch 0 (-8761639/250000 : ℚ) vp000000000100100 := by
  apply branch_left_normalized (c:=vp0000000001001000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-8761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-8761639/125000 : ℚ) by norm_num]
  exact coverp0000000001001000
private noncomputable def ep0000000001001001_0 : Blocks := edgeBlocks% "full/vectors/0000000001001001-E-0000.bin"
noncomputable def ep0000000001001001 : Blocks := ep0000000001001001_0
private theorem idp0000000001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000100100.list =
    C ((2:ℤ)^96) * horner X vp0000000001001001.list + horner X ep0000000001001001.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001001001 : Branch 1 (-8761639/250000 : ℚ) vp000000000100100 := by
  apply branch_checked idp0000000001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-8761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-8886639/125000 : ℚ) by norm_num]
  exact coverp0000000001001001
theorem coverp000000000100100 : Covers (-8761639/250000 : ℚ) vp000000000100100 := join_branches bp0000000001001000 bp0000000001001001
private noncomputable def vp00000000010010_0 : Blocks := edgeBlocks% "full/vectors/00000000010010-V-0000.bin"
private noncomputable def vp00000000010010_1 : Blocks := edgeBlocks% "full/vectors/00000000010010-V-0001.bin"
noncomputable def vp00000000010010 : Blocks := (Blocks.join vp00000000010010_0 vp00000000010010_1)
private theorem bp000000000100100 : Branch 0 (-8761639/500000 : ℚ) vp00000000010010 := by
  apply branch_left_normalized (c:=vp000000000100100) (k:=0) (m:=95) (by decide +kernel)
  rw [show 2*(-8761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-8761639/250000 : ℚ) by norm_num]
  exact coverp000000000100100
private noncomputable def ep000000000100101_0 : Blocks := edgeBlocks% "full/vectors/000000000100101-E-0000.bin"
private noncomputable def ep000000000100101_1 : Blocks := edgeBlocks% "full/vectors/000000000100101-E-0001.bin"
noncomputable def ep000000000100101 : Blocks := (Blocks.join ep000000000100101_0 ep000000000100101_1)
private theorem idp000000000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000010010.list =
    C ((2:ℤ)^179) * horner X vp000000000100101.list + horner X ep000000000100101.list := by
  exact edge_identity (B := (2:ℤ)^352) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000100101 : Branch 1 (-8761639/500000 : ℚ) vp00000000010010 := by
  apply branch_checked idp000000000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-8761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-9011639/250000 : ℚ) by norm_num]
  exact coverp000000000100101
theorem coverp00000000010010 : Covers (-8761639/500000 : ℚ) vp00000000010010 := join_branches bp000000000100100 bp000000000100101
private noncomputable def vp0000000001001_0 : Blocks := edgeBlocks% "full/vectors/0000000001001-V-0000.bin"
private noncomputable def vp0000000001001_1 : Blocks := edgeBlocks% "full/vectors/0000000001001-V-0001.bin"
private noncomputable def vp0000000001001_2 : Blocks := edgeBlocks% "full/vectors/0000000001001-V-0002.bin"
noncomputable def vp0000000001001 : Blocks := (Blocks.join vp0000000001001_0 (Blocks.join vp0000000001001_1 vp0000000001001_2))
private theorem bp00000000010010 : Branch 0 (-8761639/1000000 : ℚ) vp0000000001001 := by
  apply branch_left_normalized (c:=vp00000000010010) (k:=0) (m:=177) (by decide +kernel)
  rw [show 2*(-8761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-8761639/500000 : ℚ) by norm_num]
  exact coverp00000000010010
private noncomputable def ep00000000010011_0 : Blocks := edgeBlocks% "full/vectors/00000000010011-E-0000.bin"
private noncomputable def ep00000000010011_1 : Blocks := edgeBlocks% "full/vectors/00000000010011-E-0001.bin"
private noncomputable def ep00000000010011_2 : Blocks := edgeBlocks% "full/vectors/00000000010011-E-0002.bin"
noncomputable def ep00000000010011 : Blocks := (Blocks.join ep00000000010011_0 (Blocks.join ep00000000010011_1 ep00000000010011_2))
private theorem idp00000000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001001.list =
    C ((2:ℤ)^344) * horner X vp00000000010011.list + horner X ep00000000010011.list := by
  exact edge_identity (B := (2:ℤ)^602) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010011 : Branch 1 (-8761639/1000000 : ℚ) vp0000000001001 := by
  apply branch_checked idp00000000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-8761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-9261639/500000 : ℚ) by norm_num]
  exact coverp00000000010011
theorem coverp0000000001001 : Covers (-8761639/1000000 : ℚ) vp0000000001001 := join_branches bp00000000010010 bp00000000010011
private noncomputable def vp0000000001000111_0 : Blocks := edgeBlocks% "full/vectors/0000000001000111-V-0000.bin"
noncomputable def vp0000000001000111 : Blocks := vp0000000001000111_0
theorem coverp0000000001000111 : Covers (-8636639/125000 : ℚ) vp0000000001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001000110_0 : Blocks := edgeBlocks% "full/vectors/0000000001000110-V-0000.bin"
noncomputable def vp0000000001000110 : Blocks := vp0000000001000110_0
theorem coverp0000000001000110 : Covers (-8511639/125000 : ℚ) vp0000000001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000100011_0 : Blocks := edgeBlocks% "full/vectors/000000000100011-V-0000.bin"
noncomputable def vp000000000100011 : Blocks := vp000000000100011_0
private theorem bp0000000001000110 : Branch 0 (-8511639/250000 : ℚ) vp000000000100011 := by
  apply branch_left_normalized (c:=vp0000000001000110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-8511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-8511639/125000 : ℚ) by norm_num]
  exact coverp0000000001000110
private noncomputable def ep0000000001000111_0 : Blocks := edgeBlocks% "full/vectors/0000000001000111-E-0000.bin"
noncomputable def ep0000000001000111 : Blocks := ep0000000001000111_0
private theorem idp0000000001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000100011.list =
    C ((2:ℤ)^99) * horner X vp0000000001000111.list + horner X ep0000000001000111.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001000111 : Branch 1 (-8511639/250000 : ℚ) vp000000000100011 := by
  apply branch_checked idp0000000001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-8511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-8636639/125000 : ℚ) by norm_num]
  exact coverp0000000001000111
theorem coverp000000000100011 : Covers (-8511639/250000 : ℚ) vp000000000100011 := join_branches bp0000000001000110 bp0000000001000111
private noncomputable def vp00000000010001011_0 : Blocks := edgeBlocks% "full/vectors/00000000010001011-V-0000.bin"
noncomputable def vp00000000010001011 : Blocks := vp00000000010001011_0
theorem coverp00000000010001011 : Covers (-8449139/62500 : ℚ) vp00000000010001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000010001010_0 : Blocks := edgeBlocks% "full/vectors/00000000010001010-V-0000.bin"
noncomputable def vp00000000010001010 : Blocks := vp00000000010001010_0
theorem coverp00000000010001010 : Covers (-8386639/62500 : ℚ) vp00000000010001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001000101_0 : Blocks := edgeBlocks% "full/vectors/0000000001000101-V-0000.bin"
noncomputable def vp0000000001000101 : Blocks := vp0000000001000101_0
private theorem bp00000000010001010 : Branch 0 (-8386639/125000 : ℚ) vp0000000001000101 := by
  apply branch_left_normalized (c:=vp00000000010001010) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-8386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-8386639/62500 : ℚ) by norm_num]
  exact coverp00000000010001010
private noncomputable def ep00000000010001011_0 : Blocks := edgeBlocks% "full/vectors/00000000010001011-E-0000.bin"
noncomputable def ep00000000010001011 : Blocks := ep00000000010001011_0
private theorem idp00000000010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001000101.list =
    C ((2:ℤ)^57) * horner X vp00000000010001011.list + horner X ep00000000010001011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010001011 : Branch 1 (-8386639/125000 : ℚ) vp0000000001000101 := by
  apply branch_checked idp00000000010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-8386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-8449139/62500 : ℚ) by norm_num]
  exact coverp00000000010001011
theorem coverp0000000001000101 : Covers (-8386639/125000 : ℚ) vp0000000001000101 := join_branches bp00000000010001010 bp00000000010001011
private noncomputable def vp00000000010001001_0 : Blocks := edgeBlocks% "full/vectors/00000000010001001-V-0000.bin"
noncomputable def vp00000000010001001 : Blocks := vp00000000010001001_0
theorem coverp00000000010001001 : Covers (-8324139/62500 : ℚ) vp00000000010001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000010001000_0 : Blocks := edgeBlocks% "full/vectors/00000000010001000-V-0000.bin"
noncomputable def vp00000000010001000 : Blocks := vp00000000010001000_0
theorem coverp00000000010001000 : Covers (-8261639/62500 : ℚ) vp00000000010001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001000100_0 : Blocks := edgeBlocks% "full/vectors/0000000001000100-V-0000.bin"
noncomputable def vp0000000001000100 : Blocks := vp0000000001000100_0
private theorem bp00000000010001000 : Branch 0 (-8261639/125000 : ℚ) vp0000000001000100 := by
  apply branch_left_normalized (c:=vp00000000010001000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-8261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-8261639/62500 : ℚ) by norm_num]
  exact coverp00000000010001000
private noncomputable def ep00000000010001001_0 : Blocks := edgeBlocks% "full/vectors/00000000010001001-E-0000.bin"
noncomputable def ep00000000010001001 : Blocks := ep00000000010001001_0
private theorem idp00000000010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001000100.list =
    C ((2:ℤ)^58) * horner X vp00000000010001001.list + horner X ep00000000010001001.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010001001 : Branch 1 (-8261639/125000 : ℚ) vp0000000001000100 := by
  apply branch_checked idp00000000010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-8261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-8324139/62500 : ℚ) by norm_num]
  exact coverp00000000010001001
theorem coverp0000000001000100 : Covers (-8261639/125000 : ℚ) vp0000000001000100 := join_branches bp00000000010001000 bp00000000010001001
private noncomputable def vp000000000100010_0 : Blocks := edgeBlocks% "full/vectors/000000000100010-V-0000.bin"
noncomputable def vp000000000100010 : Blocks := vp000000000100010_0
private theorem bp0000000001000100 : Branch 0 (-8261639/250000 : ℚ) vp000000000100010 := by
  apply branch_left_normalized (c:=vp0000000001000100) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-8261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-8261639/125000 : ℚ) by norm_num]
  exact coverp0000000001000100
private noncomputable def ep0000000001000101_0 : Blocks := edgeBlocks% "full/vectors/0000000001000101-E-0000.bin"
noncomputable def ep0000000001000101 : Blocks := ep0000000001000101_0
private theorem idp0000000001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000100010.list =
    C ((2:ℤ)^100) * horner X vp0000000001000101.list + horner X ep0000000001000101.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001000101 : Branch 1 (-8261639/250000 : ℚ) vp000000000100010 := by
  apply branch_checked idp0000000001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-8261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-8386639/125000 : ℚ) by norm_num]
  exact coverp0000000001000101
theorem coverp000000000100010 : Covers (-8261639/250000 : ℚ) vp000000000100010 := join_branches bp0000000001000100 bp0000000001000101
private noncomputable def vp00000000010001_0 : Blocks := edgeBlocks% "full/vectors/00000000010001-V-0000.bin"
private noncomputable def vp00000000010001_1 : Blocks := edgeBlocks% "full/vectors/00000000010001-V-0001.bin"
noncomputable def vp00000000010001 : Blocks := (Blocks.join vp00000000010001_0 vp00000000010001_1)
private theorem bp000000000100010 : Branch 0 (-8261639/500000 : ℚ) vp00000000010001 := by
  apply branch_left_normalized (c:=vp000000000100010) (k:=0) (m:=98) (by decide +kernel)
  rw [show 2*(-8261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-8261639/250000 : ℚ) by norm_num]
  exact coverp000000000100010
private noncomputable def ep000000000100011_0 : Blocks := edgeBlocks% "full/vectors/000000000100011-E-0000.bin"
private noncomputable def ep000000000100011_1 : Blocks := edgeBlocks% "full/vectors/000000000100011-E-0001.bin"
noncomputable def ep000000000100011 : Blocks := (Blocks.join ep000000000100011_0 ep000000000100011_1)
private theorem idp000000000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000010001.list =
    C ((2:ℤ)^185) * horner X vp000000000100011.list + horner X ep000000000100011.list := by
  exact edge_identity (B := (2:ℤ)^361) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000100011 : Branch 1 (-8261639/500000 : ℚ) vp00000000010001 := by
  apply branch_checked idp000000000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-8261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-8511639/250000 : ℚ) by norm_num]
  exact coverp000000000100011
theorem coverp00000000010001 : Covers (-8261639/500000 : ℚ) vp00000000010001 := join_branches bp000000000100010 bp000000000100011
private noncomputable def vp00000000010000111_0 : Blocks := edgeBlocks% "full/vectors/00000000010000111-V-0000.bin"
noncomputable def vp00000000010000111 : Blocks := vp00000000010000111_0
theorem coverp00000000010000111 : Covers (-8199139/62500 : ℚ) vp00000000010000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000010000110_0 : Blocks := edgeBlocks% "full/vectors/00000000010000110-V-0000.bin"
noncomputable def vp00000000010000110 : Blocks := vp00000000010000110_0
theorem coverp00000000010000110 : Covers (-8136639/62500 : ℚ) vp00000000010000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001000011_0 : Blocks := edgeBlocks% "full/vectors/0000000001000011-V-0000.bin"
noncomputable def vp0000000001000011 : Blocks := vp0000000001000011_0
private theorem bp00000000010000110 : Branch 0 (-8136639/125000 : ℚ) vp0000000001000011 := by
  apply branch_left_normalized (c:=vp00000000010000110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-8136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-8136639/62500 : ℚ) by norm_num]
  exact coverp00000000010000110
private noncomputable def ep00000000010000111_0 : Blocks := edgeBlocks% "full/vectors/00000000010000111-E-0000.bin"
noncomputable def ep00000000010000111 : Blocks := ep00000000010000111_0
private theorem idp00000000010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001000011.list =
    C ((2:ℤ)^58) * horner X vp00000000010000111.list + horner X ep00000000010000111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010000111 : Branch 1 (-8136639/125000 : ℚ) vp0000000001000011 := by
  apply branch_checked idp00000000010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-8136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-8199139/62500 : ℚ) by norm_num]
  exact coverp00000000010000111
theorem coverp0000000001000011 : Covers (-8136639/125000 : ℚ) vp0000000001000011 := join_branches bp00000000010000110 bp00000000010000111
private noncomputable def vp00000000010000101_0 : Blocks := edgeBlocks% "full/vectors/00000000010000101-V-0000.bin"
noncomputable def vp00000000010000101 : Blocks := vp00000000010000101_0
theorem coverp00000000010000101 : Covers (-8074139/62500 : ℚ) vp00000000010000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000010000100_0 : Blocks := edgeBlocks% "full/vectors/00000000010000100-V-0000.bin"
noncomputable def vp00000000010000100 : Blocks := vp00000000010000100_0
theorem coverp00000000010000100 : Covers (-8011639/62500 : ℚ) vp00000000010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001000010_0 : Blocks := edgeBlocks% "full/vectors/0000000001000010-V-0000.bin"
noncomputable def vp0000000001000010 : Blocks := vp0000000001000010_0
private theorem bp00000000010000100 : Branch 0 (-8011639/125000 : ℚ) vp0000000001000010 := by
  apply branch_left_normalized (c:=vp00000000010000100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-8011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-8011639/62500 : ℚ) by norm_num]
  exact coverp00000000010000100
private noncomputable def ep00000000010000101_0 : Blocks := edgeBlocks% "full/vectors/00000000010000101-E-0000.bin"
noncomputable def ep00000000010000101 : Blocks := ep00000000010000101_0
private theorem idp00000000010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001000010.list =
    C ((2:ℤ)^58) * horner X vp00000000010000101.list + horner X ep00000000010000101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010000101 : Branch 1 (-8011639/125000 : ℚ) vp0000000001000010 := by
  apply branch_checked idp00000000010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-8011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-8074139/62500 : ℚ) by norm_num]
  exact coverp00000000010000101
theorem coverp0000000001000010 : Covers (-8011639/125000 : ℚ) vp0000000001000010 := join_branches bp00000000010000100 bp00000000010000101
private noncomputable def vp000000000100001_0 : Blocks := edgeBlocks% "full/vectors/000000000100001-V-0000.bin"
noncomputable def vp000000000100001 : Blocks := vp000000000100001_0
private theorem bp0000000001000010 : Branch 0 (-8011639/250000 : ℚ) vp000000000100001 := by
  apply branch_left_normalized (c:=vp0000000001000010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-8011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-8011639/125000 : ℚ) by norm_num]
  exact coverp0000000001000010
private noncomputable def ep0000000001000011_0 : Blocks := edgeBlocks% "full/vectors/0000000001000011-E-0000.bin"
noncomputable def ep0000000001000011 : Blocks := ep0000000001000011_0
private theorem idp0000000001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000100001.list =
    C ((2:ℤ)^102) * horner X vp0000000001000011.list + horner X ep0000000001000011.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001000011 : Branch 1 (-8011639/250000 : ℚ) vp000000000100001 := by
  apply branch_checked idp0000000001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-8011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-8136639/125000 : ℚ) by norm_num]
  exact coverp0000000001000011
theorem coverp000000000100001 : Covers (-8011639/250000 : ℚ) vp000000000100001 := join_branches bp0000000001000010 bp0000000001000011
private noncomputable def vp00000000010000011_0 : Blocks := edgeBlocks% "full/vectors/00000000010000011-V-0000.bin"
noncomputable def vp00000000010000011 : Blocks := vp00000000010000011_0
theorem coverp00000000010000011 : Covers (-7949139/62500 : ℚ) vp00000000010000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000010000010_0 : Blocks := edgeBlocks% "full/vectors/00000000010000010-V-0000.bin"
noncomputable def vp00000000010000010 : Blocks := vp00000000010000010_0
theorem coverp00000000010000010 : Covers (-7886639/62500 : ℚ) vp00000000010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001000001_0 : Blocks := edgeBlocks% "full/vectors/0000000001000001-V-0000.bin"
noncomputable def vp0000000001000001 : Blocks := vp0000000001000001_0
private theorem bp00000000010000010 : Branch 0 (-7886639/125000 : ℚ) vp0000000001000001 := by
  apply branch_left_normalized (c:=vp00000000010000010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-7886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-7886639/62500 : ℚ) by norm_num]
  exact coverp00000000010000010
private noncomputable def ep00000000010000011_0 : Blocks := edgeBlocks% "full/vectors/00000000010000011-E-0000.bin"
noncomputable def ep00000000010000011 : Blocks := ep00000000010000011_0
private theorem idp00000000010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001000001.list =
    C ((2:ℤ)^58) * horner X vp00000000010000011.list + horner X ep00000000010000011.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010000011 : Branch 1 (-7886639/125000 : ℚ) vp0000000001000001 := by
  apply branch_checked idp00000000010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-7886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-7949139/62500 : ℚ) by norm_num]
  exact coverp00000000010000011
theorem coverp0000000001000001 : Covers (-7886639/125000 : ℚ) vp0000000001000001 := join_branches bp00000000010000010 bp00000000010000011
private noncomputable def vp0000000001000000_0 : Blocks := edgeBlocks% "full/vectors/0000000001000000-V-0000.bin"
noncomputable def vp0000000001000000 : Blocks := vp0000000001000000_0
theorem coverp0000000001000000 : Covers (-7761639/125000 : ℚ) vp0000000001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000100000_0 : Blocks := edgeBlocks% "full/vectors/000000000100000-V-0000.bin"
noncomputable def vp000000000100000 : Blocks := vp000000000100000_0
private theorem bp0000000001000000 : Branch 0 (-7761639/250000 : ℚ) vp000000000100000 := by
  apply branch_left_normalized (c:=vp0000000001000000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-7761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-7761639/125000 : ℚ) by norm_num]
  exact coverp0000000001000000
private noncomputable def ep0000000001000001_0 : Blocks := edgeBlocks% "full/vectors/0000000001000001-E-0000.bin"
noncomputable def ep0000000001000001 : Blocks := ep0000000001000001_0
private theorem idp0000000001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000100000.list =
    C ((2:ℤ)^104) * horner X vp0000000001000001.list + horner X ep0000000001000001.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001000001 : Branch 1 (-7761639/250000 : ℚ) vp000000000100000 := by
  apply branch_checked idp0000000001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-7761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-7886639/125000 : ℚ) by norm_num]
  exact coverp0000000001000001
theorem coverp000000000100000 : Covers (-7761639/250000 : ℚ) vp000000000100000 := join_branches bp0000000001000000 bp0000000001000001
private noncomputable def vp00000000010000_0 : Blocks := edgeBlocks% "full/vectors/00000000010000-V-0000.bin"
private noncomputable def vp00000000010000_1 : Blocks := edgeBlocks% "full/vectors/00000000010000-V-0001.bin"
noncomputable def vp00000000010000 : Blocks := (Blocks.join vp00000000010000_0 vp00000000010000_1)
private theorem bp000000000100000 : Branch 0 (-7761639/500000 : ℚ) vp00000000010000 := by
  apply branch_left_normalized (c:=vp000000000100000) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-7761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-7761639/250000 : ℚ) by norm_num]
  exact coverp000000000100000
private noncomputable def ep000000000100001_0 : Blocks := edgeBlocks% "full/vectors/000000000100001-E-0000.bin"
private noncomputable def ep000000000100001_1 : Blocks := edgeBlocks% "full/vectors/000000000100001-E-0001.bin"
noncomputable def ep000000000100001 : Blocks := (Blocks.join ep000000000100001_0 ep000000000100001_1)
private theorem idp000000000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000010000.list =
    C ((2:ℤ)^192) * horner X vp000000000100001.list + horner X ep000000000100001.list := by
  exact edge_identity (B := (2:ℤ)^372) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000100001 : Branch 1 (-7761639/500000 : ℚ) vp00000000010000 := by
  apply branch_checked idp000000000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-7761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-8011639/250000 : ℚ) by norm_num]
  exact coverp000000000100001
theorem coverp00000000010000 : Covers (-7761639/500000 : ℚ) vp00000000010000 := join_branches bp000000000100000 bp000000000100001
private noncomputable def vp0000000001000_0 : Blocks := edgeBlocks% "full/vectors/0000000001000-V-0000.bin"
private noncomputable def vp0000000001000_1 : Blocks := edgeBlocks% "full/vectors/0000000001000-V-0001.bin"
private noncomputable def vp0000000001000_2 : Blocks := edgeBlocks% "full/vectors/0000000001000-V-0002.bin"
noncomputable def vp0000000001000 : Blocks := (Blocks.join vp0000000001000_0 (Blocks.join vp0000000001000_1 vp0000000001000_2))
private theorem bp00000000010000 : Branch 0 (-7761639/1000000 : ℚ) vp0000000001000 := by
  apply branch_left_normalized (c:=vp00000000010000) (k:=0) (m:=189) (by decide +kernel)
  rw [show 2*(-7761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-7761639/500000 : ℚ) by norm_num]
  exact coverp00000000010000
private noncomputable def ep00000000010001_0 : Blocks := edgeBlocks% "full/vectors/00000000010001-E-0000.bin"
private noncomputable def ep00000000010001_1 : Blocks := edgeBlocks% "full/vectors/00000000010001-E-0001.bin"
private noncomputable def ep00000000010001_2 : Blocks := edgeBlocks% "full/vectors/00000000010001-E-0002.bin"
noncomputable def ep00000000010001 : Blocks := (Blocks.join ep00000000010001_0 (Blocks.join ep00000000010001_1 ep00000000010001_2))
private theorem idp00000000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001000.list =
    C ((2:ℤ)^367) * horner X vp00000000010001.list + horner X ep00000000010001.list := by
  exact edge_identity (B := (2:ℤ)^637) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000010001 : Branch 1 (-7761639/1000000 : ℚ) vp0000000001000 := by
  apply branch_checked idp00000000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-7761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-8261639/500000 : ℚ) by norm_num]
  exact coverp00000000010001
theorem coverp0000000001000 : Covers (-7761639/1000000 : ℚ) vp0000000001000 := join_branches bp00000000010000 bp00000000010001
private noncomputable def vp000000000100_0 : Blocks := edgeBlocks% "full/vectors/000000000100-V-0000.bin"
private noncomputable def vp000000000100_1 : Blocks := edgeBlocks% "full/vectors/000000000100-V-0001.bin"
private noncomputable def vp000000000100_2 : Blocks := edgeBlocks% "full/vectors/000000000100-V-0002.bin"
private noncomputable def vp000000000100_3 : Blocks := edgeBlocks% "full/vectors/000000000100-V-0003.bin"
private noncomputable def vp000000000100_4 : Blocks := edgeBlocks% "full/vectors/000000000100-V-0004.bin"
private noncomputable def vp000000000100_5 : Blocks := edgeBlocks% "full/vectors/000000000100-V-0005.bin"
noncomputable def vp000000000100 : Blocks := (Blocks.join (Blocks.join vp000000000100_0 (Blocks.join vp000000000100_1 vp000000000100_2)) (Blocks.join vp000000000100_3 (Blocks.join vp000000000100_4 vp000000000100_5)))
private theorem bp0000000001000 : Branch 0 (-7761639/2000000 : ℚ) vp000000000100 := by
  apply branch_left_normalized (c:=vp0000000001000) (k:=0) (m:=362) (by decide +kernel)
  rw [show 2*(-7761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-7761639/1000000 : ℚ) by norm_num]
  exact coverp0000000001000
private noncomputable def ep0000000001001_0 : Blocks := edgeBlocks% "full/vectors/0000000001001-E-0000.bin"
private noncomputable def ep0000000001001_1 : Blocks := edgeBlocks% "full/vectors/0000000001001-E-0001.bin"
private noncomputable def ep0000000001001_2 : Blocks := edgeBlocks% "full/vectors/0000000001001-E-0002.bin"
private noncomputable def ep0000000001001_3 : Blocks := edgeBlocks% "full/vectors/0000000001001-E-0003.bin"
private noncomputable def ep0000000001001_4 : Blocks := edgeBlocks% "full/vectors/0000000001001-E-0004.bin"
private noncomputable def ep0000000001001_5 : Blocks := edgeBlocks% "full/vectors/0000000001001-E-0005.bin"
noncomputable def ep0000000001001 : Blocks := (Blocks.join (Blocks.join ep0000000001001_0 (Blocks.join ep0000000001001_1 ep0000000001001_2)) (Blocks.join ep0000000001001_3 (Blocks.join ep0000000001001_4 ep0000000001001_5)))
private theorem idp0000000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000100.list =
    C ((2:ℤ)^712) * horner X vp0000000001001.list + horner X ep0000000001001.list := by
  exact edge_identity (B := (2:ℤ)^1162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001001 : Branch 1 (-7761639/2000000 : ℚ) vp000000000100 := by
  apply branch_checked idp0000000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-7761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-8761639/1000000 : ℚ) by norm_num]
  exact coverp0000000001001
theorem coverp000000000100 : Covers (-7761639/2000000 : ℚ) vp000000000100 := join_branches bp0000000001000 bp0000000001001
private noncomputable def vp00000000010_0 : Blocks := edgeBlocks% "full/vectors/00000000010-V-0000.bin"
private noncomputable def vp00000000010_1 : Blocks := edgeBlocks% "full/vectors/00000000010-V-0001.bin"
private noncomputable def vp00000000010_2 : Blocks := edgeBlocks% "full/vectors/00000000010-V-0002.bin"
private noncomputable def vp00000000010_3 : Blocks := edgeBlocks% "full/vectors/00000000010-V-0003.bin"
private noncomputable def vp00000000010_4 : Blocks := edgeBlocks% "full/vectors/00000000010-V-0004.bin"
private noncomputable def vp00000000010_5 : Blocks := edgeBlocks% "full/vectors/00000000010-V-0005.bin"
private noncomputable def vp00000000010_6 : Blocks := edgeBlocks% "full/vectors/00000000010-V-0006.bin"
private noncomputable def vp00000000010_7 : Blocks := edgeBlocks% "full/vectors/00000000010-V-0007.bin"
private noncomputable def vp00000000010_8 : Blocks := edgeBlocks% "full/vectors/00000000010-V-0008.bin"
private noncomputable def vp00000000010_9 : Blocks := edgeBlocks% "full/vectors/00000000010-V-0009.bin"
private noncomputable def vp00000000010_10 : Blocks := edgeBlocks% "full/vectors/00000000010-V-0010.bin"
noncomputable def vp00000000010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00000000010_0 vp00000000010_1) (Blocks.join vp00000000010_2 (Blocks.join vp00000000010_3 vp00000000010_4))) (Blocks.join (Blocks.join vp00000000010_5 (Blocks.join vp00000000010_6 vp00000000010_7)) (Blocks.join vp00000000010_8 (Blocks.join vp00000000010_9 vp00000000010_10))))
private theorem bp000000000100 : Branch 0 (-7761639/4000000 : ℚ) vp00000000010 := by
  apply branch_left_normalized (c:=vp000000000100) (k:=0) (m:=703) (by decide +kernel)
  rw [show 2*(-7761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-7761639/2000000 : ℚ) by norm_num]
  exact coverp000000000100
private noncomputable def ep000000000101_0 : Blocks := edgeBlocks% "full/vectors/000000000101-E-0000.bin"
private noncomputable def ep000000000101_1 : Blocks := edgeBlocks% "full/vectors/000000000101-E-0001.bin"
private noncomputable def ep000000000101_2 : Blocks := edgeBlocks% "full/vectors/000000000101-E-0002.bin"
private noncomputable def ep000000000101_3 : Blocks := edgeBlocks% "full/vectors/000000000101-E-0003.bin"
private noncomputable def ep000000000101_4 : Blocks := edgeBlocks% "full/vectors/000000000101-E-0004.bin"
private noncomputable def ep000000000101_5 : Blocks := edgeBlocks% "full/vectors/000000000101-E-0005.bin"
private noncomputable def ep000000000101_6 : Blocks := edgeBlocks% "full/vectors/000000000101-E-0006.bin"
private noncomputable def ep000000000101_7 : Blocks := edgeBlocks% "full/vectors/000000000101-E-0007.bin"
private noncomputable def ep000000000101_8 : Blocks := edgeBlocks% "full/vectors/000000000101-E-0008.bin"
private noncomputable def ep000000000101_9 : Blocks := edgeBlocks% "full/vectors/000000000101-E-0009.bin"
private noncomputable def ep000000000101_10 : Blocks := edgeBlocks% "full/vectors/000000000101-E-0010.bin"
noncomputable def ep000000000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000000000101_0 ep000000000101_1) (Blocks.join ep000000000101_2 (Blocks.join ep000000000101_3 ep000000000101_4))) (Blocks.join (Blocks.join ep000000000101_5 (Blocks.join ep000000000101_6 ep000000000101_7)) (Blocks.join ep000000000101_8 (Blocks.join ep000000000101_9 ep000000000101_10))))
private theorem idp000000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000010.list =
    C ((2:ℤ)^1391) * horner X vp000000000101.list + horner X ep000000000101.list := by
  exact edge_identity (B := (2:ℤ)^2201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000101 : Branch 1 (-7761639/4000000 : ℚ) vp00000000010 := by
  apply branch_checked idp000000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-7761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-9761639/2000000 : ℚ) by norm_num]
  exact coverp000000000101
theorem coverp00000000010 : Covers (-7761639/4000000 : ℚ) vp00000000010 := join_branches bp000000000100 bp000000000101
private noncomputable def vp0000000001_0 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0000.bin"
private noncomputable def vp0000000001_1 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0001.bin"
private noncomputable def vp0000000001_2 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0002.bin"
private noncomputable def vp0000000001_3 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0003.bin"
private noncomputable def vp0000000001_4 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0004.bin"
private noncomputable def vp0000000001_5 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0005.bin"
private noncomputable def vp0000000001_6 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0006.bin"
private noncomputable def vp0000000001_7 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0007.bin"
private noncomputable def vp0000000001_8 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0008.bin"
private noncomputable def vp0000000001_9 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0009.bin"
private noncomputable def vp0000000001_10 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0010.bin"
private noncomputable def vp0000000001_11 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0011.bin"
private noncomputable def vp0000000001_12 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0012.bin"
private noncomputable def vp0000000001_13 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0013.bin"
private noncomputable def vp0000000001_14 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0014.bin"
private noncomputable def vp0000000001_15 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0015.bin"
private noncomputable def vp0000000001_16 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0016.bin"
private noncomputable def vp0000000001_17 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0017.bin"
private noncomputable def vp0000000001_18 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0018.bin"
private noncomputable def vp0000000001_19 : Blocks := edgeBlocks% "full/vectors/0000000001-V-0019.bin"
noncomputable def vp0000000001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000000001_0 vp0000000001_1) (Blocks.join vp0000000001_2 (Blocks.join vp0000000001_3 vp0000000001_4))) (Blocks.join (Blocks.join vp0000000001_5 vp0000000001_6) (Blocks.join vp0000000001_7 (Blocks.join vp0000000001_8 vp0000000001_9)))) (Blocks.join (Blocks.join (Blocks.join vp0000000001_10 vp0000000001_11) (Blocks.join vp0000000001_12 (Blocks.join vp0000000001_13 vp0000000001_14))) (Blocks.join (Blocks.join vp0000000001_15 vp0000000001_16) (Blocks.join vp0000000001_17 (Blocks.join vp0000000001_18 vp0000000001_19)))))
private theorem bp00000000010 : Branch 0 (-7761639/8000000 : ℚ) vp0000000001 := by
  apply branch_left_normalized (c:=vp00000000010) (k:=0) (m:=1377) (by decide +kernel)
  rw [show 2*(-7761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-7761639/4000000 : ℚ) by norm_num]
  exact coverp00000000010
private noncomputable def ep00000000011_0 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0000.bin"
private noncomputable def ep00000000011_1 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0001.bin"
private noncomputable def ep00000000011_2 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0002.bin"
private noncomputable def ep00000000011_3 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0003.bin"
private noncomputable def ep00000000011_4 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0004.bin"
private noncomputable def ep00000000011_5 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0005.bin"
private noncomputable def ep00000000011_6 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0006.bin"
private noncomputable def ep00000000011_7 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0007.bin"
private noncomputable def ep00000000011_8 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0008.bin"
private noncomputable def ep00000000011_9 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0009.bin"
private noncomputable def ep00000000011_10 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0010.bin"
private noncomputable def ep00000000011_11 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0011.bin"
private noncomputable def ep00000000011_12 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0012.bin"
private noncomputable def ep00000000011_13 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0013.bin"
private noncomputable def ep00000000011_14 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0014.bin"
private noncomputable def ep00000000011_15 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0015.bin"
private noncomputable def ep00000000011_16 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0016.bin"
private noncomputable def ep00000000011_17 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0017.bin"
private noncomputable def ep00000000011_18 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0018.bin"
private noncomputable def ep00000000011_19 : Blocks := edgeBlocks% "full/vectors/00000000011-E-0019.bin"
noncomputable def ep00000000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00000000011_0 ep00000000011_1) (Blocks.join ep00000000011_2 (Blocks.join ep00000000011_3 ep00000000011_4))) (Blocks.join (Blocks.join ep00000000011_5 ep00000000011_6) (Blocks.join ep00000000011_7 (Blocks.join ep00000000011_8 ep00000000011_9)))) (Blocks.join (Blocks.join (Blocks.join ep00000000011_10 ep00000000011_11) (Blocks.join ep00000000011_12 (Blocks.join ep00000000011_13 ep00000000011_14))) (Blocks.join (Blocks.join ep00000000011_15 ep00000000011_16) (Blocks.join ep00000000011_17 (Blocks.join ep00000000011_18 ep00000000011_19)))))
private theorem idp00000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001.list =
    C ((2:ℤ)^2468) * horner X vp00000000011.list + horner X ep00000000011.list := by
  exact edge_identity (B := (2:ℤ)^4001) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011 : Branch 1 (-7761639/8000000 : ℚ) vp0000000001 := by
  apply branch_checked idp00000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-7761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-11761639/4000000 : ℚ) by norm_num]
  exact coverp00000000011
theorem coverp0000000001 : Covers (-7761639/8000000 : ℚ) vp0000000001 := join_branches bp00000000010 bp00000000011
end NextProof.EdgeFull

