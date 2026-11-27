import NextProof.LeftKernel
import NextProof.OptEdge00007Cert
import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00006

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000000000000111111_0 : Blocks := edgeBlocks% "full/vectors/000000000000111111-V-0000.bin"
noncomputable def vp000000000000111111 : Blocks := vp000000000000111111_0
theorem coverp000000000000111111 : Covers (-1730389/31250 : ℚ) vp000000000000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000111110_0 : Blocks := edgeBlocks% "full/vectors/000000000000111110-V-0000.bin"
noncomputable def vp000000000000111110 : Blocks := vp000000000000111110_0
theorem coverp000000000000111110 : Covers (-1699139/31250 : ℚ) vp000000000000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000011111_0 : Blocks := edgeBlocks% "full/vectors/00000000000011111-V-0000.bin"
noncomputable def vp00000000000011111 : Blocks := vp00000000000011111_0
private theorem bp000000000000111110 : Branch 0 (-1699139/62500 : ℚ) vp00000000000011111 := by
  apply branch_left_normalized (c:=vp000000000000111110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-1699139/62500 : ℚ) - ((0:ℤ):ℚ) = (-1699139/31250 : ℚ) by norm_num]
  exact coverp000000000000111110
private noncomputable def ep000000000000111111_0 : Blocks := edgeBlocks% "full/vectors/000000000000111111-E-0000.bin"
noncomputable def ep000000000000111111 : Blocks := ep000000000000111111_0
private theorem idp000000000000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000011111.list =
    C ((2:ℤ)^58) * horner X vp000000000000111111.list + horner X ep000000000000111111.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000111111 : Branch 1 (-1699139/62500 : ℚ) vp00000000000011111 := by
  apply branch_checked idp000000000000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1699139/62500 : ℚ) - ((1:ℤ):ℚ) = (-1730389/31250 : ℚ) by norm_num]
  exact coverp000000000000111111
theorem coverp00000000000011111 : Covers (-1699139/62500 : ℚ) vp00000000000011111 := join_branches bp000000000000111110 bp000000000000111111
private noncomputable def vp000000000000111101_0 : Blocks := edgeBlocks% "full/vectors/000000000000111101-V-0000.bin"
noncomputable def vp000000000000111101 : Blocks := vp000000000000111101_0
theorem coverp000000000000111101 : Covers (-1667889/31250 : ℚ) vp000000000000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000111100_0 : Blocks := edgeBlocks% "full/vectors/000000000000111100-V-0000.bin"
noncomputable def vp000000000000111100 : Blocks := vp000000000000111100_0
theorem coverp000000000000111100 : Covers (-1636639/31250 : ℚ) vp000000000000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000011110_0 : Blocks := edgeBlocks% "full/vectors/00000000000011110-V-0000.bin"
noncomputable def vp00000000000011110 : Blocks := vp00000000000011110_0
private theorem bp000000000000111100 : Branch 0 (-1636639/62500 : ℚ) vp00000000000011110 := by
  apply branch_left_normalized (c:=vp000000000000111100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-1636639/62500 : ℚ) - ((0:ℤ):ℚ) = (-1636639/31250 : ℚ) by norm_num]
  exact coverp000000000000111100
private noncomputable def ep000000000000111101_0 : Blocks := edgeBlocks% "full/vectors/000000000000111101-E-0000.bin"
noncomputable def ep000000000000111101 : Blocks := ep000000000000111101_0
private theorem idp000000000000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000011110.list =
    C ((2:ℤ)^58) * horner X vp000000000000111101.list + horner X ep000000000000111101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000111101 : Branch 1 (-1636639/62500 : ℚ) vp00000000000011110 := by
  apply branch_checked idp000000000000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1636639/62500 : ℚ) - ((1:ℤ):ℚ) = (-1667889/31250 : ℚ) by norm_num]
  exact coverp000000000000111101
theorem coverp00000000000011110 : Covers (-1636639/62500 : ℚ) vp00000000000011110 := join_branches bp000000000000111100 bp000000000000111101
private noncomputable def vp0000000000001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000001111-V-0000.bin"
noncomputable def vp0000000000001111 : Blocks := vp0000000000001111_0
private theorem bp00000000000011110 : Branch 0 (-1636639/125000 : ℚ) vp0000000000001111 := by
  apply branch_left_normalized (c:=vp00000000000011110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-1636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-1636639/62500 : ℚ) by norm_num]
  exact coverp00000000000011110
private noncomputable def ep00000000000011111_0 : Blocks := edgeBlocks% "full/vectors/00000000000011111-E-0000.bin"
noncomputable def ep00000000000011111 : Blocks := ep00000000000011111_0
private theorem idp00000000000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000001111.list =
    C ((2:ℤ)^105) * horner X vp00000000000011111.list + horner X ep00000000000011111.list := by
  exact edge_identity (B := (2:ℤ)^240) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000011111 : Branch 1 (-1636639/125000 : ℚ) vp0000000000001111 := by
  apply branch_checked idp00000000000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-1699139/62500 : ℚ) by norm_num]
  exact coverp00000000000011111
theorem coverp0000000000001111 : Covers (-1636639/125000 : ℚ) vp0000000000001111 := join_branches bp00000000000011110 bp00000000000011111
private noncomputable def vp000000000000111011_0 : Blocks := edgeBlocks% "full/vectors/000000000000111011-V-0000.bin"
noncomputable def vp000000000000111011 : Blocks := vp000000000000111011_0
theorem coverp000000000000111011 : Covers (-1605389/31250 : ℚ) vp000000000000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000111010_0 : Blocks := edgeBlocks% "full/vectors/000000000000111010-V-0000.bin"
noncomputable def vp000000000000111010 : Blocks := vp000000000000111010_0
theorem coverp000000000000111010 : Covers (-1574139/31250 : ℚ) vp000000000000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000011101_0 : Blocks := edgeBlocks% "full/vectors/00000000000011101-V-0000.bin"
noncomputable def vp00000000000011101 : Blocks := vp00000000000011101_0
private theorem bp000000000000111010 : Branch 0 (-1574139/62500 : ℚ) vp00000000000011101 := by
  apply branch_left_normalized (c:=vp000000000000111010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-1574139/62500 : ℚ) - ((0:ℤ):ℚ) = (-1574139/31250 : ℚ) by norm_num]
  exact coverp000000000000111010
private noncomputable def ep000000000000111011_0 : Blocks := edgeBlocks% "full/vectors/000000000000111011-E-0000.bin"
noncomputable def ep000000000000111011 : Blocks := ep000000000000111011_0
private theorem idp000000000000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000011101.list =
    C ((2:ℤ)^59) * horner X vp000000000000111011.list + horner X ep000000000000111011.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000111011 : Branch 1 (-1574139/62500 : ℚ) vp00000000000011101 := by
  apply branch_checked idp000000000000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1574139/62500 : ℚ) - ((1:ℤ):ℚ) = (-1605389/31250 : ℚ) by norm_num]
  exact coverp000000000000111011
theorem coverp00000000000011101 : Covers (-1574139/62500 : ℚ) vp00000000000011101 := join_branches bp000000000000111010 bp000000000000111011
private noncomputable def vp000000000000111001_0 : Blocks := edgeBlocks% "full/vectors/000000000000111001-V-0000.bin"
noncomputable def vp000000000000111001 : Blocks := vp000000000000111001_0
theorem coverp000000000000111001 : Covers (-1542889/31250 : ℚ) vp000000000000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000111000_0 : Blocks := edgeBlocks% "full/vectors/000000000000111000-V-0000.bin"
noncomputable def vp000000000000111000 : Blocks := vp000000000000111000_0
theorem coverp000000000000111000 : Covers (-1511639/31250 : ℚ) vp000000000000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000011100_0 : Blocks := edgeBlocks% "full/vectors/00000000000011100-V-0000.bin"
noncomputable def vp00000000000011100 : Blocks := vp00000000000011100_0
private theorem bp000000000000111000 : Branch 0 (-1511639/62500 : ℚ) vp00000000000011100 := by
  apply branch_left_normalized (c:=vp000000000000111000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-1511639/62500 : ℚ) - ((0:ℤ):ℚ) = (-1511639/31250 : ℚ) by norm_num]
  exact coverp000000000000111000
private noncomputable def ep000000000000111001_0 : Blocks := edgeBlocks% "full/vectors/000000000000111001-E-0000.bin"
noncomputable def ep000000000000111001 : Blocks := ep000000000000111001_0
private theorem idp000000000000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000011100.list =
    C ((2:ℤ)^60) * horner X vp000000000000111001.list + horner X ep000000000000111001.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000111001 : Branch 1 (-1511639/62500 : ℚ) vp00000000000011100 := by
  apply branch_checked idp000000000000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1511639/62500 : ℚ) - ((1:ℤ):ℚ) = (-1542889/31250 : ℚ) by norm_num]
  exact coverp000000000000111001
theorem coverp00000000000011100 : Covers (-1511639/62500 : ℚ) vp00000000000011100 := join_branches bp000000000000111000 bp000000000000111001
private noncomputable def vp0000000000001110_0 : Blocks := edgeBlocks% "full/vectors/0000000000001110-V-0000.bin"
noncomputable def vp0000000000001110 : Blocks := vp0000000000001110_0
private theorem bp00000000000011100 : Branch 0 (-1511639/125000 : ℚ) vp0000000000001110 := by
  apply branch_left_normalized (c:=vp00000000000011100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-1511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-1511639/62500 : ℚ) by norm_num]
  exact coverp00000000000011100
private noncomputable def ep00000000000011101_0 : Blocks := edgeBlocks% "full/vectors/00000000000011101-E-0000.bin"
noncomputable def ep00000000000011101 : Blocks := ep00000000000011101_0
private theorem idp00000000000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000001110.list =
    C ((2:ℤ)^107) * horner X vp00000000000011101.list + horner X ep00000000000011101.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000011101 : Branch 1 (-1511639/125000 : ℚ) vp0000000000001110 := by
  apply branch_checked idp00000000000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-1574139/62500 : ℚ) by norm_num]
  exact coverp00000000000011101
theorem coverp0000000000001110 : Covers (-1511639/125000 : ℚ) vp0000000000001110 := join_branches bp00000000000011100 bp00000000000011101
private noncomputable def vp000000000000111_0 : Blocks := edgeBlocks% "full/vectors/000000000000111-V-0000.bin"
private noncomputable def vp000000000000111_1 : Blocks := edgeBlocks% "full/vectors/000000000000111-V-0001.bin"
noncomputable def vp000000000000111 : Blocks := (Blocks.join vp000000000000111_0 vp000000000000111_1)
private theorem bp0000000000001110 : Branch 0 (-1511639/250000 : ℚ) vp000000000000111 := by
  apply branch_left_normalized (c:=vp0000000000001110) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-1511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-1511639/125000 : ℚ) by norm_num]
  exact coverp0000000000001110
private noncomputable def ep0000000000001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000001111-E-0000.bin"
private noncomputable def ep0000000000001111_1 : Blocks := edgeBlocks% "full/vectors/0000000000001111-E-0001.bin"
noncomputable def ep0000000000001111 : Blocks := (Blocks.join ep0000000000001111_0 ep0000000000001111_1)
private theorem idp0000000000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000111.list =
    C ((2:ℤ)^200) * horner X vp0000000000001111.list + horner X ep0000000000001111.list := by
  exact edge_identity (B := (2:ℤ)^386) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000001111 : Branch 1 (-1511639/250000 : ℚ) vp000000000000111 := by
  apply branch_checked idp0000000000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-1636639/125000 : ℚ) by norm_num]
  exact coverp0000000000001111
theorem coverp000000000000111 : Covers (-1511639/250000 : ℚ) vp000000000000111 := join_branches bp0000000000001110 bp0000000000001111
private noncomputable def vp00000000000011011_0 : Blocks := edgeBlocks% "full/vectors/00000000000011011-V-0000.bin"
noncomputable def vp00000000000011011 : Blocks := vp00000000000011011_0
theorem coverp00000000000011011 : Covers (-1449139/62500 : ℚ) vp00000000000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000011010_0 : Blocks := edgeBlocks% "full/vectors/00000000000011010-V-0000.bin"
noncomputable def vp00000000000011010 : Blocks := vp00000000000011010_0
theorem coverp00000000000011010 : Covers (-1386639/62500 : ℚ) vp00000000000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000001101-V-0000.bin"
noncomputable def vp0000000000001101 : Blocks := vp0000000000001101_0
private theorem bp00000000000011010 : Branch 0 (-1386639/125000 : ℚ) vp0000000000001101 := by
  apply branch_left_normalized (c:=vp00000000000011010) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-1386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-1386639/62500 : ℚ) by norm_num]
  exact coverp00000000000011010
private noncomputable def ep00000000000011011_0 : Blocks := edgeBlocks% "full/vectors/00000000000011011-E-0000.bin"
noncomputable def ep00000000000011011 : Blocks := ep00000000000011011_0
private theorem idp00000000000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000001101.list =
    C ((2:ℤ)^111) * horner X vp00000000000011011.list + horner X ep00000000000011011.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000011011 : Branch 1 (-1386639/125000 : ℚ) vp0000000000001101 := by
  apply branch_checked idp00000000000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-1449139/62500 : ℚ) by norm_num]
  exact coverp00000000000011011
theorem coverp0000000000001101 : Covers (-1386639/125000 : ℚ) vp0000000000001101 := join_branches bp00000000000011010 bp00000000000011011
private noncomputable def vp000000000000110011_0 : Blocks := edgeBlocks% "full/vectors/000000000000110011-V-0000.bin"
noncomputable def vp000000000000110011 : Blocks := vp000000000000110011_0
theorem coverp000000000000110011 : Covers (-1355389/31250 : ℚ) vp000000000000110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000110010_0 : Blocks := edgeBlocks% "full/vectors/000000000000110010-V-0000.bin"
noncomputable def vp000000000000110010 : Blocks := vp000000000000110010_0
theorem coverp000000000000110010 : Covers (-1324139/31250 : ℚ) vp000000000000110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000011001_0 : Blocks := edgeBlocks% "full/vectors/00000000000011001-V-0000.bin"
noncomputable def vp00000000000011001 : Blocks := vp00000000000011001_0
private theorem bp000000000000110010 : Branch 0 (-1324139/62500 : ℚ) vp00000000000011001 := by
  apply branch_left_normalized (c:=vp000000000000110010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-1324139/62500 : ℚ) - ((0:ℤ):ℚ) = (-1324139/31250 : ℚ) by norm_num]
  exact coverp000000000000110010
private noncomputable def ep000000000000110011_0 : Blocks := edgeBlocks% "full/vectors/000000000000110011-E-0000.bin"
noncomputable def ep000000000000110011 : Blocks := ep000000000000110011_0
private theorem idp000000000000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000011001.list =
    C ((2:ℤ)^63) * horner X vp000000000000110011.list + horner X ep000000000000110011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000110011 : Branch 1 (-1324139/62500 : ℚ) vp00000000000011001 := by
  apply branch_checked idp000000000000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1324139/62500 : ℚ) - ((1:ℤ):ℚ) = (-1355389/31250 : ℚ) by norm_num]
  exact coverp000000000000110011
theorem coverp00000000000011001 : Covers (-1324139/62500 : ℚ) vp00000000000011001 := join_branches bp000000000000110010 bp000000000000110011
private noncomputable def vp000000000000110001_0 : Blocks := edgeBlocks% "full/vectors/000000000000110001-V-0000.bin"
noncomputable def vp000000000000110001 : Blocks := vp000000000000110001_0
theorem coverp000000000000110001 : Covers (-1292889/31250 : ℚ) vp000000000000110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000110000_0 : Blocks := edgeBlocks% "full/vectors/000000000000110000-V-0000.bin"
noncomputable def vp000000000000110000 : Blocks := vp000000000000110000_0
theorem coverp000000000000110000 : Covers (-1261639/31250 : ℚ) vp000000000000110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000011000_0 : Blocks := edgeBlocks% "full/vectors/00000000000011000-V-0000.bin"
noncomputable def vp00000000000011000 : Blocks := vp00000000000011000_0
private theorem bp000000000000110000 : Branch 0 (-1261639/62500 : ℚ) vp00000000000011000 := by
  apply branch_left_normalized (c:=vp000000000000110000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-1261639/62500 : ℚ) - ((0:ℤ):ℚ) = (-1261639/31250 : ℚ) by norm_num]
  exact coverp000000000000110000
private noncomputable def ep000000000000110001_0 : Blocks := edgeBlocks% "full/vectors/000000000000110001-E-0000.bin"
noncomputable def ep000000000000110001 : Blocks := ep000000000000110001_0
private theorem idp000000000000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000011000.list =
    C ((2:ℤ)^64) * horner X vp000000000000110001.list + horner X ep000000000000110001.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000110001 : Branch 1 (-1261639/62500 : ℚ) vp00000000000011000 := by
  apply branch_checked idp000000000000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1261639/62500 : ℚ) - ((1:ℤ):ℚ) = (-1292889/31250 : ℚ) by norm_num]
  exact coverp000000000000110001
theorem coverp00000000000011000 : Covers (-1261639/62500 : ℚ) vp00000000000011000 := join_branches bp000000000000110000 bp000000000000110001
private noncomputable def vp0000000000001100_0 : Blocks := edgeBlocks% "full/vectors/0000000000001100-V-0000.bin"
noncomputable def vp0000000000001100 : Blocks := vp0000000000001100_0
private theorem bp00000000000011000 : Branch 0 (-1261639/125000 : ℚ) vp0000000000001100 := by
  apply branch_left_normalized (c:=vp00000000000011000) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-1261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-1261639/62500 : ℚ) by norm_num]
  exact coverp00000000000011000
private noncomputable def ep00000000000011001_0 : Blocks := edgeBlocks% "full/vectors/00000000000011001-E-0000.bin"
noncomputable def ep00000000000011001 : Blocks := ep00000000000011001_0
private theorem idp00000000000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000001100.list =
    C ((2:ℤ)^116) * horner X vp00000000000011001.list + horner X ep00000000000011001.list := by
  exact edge_identity (B := (2:ℤ)^256) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000011001 : Branch 1 (-1261639/125000 : ℚ) vp0000000000001100 := by
  apply branch_checked idp00000000000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-1324139/62500 : ℚ) by norm_num]
  exact coverp00000000000011001
theorem coverp0000000000001100 : Covers (-1261639/125000 : ℚ) vp0000000000001100 := join_branches bp00000000000011000 bp00000000000011001
private noncomputable def vp000000000000110_0 : Blocks := edgeBlocks% "full/vectors/000000000000110-V-0000.bin"
private noncomputable def vp000000000000110_1 : Blocks := edgeBlocks% "full/vectors/000000000000110-V-0001.bin"
noncomputable def vp000000000000110 : Blocks := (Blocks.join vp000000000000110_0 vp000000000000110_1)
private theorem bp0000000000001100 : Branch 0 (-1261639/250000 : ℚ) vp000000000000110 := by
  apply branch_left_normalized (c:=vp0000000000001100) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-1261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-1261639/125000 : ℚ) by norm_num]
  exact coverp0000000000001100
private noncomputable def ep0000000000001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000001101-E-0000.bin"
private noncomputable def ep0000000000001101_1 : Blocks := edgeBlocks% "full/vectors/0000000000001101-E-0001.bin"
noncomputable def ep0000000000001101 : Blocks := (Blocks.join ep0000000000001101_0 ep0000000000001101_1)
private theorem idp0000000000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000110.list =
    C ((2:ℤ)^216) * horner X vp0000000000001101.list + horner X ep0000000000001101.list := by
  exact edge_identity (B := (2:ℤ)^409) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000001101 : Branch 1 (-1261639/250000 : ℚ) vp000000000000110 := by
  apply branch_checked idp0000000000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-1386639/125000 : ℚ) by norm_num]
  exact coverp0000000000001101
theorem coverp000000000000110 : Covers (-1261639/250000 : ℚ) vp000000000000110 := join_branches bp0000000000001100 bp0000000000001101
private noncomputable def vp00000000000011_0 : Blocks := edgeBlocks% "full/vectors/00000000000011-V-0000.bin"
private noncomputable def vp00000000000011_1 : Blocks := edgeBlocks% "full/vectors/00000000000011-V-0001.bin"
private noncomputable def vp00000000000011_2 : Blocks := edgeBlocks% "full/vectors/00000000000011-V-0002.bin"
private noncomputable def vp00000000000011_3 : Blocks := edgeBlocks% "full/vectors/00000000000011-V-0003.bin"
noncomputable def vp00000000000011 : Blocks := (Blocks.join (Blocks.join vp00000000000011_0 vp00000000000011_1) (Blocks.join vp00000000000011_2 vp00000000000011_3))
private theorem bp000000000000110 : Branch 0 (-1261639/500000 : ℚ) vp00000000000011 := by
  apply branch_left_normalized (c:=vp000000000000110) (k:=0) (m:=214) (by decide +kernel)
  rw [show 2*(-1261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-1261639/250000 : ℚ) by norm_num]
  exact coverp000000000000110
private noncomputable def ep000000000000111_0 : Blocks := edgeBlocks% "full/vectors/000000000000111-E-0000.bin"
private noncomputable def ep000000000000111_1 : Blocks := edgeBlocks% "full/vectors/000000000000111-E-0001.bin"
private noncomputable def ep000000000000111_2 : Blocks := edgeBlocks% "full/vectors/000000000000111-E-0002.bin"
private noncomputable def ep000000000000111_3 : Blocks := edgeBlocks% "full/vectors/000000000000111-E-0003.bin"
noncomputable def ep000000000000111 : Blocks := (Blocks.join (Blocks.join ep000000000000111_0 ep000000000000111_1) (Blocks.join ep000000000000111_2 ep000000000000111_3))
private theorem idp000000000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000011.list =
    C ((2:ℤ)^416) * horner X vp000000000000111.list + horner X ep000000000000111.list := by
  exact edge_identity (B := (2:ℤ)^714) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000111 : Branch 1 (-1261639/500000 : ℚ) vp00000000000011 := by
  apply branch_checked idp000000000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-1511639/250000 : ℚ) by norm_num]
  exact coverp000000000000111
theorem coverp00000000000011 : Covers (-1261639/500000 : ℚ) vp00000000000011 := join_branches bp000000000000110 bp000000000000111
private noncomputable def vp000000000000101111_0 : Blocks := edgeBlocks% "full/vectors/000000000000101111-V-0000.bin"
noncomputable def vp000000000000101111 : Blocks := vp000000000000101111_0
theorem coverp000000000000101111 : Covers (-1230389/31250 : ℚ) vp000000000000101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000101110_0 : Blocks := edgeBlocks% "full/vectors/000000000000101110-V-0000.bin"
noncomputable def vp000000000000101110 : Blocks := vp000000000000101110_0
theorem coverp000000000000101110 : Covers (-1199139/31250 : ℚ) vp000000000000101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000010111_0 : Blocks := edgeBlocks% "full/vectors/00000000000010111-V-0000.bin"
noncomputable def vp00000000000010111 : Blocks := vp00000000000010111_0
private theorem bp000000000000101110 : Branch 0 (-1199139/62500 : ℚ) vp00000000000010111 := by
  apply branch_left_normalized (c:=vp000000000000101110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-1199139/62500 : ℚ) - ((0:ℤ):ℚ) = (-1199139/31250 : ℚ) by norm_num]
  exact coverp000000000000101110
private noncomputable def ep000000000000101111_0 : Blocks := edgeBlocks% "full/vectors/000000000000101111-E-0000.bin"
noncomputable def ep000000000000101111 : Blocks := ep000000000000101111_0
private theorem idp000000000000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000010111.list =
    C ((2:ℤ)^65) * horner X vp000000000000101111.list + horner X ep000000000000101111.list := by
  exact edge_identity (B := (2:ℤ)^180) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000101111 : Branch 1 (-1199139/62500 : ℚ) vp00000000000010111 := by
  apply branch_checked idp000000000000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1199139/62500 : ℚ) - ((1:ℤ):ℚ) = (-1230389/31250 : ℚ) by norm_num]
  exact coverp000000000000101111
theorem coverp00000000000010111 : Covers (-1199139/62500 : ℚ) vp00000000000010111 := join_branches bp000000000000101110 bp000000000000101111
private noncomputable def vp000000000000101101_0 : Blocks := edgeBlocks% "full/vectors/000000000000101101-V-0000.bin"
noncomputable def vp000000000000101101 : Blocks := vp000000000000101101_0
theorem coverp000000000000101101 : Covers (-1167889/31250 : ℚ) vp000000000000101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000101100_0 : Blocks := edgeBlocks% "full/vectors/000000000000101100-V-0000.bin"
noncomputable def vp000000000000101100 : Blocks := vp000000000000101100_0
theorem coverp000000000000101100 : Covers (-1136639/31250 : ℚ) vp000000000000101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000010110_0 : Blocks := edgeBlocks% "full/vectors/00000000000010110-V-0000.bin"
noncomputable def vp00000000000010110 : Blocks := vp00000000000010110_0
private theorem bp000000000000101100 : Branch 0 (-1136639/62500 : ℚ) vp00000000000010110 := by
  apply branch_left_normalized (c:=vp000000000000101100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-1136639/62500 : ℚ) - ((0:ℤ):ℚ) = (-1136639/31250 : ℚ) by norm_num]
  exact coverp000000000000101100
private noncomputable def ep000000000000101101_0 : Blocks := edgeBlocks% "full/vectors/000000000000101101-E-0000.bin"
noncomputable def ep000000000000101101 : Blocks := ep000000000000101101_0
private theorem idp000000000000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000010110.list =
    C ((2:ℤ)^66) * horner X vp000000000000101101.list + horner X ep000000000000101101.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000101101 : Branch 1 (-1136639/62500 : ℚ) vp00000000000010110 := by
  apply branch_checked idp000000000000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1136639/62500 : ℚ) - ((1:ℤ):ℚ) = (-1167889/31250 : ℚ) by norm_num]
  exact coverp000000000000101101
theorem coverp00000000000010110 : Covers (-1136639/62500 : ℚ) vp00000000000010110 := join_branches bp000000000000101100 bp000000000000101101
private noncomputable def vp0000000000001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000001011-V-0000.bin"
noncomputable def vp0000000000001011 : Blocks := vp0000000000001011_0
private theorem bp00000000000010110 : Branch 0 (-1136639/125000 : ℚ) vp0000000000001011 := by
  apply branch_left_normalized (c:=vp00000000000010110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-1136639/62500 : ℚ) by norm_num]
  exact coverp00000000000010110
private noncomputable def ep00000000000010111_0 : Blocks := edgeBlocks% "full/vectors/00000000000010111-E-0000.bin"
noncomputable def ep00000000000010111 : Blocks := ep00000000000010111_0
private theorem idp00000000000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000001011.list =
    C ((2:ℤ)^120) * horner X vp00000000000010111.list + horner X ep00000000000010111.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000010111 : Branch 1 (-1136639/125000 : ℚ) vp0000000000001011 := by
  apply branch_checked idp00000000000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-1199139/62500 : ℚ) by norm_num]
  exact coverp00000000000010111
theorem coverp0000000000001011 : Covers (-1136639/125000 : ℚ) vp0000000000001011 := join_branches bp00000000000010110 bp00000000000010111
private noncomputable def vp000000000000101011_0 : Blocks := edgeBlocks% "full/vectors/000000000000101011-V-0000.bin"
noncomputable def vp000000000000101011 : Blocks := vp000000000000101011_0
theorem coverp000000000000101011 : Covers (-1105389/31250 : ℚ) vp000000000000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000101010_0 : Blocks := edgeBlocks% "full/vectors/000000000000101010-V-0000.bin"
noncomputable def vp000000000000101010 : Blocks := vp000000000000101010_0
theorem coverp000000000000101010 : Covers (-1074139/31250 : ℚ) vp000000000000101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000010101_0 : Blocks := edgeBlocks% "full/vectors/00000000000010101-V-0000.bin"
noncomputable def vp00000000000010101 : Blocks := vp00000000000010101_0
private theorem bp000000000000101010 : Branch 0 (-1074139/62500 : ℚ) vp00000000000010101 := by
  apply branch_left_normalized (c:=vp000000000000101010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-1074139/62500 : ℚ) - ((0:ℤ):ℚ) = (-1074139/31250 : ℚ) by norm_num]
  exact coverp000000000000101010
private noncomputable def ep000000000000101011_0 : Blocks := edgeBlocks% "full/vectors/000000000000101011-E-0000.bin"
noncomputable def ep000000000000101011 : Blocks := ep000000000000101011_0
private theorem idp000000000000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000010101.list =
    C ((2:ℤ)^68) * horner X vp000000000000101011.list + horner X ep000000000000101011.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000101011 : Branch 1 (-1074139/62500 : ℚ) vp00000000000010101 := by
  apply branch_checked idp000000000000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1074139/62500 : ℚ) - ((1:ℤ):ℚ) = (-1105389/31250 : ℚ) by norm_num]
  exact coverp000000000000101011
theorem coverp00000000000010101 : Covers (-1074139/62500 : ℚ) vp00000000000010101 := join_branches bp000000000000101010 bp000000000000101011
private noncomputable def vp000000000000101001_0 : Blocks := edgeBlocks% "full/vectors/000000000000101001-V-0000.bin"
noncomputable def vp000000000000101001 : Blocks := vp000000000000101001_0
theorem coverp000000000000101001 : Covers (-1042889/31250 : ℚ) vp000000000000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000101000_0 : Blocks := edgeBlocks% "full/vectors/000000000000101000-V-0000.bin"
noncomputable def vp000000000000101000 : Blocks := vp000000000000101000_0
theorem coverp000000000000101000 : Covers (-1011639/31250 : ℚ) vp000000000000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000010100_0 : Blocks := edgeBlocks% "full/vectors/00000000000010100-V-0000.bin"
noncomputable def vp00000000000010100 : Blocks := vp00000000000010100_0
private theorem bp000000000000101000 : Branch 0 (-1011639/62500 : ℚ) vp00000000000010100 := by
  apply branch_left_normalized (c:=vp000000000000101000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1011639/62500 : ℚ) - ((0:ℤ):ℚ) = (-1011639/31250 : ℚ) by norm_num]
  exact coverp000000000000101000
private noncomputable def ep000000000000101001_0 : Blocks := edgeBlocks% "full/vectors/000000000000101001-E-0000.bin"
noncomputable def ep000000000000101001 : Blocks := ep000000000000101001_0
private theorem idp000000000000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000010100.list =
    C ((2:ℤ)^70) * horner X vp000000000000101001.list + horner X ep000000000000101001.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000101001 : Branch 1 (-1011639/62500 : ℚ) vp00000000000010100 := by
  apply branch_checked idp000000000000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1011639/62500 : ℚ) - ((1:ℤ):ℚ) = (-1042889/31250 : ℚ) by norm_num]
  exact coverp000000000000101001
theorem coverp00000000000010100 : Covers (-1011639/62500 : ℚ) vp00000000000010100 := join_branches bp000000000000101000 bp000000000000101001
private noncomputable def vp0000000000001010_0 : Blocks := edgeBlocks% "full/vectors/0000000000001010-V-0000.bin"
noncomputable def vp0000000000001010 : Blocks := vp0000000000001010_0
private theorem bp00000000000010100 : Branch 0 (-1011639/125000 : ℚ) vp0000000000001010 := by
  apply branch_left_normalized (c:=vp00000000000010100) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-1011639/62500 : ℚ) by norm_num]
  exact coverp00000000000010100
private noncomputable def ep00000000000010101_0 : Blocks := edgeBlocks% "full/vectors/00000000000010101-E-0000.bin"
noncomputable def ep00000000000010101 : Blocks := ep00000000000010101_0
private theorem idp00000000000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000001010.list =
    C ((2:ℤ)^126) * horner X vp00000000000010101.list + horner X ep00000000000010101.list := by
  exact edge_identity (B := (2:ℤ)^272) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000010101 : Branch 1 (-1011639/125000 : ℚ) vp0000000000001010 := by
  apply branch_checked idp00000000000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-1074139/62500 : ℚ) by norm_num]
  exact coverp00000000000010101
theorem coverp0000000000001010 : Covers (-1011639/125000 : ℚ) vp0000000000001010 := join_branches bp00000000000010100 bp00000000000010101
private noncomputable def vp000000000000101_0 : Blocks := edgeBlocks% "full/vectors/000000000000101-V-0000.bin"
private noncomputable def vp000000000000101_1 : Blocks := edgeBlocks% "full/vectors/000000000000101-V-0001.bin"
noncomputable def vp000000000000101 : Blocks := (Blocks.join vp000000000000101_0 vp000000000000101_1)
private theorem bp0000000000001010 : Branch 0 (-1011639/250000 : ℚ) vp000000000000101 := by
  apply branch_left_normalized (c:=vp0000000000001010) (k:=0) (m:=124) (by decide +kernel)
  rw [show 2*(-1011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-1011639/125000 : ℚ) by norm_num]
  exact coverp0000000000001010
private noncomputable def ep0000000000001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000001011-E-0000.bin"
private noncomputable def ep0000000000001011_1 : Blocks := edgeBlocks% "full/vectors/0000000000001011-E-0001.bin"
noncomputable def ep0000000000001011 : Blocks := (Blocks.join ep0000000000001011_0 ep0000000000001011_1)
private theorem idp0000000000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000101.list =
    C ((2:ℤ)^235) * horner X vp0000000000001011.list + horner X ep0000000000001011.list := by
  exact edge_identity (B := (2:ℤ)^439) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000001011 : Branch 1 (-1011639/250000 : ℚ) vp000000000000101 := by
  apply branch_checked idp0000000000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-1136639/125000 : ℚ) by norm_num]
  exact coverp0000000000001011
theorem coverp000000000000101 : Covers (-1011639/250000 : ℚ) vp000000000000101 := join_branches bp0000000000001010 bp0000000000001011
private noncomputable def vp000000000000100111_0 : Blocks := edgeBlocks% "full/vectors/000000000000100111-V-0000.bin"
noncomputable def vp000000000000100111 : Blocks := vp000000000000100111_0
theorem coverp000000000000100111 : Covers (-980389/31250 : ℚ) vp000000000000100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000100110_0 : Blocks := edgeBlocks% "full/vectors/000000000000100110-V-0000.bin"
noncomputable def vp000000000000100110 : Blocks := vp000000000000100110_0
theorem coverp000000000000100110 : Covers (-949139/31250 : ℚ) vp000000000000100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000010011_0 : Blocks := edgeBlocks% "full/vectors/00000000000010011-V-0000.bin"
noncomputable def vp00000000000010011 : Blocks := vp00000000000010011_0
private theorem bp000000000000100110 : Branch 0 (-949139/62500 : ℚ) vp00000000000010011 := by
  apply branch_left_normalized (c:=vp000000000000100110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-949139/62500 : ℚ) - ((0:ℤ):ℚ) = (-949139/31250 : ℚ) by norm_num]
  exact coverp000000000000100110
private noncomputable def ep000000000000100111_0 : Blocks := edgeBlocks% "full/vectors/000000000000100111-E-0000.bin"
noncomputable def ep000000000000100111 : Blocks := ep000000000000100111_0
private theorem idp000000000000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000010011.list =
    C ((2:ℤ)^70) * horner X vp000000000000100111.list + horner X ep000000000000100111.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000100111 : Branch 1 (-949139/62500 : ℚ) vp00000000000010011 := by
  apply branch_checked idp000000000000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-949139/62500 : ℚ) - ((1:ℤ):ℚ) = (-980389/31250 : ℚ) by norm_num]
  exact coverp000000000000100111
theorem coverp00000000000010011 : Covers (-949139/62500 : ℚ) vp00000000000010011 := join_branches bp000000000000100110 bp000000000000100111
private noncomputable def vp000000000000100101_0 : Blocks := edgeBlocks% "full/vectors/000000000000100101-V-0000.bin"
noncomputable def vp000000000000100101 : Blocks := vp000000000000100101_0
theorem coverp000000000000100101 : Covers (-917889/31250 : ℚ) vp000000000000100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000100100_0 : Blocks := edgeBlocks% "full/vectors/000000000000100100-V-0000.bin"
noncomputable def vp000000000000100100 : Blocks := vp000000000000100100_0
theorem coverp000000000000100100 : Covers (-886639/31250 : ℚ) vp000000000000100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000010010_0 : Blocks := edgeBlocks% "full/vectors/00000000000010010-V-0000.bin"
noncomputable def vp00000000000010010 : Blocks := vp00000000000010010_0
private theorem bp000000000000100100 : Branch 0 (-886639/62500 : ℚ) vp00000000000010010 := by
  apply branch_left_normalized (c:=vp000000000000100100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-886639/31250 : ℚ) by norm_num]
  exact coverp000000000000100100
private noncomputable def ep000000000000100101_0 : Blocks := edgeBlocks% "full/vectors/000000000000100101-E-0000.bin"
noncomputable def ep000000000000100101 : Blocks := ep000000000000100101_0
private theorem idp000000000000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000010010.list =
    C ((2:ℤ)^72) * horner X vp000000000000100101.list + horner X ep000000000000100101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000100101 : Branch 1 (-886639/62500 : ℚ) vp00000000000010010 := by
  apply branch_checked idp000000000000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-917889/31250 : ℚ) by norm_num]
  exact coverp000000000000100101
theorem coverp00000000000010010 : Covers (-886639/62500 : ℚ) vp00000000000010010 := join_branches bp000000000000100100 bp000000000000100101
private noncomputable def vp0000000000001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000001001-V-0000.bin"
private noncomputable def vp0000000000001001_1 : Blocks := edgeBlocks% "full/vectors/0000000000001001-V-0001.bin"
noncomputable def vp0000000000001001 : Blocks := (Blocks.join vp0000000000001001_0 vp0000000000001001_1)
private theorem bp00000000000010010 : Branch 0 (-886639/125000 : ℚ) vp0000000000001001 := by
  apply branch_left_normalized (c:=vp00000000000010010) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-886639/62500 : ℚ) by norm_num]
  exact coverp00000000000010010
private noncomputable def ep00000000000010011_0 : Blocks := edgeBlocks% "full/vectors/00000000000010011-E-0000.bin"
private noncomputable def ep00000000000010011_1 : Blocks := edgeBlocks% "full/vectors/00000000000010011-E-0001.bin"
noncomputable def ep00000000000010011 : Blocks := (Blocks.join ep00000000000010011_0 ep00000000000010011_1)
private theorem idp00000000000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000001001.list =
    C ((2:ℤ)^131) * horner X vp00000000000010011.list + horner X ep00000000000010011.list := by
  exact edge_identity (B := (2:ℤ)^280) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000010011 : Branch 1 (-886639/125000 : ℚ) vp0000000000001001 := by
  apply branch_checked idp00000000000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-949139/62500 : ℚ) by norm_num]
  exact coverp00000000000010011
theorem coverp0000000000001001 : Covers (-886639/125000 : ℚ) vp0000000000001001 := join_branches bp00000000000010010 bp00000000000010011
private noncomputable def vp000000000000100011_0 : Blocks := edgeBlocks% "full/vectors/000000000000100011-V-0000.bin"
noncomputable def vp000000000000100011 : Blocks := vp000000000000100011_0
theorem coverp000000000000100011 : Covers (-855389/31250 : ℚ) vp000000000000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000100010_0 : Blocks := edgeBlocks% "full/vectors/000000000000100010-V-0000.bin"
noncomputable def vp000000000000100010 : Blocks := vp000000000000100010_0
theorem coverp000000000000100010 : Covers (-824139/31250 : ℚ) vp000000000000100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000010001_0 : Blocks := edgeBlocks% "full/vectors/00000000000010001-V-0000.bin"
noncomputable def vp00000000000010001 : Blocks := vp00000000000010001_0
private theorem bp000000000000100010 : Branch 0 (-824139/62500 : ℚ) vp00000000000010001 := by
  apply branch_left_normalized (c:=vp000000000000100010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-824139/31250 : ℚ) by norm_num]
  exact coverp000000000000100010
private noncomputable def ep000000000000100011_0 : Blocks := edgeBlocks% "full/vectors/000000000000100011-E-0000.bin"
noncomputable def ep000000000000100011 : Blocks := ep000000000000100011_0
private theorem idp000000000000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000010001.list =
    C ((2:ℤ)^73) * horner X vp000000000000100011.list + horner X ep000000000000100011.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000100011 : Branch 1 (-824139/62500 : ℚ) vp00000000000010001 := by
  apply branch_checked idp000000000000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-855389/31250 : ℚ) by norm_num]
  exact coverp000000000000100011
theorem coverp00000000000010001 : Covers (-824139/62500 : ℚ) vp00000000000010001 := join_branches bp000000000000100010 bp000000000000100011
private noncomputable def vp000000000000100001_0 : Blocks := edgeBlocks% "full/vectors/000000000000100001-V-0000.bin"
noncomputable def vp000000000000100001 : Blocks := vp000000000000100001_0
theorem coverp000000000000100001 : Covers (-792889/31250 : ℚ) vp000000000000100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000100000_0 : Blocks := edgeBlocks% "full/vectors/000000000000100000-V-0000.bin"
noncomputable def vp000000000000100000 : Blocks := vp000000000000100000_0
theorem coverp000000000000100000 : Covers (-761639/31250 : ℚ) vp000000000000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000010000_0 : Blocks := edgeBlocks% "full/vectors/00000000000010000-V-0000.bin"
noncomputable def vp00000000000010000 : Blocks := vp00000000000010000_0
private theorem bp000000000000100000 : Branch 0 (-761639/62500 : ℚ) vp00000000000010000 := by
  apply branch_left_normalized (c:=vp000000000000100000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-761639/31250 : ℚ) by norm_num]
  exact coverp000000000000100000
private noncomputable def ep000000000000100001_0 : Blocks := edgeBlocks% "full/vectors/000000000000100001-E-0000.bin"
noncomputable def ep000000000000100001 : Blocks := ep000000000000100001_0
private theorem idp000000000000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000010000.list =
    C ((2:ℤ)^75) * horner X vp000000000000100001.list + horner X ep000000000000100001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000100001 : Branch 1 (-761639/62500 : ℚ) vp00000000000010000 := by
  apply branch_checked idp000000000000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-792889/31250 : ℚ) by norm_num]
  exact coverp000000000000100001
theorem coverp00000000000010000 : Covers (-761639/62500 : ℚ) vp00000000000010000 := join_branches bp000000000000100000 bp000000000000100001
private noncomputable def vp0000000000001000_0 : Blocks := edgeBlocks% "full/vectors/0000000000001000-V-0000.bin"
private noncomputable def vp0000000000001000_1 : Blocks := edgeBlocks% "full/vectors/0000000000001000-V-0001.bin"
noncomputable def vp0000000000001000 : Blocks := (Blocks.join vp0000000000001000_0 vp0000000000001000_1)
private theorem bp00000000000010000 : Branch 0 (-761639/125000 : ℚ) vp0000000000001000 := by
  apply branch_left_normalized (c:=vp00000000000010000) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-761639/62500 : ℚ) by norm_num]
  exact coverp00000000000010000
private noncomputable def ep00000000000010001_0 : Blocks := edgeBlocks% "full/vectors/00000000000010001-E-0000.bin"
private noncomputable def ep00000000000010001_1 : Blocks := edgeBlocks% "full/vectors/00000000000010001-E-0001.bin"
noncomputable def ep00000000000010001 : Blocks := (Blocks.join ep00000000000010001_0 ep00000000000010001_1)
private theorem idp00000000000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000001000.list =
    C ((2:ℤ)^138) * horner X vp00000000000010001.list + horner X ep00000000000010001.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000010001 : Branch 1 (-761639/125000 : ℚ) vp0000000000001000 := by
  apply branch_checked idp00000000000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-824139/62500 : ℚ) by norm_num]
  exact coverp00000000000010001
theorem coverp0000000000001000 : Covers (-761639/125000 : ℚ) vp0000000000001000 := join_branches bp00000000000010000 bp00000000000010001
private noncomputable def vp000000000000100_0 : Blocks := edgeBlocks% "full/vectors/000000000000100-V-0000.bin"
private noncomputable def vp000000000000100_1 : Blocks := edgeBlocks% "full/vectors/000000000000100-V-0001.bin"
private noncomputable def vp000000000000100_2 : Blocks := edgeBlocks% "full/vectors/000000000000100-V-0002.bin"
noncomputable def vp000000000000100 : Blocks := (Blocks.join vp000000000000100_0 (Blocks.join vp000000000000100_1 vp000000000000100_2))
private theorem bp0000000000001000 : Branch 0 (-761639/250000 : ℚ) vp000000000000100 := by
  apply branch_left_normalized (c:=vp0000000000001000) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-761639/125000 : ℚ) by norm_num]
  exact coverp0000000000001000
private noncomputable def ep0000000000001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000001001-E-0000.bin"
private noncomputable def ep0000000000001001_1 : Blocks := edgeBlocks% "full/vectors/0000000000001001-E-0001.bin"
private noncomputable def ep0000000000001001_2 : Blocks := edgeBlocks% "full/vectors/0000000000001001-E-0002.bin"
noncomputable def ep0000000000001001 : Blocks := (Blocks.join ep0000000000001001_0 (Blocks.join ep0000000000001001_1 ep0000000000001001_2))
private theorem idp0000000000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000100.list =
    C ((2:ℤ)^260) * horner X vp0000000000001001.list + horner X ep0000000000001001.list := by
  exact edge_identity (B := (2:ℤ)^477) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000001001 : Branch 1 (-761639/250000 : ℚ) vp000000000000100 := by
  apply branch_checked idp0000000000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-886639/125000 : ℚ) by norm_num]
  exact coverp0000000000001001
theorem coverp000000000000100 : Covers (-761639/250000 : ℚ) vp000000000000100 := join_branches bp0000000000001000 bp0000000000001001
private noncomputable def vp00000000000010_0 : Blocks := edgeBlocks% "full/vectors/00000000000010-V-0000.bin"
private noncomputable def vp00000000000010_1 : Blocks := edgeBlocks% "full/vectors/00000000000010-V-0001.bin"
private noncomputable def vp00000000000010_2 : Blocks := edgeBlocks% "full/vectors/00000000000010-V-0002.bin"
private noncomputable def vp00000000000010_3 : Blocks := edgeBlocks% "full/vectors/00000000000010-V-0003.bin"
noncomputable def vp00000000000010 : Blocks := (Blocks.join (Blocks.join vp00000000000010_0 vp00000000000010_1) (Blocks.join vp00000000000010_2 vp00000000000010_3))
private theorem bp000000000000100 : Branch 0 (-761639/500000 : ℚ) vp00000000000010 := by
  apply branch_left_normalized (c:=vp000000000000100) (k:=0) (m:=259) (by decide +kernel)
  rw [show 2*(-761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-761639/250000 : ℚ) by norm_num]
  exact coverp000000000000100
private noncomputable def ep000000000000101_0 : Blocks := edgeBlocks% "full/vectors/000000000000101-E-0000.bin"
private noncomputable def ep000000000000101_1 : Blocks := edgeBlocks% "full/vectors/000000000000101-E-0001.bin"
private noncomputable def ep000000000000101_2 : Blocks := edgeBlocks% "full/vectors/000000000000101-E-0002.bin"
private noncomputable def ep000000000000101_3 : Blocks := edgeBlocks% "full/vectors/000000000000101-E-0003.bin"
noncomputable def ep000000000000101 : Blocks := (Blocks.join (Blocks.join ep000000000000101_0 ep000000000000101_1) (Blocks.join ep000000000000101_2 ep000000000000101_3))
private theorem idp000000000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000010.list =
    C ((2:ℤ)^503) * horner X vp000000000000101.list + horner X ep000000000000101.list := by
  exact edge_identity (B := (2:ℤ)^851) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000101 : Branch 1 (-761639/500000 : ℚ) vp00000000000010 := by
  apply branch_checked idp000000000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-1011639/250000 : ℚ) by norm_num]
  exact coverp000000000000101
theorem coverp00000000000010 : Covers (-761639/500000 : ℚ) vp00000000000010 := join_branches bp000000000000100 bp000000000000101
noncomputable def vp0000000000001 : Blocks := NextProof.EdgeRecovery.R0000000000001.C.data
private theorem bp00000000000010 : Branch 0 (-761639/1000000 : ℚ) vp0000000000001 := by
  apply branch_left_normalized (c:=vp00000000000010) (k:=0) (m:=502) (by decide +kernel)
  rw [show 2*(-761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-761639/500000 : ℚ) by norm_num]
  exact coverp00000000000010
private noncomputable def ep00000000000011_0 : Blocks := edgeBlocks% "full/vectors/00000000000011-E-0000.bin"
private noncomputable def ep00000000000011_1 : Blocks := edgeBlocks% "full/vectors/00000000000011-E-0001.bin"
private noncomputable def ep00000000000011_2 : Blocks := edgeBlocks% "full/vectors/00000000000011-E-0002.bin"
private noncomputable def ep00000000000011_3 : Blocks := edgeBlocks% "full/vectors/00000000000011-E-0003.bin"
private noncomputable def ep00000000000011_4 : Blocks := edgeBlocks% "full/vectors/00000000000011-E-0004.bin"
private noncomputable def ep00000000000011_5 : Blocks := edgeBlocks% "full/vectors/00000000000011-E-0005.bin"
private noncomputable def ep00000000000011_6 : Blocks := edgeBlocks% "full/vectors/00000000000011-E-0006.bin"
noncomputable def ep00000000000011 : Blocks := (Blocks.join (Blocks.join ep00000000000011_0 (Blocks.join ep00000000000011_1 ep00000000000011_2)) (Blocks.join (Blocks.join ep00000000000011_3 ep00000000000011_4) (Blocks.join ep00000000000011_5 ep00000000000011_6)))
private theorem idp00000000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000001.list =
    C ((2:ℤ)^898) * horner X vp00000000000011.list + horner X ep00000000000011.list := by
  exact edge_identity (B := (2:ℤ)^1503) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000011 : Branch 1 (-761639/1000000 : ℚ) vp0000000000001 := by
  apply branch_checked idp00000000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-1261639/500000 : ℚ) by norm_num]
  exact coverp00000000000011
theorem coverp0000000000001 : Covers (-761639/1000000 : ℚ) vp0000000000001 := join_branches bp00000000000010 bp00000000000011
noncomputable def vp000000000000 : Blocks := NextProof.EdgeRecovery.R0000000000001.P.data
private theorem bp0000000000000 : Branch 0 (1906884279970892581/16000000000000000000 : ℚ) vp000000000000 := by
  apply NextProof.Compact.LeftKernel.branch_left_normalized_check (c:=vp0000000000000) (k:=0) (m:=13823) (by decide +kernel)
  rw [show 2*(1906884279970892581/16000000000000000000 : ℚ) - ((0:ℤ):ℚ) = (1906884279970892581/8000000000000000000 : ℚ) by norm_num]
  exact coverp0000000000000
noncomputable def ep0000000000001 : Blocks := NextProof.EdgeRecovery.R0000000000001.E.data
private theorem idp0000000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000.list =
    C ((2:ℤ)^14080) * horner X vp0000000000001.list + horner X ep0000000000001.list := by
  exact NextProof.EdgeRecovery.R0000000000001.identity
private theorem bp0000000000001 : Branch 1 (1906884279970892581/16000000000000000000 : ℚ) vp000000000000 := by
  apply branch_checked idp0000000000001 (by positivity) (by decide +kernel)
  rw [show 2*(1906884279970892581/16000000000000000000 : ℚ) - ((1:ℤ):ℚ) = (-6093115720029107419/8000000000000000000 : ℚ) by norm_num]
  exact fun x hx hx' _ => coverp0000000000001 x hx hx' (le_trans (by norm_num) hx)
theorem coverp000000000000 : Covers (1906884279970892581/16000000000000000000 : ℚ) vp000000000000 := join_branches bp0000000000000 bp0000000000001
end NextProof.EdgeFull

