import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00097

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp001100011111_0 : Blocks := edgeBlocks% "full/vectors/001100011111-V-0000.bin"
noncomputable def vp001100011111 : Blocks := vp001100011111_0
theorem coverp001100011111 : Covers (-1597761639/2000000 : ℚ) vp001100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000111101_0 : Blocks := edgeBlocks% "full/vectors/0011000111101-V-0000.bin"
noncomputable def vp0011000111101 : Blocks := vp0011000111101_0
theorem coverp0011000111101 : Covers (-1596761639/1000000 : ℚ) vp0011000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000111100_0 : Blocks := edgeBlocks% "full/vectors/0011000111100-V-0000.bin"
noncomputable def vp0011000111100 : Blocks := vp0011000111100_0
theorem coverp0011000111100 : Covers (-1595761639/1000000 : ℚ) vp0011000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001100011110_0 : Blocks := edgeBlocks% "full/vectors/001100011110-V-0000.bin"
noncomputable def vp001100011110 : Blocks := vp001100011110_0
private theorem bp0011000111100 : Branch 0 (-1595761639/2000000 : ℚ) vp001100011110 := by
  apply branch_left_normalized (c:=vp0011000111100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1595761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1595761639/1000000 : ℚ) by norm_num]
  exact coverp0011000111100
private noncomputable def ep0011000111101_0 : Blocks := edgeBlocks% "full/vectors/0011000111101-E-0000.bin"
noncomputable def ep0011000111101 : Blocks := ep0011000111101_0
private theorem idp0011000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100011110.list =
    C ((2:ℤ)^73) * horner X vp0011000111101.list + horner X ep0011000111101.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000111101 : Branch 1 (-1595761639/2000000 : ℚ) vp001100011110 := by
  apply branch_checked idp0011000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1595761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1596761639/1000000 : ℚ) by norm_num]
  exact coverp0011000111101
theorem coverp001100011110 : Covers (-1595761639/2000000 : ℚ) vp001100011110 := join_branches bp0011000111100 bp0011000111101
private noncomputable def vp00110001111_0 : Blocks := edgeBlocks% "full/vectors/00110001111-V-0000.bin"
noncomputable def vp00110001111 : Blocks := vp00110001111_0
private theorem bp001100011110 : Branch 0 (-1595761639/4000000 : ℚ) vp00110001111 := by
  apply branch_left_normalized (c:=vp001100011110) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1595761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1595761639/2000000 : ℚ) by norm_num]
  exact coverp001100011110
private noncomputable def ep001100011111_0 : Blocks := edgeBlocks% "full/vectors/001100011111-E-0000.bin"
noncomputable def ep001100011111 : Blocks := ep001100011111_0
private theorem idp001100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110001111.list =
    C ((2:ℤ)^128) * horner X vp001100011111.list + horner X ep001100011111.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100011111 : Branch 1 (-1595761639/4000000 : ℚ) vp00110001111 := by
  apply branch_checked idp001100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1595761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1597761639/2000000 : ℚ) by norm_num]
  exact coverp001100011111
theorem coverp00110001111 : Covers (-1595761639/4000000 : ℚ) vp00110001111 := join_branches bp001100011110 bp001100011111
private noncomputable def vp0011000111011_0 : Blocks := edgeBlocks% "full/vectors/0011000111011-V-0000.bin"
noncomputable def vp0011000111011 : Blocks := vp0011000111011_0
theorem coverp0011000111011 : Covers (-1594761639/1000000 : ℚ) vp0011000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000111010_0 : Blocks := edgeBlocks% "full/vectors/0011000111010-V-0000.bin"
noncomputable def vp0011000111010 : Blocks := vp0011000111010_0
theorem coverp0011000111010 : Covers (-1593761639/1000000 : ℚ) vp0011000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001100011101_0 : Blocks := edgeBlocks% "full/vectors/001100011101-V-0000.bin"
noncomputable def vp001100011101 : Blocks := vp001100011101_0
private theorem bp0011000111010 : Branch 0 (-1593761639/2000000 : ℚ) vp001100011101 := by
  apply branch_left_normalized (c:=vp0011000111010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1593761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1593761639/1000000 : ℚ) by norm_num]
  exact coverp0011000111010
private noncomputable def ep0011000111011_0 : Blocks := edgeBlocks% "full/vectors/0011000111011-E-0000.bin"
noncomputable def ep0011000111011 : Blocks := ep0011000111011_0
private theorem idp0011000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100011101.list =
    C ((2:ℤ)^75) * horner X vp0011000111011.list + horner X ep0011000111011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000111011 : Branch 1 (-1593761639/2000000 : ℚ) vp001100011101 := by
  apply branch_checked idp0011000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1593761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1594761639/1000000 : ℚ) by norm_num]
  exact coverp0011000111011
theorem coverp001100011101 : Covers (-1593761639/2000000 : ℚ) vp001100011101 := join_branches bp0011000111010 bp0011000111011
private noncomputable def vp001100011100_0 : Blocks := edgeBlocks% "full/vectors/001100011100-V-0000.bin"
noncomputable def vp001100011100 : Blocks := vp001100011100_0
theorem coverp001100011100 : Covers (-1591761639/2000000 : ℚ) vp001100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00110001110_0 : Blocks := edgeBlocks% "full/vectors/00110001110-V-0000.bin"
noncomputable def vp00110001110 : Blocks := vp00110001110_0
private theorem bp001100011100 : Branch 0 (-1591761639/4000000 : ℚ) vp00110001110 := by
  apply branch_left_normalized (c:=vp001100011100) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1591761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1591761639/2000000 : ℚ) by norm_num]
  exact coverp001100011100
private noncomputable def ep001100011101_0 : Blocks := edgeBlocks% "full/vectors/001100011101-E-0000.bin"
noncomputable def ep001100011101 : Blocks := ep001100011101_0
private theorem idp001100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110001110.list =
    C ((2:ℤ)^131) * horner X vp001100011101.list + horner X ep001100011101.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100011101 : Branch 1 (-1591761639/4000000 : ℚ) vp00110001110 := by
  apply branch_checked idp001100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1591761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1593761639/2000000 : ℚ) by norm_num]
  exact coverp001100011101
theorem coverp00110001110 : Covers (-1591761639/4000000 : ℚ) vp00110001110 := join_branches bp001100011100 bp001100011101
private noncomputable def vp0011000111_0 : Blocks := edgeBlocks% "full/vectors/0011000111-V-0000.bin"
private noncomputable def vp0011000111_1 : Blocks := edgeBlocks% "full/vectors/0011000111-V-0001.bin"
noncomputable def vp0011000111 : Blocks := (Blocks.join vp0011000111_0 vp0011000111_1)
private theorem bp00110001110 : Branch 0 (-1591761639/8000000 : ℚ) vp0011000111 := by
  apply branch_left_normalized (c:=vp00110001110) (k:=0) (m:=118) (by decide +kernel)
  rw [show 2*(-1591761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1591761639/4000000 : ℚ) by norm_num]
  exact coverp00110001110
private noncomputable def ep00110001111_0 : Blocks := edgeBlocks% "full/vectors/00110001111-E-0000.bin"
private noncomputable def ep00110001111_1 : Blocks := edgeBlocks% "full/vectors/00110001111-E-0001.bin"
noncomputable def ep00110001111 : Blocks := (Blocks.join ep00110001111_0 ep00110001111_1)
private theorem idp00110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011000111.list =
    C ((2:ℤ)^241) * horner X vp00110001111.list + horner X ep00110001111.list := by
  exact edge_identity (B := (2:ℤ)^421) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110001111 : Branch 1 (-1591761639/8000000 : ℚ) vp0011000111 := by
  apply branch_checked idp00110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1591761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1595761639/4000000 : ℚ) by norm_num]
  exact coverp00110001111
theorem coverp0011000111 : Covers (-1591761639/8000000 : ℚ) vp0011000111 := join_branches bp00110001110 bp00110001111
private noncomputable def vp001100011011_0 : Blocks := edgeBlocks% "full/vectors/001100011011-V-0000.bin"
noncomputable def vp001100011011 : Blocks := vp001100011011_0
theorem coverp001100011011 : Covers (-1589761639/2000000 : ℚ) vp001100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000110101_0 : Blocks := edgeBlocks% "full/vectors/0011000110101-V-0000.bin"
noncomputable def vp0011000110101 : Blocks := vp0011000110101_0
theorem coverp0011000110101 : Covers (-1588761639/1000000 : ℚ) vp0011000110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000110100_0 : Blocks := edgeBlocks% "full/vectors/0011000110100-V-0000.bin"
noncomputable def vp0011000110100 : Blocks := vp0011000110100_0
theorem coverp0011000110100 : Covers (-1587761639/1000000 : ℚ) vp0011000110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001100011010_0 : Blocks := edgeBlocks% "full/vectors/001100011010-V-0000.bin"
noncomputable def vp001100011010 : Blocks := vp001100011010_0
private theorem bp0011000110100 : Branch 0 (-1587761639/2000000 : ℚ) vp001100011010 := by
  apply branch_left_normalized (c:=vp0011000110100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1587761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1587761639/1000000 : ℚ) by norm_num]
  exact coverp0011000110100
private noncomputable def ep0011000110101_0 : Blocks := edgeBlocks% "full/vectors/0011000110101-E-0000.bin"
noncomputable def ep0011000110101 : Blocks := ep0011000110101_0
private theorem idp0011000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100011010.list =
    C ((2:ℤ)^76) * horner X vp0011000110101.list + horner X ep0011000110101.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000110101 : Branch 1 (-1587761639/2000000 : ℚ) vp001100011010 := by
  apply branch_checked idp0011000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1587761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1588761639/1000000 : ℚ) by norm_num]
  exact coverp0011000110101
theorem coverp001100011010 : Covers (-1587761639/2000000 : ℚ) vp001100011010 := join_branches bp0011000110100 bp0011000110101
private noncomputable def vp00110001101_0 : Blocks := edgeBlocks% "full/vectors/00110001101-V-0000.bin"
noncomputable def vp00110001101 : Blocks := vp00110001101_0
private theorem bp001100011010 : Branch 0 (-1587761639/4000000 : ℚ) vp00110001101 := by
  apply branch_left_normalized (c:=vp001100011010) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-1587761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1587761639/2000000 : ℚ) by norm_num]
  exact coverp001100011010
private noncomputable def ep001100011011_0 : Blocks := edgeBlocks% "full/vectors/001100011011-E-0000.bin"
noncomputable def ep001100011011 : Blocks := ep001100011011_0
private theorem idp001100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110001101.list =
    C ((2:ℤ)^134) * horner X vp001100011011.list + horner X ep001100011011.list := by
  exact edge_identity (B := (2:ℤ)^274) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100011011 : Branch 1 (-1587761639/4000000 : ℚ) vp00110001101 := by
  apply branch_checked idp001100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1587761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1589761639/2000000 : ℚ) by norm_num]
  exact coverp001100011011
theorem coverp00110001101 : Covers (-1587761639/4000000 : ℚ) vp00110001101 := join_branches bp001100011010 bp001100011011
private noncomputable def vp0011000110011_0 : Blocks := edgeBlocks% "full/vectors/0011000110011-V-0000.bin"
noncomputable def vp0011000110011 : Blocks := vp0011000110011_0
theorem coverp0011000110011 : Covers (-1586761639/1000000 : ℚ) vp0011000110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000110010_0 : Blocks := edgeBlocks% "full/vectors/0011000110010-V-0000.bin"
noncomputable def vp0011000110010 : Blocks := vp0011000110010_0
theorem coverp0011000110010 : Covers (-1585761639/1000000 : ℚ) vp0011000110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001100011001_0 : Blocks := edgeBlocks% "full/vectors/001100011001-V-0000.bin"
noncomputable def vp001100011001 : Blocks := vp001100011001_0
private theorem bp0011000110010 : Branch 0 (-1585761639/2000000 : ℚ) vp001100011001 := by
  apply branch_left_normalized (c:=vp0011000110010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1585761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1585761639/1000000 : ℚ) by norm_num]
  exact coverp0011000110010
private noncomputable def ep0011000110011_0 : Blocks := edgeBlocks% "full/vectors/0011000110011-E-0000.bin"
noncomputable def ep0011000110011 : Blocks := ep0011000110011_0
private theorem idp0011000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100011001.list =
    C ((2:ℤ)^75) * horner X vp0011000110011.list + horner X ep0011000110011.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000110011 : Branch 1 (-1585761639/2000000 : ℚ) vp001100011001 := by
  apply branch_checked idp0011000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1585761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1586761639/1000000 : ℚ) by norm_num]
  exact coverp0011000110011
theorem coverp001100011001 : Covers (-1585761639/2000000 : ℚ) vp001100011001 := join_branches bp0011000110010 bp0011000110011
private noncomputable def vp0011000110001_0 : Blocks := edgeBlocks% "full/vectors/0011000110001-V-0000.bin"
noncomputable def vp0011000110001 : Blocks := vp0011000110001_0
theorem coverp0011000110001 : Covers (-1584761639/1000000 : ℚ) vp0011000110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000110000_0 : Blocks := edgeBlocks% "full/vectors/0011000110000-V-0000.bin"
noncomputable def vp0011000110000 : Blocks := vp0011000110000_0
theorem coverp0011000110000 : Covers (-1583761639/1000000 : ℚ) vp0011000110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001100011000_0 : Blocks := edgeBlocks% "full/vectors/001100011000-V-0000.bin"
noncomputable def vp001100011000 : Blocks := vp001100011000_0
private theorem bp0011000110000 : Branch 0 (-1583761639/2000000 : ℚ) vp001100011000 := by
  apply branch_left_normalized (c:=vp0011000110000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1583761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1583761639/1000000 : ℚ) by norm_num]
  exact coverp0011000110000
private noncomputable def ep0011000110001_0 : Blocks := edgeBlocks% "full/vectors/0011000110001-E-0000.bin"
noncomputable def ep0011000110001 : Blocks := ep0011000110001_0
private theorem idp0011000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100011000.list =
    C ((2:ℤ)^74) * horner X vp0011000110001.list + horner X ep0011000110001.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000110001 : Branch 1 (-1583761639/2000000 : ℚ) vp001100011000 := by
  apply branch_checked idp0011000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1583761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1584761639/1000000 : ℚ) by norm_num]
  exact coverp0011000110001
theorem coverp001100011000 : Covers (-1583761639/2000000 : ℚ) vp001100011000 := join_branches bp0011000110000 bp0011000110001
private noncomputable def vp00110001100_0 : Blocks := edgeBlocks% "full/vectors/00110001100-V-0000.bin"
noncomputable def vp00110001100 : Blocks := vp00110001100_0
private theorem bp001100011000 : Branch 0 (-1583761639/4000000 : ℚ) vp00110001100 := by
  apply branch_left_normalized (c:=vp001100011000) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1583761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1583761639/2000000 : ℚ) by norm_num]
  exact coverp001100011000
private noncomputable def ep001100011001_0 : Blocks := edgeBlocks% "full/vectors/001100011001-E-0000.bin"
noncomputable def ep001100011001 : Blocks := ep001100011001_0
private theorem idp001100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110001100.list =
    C ((2:ℤ)^130) * horner X vp001100011001.list + horner X ep001100011001.list := by
  exact edge_identity (B := (2:ℤ)^272) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100011001 : Branch 1 (-1583761639/4000000 : ℚ) vp00110001100 := by
  apply branch_checked idp001100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1583761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1585761639/2000000 : ℚ) by norm_num]
  exact coverp001100011001
theorem coverp00110001100 : Covers (-1583761639/4000000 : ℚ) vp00110001100 := join_branches bp001100011000 bp001100011001
private noncomputable def vp0011000110_0 : Blocks := edgeBlocks% "full/vectors/0011000110-V-0000.bin"
private noncomputable def vp0011000110_1 : Blocks := edgeBlocks% "full/vectors/0011000110-V-0001.bin"
noncomputable def vp0011000110 : Blocks := (Blocks.join vp0011000110_0 vp0011000110_1)
private theorem bp00110001100 : Branch 0 (-1583761639/8000000 : ℚ) vp0011000110 := by
  apply branch_left_normalized (c:=vp00110001100) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-1583761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1583761639/4000000 : ℚ) by norm_num]
  exact coverp00110001100
private noncomputable def ep00110001101_0 : Blocks := edgeBlocks% "full/vectors/00110001101-E-0000.bin"
private noncomputable def ep00110001101_1 : Blocks := edgeBlocks% "full/vectors/00110001101-E-0001.bin"
noncomputable def ep00110001101 : Blocks := (Blocks.join ep00110001101_0 ep00110001101_1)
private theorem idp00110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011000110.list =
    C ((2:ℤ)^242) * horner X vp00110001101.list + horner X ep00110001101.list := by
  exact edge_identity (B := (2:ℤ)^424) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110001101 : Branch 1 (-1583761639/8000000 : ℚ) vp0011000110 := by
  apply branch_checked idp00110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1583761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1587761639/4000000 : ℚ) by norm_num]
  exact coverp00110001101
theorem coverp0011000110 : Covers (-1583761639/8000000 : ℚ) vp0011000110 := join_branches bp00110001100 bp00110001101
private noncomputable def vp001100011_0 : Blocks := edgeBlocks% "full/vectors/001100011-V-0000.bin"
private noncomputable def vp001100011_1 : Blocks := edgeBlocks% "full/vectors/001100011-V-0001.bin"
private noncomputable def vp001100011_2 : Blocks := edgeBlocks% "full/vectors/001100011-V-0002.bin"
private noncomputable def vp001100011_3 : Blocks := edgeBlocks% "full/vectors/001100011-V-0003.bin"
noncomputable def vp001100011 : Blocks := (Blocks.join (Blocks.join vp001100011_0 vp001100011_1) (Blocks.join vp001100011_2 vp001100011_3))
private theorem bp0011000110 : Branch 0 (-1583761639/16000000 : ℚ) vp001100011 := by
  apply branch_left_normalized (c:=vp0011000110) (k:=0) (m:=219) (by decide +kernel)
  rw [show 2*(-1583761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1583761639/8000000 : ℚ) by norm_num]
  exact coverp0011000110
private noncomputable def ep0011000111_0 : Blocks := edgeBlocks% "full/vectors/0011000111-E-0000.bin"
private noncomputable def ep0011000111_1 : Blocks := edgeBlocks% "full/vectors/0011000111-E-0001.bin"
private noncomputable def ep0011000111_2 : Blocks := edgeBlocks% "full/vectors/0011000111-E-0002.bin"
private noncomputable def ep0011000111_3 : Blocks := edgeBlocks% "full/vectors/0011000111-E-0003.bin"
noncomputable def ep0011000111 : Blocks := (Blocks.join (Blocks.join ep0011000111_0 ep0011000111_1) (Blocks.join ep0011000111_2 ep0011000111_3))
private theorem idp0011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100011.list =
    C ((2:ℤ)^463) * horner X vp0011000111.list + horner X ep0011000111.list := by
  exact edge_identity (B := (2:ℤ)^725) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000111 : Branch 1 (-1583761639/16000000 : ℚ) vp001100011 := by
  apply branch_checked idp0011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1583761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1591761639/8000000 : ℚ) by norm_num]
  exact coverp0011000111
theorem coverp001100011 : Covers (-1583761639/16000000 : ℚ) vp001100011 := join_branches bp0011000110 bp0011000111
private noncomputable def vp0011000101111_0 : Blocks := edgeBlocks% "full/vectors/0011000101111-V-0000.bin"
noncomputable def vp0011000101111 : Blocks := vp0011000101111_0
theorem coverp0011000101111 : Covers (-1582761639/1000000 : ℚ) vp0011000101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000101110_0 : Blocks := edgeBlocks% "full/vectors/0011000101110-V-0000.bin"
noncomputable def vp0011000101110 : Blocks := vp0011000101110_0
theorem coverp0011000101110 : Covers (-1581761639/1000000 : ℚ) vp0011000101110 := cover_leaf (by decide +kernel)
private noncomputable def vp001100010111_0 : Blocks := edgeBlocks% "full/vectors/001100010111-V-0000.bin"
noncomputable def vp001100010111 : Blocks := vp001100010111_0
private theorem bp0011000101110 : Branch 0 (-1581761639/2000000 : ℚ) vp001100010111 := by
  apply branch_left_normalized (c:=vp0011000101110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1581761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1581761639/1000000 : ℚ) by norm_num]
  exact coverp0011000101110
private noncomputable def ep0011000101111_0 : Blocks := edgeBlocks% "full/vectors/0011000101111-E-0000.bin"
noncomputable def ep0011000101111 : Blocks := ep0011000101111_0
private theorem idp0011000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100010111.list =
    C ((2:ℤ)^74) * horner X vp0011000101111.list + horner X ep0011000101111.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000101111 : Branch 1 (-1581761639/2000000 : ℚ) vp001100010111 := by
  apply branch_checked idp0011000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1581761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1582761639/1000000 : ℚ) by norm_num]
  exact coverp0011000101111
theorem coverp001100010111 : Covers (-1581761639/2000000 : ℚ) vp001100010111 := join_branches bp0011000101110 bp0011000101111
private noncomputable def vp0011000101101_0 : Blocks := edgeBlocks% "full/vectors/0011000101101-V-0000.bin"
noncomputable def vp0011000101101 : Blocks := vp0011000101101_0
theorem coverp0011000101101 : Covers (-1580761639/1000000 : ℚ) vp0011000101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000101100_0 : Blocks := edgeBlocks% "full/vectors/0011000101100-V-0000.bin"
noncomputable def vp0011000101100 : Blocks := vp0011000101100_0
theorem coverp0011000101100 : Covers (-1579761639/1000000 : ℚ) vp0011000101100 := cover_leaf (by decide +kernel)
private noncomputable def vp001100010110_0 : Blocks := edgeBlocks% "full/vectors/001100010110-V-0000.bin"
noncomputable def vp001100010110 : Blocks := vp001100010110_0
private theorem bp0011000101100 : Branch 0 (-1579761639/2000000 : ℚ) vp001100010110 := by
  apply branch_left_normalized (c:=vp0011000101100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1579761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1579761639/1000000 : ℚ) by norm_num]
  exact coverp0011000101100
private noncomputable def ep0011000101101_0 : Blocks := edgeBlocks% "full/vectors/0011000101101-E-0000.bin"
noncomputable def ep0011000101101 : Blocks := ep0011000101101_0
private theorem idp0011000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100010110.list =
    C ((2:ℤ)^76) * horner X vp0011000101101.list + horner X ep0011000101101.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000101101 : Branch 1 (-1579761639/2000000 : ℚ) vp001100010110 := by
  apply branch_checked idp0011000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1579761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1580761639/1000000 : ℚ) by norm_num]
  exact coverp0011000101101
theorem coverp001100010110 : Covers (-1579761639/2000000 : ℚ) vp001100010110 := join_branches bp0011000101100 bp0011000101101
private noncomputable def vp00110001011_0 : Blocks := edgeBlocks% "full/vectors/00110001011-V-0000.bin"
noncomputable def vp00110001011 : Blocks := vp00110001011_0
private theorem bp001100010110 : Branch 0 (-1579761639/4000000 : ℚ) vp00110001011 := by
  apply branch_left_normalized (c:=vp001100010110) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-1579761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1579761639/2000000 : ℚ) by norm_num]
  exact coverp001100010110
private noncomputable def ep001100010111_0 : Blocks := edgeBlocks% "full/vectors/001100010111-E-0000.bin"
noncomputable def ep001100010111 : Blocks := ep001100010111_0
private theorem idp001100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110001011.list =
    C ((2:ℤ)^132) * horner X vp001100010111.list + horner X ep001100010111.list := by
  exact edge_identity (B := (2:ℤ)^272) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100010111 : Branch 1 (-1579761639/4000000 : ℚ) vp00110001011 := by
  apply branch_checked idp001100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1579761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1581761639/2000000 : ℚ) by norm_num]
  exact coverp001100010111
theorem coverp00110001011 : Covers (-1579761639/4000000 : ℚ) vp00110001011 := join_branches bp001100010110 bp001100010111
private noncomputable def vp0011000101011_0 : Blocks := edgeBlocks% "full/vectors/0011000101011-V-0000.bin"
noncomputable def vp0011000101011 : Blocks := vp0011000101011_0
theorem coverp0011000101011 : Covers (-1578761639/1000000 : ℚ) vp0011000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000101010_0 : Blocks := edgeBlocks% "full/vectors/0011000101010-V-0000.bin"
noncomputable def vp0011000101010 : Blocks := vp0011000101010_0
theorem coverp0011000101010 : Covers (-1577761639/1000000 : ℚ) vp0011000101010 := cover_leaf (by decide +kernel)
private noncomputable def vp001100010101_0 : Blocks := edgeBlocks% "full/vectors/001100010101-V-0000.bin"
noncomputable def vp001100010101 : Blocks := vp001100010101_0
private theorem bp0011000101010 : Branch 0 (-1577761639/2000000 : ℚ) vp001100010101 := by
  apply branch_left_normalized (c:=vp0011000101010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1577761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1577761639/1000000 : ℚ) by norm_num]
  exact coverp0011000101010
private noncomputable def ep0011000101011_0 : Blocks := edgeBlocks% "full/vectors/0011000101011-E-0000.bin"
noncomputable def ep0011000101011 : Blocks := ep0011000101011_0
private theorem idp0011000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100010101.list =
    C ((2:ℤ)^77) * horner X vp0011000101011.list + horner X ep0011000101011.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000101011 : Branch 1 (-1577761639/2000000 : ℚ) vp001100010101 := by
  apply branch_checked idp0011000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1577761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1578761639/1000000 : ℚ) by norm_num]
  exact coverp0011000101011
theorem coverp001100010101 : Covers (-1577761639/2000000 : ℚ) vp001100010101 := join_branches bp0011000101010 bp0011000101011
private noncomputable def vp0011000101001_0 : Blocks := edgeBlocks% "full/vectors/0011000101001-V-0000.bin"
noncomputable def vp0011000101001 : Blocks := vp0011000101001_0
theorem coverp0011000101001 : Covers (-1576761639/1000000 : ℚ) vp0011000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000101000_0 : Blocks := edgeBlocks% "full/vectors/0011000101000-V-0000.bin"
noncomputable def vp0011000101000 : Blocks := vp0011000101000_0
theorem coverp0011000101000 : Covers (-1575761639/1000000 : ℚ) vp0011000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp001100010100_0 : Blocks := edgeBlocks% "full/vectors/001100010100-V-0000.bin"
noncomputable def vp001100010100 : Blocks := vp001100010100_0
private theorem bp0011000101000 : Branch 0 (-1575761639/2000000 : ℚ) vp001100010100 := by
  apply branch_left_normalized (c:=vp0011000101000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1575761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1575761639/1000000 : ℚ) by norm_num]
  exact coverp0011000101000
private noncomputable def ep0011000101001_0 : Blocks := edgeBlocks% "full/vectors/0011000101001-E-0000.bin"
noncomputable def ep0011000101001 : Blocks := ep0011000101001_0
private theorem idp0011000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100010100.list =
    C ((2:ℤ)^77) * horner X vp0011000101001.list + horner X ep0011000101001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000101001 : Branch 1 (-1575761639/2000000 : ℚ) vp001100010100 := by
  apply branch_checked idp0011000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1575761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1576761639/1000000 : ℚ) by norm_num]
  exact coverp0011000101001
theorem coverp001100010100 : Covers (-1575761639/2000000 : ℚ) vp001100010100 := join_branches bp0011000101000 bp0011000101001
private noncomputable def vp00110001010_0 : Blocks := edgeBlocks% "full/vectors/00110001010-V-0000.bin"
noncomputable def vp00110001010 : Blocks := vp00110001010_0
private theorem bp001100010100 : Branch 0 (-1575761639/4000000 : ℚ) vp00110001010 := by
  apply branch_left_normalized (c:=vp001100010100) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1575761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1575761639/2000000 : ℚ) by norm_num]
  exact coverp001100010100
private noncomputable def ep001100010101_0 : Blocks := edgeBlocks% "full/vectors/001100010101-E-0000.bin"
noncomputable def ep001100010101 : Blocks := ep001100010101_0
private theorem idp001100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110001010.list =
    C ((2:ℤ)^133) * horner X vp001100010101.list + horner X ep001100010101.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100010101 : Branch 1 (-1575761639/4000000 : ℚ) vp00110001010 := by
  apply branch_checked idp001100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1575761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1577761639/2000000 : ℚ) by norm_num]
  exact coverp001100010101
theorem coverp00110001010 : Covers (-1575761639/4000000 : ℚ) vp00110001010 := join_branches bp001100010100 bp001100010101
private noncomputable def vp0011000101_0 : Blocks := edgeBlocks% "full/vectors/0011000101-V-0000.bin"
private noncomputable def vp0011000101_1 : Blocks := edgeBlocks% "full/vectors/0011000101-V-0001.bin"
noncomputable def vp0011000101 : Blocks := (Blocks.join vp0011000101_0 vp0011000101_1)
private theorem bp00110001010 : Branch 0 (-1575761639/8000000 : ℚ) vp0011000101 := by
  apply branch_left_normalized (c:=vp00110001010) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-1575761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1575761639/4000000 : ℚ) by norm_num]
  exact coverp00110001010
private noncomputable def ep00110001011_0 : Blocks := edgeBlocks% "full/vectors/00110001011-E-0000.bin"
private noncomputable def ep00110001011_1 : Blocks := edgeBlocks% "full/vectors/00110001011-E-0001.bin"
noncomputable def ep00110001011 : Blocks := (Blocks.join ep00110001011_0 ep00110001011_1)
private theorem idp00110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011000101.list =
    C ((2:ℤ)^246) * horner X vp00110001011.list + horner X ep00110001011.list := by
  exact edge_identity (B := (2:ℤ)^427) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110001011 : Branch 1 (-1575761639/8000000 : ℚ) vp0011000101 := by
  apply branch_checked idp00110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1575761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1579761639/4000000 : ℚ) by norm_num]
  exact coverp00110001011
theorem coverp0011000101 : Covers (-1575761639/8000000 : ℚ) vp0011000101 := join_branches bp00110001010 bp00110001011
private noncomputable def vp0011000100111_0 : Blocks := edgeBlocks% "full/vectors/0011000100111-V-0000.bin"
noncomputable def vp0011000100111 : Blocks := vp0011000100111_0
theorem coverp0011000100111 : Covers (-1574761639/1000000 : ℚ) vp0011000100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000100110_0 : Blocks := edgeBlocks% "full/vectors/0011000100110-V-0000.bin"
noncomputable def vp0011000100110 : Blocks := vp0011000100110_0
theorem coverp0011000100110 : Covers (-1573761639/1000000 : ℚ) vp0011000100110 := cover_leaf (by decide +kernel)
private noncomputable def vp001100010011_0 : Blocks := edgeBlocks% "full/vectors/001100010011-V-0000.bin"
noncomputable def vp001100010011 : Blocks := vp001100010011_0
private theorem bp0011000100110 : Branch 0 (-1573761639/2000000 : ℚ) vp001100010011 := by
  apply branch_left_normalized (c:=vp0011000100110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1573761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1573761639/1000000 : ℚ) by norm_num]
  exact coverp0011000100110
private noncomputable def ep0011000100111_0 : Blocks := edgeBlocks% "full/vectors/0011000100111-E-0000.bin"
noncomputable def ep0011000100111 : Blocks := ep0011000100111_0
private theorem idp0011000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100010011.list =
    C ((2:ℤ)^77) * horner X vp0011000100111.list + horner X ep0011000100111.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000100111 : Branch 1 (-1573761639/2000000 : ℚ) vp001100010011 := by
  apply branch_checked idp0011000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1573761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1574761639/1000000 : ℚ) by norm_num]
  exact coverp0011000100111
theorem coverp001100010011 : Covers (-1573761639/2000000 : ℚ) vp001100010011 := join_branches bp0011000100110 bp0011000100111
private noncomputable def vp0011000100101_0 : Blocks := edgeBlocks% "full/vectors/0011000100101-V-0000.bin"
noncomputable def vp0011000100101 : Blocks := vp0011000100101_0
theorem coverp0011000100101 : Covers (-1572761639/1000000 : ℚ) vp0011000100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000100100_0 : Blocks := edgeBlocks% "full/vectors/0011000100100-V-0000.bin"
noncomputable def vp0011000100100 : Blocks := vp0011000100100_0
theorem coverp0011000100100 : Covers (-1571761639/1000000 : ℚ) vp0011000100100 := cover_leaf (by decide +kernel)
private noncomputable def vp001100010010_0 : Blocks := edgeBlocks% "full/vectors/001100010010-V-0000.bin"
noncomputable def vp001100010010 : Blocks := vp001100010010_0
private theorem bp0011000100100 : Branch 0 (-1571761639/2000000 : ℚ) vp001100010010 := by
  apply branch_left_normalized (c:=vp0011000100100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1571761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1571761639/1000000 : ℚ) by norm_num]
  exact coverp0011000100100
private noncomputable def ep0011000100101_0 : Blocks := edgeBlocks% "full/vectors/0011000100101-E-0000.bin"
noncomputable def ep0011000100101 : Blocks := ep0011000100101_0
private theorem idp0011000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100010010.list =
    C ((2:ℤ)^76) * horner X vp0011000100101.list + horner X ep0011000100101.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000100101 : Branch 1 (-1571761639/2000000 : ℚ) vp001100010010 := by
  apply branch_checked idp0011000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1571761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1572761639/1000000 : ℚ) by norm_num]
  exact coverp0011000100101
theorem coverp001100010010 : Covers (-1571761639/2000000 : ℚ) vp001100010010 := join_branches bp0011000100100 bp0011000100101
private noncomputable def vp00110001001_0 : Blocks := edgeBlocks% "full/vectors/00110001001-V-0000.bin"
noncomputable def vp00110001001 : Blocks := vp00110001001_0
private theorem bp001100010010 : Branch 0 (-1571761639/4000000 : ℚ) vp00110001001 := by
  apply branch_left_normalized (c:=vp001100010010) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-1571761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1571761639/2000000 : ℚ) by norm_num]
  exact coverp001100010010
private noncomputable def ep001100010011_0 : Blocks := edgeBlocks% "full/vectors/001100010011-E-0000.bin"
noncomputable def ep001100010011 : Blocks := ep001100010011_0
private theorem idp001100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110001001.list =
    C ((2:ℤ)^131) * horner X vp001100010011.list + horner X ep001100010011.list := by
  exact edge_identity (B := (2:ℤ)^274) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100010011 : Branch 1 (-1571761639/4000000 : ℚ) vp00110001001 := by
  apply branch_checked idp001100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1571761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1573761639/2000000 : ℚ) by norm_num]
  exact coverp001100010011
theorem coverp00110001001 : Covers (-1571761639/4000000 : ℚ) vp00110001001 := join_branches bp001100010010 bp001100010011
private noncomputable def vp0011000100011_0 : Blocks := edgeBlocks% "full/vectors/0011000100011-V-0000.bin"
noncomputable def vp0011000100011 : Blocks := vp0011000100011_0
theorem coverp0011000100011 : Covers (-1570761639/1000000 : ℚ) vp0011000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000100010_0 : Blocks := edgeBlocks% "full/vectors/0011000100010-V-0000.bin"
noncomputable def vp0011000100010 : Blocks := vp0011000100010_0
theorem coverp0011000100010 : Covers (-1569761639/1000000 : ℚ) vp0011000100010 := cover_leaf (by decide +kernel)
private noncomputable def vp001100010001_0 : Blocks := edgeBlocks% "full/vectors/001100010001-V-0000.bin"
noncomputable def vp001100010001 : Blocks := vp001100010001_0
private theorem bp0011000100010 : Branch 0 (-1569761639/2000000 : ℚ) vp001100010001 := by
  apply branch_left_normalized (c:=vp0011000100010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1569761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1569761639/1000000 : ℚ) by norm_num]
  exact coverp0011000100010
private noncomputable def ep0011000100011_0 : Blocks := edgeBlocks% "full/vectors/0011000100011-E-0000.bin"
noncomputable def ep0011000100011 : Blocks := ep0011000100011_0
private theorem idp0011000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100010001.list =
    C ((2:ℤ)^76) * horner X vp0011000100011.list + horner X ep0011000100011.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000100011 : Branch 1 (-1569761639/2000000 : ℚ) vp001100010001 := by
  apply branch_checked idp0011000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1569761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1570761639/1000000 : ℚ) by norm_num]
  exact coverp0011000100011
theorem coverp001100010001 : Covers (-1569761639/2000000 : ℚ) vp001100010001 := join_branches bp0011000100010 bp0011000100011
private noncomputable def vp0011000100001_0 : Blocks := edgeBlocks% "full/vectors/0011000100001-V-0000.bin"
noncomputable def vp0011000100001 : Blocks := vp0011000100001_0
theorem coverp0011000100001 : Covers (-1568761639/1000000 : ℚ) vp0011000100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000100000_0 : Blocks := edgeBlocks% "full/vectors/0011000100000-V-0000.bin"
noncomputable def vp0011000100000 : Blocks := vp0011000100000_0
theorem coverp0011000100000 : Covers (-1567761639/1000000 : ℚ) vp0011000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp001100010000_0 : Blocks := edgeBlocks% "full/vectors/001100010000-V-0000.bin"
noncomputable def vp001100010000 : Blocks := vp001100010000_0
private theorem bp0011000100000 : Branch 0 (-1567761639/2000000 : ℚ) vp001100010000 := by
  apply branch_left_normalized (c:=vp0011000100000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1567761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1567761639/1000000 : ℚ) by norm_num]
  exact coverp0011000100000
private noncomputable def ep0011000100001_0 : Blocks := edgeBlocks% "full/vectors/0011000100001-E-0000.bin"
noncomputable def ep0011000100001 : Blocks := ep0011000100001_0
private theorem idp0011000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100010000.list =
    C ((2:ℤ)^76) * horner X vp0011000100001.list + horner X ep0011000100001.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000100001 : Branch 1 (-1567761639/2000000 : ℚ) vp001100010000 := by
  apply branch_checked idp0011000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1567761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1568761639/1000000 : ℚ) by norm_num]
  exact coverp0011000100001
theorem coverp001100010000 : Covers (-1567761639/2000000 : ℚ) vp001100010000 := join_branches bp0011000100000 bp0011000100001
private noncomputable def vp00110001000_0 : Blocks := edgeBlocks% "full/vectors/00110001000-V-0000.bin"
noncomputable def vp00110001000 : Blocks := vp00110001000_0
private theorem bp001100010000 : Branch 0 (-1567761639/4000000 : ℚ) vp00110001000 := by
  apply branch_left_normalized (c:=vp001100010000) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-1567761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1567761639/2000000 : ℚ) by norm_num]
  exact coverp001100010000
private noncomputable def ep001100010001_0 : Blocks := edgeBlocks% "full/vectors/001100010001-E-0000.bin"
noncomputable def ep001100010001 : Blocks := ep001100010001_0
private theorem idp001100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110001000.list =
    C ((2:ℤ)^133) * horner X vp001100010001.list + horner X ep001100010001.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100010001 : Branch 1 (-1567761639/4000000 : ℚ) vp00110001000 := by
  apply branch_checked idp001100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1567761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1569761639/2000000 : ℚ) by norm_num]
  exact coverp001100010001
theorem coverp00110001000 : Covers (-1567761639/4000000 : ℚ) vp00110001000 := join_branches bp001100010000 bp001100010001
private noncomputable def vp0011000100_0 : Blocks := edgeBlocks% "full/vectors/0011000100-V-0000.bin"
private noncomputable def vp0011000100_1 : Blocks := edgeBlocks% "full/vectors/0011000100-V-0001.bin"
noncomputable def vp0011000100 : Blocks := (Blocks.join vp0011000100_0 vp0011000100_1)
private theorem bp00110001000 : Branch 0 (-1567761639/8000000 : ℚ) vp0011000100 := by
  apply branch_left_normalized (c:=vp00110001000) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-1567761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1567761639/4000000 : ℚ) by norm_num]
  exact coverp00110001000
private noncomputable def ep00110001001_0 : Blocks := edgeBlocks% "full/vectors/00110001001-E-0000.bin"
private noncomputable def ep00110001001_1 : Blocks := edgeBlocks% "full/vectors/00110001001-E-0001.bin"
noncomputable def ep00110001001 : Blocks := (Blocks.join ep00110001001_0 ep00110001001_1)
private theorem idp00110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011000100.list =
    C ((2:ℤ)^244) * horner X vp00110001001.list + horner X ep00110001001.list := by
  exact edge_identity (B := (2:ℤ)^427) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110001001 : Branch 1 (-1567761639/8000000 : ℚ) vp0011000100 := by
  apply branch_checked idp00110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1567761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1571761639/4000000 : ℚ) by norm_num]
  exact coverp00110001001
theorem coverp0011000100 : Covers (-1567761639/8000000 : ℚ) vp0011000100 := join_branches bp00110001000 bp00110001001
private noncomputable def vp001100010_0 : Blocks := edgeBlocks% "full/vectors/001100010-V-0000.bin"
private noncomputable def vp001100010_1 : Blocks := edgeBlocks% "full/vectors/001100010-V-0001.bin"
private noncomputable def vp001100010_2 : Blocks := edgeBlocks% "full/vectors/001100010-V-0002.bin"
private noncomputable def vp001100010_3 : Blocks := edgeBlocks% "full/vectors/001100010-V-0003.bin"
noncomputable def vp001100010 : Blocks := (Blocks.join (Blocks.join vp001100010_0 vp001100010_1) (Blocks.join vp001100010_2 vp001100010_3))
private theorem bp0011000100 : Branch 0 (-1567761639/16000000 : ℚ) vp001100010 := by
  apply branch_left_normalized (c:=vp0011000100) (k:=0) (m:=220) (by decide +kernel)
  rw [show 2*(-1567761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1567761639/8000000 : ℚ) by norm_num]
  exact coverp0011000100
private noncomputable def ep0011000101_0 : Blocks := edgeBlocks% "full/vectors/0011000101-E-0000.bin"
private noncomputable def ep0011000101_1 : Blocks := edgeBlocks% "full/vectors/0011000101-E-0001.bin"
private noncomputable def ep0011000101_2 : Blocks := edgeBlocks% "full/vectors/0011000101-E-0002.bin"
private noncomputable def ep0011000101_3 : Blocks := edgeBlocks% "full/vectors/0011000101-E-0003.bin"
noncomputable def ep0011000101 : Blocks := (Blocks.join (Blocks.join ep0011000101_0 ep0011000101_1) (Blocks.join ep0011000101_2 ep0011000101_3))
private theorem idp0011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100010.list =
    C ((2:ℤ)^464) * horner X vp0011000101.list + horner X ep0011000101.list := by
  exact edge_identity (B := (2:ℤ)^729) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000101 : Branch 1 (-1567761639/16000000 : ℚ) vp001100010 := by
  apply branch_checked idp0011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1567761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1575761639/8000000 : ℚ) by norm_num]
  exact coverp0011000101
theorem coverp001100010 : Covers (-1567761639/16000000 : ℚ) vp001100010 := join_branches bp0011000100 bp0011000101
private noncomputable def vp00110001_0 : Blocks := edgeBlocks% "full/vectors/00110001-V-0000.bin"
private noncomputable def vp00110001_1 : Blocks := edgeBlocks% "full/vectors/00110001-V-0001.bin"
private noncomputable def vp00110001_2 : Blocks := edgeBlocks% "full/vectors/00110001-V-0002.bin"
private noncomputable def vp00110001_3 : Blocks := edgeBlocks% "full/vectors/00110001-V-0003.bin"
private noncomputable def vp00110001_4 : Blocks := edgeBlocks% "full/vectors/00110001-V-0004.bin"
private noncomputable def vp00110001_5 : Blocks := edgeBlocks% "full/vectors/00110001-V-0005.bin"
private noncomputable def vp00110001_6 : Blocks := edgeBlocks% "full/vectors/00110001-V-0006.bin"
noncomputable def vp00110001 : Blocks := (Blocks.join (Blocks.join vp00110001_0 (Blocks.join vp00110001_1 vp00110001_2)) (Blocks.join (Blocks.join vp00110001_3 vp00110001_4) (Blocks.join vp00110001_5 vp00110001_6)))
private theorem bp001100010 : Branch 0 (-1567761639/32000000 : ℚ) vp00110001 := by
  apply branch_left_normalized (c:=vp001100010) (k:=0) (m:=417) (by decide +kernel)
  rw [show 2*(-1567761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1567761639/16000000 : ℚ) by norm_num]
  exact coverp001100010
private noncomputable def ep001100011_0 : Blocks := edgeBlocks% "full/vectors/001100011-E-0000.bin"
private noncomputable def ep001100011_1 : Blocks := edgeBlocks% "full/vectors/001100011-E-0001.bin"
private noncomputable def ep001100011_2 : Blocks := edgeBlocks% "full/vectors/001100011-E-0002.bin"
private noncomputable def ep001100011_3 : Blocks := edgeBlocks% "full/vectors/001100011-E-0003.bin"
private noncomputable def ep001100011_4 : Blocks := edgeBlocks% "full/vectors/001100011-E-0004.bin"
private noncomputable def ep001100011_5 : Blocks := edgeBlocks% "full/vectors/001100011-E-0005.bin"
private noncomputable def ep001100011_6 : Blocks := edgeBlocks% "full/vectors/001100011-E-0006.bin"
noncomputable def ep001100011 : Blocks := (Blocks.join (Blocks.join ep001100011_0 (Blocks.join ep001100011_1 ep001100011_2)) (Blocks.join (Blocks.join ep001100011_3 ep001100011_4) (Blocks.join ep001100011_5 ep001100011_6)))
private theorem idp001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110001.list =
    C ((2:ℤ)^902) * horner X vp001100011.list + horner X ep001100011.list := by
  exact edge_identity (B := (2:ℤ)^1329) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100011 : Branch 1 (-1567761639/32000000 : ℚ) vp00110001 := by
  apply branch_checked idp001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1567761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1583761639/16000000 : ℚ) by norm_num]
  exact coverp001100011
theorem coverp00110001 : Covers (-1567761639/32000000 : ℚ) vp00110001 := join_branches bp001100010 bp001100011
private noncomputable def vp0011000011111_0 : Blocks := edgeBlocks% "full/vectors/0011000011111-V-0000.bin"
noncomputable def vp0011000011111 : Blocks := vp0011000011111_0
theorem coverp0011000011111 : Covers (-1566761639/1000000 : ℚ) vp0011000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000011110_0 : Blocks := edgeBlocks% "full/vectors/0011000011110-V-0000.bin"
noncomputable def vp0011000011110 : Blocks := vp0011000011110_0
theorem coverp0011000011110 : Covers (-1565761639/1000000 : ℚ) vp0011000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp001100001111_0 : Blocks := edgeBlocks% "full/vectors/001100001111-V-0000.bin"
noncomputable def vp001100001111 : Blocks := vp001100001111_0
private theorem bp0011000011110 : Branch 0 (-1565761639/2000000 : ℚ) vp001100001111 := by
  apply branch_left_normalized (c:=vp0011000011110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1565761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1565761639/1000000 : ℚ) by norm_num]
  exact coverp0011000011110
private noncomputable def ep0011000011111_0 : Blocks := edgeBlocks% "full/vectors/0011000011111-E-0000.bin"
noncomputable def ep0011000011111 : Blocks := ep0011000011111_0
private theorem idp0011000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100001111.list =
    C ((2:ℤ)^77) * horner X vp0011000011111.list + horner X ep0011000011111.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000011111 : Branch 1 (-1565761639/2000000 : ℚ) vp001100001111 := by
  apply branch_checked idp0011000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1565761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1566761639/1000000 : ℚ) by norm_num]
  exact coverp0011000011111
theorem coverp001100001111 : Covers (-1565761639/2000000 : ℚ) vp001100001111 := join_branches bp0011000011110 bp0011000011111
private noncomputable def vp0011000011101_0 : Blocks := edgeBlocks% "full/vectors/0011000011101-V-0000.bin"
noncomputable def vp0011000011101 : Blocks := vp0011000011101_0
theorem coverp0011000011101 : Covers (-1564761639/1000000 : ℚ) vp0011000011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000011100_0 : Blocks := edgeBlocks% "full/vectors/0011000011100-V-0000.bin"
noncomputable def vp0011000011100 : Blocks := vp0011000011100_0
theorem coverp0011000011100 : Covers (-1563761639/1000000 : ℚ) vp0011000011100 := cover_leaf (by decide +kernel)
private noncomputable def vp001100001110_0 : Blocks := edgeBlocks% "full/vectors/001100001110-V-0000.bin"
noncomputable def vp001100001110 : Blocks := vp001100001110_0
private theorem bp0011000011100 : Branch 0 (-1563761639/2000000 : ℚ) vp001100001110 := by
  apply branch_left_normalized (c:=vp0011000011100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1563761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1563761639/1000000 : ℚ) by norm_num]
  exact coverp0011000011100
private noncomputable def ep0011000011101_0 : Blocks := edgeBlocks% "full/vectors/0011000011101-E-0000.bin"
noncomputable def ep0011000011101 : Blocks := ep0011000011101_0
private theorem idp0011000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100001110.list =
    C ((2:ℤ)^77) * horner X vp0011000011101.list + horner X ep0011000011101.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000011101 : Branch 1 (-1563761639/2000000 : ℚ) vp001100001110 := by
  apply branch_checked idp0011000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1563761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1564761639/1000000 : ℚ) by norm_num]
  exact coverp0011000011101
theorem coverp001100001110 : Covers (-1563761639/2000000 : ℚ) vp001100001110 := join_branches bp0011000011100 bp0011000011101
private noncomputable def vp00110000111_0 : Blocks := edgeBlocks% "full/vectors/00110000111-V-0000.bin"
noncomputable def vp00110000111 : Blocks := vp00110000111_0
private theorem bp001100001110 : Branch 0 (-1563761639/4000000 : ℚ) vp00110000111 := by
  apply branch_left_normalized (c:=vp001100001110) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1563761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1563761639/2000000 : ℚ) by norm_num]
  exact coverp001100001110
private noncomputable def ep001100001111_0 : Blocks := edgeBlocks% "full/vectors/001100001111-E-0000.bin"
noncomputable def ep001100001111 : Blocks := ep001100001111_0
private theorem idp001100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110000111.list =
    C ((2:ℤ)^134) * horner X vp001100001111.list + horner X ep001100001111.list := by
  exact edge_identity (B := (2:ℤ)^277) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100001111 : Branch 1 (-1563761639/4000000 : ℚ) vp00110000111 := by
  apply branch_checked idp001100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1563761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1565761639/2000000 : ℚ) by norm_num]
  exact coverp001100001111
theorem coverp00110000111 : Covers (-1563761639/4000000 : ℚ) vp00110000111 := join_branches bp001100001110 bp001100001111
private noncomputable def vp0011000011011_0 : Blocks := edgeBlocks% "full/vectors/0011000011011-V-0000.bin"
noncomputable def vp0011000011011 : Blocks := vp0011000011011_0
theorem coverp0011000011011 : Covers (-1562761639/1000000 : ℚ) vp0011000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000011010_0 : Blocks := edgeBlocks% "full/vectors/0011000011010-V-0000.bin"
noncomputable def vp0011000011010 : Blocks := vp0011000011010_0
theorem coverp0011000011010 : Covers (-1561761639/1000000 : ℚ) vp0011000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp001100001101_0 : Blocks := edgeBlocks% "full/vectors/001100001101-V-0000.bin"
noncomputable def vp001100001101 : Blocks := vp001100001101_0
private theorem bp0011000011010 : Branch 0 (-1561761639/2000000 : ℚ) vp001100001101 := by
  apply branch_left_normalized (c:=vp0011000011010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1561761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1561761639/1000000 : ℚ) by norm_num]
  exact coverp0011000011010
private noncomputable def ep0011000011011_0 : Blocks := edgeBlocks% "full/vectors/0011000011011-E-0000.bin"
noncomputable def ep0011000011011 : Blocks := ep0011000011011_0
private theorem idp0011000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100001101.list =
    C ((2:ℤ)^76) * horner X vp0011000011011.list + horner X ep0011000011011.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000011011 : Branch 1 (-1561761639/2000000 : ℚ) vp001100001101 := by
  apply branch_checked idp0011000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1561761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1562761639/1000000 : ℚ) by norm_num]
  exact coverp0011000011011
theorem coverp001100001101 : Covers (-1561761639/2000000 : ℚ) vp001100001101 := join_branches bp0011000011010 bp0011000011011
private noncomputable def vp0011000011001_0 : Blocks := edgeBlocks% "full/vectors/0011000011001-V-0000.bin"
noncomputable def vp0011000011001 : Blocks := vp0011000011001_0
theorem coverp0011000011001 : Covers (-1560761639/1000000 : ℚ) vp0011000011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000011000_0 : Blocks := edgeBlocks% "full/vectors/0011000011000-V-0000.bin"
noncomputable def vp0011000011000 : Blocks := vp0011000011000_0
theorem coverp0011000011000 : Covers (-1559761639/1000000 : ℚ) vp0011000011000 := cover_leaf (by decide +kernel)
private noncomputable def vp001100001100_0 : Blocks := edgeBlocks% "full/vectors/001100001100-V-0000.bin"
noncomputable def vp001100001100 : Blocks := vp001100001100_0
private theorem bp0011000011000 : Branch 0 (-1559761639/2000000 : ℚ) vp001100001100 := by
  apply branch_left_normalized (c:=vp0011000011000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1559761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1559761639/1000000 : ℚ) by norm_num]
  exact coverp0011000011000
private noncomputable def ep0011000011001_0 : Blocks := edgeBlocks% "full/vectors/0011000011001-E-0000.bin"
noncomputable def ep0011000011001 : Blocks := ep0011000011001_0
private theorem idp0011000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100001100.list =
    C ((2:ℤ)^77) * horner X vp0011000011001.list + horner X ep0011000011001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000011001 : Branch 1 (-1559761639/2000000 : ℚ) vp001100001100 := by
  apply branch_checked idp0011000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1559761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1560761639/1000000 : ℚ) by norm_num]
  exact coverp0011000011001
theorem coverp001100001100 : Covers (-1559761639/2000000 : ℚ) vp001100001100 := join_branches bp0011000011000 bp0011000011001
private noncomputable def vp00110000110_0 : Blocks := edgeBlocks% "full/vectors/00110000110-V-0000.bin"
noncomputable def vp00110000110 : Blocks := vp00110000110_0
private theorem bp001100001100 : Branch 0 (-1559761639/4000000 : ℚ) vp00110000110 := by
  apply branch_left_normalized (c:=vp001100001100) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1559761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1559761639/2000000 : ℚ) by norm_num]
  exact coverp001100001100
private noncomputable def ep001100001101_0 : Blocks := edgeBlocks% "full/vectors/001100001101-E-0000.bin"
noncomputable def ep001100001101 : Blocks := ep001100001101_0
private theorem idp001100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110000110.list =
    C ((2:ℤ)^132) * horner X vp001100001101.list + horner X ep001100001101.list := by
  exact edge_identity (B := (2:ℤ)^274) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100001101 : Branch 1 (-1559761639/4000000 : ℚ) vp00110000110 := by
  apply branch_checked idp001100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1559761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1561761639/2000000 : ℚ) by norm_num]
  exact coverp001100001101
theorem coverp00110000110 : Covers (-1559761639/4000000 : ℚ) vp00110000110 := join_branches bp001100001100 bp001100001101
private noncomputable def vp0011000011_0 : Blocks := edgeBlocks% "full/vectors/0011000011-V-0000.bin"
private noncomputable def vp0011000011_1 : Blocks := edgeBlocks% "full/vectors/0011000011-V-0001.bin"
noncomputable def vp0011000011 : Blocks := (Blocks.join vp0011000011_0 vp0011000011_1)
private theorem bp00110000110 : Branch 0 (-1559761639/8000000 : ℚ) vp0011000011 := by
  apply branch_left_normalized (c:=vp00110000110) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-1559761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1559761639/4000000 : ℚ) by norm_num]
  exact coverp00110000110
private noncomputable def ep00110000111_0 : Blocks := edgeBlocks% "full/vectors/00110000111-E-0000.bin"
private noncomputable def ep00110000111_1 : Blocks := edgeBlocks% "full/vectors/00110000111-E-0001.bin"
noncomputable def ep00110000111 : Blocks := (Blocks.join ep00110000111_0 ep00110000111_1)
private theorem idp00110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011000011.list =
    C ((2:ℤ)^243) * horner X vp00110000111.list + horner X ep00110000111.list := by
  exact edge_identity (B := (2:ℤ)^427) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110000111 : Branch 1 (-1559761639/8000000 : ℚ) vp0011000011 := by
  apply branch_checked idp00110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1559761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1563761639/4000000 : ℚ) by norm_num]
  exact coverp00110000111
theorem coverp0011000011 : Covers (-1559761639/8000000 : ℚ) vp0011000011 := join_branches bp00110000110 bp00110000111
private noncomputable def vp0011000010111_0 : Blocks := edgeBlocks% "full/vectors/0011000010111-V-0000.bin"
noncomputable def vp0011000010111 : Blocks := vp0011000010111_0
theorem coverp0011000010111 : Covers (-1558761639/1000000 : ℚ) vp0011000010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000010110_0 : Blocks := edgeBlocks% "full/vectors/0011000010110-V-0000.bin"
noncomputable def vp0011000010110 : Blocks := vp0011000010110_0
theorem coverp0011000010110 : Covers (-1557761639/1000000 : ℚ) vp0011000010110 := cover_leaf (by decide +kernel)
private noncomputable def vp001100001011_0 : Blocks := edgeBlocks% "full/vectors/001100001011-V-0000.bin"
noncomputable def vp001100001011 : Blocks := vp001100001011_0
private theorem bp0011000010110 : Branch 0 (-1557761639/2000000 : ℚ) vp001100001011 := by
  apply branch_left_normalized (c:=vp0011000010110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1557761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1557761639/1000000 : ℚ) by norm_num]
  exact coverp0011000010110
private noncomputable def ep0011000010111_0 : Blocks := edgeBlocks% "full/vectors/0011000010111-E-0000.bin"
noncomputable def ep0011000010111 : Blocks := ep0011000010111_0
private theorem idp0011000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100001011.list =
    C ((2:ℤ)^76) * horner X vp0011000010111.list + horner X ep0011000010111.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000010111 : Branch 1 (-1557761639/2000000 : ℚ) vp001100001011 := by
  apply branch_checked idp0011000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1557761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1558761639/1000000 : ℚ) by norm_num]
  exact coverp0011000010111
theorem coverp001100001011 : Covers (-1557761639/2000000 : ℚ) vp001100001011 := join_branches bp0011000010110 bp0011000010111
private noncomputable def vp0011000010101_0 : Blocks := edgeBlocks% "full/vectors/0011000010101-V-0000.bin"
noncomputable def vp0011000010101 : Blocks := vp0011000010101_0
theorem coverp0011000010101 : Covers (-1556761639/1000000 : ℚ) vp0011000010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000010100_0 : Blocks := edgeBlocks% "full/vectors/0011000010100-V-0000.bin"
noncomputable def vp0011000010100 : Blocks := vp0011000010100_0
theorem coverp0011000010100 : Covers (-1555761639/1000000 : ℚ) vp0011000010100 := cover_leaf (by decide +kernel)
private noncomputable def vp001100001010_0 : Blocks := edgeBlocks% "full/vectors/001100001010-V-0000.bin"
noncomputable def vp001100001010 : Blocks := vp001100001010_0
private theorem bp0011000010100 : Branch 0 (-1555761639/2000000 : ℚ) vp001100001010 := by
  apply branch_left_normalized (c:=vp0011000010100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1555761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1555761639/1000000 : ℚ) by norm_num]
  exact coverp0011000010100
private noncomputable def ep0011000010101_0 : Blocks := edgeBlocks% "full/vectors/0011000010101-E-0000.bin"
noncomputable def ep0011000010101 : Blocks := ep0011000010101_0
private theorem idp0011000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100001010.list =
    C ((2:ℤ)^77) * horner X vp0011000010101.list + horner X ep0011000010101.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000010101 : Branch 1 (-1555761639/2000000 : ℚ) vp001100001010 := by
  apply branch_checked idp0011000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1555761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1556761639/1000000 : ℚ) by norm_num]
  exact coverp0011000010101
theorem coverp001100001010 : Covers (-1555761639/2000000 : ℚ) vp001100001010 := join_branches bp0011000010100 bp0011000010101
private noncomputable def vp00110000101_0 : Blocks := edgeBlocks% "full/vectors/00110000101-V-0000.bin"
noncomputable def vp00110000101 : Blocks := vp00110000101_0
private theorem bp001100001010 : Branch 0 (-1555761639/4000000 : ℚ) vp00110000101 := by
  apply branch_left_normalized (c:=vp001100001010) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1555761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1555761639/2000000 : ℚ) by norm_num]
  exact coverp001100001010
private noncomputable def ep001100001011_0 : Blocks := edgeBlocks% "full/vectors/001100001011-E-0000.bin"
noncomputable def ep001100001011 : Blocks := ep001100001011_0
private theorem idp001100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110000101.list =
    C ((2:ℤ)^134) * horner X vp001100001011.list + horner X ep001100001011.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100001011 : Branch 1 (-1555761639/4000000 : ℚ) vp00110000101 := by
  apply branch_checked idp001100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1555761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1557761639/2000000 : ℚ) by norm_num]
  exact coverp001100001011
theorem coverp00110000101 : Covers (-1555761639/4000000 : ℚ) vp00110000101 := join_branches bp001100001010 bp001100001011
private noncomputable def vp0011000010011_0 : Blocks := edgeBlocks% "full/vectors/0011000010011-V-0000.bin"
noncomputable def vp0011000010011 : Blocks := vp0011000010011_0
theorem coverp0011000010011 : Covers (-1554761639/1000000 : ℚ) vp0011000010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000010010_0 : Blocks := edgeBlocks% "full/vectors/0011000010010-V-0000.bin"
noncomputable def vp0011000010010 : Blocks := vp0011000010010_0
theorem coverp0011000010010 : Covers (-1553761639/1000000 : ℚ) vp0011000010010 := cover_leaf (by decide +kernel)
private noncomputable def vp001100001001_0 : Blocks := edgeBlocks% "full/vectors/001100001001-V-0000.bin"
noncomputable def vp001100001001 : Blocks := vp001100001001_0
private theorem bp0011000010010 : Branch 0 (-1553761639/2000000 : ℚ) vp001100001001 := by
  apply branch_left_normalized (c:=vp0011000010010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1553761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1553761639/1000000 : ℚ) by norm_num]
  exact coverp0011000010010
private noncomputable def ep0011000010011_0 : Blocks := edgeBlocks% "full/vectors/0011000010011-E-0000.bin"
noncomputable def ep0011000010011 : Blocks := ep0011000010011_0
private theorem idp0011000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100001001.list =
    C ((2:ℤ)^77) * horner X vp0011000010011.list + horner X ep0011000010011.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000010011 : Branch 1 (-1553761639/2000000 : ℚ) vp001100001001 := by
  apply branch_checked idp0011000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1553761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1554761639/1000000 : ℚ) by norm_num]
  exact coverp0011000010011
theorem coverp001100001001 : Covers (-1553761639/2000000 : ℚ) vp001100001001 := join_branches bp0011000010010 bp0011000010011
private noncomputable def vp0011000010001_0 : Blocks := edgeBlocks% "full/vectors/0011000010001-V-0000.bin"
noncomputable def vp0011000010001 : Blocks := vp0011000010001_0
theorem coverp0011000010001 : Covers (-1552761639/1000000 : ℚ) vp0011000010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000010000_0 : Blocks := edgeBlocks% "full/vectors/0011000010000-V-0000.bin"
noncomputable def vp0011000010000 : Blocks := vp0011000010000_0
theorem coverp0011000010000 : Covers (-1551761639/1000000 : ℚ) vp0011000010000 := cover_leaf (by decide +kernel)
private noncomputable def vp001100001000_0 : Blocks := edgeBlocks% "full/vectors/001100001000-V-0000.bin"
noncomputable def vp001100001000 : Blocks := vp001100001000_0
private theorem bp0011000010000 : Branch 0 (-1551761639/2000000 : ℚ) vp001100001000 := by
  apply branch_left_normalized (c:=vp0011000010000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1551761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1551761639/1000000 : ℚ) by norm_num]
  exact coverp0011000010000
private noncomputable def ep0011000010001_0 : Blocks := edgeBlocks% "full/vectors/0011000010001-E-0000.bin"
noncomputable def ep0011000010001 : Blocks := ep0011000010001_0
private theorem idp0011000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100001000.list =
    C ((2:ℤ)^77) * horner X vp0011000010001.list + horner X ep0011000010001.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000010001 : Branch 1 (-1551761639/2000000 : ℚ) vp001100001000 := by
  apply branch_checked idp0011000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1551761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1552761639/1000000 : ℚ) by norm_num]
  exact coverp0011000010001
theorem coverp001100001000 : Covers (-1551761639/2000000 : ℚ) vp001100001000 := join_branches bp0011000010000 bp0011000010001
private noncomputable def vp00110000100_0 : Blocks := edgeBlocks% "full/vectors/00110000100-V-0000.bin"
noncomputable def vp00110000100 : Blocks := vp00110000100_0
private theorem bp001100001000 : Branch 0 (-1551761639/4000000 : ℚ) vp00110000100 := by
  apply branch_left_normalized (c:=vp001100001000) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1551761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1551761639/2000000 : ℚ) by norm_num]
  exact coverp001100001000
private noncomputable def ep001100001001_0 : Blocks := edgeBlocks% "full/vectors/001100001001-E-0000.bin"
noncomputable def ep001100001001 : Blocks := ep001100001001_0
private theorem idp001100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110000100.list =
    C ((2:ℤ)^134) * horner X vp001100001001.list + horner X ep001100001001.list := by
  exact edge_identity (B := (2:ℤ)^276) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100001001 : Branch 1 (-1551761639/4000000 : ℚ) vp00110000100 := by
  apply branch_checked idp001100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1551761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1553761639/2000000 : ℚ) by norm_num]
  exact coverp001100001001
theorem coverp00110000100 : Covers (-1551761639/4000000 : ℚ) vp00110000100 := join_branches bp001100001000 bp001100001001
private noncomputable def vp0011000010_0 : Blocks := edgeBlocks% "full/vectors/0011000010-V-0000.bin"
private noncomputable def vp0011000010_1 : Blocks := edgeBlocks% "full/vectors/0011000010-V-0001.bin"
noncomputable def vp0011000010 : Blocks := (Blocks.join vp0011000010_0 vp0011000010_1)
private theorem bp00110000100 : Branch 0 (-1551761639/8000000 : ℚ) vp0011000010 := by
  apply branch_left_normalized (c:=vp00110000100) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-1551761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1551761639/4000000 : ℚ) by norm_num]
  exact coverp00110000100
private noncomputable def ep00110000101_0 : Blocks := edgeBlocks% "full/vectors/00110000101-E-0000.bin"
private noncomputable def ep00110000101_1 : Blocks := edgeBlocks% "full/vectors/00110000101-E-0001.bin"
noncomputable def ep00110000101 : Blocks := (Blocks.join ep00110000101_0 ep00110000101_1)
private theorem idp00110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011000010.list =
    C ((2:ℤ)^246) * horner X vp00110000101.list + horner X ep00110000101.list := by
  exact edge_identity (B := (2:ℤ)^429) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110000101 : Branch 1 (-1551761639/8000000 : ℚ) vp0011000010 := by
  apply branch_checked idp00110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1551761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1555761639/4000000 : ℚ) by norm_num]
  exact coverp00110000101
theorem coverp0011000010 : Covers (-1551761639/8000000 : ℚ) vp0011000010 := join_branches bp00110000100 bp00110000101
private noncomputable def vp001100001_0 : Blocks := edgeBlocks% "full/vectors/001100001-V-0000.bin"
private noncomputable def vp001100001_1 : Blocks := edgeBlocks% "full/vectors/001100001-V-0001.bin"
private noncomputable def vp001100001_2 : Blocks := edgeBlocks% "full/vectors/001100001-V-0002.bin"
private noncomputable def vp001100001_3 : Blocks := edgeBlocks% "full/vectors/001100001-V-0003.bin"
noncomputable def vp001100001 : Blocks := (Blocks.join (Blocks.join vp001100001_0 vp001100001_1) (Blocks.join vp001100001_2 vp001100001_3))
private theorem bp0011000010 : Branch 0 (-1551761639/16000000 : ℚ) vp001100001 := by
  apply branch_left_normalized (c:=vp0011000010) (k:=0) (m:=221) (by decide +kernel)
  rw [show 2*(-1551761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1551761639/8000000 : ℚ) by norm_num]
  exact coverp0011000010
private noncomputable def ep0011000011_0 : Blocks := edgeBlocks% "full/vectors/0011000011-E-0000.bin"
private noncomputable def ep0011000011_1 : Blocks := edgeBlocks% "full/vectors/0011000011-E-0001.bin"
private noncomputable def ep0011000011_2 : Blocks := edgeBlocks% "full/vectors/0011000011-E-0002.bin"
private noncomputable def ep0011000011_3 : Blocks := edgeBlocks% "full/vectors/0011000011-E-0003.bin"
noncomputable def ep0011000011 : Blocks := (Blocks.join (Blocks.join ep0011000011_0 ep0011000011_1) (Blocks.join ep0011000011_2 ep0011000011_3))
private theorem idp0011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100001.list =
    C ((2:ℤ)^468) * horner X vp0011000011.list + horner X ep0011000011.list := by
  exact edge_identity (B := (2:ℤ)^734) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000011 : Branch 1 (-1551761639/16000000 : ℚ) vp001100001 := by
  apply branch_checked idp0011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1551761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1559761639/8000000 : ℚ) by norm_num]
  exact coverp0011000011
theorem coverp001100001 : Covers (-1551761639/16000000 : ℚ) vp001100001 := join_branches bp0011000010 bp0011000011
private noncomputable def vp0011000001111_0 : Blocks := edgeBlocks% "full/vectors/0011000001111-V-0000.bin"
noncomputable def vp0011000001111 : Blocks := vp0011000001111_0
theorem coverp0011000001111 : Covers (-1550761639/1000000 : ℚ) vp0011000001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000001110_0 : Blocks := edgeBlocks% "full/vectors/0011000001110-V-0000.bin"
noncomputable def vp0011000001110 : Blocks := vp0011000001110_0
theorem coverp0011000001110 : Covers (-1549761639/1000000 : ℚ) vp0011000001110 := cover_leaf (by decide +kernel)
private noncomputable def vp001100000111_0 : Blocks := edgeBlocks% "full/vectors/001100000111-V-0000.bin"
noncomputable def vp001100000111 : Blocks := vp001100000111_0
private theorem bp0011000001110 : Branch 0 (-1549761639/2000000 : ℚ) vp001100000111 := by
  apply branch_left_normalized (c:=vp0011000001110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1549761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1549761639/1000000 : ℚ) by norm_num]
  exact coverp0011000001110
private noncomputable def ep0011000001111_0 : Blocks := edgeBlocks% "full/vectors/0011000001111-E-0000.bin"
noncomputable def ep0011000001111 : Blocks := ep0011000001111_0
private theorem idp0011000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100000111.list =
    C ((2:ℤ)^77) * horner X vp0011000001111.list + horner X ep0011000001111.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000001111 : Branch 1 (-1549761639/2000000 : ℚ) vp001100000111 := by
  apply branch_checked idp0011000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1549761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1550761639/1000000 : ℚ) by norm_num]
  exact coverp0011000001111
theorem coverp001100000111 : Covers (-1549761639/2000000 : ℚ) vp001100000111 := join_branches bp0011000001110 bp0011000001111
private noncomputable def vp0011000001101_0 : Blocks := edgeBlocks% "full/vectors/0011000001101-V-0000.bin"
noncomputable def vp0011000001101 : Blocks := vp0011000001101_0
theorem coverp0011000001101 : Covers (-1548761639/1000000 : ℚ) vp0011000001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000001100_0 : Blocks := edgeBlocks% "full/vectors/0011000001100-V-0000.bin"
noncomputable def vp0011000001100 : Blocks := vp0011000001100_0
theorem coverp0011000001100 : Covers (-1547761639/1000000 : ℚ) vp0011000001100 := cover_leaf (by decide +kernel)
private noncomputable def vp001100000110_0 : Blocks := edgeBlocks% "full/vectors/001100000110-V-0000.bin"
noncomputable def vp001100000110 : Blocks := vp001100000110_0
private theorem bp0011000001100 : Branch 0 (-1547761639/2000000 : ℚ) vp001100000110 := by
  apply branch_left_normalized (c:=vp0011000001100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1547761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1547761639/1000000 : ℚ) by norm_num]
  exact coverp0011000001100
private noncomputable def ep0011000001101_0 : Blocks := edgeBlocks% "full/vectors/0011000001101-E-0000.bin"
noncomputable def ep0011000001101 : Blocks := ep0011000001101_0
private theorem idp0011000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100000110.list =
    C ((2:ℤ)^76) * horner X vp0011000001101.list + horner X ep0011000001101.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000001101 : Branch 1 (-1547761639/2000000 : ℚ) vp001100000110 := by
  apply branch_checked idp0011000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1547761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1548761639/1000000 : ℚ) by norm_num]
  exact coverp0011000001101
theorem coverp001100000110 : Covers (-1547761639/2000000 : ℚ) vp001100000110 := join_branches bp0011000001100 bp0011000001101
private noncomputable def vp00110000011_0 : Blocks := edgeBlocks% "full/vectors/00110000011-V-0000.bin"
noncomputable def vp00110000011 : Blocks := vp00110000011_0
private theorem bp001100000110 : Branch 0 (-1547761639/4000000 : ℚ) vp00110000011 := by
  apply branch_left_normalized (c:=vp001100000110) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1547761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1547761639/2000000 : ℚ) by norm_num]
  exact coverp001100000110
private noncomputable def ep001100000111_0 : Blocks := edgeBlocks% "full/vectors/001100000111-E-0000.bin"
noncomputable def ep001100000111 : Blocks := ep001100000111_0
private theorem idp001100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110000011.list =
    C ((2:ℤ)^133) * horner X vp001100000111.list + horner X ep001100000111.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100000111 : Branch 1 (-1547761639/4000000 : ℚ) vp00110000011 := by
  apply branch_checked idp001100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1547761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1549761639/2000000 : ℚ) by norm_num]
  exact coverp001100000111
theorem coverp00110000011 : Covers (-1547761639/4000000 : ℚ) vp00110000011 := join_branches bp001100000110 bp001100000111
private noncomputable def vp0011000001011_0 : Blocks := edgeBlocks% "full/vectors/0011000001011-V-0000.bin"
noncomputable def vp0011000001011 : Blocks := vp0011000001011_0
theorem coverp0011000001011 : Covers (-1546761639/1000000 : ℚ) vp0011000001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000001010_0 : Blocks := edgeBlocks% "full/vectors/0011000001010-V-0000.bin"
noncomputable def vp0011000001010 : Blocks := vp0011000001010_0
theorem coverp0011000001010 : Covers (-1545761639/1000000 : ℚ) vp0011000001010 := cover_leaf (by decide +kernel)
private noncomputable def vp001100000101_0 : Blocks := edgeBlocks% "full/vectors/001100000101-V-0000.bin"
noncomputable def vp001100000101 : Blocks := vp001100000101_0
private theorem bp0011000001010 : Branch 0 (-1545761639/2000000 : ℚ) vp001100000101 := by
  apply branch_left_normalized (c:=vp0011000001010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1545761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1545761639/1000000 : ℚ) by norm_num]
  exact coverp0011000001010
private noncomputable def ep0011000001011_0 : Blocks := edgeBlocks% "full/vectors/0011000001011-E-0000.bin"
noncomputable def ep0011000001011 : Blocks := ep0011000001011_0
private theorem idp0011000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100000101.list =
    C ((2:ℤ)^76) * horner X vp0011000001011.list + horner X ep0011000001011.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000001011 : Branch 1 (-1545761639/2000000 : ℚ) vp001100000101 := by
  apply branch_checked idp0011000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1545761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1546761639/1000000 : ℚ) by norm_num]
  exact coverp0011000001011
theorem coverp001100000101 : Covers (-1545761639/2000000 : ℚ) vp001100000101 := join_branches bp0011000001010 bp0011000001011
private noncomputable def vp0011000001001_0 : Blocks := edgeBlocks% "full/vectors/0011000001001-V-0000.bin"
noncomputable def vp0011000001001 : Blocks := vp0011000001001_0
theorem coverp0011000001001 : Covers (-1544761639/1000000 : ℚ) vp0011000001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000001000_0 : Blocks := edgeBlocks% "full/vectors/0011000001000-V-0000.bin"
noncomputable def vp0011000001000 : Blocks := vp0011000001000_0
theorem coverp0011000001000 : Covers (-1543761639/1000000 : ℚ) vp0011000001000 := cover_leaf (by decide +kernel)
private noncomputable def vp001100000100_0 : Blocks := edgeBlocks% "full/vectors/001100000100-V-0000.bin"
noncomputable def vp001100000100 : Blocks := vp001100000100_0
private theorem bp0011000001000 : Branch 0 (-1543761639/2000000 : ℚ) vp001100000100 := by
  apply branch_left_normalized (c:=vp0011000001000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1543761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1543761639/1000000 : ℚ) by norm_num]
  exact coverp0011000001000
private noncomputable def ep0011000001001_0 : Blocks := edgeBlocks% "full/vectors/0011000001001-E-0000.bin"
noncomputable def ep0011000001001 : Blocks := ep0011000001001_0
private theorem idp0011000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100000100.list =
    C ((2:ℤ)^77) * horner X vp0011000001001.list + horner X ep0011000001001.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000001001 : Branch 1 (-1543761639/2000000 : ℚ) vp001100000100 := by
  apply branch_checked idp0011000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1543761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1544761639/1000000 : ℚ) by norm_num]
  exact coverp0011000001001
theorem coverp001100000100 : Covers (-1543761639/2000000 : ℚ) vp001100000100 := join_branches bp0011000001000 bp0011000001001
private noncomputable def vp00110000010_0 : Blocks := edgeBlocks% "full/vectors/00110000010-V-0000.bin"
noncomputable def vp00110000010 : Blocks := vp00110000010_0
private theorem bp001100000100 : Branch 0 (-1543761639/4000000 : ℚ) vp00110000010 := by
  apply branch_left_normalized (c:=vp001100000100) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1543761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1543761639/2000000 : ℚ) by norm_num]
  exact coverp001100000100
private noncomputable def ep001100000101_0 : Blocks := edgeBlocks% "full/vectors/001100000101-E-0000.bin"
noncomputable def ep001100000101 : Blocks := ep001100000101_0
private theorem idp001100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110000010.list =
    C ((2:ℤ)^135) * horner X vp001100000101.list + horner X ep001100000101.list := by
  exact edge_identity (B := (2:ℤ)^277) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100000101 : Branch 1 (-1543761639/4000000 : ℚ) vp00110000010 := by
  apply branch_checked idp001100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1543761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1545761639/2000000 : ℚ) by norm_num]
  exact coverp001100000101
theorem coverp00110000010 : Covers (-1543761639/4000000 : ℚ) vp00110000010 := join_branches bp001100000100 bp001100000101
private noncomputable def vp0011000001_0 : Blocks := edgeBlocks% "full/vectors/0011000001-V-0000.bin"
private noncomputable def vp0011000001_1 : Blocks := edgeBlocks% "full/vectors/0011000001-V-0001.bin"
noncomputable def vp0011000001 : Blocks := (Blocks.join vp0011000001_0 vp0011000001_1)
private theorem bp00110000010 : Branch 0 (-1543761639/8000000 : ℚ) vp0011000001 := by
  apply branch_left_normalized (c:=vp00110000010) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-1543761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1543761639/4000000 : ℚ) by norm_num]
  exact coverp00110000010
private noncomputable def ep00110000011_0 : Blocks := edgeBlocks% "full/vectors/00110000011-E-0000.bin"
private noncomputable def ep00110000011_1 : Blocks := edgeBlocks% "full/vectors/00110000011-E-0001.bin"
noncomputable def ep00110000011 : Blocks := (Blocks.join ep00110000011_0 ep00110000011_1)
private theorem idp00110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011000001.list =
    C ((2:ℤ)^247) * horner X vp00110000011.list + horner X ep00110000011.list := by
  exact edge_identity (B := (2:ℤ)^431) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110000011 : Branch 1 (-1543761639/8000000 : ℚ) vp0011000001 := by
  apply branch_checked idp00110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1543761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1547761639/4000000 : ℚ) by norm_num]
  exact coverp00110000011
theorem coverp0011000001 : Covers (-1543761639/8000000 : ℚ) vp0011000001 := join_branches bp00110000010 bp00110000011
private noncomputable def vp0011000000111_0 : Blocks := edgeBlocks% "full/vectors/0011000000111-V-0000.bin"
noncomputable def vp0011000000111 : Blocks := vp0011000000111_0
theorem coverp0011000000111 : Covers (-1542761639/1000000 : ℚ) vp0011000000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000000110_0 : Blocks := edgeBlocks% "full/vectors/0011000000110-V-0000.bin"
noncomputable def vp0011000000110 : Blocks := vp0011000000110_0
theorem coverp0011000000110 : Covers (-1541761639/1000000 : ℚ) vp0011000000110 := cover_leaf (by decide +kernel)
private noncomputable def vp001100000011_0 : Blocks := edgeBlocks% "full/vectors/001100000011-V-0000.bin"
noncomputable def vp001100000011 : Blocks := vp001100000011_0
private theorem bp0011000000110 : Branch 0 (-1541761639/2000000 : ℚ) vp001100000011 := by
  apply branch_left_normalized (c:=vp0011000000110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1541761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1541761639/1000000 : ℚ) by norm_num]
  exact coverp0011000000110
private noncomputable def ep0011000000111_0 : Blocks := edgeBlocks% "full/vectors/0011000000111-E-0000.bin"
noncomputable def ep0011000000111 : Blocks := ep0011000000111_0
private theorem idp0011000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100000011.list =
    C ((2:ℤ)^77) * horner X vp0011000000111.list + horner X ep0011000000111.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000000111 : Branch 1 (-1541761639/2000000 : ℚ) vp001100000011 := by
  apply branch_checked idp0011000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1541761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1542761639/1000000 : ℚ) by norm_num]
  exact coverp0011000000111
theorem coverp001100000011 : Covers (-1541761639/2000000 : ℚ) vp001100000011 := join_branches bp0011000000110 bp0011000000111
private noncomputable def vp0011000000101_0 : Blocks := edgeBlocks% "full/vectors/0011000000101-V-0000.bin"
noncomputable def vp0011000000101 : Blocks := vp0011000000101_0
theorem coverp0011000000101 : Covers (-1540761639/1000000 : ℚ) vp0011000000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000000100_0 : Blocks := edgeBlocks% "full/vectors/0011000000100-V-0000.bin"
noncomputable def vp0011000000100 : Blocks := vp0011000000100_0
theorem coverp0011000000100 : Covers (-1539761639/1000000 : ℚ) vp0011000000100 := cover_leaf (by decide +kernel)
private noncomputable def vp001100000010_0 : Blocks := edgeBlocks% "full/vectors/001100000010-V-0000.bin"
noncomputable def vp001100000010 : Blocks := vp001100000010_0
private theorem bp0011000000100 : Branch 0 (-1539761639/2000000 : ℚ) vp001100000010 := by
  apply branch_left_normalized (c:=vp0011000000100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1539761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1539761639/1000000 : ℚ) by norm_num]
  exact coverp0011000000100
private noncomputable def ep0011000000101_0 : Blocks := edgeBlocks% "full/vectors/0011000000101-E-0000.bin"
noncomputable def ep0011000000101 : Blocks := ep0011000000101_0
private theorem idp0011000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100000010.list =
    C ((2:ℤ)^77) * horner X vp0011000000101.list + horner X ep0011000000101.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000000101 : Branch 1 (-1539761639/2000000 : ℚ) vp001100000010 := by
  apply branch_checked idp0011000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1539761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1540761639/1000000 : ℚ) by norm_num]
  exact coverp0011000000101
theorem coverp001100000010 : Covers (-1539761639/2000000 : ℚ) vp001100000010 := join_branches bp0011000000100 bp0011000000101
private noncomputable def vp00110000001_0 : Blocks := edgeBlocks% "full/vectors/00110000001-V-0000.bin"
noncomputable def vp00110000001 : Blocks := vp00110000001_0
private theorem bp001100000010 : Branch 0 (-1539761639/4000000 : ℚ) vp00110000001 := by
  apply branch_left_normalized (c:=vp001100000010) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1539761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1539761639/2000000 : ℚ) by norm_num]
  exact coverp001100000010
private noncomputable def ep001100000011_0 : Blocks := edgeBlocks% "full/vectors/001100000011-E-0000.bin"
noncomputable def ep001100000011 : Blocks := ep001100000011_0
private theorem idp001100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110000001.list =
    C ((2:ℤ)^133) * horner X vp001100000011.list + horner X ep001100000011.list := by
  exact edge_identity (B := (2:ℤ)^276) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100000011 : Branch 1 (-1539761639/4000000 : ℚ) vp00110000001 := by
  apply branch_checked idp001100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1539761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1541761639/2000000 : ℚ) by norm_num]
  exact coverp001100000011
theorem coverp00110000001 : Covers (-1539761639/4000000 : ℚ) vp00110000001 := join_branches bp001100000010 bp001100000011
private noncomputable def vp0011000000011_0 : Blocks := edgeBlocks% "full/vectors/0011000000011-V-0000.bin"
noncomputable def vp0011000000011 : Blocks := vp0011000000011_0
theorem coverp0011000000011 : Covers (-1538761639/1000000 : ℚ) vp0011000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000000010_0 : Blocks := edgeBlocks% "full/vectors/0011000000010-V-0000.bin"
noncomputable def vp0011000000010 : Blocks := vp0011000000010_0
theorem coverp0011000000010 : Covers (-1537761639/1000000 : ℚ) vp0011000000010 := cover_leaf (by decide +kernel)
private noncomputable def vp001100000001_0 : Blocks := edgeBlocks% "full/vectors/001100000001-V-0000.bin"
noncomputable def vp001100000001 : Blocks := vp001100000001_0
private theorem bp0011000000010 : Branch 0 (-1537761639/2000000 : ℚ) vp001100000001 := by
  apply branch_left_normalized (c:=vp0011000000010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1537761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1537761639/1000000 : ℚ) by norm_num]
  exact coverp0011000000010
private noncomputable def ep0011000000011_0 : Blocks := edgeBlocks% "full/vectors/0011000000011-E-0000.bin"
noncomputable def ep0011000000011 : Blocks := ep0011000000011_0
private theorem idp0011000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100000001.list =
    C ((2:ℤ)^77) * horner X vp0011000000011.list + horner X ep0011000000011.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000000011 : Branch 1 (-1537761639/2000000 : ℚ) vp001100000001 := by
  apply branch_checked idp0011000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1537761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1538761639/1000000 : ℚ) by norm_num]
  exact coverp0011000000011
theorem coverp001100000001 : Covers (-1537761639/2000000 : ℚ) vp001100000001 := join_branches bp0011000000010 bp0011000000011
private noncomputable def vp0011000000001_0 : Blocks := edgeBlocks% "full/vectors/0011000000001-V-0000.bin"
noncomputable def vp0011000000001 : Blocks := vp0011000000001_0
theorem coverp0011000000001 : Covers (-1536761639/1000000 : ℚ) vp0011000000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011000000000_0 : Blocks := edgeBlocks% "full/vectors/0011000000000-V-0000.bin"
noncomputable def vp0011000000000 : Blocks := vp0011000000000_0
theorem coverp0011000000000 : Covers (-1535761639/1000000 : ℚ) vp0011000000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001100000000_0 : Blocks := edgeBlocks% "full/vectors/001100000000-V-0000.bin"
noncomputable def vp001100000000 : Blocks := vp001100000000_0
private theorem bp0011000000000 : Branch 0 (-1535761639/2000000 : ℚ) vp001100000000 := by
  apply branch_left_normalized (c:=vp0011000000000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1535761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1535761639/1000000 : ℚ) by norm_num]
  exact coverp0011000000000
private noncomputable def ep0011000000001_0 : Blocks := edgeBlocks% "full/vectors/0011000000001-E-0000.bin"
noncomputable def ep0011000000001 : Blocks := ep0011000000001_0
private theorem idp0011000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100000000.list =
    C ((2:ℤ)^77) * horner X vp0011000000001.list + horner X ep0011000000001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000000001 : Branch 1 (-1535761639/2000000 : ℚ) vp001100000000 := by
  apply branch_checked idp0011000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1535761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1536761639/1000000 : ℚ) by norm_num]
  exact coverp0011000000001
theorem coverp001100000000 : Covers (-1535761639/2000000 : ℚ) vp001100000000 := join_branches bp0011000000000 bp0011000000001
private noncomputable def vp00110000000_0 : Blocks := edgeBlocks% "full/vectors/00110000000-V-0000.bin"
noncomputable def vp00110000000 : Blocks := vp00110000000_0
private theorem bp001100000000 : Branch 0 (-1535761639/4000000 : ℚ) vp00110000000 := by
  apply branch_left_normalized (c:=vp001100000000) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1535761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1535761639/2000000 : ℚ) by norm_num]
  exact coverp001100000000
private noncomputable def ep001100000001_0 : Blocks := edgeBlocks% "full/vectors/001100000001-E-0000.bin"
noncomputable def ep001100000001 : Blocks := ep001100000001_0
private theorem idp001100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110000000.list =
    C ((2:ℤ)^133) * horner X vp001100000001.list + horner X ep001100000001.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100000001 : Branch 1 (-1535761639/4000000 : ℚ) vp00110000000 := by
  apply branch_checked idp001100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1535761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1537761639/2000000 : ℚ) by norm_num]
  exact coverp001100000001
theorem coverp00110000000 : Covers (-1535761639/4000000 : ℚ) vp00110000000 := join_branches bp001100000000 bp001100000001
private noncomputable def vp0011000000_0 : Blocks := edgeBlocks% "full/vectors/0011000000-V-0000.bin"
private noncomputable def vp0011000000_1 : Blocks := edgeBlocks% "full/vectors/0011000000-V-0001.bin"
noncomputable def vp0011000000 : Blocks := (Blocks.join vp0011000000_0 vp0011000000_1)
private theorem bp00110000000 : Branch 0 (-1535761639/8000000 : ℚ) vp0011000000 := by
  apply branch_left_normalized (c:=vp00110000000) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-1535761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1535761639/4000000 : ℚ) by norm_num]
  exact coverp00110000000
private noncomputable def ep00110000001_0 : Blocks := edgeBlocks% "full/vectors/00110000001-E-0000.bin"
private noncomputable def ep00110000001_1 : Blocks := edgeBlocks% "full/vectors/00110000001-E-0001.bin"
noncomputable def ep00110000001 : Blocks := (Blocks.join ep00110000001_0 ep00110000001_1)
private theorem idp00110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011000000.list =
    C ((2:ℤ)^244) * horner X vp00110000001.list + horner X ep00110000001.list := by
  exact edge_identity (B := (2:ℤ)^429) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110000001 : Branch 1 (-1535761639/8000000 : ℚ) vp0011000000 := by
  apply branch_checked idp00110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1535761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1539761639/4000000 : ℚ) by norm_num]
  exact coverp00110000001
theorem coverp0011000000 : Covers (-1535761639/8000000 : ℚ) vp0011000000 := join_branches bp00110000000 bp00110000001
private noncomputable def vp001100000_0 : Blocks := edgeBlocks% "full/vectors/001100000-V-0000.bin"
private noncomputable def vp001100000_1 : Blocks := edgeBlocks% "full/vectors/001100000-V-0001.bin"
private noncomputable def vp001100000_2 : Blocks := edgeBlocks% "full/vectors/001100000-V-0002.bin"
private noncomputable def vp001100000_3 : Blocks := edgeBlocks% "full/vectors/001100000-V-0003.bin"
noncomputable def vp001100000 : Blocks := (Blocks.join (Blocks.join vp001100000_0 vp001100000_1) (Blocks.join vp001100000_2 vp001100000_3))
private theorem bp0011000000 : Branch 0 (-1535761639/16000000 : ℚ) vp001100000 := by
  apply branch_left_normalized (c:=vp0011000000) (k:=0) (m:=221) (by decide +kernel)
  rw [show 2*(-1535761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1535761639/8000000 : ℚ) by norm_num]
  exact coverp0011000000
private noncomputable def ep0011000001_0 : Blocks := edgeBlocks% "full/vectors/0011000001-E-0000.bin"
private noncomputable def ep0011000001_1 : Blocks := edgeBlocks% "full/vectors/0011000001-E-0001.bin"
private noncomputable def ep0011000001_2 : Blocks := edgeBlocks% "full/vectors/0011000001-E-0002.bin"
private noncomputable def ep0011000001_3 : Blocks := edgeBlocks% "full/vectors/0011000001-E-0003.bin"
noncomputable def ep0011000001 : Blocks := (Blocks.join (Blocks.join ep0011000001_0 ep0011000001_1) (Blocks.join ep0011000001_2 ep0011000001_3))
private theorem idp0011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100000.list =
    C ((2:ℤ)^467) * horner X vp0011000001.list + horner X ep0011000001.list := by
  exact edge_identity (B := (2:ℤ)^735) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011000001 : Branch 1 (-1535761639/16000000 : ℚ) vp001100000 := by
  apply branch_checked idp0011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1535761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1543761639/8000000 : ℚ) by norm_num]
  exact coverp0011000001
theorem coverp001100000 : Covers (-1535761639/16000000 : ℚ) vp001100000 := join_branches bp0011000000 bp0011000001
private noncomputable def vp00110000_0 : Blocks := edgeBlocks% "full/vectors/00110000-V-0000.bin"
private noncomputable def vp00110000_1 : Blocks := edgeBlocks% "full/vectors/00110000-V-0001.bin"
private noncomputable def vp00110000_2 : Blocks := edgeBlocks% "full/vectors/00110000-V-0002.bin"
private noncomputable def vp00110000_3 : Blocks := edgeBlocks% "full/vectors/00110000-V-0003.bin"
private noncomputable def vp00110000_4 : Blocks := edgeBlocks% "full/vectors/00110000-V-0004.bin"
private noncomputable def vp00110000_5 : Blocks := edgeBlocks% "full/vectors/00110000-V-0005.bin"
private noncomputable def vp00110000_6 : Blocks := edgeBlocks% "full/vectors/00110000-V-0006.bin"
noncomputable def vp00110000 : Blocks := (Blocks.join (Blocks.join vp00110000_0 (Blocks.join vp00110000_1 vp00110000_2)) (Blocks.join (Blocks.join vp00110000_3 vp00110000_4) (Blocks.join vp00110000_5 vp00110000_6)))
private theorem bp001100000 : Branch 0 (-1535761639/32000000 : ℚ) vp00110000 := by
  apply branch_left_normalized (c:=vp001100000) (k:=0) (m:=421) (by decide +kernel)
  rw [show 2*(-1535761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1535761639/16000000 : ℚ) by norm_num]
  exact coverp001100000
private noncomputable def ep001100001_0 : Blocks := edgeBlocks% "full/vectors/001100001-E-0000.bin"
private noncomputable def ep001100001_1 : Blocks := edgeBlocks% "full/vectors/001100001-E-0001.bin"
private noncomputable def ep001100001_2 : Blocks := edgeBlocks% "full/vectors/001100001-E-0002.bin"
private noncomputable def ep001100001_3 : Blocks := edgeBlocks% "full/vectors/001100001-E-0003.bin"
private noncomputable def ep001100001_4 : Blocks := edgeBlocks% "full/vectors/001100001-E-0004.bin"
private noncomputable def ep001100001_5 : Blocks := edgeBlocks% "full/vectors/001100001-E-0005.bin"
private noncomputable def ep001100001_6 : Blocks := edgeBlocks% "full/vectors/001100001-E-0006.bin"
noncomputable def ep001100001 : Blocks := (Blocks.join (Blocks.join ep001100001_0 (Blocks.join ep001100001_1 ep001100001_2)) (Blocks.join (Blocks.join ep001100001_3 ep001100001_4) (Blocks.join ep001100001_5 ep001100001_6)))
private theorem idp001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110000.list =
    C ((2:ℤ)^907) * horner X vp001100001.list + horner X ep001100001.list := by
  exact edge_identity (B := (2:ℤ)^1341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100001 : Branch 1 (-1535761639/32000000 : ℚ) vp00110000 := by
  apply branch_checked idp001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1535761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1551761639/16000000 : ℚ) by norm_num]
  exact coverp001100001
theorem coverp00110000 : Covers (-1535761639/32000000 : ℚ) vp00110000 := join_branches bp001100000 bp001100001
private noncomputable def vp0011000_0 : Blocks := edgeBlocks% "full/vectors/0011000-V-0000.bin"
private noncomputable def vp0011000_1 : Blocks := edgeBlocks% "full/vectors/0011000-V-0001.bin"
private noncomputable def vp0011000_2 : Blocks := edgeBlocks% "full/vectors/0011000-V-0002.bin"
private noncomputable def vp0011000_3 : Blocks := edgeBlocks% "full/vectors/0011000-V-0003.bin"
private noncomputable def vp0011000_4 : Blocks := edgeBlocks% "full/vectors/0011000-V-0004.bin"
private noncomputable def vp0011000_5 : Blocks := edgeBlocks% "full/vectors/0011000-V-0005.bin"
private noncomputable def vp0011000_6 : Blocks := edgeBlocks% "full/vectors/0011000-V-0006.bin"
private noncomputable def vp0011000_7 : Blocks := edgeBlocks% "full/vectors/0011000-V-0007.bin"
private noncomputable def vp0011000_8 : Blocks := edgeBlocks% "full/vectors/0011000-V-0008.bin"
private noncomputable def vp0011000_9 : Blocks := edgeBlocks% "full/vectors/0011000-V-0009.bin"
private noncomputable def vp0011000_10 : Blocks := edgeBlocks% "full/vectors/0011000-V-0010.bin"
private noncomputable def vp0011000_11 : Blocks := edgeBlocks% "full/vectors/0011000-V-0011.bin"
private noncomputable def vp0011000_12 : Blocks := edgeBlocks% "full/vectors/0011000-V-0012.bin"
noncomputable def vp0011000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0011000_0 (Blocks.join vp0011000_1 vp0011000_2)) (Blocks.join vp0011000_3 (Blocks.join vp0011000_4 vp0011000_5))) (Blocks.join (Blocks.join vp0011000_6 (Blocks.join vp0011000_7 vp0011000_8)) (Blocks.join (Blocks.join vp0011000_9 vp0011000_10) (Blocks.join vp0011000_11 vp0011000_12))))
private theorem bp00110000 : Branch 0 (-1535761639/64000000 : ℚ) vp0011000 := by
  apply branch_left_normalized (c:=vp00110000) (k:=0) (m:=815) (by decide +kernel)
  rw [show 2*(-1535761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1535761639/32000000 : ℚ) by norm_num]
  exact coverp00110000
private noncomputable def ep00110001_0 : Blocks := edgeBlocks% "full/vectors/00110001-E-0000.bin"
private noncomputable def ep00110001_1 : Blocks := edgeBlocks% "full/vectors/00110001-E-0001.bin"
private noncomputable def ep00110001_2 : Blocks := edgeBlocks% "full/vectors/00110001-E-0002.bin"
private noncomputable def ep00110001_3 : Blocks := edgeBlocks% "full/vectors/00110001-E-0003.bin"
private noncomputable def ep00110001_4 : Blocks := edgeBlocks% "full/vectors/00110001-E-0004.bin"
private noncomputable def ep00110001_5 : Blocks := edgeBlocks% "full/vectors/00110001-E-0005.bin"
private noncomputable def ep00110001_6 : Blocks := edgeBlocks% "full/vectors/00110001-E-0006.bin"
private noncomputable def ep00110001_7 : Blocks := edgeBlocks% "full/vectors/00110001-E-0007.bin"
private noncomputable def ep00110001_8 : Blocks := edgeBlocks% "full/vectors/00110001-E-0008.bin"
private noncomputable def ep00110001_9 : Blocks := edgeBlocks% "full/vectors/00110001-E-0009.bin"
private noncomputable def ep00110001_10 : Blocks := edgeBlocks% "full/vectors/00110001-E-0010.bin"
private noncomputable def ep00110001_11 : Blocks := edgeBlocks% "full/vectors/00110001-E-0011.bin"
private noncomputable def ep00110001_12 : Blocks := edgeBlocks% "full/vectors/00110001-E-0012.bin"
noncomputable def ep00110001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00110001_0 (Blocks.join ep00110001_1 ep00110001_2)) (Blocks.join ep00110001_3 (Blocks.join ep00110001_4 ep00110001_5))) (Blocks.join (Blocks.join ep00110001_6 (Blocks.join ep00110001_7 ep00110001_8)) (Blocks.join (Blocks.join ep00110001_9 ep00110001_10) (Blocks.join ep00110001_11 ep00110001_12))))
private theorem idp00110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011000.list =
    C ((2:ℤ)^1774) * horner X vp00110001.list + horner X ep00110001.list := by
  exact edge_identity (B := (2:ℤ)^2535) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110001 : Branch 1 (-1535761639/64000000 : ℚ) vp0011000 := by
  apply branch_checked idp00110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1535761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1567761639/32000000 : ℚ) by norm_num]
  exact coverp00110001
theorem coverp0011000 : Covers (-1535761639/64000000 : ℚ) vp0011000 := join_branches bp00110000 bp00110001
private noncomputable def vp001100_0 : Blocks := edgeBlocks% "full/vectors/001100-V-0000.bin"
private noncomputable def vp001100_1 : Blocks := edgeBlocks% "full/vectors/001100-V-0001.bin"
private noncomputable def vp001100_2 : Blocks := edgeBlocks% "full/vectors/001100-V-0002.bin"
private noncomputable def vp001100_3 : Blocks := edgeBlocks% "full/vectors/001100-V-0003.bin"
private noncomputable def vp001100_4 : Blocks := edgeBlocks% "full/vectors/001100-V-0004.bin"
private noncomputable def vp001100_5 : Blocks := edgeBlocks% "full/vectors/001100-V-0005.bin"
private noncomputable def vp001100_6 : Blocks := edgeBlocks% "full/vectors/001100-V-0006.bin"
private noncomputable def vp001100_7 : Blocks := edgeBlocks% "full/vectors/001100-V-0007.bin"
private noncomputable def vp001100_8 : Blocks := edgeBlocks% "full/vectors/001100-V-0008.bin"
private noncomputable def vp001100_9 : Blocks := edgeBlocks% "full/vectors/001100-V-0009.bin"
private noncomputable def vp001100_10 : Blocks := edgeBlocks% "full/vectors/001100-V-0010.bin"
private noncomputable def vp001100_11 : Blocks := edgeBlocks% "full/vectors/001100-V-0011.bin"
private noncomputable def vp001100_12 : Blocks := edgeBlocks% "full/vectors/001100-V-0012.bin"
private noncomputable def vp001100_13 : Blocks := edgeBlocks% "full/vectors/001100-V-0013.bin"
private noncomputable def vp001100_14 : Blocks := edgeBlocks% "full/vectors/001100-V-0014.bin"
private noncomputable def vp001100_15 : Blocks := edgeBlocks% "full/vectors/001100-V-0015.bin"
private noncomputable def vp001100_16 : Blocks := edgeBlocks% "full/vectors/001100-V-0016.bin"
private noncomputable def vp001100_17 : Blocks := edgeBlocks% "full/vectors/001100-V-0017.bin"
private noncomputable def vp001100_18 : Blocks := edgeBlocks% "full/vectors/001100-V-0018.bin"
private noncomputable def vp001100_19 : Blocks := edgeBlocks% "full/vectors/001100-V-0019.bin"
private noncomputable def vp001100_20 : Blocks := edgeBlocks% "full/vectors/001100-V-0020.bin"
private noncomputable def vp001100_21 : Blocks := edgeBlocks% "full/vectors/001100-V-0021.bin"
private noncomputable def vp001100_22 : Blocks := edgeBlocks% "full/vectors/001100-V-0022.bin"
private noncomputable def vp001100_23 : Blocks := edgeBlocks% "full/vectors/001100-V-0023.bin"
private noncomputable def vp001100_24 : Blocks := edgeBlocks% "full/vectors/001100-V-0024.bin"
noncomputable def vp001100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp001100_0 (Blocks.join vp001100_1 vp001100_2)) (Blocks.join vp001100_3 (Blocks.join vp001100_4 vp001100_5))) (Blocks.join (Blocks.join vp001100_6 (Blocks.join vp001100_7 vp001100_8)) (Blocks.join vp001100_9 (Blocks.join vp001100_10 vp001100_11)))) (Blocks.join (Blocks.join (Blocks.join vp001100_12 (Blocks.join vp001100_13 vp001100_14)) (Blocks.join vp001100_15 (Blocks.join vp001100_16 vp001100_17))) (Blocks.join (Blocks.join vp001100_18 (Blocks.join vp001100_19 vp001100_20)) (Blocks.join (Blocks.join vp001100_21 vp001100_22) (Blocks.join vp001100_23 vp001100_24)))))
private theorem bp0011000 : Branch 0 (-1535761639/128000000 : ℚ) vp001100 := by
  apply branch_left_normalized (c:=vp0011000) (k:=0) (m:=1589) (by decide +kernel)
  rw [show 2*(-1535761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-1535761639/64000000 : ℚ) by norm_num]
  exact coverp0011000
private noncomputable def ep0011001_0 : Blocks := edgeBlocks% "full/vectors/0011001-E-0000.bin"
private noncomputable def ep0011001_1 : Blocks := edgeBlocks% "full/vectors/0011001-E-0001.bin"
private noncomputable def ep0011001_2 : Blocks := edgeBlocks% "full/vectors/0011001-E-0002.bin"
private noncomputable def ep0011001_3 : Blocks := edgeBlocks% "full/vectors/0011001-E-0003.bin"
private noncomputable def ep0011001_4 : Blocks := edgeBlocks% "full/vectors/0011001-E-0004.bin"
private noncomputable def ep0011001_5 : Blocks := edgeBlocks% "full/vectors/0011001-E-0005.bin"
private noncomputable def ep0011001_6 : Blocks := edgeBlocks% "full/vectors/0011001-E-0006.bin"
private noncomputable def ep0011001_7 : Blocks := edgeBlocks% "full/vectors/0011001-E-0007.bin"
private noncomputable def ep0011001_8 : Blocks := edgeBlocks% "full/vectors/0011001-E-0008.bin"
private noncomputable def ep0011001_9 : Blocks := edgeBlocks% "full/vectors/0011001-E-0009.bin"
private noncomputable def ep0011001_10 : Blocks := edgeBlocks% "full/vectors/0011001-E-0010.bin"
private noncomputable def ep0011001_11 : Blocks := edgeBlocks% "full/vectors/0011001-E-0011.bin"
private noncomputable def ep0011001_12 : Blocks := edgeBlocks% "full/vectors/0011001-E-0012.bin"
private noncomputable def ep0011001_13 : Blocks := edgeBlocks% "full/vectors/0011001-E-0013.bin"
private noncomputable def ep0011001_14 : Blocks := edgeBlocks% "full/vectors/0011001-E-0014.bin"
private noncomputable def ep0011001_15 : Blocks := edgeBlocks% "full/vectors/0011001-E-0015.bin"
private noncomputable def ep0011001_16 : Blocks := edgeBlocks% "full/vectors/0011001-E-0016.bin"
private noncomputable def ep0011001_17 : Blocks := edgeBlocks% "full/vectors/0011001-E-0017.bin"
private noncomputable def ep0011001_18 : Blocks := edgeBlocks% "full/vectors/0011001-E-0018.bin"
private noncomputable def ep0011001_19 : Blocks := edgeBlocks% "full/vectors/0011001-E-0019.bin"
private noncomputable def ep0011001_20 : Blocks := edgeBlocks% "full/vectors/0011001-E-0020.bin"
private noncomputable def ep0011001_21 : Blocks := edgeBlocks% "full/vectors/0011001-E-0021.bin"
private noncomputable def ep0011001_22 : Blocks := edgeBlocks% "full/vectors/0011001-E-0022.bin"
private noncomputable def ep0011001_23 : Blocks := edgeBlocks% "full/vectors/0011001-E-0023.bin"
private noncomputable def ep0011001_24 : Blocks := edgeBlocks% "full/vectors/0011001-E-0024.bin"
noncomputable def ep0011001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0011001_0 (Blocks.join ep0011001_1 ep0011001_2)) (Blocks.join ep0011001_3 (Blocks.join ep0011001_4 ep0011001_5))) (Blocks.join (Blocks.join ep0011001_6 (Blocks.join ep0011001_7 ep0011001_8)) (Blocks.join ep0011001_9 (Blocks.join ep0011001_10 ep0011001_11)))) (Blocks.join (Blocks.join (Blocks.join ep0011001_12 (Blocks.join ep0011001_13 ep0011001_14)) (Blocks.join ep0011001_15 (Blocks.join ep0011001_16 ep0011001_17))) (Blocks.join (Blocks.join ep0011001_18 (Blocks.join ep0011001_19 ep0011001_20)) (Blocks.join (Blocks.join ep0011001_21 ep0011001_22) (Blocks.join ep0011001_23 ep0011001_24)))))
private def ptsp0011001 : List ℤ := [((2:ℤ)^3897+0),((2:ℤ)^3897+1)]
private theorem boundp0011001 : 2^vp001100.size*absSum vp001100.list + ((2:ℤ)^3451*absSum vp0011001.list+absSum ep0011001.list) < (2:ℤ)^4855 := by decide +kernel
private theorem pointp0011001_0 : fastHom 1 ((2:ℤ)^3897+0) vp001100 = ((2:ℤ)^3451)*vp0011001.subst ((2:ℤ)^3897+0)+ep0011001.subst ((2:ℤ)^3897+0) := by decide +kernel
private theorem pointp0011001_1 : fastHom 1 ((2:ℤ)^3897+1) vp001100 = ((2:ℤ)^3451)*vp0011001.subst ((2:ℤ)^3897+1)+ep0011001.subst ((2:ℤ)^3897+1) := by decide +kernel
private theorem checkp0011001 (x:ℤ) (hx:x ∈ ptsp0011001) : fastHom 1 x vp001100 = ((2:ℤ)^3451)*vp0011001.subst x+ep0011001.subst x := by
  simp only [ptsp0011001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp0011001_0
  · exact pointp0011001_1
private theorem idp0011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100.list =
    C ((2:ℤ)^3451) * horner X vp0011001.list + horner X ep0011001.list := by
  apply edge_identity (B := (2:ℤ)^4855) (by decide) (by positivity) (by positivity) boundp0011001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0011001 (by decide +kernel)
  · have h : ptsp0011001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0011001.trans_le (by decide +kernel)
  · exact checkp0011001
private theorem bp0011001 : Branch 1 (-1535761639/128000000 : ℚ) vp001100 := by
  apply branch_checked idp0011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1535761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-1599761639/64000000 : ℚ) by norm_num]
  exact coverp0011001
theorem coverp001100 : Covers (-1535761639/128000000 : ℚ) vp001100 := join_branches bp0011000 bp0011001
end NextProof.EdgeFull

