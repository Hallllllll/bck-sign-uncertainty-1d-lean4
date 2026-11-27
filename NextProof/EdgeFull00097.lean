import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0011001111111_0 : Blocks := edgeBlocks% "full/vectors/0011001111111-V-0000.bin"
noncomputable def vp0011001111111 : Blocks := vp0011001111111_0
theorem coverp0011001111111 : Covers (-1662761639/1000000 : ℚ) vp0011001111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011001111110_0 : Blocks := edgeBlocks% "full/vectors/0011001111110-V-0000.bin"
noncomputable def vp0011001111110 : Blocks := vp0011001111110_0
theorem coverp0011001111110 : Covers (-1661761639/1000000 : ℚ) vp0011001111110 := cover_leaf (by decide +kernel)
private noncomputable def vp001100111111_0 : Blocks := edgeBlocks% "full/vectors/001100111111-V-0000.bin"
noncomputable def vp001100111111 : Blocks := vp001100111111_0
private theorem bp0011001111110 : Branch 0 (-1661761639/2000000 : ℚ) vp001100111111 := by
  apply branch_left_normalized (c:=vp0011001111110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1661761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1661761639/1000000 : ℚ) by norm_num]
  exact coverp0011001111110
private noncomputable def ep0011001111111_0 : Blocks := edgeBlocks% "full/vectors/0011001111111-E-0000.bin"
noncomputable def ep0011001111111 : Blocks := ep0011001111111_0
private theorem idp0011001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100111111.list =
    C ((2:ℤ)^75) * horner X vp0011001111111.list + horner X ep0011001111111.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001111111 : Branch 1 (-1661761639/2000000 : ℚ) vp001100111111 := by
  apply branch_checked idp0011001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1661761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1662761639/1000000 : ℚ) by norm_num]
  exact coverp0011001111111
theorem coverp001100111111 : Covers (-1661761639/2000000 : ℚ) vp001100111111 := join_branches bp0011001111110 bp0011001111111
private noncomputable def vp0011001111101_0 : Blocks := edgeBlocks% "full/vectors/0011001111101-V-0000.bin"
noncomputable def vp0011001111101 : Blocks := vp0011001111101_0
theorem coverp0011001111101 : Covers (-1660761639/1000000 : ℚ) vp0011001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011001111100_0 : Blocks := edgeBlocks% "full/vectors/0011001111100-V-0000.bin"
noncomputable def vp0011001111100 : Blocks := vp0011001111100_0
theorem coverp0011001111100 : Covers (-1659761639/1000000 : ℚ) vp0011001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001100111110_0 : Blocks := edgeBlocks% "full/vectors/001100111110-V-0000.bin"
noncomputable def vp001100111110 : Blocks := vp001100111110_0
private theorem bp0011001111100 : Branch 0 (-1659761639/2000000 : ℚ) vp001100111110 := by
  apply branch_left_normalized (c:=vp0011001111100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1659761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1659761639/1000000 : ℚ) by norm_num]
  exact coverp0011001111100
private noncomputable def ep0011001111101_0 : Blocks := edgeBlocks% "full/vectors/0011001111101-E-0000.bin"
noncomputable def ep0011001111101 : Blocks := ep0011001111101_0
private theorem idp0011001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100111110.list =
    C ((2:ℤ)^74) * horner X vp0011001111101.list + horner X ep0011001111101.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001111101 : Branch 1 (-1659761639/2000000 : ℚ) vp001100111110 := by
  apply branch_checked idp0011001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1659761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1660761639/1000000 : ℚ) by norm_num]
  exact coverp0011001111101
theorem coverp001100111110 : Covers (-1659761639/2000000 : ℚ) vp001100111110 := join_branches bp0011001111100 bp0011001111101
private noncomputable def vp00110011111_0 : Blocks := edgeBlocks% "full/vectors/00110011111-V-0000.bin"
noncomputable def vp00110011111 : Blocks := vp00110011111_0
private theorem bp001100111110 : Branch 0 (-1659761639/4000000 : ℚ) vp00110011111 := by
  apply branch_left_normalized (c:=vp001100111110) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1659761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1659761639/2000000 : ℚ) by norm_num]
  exact coverp001100111110
private noncomputable def ep001100111111_0 : Blocks := edgeBlocks% "full/vectors/001100111111-E-0000.bin"
noncomputable def ep001100111111 : Blocks := ep001100111111_0
private theorem idp001100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110011111.list =
    C ((2:ℤ)^130) * horner X vp001100111111.list + horner X ep001100111111.list := by
  exact edge_identity (B := (2:ℤ)^271) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100111111 : Branch 1 (-1659761639/4000000 : ℚ) vp00110011111 := by
  apply branch_checked idp001100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1659761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1661761639/2000000 : ℚ) by norm_num]
  exact coverp001100111111
theorem coverp00110011111 : Covers (-1659761639/4000000 : ℚ) vp00110011111 := join_branches bp001100111110 bp001100111111
private noncomputable def vp0011001111011_0 : Blocks := edgeBlocks% "full/vectors/0011001111011-V-0000.bin"
noncomputable def vp0011001111011 : Blocks := vp0011001111011_0
theorem coverp0011001111011 : Covers (-1658761639/1000000 : ℚ) vp0011001111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011001111010_0 : Blocks := edgeBlocks% "full/vectors/0011001111010-V-0000.bin"
noncomputable def vp0011001111010 : Blocks := vp0011001111010_0
theorem coverp0011001111010 : Covers (-1657761639/1000000 : ℚ) vp0011001111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001100111101_0 : Blocks := edgeBlocks% "full/vectors/001100111101-V-0000.bin"
noncomputable def vp001100111101 : Blocks := vp001100111101_0
private theorem bp0011001111010 : Branch 0 (-1657761639/2000000 : ℚ) vp001100111101 := by
  apply branch_left_normalized (c:=vp0011001111010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1657761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1657761639/1000000 : ℚ) by norm_num]
  exact coverp0011001111010
private noncomputable def ep0011001111011_0 : Blocks := edgeBlocks% "full/vectors/0011001111011-E-0000.bin"
noncomputable def ep0011001111011 : Blocks := ep0011001111011_0
private theorem idp0011001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100111101.list =
    C ((2:ℤ)^74) * horner X vp0011001111011.list + horner X ep0011001111011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001111011 : Branch 1 (-1657761639/2000000 : ℚ) vp001100111101 := by
  apply branch_checked idp0011001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1657761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1658761639/1000000 : ℚ) by norm_num]
  exact coverp0011001111011
theorem coverp001100111101 : Covers (-1657761639/2000000 : ℚ) vp001100111101 := join_branches bp0011001111010 bp0011001111011
private noncomputable def vp0011001111001_0 : Blocks := edgeBlocks% "full/vectors/0011001111001-V-0000.bin"
noncomputable def vp0011001111001 : Blocks := vp0011001111001_0
theorem coverp0011001111001 : Covers (-1656761639/1000000 : ℚ) vp0011001111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011001111000_0 : Blocks := edgeBlocks% "full/vectors/0011001111000-V-0000.bin"
noncomputable def vp0011001111000 : Blocks := vp0011001111000_0
theorem coverp0011001111000 : Covers (-1655761639/1000000 : ℚ) vp0011001111000 := cover_leaf (by decide +kernel)
private noncomputable def vp001100111100_0 : Blocks := edgeBlocks% "full/vectors/001100111100-V-0000.bin"
noncomputable def vp001100111100 : Blocks := vp001100111100_0
private theorem bp0011001111000 : Branch 0 (-1655761639/2000000 : ℚ) vp001100111100 := by
  apply branch_left_normalized (c:=vp0011001111000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1655761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1655761639/1000000 : ℚ) by norm_num]
  exact coverp0011001111000
private noncomputable def ep0011001111001_0 : Blocks := edgeBlocks% "full/vectors/0011001111001-E-0000.bin"
noncomputable def ep0011001111001 : Blocks := ep0011001111001_0
private theorem idp0011001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100111100.list =
    C ((2:ℤ)^74) * horner X vp0011001111001.list + horner X ep0011001111001.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001111001 : Branch 1 (-1655761639/2000000 : ℚ) vp001100111100 := by
  apply branch_checked idp0011001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1655761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1656761639/1000000 : ℚ) by norm_num]
  exact coverp0011001111001
theorem coverp001100111100 : Covers (-1655761639/2000000 : ℚ) vp001100111100 := join_branches bp0011001111000 bp0011001111001
private noncomputable def vp00110011110_0 : Blocks := edgeBlocks% "full/vectors/00110011110-V-0000.bin"
noncomputable def vp00110011110 : Blocks := vp00110011110_0
private theorem bp001100111100 : Branch 0 (-1655761639/4000000 : ℚ) vp00110011110 := by
  apply branch_left_normalized (c:=vp001100111100) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1655761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1655761639/2000000 : ℚ) by norm_num]
  exact coverp001100111100
private noncomputable def ep001100111101_0 : Blocks := edgeBlocks% "full/vectors/001100111101-E-0000.bin"
noncomputable def ep001100111101 : Blocks := ep001100111101_0
private theorem idp001100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110011110.list =
    C ((2:ℤ)^129) * horner X vp001100111101.list + horner X ep001100111101.list := by
  exact edge_identity (B := (2:ℤ)^269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100111101 : Branch 1 (-1655761639/4000000 : ℚ) vp00110011110 := by
  apply branch_checked idp001100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1655761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1657761639/2000000 : ℚ) by norm_num]
  exact coverp001100111101
theorem coverp00110011110 : Covers (-1655761639/4000000 : ℚ) vp00110011110 := join_branches bp001100111100 bp001100111101
private noncomputable def vp0011001111_0 : Blocks := edgeBlocks% "full/vectors/0011001111-V-0000.bin"
private noncomputable def vp0011001111_1 : Blocks := edgeBlocks% "full/vectors/0011001111-V-0001.bin"
noncomputable def vp0011001111 : Blocks := (Blocks.join vp0011001111_0 vp0011001111_1)
private theorem bp00110011110 : Branch 0 (-1655761639/8000000 : ℚ) vp0011001111 := by
  apply branch_left_normalized (c:=vp00110011110) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-1655761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1655761639/4000000 : ℚ) by norm_num]
  exact coverp00110011110
private noncomputable def ep00110011111_0 : Blocks := edgeBlocks% "full/vectors/00110011111-E-0000.bin"
private noncomputable def ep00110011111_1 : Blocks := edgeBlocks% "full/vectors/00110011111-E-0001.bin"
noncomputable def ep00110011111 : Blocks := (Blocks.join ep00110011111_0 ep00110011111_1)
private theorem idp00110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011001111.list =
    C ((2:ℤ)^237) * horner X vp00110011111.list + horner X ep00110011111.list := by
  exact edge_identity (B := (2:ℤ)^417) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110011111 : Branch 1 (-1655761639/8000000 : ℚ) vp0011001111 := by
  apply branch_checked idp00110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1655761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1659761639/4000000 : ℚ) by norm_num]
  exact coverp00110011111
theorem coverp0011001111 : Covers (-1655761639/8000000 : ℚ) vp0011001111 := join_branches bp00110011110 bp00110011111
private noncomputable def vp0011001110111_0 : Blocks := edgeBlocks% "full/vectors/0011001110111-V-0000.bin"
noncomputable def vp0011001110111 : Blocks := vp0011001110111_0
theorem coverp0011001110111 : Covers (-1654761639/1000000 : ℚ) vp0011001110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011001110110_0 : Blocks := edgeBlocks% "full/vectors/0011001110110-V-0000.bin"
noncomputable def vp0011001110110 : Blocks := vp0011001110110_0
theorem coverp0011001110110 : Covers (-1653761639/1000000 : ℚ) vp0011001110110 := cover_leaf (by decide +kernel)
private noncomputable def vp001100111011_0 : Blocks := edgeBlocks% "full/vectors/001100111011-V-0000.bin"
noncomputable def vp001100111011 : Blocks := vp001100111011_0
private theorem bp0011001110110 : Branch 0 (-1653761639/2000000 : ℚ) vp001100111011 := by
  apply branch_left_normalized (c:=vp0011001110110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1653761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1653761639/1000000 : ℚ) by norm_num]
  exact coverp0011001110110
private noncomputable def ep0011001110111_0 : Blocks := edgeBlocks% "full/vectors/0011001110111-E-0000.bin"
noncomputable def ep0011001110111 : Blocks := ep0011001110111_0
private theorem idp0011001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100111011.list =
    C ((2:ℤ)^73) * horner X vp0011001110111.list + horner X ep0011001110111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001110111 : Branch 1 (-1653761639/2000000 : ℚ) vp001100111011 := by
  apply branch_checked idp0011001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1653761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1654761639/1000000 : ℚ) by norm_num]
  exact coverp0011001110111
theorem coverp001100111011 : Covers (-1653761639/2000000 : ℚ) vp001100111011 := join_branches bp0011001110110 bp0011001110111
private noncomputable def vp0011001110101_0 : Blocks := edgeBlocks% "full/vectors/0011001110101-V-0000.bin"
noncomputable def vp0011001110101 : Blocks := vp0011001110101_0
theorem coverp0011001110101 : Covers (-1652761639/1000000 : ℚ) vp0011001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011001110100_0 : Blocks := edgeBlocks% "full/vectors/0011001110100-V-0000.bin"
noncomputable def vp0011001110100 : Blocks := vp0011001110100_0
theorem coverp0011001110100 : Covers (-1651761639/1000000 : ℚ) vp0011001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001100111010_0 : Blocks := edgeBlocks% "full/vectors/001100111010-V-0000.bin"
noncomputable def vp001100111010 : Blocks := vp001100111010_0
private theorem bp0011001110100 : Branch 0 (-1651761639/2000000 : ℚ) vp001100111010 := by
  apply branch_left_normalized (c:=vp0011001110100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1651761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1651761639/1000000 : ℚ) by norm_num]
  exact coverp0011001110100
private noncomputable def ep0011001110101_0 : Blocks := edgeBlocks% "full/vectors/0011001110101-E-0000.bin"
noncomputable def ep0011001110101 : Blocks := ep0011001110101_0
private theorem idp0011001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100111010.list =
    C ((2:ℤ)^74) * horner X vp0011001110101.list + horner X ep0011001110101.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001110101 : Branch 1 (-1651761639/2000000 : ℚ) vp001100111010 := by
  apply branch_checked idp0011001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1651761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1652761639/1000000 : ℚ) by norm_num]
  exact coverp0011001110101
theorem coverp001100111010 : Covers (-1651761639/2000000 : ℚ) vp001100111010 := join_branches bp0011001110100 bp0011001110101
private noncomputable def vp00110011101_0 : Blocks := edgeBlocks% "full/vectors/00110011101-V-0000.bin"
noncomputable def vp00110011101 : Blocks := vp00110011101_0
private theorem bp001100111010 : Branch 0 (-1651761639/4000000 : ℚ) vp00110011101 := by
  apply branch_left_normalized (c:=vp001100111010) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1651761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1651761639/2000000 : ℚ) by norm_num]
  exact coverp001100111010
private noncomputable def ep001100111011_0 : Blocks := edgeBlocks% "full/vectors/001100111011-E-0000.bin"
noncomputable def ep001100111011 : Blocks := ep001100111011_0
private theorem idp001100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110011101.list =
    C ((2:ℤ)^130) * horner X vp001100111011.list + horner X ep001100111011.list := by
  exact edge_identity (B := (2:ℤ)^269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100111011 : Branch 1 (-1651761639/4000000 : ℚ) vp00110011101 := by
  apply branch_checked idp001100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1651761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1653761639/2000000 : ℚ) by norm_num]
  exact coverp001100111011
theorem coverp00110011101 : Covers (-1651761639/4000000 : ℚ) vp00110011101 := join_branches bp001100111010 bp001100111011
private noncomputable def vp0011001110011_0 : Blocks := edgeBlocks% "full/vectors/0011001110011-V-0000.bin"
noncomputable def vp0011001110011 : Blocks := vp0011001110011_0
theorem coverp0011001110011 : Covers (-1650761639/1000000 : ℚ) vp0011001110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011001110010_0 : Blocks := edgeBlocks% "full/vectors/0011001110010-V-0000.bin"
noncomputable def vp0011001110010 : Blocks := vp0011001110010_0
theorem coverp0011001110010 : Covers (-1649761639/1000000 : ℚ) vp0011001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001100111001_0 : Blocks := edgeBlocks% "full/vectors/001100111001-V-0000.bin"
noncomputable def vp001100111001 : Blocks := vp001100111001_0
private theorem bp0011001110010 : Branch 0 (-1649761639/2000000 : ℚ) vp001100111001 := by
  apply branch_left_normalized (c:=vp0011001110010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1649761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1649761639/1000000 : ℚ) by norm_num]
  exact coverp0011001110010
private noncomputable def ep0011001110011_0 : Blocks := edgeBlocks% "full/vectors/0011001110011-E-0000.bin"
noncomputable def ep0011001110011 : Blocks := ep0011001110011_0
private theorem idp0011001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100111001.list =
    C ((2:ℤ)^76) * horner X vp0011001110011.list + horner X ep0011001110011.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001110011 : Branch 1 (-1649761639/2000000 : ℚ) vp001100111001 := by
  apply branch_checked idp0011001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1649761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1650761639/1000000 : ℚ) by norm_num]
  exact coverp0011001110011
theorem coverp001100111001 : Covers (-1649761639/2000000 : ℚ) vp001100111001 := join_branches bp0011001110010 bp0011001110011
private noncomputable def vp0011001110001_0 : Blocks := edgeBlocks% "full/vectors/0011001110001-V-0000.bin"
noncomputable def vp0011001110001 : Blocks := vp0011001110001_0
theorem coverp0011001110001 : Covers (-1648761639/1000000 : ℚ) vp0011001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011001110000_0 : Blocks := edgeBlocks% "full/vectors/0011001110000-V-0000.bin"
noncomputable def vp0011001110000 : Blocks := vp0011001110000_0
theorem coverp0011001110000 : Covers (-1647761639/1000000 : ℚ) vp0011001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001100111000_0 : Blocks := edgeBlocks% "full/vectors/001100111000-V-0000.bin"
noncomputable def vp001100111000 : Blocks := vp001100111000_0
private theorem bp0011001110000 : Branch 0 (-1647761639/2000000 : ℚ) vp001100111000 := by
  apply branch_left_normalized (c:=vp0011001110000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1647761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1647761639/1000000 : ℚ) by norm_num]
  exact coverp0011001110000
private noncomputable def ep0011001110001_0 : Blocks := edgeBlocks% "full/vectors/0011001110001-E-0000.bin"
noncomputable def ep0011001110001 : Blocks := ep0011001110001_0
private theorem idp0011001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100111000.list =
    C ((2:ℤ)^74) * horner X vp0011001110001.list + horner X ep0011001110001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001110001 : Branch 1 (-1647761639/2000000 : ℚ) vp001100111000 := by
  apply branch_checked idp0011001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1647761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1648761639/1000000 : ℚ) by norm_num]
  exact coverp0011001110001
theorem coverp001100111000 : Covers (-1647761639/2000000 : ℚ) vp001100111000 := join_branches bp0011001110000 bp0011001110001
private noncomputable def vp00110011100_0 : Blocks := edgeBlocks% "full/vectors/00110011100-V-0000.bin"
noncomputable def vp00110011100 : Blocks := vp00110011100_0
private theorem bp001100111000 : Branch 0 (-1647761639/4000000 : ℚ) vp00110011100 := by
  apply branch_left_normalized (c:=vp001100111000) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1647761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1647761639/2000000 : ℚ) by norm_num]
  exact coverp001100111000
private noncomputable def ep001100111001_0 : Blocks := edgeBlocks% "full/vectors/001100111001-E-0000.bin"
noncomputable def ep001100111001 : Blocks := ep001100111001_0
private theorem idp001100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110011100.list =
    C ((2:ℤ)^130) * horner X vp001100111001.list + horner X ep001100111001.list := by
  exact edge_identity (B := (2:ℤ)^271) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100111001 : Branch 1 (-1647761639/4000000 : ℚ) vp00110011100 := by
  apply branch_checked idp001100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1647761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1649761639/2000000 : ℚ) by norm_num]
  exact coverp001100111001
theorem coverp00110011100 : Covers (-1647761639/4000000 : ℚ) vp00110011100 := join_branches bp001100111000 bp001100111001
private noncomputable def vp0011001110_0 : Blocks := edgeBlocks% "full/vectors/0011001110-V-0000.bin"
private noncomputable def vp0011001110_1 : Blocks := edgeBlocks% "full/vectors/0011001110-V-0001.bin"
noncomputable def vp0011001110 : Blocks := (Blocks.join vp0011001110_0 vp0011001110_1)
private theorem bp00110011100 : Branch 0 (-1647761639/8000000 : ℚ) vp0011001110 := by
  apply branch_left_normalized (c:=vp00110011100) (k:=0) (m:=118) (by decide +kernel)
  rw [show 2*(-1647761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1647761639/4000000 : ℚ) by norm_num]
  exact coverp00110011100
private noncomputable def ep00110011101_0 : Blocks := edgeBlocks% "full/vectors/00110011101-E-0000.bin"
private noncomputable def ep00110011101_1 : Blocks := edgeBlocks% "full/vectors/00110011101-E-0001.bin"
noncomputable def ep00110011101 : Blocks := (Blocks.join ep00110011101_0 ep00110011101_1)
private theorem idp00110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011001110.list =
    C ((2:ℤ)^240) * horner X vp00110011101.list + horner X ep00110011101.list := by
  exact edge_identity (B := (2:ℤ)^419) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110011101 : Branch 1 (-1647761639/8000000 : ℚ) vp0011001110 := by
  apply branch_checked idp00110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1647761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1651761639/4000000 : ℚ) by norm_num]
  exact coverp00110011101
theorem coverp0011001110 : Covers (-1647761639/8000000 : ℚ) vp0011001110 := join_branches bp00110011100 bp00110011101
private noncomputable def vp001100111_0 : Blocks := edgeBlocks% "full/vectors/001100111-V-0000.bin"
private noncomputable def vp001100111_1 : Blocks := edgeBlocks% "full/vectors/001100111-V-0001.bin"
private noncomputable def vp001100111_2 : Blocks := edgeBlocks% "full/vectors/001100111-V-0002.bin"
private noncomputable def vp001100111_3 : Blocks := edgeBlocks% "full/vectors/001100111-V-0003.bin"
noncomputable def vp001100111 : Blocks := (Blocks.join (Blocks.join vp001100111_0 vp001100111_1) (Blocks.join vp001100111_2 vp001100111_3))
private theorem bp0011001110 : Branch 0 (-1647761639/16000000 : ℚ) vp001100111 := by
  apply branch_left_normalized (c:=vp0011001110) (k:=0) (m:=215) (by decide +kernel)
  rw [show 2*(-1647761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1647761639/8000000 : ℚ) by norm_num]
  exact coverp0011001110
private noncomputable def ep0011001111_0 : Blocks := edgeBlocks% "full/vectors/0011001111-E-0000.bin"
private noncomputable def ep0011001111_1 : Blocks := edgeBlocks% "full/vectors/0011001111-E-0001.bin"
private noncomputable def ep0011001111_2 : Blocks := edgeBlocks% "full/vectors/0011001111-E-0002.bin"
private noncomputable def ep0011001111_3 : Blocks := edgeBlocks% "full/vectors/0011001111-E-0003.bin"
noncomputable def ep0011001111 : Blocks := (Blocks.join (Blocks.join ep0011001111_0 ep0011001111_1) (Blocks.join ep0011001111_2 ep0011001111_3))
private theorem idp0011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100111.list =
    C ((2:ℤ)^455) * horner X vp0011001111.list + horner X ep0011001111.list := by
  exact edge_identity (B := (2:ℤ)^714) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001111 : Branch 1 (-1647761639/16000000 : ℚ) vp001100111 := by
  apply branch_checked idp0011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1647761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1655761639/8000000 : ℚ) by norm_num]
  exact coverp0011001111
theorem coverp001100111 : Covers (-1647761639/16000000 : ℚ) vp001100111 := join_branches bp0011001110 bp0011001111
private noncomputable def vp0011001101111_0 : Blocks := edgeBlocks% "full/vectors/0011001101111-V-0000.bin"
noncomputable def vp0011001101111 : Blocks := vp0011001101111_0
theorem coverp0011001101111 : Covers (-1646761639/1000000 : ℚ) vp0011001101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011001101110_0 : Blocks := edgeBlocks% "full/vectors/0011001101110-V-0000.bin"
noncomputable def vp0011001101110 : Blocks := vp0011001101110_0
theorem coverp0011001101110 : Covers (-1645761639/1000000 : ℚ) vp0011001101110 := cover_leaf (by decide +kernel)
private noncomputable def vp001100110111_0 : Blocks := edgeBlocks% "full/vectors/001100110111-V-0000.bin"
noncomputable def vp001100110111 : Blocks := vp001100110111_0
private theorem bp0011001101110 : Branch 0 (-1645761639/2000000 : ℚ) vp001100110111 := by
  apply branch_left_normalized (c:=vp0011001101110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1645761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1645761639/1000000 : ℚ) by norm_num]
  exact coverp0011001101110
private noncomputable def ep0011001101111_0 : Blocks := edgeBlocks% "full/vectors/0011001101111-E-0000.bin"
noncomputable def ep0011001101111 : Blocks := ep0011001101111_0
private theorem idp0011001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100110111.list =
    C ((2:ℤ)^73) * horner X vp0011001101111.list + horner X ep0011001101111.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001101111 : Branch 1 (-1645761639/2000000 : ℚ) vp001100110111 := by
  apply branch_checked idp0011001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1645761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1646761639/1000000 : ℚ) by norm_num]
  exact coverp0011001101111
theorem coverp001100110111 : Covers (-1645761639/2000000 : ℚ) vp001100110111 := join_branches bp0011001101110 bp0011001101111
private noncomputable def vp001100110110_0 : Blocks := edgeBlocks% "full/vectors/001100110110-V-0000.bin"
noncomputable def vp001100110110 : Blocks := vp001100110110_0
theorem coverp001100110110 : Covers (-1643761639/2000000 : ℚ) vp001100110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00110011011_0 : Blocks := edgeBlocks% "full/vectors/00110011011-V-0000.bin"
noncomputable def vp00110011011 : Blocks := vp00110011011_0
private theorem bp001100110110 : Branch 0 (-1643761639/4000000 : ℚ) vp00110011011 := by
  apply branch_left_normalized (c:=vp001100110110) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1643761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1643761639/2000000 : ℚ) by norm_num]
  exact coverp001100110110
private noncomputable def ep001100110111_0 : Blocks := edgeBlocks% "full/vectors/001100110111-E-0000.bin"
noncomputable def ep001100110111 : Blocks := ep001100110111_0
private theorem idp001100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110011011.list =
    C ((2:ℤ)^128) * horner X vp001100110111.list + horner X ep001100110111.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100110111 : Branch 1 (-1643761639/4000000 : ℚ) vp00110011011 := by
  apply branch_checked idp001100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1643761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1645761639/2000000 : ℚ) by norm_num]
  exact coverp001100110111
theorem coverp00110011011 : Covers (-1643761639/4000000 : ℚ) vp00110011011 := join_branches bp001100110110 bp001100110111
private noncomputable def vp001100110101_0 : Blocks := edgeBlocks% "full/vectors/001100110101-V-0000.bin"
noncomputable def vp001100110101 : Blocks := vp001100110101_0
theorem coverp001100110101 : Covers (-1641761639/2000000 : ℚ) vp001100110101 := cover_leaf (by decide +kernel)
private noncomputable def vp001100110100_0 : Blocks := edgeBlocks% "full/vectors/001100110100-V-0000.bin"
noncomputable def vp001100110100 : Blocks := vp001100110100_0
theorem coverp001100110100 : Covers (-1639761639/2000000 : ℚ) vp001100110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00110011010_0 : Blocks := edgeBlocks% "full/vectors/00110011010-V-0000.bin"
noncomputable def vp00110011010 : Blocks := vp00110011010_0
private theorem bp001100110100 : Branch 0 (-1639761639/4000000 : ℚ) vp00110011010 := by
  apply branch_left_normalized (c:=vp001100110100) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1639761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1639761639/2000000 : ℚ) by norm_num]
  exact coverp001100110100
private noncomputable def ep001100110101_0 : Blocks := edgeBlocks% "full/vectors/001100110101-E-0000.bin"
noncomputable def ep001100110101 : Blocks := ep001100110101_0
private theorem idp001100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110011010.list =
    C ((2:ℤ)^128) * horner X vp001100110101.list + horner X ep001100110101.list := by
  exact edge_identity (B := (2:ℤ)^265) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100110101 : Branch 1 (-1639761639/4000000 : ℚ) vp00110011010 := by
  apply branch_checked idp001100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1639761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1641761639/2000000 : ℚ) by norm_num]
  exact coverp001100110101
theorem coverp00110011010 : Covers (-1639761639/4000000 : ℚ) vp00110011010 := join_branches bp001100110100 bp001100110101
private noncomputable def vp0011001101_0 : Blocks := edgeBlocks% "full/vectors/0011001101-V-0000.bin"
private noncomputable def vp0011001101_1 : Blocks := edgeBlocks% "full/vectors/0011001101-V-0001.bin"
noncomputable def vp0011001101 : Blocks := (Blocks.join vp0011001101_0 vp0011001101_1)
private theorem bp00110011010 : Branch 0 (-1639761639/8000000 : ℚ) vp0011001101 := by
  apply branch_left_normalized (c:=vp00110011010) (k:=0) (m:=116) (by decide +kernel)
  rw [show 2*(-1639761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1639761639/4000000 : ℚ) by norm_num]
  exact coverp00110011010
private noncomputable def ep00110011011_0 : Blocks := edgeBlocks% "full/vectors/00110011011-E-0000.bin"
private noncomputable def ep00110011011_1 : Blocks := edgeBlocks% "full/vectors/00110011011-E-0001.bin"
noncomputable def ep00110011011 : Blocks := (Blocks.join ep00110011011_0 ep00110011011_1)
private theorem idp00110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011001101.list =
    C ((2:ℤ)^236) * horner X vp00110011011.list + horner X ep00110011011.list := by
  exact edge_identity (B := (2:ℤ)^413) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110011011 : Branch 1 (-1639761639/8000000 : ℚ) vp0011001101 := by
  apply branch_checked idp00110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1639761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1643761639/4000000 : ℚ) by norm_num]
  exact coverp00110011011
theorem coverp0011001101 : Covers (-1639761639/8000000 : ℚ) vp0011001101 := join_branches bp00110011010 bp00110011011
private noncomputable def vp001100110011_0 : Blocks := edgeBlocks% "full/vectors/001100110011-V-0000.bin"
noncomputable def vp001100110011 : Blocks := vp001100110011_0
theorem coverp001100110011 : Covers (-1637761639/2000000 : ℚ) vp001100110011 := cover_leaf (by decide +kernel)
private noncomputable def vp001100110010_0 : Blocks := edgeBlocks% "full/vectors/001100110010-V-0000.bin"
noncomputable def vp001100110010 : Blocks := vp001100110010_0
theorem coverp001100110010 : Covers (-1635761639/2000000 : ℚ) vp001100110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00110011001_0 : Blocks := edgeBlocks% "full/vectors/00110011001-V-0000.bin"
noncomputable def vp00110011001 : Blocks := vp00110011001_0
private theorem bp001100110010 : Branch 0 (-1635761639/4000000 : ℚ) vp00110011001 := by
  apply branch_left_normalized (c:=vp001100110010) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-1635761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1635761639/2000000 : ℚ) by norm_num]
  exact coverp001100110010
private noncomputable def ep001100110011_0 : Blocks := edgeBlocks% "full/vectors/001100110011-E-0000.bin"
noncomputable def ep001100110011 : Blocks := ep001100110011_0
private theorem idp001100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110011001.list =
    C ((2:ℤ)^135) * horner X vp001100110011.list + horner X ep001100110011.list := by
  exact edge_identity (B := (2:ℤ)^273) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100110011 : Branch 1 (-1635761639/4000000 : ℚ) vp00110011001 := by
  apply branch_checked idp001100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1635761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1637761639/2000000 : ℚ) by norm_num]
  exact coverp001100110011
theorem coverp00110011001 : Covers (-1635761639/4000000 : ℚ) vp00110011001 := join_branches bp001100110010 bp001100110011
private noncomputable def vp0011001100011_0 : Blocks := edgeBlocks% "full/vectors/0011001100011-V-0000.bin"
noncomputable def vp0011001100011 : Blocks := vp0011001100011_0
theorem coverp0011001100011 : Covers (-1634761639/1000000 : ℚ) vp0011001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011001100010_0 : Blocks := edgeBlocks% "full/vectors/0011001100010-V-0000.bin"
noncomputable def vp0011001100010 : Blocks := vp0011001100010_0
theorem coverp0011001100010 : Covers (-1633761639/1000000 : ℚ) vp0011001100010 := cover_leaf (by decide +kernel)
private noncomputable def vp001100110001_0 : Blocks := edgeBlocks% "full/vectors/001100110001-V-0000.bin"
noncomputable def vp001100110001 : Blocks := vp001100110001_0
private theorem bp0011001100010 : Branch 0 (-1633761639/2000000 : ℚ) vp001100110001 := by
  apply branch_left_normalized (c:=vp0011001100010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1633761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1633761639/1000000 : ℚ) by norm_num]
  exact coverp0011001100010
private noncomputable def ep0011001100011_0 : Blocks := edgeBlocks% "full/vectors/0011001100011-E-0000.bin"
noncomputable def ep0011001100011 : Blocks := ep0011001100011_0
private theorem idp0011001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100110001.list =
    C ((2:ℤ)^70) * horner X vp0011001100011.list + horner X ep0011001100011.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001100011 : Branch 1 (-1633761639/2000000 : ℚ) vp001100110001 := by
  apply branch_checked idp0011001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1633761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1634761639/1000000 : ℚ) by norm_num]
  exact coverp0011001100011
theorem coverp001100110001 : Covers (-1633761639/2000000 : ℚ) vp001100110001 := join_branches bp0011001100010 bp0011001100011
private noncomputable def vp001100110000_0 : Blocks := edgeBlocks% "full/vectors/001100110000-V-0000.bin"
noncomputable def vp001100110000 : Blocks := vp001100110000_0
theorem coverp001100110000 : Covers (-1631761639/2000000 : ℚ) vp001100110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00110011000_0 : Blocks := edgeBlocks% "full/vectors/00110011000-V-0000.bin"
noncomputable def vp00110011000 : Blocks := vp00110011000_0
private theorem bp001100110000 : Branch 0 (-1631761639/4000000 : ℚ) vp00110011000 := by
  apply branch_left_normalized (c:=vp001100110000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1631761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1631761639/2000000 : ℚ) by norm_num]
  exact coverp001100110000
private noncomputable def ep001100110001_0 : Blocks := edgeBlocks% "full/vectors/001100110001-E-0000.bin"
noncomputable def ep001100110001 : Blocks := ep001100110001_0
private theorem idp001100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110011000.list =
    C ((2:ℤ)^126) * horner X vp001100110001.list + horner X ep001100110001.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100110001 : Branch 1 (-1631761639/4000000 : ℚ) vp00110011000 := by
  apply branch_checked idp001100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1631761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1633761639/2000000 : ℚ) by norm_num]
  exact coverp001100110001
theorem coverp00110011000 : Covers (-1631761639/4000000 : ℚ) vp00110011000 := join_branches bp001100110000 bp001100110001
private noncomputable def vp0011001100_0 : Blocks := edgeBlocks% "full/vectors/0011001100-V-0000.bin"
private noncomputable def vp0011001100_1 : Blocks := edgeBlocks% "full/vectors/0011001100-V-0001.bin"
noncomputable def vp0011001100 : Blocks := (Blocks.join vp0011001100_0 vp0011001100_1)
private theorem bp00110011000 : Branch 0 (-1631761639/8000000 : ℚ) vp0011001100 := by
  apply branch_left_normalized (c:=vp00110011000) (k:=0) (m:=115) (by decide +kernel)
  rw [show 2*(-1631761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1631761639/4000000 : ℚ) by norm_num]
  exact coverp00110011000
private noncomputable def ep00110011001_0 : Blocks := edgeBlocks% "full/vectors/00110011001-E-0000.bin"
private noncomputable def ep00110011001_1 : Blocks := edgeBlocks% "full/vectors/00110011001-E-0001.bin"
noncomputable def ep00110011001 : Blocks := (Blocks.join ep00110011001_0 ep00110011001_1)
private theorem idp00110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011001100.list =
    C ((2:ℤ)^231) * horner X vp00110011001.list + horner X ep00110011001.list := by
  exact edge_identity (B := (2:ℤ)^412) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110011001 : Branch 1 (-1631761639/8000000 : ℚ) vp0011001100 := by
  apply branch_checked idp00110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1631761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1635761639/4000000 : ℚ) by norm_num]
  exact coverp00110011001
theorem coverp0011001100 : Covers (-1631761639/8000000 : ℚ) vp0011001100 := join_branches bp00110011000 bp00110011001
private noncomputable def vp001100110_0 : Blocks := edgeBlocks% "full/vectors/001100110-V-0000.bin"
private noncomputable def vp001100110_1 : Blocks := edgeBlocks% "full/vectors/001100110-V-0001.bin"
private noncomputable def vp001100110_2 : Blocks := edgeBlocks% "full/vectors/001100110-V-0002.bin"
private noncomputable def vp001100110_3 : Blocks := edgeBlocks% "full/vectors/001100110-V-0003.bin"
noncomputable def vp001100110 : Blocks := (Blocks.join (Blocks.join vp001100110_0 vp001100110_1) (Blocks.join vp001100110_2 vp001100110_3))
private theorem bp0011001100 : Branch 0 (-1631761639/16000000 : ℚ) vp001100110 := by
  apply branch_left_normalized (c:=vp0011001100) (k:=0) (m:=213) (by decide +kernel)
  rw [show 2*(-1631761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1631761639/8000000 : ℚ) by norm_num]
  exact coverp0011001100
private noncomputable def ep0011001101_0 : Blocks := edgeBlocks% "full/vectors/0011001101-E-0000.bin"
private noncomputable def ep0011001101_1 : Blocks := edgeBlocks% "full/vectors/0011001101-E-0001.bin"
private noncomputable def ep0011001101_2 : Blocks := edgeBlocks% "full/vectors/0011001101-E-0002.bin"
private noncomputable def ep0011001101_3 : Blocks := edgeBlocks% "full/vectors/0011001101-E-0003.bin"
noncomputable def ep0011001101 : Blocks := (Blocks.join (Blocks.join ep0011001101_0 ep0011001101_1) (Blocks.join ep0011001101_2 ep0011001101_3))
private theorem idp0011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100110.list =
    C ((2:ℤ)^451) * horner X vp0011001101.list + horner X ep0011001101.list := by
  exact edge_identity (B := (2:ℤ)^708) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001101 : Branch 1 (-1631761639/16000000 : ℚ) vp001100110 := by
  apply branch_checked idp0011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1631761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1639761639/8000000 : ℚ) by norm_num]
  exact coverp0011001101
theorem coverp001100110 : Covers (-1631761639/16000000 : ℚ) vp001100110 := join_branches bp0011001100 bp0011001101
private noncomputable def vp00110011_0 : Blocks := edgeBlocks% "full/vectors/00110011-V-0000.bin"
private noncomputable def vp00110011_1 : Blocks := edgeBlocks% "full/vectors/00110011-V-0001.bin"
private noncomputable def vp00110011_2 : Blocks := edgeBlocks% "full/vectors/00110011-V-0002.bin"
private noncomputable def vp00110011_3 : Blocks := edgeBlocks% "full/vectors/00110011-V-0003.bin"
private noncomputable def vp00110011_4 : Blocks := edgeBlocks% "full/vectors/00110011-V-0004.bin"
private noncomputable def vp00110011_5 : Blocks := edgeBlocks% "full/vectors/00110011-V-0005.bin"
private noncomputable def vp00110011_6 : Blocks := edgeBlocks% "full/vectors/00110011-V-0006.bin"
noncomputable def vp00110011 : Blocks := (Blocks.join (Blocks.join vp00110011_0 (Blocks.join vp00110011_1 vp00110011_2)) (Blocks.join (Blocks.join vp00110011_3 vp00110011_4) (Blocks.join vp00110011_5 vp00110011_6)))
private theorem bp001100110 : Branch 0 (-1631761639/32000000 : ℚ) vp00110011 := by
  apply branch_left_normalized (c:=vp001100110) (k:=0) (m:=405) (by decide +kernel)
  rw [show 2*(-1631761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1631761639/16000000 : ℚ) by norm_num]
  exact coverp001100110
private noncomputable def ep001100111_0 : Blocks := edgeBlocks% "full/vectors/001100111-E-0000.bin"
private noncomputable def ep001100111_1 : Blocks := edgeBlocks% "full/vectors/001100111-E-0001.bin"
private noncomputable def ep001100111_2 : Blocks := edgeBlocks% "full/vectors/001100111-E-0002.bin"
private noncomputable def ep001100111_3 : Blocks := edgeBlocks% "full/vectors/001100111-E-0003.bin"
private noncomputable def ep001100111_4 : Blocks := edgeBlocks% "full/vectors/001100111-E-0004.bin"
private noncomputable def ep001100111_5 : Blocks := edgeBlocks% "full/vectors/001100111-E-0005.bin"
private noncomputable def ep001100111_6 : Blocks := edgeBlocks% "full/vectors/001100111-E-0006.bin"
noncomputable def ep001100111 : Blocks := (Blocks.join (Blocks.join ep001100111_0 (Blocks.join ep001100111_1 ep001100111_2)) (Blocks.join (Blocks.join ep001100111_3 ep001100111_4) (Blocks.join ep001100111_5 ep001100111_6)))
private theorem idp001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110011.list =
    C ((2:ℤ)^876) * horner X vp001100111.list + horner X ep001100111.list := by
  exact edge_identity (B := (2:ℤ)^1296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100111 : Branch 1 (-1631761639/32000000 : ℚ) vp00110011 := by
  apply branch_checked idp001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1631761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1647761639/16000000 : ℚ) by norm_num]
  exact coverp001100111
theorem coverp00110011 : Covers (-1631761639/32000000 : ℚ) vp00110011 := join_branches bp001100110 bp001100111
private noncomputable def vp001100101111_0 : Blocks := edgeBlocks% "full/vectors/001100101111-V-0000.bin"
noncomputable def vp001100101111 : Blocks := vp001100101111_0
theorem coverp001100101111 : Covers (-1629761639/2000000 : ℚ) vp001100101111 := cover_leaf (by decide +kernel)
private noncomputable def vp001100101110_0 : Blocks := edgeBlocks% "full/vectors/001100101110-V-0000.bin"
noncomputable def vp001100101110 : Blocks := vp001100101110_0
theorem coverp001100101110 : Covers (-1627761639/2000000 : ℚ) vp001100101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00110010111_0 : Blocks := edgeBlocks% "full/vectors/00110010111-V-0000.bin"
noncomputable def vp00110010111 : Blocks := vp00110010111_0
private theorem bp001100101110 : Branch 0 (-1627761639/4000000 : ℚ) vp00110010111 := by
  apply branch_left_normalized (c:=vp001100101110) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1627761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1627761639/2000000 : ℚ) by norm_num]
  exact coverp001100101110
private noncomputable def ep001100101111_0 : Blocks := edgeBlocks% "full/vectors/001100101111-E-0000.bin"
noncomputable def ep001100101111 : Blocks := ep001100101111_0
private theorem idp001100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110010111.list =
    C ((2:ℤ)^125) * horner X vp001100101111.list + horner X ep001100101111.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100101111 : Branch 1 (-1627761639/4000000 : ℚ) vp00110010111 := by
  apply branch_checked idp001100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1627761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1629761639/2000000 : ℚ) by norm_num]
  exact coverp001100101111
theorem coverp00110010111 : Covers (-1627761639/4000000 : ℚ) vp00110010111 := join_branches bp001100101110 bp001100101111
private noncomputable def vp001100101101_0 : Blocks := edgeBlocks% "full/vectors/001100101101-V-0000.bin"
noncomputable def vp001100101101 : Blocks := vp001100101101_0
theorem coverp001100101101 : Covers (-1625761639/2000000 : ℚ) vp001100101101 := cover_leaf (by decide +kernel)
private noncomputable def vp001100101100_0 : Blocks := edgeBlocks% "full/vectors/001100101100-V-0000.bin"
noncomputable def vp001100101100 : Blocks := vp001100101100_0
theorem coverp001100101100 : Covers (-1623761639/2000000 : ℚ) vp001100101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00110010110_0 : Blocks := edgeBlocks% "full/vectors/00110010110-V-0000.bin"
noncomputable def vp00110010110 : Blocks := vp00110010110_0
private theorem bp001100101100 : Branch 0 (-1623761639/4000000 : ℚ) vp00110010110 := by
  apply branch_left_normalized (c:=vp001100101100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1623761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1623761639/2000000 : ℚ) by norm_num]
  exact coverp001100101100
private noncomputable def ep001100101101_0 : Blocks := edgeBlocks% "full/vectors/001100101101-E-0000.bin"
noncomputable def ep001100101101 : Blocks := ep001100101101_0
private theorem idp001100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110010110.list =
    C ((2:ℤ)^125) * horner X vp001100101101.list + horner X ep001100101101.list := by
  exact edge_identity (B := (2:ℤ)^257) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100101101 : Branch 1 (-1623761639/4000000 : ℚ) vp00110010110 := by
  apply branch_checked idp001100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1623761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1625761639/2000000 : ℚ) by norm_num]
  exact coverp001100101101
theorem coverp00110010110 : Covers (-1623761639/4000000 : ℚ) vp00110010110 := join_branches bp001100101100 bp001100101101
private noncomputable def vp0011001011_0 : Blocks := edgeBlocks% "full/vectors/0011001011-V-0000.bin"
private noncomputable def vp0011001011_1 : Blocks := edgeBlocks% "full/vectors/0011001011-V-0001.bin"
noncomputable def vp0011001011 : Blocks := (Blocks.join vp0011001011_0 vp0011001011_1)
private theorem bp00110010110 : Branch 0 (-1623761639/8000000 : ℚ) vp0011001011 := by
  apply branch_left_normalized (c:=vp00110010110) (k:=0) (m:=113) (by decide +kernel)
  rw [show 2*(-1623761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1623761639/4000000 : ℚ) by norm_num]
  exact coverp00110010110
private noncomputable def ep00110010111_0 : Blocks := edgeBlocks% "full/vectors/00110010111-E-0000.bin"
private noncomputable def ep00110010111_1 : Blocks := edgeBlocks% "full/vectors/00110010111-E-0001.bin"
noncomputable def ep00110010111 : Blocks := (Blocks.join ep00110010111_0 ep00110010111_1)
private theorem idp00110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011001011.list =
    C ((2:ℤ)^234) * horner X vp00110010111.list + horner X ep00110010111.list := by
  exact edge_identity (B := (2:ℤ)^407) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110010111 : Branch 1 (-1623761639/8000000 : ℚ) vp0011001011 := by
  apply branch_checked idp00110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1623761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1627761639/4000000 : ℚ) by norm_num]
  exact coverp00110010111
theorem coverp0011001011 : Covers (-1623761639/8000000 : ℚ) vp0011001011 := join_branches bp00110010110 bp00110010111
private noncomputable def vp001100101011_0 : Blocks := edgeBlocks% "full/vectors/001100101011-V-0000.bin"
noncomputable def vp001100101011 : Blocks := vp001100101011_0
theorem coverp001100101011 : Covers (-1621761639/2000000 : ℚ) vp001100101011 := cover_leaf (by decide +kernel)
private noncomputable def vp001100101010_0 : Blocks := edgeBlocks% "full/vectors/001100101010-V-0000.bin"
noncomputable def vp001100101010 : Blocks := vp001100101010_0
theorem coverp001100101010 : Covers (-1619761639/2000000 : ℚ) vp001100101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00110010101_0 : Blocks := edgeBlocks% "full/vectors/00110010101-V-0000.bin"
noncomputable def vp00110010101 : Blocks := vp00110010101_0
private theorem bp001100101010 : Branch 0 (-1619761639/4000000 : ℚ) vp00110010101 := by
  apply branch_left_normalized (c:=vp001100101010) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-1619761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1619761639/2000000 : ℚ) by norm_num]
  exact coverp001100101010
private noncomputable def ep001100101011_0 : Blocks := edgeBlocks% "full/vectors/001100101011-E-0000.bin"
noncomputable def ep001100101011 : Blocks := ep001100101011_0
private theorem idp001100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110010101.list =
    C ((2:ℤ)^126) * horner X vp001100101011.list + horner X ep001100101011.list := by
  exact edge_identity (B := (2:ℤ)^257) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100101011 : Branch 1 (-1619761639/4000000 : ℚ) vp00110010101 := by
  apply branch_checked idp001100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1619761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1621761639/2000000 : ℚ) by norm_num]
  exact coverp001100101011
theorem coverp00110010101 : Covers (-1619761639/4000000 : ℚ) vp00110010101 := join_branches bp001100101010 bp001100101011
private noncomputable def vp001100101001_0 : Blocks := edgeBlocks% "full/vectors/001100101001-V-0000.bin"
noncomputable def vp001100101001 : Blocks := vp001100101001_0
theorem coverp001100101001 : Covers (-1617761639/2000000 : ℚ) vp001100101001 := cover_leaf (by decide +kernel)
private noncomputable def vp001100101000_0 : Blocks := edgeBlocks% "full/vectors/001100101000-V-0000.bin"
noncomputable def vp001100101000 : Blocks := vp001100101000_0
theorem coverp001100101000 : Covers (-1615761639/2000000 : ℚ) vp001100101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00110010100_0 : Blocks := edgeBlocks% "full/vectors/00110010100-V-0000.bin"
noncomputable def vp00110010100 : Blocks := vp00110010100_0
private theorem bp001100101000 : Branch 0 (-1615761639/4000000 : ℚ) vp00110010100 := by
  apply branch_left_normalized (c:=vp001100101000) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-1615761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1615761639/2000000 : ℚ) by norm_num]
  exact coverp001100101000
private noncomputable def ep001100101001_0 : Blocks := edgeBlocks% "full/vectors/001100101001-E-0000.bin"
noncomputable def ep001100101001 : Blocks := ep001100101001_0
private theorem idp001100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110010100.list =
    C ((2:ℤ)^126) * horner X vp001100101001.list + horner X ep001100101001.list := by
  exact edge_identity (B := (2:ℤ)^257) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100101001 : Branch 1 (-1615761639/4000000 : ℚ) vp00110010100 := by
  apply branch_checked idp001100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1615761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1617761639/2000000 : ℚ) by norm_num]
  exact coverp001100101001
theorem coverp00110010100 : Covers (-1615761639/4000000 : ℚ) vp00110010100 := join_branches bp001100101000 bp001100101001
private noncomputable def vp0011001010_0 : Blocks := edgeBlocks% "full/vectors/0011001010-V-0000.bin"
private noncomputable def vp0011001010_1 : Blocks := edgeBlocks% "full/vectors/0011001010-V-0001.bin"
noncomputable def vp0011001010 : Blocks := (Blocks.join vp0011001010_0 vp0011001010_1)
private theorem bp00110010100 : Branch 0 (-1615761639/8000000 : ℚ) vp0011001010 := by
  apply branch_left_normalized (c:=vp00110010100) (k:=0) (m:=113) (by decide +kernel)
  rw [show 2*(-1615761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1615761639/4000000 : ℚ) by norm_num]
  exact coverp00110010100
private noncomputable def ep00110010101_0 : Blocks := edgeBlocks% "full/vectors/00110010101-E-0000.bin"
private noncomputable def ep00110010101_1 : Blocks := edgeBlocks% "full/vectors/00110010101-E-0001.bin"
noncomputable def ep00110010101 : Blocks := (Blocks.join ep00110010101_0 ep00110010101_1)
private theorem idp00110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011001010.list =
    C ((2:ℤ)^234) * horner X vp00110010101.list + horner X ep00110010101.list := by
  exact edge_identity (B := (2:ℤ)^406) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110010101 : Branch 1 (-1615761639/8000000 : ℚ) vp0011001010 := by
  apply branch_checked idp00110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1615761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1619761639/4000000 : ℚ) by norm_num]
  exact coverp00110010101
theorem coverp0011001010 : Covers (-1615761639/8000000 : ℚ) vp0011001010 := join_branches bp00110010100 bp00110010101
private noncomputable def vp001100101_0 : Blocks := edgeBlocks% "full/vectors/001100101-V-0000.bin"
private noncomputable def vp001100101_1 : Blocks := edgeBlocks% "full/vectors/001100101-V-0001.bin"
private noncomputable def vp001100101_2 : Blocks := edgeBlocks% "full/vectors/001100101-V-0002.bin"
private noncomputable def vp001100101_3 : Blocks := edgeBlocks% "full/vectors/001100101-V-0003.bin"
noncomputable def vp001100101 : Blocks := (Blocks.join (Blocks.join vp001100101_0 vp001100101_1) (Blocks.join vp001100101_2 vp001100101_3))
private theorem bp0011001010 : Branch 0 (-1615761639/16000000 : ℚ) vp001100101 := by
  apply branch_left_normalized (c:=vp0011001010) (k:=0) (m:=210) (by decide +kernel)
  rw [show 2*(-1615761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1615761639/8000000 : ℚ) by norm_num]
  exact coverp0011001010
private noncomputable def ep0011001011_0 : Blocks := edgeBlocks% "full/vectors/0011001011-E-0000.bin"
private noncomputable def ep0011001011_1 : Blocks := edgeBlocks% "full/vectors/0011001011-E-0001.bin"
private noncomputable def ep0011001011_2 : Blocks := edgeBlocks% "full/vectors/0011001011-E-0002.bin"
private noncomputable def ep0011001011_3 : Blocks := edgeBlocks% "full/vectors/0011001011-E-0003.bin"
noncomputable def ep0011001011 : Blocks := (Blocks.join (Blocks.join ep0011001011_0 ep0011001011_1) (Blocks.join ep0011001011_2 ep0011001011_3))
private theorem idp0011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100101.list =
    C ((2:ℤ)^451) * horner X vp0011001011.list + horner X ep0011001011.list := by
  exact edge_identity (B := (2:ℤ)^703) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001011 : Branch 1 (-1615761639/16000000 : ℚ) vp001100101 := by
  apply branch_checked idp0011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1615761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1623761639/8000000 : ℚ) by norm_num]
  exact coverp0011001011
theorem coverp001100101 : Covers (-1615761639/16000000 : ℚ) vp001100101 := join_branches bp0011001010 bp0011001011
private noncomputable def vp001100100111_0 : Blocks := edgeBlocks% "full/vectors/001100100111-V-0000.bin"
noncomputable def vp001100100111 : Blocks := vp001100100111_0
theorem coverp001100100111 : Covers (-1613761639/2000000 : ℚ) vp001100100111 := cover_leaf (by decide +kernel)
private noncomputable def vp001100100110_0 : Blocks := edgeBlocks% "full/vectors/001100100110-V-0000.bin"
noncomputable def vp001100100110 : Blocks := vp001100100110_0
theorem coverp001100100110 : Covers (-1611761639/2000000 : ℚ) vp001100100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00110010011_0 : Blocks := edgeBlocks% "full/vectors/00110010011-V-0000.bin"
noncomputable def vp00110010011 : Blocks := vp00110010011_0
private theorem bp001100100110 : Branch 0 (-1611761639/4000000 : ℚ) vp00110010011 := by
  apply branch_left_normalized (c:=vp001100100110) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1611761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1611761639/2000000 : ℚ) by norm_num]
  exact coverp001100100110
private noncomputable def ep001100100111_0 : Blocks := edgeBlocks% "full/vectors/001100100111-E-0000.bin"
noncomputable def ep001100100111 : Blocks := ep001100100111_0
private theorem idp001100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110010011.list =
    C ((2:ℤ)^126) * horner X vp001100100111.list + horner X ep001100100111.list := by
  exact edge_identity (B := (2:ℤ)^257) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100100111 : Branch 1 (-1611761639/4000000 : ℚ) vp00110010011 := by
  apply branch_checked idp001100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1611761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1613761639/2000000 : ℚ) by norm_num]
  exact coverp001100100111
theorem coverp00110010011 : Covers (-1611761639/4000000 : ℚ) vp00110010011 := join_branches bp001100100110 bp001100100111
private noncomputable def vp001100100101_0 : Blocks := edgeBlocks% "full/vectors/001100100101-V-0000.bin"
noncomputable def vp001100100101 : Blocks := vp001100100101_0
theorem coverp001100100101 : Covers (-1609761639/2000000 : ℚ) vp001100100101 := cover_leaf (by decide +kernel)
private noncomputable def vp001100100100_0 : Blocks := edgeBlocks% "full/vectors/001100100100-V-0000.bin"
noncomputable def vp001100100100 : Blocks := vp001100100100_0
theorem coverp001100100100 : Covers (-1607761639/2000000 : ℚ) vp001100100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00110010010_0 : Blocks := edgeBlocks% "full/vectors/00110010010-V-0000.bin"
noncomputable def vp00110010010 : Blocks := vp00110010010_0
private theorem bp001100100100 : Branch 0 (-1607761639/4000000 : ℚ) vp00110010010 := by
  apply branch_left_normalized (c:=vp001100100100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1607761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1607761639/2000000 : ℚ) by norm_num]
  exact coverp001100100100
private noncomputable def ep001100100101_0 : Blocks := edgeBlocks% "full/vectors/001100100101-E-0000.bin"
noncomputable def ep001100100101 : Blocks := ep001100100101_0
private theorem idp001100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110010010.list =
    C ((2:ℤ)^127) * horner X vp001100100101.list + horner X ep001100100101.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100100101 : Branch 1 (-1607761639/4000000 : ℚ) vp00110010010 := by
  apply branch_checked idp001100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1607761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1609761639/2000000 : ℚ) by norm_num]
  exact coverp001100100101
theorem coverp00110010010 : Covers (-1607761639/4000000 : ℚ) vp00110010010 := join_branches bp001100100100 bp001100100101
private noncomputable def vp0011001001_0 : Blocks := edgeBlocks% "full/vectors/0011001001-V-0000.bin"
private noncomputable def vp0011001001_1 : Blocks := edgeBlocks% "full/vectors/0011001001-V-0001.bin"
noncomputable def vp0011001001 : Blocks := (Blocks.join vp0011001001_0 vp0011001001_1)
private theorem bp00110010010 : Branch 0 (-1607761639/8000000 : ℚ) vp0011001001 := by
  apply branch_left_normalized (c:=vp00110010010) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-1607761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1607761639/4000000 : ℚ) by norm_num]
  exact coverp00110010010
private noncomputable def ep00110010011_0 : Blocks := edgeBlocks% "full/vectors/00110010011-E-0000.bin"
private noncomputable def ep00110010011_1 : Blocks := edgeBlocks% "full/vectors/00110010011-E-0001.bin"
noncomputable def ep00110010011 : Blocks := (Blocks.join ep00110010011_0 ep00110010011_1)
private theorem idp00110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011001001.list =
    C ((2:ℤ)^237) * horner X vp00110010011.list + horner X ep00110010011.list := by
  exact edge_identity (B := (2:ℤ)^409) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110010011 : Branch 1 (-1607761639/8000000 : ℚ) vp0011001001 := by
  apply branch_checked idp00110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1607761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1611761639/4000000 : ℚ) by norm_num]
  exact coverp00110010011
theorem coverp0011001001 : Covers (-1607761639/8000000 : ℚ) vp0011001001 := join_branches bp00110010010 bp00110010011
private noncomputable def vp001100100011_0 : Blocks := edgeBlocks% "full/vectors/001100100011-V-0000.bin"
noncomputable def vp001100100011 : Blocks := vp001100100011_0
theorem coverp001100100011 : Covers (-1605761639/2000000 : ℚ) vp001100100011 := cover_leaf (by decide +kernel)
private noncomputable def vp001100100010_0 : Blocks := edgeBlocks% "full/vectors/001100100010-V-0000.bin"
noncomputable def vp001100100010 : Blocks := vp001100100010_0
theorem coverp001100100010 : Covers (-1603761639/2000000 : ℚ) vp001100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00110010001_0 : Blocks := edgeBlocks% "full/vectors/00110010001-V-0000.bin"
noncomputable def vp00110010001 : Blocks := vp00110010001_0
private theorem bp001100100010 : Branch 0 (-1603761639/4000000 : ℚ) vp00110010001 := by
  apply branch_left_normalized (c:=vp001100100010) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1603761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1603761639/2000000 : ℚ) by norm_num]
  exact coverp001100100010
private noncomputable def ep001100100011_0 : Blocks := edgeBlocks% "full/vectors/001100100011-E-0000.bin"
noncomputable def ep001100100011 : Blocks := ep001100100011_0
private theorem idp001100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110010001.list =
    C ((2:ℤ)^129) * horner X vp001100100011.list + horner X ep001100100011.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100100011 : Branch 1 (-1603761639/4000000 : ℚ) vp00110010001 := by
  apply branch_checked idp001100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1603761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1605761639/2000000 : ℚ) by norm_num]
  exact coverp001100100011
theorem coverp00110010001 : Covers (-1603761639/4000000 : ℚ) vp00110010001 := join_branches bp001100100010 bp001100100011
private noncomputable def vp001100100001_0 : Blocks := edgeBlocks% "full/vectors/001100100001-V-0000.bin"
noncomputable def vp001100100001 : Blocks := vp001100100001_0
theorem coverp001100100001 : Covers (-1601761639/2000000 : ℚ) vp001100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp001100100000_0 : Blocks := edgeBlocks% "full/vectors/001100100000-V-0000.bin"
noncomputable def vp001100100000 : Blocks := vp001100100000_0
theorem coverp001100100000 : Covers (-1599761639/2000000 : ℚ) vp001100100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00110010000_0 : Blocks := edgeBlocks% "full/vectors/00110010000-V-0000.bin"
noncomputable def vp00110010000 : Blocks := vp00110010000_0
private theorem bp001100100000 : Branch 0 (-1599761639/4000000 : ℚ) vp00110010000 := by
  apply branch_left_normalized (c:=vp001100100000) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1599761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1599761639/2000000 : ℚ) by norm_num]
  exact coverp001100100000
private noncomputable def ep001100100001_0 : Blocks := edgeBlocks% "full/vectors/001100100001-E-0000.bin"
noncomputable def ep001100100001 : Blocks := ep001100100001_0
private theorem idp001100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110010000.list =
    C ((2:ℤ)^132) * horner X vp001100100001.list + horner X ep001100100001.list := by
  exact edge_identity (B := (2:ℤ)^268) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100100001 : Branch 1 (-1599761639/4000000 : ℚ) vp00110010000 := by
  apply branch_checked idp001100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1599761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1601761639/2000000 : ℚ) by norm_num]
  exact coverp001100100001
theorem coverp00110010000 : Covers (-1599761639/4000000 : ℚ) vp00110010000 := join_branches bp001100100000 bp001100100001
private noncomputable def vp0011001000_0 : Blocks := edgeBlocks% "full/vectors/0011001000-V-0000.bin"
private noncomputable def vp0011001000_1 : Blocks := edgeBlocks% "full/vectors/0011001000-V-0001.bin"
noncomputable def vp0011001000 : Blocks := (Blocks.join vp0011001000_0 vp0011001000_1)
private theorem bp00110010000 : Branch 0 (-1599761639/8000000 : ℚ) vp0011001000 := by
  apply branch_left_normalized (c:=vp00110010000) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-1599761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1599761639/4000000 : ℚ) by norm_num]
  exact coverp00110010000
private noncomputable def ep00110010001_0 : Blocks := edgeBlocks% "full/vectors/00110010001-E-0000.bin"
private noncomputable def ep00110010001_1 : Blocks := edgeBlocks% "full/vectors/00110010001-E-0001.bin"
noncomputable def ep00110010001 : Blocks := (Blocks.join ep00110010001_0 ep00110010001_1)
private theorem idp00110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011001000.list =
    C ((2:ℤ)^244) * horner X vp00110010001.list + horner X ep00110010001.list := by
  exact edge_identity (B := (2:ℤ)^419) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110010001 : Branch 1 (-1599761639/8000000 : ℚ) vp0011001000 := by
  apply branch_checked idp00110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1599761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1603761639/4000000 : ℚ) by norm_num]
  exact coverp00110010001
theorem coverp0011001000 : Covers (-1599761639/8000000 : ℚ) vp0011001000 := join_branches bp00110010000 bp00110010001
private noncomputable def vp001100100_0 : Blocks := edgeBlocks% "full/vectors/001100100-V-0000.bin"
private noncomputable def vp001100100_1 : Blocks := edgeBlocks% "full/vectors/001100100-V-0001.bin"
private noncomputable def vp001100100_2 : Blocks := edgeBlocks% "full/vectors/001100100-V-0002.bin"
private noncomputable def vp001100100_3 : Blocks := edgeBlocks% "full/vectors/001100100-V-0003.bin"
noncomputable def vp001100100 : Blocks := (Blocks.join (Blocks.join vp001100100_0 vp001100100_1) (Blocks.join vp001100100_2 vp001100100_3))
private theorem bp0011001000 : Branch 0 (-1599761639/16000000 : ℚ) vp001100100 := by
  apply branch_left_normalized (c:=vp0011001000) (k:=0) (m:=216) (by decide +kernel)
  rw [show 2*(-1599761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1599761639/8000000 : ℚ) by norm_num]
  exact coverp0011001000
private noncomputable def ep0011001001_0 : Blocks := edgeBlocks% "full/vectors/0011001001-E-0000.bin"
private noncomputable def ep0011001001_1 : Blocks := edgeBlocks% "full/vectors/0011001001-E-0001.bin"
private noncomputable def ep0011001001_2 : Blocks := edgeBlocks% "full/vectors/0011001001-E-0002.bin"
private noncomputable def ep0011001001_3 : Blocks := edgeBlocks% "full/vectors/0011001001-E-0003.bin"
noncomputable def ep0011001001 : Blocks := (Blocks.join (Blocks.join ep0011001001_0 ep0011001001_1) (Blocks.join ep0011001001_2 ep0011001001_3))
private theorem idp0011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001100100.list =
    C ((2:ℤ)^464) * horner X vp0011001001.list + horner X ep0011001001.list := by
  exact edge_identity (B := (2:ℤ)^718) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011001001 : Branch 1 (-1599761639/16000000 : ℚ) vp001100100 := by
  apply branch_checked idp0011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1599761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1607761639/8000000 : ℚ) by norm_num]
  exact coverp0011001001
theorem coverp001100100 : Covers (-1599761639/16000000 : ℚ) vp001100100 := join_branches bp0011001000 bp0011001001
private noncomputable def vp00110010_0 : Blocks := edgeBlocks% "full/vectors/00110010-V-0000.bin"
private noncomputable def vp00110010_1 : Blocks := edgeBlocks% "full/vectors/00110010-V-0001.bin"
private noncomputable def vp00110010_2 : Blocks := edgeBlocks% "full/vectors/00110010-V-0002.bin"
private noncomputable def vp00110010_3 : Blocks := edgeBlocks% "full/vectors/00110010-V-0003.bin"
private noncomputable def vp00110010_4 : Blocks := edgeBlocks% "full/vectors/00110010-V-0004.bin"
private noncomputable def vp00110010_5 : Blocks := edgeBlocks% "full/vectors/00110010-V-0005.bin"
private noncomputable def vp00110010_6 : Blocks := edgeBlocks% "full/vectors/00110010-V-0006.bin"
noncomputable def vp00110010 : Blocks := (Blocks.join (Blocks.join vp00110010_0 (Blocks.join vp00110010_1 vp00110010_2)) (Blocks.join (Blocks.join vp00110010_3 vp00110010_4) (Blocks.join vp00110010_5 vp00110010_6)))
private theorem bp001100100 : Branch 0 (-1599761639/32000000 : ℚ) vp00110010 := by
  apply branch_left_normalized (c:=vp001100100) (k:=0) (m:=411) (by decide +kernel)
  rw [show 2*(-1599761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1599761639/16000000 : ℚ) by norm_num]
  exact coverp001100100
private noncomputable def ep001100101_0 : Blocks := edgeBlocks% "full/vectors/001100101-E-0000.bin"
private noncomputable def ep001100101_1 : Blocks := edgeBlocks% "full/vectors/001100101-E-0001.bin"
private noncomputable def ep001100101_2 : Blocks := edgeBlocks% "full/vectors/001100101-E-0002.bin"
private noncomputable def ep001100101_3 : Blocks := edgeBlocks% "full/vectors/001100101-E-0003.bin"
private noncomputable def ep001100101_4 : Blocks := edgeBlocks% "full/vectors/001100101-E-0004.bin"
private noncomputable def ep001100101_5 : Blocks := edgeBlocks% "full/vectors/001100101-E-0005.bin"
private noncomputable def ep001100101_6 : Blocks := edgeBlocks% "full/vectors/001100101-E-0006.bin"
noncomputable def ep001100101 : Blocks := (Blocks.join (Blocks.join ep001100101_0 (Blocks.join ep001100101_1 ep001100101_2)) (Blocks.join (Blocks.join ep001100101_3 ep001100101_4) (Blocks.join ep001100101_5 ep001100101_6)))
private theorem idp001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110010.list =
    C ((2:ℤ)^897) * horner X vp001100101.list + horner X ep001100101.list := by
  exact edge_identity (B := (2:ℤ)^1311) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001100101 : Branch 1 (-1599761639/32000000 : ℚ) vp00110010 := by
  apply branch_checked idp001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1599761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1615761639/16000000 : ℚ) by norm_num]
  exact coverp001100101
theorem coverp00110010 : Covers (-1599761639/32000000 : ℚ) vp00110010 := join_branches bp001100100 bp001100101
private noncomputable def vp0011001_0 : Blocks := edgeBlocks% "full/vectors/0011001-V-0000.bin"
private noncomputable def vp0011001_1 : Blocks := edgeBlocks% "full/vectors/0011001-V-0001.bin"
private noncomputable def vp0011001_2 : Blocks := edgeBlocks% "full/vectors/0011001-V-0002.bin"
private noncomputable def vp0011001_3 : Blocks := edgeBlocks% "full/vectors/0011001-V-0003.bin"
private noncomputable def vp0011001_4 : Blocks := edgeBlocks% "full/vectors/0011001-V-0004.bin"
private noncomputable def vp0011001_5 : Blocks := edgeBlocks% "full/vectors/0011001-V-0005.bin"
private noncomputable def vp0011001_6 : Blocks := edgeBlocks% "full/vectors/0011001-V-0006.bin"
private noncomputable def vp0011001_7 : Blocks := edgeBlocks% "full/vectors/0011001-V-0007.bin"
private noncomputable def vp0011001_8 : Blocks := edgeBlocks% "full/vectors/0011001-V-0008.bin"
private noncomputable def vp0011001_9 : Blocks := edgeBlocks% "full/vectors/0011001-V-0009.bin"
private noncomputable def vp0011001_10 : Blocks := edgeBlocks% "full/vectors/0011001-V-0010.bin"
private noncomputable def vp0011001_11 : Blocks := edgeBlocks% "full/vectors/0011001-V-0011.bin"
private noncomputable def vp0011001_12 : Blocks := edgeBlocks% "full/vectors/0011001-V-0012.bin"
noncomputable def vp0011001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0011001_0 (Blocks.join vp0011001_1 vp0011001_2)) (Blocks.join vp0011001_3 (Blocks.join vp0011001_4 vp0011001_5))) (Blocks.join (Blocks.join vp0011001_6 (Blocks.join vp0011001_7 vp0011001_8)) (Blocks.join (Blocks.join vp0011001_9 vp0011001_10) (Blocks.join vp0011001_11 vp0011001_12))))
private theorem bp00110010 : Branch 0 (-1599761639/64000000 : ℚ) vp0011001 := by
  apply branch_left_normalized (c:=vp00110010) (k:=0) (m:=797) (by decide +kernel)
  rw [show 2*(-1599761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1599761639/32000000 : ℚ) by norm_num]
  exact coverp00110010
private noncomputable def ep00110011_0 : Blocks := edgeBlocks% "full/vectors/00110011-E-0000.bin"
private noncomputable def ep00110011_1 : Blocks := edgeBlocks% "full/vectors/00110011-E-0001.bin"
private noncomputable def ep00110011_2 : Blocks := edgeBlocks% "full/vectors/00110011-E-0002.bin"
private noncomputable def ep00110011_3 : Blocks := edgeBlocks% "full/vectors/00110011-E-0003.bin"
private noncomputable def ep00110011_4 : Blocks := edgeBlocks% "full/vectors/00110011-E-0004.bin"
private noncomputable def ep00110011_5 : Blocks := edgeBlocks% "full/vectors/00110011-E-0005.bin"
private noncomputable def ep00110011_6 : Blocks := edgeBlocks% "full/vectors/00110011-E-0006.bin"
private noncomputable def ep00110011_7 : Blocks := edgeBlocks% "full/vectors/00110011-E-0007.bin"
private noncomputable def ep00110011_8 : Blocks := edgeBlocks% "full/vectors/00110011-E-0008.bin"
private noncomputable def ep00110011_9 : Blocks := edgeBlocks% "full/vectors/00110011-E-0009.bin"
private noncomputable def ep00110011_10 : Blocks := edgeBlocks% "full/vectors/00110011-E-0010.bin"
private noncomputable def ep00110011_11 : Blocks := edgeBlocks% "full/vectors/00110011-E-0011.bin"
private noncomputable def ep00110011_12 : Blocks := edgeBlocks% "full/vectors/00110011-E-0012.bin"
noncomputable def ep00110011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00110011_0 (Blocks.join ep00110011_1 ep00110011_2)) (Blocks.join ep00110011_3 (Blocks.join ep00110011_4 ep00110011_5))) (Blocks.join (Blocks.join ep00110011_6 (Blocks.join ep00110011_7 ep00110011_8)) (Blocks.join (Blocks.join ep00110011_9 ep00110011_10) (Blocks.join ep00110011_11 ep00110011_12))))
private theorem idp00110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011001.list =
    C ((2:ℤ)^1744) * horner X vp00110011.list + horner X ep00110011.list := by
  exact edge_identity (B := (2:ℤ)^2483) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110011 : Branch 1 (-1599761639/64000000 : ℚ) vp0011001 := by
  apply branch_checked idp00110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1599761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1631761639/32000000 : ℚ) by norm_num]
  exact coverp00110011
theorem coverp0011001 : Covers (-1599761639/64000000 : ℚ) vp0011001 := join_branches bp00110010 bp00110011
end NextProof.EdgeFull

