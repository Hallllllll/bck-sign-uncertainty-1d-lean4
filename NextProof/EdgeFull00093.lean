import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0010111111111_0 : Blocks := edgeBlocks% "full/vectors/0010111111111-V-0000.bin"
noncomputable def vp0010111111111 : Blocks := vp0010111111111_0
theorem coverp0010111111111 : Covers (-1534761639/1000000 : ℚ) vp0010111111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111111110_0 : Blocks := edgeBlocks% "full/vectors/0010111111110-V-0000.bin"
noncomputable def vp0010111111110 : Blocks := vp0010111111110_0
theorem coverp0010111111110 : Covers (-1533761639/1000000 : ℚ) vp0010111111110 := cover_leaf (by decide +kernel)
private noncomputable def vp001011111111_0 : Blocks := edgeBlocks% "full/vectors/001011111111-V-0000.bin"
noncomputable def vp001011111111 : Blocks := vp001011111111_0
private theorem bp0010111111110 : Branch 0 (-1533761639/2000000 : ℚ) vp001011111111 := by
  apply branch_left_normalized (c:=vp0010111111110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1533761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1533761639/1000000 : ℚ) by norm_num]
  exact coverp0010111111110
private noncomputable def ep0010111111111_0 : Blocks := edgeBlocks% "full/vectors/0010111111111-E-0000.bin"
noncomputable def ep0010111111111 : Blocks := ep0010111111111_0
private theorem idp0010111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011111111.list =
    C ((2:ℤ)^77) * horner X vp0010111111111.list + horner X ep0010111111111.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111111111 : Branch 1 (-1533761639/2000000 : ℚ) vp001011111111 := by
  apply branch_checked idp0010111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1533761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1534761639/1000000 : ℚ) by norm_num]
  exact coverp0010111111111
theorem coverp001011111111 : Covers (-1533761639/2000000 : ℚ) vp001011111111 := join_branches bp0010111111110 bp0010111111111
private noncomputable def vp0010111111101_0 : Blocks := edgeBlocks% "full/vectors/0010111111101-V-0000.bin"
noncomputable def vp0010111111101 : Blocks := vp0010111111101_0
theorem coverp0010111111101 : Covers (-1532761639/1000000 : ℚ) vp0010111111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111111100_0 : Blocks := edgeBlocks% "full/vectors/0010111111100-V-0000.bin"
noncomputable def vp0010111111100 : Blocks := vp0010111111100_0
theorem coverp0010111111100 : Covers (-1531761639/1000000 : ℚ) vp0010111111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011111110_0 : Blocks := edgeBlocks% "full/vectors/001011111110-V-0000.bin"
noncomputable def vp001011111110 : Blocks := vp001011111110_0
private theorem bp0010111111100 : Branch 0 (-1531761639/2000000 : ℚ) vp001011111110 := by
  apply branch_left_normalized (c:=vp0010111111100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1531761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1531761639/1000000 : ℚ) by norm_num]
  exact coverp0010111111100
private noncomputable def ep0010111111101_0 : Blocks := edgeBlocks% "full/vectors/0010111111101-E-0000.bin"
noncomputable def ep0010111111101 : Blocks := ep0010111111101_0
private theorem idp0010111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011111110.list =
    C ((2:ℤ)^78) * horner X vp0010111111101.list + horner X ep0010111111101.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111111101 : Branch 1 (-1531761639/2000000 : ℚ) vp001011111110 := by
  apply branch_checked idp0010111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1531761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1532761639/1000000 : ℚ) by norm_num]
  exact coverp0010111111101
theorem coverp001011111110 : Covers (-1531761639/2000000 : ℚ) vp001011111110 := join_branches bp0010111111100 bp0010111111101
private noncomputable def vp00101111111_0 : Blocks := edgeBlocks% "full/vectors/00101111111-V-0000.bin"
noncomputable def vp00101111111 : Blocks := vp00101111111_0
private theorem bp001011111110 : Branch 0 (-1531761639/4000000 : ℚ) vp00101111111 := by
  apply branch_left_normalized (c:=vp001011111110) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-1531761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1531761639/2000000 : ℚ) by norm_num]
  exact coverp001011111110
private noncomputable def ep001011111111_0 : Blocks := edgeBlocks% "full/vectors/001011111111-E-0000.bin"
noncomputable def ep001011111111 : Blocks := ep001011111111_0
private theorem idp001011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101111111.list =
    C ((2:ℤ)^135) * horner X vp001011111111.list + horner X ep001011111111.list := by
  exact edge_identity (B := (2:ℤ)^277) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011111111 : Branch 1 (-1531761639/4000000 : ℚ) vp00101111111 := by
  apply branch_checked idp001011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1531761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1533761639/2000000 : ℚ) by norm_num]
  exact coverp001011111111
theorem coverp00101111111 : Covers (-1531761639/4000000 : ℚ) vp00101111111 := join_branches bp001011111110 bp001011111111
private noncomputable def vp0010111111011_0 : Blocks := edgeBlocks% "full/vectors/0010111111011-V-0000.bin"
noncomputable def vp0010111111011 : Blocks := vp0010111111011_0
theorem coverp0010111111011 : Covers (-1530761639/1000000 : ℚ) vp0010111111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111111010_0 : Blocks := edgeBlocks% "full/vectors/0010111111010-V-0000.bin"
noncomputable def vp0010111111010 : Blocks := vp0010111111010_0
theorem coverp0010111111010 : Covers (-1529761639/1000000 : ℚ) vp0010111111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001011111101_0 : Blocks := edgeBlocks% "full/vectors/001011111101-V-0000.bin"
noncomputable def vp001011111101 : Blocks := vp001011111101_0
private theorem bp0010111111010 : Branch 0 (-1529761639/2000000 : ℚ) vp001011111101 := by
  apply branch_left_normalized (c:=vp0010111111010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1529761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1529761639/1000000 : ℚ) by norm_num]
  exact coverp0010111111010
private noncomputable def ep0010111111011_0 : Blocks := edgeBlocks% "full/vectors/0010111111011-E-0000.bin"
noncomputable def ep0010111111011 : Blocks := ep0010111111011_0
private theorem idp0010111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011111101.list =
    C ((2:ℤ)^77) * horner X vp0010111111011.list + horner X ep0010111111011.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111111011 : Branch 1 (-1529761639/2000000 : ℚ) vp001011111101 := by
  apply branch_checked idp0010111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1529761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1530761639/1000000 : ℚ) by norm_num]
  exact coverp0010111111011
theorem coverp001011111101 : Covers (-1529761639/2000000 : ℚ) vp001011111101 := join_branches bp0010111111010 bp0010111111011
private noncomputable def vp0010111111001_0 : Blocks := edgeBlocks% "full/vectors/0010111111001-V-0000.bin"
noncomputable def vp0010111111001 : Blocks := vp0010111111001_0
theorem coverp0010111111001 : Covers (-1528761639/1000000 : ℚ) vp0010111111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111111000_0 : Blocks := edgeBlocks% "full/vectors/0010111111000-V-0000.bin"
noncomputable def vp0010111111000 : Blocks := vp0010111111000_0
theorem coverp0010111111000 : Covers (-1527761639/1000000 : ℚ) vp0010111111000 := cover_leaf (by decide +kernel)
private noncomputable def vp001011111100_0 : Blocks := edgeBlocks% "full/vectors/001011111100-V-0000.bin"
noncomputable def vp001011111100 : Blocks := vp001011111100_0
private theorem bp0010111111000 : Branch 0 (-1527761639/2000000 : ℚ) vp001011111100 := by
  apply branch_left_normalized (c:=vp0010111111000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1527761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1527761639/1000000 : ℚ) by norm_num]
  exact coverp0010111111000
private noncomputable def ep0010111111001_0 : Blocks := edgeBlocks% "full/vectors/0010111111001-E-0000.bin"
noncomputable def ep0010111111001 : Blocks := ep0010111111001_0
private theorem idp0010111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011111100.list =
    C ((2:ℤ)^76) * horner X vp0010111111001.list + horner X ep0010111111001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111111001 : Branch 1 (-1527761639/2000000 : ℚ) vp001011111100 := by
  apply branch_checked idp0010111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1527761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1528761639/1000000 : ℚ) by norm_num]
  exact coverp0010111111001
theorem coverp001011111100 : Covers (-1527761639/2000000 : ℚ) vp001011111100 := join_branches bp0010111111000 bp0010111111001
private noncomputable def vp00101111110_0 : Blocks := edgeBlocks% "full/vectors/00101111110-V-0000.bin"
noncomputable def vp00101111110 : Blocks := vp00101111110_0
private theorem bp001011111100 : Branch 0 (-1527761639/4000000 : ℚ) vp00101111110 := by
  apply branch_left_normalized (c:=vp001011111100) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1527761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1527761639/2000000 : ℚ) by norm_num]
  exact coverp001011111100
private noncomputable def ep001011111101_0 : Blocks := edgeBlocks% "full/vectors/001011111101-E-0000.bin"
noncomputable def ep001011111101 : Blocks := ep001011111101_0
private theorem idp001011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101111110.list =
    C ((2:ℤ)^132) * horner X vp001011111101.list + horner X ep001011111101.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011111101 : Branch 1 (-1527761639/4000000 : ℚ) vp00101111110 := by
  apply branch_checked idp001011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1527761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1529761639/2000000 : ℚ) by norm_num]
  exact coverp001011111101
theorem coverp00101111110 : Covers (-1527761639/4000000 : ℚ) vp00101111110 := join_branches bp001011111100 bp001011111101
private noncomputable def vp0010111111_0 : Blocks := edgeBlocks% "full/vectors/0010111111-V-0000.bin"
private noncomputable def vp0010111111_1 : Blocks := edgeBlocks% "full/vectors/0010111111-V-0001.bin"
noncomputable def vp0010111111 : Blocks := (Blocks.join vp0010111111_0 vp0010111111_1)
private theorem bp00101111110 : Branch 0 (-1527761639/8000000 : ℚ) vp0010111111 := by
  apply branch_left_normalized (c:=vp00101111110) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-1527761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1527761639/4000000 : ℚ) by norm_num]
  exact coverp00101111110
private noncomputable def ep00101111111_0 : Blocks := edgeBlocks% "full/vectors/00101111111-E-0000.bin"
private noncomputable def ep00101111111_1 : Blocks := edgeBlocks% "full/vectors/00101111111-E-0001.bin"
noncomputable def ep00101111111 : Blocks := (Blocks.join ep00101111111_0 ep00101111111_1)
private theorem idp00101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010111111.list =
    C ((2:ℤ)^245) * horner X vp00101111111.list + horner X ep00101111111.list := by
  exact edge_identity (B := (2:ℤ)^430) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101111111 : Branch 1 (-1527761639/8000000 : ℚ) vp0010111111 := by
  apply branch_checked idp00101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1527761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1531761639/4000000 : ℚ) by norm_num]
  exact coverp00101111111
theorem coverp0010111111 : Covers (-1527761639/8000000 : ℚ) vp0010111111 := join_branches bp00101111110 bp00101111111
private noncomputable def vp0010111110111_0 : Blocks := edgeBlocks% "full/vectors/0010111110111-V-0000.bin"
noncomputable def vp0010111110111 : Blocks := vp0010111110111_0
theorem coverp0010111110111 : Covers (-1526761639/1000000 : ℚ) vp0010111110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111110110_0 : Blocks := edgeBlocks% "full/vectors/0010111110110-V-0000.bin"
noncomputable def vp0010111110110 : Blocks := vp0010111110110_0
theorem coverp0010111110110 : Covers (-1525761639/1000000 : ℚ) vp0010111110110 := cover_leaf (by decide +kernel)
private noncomputable def vp001011111011_0 : Blocks := edgeBlocks% "full/vectors/001011111011-V-0000.bin"
noncomputable def vp001011111011 : Blocks := vp001011111011_0
private theorem bp0010111110110 : Branch 0 (-1525761639/2000000 : ℚ) vp001011111011 := by
  apply branch_left_normalized (c:=vp0010111110110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1525761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1525761639/1000000 : ℚ) by norm_num]
  exact coverp0010111110110
private noncomputable def ep0010111110111_0 : Blocks := edgeBlocks% "full/vectors/0010111110111-E-0000.bin"
noncomputable def ep0010111110111 : Blocks := ep0010111110111_0
private theorem idp0010111110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011111011.list =
    C ((2:ℤ)^75) * horner X vp0010111110111.list + horner X ep0010111110111.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111110111 : Branch 1 (-1525761639/2000000 : ℚ) vp001011111011 := by
  apply branch_checked idp0010111110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1525761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1526761639/1000000 : ℚ) by norm_num]
  exact coverp0010111110111
theorem coverp001011111011 : Covers (-1525761639/2000000 : ℚ) vp001011111011 := join_branches bp0010111110110 bp0010111110111
private noncomputable def vp0010111110101_0 : Blocks := edgeBlocks% "full/vectors/0010111110101-V-0000.bin"
noncomputable def vp0010111110101 : Blocks := vp0010111110101_0
theorem coverp0010111110101 : Covers (-1524761639/1000000 : ℚ) vp0010111110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111110100_0 : Blocks := edgeBlocks% "full/vectors/0010111110100-V-0000.bin"
noncomputable def vp0010111110100 : Blocks := vp0010111110100_0
theorem coverp0010111110100 : Covers (-1523761639/1000000 : ℚ) vp0010111110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011111010_0 : Blocks := edgeBlocks% "full/vectors/001011111010-V-0000.bin"
noncomputable def vp001011111010 : Blocks := vp001011111010_0
private theorem bp0010111110100 : Branch 0 (-1523761639/2000000 : ℚ) vp001011111010 := by
  apply branch_left_normalized (c:=vp0010111110100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1523761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1523761639/1000000 : ℚ) by norm_num]
  exact coverp0010111110100
private noncomputable def ep0010111110101_0 : Blocks := edgeBlocks% "full/vectors/0010111110101-E-0000.bin"
noncomputable def ep0010111110101 : Blocks := ep0010111110101_0
private theorem idp0010111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011111010.list =
    C ((2:ℤ)^77) * horner X vp0010111110101.list + horner X ep0010111110101.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111110101 : Branch 1 (-1523761639/2000000 : ℚ) vp001011111010 := by
  apply branch_checked idp0010111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1523761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1524761639/1000000 : ℚ) by norm_num]
  exact coverp0010111110101
theorem coverp001011111010 : Covers (-1523761639/2000000 : ℚ) vp001011111010 := join_branches bp0010111110100 bp0010111110101
private noncomputable def vp00101111101_0 : Blocks := edgeBlocks% "full/vectors/00101111101-V-0000.bin"
noncomputable def vp00101111101 : Blocks := vp00101111101_0
private theorem bp001011111010 : Branch 0 (-1523761639/4000000 : ℚ) vp00101111101 := by
  apply branch_left_normalized (c:=vp001011111010) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1523761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1523761639/2000000 : ℚ) by norm_num]
  exact coverp001011111010
private noncomputable def ep001011111011_0 : Blocks := edgeBlocks% "full/vectors/001011111011-E-0000.bin"
noncomputable def ep001011111011 : Blocks := ep001011111011_0
private theorem idp001011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101111101.list =
    C ((2:ℤ)^133) * horner X vp001011111011.list + horner X ep001011111011.list := by
  exact edge_identity (B := (2:ℤ)^274) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011111011 : Branch 1 (-1523761639/4000000 : ℚ) vp00101111101 := by
  apply branch_checked idp001011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1523761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1525761639/2000000 : ℚ) by norm_num]
  exact coverp001011111011
theorem coverp00101111101 : Covers (-1523761639/4000000 : ℚ) vp00101111101 := join_branches bp001011111010 bp001011111011
private noncomputable def vp0010111110011_0 : Blocks := edgeBlocks% "full/vectors/0010111110011-V-0000.bin"
noncomputable def vp0010111110011 : Blocks := vp0010111110011_0
theorem coverp0010111110011 : Covers (-1522761639/1000000 : ℚ) vp0010111110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111110010_0 : Blocks := edgeBlocks% "full/vectors/0010111110010-V-0000.bin"
noncomputable def vp0010111110010 : Blocks := vp0010111110010_0
theorem coverp0010111110010 : Covers (-1521761639/1000000 : ℚ) vp0010111110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001011111001_0 : Blocks := edgeBlocks% "full/vectors/001011111001-V-0000.bin"
noncomputable def vp001011111001 : Blocks := vp001011111001_0
private theorem bp0010111110010 : Branch 0 (-1521761639/2000000 : ℚ) vp001011111001 := by
  apply branch_left_normalized (c:=vp0010111110010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1521761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1521761639/1000000 : ℚ) by norm_num]
  exact coverp0010111110010
private noncomputable def ep0010111110011_0 : Blocks := edgeBlocks% "full/vectors/0010111110011-E-0000.bin"
noncomputable def ep0010111110011 : Blocks := ep0010111110011_0
private theorem idp0010111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011111001.list =
    C ((2:ℤ)^77) * horner X vp0010111110011.list + horner X ep0010111110011.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111110011 : Branch 1 (-1521761639/2000000 : ℚ) vp001011111001 := by
  apply branch_checked idp0010111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1521761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1522761639/1000000 : ℚ) by norm_num]
  exact coverp0010111110011
theorem coverp001011111001 : Covers (-1521761639/2000000 : ℚ) vp001011111001 := join_branches bp0010111110010 bp0010111110011
private noncomputable def vp0010111110001_0 : Blocks := edgeBlocks% "full/vectors/0010111110001-V-0000.bin"
noncomputable def vp0010111110001 : Blocks := vp0010111110001_0
theorem coverp0010111110001 : Covers (-1520761639/1000000 : ℚ) vp0010111110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111110000_0 : Blocks := edgeBlocks% "full/vectors/0010111110000-V-0000.bin"
noncomputable def vp0010111110000 : Blocks := vp0010111110000_0
theorem coverp0010111110000 : Covers (-1519761639/1000000 : ℚ) vp0010111110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001011111000_0 : Blocks := edgeBlocks% "full/vectors/001011111000-V-0000.bin"
noncomputable def vp001011111000 : Blocks := vp001011111000_0
private theorem bp0010111110000 : Branch 0 (-1519761639/2000000 : ℚ) vp001011111000 := by
  apply branch_left_normalized (c:=vp0010111110000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1519761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1519761639/1000000 : ℚ) by norm_num]
  exact coverp0010111110000
private noncomputable def ep0010111110001_0 : Blocks := edgeBlocks% "full/vectors/0010111110001-E-0000.bin"
noncomputable def ep0010111110001 : Blocks := ep0010111110001_0
private theorem idp0010111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011111000.list =
    C ((2:ℤ)^77) * horner X vp0010111110001.list + horner X ep0010111110001.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111110001 : Branch 1 (-1519761639/2000000 : ℚ) vp001011111000 := by
  apply branch_checked idp0010111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1519761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1520761639/1000000 : ℚ) by norm_num]
  exact coverp0010111110001
theorem coverp001011111000 : Covers (-1519761639/2000000 : ℚ) vp001011111000 := join_branches bp0010111110000 bp0010111110001
private noncomputable def vp00101111100_0 : Blocks := edgeBlocks% "full/vectors/00101111100-V-0000.bin"
noncomputable def vp00101111100 : Blocks := vp00101111100_0
private theorem bp001011111000 : Branch 0 (-1519761639/4000000 : ℚ) vp00101111100 := by
  apply branch_left_normalized (c:=vp001011111000) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-1519761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1519761639/2000000 : ℚ) by norm_num]
  exact coverp001011111000
private noncomputable def ep001011111001_0 : Blocks := edgeBlocks% "full/vectors/001011111001-E-0000.bin"
noncomputable def ep001011111001 : Blocks := ep001011111001_0
private theorem idp001011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101111100.list =
    C ((2:ℤ)^135) * horner X vp001011111001.list + horner X ep001011111001.list := by
  exact edge_identity (B := (2:ℤ)^277) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011111001 : Branch 1 (-1519761639/4000000 : ℚ) vp00101111100 := by
  apply branch_checked idp001011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1519761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1521761639/2000000 : ℚ) by norm_num]
  exact coverp001011111001
theorem coverp00101111100 : Covers (-1519761639/4000000 : ℚ) vp00101111100 := join_branches bp001011111000 bp001011111001
private noncomputable def vp0010111110_0 : Blocks := edgeBlocks% "full/vectors/0010111110-V-0000.bin"
private noncomputable def vp0010111110_1 : Blocks := edgeBlocks% "full/vectors/0010111110-V-0001.bin"
noncomputable def vp0010111110 : Blocks := (Blocks.join vp0010111110_0 vp0010111110_1)
private theorem bp00101111100 : Branch 0 (-1519761639/8000000 : ℚ) vp0010111110 := by
  apply branch_left_normalized (c:=vp00101111100) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-1519761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1519761639/4000000 : ℚ) by norm_num]
  exact coverp00101111100
private noncomputable def ep00101111101_0 : Blocks := edgeBlocks% "full/vectors/00101111101-E-0000.bin"
private noncomputable def ep00101111101_1 : Blocks := edgeBlocks% "full/vectors/00101111101-E-0001.bin"
noncomputable def ep00101111101 : Blocks := (Blocks.join ep00101111101_0 ep00101111101_1)
private theorem idp00101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010111110.list =
    C ((2:ℤ)^249) * horner X vp00101111101.list + horner X ep00101111101.list := by
  exact edge_identity (B := (2:ℤ)^433) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101111101 : Branch 1 (-1519761639/8000000 : ℚ) vp0010111110 := by
  apply branch_checked idp00101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1519761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1523761639/4000000 : ℚ) by norm_num]
  exact coverp00101111101
theorem coverp0010111110 : Covers (-1519761639/8000000 : ℚ) vp0010111110 := join_branches bp00101111100 bp00101111101
private noncomputable def vp001011111_0 : Blocks := edgeBlocks% "full/vectors/001011111-V-0000.bin"
private noncomputable def vp001011111_1 : Blocks := edgeBlocks% "full/vectors/001011111-V-0001.bin"
private noncomputable def vp001011111_2 : Blocks := edgeBlocks% "full/vectors/001011111-V-0002.bin"
private noncomputable def vp001011111_3 : Blocks := edgeBlocks% "full/vectors/001011111-V-0003.bin"
noncomputable def vp001011111 : Blocks := (Blocks.join (Blocks.join vp001011111_0 vp001011111_1) (Blocks.join vp001011111_2 vp001011111_3))
private theorem bp0010111110 : Branch 0 (-1519761639/16000000 : ℚ) vp001011111 := by
  apply branch_left_normalized (c:=vp0010111110) (k:=0) (m:=224) (by decide +kernel)
  rw [show 2*(-1519761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1519761639/8000000 : ℚ) by norm_num]
  exact coverp0010111110
private noncomputable def ep0010111111_0 : Blocks := edgeBlocks% "full/vectors/0010111111-E-0000.bin"
private noncomputable def ep0010111111_1 : Blocks := edgeBlocks% "full/vectors/0010111111-E-0001.bin"
private noncomputable def ep0010111111_2 : Blocks := edgeBlocks% "full/vectors/0010111111-E-0002.bin"
private noncomputable def ep0010111111_3 : Blocks := edgeBlocks% "full/vectors/0010111111-E-0003.bin"
noncomputable def ep0010111111 : Blocks := (Blocks.join (Blocks.join ep0010111111_0 ep0010111111_1) (Blocks.join ep0010111111_2 ep0010111111_3))
private theorem idp0010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011111.list =
    C ((2:ℤ)^472) * horner X vp0010111111.list + horner X ep0010111111.list := by
  exact edge_identity (B := (2:ℤ)^740) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111111 : Branch 1 (-1519761639/16000000 : ℚ) vp001011111 := by
  apply branch_checked idp0010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1519761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1527761639/8000000 : ℚ) by norm_num]
  exact coverp0010111111
theorem coverp001011111 : Covers (-1519761639/16000000 : ℚ) vp001011111 := join_branches bp0010111110 bp0010111111
private noncomputable def vp0010111101111_0 : Blocks := edgeBlocks% "full/vectors/0010111101111-V-0000.bin"
noncomputable def vp0010111101111 : Blocks := vp0010111101111_0
theorem coverp0010111101111 : Covers (-1518761639/1000000 : ℚ) vp0010111101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111101110_0 : Blocks := edgeBlocks% "full/vectors/0010111101110-V-0000.bin"
noncomputable def vp0010111101110 : Blocks := vp0010111101110_0
theorem coverp0010111101110 : Covers (-1517761639/1000000 : ℚ) vp0010111101110 := cover_leaf (by decide +kernel)
private noncomputable def vp001011110111_0 : Blocks := edgeBlocks% "full/vectors/001011110111-V-0000.bin"
noncomputable def vp001011110111 : Blocks := vp001011110111_0
private theorem bp0010111101110 : Branch 0 (-1517761639/2000000 : ℚ) vp001011110111 := by
  apply branch_left_normalized (c:=vp0010111101110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1517761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1517761639/1000000 : ℚ) by norm_num]
  exact coverp0010111101110
private noncomputable def ep0010111101111_0 : Blocks := edgeBlocks% "full/vectors/0010111101111-E-0000.bin"
noncomputable def ep0010111101111 : Blocks := ep0010111101111_0
private theorem idp0010111101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011110111.list =
    C ((2:ℤ)^76) * horner X vp0010111101111.list + horner X ep0010111101111.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111101111 : Branch 1 (-1517761639/2000000 : ℚ) vp001011110111 := by
  apply branch_checked idp0010111101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1517761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1518761639/1000000 : ℚ) by norm_num]
  exact coverp0010111101111
theorem coverp001011110111 : Covers (-1517761639/2000000 : ℚ) vp001011110111 := join_branches bp0010111101110 bp0010111101111
private noncomputable def vp0010111101101_0 : Blocks := edgeBlocks% "full/vectors/0010111101101-V-0000.bin"
noncomputable def vp0010111101101 : Blocks := vp0010111101101_0
theorem coverp0010111101101 : Covers (-1516761639/1000000 : ℚ) vp0010111101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111101100_0 : Blocks := edgeBlocks% "full/vectors/0010111101100-V-0000.bin"
noncomputable def vp0010111101100 : Blocks := vp0010111101100_0
theorem coverp0010111101100 : Covers (-1515761639/1000000 : ℚ) vp0010111101100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011110110_0 : Blocks := edgeBlocks% "full/vectors/001011110110-V-0000.bin"
noncomputable def vp001011110110 : Blocks := vp001011110110_0
private theorem bp0010111101100 : Branch 0 (-1515761639/2000000 : ℚ) vp001011110110 := by
  apply branch_left_normalized (c:=vp0010111101100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1515761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1515761639/1000000 : ℚ) by norm_num]
  exact coverp0010111101100
private noncomputable def ep0010111101101_0 : Blocks := edgeBlocks% "full/vectors/0010111101101-E-0000.bin"
noncomputable def ep0010111101101 : Blocks := ep0010111101101_0
private theorem idp0010111101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011110110.list =
    C ((2:ℤ)^74) * horner X vp0010111101101.list + horner X ep0010111101101.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111101101 : Branch 1 (-1515761639/2000000 : ℚ) vp001011110110 := by
  apply branch_checked idp0010111101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1515761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1516761639/1000000 : ℚ) by norm_num]
  exact coverp0010111101101
theorem coverp001011110110 : Covers (-1515761639/2000000 : ℚ) vp001011110110 := join_branches bp0010111101100 bp0010111101101
private noncomputable def vp00101111011_0 : Blocks := edgeBlocks% "full/vectors/00101111011-V-0000.bin"
noncomputable def vp00101111011 : Blocks := vp00101111011_0
private theorem bp001011110110 : Branch 0 (-1515761639/4000000 : ℚ) vp00101111011 := by
  apply branch_left_normalized (c:=vp001011110110) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1515761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1515761639/2000000 : ℚ) by norm_num]
  exact coverp001011110110
private noncomputable def ep001011110111_0 : Blocks := edgeBlocks% "full/vectors/001011110111-E-0000.bin"
noncomputable def ep001011110111 : Blocks := ep001011110111_0
private theorem idp001011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101111011.list =
    C ((2:ℤ)^131) * horner X vp001011110111.list + horner X ep001011110111.list := by
  exact edge_identity (B := (2:ℤ)^272) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011110111 : Branch 1 (-1515761639/4000000 : ℚ) vp00101111011 := by
  apply branch_checked idp001011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1515761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1517761639/2000000 : ℚ) by norm_num]
  exact coverp001011110111
theorem coverp00101111011 : Covers (-1515761639/4000000 : ℚ) vp00101111011 := join_branches bp001011110110 bp001011110111
private noncomputable def vp001011110101_0 : Blocks := edgeBlocks% "full/vectors/001011110101-V-0000.bin"
noncomputable def vp001011110101 : Blocks := vp001011110101_0
theorem coverp001011110101 : Covers (-1513761639/2000000 : ℚ) vp001011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp001011110100_0 : Blocks := edgeBlocks% "full/vectors/001011110100-V-0000.bin"
noncomputable def vp001011110100 : Blocks := vp001011110100_0
theorem coverp001011110100 : Covers (-1511761639/2000000 : ℚ) vp001011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00101111010_0 : Blocks := edgeBlocks% "full/vectors/00101111010-V-0000.bin"
noncomputable def vp00101111010 : Blocks := vp00101111010_0
private theorem bp001011110100 : Branch 0 (-1511761639/4000000 : ℚ) vp00101111010 := by
  apply branch_left_normalized (c:=vp001011110100) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-1511761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1511761639/2000000 : ℚ) by norm_num]
  exact coverp001011110100
private noncomputable def ep001011110101_0 : Blocks := edgeBlocks% "full/vectors/001011110101-E-0000.bin"
noncomputable def ep001011110101 : Blocks := ep001011110101_0
private theorem idp001011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101111010.list =
    C ((2:ℤ)^132) * horner X vp001011110101.list + horner X ep001011110101.list := by
  exact edge_identity (B := (2:ℤ)^271) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011110101 : Branch 1 (-1511761639/4000000 : ℚ) vp00101111010 := by
  apply branch_checked idp001011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1511761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1513761639/2000000 : ℚ) by norm_num]
  exact coverp001011110101
theorem coverp00101111010 : Covers (-1511761639/4000000 : ℚ) vp00101111010 := join_branches bp001011110100 bp001011110101
private noncomputable def vp0010111101_0 : Blocks := edgeBlocks% "full/vectors/0010111101-V-0000.bin"
private noncomputable def vp0010111101_1 : Blocks := edgeBlocks% "full/vectors/0010111101-V-0001.bin"
noncomputable def vp0010111101 : Blocks := (Blocks.join vp0010111101_0 vp0010111101_1)
private theorem bp00101111010 : Branch 0 (-1511761639/8000000 : ℚ) vp0010111101 := by
  apply branch_left_normalized (c:=vp00101111010) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-1511761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1511761639/4000000 : ℚ) by norm_num]
  exact coverp00101111010
private noncomputable def ep00101111011_0 : Blocks := edgeBlocks% "full/vectors/00101111011-E-0000.bin"
private noncomputable def ep00101111011_1 : Blocks := edgeBlocks% "full/vectors/00101111011-E-0001.bin"
noncomputable def ep00101111011 : Blocks := (Blocks.join ep00101111011_0 ep00101111011_1)
private theorem idp00101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010111101.list =
    C ((2:ℤ)^244) * horner X vp00101111011.list + horner X ep00101111011.list := by
  exact edge_identity (B := (2:ℤ)^426) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101111011 : Branch 1 (-1511761639/8000000 : ℚ) vp0010111101 := by
  apply branch_checked idp00101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1511761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1515761639/4000000 : ℚ) by norm_num]
  exact coverp00101111011
theorem coverp0010111101 : Covers (-1511761639/8000000 : ℚ) vp0010111101 := join_branches bp00101111010 bp00101111011
private noncomputable def vp001011110011_0 : Blocks := edgeBlocks% "full/vectors/001011110011-V-0000.bin"
noncomputable def vp001011110011 : Blocks := vp001011110011_0
theorem coverp001011110011 : Covers (-1509761639/2000000 : ℚ) vp001011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111100101_0 : Blocks := edgeBlocks% "full/vectors/0010111100101-V-0000.bin"
noncomputable def vp0010111100101 : Blocks := vp0010111100101_0
theorem coverp0010111100101 : Covers (-1508761639/1000000 : ℚ) vp0010111100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111100100_0 : Blocks := edgeBlocks% "full/vectors/0010111100100-V-0000.bin"
noncomputable def vp0010111100100 : Blocks := vp0010111100100_0
theorem coverp0010111100100 : Covers (-1507761639/1000000 : ℚ) vp0010111100100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011110010_0 : Blocks := edgeBlocks% "full/vectors/001011110010-V-0000.bin"
noncomputable def vp001011110010 : Blocks := vp001011110010_0
private theorem bp0010111100100 : Branch 0 (-1507761639/2000000 : ℚ) vp001011110010 := by
  apply branch_left_normalized (c:=vp0010111100100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1507761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1507761639/1000000 : ℚ) by norm_num]
  exact coverp0010111100100
private noncomputable def ep0010111100101_0 : Blocks := edgeBlocks% "full/vectors/0010111100101-E-0000.bin"
noncomputable def ep0010111100101 : Blocks := ep0010111100101_0
private theorem idp0010111100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011110010.list =
    C ((2:ℤ)^80) * horner X vp0010111100101.list + horner X ep0010111100101.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111100101 : Branch 1 (-1507761639/2000000 : ℚ) vp001011110010 := by
  apply branch_checked idp0010111100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1507761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1508761639/1000000 : ℚ) by norm_num]
  exact coverp0010111100101
theorem coverp001011110010 : Covers (-1507761639/2000000 : ℚ) vp001011110010 := join_branches bp0010111100100 bp0010111100101
private noncomputable def vp00101111001_0 : Blocks := edgeBlocks% "full/vectors/00101111001-V-0000.bin"
noncomputable def vp00101111001 : Blocks := vp00101111001_0
private theorem bp001011110010 : Branch 0 (-1507761639/4000000 : ℚ) vp00101111001 := by
  apply branch_left_normalized (c:=vp001011110010) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-1507761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1507761639/2000000 : ℚ) by norm_num]
  exact coverp001011110010
private noncomputable def ep001011110011_0 : Blocks := edgeBlocks% "full/vectors/001011110011-E-0000.bin"
noncomputable def ep001011110011 : Blocks := ep001011110011_0
private theorem idp001011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101111001.list =
    C ((2:ℤ)^138) * horner X vp001011110011.list + horner X ep001011110011.list := by
  exact edge_identity (B := (2:ℤ)^278) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011110011 : Branch 1 (-1507761639/4000000 : ℚ) vp00101111001 := by
  apply branch_checked idp001011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1507761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1509761639/2000000 : ℚ) by norm_num]
  exact coverp001011110011
theorem coverp00101111001 : Covers (-1507761639/4000000 : ℚ) vp00101111001 := join_branches bp001011110010 bp001011110011
private noncomputable def vp0010111100011_0 : Blocks := edgeBlocks% "full/vectors/0010111100011-V-0000.bin"
noncomputable def vp0010111100011 : Blocks := vp0010111100011_0
theorem coverp0010111100011 : Covers (-1506761639/1000000 : ℚ) vp0010111100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010111100010_0 : Blocks := edgeBlocks% "full/vectors/0010111100010-V-0000.bin"
noncomputable def vp0010111100010 : Blocks := vp0010111100010_0
theorem coverp0010111100010 : Covers (-1505761639/1000000 : ℚ) vp0010111100010 := cover_leaf (by decide +kernel)
private noncomputable def vp001011110001_0 : Blocks := edgeBlocks% "full/vectors/001011110001-V-0000.bin"
noncomputable def vp001011110001 : Blocks := vp001011110001_0
private theorem bp0010111100010 : Branch 0 (-1505761639/2000000 : ℚ) vp001011110001 := by
  apply branch_left_normalized (c:=vp0010111100010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1505761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1505761639/1000000 : ℚ) by norm_num]
  exact coverp0010111100010
private noncomputable def ep0010111100011_0 : Blocks := edgeBlocks% "full/vectors/0010111100011-E-0000.bin"
noncomputable def ep0010111100011 : Blocks := ep0010111100011_0
private theorem idp0010111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011110001.list =
    C ((2:ℤ)^74) * horner X vp0010111100011.list + horner X ep0010111100011.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111100011 : Branch 1 (-1505761639/2000000 : ℚ) vp001011110001 := by
  apply branch_checked idp0010111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1505761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1506761639/1000000 : ℚ) by norm_num]
  exact coverp0010111100011
theorem coverp001011110001 : Covers (-1505761639/2000000 : ℚ) vp001011110001 := join_branches bp0010111100010 bp0010111100011
private noncomputable def vp001011110000_0 : Blocks := edgeBlocks% "full/vectors/001011110000-V-0000.bin"
noncomputable def vp001011110000 : Blocks := vp001011110000_0
theorem coverp001011110000 : Covers (-1503761639/2000000 : ℚ) vp001011110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00101111000_0 : Blocks := edgeBlocks% "full/vectors/00101111000-V-0000.bin"
noncomputable def vp00101111000 : Blocks := vp00101111000_0
private theorem bp001011110000 : Branch 0 (-1503761639/4000000 : ℚ) vp00101111000 := by
  apply branch_left_normalized (c:=vp001011110000) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1503761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1503761639/2000000 : ℚ) by norm_num]
  exact coverp001011110000
private noncomputable def ep001011110001_0 : Blocks := edgeBlocks% "full/vectors/001011110001-E-0000.bin"
noncomputable def ep001011110001 : Blocks := ep001011110001_0
private theorem idp001011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101111000.list =
    C ((2:ℤ)^128) * horner X vp001011110001.list + horner X ep001011110001.list := by
  exact edge_identity (B := (2:ℤ)^267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011110001 : Branch 1 (-1503761639/4000000 : ℚ) vp00101111000 := by
  apply branch_checked idp001011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1503761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1505761639/2000000 : ℚ) by norm_num]
  exact coverp001011110001
theorem coverp00101111000 : Covers (-1503761639/4000000 : ℚ) vp00101111000 := join_branches bp001011110000 bp001011110001
private noncomputable def vp0010111100_0 : Blocks := edgeBlocks% "full/vectors/0010111100-V-0000.bin"
private noncomputable def vp0010111100_1 : Blocks := edgeBlocks% "full/vectors/0010111100-V-0001.bin"
noncomputable def vp0010111100 : Blocks := (Blocks.join vp0010111100_0 vp0010111100_1)
private theorem bp00101111000 : Branch 0 (-1503761639/8000000 : ℚ) vp0010111100 := by
  apply branch_left_normalized (c:=vp00101111000) (k:=0) (m:=118) (by decide +kernel)
  rw [show 2*(-1503761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1503761639/4000000 : ℚ) by norm_num]
  exact coverp00101111000
private noncomputable def ep00101111001_0 : Blocks := edgeBlocks% "full/vectors/00101111001-E-0000.bin"
private noncomputable def ep00101111001_1 : Blocks := edgeBlocks% "full/vectors/00101111001-E-0001.bin"
noncomputable def ep00101111001 : Blocks := (Blocks.join ep00101111001_0 ep00101111001_1)
private theorem idp00101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010111100.list =
    C ((2:ℤ)^237) * horner X vp00101111001.list + horner X ep00101111001.list := by
  exact edge_identity (B := (2:ℤ)^423) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101111001 : Branch 1 (-1503761639/8000000 : ℚ) vp0010111100 := by
  apply branch_checked idp00101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1503761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1507761639/4000000 : ℚ) by norm_num]
  exact coverp00101111001
theorem coverp0010111100 : Covers (-1503761639/8000000 : ℚ) vp0010111100 := join_branches bp00101111000 bp00101111001
private noncomputable def vp001011110_0 : Blocks := edgeBlocks% "full/vectors/001011110-V-0000.bin"
private noncomputable def vp001011110_1 : Blocks := edgeBlocks% "full/vectors/001011110-V-0001.bin"
private noncomputable def vp001011110_2 : Blocks := edgeBlocks% "full/vectors/001011110-V-0002.bin"
private noncomputable def vp001011110_3 : Blocks := edgeBlocks% "full/vectors/001011110-V-0003.bin"
noncomputable def vp001011110 : Blocks := (Blocks.join (Blocks.join vp001011110_0 vp001011110_1) (Blocks.join vp001011110_2 vp001011110_3))
private theorem bp0010111100 : Branch 0 (-1503761639/16000000 : ℚ) vp001011110 := by
  apply branch_left_normalized (c:=vp0010111100) (k:=0) (m:=220) (by decide +kernel)
  rw [show 2*(-1503761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1503761639/8000000 : ℚ) by norm_num]
  exact coverp0010111100
private noncomputable def ep0010111101_0 : Blocks := edgeBlocks% "full/vectors/0010111101-E-0000.bin"
private noncomputable def ep0010111101_1 : Blocks := edgeBlocks% "full/vectors/0010111101-E-0001.bin"
private noncomputable def ep0010111101_2 : Blocks := edgeBlocks% "full/vectors/0010111101-E-0002.bin"
private noncomputable def ep0010111101_3 : Blocks := edgeBlocks% "full/vectors/0010111101-E-0003.bin"
noncomputable def ep0010111101 : Blocks := (Blocks.join (Blocks.join ep0010111101_0 ep0010111101_1) (Blocks.join ep0010111101_2 ep0010111101_3))
private theorem idp0010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011110.list =
    C ((2:ℤ)^467) * horner X vp0010111101.list + horner X ep0010111101.list := by
  exact edge_identity (B := (2:ℤ)^732) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111101 : Branch 1 (-1503761639/16000000 : ℚ) vp001011110 := by
  apply branch_checked idp0010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1503761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1511761639/8000000 : ℚ) by norm_num]
  exact coverp0010111101
theorem coverp001011110 : Covers (-1503761639/16000000 : ℚ) vp001011110 := join_branches bp0010111100 bp0010111101
private noncomputable def vp00101111_0 : Blocks := edgeBlocks% "full/vectors/00101111-V-0000.bin"
private noncomputable def vp00101111_1 : Blocks := edgeBlocks% "full/vectors/00101111-V-0001.bin"
private noncomputable def vp00101111_2 : Blocks := edgeBlocks% "full/vectors/00101111-V-0002.bin"
private noncomputable def vp00101111_3 : Blocks := edgeBlocks% "full/vectors/00101111-V-0003.bin"
private noncomputable def vp00101111_4 : Blocks := edgeBlocks% "full/vectors/00101111-V-0004.bin"
private noncomputable def vp00101111_5 : Blocks := edgeBlocks% "full/vectors/00101111-V-0005.bin"
private noncomputable def vp00101111_6 : Blocks := edgeBlocks% "full/vectors/00101111-V-0006.bin"
noncomputable def vp00101111 : Blocks := (Blocks.join (Blocks.join vp00101111_0 (Blocks.join vp00101111_1 vp00101111_2)) (Blocks.join (Blocks.join vp00101111_3 vp00101111_4) (Blocks.join vp00101111_5 vp00101111_6)))
private theorem bp001011110 : Branch 0 (-1503761639/32000000 : ℚ) vp00101111 := by
  apply branch_left_normalized (c:=vp001011110) (k:=0) (m:=422) (by decide +kernel)
  rw [show 2*(-1503761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1503761639/16000000 : ℚ) by norm_num]
  exact coverp001011110
private noncomputable def ep001011111_0 : Blocks := edgeBlocks% "full/vectors/001011111-E-0000.bin"
private noncomputable def ep001011111_1 : Blocks := edgeBlocks% "full/vectors/001011111-E-0001.bin"
private noncomputable def ep001011111_2 : Blocks := edgeBlocks% "full/vectors/001011111-E-0002.bin"
private noncomputable def ep001011111_3 : Blocks := edgeBlocks% "full/vectors/001011111-E-0003.bin"
private noncomputable def ep001011111_4 : Blocks := edgeBlocks% "full/vectors/001011111-E-0004.bin"
private noncomputable def ep001011111_5 : Blocks := edgeBlocks% "full/vectors/001011111-E-0005.bin"
private noncomputable def ep001011111_6 : Blocks := edgeBlocks% "full/vectors/001011111-E-0006.bin"
noncomputable def ep001011111 : Blocks := (Blocks.join (Blocks.join ep001011111_0 (Blocks.join ep001011111_1 ep001011111_2)) (Blocks.join (Blocks.join ep001011111_3 ep001011111_4) (Blocks.join ep001011111_5 ep001011111_6)))
private theorem idp001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101111.list =
    C ((2:ℤ)^907) * horner X vp001011111.list + horner X ep001011111.list := by
  exact edge_identity (B := (2:ℤ)^1345) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011111 : Branch 1 (-1503761639/32000000 : ℚ) vp00101111 := by
  apply branch_checked idp001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1503761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1519761639/16000000 : ℚ) by norm_num]
  exact coverp001011111
theorem coverp00101111 : Covers (-1503761639/32000000 : ℚ) vp00101111 := join_branches bp001011110 bp001011111
private noncomputable def vp001011101111_0 : Blocks := edgeBlocks% "full/vectors/001011101111-V-0000.bin"
noncomputable def vp001011101111 : Blocks := vp001011101111_0
theorem coverp001011101111 : Covers (-1501761639/2000000 : ℚ) vp001011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp001011101110_0 : Blocks := edgeBlocks% "full/vectors/001011101110-V-0000.bin"
noncomputable def vp001011101110 : Blocks := vp001011101110_0
theorem coverp001011101110 : Covers (-1499761639/2000000 : ℚ) vp001011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00101110111_0 : Blocks := edgeBlocks% "full/vectors/00101110111-V-0000.bin"
noncomputable def vp00101110111 : Blocks := vp00101110111_0
private theorem bp001011101110 : Branch 0 (-1499761639/4000000 : ℚ) vp00101110111 := by
  apply branch_left_normalized (c:=vp001011101110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1499761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1499761639/2000000 : ℚ) by norm_num]
  exact coverp001011101110
private noncomputable def ep001011101111_0 : Blocks := edgeBlocks% "full/vectors/001011101111-E-0000.bin"
noncomputable def ep001011101111 : Blocks := ep001011101111_0
private theorem idp001011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101110111.list =
    C ((2:ℤ)^129) * horner X vp001011101111.list + horner X ep001011101111.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011101111 : Branch 1 (-1499761639/4000000 : ℚ) vp00101110111 := by
  apply branch_checked idp001011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1499761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1501761639/2000000 : ℚ) by norm_num]
  exact coverp001011101111
theorem coverp00101110111 : Covers (-1499761639/4000000 : ℚ) vp00101110111 := join_branches bp001011101110 bp001011101111
private noncomputable def vp001011101101_0 : Blocks := edgeBlocks% "full/vectors/001011101101-V-0000.bin"
noncomputable def vp001011101101 : Blocks := vp001011101101_0
theorem coverp001011101101 : Covers (-1497761639/2000000 : ℚ) vp001011101101 := cover_leaf (by decide +kernel)
private noncomputable def vp001011101100_0 : Blocks := edgeBlocks% "full/vectors/001011101100-V-0000.bin"
noncomputable def vp001011101100 : Blocks := vp001011101100_0
theorem coverp001011101100 : Covers (-1495761639/2000000 : ℚ) vp001011101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00101110110_0 : Blocks := edgeBlocks% "full/vectors/00101110110-V-0000.bin"
noncomputable def vp00101110110 : Blocks := vp00101110110_0
private theorem bp001011101100 : Branch 0 (-1495761639/4000000 : ℚ) vp00101110110 := by
  apply branch_left_normalized (c:=vp001011101100) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1495761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1495761639/2000000 : ℚ) by norm_num]
  exact coverp001011101100
private noncomputable def ep001011101101_0 : Blocks := edgeBlocks% "full/vectors/001011101101-E-0000.bin"
noncomputable def ep001011101101 : Blocks := ep001011101101_0
private theorem idp001011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101110110.list =
    C ((2:ℤ)^130) * horner X vp001011101101.list + horner X ep001011101101.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011101101 : Branch 1 (-1495761639/4000000 : ℚ) vp00101110110 := by
  apply branch_checked idp001011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1495761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1497761639/2000000 : ℚ) by norm_num]
  exact coverp001011101101
theorem coverp00101110110 : Covers (-1495761639/4000000 : ℚ) vp00101110110 := join_branches bp001011101100 bp001011101101
private noncomputable def vp0010111011_0 : Blocks := edgeBlocks% "full/vectors/0010111011-V-0000.bin"
private noncomputable def vp0010111011_1 : Blocks := edgeBlocks% "full/vectors/0010111011-V-0001.bin"
noncomputable def vp0010111011 : Blocks := (Blocks.join vp0010111011_0 vp0010111011_1)
private theorem bp00101110110 : Branch 0 (-1495761639/8000000 : ℚ) vp0010111011 := by
  apply branch_left_normalized (c:=vp00101110110) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-1495761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1495761639/4000000 : ℚ) by norm_num]
  exact coverp00101110110
private noncomputable def ep00101110111_0 : Blocks := edgeBlocks% "full/vectors/00101110111-E-0000.bin"
private noncomputable def ep00101110111_1 : Blocks := edgeBlocks% "full/vectors/00101110111-E-0001.bin"
noncomputable def ep00101110111 : Blocks := (Blocks.join ep00101110111_0 ep00101110111_1)
private theorem idp00101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010111011.list =
    C ((2:ℤ)^242) * horner X vp00101110111.list + horner X ep00101110111.list := by
  exact edge_identity (B := (2:ℤ)^419) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101110111 : Branch 1 (-1495761639/8000000 : ℚ) vp0010111011 := by
  apply branch_checked idp00101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1495761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1499761639/4000000 : ℚ) by norm_num]
  exact coverp00101110111
theorem coverp0010111011 : Covers (-1495761639/8000000 : ℚ) vp0010111011 := join_branches bp00101110110 bp00101110111
private noncomputable def vp001011101011_0 : Blocks := edgeBlocks% "full/vectors/001011101011-V-0000.bin"
noncomputable def vp001011101011 : Blocks := vp001011101011_0
theorem coverp001011101011 : Covers (-1493761639/2000000 : ℚ) vp001011101011 := cover_leaf (by decide +kernel)
private noncomputable def vp001011101010_0 : Blocks := edgeBlocks% "full/vectors/001011101010-V-0000.bin"
noncomputable def vp001011101010 : Blocks := vp001011101010_0
theorem coverp001011101010 : Covers (-1491761639/2000000 : ℚ) vp001011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00101110101_0 : Blocks := edgeBlocks% "full/vectors/00101110101-V-0000.bin"
noncomputable def vp00101110101 : Blocks := vp00101110101_0
private theorem bp001011101010 : Branch 0 (-1491761639/4000000 : ℚ) vp00101110101 := by
  apply branch_left_normalized (c:=vp001011101010) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1491761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1491761639/2000000 : ℚ) by norm_num]
  exact coverp001011101010
private noncomputable def ep001011101011_0 : Blocks := edgeBlocks% "full/vectors/001011101011-E-0000.bin"
noncomputable def ep001011101011 : Blocks := ep001011101011_0
private theorem idp001011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101110101.list =
    C ((2:ℤ)^128) * horner X vp001011101011.list + horner X ep001011101011.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011101011 : Branch 1 (-1491761639/4000000 : ℚ) vp00101110101 := by
  apply branch_checked idp001011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1491761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1493761639/2000000 : ℚ) by norm_num]
  exact coverp001011101011
theorem coverp00101110101 : Covers (-1491761639/4000000 : ℚ) vp00101110101 := join_branches bp001011101010 bp001011101011
private noncomputable def vp001011101001_0 : Blocks := edgeBlocks% "full/vectors/001011101001-V-0000.bin"
noncomputable def vp001011101001 : Blocks := vp001011101001_0
theorem coverp001011101001 : Covers (-1489761639/2000000 : ℚ) vp001011101001 := cover_leaf (by decide +kernel)
private noncomputable def vp001011101000_0 : Blocks := edgeBlocks% "full/vectors/001011101000-V-0000.bin"
noncomputable def vp001011101000 : Blocks := vp001011101000_0
theorem coverp001011101000 : Covers (-1487761639/2000000 : ℚ) vp001011101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00101110100_0 : Blocks := edgeBlocks% "full/vectors/00101110100-V-0000.bin"
noncomputable def vp00101110100 : Blocks := vp00101110100_0
private theorem bp001011101000 : Branch 0 (-1487761639/4000000 : ℚ) vp00101110100 := by
  apply branch_left_normalized (c:=vp001011101000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1487761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1487761639/2000000 : ℚ) by norm_num]
  exact coverp001011101000
private noncomputable def ep001011101001_0 : Blocks := edgeBlocks% "full/vectors/001011101001-E-0000.bin"
noncomputable def ep001011101001 : Blocks := ep001011101001_0
private theorem idp001011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101110100.list =
    C ((2:ℤ)^129) * horner X vp001011101001.list + horner X ep001011101001.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011101001 : Branch 1 (-1487761639/4000000 : ℚ) vp00101110100 := by
  apply branch_checked idp001011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1487761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1489761639/2000000 : ℚ) by norm_num]
  exact coverp001011101001
theorem coverp00101110100 : Covers (-1487761639/4000000 : ℚ) vp00101110100 := join_branches bp001011101000 bp001011101001
private noncomputable def vp0010111010_0 : Blocks := edgeBlocks% "full/vectors/0010111010-V-0000.bin"
private noncomputable def vp0010111010_1 : Blocks := edgeBlocks% "full/vectors/0010111010-V-0001.bin"
noncomputable def vp0010111010 : Blocks := (Blocks.join vp0010111010_0 vp0010111010_1)
private theorem bp00101110100 : Branch 0 (-1487761639/8000000 : ℚ) vp0010111010 := by
  apply branch_left_normalized (c:=vp00101110100) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-1487761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1487761639/4000000 : ℚ) by norm_num]
  exact coverp00101110100
private noncomputable def ep00101110101_0 : Blocks := edgeBlocks% "full/vectors/00101110101-E-0000.bin"
private noncomputable def ep00101110101_1 : Blocks := edgeBlocks% "full/vectors/00101110101-E-0001.bin"
noncomputable def ep00101110101 : Blocks := (Blocks.join ep00101110101_0 ep00101110101_1)
private theorem idp00101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010111010.list =
    C ((2:ℤ)^242) * horner X vp00101110101.list + horner X ep00101110101.list := by
  exact edge_identity (B := (2:ℤ)^417) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101110101 : Branch 1 (-1487761639/8000000 : ℚ) vp0010111010 := by
  apply branch_checked idp00101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1487761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1491761639/4000000 : ℚ) by norm_num]
  exact coverp00101110101
theorem coverp0010111010 : Covers (-1487761639/8000000 : ℚ) vp0010111010 := join_branches bp00101110100 bp00101110101
private noncomputable def vp001011101_0 : Blocks := edgeBlocks% "full/vectors/001011101-V-0000.bin"
private noncomputable def vp001011101_1 : Blocks := edgeBlocks% "full/vectors/001011101-V-0001.bin"
private noncomputable def vp001011101_2 : Blocks := edgeBlocks% "full/vectors/001011101-V-0002.bin"
private noncomputable def vp001011101_3 : Blocks := edgeBlocks% "full/vectors/001011101-V-0003.bin"
noncomputable def vp001011101 : Blocks := (Blocks.join (Blocks.join vp001011101_0 vp001011101_1) (Blocks.join vp001011101_2 vp001011101_3))
private theorem bp0010111010 : Branch 0 (-1487761639/16000000 : ℚ) vp001011101 := by
  apply branch_left_normalized (c:=vp0010111010) (k:=0) (m:=218) (by decide +kernel)
  rw [show 2*(-1487761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1487761639/8000000 : ℚ) by norm_num]
  exact coverp0010111010
private noncomputable def ep0010111011_0 : Blocks := edgeBlocks% "full/vectors/0010111011-E-0000.bin"
private noncomputable def ep0010111011_1 : Blocks := edgeBlocks% "full/vectors/0010111011-E-0001.bin"
private noncomputable def ep0010111011_2 : Blocks := edgeBlocks% "full/vectors/0010111011-E-0002.bin"
private noncomputable def ep0010111011_3 : Blocks := edgeBlocks% "full/vectors/0010111011-E-0003.bin"
noncomputable def ep0010111011 : Blocks := (Blocks.join (Blocks.join ep0010111011_0 ep0010111011_1) (Blocks.join ep0010111011_2 ep0010111011_3))
private theorem idp0010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011101.list =
    C ((2:ℤ)^467) * horner X vp0010111011.list + horner X ep0010111011.list := by
  exact edge_identity (B := (2:ℤ)^728) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111011 : Branch 1 (-1487761639/16000000 : ℚ) vp001011101 := by
  apply branch_checked idp0010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1487761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1495761639/8000000 : ℚ) by norm_num]
  exact coverp0010111011
theorem coverp001011101 : Covers (-1487761639/16000000 : ℚ) vp001011101 := join_branches bp0010111010 bp0010111011
private noncomputable def vp001011100111_0 : Blocks := edgeBlocks% "full/vectors/001011100111-V-0000.bin"
noncomputable def vp001011100111 : Blocks := vp001011100111_0
theorem coverp001011100111 : Covers (-1485761639/2000000 : ℚ) vp001011100111 := cover_leaf (by decide +kernel)
private noncomputable def vp001011100110_0 : Blocks := edgeBlocks% "full/vectors/001011100110-V-0000.bin"
noncomputable def vp001011100110 : Blocks := vp001011100110_0
theorem coverp001011100110 : Covers (-1483761639/2000000 : ℚ) vp001011100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00101110011_0 : Blocks := edgeBlocks% "full/vectors/00101110011-V-0000.bin"
noncomputable def vp00101110011 : Blocks := vp00101110011_0
private theorem bp001011100110 : Branch 0 (-1483761639/4000000 : ℚ) vp00101110011 := by
  apply branch_left_normalized (c:=vp001011100110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1483761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1483761639/2000000 : ℚ) by norm_num]
  exact coverp001011100110
private noncomputable def ep001011100111_0 : Blocks := edgeBlocks% "full/vectors/001011100111-E-0000.bin"
noncomputable def ep001011100111 : Blocks := ep001011100111_0
private theorem idp001011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101110011.list =
    C ((2:ℤ)^130) * horner X vp001011100111.list + horner X ep001011100111.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011100111 : Branch 1 (-1483761639/4000000 : ℚ) vp00101110011 := by
  apply branch_checked idp001011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1483761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1485761639/2000000 : ℚ) by norm_num]
  exact coverp001011100111
theorem coverp00101110011 : Covers (-1483761639/4000000 : ℚ) vp00101110011 := join_branches bp001011100110 bp001011100111
private noncomputable def vp001011100101_0 : Blocks := edgeBlocks% "full/vectors/001011100101-V-0000.bin"
noncomputable def vp001011100101 : Blocks := vp001011100101_0
theorem coverp001011100101 : Covers (-1481761639/2000000 : ℚ) vp001011100101 := cover_leaf (by decide +kernel)
private noncomputable def vp001011100100_0 : Blocks := edgeBlocks% "full/vectors/001011100100-V-0000.bin"
noncomputable def vp001011100100 : Blocks := vp001011100100_0
theorem coverp001011100100 : Covers (-1479761639/2000000 : ℚ) vp001011100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00101110010_0 : Blocks := edgeBlocks% "full/vectors/00101110010-V-0000.bin"
noncomputable def vp00101110010 : Blocks := vp00101110010_0
private theorem bp001011100100 : Branch 0 (-1479761639/4000000 : ℚ) vp00101110010 := by
  apply branch_left_normalized (c:=vp001011100100) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1479761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1479761639/2000000 : ℚ) by norm_num]
  exact coverp001011100100
private noncomputable def ep001011100101_0 : Blocks := edgeBlocks% "full/vectors/001011100101-E-0000.bin"
noncomputable def ep001011100101 : Blocks := ep001011100101_0
private theorem idp001011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101110010.list =
    C ((2:ℤ)^132) * horner X vp001011100101.list + horner X ep001011100101.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011100101 : Branch 1 (-1479761639/4000000 : ℚ) vp00101110010 := by
  apply branch_checked idp001011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1479761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1481761639/2000000 : ℚ) by norm_num]
  exact coverp001011100101
theorem coverp00101110010 : Covers (-1479761639/4000000 : ℚ) vp00101110010 := join_branches bp001011100100 bp001011100101
private noncomputable def vp0010111001_0 : Blocks := edgeBlocks% "full/vectors/0010111001-V-0000.bin"
private noncomputable def vp0010111001_1 : Blocks := edgeBlocks% "full/vectors/0010111001-V-0001.bin"
noncomputable def vp0010111001 : Blocks := (Blocks.join vp0010111001_0 vp0010111001_1)
private theorem bp00101110010 : Branch 0 (-1479761639/8000000 : ℚ) vp0010111001 := by
  apply branch_left_normalized (c:=vp00101110010) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-1479761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1479761639/4000000 : ℚ) by norm_num]
  exact coverp00101110010
private noncomputable def ep00101110011_0 : Blocks := edgeBlocks% "full/vectors/00101110011-E-0000.bin"
private noncomputable def ep00101110011_1 : Blocks := edgeBlocks% "full/vectors/00101110011-E-0001.bin"
noncomputable def ep00101110011 : Blocks := (Blocks.join ep00101110011_0 ep00101110011_1)
private theorem idp00101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010111001.list =
    C ((2:ℤ)^246) * horner X vp00101110011.list + horner X ep00101110011.list := by
  exact edge_identity (B := (2:ℤ)^422) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101110011 : Branch 1 (-1479761639/8000000 : ℚ) vp0010111001 := by
  apply branch_checked idp00101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1479761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1483761639/4000000 : ℚ) by norm_num]
  exact coverp00101110011
theorem coverp0010111001 : Covers (-1479761639/8000000 : ℚ) vp0010111001 := join_branches bp00101110010 bp00101110011
private noncomputable def vp001011100011_0 : Blocks := edgeBlocks% "full/vectors/001011100011-V-0000.bin"
noncomputable def vp001011100011 : Blocks := vp001011100011_0
theorem coverp001011100011 : Covers (-1477761639/2000000 : ℚ) vp001011100011 := cover_leaf (by decide +kernel)
private noncomputable def vp001011100010_0 : Blocks := edgeBlocks% "full/vectors/001011100010-V-0000.bin"
noncomputable def vp001011100010 : Blocks := vp001011100010_0
theorem coverp001011100010 : Covers (-1475761639/2000000 : ℚ) vp001011100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00101110001_0 : Blocks := edgeBlocks% "full/vectors/00101110001-V-0000.bin"
noncomputable def vp00101110001 : Blocks := vp00101110001_0
private theorem bp001011100010 : Branch 0 (-1475761639/4000000 : ℚ) vp00101110001 := by
  apply branch_left_normalized (c:=vp001011100010) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1475761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1475761639/2000000 : ℚ) by norm_num]
  exact coverp001011100010
private noncomputable def ep001011100011_0 : Blocks := edgeBlocks% "full/vectors/001011100011-E-0000.bin"
noncomputable def ep001011100011 : Blocks := ep001011100011_0
private theorem idp001011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101110001.list =
    C ((2:ℤ)^134) * horner X vp001011100011.list + horner X ep001011100011.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011100011 : Branch 1 (-1475761639/4000000 : ℚ) vp00101110001 := by
  apply branch_checked idp001011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1475761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1477761639/2000000 : ℚ) by norm_num]
  exact coverp001011100011
theorem coverp00101110001 : Covers (-1475761639/4000000 : ℚ) vp00101110001 := join_branches bp001011100010 bp001011100011
private noncomputable def vp001011100001_0 : Blocks := edgeBlocks% "full/vectors/001011100001-V-0000.bin"
noncomputable def vp001011100001 : Blocks := vp001011100001_0
theorem coverp001011100001 : Covers (-1473761639/2000000 : ℚ) vp001011100001 := cover_leaf (by decide +kernel)
private noncomputable def vp001011100000_0 : Blocks := edgeBlocks% "full/vectors/001011100000-V-0000.bin"
noncomputable def vp001011100000 : Blocks := vp001011100000_0
theorem coverp001011100000 : Covers (-1471761639/2000000 : ℚ) vp001011100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00101110000_0 : Blocks := edgeBlocks% "full/vectors/00101110000-V-0000.bin"
noncomputable def vp00101110000 : Blocks := vp00101110000_0
private theorem bp001011100000 : Branch 0 (-1471761639/4000000 : ℚ) vp00101110000 := by
  apply branch_left_normalized (c:=vp001011100000) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-1471761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1471761639/2000000 : ℚ) by norm_num]
  exact coverp001011100000
private noncomputable def ep001011100001_0 : Blocks := edgeBlocks% "full/vectors/001011100001-E-0000.bin"
noncomputable def ep001011100001 : Blocks := ep001011100001_0
private theorem idp001011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101110000.list =
    C ((2:ℤ)^140) * horner X vp001011100001.list + horner X ep001011100001.list := by
  exact edge_identity (B := (2:ℤ)^279) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011100001 : Branch 1 (-1471761639/4000000 : ℚ) vp00101110000 := by
  apply branch_checked idp001011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1471761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1473761639/2000000 : ℚ) by norm_num]
  exact coverp001011100001
theorem coverp00101110000 : Covers (-1471761639/4000000 : ℚ) vp00101110000 := join_branches bp001011100000 bp001011100001
private noncomputable def vp0010111000_0 : Blocks := edgeBlocks% "full/vectors/0010111000-V-0000.bin"
private noncomputable def vp0010111000_1 : Blocks := edgeBlocks% "full/vectors/0010111000-V-0001.bin"
noncomputable def vp0010111000 : Blocks := (Blocks.join vp0010111000_0 vp0010111000_1)
private theorem bp00101110000 : Branch 0 (-1471761639/8000000 : ℚ) vp0010111000 := by
  apply branch_left_normalized (c:=vp00101110000) (k:=0) (m:=124) (by decide +kernel)
  rw [show 2*(-1471761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1471761639/4000000 : ℚ) by norm_num]
  exact coverp00101110000
private noncomputable def ep00101110001_0 : Blocks := edgeBlocks% "full/vectors/00101110001-E-0000.bin"
private noncomputable def ep00101110001_1 : Blocks := edgeBlocks% "full/vectors/00101110001-E-0001.bin"
noncomputable def ep00101110001 : Blocks := (Blocks.join ep00101110001_0 ep00101110001_1)
private theorem idp00101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010111000.list =
    C ((2:ℤ)^255) * horner X vp00101110001.list + horner X ep00101110001.list := by
  exact edge_identity (B := (2:ℤ)^436) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101110001 : Branch 1 (-1471761639/8000000 : ℚ) vp0010111000 := by
  apply branch_checked idp00101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1471761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1475761639/4000000 : ℚ) by norm_num]
  exact coverp00101110001
theorem coverp0010111000 : Covers (-1471761639/8000000 : ℚ) vp0010111000 := join_branches bp00101110000 bp00101110001
private noncomputable def vp001011100_0 : Blocks := edgeBlocks% "full/vectors/001011100-V-0000.bin"
private noncomputable def vp001011100_1 : Blocks := edgeBlocks% "full/vectors/001011100-V-0001.bin"
private noncomputable def vp001011100_2 : Blocks := edgeBlocks% "full/vectors/001011100-V-0002.bin"
private noncomputable def vp001011100_3 : Blocks := edgeBlocks% "full/vectors/001011100-V-0003.bin"
noncomputable def vp001011100 : Blocks := (Blocks.join (Blocks.join vp001011100_0 vp001011100_1) (Blocks.join vp001011100_2 vp001011100_3))
private theorem bp0010111000 : Branch 0 (-1471761639/16000000 : ℚ) vp001011100 := by
  apply branch_left_normalized (c:=vp0010111000) (k:=0) (m:=226) (by decide +kernel)
  rw [show 2*(-1471761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1471761639/8000000 : ℚ) by norm_num]
  exact coverp0010111000
private noncomputable def ep0010111001_0 : Blocks := edgeBlocks% "full/vectors/0010111001-E-0000.bin"
private noncomputable def ep0010111001_1 : Blocks := edgeBlocks% "full/vectors/0010111001-E-0001.bin"
private noncomputable def ep0010111001_2 : Blocks := edgeBlocks% "full/vectors/0010111001-E-0002.bin"
private noncomputable def ep0010111001_3 : Blocks := edgeBlocks% "full/vectors/0010111001-E-0003.bin"
noncomputable def ep0010111001 : Blocks := (Blocks.join (Blocks.join ep0010111001_0 ep0010111001_1) (Blocks.join ep0010111001_2 ep0010111001_3))
private theorem idp0010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011100.list =
    C ((2:ℤ)^485) * horner X vp0010111001.list + horner X ep0010111001.list := by
  exact edge_identity (B := (2:ℤ)^748) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010111001 : Branch 1 (-1471761639/16000000 : ℚ) vp001011100 := by
  apply branch_checked idp0010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1471761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1479761639/8000000 : ℚ) by norm_num]
  exact coverp0010111001
theorem coverp001011100 : Covers (-1471761639/16000000 : ℚ) vp001011100 := join_branches bp0010111000 bp0010111001
private noncomputable def vp00101110_0 : Blocks := edgeBlocks% "full/vectors/00101110-V-0000.bin"
private noncomputable def vp00101110_1 : Blocks := edgeBlocks% "full/vectors/00101110-V-0001.bin"
private noncomputable def vp00101110_2 : Blocks := edgeBlocks% "full/vectors/00101110-V-0002.bin"
private noncomputable def vp00101110_3 : Blocks := edgeBlocks% "full/vectors/00101110-V-0003.bin"
private noncomputable def vp00101110_4 : Blocks := edgeBlocks% "full/vectors/00101110-V-0004.bin"
private noncomputable def vp00101110_5 : Blocks := edgeBlocks% "full/vectors/00101110-V-0005.bin"
private noncomputable def vp00101110_6 : Blocks := edgeBlocks% "full/vectors/00101110-V-0006.bin"
noncomputable def vp00101110 : Blocks := (Blocks.join (Blocks.join vp00101110_0 (Blocks.join vp00101110_1 vp00101110_2)) (Blocks.join (Blocks.join vp00101110_3 vp00101110_4) (Blocks.join vp00101110_5 vp00101110_6)))
private theorem bp001011100 : Branch 0 (-1471761639/32000000 : ℚ) vp00101110 := by
  apply branch_left_normalized (c:=vp001011100) (k:=0) (m:=430) (by decide +kernel)
  rw [show 2*(-1471761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1471761639/16000000 : ℚ) by norm_num]
  exact coverp001011100
private noncomputable def ep001011101_0 : Blocks := edgeBlocks% "full/vectors/001011101-E-0000.bin"
private noncomputable def ep001011101_1 : Blocks := edgeBlocks% "full/vectors/001011101-E-0001.bin"
private noncomputable def ep001011101_2 : Blocks := edgeBlocks% "full/vectors/001011101-E-0002.bin"
private noncomputable def ep001011101_3 : Blocks := edgeBlocks% "full/vectors/001011101-E-0003.bin"
private noncomputable def ep001011101_4 : Blocks := edgeBlocks% "full/vectors/001011101-E-0004.bin"
private noncomputable def ep001011101_5 : Blocks := edgeBlocks% "full/vectors/001011101-E-0005.bin"
private noncomputable def ep001011101_6 : Blocks := edgeBlocks% "full/vectors/001011101-E-0006.bin"
noncomputable def ep001011101 : Blocks := (Blocks.join (Blocks.join ep001011101_0 (Blocks.join ep001011101_1 ep001011101_2)) (Blocks.join (Blocks.join ep001011101_3 ep001011101_4) (Blocks.join ep001011101_5 ep001011101_6)))
private theorem idp001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101110.list =
    C ((2:ℤ)^935) * horner X vp001011101.list + horner X ep001011101.list := by
  exact edge_identity (B := (2:ℤ)^1366) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011101 : Branch 1 (-1471761639/32000000 : ℚ) vp00101110 := by
  apply branch_checked idp001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1471761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1487761639/16000000 : ℚ) by norm_num]
  exact coverp001011101
theorem coverp00101110 : Covers (-1471761639/32000000 : ℚ) vp00101110 := join_branches bp001011100 bp001011101
private noncomputable def vp0010111_0 : Blocks := edgeBlocks% "full/vectors/0010111-V-0000.bin"
private noncomputable def vp0010111_1 : Blocks := edgeBlocks% "full/vectors/0010111-V-0001.bin"
private noncomputable def vp0010111_2 : Blocks := edgeBlocks% "full/vectors/0010111-V-0002.bin"
private noncomputable def vp0010111_3 : Blocks := edgeBlocks% "full/vectors/0010111-V-0003.bin"
private noncomputable def vp0010111_4 : Blocks := edgeBlocks% "full/vectors/0010111-V-0004.bin"
private noncomputable def vp0010111_5 : Blocks := edgeBlocks% "full/vectors/0010111-V-0005.bin"
private noncomputable def vp0010111_6 : Blocks := edgeBlocks% "full/vectors/0010111-V-0006.bin"
private noncomputable def vp0010111_7 : Blocks := edgeBlocks% "full/vectors/0010111-V-0007.bin"
private noncomputable def vp0010111_8 : Blocks := edgeBlocks% "full/vectors/0010111-V-0008.bin"
private noncomputable def vp0010111_9 : Blocks := edgeBlocks% "full/vectors/0010111-V-0009.bin"
private noncomputable def vp0010111_10 : Blocks := edgeBlocks% "full/vectors/0010111-V-0010.bin"
private noncomputable def vp0010111_11 : Blocks := edgeBlocks% "full/vectors/0010111-V-0011.bin"
private noncomputable def vp0010111_12 : Blocks := edgeBlocks% "full/vectors/0010111-V-0012.bin"
noncomputable def vp0010111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0010111_0 (Blocks.join vp0010111_1 vp0010111_2)) (Blocks.join vp0010111_3 (Blocks.join vp0010111_4 vp0010111_5))) (Blocks.join (Blocks.join vp0010111_6 (Blocks.join vp0010111_7 vp0010111_8)) (Blocks.join (Blocks.join vp0010111_9 vp0010111_10) (Blocks.join vp0010111_11 vp0010111_12))))
private theorem bp00101110 : Branch 0 (-1471761639/64000000 : ℚ) vp0010111 := by
  apply branch_left_normalized (c:=vp00101110) (k:=0) (m:=832) (by decide +kernel)
  rw [show 2*(-1471761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1471761639/32000000 : ℚ) by norm_num]
  exact coverp00101110
private noncomputable def ep00101111_0 : Blocks := edgeBlocks% "full/vectors/00101111-E-0000.bin"
private noncomputable def ep00101111_1 : Blocks := edgeBlocks% "full/vectors/00101111-E-0001.bin"
private noncomputable def ep00101111_2 : Blocks := edgeBlocks% "full/vectors/00101111-E-0002.bin"
private noncomputable def ep00101111_3 : Blocks := edgeBlocks% "full/vectors/00101111-E-0003.bin"
private noncomputable def ep00101111_4 : Blocks := edgeBlocks% "full/vectors/00101111-E-0004.bin"
private noncomputable def ep00101111_5 : Blocks := edgeBlocks% "full/vectors/00101111-E-0005.bin"
private noncomputable def ep00101111_6 : Blocks := edgeBlocks% "full/vectors/00101111-E-0006.bin"
private noncomputable def ep00101111_7 : Blocks := edgeBlocks% "full/vectors/00101111-E-0007.bin"
private noncomputable def ep00101111_8 : Blocks := edgeBlocks% "full/vectors/00101111-E-0008.bin"
private noncomputable def ep00101111_9 : Blocks := edgeBlocks% "full/vectors/00101111-E-0009.bin"
private noncomputable def ep00101111_10 : Blocks := edgeBlocks% "full/vectors/00101111-E-0010.bin"
private noncomputable def ep00101111_11 : Blocks := edgeBlocks% "full/vectors/00101111-E-0011.bin"
private noncomputable def ep00101111_12 : Blocks := edgeBlocks% "full/vectors/00101111-E-0012.bin"
noncomputable def ep00101111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00101111_0 (Blocks.join ep00101111_1 ep00101111_2)) (Blocks.join ep00101111_3 (Blocks.join ep00101111_4 ep00101111_5))) (Blocks.join (Blocks.join ep00101111_6 (Blocks.join ep00101111_7 ep00101111_8)) (Blocks.join (Blocks.join ep00101111_9 ep00101111_10) (Blocks.join ep00101111_11 ep00101111_12))))
private theorem idp00101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010111.list =
    C ((2:ℤ)^1813) * horner X vp00101111.list + horner X ep00101111.list := by
  exact edge_identity (B := (2:ℤ)^2586) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101111 : Branch 1 (-1471761639/64000000 : ℚ) vp0010111 := by
  apply branch_checked idp00101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1471761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1503761639/32000000 : ℚ) by norm_num]
  exact coverp00101111
theorem coverp0010111 : Covers (-1471761639/64000000 : ℚ) vp0010111 := join_branches bp00101110 bp00101111
end NextProof.EdgeFull

