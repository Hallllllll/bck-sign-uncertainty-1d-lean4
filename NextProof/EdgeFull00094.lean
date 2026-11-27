import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00093

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0010110111111_0 : Blocks := edgeBlocks% "full/vectors/0010110111111-V-0000.bin"
noncomputable def vp0010110111111 : Blocks := vp0010110111111_0
theorem coverp0010110111111 : Covers (-1470761639/1000000 : ℚ) vp0010110111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110111110_0 : Blocks := edgeBlocks% "full/vectors/0010110111110-V-0000.bin"
noncomputable def vp0010110111110 : Blocks := vp0010110111110_0
theorem coverp0010110111110 : Covers (-1469761639/1000000 : ℚ) vp0010110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp001011011111_0 : Blocks := edgeBlocks% "full/vectors/001011011111-V-0000.bin"
noncomputable def vp001011011111 : Blocks := vp001011011111_0
private theorem bp0010110111110 : Branch 0 (-1469761639/2000000 : ℚ) vp001011011111 := by
  apply branch_left_normalized (c:=vp0010110111110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1469761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1469761639/1000000 : ℚ) by norm_num]
  exact coverp0010110111110
private noncomputable def ep0010110111111_0 : Blocks := edgeBlocks% "full/vectors/0010110111111-E-0000.bin"
noncomputable def ep0010110111111 : Blocks := ep0010110111111_0
private theorem idp0010110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011011111.list =
    C ((2:ℤ)^77) * horner X vp0010110111111.list + horner X ep0010110111111.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110111111 : Branch 1 (-1469761639/2000000 : ℚ) vp001011011111 := by
  apply branch_checked idp0010110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1469761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1470761639/1000000 : ℚ) by norm_num]
  exact coverp0010110111111
theorem coverp001011011111 : Covers (-1469761639/2000000 : ℚ) vp001011011111 := join_branches bp0010110111110 bp0010110111111
private noncomputable def vp0010110111101_0 : Blocks := edgeBlocks% "full/vectors/0010110111101-V-0000.bin"
noncomputable def vp0010110111101 : Blocks := vp0010110111101_0
theorem coverp0010110111101 : Covers (-1468761639/1000000 : ℚ) vp0010110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110111100_0 : Blocks := edgeBlocks% "full/vectors/0010110111100-V-0000.bin"
noncomputable def vp0010110111100 : Blocks := vp0010110111100_0
theorem coverp0010110111100 : Covers (-1467761639/1000000 : ℚ) vp0010110111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011011110_0 : Blocks := edgeBlocks% "full/vectors/001011011110-V-0000.bin"
noncomputable def vp001011011110 : Blocks := vp001011011110_0
private theorem bp0010110111100 : Branch 0 (-1467761639/2000000 : ℚ) vp001011011110 := by
  apply branch_left_normalized (c:=vp0010110111100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1467761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1467761639/1000000 : ℚ) by norm_num]
  exact coverp0010110111100
private noncomputable def ep0010110111101_0 : Blocks := edgeBlocks% "full/vectors/0010110111101-E-0000.bin"
noncomputable def ep0010110111101 : Blocks := ep0010110111101_0
private theorem idp0010110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011011110.list =
    C ((2:ℤ)^76) * horner X vp0010110111101.list + horner X ep0010110111101.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110111101 : Branch 1 (-1467761639/2000000 : ℚ) vp001011011110 := by
  apply branch_checked idp0010110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1467761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1468761639/1000000 : ℚ) by norm_num]
  exact coverp0010110111101
theorem coverp001011011110 : Covers (-1467761639/2000000 : ℚ) vp001011011110 := join_branches bp0010110111100 bp0010110111101
private noncomputable def vp00101101111_0 : Blocks := edgeBlocks% "full/vectors/00101101111-V-0000.bin"
noncomputable def vp00101101111 : Blocks := vp00101101111_0
private theorem bp001011011110 : Branch 0 (-1467761639/4000000 : ℚ) vp00101101111 := by
  apply branch_left_normalized (c:=vp001011011110) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-1467761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1467761639/2000000 : ℚ) by norm_num]
  exact coverp001011011110
private noncomputable def ep001011011111_0 : Blocks := edgeBlocks% "full/vectors/001011011111-E-0000.bin"
noncomputable def ep001011011111 : Blocks := ep001011011111_0
private theorem idp001011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101101111.list =
    C ((2:ℤ)^134) * horner X vp001011011111.list + horner X ep001011011111.list := by
  exact edge_identity (B := (2:ℤ)^277) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011011111 : Branch 1 (-1467761639/4000000 : ℚ) vp00101101111 := by
  apply branch_checked idp001011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1467761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1469761639/2000000 : ℚ) by norm_num]
  exact coverp001011011111
theorem coverp00101101111 : Covers (-1467761639/4000000 : ℚ) vp00101101111 := join_branches bp001011011110 bp001011011111
private noncomputable def vp0010110111011_0 : Blocks := edgeBlocks% "full/vectors/0010110111011-V-0000.bin"
noncomputable def vp0010110111011 : Blocks := vp0010110111011_0
theorem coverp0010110111011 : Covers (-1466761639/1000000 : ℚ) vp0010110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110111010_0 : Blocks := edgeBlocks% "full/vectors/0010110111010-V-0000.bin"
noncomputable def vp0010110111010 : Blocks := vp0010110111010_0
theorem coverp0010110111010 : Covers (-1465761639/1000000 : ℚ) vp0010110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001011011101_0 : Blocks := edgeBlocks% "full/vectors/001011011101-V-0000.bin"
noncomputable def vp001011011101 : Blocks := vp001011011101_0
private theorem bp0010110111010 : Branch 0 (-1465761639/2000000 : ℚ) vp001011011101 := by
  apply branch_left_normalized (c:=vp0010110111010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1465761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1465761639/1000000 : ℚ) by norm_num]
  exact coverp0010110111010
private noncomputable def ep0010110111011_0 : Blocks := edgeBlocks% "full/vectors/0010110111011-E-0000.bin"
noncomputable def ep0010110111011 : Blocks := ep0010110111011_0
private theorem idp0010110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011011101.list =
    C ((2:ℤ)^76) * horner X vp0010110111011.list + horner X ep0010110111011.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110111011 : Branch 1 (-1465761639/2000000 : ℚ) vp001011011101 := by
  apply branch_checked idp0010110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1465761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1466761639/1000000 : ℚ) by norm_num]
  exact coverp0010110111011
theorem coverp001011011101 : Covers (-1465761639/2000000 : ℚ) vp001011011101 := join_branches bp0010110111010 bp0010110111011
private noncomputable def vp0010110111001_0 : Blocks := edgeBlocks% "full/vectors/0010110111001-V-0000.bin"
noncomputable def vp0010110111001 : Blocks := vp0010110111001_0
theorem coverp0010110111001 : Covers (-1464761639/1000000 : ℚ) vp0010110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110111000_0 : Blocks := edgeBlocks% "full/vectors/0010110111000-V-0000.bin"
noncomputable def vp0010110111000 : Blocks := vp0010110111000_0
theorem coverp0010110111000 : Covers (-1463761639/1000000 : ℚ) vp0010110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp001011011100_0 : Blocks := edgeBlocks% "full/vectors/001011011100-V-0000.bin"
noncomputable def vp001011011100 : Blocks := vp001011011100_0
private theorem bp0010110111000 : Branch 0 (-1463761639/2000000 : ℚ) vp001011011100 := by
  apply branch_left_normalized (c:=vp0010110111000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-1463761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1463761639/1000000 : ℚ) by norm_num]
  exact coverp0010110111000
private noncomputable def ep0010110111001_0 : Blocks := edgeBlocks% "full/vectors/0010110111001-E-0000.bin"
noncomputable def ep0010110111001 : Blocks := ep0010110111001_0
private theorem idp0010110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011011100.list =
    C ((2:ℤ)^78) * horner X vp0010110111001.list + horner X ep0010110111001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110111001 : Branch 1 (-1463761639/2000000 : ℚ) vp001011011100 := by
  apply branch_checked idp0010110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1463761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1464761639/1000000 : ℚ) by norm_num]
  exact coverp0010110111001
theorem coverp001011011100 : Covers (-1463761639/2000000 : ℚ) vp001011011100 := join_branches bp0010110111000 bp0010110111001
private noncomputable def vp00101101110_0 : Blocks := edgeBlocks% "full/vectors/00101101110-V-0000.bin"
noncomputable def vp00101101110 : Blocks := vp00101101110_0
private theorem bp001011011100 : Branch 0 (-1463761639/4000000 : ℚ) vp00101101110 := by
  apply branch_left_normalized (c:=vp001011011100) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-1463761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1463761639/2000000 : ℚ) by norm_num]
  exact coverp001011011100
private noncomputable def ep001011011101_0 : Blocks := edgeBlocks% "full/vectors/001011011101-E-0000.bin"
noncomputable def ep001011011101 : Blocks := ep001011011101_0
private theorem idp001011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101101110.list =
    C ((2:ℤ)^136) * horner X vp001011011101.list + horner X ep001011011101.list := by
  exact edge_identity (B := (2:ℤ)^277) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011011101 : Branch 1 (-1463761639/4000000 : ℚ) vp00101101110 := by
  apply branch_checked idp001011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1463761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1465761639/2000000 : ℚ) by norm_num]
  exact coverp001011011101
theorem coverp00101101110 : Covers (-1463761639/4000000 : ℚ) vp00101101110 := join_branches bp001011011100 bp001011011101
private noncomputable def vp0010110111_0 : Blocks := edgeBlocks% "full/vectors/0010110111-V-0000.bin"
private noncomputable def vp0010110111_1 : Blocks := edgeBlocks% "full/vectors/0010110111-V-0001.bin"
noncomputable def vp0010110111 : Blocks := (Blocks.join vp0010110111_0 vp0010110111_1)
private theorem bp00101101110 : Branch 0 (-1463761639/8000000 : ℚ) vp0010110111 := by
  apply branch_left_normalized (c:=vp00101101110) (k:=0) (m:=123) (by decide +kernel)
  rw [show 2*(-1463761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1463761639/4000000 : ℚ) by norm_num]
  exact coverp00101101110
private noncomputable def ep00101101111_0 : Blocks := edgeBlocks% "full/vectors/00101101111-E-0000.bin"
private noncomputable def ep00101101111_1 : Blocks := edgeBlocks% "full/vectors/00101101111-E-0001.bin"
noncomputable def ep00101101111 : Blocks := (Blocks.join ep00101101111_0 ep00101101111_1)
private theorem idp00101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010110111.list =
    C ((2:ℤ)^250) * horner X vp00101101111.list + horner X ep00101101111.list := by
  exact edge_identity (B := (2:ℤ)^435) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101101111 : Branch 1 (-1463761639/8000000 : ℚ) vp0010110111 := by
  apply branch_checked idp00101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1463761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1467761639/4000000 : ℚ) by norm_num]
  exact coverp00101101111
theorem coverp0010110111 : Covers (-1463761639/8000000 : ℚ) vp0010110111 := join_branches bp00101101110 bp00101101111
private noncomputable def vp0010110110111_0 : Blocks := edgeBlocks% "full/vectors/0010110110111-V-0000.bin"
noncomputable def vp0010110110111 : Blocks := vp0010110110111_0
theorem coverp0010110110111 : Covers (-1462761639/1000000 : ℚ) vp0010110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110110110_0 : Blocks := edgeBlocks% "full/vectors/0010110110110-V-0000.bin"
noncomputable def vp0010110110110 : Blocks := vp0010110110110_0
theorem coverp0010110110110 : Covers (-1461761639/1000000 : ℚ) vp0010110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp001011011011_0 : Blocks := edgeBlocks% "full/vectors/001011011011-V-0000.bin"
noncomputable def vp001011011011 : Blocks := vp001011011011_0
private theorem bp0010110110110 : Branch 0 (-1461761639/2000000 : ℚ) vp001011011011 := by
  apply branch_left_normalized (c:=vp0010110110110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1461761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1461761639/1000000 : ℚ) by norm_num]
  exact coverp0010110110110
private noncomputable def ep0010110110111_0 : Blocks := edgeBlocks% "full/vectors/0010110110111-E-0000.bin"
noncomputable def ep0010110110111 : Blocks := ep0010110110111_0
private theorem idp0010110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011011011.list =
    C ((2:ℤ)^78) * horner X vp0010110110111.list + horner X ep0010110110111.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110110111 : Branch 1 (-1461761639/2000000 : ℚ) vp001011011011 := by
  apply branch_checked idp0010110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1461761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1462761639/1000000 : ℚ) by norm_num]
  exact coverp0010110110111
theorem coverp001011011011 : Covers (-1461761639/2000000 : ℚ) vp001011011011 := join_branches bp0010110110110 bp0010110110111
private noncomputable def vp0010110110101_0 : Blocks := edgeBlocks% "full/vectors/0010110110101-V-0000.bin"
noncomputable def vp0010110110101 : Blocks := vp0010110110101_0
theorem coverp0010110110101 : Covers (-1460761639/1000000 : ℚ) vp0010110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110110100_0 : Blocks := edgeBlocks% "full/vectors/0010110110100-V-0000.bin"
noncomputable def vp0010110110100 : Blocks := vp0010110110100_0
theorem coverp0010110110100 : Covers (-1459761639/1000000 : ℚ) vp0010110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011011010_0 : Blocks := edgeBlocks% "full/vectors/001011011010-V-0000.bin"
noncomputable def vp001011011010 : Blocks := vp001011011010_0
private theorem bp0010110110100 : Branch 0 (-1459761639/2000000 : ℚ) vp001011011010 := by
  apply branch_left_normalized (c:=vp0010110110100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1459761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1459761639/1000000 : ℚ) by norm_num]
  exact coverp0010110110100
private noncomputable def ep0010110110101_0 : Blocks := edgeBlocks% "full/vectors/0010110110101-E-0000.bin"
noncomputable def ep0010110110101 : Blocks := ep0010110110101_0
private theorem idp0010110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011011010.list =
    C ((2:ℤ)^79) * horner X vp0010110110101.list + horner X ep0010110110101.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110110101 : Branch 1 (-1459761639/2000000 : ℚ) vp001011011010 := by
  apply branch_checked idp0010110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1459761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1460761639/1000000 : ℚ) by norm_num]
  exact coverp0010110110101
theorem coverp001011011010 : Covers (-1459761639/2000000 : ℚ) vp001011011010 := join_branches bp0010110110100 bp0010110110101
private noncomputable def vp00101101101_0 : Blocks := edgeBlocks% "full/vectors/00101101101-V-0000.bin"
noncomputable def vp00101101101 : Blocks := vp00101101101_0
private theorem bp001011011010 : Branch 0 (-1459761639/4000000 : ℚ) vp00101101101 := by
  apply branch_left_normalized (c:=vp001011011010) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-1459761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1459761639/2000000 : ℚ) by norm_num]
  exact coverp001011011010
private noncomputable def ep001011011011_0 : Blocks := edgeBlocks% "full/vectors/001011011011-E-0000.bin"
noncomputable def ep001011011011 : Blocks := ep001011011011_0
private theorem idp001011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101101101.list =
    C ((2:ℤ)^138) * horner X vp001011011011.list + horner X ep001011011011.list := by
  exact edge_identity (B := (2:ℤ)^281) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011011011 : Branch 1 (-1459761639/4000000 : ℚ) vp00101101101 := by
  apply branch_checked idp001011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1459761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1461761639/2000000 : ℚ) by norm_num]
  exact coverp001011011011
theorem coverp00101101101 : Covers (-1459761639/4000000 : ℚ) vp00101101101 := join_branches bp001011011010 bp001011011011
private noncomputable def vp0010110110011_0 : Blocks := edgeBlocks% "full/vectors/0010110110011-V-0000.bin"
noncomputable def vp0010110110011 : Blocks := vp0010110110011_0
theorem coverp0010110110011 : Covers (-1458761639/1000000 : ℚ) vp0010110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110110010_0 : Blocks := edgeBlocks% "full/vectors/0010110110010-V-0000.bin"
noncomputable def vp0010110110010 : Blocks := vp0010110110010_0
theorem coverp0010110110010 : Covers (-1457761639/1000000 : ℚ) vp0010110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001011011001_0 : Blocks := edgeBlocks% "full/vectors/001011011001-V-0000.bin"
noncomputable def vp001011011001 : Blocks := vp001011011001_0
private theorem bp0010110110010 : Branch 0 (-1457761639/2000000 : ℚ) vp001011011001 := by
  apply branch_left_normalized (c:=vp0010110110010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1457761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1457761639/1000000 : ℚ) by norm_num]
  exact coverp0010110110010
private noncomputable def ep0010110110011_0 : Blocks := edgeBlocks% "full/vectors/0010110110011-E-0000.bin"
noncomputable def ep0010110110011 : Blocks := ep0010110110011_0
private theorem idp0010110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011011001.list =
    C ((2:ℤ)^78) * horner X vp0010110110011.list + horner X ep0010110110011.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110110011 : Branch 1 (-1457761639/2000000 : ℚ) vp001011011001 := by
  apply branch_checked idp0010110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1457761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1458761639/1000000 : ℚ) by norm_num]
  exact coverp0010110110011
theorem coverp001011011001 : Covers (-1457761639/2000000 : ℚ) vp001011011001 := join_branches bp0010110110010 bp0010110110011
private noncomputable def vp0010110110001_0 : Blocks := edgeBlocks% "full/vectors/0010110110001-V-0000.bin"
noncomputable def vp0010110110001 : Blocks := vp0010110110001_0
theorem coverp0010110110001 : Covers (-1456761639/1000000 : ℚ) vp0010110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110110000_0 : Blocks := edgeBlocks% "full/vectors/0010110110000-V-0000.bin"
noncomputable def vp0010110110000 : Blocks := vp0010110110000_0
theorem coverp0010110110000 : Covers (-1455761639/1000000 : ℚ) vp0010110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001011011000_0 : Blocks := edgeBlocks% "full/vectors/001011011000-V-0000.bin"
noncomputable def vp001011011000 : Blocks := vp001011011000_0
private theorem bp0010110110000 : Branch 0 (-1455761639/2000000 : ℚ) vp001011011000 := by
  apply branch_left_normalized (c:=vp0010110110000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1455761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1455761639/1000000 : ℚ) by norm_num]
  exact coverp0010110110000
private noncomputable def ep0010110110001_0 : Blocks := edgeBlocks% "full/vectors/0010110110001-E-0000.bin"
noncomputable def ep0010110110001 : Blocks := ep0010110110001_0
private theorem idp0010110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011011000.list =
    C ((2:ℤ)^77) * horner X vp0010110110001.list + horner X ep0010110110001.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110110001 : Branch 1 (-1455761639/2000000 : ℚ) vp001011011000 := by
  apply branch_checked idp0010110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1455761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1456761639/1000000 : ℚ) by norm_num]
  exact coverp0010110110001
theorem coverp001011011000 : Covers (-1455761639/2000000 : ℚ) vp001011011000 := join_branches bp0010110110000 bp0010110110001
private noncomputable def vp00101101100_0 : Blocks := edgeBlocks% "full/vectors/00101101100-V-0000.bin"
noncomputable def vp00101101100 : Blocks := vp00101101100_0
private theorem bp001011011000 : Branch 0 (-1455761639/4000000 : ℚ) vp00101101100 := by
  apply branch_left_normalized (c:=vp001011011000) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-1455761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1455761639/2000000 : ℚ) by norm_num]
  exact coverp001011011000
private noncomputable def ep001011011001_0 : Blocks := edgeBlocks% "full/vectors/001011011001-E-0000.bin"
noncomputable def ep001011011001 : Blocks := ep001011011001_0
private theorem idp001011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101101100.list =
    C ((2:ℤ)^136) * horner X vp001011011001.list + horner X ep001011011001.list := by
  exact edge_identity (B := (2:ℤ)^280) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011011001 : Branch 1 (-1455761639/4000000 : ℚ) vp00101101100 := by
  apply branch_checked idp001011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1455761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1457761639/2000000 : ℚ) by norm_num]
  exact coverp001011011001
theorem coverp00101101100 : Covers (-1455761639/4000000 : ℚ) vp00101101100 := join_branches bp001011011000 bp001011011001
private noncomputable def vp0010110110_0 : Blocks := edgeBlocks% "full/vectors/0010110110-V-0000.bin"
private noncomputable def vp0010110110_1 : Blocks := edgeBlocks% "full/vectors/0010110110-V-0001.bin"
noncomputable def vp0010110110 : Blocks := (Blocks.join vp0010110110_0 vp0010110110_1)
private theorem bp00101101100 : Branch 0 (-1455761639/8000000 : ℚ) vp0010110110 := by
  apply branch_left_normalized (c:=vp00101101100) (k:=0) (m:=124) (by decide +kernel)
  rw [show 2*(-1455761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1455761639/4000000 : ℚ) by norm_num]
  exact coverp00101101100
private noncomputable def ep00101101101_0 : Blocks := edgeBlocks% "full/vectors/00101101101-E-0000.bin"
private noncomputable def ep00101101101_1 : Blocks := edgeBlocks% "full/vectors/00101101101-E-0001.bin"
noncomputable def ep00101101101 : Blocks := (Blocks.join ep00101101101_0 ep00101101101_1)
private theorem idp00101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010110110.list =
    C ((2:ℤ)^251) * horner X vp00101101101.list + horner X ep00101101101.list := by
  exact edge_identity (B := (2:ℤ)^439) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101101101 : Branch 1 (-1455761639/8000000 : ℚ) vp0010110110 := by
  apply branch_checked idp00101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1455761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1459761639/4000000 : ℚ) by norm_num]
  exact coverp00101101101
theorem coverp0010110110 : Covers (-1455761639/8000000 : ℚ) vp0010110110 := join_branches bp00101101100 bp00101101101
private noncomputable def vp001011011_0 : Blocks := edgeBlocks% "full/vectors/001011011-V-0000.bin"
private noncomputable def vp001011011_1 : Blocks := edgeBlocks% "full/vectors/001011011-V-0001.bin"
private noncomputable def vp001011011_2 : Blocks := edgeBlocks% "full/vectors/001011011-V-0002.bin"
private noncomputable def vp001011011_3 : Blocks := edgeBlocks% "full/vectors/001011011-V-0003.bin"
noncomputable def vp001011011 : Blocks := (Blocks.join (Blocks.join vp001011011_0 vp001011011_1) (Blocks.join vp001011011_2 vp001011011_3))
private theorem bp0010110110 : Branch 0 (-1455761639/16000000 : ℚ) vp001011011 := by
  apply branch_left_normalized (c:=vp0010110110) (k:=0) (m:=228) (by decide +kernel)
  rw [show 2*(-1455761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1455761639/8000000 : ℚ) by norm_num]
  exact coverp0010110110
private noncomputable def ep0010110111_0 : Blocks := edgeBlocks% "full/vectors/0010110111-E-0000.bin"
private noncomputable def ep0010110111_1 : Blocks := edgeBlocks% "full/vectors/0010110111-E-0001.bin"
private noncomputable def ep0010110111_2 : Blocks := edgeBlocks% "full/vectors/0010110111-E-0002.bin"
private noncomputable def ep0010110111_3 : Blocks := edgeBlocks% "full/vectors/0010110111-E-0003.bin"
noncomputable def ep0010110111 : Blocks := (Blocks.join (Blocks.join ep0010110111_0 ep0010110111_1) (Blocks.join ep0010110111_2 ep0010110111_3))
private theorem idp0010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011011.list =
    C ((2:ℤ)^481) * horner X vp0010110111.list + horner X ep0010110111.list := by
  exact edge_identity (B := (2:ℤ)^752) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110111 : Branch 1 (-1455761639/16000000 : ℚ) vp001011011 := by
  apply branch_checked idp0010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1455761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1463761639/8000000 : ℚ) by norm_num]
  exact coverp0010110111
theorem coverp001011011 : Covers (-1455761639/16000000 : ℚ) vp001011011 := join_branches bp0010110110 bp0010110111
private noncomputable def vp0010110101111_0 : Blocks := edgeBlocks% "full/vectors/0010110101111-V-0000.bin"
noncomputable def vp0010110101111 : Blocks := vp0010110101111_0
theorem coverp0010110101111 : Covers (-1454761639/1000000 : ℚ) vp0010110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110101110_0 : Blocks := edgeBlocks% "full/vectors/0010110101110-V-0000.bin"
noncomputable def vp0010110101110 : Blocks := vp0010110101110_0
theorem coverp0010110101110 : Covers (-1453761639/1000000 : ℚ) vp0010110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp001011010111_0 : Blocks := edgeBlocks% "full/vectors/001011010111-V-0000.bin"
noncomputable def vp001011010111 : Blocks := vp001011010111_0
private theorem bp0010110101110 : Branch 0 (-1453761639/2000000 : ℚ) vp001011010111 := by
  apply branch_left_normalized (c:=vp0010110101110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1453761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1453761639/1000000 : ℚ) by norm_num]
  exact coverp0010110101110
private noncomputable def ep0010110101111_0 : Blocks := edgeBlocks% "full/vectors/0010110101111-E-0000.bin"
noncomputable def ep0010110101111 : Blocks := ep0010110101111_0
private theorem idp0010110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011010111.list =
    C ((2:ℤ)^79) * horner X vp0010110101111.list + horner X ep0010110101111.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110101111 : Branch 1 (-1453761639/2000000 : ℚ) vp001011010111 := by
  apply branch_checked idp0010110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1453761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1454761639/1000000 : ℚ) by norm_num]
  exact coverp0010110101111
theorem coverp001011010111 : Covers (-1453761639/2000000 : ℚ) vp001011010111 := join_branches bp0010110101110 bp0010110101111
private noncomputable def vp0010110101101_0 : Blocks := edgeBlocks% "full/vectors/0010110101101-V-0000.bin"
noncomputable def vp0010110101101 : Blocks := vp0010110101101_0
theorem coverp0010110101101 : Covers (-1452761639/1000000 : ℚ) vp0010110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110101100_0 : Blocks := edgeBlocks% "full/vectors/0010110101100-V-0000.bin"
noncomputable def vp0010110101100 : Blocks := vp0010110101100_0
theorem coverp0010110101100 : Covers (-1451761639/1000000 : ℚ) vp0010110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011010110_0 : Blocks := edgeBlocks% "full/vectors/001011010110-V-0000.bin"
noncomputable def vp001011010110 : Blocks := vp001011010110_0
private theorem bp0010110101100 : Branch 0 (-1451761639/2000000 : ℚ) vp001011010110 := by
  apply branch_left_normalized (c:=vp0010110101100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1451761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1451761639/1000000 : ℚ) by norm_num]
  exact coverp0010110101100
private noncomputable def ep0010110101101_0 : Blocks := edgeBlocks% "full/vectors/0010110101101-E-0000.bin"
noncomputable def ep0010110101101 : Blocks := ep0010110101101_0
private theorem idp0010110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011010110.list =
    C ((2:ℤ)^78) * horner X vp0010110101101.list + horner X ep0010110101101.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110101101 : Branch 1 (-1451761639/2000000 : ℚ) vp001011010110 := by
  apply branch_checked idp0010110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1451761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1452761639/1000000 : ℚ) by norm_num]
  exact coverp0010110101101
theorem coverp001011010110 : Covers (-1451761639/2000000 : ℚ) vp001011010110 := join_branches bp0010110101100 bp0010110101101
private noncomputable def vp00101101011_0 : Blocks := edgeBlocks% "full/vectors/00101101011-V-0000.bin"
noncomputable def vp00101101011 : Blocks := vp00101101011_0
private theorem bp001011010110 : Branch 0 (-1451761639/4000000 : ℚ) vp00101101011 := by
  apply branch_left_normalized (c:=vp001011010110) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-1451761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1451761639/2000000 : ℚ) by norm_num]
  exact coverp001011010110
private noncomputable def ep001011010111_0 : Blocks := edgeBlocks% "full/vectors/001011010111-E-0000.bin"
noncomputable def ep001011010111 : Blocks := ep001011010111_0
private theorem idp001011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101101011.list =
    C ((2:ℤ)^138) * horner X vp001011010111.list + horner X ep001011010111.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011010111 : Branch 1 (-1451761639/4000000 : ℚ) vp00101101011 := by
  apply branch_checked idp001011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1451761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1453761639/2000000 : ℚ) by norm_num]
  exact coverp001011010111
theorem coverp00101101011 : Covers (-1451761639/4000000 : ℚ) vp00101101011 := join_branches bp001011010110 bp001011010111
private noncomputable def vp0010110101011_0 : Blocks := edgeBlocks% "full/vectors/0010110101011-V-0000.bin"
noncomputable def vp0010110101011 : Blocks := vp0010110101011_0
theorem coverp0010110101011 : Covers (-1450761639/1000000 : ℚ) vp0010110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110101010_0 : Blocks := edgeBlocks% "full/vectors/0010110101010-V-0000.bin"
noncomputable def vp0010110101010 : Blocks := vp0010110101010_0
theorem coverp0010110101010 : Covers (-1449761639/1000000 : ℚ) vp0010110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp001011010101_0 : Blocks := edgeBlocks% "full/vectors/001011010101-V-0000.bin"
noncomputable def vp001011010101 : Blocks := vp001011010101_0
private theorem bp0010110101010 : Branch 0 (-1449761639/2000000 : ℚ) vp001011010101 := by
  apply branch_left_normalized (c:=vp0010110101010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1449761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1449761639/1000000 : ℚ) by norm_num]
  exact coverp0010110101010
private noncomputable def ep0010110101011_0 : Blocks := edgeBlocks% "full/vectors/0010110101011-E-0000.bin"
noncomputable def ep0010110101011 : Blocks := ep0010110101011_0
private theorem idp0010110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011010101.list =
    C ((2:ℤ)^78) * horner X vp0010110101011.list + horner X ep0010110101011.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110101011 : Branch 1 (-1449761639/2000000 : ℚ) vp001011010101 := by
  apply branch_checked idp0010110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1449761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1450761639/1000000 : ℚ) by norm_num]
  exact coverp0010110101011
theorem coverp001011010101 : Covers (-1449761639/2000000 : ℚ) vp001011010101 := join_branches bp0010110101010 bp0010110101011
private noncomputable def vp0010110101001_0 : Blocks := edgeBlocks% "full/vectors/0010110101001-V-0000.bin"
noncomputable def vp0010110101001 : Blocks := vp0010110101001_0
theorem coverp0010110101001 : Covers (-1448761639/1000000 : ℚ) vp0010110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110101000_0 : Blocks := edgeBlocks% "full/vectors/0010110101000-V-0000.bin"
noncomputable def vp0010110101000 : Blocks := vp0010110101000_0
theorem coverp0010110101000 : Covers (-1447761639/1000000 : ℚ) vp0010110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp001011010100_0 : Blocks := edgeBlocks% "full/vectors/001011010100-V-0000.bin"
noncomputable def vp001011010100 : Blocks := vp001011010100_0
private theorem bp0010110101000 : Branch 0 (-1447761639/2000000 : ℚ) vp001011010100 := by
  apply branch_left_normalized (c:=vp0010110101000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1447761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1447761639/1000000 : ℚ) by norm_num]
  exact coverp0010110101000
private noncomputable def ep0010110101001_0 : Blocks := edgeBlocks% "full/vectors/0010110101001-E-0000.bin"
noncomputable def ep0010110101001 : Blocks := ep0010110101001_0
private theorem idp0010110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011010100.list =
    C ((2:ℤ)^79) * horner X vp0010110101001.list + horner X ep0010110101001.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110101001 : Branch 1 (-1447761639/2000000 : ℚ) vp001011010100 := by
  apply branch_checked idp0010110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1447761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1448761639/1000000 : ℚ) by norm_num]
  exact coverp0010110101001
theorem coverp001011010100 : Covers (-1447761639/2000000 : ℚ) vp001011010100 := join_branches bp0010110101000 bp0010110101001
private noncomputable def vp00101101010_0 : Blocks := edgeBlocks% "full/vectors/00101101010-V-0000.bin"
noncomputable def vp00101101010 : Blocks := vp00101101010_0
private theorem bp001011010100 : Branch 0 (-1447761639/4000000 : ℚ) vp00101101010 := by
  apply branch_left_normalized (c:=vp001011010100) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1447761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1447761639/2000000 : ℚ) by norm_num]
  exact coverp001011010100
private noncomputable def ep001011010101_0 : Blocks := edgeBlocks% "full/vectors/001011010101-E-0000.bin"
noncomputable def ep001011010101 : Blocks := ep001011010101_0
private theorem idp001011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101101010.list =
    C ((2:ℤ)^138) * horner X vp001011010101.list + horner X ep001011010101.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011010101 : Branch 1 (-1447761639/4000000 : ℚ) vp00101101010 := by
  apply branch_checked idp001011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1447761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1449761639/2000000 : ℚ) by norm_num]
  exact coverp001011010101
theorem coverp00101101010 : Covers (-1447761639/4000000 : ℚ) vp00101101010 := join_branches bp001011010100 bp001011010101
private noncomputable def vp0010110101_0 : Blocks := edgeBlocks% "full/vectors/0010110101-V-0000.bin"
private noncomputable def vp0010110101_1 : Blocks := edgeBlocks% "full/vectors/0010110101-V-0001.bin"
noncomputable def vp0010110101 : Blocks := (Blocks.join vp0010110101_0 vp0010110101_1)
private theorem bp00101101010 : Branch 0 (-1447761639/8000000 : ℚ) vp0010110101 := by
  apply branch_left_normalized (c:=vp00101101010) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-1447761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1447761639/4000000 : ℚ) by norm_num]
  exact coverp00101101010
private noncomputable def ep00101101011_0 : Blocks := edgeBlocks% "full/vectors/00101101011-E-0000.bin"
private noncomputable def ep00101101011_1 : Blocks := edgeBlocks% "full/vectors/00101101011-E-0001.bin"
noncomputable def ep00101101011 : Blocks := (Blocks.join ep00101101011_0 ep00101101011_1)
private theorem idp00101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010110101.list =
    C ((2:ℤ)^252) * horner X vp00101101011.list + horner X ep00101101011.list := by
  exact edge_identity (B := (2:ℤ)^440) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101101011 : Branch 1 (-1447761639/8000000 : ℚ) vp0010110101 := by
  apply branch_checked idp00101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1447761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1451761639/4000000 : ℚ) by norm_num]
  exact coverp00101101011
theorem coverp0010110101 : Covers (-1447761639/8000000 : ℚ) vp0010110101 := join_branches bp00101101010 bp00101101011
private noncomputable def vp0010110100111_0 : Blocks := edgeBlocks% "full/vectors/0010110100111-V-0000.bin"
noncomputable def vp0010110100111 : Blocks := vp0010110100111_0
theorem coverp0010110100111 : Covers (-1446761639/1000000 : ℚ) vp0010110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110100110_0 : Blocks := edgeBlocks% "full/vectors/0010110100110-V-0000.bin"
noncomputable def vp0010110100110 : Blocks := vp0010110100110_0
theorem coverp0010110100110 : Covers (-1445761639/1000000 : ℚ) vp0010110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp001011010011_0 : Blocks := edgeBlocks% "full/vectors/001011010011-V-0000.bin"
noncomputable def vp001011010011 : Blocks := vp001011010011_0
private theorem bp0010110100110 : Branch 0 (-1445761639/2000000 : ℚ) vp001011010011 := by
  apply branch_left_normalized (c:=vp0010110100110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1445761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1445761639/1000000 : ℚ) by norm_num]
  exact coverp0010110100110
private noncomputable def ep0010110100111_0 : Blocks := edgeBlocks% "full/vectors/0010110100111-E-0000.bin"
noncomputable def ep0010110100111 : Blocks := ep0010110100111_0
private theorem idp0010110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011010011.list =
    C ((2:ℤ)^78) * horner X vp0010110100111.list + horner X ep0010110100111.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110100111 : Branch 1 (-1445761639/2000000 : ℚ) vp001011010011 := by
  apply branch_checked idp0010110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1445761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1446761639/1000000 : ℚ) by norm_num]
  exact coverp0010110100111
theorem coverp001011010011 : Covers (-1445761639/2000000 : ℚ) vp001011010011 := join_branches bp0010110100110 bp0010110100111
private noncomputable def vp0010110100101_0 : Blocks := edgeBlocks% "full/vectors/0010110100101-V-0000.bin"
noncomputable def vp0010110100101 : Blocks := vp0010110100101_0
theorem coverp0010110100101 : Covers (-1444761639/1000000 : ℚ) vp0010110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110100100_0 : Blocks := edgeBlocks% "full/vectors/0010110100100-V-0000.bin"
noncomputable def vp0010110100100 : Blocks := vp0010110100100_0
theorem coverp0010110100100 : Covers (-1443761639/1000000 : ℚ) vp0010110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011010010_0 : Blocks := edgeBlocks% "full/vectors/001011010010-V-0000.bin"
noncomputable def vp001011010010 : Blocks := vp001011010010_0
private theorem bp0010110100100 : Branch 0 (-1443761639/2000000 : ℚ) vp001011010010 := by
  apply branch_left_normalized (c:=vp0010110100100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1443761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1443761639/1000000 : ℚ) by norm_num]
  exact coverp0010110100100
private noncomputable def ep0010110100101_0 : Blocks := edgeBlocks% "full/vectors/0010110100101-E-0000.bin"
noncomputable def ep0010110100101 : Blocks := ep0010110100101_0
private theorem idp0010110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011010010.list =
    C ((2:ℤ)^79) * horner X vp0010110100101.list + horner X ep0010110100101.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110100101 : Branch 1 (-1443761639/2000000 : ℚ) vp001011010010 := by
  apply branch_checked idp0010110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1443761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1444761639/1000000 : ℚ) by norm_num]
  exact coverp0010110100101
theorem coverp001011010010 : Covers (-1443761639/2000000 : ℚ) vp001011010010 := join_branches bp0010110100100 bp0010110100101
private noncomputable def vp00101101001_0 : Blocks := edgeBlocks% "full/vectors/00101101001-V-0000.bin"
noncomputable def vp00101101001 : Blocks := vp00101101001_0
private theorem bp001011010010 : Branch 0 (-1443761639/4000000 : ℚ) vp00101101001 := by
  apply branch_left_normalized (c:=vp001011010010) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1443761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1443761639/2000000 : ℚ) by norm_num]
  exact coverp001011010010
private noncomputable def ep001011010011_0 : Blocks := edgeBlocks% "full/vectors/001011010011-E-0000.bin"
noncomputable def ep001011010011 : Blocks := ep001011010011_0
private theorem idp001011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101101001.list =
    C ((2:ℤ)^138) * horner X vp001011010011.list + horner X ep001011010011.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011010011 : Branch 1 (-1443761639/4000000 : ℚ) vp00101101001 := by
  apply branch_checked idp001011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1443761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1445761639/2000000 : ℚ) by norm_num]
  exact coverp001011010011
theorem coverp00101101001 : Covers (-1443761639/4000000 : ℚ) vp00101101001 := join_branches bp001011010010 bp001011010011
private noncomputable def vp0010110100011_0 : Blocks := edgeBlocks% "full/vectors/0010110100011-V-0000.bin"
noncomputable def vp0010110100011 : Blocks := vp0010110100011_0
theorem coverp0010110100011 : Covers (-1442761639/1000000 : ℚ) vp0010110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110100010_0 : Blocks := edgeBlocks% "full/vectors/0010110100010-V-0000.bin"
noncomputable def vp0010110100010 : Blocks := vp0010110100010_0
theorem coverp0010110100010 : Covers (-1441761639/1000000 : ℚ) vp0010110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp001011010001_0 : Blocks := edgeBlocks% "full/vectors/001011010001-V-0000.bin"
noncomputable def vp001011010001 : Blocks := vp001011010001_0
private theorem bp0010110100010 : Branch 0 (-1441761639/2000000 : ℚ) vp001011010001 := by
  apply branch_left_normalized (c:=vp0010110100010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1441761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1441761639/1000000 : ℚ) by norm_num]
  exact coverp0010110100010
private noncomputable def ep0010110100011_0 : Blocks := edgeBlocks% "full/vectors/0010110100011-E-0000.bin"
noncomputable def ep0010110100011 : Blocks := ep0010110100011_0
private theorem idp0010110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011010001.list =
    C ((2:ℤ)^78) * horner X vp0010110100011.list + horner X ep0010110100011.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110100011 : Branch 1 (-1441761639/2000000 : ℚ) vp001011010001 := by
  apply branch_checked idp0010110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1441761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1442761639/1000000 : ℚ) by norm_num]
  exact coverp0010110100011
theorem coverp001011010001 : Covers (-1441761639/2000000 : ℚ) vp001011010001 := join_branches bp0010110100010 bp0010110100011
private noncomputable def vp0010110100001_0 : Blocks := edgeBlocks% "full/vectors/0010110100001-V-0000.bin"
noncomputable def vp0010110100001 : Blocks := vp0010110100001_0
theorem coverp0010110100001 : Covers (-1440761639/1000000 : ℚ) vp0010110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110100000_0 : Blocks := edgeBlocks% "full/vectors/0010110100000-V-0000.bin"
noncomputable def vp0010110100000 : Blocks := vp0010110100000_0
theorem coverp0010110100000 : Covers (-1439761639/1000000 : ℚ) vp0010110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp001011010000_0 : Blocks := edgeBlocks% "full/vectors/001011010000-V-0000.bin"
noncomputable def vp001011010000 : Blocks := vp001011010000_0
private theorem bp0010110100000 : Branch 0 (-1439761639/2000000 : ℚ) vp001011010000 := by
  apply branch_left_normalized (c:=vp0010110100000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1439761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1439761639/1000000 : ℚ) by norm_num]
  exact coverp0010110100000
private noncomputable def ep0010110100001_0 : Blocks := edgeBlocks% "full/vectors/0010110100001-E-0000.bin"
noncomputable def ep0010110100001 : Blocks := ep0010110100001_0
private theorem idp0010110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011010000.list =
    C ((2:ℤ)^79) * horner X vp0010110100001.list + horner X ep0010110100001.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110100001 : Branch 1 (-1439761639/2000000 : ℚ) vp001011010000 := by
  apply branch_checked idp0010110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1439761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1440761639/1000000 : ℚ) by norm_num]
  exact coverp0010110100001
theorem coverp001011010000 : Covers (-1439761639/2000000 : ℚ) vp001011010000 := join_branches bp0010110100000 bp0010110100001
private noncomputable def vp00101101000_0 : Blocks := edgeBlocks% "full/vectors/00101101000-V-0000.bin"
noncomputable def vp00101101000 : Blocks := vp00101101000_0
private theorem bp001011010000 : Branch 0 (-1439761639/4000000 : ℚ) vp00101101000 := by
  apply branch_left_normalized (c:=vp001011010000) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1439761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1439761639/2000000 : ℚ) by norm_num]
  exact coverp001011010000
private noncomputable def ep001011010001_0 : Blocks := edgeBlocks% "full/vectors/001011010001-E-0000.bin"
noncomputable def ep001011010001 : Blocks := ep001011010001_0
private theorem idp001011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101101000.list =
    C ((2:ℤ)^138) * horner X vp001011010001.list + horner X ep001011010001.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011010001 : Branch 1 (-1439761639/4000000 : ℚ) vp00101101000 := by
  apply branch_checked idp001011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1439761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1441761639/2000000 : ℚ) by norm_num]
  exact coverp001011010001
theorem coverp00101101000 : Covers (-1439761639/4000000 : ℚ) vp00101101000 := join_branches bp001011010000 bp001011010001
private noncomputable def vp0010110100_0 : Blocks := edgeBlocks% "full/vectors/0010110100-V-0000.bin"
private noncomputable def vp0010110100_1 : Blocks := edgeBlocks% "full/vectors/0010110100-V-0001.bin"
noncomputable def vp0010110100 : Blocks := (Blocks.join vp0010110100_0 vp0010110100_1)
private theorem bp00101101000 : Branch 0 (-1439761639/8000000 : ℚ) vp0010110100 := by
  apply branch_left_normalized (c:=vp00101101000) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-1439761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1439761639/4000000 : ℚ) by norm_num]
  exact coverp00101101000
private noncomputable def ep00101101001_0 : Blocks := edgeBlocks% "full/vectors/00101101001-E-0000.bin"
private noncomputable def ep00101101001_1 : Blocks := edgeBlocks% "full/vectors/00101101001-E-0001.bin"
noncomputable def ep00101101001 : Blocks := (Blocks.join ep00101101001_0 ep00101101001_1)
private theorem idp00101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010110100.list =
    C ((2:ℤ)^253) * horner X vp00101101001.list + horner X ep00101101001.list := by
  exact edge_identity (B := (2:ℤ)^441) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101101001 : Branch 1 (-1439761639/8000000 : ℚ) vp0010110100 := by
  apply branch_checked idp00101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1439761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1443761639/4000000 : ℚ) by norm_num]
  exact coverp00101101001
theorem coverp0010110100 : Covers (-1439761639/8000000 : ℚ) vp0010110100 := join_branches bp00101101000 bp00101101001
private noncomputable def vp001011010_0 : Blocks := edgeBlocks% "full/vectors/001011010-V-0000.bin"
private noncomputable def vp001011010_1 : Blocks := edgeBlocks% "full/vectors/001011010-V-0001.bin"
private noncomputable def vp001011010_2 : Blocks := edgeBlocks% "full/vectors/001011010-V-0002.bin"
private noncomputable def vp001011010_3 : Blocks := edgeBlocks% "full/vectors/001011010-V-0003.bin"
noncomputable def vp001011010 : Blocks := (Blocks.join (Blocks.join vp001011010_0 vp001011010_1) (Blocks.join vp001011010_2 vp001011010_3))
private theorem bp0010110100 : Branch 0 (-1439761639/16000000 : ℚ) vp001011010 := by
  apply branch_left_normalized (c:=vp0010110100) (k:=0) (m:=229) (by decide +kernel)
  rw [show 2*(-1439761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1439761639/8000000 : ℚ) by norm_num]
  exact coverp0010110100
private noncomputable def ep0010110101_0 : Blocks := edgeBlocks% "full/vectors/0010110101-E-0000.bin"
private noncomputable def ep0010110101_1 : Blocks := edgeBlocks% "full/vectors/0010110101-E-0001.bin"
private noncomputable def ep0010110101_2 : Blocks := edgeBlocks% "full/vectors/0010110101-E-0002.bin"
private noncomputable def ep0010110101_3 : Blocks := edgeBlocks% "full/vectors/0010110101-E-0003.bin"
noncomputable def ep0010110101 : Blocks := (Blocks.join (Blocks.join ep0010110101_0 ep0010110101_1) (Blocks.join ep0010110101_2 ep0010110101_3))
private theorem idp0010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011010.list =
    C ((2:ℤ)^482) * horner X vp0010110101.list + horner X ep0010110101.list := by
  exact edge_identity (B := (2:ℤ)^757) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110101 : Branch 1 (-1439761639/16000000 : ℚ) vp001011010 := by
  apply branch_checked idp0010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1439761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1447761639/8000000 : ℚ) by norm_num]
  exact coverp0010110101
theorem coverp001011010 : Covers (-1439761639/16000000 : ℚ) vp001011010 := join_branches bp0010110100 bp0010110101
private noncomputable def vp00101101_0 : Blocks := edgeBlocks% "full/vectors/00101101-V-0000.bin"
private noncomputable def vp00101101_1 : Blocks := edgeBlocks% "full/vectors/00101101-V-0001.bin"
private noncomputable def vp00101101_2 : Blocks := edgeBlocks% "full/vectors/00101101-V-0002.bin"
private noncomputable def vp00101101_3 : Blocks := edgeBlocks% "full/vectors/00101101-V-0003.bin"
private noncomputable def vp00101101_4 : Blocks := edgeBlocks% "full/vectors/00101101-V-0004.bin"
private noncomputable def vp00101101_5 : Blocks := edgeBlocks% "full/vectors/00101101-V-0005.bin"
private noncomputable def vp00101101_6 : Blocks := edgeBlocks% "full/vectors/00101101-V-0006.bin"
noncomputable def vp00101101 : Blocks := (Blocks.join (Blocks.join vp00101101_0 (Blocks.join vp00101101_1 vp00101101_2)) (Blocks.join (Blocks.join vp00101101_3 vp00101101_4) (Blocks.join vp00101101_5 vp00101101_6)))
private theorem bp001011010 : Branch 0 (-1439761639/32000000 : ℚ) vp00101101 := by
  apply branch_left_normalized (c:=vp001011010) (k:=0) (m:=435) (by decide +kernel)
  rw [show 2*(-1439761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1439761639/16000000 : ℚ) by norm_num]
  exact coverp001011010
private noncomputable def ep001011011_0 : Blocks := edgeBlocks% "full/vectors/001011011-E-0000.bin"
private noncomputable def ep001011011_1 : Blocks := edgeBlocks% "full/vectors/001011011-E-0001.bin"
private noncomputable def ep001011011_2 : Blocks := edgeBlocks% "full/vectors/001011011-E-0002.bin"
private noncomputable def ep001011011_3 : Blocks := edgeBlocks% "full/vectors/001011011-E-0003.bin"
private noncomputable def ep001011011_4 : Blocks := edgeBlocks% "full/vectors/001011011-E-0004.bin"
private noncomputable def ep001011011_5 : Blocks := edgeBlocks% "full/vectors/001011011-E-0005.bin"
private noncomputable def ep001011011_6 : Blocks := edgeBlocks% "full/vectors/001011011-E-0006.bin"
noncomputable def ep001011011 : Blocks := (Blocks.join (Blocks.join ep001011011_0 (Blocks.join ep001011011_1 ep001011011_2)) (Blocks.join (Blocks.join ep001011011_3 ep001011011_4) (Blocks.join ep001011011_5 ep001011011_6)))
private theorem idp001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101101.list =
    C ((2:ℤ)^935) * horner X vp001011011.list + horner X ep001011011.list := by
  exact edge_identity (B := (2:ℤ)^1382) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011011 : Branch 1 (-1439761639/32000000 : ℚ) vp00101101 := by
  apply branch_checked idp001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1439761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1455761639/16000000 : ℚ) by norm_num]
  exact coverp001011011
theorem coverp00101101 : Covers (-1439761639/32000000 : ℚ) vp00101101 := join_branches bp001011010 bp001011011
private noncomputable def vp0010110011111_0 : Blocks := edgeBlocks% "full/vectors/0010110011111-V-0000.bin"
noncomputable def vp0010110011111 : Blocks := vp0010110011111_0
theorem coverp0010110011111 : Covers (-1438761639/1000000 : ℚ) vp0010110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110011110_0 : Blocks := edgeBlocks% "full/vectors/0010110011110-V-0000.bin"
noncomputable def vp0010110011110 : Blocks := vp0010110011110_0
theorem coverp0010110011110 : Covers (-1437761639/1000000 : ℚ) vp0010110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp001011001111_0 : Blocks := edgeBlocks% "full/vectors/001011001111-V-0000.bin"
noncomputable def vp001011001111 : Blocks := vp001011001111_0
private theorem bp0010110011110 : Branch 0 (-1437761639/2000000 : ℚ) vp001011001111 := by
  apply branch_left_normalized (c:=vp0010110011110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1437761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1437761639/1000000 : ℚ) by norm_num]
  exact coverp0010110011110
private noncomputable def ep0010110011111_0 : Blocks := edgeBlocks% "full/vectors/0010110011111-E-0000.bin"
noncomputable def ep0010110011111 : Blocks := ep0010110011111_0
private theorem idp0010110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011001111.list =
    C ((2:ℤ)^79) * horner X vp0010110011111.list + horner X ep0010110011111.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110011111 : Branch 1 (-1437761639/2000000 : ℚ) vp001011001111 := by
  apply branch_checked idp0010110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1437761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1438761639/1000000 : ℚ) by norm_num]
  exact coverp0010110011111
theorem coverp001011001111 : Covers (-1437761639/2000000 : ℚ) vp001011001111 := join_branches bp0010110011110 bp0010110011111
private noncomputable def vp0010110011101_0 : Blocks := edgeBlocks% "full/vectors/0010110011101-V-0000.bin"
noncomputable def vp0010110011101 : Blocks := vp0010110011101_0
theorem coverp0010110011101 : Covers (-1436761639/1000000 : ℚ) vp0010110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110011100_0 : Blocks := edgeBlocks% "full/vectors/0010110011100-V-0000.bin"
noncomputable def vp0010110011100 : Blocks := vp0010110011100_0
theorem coverp0010110011100 : Covers (-1435761639/1000000 : ℚ) vp0010110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011001110_0 : Blocks := edgeBlocks% "full/vectors/001011001110-V-0000.bin"
noncomputable def vp001011001110 : Blocks := vp001011001110_0
private theorem bp0010110011100 : Branch 0 (-1435761639/2000000 : ℚ) vp001011001110 := by
  apply branch_left_normalized (c:=vp0010110011100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1435761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1435761639/1000000 : ℚ) by norm_num]
  exact coverp0010110011100
private noncomputable def ep0010110011101_0 : Blocks := edgeBlocks% "full/vectors/0010110011101-E-0000.bin"
noncomputable def ep0010110011101 : Blocks := ep0010110011101_0
private theorem idp0010110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011001110.list =
    C ((2:ℤ)^78) * horner X vp0010110011101.list + horner X ep0010110011101.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110011101 : Branch 1 (-1435761639/2000000 : ℚ) vp001011001110 := by
  apply branch_checked idp0010110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1435761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1436761639/1000000 : ℚ) by norm_num]
  exact coverp0010110011101
theorem coverp001011001110 : Covers (-1435761639/2000000 : ℚ) vp001011001110 := join_branches bp0010110011100 bp0010110011101
private noncomputable def vp00101100111_0 : Blocks := edgeBlocks% "full/vectors/00101100111-V-0000.bin"
noncomputable def vp00101100111 : Blocks := vp00101100111_0
private theorem bp001011001110 : Branch 0 (-1435761639/4000000 : ℚ) vp00101100111 := by
  apply branch_left_normalized (c:=vp001011001110) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1435761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1435761639/2000000 : ℚ) by norm_num]
  exact coverp001011001110
private noncomputable def ep001011001111_0 : Blocks := edgeBlocks% "full/vectors/001011001111-E-0000.bin"
noncomputable def ep001011001111 : Blocks := ep001011001111_0
private theorem idp001011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101100111.list =
    C ((2:ℤ)^137) * horner X vp001011001111.list + horner X ep001011001111.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011001111 : Branch 1 (-1435761639/4000000 : ℚ) vp00101100111 := by
  apply branch_checked idp001011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1435761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1437761639/2000000 : ℚ) by norm_num]
  exact coverp001011001111
theorem coverp00101100111 : Covers (-1435761639/4000000 : ℚ) vp00101100111 := join_branches bp001011001110 bp001011001111
private noncomputable def vp0010110011011_0 : Blocks := edgeBlocks% "full/vectors/0010110011011-V-0000.bin"
noncomputable def vp0010110011011 : Blocks := vp0010110011011_0
theorem coverp0010110011011 : Covers (-1434761639/1000000 : ℚ) vp0010110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110011010_0 : Blocks := edgeBlocks% "full/vectors/0010110011010-V-0000.bin"
noncomputable def vp0010110011010 : Blocks := vp0010110011010_0
theorem coverp0010110011010 : Covers (-1433761639/1000000 : ℚ) vp0010110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp001011001101_0 : Blocks := edgeBlocks% "full/vectors/001011001101-V-0000.bin"
noncomputable def vp001011001101 : Blocks := vp001011001101_0
private theorem bp0010110011010 : Branch 0 (-1433761639/2000000 : ℚ) vp001011001101 := by
  apply branch_left_normalized (c:=vp0010110011010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1433761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1433761639/1000000 : ℚ) by norm_num]
  exact coverp0010110011010
private noncomputable def ep0010110011011_0 : Blocks := edgeBlocks% "full/vectors/0010110011011-E-0000.bin"
noncomputable def ep0010110011011 : Blocks := ep0010110011011_0
private theorem idp0010110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011001101.list =
    C ((2:ℤ)^79) * horner X vp0010110011011.list + horner X ep0010110011011.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110011011 : Branch 1 (-1433761639/2000000 : ℚ) vp001011001101 := by
  apply branch_checked idp0010110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1433761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1434761639/1000000 : ℚ) by norm_num]
  exact coverp0010110011011
theorem coverp001011001101 : Covers (-1433761639/2000000 : ℚ) vp001011001101 := join_branches bp0010110011010 bp0010110011011
private noncomputable def vp0010110011001_0 : Blocks := edgeBlocks% "full/vectors/0010110011001-V-0000.bin"
noncomputable def vp0010110011001 : Blocks := vp0010110011001_0
theorem coverp0010110011001 : Covers (-1432761639/1000000 : ℚ) vp0010110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110011000_0 : Blocks := edgeBlocks% "full/vectors/0010110011000-V-0000.bin"
noncomputable def vp0010110011000 : Blocks := vp0010110011000_0
theorem coverp0010110011000 : Covers (-1431761639/1000000 : ℚ) vp0010110011000 := cover_leaf (by decide +kernel)
private noncomputable def vp001011001100_0 : Blocks := edgeBlocks% "full/vectors/001011001100-V-0000.bin"
noncomputable def vp001011001100 : Blocks := vp001011001100_0
private theorem bp0010110011000 : Branch 0 (-1431761639/2000000 : ℚ) vp001011001100 := by
  apply branch_left_normalized (c:=vp0010110011000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1431761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1431761639/1000000 : ℚ) by norm_num]
  exact coverp0010110011000
private noncomputable def ep0010110011001_0 : Blocks := edgeBlocks% "full/vectors/0010110011001-E-0000.bin"
noncomputable def ep0010110011001 : Blocks := ep0010110011001_0
private theorem idp0010110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011001100.list =
    C ((2:ℤ)^79) * horner X vp0010110011001.list + horner X ep0010110011001.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110011001 : Branch 1 (-1431761639/2000000 : ℚ) vp001011001100 := by
  apply branch_checked idp0010110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1431761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1432761639/1000000 : ℚ) by norm_num]
  exact coverp0010110011001
theorem coverp001011001100 : Covers (-1431761639/2000000 : ℚ) vp001011001100 := join_branches bp0010110011000 bp0010110011001
private noncomputable def vp00101100110_0 : Blocks := edgeBlocks% "full/vectors/00101100110-V-0000.bin"
noncomputable def vp00101100110 : Blocks := vp00101100110_0
private theorem bp001011001100 : Branch 0 (-1431761639/4000000 : ℚ) vp00101100110 := by
  apply branch_left_normalized (c:=vp001011001100) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1431761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1431761639/2000000 : ℚ) by norm_num]
  exact coverp001011001100
private noncomputable def ep001011001101_0 : Blocks := edgeBlocks% "full/vectors/001011001101-E-0000.bin"
noncomputable def ep001011001101 : Blocks := ep001011001101_0
private theorem idp001011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101100110.list =
    C ((2:ℤ)^137) * horner X vp001011001101.list + horner X ep001011001101.list := by
  exact edge_identity (B := (2:ℤ)^282) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011001101 : Branch 1 (-1431761639/4000000 : ℚ) vp00101100110 := by
  apply branch_checked idp001011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1431761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1433761639/2000000 : ℚ) by norm_num]
  exact coverp001011001101
theorem coverp00101100110 : Covers (-1431761639/4000000 : ℚ) vp00101100110 := join_branches bp001011001100 bp001011001101
private noncomputable def vp0010110011_0 : Blocks := edgeBlocks% "full/vectors/0010110011-V-0000.bin"
private noncomputable def vp0010110011_1 : Blocks := edgeBlocks% "full/vectors/0010110011-V-0001.bin"
noncomputable def vp0010110011 : Blocks := (Blocks.join vp0010110011_0 vp0010110011_1)
private theorem bp00101100110 : Branch 0 (-1431761639/8000000 : ℚ) vp0010110011 := by
  apply branch_left_normalized (c:=vp00101100110) (k:=0) (m:=125) (by decide +kernel)
  rw [show 2*(-1431761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1431761639/4000000 : ℚ) by norm_num]
  exact coverp00101100110
private noncomputable def ep00101100111_0 : Blocks := edgeBlocks% "full/vectors/00101100111-E-0000.bin"
private noncomputable def ep00101100111_1 : Blocks := edgeBlocks% "full/vectors/00101100111-E-0001.bin"
noncomputable def ep00101100111 : Blocks := (Blocks.join ep00101100111_0 ep00101100111_1)
private theorem idp00101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010110011.list =
    C ((2:ℤ)^254) * horner X vp00101100111.list + horner X ep00101100111.list := by
  exact edge_identity (B := (2:ℤ)^442) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101100111 : Branch 1 (-1431761639/8000000 : ℚ) vp0010110011 := by
  apply branch_checked idp00101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1431761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1435761639/4000000 : ℚ) by norm_num]
  exact coverp00101100111
theorem coverp0010110011 : Covers (-1431761639/8000000 : ℚ) vp0010110011 := join_branches bp00101100110 bp00101100111
private noncomputable def vp0010110010111_0 : Blocks := edgeBlocks% "full/vectors/0010110010111-V-0000.bin"
noncomputable def vp0010110010111 : Blocks := vp0010110010111_0
theorem coverp0010110010111 : Covers (-1430761639/1000000 : ℚ) vp0010110010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110010110_0 : Blocks := edgeBlocks% "full/vectors/0010110010110-V-0000.bin"
noncomputable def vp0010110010110 : Blocks := vp0010110010110_0
theorem coverp0010110010110 : Covers (-1429761639/1000000 : ℚ) vp0010110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp001011001011_0 : Blocks := edgeBlocks% "full/vectors/001011001011-V-0000.bin"
noncomputable def vp001011001011 : Blocks := vp001011001011_0
private theorem bp0010110010110 : Branch 0 (-1429761639/2000000 : ℚ) vp001011001011 := by
  apply branch_left_normalized (c:=vp0010110010110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1429761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1429761639/1000000 : ℚ) by norm_num]
  exact coverp0010110010110
private noncomputable def ep0010110010111_0 : Blocks := edgeBlocks% "full/vectors/0010110010111-E-0000.bin"
noncomputable def ep0010110010111 : Blocks := ep0010110010111_0
private theorem idp0010110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011001011.list =
    C ((2:ℤ)^79) * horner X vp0010110010111.list + horner X ep0010110010111.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110010111 : Branch 1 (-1429761639/2000000 : ℚ) vp001011001011 := by
  apply branch_checked idp0010110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1429761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1430761639/1000000 : ℚ) by norm_num]
  exact coverp0010110010111
theorem coverp001011001011 : Covers (-1429761639/2000000 : ℚ) vp001011001011 := join_branches bp0010110010110 bp0010110010111
private noncomputable def vp0010110010101_0 : Blocks := edgeBlocks% "full/vectors/0010110010101-V-0000.bin"
noncomputable def vp0010110010101 : Blocks := vp0010110010101_0
theorem coverp0010110010101 : Covers (-1428761639/1000000 : ℚ) vp0010110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110010100_0 : Blocks := edgeBlocks% "full/vectors/0010110010100-V-0000.bin"
noncomputable def vp0010110010100 : Blocks := vp0010110010100_0
theorem coverp0010110010100 : Covers (-1427761639/1000000 : ℚ) vp0010110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011001010_0 : Blocks := edgeBlocks% "full/vectors/001011001010-V-0000.bin"
noncomputable def vp001011001010 : Blocks := vp001011001010_0
private theorem bp0010110010100 : Branch 0 (-1427761639/2000000 : ℚ) vp001011001010 := by
  apply branch_left_normalized (c:=vp0010110010100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1427761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1427761639/1000000 : ℚ) by norm_num]
  exact coverp0010110010100
private noncomputable def ep0010110010101_0 : Blocks := edgeBlocks% "full/vectors/0010110010101-E-0000.bin"
noncomputable def ep0010110010101 : Blocks := ep0010110010101_0
private theorem idp0010110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011001010.list =
    C ((2:ℤ)^79) * horner X vp0010110010101.list + horner X ep0010110010101.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110010101 : Branch 1 (-1427761639/2000000 : ℚ) vp001011001010 := by
  apply branch_checked idp0010110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1427761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1428761639/1000000 : ℚ) by norm_num]
  exact coverp0010110010101
theorem coverp001011001010 : Covers (-1427761639/2000000 : ℚ) vp001011001010 := join_branches bp0010110010100 bp0010110010101
private noncomputable def vp00101100101_0 : Blocks := edgeBlocks% "full/vectors/00101100101-V-0000.bin"
noncomputable def vp00101100101 : Blocks := vp00101100101_0
private theorem bp001011001010 : Branch 0 (-1427761639/4000000 : ℚ) vp00101100101 := by
  apply branch_left_normalized (c:=vp001011001010) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-1427761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1427761639/2000000 : ℚ) by norm_num]
  exact coverp001011001010
private noncomputable def ep001011001011_0 : Blocks := edgeBlocks% "full/vectors/001011001011-E-0000.bin"
noncomputable def ep001011001011 : Blocks := ep001011001011_0
private theorem idp001011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101100101.list =
    C ((2:ℤ)^138) * horner X vp001011001011.list + horner X ep001011001011.list := by
  exact edge_identity (B := (2:ℤ)^283) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011001011 : Branch 1 (-1427761639/4000000 : ℚ) vp00101100101 := by
  apply branch_checked idp001011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1427761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1429761639/2000000 : ℚ) by norm_num]
  exact coverp001011001011
theorem coverp00101100101 : Covers (-1427761639/4000000 : ℚ) vp00101100101 := join_branches bp001011001010 bp001011001011
private noncomputable def vp0010110010011_0 : Blocks := edgeBlocks% "full/vectors/0010110010011-V-0000.bin"
noncomputable def vp0010110010011 : Blocks := vp0010110010011_0
theorem coverp0010110010011 : Covers (-1426761639/1000000 : ℚ) vp0010110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110010010_0 : Blocks := edgeBlocks% "full/vectors/0010110010010-V-0000.bin"
noncomputable def vp0010110010010 : Blocks := vp0010110010010_0
theorem coverp0010110010010 : Covers (-1425761639/1000000 : ℚ) vp0010110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp001011001001_0 : Blocks := edgeBlocks% "full/vectors/001011001001-V-0000.bin"
noncomputable def vp001011001001 : Blocks := vp001011001001_0
private theorem bp0010110010010 : Branch 0 (-1425761639/2000000 : ℚ) vp001011001001 := by
  apply branch_left_normalized (c:=vp0010110010010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1425761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1425761639/1000000 : ℚ) by norm_num]
  exact coverp0010110010010
private noncomputable def ep0010110010011_0 : Blocks := edgeBlocks% "full/vectors/0010110010011-E-0000.bin"
noncomputable def ep0010110010011 : Blocks := ep0010110010011_0
private theorem idp0010110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011001001.list =
    C ((2:ℤ)^79) * horner X vp0010110010011.list + horner X ep0010110010011.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110010011 : Branch 1 (-1425761639/2000000 : ℚ) vp001011001001 := by
  apply branch_checked idp0010110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1425761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1426761639/1000000 : ℚ) by norm_num]
  exact coverp0010110010011
theorem coverp001011001001 : Covers (-1425761639/2000000 : ℚ) vp001011001001 := join_branches bp0010110010010 bp0010110010011
private noncomputable def vp0010110010001_0 : Blocks := edgeBlocks% "full/vectors/0010110010001-V-0000.bin"
noncomputable def vp0010110010001 : Blocks := vp0010110010001_0
theorem coverp0010110010001 : Covers (-1424761639/1000000 : ℚ) vp0010110010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110010000_0 : Blocks := edgeBlocks% "full/vectors/0010110010000-V-0000.bin"
noncomputable def vp0010110010000 : Blocks := vp0010110010000_0
theorem coverp0010110010000 : Covers (-1423761639/1000000 : ℚ) vp0010110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp001011001000_0 : Blocks := edgeBlocks% "full/vectors/001011001000-V-0000.bin"
noncomputable def vp001011001000 : Blocks := vp001011001000_0
private theorem bp0010110010000 : Branch 0 (-1423761639/2000000 : ℚ) vp001011001000 := by
  apply branch_left_normalized (c:=vp0010110010000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1423761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1423761639/1000000 : ℚ) by norm_num]
  exact coverp0010110010000
private noncomputable def ep0010110010001_0 : Blocks := edgeBlocks% "full/vectors/0010110010001-E-0000.bin"
noncomputable def ep0010110010001 : Blocks := ep0010110010001_0
private theorem idp0010110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011001000.list =
    C ((2:ℤ)^78) * horner X vp0010110010001.list + horner X ep0010110010001.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110010001 : Branch 1 (-1423761639/2000000 : ℚ) vp001011001000 := by
  apply branch_checked idp0010110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1423761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1424761639/1000000 : ℚ) by norm_num]
  exact coverp0010110010001
theorem coverp001011001000 : Covers (-1423761639/2000000 : ℚ) vp001011001000 := join_branches bp0010110010000 bp0010110010001
private noncomputable def vp00101100100_0 : Blocks := edgeBlocks% "full/vectors/00101100100-V-0000.bin"
noncomputable def vp00101100100 : Blocks := vp00101100100_0
private theorem bp001011001000 : Branch 0 (-1423761639/4000000 : ℚ) vp00101100100 := by
  apply branch_left_normalized (c:=vp001011001000) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1423761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1423761639/2000000 : ℚ) by norm_num]
  exact coverp001011001000
private noncomputable def ep001011001001_0 : Blocks := edgeBlocks% "full/vectors/001011001001-E-0000.bin"
noncomputable def ep001011001001 : Blocks := ep001011001001_0
private theorem idp001011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101100100.list =
    C ((2:ℤ)^138) * horner X vp001011001001.list + horner X ep001011001001.list := by
  exact edge_identity (B := (2:ℤ)^283) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011001001 : Branch 1 (-1423761639/4000000 : ℚ) vp00101100100 := by
  apply branch_checked idp001011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1423761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1425761639/2000000 : ℚ) by norm_num]
  exact coverp001011001001
theorem coverp00101100100 : Covers (-1423761639/4000000 : ℚ) vp00101100100 := join_branches bp001011001000 bp001011001001
private noncomputable def vp0010110010_0 : Blocks := edgeBlocks% "full/vectors/0010110010-V-0000.bin"
private noncomputable def vp0010110010_1 : Blocks := edgeBlocks% "full/vectors/0010110010-V-0001.bin"
noncomputable def vp0010110010 : Blocks := (Blocks.join vp0010110010_0 vp0010110010_1)
private theorem bp00101100100 : Branch 0 (-1423761639/8000000 : ℚ) vp0010110010 := by
  apply branch_left_normalized (c:=vp00101100100) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-1423761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1423761639/4000000 : ℚ) by norm_num]
  exact coverp00101100100
private noncomputable def ep00101100101_0 : Blocks := edgeBlocks% "full/vectors/00101100101-E-0000.bin"
private noncomputable def ep00101100101_1 : Blocks := edgeBlocks% "full/vectors/00101100101-E-0001.bin"
noncomputable def ep00101100101 : Blocks := (Blocks.join ep00101100101_0 ep00101100101_1)
private theorem idp00101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010110010.list =
    C ((2:ℤ)^254) * horner X vp00101100101.list + horner X ep00101100101.list := by
  exact edge_identity (B := (2:ℤ)^442) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101100101 : Branch 1 (-1423761639/8000000 : ℚ) vp0010110010 := by
  apply branch_checked idp00101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1423761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1427761639/4000000 : ℚ) by norm_num]
  exact coverp00101100101
theorem coverp0010110010 : Covers (-1423761639/8000000 : ℚ) vp0010110010 := join_branches bp00101100100 bp00101100101
private noncomputable def vp001011001_0 : Blocks := edgeBlocks% "full/vectors/001011001-V-0000.bin"
private noncomputable def vp001011001_1 : Blocks := edgeBlocks% "full/vectors/001011001-V-0001.bin"
private noncomputable def vp001011001_2 : Blocks := edgeBlocks% "full/vectors/001011001-V-0002.bin"
private noncomputable def vp001011001_3 : Blocks := edgeBlocks% "full/vectors/001011001-V-0003.bin"
noncomputable def vp001011001 : Blocks := (Blocks.join (Blocks.join vp001011001_0 vp001011001_1) (Blocks.join vp001011001_2 vp001011001_3))
private theorem bp0010110010 : Branch 0 (-1423761639/16000000 : ℚ) vp001011001 := by
  apply branch_left_normalized (c:=vp0010110010) (k:=0) (m:=230) (by decide +kernel)
  rw [show 2*(-1423761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1423761639/8000000 : ℚ) by norm_num]
  exact coverp0010110010
private noncomputable def ep0010110011_0 : Blocks := edgeBlocks% "full/vectors/0010110011-E-0000.bin"
private noncomputable def ep0010110011_1 : Blocks := edgeBlocks% "full/vectors/0010110011-E-0001.bin"
private noncomputable def ep0010110011_2 : Blocks := edgeBlocks% "full/vectors/0010110011-E-0002.bin"
private noncomputable def ep0010110011_3 : Blocks := edgeBlocks% "full/vectors/0010110011-E-0003.bin"
noncomputable def ep0010110011 : Blocks := (Blocks.join (Blocks.join ep0010110011_0 ep0010110011_1) (Blocks.join ep0010110011_2 ep0010110011_3))
private theorem idp0010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011001.list =
    C ((2:ℤ)^484) * horner X vp0010110011.list + horner X ep0010110011.list := by
  exact edge_identity (B := (2:ℤ)^760) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110011 : Branch 1 (-1423761639/16000000 : ℚ) vp001011001 := by
  apply branch_checked idp0010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1423761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1431761639/8000000 : ℚ) by norm_num]
  exact coverp0010110011
theorem coverp001011001 : Covers (-1423761639/16000000 : ℚ) vp001011001 := join_branches bp0010110010 bp0010110011
private noncomputable def vp0010110001111_0 : Blocks := edgeBlocks% "full/vectors/0010110001111-V-0000.bin"
noncomputable def vp0010110001111 : Blocks := vp0010110001111_0
theorem coverp0010110001111 : Covers (-1422761639/1000000 : ℚ) vp0010110001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110001110_0 : Blocks := edgeBlocks% "full/vectors/0010110001110-V-0000.bin"
noncomputable def vp0010110001110 : Blocks := vp0010110001110_0
theorem coverp0010110001110 : Covers (-1421761639/1000000 : ℚ) vp0010110001110 := cover_leaf (by decide +kernel)
private noncomputable def vp001011000111_0 : Blocks := edgeBlocks% "full/vectors/001011000111-V-0000.bin"
noncomputable def vp001011000111 : Blocks := vp001011000111_0
private theorem bp0010110001110 : Branch 0 (-1421761639/2000000 : ℚ) vp001011000111 := by
  apply branch_left_normalized (c:=vp0010110001110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1421761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1421761639/1000000 : ℚ) by norm_num]
  exact coverp0010110001110
private noncomputable def ep0010110001111_0 : Blocks := edgeBlocks% "full/vectors/0010110001111-E-0000.bin"
noncomputable def ep0010110001111 : Blocks := ep0010110001111_0
private theorem idp0010110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011000111.list =
    C ((2:ℤ)^78) * horner X vp0010110001111.list + horner X ep0010110001111.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110001111 : Branch 1 (-1421761639/2000000 : ℚ) vp001011000111 := by
  apply branch_checked idp0010110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1421761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1422761639/1000000 : ℚ) by norm_num]
  exact coverp0010110001111
theorem coverp001011000111 : Covers (-1421761639/2000000 : ℚ) vp001011000111 := join_branches bp0010110001110 bp0010110001111
private noncomputable def vp0010110001101_0 : Blocks := edgeBlocks% "full/vectors/0010110001101-V-0000.bin"
noncomputable def vp0010110001101 : Blocks := vp0010110001101_0
theorem coverp0010110001101 : Covers (-1420761639/1000000 : ℚ) vp0010110001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110001100_0 : Blocks := edgeBlocks% "full/vectors/0010110001100-V-0000.bin"
noncomputable def vp0010110001100 : Blocks := vp0010110001100_0
theorem coverp0010110001100 : Covers (-1419761639/1000000 : ℚ) vp0010110001100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011000110_0 : Blocks := edgeBlocks% "full/vectors/001011000110-V-0000.bin"
noncomputable def vp001011000110 : Blocks := vp001011000110_0
private theorem bp0010110001100 : Branch 0 (-1419761639/2000000 : ℚ) vp001011000110 := by
  apply branch_left_normalized (c:=vp0010110001100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1419761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1419761639/1000000 : ℚ) by norm_num]
  exact coverp0010110001100
private noncomputable def ep0010110001101_0 : Blocks := edgeBlocks% "full/vectors/0010110001101-E-0000.bin"
noncomputable def ep0010110001101 : Blocks := ep0010110001101_0
private theorem idp0010110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011000110.list =
    C ((2:ℤ)^79) * horner X vp0010110001101.list + horner X ep0010110001101.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110001101 : Branch 1 (-1419761639/2000000 : ℚ) vp001011000110 := by
  apply branch_checked idp0010110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1419761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1420761639/1000000 : ℚ) by norm_num]
  exact coverp0010110001101
theorem coverp001011000110 : Covers (-1419761639/2000000 : ℚ) vp001011000110 := join_branches bp0010110001100 bp0010110001101
private noncomputable def vp00101100011_0 : Blocks := edgeBlocks% "full/vectors/00101100011-V-0000.bin"
noncomputable def vp00101100011 : Blocks := vp00101100011_0
private theorem bp001011000110 : Branch 0 (-1419761639/4000000 : ℚ) vp00101100011 := by
  apply branch_left_normalized (c:=vp001011000110) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1419761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1419761639/2000000 : ℚ) by norm_num]
  exact coverp001011000110
private noncomputable def ep001011000111_0 : Blocks := edgeBlocks% "full/vectors/001011000111-E-0000.bin"
noncomputable def ep001011000111 : Blocks := ep001011000111_0
private theorem idp001011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101100011.list =
    C ((2:ℤ)^139) * horner X vp001011000111.list + horner X ep001011000111.list := by
  exact edge_identity (B := (2:ℤ)^283) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011000111 : Branch 1 (-1419761639/4000000 : ℚ) vp00101100011 := by
  apply branch_checked idp001011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1419761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1421761639/2000000 : ℚ) by norm_num]
  exact coverp001011000111
theorem coverp00101100011 : Covers (-1419761639/4000000 : ℚ) vp00101100011 := join_branches bp001011000110 bp001011000111
private noncomputable def vp0010110001011_0 : Blocks := edgeBlocks% "full/vectors/0010110001011-V-0000.bin"
noncomputable def vp0010110001011 : Blocks := vp0010110001011_0
theorem coverp0010110001011 : Covers (-1418761639/1000000 : ℚ) vp0010110001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110001010_0 : Blocks := edgeBlocks% "full/vectors/0010110001010-V-0000.bin"
noncomputable def vp0010110001010 : Blocks := vp0010110001010_0
theorem coverp0010110001010 : Covers (-1417761639/1000000 : ℚ) vp0010110001010 := cover_leaf (by decide +kernel)
private noncomputable def vp001011000101_0 : Blocks := edgeBlocks% "full/vectors/001011000101-V-0000.bin"
noncomputable def vp001011000101 : Blocks := vp001011000101_0
private theorem bp0010110001010 : Branch 0 (-1417761639/2000000 : ℚ) vp001011000101 := by
  apply branch_left_normalized (c:=vp0010110001010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1417761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1417761639/1000000 : ℚ) by norm_num]
  exact coverp0010110001010
private noncomputable def ep0010110001011_0 : Blocks := edgeBlocks% "full/vectors/0010110001011-E-0000.bin"
noncomputable def ep0010110001011 : Blocks := ep0010110001011_0
private theorem idp0010110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011000101.list =
    C ((2:ℤ)^80) * horner X vp0010110001011.list + horner X ep0010110001011.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110001011 : Branch 1 (-1417761639/2000000 : ℚ) vp001011000101 := by
  apply branch_checked idp0010110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1417761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1418761639/1000000 : ℚ) by norm_num]
  exact coverp0010110001011
theorem coverp001011000101 : Covers (-1417761639/2000000 : ℚ) vp001011000101 := join_branches bp0010110001010 bp0010110001011
private noncomputable def vp0010110001001_0 : Blocks := edgeBlocks% "full/vectors/0010110001001-V-0000.bin"
noncomputable def vp0010110001001 : Blocks := vp0010110001001_0
theorem coverp0010110001001 : Covers (-1416761639/1000000 : ℚ) vp0010110001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110001000_0 : Blocks := edgeBlocks% "full/vectors/0010110001000-V-0000.bin"
noncomputable def vp0010110001000 : Blocks := vp0010110001000_0
theorem coverp0010110001000 : Covers (-1415761639/1000000 : ℚ) vp0010110001000 := cover_leaf (by decide +kernel)
private noncomputable def vp001011000100_0 : Blocks := edgeBlocks% "full/vectors/001011000100-V-0000.bin"
noncomputable def vp001011000100 : Blocks := vp001011000100_0
private theorem bp0010110001000 : Branch 0 (-1415761639/2000000 : ℚ) vp001011000100 := by
  apply branch_left_normalized (c:=vp0010110001000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1415761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1415761639/1000000 : ℚ) by norm_num]
  exact coverp0010110001000
private noncomputable def ep0010110001001_0 : Blocks := edgeBlocks% "full/vectors/0010110001001-E-0000.bin"
noncomputable def ep0010110001001 : Blocks := ep0010110001001_0
private theorem idp0010110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011000100.list =
    C ((2:ℤ)^79) * horner X vp0010110001001.list + horner X ep0010110001001.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110001001 : Branch 1 (-1415761639/2000000 : ℚ) vp001011000100 := by
  apply branch_checked idp0010110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1415761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1416761639/1000000 : ℚ) by norm_num]
  exact coverp0010110001001
theorem coverp001011000100 : Covers (-1415761639/2000000 : ℚ) vp001011000100 := join_branches bp0010110001000 bp0010110001001
private noncomputable def vp00101100010_0 : Blocks := edgeBlocks% "full/vectors/00101100010-V-0000.bin"
noncomputable def vp00101100010 : Blocks := vp00101100010_0
private theorem bp001011000100 : Branch 0 (-1415761639/4000000 : ℚ) vp00101100010 := by
  apply branch_left_normalized (c:=vp001011000100) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1415761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1415761639/2000000 : ℚ) by norm_num]
  exact coverp001011000100
private noncomputable def ep001011000101_0 : Blocks := edgeBlocks% "full/vectors/001011000101-E-0000.bin"
noncomputable def ep001011000101 : Blocks := ep001011000101_0
private theorem idp001011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101100010.list =
    C ((2:ℤ)^139) * horner X vp001011000101.list + horner X ep001011000101.list := by
  exact edge_identity (B := (2:ℤ)^284) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011000101 : Branch 1 (-1415761639/4000000 : ℚ) vp00101100010 := by
  apply branch_checked idp001011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1415761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1417761639/2000000 : ℚ) by norm_num]
  exact coverp001011000101
theorem coverp00101100010 : Covers (-1415761639/4000000 : ℚ) vp00101100010 := join_branches bp001011000100 bp001011000101
private noncomputable def vp0010110001_0 : Blocks := edgeBlocks% "full/vectors/0010110001-V-0000.bin"
private noncomputable def vp0010110001_1 : Blocks := edgeBlocks% "full/vectors/0010110001-V-0001.bin"
noncomputable def vp0010110001 : Blocks := (Blocks.join vp0010110001_0 vp0010110001_1)
private theorem bp00101100010 : Branch 0 (-1415761639/8000000 : ℚ) vp0010110001 := by
  apply branch_left_normalized (c:=vp00101100010) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-1415761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1415761639/4000000 : ℚ) by norm_num]
  exact coverp00101100010
private noncomputable def ep00101100011_0 : Blocks := edgeBlocks% "full/vectors/00101100011-E-0000.bin"
private noncomputable def ep00101100011_1 : Blocks := edgeBlocks% "full/vectors/00101100011-E-0001.bin"
noncomputable def ep00101100011 : Blocks := (Blocks.join ep00101100011_0 ep00101100011_1)
private theorem idp00101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010110001.list =
    C ((2:ℤ)^256) * horner X vp00101100011.list + horner X ep00101100011.list := by
  exact edge_identity (B := (2:ℤ)^445) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101100011 : Branch 1 (-1415761639/8000000 : ℚ) vp0010110001 := by
  apply branch_checked idp00101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1415761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1419761639/4000000 : ℚ) by norm_num]
  exact coverp00101100011
theorem coverp0010110001 : Covers (-1415761639/8000000 : ℚ) vp0010110001 := join_branches bp00101100010 bp00101100011
private noncomputable def vp0010110000111_0 : Blocks := edgeBlocks% "full/vectors/0010110000111-V-0000.bin"
noncomputable def vp0010110000111 : Blocks := vp0010110000111_0
theorem coverp0010110000111 : Covers (-1414761639/1000000 : ℚ) vp0010110000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110000110_0 : Blocks := edgeBlocks% "full/vectors/0010110000110-V-0000.bin"
noncomputable def vp0010110000110 : Blocks := vp0010110000110_0
theorem coverp0010110000110 : Covers (-1413761639/1000000 : ℚ) vp0010110000110 := cover_leaf (by decide +kernel)
private noncomputable def vp001011000011_0 : Blocks := edgeBlocks% "full/vectors/001011000011-V-0000.bin"
noncomputable def vp001011000011 : Blocks := vp001011000011_0
private theorem bp0010110000110 : Branch 0 (-1413761639/2000000 : ℚ) vp001011000011 := by
  apply branch_left_normalized (c:=vp0010110000110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1413761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1413761639/1000000 : ℚ) by norm_num]
  exact coverp0010110000110
private noncomputable def ep0010110000111_0 : Blocks := edgeBlocks% "full/vectors/0010110000111-E-0000.bin"
noncomputable def ep0010110000111 : Blocks := ep0010110000111_0
private theorem idp0010110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011000011.list =
    C ((2:ℤ)^80) * horner X vp0010110000111.list + horner X ep0010110000111.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110000111 : Branch 1 (-1413761639/2000000 : ℚ) vp001011000011 := by
  apply branch_checked idp0010110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1413761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1414761639/1000000 : ℚ) by norm_num]
  exact coverp0010110000111
theorem coverp001011000011 : Covers (-1413761639/2000000 : ℚ) vp001011000011 := join_branches bp0010110000110 bp0010110000111
private noncomputable def vp0010110000101_0 : Blocks := edgeBlocks% "full/vectors/0010110000101-V-0000.bin"
noncomputable def vp0010110000101 : Blocks := vp0010110000101_0
theorem coverp0010110000101 : Covers (-1412761639/1000000 : ℚ) vp0010110000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110000100_0 : Blocks := edgeBlocks% "full/vectors/0010110000100-V-0000.bin"
noncomputable def vp0010110000100 : Blocks := vp0010110000100_0
theorem coverp0010110000100 : Covers (-1411761639/1000000 : ℚ) vp0010110000100 := cover_leaf (by decide +kernel)
private noncomputable def vp001011000010_0 : Blocks := edgeBlocks% "full/vectors/001011000010-V-0000.bin"
noncomputable def vp001011000010 : Blocks := vp001011000010_0
private theorem bp0010110000100 : Branch 0 (-1411761639/2000000 : ℚ) vp001011000010 := by
  apply branch_left_normalized (c:=vp0010110000100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1411761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1411761639/1000000 : ℚ) by norm_num]
  exact coverp0010110000100
private noncomputable def ep0010110000101_0 : Blocks := edgeBlocks% "full/vectors/0010110000101-E-0000.bin"
noncomputable def ep0010110000101 : Blocks := ep0010110000101_0
private theorem idp0010110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011000010.list =
    C ((2:ℤ)^79) * horner X vp0010110000101.list + horner X ep0010110000101.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110000101 : Branch 1 (-1411761639/2000000 : ℚ) vp001011000010 := by
  apply branch_checked idp0010110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1411761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1412761639/1000000 : ℚ) by norm_num]
  exact coverp0010110000101
theorem coverp001011000010 : Covers (-1411761639/2000000 : ℚ) vp001011000010 := join_branches bp0010110000100 bp0010110000101
private noncomputable def vp00101100001_0 : Blocks := edgeBlocks% "full/vectors/00101100001-V-0000.bin"
noncomputable def vp00101100001 : Blocks := vp00101100001_0
private theorem bp001011000010 : Branch 0 (-1411761639/4000000 : ℚ) vp00101100001 := by
  apply branch_left_normalized (c:=vp001011000010) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1411761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1411761639/2000000 : ℚ) by norm_num]
  exact coverp001011000010
private noncomputable def ep001011000011_0 : Blocks := edgeBlocks% "full/vectors/001011000011-E-0000.bin"
noncomputable def ep001011000011 : Blocks := ep001011000011_0
private theorem idp001011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101100001.list =
    C ((2:ℤ)^138) * horner X vp001011000011.list + horner X ep001011000011.list := by
  exact edge_identity (B := (2:ℤ)^283) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011000011 : Branch 1 (-1411761639/4000000 : ℚ) vp00101100001 := by
  apply branch_checked idp001011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1411761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1413761639/2000000 : ℚ) by norm_num]
  exact coverp001011000011
theorem coverp00101100001 : Covers (-1411761639/4000000 : ℚ) vp00101100001 := join_branches bp001011000010 bp001011000011
private noncomputable def vp0010110000011_0 : Blocks := edgeBlocks% "full/vectors/0010110000011-V-0000.bin"
noncomputable def vp0010110000011 : Blocks := vp0010110000011_0
theorem coverp0010110000011 : Covers (-1410761639/1000000 : ℚ) vp0010110000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110000010_0 : Blocks := edgeBlocks% "full/vectors/0010110000010-V-0000.bin"
noncomputable def vp0010110000010 : Blocks := vp0010110000010_0
theorem coverp0010110000010 : Covers (-1409761639/1000000 : ℚ) vp0010110000010 := cover_leaf (by decide +kernel)
private noncomputable def vp001011000001_0 : Blocks := edgeBlocks% "full/vectors/001011000001-V-0000.bin"
noncomputable def vp001011000001 : Blocks := vp001011000001_0
private theorem bp0010110000010 : Branch 0 (-1409761639/2000000 : ℚ) vp001011000001 := by
  apply branch_left_normalized (c:=vp0010110000010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1409761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1409761639/1000000 : ℚ) by norm_num]
  exact coverp0010110000010
private noncomputable def ep0010110000011_0 : Blocks := edgeBlocks% "full/vectors/0010110000011-E-0000.bin"
noncomputable def ep0010110000011 : Blocks := ep0010110000011_0
private theorem idp0010110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011000001.list =
    C ((2:ℤ)^78) * horner X vp0010110000011.list + horner X ep0010110000011.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110000011 : Branch 1 (-1409761639/2000000 : ℚ) vp001011000001 := by
  apply branch_checked idp0010110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1409761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1410761639/1000000 : ℚ) by norm_num]
  exact coverp0010110000011
theorem coverp001011000001 : Covers (-1409761639/2000000 : ℚ) vp001011000001 := join_branches bp0010110000010 bp0010110000011
private noncomputable def vp0010110000001_0 : Blocks := edgeBlocks% "full/vectors/0010110000001-V-0000.bin"
noncomputable def vp0010110000001 : Blocks := vp0010110000001_0
theorem coverp0010110000001 : Covers (-1408761639/1000000 : ℚ) vp0010110000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010110000000_0 : Blocks := edgeBlocks% "full/vectors/0010110000000-V-0000.bin"
noncomputable def vp0010110000000 : Blocks := vp0010110000000_0
theorem coverp0010110000000 : Covers (-1407761639/1000000 : ℚ) vp0010110000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001011000000_0 : Blocks := edgeBlocks% "full/vectors/001011000000-V-0000.bin"
noncomputable def vp001011000000 : Blocks := vp001011000000_0
private theorem bp0010110000000 : Branch 0 (-1407761639/2000000 : ℚ) vp001011000000 := by
  apply branch_left_normalized (c:=vp0010110000000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1407761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1407761639/1000000 : ℚ) by norm_num]
  exact coverp0010110000000
private noncomputable def ep0010110000001_0 : Blocks := edgeBlocks% "full/vectors/0010110000001-E-0000.bin"
noncomputable def ep0010110000001 : Blocks := ep0010110000001_0
private theorem idp0010110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011000000.list =
    C ((2:ℤ)^79) * horner X vp0010110000001.list + horner X ep0010110000001.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110000001 : Branch 1 (-1407761639/2000000 : ℚ) vp001011000000 := by
  apply branch_checked idp0010110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1407761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1408761639/1000000 : ℚ) by norm_num]
  exact coverp0010110000001
theorem coverp001011000000 : Covers (-1407761639/2000000 : ℚ) vp001011000000 := join_branches bp0010110000000 bp0010110000001
private noncomputable def vp00101100000_0 : Blocks := edgeBlocks% "full/vectors/00101100000-V-0000.bin"
noncomputable def vp00101100000 : Blocks := vp00101100000_0
private theorem bp001011000000 : Branch 0 (-1407761639/4000000 : ℚ) vp00101100000 := by
  apply branch_left_normalized (c:=vp001011000000) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1407761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1407761639/2000000 : ℚ) by norm_num]
  exact coverp001011000000
private noncomputable def ep001011000001_0 : Blocks := edgeBlocks% "full/vectors/001011000001-E-0000.bin"
noncomputable def ep001011000001 : Blocks := ep001011000001_0
private theorem idp001011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101100000.list =
    C ((2:ℤ)^139) * horner X vp001011000001.list + horner X ep001011000001.list := by
  exact edge_identity (B := (2:ℤ)^283) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011000001 : Branch 1 (-1407761639/4000000 : ℚ) vp00101100000 := by
  apply branch_checked idp001011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1407761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1409761639/2000000 : ℚ) by norm_num]
  exact coverp001011000001
theorem coverp00101100000 : Covers (-1407761639/4000000 : ℚ) vp00101100000 := join_branches bp001011000000 bp001011000001
private noncomputable def vp0010110000_0 : Blocks := edgeBlocks% "full/vectors/0010110000-V-0000.bin"
private noncomputable def vp0010110000_1 : Blocks := edgeBlocks% "full/vectors/0010110000-V-0001.bin"
noncomputable def vp0010110000 : Blocks := (Blocks.join vp0010110000_0 vp0010110000_1)
private theorem bp00101100000 : Branch 0 (-1407761639/8000000 : ℚ) vp0010110000 := by
  apply branch_left_normalized (c:=vp00101100000) (k:=0) (m:=126) (by decide +kernel)
  rw [show 2*(-1407761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1407761639/4000000 : ℚ) by norm_num]
  exact coverp00101100000
private noncomputable def ep00101100001_0 : Blocks := edgeBlocks% "full/vectors/00101100001-E-0000.bin"
private noncomputable def ep00101100001_1 : Blocks := edgeBlocks% "full/vectors/00101100001-E-0001.bin"
noncomputable def ep00101100001 : Blocks := (Blocks.join ep00101100001_0 ep00101100001_1)
private theorem idp00101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010110000.list =
    C ((2:ℤ)^255) * horner X vp00101100001.list + horner X ep00101100001.list := by
  exact edge_identity (B := (2:ℤ)^444) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101100001 : Branch 1 (-1407761639/8000000 : ℚ) vp0010110000 := by
  apply branch_checked idp00101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1407761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1411761639/4000000 : ℚ) by norm_num]
  exact coverp00101100001
theorem coverp0010110000 : Covers (-1407761639/8000000 : ℚ) vp0010110000 := join_branches bp00101100000 bp00101100001
private noncomputable def vp001011000_0 : Blocks := edgeBlocks% "full/vectors/001011000-V-0000.bin"
private noncomputable def vp001011000_1 : Blocks := edgeBlocks% "full/vectors/001011000-V-0001.bin"
private noncomputable def vp001011000_2 : Blocks := edgeBlocks% "full/vectors/001011000-V-0002.bin"
private noncomputable def vp001011000_3 : Blocks := edgeBlocks% "full/vectors/001011000-V-0003.bin"
noncomputable def vp001011000 : Blocks := (Blocks.join (Blocks.join vp001011000_0 vp001011000_1) (Blocks.join vp001011000_2 vp001011000_3))
private theorem bp0010110000 : Branch 0 (-1407761639/16000000 : ℚ) vp001011000 := by
  apply branch_left_normalized (c:=vp0010110000) (k:=0) (m:=231) (by decide +kernel)
  rw [show 2*(-1407761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1407761639/8000000 : ℚ) by norm_num]
  exact coverp0010110000
private noncomputable def ep0010110001_0 : Blocks := edgeBlocks% "full/vectors/0010110001-E-0000.bin"
private noncomputable def ep0010110001_1 : Blocks := edgeBlocks% "full/vectors/0010110001-E-0001.bin"
private noncomputable def ep0010110001_2 : Blocks := edgeBlocks% "full/vectors/0010110001-E-0002.bin"
private noncomputable def ep0010110001_3 : Blocks := edgeBlocks% "full/vectors/0010110001-E-0003.bin"
noncomputable def ep0010110001 : Blocks := (Blocks.join (Blocks.join ep0010110001_0 ep0010110001_1) (Blocks.join ep0010110001_2 ep0010110001_3))
private theorem idp0010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011000.list =
    C ((2:ℤ)^485) * horner X vp0010110001.list + horner X ep0010110001.list := by
  exact edge_identity (B := (2:ℤ)^763) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010110001 : Branch 1 (-1407761639/16000000 : ℚ) vp001011000 := by
  apply branch_checked idp0010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1407761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1415761639/8000000 : ℚ) by norm_num]
  exact coverp0010110001
theorem coverp001011000 : Covers (-1407761639/16000000 : ℚ) vp001011000 := join_branches bp0010110000 bp0010110001
private noncomputable def vp00101100_0 : Blocks := edgeBlocks% "full/vectors/00101100-V-0000.bin"
private noncomputable def vp00101100_1 : Blocks := edgeBlocks% "full/vectors/00101100-V-0001.bin"
private noncomputable def vp00101100_2 : Blocks := edgeBlocks% "full/vectors/00101100-V-0002.bin"
private noncomputable def vp00101100_3 : Blocks := edgeBlocks% "full/vectors/00101100-V-0003.bin"
private noncomputable def vp00101100_4 : Blocks := edgeBlocks% "full/vectors/00101100-V-0004.bin"
private noncomputable def vp00101100_5 : Blocks := edgeBlocks% "full/vectors/00101100-V-0005.bin"
private noncomputable def vp00101100_6 : Blocks := edgeBlocks% "full/vectors/00101100-V-0006.bin"
noncomputable def vp00101100 : Blocks := (Blocks.join (Blocks.join vp00101100_0 (Blocks.join vp00101100_1 vp00101100_2)) (Blocks.join (Blocks.join vp00101100_3 vp00101100_4) (Blocks.join vp00101100_5 vp00101100_6)))
private theorem bp001011000 : Branch 0 (-1407761639/32000000 : ℚ) vp00101100 := by
  apply branch_left_normalized (c:=vp001011000) (k:=0) (m:=439) (by decide +kernel)
  rw [show 2*(-1407761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1407761639/16000000 : ℚ) by norm_num]
  exact coverp001011000
private noncomputable def ep001011001_0 : Blocks := edgeBlocks% "full/vectors/001011001-E-0000.bin"
private noncomputable def ep001011001_1 : Blocks := edgeBlocks% "full/vectors/001011001-E-0001.bin"
private noncomputable def ep001011001_2 : Blocks := edgeBlocks% "full/vectors/001011001-E-0002.bin"
private noncomputable def ep001011001_3 : Blocks := edgeBlocks% "full/vectors/001011001-E-0003.bin"
private noncomputable def ep001011001_4 : Blocks := edgeBlocks% "full/vectors/001011001-E-0004.bin"
private noncomputable def ep001011001_5 : Blocks := edgeBlocks% "full/vectors/001011001-E-0005.bin"
private noncomputable def ep001011001_6 : Blocks := edgeBlocks% "full/vectors/001011001-E-0006.bin"
noncomputable def ep001011001 : Blocks := (Blocks.join (Blocks.join ep001011001_0 (Blocks.join ep001011001_1 ep001011001_2)) (Blocks.join (Blocks.join ep001011001_3 ep001011001_4) (Blocks.join ep001011001_5 ep001011001_6)))
private theorem idp001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00101100.list =
    C ((2:ℤ)^943) * horner X vp001011001.list + horner X ep001011001.list := by
  exact edge_identity (B := (2:ℤ)^1395) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001011001 : Branch 1 (-1407761639/32000000 : ℚ) vp00101100 := by
  apply branch_checked idp001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1407761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1423761639/16000000 : ℚ) by norm_num]
  exact coverp001011001
theorem coverp00101100 : Covers (-1407761639/32000000 : ℚ) vp00101100 := join_branches bp001011000 bp001011001
private noncomputable def vp0010110_0 : Blocks := edgeBlocks% "full/vectors/0010110-V-0000.bin"
private noncomputable def vp0010110_1 : Blocks := edgeBlocks% "full/vectors/0010110-V-0001.bin"
private noncomputable def vp0010110_2 : Blocks := edgeBlocks% "full/vectors/0010110-V-0002.bin"
private noncomputable def vp0010110_3 : Blocks := edgeBlocks% "full/vectors/0010110-V-0003.bin"
private noncomputable def vp0010110_4 : Blocks := edgeBlocks% "full/vectors/0010110-V-0004.bin"
private noncomputable def vp0010110_5 : Blocks := edgeBlocks% "full/vectors/0010110-V-0005.bin"
private noncomputable def vp0010110_6 : Blocks := edgeBlocks% "full/vectors/0010110-V-0006.bin"
private noncomputable def vp0010110_7 : Blocks := edgeBlocks% "full/vectors/0010110-V-0007.bin"
private noncomputable def vp0010110_8 : Blocks := edgeBlocks% "full/vectors/0010110-V-0008.bin"
private noncomputable def vp0010110_9 : Blocks := edgeBlocks% "full/vectors/0010110-V-0009.bin"
private noncomputable def vp0010110_10 : Blocks := edgeBlocks% "full/vectors/0010110-V-0010.bin"
private noncomputable def vp0010110_11 : Blocks := edgeBlocks% "full/vectors/0010110-V-0011.bin"
private noncomputable def vp0010110_12 : Blocks := edgeBlocks% "full/vectors/0010110-V-0012.bin"
noncomputable def vp0010110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0010110_0 (Blocks.join vp0010110_1 vp0010110_2)) (Blocks.join vp0010110_3 (Blocks.join vp0010110_4 vp0010110_5))) (Blocks.join (Blocks.join vp0010110_6 (Blocks.join vp0010110_7 vp0010110_8)) (Blocks.join (Blocks.join vp0010110_9 vp0010110_10) (Blocks.join vp0010110_11 vp0010110_12))))
private theorem bp00101100 : Branch 0 (-1407761639/64000000 : ℚ) vp0010110 := by
  apply branch_left_normalized (c:=vp00101100) (k:=0) (m:=850) (by decide +kernel)
  rw [show 2*(-1407761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1407761639/32000000 : ℚ) by norm_num]
  exact coverp00101100
private noncomputable def ep00101101_0 : Blocks := edgeBlocks% "full/vectors/00101101-E-0000.bin"
private noncomputable def ep00101101_1 : Blocks := edgeBlocks% "full/vectors/00101101-E-0001.bin"
private noncomputable def ep00101101_2 : Blocks := edgeBlocks% "full/vectors/00101101-E-0002.bin"
private noncomputable def ep00101101_3 : Blocks := edgeBlocks% "full/vectors/00101101-E-0003.bin"
private noncomputable def ep00101101_4 : Blocks := edgeBlocks% "full/vectors/00101101-E-0004.bin"
private noncomputable def ep00101101_5 : Blocks := edgeBlocks% "full/vectors/00101101-E-0005.bin"
private noncomputable def ep00101101_6 : Blocks := edgeBlocks% "full/vectors/00101101-E-0006.bin"
private noncomputable def ep00101101_7 : Blocks := edgeBlocks% "full/vectors/00101101-E-0007.bin"
private noncomputable def ep00101101_8 : Blocks := edgeBlocks% "full/vectors/00101101-E-0008.bin"
private noncomputable def ep00101101_9 : Blocks := edgeBlocks% "full/vectors/00101101-E-0009.bin"
private noncomputable def ep00101101_10 : Blocks := edgeBlocks% "full/vectors/00101101-E-0010.bin"
private noncomputable def ep00101101_11 : Blocks := edgeBlocks% "full/vectors/00101101-E-0011.bin"
private noncomputable def ep00101101_12 : Blocks := edgeBlocks% "full/vectors/00101101-E-0012.bin"
noncomputable def ep00101101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00101101_0 (Blocks.join ep00101101_1 ep00101101_2)) (Blocks.join ep00101101_3 (Blocks.join ep00101101_4 ep00101101_5))) (Blocks.join (Blocks.join ep00101101_6 (Blocks.join ep00101101_7 ep00101101_8)) (Blocks.join (Blocks.join ep00101101_9 ep00101101_10) (Blocks.join ep00101101_11 ep00101101_12))))
private theorem idp00101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010110.list =
    C ((2:ℤ)^1842) * horner X vp00101101.list + horner X ep00101101.list := by
  exact edge_identity (B := (2:ℤ)^2641) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00101101 : Branch 1 (-1407761639/64000000 : ℚ) vp0010110 := by
  apply branch_checked idp00101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1407761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1439761639/32000000 : ℚ) by norm_num]
  exact coverp00101101
theorem coverp0010110 : Covers (-1407761639/64000000 : ℚ) vp0010110 := join_branches bp00101100 bp00101101
private noncomputable def vp001011_0 : Blocks := edgeBlocks% "full/vectors/001011-V-0000.bin"
private noncomputable def vp001011_1 : Blocks := edgeBlocks% "full/vectors/001011-V-0001.bin"
private noncomputable def vp001011_2 : Blocks := edgeBlocks% "full/vectors/001011-V-0002.bin"
private noncomputable def vp001011_3 : Blocks := edgeBlocks% "full/vectors/001011-V-0003.bin"
private noncomputable def vp001011_4 : Blocks := edgeBlocks% "full/vectors/001011-V-0004.bin"
private noncomputable def vp001011_5 : Blocks := edgeBlocks% "full/vectors/001011-V-0005.bin"
private noncomputable def vp001011_6 : Blocks := edgeBlocks% "full/vectors/001011-V-0006.bin"
private noncomputable def vp001011_7 : Blocks := edgeBlocks% "full/vectors/001011-V-0007.bin"
private noncomputable def vp001011_8 : Blocks := edgeBlocks% "full/vectors/001011-V-0008.bin"
private noncomputable def vp001011_9 : Blocks := edgeBlocks% "full/vectors/001011-V-0009.bin"
private noncomputable def vp001011_10 : Blocks := edgeBlocks% "full/vectors/001011-V-0010.bin"
private noncomputable def vp001011_11 : Blocks := edgeBlocks% "full/vectors/001011-V-0011.bin"
private noncomputable def vp001011_12 : Blocks := edgeBlocks% "full/vectors/001011-V-0012.bin"
private noncomputable def vp001011_13 : Blocks := edgeBlocks% "full/vectors/001011-V-0013.bin"
private noncomputable def vp001011_14 : Blocks := edgeBlocks% "full/vectors/001011-V-0014.bin"
private noncomputable def vp001011_15 : Blocks := edgeBlocks% "full/vectors/001011-V-0015.bin"
private noncomputable def vp001011_16 : Blocks := edgeBlocks% "full/vectors/001011-V-0016.bin"
private noncomputable def vp001011_17 : Blocks := edgeBlocks% "full/vectors/001011-V-0017.bin"
private noncomputable def vp001011_18 : Blocks := edgeBlocks% "full/vectors/001011-V-0018.bin"
private noncomputable def vp001011_19 : Blocks := edgeBlocks% "full/vectors/001011-V-0019.bin"
private noncomputable def vp001011_20 : Blocks := edgeBlocks% "full/vectors/001011-V-0020.bin"
private noncomputable def vp001011_21 : Blocks := edgeBlocks% "full/vectors/001011-V-0021.bin"
private noncomputable def vp001011_22 : Blocks := edgeBlocks% "full/vectors/001011-V-0022.bin"
private noncomputable def vp001011_23 : Blocks := edgeBlocks% "full/vectors/001011-V-0023.bin"
private noncomputable def vp001011_24 : Blocks := edgeBlocks% "full/vectors/001011-V-0024.bin"
private noncomputable def vp001011_25 : Blocks := edgeBlocks% "full/vectors/001011-V-0025.bin"
noncomputable def vp001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp001011_0 (Blocks.join vp001011_1 vp001011_2)) (Blocks.join vp001011_3 (Blocks.join vp001011_4 vp001011_5))) (Blocks.join (Blocks.join vp001011_6 (Blocks.join vp001011_7 vp001011_8)) (Blocks.join (Blocks.join vp001011_9 vp001011_10) (Blocks.join vp001011_11 vp001011_12)))) (Blocks.join (Blocks.join (Blocks.join vp001011_13 (Blocks.join vp001011_14 vp001011_15)) (Blocks.join vp001011_16 (Blocks.join vp001011_17 vp001011_18))) (Blocks.join (Blocks.join vp001011_19 (Blocks.join vp001011_20 vp001011_21)) (Blocks.join (Blocks.join vp001011_22 vp001011_23) (Blocks.join vp001011_24 vp001011_25)))))
private theorem bp0010110 : Branch 0 (-1407761639/128000000 : ℚ) vp001011 := by
  apply branch_left_normalized (c:=vp0010110) (k:=0) (m:=1657) (by decide +kernel)
  rw [show 2*(-1407761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-1407761639/64000000 : ℚ) by norm_num]
  exact coverp0010110
private noncomputable def ep0010111_0 : Blocks := edgeBlocks% "full/vectors/0010111-E-0000.bin"
private noncomputable def ep0010111_1 : Blocks := edgeBlocks% "full/vectors/0010111-E-0001.bin"
private noncomputable def ep0010111_2 : Blocks := edgeBlocks% "full/vectors/0010111-E-0002.bin"
private noncomputable def ep0010111_3 : Blocks := edgeBlocks% "full/vectors/0010111-E-0003.bin"
private noncomputable def ep0010111_4 : Blocks := edgeBlocks% "full/vectors/0010111-E-0004.bin"
private noncomputable def ep0010111_5 : Blocks := edgeBlocks% "full/vectors/0010111-E-0005.bin"
private noncomputable def ep0010111_6 : Blocks := edgeBlocks% "full/vectors/0010111-E-0006.bin"
private noncomputable def ep0010111_7 : Blocks := edgeBlocks% "full/vectors/0010111-E-0007.bin"
private noncomputable def ep0010111_8 : Blocks := edgeBlocks% "full/vectors/0010111-E-0008.bin"
private noncomputable def ep0010111_9 : Blocks := edgeBlocks% "full/vectors/0010111-E-0009.bin"
private noncomputable def ep0010111_10 : Blocks := edgeBlocks% "full/vectors/0010111-E-0010.bin"
private noncomputable def ep0010111_11 : Blocks := edgeBlocks% "full/vectors/0010111-E-0011.bin"
private noncomputable def ep0010111_12 : Blocks := edgeBlocks% "full/vectors/0010111-E-0012.bin"
private noncomputable def ep0010111_13 : Blocks := edgeBlocks% "full/vectors/0010111-E-0013.bin"
private noncomputable def ep0010111_14 : Blocks := edgeBlocks% "full/vectors/0010111-E-0014.bin"
private noncomputable def ep0010111_15 : Blocks := edgeBlocks% "full/vectors/0010111-E-0015.bin"
private noncomputable def ep0010111_16 : Blocks := edgeBlocks% "full/vectors/0010111-E-0016.bin"
private noncomputable def ep0010111_17 : Blocks := edgeBlocks% "full/vectors/0010111-E-0017.bin"
private noncomputable def ep0010111_18 : Blocks := edgeBlocks% "full/vectors/0010111-E-0018.bin"
private noncomputable def ep0010111_19 : Blocks := edgeBlocks% "full/vectors/0010111-E-0019.bin"
private noncomputable def ep0010111_20 : Blocks := edgeBlocks% "full/vectors/0010111-E-0020.bin"
private noncomputable def ep0010111_21 : Blocks := edgeBlocks% "full/vectors/0010111-E-0021.bin"
private noncomputable def ep0010111_22 : Blocks := edgeBlocks% "full/vectors/0010111-E-0022.bin"
private noncomputable def ep0010111_23 : Blocks := edgeBlocks% "full/vectors/0010111-E-0023.bin"
private noncomputable def ep0010111_24 : Blocks := edgeBlocks% "full/vectors/0010111-E-0024.bin"
private noncomputable def ep0010111_25 : Blocks := edgeBlocks% "full/vectors/0010111-E-0025.bin"
noncomputable def ep0010111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0010111_0 (Blocks.join ep0010111_1 ep0010111_2)) (Blocks.join ep0010111_3 (Blocks.join ep0010111_4 ep0010111_5))) (Blocks.join (Blocks.join ep0010111_6 (Blocks.join ep0010111_7 ep0010111_8)) (Blocks.join (Blocks.join ep0010111_9 ep0010111_10) (Blocks.join ep0010111_11 ep0010111_12)))) (Blocks.join (Blocks.join (Blocks.join ep0010111_13 (Blocks.join ep0010111_14 ep0010111_15)) (Blocks.join ep0010111_16 (Blocks.join ep0010111_17 ep0010111_18))) (Blocks.join (Blocks.join ep0010111_19 (Blocks.join ep0010111_20 ep0010111_21)) (Blocks.join (Blocks.join ep0010111_22 ep0010111_23) (Blocks.join ep0010111_24 ep0010111_25)))))
private def ptsp0010111 : List ℤ := [((2:ℤ)^3740+0),((2:ℤ)^3740+1)]
private theorem boundp0010111 : 2^vp001011.size*absSum vp001011.list + ((2:ℤ)^3578*absSum vp0010111.list+absSum ep0010111.list) < (2:ℤ)^5057 := by decide +kernel
private theorem pointp0010111_0 : fastHom 1 ((2:ℤ)^3740+0) vp001011 = ((2:ℤ)^3578)*vp0010111.subst ((2:ℤ)^3740+0)+ep0010111.subst ((2:ℤ)^3740+0) := by decide +kernel
private theorem pointp0010111_1 : fastHom 1 ((2:ℤ)^3740+1) vp001011 = ((2:ℤ)^3578)*vp0010111.subst ((2:ℤ)^3740+1)+ep0010111.subst ((2:ℤ)^3740+1) := by decide +kernel
private theorem checkp0010111 (x:ℤ) (hx:x ∈ ptsp0010111) : fastHom 1 x vp001011 = ((2:ℤ)^3578)*vp0010111.subst x+ep0010111.subst x := by
  simp only [ptsp0010111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp0010111_0
  · exact pointp0010111_1
private theorem idp0010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001011.list =
    C ((2:ℤ)^3578) * horner X vp0010111.list + horner X ep0010111.list := by
  apply edge_identity (B := (2:ℤ)^5057) (by decide) (by positivity) (by positivity) boundp0010111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0010111 (by decide +kernel)
  · have h : ptsp0010111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0010111.trans_le (by decide +kernel)
  · exact checkp0010111
private theorem bp0010111 : Branch 1 (-1407761639/128000000 : ℚ) vp001011 := by
  apply branch_checked idp0010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1407761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-1471761639/64000000 : ℚ) by norm_num]
  exact coverp0010111
theorem coverp001011 : Covers (-1407761639/128000000 : ℚ) vp001011 := join_branches bp0010110 bp0010111
end NextProof.EdgeFull

