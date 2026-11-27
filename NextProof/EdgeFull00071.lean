import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00070

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0001010011111_0 : Blocks := edgeBlocks% "full/vectors/0001010011111-V-0000.bin"
noncomputable def vp0001010011111 : Blocks := vp0001010011111_0
theorem coverp0001010011111 : Covers (-670761639/1000000 : ℚ) vp0001010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010011110_0 : Blocks := edgeBlocks% "full/vectors/0001010011110-V-0000.bin"
noncomputable def vp0001010011110 : Blocks := vp0001010011110_0
theorem coverp0001010011110 : Covers (-669761639/1000000 : ℚ) vp0001010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000101001111_0 : Blocks := edgeBlocks% "full/vectors/000101001111-V-0000.bin"
noncomputable def vp000101001111 : Blocks := vp000101001111_0
private theorem bp0001010011110 : Branch 0 (-669761639/2000000 : ℚ) vp000101001111 := by
  apply branch_left_normalized (c:=vp0001010011110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-669761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-669761639/1000000 : ℚ) by norm_num]
  exact coverp0001010011110
private noncomputable def ep0001010011111_0 : Blocks := edgeBlocks% "full/vectors/0001010011111-E-0000.bin"
noncomputable def ep0001010011111 : Blocks := ep0001010011111_0
private theorem idp0001010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101001111.list =
    C ((2:ℤ)^98) * horner X vp0001010011111.list + horner X ep0001010011111.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010011111 : Branch 1 (-669761639/2000000 : ℚ) vp000101001111 := by
  apply branch_checked idp0001010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-669761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-670761639/1000000 : ℚ) by norm_num]
  exact coverp0001010011111
theorem coverp000101001111 : Covers (-669761639/2000000 : ℚ) vp000101001111 := join_branches bp0001010011110 bp0001010011111
private noncomputable def vp0001010011101_0 : Blocks := edgeBlocks% "full/vectors/0001010011101-V-0000.bin"
noncomputable def vp0001010011101 : Blocks := vp0001010011101_0
theorem coverp0001010011101 : Covers (-668761639/1000000 : ℚ) vp0001010011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010011100_0 : Blocks := edgeBlocks% "full/vectors/0001010011100-V-0000.bin"
noncomputable def vp0001010011100 : Blocks := vp0001010011100_0
theorem coverp0001010011100 : Covers (-667761639/1000000 : ℚ) vp0001010011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000101001110_0 : Blocks := edgeBlocks% "full/vectors/000101001110-V-0000.bin"
noncomputable def vp000101001110 : Blocks := vp000101001110_0
private theorem bp0001010011100 : Branch 0 (-667761639/2000000 : ℚ) vp000101001110 := by
  apply branch_left_normalized (c:=vp0001010011100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-667761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-667761639/1000000 : ℚ) by norm_num]
  exact coverp0001010011100
private noncomputable def ep0001010011101_0 : Blocks := edgeBlocks% "full/vectors/0001010011101-E-0000.bin"
noncomputable def ep0001010011101 : Blocks := ep0001010011101_0
private theorem idp0001010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101001110.list =
    C ((2:ℤ)^98) * horner X vp0001010011101.list + horner X ep0001010011101.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010011101 : Branch 1 (-667761639/2000000 : ℚ) vp000101001110 := by
  apply branch_checked idp0001010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-667761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-668761639/1000000 : ℚ) by norm_num]
  exact coverp0001010011101
theorem coverp000101001110 : Covers (-667761639/2000000 : ℚ) vp000101001110 := join_branches bp0001010011100 bp0001010011101
private noncomputable def vp00010100111_0 : Blocks := edgeBlocks% "full/vectors/00010100111-V-0000.bin"
private noncomputable def vp00010100111_1 : Blocks := edgeBlocks% "full/vectors/00010100111-V-0001.bin"
noncomputable def vp00010100111 : Blocks := (Blocks.join vp00010100111_0 vp00010100111_1)
private theorem bp000101001110 : Branch 0 (-667761639/4000000 : ℚ) vp00010100111 := by
  apply branch_left_normalized (c:=vp000101001110) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-667761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-667761639/2000000 : ℚ) by norm_num]
  exact coverp000101001110
private noncomputable def ep000101001111_0 : Blocks := edgeBlocks% "full/vectors/000101001111-E-0000.bin"
private noncomputable def ep000101001111_1 : Blocks := edgeBlocks% "full/vectors/000101001111-E-0001.bin"
noncomputable def ep000101001111 : Blocks := (Blocks.join ep000101001111_0 ep000101001111_1)
private theorem idp000101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010100111.list =
    C ((2:ℤ)^179) * horner X vp000101001111.list + horner X ep000101001111.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101001111 : Branch 1 (-667761639/4000000 : ℚ) vp00010100111 := by
  apply branch_checked idp000101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-667761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-669761639/2000000 : ℚ) by norm_num]
  exact coverp000101001111
theorem coverp00010100111 : Covers (-667761639/4000000 : ℚ) vp00010100111 := join_branches bp000101001110 bp000101001111
private noncomputable def vp0001010011011_0 : Blocks := edgeBlocks% "full/vectors/0001010011011-V-0000.bin"
noncomputable def vp0001010011011 : Blocks := vp0001010011011_0
theorem coverp0001010011011 : Covers (-666761639/1000000 : ℚ) vp0001010011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010011010_0 : Blocks := edgeBlocks% "full/vectors/0001010011010-V-0000.bin"
noncomputable def vp0001010011010 : Blocks := vp0001010011010_0
theorem coverp0001010011010 : Covers (-665761639/1000000 : ℚ) vp0001010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000101001101_0 : Blocks := edgeBlocks% "full/vectors/000101001101-V-0000.bin"
noncomputable def vp000101001101 : Blocks := vp000101001101_0
private theorem bp0001010011010 : Branch 0 (-665761639/2000000 : ℚ) vp000101001101 := by
  apply branch_left_normalized (c:=vp0001010011010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-665761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-665761639/1000000 : ℚ) by norm_num]
  exact coverp0001010011010
private noncomputable def ep0001010011011_0 : Blocks := edgeBlocks% "full/vectors/0001010011011-E-0000.bin"
noncomputable def ep0001010011011 : Blocks := ep0001010011011_0
private theorem idp0001010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101001101.list =
    C ((2:ℤ)^97) * horner X vp0001010011011.list + horner X ep0001010011011.list := by
  exact edge_identity (B := (2:ℤ)^222) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010011011 : Branch 1 (-665761639/2000000 : ℚ) vp000101001101 := by
  apply branch_checked idp0001010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-665761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-666761639/1000000 : ℚ) by norm_num]
  exact coverp0001010011011
theorem coverp000101001101 : Covers (-665761639/2000000 : ℚ) vp000101001101 := join_branches bp0001010011010 bp0001010011011
private noncomputable def vp0001010011001_0 : Blocks := edgeBlocks% "full/vectors/0001010011001-V-0000.bin"
noncomputable def vp0001010011001 : Blocks := vp0001010011001_0
theorem coverp0001010011001 : Covers (-664761639/1000000 : ℚ) vp0001010011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010011000_0 : Blocks := edgeBlocks% "full/vectors/0001010011000-V-0000.bin"
noncomputable def vp0001010011000 : Blocks := vp0001010011000_0
theorem coverp0001010011000 : Covers (-663761639/1000000 : ℚ) vp0001010011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000101001100_0 : Blocks := edgeBlocks% "full/vectors/000101001100-V-0000.bin"
noncomputable def vp000101001100 : Blocks := vp000101001100_0
private theorem bp0001010011000 : Branch 0 (-663761639/2000000 : ℚ) vp000101001100 := by
  apply branch_left_normalized (c:=vp0001010011000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-663761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-663761639/1000000 : ℚ) by norm_num]
  exact coverp0001010011000
private noncomputable def ep0001010011001_0 : Blocks := edgeBlocks% "full/vectors/0001010011001-E-0000.bin"
noncomputable def ep0001010011001 : Blocks := ep0001010011001_0
private theorem idp0001010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101001100.list =
    C ((2:ℤ)^98) * horner X vp0001010011001.list + horner X ep0001010011001.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010011001 : Branch 1 (-663761639/2000000 : ℚ) vp000101001100 := by
  apply branch_checked idp0001010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-663761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-664761639/1000000 : ℚ) by norm_num]
  exact coverp0001010011001
theorem coverp000101001100 : Covers (-663761639/2000000 : ℚ) vp000101001100 := join_branches bp0001010011000 bp0001010011001
private noncomputable def vp00010100110_0 : Blocks := edgeBlocks% "full/vectors/00010100110-V-0000.bin"
private noncomputable def vp00010100110_1 : Blocks := edgeBlocks% "full/vectors/00010100110-V-0001.bin"
noncomputable def vp00010100110 : Blocks := (Blocks.join vp00010100110_0 vp00010100110_1)
private theorem bp000101001100 : Branch 0 (-663761639/4000000 : ℚ) vp00010100110 := by
  apply branch_left_normalized (c:=vp000101001100) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-663761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-663761639/2000000 : ℚ) by norm_num]
  exact coverp000101001100
private noncomputable def ep000101001101_0 : Blocks := edgeBlocks% "full/vectors/000101001101-E-0000.bin"
private noncomputable def ep000101001101_1 : Blocks := edgeBlocks% "full/vectors/000101001101-E-0001.bin"
noncomputable def ep000101001101 : Blocks := (Blocks.join ep000101001101_0 ep000101001101_1)
private theorem idp000101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010100110.list =
    C ((2:ℤ)^180) * horner X vp000101001101.list + horner X ep000101001101.list := by
  exact edge_identity (B := (2:ℤ)^339) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101001101 : Branch 1 (-663761639/4000000 : ℚ) vp00010100110 := by
  apply branch_checked idp000101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-663761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-665761639/2000000 : ℚ) by norm_num]
  exact coverp000101001101
theorem coverp00010100110 : Covers (-663761639/4000000 : ℚ) vp00010100110 := join_branches bp000101001100 bp000101001101
private noncomputable def vp0001010011_0 : Blocks := edgeBlocks% "full/vectors/0001010011-V-0000.bin"
private noncomputable def vp0001010011_1 : Blocks := edgeBlocks% "full/vectors/0001010011-V-0001.bin"
private noncomputable def vp0001010011_2 : Blocks := edgeBlocks% "full/vectors/0001010011-V-0002.bin"
noncomputable def vp0001010011 : Blocks := (Blocks.join vp0001010011_0 (Blocks.join vp0001010011_1 vp0001010011_2))
private theorem bp00010100110 : Branch 0 (-663761639/8000000 : ℚ) vp0001010011 := by
  apply branch_left_normalized (c:=vp00010100110) (k:=0) (m:=167) (by decide +kernel)
  rw [show 2*(-663761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-663761639/4000000 : ℚ) by norm_num]
  exact coverp00010100110
private noncomputable def ep00010100111_0 : Blocks := edgeBlocks% "full/vectors/00010100111-E-0000.bin"
private noncomputable def ep00010100111_1 : Blocks := edgeBlocks% "full/vectors/00010100111-E-0001.bin"
private noncomputable def ep00010100111_2 : Blocks := edgeBlocks% "full/vectors/00010100111-E-0002.bin"
noncomputable def ep00010100111 : Blocks := (Blocks.join ep00010100111_0 (Blocks.join ep00010100111_1 ep00010100111_2))
private theorem idp00010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010011.list =
    C ((2:ℤ)^342) * horner X vp00010100111.list + horner X ep00010100111.list := by
  exact edge_identity (B := (2:ℤ)^572) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010100111 : Branch 1 (-663761639/8000000 : ℚ) vp0001010011 := by
  apply branch_checked idp00010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-663761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-667761639/4000000 : ℚ) by norm_num]
  exact coverp00010100111
theorem coverp0001010011 : Covers (-663761639/8000000 : ℚ) vp0001010011 := join_branches bp00010100110 bp00010100111
private noncomputable def vp0001010010111_0 : Blocks := edgeBlocks% "full/vectors/0001010010111-V-0000.bin"
noncomputable def vp0001010010111 : Blocks := vp0001010010111_0
theorem coverp0001010010111 : Covers (-662761639/1000000 : ℚ) vp0001010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010010110_0 : Blocks := edgeBlocks% "full/vectors/0001010010110-V-0000.bin"
noncomputable def vp0001010010110 : Blocks := vp0001010010110_0
theorem coverp0001010010110 : Covers (-661761639/1000000 : ℚ) vp0001010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000101001011_0 : Blocks := edgeBlocks% "full/vectors/000101001011-V-0000.bin"
noncomputable def vp000101001011 : Blocks := vp000101001011_0
private theorem bp0001010010110 : Branch 0 (-661761639/2000000 : ℚ) vp000101001011 := by
  apply branch_left_normalized (c:=vp0001010010110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-661761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-661761639/1000000 : ℚ) by norm_num]
  exact coverp0001010010110
private noncomputable def ep0001010010111_0 : Blocks := edgeBlocks% "full/vectors/0001010010111-E-0000.bin"
noncomputable def ep0001010010111 : Blocks := ep0001010010111_0
private theorem idp0001010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101001011.list =
    C ((2:ℤ)^98) * horner X vp0001010010111.list + horner X ep0001010010111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010010111 : Branch 1 (-661761639/2000000 : ℚ) vp000101001011 := by
  apply branch_checked idp0001010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-661761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-662761639/1000000 : ℚ) by norm_num]
  exact coverp0001010010111
theorem coverp000101001011 : Covers (-661761639/2000000 : ℚ) vp000101001011 := join_branches bp0001010010110 bp0001010010111
private noncomputable def vp0001010010101_0 : Blocks := edgeBlocks% "full/vectors/0001010010101-V-0000.bin"
noncomputable def vp0001010010101 : Blocks := vp0001010010101_0
theorem coverp0001010010101 : Covers (-660761639/1000000 : ℚ) vp0001010010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010010100_0 : Blocks := edgeBlocks% "full/vectors/0001010010100-V-0000.bin"
noncomputable def vp0001010010100 : Blocks := vp0001010010100_0
theorem coverp0001010010100 : Covers (-659761639/1000000 : ℚ) vp0001010010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000101001010_0 : Blocks := edgeBlocks% "full/vectors/000101001010-V-0000.bin"
noncomputable def vp000101001010 : Blocks := vp000101001010_0
private theorem bp0001010010100 : Branch 0 (-659761639/2000000 : ℚ) vp000101001010 := by
  apply branch_left_normalized (c:=vp0001010010100) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-659761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-659761639/1000000 : ℚ) by norm_num]
  exact coverp0001010010100
private noncomputable def ep0001010010101_0 : Blocks := edgeBlocks% "full/vectors/0001010010101-E-0000.bin"
noncomputable def ep0001010010101 : Blocks := ep0001010010101_0
private theorem idp0001010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101001010.list =
    C ((2:ℤ)^98) * horner X vp0001010010101.list + horner X ep0001010010101.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010010101 : Branch 1 (-659761639/2000000 : ℚ) vp000101001010 := by
  apply branch_checked idp0001010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-659761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-660761639/1000000 : ℚ) by norm_num]
  exact coverp0001010010101
theorem coverp000101001010 : Covers (-659761639/2000000 : ℚ) vp000101001010 := join_branches bp0001010010100 bp0001010010101
private noncomputable def vp00010100101_0 : Blocks := edgeBlocks% "full/vectors/00010100101-V-0000.bin"
private noncomputable def vp00010100101_1 : Blocks := edgeBlocks% "full/vectors/00010100101-V-0001.bin"
noncomputable def vp00010100101 : Blocks := (Blocks.join vp00010100101_0 vp00010100101_1)
private theorem bp000101001010 : Branch 0 (-659761639/4000000 : ℚ) vp00010100101 := by
  apply branch_left_normalized (c:=vp000101001010) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-659761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-659761639/2000000 : ℚ) by norm_num]
  exact coverp000101001010
private noncomputable def ep000101001011_0 : Blocks := edgeBlocks% "full/vectors/000101001011-E-0000.bin"
private noncomputable def ep000101001011_1 : Blocks := edgeBlocks% "full/vectors/000101001011-E-0001.bin"
noncomputable def ep000101001011 : Blocks := (Blocks.join ep000101001011_0 ep000101001011_1)
private theorem idp000101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010100101.list =
    C ((2:ℤ)^181) * horner X vp000101001011.list + horner X ep000101001011.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101001011 : Branch 1 (-659761639/4000000 : ℚ) vp00010100101 := by
  apply branch_checked idp000101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-659761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-661761639/2000000 : ℚ) by norm_num]
  exact coverp000101001011
theorem coverp00010100101 : Covers (-659761639/4000000 : ℚ) vp00010100101 := join_branches bp000101001010 bp000101001011
private noncomputable def vp0001010010011_0 : Blocks := edgeBlocks% "full/vectors/0001010010011-V-0000.bin"
noncomputable def vp0001010010011 : Blocks := vp0001010010011_0
theorem coverp0001010010011 : Covers (-658761639/1000000 : ℚ) vp0001010010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010010010_0 : Blocks := edgeBlocks% "full/vectors/0001010010010-V-0000.bin"
noncomputable def vp0001010010010 : Blocks := vp0001010010010_0
theorem coverp0001010010010 : Covers (-657761639/1000000 : ℚ) vp0001010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000101001001_0 : Blocks := edgeBlocks% "full/vectors/000101001001-V-0000.bin"
noncomputable def vp000101001001 : Blocks := vp000101001001_0
private theorem bp0001010010010 : Branch 0 (-657761639/2000000 : ℚ) vp000101001001 := by
  apply branch_left_normalized (c:=vp0001010010010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-657761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-657761639/1000000 : ℚ) by norm_num]
  exact coverp0001010010010
private noncomputable def ep0001010010011_0 : Blocks := edgeBlocks% "full/vectors/0001010010011-E-0000.bin"
noncomputable def ep0001010010011 : Blocks := ep0001010010011_0
private theorem idp0001010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101001001.list =
    C ((2:ℤ)^98) * horner X vp0001010010011.list + horner X ep0001010010011.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010010011 : Branch 1 (-657761639/2000000 : ℚ) vp000101001001 := by
  apply branch_checked idp0001010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-657761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-658761639/1000000 : ℚ) by norm_num]
  exact coverp0001010010011
theorem coverp000101001001 : Covers (-657761639/2000000 : ℚ) vp000101001001 := join_branches bp0001010010010 bp0001010010011
private noncomputable def vp0001010010001_0 : Blocks := edgeBlocks% "full/vectors/0001010010001-V-0000.bin"
noncomputable def vp0001010010001 : Blocks := vp0001010010001_0
theorem coverp0001010010001 : Covers (-656761639/1000000 : ℚ) vp0001010010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010010000_0 : Blocks := edgeBlocks% "full/vectors/0001010010000-V-0000.bin"
noncomputable def vp0001010010000 : Blocks := vp0001010010000_0
theorem coverp0001010010000 : Covers (-655761639/1000000 : ℚ) vp0001010010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000101001000_0 : Blocks := edgeBlocks% "full/vectors/000101001000-V-0000.bin"
noncomputable def vp000101001000 : Blocks := vp000101001000_0
private theorem bp0001010010000 : Branch 0 (-655761639/2000000 : ℚ) vp000101001000 := by
  apply branch_left_normalized (c:=vp0001010010000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-655761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-655761639/1000000 : ℚ) by norm_num]
  exact coverp0001010010000
private noncomputable def ep0001010010001_0 : Blocks := edgeBlocks% "full/vectors/0001010010001-E-0000.bin"
noncomputable def ep0001010010001 : Blocks := ep0001010010001_0
private theorem idp0001010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101001000.list =
    C ((2:ℤ)^99) * horner X vp0001010010001.list + horner X ep0001010010001.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010010001 : Branch 1 (-655761639/2000000 : ℚ) vp000101001000 := by
  apply branch_checked idp0001010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-655761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-656761639/1000000 : ℚ) by norm_num]
  exact coverp0001010010001
theorem coverp000101001000 : Covers (-655761639/2000000 : ℚ) vp000101001000 := join_branches bp0001010010000 bp0001010010001
private noncomputable def vp00010100100_0 : Blocks := edgeBlocks% "full/vectors/00010100100-V-0000.bin"
private noncomputable def vp00010100100_1 : Blocks := edgeBlocks% "full/vectors/00010100100-V-0001.bin"
noncomputable def vp00010100100 : Blocks := (Blocks.join vp00010100100_0 vp00010100100_1)
private theorem bp000101001000 : Branch 0 (-655761639/4000000 : ℚ) vp00010100100 := by
  apply branch_left_normalized (c:=vp000101001000) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-655761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-655761639/2000000 : ℚ) by norm_num]
  exact coverp000101001000
private noncomputable def ep000101001001_0 : Blocks := edgeBlocks% "full/vectors/000101001001-E-0000.bin"
private noncomputable def ep000101001001_1 : Blocks := edgeBlocks% "full/vectors/000101001001-E-0001.bin"
noncomputable def ep000101001001 : Blocks := (Blocks.join ep000101001001_0 ep000101001001_1)
private theorem idp000101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010100100.list =
    C ((2:ℤ)^181) * horner X vp000101001001.list + horner X ep000101001001.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101001001 : Branch 1 (-655761639/4000000 : ℚ) vp00010100100 := by
  apply branch_checked idp000101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-655761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-657761639/2000000 : ℚ) by norm_num]
  exact coverp000101001001
theorem coverp00010100100 : Covers (-655761639/4000000 : ℚ) vp00010100100 := join_branches bp000101001000 bp000101001001
private noncomputable def vp0001010010_0 : Blocks := edgeBlocks% "full/vectors/0001010010-V-0000.bin"
private noncomputable def vp0001010010_1 : Blocks := edgeBlocks% "full/vectors/0001010010-V-0001.bin"
private noncomputable def vp0001010010_2 : Blocks := edgeBlocks% "full/vectors/0001010010-V-0002.bin"
noncomputable def vp0001010010 : Blocks := (Blocks.join vp0001010010_0 (Blocks.join vp0001010010_1 vp0001010010_2))
private theorem bp00010100100 : Branch 0 (-655761639/8000000 : ℚ) vp0001010010 := by
  apply branch_left_normalized (c:=vp00010100100) (k:=0) (m:=168) (by decide +kernel)
  rw [show 2*(-655761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-655761639/4000000 : ℚ) by norm_num]
  exact coverp00010100100
private noncomputable def ep00010100101_0 : Blocks := edgeBlocks% "full/vectors/00010100101-E-0000.bin"
private noncomputable def ep00010100101_1 : Blocks := edgeBlocks% "full/vectors/00010100101-E-0001.bin"
private noncomputable def ep00010100101_2 : Blocks := edgeBlocks% "full/vectors/00010100101-E-0002.bin"
noncomputable def ep00010100101 : Blocks := (Blocks.join ep00010100101_0 (Blocks.join ep00010100101_1 ep00010100101_2))
private theorem idp00010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010010.list =
    C ((2:ℤ)^345) * horner X vp00010100101.list + horner X ep00010100101.list := by
  exact edge_identity (B := (2:ℤ)^575) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010100101 : Branch 1 (-655761639/8000000 : ℚ) vp0001010010 := by
  apply branch_checked idp00010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-655761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-659761639/4000000 : ℚ) by norm_num]
  exact coverp00010100101
theorem coverp0001010010 : Covers (-655761639/8000000 : ℚ) vp0001010010 := join_branches bp00010100100 bp00010100101
private noncomputable def vp000101001_0 : Blocks := edgeBlocks% "full/vectors/000101001-V-0000.bin"
private noncomputable def vp000101001_1 : Blocks := edgeBlocks% "full/vectors/000101001-V-0001.bin"
private noncomputable def vp000101001_2 : Blocks := edgeBlocks% "full/vectors/000101001-V-0002.bin"
private noncomputable def vp000101001_3 : Blocks := edgeBlocks% "full/vectors/000101001-V-0003.bin"
private noncomputable def vp000101001_4 : Blocks := edgeBlocks% "full/vectors/000101001-V-0004.bin"
noncomputable def vp000101001 : Blocks := (Blocks.join (Blocks.join vp000101001_0 vp000101001_1) (Blocks.join vp000101001_2 (Blocks.join vp000101001_3 vp000101001_4)))
private theorem bp0001010010 : Branch 0 (-655761639/16000000 : ℚ) vp000101001 := by
  apply branch_left_normalized (c:=vp0001010010) (k:=0) (m:=321) (by decide +kernel)
  rw [show 2*(-655761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-655761639/8000000 : ℚ) by norm_num]
  exact coverp0001010010
private noncomputable def ep0001010011_0 : Blocks := edgeBlocks% "full/vectors/0001010011-E-0000.bin"
private noncomputable def ep0001010011_1 : Blocks := edgeBlocks% "full/vectors/0001010011-E-0001.bin"
private noncomputable def ep0001010011_2 : Blocks := edgeBlocks% "full/vectors/0001010011-E-0002.bin"
private noncomputable def ep0001010011_3 : Blocks := edgeBlocks% "full/vectors/0001010011-E-0003.bin"
private noncomputable def ep0001010011_4 : Blocks := edgeBlocks% "full/vectors/0001010011-E-0004.bin"
noncomputable def ep0001010011 : Blocks := (Blocks.join (Blocks.join ep0001010011_0 ep0001010011_1) (Blocks.join ep0001010011_2 (Blocks.join ep0001010011_3 ep0001010011_4)))
private theorem idp0001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101001.list =
    C ((2:ℤ)^671) * horner X vp0001010011.list + horner X ep0001010011.list := by
  exact edge_identity (B := (2:ℤ)^1040) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010011 : Branch 1 (-655761639/16000000 : ℚ) vp000101001 := by
  apply branch_checked idp0001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-655761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-663761639/8000000 : ℚ) by norm_num]
  exact coverp0001010011
theorem coverp000101001 : Covers (-655761639/16000000 : ℚ) vp000101001 := join_branches bp0001010010 bp0001010011
private noncomputable def vp0001010001111_0 : Blocks := edgeBlocks% "full/vectors/0001010001111-V-0000.bin"
noncomputable def vp0001010001111 : Blocks := vp0001010001111_0
theorem coverp0001010001111 : Covers (-654761639/1000000 : ℚ) vp0001010001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010001110_0 : Blocks := edgeBlocks% "full/vectors/0001010001110-V-0000.bin"
noncomputable def vp0001010001110 : Blocks := vp0001010001110_0
theorem coverp0001010001110 : Covers (-653761639/1000000 : ℚ) vp0001010001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000101000111_0 : Blocks := edgeBlocks% "full/vectors/000101000111-V-0000.bin"
noncomputable def vp000101000111 : Blocks := vp000101000111_0
private theorem bp0001010001110 : Branch 0 (-653761639/2000000 : ℚ) vp000101000111 := by
  apply branch_left_normalized (c:=vp0001010001110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-653761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-653761639/1000000 : ℚ) by norm_num]
  exact coverp0001010001110
private noncomputable def ep0001010001111_0 : Blocks := edgeBlocks% "full/vectors/0001010001111-E-0000.bin"
noncomputable def ep0001010001111 : Blocks := ep0001010001111_0
private theorem idp0001010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101000111.list =
    C ((2:ℤ)^99) * horner X vp0001010001111.list + horner X ep0001010001111.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010001111 : Branch 1 (-653761639/2000000 : ℚ) vp000101000111 := by
  apply branch_checked idp0001010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-653761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-654761639/1000000 : ℚ) by norm_num]
  exact coverp0001010001111
theorem coverp000101000111 : Covers (-653761639/2000000 : ℚ) vp000101000111 := join_branches bp0001010001110 bp0001010001111
private noncomputable def vp0001010001101_0 : Blocks := edgeBlocks% "full/vectors/0001010001101-V-0000.bin"
noncomputable def vp0001010001101 : Blocks := vp0001010001101_0
theorem coverp0001010001101 : Covers (-652761639/1000000 : ℚ) vp0001010001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010001100_0 : Blocks := edgeBlocks% "full/vectors/0001010001100-V-0000.bin"
noncomputable def vp0001010001100 : Blocks := vp0001010001100_0
theorem coverp0001010001100 : Covers (-651761639/1000000 : ℚ) vp0001010001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000101000110_0 : Blocks := edgeBlocks% "full/vectors/000101000110-V-0000.bin"
noncomputable def vp000101000110 : Blocks := vp000101000110_0
private theorem bp0001010001100 : Branch 0 (-651761639/2000000 : ℚ) vp000101000110 := by
  apply branch_left_normalized (c:=vp0001010001100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-651761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-651761639/1000000 : ℚ) by norm_num]
  exact coverp0001010001100
private noncomputable def ep0001010001101_0 : Blocks := edgeBlocks% "full/vectors/0001010001101-E-0000.bin"
noncomputable def ep0001010001101 : Blocks := ep0001010001101_0
private theorem idp0001010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101000110.list =
    C ((2:ℤ)^101) * horner X vp0001010001101.list + horner X ep0001010001101.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010001101 : Branch 1 (-651761639/2000000 : ℚ) vp000101000110 := by
  apply branch_checked idp0001010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-651761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-652761639/1000000 : ℚ) by norm_num]
  exact coverp0001010001101
theorem coverp000101000110 : Covers (-651761639/2000000 : ℚ) vp000101000110 := join_branches bp0001010001100 bp0001010001101
private noncomputable def vp00010100011_0 : Blocks := edgeBlocks% "full/vectors/00010100011-V-0000.bin"
private noncomputable def vp00010100011_1 : Blocks := edgeBlocks% "full/vectors/00010100011-V-0001.bin"
noncomputable def vp00010100011 : Blocks := (Blocks.join vp00010100011_0 vp00010100011_1)
private theorem bp000101000110 : Branch 0 (-651761639/4000000 : ℚ) vp00010100011 := by
  apply branch_left_normalized (c:=vp000101000110) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-651761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-651761639/2000000 : ℚ) by norm_num]
  exact coverp000101000110
private noncomputable def ep000101000111_0 : Blocks := edgeBlocks% "full/vectors/000101000111-E-0000.bin"
private noncomputable def ep000101000111_1 : Blocks := edgeBlocks% "full/vectors/000101000111-E-0001.bin"
noncomputable def ep000101000111 : Blocks := (Blocks.join ep000101000111_0 ep000101000111_1)
private theorem idp000101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010100011.list =
    C ((2:ℤ)^185) * horner X vp000101000111.list + horner X ep000101000111.list := by
  exact edge_identity (B := (2:ℤ)^347) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101000111 : Branch 1 (-651761639/4000000 : ℚ) vp00010100011 := by
  apply branch_checked idp000101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-651761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-653761639/2000000 : ℚ) by norm_num]
  exact coverp000101000111
theorem coverp00010100011 : Covers (-651761639/4000000 : ℚ) vp00010100011 := join_branches bp000101000110 bp000101000111
private noncomputable def vp0001010001011_0 : Blocks := edgeBlocks% "full/vectors/0001010001011-V-0000.bin"
noncomputable def vp0001010001011 : Blocks := vp0001010001011_0
theorem coverp0001010001011 : Covers (-650761639/1000000 : ℚ) vp0001010001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010001010_0 : Blocks := edgeBlocks% "full/vectors/0001010001010-V-0000.bin"
noncomputable def vp0001010001010 : Blocks := vp0001010001010_0
theorem coverp0001010001010 : Covers (-649761639/1000000 : ℚ) vp0001010001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000101000101_0 : Blocks := edgeBlocks% "full/vectors/000101000101-V-0000.bin"
noncomputable def vp000101000101 : Blocks := vp000101000101_0
private theorem bp0001010001010 : Branch 0 (-649761639/2000000 : ℚ) vp000101000101 := by
  apply branch_left_normalized (c:=vp0001010001010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-649761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-649761639/1000000 : ℚ) by norm_num]
  exact coverp0001010001010
private noncomputable def ep0001010001011_0 : Blocks := edgeBlocks% "full/vectors/0001010001011-E-0000.bin"
noncomputable def ep0001010001011 : Blocks := ep0001010001011_0
private theorem idp0001010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101000101.list =
    C ((2:ℤ)^102) * horner X vp0001010001011.list + horner X ep0001010001011.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010001011 : Branch 1 (-649761639/2000000 : ℚ) vp000101000101 := by
  apply branch_checked idp0001010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-649761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-650761639/1000000 : ℚ) by norm_num]
  exact coverp0001010001011
theorem coverp000101000101 : Covers (-649761639/2000000 : ℚ) vp000101000101 := join_branches bp0001010001010 bp0001010001011
private noncomputable def vp0001010001001_0 : Blocks := edgeBlocks% "full/vectors/0001010001001-V-0000.bin"
noncomputable def vp0001010001001 : Blocks := vp0001010001001_0
theorem coverp0001010001001 : Covers (-648761639/1000000 : ℚ) vp0001010001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010001000_0 : Blocks := edgeBlocks% "full/vectors/0001010001000-V-0000.bin"
noncomputable def vp0001010001000 : Blocks := vp0001010001000_0
theorem coverp0001010001000 : Covers (-647761639/1000000 : ℚ) vp0001010001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000101000100_0 : Blocks := edgeBlocks% "full/vectors/000101000100-V-0000.bin"
noncomputable def vp000101000100 : Blocks := vp000101000100_0
private theorem bp0001010001000 : Branch 0 (-647761639/2000000 : ℚ) vp000101000100 := by
  apply branch_left_normalized (c:=vp0001010001000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-647761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-647761639/1000000 : ℚ) by norm_num]
  exact coverp0001010001000
private noncomputable def ep0001010001001_0 : Blocks := edgeBlocks% "full/vectors/0001010001001-E-0000.bin"
noncomputable def ep0001010001001 : Blocks := ep0001010001001_0
private theorem idp0001010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101000100.list =
    C ((2:ℤ)^104) * horner X vp0001010001001.list + horner X ep0001010001001.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010001001 : Branch 1 (-647761639/2000000 : ℚ) vp000101000100 := by
  apply branch_checked idp0001010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-647761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-648761639/1000000 : ℚ) by norm_num]
  exact coverp0001010001001
theorem coverp000101000100 : Covers (-647761639/2000000 : ℚ) vp000101000100 := join_branches bp0001010001000 bp0001010001001
private noncomputable def vp00010100010_0 : Blocks := edgeBlocks% "full/vectors/00010100010-V-0000.bin"
private noncomputable def vp00010100010_1 : Blocks := edgeBlocks% "full/vectors/00010100010-V-0001.bin"
noncomputable def vp00010100010 : Blocks := (Blocks.join vp00010100010_0 vp00010100010_1)
private theorem bp000101000100 : Branch 0 (-647761639/4000000 : ℚ) vp00010100010 := by
  apply branch_left_normalized (c:=vp000101000100) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-647761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-647761639/2000000 : ℚ) by norm_num]
  exact coverp000101000100
private noncomputable def ep000101000101_0 : Blocks := edgeBlocks% "full/vectors/000101000101-E-0000.bin"
private noncomputable def ep000101000101_1 : Blocks := edgeBlocks% "full/vectors/000101000101-E-0001.bin"
noncomputable def ep000101000101 : Blocks := (Blocks.join ep000101000101_0 ep000101000101_1)
private theorem idp000101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010100010.list =
    C ((2:ℤ)^189) * horner X vp000101000101.list + horner X ep000101000101.list := by
  exact edge_identity (B := (2:ℤ)^354) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101000101 : Branch 1 (-647761639/4000000 : ℚ) vp00010100010 := by
  apply branch_checked idp000101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-647761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-649761639/2000000 : ℚ) by norm_num]
  exact coverp000101000101
theorem coverp00010100010 : Covers (-647761639/4000000 : ℚ) vp00010100010 := join_branches bp000101000100 bp000101000101
private noncomputable def vp0001010001_0 : Blocks := edgeBlocks% "full/vectors/0001010001-V-0000.bin"
private noncomputable def vp0001010001_1 : Blocks := edgeBlocks% "full/vectors/0001010001-V-0001.bin"
private noncomputable def vp0001010001_2 : Blocks := edgeBlocks% "full/vectors/0001010001-V-0002.bin"
noncomputable def vp0001010001 : Blocks := (Blocks.join vp0001010001_0 (Blocks.join vp0001010001_1 vp0001010001_2))
private theorem bp00010100010 : Branch 0 (-647761639/8000000 : ℚ) vp0001010001 := by
  apply branch_left_normalized (c:=vp00010100010) (k:=0) (m:=174) (by decide +kernel)
  rw [show 2*(-647761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-647761639/4000000 : ℚ) by norm_num]
  exact coverp00010100010
private noncomputable def ep00010100011_0 : Blocks := edgeBlocks% "full/vectors/00010100011-E-0000.bin"
private noncomputable def ep00010100011_1 : Blocks := edgeBlocks% "full/vectors/00010100011-E-0001.bin"
private noncomputable def ep00010100011_2 : Blocks := edgeBlocks% "full/vectors/00010100011-E-0002.bin"
noncomputable def ep00010100011 : Blocks := (Blocks.join ep00010100011_0 (Blocks.join ep00010100011_1 ep00010100011_2))
private theorem idp00010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010001.list =
    C ((2:ℤ)^355) * horner X vp00010100011.list + horner X ep00010100011.list := by
  exact edge_identity (B := (2:ℤ)^589) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010100011 : Branch 1 (-647761639/8000000 : ℚ) vp0001010001 := by
  apply branch_checked idp00010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-647761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-651761639/4000000 : ℚ) by norm_num]
  exact coverp00010100011
theorem coverp0001010001 : Covers (-647761639/8000000 : ℚ) vp0001010001 := join_branches bp00010100010 bp00010100011
private noncomputable def vp0001010000111_0 : Blocks := edgeBlocks% "full/vectors/0001010000111-V-0000.bin"
noncomputable def vp0001010000111 : Blocks := vp0001010000111_0
theorem coverp0001010000111 : Covers (-646761639/1000000 : ℚ) vp0001010000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010100001101_0 : Blocks := edgeBlocks% "full/vectors/00010100001101-V-0000.bin"
noncomputable def vp00010100001101 : Blocks := vp00010100001101_0
theorem coverp00010100001101 : Covers (-646261639/500000 : ℚ) vp00010100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010100001100_0 : Blocks := edgeBlocks% "full/vectors/00010100001100-V-0000.bin"
noncomputable def vp00010100001100 : Blocks := vp00010100001100_0
theorem coverp00010100001100 : Covers (-645761639/500000 : ℚ) vp00010100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010000110_0 : Blocks := edgeBlocks% "full/vectors/0001010000110-V-0000.bin"
noncomputable def vp0001010000110 : Blocks := vp0001010000110_0
private theorem bp00010100001100 : Branch 0 (-645761639/1000000 : ℚ) vp0001010000110 := by
  apply branch_left_normalized (c:=vp00010100001100) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-645761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-645761639/500000 : ℚ) by norm_num]
  exact coverp00010100001100
private noncomputable def ep00010100001101_0 : Blocks := edgeBlocks% "full/vectors/00010100001101-E-0000.bin"
noncomputable def ep00010100001101 : Blocks := ep00010100001101_0
private theorem idp00010100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010000110.list =
    C ((2:ℤ)^61) * horner X vp00010100001101.list + horner X ep00010100001101.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010100001101 : Branch 1 (-645761639/1000000 : ℚ) vp0001010000110 := by
  apply branch_checked idp00010100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-645761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-646261639/500000 : ℚ) by norm_num]
  exact coverp00010100001101
theorem coverp0001010000110 : Covers (-645761639/1000000 : ℚ) vp0001010000110 := join_branches bp00010100001100 bp00010100001101
private noncomputable def vp000101000011_0 : Blocks := edgeBlocks% "full/vectors/000101000011-V-0000.bin"
noncomputable def vp000101000011 : Blocks := vp000101000011_0
private theorem bp0001010000110 : Branch 0 (-645761639/2000000 : ℚ) vp000101000011 := by
  apply branch_left_normalized (c:=vp0001010000110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-645761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-645761639/1000000 : ℚ) by norm_num]
  exact coverp0001010000110
private noncomputable def ep0001010000111_0 : Blocks := edgeBlocks% "full/vectors/0001010000111-E-0000.bin"
noncomputable def ep0001010000111 : Blocks := ep0001010000111_0
private theorem idp0001010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101000011.list =
    C ((2:ℤ)^106) * horner X vp0001010000111.list + horner X ep0001010000111.list := by
  exact edge_identity (B := (2:ℤ)^240) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010000111 : Branch 1 (-645761639/2000000 : ℚ) vp000101000011 := by
  apply branch_checked idp0001010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-645761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-646761639/1000000 : ℚ) by norm_num]
  exact coverp0001010000111
theorem coverp000101000011 : Covers (-645761639/2000000 : ℚ) vp000101000011 := join_branches bp0001010000110 bp0001010000111
private noncomputable def vp00010100001011_0 : Blocks := edgeBlocks% "full/vectors/00010100001011-V-0000.bin"
noncomputable def vp00010100001011 : Blocks := vp00010100001011_0
theorem coverp00010100001011 : Covers (-645261639/500000 : ℚ) vp00010100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010100001010_0 : Blocks := edgeBlocks% "full/vectors/00010100001010-V-0000.bin"
noncomputable def vp00010100001010 : Blocks := vp00010100001010_0
theorem coverp00010100001010 : Covers (-644761639/500000 : ℚ) vp00010100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010000101_0 : Blocks := edgeBlocks% "full/vectors/0001010000101-V-0000.bin"
noncomputable def vp0001010000101 : Blocks := vp0001010000101_0
private theorem bp00010100001010 : Branch 0 (-644761639/1000000 : ℚ) vp0001010000101 := by
  apply branch_left_normalized (c:=vp00010100001010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-644761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-644761639/500000 : ℚ) by norm_num]
  exact coverp00010100001010
private noncomputable def ep00010100001011_0 : Blocks := edgeBlocks% "full/vectors/00010100001011-E-0000.bin"
noncomputable def ep00010100001011 : Blocks := ep00010100001011_0
private theorem idp00010100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010000101.list =
    C ((2:ℤ)^63) * horner X vp00010100001011.list + horner X ep00010100001011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010100001011 : Branch 1 (-644761639/1000000 : ℚ) vp0001010000101 := by
  apply branch_checked idp00010100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-644761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-645261639/500000 : ℚ) by norm_num]
  exact coverp00010100001011
theorem coverp0001010000101 : Covers (-644761639/1000000 : ℚ) vp0001010000101 := join_branches bp00010100001010 bp00010100001011
private noncomputable def vp00010100001001_0 : Blocks := edgeBlocks% "full/vectors/00010100001001-V-0000.bin"
noncomputable def vp00010100001001 : Blocks := vp00010100001001_0
theorem coverp00010100001001 : Covers (-644261639/500000 : ℚ) vp00010100001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010100001000_0 : Blocks := edgeBlocks% "full/vectors/00010100001000-V-0000.bin"
noncomputable def vp00010100001000 : Blocks := vp00010100001000_0
theorem coverp00010100001000 : Covers (-643761639/500000 : ℚ) vp00010100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010000100_0 : Blocks := edgeBlocks% "full/vectors/0001010000100-V-0000.bin"
noncomputable def vp0001010000100 : Blocks := vp0001010000100_0
private theorem bp00010100001000 : Branch 0 (-643761639/1000000 : ℚ) vp0001010000100 := by
  apply branch_left_normalized (c:=vp00010100001000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-643761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-643761639/500000 : ℚ) by norm_num]
  exact coverp00010100001000
private noncomputable def ep00010100001001_0 : Blocks := edgeBlocks% "full/vectors/00010100001001-E-0000.bin"
noncomputable def ep00010100001001 : Blocks := ep00010100001001_0
private theorem idp00010100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010000100.list =
    C ((2:ℤ)^63) * horner X vp00010100001001.list + horner X ep00010100001001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010100001001 : Branch 1 (-643761639/1000000 : ℚ) vp0001010000100 := by
  apply branch_checked idp00010100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-643761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-644261639/500000 : ℚ) by norm_num]
  exact coverp00010100001001
theorem coverp0001010000100 : Covers (-643761639/1000000 : ℚ) vp0001010000100 := join_branches bp00010100001000 bp00010100001001
private noncomputable def vp000101000010_0 : Blocks := edgeBlocks% "full/vectors/000101000010-V-0000.bin"
noncomputable def vp000101000010 : Blocks := vp000101000010_0
private theorem bp0001010000100 : Branch 0 (-643761639/2000000 : ℚ) vp000101000010 := by
  apply branch_left_normalized (c:=vp0001010000100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-643761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-643761639/1000000 : ℚ) by norm_num]
  exact coverp0001010000100
private noncomputable def ep0001010000101_0 : Blocks := edgeBlocks% "full/vectors/0001010000101-E-0000.bin"
noncomputable def ep0001010000101 : Blocks := ep0001010000101_0
private theorem idp0001010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101000010.list =
    C ((2:ℤ)^106) * horner X vp0001010000101.list + horner X ep0001010000101.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010000101 : Branch 1 (-643761639/2000000 : ℚ) vp000101000010 := by
  apply branch_checked idp0001010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-643761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-644761639/1000000 : ℚ) by norm_num]
  exact coverp0001010000101
theorem coverp000101000010 : Covers (-643761639/2000000 : ℚ) vp000101000010 := join_branches bp0001010000100 bp0001010000101
private noncomputable def vp00010100001_0 : Blocks := edgeBlocks% "full/vectors/00010100001-V-0000.bin"
private noncomputable def vp00010100001_1 : Blocks := edgeBlocks% "full/vectors/00010100001-V-0001.bin"
noncomputable def vp00010100001 : Blocks := (Blocks.join vp00010100001_0 vp00010100001_1)
private theorem bp000101000010 : Branch 0 (-643761639/4000000 : ℚ) vp00010100001 := by
  apply branch_left_normalized (c:=vp000101000010) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-643761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-643761639/2000000 : ℚ) by norm_num]
  exact coverp000101000010
private noncomputable def ep000101000011_0 : Blocks := edgeBlocks% "full/vectors/000101000011-E-0000.bin"
private noncomputable def ep000101000011_1 : Blocks := edgeBlocks% "full/vectors/000101000011-E-0001.bin"
noncomputable def ep000101000011 : Blocks := (Blocks.join ep000101000011_0 ep000101000011_1)
private theorem idp000101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010100001.list =
    C ((2:ℤ)^192) * horner X vp000101000011.list + horner X ep000101000011.list := by
  exact edge_identity (B := (2:ℤ)^362) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101000011 : Branch 1 (-643761639/4000000 : ℚ) vp00010100001 := by
  apply branch_checked idp000101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-643761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-645761639/2000000 : ℚ) by norm_num]
  exact coverp000101000011
theorem coverp00010100001 : Covers (-643761639/4000000 : ℚ) vp00010100001 := join_branches bp000101000010 bp000101000011
private noncomputable def vp00010100000111_0 : Blocks := edgeBlocks% "full/vectors/00010100000111-V-0000.bin"
noncomputable def vp00010100000111 : Blocks := vp00010100000111_0
theorem coverp00010100000111 : Covers (-643261639/500000 : ℚ) vp00010100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010100000110_0 : Blocks := edgeBlocks% "full/vectors/00010100000110-V-0000.bin"
noncomputable def vp00010100000110 : Blocks := vp00010100000110_0
theorem coverp00010100000110 : Covers (-642761639/500000 : ℚ) vp00010100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010000011_0 : Blocks := edgeBlocks% "full/vectors/0001010000011-V-0000.bin"
noncomputable def vp0001010000011 : Blocks := vp0001010000011_0
private theorem bp00010100000110 : Branch 0 (-642761639/1000000 : ℚ) vp0001010000011 := by
  apply branch_left_normalized (c:=vp00010100000110) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-642761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-642761639/500000 : ℚ) by norm_num]
  exact coverp00010100000110
private noncomputable def ep00010100000111_0 : Blocks := edgeBlocks% "full/vectors/00010100000111-E-0000.bin"
noncomputable def ep00010100000111 : Blocks := ep00010100000111_0
private theorem idp00010100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010000011.list =
    C ((2:ℤ)^62) * horner X vp00010100000111.list + horner X ep00010100000111.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010100000111 : Branch 1 (-642761639/1000000 : ℚ) vp0001010000011 := by
  apply branch_checked idp00010100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-642761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-643261639/500000 : ℚ) by norm_num]
  exact coverp00010100000111
theorem coverp0001010000011 : Covers (-642761639/1000000 : ℚ) vp0001010000011 := join_branches bp00010100000110 bp00010100000111
private noncomputable def vp00010100000101_0 : Blocks := edgeBlocks% "full/vectors/00010100000101-V-0000.bin"
noncomputable def vp00010100000101 : Blocks := vp00010100000101_0
theorem coverp00010100000101 : Covers (-642261639/500000 : ℚ) vp00010100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010100000100_0 : Blocks := edgeBlocks% "full/vectors/00010100000100-V-0000.bin"
noncomputable def vp00010100000100 : Blocks := vp00010100000100_0
theorem coverp00010100000100 : Covers (-641761639/500000 : ℚ) vp00010100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010000010_0 : Blocks := edgeBlocks% "full/vectors/0001010000010-V-0000.bin"
noncomputable def vp0001010000010 : Blocks := vp0001010000010_0
private theorem bp00010100000100 : Branch 0 (-641761639/1000000 : ℚ) vp0001010000010 := by
  apply branch_left_normalized (c:=vp00010100000100) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-641761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-641761639/500000 : ℚ) by norm_num]
  exact coverp00010100000100
private noncomputable def ep00010100000101_0 : Blocks := edgeBlocks% "full/vectors/00010100000101-E-0000.bin"
noncomputable def ep00010100000101 : Blocks := ep00010100000101_0
private theorem idp00010100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010000010.list =
    C ((2:ℤ)^62) * horner X vp00010100000101.list + horner X ep00010100000101.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010100000101 : Branch 1 (-641761639/1000000 : ℚ) vp0001010000010 := by
  apply branch_checked idp00010100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-641761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-642261639/500000 : ℚ) by norm_num]
  exact coverp00010100000101
theorem coverp0001010000010 : Covers (-641761639/1000000 : ℚ) vp0001010000010 := join_branches bp00010100000100 bp00010100000101
private noncomputable def vp000101000001_0 : Blocks := edgeBlocks% "full/vectors/000101000001-V-0000.bin"
noncomputable def vp000101000001 : Blocks := vp000101000001_0
private theorem bp0001010000010 : Branch 0 (-641761639/2000000 : ℚ) vp000101000001 := by
  apply branch_left_normalized (c:=vp0001010000010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-641761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-641761639/1000000 : ℚ) by norm_num]
  exact coverp0001010000010
private noncomputable def ep0001010000011_0 : Blocks := edgeBlocks% "full/vectors/0001010000011-E-0000.bin"
noncomputable def ep0001010000011 : Blocks := ep0001010000011_0
private theorem idp0001010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101000001.list =
    C ((2:ℤ)^106) * horner X vp0001010000011.list + horner X ep0001010000011.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010000011 : Branch 1 (-641761639/2000000 : ℚ) vp000101000001 := by
  apply branch_checked idp0001010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-641761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-642761639/1000000 : ℚ) by norm_num]
  exact coverp0001010000011
theorem coverp000101000001 : Covers (-641761639/2000000 : ℚ) vp000101000001 := join_branches bp0001010000010 bp0001010000011
private noncomputable def vp00010100000011_0 : Blocks := edgeBlocks% "full/vectors/00010100000011-V-0000.bin"
noncomputable def vp00010100000011 : Blocks := vp00010100000011_0
theorem coverp00010100000011 : Covers (-641261639/500000 : ℚ) vp00010100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010100000010_0 : Blocks := edgeBlocks% "full/vectors/00010100000010-V-0000.bin"
noncomputable def vp00010100000010 : Blocks := vp00010100000010_0
theorem coverp00010100000010 : Covers (-640761639/500000 : ℚ) vp00010100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010000001_0 : Blocks := edgeBlocks% "full/vectors/0001010000001-V-0000.bin"
noncomputable def vp0001010000001 : Blocks := vp0001010000001_0
private theorem bp00010100000010 : Branch 0 (-640761639/1000000 : ℚ) vp0001010000001 := by
  apply branch_left_normalized (c:=vp00010100000010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-640761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-640761639/500000 : ℚ) by norm_num]
  exact coverp00010100000010
private noncomputable def ep00010100000011_0 : Blocks := edgeBlocks% "full/vectors/00010100000011-E-0000.bin"
noncomputable def ep00010100000011 : Blocks := ep00010100000011_0
private theorem idp00010100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010000001.list =
    C ((2:ℤ)^63) * horner X vp00010100000011.list + horner X ep00010100000011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010100000011 : Branch 1 (-640761639/1000000 : ℚ) vp0001010000001 := by
  apply branch_checked idp00010100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-640761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-641261639/500000 : ℚ) by norm_num]
  exact coverp00010100000011
theorem coverp0001010000001 : Covers (-640761639/1000000 : ℚ) vp0001010000001 := join_branches bp00010100000010 bp00010100000011
private noncomputable def vp00010100000001_0 : Blocks := edgeBlocks% "full/vectors/00010100000001-V-0000.bin"
noncomputable def vp00010100000001 : Blocks := vp00010100000001_0
theorem coverp00010100000001 : Covers (-640261639/500000 : ℚ) vp00010100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010100000000_0 : Blocks := edgeBlocks% "full/vectors/00010100000000-V-0000.bin"
noncomputable def vp00010100000000 : Blocks := vp00010100000000_0
theorem coverp00010100000000 : Covers (-639761639/500000 : ℚ) vp00010100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001010000000_0 : Blocks := edgeBlocks% "full/vectors/0001010000000-V-0000.bin"
noncomputable def vp0001010000000 : Blocks := vp0001010000000_0
private theorem bp00010100000000 : Branch 0 (-639761639/1000000 : ℚ) vp0001010000000 := by
  apply branch_left_normalized (c:=vp00010100000000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-639761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-639761639/500000 : ℚ) by norm_num]
  exact coverp00010100000000
private noncomputable def ep00010100000001_0 : Blocks := edgeBlocks% "full/vectors/00010100000001-E-0000.bin"
noncomputable def ep00010100000001 : Blocks := ep00010100000001_0
private theorem idp00010100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010000000.list =
    C ((2:ℤ)^63) * horner X vp00010100000001.list + horner X ep00010100000001.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010100000001 : Branch 1 (-639761639/1000000 : ℚ) vp0001010000000 := by
  apply branch_checked idp00010100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-639761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-640261639/500000 : ℚ) by norm_num]
  exact coverp00010100000001
theorem coverp0001010000000 : Covers (-639761639/1000000 : ℚ) vp0001010000000 := join_branches bp00010100000000 bp00010100000001
private noncomputable def vp000101000000_0 : Blocks := edgeBlocks% "full/vectors/000101000000-V-0000.bin"
noncomputable def vp000101000000 : Blocks := vp000101000000_0
private theorem bp0001010000000 : Branch 0 (-639761639/2000000 : ℚ) vp000101000000 := by
  apply branch_left_normalized (c:=vp0001010000000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-639761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-639761639/1000000 : ℚ) by norm_num]
  exact coverp0001010000000
private noncomputable def ep0001010000001_0 : Blocks := edgeBlocks% "full/vectors/0001010000001-E-0000.bin"
noncomputable def ep0001010000001 : Blocks := ep0001010000001_0
private theorem idp0001010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101000000.list =
    C ((2:ℤ)^106) * horner X vp0001010000001.list + horner X ep0001010000001.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010000001 : Branch 1 (-639761639/2000000 : ℚ) vp000101000000 := by
  apply branch_checked idp0001010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-639761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-640761639/1000000 : ℚ) by norm_num]
  exact coverp0001010000001
theorem coverp000101000000 : Covers (-639761639/2000000 : ℚ) vp000101000000 := join_branches bp0001010000000 bp0001010000001
private noncomputable def vp00010100000_0 : Blocks := edgeBlocks% "full/vectors/00010100000-V-0000.bin"
private noncomputable def vp00010100000_1 : Blocks := edgeBlocks% "full/vectors/00010100000-V-0001.bin"
noncomputable def vp00010100000 : Blocks := (Blocks.join vp00010100000_0 vp00010100000_1)
private theorem bp000101000000 : Branch 0 (-639761639/4000000 : ℚ) vp00010100000 := by
  apply branch_left_normalized (c:=vp000101000000) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-639761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-639761639/2000000 : ℚ) by norm_num]
  exact coverp000101000000
private noncomputable def ep000101000001_0 : Blocks := edgeBlocks% "full/vectors/000101000001-E-0000.bin"
private noncomputable def ep000101000001_1 : Blocks := edgeBlocks% "full/vectors/000101000001-E-0001.bin"
noncomputable def ep000101000001 : Blocks := (Blocks.join ep000101000001_0 ep000101000001_1)
private theorem idp000101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010100000.list =
    C ((2:ℤ)^191) * horner X vp000101000001.list + horner X ep000101000001.list := by
  exact edge_identity (B := (2:ℤ)^364) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101000001 : Branch 1 (-639761639/4000000 : ℚ) vp00010100000 := by
  apply branch_checked idp000101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-639761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-641761639/2000000 : ℚ) by norm_num]
  exact coverp000101000001
theorem coverp00010100000 : Covers (-639761639/4000000 : ℚ) vp00010100000 := join_branches bp000101000000 bp000101000001
private noncomputable def vp0001010000_0 : Blocks := edgeBlocks% "full/vectors/0001010000-V-0000.bin"
private noncomputable def vp0001010000_1 : Blocks := edgeBlocks% "full/vectors/0001010000-V-0001.bin"
private noncomputable def vp0001010000_2 : Blocks := edgeBlocks% "full/vectors/0001010000-V-0002.bin"
noncomputable def vp0001010000 : Blocks := (Blocks.join vp0001010000_0 (Blocks.join vp0001010000_1 vp0001010000_2))
private theorem bp00010100000 : Branch 0 (-639761639/8000000 : ℚ) vp0001010000 := by
  apply branch_left_normalized (c:=vp00010100000) (k:=0) (m:=178) (by decide +kernel)
  rw [show 2*(-639761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-639761639/4000000 : ℚ) by norm_num]
  exact coverp00010100000
private noncomputable def ep00010100001_0 : Blocks := edgeBlocks% "full/vectors/00010100001-E-0000.bin"
private noncomputable def ep00010100001_1 : Blocks := edgeBlocks% "full/vectors/00010100001-E-0001.bin"
private noncomputable def ep00010100001_2 : Blocks := edgeBlocks% "full/vectors/00010100001-E-0002.bin"
noncomputable def ep00010100001 : Blocks := (Blocks.join ep00010100001_0 (Blocks.join ep00010100001_1 ep00010100001_2))
private theorem idp00010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010000.list =
    C ((2:ℤ)^357) * horner X vp00010100001.list + horner X ep00010100001.list := by
  exact edge_identity (B := (2:ℤ)^601) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010100001 : Branch 1 (-639761639/8000000 : ℚ) vp0001010000 := by
  apply branch_checked idp00010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-639761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-643761639/4000000 : ℚ) by norm_num]
  exact coverp00010100001
theorem coverp0001010000 : Covers (-639761639/8000000 : ℚ) vp0001010000 := join_branches bp00010100000 bp00010100001
private noncomputable def vp000101000_0 : Blocks := edgeBlocks% "full/vectors/000101000-V-0000.bin"
private noncomputable def vp000101000_1 : Blocks := edgeBlocks% "full/vectors/000101000-V-0001.bin"
private noncomputable def vp000101000_2 : Blocks := edgeBlocks% "full/vectors/000101000-V-0002.bin"
private noncomputable def vp000101000_3 : Blocks := edgeBlocks% "full/vectors/000101000-V-0003.bin"
private noncomputable def vp000101000_4 : Blocks := edgeBlocks% "full/vectors/000101000-V-0004.bin"
noncomputable def vp000101000 : Blocks := (Blocks.join (Blocks.join vp000101000_0 vp000101000_1) (Blocks.join vp000101000_2 (Blocks.join vp000101000_3 vp000101000_4)))
private theorem bp0001010000 : Branch 0 (-639761639/16000000 : ℚ) vp000101000 := by
  apply branch_left_normalized (c:=vp0001010000) (k:=0) (m:=333) (by decide +kernel)
  rw [show 2*(-639761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-639761639/8000000 : ℚ) by norm_num]
  exact coverp0001010000
private noncomputable def ep0001010001_0 : Blocks := edgeBlocks% "full/vectors/0001010001-E-0000.bin"
private noncomputable def ep0001010001_1 : Blocks := edgeBlocks% "full/vectors/0001010001-E-0001.bin"
private noncomputable def ep0001010001_2 : Blocks := edgeBlocks% "full/vectors/0001010001-E-0002.bin"
private noncomputable def ep0001010001_3 : Blocks := edgeBlocks% "full/vectors/0001010001-E-0003.bin"
private noncomputable def ep0001010001_4 : Blocks := edgeBlocks% "full/vectors/0001010001-E-0004.bin"
noncomputable def ep0001010001 : Blocks := (Blocks.join (Blocks.join ep0001010001_0 ep0001010001_1) (Blocks.join ep0001010001_2 (Blocks.join ep0001010001_3 ep0001010001_4)))
private theorem idp0001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101000.list =
    C ((2:ℤ)^691) * horner X vp0001010001.list + horner X ep0001010001.list := by
  exact edge_identity (B := (2:ℤ)^1071) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001010001 : Branch 1 (-639761639/16000000 : ℚ) vp000101000 := by
  apply branch_checked idp0001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-639761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-647761639/8000000 : ℚ) by norm_num]
  exact coverp0001010001
theorem coverp000101000 : Covers (-639761639/16000000 : ℚ) vp000101000 := join_branches bp0001010000 bp0001010001
private noncomputable def vp00010100_0 : Blocks := edgeBlocks% "full/vectors/00010100-V-0000.bin"
private noncomputable def vp00010100_1 : Blocks := edgeBlocks% "full/vectors/00010100-V-0001.bin"
private noncomputable def vp00010100_2 : Blocks := edgeBlocks% "full/vectors/00010100-V-0002.bin"
private noncomputable def vp00010100_3 : Blocks := edgeBlocks% "full/vectors/00010100-V-0003.bin"
private noncomputable def vp00010100_4 : Blocks := edgeBlocks% "full/vectors/00010100-V-0004.bin"
private noncomputable def vp00010100_5 : Blocks := edgeBlocks% "full/vectors/00010100-V-0005.bin"
private noncomputable def vp00010100_6 : Blocks := edgeBlocks% "full/vectors/00010100-V-0006.bin"
private noncomputable def vp00010100_7 : Blocks := edgeBlocks% "full/vectors/00010100-V-0007.bin"
private noncomputable def vp00010100_8 : Blocks := edgeBlocks% "full/vectors/00010100-V-0008.bin"
private noncomputable def vp00010100_9 : Blocks := edgeBlocks% "full/vectors/00010100-V-0009.bin"
noncomputable def vp00010100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00010100_0 vp00010100_1) (Blocks.join vp00010100_2 (Blocks.join vp00010100_3 vp00010100_4))) (Blocks.join (Blocks.join vp00010100_5 vp00010100_6) (Blocks.join vp00010100_7 (Blocks.join vp00010100_8 vp00010100_9))))
private theorem bp000101000 : Branch 0 (-639761639/32000000 : ℚ) vp00010100 := by
  apply branch_left_normalized (c:=vp000101000) (k:=0) (m:=639) (by decide +kernel)
  rw [show 2*(-639761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-639761639/16000000 : ℚ) by norm_num]
  exact coverp000101000
private noncomputable def ep000101001_0 : Blocks := edgeBlocks% "full/vectors/000101001-E-0000.bin"
private noncomputable def ep000101001_1 : Blocks := edgeBlocks% "full/vectors/000101001-E-0001.bin"
private noncomputable def ep000101001_2 : Blocks := edgeBlocks% "full/vectors/000101001-E-0002.bin"
private noncomputable def ep000101001_3 : Blocks := edgeBlocks% "full/vectors/000101001-E-0003.bin"
private noncomputable def ep000101001_4 : Blocks := edgeBlocks% "full/vectors/000101001-E-0004.bin"
private noncomputable def ep000101001_5 : Blocks := edgeBlocks% "full/vectors/000101001-E-0005.bin"
private noncomputable def ep000101001_6 : Blocks := edgeBlocks% "full/vectors/000101001-E-0006.bin"
private noncomputable def ep000101001_7 : Blocks := edgeBlocks% "full/vectors/000101001-E-0007.bin"
private noncomputable def ep000101001_8 : Blocks := edgeBlocks% "full/vectors/000101001-E-0008.bin"
private noncomputable def ep000101001_9 : Blocks := edgeBlocks% "full/vectors/000101001-E-0009.bin"
noncomputable def ep000101001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000101001_0 ep000101001_1) (Blocks.join ep000101001_2 (Blocks.join ep000101001_3 ep000101001_4))) (Blocks.join (Blocks.join ep000101001_5 ep000101001_6) (Blocks.join ep000101001_7 (Blocks.join ep000101001_8 ep000101001_9))))
private theorem idp000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010100.list =
    C ((2:ℤ)^1348) * horner X vp000101001.list + horner X ep000101001.list := by
  exact edge_identity (B := (2:ℤ)^2002) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101001 : Branch 1 (-639761639/32000000 : ℚ) vp00010100 := by
  apply branch_checked idp000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-639761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-655761639/16000000 : ℚ) by norm_num]
  exact coverp000101001
theorem coverp00010100 : Covers (-639761639/32000000 : ℚ) vp00010100 := join_branches bp000101000 bp000101001
private noncomputable def vp0001010_0 : Blocks := edgeBlocks% "full/vectors/0001010-V-0000.bin"
private noncomputable def vp0001010_1 : Blocks := edgeBlocks% "full/vectors/0001010-V-0001.bin"
private noncomputable def vp0001010_2 : Blocks := edgeBlocks% "full/vectors/0001010-V-0002.bin"
private noncomputable def vp0001010_3 : Blocks := edgeBlocks% "full/vectors/0001010-V-0003.bin"
private noncomputable def vp0001010_4 : Blocks := edgeBlocks% "full/vectors/0001010-V-0004.bin"
private noncomputable def vp0001010_5 : Blocks := edgeBlocks% "full/vectors/0001010-V-0005.bin"
private noncomputable def vp0001010_6 : Blocks := edgeBlocks% "full/vectors/0001010-V-0006.bin"
private noncomputable def vp0001010_7 : Blocks := edgeBlocks% "full/vectors/0001010-V-0007.bin"
private noncomputable def vp0001010_8 : Blocks := edgeBlocks% "full/vectors/0001010-V-0008.bin"
private noncomputable def vp0001010_9 : Blocks := edgeBlocks% "full/vectors/0001010-V-0009.bin"
private noncomputable def vp0001010_10 : Blocks := edgeBlocks% "full/vectors/0001010-V-0010.bin"
private noncomputable def vp0001010_11 : Blocks := edgeBlocks% "full/vectors/0001010-V-0011.bin"
private noncomputable def vp0001010_12 : Blocks := edgeBlocks% "full/vectors/0001010-V-0012.bin"
private noncomputable def vp0001010_13 : Blocks := edgeBlocks% "full/vectors/0001010-V-0013.bin"
private noncomputable def vp0001010_14 : Blocks := edgeBlocks% "full/vectors/0001010-V-0014.bin"
private noncomputable def vp0001010_15 : Blocks := edgeBlocks% "full/vectors/0001010-V-0015.bin"
private noncomputable def vp0001010_16 : Blocks := edgeBlocks% "full/vectors/0001010-V-0016.bin"
private noncomputable def vp0001010_17 : Blocks := edgeBlocks% "full/vectors/0001010-V-0017.bin"
private noncomputable def vp0001010_18 : Blocks := edgeBlocks% "full/vectors/0001010-V-0018.bin"
noncomputable def vp0001010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0001010_0 vp0001010_1) (Blocks.join vp0001010_2 vp0001010_3)) (Blocks.join (Blocks.join vp0001010_4 vp0001010_5) (Blocks.join vp0001010_6 (Blocks.join vp0001010_7 vp0001010_8)))) (Blocks.join (Blocks.join (Blocks.join vp0001010_9 vp0001010_10) (Blocks.join vp0001010_11 (Blocks.join vp0001010_12 vp0001010_13))) (Blocks.join (Blocks.join vp0001010_14 vp0001010_15) (Blocks.join vp0001010_16 (Blocks.join vp0001010_17 vp0001010_18)))))
private theorem bp00010100 : Branch 0 (-639761639/64000000 : ℚ) vp0001010 := by
  apply branch_left_normalized (c:=vp00010100) (k:=0) (m:=1243) (by decide +kernel)
  rw [show 2*(-639761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-639761639/32000000 : ℚ) by norm_num]
  exact coverp00010100
private noncomputable def ep00010101_0 : Blocks := edgeBlocks% "full/vectors/00010101-E-0000.bin"
private noncomputable def ep00010101_1 : Blocks := edgeBlocks% "full/vectors/00010101-E-0001.bin"
private noncomputable def ep00010101_2 : Blocks := edgeBlocks% "full/vectors/00010101-E-0002.bin"
private noncomputable def ep00010101_3 : Blocks := edgeBlocks% "full/vectors/00010101-E-0003.bin"
private noncomputable def ep00010101_4 : Blocks := edgeBlocks% "full/vectors/00010101-E-0004.bin"
private noncomputable def ep00010101_5 : Blocks := edgeBlocks% "full/vectors/00010101-E-0005.bin"
private noncomputable def ep00010101_6 : Blocks := edgeBlocks% "full/vectors/00010101-E-0006.bin"
private noncomputable def ep00010101_7 : Blocks := edgeBlocks% "full/vectors/00010101-E-0007.bin"
private noncomputable def ep00010101_8 : Blocks := edgeBlocks% "full/vectors/00010101-E-0008.bin"
private noncomputable def ep00010101_9 : Blocks := edgeBlocks% "full/vectors/00010101-E-0009.bin"
private noncomputable def ep00010101_10 : Blocks := edgeBlocks% "full/vectors/00010101-E-0010.bin"
private noncomputable def ep00010101_11 : Blocks := edgeBlocks% "full/vectors/00010101-E-0011.bin"
private noncomputable def ep00010101_12 : Blocks := edgeBlocks% "full/vectors/00010101-E-0012.bin"
private noncomputable def ep00010101_13 : Blocks := edgeBlocks% "full/vectors/00010101-E-0013.bin"
private noncomputable def ep00010101_14 : Blocks := edgeBlocks% "full/vectors/00010101-E-0014.bin"
private noncomputable def ep00010101_15 : Blocks := edgeBlocks% "full/vectors/00010101-E-0015.bin"
private noncomputable def ep00010101_16 : Blocks := edgeBlocks% "full/vectors/00010101-E-0016.bin"
private noncomputable def ep00010101_17 : Blocks := edgeBlocks% "full/vectors/00010101-E-0017.bin"
private noncomputable def ep00010101_18 : Blocks := edgeBlocks% "full/vectors/00010101-E-0018.bin"
noncomputable def ep00010101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00010101_0 ep00010101_1) (Blocks.join ep00010101_2 ep00010101_3)) (Blocks.join (Blocks.join ep00010101_4 ep00010101_5) (Blocks.join ep00010101_6 (Blocks.join ep00010101_7 ep00010101_8)))) (Blocks.join (Blocks.join (Blocks.join ep00010101_9 ep00010101_10) (Blocks.join ep00010101_11 (Blocks.join ep00010101_12 ep00010101_13))) (Blocks.join (Blocks.join ep00010101_14 ep00010101_15) (Blocks.join ep00010101_16 (Blocks.join ep00010101_17 ep00010101_18)))))
private theorem idp00010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001010.list =
    C ((2:ℤ)^2612) * horner X vp00010101.list + horner X ep00010101.list := by
  exact edge_identity (B := (2:ℤ)^3824) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010101 : Branch 1 (-639761639/64000000 : ℚ) vp0001010 := by
  apply branch_checked idp00010101 (by positivity) (by decide +kernel)
  rw [show 2*(-639761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-671761639/32000000 : ℚ) by norm_num]
  exact coverp00010101
theorem coverp0001010 : Covers (-639761639/64000000 : ℚ) vp0001010 := join_branches bp00010100 bp00010101
end NextProof.EdgeFull

