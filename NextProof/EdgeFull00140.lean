import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp1100111111_0 : Blocks := edgeBlocks% "full/vectors/1100111111-V-0000.bin"
noncomputable def vp1100111111 : Blocks := vp1100111111_0
theorem coverp1100111111 : Covers (-6647761639/8000000 : ℚ) vp1100111111 := cover_leaf (by decide +kernel)
private noncomputable def vp1100111110_0 : Blocks := edgeBlocks% "full/vectors/1100111110-V-0000.bin"
noncomputable def vp1100111110 : Blocks := vp1100111110_0
theorem coverp1100111110 : Covers (-6639761639/8000000 : ℚ) vp1100111110 := cover_leaf (by decide +kernel)
private noncomputable def vp110011111_0 : Blocks := edgeBlocks% "full/vectors/110011111-V-0000.bin"
private noncomputable def vp110011111_1 : Blocks := edgeBlocks% "full/vectors/110011111-V-0001.bin"
noncomputable def vp110011111 : Blocks := (Blocks.join vp110011111_0 vp110011111_1)
private theorem bp1100111110 : Branch 0 (-6639761639/16000000 : ℚ) vp110011111 := by
  apply branch_left_normalized (c:=vp1100111110) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-6639761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6639761639/8000000 : ℚ) by norm_num]
  exact coverp1100111110
private noncomputable def ep1100111111_0 : Blocks := edgeBlocks% "full/vectors/1100111111-E-0000.bin"
private noncomputable def ep1100111111_1 : Blocks := edgeBlocks% "full/vectors/1100111111-E-0001.bin"
noncomputable def ep1100111111 : Blocks := (Blocks.join ep1100111111_0 ep1100111111_1)
private theorem idp1100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110011111.list =
    C ((2:ℤ)^263) * horner X vp1100111111.list + horner X ep1100111111.list := by
  exact edge_identity (B := (2:ℤ)^421) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100111111 : Branch 1 (-6639761639/16000000 : ℚ) vp110011111 := by
  apply branch_checked idp1100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-6639761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6647761639/8000000 : ℚ) by norm_num]
  exact coverp1100111111
theorem coverp110011111 : Covers (-6639761639/16000000 : ℚ) vp110011111 := join_branches bp1100111110 bp1100111111
private noncomputable def vp1100111101_0 : Blocks := edgeBlocks% "full/vectors/1100111101-V-0000.bin"
noncomputable def vp1100111101 : Blocks := vp1100111101_0
theorem coverp1100111101 : Covers (-6631761639/8000000 : ℚ) vp1100111101 := cover_leaf (by decide +kernel)
private noncomputable def vp1100111100_0 : Blocks := edgeBlocks% "full/vectors/1100111100-V-0000.bin"
noncomputable def vp1100111100 : Blocks := vp1100111100_0
theorem coverp1100111100 : Covers (-6623761639/8000000 : ℚ) vp1100111100 := cover_leaf (by decide +kernel)
private noncomputable def vp110011110_0 : Blocks := edgeBlocks% "full/vectors/110011110-V-0000.bin"
private noncomputable def vp110011110_1 : Blocks := edgeBlocks% "full/vectors/110011110-V-0001.bin"
noncomputable def vp110011110 : Blocks := (Blocks.join vp110011110_0 vp110011110_1)
private theorem bp1100111100 : Branch 0 (-6623761639/16000000 : ℚ) vp110011110 := by
  apply branch_left_normalized (c:=vp1100111100) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-6623761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6623761639/8000000 : ℚ) by norm_num]
  exact coverp1100111100
private noncomputable def ep1100111101_0 : Blocks := edgeBlocks% "full/vectors/1100111101-E-0000.bin"
private noncomputable def ep1100111101_1 : Blocks := edgeBlocks% "full/vectors/1100111101-E-0001.bin"
noncomputable def ep1100111101 : Blocks := (Blocks.join ep1100111101_0 ep1100111101_1)
private theorem idp1100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110011110.list =
    C ((2:ℤ)^263) * horner X vp1100111101.list + horner X ep1100111101.list := by
  exact edge_identity (B := (2:ℤ)^422) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100111101 : Branch 1 (-6623761639/16000000 : ℚ) vp110011110 := by
  apply branch_checked idp1100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-6623761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6631761639/8000000 : ℚ) by norm_num]
  exact coverp1100111101
theorem coverp110011110 : Covers (-6623761639/16000000 : ℚ) vp110011110 := join_branches bp1100111100 bp1100111101
private noncomputable def vp11001111_0 : Blocks := edgeBlocks% "full/vectors/11001111-V-0000.bin"
private noncomputable def vp11001111_1 : Blocks := edgeBlocks% "full/vectors/11001111-V-0001.bin"
private noncomputable def vp11001111_2 : Blocks := edgeBlocks% "full/vectors/11001111-V-0002.bin"
private noncomputable def vp11001111_3 : Blocks := edgeBlocks% "full/vectors/11001111-V-0003.bin"
noncomputable def vp11001111 : Blocks := (Blocks.join (Blocks.join vp11001111_0 vp11001111_1) (Blocks.join vp11001111_2 vp11001111_3))
private theorem bp110011110 : Branch 0 (-6623761639/32000000 : ℚ) vp11001111 := by
  apply branch_left_normalized (c:=vp110011110) (k:=0) (m:=216) (by decide +kernel)
  rw [show 2*(-6623761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6623761639/16000000 : ℚ) by norm_num]
  exact coverp110011110
private noncomputable def ep110011111_0 : Blocks := edgeBlocks% "full/vectors/110011111-E-0000.bin"
private noncomputable def ep110011111_1 : Blocks := edgeBlocks% "full/vectors/110011111-E-0001.bin"
private noncomputable def ep110011111_2 : Blocks := edgeBlocks% "full/vectors/110011111-E-0002.bin"
private noncomputable def ep110011111_3 : Blocks := edgeBlocks% "full/vectors/110011111-E-0003.bin"
noncomputable def ep110011111 : Blocks := (Blocks.join (Blocks.join ep110011111_0 ep110011111_1) (Blocks.join ep110011111_2 ep110011111_3))
private theorem idp110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11001111.list =
    C ((2:ℤ)^501) * horner X vp110011111.list + horner X ep110011111.list := by
  exact edge_identity (B := (2:ℤ)^716) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110011111 : Branch 1 (-6623761639/32000000 : ℚ) vp11001111 := by
  apply branch_checked idp110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-6623761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6639761639/16000000 : ℚ) by norm_num]
  exact coverp110011111
theorem coverp11001111 : Covers (-6623761639/32000000 : ℚ) vp11001111 := join_branches bp110011110 bp110011111
private noncomputable def vp1100111011_0 : Blocks := edgeBlocks% "full/vectors/1100111011-V-0000.bin"
noncomputable def vp1100111011 : Blocks := vp1100111011_0
theorem coverp1100111011 : Covers (-6615761639/8000000 : ℚ) vp1100111011 := cover_leaf (by decide +kernel)
private noncomputable def vp1100111010_0 : Blocks := edgeBlocks% "full/vectors/1100111010-V-0000.bin"
noncomputable def vp1100111010 : Blocks := vp1100111010_0
theorem coverp1100111010 : Covers (-6607761639/8000000 : ℚ) vp1100111010 := cover_leaf (by decide +kernel)
private noncomputable def vp110011101_0 : Blocks := edgeBlocks% "full/vectors/110011101-V-0000.bin"
private noncomputable def vp110011101_1 : Blocks := edgeBlocks% "full/vectors/110011101-V-0001.bin"
noncomputable def vp110011101 : Blocks := (Blocks.join vp110011101_0 vp110011101_1)
private theorem bp1100111010 : Branch 0 (-6607761639/16000000 : ℚ) vp110011101 := by
  apply branch_left_normalized (c:=vp1100111010) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-6607761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6607761639/8000000 : ℚ) by norm_num]
  exact coverp1100111010
private noncomputable def ep1100111011_0 : Blocks := edgeBlocks% "full/vectors/1100111011-E-0000.bin"
private noncomputable def ep1100111011_1 : Blocks := edgeBlocks% "full/vectors/1100111011-E-0001.bin"
noncomputable def ep1100111011 : Blocks := (Blocks.join ep1100111011_0 ep1100111011_1)
private theorem idp1100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110011101.list =
    C ((2:ℤ)^263) * horner X vp1100111011.list + horner X ep1100111011.list := by
  exact edge_identity (B := (2:ℤ)^422) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100111011 : Branch 1 (-6607761639/16000000 : ℚ) vp110011101 := by
  apply branch_checked idp1100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-6607761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6615761639/8000000 : ℚ) by norm_num]
  exact coverp1100111011
theorem coverp110011101 : Covers (-6607761639/16000000 : ℚ) vp110011101 := join_branches bp1100111010 bp1100111011
private noncomputable def vp1100111001_0 : Blocks := edgeBlocks% "full/vectors/1100111001-V-0000.bin"
noncomputable def vp1100111001 : Blocks := vp1100111001_0
theorem coverp1100111001 : Covers (-6599761639/8000000 : ℚ) vp1100111001 := cover_leaf (by decide +kernel)
private noncomputable def vp1100111000_0 : Blocks := edgeBlocks% "full/vectors/1100111000-V-0000.bin"
noncomputable def vp1100111000 : Blocks := vp1100111000_0
theorem coverp1100111000 : Covers (-6591761639/8000000 : ℚ) vp1100111000 := cover_leaf (by decide +kernel)
private noncomputable def vp110011100_0 : Blocks := edgeBlocks% "full/vectors/110011100-V-0000.bin"
private noncomputable def vp110011100_1 : Blocks := edgeBlocks% "full/vectors/110011100-V-0001.bin"
noncomputable def vp110011100 : Blocks := (Blocks.join vp110011100_0 vp110011100_1)
private theorem bp1100111000 : Branch 0 (-6591761639/16000000 : ℚ) vp110011100 := by
  apply branch_left_normalized (c:=vp1100111000) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-6591761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6591761639/8000000 : ℚ) by norm_num]
  exact coverp1100111000
private noncomputable def ep1100111001_0 : Blocks := edgeBlocks% "full/vectors/1100111001-E-0000.bin"
private noncomputable def ep1100111001_1 : Blocks := edgeBlocks% "full/vectors/1100111001-E-0001.bin"
noncomputable def ep1100111001 : Blocks := (Blocks.join ep1100111001_0 ep1100111001_1)
private theorem idp1100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110011100.list =
    C ((2:ℤ)^263) * horner X vp1100111001.list + horner X ep1100111001.list := by
  exact edge_identity (B := (2:ℤ)^422) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100111001 : Branch 1 (-6591761639/16000000 : ℚ) vp110011100 := by
  apply branch_checked idp1100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-6591761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6599761639/8000000 : ℚ) by norm_num]
  exact coverp1100111001
theorem coverp110011100 : Covers (-6591761639/16000000 : ℚ) vp110011100 := join_branches bp1100111000 bp1100111001
private noncomputable def vp11001110_0 : Blocks := edgeBlocks% "full/vectors/11001110-V-0000.bin"
private noncomputable def vp11001110_1 : Blocks := edgeBlocks% "full/vectors/11001110-V-0001.bin"
private noncomputable def vp11001110_2 : Blocks := edgeBlocks% "full/vectors/11001110-V-0002.bin"
private noncomputable def vp11001110_3 : Blocks := edgeBlocks% "full/vectors/11001110-V-0003.bin"
noncomputable def vp11001110 : Blocks := (Blocks.join (Blocks.join vp11001110_0 vp11001110_1) (Blocks.join vp11001110_2 vp11001110_3))
private theorem bp110011100 : Branch 0 (-6591761639/32000000 : ℚ) vp11001110 := by
  apply branch_left_normalized (c:=vp110011100) (k:=0) (m:=216) (by decide +kernel)
  rw [show 2*(-6591761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6591761639/16000000 : ℚ) by norm_num]
  exact coverp110011100
private noncomputable def ep110011101_0 : Blocks := edgeBlocks% "full/vectors/110011101-E-0000.bin"
private noncomputable def ep110011101_1 : Blocks := edgeBlocks% "full/vectors/110011101-E-0001.bin"
private noncomputable def ep110011101_2 : Blocks := edgeBlocks% "full/vectors/110011101-E-0002.bin"
private noncomputable def ep110011101_3 : Blocks := edgeBlocks% "full/vectors/110011101-E-0003.bin"
noncomputable def ep110011101 : Blocks := (Blocks.join (Blocks.join ep110011101_0 ep110011101_1) (Blocks.join ep110011101_2 ep110011101_3))
private theorem idp110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11001110.list =
    C ((2:ℤ)^502) * horner X vp110011101.list + horner X ep110011101.list := by
  exact edge_identity (B := (2:ℤ)^717) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110011101 : Branch 1 (-6591761639/32000000 : ℚ) vp11001110 := by
  apply branch_checked idp110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-6591761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6607761639/16000000 : ℚ) by norm_num]
  exact coverp110011101
theorem coverp11001110 : Covers (-6591761639/32000000 : ℚ) vp11001110 := join_branches bp110011100 bp110011101
private noncomputable def vp1100111_0 : Blocks := edgeBlocks% "full/vectors/1100111-V-0000.bin"
private noncomputable def vp1100111_1 : Blocks := edgeBlocks% "full/vectors/1100111-V-0001.bin"
private noncomputable def vp1100111_2 : Blocks := edgeBlocks% "full/vectors/1100111-V-0002.bin"
private noncomputable def vp1100111_3 : Blocks := edgeBlocks% "full/vectors/1100111-V-0003.bin"
private noncomputable def vp1100111_4 : Blocks := edgeBlocks% "full/vectors/1100111-V-0004.bin"
private noncomputable def vp1100111_5 : Blocks := edgeBlocks% "full/vectors/1100111-V-0005.bin"
private noncomputable def vp1100111_6 : Blocks := edgeBlocks% "full/vectors/1100111-V-0006.bin"
noncomputable def vp1100111 : Blocks := (Blocks.join (Blocks.join vp1100111_0 (Blocks.join vp1100111_1 vp1100111_2)) (Blocks.join (Blocks.join vp1100111_3 vp1100111_4) (Blocks.join vp1100111_5 vp1100111_6)))
private theorem bp11001110 : Branch 0 (-6591761639/64000000 : ℚ) vp1100111 := by
  apply branch_left_normalized (c:=vp11001110) (k:=0) (m:=409) (by decide +kernel)
  rw [show 2*(-6591761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6591761639/32000000 : ℚ) by norm_num]
  exact coverp11001110
private noncomputable def ep11001111_0 : Blocks := edgeBlocks% "full/vectors/11001111-E-0000.bin"
private noncomputable def ep11001111_1 : Blocks := edgeBlocks% "full/vectors/11001111-E-0001.bin"
private noncomputable def ep11001111_2 : Blocks := edgeBlocks% "full/vectors/11001111-E-0002.bin"
private noncomputable def ep11001111_3 : Blocks := edgeBlocks% "full/vectors/11001111-E-0003.bin"
private noncomputable def ep11001111_4 : Blocks := edgeBlocks% "full/vectors/11001111-E-0004.bin"
private noncomputable def ep11001111_5 : Blocks := edgeBlocks% "full/vectors/11001111-E-0005.bin"
private noncomputable def ep11001111_6 : Blocks := edgeBlocks% "full/vectors/11001111-E-0006.bin"
noncomputable def ep11001111 : Blocks := (Blocks.join (Blocks.join ep11001111_0 (Blocks.join ep11001111_1 ep11001111_2)) (Blocks.join (Blocks.join ep11001111_3 ep11001111_4) (Blocks.join ep11001111_5 ep11001111_6)))
private theorem idp11001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1100111.list =
    C ((2:ℤ)^974) * horner X vp11001111.list + horner X ep11001111.list := by
  exact edge_identity (B := (2:ℤ)^1302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11001111 : Branch 1 (-6591761639/64000000 : ℚ) vp1100111 := by
  apply branch_checked idp11001111 (by positivity) (by decide +kernel)
  rw [show 2*(-6591761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6623761639/32000000 : ℚ) by norm_num]
  exact coverp11001111
theorem coverp1100111 : Covers (-6591761639/64000000 : ℚ) vp1100111 := join_branches bp11001110 bp11001111
private noncomputable def vp1100110111_0 : Blocks := edgeBlocks% "full/vectors/1100110111-V-0000.bin"
noncomputable def vp1100110111 : Blocks := vp1100110111_0
theorem coverp1100110111 : Covers (-6583761639/8000000 : ℚ) vp1100110111 := cover_leaf (by decide +kernel)
private noncomputable def vp1100110110_0 : Blocks := edgeBlocks% "full/vectors/1100110110-V-0000.bin"
noncomputable def vp1100110110 : Blocks := vp1100110110_0
theorem coverp1100110110 : Covers (-6575761639/8000000 : ℚ) vp1100110110 := cover_leaf (by decide +kernel)
private noncomputable def vp110011011_0 : Blocks := edgeBlocks% "full/vectors/110011011-V-0000.bin"
private noncomputable def vp110011011_1 : Blocks := edgeBlocks% "full/vectors/110011011-V-0001.bin"
noncomputable def vp110011011 : Blocks := (Blocks.join vp110011011_0 vp110011011_1)
private theorem bp1100110110 : Branch 0 (-6575761639/16000000 : ℚ) vp110011011 := by
  apply branch_left_normalized (c:=vp1100110110) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-6575761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6575761639/8000000 : ℚ) by norm_num]
  exact coverp1100110110
private noncomputable def ep1100110111_0 : Blocks := edgeBlocks% "full/vectors/1100110111-E-0000.bin"
private noncomputable def ep1100110111_1 : Blocks := edgeBlocks% "full/vectors/1100110111-E-0001.bin"
noncomputable def ep1100110111 : Blocks := (Blocks.join ep1100110111_0 ep1100110111_1)
private theorem idp1100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110011011.list =
    C ((2:ℤ)^263) * horner X vp1100110111.list + horner X ep1100110111.list := by
  exact edge_identity (B := (2:ℤ)^423) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100110111 : Branch 1 (-6575761639/16000000 : ℚ) vp110011011 := by
  apply branch_checked idp1100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-6575761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6583761639/8000000 : ℚ) by norm_num]
  exact coverp1100110111
theorem coverp110011011 : Covers (-6575761639/16000000 : ℚ) vp110011011 := join_branches bp1100110110 bp1100110111
private noncomputable def vp1100110101_0 : Blocks := edgeBlocks% "full/vectors/1100110101-V-0000.bin"
noncomputable def vp1100110101 : Blocks := vp1100110101_0
theorem coverp1100110101 : Covers (-6567761639/8000000 : ℚ) vp1100110101 := cover_leaf (by decide +kernel)
private noncomputable def vp1100110100_0 : Blocks := edgeBlocks% "full/vectors/1100110100-V-0000.bin"
noncomputable def vp1100110100 : Blocks := vp1100110100_0
theorem coverp1100110100 : Covers (-6559761639/8000000 : ℚ) vp1100110100 := cover_leaf (by decide +kernel)
private noncomputable def vp110011010_0 : Blocks := edgeBlocks% "full/vectors/110011010-V-0000.bin"
private noncomputable def vp110011010_1 : Blocks := edgeBlocks% "full/vectors/110011010-V-0001.bin"
noncomputable def vp110011010 : Blocks := (Blocks.join vp110011010_0 vp110011010_1)
private theorem bp1100110100 : Branch 0 (-6559761639/16000000 : ℚ) vp110011010 := by
  apply branch_left_normalized (c:=vp1100110100) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-6559761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6559761639/8000000 : ℚ) by norm_num]
  exact coverp1100110100
private noncomputable def ep1100110101_0 : Blocks := edgeBlocks% "full/vectors/1100110101-E-0000.bin"
private noncomputable def ep1100110101_1 : Blocks := edgeBlocks% "full/vectors/1100110101-E-0001.bin"
noncomputable def ep1100110101 : Blocks := (Blocks.join ep1100110101_0 ep1100110101_1)
private theorem idp1100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110011010.list =
    C ((2:ℤ)^263) * horner X vp1100110101.list + horner X ep1100110101.list := by
  exact edge_identity (B := (2:ℤ)^422) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100110101 : Branch 1 (-6559761639/16000000 : ℚ) vp110011010 := by
  apply branch_checked idp1100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-6559761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6567761639/8000000 : ℚ) by norm_num]
  exact coverp1100110101
theorem coverp110011010 : Covers (-6559761639/16000000 : ℚ) vp110011010 := join_branches bp1100110100 bp1100110101
private noncomputable def vp11001101_0 : Blocks := edgeBlocks% "full/vectors/11001101-V-0000.bin"
private noncomputable def vp11001101_1 : Blocks := edgeBlocks% "full/vectors/11001101-V-0001.bin"
private noncomputable def vp11001101_2 : Blocks := edgeBlocks% "full/vectors/11001101-V-0002.bin"
private noncomputable def vp11001101_3 : Blocks := edgeBlocks% "full/vectors/11001101-V-0003.bin"
noncomputable def vp11001101 : Blocks := (Blocks.join (Blocks.join vp11001101_0 vp11001101_1) (Blocks.join vp11001101_2 vp11001101_3))
private theorem bp110011010 : Branch 0 (-6559761639/32000000 : ℚ) vp11001101 := by
  apply branch_left_normalized (c:=vp110011010) (k:=0) (m:=216) (by decide +kernel)
  rw [show 2*(-6559761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6559761639/16000000 : ℚ) by norm_num]
  exact coverp110011010
private noncomputable def ep110011011_0 : Blocks := edgeBlocks% "full/vectors/110011011-E-0000.bin"
private noncomputable def ep110011011_1 : Blocks := edgeBlocks% "full/vectors/110011011-E-0001.bin"
private noncomputable def ep110011011_2 : Blocks := edgeBlocks% "full/vectors/110011011-E-0002.bin"
private noncomputable def ep110011011_3 : Blocks := edgeBlocks% "full/vectors/110011011-E-0003.bin"
noncomputable def ep110011011 : Blocks := (Blocks.join (Blocks.join ep110011011_0 ep110011011_1) (Blocks.join ep110011011_2 ep110011011_3))
private theorem idp110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11001101.list =
    C ((2:ℤ)^502) * horner X vp110011011.list + horner X ep110011011.list := by
  exact edge_identity (B := (2:ℤ)^718) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110011011 : Branch 1 (-6559761639/32000000 : ℚ) vp11001101 := by
  apply branch_checked idp110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-6559761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6575761639/16000000 : ℚ) by norm_num]
  exact coverp110011011
theorem coverp11001101 : Covers (-6559761639/32000000 : ℚ) vp11001101 := join_branches bp110011010 bp110011011
private noncomputable def vp1100110011_0 : Blocks := edgeBlocks% "full/vectors/1100110011-V-0000.bin"
noncomputable def vp1100110011 : Blocks := vp1100110011_0
theorem coverp1100110011 : Covers (-6551761639/8000000 : ℚ) vp1100110011 := cover_leaf (by decide +kernel)
private noncomputable def vp1100110010_0 : Blocks := edgeBlocks% "full/vectors/1100110010-V-0000.bin"
noncomputable def vp1100110010 : Blocks := vp1100110010_0
theorem coverp1100110010 : Covers (-6543761639/8000000 : ℚ) vp1100110010 := cover_leaf (by decide +kernel)
private noncomputable def vp110011001_0 : Blocks := edgeBlocks% "full/vectors/110011001-V-0000.bin"
private noncomputable def vp110011001_1 : Blocks := edgeBlocks% "full/vectors/110011001-V-0001.bin"
noncomputable def vp110011001 : Blocks := (Blocks.join vp110011001_0 vp110011001_1)
private theorem bp1100110010 : Branch 0 (-6543761639/16000000 : ℚ) vp110011001 := by
  apply branch_left_normalized (c:=vp1100110010) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-6543761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6543761639/8000000 : ℚ) by norm_num]
  exact coverp1100110010
private noncomputable def ep1100110011_0 : Blocks := edgeBlocks% "full/vectors/1100110011-E-0000.bin"
private noncomputable def ep1100110011_1 : Blocks := edgeBlocks% "full/vectors/1100110011-E-0001.bin"
noncomputable def ep1100110011 : Blocks := (Blocks.join ep1100110011_0 ep1100110011_1)
private theorem idp1100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110011001.list =
    C ((2:ℤ)^263) * horner X vp1100110011.list + horner X ep1100110011.list := by
  exact edge_identity (B := (2:ℤ)^422) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100110011 : Branch 1 (-6543761639/16000000 : ℚ) vp110011001 := by
  apply branch_checked idp1100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-6543761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6551761639/8000000 : ℚ) by norm_num]
  exact coverp1100110011
theorem coverp110011001 : Covers (-6543761639/16000000 : ℚ) vp110011001 := join_branches bp1100110010 bp1100110011
private noncomputable def vp1100110001_0 : Blocks := edgeBlocks% "full/vectors/1100110001-V-0000.bin"
noncomputable def vp1100110001 : Blocks := vp1100110001_0
theorem coverp1100110001 : Covers (-6535761639/8000000 : ℚ) vp1100110001 := cover_leaf (by decide +kernel)
private noncomputable def vp1100110000_0 : Blocks := edgeBlocks% "full/vectors/1100110000-V-0000.bin"
noncomputable def vp1100110000 : Blocks := vp1100110000_0
theorem coverp1100110000 : Covers (-6527761639/8000000 : ℚ) vp1100110000 := cover_leaf (by decide +kernel)
private noncomputable def vp110011000_0 : Blocks := edgeBlocks% "full/vectors/110011000-V-0000.bin"
private noncomputable def vp110011000_1 : Blocks := edgeBlocks% "full/vectors/110011000-V-0001.bin"
noncomputable def vp110011000 : Blocks := (Blocks.join vp110011000_0 vp110011000_1)
private theorem bp1100110000 : Branch 0 (-6527761639/16000000 : ℚ) vp110011000 := by
  apply branch_left_normalized (c:=vp1100110000) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-6527761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6527761639/8000000 : ℚ) by norm_num]
  exact coverp1100110000
private noncomputable def ep1100110001_0 : Blocks := edgeBlocks% "full/vectors/1100110001-E-0000.bin"
private noncomputable def ep1100110001_1 : Blocks := edgeBlocks% "full/vectors/1100110001-E-0001.bin"
noncomputable def ep1100110001 : Blocks := (Blocks.join ep1100110001_0 ep1100110001_1)
private theorem idp1100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110011000.list =
    C ((2:ℤ)^264) * horner X vp1100110001.list + horner X ep1100110001.list := by
  exact edge_identity (B := (2:ℤ)^424) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100110001 : Branch 1 (-6527761639/16000000 : ℚ) vp110011000 := by
  apply branch_checked idp1100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-6527761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6535761639/8000000 : ℚ) by norm_num]
  exact coverp1100110001
theorem coverp110011000 : Covers (-6527761639/16000000 : ℚ) vp110011000 := join_branches bp1100110000 bp1100110001
private noncomputable def vp11001100_0 : Blocks := edgeBlocks% "full/vectors/11001100-V-0000.bin"
private noncomputable def vp11001100_1 : Blocks := edgeBlocks% "full/vectors/11001100-V-0001.bin"
private noncomputable def vp11001100_2 : Blocks := edgeBlocks% "full/vectors/11001100-V-0002.bin"
private noncomputable def vp11001100_3 : Blocks := edgeBlocks% "full/vectors/11001100-V-0003.bin"
noncomputable def vp11001100 : Blocks := (Blocks.join (Blocks.join vp11001100_0 vp11001100_1) (Blocks.join vp11001100_2 vp11001100_3))
private theorem bp110011000 : Branch 0 (-6527761639/32000000 : ℚ) vp11001100 := by
  apply branch_left_normalized (c:=vp110011000) (k:=0) (m:=217) (by decide +kernel)
  rw [show 2*(-6527761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6527761639/16000000 : ℚ) by norm_num]
  exact coverp110011000
private noncomputable def ep110011001_0 : Blocks := edgeBlocks% "full/vectors/110011001-E-0000.bin"
private noncomputable def ep110011001_1 : Blocks := edgeBlocks% "full/vectors/110011001-E-0001.bin"
private noncomputable def ep110011001_2 : Blocks := edgeBlocks% "full/vectors/110011001-E-0002.bin"
private noncomputable def ep110011001_3 : Blocks := edgeBlocks% "full/vectors/110011001-E-0003.bin"
noncomputable def ep110011001 : Blocks := (Blocks.join (Blocks.join ep110011001_0 ep110011001_1) (Blocks.join ep110011001_2 ep110011001_3))
private theorem idp110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11001100.list =
    C ((2:ℤ)^504) * horner X vp110011001.list + horner X ep110011001.list := by
  exact edge_identity (B := (2:ℤ)^720) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110011001 : Branch 1 (-6527761639/32000000 : ℚ) vp11001100 := by
  apply branch_checked idp110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-6527761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6543761639/16000000 : ℚ) by norm_num]
  exact coverp110011001
theorem coverp11001100 : Covers (-6527761639/32000000 : ℚ) vp11001100 := join_branches bp110011000 bp110011001
private noncomputable def vp1100110_0 : Blocks := edgeBlocks% "full/vectors/1100110-V-0000.bin"
private noncomputable def vp1100110_1 : Blocks := edgeBlocks% "full/vectors/1100110-V-0001.bin"
private noncomputable def vp1100110_2 : Blocks := edgeBlocks% "full/vectors/1100110-V-0002.bin"
private noncomputable def vp1100110_3 : Blocks := edgeBlocks% "full/vectors/1100110-V-0003.bin"
private noncomputable def vp1100110_4 : Blocks := edgeBlocks% "full/vectors/1100110-V-0004.bin"
private noncomputable def vp1100110_5 : Blocks := edgeBlocks% "full/vectors/1100110-V-0005.bin"
private noncomputable def vp1100110_6 : Blocks := edgeBlocks% "full/vectors/1100110-V-0006.bin"
noncomputable def vp1100110 : Blocks := (Blocks.join (Blocks.join vp1100110_0 (Blocks.join vp1100110_1 vp1100110_2)) (Blocks.join (Blocks.join vp1100110_3 vp1100110_4) (Blocks.join vp1100110_5 vp1100110_6)))
private theorem bp11001100 : Branch 0 (-6527761639/64000000 : ℚ) vp1100110 := by
  apply branch_left_normalized (c:=vp11001100) (k:=0) (m:=410) (by decide +kernel)
  rw [show 2*(-6527761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6527761639/32000000 : ℚ) by norm_num]
  exact coverp11001100
private noncomputable def ep11001101_0 : Blocks := edgeBlocks% "full/vectors/11001101-E-0000.bin"
private noncomputable def ep11001101_1 : Blocks := edgeBlocks% "full/vectors/11001101-E-0001.bin"
private noncomputable def ep11001101_2 : Blocks := edgeBlocks% "full/vectors/11001101-E-0002.bin"
private noncomputable def ep11001101_3 : Blocks := edgeBlocks% "full/vectors/11001101-E-0003.bin"
private noncomputable def ep11001101_4 : Blocks := edgeBlocks% "full/vectors/11001101-E-0004.bin"
private noncomputable def ep11001101_5 : Blocks := edgeBlocks% "full/vectors/11001101-E-0005.bin"
private noncomputable def ep11001101_6 : Blocks := edgeBlocks% "full/vectors/11001101-E-0006.bin"
noncomputable def ep11001101 : Blocks := (Blocks.join (Blocks.join ep11001101_0 (Blocks.join ep11001101_1 ep11001101_2)) (Blocks.join (Blocks.join ep11001101_3 ep11001101_4) (Blocks.join ep11001101_5 ep11001101_6)))
private theorem idp11001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1100110.list =
    C ((2:ℤ)^980) * horner X vp11001101.list + horner X ep11001101.list := by
  exact edge_identity (B := (2:ℤ)^1309) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11001101 : Branch 1 (-6527761639/64000000 : ℚ) vp1100110 := by
  apply branch_checked idp11001101 (by positivity) (by decide +kernel)
  rw [show 2*(-6527761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6559761639/32000000 : ℚ) by norm_num]
  exact coverp11001101
theorem coverp1100110 : Covers (-6527761639/64000000 : ℚ) vp1100110 := join_branches bp11001100 bp11001101
private noncomputable def vp110011_0 : Blocks := edgeBlocks% "full/vectors/110011-V-0000.bin"
private noncomputable def vp110011_1 : Blocks := edgeBlocks% "full/vectors/110011-V-0001.bin"
private noncomputable def vp110011_2 : Blocks := edgeBlocks% "full/vectors/110011-V-0002.bin"
private noncomputable def vp110011_3 : Blocks := edgeBlocks% "full/vectors/110011-V-0003.bin"
private noncomputable def vp110011_4 : Blocks := edgeBlocks% "full/vectors/110011-V-0004.bin"
private noncomputable def vp110011_5 : Blocks := edgeBlocks% "full/vectors/110011-V-0005.bin"
private noncomputable def vp110011_6 : Blocks := edgeBlocks% "full/vectors/110011-V-0006.bin"
private noncomputable def vp110011_7 : Blocks := edgeBlocks% "full/vectors/110011-V-0007.bin"
private noncomputable def vp110011_8 : Blocks := edgeBlocks% "full/vectors/110011-V-0008.bin"
private noncomputable def vp110011_9 : Blocks := edgeBlocks% "full/vectors/110011-V-0009.bin"
private noncomputable def vp110011_10 : Blocks := edgeBlocks% "full/vectors/110011-V-0010.bin"
private noncomputable def vp110011_11 : Blocks := edgeBlocks% "full/vectors/110011-V-0011.bin"
private noncomputable def vp110011_12 : Blocks := edgeBlocks% "full/vectors/110011-V-0012.bin"
noncomputable def vp110011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp110011_0 (Blocks.join vp110011_1 vp110011_2)) (Blocks.join vp110011_3 (Blocks.join vp110011_4 vp110011_5))) (Blocks.join (Blocks.join vp110011_6 (Blocks.join vp110011_7 vp110011_8)) (Blocks.join (Blocks.join vp110011_9 vp110011_10) (Blocks.join vp110011_11 vp110011_12))))
private theorem bp1100110 : Branch 0 (-6527761639/128000000 : ℚ) vp110011 := by
  apply branch_left_normalized (c:=vp1100110) (k:=0) (m:=794) (by decide +kernel)
  rw [show 2*(-6527761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-6527761639/64000000 : ℚ) by norm_num]
  exact coverp1100110
private noncomputable def ep1100111_0 : Blocks := edgeBlocks% "full/vectors/1100111-E-0000.bin"
private noncomputable def ep1100111_1 : Blocks := edgeBlocks% "full/vectors/1100111-E-0001.bin"
private noncomputable def ep1100111_2 : Blocks := edgeBlocks% "full/vectors/1100111-E-0002.bin"
private noncomputable def ep1100111_3 : Blocks := edgeBlocks% "full/vectors/1100111-E-0003.bin"
private noncomputable def ep1100111_4 : Blocks := edgeBlocks% "full/vectors/1100111-E-0004.bin"
private noncomputable def ep1100111_5 : Blocks := edgeBlocks% "full/vectors/1100111-E-0005.bin"
private noncomputable def ep1100111_6 : Blocks := edgeBlocks% "full/vectors/1100111-E-0006.bin"
private noncomputable def ep1100111_7 : Blocks := edgeBlocks% "full/vectors/1100111-E-0007.bin"
private noncomputable def ep1100111_8 : Blocks := edgeBlocks% "full/vectors/1100111-E-0008.bin"
private noncomputable def ep1100111_9 : Blocks := edgeBlocks% "full/vectors/1100111-E-0009.bin"
private noncomputable def ep1100111_10 : Blocks := edgeBlocks% "full/vectors/1100111-E-0010.bin"
private noncomputable def ep1100111_11 : Blocks := edgeBlocks% "full/vectors/1100111-E-0011.bin"
private noncomputable def ep1100111_12 : Blocks := edgeBlocks% "full/vectors/1100111-E-0012.bin"
noncomputable def ep1100111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1100111_0 (Blocks.join ep1100111_1 ep1100111_2)) (Blocks.join ep1100111_3 (Blocks.join ep1100111_4 ep1100111_5))) (Blocks.join (Blocks.join ep1100111_6 (Blocks.join ep1100111_7 ep1100111_8)) (Blocks.join (Blocks.join ep1100111_9 ep1100111_10) (Blocks.join ep1100111_11 ep1100111_12))))
private theorem idp1100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110011.list =
    C ((2:ℤ)^1916) * horner X vp1100111.list + horner X ep1100111.list := by
  exact edge_identity (B := (2:ℤ)^2469) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100111 : Branch 1 (-6527761639/128000000 : ℚ) vp110011 := by
  apply branch_checked idp1100111 (by positivity) (by decide +kernel)
  rw [show 2*(-6527761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-6591761639/64000000 : ℚ) by norm_num]
  exact coverp1100111
theorem coverp110011 : Covers (-6527761639/128000000 : ℚ) vp110011 := join_branches bp1100110 bp1100111
private noncomputable def vp1100101111_0 : Blocks := edgeBlocks% "full/vectors/1100101111-V-0000.bin"
noncomputable def vp1100101111 : Blocks := vp1100101111_0
theorem coverp1100101111 : Covers (-6519761639/8000000 : ℚ) vp1100101111 := cover_leaf (by decide +kernel)
private noncomputable def vp1100101110_0 : Blocks := edgeBlocks% "full/vectors/1100101110-V-0000.bin"
noncomputable def vp1100101110 : Blocks := vp1100101110_0
theorem coverp1100101110 : Covers (-6511761639/8000000 : ℚ) vp1100101110 := cover_leaf (by decide +kernel)
private noncomputable def vp110010111_0 : Blocks := edgeBlocks% "full/vectors/110010111-V-0000.bin"
private noncomputable def vp110010111_1 : Blocks := edgeBlocks% "full/vectors/110010111-V-0001.bin"
noncomputable def vp110010111 : Blocks := (Blocks.join vp110010111_0 vp110010111_1)
private theorem bp1100101110 : Branch 0 (-6511761639/16000000 : ℚ) vp110010111 := by
  apply branch_left_normalized (c:=vp1100101110) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-6511761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6511761639/8000000 : ℚ) by norm_num]
  exact coverp1100101110
private noncomputable def ep1100101111_0 : Blocks := edgeBlocks% "full/vectors/1100101111-E-0000.bin"
private noncomputable def ep1100101111_1 : Blocks := edgeBlocks% "full/vectors/1100101111-E-0001.bin"
noncomputable def ep1100101111 : Blocks := (Blocks.join ep1100101111_0 ep1100101111_1)
private theorem idp1100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110010111.list =
    C ((2:ℤ)^264) * horner X vp1100101111.list + horner X ep1100101111.list := by
  exact edge_identity (B := (2:ℤ)^424) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100101111 : Branch 1 (-6511761639/16000000 : ℚ) vp110010111 := by
  apply branch_checked idp1100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-6511761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6519761639/8000000 : ℚ) by norm_num]
  exact coverp1100101111
theorem coverp110010111 : Covers (-6511761639/16000000 : ℚ) vp110010111 := join_branches bp1100101110 bp1100101111
private noncomputable def vp1100101101_0 : Blocks := edgeBlocks% "full/vectors/1100101101-V-0000.bin"
noncomputable def vp1100101101 : Blocks := vp1100101101_0
theorem coverp1100101101 : Covers (-6503761639/8000000 : ℚ) vp1100101101 := cover_leaf (by decide +kernel)
private noncomputable def vp1100101100_0 : Blocks := edgeBlocks% "full/vectors/1100101100-V-0000.bin"
noncomputable def vp1100101100 : Blocks := vp1100101100_0
theorem coverp1100101100 : Covers (-6495761639/8000000 : ℚ) vp1100101100 := cover_leaf (by decide +kernel)
private noncomputable def vp110010110_0 : Blocks := edgeBlocks% "full/vectors/110010110-V-0000.bin"
private noncomputable def vp110010110_1 : Blocks := edgeBlocks% "full/vectors/110010110-V-0001.bin"
noncomputable def vp110010110 : Blocks := (Blocks.join vp110010110_0 vp110010110_1)
private theorem bp1100101100 : Branch 0 (-6495761639/16000000 : ℚ) vp110010110 := by
  apply branch_left_normalized (c:=vp1100101100) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-6495761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6495761639/8000000 : ℚ) by norm_num]
  exact coverp1100101100
private noncomputable def ep1100101101_0 : Blocks := edgeBlocks% "full/vectors/1100101101-E-0000.bin"
private noncomputable def ep1100101101_1 : Blocks := edgeBlocks% "full/vectors/1100101101-E-0001.bin"
noncomputable def ep1100101101 : Blocks := (Blocks.join ep1100101101_0 ep1100101101_1)
private theorem idp1100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110010110.list =
    C ((2:ℤ)^265) * horner X vp1100101101.list + horner X ep1100101101.list := by
  exact edge_identity (B := (2:ℤ)^424) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100101101 : Branch 1 (-6495761639/16000000 : ℚ) vp110010110 := by
  apply branch_checked idp1100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-6495761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6503761639/8000000 : ℚ) by norm_num]
  exact coverp1100101101
theorem coverp110010110 : Covers (-6495761639/16000000 : ℚ) vp110010110 := join_branches bp1100101100 bp1100101101
private noncomputable def vp11001011_0 : Blocks := edgeBlocks% "full/vectors/11001011-V-0000.bin"
private noncomputable def vp11001011_1 : Blocks := edgeBlocks% "full/vectors/11001011-V-0001.bin"
private noncomputable def vp11001011_2 : Blocks := edgeBlocks% "full/vectors/11001011-V-0002.bin"
private noncomputable def vp11001011_3 : Blocks := edgeBlocks% "full/vectors/11001011-V-0003.bin"
noncomputable def vp11001011 : Blocks := (Blocks.join (Blocks.join vp11001011_0 vp11001011_1) (Blocks.join vp11001011_2 vp11001011_3))
private theorem bp110010110 : Branch 0 (-6495761639/32000000 : ℚ) vp11001011 := by
  apply branch_left_normalized (c:=vp110010110) (k:=0) (m:=218) (by decide +kernel)
  rw [show 2*(-6495761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6495761639/16000000 : ℚ) by norm_num]
  exact coverp110010110
private noncomputable def ep110010111_0 : Blocks := edgeBlocks% "full/vectors/110010111-E-0000.bin"
private noncomputable def ep110010111_1 : Blocks := edgeBlocks% "full/vectors/110010111-E-0001.bin"
private noncomputable def ep110010111_2 : Blocks := edgeBlocks% "full/vectors/110010111-E-0002.bin"
private noncomputable def ep110010111_3 : Blocks := edgeBlocks% "full/vectors/110010111-E-0003.bin"
noncomputable def ep110010111 : Blocks := (Blocks.join (Blocks.join ep110010111_0 ep110010111_1) (Blocks.join ep110010111_2 ep110010111_3))
private theorem idp110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11001011.list =
    C ((2:ℤ)^505) * horner X vp110010111.list + horner X ep110010111.list := by
  exact edge_identity (B := (2:ℤ)^722) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110010111 : Branch 1 (-6495761639/32000000 : ℚ) vp11001011 := by
  apply branch_checked idp110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-6495761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6511761639/16000000 : ℚ) by norm_num]
  exact coverp110010111
theorem coverp11001011 : Covers (-6495761639/32000000 : ℚ) vp11001011 := join_branches bp110010110 bp110010111
private noncomputable def vp1100101011_0 : Blocks := edgeBlocks% "full/vectors/1100101011-V-0000.bin"
noncomputable def vp1100101011 : Blocks := vp1100101011_0
theorem coverp1100101011 : Covers (-6487761639/8000000 : ℚ) vp1100101011 := cover_leaf (by decide +kernel)
private noncomputable def vp1100101010_0 : Blocks := edgeBlocks% "full/vectors/1100101010-V-0000.bin"
noncomputable def vp1100101010 : Blocks := vp1100101010_0
theorem coverp1100101010 : Covers (-6479761639/8000000 : ℚ) vp1100101010 := cover_leaf (by decide +kernel)
private noncomputable def vp110010101_0 : Blocks := edgeBlocks% "full/vectors/110010101-V-0000.bin"
private noncomputable def vp110010101_1 : Blocks := edgeBlocks% "full/vectors/110010101-V-0001.bin"
noncomputable def vp110010101 : Blocks := (Blocks.join vp110010101_0 vp110010101_1)
private theorem bp1100101010 : Branch 0 (-6479761639/16000000 : ℚ) vp110010101 := by
  apply branch_left_normalized (c:=vp1100101010) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-6479761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6479761639/8000000 : ℚ) by norm_num]
  exact coverp1100101010
private noncomputable def ep1100101011_0 : Blocks := edgeBlocks% "full/vectors/1100101011-E-0000.bin"
private noncomputable def ep1100101011_1 : Blocks := edgeBlocks% "full/vectors/1100101011-E-0001.bin"
noncomputable def ep1100101011 : Blocks := (Blocks.join ep1100101011_0 ep1100101011_1)
private theorem idp1100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110010101.list =
    C ((2:ℤ)^265) * horner X vp1100101011.list + horner X ep1100101011.list := by
  exact edge_identity (B := (2:ℤ)^425) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100101011 : Branch 1 (-6479761639/16000000 : ℚ) vp110010101 := by
  apply branch_checked idp1100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-6479761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6487761639/8000000 : ℚ) by norm_num]
  exact coverp1100101011
theorem coverp110010101 : Covers (-6479761639/16000000 : ℚ) vp110010101 := join_branches bp1100101010 bp1100101011
private noncomputable def vp1100101001_0 : Blocks := edgeBlocks% "full/vectors/1100101001-V-0000.bin"
noncomputable def vp1100101001 : Blocks := vp1100101001_0
theorem coverp1100101001 : Covers (-6471761639/8000000 : ℚ) vp1100101001 := cover_leaf (by decide +kernel)
private noncomputable def vp1100101000_0 : Blocks := edgeBlocks% "full/vectors/1100101000-V-0000.bin"
noncomputable def vp1100101000 : Blocks := vp1100101000_0
theorem coverp1100101000 : Covers (-6463761639/8000000 : ℚ) vp1100101000 := cover_leaf (by decide +kernel)
private noncomputable def vp110010100_0 : Blocks := edgeBlocks% "full/vectors/110010100-V-0000.bin"
private noncomputable def vp110010100_1 : Blocks := edgeBlocks% "full/vectors/110010100-V-0001.bin"
noncomputable def vp110010100 : Blocks := (Blocks.join vp110010100_0 vp110010100_1)
private theorem bp1100101000 : Branch 0 (-6463761639/16000000 : ℚ) vp110010100 := by
  apply branch_left_normalized (c:=vp1100101000) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-6463761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6463761639/8000000 : ℚ) by norm_num]
  exact coverp1100101000
private noncomputable def ep1100101001_0 : Blocks := edgeBlocks% "full/vectors/1100101001-E-0000.bin"
private noncomputable def ep1100101001_1 : Blocks := edgeBlocks% "full/vectors/1100101001-E-0001.bin"
noncomputable def ep1100101001 : Blocks := (Blocks.join ep1100101001_0 ep1100101001_1)
private theorem idp1100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110010100.list =
    C ((2:ℤ)^264) * horner X vp1100101001.list + horner X ep1100101001.list := by
  exact edge_identity (B := (2:ℤ)^424) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100101001 : Branch 1 (-6463761639/16000000 : ℚ) vp110010100 := by
  apply branch_checked idp1100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-6463761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6471761639/8000000 : ℚ) by norm_num]
  exact coverp1100101001
theorem coverp110010100 : Covers (-6463761639/16000000 : ℚ) vp110010100 := join_branches bp1100101000 bp1100101001
private noncomputable def vp11001010_0 : Blocks := edgeBlocks% "full/vectors/11001010-V-0000.bin"
private noncomputable def vp11001010_1 : Blocks := edgeBlocks% "full/vectors/11001010-V-0001.bin"
private noncomputable def vp11001010_2 : Blocks := edgeBlocks% "full/vectors/11001010-V-0002.bin"
private noncomputable def vp11001010_3 : Blocks := edgeBlocks% "full/vectors/11001010-V-0003.bin"
noncomputable def vp11001010 : Blocks := (Blocks.join (Blocks.join vp11001010_0 vp11001010_1) (Blocks.join vp11001010_2 vp11001010_3))
private theorem bp110010100 : Branch 0 (-6463761639/32000000 : ℚ) vp11001010 := by
  apply branch_left_normalized (c:=vp110010100) (k:=0) (m:=217) (by decide +kernel)
  rw [show 2*(-6463761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6463761639/16000000 : ℚ) by norm_num]
  exact coverp110010100
private noncomputable def ep110010101_0 : Blocks := edgeBlocks% "full/vectors/110010101-E-0000.bin"
private noncomputable def ep110010101_1 : Blocks := edgeBlocks% "full/vectors/110010101-E-0001.bin"
private noncomputable def ep110010101_2 : Blocks := edgeBlocks% "full/vectors/110010101-E-0002.bin"
private noncomputable def ep110010101_3 : Blocks := edgeBlocks% "full/vectors/110010101-E-0003.bin"
noncomputable def ep110010101 : Blocks := (Blocks.join (Blocks.join ep110010101_0 ep110010101_1) (Blocks.join ep110010101_2 ep110010101_3))
private theorem idp110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11001010.list =
    C ((2:ℤ)^504) * horner X vp110010101.list + horner X ep110010101.list := by
  exact edge_identity (B := (2:ℤ)^721) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110010101 : Branch 1 (-6463761639/32000000 : ℚ) vp11001010 := by
  apply branch_checked idp110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-6463761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6479761639/16000000 : ℚ) by norm_num]
  exact coverp110010101
theorem coverp11001010 : Covers (-6463761639/32000000 : ℚ) vp11001010 := join_branches bp110010100 bp110010101
private noncomputable def vp1100101_0 : Blocks := edgeBlocks% "full/vectors/1100101-V-0000.bin"
private noncomputable def vp1100101_1 : Blocks := edgeBlocks% "full/vectors/1100101-V-0001.bin"
private noncomputable def vp1100101_2 : Blocks := edgeBlocks% "full/vectors/1100101-V-0002.bin"
private noncomputable def vp1100101_3 : Blocks := edgeBlocks% "full/vectors/1100101-V-0003.bin"
private noncomputable def vp1100101_4 : Blocks := edgeBlocks% "full/vectors/1100101-V-0004.bin"
private noncomputable def vp1100101_5 : Blocks := edgeBlocks% "full/vectors/1100101-V-0005.bin"
private noncomputable def vp1100101_6 : Blocks := edgeBlocks% "full/vectors/1100101-V-0006.bin"
noncomputable def vp1100101 : Blocks := (Blocks.join (Blocks.join vp1100101_0 (Blocks.join vp1100101_1 vp1100101_2)) (Blocks.join (Blocks.join vp1100101_3 vp1100101_4) (Blocks.join vp1100101_5 vp1100101_6)))
private theorem bp11001010 : Branch 0 (-6463761639/64000000 : ℚ) vp1100101 := by
  apply branch_left_normalized (c:=vp11001010) (k:=0) (m:=411) (by decide +kernel)
  rw [show 2*(-6463761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6463761639/32000000 : ℚ) by norm_num]
  exact coverp11001010
private noncomputable def ep11001011_0 : Blocks := edgeBlocks% "full/vectors/11001011-E-0000.bin"
private noncomputable def ep11001011_1 : Blocks := edgeBlocks% "full/vectors/11001011-E-0001.bin"
private noncomputable def ep11001011_2 : Blocks := edgeBlocks% "full/vectors/11001011-E-0002.bin"
private noncomputable def ep11001011_3 : Blocks := edgeBlocks% "full/vectors/11001011-E-0003.bin"
private noncomputable def ep11001011_4 : Blocks := edgeBlocks% "full/vectors/11001011-E-0004.bin"
private noncomputable def ep11001011_5 : Blocks := edgeBlocks% "full/vectors/11001011-E-0005.bin"
private noncomputable def ep11001011_6 : Blocks := edgeBlocks% "full/vectors/11001011-E-0006.bin"
noncomputable def ep11001011 : Blocks := (Blocks.join (Blocks.join ep11001011_0 (Blocks.join ep11001011_1 ep11001011_2)) (Blocks.join (Blocks.join ep11001011_3 ep11001011_4) (Blocks.join ep11001011_5 ep11001011_6)))
private theorem idp11001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1100101.list =
    C ((2:ℤ)^983) * horner X vp11001011.list + horner X ep11001011.list := by
  exact edge_identity (B := (2:ℤ)^1314) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11001011 : Branch 1 (-6463761639/64000000 : ℚ) vp1100101 := by
  apply branch_checked idp11001011 (by positivity) (by decide +kernel)
  rw [show 2*(-6463761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6495761639/32000000 : ℚ) by norm_num]
  exact coverp11001011
theorem coverp1100101 : Covers (-6463761639/64000000 : ℚ) vp1100101 := join_branches bp11001010 bp11001011
private noncomputable def vp1100100111_0 : Blocks := edgeBlocks% "full/vectors/1100100111-V-0000.bin"
noncomputable def vp1100100111 : Blocks := vp1100100111_0
theorem coverp1100100111 : Covers (-6455761639/8000000 : ℚ) vp1100100111 := cover_leaf (by decide +kernel)
private noncomputable def vp1100100110_0 : Blocks := edgeBlocks% "full/vectors/1100100110-V-0000.bin"
noncomputable def vp1100100110 : Blocks := vp1100100110_0
theorem coverp1100100110 : Covers (-6447761639/8000000 : ℚ) vp1100100110 := cover_leaf (by decide +kernel)
private noncomputable def vp110010011_0 : Blocks := edgeBlocks% "full/vectors/110010011-V-0000.bin"
private noncomputable def vp110010011_1 : Blocks := edgeBlocks% "full/vectors/110010011-V-0001.bin"
noncomputable def vp110010011 : Blocks := (Blocks.join vp110010011_0 vp110010011_1)
private theorem bp1100100110 : Branch 0 (-6447761639/16000000 : ℚ) vp110010011 := by
  apply branch_left_normalized (c:=vp1100100110) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-6447761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6447761639/8000000 : ℚ) by norm_num]
  exact coverp1100100110
private noncomputable def ep1100100111_0 : Blocks := edgeBlocks% "full/vectors/1100100111-E-0000.bin"
private noncomputable def ep1100100111_1 : Blocks := edgeBlocks% "full/vectors/1100100111-E-0001.bin"
noncomputable def ep1100100111 : Blocks := (Blocks.join ep1100100111_0 ep1100100111_1)
private theorem idp1100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110010011.list =
    C ((2:ℤ)^265) * horner X vp1100100111.list + horner X ep1100100111.list := by
  exact edge_identity (B := (2:ℤ)^425) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100100111 : Branch 1 (-6447761639/16000000 : ℚ) vp110010011 := by
  apply branch_checked idp1100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-6447761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6455761639/8000000 : ℚ) by norm_num]
  exact coverp1100100111
theorem coverp110010011 : Covers (-6447761639/16000000 : ℚ) vp110010011 := join_branches bp1100100110 bp1100100111
private noncomputable def vp1100100101_0 : Blocks := edgeBlocks% "full/vectors/1100100101-V-0000.bin"
noncomputable def vp1100100101 : Blocks := vp1100100101_0
theorem coverp1100100101 : Covers (-6439761639/8000000 : ℚ) vp1100100101 := cover_leaf (by decide +kernel)
private noncomputable def vp1100100100_0 : Blocks := edgeBlocks% "full/vectors/1100100100-V-0000.bin"
noncomputable def vp1100100100 : Blocks := vp1100100100_0
theorem coverp1100100100 : Covers (-6431761639/8000000 : ℚ) vp1100100100 := cover_leaf (by decide +kernel)
private noncomputable def vp110010010_0 : Blocks := edgeBlocks% "full/vectors/110010010-V-0000.bin"
private noncomputable def vp110010010_1 : Blocks := edgeBlocks% "full/vectors/110010010-V-0001.bin"
noncomputable def vp110010010 : Blocks := (Blocks.join vp110010010_0 vp110010010_1)
private theorem bp1100100100 : Branch 0 (-6431761639/16000000 : ℚ) vp110010010 := by
  apply branch_left_normalized (c:=vp1100100100) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-6431761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6431761639/8000000 : ℚ) by norm_num]
  exact coverp1100100100
private noncomputable def ep1100100101_0 : Blocks := edgeBlocks% "full/vectors/1100100101-E-0000.bin"
private noncomputable def ep1100100101_1 : Blocks := edgeBlocks% "full/vectors/1100100101-E-0001.bin"
noncomputable def ep1100100101 : Blocks := (Blocks.join ep1100100101_0 ep1100100101_1)
private theorem idp1100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110010010.list =
    C ((2:ℤ)^266) * horner X vp1100100101.list + horner X ep1100100101.list := by
  exact edge_identity (B := (2:ℤ)^426) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100100101 : Branch 1 (-6431761639/16000000 : ℚ) vp110010010 := by
  apply branch_checked idp1100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-6431761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6439761639/8000000 : ℚ) by norm_num]
  exact coverp1100100101
theorem coverp110010010 : Covers (-6431761639/16000000 : ℚ) vp110010010 := join_branches bp1100100100 bp1100100101
private noncomputable def vp11001001_0 : Blocks := edgeBlocks% "full/vectors/11001001-V-0000.bin"
private noncomputable def vp11001001_1 : Blocks := edgeBlocks% "full/vectors/11001001-V-0001.bin"
private noncomputable def vp11001001_2 : Blocks := edgeBlocks% "full/vectors/11001001-V-0002.bin"
private noncomputable def vp11001001_3 : Blocks := edgeBlocks% "full/vectors/11001001-V-0003.bin"
noncomputable def vp11001001 : Blocks := (Blocks.join (Blocks.join vp11001001_0 vp11001001_1) (Blocks.join vp11001001_2 vp11001001_3))
private theorem bp110010010 : Branch 0 (-6431761639/32000000 : ℚ) vp11001001 := by
  apply branch_left_normalized (c:=vp110010010) (k:=0) (m:=219) (by decide +kernel)
  rw [show 2*(-6431761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6431761639/16000000 : ℚ) by norm_num]
  exact coverp110010010
private noncomputable def ep110010011_0 : Blocks := edgeBlocks% "full/vectors/110010011-E-0000.bin"
private noncomputable def ep110010011_1 : Blocks := edgeBlocks% "full/vectors/110010011-E-0001.bin"
private noncomputable def ep110010011_2 : Blocks := edgeBlocks% "full/vectors/110010011-E-0002.bin"
private noncomputable def ep110010011_3 : Blocks := edgeBlocks% "full/vectors/110010011-E-0003.bin"
noncomputable def ep110010011 : Blocks := (Blocks.join (Blocks.join ep110010011_0 ep110010011_1) (Blocks.join ep110010011_2 ep110010011_3))
private theorem idp110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11001001.list =
    C ((2:ℤ)^507) * horner X vp110010011.list + horner X ep110010011.list := by
  exact edge_identity (B := (2:ℤ)^724) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110010011 : Branch 1 (-6431761639/32000000 : ℚ) vp11001001 := by
  apply branch_checked idp110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-6431761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6447761639/16000000 : ℚ) by norm_num]
  exact coverp110010011
theorem coverp11001001 : Covers (-6431761639/32000000 : ℚ) vp11001001 := join_branches bp110010010 bp110010011
private noncomputable def vp1100100011_0 : Blocks := edgeBlocks% "full/vectors/1100100011-V-0000.bin"
noncomputable def vp1100100011 : Blocks := vp1100100011_0
theorem coverp1100100011 : Covers (-6423761639/8000000 : ℚ) vp1100100011 := cover_leaf (by decide +kernel)
private noncomputable def vp1100100010_0 : Blocks := edgeBlocks% "full/vectors/1100100010-V-0000.bin"
noncomputable def vp1100100010 : Blocks := vp1100100010_0
theorem coverp1100100010 : Covers (-6415761639/8000000 : ℚ) vp1100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp110010001_0 : Blocks := edgeBlocks% "full/vectors/110010001-V-0000.bin"
private noncomputable def vp110010001_1 : Blocks := edgeBlocks% "full/vectors/110010001-V-0001.bin"
noncomputable def vp110010001 : Blocks := (Blocks.join vp110010001_0 vp110010001_1)
private theorem bp1100100010 : Branch 0 (-6415761639/16000000 : ℚ) vp110010001 := by
  apply branch_left_normalized (c:=vp1100100010) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-6415761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6415761639/8000000 : ℚ) by norm_num]
  exact coverp1100100010
private noncomputable def ep1100100011_0 : Blocks := edgeBlocks% "full/vectors/1100100011-E-0000.bin"
private noncomputable def ep1100100011_1 : Blocks := edgeBlocks% "full/vectors/1100100011-E-0001.bin"
noncomputable def ep1100100011 : Blocks := (Blocks.join ep1100100011_0 ep1100100011_1)
private theorem idp1100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110010001.list =
    C ((2:ℤ)^266) * horner X vp1100100011.list + horner X ep1100100011.list := by
  exact edge_identity (B := (2:ℤ)^426) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100100011 : Branch 1 (-6415761639/16000000 : ℚ) vp110010001 := by
  apply branch_checked idp1100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-6415761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6423761639/8000000 : ℚ) by norm_num]
  exact coverp1100100011
theorem coverp110010001 : Covers (-6415761639/16000000 : ℚ) vp110010001 := join_branches bp1100100010 bp1100100011
private noncomputable def vp1100100001_0 : Blocks := edgeBlocks% "full/vectors/1100100001-V-0000.bin"
noncomputable def vp1100100001 : Blocks := vp1100100001_0
theorem coverp1100100001 : Covers (-6407761639/8000000 : ℚ) vp1100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp1100100000_0 : Blocks := edgeBlocks% "full/vectors/1100100000-V-0000.bin"
noncomputable def vp1100100000 : Blocks := vp1100100000_0
theorem coverp1100100000 : Covers (-6399761639/8000000 : ℚ) vp1100100000 := cover_leaf (by decide +kernel)
private noncomputable def vp110010000_0 : Blocks := edgeBlocks% "full/vectors/110010000-V-0000.bin"
private noncomputable def vp110010000_1 : Blocks := edgeBlocks% "full/vectors/110010000-V-0001.bin"
noncomputable def vp110010000 : Blocks := (Blocks.join vp110010000_0 vp110010000_1)
private theorem bp1100100000 : Branch 0 (-6399761639/16000000 : ℚ) vp110010000 := by
  apply branch_left_normalized (c:=vp1100100000) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-6399761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6399761639/8000000 : ℚ) by norm_num]
  exact coverp1100100000
private noncomputable def ep1100100001_0 : Blocks := edgeBlocks% "full/vectors/1100100001-E-0000.bin"
private noncomputable def ep1100100001_1 : Blocks := edgeBlocks% "full/vectors/1100100001-E-0001.bin"
noncomputable def ep1100100001 : Blocks := (Blocks.join ep1100100001_0 ep1100100001_1)
private theorem idp1100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110010000.list =
    C ((2:ℤ)^266) * horner X vp1100100001.list + horner X ep1100100001.list := by
  exact edge_identity (B := (2:ℤ)^426) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100100001 : Branch 1 (-6399761639/16000000 : ℚ) vp110010000 := by
  apply branch_checked idp1100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-6399761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6407761639/8000000 : ℚ) by norm_num]
  exact coverp1100100001
theorem coverp110010000 : Covers (-6399761639/16000000 : ℚ) vp110010000 := join_branches bp1100100000 bp1100100001
private noncomputable def vp11001000_0 : Blocks := edgeBlocks% "full/vectors/11001000-V-0000.bin"
private noncomputable def vp11001000_1 : Blocks := edgeBlocks% "full/vectors/11001000-V-0001.bin"
private noncomputable def vp11001000_2 : Blocks := edgeBlocks% "full/vectors/11001000-V-0002.bin"
private noncomputable def vp11001000_3 : Blocks := edgeBlocks% "full/vectors/11001000-V-0003.bin"
noncomputable def vp11001000 : Blocks := (Blocks.join (Blocks.join vp11001000_0 vp11001000_1) (Blocks.join vp11001000_2 vp11001000_3))
private theorem bp110010000 : Branch 0 (-6399761639/32000000 : ℚ) vp11001000 := by
  apply branch_left_normalized (c:=vp110010000) (k:=0) (m:=219) (by decide +kernel)
  rw [show 2*(-6399761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6399761639/16000000 : ℚ) by norm_num]
  exact coverp110010000
private noncomputable def ep110010001_0 : Blocks := edgeBlocks% "full/vectors/110010001-E-0000.bin"
private noncomputable def ep110010001_1 : Blocks := edgeBlocks% "full/vectors/110010001-E-0001.bin"
private noncomputable def ep110010001_2 : Blocks := edgeBlocks% "full/vectors/110010001-E-0002.bin"
private noncomputable def ep110010001_3 : Blocks := edgeBlocks% "full/vectors/110010001-E-0003.bin"
noncomputable def ep110010001 : Blocks := (Blocks.join (Blocks.join ep110010001_0 ep110010001_1) (Blocks.join ep110010001_2 ep110010001_3))
private theorem idp110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11001000.list =
    C ((2:ℤ)^507) * horner X vp110010001.list + horner X ep110010001.list := by
  exact edge_identity (B := (2:ℤ)^725) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110010001 : Branch 1 (-6399761639/32000000 : ℚ) vp11001000 := by
  apply branch_checked idp110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-6399761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6415761639/16000000 : ℚ) by norm_num]
  exact coverp110010001
theorem coverp11001000 : Covers (-6399761639/32000000 : ℚ) vp11001000 := join_branches bp110010000 bp110010001
private noncomputable def vp1100100_0 : Blocks := edgeBlocks% "full/vectors/1100100-V-0000.bin"
private noncomputable def vp1100100_1 : Blocks := edgeBlocks% "full/vectors/1100100-V-0001.bin"
private noncomputable def vp1100100_2 : Blocks := edgeBlocks% "full/vectors/1100100-V-0002.bin"
private noncomputable def vp1100100_3 : Blocks := edgeBlocks% "full/vectors/1100100-V-0003.bin"
private noncomputable def vp1100100_4 : Blocks := edgeBlocks% "full/vectors/1100100-V-0004.bin"
private noncomputable def vp1100100_5 : Blocks := edgeBlocks% "full/vectors/1100100-V-0005.bin"
private noncomputable def vp1100100_6 : Blocks := edgeBlocks% "full/vectors/1100100-V-0006.bin"
noncomputable def vp1100100 : Blocks := (Blocks.join (Blocks.join vp1100100_0 (Blocks.join vp1100100_1 vp1100100_2)) (Blocks.join (Blocks.join vp1100100_3 vp1100100_4) (Blocks.join vp1100100_5 vp1100100_6)))
private theorem bp11001000 : Branch 0 (-6399761639/64000000 : ℚ) vp1100100 := by
  apply branch_left_normalized (c:=vp11001000) (k:=0) (m:=414) (by decide +kernel)
  rw [show 2*(-6399761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6399761639/32000000 : ℚ) by norm_num]
  exact coverp11001000
private noncomputable def ep11001001_0 : Blocks := edgeBlocks% "full/vectors/11001001-E-0000.bin"
private noncomputable def ep11001001_1 : Blocks := edgeBlocks% "full/vectors/11001001-E-0001.bin"
private noncomputable def ep11001001_2 : Blocks := edgeBlocks% "full/vectors/11001001-E-0002.bin"
private noncomputable def ep11001001_3 : Blocks := edgeBlocks% "full/vectors/11001001-E-0003.bin"
private noncomputable def ep11001001_4 : Blocks := edgeBlocks% "full/vectors/11001001-E-0004.bin"
private noncomputable def ep11001001_5 : Blocks := edgeBlocks% "full/vectors/11001001-E-0005.bin"
private noncomputable def ep11001001_6 : Blocks := edgeBlocks% "full/vectors/11001001-E-0006.bin"
noncomputable def ep11001001 : Blocks := (Blocks.join (Blocks.join ep11001001_0 (Blocks.join ep11001001_1 ep11001001_2)) (Blocks.join (Blocks.join ep11001001_3 ep11001001_4) (Blocks.join ep11001001_5 ep11001001_6)))
private theorem idp11001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1100100.list =
    C ((2:ℤ)^986) * horner X vp11001001.list + horner X ep11001001.list := by
  exact edge_identity (B := (2:ℤ)^1320) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11001001 : Branch 1 (-6399761639/64000000 : ℚ) vp1100100 := by
  apply branch_checked idp11001001 (by positivity) (by decide +kernel)
  rw [show 2*(-6399761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6431761639/32000000 : ℚ) by norm_num]
  exact coverp11001001
theorem coverp1100100 : Covers (-6399761639/64000000 : ℚ) vp1100100 := join_branches bp11001000 bp11001001
private noncomputable def vp110010_0 : Blocks := edgeBlocks% "full/vectors/110010-V-0000.bin"
private noncomputable def vp110010_1 : Blocks := edgeBlocks% "full/vectors/110010-V-0001.bin"
private noncomputable def vp110010_2 : Blocks := edgeBlocks% "full/vectors/110010-V-0002.bin"
private noncomputable def vp110010_3 : Blocks := edgeBlocks% "full/vectors/110010-V-0003.bin"
private noncomputable def vp110010_4 : Blocks := edgeBlocks% "full/vectors/110010-V-0004.bin"
private noncomputable def vp110010_5 : Blocks := edgeBlocks% "full/vectors/110010-V-0005.bin"
private noncomputable def vp110010_6 : Blocks := edgeBlocks% "full/vectors/110010-V-0006.bin"
private noncomputable def vp110010_7 : Blocks := edgeBlocks% "full/vectors/110010-V-0007.bin"
private noncomputable def vp110010_8 : Blocks := edgeBlocks% "full/vectors/110010-V-0008.bin"
private noncomputable def vp110010_9 : Blocks := edgeBlocks% "full/vectors/110010-V-0009.bin"
private noncomputable def vp110010_10 : Blocks := edgeBlocks% "full/vectors/110010-V-0010.bin"
private noncomputable def vp110010_11 : Blocks := edgeBlocks% "full/vectors/110010-V-0011.bin"
private noncomputable def vp110010_12 : Blocks := edgeBlocks% "full/vectors/110010-V-0012.bin"
noncomputable def vp110010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp110010_0 (Blocks.join vp110010_1 vp110010_2)) (Blocks.join vp110010_3 (Blocks.join vp110010_4 vp110010_5))) (Blocks.join (Blocks.join vp110010_6 (Blocks.join vp110010_7 vp110010_8)) (Blocks.join (Blocks.join vp110010_9 vp110010_10) (Blocks.join vp110010_11 vp110010_12))))
private theorem bp1100100 : Branch 0 (-6399761639/128000000 : ℚ) vp110010 := by
  apply branch_left_normalized (c:=vp1100100) (k:=0) (m:=801) (by decide +kernel)
  rw [show 2*(-6399761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-6399761639/64000000 : ℚ) by norm_num]
  exact coverp1100100
private noncomputable def ep1100101_0 : Blocks := edgeBlocks% "full/vectors/1100101-E-0000.bin"
private noncomputable def ep1100101_1 : Blocks := edgeBlocks% "full/vectors/1100101-E-0001.bin"
private noncomputable def ep1100101_2 : Blocks := edgeBlocks% "full/vectors/1100101-E-0002.bin"
private noncomputable def ep1100101_3 : Blocks := edgeBlocks% "full/vectors/1100101-E-0003.bin"
private noncomputable def ep1100101_4 : Blocks := edgeBlocks% "full/vectors/1100101-E-0004.bin"
private noncomputable def ep1100101_5 : Blocks := edgeBlocks% "full/vectors/1100101-E-0005.bin"
private noncomputable def ep1100101_6 : Blocks := edgeBlocks% "full/vectors/1100101-E-0006.bin"
private noncomputable def ep1100101_7 : Blocks := edgeBlocks% "full/vectors/1100101-E-0007.bin"
private noncomputable def ep1100101_8 : Blocks := edgeBlocks% "full/vectors/1100101-E-0008.bin"
private noncomputable def ep1100101_9 : Blocks := edgeBlocks% "full/vectors/1100101-E-0009.bin"
private noncomputable def ep1100101_10 : Blocks := edgeBlocks% "full/vectors/1100101-E-0010.bin"
private noncomputable def ep1100101_11 : Blocks := edgeBlocks% "full/vectors/1100101-E-0011.bin"
private noncomputable def ep1100101_12 : Blocks := edgeBlocks% "full/vectors/1100101-E-0012.bin"
noncomputable def ep1100101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1100101_0 (Blocks.join ep1100101_1 ep1100101_2)) (Blocks.join ep1100101_3 (Blocks.join ep1100101_4 ep1100101_5))) (Blocks.join (Blocks.join ep1100101_6 (Blocks.join ep1100101_7 ep1100101_8)) (Blocks.join (Blocks.join ep1100101_9 ep1100101_10) (Blocks.join ep1100101_11 ep1100101_12))))
private theorem idp1100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110010.list =
    C ((2:ℤ)^1928) * horner X vp1100101.list + horner X ep1100101.list := by
  exact edge_identity (B := (2:ℤ)^2489) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100101 : Branch 1 (-6399761639/128000000 : ℚ) vp110010 := by
  apply branch_checked idp1100101 (by positivity) (by decide +kernel)
  rw [show 2*(-6399761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-6463761639/64000000 : ℚ) by norm_num]
  exact coverp1100101
theorem coverp110010 : Covers (-6399761639/128000000 : ℚ) vp110010 := join_branches bp1100100 bp1100101
private noncomputable def vp11001_0 : Blocks := edgeBlocks% "full/vectors/11001-V-0000.bin"
private noncomputable def vp11001_1 : Blocks := edgeBlocks% "full/vectors/11001-V-0001.bin"
private noncomputable def vp11001_2 : Blocks := edgeBlocks% "full/vectors/11001-V-0002.bin"
private noncomputable def vp11001_3 : Blocks := edgeBlocks% "full/vectors/11001-V-0003.bin"
private noncomputable def vp11001_4 : Blocks := edgeBlocks% "full/vectors/11001-V-0004.bin"
private noncomputable def vp11001_5 : Blocks := edgeBlocks% "full/vectors/11001-V-0005.bin"
private noncomputable def vp11001_6 : Blocks := edgeBlocks% "full/vectors/11001-V-0006.bin"
private noncomputable def vp11001_7 : Blocks := edgeBlocks% "full/vectors/11001-V-0007.bin"
private noncomputable def vp11001_8 : Blocks := edgeBlocks% "full/vectors/11001-V-0008.bin"
private noncomputable def vp11001_9 : Blocks := edgeBlocks% "full/vectors/11001-V-0009.bin"
private noncomputable def vp11001_10 : Blocks := edgeBlocks% "full/vectors/11001-V-0010.bin"
private noncomputable def vp11001_11 : Blocks := edgeBlocks% "full/vectors/11001-V-0011.bin"
private noncomputable def vp11001_12 : Blocks := edgeBlocks% "full/vectors/11001-V-0012.bin"
private noncomputable def vp11001_13 : Blocks := edgeBlocks% "full/vectors/11001-V-0013.bin"
private noncomputable def vp11001_14 : Blocks := edgeBlocks% "full/vectors/11001-V-0014.bin"
private noncomputable def vp11001_15 : Blocks := edgeBlocks% "full/vectors/11001-V-0015.bin"
private noncomputable def vp11001_16 : Blocks := edgeBlocks% "full/vectors/11001-V-0016.bin"
private noncomputable def vp11001_17 : Blocks := edgeBlocks% "full/vectors/11001-V-0017.bin"
private noncomputable def vp11001_18 : Blocks := edgeBlocks% "full/vectors/11001-V-0018.bin"
private noncomputable def vp11001_19 : Blocks := edgeBlocks% "full/vectors/11001-V-0019.bin"
private noncomputable def vp11001_20 : Blocks := edgeBlocks% "full/vectors/11001-V-0020.bin"
private noncomputable def vp11001_21 : Blocks := edgeBlocks% "full/vectors/11001-V-0021.bin"
private noncomputable def vp11001_22 : Blocks := edgeBlocks% "full/vectors/11001-V-0022.bin"
private noncomputable def vp11001_23 : Blocks := edgeBlocks% "full/vectors/11001-V-0023.bin"
noncomputable def vp11001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp11001_0 (Blocks.join vp11001_1 vp11001_2)) (Blocks.join vp11001_3 (Blocks.join vp11001_4 vp11001_5))) (Blocks.join (Blocks.join vp11001_6 (Blocks.join vp11001_7 vp11001_8)) (Blocks.join vp11001_9 (Blocks.join vp11001_10 vp11001_11)))) (Blocks.join (Blocks.join (Blocks.join vp11001_12 (Blocks.join vp11001_13 vp11001_14)) (Blocks.join vp11001_15 (Blocks.join vp11001_16 vp11001_17))) (Blocks.join (Blocks.join vp11001_18 (Blocks.join vp11001_19 vp11001_20)) (Blocks.join vp11001_21 (Blocks.join vp11001_22 vp11001_23)))))
private theorem bp110010 : Branch 0 (-6399761639/256000000 : ℚ) vp11001 := by
  apply branch_left_normalized (c:=vp110010) (k:=0) (m:=1558) (by decide +kernel)
  rw [show 2*(-6399761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-6399761639/128000000 : ℚ) by norm_num]
  exact coverp110010
private noncomputable def ep110011_0 : Blocks := edgeBlocks% "full/vectors/110011-E-0000.bin"
private noncomputable def ep110011_1 : Blocks := edgeBlocks% "full/vectors/110011-E-0001.bin"
private noncomputable def ep110011_2 : Blocks := edgeBlocks% "full/vectors/110011-E-0002.bin"
private noncomputable def ep110011_3 : Blocks := edgeBlocks% "full/vectors/110011-E-0003.bin"
private noncomputable def ep110011_4 : Blocks := edgeBlocks% "full/vectors/110011-E-0004.bin"
private noncomputable def ep110011_5 : Blocks := edgeBlocks% "full/vectors/110011-E-0005.bin"
private noncomputable def ep110011_6 : Blocks := edgeBlocks% "full/vectors/110011-E-0006.bin"
private noncomputable def ep110011_7 : Blocks := edgeBlocks% "full/vectors/110011-E-0007.bin"
private noncomputable def ep110011_8 : Blocks := edgeBlocks% "full/vectors/110011-E-0008.bin"
private noncomputable def ep110011_9 : Blocks := edgeBlocks% "full/vectors/110011-E-0009.bin"
private noncomputable def ep110011_10 : Blocks := edgeBlocks% "full/vectors/110011-E-0010.bin"
private noncomputable def ep110011_11 : Blocks := edgeBlocks% "full/vectors/110011-E-0011.bin"
private noncomputable def ep110011_12 : Blocks := edgeBlocks% "full/vectors/110011-E-0012.bin"
private noncomputable def ep110011_13 : Blocks := edgeBlocks% "full/vectors/110011-E-0013.bin"
private noncomputable def ep110011_14 : Blocks := edgeBlocks% "full/vectors/110011-E-0014.bin"
private noncomputable def ep110011_15 : Blocks := edgeBlocks% "full/vectors/110011-E-0015.bin"
private noncomputable def ep110011_16 : Blocks := edgeBlocks% "full/vectors/110011-E-0016.bin"
private noncomputable def ep110011_17 : Blocks := edgeBlocks% "full/vectors/110011-E-0017.bin"
private noncomputable def ep110011_18 : Blocks := edgeBlocks% "full/vectors/110011-E-0018.bin"
private noncomputable def ep110011_19 : Blocks := edgeBlocks% "full/vectors/110011-E-0019.bin"
private noncomputable def ep110011_20 : Blocks := edgeBlocks% "full/vectors/110011-E-0020.bin"
private noncomputable def ep110011_21 : Blocks := edgeBlocks% "full/vectors/110011-E-0021.bin"
private noncomputable def ep110011_22 : Blocks := edgeBlocks% "full/vectors/110011-E-0022.bin"
private noncomputable def ep110011_23 : Blocks := edgeBlocks% "full/vectors/110011-E-0023.bin"
noncomputable def ep110011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep110011_0 (Blocks.join ep110011_1 ep110011_2)) (Blocks.join ep110011_3 (Blocks.join ep110011_4 ep110011_5))) (Blocks.join (Blocks.join ep110011_6 (Blocks.join ep110011_7 ep110011_8)) (Blocks.join ep110011_9 (Blocks.join ep110011_10 ep110011_11)))) (Blocks.join (Blocks.join (Blocks.join ep110011_12 (Blocks.join ep110011_13 ep110011_14)) (Blocks.join ep110011_15 (Blocks.join ep110011_16 ep110011_17))) (Blocks.join (Blocks.join ep110011_18 (Blocks.join ep110011_19 ep110011_20)) (Blocks.join ep110011_21 (Blocks.join ep110011_22 ep110011_23)))))
private def ptsp110011 : List ℤ := [((2:ℤ)^3970+0),((2:ℤ)^3970+1)]
private theorem boundp110011 : 2^vp11001.size*absSum vp11001.list + ((2:ℤ)^3760*absSum vp110011.list+absSum ep110011.list) < (2:ℤ)^4766 := by decide +kernel
private theorem pointp110011_0 : fastHom 1 ((2:ℤ)^3970+0) vp11001 = ((2:ℤ)^3760)*vp110011.subst ((2:ℤ)^3970+0)+ep110011.subst ((2:ℤ)^3970+0) := by decide +kernel
private theorem pointp110011_1 : fastHom 1 ((2:ℤ)^3970+1) vp11001 = ((2:ℤ)^3760)*vp110011.subst ((2:ℤ)^3970+1)+ep110011.subst ((2:ℤ)^3970+1) := by decide +kernel
private theorem checkp110011 (x:ℤ) (hx:x ∈ ptsp110011) : fastHom 1 x vp11001 = ((2:ℤ)^3760)*vp110011.subst x+ep110011.subst x := by
  simp only [ptsp110011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp110011_0
  · exact pointp110011_1
private theorem idp110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11001.list =
    C ((2:ℤ)^3760) * horner X vp110011.list + horner X ep110011.list := by
  apply edge_identity (B := (2:ℤ)^4766) (by decide) (by positivity) (by positivity) boundp110011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp110011 (by decide +kernel)
  · have h : ptsp110011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp110011.trans_le (by decide +kernel)
  · exact checkp110011
private theorem bp110011 : Branch 1 (-6399761639/256000000 : ℚ) vp11001 := by
  apply branch_checked idp110011 (by positivity) (by decide +kernel)
  rw [show 2*(-6399761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-6527761639/128000000 : ℚ) by norm_num]
  exact coverp110011
theorem coverp11001 : Covers (-6399761639/256000000 : ℚ) vp11001 := join_branches bp110010 bp110011
private noncomputable def vp1100011111_0 : Blocks := edgeBlocks% "full/vectors/1100011111-V-0000.bin"
noncomputable def vp1100011111 : Blocks := vp1100011111_0
theorem coverp1100011111 : Covers (-6391761639/8000000 : ℚ) vp1100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp1100011110_0 : Blocks := edgeBlocks% "full/vectors/1100011110-V-0000.bin"
noncomputable def vp1100011110 : Blocks := vp1100011110_0
theorem coverp1100011110 : Covers (-6383761639/8000000 : ℚ) vp1100011110 := cover_leaf (by decide +kernel)
private noncomputable def vp110001111_0 : Blocks := edgeBlocks% "full/vectors/110001111-V-0000.bin"
private noncomputable def vp110001111_1 : Blocks := edgeBlocks% "full/vectors/110001111-V-0001.bin"
noncomputable def vp110001111 : Blocks := (Blocks.join vp110001111_0 vp110001111_1)
private theorem bp1100011110 : Branch 0 (-6383761639/16000000 : ℚ) vp110001111 := by
  apply branch_left_normalized (c:=vp1100011110) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-6383761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6383761639/8000000 : ℚ) by norm_num]
  exact coverp1100011110
private noncomputable def ep1100011111_0 : Blocks := edgeBlocks% "full/vectors/1100011111-E-0000.bin"
private noncomputable def ep1100011111_1 : Blocks := edgeBlocks% "full/vectors/1100011111-E-0001.bin"
noncomputable def ep1100011111 : Blocks := (Blocks.join ep1100011111_0 ep1100011111_1)
private theorem idp1100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110001111.list =
    C ((2:ℤ)^266) * horner X vp1100011111.list + horner X ep1100011111.list := by
  exact edge_identity (B := (2:ℤ)^427) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100011111 : Branch 1 (-6383761639/16000000 : ℚ) vp110001111 := by
  apply branch_checked idp1100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-6383761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6391761639/8000000 : ℚ) by norm_num]
  exact coverp1100011111
theorem coverp110001111 : Covers (-6383761639/16000000 : ℚ) vp110001111 := join_branches bp1100011110 bp1100011111
private noncomputable def vp1100011101_0 : Blocks := edgeBlocks% "full/vectors/1100011101-V-0000.bin"
noncomputable def vp1100011101 : Blocks := vp1100011101_0
theorem coverp1100011101 : Covers (-6375761639/8000000 : ℚ) vp1100011101 := cover_leaf (by decide +kernel)
private noncomputable def vp1100011100_0 : Blocks := edgeBlocks% "full/vectors/1100011100-V-0000.bin"
noncomputable def vp1100011100 : Blocks := vp1100011100_0
theorem coverp1100011100 : Covers (-6367761639/8000000 : ℚ) vp1100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp110001110_0 : Blocks := edgeBlocks% "full/vectors/110001110-V-0000.bin"
private noncomputable def vp110001110_1 : Blocks := edgeBlocks% "full/vectors/110001110-V-0001.bin"
noncomputable def vp110001110 : Blocks := (Blocks.join vp110001110_0 vp110001110_1)
private theorem bp1100011100 : Branch 0 (-6367761639/16000000 : ℚ) vp110001110 := by
  apply branch_left_normalized (c:=vp1100011100) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-6367761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6367761639/8000000 : ℚ) by norm_num]
  exact coverp1100011100
private noncomputable def ep1100011101_0 : Blocks := edgeBlocks% "full/vectors/1100011101-E-0000.bin"
private noncomputable def ep1100011101_1 : Blocks := edgeBlocks% "full/vectors/1100011101-E-0001.bin"
noncomputable def ep1100011101 : Blocks := (Blocks.join ep1100011101_0 ep1100011101_1)
private theorem idp1100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110001110.list =
    C ((2:ℤ)^266) * horner X vp1100011101.list + horner X ep1100011101.list := by
  exact edge_identity (B := (2:ℤ)^427) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100011101 : Branch 1 (-6367761639/16000000 : ℚ) vp110001110 := by
  apply branch_checked idp1100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-6367761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6375761639/8000000 : ℚ) by norm_num]
  exact coverp1100011101
theorem coverp110001110 : Covers (-6367761639/16000000 : ℚ) vp110001110 := join_branches bp1100011100 bp1100011101
private noncomputable def vp11000111_0 : Blocks := edgeBlocks% "full/vectors/11000111-V-0000.bin"
private noncomputable def vp11000111_1 : Blocks := edgeBlocks% "full/vectors/11000111-V-0001.bin"
private noncomputable def vp11000111_2 : Blocks := edgeBlocks% "full/vectors/11000111-V-0002.bin"
private noncomputable def vp11000111_3 : Blocks := edgeBlocks% "full/vectors/11000111-V-0003.bin"
noncomputable def vp11000111 : Blocks := (Blocks.join (Blocks.join vp11000111_0 vp11000111_1) (Blocks.join vp11000111_2 vp11000111_3))
private theorem bp110001110 : Branch 0 (-6367761639/32000000 : ℚ) vp11000111 := by
  apply branch_left_normalized (c:=vp110001110) (k:=0) (m:=219) (by decide +kernel)
  rw [show 2*(-6367761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6367761639/16000000 : ℚ) by norm_num]
  exact coverp110001110
private noncomputable def ep110001111_0 : Blocks := edgeBlocks% "full/vectors/110001111-E-0000.bin"
private noncomputable def ep110001111_1 : Blocks := edgeBlocks% "full/vectors/110001111-E-0001.bin"
private noncomputable def ep110001111_2 : Blocks := edgeBlocks% "full/vectors/110001111-E-0002.bin"
private noncomputable def ep110001111_3 : Blocks := edgeBlocks% "full/vectors/110001111-E-0003.bin"
noncomputable def ep110001111 : Blocks := (Blocks.join (Blocks.join ep110001111_0 ep110001111_1) (Blocks.join ep110001111_2 ep110001111_3))
private theorem idp110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11000111.list =
    C ((2:ℤ)^507) * horner X vp110001111.list + horner X ep110001111.list := by
  exact edge_identity (B := (2:ℤ)^726) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110001111 : Branch 1 (-6367761639/32000000 : ℚ) vp11000111 := by
  apply branch_checked idp110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-6367761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6383761639/16000000 : ℚ) by norm_num]
  exact coverp110001111
theorem coverp11000111 : Covers (-6367761639/32000000 : ℚ) vp11000111 := join_branches bp110001110 bp110001111
private noncomputable def vp1100011011_0 : Blocks := edgeBlocks% "full/vectors/1100011011-V-0000.bin"
noncomputable def vp1100011011 : Blocks := vp1100011011_0
theorem coverp1100011011 : Covers (-6359761639/8000000 : ℚ) vp1100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp1100011010_0 : Blocks := edgeBlocks% "full/vectors/1100011010-V-0000.bin"
noncomputable def vp1100011010 : Blocks := vp1100011010_0
theorem coverp1100011010 : Covers (-6351761639/8000000 : ℚ) vp1100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp110001101_0 : Blocks := edgeBlocks% "full/vectors/110001101-V-0000.bin"
private noncomputable def vp110001101_1 : Blocks := edgeBlocks% "full/vectors/110001101-V-0001.bin"
noncomputable def vp110001101 : Blocks := (Blocks.join vp110001101_0 vp110001101_1)
private theorem bp1100011010 : Branch 0 (-6351761639/16000000 : ℚ) vp110001101 := by
  apply branch_left_normalized (c:=vp1100011010) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-6351761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6351761639/8000000 : ℚ) by norm_num]
  exact coverp1100011010
private noncomputable def ep1100011011_0 : Blocks := edgeBlocks% "full/vectors/1100011011-E-0000.bin"
private noncomputable def ep1100011011_1 : Blocks := edgeBlocks% "full/vectors/1100011011-E-0001.bin"
noncomputable def ep1100011011 : Blocks := (Blocks.join ep1100011011_0 ep1100011011_1)
private theorem idp1100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110001101.list =
    C ((2:ℤ)^267) * horner X vp1100011011.list + horner X ep1100011011.list := by
  exact edge_identity (B := (2:ℤ)^427) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100011011 : Branch 1 (-6351761639/16000000 : ℚ) vp110001101 := by
  apply branch_checked idp1100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-6351761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6359761639/8000000 : ℚ) by norm_num]
  exact coverp1100011011
theorem coverp110001101 : Covers (-6351761639/16000000 : ℚ) vp110001101 := join_branches bp1100011010 bp1100011011
private noncomputable def vp1100011001_0 : Blocks := edgeBlocks% "full/vectors/1100011001-V-0000.bin"
noncomputable def vp1100011001 : Blocks := vp1100011001_0
theorem coverp1100011001 : Covers (-6343761639/8000000 : ℚ) vp1100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp1100011000_0 : Blocks := edgeBlocks% "full/vectors/1100011000-V-0000.bin"
noncomputable def vp1100011000 : Blocks := vp1100011000_0
theorem coverp1100011000 : Covers (-6335761639/8000000 : ℚ) vp1100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp110001100_0 : Blocks := edgeBlocks% "full/vectors/110001100-V-0000.bin"
private noncomputable def vp110001100_1 : Blocks := edgeBlocks% "full/vectors/110001100-V-0001.bin"
noncomputable def vp110001100 : Blocks := (Blocks.join vp110001100_0 vp110001100_1)
private theorem bp1100011000 : Branch 0 (-6335761639/16000000 : ℚ) vp110001100 := by
  apply branch_left_normalized (c:=vp1100011000) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-6335761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6335761639/8000000 : ℚ) by norm_num]
  exact coverp1100011000
private noncomputable def ep1100011001_0 : Blocks := edgeBlocks% "full/vectors/1100011001-E-0000.bin"
private noncomputable def ep1100011001_1 : Blocks := edgeBlocks% "full/vectors/1100011001-E-0001.bin"
noncomputable def ep1100011001 : Blocks := (Blocks.join ep1100011001_0 ep1100011001_1)
private theorem idp1100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110001100.list =
    C ((2:ℤ)^267) * horner X vp1100011001.list + horner X ep1100011001.list := by
  exact edge_identity (B := (2:ℤ)^428) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100011001 : Branch 1 (-6335761639/16000000 : ℚ) vp110001100 := by
  apply branch_checked idp1100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-6335761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6343761639/8000000 : ℚ) by norm_num]
  exact coverp1100011001
theorem coverp110001100 : Covers (-6335761639/16000000 : ℚ) vp110001100 := join_branches bp1100011000 bp1100011001
private noncomputable def vp11000110_0 : Blocks := edgeBlocks% "full/vectors/11000110-V-0000.bin"
private noncomputable def vp11000110_1 : Blocks := edgeBlocks% "full/vectors/11000110-V-0001.bin"
private noncomputable def vp11000110_2 : Blocks := edgeBlocks% "full/vectors/11000110-V-0002.bin"
private noncomputable def vp11000110_3 : Blocks := edgeBlocks% "full/vectors/11000110-V-0003.bin"
noncomputable def vp11000110 : Blocks := (Blocks.join (Blocks.join vp11000110_0 vp11000110_1) (Blocks.join vp11000110_2 vp11000110_3))
private theorem bp110001100 : Branch 0 (-6335761639/32000000 : ℚ) vp11000110 := by
  apply branch_left_normalized (c:=vp110001100) (k:=0) (m:=220) (by decide +kernel)
  rw [show 2*(-6335761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6335761639/16000000 : ℚ) by norm_num]
  exact coverp110001100
private noncomputable def ep110001101_0 : Blocks := edgeBlocks% "full/vectors/110001101-E-0000.bin"
private noncomputable def ep110001101_1 : Blocks := edgeBlocks% "full/vectors/110001101-E-0001.bin"
private noncomputable def ep110001101_2 : Blocks := edgeBlocks% "full/vectors/110001101-E-0002.bin"
private noncomputable def ep110001101_3 : Blocks := edgeBlocks% "full/vectors/110001101-E-0003.bin"
noncomputable def ep110001101 : Blocks := (Blocks.join (Blocks.join ep110001101_0 ep110001101_1) (Blocks.join ep110001101_2 ep110001101_3))
private theorem idp110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11000110.list =
    C ((2:ℤ)^510) * horner X vp110001101.list + horner X ep110001101.list := by
  exact edge_identity (B := (2:ℤ)^729) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110001101 : Branch 1 (-6335761639/32000000 : ℚ) vp11000110 := by
  apply branch_checked idp110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-6335761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6351761639/16000000 : ℚ) by norm_num]
  exact coverp110001101
theorem coverp11000110 : Covers (-6335761639/32000000 : ℚ) vp11000110 := join_branches bp110001100 bp110001101
private noncomputable def vp1100011_0 : Blocks := edgeBlocks% "full/vectors/1100011-V-0000.bin"
private noncomputable def vp1100011_1 : Blocks := edgeBlocks% "full/vectors/1100011-V-0001.bin"
private noncomputable def vp1100011_2 : Blocks := edgeBlocks% "full/vectors/1100011-V-0002.bin"
private noncomputable def vp1100011_3 : Blocks := edgeBlocks% "full/vectors/1100011-V-0003.bin"
private noncomputable def vp1100011_4 : Blocks := edgeBlocks% "full/vectors/1100011-V-0004.bin"
private noncomputable def vp1100011_5 : Blocks := edgeBlocks% "full/vectors/1100011-V-0005.bin"
private noncomputable def vp1100011_6 : Blocks := edgeBlocks% "full/vectors/1100011-V-0006.bin"
noncomputable def vp1100011 : Blocks := (Blocks.join (Blocks.join vp1100011_0 (Blocks.join vp1100011_1 vp1100011_2)) (Blocks.join (Blocks.join vp1100011_3 vp1100011_4) (Blocks.join vp1100011_5 vp1100011_6)))
private theorem bp11000110 : Branch 0 (-6335761639/64000000 : ℚ) vp1100011 := by
  apply branch_left_normalized (c:=vp11000110) (k:=0) (m:=416) (by decide +kernel)
  rw [show 2*(-6335761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6335761639/32000000 : ℚ) by norm_num]
  exact coverp11000110
private noncomputable def ep11000111_0 : Blocks := edgeBlocks% "full/vectors/11000111-E-0000.bin"
private noncomputable def ep11000111_1 : Blocks := edgeBlocks% "full/vectors/11000111-E-0001.bin"
private noncomputable def ep11000111_2 : Blocks := edgeBlocks% "full/vectors/11000111-E-0002.bin"
private noncomputable def ep11000111_3 : Blocks := edgeBlocks% "full/vectors/11000111-E-0003.bin"
private noncomputable def ep11000111_4 : Blocks := edgeBlocks% "full/vectors/11000111-E-0004.bin"
private noncomputable def ep11000111_5 : Blocks := edgeBlocks% "full/vectors/11000111-E-0005.bin"
private noncomputable def ep11000111_6 : Blocks := edgeBlocks% "full/vectors/11000111-E-0006.bin"
noncomputable def ep11000111 : Blocks := (Blocks.join (Blocks.join ep11000111_0 (Blocks.join ep11000111_1 ep11000111_2)) (Blocks.join (Blocks.join ep11000111_3 ep11000111_4) (Blocks.join ep11000111_5 ep11000111_6)))
private theorem idp11000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1100011.list =
    C ((2:ℤ)^991) * horner X vp11000111.list + horner X ep11000111.list := by
  exact edge_identity (B := (2:ℤ)^1326) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11000111 : Branch 1 (-6335761639/64000000 : ℚ) vp1100011 := by
  apply branch_checked idp11000111 (by positivity) (by decide +kernel)
  rw [show 2*(-6335761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6367761639/32000000 : ℚ) by norm_num]
  exact coverp11000111
theorem coverp1100011 : Covers (-6335761639/64000000 : ℚ) vp1100011 := join_branches bp11000110 bp11000111
private noncomputable def vp1100010111_0 : Blocks := edgeBlocks% "full/vectors/1100010111-V-0000.bin"
noncomputable def vp1100010111 : Blocks := vp1100010111_0
theorem coverp1100010111 : Covers (-6327761639/8000000 : ℚ) vp1100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp1100010110_0 : Blocks := edgeBlocks% "full/vectors/1100010110-V-0000.bin"
noncomputable def vp1100010110 : Blocks := vp1100010110_0
theorem coverp1100010110 : Covers (-6319761639/8000000 : ℚ) vp1100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp110001011_0 : Blocks := edgeBlocks% "full/vectors/110001011-V-0000.bin"
private noncomputable def vp110001011_1 : Blocks := edgeBlocks% "full/vectors/110001011-V-0001.bin"
noncomputable def vp110001011 : Blocks := (Blocks.join vp110001011_0 vp110001011_1)
private theorem bp1100010110 : Branch 0 (-6319761639/16000000 : ℚ) vp110001011 := by
  apply branch_left_normalized (c:=vp1100010110) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-6319761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6319761639/8000000 : ℚ) by norm_num]
  exact coverp1100010110
private noncomputable def ep1100010111_0 : Blocks := edgeBlocks% "full/vectors/1100010111-E-0000.bin"
private noncomputable def ep1100010111_1 : Blocks := edgeBlocks% "full/vectors/1100010111-E-0001.bin"
noncomputable def ep1100010111 : Blocks := (Blocks.join ep1100010111_0 ep1100010111_1)
private theorem idp1100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110001011.list =
    C ((2:ℤ)^267) * horner X vp1100010111.list + horner X ep1100010111.list := by
  exact edge_identity (B := (2:ℤ)^428) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100010111 : Branch 1 (-6319761639/16000000 : ℚ) vp110001011 := by
  apply branch_checked idp1100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-6319761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6327761639/8000000 : ℚ) by norm_num]
  exact coverp1100010111
theorem coverp110001011 : Covers (-6319761639/16000000 : ℚ) vp110001011 := join_branches bp1100010110 bp1100010111
private noncomputable def vp1100010101_0 : Blocks := edgeBlocks% "full/vectors/1100010101-V-0000.bin"
noncomputable def vp1100010101 : Blocks := vp1100010101_0
theorem coverp1100010101 : Covers (-6311761639/8000000 : ℚ) vp1100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp1100010100_0 : Blocks := edgeBlocks% "full/vectors/1100010100-V-0000.bin"
noncomputable def vp1100010100 : Blocks := vp1100010100_0
theorem coverp1100010100 : Covers (-6303761639/8000000 : ℚ) vp1100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp110001010_0 : Blocks := edgeBlocks% "full/vectors/110001010-V-0000.bin"
private noncomputable def vp110001010_1 : Blocks := edgeBlocks% "full/vectors/110001010-V-0001.bin"
noncomputable def vp110001010 : Blocks := (Blocks.join vp110001010_0 vp110001010_1)
private theorem bp1100010100 : Branch 0 (-6303761639/16000000 : ℚ) vp110001010 := by
  apply branch_left_normalized (c:=vp1100010100) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-6303761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6303761639/8000000 : ℚ) by norm_num]
  exact coverp1100010100
private noncomputable def ep1100010101_0 : Blocks := edgeBlocks% "full/vectors/1100010101-E-0000.bin"
private noncomputable def ep1100010101_1 : Blocks := edgeBlocks% "full/vectors/1100010101-E-0001.bin"
noncomputable def ep1100010101 : Blocks := (Blocks.join ep1100010101_0 ep1100010101_1)
private theorem idp1100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110001010.list =
    C ((2:ℤ)^267) * horner X vp1100010101.list + horner X ep1100010101.list := by
  exact edge_identity (B := (2:ℤ)^428) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100010101 : Branch 1 (-6303761639/16000000 : ℚ) vp110001010 := by
  apply branch_checked idp1100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-6303761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6311761639/8000000 : ℚ) by norm_num]
  exact coverp1100010101
theorem coverp110001010 : Covers (-6303761639/16000000 : ℚ) vp110001010 := join_branches bp1100010100 bp1100010101
private noncomputable def vp11000101_0 : Blocks := edgeBlocks% "full/vectors/11000101-V-0000.bin"
private noncomputable def vp11000101_1 : Blocks := edgeBlocks% "full/vectors/11000101-V-0001.bin"
private noncomputable def vp11000101_2 : Blocks := edgeBlocks% "full/vectors/11000101-V-0002.bin"
private noncomputable def vp11000101_3 : Blocks := edgeBlocks% "full/vectors/11000101-V-0003.bin"
noncomputable def vp11000101 : Blocks := (Blocks.join (Blocks.join vp11000101_0 vp11000101_1) (Blocks.join vp11000101_2 vp11000101_3))
private theorem bp110001010 : Branch 0 (-6303761639/32000000 : ℚ) vp11000101 := by
  apply branch_left_normalized (c:=vp110001010) (k:=0) (m:=220) (by decide +kernel)
  rw [show 2*(-6303761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6303761639/16000000 : ℚ) by norm_num]
  exact coverp110001010
private noncomputable def ep110001011_0 : Blocks := edgeBlocks% "full/vectors/110001011-E-0000.bin"
private noncomputable def ep110001011_1 : Blocks := edgeBlocks% "full/vectors/110001011-E-0001.bin"
private noncomputable def ep110001011_2 : Blocks := edgeBlocks% "full/vectors/110001011-E-0002.bin"
private noncomputable def ep110001011_3 : Blocks := edgeBlocks% "full/vectors/110001011-E-0003.bin"
noncomputable def ep110001011 : Blocks := (Blocks.join (Blocks.join ep110001011_0 ep110001011_1) (Blocks.join ep110001011_2 ep110001011_3))
private theorem idp110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11000101.list =
    C ((2:ℤ)^510) * horner X vp110001011.list + horner X ep110001011.list := by
  exact edge_identity (B := (2:ℤ)^730) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110001011 : Branch 1 (-6303761639/32000000 : ℚ) vp11000101 := by
  apply branch_checked idp110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-6303761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6319761639/16000000 : ℚ) by norm_num]
  exact coverp110001011
theorem coverp11000101 : Covers (-6303761639/32000000 : ℚ) vp11000101 := join_branches bp110001010 bp110001011
private noncomputable def vp1100010011_0 : Blocks := edgeBlocks% "full/vectors/1100010011-V-0000.bin"
noncomputable def vp1100010011 : Blocks := vp1100010011_0
theorem coverp1100010011 : Covers (-6295761639/8000000 : ℚ) vp1100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp1100010010_0 : Blocks := edgeBlocks% "full/vectors/1100010010-V-0000.bin"
noncomputable def vp1100010010 : Blocks := vp1100010010_0
theorem coverp1100010010 : Covers (-6287761639/8000000 : ℚ) vp1100010010 := cover_leaf (by decide +kernel)
private noncomputable def vp110001001_0 : Blocks := edgeBlocks% "full/vectors/110001001-V-0000.bin"
private noncomputable def vp110001001_1 : Blocks := edgeBlocks% "full/vectors/110001001-V-0001.bin"
noncomputable def vp110001001 : Blocks := (Blocks.join vp110001001_0 vp110001001_1)
private theorem bp1100010010 : Branch 0 (-6287761639/16000000 : ℚ) vp110001001 := by
  apply branch_left_normalized (c:=vp1100010010) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-6287761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6287761639/8000000 : ℚ) by norm_num]
  exact coverp1100010010
private noncomputable def ep1100010011_0 : Blocks := edgeBlocks% "full/vectors/1100010011-E-0000.bin"
private noncomputable def ep1100010011_1 : Blocks := edgeBlocks% "full/vectors/1100010011-E-0001.bin"
noncomputable def ep1100010011 : Blocks := (Blocks.join ep1100010011_0 ep1100010011_1)
private theorem idp1100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110001001.list =
    C ((2:ℤ)^268) * horner X vp1100010011.list + horner X ep1100010011.list := by
  exact edge_identity (B := (2:ℤ)^430) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100010011 : Branch 1 (-6287761639/16000000 : ℚ) vp110001001 := by
  apply branch_checked idp1100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-6287761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6295761639/8000000 : ℚ) by norm_num]
  exact coverp1100010011
theorem coverp110001001 : Covers (-6287761639/16000000 : ℚ) vp110001001 := join_branches bp1100010010 bp1100010011
private noncomputable def vp1100010001_0 : Blocks := edgeBlocks% "full/vectors/1100010001-V-0000.bin"
noncomputable def vp1100010001 : Blocks := vp1100010001_0
theorem coverp1100010001 : Covers (-6279761639/8000000 : ℚ) vp1100010001 := cover_leaf (by decide +kernel)
private noncomputable def vp1100010000_0 : Blocks := edgeBlocks% "full/vectors/1100010000-V-0000.bin"
noncomputable def vp1100010000 : Blocks := vp1100010000_0
theorem coverp1100010000 : Covers (-6271761639/8000000 : ℚ) vp1100010000 := cover_leaf (by decide +kernel)
private noncomputable def vp110001000_0 : Blocks := edgeBlocks% "full/vectors/110001000-V-0000.bin"
private noncomputable def vp110001000_1 : Blocks := edgeBlocks% "full/vectors/110001000-V-0001.bin"
noncomputable def vp110001000 : Blocks := (Blocks.join vp110001000_0 vp110001000_1)
private theorem bp1100010000 : Branch 0 (-6271761639/16000000 : ℚ) vp110001000 := by
  apply branch_left_normalized (c:=vp1100010000) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-6271761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6271761639/8000000 : ℚ) by norm_num]
  exact coverp1100010000
private noncomputable def ep1100010001_0 : Blocks := edgeBlocks% "full/vectors/1100010001-E-0000.bin"
private noncomputable def ep1100010001_1 : Blocks := edgeBlocks% "full/vectors/1100010001-E-0001.bin"
noncomputable def ep1100010001 : Blocks := (Blocks.join ep1100010001_0 ep1100010001_1)
private theorem idp1100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110001000.list =
    C ((2:ℤ)^268) * horner X vp1100010001.list + horner X ep1100010001.list := by
  exact edge_identity (B := (2:ℤ)^429) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100010001 : Branch 1 (-6271761639/16000000 : ℚ) vp110001000 := by
  apply branch_checked idp1100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-6271761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6279761639/8000000 : ℚ) by norm_num]
  exact coverp1100010001
theorem coverp110001000 : Covers (-6271761639/16000000 : ℚ) vp110001000 := join_branches bp1100010000 bp1100010001
private noncomputable def vp11000100_0 : Blocks := edgeBlocks% "full/vectors/11000100-V-0000.bin"
private noncomputable def vp11000100_1 : Blocks := edgeBlocks% "full/vectors/11000100-V-0001.bin"
private noncomputable def vp11000100_2 : Blocks := edgeBlocks% "full/vectors/11000100-V-0002.bin"
private noncomputable def vp11000100_3 : Blocks := edgeBlocks% "full/vectors/11000100-V-0003.bin"
noncomputable def vp11000100 : Blocks := (Blocks.join (Blocks.join vp11000100_0 vp11000100_1) (Blocks.join vp11000100_2 vp11000100_3))
private theorem bp110001000 : Branch 0 (-6271761639/32000000 : ℚ) vp11000100 := by
  apply branch_left_normalized (c:=vp110001000) (k:=0) (m:=221) (by decide +kernel)
  rw [show 2*(-6271761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6271761639/16000000 : ℚ) by norm_num]
  exact coverp110001000
private noncomputable def ep110001001_0 : Blocks := edgeBlocks% "full/vectors/110001001-E-0000.bin"
private noncomputable def ep110001001_1 : Blocks := edgeBlocks% "full/vectors/110001001-E-0001.bin"
private noncomputable def ep110001001_2 : Blocks := edgeBlocks% "full/vectors/110001001-E-0002.bin"
private noncomputable def ep110001001_3 : Blocks := edgeBlocks% "full/vectors/110001001-E-0003.bin"
noncomputable def ep110001001 : Blocks := (Blocks.join (Blocks.join ep110001001_0 ep110001001_1) (Blocks.join ep110001001_2 ep110001001_3))
private theorem idp110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11000100.list =
    C ((2:ℤ)^511) * horner X vp110001001.list + horner X ep110001001.list := by
  exact edge_identity (B := (2:ℤ)^731) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110001001 : Branch 1 (-6271761639/32000000 : ℚ) vp11000100 := by
  apply branch_checked idp110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-6271761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6287761639/16000000 : ℚ) by norm_num]
  exact coverp110001001
theorem coverp11000100 : Covers (-6271761639/32000000 : ℚ) vp11000100 := join_branches bp110001000 bp110001001
private noncomputable def vp1100010_0 : Blocks := edgeBlocks% "full/vectors/1100010-V-0000.bin"
private noncomputable def vp1100010_1 : Blocks := edgeBlocks% "full/vectors/1100010-V-0001.bin"
private noncomputable def vp1100010_2 : Blocks := edgeBlocks% "full/vectors/1100010-V-0002.bin"
private noncomputable def vp1100010_3 : Blocks := edgeBlocks% "full/vectors/1100010-V-0003.bin"
private noncomputable def vp1100010_4 : Blocks := edgeBlocks% "full/vectors/1100010-V-0004.bin"
private noncomputable def vp1100010_5 : Blocks := edgeBlocks% "full/vectors/1100010-V-0005.bin"
private noncomputable def vp1100010_6 : Blocks := edgeBlocks% "full/vectors/1100010-V-0006.bin"
noncomputable def vp1100010 : Blocks := (Blocks.join (Blocks.join vp1100010_0 (Blocks.join vp1100010_1 vp1100010_2)) (Blocks.join (Blocks.join vp1100010_3 vp1100010_4) (Blocks.join vp1100010_5 vp1100010_6)))
private theorem bp11000100 : Branch 0 (-6271761639/64000000 : ℚ) vp1100010 := by
  apply branch_left_normalized (c:=vp11000100) (k:=0) (m:=418) (by decide +kernel)
  rw [show 2*(-6271761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6271761639/32000000 : ℚ) by norm_num]
  exact coverp11000100
private noncomputable def ep11000101_0 : Blocks := edgeBlocks% "full/vectors/11000101-E-0000.bin"
private noncomputable def ep11000101_1 : Blocks := edgeBlocks% "full/vectors/11000101-E-0001.bin"
private noncomputable def ep11000101_2 : Blocks := edgeBlocks% "full/vectors/11000101-E-0002.bin"
private noncomputable def ep11000101_3 : Blocks := edgeBlocks% "full/vectors/11000101-E-0003.bin"
private noncomputable def ep11000101_4 : Blocks := edgeBlocks% "full/vectors/11000101-E-0004.bin"
private noncomputable def ep11000101_5 : Blocks := edgeBlocks% "full/vectors/11000101-E-0005.bin"
private noncomputable def ep11000101_6 : Blocks := edgeBlocks% "full/vectors/11000101-E-0006.bin"
noncomputable def ep11000101 : Blocks := (Blocks.join (Blocks.join ep11000101_0 (Blocks.join ep11000101_1 ep11000101_2)) (Blocks.join (Blocks.join ep11000101_3 ep11000101_4) (Blocks.join ep11000101_5 ep11000101_6)))
private theorem idp11000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1100010.list =
    C ((2:ℤ)^994) * horner X vp11000101.list + horner X ep11000101.list := by
  exact edge_identity (B := (2:ℤ)^1331) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11000101 : Branch 1 (-6271761639/64000000 : ℚ) vp1100010 := by
  apply branch_checked idp11000101 (by positivity) (by decide +kernel)
  rw [show 2*(-6271761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6303761639/32000000 : ℚ) by norm_num]
  exact coverp11000101
theorem coverp1100010 : Covers (-6271761639/64000000 : ℚ) vp1100010 := join_branches bp11000100 bp11000101
private noncomputable def vp110001_0 : Blocks := edgeBlocks% "full/vectors/110001-V-0000.bin"
private noncomputable def vp110001_1 : Blocks := edgeBlocks% "full/vectors/110001-V-0001.bin"
private noncomputable def vp110001_2 : Blocks := edgeBlocks% "full/vectors/110001-V-0002.bin"
private noncomputable def vp110001_3 : Blocks := edgeBlocks% "full/vectors/110001-V-0003.bin"
private noncomputable def vp110001_4 : Blocks := edgeBlocks% "full/vectors/110001-V-0004.bin"
private noncomputable def vp110001_5 : Blocks := edgeBlocks% "full/vectors/110001-V-0005.bin"
private noncomputable def vp110001_6 : Blocks := edgeBlocks% "full/vectors/110001-V-0006.bin"
private noncomputable def vp110001_7 : Blocks := edgeBlocks% "full/vectors/110001-V-0007.bin"
private noncomputable def vp110001_8 : Blocks := edgeBlocks% "full/vectors/110001-V-0008.bin"
private noncomputable def vp110001_9 : Blocks := edgeBlocks% "full/vectors/110001-V-0009.bin"
private noncomputable def vp110001_10 : Blocks := edgeBlocks% "full/vectors/110001-V-0010.bin"
private noncomputable def vp110001_11 : Blocks := edgeBlocks% "full/vectors/110001-V-0011.bin"
private noncomputable def vp110001_12 : Blocks := edgeBlocks% "full/vectors/110001-V-0012.bin"
noncomputable def vp110001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp110001_0 (Blocks.join vp110001_1 vp110001_2)) (Blocks.join vp110001_3 (Blocks.join vp110001_4 vp110001_5))) (Blocks.join (Blocks.join vp110001_6 (Blocks.join vp110001_7 vp110001_8)) (Blocks.join (Blocks.join vp110001_9 vp110001_10) (Blocks.join vp110001_11 vp110001_12))))
private theorem bp1100010 : Branch 0 (-6271761639/128000000 : ℚ) vp110001 := by
  apply branch_left_normalized (c:=vp1100010) (k:=0) (m:=808) (by decide +kernel)
  rw [show 2*(-6271761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-6271761639/64000000 : ℚ) by norm_num]
  exact coverp1100010
private noncomputable def ep1100011_0 : Blocks := edgeBlocks% "full/vectors/1100011-E-0000.bin"
private noncomputable def ep1100011_1 : Blocks := edgeBlocks% "full/vectors/1100011-E-0001.bin"
private noncomputable def ep1100011_2 : Blocks := edgeBlocks% "full/vectors/1100011-E-0002.bin"
private noncomputable def ep1100011_3 : Blocks := edgeBlocks% "full/vectors/1100011-E-0003.bin"
private noncomputable def ep1100011_4 : Blocks := edgeBlocks% "full/vectors/1100011-E-0004.bin"
private noncomputable def ep1100011_5 : Blocks := edgeBlocks% "full/vectors/1100011-E-0005.bin"
private noncomputable def ep1100011_6 : Blocks := edgeBlocks% "full/vectors/1100011-E-0006.bin"
private noncomputable def ep1100011_7 : Blocks := edgeBlocks% "full/vectors/1100011-E-0007.bin"
private noncomputable def ep1100011_8 : Blocks := edgeBlocks% "full/vectors/1100011-E-0008.bin"
private noncomputable def ep1100011_9 : Blocks := edgeBlocks% "full/vectors/1100011-E-0009.bin"
private noncomputable def ep1100011_10 : Blocks := edgeBlocks% "full/vectors/1100011-E-0010.bin"
private noncomputable def ep1100011_11 : Blocks := edgeBlocks% "full/vectors/1100011-E-0011.bin"
private noncomputable def ep1100011_12 : Blocks := edgeBlocks% "full/vectors/1100011-E-0012.bin"
noncomputable def ep1100011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1100011_0 (Blocks.join ep1100011_1 ep1100011_2)) (Blocks.join ep1100011_3 (Blocks.join ep1100011_4 ep1100011_5))) (Blocks.join (Blocks.join ep1100011_6 (Blocks.join ep1100011_7 ep1100011_8)) (Blocks.join (Blocks.join ep1100011_9 ep1100011_10) (Blocks.join ep1100011_11 ep1100011_12))))
private theorem idp1100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110001.list =
    C ((2:ℤ)^1945) * horner X vp1100011.list + horner X ep1100011.list := by
  exact edge_identity (B := (2:ℤ)^2515) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100011 : Branch 1 (-6271761639/128000000 : ℚ) vp110001 := by
  apply branch_checked idp1100011 (by positivity) (by decide +kernel)
  rw [show 2*(-6271761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-6335761639/64000000 : ℚ) by norm_num]
  exact coverp1100011
theorem coverp110001 : Covers (-6271761639/128000000 : ℚ) vp110001 := join_branches bp1100010 bp1100011
private noncomputable def vp1100001111_0 : Blocks := edgeBlocks% "full/vectors/1100001111-V-0000.bin"
noncomputable def vp1100001111 : Blocks := vp1100001111_0
theorem coverp1100001111 : Covers (-6263761639/8000000 : ℚ) vp1100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp1100001110_0 : Blocks := edgeBlocks% "full/vectors/1100001110-V-0000.bin"
noncomputable def vp1100001110 : Blocks := vp1100001110_0
theorem coverp1100001110 : Covers (-6255761639/8000000 : ℚ) vp1100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp110000111_0 : Blocks := edgeBlocks% "full/vectors/110000111-V-0000.bin"
private noncomputable def vp110000111_1 : Blocks := edgeBlocks% "full/vectors/110000111-V-0001.bin"
noncomputable def vp110000111 : Blocks := (Blocks.join vp110000111_0 vp110000111_1)
private theorem bp1100001110 : Branch 0 (-6255761639/16000000 : ℚ) vp110000111 := by
  apply branch_left_normalized (c:=vp1100001110) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-6255761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6255761639/8000000 : ℚ) by norm_num]
  exact coverp1100001110
private noncomputable def ep1100001111_0 : Blocks := edgeBlocks% "full/vectors/1100001111-E-0000.bin"
private noncomputable def ep1100001111_1 : Blocks := edgeBlocks% "full/vectors/1100001111-E-0001.bin"
noncomputable def ep1100001111 : Blocks := (Blocks.join ep1100001111_0 ep1100001111_1)
private theorem idp1100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110000111.list =
    C ((2:ℤ)^268) * horner X vp1100001111.list + horner X ep1100001111.list := by
  exact edge_identity (B := (2:ℤ)^429) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100001111 : Branch 1 (-6255761639/16000000 : ℚ) vp110000111 := by
  apply branch_checked idp1100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-6255761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6263761639/8000000 : ℚ) by norm_num]
  exact coverp1100001111
theorem coverp110000111 : Covers (-6255761639/16000000 : ℚ) vp110000111 := join_branches bp1100001110 bp1100001111
private noncomputable def vp1100001101_0 : Blocks := edgeBlocks% "full/vectors/1100001101-V-0000.bin"
noncomputable def vp1100001101 : Blocks := vp1100001101_0
theorem coverp1100001101 : Covers (-6247761639/8000000 : ℚ) vp1100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp1100001100_0 : Blocks := edgeBlocks% "full/vectors/1100001100-V-0000.bin"
noncomputable def vp1100001100 : Blocks := vp1100001100_0
theorem coverp1100001100 : Covers (-6239761639/8000000 : ℚ) vp1100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp110000110_0 : Blocks := edgeBlocks% "full/vectors/110000110-V-0000.bin"
private noncomputable def vp110000110_1 : Blocks := edgeBlocks% "full/vectors/110000110-V-0001.bin"
noncomputable def vp110000110 : Blocks := (Blocks.join vp110000110_0 vp110000110_1)
private theorem bp1100001100 : Branch 0 (-6239761639/16000000 : ℚ) vp110000110 := by
  apply branch_left_normalized (c:=vp1100001100) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-6239761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6239761639/8000000 : ℚ) by norm_num]
  exact coverp1100001100
private noncomputable def ep1100001101_0 : Blocks := edgeBlocks% "full/vectors/1100001101-E-0000.bin"
private noncomputable def ep1100001101_1 : Blocks := edgeBlocks% "full/vectors/1100001101-E-0001.bin"
noncomputable def ep1100001101 : Blocks := (Blocks.join ep1100001101_0 ep1100001101_1)
private theorem idp1100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110000110.list =
    C ((2:ℤ)^269) * horner X vp1100001101.list + horner X ep1100001101.list := by
  exact edge_identity (B := (2:ℤ)^431) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100001101 : Branch 1 (-6239761639/16000000 : ℚ) vp110000110 := by
  apply branch_checked idp1100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-6239761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6247761639/8000000 : ℚ) by norm_num]
  exact coverp1100001101
theorem coverp110000110 : Covers (-6239761639/16000000 : ℚ) vp110000110 := join_branches bp1100001100 bp1100001101
private noncomputable def vp11000011_0 : Blocks := edgeBlocks% "full/vectors/11000011-V-0000.bin"
private noncomputable def vp11000011_1 : Blocks := edgeBlocks% "full/vectors/11000011-V-0001.bin"
private noncomputable def vp11000011_2 : Blocks := edgeBlocks% "full/vectors/11000011-V-0002.bin"
private noncomputable def vp11000011_3 : Blocks := edgeBlocks% "full/vectors/11000011-V-0003.bin"
noncomputable def vp11000011 : Blocks := (Blocks.join (Blocks.join vp11000011_0 vp11000011_1) (Blocks.join vp11000011_2 vp11000011_3))
private theorem bp110000110 : Branch 0 (-6239761639/32000000 : ℚ) vp11000011 := by
  apply branch_left_normalized (c:=vp110000110) (k:=0) (m:=222) (by decide +kernel)
  rw [show 2*(-6239761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6239761639/16000000 : ℚ) by norm_num]
  exact coverp110000110
private noncomputable def ep110000111_0 : Blocks := edgeBlocks% "full/vectors/110000111-E-0000.bin"
private noncomputable def ep110000111_1 : Blocks := edgeBlocks% "full/vectors/110000111-E-0001.bin"
private noncomputable def ep110000111_2 : Blocks := edgeBlocks% "full/vectors/110000111-E-0002.bin"
private noncomputable def ep110000111_3 : Blocks := edgeBlocks% "full/vectors/110000111-E-0003.bin"
noncomputable def ep110000111 : Blocks := (Blocks.join (Blocks.join ep110000111_0 ep110000111_1) (Blocks.join ep110000111_2 ep110000111_3))
private theorem idp110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11000011.list =
    C ((2:ℤ)^512) * horner X vp110000111.list + horner X ep110000111.list := by
  exact edge_identity (B := (2:ℤ)^732) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110000111 : Branch 1 (-6239761639/32000000 : ℚ) vp11000011 := by
  apply branch_checked idp110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-6239761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6255761639/16000000 : ℚ) by norm_num]
  exact coverp110000111
theorem coverp11000011 : Covers (-6239761639/32000000 : ℚ) vp11000011 := join_branches bp110000110 bp110000111
private noncomputable def vp1100001011_0 : Blocks := edgeBlocks% "full/vectors/1100001011-V-0000.bin"
noncomputable def vp1100001011 : Blocks := vp1100001011_0
theorem coverp1100001011 : Covers (-6231761639/8000000 : ℚ) vp1100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp1100001010_0 : Blocks := edgeBlocks% "full/vectors/1100001010-V-0000.bin"
noncomputable def vp1100001010 : Blocks := vp1100001010_0
theorem coverp1100001010 : Covers (-6223761639/8000000 : ℚ) vp1100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp110000101_0 : Blocks := edgeBlocks% "full/vectors/110000101-V-0000.bin"
private noncomputable def vp110000101_1 : Blocks := edgeBlocks% "full/vectors/110000101-V-0001.bin"
noncomputable def vp110000101 : Blocks := (Blocks.join vp110000101_0 vp110000101_1)
private theorem bp1100001010 : Branch 0 (-6223761639/16000000 : ℚ) vp110000101 := by
  apply branch_left_normalized (c:=vp1100001010) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-6223761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6223761639/8000000 : ℚ) by norm_num]
  exact coverp1100001010
private noncomputable def ep1100001011_0 : Blocks := edgeBlocks% "full/vectors/1100001011-E-0000.bin"
private noncomputable def ep1100001011_1 : Blocks := edgeBlocks% "full/vectors/1100001011-E-0001.bin"
noncomputable def ep1100001011 : Blocks := (Blocks.join ep1100001011_0 ep1100001011_1)
private theorem idp1100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110000101.list =
    C ((2:ℤ)^268) * horner X vp1100001011.list + horner X ep1100001011.list := by
  exact edge_identity (B := (2:ℤ)^430) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100001011 : Branch 1 (-6223761639/16000000 : ℚ) vp110000101 := by
  apply branch_checked idp1100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-6223761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6231761639/8000000 : ℚ) by norm_num]
  exact coverp1100001011
theorem coverp110000101 : Covers (-6223761639/16000000 : ℚ) vp110000101 := join_branches bp1100001010 bp1100001011
private noncomputable def vp1100001001_0 : Blocks := edgeBlocks% "full/vectors/1100001001-V-0000.bin"
noncomputable def vp1100001001 : Blocks := vp1100001001_0
theorem coverp1100001001 : Covers (-6215761639/8000000 : ℚ) vp1100001001 := cover_leaf (by decide +kernel)
private noncomputable def vp1100001000_0 : Blocks := edgeBlocks% "full/vectors/1100001000-V-0000.bin"
noncomputable def vp1100001000 : Blocks := vp1100001000_0
theorem coverp1100001000 : Covers (-6207761639/8000000 : ℚ) vp1100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp110000100_0 : Blocks := edgeBlocks% "full/vectors/110000100-V-0000.bin"
private noncomputable def vp110000100_1 : Blocks := edgeBlocks% "full/vectors/110000100-V-0001.bin"
noncomputable def vp110000100 : Blocks := (Blocks.join vp110000100_0 vp110000100_1)
private theorem bp1100001000 : Branch 0 (-6207761639/16000000 : ℚ) vp110000100 := by
  apply branch_left_normalized (c:=vp1100001000) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-6207761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6207761639/8000000 : ℚ) by norm_num]
  exact coverp1100001000
private noncomputable def ep1100001001_0 : Blocks := edgeBlocks% "full/vectors/1100001001-E-0000.bin"
private noncomputable def ep1100001001_1 : Blocks := edgeBlocks% "full/vectors/1100001001-E-0001.bin"
noncomputable def ep1100001001 : Blocks := (Blocks.join ep1100001001_0 ep1100001001_1)
private theorem idp1100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110000100.list =
    C ((2:ℤ)^269) * horner X vp1100001001.list + horner X ep1100001001.list := by
  exact edge_identity (B := (2:ℤ)^430) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100001001 : Branch 1 (-6207761639/16000000 : ℚ) vp110000100 := by
  apply branch_checked idp1100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-6207761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6215761639/8000000 : ℚ) by norm_num]
  exact coverp1100001001
theorem coverp110000100 : Covers (-6207761639/16000000 : ℚ) vp110000100 := join_branches bp1100001000 bp1100001001
private noncomputable def vp11000010_0 : Blocks := edgeBlocks% "full/vectors/11000010-V-0000.bin"
private noncomputable def vp11000010_1 : Blocks := edgeBlocks% "full/vectors/11000010-V-0001.bin"
private noncomputable def vp11000010_2 : Blocks := edgeBlocks% "full/vectors/11000010-V-0002.bin"
private noncomputable def vp11000010_3 : Blocks := edgeBlocks% "full/vectors/11000010-V-0003.bin"
noncomputable def vp11000010 : Blocks := (Blocks.join (Blocks.join vp11000010_0 vp11000010_1) (Blocks.join vp11000010_2 vp11000010_3))
private theorem bp110000100 : Branch 0 (-6207761639/32000000 : ℚ) vp11000010 := by
  apply branch_left_normalized (c:=vp110000100) (k:=0) (m:=222) (by decide +kernel)
  rw [show 2*(-6207761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6207761639/16000000 : ℚ) by norm_num]
  exact coverp110000100
private noncomputable def ep110000101_0 : Blocks := edgeBlocks% "full/vectors/110000101-E-0000.bin"
private noncomputable def ep110000101_1 : Blocks := edgeBlocks% "full/vectors/110000101-E-0001.bin"
private noncomputable def ep110000101_2 : Blocks := edgeBlocks% "full/vectors/110000101-E-0002.bin"
private noncomputable def ep110000101_3 : Blocks := edgeBlocks% "full/vectors/110000101-E-0003.bin"
noncomputable def ep110000101 : Blocks := (Blocks.join (Blocks.join ep110000101_0 ep110000101_1) (Blocks.join ep110000101_2 ep110000101_3))
private theorem idp110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11000010.list =
    C ((2:ℤ)^513) * horner X vp110000101.list + horner X ep110000101.list := by
  exact edge_identity (B := (2:ℤ)^734) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110000101 : Branch 1 (-6207761639/32000000 : ℚ) vp11000010 := by
  apply branch_checked idp110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-6207761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6223761639/16000000 : ℚ) by norm_num]
  exact coverp110000101
theorem coverp11000010 : Covers (-6207761639/32000000 : ℚ) vp11000010 := join_branches bp110000100 bp110000101
private noncomputable def vp1100001_0 : Blocks := edgeBlocks% "full/vectors/1100001-V-0000.bin"
private noncomputable def vp1100001_1 : Blocks := edgeBlocks% "full/vectors/1100001-V-0001.bin"
private noncomputable def vp1100001_2 : Blocks := edgeBlocks% "full/vectors/1100001-V-0002.bin"
private noncomputable def vp1100001_3 : Blocks := edgeBlocks% "full/vectors/1100001-V-0003.bin"
private noncomputable def vp1100001_4 : Blocks := edgeBlocks% "full/vectors/1100001-V-0004.bin"
private noncomputable def vp1100001_5 : Blocks := edgeBlocks% "full/vectors/1100001-V-0005.bin"
private noncomputable def vp1100001_6 : Blocks := edgeBlocks% "full/vectors/1100001-V-0006.bin"
noncomputable def vp1100001 : Blocks := (Blocks.join (Blocks.join vp1100001_0 (Blocks.join vp1100001_1 vp1100001_2)) (Blocks.join (Blocks.join vp1100001_3 vp1100001_4) (Blocks.join vp1100001_5 vp1100001_6)))
private theorem bp11000010 : Branch 0 (-6207761639/64000000 : ℚ) vp1100001 := by
  apply branch_left_normalized (c:=vp11000010) (k:=0) (m:=420) (by decide +kernel)
  rw [show 2*(-6207761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6207761639/32000000 : ℚ) by norm_num]
  exact coverp11000010
private noncomputable def ep11000011_0 : Blocks := edgeBlocks% "full/vectors/11000011-E-0000.bin"
private noncomputable def ep11000011_1 : Blocks := edgeBlocks% "full/vectors/11000011-E-0001.bin"
private noncomputable def ep11000011_2 : Blocks := edgeBlocks% "full/vectors/11000011-E-0002.bin"
private noncomputable def ep11000011_3 : Blocks := edgeBlocks% "full/vectors/11000011-E-0003.bin"
private noncomputable def ep11000011_4 : Blocks := edgeBlocks% "full/vectors/11000011-E-0004.bin"
private noncomputable def ep11000011_5 : Blocks := edgeBlocks% "full/vectors/11000011-E-0005.bin"
private noncomputable def ep11000011_6 : Blocks := edgeBlocks% "full/vectors/11000011-E-0006.bin"
noncomputable def ep11000011 : Blocks := (Blocks.join (Blocks.join ep11000011_0 (Blocks.join ep11000011_1 ep11000011_2)) (Blocks.join (Blocks.join ep11000011_3 ep11000011_4) (Blocks.join ep11000011_5 ep11000011_6)))
private theorem idp11000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1100001.list =
    C ((2:ℤ)^997) * horner X vp11000011.list + horner X ep11000011.list := by
  exact edge_identity (B := (2:ℤ)^1337) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11000011 : Branch 1 (-6207761639/64000000 : ℚ) vp1100001 := by
  apply branch_checked idp11000011 (by positivity) (by decide +kernel)
  rw [show 2*(-6207761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6239761639/32000000 : ℚ) by norm_num]
  exact coverp11000011
theorem coverp1100001 : Covers (-6207761639/64000000 : ℚ) vp1100001 := join_branches bp11000010 bp11000011
private noncomputable def vp1100000111_0 : Blocks := edgeBlocks% "full/vectors/1100000111-V-0000.bin"
noncomputable def vp1100000111 : Blocks := vp1100000111_0
theorem coverp1100000111 : Covers (-6199761639/8000000 : ℚ) vp1100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp1100000110_0 : Blocks := edgeBlocks% "full/vectors/1100000110-V-0000.bin"
noncomputable def vp1100000110 : Blocks := vp1100000110_0
theorem coverp1100000110 : Covers (-6191761639/8000000 : ℚ) vp1100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp110000011_0 : Blocks := edgeBlocks% "full/vectors/110000011-V-0000.bin"
private noncomputable def vp110000011_1 : Blocks := edgeBlocks% "full/vectors/110000011-V-0001.bin"
noncomputable def vp110000011 : Blocks := (Blocks.join vp110000011_0 vp110000011_1)
private theorem bp1100000110 : Branch 0 (-6191761639/16000000 : ℚ) vp110000011 := by
  apply branch_left_normalized (c:=vp1100000110) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-6191761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6191761639/8000000 : ℚ) by norm_num]
  exact coverp1100000110
private noncomputable def ep1100000111_0 : Blocks := edgeBlocks% "full/vectors/1100000111-E-0000.bin"
private noncomputable def ep1100000111_1 : Blocks := edgeBlocks% "full/vectors/1100000111-E-0001.bin"
noncomputable def ep1100000111 : Blocks := (Blocks.join ep1100000111_0 ep1100000111_1)
private theorem idp1100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110000011.list =
    C ((2:ℤ)^270) * horner X vp1100000111.list + horner X ep1100000111.list := by
  exact edge_identity (B := (2:ℤ)^431) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100000111 : Branch 1 (-6191761639/16000000 : ℚ) vp110000011 := by
  apply branch_checked idp1100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-6191761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6199761639/8000000 : ℚ) by norm_num]
  exact coverp1100000111
theorem coverp110000011 : Covers (-6191761639/16000000 : ℚ) vp110000011 := join_branches bp1100000110 bp1100000111
private noncomputable def vp1100000101_0 : Blocks := edgeBlocks% "full/vectors/1100000101-V-0000.bin"
noncomputable def vp1100000101 : Blocks := vp1100000101_0
theorem coverp1100000101 : Covers (-6183761639/8000000 : ℚ) vp1100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp1100000100_0 : Blocks := edgeBlocks% "full/vectors/1100000100-V-0000.bin"
noncomputable def vp1100000100 : Blocks := vp1100000100_0
theorem coverp1100000100 : Covers (-6175761639/8000000 : ℚ) vp1100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp110000010_0 : Blocks := edgeBlocks% "full/vectors/110000010-V-0000.bin"
private noncomputable def vp110000010_1 : Blocks := edgeBlocks% "full/vectors/110000010-V-0001.bin"
noncomputable def vp110000010 : Blocks := (Blocks.join vp110000010_0 vp110000010_1)
private theorem bp1100000100 : Branch 0 (-6175761639/16000000 : ℚ) vp110000010 := by
  apply branch_left_normalized (c:=vp1100000100) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-6175761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6175761639/8000000 : ℚ) by norm_num]
  exact coverp1100000100
private noncomputable def ep1100000101_0 : Blocks := edgeBlocks% "full/vectors/1100000101-E-0000.bin"
private noncomputable def ep1100000101_1 : Blocks := edgeBlocks% "full/vectors/1100000101-E-0001.bin"
noncomputable def ep1100000101 : Blocks := (Blocks.join ep1100000101_0 ep1100000101_1)
private theorem idp1100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110000010.list =
    C ((2:ℤ)^269) * horner X vp1100000101.list + horner X ep1100000101.list := by
  exact edge_identity (B := (2:ℤ)^431) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100000101 : Branch 1 (-6175761639/16000000 : ℚ) vp110000010 := by
  apply branch_checked idp1100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-6175761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6183761639/8000000 : ℚ) by norm_num]
  exact coverp1100000101
theorem coverp110000010 : Covers (-6175761639/16000000 : ℚ) vp110000010 := join_branches bp1100000100 bp1100000101
private noncomputable def vp11000001_0 : Blocks := edgeBlocks% "full/vectors/11000001-V-0000.bin"
private noncomputable def vp11000001_1 : Blocks := edgeBlocks% "full/vectors/11000001-V-0001.bin"
private noncomputable def vp11000001_2 : Blocks := edgeBlocks% "full/vectors/11000001-V-0002.bin"
private noncomputable def vp11000001_3 : Blocks := edgeBlocks% "full/vectors/11000001-V-0003.bin"
noncomputable def vp11000001 : Blocks := (Blocks.join (Blocks.join vp11000001_0 vp11000001_1) (Blocks.join vp11000001_2 vp11000001_3))
private theorem bp110000010 : Branch 0 (-6175761639/32000000 : ℚ) vp11000001 := by
  apply branch_left_normalized (c:=vp110000010) (k:=0) (m:=222) (by decide +kernel)
  rw [show 2*(-6175761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6175761639/16000000 : ℚ) by norm_num]
  exact coverp110000010
private noncomputable def ep110000011_0 : Blocks := edgeBlocks% "full/vectors/110000011-E-0000.bin"
private noncomputable def ep110000011_1 : Blocks := edgeBlocks% "full/vectors/110000011-E-0001.bin"
private noncomputable def ep110000011_2 : Blocks := edgeBlocks% "full/vectors/110000011-E-0002.bin"
private noncomputable def ep110000011_3 : Blocks := edgeBlocks% "full/vectors/110000011-E-0003.bin"
noncomputable def ep110000011 : Blocks := (Blocks.join (Blocks.join ep110000011_0 ep110000011_1) (Blocks.join ep110000011_2 ep110000011_3))
private theorem idp110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11000001.list =
    C ((2:ℤ)^514) * horner X vp110000011.list + horner X ep110000011.list := by
  exact edge_identity (B := (2:ℤ)^736) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110000011 : Branch 1 (-6175761639/32000000 : ℚ) vp11000001 := by
  apply branch_checked idp110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-6175761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6191761639/16000000 : ℚ) by norm_num]
  exact coverp110000011
theorem coverp11000001 : Covers (-6175761639/32000000 : ℚ) vp11000001 := join_branches bp110000010 bp110000011
private noncomputable def vp1100000011_0 : Blocks := edgeBlocks% "full/vectors/1100000011-V-0000.bin"
noncomputable def vp1100000011 : Blocks := vp1100000011_0
theorem coverp1100000011 : Covers (-6167761639/8000000 : ℚ) vp1100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp1100000010_0 : Blocks := edgeBlocks% "full/vectors/1100000010-V-0000.bin"
noncomputable def vp1100000010 : Blocks := vp1100000010_0
theorem coverp1100000010 : Covers (-6159761639/8000000 : ℚ) vp1100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp110000001_0 : Blocks := edgeBlocks% "full/vectors/110000001-V-0000.bin"
private noncomputable def vp110000001_1 : Blocks := edgeBlocks% "full/vectors/110000001-V-0001.bin"
noncomputable def vp110000001 : Blocks := (Blocks.join vp110000001_0 vp110000001_1)
private theorem bp1100000010 : Branch 0 (-6159761639/16000000 : ℚ) vp110000001 := by
  apply branch_left_normalized (c:=vp1100000010) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-6159761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6159761639/8000000 : ℚ) by norm_num]
  exact coverp1100000010
private noncomputable def ep1100000011_0 : Blocks := edgeBlocks% "full/vectors/1100000011-E-0000.bin"
private noncomputable def ep1100000011_1 : Blocks := edgeBlocks% "full/vectors/1100000011-E-0001.bin"
noncomputable def ep1100000011 : Blocks := (Blocks.join ep1100000011_0 ep1100000011_1)
private theorem idp1100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110000001.list =
    C ((2:ℤ)^270) * horner X vp1100000011.list + horner X ep1100000011.list := by
  exact edge_identity (B := (2:ℤ)^432) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100000011 : Branch 1 (-6159761639/16000000 : ℚ) vp110000001 := by
  apply branch_checked idp1100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-6159761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6167761639/8000000 : ℚ) by norm_num]
  exact coverp1100000011
theorem coverp110000001 : Covers (-6159761639/16000000 : ℚ) vp110000001 := join_branches bp1100000010 bp1100000011
private noncomputable def vp1100000001_0 : Blocks := edgeBlocks% "full/vectors/1100000001-V-0000.bin"
noncomputable def vp1100000001 : Blocks := vp1100000001_0
theorem coverp1100000001 : Covers (-6151761639/8000000 : ℚ) vp1100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp1100000000_0 : Blocks := edgeBlocks% "full/vectors/1100000000-V-0000.bin"
noncomputable def vp1100000000 : Blocks := vp1100000000_0
theorem coverp1100000000 : Covers (-6143761639/8000000 : ℚ) vp1100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp110000000_0 : Blocks := edgeBlocks% "full/vectors/110000000-V-0000.bin"
private noncomputable def vp110000000_1 : Blocks := edgeBlocks% "full/vectors/110000000-V-0001.bin"
noncomputable def vp110000000 : Blocks := (Blocks.join vp110000000_0 vp110000000_1)
private theorem bp1100000000 : Branch 0 (-6143761639/16000000 : ℚ) vp110000000 := by
  apply branch_left_normalized (c:=vp1100000000) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-6143761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6143761639/8000000 : ℚ) by norm_num]
  exact coverp1100000000
private noncomputable def ep1100000001_0 : Blocks := edgeBlocks% "full/vectors/1100000001-E-0000.bin"
private noncomputable def ep1100000001_1 : Blocks := edgeBlocks% "full/vectors/1100000001-E-0001.bin"
noncomputable def ep1100000001 : Blocks := (Blocks.join ep1100000001_0 ep1100000001_1)
private theorem idp1100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110000000.list =
    C ((2:ℤ)^270) * horner X vp1100000001.list + horner X ep1100000001.list := by
  exact edge_identity (B := (2:ℤ)^432) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100000001 : Branch 1 (-6143761639/16000000 : ℚ) vp110000000 := by
  apply branch_checked idp1100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-6143761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6151761639/8000000 : ℚ) by norm_num]
  exact coverp1100000001
theorem coverp110000000 : Covers (-6143761639/16000000 : ℚ) vp110000000 := join_branches bp1100000000 bp1100000001
private noncomputable def vp11000000_0 : Blocks := edgeBlocks% "full/vectors/11000000-V-0000.bin"
private noncomputable def vp11000000_1 : Blocks := edgeBlocks% "full/vectors/11000000-V-0001.bin"
private noncomputable def vp11000000_2 : Blocks := edgeBlocks% "full/vectors/11000000-V-0002.bin"
private noncomputable def vp11000000_3 : Blocks := edgeBlocks% "full/vectors/11000000-V-0003.bin"
noncomputable def vp11000000 : Blocks := (Blocks.join (Blocks.join vp11000000_0 vp11000000_1) (Blocks.join vp11000000_2 vp11000000_3))
private theorem bp110000000 : Branch 0 (-6143761639/32000000 : ℚ) vp11000000 := by
  apply branch_left_normalized (c:=vp110000000) (k:=0) (m:=222) (by decide +kernel)
  rw [show 2*(-6143761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6143761639/16000000 : ℚ) by norm_num]
  exact coverp110000000
private noncomputable def ep110000001_0 : Blocks := edgeBlocks% "full/vectors/110000001-E-0000.bin"
private noncomputable def ep110000001_1 : Blocks := edgeBlocks% "full/vectors/110000001-E-0001.bin"
private noncomputable def ep110000001_2 : Blocks := edgeBlocks% "full/vectors/110000001-E-0002.bin"
private noncomputable def ep110000001_3 : Blocks := edgeBlocks% "full/vectors/110000001-E-0003.bin"
noncomputable def ep110000001 : Blocks := (Blocks.join (Blocks.join ep110000001_0 ep110000001_1) (Blocks.join ep110000001_2 ep110000001_3))
private theorem idp110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11000000.list =
    C ((2:ℤ)^516) * horner X vp110000001.list + horner X ep110000001.list := by
  exact edge_identity (B := (2:ℤ)^738) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110000001 : Branch 1 (-6143761639/32000000 : ℚ) vp11000000 := by
  apply branch_checked idp110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-6143761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6159761639/16000000 : ℚ) by norm_num]
  exact coverp110000001
theorem coverp11000000 : Covers (-6143761639/32000000 : ℚ) vp11000000 := join_branches bp110000000 bp110000001
private noncomputable def vp1100000_0 : Blocks := edgeBlocks% "full/vectors/1100000-V-0000.bin"
private noncomputable def vp1100000_1 : Blocks := edgeBlocks% "full/vectors/1100000-V-0001.bin"
private noncomputable def vp1100000_2 : Blocks := edgeBlocks% "full/vectors/1100000-V-0002.bin"
private noncomputable def vp1100000_3 : Blocks := edgeBlocks% "full/vectors/1100000-V-0003.bin"
private noncomputable def vp1100000_4 : Blocks := edgeBlocks% "full/vectors/1100000-V-0004.bin"
private noncomputable def vp1100000_5 : Blocks := edgeBlocks% "full/vectors/1100000-V-0005.bin"
private noncomputable def vp1100000_6 : Blocks := edgeBlocks% "full/vectors/1100000-V-0006.bin"
noncomputable def vp1100000 : Blocks := (Blocks.join (Blocks.join vp1100000_0 (Blocks.join vp1100000_1 vp1100000_2)) (Blocks.join (Blocks.join vp1100000_3 vp1100000_4) (Blocks.join vp1100000_5 vp1100000_6)))
private theorem bp11000000 : Branch 0 (-6143761639/64000000 : ℚ) vp1100000 := by
  apply branch_left_normalized (c:=vp11000000) (k:=0) (m:=422) (by decide +kernel)
  rw [show 2*(-6143761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6143761639/32000000 : ℚ) by norm_num]
  exact coverp11000000
private noncomputable def ep11000001_0 : Blocks := edgeBlocks% "full/vectors/11000001-E-0000.bin"
private noncomputable def ep11000001_1 : Blocks := edgeBlocks% "full/vectors/11000001-E-0001.bin"
private noncomputable def ep11000001_2 : Blocks := edgeBlocks% "full/vectors/11000001-E-0002.bin"
private noncomputable def ep11000001_3 : Blocks := edgeBlocks% "full/vectors/11000001-E-0003.bin"
private noncomputable def ep11000001_4 : Blocks := edgeBlocks% "full/vectors/11000001-E-0004.bin"
private noncomputable def ep11000001_5 : Blocks := edgeBlocks% "full/vectors/11000001-E-0005.bin"
private noncomputable def ep11000001_6 : Blocks := edgeBlocks% "full/vectors/11000001-E-0006.bin"
noncomputable def ep11000001 : Blocks := (Blocks.join (Blocks.join ep11000001_0 (Blocks.join ep11000001_1 ep11000001_2)) (Blocks.join (Blocks.join ep11000001_3 ep11000001_4) (Blocks.join ep11000001_5 ep11000001_6)))
private theorem idp11000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1100000.list =
    C ((2:ℤ)^1002) * horner X vp11000001.list + horner X ep11000001.list := by
  exact edge_identity (B := (2:ℤ)^1344) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11000001 : Branch 1 (-6143761639/64000000 : ℚ) vp1100000 := by
  apply branch_checked idp11000001 (by positivity) (by decide +kernel)
  rw [show 2*(-6143761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6175761639/32000000 : ℚ) by norm_num]
  exact coverp11000001
theorem coverp1100000 : Covers (-6143761639/64000000 : ℚ) vp1100000 := join_branches bp11000000 bp11000001
private noncomputable def vp110000_0 : Blocks := edgeBlocks% "full/vectors/110000-V-0000.bin"
private noncomputable def vp110000_1 : Blocks := edgeBlocks% "full/vectors/110000-V-0001.bin"
private noncomputable def vp110000_2 : Blocks := edgeBlocks% "full/vectors/110000-V-0002.bin"
private noncomputable def vp110000_3 : Blocks := edgeBlocks% "full/vectors/110000-V-0003.bin"
private noncomputable def vp110000_4 : Blocks := edgeBlocks% "full/vectors/110000-V-0004.bin"
private noncomputable def vp110000_5 : Blocks := edgeBlocks% "full/vectors/110000-V-0005.bin"
private noncomputable def vp110000_6 : Blocks := edgeBlocks% "full/vectors/110000-V-0006.bin"
private noncomputable def vp110000_7 : Blocks := edgeBlocks% "full/vectors/110000-V-0007.bin"
private noncomputable def vp110000_8 : Blocks := edgeBlocks% "full/vectors/110000-V-0008.bin"
private noncomputable def vp110000_9 : Blocks := edgeBlocks% "full/vectors/110000-V-0009.bin"
private noncomputable def vp110000_10 : Blocks := edgeBlocks% "full/vectors/110000-V-0010.bin"
private noncomputable def vp110000_11 : Blocks := edgeBlocks% "full/vectors/110000-V-0011.bin"
private noncomputable def vp110000_12 : Blocks := edgeBlocks% "full/vectors/110000-V-0012.bin"
noncomputable def vp110000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp110000_0 (Blocks.join vp110000_1 vp110000_2)) (Blocks.join vp110000_3 (Blocks.join vp110000_4 vp110000_5))) (Blocks.join (Blocks.join vp110000_6 (Blocks.join vp110000_7 vp110000_8)) (Blocks.join (Blocks.join vp110000_9 vp110000_10) (Blocks.join vp110000_11 vp110000_12))))
private theorem bp1100000 : Branch 0 (-6143761639/128000000 : ℚ) vp110000 := by
  apply branch_left_normalized (c:=vp1100000) (k:=0) (m:=816) (by decide +kernel)
  rw [show 2*(-6143761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-6143761639/64000000 : ℚ) by norm_num]
  exact coverp1100000
private noncomputable def ep1100001_0 : Blocks := edgeBlocks% "full/vectors/1100001-E-0000.bin"
private noncomputable def ep1100001_1 : Blocks := edgeBlocks% "full/vectors/1100001-E-0001.bin"
private noncomputable def ep1100001_2 : Blocks := edgeBlocks% "full/vectors/1100001-E-0002.bin"
private noncomputable def ep1100001_3 : Blocks := edgeBlocks% "full/vectors/1100001-E-0003.bin"
private noncomputable def ep1100001_4 : Blocks := edgeBlocks% "full/vectors/1100001-E-0004.bin"
private noncomputable def ep1100001_5 : Blocks := edgeBlocks% "full/vectors/1100001-E-0005.bin"
private noncomputable def ep1100001_6 : Blocks := edgeBlocks% "full/vectors/1100001-E-0006.bin"
private noncomputable def ep1100001_7 : Blocks := edgeBlocks% "full/vectors/1100001-E-0007.bin"
private noncomputable def ep1100001_8 : Blocks := edgeBlocks% "full/vectors/1100001-E-0008.bin"
private noncomputable def ep1100001_9 : Blocks := edgeBlocks% "full/vectors/1100001-E-0009.bin"
private noncomputable def ep1100001_10 : Blocks := edgeBlocks% "full/vectors/1100001-E-0010.bin"
private noncomputable def ep1100001_11 : Blocks := edgeBlocks% "full/vectors/1100001-E-0011.bin"
private noncomputable def ep1100001_12 : Blocks := edgeBlocks% "full/vectors/1100001-E-0012.bin"
noncomputable def ep1100001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1100001_0 (Blocks.join ep1100001_1 ep1100001_2)) (Blocks.join ep1100001_3 (Blocks.join ep1100001_4 ep1100001_5))) (Blocks.join (Blocks.join ep1100001_6 (Blocks.join ep1100001_7 ep1100001_8)) (Blocks.join (Blocks.join ep1100001_9 ep1100001_10) (Blocks.join ep1100001_11 ep1100001_12))))
private theorem idp1100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110000.list =
    C ((2:ℤ)^1961) * horner X vp1100001.list + horner X ep1100001.list := by
  exact edge_identity (B := (2:ℤ)^2539) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1100001 : Branch 1 (-6143761639/128000000 : ℚ) vp110000 := by
  apply branch_checked idp1100001 (by positivity) (by decide +kernel)
  rw [show 2*(-6143761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-6207761639/64000000 : ℚ) by norm_num]
  exact coverp1100001
theorem coverp110000 : Covers (-6143761639/128000000 : ℚ) vp110000 := join_branches bp1100000 bp1100001
private noncomputable def vp11000_0 : Blocks := edgeBlocks% "full/vectors/11000-V-0000.bin"
private noncomputable def vp11000_1 : Blocks := edgeBlocks% "full/vectors/11000-V-0001.bin"
private noncomputable def vp11000_2 : Blocks := edgeBlocks% "full/vectors/11000-V-0002.bin"
private noncomputable def vp11000_3 : Blocks := edgeBlocks% "full/vectors/11000-V-0003.bin"
private noncomputable def vp11000_4 : Blocks := edgeBlocks% "full/vectors/11000-V-0004.bin"
private noncomputable def vp11000_5 : Blocks := edgeBlocks% "full/vectors/11000-V-0005.bin"
private noncomputable def vp11000_6 : Blocks := edgeBlocks% "full/vectors/11000-V-0006.bin"
private noncomputable def vp11000_7 : Blocks := edgeBlocks% "full/vectors/11000-V-0007.bin"
private noncomputable def vp11000_8 : Blocks := edgeBlocks% "full/vectors/11000-V-0008.bin"
private noncomputable def vp11000_9 : Blocks := edgeBlocks% "full/vectors/11000-V-0009.bin"
private noncomputable def vp11000_10 : Blocks := edgeBlocks% "full/vectors/11000-V-0010.bin"
private noncomputable def vp11000_11 : Blocks := edgeBlocks% "full/vectors/11000-V-0011.bin"
private noncomputable def vp11000_12 : Blocks := edgeBlocks% "full/vectors/11000-V-0012.bin"
private noncomputable def vp11000_13 : Blocks := edgeBlocks% "full/vectors/11000-V-0013.bin"
private noncomputable def vp11000_14 : Blocks := edgeBlocks% "full/vectors/11000-V-0014.bin"
private noncomputable def vp11000_15 : Blocks := edgeBlocks% "full/vectors/11000-V-0015.bin"
private noncomputable def vp11000_16 : Blocks := edgeBlocks% "full/vectors/11000-V-0016.bin"
private noncomputable def vp11000_17 : Blocks := edgeBlocks% "full/vectors/11000-V-0017.bin"
private noncomputable def vp11000_18 : Blocks := edgeBlocks% "full/vectors/11000-V-0018.bin"
private noncomputable def vp11000_19 : Blocks := edgeBlocks% "full/vectors/11000-V-0019.bin"
private noncomputable def vp11000_20 : Blocks := edgeBlocks% "full/vectors/11000-V-0020.bin"
private noncomputable def vp11000_21 : Blocks := edgeBlocks% "full/vectors/11000-V-0021.bin"
private noncomputable def vp11000_22 : Blocks := edgeBlocks% "full/vectors/11000-V-0022.bin"
private noncomputable def vp11000_23 : Blocks := edgeBlocks% "full/vectors/11000-V-0023.bin"
private noncomputable def vp11000_24 : Blocks := edgeBlocks% "full/vectors/11000-V-0024.bin"
noncomputable def vp11000 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp11000_0 (Blocks.join vp11000_1 vp11000_2)) (Blocks.join vp11000_3 (Blocks.join vp11000_4 vp11000_5))) (Blocks.join (Blocks.join vp11000_6 (Blocks.join vp11000_7 vp11000_8)) (Blocks.join vp11000_9 (Blocks.join vp11000_10 vp11000_11)))) (Blocks.join (Blocks.join (Blocks.join vp11000_12 (Blocks.join vp11000_13 vp11000_14)) (Blocks.join vp11000_15 (Blocks.join vp11000_16 vp11000_17))) (Blocks.join (Blocks.join vp11000_18 (Blocks.join vp11000_19 vp11000_20)) (Blocks.join (Blocks.join vp11000_21 vp11000_22) (Blocks.join vp11000_23 vp11000_24)))))
private theorem bp110000 : Branch 0 (-6143761639/256000000 : ℚ) vp11000 := by
  apply branch_left_normalized (c:=vp110000) (k:=0) (m:=1590) (by decide +kernel)
  rw [show 2*(-6143761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-6143761639/128000000 : ℚ) by norm_num]
  exact coverp110000
private noncomputable def ep110001_0 : Blocks := edgeBlocks% "full/vectors/110001-E-0000.bin"
private noncomputable def ep110001_1 : Blocks := edgeBlocks% "full/vectors/110001-E-0001.bin"
private noncomputable def ep110001_2 : Blocks := edgeBlocks% "full/vectors/110001-E-0002.bin"
private noncomputable def ep110001_3 : Blocks := edgeBlocks% "full/vectors/110001-E-0003.bin"
private noncomputable def ep110001_4 : Blocks := edgeBlocks% "full/vectors/110001-E-0004.bin"
private noncomputable def ep110001_5 : Blocks := edgeBlocks% "full/vectors/110001-E-0005.bin"
private noncomputable def ep110001_6 : Blocks := edgeBlocks% "full/vectors/110001-E-0006.bin"
private noncomputable def ep110001_7 : Blocks := edgeBlocks% "full/vectors/110001-E-0007.bin"
private noncomputable def ep110001_8 : Blocks := edgeBlocks% "full/vectors/110001-E-0008.bin"
private noncomputable def ep110001_9 : Blocks := edgeBlocks% "full/vectors/110001-E-0009.bin"
private noncomputable def ep110001_10 : Blocks := edgeBlocks% "full/vectors/110001-E-0010.bin"
private noncomputable def ep110001_11 : Blocks := edgeBlocks% "full/vectors/110001-E-0011.bin"
private noncomputable def ep110001_12 : Blocks := edgeBlocks% "full/vectors/110001-E-0012.bin"
private noncomputable def ep110001_13 : Blocks := edgeBlocks% "full/vectors/110001-E-0013.bin"
private noncomputable def ep110001_14 : Blocks := edgeBlocks% "full/vectors/110001-E-0014.bin"
private noncomputable def ep110001_15 : Blocks := edgeBlocks% "full/vectors/110001-E-0015.bin"
private noncomputable def ep110001_16 : Blocks := edgeBlocks% "full/vectors/110001-E-0016.bin"
private noncomputable def ep110001_17 : Blocks := edgeBlocks% "full/vectors/110001-E-0017.bin"
private noncomputable def ep110001_18 : Blocks := edgeBlocks% "full/vectors/110001-E-0018.bin"
private noncomputable def ep110001_19 : Blocks := edgeBlocks% "full/vectors/110001-E-0019.bin"
private noncomputable def ep110001_20 : Blocks := edgeBlocks% "full/vectors/110001-E-0020.bin"
private noncomputable def ep110001_21 : Blocks := edgeBlocks% "full/vectors/110001-E-0021.bin"
private noncomputable def ep110001_22 : Blocks := edgeBlocks% "full/vectors/110001-E-0022.bin"
private noncomputable def ep110001_23 : Blocks := edgeBlocks% "full/vectors/110001-E-0023.bin"
private noncomputable def ep110001_24 : Blocks := edgeBlocks% "full/vectors/110001-E-0024.bin"
noncomputable def ep110001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep110001_0 (Blocks.join ep110001_1 ep110001_2)) (Blocks.join ep110001_3 (Blocks.join ep110001_4 ep110001_5))) (Blocks.join (Blocks.join ep110001_6 (Blocks.join ep110001_7 ep110001_8)) (Blocks.join ep110001_9 (Blocks.join ep110001_10 ep110001_11)))) (Blocks.join (Blocks.join (Blocks.join ep110001_12 (Blocks.join ep110001_13 ep110001_14)) (Blocks.join ep110001_15 (Blocks.join ep110001_16 ep110001_17))) (Blocks.join (Blocks.join ep110001_18 (Blocks.join ep110001_19 ep110001_20)) (Blocks.join (Blocks.join ep110001_21 ep110001_22) (Blocks.join ep110001_23 ep110001_24)))))
private def ptsp110001 : List ℤ := [((2:ℤ)^3894+0),((2:ℤ)^3894+1)]
private theorem boundp110001 : 2^vp11000.size*absSum vp11000.list + ((2:ℤ)^3820*absSum vp110001.list+absSum ep110001.list) < (2:ℤ)^4859 := by decide +kernel
private theorem pointp110001_0 : fastHom 1 ((2:ℤ)^3894+0) vp11000 = ((2:ℤ)^3820)*vp110001.subst ((2:ℤ)^3894+0)+ep110001.subst ((2:ℤ)^3894+0) := by decide +kernel
private theorem pointp110001_1 : fastHom 1 ((2:ℤ)^3894+1) vp11000 = ((2:ℤ)^3820)*vp110001.subst ((2:ℤ)^3894+1)+ep110001.subst ((2:ℤ)^3894+1) := by decide +kernel
private theorem checkp110001 (x:ℤ) (hx:x ∈ ptsp110001) : fastHom 1 x vp11000 = ((2:ℤ)^3820)*vp110001.subst x+ep110001.subst x := by
  simp only [ptsp110001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp110001_0
  · exact pointp110001_1
private theorem idp110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11000.list =
    C ((2:ℤ)^3820) * horner X vp110001.list + horner X ep110001.list := by
  apply edge_identity (B := (2:ℤ)^4859) (by decide) (by positivity) (by positivity) boundp110001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp110001 (by decide +kernel)
  · have h : ptsp110001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp110001.trans_le (by decide +kernel)
  · exact checkp110001
private theorem bp110001 : Branch 1 (-6143761639/256000000 : ℚ) vp11000 := by
  apply branch_checked idp110001 (by positivity) (by decide +kernel)
  rw [show 2*(-6143761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-6271761639/128000000 : ℚ) by norm_num]
  exact coverp110001
theorem coverp11000 : Covers (-6143761639/256000000 : ℚ) vp11000 := join_branches bp110000 bp110001
private noncomputable def vp1100_0 : Blocks := edgeBlocks% "full/vectors/1100-V-0000.bin"
private noncomputable def vp1100_1 : Blocks := edgeBlocks% "full/vectors/1100-V-0001.bin"
private noncomputable def vp1100_2 : Blocks := edgeBlocks% "full/vectors/1100-V-0002.bin"
private noncomputable def vp1100_3 : Blocks := edgeBlocks% "full/vectors/1100-V-0003.bin"
private noncomputable def vp1100_4 : Blocks := edgeBlocks% "full/vectors/1100-V-0004.bin"
private noncomputable def vp1100_5 : Blocks := edgeBlocks% "full/vectors/1100-V-0005.bin"
private noncomputable def vp1100_6 : Blocks := edgeBlocks% "full/vectors/1100-V-0006.bin"
private noncomputable def vp1100_7 : Blocks := edgeBlocks% "full/vectors/1100-V-0007.bin"
private noncomputable def vp1100_8 : Blocks := edgeBlocks% "full/vectors/1100-V-0008.bin"
private noncomputable def vp1100_9 : Blocks := edgeBlocks% "full/vectors/1100-V-0009.bin"
private noncomputable def vp1100_10 : Blocks := edgeBlocks% "full/vectors/1100-V-0010.bin"
private noncomputable def vp1100_11 : Blocks := edgeBlocks% "full/vectors/1100-V-0011.bin"
private noncomputable def vp1100_12 : Blocks := edgeBlocks% "full/vectors/1100-V-0012.bin"
private noncomputable def vp1100_13 : Blocks := edgeBlocks% "full/vectors/1100-V-0013.bin"
private noncomputable def vp1100_14 : Blocks := edgeBlocks% "full/vectors/1100-V-0014.bin"
private noncomputable def vp1100_15 : Blocks := edgeBlocks% "full/vectors/1100-V-0015.bin"
private noncomputable def vp1100_16 : Blocks := edgeBlocks% "full/vectors/1100-V-0016.bin"
private noncomputable def vp1100_17 : Blocks := edgeBlocks% "full/vectors/1100-V-0017.bin"
private noncomputable def vp1100_18 : Blocks := edgeBlocks% "full/vectors/1100-V-0018.bin"
private noncomputable def vp1100_19 : Blocks := edgeBlocks% "full/vectors/1100-V-0019.bin"
private noncomputable def vp1100_20 : Blocks := edgeBlocks% "full/vectors/1100-V-0020.bin"
private noncomputable def vp1100_21 : Blocks := edgeBlocks% "full/vectors/1100-V-0021.bin"
private noncomputable def vp1100_22 : Blocks := edgeBlocks% "full/vectors/1100-V-0022.bin"
private noncomputable def vp1100_23 : Blocks := edgeBlocks% "full/vectors/1100-V-0023.bin"
private noncomputable def vp1100_24 : Blocks := edgeBlocks% "full/vectors/1100-V-0024.bin"
private noncomputable def vp1100_25 : Blocks := edgeBlocks% "full/vectors/1100-V-0025.bin"
private noncomputable def vp1100_26 : Blocks := edgeBlocks% "full/vectors/1100-V-0026.bin"
private noncomputable def vp1100_27 : Blocks := edgeBlocks% "full/vectors/1100-V-0027.bin"
private noncomputable def vp1100_28 : Blocks := edgeBlocks% "full/vectors/1100-V-0028.bin"
private noncomputable def vp1100_29 : Blocks := edgeBlocks% "full/vectors/1100-V-0029.bin"
private noncomputable def vp1100_30 : Blocks := edgeBlocks% "full/vectors/1100-V-0030.bin"
private noncomputable def vp1100_31 : Blocks := edgeBlocks% "full/vectors/1100-V-0031.bin"
private noncomputable def vp1100_32 : Blocks := edgeBlocks% "full/vectors/1100-V-0032.bin"
private noncomputable def vp1100_33 : Blocks := edgeBlocks% "full/vectors/1100-V-0033.bin"
private noncomputable def vp1100_34 : Blocks := edgeBlocks% "full/vectors/1100-V-0034.bin"
private noncomputable def vp1100_35 : Blocks := edgeBlocks% "full/vectors/1100-V-0035.bin"
private noncomputable def vp1100_36 : Blocks := edgeBlocks% "full/vectors/1100-V-0036.bin"
private noncomputable def vp1100_37 : Blocks := edgeBlocks% "full/vectors/1100-V-0037.bin"
private noncomputable def vp1100_38 : Blocks := edgeBlocks% "full/vectors/1100-V-0038.bin"
private noncomputable def vp1100_39 : Blocks := edgeBlocks% "full/vectors/1100-V-0039.bin"
private noncomputable def vp1100_40 : Blocks := edgeBlocks% "full/vectors/1100-V-0040.bin"
private noncomputable def vp1100_41 : Blocks := edgeBlocks% "full/vectors/1100-V-0041.bin"
private noncomputable def vp1100_42 : Blocks := edgeBlocks% "full/vectors/1100-V-0042.bin"
private noncomputable def vp1100_43 : Blocks := edgeBlocks% "full/vectors/1100-V-0043.bin"
private noncomputable def vp1100_44 : Blocks := edgeBlocks% "full/vectors/1100-V-0044.bin"
private noncomputable def vp1100_45 : Blocks := edgeBlocks% "full/vectors/1100-V-0045.bin"
noncomputable def vp1100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1100_0 vp1100_1) (Blocks.join vp1100_2 (Blocks.join vp1100_3 vp1100_4))) (Blocks.join (Blocks.join vp1100_5 (Blocks.join vp1100_6 vp1100_7)) (Blocks.join vp1100_8 (Blocks.join vp1100_9 vp1100_10)))) (Blocks.join (Blocks.join (Blocks.join vp1100_11 (Blocks.join vp1100_12 vp1100_13)) (Blocks.join vp1100_14 (Blocks.join vp1100_15 vp1100_16))) (Blocks.join (Blocks.join vp1100_17 (Blocks.join vp1100_18 vp1100_19)) (Blocks.join vp1100_20 (Blocks.join vp1100_21 vp1100_22))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1100_23 vp1100_24) (Blocks.join vp1100_25 (Blocks.join vp1100_26 vp1100_27))) (Blocks.join (Blocks.join vp1100_28 (Blocks.join vp1100_29 vp1100_30)) (Blocks.join vp1100_31 (Blocks.join vp1100_32 vp1100_33)))) (Blocks.join (Blocks.join (Blocks.join vp1100_34 (Blocks.join vp1100_35 vp1100_36)) (Blocks.join vp1100_37 (Blocks.join vp1100_38 vp1100_39))) (Blocks.join (Blocks.join vp1100_40 (Blocks.join vp1100_41 vp1100_42)) (Blocks.join vp1100_43 (Blocks.join vp1100_44 vp1100_45))))))
private theorem bp11000 : Branch 0 (-6143761639/512000000 : ℚ) vp1100 := by
  apply branch_left_normalized (c:=vp11000) (k:=0) (m:=3080) (by decide +kernel)
  rw [show 2*(-6143761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-6143761639/256000000 : ℚ) by norm_num]
  exact coverp11000
private noncomputable def ep11001_0 : Blocks := edgeBlocks% "full/vectors/11001-E-0000.bin"
private noncomputable def ep11001_1 : Blocks := edgeBlocks% "full/vectors/11001-E-0001.bin"
private noncomputable def ep11001_2 : Blocks := edgeBlocks% "full/vectors/11001-E-0002.bin"
private noncomputable def ep11001_3 : Blocks := edgeBlocks% "full/vectors/11001-E-0003.bin"
private noncomputable def ep11001_4 : Blocks := edgeBlocks% "full/vectors/11001-E-0004.bin"
private noncomputable def ep11001_5 : Blocks := edgeBlocks% "full/vectors/11001-E-0005.bin"
private noncomputable def ep11001_6 : Blocks := edgeBlocks% "full/vectors/11001-E-0006.bin"
private noncomputable def ep11001_7 : Blocks := edgeBlocks% "full/vectors/11001-E-0007.bin"
private noncomputable def ep11001_8 : Blocks := edgeBlocks% "full/vectors/11001-E-0008.bin"
private noncomputable def ep11001_9 : Blocks := edgeBlocks% "full/vectors/11001-E-0009.bin"
private noncomputable def ep11001_10 : Blocks := edgeBlocks% "full/vectors/11001-E-0010.bin"
private noncomputable def ep11001_11 : Blocks := edgeBlocks% "full/vectors/11001-E-0011.bin"
private noncomputable def ep11001_12 : Blocks := edgeBlocks% "full/vectors/11001-E-0012.bin"
private noncomputable def ep11001_13 : Blocks := edgeBlocks% "full/vectors/11001-E-0013.bin"
private noncomputable def ep11001_14 : Blocks := edgeBlocks% "full/vectors/11001-E-0014.bin"
private noncomputable def ep11001_15 : Blocks := edgeBlocks% "full/vectors/11001-E-0015.bin"
private noncomputable def ep11001_16 : Blocks := edgeBlocks% "full/vectors/11001-E-0016.bin"
private noncomputable def ep11001_17 : Blocks := edgeBlocks% "full/vectors/11001-E-0017.bin"
private noncomputable def ep11001_18 : Blocks := edgeBlocks% "full/vectors/11001-E-0018.bin"
private noncomputable def ep11001_19 : Blocks := edgeBlocks% "full/vectors/11001-E-0019.bin"
private noncomputable def ep11001_20 : Blocks := edgeBlocks% "full/vectors/11001-E-0020.bin"
private noncomputable def ep11001_21 : Blocks := edgeBlocks% "full/vectors/11001-E-0021.bin"
private noncomputable def ep11001_22 : Blocks := edgeBlocks% "full/vectors/11001-E-0022.bin"
private noncomputable def ep11001_23 : Blocks := edgeBlocks% "full/vectors/11001-E-0023.bin"
private noncomputable def ep11001_24 : Blocks := edgeBlocks% "full/vectors/11001-E-0024.bin"
private noncomputable def ep11001_25 : Blocks := edgeBlocks% "full/vectors/11001-E-0025.bin"
private noncomputable def ep11001_26 : Blocks := edgeBlocks% "full/vectors/11001-E-0026.bin"
private noncomputable def ep11001_27 : Blocks := edgeBlocks% "full/vectors/11001-E-0027.bin"
private noncomputable def ep11001_28 : Blocks := edgeBlocks% "full/vectors/11001-E-0028.bin"
private noncomputable def ep11001_29 : Blocks := edgeBlocks% "full/vectors/11001-E-0029.bin"
private noncomputable def ep11001_30 : Blocks := edgeBlocks% "full/vectors/11001-E-0030.bin"
private noncomputable def ep11001_31 : Blocks := edgeBlocks% "full/vectors/11001-E-0031.bin"
private noncomputable def ep11001_32 : Blocks := edgeBlocks% "full/vectors/11001-E-0032.bin"
private noncomputable def ep11001_33 : Blocks := edgeBlocks% "full/vectors/11001-E-0033.bin"
private noncomputable def ep11001_34 : Blocks := edgeBlocks% "full/vectors/11001-E-0034.bin"
private noncomputable def ep11001_35 : Blocks := edgeBlocks% "full/vectors/11001-E-0035.bin"
private noncomputable def ep11001_36 : Blocks := edgeBlocks% "full/vectors/11001-E-0036.bin"
private noncomputable def ep11001_37 : Blocks := edgeBlocks% "full/vectors/11001-E-0037.bin"
private noncomputable def ep11001_38 : Blocks := edgeBlocks% "full/vectors/11001-E-0038.bin"
private noncomputable def ep11001_39 : Blocks := edgeBlocks% "full/vectors/11001-E-0039.bin"
private noncomputable def ep11001_40 : Blocks := edgeBlocks% "full/vectors/11001-E-0040.bin"
private noncomputable def ep11001_41 : Blocks := edgeBlocks% "full/vectors/11001-E-0041.bin"
private noncomputable def ep11001_42 : Blocks := edgeBlocks% "full/vectors/11001-E-0042.bin"
private noncomputable def ep11001_43 : Blocks := edgeBlocks% "full/vectors/11001-E-0043.bin"
private noncomputable def ep11001_44 : Blocks := edgeBlocks% "full/vectors/11001-E-0044.bin"
private noncomputable def ep11001_45 : Blocks := edgeBlocks% "full/vectors/11001-E-0045.bin"
noncomputable def ep11001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep11001_0 ep11001_1) (Blocks.join ep11001_2 (Blocks.join ep11001_3 ep11001_4))) (Blocks.join (Blocks.join ep11001_5 (Blocks.join ep11001_6 ep11001_7)) (Blocks.join ep11001_8 (Blocks.join ep11001_9 ep11001_10)))) (Blocks.join (Blocks.join (Blocks.join ep11001_11 (Blocks.join ep11001_12 ep11001_13)) (Blocks.join ep11001_14 (Blocks.join ep11001_15 ep11001_16))) (Blocks.join (Blocks.join ep11001_17 (Blocks.join ep11001_18 ep11001_19)) (Blocks.join ep11001_20 (Blocks.join ep11001_21 ep11001_22))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep11001_23 ep11001_24) (Blocks.join ep11001_25 (Blocks.join ep11001_26 ep11001_27))) (Blocks.join (Blocks.join ep11001_28 (Blocks.join ep11001_29 ep11001_30)) (Blocks.join ep11001_31 (Blocks.join ep11001_32 ep11001_33)))) (Blocks.join (Blocks.join (Blocks.join ep11001_34 (Blocks.join ep11001_35 ep11001_36)) (Blocks.join ep11001_37 (Blocks.join ep11001_38 ep11001_39))) (Blocks.join (Blocks.join ep11001_40 (Blocks.join ep11001_41 ep11001_42)) (Blocks.join ep11001_43 (Blocks.join ep11001_44 ep11001_45))))))
private def ptsp11001 : List ℤ := [((2:ℤ)^2058+0),((2:ℤ)^2058+1),((2:ℤ)^2058+2),((2:ℤ)^2058+3),((2:ℤ)^2058+4)]
private theorem boundp11001 : 2^vp1100.size*absSum vp1100.list + ((2:ℤ)^7308*absSum vp11001.list+absSum ep11001.list) < (2:ℤ)^9224 := by decide +kernel
private theorem pointp11001_0 : fastHom 1 ((2:ℤ)^2058+0) vp1100 = ((2:ℤ)^7308)*vp11001.subst ((2:ℤ)^2058+0)+ep11001.subst ((2:ℤ)^2058+0) := by decide +kernel
private theorem pointp11001_1 : fastHom 1 ((2:ℤ)^2058+1) vp1100 = ((2:ℤ)^7308)*vp11001.subst ((2:ℤ)^2058+1)+ep11001.subst ((2:ℤ)^2058+1) := by decide +kernel
private theorem pointp11001_2 : fastHom 1 ((2:ℤ)^2058+2) vp1100 = ((2:ℤ)^7308)*vp11001.subst ((2:ℤ)^2058+2)+ep11001.subst ((2:ℤ)^2058+2) := by decide +kernel
private theorem pointp11001_3 : fastHom 1 ((2:ℤ)^2058+3) vp1100 = ((2:ℤ)^7308)*vp11001.subst ((2:ℤ)^2058+3)+ep11001.subst ((2:ℤ)^2058+3) := by decide +kernel
private theorem pointp11001_4 : fastHom 1 ((2:ℤ)^2058+4) vp1100 = ((2:ℤ)^7308)*vp11001.subst ((2:ℤ)^2058+4)+ep11001.subst ((2:ℤ)^2058+4) := by decide +kernel
private theorem checkp11001 (x:ℤ) (hx:x ∈ ptsp11001) : fastHom 1 x vp1100 = ((2:ℤ)^7308)*vp11001.subst x+ep11001.subst x := by
  simp only [ptsp11001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pointp11001_0
  · exact pointp11001_1
  · exact pointp11001_2
  · exact pointp11001_3
  · exact pointp11001_4
private theorem idp11001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1100.list =
    C ((2:ℤ)^7308) * horner X vp11001.list + horner X ep11001.list := by
  apply edge_identity (B := (2:ℤ)^9224) (by decide) (by positivity) (by positivity) boundp11001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp11001 (by decide +kernel)
  · have h : ptsp11001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp11001.trans_le (by decide +kernel)
  · exact checkp11001
private theorem bp11001 : Branch 1 (-6143761639/512000000 : ℚ) vp1100 := by
  apply branch_checked idp11001 (by positivity) (by decide +kernel)
  rw [show 2*(-6143761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-6399761639/256000000 : ℚ) by norm_num]
  exact coverp11001
theorem coverp1100 : Covers (-6143761639/512000000 : ℚ) vp1100 := join_branches bp11000 bp11001
end NextProof.EdgeFull

