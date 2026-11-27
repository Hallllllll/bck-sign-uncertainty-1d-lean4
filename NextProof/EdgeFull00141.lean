import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp110111111_0 : Blocks := edgeBlocks% "full/vectors/110111111-V-0000.bin"
private noncomputable def vp110111111_1 : Blocks := edgeBlocks% "full/vectors/110111111-V-0001.bin"
noncomputable def vp110111111 : Blocks := (Blocks.join vp110111111_0 vp110111111_1)
theorem coverp110111111 : Covers (-7151761639/16000000 : ℚ) vp110111111 := cover_leaf (by decide +kernel)
private noncomputable def vp110111110_0 : Blocks := edgeBlocks% "full/vectors/110111110-V-0000.bin"
private noncomputable def vp110111110_1 : Blocks := edgeBlocks% "full/vectors/110111110-V-0001.bin"
noncomputable def vp110111110 : Blocks := (Blocks.join vp110111110_0 vp110111110_1)
theorem coverp110111110 : Covers (-7135761639/16000000 : ℚ) vp110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp11011111_0 : Blocks := edgeBlocks% "full/vectors/11011111-V-0000.bin"
private noncomputable def vp11011111_1 : Blocks := edgeBlocks% "full/vectors/11011111-V-0001.bin"
private noncomputable def vp11011111_2 : Blocks := edgeBlocks% "full/vectors/11011111-V-0002.bin"
private noncomputable def vp11011111_3 : Blocks := edgeBlocks% "full/vectors/11011111-V-0003.bin"
noncomputable def vp11011111 : Blocks := (Blocks.join (Blocks.join vp11011111_0 vp11011111_1) (Blocks.join vp11011111_2 vp11011111_3))
private theorem bp110111110 : Branch 0 (-7135761639/32000000 : ℚ) vp11011111 := by
  apply branch_left_normalized (c:=vp110111110) (k:=0) (m:=208) (by decide +kernel)
  rw [show 2*(-7135761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7135761639/16000000 : ℚ) by norm_num]
  exact coverp110111110
private noncomputable def ep110111111_0 : Blocks := edgeBlocks% "full/vectors/110111111-E-0000.bin"
private noncomputable def ep110111111_1 : Blocks := edgeBlocks% "full/vectors/110111111-E-0001.bin"
private noncomputable def ep110111111_2 : Blocks := edgeBlocks% "full/vectors/110111111-E-0002.bin"
private noncomputable def ep110111111_3 : Blocks := edgeBlocks% "full/vectors/110111111-E-0003.bin"
noncomputable def ep110111111 : Blocks := (Blocks.join (Blocks.join ep110111111_0 ep110111111_1) (Blocks.join ep110111111_2 ep110111111_3))
private theorem idp110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11011111.list =
    C ((2:ℤ)^486) * horner X vp110111111.list + horner X ep110111111.list := by
  exact edge_identity (B := (2:ℤ)^694) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110111111 : Branch 1 (-7135761639/32000000 : ℚ) vp11011111 := by
  apply branch_checked idp110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-7135761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7151761639/16000000 : ℚ) by norm_num]
  exact coverp110111111
theorem coverp11011111 : Covers (-7135761639/32000000 : ℚ) vp11011111 := join_branches bp110111110 bp110111111
private noncomputable def vp110111101_0 : Blocks := edgeBlocks% "full/vectors/110111101-V-0000.bin"
private noncomputable def vp110111101_1 : Blocks := edgeBlocks% "full/vectors/110111101-V-0001.bin"
noncomputable def vp110111101 : Blocks := (Blocks.join vp110111101_0 vp110111101_1)
theorem coverp110111101 : Covers (-7119761639/16000000 : ℚ) vp110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp110111100_0 : Blocks := edgeBlocks% "full/vectors/110111100-V-0000.bin"
private noncomputable def vp110111100_1 : Blocks := edgeBlocks% "full/vectors/110111100-V-0001.bin"
noncomputable def vp110111100 : Blocks := (Blocks.join vp110111100_0 vp110111100_1)
theorem coverp110111100 : Covers (-7103761639/16000000 : ℚ) vp110111100 := cover_leaf (by decide +kernel)
private noncomputable def vp11011110_0 : Blocks := edgeBlocks% "full/vectors/11011110-V-0000.bin"
private noncomputable def vp11011110_1 : Blocks := edgeBlocks% "full/vectors/11011110-V-0001.bin"
private noncomputable def vp11011110_2 : Blocks := edgeBlocks% "full/vectors/11011110-V-0002.bin"
private noncomputable def vp11011110_3 : Blocks := edgeBlocks% "full/vectors/11011110-V-0003.bin"
noncomputable def vp11011110 : Blocks := (Blocks.join (Blocks.join vp11011110_0 vp11011110_1) (Blocks.join vp11011110_2 vp11011110_3))
private theorem bp110111100 : Branch 0 (-7103761639/32000000 : ℚ) vp11011110 := by
  apply branch_left_normalized (c:=vp110111100) (k:=0) (m:=210) (by decide +kernel)
  rw [show 2*(-7103761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7103761639/16000000 : ℚ) by norm_num]
  exact coverp110111100
private noncomputable def ep110111101_0 : Blocks := edgeBlocks% "full/vectors/110111101-E-0000.bin"
private noncomputable def ep110111101_1 : Blocks := edgeBlocks% "full/vectors/110111101-E-0001.bin"
private noncomputable def ep110111101_2 : Blocks := edgeBlocks% "full/vectors/110111101-E-0002.bin"
private noncomputable def ep110111101_3 : Blocks := edgeBlocks% "full/vectors/110111101-E-0003.bin"
noncomputable def ep110111101 : Blocks := (Blocks.join (Blocks.join ep110111101_0 ep110111101_1) (Blocks.join ep110111101_2 ep110111101_3))
private theorem idp110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11011110.list =
    C ((2:ℤ)^487) * horner X vp110111101.list + horner X ep110111101.list := by
  exact edge_identity (B := (2:ℤ)^696) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110111101 : Branch 1 (-7103761639/32000000 : ℚ) vp11011110 := by
  apply branch_checked idp110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-7103761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7119761639/16000000 : ℚ) by norm_num]
  exact coverp110111101
theorem coverp11011110 : Covers (-7103761639/32000000 : ℚ) vp11011110 := join_branches bp110111100 bp110111101
private noncomputable def vp1101111_0 : Blocks := edgeBlocks% "full/vectors/1101111-V-0000.bin"
private noncomputable def vp1101111_1 : Blocks := edgeBlocks% "full/vectors/1101111-V-0001.bin"
private noncomputable def vp1101111_2 : Blocks := edgeBlocks% "full/vectors/1101111-V-0002.bin"
private noncomputable def vp1101111_3 : Blocks := edgeBlocks% "full/vectors/1101111-V-0003.bin"
private noncomputable def vp1101111_4 : Blocks := edgeBlocks% "full/vectors/1101111-V-0004.bin"
private noncomputable def vp1101111_5 : Blocks := edgeBlocks% "full/vectors/1101111-V-0005.bin"
noncomputable def vp1101111 : Blocks := (Blocks.join (Blocks.join vp1101111_0 (Blocks.join vp1101111_1 vp1101111_2)) (Blocks.join vp1101111_3 (Blocks.join vp1101111_4 vp1101111_5)))
private theorem bp11011110 : Branch 0 (-7103761639/64000000 : ℚ) vp1101111 := by
  apply branch_left_normalized (c:=vp11011110) (k:=0) (m:=394) (by decide +kernel)
  rw [show 2*(-7103761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7103761639/32000000 : ℚ) by norm_num]
  exact coverp11011110
private noncomputable def ep11011111_0 : Blocks := edgeBlocks% "full/vectors/11011111-E-0000.bin"
private noncomputable def ep11011111_1 : Blocks := edgeBlocks% "full/vectors/11011111-E-0001.bin"
private noncomputable def ep11011111_2 : Blocks := edgeBlocks% "full/vectors/11011111-E-0002.bin"
private noncomputable def ep11011111_3 : Blocks := edgeBlocks% "full/vectors/11011111-E-0003.bin"
private noncomputable def ep11011111_4 : Blocks := edgeBlocks% "full/vectors/11011111-E-0004.bin"
private noncomputable def ep11011111_5 : Blocks := edgeBlocks% "full/vectors/11011111-E-0005.bin"
noncomputable def ep11011111 : Blocks := (Blocks.join (Blocks.join ep11011111_0 (Blocks.join ep11011111_1 ep11011111_2)) (Blocks.join ep11011111_3 (Blocks.join ep11011111_4 ep11011111_5)))
private theorem idp11011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1101111.list =
    C ((2:ℤ)^948) * horner X vp11011111.list + horner X ep11011111.list := by
  exact edge_identity (B := (2:ℤ)^1261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11011111 : Branch 1 (-7103761639/64000000 : ℚ) vp1101111 := by
  apply branch_checked idp11011111 (by positivity) (by decide +kernel)
  rw [show 2*(-7103761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7135761639/32000000 : ℚ) by norm_num]
  exact coverp11011111
theorem coverp1101111 : Covers (-7103761639/64000000 : ℚ) vp1101111 := join_branches bp11011110 bp11011111
private noncomputable def vp110111011_0 : Blocks := edgeBlocks% "full/vectors/110111011-V-0000.bin"
private noncomputable def vp110111011_1 : Blocks := edgeBlocks% "full/vectors/110111011-V-0001.bin"
noncomputable def vp110111011 : Blocks := (Blocks.join vp110111011_0 vp110111011_1)
theorem coverp110111011 : Covers (-7087761639/16000000 : ℚ) vp110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp110111010_0 : Blocks := edgeBlocks% "full/vectors/110111010-V-0000.bin"
private noncomputable def vp110111010_1 : Blocks := edgeBlocks% "full/vectors/110111010-V-0001.bin"
noncomputable def vp110111010 : Blocks := (Blocks.join vp110111010_0 vp110111010_1)
theorem coverp110111010 : Covers (-7071761639/16000000 : ℚ) vp110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp11011101_0 : Blocks := edgeBlocks% "full/vectors/11011101-V-0000.bin"
private noncomputable def vp11011101_1 : Blocks := edgeBlocks% "full/vectors/11011101-V-0001.bin"
private noncomputable def vp11011101_2 : Blocks := edgeBlocks% "full/vectors/11011101-V-0002.bin"
private noncomputable def vp11011101_3 : Blocks := edgeBlocks% "full/vectors/11011101-V-0003.bin"
noncomputable def vp11011101 : Blocks := (Blocks.join (Blocks.join vp11011101_0 vp11011101_1) (Blocks.join vp11011101_2 vp11011101_3))
private theorem bp110111010 : Branch 0 (-7071761639/32000000 : ℚ) vp11011101 := by
  apply branch_left_normalized (c:=vp110111010) (k:=0) (m:=209) (by decide +kernel)
  rw [show 2*(-7071761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7071761639/16000000 : ℚ) by norm_num]
  exact coverp110111010
private noncomputable def ep110111011_0 : Blocks := edgeBlocks% "full/vectors/110111011-E-0000.bin"
private noncomputable def ep110111011_1 : Blocks := edgeBlocks% "full/vectors/110111011-E-0001.bin"
private noncomputable def ep110111011_2 : Blocks := edgeBlocks% "full/vectors/110111011-E-0002.bin"
private noncomputable def ep110111011_3 : Blocks := edgeBlocks% "full/vectors/110111011-E-0003.bin"
noncomputable def ep110111011 : Blocks := (Blocks.join (Blocks.join ep110111011_0 ep110111011_1) (Blocks.join ep110111011_2 ep110111011_3))
private theorem idp110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11011101.list =
    C ((2:ℤ)^490) * horner X vp110111011.list + horner X ep110111011.list := by
  exact edge_identity (B := (2:ℤ)^698) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110111011 : Branch 1 (-7071761639/32000000 : ℚ) vp11011101 := by
  apply branch_checked idp110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-7071761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7087761639/16000000 : ℚ) by norm_num]
  exact coverp110111011
theorem coverp11011101 : Covers (-7071761639/32000000 : ℚ) vp11011101 := join_branches bp110111010 bp110111011
private noncomputable def vp110111001_0 : Blocks := edgeBlocks% "full/vectors/110111001-V-0000.bin"
private noncomputable def vp110111001_1 : Blocks := edgeBlocks% "full/vectors/110111001-V-0001.bin"
noncomputable def vp110111001 : Blocks := (Blocks.join vp110111001_0 vp110111001_1)
theorem coverp110111001 : Covers (-7055761639/16000000 : ℚ) vp110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp110111000_0 : Blocks := edgeBlocks% "full/vectors/110111000-V-0000.bin"
private noncomputable def vp110111000_1 : Blocks := edgeBlocks% "full/vectors/110111000-V-0001.bin"
noncomputable def vp110111000 : Blocks := (Blocks.join vp110111000_0 vp110111000_1)
theorem coverp110111000 : Covers (-7039761639/16000000 : ℚ) vp110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp11011100_0 : Blocks := edgeBlocks% "full/vectors/11011100-V-0000.bin"
private noncomputable def vp11011100_1 : Blocks := edgeBlocks% "full/vectors/11011100-V-0001.bin"
private noncomputable def vp11011100_2 : Blocks := edgeBlocks% "full/vectors/11011100-V-0002.bin"
private noncomputable def vp11011100_3 : Blocks := edgeBlocks% "full/vectors/11011100-V-0003.bin"
noncomputable def vp11011100 : Blocks := (Blocks.join (Blocks.join vp11011100_0 vp11011100_1) (Blocks.join vp11011100_2 vp11011100_3))
private theorem bp110111000 : Branch 0 (-7039761639/32000000 : ℚ) vp11011100 := by
  apply branch_left_normalized (c:=vp110111000) (k:=0) (m:=209) (by decide +kernel)
  rw [show 2*(-7039761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7039761639/16000000 : ℚ) by norm_num]
  exact coverp110111000
private noncomputable def ep110111001_0 : Blocks := edgeBlocks% "full/vectors/110111001-E-0000.bin"
private noncomputable def ep110111001_1 : Blocks := edgeBlocks% "full/vectors/110111001-E-0001.bin"
private noncomputable def ep110111001_2 : Blocks := edgeBlocks% "full/vectors/110111001-E-0002.bin"
private noncomputable def ep110111001_3 : Blocks := edgeBlocks% "full/vectors/110111001-E-0003.bin"
noncomputable def ep110111001 : Blocks := (Blocks.join (Blocks.join ep110111001_0 ep110111001_1) (Blocks.join ep110111001_2 ep110111001_3))
private theorem idp110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11011100.list =
    C ((2:ℤ)^490) * horner X vp110111001.list + horner X ep110111001.list := by
  exact edge_identity (B := (2:ℤ)^699) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110111001 : Branch 1 (-7039761639/32000000 : ℚ) vp11011100 := by
  apply branch_checked idp110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-7039761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7055761639/16000000 : ℚ) by norm_num]
  exact coverp110111001
theorem coverp11011100 : Covers (-7039761639/32000000 : ℚ) vp11011100 := join_branches bp110111000 bp110111001
private noncomputable def vp1101110_0 : Blocks := edgeBlocks% "full/vectors/1101110-V-0000.bin"
private noncomputable def vp1101110_1 : Blocks := edgeBlocks% "full/vectors/1101110-V-0001.bin"
private noncomputable def vp1101110_2 : Blocks := edgeBlocks% "full/vectors/1101110-V-0002.bin"
private noncomputable def vp1101110_3 : Blocks := edgeBlocks% "full/vectors/1101110-V-0003.bin"
private noncomputable def vp1101110_4 : Blocks := edgeBlocks% "full/vectors/1101110-V-0004.bin"
private noncomputable def vp1101110_5 : Blocks := edgeBlocks% "full/vectors/1101110-V-0005.bin"
noncomputable def vp1101110 : Blocks := (Blocks.join (Blocks.join vp1101110_0 (Blocks.join vp1101110_1 vp1101110_2)) (Blocks.join vp1101110_3 (Blocks.join vp1101110_4 vp1101110_5)))
private theorem bp11011100 : Branch 0 (-7039761639/64000000 : ℚ) vp1101110 := by
  apply branch_left_normalized (c:=vp11011100) (k:=0) (m:=397) (by decide +kernel)
  rw [show 2*(-7039761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7039761639/32000000 : ℚ) by norm_num]
  exact coverp11011100
private noncomputable def ep11011101_0 : Blocks := edgeBlocks% "full/vectors/11011101-E-0000.bin"
private noncomputable def ep11011101_1 : Blocks := edgeBlocks% "full/vectors/11011101-E-0001.bin"
private noncomputable def ep11011101_2 : Blocks := edgeBlocks% "full/vectors/11011101-E-0002.bin"
private noncomputable def ep11011101_3 : Blocks := edgeBlocks% "full/vectors/11011101-E-0003.bin"
private noncomputable def ep11011101_4 : Blocks := edgeBlocks% "full/vectors/11011101-E-0004.bin"
private noncomputable def ep11011101_5 : Blocks := edgeBlocks% "full/vectors/11011101-E-0005.bin"
noncomputable def ep11011101 : Blocks := (Blocks.join (Blocks.join ep11011101_0 (Blocks.join ep11011101_1 ep11011101_2)) (Blocks.join ep11011101_3 (Blocks.join ep11011101_4 ep11011101_5)))
private theorem idp11011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1101110.list =
    C ((2:ℤ)^949) * horner X vp11011101.list + horner X ep11011101.list := by
  exact edge_identity (B := (2:ℤ)^1264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11011101 : Branch 1 (-7039761639/64000000 : ℚ) vp1101110 := by
  apply branch_checked idp11011101 (by positivity) (by decide +kernel)
  rw [show 2*(-7039761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7071761639/32000000 : ℚ) by norm_num]
  exact coverp11011101
theorem coverp1101110 : Covers (-7039761639/64000000 : ℚ) vp1101110 := join_branches bp11011100 bp11011101
private noncomputable def vp110111_0 : Blocks := edgeBlocks% "full/vectors/110111-V-0000.bin"
private noncomputable def vp110111_1 : Blocks := edgeBlocks% "full/vectors/110111-V-0001.bin"
private noncomputable def vp110111_2 : Blocks := edgeBlocks% "full/vectors/110111-V-0002.bin"
private noncomputable def vp110111_3 : Blocks := edgeBlocks% "full/vectors/110111-V-0003.bin"
private noncomputable def vp110111_4 : Blocks := edgeBlocks% "full/vectors/110111-V-0004.bin"
private noncomputable def vp110111_5 : Blocks := edgeBlocks% "full/vectors/110111-V-0005.bin"
private noncomputable def vp110111_6 : Blocks := edgeBlocks% "full/vectors/110111-V-0006.bin"
private noncomputable def vp110111_7 : Blocks := edgeBlocks% "full/vectors/110111-V-0007.bin"
private noncomputable def vp110111_8 : Blocks := edgeBlocks% "full/vectors/110111-V-0008.bin"
private noncomputable def vp110111_9 : Blocks := edgeBlocks% "full/vectors/110111-V-0009.bin"
private noncomputable def vp110111_10 : Blocks := edgeBlocks% "full/vectors/110111-V-0010.bin"
private noncomputable def vp110111_11 : Blocks := edgeBlocks% "full/vectors/110111-V-0011.bin"
noncomputable def vp110111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp110111_0 (Blocks.join vp110111_1 vp110111_2)) (Blocks.join vp110111_3 (Blocks.join vp110111_4 vp110111_5))) (Blocks.join (Blocks.join vp110111_6 (Blocks.join vp110111_7 vp110111_8)) (Blocks.join vp110111_9 (Blocks.join vp110111_10 vp110111_11))))
private theorem bp1101110 : Branch 0 (-7039761639/128000000 : ℚ) vp110111 := by
  apply branch_left_normalized (c:=vp1101110) (k:=0) (m:=764) (by decide +kernel)
  rw [show 2*(-7039761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-7039761639/64000000 : ℚ) by norm_num]
  exact coverp1101110
private noncomputable def ep1101111_0 : Blocks := edgeBlocks% "full/vectors/1101111-E-0000.bin"
private noncomputable def ep1101111_1 : Blocks := edgeBlocks% "full/vectors/1101111-E-0001.bin"
private noncomputable def ep1101111_2 : Blocks := edgeBlocks% "full/vectors/1101111-E-0002.bin"
private noncomputable def ep1101111_3 : Blocks := edgeBlocks% "full/vectors/1101111-E-0003.bin"
private noncomputable def ep1101111_4 : Blocks := edgeBlocks% "full/vectors/1101111-E-0004.bin"
private noncomputable def ep1101111_5 : Blocks := edgeBlocks% "full/vectors/1101111-E-0005.bin"
private noncomputable def ep1101111_6 : Blocks := edgeBlocks% "full/vectors/1101111-E-0006.bin"
private noncomputable def ep1101111_7 : Blocks := edgeBlocks% "full/vectors/1101111-E-0007.bin"
private noncomputable def ep1101111_8 : Blocks := edgeBlocks% "full/vectors/1101111-E-0008.bin"
private noncomputable def ep1101111_9 : Blocks := edgeBlocks% "full/vectors/1101111-E-0009.bin"
private noncomputable def ep1101111_10 : Blocks := edgeBlocks% "full/vectors/1101111-E-0010.bin"
private noncomputable def ep1101111_11 : Blocks := edgeBlocks% "full/vectors/1101111-E-0011.bin"
noncomputable def ep1101111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1101111_0 (Blocks.join ep1101111_1 ep1101111_2)) (Blocks.join ep1101111_3 (Blocks.join ep1101111_4 ep1101111_5))) (Blocks.join (Blocks.join ep1101111_6 (Blocks.join ep1101111_7 ep1101111_8)) (Blocks.join ep1101111_9 (Blocks.join ep1101111_10 ep1101111_11))))
private theorem idp1101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110111.list =
    C ((2:ℤ)^1861) * horner X vp1101111.list + horner X ep1101111.list := by
  exact edge_identity (B := (2:ℤ)^2385) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1101111 : Branch 1 (-7039761639/128000000 : ℚ) vp110111 := by
  apply branch_checked idp1101111 (by positivity) (by decide +kernel)
  rw [show 2*(-7039761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-7103761639/64000000 : ℚ) by norm_num]
  exact coverp1101111
theorem coverp110111 : Covers (-7039761639/128000000 : ℚ) vp110111 := join_branches bp1101110 bp1101111
private noncomputable def vp110110111_0 : Blocks := edgeBlocks% "full/vectors/110110111-V-0000.bin"
private noncomputable def vp110110111_1 : Blocks := edgeBlocks% "full/vectors/110110111-V-0001.bin"
noncomputable def vp110110111 : Blocks := (Blocks.join vp110110111_0 vp110110111_1)
theorem coverp110110111 : Covers (-7023761639/16000000 : ℚ) vp110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp110110110_0 : Blocks := edgeBlocks% "full/vectors/110110110-V-0000.bin"
private noncomputable def vp110110110_1 : Blocks := edgeBlocks% "full/vectors/110110110-V-0001.bin"
noncomputable def vp110110110 : Blocks := (Blocks.join vp110110110_0 vp110110110_1)
theorem coverp110110110 : Covers (-7007761639/16000000 : ℚ) vp110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp11011011_0 : Blocks := edgeBlocks% "full/vectors/11011011-V-0000.bin"
private noncomputable def vp11011011_1 : Blocks := edgeBlocks% "full/vectors/11011011-V-0001.bin"
private noncomputable def vp11011011_2 : Blocks := edgeBlocks% "full/vectors/11011011-V-0002.bin"
private noncomputable def vp11011011_3 : Blocks := edgeBlocks% "full/vectors/11011011-V-0003.bin"
noncomputable def vp11011011 : Blocks := (Blocks.join (Blocks.join vp11011011_0 vp11011011_1) (Blocks.join vp11011011_2 vp11011011_3))
private theorem bp110110110 : Branch 0 (-7007761639/32000000 : ℚ) vp11011011 := by
  apply branch_left_normalized (c:=vp110110110) (k:=0) (m:=210) (by decide +kernel)
  rw [show 2*(-7007761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7007761639/16000000 : ℚ) by norm_num]
  exact coverp110110110
private noncomputable def ep110110111_0 : Blocks := edgeBlocks% "full/vectors/110110111-E-0000.bin"
private noncomputable def ep110110111_1 : Blocks := edgeBlocks% "full/vectors/110110111-E-0001.bin"
private noncomputable def ep110110111_2 : Blocks := edgeBlocks% "full/vectors/110110111-E-0002.bin"
private noncomputable def ep110110111_3 : Blocks := edgeBlocks% "full/vectors/110110111-E-0003.bin"
noncomputable def ep110110111 : Blocks := (Blocks.join (Blocks.join ep110110111_0 ep110110111_1) (Blocks.join ep110110111_2 ep110110111_3))
private theorem idp110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11011011.list =
    C ((2:ℤ)^491) * horner X vp110110111.list + horner X ep110110111.list := by
  exact edge_identity (B := (2:ℤ)^701) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110110111 : Branch 1 (-7007761639/32000000 : ℚ) vp11011011 := by
  apply branch_checked idp110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-7007761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7023761639/16000000 : ℚ) by norm_num]
  exact coverp110110111
theorem coverp11011011 : Covers (-7007761639/32000000 : ℚ) vp11011011 := join_branches bp110110110 bp110110111
private noncomputable def vp110110101_0 : Blocks := edgeBlocks% "full/vectors/110110101-V-0000.bin"
private noncomputable def vp110110101_1 : Blocks := edgeBlocks% "full/vectors/110110101-V-0001.bin"
noncomputable def vp110110101 : Blocks := (Blocks.join vp110110101_0 vp110110101_1)
theorem coverp110110101 : Covers (-6991761639/16000000 : ℚ) vp110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp110110100_0 : Blocks := edgeBlocks% "full/vectors/110110100-V-0000.bin"
private noncomputable def vp110110100_1 : Blocks := edgeBlocks% "full/vectors/110110100-V-0001.bin"
noncomputable def vp110110100 : Blocks := (Blocks.join vp110110100_0 vp110110100_1)
theorem coverp110110100 : Covers (-6975761639/16000000 : ℚ) vp110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp11011010_0 : Blocks := edgeBlocks% "full/vectors/11011010-V-0000.bin"
private noncomputable def vp11011010_1 : Blocks := edgeBlocks% "full/vectors/11011010-V-0001.bin"
private noncomputable def vp11011010_2 : Blocks := edgeBlocks% "full/vectors/11011010-V-0002.bin"
private noncomputable def vp11011010_3 : Blocks := edgeBlocks% "full/vectors/11011010-V-0003.bin"
noncomputable def vp11011010 : Blocks := (Blocks.join (Blocks.join vp11011010_0 vp11011010_1) (Blocks.join vp11011010_2 vp11011010_3))
private theorem bp110110100 : Branch 0 (-6975761639/32000000 : ℚ) vp11011010 := by
  apply branch_left_normalized (c:=vp110110100) (k:=0) (m:=211) (by decide +kernel)
  rw [show 2*(-6975761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6975761639/16000000 : ℚ) by norm_num]
  exact coverp110110100
private noncomputable def ep110110101_0 : Blocks := edgeBlocks% "full/vectors/110110101-E-0000.bin"
private noncomputable def ep110110101_1 : Blocks := edgeBlocks% "full/vectors/110110101-E-0001.bin"
private noncomputable def ep110110101_2 : Blocks := edgeBlocks% "full/vectors/110110101-E-0002.bin"
private noncomputable def ep110110101_3 : Blocks := edgeBlocks% "full/vectors/110110101-E-0003.bin"
noncomputable def ep110110101 : Blocks := (Blocks.join (Blocks.join ep110110101_0 ep110110101_1) (Blocks.join ep110110101_2 ep110110101_3))
private theorem idp110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11011010.list =
    C ((2:ℤ)^493) * horner X vp110110101.list + horner X ep110110101.list := by
  exact edge_identity (B := (2:ℤ)^703) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110110101 : Branch 1 (-6975761639/32000000 : ℚ) vp11011010 := by
  apply branch_checked idp110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-6975761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6991761639/16000000 : ℚ) by norm_num]
  exact coverp110110101
theorem coverp11011010 : Covers (-6975761639/32000000 : ℚ) vp11011010 := join_branches bp110110100 bp110110101
private noncomputable def vp1101101_0 : Blocks := edgeBlocks% "full/vectors/1101101-V-0000.bin"
private noncomputable def vp1101101_1 : Blocks := edgeBlocks% "full/vectors/1101101-V-0001.bin"
private noncomputable def vp1101101_2 : Blocks := edgeBlocks% "full/vectors/1101101-V-0002.bin"
private noncomputable def vp1101101_3 : Blocks := edgeBlocks% "full/vectors/1101101-V-0003.bin"
private noncomputable def vp1101101_4 : Blocks := edgeBlocks% "full/vectors/1101101-V-0004.bin"
private noncomputable def vp1101101_5 : Blocks := edgeBlocks% "full/vectors/1101101-V-0005.bin"
private noncomputable def vp1101101_6 : Blocks := edgeBlocks% "full/vectors/1101101-V-0006.bin"
noncomputable def vp1101101 : Blocks := (Blocks.join (Blocks.join vp1101101_0 (Blocks.join vp1101101_1 vp1101101_2)) (Blocks.join (Blocks.join vp1101101_3 vp1101101_4) (Blocks.join vp1101101_5 vp1101101_6)))
private theorem bp11011010 : Branch 0 (-6975761639/64000000 : ℚ) vp1101101 := by
  apply branch_left_normalized (c:=vp11011010) (k:=0) (m:=399) (by decide +kernel)
  rw [show 2*(-6975761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6975761639/32000000 : ℚ) by norm_num]
  exact coverp11011010
private noncomputable def ep11011011_0 : Blocks := edgeBlocks% "full/vectors/11011011-E-0000.bin"
private noncomputable def ep11011011_1 : Blocks := edgeBlocks% "full/vectors/11011011-E-0001.bin"
private noncomputable def ep11011011_2 : Blocks := edgeBlocks% "full/vectors/11011011-E-0002.bin"
private noncomputable def ep11011011_3 : Blocks := edgeBlocks% "full/vectors/11011011-E-0003.bin"
private noncomputable def ep11011011_4 : Blocks := edgeBlocks% "full/vectors/11011011-E-0004.bin"
private noncomputable def ep11011011_5 : Blocks := edgeBlocks% "full/vectors/11011011-E-0005.bin"
private noncomputable def ep11011011_6 : Blocks := edgeBlocks% "full/vectors/11011011-E-0006.bin"
noncomputable def ep11011011 : Blocks := (Blocks.join (Blocks.join ep11011011_0 (Blocks.join ep11011011_1 ep11011011_2)) (Blocks.join (Blocks.join ep11011011_3 ep11011011_4) (Blocks.join ep11011011_5 ep11011011_6)))
private theorem idp11011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1101101.list =
    C ((2:ℤ)^954) * horner X vp11011011.list + horner X ep11011011.list := by
  exact edge_identity (B := (2:ℤ)^1271) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11011011 : Branch 1 (-6975761639/64000000 : ℚ) vp1101101 := by
  apply branch_checked idp11011011 (by positivity) (by decide +kernel)
  rw [show 2*(-6975761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7007761639/32000000 : ℚ) by norm_num]
  exact coverp11011011
theorem coverp1101101 : Covers (-6975761639/64000000 : ℚ) vp1101101 := join_branches bp11011010 bp11011011
private noncomputable def vp110110011_0 : Blocks := edgeBlocks% "full/vectors/110110011-V-0000.bin"
private noncomputable def vp110110011_1 : Blocks := edgeBlocks% "full/vectors/110110011-V-0001.bin"
noncomputable def vp110110011 : Blocks := (Blocks.join vp110110011_0 vp110110011_1)
theorem coverp110110011 : Covers (-6959761639/16000000 : ℚ) vp110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp110110010_0 : Blocks := edgeBlocks% "full/vectors/110110010-V-0000.bin"
private noncomputable def vp110110010_1 : Blocks := edgeBlocks% "full/vectors/110110010-V-0001.bin"
noncomputable def vp110110010 : Blocks := (Blocks.join vp110110010_0 vp110110010_1)
theorem coverp110110010 : Covers (-6943761639/16000000 : ℚ) vp110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp11011001_0 : Blocks := edgeBlocks% "full/vectors/11011001-V-0000.bin"
private noncomputable def vp11011001_1 : Blocks := edgeBlocks% "full/vectors/11011001-V-0001.bin"
private noncomputable def vp11011001_2 : Blocks := edgeBlocks% "full/vectors/11011001-V-0002.bin"
private noncomputable def vp11011001_3 : Blocks := edgeBlocks% "full/vectors/11011001-V-0003.bin"
noncomputable def vp11011001 : Blocks := (Blocks.join (Blocks.join vp11011001_0 vp11011001_1) (Blocks.join vp11011001_2 vp11011001_3))
private theorem bp110110010 : Branch 0 (-6943761639/32000000 : ℚ) vp11011001 := by
  apply branch_left_normalized (c:=vp110110010) (k:=0) (m:=211) (by decide +kernel)
  rw [show 2*(-6943761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6943761639/16000000 : ℚ) by norm_num]
  exact coverp110110010
private noncomputable def ep110110011_0 : Blocks := edgeBlocks% "full/vectors/110110011-E-0000.bin"
private noncomputable def ep110110011_1 : Blocks := edgeBlocks% "full/vectors/110110011-E-0001.bin"
private noncomputable def ep110110011_2 : Blocks := edgeBlocks% "full/vectors/110110011-E-0002.bin"
private noncomputable def ep110110011_3 : Blocks := edgeBlocks% "full/vectors/110110011-E-0003.bin"
noncomputable def ep110110011 : Blocks := (Blocks.join (Blocks.join ep110110011_0 ep110110011_1) (Blocks.join ep110110011_2 ep110110011_3))
private theorem idp110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11011001.list =
    C ((2:ℤ)^491) * horner X vp110110011.list + horner X ep110110011.list := by
  exact edge_identity (B := (2:ℤ)^701) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110110011 : Branch 1 (-6943761639/32000000 : ℚ) vp11011001 := by
  apply branch_checked idp110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-6943761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6959761639/16000000 : ℚ) by norm_num]
  exact coverp110110011
theorem coverp11011001 : Covers (-6943761639/32000000 : ℚ) vp11011001 := join_branches bp110110010 bp110110011
private noncomputable def vp110110001_0 : Blocks := edgeBlocks% "full/vectors/110110001-V-0000.bin"
private noncomputable def vp110110001_1 : Blocks := edgeBlocks% "full/vectors/110110001-V-0001.bin"
noncomputable def vp110110001 : Blocks := (Blocks.join vp110110001_0 vp110110001_1)
theorem coverp110110001 : Covers (-6927761639/16000000 : ℚ) vp110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp110110000_0 : Blocks := edgeBlocks% "full/vectors/110110000-V-0000.bin"
private noncomputable def vp110110000_1 : Blocks := edgeBlocks% "full/vectors/110110000-V-0001.bin"
noncomputable def vp110110000 : Blocks := (Blocks.join vp110110000_0 vp110110000_1)
theorem coverp110110000 : Covers (-6911761639/16000000 : ℚ) vp110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp11011000_0 : Blocks := edgeBlocks% "full/vectors/11011000-V-0000.bin"
private noncomputable def vp11011000_1 : Blocks := edgeBlocks% "full/vectors/11011000-V-0001.bin"
private noncomputable def vp11011000_2 : Blocks := edgeBlocks% "full/vectors/11011000-V-0002.bin"
private noncomputable def vp11011000_3 : Blocks := edgeBlocks% "full/vectors/11011000-V-0003.bin"
noncomputable def vp11011000 : Blocks := (Blocks.join (Blocks.join vp11011000_0 vp11011000_1) (Blocks.join vp11011000_2 vp11011000_3))
private theorem bp110110000 : Branch 0 (-6911761639/32000000 : ℚ) vp11011000 := by
  apply branch_left_normalized (c:=vp110110000) (k:=0) (m:=212) (by decide +kernel)
  rw [show 2*(-6911761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6911761639/16000000 : ℚ) by norm_num]
  exact coverp110110000
private noncomputable def ep110110001_0 : Blocks := edgeBlocks% "full/vectors/110110001-E-0000.bin"
private noncomputable def ep110110001_1 : Blocks := edgeBlocks% "full/vectors/110110001-E-0001.bin"
private noncomputable def ep110110001_2 : Blocks := edgeBlocks% "full/vectors/110110001-E-0002.bin"
private noncomputable def ep110110001_3 : Blocks := edgeBlocks% "full/vectors/110110001-E-0003.bin"
noncomputable def ep110110001 : Blocks := (Blocks.join (Blocks.join ep110110001_0 ep110110001_1) (Blocks.join ep110110001_2 ep110110001_3))
private theorem idp110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11011000.list =
    C ((2:ℤ)^493) * horner X vp110110001.list + horner X ep110110001.list := by
  exact edge_identity (B := (2:ℤ)^704) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110110001 : Branch 1 (-6911761639/32000000 : ℚ) vp11011000 := by
  apply branch_checked idp110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-6911761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6927761639/16000000 : ℚ) by norm_num]
  exact coverp110110001
theorem coverp11011000 : Covers (-6911761639/32000000 : ℚ) vp11011000 := join_branches bp110110000 bp110110001
private noncomputable def vp1101100_0 : Blocks := edgeBlocks% "full/vectors/1101100-V-0000.bin"
private noncomputable def vp1101100_1 : Blocks := edgeBlocks% "full/vectors/1101100-V-0001.bin"
private noncomputable def vp1101100_2 : Blocks := edgeBlocks% "full/vectors/1101100-V-0002.bin"
private noncomputable def vp1101100_3 : Blocks := edgeBlocks% "full/vectors/1101100-V-0003.bin"
private noncomputable def vp1101100_4 : Blocks := edgeBlocks% "full/vectors/1101100-V-0004.bin"
private noncomputable def vp1101100_5 : Blocks := edgeBlocks% "full/vectors/1101100-V-0005.bin"
private noncomputable def vp1101100_6 : Blocks := edgeBlocks% "full/vectors/1101100-V-0006.bin"
noncomputable def vp1101100 : Blocks := (Blocks.join (Blocks.join vp1101100_0 (Blocks.join vp1101100_1 vp1101100_2)) (Blocks.join (Blocks.join vp1101100_3 vp1101100_4) (Blocks.join vp1101100_5 vp1101100_6)))
private theorem bp11011000 : Branch 0 (-6911761639/64000000 : ℚ) vp1101100 := by
  apply branch_left_normalized (c:=vp11011000) (k:=0) (m:=400) (by decide +kernel)
  rw [show 2*(-6911761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6911761639/32000000 : ℚ) by norm_num]
  exact coverp11011000
private noncomputable def ep11011001_0 : Blocks := edgeBlocks% "full/vectors/11011001-E-0000.bin"
private noncomputable def ep11011001_1 : Blocks := edgeBlocks% "full/vectors/11011001-E-0001.bin"
private noncomputable def ep11011001_2 : Blocks := edgeBlocks% "full/vectors/11011001-E-0002.bin"
private noncomputable def ep11011001_3 : Blocks := edgeBlocks% "full/vectors/11011001-E-0003.bin"
private noncomputable def ep11011001_4 : Blocks := edgeBlocks% "full/vectors/11011001-E-0004.bin"
private noncomputable def ep11011001_5 : Blocks := edgeBlocks% "full/vectors/11011001-E-0005.bin"
private noncomputable def ep11011001_6 : Blocks := edgeBlocks% "full/vectors/11011001-E-0006.bin"
noncomputable def ep11011001 : Blocks := (Blocks.join (Blocks.join ep11011001_0 (Blocks.join ep11011001_1 ep11011001_2)) (Blocks.join (Blocks.join ep11011001_3 ep11011001_4) (Blocks.join ep11011001_5 ep11011001_6)))
private theorem idp11011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1101100.list =
    C ((2:ℤ)^958) * horner X vp11011001.list + horner X ep11011001.list := by
  exact edge_identity (B := (2:ℤ)^1276) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11011001 : Branch 1 (-6911761639/64000000 : ℚ) vp1101100 := by
  apply branch_checked idp11011001 (by positivity) (by decide +kernel)
  rw [show 2*(-6911761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6943761639/32000000 : ℚ) by norm_num]
  exact coverp11011001
theorem coverp1101100 : Covers (-6911761639/64000000 : ℚ) vp1101100 := join_branches bp11011000 bp11011001
private noncomputable def vp110110_0 : Blocks := edgeBlocks% "full/vectors/110110-V-0000.bin"
private noncomputable def vp110110_1 : Blocks := edgeBlocks% "full/vectors/110110-V-0001.bin"
private noncomputable def vp110110_2 : Blocks := edgeBlocks% "full/vectors/110110-V-0002.bin"
private noncomputable def vp110110_3 : Blocks := edgeBlocks% "full/vectors/110110-V-0003.bin"
private noncomputable def vp110110_4 : Blocks := edgeBlocks% "full/vectors/110110-V-0004.bin"
private noncomputable def vp110110_5 : Blocks := edgeBlocks% "full/vectors/110110-V-0005.bin"
private noncomputable def vp110110_6 : Blocks := edgeBlocks% "full/vectors/110110-V-0006.bin"
private noncomputable def vp110110_7 : Blocks := edgeBlocks% "full/vectors/110110-V-0007.bin"
private noncomputable def vp110110_8 : Blocks := edgeBlocks% "full/vectors/110110-V-0008.bin"
private noncomputable def vp110110_9 : Blocks := edgeBlocks% "full/vectors/110110-V-0009.bin"
private noncomputable def vp110110_10 : Blocks := edgeBlocks% "full/vectors/110110-V-0010.bin"
private noncomputable def vp110110_11 : Blocks := edgeBlocks% "full/vectors/110110-V-0011.bin"
noncomputable def vp110110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp110110_0 (Blocks.join vp110110_1 vp110110_2)) (Blocks.join vp110110_3 (Blocks.join vp110110_4 vp110110_5))) (Blocks.join (Blocks.join vp110110_6 (Blocks.join vp110110_7 vp110110_8)) (Blocks.join vp110110_9 (Blocks.join vp110110_10 vp110110_11))))
private theorem bp1101100 : Branch 0 (-6911761639/128000000 : ℚ) vp110110 := by
  apply branch_left_normalized (c:=vp1101100) (k:=0) (m:=772) (by decide +kernel)
  rw [show 2*(-6911761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-6911761639/64000000 : ℚ) by norm_num]
  exact coverp1101100
private noncomputable def ep1101101_0 : Blocks := edgeBlocks% "full/vectors/1101101-E-0000.bin"
private noncomputable def ep1101101_1 : Blocks := edgeBlocks% "full/vectors/1101101-E-0001.bin"
private noncomputable def ep1101101_2 : Blocks := edgeBlocks% "full/vectors/1101101-E-0002.bin"
private noncomputable def ep1101101_3 : Blocks := edgeBlocks% "full/vectors/1101101-E-0003.bin"
private noncomputable def ep1101101_4 : Blocks := edgeBlocks% "full/vectors/1101101-E-0004.bin"
private noncomputable def ep1101101_5 : Blocks := edgeBlocks% "full/vectors/1101101-E-0005.bin"
private noncomputable def ep1101101_6 : Blocks := edgeBlocks% "full/vectors/1101101-E-0006.bin"
private noncomputable def ep1101101_7 : Blocks := edgeBlocks% "full/vectors/1101101-E-0007.bin"
private noncomputable def ep1101101_8 : Blocks := edgeBlocks% "full/vectors/1101101-E-0008.bin"
private noncomputable def ep1101101_9 : Blocks := edgeBlocks% "full/vectors/1101101-E-0009.bin"
private noncomputable def ep1101101_10 : Blocks := edgeBlocks% "full/vectors/1101101-E-0010.bin"
private noncomputable def ep1101101_11 : Blocks := edgeBlocks% "full/vectors/1101101-E-0011.bin"
noncomputable def ep1101101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1101101_0 (Blocks.join ep1101101_1 ep1101101_2)) (Blocks.join ep1101101_3 (Blocks.join ep1101101_4 ep1101101_5))) (Blocks.join (Blocks.join ep1101101_6 (Blocks.join ep1101101_7 ep1101101_8)) (Blocks.join ep1101101_9 (Blocks.join ep1101101_10 ep1101101_11))))
private theorem idp1101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110110.list =
    C ((2:ℤ)^1874) * horner X vp1101101.list + horner X ep1101101.list := by
  exact edge_identity (B := (2:ℤ)^2405) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1101101 : Branch 1 (-6911761639/128000000 : ℚ) vp110110 := by
  apply branch_checked idp1101101 (by positivity) (by decide +kernel)
  rw [show 2*(-6911761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-6975761639/64000000 : ℚ) by norm_num]
  exact coverp1101101
theorem coverp110110 : Covers (-6911761639/128000000 : ℚ) vp110110 := join_branches bp1101100 bp1101101
private noncomputable def vp11011_0 : Blocks := edgeBlocks% "full/vectors/11011-V-0000.bin"
private noncomputable def vp11011_1 : Blocks := edgeBlocks% "full/vectors/11011-V-0001.bin"
private noncomputable def vp11011_2 : Blocks := edgeBlocks% "full/vectors/11011-V-0002.bin"
private noncomputable def vp11011_3 : Blocks := edgeBlocks% "full/vectors/11011-V-0003.bin"
private noncomputable def vp11011_4 : Blocks := edgeBlocks% "full/vectors/11011-V-0004.bin"
private noncomputable def vp11011_5 : Blocks := edgeBlocks% "full/vectors/11011-V-0005.bin"
private noncomputable def vp11011_6 : Blocks := edgeBlocks% "full/vectors/11011-V-0006.bin"
private noncomputable def vp11011_7 : Blocks := edgeBlocks% "full/vectors/11011-V-0007.bin"
private noncomputable def vp11011_8 : Blocks := edgeBlocks% "full/vectors/11011-V-0008.bin"
private noncomputable def vp11011_9 : Blocks := edgeBlocks% "full/vectors/11011-V-0009.bin"
private noncomputable def vp11011_10 : Blocks := edgeBlocks% "full/vectors/11011-V-0010.bin"
private noncomputable def vp11011_11 : Blocks := edgeBlocks% "full/vectors/11011-V-0011.bin"
private noncomputable def vp11011_12 : Blocks := edgeBlocks% "full/vectors/11011-V-0012.bin"
private noncomputable def vp11011_13 : Blocks := edgeBlocks% "full/vectors/11011-V-0013.bin"
private noncomputable def vp11011_14 : Blocks := edgeBlocks% "full/vectors/11011-V-0014.bin"
private noncomputable def vp11011_15 : Blocks := edgeBlocks% "full/vectors/11011-V-0015.bin"
private noncomputable def vp11011_16 : Blocks := edgeBlocks% "full/vectors/11011-V-0016.bin"
private noncomputable def vp11011_17 : Blocks := edgeBlocks% "full/vectors/11011-V-0017.bin"
private noncomputable def vp11011_18 : Blocks := edgeBlocks% "full/vectors/11011-V-0018.bin"
private noncomputable def vp11011_19 : Blocks := edgeBlocks% "full/vectors/11011-V-0019.bin"
private noncomputable def vp11011_20 : Blocks := edgeBlocks% "full/vectors/11011-V-0020.bin"
private noncomputable def vp11011_21 : Blocks := edgeBlocks% "full/vectors/11011-V-0021.bin"
private noncomputable def vp11011_22 : Blocks := edgeBlocks% "full/vectors/11011-V-0022.bin"
noncomputable def vp11011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp11011_0 vp11011_1) (Blocks.join vp11011_2 (Blocks.join vp11011_3 vp11011_4))) (Blocks.join (Blocks.join vp11011_5 (Blocks.join vp11011_6 vp11011_7)) (Blocks.join vp11011_8 (Blocks.join vp11011_9 vp11011_10)))) (Blocks.join (Blocks.join (Blocks.join vp11011_11 (Blocks.join vp11011_12 vp11011_13)) (Blocks.join vp11011_14 (Blocks.join vp11011_15 vp11011_16))) (Blocks.join (Blocks.join vp11011_17 (Blocks.join vp11011_18 vp11011_19)) (Blocks.join vp11011_20 (Blocks.join vp11011_21 vp11011_22)))))
private theorem bp110110 : Branch 0 (-6911761639/256000000 : ℚ) vp11011 := by
  apply branch_left_normalized (c:=vp110110) (k:=0) (m:=1504) (by decide +kernel)
  rw [show 2*(-6911761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-6911761639/128000000 : ℚ) by norm_num]
  exact coverp110110
private noncomputable def ep110111_0 : Blocks := edgeBlocks% "full/vectors/110111-E-0000.bin"
private noncomputable def ep110111_1 : Blocks := edgeBlocks% "full/vectors/110111-E-0001.bin"
private noncomputable def ep110111_2 : Blocks := edgeBlocks% "full/vectors/110111-E-0002.bin"
private noncomputable def ep110111_3 : Blocks := edgeBlocks% "full/vectors/110111-E-0003.bin"
private noncomputable def ep110111_4 : Blocks := edgeBlocks% "full/vectors/110111-E-0004.bin"
private noncomputable def ep110111_5 : Blocks := edgeBlocks% "full/vectors/110111-E-0005.bin"
private noncomputable def ep110111_6 : Blocks := edgeBlocks% "full/vectors/110111-E-0006.bin"
private noncomputable def ep110111_7 : Blocks := edgeBlocks% "full/vectors/110111-E-0007.bin"
private noncomputable def ep110111_8 : Blocks := edgeBlocks% "full/vectors/110111-E-0008.bin"
private noncomputable def ep110111_9 : Blocks := edgeBlocks% "full/vectors/110111-E-0009.bin"
private noncomputable def ep110111_10 : Blocks := edgeBlocks% "full/vectors/110111-E-0010.bin"
private noncomputable def ep110111_11 : Blocks := edgeBlocks% "full/vectors/110111-E-0011.bin"
private noncomputable def ep110111_12 : Blocks := edgeBlocks% "full/vectors/110111-E-0012.bin"
private noncomputable def ep110111_13 : Blocks := edgeBlocks% "full/vectors/110111-E-0013.bin"
private noncomputable def ep110111_14 : Blocks := edgeBlocks% "full/vectors/110111-E-0014.bin"
private noncomputable def ep110111_15 : Blocks := edgeBlocks% "full/vectors/110111-E-0015.bin"
private noncomputable def ep110111_16 : Blocks := edgeBlocks% "full/vectors/110111-E-0016.bin"
private noncomputable def ep110111_17 : Blocks := edgeBlocks% "full/vectors/110111-E-0017.bin"
private noncomputable def ep110111_18 : Blocks := edgeBlocks% "full/vectors/110111-E-0018.bin"
private noncomputable def ep110111_19 : Blocks := edgeBlocks% "full/vectors/110111-E-0019.bin"
private noncomputable def ep110111_20 : Blocks := edgeBlocks% "full/vectors/110111-E-0020.bin"
private noncomputable def ep110111_21 : Blocks := edgeBlocks% "full/vectors/110111-E-0021.bin"
private noncomputable def ep110111_22 : Blocks := edgeBlocks% "full/vectors/110111-E-0022.bin"
noncomputable def ep110111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep110111_0 ep110111_1) (Blocks.join ep110111_2 (Blocks.join ep110111_3 ep110111_4))) (Blocks.join (Blocks.join ep110111_5 (Blocks.join ep110111_6 ep110111_7)) (Blocks.join ep110111_8 (Blocks.join ep110111_9 ep110111_10)))) (Blocks.join (Blocks.join (Blocks.join ep110111_11 (Blocks.join ep110111_12 ep110111_13)) (Blocks.join ep110111_14 (Blocks.join ep110111_15 ep110111_16))) (Blocks.join (Blocks.join ep110111_17 (Blocks.join ep110111_18 ep110111_19)) (Blocks.join ep110111_20 (Blocks.join ep110111_21 ep110111_22)))))
private def ptsp110111 : List ℤ := [((2:ℤ)^4116+0),((2:ℤ)^4116+1)]
private theorem boundp110111 : 2^vp11011.size*absSum vp11011.list + ((2:ℤ)^3654*absSum vp110111.list+absSum ep110111.list) < (2:ℤ)^4599 := by decide +kernel
private theorem pointp110111_0 : fastHom 1 ((2:ℤ)^4116+0) vp11011 = ((2:ℤ)^3654)*vp110111.subst ((2:ℤ)^4116+0)+ep110111.subst ((2:ℤ)^4116+0) := by decide +kernel
private theorem pointp110111_1 : fastHom 1 ((2:ℤ)^4116+1) vp11011 = ((2:ℤ)^3654)*vp110111.subst ((2:ℤ)^4116+1)+ep110111.subst ((2:ℤ)^4116+1) := by decide +kernel
private theorem checkp110111 (x:ℤ) (hx:x ∈ ptsp110111) : fastHom 1 x vp11011 = ((2:ℤ)^3654)*vp110111.subst x+ep110111.subst x := by
  simp only [ptsp110111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp110111_0
  · exact pointp110111_1
private theorem idp110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11011.list =
    C ((2:ℤ)^3654) * horner X vp110111.list + horner X ep110111.list := by
  apply edge_identity (B := (2:ℤ)^4599) (by decide) (by positivity) (by positivity) boundp110111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp110111 (by decide +kernel)
  · have h : ptsp110111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp110111.trans_le (by decide +kernel)
  · exact checkp110111
private theorem bp110111 : Branch 1 (-6911761639/256000000 : ℚ) vp11011 := by
  apply branch_checked idp110111 (by positivity) (by decide +kernel)
  rw [show 2*(-6911761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-7039761639/128000000 : ℚ) by norm_num]
  exact coverp110111
theorem coverp11011 : Covers (-6911761639/256000000 : ℚ) vp11011 := join_branches bp110110 bp110111
private noncomputable def vp110101111_0 : Blocks := edgeBlocks% "full/vectors/110101111-V-0000.bin"
private noncomputable def vp110101111_1 : Blocks := edgeBlocks% "full/vectors/110101111-V-0001.bin"
noncomputable def vp110101111 : Blocks := (Blocks.join vp110101111_0 vp110101111_1)
theorem coverp110101111 : Covers (-6895761639/16000000 : ℚ) vp110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp110101110_0 : Blocks := edgeBlocks% "full/vectors/110101110-V-0000.bin"
private noncomputable def vp110101110_1 : Blocks := edgeBlocks% "full/vectors/110101110-V-0001.bin"
noncomputable def vp110101110 : Blocks := (Blocks.join vp110101110_0 vp110101110_1)
theorem coverp110101110 : Covers (-6879761639/16000000 : ℚ) vp110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp11010111_0 : Blocks := edgeBlocks% "full/vectors/11010111-V-0000.bin"
private noncomputable def vp11010111_1 : Blocks := edgeBlocks% "full/vectors/11010111-V-0001.bin"
private noncomputable def vp11010111_2 : Blocks := edgeBlocks% "full/vectors/11010111-V-0002.bin"
private noncomputable def vp11010111_3 : Blocks := edgeBlocks% "full/vectors/11010111-V-0003.bin"
noncomputable def vp11010111 : Blocks := (Blocks.join (Blocks.join vp11010111_0 vp11010111_1) (Blocks.join vp11010111_2 vp11010111_3))
private theorem bp110101110 : Branch 0 (-6879761639/32000000 : ℚ) vp11010111 := by
  apply branch_left_normalized (c:=vp110101110) (k:=0) (m:=213) (by decide +kernel)
  rw [show 2*(-6879761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6879761639/16000000 : ℚ) by norm_num]
  exact coverp110101110
private noncomputable def ep110101111_0 : Blocks := edgeBlocks% "full/vectors/110101111-E-0000.bin"
private noncomputable def ep110101111_1 : Blocks := edgeBlocks% "full/vectors/110101111-E-0001.bin"
private noncomputable def ep110101111_2 : Blocks := edgeBlocks% "full/vectors/110101111-E-0002.bin"
private noncomputable def ep110101111_3 : Blocks := edgeBlocks% "full/vectors/110101111-E-0003.bin"
noncomputable def ep110101111 : Blocks := (Blocks.join (Blocks.join ep110101111_0 ep110101111_1) (Blocks.join ep110101111_2 ep110101111_3))
private theorem idp110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11010111.list =
    C ((2:ℤ)^495) * horner X vp110101111.list + horner X ep110101111.list := by
  exact edge_identity (B := (2:ℤ)^706) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110101111 : Branch 1 (-6879761639/32000000 : ℚ) vp11010111 := by
  apply branch_checked idp110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-6879761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6895761639/16000000 : ℚ) by norm_num]
  exact coverp110101111
theorem coverp11010111 : Covers (-6879761639/32000000 : ℚ) vp11010111 := join_branches bp110101110 bp110101111
private noncomputable def vp110101101_0 : Blocks := edgeBlocks% "full/vectors/110101101-V-0000.bin"
private noncomputable def vp110101101_1 : Blocks := edgeBlocks% "full/vectors/110101101-V-0001.bin"
noncomputable def vp110101101 : Blocks := (Blocks.join vp110101101_0 vp110101101_1)
theorem coverp110101101 : Covers (-6863761639/16000000 : ℚ) vp110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp110101100_0 : Blocks := edgeBlocks% "full/vectors/110101100-V-0000.bin"
private noncomputable def vp110101100_1 : Blocks := edgeBlocks% "full/vectors/110101100-V-0001.bin"
noncomputable def vp110101100 : Blocks := (Blocks.join vp110101100_0 vp110101100_1)
theorem coverp110101100 : Covers (-6847761639/16000000 : ℚ) vp110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp11010110_0 : Blocks := edgeBlocks% "full/vectors/11010110-V-0000.bin"
private noncomputable def vp11010110_1 : Blocks := edgeBlocks% "full/vectors/11010110-V-0001.bin"
private noncomputable def vp11010110_2 : Blocks := edgeBlocks% "full/vectors/11010110-V-0002.bin"
private noncomputable def vp11010110_3 : Blocks := edgeBlocks% "full/vectors/11010110-V-0003.bin"
noncomputable def vp11010110 : Blocks := (Blocks.join (Blocks.join vp11010110_0 vp11010110_1) (Blocks.join vp11010110_2 vp11010110_3))
private theorem bp110101100 : Branch 0 (-6847761639/32000000 : ℚ) vp11010110 := by
  apply branch_left_normalized (c:=vp110101100) (k:=0) (m:=212) (by decide +kernel)
  rw [show 2*(-6847761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6847761639/16000000 : ℚ) by norm_num]
  exact coverp110101100
private noncomputable def ep110101101_0 : Blocks := edgeBlocks% "full/vectors/110101101-E-0000.bin"
private noncomputable def ep110101101_1 : Blocks := edgeBlocks% "full/vectors/110101101-E-0001.bin"
private noncomputable def ep110101101_2 : Blocks := edgeBlocks% "full/vectors/110101101-E-0002.bin"
private noncomputable def ep110101101_3 : Blocks := edgeBlocks% "full/vectors/110101101-E-0003.bin"
noncomputable def ep110101101 : Blocks := (Blocks.join (Blocks.join ep110101101_0 ep110101101_1) (Blocks.join ep110101101_2 ep110101101_3))
private theorem idp110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11010110.list =
    C ((2:ℤ)^495) * horner X vp110101101.list + horner X ep110101101.list := by
  exact edge_identity (B := (2:ℤ)^707) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110101101 : Branch 1 (-6847761639/32000000 : ℚ) vp11010110 := by
  apply branch_checked idp110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-6847761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6863761639/16000000 : ℚ) by norm_num]
  exact coverp110101101
theorem coverp11010110 : Covers (-6847761639/32000000 : ℚ) vp11010110 := join_branches bp110101100 bp110101101
private noncomputable def vp1101011_0 : Blocks := edgeBlocks% "full/vectors/1101011-V-0000.bin"
private noncomputable def vp1101011_1 : Blocks := edgeBlocks% "full/vectors/1101011-V-0001.bin"
private noncomputable def vp1101011_2 : Blocks := edgeBlocks% "full/vectors/1101011-V-0002.bin"
private noncomputable def vp1101011_3 : Blocks := edgeBlocks% "full/vectors/1101011-V-0003.bin"
private noncomputable def vp1101011_4 : Blocks := edgeBlocks% "full/vectors/1101011-V-0004.bin"
private noncomputable def vp1101011_5 : Blocks := edgeBlocks% "full/vectors/1101011-V-0005.bin"
private noncomputable def vp1101011_6 : Blocks := edgeBlocks% "full/vectors/1101011-V-0006.bin"
noncomputable def vp1101011 : Blocks := (Blocks.join (Blocks.join vp1101011_0 (Blocks.join vp1101011_1 vp1101011_2)) (Blocks.join (Blocks.join vp1101011_3 vp1101011_4) (Blocks.join vp1101011_5 vp1101011_6)))
private theorem bp11010110 : Branch 0 (-6847761639/64000000 : ℚ) vp1101011 := by
  apply branch_left_normalized (c:=vp11010110) (k:=0) (m:=402) (by decide +kernel)
  rw [show 2*(-6847761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6847761639/32000000 : ℚ) by norm_num]
  exact coverp11010110
private noncomputable def ep11010111_0 : Blocks := edgeBlocks% "full/vectors/11010111-E-0000.bin"
private noncomputable def ep11010111_1 : Blocks := edgeBlocks% "full/vectors/11010111-E-0001.bin"
private noncomputable def ep11010111_2 : Blocks := edgeBlocks% "full/vectors/11010111-E-0002.bin"
private noncomputable def ep11010111_3 : Blocks := edgeBlocks% "full/vectors/11010111-E-0003.bin"
private noncomputable def ep11010111_4 : Blocks := edgeBlocks% "full/vectors/11010111-E-0004.bin"
private noncomputable def ep11010111_5 : Blocks := edgeBlocks% "full/vectors/11010111-E-0005.bin"
private noncomputable def ep11010111_6 : Blocks := edgeBlocks% "full/vectors/11010111-E-0006.bin"
noncomputable def ep11010111 : Blocks := (Blocks.join (Blocks.join ep11010111_0 (Blocks.join ep11010111_1 ep11010111_2)) (Blocks.join (Blocks.join ep11010111_3 ep11010111_4) (Blocks.join ep11010111_5 ep11010111_6)))
private theorem idp11010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1101011.list =
    C ((2:ℤ)^960) * horner X vp11010111.list + horner X ep11010111.list := by
  exact edge_identity (B := (2:ℤ)^1280) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11010111 : Branch 1 (-6847761639/64000000 : ℚ) vp1101011 := by
  apply branch_checked idp11010111 (by positivity) (by decide +kernel)
  rw [show 2*(-6847761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6879761639/32000000 : ℚ) by norm_num]
  exact coverp11010111
theorem coverp1101011 : Covers (-6847761639/64000000 : ℚ) vp1101011 := join_branches bp11010110 bp11010111
private noncomputable def vp110101011_0 : Blocks := edgeBlocks% "full/vectors/110101011-V-0000.bin"
private noncomputable def vp110101011_1 : Blocks := edgeBlocks% "full/vectors/110101011-V-0001.bin"
noncomputable def vp110101011 : Blocks := (Blocks.join vp110101011_0 vp110101011_1)
theorem coverp110101011 : Covers (-6831761639/16000000 : ℚ) vp110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp110101010_0 : Blocks := edgeBlocks% "full/vectors/110101010-V-0000.bin"
private noncomputable def vp110101010_1 : Blocks := edgeBlocks% "full/vectors/110101010-V-0001.bin"
noncomputable def vp110101010 : Blocks := (Blocks.join vp110101010_0 vp110101010_1)
theorem coverp110101010 : Covers (-6815761639/16000000 : ℚ) vp110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp11010101_0 : Blocks := edgeBlocks% "full/vectors/11010101-V-0000.bin"
private noncomputable def vp11010101_1 : Blocks := edgeBlocks% "full/vectors/11010101-V-0001.bin"
private noncomputable def vp11010101_2 : Blocks := edgeBlocks% "full/vectors/11010101-V-0002.bin"
private noncomputable def vp11010101_3 : Blocks := edgeBlocks% "full/vectors/11010101-V-0003.bin"
noncomputable def vp11010101 : Blocks := (Blocks.join (Blocks.join vp11010101_0 vp11010101_1) (Blocks.join vp11010101_2 vp11010101_3))
private theorem bp110101010 : Branch 0 (-6815761639/32000000 : ℚ) vp11010101 := by
  apply branch_left_normalized (c:=vp110101010) (k:=0) (m:=213) (by decide +kernel)
  rw [show 2*(-6815761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6815761639/16000000 : ℚ) by norm_num]
  exact coverp110101010
private noncomputable def ep110101011_0 : Blocks := edgeBlocks% "full/vectors/110101011-E-0000.bin"
private noncomputable def ep110101011_1 : Blocks := edgeBlocks% "full/vectors/110101011-E-0001.bin"
private noncomputable def ep110101011_2 : Blocks := edgeBlocks% "full/vectors/110101011-E-0002.bin"
private noncomputable def ep110101011_3 : Blocks := edgeBlocks% "full/vectors/110101011-E-0003.bin"
noncomputable def ep110101011 : Blocks := (Blocks.join (Blocks.join ep110101011_0 ep110101011_1) (Blocks.join ep110101011_2 ep110101011_3))
private theorem idp110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11010101.list =
    C ((2:ℤ)^494) * horner X vp110101011.list + horner X ep110101011.list := by
  exact edge_identity (B := (2:ℤ)^707) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110101011 : Branch 1 (-6815761639/32000000 : ℚ) vp11010101 := by
  apply branch_checked idp110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-6815761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6831761639/16000000 : ℚ) by norm_num]
  exact coverp110101011
theorem coverp11010101 : Covers (-6815761639/32000000 : ℚ) vp11010101 := join_branches bp110101010 bp110101011
private noncomputable def vp110101001_0 : Blocks := edgeBlocks% "full/vectors/110101001-V-0000.bin"
private noncomputable def vp110101001_1 : Blocks := edgeBlocks% "full/vectors/110101001-V-0001.bin"
noncomputable def vp110101001 : Blocks := (Blocks.join vp110101001_0 vp110101001_1)
theorem coverp110101001 : Covers (-6799761639/16000000 : ℚ) vp110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp110101000_0 : Blocks := edgeBlocks% "full/vectors/110101000-V-0000.bin"
private noncomputable def vp110101000_1 : Blocks := edgeBlocks% "full/vectors/110101000-V-0001.bin"
noncomputable def vp110101000 : Blocks := (Blocks.join vp110101000_0 vp110101000_1)
theorem coverp110101000 : Covers (-6783761639/16000000 : ℚ) vp110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp11010100_0 : Blocks := edgeBlocks% "full/vectors/11010100-V-0000.bin"
private noncomputable def vp11010100_1 : Blocks := edgeBlocks% "full/vectors/11010100-V-0001.bin"
private noncomputable def vp11010100_2 : Blocks := edgeBlocks% "full/vectors/11010100-V-0002.bin"
private noncomputable def vp11010100_3 : Blocks := edgeBlocks% "full/vectors/11010100-V-0003.bin"
noncomputable def vp11010100 : Blocks := (Blocks.join (Blocks.join vp11010100_0 vp11010100_1) (Blocks.join vp11010100_2 vp11010100_3))
private theorem bp110101000 : Branch 0 (-6783761639/32000000 : ℚ) vp11010100 := by
  apply branch_left_normalized (c:=vp110101000) (k:=0) (m:=213) (by decide +kernel)
  rw [show 2*(-6783761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6783761639/16000000 : ℚ) by norm_num]
  exact coverp110101000
private noncomputable def ep110101001_0 : Blocks := edgeBlocks% "full/vectors/110101001-E-0000.bin"
private noncomputable def ep110101001_1 : Blocks := edgeBlocks% "full/vectors/110101001-E-0001.bin"
private noncomputable def ep110101001_2 : Blocks := edgeBlocks% "full/vectors/110101001-E-0002.bin"
private noncomputable def ep110101001_3 : Blocks := edgeBlocks% "full/vectors/110101001-E-0003.bin"
noncomputable def ep110101001 : Blocks := (Blocks.join (Blocks.join ep110101001_0 ep110101001_1) (Blocks.join ep110101001_2 ep110101001_3))
private theorem idp110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11010100.list =
    C ((2:ℤ)^498) * horner X vp110101001.list + horner X ep110101001.list := by
  exact edge_identity (B := (2:ℤ)^710) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110101001 : Branch 1 (-6783761639/32000000 : ℚ) vp11010100 := by
  apply branch_checked idp110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-6783761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6799761639/16000000 : ℚ) by norm_num]
  exact coverp110101001
theorem coverp11010100 : Covers (-6783761639/32000000 : ℚ) vp11010100 := join_branches bp110101000 bp110101001
private noncomputable def vp1101010_0 : Blocks := edgeBlocks% "full/vectors/1101010-V-0000.bin"
private noncomputable def vp1101010_1 : Blocks := edgeBlocks% "full/vectors/1101010-V-0001.bin"
private noncomputable def vp1101010_2 : Blocks := edgeBlocks% "full/vectors/1101010-V-0002.bin"
private noncomputable def vp1101010_3 : Blocks := edgeBlocks% "full/vectors/1101010-V-0003.bin"
private noncomputable def vp1101010_4 : Blocks := edgeBlocks% "full/vectors/1101010-V-0004.bin"
private noncomputable def vp1101010_5 : Blocks := edgeBlocks% "full/vectors/1101010-V-0005.bin"
private noncomputable def vp1101010_6 : Blocks := edgeBlocks% "full/vectors/1101010-V-0006.bin"
noncomputable def vp1101010 : Blocks := (Blocks.join (Blocks.join vp1101010_0 (Blocks.join vp1101010_1 vp1101010_2)) (Blocks.join (Blocks.join vp1101010_3 vp1101010_4) (Blocks.join vp1101010_5 vp1101010_6)))
private theorem bp11010100 : Branch 0 (-6783761639/64000000 : ℚ) vp1101010 := by
  apply branch_left_normalized (c:=vp11010100) (k:=0) (m:=404) (by decide +kernel)
  rw [show 2*(-6783761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6783761639/32000000 : ℚ) by norm_num]
  exact coverp11010100
private noncomputable def ep11010101_0 : Blocks := edgeBlocks% "full/vectors/11010101-E-0000.bin"
private noncomputable def ep11010101_1 : Blocks := edgeBlocks% "full/vectors/11010101-E-0001.bin"
private noncomputable def ep11010101_2 : Blocks := edgeBlocks% "full/vectors/11010101-E-0002.bin"
private noncomputable def ep11010101_3 : Blocks := edgeBlocks% "full/vectors/11010101-E-0003.bin"
private noncomputable def ep11010101_4 : Blocks := edgeBlocks% "full/vectors/11010101-E-0004.bin"
private noncomputable def ep11010101_5 : Blocks := edgeBlocks% "full/vectors/11010101-E-0005.bin"
private noncomputable def ep11010101_6 : Blocks := edgeBlocks% "full/vectors/11010101-E-0006.bin"
noncomputable def ep11010101 : Blocks := (Blocks.join (Blocks.join ep11010101_0 (Blocks.join ep11010101_1 ep11010101_2)) (Blocks.join (Blocks.join ep11010101_3 ep11010101_4) (Blocks.join ep11010101_5 ep11010101_6)))
private theorem idp11010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1101010.list =
    C ((2:ℤ)^965) * horner X vp11010101.list + horner X ep11010101.list := by
  exact edge_identity (B := (2:ℤ)^1287) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11010101 : Branch 1 (-6783761639/64000000 : ℚ) vp1101010 := by
  apply branch_checked idp11010101 (by positivity) (by decide +kernel)
  rw [show 2*(-6783761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6815761639/32000000 : ℚ) by norm_num]
  exact coverp11010101
theorem coverp1101010 : Covers (-6783761639/64000000 : ℚ) vp1101010 := join_branches bp11010100 bp11010101
private noncomputable def vp110101_0 : Blocks := edgeBlocks% "full/vectors/110101-V-0000.bin"
private noncomputable def vp110101_1 : Blocks := edgeBlocks% "full/vectors/110101-V-0001.bin"
private noncomputable def vp110101_2 : Blocks := edgeBlocks% "full/vectors/110101-V-0002.bin"
private noncomputable def vp110101_3 : Blocks := edgeBlocks% "full/vectors/110101-V-0003.bin"
private noncomputable def vp110101_4 : Blocks := edgeBlocks% "full/vectors/110101-V-0004.bin"
private noncomputable def vp110101_5 : Blocks := edgeBlocks% "full/vectors/110101-V-0005.bin"
private noncomputable def vp110101_6 : Blocks := edgeBlocks% "full/vectors/110101-V-0006.bin"
private noncomputable def vp110101_7 : Blocks := edgeBlocks% "full/vectors/110101-V-0007.bin"
private noncomputable def vp110101_8 : Blocks := edgeBlocks% "full/vectors/110101-V-0008.bin"
private noncomputable def vp110101_9 : Blocks := edgeBlocks% "full/vectors/110101-V-0009.bin"
private noncomputable def vp110101_10 : Blocks := edgeBlocks% "full/vectors/110101-V-0010.bin"
private noncomputable def vp110101_11 : Blocks := edgeBlocks% "full/vectors/110101-V-0011.bin"
noncomputable def vp110101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp110101_0 (Blocks.join vp110101_1 vp110101_2)) (Blocks.join vp110101_3 (Blocks.join vp110101_4 vp110101_5))) (Blocks.join (Blocks.join vp110101_6 (Blocks.join vp110101_7 vp110101_8)) (Blocks.join vp110101_9 (Blocks.join vp110101_10 vp110101_11))))
private theorem bp1101010 : Branch 0 (-6783761639/128000000 : ℚ) vp110101 := by
  apply branch_left_normalized (c:=vp1101010) (k:=0) (m:=779) (by decide +kernel)
  rw [show 2*(-6783761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-6783761639/64000000 : ℚ) by norm_num]
  exact coverp1101010
private noncomputable def ep1101011_0 : Blocks := edgeBlocks% "full/vectors/1101011-E-0000.bin"
private noncomputable def ep1101011_1 : Blocks := edgeBlocks% "full/vectors/1101011-E-0001.bin"
private noncomputable def ep1101011_2 : Blocks := edgeBlocks% "full/vectors/1101011-E-0002.bin"
private noncomputable def ep1101011_3 : Blocks := edgeBlocks% "full/vectors/1101011-E-0003.bin"
private noncomputable def ep1101011_4 : Blocks := edgeBlocks% "full/vectors/1101011-E-0004.bin"
private noncomputable def ep1101011_5 : Blocks := edgeBlocks% "full/vectors/1101011-E-0005.bin"
private noncomputable def ep1101011_6 : Blocks := edgeBlocks% "full/vectors/1101011-E-0006.bin"
private noncomputable def ep1101011_7 : Blocks := edgeBlocks% "full/vectors/1101011-E-0007.bin"
private noncomputable def ep1101011_8 : Blocks := edgeBlocks% "full/vectors/1101011-E-0008.bin"
private noncomputable def ep1101011_9 : Blocks := edgeBlocks% "full/vectors/1101011-E-0009.bin"
private noncomputable def ep1101011_10 : Blocks := edgeBlocks% "full/vectors/1101011-E-0010.bin"
private noncomputable def ep1101011_11 : Blocks := edgeBlocks% "full/vectors/1101011-E-0011.bin"
noncomputable def ep1101011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1101011_0 (Blocks.join ep1101011_1 ep1101011_2)) (Blocks.join ep1101011_3 (Blocks.join ep1101011_4 ep1101011_5))) (Blocks.join (Blocks.join ep1101011_6 (Blocks.join ep1101011_7 ep1101011_8)) (Blocks.join ep1101011_9 (Blocks.join ep1101011_10 ep1101011_11))))
private theorem idp1101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110101.list =
    C ((2:ℤ)^1887) * horner X vp1101011.list + horner X ep1101011.list := by
  exact edge_identity (B := (2:ℤ)^2425) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1101011 : Branch 1 (-6783761639/128000000 : ℚ) vp110101 := by
  apply branch_checked idp1101011 (by positivity) (by decide +kernel)
  rw [show 2*(-6783761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-6847761639/64000000 : ℚ) by norm_num]
  exact coverp1101011
theorem coverp110101 : Covers (-6783761639/128000000 : ℚ) vp110101 := join_branches bp1101010 bp1101011
private noncomputable def vp110100111_0 : Blocks := edgeBlocks% "full/vectors/110100111-V-0000.bin"
private noncomputable def vp110100111_1 : Blocks := edgeBlocks% "full/vectors/110100111-V-0001.bin"
noncomputable def vp110100111 : Blocks := (Blocks.join vp110100111_0 vp110100111_1)
theorem coverp110100111 : Covers (-6767761639/16000000 : ℚ) vp110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp110100110_0 : Blocks := edgeBlocks% "full/vectors/110100110-V-0000.bin"
private noncomputable def vp110100110_1 : Blocks := edgeBlocks% "full/vectors/110100110-V-0001.bin"
noncomputable def vp110100110 : Blocks := (Blocks.join vp110100110_0 vp110100110_1)
theorem coverp110100110 : Covers (-6751761639/16000000 : ℚ) vp110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp11010011_0 : Blocks := edgeBlocks% "full/vectors/11010011-V-0000.bin"
private noncomputable def vp11010011_1 : Blocks := edgeBlocks% "full/vectors/11010011-V-0001.bin"
private noncomputable def vp11010011_2 : Blocks := edgeBlocks% "full/vectors/11010011-V-0002.bin"
private noncomputable def vp11010011_3 : Blocks := edgeBlocks% "full/vectors/11010011-V-0003.bin"
noncomputable def vp11010011 : Blocks := (Blocks.join (Blocks.join vp11010011_0 vp11010011_1) (Blocks.join vp11010011_2 vp11010011_3))
private theorem bp110100110 : Branch 0 (-6751761639/32000000 : ℚ) vp11010011 := by
  apply branch_left_normalized (c:=vp110100110) (k:=0) (m:=214) (by decide +kernel)
  rw [show 2*(-6751761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6751761639/16000000 : ℚ) by norm_num]
  exact coverp110100110
private noncomputable def ep110100111_0 : Blocks := edgeBlocks% "full/vectors/110100111-E-0000.bin"
private noncomputable def ep110100111_1 : Blocks := edgeBlocks% "full/vectors/110100111-E-0001.bin"
private noncomputable def ep110100111_2 : Blocks := edgeBlocks% "full/vectors/110100111-E-0002.bin"
private noncomputable def ep110100111_3 : Blocks := edgeBlocks% "full/vectors/110100111-E-0003.bin"
noncomputable def ep110100111 : Blocks := (Blocks.join (Blocks.join ep110100111_0 ep110100111_1) (Blocks.join ep110100111_2 ep110100111_3))
private theorem idp110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11010011.list =
    C ((2:ℤ)^497) * horner X vp110100111.list + horner X ep110100111.list := by
  exact edge_identity (B := (2:ℤ)^710) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110100111 : Branch 1 (-6751761639/32000000 : ℚ) vp11010011 := by
  apply branch_checked idp110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-6751761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6767761639/16000000 : ℚ) by norm_num]
  exact coverp110100111
theorem coverp11010011 : Covers (-6751761639/32000000 : ℚ) vp11010011 := join_branches bp110100110 bp110100111
private noncomputable def vp110100101_0 : Blocks := edgeBlocks% "full/vectors/110100101-V-0000.bin"
private noncomputable def vp110100101_1 : Blocks := edgeBlocks% "full/vectors/110100101-V-0001.bin"
noncomputable def vp110100101 : Blocks := (Blocks.join vp110100101_0 vp110100101_1)
theorem coverp110100101 : Covers (-6735761639/16000000 : ℚ) vp110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp110100100_0 : Blocks := edgeBlocks% "full/vectors/110100100-V-0000.bin"
private noncomputable def vp110100100_1 : Blocks := edgeBlocks% "full/vectors/110100100-V-0001.bin"
noncomputable def vp110100100 : Blocks := (Blocks.join vp110100100_0 vp110100100_1)
theorem coverp110100100 : Covers (-6719761639/16000000 : ℚ) vp110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp11010010_0 : Blocks := edgeBlocks% "full/vectors/11010010-V-0000.bin"
private noncomputable def vp11010010_1 : Blocks := edgeBlocks% "full/vectors/11010010-V-0001.bin"
private noncomputable def vp11010010_2 : Blocks := edgeBlocks% "full/vectors/11010010-V-0002.bin"
private noncomputable def vp11010010_3 : Blocks := edgeBlocks% "full/vectors/11010010-V-0003.bin"
noncomputable def vp11010010 : Blocks := (Blocks.join (Blocks.join vp11010010_0 vp11010010_1) (Blocks.join vp11010010_2 vp11010010_3))
private theorem bp110100100 : Branch 0 (-6719761639/32000000 : ℚ) vp11010010 := by
  apply branch_left_normalized (c:=vp110100100) (k:=0) (m:=215) (by decide +kernel)
  rw [show 2*(-6719761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6719761639/16000000 : ℚ) by norm_num]
  exact coverp110100100
private noncomputable def ep110100101_0 : Blocks := edgeBlocks% "full/vectors/110100101-E-0000.bin"
private noncomputable def ep110100101_1 : Blocks := edgeBlocks% "full/vectors/110100101-E-0001.bin"
private noncomputable def ep110100101_2 : Blocks := edgeBlocks% "full/vectors/110100101-E-0002.bin"
private noncomputable def ep110100101_3 : Blocks := edgeBlocks% "full/vectors/110100101-E-0003.bin"
noncomputable def ep110100101 : Blocks := (Blocks.join (Blocks.join ep110100101_0 ep110100101_1) (Blocks.join ep110100101_2 ep110100101_3))
private theorem idp110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11010010.list =
    C ((2:ℤ)^498) * horner X vp110100101.list + horner X ep110100101.list := by
  exact edge_identity (B := (2:ℤ)^712) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110100101 : Branch 1 (-6719761639/32000000 : ℚ) vp11010010 := by
  apply branch_checked idp110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-6719761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6735761639/16000000 : ℚ) by norm_num]
  exact coverp110100101
theorem coverp11010010 : Covers (-6719761639/32000000 : ℚ) vp11010010 := join_branches bp110100100 bp110100101
private noncomputable def vp1101001_0 : Blocks := edgeBlocks% "full/vectors/1101001-V-0000.bin"
private noncomputable def vp1101001_1 : Blocks := edgeBlocks% "full/vectors/1101001-V-0001.bin"
private noncomputable def vp1101001_2 : Blocks := edgeBlocks% "full/vectors/1101001-V-0002.bin"
private noncomputable def vp1101001_3 : Blocks := edgeBlocks% "full/vectors/1101001-V-0003.bin"
private noncomputable def vp1101001_4 : Blocks := edgeBlocks% "full/vectors/1101001-V-0004.bin"
private noncomputable def vp1101001_5 : Blocks := edgeBlocks% "full/vectors/1101001-V-0005.bin"
private noncomputable def vp1101001_6 : Blocks := edgeBlocks% "full/vectors/1101001-V-0006.bin"
noncomputable def vp1101001 : Blocks := (Blocks.join (Blocks.join vp1101001_0 (Blocks.join vp1101001_1 vp1101001_2)) (Blocks.join (Blocks.join vp1101001_3 vp1101001_4) (Blocks.join vp1101001_5 vp1101001_6)))
private theorem bp11010010 : Branch 0 (-6719761639/64000000 : ℚ) vp1101001 := by
  apply branch_left_normalized (c:=vp11010010) (k:=0) (m:=405) (by decide +kernel)
  rw [show 2*(-6719761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6719761639/32000000 : ℚ) by norm_num]
  exact coverp11010010
private noncomputable def ep11010011_0 : Blocks := edgeBlocks% "full/vectors/11010011-E-0000.bin"
private noncomputable def ep11010011_1 : Blocks := edgeBlocks% "full/vectors/11010011-E-0001.bin"
private noncomputable def ep11010011_2 : Blocks := edgeBlocks% "full/vectors/11010011-E-0002.bin"
private noncomputable def ep11010011_3 : Blocks := edgeBlocks% "full/vectors/11010011-E-0003.bin"
private noncomputable def ep11010011_4 : Blocks := edgeBlocks% "full/vectors/11010011-E-0004.bin"
private noncomputable def ep11010011_5 : Blocks := edgeBlocks% "full/vectors/11010011-E-0005.bin"
private noncomputable def ep11010011_6 : Blocks := edgeBlocks% "full/vectors/11010011-E-0006.bin"
noncomputable def ep11010011 : Blocks := (Blocks.join (Blocks.join ep11010011_0 (Blocks.join ep11010011_1 ep11010011_2)) (Blocks.join (Blocks.join ep11010011_3 ep11010011_4) (Blocks.join ep11010011_5 ep11010011_6)))
private theorem idp11010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1101001.list =
    C ((2:ℤ)^968) * horner X vp11010011.list + horner X ep11010011.list := by
  exact edge_identity (B := (2:ℤ)^1291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11010011 : Branch 1 (-6719761639/64000000 : ℚ) vp1101001 := by
  apply branch_checked idp11010011 (by positivity) (by decide +kernel)
  rw [show 2*(-6719761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6751761639/32000000 : ℚ) by norm_num]
  exact coverp11010011
theorem coverp1101001 : Covers (-6719761639/64000000 : ℚ) vp1101001 := join_branches bp11010010 bp11010011
private noncomputable def vp110100011_0 : Blocks := edgeBlocks% "full/vectors/110100011-V-0000.bin"
private noncomputable def vp110100011_1 : Blocks := edgeBlocks% "full/vectors/110100011-V-0001.bin"
noncomputable def vp110100011 : Blocks := (Blocks.join vp110100011_0 vp110100011_1)
theorem coverp110100011 : Covers (-6703761639/16000000 : ℚ) vp110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp1101000101_0 : Blocks := edgeBlocks% "full/vectors/1101000101-V-0000.bin"
noncomputable def vp1101000101 : Blocks := vp1101000101_0
theorem coverp1101000101 : Covers (-6695761639/8000000 : ℚ) vp1101000101 := cover_leaf (by decide +kernel)
private noncomputable def vp1101000100_0 : Blocks := edgeBlocks% "full/vectors/1101000100-V-0000.bin"
noncomputable def vp1101000100 : Blocks := vp1101000100_0
theorem coverp1101000100 : Covers (-6687761639/8000000 : ℚ) vp1101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp110100010_0 : Blocks := edgeBlocks% "full/vectors/110100010-V-0000.bin"
private noncomputable def vp110100010_1 : Blocks := edgeBlocks% "full/vectors/110100010-V-0001.bin"
noncomputable def vp110100010 : Blocks := (Blocks.join vp110100010_0 vp110100010_1)
private theorem bp1101000100 : Branch 0 (-6687761639/16000000 : ℚ) vp110100010 := by
  apply branch_left_normalized (c:=vp1101000100) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-6687761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6687761639/8000000 : ℚ) by norm_num]
  exact coverp1101000100
private noncomputable def ep1101000101_0 : Blocks := edgeBlocks% "full/vectors/1101000101-E-0000.bin"
private noncomputable def ep1101000101_1 : Blocks := edgeBlocks% "full/vectors/1101000101-E-0001.bin"
noncomputable def ep1101000101 : Blocks := (Blocks.join ep1101000101_0 ep1101000101_1)
private theorem idp1101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110100010.list =
    C ((2:ℤ)^263) * horner X vp1101000101.list + horner X ep1101000101.list := by
  exact edge_identity (B := (2:ℤ)^421) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1101000101 : Branch 1 (-6687761639/16000000 : ℚ) vp110100010 := by
  apply branch_checked idp1101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-6687761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6695761639/8000000 : ℚ) by norm_num]
  exact coverp1101000101
theorem coverp110100010 : Covers (-6687761639/16000000 : ℚ) vp110100010 := join_branches bp1101000100 bp1101000101
private noncomputable def vp11010001_0 : Blocks := edgeBlocks% "full/vectors/11010001-V-0000.bin"
private noncomputable def vp11010001_1 : Blocks := edgeBlocks% "full/vectors/11010001-V-0001.bin"
private noncomputable def vp11010001_2 : Blocks := edgeBlocks% "full/vectors/11010001-V-0002.bin"
private noncomputable def vp11010001_3 : Blocks := edgeBlocks% "full/vectors/11010001-V-0003.bin"
noncomputable def vp11010001 : Blocks := (Blocks.join (Blocks.join vp11010001_0 vp11010001_1) (Blocks.join vp11010001_2 vp11010001_3))
private theorem bp110100010 : Branch 0 (-6687761639/32000000 : ℚ) vp11010001 := by
  apply branch_left_normalized (c:=vp110100010) (k:=0) (m:=215) (by decide +kernel)
  rw [show 2*(-6687761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6687761639/16000000 : ℚ) by norm_num]
  exact coverp110100010
private noncomputable def ep110100011_0 : Blocks := edgeBlocks% "full/vectors/110100011-E-0000.bin"
private noncomputable def ep110100011_1 : Blocks := edgeBlocks% "full/vectors/110100011-E-0001.bin"
private noncomputable def ep110100011_2 : Blocks := edgeBlocks% "full/vectors/110100011-E-0002.bin"
private noncomputable def ep110100011_3 : Blocks := edgeBlocks% "full/vectors/110100011-E-0003.bin"
noncomputable def ep110100011 : Blocks := (Blocks.join (Blocks.join ep110100011_0 ep110100011_1) (Blocks.join ep110100011_2 ep110100011_3))
private theorem idp110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11010001.list =
    C ((2:ℤ)^499) * horner X vp110100011.list + horner X ep110100011.list := by
  exact edge_identity (B := (2:ℤ)^713) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110100011 : Branch 1 (-6687761639/32000000 : ℚ) vp11010001 := by
  apply branch_checked idp110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-6687761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6703761639/16000000 : ℚ) by norm_num]
  exact coverp110100011
theorem coverp11010001 : Covers (-6687761639/32000000 : ℚ) vp11010001 := join_branches bp110100010 bp110100011
private noncomputable def vp1101000011_0 : Blocks := edgeBlocks% "full/vectors/1101000011-V-0000.bin"
noncomputable def vp1101000011 : Blocks := vp1101000011_0
theorem coverp1101000011 : Covers (-6679761639/8000000 : ℚ) vp1101000011 := cover_leaf (by decide +kernel)
private noncomputable def vp1101000010_0 : Blocks := edgeBlocks% "full/vectors/1101000010-V-0000.bin"
noncomputable def vp1101000010 : Blocks := vp1101000010_0
theorem coverp1101000010 : Covers (-6671761639/8000000 : ℚ) vp1101000010 := cover_leaf (by decide +kernel)
private noncomputable def vp110100001_0 : Blocks := edgeBlocks% "full/vectors/110100001-V-0000.bin"
private noncomputable def vp110100001_1 : Blocks := edgeBlocks% "full/vectors/110100001-V-0001.bin"
noncomputable def vp110100001 : Blocks := (Blocks.join vp110100001_0 vp110100001_1)
private theorem bp1101000010 : Branch 0 (-6671761639/16000000 : ℚ) vp110100001 := by
  apply branch_left_normalized (c:=vp1101000010) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-6671761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6671761639/8000000 : ℚ) by norm_num]
  exact coverp1101000010
private noncomputable def ep1101000011_0 : Blocks := edgeBlocks% "full/vectors/1101000011-E-0000.bin"
private noncomputable def ep1101000011_1 : Blocks := edgeBlocks% "full/vectors/1101000011-E-0001.bin"
noncomputable def ep1101000011 : Blocks := (Blocks.join ep1101000011_0 ep1101000011_1)
private theorem idp1101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110100001.list =
    C ((2:ℤ)^261) * horner X vp1101000011.list + horner X ep1101000011.list := by
  exact edge_identity (B := (2:ℤ)^420) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1101000011 : Branch 1 (-6671761639/16000000 : ℚ) vp110100001 := by
  apply branch_checked idp1101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-6671761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6679761639/8000000 : ℚ) by norm_num]
  exact coverp1101000011
theorem coverp110100001 : Covers (-6671761639/16000000 : ℚ) vp110100001 := join_branches bp1101000010 bp1101000011
private noncomputable def vp1101000001_0 : Blocks := edgeBlocks% "full/vectors/1101000001-V-0000.bin"
noncomputable def vp1101000001 : Blocks := vp1101000001_0
theorem coverp1101000001 : Covers (-6663761639/8000000 : ℚ) vp1101000001 := cover_leaf (by decide +kernel)
private noncomputable def vp1101000000_0 : Blocks := edgeBlocks% "full/vectors/1101000000-V-0000.bin"
noncomputable def vp1101000000 : Blocks := vp1101000000_0
theorem coverp1101000000 : Covers (-6655761639/8000000 : ℚ) vp1101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp110100000_0 : Blocks := edgeBlocks% "full/vectors/110100000-V-0000.bin"
private noncomputable def vp110100000_1 : Blocks := edgeBlocks% "full/vectors/110100000-V-0001.bin"
noncomputable def vp110100000 : Blocks := (Blocks.join vp110100000_0 vp110100000_1)
private theorem bp1101000000 : Branch 0 (-6655761639/16000000 : ℚ) vp110100000 := by
  apply branch_left_normalized (c:=vp1101000000) (k:=0) (m:=118) (by decide +kernel)
  rw [show 2*(-6655761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-6655761639/8000000 : ℚ) by norm_num]
  exact coverp1101000000
private noncomputable def ep1101000001_0 : Blocks := edgeBlocks% "full/vectors/1101000001-E-0000.bin"
private noncomputable def ep1101000001_1 : Blocks := edgeBlocks% "full/vectors/1101000001-E-0001.bin"
noncomputable def ep1101000001 : Blocks := (Blocks.join ep1101000001_0 ep1101000001_1)
private theorem idp1101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110100000.list =
    C ((2:ℤ)^263) * horner X vp1101000001.list + horner X ep1101000001.list := by
  exact edge_identity (B := (2:ℤ)^422) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1101000001 : Branch 1 (-6655761639/16000000 : ℚ) vp110100000 := by
  apply branch_checked idp1101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-6655761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-6663761639/8000000 : ℚ) by norm_num]
  exact coverp1101000001
theorem coverp110100000 : Covers (-6655761639/16000000 : ℚ) vp110100000 := join_branches bp1101000000 bp1101000001
private noncomputable def vp11010000_0 : Blocks := edgeBlocks% "full/vectors/11010000-V-0000.bin"
private noncomputable def vp11010000_1 : Blocks := edgeBlocks% "full/vectors/11010000-V-0001.bin"
private noncomputable def vp11010000_2 : Blocks := edgeBlocks% "full/vectors/11010000-V-0002.bin"
private noncomputable def vp11010000_3 : Blocks := edgeBlocks% "full/vectors/11010000-V-0003.bin"
noncomputable def vp11010000 : Blocks := (Blocks.join (Blocks.join vp11010000_0 vp11010000_1) (Blocks.join vp11010000_2 vp11010000_3))
private theorem bp110100000 : Branch 0 (-6655761639/32000000 : ℚ) vp11010000 := by
  apply branch_left_normalized (c:=vp110100000) (k:=0) (m:=216) (by decide +kernel)
  rw [show 2*(-6655761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-6655761639/16000000 : ℚ) by norm_num]
  exact coverp110100000
private noncomputable def ep110100001_0 : Blocks := edgeBlocks% "full/vectors/110100001-E-0000.bin"
private noncomputable def ep110100001_1 : Blocks := edgeBlocks% "full/vectors/110100001-E-0001.bin"
private noncomputable def ep110100001_2 : Blocks := edgeBlocks% "full/vectors/110100001-E-0002.bin"
private noncomputable def ep110100001_3 : Blocks := edgeBlocks% "full/vectors/110100001-E-0003.bin"
noncomputable def ep110100001 : Blocks := (Blocks.join (Blocks.join ep110100001_0 ep110100001_1) (Blocks.join ep110100001_2 ep110100001_3))
private theorem idp110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11010000.list =
    C ((2:ℤ)^500) * horner X vp110100001.list + horner X ep110100001.list := by
  exact edge_identity (B := (2:ℤ)^715) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp110100001 : Branch 1 (-6655761639/32000000 : ℚ) vp11010000 := by
  apply branch_checked idp110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-6655761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-6671761639/16000000 : ℚ) by norm_num]
  exact coverp110100001
theorem coverp11010000 : Covers (-6655761639/32000000 : ℚ) vp11010000 := join_branches bp110100000 bp110100001
private noncomputable def vp1101000_0 : Blocks := edgeBlocks% "full/vectors/1101000-V-0000.bin"
private noncomputable def vp1101000_1 : Blocks := edgeBlocks% "full/vectors/1101000-V-0001.bin"
private noncomputable def vp1101000_2 : Blocks := edgeBlocks% "full/vectors/1101000-V-0002.bin"
private noncomputable def vp1101000_3 : Blocks := edgeBlocks% "full/vectors/1101000-V-0003.bin"
private noncomputable def vp1101000_4 : Blocks := edgeBlocks% "full/vectors/1101000-V-0004.bin"
private noncomputable def vp1101000_5 : Blocks := edgeBlocks% "full/vectors/1101000-V-0005.bin"
private noncomputable def vp1101000_6 : Blocks := edgeBlocks% "full/vectors/1101000-V-0006.bin"
noncomputable def vp1101000 : Blocks := (Blocks.join (Blocks.join vp1101000_0 (Blocks.join vp1101000_1 vp1101000_2)) (Blocks.join (Blocks.join vp1101000_3 vp1101000_4) (Blocks.join vp1101000_5 vp1101000_6)))
private theorem bp11010000 : Branch 0 (-6655761639/64000000 : ℚ) vp1101000 := by
  apply branch_left_normalized (c:=vp11010000) (k:=0) (m:=407) (by decide +kernel)
  rw [show 2*(-6655761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-6655761639/32000000 : ℚ) by norm_num]
  exact coverp11010000
private noncomputable def ep11010001_0 : Blocks := edgeBlocks% "full/vectors/11010001-E-0000.bin"
private noncomputable def ep11010001_1 : Blocks := edgeBlocks% "full/vectors/11010001-E-0001.bin"
private noncomputable def ep11010001_2 : Blocks := edgeBlocks% "full/vectors/11010001-E-0002.bin"
private noncomputable def ep11010001_3 : Blocks := edgeBlocks% "full/vectors/11010001-E-0003.bin"
private noncomputable def ep11010001_4 : Blocks := edgeBlocks% "full/vectors/11010001-E-0004.bin"
private noncomputable def ep11010001_5 : Blocks := edgeBlocks% "full/vectors/11010001-E-0005.bin"
private noncomputable def ep11010001_6 : Blocks := edgeBlocks% "full/vectors/11010001-E-0006.bin"
noncomputable def ep11010001 : Blocks := (Blocks.join (Blocks.join ep11010001_0 (Blocks.join ep11010001_1 ep11010001_2)) (Blocks.join (Blocks.join ep11010001_3 ep11010001_4) (Blocks.join ep11010001_5 ep11010001_6)))
private theorem idp11010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1101000.list =
    C ((2:ℤ)^971) * horner X vp11010001.list + horner X ep11010001.list := by
  exact edge_identity (B := (2:ℤ)^1297) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11010001 : Branch 1 (-6655761639/64000000 : ℚ) vp1101000 := by
  apply branch_checked idp11010001 (by positivity) (by decide +kernel)
  rw [show 2*(-6655761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-6687761639/32000000 : ℚ) by norm_num]
  exact coverp11010001
theorem coverp1101000 : Covers (-6655761639/64000000 : ℚ) vp1101000 := join_branches bp11010000 bp11010001
private noncomputable def vp110100_0 : Blocks := edgeBlocks% "full/vectors/110100-V-0000.bin"
private noncomputable def vp110100_1 : Blocks := edgeBlocks% "full/vectors/110100-V-0001.bin"
private noncomputable def vp110100_2 : Blocks := edgeBlocks% "full/vectors/110100-V-0002.bin"
private noncomputable def vp110100_3 : Blocks := edgeBlocks% "full/vectors/110100-V-0003.bin"
private noncomputable def vp110100_4 : Blocks := edgeBlocks% "full/vectors/110100-V-0004.bin"
private noncomputable def vp110100_5 : Blocks := edgeBlocks% "full/vectors/110100-V-0005.bin"
private noncomputable def vp110100_6 : Blocks := edgeBlocks% "full/vectors/110100-V-0006.bin"
private noncomputable def vp110100_7 : Blocks := edgeBlocks% "full/vectors/110100-V-0007.bin"
private noncomputable def vp110100_8 : Blocks := edgeBlocks% "full/vectors/110100-V-0008.bin"
private noncomputable def vp110100_9 : Blocks := edgeBlocks% "full/vectors/110100-V-0009.bin"
private noncomputable def vp110100_10 : Blocks := edgeBlocks% "full/vectors/110100-V-0010.bin"
private noncomputable def vp110100_11 : Blocks := edgeBlocks% "full/vectors/110100-V-0011.bin"
noncomputable def vp110100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp110100_0 (Blocks.join vp110100_1 vp110100_2)) (Blocks.join vp110100_3 (Blocks.join vp110100_4 vp110100_5))) (Blocks.join (Blocks.join vp110100_6 (Blocks.join vp110100_7 vp110100_8)) (Blocks.join vp110100_9 (Blocks.join vp110100_10 vp110100_11))))
private theorem bp1101000 : Branch 0 (-6655761639/128000000 : ℚ) vp110100 := by
  apply branch_left_normalized (c:=vp1101000) (k:=0) (m:=786) (by decide +kernel)
  rw [show 2*(-6655761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-6655761639/64000000 : ℚ) by norm_num]
  exact coverp1101000
private noncomputable def ep1101001_0 : Blocks := edgeBlocks% "full/vectors/1101001-E-0000.bin"
private noncomputable def ep1101001_1 : Blocks := edgeBlocks% "full/vectors/1101001-E-0001.bin"
private noncomputable def ep1101001_2 : Blocks := edgeBlocks% "full/vectors/1101001-E-0002.bin"
private noncomputable def ep1101001_3 : Blocks := edgeBlocks% "full/vectors/1101001-E-0003.bin"
private noncomputable def ep1101001_4 : Blocks := edgeBlocks% "full/vectors/1101001-E-0004.bin"
private noncomputable def ep1101001_5 : Blocks := edgeBlocks% "full/vectors/1101001-E-0005.bin"
private noncomputable def ep1101001_6 : Blocks := edgeBlocks% "full/vectors/1101001-E-0006.bin"
private noncomputable def ep1101001_7 : Blocks := edgeBlocks% "full/vectors/1101001-E-0007.bin"
private noncomputable def ep1101001_8 : Blocks := edgeBlocks% "full/vectors/1101001-E-0008.bin"
private noncomputable def ep1101001_9 : Blocks := edgeBlocks% "full/vectors/1101001-E-0009.bin"
private noncomputable def ep1101001_10 : Blocks := edgeBlocks% "full/vectors/1101001-E-0010.bin"
private noncomputable def ep1101001_11 : Blocks := edgeBlocks% "full/vectors/1101001-E-0011.bin"
noncomputable def ep1101001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1101001_0 (Blocks.join ep1101001_1 ep1101001_2)) (Blocks.join ep1101001_3 (Blocks.join ep1101001_4 ep1101001_5))) (Blocks.join (Blocks.join ep1101001_6 (Blocks.join ep1101001_7 ep1101001_8)) (Blocks.join ep1101001_9 (Blocks.join ep1101001_10 ep1101001_11))))
private theorem idp1101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp110100.list =
    C ((2:ℤ)^1900) * horner X vp1101001.list + horner X ep1101001.list := by
  exact edge_identity (B := (2:ℤ)^2446) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1101001 : Branch 1 (-6655761639/128000000 : ℚ) vp110100 := by
  apply branch_checked idp1101001 (by positivity) (by decide +kernel)
  rw [show 2*(-6655761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-6719761639/64000000 : ℚ) by norm_num]
  exact coverp1101001
theorem coverp110100 : Covers (-6655761639/128000000 : ℚ) vp110100 := join_branches bp1101000 bp1101001
private noncomputable def vp11010_0 : Blocks := edgeBlocks% "full/vectors/11010-V-0000.bin"
private noncomputable def vp11010_1 : Blocks := edgeBlocks% "full/vectors/11010-V-0001.bin"
private noncomputable def vp11010_2 : Blocks := edgeBlocks% "full/vectors/11010-V-0002.bin"
private noncomputable def vp11010_3 : Blocks := edgeBlocks% "full/vectors/11010-V-0003.bin"
private noncomputable def vp11010_4 : Blocks := edgeBlocks% "full/vectors/11010-V-0004.bin"
private noncomputable def vp11010_5 : Blocks := edgeBlocks% "full/vectors/11010-V-0005.bin"
private noncomputable def vp11010_6 : Blocks := edgeBlocks% "full/vectors/11010-V-0006.bin"
private noncomputable def vp11010_7 : Blocks := edgeBlocks% "full/vectors/11010-V-0007.bin"
private noncomputable def vp11010_8 : Blocks := edgeBlocks% "full/vectors/11010-V-0008.bin"
private noncomputable def vp11010_9 : Blocks := edgeBlocks% "full/vectors/11010-V-0009.bin"
private noncomputable def vp11010_10 : Blocks := edgeBlocks% "full/vectors/11010-V-0010.bin"
private noncomputable def vp11010_11 : Blocks := edgeBlocks% "full/vectors/11010-V-0011.bin"
private noncomputable def vp11010_12 : Blocks := edgeBlocks% "full/vectors/11010-V-0012.bin"
private noncomputable def vp11010_13 : Blocks := edgeBlocks% "full/vectors/11010-V-0013.bin"
private noncomputable def vp11010_14 : Blocks := edgeBlocks% "full/vectors/11010-V-0014.bin"
private noncomputable def vp11010_15 : Blocks := edgeBlocks% "full/vectors/11010-V-0015.bin"
private noncomputable def vp11010_16 : Blocks := edgeBlocks% "full/vectors/11010-V-0016.bin"
private noncomputable def vp11010_17 : Blocks := edgeBlocks% "full/vectors/11010-V-0017.bin"
private noncomputable def vp11010_18 : Blocks := edgeBlocks% "full/vectors/11010-V-0018.bin"
private noncomputable def vp11010_19 : Blocks := edgeBlocks% "full/vectors/11010-V-0019.bin"
private noncomputable def vp11010_20 : Blocks := edgeBlocks% "full/vectors/11010-V-0020.bin"
private noncomputable def vp11010_21 : Blocks := edgeBlocks% "full/vectors/11010-V-0021.bin"
private noncomputable def vp11010_22 : Blocks := edgeBlocks% "full/vectors/11010-V-0022.bin"
private noncomputable def vp11010_23 : Blocks := edgeBlocks% "full/vectors/11010-V-0023.bin"
noncomputable def vp11010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp11010_0 (Blocks.join vp11010_1 vp11010_2)) (Blocks.join vp11010_3 (Blocks.join vp11010_4 vp11010_5))) (Blocks.join (Blocks.join vp11010_6 (Blocks.join vp11010_7 vp11010_8)) (Blocks.join vp11010_9 (Blocks.join vp11010_10 vp11010_11)))) (Blocks.join (Blocks.join (Blocks.join vp11010_12 (Blocks.join vp11010_13 vp11010_14)) (Blocks.join vp11010_15 (Blocks.join vp11010_16 vp11010_17))) (Blocks.join (Blocks.join vp11010_18 (Blocks.join vp11010_19 vp11010_20)) (Blocks.join vp11010_21 (Blocks.join vp11010_22 vp11010_23)))))
private theorem bp110100 : Branch 0 (-6655761639/256000000 : ℚ) vp11010 := by
  apply branch_left_normalized (c:=vp110100) (k:=0) (m:=1530) (by decide +kernel)
  rw [show 2*(-6655761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-6655761639/128000000 : ℚ) by norm_num]
  exact coverp110100
private noncomputable def ep110101_0 : Blocks := edgeBlocks% "full/vectors/110101-E-0000.bin"
private noncomputable def ep110101_1 : Blocks := edgeBlocks% "full/vectors/110101-E-0001.bin"
private noncomputable def ep110101_2 : Blocks := edgeBlocks% "full/vectors/110101-E-0002.bin"
private noncomputable def ep110101_3 : Blocks := edgeBlocks% "full/vectors/110101-E-0003.bin"
private noncomputable def ep110101_4 : Blocks := edgeBlocks% "full/vectors/110101-E-0004.bin"
private noncomputable def ep110101_5 : Blocks := edgeBlocks% "full/vectors/110101-E-0005.bin"
private noncomputable def ep110101_6 : Blocks := edgeBlocks% "full/vectors/110101-E-0006.bin"
private noncomputable def ep110101_7 : Blocks := edgeBlocks% "full/vectors/110101-E-0007.bin"
private noncomputable def ep110101_8 : Blocks := edgeBlocks% "full/vectors/110101-E-0008.bin"
private noncomputable def ep110101_9 : Blocks := edgeBlocks% "full/vectors/110101-E-0009.bin"
private noncomputable def ep110101_10 : Blocks := edgeBlocks% "full/vectors/110101-E-0010.bin"
private noncomputable def ep110101_11 : Blocks := edgeBlocks% "full/vectors/110101-E-0011.bin"
private noncomputable def ep110101_12 : Blocks := edgeBlocks% "full/vectors/110101-E-0012.bin"
private noncomputable def ep110101_13 : Blocks := edgeBlocks% "full/vectors/110101-E-0013.bin"
private noncomputable def ep110101_14 : Blocks := edgeBlocks% "full/vectors/110101-E-0014.bin"
private noncomputable def ep110101_15 : Blocks := edgeBlocks% "full/vectors/110101-E-0015.bin"
private noncomputable def ep110101_16 : Blocks := edgeBlocks% "full/vectors/110101-E-0016.bin"
private noncomputable def ep110101_17 : Blocks := edgeBlocks% "full/vectors/110101-E-0017.bin"
private noncomputable def ep110101_18 : Blocks := edgeBlocks% "full/vectors/110101-E-0018.bin"
private noncomputable def ep110101_19 : Blocks := edgeBlocks% "full/vectors/110101-E-0019.bin"
private noncomputable def ep110101_20 : Blocks := edgeBlocks% "full/vectors/110101-E-0020.bin"
private noncomputable def ep110101_21 : Blocks := edgeBlocks% "full/vectors/110101-E-0021.bin"
private noncomputable def ep110101_22 : Blocks := edgeBlocks% "full/vectors/110101-E-0022.bin"
private noncomputable def ep110101_23 : Blocks := edgeBlocks% "full/vectors/110101-E-0023.bin"
noncomputable def ep110101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep110101_0 (Blocks.join ep110101_1 ep110101_2)) (Blocks.join ep110101_3 (Blocks.join ep110101_4 ep110101_5))) (Blocks.join (Blocks.join ep110101_6 (Blocks.join ep110101_7 ep110101_8)) (Blocks.join ep110101_9 (Blocks.join ep110101_10 ep110101_11)))) (Blocks.join (Blocks.join (Blocks.join ep110101_12 (Blocks.join ep110101_13 ep110101_14)) (Blocks.join ep110101_15 (Blocks.join ep110101_16 ep110101_17))) (Blocks.join (Blocks.join ep110101_18 (Blocks.join ep110101_19 ep110101_20)) (Blocks.join ep110101_21 (Blocks.join ep110101_22 ep110101_23)))))
private def ptsp110101 : List ℤ := [((2:ℤ)^4044+0),((2:ℤ)^4044+1)]
private theorem boundp110101 : 2^vp11010.size*absSum vp11010.list + ((2:ℤ)^3705*absSum vp110101.list+absSum ep110101.list) < (2:ℤ)^4680 := by decide +kernel
private theorem pointp110101_0 : fastHom 1 ((2:ℤ)^4044+0) vp11010 = ((2:ℤ)^3705)*vp110101.subst ((2:ℤ)^4044+0)+ep110101.subst ((2:ℤ)^4044+0) := by decide +kernel
private theorem pointp110101_1 : fastHom 1 ((2:ℤ)^4044+1) vp11010 = ((2:ℤ)^3705)*vp110101.subst ((2:ℤ)^4044+1)+ep110101.subst ((2:ℤ)^4044+1) := by decide +kernel
private theorem checkp110101 (x:ℤ) (hx:x ∈ ptsp110101) : fastHom 1 x vp11010 = ((2:ℤ)^3705)*vp110101.subst x+ep110101.subst x := by
  simp only [ptsp110101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp110101_0
  · exact pointp110101_1
private theorem idp110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11010.list =
    C ((2:ℤ)^3705) * horner X vp110101.list + horner X ep110101.list := by
  apply edge_identity (B := (2:ℤ)^4680) (by decide) (by positivity) (by positivity) boundp110101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp110101 (by decide +kernel)
  · have h : ptsp110101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp110101.trans_le (by decide +kernel)
  · exact checkp110101
private theorem bp110101 : Branch 1 (-6655761639/256000000 : ℚ) vp11010 := by
  apply branch_checked idp110101 (by positivity) (by decide +kernel)
  rw [show 2*(-6655761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-6783761639/128000000 : ℚ) by norm_num]
  exact coverp110101
theorem coverp11010 : Covers (-6655761639/256000000 : ℚ) vp11010 := join_branches bp110100 bp110101
private noncomputable def vp1101_0 : Blocks := edgeBlocks% "full/vectors/1101-V-0000.bin"
private noncomputable def vp1101_1 : Blocks := edgeBlocks% "full/vectors/1101-V-0001.bin"
private noncomputable def vp1101_2 : Blocks := edgeBlocks% "full/vectors/1101-V-0002.bin"
private noncomputable def vp1101_3 : Blocks := edgeBlocks% "full/vectors/1101-V-0003.bin"
private noncomputable def vp1101_4 : Blocks := edgeBlocks% "full/vectors/1101-V-0004.bin"
private noncomputable def vp1101_5 : Blocks := edgeBlocks% "full/vectors/1101-V-0005.bin"
private noncomputable def vp1101_6 : Blocks := edgeBlocks% "full/vectors/1101-V-0006.bin"
private noncomputable def vp1101_7 : Blocks := edgeBlocks% "full/vectors/1101-V-0007.bin"
private noncomputable def vp1101_8 : Blocks := edgeBlocks% "full/vectors/1101-V-0008.bin"
private noncomputable def vp1101_9 : Blocks := edgeBlocks% "full/vectors/1101-V-0009.bin"
private noncomputable def vp1101_10 : Blocks := edgeBlocks% "full/vectors/1101-V-0010.bin"
private noncomputable def vp1101_11 : Blocks := edgeBlocks% "full/vectors/1101-V-0011.bin"
private noncomputable def vp1101_12 : Blocks := edgeBlocks% "full/vectors/1101-V-0012.bin"
private noncomputable def vp1101_13 : Blocks := edgeBlocks% "full/vectors/1101-V-0013.bin"
private noncomputable def vp1101_14 : Blocks := edgeBlocks% "full/vectors/1101-V-0014.bin"
private noncomputable def vp1101_15 : Blocks := edgeBlocks% "full/vectors/1101-V-0015.bin"
private noncomputable def vp1101_16 : Blocks := edgeBlocks% "full/vectors/1101-V-0016.bin"
private noncomputable def vp1101_17 : Blocks := edgeBlocks% "full/vectors/1101-V-0017.bin"
private noncomputable def vp1101_18 : Blocks := edgeBlocks% "full/vectors/1101-V-0018.bin"
private noncomputable def vp1101_19 : Blocks := edgeBlocks% "full/vectors/1101-V-0019.bin"
private noncomputable def vp1101_20 : Blocks := edgeBlocks% "full/vectors/1101-V-0020.bin"
private noncomputable def vp1101_21 : Blocks := edgeBlocks% "full/vectors/1101-V-0021.bin"
private noncomputable def vp1101_22 : Blocks := edgeBlocks% "full/vectors/1101-V-0022.bin"
private noncomputable def vp1101_23 : Blocks := edgeBlocks% "full/vectors/1101-V-0023.bin"
private noncomputable def vp1101_24 : Blocks := edgeBlocks% "full/vectors/1101-V-0024.bin"
private noncomputable def vp1101_25 : Blocks := edgeBlocks% "full/vectors/1101-V-0025.bin"
private noncomputable def vp1101_26 : Blocks := edgeBlocks% "full/vectors/1101-V-0026.bin"
private noncomputable def vp1101_27 : Blocks := edgeBlocks% "full/vectors/1101-V-0027.bin"
private noncomputable def vp1101_28 : Blocks := edgeBlocks% "full/vectors/1101-V-0028.bin"
private noncomputable def vp1101_29 : Blocks := edgeBlocks% "full/vectors/1101-V-0029.bin"
private noncomputable def vp1101_30 : Blocks := edgeBlocks% "full/vectors/1101-V-0030.bin"
private noncomputable def vp1101_31 : Blocks := edgeBlocks% "full/vectors/1101-V-0031.bin"
private noncomputable def vp1101_32 : Blocks := edgeBlocks% "full/vectors/1101-V-0032.bin"
private noncomputable def vp1101_33 : Blocks := edgeBlocks% "full/vectors/1101-V-0033.bin"
private noncomputable def vp1101_34 : Blocks := edgeBlocks% "full/vectors/1101-V-0034.bin"
private noncomputable def vp1101_35 : Blocks := edgeBlocks% "full/vectors/1101-V-0035.bin"
private noncomputable def vp1101_36 : Blocks := edgeBlocks% "full/vectors/1101-V-0036.bin"
private noncomputable def vp1101_37 : Blocks := edgeBlocks% "full/vectors/1101-V-0037.bin"
private noncomputable def vp1101_38 : Blocks := edgeBlocks% "full/vectors/1101-V-0038.bin"
private noncomputable def vp1101_39 : Blocks := edgeBlocks% "full/vectors/1101-V-0039.bin"
private noncomputable def vp1101_40 : Blocks := edgeBlocks% "full/vectors/1101-V-0040.bin"
private noncomputable def vp1101_41 : Blocks := edgeBlocks% "full/vectors/1101-V-0041.bin"
private noncomputable def vp1101_42 : Blocks := edgeBlocks% "full/vectors/1101-V-0042.bin"
private noncomputable def vp1101_43 : Blocks := edgeBlocks% "full/vectors/1101-V-0043.bin"
noncomputable def vp1101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1101_0 vp1101_1) (Blocks.join vp1101_2 (Blocks.join vp1101_3 vp1101_4))) (Blocks.join (Blocks.join vp1101_5 (Blocks.join vp1101_6 vp1101_7)) (Blocks.join vp1101_8 (Blocks.join vp1101_9 vp1101_10)))) (Blocks.join (Blocks.join (Blocks.join vp1101_11 vp1101_12) (Blocks.join vp1101_13 (Blocks.join vp1101_14 vp1101_15))) (Blocks.join (Blocks.join vp1101_16 (Blocks.join vp1101_17 vp1101_18)) (Blocks.join vp1101_19 (Blocks.join vp1101_20 vp1101_21))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1101_22 vp1101_23) (Blocks.join vp1101_24 (Blocks.join vp1101_25 vp1101_26))) (Blocks.join (Blocks.join vp1101_27 (Blocks.join vp1101_28 vp1101_29)) (Blocks.join vp1101_30 (Blocks.join vp1101_31 vp1101_32)))) (Blocks.join (Blocks.join (Blocks.join vp1101_33 vp1101_34) (Blocks.join vp1101_35 (Blocks.join vp1101_36 vp1101_37))) (Blocks.join (Blocks.join vp1101_38 (Blocks.join vp1101_39 vp1101_40)) (Blocks.join vp1101_41 (Blocks.join vp1101_42 vp1101_43))))))
private theorem bp11010 : Branch 0 (-6655761639/512000000 : ℚ) vp1101 := by
  apply branch_left_normalized (c:=vp11010) (k:=0) (m:=2966) (by decide +kernel)
  rw [show 2*(-6655761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-6655761639/256000000 : ℚ) by norm_num]
  exact coverp11010
private noncomputable def ep11011_0 : Blocks := edgeBlocks% "full/vectors/11011-E-0000.bin"
private noncomputable def ep11011_1 : Blocks := edgeBlocks% "full/vectors/11011-E-0001.bin"
private noncomputable def ep11011_2 : Blocks := edgeBlocks% "full/vectors/11011-E-0002.bin"
private noncomputable def ep11011_3 : Blocks := edgeBlocks% "full/vectors/11011-E-0003.bin"
private noncomputable def ep11011_4 : Blocks := edgeBlocks% "full/vectors/11011-E-0004.bin"
private noncomputable def ep11011_5 : Blocks := edgeBlocks% "full/vectors/11011-E-0005.bin"
private noncomputable def ep11011_6 : Blocks := edgeBlocks% "full/vectors/11011-E-0006.bin"
private noncomputable def ep11011_7 : Blocks := edgeBlocks% "full/vectors/11011-E-0007.bin"
private noncomputable def ep11011_8 : Blocks := edgeBlocks% "full/vectors/11011-E-0008.bin"
private noncomputable def ep11011_9 : Blocks := edgeBlocks% "full/vectors/11011-E-0009.bin"
private noncomputable def ep11011_10 : Blocks := edgeBlocks% "full/vectors/11011-E-0010.bin"
private noncomputable def ep11011_11 : Blocks := edgeBlocks% "full/vectors/11011-E-0011.bin"
private noncomputable def ep11011_12 : Blocks := edgeBlocks% "full/vectors/11011-E-0012.bin"
private noncomputable def ep11011_13 : Blocks := edgeBlocks% "full/vectors/11011-E-0013.bin"
private noncomputable def ep11011_14 : Blocks := edgeBlocks% "full/vectors/11011-E-0014.bin"
private noncomputable def ep11011_15 : Blocks := edgeBlocks% "full/vectors/11011-E-0015.bin"
private noncomputable def ep11011_16 : Blocks := edgeBlocks% "full/vectors/11011-E-0016.bin"
private noncomputable def ep11011_17 : Blocks := edgeBlocks% "full/vectors/11011-E-0017.bin"
private noncomputable def ep11011_18 : Blocks := edgeBlocks% "full/vectors/11011-E-0018.bin"
private noncomputable def ep11011_19 : Blocks := edgeBlocks% "full/vectors/11011-E-0019.bin"
private noncomputable def ep11011_20 : Blocks := edgeBlocks% "full/vectors/11011-E-0020.bin"
private noncomputable def ep11011_21 : Blocks := edgeBlocks% "full/vectors/11011-E-0021.bin"
private noncomputable def ep11011_22 : Blocks := edgeBlocks% "full/vectors/11011-E-0022.bin"
private noncomputable def ep11011_23 : Blocks := edgeBlocks% "full/vectors/11011-E-0023.bin"
private noncomputable def ep11011_24 : Blocks := edgeBlocks% "full/vectors/11011-E-0024.bin"
private noncomputable def ep11011_25 : Blocks := edgeBlocks% "full/vectors/11011-E-0025.bin"
private noncomputable def ep11011_26 : Blocks := edgeBlocks% "full/vectors/11011-E-0026.bin"
private noncomputable def ep11011_27 : Blocks := edgeBlocks% "full/vectors/11011-E-0027.bin"
private noncomputable def ep11011_28 : Blocks := edgeBlocks% "full/vectors/11011-E-0028.bin"
private noncomputable def ep11011_29 : Blocks := edgeBlocks% "full/vectors/11011-E-0029.bin"
private noncomputable def ep11011_30 : Blocks := edgeBlocks% "full/vectors/11011-E-0030.bin"
private noncomputable def ep11011_31 : Blocks := edgeBlocks% "full/vectors/11011-E-0031.bin"
private noncomputable def ep11011_32 : Blocks := edgeBlocks% "full/vectors/11011-E-0032.bin"
private noncomputable def ep11011_33 : Blocks := edgeBlocks% "full/vectors/11011-E-0033.bin"
private noncomputable def ep11011_34 : Blocks := edgeBlocks% "full/vectors/11011-E-0034.bin"
private noncomputable def ep11011_35 : Blocks := edgeBlocks% "full/vectors/11011-E-0035.bin"
private noncomputable def ep11011_36 : Blocks := edgeBlocks% "full/vectors/11011-E-0036.bin"
private noncomputable def ep11011_37 : Blocks := edgeBlocks% "full/vectors/11011-E-0037.bin"
private noncomputable def ep11011_38 : Blocks := edgeBlocks% "full/vectors/11011-E-0038.bin"
private noncomputable def ep11011_39 : Blocks := edgeBlocks% "full/vectors/11011-E-0039.bin"
private noncomputable def ep11011_40 : Blocks := edgeBlocks% "full/vectors/11011-E-0040.bin"
private noncomputable def ep11011_41 : Blocks := edgeBlocks% "full/vectors/11011-E-0041.bin"
private noncomputable def ep11011_42 : Blocks := edgeBlocks% "full/vectors/11011-E-0042.bin"
private noncomputable def ep11011_43 : Blocks := edgeBlocks% "full/vectors/11011-E-0043.bin"
noncomputable def ep11011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep11011_0 ep11011_1) (Blocks.join ep11011_2 (Blocks.join ep11011_3 ep11011_4))) (Blocks.join (Blocks.join ep11011_5 (Blocks.join ep11011_6 ep11011_7)) (Blocks.join ep11011_8 (Blocks.join ep11011_9 ep11011_10)))) (Blocks.join (Blocks.join (Blocks.join ep11011_11 ep11011_12) (Blocks.join ep11011_13 (Blocks.join ep11011_14 ep11011_15))) (Blocks.join (Blocks.join ep11011_16 (Blocks.join ep11011_17 ep11011_18)) (Blocks.join ep11011_19 (Blocks.join ep11011_20 ep11011_21))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep11011_22 ep11011_23) (Blocks.join ep11011_24 (Blocks.join ep11011_25 ep11011_26))) (Blocks.join (Blocks.join ep11011_27 (Blocks.join ep11011_28 ep11011_29)) (Blocks.join ep11011_30 (Blocks.join ep11011_31 ep11011_32)))) (Blocks.join (Blocks.join (Blocks.join ep11011_33 ep11011_34) (Blocks.join ep11011_35 (Blocks.join ep11011_36 ep11011_37))) (Blocks.join (Blocks.join ep11011_38 (Blocks.join ep11011_39 ep11011_40)) (Blocks.join ep11011_41 (Blocks.join ep11011_42 ep11011_43))))))
private def ptsp11011 : List ℤ := [((2:ℤ)^2132+0),((2:ℤ)^2132+1),((2:ℤ)^2132+2),((2:ℤ)^2132+3),((2:ℤ)^2132+4)]
private theorem boundp11011 : 2^vp1101.size*absSum vp1101.list + ((2:ℤ)^7104*absSum vp11011.list+absSum ep11011.list) < (2:ℤ)^8896 := by decide +kernel
private theorem pointp11011_0 : fastHom 1 ((2:ℤ)^2132+0) vp1101 = ((2:ℤ)^7104)*vp11011.subst ((2:ℤ)^2132+0)+ep11011.subst ((2:ℤ)^2132+0) := by decide +kernel
private theorem pointp11011_1 : fastHom 1 ((2:ℤ)^2132+1) vp1101 = ((2:ℤ)^7104)*vp11011.subst ((2:ℤ)^2132+1)+ep11011.subst ((2:ℤ)^2132+1) := by decide +kernel
private theorem pointp11011_2 : fastHom 1 ((2:ℤ)^2132+2) vp1101 = ((2:ℤ)^7104)*vp11011.subst ((2:ℤ)^2132+2)+ep11011.subst ((2:ℤ)^2132+2) := by decide +kernel
private theorem pointp11011_3 : fastHom 1 ((2:ℤ)^2132+3) vp1101 = ((2:ℤ)^7104)*vp11011.subst ((2:ℤ)^2132+3)+ep11011.subst ((2:ℤ)^2132+3) := by decide +kernel
private theorem pointp11011_4 : fastHom 1 ((2:ℤ)^2132+4) vp1101 = ((2:ℤ)^7104)*vp11011.subst ((2:ℤ)^2132+4)+ep11011.subst ((2:ℤ)^2132+4) := by decide +kernel
private theorem checkp11011 (x:ℤ) (hx:x ∈ ptsp11011) : fastHom 1 x vp1101 = ((2:ℤ)^7104)*vp11011.subst x+ep11011.subst x := by
  simp only [ptsp11011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact pointp11011_0
  · exact pointp11011_1
  · exact pointp11011_2
  · exact pointp11011_3
  · exact pointp11011_4
private theorem idp11011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1101.list =
    C ((2:ℤ)^7104) * horner X vp11011.list + horner X ep11011.list := by
  apply edge_identity (B := (2:ℤ)^8896) (by decide) (by positivity) (by positivity) boundp11011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp11011 (by decide +kernel)
  · have h : ptsp11011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp11011.trans_le (by decide +kernel)
  · exact checkp11011
private theorem bp11011 : Branch 1 (-6655761639/512000000 : ℚ) vp1101 := by
  apply branch_checked idp11011 (by positivity) (by decide +kernel)
  rw [show 2*(-6655761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-6911761639/256000000 : ℚ) by norm_num]
  exact coverp11011
theorem coverp1101 : Covers (-6655761639/512000000 : ℚ) vp1101 := join_branches bp11010 bp11011
end NextProof.EdgeFull

