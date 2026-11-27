import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00143

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp11101111_0 : Blocks := edgeBlocks% "full/vectors/11101111-V-0000.bin"
private noncomputable def vp11101111_1 : Blocks := edgeBlocks% "full/vectors/11101111-V-0001.bin"
private noncomputable def vp11101111_2 : Blocks := edgeBlocks% "full/vectors/11101111-V-0002.bin"
noncomputable def vp11101111 : Blocks := (Blocks.join vp11101111_0 (Blocks.join vp11101111_1 vp11101111_2))
theorem coverp11101111 : Covers (-7647761639/32000000 : ℚ) vp11101111 := cover_leaf (by decide +kernel)
private noncomputable def vp11101110_0 : Blocks := edgeBlocks% "full/vectors/11101110-V-0000.bin"
private noncomputable def vp11101110_1 : Blocks := edgeBlocks% "full/vectors/11101110-V-0001.bin"
private noncomputable def vp11101110_2 : Blocks := edgeBlocks% "full/vectors/11101110-V-0002.bin"
noncomputable def vp11101110 : Blocks := (Blocks.join vp11101110_0 (Blocks.join vp11101110_1 vp11101110_2))
theorem coverp11101110 : Covers (-7615761639/32000000 : ℚ) vp11101110 := cover_leaf (by decide +kernel)
private noncomputable def vp1110111_0 : Blocks := edgeBlocks% "full/vectors/1110111-V-0000.bin"
private noncomputable def vp1110111_1 : Blocks := edgeBlocks% "full/vectors/1110111-V-0001.bin"
private noncomputable def vp1110111_2 : Blocks := edgeBlocks% "full/vectors/1110111-V-0002.bin"
private noncomputable def vp1110111_3 : Blocks := edgeBlocks% "full/vectors/1110111-V-0003.bin"
private noncomputable def vp1110111_4 : Blocks := edgeBlocks% "full/vectors/1110111-V-0004.bin"
private noncomputable def vp1110111_5 : Blocks := edgeBlocks% "full/vectors/1110111-V-0005.bin"
noncomputable def vp1110111 : Blocks := (Blocks.join (Blocks.join vp1110111_0 (Blocks.join vp1110111_1 vp1110111_2)) (Blocks.join vp1110111_3 (Blocks.join vp1110111_4 vp1110111_5)))
private theorem bp11101110 : Branch 0 (-7615761639/64000000 : ℚ) vp1110111 := by
  apply branch_left_normalized (c:=vp11101110) (k:=0) (m:=382) (by decide +kernel)
  rw [show 2*(-7615761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7615761639/32000000 : ℚ) by norm_num]
  exact coverp11101110
private noncomputable def ep11101111_0 : Blocks := edgeBlocks% "full/vectors/11101111-E-0000.bin"
private noncomputable def ep11101111_1 : Blocks := edgeBlocks% "full/vectors/11101111-E-0001.bin"
private noncomputable def ep11101111_2 : Blocks := edgeBlocks% "full/vectors/11101111-E-0002.bin"
private noncomputable def ep11101111_3 : Blocks := edgeBlocks% "full/vectors/11101111-E-0003.bin"
private noncomputable def ep11101111_4 : Blocks := edgeBlocks% "full/vectors/11101111-E-0004.bin"
private noncomputable def ep11101111_5 : Blocks := edgeBlocks% "full/vectors/11101111-E-0005.bin"
noncomputable def ep11101111 : Blocks := (Blocks.join (Blocks.join ep11101111_0 (Blocks.join ep11101111_1 ep11101111_2)) (Blocks.join ep11101111_3 (Blocks.join ep11101111_4 ep11101111_5)))
private theorem idp11101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1110111.list =
    C ((2:ℤ)^924) * horner X vp11101111.list + horner X ep11101111.list := by
  exact edge_identity (B := (2:ℤ)^1225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11101111 : Branch 1 (-7615761639/64000000 : ℚ) vp1110111 := by
  apply branch_checked idp11101111 (by positivity) (by decide +kernel)
  rw [show 2*(-7615761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7647761639/32000000 : ℚ) by norm_num]
  exact coverp11101111
theorem coverp1110111 : Covers (-7615761639/64000000 : ℚ) vp1110111 := join_branches bp11101110 bp11101111
private noncomputable def vp11101101_0 : Blocks := edgeBlocks% "full/vectors/11101101-V-0000.bin"
private noncomputable def vp11101101_1 : Blocks := edgeBlocks% "full/vectors/11101101-V-0001.bin"
private noncomputable def vp11101101_2 : Blocks := edgeBlocks% "full/vectors/11101101-V-0002.bin"
private noncomputable def vp11101101_3 : Blocks := edgeBlocks% "full/vectors/11101101-V-0003.bin"
noncomputable def vp11101101 : Blocks := (Blocks.join (Blocks.join vp11101101_0 vp11101101_1) (Blocks.join vp11101101_2 vp11101101_3))
theorem coverp11101101 : Covers (-7583761639/32000000 : ℚ) vp11101101 := cover_leaf (by decide +kernel)
private noncomputable def vp11101100_0 : Blocks := edgeBlocks% "full/vectors/11101100-V-0000.bin"
private noncomputable def vp11101100_1 : Blocks := edgeBlocks% "full/vectors/11101100-V-0001.bin"
private noncomputable def vp11101100_2 : Blocks := edgeBlocks% "full/vectors/11101100-V-0002.bin"
noncomputable def vp11101100 : Blocks := (Blocks.join vp11101100_0 (Blocks.join vp11101100_1 vp11101100_2))
theorem coverp11101100 : Covers (-7551761639/32000000 : ℚ) vp11101100 := cover_leaf (by decide +kernel)
private noncomputable def vp1110110_0 : Blocks := edgeBlocks% "full/vectors/1110110-V-0000.bin"
private noncomputable def vp1110110_1 : Blocks := edgeBlocks% "full/vectors/1110110-V-0001.bin"
private noncomputable def vp1110110_2 : Blocks := edgeBlocks% "full/vectors/1110110-V-0002.bin"
private noncomputable def vp1110110_3 : Blocks := edgeBlocks% "full/vectors/1110110-V-0003.bin"
private noncomputable def vp1110110_4 : Blocks := edgeBlocks% "full/vectors/1110110-V-0004.bin"
private noncomputable def vp1110110_5 : Blocks := edgeBlocks% "full/vectors/1110110-V-0005.bin"
noncomputable def vp1110110 : Blocks := (Blocks.join (Blocks.join vp1110110_0 (Blocks.join vp1110110_1 vp1110110_2)) (Blocks.join vp1110110_3 (Blocks.join vp1110110_4 vp1110110_5)))
private theorem bp11101100 : Branch 0 (-7551761639/64000000 : ℚ) vp1110110 := by
  apply branch_left_normalized (c:=vp11101100) (k:=0) (m:=383) (by decide +kernel)
  rw [show 2*(-7551761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7551761639/32000000 : ℚ) by norm_num]
  exact coverp11101100
private noncomputable def ep11101101_0 : Blocks := edgeBlocks% "full/vectors/11101101-E-0000.bin"
private noncomputable def ep11101101_1 : Blocks := edgeBlocks% "full/vectors/11101101-E-0001.bin"
private noncomputable def ep11101101_2 : Blocks := edgeBlocks% "full/vectors/11101101-E-0002.bin"
private noncomputable def ep11101101_3 : Blocks := edgeBlocks% "full/vectors/11101101-E-0003.bin"
private noncomputable def ep11101101_4 : Blocks := edgeBlocks% "full/vectors/11101101-E-0004.bin"
private noncomputable def ep11101101_5 : Blocks := edgeBlocks% "full/vectors/11101101-E-0005.bin"
noncomputable def ep11101101 : Blocks := (Blocks.join (Blocks.join ep11101101_0 (Blocks.join ep11101101_1 ep11101101_2)) (Blocks.join ep11101101_3 (Blocks.join ep11101101_4 ep11101101_5)))
private theorem idp11101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1110110.list =
    C ((2:ℤ)^927) * horner X vp11101101.list + horner X ep11101101.list := by
  exact edge_identity (B := (2:ℤ)^1229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11101101 : Branch 1 (-7551761639/64000000 : ℚ) vp1110110 := by
  apply branch_checked idp11101101 (by positivity) (by decide +kernel)
  rw [show 2*(-7551761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7583761639/32000000 : ℚ) by norm_num]
  exact coverp11101101
theorem coverp1110110 : Covers (-7551761639/64000000 : ℚ) vp1110110 := join_branches bp11101100 bp11101101
private noncomputable def vp111011_0 : Blocks := edgeBlocks% "full/vectors/111011-V-0000.bin"
private noncomputable def vp111011_1 : Blocks := edgeBlocks% "full/vectors/111011-V-0001.bin"
private noncomputable def vp111011_2 : Blocks := edgeBlocks% "full/vectors/111011-V-0002.bin"
private noncomputable def vp111011_3 : Blocks := edgeBlocks% "full/vectors/111011-V-0003.bin"
private noncomputable def vp111011_4 : Blocks := edgeBlocks% "full/vectors/111011-V-0004.bin"
private noncomputable def vp111011_5 : Blocks := edgeBlocks% "full/vectors/111011-V-0005.bin"
private noncomputable def vp111011_6 : Blocks := edgeBlocks% "full/vectors/111011-V-0006.bin"
private noncomputable def vp111011_7 : Blocks := edgeBlocks% "full/vectors/111011-V-0007.bin"
private noncomputable def vp111011_8 : Blocks := edgeBlocks% "full/vectors/111011-V-0008.bin"
private noncomputable def vp111011_9 : Blocks := edgeBlocks% "full/vectors/111011-V-0009.bin"
private noncomputable def vp111011_10 : Blocks := edgeBlocks% "full/vectors/111011-V-0010.bin"
private noncomputable def vp111011_11 : Blocks := edgeBlocks% "full/vectors/111011-V-0011.bin"
noncomputable def vp111011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp111011_0 (Blocks.join vp111011_1 vp111011_2)) (Blocks.join vp111011_3 (Blocks.join vp111011_4 vp111011_5))) (Blocks.join (Blocks.join vp111011_6 (Blocks.join vp111011_7 vp111011_8)) (Blocks.join vp111011_9 (Blocks.join vp111011_10 vp111011_11))))
private theorem bp1110110 : Branch 0 (-7551761639/128000000 : ℚ) vp111011 := by
  apply branch_left_normalized (c:=vp1110110) (k:=0) (m:=741) (by decide +kernel)
  rw [show 2*(-7551761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-7551761639/64000000 : ℚ) by norm_num]
  exact coverp1110110
private noncomputable def ep1110111_0 : Blocks := edgeBlocks% "full/vectors/1110111-E-0000.bin"
private noncomputable def ep1110111_1 : Blocks := edgeBlocks% "full/vectors/1110111-E-0001.bin"
private noncomputable def ep1110111_2 : Blocks := edgeBlocks% "full/vectors/1110111-E-0002.bin"
private noncomputable def ep1110111_3 : Blocks := edgeBlocks% "full/vectors/1110111-E-0003.bin"
private noncomputable def ep1110111_4 : Blocks := edgeBlocks% "full/vectors/1110111-E-0004.bin"
private noncomputable def ep1110111_5 : Blocks := edgeBlocks% "full/vectors/1110111-E-0005.bin"
private noncomputable def ep1110111_6 : Blocks := edgeBlocks% "full/vectors/1110111-E-0006.bin"
private noncomputable def ep1110111_7 : Blocks := edgeBlocks% "full/vectors/1110111-E-0007.bin"
private noncomputable def ep1110111_8 : Blocks := edgeBlocks% "full/vectors/1110111-E-0008.bin"
private noncomputable def ep1110111_9 : Blocks := edgeBlocks% "full/vectors/1110111-E-0009.bin"
private noncomputable def ep1110111_10 : Blocks := edgeBlocks% "full/vectors/1110111-E-0010.bin"
private noncomputable def ep1110111_11 : Blocks := edgeBlocks% "full/vectors/1110111-E-0011.bin"
noncomputable def ep1110111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1110111_0 (Blocks.join ep1110111_1 ep1110111_2)) (Blocks.join ep1110111_3 (Blocks.join ep1110111_4 ep1110111_5))) (Blocks.join (Blocks.join ep1110111_6 (Blocks.join ep1110111_7 ep1110111_8)) (Blocks.join ep1110111_9 (Blocks.join ep1110111_10 ep1110111_11))))
private theorem idp1110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp111011.list =
    C ((2:ℤ)^1812) * horner X vp1110111.list + horner X ep1110111.list := by
  exact edge_identity (B := (2:ℤ)^2310) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1110111 : Branch 1 (-7551761639/128000000 : ℚ) vp111011 := by
  apply branch_checked idp1110111 (by positivity) (by decide +kernel)
  rw [show 2*(-7551761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-7615761639/64000000 : ℚ) by norm_num]
  exact coverp1110111
theorem coverp111011 : Covers (-7551761639/128000000 : ℚ) vp111011 := join_branches bp1110110 bp1110111
private noncomputable def vp11101011_0 : Blocks := edgeBlocks% "full/vectors/11101011-V-0000.bin"
private noncomputable def vp11101011_1 : Blocks := edgeBlocks% "full/vectors/11101011-V-0001.bin"
private noncomputable def vp11101011_2 : Blocks := edgeBlocks% "full/vectors/11101011-V-0002.bin"
private noncomputable def vp11101011_3 : Blocks := edgeBlocks% "full/vectors/11101011-V-0003.bin"
noncomputable def vp11101011 : Blocks := (Blocks.join (Blocks.join vp11101011_0 vp11101011_1) (Blocks.join vp11101011_2 vp11101011_3))
theorem coverp11101011 : Covers (-7519761639/32000000 : ℚ) vp11101011 := cover_leaf (by decide +kernel)
private noncomputable def vp111010101_0 : Blocks := edgeBlocks% "full/vectors/111010101-V-0000.bin"
private noncomputable def vp111010101_1 : Blocks := edgeBlocks% "full/vectors/111010101-V-0001.bin"
noncomputable def vp111010101 : Blocks := (Blocks.join vp111010101_0 vp111010101_1)
theorem coverp111010101 : Covers (-7503761639/16000000 : ℚ) vp111010101 := cover_leaf (by decide +kernel)
private noncomputable def vp111010100_0 : Blocks := edgeBlocks% "full/vectors/111010100-V-0000.bin"
private noncomputable def vp111010100_1 : Blocks := edgeBlocks% "full/vectors/111010100-V-0001.bin"
noncomputable def vp111010100 : Blocks := (Blocks.join vp111010100_0 vp111010100_1)
theorem coverp111010100 : Covers (-7487761639/16000000 : ℚ) vp111010100 := cover_leaf (by decide +kernel)
private noncomputable def vp11101010_0 : Blocks := edgeBlocks% "full/vectors/11101010-V-0000.bin"
private noncomputable def vp11101010_1 : Blocks := edgeBlocks% "full/vectors/11101010-V-0001.bin"
private noncomputable def vp11101010_2 : Blocks := edgeBlocks% "full/vectors/11101010-V-0002.bin"
private noncomputable def vp11101010_3 : Blocks := edgeBlocks% "full/vectors/11101010-V-0003.bin"
noncomputable def vp11101010 : Blocks := (Blocks.join (Blocks.join vp11101010_0 vp11101010_1) (Blocks.join vp11101010_2 vp11101010_3))
private theorem bp111010100 : Branch 0 (-7487761639/32000000 : ℚ) vp11101010 := by
  apply branch_left_normalized (c:=vp111010100) (k:=0) (m:=205) (by decide +kernel)
  rw [show 2*(-7487761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7487761639/16000000 : ℚ) by norm_num]
  exact coverp111010100
private noncomputable def ep111010101_0 : Blocks := edgeBlocks% "full/vectors/111010101-E-0000.bin"
private noncomputable def ep111010101_1 : Blocks := edgeBlocks% "full/vectors/111010101-E-0001.bin"
private noncomputable def ep111010101_2 : Blocks := edgeBlocks% "full/vectors/111010101-E-0002.bin"
private noncomputable def ep111010101_3 : Blocks := edgeBlocks% "full/vectors/111010101-E-0003.bin"
noncomputable def ep111010101 : Blocks := (Blocks.join (Blocks.join ep111010101_0 ep111010101_1) (Blocks.join ep111010101_2 ep111010101_3))
private theorem idp111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11101010.list =
    C ((2:ℤ)^479) * horner X vp111010101.list + horner X ep111010101.list := by
  exact edge_identity (B := (2:ℤ)^683) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111010101 : Branch 1 (-7487761639/32000000 : ℚ) vp11101010 := by
  apply branch_checked idp111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-7487761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7503761639/16000000 : ℚ) by norm_num]
  exact coverp111010101
theorem coverp11101010 : Covers (-7487761639/32000000 : ℚ) vp11101010 := join_branches bp111010100 bp111010101
private noncomputable def vp1110101_0 : Blocks := edgeBlocks% "full/vectors/1110101-V-0000.bin"
private noncomputable def vp1110101_1 : Blocks := edgeBlocks% "full/vectors/1110101-V-0001.bin"
private noncomputable def vp1110101_2 : Blocks := edgeBlocks% "full/vectors/1110101-V-0002.bin"
private noncomputable def vp1110101_3 : Blocks := edgeBlocks% "full/vectors/1110101-V-0003.bin"
private noncomputable def vp1110101_4 : Blocks := edgeBlocks% "full/vectors/1110101-V-0004.bin"
private noncomputable def vp1110101_5 : Blocks := edgeBlocks% "full/vectors/1110101-V-0005.bin"
noncomputable def vp1110101 : Blocks := (Blocks.join (Blocks.join vp1110101_0 (Blocks.join vp1110101_1 vp1110101_2)) (Blocks.join vp1110101_3 (Blocks.join vp1110101_4 vp1110101_5)))
private theorem bp11101010 : Branch 0 (-7487761639/64000000 : ℚ) vp1110101 := by
  apply branch_left_normalized (c:=vp11101010) (k:=0) (m:=386) (by decide +kernel)
  rw [show 2*(-7487761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7487761639/32000000 : ℚ) by norm_num]
  exact coverp11101010
private noncomputable def ep11101011_0 : Blocks := edgeBlocks% "full/vectors/11101011-E-0000.bin"
private noncomputable def ep11101011_1 : Blocks := edgeBlocks% "full/vectors/11101011-E-0001.bin"
private noncomputable def ep11101011_2 : Blocks := edgeBlocks% "full/vectors/11101011-E-0002.bin"
private noncomputable def ep11101011_3 : Blocks := edgeBlocks% "full/vectors/11101011-E-0003.bin"
private noncomputable def ep11101011_4 : Blocks := edgeBlocks% "full/vectors/11101011-E-0004.bin"
private noncomputable def ep11101011_5 : Blocks := edgeBlocks% "full/vectors/11101011-E-0005.bin"
noncomputable def ep11101011 : Blocks := (Blocks.join (Blocks.join ep11101011_0 (Blocks.join ep11101011_1 ep11101011_2)) (Blocks.join ep11101011_3 (Blocks.join ep11101011_4 ep11101011_5)))
private theorem idp11101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1110101.list =
    C ((2:ℤ)^929) * horner X vp11101011.list + horner X ep11101011.list := by
  exact edge_identity (B := (2:ℤ)^1233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11101011 : Branch 1 (-7487761639/64000000 : ℚ) vp1110101 := by
  apply branch_checked idp11101011 (by positivity) (by decide +kernel)
  rw [show 2*(-7487761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7519761639/32000000 : ℚ) by norm_num]
  exact coverp11101011
theorem coverp1110101 : Covers (-7487761639/64000000 : ℚ) vp1110101 := join_branches bp11101010 bp11101011
private noncomputable def vp111010011_0 : Blocks := edgeBlocks% "full/vectors/111010011-V-0000.bin"
private noncomputable def vp111010011_1 : Blocks := edgeBlocks% "full/vectors/111010011-V-0001.bin"
noncomputable def vp111010011 : Blocks := (Blocks.join vp111010011_0 vp111010011_1)
theorem coverp111010011 : Covers (-7471761639/16000000 : ℚ) vp111010011 := cover_leaf (by decide +kernel)
private noncomputable def vp111010010_0 : Blocks := edgeBlocks% "full/vectors/111010010-V-0000.bin"
private noncomputable def vp111010010_1 : Blocks := edgeBlocks% "full/vectors/111010010-V-0001.bin"
noncomputable def vp111010010 : Blocks := (Blocks.join vp111010010_0 vp111010010_1)
theorem coverp111010010 : Covers (-7455761639/16000000 : ℚ) vp111010010 := cover_leaf (by decide +kernel)
private noncomputable def vp11101001_0 : Blocks := edgeBlocks% "full/vectors/11101001-V-0000.bin"
private noncomputable def vp11101001_1 : Blocks := edgeBlocks% "full/vectors/11101001-V-0001.bin"
private noncomputable def vp11101001_2 : Blocks := edgeBlocks% "full/vectors/11101001-V-0002.bin"
private noncomputable def vp11101001_3 : Blocks := edgeBlocks% "full/vectors/11101001-V-0003.bin"
noncomputable def vp11101001 : Blocks := (Blocks.join (Blocks.join vp11101001_0 vp11101001_1) (Blocks.join vp11101001_2 vp11101001_3))
private theorem bp111010010 : Branch 0 (-7455761639/32000000 : ℚ) vp11101001 := by
  apply branch_left_normalized (c:=vp111010010) (k:=0) (m:=204) (by decide +kernel)
  rw [show 2*(-7455761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7455761639/16000000 : ℚ) by norm_num]
  exact coverp111010010
private noncomputable def ep111010011_0 : Blocks := edgeBlocks% "full/vectors/111010011-E-0000.bin"
private noncomputable def ep111010011_1 : Blocks := edgeBlocks% "full/vectors/111010011-E-0001.bin"
private noncomputable def ep111010011_2 : Blocks := edgeBlocks% "full/vectors/111010011-E-0002.bin"
private noncomputable def ep111010011_3 : Blocks := edgeBlocks% "full/vectors/111010011-E-0003.bin"
noncomputable def ep111010011 : Blocks := (Blocks.join (Blocks.join ep111010011_0 ep111010011_1) (Blocks.join ep111010011_2 ep111010011_3))
private theorem idp111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11101001.list =
    C ((2:ℤ)^479) * horner X vp111010011.list + horner X ep111010011.list := by
  exact edge_identity (B := (2:ℤ)^684) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111010011 : Branch 1 (-7455761639/32000000 : ℚ) vp11101001 := by
  apply branch_checked idp111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-7455761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7471761639/16000000 : ℚ) by norm_num]
  exact coverp111010011
theorem coverp11101001 : Covers (-7455761639/32000000 : ℚ) vp11101001 := join_branches bp111010010 bp111010011
private noncomputable def vp111010001_0 : Blocks := edgeBlocks% "full/vectors/111010001-V-0000.bin"
private noncomputable def vp111010001_1 : Blocks := edgeBlocks% "full/vectors/111010001-V-0001.bin"
noncomputable def vp111010001 : Blocks := (Blocks.join vp111010001_0 vp111010001_1)
theorem coverp111010001 : Covers (-7439761639/16000000 : ℚ) vp111010001 := cover_leaf (by decide +kernel)
private noncomputable def vp111010000_0 : Blocks := edgeBlocks% "full/vectors/111010000-V-0000.bin"
private noncomputable def vp111010000_1 : Blocks := edgeBlocks% "full/vectors/111010000-V-0001.bin"
noncomputable def vp111010000 : Blocks := (Blocks.join vp111010000_0 vp111010000_1)
theorem coverp111010000 : Covers (-7423761639/16000000 : ℚ) vp111010000 := cover_leaf (by decide +kernel)
private noncomputable def vp11101000_0 : Blocks := edgeBlocks% "full/vectors/11101000-V-0000.bin"
private noncomputable def vp11101000_1 : Blocks := edgeBlocks% "full/vectors/11101000-V-0001.bin"
private noncomputable def vp11101000_2 : Blocks := edgeBlocks% "full/vectors/11101000-V-0002.bin"
private noncomputable def vp11101000_3 : Blocks := edgeBlocks% "full/vectors/11101000-V-0003.bin"
noncomputable def vp11101000 : Blocks := (Blocks.join (Blocks.join vp11101000_0 vp11101000_1) (Blocks.join vp11101000_2 vp11101000_3))
private theorem bp111010000 : Branch 0 (-7423761639/32000000 : ℚ) vp11101000 := by
  apply branch_left_normalized (c:=vp111010000) (k:=0) (m:=206) (by decide +kernel)
  rw [show 2*(-7423761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7423761639/16000000 : ℚ) by norm_num]
  exact coverp111010000
private noncomputable def ep111010001_0 : Blocks := edgeBlocks% "full/vectors/111010001-E-0000.bin"
private noncomputable def ep111010001_1 : Blocks := edgeBlocks% "full/vectors/111010001-E-0001.bin"
private noncomputable def ep111010001_2 : Blocks := edgeBlocks% "full/vectors/111010001-E-0002.bin"
private noncomputable def ep111010001_3 : Blocks := edgeBlocks% "full/vectors/111010001-E-0003.bin"
noncomputable def ep111010001 : Blocks := (Blocks.join (Blocks.join ep111010001_0 ep111010001_1) (Blocks.join ep111010001_2 ep111010001_3))
private theorem idp111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11101000.list =
    C ((2:ℤ)^481) * horner X vp111010001.list + horner X ep111010001.list := by
  exact edge_identity (B := (2:ℤ)^686) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111010001 : Branch 1 (-7423761639/32000000 : ℚ) vp11101000 := by
  apply branch_checked idp111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-7423761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7439761639/16000000 : ℚ) by norm_num]
  exact coverp111010001
theorem coverp11101000 : Covers (-7423761639/32000000 : ℚ) vp11101000 := join_branches bp111010000 bp111010001
private noncomputable def vp1110100_0 : Blocks := edgeBlocks% "full/vectors/1110100-V-0000.bin"
private noncomputable def vp1110100_1 : Blocks := edgeBlocks% "full/vectors/1110100-V-0001.bin"
private noncomputable def vp1110100_2 : Blocks := edgeBlocks% "full/vectors/1110100-V-0002.bin"
private noncomputable def vp1110100_3 : Blocks := edgeBlocks% "full/vectors/1110100-V-0003.bin"
private noncomputable def vp1110100_4 : Blocks := edgeBlocks% "full/vectors/1110100-V-0004.bin"
private noncomputable def vp1110100_5 : Blocks := edgeBlocks% "full/vectors/1110100-V-0005.bin"
noncomputable def vp1110100 : Blocks := (Blocks.join (Blocks.join vp1110100_0 (Blocks.join vp1110100_1 vp1110100_2)) (Blocks.join vp1110100_3 (Blocks.join vp1110100_4 vp1110100_5)))
private theorem bp11101000 : Branch 0 (-7423761639/64000000 : ℚ) vp1110100 := by
  apply branch_left_normalized (c:=vp11101000) (k:=0) (m:=387) (by decide +kernel)
  rw [show 2*(-7423761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7423761639/32000000 : ℚ) by norm_num]
  exact coverp11101000
private noncomputable def ep11101001_0 : Blocks := edgeBlocks% "full/vectors/11101001-E-0000.bin"
private noncomputable def ep11101001_1 : Blocks := edgeBlocks% "full/vectors/11101001-E-0001.bin"
private noncomputable def ep11101001_2 : Blocks := edgeBlocks% "full/vectors/11101001-E-0002.bin"
private noncomputable def ep11101001_3 : Blocks := edgeBlocks% "full/vectors/11101001-E-0003.bin"
private noncomputable def ep11101001_4 : Blocks := edgeBlocks% "full/vectors/11101001-E-0004.bin"
private noncomputable def ep11101001_5 : Blocks := edgeBlocks% "full/vectors/11101001-E-0005.bin"
noncomputable def ep11101001 : Blocks := (Blocks.join (Blocks.join ep11101001_0 (Blocks.join ep11101001_1 ep11101001_2)) (Blocks.join ep11101001_3 (Blocks.join ep11101001_4 ep11101001_5)))
private theorem idp11101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1110100.list =
    C ((2:ℤ)^933) * horner X vp11101001.list + horner X ep11101001.list := by
  exact edge_identity (B := (2:ℤ)^1238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11101001 : Branch 1 (-7423761639/64000000 : ℚ) vp1110100 := by
  apply branch_checked idp11101001 (by positivity) (by decide +kernel)
  rw [show 2*(-7423761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7455761639/32000000 : ℚ) by norm_num]
  exact coverp11101001
theorem coverp1110100 : Covers (-7423761639/64000000 : ℚ) vp1110100 := join_branches bp11101000 bp11101001
private noncomputable def vp111010_0 : Blocks := edgeBlocks% "full/vectors/111010-V-0000.bin"
private noncomputable def vp111010_1 : Blocks := edgeBlocks% "full/vectors/111010-V-0001.bin"
private noncomputable def vp111010_2 : Blocks := edgeBlocks% "full/vectors/111010-V-0002.bin"
private noncomputable def vp111010_3 : Blocks := edgeBlocks% "full/vectors/111010-V-0003.bin"
private noncomputable def vp111010_4 : Blocks := edgeBlocks% "full/vectors/111010-V-0004.bin"
private noncomputable def vp111010_5 : Blocks := edgeBlocks% "full/vectors/111010-V-0005.bin"
private noncomputable def vp111010_6 : Blocks := edgeBlocks% "full/vectors/111010-V-0006.bin"
private noncomputable def vp111010_7 : Blocks := edgeBlocks% "full/vectors/111010-V-0007.bin"
private noncomputable def vp111010_8 : Blocks := edgeBlocks% "full/vectors/111010-V-0008.bin"
private noncomputable def vp111010_9 : Blocks := edgeBlocks% "full/vectors/111010-V-0009.bin"
private noncomputable def vp111010_10 : Blocks := edgeBlocks% "full/vectors/111010-V-0010.bin"
private noncomputable def vp111010_11 : Blocks := edgeBlocks% "full/vectors/111010-V-0011.bin"
noncomputable def vp111010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp111010_0 (Blocks.join vp111010_1 vp111010_2)) (Blocks.join vp111010_3 (Blocks.join vp111010_4 vp111010_5))) (Blocks.join (Blocks.join vp111010_6 (Blocks.join vp111010_7 vp111010_8)) (Blocks.join vp111010_9 (Blocks.join vp111010_10 vp111010_11))))
private theorem bp1110100 : Branch 0 (-7423761639/128000000 : ℚ) vp111010 := by
  apply branch_left_normalized (c:=vp1110100) (k:=0) (m:=747) (by decide +kernel)
  rw [show 2*(-7423761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-7423761639/64000000 : ℚ) by norm_num]
  exact coverp1110100
private noncomputable def ep1110101_0 : Blocks := edgeBlocks% "full/vectors/1110101-E-0000.bin"
private noncomputable def ep1110101_1 : Blocks := edgeBlocks% "full/vectors/1110101-E-0001.bin"
private noncomputable def ep1110101_2 : Blocks := edgeBlocks% "full/vectors/1110101-E-0002.bin"
private noncomputable def ep1110101_3 : Blocks := edgeBlocks% "full/vectors/1110101-E-0003.bin"
private noncomputable def ep1110101_4 : Blocks := edgeBlocks% "full/vectors/1110101-E-0004.bin"
private noncomputable def ep1110101_5 : Blocks := edgeBlocks% "full/vectors/1110101-E-0005.bin"
private noncomputable def ep1110101_6 : Blocks := edgeBlocks% "full/vectors/1110101-E-0006.bin"
private noncomputable def ep1110101_7 : Blocks := edgeBlocks% "full/vectors/1110101-E-0007.bin"
private noncomputable def ep1110101_8 : Blocks := edgeBlocks% "full/vectors/1110101-E-0008.bin"
private noncomputable def ep1110101_9 : Blocks := edgeBlocks% "full/vectors/1110101-E-0009.bin"
private noncomputable def ep1110101_10 : Blocks := edgeBlocks% "full/vectors/1110101-E-0010.bin"
private noncomputable def ep1110101_11 : Blocks := edgeBlocks% "full/vectors/1110101-E-0011.bin"
noncomputable def ep1110101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1110101_0 (Blocks.join ep1110101_1 ep1110101_2)) (Blocks.join ep1110101_3 (Blocks.join ep1110101_4 ep1110101_5))) (Blocks.join (Blocks.join ep1110101_6 (Blocks.join ep1110101_7 ep1110101_8)) (Blocks.join ep1110101_9 (Blocks.join ep1110101_10 ep1110101_11))))
private theorem idp1110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp111010.list =
    C ((2:ℤ)^1823) * horner X vp1110101.list + horner X ep1110101.list := by
  exact edge_identity (B := (2:ℤ)^2326) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1110101 : Branch 1 (-7423761639/128000000 : ℚ) vp111010 := by
  apply branch_checked idp1110101 (by positivity) (by decide +kernel)
  rw [show 2*(-7423761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-7487761639/64000000 : ℚ) by norm_num]
  exact coverp1110101
theorem coverp111010 : Covers (-7423761639/128000000 : ℚ) vp111010 := join_branches bp1110100 bp1110101
private noncomputable def vp11101_0 : Blocks := edgeBlocks% "full/vectors/11101-V-0000.bin"
private noncomputable def vp11101_1 : Blocks := edgeBlocks% "full/vectors/11101-V-0001.bin"
private noncomputable def vp11101_2 : Blocks := edgeBlocks% "full/vectors/11101-V-0002.bin"
private noncomputable def vp11101_3 : Blocks := edgeBlocks% "full/vectors/11101-V-0003.bin"
private noncomputable def vp11101_4 : Blocks := edgeBlocks% "full/vectors/11101-V-0004.bin"
private noncomputable def vp11101_5 : Blocks := edgeBlocks% "full/vectors/11101-V-0005.bin"
private noncomputable def vp11101_6 : Blocks := edgeBlocks% "full/vectors/11101-V-0006.bin"
private noncomputable def vp11101_7 : Blocks := edgeBlocks% "full/vectors/11101-V-0007.bin"
private noncomputable def vp11101_8 : Blocks := edgeBlocks% "full/vectors/11101-V-0008.bin"
private noncomputable def vp11101_9 : Blocks := edgeBlocks% "full/vectors/11101-V-0009.bin"
private noncomputable def vp11101_10 : Blocks := edgeBlocks% "full/vectors/11101-V-0010.bin"
private noncomputable def vp11101_11 : Blocks := edgeBlocks% "full/vectors/11101-V-0011.bin"
private noncomputable def vp11101_12 : Blocks := edgeBlocks% "full/vectors/11101-V-0012.bin"
private noncomputable def vp11101_13 : Blocks := edgeBlocks% "full/vectors/11101-V-0013.bin"
private noncomputable def vp11101_14 : Blocks := edgeBlocks% "full/vectors/11101-V-0014.bin"
private noncomputable def vp11101_15 : Blocks := edgeBlocks% "full/vectors/11101-V-0015.bin"
private noncomputable def vp11101_16 : Blocks := edgeBlocks% "full/vectors/11101-V-0016.bin"
private noncomputable def vp11101_17 : Blocks := edgeBlocks% "full/vectors/11101-V-0017.bin"
private noncomputable def vp11101_18 : Blocks := edgeBlocks% "full/vectors/11101-V-0018.bin"
private noncomputable def vp11101_19 : Blocks := edgeBlocks% "full/vectors/11101-V-0019.bin"
private noncomputable def vp11101_20 : Blocks := edgeBlocks% "full/vectors/11101-V-0020.bin"
private noncomputable def vp11101_21 : Blocks := edgeBlocks% "full/vectors/11101-V-0021.bin"
private noncomputable def vp11101_22 : Blocks := edgeBlocks% "full/vectors/11101-V-0022.bin"
noncomputable def vp11101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp11101_0 vp11101_1) (Blocks.join vp11101_2 (Blocks.join vp11101_3 vp11101_4))) (Blocks.join (Blocks.join vp11101_5 (Blocks.join vp11101_6 vp11101_7)) (Blocks.join vp11101_8 (Blocks.join vp11101_9 vp11101_10)))) (Blocks.join (Blocks.join (Blocks.join vp11101_11 (Blocks.join vp11101_12 vp11101_13)) (Blocks.join vp11101_14 (Blocks.join vp11101_15 vp11101_16))) (Blocks.join (Blocks.join vp11101_17 (Blocks.join vp11101_18 vp11101_19)) (Blocks.join vp11101_20 (Blocks.join vp11101_21 vp11101_22)))))
private theorem bp111010 : Branch 0 (-7423761639/256000000 : ℚ) vp11101 := by
  apply branch_left_normalized (c:=vp111010) (k:=0) (m:=1452) (by decide +kernel)
  rw [show 2*(-7423761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-7423761639/128000000 : ℚ) by norm_num]
  exact coverp111010
private noncomputable def ep111011_0 : Blocks := edgeBlocks% "full/vectors/111011-E-0000.bin"
private noncomputable def ep111011_1 : Blocks := edgeBlocks% "full/vectors/111011-E-0001.bin"
private noncomputable def ep111011_2 : Blocks := edgeBlocks% "full/vectors/111011-E-0002.bin"
private noncomputable def ep111011_3 : Blocks := edgeBlocks% "full/vectors/111011-E-0003.bin"
private noncomputable def ep111011_4 : Blocks := edgeBlocks% "full/vectors/111011-E-0004.bin"
private noncomputable def ep111011_5 : Blocks := edgeBlocks% "full/vectors/111011-E-0005.bin"
private noncomputable def ep111011_6 : Blocks := edgeBlocks% "full/vectors/111011-E-0006.bin"
private noncomputable def ep111011_7 : Blocks := edgeBlocks% "full/vectors/111011-E-0007.bin"
private noncomputable def ep111011_8 : Blocks := edgeBlocks% "full/vectors/111011-E-0008.bin"
private noncomputable def ep111011_9 : Blocks := edgeBlocks% "full/vectors/111011-E-0009.bin"
private noncomputable def ep111011_10 : Blocks := edgeBlocks% "full/vectors/111011-E-0010.bin"
private noncomputable def ep111011_11 : Blocks := edgeBlocks% "full/vectors/111011-E-0011.bin"
private noncomputable def ep111011_12 : Blocks := edgeBlocks% "full/vectors/111011-E-0012.bin"
private noncomputable def ep111011_13 : Blocks := edgeBlocks% "full/vectors/111011-E-0013.bin"
private noncomputable def ep111011_14 : Blocks := edgeBlocks% "full/vectors/111011-E-0014.bin"
private noncomputable def ep111011_15 : Blocks := edgeBlocks% "full/vectors/111011-E-0015.bin"
private noncomputable def ep111011_16 : Blocks := edgeBlocks% "full/vectors/111011-E-0016.bin"
private noncomputable def ep111011_17 : Blocks := edgeBlocks% "full/vectors/111011-E-0017.bin"
private noncomputable def ep111011_18 : Blocks := edgeBlocks% "full/vectors/111011-E-0018.bin"
private noncomputable def ep111011_19 : Blocks := edgeBlocks% "full/vectors/111011-E-0019.bin"
private noncomputable def ep111011_20 : Blocks := edgeBlocks% "full/vectors/111011-E-0020.bin"
private noncomputable def ep111011_21 : Blocks := edgeBlocks% "full/vectors/111011-E-0021.bin"
private noncomputable def ep111011_22 : Blocks := edgeBlocks% "full/vectors/111011-E-0022.bin"
noncomputable def ep111011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep111011_0 ep111011_1) (Blocks.join ep111011_2 (Blocks.join ep111011_3 ep111011_4))) (Blocks.join (Blocks.join ep111011_5 (Blocks.join ep111011_6 ep111011_7)) (Blocks.join ep111011_8 (Blocks.join ep111011_9 ep111011_10)))) (Blocks.join (Blocks.join (Blocks.join ep111011_11 (Blocks.join ep111011_12 ep111011_13)) (Blocks.join ep111011_14 (Blocks.join ep111011_15 ep111011_16))) (Blocks.join (Blocks.join ep111011_17 (Blocks.join ep111011_18 ep111011_19)) (Blocks.join ep111011_20 (Blocks.join ep111011_21 ep111011_22)))))
private def ptsp111011 : List ℤ := [((2:ℤ)^4256+0),((2:ℤ)^4256+1)]
private theorem boundp111011 : 2^vp11101.size*absSum vp11101.list + ((2:ℤ)^3558*absSum vp111011.list+absSum ep111011.list) < (2:ℤ)^4450 := by decide +kernel
private theorem pointp111011_0 : fastHom 1 ((2:ℤ)^4256+0) vp11101 = ((2:ℤ)^3558)*vp111011.subst ((2:ℤ)^4256+0)+ep111011.subst ((2:ℤ)^4256+0) := by decide +kernel
private theorem pointp111011_1 : fastHom 1 ((2:ℤ)^4256+1) vp11101 = ((2:ℤ)^3558)*vp111011.subst ((2:ℤ)^4256+1)+ep111011.subst ((2:ℤ)^4256+1) := by decide +kernel
private theorem checkp111011 (x:ℤ) (hx:x ∈ ptsp111011) : fastHom 1 x vp11101 = ((2:ℤ)^3558)*vp111011.subst x+ep111011.subst x := by
  simp only [ptsp111011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp111011_0
  · exact pointp111011_1
private theorem idp111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11101.list =
    C ((2:ℤ)^3558) * horner X vp111011.list + horner X ep111011.list := by
  apply edge_identity (B := (2:ℤ)^4450) (by decide) (by positivity) (by positivity) boundp111011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp111011 (by decide +kernel)
  · have h : ptsp111011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp111011.trans_le (by decide +kernel)
  · exact checkp111011
private theorem bp111011 : Branch 1 (-7423761639/256000000 : ℚ) vp11101 := by
  apply branch_checked idp111011 (by positivity) (by decide +kernel)
  rw [show 2*(-7423761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-7551761639/128000000 : ℚ) by norm_num]
  exact coverp111011
theorem coverp11101 : Covers (-7423761639/256000000 : ℚ) vp11101 := join_branches bp111010 bp111011
private noncomputable def vp111001111_0 : Blocks := edgeBlocks% "full/vectors/111001111-V-0000.bin"
private noncomputable def vp111001111_1 : Blocks := edgeBlocks% "full/vectors/111001111-V-0001.bin"
noncomputable def vp111001111 : Blocks := (Blocks.join vp111001111_0 vp111001111_1)
theorem coverp111001111 : Covers (-7407761639/16000000 : ℚ) vp111001111 := cover_leaf (by decide +kernel)
private noncomputable def vp111001110_0 : Blocks := edgeBlocks% "full/vectors/111001110-V-0000.bin"
private noncomputable def vp111001110_1 : Blocks := edgeBlocks% "full/vectors/111001110-V-0001.bin"
noncomputable def vp111001110 : Blocks := (Blocks.join vp111001110_0 vp111001110_1)
theorem coverp111001110 : Covers (-7391761639/16000000 : ℚ) vp111001110 := cover_leaf (by decide +kernel)
private noncomputable def vp11100111_0 : Blocks := edgeBlocks% "full/vectors/11100111-V-0000.bin"
private noncomputable def vp11100111_1 : Blocks := edgeBlocks% "full/vectors/11100111-V-0001.bin"
private noncomputable def vp11100111_2 : Blocks := edgeBlocks% "full/vectors/11100111-V-0002.bin"
private noncomputable def vp11100111_3 : Blocks := edgeBlocks% "full/vectors/11100111-V-0003.bin"
noncomputable def vp11100111 : Blocks := (Blocks.join (Blocks.join vp11100111_0 vp11100111_1) (Blocks.join vp11100111_2 vp11100111_3))
private theorem bp111001110 : Branch 0 (-7391761639/32000000 : ℚ) vp11100111 := by
  apply branch_left_normalized (c:=vp111001110) (k:=0) (m:=206) (by decide +kernel)
  rw [show 2*(-7391761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7391761639/16000000 : ℚ) by norm_num]
  exact coverp111001110
private noncomputable def ep111001111_0 : Blocks := edgeBlocks% "full/vectors/111001111-E-0000.bin"
private noncomputable def ep111001111_1 : Blocks := edgeBlocks% "full/vectors/111001111-E-0001.bin"
private noncomputable def ep111001111_2 : Blocks := edgeBlocks% "full/vectors/111001111-E-0002.bin"
private noncomputable def ep111001111_3 : Blocks := edgeBlocks% "full/vectors/111001111-E-0003.bin"
noncomputable def ep111001111 : Blocks := (Blocks.join (Blocks.join ep111001111_0 ep111001111_1) (Blocks.join ep111001111_2 ep111001111_3))
private theorem idp111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11100111.list =
    C ((2:ℤ)^481) * horner X vp111001111.list + horner X ep111001111.list := by
  exact edge_identity (B := (2:ℤ)^686) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111001111 : Branch 1 (-7391761639/32000000 : ℚ) vp11100111 := by
  apply branch_checked idp111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-7391761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7407761639/16000000 : ℚ) by norm_num]
  exact coverp111001111
theorem coverp11100111 : Covers (-7391761639/32000000 : ℚ) vp11100111 := join_branches bp111001110 bp111001111
private noncomputable def vp111001101_0 : Blocks := edgeBlocks% "full/vectors/111001101-V-0000.bin"
private noncomputable def vp111001101_1 : Blocks := edgeBlocks% "full/vectors/111001101-V-0001.bin"
noncomputable def vp111001101 : Blocks := (Blocks.join vp111001101_0 vp111001101_1)
theorem coverp111001101 : Covers (-7375761639/16000000 : ℚ) vp111001101 := cover_leaf (by decide +kernel)
private noncomputable def vp111001100_0 : Blocks := edgeBlocks% "full/vectors/111001100-V-0000.bin"
private noncomputable def vp111001100_1 : Blocks := edgeBlocks% "full/vectors/111001100-V-0001.bin"
noncomputable def vp111001100 : Blocks := (Blocks.join vp111001100_0 vp111001100_1)
theorem coverp111001100 : Covers (-7359761639/16000000 : ℚ) vp111001100 := cover_leaf (by decide +kernel)
private noncomputable def vp11100110_0 : Blocks := edgeBlocks% "full/vectors/11100110-V-0000.bin"
private noncomputable def vp11100110_1 : Blocks := edgeBlocks% "full/vectors/11100110-V-0001.bin"
private noncomputable def vp11100110_2 : Blocks := edgeBlocks% "full/vectors/11100110-V-0002.bin"
private noncomputable def vp11100110_3 : Blocks := edgeBlocks% "full/vectors/11100110-V-0003.bin"
noncomputable def vp11100110 : Blocks := (Blocks.join (Blocks.join vp11100110_0 vp11100110_1) (Blocks.join vp11100110_2 vp11100110_3))
private theorem bp111001100 : Branch 0 (-7359761639/32000000 : ℚ) vp11100110 := by
  apply branch_left_normalized (c:=vp111001100) (k:=0) (m:=206) (by decide +kernel)
  rw [show 2*(-7359761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7359761639/16000000 : ℚ) by norm_num]
  exact coverp111001100
private noncomputable def ep111001101_0 : Blocks := edgeBlocks% "full/vectors/111001101-E-0000.bin"
private noncomputable def ep111001101_1 : Blocks := edgeBlocks% "full/vectors/111001101-E-0001.bin"
private noncomputable def ep111001101_2 : Blocks := edgeBlocks% "full/vectors/111001101-E-0002.bin"
private noncomputable def ep111001101_3 : Blocks := edgeBlocks% "full/vectors/111001101-E-0003.bin"
noncomputable def ep111001101 : Blocks := (Blocks.join (Blocks.join ep111001101_0 ep111001101_1) (Blocks.join ep111001101_2 ep111001101_3))
private theorem idp111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11100110.list =
    C ((2:ℤ)^481) * horner X vp111001101.list + horner X ep111001101.list := by
  exact edge_identity (B := (2:ℤ)^687) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111001101 : Branch 1 (-7359761639/32000000 : ℚ) vp11100110 := by
  apply branch_checked idp111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-7359761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7375761639/16000000 : ℚ) by norm_num]
  exact coverp111001101
theorem coverp11100110 : Covers (-7359761639/32000000 : ℚ) vp11100110 := join_branches bp111001100 bp111001101
private noncomputable def vp1110011_0 : Blocks := edgeBlocks% "full/vectors/1110011-V-0000.bin"
private noncomputable def vp1110011_1 : Blocks := edgeBlocks% "full/vectors/1110011-V-0001.bin"
private noncomputable def vp1110011_2 : Blocks := edgeBlocks% "full/vectors/1110011-V-0002.bin"
private noncomputable def vp1110011_3 : Blocks := edgeBlocks% "full/vectors/1110011-V-0003.bin"
private noncomputable def vp1110011_4 : Blocks := edgeBlocks% "full/vectors/1110011-V-0004.bin"
private noncomputable def vp1110011_5 : Blocks := edgeBlocks% "full/vectors/1110011-V-0005.bin"
noncomputable def vp1110011 : Blocks := (Blocks.join (Blocks.join vp1110011_0 (Blocks.join vp1110011_1 vp1110011_2)) (Blocks.join vp1110011_3 (Blocks.join vp1110011_4 vp1110011_5)))
private theorem bp11100110 : Branch 0 (-7359761639/64000000 : ℚ) vp1110011 := by
  apply branch_left_normalized (c:=vp11100110) (k:=0) (m:=388) (by decide +kernel)
  rw [show 2*(-7359761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7359761639/32000000 : ℚ) by norm_num]
  exact coverp11100110
private noncomputable def ep11100111_0 : Blocks := edgeBlocks% "full/vectors/11100111-E-0000.bin"
private noncomputable def ep11100111_1 : Blocks := edgeBlocks% "full/vectors/11100111-E-0001.bin"
private noncomputable def ep11100111_2 : Blocks := edgeBlocks% "full/vectors/11100111-E-0002.bin"
private noncomputable def ep11100111_3 : Blocks := edgeBlocks% "full/vectors/11100111-E-0003.bin"
private noncomputable def ep11100111_4 : Blocks := edgeBlocks% "full/vectors/11100111-E-0004.bin"
private noncomputable def ep11100111_5 : Blocks := edgeBlocks% "full/vectors/11100111-E-0005.bin"
noncomputable def ep11100111 : Blocks := (Blocks.join (Blocks.join ep11100111_0 (Blocks.join ep11100111_1 ep11100111_2)) (Blocks.join ep11100111_3 (Blocks.join ep11100111_4 ep11100111_5)))
private theorem idp11100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1110011.list =
    C ((2:ℤ)^936) * horner X vp11100111.list + horner X ep11100111.list := by
  exact edge_identity (B := (2:ℤ)^1242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11100111 : Branch 1 (-7359761639/64000000 : ℚ) vp1110011 := by
  apply branch_checked idp11100111 (by positivity) (by decide +kernel)
  rw [show 2*(-7359761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7391761639/32000000 : ℚ) by norm_num]
  exact coverp11100111
theorem coverp1110011 : Covers (-7359761639/64000000 : ℚ) vp1110011 := join_branches bp11100110 bp11100111
private noncomputable def vp111001011_0 : Blocks := edgeBlocks% "full/vectors/111001011-V-0000.bin"
private noncomputable def vp111001011_1 : Blocks := edgeBlocks% "full/vectors/111001011-V-0001.bin"
noncomputable def vp111001011 : Blocks := (Blocks.join vp111001011_0 vp111001011_1)
theorem coverp111001011 : Covers (-7343761639/16000000 : ℚ) vp111001011 := cover_leaf (by decide +kernel)
private noncomputable def vp111001010_0 : Blocks := edgeBlocks% "full/vectors/111001010-V-0000.bin"
private noncomputable def vp111001010_1 : Blocks := edgeBlocks% "full/vectors/111001010-V-0001.bin"
noncomputable def vp111001010 : Blocks := (Blocks.join vp111001010_0 vp111001010_1)
theorem coverp111001010 : Covers (-7327761639/16000000 : ℚ) vp111001010 := cover_leaf (by decide +kernel)
private noncomputable def vp11100101_0 : Blocks := edgeBlocks% "full/vectors/11100101-V-0000.bin"
private noncomputable def vp11100101_1 : Blocks := edgeBlocks% "full/vectors/11100101-V-0001.bin"
private noncomputable def vp11100101_2 : Blocks := edgeBlocks% "full/vectors/11100101-V-0002.bin"
private noncomputable def vp11100101_3 : Blocks := edgeBlocks% "full/vectors/11100101-V-0003.bin"
noncomputable def vp11100101 : Blocks := (Blocks.join (Blocks.join vp11100101_0 vp11100101_1) (Blocks.join vp11100101_2 vp11100101_3))
private theorem bp111001010 : Branch 0 (-7327761639/32000000 : ℚ) vp11100101 := by
  apply branch_left_normalized (c:=vp111001010) (k:=0) (m:=207) (by decide +kernel)
  rw [show 2*(-7327761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7327761639/16000000 : ℚ) by norm_num]
  exact coverp111001010
private noncomputable def ep111001011_0 : Blocks := edgeBlocks% "full/vectors/111001011-E-0000.bin"
private noncomputable def ep111001011_1 : Blocks := edgeBlocks% "full/vectors/111001011-E-0001.bin"
private noncomputable def ep111001011_2 : Blocks := edgeBlocks% "full/vectors/111001011-E-0002.bin"
private noncomputable def ep111001011_3 : Blocks := edgeBlocks% "full/vectors/111001011-E-0003.bin"
noncomputable def ep111001011 : Blocks := (Blocks.join (Blocks.join ep111001011_0 ep111001011_1) (Blocks.join ep111001011_2 ep111001011_3))
private theorem idp111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11100101.list =
    C ((2:ℤ)^482) * horner X vp111001011.list + horner X ep111001011.list := by
  exact edge_identity (B := (2:ℤ)^688) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111001011 : Branch 1 (-7327761639/32000000 : ℚ) vp11100101 := by
  apply branch_checked idp111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-7327761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7343761639/16000000 : ℚ) by norm_num]
  exact coverp111001011
theorem coverp11100101 : Covers (-7327761639/32000000 : ℚ) vp11100101 := join_branches bp111001010 bp111001011
private noncomputable def vp111001001_0 : Blocks := edgeBlocks% "full/vectors/111001001-V-0000.bin"
private noncomputable def vp111001001_1 : Blocks := edgeBlocks% "full/vectors/111001001-V-0001.bin"
noncomputable def vp111001001 : Blocks := (Blocks.join vp111001001_0 vp111001001_1)
theorem coverp111001001 : Covers (-7311761639/16000000 : ℚ) vp111001001 := cover_leaf (by decide +kernel)
private noncomputable def vp111001000_0 : Blocks := edgeBlocks% "full/vectors/111001000-V-0000.bin"
private noncomputable def vp111001000_1 : Blocks := edgeBlocks% "full/vectors/111001000-V-0001.bin"
noncomputable def vp111001000 : Blocks := (Blocks.join vp111001000_0 vp111001000_1)
theorem coverp111001000 : Covers (-7295761639/16000000 : ℚ) vp111001000 := cover_leaf (by decide +kernel)
private noncomputable def vp11100100_0 : Blocks := edgeBlocks% "full/vectors/11100100-V-0000.bin"
private noncomputable def vp11100100_1 : Blocks := edgeBlocks% "full/vectors/11100100-V-0001.bin"
private noncomputable def vp11100100_2 : Blocks := edgeBlocks% "full/vectors/11100100-V-0002.bin"
private noncomputable def vp11100100_3 : Blocks := edgeBlocks% "full/vectors/11100100-V-0003.bin"
noncomputable def vp11100100 : Blocks := (Blocks.join (Blocks.join vp11100100_0 vp11100100_1) (Blocks.join vp11100100_2 vp11100100_3))
private theorem bp111001000 : Branch 0 (-7295761639/32000000 : ℚ) vp11100100 := by
  apply branch_left_normalized (c:=vp111001000) (k:=0) (m:=207) (by decide +kernel)
  rw [show 2*(-7295761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7295761639/16000000 : ℚ) by norm_num]
  exact coverp111001000
private noncomputable def ep111001001_0 : Blocks := edgeBlocks% "full/vectors/111001001-E-0000.bin"
private noncomputable def ep111001001_1 : Blocks := edgeBlocks% "full/vectors/111001001-E-0001.bin"
private noncomputable def ep111001001_2 : Blocks := edgeBlocks% "full/vectors/111001001-E-0002.bin"
private noncomputable def ep111001001_3 : Blocks := edgeBlocks% "full/vectors/111001001-E-0003.bin"
noncomputable def ep111001001 : Blocks := (Blocks.join (Blocks.join ep111001001_0 ep111001001_1) (Blocks.join ep111001001_2 ep111001001_3))
private theorem idp111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11100100.list =
    C ((2:ℤ)^483) * horner X vp111001001.list + horner X ep111001001.list := by
  exact edge_identity (B := (2:ℤ)^689) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111001001 : Branch 1 (-7295761639/32000000 : ℚ) vp11100100 := by
  apply branch_checked idp111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-7295761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7311761639/16000000 : ℚ) by norm_num]
  exact coverp111001001
theorem coverp11100100 : Covers (-7295761639/32000000 : ℚ) vp11100100 := join_branches bp111001000 bp111001001
private noncomputable def vp1110010_0 : Blocks := edgeBlocks% "full/vectors/1110010-V-0000.bin"
private noncomputable def vp1110010_1 : Blocks := edgeBlocks% "full/vectors/1110010-V-0001.bin"
private noncomputable def vp1110010_2 : Blocks := edgeBlocks% "full/vectors/1110010-V-0002.bin"
private noncomputable def vp1110010_3 : Blocks := edgeBlocks% "full/vectors/1110010-V-0003.bin"
private noncomputable def vp1110010_4 : Blocks := edgeBlocks% "full/vectors/1110010-V-0004.bin"
private noncomputable def vp1110010_5 : Blocks := edgeBlocks% "full/vectors/1110010-V-0005.bin"
noncomputable def vp1110010 : Blocks := (Blocks.join (Blocks.join vp1110010_0 (Blocks.join vp1110010_1 vp1110010_2)) (Blocks.join vp1110010_3 (Blocks.join vp1110010_4 vp1110010_5)))
private theorem bp11100100 : Branch 0 (-7295761639/64000000 : ℚ) vp1110010 := by
  apply branch_left_normalized (c:=vp11100100) (k:=0) (m:=390) (by decide +kernel)
  rw [show 2*(-7295761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7295761639/32000000 : ℚ) by norm_num]
  exact coverp11100100
private noncomputable def ep11100101_0 : Blocks := edgeBlocks% "full/vectors/11100101-E-0000.bin"
private noncomputable def ep11100101_1 : Blocks := edgeBlocks% "full/vectors/11100101-E-0001.bin"
private noncomputable def ep11100101_2 : Blocks := edgeBlocks% "full/vectors/11100101-E-0002.bin"
private noncomputable def ep11100101_3 : Blocks := edgeBlocks% "full/vectors/11100101-E-0003.bin"
private noncomputable def ep11100101_4 : Blocks := edgeBlocks% "full/vectors/11100101-E-0004.bin"
private noncomputable def ep11100101_5 : Blocks := edgeBlocks% "full/vectors/11100101-E-0005.bin"
noncomputable def ep11100101 : Blocks := (Blocks.join (Blocks.join ep11100101_0 (Blocks.join ep11100101_1 ep11100101_2)) (Blocks.join ep11100101_3 (Blocks.join ep11100101_4 ep11100101_5)))
private theorem idp11100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1110010.list =
    C ((2:ℤ)^938) * horner X vp11100101.list + horner X ep11100101.list := by
  exact edge_identity (B := (2:ℤ)^1246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11100101 : Branch 1 (-7295761639/64000000 : ℚ) vp1110010 := by
  apply branch_checked idp11100101 (by positivity) (by decide +kernel)
  rw [show 2*(-7295761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7327761639/32000000 : ℚ) by norm_num]
  exact coverp11100101
theorem coverp1110010 : Covers (-7295761639/64000000 : ℚ) vp1110010 := join_branches bp11100100 bp11100101
private noncomputable def vp111001_0 : Blocks := edgeBlocks% "full/vectors/111001-V-0000.bin"
private noncomputable def vp111001_1 : Blocks := edgeBlocks% "full/vectors/111001-V-0001.bin"
private noncomputable def vp111001_2 : Blocks := edgeBlocks% "full/vectors/111001-V-0002.bin"
private noncomputable def vp111001_3 : Blocks := edgeBlocks% "full/vectors/111001-V-0003.bin"
private noncomputable def vp111001_4 : Blocks := edgeBlocks% "full/vectors/111001-V-0004.bin"
private noncomputable def vp111001_5 : Blocks := edgeBlocks% "full/vectors/111001-V-0005.bin"
private noncomputable def vp111001_6 : Blocks := edgeBlocks% "full/vectors/111001-V-0006.bin"
private noncomputable def vp111001_7 : Blocks := edgeBlocks% "full/vectors/111001-V-0007.bin"
private noncomputable def vp111001_8 : Blocks := edgeBlocks% "full/vectors/111001-V-0008.bin"
private noncomputable def vp111001_9 : Blocks := edgeBlocks% "full/vectors/111001-V-0009.bin"
private noncomputable def vp111001_10 : Blocks := edgeBlocks% "full/vectors/111001-V-0010.bin"
private noncomputable def vp111001_11 : Blocks := edgeBlocks% "full/vectors/111001-V-0011.bin"
noncomputable def vp111001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp111001_0 (Blocks.join vp111001_1 vp111001_2)) (Blocks.join vp111001_3 (Blocks.join vp111001_4 vp111001_5))) (Blocks.join (Blocks.join vp111001_6 (Blocks.join vp111001_7 vp111001_8)) (Blocks.join vp111001_9 (Blocks.join vp111001_10 vp111001_11))))
private theorem bp1110010 : Branch 0 (-7295761639/128000000 : ℚ) vp111001 := by
  apply branch_left_normalized (c:=vp1110010) (k:=0) (m:=752) (by decide +kernel)
  rw [show 2*(-7295761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-7295761639/64000000 : ℚ) by norm_num]
  exact coverp1110010
private noncomputable def ep1110011_0 : Blocks := edgeBlocks% "full/vectors/1110011-E-0000.bin"
private noncomputable def ep1110011_1 : Blocks := edgeBlocks% "full/vectors/1110011-E-0001.bin"
private noncomputable def ep1110011_2 : Blocks := edgeBlocks% "full/vectors/1110011-E-0002.bin"
private noncomputable def ep1110011_3 : Blocks := edgeBlocks% "full/vectors/1110011-E-0003.bin"
private noncomputable def ep1110011_4 : Blocks := edgeBlocks% "full/vectors/1110011-E-0004.bin"
private noncomputable def ep1110011_5 : Blocks := edgeBlocks% "full/vectors/1110011-E-0005.bin"
private noncomputable def ep1110011_6 : Blocks := edgeBlocks% "full/vectors/1110011-E-0006.bin"
private noncomputable def ep1110011_7 : Blocks := edgeBlocks% "full/vectors/1110011-E-0007.bin"
private noncomputable def ep1110011_8 : Blocks := edgeBlocks% "full/vectors/1110011-E-0008.bin"
private noncomputable def ep1110011_9 : Blocks := edgeBlocks% "full/vectors/1110011-E-0009.bin"
private noncomputable def ep1110011_10 : Blocks := edgeBlocks% "full/vectors/1110011-E-0010.bin"
private noncomputable def ep1110011_11 : Blocks := edgeBlocks% "full/vectors/1110011-E-0011.bin"
noncomputable def ep1110011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1110011_0 (Blocks.join ep1110011_1 ep1110011_2)) (Blocks.join ep1110011_3 (Blocks.join ep1110011_4 ep1110011_5))) (Blocks.join (Blocks.join ep1110011_6 (Blocks.join ep1110011_7 ep1110011_8)) (Blocks.join ep1110011_9 (Blocks.join ep1110011_10 ep1110011_11))))
private theorem idp1110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp111001.list =
    C ((2:ℤ)^1834) * horner X vp1110011.list + horner X ep1110011.list := by
  exact edge_identity (B := (2:ℤ)^2344) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1110011 : Branch 1 (-7295761639/128000000 : ℚ) vp111001 := by
  apply branch_checked idp1110011 (by positivity) (by decide +kernel)
  rw [show 2*(-7295761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-7359761639/64000000 : ℚ) by norm_num]
  exact coverp1110011
theorem coverp111001 : Covers (-7295761639/128000000 : ℚ) vp111001 := join_branches bp1110010 bp1110011
private noncomputable def vp111000111_0 : Blocks := edgeBlocks% "full/vectors/111000111-V-0000.bin"
private noncomputable def vp111000111_1 : Blocks := edgeBlocks% "full/vectors/111000111-V-0001.bin"
noncomputable def vp111000111 : Blocks := (Blocks.join vp111000111_0 vp111000111_1)
theorem coverp111000111 : Covers (-7279761639/16000000 : ℚ) vp111000111 := cover_leaf (by decide +kernel)
private noncomputable def vp111000110_0 : Blocks := edgeBlocks% "full/vectors/111000110-V-0000.bin"
private noncomputable def vp111000110_1 : Blocks := edgeBlocks% "full/vectors/111000110-V-0001.bin"
noncomputable def vp111000110 : Blocks := (Blocks.join vp111000110_0 vp111000110_1)
theorem coverp111000110 : Covers (-7263761639/16000000 : ℚ) vp111000110 := cover_leaf (by decide +kernel)
private noncomputable def vp11100011_0 : Blocks := edgeBlocks% "full/vectors/11100011-V-0000.bin"
private noncomputable def vp11100011_1 : Blocks := edgeBlocks% "full/vectors/11100011-V-0001.bin"
private noncomputable def vp11100011_2 : Blocks := edgeBlocks% "full/vectors/11100011-V-0002.bin"
private noncomputable def vp11100011_3 : Blocks := edgeBlocks% "full/vectors/11100011-V-0003.bin"
noncomputable def vp11100011 : Blocks := (Blocks.join (Blocks.join vp11100011_0 vp11100011_1) (Blocks.join vp11100011_2 vp11100011_3))
private theorem bp111000110 : Branch 0 (-7263761639/32000000 : ℚ) vp11100011 := by
  apply branch_left_normalized (c:=vp111000110) (k:=0) (m:=207) (by decide +kernel)
  rw [show 2*(-7263761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7263761639/16000000 : ℚ) by norm_num]
  exact coverp111000110
private noncomputable def ep111000111_0 : Blocks := edgeBlocks% "full/vectors/111000111-E-0000.bin"
private noncomputable def ep111000111_1 : Blocks := edgeBlocks% "full/vectors/111000111-E-0001.bin"
private noncomputable def ep111000111_2 : Blocks := edgeBlocks% "full/vectors/111000111-E-0002.bin"
private noncomputable def ep111000111_3 : Blocks := edgeBlocks% "full/vectors/111000111-E-0003.bin"
noncomputable def ep111000111 : Blocks := (Blocks.join (Blocks.join ep111000111_0 ep111000111_1) (Blocks.join ep111000111_2 ep111000111_3))
private theorem idp111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11100011.list =
    C ((2:ℤ)^484) * horner X vp111000111.list + horner X ep111000111.list := by
  exact edge_identity (B := (2:ℤ)^690) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111000111 : Branch 1 (-7263761639/32000000 : ℚ) vp11100011 := by
  apply branch_checked idp111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-7263761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7279761639/16000000 : ℚ) by norm_num]
  exact coverp111000111
theorem coverp11100011 : Covers (-7263761639/32000000 : ℚ) vp11100011 := join_branches bp111000110 bp111000111
private noncomputable def vp111000101_0 : Blocks := edgeBlocks% "full/vectors/111000101-V-0000.bin"
private noncomputable def vp111000101_1 : Blocks := edgeBlocks% "full/vectors/111000101-V-0001.bin"
noncomputable def vp111000101 : Blocks := (Blocks.join vp111000101_0 vp111000101_1)
theorem coverp111000101 : Covers (-7247761639/16000000 : ℚ) vp111000101 := cover_leaf (by decide +kernel)
private noncomputable def vp111000100_0 : Blocks := edgeBlocks% "full/vectors/111000100-V-0000.bin"
private noncomputable def vp111000100_1 : Blocks := edgeBlocks% "full/vectors/111000100-V-0001.bin"
noncomputable def vp111000100 : Blocks := (Blocks.join vp111000100_0 vp111000100_1)
theorem coverp111000100 : Covers (-7231761639/16000000 : ℚ) vp111000100 := cover_leaf (by decide +kernel)
private noncomputable def vp11100010_0 : Blocks := edgeBlocks% "full/vectors/11100010-V-0000.bin"
private noncomputable def vp11100010_1 : Blocks := edgeBlocks% "full/vectors/11100010-V-0001.bin"
private noncomputable def vp11100010_2 : Blocks := edgeBlocks% "full/vectors/11100010-V-0002.bin"
private noncomputable def vp11100010_3 : Blocks := edgeBlocks% "full/vectors/11100010-V-0003.bin"
noncomputable def vp11100010 : Blocks := (Blocks.join (Blocks.join vp11100010_0 vp11100010_1) (Blocks.join vp11100010_2 vp11100010_3))
private theorem bp111000100 : Branch 0 (-7231761639/32000000 : ℚ) vp11100010 := by
  apply branch_left_normalized (c:=vp111000100) (k:=0) (m:=208) (by decide +kernel)
  rw [show 2*(-7231761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7231761639/16000000 : ℚ) by norm_num]
  exact coverp111000100
private noncomputable def ep111000101_0 : Blocks := edgeBlocks% "full/vectors/111000101-E-0000.bin"
private noncomputable def ep111000101_1 : Blocks := edgeBlocks% "full/vectors/111000101-E-0001.bin"
private noncomputable def ep111000101_2 : Blocks := edgeBlocks% "full/vectors/111000101-E-0002.bin"
private noncomputable def ep111000101_3 : Blocks := edgeBlocks% "full/vectors/111000101-E-0003.bin"
noncomputable def ep111000101 : Blocks := (Blocks.join (Blocks.join ep111000101_0 ep111000101_1) (Blocks.join ep111000101_2 ep111000101_3))
private theorem idp111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11100010.list =
    C ((2:ℤ)^485) * horner X vp111000101.list + horner X ep111000101.list := by
  exact edge_identity (B := (2:ℤ)^692) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111000101 : Branch 1 (-7231761639/32000000 : ℚ) vp11100010 := by
  apply branch_checked idp111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-7231761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7247761639/16000000 : ℚ) by norm_num]
  exact coverp111000101
theorem coverp11100010 : Covers (-7231761639/32000000 : ℚ) vp11100010 := join_branches bp111000100 bp111000101
private noncomputable def vp1110001_0 : Blocks := edgeBlocks% "full/vectors/1110001-V-0000.bin"
private noncomputable def vp1110001_1 : Blocks := edgeBlocks% "full/vectors/1110001-V-0001.bin"
private noncomputable def vp1110001_2 : Blocks := edgeBlocks% "full/vectors/1110001-V-0002.bin"
private noncomputable def vp1110001_3 : Blocks := edgeBlocks% "full/vectors/1110001-V-0003.bin"
private noncomputable def vp1110001_4 : Blocks := edgeBlocks% "full/vectors/1110001-V-0004.bin"
private noncomputable def vp1110001_5 : Blocks := edgeBlocks% "full/vectors/1110001-V-0005.bin"
noncomputable def vp1110001 : Blocks := (Blocks.join (Blocks.join vp1110001_0 (Blocks.join vp1110001_1 vp1110001_2)) (Blocks.join vp1110001_3 (Blocks.join vp1110001_4 vp1110001_5)))
private theorem bp11100010 : Branch 0 (-7231761639/64000000 : ℚ) vp1110001 := by
  apply branch_left_normalized (c:=vp11100010) (k:=0) (m:=392) (by decide +kernel)
  rw [show 2*(-7231761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7231761639/32000000 : ℚ) by norm_num]
  exact coverp11100010
private noncomputable def ep11100011_0 : Blocks := edgeBlocks% "full/vectors/11100011-E-0000.bin"
private noncomputable def ep11100011_1 : Blocks := edgeBlocks% "full/vectors/11100011-E-0001.bin"
private noncomputable def ep11100011_2 : Blocks := edgeBlocks% "full/vectors/11100011-E-0002.bin"
private noncomputable def ep11100011_3 : Blocks := edgeBlocks% "full/vectors/11100011-E-0003.bin"
private noncomputable def ep11100011_4 : Blocks := edgeBlocks% "full/vectors/11100011-E-0004.bin"
private noncomputable def ep11100011_5 : Blocks := edgeBlocks% "full/vectors/11100011-E-0005.bin"
noncomputable def ep11100011 : Blocks := (Blocks.join (Blocks.join ep11100011_0 (Blocks.join ep11100011_1 ep11100011_2)) (Blocks.join ep11100011_3 (Blocks.join ep11100011_4 ep11100011_5)))
private theorem idp11100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1110001.list =
    C ((2:ℤ)^941) * horner X vp11100011.list + horner X ep11100011.list := by
  exact edge_identity (B := (2:ℤ)^1251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11100011 : Branch 1 (-7231761639/64000000 : ℚ) vp1110001 := by
  apply branch_checked idp11100011 (by positivity) (by decide +kernel)
  rw [show 2*(-7231761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7263761639/32000000 : ℚ) by norm_num]
  exact coverp11100011
theorem coverp1110001 : Covers (-7231761639/64000000 : ℚ) vp1110001 := join_branches bp11100010 bp11100011
private noncomputable def vp111000011_0 : Blocks := edgeBlocks% "full/vectors/111000011-V-0000.bin"
private noncomputable def vp111000011_1 : Blocks := edgeBlocks% "full/vectors/111000011-V-0001.bin"
noncomputable def vp111000011 : Blocks := (Blocks.join vp111000011_0 vp111000011_1)
theorem coverp111000011 : Covers (-7215761639/16000000 : ℚ) vp111000011 := cover_leaf (by decide +kernel)
private noncomputable def vp111000010_0 : Blocks := edgeBlocks% "full/vectors/111000010-V-0000.bin"
private noncomputable def vp111000010_1 : Blocks := edgeBlocks% "full/vectors/111000010-V-0001.bin"
noncomputable def vp111000010 : Blocks := (Blocks.join vp111000010_0 vp111000010_1)
theorem coverp111000010 : Covers (-7199761639/16000000 : ℚ) vp111000010 := cover_leaf (by decide +kernel)
private noncomputable def vp11100001_0 : Blocks := edgeBlocks% "full/vectors/11100001-V-0000.bin"
private noncomputable def vp11100001_1 : Blocks := edgeBlocks% "full/vectors/11100001-V-0001.bin"
private noncomputable def vp11100001_2 : Blocks := edgeBlocks% "full/vectors/11100001-V-0002.bin"
private noncomputable def vp11100001_3 : Blocks := edgeBlocks% "full/vectors/11100001-V-0003.bin"
noncomputable def vp11100001 : Blocks := (Blocks.join (Blocks.join vp11100001_0 vp11100001_1) (Blocks.join vp11100001_2 vp11100001_3))
private theorem bp111000010 : Branch 0 (-7199761639/32000000 : ℚ) vp11100001 := by
  apply branch_left_normalized (c:=vp111000010) (k:=0) (m:=208) (by decide +kernel)
  rw [show 2*(-7199761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7199761639/16000000 : ℚ) by norm_num]
  exact coverp111000010
private noncomputable def ep111000011_0 : Blocks := edgeBlocks% "full/vectors/111000011-E-0000.bin"
private noncomputable def ep111000011_1 : Blocks := edgeBlocks% "full/vectors/111000011-E-0001.bin"
private noncomputable def ep111000011_2 : Blocks := edgeBlocks% "full/vectors/111000011-E-0002.bin"
private noncomputable def ep111000011_3 : Blocks := edgeBlocks% "full/vectors/111000011-E-0003.bin"
noncomputable def ep111000011 : Blocks := (Blocks.join (Blocks.join ep111000011_0 ep111000011_1) (Blocks.join ep111000011_2 ep111000011_3))
private theorem idp111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11100001.list =
    C ((2:ℤ)^485) * horner X vp111000011.list + horner X ep111000011.list := by
  exact edge_identity (B := (2:ℤ)^692) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111000011 : Branch 1 (-7199761639/32000000 : ℚ) vp11100001 := by
  apply branch_checked idp111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-7199761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7215761639/16000000 : ℚ) by norm_num]
  exact coverp111000011
theorem coverp11100001 : Covers (-7199761639/32000000 : ℚ) vp11100001 := join_branches bp111000010 bp111000011
private noncomputable def vp111000001_0 : Blocks := edgeBlocks% "full/vectors/111000001-V-0000.bin"
private noncomputable def vp111000001_1 : Blocks := edgeBlocks% "full/vectors/111000001-V-0001.bin"
noncomputable def vp111000001 : Blocks := (Blocks.join vp111000001_0 vp111000001_1)
theorem coverp111000001 : Covers (-7183761639/16000000 : ℚ) vp111000001 := cover_leaf (by decide +kernel)
private noncomputable def vp111000000_0 : Blocks := edgeBlocks% "full/vectors/111000000-V-0000.bin"
private noncomputable def vp111000000_1 : Blocks := edgeBlocks% "full/vectors/111000000-V-0001.bin"
noncomputable def vp111000000 : Blocks := (Blocks.join vp111000000_0 vp111000000_1)
theorem coverp111000000 : Covers (-7167761639/16000000 : ℚ) vp111000000 := cover_leaf (by decide +kernel)
private noncomputable def vp11100000_0 : Blocks := edgeBlocks% "full/vectors/11100000-V-0000.bin"
private noncomputable def vp11100000_1 : Blocks := edgeBlocks% "full/vectors/11100000-V-0001.bin"
private noncomputable def vp11100000_2 : Blocks := edgeBlocks% "full/vectors/11100000-V-0002.bin"
private noncomputable def vp11100000_3 : Blocks := edgeBlocks% "full/vectors/11100000-V-0003.bin"
noncomputable def vp11100000 : Blocks := (Blocks.join (Blocks.join vp11100000_0 vp11100000_1) (Blocks.join vp11100000_2 vp11100000_3))
private theorem bp111000000 : Branch 0 (-7167761639/32000000 : ℚ) vp11100000 := by
  apply branch_left_normalized (c:=vp111000000) (k:=0) (m:=207) (by decide +kernel)
  rw [show 2*(-7167761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-7167761639/16000000 : ℚ) by norm_num]
  exact coverp111000000
private noncomputable def ep111000001_0 : Blocks := edgeBlocks% "full/vectors/111000001-E-0000.bin"
private noncomputable def ep111000001_1 : Blocks := edgeBlocks% "full/vectors/111000001-E-0001.bin"
private noncomputable def ep111000001_2 : Blocks := edgeBlocks% "full/vectors/111000001-E-0002.bin"
private noncomputable def ep111000001_3 : Blocks := edgeBlocks% "full/vectors/111000001-E-0003.bin"
noncomputable def ep111000001 : Blocks := (Blocks.join (Blocks.join ep111000001_0 ep111000001_1) (Blocks.join ep111000001_2 ep111000001_3))
private theorem idp111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11100000.list =
    C ((2:ℤ)^487) * horner X vp111000001.list + horner X ep111000001.list := by
  exact edge_identity (B := (2:ℤ)^694) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111000001 : Branch 1 (-7167761639/32000000 : ℚ) vp11100000 := by
  apply branch_checked idp111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-7167761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-7183761639/16000000 : ℚ) by norm_num]
  exact coverp111000001
theorem coverp11100000 : Covers (-7167761639/32000000 : ℚ) vp11100000 := join_branches bp111000000 bp111000001
private noncomputable def vp1110000_0 : Blocks := edgeBlocks% "full/vectors/1110000-V-0000.bin"
private noncomputable def vp1110000_1 : Blocks := edgeBlocks% "full/vectors/1110000-V-0001.bin"
private noncomputable def vp1110000_2 : Blocks := edgeBlocks% "full/vectors/1110000-V-0002.bin"
private noncomputable def vp1110000_3 : Blocks := edgeBlocks% "full/vectors/1110000-V-0003.bin"
private noncomputable def vp1110000_4 : Blocks := edgeBlocks% "full/vectors/1110000-V-0004.bin"
private noncomputable def vp1110000_5 : Blocks := edgeBlocks% "full/vectors/1110000-V-0005.bin"
noncomputable def vp1110000 : Blocks := (Blocks.join (Blocks.join vp1110000_0 (Blocks.join vp1110000_1 vp1110000_2)) (Blocks.join vp1110000_3 (Blocks.join vp1110000_4 vp1110000_5)))
private theorem bp11100000 : Branch 0 (-7167761639/64000000 : ℚ) vp1110000 := by
  apply branch_left_normalized (c:=vp11100000) (k:=0) (m:=393) (by decide +kernel)
  rw [show 2*(-7167761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7167761639/32000000 : ℚ) by norm_num]
  exact coverp11100000
private noncomputable def ep11100001_0 : Blocks := edgeBlocks% "full/vectors/11100001-E-0000.bin"
private noncomputable def ep11100001_1 : Blocks := edgeBlocks% "full/vectors/11100001-E-0001.bin"
private noncomputable def ep11100001_2 : Blocks := edgeBlocks% "full/vectors/11100001-E-0002.bin"
private noncomputable def ep11100001_3 : Blocks := edgeBlocks% "full/vectors/11100001-E-0003.bin"
private noncomputable def ep11100001_4 : Blocks := edgeBlocks% "full/vectors/11100001-E-0004.bin"
private noncomputable def ep11100001_5 : Blocks := edgeBlocks% "full/vectors/11100001-E-0005.bin"
noncomputable def ep11100001 : Blocks := (Blocks.join (Blocks.join ep11100001_0 (Blocks.join ep11100001_1 ep11100001_2)) (Blocks.join ep11100001_3 (Blocks.join ep11100001_4 ep11100001_5)))
private theorem idp11100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1110000.list =
    C ((2:ℤ)^945) * horner X vp11100001.list + horner X ep11100001.list := by
  exact edge_identity (B := (2:ℤ)^1256) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11100001 : Branch 1 (-7167761639/64000000 : ℚ) vp1110000 := by
  apply branch_checked idp11100001 (by positivity) (by decide +kernel)
  rw [show 2*(-7167761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7199761639/32000000 : ℚ) by norm_num]
  exact coverp11100001
theorem coverp1110000 : Covers (-7167761639/64000000 : ℚ) vp1110000 := join_branches bp11100000 bp11100001
private noncomputable def vp111000_0 : Blocks := edgeBlocks% "full/vectors/111000-V-0000.bin"
private noncomputable def vp111000_1 : Blocks := edgeBlocks% "full/vectors/111000-V-0001.bin"
private noncomputable def vp111000_2 : Blocks := edgeBlocks% "full/vectors/111000-V-0002.bin"
private noncomputable def vp111000_3 : Blocks := edgeBlocks% "full/vectors/111000-V-0003.bin"
private noncomputable def vp111000_4 : Blocks := edgeBlocks% "full/vectors/111000-V-0004.bin"
private noncomputable def vp111000_5 : Blocks := edgeBlocks% "full/vectors/111000-V-0005.bin"
private noncomputable def vp111000_6 : Blocks := edgeBlocks% "full/vectors/111000-V-0006.bin"
private noncomputable def vp111000_7 : Blocks := edgeBlocks% "full/vectors/111000-V-0007.bin"
private noncomputable def vp111000_8 : Blocks := edgeBlocks% "full/vectors/111000-V-0008.bin"
private noncomputable def vp111000_9 : Blocks := edgeBlocks% "full/vectors/111000-V-0009.bin"
private noncomputable def vp111000_10 : Blocks := edgeBlocks% "full/vectors/111000-V-0010.bin"
private noncomputable def vp111000_11 : Blocks := edgeBlocks% "full/vectors/111000-V-0011.bin"
noncomputable def vp111000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp111000_0 (Blocks.join vp111000_1 vp111000_2)) (Blocks.join vp111000_3 (Blocks.join vp111000_4 vp111000_5))) (Blocks.join (Blocks.join vp111000_6 (Blocks.join vp111000_7 vp111000_8)) (Blocks.join vp111000_9 (Blocks.join vp111000_10 vp111000_11))))
private theorem bp1110000 : Branch 0 (-7167761639/128000000 : ℚ) vp111000 := by
  apply branch_left_normalized (c:=vp1110000) (k:=0) (m:=759) (by decide +kernel)
  rw [show 2*(-7167761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-7167761639/64000000 : ℚ) by norm_num]
  exact coverp1110000
private noncomputable def ep1110001_0 : Blocks := edgeBlocks% "full/vectors/1110001-E-0000.bin"
private noncomputable def ep1110001_1 : Blocks := edgeBlocks% "full/vectors/1110001-E-0001.bin"
private noncomputable def ep1110001_2 : Blocks := edgeBlocks% "full/vectors/1110001-E-0002.bin"
private noncomputable def ep1110001_3 : Blocks := edgeBlocks% "full/vectors/1110001-E-0003.bin"
private noncomputable def ep1110001_4 : Blocks := edgeBlocks% "full/vectors/1110001-E-0004.bin"
private noncomputable def ep1110001_5 : Blocks := edgeBlocks% "full/vectors/1110001-E-0005.bin"
private noncomputable def ep1110001_6 : Blocks := edgeBlocks% "full/vectors/1110001-E-0006.bin"
private noncomputable def ep1110001_7 : Blocks := edgeBlocks% "full/vectors/1110001-E-0007.bin"
private noncomputable def ep1110001_8 : Blocks := edgeBlocks% "full/vectors/1110001-E-0008.bin"
private noncomputable def ep1110001_9 : Blocks := edgeBlocks% "full/vectors/1110001-E-0009.bin"
private noncomputable def ep1110001_10 : Blocks := edgeBlocks% "full/vectors/1110001-E-0010.bin"
private noncomputable def ep1110001_11 : Blocks := edgeBlocks% "full/vectors/1110001-E-0011.bin"
noncomputable def ep1110001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1110001_0 (Blocks.join ep1110001_1 ep1110001_2)) (Blocks.join ep1110001_3 (Blocks.join ep1110001_4 ep1110001_5))) (Blocks.join (Blocks.join ep1110001_6 (Blocks.join ep1110001_7 ep1110001_8)) (Blocks.join ep1110001_9 (Blocks.join ep1110001_10 ep1110001_11))))
private theorem idp1110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp111000.list =
    C ((2:ℤ)^1848) * horner X vp1110001.list + horner X ep1110001.list := by
  exact edge_identity (B := (2:ℤ)^2364) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1110001 : Branch 1 (-7167761639/128000000 : ℚ) vp111000 := by
  apply branch_checked idp1110001 (by positivity) (by decide +kernel)
  rw [show 2*(-7167761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-7231761639/64000000 : ℚ) by norm_num]
  exact coverp1110001
theorem coverp111000 : Covers (-7167761639/128000000 : ℚ) vp111000 := join_branches bp1110000 bp1110001
private noncomputable def vp11100_0 : Blocks := edgeBlocks% "full/vectors/11100-V-0000.bin"
private noncomputable def vp11100_1 : Blocks := edgeBlocks% "full/vectors/11100-V-0001.bin"
private noncomputable def vp11100_2 : Blocks := edgeBlocks% "full/vectors/11100-V-0002.bin"
private noncomputable def vp11100_3 : Blocks := edgeBlocks% "full/vectors/11100-V-0003.bin"
private noncomputable def vp11100_4 : Blocks := edgeBlocks% "full/vectors/11100-V-0004.bin"
private noncomputable def vp11100_5 : Blocks := edgeBlocks% "full/vectors/11100-V-0005.bin"
private noncomputable def vp11100_6 : Blocks := edgeBlocks% "full/vectors/11100-V-0006.bin"
private noncomputable def vp11100_7 : Blocks := edgeBlocks% "full/vectors/11100-V-0007.bin"
private noncomputable def vp11100_8 : Blocks := edgeBlocks% "full/vectors/11100-V-0008.bin"
private noncomputable def vp11100_9 : Blocks := edgeBlocks% "full/vectors/11100-V-0009.bin"
private noncomputable def vp11100_10 : Blocks := edgeBlocks% "full/vectors/11100-V-0010.bin"
private noncomputable def vp11100_11 : Blocks := edgeBlocks% "full/vectors/11100-V-0011.bin"
private noncomputable def vp11100_12 : Blocks := edgeBlocks% "full/vectors/11100-V-0012.bin"
private noncomputable def vp11100_13 : Blocks := edgeBlocks% "full/vectors/11100-V-0013.bin"
private noncomputable def vp11100_14 : Blocks := edgeBlocks% "full/vectors/11100-V-0014.bin"
private noncomputable def vp11100_15 : Blocks := edgeBlocks% "full/vectors/11100-V-0015.bin"
private noncomputable def vp11100_16 : Blocks := edgeBlocks% "full/vectors/11100-V-0016.bin"
private noncomputable def vp11100_17 : Blocks := edgeBlocks% "full/vectors/11100-V-0017.bin"
private noncomputable def vp11100_18 : Blocks := edgeBlocks% "full/vectors/11100-V-0018.bin"
private noncomputable def vp11100_19 : Blocks := edgeBlocks% "full/vectors/11100-V-0019.bin"
private noncomputable def vp11100_20 : Blocks := edgeBlocks% "full/vectors/11100-V-0020.bin"
private noncomputable def vp11100_21 : Blocks := edgeBlocks% "full/vectors/11100-V-0021.bin"
private noncomputable def vp11100_22 : Blocks := edgeBlocks% "full/vectors/11100-V-0022.bin"
noncomputable def vp11100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp11100_0 vp11100_1) (Blocks.join vp11100_2 (Blocks.join vp11100_3 vp11100_4))) (Blocks.join (Blocks.join vp11100_5 (Blocks.join vp11100_6 vp11100_7)) (Blocks.join vp11100_8 (Blocks.join vp11100_9 vp11100_10)))) (Blocks.join (Blocks.join (Blocks.join vp11100_11 (Blocks.join vp11100_12 vp11100_13)) (Blocks.join vp11100_14 (Blocks.join vp11100_15 vp11100_16))) (Blocks.join (Blocks.join vp11100_17 (Blocks.join vp11100_18 vp11100_19)) (Blocks.join vp11100_20 (Blocks.join vp11100_21 vp11100_22)))))
private theorem bp111000 : Branch 0 (-7167761639/256000000 : ℚ) vp11100 := by
  apply branch_left_normalized (c:=vp111000) (k:=0) (m:=1477) (by decide +kernel)
  rw [show 2*(-7167761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-7167761639/128000000 : ℚ) by norm_num]
  exact coverp111000
private noncomputable def ep111001_0 : Blocks := edgeBlocks% "full/vectors/111001-E-0000.bin"
private noncomputable def ep111001_1 : Blocks := edgeBlocks% "full/vectors/111001-E-0001.bin"
private noncomputable def ep111001_2 : Blocks := edgeBlocks% "full/vectors/111001-E-0002.bin"
private noncomputable def ep111001_3 : Blocks := edgeBlocks% "full/vectors/111001-E-0003.bin"
private noncomputable def ep111001_4 : Blocks := edgeBlocks% "full/vectors/111001-E-0004.bin"
private noncomputable def ep111001_5 : Blocks := edgeBlocks% "full/vectors/111001-E-0005.bin"
private noncomputable def ep111001_6 : Blocks := edgeBlocks% "full/vectors/111001-E-0006.bin"
private noncomputable def ep111001_7 : Blocks := edgeBlocks% "full/vectors/111001-E-0007.bin"
private noncomputable def ep111001_8 : Blocks := edgeBlocks% "full/vectors/111001-E-0008.bin"
private noncomputable def ep111001_9 : Blocks := edgeBlocks% "full/vectors/111001-E-0009.bin"
private noncomputable def ep111001_10 : Blocks := edgeBlocks% "full/vectors/111001-E-0010.bin"
private noncomputable def ep111001_11 : Blocks := edgeBlocks% "full/vectors/111001-E-0011.bin"
private noncomputable def ep111001_12 : Blocks := edgeBlocks% "full/vectors/111001-E-0012.bin"
private noncomputable def ep111001_13 : Blocks := edgeBlocks% "full/vectors/111001-E-0013.bin"
private noncomputable def ep111001_14 : Blocks := edgeBlocks% "full/vectors/111001-E-0014.bin"
private noncomputable def ep111001_15 : Blocks := edgeBlocks% "full/vectors/111001-E-0015.bin"
private noncomputable def ep111001_16 : Blocks := edgeBlocks% "full/vectors/111001-E-0016.bin"
private noncomputable def ep111001_17 : Blocks := edgeBlocks% "full/vectors/111001-E-0017.bin"
private noncomputable def ep111001_18 : Blocks := edgeBlocks% "full/vectors/111001-E-0018.bin"
private noncomputable def ep111001_19 : Blocks := edgeBlocks% "full/vectors/111001-E-0019.bin"
private noncomputable def ep111001_20 : Blocks := edgeBlocks% "full/vectors/111001-E-0020.bin"
private noncomputable def ep111001_21 : Blocks := edgeBlocks% "full/vectors/111001-E-0021.bin"
private noncomputable def ep111001_22 : Blocks := edgeBlocks% "full/vectors/111001-E-0022.bin"
noncomputable def ep111001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep111001_0 ep111001_1) (Blocks.join ep111001_2 (Blocks.join ep111001_3 ep111001_4))) (Blocks.join (Blocks.join ep111001_5 (Blocks.join ep111001_6 ep111001_7)) (Blocks.join ep111001_8 (Blocks.join ep111001_9 ep111001_10)))) (Blocks.join (Blocks.join (Blocks.join ep111001_11 (Blocks.join ep111001_12 ep111001_13)) (Blocks.join ep111001_14 (Blocks.join ep111001_15 ep111001_16))) (Blocks.join (Blocks.join ep111001_17 (Blocks.join ep111001_18 ep111001_19)) (Blocks.join ep111001_20 (Blocks.join ep111001_21 ep111001_22)))))
private def ptsp111001 : List ℤ := [((2:ℤ)^4188+0),((2:ℤ)^4188+1)]
private theorem boundp111001 : 2^vp11100.size*absSum vp11100.list + ((2:ℤ)^3604*absSum vp111001.list+absSum ep111001.list) < (2:ℤ)^4522 := by decide +kernel
private theorem pointp111001_0 : fastHom 1 ((2:ℤ)^4188+0) vp11100 = ((2:ℤ)^3604)*vp111001.subst ((2:ℤ)^4188+0)+ep111001.subst ((2:ℤ)^4188+0) := by decide +kernel
private theorem pointp111001_1 : fastHom 1 ((2:ℤ)^4188+1) vp11100 = ((2:ℤ)^3604)*vp111001.subst ((2:ℤ)^4188+1)+ep111001.subst ((2:ℤ)^4188+1) := by decide +kernel
private theorem checkp111001 (x:ℤ) (hx:x ∈ ptsp111001) : fastHom 1 x vp11100 = ((2:ℤ)^3604)*vp111001.subst x+ep111001.subst x := by
  simp only [ptsp111001,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp111001_0
  · exact pointp111001_1
private theorem idp111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11100.list =
    C ((2:ℤ)^3604) * horner X vp111001.list + horner X ep111001.list := by
  apply edge_identity (B := (2:ℤ)^4522) (by decide) (by positivity) (by positivity) boundp111001
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp111001 (by decide +kernel)
  · have h : ptsp111001.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp111001.trans_le (by decide +kernel)
  · exact checkp111001
private theorem bp111001 : Branch 1 (-7167761639/256000000 : ℚ) vp11100 := by
  apply branch_checked idp111001 (by positivity) (by decide +kernel)
  rw [show 2*(-7167761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-7295761639/128000000 : ℚ) by norm_num]
  exact coverp111001
theorem coverp11100 : Covers (-7167761639/256000000 : ℚ) vp11100 := join_branches bp111000 bp111001
private noncomputable def vp1110_0 : Blocks := edgeBlocks% "full/vectors/1110-V-0000.bin"
private noncomputable def vp1110_1 : Blocks := edgeBlocks% "full/vectors/1110-V-0001.bin"
private noncomputable def vp1110_2 : Blocks := edgeBlocks% "full/vectors/1110-V-0002.bin"
private noncomputable def vp1110_3 : Blocks := edgeBlocks% "full/vectors/1110-V-0003.bin"
private noncomputable def vp1110_4 : Blocks := edgeBlocks% "full/vectors/1110-V-0004.bin"
private noncomputable def vp1110_5 : Blocks := edgeBlocks% "full/vectors/1110-V-0005.bin"
private noncomputable def vp1110_6 : Blocks := edgeBlocks% "full/vectors/1110-V-0006.bin"
private noncomputable def vp1110_7 : Blocks := edgeBlocks% "full/vectors/1110-V-0007.bin"
private noncomputable def vp1110_8 : Blocks := edgeBlocks% "full/vectors/1110-V-0008.bin"
private noncomputable def vp1110_9 : Blocks := edgeBlocks% "full/vectors/1110-V-0009.bin"
private noncomputable def vp1110_10 : Blocks := edgeBlocks% "full/vectors/1110-V-0010.bin"
private noncomputable def vp1110_11 : Blocks := edgeBlocks% "full/vectors/1110-V-0011.bin"
private noncomputable def vp1110_12 : Blocks := edgeBlocks% "full/vectors/1110-V-0012.bin"
private noncomputable def vp1110_13 : Blocks := edgeBlocks% "full/vectors/1110-V-0013.bin"
private noncomputable def vp1110_14 : Blocks := edgeBlocks% "full/vectors/1110-V-0014.bin"
private noncomputable def vp1110_15 : Blocks := edgeBlocks% "full/vectors/1110-V-0015.bin"
private noncomputable def vp1110_16 : Blocks := edgeBlocks% "full/vectors/1110-V-0016.bin"
private noncomputable def vp1110_17 : Blocks := edgeBlocks% "full/vectors/1110-V-0017.bin"
private noncomputable def vp1110_18 : Blocks := edgeBlocks% "full/vectors/1110-V-0018.bin"
private noncomputable def vp1110_19 : Blocks := edgeBlocks% "full/vectors/1110-V-0019.bin"
private noncomputable def vp1110_20 : Blocks := edgeBlocks% "full/vectors/1110-V-0020.bin"
private noncomputable def vp1110_21 : Blocks := edgeBlocks% "full/vectors/1110-V-0021.bin"
private noncomputable def vp1110_22 : Blocks := edgeBlocks% "full/vectors/1110-V-0022.bin"
private noncomputable def vp1110_23 : Blocks := edgeBlocks% "full/vectors/1110-V-0023.bin"
private noncomputable def vp1110_24 : Blocks := edgeBlocks% "full/vectors/1110-V-0024.bin"
private noncomputable def vp1110_25 : Blocks := edgeBlocks% "full/vectors/1110-V-0025.bin"
private noncomputable def vp1110_26 : Blocks := edgeBlocks% "full/vectors/1110-V-0026.bin"
private noncomputable def vp1110_27 : Blocks := edgeBlocks% "full/vectors/1110-V-0027.bin"
private noncomputable def vp1110_28 : Blocks := edgeBlocks% "full/vectors/1110-V-0028.bin"
private noncomputable def vp1110_29 : Blocks := edgeBlocks% "full/vectors/1110-V-0029.bin"
private noncomputable def vp1110_30 : Blocks := edgeBlocks% "full/vectors/1110-V-0030.bin"
private noncomputable def vp1110_31 : Blocks := edgeBlocks% "full/vectors/1110-V-0031.bin"
private noncomputable def vp1110_32 : Blocks := edgeBlocks% "full/vectors/1110-V-0032.bin"
private noncomputable def vp1110_33 : Blocks := edgeBlocks% "full/vectors/1110-V-0033.bin"
private noncomputable def vp1110_34 : Blocks := edgeBlocks% "full/vectors/1110-V-0034.bin"
private noncomputable def vp1110_35 : Blocks := edgeBlocks% "full/vectors/1110-V-0035.bin"
private noncomputable def vp1110_36 : Blocks := edgeBlocks% "full/vectors/1110-V-0036.bin"
private noncomputable def vp1110_37 : Blocks := edgeBlocks% "full/vectors/1110-V-0037.bin"
private noncomputable def vp1110_38 : Blocks := edgeBlocks% "full/vectors/1110-V-0038.bin"
private noncomputable def vp1110_39 : Blocks := edgeBlocks% "full/vectors/1110-V-0039.bin"
private noncomputable def vp1110_40 : Blocks := edgeBlocks% "full/vectors/1110-V-0040.bin"
private noncomputable def vp1110_41 : Blocks := edgeBlocks% "full/vectors/1110-V-0041.bin"
noncomputable def vp1110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1110_0 vp1110_1) (Blocks.join vp1110_2 (Blocks.join vp1110_3 vp1110_4))) (Blocks.join (Blocks.join vp1110_5 vp1110_6) (Blocks.join vp1110_7 (Blocks.join vp1110_8 vp1110_9)))) (Blocks.join (Blocks.join (Blocks.join vp1110_10 vp1110_11) (Blocks.join vp1110_12 (Blocks.join vp1110_13 vp1110_14))) (Blocks.join (Blocks.join vp1110_15 (Blocks.join vp1110_16 vp1110_17)) (Blocks.join vp1110_18 (Blocks.join vp1110_19 vp1110_20))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1110_21 vp1110_22) (Blocks.join vp1110_23 (Blocks.join vp1110_24 vp1110_25))) (Blocks.join (Blocks.join vp1110_26 vp1110_27) (Blocks.join vp1110_28 (Blocks.join vp1110_29 vp1110_30)))) (Blocks.join (Blocks.join (Blocks.join vp1110_31 vp1110_32) (Blocks.join vp1110_33 (Blocks.join vp1110_34 vp1110_35))) (Blocks.join (Blocks.join vp1110_36 (Blocks.join vp1110_37 vp1110_38)) (Blocks.join vp1110_39 (Blocks.join vp1110_40 vp1110_41))))))
private theorem bp11100 : Branch 0 (-7167761639/512000000 : ℚ) vp1110 := by
  apply branch_left_normalized (c:=vp11100) (k:=0) (m:=2864) (by decide +kernel)
  rw [show 2*(-7167761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-7167761639/256000000 : ℚ) by norm_num]
  exact coverp11100
private noncomputable def ep11101_0 : Blocks := edgeBlocks% "full/vectors/11101-E-0000.bin"
private noncomputable def ep11101_1 : Blocks := edgeBlocks% "full/vectors/11101-E-0001.bin"
private noncomputable def ep11101_2 : Blocks := edgeBlocks% "full/vectors/11101-E-0002.bin"
private noncomputable def ep11101_3 : Blocks := edgeBlocks% "full/vectors/11101-E-0003.bin"
private noncomputable def ep11101_4 : Blocks := edgeBlocks% "full/vectors/11101-E-0004.bin"
private noncomputable def ep11101_5 : Blocks := edgeBlocks% "full/vectors/11101-E-0005.bin"
private noncomputable def ep11101_6 : Blocks := edgeBlocks% "full/vectors/11101-E-0006.bin"
private noncomputable def ep11101_7 : Blocks := edgeBlocks% "full/vectors/11101-E-0007.bin"
private noncomputable def ep11101_8 : Blocks := edgeBlocks% "full/vectors/11101-E-0008.bin"
private noncomputable def ep11101_9 : Blocks := edgeBlocks% "full/vectors/11101-E-0009.bin"
private noncomputable def ep11101_10 : Blocks := edgeBlocks% "full/vectors/11101-E-0010.bin"
private noncomputable def ep11101_11 : Blocks := edgeBlocks% "full/vectors/11101-E-0011.bin"
private noncomputable def ep11101_12 : Blocks := edgeBlocks% "full/vectors/11101-E-0012.bin"
private noncomputable def ep11101_13 : Blocks := edgeBlocks% "full/vectors/11101-E-0013.bin"
private noncomputable def ep11101_14 : Blocks := edgeBlocks% "full/vectors/11101-E-0014.bin"
private noncomputable def ep11101_15 : Blocks := edgeBlocks% "full/vectors/11101-E-0015.bin"
private noncomputable def ep11101_16 : Blocks := edgeBlocks% "full/vectors/11101-E-0016.bin"
private noncomputable def ep11101_17 : Blocks := edgeBlocks% "full/vectors/11101-E-0017.bin"
private noncomputable def ep11101_18 : Blocks := edgeBlocks% "full/vectors/11101-E-0018.bin"
private noncomputable def ep11101_19 : Blocks := edgeBlocks% "full/vectors/11101-E-0019.bin"
private noncomputable def ep11101_20 : Blocks := edgeBlocks% "full/vectors/11101-E-0020.bin"
private noncomputable def ep11101_21 : Blocks := edgeBlocks% "full/vectors/11101-E-0021.bin"
private noncomputable def ep11101_22 : Blocks := edgeBlocks% "full/vectors/11101-E-0022.bin"
private noncomputable def ep11101_23 : Blocks := edgeBlocks% "full/vectors/11101-E-0023.bin"
private noncomputable def ep11101_24 : Blocks := edgeBlocks% "full/vectors/11101-E-0024.bin"
private noncomputable def ep11101_25 : Blocks := edgeBlocks% "full/vectors/11101-E-0025.bin"
private noncomputable def ep11101_26 : Blocks := edgeBlocks% "full/vectors/11101-E-0026.bin"
private noncomputable def ep11101_27 : Blocks := edgeBlocks% "full/vectors/11101-E-0027.bin"
private noncomputable def ep11101_28 : Blocks := edgeBlocks% "full/vectors/11101-E-0028.bin"
private noncomputable def ep11101_29 : Blocks := edgeBlocks% "full/vectors/11101-E-0029.bin"
private noncomputable def ep11101_30 : Blocks := edgeBlocks% "full/vectors/11101-E-0030.bin"
private noncomputable def ep11101_31 : Blocks := edgeBlocks% "full/vectors/11101-E-0031.bin"
private noncomputable def ep11101_32 : Blocks := edgeBlocks% "full/vectors/11101-E-0032.bin"
private noncomputable def ep11101_33 : Blocks := edgeBlocks% "full/vectors/11101-E-0033.bin"
private noncomputable def ep11101_34 : Blocks := edgeBlocks% "full/vectors/11101-E-0034.bin"
private noncomputable def ep11101_35 : Blocks := edgeBlocks% "full/vectors/11101-E-0035.bin"
private noncomputable def ep11101_36 : Blocks := edgeBlocks% "full/vectors/11101-E-0036.bin"
private noncomputable def ep11101_37 : Blocks := edgeBlocks% "full/vectors/11101-E-0037.bin"
private noncomputable def ep11101_38 : Blocks := edgeBlocks% "full/vectors/11101-E-0038.bin"
private noncomputable def ep11101_39 : Blocks := edgeBlocks% "full/vectors/11101-E-0039.bin"
private noncomputable def ep11101_40 : Blocks := edgeBlocks% "full/vectors/11101-E-0040.bin"
private noncomputable def ep11101_41 : Blocks := edgeBlocks% "full/vectors/11101-E-0041.bin"
noncomputable def ep11101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep11101_0 ep11101_1) (Blocks.join ep11101_2 (Blocks.join ep11101_3 ep11101_4))) (Blocks.join (Blocks.join ep11101_5 ep11101_6) (Blocks.join ep11101_7 (Blocks.join ep11101_8 ep11101_9)))) (Blocks.join (Blocks.join (Blocks.join ep11101_10 ep11101_11) (Blocks.join ep11101_12 (Blocks.join ep11101_13 ep11101_14))) (Blocks.join (Blocks.join ep11101_15 (Blocks.join ep11101_16 ep11101_17)) (Blocks.join ep11101_18 (Blocks.join ep11101_19 ep11101_20))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep11101_21 ep11101_22) (Blocks.join ep11101_23 (Blocks.join ep11101_24 ep11101_25))) (Blocks.join (Blocks.join ep11101_26 ep11101_27) (Blocks.join ep11101_28 (Blocks.join ep11101_29 ep11101_30)))) (Blocks.join (Blocks.join (Blocks.join ep11101_31 ep11101_32) (Blocks.join ep11101_33 (Blocks.join ep11101_34 ep11101_35))) (Blocks.join (Blocks.join ep11101_36 (Blocks.join ep11101_37 ep11101_38)) (Blocks.join ep11101_39 (Blocks.join ep11101_40 ep11101_41))))))
private def ptsp11101 : List ℤ := [((2:ℤ)^2285+0),((2:ℤ)^2285+1),((2:ℤ)^2285+2),((2:ℤ)^2285+3)]
private theorem boundp11101 : 2^vp1110.size*absSum vp1110.list + ((2:ℤ)^6727*absSum vp11101.list+absSum ep11101.list) < (2:ℤ)^8409 := by decide +kernel
private theorem pointp11101_0 : fastHom 1 ((2:ℤ)^2285+0) vp1110 = ((2:ℤ)^6727)*vp11101.subst ((2:ℤ)^2285+0)+ep11101.subst ((2:ℤ)^2285+0) := by decide +kernel
private theorem pointp11101_1 : fastHom 1 ((2:ℤ)^2285+1) vp1110 = ((2:ℤ)^6727)*vp11101.subst ((2:ℤ)^2285+1)+ep11101.subst ((2:ℤ)^2285+1) := by decide +kernel
private theorem pointp11101_2 : fastHom 1 ((2:ℤ)^2285+2) vp1110 = ((2:ℤ)^6727)*vp11101.subst ((2:ℤ)^2285+2)+ep11101.subst ((2:ℤ)^2285+2) := by decide +kernel
private theorem pointp11101_3 : fastHom 1 ((2:ℤ)^2285+3) vp1110 = ((2:ℤ)^6727)*vp11101.subst ((2:ℤ)^2285+3)+ep11101.subst ((2:ℤ)^2285+3) := by decide +kernel
private theorem checkp11101 (x:ℤ) (hx:x ∈ ptsp11101) : fastHom 1 x vp1110 = ((2:ℤ)^6727)*vp11101.subst x+ep11101.subst x := by
  simp only [ptsp11101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pointp11101_0
  · exact pointp11101_1
  · exact pointp11101_2
  · exact pointp11101_3
private theorem idp11101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1110.list =
    C ((2:ℤ)^6727) * horner X vp11101.list + horner X ep11101.list := by
  apply edge_identity (B := (2:ℤ)^8409) (by decide) (by positivity) (by positivity) boundp11101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp11101 (by decide +kernel)
  · have h : ptsp11101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp11101.trans_le (by decide +kernel)
  · exact checkp11101
private theorem bp11101 : Branch 1 (-7167761639/512000000 : ℚ) vp1110 := by
  apply branch_checked idp11101 (by positivity) (by decide +kernel)
  rw [show 2*(-7167761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-7423761639/256000000 : ℚ) by norm_num]
  exact coverp11101
theorem coverp1110 : Covers (-7167761639/512000000 : ℚ) vp1110 := join_branches bp11100 bp11101
private noncomputable def vp111_0 : Blocks := edgeBlocks% "full/vectors/111-V-0000.bin"
private noncomputable def vp111_1 : Blocks := edgeBlocks% "full/vectors/111-V-0001.bin"
private noncomputable def vp111_2 : Blocks := edgeBlocks% "full/vectors/111-V-0002.bin"
private noncomputable def vp111_3 : Blocks := edgeBlocks% "full/vectors/111-V-0003.bin"
private noncomputable def vp111_4 : Blocks := edgeBlocks% "full/vectors/111-V-0004.bin"
private noncomputable def vp111_5 : Blocks := edgeBlocks% "full/vectors/111-V-0005.bin"
private noncomputable def vp111_6 : Blocks := edgeBlocks% "full/vectors/111-V-0006.bin"
private noncomputable def vp111_7 : Blocks := edgeBlocks% "full/vectors/111-V-0007.bin"
private noncomputable def vp111_8 : Blocks := edgeBlocks% "full/vectors/111-V-0008.bin"
private noncomputable def vp111_9 : Blocks := edgeBlocks% "full/vectors/111-V-0009.bin"
private noncomputable def vp111_10 : Blocks := edgeBlocks% "full/vectors/111-V-0010.bin"
private noncomputable def vp111_11 : Blocks := edgeBlocks% "full/vectors/111-V-0011.bin"
private noncomputable def vp111_12 : Blocks := edgeBlocks% "full/vectors/111-V-0012.bin"
private noncomputable def vp111_13 : Blocks := edgeBlocks% "full/vectors/111-V-0013.bin"
private noncomputable def vp111_14 : Blocks := edgeBlocks% "full/vectors/111-V-0014.bin"
private noncomputable def vp111_15 : Blocks := edgeBlocks% "full/vectors/111-V-0015.bin"
private noncomputable def vp111_16 : Blocks := edgeBlocks% "full/vectors/111-V-0016.bin"
private noncomputable def vp111_17 : Blocks := edgeBlocks% "full/vectors/111-V-0017.bin"
private noncomputable def vp111_18 : Blocks := edgeBlocks% "full/vectors/111-V-0018.bin"
private noncomputable def vp111_19 : Blocks := edgeBlocks% "full/vectors/111-V-0019.bin"
private noncomputable def vp111_20 : Blocks := edgeBlocks% "full/vectors/111-V-0020.bin"
private noncomputable def vp111_21 : Blocks := edgeBlocks% "full/vectors/111-V-0021.bin"
private noncomputable def vp111_22 : Blocks := edgeBlocks% "full/vectors/111-V-0022.bin"
private noncomputable def vp111_23 : Blocks := edgeBlocks% "full/vectors/111-V-0023.bin"
private noncomputable def vp111_24 : Blocks := edgeBlocks% "full/vectors/111-V-0024.bin"
private noncomputable def vp111_25 : Blocks := edgeBlocks% "full/vectors/111-V-0025.bin"
private noncomputable def vp111_26 : Blocks := edgeBlocks% "full/vectors/111-V-0026.bin"
private noncomputable def vp111_27 : Blocks := edgeBlocks% "full/vectors/111-V-0027.bin"
private noncomputable def vp111_28 : Blocks := edgeBlocks% "full/vectors/111-V-0028.bin"
private noncomputable def vp111_29 : Blocks := edgeBlocks% "full/vectors/111-V-0029.bin"
private noncomputable def vp111_30 : Blocks := edgeBlocks% "full/vectors/111-V-0030.bin"
private noncomputable def vp111_31 : Blocks := edgeBlocks% "full/vectors/111-V-0031.bin"
private noncomputable def vp111_32 : Blocks := edgeBlocks% "full/vectors/111-V-0032.bin"
private noncomputable def vp111_33 : Blocks := edgeBlocks% "full/vectors/111-V-0033.bin"
private noncomputable def vp111_34 : Blocks := edgeBlocks% "full/vectors/111-V-0034.bin"
private noncomputable def vp111_35 : Blocks := edgeBlocks% "full/vectors/111-V-0035.bin"
private noncomputable def vp111_36 : Blocks := edgeBlocks% "full/vectors/111-V-0036.bin"
private noncomputable def vp111_37 : Blocks := edgeBlocks% "full/vectors/111-V-0037.bin"
private noncomputable def vp111_38 : Blocks := edgeBlocks% "full/vectors/111-V-0038.bin"
private noncomputable def vp111_39 : Blocks := edgeBlocks% "full/vectors/111-V-0039.bin"
private noncomputable def vp111_40 : Blocks := edgeBlocks% "full/vectors/111-V-0040.bin"
private noncomputable def vp111_41 : Blocks := edgeBlocks% "full/vectors/111-V-0041.bin"
private noncomputable def vp111_42 : Blocks := edgeBlocks% "full/vectors/111-V-0042.bin"
private noncomputable def vp111_43 : Blocks := edgeBlocks% "full/vectors/111-V-0043.bin"
private noncomputable def vp111_44 : Blocks := edgeBlocks% "full/vectors/111-V-0044.bin"
private noncomputable def vp111_45 : Blocks := edgeBlocks% "full/vectors/111-V-0045.bin"
private noncomputable def vp111_46 : Blocks := edgeBlocks% "full/vectors/111-V-0046.bin"
private noncomputable def vp111_47 : Blocks := edgeBlocks% "full/vectors/111-V-0047.bin"
private noncomputable def vp111_48 : Blocks := edgeBlocks% "full/vectors/111-V-0048.bin"
private noncomputable def vp111_49 : Blocks := edgeBlocks% "full/vectors/111-V-0049.bin"
private noncomputable def vp111_50 : Blocks := edgeBlocks% "full/vectors/111-V-0050.bin"
private noncomputable def vp111_51 : Blocks := edgeBlocks% "full/vectors/111-V-0051.bin"
private noncomputable def vp111_52 : Blocks := edgeBlocks% "full/vectors/111-V-0052.bin"
private noncomputable def vp111_53 : Blocks := edgeBlocks% "full/vectors/111-V-0053.bin"
private noncomputable def vp111_54 : Blocks := edgeBlocks% "full/vectors/111-V-0054.bin"
private noncomputable def vp111_55 : Blocks := edgeBlocks% "full/vectors/111-V-0055.bin"
private noncomputable def vp111_56 : Blocks := edgeBlocks% "full/vectors/111-V-0056.bin"
private noncomputable def vp111_57 : Blocks := edgeBlocks% "full/vectors/111-V-0057.bin"
private noncomputable def vp111_58 : Blocks := edgeBlocks% "full/vectors/111-V-0058.bin"
private noncomputable def vp111_59 : Blocks := edgeBlocks% "full/vectors/111-V-0059.bin"
private noncomputable def vp111_60 : Blocks := edgeBlocks% "full/vectors/111-V-0060.bin"
private noncomputable def vp111_61 : Blocks := edgeBlocks% "full/vectors/111-V-0061.bin"
private noncomputable def vp111_62 : Blocks := edgeBlocks% "full/vectors/111-V-0062.bin"
private noncomputable def vp111_63 : Blocks := edgeBlocks% "full/vectors/111-V-0063.bin"
private noncomputable def vp111_64 : Blocks := edgeBlocks% "full/vectors/111-V-0064.bin"
private noncomputable def vp111_65 : Blocks := edgeBlocks% "full/vectors/111-V-0065.bin"
private noncomputable def vp111_66 : Blocks := edgeBlocks% "full/vectors/111-V-0066.bin"
noncomputable def vp111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp111_0 vp111_1) (Blocks.join vp111_2 vp111_3)) (Blocks.join (Blocks.join vp111_4 vp111_5) (Blocks.join vp111_6 vp111_7))) (Blocks.join (Blocks.join (Blocks.join vp111_8 vp111_9) (Blocks.join vp111_10 vp111_11)) (Blocks.join (Blocks.join vp111_12 vp111_13) (Blocks.join vp111_14 vp111_15)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp111_16 vp111_17) (Blocks.join vp111_18 vp111_19)) (Blocks.join (Blocks.join vp111_20 vp111_21) (Blocks.join vp111_22 vp111_23))) (Blocks.join (Blocks.join (Blocks.join vp111_24 vp111_25) (Blocks.join vp111_26 vp111_27)) (Blocks.join (Blocks.join vp111_28 vp111_29) (Blocks.join vp111_30 (Blocks.join vp111_31 vp111_32)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp111_33 vp111_34) (Blocks.join vp111_35 vp111_36)) (Blocks.join (Blocks.join vp111_37 vp111_38) (Blocks.join vp111_39 vp111_40))) (Blocks.join (Blocks.join (Blocks.join vp111_41 vp111_42) (Blocks.join vp111_43 vp111_44)) (Blocks.join (Blocks.join vp111_45 vp111_46) (Blocks.join vp111_47 (Blocks.join vp111_48 vp111_49))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp111_50 vp111_51) (Blocks.join vp111_52 vp111_53)) (Blocks.join (Blocks.join vp111_54 vp111_55) (Blocks.join vp111_56 vp111_57))) (Blocks.join (Blocks.join (Blocks.join vp111_58 vp111_59) (Blocks.join vp111_60 vp111_61)) (Blocks.join (Blocks.join vp111_62 vp111_63) (Blocks.join vp111_64 (Blocks.join vp111_65 vp111_66)))))))
private theorem bp1110 : Branch 0 (-7167761639/1024000000 : ℚ) vp111 := by
  apply branch_left_normalized (c:=vp1110) (k:=0) (m:=5249) (by decide +kernel)
  rw [show 2*(-7167761639/1024000000 : ℚ) - ((0:ℤ):ℚ) = (-7167761639/512000000 : ℚ) by norm_num]
  exact coverp1110
private noncomputable def ep1111_0 : Blocks := edgeBlocks% "full/vectors/1111-E-0000.bin"
private noncomputable def ep1111_1 : Blocks := edgeBlocks% "full/vectors/1111-E-0001.bin"
private noncomputable def ep1111_2 : Blocks := edgeBlocks% "full/vectors/1111-E-0002.bin"
private noncomputable def ep1111_3 : Blocks := edgeBlocks% "full/vectors/1111-E-0003.bin"
private noncomputable def ep1111_4 : Blocks := edgeBlocks% "full/vectors/1111-E-0004.bin"
private noncomputable def ep1111_5 : Blocks := edgeBlocks% "full/vectors/1111-E-0005.bin"
private noncomputable def ep1111_6 : Blocks := edgeBlocks% "full/vectors/1111-E-0006.bin"
private noncomputable def ep1111_7 : Blocks := edgeBlocks% "full/vectors/1111-E-0007.bin"
private noncomputable def ep1111_8 : Blocks := edgeBlocks% "full/vectors/1111-E-0008.bin"
private noncomputable def ep1111_9 : Blocks := edgeBlocks% "full/vectors/1111-E-0009.bin"
private noncomputable def ep1111_10 : Blocks := edgeBlocks% "full/vectors/1111-E-0010.bin"
private noncomputable def ep1111_11 : Blocks := edgeBlocks% "full/vectors/1111-E-0011.bin"
private noncomputable def ep1111_12 : Blocks := edgeBlocks% "full/vectors/1111-E-0012.bin"
private noncomputable def ep1111_13 : Blocks := edgeBlocks% "full/vectors/1111-E-0013.bin"
private noncomputable def ep1111_14 : Blocks := edgeBlocks% "full/vectors/1111-E-0014.bin"
private noncomputable def ep1111_15 : Blocks := edgeBlocks% "full/vectors/1111-E-0015.bin"
private noncomputable def ep1111_16 : Blocks := edgeBlocks% "full/vectors/1111-E-0016.bin"
private noncomputable def ep1111_17 : Blocks := edgeBlocks% "full/vectors/1111-E-0017.bin"
private noncomputable def ep1111_18 : Blocks := edgeBlocks% "full/vectors/1111-E-0018.bin"
private noncomputable def ep1111_19 : Blocks := edgeBlocks% "full/vectors/1111-E-0019.bin"
private noncomputable def ep1111_20 : Blocks := edgeBlocks% "full/vectors/1111-E-0020.bin"
private noncomputable def ep1111_21 : Blocks := edgeBlocks% "full/vectors/1111-E-0021.bin"
private noncomputable def ep1111_22 : Blocks := edgeBlocks% "full/vectors/1111-E-0022.bin"
private noncomputable def ep1111_23 : Blocks := edgeBlocks% "full/vectors/1111-E-0023.bin"
private noncomputable def ep1111_24 : Blocks := edgeBlocks% "full/vectors/1111-E-0024.bin"
private noncomputable def ep1111_25 : Blocks := edgeBlocks% "full/vectors/1111-E-0025.bin"
private noncomputable def ep1111_26 : Blocks := edgeBlocks% "full/vectors/1111-E-0026.bin"
private noncomputable def ep1111_27 : Blocks := edgeBlocks% "full/vectors/1111-E-0027.bin"
private noncomputable def ep1111_28 : Blocks := edgeBlocks% "full/vectors/1111-E-0028.bin"
private noncomputable def ep1111_29 : Blocks := edgeBlocks% "full/vectors/1111-E-0029.bin"
private noncomputable def ep1111_30 : Blocks := edgeBlocks% "full/vectors/1111-E-0030.bin"
private noncomputable def ep1111_31 : Blocks := edgeBlocks% "full/vectors/1111-E-0031.bin"
private noncomputable def ep1111_32 : Blocks := edgeBlocks% "full/vectors/1111-E-0032.bin"
private noncomputable def ep1111_33 : Blocks := edgeBlocks% "full/vectors/1111-E-0033.bin"
private noncomputable def ep1111_34 : Blocks := edgeBlocks% "full/vectors/1111-E-0034.bin"
private noncomputable def ep1111_35 : Blocks := edgeBlocks% "full/vectors/1111-E-0035.bin"
private noncomputable def ep1111_36 : Blocks := edgeBlocks% "full/vectors/1111-E-0036.bin"
private noncomputable def ep1111_37 : Blocks := edgeBlocks% "full/vectors/1111-E-0037.bin"
private noncomputable def ep1111_38 : Blocks := edgeBlocks% "full/vectors/1111-E-0038.bin"
private noncomputable def ep1111_39 : Blocks := edgeBlocks% "full/vectors/1111-E-0039.bin"
private noncomputable def ep1111_40 : Blocks := edgeBlocks% "full/vectors/1111-E-0040.bin"
private noncomputable def ep1111_41 : Blocks := edgeBlocks% "full/vectors/1111-E-0041.bin"
private noncomputable def ep1111_42 : Blocks := edgeBlocks% "full/vectors/1111-E-0042.bin"
private noncomputable def ep1111_43 : Blocks := edgeBlocks% "full/vectors/1111-E-0043.bin"
private noncomputable def ep1111_44 : Blocks := edgeBlocks% "full/vectors/1111-E-0044.bin"
private noncomputable def ep1111_45 : Blocks := edgeBlocks% "full/vectors/1111-E-0045.bin"
private noncomputable def ep1111_46 : Blocks := edgeBlocks% "full/vectors/1111-E-0046.bin"
private noncomputable def ep1111_47 : Blocks := edgeBlocks% "full/vectors/1111-E-0047.bin"
private noncomputable def ep1111_48 : Blocks := edgeBlocks% "full/vectors/1111-E-0048.bin"
private noncomputable def ep1111_49 : Blocks := edgeBlocks% "full/vectors/1111-E-0049.bin"
private noncomputable def ep1111_50 : Blocks := edgeBlocks% "full/vectors/1111-E-0050.bin"
private noncomputable def ep1111_51 : Blocks := edgeBlocks% "full/vectors/1111-E-0051.bin"
private noncomputable def ep1111_52 : Blocks := edgeBlocks% "full/vectors/1111-E-0052.bin"
private noncomputable def ep1111_53 : Blocks := edgeBlocks% "full/vectors/1111-E-0053.bin"
private noncomputable def ep1111_54 : Blocks := edgeBlocks% "full/vectors/1111-E-0054.bin"
private noncomputable def ep1111_55 : Blocks := edgeBlocks% "full/vectors/1111-E-0055.bin"
private noncomputable def ep1111_56 : Blocks := edgeBlocks% "full/vectors/1111-E-0056.bin"
private noncomputable def ep1111_57 : Blocks := edgeBlocks% "full/vectors/1111-E-0057.bin"
private noncomputable def ep1111_58 : Blocks := edgeBlocks% "full/vectors/1111-E-0058.bin"
private noncomputable def ep1111_59 : Blocks := edgeBlocks% "full/vectors/1111-E-0059.bin"
private noncomputable def ep1111_60 : Blocks := edgeBlocks% "full/vectors/1111-E-0060.bin"
private noncomputable def ep1111_61 : Blocks := edgeBlocks% "full/vectors/1111-E-0061.bin"
private noncomputable def ep1111_62 : Blocks := edgeBlocks% "full/vectors/1111-E-0062.bin"
private noncomputable def ep1111_63 : Blocks := edgeBlocks% "full/vectors/1111-E-0063.bin"
private noncomputable def ep1111_64 : Blocks := edgeBlocks% "full/vectors/1111-E-0064.bin"
private noncomputable def ep1111_65 : Blocks := edgeBlocks% "full/vectors/1111-E-0065.bin"
private noncomputable def ep1111_66 : Blocks := edgeBlocks% "full/vectors/1111-E-0066.bin"
noncomputable def ep1111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1111_0 ep1111_1) (Blocks.join ep1111_2 ep1111_3)) (Blocks.join (Blocks.join ep1111_4 ep1111_5) (Blocks.join ep1111_6 ep1111_7))) (Blocks.join (Blocks.join (Blocks.join ep1111_8 ep1111_9) (Blocks.join ep1111_10 ep1111_11)) (Blocks.join (Blocks.join ep1111_12 ep1111_13) (Blocks.join ep1111_14 ep1111_15)))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1111_16 ep1111_17) (Blocks.join ep1111_18 ep1111_19)) (Blocks.join (Blocks.join ep1111_20 ep1111_21) (Blocks.join ep1111_22 ep1111_23))) (Blocks.join (Blocks.join (Blocks.join ep1111_24 ep1111_25) (Blocks.join ep1111_26 ep1111_27)) (Blocks.join (Blocks.join ep1111_28 ep1111_29) (Blocks.join ep1111_30 (Blocks.join ep1111_31 ep1111_32)))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1111_33 ep1111_34) (Blocks.join ep1111_35 ep1111_36)) (Blocks.join (Blocks.join ep1111_37 ep1111_38) (Blocks.join ep1111_39 ep1111_40))) (Blocks.join (Blocks.join (Blocks.join ep1111_41 ep1111_42) (Blocks.join ep1111_43 ep1111_44)) (Blocks.join (Blocks.join ep1111_45 ep1111_46) (Blocks.join ep1111_47 (Blocks.join ep1111_48 ep1111_49))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep1111_50 ep1111_51) (Blocks.join ep1111_52 ep1111_53)) (Blocks.join (Blocks.join ep1111_54 ep1111_55) (Blocks.join ep1111_56 ep1111_57))) (Blocks.join (Blocks.join (Blocks.join ep1111_58 ep1111_59) (Blocks.join ep1111_60 ep1111_61)) (Blocks.join (Blocks.join ep1111_62 ep1111_63) (Blocks.join ep1111_64 (Blocks.join ep1111_65 ep1111_66)))))))
private def ptsp1111 : List ℤ := [((2:ℤ)^1409+0),((2:ℤ)^1409+1),((2:ℤ)^1409+2),((2:ℤ)^1409+3),((2:ℤ)^1409+4),((2:ℤ)^1409+5),((2:ℤ)^1409+6),((2:ℤ)^1409+7),((2:ℤ)^1409+8),((2:ℤ)^1409+9),((2:ℤ)^1409+10)]
private theorem boundp1111 : 2^vp111.size*absSum vp111.list + ((2:ℤ)^11468*absSum vp1111.list+absSum ep1111.list) < (2:ℤ)^14534 := by decide +kernel
private theorem pointp1111_0 : fastHom 1 ((2:ℤ)^1409+0) vp111 = ((2:ℤ)^11468)*vp1111.subst ((2:ℤ)^1409+0)+ep1111.subst ((2:ℤ)^1409+0) := by decide +kernel
private theorem pointp1111_1 : fastHom 1 ((2:ℤ)^1409+1) vp111 = ((2:ℤ)^11468)*vp1111.subst ((2:ℤ)^1409+1)+ep1111.subst ((2:ℤ)^1409+1) := by decide +kernel
private theorem pointp1111_2 : fastHom 1 ((2:ℤ)^1409+2) vp111 = ((2:ℤ)^11468)*vp1111.subst ((2:ℤ)^1409+2)+ep1111.subst ((2:ℤ)^1409+2) := by decide +kernel
private theorem pointp1111_3 : fastHom 1 ((2:ℤ)^1409+3) vp111 = ((2:ℤ)^11468)*vp1111.subst ((2:ℤ)^1409+3)+ep1111.subst ((2:ℤ)^1409+3) := by decide +kernel
private theorem pointp1111_4 : fastHom 1 ((2:ℤ)^1409+4) vp111 = ((2:ℤ)^11468)*vp1111.subst ((2:ℤ)^1409+4)+ep1111.subst ((2:ℤ)^1409+4) := by decide +kernel
private theorem pointp1111_5 : fastHom 1 ((2:ℤ)^1409+5) vp111 = ((2:ℤ)^11468)*vp1111.subst ((2:ℤ)^1409+5)+ep1111.subst ((2:ℤ)^1409+5) := by decide +kernel
private theorem pointp1111_6 : fastHom 1 ((2:ℤ)^1409+6) vp111 = ((2:ℤ)^11468)*vp1111.subst ((2:ℤ)^1409+6)+ep1111.subst ((2:ℤ)^1409+6) := by decide +kernel
private theorem pointp1111_7 : fastHom 1 ((2:ℤ)^1409+7) vp111 = ((2:ℤ)^11468)*vp1111.subst ((2:ℤ)^1409+7)+ep1111.subst ((2:ℤ)^1409+7) := by decide +kernel
private theorem pointp1111_8 : fastHom 1 ((2:ℤ)^1409+8) vp111 = ((2:ℤ)^11468)*vp1111.subst ((2:ℤ)^1409+8)+ep1111.subst ((2:ℤ)^1409+8) := by decide +kernel
private theorem pointp1111_9 : fastHom 1 ((2:ℤ)^1409+9) vp111 = ((2:ℤ)^11468)*vp1111.subst ((2:ℤ)^1409+9)+ep1111.subst ((2:ℤ)^1409+9) := by decide +kernel
private theorem pointp1111_10 : fastHom 1 ((2:ℤ)^1409+10) vp111 = ((2:ℤ)^11468)*vp1111.subst ((2:ℤ)^1409+10)+ep1111.subst ((2:ℤ)^1409+10) := by decide +kernel
private theorem checkp1111 (x:ℤ) (hx:x ∈ ptsp1111) : fastHom 1 x vp111 = ((2:ℤ)^11468)*vp1111.subst x+ep1111.subst x := by
  simp only [ptsp1111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pointp1111_0
  · exact pointp1111_1
  · exact pointp1111_2
  · exact pointp1111_3
  · exact pointp1111_4
  · exact pointp1111_5
  · exact pointp1111_6
  · exact pointp1111_7
  · exact pointp1111_8
  · exact pointp1111_9
  · exact pointp1111_10
private theorem idp1111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp111.list =
    C ((2:ℤ)^11468) * horner X vp1111.list + horner X ep1111.list := by
  apply edge_identity (B := (2:ℤ)^14534) (by decide) (by positivity) (by positivity) boundp1111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp1111 (by decide +kernel)
  · have h : ptsp1111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp1111.trans_le (by decide +kernel)
  · exact checkp1111
private theorem bp1111 : Branch 1 (-7167761639/1024000000 : ℚ) vp111 := by
  apply branch_checked idp1111 (by positivity) (by decide +kernel)
  rw [show 2*(-7167761639/1024000000 : ℚ) - ((1:ℤ):ℚ) = (-7679761639/512000000 : ℚ) by norm_num]
  exact coverp1111
theorem coverp111 : Covers (-7167761639/1024000000 : ℚ) vp111 := join_branches bp1110 bp1111
end NextProof.EdgeFull

