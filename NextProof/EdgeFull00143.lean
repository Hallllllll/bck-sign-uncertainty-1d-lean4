import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp111111_0 : Blocks := edgeBlocks% "full/vectors/111111-V-0000.bin"
private noncomputable def vp111111_1 : Blocks := edgeBlocks% "full/vectors/111111-V-0001.bin"
private noncomputable def vp111111_2 : Blocks := edgeBlocks% "full/vectors/111111-V-0002.bin"
private noncomputable def vp111111_3 : Blocks := edgeBlocks% "full/vectors/111111-V-0003.bin"
private noncomputable def vp111111_4 : Blocks := edgeBlocks% "full/vectors/111111-V-0004.bin"
private noncomputable def vp111111_5 : Blocks := edgeBlocks% "full/vectors/111111-V-0005.bin"
private noncomputable def vp111111_6 : Blocks := edgeBlocks% "full/vectors/111111-V-0006.bin"
private noncomputable def vp111111_7 : Blocks := edgeBlocks% "full/vectors/111111-V-0007.bin"
private noncomputable def vp111111_8 : Blocks := edgeBlocks% "full/vectors/111111-V-0008.bin"
private noncomputable def vp111111_9 : Blocks := edgeBlocks% "full/vectors/111111-V-0009.bin"
private noncomputable def vp111111_10 : Blocks := edgeBlocks% "full/vectors/111111-V-0010.bin"
noncomputable def vp111111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp111111_0 vp111111_1) (Blocks.join vp111111_2 (Blocks.join vp111111_3 vp111111_4))) (Blocks.join (Blocks.join vp111111_5 (Blocks.join vp111111_6 vp111111_7)) (Blocks.join vp111111_8 (Blocks.join vp111111_9 vp111111_10))))
theorem coverp111111 : Covers (-8063761639/128000000 : ℚ) vp111111 := cover_leaf (by decide +kernel)
private noncomputable def vp1111101_0 : Blocks := edgeBlocks% "full/vectors/1111101-V-0000.bin"
private noncomputable def vp1111101_1 : Blocks := edgeBlocks% "full/vectors/1111101-V-0001.bin"
private noncomputable def vp1111101_2 : Blocks := edgeBlocks% "full/vectors/1111101-V-0002.bin"
private noncomputable def vp1111101_3 : Blocks := edgeBlocks% "full/vectors/1111101-V-0003.bin"
private noncomputable def vp1111101_4 : Blocks := edgeBlocks% "full/vectors/1111101-V-0004.bin"
private noncomputable def vp1111101_5 : Blocks := edgeBlocks% "full/vectors/1111101-V-0005.bin"
noncomputable def vp1111101 : Blocks := (Blocks.join (Blocks.join vp1111101_0 (Blocks.join vp1111101_1 vp1111101_2)) (Blocks.join vp1111101_3 (Blocks.join vp1111101_4 vp1111101_5)))
theorem coverp1111101 : Covers (-7999761639/64000000 : ℚ) vp1111101 := cover_leaf (by decide +kernel)
private noncomputable def vp1111100_0 : Blocks := edgeBlocks% "full/vectors/1111100-V-0000.bin"
private noncomputable def vp1111100_1 : Blocks := edgeBlocks% "full/vectors/1111100-V-0001.bin"
private noncomputable def vp1111100_2 : Blocks := edgeBlocks% "full/vectors/1111100-V-0002.bin"
private noncomputable def vp1111100_3 : Blocks := edgeBlocks% "full/vectors/1111100-V-0003.bin"
private noncomputable def vp1111100_4 : Blocks := edgeBlocks% "full/vectors/1111100-V-0004.bin"
private noncomputable def vp1111100_5 : Blocks := edgeBlocks% "full/vectors/1111100-V-0005.bin"
noncomputable def vp1111100 : Blocks := (Blocks.join (Blocks.join vp1111100_0 (Blocks.join vp1111100_1 vp1111100_2)) (Blocks.join vp1111100_3 (Blocks.join vp1111100_4 vp1111100_5)))
theorem coverp1111100 : Covers (-7935761639/64000000 : ℚ) vp1111100 := cover_leaf (by decide +kernel)
private noncomputable def vp111110_0 : Blocks := edgeBlocks% "full/vectors/111110-V-0000.bin"
private noncomputable def vp111110_1 : Blocks := edgeBlocks% "full/vectors/111110-V-0001.bin"
private noncomputable def vp111110_2 : Blocks := edgeBlocks% "full/vectors/111110-V-0002.bin"
private noncomputable def vp111110_3 : Blocks := edgeBlocks% "full/vectors/111110-V-0003.bin"
private noncomputable def vp111110_4 : Blocks := edgeBlocks% "full/vectors/111110-V-0004.bin"
private noncomputable def vp111110_5 : Blocks := edgeBlocks% "full/vectors/111110-V-0005.bin"
private noncomputable def vp111110_6 : Blocks := edgeBlocks% "full/vectors/111110-V-0006.bin"
private noncomputable def vp111110_7 : Blocks := edgeBlocks% "full/vectors/111110-V-0007.bin"
private noncomputable def vp111110_8 : Blocks := edgeBlocks% "full/vectors/111110-V-0008.bin"
private noncomputable def vp111110_9 : Blocks := edgeBlocks% "full/vectors/111110-V-0009.bin"
private noncomputable def vp111110_10 : Blocks := edgeBlocks% "full/vectors/111110-V-0010.bin"
noncomputable def vp111110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp111110_0 vp111110_1) (Blocks.join vp111110_2 (Blocks.join vp111110_3 vp111110_4))) (Blocks.join (Blocks.join vp111110_5 (Blocks.join vp111110_6 vp111110_7)) (Blocks.join vp111110_8 (Blocks.join vp111110_9 vp111110_10))))
private theorem bp1111100 : Branch 0 (-7935761639/128000000 : ℚ) vp111110 := by
  apply branch_left_normalized (c:=vp1111100) (k:=0) (m:=723) (by decide +kernel)
  rw [show 2*(-7935761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-7935761639/64000000 : ℚ) by norm_num]
  exact coverp1111100
private noncomputable def ep1111101_0 : Blocks := edgeBlocks% "full/vectors/1111101-E-0000.bin"
private noncomputable def ep1111101_1 : Blocks := edgeBlocks% "full/vectors/1111101-E-0001.bin"
private noncomputable def ep1111101_2 : Blocks := edgeBlocks% "full/vectors/1111101-E-0002.bin"
private noncomputable def ep1111101_3 : Blocks := edgeBlocks% "full/vectors/1111101-E-0003.bin"
private noncomputable def ep1111101_4 : Blocks := edgeBlocks% "full/vectors/1111101-E-0004.bin"
private noncomputable def ep1111101_5 : Blocks := edgeBlocks% "full/vectors/1111101-E-0005.bin"
private noncomputable def ep1111101_6 : Blocks := edgeBlocks% "full/vectors/1111101-E-0006.bin"
private noncomputable def ep1111101_7 : Blocks := edgeBlocks% "full/vectors/1111101-E-0007.bin"
private noncomputable def ep1111101_8 : Blocks := edgeBlocks% "full/vectors/1111101-E-0008.bin"
private noncomputable def ep1111101_9 : Blocks := edgeBlocks% "full/vectors/1111101-E-0009.bin"
private noncomputable def ep1111101_10 : Blocks := edgeBlocks% "full/vectors/1111101-E-0010.bin"
noncomputable def ep1111101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1111101_0 ep1111101_1) (Blocks.join ep1111101_2 (Blocks.join ep1111101_3 ep1111101_4))) (Blocks.join (Blocks.join ep1111101_5 (Blocks.join ep1111101_6 ep1111101_7)) (Blocks.join ep1111101_8 (Blocks.join ep1111101_9 ep1111101_10))))
private theorem idp1111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp111110.list =
    C ((2:ℤ)^1752) * horner X vp1111101.list + horner X ep1111101.list := by
  exact edge_identity (B := (2:ℤ)^2233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1111101 : Branch 1 (-7935761639/128000000 : ℚ) vp111110 := by
  apply branch_checked idp1111101 (by positivity) (by decide +kernel)
  rw [show 2*(-7935761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-7999761639/64000000 : ℚ) by norm_num]
  exact coverp1111101
theorem coverp111110 : Covers (-7935761639/128000000 : ℚ) vp111110 := join_branches bp1111100 bp1111101
private noncomputable def vp11111_0 : Blocks := edgeBlocks% "full/vectors/11111-V-0000.bin"
private noncomputable def vp11111_1 : Blocks := edgeBlocks% "full/vectors/11111-V-0001.bin"
private noncomputable def vp11111_2 : Blocks := edgeBlocks% "full/vectors/11111-V-0002.bin"
private noncomputable def vp11111_3 : Blocks := edgeBlocks% "full/vectors/11111-V-0003.bin"
private noncomputable def vp11111_4 : Blocks := edgeBlocks% "full/vectors/11111-V-0004.bin"
private noncomputable def vp11111_5 : Blocks := edgeBlocks% "full/vectors/11111-V-0005.bin"
private noncomputable def vp11111_6 : Blocks := edgeBlocks% "full/vectors/11111-V-0006.bin"
private noncomputable def vp11111_7 : Blocks := edgeBlocks% "full/vectors/11111-V-0007.bin"
private noncomputable def vp11111_8 : Blocks := edgeBlocks% "full/vectors/11111-V-0008.bin"
private noncomputable def vp11111_9 : Blocks := edgeBlocks% "full/vectors/11111-V-0009.bin"
private noncomputable def vp11111_10 : Blocks := edgeBlocks% "full/vectors/11111-V-0010.bin"
private noncomputable def vp11111_11 : Blocks := edgeBlocks% "full/vectors/11111-V-0011.bin"
private noncomputable def vp11111_12 : Blocks := edgeBlocks% "full/vectors/11111-V-0012.bin"
private noncomputable def vp11111_13 : Blocks := edgeBlocks% "full/vectors/11111-V-0013.bin"
private noncomputable def vp11111_14 : Blocks := edgeBlocks% "full/vectors/11111-V-0014.bin"
private noncomputable def vp11111_15 : Blocks := edgeBlocks% "full/vectors/11111-V-0015.bin"
private noncomputable def vp11111_16 : Blocks := edgeBlocks% "full/vectors/11111-V-0016.bin"
private noncomputable def vp11111_17 : Blocks := edgeBlocks% "full/vectors/11111-V-0017.bin"
private noncomputable def vp11111_18 : Blocks := edgeBlocks% "full/vectors/11111-V-0018.bin"
private noncomputable def vp11111_19 : Blocks := edgeBlocks% "full/vectors/11111-V-0019.bin"
noncomputable def vp11111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp11111_0 vp11111_1) (Blocks.join vp11111_2 (Blocks.join vp11111_3 vp11111_4))) (Blocks.join (Blocks.join vp11111_5 vp11111_6) (Blocks.join vp11111_7 (Blocks.join vp11111_8 vp11111_9)))) (Blocks.join (Blocks.join (Blocks.join vp11111_10 vp11111_11) (Blocks.join vp11111_12 (Blocks.join vp11111_13 vp11111_14))) (Blocks.join (Blocks.join vp11111_15 vp11111_16) (Blocks.join vp11111_17 (Blocks.join vp11111_18 vp11111_19)))))
private theorem bp111110 : Branch 0 (-7935761639/256000000 : ℚ) vp11111 := by
  apply branch_left_normalized (c:=vp111110) (k:=0) (m:=1382) (by decide +kernel)
  rw [show 2*(-7935761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-7935761639/128000000 : ℚ) by norm_num]
  exact coverp111110
private noncomputable def ep111111_0 : Blocks := edgeBlocks% "full/vectors/111111-E-0000.bin"
private noncomputable def ep111111_1 : Blocks := edgeBlocks% "full/vectors/111111-E-0001.bin"
private noncomputable def ep111111_2 : Blocks := edgeBlocks% "full/vectors/111111-E-0002.bin"
private noncomputable def ep111111_3 : Blocks := edgeBlocks% "full/vectors/111111-E-0003.bin"
private noncomputable def ep111111_4 : Blocks := edgeBlocks% "full/vectors/111111-E-0004.bin"
private noncomputable def ep111111_5 : Blocks := edgeBlocks% "full/vectors/111111-E-0005.bin"
private noncomputable def ep111111_6 : Blocks := edgeBlocks% "full/vectors/111111-E-0006.bin"
private noncomputable def ep111111_7 : Blocks := edgeBlocks% "full/vectors/111111-E-0007.bin"
private noncomputable def ep111111_8 : Blocks := edgeBlocks% "full/vectors/111111-E-0008.bin"
private noncomputable def ep111111_9 : Blocks := edgeBlocks% "full/vectors/111111-E-0009.bin"
private noncomputable def ep111111_10 : Blocks := edgeBlocks% "full/vectors/111111-E-0010.bin"
private noncomputable def ep111111_11 : Blocks := edgeBlocks% "full/vectors/111111-E-0011.bin"
private noncomputable def ep111111_12 : Blocks := edgeBlocks% "full/vectors/111111-E-0012.bin"
private noncomputable def ep111111_13 : Blocks := edgeBlocks% "full/vectors/111111-E-0013.bin"
private noncomputable def ep111111_14 : Blocks := edgeBlocks% "full/vectors/111111-E-0014.bin"
private noncomputable def ep111111_15 : Blocks := edgeBlocks% "full/vectors/111111-E-0015.bin"
private noncomputable def ep111111_16 : Blocks := edgeBlocks% "full/vectors/111111-E-0016.bin"
private noncomputable def ep111111_17 : Blocks := edgeBlocks% "full/vectors/111111-E-0017.bin"
private noncomputable def ep111111_18 : Blocks := edgeBlocks% "full/vectors/111111-E-0018.bin"
private noncomputable def ep111111_19 : Blocks := edgeBlocks% "full/vectors/111111-E-0019.bin"
noncomputable def ep111111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep111111_0 ep111111_1) (Blocks.join ep111111_2 (Blocks.join ep111111_3 ep111111_4))) (Blocks.join (Blocks.join ep111111_5 ep111111_6) (Blocks.join ep111111_7 (Blocks.join ep111111_8 ep111111_9)))) (Blocks.join (Blocks.join (Blocks.join ep111111_10 ep111111_11) (Blocks.join ep111111_12 (Blocks.join ep111111_13 ep111111_14))) (Blocks.join (Blocks.join ep111111_15 ep111111_16) (Blocks.join ep111111_17 (Blocks.join ep111111_18 ep111111_19)))))
private theorem idp111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11111.list =
    C ((2:ℤ)^3244) * horner X vp111111.list + horner X ep111111.list := by
  exact edge_identity (B := (2:ℤ)^4093) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111111 : Branch 1 (-7935761639/256000000 : ℚ) vp11111 := by
  apply branch_checked idp111111 (by positivity) (by decide +kernel)
  rw [show 2*(-7935761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-8063761639/128000000 : ℚ) by norm_num]
  exact coverp111111
theorem coverp11111 : Covers (-7935761639/256000000 : ℚ) vp11111 := join_branches bp111110 bp111111
private noncomputable def vp1111011_0 : Blocks := edgeBlocks% "full/vectors/1111011-V-0000.bin"
private noncomputable def vp1111011_1 : Blocks := edgeBlocks% "full/vectors/1111011-V-0001.bin"
private noncomputable def vp1111011_2 : Blocks := edgeBlocks% "full/vectors/1111011-V-0002.bin"
private noncomputable def vp1111011_3 : Blocks := edgeBlocks% "full/vectors/1111011-V-0003.bin"
private noncomputable def vp1111011_4 : Blocks := edgeBlocks% "full/vectors/1111011-V-0004.bin"
private noncomputable def vp1111011_5 : Blocks := edgeBlocks% "full/vectors/1111011-V-0005.bin"
noncomputable def vp1111011 : Blocks := (Blocks.join (Blocks.join vp1111011_0 (Blocks.join vp1111011_1 vp1111011_2)) (Blocks.join vp1111011_3 (Blocks.join vp1111011_4 vp1111011_5)))
theorem coverp1111011 : Covers (-7871761639/64000000 : ℚ) vp1111011 := cover_leaf (by decide +kernel)
private noncomputable def vp11110101_0 : Blocks := edgeBlocks% "full/vectors/11110101-V-0000.bin"
private noncomputable def vp11110101_1 : Blocks := edgeBlocks% "full/vectors/11110101-V-0001.bin"
private noncomputable def vp11110101_2 : Blocks := edgeBlocks% "full/vectors/11110101-V-0002.bin"
noncomputable def vp11110101 : Blocks := (Blocks.join vp11110101_0 (Blocks.join vp11110101_1 vp11110101_2))
theorem coverp11110101 : Covers (-7839761639/32000000 : ℚ) vp11110101 := cover_leaf (by decide +kernel)
private noncomputable def vp11110100_0 : Blocks := edgeBlocks% "full/vectors/11110100-V-0000.bin"
private noncomputable def vp11110100_1 : Blocks := edgeBlocks% "full/vectors/11110100-V-0001.bin"
private noncomputable def vp11110100_2 : Blocks := edgeBlocks% "full/vectors/11110100-V-0002.bin"
noncomputable def vp11110100 : Blocks := (Blocks.join vp11110100_0 (Blocks.join vp11110100_1 vp11110100_2))
theorem coverp11110100 : Covers (-7807761639/32000000 : ℚ) vp11110100 := cover_leaf (by decide +kernel)
private noncomputable def vp1111010_0 : Blocks := edgeBlocks% "full/vectors/1111010-V-0000.bin"
private noncomputable def vp1111010_1 : Blocks := edgeBlocks% "full/vectors/1111010-V-0001.bin"
private noncomputable def vp1111010_2 : Blocks := edgeBlocks% "full/vectors/1111010-V-0002.bin"
private noncomputable def vp1111010_3 : Blocks := edgeBlocks% "full/vectors/1111010-V-0003.bin"
private noncomputable def vp1111010_4 : Blocks := edgeBlocks% "full/vectors/1111010-V-0004.bin"
private noncomputable def vp1111010_5 : Blocks := edgeBlocks% "full/vectors/1111010-V-0005.bin"
noncomputable def vp1111010 : Blocks := (Blocks.join (Blocks.join vp1111010_0 (Blocks.join vp1111010_1 vp1111010_2)) (Blocks.join vp1111010_3 (Blocks.join vp1111010_4 vp1111010_5)))
private theorem bp11110100 : Branch 0 (-7807761639/64000000 : ℚ) vp1111010 := by
  apply branch_left_normalized (c:=vp11110100) (k:=0) (m:=379) (by decide +kernel)
  rw [show 2*(-7807761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7807761639/32000000 : ℚ) by norm_num]
  exact coverp11110100
private noncomputable def ep11110101_0 : Blocks := edgeBlocks% "full/vectors/11110101-E-0000.bin"
private noncomputable def ep11110101_1 : Blocks := edgeBlocks% "full/vectors/11110101-E-0001.bin"
private noncomputable def ep11110101_2 : Blocks := edgeBlocks% "full/vectors/11110101-E-0002.bin"
private noncomputable def ep11110101_3 : Blocks := edgeBlocks% "full/vectors/11110101-E-0003.bin"
private noncomputable def ep11110101_4 : Blocks := edgeBlocks% "full/vectors/11110101-E-0004.bin"
private noncomputable def ep11110101_5 : Blocks := edgeBlocks% "full/vectors/11110101-E-0005.bin"
noncomputable def ep11110101 : Blocks := (Blocks.join (Blocks.join ep11110101_0 (Blocks.join ep11110101_1 ep11110101_2)) (Blocks.join ep11110101_3 (Blocks.join ep11110101_4 ep11110101_5)))
private theorem idp11110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1111010.list =
    C ((2:ℤ)^915) * horner X vp11110101.list + horner X ep11110101.list := by
  exact edge_identity (B := (2:ℤ)^1212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11110101 : Branch 1 (-7807761639/64000000 : ℚ) vp1111010 := by
  apply branch_checked idp11110101 (by positivity) (by decide +kernel)
  rw [show 2*(-7807761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7839761639/32000000 : ℚ) by norm_num]
  exact coverp11110101
theorem coverp1111010 : Covers (-7807761639/64000000 : ℚ) vp1111010 := join_branches bp11110100 bp11110101
private noncomputable def vp111101_0 : Blocks := edgeBlocks% "full/vectors/111101-V-0000.bin"
private noncomputable def vp111101_1 : Blocks := edgeBlocks% "full/vectors/111101-V-0001.bin"
private noncomputable def vp111101_2 : Blocks := edgeBlocks% "full/vectors/111101-V-0002.bin"
private noncomputable def vp111101_3 : Blocks := edgeBlocks% "full/vectors/111101-V-0003.bin"
private noncomputable def vp111101_4 : Blocks := edgeBlocks% "full/vectors/111101-V-0004.bin"
private noncomputable def vp111101_5 : Blocks := edgeBlocks% "full/vectors/111101-V-0005.bin"
private noncomputable def vp111101_6 : Blocks := edgeBlocks% "full/vectors/111101-V-0006.bin"
private noncomputable def vp111101_7 : Blocks := edgeBlocks% "full/vectors/111101-V-0007.bin"
private noncomputable def vp111101_8 : Blocks := edgeBlocks% "full/vectors/111101-V-0008.bin"
private noncomputable def vp111101_9 : Blocks := edgeBlocks% "full/vectors/111101-V-0009.bin"
private noncomputable def vp111101_10 : Blocks := edgeBlocks% "full/vectors/111101-V-0010.bin"
private noncomputable def vp111101_11 : Blocks := edgeBlocks% "full/vectors/111101-V-0011.bin"
noncomputable def vp111101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp111101_0 (Blocks.join vp111101_1 vp111101_2)) (Blocks.join vp111101_3 (Blocks.join vp111101_4 vp111101_5))) (Blocks.join (Blocks.join vp111101_6 (Blocks.join vp111101_7 vp111101_8)) (Blocks.join vp111101_9 (Blocks.join vp111101_10 vp111101_11))))
private theorem bp1111010 : Branch 0 (-7807761639/128000000 : ℚ) vp111101 := by
  apply branch_left_normalized (c:=vp1111010) (k:=0) (m:=729) (by decide +kernel)
  rw [show 2*(-7807761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-7807761639/64000000 : ℚ) by norm_num]
  exact coverp1111010
private noncomputable def ep1111011_0 : Blocks := edgeBlocks% "full/vectors/1111011-E-0000.bin"
private noncomputable def ep1111011_1 : Blocks := edgeBlocks% "full/vectors/1111011-E-0001.bin"
private noncomputable def ep1111011_2 : Blocks := edgeBlocks% "full/vectors/1111011-E-0002.bin"
private noncomputable def ep1111011_3 : Blocks := edgeBlocks% "full/vectors/1111011-E-0003.bin"
private noncomputable def ep1111011_4 : Blocks := edgeBlocks% "full/vectors/1111011-E-0004.bin"
private noncomputable def ep1111011_5 : Blocks := edgeBlocks% "full/vectors/1111011-E-0005.bin"
private noncomputable def ep1111011_6 : Blocks := edgeBlocks% "full/vectors/1111011-E-0006.bin"
private noncomputable def ep1111011_7 : Blocks := edgeBlocks% "full/vectors/1111011-E-0007.bin"
private noncomputable def ep1111011_8 : Blocks := edgeBlocks% "full/vectors/1111011-E-0008.bin"
private noncomputable def ep1111011_9 : Blocks := edgeBlocks% "full/vectors/1111011-E-0009.bin"
private noncomputable def ep1111011_10 : Blocks := edgeBlocks% "full/vectors/1111011-E-0010.bin"
private noncomputable def ep1111011_11 : Blocks := edgeBlocks% "full/vectors/1111011-E-0011.bin"
noncomputable def ep1111011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1111011_0 (Blocks.join ep1111011_1 ep1111011_2)) (Blocks.join ep1111011_3 (Blocks.join ep1111011_4 ep1111011_5))) (Blocks.join (Blocks.join ep1111011_6 (Blocks.join ep1111011_7 ep1111011_8)) (Blocks.join ep1111011_9 (Blocks.join ep1111011_10 ep1111011_11))))
private theorem idp1111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp111101.list =
    C ((2:ℤ)^1790) * horner X vp1111011.list + horner X ep1111011.list := by
  exact edge_identity (B := (2:ℤ)^2275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1111011 : Branch 1 (-7807761639/128000000 : ℚ) vp111101 := by
  apply branch_checked idp1111011 (by positivity) (by decide +kernel)
  rw [show 2*(-7807761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-7871761639/64000000 : ℚ) by norm_num]
  exact coverp1111011
theorem coverp111101 : Covers (-7807761639/128000000 : ℚ) vp111101 := join_branches bp1111010 bp1111011
private noncomputable def vp11110011_0 : Blocks := edgeBlocks% "full/vectors/11110011-V-0000.bin"
private noncomputable def vp11110011_1 : Blocks := edgeBlocks% "full/vectors/11110011-V-0001.bin"
private noncomputable def vp11110011_2 : Blocks := edgeBlocks% "full/vectors/11110011-V-0002.bin"
noncomputable def vp11110011 : Blocks := (Blocks.join vp11110011_0 (Blocks.join vp11110011_1 vp11110011_2))
theorem coverp11110011 : Covers (-7775761639/32000000 : ℚ) vp11110011 := cover_leaf (by decide +kernel)
private noncomputable def vp11110010_0 : Blocks := edgeBlocks% "full/vectors/11110010-V-0000.bin"
private noncomputable def vp11110010_1 : Blocks := edgeBlocks% "full/vectors/11110010-V-0001.bin"
private noncomputable def vp11110010_2 : Blocks := edgeBlocks% "full/vectors/11110010-V-0002.bin"
noncomputable def vp11110010 : Blocks := (Blocks.join vp11110010_0 (Blocks.join vp11110010_1 vp11110010_2))
theorem coverp11110010 : Covers (-7743761639/32000000 : ℚ) vp11110010 := cover_leaf (by decide +kernel)
private noncomputable def vp1111001_0 : Blocks := edgeBlocks% "full/vectors/1111001-V-0000.bin"
private noncomputable def vp1111001_1 : Blocks := edgeBlocks% "full/vectors/1111001-V-0001.bin"
private noncomputable def vp1111001_2 : Blocks := edgeBlocks% "full/vectors/1111001-V-0002.bin"
private noncomputable def vp1111001_3 : Blocks := edgeBlocks% "full/vectors/1111001-V-0003.bin"
private noncomputable def vp1111001_4 : Blocks := edgeBlocks% "full/vectors/1111001-V-0004.bin"
private noncomputable def vp1111001_5 : Blocks := edgeBlocks% "full/vectors/1111001-V-0005.bin"
noncomputable def vp1111001 : Blocks := (Blocks.join (Blocks.join vp1111001_0 (Blocks.join vp1111001_1 vp1111001_2)) (Blocks.join vp1111001_3 (Blocks.join vp1111001_4 vp1111001_5)))
private theorem bp11110010 : Branch 0 (-7743761639/64000000 : ℚ) vp1111001 := by
  apply branch_left_normalized (c:=vp11110010) (k:=0) (m:=380) (by decide +kernel)
  rw [show 2*(-7743761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7743761639/32000000 : ℚ) by norm_num]
  exact coverp11110010
private noncomputable def ep11110011_0 : Blocks := edgeBlocks% "full/vectors/11110011-E-0000.bin"
private noncomputable def ep11110011_1 : Blocks := edgeBlocks% "full/vectors/11110011-E-0001.bin"
private noncomputable def ep11110011_2 : Blocks := edgeBlocks% "full/vectors/11110011-E-0002.bin"
private noncomputable def ep11110011_3 : Blocks := edgeBlocks% "full/vectors/11110011-E-0003.bin"
private noncomputable def ep11110011_4 : Blocks := edgeBlocks% "full/vectors/11110011-E-0004.bin"
private noncomputable def ep11110011_5 : Blocks := edgeBlocks% "full/vectors/11110011-E-0005.bin"
noncomputable def ep11110011 : Blocks := (Blocks.join (Blocks.join ep11110011_0 (Blocks.join ep11110011_1 ep11110011_2)) (Blocks.join ep11110011_3 (Blocks.join ep11110011_4 ep11110011_5)))
private theorem idp11110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1111001.list =
    C ((2:ℤ)^917) * horner X vp11110011.list + horner X ep11110011.list := by
  exact edge_identity (B := (2:ℤ)^1215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11110011 : Branch 1 (-7743761639/64000000 : ℚ) vp1111001 := by
  apply branch_checked idp11110011 (by positivity) (by decide +kernel)
  rw [show 2*(-7743761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7775761639/32000000 : ℚ) by norm_num]
  exact coverp11110011
theorem coverp1111001 : Covers (-7743761639/64000000 : ℚ) vp1111001 := join_branches bp11110010 bp11110011
private noncomputable def vp11110001_0 : Blocks := edgeBlocks% "full/vectors/11110001-V-0000.bin"
private noncomputable def vp11110001_1 : Blocks := edgeBlocks% "full/vectors/11110001-V-0001.bin"
private noncomputable def vp11110001_2 : Blocks := edgeBlocks% "full/vectors/11110001-V-0002.bin"
noncomputable def vp11110001 : Blocks := (Blocks.join vp11110001_0 (Blocks.join vp11110001_1 vp11110001_2))
theorem coverp11110001 : Covers (-7711761639/32000000 : ℚ) vp11110001 := cover_leaf (by decide +kernel)
private noncomputable def vp11110000_0 : Blocks := edgeBlocks% "full/vectors/11110000-V-0000.bin"
private noncomputable def vp11110000_1 : Blocks := edgeBlocks% "full/vectors/11110000-V-0001.bin"
private noncomputable def vp11110000_2 : Blocks := edgeBlocks% "full/vectors/11110000-V-0002.bin"
noncomputable def vp11110000 : Blocks := (Blocks.join vp11110000_0 (Blocks.join vp11110000_1 vp11110000_2))
theorem coverp11110000 : Covers (-7679761639/32000000 : ℚ) vp11110000 := cover_leaf (by decide +kernel)
private noncomputable def vp1111000_0 : Blocks := edgeBlocks% "full/vectors/1111000-V-0000.bin"
private noncomputable def vp1111000_1 : Blocks := edgeBlocks% "full/vectors/1111000-V-0001.bin"
private noncomputable def vp1111000_2 : Blocks := edgeBlocks% "full/vectors/1111000-V-0002.bin"
private noncomputable def vp1111000_3 : Blocks := edgeBlocks% "full/vectors/1111000-V-0003.bin"
private noncomputable def vp1111000_4 : Blocks := edgeBlocks% "full/vectors/1111000-V-0004.bin"
private noncomputable def vp1111000_5 : Blocks := edgeBlocks% "full/vectors/1111000-V-0005.bin"
noncomputable def vp1111000 : Blocks := (Blocks.join (Blocks.join vp1111000_0 (Blocks.join vp1111000_1 vp1111000_2)) (Blocks.join vp1111000_3 (Blocks.join vp1111000_4 vp1111000_5)))
private theorem bp11110000 : Branch 0 (-7679761639/64000000 : ℚ) vp1111000 := by
  apply branch_left_normalized (c:=vp11110000) (k:=0) (m:=382) (by decide +kernel)
  rw [show 2*(-7679761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-7679761639/32000000 : ℚ) by norm_num]
  exact coverp11110000
private noncomputable def ep11110001_0 : Blocks := edgeBlocks% "full/vectors/11110001-E-0000.bin"
private noncomputable def ep11110001_1 : Blocks := edgeBlocks% "full/vectors/11110001-E-0001.bin"
private noncomputable def ep11110001_2 : Blocks := edgeBlocks% "full/vectors/11110001-E-0002.bin"
private noncomputable def ep11110001_3 : Blocks := edgeBlocks% "full/vectors/11110001-E-0003.bin"
private noncomputable def ep11110001_4 : Blocks := edgeBlocks% "full/vectors/11110001-E-0004.bin"
private noncomputable def ep11110001_5 : Blocks := edgeBlocks% "full/vectors/11110001-E-0005.bin"
noncomputable def ep11110001 : Blocks := (Blocks.join (Blocks.join ep11110001_0 (Blocks.join ep11110001_1 ep11110001_2)) (Blocks.join ep11110001_3 (Blocks.join ep11110001_4 ep11110001_5)))
private theorem idp11110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1111000.list =
    C ((2:ℤ)^920) * horner X vp11110001.list + horner X ep11110001.list := by
  exact edge_identity (B := (2:ℤ)^1220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp11110001 : Branch 1 (-7679761639/64000000 : ℚ) vp1111000 := by
  apply branch_checked idp11110001 (by positivity) (by decide +kernel)
  rw [show 2*(-7679761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-7711761639/32000000 : ℚ) by norm_num]
  exact coverp11110001
theorem coverp1111000 : Covers (-7679761639/64000000 : ℚ) vp1111000 := join_branches bp11110000 bp11110001
private noncomputable def vp111100_0 : Blocks := edgeBlocks% "full/vectors/111100-V-0000.bin"
private noncomputable def vp111100_1 : Blocks := edgeBlocks% "full/vectors/111100-V-0001.bin"
private noncomputable def vp111100_2 : Blocks := edgeBlocks% "full/vectors/111100-V-0002.bin"
private noncomputable def vp111100_3 : Blocks := edgeBlocks% "full/vectors/111100-V-0003.bin"
private noncomputable def vp111100_4 : Blocks := edgeBlocks% "full/vectors/111100-V-0004.bin"
private noncomputable def vp111100_5 : Blocks := edgeBlocks% "full/vectors/111100-V-0005.bin"
private noncomputable def vp111100_6 : Blocks := edgeBlocks% "full/vectors/111100-V-0006.bin"
private noncomputable def vp111100_7 : Blocks := edgeBlocks% "full/vectors/111100-V-0007.bin"
private noncomputable def vp111100_8 : Blocks := edgeBlocks% "full/vectors/111100-V-0008.bin"
private noncomputable def vp111100_9 : Blocks := edgeBlocks% "full/vectors/111100-V-0009.bin"
private noncomputable def vp111100_10 : Blocks := edgeBlocks% "full/vectors/111100-V-0010.bin"
private noncomputable def vp111100_11 : Blocks := edgeBlocks% "full/vectors/111100-V-0011.bin"
noncomputable def vp111100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp111100_0 (Blocks.join vp111100_1 vp111100_2)) (Blocks.join vp111100_3 (Blocks.join vp111100_4 vp111100_5))) (Blocks.join (Blocks.join vp111100_6 (Blocks.join vp111100_7 vp111100_8)) (Blocks.join vp111100_9 (Blocks.join vp111100_10 vp111100_11))))
private theorem bp1111000 : Branch 0 (-7679761639/128000000 : ℚ) vp111100 := by
  apply branch_left_normalized (c:=vp1111000) (k:=0) (m:=735) (by decide +kernel)
  rw [show 2*(-7679761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-7679761639/64000000 : ℚ) by norm_num]
  exact coverp1111000
private noncomputable def ep1111001_0 : Blocks := edgeBlocks% "full/vectors/1111001-E-0000.bin"
private noncomputable def ep1111001_1 : Blocks := edgeBlocks% "full/vectors/1111001-E-0001.bin"
private noncomputable def ep1111001_2 : Blocks := edgeBlocks% "full/vectors/1111001-E-0002.bin"
private noncomputable def ep1111001_3 : Blocks := edgeBlocks% "full/vectors/1111001-E-0003.bin"
private noncomputable def ep1111001_4 : Blocks := edgeBlocks% "full/vectors/1111001-E-0004.bin"
private noncomputable def ep1111001_5 : Blocks := edgeBlocks% "full/vectors/1111001-E-0005.bin"
private noncomputable def ep1111001_6 : Blocks := edgeBlocks% "full/vectors/1111001-E-0006.bin"
private noncomputable def ep1111001_7 : Blocks := edgeBlocks% "full/vectors/1111001-E-0007.bin"
private noncomputable def ep1111001_8 : Blocks := edgeBlocks% "full/vectors/1111001-E-0008.bin"
private noncomputable def ep1111001_9 : Blocks := edgeBlocks% "full/vectors/1111001-E-0009.bin"
private noncomputable def ep1111001_10 : Blocks := edgeBlocks% "full/vectors/1111001-E-0010.bin"
private noncomputable def ep1111001_11 : Blocks := edgeBlocks% "full/vectors/1111001-E-0011.bin"
noncomputable def ep1111001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep1111001_0 (Blocks.join ep1111001_1 ep1111001_2)) (Blocks.join ep1111001_3 (Blocks.join ep1111001_4 ep1111001_5))) (Blocks.join (Blocks.join ep1111001_6 (Blocks.join ep1111001_7 ep1111001_8)) (Blocks.join ep1111001_9 (Blocks.join ep1111001_10 ep1111001_11))))
private theorem idp1111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp111100.list =
    C ((2:ℤ)^1801) * horner X vp1111001.list + horner X ep1111001.list := by
  exact edge_identity (B := (2:ℤ)^2292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp1111001 : Branch 1 (-7679761639/128000000 : ℚ) vp111100 := by
  apply branch_checked idp1111001 (by positivity) (by decide +kernel)
  rw [show 2*(-7679761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-7743761639/64000000 : ℚ) by norm_num]
  exact coverp1111001
theorem coverp111100 : Covers (-7679761639/128000000 : ℚ) vp111100 := join_branches bp1111000 bp1111001
private noncomputable def vp11110_0 : Blocks := edgeBlocks% "full/vectors/11110-V-0000.bin"
private noncomputable def vp11110_1 : Blocks := edgeBlocks% "full/vectors/11110-V-0001.bin"
private noncomputable def vp11110_2 : Blocks := edgeBlocks% "full/vectors/11110-V-0002.bin"
private noncomputable def vp11110_3 : Blocks := edgeBlocks% "full/vectors/11110-V-0003.bin"
private noncomputable def vp11110_4 : Blocks := edgeBlocks% "full/vectors/11110-V-0004.bin"
private noncomputable def vp11110_5 : Blocks := edgeBlocks% "full/vectors/11110-V-0005.bin"
private noncomputable def vp11110_6 : Blocks := edgeBlocks% "full/vectors/11110-V-0006.bin"
private noncomputable def vp11110_7 : Blocks := edgeBlocks% "full/vectors/11110-V-0007.bin"
private noncomputable def vp11110_8 : Blocks := edgeBlocks% "full/vectors/11110-V-0008.bin"
private noncomputable def vp11110_9 : Blocks := edgeBlocks% "full/vectors/11110-V-0009.bin"
private noncomputable def vp11110_10 : Blocks := edgeBlocks% "full/vectors/11110-V-0010.bin"
private noncomputable def vp11110_11 : Blocks := edgeBlocks% "full/vectors/11110-V-0011.bin"
private noncomputable def vp11110_12 : Blocks := edgeBlocks% "full/vectors/11110-V-0012.bin"
private noncomputable def vp11110_13 : Blocks := edgeBlocks% "full/vectors/11110-V-0013.bin"
private noncomputable def vp11110_14 : Blocks := edgeBlocks% "full/vectors/11110-V-0014.bin"
private noncomputable def vp11110_15 : Blocks := edgeBlocks% "full/vectors/11110-V-0015.bin"
private noncomputable def vp11110_16 : Blocks := edgeBlocks% "full/vectors/11110-V-0016.bin"
private noncomputable def vp11110_17 : Blocks := edgeBlocks% "full/vectors/11110-V-0017.bin"
private noncomputable def vp11110_18 : Blocks := edgeBlocks% "full/vectors/11110-V-0018.bin"
private noncomputable def vp11110_19 : Blocks := edgeBlocks% "full/vectors/11110-V-0019.bin"
private noncomputable def vp11110_20 : Blocks := edgeBlocks% "full/vectors/11110-V-0020.bin"
private noncomputable def vp11110_21 : Blocks := edgeBlocks% "full/vectors/11110-V-0021.bin"
noncomputable def vp11110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp11110_0 vp11110_1) (Blocks.join vp11110_2 (Blocks.join vp11110_3 vp11110_4))) (Blocks.join (Blocks.join vp11110_5 (Blocks.join vp11110_6 vp11110_7)) (Blocks.join vp11110_8 (Blocks.join vp11110_9 vp11110_10)))) (Blocks.join (Blocks.join (Blocks.join vp11110_11 vp11110_12) (Blocks.join vp11110_13 (Blocks.join vp11110_14 vp11110_15))) (Blocks.join (Blocks.join vp11110_16 (Blocks.join vp11110_17 vp11110_18)) (Blocks.join vp11110_19 (Blocks.join vp11110_20 vp11110_21)))))
private theorem bp111100 : Branch 0 (-7679761639/256000000 : ℚ) vp11110 := by
  apply branch_left_normalized (c:=vp111100) (k:=0) (m:=1431) (by decide +kernel)
  rw [show 2*(-7679761639/256000000 : ℚ) - ((0:ℤ):ℚ) = (-7679761639/128000000 : ℚ) by norm_num]
  exact coverp111100
private noncomputable def ep111101_0 : Blocks := edgeBlocks% "full/vectors/111101-E-0000.bin"
private noncomputable def ep111101_1 : Blocks := edgeBlocks% "full/vectors/111101-E-0001.bin"
private noncomputable def ep111101_2 : Blocks := edgeBlocks% "full/vectors/111101-E-0002.bin"
private noncomputable def ep111101_3 : Blocks := edgeBlocks% "full/vectors/111101-E-0003.bin"
private noncomputable def ep111101_4 : Blocks := edgeBlocks% "full/vectors/111101-E-0004.bin"
private noncomputable def ep111101_5 : Blocks := edgeBlocks% "full/vectors/111101-E-0005.bin"
private noncomputable def ep111101_6 : Blocks := edgeBlocks% "full/vectors/111101-E-0006.bin"
private noncomputable def ep111101_7 : Blocks := edgeBlocks% "full/vectors/111101-E-0007.bin"
private noncomputable def ep111101_8 : Blocks := edgeBlocks% "full/vectors/111101-E-0008.bin"
private noncomputable def ep111101_9 : Blocks := edgeBlocks% "full/vectors/111101-E-0009.bin"
private noncomputable def ep111101_10 : Blocks := edgeBlocks% "full/vectors/111101-E-0010.bin"
private noncomputable def ep111101_11 : Blocks := edgeBlocks% "full/vectors/111101-E-0011.bin"
private noncomputable def ep111101_12 : Blocks := edgeBlocks% "full/vectors/111101-E-0012.bin"
private noncomputable def ep111101_13 : Blocks := edgeBlocks% "full/vectors/111101-E-0013.bin"
private noncomputable def ep111101_14 : Blocks := edgeBlocks% "full/vectors/111101-E-0014.bin"
private noncomputable def ep111101_15 : Blocks := edgeBlocks% "full/vectors/111101-E-0015.bin"
private noncomputable def ep111101_16 : Blocks := edgeBlocks% "full/vectors/111101-E-0016.bin"
private noncomputable def ep111101_17 : Blocks := edgeBlocks% "full/vectors/111101-E-0017.bin"
private noncomputable def ep111101_18 : Blocks := edgeBlocks% "full/vectors/111101-E-0018.bin"
private noncomputable def ep111101_19 : Blocks := edgeBlocks% "full/vectors/111101-E-0019.bin"
private noncomputable def ep111101_20 : Blocks := edgeBlocks% "full/vectors/111101-E-0020.bin"
private noncomputable def ep111101_21 : Blocks := edgeBlocks% "full/vectors/111101-E-0021.bin"
noncomputable def ep111101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep111101_0 ep111101_1) (Blocks.join ep111101_2 (Blocks.join ep111101_3 ep111101_4))) (Blocks.join (Blocks.join ep111101_5 (Blocks.join ep111101_6 ep111101_7)) (Blocks.join ep111101_8 (Blocks.join ep111101_9 ep111101_10)))) (Blocks.join (Blocks.join (Blocks.join ep111101_11 ep111101_12) (Blocks.join ep111101_13 (Blocks.join ep111101_14 ep111101_15))) (Blocks.join (Blocks.join ep111101_16 (Blocks.join ep111101_17 ep111101_18)) (Blocks.join ep111101_19 (Blocks.join ep111101_20 ep111101_21)))))
private theorem idp111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp11110.list =
    C ((2:ℤ)^3442) * horner X vp111101.list + horner X ep111101.list := by
  exact edge_identity (B := (2:ℤ)^4310) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp111101 : Branch 1 (-7679761639/256000000 : ℚ) vp11110 := by
  apply branch_checked idp111101 (by positivity) (by decide +kernel)
  rw [show 2*(-7679761639/256000000 : ℚ) - ((1:ℤ):ℚ) = (-7807761639/128000000 : ℚ) by norm_num]
  exact coverp111101
theorem coverp11110 : Covers (-7679761639/256000000 : ℚ) vp11110 := join_branches bp111100 bp111101
private noncomputable def vp1111_0 : Blocks := edgeBlocks% "full/vectors/1111-V-0000.bin"
private noncomputable def vp1111_1 : Blocks := edgeBlocks% "full/vectors/1111-V-0001.bin"
private noncomputable def vp1111_2 : Blocks := edgeBlocks% "full/vectors/1111-V-0002.bin"
private noncomputable def vp1111_3 : Blocks := edgeBlocks% "full/vectors/1111-V-0003.bin"
private noncomputable def vp1111_4 : Blocks := edgeBlocks% "full/vectors/1111-V-0004.bin"
private noncomputable def vp1111_5 : Blocks := edgeBlocks% "full/vectors/1111-V-0005.bin"
private noncomputable def vp1111_6 : Blocks := edgeBlocks% "full/vectors/1111-V-0006.bin"
private noncomputable def vp1111_7 : Blocks := edgeBlocks% "full/vectors/1111-V-0007.bin"
private noncomputable def vp1111_8 : Blocks := edgeBlocks% "full/vectors/1111-V-0008.bin"
private noncomputable def vp1111_9 : Blocks := edgeBlocks% "full/vectors/1111-V-0009.bin"
private noncomputable def vp1111_10 : Blocks := edgeBlocks% "full/vectors/1111-V-0010.bin"
private noncomputable def vp1111_11 : Blocks := edgeBlocks% "full/vectors/1111-V-0011.bin"
private noncomputable def vp1111_12 : Blocks := edgeBlocks% "full/vectors/1111-V-0012.bin"
private noncomputable def vp1111_13 : Blocks := edgeBlocks% "full/vectors/1111-V-0013.bin"
private noncomputable def vp1111_14 : Blocks := edgeBlocks% "full/vectors/1111-V-0014.bin"
private noncomputable def vp1111_15 : Blocks := edgeBlocks% "full/vectors/1111-V-0015.bin"
private noncomputable def vp1111_16 : Blocks := edgeBlocks% "full/vectors/1111-V-0016.bin"
private noncomputable def vp1111_17 : Blocks := edgeBlocks% "full/vectors/1111-V-0017.bin"
private noncomputable def vp1111_18 : Blocks := edgeBlocks% "full/vectors/1111-V-0018.bin"
private noncomputable def vp1111_19 : Blocks := edgeBlocks% "full/vectors/1111-V-0019.bin"
private noncomputable def vp1111_20 : Blocks := edgeBlocks% "full/vectors/1111-V-0020.bin"
private noncomputable def vp1111_21 : Blocks := edgeBlocks% "full/vectors/1111-V-0021.bin"
private noncomputable def vp1111_22 : Blocks := edgeBlocks% "full/vectors/1111-V-0022.bin"
private noncomputable def vp1111_23 : Blocks := edgeBlocks% "full/vectors/1111-V-0023.bin"
private noncomputable def vp1111_24 : Blocks := edgeBlocks% "full/vectors/1111-V-0024.bin"
private noncomputable def vp1111_25 : Blocks := edgeBlocks% "full/vectors/1111-V-0025.bin"
private noncomputable def vp1111_26 : Blocks := edgeBlocks% "full/vectors/1111-V-0026.bin"
private noncomputable def vp1111_27 : Blocks := edgeBlocks% "full/vectors/1111-V-0027.bin"
private noncomputable def vp1111_28 : Blocks := edgeBlocks% "full/vectors/1111-V-0028.bin"
private noncomputable def vp1111_29 : Blocks := edgeBlocks% "full/vectors/1111-V-0029.bin"
private noncomputable def vp1111_30 : Blocks := edgeBlocks% "full/vectors/1111-V-0030.bin"
private noncomputable def vp1111_31 : Blocks := edgeBlocks% "full/vectors/1111-V-0031.bin"
private noncomputable def vp1111_32 : Blocks := edgeBlocks% "full/vectors/1111-V-0032.bin"
private noncomputable def vp1111_33 : Blocks := edgeBlocks% "full/vectors/1111-V-0033.bin"
private noncomputable def vp1111_34 : Blocks := edgeBlocks% "full/vectors/1111-V-0034.bin"
private noncomputable def vp1111_35 : Blocks := edgeBlocks% "full/vectors/1111-V-0035.bin"
private noncomputable def vp1111_36 : Blocks := edgeBlocks% "full/vectors/1111-V-0036.bin"
noncomputable def vp1111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1111_0 vp1111_1) (Blocks.join vp1111_2 vp1111_3)) (Blocks.join (Blocks.join vp1111_4 vp1111_5) (Blocks.join vp1111_6 (Blocks.join vp1111_7 vp1111_8)))) (Blocks.join (Blocks.join (Blocks.join vp1111_9 vp1111_10) (Blocks.join vp1111_11 vp1111_12)) (Blocks.join (Blocks.join vp1111_13 vp1111_14) (Blocks.join vp1111_15 (Blocks.join vp1111_16 vp1111_17))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp1111_18 vp1111_19) (Blocks.join vp1111_20 vp1111_21)) (Blocks.join (Blocks.join vp1111_22 vp1111_23) (Blocks.join vp1111_24 (Blocks.join vp1111_25 vp1111_26)))) (Blocks.join (Blocks.join (Blocks.join vp1111_27 vp1111_28) (Blocks.join vp1111_29 (Blocks.join vp1111_30 vp1111_31))) (Blocks.join (Blocks.join vp1111_32 vp1111_33) (Blocks.join vp1111_34 (Blocks.join vp1111_35 vp1111_36))))))
private theorem bp11110 : Branch 0 (-7679761639/512000000 : ℚ) vp1111 := by
  apply branch_left_normalized (c:=vp11110) (k:=0) (m:=2703) (by decide +kernel)
  rw [show 2*(-7679761639/512000000 : ℚ) - ((0:ℤ):ℚ) = (-7679761639/256000000 : ℚ) by norm_num]
  exact coverp11110
private noncomputable def ep11111_0 : Blocks := edgeBlocks% "full/vectors/11111-E-0000.bin"
private noncomputable def ep11111_1 : Blocks := edgeBlocks% "full/vectors/11111-E-0001.bin"
private noncomputable def ep11111_2 : Blocks := edgeBlocks% "full/vectors/11111-E-0002.bin"
private noncomputable def ep11111_3 : Blocks := edgeBlocks% "full/vectors/11111-E-0003.bin"
private noncomputable def ep11111_4 : Blocks := edgeBlocks% "full/vectors/11111-E-0004.bin"
private noncomputable def ep11111_5 : Blocks := edgeBlocks% "full/vectors/11111-E-0005.bin"
private noncomputable def ep11111_6 : Blocks := edgeBlocks% "full/vectors/11111-E-0006.bin"
private noncomputable def ep11111_7 : Blocks := edgeBlocks% "full/vectors/11111-E-0007.bin"
private noncomputable def ep11111_8 : Blocks := edgeBlocks% "full/vectors/11111-E-0008.bin"
private noncomputable def ep11111_9 : Blocks := edgeBlocks% "full/vectors/11111-E-0009.bin"
private noncomputable def ep11111_10 : Blocks := edgeBlocks% "full/vectors/11111-E-0010.bin"
private noncomputable def ep11111_11 : Blocks := edgeBlocks% "full/vectors/11111-E-0011.bin"
private noncomputable def ep11111_12 : Blocks := edgeBlocks% "full/vectors/11111-E-0012.bin"
private noncomputable def ep11111_13 : Blocks := edgeBlocks% "full/vectors/11111-E-0013.bin"
private noncomputable def ep11111_14 : Blocks := edgeBlocks% "full/vectors/11111-E-0014.bin"
private noncomputable def ep11111_15 : Blocks := edgeBlocks% "full/vectors/11111-E-0015.bin"
private noncomputable def ep11111_16 : Blocks := edgeBlocks% "full/vectors/11111-E-0016.bin"
private noncomputable def ep11111_17 : Blocks := edgeBlocks% "full/vectors/11111-E-0017.bin"
private noncomputable def ep11111_18 : Blocks := edgeBlocks% "full/vectors/11111-E-0018.bin"
private noncomputable def ep11111_19 : Blocks := edgeBlocks% "full/vectors/11111-E-0019.bin"
private noncomputable def ep11111_20 : Blocks := edgeBlocks% "full/vectors/11111-E-0020.bin"
private noncomputable def ep11111_21 : Blocks := edgeBlocks% "full/vectors/11111-E-0021.bin"
private noncomputable def ep11111_22 : Blocks := edgeBlocks% "full/vectors/11111-E-0022.bin"
private noncomputable def ep11111_23 : Blocks := edgeBlocks% "full/vectors/11111-E-0023.bin"
private noncomputable def ep11111_24 : Blocks := edgeBlocks% "full/vectors/11111-E-0024.bin"
private noncomputable def ep11111_25 : Blocks := edgeBlocks% "full/vectors/11111-E-0025.bin"
private noncomputable def ep11111_26 : Blocks := edgeBlocks% "full/vectors/11111-E-0026.bin"
private noncomputable def ep11111_27 : Blocks := edgeBlocks% "full/vectors/11111-E-0027.bin"
private noncomputable def ep11111_28 : Blocks := edgeBlocks% "full/vectors/11111-E-0028.bin"
private noncomputable def ep11111_29 : Blocks := edgeBlocks% "full/vectors/11111-E-0029.bin"
private noncomputable def ep11111_30 : Blocks := edgeBlocks% "full/vectors/11111-E-0030.bin"
private noncomputable def ep11111_31 : Blocks := edgeBlocks% "full/vectors/11111-E-0031.bin"
private noncomputable def ep11111_32 : Blocks := edgeBlocks% "full/vectors/11111-E-0032.bin"
private noncomputable def ep11111_33 : Blocks := edgeBlocks% "full/vectors/11111-E-0033.bin"
private noncomputable def ep11111_34 : Blocks := edgeBlocks% "full/vectors/11111-E-0034.bin"
private noncomputable def ep11111_35 : Blocks := edgeBlocks% "full/vectors/11111-E-0035.bin"
private noncomputable def ep11111_36 : Blocks := edgeBlocks% "full/vectors/11111-E-0036.bin"
noncomputable def ep11111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep11111_0 ep11111_1) (Blocks.join ep11111_2 ep11111_3)) (Blocks.join (Blocks.join ep11111_4 ep11111_5) (Blocks.join ep11111_6 (Blocks.join ep11111_7 ep11111_8)))) (Blocks.join (Blocks.join (Blocks.join ep11111_9 ep11111_10) (Blocks.join ep11111_11 ep11111_12)) (Blocks.join (Blocks.join ep11111_13 ep11111_14) (Blocks.join ep11111_15 (Blocks.join ep11111_16 ep11111_17))))) (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep11111_18 ep11111_19) (Blocks.join ep11111_20 ep11111_21)) (Blocks.join (Blocks.join ep11111_22 ep11111_23) (Blocks.join ep11111_24 (Blocks.join ep11111_25 ep11111_26)))) (Blocks.join (Blocks.join (Blocks.join ep11111_27 ep11111_28) (Blocks.join ep11111_29 (Blocks.join ep11111_30 ep11111_31))) (Blocks.join (Blocks.join ep11111_32 ep11111_33) (Blocks.join ep11111_34 (Blocks.join ep11111_35 ep11111_36))))))
private def ptsp11111 : List ℤ := [((2:ℤ)^2549+0),((2:ℤ)^2549+1),((2:ℤ)^2549+2),((2:ℤ)^2549+3)]
private theorem boundp11111 : 2^vp1111.size*absSum vp1111.list + ((2:ℤ)^6184*absSum vp11111.list+absSum ep11111.list) < (2:ℤ)^7771 := by decide +kernel
private theorem pointp11111_0 : fastHom 1 ((2:ℤ)^2549+0) vp1111 = ((2:ℤ)^6184)*vp11111.subst ((2:ℤ)^2549+0)+ep11111.subst ((2:ℤ)^2549+0) := by decide +kernel
private theorem pointp11111_1 : fastHom 1 ((2:ℤ)^2549+1) vp1111 = ((2:ℤ)^6184)*vp11111.subst ((2:ℤ)^2549+1)+ep11111.subst ((2:ℤ)^2549+1) := by decide +kernel
private theorem pointp11111_2 : fastHom 1 ((2:ℤ)^2549+2) vp1111 = ((2:ℤ)^6184)*vp11111.subst ((2:ℤ)^2549+2)+ep11111.subst ((2:ℤ)^2549+2) := by decide +kernel
private theorem pointp11111_3 : fastHom 1 ((2:ℤ)^2549+3) vp1111 = ((2:ℤ)^6184)*vp11111.subst ((2:ℤ)^2549+3)+ep11111.subst ((2:ℤ)^2549+3) := by decide +kernel
private theorem checkp11111 (x:ℤ) (hx:x ∈ ptsp11111) : fastHom 1 x vp1111 = ((2:ℤ)^6184)*vp11111.subst x+ep11111.subst x := by
  simp only [ptsp11111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact pointp11111_0
  · exact pointp11111_1
  · exact pointp11111_2
  · exact pointp11111_3
private theorem idp11111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp1111.list =
    C ((2:ℤ)^6184) * horner X vp11111.list + horner X ep11111.list := by
  apply edge_identity (B := (2:ℤ)^7771) (by decide) (by positivity) (by positivity) boundp11111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp11111 (by decide +kernel)
  · have h : ptsp11111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp11111.trans_le (by decide +kernel)
  · exact checkp11111
private theorem bp11111 : Branch 1 (-7679761639/512000000 : ℚ) vp1111 := by
  apply branch_checked idp11111 (by positivity) (by decide +kernel)
  rw [show 2*(-7679761639/512000000 : ℚ) - ((1:ℤ):ℚ) = (-7935761639/256000000 : ℚ) by norm_num]
  exact coverp11111
theorem coverp1111 : Covers (-7679761639/512000000 : ℚ) vp1111 := join_branches bp11110 bp11111
end NextProof.EdgeFull

