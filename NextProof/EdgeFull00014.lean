import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00011
import NextProof.EdgeFull00013

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000000001_0 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0000.bin"
private noncomputable def vp00000000001_1 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0001.bin"
private noncomputable def vp00000000001_2 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0002.bin"
private noncomputable def vp00000000001_3 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0003.bin"
private noncomputable def vp00000000001_4 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0004.bin"
private noncomputable def vp00000000001_5 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0005.bin"
private noncomputable def vp00000000001_6 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0006.bin"
private noncomputable def vp00000000001_7 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0007.bin"
private noncomputable def vp00000000001_8 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0008.bin"
private noncomputable def vp00000000001_9 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0009.bin"
private noncomputable def vp00000000001_10 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0010.bin"
private noncomputable def vp00000000001_11 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0011.bin"
private noncomputable def vp00000000001_12 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0012.bin"
private noncomputable def vp00000000001_13 : Blocks := edgeBlocks% "full/vectors/00000000001-V-0013.bin"
noncomputable def vp00000000001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00000000001_0 (Blocks.join vp00000000001_1 vp00000000001_2)) (Blocks.join (Blocks.join vp00000000001_3 vp00000000001_4) (Blocks.join vp00000000001_5 vp00000000001_6))) (Blocks.join (Blocks.join vp00000000001_7 (Blocks.join vp00000000001_8 vp00000000001_9)) (Blocks.join (Blocks.join vp00000000001_10 vp00000000001_11) (Blocks.join vp00000000001_12 vp00000000001_13))))
private theorem bp000000000010 : Branch 0 (-3761639/4000000 : ℚ) vp00000000001 := by
  apply branch_left_normalized (c:=vp000000000010) (k:=0) (m:=987) (by decide +kernel)
  rw [show 2*(-3761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-3761639/2000000 : ℚ) by norm_num]
  exact coverp000000000010
private noncomputable def ep000000000011_0 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0000.bin"
private noncomputable def ep000000000011_1 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0001.bin"
private noncomputable def ep000000000011_2 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0002.bin"
private noncomputable def ep000000000011_3 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0003.bin"
private noncomputable def ep000000000011_4 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0004.bin"
private noncomputable def ep000000000011_5 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0005.bin"
private noncomputable def ep000000000011_6 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0006.bin"
private noncomputable def ep000000000011_7 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0007.bin"
private noncomputable def ep000000000011_8 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0008.bin"
private noncomputable def ep000000000011_9 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0009.bin"
private noncomputable def ep000000000011_10 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0010.bin"
private noncomputable def ep000000000011_11 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0011.bin"
private noncomputable def ep000000000011_12 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0012.bin"
private noncomputable def ep000000000011_13 : Blocks := edgeBlocks% "full/vectors/000000000011-E-0013.bin"
noncomputable def ep000000000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000000000011_0 (Blocks.join ep000000000011_1 ep000000000011_2)) (Blocks.join (Blocks.join ep000000000011_3 ep000000000011_4) (Blocks.join ep000000000011_5 ep000000000011_6))) (Blocks.join (Blocks.join ep000000000011_7 (Blocks.join ep000000000011_8 ep000000000011_9)) (Blocks.join (Blocks.join ep000000000011_10 ep000000000011_11) (Blocks.join ep000000000011_12 ep000000000011_13))))
private theorem idp000000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001.list =
    C ((2:ℤ)^1772) * horner X vp000000000011.list + horner X ep000000000011.list := by
  exact edge_identity (B := (2:ℤ)^2888) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011 : Branch 1 (-3761639/4000000 : ℚ) vp00000000001 := by
  apply branch_checked idp000000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-3761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-5761639/2000000 : ℚ) by norm_num]
  exact coverp000000000011
theorem coverp00000000001 : Covers (-3761639/4000000 : ℚ) vp00000000001 := join_branches bp000000000010 bp000000000011
end NextProof.EdgeFull

