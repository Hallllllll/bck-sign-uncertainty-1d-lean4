import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00016

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000000011011111111_0 : Blocks := edgeBlocks% "full/vectors/00000000011011111111-V-0000.bin"
noncomputable def vp00000000011011111111 : Blocks := vp00000000011011111111_0
theorem coverp00000000011011111111 : Covers (-27507653/15625 : ℚ) vp00000000011011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011011111110_0 : Blocks := edgeBlocks% "full/vectors/00000000011011111110-V-0000.bin"
noncomputable def vp00000000011011111110 : Blocks := vp00000000011011111110_0
theorem coverp00000000011011111110 : Covers (-27492028/15625 : ℚ) vp00000000011011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001101111111_0 : Blocks := edgeBlocks% "full/vectors/0000000001101111111-V-0000.bin"
noncomputable def vp0000000001101111111 : Blocks := vp0000000001101111111_0
private theorem bp00000000011011111110 : Branch 0 (-13746014/15625 : ℚ) vp0000000001101111111 := by
  apply branch_left_normalized (c:=vp00000000011011111110) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-13746014/15625 : ℚ) - ((0:ℤ):ℚ) = (-27492028/15625 : ℚ) by norm_num]
  exact coverp00000000011011111110
private noncomputable def ep00000000011011111111_0 : Blocks := edgeBlocks% "full/vectors/00000000011011111111-E-0000.bin"
noncomputable def ep00000000011011111111 : Blocks := ep00000000011011111111_0
private theorem idp00000000011011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001101111111.list =
    C ((2:ℤ)^17) * horner X vp00000000011011111111.list + horner X ep00000000011011111111.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011011111111 : Branch 1 (-13746014/15625 : ℚ) vp0000000001101111111 := by
  apply branch_checked idp00000000011011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-13746014/15625 : ℚ) - ((1:ℤ):ℚ) = (-27507653/15625 : ℚ) by norm_num]
  exact coverp00000000011011111111
theorem coverp0000000001101111111 : Covers (-13746014/15625 : ℚ) vp0000000001101111111 := join_branches bp00000000011011111110 bp00000000011011111111
private noncomputable def vp0000000001101111110_0 : Blocks := edgeBlocks% "full/vectors/0000000001101111110-V-0000.bin"
noncomputable def vp0000000001101111110 : Blocks := vp0000000001101111110_0
theorem coverp0000000001101111110 : Covers (-13730389/15625 : ℚ) vp0000000001101111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110111111_0 : Blocks := edgeBlocks% "full/vectors/000000000110111111-V-0000.bin"
noncomputable def vp000000000110111111 : Blocks := vp000000000110111111_0
private theorem bp0000000001101111110 : Branch 0 (-13730389/31250 : ℚ) vp000000000110111111 := by
  apply branch_left_normalized (c:=vp0000000001101111110) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-13730389/31250 : ℚ) - ((0:ℤ):ℚ) = (-13730389/15625 : ℚ) by norm_num]
  exact coverp0000000001101111110
private noncomputable def ep0000000001101111111_0 : Blocks := edgeBlocks% "full/vectors/0000000001101111111-E-0000.bin"
noncomputable def ep0000000001101111111 : Blocks := ep0000000001101111111_0
private theorem idp0000000001101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110111111.list =
    C ((2:ℤ)^24) * horner X vp0000000001101111111.list + horner X ep0000000001101111111.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001101111111 : Branch 1 (-13730389/31250 : ℚ) vp000000000110111111 := by
  apply branch_checked idp0000000001101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-13730389/31250 : ℚ) - ((1:ℤ):ℚ) = (-13746014/15625 : ℚ) by norm_num]
  exact coverp0000000001101111111
theorem coverp000000000110111111 : Covers (-13730389/31250 : ℚ) vp000000000110111111 := join_branches bp0000000001101111110 bp0000000001101111111
private noncomputable def vp000000000110111110_0 : Blocks := edgeBlocks% "full/vectors/000000000110111110-V-0000.bin"
noncomputable def vp000000000110111110 : Blocks := vp000000000110111110_0
theorem coverp000000000110111110 : Covers (-13699139/31250 : ℚ) vp000000000110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011011111_0 : Blocks := edgeBlocks% "full/vectors/00000000011011111-V-0000.bin"
noncomputable def vp00000000011011111 : Blocks := vp00000000011011111_0
private theorem bp000000000110111110 : Branch 0 (-13699139/62500 : ℚ) vp00000000011011111 := by
  apply branch_left_normalized (c:=vp000000000110111110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-13699139/62500 : ℚ) - ((0:ℤ):ℚ) = (-13699139/31250 : ℚ) by norm_num]
  exact coverp000000000110111110
private noncomputable def ep000000000110111111_0 : Blocks := edgeBlocks% "full/vectors/000000000110111111-E-0000.bin"
noncomputable def ep000000000110111111 : Blocks := ep000000000110111111_0
private theorem idp000000000110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011011111.list =
    C ((2:ℤ)^34) * horner X vp000000000110111111.list + horner X ep000000000110111111.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110111111 : Branch 1 (-13699139/62500 : ℚ) vp00000000011011111 := by
  apply branch_checked idp000000000110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-13699139/62500 : ℚ) - ((1:ℤ):ℚ) = (-13730389/31250 : ℚ) by norm_num]
  exact coverp000000000110111111
theorem coverp00000000011011111 : Covers (-13699139/62500 : ℚ) vp00000000011011111 := join_branches bp000000000110111110 bp000000000110111111
private noncomputable def vp00000000011011110_0 : Blocks := edgeBlocks% "full/vectors/00000000011011110-V-0000.bin"
noncomputable def vp00000000011011110 : Blocks := vp00000000011011110_0
theorem coverp00000000011011110 : Covers (-13636639/62500 : ℚ) vp00000000011011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001101111_0 : Blocks := edgeBlocks% "full/vectors/0000000001101111-V-0000.bin"
noncomputable def vp0000000001101111 : Blocks := vp0000000001101111_0
private theorem bp00000000011011110 : Branch 0 (-13636639/125000 : ℚ) vp0000000001101111 := by
  apply branch_left_normalized (c:=vp00000000011011110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-13636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-13636639/62500 : ℚ) by norm_num]
  exact coverp00000000011011110
private noncomputable def ep00000000011011111_0 : Blocks := edgeBlocks% "full/vectors/00000000011011111-E-0000.bin"
noncomputable def ep00000000011011111 : Blocks := ep00000000011011111_0
private theorem idp00000000011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001101111.list =
    C ((2:ℤ)^51) * horner X vp00000000011011111.list + horner X ep00000000011011111.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011011111 : Branch 1 (-13636639/125000 : ℚ) vp0000000001101111 := by
  apply branch_checked idp00000000011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-13636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-13699139/62500 : ℚ) by norm_num]
  exact coverp00000000011011111
theorem coverp0000000001101111 : Covers (-13636639/125000 : ℚ) vp0000000001101111 := join_branches bp00000000011011110 bp00000000011011111
private noncomputable def vp00000000011011101_0 : Blocks := edgeBlocks% "full/vectors/00000000011011101-V-0000.bin"
noncomputable def vp00000000011011101 : Blocks := vp00000000011011101_0
theorem coverp00000000011011101 : Covers (-13574139/62500 : ℚ) vp00000000011011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011011100_0 : Blocks := edgeBlocks% "full/vectors/00000000011011100-V-0000.bin"
noncomputable def vp00000000011011100 : Blocks := vp00000000011011100_0
theorem coverp00000000011011100 : Covers (-13511639/62500 : ℚ) vp00000000011011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001101110_0 : Blocks := edgeBlocks% "full/vectors/0000000001101110-V-0000.bin"
noncomputable def vp0000000001101110 : Blocks := vp0000000001101110_0
private theorem bp00000000011011100 : Branch 0 (-13511639/125000 : ℚ) vp0000000001101110 := by
  apply branch_left_normalized (c:=vp00000000011011100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-13511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-13511639/62500 : ℚ) by norm_num]
  exact coverp00000000011011100
private noncomputable def ep00000000011011101_0 : Blocks := edgeBlocks% "full/vectors/00000000011011101-E-0000.bin"
noncomputable def ep00000000011011101 : Blocks := ep00000000011011101_0
private theorem idp00000000011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001101110.list =
    C ((2:ℤ)^50) * horner X vp00000000011011101.list + horner X ep00000000011011101.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011011101 : Branch 1 (-13511639/125000 : ℚ) vp0000000001101110 := by
  apply branch_checked idp00000000011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-13511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-13574139/62500 : ℚ) by norm_num]
  exact coverp00000000011011101
theorem coverp0000000001101110 : Covers (-13511639/125000 : ℚ) vp0000000001101110 := join_branches bp00000000011011100 bp00000000011011101
private noncomputable def vp000000000110111_0 : Blocks := edgeBlocks% "full/vectors/000000000110111-V-0000.bin"
noncomputable def vp000000000110111 : Blocks := vp000000000110111_0
private theorem bp0000000001101110 : Branch 0 (-13511639/250000 : ℚ) vp000000000110111 := by
  apply branch_left_normalized (c:=vp0000000001101110) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-13511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-13511639/125000 : ℚ) by norm_num]
  exact coverp0000000001101110
private noncomputable def ep0000000001101111_0 : Blocks := edgeBlocks% "full/vectors/0000000001101111-E-0000.bin"
noncomputable def ep0000000001101111 : Blocks := ep0000000001101111_0
private theorem idp0000000001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110111.list =
    C ((2:ℤ)^84) * horner X vp0000000001101111.list + horner X ep0000000001101111.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001101111 : Branch 1 (-13511639/250000 : ℚ) vp000000000110111 := by
  apply branch_checked idp0000000001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-13511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-13636639/125000 : ℚ) by norm_num]
  exact coverp0000000001101111
theorem coverp000000000110111 : Covers (-13511639/250000 : ℚ) vp000000000110111 := join_branches bp0000000001101110 bp0000000001101111
private noncomputable def vp0000000001101101_0 : Blocks := edgeBlocks% "full/vectors/0000000001101101-V-0000.bin"
noncomputable def vp0000000001101101 : Blocks := vp0000000001101101_0
theorem coverp0000000001101101 : Covers (-13386639/125000 : ℚ) vp0000000001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001101100_0 : Blocks := edgeBlocks% "full/vectors/0000000001101100-V-0000.bin"
noncomputable def vp0000000001101100 : Blocks := vp0000000001101100_0
theorem coverp0000000001101100 : Covers (-13261639/125000 : ℚ) vp0000000001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110110_0 : Blocks := edgeBlocks% "full/vectors/000000000110110-V-0000.bin"
noncomputable def vp000000000110110 : Blocks := vp000000000110110_0
private theorem bp0000000001101100 : Branch 0 (-13261639/250000 : ℚ) vp000000000110110 := by
  apply branch_left_normalized (c:=vp0000000001101100) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-13261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-13261639/125000 : ℚ) by norm_num]
  exact coverp0000000001101100
private noncomputable def ep0000000001101101_0 : Blocks := edgeBlocks% "full/vectors/0000000001101101-E-0000.bin"
noncomputable def ep0000000001101101 : Blocks := ep0000000001101101_0
private theorem idp0000000001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110110.list =
    C ((2:ℤ)^85) * horner X vp0000000001101101.list + horner X ep0000000001101101.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001101101 : Branch 1 (-13261639/250000 : ℚ) vp000000000110110 := by
  apply branch_checked idp0000000001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-13261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-13386639/125000 : ℚ) by norm_num]
  exact coverp0000000001101101
theorem coverp000000000110110 : Covers (-13261639/250000 : ℚ) vp000000000110110 := join_branches bp0000000001101100 bp0000000001101101
private noncomputable def vp00000000011011_0 : Blocks := edgeBlocks% "full/vectors/00000000011011-V-0000.bin"
private noncomputable def vp00000000011011_1 : Blocks := edgeBlocks% "full/vectors/00000000011011-V-0001.bin"
noncomputable def vp00000000011011 : Blocks := (Blocks.join vp00000000011011_0 vp00000000011011_1)
private theorem bp000000000110110 : Branch 0 (-13261639/500000 : ℚ) vp00000000011011 := by
  apply branch_left_normalized (c:=vp000000000110110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-13261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-13261639/250000 : ℚ) by norm_num]
  exact coverp000000000110110
private noncomputable def ep000000000110111_0 : Blocks := edgeBlocks% "full/vectors/000000000110111-E-0000.bin"
private noncomputable def ep000000000110111_1 : Blocks := edgeBlocks% "full/vectors/000000000110111-E-0001.bin"
noncomputable def ep000000000110111 : Blocks := (Blocks.join ep000000000110111_0 ep000000000110111_1)
private theorem idp000000000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011011.list =
    C ((2:ℤ)^153) * horner X vp000000000110111.list + horner X ep000000000110111.list := by
  exact edge_identity (B := (2:ℤ)^317) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110111 : Branch 1 (-13261639/500000 : ℚ) vp00000000011011 := by
  apply branch_checked idp000000000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-13261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-13511639/250000 : ℚ) by norm_num]
  exact coverp000000000110111
theorem coverp00000000011011 : Covers (-13261639/500000 : ℚ) vp00000000011011 := join_branches bp000000000110110 bp000000000110111
private noncomputable def vp0000000001101011_0 : Blocks := edgeBlocks% "full/vectors/0000000001101011-V-0000.bin"
noncomputable def vp0000000001101011 : Blocks := vp0000000001101011_0
theorem coverp0000000001101011 : Covers (-13136639/125000 : ℚ) vp0000000001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001101010_0 : Blocks := edgeBlocks% "full/vectors/0000000001101010-V-0000.bin"
noncomputable def vp0000000001101010 : Blocks := vp0000000001101010_0
theorem coverp0000000001101010 : Covers (-13011639/125000 : ℚ) vp0000000001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110101_0 : Blocks := edgeBlocks% "full/vectors/000000000110101-V-0000.bin"
noncomputable def vp000000000110101 : Blocks := vp000000000110101_0
private theorem bp0000000001101010 : Branch 0 (-13011639/250000 : ℚ) vp000000000110101 := by
  apply branch_left_normalized (c:=vp0000000001101010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-13011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-13011639/125000 : ℚ) by norm_num]
  exact coverp0000000001101010
private noncomputable def ep0000000001101011_0 : Blocks := edgeBlocks% "full/vectors/0000000001101011-E-0000.bin"
noncomputable def ep0000000001101011 : Blocks := ep0000000001101011_0
private theorem idp0000000001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110101.list =
    C ((2:ℤ)^91) * horner X vp0000000001101011.list + horner X ep0000000001101011.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001101011 : Branch 1 (-13011639/250000 : ℚ) vp000000000110101 := by
  apply branch_checked idp0000000001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-13011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-13136639/125000 : ℚ) by norm_num]
  exact coverp0000000001101011
theorem coverp000000000110101 : Covers (-13011639/250000 : ℚ) vp000000000110101 := join_branches bp0000000001101010 bp0000000001101011
private noncomputable def vp00000000011010011_0 : Blocks := edgeBlocks% "full/vectors/00000000011010011-V-0000.bin"
noncomputable def vp00000000011010011 : Blocks := vp00000000011010011_0
theorem coverp00000000011010011 : Covers (-12949139/62500 : ℚ) vp00000000011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001101001011_0 : Blocks := edgeBlocks% "full/vectors/0000000001101001011-V-0000.bin"
noncomputable def vp0000000001101001011 : Blocks := vp0000000001101001011_0
theorem coverp0000000001101001011 : Covers (-12933514/15625 : ℚ) vp0000000001101001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001101001010_0 : Blocks := edgeBlocks% "full/vectors/0000000001101001010-V-0000.bin"
noncomputable def vp0000000001101001010 : Blocks := vp0000000001101001010_0
theorem coverp0000000001101001010 : Covers (-12917889/15625 : ℚ) vp0000000001101001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110100101_0 : Blocks := edgeBlocks% "full/vectors/000000000110100101-V-0000.bin"
noncomputable def vp000000000110100101 : Blocks := vp000000000110100101_0
private theorem bp0000000001101001010 : Branch 0 (-12917889/31250 : ℚ) vp000000000110100101 := by
  apply branch_left_normalized (c:=vp0000000001101001010) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-12917889/31250 : ℚ) - ((0:ℤ):ℚ) = (-12917889/15625 : ℚ) by norm_num]
  exact coverp0000000001101001010
private noncomputable def ep0000000001101001011_0 : Blocks := edgeBlocks% "full/vectors/0000000001101001011-E-0000.bin"
noncomputable def ep0000000001101001011 : Blocks := ep0000000001101001011_0
private theorem idp0000000001101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110100101.list =
    C ((2:ℤ)^25) * horner X vp0000000001101001011.list + horner X ep0000000001101001011.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001101001011 : Branch 1 (-12917889/31250 : ℚ) vp000000000110100101 := by
  apply branch_checked idp0000000001101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-12917889/31250 : ℚ) - ((1:ℤ):ℚ) = (-12933514/15625 : ℚ) by norm_num]
  exact coverp0000000001101001011
theorem coverp000000000110100101 : Covers (-12917889/31250 : ℚ) vp000000000110100101 := join_branches bp0000000001101001010 bp0000000001101001011
private noncomputable def vp000000000110100100_0 : Blocks := edgeBlocks% "full/vectors/000000000110100100-V-0000.bin"
noncomputable def vp000000000110100100 : Blocks := vp000000000110100100_0
theorem coverp000000000110100100 : Covers (-12886639/31250 : ℚ) vp000000000110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011010010_0 : Blocks := edgeBlocks% "full/vectors/00000000011010010-V-0000.bin"
noncomputable def vp00000000011010010 : Blocks := vp00000000011010010_0
private theorem bp000000000110100100 : Branch 0 (-12886639/62500 : ℚ) vp00000000011010010 := by
  apply branch_left_normalized (c:=vp000000000110100100) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-12886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-12886639/31250 : ℚ) by norm_num]
  exact coverp000000000110100100
private noncomputable def ep000000000110100101_0 : Blocks := edgeBlocks% "full/vectors/000000000110100101-E-0000.bin"
noncomputable def ep000000000110100101 : Blocks := ep000000000110100101_0
private theorem idp000000000110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011010010.list =
    C ((2:ℤ)^38) * horner X vp000000000110100101.list + horner X ep000000000110100101.list := by
  exact edge_identity (B := (2:ℤ)^153) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110100101 : Branch 1 (-12886639/62500 : ℚ) vp00000000011010010 := by
  apply branch_checked idp000000000110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-12886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-12917889/31250 : ℚ) by norm_num]
  exact coverp000000000110100101
theorem coverp00000000011010010 : Covers (-12886639/62500 : ℚ) vp00000000011010010 := join_branches bp000000000110100100 bp000000000110100101
private noncomputable def vp0000000001101001_0 : Blocks := edgeBlocks% "full/vectors/0000000001101001-V-0000.bin"
noncomputable def vp0000000001101001 : Blocks := vp0000000001101001_0
private theorem bp00000000011010010 : Branch 0 (-12886639/125000 : ℚ) vp0000000001101001 := by
  apply branch_left_normalized (c:=vp00000000011010010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-12886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-12886639/62500 : ℚ) by norm_num]
  exact coverp00000000011010010
private noncomputable def ep00000000011010011_0 : Blocks := edgeBlocks% "full/vectors/00000000011010011-E-0000.bin"
noncomputable def ep00000000011010011 : Blocks := ep00000000011010011_0
private theorem idp00000000011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001101001.list =
    C ((2:ℤ)^56) * horner X vp00000000011010011.list + horner X ep00000000011010011.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011010011 : Branch 1 (-12886639/125000 : ℚ) vp0000000001101001 := by
  apply branch_checked idp00000000011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-12886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-12949139/62500 : ℚ) by norm_num]
  exact coverp00000000011010011
theorem coverp0000000001101001 : Covers (-12886639/125000 : ℚ) vp0000000001101001 := join_branches bp00000000011010010 bp00000000011010011
private noncomputable def vp000000000110100011_0 : Blocks := edgeBlocks% "full/vectors/000000000110100011-V-0000.bin"
noncomputable def vp000000000110100011 : Blocks := vp000000000110100011_0
theorem coverp000000000110100011 : Covers (-12855389/31250 : ℚ) vp000000000110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110100010_0 : Blocks := edgeBlocks% "full/vectors/000000000110100010-V-0000.bin"
noncomputable def vp000000000110100010 : Blocks := vp000000000110100010_0
theorem coverp000000000110100010 : Covers (-12824139/31250 : ℚ) vp000000000110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011010001_0 : Blocks := edgeBlocks% "full/vectors/00000000011010001-V-0000.bin"
noncomputable def vp00000000011010001 : Blocks := vp00000000011010001_0
private theorem bp000000000110100010 : Branch 0 (-12824139/62500 : ℚ) vp00000000011010001 := by
  apply branch_left_normalized (c:=vp000000000110100010) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-12824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-12824139/31250 : ℚ) by norm_num]
  exact coverp000000000110100010
private noncomputable def ep000000000110100011_0 : Blocks := edgeBlocks% "full/vectors/000000000110100011-E-0000.bin"
noncomputable def ep000000000110100011 : Blocks := ep000000000110100011_0
private theorem idp000000000110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011010001.list =
    C ((2:ℤ)^37) * horner X vp000000000110100011.list + horner X ep000000000110100011.list := by
  exact edge_identity (B := (2:ℤ)^151) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110100011 : Branch 1 (-12824139/62500 : ℚ) vp00000000011010001 := by
  apply branch_checked idp000000000110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-12824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-12855389/31250 : ℚ) by norm_num]
  exact coverp000000000110100011
theorem coverp00000000011010001 : Covers (-12824139/62500 : ℚ) vp00000000011010001 := join_branches bp000000000110100010 bp000000000110100011
private noncomputable def vp000000000110100001_0 : Blocks := edgeBlocks% "full/vectors/000000000110100001-V-0000.bin"
noncomputable def vp000000000110100001 : Blocks := vp000000000110100001_0
theorem coverp000000000110100001 : Covers (-12792889/31250 : ℚ) vp000000000110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110100000_0 : Blocks := edgeBlocks% "full/vectors/000000000110100000-V-0000.bin"
noncomputable def vp000000000110100000 : Blocks := vp000000000110100000_0
theorem coverp000000000110100000 : Covers (-12761639/31250 : ℚ) vp000000000110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011010000_0 : Blocks := edgeBlocks% "full/vectors/00000000011010000-V-0000.bin"
noncomputable def vp00000000011010000 : Blocks := vp00000000011010000_0
private theorem bp000000000110100000 : Branch 0 (-12761639/62500 : ℚ) vp00000000011010000 := by
  apply branch_left_normalized (c:=vp000000000110100000) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-12761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-12761639/31250 : ℚ) by norm_num]
  exact coverp000000000110100000
private noncomputable def ep000000000110100001_0 : Blocks := edgeBlocks% "full/vectors/000000000110100001-E-0000.bin"
noncomputable def ep000000000110100001 : Blocks := ep000000000110100001_0
private theorem idp000000000110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011010000.list =
    C ((2:ℤ)^37) * horner X vp000000000110100001.list + horner X ep000000000110100001.list := by
  exact edge_identity (B := (2:ℤ)^152) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110100001 : Branch 1 (-12761639/62500 : ℚ) vp00000000011010000 := by
  apply branch_checked idp000000000110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-12761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-12792889/31250 : ℚ) by norm_num]
  exact coverp000000000110100001
theorem coverp00000000011010000 : Covers (-12761639/62500 : ℚ) vp00000000011010000 := join_branches bp000000000110100000 bp000000000110100001
private noncomputable def vp0000000001101000_0 : Blocks := edgeBlocks% "full/vectors/0000000001101000-V-0000.bin"
noncomputable def vp0000000001101000 : Blocks := vp0000000001101000_0
private theorem bp00000000011010000 : Branch 0 (-12761639/125000 : ℚ) vp0000000001101000 := by
  apply branch_left_normalized (c:=vp00000000011010000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-12761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-12761639/62500 : ℚ) by norm_num]
  exact coverp00000000011010000
private noncomputable def ep00000000011010001_0 : Blocks := edgeBlocks% "full/vectors/00000000011010001-E-0000.bin"
noncomputable def ep00000000011010001 : Blocks := ep00000000011010001_0
private theorem idp00000000011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001101000.list =
    C ((2:ℤ)^57) * horner X vp00000000011010001.list + horner X ep00000000011010001.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011010001 : Branch 1 (-12761639/125000 : ℚ) vp0000000001101000 := by
  apply branch_checked idp00000000011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-12761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-12824139/62500 : ℚ) by norm_num]
  exact coverp00000000011010001
theorem coverp0000000001101000 : Covers (-12761639/125000 : ℚ) vp0000000001101000 := join_branches bp00000000011010000 bp00000000011010001
private noncomputable def vp000000000110100_0 : Blocks := edgeBlocks% "full/vectors/000000000110100-V-0000.bin"
noncomputable def vp000000000110100 : Blocks := vp000000000110100_0
private theorem bp0000000001101000 : Branch 0 (-12761639/250000 : ℚ) vp000000000110100 := by
  apply branch_left_normalized (c:=vp0000000001101000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-12761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-12761639/125000 : ℚ) by norm_num]
  exact coverp0000000001101000
private noncomputable def ep0000000001101001_0 : Blocks := edgeBlocks% "full/vectors/0000000001101001-E-0000.bin"
noncomputable def ep0000000001101001 : Blocks := ep0000000001101001_0
private theorem idp0000000001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110100.list =
    C ((2:ℤ)^93) * horner X vp0000000001101001.list + horner X ep0000000001101001.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001101001 : Branch 1 (-12761639/250000 : ℚ) vp000000000110100 := by
  apply branch_checked idp0000000001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-12761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-12886639/125000 : ℚ) by norm_num]
  exact coverp0000000001101001
theorem coverp000000000110100 : Covers (-12761639/250000 : ℚ) vp000000000110100 := join_branches bp0000000001101000 bp0000000001101001
private noncomputable def vp00000000011010_0 : Blocks := edgeBlocks% "full/vectors/00000000011010-V-0000.bin"
private noncomputable def vp00000000011010_1 : Blocks := edgeBlocks% "full/vectors/00000000011010-V-0001.bin"
noncomputable def vp00000000011010 : Blocks := (Blocks.join vp00000000011010_0 vp00000000011010_1)
private theorem bp000000000110100 : Branch 0 (-12761639/500000 : ℚ) vp00000000011010 := by
  apply branch_left_normalized (c:=vp000000000110100) (k:=0) (m:=91) (by decide +kernel)
  rw [show 2*(-12761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-12761639/250000 : ℚ) by norm_num]
  exact coverp000000000110100
private noncomputable def ep000000000110101_0 : Blocks := edgeBlocks% "full/vectors/000000000110101-E-0000.bin"
private noncomputable def ep000000000110101_1 : Blocks := edgeBlocks% "full/vectors/000000000110101-E-0001.bin"
noncomputable def ep000000000110101 : Blocks := (Blocks.join ep000000000110101_0 ep000000000110101_1)
private theorem idp000000000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011010.list =
    C ((2:ℤ)^169) * horner X vp000000000110101.list + horner X ep000000000110101.list := by
  exact edge_identity (B := (2:ℤ)^338) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110101 : Branch 1 (-12761639/500000 : ℚ) vp00000000011010 := by
  apply branch_checked idp000000000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-12761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-13011639/250000 : ℚ) by norm_num]
  exact coverp000000000110101
theorem coverp00000000011010 : Covers (-12761639/500000 : ℚ) vp00000000011010 := join_branches bp000000000110100 bp000000000110101
private noncomputable def vp0000000001101_0 : Blocks := edgeBlocks% "full/vectors/0000000001101-V-0000.bin"
private noncomputable def vp0000000001101_1 : Blocks := edgeBlocks% "full/vectors/0000000001101-V-0001.bin"
private noncomputable def vp0000000001101_2 : Blocks := edgeBlocks% "full/vectors/0000000001101-V-0002.bin"
noncomputable def vp0000000001101 : Blocks := (Blocks.join vp0000000001101_0 (Blocks.join vp0000000001101_1 vp0000000001101_2))
private theorem bp00000000011010 : Branch 0 (-12761639/1000000 : ℚ) vp0000000001101 := by
  apply branch_left_normalized (c:=vp00000000011010) (k:=0) (m:=160) (by decide +kernel)
  rw [show 2*(-12761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-12761639/500000 : ℚ) by norm_num]
  exact coverp00000000011010
private noncomputable def ep00000000011011_0 : Blocks := edgeBlocks% "full/vectors/00000000011011-E-0000.bin"
private noncomputable def ep00000000011011_1 : Blocks := edgeBlocks% "full/vectors/00000000011011-E-0001.bin"
private noncomputable def ep00000000011011_2 : Blocks := edgeBlocks% "full/vectors/00000000011011-E-0002.bin"
noncomputable def ep00000000011011 : Blocks := (Blocks.join ep00000000011011_0 (Blocks.join ep00000000011011_1 ep00000000011011_2))
private theorem idp00000000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001101.list =
    C ((2:ℤ)^310) * horner X vp00000000011011.list + horner X ep00000000011011.list := by
  exact edge_identity (B := (2:ℤ)^546) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011011 : Branch 1 (-12761639/1000000 : ℚ) vp0000000001101 := by
  apply branch_checked idp00000000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-12761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-13261639/500000 : ℚ) by norm_num]
  exact coverp00000000011011
theorem coverp0000000001101 : Covers (-12761639/1000000 : ℚ) vp0000000001101 := join_branches bp00000000011010 bp00000000011011
private noncomputable def vp000000000110011111_0 : Blocks := edgeBlocks% "full/vectors/000000000110011111-V-0000.bin"
noncomputable def vp000000000110011111 : Blocks := vp000000000110011111_0
theorem coverp000000000110011111 : Covers (-12730389/31250 : ℚ) vp000000000110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110011110_0 : Blocks := edgeBlocks% "full/vectors/000000000110011110-V-0000.bin"
noncomputable def vp000000000110011110 : Blocks := vp000000000110011110_0
theorem coverp000000000110011110 : Covers (-12699139/31250 : ℚ) vp000000000110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011001111_0 : Blocks := edgeBlocks% "full/vectors/00000000011001111-V-0000.bin"
noncomputable def vp00000000011001111 : Blocks := vp00000000011001111_0
private theorem bp000000000110011110 : Branch 0 (-12699139/62500 : ℚ) vp00000000011001111 := by
  apply branch_left_normalized (c:=vp000000000110011110) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-12699139/62500 : ℚ) - ((0:ℤ):ℚ) = (-12699139/31250 : ℚ) by norm_num]
  exact coverp000000000110011110
private noncomputable def ep000000000110011111_0 : Blocks := edgeBlocks% "full/vectors/000000000110011111-E-0000.bin"
noncomputable def ep000000000110011111 : Blocks := ep000000000110011111_0
private theorem idp000000000110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011001111.list =
    C ((2:ℤ)^37) * horner X vp000000000110011111.list + horner X ep000000000110011111.list := by
  exact edge_identity (B := (2:ℤ)^149) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110011111 : Branch 1 (-12699139/62500 : ℚ) vp00000000011001111 := by
  apply branch_checked idp000000000110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-12699139/62500 : ℚ) - ((1:ℤ):ℚ) = (-12730389/31250 : ℚ) by norm_num]
  exact coverp000000000110011111
theorem coverp00000000011001111 : Covers (-12699139/62500 : ℚ) vp00000000011001111 := join_branches bp000000000110011110 bp000000000110011111
private noncomputable def vp000000000110011101_0 : Blocks := edgeBlocks% "full/vectors/000000000110011101-V-0000.bin"
noncomputable def vp000000000110011101 : Blocks := vp000000000110011101_0
theorem coverp000000000110011101 : Covers (-12667889/31250 : ℚ) vp000000000110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110011100_0 : Blocks := edgeBlocks% "full/vectors/000000000110011100-V-0000.bin"
noncomputable def vp000000000110011100 : Blocks := vp000000000110011100_0
theorem coverp000000000110011100 : Covers (-12636639/31250 : ℚ) vp000000000110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011001110_0 : Blocks := edgeBlocks% "full/vectors/00000000011001110-V-0000.bin"
noncomputable def vp00000000011001110 : Blocks := vp00000000011001110_0
private theorem bp000000000110011100 : Branch 0 (-12636639/62500 : ℚ) vp00000000011001110 := by
  apply branch_left_normalized (c:=vp000000000110011100) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-12636639/62500 : ℚ) - ((0:ℤ):ℚ) = (-12636639/31250 : ℚ) by norm_num]
  exact coverp000000000110011100
private noncomputable def ep000000000110011101_0 : Blocks := edgeBlocks% "full/vectors/000000000110011101-E-0000.bin"
noncomputable def ep000000000110011101 : Blocks := ep000000000110011101_0
private theorem idp000000000110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011001110.list =
    C ((2:ℤ)^37) * horner X vp000000000110011101.list + horner X ep000000000110011101.list := by
  exact edge_identity (B := (2:ℤ)^148) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110011101 : Branch 1 (-12636639/62500 : ℚ) vp00000000011001110 := by
  apply branch_checked idp000000000110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-12636639/62500 : ℚ) - ((1:ℤ):ℚ) = (-12667889/31250 : ℚ) by norm_num]
  exact coverp000000000110011101
theorem coverp00000000011001110 : Covers (-12636639/62500 : ℚ) vp00000000011001110 := join_branches bp000000000110011100 bp000000000110011101
private noncomputable def vp0000000001100111_0 : Blocks := edgeBlocks% "full/vectors/0000000001100111-V-0000.bin"
noncomputable def vp0000000001100111 : Blocks := vp0000000001100111_0
private theorem bp00000000011001110 : Branch 0 (-12636639/125000 : ℚ) vp0000000001100111 := by
  apply branch_left_normalized (c:=vp00000000011001110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-12636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-12636639/62500 : ℚ) by norm_num]
  exact coverp00000000011001110
private noncomputable def ep00000000011001111_0 : Blocks := edgeBlocks% "full/vectors/00000000011001111-E-0000.bin"
noncomputable def ep00000000011001111 : Blocks := ep00000000011001111_0
private theorem idp00000000011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001100111.list =
    C ((2:ℤ)^56) * horner X vp00000000011001111.list + horner X ep00000000011001111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011001111 : Branch 1 (-12636639/125000 : ℚ) vp0000000001100111 := by
  apply branch_checked idp00000000011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-12636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-12699139/62500 : ℚ) by norm_num]
  exact coverp00000000011001111
theorem coverp0000000001100111 : Covers (-12636639/125000 : ℚ) vp0000000001100111 := join_branches bp00000000011001110 bp00000000011001111
private noncomputable def vp000000000110011011_0 : Blocks := edgeBlocks% "full/vectors/000000000110011011-V-0000.bin"
noncomputable def vp000000000110011011 : Blocks := vp000000000110011011_0
theorem coverp000000000110011011 : Covers (-12605389/31250 : ℚ) vp000000000110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110011010_0 : Blocks := edgeBlocks% "full/vectors/000000000110011010-V-0000.bin"
noncomputable def vp000000000110011010 : Blocks := vp000000000110011010_0
theorem coverp000000000110011010 : Covers (-12574139/31250 : ℚ) vp000000000110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011001101_0 : Blocks := edgeBlocks% "full/vectors/00000000011001101-V-0000.bin"
noncomputable def vp00000000011001101 : Blocks := vp00000000011001101_0
private theorem bp000000000110011010 : Branch 0 (-12574139/62500 : ℚ) vp00000000011001101 := by
  apply branch_left_normalized (c:=vp000000000110011010) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-12574139/62500 : ℚ) - ((0:ℤ):ℚ) = (-12574139/31250 : ℚ) by norm_num]
  exact coverp000000000110011010
private noncomputable def ep000000000110011011_0 : Blocks := edgeBlocks% "full/vectors/000000000110011011-E-0000.bin"
noncomputable def ep000000000110011011 : Blocks := ep000000000110011011_0
private theorem idp000000000110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011001101.list =
    C ((2:ℤ)^37) * horner X vp000000000110011011.list + horner X ep000000000110011011.list := by
  exact edge_identity (B := (2:ℤ)^147) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110011011 : Branch 1 (-12574139/62500 : ℚ) vp00000000011001101 := by
  apply branch_checked idp000000000110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-12574139/62500 : ℚ) - ((1:ℤ):ℚ) = (-12605389/31250 : ℚ) by norm_num]
  exact coverp000000000110011011
theorem coverp00000000011001101 : Covers (-12574139/62500 : ℚ) vp00000000011001101 := join_branches bp000000000110011010 bp000000000110011011
private noncomputable def vp00000000011001100_0 : Blocks := edgeBlocks% "full/vectors/00000000011001100-V-0000.bin"
noncomputable def vp00000000011001100 : Blocks := vp00000000011001100_0
theorem coverp00000000011001100 : Covers (-12511639/62500 : ℚ) vp00000000011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001100110_0 : Blocks := edgeBlocks% "full/vectors/0000000001100110-V-0000.bin"
noncomputable def vp0000000001100110 : Blocks := vp0000000001100110_0
private theorem bp00000000011001100 : Branch 0 (-12511639/125000 : ℚ) vp0000000001100110 := by
  apply branch_left_normalized (c:=vp00000000011001100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-12511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-12511639/62500 : ℚ) by norm_num]
  exact coverp00000000011001100
private noncomputable def ep00000000011001101_0 : Blocks := edgeBlocks% "full/vectors/00000000011001101-E-0000.bin"
noncomputable def ep00000000011001101 : Blocks := ep00000000011001101_0
private theorem idp00000000011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001100110.list =
    C ((2:ℤ)^56) * horner X vp00000000011001101.list + horner X ep00000000011001101.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011001101 : Branch 1 (-12511639/125000 : ℚ) vp0000000001100110 := by
  apply branch_checked idp00000000011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-12511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-12574139/62500 : ℚ) by norm_num]
  exact coverp00000000011001101
theorem coverp0000000001100110 : Covers (-12511639/125000 : ℚ) vp0000000001100110 := join_branches bp00000000011001100 bp00000000011001101
private noncomputable def vp000000000110011_0 : Blocks := edgeBlocks% "full/vectors/000000000110011-V-0000.bin"
noncomputable def vp000000000110011 : Blocks := vp000000000110011_0
private theorem bp0000000001100110 : Branch 0 (-12511639/250000 : ℚ) vp000000000110011 := by
  apply branch_left_normalized (c:=vp0000000001100110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-12511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-12511639/125000 : ℚ) by norm_num]
  exact coverp0000000001100110
private noncomputable def ep0000000001100111_0 : Blocks := edgeBlocks% "full/vectors/0000000001100111-E-0000.bin"
noncomputable def ep0000000001100111 : Blocks := ep0000000001100111_0
private theorem idp0000000001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110011.list =
    C ((2:ℤ)^92) * horner X vp0000000001100111.list + horner X ep0000000001100111.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001100111 : Branch 1 (-12511639/250000 : ℚ) vp000000000110011 := by
  apply branch_checked idp0000000001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-12511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-12636639/125000 : ℚ) by norm_num]
  exact coverp0000000001100111
theorem coverp000000000110011 : Covers (-12511639/250000 : ℚ) vp000000000110011 := join_branches bp0000000001100110 bp0000000001100111
private noncomputable def vp00000000011001011_0 : Blocks := edgeBlocks% "full/vectors/00000000011001011-V-0000.bin"
noncomputable def vp00000000011001011 : Blocks := vp00000000011001011_0
theorem coverp00000000011001011 : Covers (-12449139/62500 : ℚ) vp00000000011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110010101_0 : Blocks := edgeBlocks% "full/vectors/000000000110010101-V-0000.bin"
noncomputable def vp000000000110010101 : Blocks := vp000000000110010101_0
theorem coverp000000000110010101 : Covers (-12417889/31250 : ℚ) vp000000000110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110010100_0 : Blocks := edgeBlocks% "full/vectors/000000000110010100-V-0000.bin"
noncomputable def vp000000000110010100 : Blocks := vp000000000110010100_0
theorem coverp000000000110010100 : Covers (-12386639/31250 : ℚ) vp000000000110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011001010_0 : Blocks := edgeBlocks% "full/vectors/00000000011001010-V-0000.bin"
noncomputable def vp00000000011001010 : Blocks := vp00000000011001010_0
private theorem bp000000000110010100 : Branch 0 (-12386639/62500 : ℚ) vp00000000011001010 := by
  apply branch_left_normalized (c:=vp000000000110010100) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-12386639/62500 : ℚ) - ((0:ℤ):ℚ) = (-12386639/31250 : ℚ) by norm_num]
  exact coverp000000000110010100
private noncomputable def ep000000000110010101_0 : Blocks := edgeBlocks% "full/vectors/000000000110010101-E-0000.bin"
noncomputable def ep000000000110010101 : Blocks := ep000000000110010101_0
private theorem idp000000000110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011001010.list =
    C ((2:ℤ)^37) * horner X vp000000000110010101.list + horner X ep000000000110010101.list := by
  exact edge_identity (B := (2:ℤ)^146) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110010101 : Branch 1 (-12386639/62500 : ℚ) vp00000000011001010 := by
  apply branch_checked idp000000000110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-12386639/62500 : ℚ) - ((1:ℤ):ℚ) = (-12417889/31250 : ℚ) by norm_num]
  exact coverp000000000110010101
theorem coverp00000000011001010 : Covers (-12386639/62500 : ℚ) vp00000000011001010 := join_branches bp000000000110010100 bp000000000110010101
private noncomputable def vp0000000001100101_0 : Blocks := edgeBlocks% "full/vectors/0000000001100101-V-0000.bin"
noncomputable def vp0000000001100101 : Blocks := vp0000000001100101_0
private theorem bp00000000011001010 : Branch 0 (-12386639/125000 : ℚ) vp0000000001100101 := by
  apply branch_left_normalized (c:=vp00000000011001010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-12386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-12386639/62500 : ℚ) by norm_num]
  exact coverp00000000011001010
private noncomputable def ep00000000011001011_0 : Blocks := edgeBlocks% "full/vectors/00000000011001011-E-0000.bin"
noncomputable def ep00000000011001011 : Blocks := ep00000000011001011_0
private theorem idp00000000011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001100101.list =
    C ((2:ℤ)^56) * horner X vp00000000011001011.list + horner X ep00000000011001011.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011001011 : Branch 1 (-12386639/125000 : ℚ) vp0000000001100101 := by
  apply branch_checked idp00000000011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-12386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-12449139/62500 : ℚ) by norm_num]
  exact coverp00000000011001011
theorem coverp0000000001100101 : Covers (-12386639/125000 : ℚ) vp0000000001100101 := join_branches bp00000000011001010 bp00000000011001011
private noncomputable def vp0000000001100100111_0 : Blocks := edgeBlocks% "full/vectors/0000000001100100111-V-0000.bin"
noncomputable def vp0000000001100100111 : Blocks := vp0000000001100100111_0
theorem coverp0000000001100100111 : Covers (-12371014/15625 : ℚ) vp0000000001100100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001100100110_0 : Blocks := edgeBlocks% "full/vectors/0000000001100100110-V-0000.bin"
noncomputable def vp0000000001100100110 : Blocks := vp0000000001100100110_0
theorem coverp0000000001100100110 : Covers (-12355389/15625 : ℚ) vp0000000001100100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110010011_0 : Blocks := edgeBlocks% "full/vectors/000000000110010011-V-0000.bin"
noncomputable def vp000000000110010011 : Blocks := vp000000000110010011_0
private theorem bp0000000001100100110 : Branch 0 (-12355389/31250 : ℚ) vp000000000110010011 := by
  apply branch_left_normalized (c:=vp0000000001100100110) (k:=0) (m:=18) (by decide +kernel)
  rw [show 2*(-12355389/31250 : ℚ) - ((0:ℤ):ℚ) = (-12355389/15625 : ℚ) by norm_num]
  exact coverp0000000001100100110
private noncomputable def ep0000000001100100111_0 : Blocks := edgeBlocks% "full/vectors/0000000001100100111-E-0000.bin"
noncomputable def ep0000000001100100111 : Blocks := ep0000000001100100111_0
private theorem idp0000000001100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110010011.list =
    C ((2:ℤ)^25) * horner X vp0000000001100100111.list + horner X ep0000000001100100111.list := by
  exact edge_identity (B := (2:ℤ)^133) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001100100111 : Branch 1 (-12355389/31250 : ℚ) vp000000000110010011 := by
  apply branch_checked idp0000000001100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-12355389/31250 : ℚ) - ((1:ℤ):ℚ) = (-12371014/15625 : ℚ) by norm_num]
  exact coverp0000000001100100111
theorem coverp000000000110010011 : Covers (-12355389/31250 : ℚ) vp000000000110010011 := join_branches bp0000000001100100110 bp0000000001100100111
private noncomputable def vp0000000001100100101_0 : Blocks := edgeBlocks% "full/vectors/0000000001100100101-V-0000.bin"
noncomputable def vp0000000001100100101 : Blocks := vp0000000001100100101_0
theorem coverp0000000001100100101 : Covers (-12339764/15625 : ℚ) vp0000000001100100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001100100100_0 : Blocks := edgeBlocks% "full/vectors/0000000001100100100-V-0000.bin"
noncomputable def vp0000000001100100100 : Blocks := vp0000000001100100100_0
theorem coverp0000000001100100100 : Covers (-12324139/15625 : ℚ) vp0000000001100100100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110010010_0 : Blocks := edgeBlocks% "full/vectors/000000000110010010-V-0000.bin"
noncomputable def vp000000000110010010 : Blocks := vp000000000110010010_0
private theorem bp0000000001100100100 : Branch 0 (-12324139/31250 : ℚ) vp000000000110010010 := by
  apply branch_left_normalized (c:=vp0000000001100100100) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-12324139/31250 : ℚ) - ((0:ℤ):ℚ) = (-12324139/15625 : ℚ) by norm_num]
  exact coverp0000000001100100100
private noncomputable def ep0000000001100100101_0 : Blocks := edgeBlocks% "full/vectors/0000000001100100101-E-0000.bin"
noncomputable def ep0000000001100100101 : Blocks := ep0000000001100100101_0
private theorem idp0000000001100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110010010.list =
    C ((2:ℤ)^25) * horner X vp0000000001100100101.list + horner X ep0000000001100100101.list := by
  exact edge_identity (B := (2:ℤ)^135) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001100100101 : Branch 1 (-12324139/31250 : ℚ) vp000000000110010010 := by
  apply branch_checked idp0000000001100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-12324139/31250 : ℚ) - ((1:ℤ):ℚ) = (-12339764/15625 : ℚ) by norm_num]
  exact coverp0000000001100100101
theorem coverp000000000110010010 : Covers (-12324139/31250 : ℚ) vp000000000110010010 := join_branches bp0000000001100100100 bp0000000001100100101
private noncomputable def vp00000000011001001_0 : Blocks := edgeBlocks% "full/vectors/00000000011001001-V-0000.bin"
noncomputable def vp00000000011001001 : Blocks := vp00000000011001001_0
private theorem bp000000000110010010 : Branch 0 (-12324139/62500 : ℚ) vp00000000011001001 := by
  apply branch_left_normalized (c:=vp000000000110010010) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-12324139/62500 : ℚ) - ((0:ℤ):ℚ) = (-12324139/31250 : ℚ) by norm_num]
  exact coverp000000000110010010
private noncomputable def ep000000000110010011_0 : Blocks := edgeBlocks% "full/vectors/000000000110010011-E-0000.bin"
noncomputable def ep000000000110010011 : Blocks := ep000000000110010011_0
private theorem idp000000000110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011001001.list =
    C ((2:ℤ)^35) * horner X vp000000000110010011.list + horner X ep000000000110010011.list := by
  exact edge_identity (B := (2:ℤ)^146) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110010011 : Branch 1 (-12324139/62500 : ℚ) vp00000000011001001 := by
  apply branch_checked idp000000000110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-12324139/62500 : ℚ) - ((1:ℤ):ℚ) = (-12355389/31250 : ℚ) by norm_num]
  exact coverp000000000110010011
theorem coverp00000000011001001 : Covers (-12324139/62500 : ℚ) vp00000000011001001 := join_branches bp000000000110010010 bp000000000110010011
private noncomputable def vp000000000110010001_0 : Blocks := edgeBlocks% "full/vectors/000000000110010001-V-0000.bin"
noncomputable def vp000000000110010001 : Blocks := vp000000000110010001_0
theorem coverp000000000110010001 : Covers (-12292889/31250 : ℚ) vp000000000110010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110010000_0 : Blocks := edgeBlocks% "full/vectors/000000000110010000-V-0000.bin"
noncomputable def vp000000000110010000 : Blocks := vp000000000110010000_0
theorem coverp000000000110010000 : Covers (-12261639/31250 : ℚ) vp000000000110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011001000_0 : Blocks := edgeBlocks% "full/vectors/00000000011001000-V-0000.bin"
noncomputable def vp00000000011001000 : Blocks := vp00000000011001000_0
private theorem bp000000000110010000 : Branch 0 (-12261639/62500 : ℚ) vp00000000011001000 := by
  apply branch_left_normalized (c:=vp000000000110010000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-12261639/62500 : ℚ) - ((0:ℤ):ℚ) = (-12261639/31250 : ℚ) by norm_num]
  exact coverp000000000110010000
private noncomputable def ep000000000110010001_0 : Blocks := edgeBlocks% "full/vectors/000000000110010001-E-0000.bin"
noncomputable def ep000000000110010001 : Blocks := ep000000000110010001_0
private theorem idp000000000110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011001000.list =
    C ((2:ℤ)^35) * horner X vp000000000110010001.list + horner X ep000000000110010001.list := by
  exact edge_identity (B := (2:ℤ)^148) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110010001 : Branch 1 (-12261639/62500 : ℚ) vp00000000011001000 := by
  apply branch_checked idp000000000110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-12261639/62500 : ℚ) - ((1:ℤ):ℚ) = (-12292889/31250 : ℚ) by norm_num]
  exact coverp000000000110010001
theorem coverp00000000011001000 : Covers (-12261639/62500 : ℚ) vp00000000011001000 := join_branches bp000000000110010000 bp000000000110010001
private noncomputable def vp0000000001100100_0 : Blocks := edgeBlocks% "full/vectors/0000000001100100-V-0000.bin"
noncomputable def vp0000000001100100 : Blocks := vp0000000001100100_0
private theorem bp00000000011001000 : Branch 0 (-12261639/125000 : ℚ) vp0000000001100100 := by
  apply branch_left_normalized (c:=vp00000000011001000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-12261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-12261639/62500 : ℚ) by norm_num]
  exact coverp00000000011001000
private noncomputable def ep00000000011001001_0 : Blocks := edgeBlocks% "full/vectors/00000000011001001-E-0000.bin"
noncomputable def ep00000000011001001 : Blocks := ep00000000011001001_0
private theorem idp00000000011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001100100.list =
    C ((2:ℤ)^54) * horner X vp00000000011001001.list + horner X ep00000000011001001.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011001001 : Branch 1 (-12261639/125000 : ℚ) vp0000000001100100 := by
  apply branch_checked idp00000000011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-12261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-12324139/62500 : ℚ) by norm_num]
  exact coverp00000000011001001
theorem coverp0000000001100100 : Covers (-12261639/125000 : ℚ) vp0000000001100100 := join_branches bp00000000011001000 bp00000000011001001
private noncomputable def vp000000000110010_0 : Blocks := edgeBlocks% "full/vectors/000000000110010-V-0000.bin"
noncomputable def vp000000000110010 : Blocks := vp000000000110010_0
private theorem bp0000000001100100 : Branch 0 (-12261639/250000 : ℚ) vp000000000110010 := by
  apply branch_left_normalized (c:=vp0000000001100100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-12261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-12261639/125000 : ℚ) by norm_num]
  exact coverp0000000001100100
private noncomputable def ep0000000001100101_0 : Blocks := edgeBlocks% "full/vectors/0000000001100101-E-0000.bin"
noncomputable def ep0000000001100101 : Blocks := ep0000000001100101_0
private theorem idp0000000001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110010.list =
    C ((2:ℤ)^90) * horner X vp0000000001100101.list + horner X ep0000000001100101.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001100101 : Branch 1 (-12261639/250000 : ℚ) vp000000000110010 := by
  apply branch_checked idp0000000001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-12261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-12386639/125000 : ℚ) by norm_num]
  exact coverp0000000001100101
theorem coverp000000000110010 : Covers (-12261639/250000 : ℚ) vp000000000110010 := join_branches bp0000000001100100 bp0000000001100101
private noncomputable def vp00000000011001_0 : Blocks := edgeBlocks% "full/vectors/00000000011001-V-0000.bin"
private noncomputable def vp00000000011001_1 : Blocks := edgeBlocks% "full/vectors/00000000011001-V-0001.bin"
noncomputable def vp00000000011001 : Blocks := (Blocks.join vp00000000011001_0 vp00000000011001_1)
private theorem bp000000000110010 : Branch 0 (-12261639/500000 : ℚ) vp00000000011001 := by
  apply branch_left_normalized (c:=vp000000000110010) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-12261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-12261639/250000 : ℚ) by norm_num]
  exact coverp000000000110010
private noncomputable def ep000000000110011_0 : Blocks := edgeBlocks% "full/vectors/000000000110011-E-0000.bin"
private noncomputable def ep000000000110011_1 : Blocks := edgeBlocks% "full/vectors/000000000110011-E-0001.bin"
noncomputable def ep000000000110011 : Blocks := (Blocks.join ep000000000110011_0 ep000000000110011_1)
private theorem idp000000000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011001.list =
    C ((2:ℤ)^160) * horner X vp000000000110011.list + horner X ep000000000110011.list := by
  exact edge_identity (B := (2:ℤ)^333) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110011 : Branch 1 (-12261639/500000 : ℚ) vp00000000011001 := by
  apply branch_checked idp000000000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-12261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-12511639/250000 : ℚ) by norm_num]
  exact coverp000000000110011
theorem coverp00000000011001 : Covers (-12261639/500000 : ℚ) vp00000000011001 := join_branches bp000000000110010 bp000000000110011
private noncomputable def vp00000000011000111_0 : Blocks := edgeBlocks% "full/vectors/00000000011000111-V-0000.bin"
noncomputable def vp00000000011000111 : Blocks := vp00000000011000111_0
theorem coverp00000000011000111 : Covers (-12199139/62500 : ℚ) vp00000000011000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011000110_0 : Blocks := edgeBlocks% "full/vectors/00000000011000110-V-0000.bin"
noncomputable def vp00000000011000110 : Blocks := vp00000000011000110_0
theorem coverp00000000011000110 : Covers (-12136639/62500 : ℚ) vp00000000011000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001100011_0 : Blocks := edgeBlocks% "full/vectors/0000000001100011-V-0000.bin"
noncomputable def vp0000000001100011 : Blocks := vp0000000001100011_0
private theorem bp00000000011000110 : Branch 0 (-12136639/125000 : ℚ) vp0000000001100011 := by
  apply branch_left_normalized (c:=vp00000000011000110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-12136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-12136639/62500 : ℚ) by norm_num]
  exact coverp00000000011000110
private noncomputable def ep00000000011000111_0 : Blocks := edgeBlocks% "full/vectors/00000000011000111-E-0000.bin"
noncomputable def ep00000000011000111 : Blocks := ep00000000011000111_0
private theorem idp00000000011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001100011.list =
    C ((2:ℤ)^53) * horner X vp00000000011000111.list + horner X ep00000000011000111.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011000111 : Branch 1 (-12136639/125000 : ℚ) vp0000000001100011 := by
  apply branch_checked idp00000000011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-12136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-12199139/62500 : ℚ) by norm_num]
  exact coverp00000000011000111
theorem coverp0000000001100011 : Covers (-12136639/125000 : ℚ) vp0000000001100011 := join_branches bp00000000011000110 bp00000000011000111
private noncomputable def vp00000000011000101_0 : Blocks := edgeBlocks% "full/vectors/00000000011000101-V-0000.bin"
noncomputable def vp00000000011000101 : Blocks := vp00000000011000101_0
theorem coverp00000000011000101 : Covers (-12074139/62500 : ℚ) vp00000000011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011000100_0 : Blocks := edgeBlocks% "full/vectors/00000000011000100-V-0000.bin"
noncomputable def vp00000000011000100 : Blocks := vp00000000011000100_0
theorem coverp00000000011000100 : Covers (-12011639/62500 : ℚ) vp00000000011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001100010_0 : Blocks := edgeBlocks% "full/vectors/0000000001100010-V-0000.bin"
noncomputable def vp0000000001100010 : Blocks := vp0000000001100010_0
private theorem bp00000000011000100 : Branch 0 (-12011639/125000 : ℚ) vp0000000001100010 := by
  apply branch_left_normalized (c:=vp00000000011000100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-12011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-12011639/62500 : ℚ) by norm_num]
  exact coverp00000000011000100
private noncomputable def ep00000000011000101_0 : Blocks := edgeBlocks% "full/vectors/00000000011000101-E-0000.bin"
noncomputable def ep00000000011000101 : Blocks := ep00000000011000101_0
private theorem idp00000000011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001100010.list =
    C ((2:ℤ)^53) * horner X vp00000000011000101.list + horner X ep00000000011000101.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011000101 : Branch 1 (-12011639/125000 : ℚ) vp0000000001100010 := by
  apply branch_checked idp00000000011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-12011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-12074139/62500 : ℚ) by norm_num]
  exact coverp00000000011000101
theorem coverp0000000001100010 : Covers (-12011639/125000 : ℚ) vp0000000001100010 := join_branches bp00000000011000100 bp00000000011000101
private noncomputable def vp000000000110001_0 : Blocks := edgeBlocks% "full/vectors/000000000110001-V-0000.bin"
noncomputable def vp000000000110001 : Blocks := vp000000000110001_0
private theorem bp0000000001100010 : Branch 0 (-12011639/250000 : ℚ) vp000000000110001 := by
  apply branch_left_normalized (c:=vp0000000001100010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-12011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-12011639/125000 : ℚ) by norm_num]
  exact coverp0000000001100010
private noncomputable def ep0000000001100011_0 : Blocks := edgeBlocks% "full/vectors/0000000001100011-E-0000.bin"
noncomputable def ep0000000001100011 : Blocks := ep0000000001100011_0
private theorem idp0000000001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110001.list =
    C ((2:ℤ)^91) * horner X vp0000000001100011.list + horner X ep0000000001100011.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001100011 : Branch 1 (-12011639/250000 : ℚ) vp000000000110001 := by
  apply branch_checked idp0000000001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-12011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-12136639/125000 : ℚ) by norm_num]
  exact coverp0000000001100011
theorem coverp000000000110001 : Covers (-12011639/250000 : ℚ) vp000000000110001 := join_branches bp0000000001100010 bp0000000001100011
private noncomputable def vp00000000011000011_0 : Blocks := edgeBlocks% "full/vectors/00000000011000011-V-0000.bin"
noncomputable def vp00000000011000011 : Blocks := vp00000000011000011_0
theorem coverp00000000011000011 : Covers (-11949139/62500 : ℚ) vp00000000011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011000010_0 : Blocks := edgeBlocks% "full/vectors/00000000011000010-V-0000.bin"
noncomputable def vp00000000011000010 : Blocks := vp00000000011000010_0
theorem coverp00000000011000010 : Covers (-11886639/62500 : ℚ) vp00000000011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001100001_0 : Blocks := edgeBlocks% "full/vectors/0000000001100001-V-0000.bin"
noncomputable def vp0000000001100001 : Blocks := vp0000000001100001_0
private theorem bp00000000011000010 : Branch 0 (-11886639/125000 : ℚ) vp0000000001100001 := by
  apply branch_left_normalized (c:=vp00000000011000010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-11886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-11886639/62500 : ℚ) by norm_num]
  exact coverp00000000011000010
private noncomputable def ep00000000011000011_0 : Blocks := edgeBlocks% "full/vectors/00000000011000011-E-0000.bin"
noncomputable def ep00000000011000011 : Blocks := ep00000000011000011_0
private theorem idp00000000011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001100001.list =
    C ((2:ℤ)^54) * horner X vp00000000011000011.list + horner X ep00000000011000011.list := by
  exact edge_identity (B := (2:ℤ)^170) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011000011 : Branch 1 (-11886639/125000 : ℚ) vp0000000001100001 := by
  apply branch_checked idp00000000011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-11886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-11949139/62500 : ℚ) by norm_num]
  exact coverp00000000011000011
theorem coverp0000000001100001 : Covers (-11886639/125000 : ℚ) vp0000000001100001 := join_branches bp00000000011000010 bp00000000011000011
private noncomputable def vp00000000011000001_0 : Blocks := edgeBlocks% "full/vectors/00000000011000001-V-0000.bin"
noncomputable def vp00000000011000001 : Blocks := vp00000000011000001_0
theorem coverp00000000011000001 : Covers (-11824139/62500 : ℚ) vp00000000011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001100000011_0 : Blocks := edgeBlocks% "full/vectors/0000000001100000011-V-0000.bin"
noncomputable def vp0000000001100000011 : Blocks := vp0000000001100000011_0
theorem coverp0000000001100000011 : Covers (-11808514/15625 : ℚ) vp0000000001100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001100000010_0 : Blocks := edgeBlocks% "full/vectors/0000000001100000010-V-0000.bin"
noncomputable def vp0000000001100000010 : Blocks := vp0000000001100000010_0
theorem coverp0000000001100000010 : Covers (-11792889/15625 : ℚ) vp0000000001100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110000001_0 : Blocks := edgeBlocks% "full/vectors/000000000110000001-V-0000.bin"
noncomputable def vp000000000110000001 : Blocks := vp000000000110000001_0
private theorem bp0000000001100000010 : Branch 0 (-11792889/31250 : ℚ) vp000000000110000001 := by
  apply branch_left_normalized (c:=vp0000000001100000010) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-11792889/31250 : ℚ) - ((0:ℤ):ℚ) = (-11792889/15625 : ℚ) by norm_num]
  exact coverp0000000001100000010
private noncomputable def ep0000000001100000011_0 : Blocks := edgeBlocks% "full/vectors/0000000001100000011-E-0000.bin"
noncomputable def ep0000000001100000011 : Blocks := ep0000000001100000011_0
private theorem idp0000000001100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110000001.list =
    C ((2:ℤ)^26) * horner X vp0000000001100000011.list + horner X ep0000000001100000011.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001100000011 : Branch 1 (-11792889/31250 : ℚ) vp000000000110000001 := by
  apply branch_checked idp0000000001100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-11792889/31250 : ℚ) - ((1:ℤ):ℚ) = (-11808514/15625 : ℚ) by norm_num]
  exact coverp0000000001100000011
theorem coverp000000000110000001 : Covers (-11792889/31250 : ℚ) vp000000000110000001 := join_branches bp0000000001100000010 bp0000000001100000011
private noncomputable def vp00000000011000000011_0 : Blocks := edgeBlocks% "full/vectors/00000000011000000011-V-0000.bin"
noncomputable def vp00000000011000000011 : Blocks := vp00000000011000000011_0
theorem coverp00000000011000000011 : Covers (-23570153/15625 : ℚ) vp00000000011000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000011000000010_0 : Blocks := edgeBlocks% "full/vectors/00000000011000000010-V-0000.bin"
noncomputable def vp00000000011000000010 : Blocks := vp00000000011000000010_0
theorem coverp00000000011000000010 : Covers (-23554528/15625 : ℚ) vp00000000011000000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000001100000001_0 : Blocks := edgeBlocks% "full/vectors/0000000001100000001-V-0000.bin"
noncomputable def vp0000000001100000001 : Blocks := vp0000000001100000001_0
private theorem bp00000000011000000010 : Branch 0 (-11777264/15625 : ℚ) vp0000000001100000001 := by
  apply branch_left_normalized (c:=vp00000000011000000010) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-11777264/15625 : ℚ) - ((0:ℤ):ℚ) = (-23554528/15625 : ℚ) by norm_num]
  exact coverp00000000011000000010
private noncomputable def ep00000000011000000011_0 : Blocks := edgeBlocks% "full/vectors/00000000011000000011-E-0000.bin"
noncomputable def ep00000000011000000011 : Blocks := ep00000000011000000011_0
private theorem idp00000000011000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001100000001.list =
    C ((2:ℤ)^19) * horner X vp00000000011000000011.list + horner X ep00000000011000000011.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011000000011 : Branch 1 (-11777264/15625 : ℚ) vp0000000001100000001 := by
  apply branch_checked idp00000000011000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-11777264/15625 : ℚ) - ((1:ℤ):ℚ) = (-23570153/15625 : ℚ) by norm_num]
  exact coverp00000000011000000011
theorem coverp0000000001100000001 : Covers (-11777264/15625 : ℚ) vp0000000001100000001 := join_branches bp00000000011000000010 bp00000000011000000011
private noncomputable def vp0000000001100000000_0 : Blocks := edgeBlocks% "full/vectors/0000000001100000000-V-0000.bin"
noncomputable def vp0000000001100000000 : Blocks := vp0000000001100000000_0
theorem coverp0000000001100000000 : Covers (-11761639/15625 : ℚ) vp0000000001100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000110000000_0 : Blocks := edgeBlocks% "full/vectors/000000000110000000-V-0000.bin"
noncomputable def vp000000000110000000 : Blocks := vp000000000110000000_0
private theorem bp0000000001100000000 : Branch 0 (-11761639/31250 : ℚ) vp000000000110000000 := by
  apply branch_left_normalized (c:=vp0000000001100000000) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-11761639/31250 : ℚ) - ((0:ℤ):ℚ) = (-11761639/15625 : ℚ) by norm_num]
  exact coverp0000000001100000000
private noncomputable def ep0000000001100000001_0 : Blocks := edgeBlocks% "full/vectors/0000000001100000001-E-0000.bin"
noncomputable def ep0000000001100000001 : Blocks := ep0000000001100000001_0
private theorem idp0000000001100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110000000.list =
    C ((2:ℤ)^24) * horner X vp0000000001100000001.list + horner X ep0000000001100000001.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001100000001 : Branch 1 (-11761639/31250 : ℚ) vp000000000110000000 := by
  apply branch_checked idp0000000001100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-11761639/31250 : ℚ) - ((1:ℤ):ℚ) = (-11777264/15625 : ℚ) by norm_num]
  exact coverp0000000001100000001
theorem coverp000000000110000000 : Covers (-11761639/31250 : ℚ) vp000000000110000000 := join_branches bp0000000001100000000 bp0000000001100000001
private noncomputable def vp00000000011000000_0 : Blocks := edgeBlocks% "full/vectors/00000000011000000-V-0000.bin"
noncomputable def vp00000000011000000 : Blocks := vp00000000011000000_0
private theorem bp000000000110000000 : Branch 0 (-11761639/62500 : ℚ) vp00000000011000000 := by
  apply branch_left_normalized (c:=vp000000000110000000) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-11761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-11761639/31250 : ℚ) by norm_num]
  exact coverp000000000110000000
private noncomputable def ep000000000110000001_0 : Blocks := edgeBlocks% "full/vectors/000000000110000001-E-0000.bin"
noncomputable def ep000000000110000001 : Blocks := ep000000000110000001_0
private theorem idp000000000110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011000000.list =
    C ((2:ℤ)^36) * horner X vp000000000110000001.list + horner X ep000000000110000001.list := by
  exact edge_identity (B := (2:ℤ)^151) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110000001 : Branch 1 (-11761639/62500 : ℚ) vp00000000011000000 := by
  apply branch_checked idp000000000110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-11761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-11792889/31250 : ℚ) by norm_num]
  exact coverp000000000110000001
theorem coverp00000000011000000 : Covers (-11761639/62500 : ℚ) vp00000000011000000 := join_branches bp000000000110000000 bp000000000110000001
private noncomputable def vp0000000001100000_0 : Blocks := edgeBlocks% "full/vectors/0000000001100000-V-0000.bin"
noncomputable def vp0000000001100000 : Blocks := vp0000000001100000_0
private theorem bp00000000011000000 : Branch 0 (-11761639/125000 : ℚ) vp0000000001100000 := by
  apply branch_left_normalized (c:=vp00000000011000000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-11761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-11761639/62500 : ℚ) by norm_num]
  exact coverp00000000011000000
private noncomputable def ep00000000011000001_0 : Blocks := edgeBlocks% "full/vectors/00000000011000001-E-0000.bin"
noncomputable def ep00000000011000001 : Blocks := ep00000000011000001_0
private theorem idp00000000011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001100000.list =
    C ((2:ℤ)^57) * horner X vp00000000011000001.list + horner X ep00000000011000001.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011000001 : Branch 1 (-11761639/125000 : ℚ) vp0000000001100000 := by
  apply branch_checked idp00000000011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-11761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-11824139/62500 : ℚ) by norm_num]
  exact coverp00000000011000001
theorem coverp0000000001100000 : Covers (-11761639/125000 : ℚ) vp0000000001100000 := join_branches bp00000000011000000 bp00000000011000001
private noncomputable def vp000000000110000_0 : Blocks := edgeBlocks% "full/vectors/000000000110000-V-0000.bin"
noncomputable def vp000000000110000 : Blocks := vp000000000110000_0
private theorem bp0000000001100000 : Branch 0 (-11761639/250000 : ℚ) vp000000000110000 := by
  apply branch_left_normalized (c:=vp0000000001100000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-11761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-11761639/125000 : ℚ) by norm_num]
  exact coverp0000000001100000
private noncomputable def ep0000000001100001_0 : Blocks := edgeBlocks% "full/vectors/0000000001100001-E-0000.bin"
noncomputable def ep0000000001100001 : Blocks := ep0000000001100001_0
private theorem idp0000000001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110000.list =
    C ((2:ℤ)^98) * horner X vp0000000001100001.list + horner X ep0000000001100001.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001100001 : Branch 1 (-11761639/250000 : ℚ) vp000000000110000 := by
  apply branch_checked idp0000000001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-11761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-11886639/125000 : ℚ) by norm_num]
  exact coverp0000000001100001
theorem coverp000000000110000 : Covers (-11761639/250000 : ℚ) vp000000000110000 := join_branches bp0000000001100000 bp0000000001100001
private noncomputable def vp00000000011000_0 : Blocks := edgeBlocks% "full/vectors/00000000011000-V-0000.bin"
private noncomputable def vp00000000011000_1 : Blocks := edgeBlocks% "full/vectors/00000000011000-V-0001.bin"
noncomputable def vp00000000011000 : Blocks := (Blocks.join vp00000000011000_0 vp00000000011000_1)
private theorem bp000000000110000 : Branch 0 (-11761639/500000 : ℚ) vp00000000011000 := by
  apply branch_left_normalized (c:=vp000000000110000) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-11761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-11761639/250000 : ℚ) by norm_num]
  exact coverp000000000110000
private noncomputable def ep000000000110001_0 : Blocks := edgeBlocks% "full/vectors/000000000110001-E-0000.bin"
private noncomputable def ep000000000110001_1 : Blocks := edgeBlocks% "full/vectors/000000000110001-E-0001.bin"
noncomputable def ep000000000110001 : Blocks := (Blocks.join ep000000000110001_0 ep000000000110001_1)
private theorem idp000000000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011000.list =
    C ((2:ℤ)^169) * horner X vp000000000110001.list + horner X ep000000000110001.list := by
  exact edge_identity (B := (2:ℤ)^340) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000110001 : Branch 1 (-11761639/500000 : ℚ) vp00000000011000 := by
  apply branch_checked idp000000000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-11761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-12011639/250000 : ℚ) by norm_num]
  exact coverp000000000110001
theorem coverp00000000011000 : Covers (-11761639/500000 : ℚ) vp00000000011000 := join_branches bp000000000110000 bp000000000110001
private noncomputable def vp0000000001100_0 : Blocks := edgeBlocks% "full/vectors/0000000001100-V-0000.bin"
private noncomputable def vp0000000001100_1 : Blocks := edgeBlocks% "full/vectors/0000000001100-V-0001.bin"
private noncomputable def vp0000000001100_2 : Blocks := edgeBlocks% "full/vectors/0000000001100-V-0002.bin"
noncomputable def vp0000000001100 : Blocks := (Blocks.join vp0000000001100_0 (Blocks.join vp0000000001100_1 vp0000000001100_2))
private theorem bp00000000011000 : Branch 0 (-11761639/1000000 : ℚ) vp0000000001100 := by
  apply branch_left_normalized (c:=vp00000000011000) (k:=0) (m:=163) (by decide +kernel)
  rw [show 2*(-11761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-11761639/500000 : ℚ) by norm_num]
  exact coverp00000000011000
private noncomputable def ep00000000011001_0 : Blocks := edgeBlocks% "full/vectors/00000000011001-E-0000.bin"
private noncomputable def ep00000000011001_1 : Blocks := edgeBlocks% "full/vectors/00000000011001-E-0001.bin"
private noncomputable def ep00000000011001_2 : Blocks := edgeBlocks% "full/vectors/00000000011001-E-0002.bin"
noncomputable def ep00000000011001 : Blocks := (Blocks.join ep00000000011001_0 (Blocks.join ep00000000011001_1 ep00000000011001_2))
private theorem idp00000000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000001100.list =
    C ((2:ℤ)^310) * horner X vp00000000011001.list + horner X ep00000000011001.list := by
  exact edge_identity (B := (2:ℤ)^556) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000011001 : Branch 1 (-11761639/1000000 : ℚ) vp0000000001100 := by
  apply branch_checked idp00000000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-11761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-12261639/500000 : ℚ) by norm_num]
  exact coverp00000000011001
theorem coverp0000000001100 : Covers (-11761639/1000000 : ℚ) vp0000000001100 := join_branches bp00000000011000 bp00000000011001
private noncomputable def vp000000000110_0 : Blocks := edgeBlocks% "full/vectors/000000000110-V-0000.bin"
private noncomputable def vp000000000110_1 : Blocks := edgeBlocks% "full/vectors/000000000110-V-0001.bin"
private noncomputable def vp000000000110_2 : Blocks := edgeBlocks% "full/vectors/000000000110-V-0002.bin"
private noncomputable def vp000000000110_3 : Blocks := edgeBlocks% "full/vectors/000000000110-V-0003.bin"
private noncomputable def vp000000000110_4 : Blocks := edgeBlocks% "full/vectors/000000000110-V-0004.bin"
noncomputable def vp000000000110 : Blocks := (Blocks.join (Blocks.join vp000000000110_0 vp000000000110_1) (Blocks.join vp000000000110_2 (Blocks.join vp000000000110_3 vp000000000110_4)))
private theorem bp0000000001100 : Branch 0 (-11761639/2000000 : ℚ) vp000000000110 := by
  apply branch_left_normalized (c:=vp0000000001100) (k:=0) (m:=304) (by decide +kernel)
  rw [show 2*(-11761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-11761639/1000000 : ℚ) by norm_num]
  exact coverp0000000001100
private noncomputable def ep0000000001101_0 : Blocks := edgeBlocks% "full/vectors/0000000001101-E-0000.bin"
private noncomputable def ep0000000001101_1 : Blocks := edgeBlocks% "full/vectors/0000000001101-E-0001.bin"
private noncomputable def ep0000000001101_2 : Blocks := edgeBlocks% "full/vectors/0000000001101-E-0002.bin"
private noncomputable def ep0000000001101_3 : Blocks := edgeBlocks% "full/vectors/0000000001101-E-0003.bin"
private noncomputable def ep0000000001101_4 : Blocks := edgeBlocks% "full/vectors/0000000001101-E-0004.bin"
noncomputable def ep0000000001101 : Blocks := (Blocks.join (Blocks.join ep0000000001101_0 ep0000000001101_1) (Blocks.join ep0000000001101_2 (Blocks.join ep0000000001101_3 ep0000000001101_4)))
private theorem idp0000000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000110.list =
    C ((2:ℤ)^588) * horner X vp0000000001101.list + horner X ep0000000001101.list := by
  exact edge_identity (B := (2:ℤ)^987) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000001101 : Branch 1 (-11761639/2000000 : ℚ) vp000000000110 := by
  apply branch_checked idp0000000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-11761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-12761639/1000000 : ℚ) by norm_num]
  exact coverp0000000001101
theorem coverp000000000110 : Covers (-11761639/2000000 : ℚ) vp000000000110 := join_branches bp0000000001100 bp0000000001101
private noncomputable def vp00000000011_0 : Blocks := edgeBlocks% "full/vectors/00000000011-V-0000.bin"
private noncomputable def vp00000000011_1 : Blocks := edgeBlocks% "full/vectors/00000000011-V-0001.bin"
private noncomputable def vp00000000011_2 : Blocks := edgeBlocks% "full/vectors/00000000011-V-0002.bin"
private noncomputable def vp00000000011_3 : Blocks := edgeBlocks% "full/vectors/00000000011-V-0003.bin"
private noncomputable def vp00000000011_4 : Blocks := edgeBlocks% "full/vectors/00000000011-V-0004.bin"
private noncomputable def vp00000000011_5 : Blocks := edgeBlocks% "full/vectors/00000000011-V-0005.bin"
private noncomputable def vp00000000011_6 : Blocks := edgeBlocks% "full/vectors/00000000011-V-0006.bin"
private noncomputable def vp00000000011_7 : Blocks := edgeBlocks% "full/vectors/00000000011-V-0007.bin"
private noncomputable def vp00000000011_8 : Blocks := edgeBlocks% "full/vectors/00000000011-V-0008.bin"
noncomputable def vp00000000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00000000011_0 vp00000000011_1) (Blocks.join vp00000000011_2 vp00000000011_3)) (Blocks.join (Blocks.join vp00000000011_4 vp00000000011_5) (Blocks.join vp00000000011_6 (Blocks.join vp00000000011_7 vp00000000011_8))))
private theorem bp000000000110 : Branch 0 (-11761639/4000000 : ℚ) vp00000000011 := by
  apply branch_left_normalized (c:=vp000000000110) (k:=0) (m:=585) (by decide +kernel)
  rw [show 2*(-11761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-11761639/2000000 : ℚ) by norm_num]
  exact coverp000000000110
private noncomputable def ep000000000111_0 : Blocks := edgeBlocks% "full/vectors/000000000111-E-0000.bin"
private noncomputable def ep000000000111_1 : Blocks := edgeBlocks% "full/vectors/000000000111-E-0001.bin"
private noncomputable def ep000000000111_2 : Blocks := edgeBlocks% "full/vectors/000000000111-E-0002.bin"
private noncomputable def ep000000000111_3 : Blocks := edgeBlocks% "full/vectors/000000000111-E-0003.bin"
private noncomputable def ep000000000111_4 : Blocks := edgeBlocks% "full/vectors/000000000111-E-0004.bin"
private noncomputable def ep000000000111_5 : Blocks := edgeBlocks% "full/vectors/000000000111-E-0005.bin"
private noncomputable def ep000000000111_6 : Blocks := edgeBlocks% "full/vectors/000000000111-E-0006.bin"
private noncomputable def ep000000000111_7 : Blocks := edgeBlocks% "full/vectors/000000000111-E-0007.bin"
private noncomputable def ep000000000111_8 : Blocks := edgeBlocks% "full/vectors/000000000111-E-0008.bin"
noncomputable def ep000000000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000000000111_0 ep000000000111_1) (Blocks.join ep000000000111_2 ep000000000111_3)) (Blocks.join (Blocks.join ep000000000111_4 ep000000000111_5) (Blocks.join ep000000000111_6 (Blocks.join ep000000000111_7 ep000000000111_8))))
private theorem idp000000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000011.list =
    C ((2:ℤ)^1147) * horner X vp000000000111.list + horner X ep000000000111.list := by
  exact edge_identity (B := (2:ℤ)^1839) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000111 : Branch 1 (-11761639/4000000 : ℚ) vp00000000011 := by
  apply branch_checked idp000000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-11761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-13761639/2000000 : ℚ) by norm_num]
  exact coverp000000000111
theorem coverp00000000011 : Covers (-11761639/4000000 : ℚ) vp00000000011 := join_branches bp000000000110 bp000000000111
end NextProof.EdgeFull

