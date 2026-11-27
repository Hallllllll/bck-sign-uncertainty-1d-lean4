import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00012

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000000001101111_0 : Blocks := edgeBlocks% "full/vectors/00000000001101111-V-0000.bin"
noncomputable def vp00000000001101111 : Blocks := vp00000000001101111_0
theorem coverp00000000001101111 : Covers (-6699139/62500 : ℚ) vp00000000001101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011011101_0 : Blocks := edgeBlocks% "full/vectors/000000000011011101-V-0000.bin"
noncomputable def vp000000000011011101 : Blocks := vp000000000011011101_0
theorem coverp000000000011011101 : Covers (-6667889/31250 : ℚ) vp000000000011011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011011100_0 : Blocks := edgeBlocks% "full/vectors/000000000011011100-V-0000.bin"
noncomputable def vp000000000011011100 : Blocks := vp000000000011011100_0
theorem coverp000000000011011100 : Covers (-6636639/31250 : ℚ) vp000000000011011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001101110_0 : Blocks := edgeBlocks% "full/vectors/00000000001101110-V-0000.bin"
noncomputable def vp00000000001101110 : Blocks := vp00000000001101110_0
private theorem bp000000000011011100 : Branch 0 (-6636639/62500 : ℚ) vp00000000001101110 := by
  apply branch_left_normalized (c:=vp000000000011011100) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-6636639/62500 : ℚ) - ((0:ℤ):ℚ) = (-6636639/31250 : ℚ) by norm_num]
  exact coverp000000000011011100
private noncomputable def ep000000000011011101_0 : Blocks := edgeBlocks% "full/vectors/000000000011011101-E-0000.bin"
noncomputable def ep000000000011011101 : Blocks := ep000000000011011101_0
private theorem idp000000000011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001101110.list =
    C ((2:ℤ)^42) * horner X vp000000000011011101.list + horner X ep000000000011011101.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011011101 : Branch 1 (-6636639/62500 : ℚ) vp00000000001101110 := by
  apply branch_checked idp000000000011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-6636639/62500 : ℚ) - ((1:ℤ):ℚ) = (-6667889/31250 : ℚ) by norm_num]
  exact coverp000000000011011101
theorem coverp00000000001101110 : Covers (-6636639/62500 : ℚ) vp00000000001101110 := join_branches bp000000000011011100 bp000000000011011101
private noncomputable def vp0000000000110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110111-V-0000.bin"
noncomputable def vp0000000000110111 : Blocks := vp0000000000110111_0
private theorem bp00000000001101110 : Branch 0 (-6636639/125000 : ℚ) vp0000000000110111 := by
  apply branch_left_normalized (c:=vp00000000001101110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-6636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-6636639/62500 : ℚ) by norm_num]
  exact coverp00000000001101110
private noncomputable def ep00000000001101111_0 : Blocks := edgeBlocks% "full/vectors/00000000001101111-E-0000.bin"
noncomputable def ep00000000001101111 : Blocks := ep00000000001101111_0
private theorem idp00000000001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110111.list =
    C ((2:ℤ)^67) * horner X vp00000000001101111.list + horner X ep00000000001101111.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001101111 : Branch 1 (-6636639/125000 : ℚ) vp0000000000110111 := by
  apply branch_checked idp00000000001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-6636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-6699139/62500 : ℚ) by norm_num]
  exact coverp00000000001101111
theorem coverp0000000000110111 : Covers (-6636639/125000 : ℚ) vp0000000000110111 := join_branches bp00000000001101110 bp00000000001101111
private noncomputable def vp000000000011011011_0 : Blocks := edgeBlocks% "full/vectors/000000000011011011-V-0000.bin"
noncomputable def vp000000000011011011 : Blocks := vp000000000011011011_0
theorem coverp000000000011011011 : Covers (-6605389/31250 : ℚ) vp000000000011011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011011010_0 : Blocks := edgeBlocks% "full/vectors/000000000011011010-V-0000.bin"
noncomputable def vp000000000011011010 : Blocks := vp000000000011011010_0
theorem coverp000000000011011010 : Covers (-6574139/31250 : ℚ) vp000000000011011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001101101_0 : Blocks := edgeBlocks% "full/vectors/00000000001101101-V-0000.bin"
noncomputable def vp00000000001101101 : Blocks := vp00000000001101101_0
private theorem bp000000000011011010 : Branch 0 (-6574139/62500 : ℚ) vp00000000001101101 := by
  apply branch_left_normalized (c:=vp000000000011011010) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-6574139/62500 : ℚ) - ((0:ℤ):ℚ) = (-6574139/31250 : ℚ) by norm_num]
  exact coverp000000000011011010
private noncomputable def ep000000000011011011_0 : Blocks := edgeBlocks% "full/vectors/000000000011011011-E-0000.bin"
noncomputable def ep000000000011011011 : Blocks := ep000000000011011011_0
private theorem idp000000000011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001101101.list =
    C ((2:ℤ)^42) * horner X vp000000000011011011.list + horner X ep000000000011011011.list := by
  exact edge_identity (B := (2:ℤ)^154) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011011011 : Branch 1 (-6574139/62500 : ℚ) vp00000000001101101 := by
  apply branch_checked idp000000000011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-6574139/62500 : ℚ) - ((1:ℤ):ℚ) = (-6605389/31250 : ℚ) by norm_num]
  exact coverp000000000011011011
theorem coverp00000000001101101 : Covers (-6574139/62500 : ℚ) vp00000000001101101 := join_branches bp000000000011011010 bp000000000011011011
private noncomputable def vp000000000011011001_0 : Blocks := edgeBlocks% "full/vectors/000000000011011001-V-0000.bin"
noncomputable def vp000000000011011001 : Blocks := vp000000000011011001_0
theorem coverp000000000011011001 : Covers (-6542889/31250 : ℚ) vp000000000011011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011011000_0 : Blocks := edgeBlocks% "full/vectors/000000000011011000-V-0000.bin"
noncomputable def vp000000000011011000 : Blocks := vp000000000011011000_0
theorem coverp000000000011011000 : Covers (-6511639/31250 : ℚ) vp000000000011011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001101100_0 : Blocks := edgeBlocks% "full/vectors/00000000001101100-V-0000.bin"
noncomputable def vp00000000001101100 : Blocks := vp00000000001101100_0
private theorem bp000000000011011000 : Branch 0 (-6511639/62500 : ℚ) vp00000000001101100 := by
  apply branch_left_normalized (c:=vp000000000011011000) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-6511639/62500 : ℚ) - ((0:ℤ):ℚ) = (-6511639/31250 : ℚ) by norm_num]
  exact coverp000000000011011000
private noncomputable def ep000000000011011001_0 : Blocks := edgeBlocks% "full/vectors/000000000011011001-E-0000.bin"
noncomputable def ep000000000011011001 : Blocks := ep000000000011011001_0
private theorem idp000000000011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001101100.list =
    C ((2:ℤ)^41) * horner X vp000000000011011001.list + horner X ep000000000011011001.list := by
  exact edge_identity (B := (2:ℤ)^154) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011011001 : Branch 1 (-6511639/62500 : ℚ) vp00000000001101100 := by
  apply branch_checked idp000000000011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-6511639/62500 : ℚ) - ((1:ℤ):ℚ) = (-6542889/31250 : ℚ) by norm_num]
  exact coverp000000000011011001
theorem coverp00000000001101100 : Covers (-6511639/62500 : ℚ) vp00000000001101100 := join_branches bp000000000011011000 bp000000000011011001
private noncomputable def vp0000000000110110_0 : Blocks := edgeBlocks% "full/vectors/0000000000110110-V-0000.bin"
noncomputable def vp0000000000110110 : Blocks := vp0000000000110110_0
private theorem bp00000000001101100 : Branch 0 (-6511639/125000 : ℚ) vp0000000000110110 := by
  apply branch_left_normalized (c:=vp00000000001101100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-6511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-6511639/62500 : ℚ) by norm_num]
  exact coverp00000000001101100
private noncomputable def ep00000000001101101_0 : Blocks := edgeBlocks% "full/vectors/00000000001101101-E-0000.bin"
noncomputable def ep00000000001101101 : Blocks := ep00000000001101101_0
private theorem idp00000000001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110110.list =
    C ((2:ℤ)^67) * horner X vp00000000001101101.list + horner X ep00000000001101101.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001101101 : Branch 1 (-6511639/125000 : ℚ) vp0000000000110110 := by
  apply branch_checked idp00000000001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-6511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-6574139/62500 : ℚ) by norm_num]
  exact coverp00000000001101101
theorem coverp0000000000110110 : Covers (-6511639/125000 : ℚ) vp0000000000110110 := join_branches bp00000000001101100 bp00000000001101101
private noncomputable def vp000000000011011_0 : Blocks := edgeBlocks% "full/vectors/000000000011011-V-0000.bin"
noncomputable def vp000000000011011 : Blocks := vp000000000011011_0
private theorem bp0000000000110110 : Branch 0 (-6511639/250000 : ℚ) vp000000000011011 := by
  apply branch_left_normalized (c:=vp0000000000110110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-6511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-6511639/125000 : ℚ) by norm_num]
  exact coverp0000000000110110
private noncomputable def ep0000000000110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110111-E-0000.bin"
noncomputable def ep0000000000110111 : Blocks := ep0000000000110111_0
private theorem idp0000000000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011011.list =
    C ((2:ℤ)^115) * horner X vp0000000000110111.list + horner X ep0000000000110111.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110111 : Branch 1 (-6511639/250000 : ℚ) vp000000000011011 := by
  apply branch_checked idp0000000000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-6511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-6636639/125000 : ℚ) by norm_num]
  exact coverp0000000000110111
theorem coverp000000000011011 : Covers (-6511639/250000 : ℚ) vp000000000011011 := join_branches bp0000000000110110 bp0000000000110111
private noncomputable def vp00000000001101011_0 : Blocks := edgeBlocks% "full/vectors/00000000001101011-V-0000.bin"
noncomputable def vp00000000001101011 : Blocks := vp00000000001101011_0
theorem coverp00000000001101011 : Covers (-6449139/62500 : ℚ) vp00000000001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011010101_0 : Blocks := edgeBlocks% "full/vectors/000000000011010101-V-0000.bin"
noncomputable def vp000000000011010101 : Blocks := vp000000000011010101_0
theorem coverp000000000011010101 : Covers (-6417889/31250 : ℚ) vp000000000011010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011010100_0 : Blocks := edgeBlocks% "full/vectors/000000000011010100-V-0000.bin"
noncomputable def vp000000000011010100 : Blocks := vp000000000011010100_0
theorem coverp000000000011010100 : Covers (-6386639/31250 : ℚ) vp000000000011010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001101010_0 : Blocks := edgeBlocks% "full/vectors/00000000001101010-V-0000.bin"
noncomputable def vp00000000001101010 : Blocks := vp00000000001101010_0
private theorem bp000000000011010100 : Branch 0 (-6386639/62500 : ℚ) vp00000000001101010 := by
  apply branch_left_normalized (c:=vp000000000011010100) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-6386639/62500 : ℚ) - ((0:ℤ):ℚ) = (-6386639/31250 : ℚ) by norm_num]
  exact coverp000000000011010100
private noncomputable def ep000000000011010101_0 : Blocks := edgeBlocks% "full/vectors/000000000011010101-E-0000.bin"
noncomputable def ep000000000011010101 : Blocks := ep000000000011010101_0
private theorem idp000000000011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001101010.list =
    C ((2:ℤ)^44) * horner X vp000000000011010101.list + horner X ep000000000011010101.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011010101 : Branch 1 (-6386639/62500 : ℚ) vp00000000001101010 := by
  apply branch_checked idp000000000011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-6386639/62500 : ℚ) - ((1:ℤ):ℚ) = (-6417889/31250 : ℚ) by norm_num]
  exact coverp000000000011010101
theorem coverp00000000001101010 : Covers (-6386639/62500 : ℚ) vp00000000001101010 := join_branches bp000000000011010100 bp000000000011010101
private noncomputable def vp0000000000110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110101-V-0000.bin"
noncomputable def vp0000000000110101 : Blocks := vp0000000000110101_0
private theorem bp00000000001101010 : Branch 0 (-6386639/125000 : ℚ) vp0000000000110101 := by
  apply branch_left_normalized (c:=vp00000000001101010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-6386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-6386639/62500 : ℚ) by norm_num]
  exact coverp00000000001101010
private noncomputable def ep00000000001101011_0 : Blocks := edgeBlocks% "full/vectors/00000000001101011-E-0000.bin"
noncomputable def ep00000000001101011 : Blocks := ep00000000001101011_0
private theorem idp00000000001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110101.list =
    C ((2:ℤ)^69) * horner X vp00000000001101011.list + horner X ep00000000001101011.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001101011 : Branch 1 (-6386639/125000 : ℚ) vp0000000000110101 := by
  apply branch_checked idp00000000001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-6386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-6449139/62500 : ℚ) by norm_num]
  exact coverp00000000001101011
theorem coverp0000000000110101 : Covers (-6386639/125000 : ℚ) vp0000000000110101 := join_branches bp00000000001101010 bp00000000001101011
private noncomputable def vp0000000000110100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110100111-V-0000.bin"
noncomputable def vp0000000000110100111 : Blocks := vp0000000000110100111_0
theorem coverp0000000000110100111 : Covers (-6371014/15625 : ℚ) vp0000000000110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001101001101_0 : Blocks := edgeBlocks% "full/vectors/00000000001101001101-V-0000.bin"
noncomputable def vp00000000001101001101 : Blocks := vp00000000001101001101_0
theorem coverp00000000001101001101 : Covers (-12726403/15625 : ℚ) vp00000000001101001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001101001100_0 : Blocks := edgeBlocks% "full/vectors/00000000001101001100-V-0000.bin"
noncomputable def vp00000000001101001100 : Blocks := vp00000000001101001100_0
theorem coverp00000000001101001100 : Covers (-12710778/15625 : ℚ) vp00000000001101001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110100110_0 : Blocks := edgeBlocks% "full/vectors/0000000000110100110-V-0000.bin"
noncomputable def vp0000000000110100110 : Blocks := vp0000000000110100110_0
private theorem bp00000000001101001100 : Branch 0 (-6355389/15625 : ℚ) vp0000000000110100110 := by
  apply branch_left_normalized (c:=vp00000000001101001100) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-6355389/15625 : ℚ) - ((0:ℤ):ℚ) = (-12710778/15625 : ℚ) by norm_num]
  exact coverp00000000001101001100
private noncomputable def ep00000000001101001101_0 : Blocks := edgeBlocks% "full/vectors/00000000001101001101-E-0000.bin"
noncomputable def ep00000000001101001101 : Blocks := ep00000000001101001101_0
private theorem idp00000000001101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110100110.list =
    C ((2:ℤ)^21) * horner X vp00000000001101001101.list + horner X ep00000000001101001101.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001101001101 : Branch 1 (-6355389/15625 : ℚ) vp0000000000110100110 := by
  apply branch_checked idp00000000001101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-6355389/15625 : ℚ) - ((1:ℤ):ℚ) = (-12726403/15625 : ℚ) by norm_num]
  exact coverp00000000001101001101
theorem coverp0000000000110100110 : Covers (-6355389/15625 : ℚ) vp0000000000110100110 := join_branches bp00000000001101001100 bp00000000001101001101
private noncomputable def vp000000000011010011_0 : Blocks := edgeBlocks% "full/vectors/000000000011010011-V-0000.bin"
noncomputable def vp000000000011010011 : Blocks := vp000000000011010011_0
private theorem bp0000000000110100110 : Branch 0 (-6355389/31250 : ℚ) vp000000000011010011 := by
  apply branch_left_normalized (c:=vp0000000000110100110) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-6355389/31250 : ℚ) - ((0:ℤ):ℚ) = (-6355389/15625 : ℚ) by norm_num]
  exact coverp0000000000110100110
private noncomputable def ep0000000000110100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110100111-E-0000.bin"
noncomputable def ep0000000000110100111 : Blocks := ep0000000000110100111_0
private theorem idp0000000000110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011010011.list =
    C ((2:ℤ)^30) * horner X vp0000000000110100111.list + horner X ep0000000000110100111.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110100111 : Branch 1 (-6355389/31250 : ℚ) vp000000000011010011 := by
  apply branch_checked idp0000000000110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-6355389/31250 : ℚ) - ((1:ℤ):ℚ) = (-6371014/15625 : ℚ) by norm_num]
  exact coverp0000000000110100111
theorem coverp000000000011010011 : Covers (-6355389/31250 : ℚ) vp000000000011010011 := join_branches bp0000000000110100110 bp0000000000110100111
private noncomputable def vp0000000000110100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110100101-V-0000.bin"
noncomputable def vp0000000000110100101 : Blocks := vp0000000000110100101_0
theorem coverp0000000000110100101 : Covers (-6339764/15625 : ℚ) vp0000000000110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011010010011_0 : Blocks := edgeBlocks% "full/vectors/000000000011010010011-V-0000.bin"
noncomputable def vp000000000011010010011 : Blocks := vp000000000011010010011_0
theorem coverp000000000011010010011 : Covers (-25343431/15625 : ℚ) vp000000000011010010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011010010010_0 : Blocks := edgeBlocks% "full/vectors/000000000011010010010-V-0000.bin"
noncomputable def vp000000000011010010010 : Blocks := vp000000000011010010010_0
theorem coverp000000000011010010010 : Covers (-25327806/15625 : ℚ) vp000000000011010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001101001001_0 : Blocks := edgeBlocks% "full/vectors/00000000001101001001-V-0000.bin"
noncomputable def vp00000000001101001001 : Blocks := vp00000000001101001001_0
private theorem bp000000000011010010010 : Branch 0 (-12663903/15625 : ℚ) vp00000000001101001001 := by
  apply branch_left_normalized (c:=vp000000000011010010010) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-12663903/15625 : ℚ) - ((0:ℤ):ℚ) = (-25327806/15625 : ℚ) by norm_num]
  exact coverp000000000011010010010
private noncomputable def ep000000000011010010011_0 : Blocks := edgeBlocks% "full/vectors/000000000011010010011-E-0000.bin"
noncomputable def ep000000000011010010011 : Blocks := ep000000000011010010011_0
private theorem idp000000000011010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001101001001.list =
    C ((2:ℤ)^17) * horner X vp000000000011010010011.list + horner X ep000000000011010010011.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011010010011 : Branch 1 (-12663903/15625 : ℚ) vp00000000001101001001 := by
  apply branch_checked idp000000000011010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-12663903/15625 : ℚ) - ((1:ℤ):ℚ) = (-25343431/15625 : ℚ) by norm_num]
  exact coverp000000000011010010011
theorem coverp00000000001101001001 : Covers (-12663903/15625 : ℚ) vp00000000001101001001 := join_branches bp000000000011010010010 bp000000000011010010011
private noncomputable def vp000000000011010010001_0 : Blocks := edgeBlocks% "full/vectors/000000000011010010001-V-0000.bin"
noncomputable def vp000000000011010010001 : Blocks := vp000000000011010010001_0
theorem coverp000000000011010010001 : Covers (-25312181/15625 : ℚ) vp000000000011010010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011010010000_0 : Blocks := edgeBlocks% "full/vectors/000000000011010010000-V-0000.bin"
noncomputable def vp000000000011010010000 : Blocks := vp000000000011010010000_0
theorem coverp000000000011010010000 : Covers (-25296556/15625 : ℚ) vp000000000011010010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001101001000_0 : Blocks := edgeBlocks% "full/vectors/00000000001101001000-V-0000.bin"
noncomputable def vp00000000001101001000 : Blocks := vp00000000001101001000_0
private theorem bp000000000011010010000 : Branch 0 (-12648278/15625 : ℚ) vp00000000001101001000 := by
  apply branch_left_normalized (c:=vp000000000011010010000) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-12648278/15625 : ℚ) - ((0:ℤ):ℚ) = (-25296556/15625 : ℚ) by norm_num]
  exact coverp000000000011010010000
private noncomputable def ep000000000011010010001_0 : Blocks := edgeBlocks% "full/vectors/000000000011010010001-E-0000.bin"
noncomputable def ep000000000011010010001 : Blocks := ep000000000011010010001_0
private theorem idp000000000011010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001101001000.list =
    C ((2:ℤ)^16) * horner X vp000000000011010010001.list + horner X ep000000000011010010001.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011010010001 : Branch 1 (-12648278/15625 : ℚ) vp00000000001101001000 := by
  apply branch_checked idp000000000011010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-12648278/15625 : ℚ) - ((1:ℤ):ℚ) = (-25312181/15625 : ℚ) by norm_num]
  exact coverp000000000011010010001
theorem coverp00000000001101001000 : Covers (-12648278/15625 : ℚ) vp00000000001101001000 := join_branches bp000000000011010010000 bp000000000011010010001
private noncomputable def vp0000000000110100100_0 : Blocks := edgeBlocks% "full/vectors/0000000000110100100-V-0000.bin"
noncomputable def vp0000000000110100100 : Blocks := vp0000000000110100100_0
private theorem bp00000000001101001000 : Branch 0 (-6324139/15625 : ℚ) vp0000000000110100100 := by
  apply branch_left_normalized (c:=vp00000000001101001000) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-6324139/15625 : ℚ) - ((0:ℤ):ℚ) = (-12648278/15625 : ℚ) by norm_num]
  exact coverp00000000001101001000
private noncomputable def ep00000000001101001001_0 : Blocks := edgeBlocks% "full/vectors/00000000001101001001-E-0000.bin"
noncomputable def ep00000000001101001001 : Blocks := ep00000000001101001001_0
private theorem idp00000000001101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110100100.list =
    C ((2:ℤ)^21) * horner X vp00000000001101001001.list + horner X ep00000000001101001001.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001101001001 : Branch 1 (-6324139/15625 : ℚ) vp0000000000110100100 := by
  apply branch_checked idp00000000001101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-6324139/15625 : ℚ) - ((1:ℤ):ℚ) = (-12663903/15625 : ℚ) by norm_num]
  exact coverp00000000001101001001
theorem coverp0000000000110100100 : Covers (-6324139/15625 : ℚ) vp0000000000110100100 := join_branches bp00000000001101001000 bp00000000001101001001
private noncomputable def vp000000000011010010_0 : Blocks := edgeBlocks% "full/vectors/000000000011010010-V-0000.bin"
noncomputable def vp000000000011010010 : Blocks := vp000000000011010010_0
private theorem bp0000000000110100100 : Branch 0 (-6324139/31250 : ℚ) vp000000000011010010 := by
  apply branch_left_normalized (c:=vp0000000000110100100) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-6324139/31250 : ℚ) - ((0:ℤ):ℚ) = (-6324139/15625 : ℚ) by norm_num]
  exact coverp0000000000110100100
private noncomputable def ep0000000000110100101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110100101-E-0000.bin"
noncomputable def ep0000000000110100101 : Blocks := ep0000000000110100101_0
private theorem idp0000000000110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011010010.list =
    C ((2:ℤ)^30) * horner X vp0000000000110100101.list + horner X ep0000000000110100101.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110100101 : Branch 1 (-6324139/31250 : ℚ) vp000000000011010010 := by
  apply branch_checked idp0000000000110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-6324139/31250 : ℚ) - ((1:ℤ):ℚ) = (-6339764/15625 : ℚ) by norm_num]
  exact coverp0000000000110100101
theorem coverp000000000011010010 : Covers (-6324139/31250 : ℚ) vp000000000011010010 := join_branches bp0000000000110100100 bp0000000000110100101
private noncomputable def vp00000000001101001_0 : Blocks := edgeBlocks% "full/vectors/00000000001101001-V-0000.bin"
noncomputable def vp00000000001101001 : Blocks := vp00000000001101001_0
private theorem bp000000000011010010 : Branch 0 (-6324139/62500 : ℚ) vp00000000001101001 := by
  apply branch_left_normalized (c:=vp000000000011010010) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-6324139/62500 : ℚ) - ((0:ℤ):ℚ) = (-6324139/31250 : ℚ) by norm_num]
  exact coverp000000000011010010
private noncomputable def ep000000000011010011_0 : Blocks := edgeBlocks% "full/vectors/000000000011010011-E-0000.bin"
noncomputable def ep000000000011010011 : Blocks := ep000000000011010011_0
private theorem idp000000000011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001101001.list =
    C ((2:ℤ)^44) * horner X vp000000000011010011.list + horner X ep000000000011010011.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011010011 : Branch 1 (-6324139/62500 : ℚ) vp00000000001101001 := by
  apply branch_checked idp000000000011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-6324139/62500 : ℚ) - ((1:ℤ):ℚ) = (-6355389/31250 : ℚ) by norm_num]
  exact coverp000000000011010011
theorem coverp00000000001101001 : Covers (-6324139/62500 : ℚ) vp00000000001101001 := join_branches bp000000000011010010 bp000000000011010011
private noncomputable def vp0000000000110100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110100011-V-0000.bin"
noncomputable def vp0000000000110100011 : Blocks := vp0000000000110100011_0
theorem coverp0000000000110100011 : Covers (-6308514/15625 : ℚ) vp0000000000110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110100010_0 : Blocks := edgeBlocks% "full/vectors/0000000000110100010-V-0000.bin"
noncomputable def vp0000000000110100010 : Blocks := vp0000000000110100010_0
theorem coverp0000000000110100010 : Covers (-6292889/15625 : ℚ) vp0000000000110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011010001_0 : Blocks := edgeBlocks% "full/vectors/000000000011010001-V-0000.bin"
noncomputable def vp000000000011010001 : Blocks := vp000000000011010001_0
private theorem bp0000000000110100010 : Branch 0 (-6292889/31250 : ℚ) vp000000000011010001 := by
  apply branch_left_normalized (c:=vp0000000000110100010) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-6292889/31250 : ℚ) - ((0:ℤ):ℚ) = (-6292889/15625 : ℚ) by norm_num]
  exact coverp0000000000110100010
private noncomputable def ep0000000000110100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110100011-E-0000.bin"
noncomputable def ep0000000000110100011 : Blocks := ep0000000000110100011_0
private theorem idp0000000000110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011010001.list =
    C ((2:ℤ)^29) * horner X vp0000000000110100011.list + horner X ep0000000000110100011.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110100011 : Branch 1 (-6292889/31250 : ℚ) vp000000000011010001 := by
  apply branch_checked idp0000000000110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-6292889/31250 : ℚ) - ((1:ℤ):ℚ) = (-6308514/15625 : ℚ) by norm_num]
  exact coverp0000000000110100011
theorem coverp000000000011010001 : Covers (-6292889/31250 : ℚ) vp000000000011010001 := join_branches bp0000000000110100010 bp0000000000110100011
private noncomputable def vp000000000011010000_0 : Blocks := edgeBlocks% "full/vectors/000000000011010000-V-0000.bin"
noncomputable def vp000000000011010000 : Blocks := vp000000000011010000_0
theorem coverp000000000011010000 : Covers (-6261639/31250 : ℚ) vp000000000011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001101000_0 : Blocks := edgeBlocks% "full/vectors/00000000001101000-V-0000.bin"
noncomputable def vp00000000001101000 : Blocks := vp00000000001101000_0
private theorem bp000000000011010000 : Branch 0 (-6261639/62500 : ℚ) vp00000000001101000 := by
  apply branch_left_normalized (c:=vp000000000011010000) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-6261639/62500 : ℚ) - ((0:ℤ):ℚ) = (-6261639/31250 : ℚ) by norm_num]
  exact coverp000000000011010000
private noncomputable def ep000000000011010001_0 : Blocks := edgeBlocks% "full/vectors/000000000011010001-E-0000.bin"
noncomputable def ep000000000011010001 : Blocks := ep000000000011010001_0
private theorem idp000000000011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001101000.list =
    C ((2:ℤ)^44) * horner X vp000000000011010001.list + horner X ep000000000011010001.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011010001 : Branch 1 (-6261639/62500 : ℚ) vp00000000001101000 := by
  apply branch_checked idp000000000011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-6261639/62500 : ℚ) - ((1:ℤ):ℚ) = (-6292889/31250 : ℚ) by norm_num]
  exact coverp000000000011010001
theorem coverp00000000001101000 : Covers (-6261639/62500 : ℚ) vp00000000001101000 := join_branches bp000000000011010000 bp000000000011010001
private noncomputable def vp0000000000110100_0 : Blocks := edgeBlocks% "full/vectors/0000000000110100-V-0000.bin"
noncomputable def vp0000000000110100 : Blocks := vp0000000000110100_0
private theorem bp00000000001101000 : Branch 0 (-6261639/125000 : ℚ) vp0000000000110100 := by
  apply branch_left_normalized (c:=vp00000000001101000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-6261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-6261639/62500 : ℚ) by norm_num]
  exact coverp00000000001101000
private noncomputable def ep00000000001101001_0 : Blocks := edgeBlocks% "full/vectors/00000000001101001-E-0000.bin"
noncomputable def ep00000000001101001 : Blocks := ep00000000001101001_0
private theorem idp00000000001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110100.list =
    C ((2:ℤ)^71) * horner X vp00000000001101001.list + horner X ep00000000001101001.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001101001 : Branch 1 (-6261639/125000 : ℚ) vp0000000000110100 := by
  apply branch_checked idp00000000001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-6261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-6324139/62500 : ℚ) by norm_num]
  exact coverp00000000001101001
theorem coverp0000000000110100 : Covers (-6261639/125000 : ℚ) vp0000000000110100 := join_branches bp00000000001101000 bp00000000001101001
private noncomputable def vp000000000011010_0 : Blocks := edgeBlocks% "full/vectors/000000000011010-V-0000.bin"
noncomputable def vp000000000011010 : Blocks := vp000000000011010_0
private theorem bp0000000000110100 : Branch 0 (-6261639/250000 : ℚ) vp000000000011010 := by
  apply branch_left_normalized (c:=vp0000000000110100) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-6261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-6261639/125000 : ℚ) by norm_num]
  exact coverp0000000000110100
private noncomputable def ep0000000000110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110101-E-0000.bin"
noncomputable def ep0000000000110101 : Blocks := ep0000000000110101_0
private theorem idp0000000000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011010.list =
    C ((2:ℤ)^120) * horner X vp0000000000110101.list + horner X ep0000000000110101.list := by
  exact edge_identity (B := (2:ℤ)^268) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110101 : Branch 1 (-6261639/250000 : ℚ) vp000000000011010 := by
  apply branch_checked idp0000000000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-6261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-6386639/125000 : ℚ) by norm_num]
  exact coverp0000000000110101
theorem coverp000000000011010 : Covers (-6261639/250000 : ℚ) vp000000000011010 := join_branches bp0000000000110100 bp0000000000110101
private noncomputable def vp00000000001101_0 : Blocks := edgeBlocks% "full/vectors/00000000001101-V-0000.bin"
private noncomputable def vp00000000001101_1 : Blocks := edgeBlocks% "full/vectors/00000000001101-V-0001.bin"
noncomputable def vp00000000001101 : Blocks := (Blocks.join vp00000000001101_0 vp00000000001101_1)
private theorem bp000000000011010 : Branch 0 (-6261639/500000 : ℚ) vp00000000001101 := by
  apply branch_left_normalized (c:=vp000000000011010) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-6261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-6261639/250000 : ℚ) by norm_num]
  exact coverp000000000011010
private noncomputable def ep000000000011011_0 : Blocks := edgeBlocks% "full/vectors/000000000011011-E-0000.bin"
private noncomputable def ep000000000011011_1 : Blocks := edgeBlocks% "full/vectors/000000000011011-E-0001.bin"
noncomputable def ep000000000011011 : Blocks := (Blocks.join ep000000000011011_0 ep000000000011011_1)
private theorem idp000000000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001101.list =
    C ((2:ℤ)^226) * horner X vp000000000011011.list + horner X ep000000000011011.list := by
  exact edge_identity (B := (2:ℤ)^425) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011011 : Branch 1 (-6261639/500000 : ℚ) vp00000000001101 := by
  apply branch_checked idp000000000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-6261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-6511639/250000 : ℚ) by norm_num]
  exact coverp000000000011011
theorem coverp00000000001101 : Covers (-6261639/500000 : ℚ) vp00000000001101 := join_branches bp000000000011010 bp000000000011011
private noncomputable def vp00000000001100111111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100111111-V-0000.bin"
noncomputable def vp00000000001100111111 : Blocks := vp00000000001100111111_0
theorem coverp00000000001100111111 : Covers (-12507653/15625 : ℚ) vp00000000001100111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011001111101_0 : Blocks := edgeBlocks% "full/vectors/000000000011001111101-V-0000.bin"
noncomputable def vp000000000011001111101 : Blocks := vp000000000011001111101_0
theorem coverp000000000011001111101 : Covers (-24999681/15625 : ℚ) vp000000000011001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011001111100_0 : Blocks := edgeBlocks% "full/vectors/000000000011001111100-V-0000.bin"
noncomputable def vp000000000011001111100 : Blocks := vp000000000011001111100_0
theorem coverp000000000011001111100 : Covers (-24984056/15625 : ℚ) vp000000000011001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100111110_0 : Blocks := edgeBlocks% "full/vectors/00000000001100111110-V-0000.bin"
noncomputable def vp00000000001100111110 : Blocks := vp00000000001100111110_0
private theorem bp000000000011001111100 : Branch 0 (-12492028/15625 : ℚ) vp00000000001100111110 := by
  apply branch_left_normalized (c:=vp000000000011001111100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-12492028/15625 : ℚ) - ((0:ℤ):ℚ) = (-24984056/15625 : ℚ) by norm_num]
  exact coverp000000000011001111100
private noncomputable def ep000000000011001111101_0 : Blocks := edgeBlocks% "full/vectors/000000000011001111101-E-0000.bin"
noncomputable def ep000000000011001111101 : Blocks := ep000000000011001111101_0
private theorem idp000000000011001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100111110.list =
    C ((2:ℤ)^17) * horner X vp000000000011001111101.list + horner X ep000000000011001111101.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011001111101 : Branch 1 (-12492028/15625 : ℚ) vp00000000001100111110 := by
  apply branch_checked idp000000000011001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-12492028/15625 : ℚ) - ((1:ℤ):ℚ) = (-24999681/15625 : ℚ) by norm_num]
  exact coverp000000000011001111101
theorem coverp00000000001100111110 : Covers (-12492028/15625 : ℚ) vp00000000001100111110 := join_branches bp000000000011001111100 bp000000000011001111101
private noncomputable def vp0000000000110011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110011111-V-0000.bin"
noncomputable def vp0000000000110011111 : Blocks := vp0000000000110011111_0
private theorem bp00000000001100111110 : Branch 0 (-6246014/15625 : ℚ) vp0000000000110011111 := by
  apply branch_left_normalized (c:=vp00000000001100111110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-6246014/15625 : ℚ) - ((0:ℤ):ℚ) = (-12492028/15625 : ℚ) by norm_num]
  exact coverp00000000001100111110
private noncomputable def ep00000000001100111111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100111111-E-0000.bin"
noncomputable def ep00000000001100111111 : Blocks := ep00000000001100111111_0
private theorem idp00000000001100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110011111.list =
    C ((2:ℤ)^22) * horner X vp00000000001100111111.list + horner X ep00000000001100111111.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100111111 : Branch 1 (-6246014/15625 : ℚ) vp0000000000110011111 := by
  apply branch_checked idp00000000001100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-6246014/15625 : ℚ) - ((1:ℤ):ℚ) = (-12507653/15625 : ℚ) by norm_num]
  exact coverp00000000001100111111
theorem coverp0000000000110011111 : Covers (-6246014/15625 : ℚ) vp0000000000110011111 := join_branches bp00000000001100111110 bp00000000001100111111
private noncomputable def vp0000000000110011110_0 : Blocks := edgeBlocks% "full/vectors/0000000000110011110-V-0000.bin"
noncomputable def vp0000000000110011110 : Blocks := vp0000000000110011110_0
theorem coverp0000000000110011110 : Covers (-6230389/15625 : ℚ) vp0000000000110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011001111_0 : Blocks := edgeBlocks% "full/vectors/000000000011001111-V-0000.bin"
noncomputable def vp000000000011001111 : Blocks := vp000000000011001111_0
private theorem bp0000000000110011110 : Branch 0 (-6230389/31250 : ℚ) vp000000000011001111 := by
  apply branch_left_normalized (c:=vp0000000000110011110) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-6230389/31250 : ℚ) - ((0:ℤ):ℚ) = (-6230389/15625 : ℚ) by norm_num]
  exact coverp0000000000110011110
private noncomputable def ep0000000000110011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110011111-E-0000.bin"
noncomputable def ep0000000000110011111 : Blocks := ep0000000000110011111_0
private theorem idp0000000000110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011001111.list =
    C ((2:ℤ)^30) * horner X vp0000000000110011111.list + horner X ep0000000000110011111.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110011111 : Branch 1 (-6230389/31250 : ℚ) vp000000000011001111 := by
  apply branch_checked idp0000000000110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-6230389/31250 : ℚ) - ((1:ℤ):ℚ) = (-6246014/15625 : ℚ) by norm_num]
  exact coverp0000000000110011111
theorem coverp000000000011001111 : Covers (-6230389/31250 : ℚ) vp000000000011001111 := join_branches bp0000000000110011110 bp0000000000110011111
private noncomputable def vp000000000011001110_0 : Blocks := edgeBlocks% "full/vectors/000000000011001110-V-0000.bin"
noncomputable def vp000000000011001110 : Blocks := vp000000000011001110_0
theorem coverp000000000011001110 : Covers (-6199139/31250 : ℚ) vp000000000011001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100111-V-0000.bin"
noncomputable def vp00000000001100111 : Blocks := vp00000000001100111_0
private theorem bp000000000011001110 : Branch 0 (-6199139/62500 : ℚ) vp00000000001100111 := by
  apply branch_left_normalized (c:=vp000000000011001110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-6199139/62500 : ℚ) - ((0:ℤ):ℚ) = (-6199139/31250 : ℚ) by norm_num]
  exact coverp000000000011001110
private noncomputable def ep000000000011001111_0 : Blocks := edgeBlocks% "full/vectors/000000000011001111-E-0000.bin"
noncomputable def ep000000000011001111 : Blocks := ep000000000011001111_0
private theorem idp000000000011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100111.list =
    C ((2:ℤ)^45) * horner X vp000000000011001111.list + horner X ep000000000011001111.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011001111 : Branch 1 (-6199139/62500 : ℚ) vp00000000001100111 := by
  apply branch_checked idp000000000011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-6199139/62500 : ℚ) - ((1:ℤ):ℚ) = (-6230389/31250 : ℚ) by norm_num]
  exact coverp000000000011001111
theorem coverp00000000001100111 : Covers (-6199139/62500 : ℚ) vp00000000001100111 := join_branches bp000000000011001110 bp000000000011001111
private noncomputable def vp00000000001100110111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100110111-V-0000.bin"
noncomputable def vp00000000001100110111 : Blocks := vp00000000001100110111_0
theorem coverp00000000001100110111 : Covers (-12382653/15625 : ℚ) vp00000000001100110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100110110_0 : Blocks := edgeBlocks% "full/vectors/00000000001100110110-V-0000.bin"
noncomputable def vp00000000001100110110 : Blocks := vp00000000001100110110_0
theorem coverp00000000001100110110 : Covers (-12367028/15625 : ℚ) vp00000000001100110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110011011-V-0000.bin"
noncomputable def vp0000000000110011011 : Blocks := vp0000000000110011011_0
private theorem bp00000000001100110110 : Branch 0 (-6183514/15625 : ℚ) vp0000000000110011011 := by
  apply branch_left_normalized (c:=vp00000000001100110110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-6183514/15625 : ℚ) - ((0:ℤ):ℚ) = (-12367028/15625 : ℚ) by norm_num]
  exact coverp00000000001100110110
private noncomputable def ep00000000001100110111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100110111-E-0000.bin"
noncomputable def ep00000000001100110111 : Blocks := ep00000000001100110111_0
private theorem idp00000000001100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110011011.list =
    C ((2:ℤ)^21) * horner X vp00000000001100110111.list + horner X ep00000000001100110111.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100110111 : Branch 1 (-6183514/15625 : ℚ) vp0000000000110011011 := by
  apply branch_checked idp00000000001100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-6183514/15625 : ℚ) - ((1:ℤ):ℚ) = (-12382653/15625 : ℚ) by norm_num]
  exact coverp00000000001100110111
theorem coverp0000000000110011011 : Covers (-6183514/15625 : ℚ) vp0000000000110011011 := join_branches bp00000000001100110110 bp00000000001100110111
private noncomputable def vp0000000000110011010_0 : Blocks := edgeBlocks% "full/vectors/0000000000110011010-V-0000.bin"
noncomputable def vp0000000000110011010 : Blocks := vp0000000000110011010_0
theorem coverp0000000000110011010 : Covers (-6167889/15625 : ℚ) vp0000000000110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011001101_0 : Blocks := edgeBlocks% "full/vectors/000000000011001101-V-0000.bin"
noncomputable def vp000000000011001101 : Blocks := vp000000000011001101_0
private theorem bp0000000000110011010 : Branch 0 (-6167889/31250 : ℚ) vp000000000011001101 := by
  apply branch_left_normalized (c:=vp0000000000110011010) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-6167889/31250 : ℚ) - ((0:ℤ):ℚ) = (-6167889/15625 : ℚ) by norm_num]
  exact coverp0000000000110011010
private noncomputable def ep0000000000110011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110011011-E-0000.bin"
noncomputable def ep0000000000110011011 : Blocks := ep0000000000110011011_0
private theorem idp0000000000110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011001101.list =
    C ((2:ℤ)^30) * horner X vp0000000000110011011.list + horner X ep0000000000110011011.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110011011 : Branch 1 (-6167889/31250 : ℚ) vp000000000011001101 := by
  apply branch_checked idp0000000000110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-6167889/31250 : ℚ) - ((1:ℤ):ℚ) = (-6183514/15625 : ℚ) by norm_num]
  exact coverp0000000000110011011
theorem coverp000000000011001101 : Covers (-6167889/31250 : ℚ) vp000000000011001101 := join_branches bp0000000000110011010 bp0000000000110011011
private noncomputable def vp0000000000110011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110011001-V-0000.bin"
noncomputable def vp0000000000110011001 : Blocks := vp0000000000110011001_0
theorem coverp0000000000110011001 : Covers (-6152264/15625 : ℚ) vp0000000000110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100110001_0 : Blocks := edgeBlocks% "full/vectors/00000000001100110001-V-0000.bin"
noncomputable def vp00000000001100110001 : Blocks := vp00000000001100110001_0
theorem coverp00000000001100110001 : Covers (-12288903/15625 : ℚ) vp00000000001100110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100110000_0 : Blocks := edgeBlocks% "full/vectors/00000000001100110000-V-0000.bin"
noncomputable def vp00000000001100110000 : Blocks := vp00000000001100110000_0
theorem coverp00000000001100110000 : Covers (-12273278/15625 : ℚ) vp00000000001100110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110011000_0 : Blocks := edgeBlocks% "full/vectors/0000000000110011000-V-0000.bin"
noncomputable def vp0000000000110011000 : Blocks := vp0000000000110011000_0
private theorem bp00000000001100110000 : Branch 0 (-6136639/15625 : ℚ) vp0000000000110011000 := by
  apply branch_left_normalized (c:=vp00000000001100110000) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-6136639/15625 : ℚ) - ((0:ℤ):ℚ) = (-12273278/15625 : ℚ) by norm_num]
  exact coverp00000000001100110000
private noncomputable def ep00000000001100110001_0 : Blocks := edgeBlocks% "full/vectors/00000000001100110001-E-0000.bin"
noncomputable def ep00000000001100110001 : Blocks := ep00000000001100110001_0
private theorem idp00000000001100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110011000.list =
    C ((2:ℤ)^21) * horner X vp00000000001100110001.list + horner X ep00000000001100110001.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100110001 : Branch 1 (-6136639/15625 : ℚ) vp0000000000110011000 := by
  apply branch_checked idp00000000001100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-6136639/15625 : ℚ) - ((1:ℤ):ℚ) = (-12288903/15625 : ℚ) by norm_num]
  exact coverp00000000001100110001
theorem coverp0000000000110011000 : Covers (-6136639/15625 : ℚ) vp0000000000110011000 := join_branches bp00000000001100110000 bp00000000001100110001
private noncomputable def vp000000000011001100_0 : Blocks := edgeBlocks% "full/vectors/000000000011001100-V-0000.bin"
noncomputable def vp000000000011001100 : Blocks := vp000000000011001100_0
private theorem bp0000000000110011000 : Branch 0 (-6136639/31250 : ℚ) vp000000000011001100 := by
  apply branch_left_normalized (c:=vp0000000000110011000) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-6136639/31250 : ℚ) - ((0:ℤ):ℚ) = (-6136639/15625 : ℚ) by norm_num]
  exact coverp0000000000110011000
private noncomputable def ep0000000000110011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110011001-E-0000.bin"
noncomputable def ep0000000000110011001 : Blocks := ep0000000000110011001_0
private theorem idp0000000000110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011001100.list =
    C ((2:ℤ)^30) * horner X vp0000000000110011001.list + horner X ep0000000000110011001.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110011001 : Branch 1 (-6136639/31250 : ℚ) vp000000000011001100 := by
  apply branch_checked idp0000000000110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-6136639/31250 : ℚ) - ((1:ℤ):ℚ) = (-6152264/15625 : ℚ) by norm_num]
  exact coverp0000000000110011001
theorem coverp000000000011001100 : Covers (-6136639/31250 : ℚ) vp000000000011001100 := join_branches bp0000000000110011000 bp0000000000110011001
private noncomputable def vp00000000001100110_0 : Blocks := edgeBlocks% "full/vectors/00000000001100110-V-0000.bin"
noncomputable def vp00000000001100110 : Blocks := vp00000000001100110_0
private theorem bp000000000011001100 : Branch 0 (-6136639/62500 : ℚ) vp00000000001100110 := by
  apply branch_left_normalized (c:=vp000000000011001100) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-6136639/62500 : ℚ) - ((0:ℤ):ℚ) = (-6136639/31250 : ℚ) by norm_num]
  exact coverp000000000011001100
private noncomputable def ep000000000011001101_0 : Blocks := edgeBlocks% "full/vectors/000000000011001101-E-0000.bin"
noncomputable def ep000000000011001101 : Blocks := ep000000000011001101_0
private theorem idp000000000011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100110.list =
    C ((2:ℤ)^45) * horner X vp000000000011001101.list + horner X ep000000000011001101.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011001101 : Branch 1 (-6136639/62500 : ℚ) vp00000000001100110 := by
  apply branch_checked idp000000000011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-6136639/62500 : ℚ) - ((1:ℤ):ℚ) = (-6167889/31250 : ℚ) by norm_num]
  exact coverp000000000011001101
theorem coverp00000000001100110 : Covers (-6136639/62500 : ℚ) vp00000000001100110 := join_branches bp000000000011001100 bp000000000011001101
private noncomputable def vp0000000000110011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110011-V-0000.bin"
noncomputable def vp0000000000110011 : Blocks := vp0000000000110011_0
private theorem bp00000000001100110 : Branch 0 (-6136639/125000 : ℚ) vp0000000000110011 := by
  apply branch_left_normalized (c:=vp00000000001100110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-6136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-6136639/62500 : ℚ) by norm_num]
  exact coverp00000000001100110
private noncomputable def ep00000000001100111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100111-E-0000.bin"
noncomputable def ep00000000001100111 : Blocks := ep00000000001100111_0
private theorem idp00000000001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110011.list =
    C ((2:ℤ)^71) * horner X vp00000000001100111.list + horner X ep00000000001100111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100111 : Branch 1 (-6136639/125000 : ℚ) vp0000000000110011 := by
  apply branch_checked idp00000000001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-6136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-6199139/62500 : ℚ) by norm_num]
  exact coverp00000000001100111
theorem coverp0000000000110011 : Covers (-6136639/125000 : ℚ) vp0000000000110011 := join_branches bp00000000001100110 bp00000000001100111
private noncomputable def vp0000000000110010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010111-V-0000.bin"
noncomputable def vp0000000000110010111 : Blocks := vp0000000000110010111_0
theorem coverp0000000000110010111 : Covers (-6121014/15625 : ℚ) vp0000000000110010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110010110_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010110-V-0000.bin"
noncomputable def vp0000000000110010110 : Blocks := vp0000000000110010110_0
theorem coverp0000000000110010110 : Covers (-6105389/15625 : ℚ) vp0000000000110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011001011_0 : Blocks := edgeBlocks% "full/vectors/000000000011001011-V-0000.bin"
noncomputable def vp000000000011001011 : Blocks := vp000000000011001011_0
private theorem bp0000000000110010110 : Branch 0 (-6105389/31250 : ℚ) vp000000000011001011 := by
  apply branch_left_normalized (c:=vp0000000000110010110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-6105389/31250 : ℚ) - ((0:ℤ):ℚ) = (-6105389/15625 : ℚ) by norm_num]
  exact coverp0000000000110010110
private noncomputable def ep0000000000110010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010111-E-0000.bin"
noncomputable def ep0000000000110010111 : Blocks := ep0000000000110010111_0
private theorem idp0000000000110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011001011.list =
    C ((2:ℤ)^30) * horner X vp0000000000110010111.list + horner X ep0000000000110010111.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110010111 : Branch 1 (-6105389/31250 : ℚ) vp000000000011001011 := by
  apply branch_checked idp0000000000110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-6105389/31250 : ℚ) - ((1:ℤ):ℚ) = (-6121014/15625 : ℚ) by norm_num]
  exact coverp0000000000110010111
theorem coverp000000000011001011 : Covers (-6105389/31250 : ℚ) vp000000000011001011 := join_branches bp0000000000110010110 bp0000000000110010111
private noncomputable def vp00000000001100101011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100101011-V-0000.bin"
noncomputable def vp00000000001100101011 : Blocks := vp00000000001100101011_0
theorem coverp00000000001100101011 : Covers (-12195153/15625 : ℚ) vp00000000001100101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011001010101_0 : Blocks := edgeBlocks% "full/vectors/000000000011001010101-V-0000.bin"
noncomputable def vp000000000011001010101 : Blocks := vp000000000011001010101_0
theorem coverp000000000011001010101 : Covers (-24374681/15625 : ℚ) vp000000000011001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011001010100_0 : Blocks := edgeBlocks% "full/vectors/000000000011001010100-V-0000.bin"
noncomputable def vp000000000011001010100 : Blocks := vp000000000011001010100_0
theorem coverp000000000011001010100 : Covers (-24359056/15625 : ℚ) vp000000000011001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100101010_0 : Blocks := edgeBlocks% "full/vectors/00000000001100101010-V-0000.bin"
noncomputable def vp00000000001100101010 : Blocks := vp00000000001100101010_0
private theorem bp000000000011001010100 : Branch 0 (-12179528/15625 : ℚ) vp00000000001100101010 := by
  apply branch_left_normalized (c:=vp000000000011001010100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-12179528/15625 : ℚ) - ((0:ℤ):ℚ) = (-24359056/15625 : ℚ) by norm_num]
  exact coverp000000000011001010100
private noncomputable def ep000000000011001010101_0 : Blocks := edgeBlocks% "full/vectors/000000000011001010101-E-0000.bin"
noncomputable def ep000000000011001010101 : Blocks := ep000000000011001010101_0
private theorem idp000000000011001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100101010.list =
    C ((2:ℤ)^17) * horner X vp000000000011001010101.list + horner X ep000000000011001010101.list := by
  exact edge_identity (B := (2:ℤ)^121) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011001010101 : Branch 1 (-12179528/15625 : ℚ) vp00000000001100101010 := by
  apply branch_checked idp000000000011001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-12179528/15625 : ℚ) - ((1:ℤ):ℚ) = (-24374681/15625 : ℚ) by norm_num]
  exact coverp000000000011001010101
theorem coverp00000000001100101010 : Covers (-12179528/15625 : ℚ) vp00000000001100101010 := join_branches bp000000000011001010100 bp000000000011001010101
private noncomputable def vp0000000000110010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010101-V-0000.bin"
noncomputable def vp0000000000110010101 : Blocks := vp0000000000110010101_0
private theorem bp00000000001100101010 : Branch 0 (-6089764/15625 : ℚ) vp0000000000110010101 := by
  apply branch_left_normalized (c:=vp00000000001100101010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-6089764/15625 : ℚ) - ((0:ℤ):ℚ) = (-12179528/15625 : ℚ) by norm_num]
  exact coverp00000000001100101010
private noncomputable def ep00000000001100101011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100101011-E-0000.bin"
noncomputable def ep00000000001100101011 : Blocks := ep00000000001100101011_0
private theorem idp00000000001100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110010101.list =
    C ((2:ℤ)^21) * horner X vp00000000001100101011.list + horner X ep00000000001100101011.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100101011 : Branch 1 (-6089764/15625 : ℚ) vp0000000000110010101 := by
  apply branch_checked idp00000000001100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-6089764/15625 : ℚ) - ((1:ℤ):ℚ) = (-12195153/15625 : ℚ) by norm_num]
  exact coverp00000000001100101011
theorem coverp0000000000110010101 : Covers (-6089764/15625 : ℚ) vp0000000000110010101 := join_branches bp00000000001100101010 bp00000000001100101011
private noncomputable def vp0000000000110010100_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010100-V-0000.bin"
noncomputable def vp0000000000110010100 : Blocks := vp0000000000110010100_0
theorem coverp0000000000110010100 : Covers (-6074139/15625 : ℚ) vp0000000000110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011001010_0 : Blocks := edgeBlocks% "full/vectors/000000000011001010-V-0000.bin"
noncomputable def vp000000000011001010 : Blocks := vp000000000011001010_0
private theorem bp0000000000110010100 : Branch 0 (-6074139/31250 : ℚ) vp000000000011001010 := by
  apply branch_left_normalized (c:=vp0000000000110010100) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-6074139/31250 : ℚ) - ((0:ℤ):ℚ) = (-6074139/15625 : ℚ) by norm_num]
  exact coverp0000000000110010100
private noncomputable def ep0000000000110010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010101-E-0000.bin"
noncomputable def ep0000000000110010101 : Blocks := ep0000000000110010101_0
private theorem idp0000000000110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011001010.list =
    C ((2:ℤ)^30) * horner X vp0000000000110010101.list + horner X ep0000000000110010101.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110010101 : Branch 1 (-6074139/31250 : ℚ) vp000000000011001010 := by
  apply branch_checked idp0000000000110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-6074139/31250 : ℚ) - ((1:ℤ):ℚ) = (-6089764/15625 : ℚ) by norm_num]
  exact coverp0000000000110010101
theorem coverp000000000011001010 : Covers (-6074139/31250 : ℚ) vp000000000011001010 := join_branches bp0000000000110010100 bp0000000000110010101
private noncomputable def vp00000000001100101_0 : Blocks := edgeBlocks% "full/vectors/00000000001100101-V-0000.bin"
noncomputable def vp00000000001100101 : Blocks := vp00000000001100101_0
private theorem bp000000000011001010 : Branch 0 (-6074139/62500 : ℚ) vp00000000001100101 := by
  apply branch_left_normalized (c:=vp000000000011001010) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-6074139/62500 : ℚ) - ((0:ℤ):ℚ) = (-6074139/31250 : ℚ) by norm_num]
  exact coverp000000000011001010
private noncomputable def ep000000000011001011_0 : Blocks := edgeBlocks% "full/vectors/000000000011001011-E-0000.bin"
noncomputable def ep000000000011001011 : Blocks := ep000000000011001011_0
private theorem idp000000000011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100101.list =
    C ((2:ℤ)^44) * horner X vp000000000011001011.list + horner X ep000000000011001011.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011001011 : Branch 1 (-6074139/62500 : ℚ) vp00000000001100101 := by
  apply branch_checked idp000000000011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-6074139/62500 : ℚ) - ((1:ℤ):ℚ) = (-6105389/31250 : ℚ) by norm_num]
  exact coverp000000000011001011
theorem coverp00000000001100101 : Covers (-6074139/62500 : ℚ) vp00000000001100101 := join_branches bp000000000011001010 bp000000000011001011
private noncomputable def vp0000000000110010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010011-V-0000.bin"
noncomputable def vp0000000000110010011 : Blocks := vp0000000000110010011_0
theorem coverp0000000000110010011 : Covers (-6058514/15625 : ℚ) vp0000000000110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110010010_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010010-V-0000.bin"
noncomputable def vp0000000000110010010 : Blocks := vp0000000000110010010_0
theorem coverp0000000000110010010 : Covers (-6042889/15625 : ℚ) vp0000000000110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011001001_0 : Blocks := edgeBlocks% "full/vectors/000000000011001001-V-0000.bin"
noncomputable def vp000000000011001001 : Blocks := vp000000000011001001_0
private theorem bp0000000000110010010 : Branch 0 (-6042889/31250 : ℚ) vp000000000011001001 := by
  apply branch_left_normalized (c:=vp0000000000110010010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-6042889/31250 : ℚ) - ((0:ℤ):ℚ) = (-6042889/15625 : ℚ) by norm_num]
  exact coverp0000000000110010010
private noncomputable def ep0000000000110010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010011-E-0000.bin"
noncomputable def ep0000000000110010011 : Blocks := ep0000000000110010011_0
private theorem idp0000000000110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011001001.list =
    C ((2:ℤ)^31) * horner X vp0000000000110010011.list + horner X ep0000000000110010011.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110010011 : Branch 1 (-6042889/31250 : ℚ) vp000000000011001001 := by
  apply branch_checked idp0000000000110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-6042889/31250 : ℚ) - ((1:ℤ):ℚ) = (-6058514/15625 : ℚ) by norm_num]
  exact coverp0000000000110010011
theorem coverp000000000011001001 : Covers (-6042889/31250 : ℚ) vp000000000011001001 := join_branches bp0000000000110010010 bp0000000000110010011
private noncomputable def vp000000000011001000111_0 : Blocks := edgeBlocks% "full/vectors/000000000011001000111-V-0000.bin"
noncomputable def vp000000000011001000111 : Blocks := vp000000000011001000111_0
theorem coverp000000000011001000111 : Covers (-24155931/15625 : ℚ) vp000000000011001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011001000110_0 : Blocks := edgeBlocks% "full/vectors/000000000011001000110-V-0000.bin"
noncomputable def vp000000000011001000110 : Blocks := vp000000000011001000110_0
theorem coverp000000000011001000110 : Covers (-24140306/15625 : ℚ) vp000000000011001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100100011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100100011-V-0000.bin"
noncomputable def vp00000000001100100011 : Blocks := vp00000000001100100011_0
private theorem bp000000000011001000110 : Branch 0 (-12070153/15625 : ℚ) vp00000000001100100011 := by
  apply branch_left_normalized (c:=vp000000000011001000110) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-12070153/15625 : ℚ) - ((0:ℤ):ℚ) = (-24140306/15625 : ℚ) by norm_num]
  exact coverp000000000011001000110
private noncomputable def ep000000000011001000111_0 : Blocks := edgeBlocks% "full/vectors/000000000011001000111-E-0000.bin"
noncomputable def ep000000000011001000111 : Blocks := ep000000000011001000111_0
private theorem idp000000000011001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100100011.list =
    C ((2:ℤ)^17) * horner X vp000000000011001000111.list + horner X ep000000000011001000111.list := by
  exact edge_identity (B := (2:ℤ)^121) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011001000111 : Branch 1 (-12070153/15625 : ℚ) vp00000000001100100011 := by
  apply branch_checked idp000000000011001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-12070153/15625 : ℚ) - ((1:ℤ):ℚ) = (-24155931/15625 : ℚ) by norm_num]
  exact coverp000000000011001000111
theorem coverp00000000001100100011 : Covers (-12070153/15625 : ℚ) vp00000000001100100011 := join_branches bp000000000011001000110 bp000000000011001000111
private noncomputable def vp00000000001100100010_0 : Blocks := edgeBlocks% "full/vectors/00000000001100100010-V-0000.bin"
noncomputable def vp00000000001100100010 : Blocks := vp00000000001100100010_0
theorem coverp00000000001100100010 : Covers (-12054528/15625 : ℚ) vp00000000001100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010001-V-0000.bin"
noncomputable def vp0000000000110010001 : Blocks := vp0000000000110010001_0
private theorem bp00000000001100100010 : Branch 0 (-6027264/15625 : ℚ) vp0000000000110010001 := by
  apply branch_left_normalized (c:=vp00000000001100100010) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-6027264/15625 : ℚ) - ((0:ℤ):ℚ) = (-12054528/15625 : ℚ) by norm_num]
  exact coverp00000000001100100010
private noncomputable def ep00000000001100100011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100100011-E-0000.bin"
noncomputable def ep00000000001100100011 : Blocks := ep00000000001100100011_0
private theorem idp00000000001100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110010001.list =
    C ((2:ℤ)^22) * horner X vp00000000001100100011.list + horner X ep00000000001100100011.list := by
  exact edge_identity (B := (2:ℤ)^127) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100100011 : Branch 1 (-6027264/15625 : ℚ) vp0000000000110010001 := by
  apply branch_checked idp00000000001100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-6027264/15625 : ℚ) - ((1:ℤ):ℚ) = (-12070153/15625 : ℚ) by norm_num]
  exact coverp00000000001100100011
theorem coverp0000000000110010001 : Covers (-6027264/15625 : ℚ) vp0000000000110010001 := join_branches bp00000000001100100010 bp00000000001100100011
private noncomputable def vp0000000000110010000_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010000-V-0000.bin"
noncomputable def vp0000000000110010000 : Blocks := vp0000000000110010000_0
theorem coverp0000000000110010000 : Covers (-6011639/15625 : ℚ) vp0000000000110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011001000_0 : Blocks := edgeBlocks% "full/vectors/000000000011001000-V-0000.bin"
noncomputable def vp000000000011001000 : Blocks := vp000000000011001000_0
private theorem bp0000000000110010000 : Branch 0 (-6011639/31250 : ℚ) vp000000000011001000 := by
  apply branch_left_normalized (c:=vp0000000000110010000) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-6011639/31250 : ℚ) - ((0:ℤ):ℚ) = (-6011639/15625 : ℚ) by norm_num]
  exact coverp0000000000110010000
private noncomputable def ep0000000000110010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010001-E-0000.bin"
noncomputable def ep0000000000110010001 : Blocks := ep0000000000110010001_0
private theorem idp0000000000110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011001000.list =
    C ((2:ℤ)^30) * horner X vp0000000000110010001.list + horner X ep0000000000110010001.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110010001 : Branch 1 (-6011639/31250 : ℚ) vp000000000011001000 := by
  apply branch_checked idp0000000000110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-6011639/31250 : ℚ) - ((1:ℤ):ℚ) = (-6027264/15625 : ℚ) by norm_num]
  exact coverp0000000000110010001
theorem coverp000000000011001000 : Covers (-6011639/31250 : ℚ) vp000000000011001000 := join_branches bp0000000000110010000 bp0000000000110010001
private noncomputable def vp00000000001100100_0 : Blocks := edgeBlocks% "full/vectors/00000000001100100-V-0000.bin"
noncomputable def vp00000000001100100 : Blocks := vp00000000001100100_0
private theorem bp000000000011001000 : Branch 0 (-6011639/62500 : ℚ) vp00000000001100100 := by
  apply branch_left_normalized (c:=vp000000000011001000) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-6011639/62500 : ℚ) - ((0:ℤ):ℚ) = (-6011639/31250 : ℚ) by norm_num]
  exact coverp000000000011001000
private noncomputable def ep000000000011001001_0 : Blocks := edgeBlocks% "full/vectors/000000000011001001-E-0000.bin"
noncomputable def ep000000000011001001 : Blocks := ep000000000011001001_0
private theorem idp000000000011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100100.list =
    C ((2:ℤ)^44) * horner X vp000000000011001001.list + horner X ep000000000011001001.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011001001 : Branch 1 (-6011639/62500 : ℚ) vp00000000001100100 := by
  apply branch_checked idp000000000011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-6011639/62500 : ℚ) - ((1:ℤ):ℚ) = (-6042889/31250 : ℚ) by norm_num]
  exact coverp000000000011001001
theorem coverp00000000001100100 : Covers (-6011639/62500 : ℚ) vp00000000001100100 := join_branches bp000000000011001000 bp000000000011001001
private noncomputable def vp0000000000110010_0 : Blocks := edgeBlocks% "full/vectors/0000000000110010-V-0000.bin"
noncomputable def vp0000000000110010 : Blocks := vp0000000000110010_0
private theorem bp00000000001100100 : Branch 0 (-6011639/125000 : ℚ) vp0000000000110010 := by
  apply branch_left_normalized (c:=vp00000000001100100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-6011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-6011639/62500 : ℚ) by norm_num]
  exact coverp00000000001100100
private noncomputable def ep00000000001100101_0 : Blocks := edgeBlocks% "full/vectors/00000000001100101-E-0000.bin"
noncomputable def ep00000000001100101 : Blocks := ep00000000001100101_0
private theorem idp00000000001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110010.list =
    C ((2:ℤ)^71) * horner X vp00000000001100101.list + horner X ep00000000001100101.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100101 : Branch 1 (-6011639/125000 : ℚ) vp0000000000110010 := by
  apply branch_checked idp00000000001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-6011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-6074139/62500 : ℚ) by norm_num]
  exact coverp00000000001100101
theorem coverp0000000000110010 : Covers (-6011639/125000 : ℚ) vp0000000000110010 := join_branches bp00000000001100100 bp00000000001100101
private noncomputable def vp000000000011001_0 : Blocks := edgeBlocks% "full/vectors/000000000011001-V-0000.bin"
noncomputable def vp000000000011001 : Blocks := vp000000000011001_0
private theorem bp0000000000110010 : Branch 0 (-6011639/250000 : ℚ) vp000000000011001 := by
  apply branch_left_normalized (c:=vp0000000000110010) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-6011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-6011639/125000 : ℚ) by norm_num]
  exact coverp0000000000110010
private noncomputable def ep0000000000110011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110011-E-0000.bin"
noncomputable def ep0000000000110011 : Blocks := ep0000000000110011_0
private theorem idp0000000000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011001.list =
    C ((2:ℤ)^125) * horner X vp0000000000110011.list + horner X ep0000000000110011.list := by
  exact edge_identity (B := (2:ℤ)^272) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110011 : Branch 1 (-6011639/250000 : ℚ) vp000000000011001 := by
  apply branch_checked idp0000000000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-6011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-6136639/125000 : ℚ) by norm_num]
  exact coverp0000000000110011
theorem coverp000000000011001 : Covers (-6011639/250000 : ℚ) vp000000000011001 := join_branches bp0000000000110010 bp0000000000110011
private noncomputable def vp00000000001100011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100011111-V-0000.bin"
noncomputable def vp00000000001100011111 : Blocks := vp00000000001100011111_0
theorem coverp00000000001100011111 : Covers (-12007653/15625 : ℚ) vp00000000001100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110001111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001111011-V-0000.bin"
noncomputable def vp0000000000110001111011 : Blocks := vp0000000000110001111011_0
theorem coverp0000000000110001111011 : Covers (-48014987/15625 : ℚ) vp0000000000110001111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110001111010_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001111010-V-0000.bin"
noncomputable def vp0000000000110001111010 : Blocks := vp0000000000110001111010_0
theorem coverp0000000000110001111010 : Covers (-47999362/15625 : ℚ) vp0000000000110001111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000111101_0 : Blocks := edgeBlocks% "full/vectors/000000000011000111101-V-0000.bin"
noncomputable def vp000000000011000111101 : Blocks := vp000000000011000111101_0
private theorem bp0000000000110001111010 : Branch 0 (-23999681/15625 : ℚ) vp000000000011000111101 := by
  apply branch_left_normalized (c:=vp0000000000110001111010) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-23999681/15625 : ℚ) - ((0:ℤ):ℚ) = (-47999362/15625 : ℚ) by norm_num]
  exact coverp0000000000110001111010
private noncomputable def ep0000000000110001111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001111011-E-0000.bin"
noncomputable def ep0000000000110001111011 : Blocks := ep0000000000110001111011_0
private theorem idp0000000000110001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000111101.list =
    C ((2:ℤ)^14) * horner X vp0000000000110001111011.list + horner X ep0000000000110001111011.list := by
  exact edge_identity (B := (2:ℤ)^117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110001111011 : Branch 1 (-23999681/15625 : ℚ) vp000000000011000111101 := by
  apply branch_checked idp0000000000110001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-23999681/15625 : ℚ) - ((1:ℤ):ℚ) = (-48014987/15625 : ℚ) by norm_num]
  exact coverp0000000000110001111011
theorem coverp000000000011000111101 : Covers (-23999681/15625 : ℚ) vp000000000011000111101 := join_branches bp0000000000110001111010 bp0000000000110001111011
private noncomputable def vp000000000011000111100_0 : Blocks := edgeBlocks% "full/vectors/000000000011000111100-V-0000.bin"
noncomputable def vp000000000011000111100 : Blocks := vp000000000011000111100_0
theorem coverp000000000011000111100 : Covers (-23984056/15625 : ℚ) vp000000000011000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100011110_0 : Blocks := edgeBlocks% "full/vectors/00000000001100011110-V-0000.bin"
noncomputable def vp00000000001100011110 : Blocks := vp00000000001100011110_0
private theorem bp000000000011000111100 : Branch 0 (-11992028/15625 : ℚ) vp00000000001100011110 := by
  apply branch_left_normalized (c:=vp000000000011000111100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-11992028/15625 : ℚ) - ((0:ℤ):ℚ) = (-23984056/15625 : ℚ) by norm_num]
  exact coverp000000000011000111100
private noncomputable def ep000000000011000111101_0 : Blocks := edgeBlocks% "full/vectors/000000000011000111101-E-0000.bin"
noncomputable def ep000000000011000111101 : Blocks := ep000000000011000111101_0
private theorem idp000000000011000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100011110.list =
    C ((2:ℤ)^17) * horner X vp000000000011000111101.list + horner X ep000000000011000111101.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000111101 : Branch 1 (-11992028/15625 : ℚ) vp00000000001100011110 := by
  apply branch_checked idp000000000011000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-11992028/15625 : ℚ) - ((1:ℤ):ℚ) = (-23999681/15625 : ℚ) by norm_num]
  exact coverp000000000011000111101
theorem coverp00000000001100011110 : Covers (-11992028/15625 : ℚ) vp00000000001100011110 := join_branches bp000000000011000111100 bp000000000011000111101
private noncomputable def vp0000000000110001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001111-V-0000.bin"
noncomputable def vp0000000000110001111 : Blocks := vp0000000000110001111_0
private theorem bp00000000001100011110 : Branch 0 (-5996014/15625 : ℚ) vp0000000000110001111 := by
  apply branch_left_normalized (c:=vp00000000001100011110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5996014/15625 : ℚ) - ((0:ℤ):ℚ) = (-11992028/15625 : ℚ) by norm_num]
  exact coverp00000000001100011110
private noncomputable def ep00000000001100011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100011111-E-0000.bin"
noncomputable def ep00000000001100011111 : Blocks := ep00000000001100011111_0
private theorem idp00000000001100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110001111.list =
    C ((2:ℤ)^21) * horner X vp00000000001100011111.list + horner X ep00000000001100011111.list := by
  exact edge_identity (B := (2:ℤ)^127) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100011111 : Branch 1 (-5996014/15625 : ℚ) vp0000000000110001111 := by
  apply branch_checked idp00000000001100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-5996014/15625 : ℚ) - ((1:ℤ):ℚ) = (-12007653/15625 : ℚ) by norm_num]
  exact coverp00000000001100011111
theorem coverp0000000000110001111 : Covers (-5996014/15625 : ℚ) vp0000000000110001111 := join_branches bp00000000001100011110 bp00000000001100011111
private noncomputable def vp000000000011000111011_0 : Blocks := edgeBlocks% "full/vectors/000000000011000111011-V-0000.bin"
noncomputable def vp000000000011000111011 : Blocks := vp000000000011000111011_0
theorem coverp000000000011000111011 : Covers (-23968431/15625 : ℚ) vp000000000011000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000111010_0 : Blocks := edgeBlocks% "full/vectors/000000000011000111010-V-0000.bin"
noncomputable def vp000000000011000111010 : Blocks := vp000000000011000111010_0
theorem coverp000000000011000111010 : Covers (-23952806/15625 : ℚ) vp000000000011000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100011101_0 : Blocks := edgeBlocks% "full/vectors/00000000001100011101-V-0000.bin"
noncomputable def vp00000000001100011101 : Blocks := vp00000000001100011101_0
private theorem bp000000000011000111010 : Branch 0 (-11976403/15625 : ℚ) vp00000000001100011101 := by
  apply branch_left_normalized (c:=vp000000000011000111010) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-11976403/15625 : ℚ) - ((0:ℤ):ℚ) = (-23952806/15625 : ℚ) by norm_num]
  exact coverp000000000011000111010
private noncomputable def ep000000000011000111011_0 : Blocks := edgeBlocks% "full/vectors/000000000011000111011-E-0000.bin"
noncomputable def ep000000000011000111011 : Blocks := ep000000000011000111011_0
private theorem idp000000000011000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100011101.list =
    C ((2:ℤ)^16) * horner X vp000000000011000111011.list + horner X ep000000000011000111011.list := by
  exact edge_identity (B := (2:ℤ)^123) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000111011 : Branch 1 (-11976403/15625 : ℚ) vp00000000001100011101 := by
  apply branch_checked idp000000000011000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-11976403/15625 : ℚ) - ((1:ℤ):ℚ) = (-23968431/15625 : ℚ) by norm_num]
  exact coverp000000000011000111011
theorem coverp00000000001100011101 : Covers (-11976403/15625 : ℚ) vp00000000001100011101 := join_branches bp000000000011000111010 bp000000000011000111011
private noncomputable def vp00000000001100011100_0 : Blocks := edgeBlocks% "full/vectors/00000000001100011100-V-0000.bin"
noncomputable def vp00000000001100011100 : Blocks := vp00000000001100011100_0
theorem coverp00000000001100011100 : Covers (-11960778/15625 : ℚ) vp00000000001100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110001110_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001110-V-0000.bin"
noncomputable def vp0000000000110001110 : Blocks := vp0000000000110001110_0
private theorem bp00000000001100011100 : Branch 0 (-5980389/15625 : ℚ) vp0000000000110001110 := by
  apply branch_left_normalized (c:=vp00000000001100011100) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-5980389/15625 : ℚ) - ((0:ℤ):ℚ) = (-11960778/15625 : ℚ) by norm_num]
  exact coverp00000000001100011100
private noncomputable def ep00000000001100011101_0 : Blocks := edgeBlocks% "full/vectors/00000000001100011101-E-0000.bin"
noncomputable def ep00000000001100011101 : Blocks := ep00000000001100011101_0
private theorem idp00000000001100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110001110.list =
    C ((2:ℤ)^20) * horner X vp00000000001100011101.list + horner X ep00000000001100011101.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100011101 : Branch 1 (-5980389/15625 : ℚ) vp0000000000110001110 := by
  apply branch_checked idp00000000001100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-5980389/15625 : ℚ) - ((1:ℤ):ℚ) = (-11976403/15625 : ℚ) by norm_num]
  exact coverp00000000001100011101
theorem coverp0000000000110001110 : Covers (-5980389/15625 : ℚ) vp0000000000110001110 := join_branches bp00000000001100011100 bp00000000001100011101
private noncomputable def vp000000000011000111_0 : Blocks := edgeBlocks% "full/vectors/000000000011000111-V-0000.bin"
noncomputable def vp000000000011000111 : Blocks := vp000000000011000111_0
private theorem bp0000000000110001110 : Branch 0 (-5980389/31250 : ℚ) vp000000000011000111 := by
  apply branch_left_normalized (c:=vp0000000000110001110) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-5980389/31250 : ℚ) - ((0:ℤ):ℚ) = (-5980389/15625 : ℚ) by norm_num]
  exact coverp0000000000110001110
private noncomputable def ep0000000000110001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001111-E-0000.bin"
noncomputable def ep0000000000110001111 : Blocks := ep0000000000110001111_0
private theorem idp0000000000110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000111.list =
    C ((2:ℤ)^29) * horner X vp0000000000110001111.list + horner X ep0000000000110001111.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110001111 : Branch 1 (-5980389/31250 : ℚ) vp000000000011000111 := by
  apply branch_checked idp0000000000110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-5980389/31250 : ℚ) - ((1:ℤ):ℚ) = (-5996014/15625 : ℚ) by norm_num]
  exact coverp0000000000110001111
theorem coverp000000000011000111 : Covers (-5980389/31250 : ℚ) vp000000000011000111 := join_branches bp0000000000110001110 bp0000000000110001111
private noncomputable def vp0000000000110001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001101-V-0000.bin"
noncomputable def vp0000000000110001101 : Blocks := vp0000000000110001101_0
theorem coverp0000000000110001101 : Covers (-5964764/15625 : ℚ) vp0000000000110001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110001100_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001100-V-0000.bin"
noncomputable def vp0000000000110001100 : Blocks := vp0000000000110001100_0
theorem coverp0000000000110001100 : Covers (-5949139/15625 : ℚ) vp0000000000110001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000110_0 : Blocks := edgeBlocks% "full/vectors/000000000011000110-V-0000.bin"
noncomputable def vp000000000011000110 : Blocks := vp000000000011000110_0
private theorem bp0000000000110001100 : Branch 0 (-5949139/31250 : ℚ) vp000000000011000110 := by
  apply branch_left_normalized (c:=vp0000000000110001100) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-5949139/31250 : ℚ) - ((0:ℤ):ℚ) = (-5949139/15625 : ℚ) by norm_num]
  exact coverp0000000000110001100
private noncomputable def ep0000000000110001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001101-E-0000.bin"
noncomputable def ep0000000000110001101 : Blocks := ep0000000000110001101_0
private theorem idp0000000000110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000110.list =
    C ((2:ℤ)^28) * horner X vp0000000000110001101.list + horner X ep0000000000110001101.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110001101 : Branch 1 (-5949139/31250 : ℚ) vp000000000011000110 := by
  apply branch_checked idp0000000000110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-5949139/31250 : ℚ) - ((1:ℤ):ℚ) = (-5964764/15625 : ℚ) by norm_num]
  exact coverp0000000000110001101
theorem coverp000000000011000110 : Covers (-5949139/31250 : ℚ) vp000000000011000110 := join_branches bp0000000000110001100 bp0000000000110001101
private noncomputable def vp00000000001100011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100011-V-0000.bin"
noncomputable def vp00000000001100011 : Blocks := vp00000000001100011_0
private theorem bp000000000011000110 : Branch 0 (-5949139/62500 : ℚ) vp00000000001100011 := by
  apply branch_left_normalized (c:=vp000000000011000110) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-5949139/62500 : ℚ) - ((0:ℤ):ℚ) = (-5949139/31250 : ℚ) by norm_num]
  exact coverp000000000011000110
private noncomputable def ep000000000011000111_0 : Blocks := edgeBlocks% "full/vectors/000000000011000111-E-0000.bin"
noncomputable def ep000000000011000111 : Blocks := ep000000000011000111_0
private theorem idp000000000011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100011.list =
    C ((2:ℤ)^42) * horner X vp000000000011000111.list + horner X ep000000000011000111.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000111 : Branch 1 (-5949139/62500 : ℚ) vp00000000001100011 := by
  apply branch_checked idp000000000011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-5949139/62500 : ℚ) - ((1:ℤ):ℚ) = (-5980389/31250 : ℚ) by norm_num]
  exact coverp000000000011000111
theorem coverp00000000001100011 : Covers (-5949139/62500 : ℚ) vp00000000001100011 := join_branches bp000000000011000110 bp000000000011000111
private noncomputable def vp0000000000110001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001011-V-0000.bin"
noncomputable def vp0000000000110001011 : Blocks := vp0000000000110001011_0
theorem coverp0000000000110001011 : Covers (-5933514/15625 : ℚ) vp0000000000110001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100010101_0 : Blocks := edgeBlocks% "full/vectors/00000000001100010101-V-0000.bin"
noncomputable def vp00000000001100010101 : Blocks := vp00000000001100010101_0
theorem coverp00000000001100010101 : Covers (-11851403/15625 : ℚ) vp00000000001100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000101001_0 : Blocks := edgeBlocks% "full/vectors/000000000011000101001-V-0000.bin"
noncomputable def vp000000000011000101001 : Blocks := vp000000000011000101001_0
theorem coverp000000000011000101001 : Covers (-23687181/15625 : ℚ) vp000000000011000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110001010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001010001-V-0000.bin"
noncomputable def vp0000000000110001010001 : Blocks := vp0000000000110001010001_0
theorem coverp0000000000110001010001 : Covers (-47358737/15625 : ℚ) vp0000000000110001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110001010000_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001010000-V-0000.bin"
noncomputable def vp0000000000110001010000 : Blocks := vp0000000000110001010000_0
theorem coverp0000000000110001010000 : Covers (-47343112/15625 : ℚ) vp0000000000110001010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000101000_0 : Blocks := edgeBlocks% "full/vectors/000000000011000101000-V-0000.bin"
noncomputable def vp000000000011000101000 : Blocks := vp000000000011000101000_0
private theorem bp0000000000110001010000 : Branch 0 (-23671556/15625 : ℚ) vp000000000011000101000 := by
  apply branch_left_normalized (c:=vp0000000000110001010000) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-23671556/15625 : ℚ) - ((0:ℤ):ℚ) = (-47343112/15625 : ℚ) by norm_num]
  exact coverp0000000000110001010000
private noncomputable def ep0000000000110001010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001010001-E-0000.bin"
noncomputable def ep0000000000110001010001 : Blocks := ep0000000000110001010001_0
private theorem idp0000000000110001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000101000.list =
    C ((2:ℤ)^14) * horner X vp0000000000110001010001.list + horner X ep0000000000110001010001.list := by
  exact edge_identity (B := (2:ℤ)^118) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110001010001 : Branch 1 (-23671556/15625 : ℚ) vp000000000011000101000 := by
  apply branch_checked idp0000000000110001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-23671556/15625 : ℚ) - ((1:ℤ):ℚ) = (-47358737/15625 : ℚ) by norm_num]
  exact coverp0000000000110001010001
theorem coverp000000000011000101000 : Covers (-23671556/15625 : ℚ) vp000000000011000101000 := join_branches bp0000000000110001010000 bp0000000000110001010001
private noncomputable def vp00000000001100010100_0 : Blocks := edgeBlocks% "full/vectors/00000000001100010100-V-0000.bin"
noncomputable def vp00000000001100010100 : Blocks := vp00000000001100010100_0
private theorem bp000000000011000101000 : Branch 0 (-11835778/15625 : ℚ) vp00000000001100010100 := by
  apply branch_left_normalized (c:=vp000000000011000101000) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-11835778/15625 : ℚ) - ((0:ℤ):ℚ) = (-23671556/15625 : ℚ) by norm_num]
  exact coverp000000000011000101000
private noncomputable def ep000000000011000101001_0 : Blocks := edgeBlocks% "full/vectors/000000000011000101001-E-0000.bin"
noncomputable def ep000000000011000101001 : Blocks := ep000000000011000101001_0
private theorem idp000000000011000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100010100.list =
    C ((2:ℤ)^17) * horner X vp000000000011000101001.list + horner X ep000000000011000101001.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000101001 : Branch 1 (-11835778/15625 : ℚ) vp00000000001100010100 := by
  apply branch_checked idp000000000011000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-11835778/15625 : ℚ) - ((1:ℤ):ℚ) = (-23687181/15625 : ℚ) by norm_num]
  exact coverp000000000011000101001
theorem coverp00000000001100010100 : Covers (-11835778/15625 : ℚ) vp00000000001100010100 := join_branches bp000000000011000101000 bp000000000011000101001
private noncomputable def vp0000000000110001010_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001010-V-0000.bin"
noncomputable def vp0000000000110001010 : Blocks := vp0000000000110001010_0
private theorem bp00000000001100010100 : Branch 0 (-5917889/15625 : ℚ) vp0000000000110001010 := by
  apply branch_left_normalized (c:=vp00000000001100010100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5917889/15625 : ℚ) - ((0:ℤ):ℚ) = (-11835778/15625 : ℚ) by norm_num]
  exact coverp00000000001100010100
private noncomputable def ep00000000001100010101_0 : Blocks := edgeBlocks% "full/vectors/00000000001100010101-E-0000.bin"
noncomputable def ep00000000001100010101 : Blocks := ep00000000001100010101_0
private theorem idp00000000001100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110001010.list =
    C ((2:ℤ)^22) * horner X vp00000000001100010101.list + horner X ep00000000001100010101.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100010101 : Branch 1 (-5917889/15625 : ℚ) vp0000000000110001010 := by
  apply branch_checked idp00000000001100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-5917889/15625 : ℚ) - ((1:ℤ):ℚ) = (-11851403/15625 : ℚ) by norm_num]
  exact coverp00000000001100010101
theorem coverp0000000000110001010 : Covers (-5917889/15625 : ℚ) vp0000000000110001010 := join_branches bp00000000001100010100 bp00000000001100010101
private noncomputable def vp000000000011000101_0 : Blocks := edgeBlocks% "full/vectors/000000000011000101-V-0000.bin"
noncomputable def vp000000000011000101 : Blocks := vp000000000011000101_0
private theorem bp0000000000110001010 : Branch 0 (-5917889/31250 : ℚ) vp000000000011000101 := by
  apply branch_left_normalized (c:=vp0000000000110001010) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-5917889/31250 : ℚ) - ((0:ℤ):ℚ) = (-5917889/15625 : ℚ) by norm_num]
  exact coverp0000000000110001010
private noncomputable def ep0000000000110001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001011-E-0000.bin"
noncomputable def ep0000000000110001011 : Blocks := ep0000000000110001011_0
private theorem idp0000000000110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000101.list =
    C ((2:ℤ)^30) * horner X vp0000000000110001011.list + horner X ep0000000000110001011.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110001011 : Branch 1 (-5917889/31250 : ℚ) vp000000000011000101 := by
  apply branch_checked idp0000000000110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-5917889/31250 : ℚ) - ((1:ℤ):ℚ) = (-5933514/15625 : ℚ) by norm_num]
  exact coverp0000000000110001011
theorem coverp000000000011000101 : Covers (-5917889/31250 : ℚ) vp000000000011000101 := join_branches bp0000000000110001010 bp0000000000110001011
private noncomputable def vp00000000001100010011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100010011-V-0000.bin"
noncomputable def vp00000000001100010011 : Blocks := vp00000000001100010011_0
theorem coverp00000000001100010011 : Covers (-11820153/15625 : ℚ) vp00000000001100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100010010_0 : Blocks := edgeBlocks% "full/vectors/00000000001100010010-V-0000.bin"
noncomputable def vp00000000001100010010 : Blocks := vp00000000001100010010_0
theorem coverp00000000001100010010 : Covers (-11804528/15625 : ℚ) vp00000000001100010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001001-V-0000.bin"
noncomputable def vp0000000000110001001 : Blocks := vp0000000000110001001_0
private theorem bp00000000001100010010 : Branch 0 (-5902264/15625 : ℚ) vp0000000000110001001 := by
  apply branch_left_normalized (c:=vp00000000001100010010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5902264/15625 : ℚ) - ((0:ℤ):ℚ) = (-11804528/15625 : ℚ) by norm_num]
  exact coverp00000000001100010010
private noncomputable def ep00000000001100010011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100010011-E-0000.bin"
noncomputable def ep00000000001100010011 : Blocks := ep00000000001100010011_0
private theorem idp00000000001100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110001001.list =
    C ((2:ℤ)^21) * horner X vp00000000001100010011.list + horner X ep00000000001100010011.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100010011 : Branch 1 (-5902264/15625 : ℚ) vp0000000000110001001 := by
  apply branch_checked idp00000000001100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-5902264/15625 : ℚ) - ((1:ℤ):ℚ) = (-11820153/15625 : ℚ) by norm_num]
  exact coverp00000000001100010011
theorem coverp0000000000110001001 : Covers (-5902264/15625 : ℚ) vp0000000000110001001 := join_branches bp00000000001100010010 bp00000000001100010011
private noncomputable def vp0000000000110001000_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001000-V-0000.bin"
noncomputable def vp0000000000110001000 : Blocks := vp0000000000110001000_0
theorem coverp0000000000110001000 : Covers (-5886639/15625 : ℚ) vp0000000000110001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000100_0 : Blocks := edgeBlocks% "full/vectors/000000000011000100-V-0000.bin"
noncomputable def vp000000000011000100 : Blocks := vp000000000011000100_0
private theorem bp0000000000110001000 : Branch 0 (-5886639/31250 : ℚ) vp000000000011000100 := by
  apply branch_left_normalized (c:=vp0000000000110001000) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-5886639/31250 : ℚ) - ((0:ℤ):ℚ) = (-5886639/15625 : ℚ) by norm_num]
  exact coverp0000000000110001000
private noncomputable def ep0000000000110001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001001-E-0000.bin"
noncomputable def ep0000000000110001001 : Blocks := ep0000000000110001001_0
private theorem idp0000000000110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000100.list =
    C ((2:ℤ)^30) * horner X vp0000000000110001001.list + horner X ep0000000000110001001.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110001001 : Branch 1 (-5886639/31250 : ℚ) vp000000000011000100 := by
  apply branch_checked idp0000000000110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-5886639/31250 : ℚ) - ((1:ℤ):ℚ) = (-5902264/15625 : ℚ) by norm_num]
  exact coverp0000000000110001001
theorem coverp000000000011000100 : Covers (-5886639/31250 : ℚ) vp000000000011000100 := join_branches bp0000000000110001000 bp0000000000110001001
private noncomputable def vp00000000001100010_0 : Blocks := edgeBlocks% "full/vectors/00000000001100010-V-0000.bin"
noncomputable def vp00000000001100010 : Blocks := vp00000000001100010_0
private theorem bp000000000011000100 : Branch 0 (-5886639/62500 : ℚ) vp00000000001100010 := by
  apply branch_left_normalized (c:=vp000000000011000100) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-5886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-5886639/31250 : ℚ) by norm_num]
  exact coverp000000000011000100
private noncomputable def ep000000000011000101_0 : Blocks := edgeBlocks% "full/vectors/000000000011000101-E-0000.bin"
noncomputable def ep000000000011000101 : Blocks := ep000000000011000101_0
private theorem idp000000000011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100010.list =
    C ((2:ℤ)^44) * horner X vp000000000011000101.list + horner X ep000000000011000101.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000101 : Branch 1 (-5886639/62500 : ℚ) vp00000000001100010 := by
  apply branch_checked idp000000000011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-5886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-5917889/31250 : ℚ) by norm_num]
  exact coverp000000000011000101
theorem coverp00000000001100010 : Covers (-5886639/62500 : ℚ) vp00000000001100010 := join_branches bp000000000011000100 bp000000000011000101
private noncomputable def vp0000000000110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001-V-0000.bin"
noncomputable def vp0000000000110001 : Blocks := vp0000000000110001_0
private theorem bp00000000001100010 : Branch 0 (-5886639/125000 : ℚ) vp0000000000110001 := by
  apply branch_left_normalized (c:=vp00000000001100010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-5886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-5886639/62500 : ℚ) by norm_num]
  exact coverp00000000001100010
private noncomputable def ep00000000001100011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100011-E-0000.bin"
noncomputable def ep00000000001100011 : Blocks := ep00000000001100011_0
private theorem idp00000000001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110001.list =
    C ((2:ℤ)^71) * horner X vp00000000001100011.list + horner X ep00000000001100011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100011 : Branch 1 (-5886639/125000 : ℚ) vp0000000000110001 := by
  apply branch_checked idp00000000001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-5886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-5949139/62500 : ℚ) by norm_num]
  exact coverp00000000001100011
theorem coverp0000000000110001 : Covers (-5886639/125000 : ℚ) vp0000000000110001 := join_branches bp00000000001100010 bp00000000001100011
private noncomputable def vp00000000001100001111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100001111-V-0000.bin"
noncomputable def vp00000000001100001111 : Blocks := vp00000000001100001111_0
theorem coverp00000000001100001111 : Covers (-11757653/15625 : ℚ) vp00000000001100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000011101_0 : Blocks := edgeBlocks% "full/vectors/000000000011000011101-V-0000.bin"
noncomputable def vp000000000011000011101 : Blocks := vp000000000011000011101_0
theorem coverp000000000011000011101 : Covers (-23499681/15625 : ℚ) vp000000000011000011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110000111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000111001-V-0000.bin"
noncomputable def vp0000000000110000111001 : Blocks := vp0000000000110000111001_0
theorem coverp0000000000110000111001 : Covers (-46983737/15625 : ℚ) vp0000000000110000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110000111000_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000111000-V-0000.bin"
noncomputable def vp0000000000110000111000 : Blocks := vp0000000000110000111000_0
theorem coverp0000000000110000111000 : Covers (-46968112/15625 : ℚ) vp0000000000110000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000011100_0 : Blocks := edgeBlocks% "full/vectors/000000000011000011100-V-0000.bin"
noncomputable def vp000000000011000011100 : Blocks := vp000000000011000011100_0
private theorem bp0000000000110000111000 : Branch 0 (-23484056/15625 : ℚ) vp000000000011000011100 := by
  apply branch_left_normalized (c:=vp0000000000110000111000) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-23484056/15625 : ℚ) - ((0:ℤ):ℚ) = (-46968112/15625 : ℚ) by norm_num]
  exact coverp0000000000110000111000
private noncomputable def ep0000000000110000111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000111001-E-0000.bin"
noncomputable def ep0000000000110000111001 : Blocks := ep0000000000110000111001_0
private theorem idp0000000000110000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000011100.list =
    C ((2:ℤ)^14) * horner X vp0000000000110000111001.list + horner X ep0000000000110000111001.list := by
  exact edge_identity (B := (2:ℤ)^117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110000111001 : Branch 1 (-23484056/15625 : ℚ) vp000000000011000011100 := by
  apply branch_checked idp0000000000110000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-23484056/15625 : ℚ) - ((1:ℤ):ℚ) = (-46983737/15625 : ℚ) by norm_num]
  exact coverp0000000000110000111001
theorem coverp000000000011000011100 : Covers (-23484056/15625 : ℚ) vp000000000011000011100 := join_branches bp0000000000110000111000 bp0000000000110000111001
private noncomputable def vp00000000001100001110_0 : Blocks := edgeBlocks% "full/vectors/00000000001100001110-V-0000.bin"
noncomputable def vp00000000001100001110 : Blocks := vp00000000001100001110_0
private theorem bp000000000011000011100 : Branch 0 (-11742028/15625 : ℚ) vp00000000001100001110 := by
  apply branch_left_normalized (c:=vp000000000011000011100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-11742028/15625 : ℚ) - ((0:ℤ):ℚ) = (-23484056/15625 : ℚ) by norm_num]
  exact coverp000000000011000011100
private noncomputable def ep000000000011000011101_0 : Blocks := edgeBlocks% "full/vectors/000000000011000011101-E-0000.bin"
noncomputable def ep000000000011000011101 : Blocks := ep000000000011000011101_0
private theorem idp000000000011000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100001110.list =
    C ((2:ℤ)^17) * horner X vp000000000011000011101.list + horner X ep000000000011000011101.list := by
  exact edge_identity (B := (2:ℤ)^121) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000011101 : Branch 1 (-11742028/15625 : ℚ) vp00000000001100001110 := by
  apply branch_checked idp000000000011000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-11742028/15625 : ℚ) - ((1:ℤ):ℚ) = (-23499681/15625 : ℚ) by norm_num]
  exact coverp000000000011000011101
theorem coverp00000000001100001110 : Covers (-11742028/15625 : ℚ) vp00000000001100001110 := join_branches bp000000000011000011100 bp000000000011000011101
private noncomputable def vp0000000000110000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000111-V-0000.bin"
noncomputable def vp0000000000110000111 : Blocks := vp0000000000110000111_0
private theorem bp00000000001100001110 : Branch 0 (-5871014/15625 : ℚ) vp0000000000110000111 := by
  apply branch_left_normalized (c:=vp00000000001100001110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5871014/15625 : ℚ) - ((0:ℤ):ℚ) = (-11742028/15625 : ℚ) by norm_num]
  exact coverp00000000001100001110
private noncomputable def ep00000000001100001111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100001111-E-0000.bin"
noncomputable def ep00000000001100001111 : Blocks := ep00000000001100001111_0
private theorem idp00000000001100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110000111.list =
    C ((2:ℤ)^23) * horner X vp00000000001100001111.list + horner X ep00000000001100001111.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100001111 : Branch 1 (-5871014/15625 : ℚ) vp0000000000110000111 := by
  apply branch_checked idp00000000001100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-5871014/15625 : ℚ) - ((1:ℤ):ℚ) = (-11757653/15625 : ℚ) by norm_num]
  exact coverp00000000001100001111
theorem coverp0000000000110000111 : Covers (-5871014/15625 : ℚ) vp0000000000110000111 := join_branches bp00000000001100001110 bp00000000001100001111
private noncomputable def vp000000000011000011011_0 : Blocks := edgeBlocks% "full/vectors/000000000011000011011-V-0000.bin"
noncomputable def vp000000000011000011011 : Blocks := vp000000000011000011011_0
theorem coverp000000000011000011011 : Covers (-23468431/15625 : ℚ) vp000000000011000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000011010_0 : Blocks := edgeBlocks% "full/vectors/000000000011000011010-V-0000.bin"
noncomputable def vp000000000011000011010 : Blocks := vp000000000011000011010_0
theorem coverp000000000011000011010 : Covers (-23452806/15625 : ℚ) vp000000000011000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100001101_0 : Blocks := edgeBlocks% "full/vectors/00000000001100001101-V-0000.bin"
noncomputable def vp00000000001100001101 : Blocks := vp00000000001100001101_0
private theorem bp000000000011000011010 : Branch 0 (-11726403/15625 : ℚ) vp00000000001100001101 := by
  apply branch_left_normalized (c:=vp000000000011000011010) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-11726403/15625 : ℚ) - ((0:ℤ):ℚ) = (-23452806/15625 : ℚ) by norm_num]
  exact coverp000000000011000011010
private noncomputable def ep000000000011000011011_0 : Blocks := edgeBlocks% "full/vectors/000000000011000011011-E-0000.bin"
noncomputable def ep000000000011000011011 : Blocks := ep000000000011000011011_0
private theorem idp000000000011000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100001101.list =
    C ((2:ℤ)^17) * horner X vp000000000011000011011.list + horner X ep000000000011000011011.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000011011 : Branch 1 (-11726403/15625 : ℚ) vp00000000001100001101 := by
  apply branch_checked idp000000000011000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-11726403/15625 : ℚ) - ((1:ℤ):ℚ) = (-23468431/15625 : ℚ) by norm_num]
  exact coverp000000000011000011011
theorem coverp00000000001100001101 : Covers (-11726403/15625 : ℚ) vp00000000001100001101 := join_branches bp000000000011000011010 bp000000000011000011011
private noncomputable def vp00000000001100001100_0 : Blocks := edgeBlocks% "full/vectors/00000000001100001100-V-0000.bin"
noncomputable def vp00000000001100001100 : Blocks := vp00000000001100001100_0
theorem coverp00000000001100001100 : Covers (-11710778/15625 : ℚ) vp00000000001100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110000110_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000110-V-0000.bin"
noncomputable def vp0000000000110000110 : Blocks := vp0000000000110000110_0
private theorem bp00000000001100001100 : Branch 0 (-5855389/15625 : ℚ) vp0000000000110000110 := by
  apply branch_left_normalized (c:=vp00000000001100001100) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-5855389/15625 : ℚ) - ((0:ℤ):ℚ) = (-11710778/15625 : ℚ) by norm_num]
  exact coverp00000000001100001100
private noncomputable def ep00000000001100001101_0 : Blocks := edgeBlocks% "full/vectors/00000000001100001101-E-0000.bin"
noncomputable def ep00000000001100001101 : Blocks := ep00000000001100001101_0
private theorem idp00000000001100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110000110.list =
    C ((2:ℤ)^21) * horner X vp00000000001100001101.list + horner X ep00000000001100001101.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100001101 : Branch 1 (-5855389/15625 : ℚ) vp0000000000110000110 := by
  apply branch_checked idp00000000001100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-5855389/15625 : ℚ) - ((1:ℤ):ℚ) = (-11726403/15625 : ℚ) by norm_num]
  exact coverp00000000001100001101
theorem coverp0000000000110000110 : Covers (-5855389/15625 : ℚ) vp0000000000110000110 := join_branches bp00000000001100001100 bp00000000001100001101
private noncomputable def vp000000000011000011_0 : Blocks := edgeBlocks% "full/vectors/000000000011000011-V-0000.bin"
noncomputable def vp000000000011000011 : Blocks := vp000000000011000011_0
private theorem bp0000000000110000110 : Branch 0 (-5855389/31250 : ℚ) vp000000000011000011 := by
  apply branch_left_normalized (c:=vp0000000000110000110) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-5855389/31250 : ℚ) - ((0:ℤ):ℚ) = (-5855389/15625 : ℚ) by norm_num]
  exact coverp0000000000110000110
private noncomputable def ep0000000000110000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000111-E-0000.bin"
noncomputable def ep0000000000110000111 : Blocks := ep0000000000110000111_0
private theorem idp0000000000110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000011.list =
    C ((2:ℤ)^29) * horner X vp0000000000110000111.list + horner X ep0000000000110000111.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110000111 : Branch 1 (-5855389/31250 : ℚ) vp000000000011000011 := by
  apply branch_checked idp0000000000110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-5855389/31250 : ℚ) - ((1:ℤ):ℚ) = (-5871014/15625 : ℚ) by norm_num]
  exact coverp0000000000110000111
theorem coverp000000000011000011 : Covers (-5855389/31250 : ℚ) vp000000000011000011 := join_branches bp0000000000110000110 bp0000000000110000111
private noncomputable def vp0000000000110000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000101-V-0000.bin"
noncomputable def vp0000000000110000101 : Blocks := vp0000000000110000101_0
theorem coverp0000000000110000101 : Covers (-5839764/15625 : ℚ) vp0000000000110000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110000100_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000100-V-0000.bin"
noncomputable def vp0000000000110000100 : Blocks := vp0000000000110000100_0
theorem coverp0000000000110000100 : Covers (-5824139/15625 : ℚ) vp0000000000110000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000010_0 : Blocks := edgeBlocks% "full/vectors/000000000011000010-V-0000.bin"
noncomputable def vp000000000011000010 : Blocks := vp000000000011000010_0
private theorem bp0000000000110000100 : Branch 0 (-5824139/31250 : ℚ) vp000000000011000010 := by
  apply branch_left_normalized (c:=vp0000000000110000100) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-5824139/31250 : ℚ) - ((0:ℤ):ℚ) = (-5824139/15625 : ℚ) by norm_num]
  exact coverp0000000000110000100
private noncomputable def ep0000000000110000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000101-E-0000.bin"
noncomputable def ep0000000000110000101 : Blocks := ep0000000000110000101_0
private theorem idp0000000000110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000010.list =
    C ((2:ℤ)^31) * horner X vp0000000000110000101.list + horner X ep0000000000110000101.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110000101 : Branch 1 (-5824139/31250 : ℚ) vp000000000011000010 := by
  apply branch_checked idp0000000000110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-5824139/31250 : ℚ) - ((1:ℤ):ℚ) = (-5839764/15625 : ℚ) by norm_num]
  exact coverp0000000000110000101
theorem coverp000000000011000010 : Covers (-5824139/31250 : ℚ) vp000000000011000010 := join_branches bp0000000000110000100 bp0000000000110000101
private noncomputable def vp00000000001100001_0 : Blocks := edgeBlocks% "full/vectors/00000000001100001-V-0000.bin"
noncomputable def vp00000000001100001 : Blocks := vp00000000001100001_0
private theorem bp000000000011000010 : Branch 0 (-5824139/62500 : ℚ) vp00000000001100001 := by
  apply branch_left_normalized (c:=vp000000000011000010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-5824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-5824139/31250 : ℚ) by norm_num]
  exact coverp000000000011000010
private noncomputable def ep000000000011000011_0 : Blocks := edgeBlocks% "full/vectors/000000000011000011-E-0000.bin"
noncomputable def ep000000000011000011 : Blocks := ep000000000011000011_0
private theorem idp000000000011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100001.list =
    C ((2:ℤ)^46) * horner X vp000000000011000011.list + horner X ep000000000011000011.list := by
  exact edge_identity (B := (2:ℤ)^160) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000011 : Branch 1 (-5824139/62500 : ℚ) vp00000000001100001 := by
  apply branch_checked idp000000000011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-5824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-5855389/31250 : ℚ) by norm_num]
  exact coverp000000000011000011
theorem coverp00000000001100001 : Covers (-5824139/62500 : ℚ) vp00000000001100001 := join_branches bp000000000011000010 bp000000000011000011
private noncomputable def vp0000000000110000011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000011111-V-0000.bin"
noncomputable def vp0000000000110000011111 : Blocks := vp0000000000110000011111_0
theorem coverp0000000000110000011111 : Covers (-46577487/15625 : ℚ) vp0000000000110000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110000011110_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000011110-V-0000.bin"
noncomputable def vp0000000000110000011110 : Blocks := vp0000000000110000011110_0
theorem coverp0000000000110000011110 : Covers (-46561862/15625 : ℚ) vp0000000000110000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000001111_0 : Blocks := edgeBlocks% "full/vectors/000000000011000001111-V-0000.bin"
noncomputable def vp000000000011000001111 : Blocks := vp000000000011000001111_0
private theorem bp0000000000110000011110 : Branch 0 (-23280931/15625 : ℚ) vp000000000011000001111 := by
  apply branch_left_normalized (c:=vp0000000000110000011110) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-23280931/15625 : ℚ) - ((0:ℤ):ℚ) = (-46561862/15625 : ℚ) by norm_num]
  exact coverp0000000000110000011110
private noncomputable def ep0000000000110000011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000011111-E-0000.bin"
noncomputable def ep0000000000110000011111 : Blocks := ep0000000000110000011111_0
private theorem idp0000000000110000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000001111.list =
    C ((2:ℤ)^14) * horner X vp0000000000110000011111.list + horner X ep0000000000110000011111.list := by
  exact edge_identity (B := (2:ℤ)^117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110000011111 : Branch 1 (-23280931/15625 : ℚ) vp000000000011000001111 := by
  apply branch_checked idp0000000000110000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-23280931/15625 : ℚ) - ((1:ℤ):ℚ) = (-46577487/15625 : ℚ) by norm_num]
  exact coverp0000000000110000011111
theorem coverp000000000011000001111 : Covers (-23280931/15625 : ℚ) vp000000000011000001111 := join_branches bp0000000000110000011110 bp0000000000110000011111
private noncomputable def vp000000000011000001110_0 : Blocks := edgeBlocks% "full/vectors/000000000011000001110-V-0000.bin"
noncomputable def vp000000000011000001110 : Blocks := vp000000000011000001110_0
theorem coverp000000000011000001110 : Covers (-23265306/15625 : ℚ) vp000000000011000001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100000111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000111-V-0000.bin"
noncomputable def vp00000000001100000111 : Blocks := vp00000000001100000111_0
private theorem bp000000000011000001110 : Branch 0 (-11632653/15625 : ℚ) vp00000000001100000111 := by
  apply branch_left_normalized (c:=vp000000000011000001110) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-11632653/15625 : ℚ) - ((0:ℤ):ℚ) = (-23265306/15625 : ℚ) by norm_num]
  exact coverp000000000011000001110
private noncomputable def ep000000000011000001111_0 : Blocks := edgeBlocks% "full/vectors/000000000011000001111-E-0000.bin"
noncomputable def ep000000000011000001111 : Blocks := ep000000000011000001111_0
private theorem idp000000000011000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100000111.list =
    C ((2:ℤ)^17) * horner X vp000000000011000001111.list + horner X ep000000000011000001111.list := by
  exact edge_identity (B := (2:ℤ)^122) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000001111 : Branch 1 (-11632653/15625 : ℚ) vp00000000001100000111 := by
  apply branch_checked idp000000000011000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-11632653/15625 : ℚ) - ((1:ℤ):ℚ) = (-23280931/15625 : ℚ) by norm_num]
  exact coverp000000000011000001111
theorem coverp00000000001100000111 : Covers (-11632653/15625 : ℚ) vp00000000001100000111 := join_branches bp000000000011000001110 bp000000000011000001111
private noncomputable def vp00000000001100000110_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000110-V-0000.bin"
noncomputable def vp00000000001100000110 : Blocks := vp00000000001100000110_0
theorem coverp00000000001100000110 : Covers (-11617028/15625 : ℚ) vp00000000001100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000011-V-0000.bin"
noncomputable def vp0000000000110000011 : Blocks := vp0000000000110000011_0
private theorem bp00000000001100000110 : Branch 0 (-5808514/15625 : ℚ) vp0000000000110000011 := by
  apply branch_left_normalized (c:=vp00000000001100000110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5808514/15625 : ℚ) - ((0:ℤ):ℚ) = (-11617028/15625 : ℚ) by norm_num]
  exact coverp00000000001100000110
private noncomputable def ep00000000001100000111_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000111-E-0000.bin"
noncomputable def ep00000000001100000111 : Blocks := ep00000000001100000111_0
private theorem idp00000000001100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110000011.list =
    C ((2:ℤ)^21) * horner X vp00000000001100000111.list + horner X ep00000000001100000111.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100000111 : Branch 1 (-5808514/15625 : ℚ) vp0000000000110000011 := by
  apply branch_checked idp00000000001100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-5808514/15625 : ℚ) - ((1:ℤ):ℚ) = (-11632653/15625 : ℚ) by norm_num]
  exact coverp00000000001100000111
theorem coverp0000000000110000011 : Covers (-5808514/15625 : ℚ) vp0000000000110000011 := join_branches bp00000000001100000110 bp00000000001100000111
private noncomputable def vp00000000001100000101_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000101-V-0000.bin"
noncomputable def vp00000000001100000101 : Blocks := vp00000000001100000101_0
theorem coverp00000000001100000101 : Covers (-11601403/15625 : ℚ) vp00000000001100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100000100_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000100-V-0000.bin"
noncomputable def vp00000000001100000100 : Blocks := vp00000000001100000100_0
theorem coverp00000000001100000100 : Covers (-11585778/15625 : ℚ) vp00000000001100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110000010_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000010-V-0000.bin"
noncomputable def vp0000000000110000010 : Blocks := vp0000000000110000010_0
private theorem bp00000000001100000100 : Branch 0 (-5792889/15625 : ℚ) vp0000000000110000010 := by
  apply branch_left_normalized (c:=vp00000000001100000100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5792889/15625 : ℚ) - ((0:ℤ):ℚ) = (-11585778/15625 : ℚ) by norm_num]
  exact coverp00000000001100000100
private noncomputable def ep00000000001100000101_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000101-E-0000.bin"
noncomputable def ep00000000001100000101 : Blocks := ep00000000001100000101_0
private theorem idp00000000001100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110000010.list =
    C ((2:ℤ)^22) * horner X vp00000000001100000101.list + horner X ep00000000001100000101.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100000101 : Branch 1 (-5792889/15625 : ℚ) vp0000000000110000010 := by
  apply branch_checked idp00000000001100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-5792889/15625 : ℚ) - ((1:ℤ):ℚ) = (-11601403/15625 : ℚ) by norm_num]
  exact coverp00000000001100000101
theorem coverp0000000000110000010 : Covers (-5792889/15625 : ℚ) vp0000000000110000010 := join_branches bp00000000001100000100 bp00000000001100000101
private noncomputable def vp000000000011000001_0 : Blocks := edgeBlocks% "full/vectors/000000000011000001-V-0000.bin"
noncomputable def vp000000000011000001 : Blocks := vp000000000011000001_0
private theorem bp0000000000110000010 : Branch 0 (-5792889/31250 : ℚ) vp000000000011000001 := by
  apply branch_left_normalized (c:=vp0000000000110000010) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-5792889/31250 : ℚ) - ((0:ℤ):ℚ) = (-5792889/15625 : ℚ) by norm_num]
  exact coverp0000000000110000010
private noncomputable def ep0000000000110000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000011-E-0000.bin"
noncomputable def ep0000000000110000011 : Blocks := ep0000000000110000011_0
private theorem idp0000000000110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000001.list =
    C ((2:ℤ)^30) * horner X vp0000000000110000011.list + horner X ep0000000000110000011.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110000011 : Branch 1 (-5792889/31250 : ℚ) vp000000000011000001 := by
  apply branch_checked idp0000000000110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-5792889/31250 : ℚ) - ((1:ℤ):ℚ) = (-5808514/15625 : ℚ) by norm_num]
  exact coverp0000000000110000011
theorem coverp000000000011000001 : Covers (-5792889/31250 : ℚ) vp000000000011000001 := join_branches bp0000000000110000010 bp0000000000110000011
private noncomputable def vp000000000011000000111_0 : Blocks := edgeBlocks% "full/vectors/000000000011000000111-V-0000.bin"
noncomputable def vp000000000011000000111 : Blocks := vp000000000011000000111_0
theorem coverp000000000011000000111 : Covers (-23155931/15625 : ℚ) vp000000000011000000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100000011011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000011011-V-0000.bin"
noncomputable def vp00000000001100000011011 : Blocks := vp00000000001100000011011_0
theorem coverp00000000001100000011011 : Covers (-92608099/15625 : ℚ) vp00000000001100000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100000011010_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000011010-V-0000.bin"
noncomputable def vp00000000001100000011010 : Blocks := vp00000000001100000011010_0
theorem coverp00000000001100000011010 : Covers (-92592474/15625 : ℚ) vp00000000001100000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110000001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000001101-V-0000.bin"
noncomputable def vp0000000000110000001101 : Blocks := vp0000000000110000001101_0
private theorem bp00000000001100000011010 : Branch 0 (-46296237/15625 : ℚ) vp0000000000110000001101 := by
  apply branch_left_normalized (c:=vp00000000001100000011010) (k:=0) (m:=9) (by decide +kernel)
  rw [show 2*(-46296237/15625 : ℚ) - ((0:ℤ):ℚ) = (-92592474/15625 : ℚ) by norm_num]
  exact coverp00000000001100000011010
private noncomputable def ep00000000001100000011011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000011011-E-0000.bin"
noncomputable def ep00000000001100000011011 : Blocks := ep00000000001100000011011_0
private theorem idp00000000001100000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110000001101.list =
    C ((2:ℤ)^12) * horner X vp00000000001100000011011.list + horner X ep00000000001100000011011.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100000011011 : Branch 1 (-46296237/15625 : ℚ) vp0000000000110000001101 := by
  apply branch_checked idp00000000001100000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-46296237/15625 : ℚ) - ((1:ℤ):ℚ) = (-92608099/15625 : ℚ) by norm_num]
  exact coverp00000000001100000011011
theorem coverp0000000000110000001101 : Covers (-46296237/15625 : ℚ) vp0000000000110000001101 := join_branches bp00000000001100000011010 bp00000000001100000011011
private noncomputable def vp00000000001100000011001_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000011001-V-0000.bin"
noncomputable def vp00000000001100000011001 : Blocks := vp00000000001100000011001_0
theorem coverp00000000001100000011001 : Covers (-92576849/15625 : ℚ) vp00000000001100000011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100000011000_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000011000-V-0000.bin"
noncomputable def vp00000000001100000011000 : Blocks := vp00000000001100000011000_0
theorem coverp00000000001100000011000 : Covers (-92561224/15625 : ℚ) vp00000000001100000011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110000001100_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000001100-V-0000.bin"
noncomputable def vp0000000000110000001100 : Blocks := vp0000000000110000001100_0
private theorem bp00000000001100000011000 : Branch 0 (-46280612/15625 : ℚ) vp0000000000110000001100 := by
  apply branch_left_normalized (c:=vp00000000001100000011000) (k:=0) (m:=9) (by decide +kernel)
  rw [show 2*(-46280612/15625 : ℚ) - ((0:ℤ):ℚ) = (-92561224/15625 : ℚ) by norm_num]
  exact coverp00000000001100000011000
private noncomputable def ep00000000001100000011001_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000011001-E-0000.bin"
noncomputable def ep00000000001100000011001 : Blocks := ep00000000001100000011001_0
private theorem idp00000000001100000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110000001100.list =
    C ((2:ℤ)^11) * horner X vp00000000001100000011001.list + horner X ep00000000001100000011001.list := by
  exact edge_identity (B := (2:ℤ)^116) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100000011001 : Branch 1 (-46280612/15625 : ℚ) vp0000000000110000001100 := by
  apply branch_checked idp00000000001100000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-46280612/15625 : ℚ) - ((1:ℤ):ℚ) = (-92576849/15625 : ℚ) by norm_num]
  exact coverp00000000001100000011001
theorem coverp0000000000110000001100 : Covers (-46280612/15625 : ℚ) vp0000000000110000001100 := join_branches bp00000000001100000011000 bp00000000001100000011001
private noncomputable def vp000000000011000000110_0 : Blocks := edgeBlocks% "full/vectors/000000000011000000110-V-0000.bin"
noncomputable def vp000000000011000000110 : Blocks := vp000000000011000000110_0
private theorem bp0000000000110000001100 : Branch 0 (-23140306/15625 : ℚ) vp000000000011000000110 := by
  apply branch_left_normalized (c:=vp0000000000110000001100) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-23140306/15625 : ℚ) - ((0:ℤ):ℚ) = (-46280612/15625 : ℚ) by norm_num]
  exact coverp0000000000110000001100
private noncomputable def ep0000000000110000001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000001101-E-0000.bin"
noncomputable def ep0000000000110000001101 : Blocks := ep0000000000110000001101_0
private theorem idp0000000000110000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000000110.list =
    C ((2:ℤ)^13) * horner X vp0000000000110000001101.list + horner X ep0000000000110000001101.list := by
  exact edge_identity (B := (2:ℤ)^118) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110000001101 : Branch 1 (-23140306/15625 : ℚ) vp000000000011000000110 := by
  apply branch_checked idp0000000000110000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-23140306/15625 : ℚ) - ((1:ℤ):ℚ) = (-46296237/15625 : ℚ) by norm_num]
  exact coverp0000000000110000001101
theorem coverp000000000011000000110 : Covers (-23140306/15625 : ℚ) vp000000000011000000110 := join_branches bp0000000000110000001100 bp0000000000110000001101
private noncomputable def vp00000000001100000011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000011-V-0000.bin"
noncomputable def vp00000000001100000011 : Blocks := vp00000000001100000011_0
private theorem bp000000000011000000110 : Branch 0 (-11570153/15625 : ℚ) vp00000000001100000011 := by
  apply branch_left_normalized (c:=vp000000000011000000110) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-11570153/15625 : ℚ) - ((0:ℤ):ℚ) = (-23140306/15625 : ℚ) by norm_num]
  exact coverp000000000011000000110
private noncomputable def ep000000000011000000111_0 : Blocks := edgeBlocks% "full/vectors/000000000011000000111-E-0000.bin"
noncomputable def ep000000000011000000111 : Blocks := ep000000000011000000111_0
private theorem idp000000000011000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100000011.list =
    C ((2:ℤ)^17) * horner X vp000000000011000000111.list + horner X ep000000000011000000111.list := by
  exact edge_identity (B := (2:ℤ)^124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000000111 : Branch 1 (-11570153/15625 : ℚ) vp00000000001100000011 := by
  apply branch_checked idp000000000011000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-11570153/15625 : ℚ) - ((1:ℤ):ℚ) = (-23155931/15625 : ℚ) by norm_num]
  exact coverp000000000011000000111
theorem coverp00000000001100000011 : Covers (-11570153/15625 : ℚ) vp00000000001100000011 := join_branches bp000000000011000000110 bp000000000011000000111
private noncomputable def vp0000000000110000001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000001011-V-0000.bin"
noncomputable def vp0000000000110000001011 : Blocks := vp0000000000110000001011_0
theorem coverp0000000000110000001011 : Covers (-46264987/15625 : ℚ) vp0000000000110000001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110000001010_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000001010-V-0000.bin"
noncomputable def vp0000000000110000001010 : Blocks := vp0000000000110000001010_0
theorem coverp0000000000110000001010 : Covers (-46249362/15625 : ℚ) vp0000000000110000001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000000101_0 : Blocks := edgeBlocks% "full/vectors/000000000011000000101-V-0000.bin"
noncomputable def vp000000000011000000101 : Blocks := vp000000000011000000101_0
private theorem bp0000000000110000001010 : Branch 0 (-23124681/15625 : ℚ) vp000000000011000000101 := by
  apply branch_left_normalized (c:=vp0000000000110000001010) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-23124681/15625 : ℚ) - ((0:ℤ):ℚ) = (-46249362/15625 : ℚ) by norm_num]
  exact coverp0000000000110000001010
private noncomputable def ep0000000000110000001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000001011-E-0000.bin"
noncomputable def ep0000000000110000001011 : Blocks := ep0000000000110000001011_0
private theorem idp0000000000110000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000000101.list =
    C ((2:ℤ)^13) * horner X vp0000000000110000001011.list + horner X ep0000000000110000001011.list := by
  exact edge_identity (B := (2:ℤ)^120) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110000001011 : Branch 1 (-23124681/15625 : ℚ) vp000000000011000000101 := by
  apply branch_checked idp0000000000110000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-23124681/15625 : ℚ) - ((1:ℤ):ℚ) = (-46264987/15625 : ℚ) by norm_num]
  exact coverp0000000000110000001011
theorem coverp000000000011000000101 : Covers (-23124681/15625 : ℚ) vp000000000011000000101 := join_branches bp0000000000110000001010 bp0000000000110000001011
private noncomputable def vp000000000011000000100_0 : Blocks := edgeBlocks% "full/vectors/000000000011000000100-V-0000.bin"
noncomputable def vp000000000011000000100 : Blocks := vp000000000011000000100_0
theorem coverp000000000011000000100 : Covers (-23109056/15625 : ℚ) vp000000000011000000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100000010_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000010-V-0000.bin"
noncomputable def vp00000000001100000010 : Blocks := vp00000000001100000010_0
private theorem bp000000000011000000100 : Branch 0 (-11554528/15625 : ℚ) vp00000000001100000010 := by
  apply branch_left_normalized (c:=vp000000000011000000100) (k:=0) (m:=12) (by decide +kernel)
  rw [show 2*(-11554528/15625 : ℚ) - ((0:ℤ):ℚ) = (-23109056/15625 : ℚ) by norm_num]
  exact coverp000000000011000000100
private noncomputable def ep000000000011000000101_0 : Blocks := edgeBlocks% "full/vectors/000000000011000000101-E-0000.bin"
noncomputable def ep000000000011000000101 : Blocks := ep000000000011000000101_0
private theorem idp000000000011000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100000010.list =
    C ((2:ℤ)^16) * horner X vp000000000011000000101.list + horner X ep000000000011000000101.list := by
  exact edge_identity (B := (2:ℤ)^125) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000000101 : Branch 1 (-11554528/15625 : ℚ) vp00000000001100000010 := by
  apply branch_checked idp000000000011000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-11554528/15625 : ℚ) - ((1:ℤ):ℚ) = (-23124681/15625 : ℚ) by norm_num]
  exact coverp000000000011000000101
theorem coverp00000000001100000010 : Covers (-11554528/15625 : ℚ) vp00000000001100000010 := join_branches bp000000000011000000100 bp000000000011000000101
private noncomputable def vp0000000000110000001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000001-V-0000.bin"
noncomputable def vp0000000000110000001 : Blocks := vp0000000000110000001_0
private theorem bp00000000001100000010 : Branch 0 (-5777264/15625 : ℚ) vp0000000000110000001 := by
  apply branch_left_normalized (c:=vp00000000001100000010) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-5777264/15625 : ℚ) - ((0:ℤ):ℚ) = (-11554528/15625 : ℚ) by norm_num]
  exact coverp00000000001100000010
private noncomputable def ep00000000001100000011_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000011-E-0000.bin"
noncomputable def ep00000000001100000011 : Blocks := ep00000000001100000011_0
private theorem idp00000000001100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110000001.list =
    C ((2:ℤ)^21) * horner X vp00000000001100000011.list + horner X ep00000000001100000011.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100000011 : Branch 1 (-5777264/15625 : ℚ) vp0000000000110000001 := by
  apply branch_checked idp00000000001100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-5777264/15625 : ℚ) - ((1:ℤ):ℚ) = (-11570153/15625 : ℚ) by norm_num]
  exact coverp00000000001100000011
theorem coverp0000000000110000001 : Covers (-5777264/15625 : ℚ) vp0000000000110000001 := join_branches bp00000000001100000010 bp00000000001100000011
private noncomputable def vp000000000011000000011_0 : Blocks := edgeBlocks% "full/vectors/000000000011000000011-V-0000.bin"
noncomputable def vp000000000011000000011 : Blocks := vp000000000011000000011_0
theorem coverp000000000011000000011 : Covers (-23093431/15625 : ℚ) vp000000000011000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011000000010_0 : Blocks := edgeBlocks% "full/vectors/000000000011000000010-V-0000.bin"
noncomputable def vp000000000011000000010 : Blocks := vp000000000011000000010_0
theorem coverp000000000011000000010 : Covers (-23077806/15625 : ℚ) vp000000000011000000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001100000001_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000001-V-0000.bin"
noncomputable def vp00000000001100000001 : Blocks := vp00000000001100000001_0
private theorem bp000000000011000000010 : Branch 0 (-11538903/15625 : ℚ) vp00000000001100000001 := by
  apply branch_left_normalized (c:=vp000000000011000000010) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-11538903/15625 : ℚ) - ((0:ℤ):ℚ) = (-23077806/15625 : ℚ) by norm_num]
  exact coverp000000000011000000010
private noncomputable def ep000000000011000000011_0 : Blocks := edgeBlocks% "full/vectors/000000000011000000011-E-0000.bin"
noncomputable def ep000000000011000000011 : Blocks := ep000000000011000000011_0
private theorem idp000000000011000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100000001.list =
    C ((2:ℤ)^16) * horner X vp000000000011000000011.list + horner X ep000000000011000000011.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000000011 : Branch 1 (-11538903/15625 : ℚ) vp00000000001100000001 := by
  apply branch_checked idp000000000011000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-11538903/15625 : ℚ) - ((1:ℤ):ℚ) = (-23093431/15625 : ℚ) by norm_num]
  exact coverp000000000011000000011
theorem coverp00000000001100000001 : Covers (-11538903/15625 : ℚ) vp00000000001100000001 := join_branches bp000000000011000000010 bp000000000011000000011
private noncomputable def vp00000000001100000000_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000000-V-0000.bin"
noncomputable def vp00000000001100000000 : Blocks := vp00000000001100000000_0
theorem coverp00000000001100000000 : Covers (-11523278/15625 : ℚ) vp00000000001100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000110000000_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000000-V-0000.bin"
noncomputable def vp0000000000110000000 : Blocks := vp0000000000110000000_0
private theorem bp00000000001100000000 : Branch 0 (-5761639/15625 : ℚ) vp0000000000110000000 := by
  apply branch_left_normalized (c:=vp00000000001100000000) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-5761639/15625 : ℚ) - ((0:ℤ):ℚ) = (-11523278/15625 : ℚ) by norm_num]
  exact coverp00000000001100000000
private noncomputable def ep00000000001100000001_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000001-E-0000.bin"
noncomputable def ep00000000001100000001 : Blocks := ep00000000001100000001_0
private theorem idp00000000001100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110000000.list =
    C ((2:ℤ)^20) * horner X vp00000000001100000001.list + horner X ep00000000001100000001.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100000001 : Branch 1 (-5761639/15625 : ℚ) vp0000000000110000000 := by
  apply branch_checked idp00000000001100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-5761639/15625 : ℚ) - ((1:ℤ):ℚ) = (-11538903/15625 : ℚ) by norm_num]
  exact coverp00000000001100000001
theorem coverp0000000000110000000 : Covers (-5761639/15625 : ℚ) vp0000000000110000000 := join_branches bp00000000001100000000 bp00000000001100000001
private noncomputable def vp000000000011000000_0 : Blocks := edgeBlocks% "full/vectors/000000000011000000-V-0000.bin"
noncomputable def vp000000000011000000 : Blocks := vp000000000011000000_0
private theorem bp0000000000110000000 : Branch 0 (-5761639/31250 : ℚ) vp000000000011000000 := by
  apply branch_left_normalized (c:=vp0000000000110000000) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-5761639/31250 : ℚ) - ((0:ℤ):ℚ) = (-5761639/15625 : ℚ) by norm_num]
  exact coverp0000000000110000000
private noncomputable def ep0000000000110000001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000001-E-0000.bin"
noncomputable def ep0000000000110000001 : Blocks := ep0000000000110000001_0
private theorem idp0000000000110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000000.list =
    C ((2:ℤ)^27) * horner X vp0000000000110000001.list + horner X ep0000000000110000001.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110000001 : Branch 1 (-5761639/31250 : ℚ) vp000000000011000000 := by
  apply branch_checked idp0000000000110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-5761639/31250 : ℚ) - ((1:ℤ):ℚ) = (-5777264/15625 : ℚ) by norm_num]
  exact coverp0000000000110000001
theorem coverp000000000011000000 : Covers (-5761639/31250 : ℚ) vp000000000011000000 := join_branches bp0000000000110000000 bp0000000000110000001
private noncomputable def vp00000000001100000_0 : Blocks := edgeBlocks% "full/vectors/00000000001100000-V-0000.bin"
noncomputable def vp00000000001100000 : Blocks := vp00000000001100000_0
private theorem bp000000000011000000 : Branch 0 (-5761639/62500 : ℚ) vp00000000001100000 := by
  apply branch_left_normalized (c:=vp000000000011000000) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-5761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-5761639/31250 : ℚ) by norm_num]
  exact coverp000000000011000000
private noncomputable def ep000000000011000001_0 : Blocks := edgeBlocks% "full/vectors/000000000011000001-E-0000.bin"
noncomputable def ep000000000011000001 : Blocks := ep000000000011000001_0
private theorem idp000000000011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100000.list =
    C ((2:ℤ)^41) * horner X vp000000000011000001.list + horner X ep000000000011000001.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011000001 : Branch 1 (-5761639/62500 : ℚ) vp00000000001100000 := by
  apply branch_checked idp000000000011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-5761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-5792889/31250 : ℚ) by norm_num]
  exact coverp000000000011000001
theorem coverp00000000001100000 : Covers (-5761639/62500 : ℚ) vp00000000001100000 := join_branches bp000000000011000000 bp000000000011000001
private noncomputable def vp0000000000110000_0 : Blocks := edgeBlocks% "full/vectors/0000000000110000-V-0000.bin"
noncomputable def vp0000000000110000 : Blocks := vp0000000000110000_0
private theorem bp00000000001100000 : Branch 0 (-5761639/125000 : ℚ) vp0000000000110000 := by
  apply branch_left_normalized (c:=vp00000000001100000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-5761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-5761639/62500 : ℚ) by norm_num]
  exact coverp00000000001100000
private noncomputable def ep00000000001100001_0 : Blocks := edgeBlocks% "full/vectors/00000000001100001-E-0000.bin"
noncomputable def ep00000000001100001 : Blocks := ep00000000001100001_0
private theorem idp00000000001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110000.list =
    C ((2:ℤ)^67) * horner X vp00000000001100001.list + horner X ep00000000001100001.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001100001 : Branch 1 (-5761639/125000 : ℚ) vp0000000000110000 := by
  apply branch_checked idp00000000001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-5761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-5824139/62500 : ℚ) by norm_num]
  exact coverp00000000001100001
theorem coverp0000000000110000 : Covers (-5761639/125000 : ℚ) vp0000000000110000 := join_branches bp00000000001100000 bp00000000001100001
private noncomputable def vp000000000011000_0 : Blocks := edgeBlocks% "full/vectors/000000000011000-V-0000.bin"
noncomputable def vp000000000011000 : Blocks := vp000000000011000_0
private theorem bp0000000000110000 : Branch 0 (-5761639/250000 : ℚ) vp000000000011000 := by
  apply branch_left_normalized (c:=vp0000000000110000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-5761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-5761639/125000 : ℚ) by norm_num]
  exact coverp0000000000110000
private noncomputable def ep0000000000110001_0 : Blocks := edgeBlocks% "full/vectors/0000000000110001-E-0000.bin"
noncomputable def ep0000000000110001 : Blocks := ep0000000000110001_0
private theorem idp0000000000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011000.list =
    C ((2:ℤ)^119) * horner X vp0000000000110001.list + horner X ep0000000000110001.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000110001 : Branch 1 (-5761639/250000 : ℚ) vp000000000011000 := by
  apply branch_checked idp0000000000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-5761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-5886639/125000 : ℚ) by norm_num]
  exact coverp0000000000110001
theorem coverp000000000011000 : Covers (-5761639/250000 : ℚ) vp000000000011000 := join_branches bp0000000000110000 bp0000000000110001
private noncomputable def vp00000000001100_0 : Blocks := edgeBlocks% "full/vectors/00000000001100-V-0000.bin"
private noncomputable def vp00000000001100_1 : Blocks := edgeBlocks% "full/vectors/00000000001100-V-0001.bin"
noncomputable def vp00000000001100 : Blocks := (Blocks.join vp00000000001100_0 vp00000000001100_1)
private theorem bp000000000011000 : Branch 0 (-5761639/500000 : ℚ) vp00000000001100 := by
  apply branch_left_normalized (c:=vp000000000011000) (k:=0) (m:=118) (by decide +kernel)
  rw [show 2*(-5761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-5761639/250000 : ℚ) by norm_num]
  exact coverp000000000011000
private noncomputable def ep000000000011001_0 : Blocks := edgeBlocks% "full/vectors/000000000011001-E-0000.bin"
private noncomputable def ep000000000011001_1 : Blocks := edgeBlocks% "full/vectors/000000000011001-E-0001.bin"
noncomputable def ep000000000011001 : Blocks := (Blocks.join ep000000000011001_0 ep000000000011001_1)
private theorem idp000000000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001100.list =
    C ((2:ℤ)^218) * horner X vp000000000011001.list + horner X ep000000000011001.list := by
  exact edge_identity (B := (2:ℤ)^418) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011001 : Branch 1 (-5761639/500000 : ℚ) vp00000000001100 := by
  apply branch_checked idp000000000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-5761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-6011639/250000 : ℚ) by norm_num]
  exact coverp000000000011001
theorem coverp00000000001100 : Covers (-5761639/500000 : ℚ) vp00000000001100 := join_branches bp000000000011000 bp000000000011001
private noncomputable def vp0000000000110_0 : Blocks := edgeBlocks% "full/vectors/0000000000110-V-0000.bin"
private noncomputable def vp0000000000110_1 : Blocks := edgeBlocks% "full/vectors/0000000000110-V-0001.bin"
private noncomputable def vp0000000000110_2 : Blocks := edgeBlocks% "full/vectors/0000000000110-V-0002.bin"
private noncomputable def vp0000000000110_3 : Blocks := edgeBlocks% "full/vectors/0000000000110-V-0003.bin"
noncomputable def vp0000000000110 : Blocks := (Blocks.join (Blocks.join vp0000000000110_0 vp0000000000110_1) (Blocks.join vp0000000000110_2 vp0000000000110_3))
private theorem bp00000000001100 : Branch 0 (-5761639/1000000 : ℚ) vp0000000000110 := by
  apply branch_left_normalized (c:=vp00000000001100) (k:=0) (m:=217) (by decide +kernel)
  rw [show 2*(-5761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-5761639/500000 : ℚ) by norm_num]
  exact coverp00000000001100
private noncomputable def ep00000000001101_0 : Blocks := edgeBlocks% "full/vectors/00000000001101-E-0000.bin"
private noncomputable def ep00000000001101_1 : Blocks := edgeBlocks% "full/vectors/00000000001101-E-0001.bin"
private noncomputable def ep00000000001101_2 : Blocks := edgeBlocks% "full/vectors/00000000001101-E-0002.bin"
private noncomputable def ep00000000001101_3 : Blocks := edgeBlocks% "full/vectors/00000000001101-E-0003.bin"
noncomputable def ep00000000001101 : Blocks := (Blocks.join (Blocks.join ep00000000001101_0 ep00000000001101_1) (Blocks.join ep00000000001101_2 ep00000000001101_3))
private theorem idp00000000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000110.list =
    C ((2:ℤ)^418) * horner X vp00000000001101.list + horner X ep00000000001101.list := by
  exact edge_identity (B := (2:ℤ)^724) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001101 : Branch 1 (-5761639/1000000 : ℚ) vp0000000000110 := by
  apply branch_checked idp00000000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-5761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-6261639/500000 : ℚ) by norm_num]
  exact coverp00000000001101
theorem coverp0000000000110 : Covers (-5761639/1000000 : ℚ) vp0000000000110 := join_branches bp00000000001100 bp00000000001101
private noncomputable def vp000000000011_0 : Blocks := edgeBlocks% "full/vectors/000000000011-V-0000.bin"
private noncomputable def vp000000000011_1 : Blocks := edgeBlocks% "full/vectors/000000000011-V-0001.bin"
private noncomputable def vp000000000011_2 : Blocks := edgeBlocks% "full/vectors/000000000011-V-0002.bin"
private noncomputable def vp000000000011_3 : Blocks := edgeBlocks% "full/vectors/000000000011-V-0003.bin"
private noncomputable def vp000000000011_4 : Blocks := edgeBlocks% "full/vectors/000000000011-V-0004.bin"
private noncomputable def vp000000000011_5 : Blocks := edgeBlocks% "full/vectors/000000000011-V-0005.bin"
private noncomputable def vp000000000011_6 : Blocks := edgeBlocks% "full/vectors/000000000011-V-0006.bin"
noncomputable def vp000000000011 : Blocks := (Blocks.join (Blocks.join vp000000000011_0 (Blocks.join vp000000000011_1 vp000000000011_2)) (Blocks.join (Blocks.join vp000000000011_3 vp000000000011_4) (Blocks.join vp000000000011_5 vp000000000011_6)))
private theorem bp0000000000110 : Branch 0 (-5761639/2000000 : ℚ) vp000000000011 := by
  apply branch_left_normalized (c:=vp0000000000110) (k:=0) (m:=417) (by decide +kernel)
  rw [show 2*(-5761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-5761639/1000000 : ℚ) by norm_num]
  exact coverp0000000000110
private noncomputable def ep0000000000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000111-E-0000.bin"
private noncomputable def ep0000000000111_1 : Blocks := edgeBlocks% "full/vectors/0000000000111-E-0001.bin"
private noncomputable def ep0000000000111_2 : Blocks := edgeBlocks% "full/vectors/0000000000111-E-0002.bin"
private noncomputable def ep0000000000111_3 : Blocks := edgeBlocks% "full/vectors/0000000000111-E-0003.bin"
private noncomputable def ep0000000000111_4 : Blocks := edgeBlocks% "full/vectors/0000000000111-E-0004.bin"
private noncomputable def ep0000000000111_5 : Blocks := edgeBlocks% "full/vectors/0000000000111-E-0005.bin"
private noncomputable def ep0000000000111_6 : Blocks := edgeBlocks% "full/vectors/0000000000111-E-0006.bin"
noncomputable def ep0000000000111 : Blocks := (Blocks.join (Blocks.join ep0000000000111_0 (Blocks.join ep0000000000111_1 ep0000000000111_2)) (Blocks.join (Blocks.join ep0000000000111_3 ep0000000000111_4) (Blocks.join ep0000000000111_5 ep0000000000111_6)))
private theorem idp0000000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011.list =
    C ((2:ℤ)^812) * horner X vp0000000000111.list + horner X ep0000000000111.list := by
  exact edge_identity (B := (2:ℤ)^1330) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000111 : Branch 1 (-5761639/2000000 : ℚ) vp000000000011 := by
  apply branch_checked idp0000000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-5761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-6761639/1000000 : ℚ) by norm_num]
  exact coverp0000000000111
theorem coverp000000000011 : Covers (-5761639/2000000 : ℚ) vp000000000011 := join_branches bp0000000000110 bp0000000000111
end NextProof.EdgeFull

