import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000000000111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000111111-V-0000.bin"
noncomputable def vp0000000000111111 : Blocks := vp0000000000111111_0
theorem coverp0000000000111111 : Covers (-7636639/125000 : ℚ) vp0000000000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001111101_0 : Blocks := edgeBlocks% "full/vectors/00000000001111101-V-0000.bin"
noncomputable def vp00000000001111101 : Blocks := vp00000000001111101_0
theorem coverp00000000001111101 : Covers (-7574139/62500 : ℚ) vp00000000001111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001111100_0 : Blocks := edgeBlocks% "full/vectors/00000000001111100-V-0000.bin"
noncomputable def vp00000000001111100 : Blocks := vp00000000001111100_0
theorem coverp00000000001111100 : Covers (-7511639/62500 : ℚ) vp00000000001111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000111110_0 : Blocks := edgeBlocks% "full/vectors/0000000000111110-V-0000.bin"
noncomputable def vp0000000000111110 : Blocks := vp0000000000111110_0
private theorem bp00000000001111100 : Branch 0 (-7511639/125000 : ℚ) vp0000000000111110 := by
  apply branch_left_normalized (c:=vp00000000001111100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-7511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-7511639/62500 : ℚ) by norm_num]
  exact coverp00000000001111100
private noncomputable def ep00000000001111101_0 : Blocks := edgeBlocks% "full/vectors/00000000001111101-E-0000.bin"
noncomputable def ep00000000001111101 : Blocks := ep00000000001111101_0
private theorem idp00000000001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000111110.list =
    C ((2:ℤ)^60) * horner X vp00000000001111101.list + horner X ep00000000001111101.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001111101 : Branch 1 (-7511639/125000 : ℚ) vp0000000000111110 := by
  apply branch_checked idp00000000001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-7511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-7574139/62500 : ℚ) by norm_num]
  exact coverp00000000001111101
theorem coverp0000000000111110 : Covers (-7511639/125000 : ℚ) vp0000000000111110 := join_branches bp00000000001111100 bp00000000001111101
private noncomputable def vp000000000011111_0 : Blocks := edgeBlocks% "full/vectors/000000000011111-V-0000.bin"
noncomputable def vp000000000011111 : Blocks := vp000000000011111_0
private theorem bp0000000000111110 : Branch 0 (-7511639/250000 : ℚ) vp000000000011111 := by
  apply branch_left_normalized (c:=vp0000000000111110) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-7511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-7511639/125000 : ℚ) by norm_num]
  exact coverp0000000000111110
private noncomputable def ep0000000000111111_0 : Blocks := edgeBlocks% "full/vectors/0000000000111111-E-0000.bin"
noncomputable def ep0000000000111111 : Blocks := ep0000000000111111_0
private theorem idp0000000000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011111.list =
    C ((2:ℤ)^106) * horner X vp0000000000111111.list + horner X ep0000000000111111.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000111111 : Branch 1 (-7511639/250000 : ℚ) vp000000000011111 := by
  apply branch_checked idp0000000000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-7511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-7636639/125000 : ℚ) by norm_num]
  exact coverp0000000000111111
theorem coverp000000000011111 : Covers (-7511639/250000 : ℚ) vp000000000011111 := join_branches bp0000000000111110 bp0000000000111111
private noncomputable def vp00000000001111011_0 : Blocks := edgeBlocks% "full/vectors/00000000001111011-V-0000.bin"
noncomputable def vp00000000001111011 : Blocks := vp00000000001111011_0
theorem coverp00000000001111011 : Covers (-7449139/62500 : ℚ) vp00000000001111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001111010_0 : Blocks := edgeBlocks% "full/vectors/00000000001111010-V-0000.bin"
noncomputable def vp00000000001111010 : Blocks := vp00000000001111010_0
theorem coverp00000000001111010 : Covers (-7386639/62500 : ℚ) vp00000000001111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000111101-V-0000.bin"
noncomputable def vp0000000000111101 : Blocks := vp0000000000111101_0
private theorem bp00000000001111010 : Branch 0 (-7386639/125000 : ℚ) vp0000000000111101 := by
  apply branch_left_normalized (c:=vp00000000001111010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-7386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-7386639/62500 : ℚ) by norm_num]
  exact coverp00000000001111010
private noncomputable def ep00000000001111011_0 : Blocks := edgeBlocks% "full/vectors/00000000001111011-E-0000.bin"
noncomputable def ep00000000001111011 : Blocks := ep00000000001111011_0
private theorem idp00000000001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000111101.list =
    C ((2:ℤ)^64) * horner X vp00000000001111011.list + horner X ep00000000001111011.list := by
  exact edge_identity (B := (2:ℤ)^180) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001111011 : Branch 1 (-7386639/125000 : ℚ) vp0000000000111101 := by
  apply branch_checked idp00000000001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-7386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-7449139/62500 : ℚ) by norm_num]
  exact coverp00000000001111011
theorem coverp0000000000111101 : Covers (-7386639/125000 : ℚ) vp0000000000111101 := join_branches bp00000000001111010 bp00000000001111011
private noncomputable def vp00000000001111001_0 : Blocks := edgeBlocks% "full/vectors/00000000001111001-V-0000.bin"
noncomputable def vp00000000001111001 : Blocks := vp00000000001111001_0
theorem coverp00000000001111001 : Covers (-7324139/62500 : ℚ) vp00000000001111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001111000_0 : Blocks := edgeBlocks% "full/vectors/00000000001111000-V-0000.bin"
noncomputable def vp00000000001111000 : Blocks := vp00000000001111000_0
theorem coverp00000000001111000 : Covers (-7261639/62500 : ℚ) vp00000000001111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000111100_0 : Blocks := edgeBlocks% "full/vectors/0000000000111100-V-0000.bin"
noncomputable def vp0000000000111100 : Blocks := vp0000000000111100_0
private theorem bp00000000001111000 : Branch 0 (-7261639/125000 : ℚ) vp0000000000111100 := by
  apply branch_left_normalized (c:=vp00000000001111000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-7261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-7261639/62500 : ℚ) by norm_num]
  exact coverp00000000001111000
private noncomputable def ep00000000001111001_0 : Blocks := edgeBlocks% "full/vectors/00000000001111001-E-0000.bin"
noncomputable def ep00000000001111001 : Blocks := ep00000000001111001_0
private theorem idp00000000001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000111100.list =
    C ((2:ℤ)^66) * horner X vp00000000001111001.list + horner X ep00000000001111001.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001111001 : Branch 1 (-7261639/125000 : ℚ) vp0000000000111100 := by
  apply branch_checked idp00000000001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-7261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-7324139/62500 : ℚ) by norm_num]
  exact coverp00000000001111001
theorem coverp0000000000111100 : Covers (-7261639/125000 : ℚ) vp0000000000111100 := join_branches bp00000000001111000 bp00000000001111001
private noncomputable def vp000000000011110_0 : Blocks := edgeBlocks% "full/vectors/000000000011110-V-0000.bin"
noncomputable def vp000000000011110 : Blocks := vp000000000011110_0
private theorem bp0000000000111100 : Branch 0 (-7261639/250000 : ℚ) vp000000000011110 := by
  apply branch_left_normalized (c:=vp0000000000111100) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-7261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-7261639/125000 : ℚ) by norm_num]
  exact coverp0000000000111100
private noncomputable def ep0000000000111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000111101-E-0000.bin"
noncomputable def ep0000000000111101 : Blocks := ep0000000000111101_0
private theorem idp0000000000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011110.list =
    C ((2:ℤ)^114) * horner X vp0000000000111101.list + horner X ep0000000000111101.list := by
  exact edge_identity (B := (2:ℤ)^255) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000111101 : Branch 1 (-7261639/250000 : ℚ) vp000000000011110 := by
  apply branch_checked idp0000000000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-7261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-7386639/125000 : ℚ) by norm_num]
  exact coverp0000000000111101
theorem coverp000000000011110 : Covers (-7261639/250000 : ℚ) vp000000000011110 := join_branches bp0000000000111100 bp0000000000111101
private noncomputable def vp00000000001111_0 : Blocks := edgeBlocks% "full/vectors/00000000001111-V-0000.bin"
private noncomputable def vp00000000001111_1 : Blocks := edgeBlocks% "full/vectors/00000000001111-V-0001.bin"
noncomputable def vp00000000001111 : Blocks := (Blocks.join vp00000000001111_0 vp00000000001111_1)
private theorem bp000000000011110 : Branch 0 (-7261639/500000 : ℚ) vp00000000001111 := by
  apply branch_left_normalized (c:=vp000000000011110) (k:=0) (m:=109) (by decide +kernel)
  rw [show 2*(-7261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-7261639/250000 : ℚ) by norm_num]
  exact coverp000000000011110
private noncomputable def ep000000000011111_0 : Blocks := edgeBlocks% "full/vectors/000000000011111-E-0000.bin"
private noncomputable def ep000000000011111_1 : Blocks := edgeBlocks% "full/vectors/000000000011111-E-0001.bin"
noncomputable def ep000000000011111 : Blocks := (Blocks.join ep000000000011111_0 ep000000000011111_1)
private theorem idp000000000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001111.list =
    C ((2:ℤ)^207) * horner X vp000000000011111.list + horner X ep000000000011111.list := by
  exact edge_identity (B := (2:ℤ)^392) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011111 : Branch 1 (-7261639/500000 : ℚ) vp00000000001111 := by
  apply branch_checked idp000000000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-7261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-7511639/250000 : ℚ) by norm_num]
  exact coverp000000000011111
theorem coverp00000000001111 : Covers (-7261639/500000 : ℚ) vp00000000001111 := join_branches bp000000000011110 bp000000000011111
private noncomputable def vp000000000011101111_0 : Blocks := edgeBlocks% "full/vectors/000000000011101111-V-0000.bin"
noncomputable def vp000000000011101111 : Blocks := vp000000000011101111_0
theorem coverp000000000011101111 : Covers (-7230389/31250 : ℚ) vp000000000011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011101110_0 : Blocks := edgeBlocks% "full/vectors/000000000011101110-V-0000.bin"
noncomputable def vp000000000011101110 : Blocks := vp000000000011101110_0
theorem coverp000000000011101110 : Covers (-7199139/31250 : ℚ) vp000000000011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001110111_0 : Blocks := edgeBlocks% "full/vectors/00000000001110111-V-0000.bin"
noncomputable def vp00000000001110111 : Blocks := vp00000000001110111_0
private theorem bp000000000011101110 : Branch 0 (-7199139/62500 : ℚ) vp00000000001110111 := by
  apply branch_left_normalized (c:=vp000000000011101110) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-7199139/62500 : ℚ) - ((0:ℤ):ℚ) = (-7199139/31250 : ℚ) by norm_num]
  exact coverp000000000011101110
private noncomputable def ep000000000011101111_0 : Blocks := edgeBlocks% "full/vectors/000000000011101111-E-0000.bin"
noncomputable def ep000000000011101111 : Blocks := ep000000000011101111_0
private theorem idp000000000011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001110111.list =
    C ((2:ℤ)^45) * horner X vp000000000011101111.list + horner X ep000000000011101111.list := by
  exact edge_identity (B := (2:ℤ)^160) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011101111 : Branch 1 (-7199139/62500 : ℚ) vp00000000001110111 := by
  apply branch_checked idp000000000011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-7199139/62500 : ℚ) - ((1:ℤ):ℚ) = (-7230389/31250 : ℚ) by norm_num]
  exact coverp000000000011101111
theorem coverp00000000001110111 : Covers (-7199139/62500 : ℚ) vp00000000001110111 := join_branches bp000000000011101110 bp000000000011101111
private noncomputable def vp0000000000111011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000111011011-V-0000.bin"
noncomputable def vp0000000000111011011 : Blocks := vp0000000000111011011_0
theorem coverp0000000000111011011 : Covers (-7183514/15625 : ℚ) vp0000000000111011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000111011010_0 : Blocks := edgeBlocks% "full/vectors/0000000000111011010-V-0000.bin"
noncomputable def vp0000000000111011010 : Blocks := vp0000000000111011010_0
theorem coverp0000000000111011010 : Covers (-7167889/15625 : ℚ) vp0000000000111011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011101101_0 : Blocks := edgeBlocks% "full/vectors/000000000011101101-V-0000.bin"
noncomputable def vp000000000011101101 : Blocks := vp000000000011101101_0
private theorem bp0000000000111011010 : Branch 0 (-7167889/31250 : ℚ) vp000000000011101101 := by
  apply branch_left_normalized (c:=vp0000000000111011010) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-7167889/31250 : ℚ) - ((0:ℤ):ℚ) = (-7167889/15625 : ℚ) by norm_num]
  exact coverp0000000000111011010
private noncomputable def ep0000000000111011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000111011011-E-0000.bin"
noncomputable def ep0000000000111011011 : Blocks := ep0000000000111011011_0
private theorem idp0000000000111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011101101.list =
    C ((2:ℤ)^30) * horner X vp0000000000111011011.list + horner X ep0000000000111011011.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000111011011 : Branch 1 (-7167889/31250 : ℚ) vp000000000011101101 := by
  apply branch_checked idp0000000000111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-7167889/31250 : ℚ) - ((1:ℤ):ℚ) = (-7183514/15625 : ℚ) by norm_num]
  exact coverp0000000000111011011
theorem coverp000000000011101101 : Covers (-7167889/31250 : ℚ) vp000000000011101101 := join_branches bp0000000000111011010 bp0000000000111011011
private noncomputable def vp0000000000111011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000111011001-V-0000.bin"
noncomputable def vp0000000000111011001 : Blocks := vp0000000000111011001_0
theorem coverp0000000000111011001 : Covers (-7152264/15625 : ℚ) vp0000000000111011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000111011000_0 : Blocks := edgeBlocks% "full/vectors/0000000000111011000-V-0000.bin"
noncomputable def vp0000000000111011000 : Blocks := vp0000000000111011000_0
theorem coverp0000000000111011000 : Covers (-7136639/15625 : ℚ) vp0000000000111011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011101100_0 : Blocks := edgeBlocks% "full/vectors/000000000011101100-V-0000.bin"
noncomputable def vp000000000011101100 : Blocks := vp000000000011101100_0
private theorem bp0000000000111011000 : Branch 0 (-7136639/31250 : ℚ) vp000000000011101100 := by
  apply branch_left_normalized (c:=vp0000000000111011000) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-7136639/31250 : ℚ) - ((0:ℤ):ℚ) = (-7136639/15625 : ℚ) by norm_num]
  exact coverp0000000000111011000
private noncomputable def ep0000000000111011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000111011001-E-0000.bin"
noncomputable def ep0000000000111011001 : Blocks := ep0000000000111011001_0
private theorem idp0000000000111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011101100.list =
    C ((2:ℤ)^29) * horner X vp0000000000111011001.list + horner X ep0000000000111011001.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000111011001 : Branch 1 (-7136639/31250 : ℚ) vp000000000011101100 := by
  apply branch_checked idp0000000000111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-7136639/31250 : ℚ) - ((1:ℤ):ℚ) = (-7152264/15625 : ℚ) by norm_num]
  exact coverp0000000000111011001
theorem coverp000000000011101100 : Covers (-7136639/31250 : ℚ) vp000000000011101100 := join_branches bp0000000000111011000 bp0000000000111011001
private noncomputable def vp00000000001110110_0 : Blocks := edgeBlocks% "full/vectors/00000000001110110-V-0000.bin"
noncomputable def vp00000000001110110 : Blocks := vp00000000001110110_0
private theorem bp000000000011101100 : Branch 0 (-7136639/62500 : ℚ) vp00000000001110110 := by
  apply branch_left_normalized (c:=vp000000000011101100) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-7136639/62500 : ℚ) - ((0:ℤ):ℚ) = (-7136639/31250 : ℚ) by norm_num]
  exact coverp000000000011101100
private noncomputable def ep000000000011101101_0 : Blocks := edgeBlocks% "full/vectors/000000000011101101-E-0000.bin"
noncomputable def ep000000000011101101 : Blocks := ep000000000011101101_0
private theorem idp000000000011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001110110.list =
    C ((2:ℤ)^43) * horner X vp000000000011101101.list + horner X ep000000000011101101.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011101101 : Branch 1 (-7136639/62500 : ℚ) vp00000000001110110 := by
  apply branch_checked idp000000000011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-7136639/62500 : ℚ) - ((1:ℤ):ℚ) = (-7167889/31250 : ℚ) by norm_num]
  exact coverp000000000011101101
theorem coverp00000000001110110 : Covers (-7136639/62500 : ℚ) vp00000000001110110 := join_branches bp000000000011101100 bp000000000011101101
private noncomputable def vp0000000000111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000111011-V-0000.bin"
noncomputable def vp0000000000111011 : Blocks := vp0000000000111011_0
private theorem bp00000000001110110 : Branch 0 (-7136639/125000 : ℚ) vp0000000000111011 := by
  apply branch_left_normalized (c:=vp00000000001110110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-7136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-7136639/62500 : ℚ) by norm_num]
  exact coverp00000000001110110
private noncomputable def ep00000000001110111_0 : Blocks := edgeBlocks% "full/vectors/00000000001110111-E-0000.bin"
noncomputable def ep00000000001110111 : Blocks := ep00000000001110111_0
private theorem idp00000000001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000111011.list =
    C ((2:ℤ)^68) * horner X vp00000000001110111.list + horner X ep00000000001110111.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001110111 : Branch 1 (-7136639/125000 : ℚ) vp0000000000111011 := by
  apply branch_checked idp00000000001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-7136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-7199139/62500 : ℚ) by norm_num]
  exact coverp00000000001110111
theorem coverp0000000000111011 : Covers (-7136639/125000 : ℚ) vp0000000000111011 := join_branches bp00000000001110110 bp00000000001110111
private noncomputable def vp000000000011101011_0 : Blocks := edgeBlocks% "full/vectors/000000000011101011-V-0000.bin"
noncomputable def vp000000000011101011 : Blocks := vp000000000011101011_0
theorem coverp000000000011101011 : Covers (-7105389/31250 : ℚ) vp000000000011101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011101010_0 : Blocks := edgeBlocks% "full/vectors/000000000011101010-V-0000.bin"
noncomputable def vp000000000011101010 : Blocks := vp000000000011101010_0
theorem coverp000000000011101010 : Covers (-7074139/31250 : ℚ) vp000000000011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001110101_0 : Blocks := edgeBlocks% "full/vectors/00000000001110101-V-0000.bin"
noncomputable def vp00000000001110101 : Blocks := vp00000000001110101_0
private theorem bp000000000011101010 : Branch 0 (-7074139/62500 : ℚ) vp00000000001110101 := by
  apply branch_left_normalized (c:=vp000000000011101010) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-7074139/62500 : ℚ) - ((0:ℤ):ℚ) = (-7074139/31250 : ℚ) by norm_num]
  exact coverp000000000011101010
private noncomputable def ep000000000011101011_0 : Blocks := edgeBlocks% "full/vectors/000000000011101011-E-0000.bin"
noncomputable def ep000000000011101011 : Blocks := ep000000000011101011_0
private theorem idp000000000011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001110101.list =
    C ((2:ℤ)^43) * horner X vp000000000011101011.list + horner X ep000000000011101011.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011101011 : Branch 1 (-7074139/62500 : ℚ) vp00000000001110101 := by
  apply branch_checked idp000000000011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-7074139/62500 : ℚ) - ((1:ℤ):ℚ) = (-7105389/31250 : ℚ) by norm_num]
  exact coverp000000000011101011
theorem coverp00000000001110101 : Covers (-7074139/62500 : ℚ) vp00000000001110101 := join_branches bp000000000011101010 bp000000000011101011
private noncomputable def vp000000000011101001_0 : Blocks := edgeBlocks% "full/vectors/000000000011101001-V-0000.bin"
noncomputable def vp000000000011101001 : Blocks := vp000000000011101001_0
theorem coverp000000000011101001 : Covers (-7042889/31250 : ℚ) vp000000000011101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011101000_0 : Blocks := edgeBlocks% "full/vectors/000000000011101000-V-0000.bin"
noncomputable def vp000000000011101000 : Blocks := vp000000000011101000_0
theorem coverp000000000011101000 : Covers (-7011639/31250 : ℚ) vp000000000011101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001110100_0 : Blocks := edgeBlocks% "full/vectors/00000000001110100-V-0000.bin"
noncomputable def vp00000000001110100 : Blocks := vp00000000001110100_0
private theorem bp000000000011101000 : Branch 0 (-7011639/62500 : ℚ) vp00000000001110100 := by
  apply branch_left_normalized (c:=vp000000000011101000) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-7011639/62500 : ℚ) - ((0:ℤ):ℚ) = (-7011639/31250 : ℚ) by norm_num]
  exact coverp000000000011101000
private noncomputable def ep000000000011101001_0 : Blocks := edgeBlocks% "full/vectors/000000000011101001-E-0000.bin"
noncomputable def ep000000000011101001 : Blocks := ep000000000011101001_0
private theorem idp000000000011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001110100.list =
    C ((2:ℤ)^43) * horner X vp000000000011101001.list + horner X ep000000000011101001.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011101001 : Branch 1 (-7011639/62500 : ℚ) vp00000000001110100 := by
  apply branch_checked idp000000000011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-7011639/62500 : ℚ) - ((1:ℤ):ℚ) = (-7042889/31250 : ℚ) by norm_num]
  exact coverp000000000011101001
theorem coverp00000000001110100 : Covers (-7011639/62500 : ℚ) vp00000000001110100 := join_branches bp000000000011101000 bp000000000011101001
private noncomputable def vp0000000000111010_0 : Blocks := edgeBlocks% "full/vectors/0000000000111010-V-0000.bin"
noncomputable def vp0000000000111010 : Blocks := vp0000000000111010_0
private theorem bp00000000001110100 : Branch 0 (-7011639/125000 : ℚ) vp0000000000111010 := by
  apply branch_left_normalized (c:=vp00000000001110100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-7011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-7011639/62500 : ℚ) by norm_num]
  exact coverp00000000001110100
private noncomputable def ep00000000001110101_0 : Blocks := edgeBlocks% "full/vectors/00000000001110101-E-0000.bin"
noncomputable def ep00000000001110101 : Blocks := ep00000000001110101_0
private theorem idp00000000001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000111010.list =
    C ((2:ℤ)^68) * horner X vp00000000001110101.list + horner X ep00000000001110101.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001110101 : Branch 1 (-7011639/125000 : ℚ) vp0000000000111010 := by
  apply branch_checked idp00000000001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-7011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-7074139/62500 : ℚ) by norm_num]
  exact coverp00000000001110101
theorem coverp0000000000111010 : Covers (-7011639/125000 : ℚ) vp0000000000111010 := join_branches bp00000000001110100 bp00000000001110101
private noncomputable def vp000000000011101_0 : Blocks := edgeBlocks% "full/vectors/000000000011101-V-0000.bin"
noncomputable def vp000000000011101 : Blocks := vp000000000011101_0
private theorem bp0000000000111010 : Branch 0 (-7011639/250000 : ℚ) vp000000000011101 := by
  apply branch_left_normalized (c:=vp0000000000111010) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-7011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-7011639/125000 : ℚ) by norm_num]
  exact coverp0000000000111010
private noncomputable def ep0000000000111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000111011-E-0000.bin"
noncomputable def ep0000000000111011 : Blocks := ep0000000000111011_0
private theorem idp0000000000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011101.list =
    C ((2:ℤ)^115) * horner X vp0000000000111011.list + horner X ep0000000000111011.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000111011 : Branch 1 (-7011639/250000 : ℚ) vp000000000011101 := by
  apply branch_checked idp0000000000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-7011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-7136639/125000 : ℚ) by norm_num]
  exact coverp0000000000111011
theorem coverp000000000011101 : Covers (-7011639/250000 : ℚ) vp000000000011101 := join_branches bp0000000000111010 bp0000000000111011
private noncomputable def vp0000000000111001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000111001111-V-0000.bin"
noncomputable def vp0000000000111001111 : Blocks := vp0000000000111001111_0
theorem coverp0000000000111001111 : Covers (-6996014/15625 : ℚ) vp0000000000111001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000111001110_0 : Blocks := edgeBlocks% "full/vectors/0000000000111001110-V-0000.bin"
noncomputable def vp0000000000111001110 : Blocks := vp0000000000111001110_0
theorem coverp0000000000111001110 : Covers (-6980389/15625 : ℚ) vp0000000000111001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011100111_0 : Blocks := edgeBlocks% "full/vectors/000000000011100111-V-0000.bin"
noncomputable def vp000000000011100111 : Blocks := vp000000000011100111_0
private theorem bp0000000000111001110 : Branch 0 (-6980389/31250 : ℚ) vp000000000011100111 := by
  apply branch_left_normalized (c:=vp0000000000111001110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-6980389/31250 : ℚ) - ((0:ℤ):ℚ) = (-6980389/15625 : ℚ) by norm_num]
  exact coverp0000000000111001110
private noncomputable def ep0000000000111001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000111001111-E-0000.bin"
noncomputable def ep0000000000111001111 : Blocks := ep0000000000111001111_0
private theorem idp0000000000111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011100111.list =
    C ((2:ℤ)^30) * horner X vp0000000000111001111.list + horner X ep0000000000111001111.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000111001111 : Branch 1 (-6980389/31250 : ℚ) vp000000000011100111 := by
  apply branch_checked idp0000000000111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-6980389/31250 : ℚ) - ((1:ℤ):ℚ) = (-6996014/15625 : ℚ) by norm_num]
  exact coverp0000000000111001111
theorem coverp000000000011100111 : Covers (-6980389/31250 : ℚ) vp000000000011100111 := join_branches bp0000000000111001110 bp0000000000111001111
private noncomputable def vp000000000011100110_0 : Blocks := edgeBlocks% "full/vectors/000000000011100110-V-0000.bin"
noncomputable def vp000000000011100110 : Blocks := vp000000000011100110_0
theorem coverp000000000011100110 : Covers (-6949139/31250 : ℚ) vp000000000011100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001110011_0 : Blocks := edgeBlocks% "full/vectors/00000000001110011-V-0000.bin"
noncomputable def vp00000000001110011 : Blocks := vp00000000001110011_0
private theorem bp000000000011100110 : Branch 0 (-6949139/62500 : ℚ) vp00000000001110011 := by
  apply branch_left_normalized (c:=vp000000000011100110) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-6949139/62500 : ℚ) - ((0:ℤ):ℚ) = (-6949139/31250 : ℚ) by norm_num]
  exact coverp000000000011100110
private noncomputable def ep000000000011100111_0 : Blocks := edgeBlocks% "full/vectors/000000000011100111-E-0000.bin"
noncomputable def ep000000000011100111 : Blocks := ep000000000011100111_0
private theorem idp000000000011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001110011.list =
    C ((2:ℤ)^43) * horner X vp000000000011100111.list + horner X ep000000000011100111.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011100111 : Branch 1 (-6949139/62500 : ℚ) vp00000000001110011 := by
  apply branch_checked idp000000000011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-6949139/62500 : ℚ) - ((1:ℤ):ℚ) = (-6980389/31250 : ℚ) by norm_num]
  exact coverp000000000011100111
theorem coverp00000000001110011 : Covers (-6949139/62500 : ℚ) vp00000000001110011 := join_branches bp000000000011100110 bp000000000011100111
private noncomputable def vp0000000000111001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000111001011-V-0000.bin"
noncomputable def vp0000000000111001011 : Blocks := vp0000000000111001011_0
theorem coverp0000000000111001011 : Covers (-6933514/15625 : ℚ) vp0000000000111001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000111001010_0 : Blocks := edgeBlocks% "full/vectors/0000000000111001010-V-0000.bin"
noncomputable def vp0000000000111001010 : Blocks := vp0000000000111001010_0
theorem coverp0000000000111001010 : Covers (-6917889/15625 : ℚ) vp0000000000111001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011100101_0 : Blocks := edgeBlocks% "full/vectors/000000000011100101-V-0000.bin"
noncomputable def vp000000000011100101 : Blocks := vp000000000011100101_0
private theorem bp0000000000111001010 : Branch 0 (-6917889/31250 : ℚ) vp000000000011100101 := by
  apply branch_left_normalized (c:=vp0000000000111001010) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-6917889/31250 : ℚ) - ((0:ℤ):ℚ) = (-6917889/15625 : ℚ) by norm_num]
  exact coverp0000000000111001010
private noncomputable def ep0000000000111001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000111001011-E-0000.bin"
noncomputable def ep0000000000111001011 : Blocks := ep0000000000111001011_0
private theorem idp0000000000111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011100101.list =
    C ((2:ℤ)^30) * horner X vp0000000000111001011.list + horner X ep0000000000111001011.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000111001011 : Branch 1 (-6917889/31250 : ℚ) vp000000000011100101 := by
  apply branch_checked idp0000000000111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-6917889/31250 : ℚ) - ((1:ℤ):ℚ) = (-6933514/15625 : ℚ) by norm_num]
  exact coverp0000000000111001011
theorem coverp000000000011100101 : Covers (-6917889/31250 : ℚ) vp000000000011100101 := join_branches bp0000000000111001010 bp0000000000111001011
private noncomputable def vp000000000011100100_0 : Blocks := edgeBlocks% "full/vectors/000000000011100100-V-0000.bin"
noncomputable def vp000000000011100100 : Blocks := vp000000000011100100_0
theorem coverp000000000011100100 : Covers (-6886639/31250 : ℚ) vp000000000011100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001110010_0 : Blocks := edgeBlocks% "full/vectors/00000000001110010-V-0000.bin"
noncomputable def vp00000000001110010 : Blocks := vp00000000001110010_0
private theorem bp000000000011100100 : Branch 0 (-6886639/62500 : ℚ) vp00000000001110010 := by
  apply branch_left_normalized (c:=vp000000000011100100) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-6886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-6886639/31250 : ℚ) by norm_num]
  exact coverp000000000011100100
private noncomputable def ep000000000011100101_0 : Blocks := edgeBlocks% "full/vectors/000000000011100101-E-0000.bin"
noncomputable def ep000000000011100101 : Blocks := ep000000000011100101_0
private theorem idp000000000011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001110010.list =
    C ((2:ℤ)^44) * horner X vp000000000011100101.list + horner X ep000000000011100101.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011100101 : Branch 1 (-6886639/62500 : ℚ) vp00000000001110010 := by
  apply branch_checked idp000000000011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-6886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-6917889/31250 : ℚ) by norm_num]
  exact coverp000000000011100101
theorem coverp00000000001110010 : Covers (-6886639/62500 : ℚ) vp00000000001110010 := join_branches bp000000000011100100 bp000000000011100101
private noncomputable def vp0000000000111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000111001-V-0000.bin"
noncomputable def vp0000000000111001 : Blocks := vp0000000000111001_0
private theorem bp00000000001110010 : Branch 0 (-6886639/125000 : ℚ) vp0000000000111001 := by
  apply branch_left_normalized (c:=vp00000000001110010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-6886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-6886639/62500 : ℚ) by norm_num]
  exact coverp00000000001110010
private noncomputable def ep00000000001110011_0 : Blocks := edgeBlocks% "full/vectors/00000000001110011-E-0000.bin"
noncomputable def ep00000000001110011 : Blocks := ep00000000001110011_0
private theorem idp00000000001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000111001.list =
    C ((2:ℤ)^69) * horner X vp00000000001110011.list + horner X ep00000000001110011.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001110011 : Branch 1 (-6886639/125000 : ℚ) vp0000000000111001 := by
  apply branch_checked idp00000000001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-6886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-6949139/62500 : ℚ) by norm_num]
  exact coverp00000000001110011
theorem coverp0000000000111001 : Covers (-6886639/125000 : ℚ) vp0000000000111001 := join_branches bp00000000001110010 bp00000000001110011
private noncomputable def vp0000000000111000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000111000111-V-0000.bin"
noncomputable def vp0000000000111000111 : Blocks := vp0000000000111000111_0
theorem coverp0000000000111000111 : Covers (-6871014/15625 : ℚ) vp0000000000111000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000111000110_0 : Blocks := edgeBlocks% "full/vectors/0000000000111000110-V-0000.bin"
noncomputable def vp0000000000111000110 : Blocks := vp0000000000111000110_0
theorem coverp0000000000111000110 : Covers (-6855389/15625 : ℚ) vp0000000000111000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011100011_0 : Blocks := edgeBlocks% "full/vectors/000000000011100011-V-0000.bin"
noncomputable def vp000000000011100011 : Blocks := vp000000000011100011_0
private theorem bp0000000000111000110 : Branch 0 (-6855389/31250 : ℚ) vp000000000011100011 := by
  apply branch_left_normalized (c:=vp0000000000111000110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-6855389/31250 : ℚ) - ((0:ℤ):ℚ) = (-6855389/15625 : ℚ) by norm_num]
  exact coverp0000000000111000110
private noncomputable def ep0000000000111000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000111000111-E-0000.bin"
noncomputable def ep0000000000111000111 : Blocks := ep0000000000111000111_0
private theorem idp0000000000111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011100011.list =
    C ((2:ℤ)^30) * horner X vp0000000000111000111.list + horner X ep0000000000111000111.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000111000111 : Branch 1 (-6855389/31250 : ℚ) vp000000000011100011 := by
  apply branch_checked idp0000000000111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-6855389/31250 : ℚ) - ((1:ℤ):ℚ) = (-6871014/15625 : ℚ) by norm_num]
  exact coverp0000000000111000111
theorem coverp000000000011100011 : Covers (-6855389/31250 : ℚ) vp000000000011100011 := join_branches bp0000000000111000110 bp0000000000111000111
private noncomputable def vp00000000001110001011_0 : Blocks := edgeBlocks% "full/vectors/00000000001110001011-V-0000.bin"
noncomputable def vp00000000001110001011 : Blocks := vp00000000001110001011_0
theorem coverp00000000001110001011 : Covers (-13695153/15625 : ℚ) vp00000000001110001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001110001010_0 : Blocks := edgeBlocks% "full/vectors/00000000001110001010-V-0000.bin"
noncomputable def vp00000000001110001010 : Blocks := vp00000000001110001010_0
theorem coverp00000000001110001010 : Covers (-13679528/15625 : ℚ) vp00000000001110001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000111000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000111000101-V-0000.bin"
noncomputable def vp0000000000111000101 : Blocks := vp0000000000111000101_0
private theorem bp00000000001110001010 : Branch 0 (-6839764/15625 : ℚ) vp0000000000111000101 := by
  apply branch_left_normalized (c:=vp00000000001110001010) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-6839764/15625 : ℚ) - ((0:ℤ):ℚ) = (-13679528/15625 : ℚ) by norm_num]
  exact coverp00000000001110001010
private noncomputable def ep00000000001110001011_0 : Blocks := edgeBlocks% "full/vectors/00000000001110001011-E-0000.bin"
noncomputable def ep00000000001110001011 : Blocks := ep00000000001110001011_0
private theorem idp00000000001110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000111000101.list =
    C ((2:ℤ)^20) * horner X vp00000000001110001011.list + horner X ep00000000001110001011.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001110001011 : Branch 1 (-6839764/15625 : ℚ) vp0000000000111000101 := by
  apply branch_checked idp00000000001110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-6839764/15625 : ℚ) - ((1:ℤ):ℚ) = (-13695153/15625 : ℚ) by norm_num]
  exact coverp00000000001110001011
theorem coverp0000000000111000101 : Covers (-6839764/15625 : ℚ) vp0000000000111000101 := join_branches bp00000000001110001010 bp00000000001110001011
private noncomputable def vp0000000000111000100_0 : Blocks := edgeBlocks% "full/vectors/0000000000111000100-V-0000.bin"
noncomputable def vp0000000000111000100 : Blocks := vp0000000000111000100_0
theorem coverp0000000000111000100 : Covers (-6824139/15625 : ℚ) vp0000000000111000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011100010_0 : Blocks := edgeBlocks% "full/vectors/000000000011100010-V-0000.bin"
noncomputable def vp000000000011100010 : Blocks := vp000000000011100010_0
private theorem bp0000000000111000100 : Branch 0 (-6824139/31250 : ℚ) vp000000000011100010 := by
  apply branch_left_normalized (c:=vp0000000000111000100) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-6824139/31250 : ℚ) - ((0:ℤ):ℚ) = (-6824139/15625 : ℚ) by norm_num]
  exact coverp0000000000111000100
private noncomputable def ep0000000000111000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000111000101-E-0000.bin"
noncomputable def ep0000000000111000101 : Blocks := ep0000000000111000101_0
private theorem idp0000000000111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011100010.list =
    C ((2:ℤ)^29) * horner X vp0000000000111000101.list + horner X ep0000000000111000101.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000111000101 : Branch 1 (-6824139/31250 : ℚ) vp000000000011100010 := by
  apply branch_checked idp0000000000111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-6824139/31250 : ℚ) - ((1:ℤ):ℚ) = (-6839764/15625 : ℚ) by norm_num]
  exact coverp0000000000111000101
theorem coverp000000000011100010 : Covers (-6824139/31250 : ℚ) vp000000000011100010 := join_branches bp0000000000111000100 bp0000000000111000101
private noncomputable def vp00000000001110001_0 : Blocks := edgeBlocks% "full/vectors/00000000001110001-V-0000.bin"
noncomputable def vp00000000001110001 : Blocks := vp00000000001110001_0
private theorem bp000000000011100010 : Branch 0 (-6824139/62500 : ℚ) vp00000000001110001 := by
  apply branch_left_normalized (c:=vp000000000011100010) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-6824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-6824139/31250 : ℚ) by norm_num]
  exact coverp000000000011100010
private noncomputable def ep000000000011100011_0 : Blocks := edgeBlocks% "full/vectors/000000000011100011-E-0000.bin"
noncomputable def ep000000000011100011 : Blocks := ep000000000011100011_0
private theorem idp000000000011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001110001.list =
    C ((2:ℤ)^42) * horner X vp000000000011100011.list + horner X ep000000000011100011.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011100011 : Branch 1 (-6824139/62500 : ℚ) vp00000000001110001 := by
  apply branch_checked idp000000000011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-6824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-6855389/31250 : ℚ) by norm_num]
  exact coverp000000000011100011
theorem coverp00000000001110001 : Covers (-6824139/62500 : ℚ) vp00000000001110001 := join_branches bp000000000011100010 bp000000000011100011
private noncomputable def vp000000000011100001_0 : Blocks := edgeBlocks% "full/vectors/000000000011100001-V-0000.bin"
noncomputable def vp000000000011100001 : Blocks := vp000000000011100001_0
theorem coverp000000000011100001 : Covers (-6792889/31250 : ℚ) vp000000000011100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000011100000_0 : Blocks := edgeBlocks% "full/vectors/000000000011100000-V-0000.bin"
noncomputable def vp000000000011100000 : Blocks := vp000000000011100000_0
theorem coverp000000000011100000 : Covers (-6761639/31250 : ℚ) vp000000000011100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001110000_0 : Blocks := edgeBlocks% "full/vectors/00000000001110000-V-0000.bin"
noncomputable def vp00000000001110000 : Blocks := vp00000000001110000_0
private theorem bp000000000011100000 : Branch 0 (-6761639/62500 : ℚ) vp00000000001110000 := by
  apply branch_left_normalized (c:=vp000000000011100000) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-6761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-6761639/31250 : ℚ) by norm_num]
  exact coverp000000000011100000
private noncomputable def ep000000000011100001_0 : Blocks := edgeBlocks% "full/vectors/000000000011100001-E-0000.bin"
noncomputable def ep000000000011100001 : Blocks := ep000000000011100001_0
private theorem idp000000000011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001110000.list =
    C ((2:ℤ)^41) * horner X vp000000000011100001.list + horner X ep000000000011100001.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011100001 : Branch 1 (-6761639/62500 : ℚ) vp00000000001110000 := by
  apply branch_checked idp000000000011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-6761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-6792889/31250 : ℚ) by norm_num]
  exact coverp000000000011100001
theorem coverp00000000001110000 : Covers (-6761639/62500 : ℚ) vp00000000001110000 := join_branches bp000000000011100000 bp000000000011100001
private noncomputable def vp0000000000111000_0 : Blocks := edgeBlocks% "full/vectors/0000000000111000-V-0000.bin"
noncomputable def vp0000000000111000 : Blocks := vp0000000000111000_0
private theorem bp00000000001110000 : Branch 0 (-6761639/125000 : ℚ) vp0000000000111000 := by
  apply branch_left_normalized (c:=vp00000000001110000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-6761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-6761639/62500 : ℚ) by norm_num]
  exact coverp00000000001110000
private noncomputable def ep00000000001110001_0 : Blocks := edgeBlocks% "full/vectors/00000000001110001-E-0000.bin"
noncomputable def ep00000000001110001 : Blocks := ep00000000001110001_0
private theorem idp00000000001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000111000.list =
    C ((2:ℤ)^67) * horner X vp00000000001110001.list + horner X ep00000000001110001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001110001 : Branch 1 (-6761639/125000 : ℚ) vp0000000000111000 := by
  apply branch_checked idp00000000001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-6761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-6824139/62500 : ℚ) by norm_num]
  exact coverp00000000001110001
theorem coverp0000000000111000 : Covers (-6761639/125000 : ℚ) vp0000000000111000 := join_branches bp00000000001110000 bp00000000001110001
private noncomputable def vp000000000011100_0 : Blocks := edgeBlocks% "full/vectors/000000000011100-V-0000.bin"
noncomputable def vp000000000011100 : Blocks := vp000000000011100_0
private theorem bp0000000000111000 : Branch 0 (-6761639/250000 : ℚ) vp000000000011100 := by
  apply branch_left_normalized (c:=vp0000000000111000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-6761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-6761639/125000 : ℚ) by norm_num]
  exact coverp0000000000111000
private noncomputable def ep0000000000111001_0 : Blocks := edgeBlocks% "full/vectors/0000000000111001-E-0000.bin"
noncomputable def ep0000000000111001 : Blocks := ep0000000000111001_0
private theorem idp0000000000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000011100.list =
    C ((2:ℤ)^114) * horner X vp0000000000111001.list + horner X ep0000000000111001.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000111001 : Branch 1 (-6761639/250000 : ℚ) vp000000000011100 := by
  apply branch_checked idp0000000000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-6761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-6886639/125000 : ℚ) by norm_num]
  exact coverp0000000000111001
theorem coverp000000000011100 : Covers (-6761639/250000 : ℚ) vp000000000011100 := join_branches bp0000000000111000 bp0000000000111001
private noncomputable def vp00000000001110_0 : Blocks := edgeBlocks% "full/vectors/00000000001110-V-0000.bin"
private noncomputable def vp00000000001110_1 : Blocks := edgeBlocks% "full/vectors/00000000001110-V-0001.bin"
noncomputable def vp00000000001110 : Blocks := (Blocks.join vp00000000001110_0 vp00000000001110_1)
private theorem bp000000000011100 : Branch 0 (-6761639/500000 : ℚ) vp00000000001110 := by
  apply branch_left_normalized (c:=vp000000000011100) (k:=0) (m:=113) (by decide +kernel)
  rw [show 2*(-6761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-6761639/250000 : ℚ) by norm_num]
  exact coverp000000000011100
private noncomputable def ep000000000011101_0 : Blocks := edgeBlocks% "full/vectors/000000000011101-E-0000.bin"
private noncomputable def ep000000000011101_1 : Blocks := edgeBlocks% "full/vectors/000000000011101-E-0001.bin"
noncomputable def ep000000000011101 : Blocks := (Blocks.join ep000000000011101_0 ep000000000011101_1)
private theorem idp000000000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001110.list =
    C ((2:ℤ)^207) * horner X vp000000000011101.list + horner X ep000000000011101.list := by
  exact edge_identity (B := (2:ℤ)^405) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000011101 : Branch 1 (-6761639/500000 : ℚ) vp00000000001110 := by
  apply branch_checked idp000000000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-6761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-7011639/250000 : ℚ) by norm_num]
  exact coverp000000000011101
theorem coverp00000000001110 : Covers (-6761639/500000 : ℚ) vp00000000001110 := join_branches bp000000000011100 bp000000000011101
private noncomputable def vp0000000000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000111-V-0000.bin"
private noncomputable def vp0000000000111_1 : Blocks := edgeBlocks% "full/vectors/0000000000111-V-0001.bin"
private noncomputable def vp0000000000111_2 : Blocks := edgeBlocks% "full/vectors/0000000000111-V-0002.bin"
private noncomputable def vp0000000000111_3 : Blocks := edgeBlocks% "full/vectors/0000000000111-V-0003.bin"
noncomputable def vp0000000000111 : Blocks := (Blocks.join (Blocks.join vp0000000000111_0 vp0000000000111_1) (Blocks.join vp0000000000111_2 vp0000000000111_3))
private theorem bp00000000001110 : Branch 0 (-6761639/1000000 : ℚ) vp0000000000111 := by
  apply branch_left_normalized (c:=vp00000000001110) (k:=0) (m:=206) (by decide +kernel)
  rw [show 2*(-6761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-6761639/500000 : ℚ) by norm_num]
  exact coverp00000000001110
private noncomputable def ep00000000001111_0 : Blocks := edgeBlocks% "full/vectors/00000000001111-E-0000.bin"
private noncomputable def ep00000000001111_1 : Blocks := edgeBlocks% "full/vectors/00000000001111-E-0001.bin"
private noncomputable def ep00000000001111_2 : Blocks := edgeBlocks% "full/vectors/00000000001111-E-0002.bin"
private noncomputable def ep00000000001111_3 : Blocks := edgeBlocks% "full/vectors/00000000001111-E-0003.bin"
noncomputable def ep00000000001111 : Blocks := (Blocks.join (Blocks.join ep00000000001111_0 ep00000000001111_1) (Blocks.join ep00000000001111_2 ep00000000001111_3))
private theorem idp00000000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000111.list =
    C ((2:ℤ)^397) * horner X vp00000000001111.list + horner X ep00000000001111.list := by
  exact edge_identity (B := (2:ℤ)^688) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001111 : Branch 1 (-6761639/1000000 : ℚ) vp0000000000111 := by
  apply branch_checked idp00000000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-6761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-7261639/500000 : ℚ) by norm_num]
  exact coverp00000000001111
theorem coverp0000000000111 : Covers (-6761639/1000000 : ℚ) vp0000000000111 := join_branches bp00000000001110 bp00000000001111
end NextProof.EdgeFull

