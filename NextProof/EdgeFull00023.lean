import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00022

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000000011011111_0 : Blocks := edgeBlocks% "full/vectors/0000000011011111-V-0000.bin"
noncomputable def vp0000000011011111 : Blocks := vp0000000011011111_0
theorem coverp0000000011011111 : Covers (-27636639/125000 : ℚ) vp0000000011011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000110111101_0 : Blocks := edgeBlocks% "full/vectors/00000000110111101-V-0000.bin"
noncomputable def vp00000000110111101 : Blocks := vp00000000110111101_0
theorem coverp00000000110111101 : Covers (-27574139/62500 : ℚ) vp00000000110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000110111100_0 : Blocks := edgeBlocks% "full/vectors/00000000110111100-V-0000.bin"
noncomputable def vp00000000110111100 : Blocks := vp00000000110111100_0
theorem coverp00000000110111100 : Covers (-27511639/62500 : ℚ) vp00000000110111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011011110_0 : Blocks := edgeBlocks% "full/vectors/0000000011011110-V-0000.bin"
noncomputable def vp0000000011011110 : Blocks := vp0000000011011110_0
private theorem bp00000000110111100 : Branch 0 (-27511639/125000 : ℚ) vp0000000011011110 := by
  apply branch_left_normalized (c:=vp00000000110111100) (k:=0) (m:=25) (by decide +kernel)
  rw [show 2*(-27511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-27511639/62500 : ℚ) by norm_num]
  exact coverp00000000110111100
private noncomputable def ep00000000110111101_0 : Blocks := edgeBlocks% "full/vectors/00000000110111101-E-0000.bin"
noncomputable def ep00000000110111101 : Blocks := ep00000000110111101_0
private theorem idp00000000110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011011110.list =
    C ((2:ℤ)^41) * horner X vp00000000110111101.list + horner X ep00000000110111101.list := by
  exact edge_identity (B := (2:ℤ)^154) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110111101 : Branch 1 (-27511639/125000 : ℚ) vp0000000011011110 := by
  apply branch_checked idp00000000110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-27511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-27574139/62500 : ℚ) by norm_num]
  exact coverp00000000110111101
theorem coverp0000000011011110 : Covers (-27511639/125000 : ℚ) vp0000000011011110 := join_branches bp00000000110111100 bp00000000110111101
private noncomputable def vp000000001101111_0 : Blocks := edgeBlocks% "full/vectors/000000001101111-V-0000.bin"
noncomputable def vp000000001101111 : Blocks := vp000000001101111_0
private theorem bp0000000011011110 : Branch 0 (-27511639/250000 : ℚ) vp000000001101111 := by
  apply branch_left_normalized (c:=vp0000000011011110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-27511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-27511639/125000 : ℚ) by norm_num]
  exact coverp0000000011011110
private noncomputable def ep0000000011011111_0 : Blocks := edgeBlocks% "full/vectors/0000000011011111-E-0000.bin"
noncomputable def ep0000000011011111 : Blocks := ep0000000011011111_0
private theorem idp0000000011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001101111.list =
    C ((2:ℤ)^66) * horner X vp0000000011011111.list + horner X ep0000000011011111.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011011111 : Branch 1 (-27511639/250000 : ℚ) vp000000001101111 := by
  apply branch_checked idp0000000011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-27511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-27636639/125000 : ℚ) by norm_num]
  exact coverp0000000011011111
theorem coverp000000001101111 : Covers (-27511639/250000 : ℚ) vp000000001101111 := join_branches bp0000000011011110 bp0000000011011111
private noncomputable def vp00000000110111011_0 : Blocks := edgeBlocks% "full/vectors/00000000110111011-V-0000.bin"
noncomputable def vp00000000110111011 : Blocks := vp00000000110111011_0
theorem coverp00000000110111011 : Covers (-27449139/62500 : ℚ) vp00000000110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000110111010_0 : Blocks := edgeBlocks% "full/vectors/00000000110111010-V-0000.bin"
noncomputable def vp00000000110111010 : Blocks := vp00000000110111010_0
theorem coverp00000000110111010 : Covers (-27386639/62500 : ℚ) vp00000000110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011011101_0 : Blocks := edgeBlocks% "full/vectors/0000000011011101-V-0000.bin"
noncomputable def vp0000000011011101 : Blocks := vp0000000011011101_0
private theorem bp00000000110111010 : Branch 0 (-27386639/125000 : ℚ) vp0000000011011101 := by
  apply branch_left_normalized (c:=vp00000000110111010) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-27386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-27386639/62500 : ℚ) by norm_num]
  exact coverp00000000110111010
private noncomputable def ep00000000110111011_0 : Blocks := edgeBlocks% "full/vectors/00000000110111011-E-0000.bin"
noncomputable def ep00000000110111011 : Blocks := ep00000000110111011_0
private theorem idp00000000110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011011101.list =
    C ((2:ℤ)^40) * horner X vp00000000110111011.list + horner X ep00000000110111011.list := by
  exact edge_identity (B := (2:ℤ)^153) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110111011 : Branch 1 (-27386639/125000 : ℚ) vp0000000011011101 := by
  apply branch_checked idp00000000110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-27386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-27449139/62500 : ℚ) by norm_num]
  exact coverp00000000110111011
theorem coverp0000000011011101 : Covers (-27386639/125000 : ℚ) vp0000000011011101 := join_branches bp00000000110111010 bp00000000110111011
private noncomputable def vp0000000011011100_0 : Blocks := edgeBlocks% "full/vectors/0000000011011100-V-0000.bin"
noncomputable def vp0000000011011100 : Blocks := vp0000000011011100_0
theorem coverp0000000011011100 : Covers (-27261639/125000 : ℚ) vp0000000011011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001101110_0 : Blocks := edgeBlocks% "full/vectors/000000001101110-V-0000.bin"
noncomputable def vp000000001101110 : Blocks := vp000000001101110_0
private theorem bp0000000011011100 : Branch 0 (-27261639/250000 : ℚ) vp000000001101110 := by
  apply branch_left_normalized (c:=vp0000000011011100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-27261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-27261639/125000 : ℚ) by norm_num]
  exact coverp0000000011011100
private noncomputable def ep0000000011011101_0 : Blocks := edgeBlocks% "full/vectors/0000000011011101-E-0000.bin"
noncomputable def ep0000000011011101 : Blocks := ep0000000011011101_0
private theorem idp0000000011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001101110.list =
    C ((2:ℤ)^68) * horner X vp0000000011011101.list + horner X ep0000000011011101.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011011101 : Branch 1 (-27261639/250000 : ℚ) vp000000001101110 := by
  apply branch_checked idp0000000011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-27261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-27386639/125000 : ℚ) by norm_num]
  exact coverp0000000011011101
theorem coverp000000001101110 : Covers (-27261639/250000 : ℚ) vp000000001101110 := join_branches bp0000000011011100 bp0000000011011101
private noncomputable def vp00000000110111_0 : Blocks := edgeBlocks% "full/vectors/00000000110111-V-0000.bin"
noncomputable def vp00000000110111 : Blocks := vp00000000110111_0
private theorem bp000000001101110 : Branch 0 (-27261639/500000 : ℚ) vp00000000110111 := by
  apply branch_left_normalized (c:=vp000000001101110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-27261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-27261639/250000 : ℚ) by norm_num]
  exact coverp000000001101110
private noncomputable def ep000000001101111_0 : Blocks := edgeBlocks% "full/vectors/000000001101111-E-0000.bin"
noncomputable def ep000000001101111 : Blocks := ep000000001101111_0
private theorem idp000000001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110111.list =
    C ((2:ℤ)^115) * horner X vp000000001101111.list + horner X ep000000001101111.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001101111 : Branch 1 (-27261639/500000 : ℚ) vp00000000110111 := by
  apply branch_checked idp000000001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-27261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-27511639/250000 : ℚ) by norm_num]
  exact coverp000000001101111
theorem coverp00000000110111 : Covers (-27261639/500000 : ℚ) vp00000000110111 := join_branches bp000000001101110 bp000000001101111
private noncomputable def vp0000000011011011_0 : Blocks := edgeBlocks% "full/vectors/0000000011011011-V-0000.bin"
noncomputable def vp0000000011011011 : Blocks := vp0000000011011011_0
theorem coverp0000000011011011 : Covers (-27136639/125000 : ℚ) vp0000000011011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011011010_0 : Blocks := edgeBlocks% "full/vectors/0000000011011010-V-0000.bin"
noncomputable def vp0000000011011010 : Blocks := vp0000000011011010_0
theorem coverp0000000011011010 : Covers (-27011639/125000 : ℚ) vp0000000011011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001101101_0 : Blocks := edgeBlocks% "full/vectors/000000001101101-V-0000.bin"
noncomputable def vp000000001101101 : Blocks := vp000000001101101_0
private theorem bp0000000011011010 : Branch 0 (-27011639/250000 : ℚ) vp000000001101101 := by
  apply branch_left_normalized (c:=vp0000000011011010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-27011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-27011639/125000 : ℚ) by norm_num]
  exact coverp0000000011011010
private noncomputable def ep0000000011011011_0 : Blocks := edgeBlocks% "full/vectors/0000000011011011-E-0000.bin"
noncomputable def ep0000000011011011 : Blocks := ep0000000011011011_0
private theorem idp0000000011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001101101.list =
    C ((2:ℤ)^70) * horner X vp0000000011011011.list + horner X ep0000000011011011.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011011011 : Branch 1 (-27011639/250000 : ℚ) vp000000001101101 := by
  apply branch_checked idp0000000011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-27011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-27136639/125000 : ℚ) by norm_num]
  exact coverp0000000011011011
theorem coverp000000001101101 : Covers (-27011639/250000 : ℚ) vp000000001101101 := join_branches bp0000000011011010 bp0000000011011011
private noncomputable def vp0000000011011001_0 : Blocks := edgeBlocks% "full/vectors/0000000011011001-V-0000.bin"
noncomputable def vp0000000011011001 : Blocks := vp0000000011011001_0
theorem coverp0000000011011001 : Covers (-26886639/125000 : ℚ) vp0000000011011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000110110001_0 : Blocks := edgeBlocks% "full/vectors/00000000110110001-V-0000.bin"
noncomputable def vp00000000110110001 : Blocks := vp00000000110110001_0
theorem coverp00000000110110001 : Covers (-26824139/62500 : ℚ) vp00000000110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000110110000_0 : Blocks := edgeBlocks% "full/vectors/00000000110110000-V-0000.bin"
noncomputable def vp00000000110110000 : Blocks := vp00000000110110000_0
theorem coverp00000000110110000 : Covers (-26761639/62500 : ℚ) vp00000000110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011011000_0 : Blocks := edgeBlocks% "full/vectors/0000000011011000-V-0000.bin"
noncomputable def vp0000000011011000 : Blocks := vp0000000011011000_0
private theorem bp00000000110110000 : Branch 0 (-26761639/125000 : ℚ) vp0000000011011000 := by
  apply branch_left_normalized (c:=vp00000000110110000) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-26761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-26761639/62500 : ℚ) by norm_num]
  exact coverp00000000110110000
private noncomputable def ep00000000110110001_0 : Blocks := edgeBlocks% "full/vectors/00000000110110001-E-0000.bin"
noncomputable def ep00000000110110001 : Blocks := ep00000000110110001_0
private theorem idp00000000110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011011000.list =
    C ((2:ℤ)^45) * horner X vp00000000110110001.list + horner X ep00000000110110001.list := by
  exact edge_identity (B := (2:ℤ)^161) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110110001 : Branch 1 (-26761639/125000 : ℚ) vp0000000011011000 := by
  apply branch_checked idp00000000110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-26761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-26824139/62500 : ℚ) by norm_num]
  exact coverp00000000110110001
theorem coverp0000000011011000 : Covers (-26761639/125000 : ℚ) vp0000000011011000 := join_branches bp00000000110110000 bp00000000110110001
private noncomputable def vp000000001101100_0 : Blocks := edgeBlocks% "full/vectors/000000001101100-V-0000.bin"
noncomputable def vp000000001101100 : Blocks := vp000000001101100_0
private theorem bp0000000011011000 : Branch 0 (-26761639/250000 : ℚ) vp000000001101100 := by
  apply branch_left_normalized (c:=vp0000000011011000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-26761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-26761639/125000 : ℚ) by norm_num]
  exact coverp0000000011011000
private noncomputable def ep0000000011011001_0 : Blocks := edgeBlocks% "full/vectors/0000000011011001-E-0000.bin"
noncomputable def ep0000000011011001 : Blocks := ep0000000011011001_0
private theorem idp0000000011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001101100.list =
    C ((2:ℤ)^70) * horner X vp0000000011011001.list + horner X ep0000000011011001.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011011001 : Branch 1 (-26761639/250000 : ℚ) vp000000001101100 := by
  apply branch_checked idp0000000011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-26761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-26886639/125000 : ℚ) by norm_num]
  exact coverp0000000011011001
theorem coverp000000001101100 : Covers (-26761639/250000 : ℚ) vp000000001101100 := join_branches bp0000000011011000 bp0000000011011001
private noncomputable def vp00000000110110_0 : Blocks := edgeBlocks% "full/vectors/00000000110110-V-0000.bin"
noncomputable def vp00000000110110 : Blocks := vp00000000110110_0
private theorem bp000000001101100 : Branch 0 (-26761639/500000 : ℚ) vp00000000110110 := by
  apply branch_left_normalized (c:=vp000000001101100) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-26761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-26761639/250000 : ℚ) by norm_num]
  exact coverp000000001101100
private noncomputable def ep000000001101101_0 : Blocks := edgeBlocks% "full/vectors/000000001101101-E-0000.bin"
noncomputable def ep000000001101101 : Blocks := ep000000001101101_0
private theorem idp000000001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110110.list =
    C ((2:ℤ)^124) * horner X vp000000001101101.list + horner X ep000000001101101.list := by
  exact edge_identity (B := (2:ℤ)^273) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001101101 : Branch 1 (-26761639/500000 : ℚ) vp00000000110110 := by
  apply branch_checked idp000000001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-26761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-27011639/250000 : ℚ) by norm_num]
  exact coverp000000001101101
theorem coverp00000000110110 : Covers (-26761639/500000 : ℚ) vp00000000110110 := join_branches bp000000001101100 bp000000001101101
private noncomputable def vp0000000011011_0 : Blocks := edgeBlocks% "full/vectors/0000000011011-V-0000.bin"
private noncomputable def vp0000000011011_1 : Blocks := edgeBlocks% "full/vectors/0000000011011-V-0001.bin"
noncomputable def vp0000000011011 : Blocks := (Blocks.join vp0000000011011_0 vp0000000011011_1)
private theorem bp00000000110110 : Branch 0 (-26761639/1000000 : ℚ) vp0000000011011 := by
  apply branch_left_normalized (c:=vp00000000110110) (k:=0) (m:=118) (by decide +kernel)
  rw [show 2*(-26761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-26761639/500000 : ℚ) by norm_num]
  exact coverp00000000110110
private noncomputable def ep00000000110111_0 : Blocks := edgeBlocks% "full/vectors/00000000110111-E-0000.bin"
private noncomputable def ep00000000110111_1 : Blocks := edgeBlocks% "full/vectors/00000000110111-E-0001.bin"
noncomputable def ep00000000110111 : Blocks := (Blocks.join ep00000000110111_0 ep00000000110111_1)
private theorem idp00000000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011011.list =
    C ((2:ℤ)^223) * horner X vp00000000110111.list + horner X ep00000000110111.list := by
  exact edge_identity (B := (2:ℤ)^418) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110111 : Branch 1 (-26761639/1000000 : ℚ) vp0000000011011 := by
  apply branch_checked idp00000000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-26761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-27261639/500000 : ℚ) by norm_num]
  exact coverp00000000110111
theorem coverp0000000011011 : Covers (-26761639/1000000 : ℚ) vp0000000011011 := join_branches bp00000000110110 bp00000000110111
private noncomputable def vp00000000110101111_0 : Blocks := edgeBlocks% "full/vectors/00000000110101111-V-0000.bin"
noncomputable def vp00000000110101111 : Blocks := vp00000000110101111_0
theorem coverp00000000110101111 : Covers (-26699139/62500 : ℚ) vp00000000110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000110101110_0 : Blocks := edgeBlocks% "full/vectors/00000000110101110-V-0000.bin"
noncomputable def vp00000000110101110 : Blocks := vp00000000110101110_0
theorem coverp00000000110101110 : Covers (-26636639/62500 : ℚ) vp00000000110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011010111_0 : Blocks := edgeBlocks% "full/vectors/0000000011010111-V-0000.bin"
noncomputable def vp0000000011010111 : Blocks := vp0000000011010111_0
private theorem bp00000000110101110 : Branch 0 (-26636639/125000 : ℚ) vp0000000011010111 := by
  apply branch_left_normalized (c:=vp00000000110101110) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-26636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-26636639/62500 : ℚ) by norm_num]
  exact coverp00000000110101110
private noncomputable def ep00000000110101111_0 : Blocks := edgeBlocks% "full/vectors/00000000110101111-E-0000.bin"
noncomputable def ep00000000110101111 : Blocks := ep00000000110101111_0
private theorem idp00000000110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011010111.list =
    C ((2:ℤ)^43) * horner X vp00000000110101111.list + horner X ep00000000110101111.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110101111 : Branch 1 (-26636639/125000 : ℚ) vp0000000011010111 := by
  apply branch_checked idp00000000110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-26636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-26699139/62500 : ℚ) by norm_num]
  exact coverp00000000110101111
theorem coverp0000000011010111 : Covers (-26636639/125000 : ℚ) vp0000000011010111 := join_branches bp00000000110101110 bp00000000110101111
private noncomputable def vp00000000110101101_0 : Blocks := edgeBlocks% "full/vectors/00000000110101101-V-0000.bin"
noncomputable def vp00000000110101101 : Blocks := vp00000000110101101_0
theorem coverp00000000110101101 : Covers (-26574139/62500 : ℚ) vp00000000110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001101011001_0 : Blocks := edgeBlocks% "full/vectors/000000001101011001-V-0000.bin"
noncomputable def vp000000001101011001 : Blocks := vp000000001101011001_0
theorem coverp000000001101011001 : Covers (-26542889/31250 : ℚ) vp000000001101011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011010110001_0 : Blocks := edgeBlocks% "full/vectors/0000000011010110001-V-0000.bin"
noncomputable def vp0000000011010110001 : Blocks := vp0000000011010110001_0
theorem coverp0000000011010110001 : Covers (-26527264/15625 : ℚ) vp0000000011010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011010110000_0 : Blocks := edgeBlocks% "full/vectors/0000000011010110000-V-0000.bin"
noncomputable def vp0000000011010110000 : Blocks := vp0000000011010110000_0
theorem coverp0000000011010110000 : Covers (-26511639/15625 : ℚ) vp0000000011010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001101011000_0 : Blocks := edgeBlocks% "full/vectors/000000001101011000-V-0000.bin"
noncomputable def vp000000001101011000 : Blocks := vp000000001101011000_0
private theorem bp0000000011010110000 : Branch 0 (-26511639/31250 : ℚ) vp000000001101011000 := by
  apply branch_left_normalized (c:=vp0000000011010110000) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-26511639/31250 : ℚ) - ((0:ℤ):ℚ) = (-26511639/15625 : ℚ) by norm_num]
  exact coverp0000000011010110000
private noncomputable def ep0000000011010110001_0 : Blocks := edgeBlocks% "full/vectors/0000000011010110001-E-0000.bin"
noncomputable def ep0000000011010110001 : Blocks := ep0000000011010110001_0
private theorem idp0000000011010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001101011000.list =
    C ((2:ℤ)^21) * horner X vp0000000011010110001.list + horner X ep0000000011010110001.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011010110001 : Branch 1 (-26511639/31250 : ℚ) vp000000001101011000 := by
  apply branch_checked idp0000000011010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-26511639/31250 : ℚ) - ((1:ℤ):ℚ) = (-26527264/15625 : ℚ) by norm_num]
  exact coverp0000000011010110001
theorem coverp000000001101011000 : Covers (-26511639/31250 : ℚ) vp000000001101011000 := join_branches bp0000000011010110000 bp0000000011010110001
private noncomputable def vp00000000110101100_0 : Blocks := edgeBlocks% "full/vectors/00000000110101100-V-0000.bin"
noncomputable def vp00000000110101100 : Blocks := vp00000000110101100_0
private theorem bp000000001101011000 : Branch 0 (-26511639/62500 : ℚ) vp00000000110101100 := by
  apply branch_left_normalized (c:=vp000000001101011000) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-26511639/62500 : ℚ) - ((0:ℤ):ℚ) = (-26511639/31250 : ℚ) by norm_num]
  exact coverp000000001101011000
private noncomputable def ep000000001101011001_0 : Blocks := edgeBlocks% "full/vectors/000000001101011001-E-0000.bin"
noncomputable def ep000000001101011001 : Blocks := ep000000001101011001_0
private theorem idp000000001101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110101100.list =
    C ((2:ℤ)^30) * horner X vp000000001101011001.list + horner X ep000000001101011001.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001101011001 : Branch 1 (-26511639/62500 : ℚ) vp00000000110101100 := by
  apply branch_checked idp000000001101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-26511639/62500 : ℚ) - ((1:ℤ):ℚ) = (-26542889/31250 : ℚ) by norm_num]
  exact coverp000000001101011001
theorem coverp00000000110101100 : Covers (-26511639/62500 : ℚ) vp00000000110101100 := join_branches bp000000001101011000 bp000000001101011001
private noncomputable def vp0000000011010110_0 : Blocks := edgeBlocks% "full/vectors/0000000011010110-V-0000.bin"
noncomputable def vp0000000011010110 : Blocks := vp0000000011010110_0
private theorem bp00000000110101100 : Branch 0 (-26511639/125000 : ℚ) vp0000000011010110 := by
  apply branch_left_normalized (c:=vp00000000110101100) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-26511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-26511639/62500 : ℚ) by norm_num]
  exact coverp00000000110101100
private noncomputable def ep00000000110101101_0 : Blocks := edgeBlocks% "full/vectors/00000000110101101-E-0000.bin"
noncomputable def ep00000000110101101 : Blocks := ep00000000110101101_0
private theorem idp00000000110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011010110.list =
    C ((2:ℤ)^44) * horner X vp00000000110101101.list + horner X ep00000000110101101.list := by
  exact edge_identity (B := (2:ℤ)^157) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110101101 : Branch 1 (-26511639/125000 : ℚ) vp0000000011010110 := by
  apply branch_checked idp00000000110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-26511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-26574139/62500 : ℚ) by norm_num]
  exact coverp00000000110101101
theorem coverp0000000011010110 : Covers (-26511639/125000 : ℚ) vp0000000011010110 := join_branches bp00000000110101100 bp00000000110101101
private noncomputable def vp000000001101011_0 : Blocks := edgeBlocks% "full/vectors/000000001101011-V-0000.bin"
noncomputable def vp000000001101011 : Blocks := vp000000001101011_0
private theorem bp0000000011010110 : Branch 0 (-26511639/250000 : ℚ) vp000000001101011 := by
  apply branch_left_normalized (c:=vp0000000011010110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-26511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-26511639/125000 : ℚ) by norm_num]
  exact coverp0000000011010110
private noncomputable def ep0000000011010111_0 : Blocks := edgeBlocks% "full/vectors/0000000011010111-E-0000.bin"
noncomputable def ep0000000011010111 : Blocks := ep0000000011010111_0
private theorem idp0000000011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001101011.list =
    C ((2:ℤ)^69) * horner X vp0000000011010111.list + horner X ep0000000011010111.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011010111 : Branch 1 (-26511639/250000 : ℚ) vp000000001101011 := by
  apply branch_checked idp0000000011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-26511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-26636639/125000 : ℚ) by norm_num]
  exact coverp0000000011010111
theorem coverp000000001101011 : Covers (-26511639/250000 : ℚ) vp000000001101011 := join_branches bp0000000011010110 bp0000000011010111
private noncomputable def vp000000001101010111_0 : Blocks := edgeBlocks% "full/vectors/000000001101010111-V-0000.bin"
noncomputable def vp000000001101010111 : Blocks := vp000000001101010111_0
theorem coverp000000001101010111 : Covers (-26480389/31250 : ℚ) vp000000001101010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001101010110_0 : Blocks := edgeBlocks% "full/vectors/000000001101010110-V-0000.bin"
noncomputable def vp000000001101010110 : Blocks := vp000000001101010110_0
theorem coverp000000001101010110 : Covers (-26449139/31250 : ℚ) vp000000001101010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000110101011_0 : Blocks := edgeBlocks% "full/vectors/00000000110101011-V-0000.bin"
noncomputable def vp00000000110101011 : Blocks := vp00000000110101011_0
private theorem bp000000001101010110 : Branch 0 (-26449139/62500 : ℚ) vp00000000110101011 := by
  apply branch_left_normalized (c:=vp000000001101010110) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-26449139/62500 : ℚ) - ((0:ℤ):ℚ) = (-26449139/31250 : ℚ) by norm_num]
  exact coverp000000001101010110
private noncomputable def ep000000001101010111_0 : Blocks := edgeBlocks% "full/vectors/000000001101010111-E-0000.bin"
noncomputable def ep000000001101010111 : Blocks := ep000000001101010111_0
private theorem idp000000001101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110101011.list =
    C ((2:ℤ)^29) * horner X vp000000001101010111.list + horner X ep000000001101010111.list := by
  exact edge_identity (B := (2:ℤ)^140) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001101010111 : Branch 1 (-26449139/62500 : ℚ) vp00000000110101011 := by
  apply branch_checked idp000000001101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-26449139/62500 : ℚ) - ((1:ℤ):ℚ) = (-26480389/31250 : ℚ) by norm_num]
  exact coverp000000001101010111
theorem coverp00000000110101011 : Covers (-26449139/62500 : ℚ) vp00000000110101011 := join_branches bp000000001101010110 bp000000001101010111
private noncomputable def vp00000000110101010_0 : Blocks := edgeBlocks% "full/vectors/00000000110101010-V-0000.bin"
noncomputable def vp00000000110101010 : Blocks := vp00000000110101010_0
theorem coverp00000000110101010 : Covers (-26386639/62500 : ℚ) vp00000000110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011010101_0 : Blocks := edgeBlocks% "full/vectors/0000000011010101-V-0000.bin"
noncomputable def vp0000000011010101 : Blocks := vp0000000011010101_0
private theorem bp00000000110101010 : Branch 0 (-26386639/125000 : ℚ) vp0000000011010101 := by
  apply branch_left_normalized (c:=vp00000000110101010) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-26386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-26386639/62500 : ℚ) by norm_num]
  exact coverp00000000110101010
private noncomputable def ep00000000110101011_0 : Blocks := edgeBlocks% "full/vectors/00000000110101011-E-0000.bin"
noncomputable def ep00000000110101011 : Blocks := ep00000000110101011_0
private theorem idp00000000110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011010101.list =
    C ((2:ℤ)^42) * horner X vp00000000110101011.list + horner X ep00000000110101011.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110101011 : Branch 1 (-26386639/125000 : ℚ) vp0000000011010101 := by
  apply branch_checked idp00000000110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-26386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-26449139/62500 : ℚ) by norm_num]
  exact coverp00000000110101011
theorem coverp0000000011010101 : Covers (-26386639/125000 : ℚ) vp0000000011010101 := join_branches bp00000000110101010 bp00000000110101011
private noncomputable def vp0000000011010100_0 : Blocks := edgeBlocks% "full/vectors/0000000011010100-V-0000.bin"
noncomputable def vp0000000011010100 : Blocks := vp0000000011010100_0
theorem coverp0000000011010100 : Covers (-26261639/125000 : ℚ) vp0000000011010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001101010_0 : Blocks := edgeBlocks% "full/vectors/000000001101010-V-0000.bin"
noncomputable def vp000000001101010 : Blocks := vp000000001101010_0
private theorem bp0000000011010100 : Branch 0 (-26261639/250000 : ℚ) vp000000001101010 := by
  apply branch_left_normalized (c:=vp0000000011010100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-26261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-26261639/125000 : ℚ) by norm_num]
  exact coverp0000000011010100
private noncomputable def ep0000000011010101_0 : Blocks := edgeBlocks% "full/vectors/0000000011010101-E-0000.bin"
noncomputable def ep0000000011010101 : Blocks := ep0000000011010101_0
private theorem idp0000000011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001101010.list =
    C ((2:ℤ)^67) * horner X vp0000000011010101.list + horner X ep0000000011010101.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011010101 : Branch 1 (-26261639/250000 : ℚ) vp000000001101010 := by
  apply branch_checked idp0000000011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-26261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-26386639/125000 : ℚ) by norm_num]
  exact coverp0000000011010101
theorem coverp000000001101010 : Covers (-26261639/250000 : ℚ) vp000000001101010 := join_branches bp0000000011010100 bp0000000011010101
private noncomputable def vp00000000110101_0 : Blocks := edgeBlocks% "full/vectors/00000000110101-V-0000.bin"
noncomputable def vp00000000110101 : Blocks := vp00000000110101_0
private theorem bp000000001101010 : Branch 0 (-26261639/500000 : ℚ) vp00000000110101 := by
  apply branch_left_normalized (c:=vp000000001101010) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-26261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-26261639/250000 : ℚ) by norm_num]
  exact coverp000000001101010
private noncomputable def ep000000001101011_0 : Blocks := edgeBlocks% "full/vectors/000000001101011-E-0000.bin"
noncomputable def ep000000001101011 : Blocks := ep000000001101011_0
private theorem idp000000001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110101.list =
    C ((2:ℤ)^116) * horner X vp000000001101011.list + horner X ep000000001101011.list := by
  exact edge_identity (B := (2:ℤ)^265) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001101011 : Branch 1 (-26261639/500000 : ℚ) vp00000000110101 := by
  apply branch_checked idp000000001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-26261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-26511639/250000 : ℚ) by norm_num]
  exact coverp000000001101011
theorem coverp00000000110101 : Covers (-26261639/500000 : ℚ) vp00000000110101 := join_branches bp000000001101010 bp000000001101011
private noncomputable def vp0000000011010011_0 : Blocks := edgeBlocks% "full/vectors/0000000011010011-V-0000.bin"
noncomputable def vp0000000011010011 : Blocks := vp0000000011010011_0
theorem coverp0000000011010011 : Covers (-26136639/125000 : ℚ) vp0000000011010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011010010_0 : Blocks := edgeBlocks% "full/vectors/0000000011010010-V-0000.bin"
noncomputable def vp0000000011010010 : Blocks := vp0000000011010010_0
theorem coverp0000000011010010 : Covers (-26011639/125000 : ℚ) vp0000000011010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001101001_0 : Blocks := edgeBlocks% "full/vectors/000000001101001-V-0000.bin"
noncomputable def vp000000001101001 : Blocks := vp000000001101001_0
private theorem bp0000000011010010 : Branch 0 (-26011639/250000 : ℚ) vp000000001101001 := by
  apply branch_left_normalized (c:=vp0000000011010010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-26011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-26011639/125000 : ℚ) by norm_num]
  exact coverp0000000011010010
private noncomputable def ep0000000011010011_0 : Blocks := edgeBlocks% "full/vectors/0000000011010011-E-0000.bin"
noncomputable def ep0000000011010011 : Blocks := ep0000000011010011_0
private theorem idp0000000011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001101001.list =
    C ((2:ℤ)^68) * horner X vp0000000011010011.list + horner X ep0000000011010011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011010011 : Branch 1 (-26011639/250000 : ℚ) vp000000001101001 := by
  apply branch_checked idp0000000011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-26011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-26136639/125000 : ℚ) by norm_num]
  exact coverp0000000011010011
theorem coverp000000001101001 : Covers (-26011639/250000 : ℚ) vp000000001101001 := join_branches bp0000000011010010 bp0000000011010011
private noncomputable def vp0000000011010001_0 : Blocks := edgeBlocks% "full/vectors/0000000011010001-V-0000.bin"
noncomputable def vp0000000011010001 : Blocks := vp0000000011010001_0
theorem coverp0000000011010001 : Covers (-25886639/125000 : ℚ) vp0000000011010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011010000_0 : Blocks := edgeBlocks% "full/vectors/0000000011010000-V-0000.bin"
noncomputable def vp0000000011010000 : Blocks := vp0000000011010000_0
theorem coverp0000000011010000 : Covers (-25761639/125000 : ℚ) vp0000000011010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001101000_0 : Blocks := edgeBlocks% "full/vectors/000000001101000-V-0000.bin"
noncomputable def vp000000001101000 : Blocks := vp000000001101000_0
private theorem bp0000000011010000 : Branch 0 (-25761639/250000 : ℚ) vp000000001101000 := by
  apply branch_left_normalized (c:=vp0000000011010000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-25761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-25761639/125000 : ℚ) by norm_num]
  exact coverp0000000011010000
private noncomputable def ep0000000011010001_0 : Blocks := edgeBlocks% "full/vectors/0000000011010001-E-0000.bin"
noncomputable def ep0000000011010001 : Blocks := ep0000000011010001_0
private theorem idp0000000011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001101000.list =
    C ((2:ℤ)^72) * horner X vp0000000011010001.list + horner X ep0000000011010001.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011010001 : Branch 1 (-25761639/250000 : ℚ) vp000000001101000 := by
  apply branch_checked idp0000000011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-25761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-25886639/125000 : ℚ) by norm_num]
  exact coverp0000000011010001
theorem coverp000000001101000 : Covers (-25761639/250000 : ℚ) vp000000001101000 := join_branches bp0000000011010000 bp0000000011010001
private noncomputable def vp00000000110100_0 : Blocks := edgeBlocks% "full/vectors/00000000110100-V-0000.bin"
noncomputable def vp00000000110100 : Blocks := vp00000000110100_0
private theorem bp000000001101000 : Branch 0 (-25761639/500000 : ℚ) vp00000000110100 := by
  apply branch_left_normalized (c:=vp000000001101000) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-25761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-25761639/250000 : ℚ) by norm_num]
  exact coverp000000001101000
private noncomputable def ep000000001101001_0 : Blocks := edgeBlocks% "full/vectors/000000001101001-E-0000.bin"
noncomputable def ep000000001101001 : Blocks := ep000000001101001_0
private theorem idp000000001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110100.list =
    C ((2:ℤ)^122) * horner X vp000000001101001.list + horner X ep000000001101001.list := by
  exact edge_identity (B := (2:ℤ)^269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001101001 : Branch 1 (-25761639/500000 : ℚ) vp00000000110100 := by
  apply branch_checked idp000000001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-25761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-26011639/250000 : ℚ) by norm_num]
  exact coverp000000001101001
theorem coverp00000000110100 : Covers (-25761639/500000 : ℚ) vp00000000110100 := join_branches bp000000001101000 bp000000001101001
private noncomputable def vp0000000011010_0 : Blocks := edgeBlocks% "full/vectors/0000000011010-V-0000.bin"
private noncomputable def vp0000000011010_1 : Blocks := edgeBlocks% "full/vectors/0000000011010-V-0001.bin"
noncomputable def vp0000000011010 : Blocks := (Blocks.join vp0000000011010_0 vp0000000011010_1)
private theorem bp00000000110100 : Branch 0 (-25761639/1000000 : ℚ) vp0000000011010 := by
  apply branch_left_normalized (c:=vp00000000110100) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-25761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-25761639/500000 : ℚ) by norm_num]
  exact coverp00000000110100
private noncomputable def ep00000000110101_0 : Blocks := edgeBlocks% "full/vectors/00000000110101-E-0000.bin"
private noncomputable def ep00000000110101_1 : Blocks := edgeBlocks% "full/vectors/00000000110101-E-0001.bin"
noncomputable def ep00000000110101 : Blocks := (Blocks.join ep00000000110101_0 ep00000000110101_1)
private theorem idp00000000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011010.list =
    C ((2:ℤ)^220) * horner X vp00000000110101.list + horner X ep00000000110101.list := by
  exact edge_identity (B := (2:ℤ)^417) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110101 : Branch 1 (-25761639/1000000 : ℚ) vp0000000011010 := by
  apply branch_checked idp00000000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-25761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-26261639/500000 : ℚ) by norm_num]
  exact coverp00000000110101
theorem coverp0000000011010 : Covers (-25761639/1000000 : ℚ) vp0000000011010 := join_branches bp00000000110100 bp00000000110101
private noncomputable def vp000000001101_0 : Blocks := edgeBlocks% "full/vectors/000000001101-V-0000.bin"
private noncomputable def vp000000001101_1 : Blocks := edgeBlocks% "full/vectors/000000001101-V-0001.bin"
private noncomputable def vp000000001101_2 : Blocks := edgeBlocks% "full/vectors/000000001101-V-0002.bin"
private noncomputable def vp000000001101_3 : Blocks := edgeBlocks% "full/vectors/000000001101-V-0003.bin"
noncomputable def vp000000001101 : Blocks := (Blocks.join (Blocks.join vp000000001101_0 vp000000001101_1) (Blocks.join vp000000001101_2 vp000000001101_3))
private theorem bp0000000011010 : Branch 0 (-25761639/2000000 : ℚ) vp000000001101 := by
  apply branch_left_normalized (c:=vp0000000011010) (k:=0) (m:=214) (by decide +kernel)
  rw [show 2*(-25761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-25761639/1000000 : ℚ) by norm_num]
  exact coverp0000000011010
private noncomputable def ep0000000011011_0 : Blocks := edgeBlocks% "full/vectors/0000000011011-E-0000.bin"
private noncomputable def ep0000000011011_1 : Blocks := edgeBlocks% "full/vectors/0000000011011-E-0001.bin"
private noncomputable def ep0000000011011_2 : Blocks := edgeBlocks% "full/vectors/0000000011011-E-0002.bin"
private noncomputable def ep0000000011011_3 : Blocks := edgeBlocks% "full/vectors/0000000011011-E-0003.bin"
noncomputable def ep0000000011011 : Blocks := (Blocks.join (Blocks.join ep0000000011011_0 ep0000000011011_1) (Blocks.join ep0000000011011_2 ep0000000011011_3))
private theorem idp0000000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001101.list =
    C ((2:ℤ)^409) * horner X vp0000000011011.list + horner X ep0000000011011.list := by
  exact edge_identity (B := (2:ℤ)^711) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011011 : Branch 1 (-25761639/2000000 : ℚ) vp000000001101 := by
  apply branch_checked idp0000000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-25761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-26761639/1000000 : ℚ) by norm_num]
  exact coverp0000000011011
theorem coverp000000001101 : Covers (-25761639/2000000 : ℚ) vp000000001101 := join_branches bp0000000011010 bp0000000011011
private noncomputable def vp00000000110011111_0 : Blocks := edgeBlocks% "full/vectors/00000000110011111-V-0000.bin"
noncomputable def vp00000000110011111 : Blocks := vp00000000110011111_0
theorem coverp00000000110011111 : Covers (-25699139/62500 : ℚ) vp00000000110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000110011110_0 : Blocks := edgeBlocks% "full/vectors/00000000110011110-V-0000.bin"
noncomputable def vp00000000110011110 : Blocks := vp00000000110011110_0
theorem coverp00000000110011110 : Covers (-25636639/62500 : ℚ) vp00000000110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011001111_0 : Blocks := edgeBlocks% "full/vectors/0000000011001111-V-0000.bin"
noncomputable def vp0000000011001111 : Blocks := vp0000000011001111_0
private theorem bp00000000110011110 : Branch 0 (-25636639/125000 : ℚ) vp0000000011001111 := by
  apply branch_left_normalized (c:=vp00000000110011110) (k:=0) (m:=29) (by decide +kernel)
  rw [show 2*(-25636639/125000 : ℚ) - ((0:ℤ):ℚ) = (-25636639/62500 : ℚ) by norm_num]
  exact coverp00000000110011110
private noncomputable def ep00000000110011111_0 : Blocks := edgeBlocks% "full/vectors/00000000110011111-E-0000.bin"
noncomputable def ep00000000110011111 : Blocks := ep00000000110011111_0
private theorem idp00000000110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011001111.list =
    C ((2:ℤ)^44) * horner X vp00000000110011111.list + horner X ep00000000110011111.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110011111 : Branch 1 (-25636639/125000 : ℚ) vp0000000011001111 := by
  apply branch_checked idp00000000110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-25636639/125000 : ℚ) - ((1:ℤ):ℚ) = (-25699139/62500 : ℚ) by norm_num]
  exact coverp00000000110011111
theorem coverp0000000011001111 : Covers (-25636639/125000 : ℚ) vp0000000011001111 := join_branches bp00000000110011110 bp00000000110011111
private noncomputable def vp000000001100111011_0 : Blocks := edgeBlocks% "full/vectors/000000001100111011-V-0000.bin"
noncomputable def vp000000001100111011 : Blocks := vp000000001100111011_0
theorem coverp000000001100111011 : Covers (-25605389/31250 : ℚ) vp000000001100111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001100111010_0 : Blocks := edgeBlocks% "full/vectors/000000001100111010-V-0000.bin"
noncomputable def vp000000001100111010 : Blocks := vp000000001100111010_0
theorem coverp000000001100111010 : Covers (-25574139/31250 : ℚ) vp000000001100111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000110011101_0 : Blocks := edgeBlocks% "full/vectors/00000000110011101-V-0000.bin"
noncomputable def vp00000000110011101 : Blocks := vp00000000110011101_0
private theorem bp000000001100111010 : Branch 0 (-25574139/62500 : ℚ) vp00000000110011101 := by
  apply branch_left_normalized (c:=vp000000001100111010) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-25574139/62500 : ℚ) - ((0:ℤ):ℚ) = (-25574139/31250 : ℚ) by norm_num]
  exact coverp000000001100111010
private noncomputable def ep000000001100111011_0 : Blocks := edgeBlocks% "full/vectors/000000001100111011-E-0000.bin"
noncomputable def ep000000001100111011 : Blocks := ep000000001100111011_0
private theorem idp000000001100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110011101.list =
    C ((2:ℤ)^30) * horner X vp000000001100111011.list + horner X ep000000001100111011.list := by
  exact edge_identity (B := (2:ℤ)^136) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001100111011 : Branch 1 (-25574139/62500 : ℚ) vp00000000110011101 := by
  apply branch_checked idp000000001100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-25574139/62500 : ℚ) - ((1:ℤ):ℚ) = (-25605389/31250 : ℚ) by norm_num]
  exact coverp000000001100111011
theorem coverp00000000110011101 : Covers (-25574139/62500 : ℚ) vp00000000110011101 := join_branches bp000000001100111010 bp000000001100111011
private noncomputable def vp000000001100111001_0 : Blocks := edgeBlocks% "full/vectors/000000001100111001-V-0000.bin"
noncomputable def vp000000001100111001 : Blocks := vp000000001100111001_0
theorem coverp000000001100111001 : Covers (-25542889/31250 : ℚ) vp000000001100111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011001110001_0 : Blocks := edgeBlocks% "full/vectors/0000000011001110001-V-0000.bin"
noncomputable def vp0000000011001110001 : Blocks := vp0000000011001110001_0
theorem coverp0000000011001110001 : Covers (-25527264/15625 : ℚ) vp0000000011001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011001110000_0 : Blocks := edgeBlocks% "full/vectors/0000000011001110000-V-0000.bin"
noncomputable def vp0000000011001110000 : Blocks := vp0000000011001110000_0
theorem coverp0000000011001110000 : Covers (-25511639/15625 : ℚ) vp0000000011001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001100111000_0 : Blocks := edgeBlocks% "full/vectors/000000001100111000-V-0000.bin"
noncomputable def vp000000001100111000 : Blocks := vp000000001100111000_0
private theorem bp0000000011001110000 : Branch 0 (-25511639/31250 : ℚ) vp000000001100111000 := by
  apply branch_left_normalized (c:=vp0000000011001110000) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-25511639/31250 : ℚ) - ((0:ℤ):ℚ) = (-25511639/15625 : ℚ) by norm_num]
  exact coverp0000000011001110000
private noncomputable def ep0000000011001110001_0 : Blocks := edgeBlocks% "full/vectors/0000000011001110001-E-0000.bin"
noncomputable def ep0000000011001110001 : Blocks := ep0000000011001110001_0
private theorem idp0000000011001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001100111000.list =
    C ((2:ℤ)^21) * horner X vp0000000011001110001.list + horner X ep0000000011001110001.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011001110001 : Branch 1 (-25511639/31250 : ℚ) vp000000001100111000 := by
  apply branch_checked idp0000000011001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-25511639/31250 : ℚ) - ((1:ℤ):ℚ) = (-25527264/15625 : ℚ) by norm_num]
  exact coverp0000000011001110001
theorem coverp000000001100111000 : Covers (-25511639/31250 : ℚ) vp000000001100111000 := join_branches bp0000000011001110000 bp0000000011001110001
private noncomputable def vp00000000110011100_0 : Blocks := edgeBlocks% "full/vectors/00000000110011100-V-0000.bin"
noncomputable def vp00000000110011100 : Blocks := vp00000000110011100_0
private theorem bp000000001100111000 : Branch 0 (-25511639/62500 : ℚ) vp00000000110011100 := by
  apply branch_left_normalized (c:=vp000000001100111000) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-25511639/62500 : ℚ) - ((0:ℤ):ℚ) = (-25511639/31250 : ℚ) by norm_num]
  exact coverp000000001100111000
private noncomputable def ep000000001100111001_0 : Blocks := edgeBlocks% "full/vectors/000000001100111001-E-0000.bin"
noncomputable def ep000000001100111001 : Blocks := ep000000001100111001_0
private theorem idp000000001100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110011100.list =
    C ((2:ℤ)^29) * horner X vp000000001100111001.list + horner X ep000000001100111001.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001100111001 : Branch 1 (-25511639/62500 : ℚ) vp00000000110011100 := by
  apply branch_checked idp000000001100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-25511639/62500 : ℚ) - ((1:ℤ):ℚ) = (-25542889/31250 : ℚ) by norm_num]
  exact coverp000000001100111001
theorem coverp00000000110011100 : Covers (-25511639/62500 : ℚ) vp00000000110011100 := join_branches bp000000001100111000 bp000000001100111001
private noncomputable def vp0000000011001110_0 : Blocks := edgeBlocks% "full/vectors/0000000011001110-V-0000.bin"
noncomputable def vp0000000011001110 : Blocks := vp0000000011001110_0
private theorem bp00000000110011100 : Branch 0 (-25511639/125000 : ℚ) vp0000000011001110 := by
  apply branch_left_normalized (c:=vp00000000110011100) (k:=0) (m:=28) (by decide +kernel)
  rw [show 2*(-25511639/125000 : ℚ) - ((0:ℤ):ℚ) = (-25511639/62500 : ℚ) by norm_num]
  exact coverp00000000110011100
private noncomputable def ep00000000110011101_0 : Blocks := edgeBlocks% "full/vectors/00000000110011101-E-0000.bin"
noncomputable def ep00000000110011101 : Blocks := ep00000000110011101_0
private theorem idp00000000110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011001110.list =
    C ((2:ℤ)^44) * horner X vp00000000110011101.list + horner X ep00000000110011101.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110011101 : Branch 1 (-25511639/125000 : ℚ) vp0000000011001110 := by
  apply branch_checked idp00000000110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-25511639/125000 : ℚ) - ((1:ℤ):ℚ) = (-25574139/62500 : ℚ) by norm_num]
  exact coverp00000000110011101
theorem coverp0000000011001110 : Covers (-25511639/125000 : ℚ) vp0000000011001110 := join_branches bp00000000110011100 bp00000000110011101
private noncomputable def vp000000001100111_0 : Blocks := edgeBlocks% "full/vectors/000000001100111-V-0000.bin"
noncomputable def vp000000001100111 : Blocks := vp000000001100111_0
private theorem bp0000000011001110 : Branch 0 (-25511639/250000 : ℚ) vp000000001100111 := by
  apply branch_left_normalized (c:=vp0000000011001110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-25511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-25511639/125000 : ℚ) by norm_num]
  exact coverp0000000011001110
private noncomputable def ep0000000011001111_0 : Blocks := edgeBlocks% "full/vectors/0000000011001111-E-0000.bin"
noncomputable def ep0000000011001111 : Blocks := ep0000000011001111_0
private theorem idp0000000011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001100111.list =
    C ((2:ℤ)^70) * horner X vp0000000011001111.list + horner X ep0000000011001111.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011001111 : Branch 1 (-25511639/250000 : ℚ) vp000000001100111 := by
  apply branch_checked idp0000000011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-25511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-25636639/125000 : ℚ) by norm_num]
  exact coverp0000000011001111
theorem coverp000000001100111 : Covers (-25511639/250000 : ℚ) vp000000001100111 := join_branches bp0000000011001110 bp0000000011001111
private noncomputable def vp000000001100110111_0 : Blocks := edgeBlocks% "full/vectors/000000001100110111-V-0000.bin"
noncomputable def vp000000001100110111 : Blocks := vp000000001100110111_0
theorem coverp000000001100110111 : Covers (-25480389/31250 : ℚ) vp000000001100110111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001100110110_0 : Blocks := edgeBlocks% "full/vectors/000000001100110110-V-0000.bin"
noncomputable def vp000000001100110110 : Blocks := vp000000001100110110_0
theorem coverp000000001100110110 : Covers (-25449139/31250 : ℚ) vp000000001100110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000110011011_0 : Blocks := edgeBlocks% "full/vectors/00000000110011011-V-0000.bin"
noncomputable def vp00000000110011011 : Blocks := vp00000000110011011_0
private theorem bp000000001100110110 : Branch 0 (-25449139/62500 : ℚ) vp00000000110011011 := by
  apply branch_left_normalized (c:=vp000000001100110110) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-25449139/62500 : ℚ) - ((0:ℤ):ℚ) = (-25449139/31250 : ℚ) by norm_num]
  exact coverp000000001100110110
private noncomputable def ep000000001100110111_0 : Blocks := edgeBlocks% "full/vectors/000000001100110111-E-0000.bin"
noncomputable def ep000000001100110111 : Blocks := ep000000001100110111_0
private theorem idp000000001100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110011011.list =
    C ((2:ℤ)^28) * horner X vp000000001100110111.list + horner X ep000000001100110111.list := by
  exact edge_identity (B := (2:ℤ)^137) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001100110111 : Branch 1 (-25449139/62500 : ℚ) vp00000000110011011 := by
  apply branch_checked idp000000001100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-25449139/62500 : ℚ) - ((1:ℤ):ℚ) = (-25480389/31250 : ℚ) by norm_num]
  exact coverp000000001100110111
theorem coverp00000000110011011 : Covers (-25449139/62500 : ℚ) vp00000000110011011 := join_branches bp000000001100110110 bp000000001100110111
private noncomputable def vp00000000110011010_0 : Blocks := edgeBlocks% "full/vectors/00000000110011010-V-0000.bin"
noncomputable def vp00000000110011010 : Blocks := vp00000000110011010_0
theorem coverp00000000110011010 : Covers (-25386639/62500 : ℚ) vp00000000110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011001101_0 : Blocks := edgeBlocks% "full/vectors/0000000011001101-V-0000.bin"
noncomputable def vp0000000011001101 : Blocks := vp0000000011001101_0
private theorem bp00000000110011010 : Branch 0 (-25386639/125000 : ℚ) vp0000000011001101 := by
  apply branch_left_normalized (c:=vp00000000110011010) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-25386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-25386639/62500 : ℚ) by norm_num]
  exact coverp00000000110011010
private noncomputable def ep00000000110011011_0 : Blocks := edgeBlocks% "full/vectors/00000000110011011-E-0000.bin"
noncomputable def ep00000000110011011 : Blocks := ep00000000110011011_0
private theorem idp00000000110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011001101.list =
    C ((2:ℤ)^41) * horner X vp00000000110011011.list + horner X ep00000000110011011.list := by
  exact edge_identity (B := (2:ℤ)^152) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110011011 : Branch 1 (-25386639/125000 : ℚ) vp0000000011001101 := by
  apply branch_checked idp00000000110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-25386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-25449139/62500 : ℚ) by norm_num]
  exact coverp00000000110011011
theorem coverp0000000011001101 : Covers (-25386639/125000 : ℚ) vp0000000011001101 := join_branches bp00000000110011010 bp00000000110011011
private noncomputable def vp0000000011001100_0 : Blocks := edgeBlocks% "full/vectors/0000000011001100-V-0000.bin"
noncomputable def vp0000000011001100 : Blocks := vp0000000011001100_0
theorem coverp0000000011001100 : Covers (-25261639/125000 : ℚ) vp0000000011001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001100110_0 : Blocks := edgeBlocks% "full/vectors/000000001100110-V-0000.bin"
noncomputable def vp000000001100110 : Blocks := vp000000001100110_0
private theorem bp0000000011001100 : Branch 0 (-25261639/250000 : ℚ) vp000000001100110 := by
  apply branch_left_normalized (c:=vp0000000011001100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-25261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-25261639/125000 : ℚ) by norm_num]
  exact coverp0000000011001100
private noncomputable def ep0000000011001101_0 : Blocks := edgeBlocks% "full/vectors/0000000011001101-E-0000.bin"
noncomputable def ep0000000011001101 : Blocks := ep0000000011001101_0
private theorem idp0000000011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001100110.list =
    C ((2:ℤ)^67) * horner X vp0000000011001101.list + horner X ep0000000011001101.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011001101 : Branch 1 (-25261639/250000 : ℚ) vp000000001100110 := by
  apply branch_checked idp0000000011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-25261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-25386639/125000 : ℚ) by norm_num]
  exact coverp0000000011001101
theorem coverp000000001100110 : Covers (-25261639/250000 : ℚ) vp000000001100110 := join_branches bp0000000011001100 bp0000000011001101
private noncomputable def vp00000000110011_0 : Blocks := edgeBlocks% "full/vectors/00000000110011-V-0000.bin"
noncomputable def vp00000000110011 : Blocks := vp00000000110011_0
private theorem bp000000001100110 : Branch 0 (-25261639/500000 : ℚ) vp00000000110011 := by
  apply branch_left_normalized (c:=vp000000001100110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-25261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-25261639/250000 : ℚ) by norm_num]
  exact coverp000000001100110
private noncomputable def ep000000001100111_0 : Blocks := edgeBlocks% "full/vectors/000000001100111-E-0000.bin"
noncomputable def ep000000001100111 : Blocks := ep000000001100111_0
private theorem idp000000001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110011.list =
    C ((2:ℤ)^116) * horner X vp000000001100111.list + horner X ep000000001100111.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001100111 : Branch 1 (-25261639/500000 : ℚ) vp00000000110011 := by
  apply branch_checked idp000000001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-25261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-25511639/250000 : ℚ) by norm_num]
  exact coverp000000001100111
theorem coverp00000000110011 : Covers (-25261639/500000 : ℚ) vp00000000110011 := join_branches bp000000001100110 bp000000001100111
private noncomputable def vp0000000011001011_0 : Blocks := edgeBlocks% "full/vectors/0000000011001011-V-0000.bin"
noncomputable def vp0000000011001011 : Blocks := vp0000000011001011_0
theorem coverp0000000011001011 : Covers (-25136639/125000 : ℚ) vp0000000011001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011001010_0 : Blocks := edgeBlocks% "full/vectors/0000000011001010-V-0000.bin"
noncomputable def vp0000000011001010 : Blocks := vp0000000011001010_0
theorem coverp0000000011001010 : Covers (-25011639/125000 : ℚ) vp0000000011001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001100101_0 : Blocks := edgeBlocks% "full/vectors/000000001100101-V-0000.bin"
noncomputable def vp000000001100101 : Blocks := vp000000001100101_0
private theorem bp0000000011001010 : Branch 0 (-25011639/250000 : ℚ) vp000000001100101 := by
  apply branch_left_normalized (c:=vp0000000011001010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-25011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-25011639/125000 : ℚ) by norm_num]
  exact coverp0000000011001010
private noncomputable def ep0000000011001011_0 : Blocks := edgeBlocks% "full/vectors/0000000011001011-E-0000.bin"
noncomputable def ep0000000011001011 : Blocks := ep0000000011001011_0
private theorem idp0000000011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001100101.list =
    C ((2:ℤ)^66) * horner X vp0000000011001011.list + horner X ep0000000011001011.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011001011 : Branch 1 (-25011639/250000 : ℚ) vp000000001100101 := by
  apply branch_checked idp0000000011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-25011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-25136639/125000 : ℚ) by norm_num]
  exact coverp0000000011001011
theorem coverp000000001100101 : Covers (-25011639/250000 : ℚ) vp000000001100101 := join_branches bp0000000011001010 bp0000000011001011
private noncomputable def vp0000000011001001_0 : Blocks := edgeBlocks% "full/vectors/0000000011001001-V-0000.bin"
noncomputable def vp0000000011001001 : Blocks := vp0000000011001001_0
theorem coverp0000000011001001 : Covers (-24886639/125000 : ℚ) vp0000000011001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011001000_0 : Blocks := edgeBlocks% "full/vectors/0000000011001000-V-0000.bin"
noncomputable def vp0000000011001000 : Blocks := vp0000000011001000_0
theorem coverp0000000011001000 : Covers (-24761639/125000 : ℚ) vp0000000011001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001100100_0 : Blocks := edgeBlocks% "full/vectors/000000001100100-V-0000.bin"
noncomputable def vp000000001100100 : Blocks := vp000000001100100_0
private theorem bp0000000011001000 : Branch 0 (-24761639/250000 : ℚ) vp000000001100100 := by
  apply branch_left_normalized (c:=vp0000000011001000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-24761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-24761639/125000 : ℚ) by norm_num]
  exact coverp0000000011001000
private noncomputable def ep0000000011001001_0 : Blocks := edgeBlocks% "full/vectors/0000000011001001-E-0000.bin"
noncomputable def ep0000000011001001 : Blocks := ep0000000011001001_0
private theorem idp0000000011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001100100.list =
    C ((2:ℤ)^66) * horner X vp0000000011001001.list + horner X ep0000000011001001.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011001001 : Branch 1 (-24761639/250000 : ℚ) vp000000001100100 := by
  apply branch_checked idp0000000011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-24761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-24886639/125000 : ℚ) by norm_num]
  exact coverp0000000011001001
theorem coverp000000001100100 : Covers (-24761639/250000 : ℚ) vp000000001100100 := join_branches bp0000000011001000 bp0000000011001001
private noncomputable def vp00000000110010_0 : Blocks := edgeBlocks% "full/vectors/00000000110010-V-0000.bin"
noncomputable def vp00000000110010 : Blocks := vp00000000110010_0
private theorem bp000000001100100 : Branch 0 (-24761639/500000 : ℚ) vp00000000110010 := by
  apply branch_left_normalized (c:=vp000000001100100) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-24761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-24761639/250000 : ℚ) by norm_num]
  exact coverp000000001100100
private noncomputable def ep000000001100101_0 : Blocks := edgeBlocks% "full/vectors/000000001100101-E-0000.bin"
noncomputable def ep000000001100101 : Blocks := ep000000001100101_0
private theorem idp000000001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110010.list =
    C ((2:ℤ)^115) * horner X vp000000001100101.list + horner X ep000000001100101.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001100101 : Branch 1 (-24761639/500000 : ℚ) vp00000000110010 := by
  apply branch_checked idp000000001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-24761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-25011639/250000 : ℚ) by norm_num]
  exact coverp000000001100101
theorem coverp00000000110010 : Covers (-24761639/500000 : ℚ) vp00000000110010 := join_branches bp000000001100100 bp000000001100101
private noncomputable def vp0000000011001_0 : Blocks := edgeBlocks% "full/vectors/0000000011001-V-0000.bin"
private noncomputable def vp0000000011001_1 : Blocks := edgeBlocks% "full/vectors/0000000011001-V-0001.bin"
noncomputable def vp0000000011001 : Blocks := (Blocks.join vp0000000011001_0 vp0000000011001_1)
private theorem bp00000000110010 : Branch 0 (-24761639/1000000 : ℚ) vp0000000011001 := by
  apply branch_left_normalized (c:=vp00000000110010) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-24761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-24761639/500000 : ℚ) by norm_num]
  exact coverp00000000110010
private noncomputable def ep00000000110011_0 : Blocks := edgeBlocks% "full/vectors/00000000110011-E-0000.bin"
private noncomputable def ep00000000110011_1 : Blocks := edgeBlocks% "full/vectors/00000000110011-E-0001.bin"
noncomputable def ep00000000110011 : Blocks := (Blocks.join ep00000000110011_0 ep00000000110011_1)
private theorem idp00000000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011001.list =
    C ((2:ℤ)^214) * horner X vp00000000110011.list + horner X ep00000000110011.list := by
  exact edge_identity (B := (2:ℤ)^411) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110011 : Branch 1 (-24761639/1000000 : ℚ) vp0000000011001 := by
  apply branch_checked idp00000000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-24761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-25261639/500000 : ℚ) by norm_num]
  exact coverp00000000110011
theorem coverp0000000011001 : Covers (-24761639/1000000 : ℚ) vp0000000011001 := join_branches bp00000000110010 bp00000000110011
private noncomputable def vp0000000011000111_0 : Blocks := edgeBlocks% "full/vectors/0000000011000111-V-0000.bin"
noncomputable def vp0000000011000111 : Blocks := vp0000000011000111_0
theorem coverp0000000011000111 : Covers (-24636639/125000 : ℚ) vp0000000011000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011000110_0 : Blocks := edgeBlocks% "full/vectors/0000000011000110-V-0000.bin"
noncomputable def vp0000000011000110 : Blocks := vp0000000011000110_0
theorem coverp0000000011000110 : Covers (-24511639/125000 : ℚ) vp0000000011000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001100011_0 : Blocks := edgeBlocks% "full/vectors/000000001100011-V-0000.bin"
noncomputable def vp000000001100011 : Blocks := vp000000001100011_0
private theorem bp0000000011000110 : Branch 0 (-24511639/250000 : ℚ) vp000000001100011 := by
  apply branch_left_normalized (c:=vp0000000011000110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-24511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-24511639/125000 : ℚ) by norm_num]
  exact coverp0000000011000110
private noncomputable def ep0000000011000111_0 : Blocks := edgeBlocks% "full/vectors/0000000011000111-E-0000.bin"
noncomputable def ep0000000011000111 : Blocks := ep0000000011000111_0
private theorem idp0000000011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001100011.list =
    C ((2:ℤ)^65) * horner X vp0000000011000111.list + horner X ep0000000011000111.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011000111 : Branch 1 (-24511639/250000 : ℚ) vp000000001100011 := by
  apply branch_checked idp0000000011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-24511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-24636639/125000 : ℚ) by norm_num]
  exact coverp0000000011000111
theorem coverp000000001100011 : Covers (-24511639/250000 : ℚ) vp000000001100011 := join_branches bp0000000011000110 bp0000000011000111
private noncomputable def vp0000000011000101_0 : Blocks := edgeBlocks% "full/vectors/0000000011000101-V-0000.bin"
noncomputable def vp0000000011000101 : Blocks := vp0000000011000101_0
theorem coverp0000000011000101 : Covers (-24386639/125000 : ℚ) vp0000000011000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011000100_0 : Blocks := edgeBlocks% "full/vectors/0000000011000100-V-0000.bin"
noncomputable def vp0000000011000100 : Blocks := vp0000000011000100_0
theorem coverp0000000011000100 : Covers (-24261639/125000 : ℚ) vp0000000011000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001100010_0 : Blocks := edgeBlocks% "full/vectors/000000001100010-V-0000.bin"
noncomputable def vp000000001100010 : Blocks := vp000000001100010_0
private theorem bp0000000011000100 : Branch 0 (-24261639/250000 : ℚ) vp000000001100010 := by
  apply branch_left_normalized (c:=vp0000000011000100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-24261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-24261639/125000 : ℚ) by norm_num]
  exact coverp0000000011000100
private noncomputable def ep0000000011000101_0 : Blocks := edgeBlocks% "full/vectors/0000000011000101-E-0000.bin"
noncomputable def ep0000000011000101 : Blocks := ep0000000011000101_0
private theorem idp0000000011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001100010.list =
    C ((2:ℤ)^65) * horner X vp0000000011000101.list + horner X ep0000000011000101.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011000101 : Branch 1 (-24261639/250000 : ℚ) vp000000001100010 := by
  apply branch_checked idp0000000011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-24261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-24386639/125000 : ℚ) by norm_num]
  exact coverp0000000011000101
theorem coverp000000001100010 : Covers (-24261639/250000 : ℚ) vp000000001100010 := join_branches bp0000000011000100 bp0000000011000101
private noncomputable def vp00000000110001_0 : Blocks := edgeBlocks% "full/vectors/00000000110001-V-0000.bin"
noncomputable def vp00000000110001 : Blocks := vp00000000110001_0
private theorem bp000000001100010 : Branch 0 (-24261639/500000 : ℚ) vp00000000110001 := by
  apply branch_left_normalized (c:=vp000000001100010) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-24261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-24261639/250000 : ℚ) by norm_num]
  exact coverp000000001100010
private noncomputable def ep000000001100011_0 : Blocks := edgeBlocks% "full/vectors/000000001100011-E-0000.bin"
noncomputable def ep000000001100011 : Blocks := ep000000001100011_0
private theorem idp000000001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110001.list =
    C ((2:ℤ)^117) * horner X vp000000001100011.list + horner X ep000000001100011.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001100011 : Branch 1 (-24261639/500000 : ℚ) vp00000000110001 := by
  apply branch_checked idp000000001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-24261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-24511639/250000 : ℚ) by norm_num]
  exact coverp000000001100011
theorem coverp00000000110001 : Covers (-24261639/500000 : ℚ) vp00000000110001 := join_branches bp000000001100010 bp000000001100011
private noncomputable def vp0000000011000011_0 : Blocks := edgeBlocks% "full/vectors/0000000011000011-V-0000.bin"
noncomputable def vp0000000011000011 : Blocks := vp0000000011000011_0
theorem coverp0000000011000011 : Covers (-24136639/125000 : ℚ) vp0000000011000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011000010_0 : Blocks := edgeBlocks% "full/vectors/0000000011000010-V-0000.bin"
noncomputable def vp0000000011000010 : Blocks := vp0000000011000010_0
theorem coverp0000000011000010 : Covers (-24011639/125000 : ℚ) vp0000000011000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001100001_0 : Blocks := edgeBlocks% "full/vectors/000000001100001-V-0000.bin"
noncomputable def vp000000001100001 : Blocks := vp000000001100001_0
private theorem bp0000000011000010 : Branch 0 (-24011639/250000 : ℚ) vp000000001100001 := by
  apply branch_left_normalized (c:=vp0000000011000010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-24011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-24011639/125000 : ℚ) by norm_num]
  exact coverp0000000011000010
private noncomputable def ep0000000011000011_0 : Blocks := edgeBlocks% "full/vectors/0000000011000011-E-0000.bin"
noncomputable def ep0000000011000011 : Blocks := ep0000000011000011_0
private theorem idp0000000011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001100001.list =
    C ((2:ℤ)^66) * horner X vp0000000011000011.list + horner X ep0000000011000011.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011000011 : Branch 1 (-24011639/250000 : ℚ) vp000000001100001 := by
  apply branch_checked idp0000000011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-24011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-24136639/125000 : ℚ) by norm_num]
  exact coverp0000000011000011
theorem coverp000000001100001 : Covers (-24011639/250000 : ℚ) vp000000001100001 := join_branches bp0000000011000010 bp0000000011000011
private noncomputable def vp0000000011000001_0 : Blocks := edgeBlocks% "full/vectors/0000000011000001-V-0000.bin"
noncomputable def vp0000000011000001 : Blocks := vp0000000011000001_0
theorem coverp0000000011000001 : Covers (-23886639/125000 : ℚ) vp0000000011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000011000000_0 : Blocks := edgeBlocks% "full/vectors/0000000011000000-V-0000.bin"
noncomputable def vp0000000011000000 : Blocks := vp0000000011000000_0
theorem coverp0000000011000000 : Covers (-23761639/125000 : ℚ) vp0000000011000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000001100000_0 : Blocks := edgeBlocks% "full/vectors/000000001100000-V-0000.bin"
noncomputable def vp000000001100000 : Blocks := vp000000001100000_0
private theorem bp0000000011000000 : Branch 0 (-23761639/250000 : ℚ) vp000000001100000 := by
  apply branch_left_normalized (c:=vp0000000011000000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-23761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-23761639/125000 : ℚ) by norm_num]
  exact coverp0000000011000000
private noncomputable def ep0000000011000001_0 : Blocks := edgeBlocks% "full/vectors/0000000011000001-E-0000.bin"
noncomputable def ep0000000011000001 : Blocks := ep0000000011000001_0
private theorem idp0000000011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001100000.list =
    C ((2:ℤ)^66) * horner X vp0000000011000001.list + horner X ep0000000011000001.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011000001 : Branch 1 (-23761639/250000 : ℚ) vp000000001100000 := by
  apply branch_checked idp0000000011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-23761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-23886639/125000 : ℚ) by norm_num]
  exact coverp0000000011000001
theorem coverp000000001100000 : Covers (-23761639/250000 : ℚ) vp000000001100000 := join_branches bp0000000011000000 bp0000000011000001
private noncomputable def vp00000000110000_0 : Blocks := edgeBlocks% "full/vectors/00000000110000-V-0000.bin"
noncomputable def vp00000000110000 : Blocks := vp00000000110000_0
private theorem bp000000001100000 : Branch 0 (-23761639/500000 : ℚ) vp00000000110000 := by
  apply branch_left_normalized (c:=vp000000001100000) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-23761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-23761639/250000 : ℚ) by norm_num]
  exact coverp000000001100000
private noncomputable def ep000000001100001_0 : Blocks := edgeBlocks% "full/vectors/000000001100001-E-0000.bin"
noncomputable def ep000000001100001 : Blocks := ep000000001100001_0
private theorem idp000000001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110000.list =
    C ((2:ℤ)^117) * horner X vp000000001100001.list + horner X ep000000001100001.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001100001 : Branch 1 (-23761639/500000 : ℚ) vp00000000110000 := by
  apply branch_checked idp000000001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-23761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-24011639/250000 : ℚ) by norm_num]
  exact coverp000000001100001
theorem coverp00000000110000 : Covers (-23761639/500000 : ℚ) vp00000000110000 := join_branches bp000000001100000 bp000000001100001
private noncomputable def vp0000000011000_0 : Blocks := edgeBlocks% "full/vectors/0000000011000-V-0000.bin"
private noncomputable def vp0000000011000_1 : Blocks := edgeBlocks% "full/vectors/0000000011000-V-0001.bin"
noncomputable def vp0000000011000 : Blocks := (Blocks.join vp0000000011000_0 vp0000000011000_1)
private theorem bp00000000110000 : Branch 0 (-23761639/1000000 : ℚ) vp0000000011000 := by
  apply branch_left_normalized (c:=vp00000000110000) (k:=0) (m:=115) (by decide +kernel)
  rw [show 2*(-23761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-23761639/500000 : ℚ) by norm_num]
  exact coverp00000000110000
private noncomputable def ep00000000110001_0 : Blocks := edgeBlocks% "full/vectors/00000000110001-E-0000.bin"
private noncomputable def ep00000000110001_1 : Blocks := edgeBlocks% "full/vectors/00000000110001-E-0001.bin"
noncomputable def ep00000000110001 : Blocks := (Blocks.join ep00000000110001_0 ep00000000110001_1)
private theorem idp00000000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011000.list =
    C ((2:ℤ)^218) * horner X vp00000000110001.list + horner X ep00000000110001.list := by
  exact edge_identity (B := (2:ℤ)^412) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000110001 : Branch 1 (-23761639/1000000 : ℚ) vp0000000011000 := by
  apply branch_checked idp00000000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-23761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-24261639/500000 : ℚ) by norm_num]
  exact coverp00000000110001
theorem coverp0000000011000 : Covers (-23761639/1000000 : ℚ) vp0000000011000 := join_branches bp00000000110000 bp00000000110001
private noncomputable def vp000000001100_0 : Blocks := edgeBlocks% "full/vectors/000000001100-V-0000.bin"
private noncomputable def vp000000001100_1 : Blocks := edgeBlocks% "full/vectors/000000001100-V-0001.bin"
private noncomputable def vp000000001100_2 : Blocks := edgeBlocks% "full/vectors/000000001100-V-0002.bin"
private noncomputable def vp000000001100_3 : Blocks := edgeBlocks% "full/vectors/000000001100-V-0003.bin"
noncomputable def vp000000001100 : Blocks := (Blocks.join (Blocks.join vp000000001100_0 vp000000001100_1) (Blocks.join vp000000001100_2 vp000000001100_3))
private theorem bp0000000011000 : Branch 0 (-23761639/2000000 : ℚ) vp000000001100 := by
  apply branch_left_normalized (c:=vp0000000011000) (k:=0) (m:=215) (by decide +kernel)
  rw [show 2*(-23761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-23761639/1000000 : ℚ) by norm_num]
  exact coverp0000000011000
private noncomputable def ep0000000011001_0 : Blocks := edgeBlocks% "full/vectors/0000000011001-E-0000.bin"
private noncomputable def ep0000000011001_1 : Blocks := edgeBlocks% "full/vectors/0000000011001-E-0001.bin"
private noncomputable def ep0000000011001_2 : Blocks := edgeBlocks% "full/vectors/0000000011001-E-0002.bin"
private noncomputable def ep0000000011001_3 : Blocks := edgeBlocks% "full/vectors/0000000011001-E-0003.bin"
noncomputable def ep0000000011001 : Blocks := (Blocks.join (Blocks.join ep0000000011001_0 ep0000000011001_1) (Blocks.join ep0000000011001_2 ep0000000011001_3))
private theorem idp0000000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000001100.list =
    C ((2:ℤ)^418) * horner X vp0000000011001.list + horner X ep0000000011001.list := by
  exact edge_identity (B := (2:ℤ)^717) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000011001 : Branch 1 (-23761639/2000000 : ℚ) vp000000001100 := by
  apply branch_checked idp0000000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-23761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-24761639/1000000 : ℚ) by norm_num]
  exact coverp0000000011001
theorem coverp000000001100 : Covers (-23761639/2000000 : ℚ) vp000000001100 := join_branches bp0000000011000 bp0000000011001
private noncomputable def vp00000000110_0 : Blocks := edgeBlocks% "full/vectors/00000000110-V-0000.bin"
private noncomputable def vp00000000110_1 : Blocks := edgeBlocks% "full/vectors/00000000110-V-0001.bin"
private noncomputable def vp00000000110_2 : Blocks := edgeBlocks% "full/vectors/00000000110-V-0002.bin"
private noncomputable def vp00000000110_3 : Blocks := edgeBlocks% "full/vectors/00000000110-V-0003.bin"
private noncomputable def vp00000000110_4 : Blocks := edgeBlocks% "full/vectors/00000000110-V-0004.bin"
private noncomputable def vp00000000110_5 : Blocks := edgeBlocks% "full/vectors/00000000110-V-0005.bin"
private noncomputable def vp00000000110_6 : Blocks := edgeBlocks% "full/vectors/00000000110-V-0006.bin"
noncomputable def vp00000000110 : Blocks := (Blocks.join (Blocks.join vp00000000110_0 (Blocks.join vp00000000110_1 vp00000000110_2)) (Blocks.join (Blocks.join vp00000000110_3 vp00000000110_4) (Blocks.join vp00000000110_5 vp00000000110_6)))
private theorem bp000000001100 : Branch 0 (-23761639/4000000 : ℚ) vp00000000110 := by
  apply branch_left_normalized (c:=vp000000001100) (k:=0) (m:=414) (by decide +kernel)
  rw [show 2*(-23761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-23761639/2000000 : ℚ) by norm_num]
  exact coverp000000001100
private noncomputable def ep000000001101_0 : Blocks := edgeBlocks% "full/vectors/000000001101-E-0000.bin"
private noncomputable def ep000000001101_1 : Blocks := edgeBlocks% "full/vectors/000000001101-E-0001.bin"
private noncomputable def ep000000001101_2 : Blocks := edgeBlocks% "full/vectors/000000001101-E-0002.bin"
private noncomputable def ep000000001101_3 : Blocks := edgeBlocks% "full/vectors/000000001101-E-0003.bin"
private noncomputable def ep000000001101_4 : Blocks := edgeBlocks% "full/vectors/000000001101-E-0004.bin"
private noncomputable def ep000000001101_5 : Blocks := edgeBlocks% "full/vectors/000000001101-E-0005.bin"
private noncomputable def ep000000001101_6 : Blocks := edgeBlocks% "full/vectors/000000001101-E-0006.bin"
noncomputable def ep000000001101 : Blocks := (Blocks.join (Blocks.join ep000000001101_0 (Blocks.join ep000000001101_1 ep000000001101_2)) (Blocks.join (Blocks.join ep000000001101_3 ep000000001101_4) (Blocks.join ep000000001101_5 ep000000001101_6)))
private theorem idp000000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000110.list =
    C ((2:ℤ)^810) * horner X vp000000001101.list + horner X ep000000001101.list := by
  exact edge_identity (B := (2:ℤ)^1323) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000001101 : Branch 1 (-23761639/4000000 : ℚ) vp00000000110 := by
  apply branch_checked idp000000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-23761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-25761639/2000000 : ℚ) by norm_num]
  exact coverp000000001101
theorem coverp00000000110 : Covers (-23761639/4000000 : ℚ) vp00000000110 := join_branches bp000000001100 bp000000001101
private noncomputable def vp0000000011_0 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0000.bin"
private noncomputable def vp0000000011_1 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0001.bin"
private noncomputable def vp0000000011_2 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0002.bin"
private noncomputable def vp0000000011_3 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0003.bin"
private noncomputable def vp0000000011_4 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0004.bin"
private noncomputable def vp0000000011_5 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0005.bin"
private noncomputable def vp0000000011_6 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0006.bin"
private noncomputable def vp0000000011_7 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0007.bin"
private noncomputable def vp0000000011_8 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0008.bin"
private noncomputable def vp0000000011_9 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0009.bin"
private noncomputable def vp0000000011_10 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0010.bin"
private noncomputable def vp0000000011_11 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0011.bin"
private noncomputable def vp0000000011_12 : Blocks := edgeBlocks% "full/vectors/0000000011-V-0012.bin"
noncomputable def vp0000000011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0000000011_0 (Blocks.join vp0000000011_1 vp0000000011_2)) (Blocks.join vp0000000011_3 (Blocks.join vp0000000011_4 vp0000000011_5))) (Blocks.join (Blocks.join vp0000000011_6 (Blocks.join vp0000000011_7 vp0000000011_8)) (Blocks.join (Blocks.join vp0000000011_9 vp0000000011_10) (Blocks.join vp0000000011_11 vp0000000011_12))))
private theorem bp00000000110 : Branch 0 (-23761639/8000000 : ℚ) vp0000000011 := by
  apply branch_left_normalized (c:=vp00000000110) (k:=0) (m:=808) (by decide +kernel)
  rw [show 2*(-23761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-23761639/4000000 : ℚ) by norm_num]
  exact coverp00000000110
private noncomputable def ep00000000111_0 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0000.bin"
private noncomputable def ep00000000111_1 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0001.bin"
private noncomputable def ep00000000111_2 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0002.bin"
private noncomputable def ep00000000111_3 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0003.bin"
private noncomputable def ep00000000111_4 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0004.bin"
private noncomputable def ep00000000111_5 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0005.bin"
private noncomputable def ep00000000111_6 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0006.bin"
private noncomputable def ep00000000111_7 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0007.bin"
private noncomputable def ep00000000111_8 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0008.bin"
private noncomputable def ep00000000111_9 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0009.bin"
private noncomputable def ep00000000111_10 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0010.bin"
private noncomputable def ep00000000111_11 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0011.bin"
private noncomputable def ep00000000111_12 : Blocks := edgeBlocks% "full/vectors/00000000111-E-0012.bin"
noncomputable def ep00000000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00000000111_0 (Blocks.join ep00000000111_1 ep00000000111_2)) (Blocks.join ep00000000111_3 (Blocks.join ep00000000111_4 ep00000000111_5))) (Blocks.join (Blocks.join ep00000000111_6 (Blocks.join ep00000000111_7 ep00000000111_8)) (Blocks.join (Blocks.join ep00000000111_9 ep00000000111_10) (Blocks.join ep00000000111_11 ep00000000111_12))))
private theorem idp00000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000011.list =
    C ((2:ℤ)^1598) * horner X vp00000000111.list + horner X ep00000000111.list := by
  exact edge_identity (B := (2:ℤ)^2518) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000111 : Branch 1 (-23761639/8000000 : ℚ) vp0000000011 := by
  apply branch_checked idp00000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-23761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-27761639/4000000 : ℚ) by norm_num]
  exact coverp00000000111
theorem coverp0000000011 : Covers (-23761639/8000000 : ℚ) vp0000000011 := join_branches bp00000000110 bp00000000111
end NextProof.EdgeFull

