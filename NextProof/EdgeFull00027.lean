import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00026

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000000010011111_0 : Blocks := edgeBlocks% "full/vectors/000000010011111-V-0000.bin"
noncomputable def vp000000010011111 : Blocks := vp000000010011111_0
theorem coverp000000010011111 : Covers (-39511639/250000 : ℚ) vp000000010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010011110_0 : Blocks := edgeBlocks% "full/vectors/000000010011110-V-0000.bin"
noncomputable def vp000000010011110 : Blocks := vp000000010011110_0
theorem coverp000000010011110 : Covers (-39261639/250000 : ℚ) vp000000010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001001111_0 : Blocks := edgeBlocks% "full/vectors/00000001001111-V-0000.bin"
noncomputable def vp00000001001111 : Blocks := vp00000001001111_0
private theorem bp000000010011110 : Branch 0 (-39261639/500000 : ℚ) vp00000001001111 := by
  apply branch_left_normalized (c:=vp000000010011110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-39261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-39261639/250000 : ℚ) by norm_num]
  exact coverp000000010011110
private noncomputable def ep000000010011111_0 : Blocks := edgeBlocks% "full/vectors/000000010011111-E-0000.bin"
noncomputable def ep000000010011111 : Blocks := ep000000010011111_0
private theorem idp000000010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001001111.list =
    C ((2:ℤ)^95) * horner X vp000000010011111.list + horner X ep000000010011111.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010011111 : Branch 1 (-39261639/500000 : ℚ) vp00000001001111 := by
  apply branch_checked idp000000010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-39261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-39511639/250000 : ℚ) by norm_num]
  exact coverp000000010011111
theorem coverp00000001001111 : Covers (-39261639/500000 : ℚ) vp00000001001111 := join_branches bp000000010011110 bp000000010011111
private noncomputable def vp000000010011101_0 : Blocks := edgeBlocks% "full/vectors/000000010011101-V-0000.bin"
noncomputable def vp000000010011101 : Blocks := vp000000010011101_0
theorem coverp000000010011101 : Covers (-39011639/250000 : ℚ) vp000000010011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010011100_0 : Blocks := edgeBlocks% "full/vectors/000000010011100-V-0000.bin"
noncomputable def vp000000010011100 : Blocks := vp000000010011100_0
theorem coverp000000010011100 : Covers (-38761639/250000 : ℚ) vp000000010011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001001110_0 : Blocks := edgeBlocks% "full/vectors/00000001001110-V-0000.bin"
noncomputable def vp00000001001110 : Blocks := vp00000001001110_0
private theorem bp000000010011100 : Branch 0 (-38761639/500000 : ℚ) vp00000001001110 := by
  apply branch_left_normalized (c:=vp000000010011100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-38761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-38761639/250000 : ℚ) by norm_num]
  exact coverp000000010011100
private noncomputable def ep000000010011101_0 : Blocks := edgeBlocks% "full/vectors/000000010011101-E-0000.bin"
noncomputable def ep000000010011101 : Blocks := ep000000010011101_0
private theorem idp000000010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001001110.list =
    C ((2:ℤ)^95) * horner X vp000000010011101.list + horner X ep000000010011101.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010011101 : Branch 1 (-38761639/500000 : ℚ) vp00000001001110 := by
  apply branch_checked idp000000010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-38761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-39011639/250000 : ℚ) by norm_num]
  exact coverp000000010011101
theorem coverp00000001001110 : Covers (-38761639/500000 : ℚ) vp00000001001110 := join_branches bp000000010011100 bp000000010011101
private noncomputable def vp0000000100111_0 : Blocks := edgeBlocks% "full/vectors/0000000100111-V-0000.bin"
private noncomputable def vp0000000100111_1 : Blocks := edgeBlocks% "full/vectors/0000000100111-V-0001.bin"
noncomputable def vp0000000100111 : Blocks := (Blocks.join vp0000000100111_0 vp0000000100111_1)
private theorem bp00000001001110 : Branch 0 (-38761639/1000000 : ℚ) vp0000000100111 := by
  apply branch_left_normalized (c:=vp00000001001110) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-38761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-38761639/500000 : ℚ) by norm_num]
  exact coverp00000001001110
private noncomputable def ep00000001001111_0 : Blocks := edgeBlocks% "full/vectors/00000001001111-E-0000.bin"
private noncomputable def ep00000001001111_1 : Blocks := edgeBlocks% "full/vectors/00000001001111-E-0001.bin"
noncomputable def ep00000001001111 : Blocks := (Blocks.join ep00000001001111_0 ep00000001001111_1)
private theorem idp00000001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100111.list =
    C ((2:ℤ)^176) * horner X vp00000001001111.list + horner X ep00000001001111.list := by
  exact edge_identity (B := (2:ℤ)^345) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001001111 : Branch 1 (-38761639/1000000 : ℚ) vp0000000100111 := by
  apply branch_checked idp00000001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-38761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-39261639/500000 : ℚ) by norm_num]
  exact coverp00000001001111
theorem coverp0000000100111 : Covers (-38761639/1000000 : ℚ) vp0000000100111 := join_branches bp00000001001110 bp00000001001111
private noncomputable def vp000000010011011_0 : Blocks := edgeBlocks% "full/vectors/000000010011011-V-0000.bin"
noncomputable def vp000000010011011 : Blocks := vp000000010011011_0
theorem coverp000000010011011 : Covers (-38511639/250000 : ℚ) vp000000010011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010011010_0 : Blocks := edgeBlocks% "full/vectors/000000010011010-V-0000.bin"
noncomputable def vp000000010011010 : Blocks := vp000000010011010_0
theorem coverp000000010011010 : Covers (-38261639/250000 : ℚ) vp000000010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001001101_0 : Blocks := edgeBlocks% "full/vectors/00000001001101-V-0000.bin"
noncomputable def vp00000001001101 : Blocks := vp00000001001101_0
private theorem bp000000010011010 : Branch 0 (-38261639/500000 : ℚ) vp00000001001101 := by
  apply branch_left_normalized (c:=vp000000010011010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-38261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-38261639/250000 : ℚ) by norm_num]
  exact coverp000000010011010
private noncomputable def ep000000010011011_0 : Blocks := edgeBlocks% "full/vectors/000000010011011-E-0000.bin"
noncomputable def ep000000010011011 : Blocks := ep000000010011011_0
private theorem idp000000010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001001101.list =
    C ((2:ℤ)^95) * horner X vp000000010011011.list + horner X ep000000010011011.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010011011 : Branch 1 (-38261639/500000 : ℚ) vp00000001001101 := by
  apply branch_checked idp000000010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-38261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-38511639/250000 : ℚ) by norm_num]
  exact coverp000000010011011
theorem coverp00000001001101 : Covers (-38261639/500000 : ℚ) vp00000001001101 := join_branches bp000000010011010 bp000000010011011
private noncomputable def vp000000010011001_0 : Blocks := edgeBlocks% "full/vectors/000000010011001-V-0000.bin"
noncomputable def vp000000010011001 : Blocks := vp000000010011001_0
theorem coverp000000010011001 : Covers (-38011639/250000 : ℚ) vp000000010011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010011000_0 : Blocks := edgeBlocks% "full/vectors/000000010011000-V-0000.bin"
noncomputable def vp000000010011000 : Blocks := vp000000010011000_0
theorem coverp000000010011000 : Covers (-37761639/250000 : ℚ) vp000000010011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001001100_0 : Blocks := edgeBlocks% "full/vectors/00000001001100-V-0000.bin"
noncomputable def vp00000001001100 : Blocks := vp00000001001100_0
private theorem bp000000010011000 : Branch 0 (-37761639/500000 : ℚ) vp00000001001100 := by
  apply branch_left_normalized (c:=vp000000010011000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-37761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-37761639/250000 : ℚ) by norm_num]
  exact coverp000000010011000
private noncomputable def ep000000010011001_0 : Blocks := edgeBlocks% "full/vectors/000000010011001-E-0000.bin"
noncomputable def ep000000010011001 : Blocks := ep000000010011001_0
private theorem idp000000010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001001100.list =
    C ((2:ℤ)^96) * horner X vp000000010011001.list + horner X ep000000010011001.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010011001 : Branch 1 (-37761639/500000 : ℚ) vp00000001001100 := by
  apply branch_checked idp000000010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-37761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-38011639/250000 : ℚ) by norm_num]
  exact coverp000000010011001
theorem coverp00000001001100 : Covers (-37761639/500000 : ℚ) vp00000001001100 := join_branches bp000000010011000 bp000000010011001
private noncomputable def vp0000000100110_0 : Blocks := edgeBlocks% "full/vectors/0000000100110-V-0000.bin"
private noncomputable def vp0000000100110_1 : Blocks := edgeBlocks% "full/vectors/0000000100110-V-0001.bin"
noncomputable def vp0000000100110 : Blocks := (Blocks.join vp0000000100110_0 vp0000000100110_1)
private theorem bp00000001001100 : Branch 0 (-37761639/1000000 : ℚ) vp0000000100110 := by
  apply branch_left_normalized (c:=vp00000001001100) (k:=0) (m:=93) (by decide +kernel)
  rw [show 2*(-37761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-37761639/500000 : ℚ) by norm_num]
  exact coverp00000001001100
private noncomputable def ep00000001001101_0 : Blocks := edgeBlocks% "full/vectors/00000001001101-E-0000.bin"
private noncomputable def ep00000001001101_1 : Blocks := edgeBlocks% "full/vectors/00000001001101-E-0001.bin"
noncomputable def ep00000001001101 : Blocks := (Blocks.join ep00000001001101_0 ep00000001001101_1)
private theorem idp00000001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100110.list =
    C ((2:ℤ)^178) * horner X vp00000001001101.list + horner X ep00000001001101.list := by
  exact edge_identity (B := (2:ℤ)^349) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001001101 : Branch 1 (-37761639/1000000 : ℚ) vp0000000100110 := by
  apply branch_checked idp00000001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-37761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-38261639/500000 : ℚ) by norm_num]
  exact coverp00000001001101
theorem coverp0000000100110 : Covers (-37761639/1000000 : ℚ) vp0000000100110 := join_branches bp00000001001100 bp00000001001101
private noncomputable def vp000000010011_0 : Blocks := edgeBlocks% "full/vectors/000000010011-V-0000.bin"
private noncomputable def vp000000010011_1 : Blocks := edgeBlocks% "full/vectors/000000010011-V-0001.bin"
private noncomputable def vp000000010011_2 : Blocks := edgeBlocks% "full/vectors/000000010011-V-0002.bin"
noncomputable def vp000000010011 : Blocks := (Blocks.join vp000000010011_0 (Blocks.join vp000000010011_1 vp000000010011_2))
private theorem bp0000000100110 : Branch 0 (-37761639/2000000 : ℚ) vp000000010011 := by
  apply branch_left_normalized (c:=vp0000000100110) (k:=0) (m:=173) (by decide +kernel)
  rw [show 2*(-37761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-37761639/1000000 : ℚ) by norm_num]
  exact coverp0000000100110
private noncomputable def ep0000000100111_0 : Blocks := edgeBlocks% "full/vectors/0000000100111-E-0000.bin"
private noncomputable def ep0000000100111_1 : Blocks := edgeBlocks% "full/vectors/0000000100111-E-0001.bin"
private noncomputable def ep0000000100111_2 : Blocks := edgeBlocks% "full/vectors/0000000100111-E-0002.bin"
noncomputable def ep0000000100111 : Blocks := (Blocks.join ep0000000100111_0 (Blocks.join ep0000000100111_1 ep0000000100111_2))
private theorem idp0000000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010011.list =
    C ((2:ℤ)^340) * horner X vp0000000100111.list + horner X ep0000000100111.list := by
  exact edge_identity (B := (2:ℤ)^592) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100111 : Branch 1 (-37761639/2000000 : ℚ) vp000000010011 := by
  apply branch_checked idp0000000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-37761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-38761639/1000000 : ℚ) by norm_num]
  exact coverp0000000100111
theorem coverp000000010011 : Covers (-37761639/2000000 : ℚ) vp000000010011 := join_branches bp0000000100110 bp0000000100111
private noncomputable def vp000000010010111_0 : Blocks := edgeBlocks% "full/vectors/000000010010111-V-0000.bin"
noncomputable def vp000000010010111 : Blocks := vp000000010010111_0
theorem coverp000000010010111 : Covers (-37511639/250000 : ℚ) vp000000010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010010110_0 : Blocks := edgeBlocks% "full/vectors/000000010010110-V-0000.bin"
noncomputable def vp000000010010110 : Blocks := vp000000010010110_0
theorem coverp000000010010110 : Covers (-37261639/250000 : ℚ) vp000000010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001001011_0 : Blocks := edgeBlocks% "full/vectors/00000001001011-V-0000.bin"
noncomputable def vp00000001001011 : Blocks := vp00000001001011_0
private theorem bp000000010010110 : Branch 0 (-37261639/500000 : ℚ) vp00000001001011 := by
  apply branch_left_normalized (c:=vp000000010010110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-37261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-37261639/250000 : ℚ) by norm_num]
  exact coverp000000010010110
private noncomputable def ep000000010010111_0 : Blocks := edgeBlocks% "full/vectors/000000010010111-E-0000.bin"
noncomputable def ep000000010010111 : Blocks := ep000000010010111_0
private theorem idp000000010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001001011.list =
    C ((2:ℤ)^98) * horner X vp000000010010111.list + horner X ep000000010010111.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010010111 : Branch 1 (-37261639/500000 : ℚ) vp00000001001011 := by
  apply branch_checked idp000000010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-37261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-37511639/250000 : ℚ) by norm_num]
  exact coverp000000010010111
theorem coverp00000001001011 : Covers (-37261639/500000 : ℚ) vp00000001001011 := join_branches bp000000010010110 bp000000010010111
private noncomputable def vp000000010010101_0 : Blocks := edgeBlocks% "full/vectors/000000010010101-V-0000.bin"
noncomputable def vp000000010010101 : Blocks := vp000000010010101_0
theorem coverp000000010010101 : Covers (-37011639/250000 : ℚ) vp000000010010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010010100_0 : Blocks := edgeBlocks% "full/vectors/000000010010100-V-0000.bin"
noncomputable def vp000000010010100 : Blocks := vp000000010010100_0
theorem coverp000000010010100 : Covers (-36761639/250000 : ℚ) vp000000010010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001001010_0 : Blocks := edgeBlocks% "full/vectors/00000001001010-V-0000.bin"
noncomputable def vp00000001001010 : Blocks := vp00000001001010_0
private theorem bp000000010010100 : Branch 0 (-36761639/500000 : ℚ) vp00000001001010 := by
  apply branch_left_normalized (c:=vp000000010010100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-36761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-36761639/250000 : ℚ) by norm_num]
  exact coverp000000010010100
private noncomputable def ep000000010010101_0 : Blocks := edgeBlocks% "full/vectors/000000010010101-E-0000.bin"
noncomputable def ep000000010010101 : Blocks := ep000000010010101_0
private theorem idp000000010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001001010.list =
    C ((2:ℤ)^99) * horner X vp000000010010101.list + horner X ep000000010010101.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010010101 : Branch 1 (-36761639/500000 : ℚ) vp00000001001010 := by
  apply branch_checked idp000000010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-36761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-37011639/250000 : ℚ) by norm_num]
  exact coverp000000010010101
theorem coverp00000001001010 : Covers (-36761639/500000 : ℚ) vp00000001001010 := join_branches bp000000010010100 bp000000010010101
private noncomputable def vp0000000100101_0 : Blocks := edgeBlocks% "full/vectors/0000000100101-V-0000.bin"
private noncomputable def vp0000000100101_1 : Blocks := edgeBlocks% "full/vectors/0000000100101-V-0001.bin"
noncomputable def vp0000000100101 : Blocks := (Blocks.join vp0000000100101_0 vp0000000100101_1)
private theorem bp00000001001010 : Branch 0 (-36761639/1000000 : ℚ) vp0000000100101 := by
  apply branch_left_normalized (c:=vp00000001001010) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-36761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-36761639/500000 : ℚ) by norm_num]
  exact coverp00000001001010
private noncomputable def ep00000001001011_0 : Blocks := edgeBlocks% "full/vectors/00000001001011-E-0000.bin"
private noncomputable def ep00000001001011_1 : Blocks := edgeBlocks% "full/vectors/00000001001011-E-0001.bin"
noncomputable def ep00000001001011 : Blocks := (Blocks.join ep00000001001011_0 ep00000001001011_1)
private theorem idp00000001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100101.list =
    C ((2:ℤ)^182) * horner X vp00000001001011.list + horner X ep00000001001011.list := by
  exact edge_identity (B := (2:ℤ)^355) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001001011 : Branch 1 (-36761639/1000000 : ℚ) vp0000000100101 := by
  apply branch_checked idp00000001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-36761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-37261639/500000 : ℚ) by norm_num]
  exact coverp00000001001011
theorem coverp0000000100101 : Covers (-36761639/1000000 : ℚ) vp0000000100101 := join_branches bp00000001001010 bp00000001001011
private noncomputable def vp000000010010011_0 : Blocks := edgeBlocks% "full/vectors/000000010010011-V-0000.bin"
noncomputable def vp000000010010011 : Blocks := vp000000010010011_0
theorem coverp000000010010011 : Covers (-36511639/250000 : ℚ) vp000000010010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010010010_0 : Blocks := edgeBlocks% "full/vectors/000000010010010-V-0000.bin"
noncomputable def vp000000010010010 : Blocks := vp000000010010010_0
theorem coverp000000010010010 : Covers (-36261639/250000 : ℚ) vp000000010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001001001_0 : Blocks := edgeBlocks% "full/vectors/00000001001001-V-0000.bin"
noncomputable def vp00000001001001 : Blocks := vp00000001001001_0
private theorem bp000000010010010 : Branch 0 (-36261639/500000 : ℚ) vp00000001001001 := by
  apply branch_left_normalized (c:=vp000000010010010) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-36261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-36261639/250000 : ℚ) by norm_num]
  exact coverp000000010010010
private noncomputable def ep000000010010011_0 : Blocks := edgeBlocks% "full/vectors/000000010010011-E-0000.bin"
noncomputable def ep000000010010011 : Blocks := ep000000010010011_0
private theorem idp000000010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001001001.list =
    C ((2:ℤ)^102) * horner X vp000000010010011.list + horner X ep000000010010011.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010010011 : Branch 1 (-36261639/500000 : ℚ) vp00000001001001 := by
  apply branch_checked idp000000010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-36261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-36511639/250000 : ℚ) by norm_num]
  exact coverp000000010010011
theorem coverp00000001001001 : Covers (-36261639/500000 : ℚ) vp00000001001001 := join_branches bp000000010010010 bp000000010010011
private noncomputable def vp0000000100100011_0 : Blocks := edgeBlocks% "full/vectors/0000000100100011-V-0000.bin"
noncomputable def vp0000000100100011 : Blocks := vp0000000100100011_0
theorem coverp0000000100100011 : Covers (-36136639/125000 : ℚ) vp0000000100100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100100010_0 : Blocks := edgeBlocks% "full/vectors/0000000100100010-V-0000.bin"
noncomputable def vp0000000100100010 : Blocks := vp0000000100100010_0
theorem coverp0000000100100010 : Covers (-36011639/125000 : ℚ) vp0000000100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010010001_0 : Blocks := edgeBlocks% "full/vectors/000000010010001-V-0000.bin"
noncomputable def vp000000010010001 : Blocks := vp000000010010001_0
private theorem bp0000000100100010 : Branch 0 (-36011639/250000 : ℚ) vp000000010010001 := by
  apply branch_left_normalized (c:=vp0000000100100010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-36011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-36011639/125000 : ℚ) by norm_num]
  exact coverp0000000100100010
private noncomputable def ep0000000100100011_0 : Blocks := edgeBlocks% "full/vectors/0000000100100011-E-0000.bin"
noncomputable def ep0000000100100011 : Blocks := ep0000000100100011_0
private theorem idp0000000100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010010001.list =
    C ((2:ℤ)^60) * horner X vp0000000100100011.list + horner X ep0000000100100011.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100100011 : Branch 1 (-36011639/250000 : ℚ) vp000000010010001 := by
  apply branch_checked idp0000000100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-36011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-36136639/125000 : ℚ) by norm_num]
  exact coverp0000000100100011
theorem coverp000000010010001 : Covers (-36011639/250000 : ℚ) vp000000010010001 := join_branches bp0000000100100010 bp0000000100100011
private noncomputable def vp0000000100100001_0 : Blocks := edgeBlocks% "full/vectors/0000000100100001-V-0000.bin"
noncomputable def vp0000000100100001 : Blocks := vp0000000100100001_0
theorem coverp0000000100100001 : Covers (-35886639/125000 : ℚ) vp0000000100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100100000_0 : Blocks := edgeBlocks% "full/vectors/0000000100100000-V-0000.bin"
noncomputable def vp0000000100100000 : Blocks := vp0000000100100000_0
theorem coverp0000000100100000 : Covers (-35761639/125000 : ℚ) vp0000000100100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010010000_0 : Blocks := edgeBlocks% "full/vectors/000000010010000-V-0000.bin"
noncomputable def vp000000010010000 : Blocks := vp000000010010000_0
private theorem bp0000000100100000 : Branch 0 (-35761639/250000 : ℚ) vp000000010010000 := by
  apply branch_left_normalized (c:=vp0000000100100000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-35761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-35761639/125000 : ℚ) by norm_num]
  exact coverp0000000100100000
private noncomputable def ep0000000100100001_0 : Blocks := edgeBlocks% "full/vectors/0000000100100001-E-0000.bin"
noncomputable def ep0000000100100001 : Blocks := ep0000000100100001_0
private theorem idp0000000100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010010000.list =
    C ((2:ℤ)^62) * horner X vp0000000100100001.list + horner X ep0000000100100001.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100100001 : Branch 1 (-35761639/250000 : ℚ) vp000000010010000 := by
  apply branch_checked idp0000000100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-35761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-35886639/125000 : ℚ) by norm_num]
  exact coverp0000000100100001
theorem coverp000000010010000 : Covers (-35761639/250000 : ℚ) vp000000010010000 := join_branches bp0000000100100000 bp0000000100100001
private noncomputable def vp00000001001000_0 : Blocks := edgeBlocks% "full/vectors/00000001001000-V-0000.bin"
noncomputable def vp00000001001000 : Blocks := vp00000001001000_0
private theorem bp000000010010000 : Branch 0 (-35761639/500000 : ℚ) vp00000001001000 := by
  apply branch_left_normalized (c:=vp000000010010000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-35761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-35761639/250000 : ℚ) by norm_num]
  exact coverp000000010010000
private noncomputable def ep000000010010001_0 : Blocks := edgeBlocks% "full/vectors/000000010010001-E-0000.bin"
noncomputable def ep000000010010001 : Blocks := ep000000010010001_0
private theorem idp000000010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001001000.list =
    C ((2:ℤ)^105) * horner X vp000000010010001.list + horner X ep000000010010001.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010010001 : Branch 1 (-35761639/500000 : ℚ) vp00000001001000 := by
  apply branch_checked idp000000010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-35761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-36011639/250000 : ℚ) by norm_num]
  exact coverp000000010010001
theorem coverp00000001001000 : Covers (-35761639/500000 : ℚ) vp00000001001000 := join_branches bp000000010010000 bp000000010010001
private noncomputable def vp0000000100100_0 : Blocks := edgeBlocks% "full/vectors/0000000100100-V-0000.bin"
private noncomputable def vp0000000100100_1 : Blocks := edgeBlocks% "full/vectors/0000000100100-V-0001.bin"
noncomputable def vp0000000100100 : Blocks := (Blocks.join vp0000000100100_0 vp0000000100100_1)
private theorem bp00000001001000 : Branch 0 (-35761639/1000000 : ℚ) vp0000000100100 := by
  apply branch_left_normalized (c:=vp00000001001000) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-35761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-35761639/500000 : ℚ) by norm_num]
  exact coverp00000001001000
private noncomputable def ep00000001001001_0 : Blocks := edgeBlocks% "full/vectors/00000001001001-E-0000.bin"
private noncomputable def ep00000001001001_1 : Blocks := edgeBlocks% "full/vectors/00000001001001-E-0001.bin"
noncomputable def ep00000001001001 : Blocks := (Blocks.join ep00000001001001_0 ep00000001001001_1)
private theorem idp00000001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100100.list =
    C ((2:ℤ)^190) * horner X vp00000001001001.list + horner X ep00000001001001.list := by
  exact edge_identity (B := (2:ℤ)^367) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001001001 : Branch 1 (-35761639/1000000 : ℚ) vp0000000100100 := by
  apply branch_checked idp00000001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-35761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-36261639/500000 : ℚ) by norm_num]
  exact coverp00000001001001
theorem coverp0000000100100 : Covers (-35761639/1000000 : ℚ) vp0000000100100 := join_branches bp00000001001000 bp00000001001001
private noncomputable def vp000000010010_0 : Blocks := edgeBlocks% "full/vectors/000000010010-V-0000.bin"
private noncomputable def vp000000010010_1 : Blocks := edgeBlocks% "full/vectors/000000010010-V-0001.bin"
private noncomputable def vp000000010010_2 : Blocks := edgeBlocks% "full/vectors/000000010010-V-0002.bin"
noncomputable def vp000000010010 : Blocks := (Blocks.join vp000000010010_0 (Blocks.join vp000000010010_1 vp000000010010_2))
private theorem bp0000000100100 : Branch 0 (-35761639/2000000 : ℚ) vp000000010010 := by
  apply branch_left_normalized (c:=vp0000000100100) (k:=0) (m:=183) (by decide +kernel)
  rw [show 2*(-35761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-35761639/1000000 : ℚ) by norm_num]
  exact coverp0000000100100
private noncomputable def ep0000000100101_0 : Blocks := edgeBlocks% "full/vectors/0000000100101-E-0000.bin"
private noncomputable def ep0000000100101_1 : Blocks := edgeBlocks% "full/vectors/0000000100101-E-0001.bin"
private noncomputable def ep0000000100101_2 : Blocks := edgeBlocks% "full/vectors/0000000100101-E-0002.bin"
noncomputable def ep0000000100101 : Blocks := (Blocks.join ep0000000100101_0 (Blocks.join ep0000000100101_1 ep0000000100101_2))
private theorem idp0000000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010010.list =
    C ((2:ℤ)^357) * horner X vp0000000100101.list + horner X ep0000000100101.list := by
  exact edge_identity (B := (2:ℤ)^616) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100101 : Branch 1 (-35761639/2000000 : ℚ) vp000000010010 := by
  apply branch_checked idp0000000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-35761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-36761639/1000000 : ℚ) by norm_num]
  exact coverp0000000100101
theorem coverp000000010010 : Covers (-35761639/2000000 : ℚ) vp000000010010 := join_branches bp0000000100100 bp0000000100101
private noncomputable def vp00000001001_0 : Blocks := edgeBlocks% "full/vectors/00000001001-V-0000.bin"
private noncomputable def vp00000001001_1 : Blocks := edgeBlocks% "full/vectors/00000001001-V-0001.bin"
private noncomputable def vp00000001001_2 : Blocks := edgeBlocks% "full/vectors/00000001001-V-0002.bin"
private noncomputable def vp00000001001_3 : Blocks := edgeBlocks% "full/vectors/00000001001-V-0003.bin"
private noncomputable def vp00000001001_4 : Blocks := edgeBlocks% "full/vectors/00000001001-V-0004.bin"
private noncomputable def vp00000001001_5 : Blocks := edgeBlocks% "full/vectors/00000001001-V-0005.bin"
noncomputable def vp00000001001 : Blocks := (Blocks.join (Blocks.join vp00000001001_0 (Blocks.join vp00000001001_1 vp00000001001_2)) (Blocks.join vp00000001001_3 (Blocks.join vp00000001001_4 vp00000001001_5)))
private theorem bp000000010010 : Branch 0 (-35761639/4000000 : ℚ) vp00000001001 := by
  apply branch_left_normalized (c:=vp000000010010) (k:=0) (m:=345) (by decide +kernel)
  rw [show 2*(-35761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-35761639/2000000 : ℚ) by norm_num]
  exact coverp000000010010
private noncomputable def ep000000010011_0 : Blocks := edgeBlocks% "full/vectors/000000010011-E-0000.bin"
private noncomputable def ep000000010011_1 : Blocks := edgeBlocks% "full/vectors/000000010011-E-0001.bin"
private noncomputable def ep000000010011_2 : Blocks := edgeBlocks% "full/vectors/000000010011-E-0002.bin"
private noncomputable def ep000000010011_3 : Blocks := edgeBlocks% "full/vectors/000000010011-E-0003.bin"
private noncomputable def ep000000010011_4 : Blocks := edgeBlocks% "full/vectors/000000010011-E-0004.bin"
private noncomputable def ep000000010011_5 : Blocks := edgeBlocks% "full/vectors/000000010011-E-0005.bin"
noncomputable def ep000000010011 : Blocks := (Blocks.join (Blocks.join ep000000010011_0 (Blocks.join ep000000010011_1 ep000000010011_2)) (Blocks.join ep000000010011_3 (Blocks.join ep000000010011_4 ep000000010011_5)))
private theorem idp000000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001001.list =
    C ((2:ℤ)^688) * horner X vp000000010011.list + horner X ep000000010011.list := by
  exact edge_identity (B := (2:ℤ)^1113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010011 : Branch 1 (-35761639/4000000 : ℚ) vp00000001001 := by
  apply branch_checked idp000000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-35761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-37761639/2000000 : ℚ) by norm_num]
  exact coverp000000010011
theorem coverp00000001001 : Covers (-35761639/4000000 : ℚ) vp00000001001 := join_branches bp000000010010 bp000000010011
private noncomputable def vp0000000100011111_0 : Blocks := edgeBlocks% "full/vectors/0000000100011111-V-0000.bin"
noncomputable def vp0000000100011111 : Blocks := vp0000000100011111_0
theorem coverp0000000100011111 : Covers (-35636639/125000 : ℚ) vp0000000100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100011110_0 : Blocks := edgeBlocks% "full/vectors/0000000100011110-V-0000.bin"
noncomputable def vp0000000100011110 : Blocks := vp0000000100011110_0
theorem coverp0000000100011110 : Covers (-35511639/125000 : ℚ) vp0000000100011110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010001111_0 : Blocks := edgeBlocks% "full/vectors/000000010001111-V-0000.bin"
noncomputable def vp000000010001111 : Blocks := vp000000010001111_0
private theorem bp0000000100011110 : Branch 0 (-35511639/250000 : ℚ) vp000000010001111 := by
  apply branch_left_normalized (c:=vp0000000100011110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-35511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-35511639/125000 : ℚ) by norm_num]
  exact coverp0000000100011110
private noncomputable def ep0000000100011111_0 : Blocks := edgeBlocks% "full/vectors/0000000100011111-E-0000.bin"
noncomputable def ep0000000100011111 : Blocks := ep0000000100011111_0
private theorem idp0000000100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010001111.list =
    C ((2:ℤ)^65) * horner X vp0000000100011111.list + horner X ep0000000100011111.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100011111 : Branch 1 (-35511639/250000 : ℚ) vp000000010001111 := by
  apply branch_checked idp0000000100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-35511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-35636639/125000 : ℚ) by norm_num]
  exact coverp0000000100011111
theorem coverp000000010001111 : Covers (-35511639/250000 : ℚ) vp000000010001111 := join_branches bp0000000100011110 bp0000000100011111
private noncomputable def vp00000001000111011_0 : Blocks := edgeBlocks% "full/vectors/00000001000111011-V-0000.bin"
noncomputable def vp00000001000111011 : Blocks := vp00000001000111011_0
theorem coverp00000001000111011 : Covers (-35449139/62500 : ℚ) vp00000001000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010001110101_0 : Blocks := edgeBlocks% "full/vectors/000000010001110101-V-0000.bin"
noncomputable def vp000000010001110101 : Blocks := vp000000010001110101_0
theorem coverp000000010001110101 : Covers (-35417889/31250 : ℚ) vp000000010001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010001110100_0 : Blocks := edgeBlocks% "full/vectors/000000010001110100-V-0000.bin"
noncomputable def vp000000010001110100 : Blocks := vp000000010001110100_0
theorem coverp000000010001110100 : Covers (-35386639/31250 : ℚ) vp000000010001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001000111010_0 : Blocks := edgeBlocks% "full/vectors/00000001000111010-V-0000.bin"
noncomputable def vp00000001000111010 : Blocks := vp00000001000111010_0
private theorem bp000000010001110100 : Branch 0 (-35386639/62500 : ℚ) vp00000001000111010 := by
  apply branch_left_normalized (c:=vp000000010001110100) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-35386639/62500 : ℚ) - ((0:ℤ):ℚ) = (-35386639/31250 : ℚ) by norm_num]
  exact coverp000000010001110100
private noncomputable def ep000000010001110101_0 : Blocks := edgeBlocks% "full/vectors/000000010001110101-E-0000.bin"
noncomputable def ep000000010001110101 : Blocks := ep000000010001110101_0
private theorem idp000000010001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000111010.list =
    C ((2:ℤ)^28) * horner X vp000000010001110101.list + horner X ep000000010001110101.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010001110101 : Branch 1 (-35386639/62500 : ℚ) vp00000001000111010 := by
  apply branch_checked idp000000010001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-35386639/62500 : ℚ) - ((1:ℤ):ℚ) = (-35417889/31250 : ℚ) by norm_num]
  exact coverp000000010001110101
theorem coverp00000001000111010 : Covers (-35386639/62500 : ℚ) vp00000001000111010 := join_branches bp000000010001110100 bp000000010001110101
private noncomputable def vp0000000100011101_0 : Blocks := edgeBlocks% "full/vectors/0000000100011101-V-0000.bin"
noncomputable def vp0000000100011101 : Blocks := vp0000000100011101_0
private theorem bp00000001000111010 : Branch 0 (-35386639/125000 : ℚ) vp0000000100011101 := by
  apply branch_left_normalized (c:=vp00000001000111010) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-35386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-35386639/62500 : ℚ) by norm_num]
  exact coverp00000001000111010
private noncomputable def ep00000001000111011_0 : Blocks := edgeBlocks% "full/vectors/00000001000111011-E-0000.bin"
noncomputable def ep00000001000111011 : Blocks := ep00000001000111011_0
private theorem idp00000001000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100011101.list =
    C ((2:ℤ)^40) * horner X vp00000001000111011.list + horner X ep00000001000111011.list := by
  exact edge_identity (B := (2:ℤ)^152) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000111011 : Branch 1 (-35386639/125000 : ℚ) vp0000000100011101 := by
  apply branch_checked idp00000001000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-35386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-35449139/62500 : ℚ) by norm_num]
  exact coverp00000001000111011
theorem coverp0000000100011101 : Covers (-35386639/125000 : ℚ) vp0000000100011101 := join_branches bp00000001000111010 bp00000001000111011
private noncomputable def vp00000001000111001_0 : Blocks := edgeBlocks% "full/vectors/00000001000111001-V-0000.bin"
noncomputable def vp00000001000111001 : Blocks := vp00000001000111001_0
theorem coverp00000001000111001 : Covers (-35324139/62500 : ℚ) vp00000001000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001000111000_0 : Blocks := edgeBlocks% "full/vectors/00000001000111000-V-0000.bin"
noncomputable def vp00000001000111000 : Blocks := vp00000001000111000_0
theorem coverp00000001000111000 : Covers (-35261639/62500 : ℚ) vp00000001000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100011100_0 : Blocks := edgeBlocks% "full/vectors/0000000100011100-V-0000.bin"
noncomputable def vp0000000100011100 : Blocks := vp0000000100011100_0
private theorem bp00000001000111000 : Branch 0 (-35261639/125000 : ℚ) vp0000000100011100 := by
  apply branch_left_normalized (c:=vp00000001000111000) (k:=0) (m:=25) (by decide +kernel)
  rw [show 2*(-35261639/125000 : ℚ) - ((0:ℤ):ℚ) = (-35261639/62500 : ℚ) by norm_num]
  exact coverp00000001000111000
private noncomputable def ep00000001000111001_0 : Blocks := edgeBlocks% "full/vectors/00000001000111001-E-0000.bin"
noncomputable def ep00000001000111001 : Blocks := ep00000001000111001_0
private theorem idp00000001000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100011100.list =
    C ((2:ℤ)^39) * horner X vp00000001000111001.list + horner X ep00000001000111001.list := by
  exact edge_identity (B := (2:ℤ)^151) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000111001 : Branch 1 (-35261639/125000 : ℚ) vp0000000100011100 := by
  apply branch_checked idp00000001000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-35261639/125000 : ℚ) - ((1:ℤ):ℚ) = (-35324139/62500 : ℚ) by norm_num]
  exact coverp00000001000111001
theorem coverp0000000100011100 : Covers (-35261639/125000 : ℚ) vp0000000100011100 := join_branches bp00000001000111000 bp00000001000111001
private noncomputable def vp000000010001110_0 : Blocks := edgeBlocks% "full/vectors/000000010001110-V-0000.bin"
noncomputable def vp000000010001110 : Blocks := vp000000010001110_0
private theorem bp0000000100011100 : Branch 0 (-35261639/250000 : ℚ) vp000000010001110 := by
  apply branch_left_normalized (c:=vp0000000100011100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-35261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-35261639/125000 : ℚ) by norm_num]
  exact coverp0000000100011100
private noncomputable def ep0000000100011101_0 : Blocks := edgeBlocks% "full/vectors/0000000100011101-E-0000.bin"
noncomputable def ep0000000100011101 : Blocks := ep0000000100011101_0
private theorem idp0000000100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010001110.list =
    C ((2:ℤ)^61) * horner X vp0000000100011101.list + horner X ep0000000100011101.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100011101 : Branch 1 (-35261639/250000 : ℚ) vp000000010001110 := by
  apply branch_checked idp0000000100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-35261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-35386639/125000 : ℚ) by norm_num]
  exact coverp0000000100011101
theorem coverp000000010001110 : Covers (-35261639/250000 : ℚ) vp000000010001110 := join_branches bp0000000100011100 bp0000000100011101
private noncomputable def vp00000001000111_0 : Blocks := edgeBlocks% "full/vectors/00000001000111-V-0000.bin"
noncomputable def vp00000001000111 : Blocks := vp00000001000111_0
private theorem bp000000010001110 : Branch 0 (-35261639/500000 : ℚ) vp00000001000111 := by
  apply branch_left_normalized (c:=vp000000010001110) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-35261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-35261639/250000 : ℚ) by norm_num]
  exact coverp000000010001110
private noncomputable def ep000000010001111_0 : Blocks := edgeBlocks% "full/vectors/000000010001111-E-0000.bin"
noncomputable def ep000000010001111 : Blocks := ep000000010001111_0
private theorem idp000000010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000111.list =
    C ((2:ℤ)^103) * horner X vp000000010001111.list + horner X ep000000010001111.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010001111 : Branch 1 (-35261639/500000 : ℚ) vp00000001000111 := by
  apply branch_checked idp000000010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-35261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-35511639/250000 : ℚ) by norm_num]
  exact coverp000000010001111
theorem coverp00000001000111 : Covers (-35261639/500000 : ℚ) vp00000001000111 := join_branches bp000000010001110 bp000000010001111
private noncomputable def vp0000000100011011_0 : Blocks := edgeBlocks% "full/vectors/0000000100011011-V-0000.bin"
noncomputable def vp0000000100011011 : Blocks := vp0000000100011011_0
theorem coverp0000000100011011 : Covers (-35136639/125000 : ℚ) vp0000000100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100011010_0 : Blocks := edgeBlocks% "full/vectors/0000000100011010-V-0000.bin"
noncomputable def vp0000000100011010 : Blocks := vp0000000100011010_0
theorem coverp0000000100011010 : Covers (-35011639/125000 : ℚ) vp0000000100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010001101_0 : Blocks := edgeBlocks% "full/vectors/000000010001101-V-0000.bin"
noncomputable def vp000000010001101 : Blocks := vp000000010001101_0
private theorem bp0000000100011010 : Branch 0 (-35011639/250000 : ℚ) vp000000010001101 := by
  apply branch_left_normalized (c:=vp0000000100011010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-35011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-35011639/125000 : ℚ) by norm_num]
  exact coverp0000000100011010
private noncomputable def ep0000000100011011_0 : Blocks := edgeBlocks% "full/vectors/0000000100011011-E-0000.bin"
noncomputable def ep0000000100011011 : Blocks := ep0000000100011011_0
private theorem idp0000000100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010001101.list =
    C ((2:ℤ)^61) * horner X vp0000000100011011.list + horner X ep0000000100011011.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100011011 : Branch 1 (-35011639/250000 : ℚ) vp000000010001101 := by
  apply branch_checked idp0000000100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-35011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-35136639/125000 : ℚ) by norm_num]
  exact coverp0000000100011011
theorem coverp000000010001101 : Covers (-35011639/250000 : ℚ) vp000000010001101 := join_branches bp0000000100011010 bp0000000100011011
private noncomputable def vp0000000100011001_0 : Blocks := edgeBlocks% "full/vectors/0000000100011001-V-0000.bin"
noncomputable def vp0000000100011001 : Blocks := vp0000000100011001_0
theorem coverp0000000100011001 : Covers (-34886639/125000 : ℚ) vp0000000100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100011000_0 : Blocks := edgeBlocks% "full/vectors/0000000100011000-V-0000.bin"
noncomputable def vp0000000100011000 : Blocks := vp0000000100011000_0
theorem coverp0000000100011000 : Covers (-34761639/125000 : ℚ) vp0000000100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010001100_0 : Blocks := edgeBlocks% "full/vectors/000000010001100-V-0000.bin"
noncomputable def vp000000010001100 : Blocks := vp000000010001100_0
private theorem bp0000000100011000 : Branch 0 (-34761639/250000 : ℚ) vp000000010001100 := by
  apply branch_left_normalized (c:=vp0000000100011000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-34761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-34761639/125000 : ℚ) by norm_num]
  exact coverp0000000100011000
private noncomputable def ep0000000100011001_0 : Blocks := edgeBlocks% "full/vectors/0000000100011001-E-0000.bin"
noncomputable def ep0000000100011001 : Blocks := ep0000000100011001_0
private theorem idp0000000100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010001100.list =
    C ((2:ℤ)^61) * horner X vp0000000100011001.list + horner X ep0000000100011001.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100011001 : Branch 1 (-34761639/250000 : ℚ) vp000000010001100 := by
  apply branch_checked idp0000000100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-34761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-34886639/125000 : ℚ) by norm_num]
  exact coverp0000000100011001
theorem coverp000000010001100 : Covers (-34761639/250000 : ℚ) vp000000010001100 := join_branches bp0000000100011000 bp0000000100011001
private noncomputable def vp00000001000110_0 : Blocks := edgeBlocks% "full/vectors/00000001000110-V-0000.bin"
noncomputable def vp00000001000110 : Blocks := vp00000001000110_0
private theorem bp000000010001100 : Branch 0 (-34761639/500000 : ℚ) vp00000001000110 := by
  apply branch_left_normalized (c:=vp000000010001100) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-34761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-34761639/250000 : ℚ) by norm_num]
  exact coverp000000010001100
private noncomputable def ep000000010001101_0 : Blocks := edgeBlocks% "full/vectors/000000010001101-E-0000.bin"
noncomputable def ep000000010001101 : Blocks := ep000000010001101_0
private theorem idp000000010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000110.list =
    C ((2:ℤ)^105) * horner X vp000000010001101.list + horner X ep000000010001101.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010001101 : Branch 1 (-34761639/500000 : ℚ) vp00000001000110 := by
  apply branch_checked idp000000010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-34761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-35011639/250000 : ℚ) by norm_num]
  exact coverp000000010001101
theorem coverp00000001000110 : Covers (-34761639/500000 : ℚ) vp00000001000110 := join_branches bp000000010001100 bp000000010001101
private noncomputable def vp0000000100011_0 : Blocks := edgeBlocks% "full/vectors/0000000100011-V-0000.bin"
private noncomputable def vp0000000100011_1 : Blocks := edgeBlocks% "full/vectors/0000000100011-V-0001.bin"
noncomputable def vp0000000100011 : Blocks := (Blocks.join vp0000000100011_0 vp0000000100011_1)
private theorem bp00000001000110 : Branch 0 (-34761639/1000000 : ℚ) vp0000000100011 := by
  apply branch_left_normalized (c:=vp00000001000110) (k:=0) (m:=103) (by decide +kernel)
  rw [show 2*(-34761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-34761639/500000 : ℚ) by norm_num]
  exact coverp00000001000110
private noncomputable def ep00000001000111_0 : Blocks := edgeBlocks% "full/vectors/00000001000111-E-0000.bin"
private noncomputable def ep00000001000111_1 : Blocks := edgeBlocks% "full/vectors/00000001000111-E-0001.bin"
noncomputable def ep00000001000111 : Blocks := (Blocks.join ep00000001000111_0 ep00000001000111_1)
private theorem idp00000001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100011.list =
    C ((2:ℤ)^187) * horner X vp00000001000111.list + horner X ep00000001000111.list := by
  exact edge_identity (B := (2:ℤ)^372) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000111 : Branch 1 (-34761639/1000000 : ℚ) vp0000000100011 := by
  apply branch_checked idp00000001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-34761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-35261639/500000 : ℚ) by norm_num]
  exact coverp00000001000111
theorem coverp0000000100011 : Covers (-34761639/1000000 : ℚ) vp0000000100011 := join_branches bp00000001000110 bp00000001000111
private noncomputable def vp0000000100010111_0 : Blocks := edgeBlocks% "full/vectors/0000000100010111-V-0000.bin"
noncomputable def vp0000000100010111 : Blocks := vp0000000100010111_0
theorem coverp0000000100010111 : Covers (-34636639/125000 : ℚ) vp0000000100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100010110_0 : Blocks := edgeBlocks% "full/vectors/0000000100010110-V-0000.bin"
noncomputable def vp0000000100010110 : Blocks := vp0000000100010110_0
theorem coverp0000000100010110 : Covers (-34511639/125000 : ℚ) vp0000000100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010001011_0 : Blocks := edgeBlocks% "full/vectors/000000010001011-V-0000.bin"
noncomputable def vp000000010001011 : Blocks := vp000000010001011_0
private theorem bp0000000100010110 : Branch 0 (-34511639/250000 : ℚ) vp000000010001011 := by
  apply branch_left_normalized (c:=vp0000000100010110) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-34511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-34511639/125000 : ℚ) by norm_num]
  exact coverp0000000100010110
private noncomputable def ep0000000100010111_0 : Blocks := edgeBlocks% "full/vectors/0000000100010111-E-0000.bin"
noncomputable def ep0000000100010111 : Blocks := ep0000000100010111_0
private theorem idp0000000100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010001011.list =
    C ((2:ℤ)^62) * horner X vp0000000100010111.list + horner X ep0000000100010111.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100010111 : Branch 1 (-34511639/250000 : ℚ) vp000000010001011 := by
  apply branch_checked idp0000000100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-34511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-34636639/125000 : ℚ) by norm_num]
  exact coverp0000000100010111
theorem coverp000000010001011 : Covers (-34511639/250000 : ℚ) vp000000010001011 := join_branches bp0000000100010110 bp0000000100010111
private noncomputable def vp0000000100010101_0 : Blocks := edgeBlocks% "full/vectors/0000000100010101-V-0000.bin"
noncomputable def vp0000000100010101 : Blocks := vp0000000100010101_0
theorem coverp0000000100010101 : Covers (-34386639/125000 : ℚ) vp0000000100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100010100_0 : Blocks := edgeBlocks% "full/vectors/0000000100010100-V-0000.bin"
noncomputable def vp0000000100010100 : Blocks := vp0000000100010100_0
theorem coverp0000000100010100 : Covers (-34261639/125000 : ℚ) vp0000000100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010001010_0 : Blocks := edgeBlocks% "full/vectors/000000010001010-V-0000.bin"
noncomputable def vp000000010001010 : Blocks := vp000000010001010_0
private theorem bp0000000100010100 : Branch 0 (-34261639/250000 : ℚ) vp000000010001010 := by
  apply branch_left_normalized (c:=vp0000000100010100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-34261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-34261639/125000 : ℚ) by norm_num]
  exact coverp0000000100010100
private noncomputable def ep0000000100010101_0 : Blocks := edgeBlocks% "full/vectors/0000000100010101-E-0000.bin"
noncomputable def ep0000000100010101 : Blocks := ep0000000100010101_0
private theorem idp0000000100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010001010.list =
    C ((2:ℤ)^63) * horner X vp0000000100010101.list + horner X ep0000000100010101.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100010101 : Branch 1 (-34261639/250000 : ℚ) vp000000010001010 := by
  apply branch_checked idp0000000100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-34261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-34386639/125000 : ℚ) by norm_num]
  exact coverp0000000100010101
theorem coverp000000010001010 : Covers (-34261639/250000 : ℚ) vp000000010001010 := join_branches bp0000000100010100 bp0000000100010101
private noncomputable def vp00000001000101_0 : Blocks := edgeBlocks% "full/vectors/00000001000101-V-0000.bin"
noncomputable def vp00000001000101 : Blocks := vp00000001000101_0
private theorem bp000000010001010 : Branch 0 (-34261639/500000 : ℚ) vp00000001000101 := by
  apply branch_left_normalized (c:=vp000000010001010) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-34261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-34261639/250000 : ℚ) by norm_num]
  exact coverp000000010001010
private noncomputable def ep000000010001011_0 : Blocks := edgeBlocks% "full/vectors/000000010001011-E-0000.bin"
noncomputable def ep000000010001011 : Blocks := ep000000010001011_0
private theorem idp000000010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000101.list =
    C ((2:ℤ)^106) * horner X vp000000010001011.list + horner X ep000000010001011.list := by
  exact edge_identity (B := (2:ℤ)^247) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010001011 : Branch 1 (-34261639/500000 : ℚ) vp00000001000101 := by
  apply branch_checked idp000000010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-34261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-34511639/250000 : ℚ) by norm_num]
  exact coverp000000010001011
theorem coverp00000001000101 : Covers (-34261639/500000 : ℚ) vp00000001000101 := join_branches bp000000010001010 bp000000010001011
private noncomputable def vp0000000100010011_0 : Blocks := edgeBlocks% "full/vectors/0000000100010011-V-0000.bin"
noncomputable def vp0000000100010011 : Blocks := vp0000000100010011_0
theorem coverp0000000100010011 : Covers (-34136639/125000 : ℚ) vp0000000100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100010010_0 : Blocks := edgeBlocks% "full/vectors/0000000100010010-V-0000.bin"
noncomputable def vp0000000100010010 : Blocks := vp0000000100010010_0
theorem coverp0000000100010010 : Covers (-34011639/125000 : ℚ) vp0000000100010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010001001_0 : Blocks := edgeBlocks% "full/vectors/000000010001001-V-0000.bin"
noncomputable def vp000000010001001 : Blocks := vp000000010001001_0
private theorem bp0000000100010010 : Branch 0 (-34011639/250000 : ℚ) vp000000010001001 := by
  apply branch_left_normalized (c:=vp0000000100010010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-34011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-34011639/125000 : ℚ) by norm_num]
  exact coverp0000000100010010
private noncomputable def ep0000000100010011_0 : Blocks := edgeBlocks% "full/vectors/0000000100010011-E-0000.bin"
noncomputable def ep0000000100010011 : Blocks := ep0000000100010011_0
private theorem idp0000000100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010001001.list =
    C ((2:ℤ)^65) * horner X vp0000000100010011.list + horner X ep0000000100010011.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100010011 : Branch 1 (-34011639/250000 : ℚ) vp000000010001001 := by
  apply branch_checked idp0000000100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-34011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-34136639/125000 : ℚ) by norm_num]
  exact coverp0000000100010011
theorem coverp000000010001001 : Covers (-34011639/250000 : ℚ) vp000000010001001 := join_branches bp0000000100010010 bp0000000100010011
private noncomputable def vp00000001000100011_0 : Blocks := edgeBlocks% "full/vectors/00000001000100011-V-0000.bin"
noncomputable def vp00000001000100011 : Blocks := vp00000001000100011_0
theorem coverp00000001000100011 : Covers (-33949139/62500 : ℚ) vp00000001000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001000100010_0 : Blocks := edgeBlocks% "full/vectors/00000001000100010-V-0000.bin"
noncomputable def vp00000001000100010 : Blocks := vp00000001000100010_0
theorem coverp00000001000100010 : Covers (-33886639/62500 : ℚ) vp00000001000100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100010001_0 : Blocks := edgeBlocks% "full/vectors/0000000100010001-V-0000.bin"
noncomputable def vp0000000100010001 : Blocks := vp0000000100010001_0
private theorem bp00000001000100010 : Branch 0 (-33886639/125000 : ℚ) vp0000000100010001 := by
  apply branch_left_normalized (c:=vp00000001000100010) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-33886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-33886639/62500 : ℚ) by norm_num]
  exact coverp00000001000100010
private noncomputable def ep00000001000100011_0 : Blocks := edgeBlocks% "full/vectors/00000001000100011-E-0000.bin"
noncomputable def ep00000001000100011 : Blocks := ep00000001000100011_0
private theorem idp00000001000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100010001.list =
    C ((2:ℤ)^42) * horner X vp00000001000100011.list + horner X ep00000001000100011.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000100011 : Branch 1 (-33886639/125000 : ℚ) vp0000000100010001 := by
  apply branch_checked idp00000001000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-33886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-33949139/62500 : ℚ) by norm_num]
  exact coverp00000001000100011
theorem coverp0000000100010001 : Covers (-33886639/125000 : ℚ) vp0000000100010001 := join_branches bp00000001000100010 bp00000001000100011
private noncomputable def vp000000010001000011_0 : Blocks := edgeBlocks% "full/vectors/000000010001000011-V-0000.bin"
noncomputable def vp000000010001000011 : Blocks := vp000000010001000011_0
theorem coverp000000010001000011 : Covers (-33855389/31250 : ℚ) vp000000010001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010001000010_0 : Blocks := edgeBlocks% "full/vectors/000000010001000010-V-0000.bin"
noncomputable def vp000000010001000010 : Blocks := vp000000010001000010_0
theorem coverp000000010001000010 : Covers (-33824139/31250 : ℚ) vp000000010001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001000100001_0 : Blocks := edgeBlocks% "full/vectors/00000001000100001-V-0000.bin"
noncomputable def vp00000001000100001 : Blocks := vp00000001000100001_0
private theorem bp000000010001000010 : Branch 0 (-33824139/62500 : ℚ) vp00000001000100001 := by
  apply branch_left_normalized (c:=vp000000010001000010) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-33824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-33824139/31250 : ℚ) by norm_num]
  exact coverp000000010001000010
private noncomputable def ep000000010001000011_0 : Blocks := edgeBlocks% "full/vectors/000000010001000011-E-0000.bin"
noncomputable def ep000000010001000011 : Blocks := ep000000010001000011_0
private theorem idp000000010001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000100001.list =
    C ((2:ℤ)^28) * horner X vp000000010001000011.list + horner X ep000000010001000011.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010001000011 : Branch 1 (-33824139/62500 : ℚ) vp00000001000100001 := by
  apply branch_checked idp000000010001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-33824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-33855389/31250 : ℚ) by norm_num]
  exact coverp000000010001000011
theorem coverp00000001000100001 : Covers (-33824139/62500 : ℚ) vp00000001000100001 := join_branches bp000000010001000010 bp000000010001000011
private noncomputable def vp00000001000100000_0 : Blocks := edgeBlocks% "full/vectors/00000001000100000-V-0000.bin"
noncomputable def vp00000001000100000 : Blocks := vp00000001000100000_0
theorem coverp00000001000100000 : Covers (-33761639/62500 : ℚ) vp00000001000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100010000_0 : Blocks := edgeBlocks% "full/vectors/0000000100010000-V-0000.bin"
noncomputable def vp0000000100010000 : Blocks := vp0000000100010000_0
private theorem bp00000001000100000 : Branch 0 (-33761639/125000 : ℚ) vp0000000100010000 := by
  apply branch_left_normalized (c:=vp00000001000100000) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-33761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-33761639/62500 : ℚ) by norm_num]
  exact coverp00000001000100000
private noncomputable def ep00000001000100001_0 : Blocks := edgeBlocks% "full/vectors/00000001000100001-E-0000.bin"
noncomputable def ep00000001000100001 : Blocks := ep00000001000100001_0
private theorem idp00000001000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100010000.list =
    C ((2:ℤ)^40) * horner X vp00000001000100001.list + horner X ep00000001000100001.list := by
  exact edge_identity (B := (2:ℤ)^153) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000100001 : Branch 1 (-33761639/125000 : ℚ) vp0000000100010000 := by
  apply branch_checked idp00000001000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-33761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-33824139/62500 : ℚ) by norm_num]
  exact coverp00000001000100001
theorem coverp0000000100010000 : Covers (-33761639/125000 : ℚ) vp0000000100010000 := join_branches bp00000001000100000 bp00000001000100001
private noncomputable def vp000000010001000_0 : Blocks := edgeBlocks% "full/vectors/000000010001000-V-0000.bin"
noncomputable def vp000000010001000 : Blocks := vp000000010001000_0
private theorem bp0000000100010000 : Branch 0 (-33761639/250000 : ℚ) vp000000010001000 := by
  apply branch_left_normalized (c:=vp0000000100010000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-33761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-33761639/125000 : ℚ) by norm_num]
  exact coverp0000000100010000
private noncomputable def ep0000000100010001_0 : Blocks := edgeBlocks% "full/vectors/0000000100010001-E-0000.bin"
noncomputable def ep0000000100010001 : Blocks := ep0000000100010001_0
private theorem idp0000000100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010001000.list =
    C ((2:ℤ)^63) * horner X vp0000000100010001.list + horner X ep0000000100010001.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100010001 : Branch 1 (-33761639/250000 : ℚ) vp000000010001000 := by
  apply branch_checked idp0000000100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-33761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-33886639/125000 : ℚ) by norm_num]
  exact coverp0000000100010001
theorem coverp000000010001000 : Covers (-33761639/250000 : ℚ) vp000000010001000 := join_branches bp0000000100010000 bp0000000100010001
private noncomputable def vp00000001000100_0 : Blocks := edgeBlocks% "full/vectors/00000001000100-V-0000.bin"
noncomputable def vp00000001000100 : Blocks := vp00000001000100_0
private theorem bp000000010001000 : Branch 0 (-33761639/500000 : ℚ) vp00000001000100 := by
  apply branch_left_normalized (c:=vp000000010001000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-33761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-33761639/250000 : ℚ) by norm_num]
  exact coverp000000010001000
private noncomputable def ep000000010001001_0 : Blocks := edgeBlocks% "full/vectors/000000010001001-E-0000.bin"
noncomputable def ep000000010001001 : Blocks := ep000000010001001_0
private theorem idp000000010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000100.list =
    C ((2:ℤ)^108) * horner X vp000000010001001.list + horner X ep000000010001001.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010001001 : Branch 1 (-33761639/500000 : ℚ) vp00000001000100 := by
  apply branch_checked idp000000010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-33761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-34011639/250000 : ℚ) by norm_num]
  exact coverp000000010001001
theorem coverp00000001000100 : Covers (-33761639/500000 : ℚ) vp00000001000100 := join_branches bp000000010001000 bp000000010001001
private noncomputable def vp0000000100010_0 : Blocks := edgeBlocks% "full/vectors/0000000100010-V-0000.bin"
private noncomputable def vp0000000100010_1 : Blocks := edgeBlocks% "full/vectors/0000000100010-V-0001.bin"
noncomputable def vp0000000100010 : Blocks := (Blocks.join vp0000000100010_0 vp0000000100010_1)
private theorem bp00000001000100 : Branch 0 (-33761639/1000000 : ℚ) vp0000000100010 := by
  apply branch_left_normalized (c:=vp00000001000100) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-33761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-33761639/500000 : ℚ) by norm_num]
  exact coverp00000001000100
private noncomputable def ep00000001000101_0 : Blocks := edgeBlocks% "full/vectors/00000001000101-E-0000.bin"
private noncomputable def ep00000001000101_1 : Blocks := edgeBlocks% "full/vectors/00000001000101-E-0001.bin"
noncomputable def ep00000001000101 : Blocks := (Blocks.join ep00000001000101_0 ep00000001000101_1)
private theorem idp00000001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100010.list =
    C ((2:ℤ)^196) * horner X vp00000001000101.list + horner X ep00000001000101.list := by
  exact edge_identity (B := (2:ℤ)^381) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000101 : Branch 1 (-33761639/1000000 : ℚ) vp0000000100010 := by
  apply branch_checked idp00000001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-33761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-34261639/500000 : ℚ) by norm_num]
  exact coverp00000001000101
theorem coverp0000000100010 : Covers (-33761639/1000000 : ℚ) vp0000000100010 := join_branches bp00000001000100 bp00000001000101
private noncomputable def vp000000010001_0 : Blocks := edgeBlocks% "full/vectors/000000010001-V-0000.bin"
private noncomputable def vp000000010001_1 : Blocks := edgeBlocks% "full/vectors/000000010001-V-0001.bin"
private noncomputable def vp000000010001_2 : Blocks := edgeBlocks% "full/vectors/000000010001-V-0002.bin"
noncomputable def vp000000010001 : Blocks := (Blocks.join vp000000010001_0 (Blocks.join vp000000010001_1 vp000000010001_2))
private theorem bp0000000100010 : Branch 0 (-33761639/2000000 : ℚ) vp000000010001 := by
  apply branch_left_normalized (c:=vp0000000100010) (k:=0) (m:=190) (by decide +kernel)
  rw [show 2*(-33761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-33761639/1000000 : ℚ) by norm_num]
  exact coverp0000000100010
private noncomputable def ep0000000100011_0 : Blocks := edgeBlocks% "full/vectors/0000000100011-E-0000.bin"
private noncomputable def ep0000000100011_1 : Blocks := edgeBlocks% "full/vectors/0000000100011-E-0001.bin"
private noncomputable def ep0000000100011_2 : Blocks := edgeBlocks% "full/vectors/0000000100011-E-0002.bin"
noncomputable def ep0000000100011 : Blocks := (Blocks.join ep0000000100011_0 (Blocks.join ep0000000100011_1 ep0000000100011_2))
private theorem idp0000000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010001.list =
    C ((2:ℤ)^368) * horner X vp0000000100011.list + horner X ep0000000100011.list := by
  exact edge_identity (B := (2:ℤ)^639) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100011 : Branch 1 (-33761639/2000000 : ℚ) vp000000010001 := by
  apply branch_checked idp0000000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-33761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-34761639/1000000 : ℚ) by norm_num]
  exact coverp0000000100011
theorem coverp000000010001 : Covers (-33761639/2000000 : ℚ) vp000000010001 := join_branches bp0000000100010 bp0000000100011
private noncomputable def vp0000000100001111_0 : Blocks := edgeBlocks% "full/vectors/0000000100001111-V-0000.bin"
noncomputable def vp0000000100001111 : Blocks := vp0000000100001111_0
theorem coverp0000000100001111 : Covers (-33636639/125000 : ℚ) vp0000000100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100001110_0 : Blocks := edgeBlocks% "full/vectors/0000000100001110-V-0000.bin"
noncomputable def vp0000000100001110 : Blocks := vp0000000100001110_0
theorem coverp0000000100001110 : Covers (-33511639/125000 : ℚ) vp0000000100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010000111_0 : Blocks := edgeBlocks% "full/vectors/000000010000111-V-0000.bin"
noncomputable def vp000000010000111 : Blocks := vp000000010000111_0
private theorem bp0000000100001110 : Branch 0 (-33511639/250000 : ℚ) vp000000010000111 := by
  apply branch_left_normalized (c:=vp0000000100001110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-33511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-33511639/125000 : ℚ) by norm_num]
  exact coverp0000000100001110
private noncomputable def ep0000000100001111_0 : Blocks := edgeBlocks% "full/vectors/0000000100001111-E-0000.bin"
noncomputable def ep0000000100001111 : Blocks := ep0000000100001111_0
private theorem idp0000000100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000111.list =
    C ((2:ℤ)^63) * horner X vp0000000100001111.list + horner X ep0000000100001111.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100001111 : Branch 1 (-33511639/250000 : ℚ) vp000000010000111 := by
  apply branch_checked idp0000000100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-33511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-33636639/125000 : ℚ) by norm_num]
  exact coverp0000000100001111
theorem coverp000000010000111 : Covers (-33511639/250000 : ℚ) vp000000010000111 := join_branches bp0000000100001110 bp0000000100001111
private noncomputable def vp0000000100001101_0 : Blocks := edgeBlocks% "full/vectors/0000000100001101-V-0000.bin"
noncomputable def vp0000000100001101 : Blocks := vp0000000100001101_0
theorem coverp0000000100001101 : Covers (-33386639/125000 : ℚ) vp0000000100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100001100_0 : Blocks := edgeBlocks% "full/vectors/0000000100001100-V-0000.bin"
noncomputable def vp0000000100001100 : Blocks := vp0000000100001100_0
theorem coverp0000000100001100 : Covers (-33261639/125000 : ℚ) vp0000000100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010000110_0 : Blocks := edgeBlocks% "full/vectors/000000010000110-V-0000.bin"
noncomputable def vp000000010000110 : Blocks := vp000000010000110_0
private theorem bp0000000100001100 : Branch 0 (-33261639/250000 : ℚ) vp000000010000110 := by
  apply branch_left_normalized (c:=vp0000000100001100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-33261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-33261639/125000 : ℚ) by norm_num]
  exact coverp0000000100001100
private noncomputable def ep0000000100001101_0 : Blocks := edgeBlocks% "full/vectors/0000000100001101-E-0000.bin"
noncomputable def ep0000000100001101 : Blocks := ep0000000100001101_0
private theorem idp0000000100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000110.list =
    C ((2:ℤ)^67) * horner X vp0000000100001101.list + horner X ep0000000100001101.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100001101 : Branch 1 (-33261639/250000 : ℚ) vp000000010000110 := by
  apply branch_checked idp0000000100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-33261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-33386639/125000 : ℚ) by norm_num]
  exact coverp0000000100001101
theorem coverp000000010000110 : Covers (-33261639/250000 : ℚ) vp000000010000110 := join_branches bp0000000100001100 bp0000000100001101
private noncomputable def vp00000001000011_0 : Blocks := edgeBlocks% "full/vectors/00000001000011-V-0000.bin"
noncomputable def vp00000001000011 : Blocks := vp00000001000011_0
private theorem bp000000010000110 : Branch 0 (-33261639/500000 : ℚ) vp00000001000011 := by
  apply branch_left_normalized (c:=vp000000010000110) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-33261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-33261639/250000 : ℚ) by norm_num]
  exact coverp000000010000110
private noncomputable def ep000000010000111_0 : Blocks := edgeBlocks% "full/vectors/000000010000111-E-0000.bin"
noncomputable def ep000000010000111 : Blocks := ep000000010000111_0
private theorem idp000000010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000011.list =
    C ((2:ℤ)^111) * horner X vp000000010000111.list + horner X ep000000010000111.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010000111 : Branch 1 (-33261639/500000 : ℚ) vp00000001000011 := by
  apply branch_checked idp000000010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-33261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-33511639/250000 : ℚ) by norm_num]
  exact coverp000000010000111
theorem coverp00000001000011 : Covers (-33261639/500000 : ℚ) vp00000001000011 := join_branches bp000000010000110 bp000000010000111
private noncomputable def vp00000001000010111_0 : Blocks := edgeBlocks% "full/vectors/00000001000010111-V-0000.bin"
noncomputable def vp00000001000010111 : Blocks := vp00000001000010111_0
theorem coverp00000001000010111 : Covers (-33199139/62500 : ℚ) vp00000001000010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001000010110_0 : Blocks := edgeBlocks% "full/vectors/00000001000010110-V-0000.bin"
noncomputable def vp00000001000010110 : Blocks := vp00000001000010110_0
theorem coverp00000001000010110 : Covers (-33136639/62500 : ℚ) vp00000001000010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100001011_0 : Blocks := edgeBlocks% "full/vectors/0000000100001011-V-0000.bin"
noncomputable def vp0000000100001011 : Blocks := vp0000000100001011_0
private theorem bp00000001000010110 : Branch 0 (-33136639/125000 : ℚ) vp0000000100001011 := by
  apply branch_left_normalized (c:=vp00000001000010110) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-33136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-33136639/62500 : ℚ) by norm_num]
  exact coverp00000001000010110
private noncomputable def ep00000001000010111_0 : Blocks := edgeBlocks% "full/vectors/00000001000010111-E-0000.bin"
noncomputable def ep00000001000010111 : Blocks := ep00000001000010111_0
private theorem idp00000001000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100001011.list =
    C ((2:ℤ)^41) * horner X vp00000001000010111.list + horner X ep00000001000010111.list := by
  exact edge_identity (B := (2:ℤ)^154) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000010111 : Branch 1 (-33136639/125000 : ℚ) vp0000000100001011 := by
  apply branch_checked idp00000001000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-33136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-33199139/62500 : ℚ) by norm_num]
  exact coverp00000001000010111
theorem coverp0000000100001011 : Covers (-33136639/125000 : ℚ) vp0000000100001011 := join_branches bp00000001000010110 bp00000001000010111
private noncomputable def vp000000010000101011_0 : Blocks := edgeBlocks% "full/vectors/000000010000101011-V-0000.bin"
noncomputable def vp000000010000101011 : Blocks := vp000000010000101011_0
theorem coverp000000010000101011 : Covers (-33105389/31250 : ℚ) vp000000010000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010000101010_0 : Blocks := edgeBlocks% "full/vectors/000000010000101010-V-0000.bin"
noncomputable def vp000000010000101010 : Blocks := vp000000010000101010_0
theorem coverp000000010000101010 : Covers (-33074139/31250 : ℚ) vp000000010000101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001000010101_0 : Blocks := edgeBlocks% "full/vectors/00000001000010101-V-0000.bin"
noncomputable def vp00000001000010101 : Blocks := vp00000001000010101_0
private theorem bp000000010000101010 : Branch 0 (-33074139/62500 : ℚ) vp00000001000010101 := by
  apply branch_left_normalized (c:=vp000000010000101010) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-33074139/62500 : ℚ) - ((0:ℤ):ℚ) = (-33074139/31250 : ℚ) by norm_num]
  exact coverp000000010000101010
private noncomputable def ep000000010000101011_0 : Blocks := edgeBlocks% "full/vectors/000000010000101011-E-0000.bin"
noncomputable def ep000000010000101011 : Blocks := ep000000010000101011_0
private theorem idp000000010000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000010101.list =
    C ((2:ℤ)^28) * horner X vp000000010000101011.list + horner X ep000000010000101011.list := by
  exact edge_identity (B := (2:ℤ)^138) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010000101011 : Branch 1 (-33074139/62500 : ℚ) vp00000001000010101 := by
  apply branch_checked idp000000010000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-33074139/62500 : ℚ) - ((1:ℤ):ℚ) = (-33105389/31250 : ℚ) by norm_num]
  exact coverp000000010000101011
theorem coverp00000001000010101 : Covers (-33074139/62500 : ℚ) vp00000001000010101 := join_branches bp000000010000101010 bp000000010000101011
private noncomputable def vp000000010000101001_0 : Blocks := edgeBlocks% "full/vectors/000000010000101001-V-0000.bin"
noncomputable def vp000000010000101001 : Blocks := vp000000010000101001_0
theorem coverp000000010000101001 : Covers (-33042889/31250 : ℚ) vp000000010000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010000101000_0 : Blocks := edgeBlocks% "full/vectors/000000010000101000-V-0000.bin"
noncomputable def vp000000010000101000 : Blocks := vp000000010000101000_0
theorem coverp000000010000101000 : Covers (-33011639/31250 : ℚ) vp000000010000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001000010100_0 : Blocks := edgeBlocks% "full/vectors/00000001000010100-V-0000.bin"
noncomputable def vp00000001000010100 : Blocks := vp00000001000010100_0
private theorem bp000000010000101000 : Branch 0 (-33011639/62500 : ℚ) vp00000001000010100 := by
  apply branch_left_normalized (c:=vp000000010000101000) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-33011639/62500 : ℚ) - ((0:ℤ):ℚ) = (-33011639/31250 : ℚ) by norm_num]
  exact coverp000000010000101000
private noncomputable def ep000000010000101001_0 : Blocks := edgeBlocks% "full/vectors/000000010000101001-E-0000.bin"
noncomputable def ep000000010000101001 : Blocks := ep000000010000101001_0
private theorem idp000000010000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000010100.list =
    C ((2:ℤ)^27) * horner X vp000000010000101001.list + horner X ep000000010000101001.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010000101001 : Branch 1 (-33011639/62500 : ℚ) vp00000001000010100 := by
  apply branch_checked idp000000010000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-33011639/62500 : ℚ) - ((1:ℤ):ℚ) = (-33042889/31250 : ℚ) by norm_num]
  exact coverp000000010000101001
theorem coverp00000001000010100 : Covers (-33011639/62500 : ℚ) vp00000001000010100 := join_branches bp000000010000101000 bp000000010000101001
private noncomputable def vp0000000100001010_0 : Blocks := edgeBlocks% "full/vectors/0000000100001010-V-0000.bin"
noncomputable def vp0000000100001010 : Blocks := vp0000000100001010_0
private theorem bp00000001000010100 : Branch 0 (-33011639/125000 : ℚ) vp0000000100001010 := by
  apply branch_left_normalized (c:=vp00000001000010100) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-33011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-33011639/62500 : ℚ) by norm_num]
  exact coverp00000001000010100
private noncomputable def ep00000001000010101_0 : Blocks := edgeBlocks% "full/vectors/00000001000010101-E-0000.bin"
noncomputable def ep00000001000010101 : Blocks := ep00000001000010101_0
private theorem idp00000001000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100001010.list =
    C ((2:ℤ)^39) * horner X vp00000001000010101.list + horner X ep00000001000010101.list := by
  exact edge_identity (B := (2:ℤ)^152) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000010101 : Branch 1 (-33011639/125000 : ℚ) vp0000000100001010 := by
  apply branch_checked idp00000001000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-33011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-33074139/62500 : ℚ) by norm_num]
  exact coverp00000001000010101
theorem coverp0000000100001010 : Covers (-33011639/125000 : ℚ) vp0000000100001010 := join_branches bp00000001000010100 bp00000001000010101
private noncomputable def vp000000010000101_0 : Blocks := edgeBlocks% "full/vectors/000000010000101-V-0000.bin"
noncomputable def vp000000010000101 : Blocks := vp000000010000101_0
private theorem bp0000000100001010 : Branch 0 (-33011639/250000 : ℚ) vp000000010000101 := by
  apply branch_left_normalized (c:=vp0000000100001010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-33011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-33011639/125000 : ℚ) by norm_num]
  exact coverp0000000100001010
private noncomputable def ep0000000100001011_0 : Blocks := edgeBlocks% "full/vectors/0000000100001011-E-0000.bin"
noncomputable def ep0000000100001011 : Blocks := ep0000000100001011_0
private theorem idp0000000100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000101.list =
    C ((2:ℤ)^62) * horner X vp0000000100001011.list + horner X ep0000000100001011.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100001011 : Branch 1 (-33011639/250000 : ℚ) vp000000010000101 := by
  apply branch_checked idp0000000100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-33011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-33136639/125000 : ℚ) by norm_num]
  exact coverp0000000100001011
theorem coverp000000010000101 : Covers (-33011639/250000 : ℚ) vp000000010000101 := join_branches bp0000000100001010 bp0000000100001011
private noncomputable def vp00000001000010011_0 : Blocks := edgeBlocks% "full/vectors/00000001000010011-V-0000.bin"
noncomputable def vp00000001000010011 : Blocks := vp00000001000010011_0
theorem coverp00000001000010011 : Covers (-32949139/62500 : ℚ) vp00000001000010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001000010010_0 : Blocks := edgeBlocks% "full/vectors/00000001000010010-V-0000.bin"
noncomputable def vp00000001000010010 : Blocks := vp00000001000010010_0
theorem coverp00000001000010010 : Covers (-32886639/62500 : ℚ) vp00000001000010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100001001_0 : Blocks := edgeBlocks% "full/vectors/0000000100001001-V-0000.bin"
noncomputable def vp0000000100001001 : Blocks := vp0000000100001001_0
private theorem bp00000001000010010 : Branch 0 (-32886639/125000 : ℚ) vp0000000100001001 := by
  apply branch_left_normalized (c:=vp00000001000010010) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-32886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-32886639/62500 : ℚ) by norm_num]
  exact coverp00000001000010010
private noncomputable def ep00000001000010011_0 : Blocks := edgeBlocks% "full/vectors/00000001000010011-E-0000.bin"
noncomputable def ep00000001000010011 : Blocks := ep00000001000010011_0
private theorem idp00000001000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100001001.list =
    C ((2:ℤ)^41) * horner X vp00000001000010011.list + horner X ep00000001000010011.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000010011 : Branch 1 (-32886639/125000 : ℚ) vp0000000100001001 := by
  apply branch_checked idp00000001000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-32886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-32949139/62500 : ℚ) by norm_num]
  exact coverp00000001000010011
theorem coverp0000000100001001 : Covers (-32886639/125000 : ℚ) vp0000000100001001 := join_branches bp00000001000010010 bp00000001000010011
private noncomputable def vp000000010000100011_0 : Blocks := edgeBlocks% "full/vectors/000000010000100011-V-0000.bin"
noncomputable def vp000000010000100011 : Blocks := vp000000010000100011_0
theorem coverp000000010000100011 : Covers (-32855389/31250 : ℚ) vp000000010000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100001000101_0 : Blocks := edgeBlocks% "full/vectors/0000000100001000101-V-0000.bin"
noncomputable def vp0000000100001000101 : Blocks := vp0000000100001000101_0
theorem coverp0000000100001000101 : Covers (-32839764/15625 : ℚ) vp0000000100001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100001000100_0 : Blocks := edgeBlocks% "full/vectors/0000000100001000100-V-0000.bin"
noncomputable def vp0000000100001000100 : Blocks := vp0000000100001000100_0
theorem coverp0000000100001000100 : Covers (-32824139/15625 : ℚ) vp0000000100001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010000100010_0 : Blocks := edgeBlocks% "full/vectors/000000010000100010-V-0000.bin"
noncomputable def vp000000010000100010 : Blocks := vp000000010000100010_0
private theorem bp0000000100001000100 : Branch 0 (-32824139/31250 : ℚ) vp000000010000100010 := by
  apply branch_left_normalized (c:=vp0000000100001000100) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-32824139/31250 : ℚ) - ((0:ℤ):ℚ) = (-32824139/15625 : ℚ) by norm_num]
  exact coverp0000000100001000100
private noncomputable def ep0000000100001000101_0 : Blocks := edgeBlocks% "full/vectors/0000000100001000101-E-0000.bin"
noncomputable def ep0000000100001000101 : Blocks := ep0000000100001000101_0
private theorem idp0000000100001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000100010.list =
    C ((2:ℤ)^20) * horner X vp0000000100001000101.list + horner X ep0000000100001000101.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100001000101 : Branch 1 (-32824139/31250 : ℚ) vp000000010000100010 := by
  apply branch_checked idp0000000100001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-32824139/31250 : ℚ) - ((1:ℤ):ℚ) = (-32839764/15625 : ℚ) by norm_num]
  exact coverp0000000100001000101
theorem coverp000000010000100010 : Covers (-32824139/31250 : ℚ) vp000000010000100010 := join_branches bp0000000100001000100 bp0000000100001000101
private noncomputable def vp00000001000010001_0 : Blocks := edgeBlocks% "full/vectors/00000001000010001-V-0000.bin"
noncomputable def vp00000001000010001 : Blocks := vp00000001000010001_0
private theorem bp000000010000100010 : Branch 0 (-32824139/62500 : ℚ) vp00000001000010001 := by
  apply branch_left_normalized (c:=vp000000010000100010) (k:=0) (m:=19) (by decide +kernel)
  rw [show 2*(-32824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-32824139/31250 : ℚ) by norm_num]
  exact coverp000000010000100010
private noncomputable def ep000000010000100011_0 : Blocks := edgeBlocks% "full/vectors/000000010000100011-E-0000.bin"
noncomputable def ep000000010000100011 : Blocks := ep000000010000100011_0
private theorem idp000000010000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000010001.list =
    C ((2:ℤ)^27) * horner X vp000000010000100011.list + horner X ep000000010000100011.list := by
  exact edge_identity (B := (2:ℤ)^139) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010000100011 : Branch 1 (-32824139/62500 : ℚ) vp00000001000010001 := by
  apply branch_checked idp000000010000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-32824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-32855389/31250 : ℚ) by norm_num]
  exact coverp000000010000100011
theorem coverp00000001000010001 : Covers (-32824139/62500 : ℚ) vp00000001000010001 := join_branches bp000000010000100010 bp000000010000100011
private noncomputable def vp00000001000010000_0 : Blocks := edgeBlocks% "full/vectors/00000001000010000-V-0000.bin"
noncomputable def vp00000001000010000 : Blocks := vp00000001000010000_0
theorem coverp00000001000010000 : Covers (-32761639/62500 : ℚ) vp00000001000010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100001000_0 : Blocks := edgeBlocks% "full/vectors/0000000100001000-V-0000.bin"
noncomputable def vp0000000100001000 : Blocks := vp0000000100001000_0
private theorem bp00000001000010000 : Branch 0 (-32761639/125000 : ℚ) vp0000000100001000 := by
  apply branch_left_normalized (c:=vp00000001000010000) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-32761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-32761639/62500 : ℚ) by norm_num]
  exact coverp00000001000010000
private noncomputable def ep00000001000010001_0 : Blocks := edgeBlocks% "full/vectors/00000001000010001-E-0000.bin"
noncomputable def ep00000001000010001 : Blocks := ep00000001000010001_0
private theorem idp00000001000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100001000.list =
    C ((2:ℤ)^39) * horner X vp00000001000010001.list + horner X ep00000001000010001.list := by
  exact edge_identity (B := (2:ℤ)^153) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000010001 : Branch 1 (-32761639/125000 : ℚ) vp0000000100001000 := by
  apply branch_checked idp00000001000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-32761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-32824139/62500 : ℚ) by norm_num]
  exact coverp00000001000010001
theorem coverp0000000100001000 : Covers (-32761639/125000 : ℚ) vp0000000100001000 := join_branches bp00000001000010000 bp00000001000010001
private noncomputable def vp000000010000100_0 : Blocks := edgeBlocks% "full/vectors/000000010000100-V-0000.bin"
noncomputable def vp000000010000100 : Blocks := vp000000010000100_0
private theorem bp0000000100001000 : Branch 0 (-32761639/250000 : ℚ) vp000000010000100 := by
  apply branch_left_normalized (c:=vp0000000100001000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-32761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-32761639/125000 : ℚ) by norm_num]
  exact coverp0000000100001000
private noncomputable def ep0000000100001001_0 : Blocks := edgeBlocks% "full/vectors/0000000100001001-E-0000.bin"
noncomputable def ep0000000100001001 : Blocks := ep0000000100001001_0
private theorem idp0000000100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000100.list =
    C ((2:ℤ)^62) * horner X vp0000000100001001.list + horner X ep0000000100001001.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100001001 : Branch 1 (-32761639/250000 : ℚ) vp000000010000100 := by
  apply branch_checked idp0000000100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-32761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-32886639/125000 : ℚ) by norm_num]
  exact coverp0000000100001001
theorem coverp000000010000100 : Covers (-32761639/250000 : ℚ) vp000000010000100 := join_branches bp0000000100001000 bp0000000100001001
private noncomputable def vp00000001000010_0 : Blocks := edgeBlocks% "full/vectors/00000001000010-V-0000.bin"
noncomputable def vp00000001000010 : Blocks := vp00000001000010_0
private theorem bp000000010000100 : Branch 0 (-32761639/500000 : ℚ) vp00000001000010 := by
  apply branch_left_normalized (c:=vp000000010000100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-32761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-32761639/250000 : ℚ) by norm_num]
  exact coverp000000010000100
private noncomputable def ep000000010000101_0 : Blocks := edgeBlocks% "full/vectors/000000010000101-E-0000.bin"
noncomputable def ep000000010000101 : Blocks := ep000000010000101_0
private theorem idp000000010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000010.list =
    C ((2:ℤ)^108) * horner X vp000000010000101.list + horner X ep000000010000101.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010000101 : Branch 1 (-32761639/500000 : ℚ) vp00000001000010 := by
  apply branch_checked idp000000010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-32761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-33011639/250000 : ℚ) by norm_num]
  exact coverp000000010000101
theorem coverp00000001000010 : Covers (-32761639/500000 : ℚ) vp00000001000010 := join_branches bp000000010000100 bp000000010000101
private noncomputable def vp0000000100001_0 : Blocks := edgeBlocks% "full/vectors/0000000100001-V-0000.bin"
private noncomputable def vp0000000100001_1 : Blocks := edgeBlocks% "full/vectors/0000000100001-V-0001.bin"
noncomputable def vp0000000100001 : Blocks := (Blocks.join vp0000000100001_0 vp0000000100001_1)
private theorem bp00000001000010 : Branch 0 (-32761639/1000000 : ℚ) vp0000000100001 := by
  apply branch_left_normalized (c:=vp00000001000010) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-32761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-32761639/500000 : ℚ) by norm_num]
  exact coverp00000001000010
private noncomputable def ep00000001000011_0 : Blocks := edgeBlocks% "full/vectors/00000001000011-E-0000.bin"
private noncomputable def ep00000001000011_1 : Blocks := edgeBlocks% "full/vectors/00000001000011-E-0001.bin"
noncomputable def ep00000001000011 : Blocks := (Blocks.join ep00000001000011_0 ep00000001000011_1)
private theorem idp00000001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100001.list =
    C ((2:ℤ)^193) * horner X vp00000001000011.list + horner X ep00000001000011.list := by
  exact edge_identity (B := (2:ℤ)^383) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000011 : Branch 1 (-32761639/1000000 : ℚ) vp0000000100001 := by
  apply branch_checked idp00000001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-32761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-33261639/500000 : ℚ) by norm_num]
  exact coverp00000001000011
theorem coverp0000000100001 : Covers (-32761639/1000000 : ℚ) vp0000000100001 := join_branches bp00000001000010 bp00000001000011
private noncomputable def vp0000000100000111_0 : Blocks := edgeBlocks% "full/vectors/0000000100000111-V-0000.bin"
noncomputable def vp0000000100000111 : Blocks := vp0000000100000111_0
theorem coverp0000000100000111 : Covers (-32636639/125000 : ℚ) vp0000000100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100000110_0 : Blocks := edgeBlocks% "full/vectors/0000000100000110-V-0000.bin"
noncomputable def vp0000000100000110 : Blocks := vp0000000100000110_0
theorem coverp0000000100000110 : Covers (-32511639/125000 : ℚ) vp0000000100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010000011_0 : Blocks := edgeBlocks% "full/vectors/000000010000011-V-0000.bin"
noncomputable def vp000000010000011 : Blocks := vp000000010000011_0
private theorem bp0000000100000110 : Branch 0 (-32511639/250000 : ℚ) vp000000010000011 := by
  apply branch_left_normalized (c:=vp0000000100000110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-32511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-32511639/125000 : ℚ) by norm_num]
  exact coverp0000000100000110
private noncomputable def ep0000000100000111_0 : Blocks := edgeBlocks% "full/vectors/0000000100000111-E-0000.bin"
noncomputable def ep0000000100000111 : Blocks := ep0000000100000111_0
private theorem idp0000000100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000011.list =
    C ((2:ℤ)^66) * horner X vp0000000100000111.list + horner X ep0000000100000111.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100000111 : Branch 1 (-32511639/250000 : ℚ) vp000000010000011 := by
  apply branch_checked idp0000000100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-32511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-32636639/125000 : ℚ) by norm_num]
  exact coverp0000000100000111
theorem coverp000000010000011 : Covers (-32511639/250000 : ℚ) vp000000010000011 := join_branches bp0000000100000110 bp0000000100000111
private noncomputable def vp00000001000001011_0 : Blocks := edgeBlocks% "full/vectors/00000001000001011-V-0000.bin"
noncomputable def vp00000001000001011 : Blocks := vp00000001000001011_0
theorem coverp00000001000001011 : Covers (-32449139/62500 : ℚ) vp00000001000001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001000001010_0 : Blocks := edgeBlocks% "full/vectors/00000001000001010-V-0000.bin"
noncomputable def vp00000001000001010 : Blocks := vp00000001000001010_0
theorem coverp00000001000001010 : Covers (-32386639/62500 : ℚ) vp00000001000001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100000101_0 : Blocks := edgeBlocks% "full/vectors/0000000100000101-V-0000.bin"
noncomputable def vp0000000100000101 : Blocks := vp0000000100000101_0
private theorem bp00000001000001010 : Branch 0 (-32386639/125000 : ℚ) vp0000000100000101 := by
  apply branch_left_normalized (c:=vp00000001000001010) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-32386639/125000 : ℚ) - ((0:ℤ):ℚ) = (-32386639/62500 : ℚ) by norm_num]
  exact coverp00000001000001010
private noncomputable def ep00000001000001011_0 : Blocks := edgeBlocks% "full/vectors/00000001000001011-E-0000.bin"
noncomputable def ep00000001000001011 : Blocks := ep00000001000001011_0
private theorem idp00000001000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100000101.list =
    C ((2:ℤ)^40) * horner X vp00000001000001011.list + horner X ep00000001000001011.list := by
  exact edge_identity (B := (2:ℤ)^153) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000001011 : Branch 1 (-32386639/125000 : ℚ) vp0000000100000101 := by
  apply branch_checked idp00000001000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-32386639/125000 : ℚ) - ((1:ℤ):ℚ) = (-32449139/62500 : ℚ) by norm_num]
  exact coverp00000001000001011
theorem coverp0000000100000101 : Covers (-32386639/125000 : ℚ) vp0000000100000101 := join_branches bp00000001000001010 bp00000001000001011
private noncomputable def vp0000000100000100_0 : Blocks := edgeBlocks% "full/vectors/0000000100000100-V-0000.bin"
noncomputable def vp0000000100000100 : Blocks := vp0000000100000100_0
theorem coverp0000000100000100 : Covers (-32261639/125000 : ℚ) vp0000000100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010000010_0 : Blocks := edgeBlocks% "full/vectors/000000010000010-V-0000.bin"
noncomputable def vp000000010000010 : Blocks := vp000000010000010_0
private theorem bp0000000100000100 : Branch 0 (-32261639/250000 : ℚ) vp000000010000010 := by
  apply branch_left_normalized (c:=vp0000000100000100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-32261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-32261639/125000 : ℚ) by norm_num]
  exact coverp0000000100000100
private noncomputable def ep0000000100000101_0 : Blocks := edgeBlocks% "full/vectors/0000000100000101-E-0000.bin"
noncomputable def ep0000000100000101 : Blocks := ep0000000100000101_0
private theorem idp0000000100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000010.list =
    C ((2:ℤ)^64) * horner X vp0000000100000101.list + horner X ep0000000100000101.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100000101 : Branch 1 (-32261639/250000 : ℚ) vp000000010000010 := by
  apply branch_checked idp0000000100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-32261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-32386639/125000 : ℚ) by norm_num]
  exact coverp0000000100000101
theorem coverp000000010000010 : Covers (-32261639/250000 : ℚ) vp000000010000010 := join_branches bp0000000100000100 bp0000000100000101
private noncomputable def vp00000001000001_0 : Blocks := edgeBlocks% "full/vectors/00000001000001-V-0000.bin"
noncomputable def vp00000001000001 : Blocks := vp00000001000001_0
private theorem bp000000010000010 : Branch 0 (-32261639/500000 : ℚ) vp00000001000001 := by
  apply branch_left_normalized (c:=vp000000010000010) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-32261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-32261639/250000 : ℚ) by norm_num]
  exact coverp000000010000010
private noncomputable def ep000000010000011_0 : Blocks := edgeBlocks% "full/vectors/000000010000011-E-0000.bin"
noncomputable def ep000000010000011 : Blocks := ep000000010000011_0
private theorem idp000000010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000001.list =
    C ((2:ℤ)^108) * horner X vp000000010000011.list + horner X ep000000010000011.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010000011 : Branch 1 (-32261639/500000 : ℚ) vp00000001000001 := by
  apply branch_checked idp000000010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-32261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-32511639/250000 : ℚ) by norm_num]
  exact coverp000000010000011
theorem coverp00000001000001 : Covers (-32261639/500000 : ℚ) vp00000001000001 := join_branches bp000000010000010 bp000000010000011
private noncomputable def vp0000000100000011_0 : Blocks := edgeBlocks% "full/vectors/0000000100000011-V-0000.bin"
noncomputable def vp0000000100000011 : Blocks := vp0000000100000011_0
theorem coverp0000000100000011 : Covers (-32136639/125000 : ℚ) vp0000000100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100000010_0 : Blocks := edgeBlocks% "full/vectors/0000000100000010-V-0000.bin"
noncomputable def vp0000000100000010 : Blocks := vp0000000100000010_0
theorem coverp0000000100000010 : Covers (-32011639/125000 : ℚ) vp0000000100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000010000001_0 : Blocks := edgeBlocks% "full/vectors/000000010000001-V-0000.bin"
noncomputable def vp000000010000001 : Blocks := vp000000010000001_0
private theorem bp0000000100000010 : Branch 0 (-32011639/250000 : ℚ) vp000000010000001 := by
  apply branch_left_normalized (c:=vp0000000100000010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-32011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-32011639/125000 : ℚ) by norm_num]
  exact coverp0000000100000010
private noncomputable def ep0000000100000011_0 : Blocks := edgeBlocks% "full/vectors/0000000100000011-E-0000.bin"
noncomputable def ep0000000100000011 : Blocks := ep0000000100000011_0
private theorem idp0000000100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000001.list =
    C ((2:ℤ)^69) * horner X vp0000000100000011.list + horner X ep0000000100000011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100000011 : Branch 1 (-32011639/250000 : ℚ) vp000000010000001 := by
  apply branch_checked idp0000000100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-32011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-32136639/125000 : ℚ) by norm_num]
  exact coverp0000000100000011
theorem coverp000000010000001 : Covers (-32011639/250000 : ℚ) vp000000010000001 := join_branches bp0000000100000010 bp0000000100000011
private noncomputable def vp00000001000000011_0 : Blocks := edgeBlocks% "full/vectors/00000001000000011-V-0000.bin"
noncomputable def vp00000001000000011 : Blocks := vp00000001000000011_0
theorem coverp00000001000000011 : Covers (-31949139/62500 : ℚ) vp00000001000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001000000010_0 : Blocks := edgeBlocks% "full/vectors/00000001000000010-V-0000.bin"
noncomputable def vp00000001000000010 : Blocks := vp00000001000000010_0
theorem coverp00000001000000010 : Covers (-31886639/62500 : ℚ) vp00000001000000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100000001_0 : Blocks := edgeBlocks% "full/vectors/0000000100000001-V-0000.bin"
noncomputable def vp0000000100000001 : Blocks := vp0000000100000001_0
private theorem bp00000001000000010 : Branch 0 (-31886639/125000 : ℚ) vp0000000100000001 := by
  apply branch_left_normalized (c:=vp00000001000000010) (k:=0) (m:=27) (by decide +kernel)
  rw [show 2*(-31886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-31886639/62500 : ℚ) by norm_num]
  exact coverp00000001000000010
private noncomputable def ep00000001000000011_0 : Blocks := edgeBlocks% "full/vectors/00000001000000011-E-0000.bin"
noncomputable def ep00000001000000011 : Blocks := ep00000001000000011_0
private theorem idp00000001000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100000001.list =
    C ((2:ℤ)^41) * horner X vp00000001000000011.list + horner X ep00000001000000011.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000000011 : Branch 1 (-31886639/125000 : ℚ) vp0000000100000001 := by
  apply branch_checked idp00000001000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-31886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-31949139/62500 : ℚ) by norm_num]
  exact coverp00000001000000011
theorem coverp0000000100000001 : Covers (-31886639/125000 : ℚ) vp0000000100000001 := join_branches bp00000001000000010 bp00000001000000011
private noncomputable def vp00000001000000001_0 : Blocks := edgeBlocks% "full/vectors/00000001000000001-V-0000.bin"
noncomputable def vp00000001000000001 : Blocks := vp00000001000000001_0
theorem coverp00000001000000001 : Covers (-31824139/62500 : ℚ) vp00000001000000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001000000000_0 : Blocks := edgeBlocks% "full/vectors/00000001000000000-V-0000.bin"
noncomputable def vp00000001000000000 : Blocks := vp00000001000000000_0
theorem coverp00000001000000000 : Covers (-31761639/62500 : ℚ) vp00000001000000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000100000000_0 : Blocks := edgeBlocks% "full/vectors/0000000100000000-V-0000.bin"
noncomputable def vp0000000100000000 : Blocks := vp0000000100000000_0
private theorem bp00000001000000000 : Branch 0 (-31761639/125000 : ℚ) vp0000000100000000 := by
  apply branch_left_normalized (c:=vp00000001000000000) (k:=0) (m:=26) (by decide +kernel)
  rw [show 2*(-31761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/62500 : ℚ) by norm_num]
  exact coverp00000001000000000
private noncomputable def ep00000001000000001_0 : Blocks := edgeBlocks% "full/vectors/00000001000000001-E-0000.bin"
noncomputable def ep00000001000000001 : Blocks := ep00000001000000001_0
private theorem idp00000001000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100000000.list =
    C ((2:ℤ)^42) * horner X vp00000001000000001.list + horner X ep00000001000000001.list := by
  exact edge_identity (B := (2:ℤ)^156) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000000001 : Branch 1 (-31761639/125000 : ℚ) vp0000000100000000 := by
  apply branch_checked idp00000001000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-31824139/62500 : ℚ) by norm_num]
  exact coverp00000001000000001
theorem coverp0000000100000000 : Covers (-31761639/125000 : ℚ) vp0000000100000000 := join_branches bp00000001000000000 bp00000001000000001
private noncomputable def vp000000010000000_0 : Blocks := edgeBlocks% "full/vectors/000000010000000-V-0000.bin"
noncomputable def vp000000010000000 : Blocks := vp000000010000000_0
private theorem bp0000000100000000 : Branch 0 (-31761639/250000 : ℚ) vp000000010000000 := by
  apply branch_left_normalized (c:=vp0000000100000000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-31761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/125000 : ℚ) by norm_num]
  exact coverp0000000100000000
private noncomputable def ep0000000100000001_0 : Blocks := edgeBlocks% "full/vectors/0000000100000001-E-0000.bin"
noncomputable def ep0000000100000001 : Blocks := ep0000000100000001_0
private theorem idp0000000100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000000.list =
    C ((2:ℤ)^66) * horner X vp0000000100000001.list + horner X ep0000000100000001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100000001 : Branch 1 (-31761639/250000 : ℚ) vp000000010000000 := by
  apply branch_checked idp0000000100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-31886639/125000 : ℚ) by norm_num]
  exact coverp0000000100000001
theorem coverp000000010000000 : Covers (-31761639/250000 : ℚ) vp000000010000000 := join_branches bp0000000100000000 bp0000000100000001
private noncomputable def vp00000001000000_0 : Blocks := edgeBlocks% "full/vectors/00000001000000-V-0000.bin"
noncomputable def vp00000001000000 : Blocks := vp00000001000000_0
private theorem bp000000010000000 : Branch 0 (-31761639/500000 : ℚ) vp00000001000000 := by
  apply branch_left_normalized (c:=vp000000010000000) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-31761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/250000 : ℚ) by norm_num]
  exact coverp000000010000000
private noncomputable def ep000000010000001_0 : Blocks := edgeBlocks% "full/vectors/000000010000001-E-0000.bin"
noncomputable def ep000000010000001 : Blocks := ep000000010000001_0
private theorem idp000000010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000000.list =
    C ((2:ℤ)^110) * horner X vp000000010000001.list + horner X ep000000010000001.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010000001 : Branch 1 (-31761639/500000 : ℚ) vp00000001000000 := by
  apply branch_checked idp000000010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-32011639/250000 : ℚ) by norm_num]
  exact coverp000000010000001
theorem coverp00000001000000 : Covers (-31761639/500000 : ℚ) vp00000001000000 := join_branches bp000000010000000 bp000000010000001
private noncomputable def vp0000000100000_0 : Blocks := edgeBlocks% "full/vectors/0000000100000-V-0000.bin"
private noncomputable def vp0000000100000_1 : Blocks := edgeBlocks% "full/vectors/0000000100000-V-0001.bin"
noncomputable def vp0000000100000 : Blocks := (Blocks.join vp0000000100000_0 vp0000000100000_1)
private theorem bp00000001000000 : Branch 0 (-31761639/1000000 : ℚ) vp0000000100000 := by
  apply branch_left_normalized (c:=vp00000001000000) (k:=0) (m:=109) (by decide +kernel)
  rw [show 2*(-31761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/500000 : ℚ) by norm_num]
  exact coverp00000001000000
private noncomputable def ep00000001000001_0 : Blocks := edgeBlocks% "full/vectors/00000001000001-E-0000.bin"
private noncomputable def ep00000001000001_1 : Blocks := edgeBlocks% "full/vectors/00000001000001-E-0001.bin"
noncomputable def ep00000001000001 : Blocks := (Blocks.join ep00000001000001_0 ep00000001000001_1)
private theorem idp00000001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100000.list =
    C ((2:ℤ)^202) * horner X vp00000001000001.list + horner X ep00000001000001.list := by
  exact edge_identity (B := (2:ℤ)^392) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001000001 : Branch 1 (-31761639/1000000 : ℚ) vp0000000100000 := by
  apply branch_checked idp00000001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-32261639/500000 : ℚ) by norm_num]
  exact coverp00000001000001
theorem coverp0000000100000 : Covers (-31761639/1000000 : ℚ) vp0000000100000 := join_branches bp00000001000000 bp00000001000001
private noncomputable def vp000000010000_0 : Blocks := edgeBlocks% "full/vectors/000000010000-V-0000.bin"
private noncomputable def vp000000010000_1 : Blocks := edgeBlocks% "full/vectors/000000010000-V-0001.bin"
private noncomputable def vp000000010000_2 : Blocks := edgeBlocks% "full/vectors/000000010000-V-0002.bin"
noncomputable def vp000000010000 : Blocks := (Blocks.join vp000000010000_0 (Blocks.join vp000000010000_1 vp000000010000_2))
private theorem bp0000000100000 : Branch 0 (-31761639/2000000 : ℚ) vp000000010000 := by
  apply branch_left_normalized (c:=vp0000000100000) (k:=0) (m:=196) (by decide +kernel)
  rw [show 2*(-31761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/1000000 : ℚ) by norm_num]
  exact coverp0000000100000
private noncomputable def ep0000000100001_0 : Blocks := edgeBlocks% "full/vectors/0000000100001-E-0000.bin"
private noncomputable def ep0000000100001_1 : Blocks := edgeBlocks% "full/vectors/0000000100001-E-0001.bin"
private noncomputable def ep0000000100001_2 : Blocks := edgeBlocks% "full/vectors/0000000100001-E-0002.bin"
noncomputable def ep0000000100001 : Blocks := (Blocks.join ep0000000100001_0 (Blocks.join ep0000000100001_1 ep0000000100001_2))
private theorem idp0000000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010000.list =
    C ((2:ℤ)^379) * horner X vp0000000100001.list + horner X ep0000000100001.list := by
  exact edge_identity (B := (2:ℤ)^657) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000100001 : Branch 1 (-31761639/2000000 : ℚ) vp000000010000 := by
  apply branch_checked idp0000000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-32761639/1000000 : ℚ) by norm_num]
  exact coverp0000000100001
theorem coverp000000010000 : Covers (-31761639/2000000 : ℚ) vp000000010000 := join_branches bp0000000100000 bp0000000100001
private noncomputable def vp00000001000_0 : Blocks := edgeBlocks% "full/vectors/00000001000-V-0000.bin"
private noncomputable def vp00000001000_1 : Blocks := edgeBlocks% "full/vectors/00000001000-V-0001.bin"
private noncomputable def vp00000001000_2 : Blocks := edgeBlocks% "full/vectors/00000001000-V-0002.bin"
private noncomputable def vp00000001000_3 : Blocks := edgeBlocks% "full/vectors/00000001000-V-0003.bin"
private noncomputable def vp00000001000_4 : Blocks := edgeBlocks% "full/vectors/00000001000-V-0004.bin"
private noncomputable def vp00000001000_5 : Blocks := edgeBlocks% "full/vectors/00000001000-V-0005.bin"
noncomputable def vp00000001000 : Blocks := (Blocks.join (Blocks.join vp00000001000_0 (Blocks.join vp00000001000_1 vp00000001000_2)) (Blocks.join vp00000001000_3 (Blocks.join vp00000001000_4 vp00000001000_5)))
private theorem bp000000010000 : Branch 0 (-31761639/4000000 : ℚ) vp00000001000 := by
  apply branch_left_normalized (c:=vp000000010000) (k:=0) (m:=369) (by decide +kernel)
  rw [show 2*(-31761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/2000000 : ℚ) by norm_num]
  exact coverp000000010000
private noncomputable def ep000000010001_0 : Blocks := edgeBlocks% "full/vectors/000000010001-E-0000.bin"
private noncomputable def ep000000010001_1 : Blocks := edgeBlocks% "full/vectors/000000010001-E-0001.bin"
private noncomputable def ep000000010001_2 : Blocks := edgeBlocks% "full/vectors/000000010001-E-0002.bin"
private noncomputable def ep000000010001_3 : Blocks := edgeBlocks% "full/vectors/000000010001-E-0003.bin"
private noncomputable def ep000000010001_4 : Blocks := edgeBlocks% "full/vectors/000000010001-E-0004.bin"
private noncomputable def ep000000010001_5 : Blocks := edgeBlocks% "full/vectors/000000010001-E-0005.bin"
noncomputable def ep000000010001 : Blocks := (Blocks.join (Blocks.join ep000000010001_0 (Blocks.join ep000000010001_1 ep000000010001_2)) (Blocks.join ep000000010001_3 (Blocks.join ep000000010001_4 ep000000010001_5)))
private theorem idp000000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001000.list =
    C ((2:ℤ)^726) * horner X vp000000010001.list + horner X ep000000010001.list := by
  exact edge_identity (B := (2:ℤ)^1183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000010001 : Branch 1 (-31761639/4000000 : ℚ) vp00000001000 := by
  apply branch_checked idp000000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-33761639/2000000 : ℚ) by norm_num]
  exact coverp000000010001
theorem coverp00000001000 : Covers (-31761639/4000000 : ℚ) vp00000001000 := join_branches bp000000010000 bp000000010001
private noncomputable def vp0000000100_0 : Blocks := edgeBlocks% "full/vectors/0000000100-V-0000.bin"
private noncomputable def vp0000000100_1 : Blocks := edgeBlocks% "full/vectors/0000000100-V-0001.bin"
private noncomputable def vp0000000100_2 : Blocks := edgeBlocks% "full/vectors/0000000100-V-0002.bin"
private noncomputable def vp0000000100_3 : Blocks := edgeBlocks% "full/vectors/0000000100-V-0003.bin"
private noncomputable def vp0000000100_4 : Blocks := edgeBlocks% "full/vectors/0000000100-V-0004.bin"
private noncomputable def vp0000000100_5 : Blocks := edgeBlocks% "full/vectors/0000000100-V-0005.bin"
private noncomputable def vp0000000100_6 : Blocks := edgeBlocks% "full/vectors/0000000100-V-0006.bin"
private noncomputable def vp0000000100_7 : Blocks := edgeBlocks% "full/vectors/0000000100-V-0007.bin"
private noncomputable def vp0000000100_8 : Blocks := edgeBlocks% "full/vectors/0000000100-V-0008.bin"
private noncomputable def vp0000000100_9 : Blocks := edgeBlocks% "full/vectors/0000000100-V-0009.bin"
private noncomputable def vp0000000100_10 : Blocks := edgeBlocks% "full/vectors/0000000100-V-0010.bin"
noncomputable def vp0000000100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0000000100_0 vp0000000100_1) (Blocks.join vp0000000100_2 (Blocks.join vp0000000100_3 vp0000000100_4))) (Blocks.join (Blocks.join vp0000000100_5 (Blocks.join vp0000000100_6 vp0000000100_7)) (Blocks.join vp0000000100_8 (Blocks.join vp0000000100_9 vp0000000100_10))))
private theorem bp00000001000 : Branch 0 (-31761639/8000000 : ℚ) vp0000000100 := by
  apply branch_left_normalized (c:=vp00000001000) (k:=0) (m:=712) (by decide +kernel)
  rw [show 2*(-31761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/4000000 : ℚ) by norm_num]
  exact coverp00000001000
private noncomputable def ep00000001001_0 : Blocks := edgeBlocks% "full/vectors/00000001001-E-0000.bin"
private noncomputable def ep00000001001_1 : Blocks := edgeBlocks% "full/vectors/00000001001-E-0001.bin"
private noncomputable def ep00000001001_2 : Blocks := edgeBlocks% "full/vectors/00000001001-E-0002.bin"
private noncomputable def ep00000001001_3 : Blocks := edgeBlocks% "full/vectors/00000001001-E-0003.bin"
private noncomputable def ep00000001001_4 : Blocks := edgeBlocks% "full/vectors/00000001001-E-0004.bin"
private noncomputable def ep00000001001_5 : Blocks := edgeBlocks% "full/vectors/00000001001-E-0005.bin"
private noncomputable def ep00000001001_6 : Blocks := edgeBlocks% "full/vectors/00000001001-E-0006.bin"
private noncomputable def ep00000001001_7 : Blocks := edgeBlocks% "full/vectors/00000001001-E-0007.bin"
private noncomputable def ep00000001001_8 : Blocks := edgeBlocks% "full/vectors/00000001001-E-0008.bin"
private noncomputable def ep00000001001_9 : Blocks := edgeBlocks% "full/vectors/00000001001-E-0009.bin"
private noncomputable def ep00000001001_10 : Blocks := edgeBlocks% "full/vectors/00000001001-E-0010.bin"
noncomputable def ep00000001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00000001001_0 ep00000001001_1) (Blocks.join ep00000001001_2 (Blocks.join ep00000001001_3 ep00000001001_4))) (Blocks.join (Blocks.join ep00000001001_5 (Blocks.join ep00000001001_6 ep00000001001_7)) (Blocks.join ep00000001001_8 (Blocks.join ep00000001001_9 ep00000001001_10))))
private theorem idp00000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000100.list =
    C ((2:ℤ)^1415) * horner X vp00000001001.list + horner X ep00000001001.list := by
  exact edge_identity (B := (2:ℤ)^2221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001001 : Branch 1 (-31761639/8000000 : ℚ) vp0000000100 := by
  apply branch_checked idp00000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-35761639/4000000 : ℚ) by norm_num]
  exact coverp00000001001
theorem coverp0000000100 : Covers (-31761639/8000000 : ℚ) vp0000000100 := join_branches bp00000001000 bp00000001001
private noncomputable def vp000000010_0 : Blocks := edgeBlocks% "full/vectors/000000010-V-0000.bin"
private noncomputable def vp000000010_1 : Blocks := edgeBlocks% "full/vectors/000000010-V-0001.bin"
private noncomputable def vp000000010_2 : Blocks := edgeBlocks% "full/vectors/000000010-V-0002.bin"
private noncomputable def vp000000010_3 : Blocks := edgeBlocks% "full/vectors/000000010-V-0003.bin"
private noncomputable def vp000000010_4 : Blocks := edgeBlocks% "full/vectors/000000010-V-0004.bin"
private noncomputable def vp000000010_5 : Blocks := edgeBlocks% "full/vectors/000000010-V-0005.bin"
private noncomputable def vp000000010_6 : Blocks := edgeBlocks% "full/vectors/000000010-V-0006.bin"
private noncomputable def vp000000010_7 : Blocks := edgeBlocks% "full/vectors/000000010-V-0007.bin"
private noncomputable def vp000000010_8 : Blocks := edgeBlocks% "full/vectors/000000010-V-0008.bin"
private noncomputable def vp000000010_9 : Blocks := edgeBlocks% "full/vectors/000000010-V-0009.bin"
private noncomputable def vp000000010_10 : Blocks := edgeBlocks% "full/vectors/000000010-V-0010.bin"
private noncomputable def vp000000010_11 : Blocks := edgeBlocks% "full/vectors/000000010-V-0011.bin"
private noncomputable def vp000000010_12 : Blocks := edgeBlocks% "full/vectors/000000010-V-0012.bin"
private noncomputable def vp000000010_13 : Blocks := edgeBlocks% "full/vectors/000000010-V-0013.bin"
private noncomputable def vp000000010_14 : Blocks := edgeBlocks% "full/vectors/000000010-V-0014.bin"
private noncomputable def vp000000010_15 : Blocks := edgeBlocks% "full/vectors/000000010-V-0015.bin"
private noncomputable def vp000000010_16 : Blocks := edgeBlocks% "full/vectors/000000010-V-0016.bin"
private noncomputable def vp000000010_17 : Blocks := edgeBlocks% "full/vectors/000000010-V-0017.bin"
private noncomputable def vp000000010_18 : Blocks := edgeBlocks% "full/vectors/000000010-V-0018.bin"
private noncomputable def vp000000010_19 : Blocks := edgeBlocks% "full/vectors/000000010-V-0019.bin"
private noncomputable def vp000000010_20 : Blocks := edgeBlocks% "full/vectors/000000010-V-0020.bin"
private noncomputable def vp000000010_21 : Blocks := edgeBlocks% "full/vectors/000000010-V-0021.bin"
noncomputable def vp000000010 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000000010_0 vp000000010_1) (Blocks.join vp000000010_2 (Blocks.join vp000000010_3 vp000000010_4))) (Blocks.join (Blocks.join vp000000010_5 (Blocks.join vp000000010_6 vp000000010_7)) (Blocks.join vp000000010_8 (Blocks.join vp000000010_9 vp000000010_10)))) (Blocks.join (Blocks.join (Blocks.join vp000000010_11 vp000000010_12) (Blocks.join vp000000010_13 (Blocks.join vp000000010_14 vp000000010_15))) (Blocks.join (Blocks.join vp000000010_16 (Blocks.join vp000000010_17 vp000000010_18)) (Blocks.join vp000000010_19 (Blocks.join vp000000010_20 vp000000010_21)))))
private theorem bp0000000100 : Branch 0 (-31761639/16000000 : ℚ) vp000000010 := by
  apply branch_left_normalized (c:=vp0000000100) (k:=0) (m:=1385) (by decide +kernel)
  rw [show 2*(-31761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-31761639/8000000 : ℚ) by norm_num]
  exact coverp0000000100
private noncomputable def ep0000000101_0 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0000.bin"
private noncomputable def ep0000000101_1 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0001.bin"
private noncomputable def ep0000000101_2 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0002.bin"
private noncomputable def ep0000000101_3 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0003.bin"
private noncomputable def ep0000000101_4 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0004.bin"
private noncomputable def ep0000000101_5 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0005.bin"
private noncomputable def ep0000000101_6 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0006.bin"
private noncomputable def ep0000000101_7 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0007.bin"
private noncomputable def ep0000000101_8 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0008.bin"
private noncomputable def ep0000000101_9 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0009.bin"
private noncomputable def ep0000000101_10 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0010.bin"
private noncomputable def ep0000000101_11 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0011.bin"
private noncomputable def ep0000000101_12 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0012.bin"
private noncomputable def ep0000000101_13 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0013.bin"
private noncomputable def ep0000000101_14 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0014.bin"
private noncomputable def ep0000000101_15 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0015.bin"
private noncomputable def ep0000000101_16 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0016.bin"
private noncomputable def ep0000000101_17 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0017.bin"
private noncomputable def ep0000000101_18 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0018.bin"
private noncomputable def ep0000000101_19 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0019.bin"
private noncomputable def ep0000000101_20 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0020.bin"
private noncomputable def ep0000000101_21 : Blocks := edgeBlocks% "full/vectors/0000000101-E-0021.bin"
noncomputable def ep0000000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000000101_0 ep0000000101_1) (Blocks.join ep0000000101_2 (Blocks.join ep0000000101_3 ep0000000101_4))) (Blocks.join (Blocks.join ep0000000101_5 (Blocks.join ep0000000101_6 ep0000000101_7)) (Blocks.join ep0000000101_8 (Blocks.join ep0000000101_9 ep0000000101_10)))) (Blocks.join (Blocks.join (Blocks.join ep0000000101_11 ep0000000101_12) (Blocks.join ep0000000101_13 (Blocks.join ep0000000101_14 ep0000000101_15))) (Blocks.join (Blocks.join ep0000000101_16 (Blocks.join ep0000000101_17 ep0000000101_18)) (Blocks.join ep0000000101_19 (Blocks.join ep0000000101_20 ep0000000101_21)))))
private theorem idp0000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000010.list =
    C ((2:ℤ)^2750) * horner X vp0000000101.list + horner X ep0000000101.list := by
  exact edge_identity (B := (2:ℤ)^4247) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000101 : Branch 1 (-31761639/16000000 : ℚ) vp000000010 := by
  apply branch_checked idp0000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-31761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-39761639/8000000 : ℚ) by norm_num]
  exact coverp0000000101
theorem coverp000000010 : Covers (-31761639/16000000 : ℚ) vp000000010 := join_branches bp0000000100 bp0000000101
end NextProof.EdgeFull

