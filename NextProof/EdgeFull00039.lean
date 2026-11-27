import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000100111111_0 : Blocks := edgeBlocks% "full/vectors/00000100111111-V-0000.bin"
noncomputable def vp00000100111111 : Blocks := vp00000100111111_0
theorem coverp00000100111111 : Covers (-159261639/500000 : ℚ) vp00000100111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100111110_0 : Blocks := edgeBlocks% "full/vectors/00000100111110-V-0000.bin"
noncomputable def vp00000100111110 : Blocks := vp00000100111110_0
theorem coverp00000100111110 : Covers (-158761639/500000 : ℚ) vp00000100111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010011111_0 : Blocks := edgeBlocks% "full/vectors/0000010011111-V-0000.bin"
noncomputable def vp0000010011111 : Blocks := vp0000010011111_0
private theorem bp00000100111110 : Branch 0 (-158761639/1000000 : ℚ) vp0000010011111 := by
  apply branch_left_normalized (c:=vp00000100111110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-158761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-158761639/500000 : ℚ) by norm_num]
  exact coverp00000100111110
private noncomputable def ep00000100111111_0 : Blocks := edgeBlocks% "full/vectors/00000100111111-E-0000.bin"
noncomputable def ep00000100111111 : Blocks := ep00000100111111_0
private theorem idp00000100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010011111.list =
    C ((2:ℤ)^101) * horner X vp00000100111111.list + horner X ep00000100111111.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100111111 : Branch 1 (-158761639/1000000 : ℚ) vp0000010011111 := by
  apply branch_checked idp00000100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-158761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-159261639/500000 : ℚ) by norm_num]
  exact coverp00000100111111
theorem coverp0000010011111 : Covers (-158761639/1000000 : ℚ) vp0000010011111 := join_branches bp00000100111110 bp00000100111111
private noncomputable def vp00000100111101_0 : Blocks := edgeBlocks% "full/vectors/00000100111101-V-0000.bin"
noncomputable def vp00000100111101 : Blocks := vp00000100111101_0
theorem coverp00000100111101 : Covers (-158261639/500000 : ℚ) vp00000100111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001111001_0 : Blocks := edgeBlocks% "full/vectors/000001001111001-V-0000.bin"
noncomputable def vp000001001111001 : Blocks := vp000001001111001_0
theorem coverp000001001111001 : Covers (-158011639/250000 : ℚ) vp000001001111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001111000_0 : Blocks := edgeBlocks% "full/vectors/000001001111000-V-0000.bin"
noncomputable def vp000001001111000 : Blocks := vp000001001111000_0
theorem coverp000001001111000 : Covers (-157761639/250000 : ℚ) vp000001001111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100111100_0 : Blocks := edgeBlocks% "full/vectors/00000100111100-V-0000.bin"
noncomputable def vp00000100111100 : Blocks := vp00000100111100_0
private theorem bp000001001111000 : Branch 0 (-157761639/500000 : ℚ) vp00000100111100 := by
  apply branch_left_normalized (c:=vp000001001111000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-157761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-157761639/250000 : ℚ) by norm_num]
  exact coverp000001001111000
private noncomputable def ep000001001111001_0 : Blocks := edgeBlocks% "full/vectors/000001001111001-E-0000.bin"
noncomputable def ep000001001111001 : Blocks := ep000001001111001_0
private theorem idp000001001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100111100.list =
    C ((2:ℤ)^64) * horner X vp000001001111001.list + horner X ep000001001111001.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001111001 : Branch 1 (-157761639/500000 : ℚ) vp00000100111100 := by
  apply branch_checked idp000001001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-157761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-158011639/250000 : ℚ) by norm_num]
  exact coverp000001001111001
theorem coverp00000100111100 : Covers (-157761639/500000 : ℚ) vp00000100111100 := join_branches bp000001001111000 bp000001001111001
private noncomputable def vp0000010011110_0 : Blocks := edgeBlocks% "full/vectors/0000010011110-V-0000.bin"
noncomputable def vp0000010011110 : Blocks := vp0000010011110_0
private theorem bp00000100111100 : Branch 0 (-157761639/1000000 : ℚ) vp0000010011110 := by
  apply branch_left_normalized (c:=vp00000100111100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-157761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-157761639/500000 : ℚ) by norm_num]
  exact coverp00000100111100
private noncomputable def ep00000100111101_0 : Blocks := edgeBlocks% "full/vectors/00000100111101-E-0000.bin"
noncomputable def ep00000100111101 : Blocks := ep00000100111101_0
private theorem idp00000100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010011110.list =
    C ((2:ℤ)^109) * horner X vp00000100111101.list + horner X ep00000100111101.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100111101 : Branch 1 (-157761639/1000000 : ℚ) vp0000010011110 := by
  apply branch_checked idp00000100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-157761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-158261639/500000 : ℚ) by norm_num]
  exact coverp00000100111101
theorem coverp0000010011110 : Covers (-157761639/1000000 : ℚ) vp0000010011110 := join_branches bp00000100111100 bp00000100111101
private noncomputable def vp000001001111_0 : Blocks := edgeBlocks% "full/vectors/000001001111-V-0000.bin"
private noncomputable def vp000001001111_1 : Blocks := edgeBlocks% "full/vectors/000001001111-V-0001.bin"
noncomputable def vp000001001111 : Blocks := (Blocks.join vp000001001111_0 vp000001001111_1)
private theorem bp0000010011110 : Branch 0 (-157761639/2000000 : ℚ) vp000001001111 := by
  apply branch_left_normalized (c:=vp0000010011110) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-157761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-157761639/1000000 : ℚ) by norm_num]
  exact coverp0000010011110
private noncomputable def ep0000010011111_0 : Blocks := edgeBlocks% "full/vectors/0000010011111-E-0000.bin"
private noncomputable def ep0000010011111_1 : Blocks := edgeBlocks% "full/vectors/0000010011111-E-0001.bin"
noncomputable def ep0000010011111 : Blocks := (Blocks.join ep0000010011111_0 ep0000010011111_1)
private theorem idp0000010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001001111.list =
    C ((2:ℤ)^191) * horner X vp0000010011111.list + horner X ep0000010011111.list := by
  exact edge_identity (B := (2:ℤ)^363) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010011111 : Branch 1 (-157761639/2000000 : ℚ) vp000001001111 := by
  apply branch_checked idp0000010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-157761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-158761639/1000000 : ℚ) by norm_num]
  exact coverp0000010011111
theorem coverp000001001111 : Covers (-157761639/2000000 : ℚ) vp000001001111 := join_branches bp0000010011110 bp0000010011111
private noncomputable def vp0000010011101111_0 : Blocks := edgeBlocks% "full/vectors/0000010011101111-V-0000.bin"
noncomputable def vp0000010011101111 : Blocks := vp0000010011101111_0
theorem coverp0000010011101111 : Covers (-157636639/125000 : ℚ) vp0000010011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000010011101110_0 : Blocks := edgeBlocks% "full/vectors/0000010011101110-V-0000.bin"
noncomputable def vp0000010011101110 : Blocks := vp0000010011101110_0
theorem coverp0000010011101110 : Covers (-157511639/125000 : ℚ) vp0000010011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001110111_0 : Blocks := edgeBlocks% "full/vectors/000001001110111-V-0000.bin"
noncomputable def vp000001001110111 : Blocks := vp000001001110111_0
private theorem bp0000010011101110 : Branch 0 (-157511639/250000 : ℚ) vp000001001110111 := by
  apply branch_left_normalized (c:=vp0000010011101110) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-157511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-157511639/125000 : ℚ) by norm_num]
  exact coverp0000010011101110
private noncomputable def ep0000010011101111_0 : Blocks := edgeBlocks% "full/vectors/0000010011101111-E-0000.bin"
noncomputable def ep0000010011101111 : Blocks := ep0000010011101111_0
private theorem idp0000010011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001001110111.list =
    C ((2:ℤ)^38) * horner X vp0000010011101111.list + horner X ep0000010011101111.list := by
  exact edge_identity (B := (2:ℤ)^150) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010011101111 : Branch 1 (-157511639/250000 : ℚ) vp000001001110111 := by
  apply branch_checked idp0000010011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-157511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-157636639/125000 : ℚ) by norm_num]
  exact coverp0000010011101111
theorem coverp000001001110111 : Covers (-157511639/250000 : ℚ) vp000001001110111 := join_branches bp0000010011101110 bp0000010011101111
private noncomputable def vp000001001110110_0 : Blocks := edgeBlocks% "full/vectors/000001001110110-V-0000.bin"
noncomputable def vp000001001110110 : Blocks := vp000001001110110_0
theorem coverp000001001110110 : Covers (-157261639/250000 : ℚ) vp000001001110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100111011_0 : Blocks := edgeBlocks% "full/vectors/00000100111011-V-0000.bin"
noncomputable def vp00000100111011 : Blocks := vp00000100111011_0
private theorem bp000001001110110 : Branch 0 (-157261639/500000 : ℚ) vp00000100111011 := by
  apply branch_left_normalized (c:=vp000001001110110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-157261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-157261639/250000 : ℚ) by norm_num]
  exact coverp000001001110110
private noncomputable def ep000001001110111_0 : Blocks := edgeBlocks% "full/vectors/000001001110111-E-0000.bin"
noncomputable def ep000001001110111 : Blocks := ep000001001110111_0
private theorem idp000001001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100111011.list =
    C ((2:ℤ)^58) * horner X vp000001001110111.list + horner X ep000001001110111.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001110111 : Branch 1 (-157261639/500000 : ℚ) vp00000100111011 := by
  apply branch_checked idp000001001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-157261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-157511639/250000 : ℚ) by norm_num]
  exact coverp000001001110111
theorem coverp00000100111011 : Covers (-157261639/500000 : ℚ) vp00000100111011 := join_branches bp000001001110110 bp000001001110111
private noncomputable def vp000001001110101_0 : Blocks := edgeBlocks% "full/vectors/000001001110101-V-0000.bin"
noncomputable def vp000001001110101 : Blocks := vp000001001110101_0
theorem coverp000001001110101 : Covers (-157011639/250000 : ℚ) vp000001001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001110100_0 : Blocks := edgeBlocks% "full/vectors/000001001110100-V-0000.bin"
noncomputable def vp000001001110100 : Blocks := vp000001001110100_0
theorem coverp000001001110100 : Covers (-156761639/250000 : ℚ) vp000001001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100111010_0 : Blocks := edgeBlocks% "full/vectors/00000100111010-V-0000.bin"
noncomputable def vp00000100111010 : Blocks := vp00000100111010_0
private theorem bp000001001110100 : Branch 0 (-156761639/500000 : ℚ) vp00000100111010 := by
  apply branch_left_normalized (c:=vp000001001110100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-156761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-156761639/250000 : ℚ) by norm_num]
  exact coverp000001001110100
private noncomputable def ep000001001110101_0 : Blocks := edgeBlocks% "full/vectors/000001001110101-E-0000.bin"
noncomputable def ep000001001110101 : Blocks := ep000001001110101_0
private theorem idp000001001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100111010.list =
    C ((2:ℤ)^59) * horner X vp000001001110101.list + horner X ep000001001110101.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001110101 : Branch 1 (-156761639/500000 : ℚ) vp00000100111010 := by
  apply branch_checked idp000001001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-156761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-157011639/250000 : ℚ) by norm_num]
  exact coverp000001001110101
theorem coverp00000100111010 : Covers (-156761639/500000 : ℚ) vp00000100111010 := join_branches bp000001001110100 bp000001001110101
private noncomputable def vp0000010011101_0 : Blocks := edgeBlocks% "full/vectors/0000010011101-V-0000.bin"
noncomputable def vp0000010011101 : Blocks := vp0000010011101_0
private theorem bp00000100111010 : Branch 0 (-156761639/1000000 : ℚ) vp0000010011101 := by
  apply branch_left_normalized (c:=vp00000100111010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-156761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-156761639/500000 : ℚ) by norm_num]
  exact coverp00000100111010
private noncomputable def ep00000100111011_0 : Blocks := edgeBlocks% "full/vectors/00000100111011-E-0000.bin"
noncomputable def ep00000100111011 : Blocks := ep00000100111011_0
private theorem idp00000100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010011101.list =
    C ((2:ℤ)^99) * horner X vp00000100111011.list + horner X ep00000100111011.list := by
  exact edge_identity (B := (2:ℤ)^236) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100111011 : Branch 1 (-156761639/1000000 : ℚ) vp0000010011101 := by
  apply branch_checked idp00000100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-156761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-157261639/500000 : ℚ) by norm_num]
  exact coverp00000100111011
theorem coverp0000010011101 : Covers (-156761639/1000000 : ℚ) vp0000010011101 := join_branches bp00000100111010 bp00000100111011
private noncomputable def vp000001001110011_0 : Blocks := edgeBlocks% "full/vectors/000001001110011-V-0000.bin"
noncomputable def vp000001001110011 : Blocks := vp000001001110011_0
theorem coverp000001001110011 : Covers (-156511639/250000 : ℚ) vp000001001110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001110010_0 : Blocks := edgeBlocks% "full/vectors/000001001110010-V-0000.bin"
noncomputable def vp000001001110010 : Blocks := vp000001001110010_0
theorem coverp000001001110010 : Covers (-156261639/250000 : ℚ) vp000001001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100111001_0 : Blocks := edgeBlocks% "full/vectors/00000100111001-V-0000.bin"
noncomputable def vp00000100111001 : Blocks := vp00000100111001_0
private theorem bp000001001110010 : Branch 0 (-156261639/500000 : ℚ) vp00000100111001 := by
  apply branch_left_normalized (c:=vp000001001110010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-156261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-156261639/250000 : ℚ) by norm_num]
  exact coverp000001001110010
private noncomputable def ep000001001110011_0 : Blocks := edgeBlocks% "full/vectors/000001001110011-E-0000.bin"
noncomputable def ep000001001110011 : Blocks := ep000001001110011_0
private theorem idp000001001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100111001.list =
    C ((2:ℤ)^60) * horner X vp000001001110011.list + horner X ep000001001110011.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001110011 : Branch 1 (-156261639/500000 : ℚ) vp00000100111001 := by
  apply branch_checked idp000001001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-156261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-156511639/250000 : ℚ) by norm_num]
  exact coverp000001001110011
theorem coverp00000100111001 : Covers (-156261639/500000 : ℚ) vp00000100111001 := join_branches bp000001001110010 bp000001001110011
private noncomputable def vp000001001110001_0 : Blocks := edgeBlocks% "full/vectors/000001001110001-V-0000.bin"
noncomputable def vp000001001110001 : Blocks := vp000001001110001_0
theorem coverp000001001110001 : Covers (-156011639/250000 : ℚ) vp000001001110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001110000_0 : Blocks := edgeBlocks% "full/vectors/000001001110000-V-0000.bin"
noncomputable def vp000001001110000 : Blocks := vp000001001110000_0
theorem coverp000001001110000 : Covers (-155761639/250000 : ℚ) vp000001001110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100111000_0 : Blocks := edgeBlocks% "full/vectors/00000100111000-V-0000.bin"
noncomputable def vp00000100111000 : Blocks := vp00000100111000_0
private theorem bp000001001110000 : Branch 0 (-155761639/500000 : ℚ) vp00000100111000 := by
  apply branch_left_normalized (c:=vp000001001110000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-155761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-155761639/250000 : ℚ) by norm_num]
  exact coverp000001001110000
private noncomputable def ep000001001110001_0 : Blocks := edgeBlocks% "full/vectors/000001001110001-E-0000.bin"
noncomputable def ep000001001110001 : Blocks := ep000001001110001_0
private theorem idp000001001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100111000.list =
    C ((2:ℤ)^60) * horner X vp000001001110001.list + horner X ep000001001110001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001110001 : Branch 1 (-155761639/500000 : ℚ) vp00000100111000 := by
  apply branch_checked idp000001001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-155761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-156011639/250000 : ℚ) by norm_num]
  exact coverp000001001110001
theorem coverp00000100111000 : Covers (-155761639/500000 : ℚ) vp00000100111000 := join_branches bp000001001110000 bp000001001110001
private noncomputable def vp0000010011100_0 : Blocks := edgeBlocks% "full/vectors/0000010011100-V-0000.bin"
noncomputable def vp0000010011100 : Blocks := vp0000010011100_0
private theorem bp00000100111000 : Branch 0 (-155761639/1000000 : ℚ) vp0000010011100 := by
  apply branch_left_normalized (c:=vp00000100111000) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-155761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-155761639/500000 : ℚ) by norm_num]
  exact coverp00000100111000
private noncomputable def ep00000100111001_0 : Blocks := edgeBlocks% "full/vectors/00000100111001-E-0000.bin"
noncomputable def ep00000100111001 : Blocks := ep00000100111001_0
private theorem idp00000100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010011100.list =
    C ((2:ℤ)^101) * horner X vp00000100111001.list + horner X ep00000100111001.list := by
  exact edge_identity (B := (2:ℤ)^237) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100111001 : Branch 1 (-155761639/1000000 : ℚ) vp0000010011100 := by
  apply branch_checked idp00000100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-155761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-156261639/500000 : ℚ) by norm_num]
  exact coverp00000100111001
theorem coverp0000010011100 : Covers (-155761639/1000000 : ℚ) vp0000010011100 := join_branches bp00000100111000 bp00000100111001
private noncomputable def vp000001001110_0 : Blocks := edgeBlocks% "full/vectors/000001001110-V-0000.bin"
private noncomputable def vp000001001110_1 : Blocks := edgeBlocks% "full/vectors/000001001110-V-0001.bin"
noncomputable def vp000001001110 : Blocks := (Blocks.join vp000001001110_0 vp000001001110_1)
private theorem bp0000010011100 : Branch 0 (-155761639/2000000 : ℚ) vp000001001110 := by
  apply branch_left_normalized (c:=vp0000010011100) (k:=0) (m:=97) (by decide +kernel)
  rw [show 2*(-155761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-155761639/1000000 : ℚ) by norm_num]
  exact coverp0000010011100
private noncomputable def ep0000010011101_0 : Blocks := edgeBlocks% "full/vectors/0000010011101-E-0000.bin"
private noncomputable def ep0000010011101_1 : Blocks := edgeBlocks% "full/vectors/0000010011101-E-0001.bin"
noncomputable def ep0000010011101 : Blocks := (Blocks.join ep0000010011101_0 ep0000010011101_1)
private theorem idp0000010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001001110.list =
    C ((2:ℤ)^183) * horner X vp0000010011101.list + horner X ep0000010011101.list := by
  exact edge_identity (B := (2:ℤ)^357) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010011101 : Branch 1 (-155761639/2000000 : ℚ) vp000001001110 := by
  apply branch_checked idp0000010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-155761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-156761639/1000000 : ℚ) by norm_num]
  exact coverp0000010011101
theorem coverp000001001110 : Covers (-155761639/2000000 : ℚ) vp000001001110 := join_branches bp0000010011100 bp0000010011101
private noncomputable def vp00000100111_0 : Blocks := edgeBlocks% "full/vectors/00000100111-V-0000.bin"
private noncomputable def vp00000100111_1 : Blocks := edgeBlocks% "full/vectors/00000100111-V-0001.bin"
private noncomputable def vp00000100111_2 : Blocks := edgeBlocks% "full/vectors/00000100111-V-0002.bin"
noncomputable def vp00000100111 : Blocks := (Blocks.join vp00000100111_0 (Blocks.join vp00000100111_1 vp00000100111_2))
private theorem bp000001001110 : Branch 0 (-155761639/4000000 : ℚ) vp00000100111 := by
  apply branch_left_normalized (c:=vp000001001110) (k:=0) (m:=176) (by decide +kernel)
  rw [show 2*(-155761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-155761639/2000000 : ℚ) by norm_num]
  exact coverp000001001110
private noncomputable def ep000001001111_0 : Blocks := edgeBlocks% "full/vectors/000001001111-E-0000.bin"
private noncomputable def ep000001001111_1 : Blocks := edgeBlocks% "full/vectors/000001001111-E-0001.bin"
private noncomputable def ep000001001111_2 : Blocks := edgeBlocks% "full/vectors/000001001111-E-0002.bin"
noncomputable def ep000001001111 : Blocks := (Blocks.join ep000001001111_0 (Blocks.join ep000001001111_1 ep000001001111_2))
private theorem idp000001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100111.list =
    C ((2:ℤ)^341) * horner X vp000001001111.list + horner X ep000001001111.list := by
  exact edge_identity (B := (2:ℤ)^598) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001111 : Branch 1 (-155761639/4000000 : ℚ) vp00000100111 := by
  apply branch_checked idp000001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-155761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-157761639/2000000 : ℚ) by norm_num]
  exact coverp000001001111
theorem coverp00000100111 : Covers (-155761639/4000000 : ℚ) vp00000100111 := join_branches bp000001001110 bp000001001111
private noncomputable def vp000001001101111_0 : Blocks := edgeBlocks% "full/vectors/000001001101111-V-0000.bin"
noncomputable def vp000001001101111 : Blocks := vp000001001101111_0
theorem coverp000001001101111 : Covers (-155511639/250000 : ℚ) vp000001001101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001101110_0 : Blocks := edgeBlocks% "full/vectors/000001001101110-V-0000.bin"
noncomputable def vp000001001101110 : Blocks := vp000001001101110_0
theorem coverp000001001101110 : Covers (-155261639/250000 : ℚ) vp000001001101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100110111_0 : Blocks := edgeBlocks% "full/vectors/00000100110111-V-0000.bin"
noncomputable def vp00000100110111 : Blocks := vp00000100110111_0
private theorem bp000001001101110 : Branch 0 (-155261639/500000 : ℚ) vp00000100110111 := by
  apply branch_left_normalized (c:=vp000001001101110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-155261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-155261639/250000 : ℚ) by norm_num]
  exact coverp000001001101110
private noncomputable def ep000001001101111_0 : Blocks := edgeBlocks% "full/vectors/000001001101111-E-0000.bin"
noncomputable def ep000001001101111 : Blocks := ep000001001101111_0
private theorem idp000001001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100110111.list =
    C ((2:ℤ)^60) * horner X vp000001001101111.list + horner X ep000001001101111.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001101111 : Branch 1 (-155261639/500000 : ℚ) vp00000100110111 := by
  apply branch_checked idp000001001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-155261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-155511639/250000 : ℚ) by norm_num]
  exact coverp000001001101111
theorem coverp00000100110111 : Covers (-155261639/500000 : ℚ) vp00000100110111 := join_branches bp000001001101110 bp000001001101111
private noncomputable def vp000001001101101_0 : Blocks := edgeBlocks% "full/vectors/000001001101101-V-0000.bin"
noncomputable def vp000001001101101 : Blocks := vp000001001101101_0
theorem coverp000001001101101 : Covers (-155011639/250000 : ℚ) vp000001001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001101100_0 : Blocks := edgeBlocks% "full/vectors/000001001101100-V-0000.bin"
noncomputable def vp000001001101100 : Blocks := vp000001001101100_0
theorem coverp000001001101100 : Covers (-154761639/250000 : ℚ) vp000001001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100110110_0 : Blocks := edgeBlocks% "full/vectors/00000100110110-V-0000.bin"
noncomputable def vp00000100110110 : Blocks := vp00000100110110_0
private theorem bp000001001101100 : Branch 0 (-154761639/500000 : ℚ) vp00000100110110 := by
  apply branch_left_normalized (c:=vp000001001101100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-154761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-154761639/250000 : ℚ) by norm_num]
  exact coverp000001001101100
private noncomputable def ep000001001101101_0 : Blocks := edgeBlocks% "full/vectors/000001001101101-E-0000.bin"
noncomputable def ep000001001101101 : Blocks := ep000001001101101_0
private theorem idp000001001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100110110.list =
    C ((2:ℤ)^60) * horner X vp000001001101101.list + horner X ep000001001101101.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001101101 : Branch 1 (-154761639/500000 : ℚ) vp00000100110110 := by
  apply branch_checked idp000001001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-154761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-155011639/250000 : ℚ) by norm_num]
  exact coverp000001001101101
theorem coverp00000100110110 : Covers (-154761639/500000 : ℚ) vp00000100110110 := join_branches bp000001001101100 bp000001001101101
private noncomputable def vp0000010011011_0 : Blocks := edgeBlocks% "full/vectors/0000010011011-V-0000.bin"
noncomputable def vp0000010011011 : Blocks := vp0000010011011_0
private theorem bp00000100110110 : Branch 0 (-154761639/1000000 : ℚ) vp0000010011011 := by
  apply branch_left_normalized (c:=vp00000100110110) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-154761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-154761639/500000 : ℚ) by norm_num]
  exact coverp00000100110110
private noncomputable def ep00000100110111_0 : Blocks := edgeBlocks% "full/vectors/00000100110111-E-0000.bin"
noncomputable def ep00000100110111 : Blocks := ep00000100110111_0
private theorem idp00000100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010011011.list =
    C ((2:ℤ)^103) * horner X vp00000100110111.list + horner X ep00000100110111.list := by
  exact edge_identity (B := (2:ℤ)^239) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100110111 : Branch 1 (-154761639/1000000 : ℚ) vp0000010011011 := by
  apply branch_checked idp00000100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-154761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-155261639/500000 : ℚ) by norm_num]
  exact coverp00000100110111
theorem coverp0000010011011 : Covers (-154761639/1000000 : ℚ) vp0000010011011 := join_branches bp00000100110110 bp00000100110111
private noncomputable def vp000001001101011_0 : Blocks := edgeBlocks% "full/vectors/000001001101011-V-0000.bin"
noncomputable def vp000001001101011 : Blocks := vp000001001101011_0
theorem coverp000001001101011 : Covers (-154511639/250000 : ℚ) vp000001001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001101010_0 : Blocks := edgeBlocks% "full/vectors/000001001101010-V-0000.bin"
noncomputable def vp000001001101010 : Blocks := vp000001001101010_0
theorem coverp000001001101010 : Covers (-154261639/250000 : ℚ) vp000001001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100110101_0 : Blocks := edgeBlocks% "full/vectors/00000100110101-V-0000.bin"
noncomputable def vp00000100110101 : Blocks := vp00000100110101_0
private theorem bp000001001101010 : Branch 0 (-154261639/500000 : ℚ) vp00000100110101 := by
  apply branch_left_normalized (c:=vp000001001101010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-154261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-154261639/250000 : ℚ) by norm_num]
  exact coverp000001001101010
private noncomputable def ep000001001101011_0 : Blocks := edgeBlocks% "full/vectors/000001001101011-E-0000.bin"
noncomputable def ep000001001101011 : Blocks := ep000001001101011_0
private theorem idp000001001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100110101.list =
    C ((2:ℤ)^61) * horner X vp000001001101011.list + horner X ep000001001101011.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001101011 : Branch 1 (-154261639/500000 : ℚ) vp00000100110101 := by
  apply branch_checked idp000001001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-154261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-154511639/250000 : ℚ) by norm_num]
  exact coverp000001001101011
theorem coverp00000100110101 : Covers (-154261639/500000 : ℚ) vp00000100110101 := join_branches bp000001001101010 bp000001001101011
private noncomputable def vp000001001101001_0 : Blocks := edgeBlocks% "full/vectors/000001001101001-V-0000.bin"
noncomputable def vp000001001101001 : Blocks := vp000001001101001_0
theorem coverp000001001101001 : Covers (-154011639/250000 : ℚ) vp000001001101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001101000_0 : Blocks := edgeBlocks% "full/vectors/000001001101000-V-0000.bin"
noncomputable def vp000001001101000 : Blocks := vp000001001101000_0
theorem coverp000001001101000 : Covers (-153761639/250000 : ℚ) vp000001001101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100110100_0 : Blocks := edgeBlocks% "full/vectors/00000100110100-V-0000.bin"
noncomputable def vp00000100110100 : Blocks := vp00000100110100_0
private theorem bp000001001101000 : Branch 0 (-153761639/500000 : ℚ) vp00000100110100 := by
  apply branch_left_normalized (c:=vp000001001101000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-153761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-153761639/250000 : ℚ) by norm_num]
  exact coverp000001001101000
private noncomputable def ep000001001101001_0 : Blocks := edgeBlocks% "full/vectors/000001001101001-E-0000.bin"
noncomputable def ep000001001101001 : Blocks := ep000001001101001_0
private theorem idp000001001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100110100.list =
    C ((2:ℤ)^64) * horner X vp000001001101001.list + horner X ep000001001101001.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001101001 : Branch 1 (-153761639/500000 : ℚ) vp00000100110100 := by
  apply branch_checked idp000001001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-153761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-154011639/250000 : ℚ) by norm_num]
  exact coverp000001001101001
theorem coverp00000100110100 : Covers (-153761639/500000 : ℚ) vp00000100110100 := join_branches bp000001001101000 bp000001001101001
private noncomputable def vp0000010011010_0 : Blocks := edgeBlocks% "full/vectors/0000010011010-V-0000.bin"
noncomputable def vp0000010011010 : Blocks := vp0000010011010_0
private theorem bp00000100110100 : Branch 0 (-153761639/1000000 : ℚ) vp0000010011010 := by
  apply branch_left_normalized (c:=vp00000100110100) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-153761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-153761639/500000 : ℚ) by norm_num]
  exact coverp00000100110100
private noncomputable def ep00000100110101_0 : Blocks := edgeBlocks% "full/vectors/00000100110101-E-0000.bin"
noncomputable def ep00000100110101 : Blocks := ep00000100110101_0
private theorem idp00000100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010011010.list =
    C ((2:ℤ)^108) * horner X vp00000100110101.list + horner X ep00000100110101.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100110101 : Branch 1 (-153761639/1000000 : ℚ) vp0000010011010 := by
  apply branch_checked idp00000100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-153761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-154261639/500000 : ℚ) by norm_num]
  exact coverp00000100110101
theorem coverp0000010011010 : Covers (-153761639/1000000 : ℚ) vp0000010011010 := join_branches bp00000100110100 bp00000100110101
private noncomputable def vp000001001101_0 : Blocks := edgeBlocks% "full/vectors/000001001101-V-0000.bin"
private noncomputable def vp000001001101_1 : Blocks := edgeBlocks% "full/vectors/000001001101-V-0001.bin"
noncomputable def vp000001001101 : Blocks := (Blocks.join vp000001001101_0 vp000001001101_1)
private theorem bp0000010011010 : Branch 0 (-153761639/2000000 : ℚ) vp000001001101 := by
  apply branch_left_normalized (c:=vp0000010011010) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-153761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-153761639/1000000 : ℚ) by norm_num]
  exact coverp0000010011010
private noncomputable def ep0000010011011_0 : Blocks := edgeBlocks% "full/vectors/0000010011011-E-0000.bin"
private noncomputable def ep0000010011011_1 : Blocks := edgeBlocks% "full/vectors/0000010011011-E-0001.bin"
noncomputable def ep0000010011011 : Blocks := (Blocks.join ep0000010011011_0 ep0000010011011_1)
private theorem idp0000010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001001101.list =
    C ((2:ℤ)^192) * horner X vp0000010011011.list + horner X ep0000010011011.list := by
  exact edge_identity (B := (2:ℤ)^368) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010011011 : Branch 1 (-153761639/2000000 : ℚ) vp000001001101 := by
  apply branch_checked idp0000010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-153761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-154761639/1000000 : ℚ) by norm_num]
  exact coverp0000010011011
theorem coverp000001001101 : Covers (-153761639/2000000 : ℚ) vp000001001101 := join_branches bp0000010011010 bp0000010011011
private noncomputable def vp000001001100111_0 : Blocks := edgeBlocks% "full/vectors/000001001100111-V-0000.bin"
noncomputable def vp000001001100111 : Blocks := vp000001001100111_0
theorem coverp000001001100111 : Covers (-153511639/250000 : ℚ) vp000001001100111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001100110_0 : Blocks := edgeBlocks% "full/vectors/000001001100110-V-0000.bin"
noncomputable def vp000001001100110 : Blocks := vp000001001100110_0
theorem coverp000001001100110 : Covers (-153261639/250000 : ℚ) vp000001001100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100110011_0 : Blocks := edgeBlocks% "full/vectors/00000100110011-V-0000.bin"
noncomputable def vp00000100110011 : Blocks := vp00000100110011_0
private theorem bp000001001100110 : Branch 0 (-153261639/500000 : ℚ) vp00000100110011 := by
  apply branch_left_normalized (c:=vp000001001100110) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-153261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-153261639/250000 : ℚ) by norm_num]
  exact coverp000001001100110
private noncomputable def ep000001001100111_0 : Blocks := edgeBlocks% "full/vectors/000001001100111-E-0000.bin"
noncomputable def ep000001001100111 : Blocks := ep000001001100111_0
private theorem idp000001001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100110011.list =
    C ((2:ℤ)^60) * horner X vp000001001100111.list + horner X ep000001001100111.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001100111 : Branch 1 (-153261639/500000 : ℚ) vp00000100110011 := by
  apply branch_checked idp000001001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-153261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-153511639/250000 : ℚ) by norm_num]
  exact coverp000001001100111
theorem coverp00000100110011 : Covers (-153261639/500000 : ℚ) vp00000100110011 := join_branches bp000001001100110 bp000001001100111
private noncomputable def vp000001001100101_0 : Blocks := edgeBlocks% "full/vectors/000001001100101-V-0000.bin"
noncomputable def vp000001001100101 : Blocks := vp000001001100101_0
theorem coverp000001001100101 : Covers (-153011639/250000 : ℚ) vp000001001100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001100100_0 : Blocks := edgeBlocks% "full/vectors/000001001100100-V-0000.bin"
noncomputable def vp000001001100100 : Blocks := vp000001001100100_0
theorem coverp000001001100100 : Covers (-152761639/250000 : ℚ) vp000001001100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100110010_0 : Blocks := edgeBlocks% "full/vectors/00000100110010-V-0000.bin"
noncomputable def vp00000100110010 : Blocks := vp00000100110010_0
private theorem bp000001001100100 : Branch 0 (-152761639/500000 : ℚ) vp00000100110010 := by
  apply branch_left_normalized (c:=vp000001001100100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-152761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-152761639/250000 : ℚ) by norm_num]
  exact coverp000001001100100
private noncomputable def ep000001001100101_0 : Blocks := edgeBlocks% "full/vectors/000001001100101-E-0000.bin"
noncomputable def ep000001001100101 : Blocks := ep000001001100101_0
private theorem idp000001001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100110010.list =
    C ((2:ℤ)^60) * horner X vp000001001100101.list + horner X ep000001001100101.list := by
  exact edge_identity (B := (2:ℤ)^180) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001100101 : Branch 1 (-152761639/500000 : ℚ) vp00000100110010 := by
  apply branch_checked idp000001001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-152761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-153011639/250000 : ℚ) by norm_num]
  exact coverp000001001100101
theorem coverp00000100110010 : Covers (-152761639/500000 : ℚ) vp00000100110010 := join_branches bp000001001100100 bp000001001100101
private noncomputable def vp0000010011001_0 : Blocks := edgeBlocks% "full/vectors/0000010011001-V-0000.bin"
noncomputable def vp0000010011001 : Blocks := vp0000010011001_0
private theorem bp00000100110010 : Branch 0 (-152761639/1000000 : ℚ) vp0000010011001 := by
  apply branch_left_normalized (c:=vp00000100110010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-152761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-152761639/500000 : ℚ) by norm_num]
  exact coverp00000100110010
private noncomputable def ep00000100110011_0 : Blocks := edgeBlocks% "full/vectors/00000100110011-E-0000.bin"
noncomputable def ep00000100110011 : Blocks := ep00000100110011_0
private theorem idp00000100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010011001.list =
    C ((2:ℤ)^101) * horner X vp00000100110011.list + horner X ep00000100110011.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100110011 : Branch 1 (-152761639/1000000 : ℚ) vp0000010011001 := by
  apply branch_checked idp00000100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-152761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-153261639/500000 : ℚ) by norm_num]
  exact coverp00000100110011
theorem coverp0000010011001 : Covers (-152761639/1000000 : ℚ) vp0000010011001 := join_branches bp00000100110010 bp00000100110011
private noncomputable def vp000001001100011_0 : Blocks := edgeBlocks% "full/vectors/000001001100011-V-0000.bin"
noncomputable def vp000001001100011 : Blocks := vp000001001100011_0
theorem coverp000001001100011 : Covers (-152511639/250000 : ℚ) vp000001001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001100010_0 : Blocks := edgeBlocks% "full/vectors/000001001100010-V-0000.bin"
noncomputable def vp000001001100010 : Blocks := vp000001001100010_0
theorem coverp000001001100010 : Covers (-152261639/250000 : ℚ) vp000001001100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100110001_0 : Blocks := edgeBlocks% "full/vectors/00000100110001-V-0000.bin"
noncomputable def vp00000100110001 : Blocks := vp00000100110001_0
private theorem bp000001001100010 : Branch 0 (-152261639/500000 : ℚ) vp00000100110001 := by
  apply branch_left_normalized (c:=vp000001001100010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-152261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-152261639/250000 : ℚ) by norm_num]
  exact coverp000001001100010
private noncomputable def ep000001001100011_0 : Blocks := edgeBlocks% "full/vectors/000001001100011-E-0000.bin"
noncomputable def ep000001001100011 : Blocks := ep000001001100011_0
private theorem idp000001001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100110001.list =
    C ((2:ℤ)^62) * horner X vp000001001100011.list + horner X ep000001001100011.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001100011 : Branch 1 (-152261639/500000 : ℚ) vp00000100110001 := by
  apply branch_checked idp000001001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-152261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-152511639/250000 : ℚ) by norm_num]
  exact coverp000001001100011
theorem coverp00000100110001 : Covers (-152261639/500000 : ℚ) vp00000100110001 := join_branches bp000001001100010 bp000001001100011
private noncomputable def vp000001001100001_0 : Blocks := edgeBlocks% "full/vectors/000001001100001-V-0000.bin"
noncomputable def vp000001001100001 : Blocks := vp000001001100001_0
theorem coverp000001001100001 : Covers (-152011639/250000 : ℚ) vp000001001100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001100000_0 : Blocks := edgeBlocks% "full/vectors/000001001100000-V-0000.bin"
noncomputable def vp000001001100000 : Blocks := vp000001001100000_0
theorem coverp000001001100000 : Covers (-151761639/250000 : ℚ) vp000001001100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100110000_0 : Blocks := edgeBlocks% "full/vectors/00000100110000-V-0000.bin"
noncomputable def vp00000100110000 : Blocks := vp00000100110000_0
private theorem bp000001001100000 : Branch 0 (-151761639/500000 : ℚ) vp00000100110000 := by
  apply branch_left_normalized (c:=vp000001001100000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-151761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-151761639/250000 : ℚ) by norm_num]
  exact coverp000001001100000
private noncomputable def ep000001001100001_0 : Blocks := edgeBlocks% "full/vectors/000001001100001-E-0000.bin"
noncomputable def ep000001001100001 : Blocks := ep000001001100001_0
private theorem idp000001001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100110000.list =
    C ((2:ℤ)^62) * horner X vp000001001100001.list + horner X ep000001001100001.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001100001 : Branch 1 (-151761639/500000 : ℚ) vp00000100110000 := by
  apply branch_checked idp000001001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-151761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-152011639/250000 : ℚ) by norm_num]
  exact coverp000001001100001
theorem coverp00000100110000 : Covers (-151761639/500000 : ℚ) vp00000100110000 := join_branches bp000001001100000 bp000001001100001
private noncomputable def vp0000010011000_0 : Blocks := edgeBlocks% "full/vectors/0000010011000-V-0000.bin"
noncomputable def vp0000010011000 : Blocks := vp0000010011000_0
private theorem bp00000100110000 : Branch 0 (-151761639/1000000 : ℚ) vp0000010011000 := by
  apply branch_left_normalized (c:=vp00000100110000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-151761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-151761639/500000 : ℚ) by norm_num]
  exact coverp00000100110000
private noncomputable def ep00000100110001_0 : Blocks := edgeBlocks% "full/vectors/00000100110001-E-0000.bin"
noncomputable def ep00000100110001 : Blocks := ep00000100110001_0
private theorem idp00000100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010011000.list =
    C ((2:ℤ)^104) * horner X vp00000100110001.list + horner X ep00000100110001.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100110001 : Branch 1 (-151761639/1000000 : ℚ) vp0000010011000 := by
  apply branch_checked idp00000100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-151761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-152261639/500000 : ℚ) by norm_num]
  exact coverp00000100110001
theorem coverp0000010011000 : Covers (-151761639/1000000 : ℚ) vp0000010011000 := join_branches bp00000100110000 bp00000100110001
private noncomputable def vp000001001100_0 : Blocks := edgeBlocks% "full/vectors/000001001100-V-0000.bin"
private noncomputable def vp000001001100_1 : Blocks := edgeBlocks% "full/vectors/000001001100-V-0001.bin"
noncomputable def vp000001001100 : Blocks := (Blocks.join vp000001001100_0 vp000001001100_1)
private theorem bp0000010011000 : Branch 0 (-151761639/2000000 : ℚ) vp000001001100 := by
  apply branch_left_normalized (c:=vp0000010011000) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-151761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-151761639/1000000 : ℚ) by norm_num]
  exact coverp0000010011000
private noncomputable def ep0000010011001_0 : Blocks := edgeBlocks% "full/vectors/0000010011001-E-0000.bin"
private noncomputable def ep0000010011001_1 : Blocks := edgeBlocks% "full/vectors/0000010011001-E-0001.bin"
noncomputable def ep0000010011001 : Blocks := (Blocks.join ep0000010011001_0 ep0000010011001_1)
private theorem idp0000010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001001100.list =
    C ((2:ℤ)^187) * horner X vp0000010011001.list + horner X ep0000010011001.list := by
  exact edge_identity (B := (2:ℤ)^365) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010011001 : Branch 1 (-151761639/2000000 : ℚ) vp000001001100 := by
  apply branch_checked idp0000010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-151761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-152761639/1000000 : ℚ) by norm_num]
  exact coverp0000010011001
theorem coverp000001001100 : Covers (-151761639/2000000 : ℚ) vp000001001100 := join_branches bp0000010011000 bp0000010011001
private noncomputable def vp00000100110_0 : Blocks := edgeBlocks% "full/vectors/00000100110-V-0000.bin"
private noncomputable def vp00000100110_1 : Blocks := edgeBlocks% "full/vectors/00000100110-V-0001.bin"
private noncomputable def vp00000100110_2 : Blocks := edgeBlocks% "full/vectors/00000100110-V-0002.bin"
noncomputable def vp00000100110 : Blocks := (Blocks.join vp00000100110_0 (Blocks.join vp00000100110_1 vp00000100110_2))
private theorem bp000001001100 : Branch 0 (-151761639/4000000 : ℚ) vp00000100110 := by
  apply branch_left_normalized (c:=vp000001001100) (k:=0) (m:=180) (by decide +kernel)
  rw [show 2*(-151761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-151761639/2000000 : ℚ) by norm_num]
  exact coverp000001001100
private noncomputable def ep000001001101_0 : Blocks := edgeBlocks% "full/vectors/000001001101-E-0000.bin"
private noncomputable def ep000001001101_1 : Blocks := edgeBlocks% "full/vectors/000001001101-E-0001.bin"
private noncomputable def ep000001001101_2 : Blocks := edgeBlocks% "full/vectors/000001001101-E-0002.bin"
noncomputable def ep000001001101 : Blocks := (Blocks.join ep000001001101_0 (Blocks.join ep000001001101_1 ep000001001101_2))
private theorem idp000001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100110.list =
    C ((2:ℤ)^349) * horner X vp000001001101.list + horner X ep000001001101.list := by
  exact edge_identity (B := (2:ℤ)^609) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001101 : Branch 1 (-151761639/4000000 : ℚ) vp00000100110 := by
  apply branch_checked idp000001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-151761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-153761639/2000000 : ℚ) by norm_num]
  exact coverp000001001101
theorem coverp00000100110 : Covers (-151761639/4000000 : ℚ) vp00000100110 := join_branches bp000001001100 bp000001001101
private noncomputable def vp0000010011_0 : Blocks := edgeBlocks% "full/vectors/0000010011-V-0000.bin"
private noncomputable def vp0000010011_1 : Blocks := edgeBlocks% "full/vectors/0000010011-V-0001.bin"
private noncomputable def vp0000010011_2 : Blocks := edgeBlocks% "full/vectors/0000010011-V-0002.bin"
private noncomputable def vp0000010011_3 : Blocks := edgeBlocks% "full/vectors/0000010011-V-0003.bin"
private noncomputable def vp0000010011_4 : Blocks := edgeBlocks% "full/vectors/0000010011-V-0004.bin"
private noncomputable def vp0000010011_5 : Blocks := edgeBlocks% "full/vectors/0000010011-V-0005.bin"
noncomputable def vp0000010011 : Blocks := (Blocks.join (Blocks.join vp0000010011_0 (Blocks.join vp0000010011_1 vp0000010011_2)) (Blocks.join vp0000010011_3 (Blocks.join vp0000010011_4 vp0000010011_5)))
private theorem bp00000100110 : Branch 0 (-151761639/8000000 : ℚ) vp0000010011 := by
  apply branch_left_normalized (c:=vp00000100110) (k:=0) (m:=339) (by decide +kernel)
  rw [show 2*(-151761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-151761639/4000000 : ℚ) by norm_num]
  exact coverp00000100110
private noncomputable def ep00000100111_0 : Blocks := edgeBlocks% "full/vectors/00000100111-E-0000.bin"
private noncomputable def ep00000100111_1 : Blocks := edgeBlocks% "full/vectors/00000100111-E-0001.bin"
private noncomputable def ep00000100111_2 : Blocks := edgeBlocks% "full/vectors/00000100111-E-0002.bin"
private noncomputable def ep00000100111_3 : Blocks := edgeBlocks% "full/vectors/00000100111-E-0003.bin"
private noncomputable def ep00000100111_4 : Blocks := edgeBlocks% "full/vectors/00000100111-E-0004.bin"
private noncomputable def ep00000100111_5 : Blocks := edgeBlocks% "full/vectors/00000100111-E-0005.bin"
noncomputable def ep00000100111 : Blocks := (Blocks.join (Blocks.join ep00000100111_0 (Blocks.join ep00000100111_1 ep00000100111_2)) (Blocks.join ep00000100111_3 (Blocks.join ep00000100111_4 ep00000100111_5)))
private theorem idp00000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010011.list =
    C ((2:ℤ)^680) * horner X vp00000100111.list + horner X ep00000100111.list := by
  exact edge_identity (B := (2:ℤ)^1092) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100111 : Branch 1 (-151761639/8000000 : ℚ) vp0000010011 := by
  apply branch_checked idp00000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-151761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-155761639/4000000 : ℚ) by norm_num]
  exact coverp00000100111
theorem coverp0000010011 : Covers (-151761639/8000000 : ℚ) vp0000010011 := join_branches bp00000100110 bp00000100111
private noncomputable def vp000001001011111_0 : Blocks := edgeBlocks% "full/vectors/000001001011111-V-0000.bin"
noncomputable def vp000001001011111 : Blocks := vp000001001011111_0
theorem coverp000001001011111 : Covers (-151511639/250000 : ℚ) vp000001001011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001011110_0 : Blocks := edgeBlocks% "full/vectors/000001001011110-V-0000.bin"
noncomputable def vp000001001011110 : Blocks := vp000001001011110_0
theorem coverp000001001011110 : Covers (-151261639/250000 : ℚ) vp000001001011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100101111_0 : Blocks := edgeBlocks% "full/vectors/00000100101111-V-0000.bin"
noncomputable def vp00000100101111 : Blocks := vp00000100101111_0
private theorem bp000001001011110 : Branch 0 (-151261639/500000 : ℚ) vp00000100101111 := by
  apply branch_left_normalized (c:=vp000001001011110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-151261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-151261639/250000 : ℚ) by norm_num]
  exact coverp000001001011110
private noncomputable def ep000001001011111_0 : Blocks := edgeBlocks% "full/vectors/000001001011111-E-0000.bin"
noncomputable def ep000001001011111 : Blocks := ep000001001011111_0
private theorem idp000001001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100101111.list =
    C ((2:ℤ)^62) * horner X vp000001001011111.list + horner X ep000001001011111.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001011111 : Branch 1 (-151261639/500000 : ℚ) vp00000100101111 := by
  apply branch_checked idp000001001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-151261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-151511639/250000 : ℚ) by norm_num]
  exact coverp000001001011111
theorem coverp00000100101111 : Covers (-151261639/500000 : ℚ) vp00000100101111 := join_branches bp000001001011110 bp000001001011111
private noncomputable def vp000001001011101_0 : Blocks := edgeBlocks% "full/vectors/000001001011101-V-0000.bin"
noncomputable def vp000001001011101 : Blocks := vp000001001011101_0
theorem coverp000001001011101 : Covers (-151011639/250000 : ℚ) vp000001001011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001011100_0 : Blocks := edgeBlocks% "full/vectors/000001001011100-V-0000.bin"
noncomputable def vp000001001011100 : Blocks := vp000001001011100_0
theorem coverp000001001011100 : Covers (-150761639/250000 : ℚ) vp000001001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100101110_0 : Blocks := edgeBlocks% "full/vectors/00000100101110-V-0000.bin"
noncomputable def vp00000100101110 : Blocks := vp00000100101110_0
private theorem bp000001001011100 : Branch 0 (-150761639/500000 : ℚ) vp00000100101110 := by
  apply branch_left_normalized (c:=vp000001001011100) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-150761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-150761639/250000 : ℚ) by norm_num]
  exact coverp000001001011100
private noncomputable def ep000001001011101_0 : Blocks := edgeBlocks% "full/vectors/000001001011101-E-0000.bin"
noncomputable def ep000001001011101 : Blocks := ep000001001011101_0
private theorem idp000001001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100101110.list =
    C ((2:ℤ)^62) * horner X vp000001001011101.list + horner X ep000001001011101.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001011101 : Branch 1 (-150761639/500000 : ℚ) vp00000100101110 := by
  apply branch_checked idp000001001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-150761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-151011639/250000 : ℚ) by norm_num]
  exact coverp000001001011101
theorem coverp00000100101110 : Covers (-150761639/500000 : ℚ) vp00000100101110 := join_branches bp000001001011100 bp000001001011101
private noncomputable def vp0000010010111_0 : Blocks := edgeBlocks% "full/vectors/0000010010111-V-0000.bin"
noncomputable def vp0000010010111 : Blocks := vp0000010010111_0
private theorem bp00000100101110 : Branch 0 (-150761639/1000000 : ℚ) vp0000010010111 := by
  apply branch_left_normalized (c:=vp00000100101110) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-150761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-150761639/500000 : ℚ) by norm_num]
  exact coverp00000100101110
private noncomputable def ep00000100101111_0 : Blocks := edgeBlocks% "full/vectors/00000100101111-E-0000.bin"
noncomputable def ep00000100101111 : Blocks := ep00000100101111_0
private theorem idp00000100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010010111.list =
    C ((2:ℤ)^107) * horner X vp00000100101111.list + horner X ep00000100101111.list := by
  exact edge_identity (B := (2:ℤ)^248) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100101111 : Branch 1 (-150761639/1000000 : ℚ) vp0000010010111 := by
  apply branch_checked idp00000100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-150761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-151261639/500000 : ℚ) by norm_num]
  exact coverp00000100101111
theorem coverp0000010010111 : Covers (-150761639/1000000 : ℚ) vp0000010010111 := join_branches bp00000100101110 bp00000100101111
private noncomputable def vp000001001011011_0 : Blocks := edgeBlocks% "full/vectors/000001001011011-V-0000.bin"
noncomputable def vp000001001011011 : Blocks := vp000001001011011_0
theorem coverp000001001011011 : Covers (-150511639/250000 : ℚ) vp000001001011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001011010_0 : Blocks := edgeBlocks% "full/vectors/000001001011010-V-0000.bin"
noncomputable def vp000001001011010 : Blocks := vp000001001011010_0
theorem coverp000001001011010 : Covers (-150261639/250000 : ℚ) vp000001001011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100101101_0 : Blocks := edgeBlocks% "full/vectors/00000100101101-V-0000.bin"
noncomputable def vp00000100101101 : Blocks := vp00000100101101_0
private theorem bp000001001011010 : Branch 0 (-150261639/500000 : ℚ) vp00000100101101 := by
  apply branch_left_normalized (c:=vp000001001011010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-150261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-150261639/250000 : ℚ) by norm_num]
  exact coverp000001001011010
private noncomputable def ep000001001011011_0 : Blocks := edgeBlocks% "full/vectors/000001001011011-E-0000.bin"
noncomputable def ep000001001011011 : Blocks := ep000001001011011_0
private theorem idp000001001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100101101.list =
    C ((2:ℤ)^63) * horner X vp000001001011011.list + horner X ep000001001011011.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001011011 : Branch 1 (-150261639/500000 : ℚ) vp00000100101101 := by
  apply branch_checked idp000001001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-150261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-150511639/250000 : ℚ) by norm_num]
  exact coverp000001001011011
theorem coverp00000100101101 : Covers (-150261639/500000 : ℚ) vp00000100101101 := join_branches bp000001001011010 bp000001001011011
private noncomputable def vp000001001011001_0 : Blocks := edgeBlocks% "full/vectors/000001001011001-V-0000.bin"
noncomputable def vp000001001011001 : Blocks := vp000001001011001_0
theorem coverp000001001011001 : Covers (-150011639/250000 : ℚ) vp000001001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001011000_0 : Blocks := edgeBlocks% "full/vectors/000001001011000-V-0000.bin"
noncomputable def vp000001001011000 : Blocks := vp000001001011000_0
theorem coverp000001001011000 : Covers (-149761639/250000 : ℚ) vp000001001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100101100_0 : Blocks := edgeBlocks% "full/vectors/00000100101100-V-0000.bin"
noncomputable def vp00000100101100 : Blocks := vp00000100101100_0
private theorem bp000001001011000 : Branch 0 (-149761639/500000 : ℚ) vp00000100101100 := by
  apply branch_left_normalized (c:=vp000001001011000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-149761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-149761639/250000 : ℚ) by norm_num]
  exact coverp000001001011000
private noncomputable def ep000001001011001_0 : Blocks := edgeBlocks% "full/vectors/000001001011001-E-0000.bin"
noncomputable def ep000001001011001 : Blocks := ep000001001011001_0
private theorem idp000001001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100101100.list =
    C ((2:ℤ)^62) * horner X vp000001001011001.list + horner X ep000001001011001.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001011001 : Branch 1 (-149761639/500000 : ℚ) vp00000100101100 := by
  apply branch_checked idp000001001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-149761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-150011639/250000 : ℚ) by norm_num]
  exact coverp000001001011001
theorem coverp00000100101100 : Covers (-149761639/500000 : ℚ) vp00000100101100 := join_branches bp000001001011000 bp000001001011001
private noncomputable def vp0000010010110_0 : Blocks := edgeBlocks% "full/vectors/0000010010110-V-0000.bin"
noncomputable def vp0000010010110 : Blocks := vp0000010010110_0
private theorem bp00000100101100 : Branch 0 (-149761639/1000000 : ℚ) vp0000010010110 := by
  apply branch_left_normalized (c:=vp00000100101100) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-149761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-149761639/500000 : ℚ) by norm_num]
  exact coverp00000100101100
private noncomputable def ep00000100101101_0 : Blocks := edgeBlocks% "full/vectors/00000100101101-E-0000.bin"
noncomputable def ep00000100101101 : Blocks := ep00000100101101_0
private theorem idp00000100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010010110.list =
    C ((2:ℤ)^104) * horner X vp00000100101101.list + horner X ep00000100101101.list := by
  exact edge_identity (B := (2:ℤ)^247) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100101101 : Branch 1 (-149761639/1000000 : ℚ) vp0000010010110 := by
  apply branch_checked idp00000100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-149761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-150261639/500000 : ℚ) by norm_num]
  exact coverp00000100101101
theorem coverp0000010010110 : Covers (-149761639/1000000 : ℚ) vp0000010010110 := join_branches bp00000100101100 bp00000100101101
private noncomputable def vp000001001011_0 : Blocks := edgeBlocks% "full/vectors/000001001011-V-0000.bin"
private noncomputable def vp000001001011_1 : Blocks := edgeBlocks% "full/vectors/000001001011-V-0001.bin"
noncomputable def vp000001001011 : Blocks := (Blocks.join vp000001001011_0 vp000001001011_1)
private theorem bp0000010010110 : Branch 0 (-149761639/2000000 : ℚ) vp000001001011 := by
  apply branch_left_normalized (c:=vp0000010010110) (k:=0) (m:=101) (by decide +kernel)
  rw [show 2*(-149761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-149761639/1000000 : ℚ) by norm_num]
  exact coverp0000010010110
private noncomputable def ep0000010010111_0 : Blocks := edgeBlocks% "full/vectors/0000010010111-E-0000.bin"
private noncomputable def ep0000010010111_1 : Blocks := edgeBlocks% "full/vectors/0000010010111-E-0001.bin"
noncomputable def ep0000010010111 : Blocks := (Blocks.join ep0000010010111_0 ep0000010010111_1)
private theorem idp0000010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001001011.list =
    C ((2:ℤ)^190) * horner X vp0000010010111.list + horner X ep0000010010111.list := by
  exact edge_identity (B := (2:ℤ)^372) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010010111 : Branch 1 (-149761639/2000000 : ℚ) vp000001001011 := by
  apply branch_checked idp0000010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-149761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-150761639/1000000 : ℚ) by norm_num]
  exact coverp0000010010111
theorem coverp000001001011 : Covers (-149761639/2000000 : ℚ) vp000001001011 := join_branches bp0000010010110 bp0000010010111
private noncomputable def vp000001001010111_0 : Blocks := edgeBlocks% "full/vectors/000001001010111-V-0000.bin"
noncomputable def vp000001001010111 : Blocks := vp000001001010111_0
theorem coverp000001001010111 : Covers (-149511639/250000 : ℚ) vp000001001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001010110_0 : Blocks := edgeBlocks% "full/vectors/000001001010110-V-0000.bin"
noncomputable def vp000001001010110 : Blocks := vp000001001010110_0
theorem coverp000001001010110 : Covers (-149261639/250000 : ℚ) vp000001001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100101011_0 : Blocks := edgeBlocks% "full/vectors/00000100101011-V-0000.bin"
noncomputable def vp00000100101011 : Blocks := vp00000100101011_0
private theorem bp000001001010110 : Branch 0 (-149261639/500000 : ℚ) vp00000100101011 := by
  apply branch_left_normalized (c:=vp000001001010110) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-149261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-149261639/250000 : ℚ) by norm_num]
  exact coverp000001001010110
private noncomputable def ep000001001010111_0 : Blocks := edgeBlocks% "full/vectors/000001001010111-E-0000.bin"
noncomputable def ep000001001010111 : Blocks := ep000001001010111_0
private theorem idp000001001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100101011.list =
    C ((2:ℤ)^61) * horner X vp000001001010111.list + horner X ep000001001010111.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001010111 : Branch 1 (-149261639/500000 : ℚ) vp00000100101011 := by
  apply branch_checked idp000001001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-149261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-149511639/250000 : ℚ) by norm_num]
  exact coverp000001001010111
theorem coverp00000100101011 : Covers (-149261639/500000 : ℚ) vp00000100101011 := join_branches bp000001001010110 bp000001001010111
private noncomputable def vp000001001010101_0 : Blocks := edgeBlocks% "full/vectors/000001001010101-V-0000.bin"
noncomputable def vp000001001010101 : Blocks := vp000001001010101_0
theorem coverp000001001010101 : Covers (-149011639/250000 : ℚ) vp000001001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001010100_0 : Blocks := edgeBlocks% "full/vectors/000001001010100-V-0000.bin"
noncomputable def vp000001001010100 : Blocks := vp000001001010100_0
theorem coverp000001001010100 : Covers (-148761639/250000 : ℚ) vp000001001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100101010_0 : Blocks := edgeBlocks% "full/vectors/00000100101010-V-0000.bin"
noncomputable def vp00000100101010 : Blocks := vp00000100101010_0
private theorem bp000001001010100 : Branch 0 (-148761639/500000 : ℚ) vp00000100101010 := by
  apply branch_left_normalized (c:=vp000001001010100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-148761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-148761639/250000 : ℚ) by norm_num]
  exact coverp000001001010100
private noncomputable def ep000001001010101_0 : Blocks := edgeBlocks% "full/vectors/000001001010101-E-0000.bin"
noncomputable def ep000001001010101 : Blocks := ep000001001010101_0
private theorem idp000001001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100101010.list =
    C ((2:ℤ)^62) * horner X vp000001001010101.list + horner X ep000001001010101.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001010101 : Branch 1 (-148761639/500000 : ℚ) vp00000100101010 := by
  apply branch_checked idp000001001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-148761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-149011639/250000 : ℚ) by norm_num]
  exact coverp000001001010101
theorem coverp00000100101010 : Covers (-148761639/500000 : ℚ) vp00000100101010 := join_branches bp000001001010100 bp000001001010101
private noncomputable def vp0000010010101_0 : Blocks := edgeBlocks% "full/vectors/0000010010101-V-0000.bin"
noncomputable def vp0000010010101 : Blocks := vp0000010010101_0
private theorem bp00000100101010 : Branch 0 (-148761639/1000000 : ℚ) vp0000010010101 := by
  apply branch_left_normalized (c:=vp00000100101010) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-148761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-148761639/500000 : ℚ) by norm_num]
  exact coverp00000100101010
private noncomputable def ep00000100101011_0 : Blocks := edgeBlocks% "full/vectors/00000100101011-E-0000.bin"
noncomputable def ep00000100101011 : Blocks := ep00000100101011_0
private theorem idp00000100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010010101.list =
    C ((2:ℤ)^105) * horner X vp00000100101011.list + horner X ep00000100101011.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100101011 : Branch 1 (-148761639/1000000 : ℚ) vp0000010010101 := by
  apply branch_checked idp00000100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-148761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-149261639/500000 : ℚ) by norm_num]
  exact coverp00000100101011
theorem coverp0000010010101 : Covers (-148761639/1000000 : ℚ) vp0000010010101 := join_branches bp00000100101010 bp00000100101011
private noncomputable def vp000001001010011_0 : Blocks := edgeBlocks% "full/vectors/000001001010011-V-0000.bin"
noncomputable def vp000001001010011 : Blocks := vp000001001010011_0
theorem coverp000001001010011 : Covers (-148511639/250000 : ℚ) vp000001001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001010010_0 : Blocks := edgeBlocks% "full/vectors/000001001010010-V-0000.bin"
noncomputable def vp000001001010010 : Blocks := vp000001001010010_0
theorem coverp000001001010010 : Covers (-148261639/250000 : ℚ) vp000001001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100101001_0 : Blocks := edgeBlocks% "full/vectors/00000100101001-V-0000.bin"
noncomputable def vp00000100101001 : Blocks := vp00000100101001_0
private theorem bp000001001010010 : Branch 0 (-148261639/500000 : ℚ) vp00000100101001 := by
  apply branch_left_normalized (c:=vp000001001010010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-148261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-148261639/250000 : ℚ) by norm_num]
  exact coverp000001001010010
private noncomputable def ep000001001010011_0 : Blocks := edgeBlocks% "full/vectors/000001001010011-E-0000.bin"
noncomputable def ep000001001010011 : Blocks := ep000001001010011_0
private theorem idp000001001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100101001.list =
    C ((2:ℤ)^63) * horner X vp000001001010011.list + horner X ep000001001010011.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001010011 : Branch 1 (-148261639/500000 : ℚ) vp00000100101001 := by
  apply branch_checked idp000001001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-148261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-148511639/250000 : ℚ) by norm_num]
  exact coverp000001001010011
theorem coverp00000100101001 : Covers (-148261639/500000 : ℚ) vp00000100101001 := join_branches bp000001001010010 bp000001001010011
private noncomputable def vp000001001010001_0 : Blocks := edgeBlocks% "full/vectors/000001001010001-V-0000.bin"
noncomputable def vp000001001010001 : Blocks := vp000001001010001_0
theorem coverp000001001010001 : Covers (-148011639/250000 : ℚ) vp000001001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001010000_0 : Blocks := edgeBlocks% "full/vectors/000001001010000-V-0000.bin"
noncomputable def vp000001001010000 : Blocks := vp000001001010000_0
theorem coverp000001001010000 : Covers (-147761639/250000 : ℚ) vp000001001010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100101000_0 : Blocks := edgeBlocks% "full/vectors/00000100101000-V-0000.bin"
noncomputable def vp00000100101000 : Blocks := vp00000100101000_0
private theorem bp000001001010000 : Branch 0 (-147761639/500000 : ℚ) vp00000100101000 := by
  apply branch_left_normalized (c:=vp000001001010000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-147761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-147761639/250000 : ℚ) by norm_num]
  exact coverp000001001010000
private noncomputable def ep000001001010001_0 : Blocks := edgeBlocks% "full/vectors/000001001010001-E-0000.bin"
noncomputable def ep000001001010001 : Blocks := ep000001001010001_0
private theorem idp000001001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100101000.list =
    C ((2:ℤ)^63) * horner X vp000001001010001.list + horner X ep000001001010001.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001010001 : Branch 1 (-147761639/500000 : ℚ) vp00000100101000 := by
  apply branch_checked idp000001001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-147761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-148011639/250000 : ℚ) by norm_num]
  exact coverp000001001010001
theorem coverp00000100101000 : Covers (-147761639/500000 : ℚ) vp00000100101000 := join_branches bp000001001010000 bp000001001010001
private noncomputable def vp0000010010100_0 : Blocks := edgeBlocks% "full/vectors/0000010010100-V-0000.bin"
noncomputable def vp0000010010100 : Blocks := vp0000010010100_0
private theorem bp00000100101000 : Branch 0 (-147761639/1000000 : ℚ) vp0000010010100 := by
  apply branch_left_normalized (c:=vp00000100101000) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-147761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-147761639/500000 : ℚ) by norm_num]
  exact coverp00000100101000
private noncomputable def ep00000100101001_0 : Blocks := edgeBlocks% "full/vectors/00000100101001-E-0000.bin"
noncomputable def ep00000100101001 : Blocks := ep00000100101001_0
private theorem idp00000100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010010100.list =
    C ((2:ℤ)^106) * horner X vp00000100101001.list + horner X ep00000100101001.list := by
  exact edge_identity (B := (2:ℤ)^248) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100101001 : Branch 1 (-147761639/1000000 : ℚ) vp0000010010100 := by
  apply branch_checked idp00000100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-147761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-148261639/500000 : ℚ) by norm_num]
  exact coverp00000100101001
theorem coverp0000010010100 : Covers (-147761639/1000000 : ℚ) vp0000010010100 := join_branches bp00000100101000 bp00000100101001
private noncomputable def vp000001001010_0 : Blocks := edgeBlocks% "full/vectors/000001001010-V-0000.bin"
private noncomputable def vp000001001010_1 : Blocks := edgeBlocks% "full/vectors/000001001010-V-0001.bin"
noncomputable def vp000001001010 : Blocks := (Blocks.join vp000001001010_0 vp000001001010_1)
private theorem bp0000010010100 : Branch 0 (-147761639/2000000 : ℚ) vp000001001010 := by
  apply branch_left_normalized (c:=vp0000010010100) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-147761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-147761639/1000000 : ℚ) by norm_num]
  exact coverp0000010010100
private noncomputable def ep0000010010101_0 : Blocks := edgeBlocks% "full/vectors/0000010010101-E-0000.bin"
private noncomputable def ep0000010010101_1 : Blocks := edgeBlocks% "full/vectors/0000010010101-E-0001.bin"
noncomputable def ep0000010010101 : Blocks := (Blocks.join ep0000010010101_0 ep0000010010101_1)
private theorem idp0000010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001001010.list =
    C ((2:ℤ)^192) * horner X vp0000010010101.list + horner X ep0000010010101.list := by
  exact edge_identity (B := (2:ℤ)^373) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010010101 : Branch 1 (-147761639/2000000 : ℚ) vp000001001010 := by
  apply branch_checked idp0000010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-147761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-148761639/1000000 : ℚ) by norm_num]
  exact coverp0000010010101
theorem coverp000001001010 : Covers (-147761639/2000000 : ℚ) vp000001001010 := join_branches bp0000010010100 bp0000010010101
private noncomputable def vp00000100101_0 : Blocks := edgeBlocks% "full/vectors/00000100101-V-0000.bin"
private noncomputable def vp00000100101_1 : Blocks := edgeBlocks% "full/vectors/00000100101-V-0001.bin"
private noncomputable def vp00000100101_2 : Blocks := edgeBlocks% "full/vectors/00000100101-V-0002.bin"
noncomputable def vp00000100101 : Blocks := (Blocks.join vp00000100101_0 (Blocks.join vp00000100101_1 vp00000100101_2))
private theorem bp000001001010 : Branch 0 (-147761639/4000000 : ℚ) vp00000100101 := by
  apply branch_left_normalized (c:=vp000001001010) (k:=0) (m:=184) (by decide +kernel)
  rw [show 2*(-147761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-147761639/2000000 : ℚ) by norm_num]
  exact coverp000001001010
private noncomputable def ep000001001011_0 : Blocks := edgeBlocks% "full/vectors/000001001011-E-0000.bin"
private noncomputable def ep000001001011_1 : Blocks := edgeBlocks% "full/vectors/000001001011-E-0001.bin"
private noncomputable def ep000001001011_2 : Blocks := edgeBlocks% "full/vectors/000001001011-E-0002.bin"
noncomputable def ep000001001011 : Blocks := (Blocks.join ep000001001011_0 (Blocks.join ep000001001011_1 ep000001001011_2))
private theorem idp000001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100101.list =
    C ((2:ℤ)^357) * horner X vp000001001011.list + horner X ep000001001011.list := by
  exact edge_identity (B := (2:ℤ)^619) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001011 : Branch 1 (-147761639/4000000 : ℚ) vp00000100101 := by
  apply branch_checked idp000001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-147761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-149761639/2000000 : ℚ) by norm_num]
  exact coverp000001001011
theorem coverp00000100101 : Covers (-147761639/4000000 : ℚ) vp00000100101 := join_branches bp000001001010 bp000001001011
private noncomputable def vp000001001001111_0 : Blocks := edgeBlocks% "full/vectors/000001001001111-V-0000.bin"
noncomputable def vp000001001001111 : Blocks := vp000001001001111_0
theorem coverp000001001001111 : Covers (-147511639/250000 : ℚ) vp000001001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001001110_0 : Blocks := edgeBlocks% "full/vectors/000001001001110-V-0000.bin"
noncomputable def vp000001001001110 : Blocks := vp000001001001110_0
theorem coverp000001001001110 : Covers (-147261639/250000 : ℚ) vp000001001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100100111_0 : Blocks := edgeBlocks% "full/vectors/00000100100111-V-0000.bin"
noncomputable def vp00000100100111 : Blocks := vp00000100100111_0
private theorem bp000001001001110 : Branch 0 (-147261639/500000 : ℚ) vp00000100100111 := by
  apply branch_left_normalized (c:=vp000001001001110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-147261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-147261639/250000 : ℚ) by norm_num]
  exact coverp000001001001110
private noncomputable def ep000001001001111_0 : Blocks := edgeBlocks% "full/vectors/000001001001111-E-0000.bin"
noncomputable def ep000001001001111 : Blocks := ep000001001001111_0
private theorem idp000001001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100100111.list =
    C ((2:ℤ)^64) * horner X vp000001001001111.list + horner X ep000001001001111.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001001111 : Branch 1 (-147261639/500000 : ℚ) vp00000100100111 := by
  apply branch_checked idp000001001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-147261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-147511639/250000 : ℚ) by norm_num]
  exact coverp000001001001111
theorem coverp00000100100111 : Covers (-147261639/500000 : ℚ) vp00000100100111 := join_branches bp000001001001110 bp000001001001111
private noncomputable def vp000001001001101_0 : Blocks := edgeBlocks% "full/vectors/000001001001101-V-0000.bin"
noncomputable def vp000001001001101 : Blocks := vp000001001001101_0
theorem coverp000001001001101 : Covers (-147011639/250000 : ℚ) vp000001001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001001100_0 : Blocks := edgeBlocks% "full/vectors/000001001001100-V-0000.bin"
noncomputable def vp000001001001100 : Blocks := vp000001001001100_0
theorem coverp000001001001100 : Covers (-146761639/250000 : ℚ) vp000001001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100100110_0 : Blocks := edgeBlocks% "full/vectors/00000100100110-V-0000.bin"
noncomputable def vp00000100100110 : Blocks := vp00000100100110_0
private theorem bp000001001001100 : Branch 0 (-146761639/500000 : ℚ) vp00000100100110 := by
  apply branch_left_normalized (c:=vp000001001001100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-146761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-146761639/250000 : ℚ) by norm_num]
  exact coverp000001001001100
private noncomputable def ep000001001001101_0 : Blocks := edgeBlocks% "full/vectors/000001001001101-E-0000.bin"
noncomputable def ep000001001001101 : Blocks := ep000001001001101_0
private theorem idp000001001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100100110.list =
    C ((2:ℤ)^63) * horner X vp000001001001101.list + horner X ep000001001001101.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001001101 : Branch 1 (-146761639/500000 : ℚ) vp00000100100110 := by
  apply branch_checked idp000001001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-146761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-147011639/250000 : ℚ) by norm_num]
  exact coverp000001001001101
theorem coverp00000100100110 : Covers (-146761639/500000 : ℚ) vp00000100100110 := join_branches bp000001001001100 bp000001001001101
private noncomputable def vp0000010010011_0 : Blocks := edgeBlocks% "full/vectors/0000010010011-V-0000.bin"
noncomputable def vp0000010010011 : Blocks := vp0000010010011_0
private theorem bp00000100100110 : Branch 0 (-146761639/1000000 : ℚ) vp0000010010011 := by
  apply branch_left_normalized (c:=vp00000100100110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-146761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-146761639/500000 : ℚ) by norm_num]
  exact coverp00000100100110
private noncomputable def ep00000100100111_0 : Blocks := edgeBlocks% "full/vectors/00000100100111-E-0000.bin"
noncomputable def ep00000100100111 : Blocks := ep00000100100111_0
private theorem idp00000100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010010011.list =
    C ((2:ℤ)^106) * horner X vp00000100100111.list + horner X ep00000100100111.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100100111 : Branch 1 (-146761639/1000000 : ℚ) vp0000010010011 := by
  apply branch_checked idp00000100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-146761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-147261639/500000 : ℚ) by norm_num]
  exact coverp00000100100111
theorem coverp0000010010011 : Covers (-146761639/1000000 : ℚ) vp0000010010011 := join_branches bp00000100100110 bp00000100100111
private noncomputable def vp000001001001011_0 : Blocks := edgeBlocks% "full/vectors/000001001001011-V-0000.bin"
noncomputable def vp000001001001011 : Blocks := vp000001001001011_0
theorem coverp000001001001011 : Covers (-146511639/250000 : ℚ) vp000001001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001001010_0 : Blocks := edgeBlocks% "full/vectors/000001001001010-V-0000.bin"
noncomputable def vp000001001001010 : Blocks := vp000001001001010_0
theorem coverp000001001001010 : Covers (-146261639/250000 : ℚ) vp000001001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100100101_0 : Blocks := edgeBlocks% "full/vectors/00000100100101-V-0000.bin"
noncomputable def vp00000100100101 : Blocks := vp00000100100101_0
private theorem bp000001001001010 : Branch 0 (-146261639/500000 : ℚ) vp00000100100101 := by
  apply branch_left_normalized (c:=vp000001001001010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-146261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-146261639/250000 : ℚ) by norm_num]
  exact coverp000001001001010
private noncomputable def ep000001001001011_0 : Blocks := edgeBlocks% "full/vectors/000001001001011-E-0000.bin"
noncomputable def ep000001001001011 : Blocks := ep000001001001011_0
private theorem idp000001001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100100101.list =
    C ((2:ℤ)^63) * horner X vp000001001001011.list + horner X ep000001001001011.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001001011 : Branch 1 (-146261639/500000 : ℚ) vp00000100100101 := by
  apply branch_checked idp000001001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-146261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-146511639/250000 : ℚ) by norm_num]
  exact coverp000001001001011
theorem coverp00000100100101 : Covers (-146261639/500000 : ℚ) vp00000100100101 := join_branches bp000001001001010 bp000001001001011
private noncomputable def vp000001001001001_0 : Blocks := edgeBlocks% "full/vectors/000001001001001-V-0000.bin"
noncomputable def vp000001001001001 : Blocks := vp000001001001001_0
theorem coverp000001001001001 : Covers (-146011639/250000 : ℚ) vp000001001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001001000_0 : Blocks := edgeBlocks% "full/vectors/000001001001000-V-0000.bin"
noncomputable def vp000001001001000 : Blocks := vp000001001001000_0
theorem coverp000001001001000 : Covers (-145761639/250000 : ℚ) vp000001001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100100100_0 : Blocks := edgeBlocks% "full/vectors/00000100100100-V-0000.bin"
noncomputable def vp00000100100100 : Blocks := vp00000100100100_0
private theorem bp000001001001000 : Branch 0 (-145761639/500000 : ℚ) vp00000100100100 := by
  apply branch_left_normalized (c:=vp000001001001000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-145761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-145761639/250000 : ℚ) by norm_num]
  exact coverp000001001001000
private noncomputable def ep000001001001001_0 : Blocks := edgeBlocks% "full/vectors/000001001001001-E-0000.bin"
noncomputable def ep000001001001001 : Blocks := ep000001001001001_0
private theorem idp000001001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100100100.list =
    C ((2:ℤ)^62) * horner X vp000001001001001.list + horner X ep000001001001001.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001001001 : Branch 1 (-145761639/500000 : ℚ) vp00000100100100 := by
  apply branch_checked idp000001001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-145761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-146011639/250000 : ℚ) by norm_num]
  exact coverp000001001001001
theorem coverp00000100100100 : Covers (-145761639/500000 : ℚ) vp00000100100100 := join_branches bp000001001001000 bp000001001001001
private noncomputable def vp0000010010010_0 : Blocks := edgeBlocks% "full/vectors/0000010010010-V-0000.bin"
noncomputable def vp0000010010010 : Blocks := vp0000010010010_0
private theorem bp00000100100100 : Branch 0 (-145761639/1000000 : ℚ) vp0000010010010 := by
  apply branch_left_normalized (c:=vp00000100100100) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-145761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-145761639/500000 : ℚ) by norm_num]
  exact coverp00000100100100
private noncomputable def ep00000100100101_0 : Blocks := edgeBlocks% "full/vectors/00000100100101-E-0000.bin"
noncomputable def ep00000100100101 : Blocks := ep00000100100101_0
private theorem idp00000100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010010010.list =
    C ((2:ℤ)^106) * horner X vp00000100100101.list + horner X ep00000100100101.list := by
  exact edge_identity (B := (2:ℤ)^247) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100100101 : Branch 1 (-145761639/1000000 : ℚ) vp0000010010010 := by
  apply branch_checked idp00000100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-145761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-146261639/500000 : ℚ) by norm_num]
  exact coverp00000100100101
theorem coverp0000010010010 : Covers (-145761639/1000000 : ℚ) vp0000010010010 := join_branches bp00000100100100 bp00000100100101
private noncomputable def vp000001001001_0 : Blocks := edgeBlocks% "full/vectors/000001001001-V-0000.bin"
private noncomputable def vp000001001001_1 : Blocks := edgeBlocks% "full/vectors/000001001001-V-0001.bin"
noncomputable def vp000001001001 : Blocks := (Blocks.join vp000001001001_0 vp000001001001_1)
private theorem bp0000010010010 : Branch 0 (-145761639/2000000 : ℚ) vp000001001001 := by
  apply branch_left_normalized (c:=vp0000010010010) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-145761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-145761639/1000000 : ℚ) by norm_num]
  exact coverp0000010010010
private noncomputable def ep0000010010011_0 : Blocks := edgeBlocks% "full/vectors/0000010010011-E-0000.bin"
private noncomputable def ep0000010010011_1 : Blocks := edgeBlocks% "full/vectors/0000010010011-E-0001.bin"
noncomputable def ep0000010010011 : Blocks := (Blocks.join ep0000010010011_0 ep0000010010011_1)
private theorem idp0000010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001001001.list =
    C ((2:ℤ)^190) * horner X vp0000010010011.list + horner X ep0000010010011.list := by
  exact edge_identity (B := (2:ℤ)^373) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010010011 : Branch 1 (-145761639/2000000 : ℚ) vp000001001001 := by
  apply branch_checked idp0000010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-145761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-146761639/1000000 : ℚ) by norm_num]
  exact coverp0000010010011
theorem coverp000001001001 : Covers (-145761639/2000000 : ℚ) vp000001001001 := join_branches bp0000010010010 bp0000010010011
private noncomputable def vp000001001000111_0 : Blocks := edgeBlocks% "full/vectors/000001001000111-V-0000.bin"
noncomputable def vp000001001000111 : Blocks := vp000001001000111_0
theorem coverp000001001000111 : Covers (-145511639/250000 : ℚ) vp000001001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001000110_0 : Blocks := edgeBlocks% "full/vectors/000001001000110-V-0000.bin"
noncomputable def vp000001001000110 : Blocks := vp000001001000110_0
theorem coverp000001001000110 : Covers (-145261639/250000 : ℚ) vp000001001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100100011_0 : Blocks := edgeBlocks% "full/vectors/00000100100011-V-0000.bin"
noncomputable def vp00000100100011 : Blocks := vp00000100100011_0
private theorem bp000001001000110 : Branch 0 (-145261639/500000 : ℚ) vp00000100100011 := by
  apply branch_left_normalized (c:=vp000001001000110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-145261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-145261639/250000 : ℚ) by norm_num]
  exact coverp000001001000110
private noncomputable def ep000001001000111_0 : Blocks := edgeBlocks% "full/vectors/000001001000111-E-0000.bin"
noncomputable def ep000001001000111 : Blocks := ep000001001000111_0
private theorem idp000001001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100100011.list =
    C ((2:ℤ)^63) * horner X vp000001001000111.list + horner X ep000001001000111.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001000111 : Branch 1 (-145261639/500000 : ℚ) vp00000100100011 := by
  apply branch_checked idp000001001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-145261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-145511639/250000 : ℚ) by norm_num]
  exact coverp000001001000111
theorem coverp00000100100011 : Covers (-145261639/500000 : ℚ) vp00000100100011 := join_branches bp000001001000110 bp000001001000111
private noncomputable def vp000001001000101_0 : Blocks := edgeBlocks% "full/vectors/000001001000101-V-0000.bin"
noncomputable def vp000001001000101 : Blocks := vp000001001000101_0
theorem coverp000001001000101 : Covers (-145011639/250000 : ℚ) vp000001001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001000100_0 : Blocks := edgeBlocks% "full/vectors/000001001000100-V-0000.bin"
noncomputable def vp000001001000100 : Blocks := vp000001001000100_0
theorem coverp000001001000100 : Covers (-144761639/250000 : ℚ) vp000001001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100100010_0 : Blocks := edgeBlocks% "full/vectors/00000100100010-V-0000.bin"
noncomputable def vp00000100100010 : Blocks := vp00000100100010_0
private theorem bp000001001000100 : Branch 0 (-144761639/500000 : ℚ) vp00000100100010 := by
  apply branch_left_normalized (c:=vp000001001000100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-144761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-144761639/250000 : ℚ) by norm_num]
  exact coverp000001001000100
private noncomputable def ep000001001000101_0 : Blocks := edgeBlocks% "full/vectors/000001001000101-E-0000.bin"
noncomputable def ep000001001000101 : Blocks := ep000001001000101_0
private theorem idp000001001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100100010.list =
    C ((2:ℤ)^64) * horner X vp000001001000101.list + horner X ep000001001000101.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001000101 : Branch 1 (-144761639/500000 : ℚ) vp00000100100010 := by
  apply branch_checked idp000001001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-144761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-145011639/250000 : ℚ) by norm_num]
  exact coverp000001001000101
theorem coverp00000100100010 : Covers (-144761639/500000 : ℚ) vp00000100100010 := join_branches bp000001001000100 bp000001001000101
private noncomputable def vp0000010010001_0 : Blocks := edgeBlocks% "full/vectors/0000010010001-V-0000.bin"
noncomputable def vp0000010010001 : Blocks := vp0000010010001_0
private theorem bp00000100100010 : Branch 0 (-144761639/1000000 : ℚ) vp0000010010001 := by
  apply branch_left_normalized (c:=vp00000100100010) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-144761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-144761639/500000 : ℚ) by norm_num]
  exact coverp00000100100010
private noncomputable def ep00000100100011_0 : Blocks := edgeBlocks% "full/vectors/00000100100011-E-0000.bin"
noncomputable def ep00000100100011 : Blocks := ep00000100100011_0
private theorem idp00000100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010010001.list =
    C ((2:ℤ)^107) * horner X vp00000100100011.list + horner X ep00000100100011.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100100011 : Branch 1 (-144761639/1000000 : ℚ) vp0000010010001 := by
  apply branch_checked idp00000100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-144761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-145261639/500000 : ℚ) by norm_num]
  exact coverp00000100100011
theorem coverp0000010010001 : Covers (-144761639/1000000 : ℚ) vp0000010010001 := join_branches bp00000100100010 bp00000100100011
private noncomputable def vp000001001000011_0 : Blocks := edgeBlocks% "full/vectors/000001001000011-V-0000.bin"
noncomputable def vp000001001000011 : Blocks := vp000001001000011_0
theorem coverp000001001000011 : Covers (-144511639/250000 : ℚ) vp000001001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001000010_0 : Blocks := edgeBlocks% "full/vectors/000001001000010-V-0000.bin"
noncomputable def vp000001001000010 : Blocks := vp000001001000010_0
theorem coverp000001001000010 : Covers (-144261639/250000 : ℚ) vp000001001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100100001_0 : Blocks := edgeBlocks% "full/vectors/00000100100001-V-0000.bin"
noncomputable def vp00000100100001 : Blocks := vp00000100100001_0
private theorem bp000001001000010 : Branch 0 (-144261639/500000 : ℚ) vp00000100100001 := by
  apply branch_left_normalized (c:=vp000001001000010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-144261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-144261639/250000 : ℚ) by norm_num]
  exact coverp000001001000010
private noncomputable def ep000001001000011_0 : Blocks := edgeBlocks% "full/vectors/000001001000011-E-0000.bin"
noncomputable def ep000001001000011 : Blocks := ep000001001000011_0
private theorem idp000001001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100100001.list =
    C ((2:ℤ)^64) * horner X vp000001001000011.list + horner X ep000001001000011.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001000011 : Branch 1 (-144261639/500000 : ℚ) vp00000100100001 := by
  apply branch_checked idp000001001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-144261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-144511639/250000 : ℚ) by norm_num]
  exact coverp000001001000011
theorem coverp00000100100001 : Covers (-144261639/500000 : ℚ) vp00000100100001 := join_branches bp000001001000010 bp000001001000011
private noncomputable def vp000001001000001_0 : Blocks := edgeBlocks% "full/vectors/000001001000001-V-0000.bin"
noncomputable def vp000001001000001 : Blocks := vp000001001000001_0
theorem coverp000001001000001 : Covers (-144011639/250000 : ℚ) vp000001001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001001000000_0 : Blocks := edgeBlocks% "full/vectors/000001001000000-V-0000.bin"
noncomputable def vp000001001000000 : Blocks := vp000001001000000_0
theorem coverp000001001000000 : Covers (-143761639/250000 : ℚ) vp000001001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000100100000_0 : Blocks := edgeBlocks% "full/vectors/00000100100000-V-0000.bin"
noncomputable def vp00000100100000 : Blocks := vp00000100100000_0
private theorem bp000001001000000 : Branch 0 (-143761639/500000 : ℚ) vp00000100100000 := by
  apply branch_left_normalized (c:=vp000001001000000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-143761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-143761639/250000 : ℚ) by norm_num]
  exact coverp000001001000000
private noncomputable def ep000001001000001_0 : Blocks := edgeBlocks% "full/vectors/000001001000001-E-0000.bin"
noncomputable def ep000001001000001 : Blocks := ep000001001000001_0
private theorem idp000001001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100100000.list =
    C ((2:ℤ)^63) * horner X vp000001001000001.list + horner X ep000001001000001.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001000001 : Branch 1 (-143761639/500000 : ℚ) vp00000100100000 := by
  apply branch_checked idp000001001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-143761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-144011639/250000 : ℚ) by norm_num]
  exact coverp000001001000001
theorem coverp00000100100000 : Covers (-143761639/500000 : ℚ) vp00000100100000 := join_branches bp000001001000000 bp000001001000001
private noncomputable def vp0000010010000_0 : Blocks := edgeBlocks% "full/vectors/0000010010000-V-0000.bin"
noncomputable def vp0000010010000 : Blocks := vp0000010010000_0
private theorem bp00000100100000 : Branch 0 (-143761639/1000000 : ℚ) vp0000010010000 := by
  apply branch_left_normalized (c:=vp00000100100000) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-143761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-143761639/500000 : ℚ) by norm_num]
  exact coverp00000100100000
private noncomputable def ep00000100100001_0 : Blocks := edgeBlocks% "full/vectors/00000100100001-E-0000.bin"
noncomputable def ep00000100100001 : Blocks := ep00000100100001_0
private theorem idp00000100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010010000.list =
    C ((2:ℤ)^108) * horner X vp00000100100001.list + horner X ep00000100100001.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100100001 : Branch 1 (-143761639/1000000 : ℚ) vp0000010010000 := by
  apply branch_checked idp00000100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-143761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-144261639/500000 : ℚ) by norm_num]
  exact coverp00000100100001
theorem coverp0000010010000 : Covers (-143761639/1000000 : ℚ) vp0000010010000 := join_branches bp00000100100000 bp00000100100001
private noncomputable def vp000001001000_0 : Blocks := edgeBlocks% "full/vectors/000001001000-V-0000.bin"
private noncomputable def vp000001001000_1 : Blocks := edgeBlocks% "full/vectors/000001001000-V-0001.bin"
noncomputable def vp000001001000 : Blocks := (Blocks.join vp000001001000_0 vp000001001000_1)
private theorem bp0000010010000 : Branch 0 (-143761639/2000000 : ℚ) vp000001001000 := by
  apply branch_left_normalized (c:=vp0000010010000) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-143761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-143761639/1000000 : ℚ) by norm_num]
  exact coverp0000010010000
private noncomputable def ep0000010010001_0 : Blocks := edgeBlocks% "full/vectors/0000010010001-E-0000.bin"
private noncomputable def ep0000010010001_1 : Blocks := edgeBlocks% "full/vectors/0000010010001-E-0001.bin"
noncomputable def ep0000010010001 : Blocks := (Blocks.join ep0000010010001_0 ep0000010010001_1)
private theorem idp0000010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001001000.list =
    C ((2:ℤ)^194) * horner X vp0000010010001.list + horner X ep0000010010001.list := by
  exact edge_identity (B := (2:ℤ)^377) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010010001 : Branch 1 (-143761639/2000000 : ℚ) vp000001001000 := by
  apply branch_checked idp0000010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-143761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-144761639/1000000 : ℚ) by norm_num]
  exact coverp0000010010001
theorem coverp000001001000 : Covers (-143761639/2000000 : ℚ) vp000001001000 := join_branches bp0000010010000 bp0000010010001
private noncomputable def vp00000100100_0 : Blocks := edgeBlocks% "full/vectors/00000100100-V-0000.bin"
private noncomputable def vp00000100100_1 : Blocks := edgeBlocks% "full/vectors/00000100100-V-0001.bin"
private noncomputable def vp00000100100_2 : Blocks := edgeBlocks% "full/vectors/00000100100-V-0002.bin"
noncomputable def vp00000100100 : Blocks := (Blocks.join vp00000100100_0 (Blocks.join vp00000100100_1 vp00000100100_2))
private theorem bp000001001000 : Branch 0 (-143761639/4000000 : ℚ) vp00000100100 := by
  apply branch_left_normalized (c:=vp000001001000) (k:=0) (m:=186) (by decide +kernel)
  rw [show 2*(-143761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-143761639/2000000 : ℚ) by norm_num]
  exact coverp000001001000
private noncomputable def ep000001001001_0 : Blocks := edgeBlocks% "full/vectors/000001001001-E-0000.bin"
private noncomputable def ep000001001001_1 : Blocks := edgeBlocks% "full/vectors/000001001001-E-0001.bin"
private noncomputable def ep000001001001_2 : Blocks := edgeBlocks% "full/vectors/000001001001-E-0002.bin"
noncomputable def ep000001001001 : Blocks := (Blocks.join ep000001001001_0 (Blocks.join ep000001001001_1 ep000001001001_2))
private theorem idp000001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000100100.list =
    C ((2:ℤ)^364) * horner X vp000001001001.list + horner X ep000001001001.list := by
  exact edge_identity (B := (2:ℤ)^627) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001001001 : Branch 1 (-143761639/4000000 : ℚ) vp00000100100 := by
  apply branch_checked idp000001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-143761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-145761639/2000000 : ℚ) by norm_num]
  exact coverp000001001001
theorem coverp00000100100 : Covers (-143761639/4000000 : ℚ) vp00000100100 := join_branches bp000001001000 bp000001001001
private noncomputable def vp0000010010_0 : Blocks := edgeBlocks% "full/vectors/0000010010-V-0000.bin"
private noncomputable def vp0000010010_1 : Blocks := edgeBlocks% "full/vectors/0000010010-V-0001.bin"
private noncomputable def vp0000010010_2 : Blocks := edgeBlocks% "full/vectors/0000010010-V-0002.bin"
private noncomputable def vp0000010010_3 : Blocks := edgeBlocks% "full/vectors/0000010010-V-0003.bin"
private noncomputable def vp0000010010_4 : Blocks := edgeBlocks% "full/vectors/0000010010-V-0004.bin"
private noncomputable def vp0000010010_5 : Blocks := edgeBlocks% "full/vectors/0000010010-V-0005.bin"
noncomputable def vp0000010010 : Blocks := (Blocks.join (Blocks.join vp0000010010_0 (Blocks.join vp0000010010_1 vp0000010010_2)) (Blocks.join vp0000010010_3 (Blocks.join vp0000010010_4 vp0000010010_5)))
private theorem bp00000100100 : Branch 0 (-143761639/8000000 : ℚ) vp0000010010 := by
  apply branch_left_normalized (c:=vp00000100100) (k:=0) (m:=350) (by decide +kernel)
  rw [show 2*(-143761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-143761639/4000000 : ℚ) by norm_num]
  exact coverp00000100100
private noncomputable def ep00000100101_0 : Blocks := edgeBlocks% "full/vectors/00000100101-E-0000.bin"
private noncomputable def ep00000100101_1 : Blocks := edgeBlocks% "full/vectors/00000100101-E-0001.bin"
private noncomputable def ep00000100101_2 : Blocks := edgeBlocks% "full/vectors/00000100101-E-0002.bin"
private noncomputable def ep00000100101_3 : Blocks := edgeBlocks% "full/vectors/00000100101-E-0003.bin"
private noncomputable def ep00000100101_4 : Blocks := edgeBlocks% "full/vectors/00000100101-E-0004.bin"
private noncomputable def ep00000100101_5 : Blocks := edgeBlocks% "full/vectors/00000100101-E-0005.bin"
noncomputable def ep00000100101 : Blocks := (Blocks.join (Blocks.join ep00000100101_0 (Blocks.join ep00000100101_1 ep00000100101_2)) (Blocks.join ep00000100101_3 (Blocks.join ep00000100101_4 ep00000100101_5)))
private theorem idp00000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000010010.list =
    C ((2:ℤ)^698) * horner X vp00000100101.list + horner X ep00000100101.list := by
  exact edge_identity (B := (2:ℤ)^1124) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000100101 : Branch 1 (-143761639/8000000 : ℚ) vp0000010010 := by
  apply branch_checked idp00000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-143761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-147761639/4000000 : ℚ) by norm_num]
  exact coverp00000100101
theorem coverp0000010010 : Covers (-143761639/8000000 : ℚ) vp0000010010 := join_branches bp00000100100 bp00000100101
private noncomputable def vp000001001_0 : Blocks := edgeBlocks% "full/vectors/000001001-V-0000.bin"
private noncomputable def vp000001001_1 : Blocks := edgeBlocks% "full/vectors/000001001-V-0001.bin"
private noncomputable def vp000001001_2 : Blocks := edgeBlocks% "full/vectors/000001001-V-0002.bin"
private noncomputable def vp000001001_3 : Blocks := edgeBlocks% "full/vectors/000001001-V-0003.bin"
private noncomputable def vp000001001_4 : Blocks := edgeBlocks% "full/vectors/000001001-V-0004.bin"
private noncomputable def vp000001001_5 : Blocks := edgeBlocks% "full/vectors/000001001-V-0005.bin"
private noncomputable def vp000001001_6 : Blocks := edgeBlocks% "full/vectors/000001001-V-0006.bin"
private noncomputable def vp000001001_7 : Blocks := edgeBlocks% "full/vectors/000001001-V-0007.bin"
private noncomputable def vp000001001_8 : Blocks := edgeBlocks% "full/vectors/000001001-V-0008.bin"
private noncomputable def vp000001001_9 : Blocks := edgeBlocks% "full/vectors/000001001-V-0009.bin"
private noncomputable def vp000001001_10 : Blocks := edgeBlocks% "full/vectors/000001001-V-0010.bin"
noncomputable def vp000001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000001001_0 vp000001001_1) (Blocks.join vp000001001_2 (Blocks.join vp000001001_3 vp000001001_4))) (Blocks.join (Blocks.join vp000001001_5 (Blocks.join vp000001001_6 vp000001001_7)) (Blocks.join vp000001001_8 (Blocks.join vp000001001_9 vp000001001_10))))
private theorem bp0000010010 : Branch 0 (-143761639/16000000 : ℚ) vp000001001 := by
  apply branch_left_normalized (c:=vp0000010010) (k:=0) (m:=673) (by decide +kernel)
  rw [show 2*(-143761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-143761639/8000000 : ℚ) by norm_num]
  exact coverp0000010010
private noncomputable def ep0000010011_0 : Blocks := edgeBlocks% "full/vectors/0000010011-E-0000.bin"
private noncomputable def ep0000010011_1 : Blocks := edgeBlocks% "full/vectors/0000010011-E-0001.bin"
private noncomputable def ep0000010011_2 : Blocks := edgeBlocks% "full/vectors/0000010011-E-0002.bin"
private noncomputable def ep0000010011_3 : Blocks := edgeBlocks% "full/vectors/0000010011-E-0003.bin"
private noncomputable def ep0000010011_4 : Blocks := edgeBlocks% "full/vectors/0000010011-E-0004.bin"
private noncomputable def ep0000010011_5 : Blocks := edgeBlocks% "full/vectors/0000010011-E-0005.bin"
private noncomputable def ep0000010011_6 : Blocks := edgeBlocks% "full/vectors/0000010011-E-0006.bin"
private noncomputable def ep0000010011_7 : Blocks := edgeBlocks% "full/vectors/0000010011-E-0007.bin"
private noncomputable def ep0000010011_8 : Blocks := edgeBlocks% "full/vectors/0000010011-E-0008.bin"
private noncomputable def ep0000010011_9 : Blocks := edgeBlocks% "full/vectors/0000010011-E-0009.bin"
private noncomputable def ep0000010011_10 : Blocks := edgeBlocks% "full/vectors/0000010011-E-0010.bin"
noncomputable def ep0000010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000010011_0 ep0000010011_1) (Blocks.join ep0000010011_2 (Blocks.join ep0000010011_3 ep0000010011_4))) (Blocks.join (Blocks.join ep0000010011_5 (Blocks.join ep0000010011_6 ep0000010011_7)) (Blocks.join ep0000010011_8 (Blocks.join ep0000010011_9 ep0000010011_10))))
private theorem idp0000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001001.list =
    C ((2:ℤ)^1359) * horner X vp0000010011.list + horner X ep0000010011.list := by
  exact edge_identity (B := (2:ℤ)^2104) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000010011 : Branch 1 (-143761639/16000000 : ℚ) vp000001001 := by
  apply branch_checked idp0000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-143761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-151761639/8000000 : ℚ) by norm_num]
  exact coverp0000010011
theorem coverp000001001 : Covers (-143761639/16000000 : ℚ) vp000001001 := join_branches bp0000010010 bp0000010011
end NextProof.EdgeFull

