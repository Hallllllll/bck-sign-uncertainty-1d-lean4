import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00032

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000001000111111_0 : Blocks := edgeBlocks% "full/vectors/0000001000111111-V-0000.bin"
noncomputable def vp0000001000111111 : Blocks := vp0000001000111111_0
theorem coverp0000001000111111 : Covers (-71636639/125000 : ℚ) vp0000001000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001000111110_0 : Blocks := edgeBlocks% "full/vectors/0000001000111110-V-0000.bin"
noncomputable def vp0000001000111110 : Blocks := vp0000001000111110_0
theorem coverp0000001000111110 : Covers (-71511639/125000 : ℚ) vp0000001000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100011111_0 : Blocks := edgeBlocks% "full/vectors/000000100011111-V-0000.bin"
noncomputable def vp000000100011111 : Blocks := vp000000100011111_0
private theorem bp0000001000111110 : Branch 0 (-71511639/250000 : ℚ) vp000000100011111 := by
  apply branch_left_normalized (c:=vp0000001000111110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-71511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-71511639/125000 : ℚ) by norm_num]
  exact coverp0000001000111110
private noncomputable def ep0000001000111111_0 : Blocks := edgeBlocks% "full/vectors/0000001000111111-E-0000.bin"
noncomputable def ep0000001000111111 : Blocks := ep0000001000111111_0
private theorem idp0000001000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100011111.list =
    C ((2:ℤ)^50) * horner X vp0000001000111111.list + horner X ep0000001000111111.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001000111111 : Branch 1 (-71511639/250000 : ℚ) vp000000100011111 := by
  apply branch_checked idp0000001000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-71511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-71636639/125000 : ℚ) by norm_num]
  exact coverp0000001000111111
theorem coverp000000100011111 : Covers (-71511639/250000 : ℚ) vp000000100011111 := join_branches bp0000001000111110 bp0000001000111111
private noncomputable def vp0000001000111101_0 : Blocks := edgeBlocks% "full/vectors/0000001000111101-V-0000.bin"
noncomputable def vp0000001000111101 : Blocks := vp0000001000111101_0
theorem coverp0000001000111101 : Covers (-71386639/125000 : ℚ) vp0000001000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001000111100_0 : Blocks := edgeBlocks% "full/vectors/0000001000111100-V-0000.bin"
noncomputable def vp0000001000111100 : Blocks := vp0000001000111100_0
theorem coverp0000001000111100 : Covers (-71261639/125000 : ℚ) vp0000001000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100011110_0 : Blocks := edgeBlocks% "full/vectors/000000100011110-V-0000.bin"
noncomputable def vp000000100011110 : Blocks := vp000000100011110_0
private theorem bp0000001000111100 : Branch 0 (-71261639/250000 : ℚ) vp000000100011110 := by
  apply branch_left_normalized (c:=vp0000001000111100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-71261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-71261639/125000 : ℚ) by norm_num]
  exact coverp0000001000111100
private noncomputable def ep0000001000111101_0 : Blocks := edgeBlocks% "full/vectors/0000001000111101-E-0000.bin"
noncomputable def ep0000001000111101 : Blocks := ep0000001000111101_0
private theorem idp0000001000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100011110.list =
    C ((2:ℤ)^48) * horner X vp0000001000111101.list + horner X ep0000001000111101.list := by
  exact edge_identity (B := (2:ℤ)^163) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001000111101 : Branch 1 (-71261639/250000 : ℚ) vp000000100011110 := by
  apply branch_checked idp0000001000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-71261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-71386639/125000 : ℚ) by norm_num]
  exact coverp0000001000111101
theorem coverp000000100011110 : Covers (-71261639/250000 : ℚ) vp000000100011110 := join_branches bp0000001000111100 bp0000001000111101
private noncomputable def vp00000010001111_0 : Blocks := edgeBlocks% "full/vectors/00000010001111-V-0000.bin"
noncomputable def vp00000010001111 : Blocks := vp00000010001111_0
private theorem bp000000100011110 : Branch 0 (-71261639/500000 : ℚ) vp00000010001111 := by
  apply branch_left_normalized (c:=vp000000100011110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-71261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-71261639/250000 : ℚ) by norm_num]
  exact coverp000000100011110
private noncomputable def ep000000100011111_0 : Blocks := edgeBlocks% "full/vectors/000000100011111-E-0000.bin"
noncomputable def ep000000100011111 : Blocks := ep000000100011111_0
private theorem idp000000100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010001111.list =
    C ((2:ℤ)^78) * horner X vp000000100011111.list + horner X ep000000100011111.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100011111 : Branch 1 (-71261639/500000 : ℚ) vp00000010001111 := by
  apply branch_checked idp000000100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-71261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-71511639/250000 : ℚ) by norm_num]
  exact coverp000000100011111
theorem coverp00000010001111 : Covers (-71261639/500000 : ℚ) vp00000010001111 := join_branches bp000000100011110 bp000000100011111
private noncomputable def vp0000001000111011_0 : Blocks := edgeBlocks% "full/vectors/0000001000111011-V-0000.bin"
noncomputable def vp0000001000111011 : Blocks := vp0000001000111011_0
theorem coverp0000001000111011 : Covers (-71136639/125000 : ℚ) vp0000001000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000001000111010_0 : Blocks := edgeBlocks% "full/vectors/0000001000111010-V-0000.bin"
noncomputable def vp0000001000111010 : Blocks := vp0000001000111010_0
theorem coverp0000001000111010 : Covers (-71011639/125000 : ℚ) vp0000001000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100011101_0 : Blocks := edgeBlocks% "full/vectors/000000100011101-V-0000.bin"
noncomputable def vp000000100011101 : Blocks := vp000000100011101_0
private theorem bp0000001000111010 : Branch 0 (-71011639/250000 : ℚ) vp000000100011101 := by
  apply branch_left_normalized (c:=vp0000001000111010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-71011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-71011639/125000 : ℚ) by norm_num]
  exact coverp0000001000111010
private noncomputable def ep0000001000111011_0 : Blocks := edgeBlocks% "full/vectors/0000001000111011-E-0000.bin"
noncomputable def ep0000001000111011 : Blocks := ep0000001000111011_0
private theorem idp0000001000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100011101.list =
    C ((2:ℤ)^47) * horner X vp0000001000111011.list + horner X ep0000001000111011.list := by
  exact edge_identity (B := (2:ℤ)^161) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001000111011 : Branch 1 (-71011639/250000 : ℚ) vp000000100011101 := by
  apply branch_checked idp0000001000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-71011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-71136639/125000 : ℚ) by norm_num]
  exact coverp0000001000111011
theorem coverp000000100011101 : Covers (-71011639/250000 : ℚ) vp000000100011101 := join_branches bp0000001000111010 bp0000001000111011
private noncomputable def vp000000100011100_0 : Blocks := edgeBlocks% "full/vectors/000000100011100-V-0000.bin"
noncomputable def vp000000100011100 : Blocks := vp000000100011100_0
theorem coverp000000100011100 : Covers (-70761639/250000 : ℚ) vp000000100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010001110_0 : Blocks := edgeBlocks% "full/vectors/00000010001110-V-0000.bin"
noncomputable def vp00000010001110 : Blocks := vp00000010001110_0
private theorem bp000000100011100 : Branch 0 (-70761639/500000 : ℚ) vp00000010001110 := by
  apply branch_left_normalized (c:=vp000000100011100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-70761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-70761639/250000 : ℚ) by norm_num]
  exact coverp000000100011100
private noncomputable def ep000000100011101_0 : Blocks := edgeBlocks% "full/vectors/000000100011101-E-0000.bin"
noncomputable def ep000000100011101 : Blocks := ep000000100011101_0
private theorem idp000000100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010001110.list =
    C ((2:ℤ)^79) * horner X vp000000100011101.list + horner X ep000000100011101.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100011101 : Branch 1 (-70761639/500000 : ℚ) vp00000010001110 := by
  apply branch_checked idp000000100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-70761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-71011639/250000 : ℚ) by norm_num]
  exact coverp000000100011101
theorem coverp00000010001110 : Covers (-70761639/500000 : ℚ) vp00000010001110 := join_branches bp000000100011100 bp000000100011101
private noncomputable def vp0000001000111_0 : Blocks := edgeBlocks% "full/vectors/0000001000111-V-0000.bin"
private noncomputable def vp0000001000111_1 : Blocks := edgeBlocks% "full/vectors/0000001000111-V-0001.bin"
noncomputable def vp0000001000111 : Blocks := (Blocks.join vp0000001000111_0 vp0000001000111_1)
private theorem bp00000010001110 : Branch 0 (-70761639/1000000 : ℚ) vp0000001000111 := by
  apply branch_left_normalized (c:=vp00000010001110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-70761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-70761639/500000 : ℚ) by norm_num]
  exact coverp00000010001110
private noncomputable def ep00000010001111_0 : Blocks := edgeBlocks% "full/vectors/00000010001111-E-0000.bin"
private noncomputable def ep00000010001111_1 : Blocks := edgeBlocks% "full/vectors/00000010001111-E-0001.bin"
noncomputable def ep00000010001111 : Blocks := (Blocks.join ep00000010001111_0 ep00000010001111_1)
private theorem idp00000010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001000111.list =
    C ((2:ℤ)^138) * horner X vp00000010001111.list + horner X ep00000010001111.list := by
  exact edge_identity (B := (2:ℤ)^297) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010001111 : Branch 1 (-70761639/1000000 : ℚ) vp0000001000111 := by
  apply branch_checked idp00000010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-70761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-71261639/500000 : ℚ) by norm_num]
  exact coverp00000010001111
theorem coverp0000001000111 : Covers (-70761639/1000000 : ℚ) vp0000001000111 := join_branches bp00000010001110 bp00000010001111
private noncomputable def vp000000100011011_0 : Blocks := edgeBlocks% "full/vectors/000000100011011-V-0000.bin"
noncomputable def vp000000100011011 : Blocks := vp000000100011011_0
theorem coverp000000100011011 : Covers (-70511639/250000 : ℚ) vp000000100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100011010_0 : Blocks := edgeBlocks% "full/vectors/000000100011010-V-0000.bin"
noncomputable def vp000000100011010 : Blocks := vp000000100011010_0
theorem coverp000000100011010 : Covers (-70261639/250000 : ℚ) vp000000100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010001101_0 : Blocks := edgeBlocks% "full/vectors/00000010001101-V-0000.bin"
noncomputable def vp00000010001101 : Blocks := vp00000010001101_0
private theorem bp000000100011010 : Branch 0 (-70261639/500000 : ℚ) vp00000010001101 := by
  apply branch_left_normalized (c:=vp000000100011010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-70261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-70261639/250000 : ℚ) by norm_num]
  exact coverp000000100011010
private noncomputable def ep000000100011011_0 : Blocks := edgeBlocks% "full/vectors/000000100011011-E-0000.bin"
noncomputable def ep000000100011011 : Blocks := ep000000100011011_0
private theorem idp000000100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010001101.list =
    C ((2:ℤ)^78) * horner X vp000000100011011.list + horner X ep000000100011011.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100011011 : Branch 1 (-70261639/500000 : ℚ) vp00000010001101 := by
  apply branch_checked idp000000100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-70261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-70511639/250000 : ℚ) by norm_num]
  exact coverp000000100011011
theorem coverp00000010001101 : Covers (-70261639/500000 : ℚ) vp00000010001101 := join_branches bp000000100011010 bp000000100011011
private noncomputable def vp000000100011001_0 : Blocks := edgeBlocks% "full/vectors/000000100011001-V-0000.bin"
noncomputable def vp000000100011001 : Blocks := vp000000100011001_0
theorem coverp000000100011001 : Covers (-70011639/250000 : ℚ) vp000000100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100011000_0 : Blocks := edgeBlocks% "full/vectors/000000100011000-V-0000.bin"
noncomputable def vp000000100011000 : Blocks := vp000000100011000_0
theorem coverp000000100011000 : Covers (-69761639/250000 : ℚ) vp000000100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010001100_0 : Blocks := edgeBlocks% "full/vectors/00000010001100-V-0000.bin"
noncomputable def vp00000010001100 : Blocks := vp00000010001100_0
private theorem bp000000100011000 : Branch 0 (-69761639/500000 : ℚ) vp00000010001100 := by
  apply branch_left_normalized (c:=vp000000100011000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-69761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-69761639/250000 : ℚ) by norm_num]
  exact coverp000000100011000
private noncomputable def ep000000100011001_0 : Blocks := edgeBlocks% "full/vectors/000000100011001-E-0000.bin"
noncomputable def ep000000100011001 : Blocks := ep000000100011001_0
private theorem idp000000100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010001100.list =
    C ((2:ℤ)^78) * horner X vp000000100011001.list + horner X ep000000100011001.list := by
  exact edge_identity (B := (2:ℤ)^204) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100011001 : Branch 1 (-69761639/500000 : ℚ) vp00000010001100 := by
  apply branch_checked idp000000100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-69761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-70011639/250000 : ℚ) by norm_num]
  exact coverp000000100011001
theorem coverp00000010001100 : Covers (-69761639/500000 : ℚ) vp00000010001100 := join_branches bp000000100011000 bp000000100011001
private noncomputable def vp0000001000110_0 : Blocks := edgeBlocks% "full/vectors/0000001000110-V-0000.bin"
private noncomputable def vp0000001000110_1 : Blocks := edgeBlocks% "full/vectors/0000001000110-V-0001.bin"
noncomputable def vp0000001000110 : Blocks := (Blocks.join vp0000001000110_0 vp0000001000110_1)
private theorem bp00000010001100 : Branch 0 (-69761639/1000000 : ℚ) vp0000001000110 := by
  apply branch_left_normalized (c:=vp00000010001100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-69761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-69761639/500000 : ℚ) by norm_num]
  exact coverp00000010001100
private noncomputable def ep00000010001101_0 : Blocks := edgeBlocks% "full/vectors/00000010001101-E-0000.bin"
private noncomputable def ep00000010001101_1 : Blocks := edgeBlocks% "full/vectors/00000010001101-E-0001.bin"
noncomputable def ep00000010001101 : Blocks := (Blocks.join ep00000010001101_0 ep00000010001101_1)
private theorem idp00000010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001000110.list =
    C ((2:ℤ)^140) * horner X vp00000010001101.list + horner X ep00000010001101.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010001101 : Branch 1 (-69761639/1000000 : ℚ) vp0000001000110 := by
  apply branch_checked idp00000010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-69761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-70261639/500000 : ℚ) by norm_num]
  exact coverp00000010001101
theorem coverp0000001000110 : Covers (-69761639/1000000 : ℚ) vp0000001000110 := join_branches bp00000010001100 bp00000010001101
private noncomputable def vp000000100011_0 : Blocks := edgeBlocks% "full/vectors/000000100011-V-0000.bin"
private noncomputable def vp000000100011_1 : Blocks := edgeBlocks% "full/vectors/000000100011-V-0001.bin"
noncomputable def vp000000100011 : Blocks := (Blocks.join vp000000100011_0 vp000000100011_1)
private theorem bp0000001000110 : Branch 0 (-69761639/2000000 : ℚ) vp000000100011 := by
  apply branch_left_normalized (c:=vp0000001000110) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-69761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-69761639/1000000 : ℚ) by norm_num]
  exact coverp0000001000110
private noncomputable def ep0000001000111_0 : Blocks := edgeBlocks% "full/vectors/0000001000111-E-0000.bin"
private noncomputable def ep0000001000111_1 : Blocks := edgeBlocks% "full/vectors/0000001000111-E-0001.bin"
noncomputable def ep0000001000111 : Blocks := (Blocks.join ep0000001000111_0 ep0000001000111_1)
private theorem idp0000001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100011.list =
    C ((2:ℤ)^258) * horner X vp0000001000111.list + horner X ep0000001000111.list := by
  exact edge_identity (B := (2:ℤ)^475) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001000111 : Branch 1 (-69761639/2000000 : ℚ) vp000000100011 := by
  apply branch_checked idp0000001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-69761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-70761639/1000000 : ℚ) by norm_num]
  exact coverp0000001000111
theorem coverp000000100011 : Covers (-69761639/2000000 : ℚ) vp000000100011 := join_branches bp0000001000110 bp0000001000111
private noncomputable def vp000000100010111_0 : Blocks := edgeBlocks% "full/vectors/000000100010111-V-0000.bin"
noncomputable def vp000000100010111 : Blocks := vp000000100010111_0
theorem coverp000000100010111 : Covers (-69511639/250000 : ℚ) vp000000100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100010110_0 : Blocks := edgeBlocks% "full/vectors/000000100010110-V-0000.bin"
noncomputable def vp000000100010110 : Blocks := vp000000100010110_0
theorem coverp000000100010110 : Covers (-69261639/250000 : ℚ) vp000000100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010001011_0 : Blocks := edgeBlocks% "full/vectors/00000010001011-V-0000.bin"
noncomputable def vp00000010001011 : Blocks := vp00000010001011_0
private theorem bp000000100010110 : Branch 0 (-69261639/500000 : ℚ) vp00000010001011 := by
  apply branch_left_normalized (c:=vp000000100010110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-69261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-69261639/250000 : ℚ) by norm_num]
  exact coverp000000100010110
private noncomputable def ep000000100010111_0 : Blocks := edgeBlocks% "full/vectors/000000100010111-E-0000.bin"
noncomputable def ep000000100010111 : Blocks := ep000000100010111_0
private theorem idp000000100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010001011.list =
    C ((2:ℤ)^82) * horner X vp000000100010111.list + horner X ep000000100010111.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100010111 : Branch 1 (-69261639/500000 : ℚ) vp00000010001011 := by
  apply branch_checked idp000000100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-69261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-69511639/250000 : ℚ) by norm_num]
  exact coverp000000100010111
theorem coverp00000010001011 : Covers (-69261639/500000 : ℚ) vp00000010001011 := join_branches bp000000100010110 bp000000100010111
private noncomputable def vp000000100010101_0 : Blocks := edgeBlocks% "full/vectors/000000100010101-V-0000.bin"
noncomputable def vp000000100010101 : Blocks := vp000000100010101_0
theorem coverp000000100010101 : Covers (-69011639/250000 : ℚ) vp000000100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010001010011_0 : Blocks := edgeBlocks% "full/vectors/00000010001010011-V-0000.bin"
noncomputable def vp00000010001010011 : Blocks := vp00000010001010011_0
theorem coverp00000010001010011 : Covers (-68949139/62500 : ℚ) vp00000010001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100010100101_0 : Blocks := edgeBlocks% "full/vectors/000000100010100101-V-0000.bin"
noncomputable def vp000000100010100101 : Blocks := vp000000100010100101_0
theorem coverp000000100010100101 : Covers (-68917889/31250 : ℚ) vp000000100010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100010100100_0 : Blocks := edgeBlocks% "full/vectors/000000100010100100-V-0000.bin"
noncomputable def vp000000100010100100 : Blocks := vp000000100010100100_0
theorem coverp000000100010100100 : Covers (-68886639/31250 : ℚ) vp000000100010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010001010010_0 : Blocks := edgeBlocks% "full/vectors/00000010001010010-V-0000.bin"
noncomputable def vp00000010001010010 : Blocks := vp00000010001010010_0
private theorem bp000000100010100100 : Branch 0 (-68886639/62500 : ℚ) vp00000010001010010 := by
  apply branch_left_normalized (c:=vp000000100010100100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-68886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-68886639/31250 : ℚ) by norm_num]
  exact coverp000000100010100100
private noncomputable def ep000000100010100101_0 : Blocks := edgeBlocks% "full/vectors/000000100010100101-E-0000.bin"
noncomputable def ep000000100010100101 : Blocks := ep000000100010100101_0
private theorem idp000000100010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010001010010.list =
    C ((2:ℤ)^22) * horner X vp000000100010100101.list + horner X ep000000100010100101.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100010100101 : Branch 1 (-68886639/62500 : ℚ) vp00000010001010010 := by
  apply branch_checked idp000000100010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-68886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-68917889/31250 : ℚ) by norm_num]
  exact coverp000000100010100101
theorem coverp00000010001010010 : Covers (-68886639/62500 : ℚ) vp00000010001010010 := join_branches bp000000100010100100 bp000000100010100101
private noncomputable def vp0000001000101001_0 : Blocks := edgeBlocks% "full/vectors/0000001000101001-V-0000.bin"
noncomputable def vp0000001000101001 : Blocks := vp0000001000101001_0
private theorem bp00000010001010010 : Branch 0 (-68886639/125000 : ℚ) vp0000001000101001 := by
  apply branch_left_normalized (c:=vp00000010001010010) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-68886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-68886639/62500 : ℚ) by norm_num]
  exact coverp00000010001010010
private noncomputable def ep00000010001010011_0 : Blocks := edgeBlocks% "full/vectors/00000010001010011-E-0000.bin"
noncomputable def ep00000010001010011 : Blocks := ep00000010001010011_0
private theorem idp00000010001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001000101001.list =
    C ((2:ℤ)^33) * horner X vp00000010001010011.list + horner X ep00000010001010011.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010001010011 : Branch 1 (-68886639/125000 : ℚ) vp0000001000101001 := by
  apply branch_checked idp00000010001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-68886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-68949139/62500 : ℚ) by norm_num]
  exact coverp00000010001010011
theorem coverp0000001000101001 : Covers (-68886639/125000 : ℚ) vp0000001000101001 := join_branches bp00000010001010010 bp00000010001010011
private noncomputable def vp0000001000101000_0 : Blocks := edgeBlocks% "full/vectors/0000001000101000-V-0000.bin"
noncomputable def vp0000001000101000 : Blocks := vp0000001000101000_0
theorem coverp0000001000101000 : Covers (-68761639/125000 : ℚ) vp0000001000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100010100_0 : Blocks := edgeBlocks% "full/vectors/000000100010100-V-0000.bin"
noncomputable def vp000000100010100 : Blocks := vp000000100010100_0
private theorem bp0000001000101000 : Branch 0 (-68761639/250000 : ℚ) vp000000100010100 := by
  apply branch_left_normalized (c:=vp0000001000101000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-68761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-68761639/125000 : ℚ) by norm_num]
  exact coverp0000001000101000
private noncomputable def ep0000001000101001_0 : Blocks := edgeBlocks% "full/vectors/0000001000101001-E-0000.bin"
noncomputable def ep0000001000101001 : Blocks := ep0000001000101001_0
private theorem idp0000001000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100010100.list =
    C ((2:ℤ)^48) * horner X vp0000001000101001.list + horner X ep0000001000101001.list := by
  exact edge_identity (B := (2:ℤ)^162) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001000101001 : Branch 1 (-68761639/250000 : ℚ) vp000000100010100 := by
  apply branch_checked idp0000001000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-68761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-68886639/125000 : ℚ) by norm_num]
  exact coverp0000001000101001
theorem coverp000000100010100 : Covers (-68761639/250000 : ℚ) vp000000100010100 := join_branches bp0000001000101000 bp0000001000101001
private noncomputable def vp00000010001010_0 : Blocks := edgeBlocks% "full/vectors/00000010001010-V-0000.bin"
noncomputable def vp00000010001010 : Blocks := vp00000010001010_0
private theorem bp000000100010100 : Branch 0 (-68761639/500000 : ℚ) vp00000010001010 := by
  apply branch_left_normalized (c:=vp000000100010100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-68761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-68761639/250000 : ℚ) by norm_num]
  exact coverp000000100010100
private noncomputable def ep000000100010101_0 : Blocks := edgeBlocks% "full/vectors/000000100010101-E-0000.bin"
noncomputable def ep000000100010101 : Blocks := ep000000100010101_0
private theorem idp000000100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010001010.list =
    C ((2:ℤ)^79) * horner X vp000000100010101.list + horner X ep000000100010101.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100010101 : Branch 1 (-68761639/500000 : ℚ) vp00000010001010 := by
  apply branch_checked idp000000100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-68761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-69011639/250000 : ℚ) by norm_num]
  exact coverp000000100010101
theorem coverp00000010001010 : Covers (-68761639/500000 : ℚ) vp00000010001010 := join_branches bp000000100010100 bp000000100010101
private noncomputable def vp0000001000101_0 : Blocks := edgeBlocks% "full/vectors/0000001000101-V-0000.bin"
private noncomputable def vp0000001000101_1 : Blocks := edgeBlocks% "full/vectors/0000001000101-V-0001.bin"
noncomputable def vp0000001000101 : Blocks := (Blocks.join vp0000001000101_0 vp0000001000101_1)
private theorem bp00000010001010 : Branch 0 (-68761639/1000000 : ℚ) vp0000001000101 := by
  apply branch_left_normalized (c:=vp00000010001010) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-68761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-68761639/500000 : ℚ) by norm_num]
  exact coverp00000010001010
private noncomputable def ep00000010001011_0 : Blocks := edgeBlocks% "full/vectors/00000010001011-E-0000.bin"
private noncomputable def ep00000010001011_1 : Blocks := edgeBlocks% "full/vectors/00000010001011-E-0001.bin"
noncomputable def ep00000010001011 : Blocks := (Blocks.join ep00000010001011_0 ep00000010001011_1)
private theorem idp00000010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001000101.list =
    C ((2:ℤ)^142) * horner X vp00000010001011.list + horner X ep00000010001011.list := by
  exact edge_identity (B := (2:ℤ)^300) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010001011 : Branch 1 (-68761639/1000000 : ℚ) vp0000001000101 := by
  apply branch_checked idp00000010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-68761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-69261639/500000 : ℚ) by norm_num]
  exact coverp00000010001011
theorem coverp0000001000101 : Covers (-68761639/1000000 : ℚ) vp0000001000101 := join_branches bp00000010001010 bp00000010001011
private noncomputable def vp000000100010011_0 : Blocks := edgeBlocks% "full/vectors/000000100010011-V-0000.bin"
noncomputable def vp000000100010011 : Blocks := vp000000100010011_0
theorem coverp000000100010011 : Covers (-68511639/250000 : ℚ) vp000000100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100010010_0 : Blocks := edgeBlocks% "full/vectors/000000100010010-V-0000.bin"
noncomputable def vp000000100010010 : Blocks := vp000000100010010_0
theorem coverp000000100010010 : Covers (-68261639/250000 : ℚ) vp000000100010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010001001_0 : Blocks := edgeBlocks% "full/vectors/00000010001001-V-0000.bin"
noncomputable def vp00000010001001 : Blocks := vp00000010001001_0
private theorem bp000000100010010 : Branch 0 (-68261639/500000 : ℚ) vp00000010001001 := by
  apply branch_left_normalized (c:=vp000000100010010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-68261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-68261639/250000 : ℚ) by norm_num]
  exact coverp000000100010010
private noncomputable def ep000000100010011_0 : Blocks := edgeBlocks% "full/vectors/000000100010011-E-0000.bin"
noncomputable def ep000000100010011 : Blocks := ep000000100010011_0
private theorem idp000000100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010001001.list =
    C ((2:ℤ)^77) * horner X vp000000100010011.list + horner X ep000000100010011.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100010011 : Branch 1 (-68261639/500000 : ℚ) vp00000010001001 := by
  apply branch_checked idp000000100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-68261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-68511639/250000 : ℚ) by norm_num]
  exact coverp000000100010011
theorem coverp00000010001001 : Covers (-68261639/500000 : ℚ) vp00000010001001 := join_branches bp000000100010010 bp000000100010011
private noncomputable def vp000000100010001_0 : Blocks := edgeBlocks% "full/vectors/000000100010001-V-0000.bin"
noncomputable def vp000000100010001 : Blocks := vp000000100010001_0
theorem coverp000000100010001 : Covers (-68011639/250000 : ℚ) vp000000100010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100010000_0 : Blocks := edgeBlocks% "full/vectors/000000100010000-V-0000.bin"
noncomputable def vp000000100010000 : Blocks := vp000000100010000_0
theorem coverp000000100010000 : Covers (-67761639/250000 : ℚ) vp000000100010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010001000_0 : Blocks := edgeBlocks% "full/vectors/00000010001000-V-0000.bin"
noncomputable def vp00000010001000 : Blocks := vp00000010001000_0
private theorem bp000000100010000 : Branch 0 (-67761639/500000 : ℚ) vp00000010001000 := by
  apply branch_left_normalized (c:=vp000000100010000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-67761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-67761639/250000 : ℚ) by norm_num]
  exact coverp000000100010000
private noncomputable def ep000000100010001_0 : Blocks := edgeBlocks% "full/vectors/000000100010001-E-0000.bin"
noncomputable def ep000000100010001 : Blocks := ep000000100010001_0
private theorem idp000000100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010001000.list =
    C ((2:ℤ)^77) * horner X vp000000100010001.list + horner X ep000000100010001.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100010001 : Branch 1 (-67761639/500000 : ℚ) vp00000010001000 := by
  apply branch_checked idp000000100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-67761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-68011639/250000 : ℚ) by norm_num]
  exact coverp000000100010001
theorem coverp00000010001000 : Covers (-67761639/500000 : ℚ) vp00000010001000 := join_branches bp000000100010000 bp000000100010001
private noncomputable def vp0000001000100_0 : Blocks := edgeBlocks% "full/vectors/0000001000100-V-0000.bin"
private noncomputable def vp0000001000100_1 : Blocks := edgeBlocks% "full/vectors/0000001000100-V-0001.bin"
noncomputable def vp0000001000100 : Blocks := (Blocks.join vp0000001000100_0 vp0000001000100_1)
private theorem bp00000010001000 : Branch 0 (-67761639/1000000 : ℚ) vp0000001000100 := by
  apply branch_left_normalized (c:=vp00000010001000) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-67761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-67761639/500000 : ℚ) by norm_num]
  exact coverp00000010001000
private noncomputable def ep00000010001001_0 : Blocks := edgeBlocks% "full/vectors/00000010001001-E-0000.bin"
private noncomputable def ep00000010001001_1 : Blocks := edgeBlocks% "full/vectors/00000010001001-E-0001.bin"
noncomputable def ep00000010001001 : Blocks := (Blocks.join ep00000010001001_0 ep00000010001001_1)
private theorem idp00000010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001000100.list =
    C ((2:ℤ)^138) * horner X vp00000010001001.list + horner X ep00000010001001.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010001001 : Branch 1 (-67761639/1000000 : ℚ) vp0000001000100 := by
  apply branch_checked idp00000010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-67761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-68261639/500000 : ℚ) by norm_num]
  exact coverp00000010001001
theorem coverp0000001000100 : Covers (-67761639/1000000 : ℚ) vp0000001000100 := join_branches bp00000010001000 bp00000010001001
private noncomputable def vp000000100010_0 : Blocks := edgeBlocks% "full/vectors/000000100010-V-0000.bin"
private noncomputable def vp000000100010_1 : Blocks := edgeBlocks% "full/vectors/000000100010-V-0001.bin"
noncomputable def vp000000100010 : Blocks := (Blocks.join vp000000100010_0 vp000000100010_1)
private theorem bp0000001000100 : Branch 0 (-67761639/2000000 : ℚ) vp000000100010 := by
  apply branch_left_normalized (c:=vp0000001000100) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-67761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-67761639/1000000 : ℚ) by norm_num]
  exact coverp0000001000100
private noncomputable def ep0000001000101_0 : Blocks := edgeBlocks% "full/vectors/0000001000101-E-0000.bin"
private noncomputable def ep0000001000101_1 : Blocks := edgeBlocks% "full/vectors/0000001000101-E-0001.bin"
noncomputable def ep0000001000101 : Blocks := (Blocks.join ep0000001000101_0 ep0000001000101_1)
private theorem idp0000001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100010.list =
    C ((2:ℤ)^255) * horner X vp0000001000101.list + horner X ep0000001000101.list := by
  exact edge_identity (B := (2:ℤ)^474) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001000101 : Branch 1 (-67761639/2000000 : ℚ) vp000000100010 := by
  apply branch_checked idp0000001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-67761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-68761639/1000000 : ℚ) by norm_num]
  exact coverp0000001000101
theorem coverp000000100010 : Covers (-67761639/2000000 : ℚ) vp000000100010 := join_branches bp0000001000100 bp0000001000101
private noncomputable def vp00000010001_0 : Blocks := edgeBlocks% "full/vectors/00000010001-V-0000.bin"
private noncomputable def vp00000010001_1 : Blocks := edgeBlocks% "full/vectors/00000010001-V-0001.bin"
private noncomputable def vp00000010001_2 : Blocks := edgeBlocks% "full/vectors/00000010001-V-0002.bin"
private noncomputable def vp00000010001_3 : Blocks := edgeBlocks% "full/vectors/00000010001-V-0003.bin"
noncomputable def vp00000010001 : Blocks := (Blocks.join (Blocks.join vp00000010001_0 vp00000010001_1) (Blocks.join vp00000010001_2 vp00000010001_3))
private theorem bp000000100010 : Branch 0 (-67761639/4000000 : ℚ) vp00000010001 := by
  apply branch_left_normalized (c:=vp000000100010) (k:=0) (m:=254) (by decide +kernel)
  rw [show 2*(-67761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-67761639/2000000 : ℚ) by norm_num]
  exact coverp000000100010
private noncomputable def ep000000100011_0 : Blocks := edgeBlocks% "full/vectors/000000100011-E-0000.bin"
private noncomputable def ep000000100011_1 : Blocks := edgeBlocks% "full/vectors/000000100011-E-0001.bin"
private noncomputable def ep000000100011_2 : Blocks := edgeBlocks% "full/vectors/000000100011-E-0002.bin"
private noncomputable def ep000000100011_3 : Blocks := edgeBlocks% "full/vectors/000000100011-E-0003.bin"
noncomputable def ep000000100011 : Blocks := (Blocks.join (Blocks.join ep000000100011_0 ep000000100011_1) (Blocks.join ep000000100011_2 ep000000100011_3))
private theorem idp000000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010001.list =
    C ((2:ℤ)^500) * horner X vp000000100011.list + horner X ep000000100011.list := by
  exact edge_identity (B := (2:ℤ)^837) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100011 : Branch 1 (-67761639/4000000 : ℚ) vp00000010001 := by
  apply branch_checked idp000000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-67761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-69761639/2000000 : ℚ) by norm_num]
  exact coverp000000100011
theorem coverp00000010001 : Covers (-67761639/4000000 : ℚ) vp00000010001 := join_branches bp000000100010 bp000000100011
private noncomputable def vp000000100001111_0 : Blocks := edgeBlocks% "full/vectors/000000100001111-V-0000.bin"
noncomputable def vp000000100001111 : Blocks := vp000000100001111_0
theorem coverp000000100001111 : Covers (-67511639/250000 : ℚ) vp000000100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100001110_0 : Blocks := edgeBlocks% "full/vectors/000000100001110-V-0000.bin"
noncomputable def vp000000100001110 : Blocks := vp000000100001110_0
theorem coverp000000100001110 : Covers (-67261639/250000 : ℚ) vp000000100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010000111_0 : Blocks := edgeBlocks% "full/vectors/00000010000111-V-0000.bin"
noncomputable def vp00000010000111 : Blocks := vp00000010000111_0
private theorem bp000000100001110 : Branch 0 (-67261639/500000 : ℚ) vp00000010000111 := by
  apply branch_left_normalized (c:=vp000000100001110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-67261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-67261639/250000 : ℚ) by norm_num]
  exact coverp000000100001110
private noncomputable def ep000000100001111_0 : Blocks := edgeBlocks% "full/vectors/000000100001111-E-0000.bin"
noncomputable def ep000000100001111 : Blocks := ep000000100001111_0
private theorem idp000000100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010000111.list =
    C ((2:ℤ)^76) * horner X vp000000100001111.list + horner X ep000000100001111.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100001111 : Branch 1 (-67261639/500000 : ℚ) vp00000010000111 := by
  apply branch_checked idp000000100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-67261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-67511639/250000 : ℚ) by norm_num]
  exact coverp000000100001111
theorem coverp00000010000111 : Covers (-67261639/500000 : ℚ) vp00000010000111 := join_branches bp000000100001110 bp000000100001111
private noncomputable def vp000000100001101_0 : Blocks := edgeBlocks% "full/vectors/000000100001101-V-0000.bin"
noncomputable def vp000000100001101 : Blocks := vp000000100001101_0
theorem coverp000000100001101 : Covers (-67011639/250000 : ℚ) vp000000100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100001100_0 : Blocks := edgeBlocks% "full/vectors/000000100001100-V-0000.bin"
noncomputable def vp000000100001100 : Blocks := vp000000100001100_0
theorem coverp000000100001100 : Covers (-66761639/250000 : ℚ) vp000000100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010000110_0 : Blocks := edgeBlocks% "full/vectors/00000010000110-V-0000.bin"
noncomputable def vp00000010000110 : Blocks := vp00000010000110_0
private theorem bp000000100001100 : Branch 0 (-66761639/500000 : ℚ) vp00000010000110 := by
  apply branch_left_normalized (c:=vp000000100001100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-66761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-66761639/250000 : ℚ) by norm_num]
  exact coverp000000100001100
private noncomputable def ep000000100001101_0 : Blocks := edgeBlocks% "full/vectors/000000100001101-E-0000.bin"
noncomputable def ep000000100001101 : Blocks := ep000000100001101_0
private theorem idp000000100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010000110.list =
    C ((2:ℤ)^77) * horner X vp000000100001101.list + horner X ep000000100001101.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100001101 : Branch 1 (-66761639/500000 : ℚ) vp00000010000110 := by
  apply branch_checked idp000000100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-66761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-67011639/250000 : ℚ) by norm_num]
  exact coverp000000100001101
theorem coverp00000010000110 : Covers (-66761639/500000 : ℚ) vp00000010000110 := join_branches bp000000100001100 bp000000100001101
private noncomputable def vp0000001000011_0 : Blocks := edgeBlocks% "full/vectors/0000001000011-V-0000.bin"
private noncomputable def vp0000001000011_1 : Blocks := edgeBlocks% "full/vectors/0000001000011-V-0001.bin"
noncomputable def vp0000001000011 : Blocks := (Blocks.join vp0000001000011_0 vp0000001000011_1)
private theorem bp00000010000110 : Branch 0 (-66761639/1000000 : ℚ) vp0000001000011 := by
  apply branch_left_normalized (c:=vp00000010000110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-66761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-66761639/500000 : ℚ) by norm_num]
  exact coverp00000010000110
private noncomputable def ep00000010000111_0 : Blocks := edgeBlocks% "full/vectors/00000010000111-E-0000.bin"
private noncomputable def ep00000010000111_1 : Blocks := edgeBlocks% "full/vectors/00000010000111-E-0001.bin"
noncomputable def ep00000010000111 : Blocks := (Blocks.join ep00000010000111_0 ep00000010000111_1)
private theorem idp00000010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001000011.list =
    C ((2:ℤ)^138) * horner X vp00000010000111.list + horner X ep00000010000111.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010000111 : Branch 1 (-66761639/1000000 : ℚ) vp0000001000011 := by
  apply branch_checked idp00000010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-66761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-67261639/500000 : ℚ) by norm_num]
  exact coverp00000010000111
theorem coverp0000001000011 : Covers (-66761639/1000000 : ℚ) vp0000001000011 := join_branches bp00000010000110 bp00000010000111
private noncomputable def vp000000100001011_0 : Blocks := edgeBlocks% "full/vectors/000000100001011-V-0000.bin"
noncomputable def vp000000100001011 : Blocks := vp000000100001011_0
theorem coverp000000100001011 : Covers (-66511639/250000 : ℚ) vp000000100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100001010_0 : Blocks := edgeBlocks% "full/vectors/000000100001010-V-0000.bin"
noncomputable def vp000000100001010 : Blocks := vp000000100001010_0
theorem coverp000000100001010 : Covers (-66261639/250000 : ℚ) vp000000100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010000101_0 : Blocks := edgeBlocks% "full/vectors/00000010000101-V-0000.bin"
noncomputable def vp00000010000101 : Blocks := vp00000010000101_0
private theorem bp000000100001010 : Branch 0 (-66261639/500000 : ℚ) vp00000010000101 := by
  apply branch_left_normalized (c:=vp000000100001010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-66261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-66261639/250000 : ℚ) by norm_num]
  exact coverp000000100001010
private noncomputable def ep000000100001011_0 : Blocks := edgeBlocks% "full/vectors/000000100001011-E-0000.bin"
noncomputable def ep000000100001011 : Blocks := ep000000100001011_0
private theorem idp000000100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010000101.list =
    C ((2:ℤ)^78) * horner X vp000000100001011.list + horner X ep000000100001011.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100001011 : Branch 1 (-66261639/500000 : ℚ) vp00000010000101 := by
  apply branch_checked idp000000100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-66261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-66511639/250000 : ℚ) by norm_num]
  exact coverp000000100001011
theorem coverp00000010000101 : Covers (-66261639/500000 : ℚ) vp00000010000101 := join_branches bp000000100001010 bp000000100001011
private noncomputable def vp000000100001001_0 : Blocks := edgeBlocks% "full/vectors/000000100001001-V-0000.bin"
noncomputable def vp000000100001001 : Blocks := vp000000100001001_0
theorem coverp000000100001001 : Covers (-66011639/250000 : ℚ) vp000000100001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100001000_0 : Blocks := edgeBlocks% "full/vectors/000000100001000-V-0000.bin"
noncomputable def vp000000100001000 : Blocks := vp000000100001000_0
theorem coverp000000100001000 : Covers (-65761639/250000 : ℚ) vp000000100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010000100_0 : Blocks := edgeBlocks% "full/vectors/00000010000100-V-0000.bin"
noncomputable def vp00000010000100 : Blocks := vp00000010000100_0
private theorem bp000000100001000 : Branch 0 (-65761639/500000 : ℚ) vp00000010000100 := by
  apply branch_left_normalized (c:=vp000000100001000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-65761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-65761639/250000 : ℚ) by norm_num]
  exact coverp000000100001000
private noncomputable def ep000000100001001_0 : Blocks := edgeBlocks% "full/vectors/000000100001001-E-0000.bin"
noncomputable def ep000000100001001 : Blocks := ep000000100001001_0
private theorem idp000000100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010000100.list =
    C ((2:ℤ)^77) * horner X vp000000100001001.list + horner X ep000000100001001.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100001001 : Branch 1 (-65761639/500000 : ℚ) vp00000010000100 := by
  apply branch_checked idp000000100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-65761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-66011639/250000 : ℚ) by norm_num]
  exact coverp000000100001001
theorem coverp00000010000100 : Covers (-65761639/500000 : ℚ) vp00000010000100 := join_branches bp000000100001000 bp000000100001001
private noncomputable def vp0000001000010_0 : Blocks := edgeBlocks% "full/vectors/0000001000010-V-0000.bin"
private noncomputable def vp0000001000010_1 : Blocks := edgeBlocks% "full/vectors/0000001000010-V-0001.bin"
noncomputable def vp0000001000010 : Blocks := (Blocks.join vp0000001000010_0 vp0000001000010_1)
private theorem bp00000010000100 : Branch 0 (-65761639/1000000 : ℚ) vp0000001000010 := by
  apply branch_left_normalized (c:=vp00000010000100) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-65761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-65761639/500000 : ℚ) by norm_num]
  exact coverp00000010000100
private noncomputable def ep00000010000101_0 : Blocks := edgeBlocks% "full/vectors/00000010000101-E-0000.bin"
private noncomputable def ep00000010000101_1 : Blocks := edgeBlocks% "full/vectors/00000010000101-E-0001.bin"
noncomputable def ep00000010000101 : Blocks := (Blocks.join ep00000010000101_0 ep00000010000101_1)
private theorem idp00000010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001000010.list =
    C ((2:ℤ)^139) * horner X vp00000010000101.list + horner X ep00000010000101.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010000101 : Branch 1 (-65761639/1000000 : ℚ) vp0000001000010 := by
  apply branch_checked idp00000010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-65761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-66261639/500000 : ℚ) by norm_num]
  exact coverp00000010000101
theorem coverp0000001000010 : Covers (-65761639/1000000 : ℚ) vp0000001000010 := join_branches bp00000010000100 bp00000010000101
private noncomputable def vp000000100001_0 : Blocks := edgeBlocks% "full/vectors/000000100001-V-0000.bin"
private noncomputable def vp000000100001_1 : Blocks := edgeBlocks% "full/vectors/000000100001-V-0001.bin"
private noncomputable def vp000000100001_2 : Blocks := edgeBlocks% "full/vectors/000000100001-V-0002.bin"
noncomputable def vp000000100001 : Blocks := (Blocks.join vp000000100001_0 (Blocks.join vp000000100001_1 vp000000100001_2))
private theorem bp0000001000010 : Branch 0 (-65761639/2000000 : ℚ) vp000000100001 := by
  apply branch_left_normalized (c:=vp0000001000010) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-65761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-65761639/1000000 : ℚ) by norm_num]
  exact coverp0000001000010
private noncomputable def ep0000001000011_0 : Blocks := edgeBlocks% "full/vectors/0000001000011-E-0000.bin"
private noncomputable def ep0000001000011_1 : Blocks := edgeBlocks% "full/vectors/0000001000011-E-0001.bin"
private noncomputable def ep0000001000011_2 : Blocks := edgeBlocks% "full/vectors/0000001000011-E-0002.bin"
noncomputable def ep0000001000011 : Blocks := (Blocks.join ep0000001000011_0 (Blocks.join ep0000001000011_1 ep0000001000011_2))
private theorem idp0000001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100001.list =
    C ((2:ℤ)^262) * horner X vp0000001000011.list + horner X ep0000001000011.list := by
  exact edge_identity (B := (2:ℤ)^475) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001000011 : Branch 1 (-65761639/2000000 : ℚ) vp000000100001 := by
  apply branch_checked idp0000001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-65761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-66761639/1000000 : ℚ) by norm_num]
  exact coverp0000001000011
theorem coverp000000100001 : Covers (-65761639/2000000 : ℚ) vp000000100001 := join_branches bp0000001000010 bp0000001000011
private noncomputable def vp000000100000111_0 : Blocks := edgeBlocks% "full/vectors/000000100000111-V-0000.bin"
noncomputable def vp000000100000111 : Blocks := vp000000100000111_0
theorem coverp000000100000111 : Covers (-65511639/250000 : ℚ) vp000000100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100000110_0 : Blocks := edgeBlocks% "full/vectors/000000100000110-V-0000.bin"
noncomputable def vp000000100000110 : Blocks := vp000000100000110_0
theorem coverp000000100000110 : Covers (-65261639/250000 : ℚ) vp000000100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010000011_0 : Blocks := edgeBlocks% "full/vectors/00000010000011-V-0000.bin"
noncomputable def vp00000010000011 : Blocks := vp00000010000011_0
private theorem bp000000100000110 : Branch 0 (-65261639/500000 : ℚ) vp00000010000011 := by
  apply branch_left_normalized (c:=vp000000100000110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-65261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-65261639/250000 : ℚ) by norm_num]
  exact coverp000000100000110
private noncomputable def ep000000100000111_0 : Blocks := edgeBlocks% "full/vectors/000000100000111-E-0000.bin"
noncomputable def ep000000100000111 : Blocks := ep000000100000111_0
private theorem idp000000100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010000011.list =
    C ((2:ℤ)^78) * horner X vp000000100000111.list + horner X ep000000100000111.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100000111 : Branch 1 (-65261639/500000 : ℚ) vp00000010000011 := by
  apply branch_checked idp000000100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-65261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-65511639/250000 : ℚ) by norm_num]
  exact coverp000000100000111
theorem coverp00000010000011 : Covers (-65261639/500000 : ℚ) vp00000010000011 := join_branches bp000000100000110 bp000000100000111
private noncomputable def vp000000100000101_0 : Blocks := edgeBlocks% "full/vectors/000000100000101-V-0000.bin"
noncomputable def vp000000100000101 : Blocks := vp000000100000101_0
theorem coverp000000100000101 : Covers (-65011639/250000 : ℚ) vp000000100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100000100_0 : Blocks := edgeBlocks% "full/vectors/000000100000100-V-0000.bin"
noncomputable def vp000000100000100 : Blocks := vp000000100000100_0
theorem coverp000000100000100 : Covers (-64761639/250000 : ℚ) vp000000100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010000010_0 : Blocks := edgeBlocks% "full/vectors/00000010000010-V-0000.bin"
noncomputable def vp00000010000010 : Blocks := vp00000010000010_0
private theorem bp000000100000100 : Branch 0 (-64761639/500000 : ℚ) vp00000010000010 := by
  apply branch_left_normalized (c:=vp000000100000100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-64761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-64761639/250000 : ℚ) by norm_num]
  exact coverp000000100000100
private noncomputable def ep000000100000101_0 : Blocks := edgeBlocks% "full/vectors/000000100000101-E-0000.bin"
noncomputable def ep000000100000101 : Blocks := ep000000100000101_0
private theorem idp000000100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010000010.list =
    C ((2:ℤ)^77) * horner X vp000000100000101.list + horner X ep000000100000101.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100000101 : Branch 1 (-64761639/500000 : ℚ) vp00000010000010 := by
  apply branch_checked idp000000100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-64761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-65011639/250000 : ℚ) by norm_num]
  exact coverp000000100000101
theorem coverp00000010000010 : Covers (-64761639/500000 : ℚ) vp00000010000010 := join_branches bp000000100000100 bp000000100000101
private noncomputable def vp0000001000001_0 : Blocks := edgeBlocks% "full/vectors/0000001000001-V-0000.bin"
private noncomputable def vp0000001000001_1 : Blocks := edgeBlocks% "full/vectors/0000001000001-V-0001.bin"
noncomputable def vp0000001000001 : Blocks := (Blocks.join vp0000001000001_0 vp0000001000001_1)
private theorem bp00000010000010 : Branch 0 (-64761639/1000000 : ℚ) vp0000001000001 := by
  apply branch_left_normalized (c:=vp00000010000010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-64761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-64761639/500000 : ℚ) by norm_num]
  exact coverp00000010000010
private noncomputable def ep00000010000011_0 : Blocks := edgeBlocks% "full/vectors/00000010000011-E-0000.bin"
private noncomputable def ep00000010000011_1 : Blocks := edgeBlocks% "full/vectors/00000010000011-E-0001.bin"
noncomputable def ep00000010000011 : Blocks := (Blocks.join ep00000010000011_0 ep00000010000011_1)
private theorem idp00000010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001000001.list =
    C ((2:ℤ)^139) * horner X vp00000010000011.list + horner X ep00000010000011.list := by
  exact edge_identity (B := (2:ℤ)^290) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010000011 : Branch 1 (-64761639/1000000 : ℚ) vp0000001000001 := by
  apply branch_checked idp00000010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-64761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-65261639/500000 : ℚ) by norm_num]
  exact coverp00000010000011
theorem coverp0000001000001 : Covers (-64761639/1000000 : ℚ) vp0000001000001 := join_branches bp00000010000010 bp00000010000011
private noncomputable def vp000000100000011_0 : Blocks := edgeBlocks% "full/vectors/000000100000011-V-0000.bin"
noncomputable def vp000000100000011 : Blocks := vp000000100000011_0
theorem coverp000000100000011 : Covers (-64511639/250000 : ℚ) vp000000100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100000010_0 : Blocks := edgeBlocks% "full/vectors/000000100000010-V-0000.bin"
noncomputable def vp000000100000010 : Blocks := vp000000100000010_0
theorem coverp000000100000010 : Covers (-64261639/250000 : ℚ) vp000000100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010000001_0 : Blocks := edgeBlocks% "full/vectors/00000010000001-V-0000.bin"
noncomputable def vp00000010000001 : Blocks := vp00000010000001_0
private theorem bp000000100000010 : Branch 0 (-64261639/500000 : ℚ) vp00000010000001 := by
  apply branch_left_normalized (c:=vp000000100000010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-64261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-64261639/250000 : ℚ) by norm_num]
  exact coverp000000100000010
private noncomputable def ep000000100000011_0 : Blocks := edgeBlocks% "full/vectors/000000100000011-E-0000.bin"
noncomputable def ep000000100000011 : Blocks := ep000000100000011_0
private theorem idp000000100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010000001.list =
    C ((2:ℤ)^77) * horner X vp000000100000011.list + horner X ep000000100000011.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100000011 : Branch 1 (-64261639/500000 : ℚ) vp00000010000001 := by
  apply branch_checked idp000000100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-64261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-64511639/250000 : ℚ) by norm_num]
  exact coverp000000100000011
theorem coverp00000010000001 : Covers (-64261639/500000 : ℚ) vp00000010000001 := join_branches bp000000100000010 bp000000100000011
private noncomputable def vp000000100000001_0 : Blocks := edgeBlocks% "full/vectors/000000100000001-V-0000.bin"
noncomputable def vp000000100000001 : Blocks := vp000000100000001_0
theorem coverp000000100000001 : Covers (-64011639/250000 : ℚ) vp000000100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000100000000_0 : Blocks := edgeBlocks% "full/vectors/000000100000000-V-0000.bin"
noncomputable def vp000000100000000 : Blocks := vp000000100000000_0
theorem coverp000000100000000 : Covers (-63761639/250000 : ℚ) vp000000100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000010000000_0 : Blocks := edgeBlocks% "full/vectors/00000010000000-V-0000.bin"
noncomputable def vp00000010000000 : Blocks := vp00000010000000_0
private theorem bp000000100000000 : Branch 0 (-63761639/500000 : ℚ) vp00000010000000 := by
  apply branch_left_normalized (c:=vp000000100000000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-63761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-63761639/250000 : ℚ) by norm_num]
  exact coverp000000100000000
private noncomputable def ep000000100000001_0 : Blocks := edgeBlocks% "full/vectors/000000100000001-E-0000.bin"
noncomputable def ep000000100000001 : Blocks := ep000000100000001_0
private theorem idp000000100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010000000.list =
    C ((2:ℤ)^77) * horner X vp000000100000001.list + horner X ep000000100000001.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100000001 : Branch 1 (-63761639/500000 : ℚ) vp00000010000000 := by
  apply branch_checked idp000000100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-63761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-64011639/250000 : ℚ) by norm_num]
  exact coverp000000100000001
theorem coverp00000010000000 : Covers (-63761639/500000 : ℚ) vp00000010000000 := join_branches bp000000100000000 bp000000100000001
private noncomputable def vp0000001000000_0 : Blocks := edgeBlocks% "full/vectors/0000001000000-V-0000.bin"
private noncomputable def vp0000001000000_1 : Blocks := edgeBlocks% "full/vectors/0000001000000-V-0001.bin"
noncomputable def vp0000001000000 : Blocks := (Blocks.join vp0000001000000_0 vp0000001000000_1)
private theorem bp00000010000000 : Branch 0 (-63761639/1000000 : ℚ) vp0000001000000 := by
  apply branch_left_normalized (c:=vp00000010000000) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-63761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-63761639/500000 : ℚ) by norm_num]
  exact coverp00000010000000
private noncomputable def ep00000010000001_0 : Blocks := edgeBlocks% "full/vectors/00000010000001-E-0000.bin"
private noncomputable def ep00000010000001_1 : Blocks := edgeBlocks% "full/vectors/00000010000001-E-0001.bin"
noncomputable def ep00000010000001 : Blocks := (Blocks.join ep00000010000001_0 ep00000010000001_1)
private theorem idp00000010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001000000.list =
    C ((2:ℤ)^141) * horner X vp00000010000001.list + horner X ep00000010000001.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010000001 : Branch 1 (-63761639/1000000 : ℚ) vp0000001000000 := by
  apply branch_checked idp00000010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-63761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-64261639/500000 : ℚ) by norm_num]
  exact coverp00000010000001
theorem coverp0000001000000 : Covers (-63761639/1000000 : ℚ) vp0000001000000 := join_branches bp00000010000000 bp00000010000001
private noncomputable def vp000000100000_0 : Blocks := edgeBlocks% "full/vectors/000000100000-V-0000.bin"
private noncomputable def vp000000100000_1 : Blocks := edgeBlocks% "full/vectors/000000100000-V-0001.bin"
private noncomputable def vp000000100000_2 : Blocks := edgeBlocks% "full/vectors/000000100000-V-0002.bin"
noncomputable def vp000000100000 : Blocks := (Blocks.join vp000000100000_0 (Blocks.join vp000000100000_1 vp000000100000_2))
private theorem bp0000001000000 : Branch 0 (-63761639/2000000 : ℚ) vp000000100000 := by
  apply branch_left_normalized (c:=vp0000001000000) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-63761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-63761639/1000000 : ℚ) by norm_num]
  exact coverp0000001000000
private noncomputable def ep0000001000001_0 : Blocks := edgeBlocks% "full/vectors/0000001000001-E-0000.bin"
private noncomputable def ep0000001000001_1 : Blocks := edgeBlocks% "full/vectors/0000001000001-E-0001.bin"
private noncomputable def ep0000001000001_2 : Blocks := edgeBlocks% "full/vectors/0000001000001-E-0002.bin"
noncomputable def ep0000001000001 : Blocks := (Blocks.join ep0000001000001_0 (Blocks.join ep0000001000001_1 ep0000001000001_2))
private theorem idp0000001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100000.list =
    C ((2:ℤ)^266) * horner X vp0000001000001.list + horner X ep0000001000001.list := by
  exact edge_identity (B := (2:ℤ)^479) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001000001 : Branch 1 (-63761639/2000000 : ℚ) vp000000100000 := by
  apply branch_checked idp0000001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-63761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-64761639/1000000 : ℚ) by norm_num]
  exact coverp0000001000001
theorem coverp000000100000 : Covers (-63761639/2000000 : ℚ) vp000000100000 := join_branches bp0000001000000 bp0000001000001
private noncomputable def vp00000010000_0 : Blocks := edgeBlocks% "full/vectors/00000010000-V-0000.bin"
private noncomputable def vp00000010000_1 : Blocks := edgeBlocks% "full/vectors/00000010000-V-0001.bin"
private noncomputable def vp00000010000_2 : Blocks := edgeBlocks% "full/vectors/00000010000-V-0002.bin"
private noncomputable def vp00000010000_3 : Blocks := edgeBlocks% "full/vectors/00000010000-V-0003.bin"
noncomputable def vp00000010000 : Blocks := (Blocks.join (Blocks.join vp00000010000_0 vp00000010000_1) (Blocks.join vp00000010000_2 vp00000010000_3))
private theorem bp000000100000 : Branch 0 (-63761639/4000000 : ℚ) vp00000010000 := by
  apply branch_left_normalized (c:=vp000000100000) (k:=0) (m:=259) (by decide +kernel)
  rw [show 2*(-63761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-63761639/2000000 : ℚ) by norm_num]
  exact coverp000000100000
private noncomputable def ep000000100001_0 : Blocks := edgeBlocks% "full/vectors/000000100001-E-0000.bin"
private noncomputable def ep000000100001_1 : Blocks := edgeBlocks% "full/vectors/000000100001-E-0001.bin"
private noncomputable def ep000000100001_2 : Blocks := edgeBlocks% "full/vectors/000000100001-E-0002.bin"
private noncomputable def ep000000100001_3 : Blocks := edgeBlocks% "full/vectors/000000100001-E-0003.bin"
noncomputable def ep000000100001 : Blocks := (Blocks.join (Blocks.join ep000000100001_0 ep000000100001_1) (Blocks.join ep000000100001_2 ep000000100001_3))
private theorem idp000000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000010000.list =
    C ((2:ℤ)^514) * horner X vp000000100001.list + horner X ep000000100001.list := by
  exact edge_identity (B := (2:ℤ)^852) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000100001 : Branch 1 (-63761639/4000000 : ℚ) vp00000010000 := by
  apply branch_checked idp000000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-63761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-65761639/2000000 : ℚ) by norm_num]
  exact coverp000000100001
theorem coverp00000010000 : Covers (-63761639/4000000 : ℚ) vp00000010000 := join_branches bp000000100000 bp000000100001
private noncomputable def vp0000001000_0 : Blocks := edgeBlocks% "full/vectors/0000001000-V-0000.bin"
private noncomputable def vp0000001000_1 : Blocks := edgeBlocks% "full/vectors/0000001000-V-0001.bin"
private noncomputable def vp0000001000_2 : Blocks := edgeBlocks% "full/vectors/0000001000-V-0002.bin"
private noncomputable def vp0000001000_3 : Blocks := edgeBlocks% "full/vectors/0000001000-V-0003.bin"
private noncomputable def vp0000001000_4 : Blocks := edgeBlocks% "full/vectors/0000001000-V-0004.bin"
private noncomputable def vp0000001000_5 : Blocks := edgeBlocks% "full/vectors/0000001000-V-0005.bin"
private noncomputable def vp0000001000_6 : Blocks := edgeBlocks% "full/vectors/0000001000-V-0006.bin"
private noncomputable def vp0000001000_7 : Blocks := edgeBlocks% "full/vectors/0000001000-V-0007.bin"
noncomputable def vp0000001000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0000001000_0 vp0000001000_1) (Blocks.join vp0000001000_2 vp0000001000_3)) (Blocks.join (Blocks.join vp0000001000_4 vp0000001000_5) (Blocks.join vp0000001000_6 vp0000001000_7)))
private theorem bp00000010000 : Branch 0 (-63761639/8000000 : ℚ) vp0000001000 := by
  apply branch_left_normalized (c:=vp00000010000) (k:=0) (m:=502) (by decide +kernel)
  rw [show 2*(-63761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-63761639/4000000 : ℚ) by norm_num]
  exact coverp00000010000
private noncomputable def ep00000010001_0 : Blocks := edgeBlocks% "full/vectors/00000010001-E-0000.bin"
private noncomputable def ep00000010001_1 : Blocks := edgeBlocks% "full/vectors/00000010001-E-0001.bin"
private noncomputable def ep00000010001_2 : Blocks := edgeBlocks% "full/vectors/00000010001-E-0002.bin"
private noncomputable def ep00000010001_3 : Blocks := edgeBlocks% "full/vectors/00000010001-E-0003.bin"
private noncomputable def ep00000010001_4 : Blocks := edgeBlocks% "full/vectors/00000010001-E-0004.bin"
private noncomputable def ep00000010001_5 : Blocks := edgeBlocks% "full/vectors/00000010001-E-0005.bin"
private noncomputable def ep00000010001_6 : Blocks := edgeBlocks% "full/vectors/00000010001-E-0006.bin"
private noncomputable def ep00000010001_7 : Blocks := edgeBlocks% "full/vectors/00000010001-E-0007.bin"
noncomputable def ep00000010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00000010001_0 ep00000010001_1) (Blocks.join ep00000010001_2 ep00000010001_3)) (Blocks.join (Blocks.join ep00000010001_4 ep00000010001_5) (Blocks.join ep00000010001_6 ep00000010001_7)))
private theorem idp00000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000001000.list =
    C ((2:ℤ)^1003) * horner X vp00000010001.list + horner X ep00000010001.list := by
  exact edge_identity (B := (2:ℤ)^1592) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000010001 : Branch 1 (-63761639/8000000 : ℚ) vp0000001000 := by
  apply branch_checked idp00000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-63761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-67761639/4000000 : ℚ) by norm_num]
  exact coverp00000010001
theorem coverp0000001000 : Covers (-63761639/8000000 : ℚ) vp0000001000 := join_branches bp00000010000 bp00000010001
private noncomputable def vp000000100_0 : Blocks := edgeBlocks% "full/vectors/000000100-V-0000.bin"
private noncomputable def vp000000100_1 : Blocks := edgeBlocks% "full/vectors/000000100-V-0001.bin"
private noncomputable def vp000000100_2 : Blocks := edgeBlocks% "full/vectors/000000100-V-0002.bin"
private noncomputable def vp000000100_3 : Blocks := edgeBlocks% "full/vectors/000000100-V-0003.bin"
private noncomputable def vp000000100_4 : Blocks := edgeBlocks% "full/vectors/000000100-V-0004.bin"
private noncomputable def vp000000100_5 : Blocks := edgeBlocks% "full/vectors/000000100-V-0005.bin"
private noncomputable def vp000000100_6 : Blocks := edgeBlocks% "full/vectors/000000100-V-0006.bin"
private noncomputable def vp000000100_7 : Blocks := edgeBlocks% "full/vectors/000000100-V-0007.bin"
private noncomputable def vp000000100_8 : Blocks := edgeBlocks% "full/vectors/000000100-V-0008.bin"
private noncomputable def vp000000100_9 : Blocks := edgeBlocks% "full/vectors/000000100-V-0009.bin"
private noncomputable def vp000000100_10 : Blocks := edgeBlocks% "full/vectors/000000100-V-0010.bin"
private noncomputable def vp000000100_11 : Blocks := edgeBlocks% "full/vectors/000000100-V-0011.bin"
private noncomputable def vp000000100_12 : Blocks := edgeBlocks% "full/vectors/000000100-V-0012.bin"
private noncomputable def vp000000100_13 : Blocks := edgeBlocks% "full/vectors/000000100-V-0013.bin"
private noncomputable def vp000000100_14 : Blocks := edgeBlocks% "full/vectors/000000100-V-0014.bin"
private noncomputable def vp000000100_15 : Blocks := edgeBlocks% "full/vectors/000000100-V-0015.bin"
noncomputable def vp000000100 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp000000100_0 vp000000100_1) (Blocks.join vp000000100_2 vp000000100_3)) (Blocks.join (Blocks.join vp000000100_4 vp000000100_5) (Blocks.join vp000000100_6 vp000000100_7))) (Blocks.join (Blocks.join (Blocks.join vp000000100_8 vp000000100_9) (Blocks.join vp000000100_10 vp000000100_11)) (Blocks.join (Blocks.join vp000000100_12 vp000000100_13) (Blocks.join vp000000100_14 vp000000100_15))))
private theorem bp0000001000 : Branch 0 (-63761639/16000000 : ℚ) vp000000100 := by
  apply branch_left_normalized (c:=vp0000001000) (k:=0) (m:=983) (by decide +kernel)
  rw [show 2*(-63761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-63761639/8000000 : ℚ) by norm_num]
  exact coverp0000001000
private noncomputable def ep0000001001_0 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0000.bin"
private noncomputable def ep0000001001_1 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0001.bin"
private noncomputable def ep0000001001_2 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0002.bin"
private noncomputable def ep0000001001_3 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0003.bin"
private noncomputable def ep0000001001_4 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0004.bin"
private noncomputable def ep0000001001_5 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0005.bin"
private noncomputable def ep0000001001_6 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0006.bin"
private noncomputable def ep0000001001_7 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0007.bin"
private noncomputable def ep0000001001_8 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0008.bin"
private noncomputable def ep0000001001_9 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0009.bin"
private noncomputable def ep0000001001_10 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0010.bin"
private noncomputable def ep0000001001_11 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0011.bin"
private noncomputable def ep0000001001_12 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0012.bin"
private noncomputable def ep0000001001_13 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0013.bin"
private noncomputable def ep0000001001_14 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0014.bin"
private noncomputable def ep0000001001_15 : Blocks := edgeBlocks% "full/vectors/0000001001-E-0015.bin"
noncomputable def ep0000001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0000001001_0 ep0000001001_1) (Blocks.join ep0000001001_2 ep0000001001_3)) (Blocks.join (Blocks.join ep0000001001_4 ep0000001001_5) (Blocks.join ep0000001001_6 ep0000001001_7))) (Blocks.join (Blocks.join (Blocks.join ep0000001001_8 ep0000001001_9) (Blocks.join ep0000001001_10 ep0000001001_11)) (Blocks.join (Blocks.join ep0000001001_12 ep0000001001_13) (Blocks.join ep0000001001_14 ep0000001001_15))))
private theorem idp0000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000100.list =
    C ((2:ℤ)^1957) * horner X vp0000001001.list + horner X ep0000001001.list := by
  exact edge_identity (B := (2:ℤ)^3046) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000001001 : Branch 1 (-63761639/16000000 : ℚ) vp000000100 := by
  apply branch_checked idp0000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-63761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-71761639/8000000 : ℚ) by norm_num]
  exact coverp0000001001
theorem coverp000000100 : Covers (-63761639/16000000 : ℚ) vp000000100 := join_branches bp0000001000 bp0000001001
end NextProof.EdgeFull

