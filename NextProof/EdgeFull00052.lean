import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00051

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000010000111111_0 : Blocks := edgeBlocks% "full/vectors/000010000111111-V-0000.bin"
noncomputable def vp000010000111111 : Blocks := vp000010000111111_0
theorem coverp000010000111111 : Covers (-271511639/250000 : ℚ) vp000010000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000010000111110_0 : Blocks := edgeBlocks% "full/vectors/000010000111110-V-0000.bin"
noncomputable def vp000010000111110 : Blocks := vp000010000111110_0
theorem coverp000010000111110 : Covers (-271261639/250000 : ℚ) vp000010000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000011111_0 : Blocks := edgeBlocks% "full/vectors/00001000011111-V-0000.bin"
noncomputable def vp00001000011111 : Blocks := vp00001000011111_0
private theorem bp000010000111110 : Branch 0 (-271261639/500000 : ℚ) vp00001000011111 := by
  apply branch_left_normalized (c:=vp000010000111110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-271261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-271261639/250000 : ℚ) by norm_num]
  exact coverp000010000111110
private noncomputable def ep000010000111111_0 : Blocks := edgeBlocks% "full/vectors/000010000111111-E-0000.bin"
noncomputable def ep000010000111111 : Blocks := ep000010000111111_0
private theorem idp000010000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000011111.list =
    C ((2:ℤ)^51) * horner X vp000010000111111.list + horner X ep000010000111111.list := by
  exact edge_identity (B := (2:ℤ)^168) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010000111111 : Branch 1 (-271261639/500000 : ℚ) vp00001000011111 := by
  apply branch_checked idp000010000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-271261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-271511639/250000 : ℚ) by norm_num]
  exact coverp000010000111111
theorem coverp00001000011111 : Covers (-271261639/500000 : ℚ) vp00001000011111 := join_branches bp000010000111110 bp000010000111111
private noncomputable def vp000010000111101_0 : Blocks := edgeBlocks% "full/vectors/000010000111101-V-0000.bin"
noncomputable def vp000010000111101 : Blocks := vp000010000111101_0
theorem coverp000010000111101 : Covers (-271011639/250000 : ℚ) vp000010000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000010000111100_0 : Blocks := edgeBlocks% "full/vectors/000010000111100-V-0000.bin"
noncomputable def vp000010000111100 : Blocks := vp000010000111100_0
theorem coverp000010000111100 : Covers (-270761639/250000 : ℚ) vp000010000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000011110_0 : Blocks := edgeBlocks% "full/vectors/00001000011110-V-0000.bin"
noncomputable def vp00001000011110 : Blocks := vp00001000011110_0
private theorem bp000010000111100 : Branch 0 (-270761639/500000 : ℚ) vp00001000011110 := by
  apply branch_left_normalized (c:=vp000010000111100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-270761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-270761639/250000 : ℚ) by norm_num]
  exact coverp000010000111100
private noncomputable def ep000010000111101_0 : Blocks := edgeBlocks% "full/vectors/000010000111101-E-0000.bin"
noncomputable def ep000010000111101 : Blocks := ep000010000111101_0
private theorem idp000010000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000011110.list =
    C ((2:ℤ)^49) * horner X vp000010000111101.list + horner X ep000010000111101.list := by
  exact edge_identity (B := (2:ℤ)^166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010000111101 : Branch 1 (-270761639/500000 : ℚ) vp00001000011110 := by
  apply branch_checked idp000010000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-270761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-271011639/250000 : ℚ) by norm_num]
  exact coverp000010000111101
theorem coverp00001000011110 : Covers (-270761639/500000 : ℚ) vp00001000011110 := join_branches bp000010000111100 bp000010000111101
private noncomputable def vp0000100001111_0 : Blocks := edgeBlocks% "full/vectors/0000100001111-V-0000.bin"
noncomputable def vp0000100001111 : Blocks := vp0000100001111_0
private theorem bp00001000011110 : Branch 0 (-270761639/1000000 : ℚ) vp0000100001111 := by
  apply branch_left_normalized (c:=vp00001000011110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-270761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-270761639/500000 : ℚ) by norm_num]
  exact coverp00001000011110
private noncomputable def ep00001000011111_0 : Blocks := edgeBlocks% "full/vectors/00001000011111-E-0000.bin"
noncomputable def ep00001000011111 : Blocks := ep00001000011111_0
private theorem idp00001000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100001111.list =
    C ((2:ℤ)^83) * horner X vp00001000011111.list + horner X ep00001000011111.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000011111 : Branch 1 (-270761639/1000000 : ℚ) vp0000100001111 := by
  apply branch_checked idp00001000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-270761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-271261639/500000 : ℚ) by norm_num]
  exact coverp00001000011111
theorem coverp0000100001111 : Covers (-270761639/1000000 : ℚ) vp0000100001111 := join_branches bp00001000011110 bp00001000011111
private noncomputable def vp000010000111011_0 : Blocks := edgeBlocks% "full/vectors/000010000111011-V-0000.bin"
noncomputable def vp000010000111011 : Blocks := vp000010000111011_0
theorem coverp000010000111011 : Covers (-270511639/250000 : ℚ) vp000010000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000010000111010_0 : Blocks := edgeBlocks% "full/vectors/000010000111010-V-0000.bin"
noncomputable def vp000010000111010 : Blocks := vp000010000111010_0
theorem coverp000010000111010 : Covers (-270261639/250000 : ℚ) vp000010000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000011101_0 : Blocks := edgeBlocks% "full/vectors/00001000011101-V-0000.bin"
noncomputable def vp00001000011101 : Blocks := vp00001000011101_0
private theorem bp000010000111010 : Branch 0 (-270261639/500000 : ℚ) vp00001000011101 := by
  apply branch_left_normalized (c:=vp000010000111010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-270261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-270261639/250000 : ℚ) by norm_num]
  exact coverp000010000111010
private noncomputable def ep000010000111011_0 : Blocks := edgeBlocks% "full/vectors/000010000111011-E-0000.bin"
noncomputable def ep000010000111011 : Blocks := ep000010000111011_0
private theorem idp000010000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000011101.list =
    C ((2:ℤ)^49) * horner X vp000010000111011.list + horner X ep000010000111011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010000111011 : Branch 1 (-270261639/500000 : ℚ) vp00001000011101 := by
  apply branch_checked idp000010000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-270261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-270511639/250000 : ℚ) by norm_num]
  exact coverp000010000111011
theorem coverp00001000011101 : Covers (-270261639/500000 : ℚ) vp00001000011101 := join_branches bp000010000111010 bp000010000111011
private noncomputable def vp00001000011100_0 : Blocks := edgeBlocks% "full/vectors/00001000011100-V-0000.bin"
noncomputable def vp00001000011100 : Blocks := vp00001000011100_0
theorem coverp00001000011100 : Covers (-269761639/500000 : ℚ) vp00001000011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100001110_0 : Blocks := edgeBlocks% "full/vectors/0000100001110-V-0000.bin"
noncomputable def vp0000100001110 : Blocks := vp0000100001110_0
private theorem bp00001000011100 : Branch 0 (-269761639/1000000 : ℚ) vp0000100001110 := by
  apply branch_left_normalized (c:=vp00001000011100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-269761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-269761639/500000 : ℚ) by norm_num]
  exact coverp00001000011100
private noncomputable def ep00001000011101_0 : Blocks := edgeBlocks% "full/vectors/00001000011101-E-0000.bin"
noncomputable def ep00001000011101 : Blocks := ep00001000011101_0
private theorem idp00001000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100001110.list =
    C ((2:ℤ)^82) * horner X vp00001000011101.list + horner X ep00001000011101.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000011101 : Branch 1 (-269761639/1000000 : ℚ) vp0000100001110 := by
  apply branch_checked idp00001000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-269761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-270261639/500000 : ℚ) by norm_num]
  exact coverp00001000011101
theorem coverp0000100001110 : Covers (-269761639/1000000 : ℚ) vp0000100001110 := join_branches bp00001000011100 bp00001000011101
private noncomputable def vp000010000111_0 : Blocks := edgeBlocks% "full/vectors/000010000111-V-0000.bin"
private noncomputable def vp000010000111_1 : Blocks := edgeBlocks% "full/vectors/000010000111-V-0001.bin"
noncomputable def vp000010000111 : Blocks := (Blocks.join vp000010000111_0 vp000010000111_1)
private theorem bp0000100001110 : Branch 0 (-269761639/2000000 : ℚ) vp000010000111 := by
  apply branch_left_normalized (c:=vp0000100001110) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-269761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-269761639/1000000 : ℚ) by norm_num]
  exact coverp0000100001110
private noncomputable def ep0000100001111_0 : Blocks := edgeBlocks% "full/vectors/0000100001111-E-0000.bin"
private noncomputable def ep0000100001111_1 : Blocks := edgeBlocks% "full/vectors/0000100001111-E-0001.bin"
noncomputable def ep0000100001111 : Blocks := (Blocks.join ep0000100001111_0 ep0000100001111_1)
private theorem idp0000100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010000111.list =
    C ((2:ℤ)^144) * horner X vp0000100001111.list + horner X ep0000100001111.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100001111 : Branch 1 (-269761639/2000000 : ℚ) vp000010000111 := by
  apply branch_checked idp0000100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-269761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-270761639/1000000 : ℚ) by norm_num]
  exact coverp0000100001111
theorem coverp000010000111 : Covers (-269761639/2000000 : ℚ) vp000010000111 := join_branches bp0000100001110 bp0000100001111
private noncomputable def vp00001000011011_0 : Blocks := edgeBlocks% "full/vectors/00001000011011-V-0000.bin"
noncomputable def vp00001000011011 : Blocks := vp00001000011011_0
theorem coverp00001000011011 : Covers (-269261639/500000 : ℚ) vp00001000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000011010_0 : Blocks := edgeBlocks% "full/vectors/00001000011010-V-0000.bin"
noncomputable def vp00001000011010 : Blocks := vp00001000011010_0
theorem coverp00001000011010 : Covers (-268761639/500000 : ℚ) vp00001000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100001101_0 : Blocks := edgeBlocks% "full/vectors/0000100001101-V-0000.bin"
noncomputable def vp0000100001101 : Blocks := vp0000100001101_0
private theorem bp00001000011010 : Branch 0 (-268761639/1000000 : ℚ) vp0000100001101 := by
  apply branch_left_normalized (c:=vp00001000011010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-268761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-268761639/500000 : ℚ) by norm_num]
  exact coverp00001000011010
private noncomputable def ep00001000011011_0 : Blocks := edgeBlocks% "full/vectors/00001000011011-E-0000.bin"
noncomputable def ep00001000011011 : Blocks := ep00001000011011_0
private theorem idp00001000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100001101.list =
    C ((2:ℤ)^79) * horner X vp00001000011011.list + horner X ep00001000011011.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000011011 : Branch 1 (-268761639/1000000 : ℚ) vp0000100001101 := by
  apply branch_checked idp00001000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-268761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-269261639/500000 : ℚ) by norm_num]
  exact coverp00001000011011
theorem coverp0000100001101 : Covers (-268761639/1000000 : ℚ) vp0000100001101 := join_branches bp00001000011010 bp00001000011011
private noncomputable def vp00001000011001_0 : Blocks := edgeBlocks% "full/vectors/00001000011001-V-0000.bin"
noncomputable def vp00001000011001 : Blocks := vp00001000011001_0
theorem coverp00001000011001 : Covers (-268261639/500000 : ℚ) vp00001000011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000011000_0 : Blocks := edgeBlocks% "full/vectors/00001000011000-V-0000.bin"
noncomputable def vp00001000011000 : Blocks := vp00001000011000_0
theorem coverp00001000011000 : Covers (-267761639/500000 : ℚ) vp00001000011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100001100_0 : Blocks := edgeBlocks% "full/vectors/0000100001100-V-0000.bin"
noncomputable def vp0000100001100 : Blocks := vp0000100001100_0
private theorem bp00001000011000 : Branch 0 (-267761639/1000000 : ℚ) vp0000100001100 := by
  apply branch_left_normalized (c:=vp00001000011000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-267761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-267761639/500000 : ℚ) by norm_num]
  exact coverp00001000011000
private noncomputable def ep00001000011001_0 : Blocks := edgeBlocks% "full/vectors/00001000011001-E-0000.bin"
noncomputable def ep00001000011001 : Blocks := ep00001000011001_0
private theorem idp00001000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100001100.list =
    C ((2:ℤ)^80) * horner X vp00001000011001.list + horner X ep00001000011001.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000011001 : Branch 1 (-267761639/1000000 : ℚ) vp0000100001100 := by
  apply branch_checked idp00001000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-267761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-268261639/500000 : ℚ) by norm_num]
  exact coverp00001000011001
theorem coverp0000100001100 : Covers (-267761639/1000000 : ℚ) vp0000100001100 := join_branches bp00001000011000 bp00001000011001
private noncomputable def vp000010000110_0 : Blocks := edgeBlocks% "full/vectors/000010000110-V-0000.bin"
private noncomputable def vp000010000110_1 : Blocks := edgeBlocks% "full/vectors/000010000110-V-0001.bin"
noncomputable def vp000010000110 : Blocks := (Blocks.join vp000010000110_0 vp000010000110_1)
private theorem bp0000100001100 : Branch 0 (-267761639/2000000 : ℚ) vp000010000110 := by
  apply branch_left_normalized (c:=vp0000100001100) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-267761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-267761639/1000000 : ℚ) by norm_num]
  exact coverp0000100001100
private noncomputable def ep0000100001101_0 : Blocks := edgeBlocks% "full/vectors/0000100001101-E-0000.bin"
private noncomputable def ep0000100001101_1 : Blocks := edgeBlocks% "full/vectors/0000100001101-E-0001.bin"
noncomputable def ep0000100001101 : Blocks := (Blocks.join ep0000100001101_0 ep0000100001101_1)
private theorem idp0000100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010000110.list =
    C ((2:ℤ)^144) * horner X vp0000100001101.list + horner X ep0000100001101.list := by
  exact edge_identity (B := (2:ℤ)^298) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100001101 : Branch 1 (-267761639/2000000 : ℚ) vp000010000110 := by
  apply branch_checked idp0000100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-267761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-268761639/1000000 : ℚ) by norm_num]
  exact coverp0000100001101
theorem coverp000010000110 : Covers (-267761639/2000000 : ℚ) vp000010000110 := join_branches bp0000100001100 bp0000100001101
private noncomputable def vp00001000011_0 : Blocks := edgeBlocks% "full/vectors/00001000011-V-0000.bin"
private noncomputable def vp00001000011_1 : Blocks := edgeBlocks% "full/vectors/00001000011-V-0001.bin"
private noncomputable def vp00001000011_2 : Blocks := edgeBlocks% "full/vectors/00001000011-V-0002.bin"
noncomputable def vp00001000011 : Blocks := (Blocks.join vp00001000011_0 (Blocks.join vp00001000011_1 vp00001000011_2))
private theorem bp000010000110 : Branch 0 (-267761639/4000000 : ℚ) vp00001000011 := by
  apply branch_left_normalized (c:=vp000010000110) (k:=0) (m:=138) (by decide +kernel)
  rw [show 2*(-267761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-267761639/2000000 : ℚ) by norm_num]
  exact coverp000010000110
private noncomputable def ep000010000111_0 : Blocks := edgeBlocks% "full/vectors/000010000111-E-0000.bin"
private noncomputable def ep000010000111_1 : Blocks := edgeBlocks% "full/vectors/000010000111-E-0001.bin"
private noncomputable def ep000010000111_2 : Blocks := edgeBlocks% "full/vectors/000010000111-E-0002.bin"
noncomputable def ep000010000111 : Blocks := (Blocks.join ep000010000111_0 (Blocks.join ep000010000111_1 ep000010000111_2))
private theorem idp000010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000011.list =
    C ((2:ℤ)^267) * horner X vp000010000111.list + horner X ep000010000111.list := by
  exact edge_identity (B := (2:ℤ)^481) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010000111 : Branch 1 (-267761639/4000000 : ℚ) vp00001000011 := by
  apply branch_checked idp000010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-267761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-269761639/2000000 : ℚ) by norm_num]
  exact coverp000010000111
theorem coverp00001000011 : Covers (-267761639/4000000 : ℚ) vp00001000011 := join_branches bp000010000110 bp000010000111
private noncomputable def vp00001000010111_0 : Blocks := edgeBlocks% "full/vectors/00001000010111-V-0000.bin"
noncomputable def vp00001000010111 : Blocks := vp00001000010111_0
theorem coverp00001000010111 : Covers (-267261639/500000 : ℚ) vp00001000010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000010110_0 : Blocks := edgeBlocks% "full/vectors/00001000010110-V-0000.bin"
noncomputable def vp00001000010110 : Blocks := vp00001000010110_0
theorem coverp00001000010110 : Covers (-266761639/500000 : ℚ) vp00001000010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100001011_0 : Blocks := edgeBlocks% "full/vectors/0000100001011-V-0000.bin"
noncomputable def vp0000100001011 : Blocks := vp0000100001011_0
private theorem bp00001000010110 : Branch 0 (-266761639/1000000 : ℚ) vp0000100001011 := by
  apply branch_left_normalized (c:=vp00001000010110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-266761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-266761639/500000 : ℚ) by norm_num]
  exact coverp00001000010110
private noncomputable def ep00001000010111_0 : Blocks := edgeBlocks% "full/vectors/00001000010111-E-0000.bin"
noncomputable def ep00001000010111 : Blocks := ep00001000010111_0
private theorem idp00001000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100001011.list =
    C ((2:ℤ)^79) * horner X vp00001000010111.list + horner X ep00001000010111.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000010111 : Branch 1 (-266761639/1000000 : ℚ) vp0000100001011 := by
  apply branch_checked idp00001000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-266761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-267261639/500000 : ℚ) by norm_num]
  exact coverp00001000010111
theorem coverp0000100001011 : Covers (-266761639/1000000 : ℚ) vp0000100001011 := join_branches bp00001000010110 bp00001000010111
private noncomputable def vp00001000010101_0 : Blocks := edgeBlocks% "full/vectors/00001000010101-V-0000.bin"
noncomputable def vp00001000010101 : Blocks := vp00001000010101_0
theorem coverp00001000010101 : Covers (-266261639/500000 : ℚ) vp00001000010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000010100_0 : Blocks := edgeBlocks% "full/vectors/00001000010100-V-0000.bin"
noncomputable def vp00001000010100 : Blocks := vp00001000010100_0
theorem coverp00001000010100 : Covers (-265761639/500000 : ℚ) vp00001000010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100001010_0 : Blocks := edgeBlocks% "full/vectors/0000100001010-V-0000.bin"
noncomputable def vp0000100001010 : Blocks := vp0000100001010_0
private theorem bp00001000010100 : Branch 0 (-265761639/1000000 : ℚ) vp0000100001010 := by
  apply branch_left_normalized (c:=vp00001000010100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-265761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-265761639/500000 : ℚ) by norm_num]
  exact coverp00001000010100
private noncomputable def ep00001000010101_0 : Blocks := edgeBlocks% "full/vectors/00001000010101-E-0000.bin"
noncomputable def ep00001000010101 : Blocks := ep00001000010101_0
private theorem idp00001000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100001010.list =
    C ((2:ℤ)^79) * horner X vp00001000010101.list + horner X ep00001000010101.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000010101 : Branch 1 (-265761639/1000000 : ℚ) vp0000100001010 := by
  apply branch_checked idp00001000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-265761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-266261639/500000 : ℚ) by norm_num]
  exact coverp00001000010101
theorem coverp0000100001010 : Covers (-265761639/1000000 : ℚ) vp0000100001010 := join_branches bp00001000010100 bp00001000010101
private noncomputable def vp000010000101_0 : Blocks := edgeBlocks% "full/vectors/000010000101-V-0000.bin"
private noncomputable def vp000010000101_1 : Blocks := edgeBlocks% "full/vectors/000010000101-V-0001.bin"
noncomputable def vp000010000101 : Blocks := (Blocks.join vp000010000101_0 vp000010000101_1)
private theorem bp0000100001010 : Branch 0 (-265761639/2000000 : ℚ) vp000010000101 := by
  apply branch_left_normalized (c:=vp0000100001010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-265761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-265761639/1000000 : ℚ) by norm_num]
  exact coverp0000100001010
private noncomputable def ep0000100001011_0 : Blocks := edgeBlocks% "full/vectors/0000100001011-E-0000.bin"
private noncomputable def ep0000100001011_1 : Blocks := edgeBlocks% "full/vectors/0000100001011-E-0001.bin"
noncomputable def ep0000100001011 : Blocks := (Blocks.join ep0000100001011_0 ep0000100001011_1)
private theorem idp0000100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010000101.list =
    C ((2:ℤ)^143) * horner X vp0000100001011.list + horner X ep0000100001011.list := by
  exact edge_identity (B := (2:ℤ)^294) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100001011 : Branch 1 (-265761639/2000000 : ℚ) vp000010000101 := by
  apply branch_checked idp0000100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-265761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-266761639/1000000 : ℚ) by norm_num]
  exact coverp0000100001011
theorem coverp000010000101 : Covers (-265761639/2000000 : ℚ) vp000010000101 := join_branches bp0000100001010 bp0000100001011
private noncomputable def vp00001000010011_0 : Blocks := edgeBlocks% "full/vectors/00001000010011-V-0000.bin"
noncomputable def vp00001000010011 : Blocks := vp00001000010011_0
theorem coverp00001000010011 : Covers (-265261639/500000 : ℚ) vp00001000010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000010010_0 : Blocks := edgeBlocks% "full/vectors/00001000010010-V-0000.bin"
noncomputable def vp00001000010010 : Blocks := vp00001000010010_0
theorem coverp00001000010010 : Covers (-264761639/500000 : ℚ) vp00001000010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100001001_0 : Blocks := edgeBlocks% "full/vectors/0000100001001-V-0000.bin"
noncomputable def vp0000100001001 : Blocks := vp0000100001001_0
private theorem bp00001000010010 : Branch 0 (-264761639/1000000 : ℚ) vp0000100001001 := by
  apply branch_left_normalized (c:=vp00001000010010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-264761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-264761639/500000 : ℚ) by norm_num]
  exact coverp00001000010010
private noncomputable def ep00001000010011_0 : Blocks := edgeBlocks% "full/vectors/00001000010011-E-0000.bin"
noncomputable def ep00001000010011 : Blocks := ep00001000010011_0
private theorem idp00001000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100001001.list =
    C ((2:ℤ)^79) * horner X vp00001000010011.list + horner X ep00001000010011.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000010011 : Branch 1 (-264761639/1000000 : ℚ) vp0000100001001 := by
  apply branch_checked idp00001000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-264761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-265261639/500000 : ℚ) by norm_num]
  exact coverp00001000010011
theorem coverp0000100001001 : Covers (-264761639/1000000 : ℚ) vp0000100001001 := join_branches bp00001000010010 bp00001000010011
private noncomputable def vp00001000010001_0 : Blocks := edgeBlocks% "full/vectors/00001000010001-V-0000.bin"
noncomputable def vp00001000010001 : Blocks := vp00001000010001_0
theorem coverp00001000010001 : Covers (-264261639/500000 : ℚ) vp00001000010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000010000_0 : Blocks := edgeBlocks% "full/vectors/00001000010000-V-0000.bin"
noncomputable def vp00001000010000 : Blocks := vp00001000010000_0
theorem coverp00001000010000 : Covers (-263761639/500000 : ℚ) vp00001000010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100001000_0 : Blocks := edgeBlocks% "full/vectors/0000100001000-V-0000.bin"
noncomputable def vp0000100001000 : Blocks := vp0000100001000_0
private theorem bp00001000010000 : Branch 0 (-263761639/1000000 : ℚ) vp0000100001000 := by
  apply branch_left_normalized (c:=vp00001000010000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-263761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-263761639/500000 : ℚ) by norm_num]
  exact coverp00001000010000
private noncomputable def ep00001000010001_0 : Blocks := edgeBlocks% "full/vectors/00001000010001-E-0000.bin"
noncomputable def ep00001000010001 : Blocks := ep00001000010001_0
private theorem idp00001000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100001000.list =
    C ((2:ℤ)^79) * horner X vp00001000010001.list + horner X ep00001000010001.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000010001 : Branch 1 (-263761639/1000000 : ℚ) vp0000100001000 := by
  apply branch_checked idp00001000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-263761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-264261639/500000 : ℚ) by norm_num]
  exact coverp00001000010001
theorem coverp0000100001000 : Covers (-263761639/1000000 : ℚ) vp0000100001000 := join_branches bp00001000010000 bp00001000010001
private noncomputable def vp000010000100_0 : Blocks := edgeBlocks% "full/vectors/000010000100-V-0000.bin"
private noncomputable def vp000010000100_1 : Blocks := edgeBlocks% "full/vectors/000010000100-V-0001.bin"
noncomputable def vp000010000100 : Blocks := (Blocks.join vp000010000100_0 vp000010000100_1)
private theorem bp0000100001000 : Branch 0 (-263761639/2000000 : ℚ) vp000010000100 := by
  apply branch_left_normalized (c:=vp0000100001000) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-263761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-263761639/1000000 : ℚ) by norm_num]
  exact coverp0000100001000
private noncomputable def ep0000100001001_0 : Blocks := edgeBlocks% "full/vectors/0000100001001-E-0000.bin"
private noncomputable def ep0000100001001_1 : Blocks := edgeBlocks% "full/vectors/0000100001001-E-0001.bin"
noncomputable def ep0000100001001 : Blocks := (Blocks.join ep0000100001001_0 ep0000100001001_1)
private theorem idp0000100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010000100.list =
    C ((2:ℤ)^143) * horner X vp0000100001001.list + horner X ep0000100001001.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100001001 : Branch 1 (-263761639/2000000 : ℚ) vp000010000100 := by
  apply branch_checked idp0000100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-263761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-264761639/1000000 : ℚ) by norm_num]
  exact coverp0000100001001
theorem coverp000010000100 : Covers (-263761639/2000000 : ℚ) vp000010000100 := join_branches bp0000100001000 bp0000100001001
private noncomputable def vp00001000010_0 : Blocks := edgeBlocks% "full/vectors/00001000010-V-0000.bin"
private noncomputable def vp00001000010_1 : Blocks := edgeBlocks% "full/vectors/00001000010-V-0001.bin"
private noncomputable def vp00001000010_2 : Blocks := edgeBlocks% "full/vectors/00001000010-V-0002.bin"
noncomputable def vp00001000010 : Blocks := (Blocks.join vp00001000010_0 (Blocks.join vp00001000010_1 vp00001000010_2))
private theorem bp000010000100 : Branch 0 (-263761639/4000000 : ℚ) vp00001000010 := by
  apply branch_left_normalized (c:=vp000010000100) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-263761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-263761639/2000000 : ℚ) by norm_num]
  exact coverp000010000100
private noncomputable def ep000010000101_0 : Blocks := edgeBlocks% "full/vectors/000010000101-E-0000.bin"
private noncomputable def ep000010000101_1 : Blocks := edgeBlocks% "full/vectors/000010000101-E-0001.bin"
private noncomputable def ep000010000101_2 : Blocks := edgeBlocks% "full/vectors/000010000101-E-0002.bin"
noncomputable def ep000010000101 : Blocks := (Blocks.join ep000010000101_0 (Blocks.join ep000010000101_1 ep000010000101_2))
private theorem idp000010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000010.list =
    C ((2:ℤ)^268) * horner X vp000010000101.list + horner X ep000010000101.list := by
  exact edge_identity (B := (2:ℤ)^477) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010000101 : Branch 1 (-263761639/4000000 : ℚ) vp00001000010 := by
  apply branch_checked idp000010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-263761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-265761639/2000000 : ℚ) by norm_num]
  exact coverp000010000101
theorem coverp00001000010 : Covers (-263761639/4000000 : ℚ) vp00001000010 := join_branches bp000010000100 bp000010000101
private noncomputable def vp0000100001_0 : Blocks := edgeBlocks% "full/vectors/0000100001-V-0000.bin"
private noncomputable def vp0000100001_1 : Blocks := edgeBlocks% "full/vectors/0000100001-V-0001.bin"
private noncomputable def vp0000100001_2 : Blocks := edgeBlocks% "full/vectors/0000100001-V-0002.bin"
private noncomputable def vp0000100001_3 : Blocks := edgeBlocks% "full/vectors/0000100001-V-0003.bin"
noncomputable def vp0000100001 : Blocks := (Blocks.join (Blocks.join vp0000100001_0 vp0000100001_1) (Blocks.join vp0000100001_2 vp0000100001_3))
private theorem bp00001000010 : Branch 0 (-263761639/8000000 : ℚ) vp0000100001 := by
  apply branch_left_normalized (c:=vp00001000010) (k:=0) (m:=257) (by decide +kernel)
  rw [show 2*(-263761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-263761639/4000000 : ℚ) by norm_num]
  exact coverp00001000010
private noncomputable def ep00001000011_0 : Blocks := edgeBlocks% "full/vectors/00001000011-E-0000.bin"
private noncomputable def ep00001000011_1 : Blocks := edgeBlocks% "full/vectors/00001000011-E-0001.bin"
private noncomputable def ep00001000011_2 : Blocks := edgeBlocks% "full/vectors/00001000011-E-0002.bin"
private noncomputable def ep00001000011_3 : Blocks := edgeBlocks% "full/vectors/00001000011-E-0003.bin"
noncomputable def ep00001000011 : Blocks := (Blocks.join (Blocks.join ep00001000011_0 ep00001000011_1) (Blocks.join ep00001000011_2 ep00001000011_3))
private theorem idp00001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100001.list =
    C ((2:ℤ)^516) * horner X vp00001000011.list + horner X ep00001000011.list := by
  exact edge_identity (B := (2:ℤ)^844) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000011 : Branch 1 (-263761639/8000000 : ℚ) vp0000100001 := by
  apply branch_checked idp00001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-263761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-267761639/4000000 : ℚ) by norm_num]
  exact coverp00001000011
theorem coverp0000100001 : Covers (-263761639/8000000 : ℚ) vp0000100001 := join_branches bp00001000010 bp00001000011
private noncomputable def vp00001000001111_0 : Blocks := edgeBlocks% "full/vectors/00001000001111-V-0000.bin"
noncomputable def vp00001000001111 : Blocks := vp00001000001111_0
theorem coverp00001000001111 : Covers (-263261639/500000 : ℚ) vp00001000001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000001110_0 : Blocks := edgeBlocks% "full/vectors/00001000001110-V-0000.bin"
noncomputable def vp00001000001110 : Blocks := vp00001000001110_0
theorem coverp00001000001110 : Covers (-262761639/500000 : ℚ) vp00001000001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100000111_0 : Blocks := edgeBlocks% "full/vectors/0000100000111-V-0000.bin"
noncomputable def vp0000100000111 : Blocks := vp0000100000111_0
private theorem bp00001000001110 : Branch 0 (-262761639/1000000 : ℚ) vp0000100000111 := by
  apply branch_left_normalized (c:=vp00001000001110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-262761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-262761639/500000 : ℚ) by norm_num]
  exact coverp00001000001110
private noncomputable def ep00001000001111_0 : Blocks := edgeBlocks% "full/vectors/00001000001111-E-0000.bin"
noncomputable def ep00001000001111 : Blocks := ep00001000001111_0
private theorem idp00001000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100000111.list =
    C ((2:ℤ)^80) * horner X vp00001000001111.list + horner X ep00001000001111.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000001111 : Branch 1 (-262761639/1000000 : ℚ) vp0000100000111 := by
  apply branch_checked idp00001000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-262761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-263261639/500000 : ℚ) by norm_num]
  exact coverp00001000001111
theorem coverp0000100000111 : Covers (-262761639/1000000 : ℚ) vp0000100000111 := join_branches bp00001000001110 bp00001000001111
private noncomputable def vp00001000001101_0 : Blocks := edgeBlocks% "full/vectors/00001000001101-V-0000.bin"
noncomputable def vp00001000001101 : Blocks := vp00001000001101_0
theorem coverp00001000001101 : Covers (-262261639/500000 : ℚ) vp00001000001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000001100_0 : Blocks := edgeBlocks% "full/vectors/00001000001100-V-0000.bin"
noncomputable def vp00001000001100 : Blocks := vp00001000001100_0
theorem coverp00001000001100 : Covers (-261761639/500000 : ℚ) vp00001000001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100000110_0 : Blocks := edgeBlocks% "full/vectors/0000100000110-V-0000.bin"
noncomputable def vp0000100000110 : Blocks := vp0000100000110_0
private theorem bp00001000001100 : Branch 0 (-261761639/1000000 : ℚ) vp0000100000110 := by
  apply branch_left_normalized (c:=vp00001000001100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-261761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-261761639/500000 : ℚ) by norm_num]
  exact coverp00001000001100
private noncomputable def ep00001000001101_0 : Blocks := edgeBlocks% "full/vectors/00001000001101-E-0000.bin"
noncomputable def ep00001000001101 : Blocks := ep00001000001101_0
private theorem idp00001000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100000110.list =
    C ((2:ℤ)^79) * horner X vp00001000001101.list + horner X ep00001000001101.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000001101 : Branch 1 (-261761639/1000000 : ℚ) vp0000100000110 := by
  apply branch_checked idp00001000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-261761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-262261639/500000 : ℚ) by norm_num]
  exact coverp00001000001101
theorem coverp0000100000110 : Covers (-261761639/1000000 : ℚ) vp0000100000110 := join_branches bp00001000001100 bp00001000001101
private noncomputable def vp000010000011_0 : Blocks := edgeBlocks% "full/vectors/000010000011-V-0000.bin"
private noncomputable def vp000010000011_1 : Blocks := edgeBlocks% "full/vectors/000010000011-V-0001.bin"
noncomputable def vp000010000011 : Blocks := (Blocks.join vp000010000011_0 vp000010000011_1)
private theorem bp0000100000110 : Branch 0 (-261761639/2000000 : ℚ) vp000010000011 := by
  apply branch_left_normalized (c:=vp0000100000110) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-261761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-261761639/1000000 : ℚ) by norm_num]
  exact coverp0000100000110
private noncomputable def ep0000100000111_0 : Blocks := edgeBlocks% "full/vectors/0000100000111-E-0000.bin"
private noncomputable def ep0000100000111_1 : Blocks := edgeBlocks% "full/vectors/0000100000111-E-0001.bin"
noncomputable def ep0000100000111 : Blocks := (Blocks.join ep0000100000111_0 ep0000100000111_1)
private theorem idp0000100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010000011.list =
    C ((2:ℤ)^143) * horner X vp0000100000111.list + horner X ep0000100000111.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100000111 : Branch 1 (-261761639/2000000 : ℚ) vp000010000011 := by
  apply branch_checked idp0000100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-261761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-262761639/1000000 : ℚ) by norm_num]
  exact coverp0000100000111
theorem coverp000010000011 : Covers (-261761639/2000000 : ℚ) vp000010000011 := join_branches bp0000100000110 bp0000100000111
private noncomputable def vp00001000001011_0 : Blocks := edgeBlocks% "full/vectors/00001000001011-V-0000.bin"
noncomputable def vp00001000001011 : Blocks := vp00001000001011_0
theorem coverp00001000001011 : Covers (-261261639/500000 : ℚ) vp00001000001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000001010_0 : Blocks := edgeBlocks% "full/vectors/00001000001010-V-0000.bin"
noncomputable def vp00001000001010 : Blocks := vp00001000001010_0
theorem coverp00001000001010 : Covers (-260761639/500000 : ℚ) vp00001000001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100000101_0 : Blocks := edgeBlocks% "full/vectors/0000100000101-V-0000.bin"
noncomputable def vp0000100000101 : Blocks := vp0000100000101_0
private theorem bp00001000001010 : Branch 0 (-260761639/1000000 : ℚ) vp0000100000101 := by
  apply branch_left_normalized (c:=vp00001000001010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-260761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-260761639/500000 : ℚ) by norm_num]
  exact coverp00001000001010
private noncomputable def ep00001000001011_0 : Blocks := edgeBlocks% "full/vectors/00001000001011-E-0000.bin"
noncomputable def ep00001000001011 : Blocks := ep00001000001011_0
private theorem idp00001000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100000101.list =
    C ((2:ℤ)^78) * horner X vp00001000001011.list + horner X ep00001000001011.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000001011 : Branch 1 (-260761639/1000000 : ℚ) vp0000100000101 := by
  apply branch_checked idp00001000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-260761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-261261639/500000 : ℚ) by norm_num]
  exact coverp00001000001011
theorem coverp0000100000101 : Covers (-260761639/1000000 : ℚ) vp0000100000101 := join_branches bp00001000001010 bp00001000001011
private noncomputable def vp00001000001001_0 : Blocks := edgeBlocks% "full/vectors/00001000001001-V-0000.bin"
noncomputable def vp00001000001001 : Blocks := vp00001000001001_0
theorem coverp00001000001001 : Covers (-260261639/500000 : ℚ) vp00001000001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000001000_0 : Blocks := edgeBlocks% "full/vectors/00001000001000-V-0000.bin"
noncomputable def vp00001000001000 : Blocks := vp00001000001000_0
theorem coverp00001000001000 : Covers (-259761639/500000 : ℚ) vp00001000001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100000100_0 : Blocks := edgeBlocks% "full/vectors/0000100000100-V-0000.bin"
noncomputable def vp0000100000100 : Blocks := vp0000100000100_0
private theorem bp00001000001000 : Branch 0 (-259761639/1000000 : ℚ) vp0000100000100 := by
  apply branch_left_normalized (c:=vp00001000001000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-259761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-259761639/500000 : ℚ) by norm_num]
  exact coverp00001000001000
private noncomputable def ep00001000001001_0 : Blocks := edgeBlocks% "full/vectors/00001000001001-E-0000.bin"
noncomputable def ep00001000001001 : Blocks := ep00001000001001_0
private theorem idp00001000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100000100.list =
    C ((2:ℤ)^79) * horner X vp00001000001001.list + horner X ep00001000001001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000001001 : Branch 1 (-259761639/1000000 : ℚ) vp0000100000100 := by
  apply branch_checked idp00001000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-259761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-260261639/500000 : ℚ) by norm_num]
  exact coverp00001000001001
theorem coverp0000100000100 : Covers (-259761639/1000000 : ℚ) vp0000100000100 := join_branches bp00001000001000 bp00001000001001
private noncomputable def vp000010000010_0 : Blocks := edgeBlocks% "full/vectors/000010000010-V-0000.bin"
private noncomputable def vp000010000010_1 : Blocks := edgeBlocks% "full/vectors/000010000010-V-0001.bin"
noncomputable def vp000010000010 : Blocks := (Blocks.join vp000010000010_0 vp000010000010_1)
private theorem bp0000100000100 : Branch 0 (-259761639/2000000 : ℚ) vp000010000010 := by
  apply branch_left_normalized (c:=vp0000100000100) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-259761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-259761639/1000000 : ℚ) by norm_num]
  exact coverp0000100000100
private noncomputable def ep0000100000101_0 : Blocks := edgeBlocks% "full/vectors/0000100000101-E-0000.bin"
private noncomputable def ep0000100000101_1 : Blocks := edgeBlocks% "full/vectors/0000100000101-E-0001.bin"
noncomputable def ep0000100000101 : Blocks := (Blocks.join ep0000100000101_0 ep0000100000101_1)
private theorem idp0000100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010000010.list =
    C ((2:ℤ)^144) * horner X vp0000100000101.list + horner X ep0000100000101.list := by
  exact edge_identity (B := (2:ℤ)^292) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100000101 : Branch 1 (-259761639/2000000 : ℚ) vp000010000010 := by
  apply branch_checked idp0000100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-259761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-260761639/1000000 : ℚ) by norm_num]
  exact coverp0000100000101
theorem coverp000010000010 : Covers (-259761639/2000000 : ℚ) vp000010000010 := join_branches bp0000100000100 bp0000100000101
private noncomputable def vp00001000001_0 : Blocks := edgeBlocks% "full/vectors/00001000001-V-0000.bin"
private noncomputable def vp00001000001_1 : Blocks := edgeBlocks% "full/vectors/00001000001-V-0001.bin"
private noncomputable def vp00001000001_2 : Blocks := edgeBlocks% "full/vectors/00001000001-V-0002.bin"
noncomputable def vp00001000001 : Blocks := (Blocks.join vp00001000001_0 (Blocks.join vp00001000001_1 vp00001000001_2))
private theorem bp000010000010 : Branch 0 (-259761639/4000000 : ℚ) vp00001000001 := by
  apply branch_left_normalized (c:=vp000010000010) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-259761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-259761639/2000000 : ℚ) by norm_num]
  exact coverp000010000010
private noncomputable def ep000010000011_0 : Blocks := edgeBlocks% "full/vectors/000010000011-E-0000.bin"
private noncomputable def ep000010000011_1 : Blocks := edgeBlocks% "full/vectors/000010000011-E-0001.bin"
private noncomputable def ep000010000011_2 : Blocks := edgeBlocks% "full/vectors/000010000011-E-0002.bin"
noncomputable def ep000010000011 : Blocks := (Blocks.join ep000010000011_0 (Blocks.join ep000010000011_1 ep000010000011_2))
private theorem idp000010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000001.list =
    C ((2:ℤ)^270) * horner X vp000010000011.list + horner X ep000010000011.list := by
  exact edge_identity (B := (2:ℤ)^478) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010000011 : Branch 1 (-259761639/4000000 : ℚ) vp00001000001 := by
  apply branch_checked idp000010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-259761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-261761639/2000000 : ℚ) by norm_num]
  exact coverp000010000011
theorem coverp00001000001 : Covers (-259761639/4000000 : ℚ) vp00001000001 := join_branches bp000010000010 bp000010000011
private noncomputable def vp00001000000111_0 : Blocks := edgeBlocks% "full/vectors/00001000000111-V-0000.bin"
noncomputable def vp00001000000111 : Blocks := vp00001000000111_0
theorem coverp00001000000111 : Covers (-259261639/500000 : ℚ) vp00001000000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000000110_0 : Blocks := edgeBlocks% "full/vectors/00001000000110-V-0000.bin"
noncomputable def vp00001000000110 : Blocks := vp00001000000110_0
theorem coverp00001000000110 : Covers (-258761639/500000 : ℚ) vp00001000000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100000011_0 : Blocks := edgeBlocks% "full/vectors/0000100000011-V-0000.bin"
noncomputable def vp0000100000011 : Blocks := vp0000100000011_0
private theorem bp00001000000110 : Branch 0 (-258761639/1000000 : ℚ) vp0000100000011 := by
  apply branch_left_normalized (c:=vp00001000000110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-258761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-258761639/500000 : ℚ) by norm_num]
  exact coverp00001000000110
private noncomputable def ep00001000000111_0 : Blocks := edgeBlocks% "full/vectors/00001000000111-E-0000.bin"
noncomputable def ep00001000000111 : Blocks := ep00001000000111_0
private theorem idp00001000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100000011.list =
    C ((2:ℤ)^80) * horner X vp00001000000111.list + horner X ep00001000000111.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000000111 : Branch 1 (-258761639/1000000 : ℚ) vp0000100000011 := by
  apply branch_checked idp00001000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-258761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-259261639/500000 : ℚ) by norm_num]
  exact coverp00001000000111
theorem coverp0000100000011 : Covers (-258761639/1000000 : ℚ) vp0000100000011 := join_branches bp00001000000110 bp00001000000111
private noncomputable def vp00001000000101_0 : Blocks := edgeBlocks% "full/vectors/00001000000101-V-0000.bin"
noncomputable def vp00001000000101 : Blocks := vp00001000000101_0
theorem coverp00001000000101 : Covers (-258261639/500000 : ℚ) vp00001000000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000000100_0 : Blocks := edgeBlocks% "full/vectors/00001000000100-V-0000.bin"
noncomputable def vp00001000000100 : Blocks := vp00001000000100_0
theorem coverp00001000000100 : Covers (-257761639/500000 : ℚ) vp00001000000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100000010_0 : Blocks := edgeBlocks% "full/vectors/0000100000010-V-0000.bin"
noncomputable def vp0000100000010 : Blocks := vp0000100000010_0
private theorem bp00001000000100 : Branch 0 (-257761639/1000000 : ℚ) vp0000100000010 := by
  apply branch_left_normalized (c:=vp00001000000100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-257761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-257761639/500000 : ℚ) by norm_num]
  exact coverp00001000000100
private noncomputable def ep00001000000101_0 : Blocks := edgeBlocks% "full/vectors/00001000000101-E-0000.bin"
noncomputable def ep00001000000101 : Blocks := ep00001000000101_0
private theorem idp00001000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100000010.list =
    C ((2:ℤ)^80) * horner X vp00001000000101.list + horner X ep00001000000101.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000000101 : Branch 1 (-257761639/1000000 : ℚ) vp0000100000010 := by
  apply branch_checked idp00001000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-257761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-258261639/500000 : ℚ) by norm_num]
  exact coverp00001000000101
theorem coverp0000100000010 : Covers (-257761639/1000000 : ℚ) vp0000100000010 := join_branches bp00001000000100 bp00001000000101
private noncomputable def vp000010000001_0 : Blocks := edgeBlocks% "full/vectors/000010000001-V-0000.bin"
private noncomputable def vp000010000001_1 : Blocks := edgeBlocks% "full/vectors/000010000001-V-0001.bin"
noncomputable def vp000010000001 : Blocks := (Blocks.join vp000010000001_0 vp000010000001_1)
private theorem bp0000100000010 : Branch 0 (-257761639/2000000 : ℚ) vp000010000001 := by
  apply branch_left_normalized (c:=vp0000100000010) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-257761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-257761639/1000000 : ℚ) by norm_num]
  exact coverp0000100000010
private noncomputable def ep0000100000011_0 : Blocks := edgeBlocks% "full/vectors/0000100000011-E-0000.bin"
private noncomputable def ep0000100000011_1 : Blocks := edgeBlocks% "full/vectors/0000100000011-E-0001.bin"
noncomputable def ep0000100000011 : Blocks := (Blocks.join ep0000100000011_0 ep0000100000011_1)
private theorem idp0000100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010000001.list =
    C ((2:ℤ)^144) * horner X vp0000100000011.list + horner X ep0000100000011.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100000011 : Branch 1 (-257761639/2000000 : ℚ) vp000010000001 := by
  apply branch_checked idp0000100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-257761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-258761639/1000000 : ℚ) by norm_num]
  exact coverp0000100000011
theorem coverp000010000001 : Covers (-257761639/2000000 : ℚ) vp000010000001 := join_branches bp0000100000010 bp0000100000011
private noncomputable def vp00001000000011_0 : Blocks := edgeBlocks% "full/vectors/00001000000011-V-0000.bin"
noncomputable def vp00001000000011 : Blocks := vp00001000000011_0
theorem coverp00001000000011 : Covers (-257261639/500000 : ℚ) vp00001000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000000010_0 : Blocks := edgeBlocks% "full/vectors/00001000000010-V-0000.bin"
noncomputable def vp00001000000010 : Blocks := vp00001000000010_0
theorem coverp00001000000010 : Covers (-256761639/500000 : ℚ) vp00001000000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100000001_0 : Blocks := edgeBlocks% "full/vectors/0000100000001-V-0000.bin"
noncomputable def vp0000100000001 : Blocks := vp0000100000001_0
private theorem bp00001000000010 : Branch 0 (-256761639/1000000 : ℚ) vp0000100000001 := by
  apply branch_left_normalized (c:=vp00001000000010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-256761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-256761639/500000 : ℚ) by norm_num]
  exact coverp00001000000010
private noncomputable def ep00001000000011_0 : Blocks := edgeBlocks% "full/vectors/00001000000011-E-0000.bin"
noncomputable def ep00001000000011 : Blocks := ep00001000000011_0
private theorem idp00001000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100000001.list =
    C ((2:ℤ)^80) * horner X vp00001000000011.list + horner X ep00001000000011.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000000011 : Branch 1 (-256761639/1000000 : ℚ) vp0000100000001 := by
  apply branch_checked idp00001000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-256761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-257261639/500000 : ℚ) by norm_num]
  exact coverp00001000000011
theorem coverp0000100000001 : Covers (-256761639/1000000 : ℚ) vp0000100000001 := join_branches bp00001000000010 bp00001000000011
private noncomputable def vp00001000000001_0 : Blocks := edgeBlocks% "full/vectors/00001000000001-V-0000.bin"
noncomputable def vp00001000000001 : Blocks := vp00001000000001_0
theorem coverp00001000000001 : Covers (-256261639/500000 : ℚ) vp00001000000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001000000000_0 : Blocks := edgeBlocks% "full/vectors/00001000000000-V-0000.bin"
noncomputable def vp00001000000000 : Blocks := vp00001000000000_0
theorem coverp00001000000000 : Covers (-255761639/500000 : ℚ) vp00001000000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000100000000_0 : Blocks := edgeBlocks% "full/vectors/0000100000000-V-0000.bin"
noncomputable def vp0000100000000 : Blocks := vp0000100000000_0
private theorem bp00001000000000 : Branch 0 (-255761639/1000000 : ℚ) vp0000100000000 := by
  apply branch_left_normalized (c:=vp00001000000000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-255761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-255761639/500000 : ℚ) by norm_num]
  exact coverp00001000000000
private noncomputable def ep00001000000001_0 : Blocks := edgeBlocks% "full/vectors/00001000000001-E-0000.bin"
noncomputable def ep00001000000001 : Blocks := ep00001000000001_0
private theorem idp00001000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100000000.list =
    C ((2:ℤ)^80) * horner X vp00001000000001.list + horner X ep00001000000001.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000000001 : Branch 1 (-255761639/1000000 : ℚ) vp0000100000000 := by
  apply branch_checked idp00001000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-255761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-256261639/500000 : ℚ) by norm_num]
  exact coverp00001000000001
theorem coverp0000100000000 : Covers (-255761639/1000000 : ℚ) vp0000100000000 := join_branches bp00001000000000 bp00001000000001
private noncomputable def vp000010000000_0 : Blocks := edgeBlocks% "full/vectors/000010000000-V-0000.bin"
private noncomputable def vp000010000000_1 : Blocks := edgeBlocks% "full/vectors/000010000000-V-0001.bin"
noncomputable def vp000010000000 : Blocks := (Blocks.join vp000010000000_0 vp000010000000_1)
private theorem bp0000100000000 : Branch 0 (-255761639/2000000 : ℚ) vp000010000000 := by
  apply branch_left_normalized (c:=vp0000100000000) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-255761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-255761639/1000000 : ℚ) by norm_num]
  exact coverp0000100000000
private noncomputable def ep0000100000001_0 : Blocks := edgeBlocks% "full/vectors/0000100000001-E-0000.bin"
private noncomputable def ep0000100000001_1 : Blocks := edgeBlocks% "full/vectors/0000100000001-E-0001.bin"
noncomputable def ep0000100000001 : Blocks := (Blocks.join ep0000100000001_0 ep0000100000001_1)
private theorem idp0000100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010000000.list =
    C ((2:ℤ)^144) * horner X vp0000100000001.list + horner X ep0000100000001.list := by
  exact edge_identity (B := (2:ℤ)^294) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100000001 : Branch 1 (-255761639/2000000 : ℚ) vp000010000000 := by
  apply branch_checked idp0000100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-255761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-256761639/1000000 : ℚ) by norm_num]
  exact coverp0000100000001
theorem coverp000010000000 : Covers (-255761639/2000000 : ℚ) vp000010000000 := join_branches bp0000100000000 bp0000100000001
private noncomputable def vp00001000000_0 : Blocks := edgeBlocks% "full/vectors/00001000000-V-0000.bin"
private noncomputable def vp00001000000_1 : Blocks := edgeBlocks% "full/vectors/00001000000-V-0001.bin"
private noncomputable def vp00001000000_2 : Blocks := edgeBlocks% "full/vectors/00001000000-V-0002.bin"
noncomputable def vp00001000000 : Blocks := (Blocks.join vp00001000000_0 (Blocks.join vp00001000000_1 vp00001000000_2))
private theorem bp000010000000 : Branch 0 (-255761639/4000000 : ℚ) vp00001000000 := by
  apply branch_left_normalized (c:=vp000010000000) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-255761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-255761639/2000000 : ℚ) by norm_num]
  exact coverp000010000000
private noncomputable def ep000010000001_0 : Blocks := edgeBlocks% "full/vectors/000010000001-E-0000.bin"
private noncomputable def ep000010000001_1 : Blocks := edgeBlocks% "full/vectors/000010000001-E-0001.bin"
private noncomputable def ep000010000001_2 : Blocks := edgeBlocks% "full/vectors/000010000001-E-0002.bin"
noncomputable def ep000010000001 : Blocks := (Blocks.join ep000010000001_0 (Blocks.join ep000010000001_1 ep000010000001_2))
private theorem idp000010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000000.list =
    C ((2:ℤ)^273) * horner X vp000010000001.list + horner X ep000010000001.list := by
  exact edge_identity (B := (2:ℤ)^482) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010000001 : Branch 1 (-255761639/4000000 : ℚ) vp00001000000 := by
  apply branch_checked idp000010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-255761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-257761639/2000000 : ℚ) by norm_num]
  exact coverp000010000001
theorem coverp00001000000 : Covers (-255761639/4000000 : ℚ) vp00001000000 := join_branches bp000010000000 bp000010000001
private noncomputable def vp0000100000_0 : Blocks := edgeBlocks% "full/vectors/0000100000-V-0000.bin"
private noncomputable def vp0000100000_1 : Blocks := edgeBlocks% "full/vectors/0000100000-V-0001.bin"
private noncomputable def vp0000100000_2 : Blocks := edgeBlocks% "full/vectors/0000100000-V-0002.bin"
private noncomputable def vp0000100000_3 : Blocks := edgeBlocks% "full/vectors/0000100000-V-0003.bin"
noncomputable def vp0000100000 : Blocks := (Blocks.join (Blocks.join vp0000100000_0 vp0000100000_1) (Blocks.join vp0000100000_2 vp0000100000_3))
private theorem bp00001000000 : Branch 0 (-255761639/8000000 : ℚ) vp0000100000 := by
  apply branch_left_normalized (c:=vp00001000000) (k:=0) (m:=260) (by decide +kernel)
  rw [show 2*(-255761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-255761639/4000000 : ℚ) by norm_num]
  exact coverp00001000000
private noncomputable def ep00001000001_0 : Blocks := edgeBlocks% "full/vectors/00001000001-E-0000.bin"
private noncomputable def ep00001000001_1 : Blocks := edgeBlocks% "full/vectors/00001000001-E-0001.bin"
private noncomputable def ep00001000001_2 : Blocks := edgeBlocks% "full/vectors/00001000001-E-0002.bin"
private noncomputable def ep00001000001_3 : Blocks := edgeBlocks% "full/vectors/00001000001-E-0003.bin"
noncomputable def ep00001000001 : Blocks := (Blocks.join (Blocks.join ep00001000001_0 ep00001000001_1) (Blocks.join ep00001000001_2 ep00001000001_3))
private theorem idp00001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000100000.list =
    C ((2:ℤ)^529) * horner X vp00001000001.list + horner X ep00001000001.list := by
  exact edge_identity (B := (2:ℤ)^856) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001000001 : Branch 1 (-255761639/8000000 : ℚ) vp0000100000 := by
  apply branch_checked idp00001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-255761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-259761639/4000000 : ℚ) by norm_num]
  exact coverp00001000001
theorem coverp0000100000 : Covers (-255761639/8000000 : ℚ) vp0000100000 := join_branches bp00001000000 bp00001000001
private noncomputable def vp000010000_0 : Blocks := edgeBlocks% "full/vectors/000010000-V-0000.bin"
private noncomputable def vp000010000_1 : Blocks := edgeBlocks% "full/vectors/000010000-V-0001.bin"
private noncomputable def vp000010000_2 : Blocks := edgeBlocks% "full/vectors/000010000-V-0002.bin"
private noncomputable def vp000010000_3 : Blocks := edgeBlocks% "full/vectors/000010000-V-0003.bin"
private noncomputable def vp000010000_4 : Blocks := edgeBlocks% "full/vectors/000010000-V-0004.bin"
private noncomputable def vp000010000_5 : Blocks := edgeBlocks% "full/vectors/000010000-V-0005.bin"
private noncomputable def vp000010000_6 : Blocks := edgeBlocks% "full/vectors/000010000-V-0006.bin"
private noncomputable def vp000010000_7 : Blocks := edgeBlocks% "full/vectors/000010000-V-0007.bin"
noncomputable def vp000010000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000010000_0 vp000010000_1) (Blocks.join vp000010000_2 vp000010000_3)) (Blocks.join (Blocks.join vp000010000_4 vp000010000_5) (Blocks.join vp000010000_6 vp000010000_7)))
private theorem bp0000100000 : Branch 0 (-255761639/16000000 : ℚ) vp000010000 := by
  apply branch_left_normalized (c:=vp0000100000) (k:=0) (m:=504) (by decide +kernel)
  rw [show 2*(-255761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-255761639/8000000 : ℚ) by norm_num]
  exact coverp0000100000
private noncomputable def ep0000100001_0 : Blocks := edgeBlocks% "full/vectors/0000100001-E-0000.bin"
private noncomputable def ep0000100001_1 : Blocks := edgeBlocks% "full/vectors/0000100001-E-0001.bin"
private noncomputable def ep0000100001_2 : Blocks := edgeBlocks% "full/vectors/0000100001-E-0002.bin"
private noncomputable def ep0000100001_3 : Blocks := edgeBlocks% "full/vectors/0000100001-E-0003.bin"
private noncomputable def ep0000100001_4 : Blocks := edgeBlocks% "full/vectors/0000100001-E-0004.bin"
private noncomputable def ep0000100001_5 : Blocks := edgeBlocks% "full/vectors/0000100001-E-0005.bin"
private noncomputable def ep0000100001_6 : Blocks := edgeBlocks% "full/vectors/0000100001-E-0006.bin"
private noncomputable def ep0000100001_7 : Blocks := edgeBlocks% "full/vectors/0000100001-E-0007.bin"
noncomputable def ep0000100001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000100001_0 ep0000100001_1) (Blocks.join ep0000100001_2 ep0000100001_3)) (Blocks.join (Blocks.join ep0000100001_4 ep0000100001_5) (Blocks.join ep0000100001_6 ep0000100001_7)))
private theorem idp0000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000010000.list =
    C ((2:ℤ)^1031) * horner X vp0000100001.list + horner X ep0000100001.list := by
  exact edge_identity (B := (2:ℤ)^1595) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000100001 : Branch 1 (-255761639/16000000 : ℚ) vp000010000 := by
  apply branch_checked idp0000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-255761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-263761639/8000000 : ℚ) by norm_num]
  exact coverp0000100001
theorem coverp000010000 : Covers (-255761639/16000000 : ℚ) vp000010000 := join_branches bp0000100000 bp0000100001
private noncomputable def vp00001000_0 : Blocks := edgeBlocks% "full/vectors/00001000-V-0000.bin"
private noncomputable def vp00001000_1 : Blocks := edgeBlocks% "full/vectors/00001000-V-0001.bin"
private noncomputable def vp00001000_2 : Blocks := edgeBlocks% "full/vectors/00001000-V-0002.bin"
private noncomputable def vp00001000_3 : Blocks := edgeBlocks% "full/vectors/00001000-V-0003.bin"
private noncomputable def vp00001000_4 : Blocks := edgeBlocks% "full/vectors/00001000-V-0004.bin"
private noncomputable def vp00001000_5 : Blocks := edgeBlocks% "full/vectors/00001000-V-0005.bin"
private noncomputable def vp00001000_6 : Blocks := edgeBlocks% "full/vectors/00001000-V-0006.bin"
private noncomputable def vp00001000_7 : Blocks := edgeBlocks% "full/vectors/00001000-V-0007.bin"
private noncomputable def vp00001000_8 : Blocks := edgeBlocks% "full/vectors/00001000-V-0008.bin"
private noncomputable def vp00001000_9 : Blocks := edgeBlocks% "full/vectors/00001000-V-0009.bin"
private noncomputable def vp00001000_10 : Blocks := edgeBlocks% "full/vectors/00001000-V-0010.bin"
private noncomputable def vp00001000_11 : Blocks := edgeBlocks% "full/vectors/00001000-V-0011.bin"
private noncomputable def vp00001000_12 : Blocks := edgeBlocks% "full/vectors/00001000-V-0012.bin"
private noncomputable def vp00001000_13 : Blocks := edgeBlocks% "full/vectors/00001000-V-0013.bin"
private noncomputable def vp00001000_14 : Blocks := edgeBlocks% "full/vectors/00001000-V-0014.bin"
private noncomputable def vp00001000_15 : Blocks := edgeBlocks% "full/vectors/00001000-V-0015.bin"
noncomputable def vp00001000 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00001000_0 vp00001000_1) (Blocks.join vp00001000_2 vp00001000_3)) (Blocks.join (Blocks.join vp00001000_4 vp00001000_5) (Blocks.join vp00001000_6 vp00001000_7))) (Blocks.join (Blocks.join (Blocks.join vp00001000_8 vp00001000_9) (Blocks.join vp00001000_10 vp00001000_11)) (Blocks.join (Blocks.join vp00001000_12 vp00001000_13) (Blocks.join vp00001000_14 vp00001000_15))))
private theorem bp000010000 : Branch 0 (-255761639/32000000 : ℚ) vp00001000 := by
  apply branch_left_normalized (c:=vp000010000) (k:=0) (m:=984) (by decide +kernel)
  rw [show 2*(-255761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-255761639/16000000 : ℚ) by norm_num]
  exact coverp000010000
private noncomputable def ep000010001_0 : Blocks := edgeBlocks% "full/vectors/000010001-E-0000.bin"
private noncomputable def ep000010001_1 : Blocks := edgeBlocks% "full/vectors/000010001-E-0001.bin"
private noncomputable def ep000010001_2 : Blocks := edgeBlocks% "full/vectors/000010001-E-0002.bin"
private noncomputable def ep000010001_3 : Blocks := edgeBlocks% "full/vectors/000010001-E-0003.bin"
private noncomputable def ep000010001_4 : Blocks := edgeBlocks% "full/vectors/000010001-E-0004.bin"
private noncomputable def ep000010001_5 : Blocks := edgeBlocks% "full/vectors/000010001-E-0005.bin"
private noncomputable def ep000010001_6 : Blocks := edgeBlocks% "full/vectors/000010001-E-0006.bin"
private noncomputable def ep000010001_7 : Blocks := edgeBlocks% "full/vectors/000010001-E-0007.bin"
private noncomputable def ep000010001_8 : Blocks := edgeBlocks% "full/vectors/000010001-E-0008.bin"
private noncomputable def ep000010001_9 : Blocks := edgeBlocks% "full/vectors/000010001-E-0009.bin"
private noncomputable def ep000010001_10 : Blocks := edgeBlocks% "full/vectors/000010001-E-0010.bin"
private noncomputable def ep000010001_11 : Blocks := edgeBlocks% "full/vectors/000010001-E-0011.bin"
private noncomputable def ep000010001_12 : Blocks := edgeBlocks% "full/vectors/000010001-E-0012.bin"
private noncomputable def ep000010001_13 : Blocks := edgeBlocks% "full/vectors/000010001-E-0013.bin"
private noncomputable def ep000010001_14 : Blocks := edgeBlocks% "full/vectors/000010001-E-0014.bin"
private noncomputable def ep000010001_15 : Blocks := edgeBlocks% "full/vectors/000010001-E-0015.bin"
noncomputable def ep000010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep000010001_0 ep000010001_1) (Blocks.join ep000010001_2 ep000010001_3)) (Blocks.join (Blocks.join ep000010001_4 ep000010001_5) (Blocks.join ep000010001_6 ep000010001_7))) (Blocks.join (Blocks.join (Blocks.join ep000010001_8 ep000010001_9) (Blocks.join ep000010001_10 ep000010001_11)) (Blocks.join (Blocks.join ep000010001_12 ep000010001_13) (Blocks.join ep000010001_14 ep000010001_15))))
private theorem idp000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001000.list =
    C ((2:ℤ)^2006) * horner X vp000010001.list + horner X ep000010001.list := by
  exact edge_identity (B := (2:ℤ)^3049) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000010001 : Branch 1 (-255761639/32000000 : ℚ) vp00001000 := by
  apply branch_checked idp000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-255761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-271761639/16000000 : ℚ) by norm_num]
  exact coverp000010001
theorem coverp00001000 : Covers (-255761639/32000000 : ℚ) vp00001000 := join_branches bp000010000 bp000010001
end NextProof.EdgeFull

