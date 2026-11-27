import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0001000111111_0 : Blocks := edgeBlocks% "full/vectors/0001000111111-V-0000.bin"
noncomputable def vp0001000111111 : Blocks := vp0001000111111_0
theorem coverp0001000111111 : Covers (-574761639/1000000 : ℚ) vp0001000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000111110_0 : Blocks := edgeBlocks% "full/vectors/0001000111110-V-0000.bin"
noncomputable def vp0001000111110 : Blocks := vp0001000111110_0
theorem coverp0001000111110 : Covers (-573761639/1000000 : ℚ) vp0001000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000100011111_0 : Blocks := edgeBlocks% "full/vectors/000100011111-V-0000.bin"
noncomputable def vp000100011111 : Blocks := vp000100011111_0
private theorem bp0001000111110 : Branch 0 (-573761639/2000000 : ℚ) vp000100011111 := by
  apply branch_left_normalized (c:=vp0001000111110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-573761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-573761639/1000000 : ℚ) by norm_num]
  exact coverp0001000111110
private noncomputable def ep0001000111111_0 : Blocks := edgeBlocks% "full/vectors/0001000111111-E-0000.bin"
noncomputable def ep0001000111111 : Blocks := ep0001000111111_0
private theorem idp0001000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100011111.list =
    C ((2:ℤ)^105) * horner X vp0001000111111.list + horner X ep0001000111111.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000111111 : Branch 1 (-573761639/2000000 : ℚ) vp000100011111 := by
  apply branch_checked idp0001000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-573761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-574761639/1000000 : ℚ) by norm_num]
  exact coverp0001000111111
theorem coverp000100011111 : Covers (-573761639/2000000 : ℚ) vp000100011111 := join_branches bp0001000111110 bp0001000111111
private noncomputable def vp0001000111101_0 : Blocks := edgeBlocks% "full/vectors/0001000111101-V-0000.bin"
noncomputable def vp0001000111101 : Blocks := vp0001000111101_0
theorem coverp0001000111101 : Covers (-572761639/1000000 : ℚ) vp0001000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000111100_0 : Blocks := edgeBlocks% "full/vectors/0001000111100-V-0000.bin"
noncomputable def vp0001000111100 : Blocks := vp0001000111100_0
theorem coverp0001000111100 : Covers (-571761639/1000000 : ℚ) vp0001000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000100011110_0 : Blocks := edgeBlocks% "full/vectors/000100011110-V-0000.bin"
noncomputable def vp000100011110 : Blocks := vp000100011110_0
private theorem bp0001000111100 : Branch 0 (-571761639/2000000 : ℚ) vp000100011110 := by
  apply branch_left_normalized (c:=vp0001000111100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-571761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-571761639/1000000 : ℚ) by norm_num]
  exact coverp0001000111100
private noncomputable def ep0001000111101_0 : Blocks := edgeBlocks% "full/vectors/0001000111101-E-0000.bin"
noncomputable def ep0001000111101 : Blocks := ep0001000111101_0
private theorem idp0001000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100011110.list =
    C ((2:ℤ)^105) * horner X vp0001000111101.list + horner X ep0001000111101.list := by
  exact edge_identity (B := (2:ℤ)^235) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000111101 : Branch 1 (-571761639/2000000 : ℚ) vp000100011110 := by
  apply branch_checked idp0001000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-571761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-572761639/1000000 : ℚ) by norm_num]
  exact coverp0001000111101
theorem coverp000100011110 : Covers (-571761639/2000000 : ℚ) vp000100011110 := join_branches bp0001000111100 bp0001000111101
private noncomputable def vp00010001111_0 : Blocks := edgeBlocks% "full/vectors/00010001111-V-0000.bin"
private noncomputable def vp00010001111_1 : Blocks := edgeBlocks% "full/vectors/00010001111-V-0001.bin"
noncomputable def vp00010001111 : Blocks := (Blocks.join vp00010001111_0 vp00010001111_1)
private theorem bp000100011110 : Branch 0 (-571761639/4000000 : ℚ) vp00010001111 := by
  apply branch_left_normalized (c:=vp000100011110) (k:=0) (m:=98) (by decide +kernel)
  rw [show 2*(-571761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-571761639/2000000 : ℚ) by norm_num]
  exact coverp000100011110
private noncomputable def ep000100011111_0 : Blocks := edgeBlocks% "full/vectors/000100011111-E-0000.bin"
private noncomputable def ep000100011111_1 : Blocks := edgeBlocks% "full/vectors/000100011111-E-0001.bin"
noncomputable def ep000100011111 : Blocks := (Blocks.join ep000100011111_0 ep000100011111_1)
private theorem idp000100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010001111.list =
    C ((2:ℤ)^194) * horner X vp000100011111.list + horner X ep000100011111.list := by
  exact edge_identity (B := (2:ℤ)^361) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100011111 : Branch 1 (-571761639/4000000 : ℚ) vp00010001111 := by
  apply branch_checked idp000100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-571761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-573761639/2000000 : ℚ) by norm_num]
  exact coverp000100011111
theorem coverp00010001111 : Covers (-571761639/4000000 : ℚ) vp00010001111 := join_branches bp000100011110 bp000100011111
private noncomputable def vp0001000111011_0 : Blocks := edgeBlocks% "full/vectors/0001000111011-V-0000.bin"
noncomputable def vp0001000111011 : Blocks := vp0001000111011_0
theorem coverp0001000111011 : Covers (-570761639/1000000 : ℚ) vp0001000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000111010_0 : Blocks := edgeBlocks% "full/vectors/0001000111010-V-0000.bin"
noncomputable def vp0001000111010 : Blocks := vp0001000111010_0
theorem coverp0001000111010 : Covers (-569761639/1000000 : ℚ) vp0001000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000100011101_0 : Blocks := edgeBlocks% "full/vectors/000100011101-V-0000.bin"
noncomputable def vp000100011101 : Blocks := vp000100011101_0
private theorem bp0001000111010 : Branch 0 (-569761639/2000000 : ℚ) vp000100011101 := by
  apply branch_left_normalized (c:=vp0001000111010) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-569761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-569761639/1000000 : ℚ) by norm_num]
  exact coverp0001000111010
private noncomputable def ep0001000111011_0 : Blocks := edgeBlocks% "full/vectors/0001000111011-E-0000.bin"
noncomputable def ep0001000111011 : Blocks := ep0001000111011_0
private theorem idp0001000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100011101.list =
    C ((2:ℤ)^107) * horner X vp0001000111011.list + horner X ep0001000111011.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000111011 : Branch 1 (-569761639/2000000 : ℚ) vp000100011101 := by
  apply branch_checked idp0001000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-569761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-570761639/1000000 : ℚ) by norm_num]
  exact coverp0001000111011
theorem coverp000100011101 : Covers (-569761639/2000000 : ℚ) vp000100011101 := join_branches bp0001000111010 bp0001000111011
private noncomputable def vp0001000111001_0 : Blocks := edgeBlocks% "full/vectors/0001000111001-V-0000.bin"
noncomputable def vp0001000111001 : Blocks := vp0001000111001_0
theorem coverp0001000111001 : Covers (-568761639/1000000 : ℚ) vp0001000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000111000_0 : Blocks := edgeBlocks% "full/vectors/0001000111000-V-0000.bin"
noncomputable def vp0001000111000 : Blocks := vp0001000111000_0
theorem coverp0001000111000 : Covers (-567761639/1000000 : ℚ) vp0001000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000100011100_0 : Blocks := edgeBlocks% "full/vectors/000100011100-V-0000.bin"
noncomputable def vp000100011100 : Blocks := vp000100011100_0
private theorem bp0001000111000 : Branch 0 (-567761639/2000000 : ℚ) vp000100011100 := by
  apply branch_left_normalized (c:=vp0001000111000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-567761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-567761639/1000000 : ℚ) by norm_num]
  exact coverp0001000111000
private noncomputable def ep0001000111001_0 : Blocks := edgeBlocks% "full/vectors/0001000111001-E-0000.bin"
noncomputable def ep0001000111001 : Blocks := ep0001000111001_0
private theorem idp0001000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100011100.list =
    C ((2:ℤ)^108) * horner X vp0001000111001.list + horner X ep0001000111001.list := by
  exact edge_identity (B := (2:ℤ)^240) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000111001 : Branch 1 (-567761639/2000000 : ℚ) vp000100011100 := by
  apply branch_checked idp0001000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-567761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-568761639/1000000 : ℚ) by norm_num]
  exact coverp0001000111001
theorem coverp000100011100 : Covers (-567761639/2000000 : ℚ) vp000100011100 := join_branches bp0001000111000 bp0001000111001
private noncomputable def vp00010001110_0 : Blocks := edgeBlocks% "full/vectors/00010001110-V-0000.bin"
private noncomputable def vp00010001110_1 : Blocks := edgeBlocks% "full/vectors/00010001110-V-0001.bin"
noncomputable def vp00010001110 : Blocks := (Blocks.join vp00010001110_0 vp00010001110_1)
private theorem bp000100011100 : Branch 0 (-567761639/4000000 : ℚ) vp00010001110 := by
  apply branch_left_normalized (c:=vp000100011100) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-567761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-567761639/2000000 : ℚ) by norm_num]
  exact coverp000100011100
private noncomputable def ep000100011101_0 : Blocks := edgeBlocks% "full/vectors/000100011101-E-0000.bin"
private noncomputable def ep000100011101_1 : Blocks := edgeBlocks% "full/vectors/000100011101-E-0001.bin"
noncomputable def ep000100011101 : Blocks := (Blocks.join ep000100011101_0 ep000100011101_1)
private theorem idp000100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010001110.list =
    C ((2:ℤ)^197) * horner X vp000100011101.list + horner X ep000100011101.list := by
  exact edge_identity (B := (2:ℤ)^367) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100011101 : Branch 1 (-567761639/4000000 : ℚ) vp00010001110 := by
  apply branch_checked idp000100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-567761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-569761639/2000000 : ℚ) by norm_num]
  exact coverp000100011101
theorem coverp00010001110 : Covers (-567761639/4000000 : ℚ) vp00010001110 := join_branches bp000100011100 bp000100011101
private noncomputable def vp0001000111_0 : Blocks := edgeBlocks% "full/vectors/0001000111-V-0000.bin"
private noncomputable def vp0001000111_1 : Blocks := edgeBlocks% "full/vectors/0001000111-V-0001.bin"
private noncomputable def vp0001000111_2 : Blocks := edgeBlocks% "full/vectors/0001000111-V-0002.bin"
noncomputable def vp0001000111 : Blocks := (Blocks.join vp0001000111_0 (Blocks.join vp0001000111_1 vp0001000111_2))
private theorem bp00010001110 : Branch 0 (-567761639/8000000 : ℚ) vp0001000111 := by
  apply branch_left_normalized (c:=vp00010001110) (k:=0) (m:=183) (by decide +kernel)
  rw [show 2*(-567761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-567761639/4000000 : ℚ) by norm_num]
  exact coverp00010001110
private noncomputable def ep00010001111_0 : Blocks := edgeBlocks% "full/vectors/00010001111-E-0000.bin"
private noncomputable def ep00010001111_1 : Blocks := edgeBlocks% "full/vectors/00010001111-E-0001.bin"
private noncomputable def ep00010001111_2 : Blocks := edgeBlocks% "full/vectors/00010001111-E-0002.bin"
noncomputable def ep00010001111 : Blocks := (Blocks.join ep00010001111_0 (Blocks.join ep00010001111_1 ep00010001111_2))
private theorem idp00010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000111.list =
    C ((2:ℤ)^375) * horner X vp00010001111.list + horner X ep00010001111.list := by
  exact edge_identity (B := (2:ℤ)^620) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001111 : Branch 1 (-567761639/8000000 : ℚ) vp0001000111 := by
  apply branch_checked idp00010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-567761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-571761639/4000000 : ℚ) by norm_num]
  exact coverp00010001111
theorem coverp0001000111 : Covers (-567761639/8000000 : ℚ) vp0001000111 := join_branches bp00010001110 bp00010001111
private noncomputable def vp0001000110111_0 : Blocks := edgeBlocks% "full/vectors/0001000110111-V-0000.bin"
noncomputable def vp0001000110111 : Blocks := vp0001000110111_0
theorem coverp0001000110111 : Covers (-566761639/1000000 : ℚ) vp0001000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001101101_0 : Blocks := edgeBlocks% "full/vectors/00010001101101-V-0000.bin"
noncomputable def vp00010001101101 : Blocks := vp00010001101101_0
theorem coverp00010001101101 : Covers (-566261639/500000 : ℚ) vp00010001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001101100_0 : Blocks := edgeBlocks% "full/vectors/00010001101100-V-0000.bin"
noncomputable def vp00010001101100 : Blocks := vp00010001101100_0
theorem coverp00010001101100 : Covers (-565761639/500000 : ℚ) vp00010001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000110110_0 : Blocks := edgeBlocks% "full/vectors/0001000110110-V-0000.bin"
noncomputable def vp0001000110110 : Blocks := vp0001000110110_0
private theorem bp00010001101100 : Branch 0 (-565761639/1000000 : ℚ) vp0001000110110 := by
  apply branch_left_normalized (c:=vp00010001101100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-565761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-565761639/500000 : ℚ) by norm_num]
  exact coverp00010001101100
private noncomputable def ep00010001101101_0 : Blocks := edgeBlocks% "full/vectors/00010001101101-E-0000.bin"
noncomputable def ep00010001101101 : Blocks := ep00010001101101_0
private theorem idp00010001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000110110.list =
    C ((2:ℤ)^65) * horner X vp00010001101101.list + horner X ep00010001101101.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001101101 : Branch 1 (-565761639/1000000 : ℚ) vp0001000110110 := by
  apply branch_checked idp00010001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-565761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-566261639/500000 : ℚ) by norm_num]
  exact coverp00010001101101
theorem coverp0001000110110 : Covers (-565761639/1000000 : ℚ) vp0001000110110 := join_branches bp00010001101100 bp00010001101101
private noncomputable def vp000100011011_0 : Blocks := edgeBlocks% "full/vectors/000100011011-V-0000.bin"
noncomputable def vp000100011011 : Blocks := vp000100011011_0
private theorem bp0001000110110 : Branch 0 (-565761639/2000000 : ℚ) vp000100011011 := by
  apply branch_left_normalized (c:=vp0001000110110) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-565761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-565761639/1000000 : ℚ) by norm_num]
  exact coverp0001000110110
private noncomputable def ep0001000110111_0 : Blocks := edgeBlocks% "full/vectors/0001000110111-E-0000.bin"
noncomputable def ep0001000110111 : Blocks := ep0001000110111_0
private theorem idp0001000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100011011.list =
    C ((2:ℤ)^111) * horner X vp0001000110111.list + horner X ep0001000110111.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000110111 : Branch 1 (-565761639/2000000 : ℚ) vp000100011011 := by
  apply branch_checked idp0001000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-565761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-566761639/1000000 : ℚ) by norm_num]
  exact coverp0001000110111
theorem coverp000100011011 : Covers (-565761639/2000000 : ℚ) vp000100011011 := join_branches bp0001000110110 bp0001000110111
private noncomputable def vp00010001101011_0 : Blocks := edgeBlocks% "full/vectors/00010001101011-V-0000.bin"
noncomputable def vp00010001101011 : Blocks := vp00010001101011_0
theorem coverp00010001101011 : Covers (-565261639/500000 : ℚ) vp00010001101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001101010_0 : Blocks := edgeBlocks% "full/vectors/00010001101010-V-0000.bin"
noncomputable def vp00010001101010 : Blocks := vp00010001101010_0
theorem coverp00010001101010 : Covers (-564761639/500000 : ℚ) vp00010001101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000110101_0 : Blocks := edgeBlocks% "full/vectors/0001000110101-V-0000.bin"
noncomputable def vp0001000110101 : Blocks := vp0001000110101_0
private theorem bp00010001101010 : Branch 0 (-564761639/1000000 : ℚ) vp0001000110101 := by
  apply branch_left_normalized (c:=vp00010001101010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-564761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-564761639/500000 : ℚ) by norm_num]
  exact coverp00010001101010
private noncomputable def ep00010001101011_0 : Blocks := edgeBlocks% "full/vectors/00010001101011-E-0000.bin"
noncomputable def ep00010001101011 : Blocks := ep00010001101011_0
private theorem idp00010001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000110101.list =
    C ((2:ℤ)^66) * horner X vp00010001101011.list + horner X ep00010001101011.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001101011 : Branch 1 (-564761639/1000000 : ℚ) vp0001000110101 := by
  apply branch_checked idp00010001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-564761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-565261639/500000 : ℚ) by norm_num]
  exact coverp00010001101011
theorem coverp0001000110101 : Covers (-564761639/1000000 : ℚ) vp0001000110101 := join_branches bp00010001101010 bp00010001101011
private noncomputable def vp00010001101001_0 : Blocks := edgeBlocks% "full/vectors/00010001101001-V-0000.bin"
noncomputable def vp00010001101001 : Blocks := vp00010001101001_0
theorem coverp00010001101001 : Covers (-564261639/500000 : ℚ) vp00010001101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001101000_0 : Blocks := edgeBlocks% "full/vectors/00010001101000-V-0000.bin"
noncomputable def vp00010001101000 : Blocks := vp00010001101000_0
theorem coverp00010001101000 : Covers (-563761639/500000 : ℚ) vp00010001101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000110100_0 : Blocks := edgeBlocks% "full/vectors/0001000110100-V-0000.bin"
noncomputable def vp0001000110100 : Blocks := vp0001000110100_0
private theorem bp00010001101000 : Branch 0 (-563761639/1000000 : ℚ) vp0001000110100 := by
  apply branch_left_normalized (c:=vp00010001101000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-563761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-563761639/500000 : ℚ) by norm_num]
  exact coverp00010001101000
private noncomputable def ep00010001101001_0 : Blocks := edgeBlocks% "full/vectors/00010001101001-E-0000.bin"
noncomputable def ep00010001101001 : Blocks := ep00010001101001_0
private theorem idp00010001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000110100.list =
    C ((2:ℤ)^65) * horner X vp00010001101001.list + horner X ep00010001101001.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001101001 : Branch 1 (-563761639/1000000 : ℚ) vp0001000110100 := by
  apply branch_checked idp00010001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-563761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-564261639/500000 : ℚ) by norm_num]
  exact coverp00010001101001
theorem coverp0001000110100 : Covers (-563761639/1000000 : ℚ) vp0001000110100 := join_branches bp00010001101000 bp00010001101001
private noncomputable def vp000100011010_0 : Blocks := edgeBlocks% "full/vectors/000100011010-V-0000.bin"
noncomputable def vp000100011010 : Blocks := vp000100011010_0
private theorem bp0001000110100 : Branch 0 (-563761639/2000000 : ℚ) vp000100011010 := by
  apply branch_left_normalized (c:=vp0001000110100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-563761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-563761639/1000000 : ℚ) by norm_num]
  exact coverp0001000110100
private noncomputable def ep0001000110101_0 : Blocks := edgeBlocks% "full/vectors/0001000110101-E-0000.bin"
noncomputable def ep0001000110101 : Blocks := ep0001000110101_0
private theorem idp0001000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100011010.list =
    C ((2:ℤ)^111) * horner X vp0001000110101.list + horner X ep0001000110101.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000110101 : Branch 1 (-563761639/2000000 : ℚ) vp000100011010 := by
  apply branch_checked idp0001000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-563761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-564761639/1000000 : ℚ) by norm_num]
  exact coverp0001000110101
theorem coverp000100011010 : Covers (-563761639/2000000 : ℚ) vp000100011010 := join_branches bp0001000110100 bp0001000110101
private noncomputable def vp00010001101_0 : Blocks := edgeBlocks% "full/vectors/00010001101-V-0000.bin"
private noncomputable def vp00010001101_1 : Blocks := edgeBlocks% "full/vectors/00010001101-V-0001.bin"
noncomputable def vp00010001101 : Blocks := (Blocks.join vp00010001101_0 vp00010001101_1)
private theorem bp000100011010 : Branch 0 (-563761639/4000000 : ℚ) vp00010001101 := by
  apply branch_left_normalized (c:=vp000100011010) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-563761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-563761639/2000000 : ℚ) by norm_num]
  exact coverp000100011010
private noncomputable def ep000100011011_0 : Blocks := edgeBlocks% "full/vectors/000100011011-E-0000.bin"
private noncomputable def ep000100011011_1 : Blocks := edgeBlocks% "full/vectors/000100011011-E-0001.bin"
noncomputable def ep000100011011 : Blocks := (Blocks.join ep000100011011_0 ep000100011011_1)
private theorem idp000100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010001101.list =
    C ((2:ℤ)^203) * horner X vp000100011011.list + horner X ep000100011011.list := by
  exact edge_identity (B := (2:ℤ)^378) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100011011 : Branch 1 (-563761639/4000000 : ℚ) vp00010001101 := by
  apply branch_checked idp000100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-563761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-565761639/2000000 : ℚ) by norm_num]
  exact coverp000100011011
theorem coverp00010001101 : Covers (-563761639/4000000 : ℚ) vp00010001101 := join_branches bp000100011010 bp000100011011
private noncomputable def vp00010001100111_0 : Blocks := edgeBlocks% "full/vectors/00010001100111-V-0000.bin"
noncomputable def vp00010001100111 : Blocks := vp00010001100111_0
theorem coverp00010001100111 : Covers (-563261639/500000 : ℚ) vp00010001100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001100110_0 : Blocks := edgeBlocks% "full/vectors/00010001100110-V-0000.bin"
noncomputable def vp00010001100110 : Blocks := vp00010001100110_0
theorem coverp00010001100110 : Covers (-562761639/500000 : ℚ) vp00010001100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000110011_0 : Blocks := edgeBlocks% "full/vectors/0001000110011-V-0000.bin"
noncomputable def vp0001000110011 : Blocks := vp0001000110011_0
private theorem bp00010001100110 : Branch 0 (-562761639/1000000 : ℚ) vp0001000110011 := by
  apply branch_left_normalized (c:=vp00010001100110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-562761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-562761639/500000 : ℚ) by norm_num]
  exact coverp00010001100110
private noncomputable def ep00010001100111_0 : Blocks := edgeBlocks% "full/vectors/00010001100111-E-0000.bin"
noncomputable def ep00010001100111 : Blocks := ep00010001100111_0
private theorem idp00010001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000110011.list =
    C ((2:ℤ)^65) * horner X vp00010001100111.list + horner X ep00010001100111.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001100111 : Branch 1 (-562761639/1000000 : ℚ) vp0001000110011 := by
  apply branch_checked idp00010001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-562761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-563261639/500000 : ℚ) by norm_num]
  exact coverp00010001100111
theorem coverp0001000110011 : Covers (-562761639/1000000 : ℚ) vp0001000110011 := join_branches bp00010001100110 bp00010001100111
private noncomputable def vp00010001100101_0 : Blocks := edgeBlocks% "full/vectors/00010001100101-V-0000.bin"
noncomputable def vp00010001100101 : Blocks := vp00010001100101_0
theorem coverp00010001100101 : Covers (-562261639/500000 : ℚ) vp00010001100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001100100_0 : Blocks := edgeBlocks% "full/vectors/00010001100100-V-0000.bin"
noncomputable def vp00010001100100 : Blocks := vp00010001100100_0
theorem coverp00010001100100 : Covers (-561761639/500000 : ℚ) vp00010001100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000110010_0 : Blocks := edgeBlocks% "full/vectors/0001000110010-V-0000.bin"
noncomputable def vp0001000110010 : Blocks := vp0001000110010_0
private theorem bp00010001100100 : Branch 0 (-561761639/1000000 : ℚ) vp0001000110010 := by
  apply branch_left_normalized (c:=vp00010001100100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-561761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-561761639/500000 : ℚ) by norm_num]
  exact coverp00010001100100
private noncomputable def ep00010001100101_0 : Blocks := edgeBlocks% "full/vectors/00010001100101-E-0000.bin"
noncomputable def ep00010001100101 : Blocks := ep00010001100101_0
private theorem idp00010001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000110010.list =
    C ((2:ℤ)^65) * horner X vp00010001100101.list + horner X ep00010001100101.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001100101 : Branch 1 (-561761639/1000000 : ℚ) vp0001000110010 := by
  apply branch_checked idp00010001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-561761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-562261639/500000 : ℚ) by norm_num]
  exact coverp00010001100101
theorem coverp0001000110010 : Covers (-561761639/1000000 : ℚ) vp0001000110010 := join_branches bp00010001100100 bp00010001100101
private noncomputable def vp000100011001_0 : Blocks := edgeBlocks% "full/vectors/000100011001-V-0000.bin"
noncomputable def vp000100011001 : Blocks := vp000100011001_0
private theorem bp0001000110010 : Branch 0 (-561761639/2000000 : ℚ) vp000100011001 := by
  apply branch_left_normalized (c:=vp0001000110010) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-561761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-561761639/1000000 : ℚ) by norm_num]
  exact coverp0001000110010
private noncomputable def ep0001000110011_0 : Blocks := edgeBlocks% "full/vectors/0001000110011-E-0000.bin"
noncomputable def ep0001000110011 : Blocks := ep0001000110011_0
private theorem idp0001000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100011001.list =
    C ((2:ℤ)^110) * horner X vp0001000110011.list + horner X ep0001000110011.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000110011 : Branch 1 (-561761639/2000000 : ℚ) vp000100011001 := by
  apply branch_checked idp0001000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-561761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-562761639/1000000 : ℚ) by norm_num]
  exact coverp0001000110011
theorem coverp000100011001 : Covers (-561761639/2000000 : ℚ) vp000100011001 := join_branches bp0001000110010 bp0001000110011
private noncomputable def vp00010001100011_0 : Blocks := edgeBlocks% "full/vectors/00010001100011-V-0000.bin"
noncomputable def vp00010001100011 : Blocks := vp00010001100011_0
theorem coverp00010001100011 : Covers (-561261639/500000 : ℚ) vp00010001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001100010_0 : Blocks := edgeBlocks% "full/vectors/00010001100010-V-0000.bin"
noncomputable def vp00010001100010 : Blocks := vp00010001100010_0
theorem coverp00010001100010 : Covers (-560761639/500000 : ℚ) vp00010001100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000110001_0 : Blocks := edgeBlocks% "full/vectors/0001000110001-V-0000.bin"
noncomputable def vp0001000110001 : Blocks := vp0001000110001_0
private theorem bp00010001100010 : Branch 0 (-560761639/1000000 : ℚ) vp0001000110001 := by
  apply branch_left_normalized (c:=vp00010001100010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-560761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-560761639/500000 : ℚ) by norm_num]
  exact coverp00010001100010
private noncomputable def ep00010001100011_0 : Blocks := edgeBlocks% "full/vectors/00010001100011-E-0000.bin"
noncomputable def ep00010001100011 : Blocks := ep00010001100011_0
private theorem idp00010001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000110001.list =
    C ((2:ℤ)^65) * horner X vp00010001100011.list + horner X ep00010001100011.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001100011 : Branch 1 (-560761639/1000000 : ℚ) vp0001000110001 := by
  apply branch_checked idp00010001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-560761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-561261639/500000 : ℚ) by norm_num]
  exact coverp00010001100011
theorem coverp0001000110001 : Covers (-560761639/1000000 : ℚ) vp0001000110001 := join_branches bp00010001100010 bp00010001100011
private noncomputable def vp00010001100001_0 : Blocks := edgeBlocks% "full/vectors/00010001100001-V-0000.bin"
noncomputable def vp00010001100001 : Blocks := vp00010001100001_0
theorem coverp00010001100001 : Covers (-560261639/500000 : ℚ) vp00010001100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001100000_0 : Blocks := edgeBlocks% "full/vectors/00010001100000-V-0000.bin"
noncomputable def vp00010001100000 : Blocks := vp00010001100000_0
theorem coverp00010001100000 : Covers (-559761639/500000 : ℚ) vp00010001100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000110000_0 : Blocks := edgeBlocks% "full/vectors/0001000110000-V-0000.bin"
noncomputable def vp0001000110000 : Blocks := vp0001000110000_0
private theorem bp00010001100000 : Branch 0 (-559761639/1000000 : ℚ) vp0001000110000 := by
  apply branch_left_normalized (c:=vp00010001100000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-559761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-559761639/500000 : ℚ) by norm_num]
  exact coverp00010001100000
private noncomputable def ep00010001100001_0 : Blocks := edgeBlocks% "full/vectors/00010001100001-E-0000.bin"
noncomputable def ep00010001100001 : Blocks := ep00010001100001_0
private theorem idp00010001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000110000.list =
    C ((2:ℤ)^66) * horner X vp00010001100001.list + horner X ep00010001100001.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001100001 : Branch 1 (-559761639/1000000 : ℚ) vp0001000110000 := by
  apply branch_checked idp00010001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-559761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-560261639/500000 : ℚ) by norm_num]
  exact coverp00010001100001
theorem coverp0001000110000 : Covers (-559761639/1000000 : ℚ) vp0001000110000 := join_branches bp00010001100000 bp00010001100001
private noncomputable def vp000100011000_0 : Blocks := edgeBlocks% "full/vectors/000100011000-V-0000.bin"
noncomputable def vp000100011000 : Blocks := vp000100011000_0
private theorem bp0001000110000 : Branch 0 (-559761639/2000000 : ℚ) vp000100011000 := by
  apply branch_left_normalized (c:=vp0001000110000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-559761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-559761639/1000000 : ℚ) by norm_num]
  exact coverp0001000110000
private noncomputable def ep0001000110001_0 : Blocks := edgeBlocks% "full/vectors/0001000110001-E-0000.bin"
noncomputable def ep0001000110001 : Blocks := ep0001000110001_0
private theorem idp0001000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100011000.list =
    C ((2:ℤ)^112) * horner X vp0001000110001.list + horner X ep0001000110001.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000110001 : Branch 1 (-559761639/2000000 : ℚ) vp000100011000 := by
  apply branch_checked idp0001000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-559761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-560761639/1000000 : ℚ) by norm_num]
  exact coverp0001000110001
theorem coverp000100011000 : Covers (-559761639/2000000 : ℚ) vp000100011000 := join_branches bp0001000110000 bp0001000110001
private noncomputable def vp00010001100_0 : Blocks := edgeBlocks% "full/vectors/00010001100-V-0000.bin"
private noncomputable def vp00010001100_1 : Blocks := edgeBlocks% "full/vectors/00010001100-V-0001.bin"
noncomputable def vp00010001100 : Blocks := (Blocks.join vp00010001100_0 vp00010001100_1)
private theorem bp000100011000 : Branch 0 (-559761639/4000000 : ℚ) vp00010001100 := by
  apply branch_left_normalized (c:=vp000100011000) (k:=0) (m:=105) (by decide +kernel)
  rw [show 2*(-559761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-559761639/2000000 : ℚ) by norm_num]
  exact coverp000100011000
private noncomputable def ep000100011001_0 : Blocks := edgeBlocks% "full/vectors/000100011001-E-0000.bin"
private noncomputable def ep000100011001_1 : Blocks := edgeBlocks% "full/vectors/000100011001-E-0001.bin"
noncomputable def ep000100011001 : Blocks := (Blocks.join ep000100011001_0 ep000100011001_1)
private theorem idp000100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010001100.list =
    C ((2:ℤ)^202) * horner X vp000100011001.list + horner X ep000100011001.list := by
  exact edge_identity (B := (2:ℤ)^380) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100011001 : Branch 1 (-559761639/4000000 : ℚ) vp00010001100 := by
  apply branch_checked idp000100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-559761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-561761639/2000000 : ℚ) by norm_num]
  exact coverp000100011001
theorem coverp00010001100 : Covers (-559761639/4000000 : ℚ) vp00010001100 := join_branches bp000100011000 bp000100011001
private noncomputable def vp0001000110_0 : Blocks := edgeBlocks% "full/vectors/0001000110-V-0000.bin"
private noncomputable def vp0001000110_1 : Blocks := edgeBlocks% "full/vectors/0001000110-V-0001.bin"
private noncomputable def vp0001000110_2 : Blocks := edgeBlocks% "full/vectors/0001000110-V-0002.bin"
noncomputable def vp0001000110 : Blocks := (Blocks.join vp0001000110_0 (Blocks.join vp0001000110_1 vp0001000110_2))
private theorem bp00010001100 : Branch 0 (-559761639/8000000 : ℚ) vp0001000110 := by
  apply branch_left_normalized (c:=vp00010001100) (k:=0) (m:=189) (by decide +kernel)
  rw [show 2*(-559761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-559761639/4000000 : ℚ) by norm_num]
  exact coverp00010001100
private noncomputable def ep00010001101_0 : Blocks := edgeBlocks% "full/vectors/00010001101-E-0000.bin"
private noncomputable def ep00010001101_1 : Blocks := edgeBlocks% "full/vectors/00010001101-E-0001.bin"
private noncomputable def ep00010001101_2 : Blocks := edgeBlocks% "full/vectors/00010001101-E-0002.bin"
noncomputable def ep00010001101 : Blocks := (Blocks.join ep00010001101_0 (Blocks.join ep00010001101_1 ep00010001101_2))
private theorem idp00010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000110.list =
    C ((2:ℤ)^378) * horner X vp00010001101.list + horner X ep00010001101.list := by
  exact edge_identity (B := (2:ℤ)^633) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001101 : Branch 1 (-559761639/8000000 : ℚ) vp0001000110 := by
  apply branch_checked idp00010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-559761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-563761639/4000000 : ℚ) by norm_num]
  exact coverp00010001101
theorem coverp0001000110 : Covers (-559761639/8000000 : ℚ) vp0001000110 := join_branches bp00010001100 bp00010001101
private noncomputable def vp000100011_0 : Blocks := edgeBlocks% "full/vectors/000100011-V-0000.bin"
private noncomputable def vp000100011_1 : Blocks := edgeBlocks% "full/vectors/000100011-V-0001.bin"
private noncomputable def vp000100011_2 : Blocks := edgeBlocks% "full/vectors/000100011-V-0002.bin"
private noncomputable def vp000100011_3 : Blocks := edgeBlocks% "full/vectors/000100011-V-0003.bin"
private noncomputable def vp000100011_4 : Blocks := edgeBlocks% "full/vectors/000100011-V-0004.bin"
private noncomputable def vp000100011_5 : Blocks := edgeBlocks% "full/vectors/000100011-V-0005.bin"
noncomputable def vp000100011 : Blocks := (Blocks.join (Blocks.join vp000100011_0 (Blocks.join vp000100011_1 vp000100011_2)) (Blocks.join vp000100011_3 (Blocks.join vp000100011_4 vp000100011_5)))
private theorem bp0001000110 : Branch 0 (-559761639/16000000 : ℚ) vp000100011 := by
  apply branch_left_normalized (c:=vp0001000110) (k:=0) (m:=354) (by decide +kernel)
  rw [show 2*(-559761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-559761639/8000000 : ℚ) by norm_num]
  exact coverp0001000110
private noncomputable def ep0001000111_0 : Blocks := edgeBlocks% "full/vectors/0001000111-E-0000.bin"
private noncomputable def ep0001000111_1 : Blocks := edgeBlocks% "full/vectors/0001000111-E-0001.bin"
private noncomputable def ep0001000111_2 : Blocks := edgeBlocks% "full/vectors/0001000111-E-0002.bin"
private noncomputable def ep0001000111_3 : Blocks := edgeBlocks% "full/vectors/0001000111-E-0003.bin"
private noncomputable def ep0001000111_4 : Blocks := edgeBlocks% "full/vectors/0001000111-E-0004.bin"
private noncomputable def ep0001000111_5 : Blocks := edgeBlocks% "full/vectors/0001000111-E-0005.bin"
noncomputable def ep0001000111 : Blocks := (Blocks.join (Blocks.join ep0001000111_0 (Blocks.join ep0001000111_1 ep0001000111_2)) (Blocks.join ep0001000111_3 (Blocks.join ep0001000111_4 ep0001000111_5)))
private theorem idp0001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100011.list =
    C ((2:ℤ)^734) * horner X vp0001000111.list + horner X ep0001000111.list := by
  exact edge_identity (B := (2:ℤ)^1135) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000111 : Branch 1 (-559761639/16000000 : ℚ) vp000100011 := by
  apply branch_checked idp0001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-559761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-567761639/8000000 : ℚ) by norm_num]
  exact coverp0001000111
theorem coverp000100011 : Covers (-559761639/16000000 : ℚ) vp000100011 := join_branches bp0001000110 bp0001000111
private noncomputable def vp00010001011111_0 : Blocks := edgeBlocks% "full/vectors/00010001011111-V-0000.bin"
noncomputable def vp00010001011111 : Blocks := vp00010001011111_0
theorem coverp00010001011111 : Covers (-559261639/500000 : ℚ) vp00010001011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001011110_0 : Blocks := edgeBlocks% "full/vectors/00010001011110-V-0000.bin"
noncomputable def vp00010001011110 : Blocks := vp00010001011110_0
theorem coverp00010001011110 : Covers (-558761639/500000 : ℚ) vp00010001011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000101111_0 : Blocks := edgeBlocks% "full/vectors/0001000101111-V-0000.bin"
noncomputable def vp0001000101111 : Blocks := vp0001000101111_0
private theorem bp00010001011110 : Branch 0 (-558761639/1000000 : ℚ) vp0001000101111 := by
  apply branch_left_normalized (c:=vp00010001011110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-558761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-558761639/500000 : ℚ) by norm_num]
  exact coverp00010001011110
private noncomputable def ep00010001011111_0 : Blocks := edgeBlocks% "full/vectors/00010001011111-E-0000.bin"
noncomputable def ep00010001011111 : Blocks := ep00010001011111_0
private theorem idp00010001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000101111.list =
    C ((2:ℤ)^66) * horner X vp00010001011111.list + horner X ep00010001011111.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001011111 : Branch 1 (-558761639/1000000 : ℚ) vp0001000101111 := by
  apply branch_checked idp00010001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-558761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-559261639/500000 : ℚ) by norm_num]
  exact coverp00010001011111
theorem coverp0001000101111 : Covers (-558761639/1000000 : ℚ) vp0001000101111 := join_branches bp00010001011110 bp00010001011111
private noncomputable def vp00010001011101_0 : Blocks := edgeBlocks% "full/vectors/00010001011101-V-0000.bin"
noncomputable def vp00010001011101 : Blocks := vp00010001011101_0
theorem coverp00010001011101 : Covers (-558261639/500000 : ℚ) vp00010001011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001011100_0 : Blocks := edgeBlocks% "full/vectors/00010001011100-V-0000.bin"
noncomputable def vp00010001011100 : Blocks := vp00010001011100_0
theorem coverp00010001011100 : Covers (-557761639/500000 : ℚ) vp00010001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000101110_0 : Blocks := edgeBlocks% "full/vectors/0001000101110-V-0000.bin"
noncomputable def vp0001000101110 : Blocks := vp0001000101110_0
private theorem bp00010001011100 : Branch 0 (-557761639/1000000 : ℚ) vp0001000101110 := by
  apply branch_left_normalized (c:=vp00010001011100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-557761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-557761639/500000 : ℚ) by norm_num]
  exact coverp00010001011100
private noncomputable def ep00010001011101_0 : Blocks := edgeBlocks% "full/vectors/00010001011101-E-0000.bin"
noncomputable def ep00010001011101 : Blocks := ep00010001011101_0
private theorem idp00010001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000101110.list =
    C ((2:ℤ)^65) * horner X vp00010001011101.list + horner X ep00010001011101.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001011101 : Branch 1 (-557761639/1000000 : ℚ) vp0001000101110 := by
  apply branch_checked idp00010001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-557761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-558261639/500000 : ℚ) by norm_num]
  exact coverp00010001011101
theorem coverp0001000101110 : Covers (-557761639/1000000 : ℚ) vp0001000101110 := join_branches bp00010001011100 bp00010001011101
private noncomputable def vp000100010111_0 : Blocks := edgeBlocks% "full/vectors/000100010111-V-0000.bin"
noncomputable def vp000100010111 : Blocks := vp000100010111_0
private theorem bp0001000101110 : Branch 0 (-557761639/2000000 : ℚ) vp000100010111 := by
  apply branch_left_normalized (c:=vp0001000101110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-557761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-557761639/1000000 : ℚ) by norm_num]
  exact coverp0001000101110
private noncomputable def ep0001000101111_0 : Blocks := edgeBlocks% "full/vectors/0001000101111-E-0000.bin"
noncomputable def ep0001000101111 : Blocks := ep0001000101111_0
private theorem idp0001000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100010111.list =
    C ((2:ℤ)^111) * horner X vp0001000101111.list + horner X ep0001000101111.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000101111 : Branch 1 (-557761639/2000000 : ℚ) vp000100010111 := by
  apply branch_checked idp0001000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-557761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-558761639/1000000 : ℚ) by norm_num]
  exact coverp0001000101111
theorem coverp000100010111 : Covers (-557761639/2000000 : ℚ) vp000100010111 := join_branches bp0001000101110 bp0001000101111
private noncomputable def vp00010001011011_0 : Blocks := edgeBlocks% "full/vectors/00010001011011-V-0000.bin"
noncomputable def vp00010001011011 : Blocks := vp00010001011011_0
theorem coverp00010001011011 : Covers (-557261639/500000 : ℚ) vp00010001011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001011010_0 : Blocks := edgeBlocks% "full/vectors/00010001011010-V-0000.bin"
noncomputable def vp00010001011010 : Blocks := vp00010001011010_0
theorem coverp00010001011010 : Covers (-556761639/500000 : ℚ) vp00010001011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000101101_0 : Blocks := edgeBlocks% "full/vectors/0001000101101-V-0000.bin"
noncomputable def vp0001000101101 : Blocks := vp0001000101101_0
private theorem bp00010001011010 : Branch 0 (-556761639/1000000 : ℚ) vp0001000101101 := by
  apply branch_left_normalized (c:=vp00010001011010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-556761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-556761639/500000 : ℚ) by norm_num]
  exact coverp00010001011010
private noncomputable def ep00010001011011_0 : Blocks := edgeBlocks% "full/vectors/00010001011011-E-0000.bin"
noncomputable def ep00010001011011 : Blocks := ep00010001011011_0
private theorem idp00010001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000101101.list =
    C ((2:ℤ)^66) * horner X vp00010001011011.list + horner X ep00010001011011.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001011011 : Branch 1 (-556761639/1000000 : ℚ) vp0001000101101 := by
  apply branch_checked idp00010001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-556761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-557261639/500000 : ℚ) by norm_num]
  exact coverp00010001011011
theorem coverp0001000101101 : Covers (-556761639/1000000 : ℚ) vp0001000101101 := join_branches bp00010001011010 bp00010001011011
private noncomputable def vp00010001011001_0 : Blocks := edgeBlocks% "full/vectors/00010001011001-V-0000.bin"
noncomputable def vp00010001011001 : Blocks := vp00010001011001_0
theorem coverp00010001011001 : Covers (-556261639/500000 : ℚ) vp00010001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001011000_0 : Blocks := edgeBlocks% "full/vectors/00010001011000-V-0000.bin"
noncomputable def vp00010001011000 : Blocks := vp00010001011000_0
theorem coverp00010001011000 : Covers (-555761639/500000 : ℚ) vp00010001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000101100_0 : Blocks := edgeBlocks% "full/vectors/0001000101100-V-0000.bin"
noncomputable def vp0001000101100 : Blocks := vp0001000101100_0
private theorem bp00010001011000 : Branch 0 (-555761639/1000000 : ℚ) vp0001000101100 := by
  apply branch_left_normalized (c:=vp00010001011000) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-555761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-555761639/500000 : ℚ) by norm_num]
  exact coverp00010001011000
private noncomputable def ep00010001011001_0 : Blocks := edgeBlocks% "full/vectors/00010001011001-E-0000.bin"
noncomputable def ep00010001011001 : Blocks := ep00010001011001_0
private theorem idp00010001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000101100.list =
    C ((2:ℤ)^66) * horner X vp00010001011001.list + horner X ep00010001011001.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001011001 : Branch 1 (-555761639/1000000 : ℚ) vp0001000101100 := by
  apply branch_checked idp00010001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-555761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-556261639/500000 : ℚ) by norm_num]
  exact coverp00010001011001
theorem coverp0001000101100 : Covers (-555761639/1000000 : ℚ) vp0001000101100 := join_branches bp00010001011000 bp00010001011001
private noncomputable def vp000100010110_0 : Blocks := edgeBlocks% "full/vectors/000100010110-V-0000.bin"
noncomputable def vp000100010110 : Blocks := vp000100010110_0
private theorem bp0001000101100 : Branch 0 (-555761639/2000000 : ℚ) vp000100010110 := by
  apply branch_left_normalized (c:=vp0001000101100) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-555761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-555761639/1000000 : ℚ) by norm_num]
  exact coverp0001000101100
private noncomputable def ep0001000101101_0 : Blocks := edgeBlocks% "full/vectors/0001000101101-E-0000.bin"
noncomputable def ep0001000101101 : Blocks := ep0001000101101_0
private theorem idp0001000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100010110.list =
    C ((2:ℤ)^112) * horner X vp0001000101101.list + horner X ep0001000101101.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000101101 : Branch 1 (-555761639/2000000 : ℚ) vp000100010110 := by
  apply branch_checked idp0001000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-555761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-556761639/1000000 : ℚ) by norm_num]
  exact coverp0001000101101
theorem coverp000100010110 : Covers (-555761639/2000000 : ℚ) vp000100010110 := join_branches bp0001000101100 bp0001000101101
private noncomputable def vp00010001011_0 : Blocks := edgeBlocks% "full/vectors/00010001011-V-0000.bin"
private noncomputable def vp00010001011_1 : Blocks := edgeBlocks% "full/vectors/00010001011-V-0001.bin"
noncomputable def vp00010001011 : Blocks := (Blocks.join vp00010001011_0 vp00010001011_1)
private theorem bp000100010110 : Branch 0 (-555761639/4000000 : ℚ) vp00010001011 := by
  apply branch_left_normalized (c:=vp000100010110) (k:=0) (m:=105) (by decide +kernel)
  rw [show 2*(-555761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-555761639/2000000 : ℚ) by norm_num]
  exact coverp000100010110
private noncomputable def ep000100010111_0 : Blocks := edgeBlocks% "full/vectors/000100010111-E-0000.bin"
private noncomputable def ep000100010111_1 : Blocks := edgeBlocks% "full/vectors/000100010111-E-0001.bin"
noncomputable def ep000100010111 : Blocks := (Blocks.join ep000100010111_0 ep000100010111_1)
private theorem idp000100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010001011.list =
    C ((2:ℤ)^201) * horner X vp000100010111.list + horner X ep000100010111.list := by
  exact edge_identity (B := (2:ℤ)^380) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100010111 : Branch 1 (-555761639/4000000 : ℚ) vp00010001011 := by
  apply branch_checked idp000100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-555761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-557761639/2000000 : ℚ) by norm_num]
  exact coverp000100010111
theorem coverp00010001011 : Covers (-555761639/4000000 : ℚ) vp00010001011 := join_branches bp000100010110 bp000100010111
private noncomputable def vp00010001010111_0 : Blocks := edgeBlocks% "full/vectors/00010001010111-V-0000.bin"
noncomputable def vp00010001010111 : Blocks := vp00010001010111_0
theorem coverp00010001010111 : Covers (-555261639/500000 : ℚ) vp00010001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001010110_0 : Blocks := edgeBlocks% "full/vectors/00010001010110-V-0000.bin"
noncomputable def vp00010001010110 : Blocks := vp00010001010110_0
theorem coverp00010001010110 : Covers (-554761639/500000 : ℚ) vp00010001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000101011_0 : Blocks := edgeBlocks% "full/vectors/0001000101011-V-0000.bin"
noncomputable def vp0001000101011 : Blocks := vp0001000101011_0
private theorem bp00010001010110 : Branch 0 (-554761639/1000000 : ℚ) vp0001000101011 := by
  apply branch_left_normalized (c:=vp00010001010110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-554761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-554761639/500000 : ℚ) by norm_num]
  exact coverp00010001010110
private noncomputable def ep00010001010111_0 : Blocks := edgeBlocks% "full/vectors/00010001010111-E-0000.bin"
noncomputable def ep00010001010111 : Blocks := ep00010001010111_0
private theorem idp00010001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000101011.list =
    C ((2:ℤ)^65) * horner X vp00010001010111.list + horner X ep00010001010111.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001010111 : Branch 1 (-554761639/1000000 : ℚ) vp0001000101011 := by
  apply branch_checked idp00010001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-554761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-555261639/500000 : ℚ) by norm_num]
  exact coverp00010001010111
theorem coverp0001000101011 : Covers (-554761639/1000000 : ℚ) vp0001000101011 := join_branches bp00010001010110 bp00010001010111
private noncomputable def vp00010001010101_0 : Blocks := edgeBlocks% "full/vectors/00010001010101-V-0000.bin"
noncomputable def vp00010001010101 : Blocks := vp00010001010101_0
theorem coverp00010001010101 : Covers (-554261639/500000 : ℚ) vp00010001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001010100_0 : Blocks := edgeBlocks% "full/vectors/00010001010100-V-0000.bin"
noncomputable def vp00010001010100 : Blocks := vp00010001010100_0
theorem coverp00010001010100 : Covers (-553761639/500000 : ℚ) vp00010001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000101010_0 : Blocks := edgeBlocks% "full/vectors/0001000101010-V-0000.bin"
noncomputable def vp0001000101010 : Blocks := vp0001000101010_0
private theorem bp00010001010100 : Branch 0 (-553761639/1000000 : ℚ) vp0001000101010 := by
  apply branch_left_normalized (c:=vp00010001010100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-553761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-553761639/500000 : ℚ) by norm_num]
  exact coverp00010001010100
private noncomputable def ep00010001010101_0 : Blocks := edgeBlocks% "full/vectors/00010001010101-E-0000.bin"
noncomputable def ep00010001010101 : Blocks := ep00010001010101_0
private theorem idp00010001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000101010.list =
    C ((2:ℤ)^66) * horner X vp00010001010101.list + horner X ep00010001010101.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001010101 : Branch 1 (-553761639/1000000 : ℚ) vp0001000101010 := by
  apply branch_checked idp00010001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-553761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-554261639/500000 : ℚ) by norm_num]
  exact coverp00010001010101
theorem coverp0001000101010 : Covers (-553761639/1000000 : ℚ) vp0001000101010 := join_branches bp00010001010100 bp00010001010101
private noncomputable def vp000100010101_0 : Blocks := edgeBlocks% "full/vectors/000100010101-V-0000.bin"
noncomputable def vp000100010101 : Blocks := vp000100010101_0
private theorem bp0001000101010 : Branch 0 (-553761639/2000000 : ℚ) vp000100010101 := by
  apply branch_left_normalized (c:=vp0001000101010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-553761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-553761639/1000000 : ℚ) by norm_num]
  exact coverp0001000101010
private noncomputable def ep0001000101011_0 : Blocks := edgeBlocks% "full/vectors/0001000101011-E-0000.bin"
noncomputable def ep0001000101011 : Blocks := ep0001000101011_0
private theorem idp0001000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100010101.list =
    C ((2:ℤ)^112) * horner X vp0001000101011.list + horner X ep0001000101011.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000101011 : Branch 1 (-553761639/2000000 : ℚ) vp000100010101 := by
  apply branch_checked idp0001000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-553761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-554761639/1000000 : ℚ) by norm_num]
  exact coverp0001000101011
theorem coverp000100010101 : Covers (-553761639/2000000 : ℚ) vp000100010101 := join_branches bp0001000101010 bp0001000101011
private noncomputable def vp00010001010011_0 : Blocks := edgeBlocks% "full/vectors/00010001010011-V-0000.bin"
noncomputable def vp00010001010011 : Blocks := vp00010001010011_0
theorem coverp00010001010011 : Covers (-553261639/500000 : ℚ) vp00010001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001010010_0 : Blocks := edgeBlocks% "full/vectors/00010001010010-V-0000.bin"
noncomputable def vp00010001010010 : Blocks := vp00010001010010_0
theorem coverp00010001010010 : Covers (-552761639/500000 : ℚ) vp00010001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000101001_0 : Blocks := edgeBlocks% "full/vectors/0001000101001-V-0000.bin"
noncomputable def vp0001000101001 : Blocks := vp0001000101001_0
private theorem bp00010001010010 : Branch 0 (-552761639/1000000 : ℚ) vp0001000101001 := by
  apply branch_left_normalized (c:=vp00010001010010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-552761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-552761639/500000 : ℚ) by norm_num]
  exact coverp00010001010010
private noncomputable def ep00010001010011_0 : Blocks := edgeBlocks% "full/vectors/00010001010011-E-0000.bin"
noncomputable def ep00010001010011 : Blocks := ep00010001010011_0
private theorem idp00010001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000101001.list =
    C ((2:ℤ)^66) * horner X vp00010001010011.list + horner X ep00010001010011.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001010011 : Branch 1 (-552761639/1000000 : ℚ) vp0001000101001 := by
  apply branch_checked idp00010001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-552761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-553261639/500000 : ℚ) by norm_num]
  exact coverp00010001010011
theorem coverp0001000101001 : Covers (-552761639/1000000 : ℚ) vp0001000101001 := join_branches bp00010001010010 bp00010001010011
private noncomputable def vp00010001010001_0 : Blocks := edgeBlocks% "full/vectors/00010001010001-V-0000.bin"
noncomputable def vp00010001010001 : Blocks := vp00010001010001_0
theorem coverp00010001010001 : Covers (-552261639/500000 : ℚ) vp00010001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001010000_0 : Blocks := edgeBlocks% "full/vectors/00010001010000-V-0000.bin"
noncomputable def vp00010001010000 : Blocks := vp00010001010000_0
theorem coverp00010001010000 : Covers (-551761639/500000 : ℚ) vp00010001010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000101000_0 : Blocks := edgeBlocks% "full/vectors/0001000101000-V-0000.bin"
noncomputable def vp0001000101000 : Blocks := vp0001000101000_0
private theorem bp00010001010000 : Branch 0 (-551761639/1000000 : ℚ) vp0001000101000 := by
  apply branch_left_normalized (c:=vp00010001010000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-551761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-551761639/500000 : ℚ) by norm_num]
  exact coverp00010001010000
private noncomputable def ep00010001010001_0 : Blocks := edgeBlocks% "full/vectors/00010001010001-E-0000.bin"
noncomputable def ep00010001010001 : Blocks := ep00010001010001_0
private theorem idp00010001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000101000.list =
    C ((2:ℤ)^66) * horner X vp00010001010001.list + horner X ep00010001010001.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001010001 : Branch 1 (-551761639/1000000 : ℚ) vp0001000101000 := by
  apply branch_checked idp00010001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-551761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-552261639/500000 : ℚ) by norm_num]
  exact coverp00010001010001
theorem coverp0001000101000 : Covers (-551761639/1000000 : ℚ) vp0001000101000 := join_branches bp00010001010000 bp00010001010001
private noncomputable def vp000100010100_0 : Blocks := edgeBlocks% "full/vectors/000100010100-V-0000.bin"
noncomputable def vp000100010100 : Blocks := vp000100010100_0
private theorem bp0001000101000 : Branch 0 (-551761639/2000000 : ℚ) vp000100010100 := by
  apply branch_left_normalized (c:=vp0001000101000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-551761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-551761639/1000000 : ℚ) by norm_num]
  exact coverp0001000101000
private noncomputable def ep0001000101001_0 : Blocks := edgeBlocks% "full/vectors/0001000101001-E-0000.bin"
noncomputable def ep0001000101001 : Blocks := ep0001000101001_0
private theorem idp0001000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100010100.list =
    C ((2:ℤ)^112) * horner X vp0001000101001.list + horner X ep0001000101001.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000101001 : Branch 1 (-551761639/2000000 : ℚ) vp000100010100 := by
  apply branch_checked idp0001000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-551761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-552761639/1000000 : ℚ) by norm_num]
  exact coverp0001000101001
theorem coverp000100010100 : Covers (-551761639/2000000 : ℚ) vp000100010100 := join_branches bp0001000101000 bp0001000101001
private noncomputable def vp00010001010_0 : Blocks := edgeBlocks% "full/vectors/00010001010-V-0000.bin"
private noncomputable def vp00010001010_1 : Blocks := edgeBlocks% "full/vectors/00010001010-V-0001.bin"
noncomputable def vp00010001010 : Blocks := (Blocks.join vp00010001010_0 vp00010001010_1)
private theorem bp000100010100 : Branch 0 (-551761639/4000000 : ℚ) vp00010001010 := by
  apply branch_left_normalized (c:=vp000100010100) (k:=0) (m:=105) (by decide +kernel)
  rw [show 2*(-551761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-551761639/2000000 : ℚ) by norm_num]
  exact coverp000100010100
private noncomputable def ep000100010101_0 : Blocks := edgeBlocks% "full/vectors/000100010101-E-0000.bin"
private noncomputable def ep000100010101_1 : Blocks := edgeBlocks% "full/vectors/000100010101-E-0001.bin"
noncomputable def ep000100010101 : Blocks := (Blocks.join ep000100010101_0 ep000100010101_1)
private theorem idp000100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010001010.list =
    C ((2:ℤ)^203) * horner X vp000100010101.list + horner X ep000100010101.list := by
  exact edge_identity (B := (2:ℤ)^382) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100010101 : Branch 1 (-551761639/4000000 : ℚ) vp00010001010 := by
  apply branch_checked idp000100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-551761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-553761639/2000000 : ℚ) by norm_num]
  exact coverp000100010101
theorem coverp00010001010 : Covers (-551761639/4000000 : ℚ) vp00010001010 := join_branches bp000100010100 bp000100010101
private noncomputable def vp0001000101_0 : Blocks := edgeBlocks% "full/vectors/0001000101-V-0000.bin"
private noncomputable def vp0001000101_1 : Blocks := edgeBlocks% "full/vectors/0001000101-V-0001.bin"
private noncomputable def vp0001000101_2 : Blocks := edgeBlocks% "full/vectors/0001000101-V-0002.bin"
noncomputable def vp0001000101 : Blocks := (Blocks.join vp0001000101_0 (Blocks.join vp0001000101_1 vp0001000101_2))
private theorem bp00010001010 : Branch 0 (-551761639/8000000 : ℚ) vp0001000101 := by
  apply branch_left_normalized (c:=vp00010001010) (k:=0) (m:=190) (by decide +kernel)
  rw [show 2*(-551761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-551761639/4000000 : ℚ) by norm_num]
  exact coverp00010001010
private noncomputable def ep00010001011_0 : Blocks := edgeBlocks% "full/vectors/00010001011-E-0000.bin"
private noncomputable def ep00010001011_1 : Blocks := edgeBlocks% "full/vectors/00010001011-E-0001.bin"
private noncomputable def ep00010001011_2 : Blocks := edgeBlocks% "full/vectors/00010001011-E-0002.bin"
noncomputable def ep00010001011 : Blocks := (Blocks.join ep00010001011_0 (Blocks.join ep00010001011_1 ep00010001011_2))
private theorem idp00010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000101.list =
    C ((2:ℤ)^381) * horner X vp00010001011.list + horner X ep00010001011.list := by
  exact edge_identity (B := (2:ℤ)^637) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001011 : Branch 1 (-551761639/8000000 : ℚ) vp0001000101 := by
  apply branch_checked idp00010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-551761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-555761639/4000000 : ℚ) by norm_num]
  exact coverp00010001011
theorem coverp0001000101 : Covers (-551761639/8000000 : ℚ) vp0001000101 := join_branches bp00010001010 bp00010001011
private noncomputable def vp00010001001111_0 : Blocks := edgeBlocks% "full/vectors/00010001001111-V-0000.bin"
noncomputable def vp00010001001111 : Blocks := vp00010001001111_0
theorem coverp00010001001111 : Covers (-551261639/500000 : ℚ) vp00010001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001001110_0 : Blocks := edgeBlocks% "full/vectors/00010001001110-V-0000.bin"
noncomputable def vp00010001001110 : Blocks := vp00010001001110_0
theorem coverp00010001001110 : Covers (-550761639/500000 : ℚ) vp00010001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000100111_0 : Blocks := edgeBlocks% "full/vectors/0001000100111-V-0000.bin"
noncomputable def vp0001000100111 : Blocks := vp0001000100111_0
private theorem bp00010001001110 : Branch 0 (-550761639/1000000 : ℚ) vp0001000100111 := by
  apply branch_left_normalized (c:=vp00010001001110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-550761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-550761639/500000 : ℚ) by norm_num]
  exact coverp00010001001110
private noncomputable def ep00010001001111_0 : Blocks := edgeBlocks% "full/vectors/00010001001111-E-0000.bin"
noncomputable def ep00010001001111 : Blocks := ep00010001001111_0
private theorem idp00010001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000100111.list =
    C ((2:ℤ)^65) * horner X vp00010001001111.list + horner X ep00010001001111.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001001111 : Branch 1 (-550761639/1000000 : ℚ) vp0001000100111 := by
  apply branch_checked idp00010001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-550761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-551261639/500000 : ℚ) by norm_num]
  exact coverp00010001001111
theorem coverp0001000100111 : Covers (-550761639/1000000 : ℚ) vp0001000100111 := join_branches bp00010001001110 bp00010001001111
private noncomputable def vp00010001001101_0 : Blocks := edgeBlocks% "full/vectors/00010001001101-V-0000.bin"
noncomputable def vp00010001001101 : Blocks := vp00010001001101_0
theorem coverp00010001001101 : Covers (-550261639/500000 : ℚ) vp00010001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001001100_0 : Blocks := edgeBlocks% "full/vectors/00010001001100-V-0000.bin"
noncomputable def vp00010001001100 : Blocks := vp00010001001100_0
theorem coverp00010001001100 : Covers (-549761639/500000 : ℚ) vp00010001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000100110_0 : Blocks := edgeBlocks% "full/vectors/0001000100110-V-0000.bin"
noncomputable def vp0001000100110 : Blocks := vp0001000100110_0
private theorem bp00010001001100 : Branch 0 (-549761639/1000000 : ℚ) vp0001000100110 := by
  apply branch_left_normalized (c:=vp00010001001100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-549761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-549761639/500000 : ℚ) by norm_num]
  exact coverp00010001001100
private noncomputable def ep00010001001101_0 : Blocks := edgeBlocks% "full/vectors/00010001001101-E-0000.bin"
noncomputable def ep00010001001101 : Blocks := ep00010001001101_0
private theorem idp00010001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000100110.list =
    C ((2:ℤ)^66) * horner X vp00010001001101.list + horner X ep00010001001101.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001001101 : Branch 1 (-549761639/1000000 : ℚ) vp0001000100110 := by
  apply branch_checked idp00010001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-549761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-550261639/500000 : ℚ) by norm_num]
  exact coverp00010001001101
theorem coverp0001000100110 : Covers (-549761639/1000000 : ℚ) vp0001000100110 := join_branches bp00010001001100 bp00010001001101
private noncomputable def vp000100010011_0 : Blocks := edgeBlocks% "full/vectors/000100010011-V-0000.bin"
noncomputable def vp000100010011 : Blocks := vp000100010011_0
private theorem bp0001000100110 : Branch 0 (-549761639/2000000 : ℚ) vp000100010011 := by
  apply branch_left_normalized (c:=vp0001000100110) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-549761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-549761639/1000000 : ℚ) by norm_num]
  exact coverp0001000100110
private noncomputable def ep0001000100111_0 : Blocks := edgeBlocks% "full/vectors/0001000100111-E-0000.bin"
noncomputable def ep0001000100111 : Blocks := ep0001000100111_0
private theorem idp0001000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100010011.list =
    C ((2:ℤ)^112) * horner X vp0001000100111.list + horner X ep0001000100111.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000100111 : Branch 1 (-549761639/2000000 : ℚ) vp000100010011 := by
  apply branch_checked idp0001000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-549761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-550761639/1000000 : ℚ) by norm_num]
  exact coverp0001000100111
theorem coverp000100010011 : Covers (-549761639/2000000 : ℚ) vp000100010011 := join_branches bp0001000100110 bp0001000100111
private noncomputable def vp00010001001011_0 : Blocks := edgeBlocks% "full/vectors/00010001001011-V-0000.bin"
noncomputable def vp00010001001011 : Blocks := vp00010001001011_0
theorem coverp00010001001011 : Covers (-549261639/500000 : ℚ) vp00010001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001001010_0 : Blocks := edgeBlocks% "full/vectors/00010001001010-V-0000.bin"
noncomputable def vp00010001001010 : Blocks := vp00010001001010_0
theorem coverp00010001001010 : Covers (-548761639/500000 : ℚ) vp00010001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000100101_0 : Blocks := edgeBlocks% "full/vectors/0001000100101-V-0000.bin"
noncomputable def vp0001000100101 : Blocks := vp0001000100101_0
private theorem bp00010001001010 : Branch 0 (-548761639/1000000 : ℚ) vp0001000100101 := by
  apply branch_left_normalized (c:=vp00010001001010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-548761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-548761639/500000 : ℚ) by norm_num]
  exact coverp00010001001010
private noncomputable def ep00010001001011_0 : Blocks := edgeBlocks% "full/vectors/00010001001011-E-0000.bin"
noncomputable def ep00010001001011 : Blocks := ep00010001001011_0
private theorem idp00010001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000100101.list =
    C ((2:ℤ)^66) * horner X vp00010001001011.list + horner X ep00010001001011.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001001011 : Branch 1 (-548761639/1000000 : ℚ) vp0001000100101 := by
  apply branch_checked idp00010001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-548761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-549261639/500000 : ℚ) by norm_num]
  exact coverp00010001001011
theorem coverp0001000100101 : Covers (-548761639/1000000 : ℚ) vp0001000100101 := join_branches bp00010001001010 bp00010001001011
private noncomputable def vp00010001001001_0 : Blocks := edgeBlocks% "full/vectors/00010001001001-V-0000.bin"
noncomputable def vp00010001001001 : Blocks := vp00010001001001_0
theorem coverp00010001001001 : Covers (-548261639/500000 : ℚ) vp00010001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001001000_0 : Blocks := edgeBlocks% "full/vectors/00010001001000-V-0000.bin"
noncomputable def vp00010001001000 : Blocks := vp00010001001000_0
theorem coverp00010001001000 : Covers (-547761639/500000 : ℚ) vp00010001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000100100_0 : Blocks := edgeBlocks% "full/vectors/0001000100100-V-0000.bin"
noncomputable def vp0001000100100 : Blocks := vp0001000100100_0
private theorem bp00010001001000 : Branch 0 (-547761639/1000000 : ℚ) vp0001000100100 := by
  apply branch_left_normalized (c:=vp00010001001000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-547761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-547761639/500000 : ℚ) by norm_num]
  exact coverp00010001001000
private noncomputable def ep00010001001001_0 : Blocks := edgeBlocks% "full/vectors/00010001001001-E-0000.bin"
noncomputable def ep00010001001001 : Blocks := ep00010001001001_0
private theorem idp00010001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000100100.list =
    C ((2:ℤ)^66) * horner X vp00010001001001.list + horner X ep00010001001001.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001001001 : Branch 1 (-547761639/1000000 : ℚ) vp0001000100100 := by
  apply branch_checked idp00010001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-547761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-548261639/500000 : ℚ) by norm_num]
  exact coverp00010001001001
theorem coverp0001000100100 : Covers (-547761639/1000000 : ℚ) vp0001000100100 := join_branches bp00010001001000 bp00010001001001
private noncomputable def vp000100010010_0 : Blocks := edgeBlocks% "full/vectors/000100010010-V-0000.bin"
noncomputable def vp000100010010 : Blocks := vp000100010010_0
private theorem bp0001000100100 : Branch 0 (-547761639/2000000 : ℚ) vp000100010010 := by
  apply branch_left_normalized (c:=vp0001000100100) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-547761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-547761639/1000000 : ℚ) by norm_num]
  exact coverp0001000100100
private noncomputable def ep0001000100101_0 : Blocks := edgeBlocks% "full/vectors/0001000100101-E-0000.bin"
noncomputable def ep0001000100101 : Blocks := ep0001000100101_0
private theorem idp0001000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100010010.list =
    C ((2:ℤ)^112) * horner X vp0001000100101.list + horner X ep0001000100101.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000100101 : Branch 1 (-547761639/2000000 : ℚ) vp000100010010 := by
  apply branch_checked idp0001000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-547761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-548761639/1000000 : ℚ) by norm_num]
  exact coverp0001000100101
theorem coverp000100010010 : Covers (-547761639/2000000 : ℚ) vp000100010010 := join_branches bp0001000100100 bp0001000100101
private noncomputable def vp00010001001_0 : Blocks := edgeBlocks% "full/vectors/00010001001-V-0000.bin"
private noncomputable def vp00010001001_1 : Blocks := edgeBlocks% "full/vectors/00010001001-V-0001.bin"
noncomputable def vp00010001001 : Blocks := (Blocks.join vp00010001001_0 vp00010001001_1)
private theorem bp000100010010 : Branch 0 (-547761639/4000000 : ℚ) vp00010001001 := by
  apply branch_left_normalized (c:=vp000100010010) (k:=0) (m:=105) (by decide +kernel)
  rw [show 2*(-547761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-547761639/2000000 : ℚ) by norm_num]
  exact coverp000100010010
private noncomputable def ep000100010011_0 : Blocks := edgeBlocks% "full/vectors/000100010011-E-0000.bin"
private noncomputable def ep000100010011_1 : Blocks := edgeBlocks% "full/vectors/000100010011-E-0001.bin"
noncomputable def ep000100010011 : Blocks := (Blocks.join ep000100010011_0 ep000100010011_1)
private theorem idp000100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010001001.list =
    C ((2:ℤ)^203) * horner X vp000100010011.list + horner X ep000100010011.list := by
  exact edge_identity (B := (2:ℤ)^382) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100010011 : Branch 1 (-547761639/4000000 : ℚ) vp00010001001 := by
  apply branch_checked idp000100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-547761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-549761639/2000000 : ℚ) by norm_num]
  exact coverp000100010011
theorem coverp00010001001 : Covers (-547761639/4000000 : ℚ) vp00010001001 := join_branches bp000100010010 bp000100010011
private noncomputable def vp00010001000111_0 : Blocks := edgeBlocks% "full/vectors/00010001000111-V-0000.bin"
noncomputable def vp00010001000111 : Blocks := vp00010001000111_0
theorem coverp00010001000111 : Covers (-547261639/500000 : ℚ) vp00010001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001000110_0 : Blocks := edgeBlocks% "full/vectors/00010001000110-V-0000.bin"
noncomputable def vp00010001000110 : Blocks := vp00010001000110_0
theorem coverp00010001000110 : Covers (-546761639/500000 : ℚ) vp00010001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000100011_0 : Blocks := edgeBlocks% "full/vectors/0001000100011-V-0000.bin"
noncomputable def vp0001000100011 : Blocks := vp0001000100011_0
private theorem bp00010001000110 : Branch 0 (-546761639/1000000 : ℚ) vp0001000100011 := by
  apply branch_left_normalized (c:=vp00010001000110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-546761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-546761639/500000 : ℚ) by norm_num]
  exact coverp00010001000110
private noncomputable def ep00010001000111_0 : Blocks := edgeBlocks% "full/vectors/00010001000111-E-0000.bin"
noncomputable def ep00010001000111 : Blocks := ep00010001000111_0
private theorem idp00010001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000100011.list =
    C ((2:ℤ)^66) * horner X vp00010001000111.list + horner X ep00010001000111.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001000111 : Branch 1 (-546761639/1000000 : ℚ) vp0001000100011 := by
  apply branch_checked idp00010001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-546761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-547261639/500000 : ℚ) by norm_num]
  exact coverp00010001000111
theorem coverp0001000100011 : Covers (-546761639/1000000 : ℚ) vp0001000100011 := join_branches bp00010001000110 bp00010001000111
private noncomputable def vp00010001000101_0 : Blocks := edgeBlocks% "full/vectors/00010001000101-V-0000.bin"
noncomputable def vp00010001000101 : Blocks := vp00010001000101_0
theorem coverp00010001000101 : Covers (-546261639/500000 : ℚ) vp00010001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001000100_0 : Blocks := edgeBlocks% "full/vectors/00010001000100-V-0000.bin"
noncomputable def vp00010001000100 : Blocks := vp00010001000100_0
theorem coverp00010001000100 : Covers (-545761639/500000 : ℚ) vp00010001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000100010_0 : Blocks := edgeBlocks% "full/vectors/0001000100010-V-0000.bin"
noncomputable def vp0001000100010 : Blocks := vp0001000100010_0
private theorem bp00010001000100 : Branch 0 (-545761639/1000000 : ℚ) vp0001000100010 := by
  apply branch_left_normalized (c:=vp00010001000100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-545761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-545761639/500000 : ℚ) by norm_num]
  exact coverp00010001000100
private noncomputable def ep00010001000101_0 : Blocks := edgeBlocks% "full/vectors/00010001000101-E-0000.bin"
noncomputable def ep00010001000101 : Blocks := ep00010001000101_0
private theorem idp00010001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000100010.list =
    C ((2:ℤ)^66) * horner X vp00010001000101.list + horner X ep00010001000101.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001000101 : Branch 1 (-545761639/1000000 : ℚ) vp0001000100010 := by
  apply branch_checked idp00010001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-545761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-546261639/500000 : ℚ) by norm_num]
  exact coverp00010001000101
theorem coverp0001000100010 : Covers (-545761639/1000000 : ℚ) vp0001000100010 := join_branches bp00010001000100 bp00010001000101
private noncomputable def vp000100010001_0 : Blocks := edgeBlocks% "full/vectors/000100010001-V-0000.bin"
noncomputable def vp000100010001 : Blocks := vp000100010001_0
private theorem bp0001000100010 : Branch 0 (-545761639/2000000 : ℚ) vp000100010001 := by
  apply branch_left_normalized (c:=vp0001000100010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-545761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-545761639/1000000 : ℚ) by norm_num]
  exact coverp0001000100010
private noncomputable def ep0001000100011_0 : Blocks := edgeBlocks% "full/vectors/0001000100011-E-0000.bin"
noncomputable def ep0001000100011 : Blocks := ep0001000100011_0
private theorem idp0001000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100010001.list =
    C ((2:ℤ)^112) * horner X vp0001000100011.list + horner X ep0001000100011.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000100011 : Branch 1 (-545761639/2000000 : ℚ) vp000100010001 := by
  apply branch_checked idp0001000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-545761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-546761639/1000000 : ℚ) by norm_num]
  exact coverp0001000100011
theorem coverp000100010001 : Covers (-545761639/2000000 : ℚ) vp000100010001 := join_branches bp0001000100010 bp0001000100011
private noncomputable def vp00010001000011_0 : Blocks := edgeBlocks% "full/vectors/00010001000011-V-0000.bin"
noncomputable def vp00010001000011 : Blocks := vp00010001000011_0
theorem coverp00010001000011 : Covers (-545261639/500000 : ℚ) vp00010001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001000010_0 : Blocks := edgeBlocks% "full/vectors/00010001000010-V-0000.bin"
noncomputable def vp00010001000010 : Blocks := vp00010001000010_0
theorem coverp00010001000010 : Covers (-544761639/500000 : ℚ) vp00010001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000100001_0 : Blocks := edgeBlocks% "full/vectors/0001000100001-V-0000.bin"
noncomputable def vp0001000100001 : Blocks := vp0001000100001_0
private theorem bp00010001000010 : Branch 0 (-544761639/1000000 : ℚ) vp0001000100001 := by
  apply branch_left_normalized (c:=vp00010001000010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-544761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-544761639/500000 : ℚ) by norm_num]
  exact coverp00010001000010
private noncomputable def ep00010001000011_0 : Blocks := edgeBlocks% "full/vectors/00010001000011-E-0000.bin"
noncomputable def ep00010001000011 : Blocks := ep00010001000011_0
private theorem idp00010001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000100001.list =
    C ((2:ℤ)^66) * horner X vp00010001000011.list + horner X ep00010001000011.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001000011 : Branch 1 (-544761639/1000000 : ℚ) vp0001000100001 := by
  apply branch_checked idp00010001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-544761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-545261639/500000 : ℚ) by norm_num]
  exact coverp00010001000011
theorem coverp0001000100001 : Covers (-544761639/1000000 : ℚ) vp0001000100001 := join_branches bp00010001000010 bp00010001000011
private noncomputable def vp00010001000001_0 : Blocks := edgeBlocks% "full/vectors/00010001000001-V-0000.bin"
noncomputable def vp00010001000001 : Blocks := vp00010001000001_0
theorem coverp00010001000001 : Covers (-544261639/500000 : ℚ) vp00010001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010001000000_0 : Blocks := edgeBlocks% "full/vectors/00010001000000-V-0000.bin"
noncomputable def vp00010001000000 : Blocks := vp00010001000000_0
theorem coverp00010001000000 : Covers (-543761639/500000 : ℚ) vp00010001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000100000_0 : Blocks := edgeBlocks% "full/vectors/0001000100000-V-0000.bin"
noncomputable def vp0001000100000 : Blocks := vp0001000100000_0
private theorem bp00010001000000 : Branch 0 (-543761639/1000000 : ℚ) vp0001000100000 := by
  apply branch_left_normalized (c:=vp00010001000000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-543761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-543761639/500000 : ℚ) by norm_num]
  exact coverp00010001000000
private noncomputable def ep00010001000001_0 : Blocks := edgeBlocks% "full/vectors/00010001000001-E-0000.bin"
noncomputable def ep00010001000001 : Blocks := ep00010001000001_0
private theorem idp00010001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000100000.list =
    C ((2:ℤ)^66) * horner X vp00010001000001.list + horner X ep00010001000001.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001000001 : Branch 1 (-543761639/1000000 : ℚ) vp0001000100000 := by
  apply branch_checked idp00010001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-543761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-544261639/500000 : ℚ) by norm_num]
  exact coverp00010001000001
theorem coverp0001000100000 : Covers (-543761639/1000000 : ℚ) vp0001000100000 := join_branches bp00010001000000 bp00010001000001
private noncomputable def vp000100010000_0 : Blocks := edgeBlocks% "full/vectors/000100010000-V-0000.bin"
noncomputable def vp000100010000 : Blocks := vp000100010000_0
private theorem bp0001000100000 : Branch 0 (-543761639/2000000 : ℚ) vp000100010000 := by
  apply branch_left_normalized (c:=vp0001000100000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-543761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-543761639/1000000 : ℚ) by norm_num]
  exact coverp0001000100000
private noncomputable def ep0001000100001_0 : Blocks := edgeBlocks% "full/vectors/0001000100001-E-0000.bin"
noncomputable def ep0001000100001 : Blocks := ep0001000100001_0
private theorem idp0001000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100010000.list =
    C ((2:ℤ)^113) * horner X vp0001000100001.list + horner X ep0001000100001.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000100001 : Branch 1 (-543761639/2000000 : ℚ) vp000100010000 := by
  apply branch_checked idp0001000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-543761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-544761639/1000000 : ℚ) by norm_num]
  exact coverp0001000100001
theorem coverp000100010000 : Covers (-543761639/2000000 : ℚ) vp000100010000 := join_branches bp0001000100000 bp0001000100001
private noncomputable def vp00010001000_0 : Blocks := edgeBlocks% "full/vectors/00010001000-V-0000.bin"
private noncomputable def vp00010001000_1 : Blocks := edgeBlocks% "full/vectors/00010001000-V-0001.bin"
noncomputable def vp00010001000 : Blocks := (Blocks.join vp00010001000_0 vp00010001000_1)
private theorem bp000100010000 : Branch 0 (-543761639/4000000 : ℚ) vp00010001000 := by
  apply branch_left_normalized (c:=vp000100010000) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-543761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-543761639/2000000 : ℚ) by norm_num]
  exact coverp000100010000
private noncomputable def ep000100010001_0 : Blocks := edgeBlocks% "full/vectors/000100010001-E-0000.bin"
private noncomputable def ep000100010001_1 : Blocks := edgeBlocks% "full/vectors/000100010001-E-0001.bin"
noncomputable def ep000100010001 : Blocks := (Blocks.join ep000100010001_0 ep000100010001_1)
private theorem idp000100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010001000.list =
    C ((2:ℤ)^204) * horner X vp000100010001.list + horner X ep000100010001.list := by
  exact edge_identity (B := (2:ℤ)^384) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100010001 : Branch 1 (-543761639/4000000 : ℚ) vp00010001000 := by
  apply branch_checked idp000100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-543761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-545761639/2000000 : ℚ) by norm_num]
  exact coverp000100010001
theorem coverp00010001000 : Covers (-543761639/4000000 : ℚ) vp00010001000 := join_branches bp000100010000 bp000100010001
private noncomputable def vp0001000100_0 : Blocks := edgeBlocks% "full/vectors/0001000100-V-0000.bin"
private noncomputable def vp0001000100_1 : Blocks := edgeBlocks% "full/vectors/0001000100-V-0001.bin"
private noncomputable def vp0001000100_2 : Blocks := edgeBlocks% "full/vectors/0001000100-V-0002.bin"
noncomputable def vp0001000100 : Blocks := (Blocks.join vp0001000100_0 (Blocks.join vp0001000100_1 vp0001000100_2))
private theorem bp00010001000 : Branch 0 (-543761639/8000000 : ℚ) vp0001000100 := by
  apply branch_left_normalized (c:=vp00010001000) (k:=0) (m:=191) (by decide +kernel)
  rw [show 2*(-543761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-543761639/4000000 : ℚ) by norm_num]
  exact coverp00010001000
private noncomputable def ep00010001001_0 : Blocks := edgeBlocks% "full/vectors/00010001001-E-0000.bin"
private noncomputable def ep00010001001_1 : Blocks := edgeBlocks% "full/vectors/00010001001-E-0001.bin"
private noncomputable def ep00010001001_2 : Blocks := edgeBlocks% "full/vectors/00010001001-E-0002.bin"
noncomputable def ep00010001001 : Blocks := (Blocks.join ep00010001001_0 (Blocks.join ep00010001001_1 ep00010001001_2))
private theorem idp00010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000100.list =
    C ((2:ℤ)^383) * horner X vp00010001001.list + horner X ep00010001001.list := by
  exact edge_identity (B := (2:ℤ)^641) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001001 : Branch 1 (-543761639/8000000 : ℚ) vp0001000100 := by
  apply branch_checked idp00010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-543761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-547761639/4000000 : ℚ) by norm_num]
  exact coverp00010001001
theorem coverp0001000100 : Covers (-543761639/8000000 : ℚ) vp0001000100 := join_branches bp00010001000 bp00010001001
private noncomputable def vp000100010_0 : Blocks := edgeBlocks% "full/vectors/000100010-V-0000.bin"
private noncomputable def vp000100010_1 : Blocks := edgeBlocks% "full/vectors/000100010-V-0001.bin"
private noncomputable def vp000100010_2 : Blocks := edgeBlocks% "full/vectors/000100010-V-0002.bin"
private noncomputable def vp000100010_3 : Blocks := edgeBlocks% "full/vectors/000100010-V-0003.bin"
private noncomputable def vp000100010_4 : Blocks := edgeBlocks% "full/vectors/000100010-V-0004.bin"
private noncomputable def vp000100010_5 : Blocks := edgeBlocks% "full/vectors/000100010-V-0005.bin"
noncomputable def vp000100010 : Blocks := (Blocks.join (Blocks.join vp000100010_0 (Blocks.join vp000100010_1 vp000100010_2)) (Blocks.join vp000100010_3 (Blocks.join vp000100010_4 vp000100010_5)))
private theorem bp0001000100 : Branch 0 (-543761639/16000000 : ℚ) vp000100010 := by
  apply branch_left_normalized (c:=vp0001000100) (k:=0) (m:=359) (by decide +kernel)
  rw [show 2*(-543761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-543761639/8000000 : ℚ) by norm_num]
  exact coverp0001000100
private noncomputable def ep0001000101_0 : Blocks := edgeBlocks% "full/vectors/0001000101-E-0000.bin"
private noncomputable def ep0001000101_1 : Blocks := edgeBlocks% "full/vectors/0001000101-E-0001.bin"
private noncomputable def ep0001000101_2 : Blocks := edgeBlocks% "full/vectors/0001000101-E-0002.bin"
private noncomputable def ep0001000101_3 : Blocks := edgeBlocks% "full/vectors/0001000101-E-0003.bin"
private noncomputable def ep0001000101_4 : Blocks := edgeBlocks% "full/vectors/0001000101-E-0004.bin"
private noncomputable def ep0001000101_5 : Blocks := edgeBlocks% "full/vectors/0001000101-E-0005.bin"
noncomputable def ep0001000101 : Blocks := (Blocks.join (Blocks.join ep0001000101_0 (Blocks.join ep0001000101_1 ep0001000101_2)) (Blocks.join ep0001000101_3 (Blocks.join ep0001000101_4 ep0001000101_5)))
private theorem idp0001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100010.list =
    C ((2:ℤ)^737) * horner X vp0001000101.list + horner X ep0001000101.list := by
  exact edge_identity (B := (2:ℤ)^1150) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000101 : Branch 1 (-543761639/16000000 : ℚ) vp000100010 := by
  apply branch_checked idp0001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-543761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-551761639/8000000 : ℚ) by norm_num]
  exact coverp0001000101
theorem coverp000100010 : Covers (-543761639/16000000 : ℚ) vp000100010 := join_branches bp0001000100 bp0001000101
private noncomputable def vp00010001_0 : Blocks := edgeBlocks% "full/vectors/00010001-V-0000.bin"
private noncomputable def vp00010001_1 : Blocks := edgeBlocks% "full/vectors/00010001-V-0001.bin"
private noncomputable def vp00010001_2 : Blocks := edgeBlocks% "full/vectors/00010001-V-0002.bin"
private noncomputable def vp00010001_3 : Blocks := edgeBlocks% "full/vectors/00010001-V-0003.bin"
private noncomputable def vp00010001_4 : Blocks := edgeBlocks% "full/vectors/00010001-V-0004.bin"
private noncomputable def vp00010001_5 : Blocks := edgeBlocks% "full/vectors/00010001-V-0005.bin"
private noncomputable def vp00010001_6 : Blocks := edgeBlocks% "full/vectors/00010001-V-0006.bin"
private noncomputable def vp00010001_7 : Blocks := edgeBlocks% "full/vectors/00010001-V-0007.bin"
private noncomputable def vp00010001_8 : Blocks := edgeBlocks% "full/vectors/00010001-V-0008.bin"
private noncomputable def vp00010001_9 : Blocks := edgeBlocks% "full/vectors/00010001-V-0009.bin"
private noncomputable def vp00010001_10 : Blocks := edgeBlocks% "full/vectors/00010001-V-0010.bin"
noncomputable def vp00010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00010001_0 vp00010001_1) (Blocks.join vp00010001_2 (Blocks.join vp00010001_3 vp00010001_4))) (Blocks.join (Blocks.join vp00010001_5 (Blocks.join vp00010001_6 vp00010001_7)) (Blocks.join vp00010001_8 (Blocks.join vp00010001_9 vp00010001_10))))
private theorem bp000100010 : Branch 0 (-543761639/32000000 : ℚ) vp00010001 := by
  apply branch_left_normalized (c:=vp000100010) (k:=0) (m:=690) (by decide +kernel)
  rw [show 2*(-543761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-543761639/16000000 : ℚ) by norm_num]
  exact coverp000100010
private noncomputable def ep000100011_0 : Blocks := edgeBlocks% "full/vectors/000100011-E-0000.bin"
private noncomputable def ep000100011_1 : Blocks := edgeBlocks% "full/vectors/000100011-E-0001.bin"
private noncomputable def ep000100011_2 : Blocks := edgeBlocks% "full/vectors/000100011-E-0002.bin"
private noncomputable def ep000100011_3 : Blocks := edgeBlocks% "full/vectors/000100011-E-0003.bin"
private noncomputable def ep000100011_4 : Blocks := edgeBlocks% "full/vectors/000100011-E-0004.bin"
private noncomputable def ep000100011_5 : Blocks := edgeBlocks% "full/vectors/000100011-E-0005.bin"
private noncomputable def ep000100011_6 : Blocks := edgeBlocks% "full/vectors/000100011-E-0006.bin"
private noncomputable def ep000100011_7 : Blocks := edgeBlocks% "full/vectors/000100011-E-0007.bin"
private noncomputable def ep000100011_8 : Blocks := edgeBlocks% "full/vectors/000100011-E-0008.bin"
private noncomputable def ep000100011_9 : Blocks := edgeBlocks% "full/vectors/000100011-E-0009.bin"
private noncomputable def ep000100011_10 : Blocks := edgeBlocks% "full/vectors/000100011-E-0010.bin"
noncomputable def ep000100011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000100011_0 ep000100011_1) (Blocks.join ep000100011_2 (Blocks.join ep000100011_3 ep000100011_4))) (Blocks.join (Blocks.join ep000100011_5 (Blocks.join ep000100011_6 ep000100011_7)) (Blocks.join ep000100011_8 (Blocks.join ep000100011_9 ep000100011_10))))
private theorem idp000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010001.list =
    C ((2:ℤ)^1439) * horner X vp000100011.list + horner X ep000100011.list := by
  exact edge_identity (B := (2:ℤ)^2159) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100011 : Branch 1 (-543761639/32000000 : ℚ) vp00010001 := by
  apply branch_checked idp000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-543761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-559761639/16000000 : ℚ) by norm_num]
  exact coverp000100011
theorem coverp00010001 : Covers (-543761639/32000000 : ℚ) vp00010001 := join_branches bp000100010 bp000100011
end NextProof.EdgeFull

