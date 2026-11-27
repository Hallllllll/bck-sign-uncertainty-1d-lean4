import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00065

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00010000111111_0 : Blocks := edgeBlocks% "full/vectors/00010000111111-V-0000.bin"
noncomputable def vp00010000111111 : Blocks := vp00010000111111_0
theorem coverp00010000111111 : Covers (-543261639/500000 : ℚ) vp00010000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000111110_0 : Blocks := edgeBlocks% "full/vectors/00010000111110-V-0000.bin"
noncomputable def vp00010000111110 : Blocks := vp00010000111110_0
theorem coverp00010000111110 : Covers (-542761639/500000 : ℚ) vp00010000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000011111_0 : Blocks := edgeBlocks% "full/vectors/0001000011111-V-0000.bin"
noncomputable def vp0001000011111 : Blocks := vp0001000011111_0
private theorem bp00010000111110 : Branch 0 (-542761639/1000000 : ℚ) vp0001000011111 := by
  apply branch_left_normalized (c:=vp00010000111110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-542761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-542761639/500000 : ℚ) by norm_num]
  exact coverp00010000111110
private noncomputable def ep00010000111111_0 : Blocks := edgeBlocks% "full/vectors/00010000111111-E-0000.bin"
noncomputable def ep00010000111111 : Blocks := ep00010000111111_0
private theorem idp00010000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000011111.list =
    C ((2:ℤ)^66) * horner X vp00010000111111.list + horner X ep00010000111111.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000111111 : Branch 1 (-542761639/1000000 : ℚ) vp0001000011111 := by
  apply branch_checked idp00010000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-542761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-543261639/500000 : ℚ) by norm_num]
  exact coverp00010000111111
theorem coverp0001000011111 : Covers (-542761639/1000000 : ℚ) vp0001000011111 := join_branches bp00010000111110 bp00010000111111
private noncomputable def vp00010000111101_0 : Blocks := edgeBlocks% "full/vectors/00010000111101-V-0000.bin"
noncomputable def vp00010000111101 : Blocks := vp00010000111101_0
theorem coverp00010000111101 : Covers (-542261639/500000 : ℚ) vp00010000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000111100_0 : Blocks := edgeBlocks% "full/vectors/00010000111100-V-0000.bin"
noncomputable def vp00010000111100 : Blocks := vp00010000111100_0
theorem coverp00010000111100 : Covers (-541761639/500000 : ℚ) vp00010000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000011110_0 : Blocks := edgeBlocks% "full/vectors/0001000011110-V-0000.bin"
noncomputable def vp0001000011110 : Blocks := vp0001000011110_0
private theorem bp00010000111100 : Branch 0 (-541761639/1000000 : ℚ) vp0001000011110 := by
  apply branch_left_normalized (c:=vp00010000111100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-541761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-541761639/500000 : ℚ) by norm_num]
  exact coverp00010000111100
private noncomputable def ep00010000111101_0 : Blocks := edgeBlocks% "full/vectors/00010000111101-E-0000.bin"
noncomputable def ep00010000111101 : Blocks := ep00010000111101_0
private theorem idp00010000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000011110.list =
    C ((2:ℤ)^67) * horner X vp00010000111101.list + horner X ep00010000111101.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000111101 : Branch 1 (-541761639/1000000 : ℚ) vp0001000011110 := by
  apply branch_checked idp00010000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-541761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-542261639/500000 : ℚ) by norm_num]
  exact coverp00010000111101
theorem coverp0001000011110 : Covers (-541761639/1000000 : ℚ) vp0001000011110 := join_branches bp00010000111100 bp00010000111101
private noncomputable def vp000100001111_0 : Blocks := edgeBlocks% "full/vectors/000100001111-V-0000.bin"
noncomputable def vp000100001111 : Blocks := vp000100001111_0
private theorem bp0001000011110 : Branch 0 (-541761639/2000000 : ℚ) vp000100001111 := by
  apply branch_left_normalized (c:=vp0001000011110) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-541761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-541761639/1000000 : ℚ) by norm_num]
  exact coverp0001000011110
private noncomputable def ep0001000011111_0 : Blocks := edgeBlocks% "full/vectors/0001000011111-E-0000.bin"
noncomputable def ep0001000011111 : Blocks := ep0001000011111_0
private theorem idp0001000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100001111.list =
    C ((2:ℤ)^112) * horner X vp0001000011111.list + horner X ep0001000011111.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000011111 : Branch 1 (-541761639/2000000 : ℚ) vp000100001111 := by
  apply branch_checked idp0001000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-541761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-542761639/1000000 : ℚ) by norm_num]
  exact coverp0001000011111
theorem coverp000100001111 : Covers (-541761639/2000000 : ℚ) vp000100001111 := join_branches bp0001000011110 bp0001000011111
private noncomputable def vp00010000111011_0 : Blocks := edgeBlocks% "full/vectors/00010000111011-V-0000.bin"
noncomputable def vp00010000111011 : Blocks := vp00010000111011_0
theorem coverp00010000111011 : Covers (-541261639/500000 : ℚ) vp00010000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000111010_0 : Blocks := edgeBlocks% "full/vectors/00010000111010-V-0000.bin"
noncomputable def vp00010000111010 : Blocks := vp00010000111010_0
theorem coverp00010000111010 : Covers (-540761639/500000 : ℚ) vp00010000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000011101_0 : Blocks := edgeBlocks% "full/vectors/0001000011101-V-0000.bin"
noncomputable def vp0001000011101 : Blocks := vp0001000011101_0
private theorem bp00010000111010 : Branch 0 (-540761639/1000000 : ℚ) vp0001000011101 := by
  apply branch_left_normalized (c:=vp00010000111010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-540761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-540761639/500000 : ℚ) by norm_num]
  exact coverp00010000111010
private noncomputable def ep00010000111011_0 : Blocks := edgeBlocks% "full/vectors/00010000111011-E-0000.bin"
noncomputable def ep00010000111011 : Blocks := ep00010000111011_0
private theorem idp00010000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000011101.list =
    C ((2:ℤ)^66) * horner X vp00010000111011.list + horner X ep00010000111011.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000111011 : Branch 1 (-540761639/1000000 : ℚ) vp0001000011101 := by
  apply branch_checked idp00010000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-540761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-541261639/500000 : ℚ) by norm_num]
  exact coverp00010000111011
theorem coverp0001000011101 : Covers (-540761639/1000000 : ℚ) vp0001000011101 := join_branches bp00010000111010 bp00010000111011
private noncomputable def vp00010000111001_0 : Blocks := edgeBlocks% "full/vectors/00010000111001-V-0000.bin"
noncomputable def vp00010000111001 : Blocks := vp00010000111001_0
theorem coverp00010000111001 : Covers (-540261639/500000 : ℚ) vp00010000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000111000_0 : Blocks := edgeBlocks% "full/vectors/00010000111000-V-0000.bin"
noncomputable def vp00010000111000 : Blocks := vp00010000111000_0
theorem coverp00010000111000 : Covers (-539761639/500000 : ℚ) vp00010000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000011100_0 : Blocks := edgeBlocks% "full/vectors/0001000011100-V-0000.bin"
noncomputable def vp0001000011100 : Blocks := vp0001000011100_0
private theorem bp00010000111000 : Branch 0 (-539761639/1000000 : ℚ) vp0001000011100 := by
  apply branch_left_normalized (c:=vp00010000111000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-539761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-539761639/500000 : ℚ) by norm_num]
  exact coverp00010000111000
private noncomputable def ep00010000111001_0 : Blocks := edgeBlocks% "full/vectors/00010000111001-E-0000.bin"
noncomputable def ep00010000111001 : Blocks := ep00010000111001_0
private theorem idp00010000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000011100.list =
    C ((2:ℤ)^66) * horner X vp00010000111001.list + horner X ep00010000111001.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000111001 : Branch 1 (-539761639/1000000 : ℚ) vp0001000011100 := by
  apply branch_checked idp00010000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-539761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-540261639/500000 : ℚ) by norm_num]
  exact coverp00010000111001
theorem coverp0001000011100 : Covers (-539761639/1000000 : ℚ) vp0001000011100 := join_branches bp00010000111000 bp00010000111001
private noncomputable def vp000100001110_0 : Blocks := edgeBlocks% "full/vectors/000100001110-V-0000.bin"
noncomputable def vp000100001110 : Blocks := vp000100001110_0
private theorem bp0001000011100 : Branch 0 (-539761639/2000000 : ℚ) vp000100001110 := by
  apply branch_left_normalized (c:=vp0001000011100) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-539761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-539761639/1000000 : ℚ) by norm_num]
  exact coverp0001000011100
private noncomputable def ep0001000011101_0 : Blocks := edgeBlocks% "full/vectors/0001000011101-E-0000.bin"
noncomputable def ep0001000011101 : Blocks := ep0001000011101_0
private theorem idp0001000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100001110.list =
    C ((2:ℤ)^112) * horner X vp0001000011101.list + horner X ep0001000011101.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000011101 : Branch 1 (-539761639/2000000 : ℚ) vp000100001110 := by
  apply branch_checked idp0001000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-539761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-540761639/1000000 : ℚ) by norm_num]
  exact coverp0001000011101
theorem coverp000100001110 : Covers (-539761639/2000000 : ℚ) vp000100001110 := join_branches bp0001000011100 bp0001000011101
private noncomputable def vp00010000111_0 : Blocks := edgeBlocks% "full/vectors/00010000111-V-0000.bin"
private noncomputable def vp00010000111_1 : Blocks := edgeBlocks% "full/vectors/00010000111-V-0001.bin"
noncomputable def vp00010000111 : Blocks := (Blocks.join vp00010000111_0 vp00010000111_1)
private theorem bp000100001110 : Branch 0 (-539761639/4000000 : ℚ) vp00010000111 := by
  apply branch_left_normalized (c:=vp000100001110) (k:=0) (m:=105) (by decide +kernel)
  rw [show 2*(-539761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-539761639/2000000 : ℚ) by norm_num]
  exact coverp000100001110
private noncomputable def ep000100001111_0 : Blocks := edgeBlocks% "full/vectors/000100001111-E-0000.bin"
private noncomputable def ep000100001111_1 : Blocks := edgeBlocks% "full/vectors/000100001111-E-0001.bin"
noncomputable def ep000100001111 : Blocks := (Blocks.join ep000100001111_0 ep000100001111_1)
private theorem idp000100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010000111.list =
    C ((2:ℤ)^204) * horner X vp000100001111.list + horner X ep000100001111.list := by
  exact edge_identity (B := (2:ℤ)^384) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100001111 : Branch 1 (-539761639/4000000 : ℚ) vp00010000111 := by
  apply branch_checked idp000100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-539761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-541761639/2000000 : ℚ) by norm_num]
  exact coverp000100001111
theorem coverp00010000111 : Covers (-539761639/4000000 : ℚ) vp00010000111 := join_branches bp000100001110 bp000100001111
private noncomputable def vp00010000110111_0 : Blocks := edgeBlocks% "full/vectors/00010000110111-V-0000.bin"
noncomputable def vp00010000110111 : Blocks := vp00010000110111_0
theorem coverp00010000110111 : Covers (-539261639/500000 : ℚ) vp00010000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000110110_0 : Blocks := edgeBlocks% "full/vectors/00010000110110-V-0000.bin"
noncomputable def vp00010000110110 : Blocks := vp00010000110110_0
theorem coverp00010000110110 : Covers (-538761639/500000 : ℚ) vp00010000110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000011011_0 : Blocks := edgeBlocks% "full/vectors/0001000011011-V-0000.bin"
noncomputable def vp0001000011011 : Blocks := vp0001000011011_0
private theorem bp00010000110110 : Branch 0 (-538761639/1000000 : ℚ) vp0001000011011 := by
  apply branch_left_normalized (c:=vp00010000110110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-538761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-538761639/500000 : ℚ) by norm_num]
  exact coverp00010000110110
private noncomputable def ep00010000110111_0 : Blocks := edgeBlocks% "full/vectors/00010000110111-E-0000.bin"
noncomputable def ep00010000110111 : Blocks := ep00010000110111_0
private theorem idp00010000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000011011.list =
    C ((2:ℤ)^65) * horner X vp00010000110111.list + horner X ep00010000110111.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000110111 : Branch 1 (-538761639/1000000 : ℚ) vp0001000011011 := by
  apply branch_checked idp00010000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-538761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-539261639/500000 : ℚ) by norm_num]
  exact coverp00010000110111
theorem coverp0001000011011 : Covers (-538761639/1000000 : ℚ) vp0001000011011 := join_branches bp00010000110110 bp00010000110111
private noncomputable def vp00010000110101_0 : Blocks := edgeBlocks% "full/vectors/00010000110101-V-0000.bin"
noncomputable def vp00010000110101 : Blocks := vp00010000110101_0
theorem coverp00010000110101 : Covers (-538261639/500000 : ℚ) vp00010000110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000110100_0 : Blocks := edgeBlocks% "full/vectors/00010000110100-V-0000.bin"
noncomputable def vp00010000110100 : Blocks := vp00010000110100_0
theorem coverp00010000110100 : Covers (-537761639/500000 : ℚ) vp00010000110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000011010_0 : Blocks := edgeBlocks% "full/vectors/0001000011010-V-0000.bin"
noncomputable def vp0001000011010 : Blocks := vp0001000011010_0
private theorem bp00010000110100 : Branch 0 (-537761639/1000000 : ℚ) vp0001000011010 := by
  apply branch_left_normalized (c:=vp00010000110100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-537761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-537761639/500000 : ℚ) by norm_num]
  exact coverp00010000110100
private noncomputable def ep00010000110101_0 : Blocks := edgeBlocks% "full/vectors/00010000110101-E-0000.bin"
noncomputable def ep00010000110101 : Blocks := ep00010000110101_0
private theorem idp00010000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000011010.list =
    C ((2:ℤ)^67) * horner X vp00010000110101.list + horner X ep00010000110101.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000110101 : Branch 1 (-537761639/1000000 : ℚ) vp0001000011010 := by
  apply branch_checked idp00010000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-537761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-538261639/500000 : ℚ) by norm_num]
  exact coverp00010000110101
theorem coverp0001000011010 : Covers (-537761639/1000000 : ℚ) vp0001000011010 := join_branches bp00010000110100 bp00010000110101
private noncomputable def vp000100001101_0 : Blocks := edgeBlocks% "full/vectors/000100001101-V-0000.bin"
noncomputable def vp000100001101 : Blocks := vp000100001101_0
private theorem bp0001000011010 : Branch 0 (-537761639/2000000 : ℚ) vp000100001101 := by
  apply branch_left_normalized (c:=vp0001000011010) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-537761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-537761639/1000000 : ℚ) by norm_num]
  exact coverp0001000011010
private noncomputable def ep0001000011011_0 : Blocks := edgeBlocks% "full/vectors/0001000011011-E-0000.bin"
noncomputable def ep0001000011011 : Blocks := ep0001000011011_0
private theorem idp0001000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100001101.list =
    C ((2:ℤ)^113) * horner X vp0001000011011.list + horner X ep0001000011011.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000011011 : Branch 1 (-537761639/2000000 : ℚ) vp000100001101 := by
  apply branch_checked idp0001000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-537761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-538761639/1000000 : ℚ) by norm_num]
  exact coverp0001000011011
theorem coverp000100001101 : Covers (-537761639/2000000 : ℚ) vp000100001101 := join_branches bp0001000011010 bp0001000011011
private noncomputable def vp00010000110011_0 : Blocks := edgeBlocks% "full/vectors/00010000110011-V-0000.bin"
noncomputable def vp00010000110011 : Blocks := vp00010000110011_0
theorem coverp00010000110011 : Covers (-537261639/500000 : ℚ) vp00010000110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000110010_0 : Blocks := edgeBlocks% "full/vectors/00010000110010-V-0000.bin"
noncomputable def vp00010000110010 : Blocks := vp00010000110010_0
theorem coverp00010000110010 : Covers (-536761639/500000 : ℚ) vp00010000110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000011001_0 : Blocks := edgeBlocks% "full/vectors/0001000011001-V-0000.bin"
noncomputable def vp0001000011001 : Blocks := vp0001000011001_0
private theorem bp00010000110010 : Branch 0 (-536761639/1000000 : ℚ) vp0001000011001 := by
  apply branch_left_normalized (c:=vp00010000110010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-536761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-536761639/500000 : ℚ) by norm_num]
  exact coverp00010000110010
private noncomputable def ep00010000110011_0 : Blocks := edgeBlocks% "full/vectors/00010000110011-E-0000.bin"
noncomputable def ep00010000110011 : Blocks := ep00010000110011_0
private theorem idp00010000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000011001.list =
    C ((2:ℤ)^67) * horner X vp00010000110011.list + horner X ep00010000110011.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000110011 : Branch 1 (-536761639/1000000 : ℚ) vp0001000011001 := by
  apply branch_checked idp00010000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-536761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-537261639/500000 : ℚ) by norm_num]
  exact coverp00010000110011
theorem coverp0001000011001 : Covers (-536761639/1000000 : ℚ) vp0001000011001 := join_branches bp00010000110010 bp00010000110011
private noncomputable def vp00010000110001_0 : Blocks := edgeBlocks% "full/vectors/00010000110001-V-0000.bin"
noncomputable def vp00010000110001 : Blocks := vp00010000110001_0
theorem coverp00010000110001 : Covers (-536261639/500000 : ℚ) vp00010000110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000110000_0 : Blocks := edgeBlocks% "full/vectors/00010000110000-V-0000.bin"
noncomputable def vp00010000110000 : Blocks := vp00010000110000_0
theorem coverp00010000110000 : Covers (-535761639/500000 : ℚ) vp00010000110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000011000_0 : Blocks := edgeBlocks% "full/vectors/0001000011000-V-0000.bin"
noncomputable def vp0001000011000 : Blocks := vp0001000011000_0
private theorem bp00010000110000 : Branch 0 (-535761639/1000000 : ℚ) vp0001000011000 := by
  apply branch_left_normalized (c:=vp00010000110000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-535761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-535761639/500000 : ℚ) by norm_num]
  exact coverp00010000110000
private noncomputable def ep00010000110001_0 : Blocks := edgeBlocks% "full/vectors/00010000110001-E-0000.bin"
noncomputable def ep00010000110001 : Blocks := ep00010000110001_0
private theorem idp00010000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000011000.list =
    C ((2:ℤ)^67) * horner X vp00010000110001.list + horner X ep00010000110001.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000110001 : Branch 1 (-535761639/1000000 : ℚ) vp0001000011000 := by
  apply branch_checked idp00010000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-535761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-536261639/500000 : ℚ) by norm_num]
  exact coverp00010000110001
theorem coverp0001000011000 : Covers (-535761639/1000000 : ℚ) vp0001000011000 := join_branches bp00010000110000 bp00010000110001
private noncomputable def vp000100001100_0 : Blocks := edgeBlocks% "full/vectors/000100001100-V-0000.bin"
noncomputable def vp000100001100 : Blocks := vp000100001100_0
private theorem bp0001000011000 : Branch 0 (-535761639/2000000 : ℚ) vp000100001100 := by
  apply branch_left_normalized (c:=vp0001000011000) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-535761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-535761639/1000000 : ℚ) by norm_num]
  exact coverp0001000011000
private noncomputable def ep0001000011001_0 : Blocks := edgeBlocks% "full/vectors/0001000011001-E-0000.bin"
noncomputable def ep0001000011001 : Blocks := ep0001000011001_0
private theorem idp0001000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100001100.list =
    C ((2:ℤ)^114) * horner X vp0001000011001.list + horner X ep0001000011001.list := by
  exact edge_identity (B := (2:ℤ)^255) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000011001 : Branch 1 (-535761639/2000000 : ℚ) vp000100001100 := by
  apply branch_checked idp0001000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-535761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-536761639/1000000 : ℚ) by norm_num]
  exact coverp0001000011001
theorem coverp000100001100 : Covers (-535761639/2000000 : ℚ) vp000100001100 := join_branches bp0001000011000 bp0001000011001
private noncomputable def vp00010000110_0 : Blocks := edgeBlocks% "full/vectors/00010000110-V-0000.bin"
private noncomputable def vp00010000110_1 : Blocks := edgeBlocks% "full/vectors/00010000110-V-0001.bin"
noncomputable def vp00010000110 : Blocks := (Blocks.join vp00010000110_0 vp00010000110_1)
private theorem bp000100001100 : Branch 0 (-535761639/4000000 : ℚ) vp00010000110 := by
  apply branch_left_normalized (c:=vp000100001100) (k:=0) (m:=107) (by decide +kernel)
  rw [show 2*(-535761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-535761639/2000000 : ℚ) by norm_num]
  exact coverp000100001100
private noncomputable def ep000100001101_0 : Blocks := edgeBlocks% "full/vectors/000100001101-E-0000.bin"
private noncomputable def ep000100001101_1 : Blocks := edgeBlocks% "full/vectors/000100001101-E-0001.bin"
noncomputable def ep000100001101 : Blocks := (Blocks.join ep000100001101_0 ep000100001101_1)
private theorem idp000100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010000110.list =
    C ((2:ℤ)^205) * horner X vp000100001101.list + horner X ep000100001101.list := by
  exact edge_identity (B := (2:ℤ)^385) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100001101 : Branch 1 (-535761639/4000000 : ℚ) vp00010000110 := by
  apply branch_checked idp000100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-535761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-537761639/2000000 : ℚ) by norm_num]
  exact coverp000100001101
theorem coverp00010000110 : Covers (-535761639/4000000 : ℚ) vp00010000110 := join_branches bp000100001100 bp000100001101
private noncomputable def vp0001000011_0 : Blocks := edgeBlocks% "full/vectors/0001000011-V-0000.bin"
private noncomputable def vp0001000011_1 : Blocks := edgeBlocks% "full/vectors/0001000011-V-0001.bin"
private noncomputable def vp0001000011_2 : Blocks := edgeBlocks% "full/vectors/0001000011-V-0002.bin"
noncomputable def vp0001000011 : Blocks := (Blocks.join vp0001000011_0 (Blocks.join vp0001000011_1 vp0001000011_2))
private theorem bp00010000110 : Branch 0 (-535761639/8000000 : ℚ) vp0001000011 := by
  apply branch_left_normalized (c:=vp00010000110) (k:=0) (m:=192) (by decide +kernel)
  rw [show 2*(-535761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-535761639/4000000 : ℚ) by norm_num]
  exact coverp00010000110
private noncomputable def ep00010000111_0 : Blocks := edgeBlocks% "full/vectors/00010000111-E-0000.bin"
private noncomputable def ep00010000111_1 : Blocks := edgeBlocks% "full/vectors/00010000111-E-0001.bin"
private noncomputable def ep00010000111_2 : Blocks := edgeBlocks% "full/vectors/00010000111-E-0002.bin"
noncomputable def ep00010000111 : Blocks := (Blocks.join ep00010000111_0 (Blocks.join ep00010000111_1 ep00010000111_2))
private theorem idp00010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000011.list =
    C ((2:ℤ)^385) * horner X vp00010000111.list + horner X ep00010000111.list := by
  exact edge_identity (B := (2:ℤ)^644) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000111 : Branch 1 (-535761639/8000000 : ℚ) vp0001000011 := by
  apply branch_checked idp00010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-535761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-539761639/4000000 : ℚ) by norm_num]
  exact coverp00010000111
theorem coverp0001000011 : Covers (-535761639/8000000 : ℚ) vp0001000011 := join_branches bp00010000110 bp00010000111
private noncomputable def vp00010000101111_0 : Blocks := edgeBlocks% "full/vectors/00010000101111-V-0000.bin"
noncomputable def vp00010000101111 : Blocks := vp00010000101111_0
theorem coverp00010000101111 : Covers (-535261639/500000 : ℚ) vp00010000101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000101110_0 : Blocks := edgeBlocks% "full/vectors/00010000101110-V-0000.bin"
noncomputable def vp00010000101110 : Blocks := vp00010000101110_0
theorem coverp00010000101110 : Covers (-534761639/500000 : ℚ) vp00010000101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000010111_0 : Blocks := edgeBlocks% "full/vectors/0001000010111-V-0000.bin"
noncomputable def vp0001000010111 : Blocks := vp0001000010111_0
private theorem bp00010000101110 : Branch 0 (-534761639/1000000 : ℚ) vp0001000010111 := by
  apply branch_left_normalized (c:=vp00010000101110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-534761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-534761639/500000 : ℚ) by norm_num]
  exact coverp00010000101110
private noncomputable def ep00010000101111_0 : Blocks := edgeBlocks% "full/vectors/00010000101111-E-0000.bin"
noncomputable def ep00010000101111 : Blocks := ep00010000101111_0
private theorem idp00010000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000010111.list =
    C ((2:ℤ)^66) * horner X vp00010000101111.list + horner X ep00010000101111.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000101111 : Branch 1 (-534761639/1000000 : ℚ) vp0001000010111 := by
  apply branch_checked idp00010000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-534761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-535261639/500000 : ℚ) by norm_num]
  exact coverp00010000101111
theorem coverp0001000010111 : Covers (-534761639/1000000 : ℚ) vp0001000010111 := join_branches bp00010000101110 bp00010000101111
private noncomputable def vp00010000101101_0 : Blocks := edgeBlocks% "full/vectors/00010000101101-V-0000.bin"
noncomputable def vp00010000101101 : Blocks := vp00010000101101_0
theorem coverp00010000101101 : Covers (-534261639/500000 : ℚ) vp00010000101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000101100_0 : Blocks := edgeBlocks% "full/vectors/00010000101100-V-0000.bin"
noncomputable def vp00010000101100 : Blocks := vp00010000101100_0
theorem coverp00010000101100 : Covers (-533761639/500000 : ℚ) vp00010000101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000010110_0 : Blocks := edgeBlocks% "full/vectors/0001000010110-V-0000.bin"
noncomputable def vp0001000010110 : Blocks := vp0001000010110_0
private theorem bp00010000101100 : Branch 0 (-533761639/1000000 : ℚ) vp0001000010110 := by
  apply branch_left_normalized (c:=vp00010000101100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-533761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-533761639/500000 : ℚ) by norm_num]
  exact coverp00010000101100
private noncomputable def ep00010000101101_0 : Blocks := edgeBlocks% "full/vectors/00010000101101-E-0000.bin"
noncomputable def ep00010000101101 : Blocks := ep00010000101101_0
private theorem idp00010000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000010110.list =
    C ((2:ℤ)^66) * horner X vp00010000101101.list + horner X ep00010000101101.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000101101 : Branch 1 (-533761639/1000000 : ℚ) vp0001000010110 := by
  apply branch_checked idp00010000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-533761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-534261639/500000 : ℚ) by norm_num]
  exact coverp00010000101101
theorem coverp0001000010110 : Covers (-533761639/1000000 : ℚ) vp0001000010110 := join_branches bp00010000101100 bp00010000101101
private noncomputable def vp000100001011_0 : Blocks := edgeBlocks% "full/vectors/000100001011-V-0000.bin"
noncomputable def vp000100001011 : Blocks := vp000100001011_0
private theorem bp0001000010110 : Branch 0 (-533761639/2000000 : ℚ) vp000100001011 := by
  apply branch_left_normalized (c:=vp0001000010110) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-533761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-533761639/1000000 : ℚ) by norm_num]
  exact coverp0001000010110
private noncomputable def ep0001000010111_0 : Blocks := edgeBlocks% "full/vectors/0001000010111-E-0000.bin"
noncomputable def ep0001000010111 : Blocks := ep0001000010111_0
private theorem idp0001000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100001011.list =
    C ((2:ℤ)^113) * horner X vp0001000010111.list + horner X ep0001000010111.list := by
  exact edge_identity (B := (2:ℤ)^255) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000010111 : Branch 1 (-533761639/2000000 : ℚ) vp000100001011 := by
  apply branch_checked idp0001000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-533761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-534761639/1000000 : ℚ) by norm_num]
  exact coverp0001000010111
theorem coverp000100001011 : Covers (-533761639/2000000 : ℚ) vp000100001011 := join_branches bp0001000010110 bp0001000010111
private noncomputable def vp00010000101011_0 : Blocks := edgeBlocks% "full/vectors/00010000101011-V-0000.bin"
noncomputable def vp00010000101011 : Blocks := vp00010000101011_0
theorem coverp00010000101011 : Covers (-533261639/500000 : ℚ) vp00010000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000101010_0 : Blocks := edgeBlocks% "full/vectors/00010000101010-V-0000.bin"
noncomputable def vp00010000101010 : Blocks := vp00010000101010_0
theorem coverp00010000101010 : Covers (-532761639/500000 : ℚ) vp00010000101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000010101_0 : Blocks := edgeBlocks% "full/vectors/0001000010101-V-0000.bin"
noncomputable def vp0001000010101 : Blocks := vp0001000010101_0
private theorem bp00010000101010 : Branch 0 (-532761639/1000000 : ℚ) vp0001000010101 := by
  apply branch_left_normalized (c:=vp00010000101010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-532761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-532761639/500000 : ℚ) by norm_num]
  exact coverp00010000101010
private noncomputable def ep00010000101011_0 : Blocks := edgeBlocks% "full/vectors/00010000101011-E-0000.bin"
noncomputable def ep00010000101011 : Blocks := ep00010000101011_0
private theorem idp00010000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000010101.list =
    C ((2:ℤ)^67) * horner X vp00010000101011.list + horner X ep00010000101011.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000101011 : Branch 1 (-532761639/1000000 : ℚ) vp0001000010101 := by
  apply branch_checked idp00010000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-532761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-533261639/500000 : ℚ) by norm_num]
  exact coverp00010000101011
theorem coverp0001000010101 : Covers (-532761639/1000000 : ℚ) vp0001000010101 := join_branches bp00010000101010 bp00010000101011
private noncomputable def vp00010000101001_0 : Blocks := edgeBlocks% "full/vectors/00010000101001-V-0000.bin"
noncomputable def vp00010000101001 : Blocks := vp00010000101001_0
theorem coverp00010000101001 : Covers (-532261639/500000 : ℚ) vp00010000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000101000_0 : Blocks := edgeBlocks% "full/vectors/00010000101000-V-0000.bin"
noncomputable def vp00010000101000 : Blocks := vp00010000101000_0
theorem coverp00010000101000 : Covers (-531761639/500000 : ℚ) vp00010000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000010100_0 : Blocks := edgeBlocks% "full/vectors/0001000010100-V-0000.bin"
noncomputable def vp0001000010100 : Blocks := vp0001000010100_0
private theorem bp00010000101000 : Branch 0 (-531761639/1000000 : ℚ) vp0001000010100 := by
  apply branch_left_normalized (c:=vp00010000101000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-531761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-531761639/500000 : ℚ) by norm_num]
  exact coverp00010000101000
private noncomputable def ep00010000101001_0 : Blocks := edgeBlocks% "full/vectors/00010000101001-E-0000.bin"
noncomputable def ep00010000101001 : Blocks := ep00010000101001_0
private theorem idp00010000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000010100.list =
    C ((2:ℤ)^67) * horner X vp00010000101001.list + horner X ep00010000101001.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000101001 : Branch 1 (-531761639/1000000 : ℚ) vp0001000010100 := by
  apply branch_checked idp00010000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-531761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-532261639/500000 : ℚ) by norm_num]
  exact coverp00010000101001
theorem coverp0001000010100 : Covers (-531761639/1000000 : ℚ) vp0001000010100 := join_branches bp00010000101000 bp00010000101001
private noncomputable def vp000100001010_0 : Blocks := edgeBlocks% "full/vectors/000100001010-V-0000.bin"
noncomputable def vp000100001010 : Blocks := vp000100001010_0
private theorem bp0001000010100 : Branch 0 (-531761639/2000000 : ℚ) vp000100001010 := by
  apply branch_left_normalized (c:=vp0001000010100) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-531761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-531761639/1000000 : ℚ) by norm_num]
  exact coverp0001000010100
private noncomputable def ep0001000010101_0 : Blocks := edgeBlocks% "full/vectors/0001000010101-E-0000.bin"
noncomputable def ep0001000010101 : Blocks := ep0001000010101_0
private theorem idp0001000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100001010.list =
    C ((2:ℤ)^113) * horner X vp0001000010101.list + horner X ep0001000010101.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000010101 : Branch 1 (-531761639/2000000 : ℚ) vp000100001010 := by
  apply branch_checked idp0001000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-531761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-532761639/1000000 : ℚ) by norm_num]
  exact coverp0001000010101
theorem coverp000100001010 : Covers (-531761639/2000000 : ℚ) vp000100001010 := join_branches bp0001000010100 bp0001000010101
private noncomputable def vp00010000101_0 : Blocks := edgeBlocks% "full/vectors/00010000101-V-0000.bin"
private noncomputable def vp00010000101_1 : Blocks := edgeBlocks% "full/vectors/00010000101-V-0001.bin"
noncomputable def vp00010000101 : Blocks := (Blocks.join vp00010000101_0 vp00010000101_1)
private theorem bp000100001010 : Branch 0 (-531761639/4000000 : ℚ) vp00010000101 := by
  apply branch_left_normalized (c:=vp000100001010) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-531761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-531761639/2000000 : ℚ) by norm_num]
  exact coverp000100001010
private noncomputable def ep000100001011_0 : Blocks := edgeBlocks% "full/vectors/000100001011-E-0000.bin"
private noncomputable def ep000100001011_1 : Blocks := edgeBlocks% "full/vectors/000100001011-E-0001.bin"
noncomputable def ep000100001011 : Blocks := (Blocks.join ep000100001011_0 ep000100001011_1)
private theorem idp000100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010000101.list =
    C ((2:ℤ)^205) * horner X vp000100001011.list + horner X ep000100001011.list := by
  exact edge_identity (B := (2:ℤ)^385) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100001011 : Branch 1 (-531761639/4000000 : ℚ) vp00010000101 := by
  apply branch_checked idp000100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-531761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-533761639/2000000 : ℚ) by norm_num]
  exact coverp000100001011
theorem coverp00010000101 : Covers (-531761639/4000000 : ℚ) vp00010000101 := join_branches bp000100001010 bp000100001011
private noncomputable def vp00010000100111_0 : Blocks := edgeBlocks% "full/vectors/00010000100111-V-0000.bin"
noncomputable def vp00010000100111 : Blocks := vp00010000100111_0
theorem coverp00010000100111 : Covers (-531261639/500000 : ℚ) vp00010000100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000100110_0 : Blocks := edgeBlocks% "full/vectors/00010000100110-V-0000.bin"
noncomputable def vp00010000100110 : Blocks := vp00010000100110_0
theorem coverp00010000100110 : Covers (-530761639/500000 : ℚ) vp00010000100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000010011_0 : Blocks := edgeBlocks% "full/vectors/0001000010011-V-0000.bin"
noncomputable def vp0001000010011 : Blocks := vp0001000010011_0
private theorem bp00010000100110 : Branch 0 (-530761639/1000000 : ℚ) vp0001000010011 := by
  apply branch_left_normalized (c:=vp00010000100110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-530761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-530761639/500000 : ℚ) by norm_num]
  exact coverp00010000100110
private noncomputable def ep00010000100111_0 : Blocks := edgeBlocks% "full/vectors/00010000100111-E-0000.bin"
noncomputable def ep00010000100111 : Blocks := ep00010000100111_0
private theorem idp00010000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000010011.list =
    C ((2:ℤ)^67) * horner X vp00010000100111.list + horner X ep00010000100111.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000100111 : Branch 1 (-530761639/1000000 : ℚ) vp0001000010011 := by
  apply branch_checked idp00010000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-530761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-531261639/500000 : ℚ) by norm_num]
  exact coverp00010000100111
theorem coverp0001000010011 : Covers (-530761639/1000000 : ℚ) vp0001000010011 := join_branches bp00010000100110 bp00010000100111
private noncomputable def vp00010000100101_0 : Blocks := edgeBlocks% "full/vectors/00010000100101-V-0000.bin"
noncomputable def vp00010000100101 : Blocks := vp00010000100101_0
theorem coverp00010000100101 : Covers (-530261639/500000 : ℚ) vp00010000100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000100100_0 : Blocks := edgeBlocks% "full/vectors/00010000100100-V-0000.bin"
noncomputable def vp00010000100100 : Blocks := vp00010000100100_0
theorem coverp00010000100100 : Covers (-529761639/500000 : ℚ) vp00010000100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000010010_0 : Blocks := edgeBlocks% "full/vectors/0001000010010-V-0000.bin"
noncomputable def vp0001000010010 : Blocks := vp0001000010010_0
private theorem bp00010000100100 : Branch 0 (-529761639/1000000 : ℚ) vp0001000010010 := by
  apply branch_left_normalized (c:=vp00010000100100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-529761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-529761639/500000 : ℚ) by norm_num]
  exact coverp00010000100100
private noncomputable def ep00010000100101_0 : Blocks := edgeBlocks% "full/vectors/00010000100101-E-0000.bin"
noncomputable def ep00010000100101 : Blocks := ep00010000100101_0
private theorem idp00010000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000010010.list =
    C ((2:ℤ)^67) * horner X vp00010000100101.list + horner X ep00010000100101.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000100101 : Branch 1 (-529761639/1000000 : ℚ) vp0001000010010 := by
  apply branch_checked idp00010000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-529761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-530261639/500000 : ℚ) by norm_num]
  exact coverp00010000100101
theorem coverp0001000010010 : Covers (-529761639/1000000 : ℚ) vp0001000010010 := join_branches bp00010000100100 bp00010000100101
private noncomputable def vp000100001001_0 : Blocks := edgeBlocks% "full/vectors/000100001001-V-0000.bin"
noncomputable def vp000100001001 : Blocks := vp000100001001_0
private theorem bp0001000010010 : Branch 0 (-529761639/2000000 : ℚ) vp000100001001 := by
  apply branch_left_normalized (c:=vp0001000010010) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-529761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-529761639/1000000 : ℚ) by norm_num]
  exact coverp0001000010010
private noncomputable def ep0001000010011_0 : Blocks := edgeBlocks% "full/vectors/0001000010011-E-0000.bin"
noncomputable def ep0001000010011 : Blocks := ep0001000010011_0
private theorem idp0001000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100001001.list =
    C ((2:ℤ)^114) * horner X vp0001000010011.list + horner X ep0001000010011.list := by
  exact edge_identity (B := (2:ℤ)^256) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000010011 : Branch 1 (-529761639/2000000 : ℚ) vp000100001001 := by
  apply branch_checked idp0001000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-529761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-530761639/1000000 : ℚ) by norm_num]
  exact coverp0001000010011
theorem coverp000100001001 : Covers (-529761639/2000000 : ℚ) vp000100001001 := join_branches bp0001000010010 bp0001000010011
private noncomputable def vp00010000100011_0 : Blocks := edgeBlocks% "full/vectors/00010000100011-V-0000.bin"
noncomputable def vp00010000100011 : Blocks := vp00010000100011_0
theorem coverp00010000100011 : Covers (-529261639/500000 : ℚ) vp00010000100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000100010_0 : Blocks := edgeBlocks% "full/vectors/00010000100010-V-0000.bin"
noncomputable def vp00010000100010 : Blocks := vp00010000100010_0
theorem coverp00010000100010 : Covers (-528761639/500000 : ℚ) vp00010000100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000010001_0 : Blocks := edgeBlocks% "full/vectors/0001000010001-V-0000.bin"
noncomputable def vp0001000010001 : Blocks := vp0001000010001_0
private theorem bp00010000100010 : Branch 0 (-528761639/1000000 : ℚ) vp0001000010001 := by
  apply branch_left_normalized (c:=vp00010000100010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-528761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-528761639/500000 : ℚ) by norm_num]
  exact coverp00010000100010
private noncomputable def ep00010000100011_0 : Blocks := edgeBlocks% "full/vectors/00010000100011-E-0000.bin"
noncomputable def ep00010000100011 : Blocks := ep00010000100011_0
private theorem idp00010000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000010001.list =
    C ((2:ℤ)^66) * horner X vp00010000100011.list + horner X ep00010000100011.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000100011 : Branch 1 (-528761639/1000000 : ℚ) vp0001000010001 := by
  apply branch_checked idp00010000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-528761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-529261639/500000 : ℚ) by norm_num]
  exact coverp00010000100011
theorem coverp0001000010001 : Covers (-528761639/1000000 : ℚ) vp0001000010001 := join_branches bp00010000100010 bp00010000100011
private noncomputable def vp00010000100001_0 : Blocks := edgeBlocks% "full/vectors/00010000100001-V-0000.bin"
noncomputable def vp00010000100001 : Blocks := vp00010000100001_0
theorem coverp00010000100001 : Covers (-528261639/500000 : ℚ) vp00010000100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000100000_0 : Blocks := edgeBlocks% "full/vectors/00010000100000-V-0000.bin"
noncomputable def vp00010000100000 : Blocks := vp00010000100000_0
theorem coverp00010000100000 : Covers (-527761639/500000 : ℚ) vp00010000100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000010000_0 : Blocks := edgeBlocks% "full/vectors/0001000010000-V-0000.bin"
noncomputable def vp0001000010000 : Blocks := vp0001000010000_0
private theorem bp00010000100000 : Branch 0 (-527761639/1000000 : ℚ) vp0001000010000 := by
  apply branch_left_normalized (c:=vp00010000100000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-527761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-527761639/500000 : ℚ) by norm_num]
  exact coverp00010000100000
private noncomputable def ep00010000100001_0 : Blocks := edgeBlocks% "full/vectors/00010000100001-E-0000.bin"
noncomputable def ep00010000100001 : Blocks := ep00010000100001_0
private theorem idp00010000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000010000.list =
    C ((2:ℤ)^67) * horner X vp00010000100001.list + horner X ep00010000100001.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000100001 : Branch 1 (-527761639/1000000 : ℚ) vp0001000010000 := by
  apply branch_checked idp00010000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-527761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-528261639/500000 : ℚ) by norm_num]
  exact coverp00010000100001
theorem coverp0001000010000 : Covers (-527761639/1000000 : ℚ) vp0001000010000 := join_branches bp00010000100000 bp00010000100001
private noncomputable def vp000100001000_0 : Blocks := edgeBlocks% "full/vectors/000100001000-V-0000.bin"
noncomputable def vp000100001000 : Blocks := vp000100001000_0
private theorem bp0001000010000 : Branch 0 (-527761639/2000000 : ℚ) vp000100001000 := by
  apply branch_left_normalized (c:=vp0001000010000) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-527761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-527761639/1000000 : ℚ) by norm_num]
  exact coverp0001000010000
private noncomputable def ep0001000010001_0 : Blocks := edgeBlocks% "full/vectors/0001000010001-E-0000.bin"
noncomputable def ep0001000010001 : Blocks := ep0001000010001_0
private theorem idp0001000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100001000.list =
    C ((2:ℤ)^114) * horner X vp0001000010001.list + horner X ep0001000010001.list := by
  exact edge_identity (B := (2:ℤ)^255) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000010001 : Branch 1 (-527761639/2000000 : ℚ) vp000100001000 := by
  apply branch_checked idp0001000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-527761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-528761639/1000000 : ℚ) by norm_num]
  exact coverp0001000010001
theorem coverp000100001000 : Covers (-527761639/2000000 : ℚ) vp000100001000 := join_branches bp0001000010000 bp0001000010001
private noncomputable def vp00010000100_0 : Blocks := edgeBlocks% "full/vectors/00010000100-V-0000.bin"
private noncomputable def vp00010000100_1 : Blocks := edgeBlocks% "full/vectors/00010000100-V-0001.bin"
noncomputable def vp00010000100 : Blocks := (Blocks.join vp00010000100_0 vp00010000100_1)
private theorem bp000100001000 : Branch 0 (-527761639/4000000 : ℚ) vp00010000100 := by
  apply branch_left_normalized (c:=vp000100001000) (k:=0) (m:=107) (by decide +kernel)
  rw [show 2*(-527761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-527761639/2000000 : ℚ) by norm_num]
  exact coverp000100001000
private noncomputable def ep000100001001_0 : Blocks := edgeBlocks% "full/vectors/000100001001-E-0000.bin"
private noncomputable def ep000100001001_1 : Blocks := edgeBlocks% "full/vectors/000100001001-E-0001.bin"
noncomputable def ep000100001001 : Blocks := (Blocks.join ep000100001001_0 ep000100001001_1)
private theorem idp000100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010000100.list =
    C ((2:ℤ)^205) * horner X vp000100001001.list + horner X ep000100001001.list := by
  exact edge_identity (B := (2:ℤ)^387) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100001001 : Branch 1 (-527761639/4000000 : ℚ) vp00010000100 := by
  apply branch_checked idp000100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-527761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-529761639/2000000 : ℚ) by norm_num]
  exact coverp000100001001
theorem coverp00010000100 : Covers (-527761639/4000000 : ℚ) vp00010000100 := join_branches bp000100001000 bp000100001001
private noncomputable def vp0001000010_0 : Blocks := edgeBlocks% "full/vectors/0001000010-V-0000.bin"
private noncomputable def vp0001000010_1 : Blocks := edgeBlocks% "full/vectors/0001000010-V-0001.bin"
private noncomputable def vp0001000010_2 : Blocks := edgeBlocks% "full/vectors/0001000010-V-0002.bin"
noncomputable def vp0001000010 : Blocks := (Blocks.join vp0001000010_0 (Blocks.join vp0001000010_1 vp0001000010_2))
private theorem bp00010000100 : Branch 0 (-527761639/8000000 : ℚ) vp0001000010 := by
  apply branch_left_normalized (c:=vp00010000100) (k:=0) (m:=193) (by decide +kernel)
  rw [show 2*(-527761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-527761639/4000000 : ℚ) by norm_num]
  exact coverp00010000100
private noncomputable def ep00010000101_0 : Blocks := edgeBlocks% "full/vectors/00010000101-E-0000.bin"
private noncomputable def ep00010000101_1 : Blocks := edgeBlocks% "full/vectors/00010000101-E-0001.bin"
private noncomputable def ep00010000101_2 : Blocks := edgeBlocks% "full/vectors/00010000101-E-0002.bin"
noncomputable def ep00010000101 : Blocks := (Blocks.join ep00010000101_0 (Blocks.join ep00010000101_1 ep00010000101_2))
private theorem idp00010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000010.list =
    C ((2:ℤ)^387) * horner X vp00010000101.list + horner X ep00010000101.list := by
  exact edge_identity (B := (2:ℤ)^647) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000101 : Branch 1 (-527761639/8000000 : ℚ) vp0001000010 := by
  apply branch_checked idp00010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-527761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-531761639/4000000 : ℚ) by norm_num]
  exact coverp00010000101
theorem coverp0001000010 : Covers (-527761639/8000000 : ℚ) vp0001000010 := join_branches bp00010000100 bp00010000101
private noncomputable def vp000100001_0 : Blocks := edgeBlocks% "full/vectors/000100001-V-0000.bin"
private noncomputable def vp000100001_1 : Blocks := edgeBlocks% "full/vectors/000100001-V-0001.bin"
private noncomputable def vp000100001_2 : Blocks := edgeBlocks% "full/vectors/000100001-V-0002.bin"
private noncomputable def vp000100001_3 : Blocks := edgeBlocks% "full/vectors/000100001-V-0003.bin"
private noncomputable def vp000100001_4 : Blocks := edgeBlocks% "full/vectors/000100001-V-0004.bin"
private noncomputable def vp000100001_5 : Blocks := edgeBlocks% "full/vectors/000100001-V-0005.bin"
noncomputable def vp000100001 : Blocks := (Blocks.join (Blocks.join vp000100001_0 (Blocks.join vp000100001_1 vp000100001_2)) (Blocks.join vp000100001_3 (Blocks.join vp000100001_4 vp000100001_5)))
private theorem bp0001000010 : Branch 0 (-527761639/16000000 : ℚ) vp000100001 := by
  apply branch_left_normalized (c:=vp0001000010) (k:=0) (m:=363) (by decide +kernel)
  rw [show 2*(-527761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-527761639/8000000 : ℚ) by norm_num]
  exact coverp0001000010
private noncomputable def ep0001000011_0 : Blocks := edgeBlocks% "full/vectors/0001000011-E-0000.bin"
private noncomputable def ep0001000011_1 : Blocks := edgeBlocks% "full/vectors/0001000011-E-0001.bin"
private noncomputable def ep0001000011_2 : Blocks := edgeBlocks% "full/vectors/0001000011-E-0002.bin"
private noncomputable def ep0001000011_3 : Blocks := edgeBlocks% "full/vectors/0001000011-E-0003.bin"
private noncomputable def ep0001000011_4 : Blocks := edgeBlocks% "full/vectors/0001000011-E-0004.bin"
private noncomputable def ep0001000011_5 : Blocks := edgeBlocks% "full/vectors/0001000011-E-0005.bin"
noncomputable def ep0001000011 : Blocks := (Blocks.join (Blocks.join ep0001000011_0 (Blocks.join ep0001000011_1 ep0001000011_2)) (Blocks.join ep0001000011_3 (Blocks.join ep0001000011_4 ep0001000011_5)))
private theorem idp0001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100001.list =
    C ((2:ℤ)^748) * horner X vp0001000011.list + horner X ep0001000011.list := by
  exact edge_identity (B := (2:ℤ)^1166) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000011 : Branch 1 (-527761639/16000000 : ℚ) vp000100001 := by
  apply branch_checked idp0001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-527761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-535761639/8000000 : ℚ) by norm_num]
  exact coverp0001000011
theorem coverp000100001 : Covers (-527761639/16000000 : ℚ) vp000100001 := join_branches bp0001000010 bp0001000011
private noncomputable def vp00010000011111_0 : Blocks := edgeBlocks% "full/vectors/00010000011111-V-0000.bin"
noncomputable def vp00010000011111 : Blocks := vp00010000011111_0
theorem coverp00010000011111 : Covers (-527261639/500000 : ℚ) vp00010000011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000011110_0 : Blocks := edgeBlocks% "full/vectors/00010000011110-V-0000.bin"
noncomputable def vp00010000011110 : Blocks := vp00010000011110_0
theorem coverp00010000011110 : Covers (-526761639/500000 : ℚ) vp00010000011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000001111_0 : Blocks := edgeBlocks% "full/vectors/0001000001111-V-0000.bin"
noncomputable def vp0001000001111 : Blocks := vp0001000001111_0
private theorem bp00010000011110 : Branch 0 (-526761639/1000000 : ℚ) vp0001000001111 := by
  apply branch_left_normalized (c:=vp00010000011110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-526761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-526761639/500000 : ℚ) by norm_num]
  exact coverp00010000011110
private noncomputable def ep00010000011111_0 : Blocks := edgeBlocks% "full/vectors/00010000011111-E-0000.bin"
noncomputable def ep00010000011111 : Blocks := ep00010000011111_0
private theorem idp00010000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000001111.list =
    C ((2:ℤ)^67) * horner X vp00010000011111.list + horner X ep00010000011111.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000011111 : Branch 1 (-526761639/1000000 : ℚ) vp0001000001111 := by
  apply branch_checked idp00010000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-526761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-527261639/500000 : ℚ) by norm_num]
  exact coverp00010000011111
theorem coverp0001000001111 : Covers (-526761639/1000000 : ℚ) vp0001000001111 := join_branches bp00010000011110 bp00010000011111
private noncomputable def vp00010000011101_0 : Blocks := edgeBlocks% "full/vectors/00010000011101-V-0000.bin"
noncomputable def vp00010000011101 : Blocks := vp00010000011101_0
theorem coverp00010000011101 : Covers (-526261639/500000 : ℚ) vp00010000011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000011100_0 : Blocks := edgeBlocks% "full/vectors/00010000011100-V-0000.bin"
noncomputable def vp00010000011100 : Blocks := vp00010000011100_0
theorem coverp00010000011100 : Covers (-525761639/500000 : ℚ) vp00010000011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000001110_0 : Blocks := edgeBlocks% "full/vectors/0001000001110-V-0000.bin"
noncomputable def vp0001000001110 : Blocks := vp0001000001110_0
private theorem bp00010000011100 : Branch 0 (-525761639/1000000 : ℚ) vp0001000001110 := by
  apply branch_left_normalized (c:=vp00010000011100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-525761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-525761639/500000 : ℚ) by norm_num]
  exact coverp00010000011100
private noncomputable def ep00010000011101_0 : Blocks := edgeBlocks% "full/vectors/00010000011101-E-0000.bin"
noncomputable def ep00010000011101 : Blocks := ep00010000011101_0
private theorem idp00010000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000001110.list =
    C ((2:ℤ)^68) * horner X vp00010000011101.list + horner X ep00010000011101.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000011101 : Branch 1 (-525761639/1000000 : ℚ) vp0001000001110 := by
  apply branch_checked idp00010000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-525761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-526261639/500000 : ℚ) by norm_num]
  exact coverp00010000011101
theorem coverp0001000001110 : Covers (-525761639/1000000 : ℚ) vp0001000001110 := join_branches bp00010000011100 bp00010000011101
private noncomputable def vp000100000111_0 : Blocks := edgeBlocks% "full/vectors/000100000111-V-0000.bin"
noncomputable def vp000100000111 : Blocks := vp000100000111_0
private theorem bp0001000001110 : Branch 0 (-525761639/2000000 : ℚ) vp000100000111 := by
  apply branch_left_normalized (c:=vp0001000001110) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-525761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-525761639/1000000 : ℚ) by norm_num]
  exact coverp0001000001110
private noncomputable def ep0001000001111_0 : Blocks := edgeBlocks% "full/vectors/0001000001111-E-0000.bin"
noncomputable def ep0001000001111 : Blocks := ep0001000001111_0
private theorem idp0001000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100000111.list =
    C ((2:ℤ)^114) * horner X vp0001000001111.list + horner X ep0001000001111.list := by
  exact edge_identity (B := (2:ℤ)^256) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000001111 : Branch 1 (-525761639/2000000 : ℚ) vp000100000111 := by
  apply branch_checked idp0001000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-525761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-526761639/1000000 : ℚ) by norm_num]
  exact coverp0001000001111
theorem coverp000100000111 : Covers (-525761639/2000000 : ℚ) vp000100000111 := join_branches bp0001000001110 bp0001000001111
private noncomputable def vp00010000011011_0 : Blocks := edgeBlocks% "full/vectors/00010000011011-V-0000.bin"
noncomputable def vp00010000011011 : Blocks := vp00010000011011_0
theorem coverp00010000011011 : Covers (-525261639/500000 : ℚ) vp00010000011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000011010_0 : Blocks := edgeBlocks% "full/vectors/00010000011010-V-0000.bin"
noncomputable def vp00010000011010 : Blocks := vp00010000011010_0
theorem coverp00010000011010 : Covers (-524761639/500000 : ℚ) vp00010000011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000001101_0 : Blocks := edgeBlocks% "full/vectors/0001000001101-V-0000.bin"
noncomputable def vp0001000001101 : Blocks := vp0001000001101_0
private theorem bp00010000011010 : Branch 0 (-524761639/1000000 : ℚ) vp0001000001101 := by
  apply branch_left_normalized (c:=vp00010000011010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-524761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-524761639/500000 : ℚ) by norm_num]
  exact coverp00010000011010
private noncomputable def ep00010000011011_0 : Blocks := edgeBlocks% "full/vectors/00010000011011-E-0000.bin"
noncomputable def ep00010000011011 : Blocks := ep00010000011011_0
private theorem idp00010000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000001101.list =
    C ((2:ℤ)^66) * horner X vp00010000011011.list + horner X ep00010000011011.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000011011 : Branch 1 (-524761639/1000000 : ℚ) vp0001000001101 := by
  apply branch_checked idp00010000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-524761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-525261639/500000 : ℚ) by norm_num]
  exact coverp00010000011011
theorem coverp0001000001101 : Covers (-524761639/1000000 : ℚ) vp0001000001101 := join_branches bp00010000011010 bp00010000011011
private noncomputable def vp00010000011001_0 : Blocks := edgeBlocks% "full/vectors/00010000011001-V-0000.bin"
noncomputable def vp00010000011001 : Blocks := vp00010000011001_0
theorem coverp00010000011001 : Covers (-524261639/500000 : ℚ) vp00010000011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000011000_0 : Blocks := edgeBlocks% "full/vectors/00010000011000-V-0000.bin"
noncomputable def vp00010000011000 : Blocks := vp00010000011000_0
theorem coverp00010000011000 : Covers (-523761639/500000 : ℚ) vp00010000011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000001100_0 : Blocks := edgeBlocks% "full/vectors/0001000001100-V-0000.bin"
noncomputable def vp0001000001100 : Blocks := vp0001000001100_0
private theorem bp00010000011000 : Branch 0 (-523761639/1000000 : ℚ) vp0001000001100 := by
  apply branch_left_normalized (c:=vp00010000011000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-523761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-523761639/500000 : ℚ) by norm_num]
  exact coverp00010000011000
private noncomputable def ep00010000011001_0 : Blocks := edgeBlocks% "full/vectors/00010000011001-E-0000.bin"
noncomputable def ep00010000011001 : Blocks := ep00010000011001_0
private theorem idp00010000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000001100.list =
    C ((2:ℤ)^66) * horner X vp00010000011001.list + horner X ep00010000011001.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000011001 : Branch 1 (-523761639/1000000 : ℚ) vp0001000001100 := by
  apply branch_checked idp00010000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-523761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-524261639/500000 : ℚ) by norm_num]
  exact coverp00010000011001
theorem coverp0001000001100 : Covers (-523761639/1000000 : ℚ) vp0001000001100 := join_branches bp00010000011000 bp00010000011001
private noncomputable def vp000100000110_0 : Blocks := edgeBlocks% "full/vectors/000100000110-V-0000.bin"
noncomputable def vp000100000110 : Blocks := vp000100000110_0
private theorem bp0001000001100 : Branch 0 (-523761639/2000000 : ℚ) vp000100000110 := by
  apply branch_left_normalized (c:=vp0001000001100) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-523761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-523761639/1000000 : ℚ) by norm_num]
  exact coverp0001000001100
private noncomputable def ep0001000001101_0 : Blocks := edgeBlocks% "full/vectors/0001000001101-E-0000.bin"
noncomputable def ep0001000001101 : Blocks := ep0001000001101_0
private theorem idp0001000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100000110.list =
    C ((2:ℤ)^113) * horner X vp0001000001101.list + horner X ep0001000001101.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000001101 : Branch 1 (-523761639/2000000 : ℚ) vp000100000110 := by
  apply branch_checked idp0001000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-523761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-524761639/1000000 : ℚ) by norm_num]
  exact coverp0001000001101
theorem coverp000100000110 : Covers (-523761639/2000000 : ℚ) vp000100000110 := join_branches bp0001000001100 bp0001000001101
private noncomputable def vp00010000011_0 : Blocks := edgeBlocks% "full/vectors/00010000011-V-0000.bin"
private noncomputable def vp00010000011_1 : Blocks := edgeBlocks% "full/vectors/00010000011-V-0001.bin"
noncomputable def vp00010000011 : Blocks := (Blocks.join vp00010000011_0 vp00010000011_1)
private theorem bp000100000110 : Branch 0 (-523761639/4000000 : ℚ) vp00010000011 := by
  apply branch_left_normalized (c:=vp000100000110) (k:=0) (m:=107) (by decide +kernel)
  rw [show 2*(-523761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-523761639/2000000 : ℚ) by norm_num]
  exact coverp000100000110
private noncomputable def ep000100000111_0 : Blocks := edgeBlocks% "full/vectors/000100000111-E-0000.bin"
private noncomputable def ep000100000111_1 : Blocks := edgeBlocks% "full/vectors/000100000111-E-0001.bin"
noncomputable def ep000100000111 : Blocks := (Blocks.join ep000100000111_0 ep000100000111_1)
private theorem idp000100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010000011.list =
    C ((2:ℤ)^204) * horner X vp000100000111.list + horner X ep000100000111.list := by
  exact edge_identity (B := (2:ℤ)^386) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100000111 : Branch 1 (-523761639/4000000 : ℚ) vp00010000011 := by
  apply branch_checked idp000100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-523761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-525761639/2000000 : ℚ) by norm_num]
  exact coverp000100000111
theorem coverp00010000011 : Covers (-523761639/4000000 : ℚ) vp00010000011 := join_branches bp000100000110 bp000100000111
private noncomputable def vp00010000010111_0 : Blocks := edgeBlocks% "full/vectors/00010000010111-V-0000.bin"
noncomputable def vp00010000010111 : Blocks := vp00010000010111_0
theorem coverp00010000010111 : Covers (-523261639/500000 : ℚ) vp00010000010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000010110_0 : Blocks := edgeBlocks% "full/vectors/00010000010110-V-0000.bin"
noncomputable def vp00010000010110 : Blocks := vp00010000010110_0
theorem coverp00010000010110 : Covers (-522761639/500000 : ℚ) vp00010000010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000001011_0 : Blocks := edgeBlocks% "full/vectors/0001000001011-V-0000.bin"
noncomputable def vp0001000001011 : Blocks := vp0001000001011_0
private theorem bp00010000010110 : Branch 0 (-522761639/1000000 : ℚ) vp0001000001011 := by
  apply branch_left_normalized (c:=vp00010000010110) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-522761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-522761639/500000 : ℚ) by norm_num]
  exact coverp00010000010110
private noncomputable def ep00010000010111_0 : Blocks := edgeBlocks% "full/vectors/00010000010111-E-0000.bin"
noncomputable def ep00010000010111 : Blocks := ep00010000010111_0
private theorem idp00010000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000001011.list =
    C ((2:ℤ)^65) * horner X vp00010000010111.list + horner X ep00010000010111.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000010111 : Branch 1 (-522761639/1000000 : ℚ) vp0001000001011 := by
  apply branch_checked idp00010000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-522761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-523261639/500000 : ℚ) by norm_num]
  exact coverp00010000010111
theorem coverp0001000001011 : Covers (-522761639/1000000 : ℚ) vp0001000001011 := join_branches bp00010000010110 bp00010000010111
private noncomputable def vp00010000010101_0 : Blocks := edgeBlocks% "full/vectors/00010000010101-V-0000.bin"
noncomputable def vp00010000010101 : Blocks := vp00010000010101_0
theorem coverp00010000010101 : Covers (-522261639/500000 : ℚ) vp00010000010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000010100_0 : Blocks := edgeBlocks% "full/vectors/00010000010100-V-0000.bin"
noncomputable def vp00010000010100 : Blocks := vp00010000010100_0
theorem coverp00010000010100 : Covers (-521761639/500000 : ℚ) vp00010000010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000001010_0 : Blocks := edgeBlocks% "full/vectors/0001000001010-V-0000.bin"
noncomputable def vp0001000001010 : Blocks := vp0001000001010_0
private theorem bp00010000010100 : Branch 0 (-521761639/1000000 : ℚ) vp0001000001010 := by
  apply branch_left_normalized (c:=vp00010000010100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-521761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-521761639/500000 : ℚ) by norm_num]
  exact coverp00010000010100
private noncomputable def ep00010000010101_0 : Blocks := edgeBlocks% "full/vectors/00010000010101-E-0000.bin"
noncomputable def ep00010000010101 : Blocks := ep00010000010101_0
private theorem idp00010000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000001010.list =
    C ((2:ℤ)^66) * horner X vp00010000010101.list + horner X ep00010000010101.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000010101 : Branch 1 (-521761639/1000000 : ℚ) vp0001000001010 := by
  apply branch_checked idp00010000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-521761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-522261639/500000 : ℚ) by norm_num]
  exact coverp00010000010101
theorem coverp0001000001010 : Covers (-521761639/1000000 : ℚ) vp0001000001010 := join_branches bp00010000010100 bp00010000010101
private noncomputable def vp000100000101_0 : Blocks := edgeBlocks% "full/vectors/000100000101-V-0000.bin"
noncomputable def vp000100000101 : Blocks := vp000100000101_0
private theorem bp0001000001010 : Branch 0 (-521761639/2000000 : ℚ) vp000100000101 := by
  apply branch_left_normalized (c:=vp0001000001010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-521761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-521761639/1000000 : ℚ) by norm_num]
  exact coverp0001000001010
private noncomputable def ep0001000001011_0 : Blocks := edgeBlocks% "full/vectors/0001000001011-E-0000.bin"
noncomputable def ep0001000001011 : Blocks := ep0001000001011_0
private theorem idp0001000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100000101.list =
    C ((2:ℤ)^112) * horner X vp0001000001011.list + horner X ep0001000001011.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000001011 : Branch 1 (-521761639/2000000 : ℚ) vp000100000101 := by
  apply branch_checked idp0001000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-521761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-522761639/1000000 : ℚ) by norm_num]
  exact coverp0001000001011
theorem coverp000100000101 : Covers (-521761639/2000000 : ℚ) vp000100000101 := join_branches bp0001000001010 bp0001000001011
private noncomputable def vp00010000010011_0 : Blocks := edgeBlocks% "full/vectors/00010000010011-V-0000.bin"
noncomputable def vp00010000010011 : Blocks := vp00010000010011_0
theorem coverp00010000010011 : Covers (-521261639/500000 : ℚ) vp00010000010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000010010_0 : Blocks := edgeBlocks% "full/vectors/00010000010010-V-0000.bin"
noncomputable def vp00010000010010 : Blocks := vp00010000010010_0
theorem coverp00010000010010 : Covers (-520761639/500000 : ℚ) vp00010000010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000001001_0 : Blocks := edgeBlocks% "full/vectors/0001000001001-V-0000.bin"
noncomputable def vp0001000001001 : Blocks := vp0001000001001_0
private theorem bp00010000010010 : Branch 0 (-520761639/1000000 : ℚ) vp0001000001001 := by
  apply branch_left_normalized (c:=vp00010000010010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-520761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-520761639/500000 : ℚ) by norm_num]
  exact coverp00010000010010
private noncomputable def ep00010000010011_0 : Blocks := edgeBlocks% "full/vectors/00010000010011-E-0000.bin"
noncomputable def ep00010000010011 : Blocks := ep00010000010011_0
private theorem idp00010000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000001001.list =
    C ((2:ℤ)^66) * horner X vp00010000010011.list + horner X ep00010000010011.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000010011 : Branch 1 (-520761639/1000000 : ℚ) vp0001000001001 := by
  apply branch_checked idp00010000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-520761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-521261639/500000 : ℚ) by norm_num]
  exact coverp00010000010011
theorem coverp0001000001001 : Covers (-520761639/1000000 : ℚ) vp0001000001001 := join_branches bp00010000010010 bp00010000010011
private noncomputable def vp00010000010001_0 : Blocks := edgeBlocks% "full/vectors/00010000010001-V-0000.bin"
noncomputable def vp00010000010001 : Blocks := vp00010000010001_0
theorem coverp00010000010001 : Covers (-520261639/500000 : ℚ) vp00010000010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000010000_0 : Blocks := edgeBlocks% "full/vectors/00010000010000-V-0000.bin"
noncomputable def vp00010000010000 : Blocks := vp00010000010000_0
theorem coverp00010000010000 : Covers (-519761639/500000 : ℚ) vp00010000010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000001000_0 : Blocks := edgeBlocks% "full/vectors/0001000001000-V-0000.bin"
noncomputable def vp0001000001000 : Blocks := vp0001000001000_0
private theorem bp00010000010000 : Branch 0 (-519761639/1000000 : ℚ) vp0001000001000 := by
  apply branch_left_normalized (c:=vp00010000010000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-519761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-519761639/500000 : ℚ) by norm_num]
  exact coverp00010000010000
private noncomputable def ep00010000010001_0 : Blocks := edgeBlocks% "full/vectors/00010000010001-E-0000.bin"
noncomputable def ep00010000010001 : Blocks := ep00010000010001_0
private theorem idp00010000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000001000.list =
    C ((2:ℤ)^66) * horner X vp00010000010001.list + horner X ep00010000010001.list := by
  exact edge_identity (B := (2:ℤ)^186) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000010001 : Branch 1 (-519761639/1000000 : ℚ) vp0001000001000 := by
  apply branch_checked idp00010000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-519761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-520261639/500000 : ℚ) by norm_num]
  exact coverp00010000010001
theorem coverp0001000001000 : Covers (-519761639/1000000 : ℚ) vp0001000001000 := join_branches bp00010000010000 bp00010000010001
private noncomputable def vp000100000100_0 : Blocks := edgeBlocks% "full/vectors/000100000100-V-0000.bin"
noncomputable def vp000100000100 : Blocks := vp000100000100_0
private theorem bp0001000001000 : Branch 0 (-519761639/2000000 : ℚ) vp000100000100 := by
  apply branch_left_normalized (c:=vp0001000001000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-519761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-519761639/1000000 : ℚ) by norm_num]
  exact coverp0001000001000
private noncomputable def ep0001000001001_0 : Blocks := edgeBlocks% "full/vectors/0001000001001-E-0000.bin"
noncomputable def ep0001000001001 : Blocks := ep0001000001001_0
private theorem idp0001000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100000100.list =
    C ((2:ℤ)^113) * horner X vp0001000001001.list + horner X ep0001000001001.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000001001 : Branch 1 (-519761639/2000000 : ℚ) vp000100000100 := by
  apply branch_checked idp0001000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-519761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-520761639/1000000 : ℚ) by norm_num]
  exact coverp0001000001001
theorem coverp000100000100 : Covers (-519761639/2000000 : ℚ) vp000100000100 := join_branches bp0001000001000 bp0001000001001
private noncomputable def vp00010000010_0 : Blocks := edgeBlocks% "full/vectors/00010000010-V-0000.bin"
private noncomputable def vp00010000010_1 : Blocks := edgeBlocks% "full/vectors/00010000010-V-0001.bin"
noncomputable def vp00010000010 : Blocks := (Blocks.join vp00010000010_0 vp00010000010_1)
private theorem bp000100000100 : Branch 0 (-519761639/4000000 : ℚ) vp00010000010 := by
  apply branch_left_normalized (c:=vp000100000100) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-519761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-519761639/2000000 : ℚ) by norm_num]
  exact coverp000100000100
private noncomputable def ep000100000101_0 : Blocks := edgeBlocks% "full/vectors/000100000101-E-0000.bin"
private noncomputable def ep000100000101_1 : Blocks := edgeBlocks% "full/vectors/000100000101-E-0001.bin"
noncomputable def ep000100000101 : Blocks := (Blocks.join ep000100000101_0 ep000100000101_1)
private theorem idp000100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010000010.list =
    C ((2:ℤ)^205) * horner X vp000100000101.list + horner X ep000100000101.list := by
  exact edge_identity (B := (2:ℤ)^384) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100000101 : Branch 1 (-519761639/4000000 : ℚ) vp00010000010 := by
  apply branch_checked idp000100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-519761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-521761639/2000000 : ℚ) by norm_num]
  exact coverp000100000101
theorem coverp00010000010 : Covers (-519761639/4000000 : ℚ) vp00010000010 := join_branches bp000100000100 bp000100000101
private noncomputable def vp0001000001_0 : Blocks := edgeBlocks% "full/vectors/0001000001-V-0000.bin"
private noncomputable def vp0001000001_1 : Blocks := edgeBlocks% "full/vectors/0001000001-V-0001.bin"
private noncomputable def vp0001000001_2 : Blocks := edgeBlocks% "full/vectors/0001000001-V-0002.bin"
noncomputable def vp0001000001 : Blocks := (Blocks.join vp0001000001_0 (Blocks.join vp0001000001_1 vp0001000001_2))
private theorem bp00010000010 : Branch 0 (-519761639/8000000 : ℚ) vp0001000001 := by
  apply branch_left_normalized (c:=vp00010000010) (k:=0) (m:=192) (by decide +kernel)
  rw [show 2*(-519761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-519761639/4000000 : ℚ) by norm_num]
  exact coverp00010000010
private noncomputable def ep00010000011_0 : Blocks := edgeBlocks% "full/vectors/00010000011-E-0000.bin"
private noncomputable def ep00010000011_1 : Blocks := edgeBlocks% "full/vectors/00010000011-E-0001.bin"
private noncomputable def ep00010000011_2 : Blocks := edgeBlocks% "full/vectors/00010000011-E-0002.bin"
noncomputable def ep00010000011 : Blocks := (Blocks.join ep00010000011_0 (Blocks.join ep00010000011_1 ep00010000011_2))
private theorem idp00010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000001.list =
    C ((2:ℤ)^387) * horner X vp00010000011.list + horner X ep00010000011.list := by
  exact edge_identity (B := (2:ℤ)^648) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000011 : Branch 1 (-519761639/8000000 : ℚ) vp0001000001 := by
  apply branch_checked idp00010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-519761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-523761639/4000000 : ℚ) by norm_num]
  exact coverp00010000011
theorem coverp0001000001 : Covers (-519761639/8000000 : ℚ) vp0001000001 := join_branches bp00010000010 bp00010000011
private noncomputable def vp00010000001111_0 : Blocks := edgeBlocks% "full/vectors/00010000001111-V-0000.bin"
noncomputable def vp00010000001111 : Blocks := vp00010000001111_0
theorem coverp00010000001111 : Covers (-519261639/500000 : ℚ) vp00010000001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000001110_0 : Blocks := edgeBlocks% "full/vectors/00010000001110-V-0000.bin"
noncomputable def vp00010000001110 : Blocks := vp00010000001110_0
theorem coverp00010000001110 : Covers (-518761639/500000 : ℚ) vp00010000001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000000111_0 : Blocks := edgeBlocks% "full/vectors/0001000000111-V-0000.bin"
noncomputable def vp0001000000111 : Blocks := vp0001000000111_0
private theorem bp00010000001110 : Branch 0 (-518761639/1000000 : ℚ) vp0001000000111 := by
  apply branch_left_normalized (c:=vp00010000001110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-518761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-518761639/500000 : ℚ) by norm_num]
  exact coverp00010000001110
private noncomputable def ep00010000001111_0 : Blocks := edgeBlocks% "full/vectors/00010000001111-E-0000.bin"
noncomputable def ep00010000001111 : Blocks := ep00010000001111_0
private theorem idp00010000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000000111.list =
    C ((2:ℤ)^68) * horner X vp00010000001111.list + horner X ep00010000001111.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000001111 : Branch 1 (-518761639/1000000 : ℚ) vp0001000000111 := by
  apply branch_checked idp00010000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-518761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-519261639/500000 : ℚ) by norm_num]
  exact coverp00010000001111
theorem coverp0001000000111 : Covers (-518761639/1000000 : ℚ) vp0001000000111 := join_branches bp00010000001110 bp00010000001111
private noncomputable def vp00010000001101_0 : Blocks := edgeBlocks% "full/vectors/00010000001101-V-0000.bin"
noncomputable def vp00010000001101 : Blocks := vp00010000001101_0
theorem coverp00010000001101 : Covers (-518261639/500000 : ℚ) vp00010000001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000001100_0 : Blocks := edgeBlocks% "full/vectors/00010000001100-V-0000.bin"
noncomputable def vp00010000001100 : Blocks := vp00010000001100_0
theorem coverp00010000001100 : Covers (-517761639/500000 : ℚ) vp00010000001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000000110_0 : Blocks := edgeBlocks% "full/vectors/0001000000110-V-0000.bin"
noncomputable def vp0001000000110 : Blocks := vp0001000000110_0
private theorem bp00010000001100 : Branch 0 (-517761639/1000000 : ℚ) vp0001000000110 := by
  apply branch_left_normalized (c:=vp00010000001100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-517761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-517761639/500000 : ℚ) by norm_num]
  exact coverp00010000001100
private noncomputable def ep00010000001101_0 : Blocks := edgeBlocks% "full/vectors/00010000001101-E-0000.bin"
noncomputable def ep00010000001101 : Blocks := ep00010000001101_0
private theorem idp00010000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000000110.list =
    C ((2:ℤ)^64) * horner X vp00010000001101.list + horner X ep00010000001101.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000001101 : Branch 1 (-517761639/1000000 : ℚ) vp0001000000110 := by
  apply branch_checked idp00010000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-517761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-518261639/500000 : ℚ) by norm_num]
  exact coverp00010000001101
theorem coverp0001000000110 : Covers (-517761639/1000000 : ℚ) vp0001000000110 := join_branches bp00010000001100 bp00010000001101
private noncomputable def vp000100000011_0 : Blocks := edgeBlocks% "full/vectors/000100000011-V-0000.bin"
noncomputable def vp000100000011 : Blocks := vp000100000011_0
private theorem bp0001000000110 : Branch 0 (-517761639/2000000 : ℚ) vp000100000011 := by
  apply branch_left_normalized (c:=vp0001000000110) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-517761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-517761639/1000000 : ℚ) by norm_num]
  exact coverp0001000000110
private noncomputable def ep0001000000111_0 : Blocks := edgeBlocks% "full/vectors/0001000000111-E-0000.bin"
noncomputable def ep0001000000111 : Blocks := ep0001000000111_0
private theorem idp0001000000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100000011.list =
    C ((2:ℤ)^110) * horner X vp0001000000111.list + horner X ep0001000000111.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000000111 : Branch 1 (-517761639/2000000 : ℚ) vp000100000011 := by
  apply branch_checked idp0001000000111 (by positivity) (by decide +kernel)
  rw [show 2*(-517761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-518761639/1000000 : ℚ) by norm_num]
  exact coverp0001000000111
theorem coverp000100000011 : Covers (-517761639/2000000 : ℚ) vp000100000011 := join_branches bp0001000000110 bp0001000000111
private noncomputable def vp00010000001011_0 : Blocks := edgeBlocks% "full/vectors/00010000001011-V-0000.bin"
noncomputable def vp00010000001011 : Blocks := vp00010000001011_0
theorem coverp00010000001011 : Covers (-517261639/500000 : ℚ) vp00010000001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000001010_0 : Blocks := edgeBlocks% "full/vectors/00010000001010-V-0000.bin"
noncomputable def vp00010000001010 : Blocks := vp00010000001010_0
theorem coverp00010000001010 : Covers (-516761639/500000 : ℚ) vp00010000001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000000101_0 : Blocks := edgeBlocks% "full/vectors/0001000000101-V-0000.bin"
noncomputable def vp0001000000101 : Blocks := vp0001000000101_0
private theorem bp00010000001010 : Branch 0 (-516761639/1000000 : ℚ) vp0001000000101 := by
  apply branch_left_normalized (c:=vp00010000001010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-516761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-516761639/500000 : ℚ) by norm_num]
  exact coverp00010000001010
private noncomputable def ep00010000001011_0 : Blocks := edgeBlocks% "full/vectors/00010000001011-E-0000.bin"
noncomputable def ep00010000001011 : Blocks := ep00010000001011_0
private theorem idp00010000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000000101.list =
    C ((2:ℤ)^64) * horner X vp00010000001011.list + horner X ep00010000001011.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000001011 : Branch 1 (-516761639/1000000 : ℚ) vp0001000000101 := by
  apply branch_checked idp00010000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-516761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-517261639/500000 : ℚ) by norm_num]
  exact coverp00010000001011
theorem coverp0001000000101 : Covers (-516761639/1000000 : ℚ) vp0001000000101 := join_branches bp00010000001010 bp00010000001011
private noncomputable def vp00010000001001_0 : Blocks := edgeBlocks% "full/vectors/00010000001001-V-0000.bin"
noncomputable def vp00010000001001 : Blocks := vp00010000001001_0
theorem coverp00010000001001 : Covers (-516261639/500000 : ℚ) vp00010000001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010000001000_0 : Blocks := edgeBlocks% "full/vectors/00010000001000-V-0000.bin"
noncomputable def vp00010000001000 : Blocks := vp00010000001000_0
theorem coverp00010000001000 : Covers (-515761639/500000 : ℚ) vp00010000001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000000100_0 : Blocks := edgeBlocks% "full/vectors/0001000000100-V-0000.bin"
noncomputable def vp0001000000100 : Blocks := vp0001000000100_0
private theorem bp00010000001000 : Branch 0 (-515761639/1000000 : ℚ) vp0001000000100 := by
  apply branch_left_normalized (c:=vp00010000001000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-515761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-515761639/500000 : ℚ) by norm_num]
  exact coverp00010000001000
private noncomputable def ep00010000001001_0 : Blocks := edgeBlocks% "full/vectors/00010000001001-E-0000.bin"
noncomputable def ep00010000001001 : Blocks := ep00010000001001_0
private theorem idp00010000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000000100.list =
    C ((2:ℤ)^63) * horner X vp00010000001001.list + horner X ep00010000001001.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000001001 : Branch 1 (-515761639/1000000 : ℚ) vp0001000000100 := by
  apply branch_checked idp00010000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-515761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-516261639/500000 : ℚ) by norm_num]
  exact coverp00010000001001
theorem coverp0001000000100 : Covers (-515761639/1000000 : ℚ) vp0001000000100 := join_branches bp00010000001000 bp00010000001001
private noncomputable def vp000100000010_0 : Blocks := edgeBlocks% "full/vectors/000100000010-V-0000.bin"
noncomputable def vp000100000010 : Blocks := vp000100000010_0
private theorem bp0001000000100 : Branch 0 (-515761639/2000000 : ℚ) vp000100000010 := by
  apply branch_left_normalized (c:=vp0001000000100) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-515761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-515761639/1000000 : ℚ) by norm_num]
  exact coverp0001000000100
private noncomputable def ep0001000000101_0 : Blocks := edgeBlocks% "full/vectors/0001000000101-E-0000.bin"
noncomputable def ep0001000000101 : Blocks := ep0001000000101_0
private theorem idp0001000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100000010.list =
    C ((2:ℤ)^109) * horner X vp0001000000101.list + horner X ep0001000000101.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000000101 : Branch 1 (-515761639/2000000 : ℚ) vp000100000010 := by
  apply branch_checked idp0001000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-515761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-516761639/1000000 : ℚ) by norm_num]
  exact coverp0001000000101
theorem coverp000100000010 : Covers (-515761639/2000000 : ℚ) vp000100000010 := join_branches bp0001000000100 bp0001000000101
private noncomputable def vp00010000001_0 : Blocks := edgeBlocks% "full/vectors/00010000001-V-0000.bin"
private noncomputable def vp00010000001_1 : Blocks := edgeBlocks% "full/vectors/00010000001-V-0001.bin"
noncomputable def vp00010000001 : Blocks := (Blocks.join vp00010000001_0 vp00010000001_1)
private theorem bp000100000010 : Branch 0 (-515761639/4000000 : ℚ) vp00010000001 := by
  apply branch_left_normalized (c:=vp000100000010) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-515761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-515761639/2000000 : ℚ) by norm_num]
  exact coverp000100000010
private noncomputable def ep000100000011_0 : Blocks := edgeBlocks% "full/vectors/000100000011-E-0000.bin"
private noncomputable def ep000100000011_1 : Blocks := edgeBlocks% "full/vectors/000100000011-E-0001.bin"
noncomputable def ep000100000011 : Blocks := (Blocks.join ep000100000011_0 ep000100000011_1)
private theorem idp000100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010000001.list =
    C ((2:ℤ)^199) * horner X vp000100000011.list + horner X ep000100000011.list := by
  exact edge_identity (B := (2:ℤ)^378) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100000011 : Branch 1 (-515761639/4000000 : ℚ) vp00010000001 := by
  apply branch_checked idp000100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-515761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-517761639/2000000 : ℚ) by norm_num]
  exact coverp000100000011
theorem coverp00010000001 : Covers (-515761639/4000000 : ℚ) vp00010000001 := join_branches bp000100000010 bp000100000011
private noncomputable def vp0001000000011_0 : Blocks := edgeBlocks% "full/vectors/0001000000011-V-0000.bin"
noncomputable def vp0001000000011 : Blocks := vp0001000000011_0
theorem coverp0001000000011 : Covers (-514761639/1000000 : ℚ) vp0001000000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000000010_0 : Blocks := edgeBlocks% "full/vectors/0001000000010-V-0000.bin"
noncomputable def vp0001000000010 : Blocks := vp0001000000010_0
theorem coverp0001000000010 : Covers (-513761639/1000000 : ℚ) vp0001000000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000100000001_0 : Blocks := edgeBlocks% "full/vectors/000100000001-V-0000.bin"
noncomputable def vp000100000001 : Blocks := vp000100000001_0
private theorem bp0001000000010 : Branch 0 (-513761639/2000000 : ℚ) vp000100000001 := by
  apply branch_left_normalized (c:=vp0001000000010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-513761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-513761639/1000000 : ℚ) by norm_num]
  exact coverp0001000000010
private noncomputable def ep0001000000011_0 : Blocks := edgeBlocks% "full/vectors/0001000000011-E-0000.bin"
noncomputable def ep0001000000011 : Blocks := ep0001000000011_0
private theorem idp0001000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100000001.list =
    C ((2:ℤ)^109) * horner X vp0001000000011.list + horner X ep0001000000011.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000000011 : Branch 1 (-513761639/2000000 : ℚ) vp000100000001 := by
  apply branch_checked idp0001000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-513761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-514761639/1000000 : ℚ) by norm_num]
  exact coverp0001000000011
theorem coverp000100000001 : Covers (-513761639/2000000 : ℚ) vp000100000001 := join_branches bp0001000000010 bp0001000000011
private noncomputable def vp0001000000001_0 : Blocks := edgeBlocks% "full/vectors/0001000000001-V-0000.bin"
noncomputable def vp0001000000001 : Blocks := vp0001000000001_0
theorem coverp0001000000001 : Covers (-512761639/1000000 : ℚ) vp0001000000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001000000000_0 : Blocks := edgeBlocks% "full/vectors/0001000000000-V-0000.bin"
noncomputable def vp0001000000000 : Blocks := vp0001000000000_0
theorem coverp0001000000000 : Covers (-511761639/1000000 : ℚ) vp0001000000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000100000000_0 : Blocks := edgeBlocks% "full/vectors/000100000000-V-0000.bin"
noncomputable def vp000100000000 : Blocks := vp000100000000_0
private theorem bp0001000000000 : Branch 0 (-511761639/2000000 : ℚ) vp000100000000 := by
  apply branch_left_normalized (c:=vp0001000000000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-511761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-511761639/1000000 : ℚ) by norm_num]
  exact coverp0001000000000
private noncomputable def ep0001000000001_0 : Blocks := edgeBlocks% "full/vectors/0001000000001-E-0000.bin"
noncomputable def ep0001000000001 : Blocks := ep0001000000001_0
private theorem idp0001000000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100000000.list =
    C ((2:ℤ)^108) * horner X vp0001000000001.list + horner X ep0001000000001.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000000001 : Branch 1 (-511761639/2000000 : ℚ) vp000100000000 := by
  apply branch_checked idp0001000000001 (by positivity) (by decide +kernel)
  rw [show 2*(-511761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-512761639/1000000 : ℚ) by norm_num]
  exact coverp0001000000001
theorem coverp000100000000 : Covers (-511761639/2000000 : ℚ) vp000100000000 := join_branches bp0001000000000 bp0001000000001
private noncomputable def vp00010000000_0 : Blocks := edgeBlocks% "full/vectors/00010000000-V-0000.bin"
private noncomputable def vp00010000000_1 : Blocks := edgeBlocks% "full/vectors/00010000000-V-0001.bin"
noncomputable def vp00010000000 : Blocks := (Blocks.join vp00010000000_0 vp00010000000_1)
private theorem bp000100000000 : Branch 0 (-511761639/4000000 : ℚ) vp00010000000 := by
  apply branch_left_normalized (c:=vp000100000000) (k:=0) (m:=102) (by decide +kernel)
  rw [show 2*(-511761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-511761639/2000000 : ℚ) by norm_num]
  exact coverp000100000000
private noncomputable def ep000100000001_0 : Blocks := edgeBlocks% "full/vectors/000100000001-E-0000.bin"
private noncomputable def ep000100000001_1 : Blocks := edgeBlocks% "full/vectors/000100000001-E-0001.bin"
noncomputable def ep000100000001 : Blocks := (Blocks.join ep000100000001_0 ep000100000001_1)
private theorem idp000100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010000000.list =
    C ((2:ℤ)^200) * horner X vp000100000001.list + horner X ep000100000001.list := by
  exact edge_identity (B := (2:ℤ)^374) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100000001 : Branch 1 (-511761639/4000000 : ℚ) vp00010000000 := by
  apply branch_checked idp000100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-511761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-513761639/2000000 : ℚ) by norm_num]
  exact coverp000100000001
theorem coverp00010000000 : Covers (-511761639/4000000 : ℚ) vp00010000000 := join_branches bp000100000000 bp000100000001
private noncomputable def vp0001000000_0 : Blocks := edgeBlocks% "full/vectors/0001000000-V-0000.bin"
private noncomputable def vp0001000000_1 : Blocks := edgeBlocks% "full/vectors/0001000000-V-0001.bin"
private noncomputable def vp0001000000_2 : Blocks := edgeBlocks% "full/vectors/0001000000-V-0002.bin"
noncomputable def vp0001000000 : Blocks := (Blocks.join vp0001000000_0 (Blocks.join vp0001000000_1 vp0001000000_2))
private theorem bp00010000000 : Branch 0 (-511761639/8000000 : ℚ) vp0001000000 := by
  apply branch_left_normalized (c:=vp00010000000) (k:=0) (m:=189) (by decide +kernel)
  rw [show 2*(-511761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-511761639/4000000 : ℚ) by norm_num]
  exact coverp00010000000
private noncomputable def ep00010000001_0 : Blocks := edgeBlocks% "full/vectors/00010000001-E-0000.bin"
private noncomputable def ep00010000001_1 : Blocks := edgeBlocks% "full/vectors/00010000001-E-0001.bin"
private noncomputable def ep00010000001_2 : Blocks := edgeBlocks% "full/vectors/00010000001-E-0002.bin"
noncomputable def ep00010000001 : Blocks := (Blocks.join ep00010000001_0 (Blocks.join ep00010000001_1 ep00010000001_2))
private theorem idp00010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000000.list =
    C ((2:ℤ)^383) * horner X vp00010000001.list + horner X ep00010000001.list := by
  exact edge_identity (B := (2:ℤ)^639) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010000001 : Branch 1 (-511761639/8000000 : ℚ) vp0001000000 := by
  apply branch_checked idp00010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-511761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-515761639/4000000 : ℚ) by norm_num]
  exact coverp00010000001
theorem coverp0001000000 : Covers (-511761639/8000000 : ℚ) vp0001000000 := join_branches bp00010000000 bp00010000001
private noncomputable def vp000100000_0 : Blocks := edgeBlocks% "full/vectors/000100000-V-0000.bin"
private noncomputable def vp000100000_1 : Blocks := edgeBlocks% "full/vectors/000100000-V-0001.bin"
private noncomputable def vp000100000_2 : Blocks := edgeBlocks% "full/vectors/000100000-V-0002.bin"
private noncomputable def vp000100000_3 : Blocks := edgeBlocks% "full/vectors/000100000-V-0003.bin"
private noncomputable def vp000100000_4 : Blocks := edgeBlocks% "full/vectors/000100000-V-0004.bin"
private noncomputable def vp000100000_5 : Blocks := edgeBlocks% "full/vectors/000100000-V-0005.bin"
noncomputable def vp000100000 : Blocks := (Blocks.join (Blocks.join vp000100000_0 (Blocks.join vp000100000_1 vp000100000_2)) (Blocks.join vp000100000_3 (Blocks.join vp000100000_4 vp000100000_5)))
private theorem bp0001000000 : Branch 0 (-511761639/16000000 : ℚ) vp000100000 := by
  apply branch_left_normalized (c:=vp0001000000) (k:=0) (m:=362) (by decide +kernel)
  rw [show 2*(-511761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-511761639/8000000 : ℚ) by norm_num]
  exact coverp0001000000
private noncomputable def ep0001000001_0 : Blocks := edgeBlocks% "full/vectors/0001000001-E-0000.bin"
private noncomputable def ep0001000001_1 : Blocks := edgeBlocks% "full/vectors/0001000001-E-0001.bin"
private noncomputable def ep0001000001_2 : Blocks := edgeBlocks% "full/vectors/0001000001-E-0002.bin"
private noncomputable def ep0001000001_3 : Blocks := edgeBlocks% "full/vectors/0001000001-E-0003.bin"
private noncomputable def ep0001000001_4 : Blocks := edgeBlocks% "full/vectors/0001000001-E-0004.bin"
private noncomputable def ep0001000001_5 : Blocks := edgeBlocks% "full/vectors/0001000001-E-0005.bin"
noncomputable def ep0001000001 : Blocks := (Blocks.join (Blocks.join ep0001000001_0 (Blocks.join ep0001000001_1 ep0001000001_2)) (Blocks.join ep0001000001_3 (Blocks.join ep0001000001_4 ep0001000001_5)))
private theorem idp0001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100000.list =
    C ((2:ℤ)^743) * horner X vp0001000001.list + horner X ep0001000001.list := by
  exact edge_identity (B := (2:ℤ)^1164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001000001 : Branch 1 (-511761639/16000000 : ℚ) vp000100000 := by
  apply branch_checked idp0001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-511761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-519761639/8000000 : ℚ) by norm_num]
  exact coverp0001000001
theorem coverp000100000 : Covers (-511761639/16000000 : ℚ) vp000100000 := join_branches bp0001000000 bp0001000001
private noncomputable def vp00010000_0 : Blocks := edgeBlocks% "full/vectors/00010000-V-0000.bin"
private noncomputable def vp00010000_1 : Blocks := edgeBlocks% "full/vectors/00010000-V-0001.bin"
private noncomputable def vp00010000_2 : Blocks := edgeBlocks% "full/vectors/00010000-V-0002.bin"
private noncomputable def vp00010000_3 : Blocks := edgeBlocks% "full/vectors/00010000-V-0003.bin"
private noncomputable def vp00010000_4 : Blocks := edgeBlocks% "full/vectors/00010000-V-0004.bin"
private noncomputable def vp00010000_5 : Blocks := edgeBlocks% "full/vectors/00010000-V-0005.bin"
private noncomputable def vp00010000_6 : Blocks := edgeBlocks% "full/vectors/00010000-V-0006.bin"
private noncomputable def vp00010000_7 : Blocks := edgeBlocks% "full/vectors/00010000-V-0007.bin"
private noncomputable def vp00010000_8 : Blocks := edgeBlocks% "full/vectors/00010000-V-0008.bin"
private noncomputable def vp00010000_9 : Blocks := edgeBlocks% "full/vectors/00010000-V-0009.bin"
private noncomputable def vp00010000_10 : Blocks := edgeBlocks% "full/vectors/00010000-V-0010.bin"
noncomputable def vp00010000 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00010000_0 vp00010000_1) (Blocks.join vp00010000_2 (Blocks.join vp00010000_3 vp00010000_4))) (Blocks.join (Blocks.join vp00010000_5 (Blocks.join vp00010000_6 vp00010000_7)) (Blocks.join vp00010000_8 (Blocks.join vp00010000_9 vp00010000_10))))
private theorem bp000100000 : Branch 0 (-511761639/32000000 : ℚ) vp00010000 := by
  apply branch_left_normalized (c:=vp000100000) (k:=0) (m:=704) (by decide +kernel)
  rw [show 2*(-511761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-511761639/16000000 : ℚ) by norm_num]
  exact coverp000100000
private noncomputable def ep000100001_0 : Blocks := edgeBlocks% "full/vectors/000100001-E-0000.bin"
private noncomputable def ep000100001_1 : Blocks := edgeBlocks% "full/vectors/000100001-E-0001.bin"
private noncomputable def ep000100001_2 : Blocks := edgeBlocks% "full/vectors/000100001-E-0002.bin"
private noncomputable def ep000100001_3 : Blocks := edgeBlocks% "full/vectors/000100001-E-0003.bin"
private noncomputable def ep000100001_4 : Blocks := edgeBlocks% "full/vectors/000100001-E-0004.bin"
private noncomputable def ep000100001_5 : Blocks := edgeBlocks% "full/vectors/000100001-E-0005.bin"
private noncomputable def ep000100001_6 : Blocks := edgeBlocks% "full/vectors/000100001-E-0006.bin"
private noncomputable def ep000100001_7 : Blocks := edgeBlocks% "full/vectors/000100001-E-0007.bin"
private noncomputable def ep000100001_8 : Blocks := edgeBlocks% "full/vectors/000100001-E-0008.bin"
private noncomputable def ep000100001_9 : Blocks := edgeBlocks% "full/vectors/000100001-E-0009.bin"
private noncomputable def ep000100001_10 : Blocks := edgeBlocks% "full/vectors/000100001-E-0010.bin"
noncomputable def ep000100001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000100001_0 ep000100001_1) (Blocks.join ep000100001_2 (Blocks.join ep000100001_3 ep000100001_4))) (Blocks.join (Blocks.join ep000100001_5 (Blocks.join ep000100001_6 ep000100001_7)) (Blocks.join ep000100001_8 (Blocks.join ep000100001_9 ep000100001_10))))
private theorem idp000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010000.list =
    C ((2:ℤ)^1461) * horner X vp000100001.list + horner X ep000100001.list := by
  exact edge_identity (B := (2:ℤ)^2203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100001 : Branch 1 (-511761639/32000000 : ℚ) vp00010000 := by
  apply branch_checked idp000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-511761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-527761639/16000000 : ℚ) by norm_num]
  exact coverp000100001
theorem coverp00010000 : Covers (-511761639/32000000 : ℚ) vp00010000 := join_branches bp000100000 bp000100001
private noncomputable def vp0001000_0 : Blocks := edgeBlocks% "full/vectors/0001000-V-0000.bin"
private noncomputable def vp0001000_1 : Blocks := edgeBlocks% "full/vectors/0001000-V-0001.bin"
private noncomputable def vp0001000_2 : Blocks := edgeBlocks% "full/vectors/0001000-V-0002.bin"
private noncomputable def vp0001000_3 : Blocks := edgeBlocks% "full/vectors/0001000-V-0003.bin"
private noncomputable def vp0001000_4 : Blocks := edgeBlocks% "full/vectors/0001000-V-0004.bin"
private noncomputable def vp0001000_5 : Blocks := edgeBlocks% "full/vectors/0001000-V-0005.bin"
private noncomputable def vp0001000_6 : Blocks := edgeBlocks% "full/vectors/0001000-V-0006.bin"
private noncomputable def vp0001000_7 : Blocks := edgeBlocks% "full/vectors/0001000-V-0007.bin"
private noncomputable def vp0001000_8 : Blocks := edgeBlocks% "full/vectors/0001000-V-0008.bin"
private noncomputable def vp0001000_9 : Blocks := edgeBlocks% "full/vectors/0001000-V-0009.bin"
private noncomputable def vp0001000_10 : Blocks := edgeBlocks% "full/vectors/0001000-V-0010.bin"
private noncomputable def vp0001000_11 : Blocks := edgeBlocks% "full/vectors/0001000-V-0011.bin"
private noncomputable def vp0001000_12 : Blocks := edgeBlocks% "full/vectors/0001000-V-0012.bin"
private noncomputable def vp0001000_13 : Blocks := edgeBlocks% "full/vectors/0001000-V-0013.bin"
private noncomputable def vp0001000_14 : Blocks := edgeBlocks% "full/vectors/0001000-V-0014.bin"
private noncomputable def vp0001000_15 : Blocks := edgeBlocks% "full/vectors/0001000-V-0015.bin"
private noncomputable def vp0001000_16 : Blocks := edgeBlocks% "full/vectors/0001000-V-0016.bin"
private noncomputable def vp0001000_17 : Blocks := edgeBlocks% "full/vectors/0001000-V-0017.bin"
private noncomputable def vp0001000_18 : Blocks := edgeBlocks% "full/vectors/0001000-V-0018.bin"
private noncomputable def vp0001000_19 : Blocks := edgeBlocks% "full/vectors/0001000-V-0019.bin"
private noncomputable def vp0001000_20 : Blocks := edgeBlocks% "full/vectors/0001000-V-0020.bin"
noncomputable def vp0001000 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0001000_0 vp0001000_1) (Blocks.join vp0001000_2 (Blocks.join vp0001000_3 vp0001000_4))) (Blocks.join (Blocks.join vp0001000_5 vp0001000_6) (Blocks.join vp0001000_7 (Blocks.join vp0001000_8 vp0001000_9)))) (Blocks.join (Blocks.join (Blocks.join vp0001000_10 vp0001000_11) (Blocks.join vp0001000_12 (Blocks.join vp0001000_13 vp0001000_14))) (Blocks.join (Blocks.join vp0001000_15 (Blocks.join vp0001000_16 vp0001000_17)) (Blocks.join vp0001000_18 (Blocks.join vp0001000_19 vp0001000_20)))))
private theorem bp00010000 : Branch 0 (-511761639/64000000 : ℚ) vp0001000 := by
  apply branch_left_normalized (c:=vp00010000) (k:=0) (m:=1378) (by decide +kernel)
  rw [show 2*(-511761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-511761639/32000000 : ℚ) by norm_num]
  exact coverp00010000
private noncomputable def ep00010001_0 : Blocks := edgeBlocks% "full/vectors/00010001-E-0000.bin"
private noncomputable def ep00010001_1 : Blocks := edgeBlocks% "full/vectors/00010001-E-0001.bin"
private noncomputable def ep00010001_2 : Blocks := edgeBlocks% "full/vectors/00010001-E-0002.bin"
private noncomputable def ep00010001_3 : Blocks := edgeBlocks% "full/vectors/00010001-E-0003.bin"
private noncomputable def ep00010001_4 : Blocks := edgeBlocks% "full/vectors/00010001-E-0004.bin"
private noncomputable def ep00010001_5 : Blocks := edgeBlocks% "full/vectors/00010001-E-0005.bin"
private noncomputable def ep00010001_6 : Blocks := edgeBlocks% "full/vectors/00010001-E-0006.bin"
private noncomputable def ep00010001_7 : Blocks := edgeBlocks% "full/vectors/00010001-E-0007.bin"
private noncomputable def ep00010001_8 : Blocks := edgeBlocks% "full/vectors/00010001-E-0008.bin"
private noncomputable def ep00010001_9 : Blocks := edgeBlocks% "full/vectors/00010001-E-0009.bin"
private noncomputable def ep00010001_10 : Blocks := edgeBlocks% "full/vectors/00010001-E-0010.bin"
private noncomputable def ep00010001_11 : Blocks := edgeBlocks% "full/vectors/00010001-E-0011.bin"
private noncomputable def ep00010001_12 : Blocks := edgeBlocks% "full/vectors/00010001-E-0012.bin"
private noncomputable def ep00010001_13 : Blocks := edgeBlocks% "full/vectors/00010001-E-0013.bin"
private noncomputable def ep00010001_14 : Blocks := edgeBlocks% "full/vectors/00010001-E-0014.bin"
private noncomputable def ep00010001_15 : Blocks := edgeBlocks% "full/vectors/00010001-E-0015.bin"
private noncomputable def ep00010001_16 : Blocks := edgeBlocks% "full/vectors/00010001-E-0016.bin"
private noncomputable def ep00010001_17 : Blocks := edgeBlocks% "full/vectors/00010001-E-0017.bin"
private noncomputable def ep00010001_18 : Blocks := edgeBlocks% "full/vectors/00010001-E-0018.bin"
private noncomputable def ep00010001_19 : Blocks := edgeBlocks% "full/vectors/00010001-E-0019.bin"
private noncomputable def ep00010001_20 : Blocks := edgeBlocks% "full/vectors/00010001-E-0020.bin"
noncomputable def ep00010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00010001_0 ep00010001_1) (Blocks.join ep00010001_2 (Blocks.join ep00010001_3 ep00010001_4))) (Blocks.join (Blocks.join ep00010001_5 ep00010001_6) (Blocks.join ep00010001_7 (Blocks.join ep00010001_8 ep00010001_9)))) (Blocks.join (Blocks.join (Blocks.join ep00010001_10 ep00010001_11) (Blocks.join ep00010001_12 (Blocks.join ep00010001_13 ep00010001_14))) (Blocks.join (Blocks.join ep00010001_15 (Blocks.join ep00010001_16 ep00010001_17)) (Blocks.join ep00010001_18 (Blocks.join ep00010001_19 ep00010001_20)))))
private theorem idp00010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001000.list =
    C ((2:ℤ)^2856) * horner X vp00010001.list + horner X ep00010001.list := by
  exact edge_identity (B := (2:ℤ)^4228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010001 : Branch 1 (-511761639/64000000 : ℚ) vp0001000 := by
  apply branch_checked idp00010001 (by positivity) (by decide +kernel)
  rw [show 2*(-511761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-543761639/32000000 : ℚ) by norm_num]
  exact coverp00010001
theorem coverp0001000 : Covers (-511761639/64000000 : ℚ) vp0001000 := join_branches bp00010000 bp00010001
end NextProof.EdgeFull

