import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0001100111111_0 : Blocks := edgeBlocks% "full/vectors/0001100111111-V-0000.bin"
noncomputable def vp0001100111111 : Blocks := vp0001100111111_0
theorem coverp0001100111111 : Covers (-830761639/1000000 : ℚ) vp0001100111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100111110_0 : Blocks := edgeBlocks% "full/vectors/0001100111110-V-0000.bin"
noncomputable def vp0001100111110 : Blocks := vp0001100111110_0
theorem coverp0001100111110 : Covers (-829761639/1000000 : ℚ) vp0001100111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000110011111_0 : Blocks := edgeBlocks% "full/vectors/000110011111-V-0000.bin"
noncomputable def vp000110011111 : Blocks := vp000110011111_0
private theorem bp0001100111110 : Branch 0 (-829761639/2000000 : ℚ) vp000110011111 := by
  apply branch_left_normalized (c:=vp0001100111110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-829761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-829761639/1000000 : ℚ) by norm_num]
  exact coverp0001100111110
private noncomputable def ep0001100111111_0 : Blocks := edgeBlocks% "full/vectors/0001100111111-E-0000.bin"
noncomputable def ep0001100111111 : Blocks := ep0001100111111_0
private theorem idp0001100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110011111.list =
    C ((2:ℤ)^91) * horner X vp0001100111111.list + horner X ep0001100111111.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100111111 : Branch 1 (-829761639/2000000 : ℚ) vp000110011111 := by
  apply branch_checked idp0001100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-829761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-830761639/1000000 : ℚ) by norm_num]
  exact coverp0001100111111
theorem coverp000110011111 : Covers (-829761639/2000000 : ℚ) vp000110011111 := join_branches bp0001100111110 bp0001100111111
private noncomputable def vp0001100111101_0 : Blocks := edgeBlocks% "full/vectors/0001100111101-V-0000.bin"
noncomputable def vp0001100111101 : Blocks := vp0001100111101_0
theorem coverp0001100111101 : Covers (-828761639/1000000 : ℚ) vp0001100111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100111100_0 : Blocks := edgeBlocks% "full/vectors/0001100111100-V-0000.bin"
noncomputable def vp0001100111100 : Blocks := vp0001100111100_0
theorem coverp0001100111100 : Covers (-827761639/1000000 : ℚ) vp0001100111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000110011110_0 : Blocks := edgeBlocks% "full/vectors/000110011110-V-0000.bin"
noncomputable def vp000110011110 : Blocks := vp000110011110_0
private theorem bp0001100111100 : Branch 0 (-827761639/2000000 : ℚ) vp000110011110 := by
  apply branch_left_normalized (c:=vp0001100111100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-827761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-827761639/1000000 : ℚ) by norm_num]
  exact coverp0001100111100
private noncomputable def ep0001100111101_0 : Blocks := edgeBlocks% "full/vectors/0001100111101-E-0000.bin"
noncomputable def ep0001100111101 : Blocks := ep0001100111101_0
private theorem idp0001100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110011110.list =
    C ((2:ℤ)^92) * horner X vp0001100111101.list + horner X ep0001100111101.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100111101 : Branch 1 (-827761639/2000000 : ℚ) vp000110011110 := by
  apply branch_checked idp0001100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-827761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-828761639/1000000 : ℚ) by norm_num]
  exact coverp0001100111101
theorem coverp000110011110 : Covers (-827761639/2000000 : ℚ) vp000110011110 := join_branches bp0001100111100 bp0001100111101
private noncomputable def vp00011001111_0 : Blocks := edgeBlocks% "full/vectors/00011001111-V-0000.bin"
private noncomputable def vp00011001111_1 : Blocks := edgeBlocks% "full/vectors/00011001111-V-0001.bin"
noncomputable def vp00011001111 : Blocks := (Blocks.join vp00011001111_0 vp00011001111_1)
private theorem bp000110011110 : Branch 0 (-827761639/4000000 : ℚ) vp00011001111 := by
  apply branch_left_normalized (c:=vp000110011110) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-827761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-827761639/2000000 : ℚ) by norm_num]
  exact coverp000110011110
private noncomputable def ep000110011111_0 : Blocks := edgeBlocks% "full/vectors/000110011111-E-0000.bin"
private noncomputable def ep000110011111_1 : Blocks := edgeBlocks% "full/vectors/000110011111-E-0001.bin"
noncomputable def ep000110011111 : Blocks := (Blocks.join ep000110011111_0 ep000110011111_1)
private theorem idp000110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011001111.list =
    C ((2:ℤ)^167) * horner X vp000110011111.list + horner X ep000110011111.list := by
  exact edge_identity (B := (2:ℤ)^319) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110011111 : Branch 1 (-827761639/4000000 : ℚ) vp00011001111 := by
  apply branch_checked idp000110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-827761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-829761639/2000000 : ℚ) by norm_num]
  exact coverp000110011111
theorem coverp00011001111 : Covers (-827761639/4000000 : ℚ) vp00011001111 := join_branches bp000110011110 bp000110011111
private noncomputable def vp0001100111011_0 : Blocks := edgeBlocks% "full/vectors/0001100111011-V-0000.bin"
noncomputable def vp0001100111011 : Blocks := vp0001100111011_0
theorem coverp0001100111011 : Covers (-826761639/1000000 : ℚ) vp0001100111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100111010_0 : Blocks := edgeBlocks% "full/vectors/0001100111010-V-0000.bin"
noncomputable def vp0001100111010 : Blocks := vp0001100111010_0
theorem coverp0001100111010 : Covers (-825761639/1000000 : ℚ) vp0001100111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000110011101_0 : Blocks := edgeBlocks% "full/vectors/000110011101-V-0000.bin"
noncomputable def vp000110011101 : Blocks := vp000110011101_0
private theorem bp0001100111010 : Branch 0 (-825761639/2000000 : ℚ) vp000110011101 := by
  apply branch_left_normalized (c:=vp0001100111010) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-825761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-825761639/1000000 : ℚ) by norm_num]
  exact coverp0001100111010
private noncomputable def ep0001100111011_0 : Blocks := edgeBlocks% "full/vectors/0001100111011-E-0000.bin"
noncomputable def ep0001100111011 : Blocks := ep0001100111011_0
private theorem idp0001100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110011101.list =
    C ((2:ℤ)^94) * horner X vp0001100111011.list + horner X ep0001100111011.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100111011 : Branch 1 (-825761639/2000000 : ℚ) vp000110011101 := by
  apply branch_checked idp0001100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-825761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-826761639/1000000 : ℚ) by norm_num]
  exact coverp0001100111011
theorem coverp000110011101 : Covers (-825761639/2000000 : ℚ) vp000110011101 := join_branches bp0001100111010 bp0001100111011
private noncomputable def vp0001100111001_0 : Blocks := edgeBlocks% "full/vectors/0001100111001-V-0000.bin"
noncomputable def vp0001100111001 : Blocks := vp0001100111001_0
theorem coverp0001100111001 : Covers (-824761639/1000000 : ℚ) vp0001100111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100111000_0 : Blocks := edgeBlocks% "full/vectors/0001100111000-V-0000.bin"
noncomputable def vp0001100111000 : Blocks := vp0001100111000_0
theorem coverp0001100111000 : Covers (-823761639/1000000 : ℚ) vp0001100111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000110011100_0 : Blocks := edgeBlocks% "full/vectors/000110011100-V-0000.bin"
noncomputable def vp000110011100 : Blocks := vp000110011100_0
private theorem bp0001100111000 : Branch 0 (-823761639/2000000 : ℚ) vp000110011100 := by
  apply branch_left_normalized (c:=vp0001100111000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-823761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-823761639/1000000 : ℚ) by norm_num]
  exact coverp0001100111000
private noncomputable def ep0001100111001_0 : Blocks := edgeBlocks% "full/vectors/0001100111001-E-0000.bin"
noncomputable def ep0001100111001 : Blocks := ep0001100111001_0
private theorem idp0001100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110011100.list =
    C ((2:ℤ)^97) * horner X vp0001100111001.list + horner X ep0001100111001.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100111001 : Branch 1 (-823761639/2000000 : ℚ) vp000110011100 := by
  apply branch_checked idp0001100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-823761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-824761639/1000000 : ℚ) by norm_num]
  exact coverp0001100111001
theorem coverp000110011100 : Covers (-823761639/2000000 : ℚ) vp000110011100 := join_branches bp0001100111000 bp0001100111001
private noncomputable def vp00011001110_0 : Blocks := edgeBlocks% "full/vectors/00011001110-V-0000.bin"
private noncomputable def vp00011001110_1 : Blocks := edgeBlocks% "full/vectors/00011001110-V-0001.bin"
noncomputable def vp00011001110 : Blocks := (Blocks.join vp00011001110_0 vp00011001110_1)
private theorem bp000110011100 : Branch 0 (-823761639/4000000 : ℚ) vp00011001110 := by
  apply branch_left_normalized (c:=vp000110011100) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-823761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-823761639/2000000 : ℚ) by norm_num]
  exact coverp000110011100
private noncomputable def ep000110011101_0 : Blocks := edgeBlocks% "full/vectors/000110011101-E-0000.bin"
private noncomputable def ep000110011101_1 : Blocks := edgeBlocks% "full/vectors/000110011101-E-0001.bin"
noncomputable def ep000110011101 : Blocks := (Blocks.join ep000110011101_0 ep000110011101_1)
private theorem idp000110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011001110.list =
    C ((2:ℤ)^173) * horner X vp000110011101.list + horner X ep000110011101.list := by
  exact edge_identity (B := (2:ℤ)^329) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110011101 : Branch 1 (-823761639/4000000 : ℚ) vp00011001110 := by
  apply branch_checked idp000110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-823761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-825761639/2000000 : ℚ) by norm_num]
  exact coverp000110011101
theorem coverp00011001110 : Covers (-823761639/4000000 : ℚ) vp00011001110 := join_branches bp000110011100 bp000110011101
private noncomputable def vp0001100111_0 : Blocks := edgeBlocks% "full/vectors/0001100111-V-0000.bin"
private noncomputable def vp0001100111_1 : Blocks := edgeBlocks% "full/vectors/0001100111-V-0001.bin"
private noncomputable def vp0001100111_2 : Blocks := edgeBlocks% "full/vectors/0001100111-V-0002.bin"
noncomputable def vp0001100111 : Blocks := (Blocks.join vp0001100111_0 (Blocks.join vp0001100111_1 vp0001100111_2))
private theorem bp00011001110 : Branch 0 (-823761639/8000000 : ℚ) vp0001100111 := by
  apply branch_left_normalized (c:=vp00011001110) (k:=0) (m:=157) (by decide +kernel)
  rw [show 2*(-823761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-823761639/4000000 : ℚ) by norm_num]
  exact coverp00011001110
private noncomputable def ep00011001111_0 : Blocks := edgeBlocks% "full/vectors/00011001111-E-0000.bin"
private noncomputable def ep00011001111_1 : Blocks := edgeBlocks% "full/vectors/00011001111-E-0001.bin"
private noncomputable def ep00011001111_2 : Blocks := edgeBlocks% "full/vectors/00011001111-E-0002.bin"
noncomputable def ep00011001111 : Blocks := (Blocks.join ep00011001111_0 (Blocks.join ep00011001111_1 ep00011001111_2))
private theorem idp00011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100111.list =
    C ((2:ℤ)^323) * horner X vp00011001111.list + horner X ep00011001111.list := by
  exact edge_identity (B := (2:ℤ)^538) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001111 : Branch 1 (-823761639/8000000 : ℚ) vp0001100111 := by
  apply branch_checked idp00011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-823761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-827761639/4000000 : ℚ) by norm_num]
  exact coverp00011001111
theorem coverp0001100111 : Covers (-823761639/8000000 : ℚ) vp0001100111 := join_branches bp00011001110 bp00011001111
private noncomputable def vp0001100110111_0 : Blocks := edgeBlocks% "full/vectors/0001100110111-V-0000.bin"
noncomputable def vp0001100110111 : Blocks := vp0001100110111_0
theorem coverp0001100110111 : Covers (-822761639/1000000 : ℚ) vp0001100110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001101101_0 : Blocks := edgeBlocks% "full/vectors/00011001101101-V-0000.bin"
noncomputable def vp00011001101101 : Blocks := vp00011001101101_0
theorem coverp00011001101101 : Covers (-822261639/500000 : ℚ) vp00011001101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001101100_0 : Blocks := edgeBlocks% "full/vectors/00011001101100-V-0000.bin"
noncomputable def vp00011001101100 : Blocks := vp00011001101100_0
theorem coverp00011001101100 : Covers (-821761639/500000 : ℚ) vp00011001101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100110110_0 : Blocks := edgeBlocks% "full/vectors/0001100110110-V-0000.bin"
noncomputable def vp0001100110110 : Blocks := vp0001100110110_0
private theorem bp00011001101100 : Branch 0 (-821761639/1000000 : ℚ) vp0001100110110 := by
  apply branch_left_normalized (c:=vp00011001101100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-821761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-821761639/500000 : ℚ) by norm_num]
  exact coverp00011001101100
private noncomputable def ep00011001101101_0 : Blocks := edgeBlocks% "full/vectors/00011001101101-E-0000.bin"
noncomputable def ep00011001101101 : Blocks := ep00011001101101_0
private theorem idp00011001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100110110.list =
    C ((2:ℤ)^56) * horner X vp00011001101101.list + horner X ep00011001101101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001101101 : Branch 1 (-821761639/1000000 : ℚ) vp0001100110110 := by
  apply branch_checked idp00011001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-821761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-822261639/500000 : ℚ) by norm_num]
  exact coverp00011001101101
theorem coverp0001100110110 : Covers (-821761639/1000000 : ℚ) vp0001100110110 := join_branches bp00011001101100 bp00011001101101
private noncomputable def vp000110011011_0 : Blocks := edgeBlocks% "full/vectors/000110011011-V-0000.bin"
noncomputable def vp000110011011 : Blocks := vp000110011011_0
private theorem bp0001100110110 : Branch 0 (-821761639/2000000 : ℚ) vp000110011011 := by
  apply branch_left_normalized (c:=vp0001100110110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-821761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-821761639/1000000 : ℚ) by norm_num]
  exact coverp0001100110110
private noncomputable def ep0001100110111_0 : Blocks := edgeBlocks% "full/vectors/0001100110111-E-0000.bin"
noncomputable def ep0001100110111 : Blocks := ep0001100110111_0
private theorem idp0001100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110011011.list =
    C ((2:ℤ)^94) * horner X vp0001100110111.list + horner X ep0001100110111.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100110111 : Branch 1 (-821761639/2000000 : ℚ) vp000110011011 := by
  apply branch_checked idp0001100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-821761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-822761639/1000000 : ℚ) by norm_num]
  exact coverp0001100110111
theorem coverp000110011011 : Covers (-821761639/2000000 : ℚ) vp000110011011 := join_branches bp0001100110110 bp0001100110111
private noncomputable def vp0001100110101_0 : Blocks := edgeBlocks% "full/vectors/0001100110101-V-0000.bin"
noncomputable def vp0001100110101 : Blocks := vp0001100110101_0
theorem coverp0001100110101 : Covers (-820761639/1000000 : ℚ) vp0001100110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100110100_0 : Blocks := edgeBlocks% "full/vectors/0001100110100-V-0000.bin"
noncomputable def vp0001100110100 : Blocks := vp0001100110100_0
theorem coverp0001100110100 : Covers (-819761639/1000000 : ℚ) vp0001100110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000110011010_0 : Blocks := edgeBlocks% "full/vectors/000110011010-V-0000.bin"
noncomputable def vp000110011010 : Blocks := vp000110011010_0
private theorem bp0001100110100 : Branch 0 (-819761639/2000000 : ℚ) vp000110011010 := by
  apply branch_left_normalized (c:=vp0001100110100) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-819761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-819761639/1000000 : ℚ) by norm_num]
  exact coverp0001100110100
private noncomputable def ep0001100110101_0 : Blocks := edgeBlocks% "full/vectors/0001100110101-E-0000.bin"
noncomputable def ep0001100110101 : Blocks := ep0001100110101_0
private theorem idp0001100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110011010.list =
    C ((2:ℤ)^94) * horner X vp0001100110101.list + horner X ep0001100110101.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100110101 : Branch 1 (-819761639/2000000 : ℚ) vp000110011010 := by
  apply branch_checked idp0001100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-819761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-820761639/1000000 : ℚ) by norm_num]
  exact coverp0001100110101
theorem coverp000110011010 : Covers (-819761639/2000000 : ℚ) vp000110011010 := join_branches bp0001100110100 bp0001100110101
private noncomputable def vp00011001101_0 : Blocks := edgeBlocks% "full/vectors/00011001101-V-0000.bin"
private noncomputable def vp00011001101_1 : Blocks := edgeBlocks% "full/vectors/00011001101-V-0001.bin"
noncomputable def vp00011001101 : Blocks := (Blocks.join vp00011001101_0 vp00011001101_1)
private theorem bp000110011010 : Branch 0 (-819761639/4000000 : ℚ) vp00011001101 := by
  apply branch_left_normalized (c:=vp000110011010) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-819761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-819761639/2000000 : ℚ) by norm_num]
  exact coverp000110011010
private noncomputable def ep000110011011_0 : Blocks := edgeBlocks% "full/vectors/000110011011-E-0000.bin"
private noncomputable def ep000110011011_1 : Blocks := edgeBlocks% "full/vectors/000110011011-E-0001.bin"
noncomputable def ep000110011011 : Blocks := (Blocks.join ep000110011011_0 ep000110011011_1)
private theorem idp000110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011001101.list =
    C ((2:ℤ)^169) * horner X vp000110011011.list + horner X ep000110011011.list := by
  exact edge_identity (B := (2:ℤ)^331) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110011011 : Branch 1 (-819761639/4000000 : ℚ) vp00011001101 := by
  apply branch_checked idp000110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-819761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-821761639/2000000 : ℚ) by norm_num]
  exact coverp000110011011
theorem coverp00011001101 : Covers (-819761639/4000000 : ℚ) vp00011001101 := join_branches bp000110011010 bp000110011011
private noncomputable def vp0001100110011_0 : Blocks := edgeBlocks% "full/vectors/0001100110011-V-0000.bin"
noncomputable def vp0001100110011 : Blocks := vp0001100110011_0
theorem coverp0001100110011 : Covers (-818761639/1000000 : ℚ) vp0001100110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100110010_0 : Blocks := edgeBlocks% "full/vectors/0001100110010-V-0000.bin"
noncomputable def vp0001100110010 : Blocks := vp0001100110010_0
theorem coverp0001100110010 : Covers (-817761639/1000000 : ℚ) vp0001100110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000110011001_0 : Blocks := edgeBlocks% "full/vectors/000110011001-V-0000.bin"
noncomputable def vp000110011001 : Blocks := vp000110011001_0
private theorem bp0001100110010 : Branch 0 (-817761639/2000000 : ℚ) vp000110011001 := by
  apply branch_left_normalized (c:=vp0001100110010) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-817761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-817761639/1000000 : ℚ) by norm_num]
  exact coverp0001100110010
private noncomputable def ep0001100110011_0 : Blocks := edgeBlocks% "full/vectors/0001100110011-E-0000.bin"
noncomputable def ep0001100110011 : Blocks := ep0001100110011_0
private theorem idp0001100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110011001.list =
    C ((2:ℤ)^96) * horner X vp0001100110011.list + horner X ep0001100110011.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100110011 : Branch 1 (-817761639/2000000 : ℚ) vp000110011001 := by
  apply branch_checked idp0001100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-817761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-818761639/1000000 : ℚ) by norm_num]
  exact coverp0001100110011
theorem coverp000110011001 : Covers (-817761639/2000000 : ℚ) vp000110011001 := join_branches bp0001100110010 bp0001100110011
private noncomputable def vp0001100110001_0 : Blocks := edgeBlocks% "full/vectors/0001100110001-V-0000.bin"
noncomputable def vp0001100110001 : Blocks := vp0001100110001_0
theorem coverp0001100110001 : Covers (-816761639/1000000 : ℚ) vp0001100110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001100001_0 : Blocks := edgeBlocks% "full/vectors/00011001100001-V-0000.bin"
noncomputable def vp00011001100001 : Blocks := vp00011001100001_0
theorem coverp00011001100001 : Covers (-816261639/500000 : ℚ) vp00011001100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001100000_0 : Blocks := edgeBlocks% "full/vectors/00011001100000-V-0000.bin"
noncomputable def vp00011001100000 : Blocks := vp00011001100000_0
theorem coverp00011001100000 : Covers (-815761639/500000 : ℚ) vp00011001100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100110000_0 : Blocks := edgeBlocks% "full/vectors/0001100110000-V-0000.bin"
noncomputable def vp0001100110000 : Blocks := vp0001100110000_0
private theorem bp00011001100000 : Branch 0 (-815761639/1000000 : ℚ) vp0001100110000 := by
  apply branch_left_normalized (c:=vp00011001100000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-815761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-815761639/500000 : ℚ) by norm_num]
  exact coverp00011001100000
private noncomputable def ep00011001100001_0 : Blocks := edgeBlocks% "full/vectors/00011001100001-E-0000.bin"
noncomputable def ep00011001100001 : Blocks := ep00011001100001_0
private theorem idp00011001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100110000.list =
    C ((2:ℤ)^58) * horner X vp00011001100001.list + horner X ep00011001100001.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001100001 : Branch 1 (-815761639/1000000 : ℚ) vp0001100110000 := by
  apply branch_checked idp00011001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-815761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-816261639/500000 : ℚ) by norm_num]
  exact coverp00011001100001
theorem coverp0001100110000 : Covers (-815761639/1000000 : ℚ) vp0001100110000 := join_branches bp00011001100000 bp00011001100001
private noncomputable def vp000110011000_0 : Blocks := edgeBlocks% "full/vectors/000110011000-V-0000.bin"
noncomputable def vp000110011000 : Blocks := vp000110011000_0
private theorem bp0001100110000 : Branch 0 (-815761639/2000000 : ℚ) vp000110011000 := by
  apply branch_left_normalized (c:=vp0001100110000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-815761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-815761639/1000000 : ℚ) by norm_num]
  exact coverp0001100110000
private noncomputable def ep0001100110001_0 : Blocks := edgeBlocks% "full/vectors/0001100110001-E-0000.bin"
noncomputable def ep0001100110001 : Blocks := ep0001100110001_0
private theorem idp0001100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110011000.list =
    C ((2:ℤ)^96) * horner X vp0001100110001.list + horner X ep0001100110001.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100110001 : Branch 1 (-815761639/2000000 : ℚ) vp000110011000 := by
  apply branch_checked idp0001100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-815761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-816761639/1000000 : ℚ) by norm_num]
  exact coverp0001100110001
theorem coverp000110011000 : Covers (-815761639/2000000 : ℚ) vp000110011000 := join_branches bp0001100110000 bp0001100110001
private noncomputable def vp00011001100_0 : Blocks := edgeBlocks% "full/vectors/00011001100-V-0000.bin"
private noncomputable def vp00011001100_1 : Blocks := edgeBlocks% "full/vectors/00011001100-V-0001.bin"
noncomputable def vp00011001100 : Blocks := (Blocks.join vp00011001100_0 vp00011001100_1)
private theorem bp000110011000 : Branch 0 (-815761639/4000000 : ℚ) vp00011001100 := by
  apply branch_left_normalized (c:=vp000110011000) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-815761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-815761639/2000000 : ℚ) by norm_num]
  exact coverp000110011000
private noncomputable def ep000110011001_0 : Blocks := edgeBlocks% "full/vectors/000110011001-E-0000.bin"
private noncomputable def ep000110011001_1 : Blocks := edgeBlocks% "full/vectors/000110011001-E-0001.bin"
noncomputable def ep000110011001 : Blocks := (Blocks.join ep000110011001_0 ep000110011001_1)
private theorem idp000110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011001100.list =
    C ((2:ℤ)^173) * horner X vp000110011001.list + horner X ep000110011001.list := by
  exact edge_identity (B := (2:ℤ)^335) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110011001 : Branch 1 (-815761639/4000000 : ℚ) vp00011001100 := by
  apply branch_checked idp000110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-815761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-817761639/2000000 : ℚ) by norm_num]
  exact coverp000110011001
theorem coverp00011001100 : Covers (-815761639/4000000 : ℚ) vp00011001100 := join_branches bp000110011000 bp000110011001
private noncomputable def vp0001100110_0 : Blocks := edgeBlocks% "full/vectors/0001100110-V-0000.bin"
private noncomputable def vp0001100110_1 : Blocks := edgeBlocks% "full/vectors/0001100110-V-0001.bin"
private noncomputable def vp0001100110_2 : Blocks := edgeBlocks% "full/vectors/0001100110-V-0002.bin"
noncomputable def vp0001100110 : Blocks := (Blocks.join vp0001100110_0 (Blocks.join vp0001100110_1 vp0001100110_2))
private theorem bp00011001100 : Branch 0 (-815761639/8000000 : ℚ) vp0001100110 := by
  apply branch_left_normalized (c:=vp00011001100) (k:=0) (m:=159) (by decide +kernel)
  rw [show 2*(-815761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-815761639/4000000 : ℚ) by norm_num]
  exact coverp00011001100
private noncomputable def ep00011001101_0 : Blocks := edgeBlocks% "full/vectors/00011001101-E-0000.bin"
private noncomputable def ep00011001101_1 : Blocks := edgeBlocks% "full/vectors/00011001101-E-0001.bin"
private noncomputable def ep00011001101_2 : Blocks := edgeBlocks% "full/vectors/00011001101-E-0002.bin"
noncomputable def ep00011001101 : Blocks := (Blocks.join ep00011001101_0 (Blocks.join ep00011001101_1 ep00011001101_2))
private theorem idp00011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100110.list =
    C ((2:ℤ)^324) * horner X vp00011001101.list + horner X ep00011001101.list := by
  exact edge_identity (B := (2:ℤ)^546) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001101 : Branch 1 (-815761639/8000000 : ℚ) vp0001100110 := by
  apply branch_checked idp00011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-815761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-819761639/4000000 : ℚ) by norm_num]
  exact coverp00011001101
theorem coverp0001100110 : Covers (-815761639/8000000 : ℚ) vp0001100110 := join_branches bp00011001100 bp00011001101
private noncomputable def vp000110011_0 : Blocks := edgeBlocks% "full/vectors/000110011-V-0000.bin"
private noncomputable def vp000110011_1 : Blocks := edgeBlocks% "full/vectors/000110011-V-0001.bin"
private noncomputable def vp000110011_2 : Blocks := edgeBlocks% "full/vectors/000110011-V-0002.bin"
private noncomputable def vp000110011_3 : Blocks := edgeBlocks% "full/vectors/000110011-V-0003.bin"
private noncomputable def vp000110011_4 : Blocks := edgeBlocks% "full/vectors/000110011-V-0004.bin"
noncomputable def vp000110011 : Blocks := (Blocks.join (Blocks.join vp000110011_0 vp000110011_1) (Blocks.join vp000110011_2 (Blocks.join vp000110011_3 vp000110011_4)))
private theorem bp0001100110 : Branch 0 (-815761639/16000000 : ℚ) vp000110011 := by
  apply branch_left_normalized (c:=vp0001100110) (k:=0) (m:=297) (by decide +kernel)
  rw [show 2*(-815761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-815761639/8000000 : ℚ) by norm_num]
  exact coverp0001100110
private noncomputable def ep0001100111_0 : Blocks := edgeBlocks% "full/vectors/0001100111-E-0000.bin"
private noncomputable def ep0001100111_1 : Blocks := edgeBlocks% "full/vectors/0001100111-E-0001.bin"
private noncomputable def ep0001100111_2 : Blocks := edgeBlocks% "full/vectors/0001100111-E-0002.bin"
private noncomputable def ep0001100111_3 : Blocks := edgeBlocks% "full/vectors/0001100111-E-0003.bin"
private noncomputable def ep0001100111_4 : Blocks := edgeBlocks% "full/vectors/0001100111-E-0004.bin"
noncomputable def ep0001100111 : Blocks := (Blocks.join (Blocks.join ep0001100111_0 ep0001100111_1) (Blocks.join ep0001100111_2 (Blocks.join ep0001100111_3 ep0001100111_4)))
private theorem idp0001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110011.list =
    C ((2:ℤ)^619) * horner X vp0001100111.list + horner X ep0001100111.list := by
  exact edge_identity (B := (2:ℤ)^963) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100111 : Branch 1 (-815761639/16000000 : ℚ) vp000110011 := by
  apply branch_checked idp0001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-815761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-823761639/8000000 : ℚ) by norm_num]
  exact coverp0001100111
theorem coverp000110011 : Covers (-815761639/16000000 : ℚ) vp000110011 := join_branches bp0001100110 bp0001100111
private noncomputable def vp00011001011111_0 : Blocks := edgeBlocks% "full/vectors/00011001011111-V-0000.bin"
noncomputable def vp00011001011111 : Blocks := vp00011001011111_0
theorem coverp00011001011111 : Covers (-815261639/500000 : ℚ) vp00011001011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001011110_0 : Blocks := edgeBlocks% "full/vectors/00011001011110-V-0000.bin"
noncomputable def vp00011001011110 : Blocks := vp00011001011110_0
theorem coverp00011001011110 : Covers (-814761639/500000 : ℚ) vp00011001011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100101111_0 : Blocks := edgeBlocks% "full/vectors/0001100101111-V-0000.bin"
noncomputable def vp0001100101111 : Blocks := vp0001100101111_0
private theorem bp00011001011110 : Branch 0 (-814761639/1000000 : ℚ) vp0001100101111 := by
  apply branch_left_normalized (c:=vp00011001011110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-814761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-814761639/500000 : ℚ) by norm_num]
  exact coverp00011001011110
private noncomputable def ep00011001011111_0 : Blocks := edgeBlocks% "full/vectors/00011001011111-E-0000.bin"
noncomputable def ep00011001011111 : Blocks := ep00011001011111_0
private theorem idp00011001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100101111.list =
    C ((2:ℤ)^58) * horner X vp00011001011111.list + horner X ep00011001011111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001011111 : Branch 1 (-814761639/1000000 : ℚ) vp0001100101111 := by
  apply branch_checked idp00011001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-814761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-815261639/500000 : ℚ) by norm_num]
  exact coverp00011001011111
theorem coverp0001100101111 : Covers (-814761639/1000000 : ℚ) vp0001100101111 := join_branches bp00011001011110 bp00011001011111
private noncomputable def vp00011001011101_0 : Blocks := edgeBlocks% "full/vectors/00011001011101-V-0000.bin"
noncomputable def vp00011001011101 : Blocks := vp00011001011101_0
theorem coverp00011001011101 : Covers (-814261639/500000 : ℚ) vp00011001011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001011100_0 : Blocks := edgeBlocks% "full/vectors/00011001011100-V-0000.bin"
noncomputable def vp00011001011100 : Blocks := vp00011001011100_0
theorem coverp00011001011100 : Covers (-813761639/500000 : ℚ) vp00011001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100101110_0 : Blocks := edgeBlocks% "full/vectors/0001100101110-V-0000.bin"
noncomputable def vp0001100101110 : Blocks := vp0001100101110_0
private theorem bp00011001011100 : Branch 0 (-813761639/1000000 : ℚ) vp0001100101110 := by
  apply branch_left_normalized (c:=vp00011001011100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-813761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-813761639/500000 : ℚ) by norm_num]
  exact coverp00011001011100
private noncomputable def ep00011001011101_0 : Blocks := edgeBlocks% "full/vectors/00011001011101-E-0000.bin"
noncomputable def ep00011001011101 : Blocks := ep00011001011101_0
private theorem idp00011001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100101110.list =
    C ((2:ℤ)^57) * horner X vp00011001011101.list + horner X ep00011001011101.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001011101 : Branch 1 (-813761639/1000000 : ℚ) vp0001100101110 := by
  apply branch_checked idp00011001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-813761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-814261639/500000 : ℚ) by norm_num]
  exact coverp00011001011101
theorem coverp0001100101110 : Covers (-813761639/1000000 : ℚ) vp0001100101110 := join_branches bp00011001011100 bp00011001011101
private noncomputable def vp000110010111_0 : Blocks := edgeBlocks% "full/vectors/000110010111-V-0000.bin"
noncomputable def vp000110010111 : Blocks := vp000110010111_0
private theorem bp0001100101110 : Branch 0 (-813761639/2000000 : ℚ) vp000110010111 := by
  apply branch_left_normalized (c:=vp0001100101110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-813761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-813761639/1000000 : ℚ) by norm_num]
  exact coverp0001100101110
private noncomputable def ep0001100101111_0 : Blocks := edgeBlocks% "full/vectors/0001100101111-E-0000.bin"
noncomputable def ep0001100101111 : Blocks := ep0001100101111_0
private theorem idp0001100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110010111.list =
    C ((2:ℤ)^96) * horner X vp0001100101111.list + horner X ep0001100101111.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100101111 : Branch 1 (-813761639/2000000 : ℚ) vp000110010111 := by
  apply branch_checked idp0001100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-813761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-814761639/1000000 : ℚ) by norm_num]
  exact coverp0001100101111
theorem coverp000110010111 : Covers (-813761639/2000000 : ℚ) vp000110010111 := join_branches bp0001100101110 bp0001100101111
private noncomputable def vp00011001011011_0 : Blocks := edgeBlocks% "full/vectors/00011001011011-V-0000.bin"
noncomputable def vp00011001011011 : Blocks := vp00011001011011_0
theorem coverp00011001011011 : Covers (-813261639/500000 : ℚ) vp00011001011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001011010_0 : Blocks := edgeBlocks% "full/vectors/00011001011010-V-0000.bin"
noncomputable def vp00011001011010 : Blocks := vp00011001011010_0
theorem coverp00011001011010 : Covers (-812761639/500000 : ℚ) vp00011001011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100101101_0 : Blocks := edgeBlocks% "full/vectors/0001100101101-V-0000.bin"
noncomputable def vp0001100101101 : Blocks := vp0001100101101_0
private theorem bp00011001011010 : Branch 0 (-812761639/1000000 : ℚ) vp0001100101101 := by
  apply branch_left_normalized (c:=vp00011001011010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-812761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-812761639/500000 : ℚ) by norm_num]
  exact coverp00011001011010
private noncomputable def ep00011001011011_0 : Blocks := edgeBlocks% "full/vectors/00011001011011-E-0000.bin"
noncomputable def ep00011001011011 : Blocks := ep00011001011011_0
private theorem idp00011001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100101101.list =
    C ((2:ℤ)^56) * horner X vp00011001011011.list + horner X ep00011001011011.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001011011 : Branch 1 (-812761639/1000000 : ℚ) vp0001100101101 := by
  apply branch_checked idp00011001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-812761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-813261639/500000 : ℚ) by norm_num]
  exact coverp00011001011011
theorem coverp0001100101101 : Covers (-812761639/1000000 : ℚ) vp0001100101101 := join_branches bp00011001011010 bp00011001011011
private noncomputable def vp00011001011001_0 : Blocks := edgeBlocks% "full/vectors/00011001011001-V-0000.bin"
noncomputable def vp00011001011001 : Blocks := vp00011001011001_0
theorem coverp00011001011001 : Covers (-812261639/500000 : ℚ) vp00011001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001011000_0 : Blocks := edgeBlocks% "full/vectors/00011001011000-V-0000.bin"
noncomputable def vp00011001011000 : Blocks := vp00011001011000_0
theorem coverp00011001011000 : Covers (-811761639/500000 : ℚ) vp00011001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100101100_0 : Blocks := edgeBlocks% "full/vectors/0001100101100-V-0000.bin"
noncomputable def vp0001100101100 : Blocks := vp0001100101100_0
private theorem bp00011001011000 : Branch 0 (-811761639/1000000 : ℚ) vp0001100101100 := by
  apply branch_left_normalized (c:=vp00011001011000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-811761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-811761639/500000 : ℚ) by norm_num]
  exact coverp00011001011000
private noncomputable def ep00011001011001_0 : Blocks := edgeBlocks% "full/vectors/00011001011001-E-0000.bin"
noncomputable def ep00011001011001 : Blocks := ep00011001011001_0
private theorem idp00011001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100101100.list =
    C ((2:ℤ)^58) * horner X vp00011001011001.list + horner X ep00011001011001.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001011001 : Branch 1 (-811761639/1000000 : ℚ) vp0001100101100 := by
  apply branch_checked idp00011001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-811761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-812261639/500000 : ℚ) by norm_num]
  exact coverp00011001011001
theorem coverp0001100101100 : Covers (-811761639/1000000 : ℚ) vp0001100101100 := join_branches bp00011001011000 bp00011001011001
private noncomputable def vp000110010110_0 : Blocks := edgeBlocks% "full/vectors/000110010110-V-0000.bin"
noncomputable def vp000110010110 : Blocks := vp000110010110_0
private theorem bp0001100101100 : Branch 0 (-811761639/2000000 : ℚ) vp000110010110 := by
  apply branch_left_normalized (c:=vp0001100101100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-811761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-811761639/1000000 : ℚ) by norm_num]
  exact coverp0001100101100
private noncomputable def ep0001100101101_0 : Blocks := edgeBlocks% "full/vectors/0001100101101-E-0000.bin"
noncomputable def ep0001100101101 : Blocks := ep0001100101101_0
private theorem idp0001100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110010110.list =
    C ((2:ℤ)^97) * horner X vp0001100101101.list + horner X ep0001100101101.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100101101 : Branch 1 (-811761639/2000000 : ℚ) vp000110010110 := by
  apply branch_checked idp0001100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-811761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-812761639/1000000 : ℚ) by norm_num]
  exact coverp0001100101101
theorem coverp000110010110 : Covers (-811761639/2000000 : ℚ) vp000110010110 := join_branches bp0001100101100 bp0001100101101
private noncomputable def vp00011001011_0 : Blocks := edgeBlocks% "full/vectors/00011001011-V-0000.bin"
private noncomputable def vp00011001011_1 : Blocks := edgeBlocks% "full/vectors/00011001011-V-0001.bin"
noncomputable def vp00011001011 : Blocks := (Blocks.join vp00011001011_0 vp00011001011_1)
private theorem bp000110010110 : Branch 0 (-811761639/4000000 : ℚ) vp00011001011 := by
  apply branch_left_normalized (c:=vp000110010110) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-811761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-811761639/2000000 : ℚ) by norm_num]
  exact coverp000110010110
private noncomputable def ep000110010111_0 : Blocks := edgeBlocks% "full/vectors/000110010111-E-0000.bin"
private noncomputable def ep000110010111_1 : Blocks := edgeBlocks% "full/vectors/000110010111-E-0001.bin"
noncomputable def ep000110010111 : Blocks := (Blocks.join ep000110010111_0 ep000110010111_1)
private theorem idp000110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011001011.list =
    C ((2:ℤ)^171) * horner X vp000110010111.list + horner X ep000110010111.list := by
  exact edge_identity (B := (2:ℤ)^334) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110010111 : Branch 1 (-811761639/4000000 : ℚ) vp00011001011 := by
  apply branch_checked idp000110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-811761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-813761639/2000000 : ℚ) by norm_num]
  exact coverp000110010111
theorem coverp00011001011 : Covers (-811761639/4000000 : ℚ) vp00011001011 := join_branches bp000110010110 bp000110010111
private noncomputable def vp00011001010111_0 : Blocks := edgeBlocks% "full/vectors/00011001010111-V-0000.bin"
noncomputable def vp00011001010111 : Blocks := vp00011001010111_0
theorem coverp00011001010111 : Covers (-811261639/500000 : ℚ) vp00011001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001010110_0 : Blocks := edgeBlocks% "full/vectors/00011001010110-V-0000.bin"
noncomputable def vp00011001010110 : Blocks := vp00011001010110_0
theorem coverp00011001010110 : Covers (-810761639/500000 : ℚ) vp00011001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100101011_0 : Blocks := edgeBlocks% "full/vectors/0001100101011-V-0000.bin"
noncomputable def vp0001100101011 : Blocks := vp0001100101011_0
private theorem bp00011001010110 : Branch 0 (-810761639/1000000 : ℚ) vp0001100101011 := by
  apply branch_left_normalized (c:=vp00011001010110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-810761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-810761639/500000 : ℚ) by norm_num]
  exact coverp00011001010110
private noncomputable def ep00011001010111_0 : Blocks := edgeBlocks% "full/vectors/00011001010111-E-0000.bin"
noncomputable def ep00011001010111 : Blocks := ep00011001010111_0
private theorem idp00011001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100101011.list =
    C ((2:ℤ)^58) * horner X vp00011001010111.list + horner X ep00011001010111.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001010111 : Branch 1 (-810761639/1000000 : ℚ) vp0001100101011 := by
  apply branch_checked idp00011001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-810761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-811261639/500000 : ℚ) by norm_num]
  exact coverp00011001010111
theorem coverp0001100101011 : Covers (-810761639/1000000 : ℚ) vp0001100101011 := join_branches bp00011001010110 bp00011001010111
private noncomputable def vp00011001010101_0 : Blocks := edgeBlocks% "full/vectors/00011001010101-V-0000.bin"
noncomputable def vp00011001010101 : Blocks := vp00011001010101_0
theorem coverp00011001010101 : Covers (-810261639/500000 : ℚ) vp00011001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001010100_0 : Blocks := edgeBlocks% "full/vectors/00011001010100-V-0000.bin"
noncomputable def vp00011001010100 : Blocks := vp00011001010100_0
theorem coverp00011001010100 : Covers (-809761639/500000 : ℚ) vp00011001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100101010_0 : Blocks := edgeBlocks% "full/vectors/0001100101010-V-0000.bin"
noncomputable def vp0001100101010 : Blocks := vp0001100101010_0
private theorem bp00011001010100 : Branch 0 (-809761639/1000000 : ℚ) vp0001100101010 := by
  apply branch_left_normalized (c:=vp00011001010100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-809761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-809761639/500000 : ℚ) by norm_num]
  exact coverp00011001010100
private noncomputable def ep00011001010101_0 : Blocks := edgeBlocks% "full/vectors/00011001010101-E-0000.bin"
noncomputable def ep00011001010101 : Blocks := ep00011001010101_0
private theorem idp00011001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100101010.list =
    C ((2:ℤ)^58) * horner X vp00011001010101.list + horner X ep00011001010101.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001010101 : Branch 1 (-809761639/1000000 : ℚ) vp0001100101010 := by
  apply branch_checked idp00011001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-809761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-810261639/500000 : ℚ) by norm_num]
  exact coverp00011001010101
theorem coverp0001100101010 : Covers (-809761639/1000000 : ℚ) vp0001100101010 := join_branches bp00011001010100 bp00011001010101
private noncomputable def vp000110010101_0 : Blocks := edgeBlocks% "full/vectors/000110010101-V-0000.bin"
noncomputable def vp000110010101 : Blocks := vp000110010101_0
private theorem bp0001100101010 : Branch 0 (-809761639/2000000 : ℚ) vp000110010101 := by
  apply branch_left_normalized (c:=vp0001100101010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-809761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-809761639/1000000 : ℚ) by norm_num]
  exact coverp0001100101010
private noncomputable def ep0001100101011_0 : Blocks := edgeBlocks% "full/vectors/0001100101011-E-0000.bin"
noncomputable def ep0001100101011 : Blocks := ep0001100101011_0
private theorem idp0001100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110010101.list =
    C ((2:ℤ)^96) * horner X vp0001100101011.list + horner X ep0001100101011.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100101011 : Branch 1 (-809761639/2000000 : ℚ) vp000110010101 := by
  apply branch_checked idp0001100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-809761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-810761639/1000000 : ℚ) by norm_num]
  exact coverp0001100101011
theorem coverp000110010101 : Covers (-809761639/2000000 : ℚ) vp000110010101 := join_branches bp0001100101010 bp0001100101011
private noncomputable def vp00011001010011_0 : Blocks := edgeBlocks% "full/vectors/00011001010011-V-0000.bin"
noncomputable def vp00011001010011 : Blocks := vp00011001010011_0
theorem coverp00011001010011 : Covers (-809261639/500000 : ℚ) vp00011001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001010010_0 : Blocks := edgeBlocks% "full/vectors/00011001010010-V-0000.bin"
noncomputable def vp00011001010010 : Blocks := vp00011001010010_0
theorem coverp00011001010010 : Covers (-808761639/500000 : ℚ) vp00011001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100101001_0 : Blocks := edgeBlocks% "full/vectors/0001100101001-V-0000.bin"
noncomputable def vp0001100101001 : Blocks := vp0001100101001_0
private theorem bp00011001010010 : Branch 0 (-808761639/1000000 : ℚ) vp0001100101001 := by
  apply branch_left_normalized (c:=vp00011001010010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-808761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-808761639/500000 : ℚ) by norm_num]
  exact coverp00011001010010
private noncomputable def ep00011001010011_0 : Blocks := edgeBlocks% "full/vectors/00011001010011-E-0000.bin"
noncomputable def ep00011001010011 : Blocks := ep00011001010011_0
private theorem idp00011001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100101001.list =
    C ((2:ℤ)^58) * horner X vp00011001010011.list + horner X ep00011001010011.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001010011 : Branch 1 (-808761639/1000000 : ℚ) vp0001100101001 := by
  apply branch_checked idp00011001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-808761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-809261639/500000 : ℚ) by norm_num]
  exact coverp00011001010011
theorem coverp0001100101001 : Covers (-808761639/1000000 : ℚ) vp0001100101001 := join_branches bp00011001010010 bp00011001010011
private noncomputable def vp00011001010001_0 : Blocks := edgeBlocks% "full/vectors/00011001010001-V-0000.bin"
noncomputable def vp00011001010001 : Blocks := vp00011001010001_0
theorem coverp00011001010001 : Covers (-808261639/500000 : ℚ) vp00011001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001010000_0 : Blocks := edgeBlocks% "full/vectors/00011001010000-V-0000.bin"
noncomputable def vp00011001010000 : Blocks := vp00011001010000_0
theorem coverp00011001010000 : Covers (-807761639/500000 : ℚ) vp00011001010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100101000_0 : Blocks := edgeBlocks% "full/vectors/0001100101000-V-0000.bin"
noncomputable def vp0001100101000 : Blocks := vp0001100101000_0
private theorem bp00011001010000 : Branch 0 (-807761639/1000000 : ℚ) vp0001100101000 := by
  apply branch_left_normalized (c:=vp00011001010000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-807761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-807761639/500000 : ℚ) by norm_num]
  exact coverp00011001010000
private noncomputable def ep00011001010001_0 : Blocks := edgeBlocks% "full/vectors/00011001010001-E-0000.bin"
noncomputable def ep00011001010001 : Blocks := ep00011001010001_0
private theorem idp00011001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100101000.list =
    C ((2:ℤ)^58) * horner X vp00011001010001.list + horner X ep00011001010001.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001010001 : Branch 1 (-807761639/1000000 : ℚ) vp0001100101000 := by
  apply branch_checked idp00011001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-807761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-808261639/500000 : ℚ) by norm_num]
  exact coverp00011001010001
theorem coverp0001100101000 : Covers (-807761639/1000000 : ℚ) vp0001100101000 := join_branches bp00011001010000 bp00011001010001
private noncomputable def vp000110010100_0 : Blocks := edgeBlocks% "full/vectors/000110010100-V-0000.bin"
noncomputable def vp000110010100 : Blocks := vp000110010100_0
private theorem bp0001100101000 : Branch 0 (-807761639/2000000 : ℚ) vp000110010100 := by
  apply branch_left_normalized (c:=vp0001100101000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-807761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-807761639/1000000 : ℚ) by norm_num]
  exact coverp0001100101000
private noncomputable def ep0001100101001_0 : Blocks := edgeBlocks% "full/vectors/0001100101001-E-0000.bin"
noncomputable def ep0001100101001 : Blocks := ep0001100101001_0
private theorem idp0001100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110010100.list =
    C ((2:ℤ)^97) * horner X vp0001100101001.list + horner X ep0001100101001.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100101001 : Branch 1 (-807761639/2000000 : ℚ) vp000110010100 := by
  apply branch_checked idp0001100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-807761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-808761639/1000000 : ℚ) by norm_num]
  exact coverp0001100101001
theorem coverp000110010100 : Covers (-807761639/2000000 : ℚ) vp000110010100 := join_branches bp0001100101000 bp0001100101001
private noncomputable def vp00011001010_0 : Blocks := edgeBlocks% "full/vectors/00011001010-V-0000.bin"
private noncomputable def vp00011001010_1 : Blocks := edgeBlocks% "full/vectors/00011001010-V-0001.bin"
noncomputable def vp00011001010 : Blocks := (Blocks.join vp00011001010_0 vp00011001010_1)
private theorem bp000110010100 : Branch 0 (-807761639/4000000 : ℚ) vp00011001010 := by
  apply branch_left_normalized (c:=vp000110010100) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-807761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-807761639/2000000 : ℚ) by norm_num]
  exact coverp000110010100
private noncomputable def ep000110010101_0 : Blocks := edgeBlocks% "full/vectors/000110010101-E-0000.bin"
private noncomputable def ep000110010101_1 : Blocks := edgeBlocks% "full/vectors/000110010101-E-0001.bin"
noncomputable def ep000110010101 : Blocks := (Blocks.join ep000110010101_0 ep000110010101_1)
private theorem idp000110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011001010.list =
    C ((2:ℤ)^173) * horner X vp000110010101.list + horner X ep000110010101.list := by
  exact edge_identity (B := (2:ℤ)^336) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110010101 : Branch 1 (-807761639/4000000 : ℚ) vp00011001010 := by
  apply branch_checked idp000110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-807761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-809761639/2000000 : ℚ) by norm_num]
  exact coverp000110010101
theorem coverp00011001010 : Covers (-807761639/4000000 : ℚ) vp00011001010 := join_branches bp000110010100 bp000110010101
private noncomputable def vp0001100101_0 : Blocks := edgeBlocks% "full/vectors/0001100101-V-0000.bin"
private noncomputable def vp0001100101_1 : Blocks := edgeBlocks% "full/vectors/0001100101-V-0001.bin"
private noncomputable def vp0001100101_2 : Blocks := edgeBlocks% "full/vectors/0001100101-V-0002.bin"
noncomputable def vp0001100101 : Blocks := (Blocks.join vp0001100101_0 (Blocks.join vp0001100101_1 vp0001100101_2))
private theorem bp00011001010 : Branch 0 (-807761639/8000000 : ℚ) vp0001100101 := by
  apply branch_left_normalized (c:=vp00011001010) (k:=0) (m:=160) (by decide +kernel)
  rw [show 2*(-807761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-807761639/4000000 : ℚ) by norm_num]
  exact coverp00011001010
private noncomputable def ep00011001011_0 : Blocks := edgeBlocks% "full/vectors/00011001011-E-0000.bin"
private noncomputable def ep00011001011_1 : Blocks := edgeBlocks% "full/vectors/00011001011-E-0001.bin"
private noncomputable def ep00011001011_2 : Blocks := edgeBlocks% "full/vectors/00011001011-E-0002.bin"
noncomputable def ep00011001011 : Blocks := (Blocks.join ep00011001011_0 (Blocks.join ep00011001011_1 ep00011001011_2))
private theorem idp00011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100101.list =
    C ((2:ℤ)^323) * horner X vp00011001011.list + horner X ep00011001011.list := by
  exact edge_identity (B := (2:ℤ)^547) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001011 : Branch 1 (-807761639/8000000 : ℚ) vp0001100101 := by
  apply branch_checked idp00011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-807761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-811761639/4000000 : ℚ) by norm_num]
  exact coverp00011001011
theorem coverp0001100101 : Covers (-807761639/8000000 : ℚ) vp0001100101 := join_branches bp00011001010 bp00011001011
private noncomputable def vp00011001001111_0 : Blocks := edgeBlocks% "full/vectors/00011001001111-V-0000.bin"
noncomputable def vp00011001001111 : Blocks := vp00011001001111_0
theorem coverp00011001001111 : Covers (-807261639/500000 : ℚ) vp00011001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001001110_0 : Blocks := edgeBlocks% "full/vectors/00011001001110-V-0000.bin"
noncomputable def vp00011001001110 : Blocks := vp00011001001110_0
theorem coverp00011001001110 : Covers (-806761639/500000 : ℚ) vp00011001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100100111_0 : Blocks := edgeBlocks% "full/vectors/0001100100111-V-0000.bin"
noncomputable def vp0001100100111 : Blocks := vp0001100100111_0
private theorem bp00011001001110 : Branch 0 (-806761639/1000000 : ℚ) vp0001100100111 := by
  apply branch_left_normalized (c:=vp00011001001110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-806761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-806761639/500000 : ℚ) by norm_num]
  exact coverp00011001001110
private noncomputable def ep00011001001111_0 : Blocks := edgeBlocks% "full/vectors/00011001001111-E-0000.bin"
noncomputable def ep00011001001111 : Blocks := ep00011001001111_0
private theorem idp00011001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100100111.list =
    C ((2:ℤ)^58) * horner X vp00011001001111.list + horner X ep00011001001111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001001111 : Branch 1 (-806761639/1000000 : ℚ) vp0001100100111 := by
  apply branch_checked idp00011001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-806761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-807261639/500000 : ℚ) by norm_num]
  exact coverp00011001001111
theorem coverp0001100100111 : Covers (-806761639/1000000 : ℚ) vp0001100100111 := join_branches bp00011001001110 bp00011001001111
private noncomputable def vp00011001001101_0 : Blocks := edgeBlocks% "full/vectors/00011001001101-V-0000.bin"
noncomputable def vp00011001001101 : Blocks := vp00011001001101_0
theorem coverp00011001001101 : Covers (-806261639/500000 : ℚ) vp00011001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001001100_0 : Blocks := edgeBlocks% "full/vectors/00011001001100-V-0000.bin"
noncomputable def vp00011001001100 : Blocks := vp00011001001100_0
theorem coverp00011001001100 : Covers (-805761639/500000 : ℚ) vp00011001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100100110_0 : Blocks := edgeBlocks% "full/vectors/0001100100110-V-0000.bin"
noncomputable def vp0001100100110 : Blocks := vp0001100100110_0
private theorem bp00011001001100 : Branch 0 (-805761639/1000000 : ℚ) vp0001100100110 := by
  apply branch_left_normalized (c:=vp00011001001100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-805761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-805761639/500000 : ℚ) by norm_num]
  exact coverp00011001001100
private noncomputable def ep00011001001101_0 : Blocks := edgeBlocks% "full/vectors/00011001001101-E-0000.bin"
noncomputable def ep00011001001101 : Blocks := ep00011001001101_0
private theorem idp00011001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100100110.list =
    C ((2:ℤ)^58) * horner X vp00011001001101.list + horner X ep00011001001101.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001001101 : Branch 1 (-805761639/1000000 : ℚ) vp0001100100110 := by
  apply branch_checked idp00011001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-805761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-806261639/500000 : ℚ) by norm_num]
  exact coverp00011001001101
theorem coverp0001100100110 : Covers (-805761639/1000000 : ℚ) vp0001100100110 := join_branches bp00011001001100 bp00011001001101
private noncomputable def vp000110010011_0 : Blocks := edgeBlocks% "full/vectors/000110010011-V-0000.bin"
noncomputable def vp000110010011 : Blocks := vp000110010011_0
private theorem bp0001100100110 : Branch 0 (-805761639/2000000 : ℚ) vp000110010011 := by
  apply branch_left_normalized (c:=vp0001100100110) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-805761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-805761639/1000000 : ℚ) by norm_num]
  exact coverp0001100100110
private noncomputable def ep0001100100111_0 : Blocks := edgeBlocks% "full/vectors/0001100100111-E-0000.bin"
noncomputable def ep0001100100111 : Blocks := ep0001100100111_0
private theorem idp0001100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110010011.list =
    C ((2:ℤ)^97) * horner X vp0001100100111.list + horner X ep0001100100111.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100100111 : Branch 1 (-805761639/2000000 : ℚ) vp000110010011 := by
  apply branch_checked idp0001100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-805761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-806761639/1000000 : ℚ) by norm_num]
  exact coverp0001100100111
theorem coverp000110010011 : Covers (-805761639/2000000 : ℚ) vp000110010011 := join_branches bp0001100100110 bp0001100100111
private noncomputable def vp00011001001011_0 : Blocks := edgeBlocks% "full/vectors/00011001001011-V-0000.bin"
noncomputable def vp00011001001011 : Blocks := vp00011001001011_0
theorem coverp00011001001011 : Covers (-805261639/500000 : ℚ) vp00011001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001001010_0 : Blocks := edgeBlocks% "full/vectors/00011001001010-V-0000.bin"
noncomputable def vp00011001001010 : Blocks := vp00011001001010_0
theorem coverp00011001001010 : Covers (-804761639/500000 : ℚ) vp00011001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100100101_0 : Blocks := edgeBlocks% "full/vectors/0001100100101-V-0000.bin"
noncomputable def vp0001100100101 : Blocks := vp0001100100101_0
private theorem bp00011001001010 : Branch 0 (-804761639/1000000 : ℚ) vp0001100100101 := by
  apply branch_left_normalized (c:=vp00011001001010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-804761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-804761639/500000 : ℚ) by norm_num]
  exact coverp00011001001010
private noncomputable def ep00011001001011_0 : Blocks := edgeBlocks% "full/vectors/00011001001011-E-0000.bin"
noncomputable def ep00011001001011 : Blocks := ep00011001001011_0
private theorem idp00011001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100100101.list =
    C ((2:ℤ)^57) * horner X vp00011001001011.list + horner X ep00011001001011.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001001011 : Branch 1 (-804761639/1000000 : ℚ) vp0001100100101 := by
  apply branch_checked idp00011001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-804761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-805261639/500000 : ℚ) by norm_num]
  exact coverp00011001001011
theorem coverp0001100100101 : Covers (-804761639/1000000 : ℚ) vp0001100100101 := join_branches bp00011001001010 bp00011001001011
private noncomputable def vp00011001001001_0 : Blocks := edgeBlocks% "full/vectors/00011001001001-V-0000.bin"
noncomputable def vp00011001001001 : Blocks := vp00011001001001_0
theorem coverp00011001001001 : Covers (-804261639/500000 : ℚ) vp00011001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001001000_0 : Blocks := edgeBlocks% "full/vectors/00011001001000-V-0000.bin"
noncomputable def vp00011001001000 : Blocks := vp00011001001000_0
theorem coverp00011001001000 : Covers (-803761639/500000 : ℚ) vp00011001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100100100_0 : Blocks := edgeBlocks% "full/vectors/0001100100100-V-0000.bin"
noncomputable def vp0001100100100 : Blocks := vp0001100100100_0
private theorem bp00011001001000 : Branch 0 (-803761639/1000000 : ℚ) vp0001100100100 := by
  apply branch_left_normalized (c:=vp00011001001000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-803761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-803761639/500000 : ℚ) by norm_num]
  exact coverp00011001001000
private noncomputable def ep00011001001001_0 : Blocks := edgeBlocks% "full/vectors/00011001001001-E-0000.bin"
noncomputable def ep00011001001001 : Blocks := ep00011001001001_0
private theorem idp00011001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100100100.list =
    C ((2:ℤ)^58) * horner X vp00011001001001.list + horner X ep00011001001001.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001001001 : Branch 1 (-803761639/1000000 : ℚ) vp0001100100100 := by
  apply branch_checked idp00011001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-803761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-804261639/500000 : ℚ) by norm_num]
  exact coverp00011001001001
theorem coverp0001100100100 : Covers (-803761639/1000000 : ℚ) vp0001100100100 := join_branches bp00011001001000 bp00011001001001
private noncomputable def vp000110010010_0 : Blocks := edgeBlocks% "full/vectors/000110010010-V-0000.bin"
noncomputable def vp000110010010 : Blocks := vp000110010010_0
private theorem bp0001100100100 : Branch 0 (-803761639/2000000 : ℚ) vp000110010010 := by
  apply branch_left_normalized (c:=vp0001100100100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-803761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-803761639/1000000 : ℚ) by norm_num]
  exact coverp0001100100100
private noncomputable def ep0001100100101_0 : Blocks := edgeBlocks% "full/vectors/0001100100101-E-0000.bin"
noncomputable def ep0001100100101 : Blocks := ep0001100100101_0
private theorem idp0001100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110010010.list =
    C ((2:ℤ)^97) * horner X vp0001100100101.list + horner X ep0001100100101.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100100101 : Branch 1 (-803761639/2000000 : ℚ) vp000110010010 := by
  apply branch_checked idp0001100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-803761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-804761639/1000000 : ℚ) by norm_num]
  exact coverp0001100100101
theorem coverp000110010010 : Covers (-803761639/2000000 : ℚ) vp000110010010 := join_branches bp0001100100100 bp0001100100101
private noncomputable def vp00011001001_0 : Blocks := edgeBlocks% "full/vectors/00011001001-V-0000.bin"
private noncomputable def vp00011001001_1 : Blocks := edgeBlocks% "full/vectors/00011001001-V-0001.bin"
noncomputable def vp00011001001 : Blocks := (Blocks.join vp00011001001_0 vp00011001001_1)
private theorem bp000110010010 : Branch 0 (-803761639/4000000 : ℚ) vp00011001001 := by
  apply branch_left_normalized (c:=vp000110010010) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-803761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-803761639/2000000 : ℚ) by norm_num]
  exact coverp000110010010
private noncomputable def ep000110010011_0 : Blocks := edgeBlocks% "full/vectors/000110010011-E-0000.bin"
private noncomputable def ep000110010011_1 : Blocks := edgeBlocks% "full/vectors/000110010011-E-0001.bin"
noncomputable def ep000110010011 : Blocks := (Blocks.join ep000110010011_0 ep000110010011_1)
private theorem idp000110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011001001.list =
    C ((2:ℤ)^173) * horner X vp000110010011.list + horner X ep000110010011.list := by
  exact edge_identity (B := (2:ℤ)^337) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110010011 : Branch 1 (-803761639/4000000 : ℚ) vp00011001001 := by
  apply branch_checked idp000110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-803761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-805761639/2000000 : ℚ) by norm_num]
  exact coverp000110010011
theorem coverp00011001001 : Covers (-803761639/4000000 : ℚ) vp00011001001 := join_branches bp000110010010 bp000110010011
private noncomputable def vp00011001000111_0 : Blocks := edgeBlocks% "full/vectors/00011001000111-V-0000.bin"
noncomputable def vp00011001000111 : Blocks := vp00011001000111_0
theorem coverp00011001000111 : Covers (-803261639/500000 : ℚ) vp00011001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001000110_0 : Blocks := edgeBlocks% "full/vectors/00011001000110-V-0000.bin"
noncomputable def vp00011001000110 : Blocks := vp00011001000110_0
theorem coverp00011001000110 : Covers (-802761639/500000 : ℚ) vp00011001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100100011_0 : Blocks := edgeBlocks% "full/vectors/0001100100011-V-0000.bin"
noncomputable def vp0001100100011 : Blocks := vp0001100100011_0
private theorem bp00011001000110 : Branch 0 (-802761639/1000000 : ℚ) vp0001100100011 := by
  apply branch_left_normalized (c:=vp00011001000110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-802761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-802761639/500000 : ℚ) by norm_num]
  exact coverp00011001000110
private noncomputable def ep00011001000111_0 : Blocks := edgeBlocks% "full/vectors/00011001000111-E-0000.bin"
noncomputable def ep00011001000111 : Blocks := ep00011001000111_0
private theorem idp00011001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100100011.list =
    C ((2:ℤ)^58) * horner X vp00011001000111.list + horner X ep00011001000111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001000111 : Branch 1 (-802761639/1000000 : ℚ) vp0001100100011 := by
  apply branch_checked idp00011001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-802761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-803261639/500000 : ℚ) by norm_num]
  exact coverp00011001000111
theorem coverp0001100100011 : Covers (-802761639/1000000 : ℚ) vp0001100100011 := join_branches bp00011001000110 bp00011001000111
private noncomputable def vp00011001000101_0 : Blocks := edgeBlocks% "full/vectors/00011001000101-V-0000.bin"
noncomputable def vp00011001000101 : Blocks := vp00011001000101_0
theorem coverp00011001000101 : Covers (-802261639/500000 : ℚ) vp00011001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001000100_0 : Blocks := edgeBlocks% "full/vectors/00011001000100-V-0000.bin"
noncomputable def vp00011001000100 : Blocks := vp00011001000100_0
theorem coverp00011001000100 : Covers (-801761639/500000 : ℚ) vp00011001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100100010_0 : Blocks := edgeBlocks% "full/vectors/0001100100010-V-0000.bin"
noncomputable def vp0001100100010 : Blocks := vp0001100100010_0
private theorem bp00011001000100 : Branch 0 (-801761639/1000000 : ℚ) vp0001100100010 := by
  apply branch_left_normalized (c:=vp00011001000100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-801761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-801761639/500000 : ℚ) by norm_num]
  exact coverp00011001000100
private noncomputable def ep00011001000101_0 : Blocks := edgeBlocks% "full/vectors/00011001000101-E-0000.bin"
noncomputable def ep00011001000101 : Blocks := ep00011001000101_0
private theorem idp00011001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100100010.list =
    C ((2:ℤ)^58) * horner X vp00011001000101.list + horner X ep00011001000101.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001000101 : Branch 1 (-801761639/1000000 : ℚ) vp0001100100010 := by
  apply branch_checked idp00011001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-801761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-802261639/500000 : ℚ) by norm_num]
  exact coverp00011001000101
theorem coverp0001100100010 : Covers (-801761639/1000000 : ℚ) vp0001100100010 := join_branches bp00011001000100 bp00011001000101
private noncomputable def vp000110010001_0 : Blocks := edgeBlocks% "full/vectors/000110010001-V-0000.bin"
noncomputable def vp000110010001 : Blocks := vp000110010001_0
private theorem bp0001100100010 : Branch 0 (-801761639/2000000 : ℚ) vp000110010001 := by
  apply branch_left_normalized (c:=vp0001100100010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-801761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-801761639/1000000 : ℚ) by norm_num]
  exact coverp0001100100010
private noncomputable def ep0001100100011_0 : Blocks := edgeBlocks% "full/vectors/0001100100011-E-0000.bin"
noncomputable def ep0001100100011 : Blocks := ep0001100100011_0
private theorem idp0001100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110010001.list =
    C ((2:ℤ)^98) * horner X vp0001100100011.list + horner X ep0001100100011.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100100011 : Branch 1 (-801761639/2000000 : ℚ) vp000110010001 := by
  apply branch_checked idp0001100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-801761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-802761639/1000000 : ℚ) by norm_num]
  exact coverp0001100100011
theorem coverp000110010001 : Covers (-801761639/2000000 : ℚ) vp000110010001 := join_branches bp0001100100010 bp0001100100011
private noncomputable def vp00011001000011_0 : Blocks := edgeBlocks% "full/vectors/00011001000011-V-0000.bin"
noncomputable def vp00011001000011 : Blocks := vp00011001000011_0
theorem coverp00011001000011 : Covers (-801261639/500000 : ℚ) vp00011001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001000010_0 : Blocks := edgeBlocks% "full/vectors/00011001000010-V-0000.bin"
noncomputable def vp00011001000010 : Blocks := vp00011001000010_0
theorem coverp00011001000010 : Covers (-800761639/500000 : ℚ) vp00011001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100100001_0 : Blocks := edgeBlocks% "full/vectors/0001100100001-V-0000.bin"
noncomputable def vp0001100100001 : Blocks := vp0001100100001_0
private theorem bp00011001000010 : Branch 0 (-800761639/1000000 : ℚ) vp0001100100001 := by
  apply branch_left_normalized (c:=vp00011001000010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-800761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-800761639/500000 : ℚ) by norm_num]
  exact coverp00011001000010
private noncomputable def ep00011001000011_0 : Blocks := edgeBlocks% "full/vectors/00011001000011-E-0000.bin"
noncomputable def ep00011001000011 : Blocks := ep00011001000011_0
private theorem idp00011001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100100001.list =
    C ((2:ℤ)^58) * horner X vp00011001000011.list + horner X ep00011001000011.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001000011 : Branch 1 (-800761639/1000000 : ℚ) vp0001100100001 := by
  apply branch_checked idp00011001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-800761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-801261639/500000 : ℚ) by norm_num]
  exact coverp00011001000011
theorem coverp0001100100001 : Covers (-800761639/1000000 : ℚ) vp0001100100001 := join_branches bp00011001000010 bp00011001000011
private noncomputable def vp00011001000001_0 : Blocks := edgeBlocks% "full/vectors/00011001000001-V-0000.bin"
noncomputable def vp00011001000001 : Blocks := vp00011001000001_0
theorem coverp00011001000001 : Covers (-800261639/500000 : ℚ) vp00011001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00011001000000_0 : Blocks := edgeBlocks% "full/vectors/00011001000000-V-0000.bin"
noncomputable def vp00011001000000 : Blocks := vp00011001000000_0
theorem coverp00011001000000 : Covers (-799761639/500000 : ℚ) vp00011001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001100100000_0 : Blocks := edgeBlocks% "full/vectors/0001100100000-V-0000.bin"
noncomputable def vp0001100100000 : Blocks := vp0001100100000_0
private theorem bp00011001000000 : Branch 0 (-799761639/1000000 : ℚ) vp0001100100000 := by
  apply branch_left_normalized (c:=vp00011001000000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-799761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-799761639/500000 : ℚ) by norm_num]
  exact coverp00011001000000
private noncomputable def ep00011001000001_0 : Blocks := edgeBlocks% "full/vectors/00011001000001-E-0000.bin"
noncomputable def ep00011001000001 : Blocks := ep00011001000001_0
private theorem idp00011001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100100000.list =
    C ((2:ℤ)^58) * horner X vp00011001000001.list + horner X ep00011001000001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001000001 : Branch 1 (-799761639/1000000 : ℚ) vp0001100100000 := by
  apply branch_checked idp00011001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-799761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-800261639/500000 : ℚ) by norm_num]
  exact coverp00011001000001
theorem coverp0001100100000 : Covers (-799761639/1000000 : ℚ) vp0001100100000 := join_branches bp00011001000000 bp00011001000001
private noncomputable def vp000110010000_0 : Blocks := edgeBlocks% "full/vectors/000110010000-V-0000.bin"
noncomputable def vp000110010000 : Blocks := vp000110010000_0
private theorem bp0001100100000 : Branch 0 (-799761639/2000000 : ℚ) vp000110010000 := by
  apply branch_left_normalized (c:=vp0001100100000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-799761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-799761639/1000000 : ℚ) by norm_num]
  exact coverp0001100100000
private noncomputable def ep0001100100001_0 : Blocks := edgeBlocks% "full/vectors/0001100100001-E-0000.bin"
noncomputable def ep0001100100001 : Blocks := ep0001100100001_0
private theorem idp0001100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110010000.list =
    C ((2:ℤ)^97) * horner X vp0001100100001.list + horner X ep0001100100001.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100100001 : Branch 1 (-799761639/2000000 : ℚ) vp000110010000 := by
  apply branch_checked idp0001100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-799761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-800761639/1000000 : ℚ) by norm_num]
  exact coverp0001100100001
theorem coverp000110010000 : Covers (-799761639/2000000 : ℚ) vp000110010000 := join_branches bp0001100100000 bp0001100100001
private noncomputable def vp00011001000_0 : Blocks := edgeBlocks% "full/vectors/00011001000-V-0000.bin"
private noncomputable def vp00011001000_1 : Blocks := edgeBlocks% "full/vectors/00011001000-V-0001.bin"
noncomputable def vp00011001000 : Blocks := (Blocks.join vp00011001000_0 vp00011001000_1)
private theorem bp000110010000 : Branch 0 (-799761639/4000000 : ℚ) vp00011001000 := by
  apply branch_left_normalized (c:=vp000110010000) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-799761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-799761639/2000000 : ℚ) by norm_num]
  exact coverp000110010000
private noncomputable def ep000110010001_0 : Blocks := edgeBlocks% "full/vectors/000110010001-E-0000.bin"
private noncomputable def ep000110010001_1 : Blocks := edgeBlocks% "full/vectors/000110010001-E-0001.bin"
noncomputable def ep000110010001 : Blocks := (Blocks.join ep000110010001_0 ep000110010001_1)
private theorem idp000110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011001000.list =
    C ((2:ℤ)^174) * horner X vp000110010001.list + horner X ep000110010001.list := by
  exact edge_identity (B := (2:ℤ)^338) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110010001 : Branch 1 (-799761639/4000000 : ℚ) vp00011001000 := by
  apply branch_checked idp000110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-799761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-801761639/2000000 : ℚ) by norm_num]
  exact coverp000110010001
theorem coverp00011001000 : Covers (-799761639/4000000 : ℚ) vp00011001000 := join_branches bp000110010000 bp000110010001
private noncomputable def vp0001100100_0 : Blocks := edgeBlocks% "full/vectors/0001100100-V-0000.bin"
private noncomputable def vp0001100100_1 : Blocks := edgeBlocks% "full/vectors/0001100100-V-0001.bin"
private noncomputable def vp0001100100_2 : Blocks := edgeBlocks% "full/vectors/0001100100-V-0002.bin"
noncomputable def vp0001100100 : Blocks := (Blocks.join vp0001100100_0 (Blocks.join vp0001100100_1 vp0001100100_2))
private theorem bp00011001000 : Branch 0 (-799761639/8000000 : ℚ) vp0001100100 := by
  apply branch_left_normalized (c:=vp00011001000) (k:=0) (m:=161) (by decide +kernel)
  rw [show 2*(-799761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-799761639/4000000 : ℚ) by norm_num]
  exact coverp00011001000
private noncomputable def ep00011001001_0 : Blocks := edgeBlocks% "full/vectors/00011001001-E-0000.bin"
private noncomputable def ep00011001001_1 : Blocks := edgeBlocks% "full/vectors/00011001001-E-0001.bin"
private noncomputable def ep00011001001_2 : Blocks := edgeBlocks% "full/vectors/00011001001-E-0002.bin"
noncomputable def ep00011001001 : Blocks := (Blocks.join ep00011001001_0 (Blocks.join ep00011001001_1 ep00011001001_2))
private theorem idp00011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001100100.list =
    C ((2:ℤ)^325) * horner X vp00011001001.list + horner X ep00011001001.list := by
  exact edge_identity (B := (2:ℤ)^551) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00011001001 : Branch 1 (-799761639/8000000 : ℚ) vp0001100100 := by
  apply branch_checked idp00011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-799761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-803761639/4000000 : ℚ) by norm_num]
  exact coverp00011001001
theorem coverp0001100100 : Covers (-799761639/8000000 : ℚ) vp0001100100 := join_branches bp00011001000 bp00011001001
private noncomputable def vp000110010_0 : Blocks := edgeBlocks% "full/vectors/000110010-V-0000.bin"
private noncomputable def vp000110010_1 : Blocks := edgeBlocks% "full/vectors/000110010-V-0001.bin"
private noncomputable def vp000110010_2 : Blocks := edgeBlocks% "full/vectors/000110010-V-0002.bin"
private noncomputable def vp000110010_3 : Blocks := edgeBlocks% "full/vectors/000110010-V-0003.bin"
private noncomputable def vp000110010_4 : Blocks := edgeBlocks% "full/vectors/000110010-V-0004.bin"
noncomputable def vp000110010 : Blocks := (Blocks.join (Blocks.join vp000110010_0 vp000110010_1) (Blocks.join vp000110010_2 (Blocks.join vp000110010_3 vp000110010_4)))
private theorem bp0001100100 : Branch 0 (-799761639/16000000 : ℚ) vp000110010 := by
  apply branch_left_normalized (c:=vp0001100100) (k:=0) (m:=300) (by decide +kernel)
  rw [show 2*(-799761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-799761639/8000000 : ℚ) by norm_num]
  exact coverp0001100100
private noncomputable def ep0001100101_0 : Blocks := edgeBlocks% "full/vectors/0001100101-E-0000.bin"
private noncomputable def ep0001100101_1 : Blocks := edgeBlocks% "full/vectors/0001100101-E-0001.bin"
private noncomputable def ep0001100101_2 : Blocks := edgeBlocks% "full/vectors/0001100101-E-0002.bin"
private noncomputable def ep0001100101_3 : Blocks := edgeBlocks% "full/vectors/0001100101-E-0003.bin"
private noncomputable def ep0001100101_4 : Blocks := edgeBlocks% "full/vectors/0001100101-E-0004.bin"
noncomputable def ep0001100101 : Blocks := (Blocks.join (Blocks.join ep0001100101_0 ep0001100101_1) (Blocks.join ep0001100101_2 (Blocks.join ep0001100101_3 ep0001100101_4)))
private theorem idp0001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000110010.list =
    C ((2:ℤ)^622) * horner X vp0001100101.list + horner X ep0001100101.list := by
  exact edge_identity (B := (2:ℤ)^972) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001100101 : Branch 1 (-799761639/16000000 : ℚ) vp000110010 := by
  apply branch_checked idp0001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-799761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-807761639/8000000 : ℚ) by norm_num]
  exact coverp0001100101
theorem coverp000110010 : Covers (-799761639/16000000 : ℚ) vp000110010 := join_branches bp0001100100 bp0001100101
private noncomputable def vp00011001_0 : Blocks := edgeBlocks% "full/vectors/00011001-V-0000.bin"
private noncomputable def vp00011001_1 : Blocks := edgeBlocks% "full/vectors/00011001-V-0001.bin"
private noncomputable def vp00011001_2 : Blocks := edgeBlocks% "full/vectors/00011001-V-0002.bin"
private noncomputable def vp00011001_3 : Blocks := edgeBlocks% "full/vectors/00011001-V-0003.bin"
private noncomputable def vp00011001_4 : Blocks := edgeBlocks% "full/vectors/00011001-V-0004.bin"
private noncomputable def vp00011001_5 : Blocks := edgeBlocks% "full/vectors/00011001-V-0005.bin"
private noncomputable def vp00011001_6 : Blocks := edgeBlocks% "full/vectors/00011001-V-0006.bin"
private noncomputable def vp00011001_7 : Blocks := edgeBlocks% "full/vectors/00011001-V-0007.bin"
private noncomputable def vp00011001_8 : Blocks := edgeBlocks% "full/vectors/00011001-V-0008.bin"
noncomputable def vp00011001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00011001_0 vp00011001_1) (Blocks.join vp00011001_2 vp00011001_3)) (Blocks.join (Blocks.join vp00011001_4 vp00011001_5) (Blocks.join vp00011001_6 (Blocks.join vp00011001_7 vp00011001_8))))
private theorem bp000110010 : Branch 0 (-799761639/32000000 : ℚ) vp00011001 := by
  apply branch_left_normalized (c:=vp000110010) (k:=0) (m:=574) (by decide +kernel)
  rw [show 2*(-799761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-799761639/16000000 : ℚ) by norm_num]
  exact coverp000110010
private noncomputable def ep000110011_0 : Blocks := edgeBlocks% "full/vectors/000110011-E-0000.bin"
private noncomputable def ep000110011_1 : Blocks := edgeBlocks% "full/vectors/000110011-E-0001.bin"
private noncomputable def ep000110011_2 : Blocks := edgeBlocks% "full/vectors/000110011-E-0002.bin"
private noncomputable def ep000110011_3 : Blocks := edgeBlocks% "full/vectors/000110011-E-0003.bin"
private noncomputable def ep000110011_4 : Blocks := edgeBlocks% "full/vectors/000110011-E-0004.bin"
private noncomputable def ep000110011_5 : Blocks := edgeBlocks% "full/vectors/000110011-E-0005.bin"
private noncomputable def ep000110011_6 : Blocks := edgeBlocks% "full/vectors/000110011-E-0006.bin"
private noncomputable def ep000110011_7 : Blocks := edgeBlocks% "full/vectors/000110011-E-0007.bin"
private noncomputable def ep000110011_8 : Blocks := edgeBlocks% "full/vectors/000110011-E-0008.bin"
noncomputable def ep000110011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000110011_0 ep000110011_1) (Blocks.join ep000110011_2 ep000110011_3)) (Blocks.join (Blocks.join ep000110011_4 ep000110011_5) (Blocks.join ep000110011_6 (Blocks.join ep000110011_7 ep000110011_8))))
private theorem idp000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00011001.list =
    C ((2:ℤ)^1211) * horner X vp000110011.list + horner X ep000110011.list := by
  exact edge_identity (B := (2:ℤ)^1807) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000110011 : Branch 1 (-799761639/32000000 : ℚ) vp00011001 := by
  apply branch_checked idp000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-799761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-815761639/16000000 : ℚ) by norm_num]
  exact coverp000110011
theorem coverp00011001 : Covers (-799761639/32000000 : ℚ) vp00011001 := join_branches bp000110010 bp000110011
end NextProof.EdgeFull

