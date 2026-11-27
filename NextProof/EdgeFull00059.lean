import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00058

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00001100111111_0 : Blocks := edgeBlocks% "full/vectors/00001100111111-V-0000.bin"
noncomputable def vp00001100111111 : Blocks := vp00001100111111_0
theorem coverp00001100111111 : Covers (-415261639/500000 : ℚ) vp00001100111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100111110_0 : Blocks := edgeBlocks% "full/vectors/00001100111110-V-0000.bin"
noncomputable def vp00001100111110 : Blocks := vp00001100111110_0
theorem coverp00001100111110 : Covers (-414761639/500000 : ℚ) vp00001100111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110011111_0 : Blocks := edgeBlocks% "full/vectors/0000110011111-V-0000.bin"
noncomputable def vp0000110011111 : Blocks := vp0000110011111_0
private theorem bp00001100111110 : Branch 0 (-414761639/1000000 : ℚ) vp0000110011111 := by
  apply branch_left_normalized (c:=vp00001100111110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-414761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-414761639/500000 : ℚ) by norm_num]
  exact coverp00001100111110
private noncomputable def ep00001100111111_0 : Blocks := edgeBlocks% "full/vectors/00001100111111-E-0000.bin"
noncomputable def ep00001100111111 : Blocks := ep00001100111111_0
private theorem idp00001100111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110011111.list =
    C ((2:ℤ)^71) * horner X vp00001100111111.list + horner X ep00001100111111.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100111111 : Branch 1 (-414761639/1000000 : ℚ) vp0000110011111 := by
  apply branch_checked idp00001100111111 (by positivity) (by decide +kernel)
  rw [show 2*(-414761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-415261639/500000 : ℚ) by norm_num]
  exact coverp00001100111111
theorem coverp0000110011111 : Covers (-414761639/1000000 : ℚ) vp0000110011111 := join_branches bp00001100111110 bp00001100111111
private noncomputable def vp00001100111101_0 : Blocks := edgeBlocks% "full/vectors/00001100111101-V-0000.bin"
noncomputable def vp00001100111101 : Blocks := vp00001100111101_0
theorem coverp00001100111101 : Covers (-414261639/500000 : ℚ) vp00001100111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100111100_0 : Blocks := edgeBlocks% "full/vectors/00001100111100-V-0000.bin"
noncomputable def vp00001100111100 : Blocks := vp00001100111100_0
theorem coverp00001100111100 : Covers (-413761639/500000 : ℚ) vp00001100111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110011110_0 : Blocks := edgeBlocks% "full/vectors/0000110011110-V-0000.bin"
noncomputable def vp0000110011110 : Blocks := vp0000110011110_0
private theorem bp00001100111100 : Branch 0 (-413761639/1000000 : ℚ) vp0000110011110 := by
  apply branch_left_normalized (c:=vp00001100111100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-413761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-413761639/500000 : ℚ) by norm_num]
  exact coverp00001100111100
private noncomputable def ep00001100111101_0 : Blocks := edgeBlocks% "full/vectors/00001100111101-E-0000.bin"
noncomputable def ep00001100111101 : Blocks := ep00001100111101_0
private theorem idp00001100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110011110.list =
    C ((2:ℤ)^71) * horner X vp00001100111101.list + horner X ep00001100111101.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100111101 : Branch 1 (-413761639/1000000 : ℚ) vp0000110011110 := by
  apply branch_checked idp00001100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-413761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-414261639/500000 : ℚ) by norm_num]
  exact coverp00001100111101
theorem coverp0000110011110 : Covers (-413761639/1000000 : ℚ) vp0000110011110 := join_branches bp00001100111100 bp00001100111101
private noncomputable def vp000011001111_0 : Blocks := edgeBlocks% "full/vectors/000011001111-V-0000.bin"
noncomputable def vp000011001111 : Blocks := vp000011001111_0
private theorem bp0000110011110 : Branch 0 (-413761639/2000000 : ℚ) vp000011001111 := by
  apply branch_left_normalized (c:=vp0000110011110) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-413761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-413761639/1000000 : ℚ) by norm_num]
  exact coverp0000110011110
private noncomputable def ep0000110011111_0 : Blocks := edgeBlocks% "full/vectors/0000110011111-E-0000.bin"
noncomputable def ep0000110011111 : Blocks := ep0000110011111_0
private theorem idp0000110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011001111.list =
    C ((2:ℤ)^123) * horner X vp0000110011111.list + horner X ep0000110011111.list := by
  exact edge_identity (B := (2:ℤ)^269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110011111 : Branch 1 (-413761639/2000000 : ℚ) vp000011001111 := by
  apply branch_checked idp0000110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-413761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-414761639/1000000 : ℚ) by norm_num]
  exact coverp0000110011111
theorem coverp000011001111 : Covers (-413761639/2000000 : ℚ) vp000011001111 := join_branches bp0000110011110 bp0000110011111
private noncomputable def vp00001100111011_0 : Blocks := edgeBlocks% "full/vectors/00001100111011-V-0000.bin"
noncomputable def vp00001100111011 : Blocks := vp00001100111011_0
theorem coverp00001100111011 : Covers (-413261639/500000 : ℚ) vp00001100111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100111010_0 : Blocks := edgeBlocks% "full/vectors/00001100111010-V-0000.bin"
noncomputable def vp00001100111010 : Blocks := vp00001100111010_0
theorem coverp00001100111010 : Covers (-412761639/500000 : ℚ) vp00001100111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110011101_0 : Blocks := edgeBlocks% "full/vectors/0000110011101-V-0000.bin"
noncomputable def vp0000110011101 : Blocks := vp0000110011101_0
private theorem bp00001100111010 : Branch 0 (-412761639/1000000 : ℚ) vp0000110011101 := by
  apply branch_left_normalized (c:=vp00001100111010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-412761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-412761639/500000 : ℚ) by norm_num]
  exact coverp00001100111010
private noncomputable def ep00001100111011_0 : Blocks := edgeBlocks% "full/vectors/00001100111011-E-0000.bin"
noncomputable def ep00001100111011 : Blocks := ep00001100111011_0
private theorem idp00001100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110011101.list =
    C ((2:ℤ)^72) * horner X vp00001100111011.list + horner X ep00001100111011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100111011 : Branch 1 (-412761639/1000000 : ℚ) vp0000110011101 := by
  apply branch_checked idp00001100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-412761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-413261639/500000 : ℚ) by norm_num]
  exact coverp00001100111011
theorem coverp0000110011101 : Covers (-412761639/1000000 : ℚ) vp0000110011101 := join_branches bp00001100111010 bp00001100111011
private noncomputable def vp00001100111001_0 : Blocks := edgeBlocks% "full/vectors/00001100111001-V-0000.bin"
noncomputable def vp00001100111001 : Blocks := vp00001100111001_0
theorem coverp00001100111001 : Covers (-412261639/500000 : ℚ) vp00001100111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100111000_0 : Blocks := edgeBlocks% "full/vectors/00001100111000-V-0000.bin"
noncomputable def vp00001100111000 : Blocks := vp00001100111000_0
theorem coverp00001100111000 : Covers (-411761639/500000 : ℚ) vp00001100111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110011100_0 : Blocks := edgeBlocks% "full/vectors/0000110011100-V-0000.bin"
noncomputable def vp0000110011100 : Blocks := vp0000110011100_0
private theorem bp00001100111000 : Branch 0 (-411761639/1000000 : ℚ) vp0000110011100 := by
  apply branch_left_normalized (c:=vp00001100111000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-411761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-411761639/500000 : ℚ) by norm_num]
  exact coverp00001100111000
private noncomputable def ep00001100111001_0 : Blocks := edgeBlocks% "full/vectors/00001100111001-E-0000.bin"
noncomputable def ep00001100111001 : Blocks := ep00001100111001_0
private theorem idp00001100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110011100.list =
    C ((2:ℤ)^72) * horner X vp00001100111001.list + horner X ep00001100111001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100111001 : Branch 1 (-411761639/1000000 : ℚ) vp0000110011100 := by
  apply branch_checked idp00001100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-411761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-412261639/500000 : ℚ) by norm_num]
  exact coverp00001100111001
theorem coverp0000110011100 : Covers (-411761639/1000000 : ℚ) vp0000110011100 := join_branches bp00001100111000 bp00001100111001
private noncomputable def vp000011001110_0 : Blocks := edgeBlocks% "full/vectors/000011001110-V-0000.bin"
noncomputable def vp000011001110 : Blocks := vp000011001110_0
private theorem bp0000110011100 : Branch 0 (-411761639/2000000 : ℚ) vp000011001110 := by
  apply branch_left_normalized (c:=vp0000110011100) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-411761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-411761639/1000000 : ℚ) by norm_num]
  exact coverp0000110011100
private noncomputable def ep0000110011101_0 : Blocks := edgeBlocks% "full/vectors/0000110011101-E-0000.bin"
noncomputable def ep0000110011101 : Blocks := ep0000110011101_0
private theorem idp0000110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011001110.list =
    C ((2:ℤ)^125) * horner X vp0000110011101.list + horner X ep0000110011101.list := by
  exact edge_identity (B := (2:ℤ)^271) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110011101 : Branch 1 (-411761639/2000000 : ℚ) vp000011001110 := by
  apply branch_checked idp0000110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-411761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-412761639/1000000 : ℚ) by norm_num]
  exact coverp0000110011101
theorem coverp000011001110 : Covers (-411761639/2000000 : ℚ) vp000011001110 := join_branches bp0000110011100 bp0000110011101
private noncomputable def vp00001100111_0 : Blocks := edgeBlocks% "full/vectors/00001100111-V-0000.bin"
private noncomputable def vp00001100111_1 : Blocks := edgeBlocks% "full/vectors/00001100111-V-0001.bin"
noncomputable def vp00001100111 : Blocks := (Blocks.join vp00001100111_0 vp00001100111_1)
private theorem bp000011001110 : Branch 0 (-411761639/4000000 : ℚ) vp00001100111 := by
  apply branch_left_normalized (c:=vp000011001110) (k:=0) (m:=118) (by decide +kernel)
  rw [show 2*(-411761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-411761639/2000000 : ℚ) by norm_num]
  exact coverp000011001110
private noncomputable def ep000011001111_0 : Blocks := edgeBlocks% "full/vectors/000011001111-E-0000.bin"
private noncomputable def ep000011001111_1 : Blocks := edgeBlocks% "full/vectors/000011001111-E-0001.bin"
noncomputable def ep000011001111 : Blocks := (Blocks.join ep000011001111_0 ep000011001111_1)
private theorem idp000011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001100111.list =
    C ((2:ℤ)^228) * horner X vp000011001111.list + horner X ep000011001111.list := by
  exact edge_identity (B := (2:ℤ)^419) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011001111 : Branch 1 (-411761639/4000000 : ℚ) vp00001100111 := by
  apply branch_checked idp000011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-411761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-413761639/2000000 : ℚ) by norm_num]
  exact coverp000011001111
theorem coverp00001100111 : Covers (-411761639/4000000 : ℚ) vp00001100111 := join_branches bp000011001110 bp000011001111
private noncomputable def vp00001100110111_0 : Blocks := edgeBlocks% "full/vectors/00001100110111-V-0000.bin"
noncomputable def vp00001100110111 : Blocks := vp00001100110111_0
theorem coverp00001100110111 : Covers (-411261639/500000 : ℚ) vp00001100110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100110110_0 : Blocks := edgeBlocks% "full/vectors/00001100110110-V-0000.bin"
noncomputable def vp00001100110110 : Blocks := vp00001100110110_0
theorem coverp00001100110110 : Covers (-410761639/500000 : ℚ) vp00001100110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110011011_0 : Blocks := edgeBlocks% "full/vectors/0000110011011-V-0000.bin"
noncomputable def vp0000110011011 : Blocks := vp0000110011011_0
private theorem bp00001100110110 : Branch 0 (-410761639/1000000 : ℚ) vp0000110011011 := by
  apply branch_left_normalized (c:=vp00001100110110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-410761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-410761639/500000 : ℚ) by norm_num]
  exact coverp00001100110110
private noncomputable def ep00001100110111_0 : Blocks := edgeBlocks% "full/vectors/00001100110111-E-0000.bin"
noncomputable def ep00001100110111 : Blocks := ep00001100110111_0
private theorem idp00001100110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110011011.list =
    C ((2:ℤ)^73) * horner X vp00001100110111.list + horner X ep00001100110111.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100110111 : Branch 1 (-410761639/1000000 : ℚ) vp0000110011011 := by
  apply branch_checked idp00001100110111 (by positivity) (by decide +kernel)
  rw [show 2*(-410761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-411261639/500000 : ℚ) by norm_num]
  exact coverp00001100110111
theorem coverp0000110011011 : Covers (-410761639/1000000 : ℚ) vp0000110011011 := join_branches bp00001100110110 bp00001100110111
private noncomputable def vp00001100110101_0 : Blocks := edgeBlocks% "full/vectors/00001100110101-V-0000.bin"
noncomputable def vp00001100110101 : Blocks := vp00001100110101_0
theorem coverp00001100110101 : Covers (-410261639/500000 : ℚ) vp00001100110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100110100_0 : Blocks := edgeBlocks% "full/vectors/00001100110100-V-0000.bin"
noncomputable def vp00001100110100 : Blocks := vp00001100110100_0
theorem coverp00001100110100 : Covers (-409761639/500000 : ℚ) vp00001100110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110011010_0 : Blocks := edgeBlocks% "full/vectors/0000110011010-V-0000.bin"
noncomputable def vp0000110011010 : Blocks := vp0000110011010_0
private theorem bp00001100110100 : Branch 0 (-409761639/1000000 : ℚ) vp0000110011010 := by
  apply branch_left_normalized (c:=vp00001100110100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-409761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-409761639/500000 : ℚ) by norm_num]
  exact coverp00001100110100
private noncomputable def ep00001100110101_0 : Blocks := edgeBlocks% "full/vectors/00001100110101-E-0000.bin"
noncomputable def ep00001100110101 : Blocks := ep00001100110101_0
private theorem idp00001100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110011010.list =
    C ((2:ℤ)^73) * horner X vp00001100110101.list + horner X ep00001100110101.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100110101 : Branch 1 (-409761639/1000000 : ℚ) vp0000110011010 := by
  apply branch_checked idp00001100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-409761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-410261639/500000 : ℚ) by norm_num]
  exact coverp00001100110101
theorem coverp0000110011010 : Covers (-409761639/1000000 : ℚ) vp0000110011010 := join_branches bp00001100110100 bp00001100110101
private noncomputable def vp000011001101_0 : Blocks := edgeBlocks% "full/vectors/000011001101-V-0000.bin"
noncomputable def vp000011001101 : Blocks := vp000011001101_0
private theorem bp0000110011010 : Branch 0 (-409761639/2000000 : ℚ) vp000011001101 := by
  apply branch_left_normalized (c:=vp0000110011010) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-409761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-409761639/1000000 : ℚ) by norm_num]
  exact coverp0000110011010
private noncomputable def ep0000110011011_0 : Blocks := edgeBlocks% "full/vectors/0000110011011-E-0000.bin"
noncomputable def ep0000110011011 : Blocks := ep0000110011011_0
private theorem idp0000110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011001101.list =
    C ((2:ℤ)^126) * horner X vp0000110011011.list + horner X ep0000110011011.list := by
  exact edge_identity (B := (2:ℤ)^274) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110011011 : Branch 1 (-409761639/2000000 : ℚ) vp000011001101 := by
  apply branch_checked idp0000110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-409761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-410761639/1000000 : ℚ) by norm_num]
  exact coverp0000110011011
theorem coverp000011001101 : Covers (-409761639/2000000 : ℚ) vp000011001101 := join_branches bp0000110011010 bp0000110011011
private noncomputable def vp00001100110011_0 : Blocks := edgeBlocks% "full/vectors/00001100110011-V-0000.bin"
noncomputable def vp00001100110011 : Blocks := vp00001100110011_0
theorem coverp00001100110011 : Covers (-409261639/500000 : ℚ) vp00001100110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100110010_0 : Blocks := edgeBlocks% "full/vectors/00001100110010-V-0000.bin"
noncomputable def vp00001100110010 : Blocks := vp00001100110010_0
theorem coverp00001100110010 : Covers (-408761639/500000 : ℚ) vp00001100110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110011001_0 : Blocks := edgeBlocks% "full/vectors/0000110011001-V-0000.bin"
noncomputable def vp0000110011001 : Blocks := vp0000110011001_0
private theorem bp00001100110010 : Branch 0 (-408761639/1000000 : ℚ) vp0000110011001 := by
  apply branch_left_normalized (c:=vp00001100110010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-408761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-408761639/500000 : ℚ) by norm_num]
  exact coverp00001100110010
private noncomputable def ep00001100110011_0 : Blocks := edgeBlocks% "full/vectors/00001100110011-E-0000.bin"
noncomputable def ep00001100110011 : Blocks := ep00001100110011_0
private theorem idp00001100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110011001.list =
    C ((2:ℤ)^72) * horner X vp00001100110011.list + horner X ep00001100110011.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100110011 : Branch 1 (-408761639/1000000 : ℚ) vp0000110011001 := by
  apply branch_checked idp00001100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-408761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-409261639/500000 : ℚ) by norm_num]
  exact coverp00001100110011
theorem coverp0000110011001 : Covers (-408761639/1000000 : ℚ) vp0000110011001 := join_branches bp00001100110010 bp00001100110011
private noncomputable def vp00001100110001_0 : Blocks := edgeBlocks% "full/vectors/00001100110001-V-0000.bin"
noncomputable def vp00001100110001 : Blocks := vp00001100110001_0
theorem coverp00001100110001 : Covers (-408261639/500000 : ℚ) vp00001100110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100110000_0 : Blocks := edgeBlocks% "full/vectors/00001100110000-V-0000.bin"
noncomputable def vp00001100110000 : Blocks := vp00001100110000_0
theorem coverp00001100110000 : Covers (-407761639/500000 : ℚ) vp00001100110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110011000_0 : Blocks := edgeBlocks% "full/vectors/0000110011000-V-0000.bin"
noncomputable def vp0000110011000 : Blocks := vp0000110011000_0
private theorem bp00001100110000 : Branch 0 (-407761639/1000000 : ℚ) vp0000110011000 := by
  apply branch_left_normalized (c:=vp00001100110000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-407761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-407761639/500000 : ℚ) by norm_num]
  exact coverp00001100110000
private noncomputable def ep00001100110001_0 : Blocks := edgeBlocks% "full/vectors/00001100110001-E-0000.bin"
noncomputable def ep00001100110001 : Blocks := ep00001100110001_0
private theorem idp00001100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110011000.list =
    C ((2:ℤ)^73) * horner X vp00001100110001.list + horner X ep00001100110001.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100110001 : Branch 1 (-407761639/1000000 : ℚ) vp0000110011000 := by
  apply branch_checked idp00001100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-407761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-408261639/500000 : ℚ) by norm_num]
  exact coverp00001100110001
theorem coverp0000110011000 : Covers (-407761639/1000000 : ℚ) vp0000110011000 := join_branches bp00001100110000 bp00001100110001
private noncomputable def vp000011001100_0 : Blocks := edgeBlocks% "full/vectors/000011001100-V-0000.bin"
noncomputable def vp000011001100 : Blocks := vp000011001100_0
private theorem bp0000110011000 : Branch 0 (-407761639/2000000 : ℚ) vp000011001100 := by
  apply branch_left_normalized (c:=vp0000110011000) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-407761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-407761639/1000000 : ℚ) by norm_num]
  exact coverp0000110011000
private noncomputable def ep0000110011001_0 : Blocks := edgeBlocks% "full/vectors/0000110011001-E-0000.bin"
noncomputable def ep0000110011001 : Blocks := ep0000110011001_0
private theorem idp0000110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011001100.list =
    C ((2:ℤ)^126) * horner X vp0000110011001.list + horner X ep0000110011001.list := by
  exact edge_identity (B := (2:ℤ)^273) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110011001 : Branch 1 (-407761639/2000000 : ℚ) vp000011001100 := by
  apply branch_checked idp0000110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-407761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-408761639/1000000 : ℚ) by norm_num]
  exact coverp0000110011001
theorem coverp000011001100 : Covers (-407761639/2000000 : ℚ) vp000011001100 := join_branches bp0000110011000 bp0000110011001
private noncomputable def vp00001100110_0 : Blocks := edgeBlocks% "full/vectors/00001100110-V-0000.bin"
private noncomputable def vp00001100110_1 : Blocks := edgeBlocks% "full/vectors/00001100110-V-0001.bin"
noncomputable def vp00001100110 : Blocks := (Blocks.join vp00001100110_0 vp00001100110_1)
private theorem bp000011001100 : Branch 0 (-407761639/4000000 : ℚ) vp00001100110 := by
  apply branch_left_normalized (c:=vp000011001100) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-407761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-407761639/2000000 : ℚ) by norm_num]
  exact coverp000011001100
private noncomputable def ep000011001101_0 : Blocks := edgeBlocks% "full/vectors/000011001101-E-0000.bin"
private noncomputable def ep000011001101_1 : Blocks := edgeBlocks% "full/vectors/000011001101-E-0001.bin"
noncomputable def ep000011001101 : Blocks := (Blocks.join ep000011001101_0 ep000011001101_1)
private theorem idp000011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001100110.list =
    C ((2:ℤ)^228) * horner X vp000011001101.list + horner X ep000011001101.list := by
  exact edge_identity (B := (2:ℤ)^422) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011001101 : Branch 1 (-407761639/4000000 : ℚ) vp00001100110 := by
  apply branch_checked idp000011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-407761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-409761639/2000000 : ℚ) by norm_num]
  exact coverp000011001101
theorem coverp00001100110 : Covers (-407761639/4000000 : ℚ) vp00001100110 := join_branches bp000011001100 bp000011001101
private noncomputable def vp0000110011_0 : Blocks := edgeBlocks% "full/vectors/0000110011-V-0000.bin"
private noncomputable def vp0000110011_1 : Blocks := edgeBlocks% "full/vectors/0000110011-V-0001.bin"
private noncomputable def vp0000110011_2 : Blocks := edgeBlocks% "full/vectors/0000110011-V-0002.bin"
private noncomputable def vp0000110011_3 : Blocks := edgeBlocks% "full/vectors/0000110011-V-0003.bin"
noncomputable def vp0000110011 : Blocks := (Blocks.join (Blocks.join vp0000110011_0 vp0000110011_1) (Blocks.join vp0000110011_2 vp0000110011_3))
private theorem bp00001100110 : Branch 0 (-407761639/8000000 : ℚ) vp0000110011 := by
  apply branch_left_normalized (c:=vp00001100110) (k:=0) (m:=216) (by decide +kernel)
  rw [show 2*(-407761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-407761639/4000000 : ℚ) by norm_num]
  exact coverp00001100110
private noncomputable def ep00001100111_0 : Blocks := edgeBlocks% "full/vectors/00001100111-E-0000.bin"
private noncomputable def ep00001100111_1 : Blocks := edgeBlocks% "full/vectors/00001100111-E-0001.bin"
private noncomputable def ep00001100111_2 : Blocks := edgeBlocks% "full/vectors/00001100111-E-0002.bin"
private noncomputable def ep00001100111_3 : Blocks := edgeBlocks% "full/vectors/00001100111-E-0003.bin"
noncomputable def ep00001100111 : Blocks := (Blocks.join (Blocks.join ep00001100111_0 ep00001100111_1) (Blocks.join ep00001100111_2 ep00001100111_3))
private theorem idp00001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110011.list =
    C ((2:ℤ)^434) * horner X vp00001100111.list + horner X ep00001100111.list := by
  exact edge_identity (B := (2:ℤ)^718) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100111 : Branch 1 (-407761639/8000000 : ℚ) vp0000110011 := by
  apply branch_checked idp00001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-407761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-411761639/4000000 : ℚ) by norm_num]
  exact coverp00001100111
theorem coverp0000110011 : Covers (-407761639/8000000 : ℚ) vp0000110011 := join_branches bp00001100110 bp00001100111
private noncomputable def vp00001100101111_0 : Blocks := edgeBlocks% "full/vectors/00001100101111-V-0000.bin"
noncomputable def vp00001100101111 : Blocks := vp00001100101111_0
theorem coverp00001100101111 : Covers (-407261639/500000 : ℚ) vp00001100101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100101110_0 : Blocks := edgeBlocks% "full/vectors/00001100101110-V-0000.bin"
noncomputable def vp00001100101110 : Blocks := vp00001100101110_0
theorem coverp00001100101110 : Covers (-406761639/500000 : ℚ) vp00001100101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110010111_0 : Blocks := edgeBlocks% "full/vectors/0000110010111-V-0000.bin"
noncomputable def vp0000110010111 : Blocks := vp0000110010111_0
private theorem bp00001100101110 : Branch 0 (-406761639/1000000 : ℚ) vp0000110010111 := by
  apply branch_left_normalized (c:=vp00001100101110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-406761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-406761639/500000 : ℚ) by norm_num]
  exact coverp00001100101110
private noncomputable def ep00001100101111_0 : Blocks := edgeBlocks% "full/vectors/00001100101111-E-0000.bin"
noncomputable def ep00001100101111 : Blocks := ep00001100101111_0
private theorem idp00001100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110010111.list =
    C ((2:ℤ)^73) * horner X vp00001100101111.list + horner X ep00001100101111.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100101111 : Branch 1 (-406761639/1000000 : ℚ) vp0000110010111 := by
  apply branch_checked idp00001100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-406761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-407261639/500000 : ℚ) by norm_num]
  exact coverp00001100101111
theorem coverp0000110010111 : Covers (-406761639/1000000 : ℚ) vp0000110010111 := join_branches bp00001100101110 bp00001100101111
private noncomputable def vp00001100101101_0 : Blocks := edgeBlocks% "full/vectors/00001100101101-V-0000.bin"
noncomputable def vp00001100101101 : Blocks := vp00001100101101_0
theorem coverp00001100101101 : Covers (-406261639/500000 : ℚ) vp00001100101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100101100_0 : Blocks := edgeBlocks% "full/vectors/00001100101100-V-0000.bin"
noncomputable def vp00001100101100 : Blocks := vp00001100101100_0
theorem coverp00001100101100 : Covers (-405761639/500000 : ℚ) vp00001100101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110010110_0 : Blocks := edgeBlocks% "full/vectors/0000110010110-V-0000.bin"
noncomputable def vp0000110010110 : Blocks := vp0000110010110_0
private theorem bp00001100101100 : Branch 0 (-405761639/1000000 : ℚ) vp0000110010110 := by
  apply branch_left_normalized (c:=vp00001100101100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-405761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-405761639/500000 : ℚ) by norm_num]
  exact coverp00001100101100
private noncomputable def ep00001100101101_0 : Blocks := edgeBlocks% "full/vectors/00001100101101-E-0000.bin"
noncomputable def ep00001100101101 : Blocks := ep00001100101101_0
private theorem idp00001100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110010110.list =
    C ((2:ℤ)^73) * horner X vp00001100101101.list + horner X ep00001100101101.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100101101 : Branch 1 (-405761639/1000000 : ℚ) vp0000110010110 := by
  apply branch_checked idp00001100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-405761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-406261639/500000 : ℚ) by norm_num]
  exact coverp00001100101101
theorem coverp0000110010110 : Covers (-405761639/1000000 : ℚ) vp0000110010110 := join_branches bp00001100101100 bp00001100101101
private noncomputable def vp000011001011_0 : Blocks := edgeBlocks% "full/vectors/000011001011-V-0000.bin"
noncomputable def vp000011001011 : Blocks := vp000011001011_0
private theorem bp0000110010110 : Branch 0 (-405761639/2000000 : ℚ) vp000011001011 := by
  apply branch_left_normalized (c:=vp0000110010110) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-405761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-405761639/1000000 : ℚ) by norm_num]
  exact coverp0000110010110
private noncomputable def ep0000110010111_0 : Blocks := edgeBlocks% "full/vectors/0000110010111-E-0000.bin"
noncomputable def ep0000110010111 : Blocks := ep0000110010111_0
private theorem idp0000110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011001011.list =
    C ((2:ℤ)^126) * horner X vp0000110010111.list + horner X ep0000110010111.list := by
  exact edge_identity (B := (2:ℤ)^274) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110010111 : Branch 1 (-405761639/2000000 : ℚ) vp000011001011 := by
  apply branch_checked idp0000110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-405761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-406761639/1000000 : ℚ) by norm_num]
  exact coverp0000110010111
theorem coverp000011001011 : Covers (-405761639/2000000 : ℚ) vp000011001011 := join_branches bp0000110010110 bp0000110010111
private noncomputable def vp00001100101011_0 : Blocks := edgeBlocks% "full/vectors/00001100101011-V-0000.bin"
noncomputable def vp00001100101011 : Blocks := vp00001100101011_0
theorem coverp00001100101011 : Covers (-405261639/500000 : ℚ) vp00001100101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100101010_0 : Blocks := edgeBlocks% "full/vectors/00001100101010-V-0000.bin"
noncomputable def vp00001100101010 : Blocks := vp00001100101010_0
theorem coverp00001100101010 : Covers (-404761639/500000 : ℚ) vp00001100101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110010101_0 : Blocks := edgeBlocks% "full/vectors/0000110010101-V-0000.bin"
noncomputable def vp0000110010101 : Blocks := vp0000110010101_0
private theorem bp00001100101010 : Branch 0 (-404761639/1000000 : ℚ) vp0000110010101 := by
  apply branch_left_normalized (c:=vp00001100101010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-404761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-404761639/500000 : ℚ) by norm_num]
  exact coverp00001100101010
private noncomputable def ep00001100101011_0 : Blocks := edgeBlocks% "full/vectors/00001100101011-E-0000.bin"
noncomputable def ep00001100101011 : Blocks := ep00001100101011_0
private theorem idp00001100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110010101.list =
    C ((2:ℤ)^73) * horner X vp00001100101011.list + horner X ep00001100101011.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100101011 : Branch 1 (-404761639/1000000 : ℚ) vp0000110010101 := by
  apply branch_checked idp00001100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-404761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-405261639/500000 : ℚ) by norm_num]
  exact coverp00001100101011
theorem coverp0000110010101 : Covers (-404761639/1000000 : ℚ) vp0000110010101 := join_branches bp00001100101010 bp00001100101011
private noncomputable def vp00001100101001_0 : Blocks := edgeBlocks% "full/vectors/00001100101001-V-0000.bin"
noncomputable def vp00001100101001 : Blocks := vp00001100101001_0
theorem coverp00001100101001 : Covers (-404261639/500000 : ℚ) vp00001100101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100101000_0 : Blocks := edgeBlocks% "full/vectors/00001100101000-V-0000.bin"
noncomputable def vp00001100101000 : Blocks := vp00001100101000_0
theorem coverp00001100101000 : Covers (-403761639/500000 : ℚ) vp00001100101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110010100_0 : Blocks := edgeBlocks% "full/vectors/0000110010100-V-0000.bin"
noncomputable def vp0000110010100 : Blocks := vp0000110010100_0
private theorem bp00001100101000 : Branch 0 (-403761639/1000000 : ℚ) vp0000110010100 := by
  apply branch_left_normalized (c:=vp00001100101000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-403761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-403761639/500000 : ℚ) by norm_num]
  exact coverp00001100101000
private noncomputable def ep00001100101001_0 : Blocks := edgeBlocks% "full/vectors/00001100101001-E-0000.bin"
noncomputable def ep00001100101001 : Blocks := ep00001100101001_0
private theorem idp00001100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110010100.list =
    C ((2:ℤ)^72) * horner X vp00001100101001.list + horner X ep00001100101001.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100101001 : Branch 1 (-403761639/1000000 : ℚ) vp0000110010100 := by
  apply branch_checked idp00001100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-403761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-404261639/500000 : ℚ) by norm_num]
  exact coverp00001100101001
theorem coverp0000110010100 : Covers (-403761639/1000000 : ℚ) vp0000110010100 := join_branches bp00001100101000 bp00001100101001
private noncomputable def vp000011001010_0 : Blocks := edgeBlocks% "full/vectors/000011001010-V-0000.bin"
noncomputable def vp000011001010 : Blocks := vp000011001010_0
private theorem bp0000110010100 : Branch 0 (-403761639/2000000 : ℚ) vp000011001010 := by
  apply branch_left_normalized (c:=vp0000110010100) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-403761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-403761639/1000000 : ℚ) by norm_num]
  exact coverp0000110010100
private noncomputable def ep0000110010101_0 : Blocks := edgeBlocks% "full/vectors/0000110010101-E-0000.bin"
noncomputable def ep0000110010101 : Blocks := ep0000110010101_0
private theorem idp0000110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011001010.list =
    C ((2:ℤ)^125) * horner X vp0000110010101.list + horner X ep0000110010101.list := by
  exact edge_identity (B := (2:ℤ)^273) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110010101 : Branch 1 (-403761639/2000000 : ℚ) vp000011001010 := by
  apply branch_checked idp0000110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-403761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-404761639/1000000 : ℚ) by norm_num]
  exact coverp0000110010101
theorem coverp000011001010 : Covers (-403761639/2000000 : ℚ) vp000011001010 := join_branches bp0000110010100 bp0000110010101
private noncomputable def vp00001100101_0 : Blocks := edgeBlocks% "full/vectors/00001100101-V-0000.bin"
private noncomputable def vp00001100101_1 : Blocks := edgeBlocks% "full/vectors/00001100101-V-0001.bin"
noncomputable def vp00001100101 : Blocks := (Blocks.join vp00001100101_0 vp00001100101_1)
private theorem bp000011001010 : Branch 0 (-403761639/4000000 : ℚ) vp00001100101 := by
  apply branch_left_normalized (c:=vp000011001010) (k:=0) (m:=119) (by decide +kernel)
  rw [show 2*(-403761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-403761639/2000000 : ℚ) by norm_num]
  exact coverp000011001010
private noncomputable def ep000011001011_0 : Blocks := edgeBlocks% "full/vectors/000011001011-E-0000.bin"
private noncomputable def ep000011001011_1 : Blocks := edgeBlocks% "full/vectors/000011001011-E-0001.bin"
noncomputable def ep000011001011 : Blocks := (Blocks.join ep000011001011_0 ep000011001011_1)
private theorem idp000011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001100101.list =
    C ((2:ℤ)^230) * horner X vp000011001011.list + horner X ep000011001011.list := by
  exact edge_identity (B := (2:ℤ)^424) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011001011 : Branch 1 (-403761639/4000000 : ℚ) vp00001100101 := by
  apply branch_checked idp000011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-403761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-405761639/2000000 : ℚ) by norm_num]
  exact coverp000011001011
theorem coverp00001100101 : Covers (-403761639/4000000 : ℚ) vp00001100101 := join_branches bp000011001010 bp000011001011
private noncomputable def vp00001100100111_0 : Blocks := edgeBlocks% "full/vectors/00001100100111-V-0000.bin"
noncomputable def vp00001100100111 : Blocks := vp00001100100111_0
theorem coverp00001100100111 : Covers (-403261639/500000 : ℚ) vp00001100100111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100100110_0 : Blocks := edgeBlocks% "full/vectors/00001100100110-V-0000.bin"
noncomputable def vp00001100100110 : Blocks := vp00001100100110_0
theorem coverp00001100100110 : Covers (-402761639/500000 : ℚ) vp00001100100110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110010011_0 : Blocks := edgeBlocks% "full/vectors/0000110010011-V-0000.bin"
noncomputable def vp0000110010011 : Blocks := vp0000110010011_0
private theorem bp00001100100110 : Branch 0 (-402761639/1000000 : ℚ) vp0000110010011 := by
  apply branch_left_normalized (c:=vp00001100100110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-402761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-402761639/500000 : ℚ) by norm_num]
  exact coverp00001100100110
private noncomputable def ep00001100100111_0 : Blocks := edgeBlocks% "full/vectors/00001100100111-E-0000.bin"
noncomputable def ep00001100100111 : Blocks := ep00001100100111_0
private theorem idp00001100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110010011.list =
    C ((2:ℤ)^73) * horner X vp00001100100111.list + horner X ep00001100100111.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100100111 : Branch 1 (-402761639/1000000 : ℚ) vp0000110010011 := by
  apply branch_checked idp00001100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-402761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-403261639/500000 : ℚ) by norm_num]
  exact coverp00001100100111
theorem coverp0000110010011 : Covers (-402761639/1000000 : ℚ) vp0000110010011 := join_branches bp00001100100110 bp00001100100111
private noncomputable def vp00001100100101_0 : Blocks := edgeBlocks% "full/vectors/00001100100101-V-0000.bin"
noncomputable def vp00001100100101 : Blocks := vp00001100100101_0
theorem coverp00001100100101 : Covers (-402261639/500000 : ℚ) vp00001100100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100100100_0 : Blocks := edgeBlocks% "full/vectors/00001100100100-V-0000.bin"
noncomputable def vp00001100100100 : Blocks := vp00001100100100_0
theorem coverp00001100100100 : Covers (-401761639/500000 : ℚ) vp00001100100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110010010_0 : Blocks := edgeBlocks% "full/vectors/0000110010010-V-0000.bin"
noncomputable def vp0000110010010 : Blocks := vp0000110010010_0
private theorem bp00001100100100 : Branch 0 (-401761639/1000000 : ℚ) vp0000110010010 := by
  apply branch_left_normalized (c:=vp00001100100100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-401761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-401761639/500000 : ℚ) by norm_num]
  exact coverp00001100100100
private noncomputable def ep00001100100101_0 : Blocks := edgeBlocks% "full/vectors/00001100100101-E-0000.bin"
noncomputable def ep00001100100101 : Blocks := ep00001100100101_0
private theorem idp00001100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110010010.list =
    C ((2:ℤ)^72) * horner X vp00001100100101.list + horner X ep00001100100101.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100100101 : Branch 1 (-401761639/1000000 : ℚ) vp0000110010010 := by
  apply branch_checked idp00001100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-401761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-402261639/500000 : ℚ) by norm_num]
  exact coverp00001100100101
theorem coverp0000110010010 : Covers (-401761639/1000000 : ℚ) vp0000110010010 := join_branches bp00001100100100 bp00001100100101
private noncomputable def vp000011001001_0 : Blocks := edgeBlocks% "full/vectors/000011001001-V-0000.bin"
noncomputable def vp000011001001 : Blocks := vp000011001001_0
private theorem bp0000110010010 : Branch 0 (-401761639/2000000 : ℚ) vp000011001001 := by
  apply branch_left_normalized (c:=vp0000110010010) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-401761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-401761639/1000000 : ℚ) by norm_num]
  exact coverp0000110010010
private noncomputable def ep0000110010011_0 : Blocks := edgeBlocks% "full/vectors/0000110010011-E-0000.bin"
noncomputable def ep0000110010011 : Blocks := ep0000110010011_0
private theorem idp0000110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011001001.list =
    C ((2:ℤ)^125) * horner X vp0000110010011.list + horner X ep0000110010011.list := by
  exact edge_identity (B := (2:ℤ)^273) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110010011 : Branch 1 (-401761639/2000000 : ℚ) vp000011001001 := by
  apply branch_checked idp0000110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-401761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-402761639/1000000 : ℚ) by norm_num]
  exact coverp0000110010011
theorem coverp000011001001 : Covers (-401761639/2000000 : ℚ) vp000011001001 := join_branches bp0000110010010 bp0000110010011
private noncomputable def vp00001100100011_0 : Blocks := edgeBlocks% "full/vectors/00001100100011-V-0000.bin"
noncomputable def vp00001100100011 : Blocks := vp00001100100011_0
theorem coverp00001100100011 : Covers (-401261639/500000 : ℚ) vp00001100100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100100010_0 : Blocks := edgeBlocks% "full/vectors/00001100100010-V-0000.bin"
noncomputable def vp00001100100010 : Blocks := vp00001100100010_0
theorem coverp00001100100010 : Covers (-400761639/500000 : ℚ) vp00001100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110010001_0 : Blocks := edgeBlocks% "full/vectors/0000110010001-V-0000.bin"
noncomputable def vp0000110010001 : Blocks := vp0000110010001_0
private theorem bp00001100100010 : Branch 0 (-400761639/1000000 : ℚ) vp0000110010001 := by
  apply branch_left_normalized (c:=vp00001100100010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-400761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-400761639/500000 : ℚ) by norm_num]
  exact coverp00001100100010
private noncomputable def ep00001100100011_0 : Blocks := edgeBlocks% "full/vectors/00001100100011-E-0000.bin"
noncomputable def ep00001100100011 : Blocks := ep00001100100011_0
private theorem idp00001100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110010001.list =
    C ((2:ℤ)^74) * horner X vp00001100100011.list + horner X ep00001100100011.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100100011 : Branch 1 (-400761639/1000000 : ℚ) vp0000110010001 := by
  apply branch_checked idp00001100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-400761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-401261639/500000 : ℚ) by norm_num]
  exact coverp00001100100011
theorem coverp0000110010001 : Covers (-400761639/1000000 : ℚ) vp0000110010001 := join_branches bp00001100100010 bp00001100100011
private noncomputable def vp00001100100001_0 : Blocks := edgeBlocks% "full/vectors/00001100100001-V-0000.bin"
noncomputable def vp00001100100001 : Blocks := vp00001100100001_0
theorem coverp00001100100001 : Covers (-400261639/500000 : ℚ) vp00001100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100100000_0 : Blocks := edgeBlocks% "full/vectors/00001100100000-V-0000.bin"
noncomputable def vp00001100100000 : Blocks := vp00001100100000_0
theorem coverp00001100100000 : Covers (-399761639/500000 : ℚ) vp00001100100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110010000_0 : Blocks := edgeBlocks% "full/vectors/0000110010000-V-0000.bin"
noncomputable def vp0000110010000 : Blocks := vp0000110010000_0
private theorem bp00001100100000 : Branch 0 (-399761639/1000000 : ℚ) vp0000110010000 := by
  apply branch_left_normalized (c:=vp00001100100000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-399761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-399761639/500000 : ℚ) by norm_num]
  exact coverp00001100100000
private noncomputable def ep00001100100001_0 : Blocks := edgeBlocks% "full/vectors/00001100100001-E-0000.bin"
noncomputable def ep00001100100001 : Blocks := ep00001100100001_0
private theorem idp00001100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110010000.list =
    C ((2:ℤ)^73) * horner X vp00001100100001.list + horner X ep00001100100001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100100001 : Branch 1 (-399761639/1000000 : ℚ) vp0000110010000 := by
  apply branch_checked idp00001100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-399761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-400261639/500000 : ℚ) by norm_num]
  exact coverp00001100100001
theorem coverp0000110010000 : Covers (-399761639/1000000 : ℚ) vp0000110010000 := join_branches bp00001100100000 bp00001100100001
private noncomputable def vp000011001000_0 : Blocks := edgeBlocks% "full/vectors/000011001000-V-0000.bin"
noncomputable def vp000011001000 : Blocks := vp000011001000_0
private theorem bp0000110010000 : Branch 0 (-399761639/2000000 : ℚ) vp000011001000 := by
  apply branch_left_normalized (c:=vp0000110010000) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-399761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-399761639/1000000 : ℚ) by norm_num]
  exact coverp0000110010000
private noncomputable def ep0000110010001_0 : Blocks := edgeBlocks% "full/vectors/0000110010001-E-0000.bin"
noncomputable def ep0000110010001 : Blocks := ep0000110010001_0
private theorem idp0000110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011001000.list =
    C ((2:ℤ)^127) * horner X vp0000110010001.list + horner X ep0000110010001.list := by
  exact edge_identity (B := (2:ℤ)^276) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110010001 : Branch 1 (-399761639/2000000 : ℚ) vp000011001000 := by
  apply branch_checked idp0000110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-399761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-400761639/1000000 : ℚ) by norm_num]
  exact coverp0000110010001
theorem coverp000011001000 : Covers (-399761639/2000000 : ℚ) vp000011001000 := join_branches bp0000110010000 bp0000110010001
private noncomputable def vp00001100100_0 : Blocks := edgeBlocks% "full/vectors/00001100100-V-0000.bin"
private noncomputable def vp00001100100_1 : Blocks := edgeBlocks% "full/vectors/00001100100-V-0001.bin"
noncomputable def vp00001100100 : Blocks := (Blocks.join vp00001100100_0 vp00001100100_1)
private theorem bp000011001000 : Branch 0 (-399761639/4000000 : ℚ) vp00001100100 := by
  apply branch_left_normalized (c:=vp000011001000) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-399761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-399761639/2000000 : ℚ) by norm_num]
  exact coverp000011001000
private noncomputable def ep000011001001_0 : Blocks := edgeBlocks% "full/vectors/000011001001-E-0000.bin"
private noncomputable def ep000011001001_1 : Blocks := edgeBlocks% "full/vectors/000011001001-E-0001.bin"
noncomputable def ep000011001001 : Blocks := (Blocks.join ep000011001001_0 ep000011001001_1)
private theorem idp000011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001100100.list =
    C ((2:ℤ)^233) * horner X vp000011001001.list + horner X ep000011001001.list := by
  exact edge_identity (B := (2:ℤ)^427) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011001001 : Branch 1 (-399761639/4000000 : ℚ) vp00001100100 := by
  apply branch_checked idp000011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-399761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-401761639/2000000 : ℚ) by norm_num]
  exact coverp000011001001
theorem coverp00001100100 : Covers (-399761639/4000000 : ℚ) vp00001100100 := join_branches bp000011001000 bp000011001001
private noncomputable def vp0000110010_0 : Blocks := edgeBlocks% "full/vectors/0000110010-V-0000.bin"
private noncomputable def vp0000110010_1 : Blocks := edgeBlocks% "full/vectors/0000110010-V-0001.bin"
private noncomputable def vp0000110010_2 : Blocks := edgeBlocks% "full/vectors/0000110010-V-0002.bin"
private noncomputable def vp0000110010_3 : Blocks := edgeBlocks% "full/vectors/0000110010-V-0003.bin"
noncomputable def vp0000110010 : Blocks := (Blocks.join (Blocks.join vp0000110010_0 vp0000110010_1) (Blocks.join vp0000110010_2 vp0000110010_3))
private theorem bp00001100100 : Branch 0 (-399761639/8000000 : ℚ) vp0000110010 := by
  apply branch_left_normalized (c:=vp00001100100) (k:=0) (m:=219) (by decide +kernel)
  rw [show 2*(-399761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-399761639/4000000 : ℚ) by norm_num]
  exact coverp00001100100
private noncomputable def ep00001100101_0 : Blocks := edgeBlocks% "full/vectors/00001100101-E-0000.bin"
private noncomputable def ep00001100101_1 : Blocks := edgeBlocks% "full/vectors/00001100101-E-0001.bin"
private noncomputable def ep00001100101_2 : Blocks := edgeBlocks% "full/vectors/00001100101-E-0002.bin"
private noncomputable def ep00001100101_3 : Blocks := edgeBlocks% "full/vectors/00001100101-E-0003.bin"
noncomputable def ep00001100101 : Blocks := (Blocks.join (Blocks.join ep00001100101_0 ep00001100101_1) (Blocks.join ep00001100101_2 ep00001100101_3))
private theorem idp00001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110010.list =
    C ((2:ℤ)^439) * horner X vp00001100101.list + horner X ep00001100101.list := by
  exact edge_identity (B := (2:ℤ)^726) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100101 : Branch 1 (-399761639/8000000 : ℚ) vp0000110010 := by
  apply branch_checked idp00001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-399761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-403761639/4000000 : ℚ) by norm_num]
  exact coverp00001100101
theorem coverp0000110010 : Covers (-399761639/8000000 : ℚ) vp0000110010 := join_branches bp00001100100 bp00001100101
private noncomputable def vp000011001_0 : Blocks := edgeBlocks% "full/vectors/000011001-V-0000.bin"
private noncomputable def vp000011001_1 : Blocks := edgeBlocks% "full/vectors/000011001-V-0001.bin"
private noncomputable def vp000011001_2 : Blocks := edgeBlocks% "full/vectors/000011001-V-0002.bin"
private noncomputable def vp000011001_3 : Blocks := edgeBlocks% "full/vectors/000011001-V-0003.bin"
private noncomputable def vp000011001_4 : Blocks := edgeBlocks% "full/vectors/000011001-V-0004.bin"
private noncomputable def vp000011001_5 : Blocks := edgeBlocks% "full/vectors/000011001-V-0005.bin"
private noncomputable def vp000011001_6 : Blocks := edgeBlocks% "full/vectors/000011001-V-0006.bin"
noncomputable def vp000011001 : Blocks := (Blocks.join (Blocks.join vp000011001_0 (Blocks.join vp000011001_1 vp000011001_2)) (Blocks.join (Blocks.join vp000011001_3 vp000011001_4) (Blocks.join vp000011001_5 vp000011001_6)))
private theorem bp0000110010 : Branch 0 (-399761639/16000000 : ℚ) vp000011001 := by
  apply branch_left_normalized (c:=vp0000110010) (k:=0) (m:=414) (by decide +kernel)
  rw [show 2*(-399761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-399761639/8000000 : ℚ) by norm_num]
  exact coverp0000110010
private noncomputable def ep0000110011_0 : Blocks := edgeBlocks% "full/vectors/0000110011-E-0000.bin"
private noncomputable def ep0000110011_1 : Blocks := edgeBlocks% "full/vectors/0000110011-E-0001.bin"
private noncomputable def ep0000110011_2 : Blocks := edgeBlocks% "full/vectors/0000110011-E-0002.bin"
private noncomputable def ep0000110011_3 : Blocks := edgeBlocks% "full/vectors/0000110011-E-0003.bin"
private noncomputable def ep0000110011_4 : Blocks := edgeBlocks% "full/vectors/0000110011-E-0004.bin"
private noncomputable def ep0000110011_5 : Blocks := edgeBlocks% "full/vectors/0000110011-E-0005.bin"
private noncomputable def ep0000110011_6 : Blocks := edgeBlocks% "full/vectors/0000110011-E-0006.bin"
noncomputable def ep0000110011 : Blocks := (Blocks.join (Blocks.join ep0000110011_0 (Blocks.join ep0000110011_1 ep0000110011_2)) (Blocks.join (Blocks.join ep0000110011_3 ep0000110011_4) (Blocks.join ep0000110011_5 ep0000110011_6)))
private theorem idp0000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011001.list =
    C ((2:ℤ)^849) * horner X vp0000110011.list + horner X ep0000110011.list := by
  exact edge_identity (B := (2:ℤ)^1320) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110011 : Branch 1 (-399761639/16000000 : ℚ) vp000011001 := by
  apply branch_checked idp0000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-399761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-407761639/8000000 : ℚ) by norm_num]
  exact coverp0000110011
theorem coverp000011001 : Covers (-399761639/16000000 : ℚ) vp000011001 := join_branches bp0000110010 bp0000110011
private noncomputable def vp00001100011111_0 : Blocks := edgeBlocks% "full/vectors/00001100011111-V-0000.bin"
noncomputable def vp00001100011111 : Blocks := vp00001100011111_0
theorem coverp00001100011111 : Covers (-399261639/500000 : ℚ) vp00001100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100011110_0 : Blocks := edgeBlocks% "full/vectors/00001100011110-V-0000.bin"
noncomputable def vp00001100011110 : Blocks := vp00001100011110_0
theorem coverp00001100011110 : Covers (-398761639/500000 : ℚ) vp00001100011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110001111_0 : Blocks := edgeBlocks% "full/vectors/0000110001111-V-0000.bin"
noncomputable def vp0000110001111 : Blocks := vp0000110001111_0
private theorem bp00001100011110 : Branch 0 (-398761639/1000000 : ℚ) vp0000110001111 := by
  apply branch_left_normalized (c:=vp00001100011110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-398761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-398761639/500000 : ℚ) by norm_num]
  exact coverp00001100011110
private noncomputable def ep00001100011111_0 : Blocks := edgeBlocks% "full/vectors/00001100011111-E-0000.bin"
noncomputable def ep00001100011111 : Blocks := ep00001100011111_0
private theorem idp00001100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110001111.list =
    C ((2:ℤ)^73) * horner X vp00001100011111.list + horner X ep00001100011111.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100011111 : Branch 1 (-398761639/1000000 : ℚ) vp0000110001111 := by
  apply branch_checked idp00001100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-398761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-399261639/500000 : ℚ) by norm_num]
  exact coverp00001100011111
theorem coverp0000110001111 : Covers (-398761639/1000000 : ℚ) vp0000110001111 := join_branches bp00001100011110 bp00001100011111
private noncomputable def vp00001100011101_0 : Blocks := edgeBlocks% "full/vectors/00001100011101-V-0000.bin"
noncomputable def vp00001100011101 : Blocks := vp00001100011101_0
theorem coverp00001100011101 : Covers (-398261639/500000 : ℚ) vp00001100011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100011100_0 : Blocks := edgeBlocks% "full/vectors/00001100011100-V-0000.bin"
noncomputable def vp00001100011100 : Blocks := vp00001100011100_0
theorem coverp00001100011100 : Covers (-397761639/500000 : ℚ) vp00001100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110001110_0 : Blocks := edgeBlocks% "full/vectors/0000110001110-V-0000.bin"
noncomputable def vp0000110001110 : Blocks := vp0000110001110_0
private theorem bp00001100011100 : Branch 0 (-397761639/1000000 : ℚ) vp0000110001110 := by
  apply branch_left_normalized (c:=vp00001100011100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-397761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-397761639/500000 : ℚ) by norm_num]
  exact coverp00001100011100
private noncomputable def ep00001100011101_0 : Blocks := edgeBlocks% "full/vectors/00001100011101-E-0000.bin"
noncomputable def ep00001100011101 : Blocks := ep00001100011101_0
private theorem idp00001100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110001110.list =
    C ((2:ℤ)^73) * horner X vp00001100011101.list + horner X ep00001100011101.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100011101 : Branch 1 (-397761639/1000000 : ℚ) vp0000110001110 := by
  apply branch_checked idp00001100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-397761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-398261639/500000 : ℚ) by norm_num]
  exact coverp00001100011101
theorem coverp0000110001110 : Covers (-397761639/1000000 : ℚ) vp0000110001110 := join_branches bp00001100011100 bp00001100011101
private noncomputable def vp000011000111_0 : Blocks := edgeBlocks% "full/vectors/000011000111-V-0000.bin"
noncomputable def vp000011000111 : Blocks := vp000011000111_0
private theorem bp0000110001110 : Branch 0 (-397761639/2000000 : ℚ) vp000011000111 := by
  apply branch_left_normalized (c:=vp0000110001110) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-397761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-397761639/1000000 : ℚ) by norm_num]
  exact coverp0000110001110
private noncomputable def ep0000110001111_0 : Blocks := edgeBlocks% "full/vectors/0000110001111-E-0000.bin"
noncomputable def ep0000110001111 : Blocks := ep0000110001111_0
private theorem idp0000110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011000111.list =
    C ((2:ℤ)^127) * horner X vp0000110001111.list + horner X ep0000110001111.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110001111 : Branch 1 (-397761639/2000000 : ℚ) vp000011000111 := by
  apply branch_checked idp0000110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-397761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-398761639/1000000 : ℚ) by norm_num]
  exact coverp0000110001111
theorem coverp000011000111 : Covers (-397761639/2000000 : ℚ) vp000011000111 := join_branches bp0000110001110 bp0000110001111
private noncomputable def vp00001100011011_0 : Blocks := edgeBlocks% "full/vectors/00001100011011-V-0000.bin"
noncomputable def vp00001100011011 : Blocks := vp00001100011011_0
theorem coverp00001100011011 : Covers (-397261639/500000 : ℚ) vp00001100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100011010_0 : Blocks := edgeBlocks% "full/vectors/00001100011010-V-0000.bin"
noncomputable def vp00001100011010 : Blocks := vp00001100011010_0
theorem coverp00001100011010 : Covers (-396761639/500000 : ℚ) vp00001100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110001101_0 : Blocks := edgeBlocks% "full/vectors/0000110001101-V-0000.bin"
noncomputable def vp0000110001101 : Blocks := vp0000110001101_0
private theorem bp00001100011010 : Branch 0 (-396761639/1000000 : ℚ) vp0000110001101 := by
  apply branch_left_normalized (c:=vp00001100011010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-396761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-396761639/500000 : ℚ) by norm_num]
  exact coverp00001100011010
private noncomputable def ep00001100011011_0 : Blocks := edgeBlocks% "full/vectors/00001100011011-E-0000.bin"
noncomputable def ep00001100011011 : Blocks := ep00001100011011_0
private theorem idp00001100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110001101.list =
    C ((2:ℤ)^74) * horner X vp00001100011011.list + horner X ep00001100011011.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100011011 : Branch 1 (-396761639/1000000 : ℚ) vp0000110001101 := by
  apply branch_checked idp00001100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-396761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-397261639/500000 : ℚ) by norm_num]
  exact coverp00001100011011
theorem coverp0000110001101 : Covers (-396761639/1000000 : ℚ) vp0000110001101 := join_branches bp00001100011010 bp00001100011011
private noncomputable def vp00001100011001_0 : Blocks := edgeBlocks% "full/vectors/00001100011001-V-0000.bin"
noncomputable def vp00001100011001 : Blocks := vp00001100011001_0
theorem coverp00001100011001 : Covers (-396261639/500000 : ℚ) vp00001100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100011000_0 : Blocks := edgeBlocks% "full/vectors/00001100011000-V-0000.bin"
noncomputable def vp00001100011000 : Blocks := vp00001100011000_0
theorem coverp00001100011000 : Covers (-395761639/500000 : ℚ) vp00001100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110001100_0 : Blocks := edgeBlocks% "full/vectors/0000110001100-V-0000.bin"
noncomputable def vp0000110001100 : Blocks := vp0000110001100_0
private theorem bp00001100011000 : Branch 0 (-395761639/1000000 : ℚ) vp0000110001100 := by
  apply branch_left_normalized (c:=vp00001100011000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-395761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-395761639/500000 : ℚ) by norm_num]
  exact coverp00001100011000
private noncomputable def ep00001100011001_0 : Blocks := edgeBlocks% "full/vectors/00001100011001-E-0000.bin"
noncomputable def ep00001100011001 : Blocks := ep00001100011001_0
private theorem idp00001100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110001100.list =
    C ((2:ℤ)^74) * horner X vp00001100011001.list + horner X ep00001100011001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100011001 : Branch 1 (-395761639/1000000 : ℚ) vp0000110001100 := by
  apply branch_checked idp00001100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-395761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-396261639/500000 : ℚ) by norm_num]
  exact coverp00001100011001
theorem coverp0000110001100 : Covers (-395761639/1000000 : ℚ) vp0000110001100 := join_branches bp00001100011000 bp00001100011001
private noncomputable def vp000011000110_0 : Blocks := edgeBlocks% "full/vectors/000011000110-V-0000.bin"
noncomputable def vp000011000110 : Blocks := vp000011000110_0
private theorem bp0000110001100 : Branch 0 (-395761639/2000000 : ℚ) vp000011000110 := by
  apply branch_left_normalized (c:=vp0000110001100) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-395761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-395761639/1000000 : ℚ) by norm_num]
  exact coverp0000110001100
private noncomputable def ep0000110001101_0 : Blocks := edgeBlocks% "full/vectors/0000110001101-E-0000.bin"
noncomputable def ep0000110001101 : Blocks := ep0000110001101_0
private theorem idp0000110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011000110.list =
    C ((2:ℤ)^127) * horner X vp0000110001101.list + horner X ep0000110001101.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110001101 : Branch 1 (-395761639/2000000 : ℚ) vp000011000110 := by
  apply branch_checked idp0000110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-395761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-396761639/1000000 : ℚ) by norm_num]
  exact coverp0000110001101
theorem coverp000011000110 : Covers (-395761639/2000000 : ℚ) vp000011000110 := join_branches bp0000110001100 bp0000110001101
private noncomputable def vp00001100011_0 : Blocks := edgeBlocks% "full/vectors/00001100011-V-0000.bin"
private noncomputable def vp00001100011_1 : Blocks := edgeBlocks% "full/vectors/00001100011-V-0001.bin"
noncomputable def vp00001100011 : Blocks := (Blocks.join vp00001100011_0 vp00001100011_1)
private theorem bp000011000110 : Branch 0 (-395761639/4000000 : ℚ) vp00001100011 := by
  apply branch_left_normalized (c:=vp000011000110) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-395761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-395761639/2000000 : ℚ) by norm_num]
  exact coverp000011000110
private noncomputable def ep000011000111_0 : Blocks := edgeBlocks% "full/vectors/000011000111-E-0000.bin"
private noncomputable def ep000011000111_1 : Blocks := edgeBlocks% "full/vectors/000011000111-E-0001.bin"
noncomputable def ep000011000111 : Blocks := (Blocks.join ep000011000111_0 ep000011000111_1)
private theorem idp000011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001100011.list =
    C ((2:ℤ)^232) * horner X vp000011000111.list + horner X ep000011000111.list := by
  exact edge_identity (B := (2:ℤ)^427) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011000111 : Branch 1 (-395761639/4000000 : ℚ) vp00001100011 := by
  apply branch_checked idp000011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-395761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-397761639/2000000 : ℚ) by norm_num]
  exact coverp000011000111
theorem coverp00001100011 : Covers (-395761639/4000000 : ℚ) vp00001100011 := join_branches bp000011000110 bp000011000111
private noncomputable def vp00001100010111_0 : Blocks := edgeBlocks% "full/vectors/00001100010111-V-0000.bin"
noncomputable def vp00001100010111 : Blocks := vp00001100010111_0
theorem coverp00001100010111 : Covers (-395261639/500000 : ℚ) vp00001100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100010110_0 : Blocks := edgeBlocks% "full/vectors/00001100010110-V-0000.bin"
noncomputable def vp00001100010110 : Blocks := vp00001100010110_0
theorem coverp00001100010110 : Covers (-394761639/500000 : ℚ) vp00001100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110001011_0 : Blocks := edgeBlocks% "full/vectors/0000110001011-V-0000.bin"
noncomputable def vp0000110001011 : Blocks := vp0000110001011_0
private theorem bp00001100010110 : Branch 0 (-394761639/1000000 : ℚ) vp0000110001011 := by
  apply branch_left_normalized (c:=vp00001100010110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-394761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-394761639/500000 : ℚ) by norm_num]
  exact coverp00001100010110
private noncomputable def ep00001100010111_0 : Blocks := edgeBlocks% "full/vectors/00001100010111-E-0000.bin"
noncomputable def ep00001100010111 : Blocks := ep00001100010111_0
private theorem idp00001100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110001011.list =
    C ((2:ℤ)^74) * horner X vp00001100010111.list + horner X ep00001100010111.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100010111 : Branch 1 (-394761639/1000000 : ℚ) vp0000110001011 := by
  apply branch_checked idp00001100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-394761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-395261639/500000 : ℚ) by norm_num]
  exact coverp00001100010111
theorem coverp0000110001011 : Covers (-394761639/1000000 : ℚ) vp0000110001011 := join_branches bp00001100010110 bp00001100010111
private noncomputable def vp00001100010101_0 : Blocks := edgeBlocks% "full/vectors/00001100010101-V-0000.bin"
noncomputable def vp00001100010101 : Blocks := vp00001100010101_0
theorem coverp00001100010101 : Covers (-394261639/500000 : ℚ) vp00001100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100010100_0 : Blocks := edgeBlocks% "full/vectors/00001100010100-V-0000.bin"
noncomputable def vp00001100010100 : Blocks := vp00001100010100_0
theorem coverp00001100010100 : Covers (-393761639/500000 : ℚ) vp00001100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110001010_0 : Blocks := edgeBlocks% "full/vectors/0000110001010-V-0000.bin"
noncomputable def vp0000110001010 : Blocks := vp0000110001010_0
private theorem bp00001100010100 : Branch 0 (-393761639/1000000 : ℚ) vp0000110001010 := by
  apply branch_left_normalized (c:=vp00001100010100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-393761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-393761639/500000 : ℚ) by norm_num]
  exact coverp00001100010100
private noncomputable def ep00001100010101_0 : Blocks := edgeBlocks% "full/vectors/00001100010101-E-0000.bin"
noncomputable def ep00001100010101 : Blocks := ep00001100010101_0
private theorem idp00001100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110001010.list =
    C ((2:ℤ)^74) * horner X vp00001100010101.list + horner X ep00001100010101.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100010101 : Branch 1 (-393761639/1000000 : ℚ) vp0000110001010 := by
  apply branch_checked idp00001100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-393761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-394261639/500000 : ℚ) by norm_num]
  exact coverp00001100010101
theorem coverp0000110001010 : Covers (-393761639/1000000 : ℚ) vp0000110001010 := join_branches bp00001100010100 bp00001100010101
private noncomputable def vp000011000101_0 : Blocks := edgeBlocks% "full/vectors/000011000101-V-0000.bin"
noncomputable def vp000011000101 : Blocks := vp000011000101_0
private theorem bp0000110001010 : Branch 0 (-393761639/2000000 : ℚ) vp000011000101 := by
  apply branch_left_normalized (c:=vp0000110001010) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-393761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-393761639/1000000 : ℚ) by norm_num]
  exact coverp0000110001010
private noncomputable def ep0000110001011_0 : Blocks := edgeBlocks% "full/vectors/0000110001011-E-0000.bin"
noncomputable def ep0000110001011 : Blocks := ep0000110001011_0
private theorem idp0000110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011000101.list =
    C ((2:ℤ)^128) * horner X vp0000110001011.list + horner X ep0000110001011.list := by
  exact edge_identity (B := (2:ℤ)^276) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110001011 : Branch 1 (-393761639/2000000 : ℚ) vp000011000101 := by
  apply branch_checked idp0000110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-393761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-394761639/1000000 : ℚ) by norm_num]
  exact coverp0000110001011
theorem coverp000011000101 : Covers (-393761639/2000000 : ℚ) vp000011000101 := join_branches bp0000110001010 bp0000110001011
private noncomputable def vp00001100010011_0 : Blocks := edgeBlocks% "full/vectors/00001100010011-V-0000.bin"
noncomputable def vp00001100010011 : Blocks := vp00001100010011_0
theorem coverp00001100010011 : Covers (-393261639/500000 : ℚ) vp00001100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100010010_0 : Blocks := edgeBlocks% "full/vectors/00001100010010-V-0000.bin"
noncomputable def vp00001100010010 : Blocks := vp00001100010010_0
theorem coverp00001100010010 : Covers (-392761639/500000 : ℚ) vp00001100010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110001001_0 : Blocks := edgeBlocks% "full/vectors/0000110001001-V-0000.bin"
noncomputable def vp0000110001001 : Blocks := vp0000110001001_0
private theorem bp00001100010010 : Branch 0 (-392761639/1000000 : ℚ) vp0000110001001 := by
  apply branch_left_normalized (c:=vp00001100010010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-392761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-392761639/500000 : ℚ) by norm_num]
  exact coverp00001100010010
private noncomputable def ep00001100010011_0 : Blocks := edgeBlocks% "full/vectors/00001100010011-E-0000.bin"
noncomputable def ep00001100010011 : Blocks := ep00001100010011_0
private theorem idp00001100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110001001.list =
    C ((2:ℤ)^74) * horner X vp00001100010011.list + horner X ep00001100010011.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100010011 : Branch 1 (-392761639/1000000 : ℚ) vp0000110001001 := by
  apply branch_checked idp00001100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-392761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-393261639/500000 : ℚ) by norm_num]
  exact coverp00001100010011
theorem coverp0000110001001 : Covers (-392761639/1000000 : ℚ) vp0000110001001 := join_branches bp00001100010010 bp00001100010011
private noncomputable def vp00001100010001_0 : Blocks := edgeBlocks% "full/vectors/00001100010001-V-0000.bin"
noncomputable def vp00001100010001 : Blocks := vp00001100010001_0
theorem coverp00001100010001 : Covers (-392261639/500000 : ℚ) vp00001100010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100010000_0 : Blocks := edgeBlocks% "full/vectors/00001100010000-V-0000.bin"
noncomputable def vp00001100010000 : Blocks := vp00001100010000_0
theorem coverp00001100010000 : Covers (-391761639/500000 : ℚ) vp00001100010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110001000_0 : Blocks := edgeBlocks% "full/vectors/0000110001000-V-0000.bin"
noncomputable def vp0000110001000 : Blocks := vp0000110001000_0
private theorem bp00001100010000 : Branch 0 (-391761639/1000000 : ℚ) vp0000110001000 := by
  apply branch_left_normalized (c:=vp00001100010000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-391761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-391761639/500000 : ℚ) by norm_num]
  exact coverp00001100010000
private noncomputable def ep00001100010001_0 : Blocks := edgeBlocks% "full/vectors/00001100010001-E-0000.bin"
noncomputable def ep00001100010001 : Blocks := ep00001100010001_0
private theorem idp00001100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110001000.list =
    C ((2:ℤ)^72) * horner X vp00001100010001.list + horner X ep00001100010001.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100010001 : Branch 1 (-391761639/1000000 : ℚ) vp0000110001000 := by
  apply branch_checked idp00001100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-391761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-392261639/500000 : ℚ) by norm_num]
  exact coverp00001100010001
theorem coverp0000110001000 : Covers (-391761639/1000000 : ℚ) vp0000110001000 := join_branches bp00001100010000 bp00001100010001
private noncomputable def vp000011000100_0 : Blocks := edgeBlocks% "full/vectors/000011000100-V-0000.bin"
noncomputable def vp000011000100 : Blocks := vp000011000100_0
private theorem bp0000110001000 : Branch 0 (-391761639/2000000 : ℚ) vp000011000100 := by
  apply branch_left_normalized (c:=vp0000110001000) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-391761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-391761639/1000000 : ℚ) by norm_num]
  exact coverp0000110001000
private noncomputable def ep0000110001001_0 : Blocks := edgeBlocks% "full/vectors/0000110001001-E-0000.bin"
noncomputable def ep0000110001001 : Blocks := ep0000110001001_0
private theorem idp0000110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011000100.list =
    C ((2:ℤ)^126) * horner X vp0000110001001.list + horner X ep0000110001001.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110001001 : Branch 1 (-391761639/2000000 : ℚ) vp000011000100 := by
  apply branch_checked idp0000110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-391761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-392761639/1000000 : ℚ) by norm_num]
  exact coverp0000110001001
theorem coverp000011000100 : Covers (-391761639/2000000 : ℚ) vp000011000100 := join_branches bp0000110001000 bp0000110001001
private noncomputable def vp00001100010_0 : Blocks := edgeBlocks% "full/vectors/00001100010-V-0000.bin"
private noncomputable def vp00001100010_1 : Blocks := edgeBlocks% "full/vectors/00001100010-V-0001.bin"
noncomputable def vp00001100010 : Blocks := (Blocks.join vp00001100010_0 vp00001100010_1)
private theorem bp000011000100 : Branch 0 (-391761639/4000000 : ℚ) vp00001100010 := by
  apply branch_left_normalized (c:=vp000011000100) (k:=0) (m:=120) (by decide +kernel)
  rw [show 2*(-391761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-391761639/2000000 : ℚ) by norm_num]
  exact coverp000011000100
private noncomputable def ep000011000101_0 : Blocks := edgeBlocks% "full/vectors/000011000101-E-0000.bin"
private noncomputable def ep000011000101_1 : Blocks := edgeBlocks% "full/vectors/000011000101-E-0001.bin"
noncomputable def ep000011000101 : Blocks := (Blocks.join ep000011000101_0 ep000011000101_1)
private theorem idp000011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001100010.list =
    C ((2:ℤ)^233) * horner X vp000011000101.list + horner X ep000011000101.list := by
  exact edge_identity (B := (2:ℤ)^429) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011000101 : Branch 1 (-391761639/4000000 : ℚ) vp00001100010 := by
  apply branch_checked idp000011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-391761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-393761639/2000000 : ℚ) by norm_num]
  exact coverp000011000101
theorem coverp00001100010 : Covers (-391761639/4000000 : ℚ) vp00001100010 := join_branches bp000011000100 bp000011000101
private noncomputable def vp0000110001_0 : Blocks := edgeBlocks% "full/vectors/0000110001-V-0000.bin"
private noncomputable def vp0000110001_1 : Blocks := edgeBlocks% "full/vectors/0000110001-V-0001.bin"
private noncomputable def vp0000110001_2 : Blocks := edgeBlocks% "full/vectors/0000110001-V-0002.bin"
private noncomputable def vp0000110001_3 : Blocks := edgeBlocks% "full/vectors/0000110001-V-0003.bin"
noncomputable def vp0000110001 : Blocks := (Blocks.join (Blocks.join vp0000110001_0 vp0000110001_1) (Blocks.join vp0000110001_2 vp0000110001_3))
private theorem bp00001100010 : Branch 0 (-391761639/8000000 : ℚ) vp0000110001 := by
  apply branch_left_normalized (c:=vp00001100010) (k:=0) (m:=221) (by decide +kernel)
  rw [show 2*(-391761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-391761639/4000000 : ℚ) by norm_num]
  exact coverp00001100010
private noncomputable def ep00001100011_0 : Blocks := edgeBlocks% "full/vectors/00001100011-E-0000.bin"
private noncomputable def ep00001100011_1 : Blocks := edgeBlocks% "full/vectors/00001100011-E-0001.bin"
private noncomputable def ep00001100011_2 : Blocks := edgeBlocks% "full/vectors/00001100011-E-0002.bin"
private noncomputable def ep00001100011_3 : Blocks := edgeBlocks% "full/vectors/00001100011-E-0003.bin"
noncomputable def ep00001100011 : Blocks := (Blocks.join (Blocks.join ep00001100011_0 ep00001100011_1) (Blocks.join ep00001100011_2 ep00001100011_3))
private theorem idp00001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110001.list =
    C ((2:ℤ)^442) * horner X vp00001100011.list + horner X ep00001100011.list := by
  exact edge_identity (B := (2:ℤ)^731) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100011 : Branch 1 (-391761639/8000000 : ℚ) vp0000110001 := by
  apply branch_checked idp00001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-391761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-395761639/4000000 : ℚ) by norm_num]
  exact coverp00001100011
theorem coverp0000110001 : Covers (-391761639/8000000 : ℚ) vp0000110001 := join_branches bp00001100010 bp00001100011
private noncomputable def vp00001100001111_0 : Blocks := edgeBlocks% "full/vectors/00001100001111-V-0000.bin"
noncomputable def vp00001100001111 : Blocks := vp00001100001111_0
theorem coverp00001100001111 : Covers (-391261639/500000 : ℚ) vp00001100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100001110_0 : Blocks := edgeBlocks% "full/vectors/00001100001110-V-0000.bin"
noncomputable def vp00001100001110 : Blocks := vp00001100001110_0
theorem coverp00001100001110 : Covers (-390761639/500000 : ℚ) vp00001100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110000111_0 : Blocks := edgeBlocks% "full/vectors/0000110000111-V-0000.bin"
noncomputable def vp0000110000111 : Blocks := vp0000110000111_0
private theorem bp00001100001110 : Branch 0 (-390761639/1000000 : ℚ) vp0000110000111 := by
  apply branch_left_normalized (c:=vp00001100001110) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-390761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-390761639/500000 : ℚ) by norm_num]
  exact coverp00001100001110
private noncomputable def ep00001100001111_0 : Blocks := edgeBlocks% "full/vectors/00001100001111-E-0000.bin"
noncomputable def ep00001100001111 : Blocks := ep00001100001111_0
private theorem idp00001100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110000111.list =
    C ((2:ℤ)^74) * horner X vp00001100001111.list + horner X ep00001100001111.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100001111 : Branch 1 (-390761639/1000000 : ℚ) vp0000110000111 := by
  apply branch_checked idp00001100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-390761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-391261639/500000 : ℚ) by norm_num]
  exact coverp00001100001111
theorem coverp0000110000111 : Covers (-390761639/1000000 : ℚ) vp0000110000111 := join_branches bp00001100001110 bp00001100001111
private noncomputable def vp00001100001101_0 : Blocks := edgeBlocks% "full/vectors/00001100001101-V-0000.bin"
noncomputable def vp00001100001101 : Blocks := vp00001100001101_0
theorem coverp00001100001101 : Covers (-390261639/500000 : ℚ) vp00001100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100001100_0 : Blocks := edgeBlocks% "full/vectors/00001100001100-V-0000.bin"
noncomputable def vp00001100001100 : Blocks := vp00001100001100_0
theorem coverp00001100001100 : Covers (-389761639/500000 : ℚ) vp00001100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110000110_0 : Blocks := edgeBlocks% "full/vectors/0000110000110-V-0000.bin"
noncomputable def vp0000110000110 : Blocks := vp0000110000110_0
private theorem bp00001100001100 : Branch 0 (-389761639/1000000 : ℚ) vp0000110000110 := by
  apply branch_left_normalized (c:=vp00001100001100) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-389761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-389761639/500000 : ℚ) by norm_num]
  exact coverp00001100001100
private noncomputable def ep00001100001101_0 : Blocks := edgeBlocks% "full/vectors/00001100001101-E-0000.bin"
noncomputable def ep00001100001101 : Blocks := ep00001100001101_0
private theorem idp00001100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110000110.list =
    C ((2:ℤ)^74) * horner X vp00001100001101.list + horner X ep00001100001101.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100001101 : Branch 1 (-389761639/1000000 : ℚ) vp0000110000110 := by
  apply branch_checked idp00001100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-389761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-390261639/500000 : ℚ) by norm_num]
  exact coverp00001100001101
theorem coverp0000110000110 : Covers (-389761639/1000000 : ℚ) vp0000110000110 := join_branches bp00001100001100 bp00001100001101
private noncomputable def vp000011000011_0 : Blocks := edgeBlocks% "full/vectors/000011000011-V-0000.bin"
noncomputable def vp000011000011 : Blocks := vp000011000011_0
private theorem bp0000110000110 : Branch 0 (-389761639/2000000 : ℚ) vp000011000011 := by
  apply branch_left_normalized (c:=vp0000110000110) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-389761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-389761639/1000000 : ℚ) by norm_num]
  exact coverp0000110000110
private noncomputable def ep0000110000111_0 : Blocks := edgeBlocks% "full/vectors/0000110000111-E-0000.bin"
noncomputable def ep0000110000111 : Blocks := ep0000110000111_0
private theorem idp0000110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011000011.list =
    C ((2:ℤ)^128) * horner X vp0000110000111.list + horner X ep0000110000111.list := by
  exact edge_identity (B := (2:ℤ)^277) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110000111 : Branch 1 (-389761639/2000000 : ℚ) vp000011000011 := by
  apply branch_checked idp0000110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-389761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-390761639/1000000 : ℚ) by norm_num]
  exact coverp0000110000111
theorem coverp000011000011 : Covers (-389761639/2000000 : ℚ) vp000011000011 := join_branches bp0000110000110 bp0000110000111
private noncomputable def vp00001100001011_0 : Blocks := edgeBlocks% "full/vectors/00001100001011-V-0000.bin"
noncomputable def vp00001100001011 : Blocks := vp00001100001011_0
theorem coverp00001100001011 : Covers (-389261639/500000 : ℚ) vp00001100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100001010_0 : Blocks := edgeBlocks% "full/vectors/00001100001010-V-0000.bin"
noncomputable def vp00001100001010 : Blocks := vp00001100001010_0
theorem coverp00001100001010 : Covers (-388761639/500000 : ℚ) vp00001100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110000101_0 : Blocks := edgeBlocks% "full/vectors/0000110000101-V-0000.bin"
noncomputable def vp0000110000101 : Blocks := vp0000110000101_0
private theorem bp00001100001010 : Branch 0 (-388761639/1000000 : ℚ) vp0000110000101 := by
  apply branch_left_normalized (c:=vp00001100001010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-388761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-388761639/500000 : ℚ) by norm_num]
  exact coverp00001100001010
private noncomputable def ep00001100001011_0 : Blocks := edgeBlocks% "full/vectors/00001100001011-E-0000.bin"
noncomputable def ep00001100001011 : Blocks := ep00001100001011_0
private theorem idp00001100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110000101.list =
    C ((2:ℤ)^75) * horner X vp00001100001011.list + horner X ep00001100001011.list := by
  exact edge_identity (B := (2:ℤ)^200) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100001011 : Branch 1 (-388761639/1000000 : ℚ) vp0000110000101 := by
  apply branch_checked idp00001100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-388761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-389261639/500000 : ℚ) by norm_num]
  exact coverp00001100001011
theorem coverp0000110000101 : Covers (-388761639/1000000 : ℚ) vp0000110000101 := join_branches bp00001100001010 bp00001100001011
private noncomputable def vp00001100001001_0 : Blocks := edgeBlocks% "full/vectors/00001100001001-V-0000.bin"
noncomputable def vp00001100001001 : Blocks := vp00001100001001_0
theorem coverp00001100001001 : Covers (-388261639/500000 : ℚ) vp00001100001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100001000_0 : Blocks := edgeBlocks% "full/vectors/00001100001000-V-0000.bin"
noncomputable def vp00001100001000 : Blocks := vp00001100001000_0
theorem coverp00001100001000 : Covers (-387761639/500000 : ℚ) vp00001100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110000100_0 : Blocks := edgeBlocks% "full/vectors/0000110000100-V-0000.bin"
noncomputable def vp0000110000100 : Blocks := vp0000110000100_0
private theorem bp00001100001000 : Branch 0 (-387761639/1000000 : ℚ) vp0000110000100 := by
  apply branch_left_normalized (c:=vp00001100001000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-387761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-387761639/500000 : ℚ) by norm_num]
  exact coverp00001100001000
private noncomputable def ep00001100001001_0 : Blocks := edgeBlocks% "full/vectors/00001100001001-E-0000.bin"
noncomputable def ep00001100001001 : Blocks := ep00001100001001_0
private theorem idp00001100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110000100.list =
    C ((2:ℤ)^74) * horner X vp00001100001001.list + horner X ep00001100001001.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100001001 : Branch 1 (-387761639/1000000 : ℚ) vp0000110000100 := by
  apply branch_checked idp00001100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-387761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-388261639/500000 : ℚ) by norm_num]
  exact coverp00001100001001
theorem coverp0000110000100 : Covers (-387761639/1000000 : ℚ) vp0000110000100 := join_branches bp00001100001000 bp00001100001001
private noncomputable def vp000011000010_0 : Blocks := edgeBlocks% "full/vectors/000011000010-V-0000.bin"
noncomputable def vp000011000010 : Blocks := vp000011000010_0
private theorem bp0000110000100 : Branch 0 (-387761639/2000000 : ℚ) vp000011000010 := by
  apply branch_left_normalized (c:=vp0000110000100) (k:=0) (m:=70) (by decide +kernel)
  rw [show 2*(-387761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-387761639/1000000 : ℚ) by norm_num]
  exact coverp0000110000100
private noncomputable def ep0000110000101_0 : Blocks := edgeBlocks% "full/vectors/0000110000101-E-0000.bin"
noncomputable def ep0000110000101 : Blocks := ep0000110000101_0
private theorem idp0000110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011000010.list =
    C ((2:ℤ)^127) * horner X vp0000110000101.list + horner X ep0000110000101.list := by
  exact edge_identity (B := (2:ℤ)^276) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110000101 : Branch 1 (-387761639/2000000 : ℚ) vp000011000010 := by
  apply branch_checked idp0000110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-387761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-388761639/1000000 : ℚ) by norm_num]
  exact coverp0000110000101
theorem coverp000011000010 : Covers (-387761639/2000000 : ℚ) vp000011000010 := join_branches bp0000110000100 bp0000110000101
private noncomputable def vp00001100001_0 : Blocks := edgeBlocks% "full/vectors/00001100001-V-0000.bin"
private noncomputable def vp00001100001_1 : Blocks := edgeBlocks% "full/vectors/00001100001-V-0001.bin"
noncomputable def vp00001100001 : Blocks := (Blocks.join vp00001100001_0 vp00001100001_1)
private theorem bp000011000010 : Branch 0 (-387761639/4000000 : ℚ) vp00001100001 := by
  apply branch_left_normalized (c:=vp000011000010) (k:=0) (m:=121) (by decide +kernel)
  rw [show 2*(-387761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-387761639/2000000 : ℚ) by norm_num]
  exact coverp000011000010
private noncomputable def ep000011000011_0 : Blocks := edgeBlocks% "full/vectors/000011000011-E-0000.bin"
private noncomputable def ep000011000011_1 : Blocks := edgeBlocks% "full/vectors/000011000011-E-0001.bin"
noncomputable def ep000011000011 : Blocks := (Blocks.join ep000011000011_0 ep000011000011_1)
private theorem idp000011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001100001.list =
    C ((2:ℤ)^233) * horner X vp000011000011.list + horner X ep000011000011.list := by
  exact edge_identity (B := (2:ℤ)^429) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011000011 : Branch 1 (-387761639/4000000 : ℚ) vp00001100001 := by
  apply branch_checked idp000011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-387761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-389761639/2000000 : ℚ) by norm_num]
  exact coverp000011000011
theorem coverp00001100001 : Covers (-387761639/4000000 : ℚ) vp00001100001 := join_branches bp000011000010 bp000011000011
private noncomputable def vp00001100000111_0 : Blocks := edgeBlocks% "full/vectors/00001100000111-V-0000.bin"
noncomputable def vp00001100000111 : Blocks := vp00001100000111_0
theorem coverp00001100000111 : Covers (-387261639/500000 : ℚ) vp00001100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100000110_0 : Blocks := edgeBlocks% "full/vectors/00001100000110-V-0000.bin"
noncomputable def vp00001100000110 : Blocks := vp00001100000110_0
theorem coverp00001100000110 : Covers (-386761639/500000 : ℚ) vp00001100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110000011_0 : Blocks := edgeBlocks% "full/vectors/0000110000011-V-0000.bin"
noncomputable def vp0000110000011 : Blocks := vp0000110000011_0
private theorem bp00001100000110 : Branch 0 (-386761639/1000000 : ℚ) vp0000110000011 := by
  apply branch_left_normalized (c:=vp00001100000110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-386761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-386761639/500000 : ℚ) by norm_num]
  exact coverp00001100000110
private noncomputable def ep00001100000111_0 : Blocks := edgeBlocks% "full/vectors/00001100000111-E-0000.bin"
noncomputable def ep00001100000111 : Blocks := ep00001100000111_0
private theorem idp00001100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110000011.list =
    C ((2:ℤ)^72) * horner X vp00001100000111.list + horner X ep00001100000111.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100000111 : Branch 1 (-386761639/1000000 : ℚ) vp0000110000011 := by
  apply branch_checked idp00001100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-386761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-387261639/500000 : ℚ) by norm_num]
  exact coverp00001100000111
theorem coverp0000110000011 : Covers (-386761639/1000000 : ℚ) vp0000110000011 := join_branches bp00001100000110 bp00001100000111
private noncomputable def vp00001100000101_0 : Blocks := edgeBlocks% "full/vectors/00001100000101-V-0000.bin"
noncomputable def vp00001100000101 : Blocks := vp00001100000101_0
theorem coverp00001100000101 : Covers (-386261639/500000 : ℚ) vp00001100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100000100_0 : Blocks := edgeBlocks% "full/vectors/00001100000100-V-0000.bin"
noncomputable def vp00001100000100 : Blocks := vp00001100000100_0
theorem coverp00001100000100 : Covers (-385761639/500000 : ℚ) vp00001100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110000010_0 : Blocks := edgeBlocks% "full/vectors/0000110000010-V-0000.bin"
noncomputable def vp0000110000010 : Blocks := vp0000110000010_0
private theorem bp00001100000100 : Branch 0 (-385761639/1000000 : ℚ) vp0000110000010 := by
  apply branch_left_normalized (c:=vp00001100000100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-385761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-385761639/500000 : ℚ) by norm_num]
  exact coverp00001100000100
private noncomputable def ep00001100000101_0 : Blocks := edgeBlocks% "full/vectors/00001100000101-E-0000.bin"
noncomputable def ep00001100000101 : Blocks := ep00001100000101_0
private theorem idp00001100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110000010.list =
    C ((2:ℤ)^73) * horner X vp00001100000101.list + horner X ep00001100000101.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100000101 : Branch 1 (-385761639/1000000 : ℚ) vp0000110000010 := by
  apply branch_checked idp00001100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-385761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-386261639/500000 : ℚ) by norm_num]
  exact coverp00001100000101
theorem coverp0000110000010 : Covers (-385761639/1000000 : ℚ) vp0000110000010 := join_branches bp00001100000100 bp00001100000101
private noncomputable def vp000011000001_0 : Blocks := edgeBlocks% "full/vectors/000011000001-V-0000.bin"
noncomputable def vp000011000001 : Blocks := vp000011000001_0
private theorem bp0000110000010 : Branch 0 (-385761639/2000000 : ℚ) vp000011000001 := by
  apply branch_left_normalized (c:=vp0000110000010) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-385761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-385761639/1000000 : ℚ) by norm_num]
  exact coverp0000110000010
private noncomputable def ep0000110000011_0 : Blocks := edgeBlocks% "full/vectors/0000110000011-E-0000.bin"
noncomputable def ep0000110000011 : Blocks := ep0000110000011_0
private theorem idp0000110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011000001.list =
    C ((2:ℤ)^127) * horner X vp0000110000011.list + horner X ep0000110000011.list := by
  exact edge_identity (B := (2:ℤ)^274) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110000011 : Branch 1 (-385761639/2000000 : ℚ) vp000011000001 := by
  apply branch_checked idp0000110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-385761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-386761639/1000000 : ℚ) by norm_num]
  exact coverp0000110000011
theorem coverp000011000001 : Covers (-385761639/2000000 : ℚ) vp000011000001 := join_branches bp0000110000010 bp0000110000011
private noncomputable def vp00001100000011_0 : Blocks := edgeBlocks% "full/vectors/00001100000011-V-0000.bin"
noncomputable def vp00001100000011 : Blocks := vp00001100000011_0
theorem coverp00001100000011 : Covers (-385261639/500000 : ℚ) vp00001100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100000010_0 : Blocks := edgeBlocks% "full/vectors/00001100000010-V-0000.bin"
noncomputable def vp00001100000010 : Blocks := vp00001100000010_0
theorem coverp00001100000010 : Covers (-384761639/500000 : ℚ) vp00001100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110000001_0 : Blocks := edgeBlocks% "full/vectors/0000110000001-V-0000.bin"
noncomputable def vp0000110000001 : Blocks := vp0000110000001_0
private theorem bp00001100000010 : Branch 0 (-384761639/1000000 : ℚ) vp0000110000001 := by
  apply branch_left_normalized (c:=vp00001100000010) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-384761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-384761639/500000 : ℚ) by norm_num]
  exact coverp00001100000010
private noncomputable def ep00001100000011_0 : Blocks := edgeBlocks% "full/vectors/00001100000011-E-0000.bin"
noncomputable def ep00001100000011 : Blocks := ep00001100000011_0
private theorem idp00001100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110000001.list =
    C ((2:ℤ)^74) * horner X vp00001100000011.list + horner X ep00001100000011.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100000011 : Branch 1 (-384761639/1000000 : ℚ) vp0000110000001 := by
  apply branch_checked idp00001100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-384761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-385261639/500000 : ℚ) by norm_num]
  exact coverp00001100000011
theorem coverp0000110000001 : Covers (-384761639/1000000 : ℚ) vp0000110000001 := join_branches bp00001100000010 bp00001100000011
private noncomputable def vp00001100000001_0 : Blocks := edgeBlocks% "full/vectors/00001100000001-V-0000.bin"
noncomputable def vp00001100000001 : Blocks := vp00001100000001_0
theorem coverp00001100000001 : Covers (-384261639/500000 : ℚ) vp00001100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001100000000_0 : Blocks := edgeBlocks% "full/vectors/00001100000000-V-0000.bin"
noncomputable def vp00001100000000 : Blocks := vp00001100000000_0
theorem coverp00001100000000 : Covers (-383761639/500000 : ℚ) vp00001100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110000000_0 : Blocks := edgeBlocks% "full/vectors/0000110000000-V-0000.bin"
noncomputable def vp0000110000000 : Blocks := vp0000110000000_0
private theorem bp00001100000000 : Branch 0 (-383761639/1000000 : ℚ) vp0000110000000 := by
  apply branch_left_normalized (c:=vp00001100000000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-383761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-383761639/500000 : ℚ) by norm_num]
  exact coverp00001100000000
private noncomputable def ep00001100000001_0 : Blocks := edgeBlocks% "full/vectors/00001100000001-E-0000.bin"
noncomputable def ep00001100000001 : Blocks := ep00001100000001_0
private theorem idp00001100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110000000.list =
    C ((2:ℤ)^77) * horner X vp00001100000001.list + horner X ep00001100000001.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100000001 : Branch 1 (-383761639/1000000 : ℚ) vp0000110000000 := by
  apply branch_checked idp00001100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-383761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-384261639/500000 : ℚ) by norm_num]
  exact coverp00001100000001
theorem coverp0000110000000 : Covers (-383761639/1000000 : ℚ) vp0000110000000 := join_branches bp00001100000000 bp00001100000001
private noncomputable def vp000011000000_0 : Blocks := edgeBlocks% "full/vectors/000011000000-V-0000.bin"
noncomputable def vp000011000000 : Blocks := vp000011000000_0
private theorem bp0000110000000 : Branch 0 (-383761639/2000000 : ℚ) vp000011000000 := by
  apply branch_left_normalized (c:=vp0000110000000) (k:=0) (m:=71) (by decide +kernel)
  rw [show 2*(-383761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-383761639/1000000 : ℚ) by norm_num]
  exact coverp0000110000000
private noncomputable def ep0000110000001_0 : Blocks := edgeBlocks% "full/vectors/0000110000001-E-0000.bin"
noncomputable def ep0000110000001 : Blocks := ep0000110000001_0
private theorem idp0000110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011000000.list =
    C ((2:ℤ)^131) * horner X vp0000110000001.list + horner X ep0000110000001.list := by
  exact edge_identity (B := (2:ℤ)^278) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110000001 : Branch 1 (-383761639/2000000 : ℚ) vp000011000000 := by
  apply branch_checked idp0000110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-383761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-384761639/1000000 : ℚ) by norm_num]
  exact coverp0000110000001
theorem coverp000011000000 : Covers (-383761639/2000000 : ℚ) vp000011000000 := join_branches bp0000110000000 bp0000110000001
private noncomputable def vp00001100000_0 : Blocks := edgeBlocks% "full/vectors/00001100000-V-0000.bin"
private noncomputable def vp00001100000_1 : Blocks := edgeBlocks% "full/vectors/00001100000-V-0001.bin"
noncomputable def vp00001100000 : Blocks := (Blocks.join vp00001100000_0 vp00001100000_1)
private theorem bp000011000000 : Branch 0 (-383761639/4000000 : ℚ) vp00001100000 := by
  apply branch_left_normalized (c:=vp000011000000) (k:=0) (m:=122) (by decide +kernel)
  rw [show 2*(-383761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-383761639/2000000 : ℚ) by norm_num]
  exact coverp000011000000
private noncomputable def ep000011000001_0 : Blocks := edgeBlocks% "full/vectors/000011000001-E-0000.bin"
private noncomputable def ep000011000001_1 : Blocks := edgeBlocks% "full/vectors/000011000001-E-0001.bin"
noncomputable def ep000011000001 : Blocks := (Blocks.join ep000011000001_0 ep000011000001_1)
private theorem idp000011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001100000.list =
    C ((2:ℤ)^238) * horner X vp000011000001.list + horner X ep000011000001.list := by
  exact edge_identity (B := (2:ℤ)^433) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011000001 : Branch 1 (-383761639/4000000 : ℚ) vp00001100000 := by
  apply branch_checked idp000011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-383761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-385761639/2000000 : ℚ) by norm_num]
  exact coverp000011000001
theorem coverp00001100000 : Covers (-383761639/4000000 : ℚ) vp00001100000 := join_branches bp000011000000 bp000011000001
private noncomputable def vp0000110000_0 : Blocks := edgeBlocks% "full/vectors/0000110000-V-0000.bin"
private noncomputable def vp0000110000_1 : Blocks := edgeBlocks% "full/vectors/0000110000-V-0001.bin"
private noncomputable def vp0000110000_2 : Blocks := edgeBlocks% "full/vectors/0000110000-V-0002.bin"
private noncomputable def vp0000110000_3 : Blocks := edgeBlocks% "full/vectors/0000110000-V-0003.bin"
noncomputable def vp0000110000 : Blocks := (Blocks.join (Blocks.join vp0000110000_0 vp0000110000_1) (Blocks.join vp0000110000_2 vp0000110000_3))
private theorem bp00001100000 : Branch 0 (-383761639/8000000 : ℚ) vp0000110000 := by
  apply branch_left_normalized (c:=vp00001100000) (k:=0) (m:=223) (by decide +kernel)
  rw [show 2*(-383761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-383761639/4000000 : ℚ) by norm_num]
  exact coverp00001100000
private noncomputable def ep00001100001_0 : Blocks := edgeBlocks% "full/vectors/00001100001-E-0000.bin"
private noncomputable def ep00001100001_1 : Blocks := edgeBlocks% "full/vectors/00001100001-E-0001.bin"
private noncomputable def ep00001100001_2 : Blocks := edgeBlocks% "full/vectors/00001100001-E-0002.bin"
private noncomputable def ep00001100001_3 : Blocks := edgeBlocks% "full/vectors/00001100001-E-0003.bin"
noncomputable def ep00001100001 : Blocks := (Blocks.join (Blocks.join ep00001100001_0 ep00001100001_1) (Blocks.join ep00001100001_2 ep00001100001_3))
private theorem idp00001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110000.list =
    C ((2:ℤ)^447) * horner X vp00001100001.list + horner X ep00001100001.list := by
  exact edge_identity (B := (2:ℤ)^738) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001100001 : Branch 1 (-383761639/8000000 : ℚ) vp0000110000 := by
  apply branch_checked idp00001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-383761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-387761639/4000000 : ℚ) by norm_num]
  exact coverp00001100001
theorem coverp0000110000 : Covers (-383761639/8000000 : ℚ) vp0000110000 := join_branches bp00001100000 bp00001100001
private noncomputable def vp000011000_0 : Blocks := edgeBlocks% "full/vectors/000011000-V-0000.bin"
private noncomputable def vp000011000_1 : Blocks := edgeBlocks% "full/vectors/000011000-V-0001.bin"
private noncomputable def vp000011000_2 : Blocks := edgeBlocks% "full/vectors/000011000-V-0002.bin"
private noncomputable def vp000011000_3 : Blocks := edgeBlocks% "full/vectors/000011000-V-0003.bin"
private noncomputable def vp000011000_4 : Blocks := edgeBlocks% "full/vectors/000011000-V-0004.bin"
private noncomputable def vp000011000_5 : Blocks := edgeBlocks% "full/vectors/000011000-V-0005.bin"
private noncomputable def vp000011000_6 : Blocks := edgeBlocks% "full/vectors/000011000-V-0006.bin"
noncomputable def vp000011000 : Blocks := (Blocks.join (Blocks.join vp000011000_0 (Blocks.join vp000011000_1 vp000011000_2)) (Blocks.join (Blocks.join vp000011000_3 vp000011000_4) (Blocks.join vp000011000_5 vp000011000_6)))
private theorem bp0000110000 : Branch 0 (-383761639/16000000 : ℚ) vp000011000 := by
  apply branch_left_normalized (c:=vp0000110000) (k:=0) (m:=422) (by decide +kernel)
  rw [show 2*(-383761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-383761639/8000000 : ℚ) by norm_num]
  exact coverp0000110000
private noncomputable def ep0000110001_0 : Blocks := edgeBlocks% "full/vectors/0000110001-E-0000.bin"
private noncomputable def ep0000110001_1 : Blocks := edgeBlocks% "full/vectors/0000110001-E-0001.bin"
private noncomputable def ep0000110001_2 : Blocks := edgeBlocks% "full/vectors/0000110001-E-0002.bin"
private noncomputable def ep0000110001_3 : Blocks := edgeBlocks% "full/vectors/0000110001-E-0003.bin"
private noncomputable def ep0000110001_4 : Blocks := edgeBlocks% "full/vectors/0000110001-E-0004.bin"
private noncomputable def ep0000110001_5 : Blocks := edgeBlocks% "full/vectors/0000110001-E-0005.bin"
private noncomputable def ep0000110001_6 : Blocks := edgeBlocks% "full/vectors/0000110001-E-0006.bin"
noncomputable def ep0000110001 : Blocks := (Blocks.join (Blocks.join ep0000110001_0 (Blocks.join ep0000110001_1 ep0000110001_2)) (Blocks.join (Blocks.join ep0000110001_3 ep0000110001_4) (Blocks.join ep0000110001_5 ep0000110001_6)))
private theorem idp0000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011000.list =
    C ((2:ℤ)^864) * horner X vp0000110001.list + horner X ep0000110001.list := by
  exact edge_identity (B := (2:ℤ)^1344) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110001 : Branch 1 (-383761639/16000000 : ℚ) vp000011000 := by
  apply branch_checked idp0000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-383761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-391761639/8000000 : ℚ) by norm_num]
  exact coverp0000110001
theorem coverp000011000 : Covers (-383761639/16000000 : ℚ) vp000011000 := join_branches bp0000110000 bp0000110001
private noncomputable def vp00001100_0 : Blocks := edgeBlocks% "full/vectors/00001100-V-0000.bin"
private noncomputable def vp00001100_1 : Blocks := edgeBlocks% "full/vectors/00001100-V-0001.bin"
private noncomputable def vp00001100_2 : Blocks := edgeBlocks% "full/vectors/00001100-V-0002.bin"
private noncomputable def vp00001100_3 : Blocks := edgeBlocks% "full/vectors/00001100-V-0003.bin"
private noncomputable def vp00001100_4 : Blocks := edgeBlocks% "full/vectors/00001100-V-0004.bin"
private noncomputable def vp00001100_5 : Blocks := edgeBlocks% "full/vectors/00001100-V-0005.bin"
private noncomputable def vp00001100_6 : Blocks := edgeBlocks% "full/vectors/00001100-V-0006.bin"
private noncomputable def vp00001100_7 : Blocks := edgeBlocks% "full/vectors/00001100-V-0007.bin"
private noncomputable def vp00001100_8 : Blocks := edgeBlocks% "full/vectors/00001100-V-0008.bin"
private noncomputable def vp00001100_9 : Blocks := edgeBlocks% "full/vectors/00001100-V-0009.bin"
private noncomputable def vp00001100_10 : Blocks := edgeBlocks% "full/vectors/00001100-V-0010.bin"
private noncomputable def vp00001100_11 : Blocks := edgeBlocks% "full/vectors/00001100-V-0011.bin"
private noncomputable def vp00001100_12 : Blocks := edgeBlocks% "full/vectors/00001100-V-0012.bin"
noncomputable def vp00001100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00001100_0 (Blocks.join vp00001100_1 vp00001100_2)) (Blocks.join vp00001100_3 (Blocks.join vp00001100_4 vp00001100_5))) (Blocks.join (Blocks.join vp00001100_6 (Blocks.join vp00001100_7 vp00001100_8)) (Blocks.join (Blocks.join vp00001100_9 vp00001100_10) (Blocks.join vp00001100_11 vp00001100_12))))
private theorem bp000011000 : Branch 0 (-383761639/32000000 : ℚ) vp00001100 := by
  apply branch_left_normalized (c:=vp000011000) (k:=0) (m:=816) (by decide +kernel)
  rw [show 2*(-383761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-383761639/16000000 : ℚ) by norm_num]
  exact coverp000011000
private noncomputable def ep000011001_0 : Blocks := edgeBlocks% "full/vectors/000011001-E-0000.bin"
private noncomputable def ep000011001_1 : Blocks := edgeBlocks% "full/vectors/000011001-E-0001.bin"
private noncomputable def ep000011001_2 : Blocks := edgeBlocks% "full/vectors/000011001-E-0002.bin"
private noncomputable def ep000011001_3 : Blocks := edgeBlocks% "full/vectors/000011001-E-0003.bin"
private noncomputable def ep000011001_4 : Blocks := edgeBlocks% "full/vectors/000011001-E-0004.bin"
private noncomputable def ep000011001_5 : Blocks := edgeBlocks% "full/vectors/000011001-E-0005.bin"
private noncomputable def ep000011001_6 : Blocks := edgeBlocks% "full/vectors/000011001-E-0006.bin"
private noncomputable def ep000011001_7 : Blocks := edgeBlocks% "full/vectors/000011001-E-0007.bin"
private noncomputable def ep000011001_8 : Blocks := edgeBlocks% "full/vectors/000011001-E-0008.bin"
private noncomputable def ep000011001_9 : Blocks := edgeBlocks% "full/vectors/000011001-E-0009.bin"
private noncomputable def ep000011001_10 : Blocks := edgeBlocks% "full/vectors/000011001-E-0010.bin"
private noncomputable def ep000011001_11 : Blocks := edgeBlocks% "full/vectors/000011001-E-0011.bin"
private noncomputable def ep000011001_12 : Blocks := edgeBlocks% "full/vectors/000011001-E-0012.bin"
noncomputable def ep000011001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000011001_0 (Blocks.join ep000011001_1 ep000011001_2)) (Blocks.join ep000011001_3 (Blocks.join ep000011001_4 ep000011001_5))) (Blocks.join (Blocks.join ep000011001_6 (Blocks.join ep000011001_7 ep000011001_8)) (Blocks.join (Blocks.join ep000011001_9 ep000011001_10) (Blocks.join ep000011001_11 ep000011001_12))))
private theorem idp000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001100.list =
    C ((2:ℤ)^1683) * horner X vp000011001.list + horner X ep000011001.list := by
  exact edge_identity (B := (2:ℤ)^2538) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011001 : Branch 1 (-383761639/32000000 : ℚ) vp00001100 := by
  apply branch_checked idp000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-383761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-399761639/16000000 : ℚ) by norm_num]
  exact coverp000011001
theorem coverp00001100 : Covers (-383761639/32000000 : ℚ) vp00001100 := join_branches bp000011000 bp000011001
private noncomputable def vp0000110_0 : Blocks := edgeBlocks% "full/vectors/0000110-V-0000.bin"
private noncomputable def vp0000110_1 : Blocks := edgeBlocks% "full/vectors/0000110-V-0001.bin"
private noncomputable def vp0000110_2 : Blocks := edgeBlocks% "full/vectors/0000110-V-0002.bin"
private noncomputable def vp0000110_3 : Blocks := edgeBlocks% "full/vectors/0000110-V-0003.bin"
private noncomputable def vp0000110_4 : Blocks := edgeBlocks% "full/vectors/0000110-V-0004.bin"
private noncomputable def vp0000110_5 : Blocks := edgeBlocks% "full/vectors/0000110-V-0005.bin"
private noncomputable def vp0000110_6 : Blocks := edgeBlocks% "full/vectors/0000110-V-0006.bin"
private noncomputable def vp0000110_7 : Blocks := edgeBlocks% "full/vectors/0000110-V-0007.bin"
private noncomputable def vp0000110_8 : Blocks := edgeBlocks% "full/vectors/0000110-V-0008.bin"
private noncomputable def vp0000110_9 : Blocks := edgeBlocks% "full/vectors/0000110-V-0009.bin"
private noncomputable def vp0000110_10 : Blocks := edgeBlocks% "full/vectors/0000110-V-0010.bin"
private noncomputable def vp0000110_11 : Blocks := edgeBlocks% "full/vectors/0000110-V-0011.bin"
private noncomputable def vp0000110_12 : Blocks := edgeBlocks% "full/vectors/0000110-V-0012.bin"
private noncomputable def vp0000110_13 : Blocks := edgeBlocks% "full/vectors/0000110-V-0013.bin"
private noncomputable def vp0000110_14 : Blocks := edgeBlocks% "full/vectors/0000110-V-0014.bin"
private noncomputable def vp0000110_15 : Blocks := edgeBlocks% "full/vectors/0000110-V-0015.bin"
private noncomputable def vp0000110_16 : Blocks := edgeBlocks% "full/vectors/0000110-V-0016.bin"
private noncomputable def vp0000110_17 : Blocks := edgeBlocks% "full/vectors/0000110-V-0017.bin"
private noncomputable def vp0000110_18 : Blocks := edgeBlocks% "full/vectors/0000110-V-0018.bin"
private noncomputable def vp0000110_19 : Blocks := edgeBlocks% "full/vectors/0000110-V-0019.bin"
private noncomputable def vp0000110_20 : Blocks := edgeBlocks% "full/vectors/0000110-V-0020.bin"
private noncomputable def vp0000110_21 : Blocks := edgeBlocks% "full/vectors/0000110-V-0021.bin"
private noncomputable def vp0000110_22 : Blocks := edgeBlocks% "full/vectors/0000110-V-0022.bin"
private noncomputable def vp0000110_23 : Blocks := edgeBlocks% "full/vectors/0000110-V-0023.bin"
private noncomputable def vp0000110_24 : Blocks := edgeBlocks% "full/vectors/0000110-V-0024.bin"
noncomputable def vp0000110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0000110_0 (Blocks.join vp0000110_1 vp0000110_2)) (Blocks.join vp0000110_3 (Blocks.join vp0000110_4 vp0000110_5))) (Blocks.join (Blocks.join vp0000110_6 (Blocks.join vp0000110_7 vp0000110_8)) (Blocks.join vp0000110_9 (Blocks.join vp0000110_10 vp0000110_11)))) (Blocks.join (Blocks.join (Blocks.join vp0000110_12 (Blocks.join vp0000110_13 vp0000110_14)) (Blocks.join vp0000110_15 (Blocks.join vp0000110_16 vp0000110_17))) (Blocks.join (Blocks.join vp0000110_18 (Blocks.join vp0000110_19 vp0000110_20)) (Blocks.join (Blocks.join vp0000110_21 vp0000110_22) (Blocks.join vp0000110_23 vp0000110_24)))))
private theorem bp00001100 : Branch 0 (-383761639/64000000 : ℚ) vp0000110 := by
  apply branch_left_normalized (c:=vp00001100) (k:=0) (m:=1590) (by decide +kernel)
  rw [show 2*(-383761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-383761639/32000000 : ℚ) by norm_num]
  exact coverp00001100
private noncomputable def ep00001101_0 : Blocks := edgeBlocks% "full/vectors/00001101-E-0000.bin"
private noncomputable def ep00001101_1 : Blocks := edgeBlocks% "full/vectors/00001101-E-0001.bin"
private noncomputable def ep00001101_2 : Blocks := edgeBlocks% "full/vectors/00001101-E-0002.bin"
private noncomputable def ep00001101_3 : Blocks := edgeBlocks% "full/vectors/00001101-E-0003.bin"
private noncomputable def ep00001101_4 : Blocks := edgeBlocks% "full/vectors/00001101-E-0004.bin"
private noncomputable def ep00001101_5 : Blocks := edgeBlocks% "full/vectors/00001101-E-0005.bin"
private noncomputable def ep00001101_6 : Blocks := edgeBlocks% "full/vectors/00001101-E-0006.bin"
private noncomputable def ep00001101_7 : Blocks := edgeBlocks% "full/vectors/00001101-E-0007.bin"
private noncomputable def ep00001101_8 : Blocks := edgeBlocks% "full/vectors/00001101-E-0008.bin"
private noncomputable def ep00001101_9 : Blocks := edgeBlocks% "full/vectors/00001101-E-0009.bin"
private noncomputable def ep00001101_10 : Blocks := edgeBlocks% "full/vectors/00001101-E-0010.bin"
private noncomputable def ep00001101_11 : Blocks := edgeBlocks% "full/vectors/00001101-E-0011.bin"
private noncomputable def ep00001101_12 : Blocks := edgeBlocks% "full/vectors/00001101-E-0012.bin"
private noncomputable def ep00001101_13 : Blocks := edgeBlocks% "full/vectors/00001101-E-0013.bin"
private noncomputable def ep00001101_14 : Blocks := edgeBlocks% "full/vectors/00001101-E-0014.bin"
private noncomputable def ep00001101_15 : Blocks := edgeBlocks% "full/vectors/00001101-E-0015.bin"
private noncomputable def ep00001101_16 : Blocks := edgeBlocks% "full/vectors/00001101-E-0016.bin"
private noncomputable def ep00001101_17 : Blocks := edgeBlocks% "full/vectors/00001101-E-0017.bin"
private noncomputable def ep00001101_18 : Blocks := edgeBlocks% "full/vectors/00001101-E-0018.bin"
private noncomputable def ep00001101_19 : Blocks := edgeBlocks% "full/vectors/00001101-E-0019.bin"
private noncomputable def ep00001101_20 : Blocks := edgeBlocks% "full/vectors/00001101-E-0020.bin"
private noncomputable def ep00001101_21 : Blocks := edgeBlocks% "full/vectors/00001101-E-0021.bin"
private noncomputable def ep00001101_22 : Blocks := edgeBlocks% "full/vectors/00001101-E-0022.bin"
private noncomputable def ep00001101_23 : Blocks := edgeBlocks% "full/vectors/00001101-E-0023.bin"
private noncomputable def ep00001101_24 : Blocks := edgeBlocks% "full/vectors/00001101-E-0024.bin"
noncomputable def ep00001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00001101_0 (Blocks.join ep00001101_1 ep00001101_2)) (Blocks.join ep00001101_3 (Blocks.join ep00001101_4 ep00001101_5))) (Blocks.join (Blocks.join ep00001101_6 (Blocks.join ep00001101_7 ep00001101_8)) (Blocks.join ep00001101_9 (Blocks.join ep00001101_10 ep00001101_11)))) (Blocks.join (Blocks.join (Blocks.join ep00001101_12 (Blocks.join ep00001101_13 ep00001101_14)) (Blocks.join ep00001101_15 (Blocks.join ep00001101_16 ep00001101_17))) (Blocks.join (Blocks.join ep00001101_18 (Blocks.join ep00001101_19 ep00001101_20)) (Blocks.join (Blocks.join ep00001101_21 ep00001101_22) (Blocks.join ep00001101_23 ep00001101_24)))))
private def ptsp00001101 : List ℤ := [((2:ℤ)^3896+0),((2:ℤ)^3896+1)]
private theorem boundp00001101 : 2^vp0000110.size*absSum vp0000110.list + ((2:ℤ)^3265*absSum vp00001101.list+absSum ep00001101.list) < (2:ℤ)^4858 := by decide +kernel
private theorem pointp00001101_0 : fastHom 1 ((2:ℤ)^3896+0) vp0000110 = ((2:ℤ)^3265)*vp00001101.subst ((2:ℤ)^3896+0)+ep00001101.subst ((2:ℤ)^3896+0) := by decide +kernel
private theorem pointp00001101_1 : fastHom 1 ((2:ℤ)^3896+1) vp0000110 = ((2:ℤ)^3265)*vp00001101.subst ((2:ℤ)^3896+1)+ep00001101.subst ((2:ℤ)^3896+1) := by decide +kernel
private theorem checkp00001101 (x:ℤ) (hx:x ∈ ptsp00001101) : fastHom 1 x vp0000110 = ((2:ℤ)^3265)*vp00001101.subst x+ep00001101.subst x := by
  simp only [ptsp00001101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp00001101_0
  · exact pointp00001101_1
private theorem idp00001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110.list =
    C ((2:ℤ)^3265) * horner X vp00001101.list + horner X ep00001101.list := by
  apply edge_identity (B := (2:ℤ)^4858) (by decide) (by positivity) (by positivity) boundp00001101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp00001101 (by decide +kernel)
  · have h : ptsp00001101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp00001101.trans_le (by decide +kernel)
  · exact checkp00001101
private theorem bp00001101 : Branch 1 (-383761639/64000000 : ℚ) vp0000110 := by
  apply branch_checked idp00001101 (by positivity) (by decide +kernel)
  rw [show 2*(-383761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-415761639/32000000 : ℚ) by norm_num]
  exact coverp00001101
theorem coverp0000110 : Covers (-383761639/64000000 : ℚ) vp0000110 := join_branches bp00001100 bp00001101
end NextProof.EdgeFull

