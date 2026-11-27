import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00044

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00000110011111_0 : Blocks := edgeBlocks% "full/vectors/00000110011111-V-0000.bin"
noncomputable def vp00000110011111 : Blocks := vp00000110011111_0
theorem coverp00000110011111 : Covers (-207261639/500000 : ℚ) vp00000110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110011110_0 : Blocks := edgeBlocks% "full/vectors/00000110011110-V-0000.bin"
noncomputable def vp00000110011110 : Blocks := vp00000110011110_0
theorem coverp00000110011110 : Covers (-206761639/500000 : ℚ) vp00000110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011001111_0 : Blocks := edgeBlocks% "full/vectors/0000011001111-V-0000.bin"
noncomputable def vp0000011001111 : Blocks := vp0000011001111_0
private theorem bp00000110011110 : Branch 0 (-206761639/1000000 : ℚ) vp0000011001111 := by
  apply branch_left_normalized (c:=vp00000110011110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-206761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-206761639/500000 : ℚ) by norm_num]
  exact coverp00000110011110
private noncomputable def ep00000110011111_0 : Blocks := edgeBlocks% "full/vectors/00000110011111-E-0000.bin"
noncomputable def ep00000110011111 : Blocks := ep00000110011111_0
private theorem idp00000110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011001111.list =
    C ((2:ℤ)^87) * horner X vp00000110011111.list + horner X ep00000110011111.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110011111 : Branch 1 (-206761639/1000000 : ℚ) vp0000011001111 := by
  apply branch_checked idp00000110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-206761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-207261639/500000 : ℚ) by norm_num]
  exact coverp00000110011111
theorem coverp0000011001111 : Covers (-206761639/1000000 : ℚ) vp0000011001111 := join_branches bp00000110011110 bp00000110011111
private noncomputable def vp00000110011101_0 : Blocks := edgeBlocks% "full/vectors/00000110011101-V-0000.bin"
noncomputable def vp00000110011101 : Blocks := vp00000110011101_0
theorem coverp00000110011101 : Covers (-206261639/500000 : ℚ) vp00000110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110011100_0 : Blocks := edgeBlocks% "full/vectors/00000110011100-V-0000.bin"
noncomputable def vp00000110011100 : Blocks := vp00000110011100_0
theorem coverp00000110011100 : Covers (-205761639/500000 : ℚ) vp00000110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011001110_0 : Blocks := edgeBlocks% "full/vectors/0000011001110-V-0000.bin"
noncomputable def vp0000011001110 : Blocks := vp0000011001110_0
private theorem bp00000110011100 : Branch 0 (-205761639/1000000 : ℚ) vp0000011001110 := by
  apply branch_left_normalized (c:=vp00000110011100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-205761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-205761639/500000 : ℚ) by norm_num]
  exact coverp00000110011100
private noncomputable def ep00000110011101_0 : Blocks := edgeBlocks% "full/vectors/00000110011101-E-0000.bin"
noncomputable def ep00000110011101 : Blocks := ep00000110011101_0
private theorem idp00000110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011001110.list =
    C ((2:ℤ)^87) * horner X vp00000110011101.list + horner X ep00000110011101.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110011101 : Branch 1 (-205761639/1000000 : ℚ) vp0000011001110 := by
  apply branch_checked idp00000110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-205761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-206261639/500000 : ℚ) by norm_num]
  exact coverp00000110011101
theorem coverp0000011001110 : Covers (-205761639/1000000 : ℚ) vp0000011001110 := join_branches bp00000110011100 bp00000110011101
private noncomputable def vp000001100111_0 : Blocks := edgeBlocks% "full/vectors/000001100111-V-0000.bin"
private noncomputable def vp000001100111_1 : Blocks := edgeBlocks% "full/vectors/000001100111-V-0001.bin"
noncomputable def vp000001100111 : Blocks := (Blocks.join vp000001100111_0 vp000001100111_1)
private theorem bp0000011001110 : Branch 0 (-205761639/2000000 : ℚ) vp000001100111 := by
  apply branch_left_normalized (c:=vp0000011001110) (k:=0) (m:=83) (by decide +kernel)
  rw [show 2*(-205761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-205761639/1000000 : ℚ) by norm_num]
  exact coverp0000011001110
private noncomputable def ep0000011001111_0 : Blocks := edgeBlocks% "full/vectors/0000011001111-E-0000.bin"
private noncomputable def ep0000011001111_1 : Blocks := edgeBlocks% "full/vectors/0000011001111-E-0001.bin"
noncomputable def ep0000011001111 : Blocks := (Blocks.join ep0000011001111_0 ep0000011001111_1)
private theorem idp0000011001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001100111.list =
    C ((2:ℤ)^159) * horner X vp0000011001111.list + horner X ep0000011001111.list := by
  exact edge_identity (B := (2:ℤ)^316) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011001111 : Branch 1 (-205761639/2000000 : ℚ) vp000001100111 := by
  apply branch_checked idp0000011001111 (by positivity) (by decide +kernel)
  rw [show 2*(-205761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-206761639/1000000 : ℚ) by norm_num]
  exact coverp0000011001111
theorem coverp000001100111 : Covers (-205761639/2000000 : ℚ) vp000001100111 := join_branches bp0000011001110 bp0000011001111
private noncomputable def vp00000110011011_0 : Blocks := edgeBlocks% "full/vectors/00000110011011-V-0000.bin"
noncomputable def vp00000110011011 : Blocks := vp00000110011011_0
theorem coverp00000110011011 : Covers (-205261639/500000 : ℚ) vp00000110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110011010_0 : Blocks := edgeBlocks% "full/vectors/00000110011010-V-0000.bin"
noncomputable def vp00000110011010 : Blocks := vp00000110011010_0
theorem coverp00000110011010 : Covers (-204761639/500000 : ℚ) vp00000110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011001101_0 : Blocks := edgeBlocks% "full/vectors/0000011001101-V-0000.bin"
noncomputable def vp0000011001101 : Blocks := vp0000011001101_0
private theorem bp00000110011010 : Branch 0 (-204761639/1000000 : ℚ) vp0000011001101 := by
  apply branch_left_normalized (c:=vp00000110011010) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-204761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-204761639/500000 : ℚ) by norm_num]
  exact coverp00000110011010
private noncomputable def ep00000110011011_0 : Blocks := edgeBlocks% "full/vectors/00000110011011-E-0000.bin"
noncomputable def ep00000110011011 : Blocks := ep00000110011011_0
private theorem idp00000110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011001101.list =
    C ((2:ℤ)^89) * horner X vp00000110011011.list + horner X ep00000110011011.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110011011 : Branch 1 (-204761639/1000000 : ℚ) vp0000011001101 := by
  apply branch_checked idp00000110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-204761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-205261639/500000 : ℚ) by norm_num]
  exact coverp00000110011011
theorem coverp0000011001101 : Covers (-204761639/1000000 : ℚ) vp0000011001101 := join_branches bp00000110011010 bp00000110011011
private noncomputable def vp00000110011001_0 : Blocks := edgeBlocks% "full/vectors/00000110011001-V-0000.bin"
noncomputable def vp00000110011001 : Blocks := vp00000110011001_0
theorem coverp00000110011001 : Covers (-204261639/500000 : ℚ) vp00000110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110011000_0 : Blocks := edgeBlocks% "full/vectors/00000110011000-V-0000.bin"
noncomputable def vp00000110011000 : Blocks := vp00000110011000_0
theorem coverp00000110011000 : Covers (-203761639/500000 : ℚ) vp00000110011000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011001100_0 : Blocks := edgeBlocks% "full/vectors/0000011001100-V-0000.bin"
noncomputable def vp0000011001100 : Blocks := vp0000011001100_0
private theorem bp00000110011000 : Branch 0 (-203761639/1000000 : ℚ) vp0000011001100 := by
  apply branch_left_normalized (c:=vp00000110011000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-203761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-203761639/500000 : ℚ) by norm_num]
  exact coverp00000110011000
private noncomputable def ep00000110011001_0 : Blocks := edgeBlocks% "full/vectors/00000110011001-E-0000.bin"
noncomputable def ep00000110011001 : Blocks := ep00000110011001_0
private theorem idp00000110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011001100.list =
    C ((2:ℤ)^89) * horner X vp00000110011001.list + horner X ep00000110011001.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110011001 : Branch 1 (-203761639/1000000 : ℚ) vp0000011001100 := by
  apply branch_checked idp00000110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-203761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-204261639/500000 : ℚ) by norm_num]
  exact coverp00000110011001
theorem coverp0000011001100 : Covers (-203761639/1000000 : ℚ) vp0000011001100 := join_branches bp00000110011000 bp00000110011001
private noncomputable def vp000001100110_0 : Blocks := edgeBlocks% "full/vectors/000001100110-V-0000.bin"
private noncomputable def vp000001100110_1 : Blocks := edgeBlocks% "full/vectors/000001100110-V-0001.bin"
noncomputable def vp000001100110 : Blocks := (Blocks.join vp000001100110_0 vp000001100110_1)
private theorem bp0000011001100 : Branch 0 (-203761639/2000000 : ℚ) vp000001100110 := by
  apply branch_left_normalized (c:=vp0000011001100) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-203761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-203761639/1000000 : ℚ) by norm_num]
  exact coverp0000011001100
private noncomputable def ep0000011001101_0 : Blocks := edgeBlocks% "full/vectors/0000011001101-E-0000.bin"
private noncomputable def ep0000011001101_1 : Blocks := edgeBlocks% "full/vectors/0000011001101-E-0001.bin"
noncomputable def ep0000011001101 : Blocks := (Blocks.join ep0000011001101_0 ep0000011001101_1)
private theorem idp0000011001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001100110.list =
    C ((2:ℤ)^160) * horner X vp0000011001101.list + horner X ep0000011001101.list := by
  exact edge_identity (B := (2:ℤ)^319) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011001101 : Branch 1 (-203761639/2000000 : ℚ) vp000001100110 := by
  apply branch_checked idp0000011001101 (by positivity) (by decide +kernel)
  rw [show 2*(-203761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-204761639/1000000 : ℚ) by norm_num]
  exact coverp0000011001101
theorem coverp000001100110 : Covers (-203761639/2000000 : ℚ) vp000001100110 := join_branches bp0000011001100 bp0000011001101
private noncomputable def vp00000110011_0 : Blocks := edgeBlocks% "full/vectors/00000110011-V-0000.bin"
private noncomputable def vp00000110011_1 : Blocks := edgeBlocks% "full/vectors/00000110011-V-0001.bin"
private noncomputable def vp00000110011_2 : Blocks := edgeBlocks% "full/vectors/00000110011-V-0002.bin"
noncomputable def vp00000110011 : Blocks := (Blocks.join vp00000110011_0 (Blocks.join vp00000110011_1 vp00000110011_2))
private theorem bp000001100110 : Branch 0 (-203761639/4000000 : ℚ) vp00000110011 := by
  apply branch_left_normalized (c:=vp000001100110) (k:=0) (m:=153) (by decide +kernel)
  rw [show 2*(-203761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-203761639/2000000 : ℚ) by norm_num]
  exact coverp000001100110
private noncomputable def ep000001100111_0 : Blocks := edgeBlocks% "full/vectors/000001100111-E-0000.bin"
private noncomputable def ep000001100111_1 : Blocks := edgeBlocks% "full/vectors/000001100111-E-0001.bin"
private noncomputable def ep000001100111_2 : Blocks := edgeBlocks% "full/vectors/000001100111-E-0002.bin"
noncomputable def ep000001100111 : Blocks := (Blocks.join ep000001100111_0 (Blocks.join ep000001100111_1 ep000001100111_2))
private theorem idp000001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110011.list =
    C ((2:ℤ)^305) * horner X vp000001100111.list + horner X ep000001100111.list := by
  exact edge_identity (B := (2:ℤ)^530) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100111 : Branch 1 (-203761639/4000000 : ℚ) vp00000110011 := by
  apply branch_checked idp000001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-203761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-205761639/2000000 : ℚ) by norm_num]
  exact coverp000001100111
theorem coverp00000110011 : Covers (-203761639/4000000 : ℚ) vp00000110011 := join_branches bp000001100110 bp000001100111
private noncomputable def vp00000110010111_0 : Blocks := edgeBlocks% "full/vectors/00000110010111-V-0000.bin"
noncomputable def vp00000110010111 : Blocks := vp00000110010111_0
theorem coverp00000110010111 : Covers (-203261639/500000 : ℚ) vp00000110010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110010110_0 : Blocks := edgeBlocks% "full/vectors/00000110010110-V-0000.bin"
noncomputable def vp00000110010110 : Blocks := vp00000110010110_0
theorem coverp00000110010110 : Covers (-202761639/500000 : ℚ) vp00000110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011001011_0 : Blocks := edgeBlocks% "full/vectors/0000011001011-V-0000.bin"
noncomputable def vp0000011001011 : Blocks := vp0000011001011_0
private theorem bp00000110010110 : Branch 0 (-202761639/1000000 : ℚ) vp0000011001011 := by
  apply branch_left_normalized (c:=vp00000110010110) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-202761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-202761639/500000 : ℚ) by norm_num]
  exact coverp00000110010110
private noncomputable def ep00000110010111_0 : Blocks := edgeBlocks% "full/vectors/00000110010111-E-0000.bin"
noncomputable def ep00000110010111 : Blocks := ep00000110010111_0
private theorem idp00000110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011001011.list =
    C ((2:ℤ)^90) * horner X vp00000110010111.list + horner X ep00000110010111.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110010111 : Branch 1 (-202761639/1000000 : ℚ) vp0000011001011 := by
  apply branch_checked idp00000110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-202761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-203261639/500000 : ℚ) by norm_num]
  exact coverp00000110010111
theorem coverp0000011001011 : Covers (-202761639/1000000 : ℚ) vp0000011001011 := join_branches bp00000110010110 bp00000110010111
private noncomputable def vp00000110010101_0 : Blocks := edgeBlocks% "full/vectors/00000110010101-V-0000.bin"
noncomputable def vp00000110010101 : Blocks := vp00000110010101_0
theorem coverp00000110010101 : Covers (-202261639/500000 : ℚ) vp00000110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110010100_0 : Blocks := edgeBlocks% "full/vectors/00000110010100-V-0000.bin"
noncomputable def vp00000110010100 : Blocks := vp00000110010100_0
theorem coverp00000110010100 : Covers (-201761639/500000 : ℚ) vp00000110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000011001010_0 : Blocks := edgeBlocks% "full/vectors/0000011001010-V-0000.bin"
noncomputable def vp0000011001010 : Blocks := vp0000011001010_0
private theorem bp00000110010100 : Branch 0 (-201761639/1000000 : ℚ) vp0000011001010 := by
  apply branch_left_normalized (c:=vp00000110010100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-201761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-201761639/500000 : ℚ) by norm_num]
  exact coverp00000110010100
private noncomputable def ep00000110010101_0 : Blocks := edgeBlocks% "full/vectors/00000110010101-E-0000.bin"
noncomputable def ep00000110010101 : Blocks := ep00000110010101_0
private theorem idp00000110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011001010.list =
    C ((2:ℤ)^92) * horner X vp00000110010101.list + horner X ep00000110010101.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110010101 : Branch 1 (-201761639/1000000 : ℚ) vp0000011001010 := by
  apply branch_checked idp00000110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-201761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-202261639/500000 : ℚ) by norm_num]
  exact coverp00000110010101
theorem coverp0000011001010 : Covers (-201761639/1000000 : ℚ) vp0000011001010 := join_branches bp00000110010100 bp00000110010101
private noncomputable def vp000001100101_0 : Blocks := edgeBlocks% "full/vectors/000001100101-V-0000.bin"
private noncomputable def vp000001100101_1 : Blocks := edgeBlocks% "full/vectors/000001100101-V-0001.bin"
noncomputable def vp000001100101 : Blocks := (Blocks.join vp000001100101_0 vp000001100101_1)
private theorem bp0000011001010 : Branch 0 (-201761639/2000000 : ℚ) vp000001100101 := by
  apply branch_left_normalized (c:=vp0000011001010) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-201761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-201761639/1000000 : ℚ) by norm_num]
  exact coverp0000011001010
private noncomputable def ep0000011001011_0 : Blocks := edgeBlocks% "full/vectors/0000011001011-E-0000.bin"
private noncomputable def ep0000011001011_1 : Blocks := edgeBlocks% "full/vectors/0000011001011-E-0001.bin"
noncomputable def ep0000011001011 : Blocks := (Blocks.join ep0000011001011_0 ep0000011001011_1)
private theorem idp0000011001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001100101.list =
    C ((2:ℤ)^165) * horner X vp0000011001011.list + horner X ep0000011001011.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011001011 : Branch 1 (-201761639/2000000 : ℚ) vp000001100101 := by
  apply branch_checked idp0000011001011 (by positivity) (by decide +kernel)
  rw [show 2*(-201761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-202761639/1000000 : ℚ) by norm_num]
  exact coverp0000011001011
theorem coverp000001100101 : Covers (-201761639/2000000 : ℚ) vp000001100101 := join_branches bp0000011001010 bp0000011001011
private noncomputable def vp00000110010011_0 : Blocks := edgeBlocks% "full/vectors/00000110010011-V-0000.bin"
noncomputable def vp00000110010011 : Blocks := vp00000110010011_0
theorem coverp00000110010011 : Covers (-201261639/500000 : ℚ) vp00000110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100100101_0 : Blocks := edgeBlocks% "full/vectors/000001100100101-V-0000.bin"
noncomputable def vp000001100100101 : Blocks := vp000001100100101_0
theorem coverp000001100100101 : Covers (-201011639/250000 : ℚ) vp000001100100101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100100100_0 : Blocks := edgeBlocks% "full/vectors/000001100100100-V-0000.bin"
noncomputable def vp000001100100100 : Blocks := vp000001100100100_0
theorem coverp000001100100100 : Covers (-200761639/250000 : ℚ) vp000001100100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110010010_0 : Blocks := edgeBlocks% "full/vectors/00000110010010-V-0000.bin"
noncomputable def vp00000110010010 : Blocks := vp00000110010010_0
private theorem bp000001100100100 : Branch 0 (-200761639/500000 : ℚ) vp00000110010010 := by
  apply branch_left_normalized (c:=vp000001100100100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-200761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-200761639/250000 : ℚ) by norm_num]
  exact coverp000001100100100
private noncomputable def ep000001100100101_0 : Blocks := edgeBlocks% "full/vectors/000001100100101-E-0000.bin"
noncomputable def ep000001100100101 : Blocks := ep000001100100101_0
private theorem idp000001100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110010010.list =
    C ((2:ℤ)^58) * horner X vp000001100100101.list + horner X ep000001100100101.list := by
  exact edge_identity (B := (2:ℤ)^174) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100100101 : Branch 1 (-200761639/500000 : ℚ) vp00000110010010 := by
  apply branch_checked idp000001100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-200761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-201011639/250000 : ℚ) by norm_num]
  exact coverp000001100100101
theorem coverp00000110010010 : Covers (-200761639/500000 : ℚ) vp00000110010010 := join_branches bp000001100100100 bp000001100100101
private noncomputable def vp0000011001001_0 : Blocks := edgeBlocks% "full/vectors/0000011001001-V-0000.bin"
noncomputable def vp0000011001001 : Blocks := vp0000011001001_0
private theorem bp00000110010010 : Branch 0 (-200761639/1000000 : ℚ) vp0000011001001 := by
  apply branch_left_normalized (c:=vp00000110010010) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-200761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-200761639/500000 : ℚ) by norm_num]
  exact coverp00000110010010
private noncomputable def ep00000110010011_0 : Blocks := edgeBlocks% "full/vectors/00000110010011-E-0000.bin"
noncomputable def ep00000110010011 : Blocks := ep00000110010011_0
private theorem idp00000110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011001001.list =
    C ((2:ℤ)^96) * horner X vp00000110010011.list + horner X ep00000110010011.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110010011 : Branch 1 (-200761639/1000000 : ℚ) vp0000011001001 := by
  apply branch_checked idp00000110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-200761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-201261639/500000 : ℚ) by norm_num]
  exact coverp00000110010011
theorem coverp0000011001001 : Covers (-200761639/1000000 : ℚ) vp0000011001001 := join_branches bp00000110010010 bp00000110010011
private noncomputable def vp000001100100011_0 : Blocks := edgeBlocks% "full/vectors/000001100100011-V-0000.bin"
noncomputable def vp000001100100011 : Blocks := vp000001100100011_0
theorem coverp000001100100011 : Covers (-200511639/250000 : ℚ) vp000001100100011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100100010_0 : Blocks := edgeBlocks% "full/vectors/000001100100010-V-0000.bin"
noncomputable def vp000001100100010 : Blocks := vp000001100100010_0
theorem coverp000001100100010 : Covers (-200261639/250000 : ℚ) vp000001100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110010001_0 : Blocks := edgeBlocks% "full/vectors/00000110010001-V-0000.bin"
noncomputable def vp00000110010001 : Blocks := vp00000110010001_0
private theorem bp000001100100010 : Branch 0 (-200261639/500000 : ℚ) vp00000110010001 := by
  apply branch_left_normalized (c:=vp000001100100010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-200261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-200261639/250000 : ℚ) by norm_num]
  exact coverp000001100100010
private noncomputable def ep000001100100011_0 : Blocks := edgeBlocks% "full/vectors/000001100100011-E-0000.bin"
noncomputable def ep000001100100011 : Blocks := ep000001100100011_0
private theorem idp000001100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110010001.list =
    C ((2:ℤ)^56) * horner X vp000001100100011.list + horner X ep000001100100011.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100100011 : Branch 1 (-200261639/500000 : ℚ) vp00000110010001 := by
  apply branch_checked idp000001100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-200261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-200511639/250000 : ℚ) by norm_num]
  exact coverp000001100100011
theorem coverp00000110010001 : Covers (-200261639/500000 : ℚ) vp00000110010001 := join_branches bp000001100100010 bp000001100100011
private noncomputable def vp000001100100001_0 : Blocks := edgeBlocks% "full/vectors/000001100100001-V-0000.bin"
noncomputable def vp000001100100001 : Blocks := vp000001100100001_0
theorem coverp000001100100001 : Covers (-200011639/250000 : ℚ) vp000001100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100100000_0 : Blocks := edgeBlocks% "full/vectors/000001100100000-V-0000.bin"
noncomputable def vp000001100100000 : Blocks := vp000001100100000_0
theorem coverp000001100100000 : Covers (-199761639/250000 : ℚ) vp000001100100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110010000_0 : Blocks := edgeBlocks% "full/vectors/00000110010000-V-0000.bin"
noncomputable def vp00000110010000 : Blocks := vp00000110010000_0
private theorem bp000001100100000 : Branch 0 (-199761639/500000 : ℚ) vp00000110010000 := by
  apply branch_left_normalized (c:=vp000001100100000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-199761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-199761639/250000 : ℚ) by norm_num]
  exact coverp000001100100000
private noncomputable def ep000001100100001_0 : Blocks := edgeBlocks% "full/vectors/000001100100001-E-0000.bin"
noncomputable def ep000001100100001 : Blocks := ep000001100100001_0
private theorem idp000001100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110010000.list =
    C ((2:ℤ)^55) * horner X vp000001100100001.list + horner X ep000001100100001.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100100001 : Branch 1 (-199761639/500000 : ℚ) vp00000110010000 := by
  apply branch_checked idp000001100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-199761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-200011639/250000 : ℚ) by norm_num]
  exact coverp000001100100001
theorem coverp00000110010000 : Covers (-199761639/500000 : ℚ) vp00000110010000 := join_branches bp000001100100000 bp000001100100001
private noncomputable def vp0000011001000_0 : Blocks := edgeBlocks% "full/vectors/0000011001000-V-0000.bin"
noncomputable def vp0000011001000 : Blocks := vp0000011001000_0
private theorem bp00000110010000 : Branch 0 (-199761639/1000000 : ℚ) vp0000011001000 := by
  apply branch_left_normalized (c:=vp00000110010000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-199761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-199761639/500000 : ℚ) by norm_num]
  exact coverp00000110010000
private noncomputable def ep00000110010001_0 : Blocks := edgeBlocks% "full/vectors/00000110010001-E-0000.bin"
noncomputable def ep00000110010001 : Blocks := ep00000110010001_0
private theorem idp00000110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011001000.list =
    C ((2:ℤ)^91) * horner X vp00000110010001.list + horner X ep00000110010001.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110010001 : Branch 1 (-199761639/1000000 : ℚ) vp0000011001000 := by
  apply branch_checked idp00000110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-199761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-200261639/500000 : ℚ) by norm_num]
  exact coverp00000110010001
theorem coverp0000011001000 : Covers (-199761639/1000000 : ℚ) vp0000011001000 := join_branches bp00000110010000 bp00000110010001
private noncomputable def vp000001100100_0 : Blocks := edgeBlocks% "full/vectors/000001100100-V-0000.bin"
private noncomputable def vp000001100100_1 : Blocks := edgeBlocks% "full/vectors/000001100100-V-0001.bin"
noncomputable def vp000001100100 : Blocks := (Blocks.join vp000001100100_0 vp000001100100_1)
private theorem bp0000011001000 : Branch 0 (-199761639/2000000 : ℚ) vp000001100100 := by
  apply branch_left_normalized (c:=vp0000011001000) (k:=0) (m:=89) (by decide +kernel)
  rw [show 2*(-199761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-199761639/1000000 : ℚ) by norm_num]
  exact coverp0000011001000
private noncomputable def ep0000011001001_0 : Blocks := edgeBlocks% "full/vectors/0000011001001-E-0000.bin"
private noncomputable def ep0000011001001_1 : Blocks := edgeBlocks% "full/vectors/0000011001001-E-0001.bin"
noncomputable def ep0000011001001 : Blocks := (Blocks.join ep0000011001001_0 ep0000011001001_1)
private theorem idp0000011001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001100100.list =
    C ((2:ℤ)^166) * horner X vp0000011001001.list + horner X ep0000011001001.list := by
  exact edge_identity (B := (2:ℤ)^334) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011001001 : Branch 1 (-199761639/2000000 : ℚ) vp000001100100 := by
  apply branch_checked idp0000011001001 (by positivity) (by decide +kernel)
  rw [show 2*(-199761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-200761639/1000000 : ℚ) by norm_num]
  exact coverp0000011001001
theorem coverp000001100100 : Covers (-199761639/2000000 : ℚ) vp000001100100 := join_branches bp0000011001000 bp0000011001001
private noncomputable def vp00000110010_0 : Blocks := edgeBlocks% "full/vectors/00000110010-V-0000.bin"
private noncomputable def vp00000110010_1 : Blocks := edgeBlocks% "full/vectors/00000110010-V-0001.bin"
private noncomputable def vp00000110010_2 : Blocks := edgeBlocks% "full/vectors/00000110010-V-0002.bin"
noncomputable def vp00000110010 : Blocks := (Blocks.join vp00000110010_0 (Blocks.join vp00000110010_1 vp00000110010_2))
private theorem bp000001100100 : Branch 0 (-199761639/4000000 : ℚ) vp00000110010 := by
  apply branch_left_normalized (c:=vp000001100100) (k:=0) (m:=160) (by decide +kernel)
  rw [show 2*(-199761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-199761639/2000000 : ℚ) by norm_num]
  exact coverp000001100100
private noncomputable def ep000001100101_0 : Blocks := edgeBlocks% "full/vectors/000001100101-E-0000.bin"
private noncomputable def ep000001100101_1 : Blocks := edgeBlocks% "full/vectors/000001100101-E-0001.bin"
private noncomputable def ep000001100101_2 : Blocks := edgeBlocks% "full/vectors/000001100101-E-0002.bin"
noncomputable def ep000001100101 : Blocks := (Blocks.join ep000001100101_0 (Blocks.join ep000001100101_1 ep000001100101_2))
private theorem idp000001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110010.list =
    C ((2:ℤ)^315) * horner X vp000001100101.list + horner X ep000001100101.list := by
  exact edge_identity (B := (2:ℤ)^546) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100101 : Branch 1 (-199761639/4000000 : ℚ) vp00000110010 := by
  apply branch_checked idp000001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-199761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-201761639/2000000 : ℚ) by norm_num]
  exact coverp000001100101
theorem coverp00000110010 : Covers (-199761639/4000000 : ℚ) vp00000110010 := join_branches bp000001100100 bp000001100101
private noncomputable def vp0000011001_0 : Blocks := edgeBlocks% "full/vectors/0000011001-V-0000.bin"
private noncomputable def vp0000011001_1 : Blocks := edgeBlocks% "full/vectors/0000011001-V-0001.bin"
private noncomputable def vp0000011001_2 : Blocks := edgeBlocks% "full/vectors/0000011001-V-0002.bin"
private noncomputable def vp0000011001_3 : Blocks := edgeBlocks% "full/vectors/0000011001-V-0003.bin"
private noncomputable def vp0000011001_4 : Blocks := edgeBlocks% "full/vectors/0000011001-V-0004.bin"
noncomputable def vp0000011001 : Blocks := (Blocks.join (Blocks.join vp0000011001_0 vp0000011001_1) (Blocks.join vp0000011001_2 (Blocks.join vp0000011001_3 vp0000011001_4)))
private theorem bp00000110010 : Branch 0 (-199761639/8000000 : ℚ) vp0000011001 := by
  apply branch_left_normalized (c:=vp00000110010) (k:=0) (m:=298) (by decide +kernel)
  rw [show 2*(-199761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-199761639/4000000 : ℚ) by norm_num]
  exact coverp00000110010
private noncomputable def ep00000110011_0 : Blocks := edgeBlocks% "full/vectors/00000110011-E-0000.bin"
private noncomputable def ep00000110011_1 : Blocks := edgeBlocks% "full/vectors/00000110011-E-0001.bin"
private noncomputable def ep00000110011_2 : Blocks := edgeBlocks% "full/vectors/00000110011-E-0002.bin"
private noncomputable def ep00000110011_3 : Blocks := edgeBlocks% "full/vectors/00000110011-E-0003.bin"
private noncomputable def ep00000110011_4 : Blocks := edgeBlocks% "full/vectors/00000110011-E-0004.bin"
noncomputable def ep00000110011 : Blocks := (Blocks.join (Blocks.join ep00000110011_0 ep00000110011_1) (Blocks.join ep00000110011_2 (Blocks.join ep00000110011_3 ep00000110011_4)))
private theorem idp00000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011001.list =
    C ((2:ℤ)^605) * horner X vp00000110011.list + horner X ep00000110011.list := by
  exact edge_identity (B := (2:ℤ)^968) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110011 : Branch 1 (-199761639/8000000 : ℚ) vp0000011001 := by
  apply branch_checked idp00000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-199761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-203761639/4000000 : ℚ) by norm_num]
  exact coverp00000110011
theorem coverp0000011001 : Covers (-199761639/8000000 : ℚ) vp0000011001 := join_branches bp00000110010 bp00000110011
private noncomputable def vp000001100011111_0 : Blocks := edgeBlocks% "full/vectors/000001100011111-V-0000.bin"
noncomputable def vp000001100011111 : Blocks := vp000001100011111_0
theorem coverp000001100011111 : Covers (-199511639/250000 : ℚ) vp000001100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100011110_0 : Blocks := edgeBlocks% "full/vectors/000001100011110-V-0000.bin"
noncomputable def vp000001100011110 : Blocks := vp000001100011110_0
theorem coverp000001100011110 : Covers (-199261639/250000 : ℚ) vp000001100011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110001111_0 : Blocks := edgeBlocks% "full/vectors/00000110001111-V-0000.bin"
noncomputable def vp00000110001111 : Blocks := vp00000110001111_0
private theorem bp000001100011110 : Branch 0 (-199261639/500000 : ℚ) vp00000110001111 := by
  apply branch_left_normalized (c:=vp000001100011110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-199261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-199261639/250000 : ℚ) by norm_num]
  exact coverp000001100011110
private noncomputable def ep000001100011111_0 : Blocks := edgeBlocks% "full/vectors/000001100011111-E-0000.bin"
noncomputable def ep000001100011111 : Blocks := ep000001100011111_0
private theorem idp000001100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110001111.list =
    C ((2:ℤ)^55) * horner X vp000001100011111.list + horner X ep000001100011111.list := by
  exact edge_identity (B := (2:ℤ)^171) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100011111 : Branch 1 (-199261639/500000 : ℚ) vp00000110001111 := by
  apply branch_checked idp000001100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-199261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-199511639/250000 : ℚ) by norm_num]
  exact coverp000001100011111
theorem coverp00000110001111 : Covers (-199261639/500000 : ℚ) vp00000110001111 := join_branches bp000001100011110 bp000001100011111
private noncomputable def vp000001100011101_0 : Blocks := edgeBlocks% "full/vectors/000001100011101-V-0000.bin"
noncomputable def vp000001100011101 : Blocks := vp000001100011101_0
theorem coverp000001100011101 : Covers (-199011639/250000 : ℚ) vp000001100011101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100011100_0 : Blocks := edgeBlocks% "full/vectors/000001100011100-V-0000.bin"
noncomputable def vp000001100011100 : Blocks := vp000001100011100_0
theorem coverp000001100011100 : Covers (-198761639/250000 : ℚ) vp000001100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110001110_0 : Blocks := edgeBlocks% "full/vectors/00000110001110-V-0000.bin"
noncomputable def vp00000110001110 : Blocks := vp00000110001110_0
private theorem bp000001100011100 : Branch 0 (-198761639/500000 : ℚ) vp00000110001110 := by
  apply branch_left_normalized (c:=vp000001100011100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-198761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-198761639/250000 : ℚ) by norm_num]
  exact coverp000001100011100
private noncomputable def ep000001100011101_0 : Blocks := edgeBlocks% "full/vectors/000001100011101-E-0000.bin"
noncomputable def ep000001100011101 : Blocks := ep000001100011101_0
private theorem idp000001100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110001110.list =
    C ((2:ℤ)^56) * horner X vp000001100011101.list + horner X ep000001100011101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100011101 : Branch 1 (-198761639/500000 : ℚ) vp00000110001110 := by
  apply branch_checked idp000001100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-198761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-199011639/250000 : ℚ) by norm_num]
  exact coverp000001100011101
theorem coverp00000110001110 : Covers (-198761639/500000 : ℚ) vp00000110001110 := join_branches bp000001100011100 bp000001100011101
private noncomputable def vp0000011000111_0 : Blocks := edgeBlocks% "full/vectors/0000011000111-V-0000.bin"
noncomputable def vp0000011000111 : Blocks := vp0000011000111_0
private theorem bp00000110001110 : Branch 0 (-198761639/1000000 : ℚ) vp0000011000111 := by
  apply branch_left_normalized (c:=vp00000110001110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-198761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-198761639/500000 : ℚ) by norm_num]
  exact coverp00000110001110
private noncomputable def ep00000110001111_0 : Blocks := edgeBlocks% "full/vectors/00000110001111-E-0000.bin"
noncomputable def ep00000110001111 : Blocks := ep00000110001111_0
private theorem idp00000110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011000111.list =
    C ((2:ℤ)^93) * horner X vp00000110001111.list + horner X ep00000110001111.list := by
  exact edge_identity (B := (2:ℤ)^226) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110001111 : Branch 1 (-198761639/1000000 : ℚ) vp0000011000111 := by
  apply branch_checked idp00000110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-198761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-199261639/500000 : ℚ) by norm_num]
  exact coverp00000110001111
theorem coverp0000011000111 : Covers (-198761639/1000000 : ℚ) vp0000011000111 := join_branches bp00000110001110 bp00000110001111
private noncomputable def vp000001100011011_0 : Blocks := edgeBlocks% "full/vectors/000001100011011-V-0000.bin"
noncomputable def vp000001100011011 : Blocks := vp000001100011011_0
theorem coverp000001100011011 : Covers (-198511639/250000 : ℚ) vp000001100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100011010_0 : Blocks := edgeBlocks% "full/vectors/000001100011010-V-0000.bin"
noncomputable def vp000001100011010 : Blocks := vp000001100011010_0
theorem coverp000001100011010 : Covers (-198261639/250000 : ℚ) vp000001100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110001101_0 : Blocks := edgeBlocks% "full/vectors/00000110001101-V-0000.bin"
noncomputable def vp00000110001101 : Blocks := vp00000110001101_0
private theorem bp000001100011010 : Branch 0 (-198261639/500000 : ℚ) vp00000110001101 := by
  apply branch_left_normalized (c:=vp000001100011010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-198261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-198261639/250000 : ℚ) by norm_num]
  exact coverp000001100011010
private noncomputable def ep000001100011011_0 : Blocks := edgeBlocks% "full/vectors/000001100011011-E-0000.bin"
noncomputable def ep000001100011011 : Blocks := ep000001100011011_0
private theorem idp000001100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110001101.list =
    C ((2:ℤ)^56) * horner X vp000001100011011.list + horner X ep000001100011011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100011011 : Branch 1 (-198261639/500000 : ℚ) vp00000110001101 := by
  apply branch_checked idp000001100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-198261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-198511639/250000 : ℚ) by norm_num]
  exact coverp000001100011011
theorem coverp00000110001101 : Covers (-198261639/500000 : ℚ) vp00000110001101 := join_branches bp000001100011010 bp000001100011011
private noncomputable def vp000001100011001_0 : Blocks := edgeBlocks% "full/vectors/000001100011001-V-0000.bin"
noncomputable def vp000001100011001 : Blocks := vp000001100011001_0
theorem coverp000001100011001 : Covers (-198011639/250000 : ℚ) vp000001100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100011000_0 : Blocks := edgeBlocks% "full/vectors/000001100011000-V-0000.bin"
noncomputable def vp000001100011000 : Blocks := vp000001100011000_0
theorem coverp000001100011000 : Covers (-197761639/250000 : ℚ) vp000001100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110001100_0 : Blocks := edgeBlocks% "full/vectors/00000110001100-V-0000.bin"
noncomputable def vp00000110001100 : Blocks := vp00000110001100_0
private theorem bp000001100011000 : Branch 0 (-197761639/500000 : ℚ) vp00000110001100 := by
  apply branch_left_normalized (c:=vp000001100011000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-197761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-197761639/250000 : ℚ) by norm_num]
  exact coverp000001100011000
private noncomputable def ep000001100011001_0 : Blocks := edgeBlocks% "full/vectors/000001100011001-E-0000.bin"
noncomputable def ep000001100011001 : Blocks := ep000001100011001_0
private theorem idp000001100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110001100.list =
    C ((2:ℤ)^56) * horner X vp000001100011001.list + horner X ep000001100011001.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100011001 : Branch 1 (-197761639/500000 : ℚ) vp00000110001100 := by
  apply branch_checked idp000001100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-197761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-198011639/250000 : ℚ) by norm_num]
  exact coverp000001100011001
theorem coverp00000110001100 : Covers (-197761639/500000 : ℚ) vp00000110001100 := join_branches bp000001100011000 bp000001100011001
private noncomputable def vp0000011000110_0 : Blocks := edgeBlocks% "full/vectors/0000011000110-V-0000.bin"
noncomputable def vp0000011000110 : Blocks := vp0000011000110_0
private theorem bp00000110001100 : Branch 0 (-197761639/1000000 : ℚ) vp0000011000110 := by
  apply branch_left_normalized (c:=vp00000110001100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-197761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-197761639/500000 : ℚ) by norm_num]
  exact coverp00000110001100
private noncomputable def ep00000110001101_0 : Blocks := edgeBlocks% "full/vectors/00000110001101-E-0000.bin"
noncomputable def ep00000110001101 : Blocks := ep00000110001101_0
private theorem idp00000110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011000110.list =
    C ((2:ℤ)^94) * horner X vp00000110001101.list + horner X ep00000110001101.list := by
  exact edge_identity (B := (2:ℤ)^227) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110001101 : Branch 1 (-197761639/1000000 : ℚ) vp0000011000110 := by
  apply branch_checked idp00000110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-197761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-198261639/500000 : ℚ) by norm_num]
  exact coverp00000110001101
theorem coverp0000011000110 : Covers (-197761639/1000000 : ℚ) vp0000011000110 := join_branches bp00000110001100 bp00000110001101
private noncomputable def vp000001100011_0 : Blocks := edgeBlocks% "full/vectors/000001100011-V-0000.bin"
private noncomputable def vp000001100011_1 : Blocks := edgeBlocks% "full/vectors/000001100011-V-0001.bin"
noncomputable def vp000001100011 : Blocks := (Blocks.join vp000001100011_0 vp000001100011_1)
private theorem bp0000011000110 : Branch 0 (-197761639/2000000 : ℚ) vp000001100011 := by
  apply branch_left_normalized (c:=vp0000011000110) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-197761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-197761639/1000000 : ℚ) by norm_num]
  exact coverp0000011000110
private noncomputable def ep0000011000111_0 : Blocks := edgeBlocks% "full/vectors/0000011000111-E-0000.bin"
private noncomputable def ep0000011000111_1 : Blocks := edgeBlocks% "full/vectors/0000011000111-E-0001.bin"
noncomputable def ep0000011000111 : Blocks := (Blocks.join ep0000011000111_0 ep0000011000111_1)
private theorem idp0000011000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001100011.list =
    C ((2:ℤ)^167) * horner X vp0000011000111.list + horner X ep0000011000111.list := by
  exact edge_identity (B := (2:ℤ)^334) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011000111 : Branch 1 (-197761639/2000000 : ℚ) vp000001100011 := by
  apply branch_checked idp0000011000111 (by positivity) (by decide +kernel)
  rw [show 2*(-197761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-198761639/1000000 : ℚ) by norm_num]
  exact coverp0000011000111
theorem coverp000001100011 : Covers (-197761639/2000000 : ℚ) vp000001100011 := join_branches bp0000011000110 bp0000011000111
private noncomputable def vp000001100010111_0 : Blocks := edgeBlocks% "full/vectors/000001100010111-V-0000.bin"
noncomputable def vp000001100010111 : Blocks := vp000001100010111_0
theorem coverp000001100010111 : Covers (-197511639/250000 : ℚ) vp000001100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100010110_0 : Blocks := edgeBlocks% "full/vectors/000001100010110-V-0000.bin"
noncomputable def vp000001100010110 : Blocks := vp000001100010110_0
theorem coverp000001100010110 : Covers (-197261639/250000 : ℚ) vp000001100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110001011_0 : Blocks := edgeBlocks% "full/vectors/00000110001011-V-0000.bin"
noncomputable def vp00000110001011 : Blocks := vp00000110001011_0
private theorem bp000001100010110 : Branch 0 (-197261639/500000 : ℚ) vp00000110001011 := by
  apply branch_left_normalized (c:=vp000001100010110) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-197261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-197261639/250000 : ℚ) by norm_num]
  exact coverp000001100010110
private noncomputable def ep000001100010111_0 : Blocks := edgeBlocks% "full/vectors/000001100010111-E-0000.bin"
noncomputable def ep000001100010111 : Blocks := ep000001100010111_0
private theorem idp000001100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110001011.list =
    C ((2:ℤ)^58) * horner X vp000001100010111.list + horner X ep000001100010111.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100010111 : Branch 1 (-197261639/500000 : ℚ) vp00000110001011 := by
  apply branch_checked idp000001100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-197261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-197511639/250000 : ℚ) by norm_num]
  exact coverp000001100010111
theorem coverp00000110001011 : Covers (-197261639/500000 : ℚ) vp00000110001011 := join_branches bp000001100010110 bp000001100010111
private noncomputable def vp000001100010101_0 : Blocks := edgeBlocks% "full/vectors/000001100010101-V-0000.bin"
noncomputable def vp000001100010101 : Blocks := vp000001100010101_0
theorem coverp000001100010101 : Covers (-197011639/250000 : ℚ) vp000001100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100010100_0 : Blocks := edgeBlocks% "full/vectors/000001100010100-V-0000.bin"
noncomputable def vp000001100010100 : Blocks := vp000001100010100_0
theorem coverp000001100010100 : Covers (-196761639/250000 : ℚ) vp000001100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110001010_0 : Blocks := edgeBlocks% "full/vectors/00000110001010-V-0000.bin"
noncomputable def vp00000110001010 : Blocks := vp00000110001010_0
private theorem bp000001100010100 : Branch 0 (-196761639/500000 : ℚ) vp00000110001010 := by
  apply branch_left_normalized (c:=vp000001100010100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-196761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-196761639/250000 : ℚ) by norm_num]
  exact coverp000001100010100
private noncomputable def ep000001100010101_0 : Blocks := edgeBlocks% "full/vectors/000001100010101-E-0000.bin"
noncomputable def ep000001100010101 : Blocks := ep000001100010101_0
private theorem idp000001100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110001010.list =
    C ((2:ℤ)^58) * horner X vp000001100010101.list + horner X ep000001100010101.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100010101 : Branch 1 (-196761639/500000 : ℚ) vp00000110001010 := by
  apply branch_checked idp000001100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-196761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-197011639/250000 : ℚ) by norm_num]
  exact coverp000001100010101
theorem coverp00000110001010 : Covers (-196761639/500000 : ℚ) vp00000110001010 := join_branches bp000001100010100 bp000001100010101
private noncomputable def vp0000011000101_0 : Blocks := edgeBlocks% "full/vectors/0000011000101-V-0000.bin"
noncomputable def vp0000011000101 : Blocks := vp0000011000101_0
private theorem bp00000110001010 : Branch 0 (-196761639/1000000 : ℚ) vp0000011000101 := by
  apply branch_left_normalized (c:=vp00000110001010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-196761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-196761639/500000 : ℚ) by norm_num]
  exact coverp00000110001010
private noncomputable def ep00000110001011_0 : Blocks := edgeBlocks% "full/vectors/00000110001011-E-0000.bin"
noncomputable def ep00000110001011 : Blocks := ep00000110001011_0
private theorem idp00000110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011000101.list =
    C ((2:ℤ)^97) * horner X vp00000110001011.list + horner X ep00000110001011.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110001011 : Branch 1 (-196761639/1000000 : ℚ) vp0000011000101 := by
  apply branch_checked idp00000110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-196761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-197261639/500000 : ℚ) by norm_num]
  exact coverp00000110001011
theorem coverp0000011000101 : Covers (-196761639/1000000 : ℚ) vp0000011000101 := join_branches bp00000110001010 bp00000110001011
private noncomputable def vp000001100010011_0 : Blocks := edgeBlocks% "full/vectors/000001100010011-V-0000.bin"
noncomputable def vp000001100010011 : Blocks := vp000001100010011_0
theorem coverp000001100010011 : Covers (-196511639/250000 : ℚ) vp000001100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100010010_0 : Blocks := edgeBlocks% "full/vectors/000001100010010-V-0000.bin"
noncomputable def vp000001100010010 : Blocks := vp000001100010010_0
theorem coverp000001100010010 : Covers (-196261639/250000 : ℚ) vp000001100010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110001001_0 : Blocks := edgeBlocks% "full/vectors/00000110001001-V-0000.bin"
noncomputable def vp00000110001001 : Blocks := vp00000110001001_0
private theorem bp000001100010010 : Branch 0 (-196261639/500000 : ℚ) vp00000110001001 := by
  apply branch_left_normalized (c:=vp000001100010010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-196261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-196261639/250000 : ℚ) by norm_num]
  exact coverp000001100010010
private noncomputable def ep000001100010011_0 : Blocks := edgeBlocks% "full/vectors/000001100010011-E-0000.bin"
noncomputable def ep000001100010011 : Blocks := ep000001100010011_0
private theorem idp000001100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110001001.list =
    C ((2:ℤ)^57) * horner X vp000001100010011.list + horner X ep000001100010011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100010011 : Branch 1 (-196261639/500000 : ℚ) vp00000110001001 := by
  apply branch_checked idp000001100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-196261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-196511639/250000 : ℚ) by norm_num]
  exact coverp000001100010011
theorem coverp00000110001001 : Covers (-196261639/500000 : ℚ) vp00000110001001 := join_branches bp000001100010010 bp000001100010011
private noncomputable def vp000001100010001_0 : Blocks := edgeBlocks% "full/vectors/000001100010001-V-0000.bin"
noncomputable def vp000001100010001 : Blocks := vp000001100010001_0
theorem coverp000001100010001 : Covers (-196011639/250000 : ℚ) vp000001100010001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100010000_0 : Blocks := edgeBlocks% "full/vectors/000001100010000-V-0000.bin"
noncomputable def vp000001100010000 : Blocks := vp000001100010000_0
theorem coverp000001100010000 : Covers (-195761639/250000 : ℚ) vp000001100010000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110001000_0 : Blocks := edgeBlocks% "full/vectors/00000110001000-V-0000.bin"
noncomputable def vp00000110001000 : Blocks := vp00000110001000_0
private theorem bp000001100010000 : Branch 0 (-195761639/500000 : ℚ) vp00000110001000 := by
  apply branch_left_normalized (c:=vp000001100010000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-195761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-195761639/250000 : ℚ) by norm_num]
  exact coverp000001100010000
private noncomputable def ep000001100010001_0 : Blocks := edgeBlocks% "full/vectors/000001100010001-E-0000.bin"
noncomputable def ep000001100010001 : Blocks := ep000001100010001_0
private theorem idp000001100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110001000.list =
    C ((2:ℤ)^57) * horner X vp000001100010001.list + horner X ep000001100010001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100010001 : Branch 1 (-195761639/500000 : ℚ) vp00000110001000 := by
  apply branch_checked idp000001100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-195761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-196011639/250000 : ℚ) by norm_num]
  exact coverp000001100010001
theorem coverp00000110001000 : Covers (-195761639/500000 : ℚ) vp00000110001000 := join_branches bp000001100010000 bp000001100010001
private noncomputable def vp0000011000100_0 : Blocks := edgeBlocks% "full/vectors/0000011000100-V-0000.bin"
noncomputable def vp0000011000100 : Blocks := vp0000011000100_0
private theorem bp00000110001000 : Branch 0 (-195761639/1000000 : ℚ) vp0000011000100 := by
  apply branch_left_normalized (c:=vp00000110001000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-195761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-195761639/500000 : ℚ) by norm_num]
  exact coverp00000110001000
private noncomputable def ep00000110001001_0 : Blocks := edgeBlocks% "full/vectors/00000110001001-E-0000.bin"
noncomputable def ep00000110001001 : Blocks := ep00000110001001_0
private theorem idp00000110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011000100.list =
    C ((2:ℤ)^95) * horner X vp00000110001001.list + horner X ep00000110001001.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110001001 : Branch 1 (-195761639/1000000 : ℚ) vp0000011000100 := by
  apply branch_checked idp00000110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-195761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-196261639/500000 : ℚ) by norm_num]
  exact coverp00000110001001
theorem coverp0000011000100 : Covers (-195761639/1000000 : ℚ) vp0000011000100 := join_branches bp00000110001000 bp00000110001001
private noncomputable def vp000001100010_0 : Blocks := edgeBlocks% "full/vectors/000001100010-V-0000.bin"
private noncomputable def vp000001100010_1 : Blocks := edgeBlocks% "full/vectors/000001100010-V-0001.bin"
noncomputable def vp000001100010 : Blocks := (Blocks.join vp000001100010_0 vp000001100010_1)
private theorem bp0000011000100 : Branch 0 (-195761639/2000000 : ℚ) vp000001100010 := by
  apply branch_left_normalized (c:=vp0000011000100) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-195761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-195761639/1000000 : ℚ) by norm_num]
  exact coverp0000011000100
private noncomputable def ep0000011000101_0 : Blocks := edgeBlocks% "full/vectors/0000011000101-E-0000.bin"
private noncomputable def ep0000011000101_1 : Blocks := edgeBlocks% "full/vectors/0000011000101-E-0001.bin"
noncomputable def ep0000011000101 : Blocks := (Blocks.join ep0000011000101_0 ep0000011000101_1)
private theorem idp0000011000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001100010.list =
    C ((2:ℤ)^168) * horner X vp0000011000101.list + horner X ep0000011000101.list := by
  exact edge_identity (B := (2:ℤ)^339) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011000101 : Branch 1 (-195761639/2000000 : ℚ) vp000001100010 := by
  apply branch_checked idp0000011000101 (by positivity) (by decide +kernel)
  rw [show 2*(-195761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-196761639/1000000 : ℚ) by norm_num]
  exact coverp0000011000101
theorem coverp000001100010 : Covers (-195761639/2000000 : ℚ) vp000001100010 := join_branches bp0000011000100 bp0000011000101
private noncomputable def vp00000110001_0 : Blocks := edgeBlocks% "full/vectors/00000110001-V-0000.bin"
private noncomputable def vp00000110001_1 : Blocks := edgeBlocks% "full/vectors/00000110001-V-0001.bin"
private noncomputable def vp00000110001_2 : Blocks := edgeBlocks% "full/vectors/00000110001-V-0002.bin"
noncomputable def vp00000110001 : Blocks := (Blocks.join vp00000110001_0 (Blocks.join vp00000110001_1 vp00000110001_2))
private theorem bp000001100010 : Branch 0 (-195761639/4000000 : ℚ) vp00000110001 := by
  apply branch_left_normalized (c:=vp000001100010) (k:=0) (m:=162) (by decide +kernel)
  rw [show 2*(-195761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-195761639/2000000 : ℚ) by norm_num]
  exact coverp000001100010
private noncomputable def ep000001100011_0 : Blocks := edgeBlocks% "full/vectors/000001100011-E-0000.bin"
private noncomputable def ep000001100011_1 : Blocks := edgeBlocks% "full/vectors/000001100011-E-0001.bin"
private noncomputable def ep000001100011_2 : Blocks := edgeBlocks% "full/vectors/000001100011-E-0002.bin"
noncomputable def ep000001100011 : Blocks := (Blocks.join ep000001100011_0 (Blocks.join ep000001100011_1 ep000001100011_2))
private theorem idp000001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110001.list =
    C ((2:ℤ)^318) * horner X vp000001100011.list + horner X ep000001100011.list := by
  exact edge_identity (B := (2:ℤ)^555) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100011 : Branch 1 (-195761639/4000000 : ℚ) vp00000110001 := by
  apply branch_checked idp000001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-195761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-197761639/2000000 : ℚ) by norm_num]
  exact coverp000001100011
theorem coverp00000110001 : Covers (-195761639/4000000 : ℚ) vp00000110001 := join_branches bp000001100010 bp000001100011
private noncomputable def vp000001100001111_0 : Blocks := edgeBlocks% "full/vectors/000001100001111-V-0000.bin"
noncomputable def vp000001100001111 : Blocks := vp000001100001111_0
theorem coverp000001100001111 : Covers (-195511639/250000 : ℚ) vp000001100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100001110_0 : Blocks := edgeBlocks% "full/vectors/000001100001110-V-0000.bin"
noncomputable def vp000001100001110 : Blocks := vp000001100001110_0
theorem coverp000001100001110 : Covers (-195261639/250000 : ℚ) vp000001100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110000111_0 : Blocks := edgeBlocks% "full/vectors/00000110000111-V-0000.bin"
noncomputable def vp00000110000111 : Blocks := vp00000110000111_0
private theorem bp000001100001110 : Branch 0 (-195261639/500000 : ℚ) vp00000110000111 := by
  apply branch_left_normalized (c:=vp000001100001110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-195261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-195261639/250000 : ℚ) by norm_num]
  exact coverp000001100001110
private noncomputable def ep000001100001111_0 : Blocks := edgeBlocks% "full/vectors/000001100001111-E-0000.bin"
noncomputable def ep000001100001111 : Blocks := ep000001100001111_0
private theorem idp000001100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110000111.list =
    C ((2:ℤ)^58) * horner X vp000001100001111.list + horner X ep000001100001111.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100001111 : Branch 1 (-195261639/500000 : ℚ) vp00000110000111 := by
  apply branch_checked idp000001100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-195261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-195511639/250000 : ℚ) by norm_num]
  exact coverp000001100001111
theorem coverp00000110000111 : Covers (-195261639/500000 : ℚ) vp00000110000111 := join_branches bp000001100001110 bp000001100001111
private noncomputable def vp000001100001101_0 : Blocks := edgeBlocks% "full/vectors/000001100001101-V-0000.bin"
noncomputable def vp000001100001101 : Blocks := vp000001100001101_0
theorem coverp000001100001101 : Covers (-195011639/250000 : ℚ) vp000001100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100001100_0 : Blocks := edgeBlocks% "full/vectors/000001100001100-V-0000.bin"
noncomputable def vp000001100001100 : Blocks := vp000001100001100_0
theorem coverp000001100001100 : Covers (-194761639/250000 : ℚ) vp000001100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110000110_0 : Blocks := edgeBlocks% "full/vectors/00000110000110-V-0000.bin"
noncomputable def vp00000110000110 : Blocks := vp00000110000110_0
private theorem bp000001100001100 : Branch 0 (-194761639/500000 : ℚ) vp00000110000110 := by
  apply branch_left_normalized (c:=vp000001100001100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-194761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-194761639/250000 : ℚ) by norm_num]
  exact coverp000001100001100
private noncomputable def ep000001100001101_0 : Blocks := edgeBlocks% "full/vectors/000001100001101-E-0000.bin"
noncomputable def ep000001100001101 : Blocks := ep000001100001101_0
private theorem idp000001100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110000110.list =
    C ((2:ℤ)^58) * horner X vp000001100001101.list + horner X ep000001100001101.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100001101 : Branch 1 (-194761639/500000 : ℚ) vp00000110000110 := by
  apply branch_checked idp000001100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-194761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-195011639/250000 : ℚ) by norm_num]
  exact coverp000001100001101
theorem coverp00000110000110 : Covers (-194761639/500000 : ℚ) vp00000110000110 := join_branches bp000001100001100 bp000001100001101
private noncomputable def vp0000011000011_0 : Blocks := edgeBlocks% "full/vectors/0000011000011-V-0000.bin"
noncomputable def vp0000011000011 : Blocks := vp0000011000011_0
private theorem bp00000110000110 : Branch 0 (-194761639/1000000 : ℚ) vp0000011000011 := by
  apply branch_left_normalized (c:=vp00000110000110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-194761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-194761639/500000 : ℚ) by norm_num]
  exact coverp00000110000110
private noncomputable def ep00000110000111_0 : Blocks := edgeBlocks% "full/vectors/00000110000111-E-0000.bin"
noncomputable def ep00000110000111 : Blocks := ep00000110000111_0
private theorem idp00000110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011000011.list =
    C ((2:ℤ)^96) * horner X vp00000110000111.list + horner X ep00000110000111.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110000111 : Branch 1 (-194761639/1000000 : ℚ) vp0000011000011 := by
  apply branch_checked idp00000110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-194761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-195261639/500000 : ℚ) by norm_num]
  exact coverp00000110000111
theorem coverp0000011000011 : Covers (-194761639/1000000 : ℚ) vp0000011000011 := join_branches bp00000110000110 bp00000110000111
private noncomputable def vp000001100001011_0 : Blocks := edgeBlocks% "full/vectors/000001100001011-V-0000.bin"
noncomputable def vp000001100001011 : Blocks := vp000001100001011_0
theorem coverp000001100001011 : Covers (-194511639/250000 : ℚ) vp000001100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100001010_0 : Blocks := edgeBlocks% "full/vectors/000001100001010-V-0000.bin"
noncomputable def vp000001100001010 : Blocks := vp000001100001010_0
theorem coverp000001100001010 : Covers (-194261639/250000 : ℚ) vp000001100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110000101_0 : Blocks := edgeBlocks% "full/vectors/00000110000101-V-0000.bin"
noncomputable def vp00000110000101 : Blocks := vp00000110000101_0
private theorem bp000001100001010 : Branch 0 (-194261639/500000 : ℚ) vp00000110000101 := by
  apply branch_left_normalized (c:=vp000001100001010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-194261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-194261639/250000 : ℚ) by norm_num]
  exact coverp000001100001010
private noncomputable def ep000001100001011_0 : Blocks := edgeBlocks% "full/vectors/000001100001011-E-0000.bin"
noncomputable def ep000001100001011 : Blocks := ep000001100001011_0
private theorem idp000001100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110000101.list =
    C ((2:ℤ)^58) * horner X vp000001100001011.list + horner X ep000001100001011.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100001011 : Branch 1 (-194261639/500000 : ℚ) vp00000110000101 := by
  apply branch_checked idp000001100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-194261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-194511639/250000 : ℚ) by norm_num]
  exact coverp000001100001011
theorem coverp00000110000101 : Covers (-194261639/500000 : ℚ) vp00000110000101 := join_branches bp000001100001010 bp000001100001011
private noncomputable def vp000001100001001_0 : Blocks := edgeBlocks% "full/vectors/000001100001001-V-0000.bin"
noncomputable def vp000001100001001 : Blocks := vp000001100001001_0
theorem coverp000001100001001 : Covers (-194011639/250000 : ℚ) vp000001100001001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100001000_0 : Blocks := edgeBlocks% "full/vectors/000001100001000-V-0000.bin"
noncomputable def vp000001100001000 : Blocks := vp000001100001000_0
theorem coverp000001100001000 : Covers (-193761639/250000 : ℚ) vp000001100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110000100_0 : Blocks := edgeBlocks% "full/vectors/00000110000100-V-0000.bin"
noncomputable def vp00000110000100 : Blocks := vp00000110000100_0
private theorem bp000001100001000 : Branch 0 (-193761639/500000 : ℚ) vp00000110000100 := by
  apply branch_left_normalized (c:=vp000001100001000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-193761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-193761639/250000 : ℚ) by norm_num]
  exact coverp000001100001000
private noncomputable def ep000001100001001_0 : Blocks := edgeBlocks% "full/vectors/000001100001001-E-0000.bin"
noncomputable def ep000001100001001 : Blocks := ep000001100001001_0
private theorem idp000001100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110000100.list =
    C ((2:ℤ)^57) * horner X vp000001100001001.list + horner X ep000001100001001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100001001 : Branch 1 (-193761639/500000 : ℚ) vp00000110000100 := by
  apply branch_checked idp000001100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-193761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-194011639/250000 : ℚ) by norm_num]
  exact coverp000001100001001
theorem coverp00000110000100 : Covers (-193761639/500000 : ℚ) vp00000110000100 := join_branches bp000001100001000 bp000001100001001
private noncomputable def vp0000011000010_0 : Blocks := edgeBlocks% "full/vectors/0000011000010-V-0000.bin"
noncomputable def vp0000011000010 : Blocks := vp0000011000010_0
private theorem bp00000110000100 : Branch 0 (-193761639/1000000 : ℚ) vp0000011000010 := by
  apply branch_left_normalized (c:=vp00000110000100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-193761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-193761639/500000 : ℚ) by norm_num]
  exact coverp00000110000100
private noncomputable def ep00000110000101_0 : Blocks := edgeBlocks% "full/vectors/00000110000101-E-0000.bin"
noncomputable def ep00000110000101 : Blocks := ep00000110000101_0
private theorem idp00000110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011000010.list =
    C ((2:ℤ)^96) * horner X vp00000110000101.list + horner X ep00000110000101.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110000101 : Branch 1 (-193761639/1000000 : ℚ) vp0000011000010 := by
  apply branch_checked idp00000110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-193761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-194261639/500000 : ℚ) by norm_num]
  exact coverp00000110000101
theorem coverp0000011000010 : Covers (-193761639/1000000 : ℚ) vp0000011000010 := join_branches bp00000110000100 bp00000110000101
private noncomputable def vp000001100001_0 : Blocks := edgeBlocks% "full/vectors/000001100001-V-0000.bin"
private noncomputable def vp000001100001_1 : Blocks := edgeBlocks% "full/vectors/000001100001-V-0001.bin"
noncomputable def vp000001100001 : Blocks := (Blocks.join vp000001100001_0 vp000001100001_1)
private theorem bp0000011000010 : Branch 0 (-193761639/2000000 : ℚ) vp000001100001 := by
  apply branch_left_normalized (c:=vp0000011000010) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-193761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-193761639/1000000 : ℚ) by norm_num]
  exact coverp0000011000010
private noncomputable def ep0000011000011_0 : Blocks := edgeBlocks% "full/vectors/0000011000011-E-0000.bin"
private noncomputable def ep0000011000011_1 : Blocks := edgeBlocks% "full/vectors/0000011000011-E-0001.bin"
noncomputable def ep0000011000011 : Blocks := (Blocks.join ep0000011000011_0 ep0000011000011_1)
private theorem idp0000011000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001100001.list =
    C ((2:ℤ)^170) * horner X vp0000011000011.list + horner X ep0000011000011.list := by
  exact edge_identity (B := (2:ℤ)^341) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011000011 : Branch 1 (-193761639/2000000 : ℚ) vp000001100001 := by
  apply branch_checked idp0000011000011 (by positivity) (by decide +kernel)
  rw [show 2*(-193761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-194761639/1000000 : ℚ) by norm_num]
  exact coverp0000011000011
theorem coverp000001100001 : Covers (-193761639/2000000 : ℚ) vp000001100001 := join_branches bp0000011000010 bp0000011000011
private noncomputable def vp000001100000111_0 : Blocks := edgeBlocks% "full/vectors/000001100000111-V-0000.bin"
noncomputable def vp000001100000111 : Blocks := vp000001100000111_0
theorem coverp000001100000111 : Covers (-193511639/250000 : ℚ) vp000001100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100000110_0 : Blocks := edgeBlocks% "full/vectors/000001100000110-V-0000.bin"
noncomputable def vp000001100000110 : Blocks := vp000001100000110_0
theorem coverp000001100000110 : Covers (-193261639/250000 : ℚ) vp000001100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110000011_0 : Blocks := edgeBlocks% "full/vectors/00000110000011-V-0000.bin"
noncomputable def vp00000110000011 : Blocks := vp00000110000011_0
private theorem bp000001100000110 : Branch 0 (-193261639/500000 : ℚ) vp00000110000011 := by
  apply branch_left_normalized (c:=vp000001100000110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-193261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-193261639/250000 : ℚ) by norm_num]
  exact coverp000001100000110
private noncomputable def ep000001100000111_0 : Blocks := edgeBlocks% "full/vectors/000001100000111-E-0000.bin"
noncomputable def ep000001100000111 : Blocks := ep000001100000111_0
private theorem idp000001100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110000011.list =
    C ((2:ℤ)^58) * horner X vp000001100000111.list + horner X ep000001100000111.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100000111 : Branch 1 (-193261639/500000 : ℚ) vp00000110000011 := by
  apply branch_checked idp000001100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-193261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-193511639/250000 : ℚ) by norm_num]
  exact coverp000001100000111
theorem coverp00000110000011 : Covers (-193261639/500000 : ℚ) vp00000110000011 := join_branches bp000001100000110 bp000001100000111
private noncomputable def vp000001100000101_0 : Blocks := edgeBlocks% "full/vectors/000001100000101-V-0000.bin"
noncomputable def vp000001100000101 : Blocks := vp000001100000101_0
theorem coverp000001100000101 : Covers (-193011639/250000 : ℚ) vp000001100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100000100_0 : Blocks := edgeBlocks% "full/vectors/000001100000100-V-0000.bin"
noncomputable def vp000001100000100 : Blocks := vp000001100000100_0
theorem coverp000001100000100 : Covers (-192761639/250000 : ℚ) vp000001100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110000010_0 : Blocks := edgeBlocks% "full/vectors/00000110000010-V-0000.bin"
noncomputable def vp00000110000010 : Blocks := vp00000110000010_0
private theorem bp000001100000100 : Branch 0 (-192761639/500000 : ℚ) vp00000110000010 := by
  apply branch_left_normalized (c:=vp000001100000100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-192761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-192761639/250000 : ℚ) by norm_num]
  exact coverp000001100000100
private noncomputable def ep000001100000101_0 : Blocks := edgeBlocks% "full/vectors/000001100000101-E-0000.bin"
noncomputable def ep000001100000101 : Blocks := ep000001100000101_0
private theorem idp000001100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110000010.list =
    C ((2:ℤ)^57) * horner X vp000001100000101.list + horner X ep000001100000101.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100000101 : Branch 1 (-192761639/500000 : ℚ) vp00000110000010 := by
  apply branch_checked idp000001100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-192761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-193011639/250000 : ℚ) by norm_num]
  exact coverp000001100000101
theorem coverp00000110000010 : Covers (-192761639/500000 : ℚ) vp00000110000010 := join_branches bp000001100000100 bp000001100000101
private noncomputable def vp0000011000001_0 : Blocks := edgeBlocks% "full/vectors/0000011000001-V-0000.bin"
noncomputable def vp0000011000001 : Blocks := vp0000011000001_0
private theorem bp00000110000010 : Branch 0 (-192761639/1000000 : ℚ) vp0000011000001 := by
  apply branch_left_normalized (c:=vp00000110000010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-192761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-192761639/500000 : ℚ) by norm_num]
  exact coverp00000110000010
private noncomputable def ep00000110000011_0 : Blocks := edgeBlocks% "full/vectors/00000110000011-E-0000.bin"
noncomputable def ep00000110000011 : Blocks := ep00000110000011_0
private theorem idp00000110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011000001.list =
    C ((2:ℤ)^95) * horner X vp00000110000011.list + horner X ep00000110000011.list := by
  exact edge_identity (B := (2:ℤ)^233) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110000011 : Branch 1 (-192761639/1000000 : ℚ) vp0000011000001 := by
  apply branch_checked idp00000110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-192761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-193261639/500000 : ℚ) by norm_num]
  exact coverp00000110000011
theorem coverp0000011000001 : Covers (-192761639/1000000 : ℚ) vp0000011000001 := join_branches bp00000110000010 bp00000110000011
private noncomputable def vp000001100000011_0 : Blocks := edgeBlocks% "full/vectors/000001100000011-V-0000.bin"
noncomputable def vp000001100000011 : Blocks := vp000001100000011_0
theorem coverp000001100000011 : Covers (-192511639/250000 : ℚ) vp000001100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100000010_0 : Blocks := edgeBlocks% "full/vectors/000001100000010-V-0000.bin"
noncomputable def vp000001100000010 : Blocks := vp000001100000010_0
theorem coverp000001100000010 : Covers (-192261639/250000 : ℚ) vp000001100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110000001_0 : Blocks := edgeBlocks% "full/vectors/00000110000001-V-0000.bin"
noncomputable def vp00000110000001 : Blocks := vp00000110000001_0
private theorem bp000001100000010 : Branch 0 (-192261639/500000 : ℚ) vp00000110000001 := by
  apply branch_left_normalized (c:=vp000001100000010) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-192261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-192261639/250000 : ℚ) by norm_num]
  exact coverp000001100000010
private noncomputable def ep000001100000011_0 : Blocks := edgeBlocks% "full/vectors/000001100000011-E-0000.bin"
noncomputable def ep000001100000011 : Blocks := ep000001100000011_0
private theorem idp000001100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110000001.list =
    C ((2:ℤ)^57) * horner X vp000001100000011.list + horner X ep000001100000011.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100000011 : Branch 1 (-192261639/500000 : ℚ) vp00000110000001 := by
  apply branch_checked idp000001100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-192261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-192511639/250000 : ℚ) by norm_num]
  exact coverp000001100000011
theorem coverp00000110000001 : Covers (-192261639/500000 : ℚ) vp00000110000001 := join_branches bp000001100000010 bp000001100000011
private noncomputable def vp000001100000001_0 : Blocks := edgeBlocks% "full/vectors/000001100000001-V-0000.bin"
noncomputable def vp000001100000001 : Blocks := vp000001100000001_0
theorem coverp000001100000001 : Covers (-192011639/250000 : ℚ) vp000001100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000001100000000_0 : Blocks := edgeBlocks% "full/vectors/000001100000000-V-0000.bin"
noncomputable def vp000001100000000 : Blocks := vp000001100000000_0
theorem coverp000001100000000 : Covers (-191761639/250000 : ℚ) vp000001100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000110000000_0 : Blocks := edgeBlocks% "full/vectors/00000110000000-V-0000.bin"
noncomputable def vp00000110000000 : Blocks := vp00000110000000_0
private theorem bp000001100000000 : Branch 0 (-191761639/500000 : ℚ) vp00000110000000 := by
  apply branch_left_normalized (c:=vp000001100000000) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-191761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-191761639/250000 : ℚ) by norm_num]
  exact coverp000001100000000
private noncomputable def ep000001100000001_0 : Blocks := edgeBlocks% "full/vectors/000001100000001-E-0000.bin"
noncomputable def ep000001100000001 : Blocks := ep000001100000001_0
private theorem idp000001100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110000000.list =
    C ((2:ℤ)^57) * horner X vp000001100000001.list + horner X ep000001100000001.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100000001 : Branch 1 (-191761639/500000 : ℚ) vp00000110000000 := by
  apply branch_checked idp000001100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-191761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-192011639/250000 : ℚ) by norm_num]
  exact coverp000001100000001
theorem coverp00000110000000 : Covers (-191761639/500000 : ℚ) vp00000110000000 := join_branches bp000001100000000 bp000001100000001
private noncomputable def vp0000011000000_0 : Blocks := edgeBlocks% "full/vectors/0000011000000-V-0000.bin"
noncomputable def vp0000011000000 : Blocks := vp0000011000000_0
private theorem bp00000110000000 : Branch 0 (-191761639/1000000 : ℚ) vp0000011000000 := by
  apply branch_left_normalized (c:=vp00000110000000) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-191761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-191761639/500000 : ℚ) by norm_num]
  exact coverp00000110000000
private noncomputable def ep00000110000001_0 : Blocks := edgeBlocks% "full/vectors/00000110000001-E-0000.bin"
noncomputable def ep00000110000001 : Blocks := ep00000110000001_0
private theorem idp00000110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011000000.list =
    C ((2:ℤ)^96) * horner X vp00000110000001.list + horner X ep00000110000001.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110000001 : Branch 1 (-191761639/1000000 : ℚ) vp0000011000000 := by
  apply branch_checked idp00000110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-191761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-192261639/500000 : ℚ) by norm_num]
  exact coverp00000110000001
theorem coverp0000011000000 : Covers (-191761639/1000000 : ℚ) vp0000011000000 := join_branches bp00000110000000 bp00000110000001
private noncomputable def vp000001100000_0 : Blocks := edgeBlocks% "full/vectors/000001100000-V-0000.bin"
private noncomputable def vp000001100000_1 : Blocks := edgeBlocks% "full/vectors/000001100000-V-0001.bin"
noncomputable def vp000001100000 : Blocks := (Blocks.join vp000001100000_0 vp000001100000_1)
private theorem bp0000011000000 : Branch 0 (-191761639/2000000 : ℚ) vp000001100000 := by
  apply branch_left_normalized (c:=vp0000011000000) (k:=0) (m:=92) (by decide +kernel)
  rw [show 2*(-191761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-191761639/1000000 : ℚ) by norm_num]
  exact coverp0000011000000
private noncomputable def ep0000011000001_0 : Blocks := edgeBlocks% "full/vectors/0000011000001-E-0000.bin"
private noncomputable def ep0000011000001_1 : Blocks := edgeBlocks% "full/vectors/0000011000001-E-0001.bin"
noncomputable def ep0000011000001 : Blocks := (Blocks.join ep0000011000001_0 ep0000011000001_1)
private theorem idp0000011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001100000.list =
    C ((2:ℤ)^170) * horner X vp0000011000001.list + horner X ep0000011000001.list := by
  exact edge_identity (B := (2:ℤ)^342) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011000001 : Branch 1 (-191761639/2000000 : ℚ) vp000001100000 := by
  apply branch_checked idp0000011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-191761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-192761639/1000000 : ℚ) by norm_num]
  exact coverp0000011000001
theorem coverp000001100000 : Covers (-191761639/2000000 : ℚ) vp000001100000 := join_branches bp0000011000000 bp0000011000001
private noncomputable def vp00000110000_0 : Blocks := edgeBlocks% "full/vectors/00000110000-V-0000.bin"
private noncomputable def vp00000110000_1 : Blocks := edgeBlocks% "full/vectors/00000110000-V-0001.bin"
private noncomputable def vp00000110000_2 : Blocks := edgeBlocks% "full/vectors/00000110000-V-0002.bin"
noncomputable def vp00000110000 : Blocks := (Blocks.join vp00000110000_0 (Blocks.join vp00000110000_1 vp00000110000_2))
private theorem bp000001100000 : Branch 0 (-191761639/4000000 : ℚ) vp00000110000 := by
  apply branch_left_normalized (c:=vp000001100000) (k:=0) (m:=164) (by decide +kernel)
  rw [show 2*(-191761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-191761639/2000000 : ℚ) by norm_num]
  exact coverp000001100000
private noncomputable def ep000001100001_0 : Blocks := edgeBlocks% "full/vectors/000001100001-E-0000.bin"
private noncomputable def ep000001100001_1 : Blocks := edgeBlocks% "full/vectors/000001100001-E-0001.bin"
private noncomputable def ep000001100001_2 : Blocks := edgeBlocks% "full/vectors/000001100001-E-0002.bin"
noncomputable def ep000001100001 : Blocks := (Blocks.join ep000001100001_0 (Blocks.join ep000001100001_1 ep000001100001_2))
private theorem idp000001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110000.list =
    C ((2:ℤ)^317) * horner X vp000001100001.list + horner X ep000001100001.list := by
  exact edge_identity (B := (2:ℤ)^558) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001100001 : Branch 1 (-191761639/4000000 : ℚ) vp00000110000 := by
  apply branch_checked idp000001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-191761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-193761639/2000000 : ℚ) by norm_num]
  exact coverp000001100001
theorem coverp00000110000 : Covers (-191761639/4000000 : ℚ) vp00000110000 := join_branches bp000001100000 bp000001100001
private noncomputable def vp0000011000_0 : Blocks := edgeBlocks% "full/vectors/0000011000-V-0000.bin"
private noncomputable def vp0000011000_1 : Blocks := edgeBlocks% "full/vectors/0000011000-V-0001.bin"
private noncomputable def vp0000011000_2 : Blocks := edgeBlocks% "full/vectors/0000011000-V-0002.bin"
private noncomputable def vp0000011000_3 : Blocks := edgeBlocks% "full/vectors/0000011000-V-0003.bin"
private noncomputable def vp0000011000_4 : Blocks := edgeBlocks% "full/vectors/0000011000-V-0004.bin"
noncomputable def vp0000011000 : Blocks := (Blocks.join (Blocks.join vp0000011000_0 vp0000011000_1) (Blocks.join vp0000011000_2 (Blocks.join vp0000011000_3 vp0000011000_4)))
private theorem bp00000110000 : Branch 0 (-191761639/8000000 : ℚ) vp0000011000 := by
  apply branch_left_normalized (c:=vp00000110000) (k:=0) (m:=305) (by decide +kernel)
  rw [show 2*(-191761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-191761639/4000000 : ℚ) by norm_num]
  exact coverp00000110000
private noncomputable def ep00000110001_0 : Blocks := edgeBlocks% "full/vectors/00000110001-E-0000.bin"
private noncomputable def ep00000110001_1 : Blocks := edgeBlocks% "full/vectors/00000110001-E-0001.bin"
private noncomputable def ep00000110001_2 : Blocks := edgeBlocks% "full/vectors/00000110001-E-0002.bin"
private noncomputable def ep00000110001_3 : Blocks := edgeBlocks% "full/vectors/00000110001-E-0003.bin"
private noncomputable def ep00000110001_4 : Blocks := edgeBlocks% "full/vectors/00000110001-E-0004.bin"
noncomputable def ep00000110001 : Blocks := (Blocks.join (Blocks.join ep00000110001_0 ep00000110001_1) (Blocks.join ep00000110001_2 (Blocks.join ep00000110001_3 ep00000110001_4)))
private theorem idp00000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000011000.list =
    C ((2:ℤ)^609) * horner X vp00000110001.list + horner X ep00000110001.list := by
  exact edge_identity (B := (2:ℤ)^988) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000110001 : Branch 1 (-191761639/8000000 : ℚ) vp0000011000 := by
  apply branch_checked idp00000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-191761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-195761639/4000000 : ℚ) by norm_num]
  exact coverp00000110001
theorem coverp0000011000 : Covers (-191761639/8000000 : ℚ) vp0000011000 := join_branches bp00000110000 bp00000110001
private noncomputable def vp000001100_0 : Blocks := edgeBlocks% "full/vectors/000001100-V-0000.bin"
private noncomputable def vp000001100_1 : Blocks := edgeBlocks% "full/vectors/000001100-V-0001.bin"
private noncomputable def vp000001100_2 : Blocks := edgeBlocks% "full/vectors/000001100-V-0002.bin"
private noncomputable def vp000001100_3 : Blocks := edgeBlocks% "full/vectors/000001100-V-0003.bin"
private noncomputable def vp000001100_4 : Blocks := edgeBlocks% "full/vectors/000001100-V-0004.bin"
private noncomputable def vp000001100_5 : Blocks := edgeBlocks% "full/vectors/000001100-V-0005.bin"
private noncomputable def vp000001100_6 : Blocks := edgeBlocks% "full/vectors/000001100-V-0006.bin"
private noncomputable def vp000001100_7 : Blocks := edgeBlocks% "full/vectors/000001100-V-0007.bin"
private noncomputable def vp000001100_8 : Blocks := edgeBlocks% "full/vectors/000001100-V-0008.bin"
noncomputable def vp000001100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp000001100_0 vp000001100_1) (Blocks.join vp000001100_2 vp000001100_3)) (Blocks.join (Blocks.join vp000001100_4 vp000001100_5) (Blocks.join vp000001100_6 (Blocks.join vp000001100_7 vp000001100_8))))
private theorem bp0000011000 : Branch 0 (-191761639/16000000 : ℚ) vp000001100 := by
  apply branch_left_normalized (c:=vp0000011000) (k:=0) (m:=585) (by decide +kernel)
  rw [show 2*(-191761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-191761639/8000000 : ℚ) by norm_num]
  exact coverp0000011000
private noncomputable def ep0000011001_0 : Blocks := edgeBlocks% "full/vectors/0000011001-E-0000.bin"
private noncomputable def ep0000011001_1 : Blocks := edgeBlocks% "full/vectors/0000011001-E-0001.bin"
private noncomputable def ep0000011001_2 : Blocks := edgeBlocks% "full/vectors/0000011001-E-0002.bin"
private noncomputable def ep0000011001_3 : Blocks := edgeBlocks% "full/vectors/0000011001-E-0003.bin"
private noncomputable def ep0000011001_4 : Blocks := edgeBlocks% "full/vectors/0000011001-E-0004.bin"
private noncomputable def ep0000011001_5 : Blocks := edgeBlocks% "full/vectors/0000011001-E-0005.bin"
private noncomputable def ep0000011001_6 : Blocks := edgeBlocks% "full/vectors/0000011001-E-0006.bin"
private noncomputable def ep0000011001_7 : Blocks := edgeBlocks% "full/vectors/0000011001-E-0007.bin"
private noncomputable def ep0000011001_8 : Blocks := edgeBlocks% "full/vectors/0000011001-E-0008.bin"
noncomputable def ep0000011001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep0000011001_0 ep0000011001_1) (Blocks.join ep0000011001_2 ep0000011001_3)) (Blocks.join (Blocks.join ep0000011001_4 ep0000011001_5) (Blocks.join ep0000011001_6 (Blocks.join ep0000011001_7 ep0000011001_8))))
private theorem idp0000011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000001100.list =
    C ((2:ℤ)^1188) * horner X vp0000011001.list + horner X ep0000011001.list := by
  exact edge_identity (B := (2:ℤ)^1841) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000011001 : Branch 1 (-191761639/16000000 : ℚ) vp000001100 := by
  apply branch_checked idp0000011001 (by positivity) (by decide +kernel)
  rw [show 2*(-191761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-199761639/8000000 : ℚ) by norm_num]
  exact coverp0000011001
theorem coverp000001100 : Covers (-191761639/16000000 : ℚ) vp000001100 := join_branches bp0000011000 bp0000011001
private noncomputable def vp00000110_0 : Blocks := edgeBlocks% "full/vectors/00000110-V-0000.bin"
private noncomputable def vp00000110_1 : Blocks := edgeBlocks% "full/vectors/00000110-V-0001.bin"
private noncomputable def vp00000110_2 : Blocks := edgeBlocks% "full/vectors/00000110-V-0002.bin"
private noncomputable def vp00000110_3 : Blocks := edgeBlocks% "full/vectors/00000110-V-0003.bin"
private noncomputable def vp00000110_4 : Blocks := edgeBlocks% "full/vectors/00000110-V-0004.bin"
private noncomputable def vp00000110_5 : Blocks := edgeBlocks% "full/vectors/00000110-V-0005.bin"
private noncomputable def vp00000110_6 : Blocks := edgeBlocks% "full/vectors/00000110-V-0006.bin"
private noncomputable def vp00000110_7 : Blocks := edgeBlocks% "full/vectors/00000110-V-0007.bin"
private noncomputable def vp00000110_8 : Blocks := edgeBlocks% "full/vectors/00000110-V-0008.bin"
private noncomputable def vp00000110_9 : Blocks := edgeBlocks% "full/vectors/00000110-V-0009.bin"
private noncomputable def vp00000110_10 : Blocks := edgeBlocks% "full/vectors/00000110-V-0010.bin"
private noncomputable def vp00000110_11 : Blocks := edgeBlocks% "full/vectors/00000110-V-0011.bin"
private noncomputable def vp00000110_12 : Blocks := edgeBlocks% "full/vectors/00000110-V-0012.bin"
private noncomputable def vp00000110_13 : Blocks := edgeBlocks% "full/vectors/00000110-V-0013.bin"
private noncomputable def vp00000110_14 : Blocks := edgeBlocks% "full/vectors/00000110-V-0014.bin"
private noncomputable def vp00000110_15 : Blocks := edgeBlocks% "full/vectors/00000110-V-0015.bin"
private noncomputable def vp00000110_16 : Blocks := edgeBlocks% "full/vectors/00000110-V-0016.bin"
private noncomputable def vp00000110_17 : Blocks := edgeBlocks% "full/vectors/00000110-V-0017.bin"
noncomputable def vp00000110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp00000110_0 vp00000110_1) (Blocks.join vp00000110_2 vp00000110_3)) (Blocks.join (Blocks.join vp00000110_4 vp00000110_5) (Blocks.join vp00000110_6 (Blocks.join vp00000110_7 vp00000110_8)))) (Blocks.join (Blocks.join (Blocks.join vp00000110_9 vp00000110_10) (Blocks.join vp00000110_11 vp00000110_12)) (Blocks.join (Blocks.join vp00000110_13 vp00000110_14) (Blocks.join vp00000110_15 (Blocks.join vp00000110_16 vp00000110_17)))))
private theorem bp000001100 : Branch 0 (-191761639/32000000 : ℚ) vp00000110 := by
  apply branch_left_normalized (c:=vp000001100) (k:=0) (m:=1139) (by decide +kernel)
  rw [show 2*(-191761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-191761639/16000000 : ℚ) by norm_num]
  exact coverp000001100
private noncomputable def ep000001101_0 : Blocks := edgeBlocks% "full/vectors/000001101-E-0000.bin"
private noncomputable def ep000001101_1 : Blocks := edgeBlocks% "full/vectors/000001101-E-0001.bin"
private noncomputable def ep000001101_2 : Blocks := edgeBlocks% "full/vectors/000001101-E-0002.bin"
private noncomputable def ep000001101_3 : Blocks := edgeBlocks% "full/vectors/000001101-E-0003.bin"
private noncomputable def ep000001101_4 : Blocks := edgeBlocks% "full/vectors/000001101-E-0004.bin"
private noncomputable def ep000001101_5 : Blocks := edgeBlocks% "full/vectors/000001101-E-0005.bin"
private noncomputable def ep000001101_6 : Blocks := edgeBlocks% "full/vectors/000001101-E-0006.bin"
private noncomputable def ep000001101_7 : Blocks := edgeBlocks% "full/vectors/000001101-E-0007.bin"
private noncomputable def ep000001101_8 : Blocks := edgeBlocks% "full/vectors/000001101-E-0008.bin"
private noncomputable def ep000001101_9 : Blocks := edgeBlocks% "full/vectors/000001101-E-0009.bin"
private noncomputable def ep000001101_10 : Blocks := edgeBlocks% "full/vectors/000001101-E-0010.bin"
private noncomputable def ep000001101_11 : Blocks := edgeBlocks% "full/vectors/000001101-E-0011.bin"
private noncomputable def ep000001101_12 : Blocks := edgeBlocks% "full/vectors/000001101-E-0012.bin"
private noncomputable def ep000001101_13 : Blocks := edgeBlocks% "full/vectors/000001101-E-0013.bin"
private noncomputable def ep000001101_14 : Blocks := edgeBlocks% "full/vectors/000001101-E-0014.bin"
private noncomputable def ep000001101_15 : Blocks := edgeBlocks% "full/vectors/000001101-E-0015.bin"
private noncomputable def ep000001101_16 : Blocks := edgeBlocks% "full/vectors/000001101-E-0016.bin"
private noncomputable def ep000001101_17 : Blocks := edgeBlocks% "full/vectors/000001101-E-0017.bin"
noncomputable def ep000001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep000001101_0 ep000001101_1) (Blocks.join ep000001101_2 ep000001101_3)) (Blocks.join (Blocks.join ep000001101_4 ep000001101_5) (Blocks.join ep000001101_6 (Blocks.join ep000001101_7 ep000001101_8)))) (Blocks.join (Blocks.join (Blocks.join ep000001101_9 ep000001101_10) (Blocks.join ep000001101_11 ep000001101_12)) (Blocks.join (Blocks.join ep000001101_13 ep000001101_14) (Blocks.join ep000001101_15 (Blocks.join ep000001101_16 ep000001101_17)))))
private theorem idp000001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000110.list =
    C ((2:ℤ)^2320) * horner X vp000001101.list + horner X ep000001101.list := by
  exact edge_identity (B := (2:ℤ)^3508) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000001101 : Branch 1 (-191761639/32000000 : ℚ) vp00000110 := by
  apply branch_checked idp000001101 (by positivity) (by decide +kernel)
  rw [show 2*(-191761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-207761639/16000000 : ℚ) by norm_num]
  exact coverp000001101
theorem coverp00000110 : Covers (-191761639/32000000 : ℚ) vp00000110 := join_branches bp000001100 bp000001101
end NextProof.EdgeFull

