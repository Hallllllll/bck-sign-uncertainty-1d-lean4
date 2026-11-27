import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000000011111111_0 : Blocks := edgeBlocks% "full/vectors/000000011111111-V-0000.bin"
noncomputable def vp000000011111111 : Blocks := vp000000011111111_0
theorem coverp000000011111111 : Covers (-63511639/250000 : ℚ) vp000000011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011111110_0 : Blocks := edgeBlocks% "full/vectors/000000011111110-V-0000.bin"
noncomputable def vp000000011111110 : Blocks := vp000000011111110_0
theorem coverp000000011111110 : Covers (-63261639/250000 : ℚ) vp000000011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001111111_0 : Blocks := edgeBlocks% "full/vectors/00000001111111-V-0000.bin"
noncomputable def vp00000001111111 : Blocks := vp00000001111111_0
private theorem bp000000011111110 : Branch 0 (-63261639/500000 : ℚ) vp00000001111111 := by
  apply branch_left_normalized (c:=vp000000011111110) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-63261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-63261639/250000 : ℚ) by norm_num]
  exact coverp000000011111110
private noncomputable def ep000000011111111_0 : Blocks := edgeBlocks% "full/vectors/000000011111111-E-0000.bin"
noncomputable def ep000000011111111 : Blocks := ep000000011111111_0
private theorem idp000000011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001111111.list =
    C ((2:ℤ)^79) * horner X vp000000011111111.list + horner X ep000000011111111.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011111111 : Branch 1 (-63261639/500000 : ℚ) vp00000001111111 := by
  apply branch_checked idp000000011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-63261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-63511639/250000 : ℚ) by norm_num]
  exact coverp000000011111111
theorem coverp00000001111111 : Covers (-63261639/500000 : ℚ) vp00000001111111 := join_branches bp000000011111110 bp000000011111111
private noncomputable def vp000000011111101_0 : Blocks := edgeBlocks% "full/vectors/000000011111101-V-0000.bin"
noncomputable def vp000000011111101 : Blocks := vp000000011111101_0
theorem coverp000000011111101 : Covers (-63011639/250000 : ℚ) vp000000011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011111100_0 : Blocks := edgeBlocks% "full/vectors/000000011111100-V-0000.bin"
noncomputable def vp000000011111100 : Blocks := vp000000011111100_0
theorem coverp000000011111100 : Covers (-62761639/250000 : ℚ) vp000000011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001111110_0 : Blocks := edgeBlocks% "full/vectors/00000001111110-V-0000.bin"
noncomputable def vp00000001111110 : Blocks := vp00000001111110_0
private theorem bp000000011111100 : Branch 0 (-62761639/500000 : ℚ) vp00000001111110 := by
  apply branch_left_normalized (c:=vp000000011111100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-62761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-62761639/250000 : ℚ) by norm_num]
  exact coverp000000011111100
private noncomputable def ep000000011111101_0 : Blocks := edgeBlocks% "full/vectors/000000011111101-E-0000.bin"
noncomputable def ep000000011111101 : Blocks := ep000000011111101_0
private theorem idp000000011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001111110.list =
    C ((2:ℤ)^79) * horner X vp000000011111101.list + horner X ep000000011111101.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011111101 : Branch 1 (-62761639/500000 : ℚ) vp00000001111110 := by
  apply branch_checked idp000000011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-62761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-63011639/250000 : ℚ) by norm_num]
  exact coverp000000011111101
theorem coverp00000001111110 : Covers (-62761639/500000 : ℚ) vp00000001111110 := join_branches bp000000011111100 bp000000011111101
private noncomputable def vp0000000111111_0 : Blocks := edgeBlocks% "full/vectors/0000000111111-V-0000.bin"
private noncomputable def vp0000000111111_1 : Blocks := edgeBlocks% "full/vectors/0000000111111-V-0001.bin"
noncomputable def vp0000000111111 : Blocks := (Blocks.join vp0000000111111_0 vp0000000111111_1)
private theorem bp00000001111110 : Branch 0 (-62761639/1000000 : ℚ) vp0000000111111 := by
  apply branch_left_normalized (c:=vp00000001111110) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-62761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-62761639/500000 : ℚ) by norm_num]
  exact coverp00000001111110
private noncomputable def ep00000001111111_0 : Blocks := edgeBlocks% "full/vectors/00000001111111-E-0000.bin"
private noncomputable def ep00000001111111_1 : Blocks := edgeBlocks% "full/vectors/00000001111111-E-0001.bin"
noncomputable def ep00000001111111 : Blocks := (Blocks.join ep00000001111111_0 ep00000001111111_1)
private theorem idp00000001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000111111.list =
    C ((2:ℤ)^142) * horner X vp00000001111111.list + horner X ep00000001111111.list := by
  exact edge_identity (B := (2:ℤ)^294) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001111111 : Branch 1 (-62761639/1000000 : ℚ) vp0000000111111 := by
  apply branch_checked idp00000001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-62761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-63261639/500000 : ℚ) by norm_num]
  exact coverp00000001111111
theorem coverp0000000111111 : Covers (-62761639/1000000 : ℚ) vp0000000111111 := join_branches bp00000001111110 bp00000001111111
private noncomputable def vp000000011111011_0 : Blocks := edgeBlocks% "full/vectors/000000011111011-V-0000.bin"
noncomputable def vp000000011111011 : Blocks := vp000000011111011_0
theorem coverp000000011111011 : Covers (-62511639/250000 : ℚ) vp000000011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011111010_0 : Blocks := edgeBlocks% "full/vectors/000000011111010-V-0000.bin"
noncomputable def vp000000011111010 : Blocks := vp000000011111010_0
theorem coverp000000011111010 : Covers (-62261639/250000 : ℚ) vp000000011111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001111101_0 : Blocks := edgeBlocks% "full/vectors/00000001111101-V-0000.bin"
noncomputable def vp00000001111101 : Blocks := vp00000001111101_0
private theorem bp000000011111010 : Branch 0 (-62261639/500000 : ℚ) vp00000001111101 := by
  apply branch_left_normalized (c:=vp000000011111010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-62261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-62261639/250000 : ℚ) by norm_num]
  exact coverp000000011111010
private noncomputable def ep000000011111011_0 : Blocks := edgeBlocks% "full/vectors/000000011111011-E-0000.bin"
noncomputable def ep000000011111011 : Blocks := ep000000011111011_0
private theorem idp000000011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001111101.list =
    C ((2:ℤ)^79) * horner X vp000000011111011.list + horner X ep000000011111011.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011111011 : Branch 1 (-62261639/500000 : ℚ) vp00000001111101 := by
  apply branch_checked idp000000011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-62261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-62511639/250000 : ℚ) by norm_num]
  exact coverp000000011111011
theorem coverp00000001111101 : Covers (-62261639/500000 : ℚ) vp00000001111101 := join_branches bp000000011111010 bp000000011111011
private noncomputable def vp000000011111001_0 : Blocks := edgeBlocks% "full/vectors/000000011111001-V-0000.bin"
noncomputable def vp000000011111001 : Blocks := vp000000011111001_0
theorem coverp000000011111001 : Covers (-62011639/250000 : ℚ) vp000000011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011111000_0 : Blocks := edgeBlocks% "full/vectors/000000011111000-V-0000.bin"
noncomputable def vp000000011111000 : Blocks := vp000000011111000_0
theorem coverp000000011111000 : Covers (-61761639/250000 : ℚ) vp000000011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001111100_0 : Blocks := edgeBlocks% "full/vectors/00000001111100-V-0000.bin"
noncomputable def vp00000001111100 : Blocks := vp00000001111100_0
private theorem bp000000011111000 : Branch 0 (-61761639/500000 : ℚ) vp00000001111100 := by
  apply branch_left_normalized (c:=vp000000011111000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-61761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-61761639/250000 : ℚ) by norm_num]
  exact coverp000000011111000
private noncomputable def ep000000011111001_0 : Blocks := edgeBlocks% "full/vectors/000000011111001-E-0000.bin"
noncomputable def ep000000011111001 : Blocks := ep000000011111001_0
private theorem idp000000011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001111100.list =
    C ((2:ℤ)^79) * horner X vp000000011111001.list + horner X ep000000011111001.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011111001 : Branch 1 (-61761639/500000 : ℚ) vp00000001111100 := by
  apply branch_checked idp000000011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-61761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-62011639/250000 : ℚ) by norm_num]
  exact coverp000000011111001
theorem coverp00000001111100 : Covers (-61761639/500000 : ℚ) vp00000001111100 := join_branches bp000000011111000 bp000000011111001
private noncomputable def vp0000000111110_0 : Blocks := edgeBlocks% "full/vectors/0000000111110-V-0000.bin"
private noncomputable def vp0000000111110_1 : Blocks := edgeBlocks% "full/vectors/0000000111110-V-0001.bin"
noncomputable def vp0000000111110 : Blocks := (Blocks.join vp0000000111110_0 vp0000000111110_1)
private theorem bp00000001111100 : Branch 0 (-61761639/1000000 : ℚ) vp0000000111110 := by
  apply branch_left_normalized (c:=vp00000001111100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-61761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-61761639/500000 : ℚ) by norm_num]
  exact coverp00000001111100
private noncomputable def ep00000001111101_0 : Blocks := edgeBlocks% "full/vectors/00000001111101-E-0000.bin"
private noncomputable def ep00000001111101_1 : Blocks := edgeBlocks% "full/vectors/00000001111101-E-0001.bin"
noncomputable def ep00000001111101 : Blocks := (Blocks.join ep00000001111101_0 ep00000001111101_1)
private theorem idp00000001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000111110.list =
    C ((2:ℤ)^143) * horner X vp00000001111101.list + horner X ep00000001111101.list := by
  exact edge_identity (B := (2:ℤ)^295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001111101 : Branch 1 (-61761639/1000000 : ℚ) vp0000000111110 := by
  apply branch_checked idp00000001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-61761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-62261639/500000 : ℚ) by norm_num]
  exact coverp00000001111101
theorem coverp0000000111110 : Covers (-61761639/1000000 : ℚ) vp0000000111110 := join_branches bp00000001111100 bp00000001111101
private noncomputable def vp000000011111_0 : Blocks := edgeBlocks% "full/vectors/000000011111-V-0000.bin"
private noncomputable def vp000000011111_1 : Blocks := edgeBlocks% "full/vectors/000000011111-V-0001.bin"
private noncomputable def vp000000011111_2 : Blocks := edgeBlocks% "full/vectors/000000011111-V-0002.bin"
noncomputable def vp000000011111 : Blocks := (Blocks.join vp000000011111_0 (Blocks.join vp000000011111_1 vp000000011111_2))
private theorem bp0000000111110 : Branch 0 (-61761639/2000000 : ℚ) vp000000011111 := by
  apply branch_left_normalized (c:=vp0000000111110) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-61761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-61761639/1000000 : ℚ) by norm_num]
  exact coverp0000000111110
private noncomputable def ep0000000111111_0 : Blocks := edgeBlocks% "full/vectors/0000000111111-E-0000.bin"
private noncomputable def ep0000000111111_1 : Blocks := edgeBlocks% "full/vectors/0000000111111-E-0001.bin"
private noncomputable def ep0000000111111_2 : Blocks := edgeBlocks% "full/vectors/0000000111111-E-0002.bin"
noncomputable def ep0000000111111 : Blocks := (Blocks.join ep0000000111111_0 (Blocks.join ep0000000111111_1 ep0000000111111_2))
private theorem idp0000000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011111.list =
    C ((2:ℤ)^270) * horner X vp0000000111111.list + horner X ep0000000111111.list := by
  exact edge_identity (B := (2:ℤ)^486) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111111 : Branch 1 (-61761639/2000000 : ℚ) vp000000011111 := by
  apply branch_checked idp0000000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-61761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-62761639/1000000 : ℚ) by norm_num]
  exact coverp0000000111111
theorem coverp000000011111 : Covers (-61761639/2000000 : ℚ) vp000000011111 := join_branches bp0000000111110 bp0000000111111
private noncomputable def vp000000011110111_0 : Blocks := edgeBlocks% "full/vectors/000000011110111-V-0000.bin"
noncomputable def vp000000011110111 : Blocks := vp000000011110111_0
theorem coverp000000011110111 : Covers (-61511639/250000 : ℚ) vp000000011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011110110_0 : Blocks := edgeBlocks% "full/vectors/000000011110110-V-0000.bin"
noncomputable def vp000000011110110 : Blocks := vp000000011110110_0
theorem coverp000000011110110 : Covers (-61261639/250000 : ℚ) vp000000011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001111011_0 : Blocks := edgeBlocks% "full/vectors/00000001111011-V-0000.bin"
noncomputable def vp00000001111011 : Blocks := vp00000001111011_0
private theorem bp000000011110110 : Branch 0 (-61261639/500000 : ℚ) vp00000001111011 := by
  apply branch_left_normalized (c:=vp000000011110110) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-61261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-61261639/250000 : ℚ) by norm_num]
  exact coverp000000011110110
private noncomputable def ep000000011110111_0 : Blocks := edgeBlocks% "full/vectors/000000011110111-E-0000.bin"
noncomputable def ep000000011110111 : Blocks := ep000000011110111_0
private theorem idp000000011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001111011.list =
    C ((2:ℤ)^79) * horner X vp000000011110111.list + horner X ep000000011110111.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011110111 : Branch 1 (-61261639/500000 : ℚ) vp00000001111011 := by
  apply branch_checked idp000000011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-61261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-61511639/250000 : ℚ) by norm_num]
  exact coverp000000011110111
theorem coverp00000001111011 : Covers (-61261639/500000 : ℚ) vp00000001111011 := join_branches bp000000011110110 bp000000011110111
private noncomputable def vp000000011110101_0 : Blocks := edgeBlocks% "full/vectors/000000011110101-V-0000.bin"
noncomputable def vp000000011110101 : Blocks := vp000000011110101_0
theorem coverp000000011110101 : Covers (-61011639/250000 : ℚ) vp000000011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011110100_0 : Blocks := edgeBlocks% "full/vectors/000000011110100-V-0000.bin"
noncomputable def vp000000011110100 : Blocks := vp000000011110100_0
theorem coverp000000011110100 : Covers (-60761639/250000 : ℚ) vp000000011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001111010_0 : Blocks := edgeBlocks% "full/vectors/00000001111010-V-0000.bin"
noncomputable def vp00000001111010 : Blocks := vp00000001111010_0
private theorem bp000000011110100 : Branch 0 (-60761639/500000 : ℚ) vp00000001111010 := by
  apply branch_left_normalized (c:=vp000000011110100) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-60761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-60761639/250000 : ℚ) by norm_num]
  exact coverp000000011110100
private noncomputable def ep000000011110101_0 : Blocks := edgeBlocks% "full/vectors/000000011110101-E-0000.bin"
noncomputable def ep000000011110101 : Blocks := ep000000011110101_0
private theorem idp000000011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001111010.list =
    C ((2:ℤ)^79) * horner X vp000000011110101.list + horner X ep000000011110101.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011110101 : Branch 1 (-60761639/500000 : ℚ) vp00000001111010 := by
  apply branch_checked idp000000011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-60761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-61011639/250000 : ℚ) by norm_num]
  exact coverp000000011110101
theorem coverp00000001111010 : Covers (-60761639/500000 : ℚ) vp00000001111010 := join_branches bp000000011110100 bp000000011110101
private noncomputable def vp0000000111101_0 : Blocks := edgeBlocks% "full/vectors/0000000111101-V-0000.bin"
private noncomputable def vp0000000111101_1 : Blocks := edgeBlocks% "full/vectors/0000000111101-V-0001.bin"
noncomputable def vp0000000111101 : Blocks := (Blocks.join vp0000000111101_0 vp0000000111101_1)
private theorem bp00000001111010 : Branch 0 (-60761639/1000000 : ℚ) vp0000000111101 := by
  apply branch_left_normalized (c:=vp00000001111010) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-60761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-60761639/500000 : ℚ) by norm_num]
  exact coverp00000001111010
private noncomputable def ep00000001111011_0 : Blocks := edgeBlocks% "full/vectors/00000001111011-E-0000.bin"
private noncomputable def ep00000001111011_1 : Blocks := edgeBlocks% "full/vectors/00000001111011-E-0001.bin"
noncomputable def ep00000001111011 : Blocks := (Blocks.join ep00000001111011_0 ep00000001111011_1)
private theorem idp00000001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000111101.list =
    C ((2:ℤ)^144) * horner X vp00000001111011.list + horner X ep00000001111011.list := by
  exact edge_identity (B := (2:ℤ)^297) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001111011 : Branch 1 (-60761639/1000000 : ℚ) vp0000000111101 := by
  apply branch_checked idp00000001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-60761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-61261639/500000 : ℚ) by norm_num]
  exact coverp00000001111011
theorem coverp0000000111101 : Covers (-60761639/1000000 : ℚ) vp0000000111101 := join_branches bp00000001111010 bp00000001111011
private noncomputable def vp000000011110011_0 : Blocks := edgeBlocks% "full/vectors/000000011110011-V-0000.bin"
noncomputable def vp000000011110011 : Blocks := vp000000011110011_0
theorem coverp000000011110011 : Covers (-60511639/250000 : ℚ) vp000000011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011110010_0 : Blocks := edgeBlocks% "full/vectors/000000011110010-V-0000.bin"
noncomputable def vp000000011110010 : Blocks := vp000000011110010_0
theorem coverp000000011110010 : Covers (-60261639/250000 : ℚ) vp000000011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001111001_0 : Blocks := edgeBlocks% "full/vectors/00000001111001-V-0000.bin"
noncomputable def vp00000001111001 : Blocks := vp00000001111001_0
private theorem bp000000011110010 : Branch 0 (-60261639/500000 : ℚ) vp00000001111001 := by
  apply branch_left_normalized (c:=vp000000011110010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-60261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-60261639/250000 : ℚ) by norm_num]
  exact coverp000000011110010
private noncomputable def ep000000011110011_0 : Blocks := edgeBlocks% "full/vectors/000000011110011-E-0000.bin"
noncomputable def ep000000011110011 : Blocks := ep000000011110011_0
private theorem idp000000011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001111001.list =
    C ((2:ℤ)^81) * horner X vp000000011110011.list + horner X ep000000011110011.list := by
  exact edge_identity (B := (2:ℤ)^203) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011110011 : Branch 1 (-60261639/500000 : ℚ) vp00000001111001 := by
  apply branch_checked idp000000011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-60261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-60511639/250000 : ℚ) by norm_num]
  exact coverp000000011110011
theorem coverp00000001111001 : Covers (-60261639/500000 : ℚ) vp00000001111001 := join_branches bp000000011110010 bp000000011110011
private noncomputable def vp000000011110001_0 : Blocks := edgeBlocks% "full/vectors/000000011110001-V-0000.bin"
noncomputable def vp000000011110001 : Blocks := vp000000011110001_0
theorem coverp000000011110001 : Covers (-60011639/250000 : ℚ) vp000000011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011110000_0 : Blocks := edgeBlocks% "full/vectors/000000011110000-V-0000.bin"
noncomputable def vp000000011110000 : Blocks := vp000000011110000_0
theorem coverp000000011110000 : Covers (-59761639/250000 : ℚ) vp000000011110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001111000_0 : Blocks := edgeBlocks% "full/vectors/00000001111000-V-0000.bin"
noncomputable def vp00000001111000 : Blocks := vp00000001111000_0
private theorem bp000000011110000 : Branch 0 (-59761639/500000 : ℚ) vp00000001111000 := by
  apply branch_left_normalized (c:=vp000000011110000) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-59761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-59761639/250000 : ℚ) by norm_num]
  exact coverp000000011110000
private noncomputable def ep000000011110001_0 : Blocks := edgeBlocks% "full/vectors/000000011110001-E-0000.bin"
noncomputable def ep000000011110001 : Blocks := ep000000011110001_0
private theorem idp000000011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001111000.list =
    C ((2:ℤ)^82) * horner X vp000000011110001.list + horner X ep000000011110001.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011110001 : Branch 1 (-59761639/500000 : ℚ) vp00000001111000 := by
  apply branch_checked idp000000011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-59761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-60011639/250000 : ℚ) by norm_num]
  exact coverp000000011110001
theorem coverp00000001111000 : Covers (-59761639/500000 : ℚ) vp00000001111000 := join_branches bp000000011110000 bp000000011110001
private noncomputable def vp0000000111100_0 : Blocks := edgeBlocks% "full/vectors/0000000111100-V-0000.bin"
private noncomputable def vp0000000111100_1 : Blocks := edgeBlocks% "full/vectors/0000000111100-V-0001.bin"
noncomputable def vp0000000111100 : Blocks := (Blocks.join vp0000000111100_0 vp0000000111100_1)
private theorem bp00000001111000 : Branch 0 (-59761639/1000000 : ℚ) vp0000000111100 := by
  apply branch_left_normalized (c:=vp00000001111000) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-59761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-59761639/500000 : ℚ) by norm_num]
  exact coverp00000001111000
private noncomputable def ep00000001111001_0 : Blocks := edgeBlocks% "full/vectors/00000001111001-E-0000.bin"
private noncomputable def ep00000001111001_1 : Blocks := edgeBlocks% "full/vectors/00000001111001-E-0001.bin"
noncomputable def ep00000001111001 : Blocks := (Blocks.join ep00000001111001_0 ep00000001111001_1)
private theorem idp00000001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000111100.list =
    C ((2:ℤ)^148) * horner X vp00000001111001.list + horner X ep00000001111001.list := by
  exact edge_identity (B := (2:ℤ)^303) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001111001 : Branch 1 (-59761639/1000000 : ℚ) vp0000000111100 := by
  apply branch_checked idp00000001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-59761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-60261639/500000 : ℚ) by norm_num]
  exact coverp00000001111001
theorem coverp0000000111100 : Covers (-59761639/1000000 : ℚ) vp0000000111100 := join_branches bp00000001111000 bp00000001111001
private noncomputable def vp000000011110_0 : Blocks := edgeBlocks% "full/vectors/000000011110-V-0000.bin"
private noncomputable def vp000000011110_1 : Blocks := edgeBlocks% "full/vectors/000000011110-V-0001.bin"
private noncomputable def vp000000011110_2 : Blocks := edgeBlocks% "full/vectors/000000011110-V-0002.bin"
noncomputable def vp000000011110 : Blocks := (Blocks.join vp000000011110_0 (Blocks.join vp000000011110_1 vp000000011110_2))
private theorem bp0000000111100 : Branch 0 (-59761639/2000000 : ℚ) vp000000011110 := by
  apply branch_left_normalized (c:=vp0000000111100) (k:=0) (m:=143) (by decide +kernel)
  rw [show 2*(-59761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-59761639/1000000 : ℚ) by norm_num]
  exact coverp0000000111100
private noncomputable def ep0000000111101_0 : Blocks := edgeBlocks% "full/vectors/0000000111101-E-0000.bin"
private noncomputable def ep0000000111101_1 : Blocks := edgeBlocks% "full/vectors/0000000111101-E-0001.bin"
private noncomputable def ep0000000111101_2 : Blocks := edgeBlocks% "full/vectors/0000000111101-E-0002.bin"
noncomputable def ep0000000111101 : Blocks := (Blocks.join ep0000000111101_0 (Blocks.join ep0000000111101_1 ep0000000111101_2))
private theorem idp0000000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011110.list =
    C ((2:ℤ)^278) * horner X vp0000000111101.list + horner X ep0000000111101.list := by
  exact edge_identity (B := (2:ℤ)^496) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111101 : Branch 1 (-59761639/2000000 : ℚ) vp000000011110 := by
  apply branch_checked idp0000000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-59761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-60761639/1000000 : ℚ) by norm_num]
  exact coverp0000000111101
theorem coverp000000011110 : Covers (-59761639/2000000 : ℚ) vp000000011110 := join_branches bp0000000111100 bp0000000111101
private noncomputable def vp00000001111_0 : Blocks := edgeBlocks% "full/vectors/00000001111-V-0000.bin"
private noncomputable def vp00000001111_1 : Blocks := edgeBlocks% "full/vectors/00000001111-V-0001.bin"
private noncomputable def vp00000001111_2 : Blocks := edgeBlocks% "full/vectors/00000001111-V-0002.bin"
private noncomputable def vp00000001111_3 : Blocks := edgeBlocks% "full/vectors/00000001111-V-0003.bin"
private noncomputable def vp00000001111_4 : Blocks := edgeBlocks% "full/vectors/00000001111-V-0004.bin"
noncomputable def vp00000001111 : Blocks := (Blocks.join (Blocks.join vp00000001111_0 vp00000001111_1) (Blocks.join vp00000001111_2 (Blocks.join vp00000001111_3 vp00000001111_4)))
private theorem bp000000011110 : Branch 0 (-59761639/4000000 : ℚ) vp00000001111 := by
  apply branch_left_normalized (c:=vp000000011110) (k:=0) (m:=269) (by decide +kernel)
  rw [show 2*(-59761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-59761639/2000000 : ℚ) by norm_num]
  exact coverp000000011110
private noncomputable def ep000000011111_0 : Blocks := edgeBlocks% "full/vectors/000000011111-E-0000.bin"
private noncomputable def ep000000011111_1 : Blocks := edgeBlocks% "full/vectors/000000011111-E-0001.bin"
private noncomputable def ep000000011111_2 : Blocks := edgeBlocks% "full/vectors/000000011111-E-0002.bin"
private noncomputable def ep000000011111_3 : Blocks := edgeBlocks% "full/vectors/000000011111-E-0003.bin"
private noncomputable def ep000000011111_4 : Blocks := edgeBlocks% "full/vectors/000000011111-E-0004.bin"
noncomputable def ep000000011111 : Blocks := (Blocks.join (Blocks.join ep000000011111_0 ep000000011111_1) (Blocks.join ep000000011111_2 (Blocks.join ep000000011111_3 ep000000011111_4)))
private theorem idp000000011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001111.list =
    C ((2:ℤ)^535) * horner X vp000000011111.list + horner X ep000000011111.list := by
  exact edge_identity (B := (2:ℤ)^882) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011111 : Branch 1 (-59761639/4000000 : ℚ) vp00000001111 := by
  apply branch_checked idp000000011111 (by positivity) (by decide +kernel)
  rw [show 2*(-59761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-61761639/2000000 : ℚ) by norm_num]
  exact coverp000000011111
theorem coverp00000001111 : Covers (-59761639/4000000 : ℚ) vp00000001111 := join_branches bp000000011110 bp000000011111
private noncomputable def vp000000011101111_0 : Blocks := edgeBlocks% "full/vectors/000000011101111-V-0000.bin"
noncomputable def vp000000011101111 : Blocks := vp000000011101111_0
theorem coverp000000011101111 : Covers (-59511639/250000 : ℚ) vp000000011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011101110_0 : Blocks := edgeBlocks% "full/vectors/000000011101110-V-0000.bin"
noncomputable def vp000000011101110 : Blocks := vp000000011101110_0
theorem coverp000000011101110 : Covers (-59261639/250000 : ℚ) vp000000011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001110111_0 : Blocks := edgeBlocks% "full/vectors/00000001110111-V-0000.bin"
noncomputable def vp00000001110111 : Blocks := vp00000001110111_0
private theorem bp000000011101110 : Branch 0 (-59261639/500000 : ℚ) vp00000001110111 := by
  apply branch_left_normalized (c:=vp000000011101110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-59261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-59261639/250000 : ℚ) by norm_num]
  exact coverp000000011101110
private noncomputable def ep000000011101111_0 : Blocks := edgeBlocks% "full/vectors/000000011101111-E-0000.bin"
noncomputable def ep000000011101111 : Blocks := ep000000011101111_0
private theorem idp000000011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001110111.list =
    C ((2:ℤ)^83) * horner X vp000000011101111.list + horner X ep000000011101111.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011101111 : Branch 1 (-59261639/500000 : ℚ) vp00000001110111 := by
  apply branch_checked idp000000011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-59261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-59511639/250000 : ℚ) by norm_num]
  exact coverp000000011101111
theorem coverp00000001110111 : Covers (-59261639/500000 : ℚ) vp00000001110111 := join_branches bp000000011101110 bp000000011101111
private noncomputable def vp000000011101101_0 : Blocks := edgeBlocks% "full/vectors/000000011101101-V-0000.bin"
noncomputable def vp000000011101101 : Blocks := vp000000011101101_0
theorem coverp000000011101101 : Covers (-59011639/250000 : ℚ) vp000000011101101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011101100_0 : Blocks := edgeBlocks% "full/vectors/000000011101100-V-0000.bin"
noncomputable def vp000000011101100 : Blocks := vp000000011101100_0
theorem coverp000000011101100 : Covers (-58761639/250000 : ℚ) vp000000011101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001110110_0 : Blocks := edgeBlocks% "full/vectors/00000001110110-V-0000.bin"
noncomputable def vp00000001110110 : Blocks := vp00000001110110_0
private theorem bp000000011101100 : Branch 0 (-58761639/500000 : ℚ) vp00000001110110 := by
  apply branch_left_normalized (c:=vp000000011101100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-58761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-58761639/250000 : ℚ) by norm_num]
  exact coverp000000011101100
private noncomputable def ep000000011101101_0 : Blocks := edgeBlocks% "full/vectors/000000011101101-E-0000.bin"
noncomputable def ep000000011101101 : Blocks := ep000000011101101_0
private theorem idp000000011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001110110.list =
    C ((2:ℤ)^85) * horner X vp000000011101101.list + horner X ep000000011101101.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011101101 : Branch 1 (-58761639/500000 : ℚ) vp00000001110110 := by
  apply branch_checked idp000000011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-58761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-59011639/250000 : ℚ) by norm_num]
  exact coverp000000011101101
theorem coverp00000001110110 : Covers (-58761639/500000 : ℚ) vp00000001110110 := join_branches bp000000011101100 bp000000011101101
private noncomputable def vp0000000111011_0 : Blocks := edgeBlocks% "full/vectors/0000000111011-V-0000.bin"
private noncomputable def vp0000000111011_1 : Blocks := edgeBlocks% "full/vectors/0000000111011-V-0001.bin"
noncomputable def vp0000000111011 : Blocks := (Blocks.join vp0000000111011_0 vp0000000111011_1)
private theorem bp00000001110110 : Branch 0 (-58761639/1000000 : ℚ) vp0000000111011 := by
  apply branch_left_normalized (c:=vp00000001110110) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-58761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-58761639/500000 : ℚ) by norm_num]
  exact coverp00000001110110
private noncomputable def ep00000001110111_0 : Blocks := edgeBlocks% "full/vectors/00000001110111-E-0000.bin"
private noncomputable def ep00000001110111_1 : Blocks := edgeBlocks% "full/vectors/00000001110111-E-0001.bin"
noncomputable def ep00000001110111 : Blocks := (Blocks.join ep00000001110111_0 ep00000001110111_1)
private theorem idp00000001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000111011.list =
    C ((2:ℤ)^151) * horner X vp00000001110111.list + horner X ep00000001110111.list := by
  exact edge_identity (B := (2:ℤ)^309) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001110111 : Branch 1 (-58761639/1000000 : ℚ) vp0000000111011 := by
  apply branch_checked idp00000001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-58761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-59261639/500000 : ℚ) by norm_num]
  exact coverp00000001110111
theorem coverp0000000111011 : Covers (-58761639/1000000 : ℚ) vp0000000111011 := join_branches bp00000001110110 bp00000001110111
private noncomputable def vp000000011101011_0 : Blocks := edgeBlocks% "full/vectors/000000011101011-V-0000.bin"
noncomputable def vp000000011101011 : Blocks := vp000000011101011_0
theorem coverp000000011101011 : Covers (-58511639/250000 : ℚ) vp000000011101011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011101010_0 : Blocks := edgeBlocks% "full/vectors/000000011101010-V-0000.bin"
noncomputable def vp000000011101010 : Blocks := vp000000011101010_0
theorem coverp000000011101010 : Covers (-58261639/250000 : ℚ) vp000000011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001110101_0 : Blocks := edgeBlocks% "full/vectors/00000001110101-V-0000.bin"
noncomputable def vp00000001110101 : Blocks := vp00000001110101_0
private theorem bp000000011101010 : Branch 0 (-58261639/500000 : ℚ) vp00000001110101 := by
  apply branch_left_normalized (c:=vp000000011101010) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-58261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-58261639/250000 : ℚ) by norm_num]
  exact coverp000000011101010
private noncomputable def ep000000011101011_0 : Blocks := edgeBlocks% "full/vectors/000000011101011-E-0000.bin"
noncomputable def ep000000011101011 : Blocks := ep000000011101011_0
private theorem idp000000011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001110101.list =
    C ((2:ℤ)^87) * horner X vp000000011101011.list + horner X ep000000011101011.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011101011 : Branch 1 (-58261639/500000 : ℚ) vp00000001110101 := by
  apply branch_checked idp000000011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-58261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-58511639/250000 : ℚ) by norm_num]
  exact coverp000000011101011
theorem coverp00000001110101 : Covers (-58261639/500000 : ℚ) vp00000001110101 := join_branches bp000000011101010 bp000000011101011
private noncomputable def vp0000000111010011_0 : Blocks := edgeBlocks% "full/vectors/0000000111010011-V-0000.bin"
noncomputable def vp0000000111010011 : Blocks := vp0000000111010011_0
theorem coverp0000000111010011 : Covers (-58136639/125000 : ℚ) vp0000000111010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000111010010_0 : Blocks := edgeBlocks% "full/vectors/0000000111010010-V-0000.bin"
noncomputable def vp0000000111010010 : Blocks := vp0000000111010010_0
theorem coverp0000000111010010 : Covers (-58011639/125000 : ℚ) vp0000000111010010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011101001_0 : Blocks := edgeBlocks% "full/vectors/000000011101001-V-0000.bin"
noncomputable def vp000000011101001 : Blocks := vp000000011101001_0
private theorem bp0000000111010010 : Branch 0 (-58011639/250000 : ℚ) vp000000011101001 := by
  apply branch_left_normalized (c:=vp0000000111010010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-58011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-58011639/125000 : ℚ) by norm_num]
  exact coverp0000000111010010
private noncomputable def ep0000000111010011_0 : Blocks := edgeBlocks% "full/vectors/0000000111010011-E-0000.bin"
noncomputable def ep0000000111010011 : Blocks := ep0000000111010011_0
private theorem idp0000000111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011101001.list =
    C ((2:ℤ)^54) * horner X vp0000000111010011.list + horner X ep0000000111010011.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111010011 : Branch 1 (-58011639/250000 : ℚ) vp000000011101001 := by
  apply branch_checked idp0000000111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-58011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-58136639/125000 : ℚ) by norm_num]
  exact coverp0000000111010011
theorem coverp000000011101001 : Covers (-58011639/250000 : ℚ) vp000000011101001 := join_branches bp0000000111010010 bp0000000111010011
private noncomputable def vp0000000111010001_0 : Blocks := edgeBlocks% "full/vectors/0000000111010001-V-0000.bin"
noncomputable def vp0000000111010001 : Blocks := vp0000000111010001_0
theorem coverp0000000111010001 : Covers (-57886639/125000 : ℚ) vp0000000111010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001110100001_0 : Blocks := edgeBlocks% "full/vectors/00000001110100001-V-0000.bin"
noncomputable def vp00000001110100001 : Blocks := vp00000001110100001_0
theorem coverp00000001110100001 : Covers (-57824139/62500 : ℚ) vp00000001110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000001110100000_0 : Blocks := edgeBlocks% "full/vectors/00000001110100000-V-0000.bin"
noncomputable def vp00000001110100000 : Blocks := vp00000001110100000_0
theorem coverp00000001110100000 : Covers (-57761639/62500 : ℚ) vp00000001110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000111010000_0 : Blocks := edgeBlocks% "full/vectors/0000000111010000-V-0000.bin"
noncomputable def vp0000000111010000 : Blocks := vp0000000111010000_0
private theorem bp00000001110100000 : Branch 0 (-57761639/125000 : ℚ) vp0000000111010000 := by
  apply branch_left_normalized (c:=vp00000001110100000) (k:=0) (m:=24) (by decide +kernel)
  rw [show 2*(-57761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-57761639/62500 : ℚ) by norm_num]
  exact coverp00000001110100000
private noncomputable def ep00000001110100001_0 : Blocks := edgeBlocks% "full/vectors/00000001110100001-E-0000.bin"
noncomputable def ep00000001110100001 : Blocks := ep00000001110100001_0
private theorem idp00000001110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000111010000.list =
    C ((2:ℤ)^35) * horner X vp00000001110100001.list + horner X ep00000001110100001.list := by
  exact edge_identity (B := (2:ℤ)^148) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001110100001 : Branch 1 (-57761639/125000 : ℚ) vp0000000111010000 := by
  apply branch_checked idp00000001110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-57761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-57824139/62500 : ℚ) by norm_num]
  exact coverp00000001110100001
theorem coverp0000000111010000 : Covers (-57761639/125000 : ℚ) vp0000000111010000 := join_branches bp00000001110100000 bp00000001110100001
private noncomputable def vp000000011101000_0 : Blocks := edgeBlocks% "full/vectors/000000011101000-V-0000.bin"
noncomputable def vp000000011101000 : Blocks := vp000000011101000_0
private theorem bp0000000111010000 : Branch 0 (-57761639/250000 : ℚ) vp000000011101000 := by
  apply branch_left_normalized (c:=vp0000000111010000) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-57761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-57761639/125000 : ℚ) by norm_num]
  exact coverp0000000111010000
private noncomputable def ep0000000111010001_0 : Blocks := edgeBlocks% "full/vectors/0000000111010001-E-0000.bin"
noncomputable def ep0000000111010001 : Blocks := ep0000000111010001_0
private theorem idp0000000111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011101000.list =
    C ((2:ℤ)^54) * horner X vp0000000111010001.list + horner X ep0000000111010001.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111010001 : Branch 1 (-57761639/250000 : ℚ) vp000000011101000 := by
  apply branch_checked idp0000000111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-57761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-57886639/125000 : ℚ) by norm_num]
  exact coverp0000000111010001
theorem coverp000000011101000 : Covers (-57761639/250000 : ℚ) vp000000011101000 := join_branches bp0000000111010000 bp0000000111010001
private noncomputable def vp00000001110100_0 : Blocks := edgeBlocks% "full/vectors/00000001110100-V-0000.bin"
noncomputable def vp00000001110100 : Blocks := vp00000001110100_0
private theorem bp000000011101000 : Branch 0 (-57761639/500000 : ℚ) vp00000001110100 := by
  apply branch_left_normalized (c:=vp000000011101000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-57761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-57761639/250000 : ℚ) by norm_num]
  exact coverp000000011101000
private noncomputable def ep000000011101001_0 : Blocks := edgeBlocks% "full/vectors/000000011101001-E-0000.bin"
noncomputable def ep000000011101001 : Blocks := ep000000011101001_0
private theorem idp000000011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001110100.list =
    C ((2:ℤ)^92) * horner X vp000000011101001.list + horner X ep000000011101001.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011101001 : Branch 1 (-57761639/500000 : ℚ) vp00000001110100 := by
  apply branch_checked idp000000011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-57761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-58011639/250000 : ℚ) by norm_num]
  exact coverp000000011101001
theorem coverp00000001110100 : Covers (-57761639/500000 : ℚ) vp00000001110100 := join_branches bp000000011101000 bp000000011101001
private noncomputable def vp0000000111010_0 : Blocks := edgeBlocks% "full/vectors/0000000111010-V-0000.bin"
private noncomputable def vp0000000111010_1 : Blocks := edgeBlocks% "full/vectors/0000000111010-V-0001.bin"
noncomputable def vp0000000111010 : Blocks := (Blocks.join vp0000000111010_0 vp0000000111010_1)
private theorem bp00000001110100 : Branch 0 (-57761639/1000000 : ℚ) vp0000000111010 := by
  apply branch_left_normalized (c:=vp00000001110100) (k:=0) (m:=86) (by decide +kernel)
  rw [show 2*(-57761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-57761639/500000 : ℚ) by norm_num]
  exact coverp00000001110100
private noncomputable def ep00000001110101_0 : Blocks := edgeBlocks% "full/vectors/00000001110101-E-0000.bin"
private noncomputable def ep00000001110101_1 : Blocks := edgeBlocks% "full/vectors/00000001110101-E-0001.bin"
noncomputable def ep00000001110101 : Blocks := (Blocks.join ep00000001110101_0 ep00000001110101_1)
private theorem idp00000001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000111010.list =
    C ((2:ℤ)^162) * horner X vp00000001110101.list + horner X ep00000001110101.list := by
  exact edge_identity (B := (2:ℤ)^325) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001110101 : Branch 1 (-57761639/1000000 : ℚ) vp0000000111010 := by
  apply branch_checked idp00000001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-57761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-58261639/500000 : ℚ) by norm_num]
  exact coverp00000001110101
theorem coverp0000000111010 : Covers (-57761639/1000000 : ℚ) vp0000000111010 := join_branches bp00000001110100 bp00000001110101
private noncomputable def vp000000011101_0 : Blocks := edgeBlocks% "full/vectors/000000011101-V-0000.bin"
private noncomputable def vp000000011101_1 : Blocks := edgeBlocks% "full/vectors/000000011101-V-0001.bin"
private noncomputable def vp000000011101_2 : Blocks := edgeBlocks% "full/vectors/000000011101-V-0002.bin"
noncomputable def vp000000011101 : Blocks := (Blocks.join vp000000011101_0 (Blocks.join vp000000011101_1 vp000000011101_2))
private theorem bp0000000111010 : Branch 0 (-57761639/2000000 : ℚ) vp000000011101 := by
  apply branch_left_normalized (c:=vp0000000111010) (k:=0) (m:=152) (by decide +kernel)
  rw [show 2*(-57761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-57761639/1000000 : ℚ) by norm_num]
  exact coverp0000000111010
private noncomputable def ep0000000111011_0 : Blocks := edgeBlocks% "full/vectors/0000000111011-E-0000.bin"
private noncomputable def ep0000000111011_1 : Blocks := edgeBlocks% "full/vectors/0000000111011-E-0001.bin"
private noncomputable def ep0000000111011_2 : Blocks := edgeBlocks% "full/vectors/0000000111011-E-0002.bin"
noncomputable def ep0000000111011 : Blocks := (Blocks.join ep0000000111011_0 (Blocks.join ep0000000111011_1 ep0000000111011_2))
private theorem idp0000000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011101.list =
    C ((2:ℤ)^296) * horner X vp0000000111011.list + horner X ep0000000111011.list := by
  exact edge_identity (B := (2:ℤ)^522) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111011 : Branch 1 (-57761639/2000000 : ℚ) vp000000011101 := by
  apply branch_checked idp0000000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-57761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-58761639/1000000 : ℚ) by norm_num]
  exact coverp0000000111011
theorem coverp000000011101 : Covers (-57761639/2000000 : ℚ) vp000000011101 := join_branches bp0000000111010 bp0000000111011
private noncomputable def vp0000000111001111_0 : Blocks := edgeBlocks% "full/vectors/0000000111001111-V-0000.bin"
noncomputable def vp0000000111001111 : Blocks := vp0000000111001111_0
theorem coverp0000000111001111 : Covers (-57636639/125000 : ℚ) vp0000000111001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000111001110_0 : Blocks := edgeBlocks% "full/vectors/0000000111001110-V-0000.bin"
noncomputable def vp0000000111001110 : Blocks := vp0000000111001110_0
theorem coverp0000000111001110 : Covers (-57511639/125000 : ℚ) vp0000000111001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011100111_0 : Blocks := edgeBlocks% "full/vectors/000000011100111-V-0000.bin"
noncomputable def vp000000011100111 : Blocks := vp000000011100111_0
private theorem bp0000000111001110 : Branch 0 (-57511639/250000 : ℚ) vp000000011100111 := by
  apply branch_left_normalized (c:=vp0000000111001110) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-57511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-57511639/125000 : ℚ) by norm_num]
  exact coverp0000000111001110
private noncomputable def ep0000000111001111_0 : Blocks := edgeBlocks% "full/vectors/0000000111001111-E-0000.bin"
noncomputable def ep0000000111001111 : Blocks := ep0000000111001111_0
private theorem idp0000000111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011100111.list =
    C ((2:ℤ)^52) * horner X vp0000000111001111.list + horner X ep0000000111001111.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111001111 : Branch 1 (-57511639/250000 : ℚ) vp000000011100111 := by
  apply branch_checked idp0000000111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-57511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-57636639/125000 : ℚ) by norm_num]
  exact coverp0000000111001111
theorem coverp000000011100111 : Covers (-57511639/250000 : ℚ) vp000000011100111 := join_branches bp0000000111001110 bp0000000111001111
private noncomputable def vp0000000111001101_0 : Blocks := edgeBlocks% "full/vectors/0000000111001101-V-0000.bin"
noncomputable def vp0000000111001101 : Blocks := vp0000000111001101_0
theorem coverp0000000111001101 : Covers (-57386639/125000 : ℚ) vp0000000111001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000111001100_0 : Blocks := edgeBlocks% "full/vectors/0000000111001100-V-0000.bin"
noncomputable def vp0000000111001100 : Blocks := vp0000000111001100_0
theorem coverp0000000111001100 : Covers (-57261639/125000 : ℚ) vp0000000111001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011100110_0 : Blocks := edgeBlocks% "full/vectors/000000011100110-V-0000.bin"
noncomputable def vp000000011100110 : Blocks := vp000000011100110_0
private theorem bp0000000111001100 : Branch 0 (-57261639/250000 : ℚ) vp000000011100110 := by
  apply branch_left_normalized (c:=vp0000000111001100) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-57261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-57261639/125000 : ℚ) by norm_num]
  exact coverp0000000111001100
private noncomputable def ep0000000111001101_0 : Blocks := edgeBlocks% "full/vectors/0000000111001101-E-0000.bin"
noncomputable def ep0000000111001101 : Blocks := ep0000000111001101_0
private theorem idp0000000111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011100110.list =
    C ((2:ℤ)^51) * horner X vp0000000111001101.list + horner X ep0000000111001101.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111001101 : Branch 1 (-57261639/250000 : ℚ) vp000000011100110 := by
  apply branch_checked idp0000000111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-57261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-57386639/125000 : ℚ) by norm_num]
  exact coverp0000000111001101
theorem coverp000000011100110 : Covers (-57261639/250000 : ℚ) vp000000011100110 := join_branches bp0000000111001100 bp0000000111001101
private noncomputable def vp00000001110011_0 : Blocks := edgeBlocks% "full/vectors/00000001110011-V-0000.bin"
noncomputable def vp00000001110011 : Blocks := vp00000001110011_0
private theorem bp000000011100110 : Branch 0 (-57261639/500000 : ℚ) vp00000001110011 := by
  apply branch_left_normalized (c:=vp000000011100110) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-57261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-57261639/250000 : ℚ) by norm_num]
  exact coverp000000011100110
private noncomputable def ep000000011100111_0 : Blocks := edgeBlocks% "full/vectors/000000011100111-E-0000.bin"
noncomputable def ep000000011100111 : Blocks := ep000000011100111_0
private theorem idp000000011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001110011.list =
    C ((2:ℤ)^86) * horner X vp000000011100111.list + horner X ep000000011100111.list := by
  exact edge_identity (B := (2:ℤ)^219) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011100111 : Branch 1 (-57261639/500000 : ℚ) vp00000001110011 := by
  apply branch_checked idp000000011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-57261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-57511639/250000 : ℚ) by norm_num]
  exact coverp000000011100111
theorem coverp00000001110011 : Covers (-57261639/500000 : ℚ) vp00000001110011 := join_branches bp000000011100110 bp000000011100111
private noncomputable def vp0000000111001011_0 : Blocks := edgeBlocks% "full/vectors/0000000111001011-V-0000.bin"
noncomputable def vp0000000111001011 : Blocks := vp0000000111001011_0
theorem coverp0000000111001011 : Covers (-57136639/125000 : ℚ) vp0000000111001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000111001010_0 : Blocks := edgeBlocks% "full/vectors/0000000111001010-V-0000.bin"
noncomputable def vp0000000111001010 : Blocks := vp0000000111001010_0
theorem coverp0000000111001010 : Covers (-57011639/125000 : ℚ) vp0000000111001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011100101_0 : Blocks := edgeBlocks% "full/vectors/000000011100101-V-0000.bin"
noncomputable def vp000000011100101 : Blocks := vp000000011100101_0
private theorem bp0000000111001010 : Branch 0 (-57011639/250000 : ℚ) vp000000011100101 := by
  apply branch_left_normalized (c:=vp0000000111001010) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-57011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-57011639/125000 : ℚ) by norm_num]
  exact coverp0000000111001010
private noncomputable def ep0000000111001011_0 : Blocks := edgeBlocks% "full/vectors/0000000111001011-E-0000.bin"
noncomputable def ep0000000111001011 : Blocks := ep0000000111001011_0
private theorem idp0000000111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011100101.list =
    C ((2:ℤ)^51) * horner X vp0000000111001011.list + horner X ep0000000111001011.list := by
  exact edge_identity (B := (2:ℤ)^167) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111001011 : Branch 1 (-57011639/250000 : ℚ) vp000000011100101 := by
  apply branch_checked idp0000000111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-57011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-57136639/125000 : ℚ) by norm_num]
  exact coverp0000000111001011
theorem coverp000000011100101 : Covers (-57011639/250000 : ℚ) vp000000011100101 := join_branches bp0000000111001010 bp0000000111001011
private noncomputable def vp0000000111001001_0 : Blocks := edgeBlocks% "full/vectors/0000000111001001-V-0000.bin"
noncomputable def vp0000000111001001 : Blocks := vp0000000111001001_0
theorem coverp0000000111001001 : Covers (-56886639/125000 : ℚ) vp0000000111001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000111001000_0 : Blocks := edgeBlocks% "full/vectors/0000000111001000-V-0000.bin"
noncomputable def vp0000000111001000 : Blocks := vp0000000111001000_0
theorem coverp0000000111001000 : Covers (-56761639/125000 : ℚ) vp0000000111001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011100100_0 : Blocks := edgeBlocks% "full/vectors/000000011100100-V-0000.bin"
noncomputable def vp000000011100100 : Blocks := vp000000011100100_0
private theorem bp0000000111001000 : Branch 0 (-56761639/250000 : ℚ) vp000000011100100 := by
  apply branch_left_normalized (c:=vp0000000111001000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-56761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-56761639/125000 : ℚ) by norm_num]
  exact coverp0000000111001000
private noncomputable def ep0000000111001001_0 : Blocks := edgeBlocks% "full/vectors/0000000111001001-E-0000.bin"
noncomputable def ep0000000111001001 : Blocks := ep0000000111001001_0
private theorem idp0000000111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011100100.list =
    C ((2:ℤ)^53) * horner X vp0000000111001001.list + horner X ep0000000111001001.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111001001 : Branch 1 (-56761639/250000 : ℚ) vp000000011100100 := by
  apply branch_checked idp0000000111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-56761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-56886639/125000 : ℚ) by norm_num]
  exact coverp0000000111001001
theorem coverp000000011100100 : Covers (-56761639/250000 : ℚ) vp000000011100100 := join_branches bp0000000111001000 bp0000000111001001
private noncomputable def vp00000001110010_0 : Blocks := edgeBlocks% "full/vectors/00000001110010-V-0000.bin"
noncomputable def vp00000001110010 : Blocks := vp00000001110010_0
private theorem bp000000011100100 : Branch 0 (-56761639/500000 : ℚ) vp00000001110010 := by
  apply branch_left_normalized (c:=vp000000011100100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-56761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-56761639/250000 : ℚ) by norm_num]
  exact coverp000000011100100
private noncomputable def ep000000011100101_0 : Blocks := edgeBlocks% "full/vectors/000000011100101-E-0000.bin"
noncomputable def ep000000011100101 : Blocks := ep000000011100101_0
private theorem idp000000011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001110010.list =
    C ((2:ℤ)^88) * horner X vp000000011100101.list + horner X ep000000011100101.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011100101 : Branch 1 (-56761639/500000 : ℚ) vp00000001110010 := by
  apply branch_checked idp000000011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-56761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-57011639/250000 : ℚ) by norm_num]
  exact coverp000000011100101
theorem coverp00000001110010 : Covers (-56761639/500000 : ℚ) vp00000001110010 := join_branches bp000000011100100 bp000000011100101
private noncomputable def vp0000000111001_0 : Blocks := edgeBlocks% "full/vectors/0000000111001-V-0000.bin"
private noncomputable def vp0000000111001_1 : Blocks := edgeBlocks% "full/vectors/0000000111001-V-0001.bin"
noncomputable def vp0000000111001 : Blocks := (Blocks.join vp0000000111001_0 vp0000000111001_1)
private theorem bp00000001110010 : Branch 0 (-56761639/1000000 : ℚ) vp0000000111001 := by
  apply branch_left_normalized (c:=vp00000001110010) (k:=0) (m:=85) (by decide +kernel)
  rw [show 2*(-56761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-56761639/500000 : ℚ) by norm_num]
  exact coverp00000001110010
private noncomputable def ep00000001110011_0 : Blocks := edgeBlocks% "full/vectors/00000001110011-E-0000.bin"
private noncomputable def ep00000001110011_1 : Blocks := edgeBlocks% "full/vectors/00000001110011-E-0001.bin"
noncomputable def ep00000001110011 : Blocks := (Blocks.join ep00000001110011_0 ep00000001110011_1)
private theorem idp00000001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000111001.list =
    C ((2:ℤ)^155) * horner X vp00000001110011.list + horner X ep00000001110011.list := by
  exact edge_identity (B := (2:ℤ)^320) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001110011 : Branch 1 (-56761639/1000000 : ℚ) vp0000000111001 := by
  apply branch_checked idp00000001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-56761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-57261639/500000 : ℚ) by norm_num]
  exact coverp00000001110011
theorem coverp0000000111001 : Covers (-56761639/1000000 : ℚ) vp0000000111001 := join_branches bp00000001110010 bp00000001110011
private noncomputable def vp0000000111000111_0 : Blocks := edgeBlocks% "full/vectors/0000000111000111-V-0000.bin"
noncomputable def vp0000000111000111 : Blocks := vp0000000111000111_0
theorem coverp0000000111000111 : Covers (-56636639/125000 : ℚ) vp0000000111000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000111000110_0 : Blocks := edgeBlocks% "full/vectors/0000000111000110-V-0000.bin"
noncomputable def vp0000000111000110 : Blocks := vp0000000111000110_0
theorem coverp0000000111000110 : Covers (-56511639/125000 : ℚ) vp0000000111000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011100011_0 : Blocks := edgeBlocks% "full/vectors/000000011100011-V-0000.bin"
noncomputable def vp000000011100011 : Blocks := vp000000011100011_0
private theorem bp0000000111000110 : Branch 0 (-56511639/250000 : ℚ) vp000000011100011 := by
  apply branch_left_normalized (c:=vp0000000111000110) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-56511639/250000 : ℚ) - ((0:ℤ):ℚ) = (-56511639/125000 : ℚ) by norm_num]
  exact coverp0000000111000110
private noncomputable def ep0000000111000111_0 : Blocks := edgeBlocks% "full/vectors/0000000111000111-E-0000.bin"
noncomputable def ep0000000111000111 : Blocks := ep0000000111000111_0
private theorem idp0000000111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011100011.list =
    C ((2:ℤ)^53) * horner X vp0000000111000111.list + horner X ep0000000111000111.list := by
  exact edge_identity (B := (2:ℤ)^169) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111000111 : Branch 1 (-56511639/250000 : ℚ) vp000000011100011 := by
  apply branch_checked idp0000000111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-56511639/250000 : ℚ) - ((1:ℤ):ℚ) = (-56636639/125000 : ℚ) by norm_num]
  exact coverp0000000111000111
theorem coverp000000011100011 : Covers (-56511639/250000 : ℚ) vp000000011100011 := join_branches bp0000000111000110 bp0000000111000111
private noncomputable def vp0000000111000101_0 : Blocks := edgeBlocks% "full/vectors/0000000111000101-V-0000.bin"
noncomputable def vp0000000111000101 : Blocks := vp0000000111000101_0
theorem coverp0000000111000101 : Covers (-56386639/125000 : ℚ) vp0000000111000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000111000100_0 : Blocks := edgeBlocks% "full/vectors/0000000111000100-V-0000.bin"
noncomputable def vp0000000111000100 : Blocks := vp0000000111000100_0
theorem coverp0000000111000100 : Covers (-56261639/125000 : ℚ) vp0000000111000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011100010_0 : Blocks := edgeBlocks% "full/vectors/000000011100010-V-0000.bin"
noncomputable def vp000000011100010 : Blocks := vp000000011100010_0
private theorem bp0000000111000100 : Branch 0 (-56261639/250000 : ℚ) vp000000011100010 := by
  apply branch_left_normalized (c:=vp0000000111000100) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-56261639/250000 : ℚ) - ((0:ℤ):ℚ) = (-56261639/125000 : ℚ) by norm_num]
  exact coverp0000000111000100
private noncomputable def ep0000000111000101_0 : Blocks := edgeBlocks% "full/vectors/0000000111000101-E-0000.bin"
noncomputable def ep0000000111000101 : Blocks := ep0000000111000101_0
private theorem idp0000000111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011100010.list =
    C ((2:ℤ)^54) * horner X vp0000000111000101.list + horner X ep0000000111000101.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111000101 : Branch 1 (-56261639/250000 : ℚ) vp000000011100010 := by
  apply branch_checked idp0000000111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-56261639/250000 : ℚ) - ((1:ℤ):ℚ) = (-56386639/125000 : ℚ) by norm_num]
  exact coverp0000000111000101
theorem coverp000000011100010 : Covers (-56261639/250000 : ℚ) vp000000011100010 := join_branches bp0000000111000100 bp0000000111000101
private noncomputable def vp00000001110001_0 : Blocks := edgeBlocks% "full/vectors/00000001110001-V-0000.bin"
noncomputable def vp00000001110001 : Blocks := vp00000001110001_0
private theorem bp000000011100010 : Branch 0 (-56261639/500000 : ℚ) vp00000001110001 := by
  apply branch_left_normalized (c:=vp000000011100010) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-56261639/500000 : ℚ) - ((0:ℤ):ℚ) = (-56261639/250000 : ℚ) by norm_num]
  exact coverp000000011100010
private noncomputable def ep000000011100011_0 : Blocks := edgeBlocks% "full/vectors/000000011100011-E-0000.bin"
noncomputable def ep000000011100011 : Blocks := ep000000011100011_0
private theorem idp000000011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001110001.list =
    C ((2:ℤ)^90) * horner X vp000000011100011.list + horner X ep000000011100011.list := by
  exact edge_identity (B := (2:ℤ)^223) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011100011 : Branch 1 (-56261639/500000 : ℚ) vp00000001110001 := by
  apply branch_checked idp000000011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-56261639/500000 : ℚ) - ((1:ℤ):ℚ) = (-56511639/250000 : ℚ) by norm_num]
  exact coverp000000011100011
theorem coverp00000001110001 : Covers (-56261639/500000 : ℚ) vp00000001110001 := join_branches bp000000011100010 bp000000011100011
private noncomputable def vp0000000111000011_0 : Blocks := edgeBlocks% "full/vectors/0000000111000011-V-0000.bin"
noncomputable def vp0000000111000011 : Blocks := vp0000000111000011_0
theorem coverp0000000111000011 : Covers (-56136639/125000 : ℚ) vp0000000111000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000111000010_0 : Blocks := edgeBlocks% "full/vectors/0000000111000010-V-0000.bin"
noncomputable def vp0000000111000010 : Blocks := vp0000000111000010_0
theorem coverp0000000111000010 : Covers (-56011639/125000 : ℚ) vp0000000111000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011100001_0 : Blocks := edgeBlocks% "full/vectors/000000011100001-V-0000.bin"
noncomputable def vp000000011100001 : Blocks := vp000000011100001_0
private theorem bp0000000111000010 : Branch 0 (-56011639/250000 : ℚ) vp000000011100001 := by
  apply branch_left_normalized (c:=vp0000000111000010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-56011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-56011639/125000 : ℚ) by norm_num]
  exact coverp0000000111000010
private noncomputable def ep0000000111000011_0 : Blocks := edgeBlocks% "full/vectors/0000000111000011-E-0000.bin"
noncomputable def ep0000000111000011 : Blocks := ep0000000111000011_0
private theorem idp0000000111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011100001.list =
    C ((2:ℤ)^56) * horner X vp0000000111000011.list + horner X ep0000000111000011.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111000011 : Branch 1 (-56011639/250000 : ℚ) vp000000011100001 := by
  apply branch_checked idp0000000111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-56011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-56136639/125000 : ℚ) by norm_num]
  exact coverp0000000111000011
theorem coverp000000011100001 : Covers (-56011639/250000 : ℚ) vp000000011100001 := join_branches bp0000000111000010 bp0000000111000011
private noncomputable def vp0000000111000001_0 : Blocks := edgeBlocks% "full/vectors/0000000111000001-V-0000.bin"
noncomputable def vp0000000111000001 : Blocks := vp0000000111000001_0
theorem coverp0000000111000001 : Covers (-55886639/125000 : ℚ) vp0000000111000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000111000000_0 : Blocks := edgeBlocks% "full/vectors/0000000111000000-V-0000.bin"
noncomputable def vp0000000111000000 : Blocks := vp0000000111000000_0
theorem coverp0000000111000000 : Covers (-55761639/125000 : ℚ) vp0000000111000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000011100000_0 : Blocks := edgeBlocks% "full/vectors/000000011100000-V-0000.bin"
noncomputable def vp000000011100000 : Blocks := vp000000011100000_0
private theorem bp0000000111000000 : Branch 0 (-55761639/250000 : ℚ) vp000000011100000 := by
  apply branch_left_normalized (c:=vp0000000111000000) (k:=0) (m:=33) (by decide +kernel)
  rw [show 2*(-55761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-55761639/125000 : ℚ) by norm_num]
  exact coverp0000000111000000
private noncomputable def ep0000000111000001_0 : Blocks := edgeBlocks% "full/vectors/0000000111000001-E-0000.bin"
noncomputable def ep0000000111000001 : Blocks := ep0000000111000001_0
private theorem idp0000000111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011100000.list =
    C ((2:ℤ)^53) * horner X vp0000000111000001.list + horner X ep0000000111000001.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111000001 : Branch 1 (-55761639/250000 : ℚ) vp000000011100000 := by
  apply branch_checked idp0000000111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-55761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-55886639/125000 : ℚ) by norm_num]
  exact coverp0000000111000001
theorem coverp000000011100000 : Covers (-55761639/250000 : ℚ) vp000000011100000 := join_branches bp0000000111000000 bp0000000111000001
private noncomputable def vp00000001110000_0 : Blocks := edgeBlocks% "full/vectors/00000001110000-V-0000.bin"
noncomputable def vp00000001110000 : Blocks := vp00000001110000_0
private theorem bp000000011100000 : Branch 0 (-55761639/500000 : ℚ) vp00000001110000 := by
  apply branch_left_normalized (c:=vp000000011100000) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-55761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-55761639/250000 : ℚ) by norm_num]
  exact coverp000000011100000
private noncomputable def ep000000011100001_0 : Blocks := edgeBlocks% "full/vectors/000000011100001-E-0000.bin"
noncomputable def ep000000011100001 : Blocks := ep000000011100001_0
private theorem idp000000011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001110000.list =
    C ((2:ℤ)^88) * horner X vp000000011100001.list + horner X ep000000011100001.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011100001 : Branch 1 (-55761639/500000 : ℚ) vp00000001110000 := by
  apply branch_checked idp000000011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-55761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-56011639/250000 : ℚ) by norm_num]
  exact coverp000000011100001
theorem coverp00000001110000 : Covers (-55761639/500000 : ℚ) vp00000001110000 := join_branches bp000000011100000 bp000000011100001
private noncomputable def vp0000000111000_0 : Blocks := edgeBlocks% "full/vectors/0000000111000-V-0000.bin"
private noncomputable def vp0000000111000_1 : Blocks := edgeBlocks% "full/vectors/0000000111000-V-0001.bin"
noncomputable def vp0000000111000 : Blocks := (Blocks.join vp0000000111000_0 vp0000000111000_1)
private theorem bp00000001110000 : Branch 0 (-55761639/1000000 : ℚ) vp0000000111000 := by
  apply branch_left_normalized (c:=vp00000001110000) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-55761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-55761639/500000 : ℚ) by norm_num]
  exact coverp00000001110000
private noncomputable def ep00000001110001_0 : Blocks := edgeBlocks% "full/vectors/00000001110001-E-0000.bin"
private noncomputable def ep00000001110001_1 : Blocks := edgeBlocks% "full/vectors/00000001110001-E-0001.bin"
noncomputable def ep00000001110001 : Blocks := (Blocks.join ep00000001110001_0 ep00000001110001_1)
private theorem idp00000001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000111000.list =
    C ((2:ℤ)^159) * horner X vp00000001110001.list + horner X ep00000001110001.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001110001 : Branch 1 (-55761639/1000000 : ℚ) vp0000000111000 := by
  apply branch_checked idp00000001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-55761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-56261639/500000 : ℚ) by norm_num]
  exact coverp00000001110001
theorem coverp0000000111000 : Covers (-55761639/1000000 : ℚ) vp0000000111000 := join_branches bp00000001110000 bp00000001110001
private noncomputable def vp000000011100_0 : Blocks := edgeBlocks% "full/vectors/000000011100-V-0000.bin"
private noncomputable def vp000000011100_1 : Blocks := edgeBlocks% "full/vectors/000000011100-V-0001.bin"
private noncomputable def vp000000011100_2 : Blocks := edgeBlocks% "full/vectors/000000011100-V-0002.bin"
noncomputable def vp000000011100 : Blocks := (Blocks.join vp000000011100_0 (Blocks.join vp000000011100_1 vp000000011100_2))
private theorem bp0000000111000 : Branch 0 (-55761639/2000000 : ℚ) vp000000011100 := by
  apply branch_left_normalized (c:=vp0000000111000) (k:=0) (m:=154) (by decide +kernel)
  rw [show 2*(-55761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-55761639/1000000 : ℚ) by norm_num]
  exact coverp0000000111000
private noncomputable def ep0000000111001_0 : Blocks := edgeBlocks% "full/vectors/0000000111001-E-0000.bin"
private noncomputable def ep0000000111001_1 : Blocks := edgeBlocks% "full/vectors/0000000111001-E-0001.bin"
private noncomputable def ep0000000111001_2 : Blocks := edgeBlocks% "full/vectors/0000000111001-E-0002.bin"
noncomputable def ep0000000111001 : Blocks := (Blocks.join ep0000000111001_0 (Blocks.join ep0000000111001_1 ep0000000111001_2))
private theorem idp0000000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000011100.list =
    C ((2:ℤ)^295) * horner X vp0000000111001.list + horner X ep0000000111001.list := by
  exact edge_identity (B := (2:ℤ)^528) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000111001 : Branch 1 (-55761639/2000000 : ℚ) vp000000011100 := by
  apply branch_checked idp0000000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-55761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-56761639/1000000 : ℚ) by norm_num]
  exact coverp0000000111001
theorem coverp000000011100 : Covers (-55761639/2000000 : ℚ) vp000000011100 := join_branches bp0000000111000 bp0000000111001
private noncomputable def vp00000001110_0 : Blocks := edgeBlocks% "full/vectors/00000001110-V-0000.bin"
private noncomputable def vp00000001110_1 : Blocks := edgeBlocks% "full/vectors/00000001110-V-0001.bin"
private noncomputable def vp00000001110_2 : Blocks := edgeBlocks% "full/vectors/00000001110-V-0002.bin"
private noncomputable def vp00000001110_3 : Blocks := edgeBlocks% "full/vectors/00000001110-V-0003.bin"
private noncomputable def vp00000001110_4 : Blocks := edgeBlocks% "full/vectors/00000001110-V-0004.bin"
noncomputable def vp00000001110 : Blocks := (Blocks.join (Blocks.join vp00000001110_0 vp00000001110_1) (Blocks.join vp00000001110_2 (Blocks.join vp00000001110_3 vp00000001110_4)))
private theorem bp000000011100 : Branch 0 (-55761639/4000000 : ℚ) vp00000001110 := by
  apply branch_left_normalized (c:=vp000000011100) (k:=0) (m:=285) (by decide +kernel)
  rw [show 2*(-55761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-55761639/2000000 : ℚ) by norm_num]
  exact coverp000000011100
private noncomputable def ep000000011101_0 : Blocks := edgeBlocks% "full/vectors/000000011101-E-0000.bin"
private noncomputable def ep000000011101_1 : Blocks := edgeBlocks% "full/vectors/000000011101-E-0001.bin"
private noncomputable def ep000000011101_2 : Blocks := edgeBlocks% "full/vectors/000000011101-E-0002.bin"
private noncomputable def ep000000011101_3 : Blocks := edgeBlocks% "full/vectors/000000011101-E-0003.bin"
private noncomputable def ep000000011101_4 : Blocks := edgeBlocks% "full/vectors/000000011101-E-0004.bin"
noncomputable def ep000000011101 : Blocks := (Blocks.join (Blocks.join ep000000011101_0 ep000000011101_1) (Blocks.join ep000000011101_2 (Blocks.join ep000000011101_3 ep000000011101_4)))
private theorem idp000000011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000001110.list =
    C ((2:ℤ)^557) * horner X vp000000011101.list + horner X ep000000011101.list := by
  exact edge_identity (B := (2:ℤ)^927) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000011101 : Branch 1 (-55761639/4000000 : ℚ) vp00000001110 := by
  apply branch_checked idp000000011101 (by positivity) (by decide +kernel)
  rw [show 2*(-55761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-57761639/2000000 : ℚ) by norm_num]
  exact coverp000000011101
theorem coverp00000001110 : Covers (-55761639/4000000 : ℚ) vp00000001110 := join_branches bp000000011100 bp000000011101
private noncomputable def vp0000000111_0 : Blocks := edgeBlocks% "full/vectors/0000000111-V-0000.bin"
private noncomputable def vp0000000111_1 : Blocks := edgeBlocks% "full/vectors/0000000111-V-0001.bin"
private noncomputable def vp0000000111_2 : Blocks := edgeBlocks% "full/vectors/0000000111-V-0002.bin"
private noncomputable def vp0000000111_3 : Blocks := edgeBlocks% "full/vectors/0000000111-V-0003.bin"
private noncomputable def vp0000000111_4 : Blocks := edgeBlocks% "full/vectors/0000000111-V-0004.bin"
private noncomputable def vp0000000111_5 : Blocks := edgeBlocks% "full/vectors/0000000111-V-0005.bin"
private noncomputable def vp0000000111_6 : Blocks := edgeBlocks% "full/vectors/0000000111-V-0006.bin"
private noncomputable def vp0000000111_7 : Blocks := edgeBlocks% "full/vectors/0000000111-V-0007.bin"
private noncomputable def vp0000000111_8 : Blocks := edgeBlocks% "full/vectors/0000000111-V-0008.bin"
noncomputable def vp0000000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0000000111_0 vp0000000111_1) (Blocks.join vp0000000111_2 vp0000000111_3)) (Blocks.join (Blocks.join vp0000000111_4 vp0000000111_5) (Blocks.join vp0000000111_6 (Blocks.join vp0000000111_7 vp0000000111_8))))
private theorem bp00000001110 : Branch 0 (-55761639/8000000 : ℚ) vp0000000111 := by
  apply branch_left_normalized (c:=vp00000001110) (k:=0) (m:=545) (by decide +kernel)
  rw [show 2*(-55761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-55761639/4000000 : ℚ) by norm_num]
  exact coverp00000001110
private noncomputable def ep00000001111_0 : Blocks := edgeBlocks% "full/vectors/00000001111-E-0000.bin"
private noncomputable def ep00000001111_1 : Blocks := edgeBlocks% "full/vectors/00000001111-E-0001.bin"
private noncomputable def ep00000001111_2 : Blocks := edgeBlocks% "full/vectors/00000001111-E-0002.bin"
private noncomputable def ep00000001111_3 : Blocks := edgeBlocks% "full/vectors/00000001111-E-0003.bin"
private noncomputable def ep00000001111_4 : Blocks := edgeBlocks% "full/vectors/00000001111-E-0004.bin"
private noncomputable def ep00000001111_5 : Blocks := edgeBlocks% "full/vectors/00000001111-E-0005.bin"
private noncomputable def ep00000001111_6 : Blocks := edgeBlocks% "full/vectors/00000001111-E-0006.bin"
private noncomputable def ep00000001111_7 : Blocks := edgeBlocks% "full/vectors/00000001111-E-0007.bin"
private noncomputable def ep00000001111_8 : Blocks := edgeBlocks% "full/vectors/00000001111-E-0008.bin"
noncomputable def ep00000001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00000001111_0 ep00000001111_1) (Blocks.join ep00000001111_2 ep00000001111_3)) (Blocks.join (Blocks.join ep00000001111_4 ep00000001111_5) (Blocks.join ep00000001111_6 (Blocks.join ep00000001111_7 ep00000001111_8))))
private theorem idp00000001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000111.list =
    C ((2:ℤ)^1093) * horner X vp00000001111.list + horner X ep00000001111.list := by
  exact edge_identity (B := (2:ℤ)^1717) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000001111 : Branch 1 (-55761639/8000000 : ℚ) vp0000000111 := by
  apply branch_checked idp00000001111 (by positivity) (by decide +kernel)
  rw [show 2*(-55761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-59761639/4000000 : ℚ) by norm_num]
  exact coverp00000001111
theorem coverp0000000111 : Covers (-55761639/8000000 : ℚ) vp0000000111 := join_branches bp00000001110 bp00000001111
end NextProof.EdgeFull

