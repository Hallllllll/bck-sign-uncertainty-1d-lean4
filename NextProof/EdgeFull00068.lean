import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00067

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00010010111111_0 : Blocks := edgeBlocks% "full/vectors/00010010111111-V-0000.bin"
noncomputable def vp00010010111111 : Blocks := vp00010010111111_0
theorem coverp00010010111111 : Covers (-607261639/500000 : ℚ) vp00010010111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010111110_0 : Blocks := edgeBlocks% "full/vectors/00010010111110-V-0000.bin"
noncomputable def vp00010010111110 : Blocks := vp00010010111110_0
theorem coverp00010010111110 : Covers (-606761639/500000 : ℚ) vp00010010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001011111_0 : Blocks := edgeBlocks% "full/vectors/0001001011111-V-0000.bin"
noncomputable def vp0001001011111 : Blocks := vp0001001011111_0
private theorem bp00010010111110 : Branch 0 (-606761639/1000000 : ℚ) vp0001001011111 := by
  apply branch_left_normalized (c:=vp00010010111110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-606761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-606761639/500000 : ℚ) by norm_num]
  exact coverp00010010111110
private noncomputable def ep00010010111111_0 : Blocks := edgeBlocks% "full/vectors/00010010111111-E-0000.bin"
noncomputable def ep00010010111111 : Blocks := ep00010010111111_0
private theorem idp00010010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001011111.list =
    C ((2:ℤ)^64) * horner X vp00010010111111.list + horner X ep00010010111111.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010111111 : Branch 1 (-606761639/1000000 : ℚ) vp0001001011111 := by
  apply branch_checked idp00010010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-606761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-607261639/500000 : ℚ) by norm_num]
  exact coverp00010010111111
theorem coverp0001001011111 : Covers (-606761639/1000000 : ℚ) vp0001001011111 := join_branches bp00010010111110 bp00010010111111
private noncomputable def vp00010010111101_0 : Blocks := edgeBlocks% "full/vectors/00010010111101-V-0000.bin"
noncomputable def vp00010010111101 : Blocks := vp00010010111101_0
theorem coverp00010010111101 : Covers (-606261639/500000 : ℚ) vp00010010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010111100_0 : Blocks := edgeBlocks% "full/vectors/00010010111100-V-0000.bin"
noncomputable def vp00010010111100 : Blocks := vp00010010111100_0
theorem coverp00010010111100 : Covers (-605761639/500000 : ℚ) vp00010010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001011110_0 : Blocks := edgeBlocks% "full/vectors/0001001011110-V-0000.bin"
noncomputable def vp0001001011110 : Blocks := vp0001001011110_0
private theorem bp00010010111100 : Branch 0 (-605761639/1000000 : ℚ) vp0001001011110 := by
  apply branch_left_normalized (c:=vp00010010111100) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-605761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-605761639/500000 : ℚ) by norm_num]
  exact coverp00010010111100
private noncomputable def ep00010010111101_0 : Blocks := edgeBlocks% "full/vectors/00010010111101-E-0000.bin"
noncomputable def ep00010010111101 : Blocks := ep00010010111101_0
private theorem idp00010010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001011110.list =
    C ((2:ℤ)^62) * horner X vp00010010111101.list + horner X ep00010010111101.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010111101 : Branch 1 (-605761639/1000000 : ℚ) vp0001001011110 := by
  apply branch_checked idp00010010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-605761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-606261639/500000 : ℚ) by norm_num]
  exact coverp00010010111101
theorem coverp0001001011110 : Covers (-605761639/1000000 : ℚ) vp0001001011110 := join_branches bp00010010111100 bp00010010111101
private noncomputable def vp000100101111_0 : Blocks := edgeBlocks% "full/vectors/000100101111-V-0000.bin"
noncomputable def vp000100101111 : Blocks := vp000100101111_0
private theorem bp0001001011110 : Branch 0 (-605761639/2000000 : ℚ) vp000100101111 := by
  apply branch_left_normalized (c:=vp0001001011110) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-605761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-605761639/1000000 : ℚ) by norm_num]
  exact coverp0001001011110
private noncomputable def ep0001001011111_0 : Blocks := edgeBlocks% "full/vectors/0001001011111-E-0000.bin"
noncomputable def ep0001001011111 : Blocks := ep0001001011111_0
private theorem idp0001001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100101111.list =
    C ((2:ℤ)^106) * horner X vp0001001011111.list + horner X ep0001001011111.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001011111 : Branch 1 (-605761639/2000000 : ℚ) vp000100101111 := by
  apply branch_checked idp0001001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-605761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-606761639/1000000 : ℚ) by norm_num]
  exact coverp0001001011111
theorem coverp000100101111 : Covers (-605761639/2000000 : ℚ) vp000100101111 := join_branches bp0001001011110 bp0001001011111
private noncomputable def vp00010010111011_0 : Blocks := edgeBlocks% "full/vectors/00010010111011-V-0000.bin"
noncomputable def vp00010010111011 : Blocks := vp00010010111011_0
theorem coverp00010010111011 : Covers (-605261639/500000 : ℚ) vp00010010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010111010_0 : Blocks := edgeBlocks% "full/vectors/00010010111010-V-0000.bin"
noncomputable def vp00010010111010 : Blocks := vp00010010111010_0
theorem coverp00010010111010 : Covers (-604761639/500000 : ℚ) vp00010010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001011101_0 : Blocks := edgeBlocks% "full/vectors/0001001011101-V-0000.bin"
noncomputable def vp0001001011101 : Blocks := vp0001001011101_0
private theorem bp00010010111010 : Branch 0 (-604761639/1000000 : ℚ) vp0001001011101 := by
  apply branch_left_normalized (c:=vp00010010111010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-604761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-604761639/500000 : ℚ) by norm_num]
  exact coverp00010010111010
private noncomputable def ep00010010111011_0 : Blocks := edgeBlocks% "full/vectors/00010010111011-E-0000.bin"
noncomputable def ep00010010111011 : Blocks := ep00010010111011_0
private theorem idp00010010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001011101.list =
    C ((2:ℤ)^62) * horner X vp00010010111011.list + horner X ep00010010111011.list := by
  exact edge_identity (B := (2:ℤ)^181) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010111011 : Branch 1 (-604761639/1000000 : ℚ) vp0001001011101 := by
  apply branch_checked idp00010010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-604761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-605261639/500000 : ℚ) by norm_num]
  exact coverp00010010111011
theorem coverp0001001011101 : Covers (-604761639/1000000 : ℚ) vp0001001011101 := join_branches bp00010010111010 bp00010010111011
private noncomputable def vp00010010111001_0 : Blocks := edgeBlocks% "full/vectors/00010010111001-V-0000.bin"
noncomputable def vp00010010111001 : Blocks := vp00010010111001_0
theorem coverp00010010111001 : Covers (-604261639/500000 : ℚ) vp00010010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010111000_0 : Blocks := edgeBlocks% "full/vectors/00010010111000-V-0000.bin"
noncomputable def vp00010010111000 : Blocks := vp00010010111000_0
theorem coverp00010010111000 : Covers (-603761639/500000 : ℚ) vp00010010111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001011100_0 : Blocks := edgeBlocks% "full/vectors/0001001011100-V-0000.bin"
noncomputable def vp0001001011100 : Blocks := vp0001001011100_0
private theorem bp00010010111000 : Branch 0 (-603761639/1000000 : ℚ) vp0001001011100 := by
  apply branch_left_normalized (c:=vp00010010111000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-603761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-603761639/500000 : ℚ) by norm_num]
  exact coverp00010010111000
private noncomputable def ep00010010111001_0 : Blocks := edgeBlocks% "full/vectors/00010010111001-E-0000.bin"
noncomputable def ep00010010111001 : Blocks := ep00010010111001_0
private theorem idp00010010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001011100.list =
    C ((2:ℤ)^63) * horner X vp00010010111001.list + horner X ep00010010111001.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010111001 : Branch 1 (-603761639/1000000 : ℚ) vp0001001011100 := by
  apply branch_checked idp00010010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-603761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-604261639/500000 : ℚ) by norm_num]
  exact coverp00010010111001
theorem coverp0001001011100 : Covers (-603761639/1000000 : ℚ) vp0001001011100 := join_branches bp00010010111000 bp00010010111001
private noncomputable def vp000100101110_0 : Blocks := edgeBlocks% "full/vectors/000100101110-V-0000.bin"
noncomputable def vp000100101110 : Blocks := vp000100101110_0
private theorem bp0001001011100 : Branch 0 (-603761639/2000000 : ℚ) vp000100101110 := by
  apply branch_left_normalized (c:=vp0001001011100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-603761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-603761639/1000000 : ℚ) by norm_num]
  exact coverp0001001011100
private noncomputable def ep0001001011101_0 : Blocks := edgeBlocks% "full/vectors/0001001011101-E-0000.bin"
noncomputable def ep0001001011101 : Blocks := ep0001001011101_0
private theorem idp0001001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100101110.list =
    C ((2:ℤ)^107) * horner X vp0001001011101.list + horner X ep0001001011101.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001011101 : Branch 1 (-603761639/2000000 : ℚ) vp000100101110 := by
  apply branch_checked idp0001001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-603761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-604761639/1000000 : ℚ) by norm_num]
  exact coverp0001001011101
theorem coverp000100101110 : Covers (-603761639/2000000 : ℚ) vp000100101110 := join_branches bp0001001011100 bp0001001011101
private noncomputable def vp00010010111_0 : Blocks := edgeBlocks% "full/vectors/00010010111-V-0000.bin"
private noncomputable def vp00010010111_1 : Blocks := edgeBlocks% "full/vectors/00010010111-V-0001.bin"
noncomputable def vp00010010111 : Blocks := (Blocks.join vp00010010111_0 vp00010010111_1)
private theorem bp000100101110 : Branch 0 (-603761639/4000000 : ℚ) vp00010010111 := by
  apply branch_left_normalized (c:=vp000100101110) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-603761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-603761639/2000000 : ℚ) by norm_num]
  exact coverp000100101110
private noncomputable def ep000100101111_0 : Blocks := edgeBlocks% "full/vectors/000100101111-E-0000.bin"
private noncomputable def ep000100101111_1 : Blocks := edgeBlocks% "full/vectors/000100101111-E-0001.bin"
noncomputable def ep000100101111 : Blocks := (Blocks.join ep000100101111_0 ep000100101111_1)
private theorem idp000100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010010111.list =
    C ((2:ℤ)^193) * horner X vp000100101111.list + horner X ep000100101111.list := by
  exact edge_identity (B := (2:ℤ)^367) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100101111 : Branch 1 (-603761639/4000000 : ℚ) vp00010010111 := by
  apply branch_checked idp000100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-603761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-605761639/2000000 : ℚ) by norm_num]
  exact coverp000100101111
theorem coverp00010010111 : Covers (-603761639/4000000 : ℚ) vp00010010111 := join_branches bp000100101110 bp000100101111
private noncomputable def vp00010010110111_0 : Blocks := edgeBlocks% "full/vectors/00010010110111-V-0000.bin"
noncomputable def vp00010010110111 : Blocks := vp00010010110111_0
theorem coverp00010010110111 : Covers (-603261639/500000 : ℚ) vp00010010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010110110_0 : Blocks := edgeBlocks% "full/vectors/00010010110110-V-0000.bin"
noncomputable def vp00010010110110 : Blocks := vp00010010110110_0
theorem coverp00010010110110 : Covers (-602761639/500000 : ℚ) vp00010010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001011011_0 : Blocks := edgeBlocks% "full/vectors/0001001011011-V-0000.bin"
noncomputable def vp0001001011011 : Blocks := vp0001001011011_0
private theorem bp00010010110110 : Branch 0 (-602761639/1000000 : ℚ) vp0001001011011 := by
  apply branch_left_normalized (c:=vp00010010110110) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-602761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-602761639/500000 : ℚ) by norm_num]
  exact coverp00010010110110
private noncomputable def ep00010010110111_0 : Blocks := edgeBlocks% "full/vectors/00010010110111-E-0000.bin"
noncomputable def ep00010010110111 : Blocks := ep00010010110111_0
private theorem idp00010010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001011011.list =
    C ((2:ℤ)^64) * horner X vp00010010110111.list + horner X ep00010010110111.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010110111 : Branch 1 (-602761639/1000000 : ℚ) vp0001001011011 := by
  apply branch_checked idp00010010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-602761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-603261639/500000 : ℚ) by norm_num]
  exact coverp00010010110111
theorem coverp0001001011011 : Covers (-602761639/1000000 : ℚ) vp0001001011011 := join_branches bp00010010110110 bp00010010110111
private noncomputable def vp00010010110101_0 : Blocks := edgeBlocks% "full/vectors/00010010110101-V-0000.bin"
noncomputable def vp00010010110101 : Blocks := vp00010010110101_0
theorem coverp00010010110101 : Covers (-602261639/500000 : ℚ) vp00010010110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010110100_0 : Blocks := edgeBlocks% "full/vectors/00010010110100-V-0000.bin"
noncomputable def vp00010010110100 : Blocks := vp00010010110100_0
theorem coverp00010010110100 : Covers (-601761639/500000 : ℚ) vp00010010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001011010_0 : Blocks := edgeBlocks% "full/vectors/0001001011010-V-0000.bin"
noncomputable def vp0001001011010 : Blocks := vp0001001011010_0
private theorem bp00010010110100 : Branch 0 (-601761639/1000000 : ℚ) vp0001001011010 := by
  apply branch_left_normalized (c:=vp00010010110100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-601761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-601761639/500000 : ℚ) by norm_num]
  exact coverp00010010110100
private noncomputable def ep00010010110101_0 : Blocks := edgeBlocks% "full/vectors/00010010110101-E-0000.bin"
noncomputable def ep00010010110101 : Blocks := ep00010010110101_0
private theorem idp00010010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001011010.list =
    C ((2:ℤ)^64) * horner X vp00010010110101.list + horner X ep00010010110101.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010110101 : Branch 1 (-601761639/1000000 : ℚ) vp0001001011010 := by
  apply branch_checked idp00010010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-601761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-602261639/500000 : ℚ) by norm_num]
  exact coverp00010010110101
theorem coverp0001001011010 : Covers (-601761639/1000000 : ℚ) vp0001001011010 := join_branches bp00010010110100 bp00010010110101
private noncomputable def vp000100101101_0 : Blocks := edgeBlocks% "full/vectors/000100101101-V-0000.bin"
noncomputable def vp000100101101 : Blocks := vp000100101101_0
private theorem bp0001001011010 : Branch 0 (-601761639/2000000 : ℚ) vp000100101101 := by
  apply branch_left_normalized (c:=vp0001001011010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-601761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-601761639/1000000 : ℚ) by norm_num]
  exact coverp0001001011010
private noncomputable def ep0001001011011_0 : Blocks := edgeBlocks% "full/vectors/0001001011011-E-0000.bin"
noncomputable def ep0001001011011 : Blocks := ep0001001011011_0
private theorem idp0001001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100101101.list =
    C ((2:ℤ)^110) * horner X vp0001001011011.list + horner X ep0001001011011.list := by
  exact edge_identity (B := (2:ℤ)^247) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001011011 : Branch 1 (-601761639/2000000 : ℚ) vp000100101101 := by
  apply branch_checked idp0001001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-601761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-602761639/1000000 : ℚ) by norm_num]
  exact coverp0001001011011
theorem coverp000100101101 : Covers (-601761639/2000000 : ℚ) vp000100101101 := join_branches bp0001001011010 bp0001001011011
private noncomputable def vp00010010110011_0 : Blocks := edgeBlocks% "full/vectors/00010010110011-V-0000.bin"
noncomputable def vp00010010110011 : Blocks := vp00010010110011_0
theorem coverp00010010110011 : Covers (-601261639/500000 : ℚ) vp00010010110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010110010_0 : Blocks := edgeBlocks% "full/vectors/00010010110010-V-0000.bin"
noncomputable def vp00010010110010 : Blocks := vp00010010110010_0
theorem coverp00010010110010 : Covers (-600761639/500000 : ℚ) vp00010010110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001011001_0 : Blocks := edgeBlocks% "full/vectors/0001001011001-V-0000.bin"
noncomputable def vp0001001011001 : Blocks := vp0001001011001_0
private theorem bp00010010110010 : Branch 0 (-600761639/1000000 : ℚ) vp0001001011001 := by
  apply branch_left_normalized (c:=vp00010010110010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-600761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-600761639/500000 : ℚ) by norm_num]
  exact coverp00010010110010
private noncomputable def ep00010010110011_0 : Blocks := edgeBlocks% "full/vectors/00010010110011-E-0000.bin"
noncomputable def ep00010010110011 : Blocks := ep00010010110011_0
private theorem idp00010010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001011001.list =
    C ((2:ℤ)^64) * horner X vp00010010110011.list + horner X ep00010010110011.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010110011 : Branch 1 (-600761639/1000000 : ℚ) vp0001001011001 := by
  apply branch_checked idp00010010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-600761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-601261639/500000 : ℚ) by norm_num]
  exact coverp00010010110011
theorem coverp0001001011001 : Covers (-600761639/1000000 : ℚ) vp0001001011001 := join_branches bp00010010110010 bp00010010110011
private noncomputable def vp00010010110001_0 : Blocks := edgeBlocks% "full/vectors/00010010110001-V-0000.bin"
noncomputable def vp00010010110001 : Blocks := vp00010010110001_0
theorem coverp00010010110001 : Covers (-600261639/500000 : ℚ) vp00010010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010110000_0 : Blocks := edgeBlocks% "full/vectors/00010010110000-V-0000.bin"
noncomputable def vp00010010110000 : Blocks := vp00010010110000_0
theorem coverp00010010110000 : Covers (-599761639/500000 : ℚ) vp00010010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001011000_0 : Blocks := edgeBlocks% "full/vectors/0001001011000-V-0000.bin"
noncomputable def vp0001001011000 : Blocks := vp0001001011000_0
private theorem bp00010010110000 : Branch 0 (-599761639/1000000 : ℚ) vp0001001011000 := by
  apply branch_left_normalized (c:=vp00010010110000) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-599761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-599761639/500000 : ℚ) by norm_num]
  exact coverp00010010110000
private noncomputable def ep00010010110001_0 : Blocks := edgeBlocks% "full/vectors/00010010110001-E-0000.bin"
noncomputable def ep00010010110001 : Blocks := ep00010010110001_0
private theorem idp00010010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001011000.list =
    C ((2:ℤ)^62) * horner X vp00010010110001.list + horner X ep00010010110001.list := by
  exact edge_identity (B := (2:ℤ)^182) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010110001 : Branch 1 (-599761639/1000000 : ℚ) vp0001001011000 := by
  apply branch_checked idp00010010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-599761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-600261639/500000 : ℚ) by norm_num]
  exact coverp00010010110001
theorem coverp0001001011000 : Covers (-599761639/1000000 : ℚ) vp0001001011000 := join_branches bp00010010110000 bp00010010110001
private noncomputable def vp000100101100_0 : Blocks := edgeBlocks% "full/vectors/000100101100-V-0000.bin"
noncomputable def vp000100101100 : Blocks := vp000100101100_0
private theorem bp0001001011000 : Branch 0 (-599761639/2000000 : ℚ) vp000100101100 := by
  apply branch_left_normalized (c:=vp0001001011000) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-599761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-599761639/1000000 : ℚ) by norm_num]
  exact coverp0001001011000
private noncomputable def ep0001001011001_0 : Blocks := edgeBlocks% "full/vectors/0001001011001-E-0000.bin"
noncomputable def ep0001001011001 : Blocks := ep0001001011001_0
private theorem idp0001001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100101100.list =
    C ((2:ℤ)^105) * horner X vp0001001011001.list + horner X ep0001001011001.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001011001 : Branch 1 (-599761639/2000000 : ℚ) vp000100101100 := by
  apply branch_checked idp0001001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-599761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-600761639/1000000 : ℚ) by norm_num]
  exact coverp0001001011001
theorem coverp000100101100 : Covers (-599761639/2000000 : ℚ) vp000100101100 := join_branches bp0001001011000 bp0001001011001
private noncomputable def vp00010010110_0 : Blocks := edgeBlocks% "full/vectors/00010010110-V-0000.bin"
private noncomputable def vp00010010110_1 : Blocks := edgeBlocks% "full/vectors/00010010110-V-0001.bin"
noncomputable def vp00010010110 : Blocks := (Blocks.join vp00010010110_0 vp00010010110_1)
private theorem bp000100101100 : Branch 0 (-599761639/4000000 : ℚ) vp00010010110 := by
  apply branch_left_normalized (c:=vp000100101100) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-599761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-599761639/2000000 : ℚ) by norm_num]
  exact coverp000100101100
private noncomputable def ep000100101101_0 : Blocks := edgeBlocks% "full/vectors/000100101101-E-0000.bin"
private noncomputable def ep000100101101_1 : Blocks := edgeBlocks% "full/vectors/000100101101-E-0001.bin"
noncomputable def ep000100101101 : Blocks := (Blocks.join ep000100101101_0 ep000100101101_1)
private theorem idp000100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010010110.list =
    C ((2:ℤ)^193) * horner X vp000100101101.list + horner X ep000100101101.list := by
  exact edge_identity (B := (2:ℤ)^368) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100101101 : Branch 1 (-599761639/4000000 : ℚ) vp00010010110 := by
  apply branch_checked idp000100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-599761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-601761639/2000000 : ℚ) by norm_num]
  exact coverp000100101101
theorem coverp00010010110 : Covers (-599761639/4000000 : ℚ) vp00010010110 := join_branches bp000100101100 bp000100101101
private noncomputable def vp0001001011_0 : Blocks := edgeBlocks% "full/vectors/0001001011-V-0000.bin"
private noncomputable def vp0001001011_1 : Blocks := edgeBlocks% "full/vectors/0001001011-V-0001.bin"
private noncomputable def vp0001001011_2 : Blocks := edgeBlocks% "full/vectors/0001001011-V-0002.bin"
noncomputable def vp0001001011 : Blocks := (Blocks.join vp0001001011_0 (Blocks.join vp0001001011_1 vp0001001011_2))
private theorem bp00010010110 : Branch 0 (-599761639/8000000 : ℚ) vp0001001011 := by
  apply branch_left_normalized (c:=vp00010010110) (k:=0) (m:=182) (by decide +kernel)
  rw [show 2*(-599761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-599761639/4000000 : ℚ) by norm_num]
  exact coverp00010010110
private noncomputable def ep00010010111_0 : Blocks := edgeBlocks% "full/vectors/00010010111-E-0000.bin"
private noncomputable def ep00010010111_1 : Blocks := edgeBlocks% "full/vectors/00010010111-E-0001.bin"
private noncomputable def ep00010010111_2 : Blocks := edgeBlocks% "full/vectors/00010010111-E-0002.bin"
noncomputable def ep00010010111 : Blocks := (Blocks.join ep00010010111_0 (Blocks.join ep00010010111_1 ep00010010111_2))
private theorem idp00010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001011.list =
    C ((2:ℤ)^365) * horner X vp00010010111.list + horner X ep00010010111.list := by
  exact edge_identity (B := (2:ℤ)^612) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010111 : Branch 1 (-599761639/8000000 : ℚ) vp0001001011 := by
  apply branch_checked idp00010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-599761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-603761639/4000000 : ℚ) by norm_num]
  exact coverp00010010111
theorem coverp0001001011 : Covers (-599761639/8000000 : ℚ) vp0001001011 := join_branches bp00010010110 bp00010010111
private noncomputable def vp00010010101111_0 : Blocks := edgeBlocks% "full/vectors/00010010101111-V-0000.bin"
noncomputable def vp00010010101111 : Blocks := vp00010010101111_0
theorem coverp00010010101111 : Covers (-599261639/500000 : ℚ) vp00010010101111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010101110_0 : Blocks := edgeBlocks% "full/vectors/00010010101110-V-0000.bin"
noncomputable def vp00010010101110 : Blocks := vp00010010101110_0
theorem coverp00010010101110 : Covers (-598761639/500000 : ℚ) vp00010010101110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001010111_0 : Blocks := edgeBlocks% "full/vectors/0001001010111-V-0000.bin"
noncomputable def vp0001001010111 : Blocks := vp0001001010111_0
private theorem bp00010010101110 : Branch 0 (-598761639/1000000 : ℚ) vp0001001010111 := by
  apply branch_left_normalized (c:=vp00010010101110) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-598761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-598761639/500000 : ℚ) by norm_num]
  exact coverp00010010101110
private noncomputable def ep00010010101111_0 : Blocks := edgeBlocks% "full/vectors/00010010101111-E-0000.bin"
noncomputable def ep00010010101111 : Blocks := ep00010010101111_0
private theorem idp00010010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001010111.list =
    C ((2:ℤ)^61) * horner X vp00010010101111.list + horner X ep00010010101111.list := by
  exact edge_identity (B := (2:ℤ)^179) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010101111 : Branch 1 (-598761639/1000000 : ℚ) vp0001001010111 := by
  apply branch_checked idp00010010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-598761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-599261639/500000 : ℚ) by norm_num]
  exact coverp00010010101111
theorem coverp0001001010111 : Covers (-598761639/1000000 : ℚ) vp0001001010111 := join_branches bp00010010101110 bp00010010101111
private noncomputable def vp00010010101101_0 : Blocks := edgeBlocks% "full/vectors/00010010101101-V-0000.bin"
noncomputable def vp00010010101101 : Blocks := vp00010010101101_0
theorem coverp00010010101101 : Covers (-598261639/500000 : ℚ) vp00010010101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010101100_0 : Blocks := edgeBlocks% "full/vectors/00010010101100-V-0000.bin"
noncomputable def vp00010010101100 : Blocks := vp00010010101100_0
theorem coverp00010010101100 : Covers (-597761639/500000 : ℚ) vp00010010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001010110_0 : Blocks := edgeBlocks% "full/vectors/0001001010110-V-0000.bin"
noncomputable def vp0001001010110 : Blocks := vp0001001010110_0
private theorem bp00010010101100 : Branch 0 (-597761639/1000000 : ℚ) vp0001001010110 := by
  apply branch_left_normalized (c:=vp00010010101100) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-597761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-597761639/500000 : ℚ) by norm_num]
  exact coverp00010010101100
private noncomputable def ep00010010101101_0 : Blocks := edgeBlocks% "full/vectors/00010010101101-E-0000.bin"
noncomputable def ep00010010101101 : Blocks := ep00010010101101_0
private theorem idp00010010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001010110.list =
    C ((2:ℤ)^62) * horner X vp00010010101101.list + horner X ep00010010101101.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010101101 : Branch 1 (-597761639/1000000 : ℚ) vp0001001010110 := by
  apply branch_checked idp00010010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-597761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-598261639/500000 : ℚ) by norm_num]
  exact coverp00010010101101
theorem coverp0001001010110 : Covers (-597761639/1000000 : ℚ) vp0001001010110 := join_branches bp00010010101100 bp00010010101101
private noncomputable def vp000100101011_0 : Blocks := edgeBlocks% "full/vectors/000100101011-V-0000.bin"
noncomputable def vp000100101011 : Blocks := vp000100101011_0
private theorem bp0001001010110 : Branch 0 (-597761639/2000000 : ℚ) vp000100101011 := by
  apply branch_left_normalized (c:=vp0001001010110) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-597761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-597761639/1000000 : ℚ) by norm_num]
  exact coverp0001001010110
private noncomputable def ep0001001010111_0 : Blocks := edgeBlocks% "full/vectors/0001001010111-E-0000.bin"
noncomputable def ep0001001010111 : Blocks := ep0001001010111_0
private theorem idp0001001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100101011.list =
    C ((2:ℤ)^106) * horner X vp0001001010111.list + horner X ep0001001010111.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001010111 : Branch 1 (-597761639/2000000 : ℚ) vp000100101011 := by
  apply branch_checked idp0001001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-597761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-598761639/1000000 : ℚ) by norm_num]
  exact coverp0001001010111
theorem coverp000100101011 : Covers (-597761639/2000000 : ℚ) vp000100101011 := join_branches bp0001001010110 bp0001001010111
private noncomputable def vp00010010101011_0 : Blocks := edgeBlocks% "full/vectors/00010010101011-V-0000.bin"
noncomputable def vp00010010101011 : Blocks := vp00010010101011_0
theorem coverp00010010101011 : Covers (-597261639/500000 : ℚ) vp00010010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010101010_0 : Blocks := edgeBlocks% "full/vectors/00010010101010-V-0000.bin"
noncomputable def vp00010010101010 : Blocks := vp00010010101010_0
theorem coverp00010010101010 : Covers (-596761639/500000 : ℚ) vp00010010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001010101_0 : Blocks := edgeBlocks% "full/vectors/0001001010101-V-0000.bin"
noncomputable def vp0001001010101 : Blocks := vp0001001010101_0
private theorem bp00010010101010 : Branch 0 (-596761639/1000000 : ℚ) vp0001001010101 := by
  apply branch_left_normalized (c:=vp00010010101010) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-596761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-596761639/500000 : ℚ) by norm_num]
  exact coverp00010010101010
private noncomputable def ep00010010101011_0 : Blocks := edgeBlocks% "full/vectors/00010010101011-E-0000.bin"
noncomputable def ep00010010101011 : Blocks := ep00010010101011_0
private theorem idp00010010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001010101.list =
    C ((2:ℤ)^61) * horner X vp00010010101011.list + horner X ep00010010101011.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010101011 : Branch 1 (-596761639/1000000 : ℚ) vp0001001010101 := by
  apply branch_checked idp00010010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-596761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-597261639/500000 : ℚ) by norm_num]
  exact coverp00010010101011
theorem coverp0001001010101 : Covers (-596761639/1000000 : ℚ) vp0001001010101 := join_branches bp00010010101010 bp00010010101011
private noncomputable def vp00010010101001_0 : Blocks := edgeBlocks% "full/vectors/00010010101001-V-0000.bin"
noncomputable def vp00010010101001 : Blocks := vp00010010101001_0
theorem coverp00010010101001 : Covers (-596261639/500000 : ℚ) vp00010010101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010101000_0 : Blocks := edgeBlocks% "full/vectors/00010010101000-V-0000.bin"
noncomputable def vp00010010101000 : Blocks := vp00010010101000_0
theorem coverp00010010101000 : Covers (-595761639/500000 : ℚ) vp00010010101000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001010100_0 : Blocks := edgeBlocks% "full/vectors/0001001010100-V-0000.bin"
noncomputable def vp0001001010100 : Blocks := vp0001001010100_0
private theorem bp00010010101000 : Branch 0 (-595761639/1000000 : ℚ) vp0001001010100 := by
  apply branch_left_normalized (c:=vp00010010101000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-595761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-595761639/500000 : ℚ) by norm_num]
  exact coverp00010010101000
private noncomputable def ep00010010101001_0 : Blocks := edgeBlocks% "full/vectors/00010010101001-E-0000.bin"
noncomputable def ep00010010101001 : Blocks := ep00010010101001_0
private theorem idp00010010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001010100.list =
    C ((2:ℤ)^61) * horner X vp00010010101001.list + horner X ep00010010101001.list := by
  exact edge_identity (B := (2:ℤ)^177) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010101001 : Branch 1 (-595761639/1000000 : ℚ) vp0001001010100 := by
  apply branch_checked idp00010010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-595761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-596261639/500000 : ℚ) by norm_num]
  exact coverp00010010101001
theorem coverp0001001010100 : Covers (-595761639/1000000 : ℚ) vp0001001010100 := join_branches bp00010010101000 bp00010010101001
private noncomputable def vp000100101010_0 : Blocks := edgeBlocks% "full/vectors/000100101010-V-0000.bin"
noncomputable def vp000100101010 : Blocks := vp000100101010_0
private theorem bp0001001010100 : Branch 0 (-595761639/2000000 : ℚ) vp000100101010 := by
  apply branch_left_normalized (c:=vp0001001010100) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-595761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-595761639/1000000 : ℚ) by norm_num]
  exact coverp0001001010100
private noncomputable def ep0001001010101_0 : Blocks := edgeBlocks% "full/vectors/0001001010101-E-0000.bin"
noncomputable def ep0001001010101 : Blocks := ep0001001010101_0
private theorem idp0001001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100101010.list =
    C ((2:ℤ)^107) * horner X vp0001001010101.list + horner X ep0001001010101.list := by
  exact edge_identity (B := (2:ℤ)^241) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001010101 : Branch 1 (-595761639/2000000 : ℚ) vp000100101010 := by
  apply branch_checked idp0001001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-595761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-596761639/1000000 : ℚ) by norm_num]
  exact coverp0001001010101
theorem coverp000100101010 : Covers (-595761639/2000000 : ℚ) vp000100101010 := join_branches bp0001001010100 bp0001001010101
private noncomputable def vp00010010101_0 : Blocks := edgeBlocks% "full/vectors/00010010101-V-0000.bin"
private noncomputable def vp00010010101_1 : Blocks := edgeBlocks% "full/vectors/00010010101-V-0001.bin"
noncomputable def vp00010010101 : Blocks := (Blocks.join vp00010010101_0 vp00010010101_1)
private theorem bp000100101010 : Branch 0 (-595761639/4000000 : ℚ) vp00010010101 := by
  apply branch_left_normalized (c:=vp000100101010) (k:=0) (m:=100) (by decide +kernel)
  rw [show 2*(-595761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-595761639/2000000 : ℚ) by norm_num]
  exact coverp000100101010
private noncomputable def ep000100101011_0 : Blocks := edgeBlocks% "full/vectors/000100101011-E-0000.bin"
private noncomputable def ep000100101011_1 : Blocks := edgeBlocks% "full/vectors/000100101011-E-0001.bin"
noncomputable def ep000100101011 : Blocks := (Blocks.join ep000100101011_0 ep000100101011_1)
private theorem idp000100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010010101.list =
    C ((2:ℤ)^192) * horner X vp000100101011.list + horner X ep000100101011.list := by
  exact edge_identity (B := (2:ℤ)^364) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100101011 : Branch 1 (-595761639/4000000 : ℚ) vp00010010101 := by
  apply branch_checked idp000100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-595761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-597761639/2000000 : ℚ) by norm_num]
  exact coverp000100101011
theorem coverp00010010101 : Covers (-595761639/4000000 : ℚ) vp00010010101 := join_branches bp000100101010 bp000100101011
private noncomputable def vp0001001010011_0 : Blocks := edgeBlocks% "full/vectors/0001001010011-V-0000.bin"
noncomputable def vp0001001010011 : Blocks := vp0001001010011_0
theorem coverp0001001010011 : Covers (-594761639/1000000 : ℚ) vp0001001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010100101_0 : Blocks := edgeBlocks% "full/vectors/00010010100101-V-0000.bin"
noncomputable def vp00010010100101 : Blocks := vp00010010100101_0
theorem coverp00010010100101 : Covers (-594261639/500000 : ℚ) vp00010010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010100100_0 : Blocks := edgeBlocks% "full/vectors/00010010100100-V-0000.bin"
noncomputable def vp00010010100100 : Blocks := vp00010010100100_0
theorem coverp00010010100100 : Covers (-593761639/500000 : ℚ) vp00010010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001010010_0 : Blocks := edgeBlocks% "full/vectors/0001001010010-V-0000.bin"
noncomputable def vp0001001010010 : Blocks := vp0001001010010_0
private theorem bp00010010100100 : Branch 0 (-593761639/1000000 : ℚ) vp0001001010010 := by
  apply branch_left_normalized (c:=vp00010010100100) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-593761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-593761639/500000 : ℚ) by norm_num]
  exact coverp00010010100100
private noncomputable def ep00010010100101_0 : Blocks := edgeBlocks% "full/vectors/00010010100101-E-0000.bin"
noncomputable def ep00010010100101 : Blocks := ep00010010100101_0
private theorem idp00010010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001010010.list =
    C ((2:ℤ)^66) * horner X vp00010010100101.list + horner X ep00010010100101.list := by
  exact edge_identity (B := (2:ℤ)^184) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010100101 : Branch 1 (-593761639/1000000 : ℚ) vp0001001010010 := by
  apply branch_checked idp00010010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-593761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-594261639/500000 : ℚ) by norm_num]
  exact coverp00010010100101
theorem coverp0001001010010 : Covers (-593761639/1000000 : ℚ) vp0001001010010 := join_branches bp00010010100100 bp00010010100101
private noncomputable def vp000100101001_0 : Blocks := edgeBlocks% "full/vectors/000100101001-V-0000.bin"
noncomputable def vp000100101001 : Blocks := vp000100101001_0
private theorem bp0001001010010 : Branch 0 (-593761639/2000000 : ℚ) vp000100101001 := by
  apply branch_left_normalized (c:=vp0001001010010) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-593761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-593761639/1000000 : ℚ) by norm_num]
  exact coverp0001001010010
private noncomputable def ep0001001010011_0 : Blocks := edgeBlocks% "full/vectors/0001001010011-E-0000.bin"
noncomputable def ep0001001010011 : Blocks := ep0001001010011_0
private theorem idp0001001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100101001.list =
    C ((2:ℤ)^112) * horner X vp0001001010011.list + horner X ep0001001010011.list := by
  exact edge_identity (B := (2:ℤ)^247) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001010011 : Branch 1 (-593761639/2000000 : ℚ) vp000100101001 := by
  apply branch_checked idp0001001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-593761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-594761639/1000000 : ℚ) by norm_num]
  exact coverp0001001010011
theorem coverp000100101001 : Covers (-593761639/2000000 : ℚ) vp000100101001 := join_branches bp0001001010010 bp0001001010011
private noncomputable def vp00010010100011_0 : Blocks := edgeBlocks% "full/vectors/00010010100011-V-0000.bin"
noncomputable def vp00010010100011 : Blocks := vp00010010100011_0
theorem coverp00010010100011 : Covers (-593261639/500000 : ℚ) vp00010010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010100010_0 : Blocks := edgeBlocks% "full/vectors/00010010100010-V-0000.bin"
noncomputable def vp00010010100010 : Blocks := vp00010010100010_0
theorem coverp00010010100010 : Covers (-592761639/500000 : ℚ) vp00010010100010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001010001_0 : Blocks := edgeBlocks% "full/vectors/0001001010001-V-0000.bin"
noncomputable def vp0001001010001 : Blocks := vp0001001010001_0
private theorem bp00010010100010 : Branch 0 (-592761639/1000000 : ℚ) vp0001001010001 := by
  apply branch_left_normalized (c:=vp00010010100010) (k:=0) (m:=37) (by decide +kernel)
  rw [show 2*(-592761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-592761639/500000 : ℚ) by norm_num]
  exact coverp00010010100010
private noncomputable def ep00010010100011_0 : Blocks := edgeBlocks% "full/vectors/00010010100011-E-0000.bin"
noncomputable def ep00010010100011 : Blocks := ep00010010100011_0
private theorem idp00010010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001010001.list =
    C ((2:ℤ)^60) * horner X vp00010010100011.list + horner X ep00010010100011.list := by
  exact edge_identity (B := (2:ℤ)^178) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010100011 : Branch 1 (-592761639/1000000 : ℚ) vp0001001010001 := by
  apply branch_checked idp00010010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-592761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-593261639/500000 : ℚ) by norm_num]
  exact coverp00010010100011
theorem coverp0001001010001 : Covers (-592761639/1000000 : ℚ) vp0001001010001 := join_branches bp00010010100010 bp00010010100011
private noncomputable def vp00010010100001_0 : Blocks := edgeBlocks% "full/vectors/00010010100001-V-0000.bin"
noncomputable def vp00010010100001 : Blocks := vp00010010100001_0
theorem coverp00010010100001 : Covers (-592261639/500000 : ℚ) vp00010010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp00010010100000_0 : Blocks := edgeBlocks% "full/vectors/00010010100000-V-0000.bin"
noncomputable def vp00010010100000 : Blocks := vp00010010100000_0
theorem coverp00010010100000 : Covers (-591761639/500000 : ℚ) vp00010010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001010000_0 : Blocks := edgeBlocks% "full/vectors/0001001010000-V-0000.bin"
noncomputable def vp0001001010000 : Blocks := vp0001001010000_0
private theorem bp00010010100000 : Branch 0 (-591761639/1000000 : ℚ) vp0001001010000 := by
  apply branch_left_normalized (c:=vp00010010100000) (k:=0) (m:=36) (by decide +kernel)
  rw [show 2*(-591761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-591761639/500000 : ℚ) by norm_num]
  exact coverp00010010100000
private noncomputable def ep00010010100001_0 : Blocks := edgeBlocks% "full/vectors/00010010100001-E-0000.bin"
noncomputable def ep00010010100001 : Blocks := ep00010010100001_0
private theorem idp00010010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001010000.list =
    C ((2:ℤ)^59) * horner X vp00010010100001.list + horner X ep00010010100001.list := by
  exact edge_identity (B := (2:ℤ)^175) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010100001 : Branch 1 (-591761639/1000000 : ℚ) vp0001001010000 := by
  apply branch_checked idp00010010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-591761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-592261639/500000 : ℚ) by norm_num]
  exact coverp00010010100001
theorem coverp0001001010000 : Covers (-591761639/1000000 : ℚ) vp0001001010000 := join_branches bp00010010100000 bp00010010100001
private noncomputable def vp000100101000_0 : Blocks := edgeBlocks% "full/vectors/000100101000-V-0000.bin"
noncomputable def vp000100101000 : Blocks := vp000100101000_0
private theorem bp0001001010000 : Branch 0 (-591761639/2000000 : ℚ) vp000100101000 := by
  apply branch_left_normalized (c:=vp0001001010000) (k:=0) (m:=57) (by decide +kernel)
  rw [show 2*(-591761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-591761639/1000000 : ℚ) by norm_num]
  exact coverp0001001010000
private noncomputable def ep0001001010001_0 : Blocks := edgeBlocks% "full/vectors/0001001010001-E-0000.bin"
noncomputable def ep0001001010001 : Blocks := ep0001001010001_0
private theorem idp0001001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100101000.list =
    C ((2:ℤ)^103) * horner X vp0001001010001.list + horner X ep0001001010001.list := by
  exact edge_identity (B := (2:ℤ)^238) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001010001 : Branch 1 (-591761639/2000000 : ℚ) vp000100101000 := by
  apply branch_checked idp0001001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-591761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-592761639/1000000 : ℚ) by norm_num]
  exact coverp0001001010001
theorem coverp000100101000 : Covers (-591761639/2000000 : ℚ) vp000100101000 := join_branches bp0001001010000 bp0001001010001
private noncomputable def vp00010010100_0 : Blocks := edgeBlocks% "full/vectors/00010010100-V-0000.bin"
private noncomputable def vp00010010100_1 : Blocks := edgeBlocks% "full/vectors/00010010100-V-0001.bin"
noncomputable def vp00010010100 : Blocks := (Blocks.join vp00010010100_0 vp00010010100_1)
private theorem bp000100101000 : Branch 0 (-591761639/4000000 : ℚ) vp00010010100 := by
  apply branch_left_normalized (c:=vp000100101000) (k:=0) (m:=99) (by decide +kernel)
  rw [show 2*(-591761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-591761639/2000000 : ℚ) by norm_num]
  exact coverp000100101000
private noncomputable def ep000100101001_0 : Blocks := edgeBlocks% "full/vectors/000100101001-E-0000.bin"
private noncomputable def ep000100101001_1 : Blocks := edgeBlocks% "full/vectors/000100101001-E-0001.bin"
noncomputable def ep000100101001 : Blocks := (Blocks.join ep000100101001_0 ep000100101001_1)
private theorem idp000100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010010100.list =
    C ((2:ℤ)^186) * horner X vp000100101001.list + horner X ep000100101001.list := by
  exact edge_identity (B := (2:ℤ)^362) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100101001 : Branch 1 (-591761639/4000000 : ℚ) vp00010010100 := by
  apply branch_checked idp000100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-591761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-593761639/2000000 : ℚ) by norm_num]
  exact coverp000100101001
theorem coverp00010010100 : Covers (-591761639/4000000 : ℚ) vp00010010100 := join_branches bp000100101000 bp000100101001
private noncomputable def vp0001001010_0 : Blocks := edgeBlocks% "full/vectors/0001001010-V-0000.bin"
private noncomputable def vp0001001010_1 : Blocks := edgeBlocks% "full/vectors/0001001010-V-0001.bin"
private noncomputable def vp0001001010_2 : Blocks := edgeBlocks% "full/vectors/0001001010-V-0002.bin"
noncomputable def vp0001001010 : Blocks := (Blocks.join vp0001001010_0 (Blocks.join vp0001001010_1 vp0001001010_2))
private theorem bp00010010100 : Branch 0 (-591761639/8000000 : ℚ) vp0001001010 := by
  apply branch_left_normalized (c:=vp00010010100) (k:=0) (m:=180) (by decide +kernel)
  rw [show 2*(-591761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-591761639/4000000 : ℚ) by norm_num]
  exact coverp00010010100
private noncomputable def ep00010010101_0 : Blocks := edgeBlocks% "full/vectors/00010010101-E-0000.bin"
private noncomputable def ep00010010101_1 : Blocks := edgeBlocks% "full/vectors/00010010101-E-0001.bin"
private noncomputable def ep00010010101_2 : Blocks := edgeBlocks% "full/vectors/00010010101-E-0002.bin"
noncomputable def ep00010010101 : Blocks := (Blocks.join ep00010010101_0 (Blocks.join ep00010010101_1 ep00010010101_2))
private theorem idp00010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001010.list =
    C ((2:ℤ)^363) * horner X vp00010010101.list + horner X ep00010010101.list := by
  exact edge_identity (B := (2:ℤ)^608) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010101 : Branch 1 (-591761639/8000000 : ℚ) vp0001001010 := by
  apply branch_checked idp00010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-591761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-595761639/4000000 : ℚ) by norm_num]
  exact coverp00010010101
theorem coverp0001001010 : Covers (-591761639/8000000 : ℚ) vp0001001010 := join_branches bp00010010100 bp00010010101
private noncomputable def vp000100101_0 : Blocks := edgeBlocks% "full/vectors/000100101-V-0000.bin"
private noncomputable def vp000100101_1 : Blocks := edgeBlocks% "full/vectors/000100101-V-0001.bin"
private noncomputable def vp000100101_2 : Blocks := edgeBlocks% "full/vectors/000100101-V-0002.bin"
private noncomputable def vp000100101_3 : Blocks := edgeBlocks% "full/vectors/000100101-V-0003.bin"
private noncomputable def vp000100101_4 : Blocks := edgeBlocks% "full/vectors/000100101-V-0004.bin"
private noncomputable def vp000100101_5 : Blocks := edgeBlocks% "full/vectors/000100101-V-0005.bin"
noncomputable def vp000100101 : Blocks := (Blocks.join (Blocks.join vp000100101_0 (Blocks.join vp000100101_1 vp000100101_2)) (Blocks.join vp000100101_3 (Blocks.join vp000100101_4 vp000100101_5)))
private theorem bp0001001010 : Branch 0 (-591761639/16000000 : ℚ) vp000100101 := by
  apply branch_left_normalized (c:=vp0001001010) (k:=0) (m:=341) (by decide +kernel)
  rw [show 2*(-591761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-591761639/8000000 : ℚ) by norm_num]
  exact coverp0001001010
private noncomputable def ep0001001011_0 : Blocks := edgeBlocks% "full/vectors/0001001011-E-0000.bin"
private noncomputable def ep0001001011_1 : Blocks := edgeBlocks% "full/vectors/0001001011-E-0001.bin"
private noncomputable def ep0001001011_2 : Blocks := edgeBlocks% "full/vectors/0001001011-E-0002.bin"
private noncomputable def ep0001001011_3 : Blocks := edgeBlocks% "full/vectors/0001001011-E-0003.bin"
private noncomputable def ep0001001011_4 : Blocks := edgeBlocks% "full/vectors/0001001011-E-0004.bin"
private noncomputable def ep0001001011_5 : Blocks := edgeBlocks% "full/vectors/0001001011-E-0005.bin"
noncomputable def ep0001001011 : Blocks := (Blocks.join (Blocks.join ep0001001011_0 (Blocks.join ep0001001011_1 ep0001001011_2)) (Blocks.join ep0001001011_3 (Blocks.join ep0001001011_4 ep0001001011_5)))
private theorem idp0001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100101.list =
    C ((2:ℤ)^701) * horner X vp0001001011.list + horner X ep0001001011.list := by
  exact edge_identity (B := (2:ℤ)^1097) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001011 : Branch 1 (-591761639/16000000 : ℚ) vp000100101 := by
  apply branch_checked idp0001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-591761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-599761639/8000000 : ℚ) by norm_num]
  exact coverp0001001011
theorem coverp000100101 : Covers (-591761639/16000000 : ℚ) vp000100101 := join_branches bp0001001010 bp0001001011
private noncomputable def vp0001001001111_0 : Blocks := edgeBlocks% "full/vectors/0001001001111-V-0000.bin"
noncomputable def vp0001001001111 : Blocks := vp0001001001111_0
theorem coverp0001001001111 : Covers (-590761639/1000000 : ℚ) vp0001001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001001110_0 : Blocks := edgeBlocks% "full/vectors/0001001001110-V-0000.bin"
noncomputable def vp0001001001110 : Blocks := vp0001001001110_0
theorem coverp0001001001110 : Covers (-589761639/1000000 : ℚ) vp0001001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000100100111_0 : Blocks := edgeBlocks% "full/vectors/000100100111-V-0000.bin"
noncomputable def vp000100100111 : Blocks := vp000100100111_0
private theorem bp0001001001110 : Branch 0 (-589761639/2000000 : ℚ) vp000100100111 := by
  apply branch_left_normalized (c:=vp0001001001110) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-589761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-589761639/1000000 : ℚ) by norm_num]
  exact coverp0001001001110
private noncomputable def ep0001001001111_0 : Blocks := edgeBlocks% "full/vectors/0001001001111-E-0000.bin"
noncomputable def ep0001001001111 : Blocks := ep0001001001111_0
private theorem idp0001001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100100111.list =
    C ((2:ℤ)^102) * horner X vp0001001001111.list + horner X ep0001001001111.list := by
  exact edge_identity (B := (2:ℤ)^234) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001001111 : Branch 1 (-589761639/2000000 : ℚ) vp000100100111 := by
  apply branch_checked idp0001001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-589761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-590761639/1000000 : ℚ) by norm_num]
  exact coverp0001001001111
theorem coverp000100100111 : Covers (-589761639/2000000 : ℚ) vp000100100111 := join_branches bp0001001001110 bp0001001001111
private noncomputable def vp0001001001101_0 : Blocks := edgeBlocks% "full/vectors/0001001001101-V-0000.bin"
noncomputable def vp0001001001101 : Blocks := vp0001001001101_0
theorem coverp0001001001101 : Covers (-588761639/1000000 : ℚ) vp0001001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001001100_0 : Blocks := edgeBlocks% "full/vectors/0001001001100-V-0000.bin"
noncomputable def vp0001001001100 : Blocks := vp0001001001100_0
theorem coverp0001001001100 : Covers (-587761639/1000000 : ℚ) vp0001001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000100100110_0 : Blocks := edgeBlocks% "full/vectors/000100100110-V-0000.bin"
noncomputable def vp000100100110 : Blocks := vp000100100110_0
private theorem bp0001001001100 : Branch 0 (-587761639/2000000 : ℚ) vp000100100110 := by
  apply branch_left_normalized (c:=vp0001001001100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-587761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-587761639/1000000 : ℚ) by norm_num]
  exact coverp0001001001100
private noncomputable def ep0001001001101_0 : Blocks := edgeBlocks% "full/vectors/0001001001101-E-0000.bin"
noncomputable def ep0001001001101 : Blocks := ep0001001001101_0
private theorem idp0001001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100100110.list =
    C ((2:ℤ)^103) * horner X vp0001001001101.list + horner X ep0001001001101.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001001101 : Branch 1 (-587761639/2000000 : ℚ) vp000100100110 := by
  apply branch_checked idp0001001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-587761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-588761639/1000000 : ℚ) by norm_num]
  exact coverp0001001001101
theorem coverp000100100110 : Covers (-587761639/2000000 : ℚ) vp000100100110 := join_branches bp0001001001100 bp0001001001101
private noncomputable def vp00010010011_0 : Blocks := edgeBlocks% "full/vectors/00010010011-V-0000.bin"
private noncomputable def vp00010010011_1 : Blocks := edgeBlocks% "full/vectors/00010010011-V-0001.bin"
noncomputable def vp00010010011 : Blocks := (Blocks.join vp00010010011_0 vp00010010011_1)
private theorem bp000100100110 : Branch 0 (-587761639/4000000 : ℚ) vp00010010011 := by
  apply branch_left_normalized (c:=vp000100100110) (k:=0) (m:=97) (by decide +kernel)
  rw [show 2*(-587761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-587761639/2000000 : ℚ) by norm_num]
  exact coverp000100100110
private noncomputable def ep000100100111_0 : Blocks := edgeBlocks% "full/vectors/000100100111-E-0000.bin"
private noncomputable def ep000100100111_1 : Blocks := edgeBlocks% "full/vectors/000100100111-E-0001.bin"
noncomputable def ep000100100111 : Blocks := (Blocks.join ep000100100111_0 ep000100100111_1)
private theorem idp000100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010010011.list =
    C ((2:ℤ)^189) * horner X vp000100100111.list + horner X ep000100100111.list := by
  exact edge_identity (B := (2:ℤ)^356) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100100111 : Branch 1 (-587761639/4000000 : ℚ) vp00010010011 := by
  apply branch_checked idp000100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-587761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-589761639/2000000 : ℚ) by norm_num]
  exact coverp000100100111
theorem coverp00010010011 : Covers (-587761639/4000000 : ℚ) vp00010010011 := join_branches bp000100100110 bp000100100111
private noncomputable def vp0001001001011_0 : Blocks := edgeBlocks% "full/vectors/0001001001011-V-0000.bin"
noncomputable def vp0001001001011 : Blocks := vp0001001001011_0
theorem coverp0001001001011 : Covers (-586761639/1000000 : ℚ) vp0001001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001001010_0 : Blocks := edgeBlocks% "full/vectors/0001001001010-V-0000.bin"
noncomputable def vp0001001001010 : Blocks := vp0001001001010_0
theorem coverp0001001001010 : Covers (-585761639/1000000 : ℚ) vp0001001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000100100101_0 : Blocks := edgeBlocks% "full/vectors/000100100101-V-0000.bin"
noncomputable def vp000100100101 : Blocks := vp000100100101_0
private theorem bp0001001001010 : Branch 0 (-585761639/2000000 : ℚ) vp000100100101 := by
  apply branch_left_normalized (c:=vp0001001001010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-585761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-585761639/1000000 : ℚ) by norm_num]
  exact coverp0001001001010
private noncomputable def ep0001001001011_0 : Blocks := edgeBlocks% "full/vectors/0001001001011-E-0000.bin"
noncomputable def ep0001001001011 : Blocks := ep0001001001011_0
private theorem idp0001001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100100101.list =
    C ((2:ℤ)^102) * horner X vp0001001001011.list + horner X ep0001001001011.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001001011 : Branch 1 (-585761639/2000000 : ℚ) vp000100100101 := by
  apply branch_checked idp0001001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-585761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-586761639/1000000 : ℚ) by norm_num]
  exact coverp0001001001011
theorem coverp000100100101 : Covers (-585761639/2000000 : ℚ) vp000100100101 := join_branches bp0001001001010 bp0001001001011
private noncomputable def vp0001001001001_0 : Blocks := edgeBlocks% "full/vectors/0001001001001-V-0000.bin"
noncomputable def vp0001001001001 : Blocks := vp0001001001001_0
theorem coverp0001001001001 : Covers (-584761639/1000000 : ℚ) vp0001001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001001000_0 : Blocks := edgeBlocks% "full/vectors/0001001001000-V-0000.bin"
noncomputable def vp0001001001000 : Blocks := vp0001001001000_0
theorem coverp0001001001000 : Covers (-583761639/1000000 : ℚ) vp0001001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000100100100_0 : Blocks := edgeBlocks% "full/vectors/000100100100-V-0000.bin"
noncomputable def vp000100100100 : Blocks := vp000100100100_0
private theorem bp0001001001000 : Branch 0 (-583761639/2000000 : ℚ) vp000100100100 := by
  apply branch_left_normalized (c:=vp0001001001000) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-583761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-583761639/1000000 : ℚ) by norm_num]
  exact coverp0001001001000
private noncomputable def ep0001001001001_0 : Blocks := edgeBlocks% "full/vectors/0001001001001-E-0000.bin"
noncomputable def ep0001001001001 : Blocks := ep0001001001001_0
private theorem idp0001001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100100100.list =
    C ((2:ℤ)^102) * horner X vp0001001001001.list + horner X ep0001001001001.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001001001 : Branch 1 (-583761639/2000000 : ℚ) vp000100100100 := by
  apply branch_checked idp0001001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-583761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-584761639/1000000 : ℚ) by norm_num]
  exact coverp0001001001001
theorem coverp000100100100 : Covers (-583761639/2000000 : ℚ) vp000100100100 := join_branches bp0001001001000 bp0001001001001
private noncomputable def vp00010010010_0 : Blocks := edgeBlocks% "full/vectors/00010010010-V-0000.bin"
private noncomputable def vp00010010010_1 : Blocks := edgeBlocks% "full/vectors/00010010010-V-0001.bin"
noncomputable def vp00010010010 : Blocks := (Blocks.join vp00010010010_0 vp00010010010_1)
private theorem bp000100100100 : Branch 0 (-583761639/4000000 : ℚ) vp00010010010 := by
  apply branch_left_normalized (c:=vp000100100100) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-583761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-583761639/2000000 : ℚ) by norm_num]
  exact coverp000100100100
private noncomputable def ep000100100101_0 : Blocks := edgeBlocks% "full/vectors/000100100101-E-0000.bin"
private noncomputable def ep000100100101_1 : Blocks := edgeBlocks% "full/vectors/000100100101-E-0001.bin"
noncomputable def ep000100100101 : Blocks := (Blocks.join ep000100100101_0 ep000100100101_1)
private theorem idp000100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010010010.list =
    C ((2:ℤ)^189) * horner X vp000100100101.list + horner X ep000100100101.list := by
  exact edge_identity (B := (2:ℤ)^354) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100100101 : Branch 1 (-583761639/4000000 : ℚ) vp00010010010 := by
  apply branch_checked idp000100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-583761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-585761639/2000000 : ℚ) by norm_num]
  exact coverp000100100101
theorem coverp00010010010 : Covers (-583761639/4000000 : ℚ) vp00010010010 := join_branches bp000100100100 bp000100100101
private noncomputable def vp0001001001_0 : Blocks := edgeBlocks% "full/vectors/0001001001-V-0000.bin"
private noncomputable def vp0001001001_1 : Blocks := edgeBlocks% "full/vectors/0001001001-V-0001.bin"
private noncomputable def vp0001001001_2 : Blocks := edgeBlocks% "full/vectors/0001001001-V-0002.bin"
noncomputable def vp0001001001 : Blocks := (Blocks.join vp0001001001_0 (Blocks.join vp0001001001_1 vp0001001001_2))
private theorem bp00010010010 : Branch 0 (-583761639/8000000 : ℚ) vp0001001001 := by
  apply branch_left_normalized (c:=vp00010010010) (k:=0) (m:=177) (by decide +kernel)
  rw [show 2*(-583761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-583761639/4000000 : ℚ) by norm_num]
  exact coverp00010010010
private noncomputable def ep00010010011_0 : Blocks := edgeBlocks% "full/vectors/00010010011-E-0000.bin"
private noncomputable def ep00010010011_1 : Blocks := edgeBlocks% "full/vectors/00010010011-E-0001.bin"
private noncomputable def ep00010010011_2 : Blocks := edgeBlocks% "full/vectors/00010010011-E-0002.bin"
noncomputable def ep00010010011 : Blocks := (Blocks.join ep00010010011_0 (Blocks.join ep00010010011_1 ep00010010011_2))
private theorem idp00010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001001.list =
    C ((2:ℤ)^362) * horner X vp00010010011.list + horner X ep00010010011.list := by
  exact edge_identity (B := (2:ℤ)^602) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010011 : Branch 1 (-583761639/8000000 : ℚ) vp0001001001 := by
  apply branch_checked idp00010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-583761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-587761639/4000000 : ℚ) by norm_num]
  exact coverp00010010011
theorem coverp0001001001 : Covers (-583761639/8000000 : ℚ) vp0001001001 := join_branches bp00010010010 bp00010010011
private noncomputable def vp0001001000111_0 : Blocks := edgeBlocks% "full/vectors/0001001000111-V-0000.bin"
noncomputable def vp0001001000111 : Blocks := vp0001001000111_0
theorem coverp0001001000111 : Covers (-582761639/1000000 : ℚ) vp0001001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001000110_0 : Blocks := edgeBlocks% "full/vectors/0001001000110-V-0000.bin"
noncomputable def vp0001001000110 : Blocks := vp0001001000110_0
theorem coverp0001001000110 : Covers (-581761639/1000000 : ℚ) vp0001001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000100100011_0 : Blocks := edgeBlocks% "full/vectors/000100100011-V-0000.bin"
noncomputable def vp000100100011 : Blocks := vp000100100011_0
private theorem bp0001001000110 : Branch 0 (-581761639/2000000 : ℚ) vp000100100011 := by
  apply branch_left_normalized (c:=vp0001001000110) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-581761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-581761639/1000000 : ℚ) by norm_num]
  exact coverp0001001000110
private noncomputable def ep0001001000111_0 : Blocks := edgeBlocks% "full/vectors/0001001000111-E-0000.bin"
noncomputable def ep0001001000111 : Blocks := ep0001001000111_0
private theorem idp0001001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100100011.list =
    C ((2:ℤ)^103) * horner X vp0001001000111.list + horner X ep0001001000111.list := by
  exact edge_identity (B := (2:ℤ)^231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001000111 : Branch 1 (-581761639/2000000 : ℚ) vp000100100011 := by
  apply branch_checked idp0001001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-581761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-582761639/1000000 : ℚ) by norm_num]
  exact coverp0001001000111
theorem coverp000100100011 : Covers (-581761639/2000000 : ℚ) vp000100100011 := join_branches bp0001001000110 bp0001001000111
private noncomputable def vp0001001000101_0 : Blocks := edgeBlocks% "full/vectors/0001001000101-V-0000.bin"
noncomputable def vp0001001000101 : Blocks := vp0001001000101_0
theorem coverp0001001000101 : Covers (-580761639/1000000 : ℚ) vp0001001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001000100_0 : Blocks := edgeBlocks% "full/vectors/0001001000100-V-0000.bin"
noncomputable def vp0001001000100 : Blocks := vp0001001000100_0
theorem coverp0001001000100 : Covers (-579761639/1000000 : ℚ) vp0001001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000100100010_0 : Blocks := edgeBlocks% "full/vectors/000100100010-V-0000.bin"
noncomputable def vp000100100010 : Blocks := vp000100100010_0
private theorem bp0001001000100 : Branch 0 (-579761639/2000000 : ℚ) vp000100100010 := by
  apply branch_left_normalized (c:=vp0001001000100) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-579761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-579761639/1000000 : ℚ) by norm_num]
  exact coverp0001001000100
private noncomputable def ep0001001000101_0 : Blocks := edgeBlocks% "full/vectors/0001001000101-E-0000.bin"
noncomputable def ep0001001000101 : Blocks := ep0001001000101_0
private theorem idp0001001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100100010.list =
    C ((2:ℤ)^103) * horner X vp0001001000101.list + horner X ep0001001000101.list := by
  exact edge_identity (B := (2:ℤ)^230) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001000101 : Branch 1 (-579761639/2000000 : ℚ) vp000100100010 := by
  apply branch_checked idp0001001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-579761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-580761639/1000000 : ℚ) by norm_num]
  exact coverp0001001000101
theorem coverp000100100010 : Covers (-579761639/2000000 : ℚ) vp000100100010 := join_branches bp0001001000100 bp0001001000101
private noncomputable def vp00010010001_0 : Blocks := edgeBlocks% "full/vectors/00010010001-V-0000.bin"
private noncomputable def vp00010010001_1 : Blocks := edgeBlocks% "full/vectors/00010010001-V-0001.bin"
noncomputable def vp00010010001 : Blocks := (Blocks.join vp00010010001_0 vp00010010001_1)
private theorem bp000100100010 : Branch 0 (-579761639/4000000 : ℚ) vp00010010001 := by
  apply branch_left_normalized (c:=vp000100100010) (k:=0) (m:=96) (by decide +kernel)
  rw [show 2*(-579761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-579761639/2000000 : ℚ) by norm_num]
  exact coverp000100100010
private noncomputable def ep000100100011_0 : Blocks := edgeBlocks% "full/vectors/000100100011-E-0000.bin"
private noncomputable def ep000100100011_1 : Blocks := edgeBlocks% "full/vectors/000100100011-E-0001.bin"
noncomputable def ep000100100011 : Blocks := (Blocks.join ep000100100011_0 ep000100100011_1)
private theorem idp000100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010010001.list =
    C ((2:ℤ)^190) * horner X vp000100100011.list + horner X ep000100100011.list := by
  exact edge_identity (B := (2:ℤ)^355) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100100011 : Branch 1 (-579761639/4000000 : ℚ) vp00010010001 := by
  apply branch_checked idp000100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-579761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-581761639/2000000 : ℚ) by norm_num]
  exact coverp000100100011
theorem coverp00010010001 : Covers (-579761639/4000000 : ℚ) vp00010010001 := join_branches bp000100100010 bp000100100011
private noncomputable def vp0001001000011_0 : Blocks := edgeBlocks% "full/vectors/0001001000011-V-0000.bin"
noncomputable def vp0001001000011 : Blocks := vp0001001000011_0
theorem coverp0001001000011 : Covers (-578761639/1000000 : ℚ) vp0001001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001000010_0 : Blocks := edgeBlocks% "full/vectors/0001001000010-V-0000.bin"
noncomputable def vp0001001000010 : Blocks := vp0001001000010_0
theorem coverp0001001000010 : Covers (-577761639/1000000 : ℚ) vp0001001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000100100001_0 : Blocks := edgeBlocks% "full/vectors/000100100001-V-0000.bin"
noncomputable def vp000100100001 : Blocks := vp000100100001_0
private theorem bp0001001000010 : Branch 0 (-577761639/2000000 : ℚ) vp000100100001 := by
  apply branch_left_normalized (c:=vp0001001000010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-577761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-577761639/1000000 : ℚ) by norm_num]
  exact coverp0001001000010
private noncomputable def ep0001001000011_0 : Blocks := edgeBlocks% "full/vectors/0001001000011-E-0000.bin"
noncomputable def ep0001001000011 : Blocks := ep0001001000011_0
private theorem idp0001001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100100001.list =
    C ((2:ℤ)^104) * horner X vp0001001000011.list + horner X ep0001001000011.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001000011 : Branch 1 (-577761639/2000000 : ℚ) vp000100100001 := by
  apply branch_checked idp0001001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-577761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-578761639/1000000 : ℚ) by norm_num]
  exact coverp0001001000011
theorem coverp000100100001 : Covers (-577761639/2000000 : ℚ) vp000100100001 := join_branches bp0001001000010 bp0001001000011
private noncomputable def vp0001001000001_0 : Blocks := edgeBlocks% "full/vectors/0001001000001-V-0000.bin"
noncomputable def vp0001001000001 : Blocks := vp0001001000001_0
theorem coverp0001001000001 : Covers (-576761639/1000000 : ℚ) vp0001001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001001000000_0 : Blocks := edgeBlocks% "full/vectors/0001001000000-V-0000.bin"
noncomputable def vp0001001000000 : Blocks := vp0001001000000_0
theorem coverp0001001000000 : Covers (-575761639/1000000 : ℚ) vp0001001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000100100000_0 : Blocks := edgeBlocks% "full/vectors/000100100000-V-0000.bin"
noncomputable def vp000100100000 : Blocks := vp000100100000_0
private theorem bp0001001000000 : Branch 0 (-575761639/2000000 : ℚ) vp000100100000 := by
  apply branch_left_normalized (c:=vp0001001000000) (k:=0) (m:=56) (by decide +kernel)
  rw [show 2*(-575761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-575761639/1000000 : ℚ) by norm_num]
  exact coverp0001001000000
private noncomputable def ep0001001000001_0 : Blocks := edgeBlocks% "full/vectors/0001001000001-E-0000.bin"
noncomputable def ep0001001000001 : Blocks := ep0001001000001_0
private theorem idp0001001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100100000.list =
    C ((2:ℤ)^104) * horner X vp0001001000001.list + horner X ep0001001000001.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001000001 : Branch 1 (-575761639/2000000 : ℚ) vp000100100000 := by
  apply branch_checked idp0001001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-575761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-576761639/1000000 : ℚ) by norm_num]
  exact coverp0001001000001
theorem coverp000100100000 : Covers (-575761639/2000000 : ℚ) vp000100100000 := join_branches bp0001001000000 bp0001001000001
private noncomputable def vp00010010000_0 : Blocks := edgeBlocks% "full/vectors/00010010000-V-0000.bin"
private noncomputable def vp00010010000_1 : Blocks := edgeBlocks% "full/vectors/00010010000-V-0001.bin"
noncomputable def vp00010010000 : Blocks := (Blocks.join vp00010010000_0 vp00010010000_1)
private theorem bp000100100000 : Branch 0 (-575761639/4000000 : ℚ) vp00010010000 := by
  apply branch_left_normalized (c:=vp000100100000) (k:=0) (m:=97) (by decide +kernel)
  rw [show 2*(-575761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-575761639/2000000 : ℚ) by norm_num]
  exact coverp000100100000
private noncomputable def ep000100100001_0 : Blocks := edgeBlocks% "full/vectors/000100100001-E-0000.bin"
private noncomputable def ep000100100001_1 : Blocks := edgeBlocks% "full/vectors/000100100001-E-0001.bin"
noncomputable def ep000100100001 : Blocks := (Blocks.join ep000100100001_0 ep000100100001_1)
private theorem idp000100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010010000.list =
    C ((2:ℤ)^192) * horner X vp000100100001.list + horner X ep000100100001.list := by
  exact edge_identity (B := (2:ℤ)^358) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100100001 : Branch 1 (-575761639/4000000 : ℚ) vp00010010000 := by
  apply branch_checked idp000100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-575761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-577761639/2000000 : ℚ) by norm_num]
  exact coverp000100100001
theorem coverp00010010000 : Covers (-575761639/4000000 : ℚ) vp00010010000 := join_branches bp000100100000 bp000100100001
private noncomputable def vp0001001000_0 : Blocks := edgeBlocks% "full/vectors/0001001000-V-0000.bin"
private noncomputable def vp0001001000_1 : Blocks := edgeBlocks% "full/vectors/0001001000-V-0001.bin"
private noncomputable def vp0001001000_2 : Blocks := edgeBlocks% "full/vectors/0001001000-V-0002.bin"
noncomputable def vp0001001000 : Blocks := (Blocks.join vp0001001000_0 (Blocks.join vp0001001000_1 vp0001001000_2))
private theorem bp00010010000 : Branch 0 (-575761639/8000000 : ℚ) vp0001001000 := by
  apply branch_left_normalized (c:=vp00010010000) (k:=0) (m:=179) (by decide +kernel)
  rw [show 2*(-575761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-575761639/4000000 : ℚ) by norm_num]
  exact coverp00010010000
private noncomputable def ep00010010001_0 : Blocks := edgeBlocks% "full/vectors/00010010001-E-0000.bin"
private noncomputable def ep00010010001_1 : Blocks := edgeBlocks% "full/vectors/00010010001-E-0001.bin"
private noncomputable def ep00010010001_2 : Blocks := edgeBlocks% "full/vectors/00010010001-E-0002.bin"
noncomputable def ep00010010001 : Blocks := (Blocks.join ep00010010001_0 (Blocks.join ep00010010001_1 ep00010010001_2))
private theorem idp00010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001000.list =
    C ((2:ℤ)^366) * horner X vp00010010001.list + horner X ep00010010001.list := by
  exact edge_identity (B := (2:ℤ)^607) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010010001 : Branch 1 (-575761639/8000000 : ℚ) vp0001001000 := by
  apply branch_checked idp00010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-575761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-579761639/4000000 : ℚ) by norm_num]
  exact coverp00010010001
theorem coverp0001001000 : Covers (-575761639/8000000 : ℚ) vp0001001000 := join_branches bp00010010000 bp00010010001
private noncomputable def vp000100100_0 : Blocks := edgeBlocks% "full/vectors/000100100-V-0000.bin"
private noncomputable def vp000100100_1 : Blocks := edgeBlocks% "full/vectors/000100100-V-0001.bin"
private noncomputable def vp000100100_2 : Blocks := edgeBlocks% "full/vectors/000100100-V-0002.bin"
private noncomputable def vp000100100_3 : Blocks := edgeBlocks% "full/vectors/000100100-V-0003.bin"
private noncomputable def vp000100100_4 : Blocks := edgeBlocks% "full/vectors/000100100-V-0004.bin"
private noncomputable def vp000100100_5 : Blocks := edgeBlocks% "full/vectors/000100100-V-0005.bin"
noncomputable def vp000100100 : Blocks := (Blocks.join (Blocks.join vp000100100_0 (Blocks.join vp000100100_1 vp000100100_2)) (Blocks.join vp000100100_3 (Blocks.join vp000100100_4 vp000100100_5)))
private theorem bp0001001000 : Branch 0 (-575761639/16000000 : ℚ) vp000100100 := by
  apply branch_left_normalized (c:=vp0001001000) (k:=0) (m:=341) (by decide +kernel)
  rw [show 2*(-575761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-575761639/8000000 : ℚ) by norm_num]
  exact coverp0001001000
private noncomputable def ep0001001001_0 : Blocks := edgeBlocks% "full/vectors/0001001001-E-0000.bin"
private noncomputable def ep0001001001_1 : Blocks := edgeBlocks% "full/vectors/0001001001-E-0001.bin"
private noncomputable def ep0001001001_2 : Blocks := edgeBlocks% "full/vectors/0001001001-E-0002.bin"
private noncomputable def ep0001001001_3 : Blocks := edgeBlocks% "full/vectors/0001001001-E-0003.bin"
private noncomputable def ep0001001001_4 : Blocks := edgeBlocks% "full/vectors/0001001001-E-0004.bin"
private noncomputable def ep0001001001_5 : Blocks := edgeBlocks% "full/vectors/0001001001-E-0005.bin"
noncomputable def ep0001001001 : Blocks := (Blocks.join (Blocks.join ep0001001001_0 (Blocks.join ep0001001001_1 ep0001001001_2)) (Blocks.join ep0001001001_3 (Blocks.join ep0001001001_4 ep0001001001_5)))
private theorem idp0001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000100100.list =
    C ((2:ℤ)^713) * horner X vp0001001001.list + horner X ep0001001001.list := by
  exact edge_identity (B := (2:ℤ)^1104) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001001001 : Branch 1 (-575761639/16000000 : ℚ) vp000100100 := by
  apply branch_checked idp0001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-575761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-583761639/8000000 : ℚ) by norm_num]
  exact coverp0001001001
theorem coverp000100100 : Covers (-575761639/16000000 : ℚ) vp000100100 := join_branches bp0001001000 bp0001001001
private noncomputable def vp00010010_0 : Blocks := edgeBlocks% "full/vectors/00010010-V-0000.bin"
private noncomputable def vp00010010_1 : Blocks := edgeBlocks% "full/vectors/00010010-V-0001.bin"
private noncomputable def vp00010010_2 : Blocks := edgeBlocks% "full/vectors/00010010-V-0002.bin"
private noncomputable def vp00010010_3 : Blocks := edgeBlocks% "full/vectors/00010010-V-0003.bin"
private noncomputable def vp00010010_4 : Blocks := edgeBlocks% "full/vectors/00010010-V-0004.bin"
private noncomputable def vp00010010_5 : Blocks := edgeBlocks% "full/vectors/00010010-V-0005.bin"
private noncomputable def vp00010010_6 : Blocks := edgeBlocks% "full/vectors/00010010-V-0006.bin"
private noncomputable def vp00010010_7 : Blocks := edgeBlocks% "full/vectors/00010010-V-0007.bin"
private noncomputable def vp00010010_8 : Blocks := edgeBlocks% "full/vectors/00010010-V-0008.bin"
private noncomputable def vp00010010_9 : Blocks := edgeBlocks% "full/vectors/00010010-V-0009.bin"
private noncomputable def vp00010010_10 : Blocks := edgeBlocks% "full/vectors/00010010-V-0010.bin"
noncomputable def vp00010010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00010010_0 vp00010010_1) (Blocks.join vp00010010_2 (Blocks.join vp00010010_3 vp00010010_4))) (Blocks.join (Blocks.join vp00010010_5 (Blocks.join vp00010010_6 vp00010010_7)) (Blocks.join vp00010010_8 (Blocks.join vp00010010_9 vp00010010_10))))
private theorem bp000100100 : Branch 0 (-575761639/32000000 : ℚ) vp00010010 := by
  apply branch_left_normalized (c:=vp000100100) (k:=0) (m:=665) (by decide +kernel)
  rw [show 2*(-575761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-575761639/16000000 : ℚ) by norm_num]
  exact coverp000100100
private noncomputable def ep000100101_0 : Blocks := edgeBlocks% "full/vectors/000100101-E-0000.bin"
private noncomputable def ep000100101_1 : Blocks := edgeBlocks% "full/vectors/000100101-E-0001.bin"
private noncomputable def ep000100101_2 : Blocks := edgeBlocks% "full/vectors/000100101-E-0002.bin"
private noncomputable def ep000100101_3 : Blocks := edgeBlocks% "full/vectors/000100101-E-0003.bin"
private noncomputable def ep000100101_4 : Blocks := edgeBlocks% "full/vectors/000100101-E-0004.bin"
private noncomputable def ep000100101_5 : Blocks := edgeBlocks% "full/vectors/000100101-E-0005.bin"
private noncomputable def ep000100101_6 : Blocks := edgeBlocks% "full/vectors/000100101-E-0006.bin"
private noncomputable def ep000100101_7 : Blocks := edgeBlocks% "full/vectors/000100101-E-0007.bin"
private noncomputable def ep000100101_8 : Blocks := edgeBlocks% "full/vectors/000100101-E-0008.bin"
private noncomputable def ep000100101_9 : Blocks := edgeBlocks% "full/vectors/000100101-E-0009.bin"
private noncomputable def ep000100101_10 : Blocks := edgeBlocks% "full/vectors/000100101-E-0010.bin"
noncomputable def ep000100101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000100101_0 ep000100101_1) (Blocks.join ep000100101_2 (Blocks.join ep000100101_3 ep000100101_4))) (Blocks.join (Blocks.join ep000100101_5 (Blocks.join ep000100101_6 ep000100101_7)) (Blocks.join ep000100101_8 (Blocks.join ep000100101_9 ep000100101_10))))
private theorem idp000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010010.list =
    C ((2:ℤ)^1390) * horner X vp000100101.list + horner X ep000100101.list := by
  exact edge_identity (B := (2:ℤ)^2084) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000100101 : Branch 1 (-575761639/32000000 : ℚ) vp00010010 := by
  apply branch_checked idp000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-575761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-591761639/16000000 : ℚ) by norm_num]
  exact coverp000100101
theorem coverp00010010 : Covers (-575761639/32000000 : ℚ) vp00010010 := join_branches bp000100100 bp000100101
private noncomputable def vp0001001_0 : Blocks := edgeBlocks% "full/vectors/0001001-V-0000.bin"
private noncomputable def vp0001001_1 : Blocks := edgeBlocks% "full/vectors/0001001-V-0001.bin"
private noncomputable def vp0001001_2 : Blocks := edgeBlocks% "full/vectors/0001001-V-0002.bin"
private noncomputable def vp0001001_3 : Blocks := edgeBlocks% "full/vectors/0001001-V-0003.bin"
private noncomputable def vp0001001_4 : Blocks := edgeBlocks% "full/vectors/0001001-V-0004.bin"
private noncomputable def vp0001001_5 : Blocks := edgeBlocks% "full/vectors/0001001-V-0005.bin"
private noncomputable def vp0001001_6 : Blocks := edgeBlocks% "full/vectors/0001001-V-0006.bin"
private noncomputable def vp0001001_7 : Blocks := edgeBlocks% "full/vectors/0001001-V-0007.bin"
private noncomputable def vp0001001_8 : Blocks := edgeBlocks% "full/vectors/0001001-V-0008.bin"
private noncomputable def vp0001001_9 : Blocks := edgeBlocks% "full/vectors/0001001-V-0009.bin"
private noncomputable def vp0001001_10 : Blocks := edgeBlocks% "full/vectors/0001001-V-0010.bin"
private noncomputable def vp0001001_11 : Blocks := edgeBlocks% "full/vectors/0001001-V-0011.bin"
private noncomputable def vp0001001_12 : Blocks := edgeBlocks% "full/vectors/0001001-V-0012.bin"
private noncomputable def vp0001001_13 : Blocks := edgeBlocks% "full/vectors/0001001-V-0013.bin"
private noncomputable def vp0001001_14 : Blocks := edgeBlocks% "full/vectors/0001001-V-0014.bin"
private noncomputable def vp0001001_15 : Blocks := edgeBlocks% "full/vectors/0001001-V-0015.bin"
private noncomputable def vp0001001_16 : Blocks := edgeBlocks% "full/vectors/0001001-V-0016.bin"
private noncomputable def vp0001001_17 : Blocks := edgeBlocks% "full/vectors/0001001-V-0017.bin"
private noncomputable def vp0001001_18 : Blocks := edgeBlocks% "full/vectors/0001001-V-0018.bin"
private noncomputable def vp0001001_19 : Blocks := edgeBlocks% "full/vectors/0001001-V-0019.bin"
noncomputable def vp0001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp0001001_0 vp0001001_1) (Blocks.join vp0001001_2 (Blocks.join vp0001001_3 vp0001001_4))) (Blocks.join (Blocks.join vp0001001_5 vp0001001_6) (Blocks.join vp0001001_7 (Blocks.join vp0001001_8 vp0001001_9)))) (Blocks.join (Blocks.join (Blocks.join vp0001001_10 vp0001001_11) (Blocks.join vp0001001_12 (Blocks.join vp0001001_13 vp0001001_14))) (Blocks.join (Blocks.join vp0001001_15 vp0001001_16) (Blocks.join vp0001001_17 (Blocks.join vp0001001_18 vp0001001_19)))))
private theorem bp00010010 : Branch 0 (-575761639/64000000 : ℚ) vp0001001 := by
  apply branch_left_normalized (c:=vp00010010) (k:=0) (m:=1301) (by decide +kernel)
  rw [show 2*(-575761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-575761639/32000000 : ℚ) by norm_num]
  exact coverp00010010
private noncomputable def ep00010011_0 : Blocks := edgeBlocks% "full/vectors/00010011-E-0000.bin"
private noncomputable def ep00010011_1 : Blocks := edgeBlocks% "full/vectors/00010011-E-0001.bin"
private noncomputable def ep00010011_2 : Blocks := edgeBlocks% "full/vectors/00010011-E-0002.bin"
private noncomputable def ep00010011_3 : Blocks := edgeBlocks% "full/vectors/00010011-E-0003.bin"
private noncomputable def ep00010011_4 : Blocks := edgeBlocks% "full/vectors/00010011-E-0004.bin"
private noncomputable def ep00010011_5 : Blocks := edgeBlocks% "full/vectors/00010011-E-0005.bin"
private noncomputable def ep00010011_6 : Blocks := edgeBlocks% "full/vectors/00010011-E-0006.bin"
private noncomputable def ep00010011_7 : Blocks := edgeBlocks% "full/vectors/00010011-E-0007.bin"
private noncomputable def ep00010011_8 : Blocks := edgeBlocks% "full/vectors/00010011-E-0008.bin"
private noncomputable def ep00010011_9 : Blocks := edgeBlocks% "full/vectors/00010011-E-0009.bin"
private noncomputable def ep00010011_10 : Blocks := edgeBlocks% "full/vectors/00010011-E-0010.bin"
private noncomputable def ep00010011_11 : Blocks := edgeBlocks% "full/vectors/00010011-E-0011.bin"
private noncomputable def ep00010011_12 : Blocks := edgeBlocks% "full/vectors/00010011-E-0012.bin"
private noncomputable def ep00010011_13 : Blocks := edgeBlocks% "full/vectors/00010011-E-0013.bin"
private noncomputable def ep00010011_14 : Blocks := edgeBlocks% "full/vectors/00010011-E-0014.bin"
private noncomputable def ep00010011_15 : Blocks := edgeBlocks% "full/vectors/00010011-E-0015.bin"
private noncomputable def ep00010011_16 : Blocks := edgeBlocks% "full/vectors/00010011-E-0016.bin"
private noncomputable def ep00010011_17 : Blocks := edgeBlocks% "full/vectors/00010011-E-0017.bin"
private noncomputable def ep00010011_18 : Blocks := edgeBlocks% "full/vectors/00010011-E-0018.bin"
private noncomputable def ep00010011_19 : Blocks := edgeBlocks% "full/vectors/00010011-E-0019.bin"
noncomputable def ep00010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep00010011_0 ep00010011_1) (Blocks.join ep00010011_2 (Blocks.join ep00010011_3 ep00010011_4))) (Blocks.join (Blocks.join ep00010011_5 ep00010011_6) (Blocks.join ep00010011_7 (Blocks.join ep00010011_8 ep00010011_9)))) (Blocks.join (Blocks.join (Blocks.join ep00010011_10 ep00010011_11) (Blocks.join ep00010011_12 (Blocks.join ep00010011_13 ep00010011_14))) (Blocks.join (Blocks.join ep00010011_15 ep00010011_16) (Blocks.join ep00010011_17 (Blocks.join ep00010011_18 ep00010011_19)))))
private theorem idp00010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001001.list =
    C ((2:ℤ)^2709) * horner X vp00010011.list + horner X ep00010011.list := by
  exact edge_identity (B := (2:ℤ)^3998) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010011 : Branch 1 (-575761639/64000000 : ℚ) vp0001001 := by
  apply branch_checked idp00010011 (by positivity) (by decide +kernel)
  rw [show 2*(-575761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-607761639/32000000 : ℚ) by norm_num]
  exact coverp00010011
theorem coverp0001001 : Covers (-575761639/64000000 : ℚ) vp0001001 := join_branches bp00010010 bp00010011
end NextProof.EdgeFull

