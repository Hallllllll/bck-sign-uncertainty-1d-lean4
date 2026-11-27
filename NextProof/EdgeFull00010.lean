import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00009

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0000000000101011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011111-V-0000.bin"
noncomputable def vp0000000000101011111 : Blocks := vp0000000000101011111_0
theorem coverp0000000000101011111 : Covers (-5246014/15625 : ℚ) vp0000000000101011111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010101111011_0 : Blocks := edgeBlocks% "full/vectors/000000000010101111011-V-0000.bin"
noncomputable def vp000000000010101111011 : Blocks := vp000000000010101111011_0
theorem coverp000000000010101111011 : Covers (-20968431/15625 : ℚ) vp000000000010101111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010101111010_0 : Blocks := edgeBlocks% "full/vectors/000000000010101111010-V-0000.bin"
noncomputable def vp000000000010101111010 : Blocks := vp000000000010101111010_0
theorem coverp000000000010101111010 : Covers (-20952806/15625 : ℚ) vp000000000010101111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010111101_0 : Blocks := edgeBlocks% "full/vectors/00000000001010111101-V-0000.bin"
noncomputable def vp00000000001010111101 : Blocks := vp00000000001010111101_0
private theorem bp000000000010101111010 : Branch 0 (-10476403/15625 : ℚ) vp00000000001010111101 := by
  apply branch_left_normalized (c:=vp000000000010101111010) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-10476403/15625 : ℚ) - ((0:ℤ):ℚ) = (-20952806/15625 : ℚ) by norm_num]
  exact coverp000000000010101111010
private noncomputable def ep000000000010101111011_0 : Blocks := edgeBlocks% "full/vectors/000000000010101111011-E-0000.bin"
noncomputable def ep000000000010101111011 : Blocks := ep000000000010101111011_0
private theorem idp000000000010101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001010111101.list =
    C ((2:ℤ)^18) * horner X vp000000000010101111011.list + horner X ep000000000010101111011.list := by
  exact edge_identity (B := (2:ℤ)^127) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010101111011 : Branch 1 (-10476403/15625 : ℚ) vp00000000001010111101 := by
  apply branch_checked idp000000000010101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-10476403/15625 : ℚ) - ((1:ℤ):ℚ) = (-20968431/15625 : ℚ) by norm_num]
  exact coverp000000000010101111011
theorem coverp00000000001010111101 : Covers (-10476403/15625 : ℚ) vp00000000001010111101 := join_branches bp000000000010101111010 bp000000000010101111011
private noncomputable def vp00000000001010111100_0 : Blocks := edgeBlocks% "full/vectors/00000000001010111100-V-0000.bin"
noncomputable def vp00000000001010111100 : Blocks := vp00000000001010111100_0
theorem coverp00000000001010111100 : Covers (-10460778/15625 : ℚ) vp00000000001010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101011110_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011110-V-0000.bin"
noncomputable def vp0000000000101011110 : Blocks := vp0000000000101011110_0
private theorem bp00000000001010111100 : Branch 0 (-5230389/15625 : ℚ) vp0000000000101011110 := by
  apply branch_left_normalized (c:=vp00000000001010111100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5230389/15625 : ℚ) - ((0:ℤ):ℚ) = (-10460778/15625 : ℚ) by norm_num]
  exact coverp00000000001010111100
private noncomputable def ep00000000001010111101_0 : Blocks := edgeBlocks% "full/vectors/00000000001010111101-E-0000.bin"
noncomputable def ep00000000001010111101 : Blocks := ep00000000001010111101_0
private theorem idp00000000001010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101011110.list =
    C ((2:ℤ)^22) * horner X vp00000000001010111101.list + horner X ep00000000001010111101.list := by
  exact edge_identity (B := (2:ℤ)^133) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010111101 : Branch 1 (-5230389/15625 : ℚ) vp0000000000101011110 := by
  apply branch_checked idp00000000001010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-5230389/15625 : ℚ) - ((1:ℤ):ℚ) = (-10476403/15625 : ℚ) by norm_num]
  exact coverp00000000001010111101
theorem coverp0000000000101011110 : Covers (-5230389/15625 : ℚ) vp0000000000101011110 := join_branches bp00000000001010111100 bp00000000001010111101
private noncomputable def vp000000000010101111_0 : Blocks := edgeBlocks% "full/vectors/000000000010101111-V-0000.bin"
noncomputable def vp000000000010101111 : Blocks := vp000000000010101111_0
private theorem bp0000000000101011110 : Branch 0 (-5230389/31250 : ℚ) vp000000000010101111 := by
  apply branch_left_normalized (c:=vp0000000000101011110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-5230389/31250 : ℚ) - ((0:ℤ):ℚ) = (-5230389/15625 : ℚ) by norm_num]
  exact coverp0000000000101011110
private noncomputable def ep0000000000101011111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011111-E-0000.bin"
noncomputable def ep0000000000101011111 : Blocks := ep0000000000101011111_0
private theorem idp0000000000101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010101111.list =
    C ((2:ℤ)^31) * horner X vp0000000000101011111.list + horner X ep0000000000101011111.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101011111 : Branch 1 (-5230389/31250 : ℚ) vp000000000010101111 := by
  apply branch_checked idp0000000000101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-5230389/31250 : ℚ) - ((1:ℤ):ℚ) = (-5246014/15625 : ℚ) by norm_num]
  exact coverp0000000000101011111
theorem coverp000000000010101111 : Covers (-5230389/31250 : ℚ) vp000000000010101111 := join_branches bp0000000000101011110 bp0000000000101011111
private noncomputable def vp0000000000101011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011101-V-0000.bin"
noncomputable def vp0000000000101011101 : Blocks := vp0000000000101011101_0
theorem coverp0000000000101011101 : Covers (-5214764/15625 : ℚ) vp0000000000101011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101011100_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011100-V-0000.bin"
noncomputable def vp0000000000101011100 : Blocks := vp0000000000101011100_0
theorem coverp0000000000101011100 : Covers (-5199139/15625 : ℚ) vp0000000000101011100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010101110_0 : Blocks := edgeBlocks% "full/vectors/000000000010101110-V-0000.bin"
noncomputable def vp000000000010101110 : Blocks := vp000000000010101110_0
private theorem bp0000000000101011100 : Branch 0 (-5199139/31250 : ℚ) vp000000000010101110 := by
  apply branch_left_normalized (c:=vp0000000000101011100) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-5199139/31250 : ℚ) - ((0:ℤ):ℚ) = (-5199139/15625 : ℚ) by norm_num]
  exact coverp0000000000101011100
private noncomputable def ep0000000000101011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011101-E-0000.bin"
noncomputable def ep0000000000101011101 : Blocks := ep0000000000101011101_0
private theorem idp0000000000101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010101110.list =
    C ((2:ℤ)^32) * horner X vp0000000000101011101.list + horner X ep0000000000101011101.list := by
  exact edge_identity (B := (2:ℤ)^145) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101011101 : Branch 1 (-5199139/31250 : ℚ) vp000000000010101110 := by
  apply branch_checked idp0000000000101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-5199139/31250 : ℚ) - ((1:ℤ):ℚ) = (-5214764/15625 : ℚ) by norm_num]
  exact coverp0000000000101011101
theorem coverp000000000010101110 : Covers (-5199139/31250 : ℚ) vp000000000010101110 := join_branches bp0000000000101011100 bp0000000000101011101
private noncomputable def vp00000000001010111_0 : Blocks := edgeBlocks% "full/vectors/00000000001010111-V-0000.bin"
noncomputable def vp00000000001010111 : Blocks := vp00000000001010111_0
private theorem bp000000000010101110 : Branch 0 (-5199139/62500 : ℚ) vp00000000001010111 := by
  apply branch_left_normalized (c:=vp000000000010101110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-5199139/62500 : ℚ) - ((0:ℤ):ℚ) = (-5199139/31250 : ℚ) by norm_num]
  exact coverp000000000010101110
private noncomputable def ep000000000010101111_0 : Blocks := edgeBlocks% "full/vectors/000000000010101111-E-0000.bin"
noncomputable def ep000000000010101111 : Blocks := ep000000000010101111_0
private theorem idp000000000010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001010111.list =
    C ((2:ℤ)^47) * horner X vp000000000010101111.list + horner X ep000000000010101111.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010101111 : Branch 1 (-5199139/62500 : ℚ) vp00000000001010111 := by
  apply branch_checked idp000000000010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-5199139/62500 : ℚ) - ((1:ℤ):ℚ) = (-5230389/31250 : ℚ) by norm_num]
  exact coverp000000000010101111
theorem coverp00000000001010111 : Covers (-5199139/62500 : ℚ) vp00000000001010111 := join_branches bp000000000010101110 bp000000000010101111
private noncomputable def vp00000000001010110111_0 : Blocks := edgeBlocks% "full/vectors/00000000001010110111-V-0000.bin"
noncomputable def vp00000000001010110111 : Blocks := vp00000000001010110111_0
theorem coverp00000000001010110111 : Covers (-10382653/15625 : ℚ) vp00000000001010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010110110_0 : Blocks := edgeBlocks% "full/vectors/00000000001010110110-V-0000.bin"
noncomputable def vp00000000001010110110 : Blocks := vp00000000001010110110_0
theorem coverp00000000001010110110 : Covers (-10367028/15625 : ℚ) vp00000000001010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011011-V-0000.bin"
noncomputable def vp0000000000101011011 : Blocks := vp0000000000101011011_0
private theorem bp00000000001010110110 : Branch 0 (-5183514/15625 : ℚ) vp0000000000101011011 := by
  apply branch_left_normalized (c:=vp00000000001010110110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5183514/15625 : ℚ) - ((0:ℤ):ℚ) = (-10367028/15625 : ℚ) by norm_num]
  exact coverp00000000001010110110
private noncomputable def ep00000000001010110111_0 : Blocks := edgeBlocks% "full/vectors/00000000001010110111-E-0000.bin"
noncomputable def ep00000000001010110111 : Blocks := ep00000000001010110111_0
private theorem idp00000000001010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101011011.list =
    C ((2:ℤ)^23) * horner X vp00000000001010110111.list + horner X ep00000000001010110111.list := by
  exact edge_identity (B := (2:ℤ)^133) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010110111 : Branch 1 (-5183514/15625 : ℚ) vp0000000000101011011 := by
  apply branch_checked idp00000000001010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-5183514/15625 : ℚ) - ((1:ℤ):ℚ) = (-10382653/15625 : ℚ) by norm_num]
  exact coverp00000000001010110111
theorem coverp0000000000101011011 : Covers (-5183514/15625 : ℚ) vp0000000000101011011 := join_branches bp00000000001010110110 bp00000000001010110111
private noncomputable def vp0000000000101011010_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011010-V-0000.bin"
noncomputable def vp0000000000101011010 : Blocks := vp0000000000101011010_0
theorem coverp0000000000101011010 : Covers (-5167889/15625 : ℚ) vp0000000000101011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010101101_0 : Blocks := edgeBlocks% "full/vectors/000000000010101101-V-0000.bin"
noncomputable def vp000000000010101101 : Blocks := vp000000000010101101_0
private theorem bp0000000000101011010 : Branch 0 (-5167889/31250 : ℚ) vp000000000010101101 := by
  apply branch_left_normalized (c:=vp0000000000101011010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-5167889/31250 : ℚ) - ((0:ℤ):ℚ) = (-5167889/15625 : ℚ) by norm_num]
  exact coverp0000000000101011010
private noncomputable def ep0000000000101011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011011-E-0000.bin"
noncomputable def ep0000000000101011011 : Blocks := ep0000000000101011011_0
private theorem idp0000000000101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010101101.list =
    C ((2:ℤ)^31) * horner X vp0000000000101011011.list + horner X ep0000000000101011011.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101011011 : Branch 1 (-5167889/31250 : ℚ) vp000000000010101101 := by
  apply branch_checked idp0000000000101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-5167889/31250 : ℚ) - ((1:ℤ):ℚ) = (-5183514/15625 : ℚ) by norm_num]
  exact coverp0000000000101011011
theorem coverp000000000010101101 : Covers (-5167889/31250 : ℚ) vp000000000010101101 := join_branches bp0000000000101011010 bp0000000000101011011
private noncomputable def vp0000000000101011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011001-V-0000.bin"
noncomputable def vp0000000000101011001 : Blocks := vp0000000000101011001_0
theorem coverp0000000000101011001 : Covers (-5152264/15625 : ℚ) vp0000000000101011001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010110001_0 : Blocks := edgeBlocks% "full/vectors/00000000001010110001-V-0000.bin"
noncomputable def vp00000000001010110001 : Blocks := vp00000000001010110001_0
theorem coverp00000000001010110001 : Covers (-10288903/15625 : ℚ) vp00000000001010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010110000_0 : Blocks := edgeBlocks% "full/vectors/00000000001010110000-V-0000.bin"
noncomputable def vp00000000001010110000 : Blocks := vp00000000001010110000_0
theorem coverp00000000001010110000 : Covers (-10273278/15625 : ℚ) vp00000000001010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101011000_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011000-V-0000.bin"
noncomputable def vp0000000000101011000 : Blocks := vp0000000000101011000_0
private theorem bp00000000001010110000 : Branch 0 (-5136639/15625 : ℚ) vp0000000000101011000 := by
  apply branch_left_normalized (c:=vp00000000001010110000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5136639/15625 : ℚ) - ((0:ℤ):ℚ) = (-10273278/15625 : ℚ) by norm_num]
  exact coverp00000000001010110000
private noncomputable def ep00000000001010110001_0 : Blocks := edgeBlocks% "full/vectors/00000000001010110001-E-0000.bin"
noncomputable def ep00000000001010110001 : Blocks := ep00000000001010110001_0
private theorem idp00000000001010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101011000.list =
    C ((2:ℤ)^23) * horner X vp00000000001010110001.list + horner X ep00000000001010110001.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010110001 : Branch 1 (-5136639/15625 : ℚ) vp0000000000101011000 := by
  apply branch_checked idp00000000001010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-5136639/15625 : ℚ) - ((1:ℤ):ℚ) = (-10288903/15625 : ℚ) by norm_num]
  exact coverp00000000001010110001
theorem coverp0000000000101011000 : Covers (-5136639/15625 : ℚ) vp0000000000101011000 := join_branches bp00000000001010110000 bp00000000001010110001
private noncomputable def vp000000000010101100_0 : Blocks := edgeBlocks% "full/vectors/000000000010101100-V-0000.bin"
noncomputable def vp000000000010101100 : Blocks := vp000000000010101100_0
private theorem bp0000000000101011000 : Branch 0 (-5136639/31250 : ℚ) vp000000000010101100 := by
  apply branch_left_normalized (c:=vp0000000000101011000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-5136639/31250 : ℚ) - ((0:ℤ):ℚ) = (-5136639/15625 : ℚ) by norm_num]
  exact coverp0000000000101011000
private noncomputable def ep0000000000101011001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011001-E-0000.bin"
noncomputable def ep0000000000101011001 : Blocks := ep0000000000101011001_0
private theorem idp0000000000101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010101100.list =
    C ((2:ℤ)^32) * horner X vp0000000000101011001.list + horner X ep0000000000101011001.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101011001 : Branch 1 (-5136639/31250 : ℚ) vp000000000010101100 := by
  apply branch_checked idp0000000000101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-5136639/31250 : ℚ) - ((1:ℤ):ℚ) = (-5152264/15625 : ℚ) by norm_num]
  exact coverp0000000000101011001
theorem coverp000000000010101100 : Covers (-5136639/31250 : ℚ) vp000000000010101100 := join_branches bp0000000000101011000 bp0000000000101011001
private noncomputable def vp00000000001010110_0 : Blocks := edgeBlocks% "full/vectors/00000000001010110-V-0000.bin"
noncomputable def vp00000000001010110 : Blocks := vp00000000001010110_0
private theorem bp000000000010101100 : Branch 0 (-5136639/62500 : ℚ) vp00000000001010110 := by
  apply branch_left_normalized (c:=vp000000000010101100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-5136639/62500 : ℚ) - ((0:ℤ):ℚ) = (-5136639/31250 : ℚ) by norm_num]
  exact coverp000000000010101100
private noncomputable def ep000000000010101101_0 : Blocks := edgeBlocks% "full/vectors/000000000010101101-E-0000.bin"
noncomputable def ep000000000010101101 : Blocks := ep000000000010101101_0
private theorem idp000000000010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001010110.list =
    C ((2:ℤ)^47) * horner X vp000000000010101101.list + horner X ep000000000010101101.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010101101 : Branch 1 (-5136639/62500 : ℚ) vp00000000001010110 := by
  apply branch_checked idp000000000010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-5136639/62500 : ℚ) - ((1:ℤ):ℚ) = (-5167889/31250 : ℚ) by norm_num]
  exact coverp000000000010101101
theorem coverp00000000001010110 : Covers (-5136639/62500 : ℚ) vp00000000001010110 := join_branches bp000000000010101100 bp000000000010101101
private noncomputable def vp0000000000101011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011-V-0000.bin"
noncomputable def vp0000000000101011 : Blocks := vp0000000000101011_0
private theorem bp00000000001010110 : Branch 0 (-5136639/125000 : ℚ) vp0000000000101011 := by
  apply branch_left_normalized (c:=vp00000000001010110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-5136639/125000 : ℚ) - ((0:ℤ):ℚ) = (-5136639/62500 : ℚ) by norm_num]
  exact coverp00000000001010110
private noncomputable def ep00000000001010111_0 : Blocks := edgeBlocks% "full/vectors/00000000001010111-E-0000.bin"
noncomputable def ep00000000001010111 : Blocks := ep00000000001010111_0
private theorem idp00000000001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101011.list =
    C ((2:ℤ)^76) * horner X vp00000000001010111.list + horner X ep00000000001010111.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010111 : Branch 1 (-5136639/125000 : ℚ) vp0000000000101011 := by
  apply branch_checked idp00000000001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-5136639/125000 : ℚ) - ((1:ℤ):ℚ) = (-5199139/62500 : ℚ) by norm_num]
  exact coverp00000000001010111
theorem coverp0000000000101011 : Covers (-5136639/125000 : ℚ) vp0000000000101011 := join_branches bp00000000001010110 bp00000000001010111
private noncomputable def vp0000000000101010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010111-V-0000.bin"
noncomputable def vp0000000000101010111 : Blocks := vp0000000000101010111_0
theorem coverp0000000000101010111 : Covers (-5121014/15625 : ℚ) vp0000000000101010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101010110_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010110-V-0000.bin"
noncomputable def vp0000000000101010110 : Blocks := vp0000000000101010110_0
theorem coverp0000000000101010110 : Covers (-5105389/15625 : ℚ) vp0000000000101010110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010101011_0 : Blocks := edgeBlocks% "full/vectors/000000000010101011-V-0000.bin"
noncomputable def vp000000000010101011 : Blocks := vp000000000010101011_0
private theorem bp0000000000101010110 : Branch 0 (-5105389/31250 : ℚ) vp000000000010101011 := by
  apply branch_left_normalized (c:=vp0000000000101010110) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-5105389/31250 : ℚ) - ((0:ℤ):ℚ) = (-5105389/15625 : ℚ) by norm_num]
  exact coverp0000000000101010110
private noncomputable def ep0000000000101010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010111-E-0000.bin"
noncomputable def ep0000000000101010111 : Blocks := ep0000000000101010111_0
private theorem idp0000000000101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010101011.list =
    C ((2:ℤ)^32) * horner X vp0000000000101010111.list + horner X ep0000000000101010111.list := by
  exact edge_identity (B := (2:ℤ)^144) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101010111 : Branch 1 (-5105389/31250 : ℚ) vp000000000010101011 := by
  apply branch_checked idp0000000000101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-5105389/31250 : ℚ) - ((1:ℤ):ℚ) = (-5121014/15625 : ℚ) by norm_num]
  exact coverp0000000000101010111
theorem coverp000000000010101011 : Covers (-5105389/31250 : ℚ) vp000000000010101011 := join_branches bp0000000000101010110 bp0000000000101010111
private noncomputable def vp00000000001010101011_0 : Blocks := edgeBlocks% "full/vectors/00000000001010101011-V-0000.bin"
noncomputable def vp00000000001010101011 : Blocks := vp00000000001010101011_0
theorem coverp00000000001010101011 : Covers (-10195153/15625 : ℚ) vp00000000001010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010101010_0 : Blocks := edgeBlocks% "full/vectors/00000000001010101010-V-0000.bin"
noncomputable def vp00000000001010101010 : Blocks := vp00000000001010101010_0
theorem coverp00000000001010101010 : Covers (-10179528/15625 : ℚ) vp00000000001010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010101-V-0000.bin"
noncomputable def vp0000000000101010101 : Blocks := vp0000000000101010101_0
private theorem bp00000000001010101010 : Branch 0 (-5089764/15625 : ℚ) vp0000000000101010101 := by
  apply branch_left_normalized (c:=vp00000000001010101010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5089764/15625 : ℚ) - ((0:ℤ):ℚ) = (-10179528/15625 : ℚ) by norm_num]
  exact coverp00000000001010101010
private noncomputable def ep00000000001010101011_0 : Blocks := edgeBlocks% "full/vectors/00000000001010101011-E-0000.bin"
noncomputable def ep00000000001010101011 : Blocks := ep00000000001010101011_0
private theorem idp00000000001010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101010101.list =
    C ((2:ℤ)^23) * horner X vp00000000001010101011.list + horner X ep00000000001010101011.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010101011 : Branch 1 (-5089764/15625 : ℚ) vp0000000000101010101 := by
  apply branch_checked idp00000000001010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-5089764/15625 : ℚ) - ((1:ℤ):ℚ) = (-10195153/15625 : ℚ) by norm_num]
  exact coverp00000000001010101011
theorem coverp0000000000101010101 : Covers (-5089764/15625 : ℚ) vp0000000000101010101 := join_branches bp00000000001010101010 bp00000000001010101011
private noncomputable def vp0000000000101010100_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010100-V-0000.bin"
noncomputable def vp0000000000101010100 : Blocks := vp0000000000101010100_0
theorem coverp0000000000101010100 : Covers (-5074139/15625 : ℚ) vp0000000000101010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010101010_0 : Blocks := edgeBlocks% "full/vectors/000000000010101010-V-0000.bin"
noncomputable def vp000000000010101010 : Blocks := vp000000000010101010_0
private theorem bp0000000000101010100 : Branch 0 (-5074139/31250 : ℚ) vp000000000010101010 := by
  apply branch_left_normalized (c:=vp0000000000101010100) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-5074139/31250 : ℚ) - ((0:ℤ):ℚ) = (-5074139/15625 : ℚ) by norm_num]
  exact coverp0000000000101010100
private noncomputable def ep0000000000101010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010101-E-0000.bin"
noncomputable def ep0000000000101010101 : Blocks := ep0000000000101010101_0
private theorem idp0000000000101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010101010.list =
    C ((2:ℤ)^32) * horner X vp0000000000101010101.list + horner X ep0000000000101010101.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101010101 : Branch 1 (-5074139/31250 : ℚ) vp000000000010101010 := by
  apply branch_checked idp0000000000101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-5074139/31250 : ℚ) - ((1:ℤ):ℚ) = (-5089764/15625 : ℚ) by norm_num]
  exact coverp0000000000101010101
theorem coverp000000000010101010 : Covers (-5074139/31250 : ℚ) vp000000000010101010 := join_branches bp0000000000101010100 bp0000000000101010101
private noncomputable def vp00000000001010101_0 : Blocks := edgeBlocks% "full/vectors/00000000001010101-V-0000.bin"
noncomputable def vp00000000001010101 : Blocks := vp00000000001010101_0
private theorem bp000000000010101010 : Branch 0 (-5074139/62500 : ℚ) vp00000000001010101 := by
  apply branch_left_normalized (c:=vp000000000010101010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-5074139/62500 : ℚ) - ((0:ℤ):ℚ) = (-5074139/31250 : ℚ) by norm_num]
  exact coverp000000000010101010
private noncomputable def ep000000000010101011_0 : Blocks := edgeBlocks% "full/vectors/000000000010101011-E-0000.bin"
noncomputable def ep000000000010101011 : Blocks := ep000000000010101011_0
private theorem idp000000000010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001010101.list =
    C ((2:ℤ)^47) * horner X vp000000000010101011.list + horner X ep000000000010101011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010101011 : Branch 1 (-5074139/62500 : ℚ) vp00000000001010101 := by
  apply branch_checked idp000000000010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-5074139/62500 : ℚ) - ((1:ℤ):ℚ) = (-5105389/31250 : ℚ) by norm_num]
  exact coverp000000000010101011
theorem coverp00000000001010101 : Covers (-5074139/62500 : ℚ) vp00000000001010101 := join_branches bp000000000010101010 bp000000000010101011
private noncomputable def vp0000000000101010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010011-V-0000.bin"
noncomputable def vp0000000000101010011 : Blocks := vp0000000000101010011_0
theorem coverp0000000000101010011 : Covers (-5058514/15625 : ℚ) vp0000000000101010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010100101_0 : Blocks := edgeBlocks% "full/vectors/00000000001010100101-V-0000.bin"
noncomputable def vp00000000001010100101 : Blocks := vp00000000001010100101_0
theorem coverp00000000001010100101 : Covers (-10101403/15625 : ℚ) vp00000000001010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010100100_0 : Blocks := edgeBlocks% "full/vectors/00000000001010100100-V-0000.bin"
noncomputable def vp00000000001010100100 : Blocks := vp00000000001010100100_0
theorem coverp00000000001010100100 : Covers (-10085778/15625 : ℚ) vp00000000001010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101010010_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010010-V-0000.bin"
noncomputable def vp0000000000101010010 : Blocks := vp0000000000101010010_0
private theorem bp00000000001010100100 : Branch 0 (-5042889/15625 : ℚ) vp0000000000101010010 := by
  apply branch_left_normalized (c:=vp00000000001010100100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-5042889/15625 : ℚ) - ((0:ℤ):ℚ) = (-10085778/15625 : ℚ) by norm_num]
  exact coverp00000000001010100100
private noncomputable def ep00000000001010100101_0 : Blocks := edgeBlocks% "full/vectors/00000000001010100101-E-0000.bin"
noncomputable def ep00000000001010100101 : Blocks := ep00000000001010100101_0
private theorem idp00000000001010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101010010.list =
    C ((2:ℤ)^23) * horner X vp00000000001010100101.list + horner X ep00000000001010100101.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010100101 : Branch 1 (-5042889/15625 : ℚ) vp0000000000101010010 := by
  apply branch_checked idp00000000001010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-5042889/15625 : ℚ) - ((1:ℤ):ℚ) = (-10101403/15625 : ℚ) by norm_num]
  exact coverp00000000001010100101
theorem coverp0000000000101010010 : Covers (-5042889/15625 : ℚ) vp0000000000101010010 := join_branches bp00000000001010100100 bp00000000001010100101
private noncomputable def vp000000000010101001_0 : Blocks := edgeBlocks% "full/vectors/000000000010101001-V-0000.bin"
noncomputable def vp000000000010101001 : Blocks := vp000000000010101001_0
private theorem bp0000000000101010010 : Branch 0 (-5042889/31250 : ℚ) vp000000000010101001 := by
  apply branch_left_normalized (c:=vp0000000000101010010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-5042889/31250 : ℚ) - ((0:ℤ):ℚ) = (-5042889/15625 : ℚ) by norm_num]
  exact coverp0000000000101010010
private noncomputable def ep0000000000101010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010011-E-0000.bin"
noncomputable def ep0000000000101010011 : Blocks := ep0000000000101010011_0
private theorem idp0000000000101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010101001.list =
    C ((2:ℤ)^31) * horner X vp0000000000101010011.list + horner X ep0000000000101010011.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101010011 : Branch 1 (-5042889/31250 : ℚ) vp000000000010101001 := by
  apply branch_checked idp0000000000101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-5042889/31250 : ℚ) - ((1:ℤ):ℚ) = (-5058514/15625 : ℚ) by norm_num]
  exact coverp0000000000101010011
theorem coverp000000000010101001 : Covers (-5042889/31250 : ℚ) vp000000000010101001 := join_branches bp0000000000101010010 bp0000000000101010011
private noncomputable def vp0000000000101010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010001-V-0000.bin"
noncomputable def vp0000000000101010001 : Blocks := vp0000000000101010001_0
theorem coverp0000000000101010001 : Covers (-5027264/15625 : ℚ) vp0000000000101010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101010000_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010000-V-0000.bin"
noncomputable def vp0000000000101010000 : Blocks := vp0000000000101010000_0
theorem coverp0000000000101010000 : Covers (-5011639/15625 : ℚ) vp0000000000101010000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010101000_0 : Blocks := edgeBlocks% "full/vectors/000000000010101000-V-0000.bin"
noncomputable def vp000000000010101000 : Blocks := vp000000000010101000_0
private theorem bp0000000000101010000 : Branch 0 (-5011639/31250 : ℚ) vp000000000010101000 := by
  apply branch_left_normalized (c:=vp0000000000101010000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-5011639/31250 : ℚ) - ((0:ℤ):ℚ) = (-5011639/15625 : ℚ) by norm_num]
  exact coverp0000000000101010000
private noncomputable def ep0000000000101010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010001-E-0000.bin"
noncomputable def ep0000000000101010001 : Blocks := ep0000000000101010001_0
private theorem idp0000000000101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010101000.list =
    C ((2:ℤ)^32) * horner X vp0000000000101010001.list + horner X ep0000000000101010001.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101010001 : Branch 1 (-5011639/31250 : ℚ) vp000000000010101000 := by
  apply branch_checked idp0000000000101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-5011639/31250 : ℚ) - ((1:ℤ):ℚ) = (-5027264/15625 : ℚ) by norm_num]
  exact coverp0000000000101010001
theorem coverp000000000010101000 : Covers (-5011639/31250 : ℚ) vp000000000010101000 := join_branches bp0000000000101010000 bp0000000000101010001
private noncomputable def vp00000000001010100_0 : Blocks := edgeBlocks% "full/vectors/00000000001010100-V-0000.bin"
noncomputable def vp00000000001010100 : Blocks := vp00000000001010100_0
private theorem bp000000000010101000 : Branch 0 (-5011639/62500 : ℚ) vp00000000001010100 := by
  apply branch_left_normalized (c:=vp000000000010101000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-5011639/62500 : ℚ) - ((0:ℤ):ℚ) = (-5011639/31250 : ℚ) by norm_num]
  exact coverp000000000010101000
private noncomputable def ep000000000010101001_0 : Blocks := edgeBlocks% "full/vectors/000000000010101001-E-0000.bin"
noncomputable def ep000000000010101001 : Blocks := ep000000000010101001_0
private theorem idp000000000010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001010100.list =
    C ((2:ℤ)^48) * horner X vp000000000010101001.list + horner X ep000000000010101001.list := by
  exact edge_identity (B := (2:ℤ)^165) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010101001 : Branch 1 (-5011639/62500 : ℚ) vp00000000001010100 := by
  apply branch_checked idp000000000010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-5011639/62500 : ℚ) - ((1:ℤ):ℚ) = (-5042889/31250 : ℚ) by norm_num]
  exact coverp000000000010101001
theorem coverp00000000001010100 : Covers (-5011639/62500 : ℚ) vp00000000001010100 := join_branches bp000000000010101000 bp000000000010101001
private noncomputable def vp0000000000101010_0 : Blocks := edgeBlocks% "full/vectors/0000000000101010-V-0000.bin"
noncomputable def vp0000000000101010 : Blocks := vp0000000000101010_0
private theorem bp00000000001010100 : Branch 0 (-5011639/125000 : ℚ) vp0000000000101010 := by
  apply branch_left_normalized (c:=vp00000000001010100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-5011639/125000 : ℚ) - ((0:ℤ):ℚ) = (-5011639/62500 : ℚ) by norm_num]
  exact coverp00000000001010100
private noncomputable def ep00000000001010101_0 : Blocks := edgeBlocks% "full/vectors/00000000001010101-E-0000.bin"
noncomputable def ep00000000001010101 : Blocks := ep00000000001010101_0
private theorem idp00000000001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101010.list =
    C ((2:ℤ)^76) * horner X vp00000000001010101.list + horner X ep00000000001010101.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010101 : Branch 1 (-5011639/125000 : ℚ) vp0000000000101010 := by
  apply branch_checked idp00000000001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-5011639/125000 : ℚ) - ((1:ℤ):ℚ) = (-5074139/62500 : ℚ) by norm_num]
  exact coverp00000000001010101
theorem coverp0000000000101010 : Covers (-5011639/125000 : ℚ) vp0000000000101010 := join_branches bp00000000001010100 bp00000000001010101
private noncomputable def vp000000000010101_0 : Blocks := edgeBlocks% "full/vectors/000000000010101-V-0000.bin"
private noncomputable def vp000000000010101_1 : Blocks := edgeBlocks% "full/vectors/000000000010101-V-0001.bin"
noncomputable def vp000000000010101 : Blocks := (Blocks.join vp000000000010101_0 vp000000000010101_1)
private theorem bp0000000000101010 : Branch 0 (-5011639/250000 : ℚ) vp000000000010101 := by
  apply branch_left_normalized (c:=vp0000000000101010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-5011639/250000 : ℚ) - ((0:ℤ):ℚ) = (-5011639/125000 : ℚ) by norm_num]
  exact coverp0000000000101010
private noncomputable def ep0000000000101011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101011-E-0000.bin"
private noncomputable def ep0000000000101011_1 : Blocks := edgeBlocks% "full/vectors/0000000000101011-E-0001.bin"
noncomputable def ep0000000000101011 : Blocks := (Blocks.join ep0000000000101011_0 ep0000000000101011_1)
private theorem idp0000000000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010101.list =
    C ((2:ℤ)^131) * horner X vp0000000000101011.list + horner X ep0000000000101011.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101011 : Branch 1 (-5011639/250000 : ℚ) vp000000000010101 := by
  apply branch_checked idp0000000000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-5011639/250000 : ℚ) - ((1:ℤ):ℚ) = (-5136639/125000 : ℚ) by norm_num]
  exact coverp0000000000101011
theorem coverp000000000010101 : Covers (-5011639/250000 : ℚ) vp000000000010101 := join_branches bp0000000000101010 bp0000000000101011
private noncomputable def vp00000000001010011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001010011111-V-0000.bin"
noncomputable def vp00000000001010011111 : Blocks := vp00000000001010011111_0
theorem coverp00000000001010011111 : Covers (-10007653/15625 : ℚ) vp00000000001010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010011110_0 : Blocks := edgeBlocks% "full/vectors/00000000001010011110-V-0000.bin"
noncomputable def vp00000000001010011110 : Blocks := vp00000000001010011110_0
theorem coverp00000000001010011110 : Covers (-9992028/15625 : ℚ) vp00000000001010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001111-V-0000.bin"
noncomputable def vp0000000000101001111 : Blocks := vp0000000000101001111_0
private theorem bp00000000001010011110 : Branch 0 (-4996014/15625 : ℚ) vp0000000000101001111 := by
  apply branch_left_normalized (c:=vp00000000001010011110) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4996014/15625 : ℚ) - ((0:ℤ):ℚ) = (-9992028/15625 : ℚ) by norm_num]
  exact coverp00000000001010011110
private noncomputable def ep00000000001010011111_0 : Blocks := edgeBlocks% "full/vectors/00000000001010011111-E-0000.bin"
noncomputable def ep00000000001010011111 : Blocks := ep00000000001010011111_0
private theorem idp00000000001010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101001111.list =
    C ((2:ℤ)^23) * horner X vp00000000001010011111.list + horner X ep00000000001010011111.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010011111 : Branch 1 (-4996014/15625 : ℚ) vp0000000000101001111 := by
  apply branch_checked idp00000000001010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-4996014/15625 : ℚ) - ((1:ℤ):ℚ) = (-10007653/15625 : ℚ) by norm_num]
  exact coverp00000000001010011111
theorem coverp0000000000101001111 : Covers (-4996014/15625 : ℚ) vp0000000000101001111 := join_branches bp00000000001010011110 bp00000000001010011111
private noncomputable def vp00000000001010011101_0 : Blocks := edgeBlocks% "full/vectors/00000000001010011101-V-0000.bin"
noncomputable def vp00000000001010011101 : Blocks := vp00000000001010011101_0
theorem coverp00000000001010011101 : Covers (-9976403/15625 : ℚ) vp00000000001010011101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010011100_0 : Blocks := edgeBlocks% "full/vectors/00000000001010011100-V-0000.bin"
noncomputable def vp00000000001010011100 : Blocks := vp00000000001010011100_0
theorem coverp00000000001010011100 : Covers (-9960778/15625 : ℚ) vp00000000001010011100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101001110_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001110-V-0000.bin"
noncomputable def vp0000000000101001110 : Blocks := vp0000000000101001110_0
private theorem bp00000000001010011100 : Branch 0 (-4980389/15625 : ℚ) vp0000000000101001110 := by
  apply branch_left_normalized (c:=vp00000000001010011100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4980389/15625 : ℚ) - ((0:ℤ):ℚ) = (-9960778/15625 : ℚ) by norm_num]
  exact coverp00000000001010011100
private noncomputable def ep00000000001010011101_0 : Blocks := edgeBlocks% "full/vectors/00000000001010011101-E-0000.bin"
noncomputable def ep00000000001010011101 : Blocks := ep00000000001010011101_0
private theorem idp00000000001010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101001110.list =
    C ((2:ℤ)^23) * horner X vp00000000001010011101.list + horner X ep00000000001010011101.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010011101 : Branch 1 (-4980389/15625 : ℚ) vp0000000000101001110 := by
  apply branch_checked idp00000000001010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-4980389/15625 : ℚ) - ((1:ℤ):ℚ) = (-9976403/15625 : ℚ) by norm_num]
  exact coverp00000000001010011101
theorem coverp0000000000101001110 : Covers (-4980389/15625 : ℚ) vp0000000000101001110 := join_branches bp00000000001010011100 bp00000000001010011101
private noncomputable def vp000000000010100111_0 : Blocks := edgeBlocks% "full/vectors/000000000010100111-V-0000.bin"
noncomputable def vp000000000010100111 : Blocks := vp000000000010100111_0
private theorem bp0000000000101001110 : Branch 0 (-4980389/31250 : ℚ) vp000000000010100111 := by
  apply branch_left_normalized (c:=vp0000000000101001110) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4980389/31250 : ℚ) - ((0:ℤ):ℚ) = (-4980389/15625 : ℚ) by norm_num]
  exact coverp0000000000101001110
private noncomputable def ep0000000000101001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001111-E-0000.bin"
noncomputable def ep0000000000101001111 : Blocks := ep0000000000101001111_0
private theorem idp0000000000101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010100111.list =
    C ((2:ℤ)^32) * horner X vp0000000000101001111.list + horner X ep0000000000101001111.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101001111 : Branch 1 (-4980389/31250 : ℚ) vp000000000010100111 := by
  apply branch_checked idp0000000000101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-4980389/31250 : ℚ) - ((1:ℤ):ℚ) = (-4996014/15625 : ℚ) by norm_num]
  exact coverp0000000000101001111
theorem coverp000000000010100111 : Covers (-4980389/31250 : ℚ) vp000000000010100111 := join_branches bp0000000000101001110 bp0000000000101001111
private noncomputable def vp0000000000101001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001101-V-0000.bin"
noncomputable def vp0000000000101001101 : Blocks := vp0000000000101001101_0
theorem coverp0000000000101001101 : Covers (-4964764/15625 : ℚ) vp0000000000101001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101001100_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001100-V-0000.bin"
noncomputable def vp0000000000101001100 : Blocks := vp0000000000101001100_0
theorem coverp0000000000101001100 : Covers (-4949139/15625 : ℚ) vp0000000000101001100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010100110_0 : Blocks := edgeBlocks% "full/vectors/000000000010100110-V-0000.bin"
noncomputable def vp000000000010100110 : Blocks := vp000000000010100110_0
private theorem bp0000000000101001100 : Branch 0 (-4949139/31250 : ℚ) vp000000000010100110 := by
  apply branch_left_normalized (c:=vp0000000000101001100) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4949139/31250 : ℚ) - ((0:ℤ):ℚ) = (-4949139/15625 : ℚ) by norm_num]
  exact coverp0000000000101001100
private noncomputable def ep0000000000101001101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001101-E-0000.bin"
noncomputable def ep0000000000101001101 : Blocks := ep0000000000101001101_0
private theorem idp0000000000101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010100110.list =
    C ((2:ℤ)^32) * horner X vp0000000000101001101.list + horner X ep0000000000101001101.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101001101 : Branch 1 (-4949139/31250 : ℚ) vp000000000010100110 := by
  apply branch_checked idp0000000000101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-4949139/31250 : ℚ) - ((1:ℤ):ℚ) = (-4964764/15625 : ℚ) by norm_num]
  exact coverp0000000000101001101
theorem coverp000000000010100110 : Covers (-4949139/31250 : ℚ) vp000000000010100110 := join_branches bp0000000000101001100 bp0000000000101001101
private noncomputable def vp00000000001010011_0 : Blocks := edgeBlocks% "full/vectors/00000000001010011-V-0000.bin"
noncomputable def vp00000000001010011 : Blocks := vp00000000001010011_0
private theorem bp000000000010100110 : Branch 0 (-4949139/62500 : ℚ) vp00000000001010011 := by
  apply branch_left_normalized (c:=vp000000000010100110) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-4949139/62500 : ℚ) - ((0:ℤ):ℚ) = (-4949139/31250 : ℚ) by norm_num]
  exact coverp000000000010100110
private noncomputable def ep000000000010100111_0 : Blocks := edgeBlocks% "full/vectors/000000000010100111-E-0000.bin"
noncomputable def ep000000000010100111 : Blocks := ep000000000010100111_0
private theorem idp000000000010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001010011.list =
    C ((2:ℤ)^48) * horner X vp000000000010100111.list + horner X ep000000000010100111.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010100111 : Branch 1 (-4949139/62500 : ℚ) vp00000000001010011 := by
  apply branch_checked idp000000000010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-4949139/62500 : ℚ) - ((1:ℤ):ℚ) = (-4980389/31250 : ℚ) by norm_num]
  exact coverp000000000010100111
theorem coverp00000000001010011 : Covers (-4949139/62500 : ℚ) vp00000000001010011 := join_branches bp000000000010100110 bp000000000010100111
private noncomputable def vp00000000001010010111_0 : Blocks := edgeBlocks% "full/vectors/00000000001010010111-V-0000.bin"
noncomputable def vp00000000001010010111 : Blocks := vp00000000001010010111_0
theorem coverp00000000001010010111 : Covers (-9882653/15625 : ℚ) vp00000000001010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010010110_0 : Blocks := edgeBlocks% "full/vectors/00000000001010010110-V-0000.bin"
noncomputable def vp00000000001010010110 : Blocks := vp00000000001010010110_0
theorem coverp00000000001010010110 : Covers (-9867028/15625 : ℚ) vp00000000001010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001011-V-0000.bin"
noncomputable def vp0000000000101001011 : Blocks := vp0000000000101001011_0
private theorem bp00000000001010010110 : Branch 0 (-4933514/15625 : ℚ) vp0000000000101001011 := by
  apply branch_left_normalized (c:=vp00000000001010010110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4933514/15625 : ℚ) - ((0:ℤ):ℚ) = (-9867028/15625 : ℚ) by norm_num]
  exact coverp00000000001010010110
private noncomputable def ep00000000001010010111_0 : Blocks := edgeBlocks% "full/vectors/00000000001010010111-E-0000.bin"
noncomputable def ep00000000001010010111 : Blocks := ep00000000001010010111_0
private theorem idp00000000001010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101001011.list =
    C ((2:ℤ)^22) * horner X vp00000000001010010111.list + horner X ep00000000001010010111.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010010111 : Branch 1 (-4933514/15625 : ℚ) vp0000000000101001011 := by
  apply branch_checked idp00000000001010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-4933514/15625 : ℚ) - ((1:ℤ):ℚ) = (-9882653/15625 : ℚ) by norm_num]
  exact coverp00000000001010010111
theorem coverp0000000000101001011 : Covers (-4933514/15625 : ℚ) vp0000000000101001011 := join_branches bp00000000001010010110 bp00000000001010010111
private noncomputable def vp0000000000101001010_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001010-V-0000.bin"
noncomputable def vp0000000000101001010 : Blocks := vp0000000000101001010_0
theorem coverp0000000000101001010 : Covers (-4917889/15625 : ℚ) vp0000000000101001010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010100101_0 : Blocks := edgeBlocks% "full/vectors/000000000010100101-V-0000.bin"
noncomputable def vp000000000010100101 : Blocks := vp000000000010100101_0
private theorem bp0000000000101001010 : Branch 0 (-4917889/31250 : ℚ) vp000000000010100101 := by
  apply branch_left_normalized (c:=vp0000000000101001010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4917889/31250 : ℚ) - ((0:ℤ):ℚ) = (-4917889/15625 : ℚ) by norm_num]
  exact coverp0000000000101001010
private noncomputable def ep0000000000101001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001011-E-0000.bin"
noncomputable def ep0000000000101001011 : Blocks := ep0000000000101001011_0
private theorem idp0000000000101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010100101.list =
    C ((2:ℤ)^32) * horner X vp0000000000101001011.list + horner X ep0000000000101001011.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101001011 : Branch 1 (-4917889/31250 : ℚ) vp000000000010100101 := by
  apply branch_checked idp0000000000101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4917889/31250 : ℚ) - ((1:ℤ):ℚ) = (-4933514/15625 : ℚ) by norm_num]
  exact coverp0000000000101001011
theorem coverp000000000010100101 : Covers (-4917889/31250 : ℚ) vp000000000010100101 := join_branches bp0000000000101001010 bp0000000000101001011
private noncomputable def vp0000000000101001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001001-V-0000.bin"
noncomputable def vp0000000000101001001 : Blocks := vp0000000000101001001_0
theorem coverp0000000000101001001 : Covers (-4902264/15625 : ℚ) vp0000000000101001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010010001_0 : Blocks := edgeBlocks% "full/vectors/00000000001010010001-V-0000.bin"
noncomputable def vp00000000001010010001 : Blocks := vp00000000001010010001_0
theorem coverp00000000001010010001 : Covers (-9788903/15625 : ℚ) vp00000000001010010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010010000_0 : Blocks := edgeBlocks% "full/vectors/00000000001010010000-V-0000.bin"
noncomputable def vp00000000001010010000 : Blocks := vp00000000001010010000_0
theorem coverp00000000001010010000 : Covers (-9773278/15625 : ℚ) vp00000000001010010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101001000_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001000-V-0000.bin"
noncomputable def vp0000000000101001000 : Blocks := vp0000000000101001000_0
private theorem bp00000000001010010000 : Branch 0 (-4886639/15625 : ℚ) vp0000000000101001000 := by
  apply branch_left_normalized (c:=vp00000000001010010000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4886639/15625 : ℚ) - ((0:ℤ):ℚ) = (-9773278/15625 : ℚ) by norm_num]
  exact coverp00000000001010010000
private noncomputable def ep00000000001010010001_0 : Blocks := edgeBlocks% "full/vectors/00000000001010010001-E-0000.bin"
noncomputable def ep00000000001010010001 : Blocks := ep00000000001010010001_0
private theorem idp00000000001010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101001000.list =
    C ((2:ℤ)^23) * horner X vp00000000001010010001.list + horner X ep00000000001010010001.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010010001 : Branch 1 (-4886639/15625 : ℚ) vp0000000000101001000 := by
  apply branch_checked idp00000000001010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4886639/15625 : ℚ) - ((1:ℤ):ℚ) = (-9788903/15625 : ℚ) by norm_num]
  exact coverp00000000001010010001
theorem coverp0000000000101001000 : Covers (-4886639/15625 : ℚ) vp0000000000101001000 := join_branches bp00000000001010010000 bp00000000001010010001
private noncomputable def vp000000000010100100_0 : Blocks := edgeBlocks% "full/vectors/000000000010100100-V-0000.bin"
noncomputable def vp000000000010100100 : Blocks := vp000000000010100100_0
private theorem bp0000000000101001000 : Branch 0 (-4886639/31250 : ℚ) vp000000000010100100 := by
  apply branch_left_normalized (c:=vp0000000000101001000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4886639/31250 : ℚ) - ((0:ℤ):ℚ) = (-4886639/15625 : ℚ) by norm_num]
  exact coverp0000000000101001000
private noncomputable def ep0000000000101001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001001-E-0000.bin"
noncomputable def ep0000000000101001001 : Blocks := ep0000000000101001001_0
private theorem idp0000000000101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010100100.list =
    C ((2:ℤ)^32) * horner X vp0000000000101001001.list + horner X ep0000000000101001001.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101001001 : Branch 1 (-4886639/31250 : ℚ) vp000000000010100100 := by
  apply branch_checked idp0000000000101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-4886639/31250 : ℚ) - ((1:ℤ):ℚ) = (-4902264/15625 : ℚ) by norm_num]
  exact coverp0000000000101001001
theorem coverp000000000010100100 : Covers (-4886639/31250 : ℚ) vp000000000010100100 := join_branches bp0000000000101001000 bp0000000000101001001
private noncomputable def vp00000000001010010_0 : Blocks := edgeBlocks% "full/vectors/00000000001010010-V-0000.bin"
noncomputable def vp00000000001010010 : Blocks := vp00000000001010010_0
private theorem bp000000000010100100 : Branch 0 (-4886639/62500 : ℚ) vp00000000001010010 := by
  apply branch_left_normalized (c:=vp000000000010100100) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-4886639/62500 : ℚ) - ((0:ℤ):ℚ) = (-4886639/31250 : ℚ) by norm_num]
  exact coverp000000000010100100
private noncomputable def ep000000000010100101_0 : Blocks := edgeBlocks% "full/vectors/000000000010100101-E-0000.bin"
noncomputable def ep000000000010100101 : Blocks := ep000000000010100101_0
private theorem idp000000000010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001010010.list =
    C ((2:ℤ)^48) * horner X vp000000000010100101.list + horner X ep000000000010100101.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010100101 : Branch 1 (-4886639/62500 : ℚ) vp00000000001010010 := by
  apply branch_checked idp000000000010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-4886639/62500 : ℚ) - ((1:ℤ):ℚ) = (-4917889/31250 : ℚ) by norm_num]
  exact coverp000000000010100101
theorem coverp00000000001010010 : Covers (-4886639/62500 : ℚ) vp00000000001010010 := join_branches bp000000000010100100 bp000000000010100101
private noncomputable def vp0000000000101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001-V-0000.bin"
noncomputable def vp0000000000101001 : Blocks := vp0000000000101001_0
private theorem bp00000000001010010 : Branch 0 (-4886639/125000 : ℚ) vp0000000000101001 := by
  apply branch_left_normalized (c:=vp00000000001010010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-4886639/125000 : ℚ) - ((0:ℤ):ℚ) = (-4886639/62500 : ℚ) by norm_num]
  exact coverp00000000001010010
private noncomputable def ep00000000001010011_0 : Blocks := edgeBlocks% "full/vectors/00000000001010011-E-0000.bin"
noncomputable def ep00000000001010011 : Blocks := ep00000000001010011_0
private theorem idp00000000001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101001.list =
    C ((2:ℤ)^77) * horner X vp00000000001010011.list + horner X ep00000000001010011.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010011 : Branch 1 (-4886639/125000 : ℚ) vp0000000000101001 := by
  apply branch_checked idp00000000001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-4886639/125000 : ℚ) - ((1:ℤ):ℚ) = (-4949139/62500 : ℚ) by norm_num]
  exact coverp00000000001010011
theorem coverp0000000000101001 : Covers (-4886639/125000 : ℚ) vp0000000000101001 := join_branches bp00000000001010010 bp00000000001010011
private noncomputable def vp0000000000101000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000111-V-0000.bin"
noncomputable def vp0000000000101000111 : Blocks := vp0000000000101000111_0
theorem coverp0000000000101000111 : Covers (-4871014/15625 : ℚ) vp0000000000101000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101000110_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000110-V-0000.bin"
noncomputable def vp0000000000101000110 : Blocks := vp0000000000101000110_0
theorem coverp0000000000101000110 : Covers (-4855389/15625 : ℚ) vp0000000000101000110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010100011_0 : Blocks := edgeBlocks% "full/vectors/000000000010100011-V-0000.bin"
noncomputable def vp000000000010100011 : Blocks := vp000000000010100011_0
private theorem bp0000000000101000110 : Branch 0 (-4855389/31250 : ℚ) vp000000000010100011 := by
  apply branch_left_normalized (c:=vp0000000000101000110) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4855389/31250 : ℚ) - ((0:ℤ):ℚ) = (-4855389/15625 : ℚ) by norm_num]
  exact coverp0000000000101000110
private noncomputable def ep0000000000101000111_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000111-E-0000.bin"
noncomputable def ep0000000000101000111 : Blocks := ep0000000000101000111_0
private theorem idp0000000000101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010100011.list =
    C ((2:ℤ)^32) * horner X vp0000000000101000111.list + horner X ep0000000000101000111.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101000111 : Branch 1 (-4855389/31250 : ℚ) vp000000000010100011 := by
  apply branch_checked idp0000000000101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4855389/31250 : ℚ) - ((1:ℤ):ℚ) = (-4871014/15625 : ℚ) by norm_num]
  exact coverp0000000000101000111
theorem coverp000000000010100011 : Covers (-4855389/31250 : ℚ) vp000000000010100011 := join_branches bp0000000000101000110 bp0000000000101000111
private noncomputable def vp00000000001010001011_0 : Blocks := edgeBlocks% "full/vectors/00000000001010001011-V-0000.bin"
noncomputable def vp00000000001010001011 : Blocks := vp00000000001010001011_0
theorem coverp00000000001010001011 : Covers (-9695153/15625 : ℚ) vp00000000001010001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010001010_0 : Blocks := edgeBlocks% "full/vectors/00000000001010001010-V-0000.bin"
noncomputable def vp00000000001010001010 : Blocks := vp00000000001010001010_0
theorem coverp00000000001010001010 : Covers (-9679528/15625 : ℚ) vp00000000001010001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000101-V-0000.bin"
noncomputable def vp0000000000101000101 : Blocks := vp0000000000101000101_0
private theorem bp00000000001010001010 : Branch 0 (-4839764/15625 : ℚ) vp0000000000101000101 := by
  apply branch_left_normalized (c:=vp00000000001010001010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4839764/15625 : ℚ) - ((0:ℤ):ℚ) = (-9679528/15625 : ℚ) by norm_num]
  exact coverp00000000001010001010
private noncomputable def ep00000000001010001011_0 : Blocks := edgeBlocks% "full/vectors/00000000001010001011-E-0000.bin"
noncomputable def ep00000000001010001011 : Blocks := ep00000000001010001011_0
private theorem idp00000000001010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101000101.list =
    C ((2:ℤ)^23) * horner X vp00000000001010001011.list + horner X ep00000000001010001011.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010001011 : Branch 1 (-4839764/15625 : ℚ) vp0000000000101000101 := by
  apply branch_checked idp00000000001010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4839764/15625 : ℚ) - ((1:ℤ):ℚ) = (-9695153/15625 : ℚ) by norm_num]
  exact coverp00000000001010001011
theorem coverp0000000000101000101 : Covers (-4839764/15625 : ℚ) vp0000000000101000101 := join_branches bp00000000001010001010 bp00000000001010001011
private noncomputable def vp0000000000101000100_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000100-V-0000.bin"
noncomputable def vp0000000000101000100 : Blocks := vp0000000000101000100_0
theorem coverp0000000000101000100 : Covers (-4824139/15625 : ℚ) vp0000000000101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010100010_0 : Blocks := edgeBlocks% "full/vectors/000000000010100010-V-0000.bin"
noncomputable def vp000000000010100010 : Blocks := vp000000000010100010_0
private theorem bp0000000000101000100 : Branch 0 (-4824139/31250 : ℚ) vp000000000010100010 := by
  apply branch_left_normalized (c:=vp0000000000101000100) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4824139/31250 : ℚ) - ((0:ℤ):ℚ) = (-4824139/15625 : ℚ) by norm_num]
  exact coverp0000000000101000100
private noncomputable def ep0000000000101000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000101-E-0000.bin"
noncomputable def ep0000000000101000101 : Blocks := ep0000000000101000101_0
private theorem idp0000000000101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010100010.list =
    C ((2:ℤ)^32) * horner X vp0000000000101000101.list + horner X ep0000000000101000101.list := by
  exact edge_identity (B := (2:ℤ)^142) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101000101 : Branch 1 (-4824139/31250 : ℚ) vp000000000010100010 := by
  apply branch_checked idp0000000000101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4824139/31250 : ℚ) - ((1:ℤ):ℚ) = (-4839764/15625 : ℚ) by norm_num]
  exact coverp0000000000101000101
theorem coverp000000000010100010 : Covers (-4824139/31250 : ℚ) vp000000000010100010 := join_branches bp0000000000101000100 bp0000000000101000101
private noncomputable def vp00000000001010001_0 : Blocks := edgeBlocks% "full/vectors/00000000001010001-V-0000.bin"
noncomputable def vp00000000001010001 : Blocks := vp00000000001010001_0
private theorem bp000000000010100010 : Branch 0 (-4824139/62500 : ℚ) vp00000000001010001 := by
  apply branch_left_normalized (c:=vp000000000010100010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-4824139/62500 : ℚ) - ((0:ℤ):ℚ) = (-4824139/31250 : ℚ) by norm_num]
  exact coverp000000000010100010
private noncomputable def ep000000000010100011_0 : Blocks := edgeBlocks% "full/vectors/000000000010100011-E-0000.bin"
noncomputable def ep000000000010100011 : Blocks := ep000000000010100011_0
private theorem idp000000000010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001010001.list =
    C ((2:ℤ)^48) * horner X vp000000000010100011.list + horner X ep000000000010100011.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010100011 : Branch 1 (-4824139/62500 : ℚ) vp00000000001010001 := by
  apply branch_checked idp000000000010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-4824139/62500 : ℚ) - ((1:ℤ):ℚ) = (-4855389/31250 : ℚ) by norm_num]
  exact coverp000000000010100011
theorem coverp00000000001010001 : Covers (-4824139/62500 : ℚ) vp00000000001010001 := join_branches bp000000000010100010 bp000000000010100011
private noncomputable def vp00000000001010000111_0 : Blocks := edgeBlocks% "full/vectors/00000000001010000111-V-0000.bin"
noncomputable def vp00000000001010000111 : Blocks := vp00000000001010000111_0
theorem coverp00000000001010000111 : Covers (-9632653/15625 : ℚ) vp00000000001010000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010000110_0 : Blocks := edgeBlocks% "full/vectors/00000000001010000110-V-0000.bin"
noncomputable def vp00000000001010000110 : Blocks := vp00000000001010000110_0
theorem coverp00000000001010000110 : Covers (-9617028/15625 : ℚ) vp00000000001010000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000011-V-0000.bin"
noncomputable def vp0000000000101000011 : Blocks := vp0000000000101000011_0
private theorem bp00000000001010000110 : Branch 0 (-4808514/15625 : ℚ) vp0000000000101000011 := by
  apply branch_left_normalized (c:=vp00000000001010000110) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-4808514/15625 : ℚ) - ((0:ℤ):ℚ) = (-9617028/15625 : ℚ) by norm_num]
  exact coverp00000000001010000110
private noncomputable def ep00000000001010000111_0 : Blocks := edgeBlocks% "full/vectors/00000000001010000111-E-0000.bin"
noncomputable def ep00000000001010000111 : Blocks := ep00000000001010000111_0
private theorem idp00000000001010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101000011.list =
    C ((2:ℤ)^23) * horner X vp00000000001010000111.list + horner X ep00000000001010000111.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010000111 : Branch 1 (-4808514/15625 : ℚ) vp0000000000101000011 := by
  apply branch_checked idp00000000001010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-4808514/15625 : ℚ) - ((1:ℤ):ℚ) = (-9632653/15625 : ℚ) by norm_num]
  exact coverp00000000001010000111
theorem coverp0000000000101000011 : Covers (-4808514/15625 : ℚ) vp0000000000101000011 := join_branches bp00000000001010000110 bp00000000001010000111
private noncomputable def vp00000000001010000101_0 : Blocks := edgeBlocks% "full/vectors/00000000001010000101-V-0000.bin"
noncomputable def vp00000000001010000101 : Blocks := vp00000000001010000101_0
theorem coverp00000000001010000101 : Covers (-9601403/15625 : ℚ) vp00000000001010000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000001010000100_0 : Blocks := edgeBlocks% "full/vectors/00000000001010000100-V-0000.bin"
noncomputable def vp00000000001010000100 : Blocks := vp00000000001010000100_0
theorem coverp00000000001010000100 : Covers (-9585778/15625 : ℚ) vp00000000001010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101000010_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000010-V-0000.bin"
noncomputable def vp0000000000101000010 : Blocks := vp0000000000101000010_0
private theorem bp00000000001010000100 : Branch 0 (-4792889/15625 : ℚ) vp0000000000101000010 := by
  apply branch_left_normalized (c:=vp00000000001010000100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-4792889/15625 : ℚ) - ((0:ℤ):ℚ) = (-9585778/15625 : ℚ) by norm_num]
  exact coverp00000000001010000100
private noncomputable def ep00000000001010000101_0 : Blocks := edgeBlocks% "full/vectors/00000000001010000101-E-0000.bin"
noncomputable def ep00000000001010000101 : Blocks := ep00000000001010000101_0
private theorem idp00000000001010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101000010.list =
    C ((2:ℤ)^23) * horner X vp00000000001010000101.list + horner X ep00000000001010000101.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010000101 : Branch 1 (-4792889/15625 : ℚ) vp0000000000101000010 := by
  apply branch_checked idp00000000001010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-4792889/15625 : ℚ) - ((1:ℤ):ℚ) = (-9601403/15625 : ℚ) by norm_num]
  exact coverp00000000001010000101
theorem coverp0000000000101000010 : Covers (-4792889/15625 : ℚ) vp0000000000101000010 := join_branches bp00000000001010000100 bp00000000001010000101
private noncomputable def vp000000000010100001_0 : Blocks := edgeBlocks% "full/vectors/000000000010100001-V-0000.bin"
noncomputable def vp000000000010100001 : Blocks := vp000000000010100001_0
private theorem bp0000000000101000010 : Branch 0 (-4792889/31250 : ℚ) vp000000000010100001 := by
  apply branch_left_normalized (c:=vp0000000000101000010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4792889/31250 : ℚ) - ((0:ℤ):ℚ) = (-4792889/15625 : ℚ) by norm_num]
  exact coverp0000000000101000010
private noncomputable def ep0000000000101000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000011-E-0000.bin"
noncomputable def ep0000000000101000011 : Blocks := ep0000000000101000011_0
private theorem idp0000000000101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010100001.list =
    C ((2:ℤ)^32) * horner X vp0000000000101000011.list + horner X ep0000000000101000011.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101000011 : Branch 1 (-4792889/31250 : ℚ) vp000000000010100001 := by
  apply branch_checked idp0000000000101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-4792889/31250 : ℚ) - ((1:ℤ):ℚ) = (-4808514/15625 : ℚ) by norm_num]
  exact coverp0000000000101000011
theorem coverp000000000010100001 : Covers (-4792889/31250 : ℚ) vp000000000010100001 := join_branches bp0000000000101000010 bp0000000000101000011
private noncomputable def vp0000000000101000001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000001-V-0000.bin"
noncomputable def vp0000000000101000001 : Blocks := vp0000000000101000001_0
theorem coverp0000000000101000001 : Covers (-4777264/15625 : ℚ) vp0000000000101000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000101000000_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000000-V-0000.bin"
noncomputable def vp0000000000101000000 : Blocks := vp0000000000101000000_0
theorem coverp0000000000101000000 : Covers (-4761639/15625 : ℚ) vp0000000000101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000010100000_0 : Blocks := edgeBlocks% "full/vectors/000000000010100000-V-0000.bin"
noncomputable def vp000000000010100000 : Blocks := vp000000000010100000_0
private theorem bp0000000000101000000 : Branch 0 (-4761639/31250 : ℚ) vp000000000010100000 := by
  apply branch_left_normalized (c:=vp0000000000101000000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-4761639/31250 : ℚ) - ((0:ℤ):ℚ) = (-4761639/15625 : ℚ) by norm_num]
  exact coverp0000000000101000000
private noncomputable def ep0000000000101000001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000001-E-0000.bin"
noncomputable def ep0000000000101000001 : Blocks := ep0000000000101000001_0
private theorem idp0000000000101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010100000.list =
    C ((2:ℤ)^32) * horner X vp0000000000101000001.list + horner X ep0000000000101000001.list := by
  exact edge_identity (B := (2:ℤ)^143) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101000001 : Branch 1 (-4761639/31250 : ℚ) vp000000000010100000 := by
  apply branch_checked idp0000000000101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-4761639/31250 : ℚ) - ((1:ℤ):ℚ) = (-4777264/15625 : ℚ) by norm_num]
  exact coverp0000000000101000001
theorem coverp000000000010100000 : Covers (-4761639/31250 : ℚ) vp000000000010100000 := join_branches bp0000000000101000000 bp0000000000101000001
private noncomputable def vp00000000001010000_0 : Blocks := edgeBlocks% "full/vectors/00000000001010000-V-0000.bin"
noncomputable def vp00000000001010000 : Blocks := vp00000000001010000_0
private theorem bp000000000010100000 : Branch 0 (-4761639/62500 : ℚ) vp00000000001010000 := by
  apply branch_left_normalized (c:=vp000000000010100000) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-4761639/62500 : ℚ) - ((0:ℤ):ℚ) = (-4761639/31250 : ℚ) by norm_num]
  exact coverp000000000010100000
private noncomputable def ep000000000010100001_0 : Blocks := edgeBlocks% "full/vectors/000000000010100001-E-0000.bin"
noncomputable def ep000000000010100001 : Blocks := ep000000000010100001_0
private theorem idp000000000010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001010000.list =
    C ((2:ℤ)^48) * horner X vp000000000010100001.list + horner X ep000000000010100001.list := by
  exact edge_identity (B := (2:ℤ)^164) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010100001 : Branch 1 (-4761639/62500 : ℚ) vp00000000001010000 := by
  apply branch_checked idp000000000010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-4761639/62500 : ℚ) - ((1:ℤ):ℚ) = (-4792889/31250 : ℚ) by norm_num]
  exact coverp000000000010100001
theorem coverp00000000001010000 : Covers (-4761639/62500 : ℚ) vp00000000001010000 := join_branches bp000000000010100000 bp000000000010100001
private noncomputable def vp0000000000101000_0 : Blocks := edgeBlocks% "full/vectors/0000000000101000-V-0000.bin"
noncomputable def vp0000000000101000 : Blocks := vp0000000000101000_0
private theorem bp00000000001010000 : Branch 0 (-4761639/125000 : ℚ) vp0000000000101000 := by
  apply branch_left_normalized (c:=vp00000000001010000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-4761639/125000 : ℚ) - ((0:ℤ):ℚ) = (-4761639/62500 : ℚ) by norm_num]
  exact coverp00000000001010000
private noncomputable def ep00000000001010001_0 : Blocks := edgeBlocks% "full/vectors/00000000001010001-E-0000.bin"
noncomputable def ep00000000001010001 : Blocks := ep00000000001010001_0
private theorem idp00000000001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101000.list =
    C ((2:ℤ)^78) * horner X vp00000000001010001.list + horner X ep00000000001010001.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001010001 : Branch 1 (-4761639/125000 : ℚ) vp0000000000101000 := by
  apply branch_checked idp00000000001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-4761639/125000 : ℚ) - ((1:ℤ):ℚ) = (-4824139/62500 : ℚ) by norm_num]
  exact coverp00000000001010001
theorem coverp0000000000101000 : Covers (-4761639/125000 : ℚ) vp0000000000101000 := join_branches bp00000000001010000 bp00000000001010001
private noncomputable def vp000000000010100_0 : Blocks := edgeBlocks% "full/vectors/000000000010100-V-0000.bin"
private noncomputable def vp000000000010100_1 : Blocks := edgeBlocks% "full/vectors/000000000010100-V-0001.bin"
noncomputable def vp000000000010100 : Blocks := (Blocks.join vp000000000010100_0 vp000000000010100_1)
private theorem bp0000000000101000 : Branch 0 (-4761639/250000 : ℚ) vp000000000010100 := by
  apply branch_left_normalized (c:=vp0000000000101000) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-4761639/250000 : ℚ) - ((0:ℤ):ℚ) = (-4761639/125000 : ℚ) by norm_num]
  exact coverp0000000000101000
private noncomputable def ep0000000000101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000101001-E-0000.bin"
private noncomputable def ep0000000000101001_1 : Blocks := edgeBlocks% "full/vectors/0000000000101001-E-0001.bin"
noncomputable def ep0000000000101001 : Blocks := (Blocks.join ep0000000000101001_0 ep0000000000101001_1)
private theorem idp0000000000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000010100.list =
    C ((2:ℤ)^134) * horner X vp0000000000101001.list + horner X ep0000000000101001.list := by
  exact edge_identity (B := (2:ℤ)^291) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000101001 : Branch 1 (-4761639/250000 : ℚ) vp000000000010100 := by
  apply branch_checked idp0000000000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-4761639/250000 : ℚ) - ((1:ℤ):ℚ) = (-4886639/125000 : ℚ) by norm_num]
  exact coverp0000000000101001
theorem coverp000000000010100 : Covers (-4761639/250000 : ℚ) vp000000000010100 := join_branches bp0000000000101000 bp0000000000101001
private noncomputable def vp00000000001010_0 : Blocks := edgeBlocks% "full/vectors/00000000001010-V-0000.bin"
private noncomputable def vp00000000001010_1 : Blocks := edgeBlocks% "full/vectors/00000000001010-V-0001.bin"
noncomputable def vp00000000001010 : Blocks := (Blocks.join vp00000000001010_0 vp00000000001010_1)
private theorem bp000000000010100 : Branch 0 (-4761639/500000 : ℚ) vp00000000001010 := by
  apply branch_left_normalized (c:=vp000000000010100) (k:=0) (m:=133) (by decide +kernel)
  rw [show 2*(-4761639/500000 : ℚ) - ((0:ℤ):ℚ) = (-4761639/250000 : ℚ) by norm_num]
  exact coverp000000000010100
private noncomputable def ep000000000010101_0 : Blocks := edgeBlocks% "full/vectors/000000000010101-E-0000.bin"
private noncomputable def ep000000000010101_1 : Blocks := edgeBlocks% "full/vectors/000000000010101-E-0001.bin"
noncomputable def ep000000000010101 : Blocks := (Blocks.join ep000000000010101_0 ep000000000010101_1)
private theorem idp000000000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000001010.list =
    C ((2:ℤ)^244) * horner X vp000000000010101.list + horner X ep000000000010101.list := by
  exact edge_identity (B := (2:ℤ)^460) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000010101 : Branch 1 (-4761639/500000 : ℚ) vp00000000001010 := by
  apply branch_checked idp000000000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-4761639/500000 : ℚ) - ((1:ℤ):ℚ) = (-5011639/250000 : ℚ) by norm_num]
  exact coverp000000000010101
theorem coverp00000000001010 : Covers (-4761639/500000 : ℚ) vp00000000001010 := join_branches bp000000000010100 bp000000000010101
private noncomputable def vp0000000000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000101-V-0000.bin"
private noncomputable def vp0000000000101_1 : Blocks := edgeBlocks% "full/vectors/0000000000101-V-0001.bin"
private noncomputable def vp0000000000101_2 : Blocks := edgeBlocks% "full/vectors/0000000000101-V-0002.bin"
private noncomputable def vp0000000000101_3 : Blocks := edgeBlocks% "full/vectors/0000000000101-V-0003.bin"
noncomputable def vp0000000000101 : Blocks := (Blocks.join (Blocks.join vp0000000000101_0 vp0000000000101_1) (Blocks.join vp0000000000101_2 vp0000000000101_3))
private theorem bp00000000001010 : Branch 0 (-4761639/1000000 : ℚ) vp0000000000101 := by
  apply branch_left_normalized (c:=vp00000000001010) (k:=0) (m:=243) (by decide +kernel)
  rw [show 2*(-4761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-4761639/500000 : ℚ) by norm_num]
  exact coverp00000000001010
private noncomputable def ep00000000001011_0 : Blocks := edgeBlocks% "full/vectors/00000000001011-E-0000.bin"
private noncomputable def ep00000000001011_1 : Blocks := edgeBlocks% "full/vectors/00000000001011-E-0001.bin"
private noncomputable def ep00000000001011_2 : Blocks := edgeBlocks% "full/vectors/00000000001011-E-0002.bin"
private noncomputable def ep00000000001011_3 : Blocks := edgeBlocks% "full/vectors/00000000001011-E-0003.bin"
noncomputable def ep00000000001011 : Blocks := (Blocks.join (Blocks.join ep00000000001011_0 ep00000000001011_1) (Blocks.join ep00000000001011_2 ep00000000001011_3))
private theorem idp00000000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000101.list =
    C ((2:ℤ)^510) * horner X vp00000000001011.list + horner X ep00000000001011.list := by
  exact edge_identity (B := (2:ℤ)^842) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000001011 : Branch 1 (-4761639/1000000 : ℚ) vp0000000000101 := by
  apply branch_checked idp00000000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-4761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-5261639/500000 : ℚ) by norm_num]
  exact coverp00000000001011
theorem coverp0000000000101 : Covers (-4761639/1000000 : ℚ) vp0000000000101 := join_branches bp00000000001010 bp00000000001011
end NextProof.EdgeFull

