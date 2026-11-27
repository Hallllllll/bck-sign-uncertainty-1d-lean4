import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00001

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp000000000000001011111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011111-V-0000.bin"
noncomputable def vp000000000000001011111 : Blocks := vp000000000000001011111_0
theorem coverp000000000000001011111 : Covers (-530931/15625 : ℚ) vp000000000000001011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010111101-V-0000.bin"
noncomputable def vp0000000000000010111101 : Blocks := vp0000000000000010111101_0
theorem coverp0000000000000010111101 : Covers (-1046237/15625 : ℚ) vp0000000000000010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101111001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101111001-V-0000.bin"
noncomputable def vp00000000000000101111001 : Blocks := vp00000000000000101111001_0
theorem coverp00000000000000101111001 : Covers (-2076849/15625 : ℚ) vp00000000000000101111001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101111000_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101111000-V-0000.bin"
noncomputable def vp00000000000000101111000 : Blocks := vp00000000000000101111000_0
theorem coverp00000000000000101111000 : Covers (-2061224/15625 : ℚ) vp00000000000000101111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010111100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010111100-V-0000.bin"
noncomputable def vp0000000000000010111100 : Blocks := vp0000000000000010111100_0
private theorem bp00000000000000101111000 : Branch 0 (-1030612/15625 : ℚ) vp0000000000000010111100 := by
  apply branch_left_normalized (c:=vp00000000000000101111000) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-1030612/15625 : ℚ) - ((0:ℤ):ℚ) = (-2061224/15625 : ℚ) by norm_num]
  exact coverp00000000000000101111000
private noncomputable def ep00000000000000101111001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101111001-E-0000.bin"
noncomputable def ep00000000000000101111001 : Blocks := ep00000000000000101111001_0
private theorem idp00000000000000101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010111100.list =
    C ((2:ℤ)^17) * horner X vp00000000000000101111001.list + horner X ep00000000000000101111001.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101111001 : Branch 1 (-1030612/15625 : ℚ) vp0000000000000010111100 := by
  apply branch_checked idp00000000000000101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1030612/15625 : ℚ) - ((1:ℤ):ℚ) = (-2076849/15625 : ℚ) by norm_num]
  exact coverp00000000000000101111001
theorem coverp0000000000000010111100 : Covers (-1030612/15625 : ℚ) vp0000000000000010111100 := join_branches bp00000000000000101111000 bp00000000000000101111001
private noncomputable def vp000000000000001011110_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011110-V-0000.bin"
noncomputable def vp000000000000001011110 : Blocks := vp000000000000001011110_0
private theorem bp0000000000000010111100 : Branch 0 (-515306/15625 : ℚ) vp000000000000001011110 := by
  apply branch_left_normalized (c:=vp0000000000000010111100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-515306/15625 : ℚ) - ((0:ℤ):ℚ) = (-1030612/15625 : ℚ) by norm_num]
  exact coverp0000000000000010111100
private noncomputable def ep0000000000000010111101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010111101-E-0000.bin"
noncomputable def ep0000000000000010111101 : Blocks := ep0000000000000010111101_0
private theorem idp0000000000000010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001011110.list =
    C ((2:ℤ)^22) * horner X vp0000000000000010111101.list + horner X ep0000000000000010111101.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010111101 : Branch 1 (-515306/15625 : ℚ) vp000000000000001011110 := by
  apply branch_checked idp0000000000000010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-515306/15625 : ℚ) - ((1:ℤ):ℚ) = (-1046237/15625 : ℚ) by norm_num]
  exact coverp0000000000000010111101
theorem coverp000000000000001011110 : Covers (-515306/15625 : ℚ) vp000000000000001011110 := join_branches bp0000000000000010111100 bp0000000000000010111101
private noncomputable def vp00000000000000101111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101111-V-0000.bin"
noncomputable def vp00000000000000101111 : Blocks := vp00000000000000101111_0
private theorem bp000000000000001011110 : Branch 0 (-257653/15625 : ℚ) vp00000000000000101111 := by
  apply branch_left_normalized (c:=vp000000000000001011110) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-257653/15625 : ℚ) - ((0:ℤ):ℚ) = (-515306/15625 : ℚ) by norm_num]
  exact coverp000000000000001011110
private noncomputable def ep000000000000001011111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011111-E-0000.bin"
noncomputable def ep000000000000001011111 : Blocks := ep000000000000001011111_0
private theorem idp000000000000001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000101111.list =
    C ((2:ℤ)^31) * horner X vp000000000000001011111.list + horner X ep000000000000001011111.list := by
  exact edge_identity (B := (2:ℤ)^127) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001011111 : Branch 1 (-257653/15625 : ℚ) vp00000000000000101111 := by
  apply branch_checked idp000000000000001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-257653/15625 : ℚ) - ((1:ℤ):ℚ) = (-530931/15625 : ℚ) by norm_num]
  exact coverp000000000000001011111
theorem coverp00000000000000101111 : Covers (-257653/15625 : ℚ) vp00000000000000101111 := join_branches bp000000000000001011110 bp000000000000001011111
private noncomputable def vp0000000000000010111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010111011-V-0000.bin"
noncomputable def vp0000000000000010111011 : Blocks := vp0000000000000010111011_0
theorem coverp0000000000000010111011 : Covers (-1014987/15625 : ℚ) vp0000000000000010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010111010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010111010-V-0000.bin"
noncomputable def vp0000000000000010111010 : Blocks := vp0000000000000010111010_0
theorem coverp0000000000000010111010 : Covers (-999362/15625 : ℚ) vp0000000000000010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001011101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011101-V-0000.bin"
noncomputable def vp000000000000001011101 : Blocks := vp000000000000001011101_0
private theorem bp0000000000000010111010 : Branch 0 (-499681/15625 : ℚ) vp000000000000001011101 := by
  apply branch_left_normalized (c:=vp0000000000000010111010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-499681/15625 : ℚ) - ((0:ℤ):ℚ) = (-999362/15625 : ℚ) by norm_num]
  exact coverp0000000000000010111010
private noncomputable def ep0000000000000010111011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010111011-E-0000.bin"
noncomputable def ep0000000000000010111011 : Blocks := ep0000000000000010111011_0
private theorem idp0000000000000010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001011101.list =
    C ((2:ℤ)^22) * horner X vp0000000000000010111011.list + horner X ep0000000000000010111011.list := by
  exact edge_identity (B := (2:ℤ)^116) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010111011 : Branch 1 (-499681/15625 : ℚ) vp000000000000001011101 := by
  apply branch_checked idp0000000000000010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-499681/15625 : ℚ) - ((1:ℤ):ℚ) = (-1014987/15625 : ℚ) by norm_num]
  exact coverp0000000000000010111011
theorem coverp000000000000001011101 : Covers (-499681/15625 : ℚ) vp000000000000001011101 := join_branches bp0000000000000010111010 bp0000000000000010111011
private noncomputable def vp000000000000001011100_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011100-V-0000.bin"
noncomputable def vp000000000000001011100 : Blocks := vp000000000000001011100_0
theorem coverp000000000000001011100 : Covers (-484056/15625 : ℚ) vp000000000000001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101110_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101110-V-0000.bin"
noncomputable def vp00000000000000101110 : Blocks := vp00000000000000101110_0
private theorem bp000000000000001011100 : Branch 0 (-242028/15625 : ℚ) vp00000000000000101110 := by
  apply branch_left_normalized (c:=vp000000000000001011100) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-242028/15625 : ℚ) - ((0:ℤ):ℚ) = (-484056/15625 : ℚ) by norm_num]
  exact coverp000000000000001011100
private noncomputable def ep000000000000001011101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011101-E-0000.bin"
noncomputable def ep000000000000001011101 : Blocks := ep000000000000001011101_0
private theorem idp000000000000001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000101110.list =
    C ((2:ℤ)^31) * horner X vp000000000000001011101.list + horner X ep000000000000001011101.list := by
  exact edge_identity (B := (2:ℤ)^127) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001011101 : Branch 1 (-242028/15625 : ℚ) vp00000000000000101110 := by
  apply branch_checked idp000000000000001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-242028/15625 : ℚ) - ((1:ℤ):ℚ) = (-499681/15625 : ℚ) by norm_num]
  exact coverp000000000000001011101
theorem coverp00000000000000101110 : Covers (-242028/15625 : ℚ) vp00000000000000101110 := join_branches bp000000000000001011100 bp000000000000001011101
private noncomputable def vp0000000000000010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010111-V-0000.bin"
noncomputable def vp0000000000000010111 : Blocks := vp0000000000000010111_0
private theorem bp00000000000000101110 : Branch 0 (-121014/15625 : ℚ) vp0000000000000010111 := by
  apply branch_left_normalized (c:=vp00000000000000101110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-121014/15625 : ℚ) - ((0:ℤ):ℚ) = (-242028/15625 : ℚ) by norm_num]
  exact coverp00000000000000101110
private noncomputable def ep00000000000000101111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101111-E-0000.bin"
noncomputable def ep00000000000000101111 : Blocks := ep00000000000000101111_0
private theorem idp00000000000000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010111.list =
    C ((2:ℤ)^46) * horner X vp00000000000000101111.list + horner X ep00000000000000101111.list := by
  exact edge_identity (B := (2:ℤ)^147) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101111 : Branch 1 (-121014/15625 : ℚ) vp0000000000000010111 := by
  apply branch_checked idp00000000000000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-121014/15625 : ℚ) - ((1:ℤ):ℚ) = (-257653/15625 : ℚ) by norm_num]
  exact coverp00000000000000101111
theorem coverp0000000000000010111 : Covers (-121014/15625 : ℚ) vp0000000000000010111 := join_branches bp00000000000000101110 bp00000000000000101111
private noncomputable def vp0000000000000010110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010110111-V-0000.bin"
noncomputable def vp0000000000000010110111 : Blocks := vp0000000000000010110111_0
theorem coverp0000000000000010110111 : Covers (-952487/15625 : ℚ) vp0000000000000010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101101101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101101101-V-0000.bin"
noncomputable def vp00000000000000101101101 : Blocks := vp00000000000000101101101_0
theorem coverp00000000000000101101101 : Covers (-1889349/15625 : ℚ) vp00000000000000101101101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101101100_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101101100-V-0000.bin"
noncomputable def vp00000000000000101101100 : Blocks := vp00000000000000101101100_0
theorem coverp00000000000000101101100 : Covers (-1873724/15625 : ℚ) vp00000000000000101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010110110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010110110-V-0000.bin"
noncomputable def vp0000000000000010110110 : Blocks := vp0000000000000010110110_0
private theorem bp00000000000000101101100 : Branch 0 (-936862/15625 : ℚ) vp0000000000000010110110 := by
  apply branch_left_normalized (c:=vp00000000000000101101100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-936862/15625 : ℚ) - ((0:ℤ):ℚ) = (-1873724/15625 : ℚ) by norm_num]
  exact coverp00000000000000101101100
private noncomputable def ep00000000000000101101101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101101101-E-0000.bin"
noncomputable def ep00000000000000101101101 : Blocks := ep00000000000000101101101_0
private theorem idp00000000000000101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010110110.list =
    C ((2:ℤ)^17) * horner X vp00000000000000101101101.list + horner X ep00000000000000101101101.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101101101 : Branch 1 (-936862/15625 : ℚ) vp0000000000000010110110 := by
  apply branch_checked idp00000000000000101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-936862/15625 : ℚ) - ((1:ℤ):ℚ) = (-1889349/15625 : ℚ) by norm_num]
  exact coverp00000000000000101101101
theorem coverp0000000000000010110110 : Covers (-936862/15625 : ℚ) vp0000000000000010110110 := join_branches bp00000000000000101101100 bp00000000000000101101101
private noncomputable def vp000000000000001011011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011011-V-0000.bin"
noncomputable def vp000000000000001011011 : Blocks := vp000000000000001011011_0
private theorem bp0000000000000010110110 : Branch 0 (-468431/15625 : ℚ) vp000000000000001011011 := by
  apply branch_left_normalized (c:=vp0000000000000010110110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-468431/15625 : ℚ) - ((0:ℤ):ℚ) = (-936862/15625 : ℚ) by norm_num]
  exact coverp0000000000000010110110
private noncomputable def ep0000000000000010110111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010110111-E-0000.bin"
noncomputable def ep0000000000000010110111 : Blocks := ep0000000000000010110111_0
private theorem idp0000000000000010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001011011.list =
    C ((2:ℤ)^23) * horner X vp0000000000000010110111.list + horner X ep0000000000000010110111.list := by
  exact edge_identity (B := (2:ℤ)^116) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010110111 : Branch 1 (-468431/15625 : ℚ) vp000000000000001011011 := by
  apply branch_checked idp0000000000000010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-468431/15625 : ℚ) - ((1:ℤ):ℚ) = (-952487/15625 : ℚ) by norm_num]
  exact coverp0000000000000010110111
theorem coverp000000000000001011011 : Covers (-468431/15625 : ℚ) vp000000000000001011011 := join_branches bp0000000000000010110110 bp0000000000000010110111
private noncomputable def vp00000000000000101101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101101011-V-0000.bin"
noncomputable def vp00000000000000101101011 : Blocks := vp00000000000000101101011_0
theorem coverp00000000000000101101011 : Covers (-1858099/15625 : ℚ) vp00000000000000101101011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101101010_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101101010-V-0000.bin"
noncomputable def vp00000000000000101101010 : Blocks := vp00000000000000101101010_0
theorem coverp00000000000000101101010 : Covers (-1842474/15625 : ℚ) vp00000000000000101101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010110101-V-0000.bin"
noncomputable def vp0000000000000010110101 : Blocks := vp0000000000000010110101_0
private theorem bp00000000000000101101010 : Branch 0 (-921237/15625 : ℚ) vp0000000000000010110101 := by
  apply branch_left_normalized (c:=vp00000000000000101101010) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-921237/15625 : ℚ) - ((0:ℤ):ℚ) = (-1842474/15625 : ℚ) by norm_num]
  exact coverp00000000000000101101010
private noncomputable def ep00000000000000101101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101101011-E-0000.bin"
noncomputable def ep00000000000000101101011 : Blocks := ep00000000000000101101011_0
private theorem idp00000000000000101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010110101.list =
    C ((2:ℤ)^17) * horner X vp00000000000000101101011.list + horner X ep00000000000000101101011.list := by
  exact edge_identity (B := (2:ℤ)^110) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101101011 : Branch 1 (-921237/15625 : ℚ) vp0000000000000010110101 := by
  apply branch_checked idp00000000000000101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-921237/15625 : ℚ) - ((1:ℤ):ℚ) = (-1858099/15625 : ℚ) by norm_num]
  exact coverp00000000000000101101011
theorem coverp0000000000000010110101 : Covers (-921237/15625 : ℚ) vp0000000000000010110101 := join_branches bp00000000000000101101010 bp00000000000000101101011
private noncomputable def vp0000000000000010110100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010110100-V-0000.bin"
noncomputable def vp0000000000000010110100 : Blocks := vp0000000000000010110100_0
theorem coverp0000000000000010110100 : Covers (-905612/15625 : ℚ) vp0000000000000010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001011010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011010-V-0000.bin"
noncomputable def vp000000000000001011010 : Blocks := vp000000000000001011010_0
private theorem bp0000000000000010110100 : Branch 0 (-452806/15625 : ℚ) vp000000000000001011010 := by
  apply branch_left_normalized (c:=vp0000000000000010110100) (k:=0) (m:=15) (by decide +kernel)
  rw [show 2*(-452806/15625 : ℚ) - ((0:ℤ):ℚ) = (-905612/15625 : ℚ) by norm_num]
  exact coverp0000000000000010110100
private noncomputable def ep0000000000000010110101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010110101-E-0000.bin"
noncomputable def ep0000000000000010110101 : Blocks := ep0000000000000010110101_0
private theorem idp0000000000000010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001011010.list =
    C ((2:ℤ)^22) * horner X vp0000000000000010110101.list + horner X ep0000000000000010110101.list := by
  exact edge_identity (B := (2:ℤ)^116) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010110101 : Branch 1 (-452806/15625 : ℚ) vp000000000000001011010 := by
  apply branch_checked idp0000000000000010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-452806/15625 : ℚ) - ((1:ℤ):ℚ) = (-921237/15625 : ℚ) by norm_num]
  exact coverp0000000000000010110101
theorem coverp000000000000001011010 : Covers (-452806/15625 : ℚ) vp000000000000001011010 := join_branches bp0000000000000010110100 bp0000000000000010110101
private noncomputable def vp00000000000000101101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101101-V-0000.bin"
noncomputable def vp00000000000000101101 : Blocks := vp00000000000000101101_0
private theorem bp000000000000001011010 : Branch 0 (-226403/15625 : ℚ) vp00000000000000101101 := by
  apply branch_left_normalized (c:=vp000000000000001011010) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-226403/15625 : ℚ) - ((0:ℤ):ℚ) = (-452806/15625 : ℚ) by norm_num]
  exact coverp000000000000001011010
private noncomputable def ep000000000000001011011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011011-E-0000.bin"
noncomputable def ep000000000000001011011 : Blocks := ep000000000000001011011_0
private theorem idp000000000000001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000101101.list =
    C ((2:ℤ)^30) * horner X vp000000000000001011011.list + horner X ep000000000000001011011.list := by
  exact edge_identity (B := (2:ℤ)^126) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001011011 : Branch 1 (-226403/15625 : ℚ) vp00000000000000101101 := by
  apply branch_checked idp000000000000001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-226403/15625 : ℚ) - ((1:ℤ):ℚ) = (-468431/15625 : ℚ) by norm_num]
  exact coverp000000000000001011011
theorem coverp00000000000000101101 : Covers (-226403/15625 : ℚ) vp00000000000000101101 := join_branches bp000000000000001011010 bp000000000000001011011
private noncomputable def vp000000000000001011001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011001-V-0000.bin"
noncomputable def vp000000000000001011001 : Blocks := vp000000000000001011001_0
theorem coverp000000000000001011001 : Covers (-437181/15625 : ℚ) vp000000000000001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001011000_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011000-V-0000.bin"
noncomputable def vp000000000000001011000 : Blocks := vp000000000000001011000_0
theorem coverp000000000000001011000 : Covers (-421556/15625 : ℚ) vp000000000000001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101100_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101100-V-0000.bin"
noncomputable def vp00000000000000101100 : Blocks := vp00000000000000101100_0
private theorem bp000000000000001011000 : Branch 0 (-210778/15625 : ℚ) vp00000000000000101100 := by
  apply branch_left_normalized (c:=vp000000000000001011000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-210778/15625 : ℚ) - ((0:ℤ):ℚ) = (-421556/15625 : ℚ) by norm_num]
  exact coverp000000000000001011000
private noncomputable def ep000000000000001011001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011001-E-0000.bin"
noncomputable def ep000000000000001011001 : Blocks := ep000000000000001011001_0
private theorem idp000000000000001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000101100.list =
    C ((2:ℤ)^31) * horner X vp000000000000001011001.list + horner X ep000000000000001011001.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001011001 : Branch 1 (-210778/15625 : ℚ) vp00000000000000101100 := by
  apply branch_checked idp000000000000001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-210778/15625 : ℚ) - ((1:ℤ):ℚ) = (-437181/15625 : ℚ) by norm_num]
  exact coverp000000000000001011001
theorem coverp00000000000000101100 : Covers (-210778/15625 : ℚ) vp00000000000000101100 := join_branches bp000000000000001011000 bp000000000000001011001
private noncomputable def vp0000000000000010110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010110-V-0000.bin"
noncomputable def vp0000000000000010110 : Blocks := vp0000000000000010110_0
private theorem bp00000000000000101100 : Branch 0 (-105389/15625 : ℚ) vp0000000000000010110 := by
  apply branch_left_normalized (c:=vp00000000000000101100) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-105389/15625 : ℚ) - ((0:ℤ):ℚ) = (-210778/15625 : ℚ) by norm_num]
  exact coverp00000000000000101100
private noncomputable def ep00000000000000101101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101101-E-0000.bin"
noncomputable def ep00000000000000101101 : Blocks := ep00000000000000101101_0
private theorem idp00000000000000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010110.list =
    C ((2:ℤ)^48) * horner X vp00000000000000101101.list + horner X ep00000000000000101101.list := by
  exact edge_identity (B := (2:ℤ)^150) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101101 : Branch 1 (-105389/15625 : ℚ) vp0000000000000010110 := by
  apply branch_checked idp00000000000000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-105389/15625 : ℚ) - ((1:ℤ):ℚ) = (-226403/15625 : ℚ) by norm_num]
  exact coverp00000000000000101101
theorem coverp0000000000000010110 : Covers (-105389/15625 : ℚ) vp0000000000000010110 := join_branches bp00000000000000101100 bp00000000000000101101
private noncomputable def vp000000000000001011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011-V-0000.bin"
noncomputable def vp000000000000001011 : Blocks := vp000000000000001011_0
private theorem bp0000000000000010110 : Branch 0 (-105389/31250 : ℚ) vp000000000000001011 := by
  apply branch_left_normalized (c:=vp0000000000000010110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-105389/31250 : ℚ) - ((0:ℤ):ℚ) = (-105389/15625 : ℚ) by norm_num]
  exact coverp0000000000000010110
private noncomputable def ep0000000000000010111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010111-E-0000.bin"
noncomputable def ep0000000000000010111 : Blocks := ep0000000000000010111_0
private theorem idp0000000000000010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001011.list =
    C ((2:ℤ)^76) * horner X vp0000000000000010111.list + horner X ep0000000000000010111.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010111 : Branch 1 (-105389/31250 : ℚ) vp000000000000001011 := by
  apply branch_checked idp0000000000000010111 (by positivity) (by decide +kernel)
  rw [show 2*(-105389/31250 : ℚ) - ((1:ℤ):ℚ) = (-121014/15625 : ℚ) by norm_num]
  exact coverp0000000000000010111
theorem coverp000000000000001011 : Covers (-105389/31250 : ℚ) vp000000000000001011 := join_branches bp0000000000000010110 bp0000000000000010111
private noncomputable def vp00000000000000101011111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101011111-V-0000.bin"
noncomputable def vp00000000000000101011111 : Blocks := vp00000000000000101011111_0
theorem coverp00000000000000101011111 : Covers (-1670599/15625 : ℚ) vp00000000000000101011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101011110_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101011110-V-0000.bin"
noncomputable def vp00000000000000101011110 : Blocks := vp00000000000000101011110_0
theorem coverp00000000000000101011110 : Covers (-1654974/15625 : ℚ) vp00000000000000101011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010101111-V-0000.bin"
noncomputable def vp0000000000000010101111 : Blocks := vp0000000000000010101111_0
private theorem bp00000000000000101011110 : Branch 0 (-827487/15625 : ℚ) vp0000000000000010101111 := by
  apply branch_left_normalized (c:=vp00000000000000101011110) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-827487/15625 : ℚ) - ((0:ℤ):ℚ) = (-1654974/15625 : ℚ) by norm_num]
  exact coverp00000000000000101011110
private noncomputable def ep00000000000000101011111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101011111-E-0000.bin"
noncomputable def ep00000000000000101011111 : Blocks := ep00000000000000101011111_0
private theorem idp00000000000000101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010101111.list =
    C ((2:ℤ)^17) * horner X vp00000000000000101011111.list + horner X ep00000000000000101011111.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101011111 : Branch 1 (-827487/15625 : ℚ) vp0000000000000010101111 := by
  apply branch_checked idp00000000000000101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-827487/15625 : ℚ) - ((1:ℤ):ℚ) = (-1670599/15625 : ℚ) by norm_num]
  exact coverp00000000000000101011111
theorem coverp0000000000000010101111 : Covers (-827487/15625 : ℚ) vp0000000000000010101111 := join_branches bp00000000000000101011110 bp00000000000000101011111
private noncomputable def vp0000000000000010101110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010101110-V-0000.bin"
noncomputable def vp0000000000000010101110 : Blocks := vp0000000000000010101110_0
theorem coverp0000000000000010101110 : Covers (-811862/15625 : ℚ) vp0000000000000010101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001010111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010111-V-0000.bin"
noncomputable def vp000000000000001010111 : Blocks := vp000000000000001010111_0
private theorem bp0000000000000010101110 : Branch 0 (-405931/15625 : ℚ) vp000000000000001010111 := by
  apply branch_left_normalized (c:=vp0000000000000010101110) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-405931/15625 : ℚ) - ((0:ℤ):ℚ) = (-811862/15625 : ℚ) by norm_num]
  exact coverp0000000000000010101110
private noncomputable def ep0000000000000010101111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010101111-E-0000.bin"
noncomputable def ep0000000000000010101111 : Blocks := ep0000000000000010101111_0
private theorem idp0000000000000010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001010111.list =
    C ((2:ℤ)^22) * horner X vp0000000000000010101111.list + horner X ep0000000000000010101111.list := by
  exact edge_identity (B := (2:ℤ)^116) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010101111 : Branch 1 (-405931/15625 : ℚ) vp000000000000001010111 := by
  apply branch_checked idp0000000000000010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-405931/15625 : ℚ) - ((1:ℤ):ℚ) = (-827487/15625 : ℚ) by norm_num]
  exact coverp0000000000000010101111
theorem coverp000000000000001010111 : Covers (-405931/15625 : ℚ) vp000000000000001010111 := join_branches bp0000000000000010101110 bp0000000000000010101111
private noncomputable def vp000000000000001010110_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010110-V-0000.bin"
noncomputable def vp000000000000001010110 : Blocks := vp000000000000001010110_0
theorem coverp000000000000001010110 : Covers (-390306/15625 : ℚ) vp000000000000001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101011-V-0000.bin"
noncomputable def vp00000000000000101011 : Blocks := vp00000000000000101011_0
private theorem bp000000000000001010110 : Branch 0 (-195153/15625 : ℚ) vp00000000000000101011 := by
  apply branch_left_normalized (c:=vp000000000000001010110) (k:=0) (m:=20) (by decide +kernel)
  rw [show 2*(-195153/15625 : ℚ) - ((0:ℤ):ℚ) = (-390306/15625 : ℚ) by norm_num]
  exact coverp000000000000001010110
private noncomputable def ep000000000000001010111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010111-E-0000.bin"
noncomputable def ep000000000000001010111 : Blocks := ep000000000000001010111_0
private theorem idp000000000000001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000101011.list =
    C ((2:ℤ)^31) * horner X vp000000000000001010111.list + horner X ep000000000000001010111.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001010111 : Branch 1 (-195153/15625 : ℚ) vp00000000000000101011 := by
  apply branch_checked idp000000000000001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-195153/15625 : ℚ) - ((1:ℤ):ℚ) = (-405931/15625 : ℚ) by norm_num]
  exact coverp000000000000001010111
theorem coverp00000000000000101011 : Covers (-195153/15625 : ℚ) vp00000000000000101011 := join_branches bp000000000000001010110 bp000000000000001010111
private noncomputable def vp000000000000001010101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010101-V-0000.bin"
noncomputable def vp000000000000001010101 : Blocks := vp000000000000001010101_0
theorem coverp000000000000001010101 : Covers (-374681/15625 : ℚ) vp000000000000001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101010011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101010011-V-0000.bin"
noncomputable def vp00000000000000101010011 : Blocks := vp00000000000000101010011_0
theorem coverp00000000000000101010011 : Covers (-1483099/15625 : ℚ) vp00000000000000101010011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101010010_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101010010-V-0000.bin"
noncomputable def vp00000000000000101010010 : Blocks := vp00000000000000101010010_0
theorem coverp00000000000000101010010 : Covers (-1467474/15625 : ℚ) vp00000000000000101010010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010101001-V-0000.bin"
noncomputable def vp0000000000000010101001 : Blocks := vp0000000000000010101001_0
private theorem bp00000000000000101010010 : Branch 0 (-733737/15625 : ℚ) vp0000000000000010101001 := by
  apply branch_left_normalized (c:=vp00000000000000101010010) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-733737/15625 : ℚ) - ((0:ℤ):ℚ) = (-1467474/15625 : ℚ) by norm_num]
  exact coverp00000000000000101010010
private noncomputable def ep00000000000000101010011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101010011-E-0000.bin"
noncomputable def ep00000000000000101010011 : Blocks := ep00000000000000101010011_0
private theorem idp00000000000000101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010101001.list =
    C ((2:ℤ)^18) * horner X vp00000000000000101010011.list + horner X ep00000000000000101010011.list := by
  exact edge_identity (B := (2:ℤ)^110) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101010011 : Branch 1 (-733737/15625 : ℚ) vp0000000000000010101001 := by
  apply branch_checked idp00000000000000101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-733737/15625 : ℚ) - ((1:ℤ):ℚ) = (-1483099/15625 : ℚ) by norm_num]
  exact coverp00000000000000101010011
theorem coverp0000000000000010101001 : Covers (-733737/15625 : ℚ) vp0000000000000010101001 := join_branches bp00000000000000101010010 bp00000000000000101010011
private noncomputable def vp00000000000000101010001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101010001-V-0000.bin"
noncomputable def vp00000000000000101010001 : Blocks := vp00000000000000101010001_0
theorem coverp00000000000000101010001 : Covers (-1451849/15625 : ℚ) vp00000000000000101010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101010000_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101010000-V-0000.bin"
noncomputable def vp00000000000000101010000 : Blocks := vp00000000000000101010000_0
theorem coverp00000000000000101010000 : Covers (-1436224/15625 : ℚ) vp00000000000000101010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010101000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010101000-V-0000.bin"
noncomputable def vp0000000000000010101000 : Blocks := vp0000000000000010101000_0
private theorem bp00000000000000101010000 : Branch 0 (-718112/15625 : ℚ) vp0000000000000010101000 := by
  apply branch_left_normalized (c:=vp00000000000000101010000) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-718112/15625 : ℚ) - ((0:ℤ):ℚ) = (-1436224/15625 : ℚ) by norm_num]
  exact coverp00000000000000101010000
private noncomputable def ep00000000000000101010001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101010001-E-0000.bin"
noncomputable def ep00000000000000101010001 : Blocks := ep00000000000000101010001_0
private theorem idp00000000000000101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010101000.list =
    C ((2:ℤ)^17) * horner X vp00000000000000101010001.list + horner X ep00000000000000101010001.list := by
  exact edge_identity (B := (2:ℤ)^110) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101010001 : Branch 1 (-718112/15625 : ℚ) vp0000000000000010101000 := by
  apply branch_checked idp00000000000000101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-718112/15625 : ℚ) - ((1:ℤ):ℚ) = (-1451849/15625 : ℚ) by norm_num]
  exact coverp00000000000000101010001
theorem coverp0000000000000010101000 : Covers (-718112/15625 : ℚ) vp0000000000000010101000 := join_branches bp00000000000000101010000 bp00000000000000101010001
private noncomputable def vp000000000000001010100_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010100-V-0000.bin"
noncomputable def vp000000000000001010100 : Blocks := vp000000000000001010100_0
private theorem bp0000000000000010101000 : Branch 0 (-359056/15625 : ℚ) vp000000000000001010100 := by
  apply branch_left_normalized (c:=vp0000000000000010101000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-359056/15625 : ℚ) - ((0:ℤ):ℚ) = (-718112/15625 : ℚ) by norm_num]
  exact coverp0000000000000010101000
private noncomputable def ep0000000000000010101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010101001-E-0000.bin"
noncomputable def ep0000000000000010101001 : Blocks := ep0000000000000010101001_0
private theorem idp0000000000000010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001010100.list =
    C ((2:ℤ)^22) * horner X vp0000000000000010101001.list + horner X ep0000000000000010101001.list := by
  exact edge_identity (B := (2:ℤ)^116) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010101001 : Branch 1 (-359056/15625 : ℚ) vp000000000000001010100 := by
  apply branch_checked idp0000000000000010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-359056/15625 : ℚ) - ((1:ℤ):ℚ) = (-733737/15625 : ℚ) by norm_num]
  exact coverp0000000000000010101001
theorem coverp000000000000001010100 : Covers (-359056/15625 : ℚ) vp000000000000001010100 := join_branches bp0000000000000010101000 bp0000000000000010101001
private noncomputable def vp00000000000000101010_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101010-V-0000.bin"
noncomputable def vp00000000000000101010 : Blocks := vp00000000000000101010_0
private theorem bp000000000000001010100 : Branch 0 (-179528/15625 : ℚ) vp00000000000000101010 := by
  apply branch_left_normalized (c:=vp000000000000001010100) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-179528/15625 : ℚ) - ((0:ℤ):ℚ) = (-359056/15625 : ℚ) by norm_num]
  exact coverp000000000000001010100
private noncomputable def ep000000000000001010101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010101-E-0000.bin"
noncomputable def ep000000000000001010101 : Blocks := ep000000000000001010101_0
private theorem idp000000000000001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000101010.list =
    C ((2:ℤ)^31) * horner X vp000000000000001010101.list + horner X ep000000000000001010101.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001010101 : Branch 1 (-179528/15625 : ℚ) vp00000000000000101010 := by
  apply branch_checked idp000000000000001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-179528/15625 : ℚ) - ((1:ℤ):ℚ) = (-374681/15625 : ℚ) by norm_num]
  exact coverp000000000000001010101
theorem coverp00000000000000101010 : Covers (-179528/15625 : ℚ) vp00000000000000101010 := join_branches bp000000000000001010100 bp000000000000001010101
private noncomputable def vp0000000000000010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010101-V-0000.bin"
noncomputable def vp0000000000000010101 : Blocks := vp0000000000000010101_0
private theorem bp00000000000000101010 : Branch 0 (-89764/15625 : ℚ) vp0000000000000010101 := by
  apply branch_left_normalized (c:=vp00000000000000101010) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-89764/15625 : ℚ) - ((0:ℤ):ℚ) = (-179528/15625 : ℚ) by norm_num]
  exact coverp00000000000000101010
private noncomputable def ep00000000000000101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101011-E-0000.bin"
noncomputable def ep00000000000000101011 : Blocks := ep00000000000000101011_0
private theorem idp00000000000000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010101.list =
    C ((2:ℤ)^47) * horner X vp00000000000000101011.list + horner X ep00000000000000101011.list := by
  exact edge_identity (B := (2:ℤ)^149) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101011 : Branch 1 (-89764/15625 : ℚ) vp0000000000000010101 := by
  apply branch_checked idp00000000000000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-89764/15625 : ℚ) - ((1:ℤ):ℚ) = (-195153/15625 : ℚ) by norm_num]
  exact coverp00000000000000101011
theorem coverp0000000000000010101 : Covers (-89764/15625 : ℚ) vp0000000000000010101 := join_branches bp00000000000000101010 bp00000000000000101011
private noncomputable def vp000000000000001010011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010011-V-0000.bin"
noncomputable def vp000000000000001010011 : Blocks := vp000000000000001010011_0
theorem coverp000000000000001010011 : Covers (-343431/15625 : ℚ) vp000000000000001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001010010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010010-V-0000.bin"
noncomputable def vp000000000000001010010 : Blocks := vp000000000000001010010_0
theorem coverp000000000000001010010 : Covers (-327806/15625 : ℚ) vp000000000000001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101001-V-0000.bin"
noncomputable def vp00000000000000101001 : Blocks := vp00000000000000101001_0
private theorem bp000000000000001010010 : Branch 0 (-163903/15625 : ℚ) vp00000000000000101001 := by
  apply branch_left_normalized (c:=vp000000000000001010010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-163903/15625 : ℚ) - ((0:ℤ):ℚ) = (-327806/15625 : ℚ) by norm_num]
  exact coverp000000000000001010010
private noncomputable def ep000000000000001010011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010011-E-0000.bin"
noncomputable def ep000000000000001010011 : Blocks := ep000000000000001010011_0
private theorem idp000000000000001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000101001.list =
    C ((2:ℤ)^32) * horner X vp000000000000001010011.list + horner X ep000000000000001010011.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001010011 : Branch 1 (-163903/15625 : ℚ) vp00000000000000101001 := by
  apply branch_checked idp000000000000001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-163903/15625 : ℚ) - ((1:ℤ):ℚ) = (-343431/15625 : ℚ) by norm_num]
  exact coverp000000000000001010011
theorem coverp00000000000000101001 : Covers (-163903/15625 : ℚ) vp00000000000000101001 := join_branches bp000000000000001010010 bp000000000000001010011
private noncomputable def vp0000000000000010100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010100011-V-0000.bin"
noncomputable def vp0000000000000010100011 : Blocks := vp0000000000000010100011_0
theorem coverp0000000000000010100011 : Covers (-639987/15625 : ℚ) vp0000000000000010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101000101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101000101-V-0000.bin"
noncomputable def vp00000000000000101000101 : Blocks := vp00000000000000101000101_0
theorem coverp00000000000000101000101 : Covers (-1264349/15625 : ℚ) vp00000000000000101000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000101000100_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101000100-V-0000.bin"
noncomputable def vp00000000000000101000100 : Blocks := vp00000000000000101000100_0
theorem coverp00000000000000101000100 : Covers (-1248724/15625 : ℚ) vp00000000000000101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010100010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010100010-V-0000.bin"
noncomputable def vp0000000000000010100010 : Blocks := vp0000000000000010100010_0
private theorem bp00000000000000101000100 : Branch 0 (-624362/15625 : ℚ) vp0000000000000010100010 := by
  apply branch_left_normalized (c:=vp00000000000000101000100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-624362/15625 : ℚ) - ((0:ℤ):ℚ) = (-1248724/15625 : ℚ) by norm_num]
  exact coverp00000000000000101000100
private noncomputable def ep00000000000000101000101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101000101-E-0000.bin"
noncomputable def ep00000000000000101000101 : Blocks := ep00000000000000101000101_0
private theorem idp00000000000000101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010100010.list =
    C ((2:ℤ)^18) * horner X vp00000000000000101000101.list + horner X ep00000000000000101000101.list := by
  exact edge_identity (B := (2:ℤ)^111) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101000101 : Branch 1 (-624362/15625 : ℚ) vp0000000000000010100010 := by
  apply branch_checked idp00000000000000101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-624362/15625 : ℚ) - ((1:ℤ):ℚ) = (-1264349/15625 : ℚ) by norm_num]
  exact coverp00000000000000101000101
theorem coverp0000000000000010100010 : Covers (-624362/15625 : ℚ) vp0000000000000010100010 := join_branches bp00000000000000101000100 bp00000000000000101000101
private noncomputable def vp000000000000001010001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010001-V-0000.bin"
noncomputable def vp000000000000001010001 : Blocks := vp000000000000001010001_0
private theorem bp0000000000000010100010 : Branch 0 (-312181/15625 : ℚ) vp000000000000001010001 := by
  apply branch_left_normalized (c:=vp0000000000000010100010) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-312181/15625 : ℚ) - ((0:ℤ):ℚ) = (-624362/15625 : ℚ) by norm_num]
  exact coverp0000000000000010100010
private noncomputable def ep0000000000000010100011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010100011-E-0000.bin"
noncomputable def ep0000000000000010100011 : Blocks := ep0000000000000010100011_0
private theorem idp0000000000000010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001010001.list =
    C ((2:ℤ)^23) * horner X vp0000000000000010100011.list + horner X ep0000000000000010100011.list := by
  exact edge_identity (B := (2:ℤ)^117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010100011 : Branch 1 (-312181/15625 : ℚ) vp000000000000001010001 := by
  apply branch_checked idp0000000000000010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-312181/15625 : ℚ) - ((1:ℤ):ℚ) = (-639987/15625 : ℚ) by norm_num]
  exact coverp0000000000000010100011
theorem coverp000000000000001010001 : Covers (-312181/15625 : ℚ) vp000000000000001010001 := join_branches bp0000000000000010100010 bp0000000000000010100011
private noncomputable def vp0000000000000010100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010100001-V-0000.bin"
noncomputable def vp0000000000000010100001 : Blocks := vp0000000000000010100001_0
theorem coverp0000000000000010100001 : Covers (-608737/15625 : ℚ) vp0000000000000010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010100000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010100000-V-0000.bin"
noncomputable def vp0000000000000010100000 : Blocks := vp0000000000000010100000_0
theorem coverp0000000000000010100000 : Covers (-593112/15625 : ℚ) vp0000000000000010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001010000_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010000-V-0000.bin"
noncomputable def vp000000000000001010000 : Blocks := vp000000000000001010000_0
private theorem bp0000000000000010100000 : Branch 0 (-296556/15625 : ℚ) vp000000000000001010000 := by
  apply branch_left_normalized (c:=vp0000000000000010100000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-296556/15625 : ℚ) - ((0:ℤ):ℚ) = (-593112/15625 : ℚ) by norm_num]
  exact coverp0000000000000010100000
private noncomputable def ep0000000000000010100001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010100001-E-0000.bin"
noncomputable def ep0000000000000010100001 : Blocks := ep0000000000000010100001_0
private theorem idp0000000000000010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001010000.list =
    C ((2:ℤ)^22) * horner X vp0000000000000010100001.list + horner X ep0000000000000010100001.list := by
  exact edge_identity (B := (2:ℤ)^117) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010100001 : Branch 1 (-296556/15625 : ℚ) vp000000000000001010000 := by
  apply branch_checked idp0000000000000010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-296556/15625 : ℚ) - ((1:ℤ):ℚ) = (-608737/15625 : ℚ) by norm_num]
  exact coverp0000000000000010100001
theorem coverp000000000000001010000 : Covers (-296556/15625 : ℚ) vp000000000000001010000 := join_branches bp0000000000000010100000 bp0000000000000010100001
private noncomputable def vp00000000000000101000_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101000-V-0000.bin"
noncomputable def vp00000000000000101000 : Blocks := vp00000000000000101000_0
private theorem bp000000000000001010000 : Branch 0 (-148278/15625 : ℚ) vp00000000000000101000 := by
  apply branch_left_normalized (c:=vp000000000000001010000) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-148278/15625 : ℚ) - ((0:ℤ):ℚ) = (-296556/15625 : ℚ) by norm_num]
  exact coverp000000000000001010000
private noncomputable def ep000000000000001010001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010001-E-0000.bin"
noncomputable def ep000000000000001010001 : Blocks := ep000000000000001010001_0
private theorem idp000000000000001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000101000.list =
    C ((2:ℤ)^31) * horner X vp000000000000001010001.list + horner X ep000000000000001010001.list := by
  exact edge_identity (B := (2:ℤ)^128) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001010001 : Branch 1 (-148278/15625 : ℚ) vp00000000000000101000 := by
  apply branch_checked idp000000000000001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-148278/15625 : ℚ) - ((1:ℤ):ℚ) = (-312181/15625 : ℚ) by norm_num]
  exact coverp000000000000001010001
theorem coverp00000000000000101000 : Covers (-148278/15625 : ℚ) vp00000000000000101000 := join_branches bp000000000000001010000 bp000000000000001010001
private noncomputable def vp0000000000000010100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010100-V-0000.bin"
noncomputable def vp0000000000000010100 : Blocks := vp0000000000000010100_0
private theorem bp00000000000000101000 : Branch 0 (-74139/15625 : ℚ) vp0000000000000010100 := by
  apply branch_left_normalized (c:=vp00000000000000101000) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-74139/15625 : ℚ) - ((0:ℤ):ℚ) = (-148278/15625 : ℚ) by norm_num]
  exact coverp00000000000000101000
private noncomputable def ep00000000000000101001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101001-E-0000.bin"
noncomputable def ep00000000000000101001 : Blocks := ep00000000000000101001_0
private theorem idp00000000000000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010100.list =
    C ((2:ℤ)^47) * horner X vp00000000000000101001.list + horner X ep00000000000000101001.list := by
  exact edge_identity (B := (2:ℤ)^150) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101001 : Branch 1 (-74139/15625 : ℚ) vp0000000000000010100 := by
  apply branch_checked idp00000000000000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-74139/15625 : ℚ) - ((1:ℤ):ℚ) = (-163903/15625 : ℚ) by norm_num]
  exact coverp00000000000000101001
theorem coverp0000000000000010100 : Covers (-74139/15625 : ℚ) vp0000000000000010100 := join_branches bp00000000000000101000 bp00000000000000101001
private noncomputable def vp000000000000001010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001010-V-0000.bin"
noncomputable def vp000000000000001010 : Blocks := vp000000000000001010_0
private theorem bp0000000000000010100 : Branch 0 (-74139/31250 : ℚ) vp000000000000001010 := by
  apply branch_left_normalized (c:=vp0000000000000010100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-74139/31250 : ℚ) - ((0:ℤ):ℚ) = (-74139/15625 : ℚ) by norm_num]
  exact coverp0000000000000010100
private noncomputable def ep0000000000000010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010101-E-0000.bin"
noncomputable def ep0000000000000010101 : Blocks := ep0000000000000010101_0
private theorem idp0000000000000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001010.list =
    C ((2:ℤ)^76) * horner X vp0000000000000010101.list + horner X ep0000000000000010101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010101 : Branch 1 (-74139/31250 : ℚ) vp000000000000001010 := by
  apply branch_checked idp0000000000000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-74139/31250 : ℚ) - ((1:ℤ):ℚ) = (-89764/15625 : ℚ) by norm_num]
  exact coverp0000000000000010101
theorem coverp000000000000001010 : Covers (-74139/31250 : ℚ) vp000000000000001010 := join_branches bp0000000000000010100 bp0000000000000010101
private noncomputable def vp00000000000000101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101-V-0000.bin"
private noncomputable def vp00000000000000101_1 : Blocks := edgeBlocks% "full/vectors/00000000000000101-V-0001.bin"
noncomputable def vp00000000000000101 : Blocks := (Blocks.join vp00000000000000101_0 vp00000000000000101_1)
private theorem bp000000000000001010 : Branch 0 (-74139/62500 : ℚ) vp00000000000000101 := by
  apply branch_left_normalized (c:=vp000000000000001010) (k:=0) (m:=75) (by decide +kernel)
  rw [show 2*(-74139/62500 : ℚ) - ((0:ℤ):ℚ) = (-74139/31250 : ℚ) by norm_num]
  exact coverp000000000000001010
private noncomputable def ep000000000000001011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001011-E-0000.bin"
private noncomputable def ep000000000000001011_1 : Blocks := edgeBlocks% "full/vectors/000000000000001011-E-0001.bin"
noncomputable def ep000000000000001011 : Blocks := (Blocks.join ep000000000000001011_0 ep000000000000001011_1)
private theorem idp000000000000001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000101.list =
    C ((2:ℤ)^133) * horner X vp000000000000001011.list + horner X ep000000000000001011.list := by
  exact edge_identity (B := (2:ℤ)^275) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001011 : Branch 1 (-74139/62500 : ℚ) vp00000000000000101 := by
  apply branch_checked idp000000000000001011 (by positivity) (by decide +kernel)
  rw [show 2*(-74139/62500 : ℚ) - ((1:ℤ):ℚ) = (-105389/31250 : ℚ) by norm_num]
  exact coverp000000000000001011
theorem coverp00000000000000101 : Covers (-74139/62500 : ℚ) vp00000000000000101 := join_branches bp000000000000001010 bp000000000000001011
private noncomputable def vp000000000000001001111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001111-V-0000.bin"
noncomputable def vp000000000000001001111 : Blocks := vp000000000000001001111_0
theorem coverp000000000000001001111 : Covers (-280931/15625 : ℚ) vp000000000000001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100111011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100111011-V-0000.bin"
noncomputable def vp00000000000000100111011 : Blocks := vp00000000000000100111011_0
theorem coverp00000000000000100111011 : Covers (-1108099/15625 : ℚ) vp00000000000000100111011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001001110101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001110101-V-0000.bin"
noncomputable def vp000000000000001001110101 : Blocks := vp000000000000001001110101_0
theorem coverp000000000000001001110101 : Covers (-2200573/15625 : ℚ) vp000000000000001001110101 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001001110100_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001110100-V-0000.bin"
noncomputable def vp000000000000001001110100 : Blocks := vp000000000000001001110100_0
theorem coverp000000000000001001110100 : Covers (-2184948/15625 : ℚ) vp000000000000001001110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100111010_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100111010-V-0000.bin"
noncomputable def vp00000000000000100111010 : Blocks := vp00000000000000100111010_0
private theorem bp000000000000001001110100 : Branch 0 (-1092474/15625 : ℚ) vp00000000000000100111010 := by
  apply branch_left_normalized (c:=vp000000000000001001110100) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-1092474/15625 : ℚ) - ((0:ℤ):ℚ) = (-2184948/15625 : ℚ) by norm_num]
  exact coverp000000000000001001110100
private noncomputable def ep000000000000001001110101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001110101-E-0000.bin"
noncomputable def ep000000000000001001110101 : Blocks := ep000000000000001001110101_0
private theorem idp000000000000001001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100111010.list =
    C ((2:ℤ)^15) * horner X vp000000000000001001110101.list + horner X ep000000000000001001110101.list := by
  exact edge_identity (B := (2:ℤ)^106) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001001110101 : Branch 1 (-1092474/15625 : ℚ) vp00000000000000100111010 := by
  apply branch_checked idp000000000000001001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1092474/15625 : ℚ) - ((1:ℤ):ℚ) = (-2200573/15625 : ℚ) by norm_num]
  exact coverp000000000000001001110101
theorem coverp00000000000000100111010 : Covers (-1092474/15625 : ℚ) vp00000000000000100111010 := join_branches bp000000000000001001110100 bp000000000000001001110101
private noncomputable def vp0000000000000010011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010011101-V-0000.bin"
noncomputable def vp0000000000000010011101 : Blocks := vp0000000000000010011101_0
private theorem bp00000000000000100111010 : Branch 0 (-546237/15625 : ℚ) vp0000000000000010011101 := by
  apply branch_left_normalized (c:=vp00000000000000100111010) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-546237/15625 : ℚ) - ((0:ℤ):ℚ) = (-1092474/15625 : ℚ) by norm_num]
  exact coverp00000000000000100111010
private noncomputable def ep00000000000000100111011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100111011-E-0000.bin"
noncomputable def ep00000000000000100111011 : Blocks := ep00000000000000100111011_0
private theorem idp00000000000000100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010011101.list =
    C ((2:ℤ)^18) * horner X vp00000000000000100111011.list + horner X ep00000000000000100111011.list := by
  exact edge_identity (B := (2:ℤ)^111) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100111011 : Branch 1 (-546237/15625 : ℚ) vp0000000000000010011101 := by
  apply branch_checked idp00000000000000100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-546237/15625 : ℚ) - ((1:ℤ):ℚ) = (-1108099/15625 : ℚ) by norm_num]
  exact coverp00000000000000100111011
theorem coverp0000000000000010011101 : Covers (-546237/15625 : ℚ) vp0000000000000010011101 := join_branches bp00000000000000100111010 bp00000000000000100111011
private noncomputable def vp000000000000001001110011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001110011-V-0000.bin"
noncomputable def vp000000000000001001110011 : Blocks := vp000000000000001001110011_0
theorem coverp000000000000001001110011 : Covers (-2169323/15625 : ℚ) vp000000000000001001110011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001001110010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001110010-V-0000.bin"
noncomputable def vp000000000000001001110010 : Blocks := vp000000000000001001110010_0
theorem coverp000000000000001001110010 : Covers (-2153698/15625 : ℚ) vp000000000000001001110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100111001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100111001-V-0000.bin"
noncomputable def vp00000000000000100111001 : Blocks := vp00000000000000100111001_0
private theorem bp000000000000001001110010 : Branch 0 (-1076849/15625 : ℚ) vp00000000000000100111001 := by
  apply branch_left_normalized (c:=vp000000000000001001110010) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-1076849/15625 : ℚ) - ((0:ℤ):ℚ) = (-2153698/15625 : ℚ) by norm_num]
  exact coverp000000000000001001110010
private noncomputable def ep000000000000001001110011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001110011-E-0000.bin"
noncomputable def ep000000000000001001110011 : Blocks := ep000000000000001001110011_0
private theorem idp000000000000001001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100111001.list =
    C ((2:ℤ)^14) * horner X vp000000000000001001110011.list + horner X ep000000000000001001110011.list := by
  exact edge_identity (B := (2:ℤ)^107) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001001110011 : Branch 1 (-1076849/15625 : ℚ) vp00000000000000100111001 := by
  apply branch_checked idp000000000000001001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1076849/15625 : ℚ) - ((1:ℤ):ℚ) = (-2169323/15625 : ℚ) by norm_num]
  exact coverp000000000000001001110011
theorem coverp00000000000000100111001 : Covers (-1076849/15625 : ℚ) vp00000000000000100111001 := join_branches bp000000000000001001110010 bp000000000000001001110011
private noncomputable def vp00000000000000100111000_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100111000-V-0000.bin"
noncomputable def vp00000000000000100111000 : Blocks := vp00000000000000100111000_0
theorem coverp00000000000000100111000 : Covers (-1061224/15625 : ℚ) vp00000000000000100111000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010011100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010011100-V-0000.bin"
noncomputable def vp0000000000000010011100 : Blocks := vp0000000000000010011100_0
private theorem bp00000000000000100111000 : Branch 0 (-530612/15625 : ℚ) vp0000000000000010011100 := by
  apply branch_left_normalized (c:=vp00000000000000100111000) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-530612/15625 : ℚ) - ((0:ℤ):ℚ) = (-1061224/15625 : ℚ) by norm_num]
  exact coverp00000000000000100111000
private noncomputable def ep00000000000000100111001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100111001-E-0000.bin"
noncomputable def ep00000000000000100111001 : Blocks := ep00000000000000100111001_0
private theorem idp00000000000000100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010011100.list =
    C ((2:ℤ)^17) * horner X vp00000000000000100111001.list + horner X ep00000000000000100111001.list := by
  exact edge_identity (B := (2:ℤ)^111) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100111001 : Branch 1 (-530612/15625 : ℚ) vp0000000000000010011100 := by
  apply branch_checked idp00000000000000100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-530612/15625 : ℚ) - ((1:ℤ):ℚ) = (-1076849/15625 : ℚ) by norm_num]
  exact coverp00000000000000100111001
theorem coverp0000000000000010011100 : Covers (-530612/15625 : ℚ) vp0000000000000010011100 := join_branches bp00000000000000100111000 bp00000000000000100111001
private noncomputable def vp000000000000001001110_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001110-V-0000.bin"
noncomputable def vp000000000000001001110 : Blocks := vp000000000000001001110_0
private theorem bp0000000000000010011100 : Branch 0 (-265306/15625 : ℚ) vp000000000000001001110 := by
  apply branch_left_normalized (c:=vp0000000000000010011100) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-265306/15625 : ℚ) - ((0:ℤ):ℚ) = (-530612/15625 : ℚ) by norm_num]
  exact coverp0000000000000010011100
private noncomputable def ep0000000000000010011101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010011101-E-0000.bin"
noncomputable def ep0000000000000010011101 : Blocks := ep0000000000000010011101_0
private theorem idp0000000000000010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001001110.list =
    C ((2:ℤ)^23) * horner X vp0000000000000010011101.list + horner X ep0000000000000010011101.list := by
  exact edge_identity (B := (2:ℤ)^118) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010011101 : Branch 1 (-265306/15625 : ℚ) vp000000000000001001110 := by
  apply branch_checked idp0000000000000010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-265306/15625 : ℚ) - ((1:ℤ):ℚ) = (-546237/15625 : ℚ) by norm_num]
  exact coverp0000000000000010011101
theorem coverp000000000000001001110 : Covers (-265306/15625 : ℚ) vp000000000000001001110 := join_branches bp0000000000000010011100 bp0000000000000010011101
private noncomputable def vp00000000000000100111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100111-V-0000.bin"
noncomputable def vp00000000000000100111 : Blocks := vp00000000000000100111_0
private theorem bp000000000000001001110 : Branch 0 (-132653/15625 : ℚ) vp00000000000000100111 := by
  apply branch_left_normalized (c:=vp000000000000001001110) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-132653/15625 : ℚ) - ((0:ℤ):ℚ) = (-265306/15625 : ℚ) by norm_num]
  exact coverp000000000000001001110
private noncomputable def ep000000000000001001111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001111-E-0000.bin"
noncomputable def ep000000000000001001111 : Blocks := ep000000000000001001111_0
private theorem idp000000000000001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100111.list =
    C ((2:ℤ)^31) * horner X vp000000000000001001111.list + horner X ep000000000000001001111.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001001111 : Branch 1 (-132653/15625 : ℚ) vp00000000000000100111 := by
  apply branch_checked idp000000000000001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-132653/15625 : ℚ) - ((1:ℤ):ℚ) = (-280931/15625 : ℚ) by norm_num]
  exact coverp000000000000001001111
theorem coverp00000000000000100111 : Covers (-132653/15625 : ℚ) vp00000000000000100111 := join_branches bp000000000000001001110 bp000000000000001001111
private noncomputable def vp0000000000000010011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010011011-V-0000.bin"
noncomputable def vp0000000000000010011011 : Blocks := vp0000000000000010011011_0
theorem coverp0000000000000010011011 : Covers (-514987/15625 : ℚ) vp0000000000000010011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010011010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010011010-V-0000.bin"
noncomputable def vp0000000000000010011010 : Blocks := vp0000000000000010011010_0
theorem coverp0000000000000010011010 : Covers (-499362/15625 : ℚ) vp0000000000000010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001001101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001101-V-0000.bin"
noncomputable def vp000000000000001001101 : Blocks := vp000000000000001001101_0
private theorem bp0000000000000010011010 : Branch 0 (-249681/15625 : ℚ) vp000000000000001001101 := by
  apply branch_left_normalized (c:=vp0000000000000010011010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-249681/15625 : ℚ) - ((0:ℤ):ℚ) = (-499362/15625 : ℚ) by norm_num]
  exact coverp0000000000000010011010
private noncomputable def ep0000000000000010011011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010011011-E-0000.bin"
noncomputable def ep0000000000000010011011 : Blocks := ep0000000000000010011011_0
private theorem idp0000000000000010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001001101.list =
    C ((2:ℤ)^22) * horner X vp0000000000000010011011.list + horner X ep0000000000000010011011.list := by
  exact edge_identity (B := (2:ℤ)^118) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010011011 : Branch 1 (-249681/15625 : ℚ) vp000000000000001001101 := by
  apply branch_checked idp0000000000000010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-249681/15625 : ℚ) - ((1:ℤ):ℚ) = (-514987/15625 : ℚ) by norm_num]
  exact coverp0000000000000010011011
theorem coverp000000000000001001101 : Covers (-249681/15625 : ℚ) vp000000000000001001101 := join_branches bp0000000000000010011010 bp0000000000000010011011
private noncomputable def vp000000000000001001100_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001100-V-0000.bin"
noncomputable def vp000000000000001001100 : Blocks := vp000000000000001001100_0
theorem coverp000000000000001001100 : Covers (-234056/15625 : ℚ) vp000000000000001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100110_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100110-V-0000.bin"
noncomputable def vp00000000000000100110 : Blocks := vp00000000000000100110_0
private theorem bp000000000000001001100 : Branch 0 (-117028/15625 : ℚ) vp00000000000000100110 := by
  apply branch_left_normalized (c:=vp000000000000001001100) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-117028/15625 : ℚ) - ((0:ℤ):ℚ) = (-234056/15625 : ℚ) by norm_num]
  exact coverp000000000000001001100
private noncomputable def ep000000000000001001101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001101-E-0000.bin"
noncomputable def ep000000000000001001101 : Blocks := ep000000000000001001101_0
private theorem idp000000000000001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100110.list =
    C ((2:ℤ)^31) * horner X vp000000000000001001101.list + horner X ep000000000000001001101.list := by
  exact edge_identity (B := (2:ℤ)^129) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001001101 : Branch 1 (-117028/15625 : ℚ) vp00000000000000100110 := by
  apply branch_checked idp000000000000001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-117028/15625 : ℚ) - ((1:ℤ):ℚ) = (-249681/15625 : ℚ) by norm_num]
  exact coverp000000000000001001101
theorem coverp00000000000000100110 : Covers (-117028/15625 : ℚ) vp00000000000000100110 := join_branches bp000000000000001001100 bp000000000000001001101
private noncomputable def vp0000000000000010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010011-V-0000.bin"
noncomputable def vp0000000000000010011 : Blocks := vp0000000000000010011_0
private theorem bp00000000000000100110 : Branch 0 (-58514/15625 : ℚ) vp0000000000000010011 := by
  apply branch_left_normalized (c:=vp00000000000000100110) (k:=0) (m:=30) (by decide +kernel)
  rw [show 2*(-58514/15625 : ℚ) - ((0:ℤ):ℚ) = (-117028/15625 : ℚ) by norm_num]
  exact coverp00000000000000100110
private noncomputable def ep00000000000000100111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100111-E-0000.bin"
noncomputable def ep00000000000000100111 : Blocks := ep00000000000000100111_0
private theorem idp00000000000000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010011.list =
    C ((2:ℤ)^47) * horner X vp00000000000000100111.list + horner X ep00000000000000100111.list := by
  exact edge_identity (B := (2:ℤ)^151) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100111 : Branch 1 (-58514/15625 : ℚ) vp0000000000000010011 := by
  apply branch_checked idp00000000000000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-58514/15625 : ℚ) - ((1:ℤ):ℚ) = (-132653/15625 : ℚ) by norm_num]
  exact coverp00000000000000100111
theorem coverp0000000000000010011 : Covers (-58514/15625 : ℚ) vp0000000000000010011 := join_branches bp00000000000000100110 bp00000000000000100111
private noncomputable def vp000000000000001001011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001011-V-0000.bin"
noncomputable def vp000000000000001001011 : Blocks := vp000000000000001001011_0
theorem coverp000000000000001001011 : Covers (-218431/15625 : ℚ) vp000000000000001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001001010111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001010111-V-0000.bin"
noncomputable def vp000000000000001001010111 : Blocks := vp000000000000001001010111_0
theorem coverp000000000000001001010111 : Covers (-1731823/15625 : ℚ) vp000000000000001001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001001010110_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001010110-V-0000.bin"
noncomputable def vp000000000000001001010110 : Blocks := vp000000000000001001010110_0
theorem coverp000000000000001001010110 : Covers (-1716198/15625 : ℚ) vp000000000000001001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100101011-V-0000.bin"
noncomputable def vp00000000000000100101011 : Blocks := vp00000000000000100101011_0
private theorem bp000000000000001001010110 : Branch 0 (-858099/15625 : ℚ) vp00000000000000100101011 := by
  apply branch_left_normalized (c:=vp000000000000001001010110) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-858099/15625 : ℚ) - ((0:ℤ):ℚ) = (-1716198/15625 : ℚ) by norm_num]
  exact coverp000000000000001001010110
private noncomputable def ep000000000000001001010111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001010111-E-0000.bin"
noncomputable def ep000000000000001001010111 : Blocks := ep000000000000001001010111_0
private theorem idp000000000000001001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100101011.list =
    C ((2:ℤ)^15) * horner X vp000000000000001001010111.list + horner X ep000000000000001001010111.list := by
  exact edge_identity (B := (2:ℤ)^107) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001001010111 : Branch 1 (-858099/15625 : ℚ) vp00000000000000100101011 := by
  apply branch_checked idp000000000000001001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-858099/15625 : ℚ) - ((1:ℤ):ℚ) = (-1731823/15625 : ℚ) by norm_num]
  exact coverp000000000000001001010111
theorem coverp00000000000000100101011 : Covers (-858099/15625 : ℚ) vp00000000000000100101011 := join_branches bp000000000000001001010110 bp000000000000001001010111
private noncomputable def vp00000000000000100101010_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100101010-V-0000.bin"
noncomputable def vp00000000000000100101010 : Blocks := vp00000000000000100101010_0
theorem coverp00000000000000100101010 : Covers (-842474/15625 : ℚ) vp00000000000000100101010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010010101-V-0000.bin"
noncomputable def vp0000000000000010010101 : Blocks := vp0000000000000010010101_0
private theorem bp00000000000000100101010 : Branch 0 (-421237/15625 : ℚ) vp0000000000000010010101 := by
  apply branch_left_normalized (c:=vp00000000000000100101010) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-421237/15625 : ℚ) - ((0:ℤ):ℚ) = (-842474/15625 : ℚ) by norm_num]
  exact coverp00000000000000100101010
private noncomputable def ep00000000000000100101011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100101011-E-0000.bin"
noncomputable def ep00000000000000100101011 : Blocks := ep00000000000000100101011_0
private theorem idp00000000000000100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010010101.list =
    C ((2:ℤ)^17) * horner X vp00000000000000100101011.list + horner X ep00000000000000100101011.list := by
  exact edge_identity (B := (2:ℤ)^111) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100101011 : Branch 1 (-421237/15625 : ℚ) vp0000000000000010010101 := by
  apply branch_checked idp00000000000000100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-421237/15625 : ℚ) - ((1:ℤ):ℚ) = (-858099/15625 : ℚ) by norm_num]
  exact coverp00000000000000100101011
theorem coverp0000000000000010010101 : Covers (-421237/15625 : ℚ) vp0000000000000010010101 := join_branches bp00000000000000100101010 bp00000000000000100101011
private noncomputable def vp0000000000000010010100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010010100-V-0000.bin"
noncomputable def vp0000000000000010010100 : Blocks := vp0000000000000010010100_0
theorem coverp0000000000000010010100 : Covers (-405612/15625 : ℚ) vp0000000000000010010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001001010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001010-V-0000.bin"
noncomputable def vp000000000000001001010 : Blocks := vp000000000000001001010_0
private theorem bp0000000000000010010100 : Branch 0 (-202806/15625 : ℚ) vp000000000000001001010 := by
  apply branch_left_normalized (c:=vp0000000000000010010100) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-202806/15625 : ℚ) - ((0:ℤ):ℚ) = (-405612/15625 : ℚ) by norm_num]
  exact coverp0000000000000010010100
private noncomputable def ep0000000000000010010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010010101-E-0000.bin"
noncomputable def ep0000000000000010010101 : Blocks := ep0000000000000010010101_0
private theorem idp0000000000000010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001001010.list =
    C ((2:ℤ)^23) * horner X vp0000000000000010010101.list + horner X ep0000000000000010010101.list := by
  exact edge_identity (B := (2:ℤ)^119) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010010101 : Branch 1 (-202806/15625 : ℚ) vp000000000000001001010 := by
  apply branch_checked idp0000000000000010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-202806/15625 : ℚ) - ((1:ℤ):ℚ) = (-421237/15625 : ℚ) by norm_num]
  exact coverp0000000000000010010101
theorem coverp000000000000001001010 : Covers (-202806/15625 : ℚ) vp000000000000001001010 := join_branches bp0000000000000010010100 bp0000000000000010010101
private noncomputable def vp00000000000000100101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100101-V-0000.bin"
noncomputable def vp00000000000000100101 : Blocks := vp00000000000000100101_0
private theorem bp000000000000001001010 : Branch 0 (-101403/15625 : ℚ) vp00000000000000100101 := by
  apply branch_left_normalized (c:=vp000000000000001001010) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-101403/15625 : ℚ) - ((0:ℤ):ℚ) = (-202806/15625 : ℚ) by norm_num]
  exact coverp000000000000001001010
private noncomputable def ep000000000000001001011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001011-E-0000.bin"
noncomputable def ep000000000000001001011 : Blocks := ep000000000000001001011_0
private theorem idp000000000000001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100101.list =
    C ((2:ℤ)^32) * horner X vp000000000000001001011.list + horner X ep000000000000001001011.list := by
  exact edge_identity (B := (2:ℤ)^130) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001001011 : Branch 1 (-101403/15625 : ℚ) vp00000000000000100101 := by
  apply branch_checked idp000000000000001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-101403/15625 : ℚ) - ((1:ℤ):ℚ) = (-218431/15625 : ℚ) by norm_num]
  exact coverp000000000000001001011
theorem coverp00000000000000100101 : Covers (-101403/15625 : ℚ) vp00000000000000100101 := join_branches bp000000000000001001010 bp000000000000001001011
private noncomputable def vp000000000000001001001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001001-V-0000.bin"
noncomputable def vp000000000000001001001 : Blocks := vp000000000000001001001_0
theorem coverp000000000000001001001 : Covers (-187181/15625 : ℚ) vp000000000000001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010010001-V-0000.bin"
noncomputable def vp0000000000000010010001 : Blocks := vp0000000000000010010001_0
theorem coverp0000000000000010010001 : Covers (-358737/15625 : ℚ) vp0000000000000010010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100100001-V-0000.bin"
noncomputable def vp00000000000000100100001 : Blocks := vp00000000000000100100001_0
theorem coverp00000000000000100100001 : Covers (-701849/15625 : ℚ) vp00000000000000100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001001000001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001000001-V-0000.bin"
noncomputable def vp000000000000001001000001 : Blocks := vp000000000000001001000001_0
theorem coverp000000000000001001000001 : Covers (-1388073/15625 : ℚ) vp000000000000001001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001001000000_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001000000-V-0000.bin"
noncomputable def vp000000000000001001000000 : Blocks := vp000000000000001001000000_0
theorem coverp000000000000001001000000 : Covers (-1372448/15625 : ℚ) vp000000000000001001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100100000_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100100000-V-0000.bin"
noncomputable def vp00000000000000100100000 : Blocks := vp00000000000000100100000_0
private theorem bp000000000000001001000000 : Branch 0 (-686224/15625 : ℚ) vp00000000000000100100000 := by
  apply branch_left_normalized (c:=vp000000000000001001000000) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-686224/15625 : ℚ) - ((0:ℤ):ℚ) = (-1372448/15625 : ℚ) by norm_num]
  exact coverp000000000000001001000000
private noncomputable def ep000000000000001001000001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001000001-E-0000.bin"
noncomputable def ep000000000000001001000001 : Blocks := ep000000000000001001000001_0
private theorem idp000000000000001001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100100000.list =
    C ((2:ℤ)^15) * horner X vp000000000000001001000001.list + horner X ep000000000000001001000001.list := by
  exact edge_identity (B := (2:ℤ)^108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001001000001 : Branch 1 (-686224/15625 : ℚ) vp00000000000000100100000 := by
  apply branch_checked idp000000000000001001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-686224/15625 : ℚ) - ((1:ℤ):ℚ) = (-1388073/15625 : ℚ) by norm_num]
  exact coverp000000000000001001000001
theorem coverp00000000000000100100000 : Covers (-686224/15625 : ℚ) vp00000000000000100100000 := join_branches bp000000000000001001000000 bp000000000000001001000001
private noncomputable def vp0000000000000010010000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010010000-V-0000.bin"
noncomputable def vp0000000000000010010000 : Blocks := vp0000000000000010010000_0
private theorem bp00000000000000100100000 : Branch 0 (-343112/15625 : ℚ) vp0000000000000010010000 := by
  apply branch_left_normalized (c:=vp00000000000000100100000) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-343112/15625 : ℚ) - ((0:ℤ):ℚ) = (-686224/15625 : ℚ) by norm_num]
  exact coverp00000000000000100100000
private noncomputable def ep00000000000000100100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100100001-E-0000.bin"
noncomputable def ep00000000000000100100001 : Blocks := ep00000000000000100100001_0
private theorem idp00000000000000100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010010000.list =
    C ((2:ℤ)^18) * horner X vp00000000000000100100001.list + horner X ep00000000000000100100001.list := by
  exact edge_identity (B := (2:ℤ)^112) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100100001 : Branch 1 (-343112/15625 : ℚ) vp0000000000000010010000 := by
  apply branch_checked idp00000000000000100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-343112/15625 : ℚ) - ((1:ℤ):ℚ) = (-701849/15625 : ℚ) by norm_num]
  exact coverp00000000000000100100001
theorem coverp0000000000000010010000 : Covers (-343112/15625 : ℚ) vp0000000000000010010000 := join_branches bp00000000000000100100000 bp00000000000000100100001
private noncomputable def vp000000000000001001000_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001000-V-0000.bin"
noncomputable def vp000000000000001001000 : Blocks := vp000000000000001001000_0
private theorem bp0000000000000010010000 : Branch 0 (-171556/15625 : ℚ) vp000000000000001001000 := by
  apply branch_left_normalized (c:=vp0000000000000010010000) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-171556/15625 : ℚ) - ((0:ℤ):ℚ) = (-343112/15625 : ℚ) by norm_num]
  exact coverp0000000000000010010000
private noncomputable def ep0000000000000010010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010010001-E-0000.bin"
noncomputable def ep0000000000000010010001 : Blocks := ep0000000000000010010001_0
private theorem idp0000000000000010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001001000.list =
    C ((2:ℤ)^24) * horner X vp0000000000000010010001.list + horner X ep0000000000000010010001.list := by
  exact edge_identity (B := (2:ℤ)^120) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010010001 : Branch 1 (-171556/15625 : ℚ) vp000000000000001001000 := by
  apply branch_checked idp0000000000000010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-171556/15625 : ℚ) - ((1:ℤ):ℚ) = (-358737/15625 : ℚ) by norm_num]
  exact coverp0000000000000010010001
theorem coverp000000000000001001000 : Covers (-171556/15625 : ℚ) vp000000000000001001000 := join_branches bp0000000000000010010000 bp0000000000000010010001
private noncomputable def vp00000000000000100100_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100100-V-0000.bin"
noncomputable def vp00000000000000100100 : Blocks := vp00000000000000100100_0
private theorem bp000000000000001001000 : Branch 0 (-85778/15625 : ℚ) vp00000000000000100100 := by
  apply branch_left_normalized (c:=vp000000000000001001000) (k:=0) (m:=23) (by decide +kernel)
  rw [show 2*(-85778/15625 : ℚ) - ((0:ℤ):ℚ) = (-171556/15625 : ℚ) by norm_num]
  exact coverp000000000000001001000
private noncomputable def ep000000000000001001001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001001-E-0000.bin"
noncomputable def ep000000000000001001001 : Blocks := ep000000000000001001001_0
private theorem idp000000000000001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100100.list =
    C ((2:ℤ)^33) * horner X vp000000000000001001001.list + horner X ep000000000000001001001.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001001001 : Branch 1 (-85778/15625 : ℚ) vp00000000000000100100 := by
  apply branch_checked idp000000000000001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-85778/15625 : ℚ) - ((1:ℤ):ℚ) = (-187181/15625 : ℚ) by norm_num]
  exact coverp000000000000001001001
theorem coverp00000000000000100100 : Covers (-85778/15625 : ℚ) vp00000000000000100100 := join_branches bp000000000000001001000 bp000000000000001001001
private noncomputable def vp0000000000000010010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010010-V-0000.bin"
noncomputable def vp0000000000000010010 : Blocks := vp0000000000000010010_0
private theorem bp00000000000000100100 : Branch 0 (-42889/15625 : ℚ) vp0000000000000010010 := by
  apply branch_left_normalized (c:=vp00000000000000100100) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-42889/15625 : ℚ) - ((0:ℤ):ℚ) = (-85778/15625 : ℚ) by norm_num]
  exact coverp00000000000000100100
private noncomputable def ep00000000000000100101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100101-E-0000.bin"
noncomputable def ep00000000000000100101 : Blocks := ep00000000000000100101_0
private theorem idp00000000000000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010010.list =
    C ((2:ℤ)^50) * horner X vp00000000000000100101.list + horner X ep00000000000000100101.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100101 : Branch 1 (-42889/15625 : ℚ) vp0000000000000010010 := by
  apply branch_checked idp00000000000000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-42889/15625 : ℚ) - ((1:ℤ):ℚ) = (-101403/15625 : ℚ) by norm_num]
  exact coverp00000000000000100101
theorem coverp0000000000000010010 : Covers (-42889/15625 : ℚ) vp0000000000000010010 := join_branches bp00000000000000100100 bp00000000000000100101
private noncomputable def vp000000000000001001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001-V-0000.bin"
noncomputable def vp000000000000001001 : Blocks := vp000000000000001001_0
private theorem bp0000000000000010010 : Branch 0 (-42889/31250 : ℚ) vp000000000000001001 := by
  apply branch_left_normalized (c:=vp0000000000000010010) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-42889/31250 : ℚ) - ((0:ℤ):ℚ) = (-42889/15625 : ℚ) by norm_num]
  exact coverp0000000000000010010
private noncomputable def ep0000000000000010011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010011-E-0000.bin"
noncomputable def ep0000000000000010011 : Blocks := ep0000000000000010011_0
private theorem idp0000000000000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001001.list =
    C ((2:ℤ)^81) * horner X vp0000000000000010011.list + horner X ep0000000000000010011.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010011 : Branch 1 (-42889/31250 : ℚ) vp000000000000001001 := by
  apply branch_checked idp0000000000000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-42889/31250 : ℚ) - ((1:ℤ):ℚ) = (-58514/15625 : ℚ) by norm_num]
  exact coverp0000000000000010011
theorem coverp000000000000001001 : Covers (-42889/31250 : ℚ) vp000000000000001001 := join_branches bp0000000000000010010 bp0000000000000010011
private noncomputable def vp00000000000000100011111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100011111-V-0000.bin"
noncomputable def vp00000000000000100011111 : Blocks := vp00000000000000100011111_0
theorem coverp00000000000000100011111 : Covers (-670599/15625 : ℚ) vp00000000000000100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100011110_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100011110-V-0000.bin"
noncomputable def vp00000000000000100011110 : Blocks := vp00000000000000100011110_0
theorem coverp00000000000000100011110 : Covers (-654974/15625 : ℚ) vp00000000000000100011110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001111-V-0000.bin"
noncomputable def vp0000000000000010001111 : Blocks := vp0000000000000010001111_0
private theorem bp00000000000000100011110 : Branch 0 (-327487/15625 : ℚ) vp0000000000000010001111 := by
  apply branch_left_normalized (c:=vp00000000000000100011110) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-327487/15625 : ℚ) - ((0:ℤ):ℚ) = (-654974/15625 : ℚ) by norm_num]
  exact coverp00000000000000100011110
private noncomputable def ep00000000000000100011111_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100011111-E-0000.bin"
noncomputable def ep00000000000000100011111 : Blocks := ep00000000000000100011111_0
private theorem idp00000000000000100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010001111.list =
    C ((2:ℤ)^17) * horner X vp00000000000000100011111.list + horner X ep00000000000000100011111.list := by
  exact edge_identity (B := (2:ℤ)^112) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100011111 : Branch 1 (-327487/15625 : ℚ) vp0000000000000010001111 := by
  apply branch_checked idp00000000000000100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-327487/15625 : ℚ) - ((1:ℤ):ℚ) = (-670599/15625 : ℚ) by norm_num]
  exact coverp00000000000000100011111
theorem coverp0000000000000010001111 : Covers (-327487/15625 : ℚ) vp0000000000000010001111 := join_branches bp00000000000000100011110 bp00000000000000100011111
private noncomputable def vp0000000000000010001110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001110-V-0000.bin"
noncomputable def vp0000000000000010001110 : Blocks := vp0000000000000010001110_0
theorem coverp0000000000000010001110 : Covers (-311862/15625 : ℚ) vp0000000000000010001110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001000111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000111-V-0000.bin"
noncomputable def vp000000000000001000111 : Blocks := vp000000000000001000111_0
private theorem bp0000000000000010001110 : Branch 0 (-155931/15625 : ℚ) vp000000000000001000111 := by
  apply branch_left_normalized (c:=vp0000000000000010001110) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-155931/15625 : ℚ) - ((0:ℤ):ℚ) = (-311862/15625 : ℚ) by norm_num]
  exact coverp0000000000000010001110
private noncomputable def ep0000000000000010001111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001111-E-0000.bin"
noncomputable def ep0000000000000010001111 : Blocks := ep0000000000000010001111_0
private theorem idp0000000000000010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001000111.list =
    C ((2:ℤ)^23) * horner X vp0000000000000010001111.list + horner X ep0000000000000010001111.list := by
  exact edge_identity (B := (2:ℤ)^119) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010001111 : Branch 1 (-155931/15625 : ℚ) vp000000000000001000111 := by
  apply branch_checked idp0000000000000010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-155931/15625 : ℚ) - ((1:ℤ):ℚ) = (-327487/15625 : ℚ) by norm_num]
  exact coverp0000000000000010001111
theorem coverp000000000000001000111 : Covers (-155931/15625 : ℚ) vp000000000000001000111 := join_branches bp0000000000000010001110 bp0000000000000010001111
private noncomputable def vp000000000000001000110_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000110-V-0000.bin"
noncomputable def vp000000000000001000110 : Blocks := vp000000000000001000110_0
theorem coverp000000000000001000110 : Covers (-140306/15625 : ℚ) vp000000000000001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100011-V-0000.bin"
noncomputable def vp00000000000000100011 : Blocks := vp00000000000000100011_0
private theorem bp000000000000001000110 : Branch 0 (-70153/15625 : ℚ) vp00000000000000100011 := by
  apply branch_left_normalized (c:=vp000000000000001000110) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-70153/15625 : ℚ) - ((0:ℤ):ℚ) = (-140306/15625 : ℚ) by norm_num]
  exact coverp000000000000001000110
private noncomputable def ep000000000000001000111_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000111-E-0000.bin"
noncomputable def ep000000000000001000111 : Blocks := ep000000000000001000111_0
private theorem idp000000000000001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100011.list =
    C ((2:ℤ)^32) * horner X vp000000000000001000111.list + horner X ep000000000000001000111.list := by
  exact edge_identity (B := (2:ℤ)^131) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001000111 : Branch 1 (-70153/15625 : ℚ) vp00000000000000100011 := by
  apply branch_checked idp000000000000001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-70153/15625 : ℚ) - ((1:ℤ):ℚ) = (-155931/15625 : ℚ) by norm_num]
  exact coverp000000000000001000111
theorem coverp00000000000000100011 : Covers (-70153/15625 : ℚ) vp00000000000000100011 := join_branches bp000000000000001000110 bp000000000000001000111
private noncomputable def vp0000000000000010001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001011-V-0000.bin"
noncomputable def vp0000000000000010001011 : Blocks := vp0000000000000010001011_0
theorem coverp0000000000000010001011 : Covers (-264987/15625 : ℚ) vp0000000000000010001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001000101011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000101011-V-0000.bin"
noncomputable def vp000000000000001000101011 : Blocks := vp000000000000001000101011_0
theorem coverp000000000000001000101011 : Covers (-1044323/15625 : ℚ) vp000000000000001000101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010001010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001010101-V-0000.bin"
noncomputable def vp0000000000000010001010101 : Blocks := vp0000000000000010001010101_0
theorem coverp0000000000000010001010101 : Covers (-2073021/15625 : ℚ) vp0000000000000010001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010001010100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001010100-V-0000.bin"
noncomputable def vp0000000000000010001010100 : Blocks := vp0000000000000010001010100_0
theorem coverp0000000000000010001010100 : Covers (-2057396/15625 : ℚ) vp0000000000000010001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001000101010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000101010-V-0000.bin"
noncomputable def vp000000000000001000101010 : Blocks := vp000000000000001000101010_0
private theorem bp0000000000000010001010100 : Branch 0 (-1028698/15625 : ℚ) vp000000000000001000101010 := by
  apply branch_left_normalized (c:=vp0000000000000010001010100) (k:=0) (m:=10) (by decide +kernel)
  rw [show 2*(-1028698/15625 : ℚ) - ((0:ℤ):ℚ) = (-2057396/15625 : ℚ) by norm_num]
  exact coverp0000000000000010001010100
private noncomputable def ep0000000000000010001010101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001010101-E-0000.bin"
noncomputable def ep0000000000000010001010101 : Blocks := ep0000000000000010001010101_0
private theorem idp0000000000000010001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001000101010.list =
    C ((2:ℤ)^12) * horner X vp0000000000000010001010101.list + horner X ep0000000000000010001010101.list := by
  exact edge_identity (B := (2:ℤ)^104) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010001010101 : Branch 1 (-1028698/15625 : ℚ) vp000000000000001000101010 := by
  apply branch_checked idp0000000000000010001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1028698/15625 : ℚ) - ((1:ℤ):ℚ) = (-2073021/15625 : ℚ) by norm_num]
  exact coverp0000000000000010001010101
theorem coverp000000000000001000101010 : Covers (-1028698/15625 : ℚ) vp000000000000001000101010 := join_branches bp0000000000000010001010100 bp0000000000000010001010101
private noncomputable def vp00000000000000100010101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100010101-V-0000.bin"
noncomputable def vp00000000000000100010101 : Blocks := vp00000000000000100010101_0
private theorem bp000000000000001000101010 : Branch 0 (-514349/15625 : ℚ) vp00000000000000100010101 := by
  apply branch_left_normalized (c:=vp000000000000001000101010) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-514349/15625 : ℚ) - ((0:ℤ):ℚ) = (-1028698/15625 : ℚ) by norm_num]
  exact coverp000000000000001000101010
private noncomputable def ep000000000000001000101011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000101011-E-0000.bin"
noncomputable def ep000000000000001000101011 : Blocks := ep000000000000001000101011_0
private theorem idp000000000000001000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100010101.list =
    C ((2:ℤ)^15) * horner X vp000000000000001000101011.list + horner X ep000000000000001000101011.list := by
  exact edge_identity (B := (2:ℤ)^108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001000101011 : Branch 1 (-514349/15625 : ℚ) vp00000000000000100010101 := by
  apply branch_checked idp000000000000001000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-514349/15625 : ℚ) - ((1:ℤ):ℚ) = (-1044323/15625 : ℚ) by norm_num]
  exact coverp000000000000001000101011
theorem coverp00000000000000100010101 : Covers (-514349/15625 : ℚ) vp00000000000000100010101 := join_branches bp000000000000001000101010 bp000000000000001000101011
private noncomputable def vp000000000000001000101001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000101001-V-0000.bin"
noncomputable def vp000000000000001000101001 : Blocks := vp000000000000001000101001_0
theorem coverp000000000000001000101001 : Covers (-1013073/15625 : ℚ) vp000000000000001000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001000101000_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000101000-V-0000.bin"
noncomputable def vp000000000000001000101000 : Blocks := vp000000000000001000101000_0
theorem coverp000000000000001000101000 : Covers (-997448/15625 : ℚ) vp000000000000001000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100010100_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100010100-V-0000.bin"
noncomputable def vp00000000000000100010100 : Blocks := vp00000000000000100010100_0
private theorem bp000000000000001000101000 : Branch 0 (-498724/15625 : ℚ) vp00000000000000100010100 := by
  apply branch_left_normalized (c:=vp000000000000001000101000) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-498724/15625 : ℚ) - ((0:ℤ):ℚ) = (-997448/15625 : ℚ) by norm_num]
  exact coverp000000000000001000101000
private noncomputable def ep000000000000001000101001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000101001-E-0000.bin"
noncomputable def ep000000000000001000101001 : Blocks := ep000000000000001000101001_0
private theorem idp000000000000001000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100010100.list =
    C ((2:ℤ)^14) * horner X vp000000000000001000101001.list + horner X ep000000000000001000101001.list := by
  exact edge_identity (B := (2:ℤ)^108) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001000101001 : Branch 1 (-498724/15625 : ℚ) vp00000000000000100010100 := by
  apply branch_checked idp000000000000001000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-498724/15625 : ℚ) - ((1:ℤ):ℚ) = (-1013073/15625 : ℚ) by norm_num]
  exact coverp000000000000001000101001
theorem coverp00000000000000100010100 : Covers (-498724/15625 : ℚ) vp00000000000000100010100 := join_branches bp000000000000001000101000 bp000000000000001000101001
private noncomputable def vp0000000000000010001010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001010-V-0000.bin"
noncomputable def vp0000000000000010001010 : Blocks := vp0000000000000010001010_0
private theorem bp00000000000000100010100 : Branch 0 (-249362/15625 : ℚ) vp0000000000000010001010 := by
  apply branch_left_normalized (c:=vp00000000000000100010100) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-249362/15625 : ℚ) - ((0:ℤ):ℚ) = (-498724/15625 : ℚ) by norm_num]
  exact coverp00000000000000100010100
private noncomputable def ep00000000000000100010101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100010101-E-0000.bin"
noncomputable def ep00000000000000100010101 : Blocks := ep00000000000000100010101_0
private theorem idp00000000000000100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010001010.list =
    C ((2:ℤ)^18) * horner X vp00000000000000100010101.list + horner X ep00000000000000100010101.list := by
  exact edge_identity (B := (2:ℤ)^113) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100010101 : Branch 1 (-249362/15625 : ℚ) vp0000000000000010001010 := by
  apply branch_checked idp00000000000000100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-249362/15625 : ℚ) - ((1:ℤ):ℚ) = (-514349/15625 : ℚ) by norm_num]
  exact coverp00000000000000100010101
theorem coverp0000000000000010001010 : Covers (-249362/15625 : ℚ) vp0000000000000010001010 := join_branches bp00000000000000100010100 bp00000000000000100010101
private noncomputable def vp000000000000001000101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000101-V-0000.bin"
noncomputable def vp000000000000001000101 : Blocks := vp000000000000001000101_0
private theorem bp0000000000000010001010 : Branch 0 (-124681/15625 : ℚ) vp000000000000001000101 := by
  apply branch_left_normalized (c:=vp0000000000000010001010) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-124681/15625 : ℚ) - ((0:ℤ):ℚ) = (-249362/15625 : ℚ) by norm_num]
  exact coverp0000000000000010001010
private noncomputable def ep0000000000000010001011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001011-E-0000.bin"
noncomputable def ep0000000000000010001011 : Blocks := ep0000000000000010001011_0
private theorem idp0000000000000010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001000101.list =
    C ((2:ℤ)^24) * horner X vp0000000000000010001011.list + horner X ep0000000000000010001011.list := by
  exact edge_identity (B := (2:ℤ)^121) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010001011 : Branch 1 (-124681/15625 : ℚ) vp000000000000001000101 := by
  apply branch_checked idp0000000000000010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-124681/15625 : ℚ) - ((1:ℤ):ℚ) = (-264987/15625 : ℚ) by norm_num]
  exact coverp0000000000000010001011
theorem coverp000000000000001000101 : Covers (-124681/15625 : ℚ) vp000000000000001000101 := join_branches bp0000000000000010001010 bp0000000000000010001011
private noncomputable def vp0000000000000010001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001001-V-0000.bin"
noncomputable def vp0000000000000010001001 : Blocks := vp0000000000000010001001_0
theorem coverp0000000000000010001001 : Covers (-233737/15625 : ℚ) vp0000000000000010001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010001000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001000-V-0000.bin"
noncomputable def vp0000000000000010001000 : Blocks := vp0000000000000010001000_0
theorem coverp0000000000000010001000 : Covers (-218112/15625 : ℚ) vp0000000000000010001000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001000100_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000100-V-0000.bin"
noncomputable def vp000000000000001000100 : Blocks := vp000000000000001000100_0
private theorem bp0000000000000010001000 : Branch 0 (-109056/15625 : ℚ) vp000000000000001000100 := by
  apply branch_left_normalized (c:=vp0000000000000010001000) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-109056/15625 : ℚ) - ((0:ℤ):ℚ) = (-218112/15625 : ℚ) by norm_num]
  exact coverp0000000000000010001000
private noncomputable def ep0000000000000010001001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001001-E-0000.bin"
noncomputable def ep0000000000000010001001 : Blocks := ep0000000000000010001001_0
private theorem idp0000000000000010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001000100.list =
    C ((2:ℤ)^23) * horner X vp0000000000000010001001.list + horner X ep0000000000000010001001.list := by
  exact edge_identity (B := (2:ℤ)^120) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010001001 : Branch 1 (-109056/15625 : ℚ) vp000000000000001000100 := by
  apply branch_checked idp0000000000000010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-109056/15625 : ℚ) - ((1:ℤ):ℚ) = (-233737/15625 : ℚ) by norm_num]
  exact coverp0000000000000010001001
theorem coverp000000000000001000100 : Covers (-109056/15625 : ℚ) vp000000000000001000100 := join_branches bp0000000000000010001000 bp0000000000000010001001
private noncomputable def vp00000000000000100010_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100010-V-0000.bin"
noncomputable def vp00000000000000100010 : Blocks := vp00000000000000100010_0
private theorem bp000000000000001000100 : Branch 0 (-54528/15625 : ℚ) vp00000000000000100010 := by
  apply branch_left_normalized (c:=vp000000000000001000100) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-54528/15625 : ℚ) - ((0:ℤ):ℚ) = (-109056/15625 : ℚ) by norm_num]
  exact coverp000000000000001000100
private noncomputable def ep000000000000001000101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000101-E-0000.bin"
noncomputable def ep000000000000001000101 : Blocks := ep000000000000001000101_0
private theorem idp000000000000001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100010.list =
    C ((2:ℤ)^32) * horner X vp000000000000001000101.list + horner X ep000000000000001000101.list := by
  exact edge_identity (B := (2:ℤ)^132) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001000101 : Branch 1 (-54528/15625 : ℚ) vp00000000000000100010 := by
  apply branch_checked idp000000000000001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-54528/15625 : ℚ) - ((1:ℤ):ℚ) = (-124681/15625 : ℚ) by norm_num]
  exact coverp000000000000001000101
theorem coverp00000000000000100010 : Covers (-54528/15625 : ℚ) vp00000000000000100010 := join_branches bp000000000000001000100 bp000000000000001000101
private noncomputable def vp0000000000000010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001-V-0000.bin"
noncomputable def vp0000000000000010001 : Blocks := vp0000000000000010001_0
private theorem bp00000000000000100010 : Branch 0 (-27264/15625 : ℚ) vp0000000000000010001 := by
  apply branch_left_normalized (c:=vp00000000000000100010) (k:=0) (m:=31) (by decide +kernel)
  rw [show 2*(-27264/15625 : ℚ) - ((0:ℤ):ℚ) = (-54528/15625 : ℚ) by norm_num]
  exact coverp00000000000000100010
private noncomputable def ep00000000000000100011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100011-E-0000.bin"
noncomputable def ep00000000000000100011 : Blocks := ep00000000000000100011_0
private theorem idp00000000000000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010001.list =
    C ((2:ℤ)^49) * horner X vp00000000000000100011.list + horner X ep00000000000000100011.list := by
  exact edge_identity (B := (2:ℤ)^155) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100011 : Branch 1 (-27264/15625 : ℚ) vp0000000000000010001 := by
  apply branch_checked idp00000000000000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-27264/15625 : ℚ) - ((1:ℤ):ℚ) = (-70153/15625 : ℚ) by norm_num]
  exact coverp00000000000000100011
theorem coverp0000000000000010001 : Covers (-27264/15625 : ℚ) vp0000000000000010001 := join_branches bp00000000000000100010 bp00000000000000100011
private noncomputable def vp000000000000001000011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000011-V-0000.bin"
noncomputable def vp000000000000001000011 : Blocks := vp000000000000001000011_0
theorem coverp000000000000001000011 : Covers (-93431/15625 : ℚ) vp000000000000001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100001011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100001011-V-0000.bin"
noncomputable def vp00000000000000100001011 : Blocks := vp00000000000000100001011_0
theorem coverp00000000000000100001011 : Covers (-358099/15625 : ℚ) vp00000000000000100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001000010101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000010101-V-0000.bin"
noncomputable def vp000000000000001000010101 : Blocks := vp000000000000001000010101_0
theorem coverp000000000000001000010101 : Covers (-700573/15625 : ℚ) vp000000000000001000010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010000101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000101001-V-0000.bin"
noncomputable def vp0000000000000010000101001 : Blocks := vp0000000000000010000101001_0
theorem coverp0000000000000010000101001 : Covers (-1385521/15625 : ℚ) vp0000000000000010000101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010000101000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000101000-V-0000.bin"
noncomputable def vp0000000000000010000101000 : Blocks := vp0000000000000010000101000_0
theorem coverp0000000000000010000101000 : Covers (-1369896/15625 : ℚ) vp0000000000000010000101000 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001000010100_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000010100-V-0000.bin"
noncomputable def vp000000000000001000010100 : Blocks := vp000000000000001000010100_0
private theorem bp0000000000000010000101000 : Branch 0 (-684948/15625 : ℚ) vp000000000000001000010100 := by
  apply branch_left_normalized (c:=vp0000000000000010000101000) (k:=0) (m:=9) (by decide +kernel)
  rw [show 2*(-684948/15625 : ℚ) - ((0:ℤ):ℚ) = (-1369896/15625 : ℚ) by norm_num]
  exact coverp0000000000000010000101000
private noncomputable def ep0000000000000010000101001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000101001-E-0000.bin"
noncomputable def ep0000000000000010000101001 : Blocks := ep0000000000000010000101001_0
private theorem idp0000000000000010000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001000010100.list =
    C ((2:ℤ)^12) * horner X vp0000000000000010000101001.list + horner X ep0000000000000010000101001.list := by
  exact edge_identity (B := (2:ℤ)^104) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010000101001 : Branch 1 (-684948/15625 : ℚ) vp000000000000001000010100 := by
  apply branch_checked idp0000000000000010000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-684948/15625 : ℚ) - ((1:ℤ):ℚ) = (-1385521/15625 : ℚ) by norm_num]
  exact coverp0000000000000010000101001
theorem coverp000000000000001000010100 : Covers (-684948/15625 : ℚ) vp000000000000001000010100 := join_branches bp0000000000000010000101000 bp0000000000000010000101001
private noncomputable def vp00000000000000100001010_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100001010-V-0000.bin"
noncomputable def vp00000000000000100001010 : Blocks := vp00000000000000100001010_0
private theorem bp000000000000001000010100 : Branch 0 (-342474/15625 : ℚ) vp00000000000000100001010 := by
  apply branch_left_normalized (c:=vp000000000000001000010100) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-342474/15625 : ℚ) - ((0:ℤ):ℚ) = (-684948/15625 : ℚ) by norm_num]
  exact coverp000000000000001000010100
private noncomputable def ep000000000000001000010101_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000010101-E-0000.bin"
noncomputable def ep000000000000001000010101 : Blocks := ep000000000000001000010101_0
private theorem idp000000000000001000010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100001010.list =
    C ((2:ℤ)^15) * horner X vp000000000000001000010101.list + horner X ep000000000000001000010101.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001000010101 : Branch 1 (-342474/15625 : ℚ) vp00000000000000100001010 := by
  apply branch_checked idp000000000000001000010101 (by positivity) (by decide +kernel)
  rw [show 2*(-342474/15625 : ℚ) - ((1:ℤ):ℚ) = (-700573/15625 : ℚ) by norm_num]
  exact coverp000000000000001000010101
theorem coverp00000000000000100001010 : Covers (-342474/15625 : ℚ) vp00000000000000100001010 := join_branches bp000000000000001000010100 bp000000000000001000010101
private noncomputable def vp0000000000000010000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000101-V-0000.bin"
noncomputable def vp0000000000000010000101 : Blocks := vp0000000000000010000101_0
private theorem bp00000000000000100001010 : Branch 0 (-171237/15625 : ℚ) vp0000000000000010000101 := by
  apply branch_left_normalized (c:=vp00000000000000100001010) (k:=0) (m:=14) (by decide +kernel)
  rw [show 2*(-171237/15625 : ℚ) - ((0:ℤ):ℚ) = (-342474/15625 : ℚ) by norm_num]
  exact coverp00000000000000100001010
private noncomputable def ep00000000000000100001011_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100001011-E-0000.bin"
noncomputable def ep00000000000000100001011 : Blocks := ep00000000000000100001011_0
private theorem idp00000000000000100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010000101.list =
    C ((2:ℤ)^19) * horner X vp00000000000000100001011.list + horner X ep00000000000000100001011.list := by
  exact edge_identity (B := (2:ℤ)^114) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100001011 : Branch 1 (-171237/15625 : ℚ) vp0000000000000010000101 := by
  apply branch_checked idp00000000000000100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-171237/15625 : ℚ) - ((1:ℤ):ℚ) = (-358099/15625 : ℚ) by norm_num]
  exact coverp00000000000000100001011
theorem coverp0000000000000010000101 : Covers (-171237/15625 : ℚ) vp0000000000000010000101 := join_branches bp00000000000000100001010 bp00000000000000100001011
private noncomputable def vp0000000000000010000100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000100111-V-0000.bin"
noncomputable def vp0000000000000010000100111 : Blocks := vp0000000000000010000100111_0
theorem coverp0000000000000010000100111 : Covers (-1354271/15625 : ℚ) vp0000000000000010000100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010000100110_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000100110-V-0000.bin"
noncomputable def vp0000000000000010000100110 : Blocks := vp0000000000000010000100110_0
theorem coverp0000000000000010000100110 : Covers (-1338646/15625 : ℚ) vp0000000000000010000100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001000010011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000010011-V-0000.bin"
noncomputable def vp000000000000001000010011 : Blocks := vp000000000000001000010011_0
private theorem bp0000000000000010000100110 : Branch 0 (-669323/15625 : ℚ) vp000000000000001000010011 := by
  apply branch_left_normalized (c:=vp0000000000000010000100110) (k:=0) (m:=9) (by decide +kernel)
  rw [show 2*(-669323/15625 : ℚ) - ((0:ℤ):ℚ) = (-1338646/15625 : ℚ) by norm_num]
  exact coverp0000000000000010000100110
private noncomputable def ep0000000000000010000100111_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000100111-E-0000.bin"
noncomputable def ep0000000000000010000100111 : Blocks := ep0000000000000010000100111_0
private theorem idp0000000000000010000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001000010011.list =
    C ((2:ℤ)^12) * horner X vp0000000000000010000100111.list + horner X ep0000000000000010000100111.list := by
  exact edge_identity (B := (2:ℤ)^106) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010000100111 : Branch 1 (-669323/15625 : ℚ) vp000000000000001000010011 := by
  apply branch_checked idp0000000000000010000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-669323/15625 : ℚ) - ((1:ℤ):ℚ) = (-1354271/15625 : ℚ) by norm_num]
  exact coverp0000000000000010000100111
theorem coverp000000000000001000010011 : Covers (-669323/15625 : ℚ) vp000000000000001000010011 := join_branches bp0000000000000010000100110 bp0000000000000010000100111
private noncomputable def vp000000000000001000010010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000010010-V-0000.bin"
noncomputable def vp000000000000001000010010 : Blocks := vp000000000000001000010010_0
theorem coverp000000000000001000010010 : Covers (-653698/15625 : ℚ) vp000000000000001000010010 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100001001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100001001-V-0000.bin"
noncomputable def vp00000000000000100001001 : Blocks := vp00000000000000100001001_0
private theorem bp000000000000001000010010 : Branch 0 (-326849/15625 : ℚ) vp00000000000000100001001 := by
  apply branch_left_normalized (c:=vp000000000000001000010010) (k:=0) (m:=11) (by decide +kernel)
  rw [show 2*(-326849/15625 : ℚ) - ((0:ℤ):ℚ) = (-653698/15625 : ℚ) by norm_num]
  exact coverp000000000000001000010010
private noncomputable def ep000000000000001000010011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000010011-E-0000.bin"
noncomputable def ep000000000000001000010011 : Blocks := ep000000000000001000010011_0
private theorem idp000000000000001000010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100001001.list =
    C ((2:ℤ)^14) * horner X vp000000000000001000010011.list + horner X ep000000000000001000010011.list := by
  exact edge_identity (B := (2:ℤ)^109) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001000010011 : Branch 1 (-326849/15625 : ℚ) vp00000000000000100001001 := by
  apply branch_checked idp000000000000001000010011 (by positivity) (by decide +kernel)
  rw [show 2*(-326849/15625 : ℚ) - ((1:ℤ):ℚ) = (-669323/15625 : ℚ) by norm_num]
  exact coverp000000000000001000010011
theorem coverp00000000000000100001001 : Covers (-326849/15625 : ℚ) vp00000000000000100001001 := join_branches bp000000000000001000010010 bp000000000000001000010011
private noncomputable def vp00000000000000100001000_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100001000-V-0000.bin"
noncomputable def vp00000000000000100001000 : Blocks := vp00000000000000100001000_0
theorem coverp00000000000000100001000 : Covers (-311224/15625 : ℚ) vp00000000000000100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010000100_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000100-V-0000.bin"
noncomputable def vp0000000000000010000100 : Blocks := vp0000000000000010000100_0
private theorem bp00000000000000100001000 : Branch 0 (-155612/15625 : ℚ) vp0000000000000010000100 := by
  apply branch_left_normalized (c:=vp00000000000000100001000) (k:=0) (m:=13) (by decide +kernel)
  rw [show 2*(-155612/15625 : ℚ) - ((0:ℤ):ℚ) = (-311224/15625 : ℚ) by norm_num]
  exact coverp00000000000000100001000
private noncomputable def ep00000000000000100001001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100001001-E-0000.bin"
noncomputable def ep00000000000000100001001 : Blocks := ep00000000000000100001001_0
private theorem idp00000000000000100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010000100.list =
    C ((2:ℤ)^18) * horner X vp00000000000000100001001.list + horner X ep00000000000000100001001.list := by
  exact edge_identity (B := (2:ℤ)^115) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100001001 : Branch 1 (-155612/15625 : ℚ) vp0000000000000010000100 := by
  apply branch_checked idp00000000000000100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-155612/15625 : ℚ) - ((1:ℤ):ℚ) = (-326849/15625 : ℚ) by norm_num]
  exact coverp00000000000000100001001
theorem coverp0000000000000010000100 : Covers (-155612/15625 : ℚ) vp0000000000000010000100 := join_branches bp00000000000000100001000 bp00000000000000100001001
private noncomputable def vp000000000000001000010_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000010-V-0000.bin"
noncomputable def vp000000000000001000010 : Blocks := vp000000000000001000010_0
private theorem bp0000000000000010000100 : Branch 0 (-77806/15625 : ℚ) vp000000000000001000010 := by
  apply branch_left_normalized (c:=vp0000000000000010000100) (k:=0) (m:=17) (by decide +kernel)
  rw [show 2*(-77806/15625 : ℚ) - ((0:ℤ):ℚ) = (-155612/15625 : ℚ) by norm_num]
  exact coverp0000000000000010000100
private noncomputable def ep0000000000000010000101_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000101-E-0000.bin"
noncomputable def ep0000000000000010000101 : Blocks := ep0000000000000010000101_0
private theorem idp0000000000000010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001000010.list =
    C ((2:ℤ)^22) * horner X vp0000000000000010000101.list + horner X ep0000000000000010000101.list := by
  exact edge_identity (B := (2:ℤ)^120) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010000101 : Branch 1 (-77806/15625 : ℚ) vp000000000000001000010 := by
  apply branch_checked idp0000000000000010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-77806/15625 : ℚ) - ((1:ℤ):ℚ) = (-171237/15625 : ℚ) by norm_num]
  exact coverp0000000000000010000101
theorem coverp000000000000001000010 : Covers (-77806/15625 : ℚ) vp000000000000001000010 := join_branches bp0000000000000010000100 bp0000000000000010000101
private noncomputable def vp00000000000000100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100001-V-0000.bin"
noncomputable def vp00000000000000100001 : Blocks := vp00000000000000100001_0
private theorem bp000000000000001000010 : Branch 0 (-38903/15625 : ℚ) vp00000000000000100001 := by
  apply branch_left_normalized (c:=vp000000000000001000010) (k:=0) (m:=21) (by decide +kernel)
  rw [show 2*(-38903/15625 : ℚ) - ((0:ℤ):ℚ) = (-77806/15625 : ℚ) by norm_num]
  exact coverp000000000000001000010
private noncomputable def ep000000000000001000011_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000011-E-0000.bin"
noncomputable def ep000000000000001000011 : Blocks := ep000000000000001000011_0
private theorem idp000000000000001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100001.list =
    C ((2:ℤ)^32) * horner X vp000000000000001000011.list + horner X ep000000000000001000011.list := by
  exact edge_identity (B := (2:ℤ)^133) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001000011 : Branch 1 (-38903/15625 : ℚ) vp00000000000000100001 := by
  apply branch_checked idp000000000000001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-38903/15625 : ℚ) - ((1:ℤ):ℚ) = (-93431/15625 : ℚ) by norm_num]
  exact coverp000000000000001000011
theorem coverp00000000000000100001 : Covers (-38903/15625 : ℚ) vp00000000000000100001 := join_branches bp000000000000001000010 bp000000000000001000011
private noncomputable def vp0000000000000010000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000011-V-0000.bin"
noncomputable def vp0000000000000010000011 : Blocks := vp0000000000000010000011_0
theorem coverp0000000000000010000011 : Covers (-139987/15625 : ℚ) vp0000000000000010000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000000000000010000010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000010-V-0000.bin"
noncomputable def vp0000000000000010000010 : Blocks := vp0000000000000010000010_0
theorem coverp0000000000000010000010 : Covers (-124362/15625 : ℚ) vp0000000000000010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp000000000000001000001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000001-V-0000.bin"
noncomputable def vp000000000000001000001 : Blocks := vp000000000000001000001_0
private theorem bp0000000000000010000010 : Branch 0 (-62181/15625 : ℚ) vp000000000000001000001 := by
  apply branch_left_normalized (c:=vp0000000000000010000010) (k:=0) (m:=16) (by decide +kernel)
  rw [show 2*(-62181/15625 : ℚ) - ((0:ℤ):ℚ) = (-124362/15625 : ℚ) by norm_num]
  exact coverp0000000000000010000010
private noncomputable def ep0000000000000010000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000011-E-0000.bin"
noncomputable def ep0000000000000010000011 : Blocks := ep0000000000000010000011_0
private theorem idp0000000000000010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001000001.list =
    C ((2:ℤ)^22) * horner X vp0000000000000010000011.list + horner X ep0000000000000010000011.list := by
  exact edge_identity (B := (2:ℤ)^121) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010000011 : Branch 1 (-62181/15625 : ℚ) vp000000000000001000001 := by
  apply branch_checked idp0000000000000010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-62181/15625 : ℚ) - ((1:ℤ):ℚ) = (-139987/15625 : ℚ) by norm_num]
  exact coverp0000000000000010000011
theorem coverp000000000000001000001 : Covers (-62181/15625 : ℚ) vp000000000000001000001 := join_branches bp0000000000000010000010 bp0000000000000010000011
private noncomputable def vp000000000000001000000_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000000-V-0000.bin"
noncomputable def vp000000000000001000000 : Blocks := vp000000000000001000000_0
theorem coverp000000000000001000000 : Covers (-46556/15625 : ℚ) vp000000000000001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp00000000000000100000_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100000-V-0000.bin"
noncomputable def vp00000000000000100000 : Blocks := vp00000000000000100000_0
private theorem bp000000000000001000000 : Branch 0 (-23278/15625 : ℚ) vp00000000000000100000 := by
  apply branch_left_normalized (c:=vp000000000000001000000) (k:=0) (m:=22) (by decide +kernel)
  rw [show 2*(-23278/15625 : ℚ) - ((0:ℤ):ℚ) = (-46556/15625 : ℚ) by norm_num]
  exact coverp000000000000001000000
private noncomputable def ep000000000000001000001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000001-E-0000.bin"
noncomputable def ep000000000000001000001 : Blocks := ep000000000000001000001_0
private theorem idp000000000000001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100000.list =
    C ((2:ℤ)^33) * horner X vp000000000000001000001.list + horner X ep000000000000001000001.list := by
  exact edge_identity (B := (2:ℤ)^135) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001000001 : Branch 1 (-23278/15625 : ℚ) vp00000000000000100000 := by
  apply branch_checked idp000000000000001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-23278/15625 : ℚ) - ((1:ℤ):ℚ) = (-62181/15625 : ℚ) by norm_num]
  exact coverp000000000000001000001
theorem coverp00000000000000100000 : Covers (-23278/15625 : ℚ) vp00000000000000100000 := join_branches bp000000000000001000000 bp000000000000001000001
private noncomputable def vp0000000000000010000_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010000-V-0000.bin"
noncomputable def vp0000000000000010000 : Blocks := vp0000000000000010000_0
private theorem bp00000000000000100000 : Branch 0 (-11639/15625 : ℚ) vp0000000000000010000 := by
  apply branch_left_normalized (c:=vp00000000000000100000) (k:=0) (m:=32) (by decide +kernel)
  rw [show 2*(-11639/15625 : ℚ) - ((0:ℤ):ℚ) = (-23278/15625 : ℚ) by norm_num]
  exact coverp00000000000000100000
private noncomputable def ep00000000000000100001_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100001-E-0000.bin"
noncomputable def ep00000000000000100001 : Blocks := ep00000000000000100001_0
private theorem idp00000000000000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010000.list =
    C ((2:ℤ)^50) * horner X vp00000000000000100001.list + horner X ep00000000000000100001.list := by
  exact edge_identity (B := (2:ℤ)^158) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000100001 : Branch 1 (-11639/15625 : ℚ) vp0000000000000010000 := by
  apply branch_checked idp00000000000000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-11639/15625 : ℚ) - ((1:ℤ):ℚ) = (-38903/15625 : ℚ) by norm_num]
  exact coverp00000000000000100001
theorem coverp0000000000000010000 : Covers (-11639/15625 : ℚ) vp0000000000000010000 := join_branches bp00000000000000100000 bp00000000000000100001
private noncomputable def vp000000000000001000_0 : Blocks := edgeBlocks% "full/vectors/000000000000001000-V-0000.bin"
noncomputable def vp000000000000001000 : Blocks := vp000000000000001000_0
private theorem bp0000000000000010000 : Branch 0 (-11639/31250 : ℚ) vp000000000000001000 := by
  apply branch_left_normalized (c:=vp0000000000000010000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-11639/31250 : ℚ) - ((0:ℤ):ℚ) = (-11639/15625 : ℚ) by norm_num]
  exact coverp0000000000000010000
private noncomputable def ep0000000000000010001_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010001-E-0000.bin"
noncomputable def ep0000000000000010001 : Blocks := ep0000000000000010001_0
private theorem idp0000000000000010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001000.list =
    C ((2:ℤ)^82) * horner X vp0000000000000010001.list + horner X ep0000000000000010001.list := by
  exact edge_identity (B := (2:ℤ)^201) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000010001 : Branch 1 (-11639/31250 : ℚ) vp000000000000001000 := by
  apply branch_checked idp0000000000000010001 (by positivity) (by decide +kernel)
  rw [show 2*(-11639/31250 : ℚ) - ((1:ℤ):ℚ) = (-27264/15625 : ℚ) by norm_num]
  exact coverp0000000000000010001
theorem coverp000000000000001000 : Covers (-11639/31250 : ℚ) vp000000000000001000 := join_branches bp0000000000000010000 bp0000000000000010001
private noncomputable def vp00000000000000100_0 : Blocks := edgeBlocks% "full/vectors/00000000000000100-V-0000.bin"
private noncomputable def vp00000000000000100_1 : Blocks := edgeBlocks% "full/vectors/00000000000000100-V-0001.bin"
noncomputable def vp00000000000000100 : Blocks := (Blocks.join vp00000000000000100_0 vp00000000000000100_1)
private theorem bp000000000000001000 : Branch 0 (-11639/62500 : ℚ) vp00000000000000100 := by
  apply branch_left_normalized (c:=vp000000000000001000) (k:=0) (m:=81) (by decide +kernel)
  rw [show 2*(-11639/62500 : ℚ) - ((0:ℤ):ℚ) = (-11639/31250 : ℚ) by norm_num]
  exact coverp000000000000001000
private noncomputable def ep000000000000001001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001001-E-0000.bin"
private noncomputable def ep000000000000001001_1 : Blocks := edgeBlocks% "full/vectors/000000000000001001-E-0001.bin"
noncomputable def ep000000000000001001 : Blocks := (Blocks.join ep000000000000001001_0 ep000000000000001001_1)
private theorem idp000000000000001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00000000000000100.list =
    C ((2:ℤ)^144) * horner X vp000000000000001001.list + horner X ep000000000000001001.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000000000000001001 : Branch 1 (-11639/62500 : ℚ) vp00000000000000100 := by
  apply branch_checked idp000000000000001001 (by positivity) (by decide +kernel)
  rw [show 2*(-11639/62500 : ℚ) - ((1:ℤ):ℚ) = (-42889/31250 : ℚ) by norm_num]
  exact coverp000000000000001001
theorem coverp00000000000000100 : Covers (-11639/62500 : ℚ) vp00000000000000100 := join_branches bp000000000000001000 bp000000000000001001
private noncomputable def vp0000000000000010_0 : Blocks := edgeBlocks% "full/vectors/0000000000000010-V-0000.bin"
private noncomputable def vp0000000000000010_1 : Blocks := edgeBlocks% "full/vectors/0000000000000010-V-0001.bin"
private noncomputable def vp0000000000000010_2 : Blocks := edgeBlocks% "full/vectors/0000000000000010-V-0002.bin"
noncomputable def vp0000000000000010 : Blocks := (Blocks.join vp0000000000000010_0 (Blocks.join vp0000000000000010_1 vp0000000000000010_2))
private theorem bp00000000000000100 : Branch 0 (-11639/125000 : ℚ) vp0000000000000010 := by
  apply branch_left_normalized (c:=vp00000000000000100) (k:=0) (m:=143) (by decide +kernel)
  rw [show 2*(-11639/125000 : ℚ) - ((0:ℤ):ℚ) = (-11639/62500 : ℚ) by norm_num]
  exact coverp00000000000000100
private noncomputable def ep00000000000000101_0 : Blocks := edgeBlocks% "full/vectors/00000000000000101-E-0000.bin"
private noncomputable def ep00000000000000101_1 : Blocks := edgeBlocks% "full/vectors/00000000000000101-E-0001.bin"
private noncomputable def ep00000000000000101_2 : Blocks := edgeBlocks% "full/vectors/00000000000000101-E-0002.bin"
noncomputable def ep00000000000000101 : Blocks := (Blocks.join ep00000000000000101_0 (Blocks.join ep00000000000000101_1 ep00000000000000101_2))
private theorem idp00000000000000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000000000000010.list =
    C ((2:ℤ)^268) * horner X vp00000000000000101.list + horner X ep00000000000000101.list := by
  exact edge_identity (B := (2:ℤ)^482) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00000000000000101 : Branch 1 (-11639/125000 : ℚ) vp0000000000000010 := by
  apply branch_checked idp00000000000000101 (by positivity) (by decide +kernel)
  rw [show 2*(-11639/125000 : ℚ) - ((1:ℤ):ℚ) = (-74139/62500 : ℚ) by norm_num]
  exact coverp00000000000000101
theorem coverp0000000000000010 : Covers (-11639/125000 : ℚ) vp0000000000000010 := join_branches bp00000000000000100 bp00000000000000101
private noncomputable def vp000000000000001_0 : Blocks := edgeBlocks% "full/vectors/000000000000001-V-0000.bin"
private noncomputable def vp000000000000001_1 : Blocks := edgeBlocks% "full/vectors/000000000000001-V-0001.bin"
private noncomputable def vp000000000000001_2 : Blocks := edgeBlocks% "full/vectors/000000000000001-V-0002.bin"
private noncomputable def vp000000000000001_3 : Blocks := edgeBlocks% "full/vectors/000000000000001-V-0003.bin"
noncomputable def vp000000000000001 : Blocks := (Blocks.join (Blocks.join vp000000000000001_0 vp000000000000001_1) (Blocks.join vp000000000000001_2 vp000000000000001_3))
private theorem bp0000000000000010 : Branch 0 (-11639/250000 : ℚ) vp000000000000001 := by
  apply branch_left_normalized (c:=vp0000000000000010) (k:=0) (m:=267) (by decide +kernel)
  rw [show 2*(-11639/250000 : ℚ) - ((0:ℤ):ℚ) = (-11639/125000 : ℚ) by norm_num]
  exact coverp0000000000000010
private noncomputable def ep0000000000000011_0 : Blocks := edgeBlocks% "full/vectors/0000000000000011-E-0000.bin"
private noncomputable def ep0000000000000011_1 : Blocks := edgeBlocks% "full/vectors/0000000000000011-E-0001.bin"
private noncomputable def ep0000000000000011_2 : Blocks := edgeBlocks% "full/vectors/0000000000000011-E-0002.bin"
private noncomputable def ep0000000000000011_3 : Blocks := edgeBlocks% "full/vectors/0000000000000011-E-0003.bin"
noncomputable def ep0000000000000011 : Blocks := (Blocks.join (Blocks.join ep0000000000000011_0 ep0000000000000011_1) (Blocks.join ep0000000000000011_2 ep0000000000000011_3))
private theorem idp0000000000000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000000000000001.list =
    C ((2:ℤ)^460) * horner X vp0000000000000011.list + horner X ep0000000000000011.list := by
  exact edge_identity (B := (2:ℤ)^804) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000000000000011 : Branch 1 (-11639/250000 : ℚ) vp000000000000001 := by
  apply branch_checked idp0000000000000011 (by positivity) (by decide +kernel)
  rw [show 2*(-11639/250000 : ℚ) - ((1:ℤ):ℚ) = (-136639/125000 : ℚ) by norm_num]
  exact coverp0000000000000011
theorem coverp000000000000001 : Covers (-11639/250000 : ℚ) vp000000000000001 := join_branches bp0000000000000010 bp0000000000000011
end NextProof.EdgeFull

