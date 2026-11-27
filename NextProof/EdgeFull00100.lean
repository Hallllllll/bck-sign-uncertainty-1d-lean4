import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00099

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp001101011111_0 : Blocks := edgeBlocks% "full/vectors/001101011111-V-0000.bin"
noncomputable def vp001101011111 : Blocks := vp001101011111_0
theorem coverp001101011111 : Covers (-1725761639/2000000 : ℚ) vp001101011111 := cover_leaf (by decide +kernel)
private noncomputable def vp001101011110_0 : Blocks := edgeBlocks% "full/vectors/001101011110-V-0000.bin"
noncomputable def vp001101011110 : Blocks := vp001101011110_0
theorem coverp001101011110 : Covers (-1723761639/2000000 : ℚ) vp001101011110 := cover_leaf (by decide +kernel)
private noncomputable def vp00110101111_0 : Blocks := edgeBlocks% "full/vectors/00110101111-V-0000.bin"
noncomputable def vp00110101111 : Blocks := vp00110101111_0
private theorem bp001101011110 : Branch 0 (-1723761639/4000000 : ℚ) vp00110101111 := by
  apply branch_left_normalized (c:=vp001101011110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1723761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1723761639/2000000 : ℚ) by norm_num]
  exact coverp001101011110
private noncomputable def ep001101011111_0 : Blocks := edgeBlocks% "full/vectors/001101011111-E-0000.bin"
noncomputable def ep001101011111 : Blocks := ep001101011111_0
private theorem idp001101011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110101111.list =
    C ((2:ℤ)^127) * horner X vp001101011111.list + horner X ep001101011111.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101011111 : Branch 1 (-1723761639/4000000 : ℚ) vp00110101111 := by
  apply branch_checked idp001101011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1723761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1725761639/2000000 : ℚ) by norm_num]
  exact coverp001101011111
theorem coverp00110101111 : Covers (-1723761639/4000000 : ℚ) vp00110101111 := join_branches bp001101011110 bp001101011111
private noncomputable def vp001101011101_0 : Blocks := edgeBlocks% "full/vectors/001101011101-V-0000.bin"
noncomputable def vp001101011101 : Blocks := vp001101011101_0
theorem coverp001101011101 : Covers (-1721761639/2000000 : ℚ) vp001101011101 := cover_leaf (by decide +kernel)
private noncomputable def vp001101011100_0 : Blocks := edgeBlocks% "full/vectors/001101011100-V-0000.bin"
noncomputable def vp001101011100 : Blocks := vp001101011100_0
theorem coverp001101011100 : Covers (-1719761639/2000000 : ℚ) vp001101011100 := cover_leaf (by decide +kernel)
private noncomputable def vp00110101110_0 : Blocks := edgeBlocks% "full/vectors/00110101110-V-0000.bin"
noncomputable def vp00110101110 : Blocks := vp00110101110_0
private theorem bp001101011100 : Branch 0 (-1719761639/4000000 : ℚ) vp00110101110 := by
  apply branch_left_normalized (c:=vp001101011100) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1719761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1719761639/2000000 : ℚ) by norm_num]
  exact coverp001101011100
private noncomputable def ep001101011101_0 : Blocks := edgeBlocks% "full/vectors/001101011101-E-0000.bin"
noncomputable def ep001101011101 : Blocks := ep001101011101_0
private theorem idp001101011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110101110.list =
    C ((2:ℤ)^129) * horner X vp001101011101.list + horner X ep001101011101.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101011101 : Branch 1 (-1719761639/4000000 : ℚ) vp00110101110 := by
  apply branch_checked idp001101011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1719761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1721761639/2000000 : ℚ) by norm_num]
  exact coverp001101011101
theorem coverp00110101110 : Covers (-1719761639/4000000 : ℚ) vp00110101110 := join_branches bp001101011100 bp001101011101
private noncomputable def vp0011010111_0 : Blocks := edgeBlocks% "full/vectors/0011010111-V-0000.bin"
private noncomputable def vp0011010111_1 : Blocks := edgeBlocks% "full/vectors/0011010111-V-0001.bin"
noncomputable def vp0011010111 : Blocks := (Blocks.join vp0011010111_0 vp0011010111_1)
private theorem bp00110101110 : Branch 0 (-1719761639/8000000 : ℚ) vp0011010111 := by
  apply branch_left_normalized (c:=vp00110101110) (k:=0) (m:=115) (by decide +kernel)
  rw [show 2*(-1719761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1719761639/4000000 : ℚ) by norm_num]
  exact coverp00110101110
private noncomputable def ep00110101111_0 : Blocks := edgeBlocks% "full/vectors/00110101111-E-0000.bin"
private noncomputable def ep00110101111_1 : Blocks := edgeBlocks% "full/vectors/00110101111-E-0001.bin"
noncomputable def ep00110101111 : Blocks := (Blocks.join ep00110101111_0 ep00110101111_1)
private theorem idp00110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011010111.list =
    C ((2:ℤ)^236) * horner X vp00110101111.list + horner X ep00110101111.list := by
  exact edge_identity (B := (2:ℤ)^412) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110101111 : Branch 1 (-1719761639/8000000 : ℚ) vp0011010111 := by
  apply branch_checked idp00110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1719761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1723761639/4000000 : ℚ) by norm_num]
  exact coverp00110101111
theorem coverp0011010111 : Covers (-1719761639/8000000 : ℚ) vp0011010111 := join_branches bp00110101110 bp00110101111
private noncomputable def vp0011010110111_0 : Blocks := edgeBlocks% "full/vectors/0011010110111-V-0000.bin"
noncomputable def vp0011010110111 : Blocks := vp0011010110111_0
theorem coverp0011010110111 : Covers (-1718761639/1000000 : ℚ) vp0011010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010110110_0 : Blocks := edgeBlocks% "full/vectors/0011010110110-V-0000.bin"
noncomputable def vp0011010110110 : Blocks := vp0011010110110_0
theorem coverp0011010110110 : Covers (-1717761639/1000000 : ℚ) vp0011010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp001101011011_0 : Blocks := edgeBlocks% "full/vectors/001101011011-V-0000.bin"
noncomputable def vp001101011011 : Blocks := vp001101011011_0
private theorem bp0011010110110 : Branch 0 (-1717761639/2000000 : ℚ) vp001101011011 := by
  apply branch_left_normalized (c:=vp0011010110110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1717761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1717761639/1000000 : ℚ) by norm_num]
  exact coverp0011010110110
private noncomputable def ep0011010110111_0 : Blocks := edgeBlocks% "full/vectors/0011010110111-E-0000.bin"
noncomputable def ep0011010110111 : Blocks := ep0011010110111_0
private theorem idp0011010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101011011.list =
    C ((2:ℤ)^74) * horner X vp0011010110111.list + horner X ep0011010110111.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010110111 : Branch 1 (-1717761639/2000000 : ℚ) vp001101011011 := by
  apply branch_checked idp0011010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1717761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1718761639/1000000 : ℚ) by norm_num]
  exact coverp0011010110111
theorem coverp001101011011 : Covers (-1717761639/2000000 : ℚ) vp001101011011 := join_branches bp0011010110110 bp0011010110111
private noncomputable def vp0011010110101_0 : Blocks := edgeBlocks% "full/vectors/0011010110101-V-0000.bin"
noncomputable def vp0011010110101 : Blocks := vp0011010110101_0
theorem coverp0011010110101 : Covers (-1716761639/1000000 : ℚ) vp0011010110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010110100_0 : Blocks := edgeBlocks% "full/vectors/0011010110100-V-0000.bin"
noncomputable def vp0011010110100 : Blocks := vp0011010110100_0
theorem coverp0011010110100 : Covers (-1715761639/1000000 : ℚ) vp0011010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001101011010_0 : Blocks := edgeBlocks% "full/vectors/001101011010-V-0000.bin"
noncomputable def vp001101011010 : Blocks := vp001101011010_0
private theorem bp0011010110100 : Branch 0 (-1715761639/2000000 : ℚ) vp001101011010 := by
  apply branch_left_normalized (c:=vp0011010110100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1715761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1715761639/1000000 : ℚ) by norm_num]
  exact coverp0011010110100
private noncomputable def ep0011010110101_0 : Blocks := edgeBlocks% "full/vectors/0011010110101-E-0000.bin"
noncomputable def ep0011010110101 : Blocks := ep0011010110101_0
private theorem idp0011010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101011010.list =
    C ((2:ℤ)^73) * horner X vp0011010110101.list + horner X ep0011010110101.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010110101 : Branch 1 (-1715761639/2000000 : ℚ) vp001101011010 := by
  apply branch_checked idp0011010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1715761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1716761639/1000000 : ℚ) by norm_num]
  exact coverp0011010110101
theorem coverp001101011010 : Covers (-1715761639/2000000 : ℚ) vp001101011010 := join_branches bp0011010110100 bp0011010110101
private noncomputable def vp00110101101_0 : Blocks := edgeBlocks% "full/vectors/00110101101-V-0000.bin"
noncomputable def vp00110101101 : Blocks := vp00110101101_0
private theorem bp001101011010 : Branch 0 (-1715761639/4000000 : ℚ) vp00110101101 := by
  apply branch_left_normalized (c:=vp001101011010) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1715761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1715761639/2000000 : ℚ) by norm_num]
  exact coverp001101011010
private noncomputable def ep001101011011_0 : Blocks := edgeBlocks% "full/vectors/001101011011-E-0000.bin"
noncomputable def ep001101011011 : Blocks := ep001101011011_0
private theorem idp001101011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110101101.list =
    C ((2:ℤ)^127) * horner X vp001101011011.list + horner X ep001101011011.list := by
  exact edge_identity (B := (2:ℤ)^267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101011011 : Branch 1 (-1715761639/4000000 : ℚ) vp00110101101 := by
  apply branch_checked idp001101011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1715761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1717761639/2000000 : ℚ) by norm_num]
  exact coverp001101011011
theorem coverp00110101101 : Covers (-1715761639/4000000 : ℚ) vp00110101101 := join_branches bp001101011010 bp001101011011
private noncomputable def vp0011010110011_0 : Blocks := edgeBlocks% "full/vectors/0011010110011-V-0000.bin"
noncomputable def vp0011010110011 : Blocks := vp0011010110011_0
theorem coverp0011010110011 : Covers (-1714761639/1000000 : ℚ) vp0011010110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010110010_0 : Blocks := edgeBlocks% "full/vectors/0011010110010-V-0000.bin"
noncomputable def vp0011010110010 : Blocks := vp0011010110010_0
theorem coverp0011010110010 : Covers (-1713761639/1000000 : ℚ) vp0011010110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001101011001_0 : Blocks := edgeBlocks% "full/vectors/001101011001-V-0000.bin"
noncomputable def vp001101011001 : Blocks := vp001101011001_0
private theorem bp0011010110010 : Branch 0 (-1713761639/2000000 : ℚ) vp001101011001 := by
  apply branch_left_normalized (c:=vp0011010110010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1713761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1713761639/1000000 : ℚ) by norm_num]
  exact coverp0011010110010
private noncomputable def ep0011010110011_0 : Blocks := edgeBlocks% "full/vectors/0011010110011-E-0000.bin"
noncomputable def ep0011010110011 : Blocks := ep0011010110011_0
private theorem idp0011010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101011001.list =
    C ((2:ℤ)^73) * horner X vp0011010110011.list + horner X ep0011010110011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010110011 : Branch 1 (-1713761639/2000000 : ℚ) vp001101011001 := by
  apply branch_checked idp0011010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1713761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1714761639/1000000 : ℚ) by norm_num]
  exact coverp0011010110011
theorem coverp001101011001 : Covers (-1713761639/2000000 : ℚ) vp001101011001 := join_branches bp0011010110010 bp0011010110011
private noncomputable def vp0011010110001_0 : Blocks := edgeBlocks% "full/vectors/0011010110001-V-0000.bin"
noncomputable def vp0011010110001 : Blocks := vp0011010110001_0
theorem coverp0011010110001 : Covers (-1712761639/1000000 : ℚ) vp0011010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010110000_0 : Blocks := edgeBlocks% "full/vectors/0011010110000-V-0000.bin"
noncomputable def vp0011010110000 : Blocks := vp0011010110000_0
theorem coverp0011010110000 : Covers (-1711761639/1000000 : ℚ) vp0011010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001101011000_0 : Blocks := edgeBlocks% "full/vectors/001101011000-V-0000.bin"
noncomputable def vp001101011000 : Blocks := vp001101011000_0
private theorem bp0011010110000 : Branch 0 (-1711761639/2000000 : ℚ) vp001101011000 := by
  apply branch_left_normalized (c:=vp0011010110000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1711761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1711761639/1000000 : ℚ) by norm_num]
  exact coverp0011010110000
private noncomputable def ep0011010110001_0 : Blocks := edgeBlocks% "full/vectors/0011010110001-E-0000.bin"
noncomputable def ep0011010110001 : Blocks := ep0011010110001_0
private theorem idp0011010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101011000.list =
    C ((2:ℤ)^74) * horner X vp0011010110001.list + horner X ep0011010110001.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010110001 : Branch 1 (-1711761639/2000000 : ℚ) vp001101011000 := by
  apply branch_checked idp0011010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1711761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1712761639/1000000 : ℚ) by norm_num]
  exact coverp0011010110001
theorem coverp001101011000 : Covers (-1711761639/2000000 : ℚ) vp001101011000 := join_branches bp0011010110000 bp0011010110001
private noncomputable def vp00110101100_0 : Blocks := edgeBlocks% "full/vectors/00110101100-V-0000.bin"
noncomputable def vp00110101100 : Blocks := vp00110101100_0
private theorem bp001101011000 : Branch 0 (-1711761639/4000000 : ℚ) vp00110101100 := by
  apply branch_left_normalized (c:=vp001101011000) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1711761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1711761639/2000000 : ℚ) by norm_num]
  exact coverp001101011000
private noncomputable def ep001101011001_0 : Blocks := edgeBlocks% "full/vectors/001101011001-E-0000.bin"
noncomputable def ep001101011001 : Blocks := ep001101011001_0
private theorem idp001101011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110101100.list =
    C ((2:ℤ)^128) * horner X vp001101011001.list + horner X ep001101011001.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101011001 : Branch 1 (-1711761639/4000000 : ℚ) vp00110101100 := by
  apply branch_checked idp001101011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1711761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1713761639/2000000 : ℚ) by norm_num]
  exact coverp001101011001
theorem coverp00110101100 : Covers (-1711761639/4000000 : ℚ) vp00110101100 := join_branches bp001101011000 bp001101011001
private noncomputable def vp0011010110_0 : Blocks := edgeBlocks% "full/vectors/0011010110-V-0000.bin"
private noncomputable def vp0011010110_1 : Blocks := edgeBlocks% "full/vectors/0011010110-V-0001.bin"
noncomputable def vp0011010110 : Blocks := (Blocks.join vp0011010110_0 vp0011010110_1)
private theorem bp00110101100 : Branch 0 (-1711761639/8000000 : ℚ) vp0011010110 := by
  apply branch_left_normalized (c:=vp00110101100) (k:=0) (m:=115) (by decide +kernel)
  rw [show 2*(-1711761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1711761639/4000000 : ℚ) by norm_num]
  exact coverp00110101100
private noncomputable def ep00110101101_0 : Blocks := edgeBlocks% "full/vectors/00110101101-E-0000.bin"
private noncomputable def ep00110101101_1 : Blocks := edgeBlocks% "full/vectors/00110101101-E-0001.bin"
noncomputable def ep00110101101 : Blocks := (Blocks.join ep00110101101_0 ep00110101101_1)
private theorem idp00110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011010110.list =
    C ((2:ℤ)^235) * horner X vp00110101101.list + horner X ep00110101101.list := by
  exact edge_identity (B := (2:ℤ)^413) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110101101 : Branch 1 (-1711761639/8000000 : ℚ) vp0011010110 := by
  apply branch_checked idp00110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1711761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1715761639/4000000 : ℚ) by norm_num]
  exact coverp00110101101
theorem coverp0011010110 : Covers (-1711761639/8000000 : ℚ) vp0011010110 := join_branches bp00110101100 bp00110101101
private noncomputable def vp001101011_0 : Blocks := edgeBlocks% "full/vectors/001101011-V-0000.bin"
private noncomputable def vp001101011_1 : Blocks := edgeBlocks% "full/vectors/001101011-V-0001.bin"
private noncomputable def vp001101011_2 : Blocks := edgeBlocks% "full/vectors/001101011-V-0002.bin"
private noncomputable def vp001101011_3 : Blocks := edgeBlocks% "full/vectors/001101011-V-0003.bin"
noncomputable def vp001101011 : Blocks := (Blocks.join (Blocks.join vp001101011_0 vp001101011_1) (Blocks.join vp001101011_2 vp001101011_3))
private theorem bp0011010110 : Branch 0 (-1711761639/16000000 : ℚ) vp001101011 := by
  apply branch_left_normalized (c:=vp0011010110) (k:=0) (m:=211) (by decide +kernel)
  rw [show 2*(-1711761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1711761639/8000000 : ℚ) by norm_num]
  exact coverp0011010110
private noncomputable def ep0011010111_0 : Blocks := edgeBlocks% "full/vectors/0011010111-E-0000.bin"
private noncomputable def ep0011010111_1 : Blocks := edgeBlocks% "full/vectors/0011010111-E-0001.bin"
private noncomputable def ep0011010111_2 : Blocks := edgeBlocks% "full/vectors/0011010111-E-0002.bin"
private noncomputable def ep0011010111_3 : Blocks := edgeBlocks% "full/vectors/0011010111-E-0003.bin"
noncomputable def ep0011010111 : Blocks := (Blocks.join (Blocks.join ep0011010111_0 ep0011010111_1) (Blocks.join ep0011010111_2 ep0011010111_3))
private theorem idp0011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101011.list =
    C ((2:ℤ)^447) * horner X vp0011010111.list + horner X ep0011010111.list := by
  exact edge_identity (B := (2:ℤ)^702) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010111 : Branch 1 (-1711761639/16000000 : ℚ) vp001101011 := by
  apply branch_checked idp0011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1711761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1719761639/8000000 : ℚ) by norm_num]
  exact coverp0011010111
theorem coverp001101011 : Covers (-1711761639/16000000 : ℚ) vp001101011 := join_branches bp0011010110 bp0011010111
private noncomputable def vp0011010101111_0 : Blocks := edgeBlocks% "full/vectors/0011010101111-V-0000.bin"
noncomputable def vp0011010101111 : Blocks := vp0011010101111_0
theorem coverp0011010101111 : Covers (-1710761639/1000000 : ℚ) vp0011010101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010101110_0 : Blocks := edgeBlocks% "full/vectors/0011010101110-V-0000.bin"
noncomputable def vp0011010101110 : Blocks := vp0011010101110_0
theorem coverp0011010101110 : Covers (-1709761639/1000000 : ℚ) vp0011010101110 := cover_leaf (by decide +kernel)
private noncomputable def vp001101010111_0 : Blocks := edgeBlocks% "full/vectors/001101010111-V-0000.bin"
noncomputable def vp001101010111 : Blocks := vp001101010111_0
private theorem bp0011010101110 : Branch 0 (-1709761639/2000000 : ℚ) vp001101010111 := by
  apply branch_left_normalized (c:=vp0011010101110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1709761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1709761639/1000000 : ℚ) by norm_num]
  exact coverp0011010101110
private noncomputable def ep0011010101111_0 : Blocks := edgeBlocks% "full/vectors/0011010101111-E-0000.bin"
noncomputable def ep0011010101111 : Blocks := ep0011010101111_0
private theorem idp0011010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101010111.list =
    C ((2:ℤ)^74) * horner X vp0011010101111.list + horner X ep0011010101111.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010101111 : Branch 1 (-1709761639/2000000 : ℚ) vp001101010111 := by
  apply branch_checked idp0011010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1709761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1710761639/1000000 : ℚ) by norm_num]
  exact coverp0011010101111
theorem coverp001101010111 : Covers (-1709761639/2000000 : ℚ) vp001101010111 := join_branches bp0011010101110 bp0011010101111
private noncomputable def vp0011010101101_0 : Blocks := edgeBlocks% "full/vectors/0011010101101-V-0000.bin"
noncomputable def vp0011010101101 : Blocks := vp0011010101101_0
theorem coverp0011010101101 : Covers (-1708761639/1000000 : ℚ) vp0011010101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010101100_0 : Blocks := edgeBlocks% "full/vectors/0011010101100-V-0000.bin"
noncomputable def vp0011010101100 : Blocks := vp0011010101100_0
theorem coverp0011010101100 : Covers (-1707761639/1000000 : ℚ) vp0011010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp001101010110_0 : Blocks := edgeBlocks% "full/vectors/001101010110-V-0000.bin"
noncomputable def vp001101010110 : Blocks := vp001101010110_0
private theorem bp0011010101100 : Branch 0 (-1707761639/2000000 : ℚ) vp001101010110 := by
  apply branch_left_normalized (c:=vp0011010101100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1707761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1707761639/1000000 : ℚ) by norm_num]
  exact coverp0011010101100
private noncomputable def ep0011010101101_0 : Blocks := edgeBlocks% "full/vectors/0011010101101-E-0000.bin"
noncomputable def ep0011010101101 : Blocks := ep0011010101101_0
private theorem idp0011010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101010110.list =
    C ((2:ℤ)^74) * horner X vp0011010101101.list + horner X ep0011010101101.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010101101 : Branch 1 (-1707761639/2000000 : ℚ) vp001101010110 := by
  apply branch_checked idp0011010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1707761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1708761639/1000000 : ℚ) by norm_num]
  exact coverp0011010101101
theorem coverp001101010110 : Covers (-1707761639/2000000 : ℚ) vp001101010110 := join_branches bp0011010101100 bp0011010101101
private noncomputable def vp00110101011_0 : Blocks := edgeBlocks% "full/vectors/00110101011-V-0000.bin"
noncomputable def vp00110101011 : Blocks := vp00110101011_0
private theorem bp001101010110 : Branch 0 (-1707761639/4000000 : ℚ) vp00110101011 := by
  apply branch_left_normalized (c:=vp001101010110) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1707761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1707761639/2000000 : ℚ) by norm_num]
  exact coverp001101010110
private noncomputable def ep001101010111_0 : Blocks := edgeBlocks% "full/vectors/001101010111-E-0000.bin"
noncomputable def ep001101010111 : Blocks := ep001101010111_0
private theorem idp001101010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110101011.list =
    C ((2:ℤ)^129) * horner X vp001101010111.list + horner X ep001101010111.list := by
  exact edge_identity (B := (2:ℤ)^268) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101010111 : Branch 1 (-1707761639/4000000 : ℚ) vp00110101011 := by
  apply branch_checked idp001101010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1707761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1709761639/2000000 : ℚ) by norm_num]
  exact coverp001101010111
theorem coverp00110101011 : Covers (-1707761639/4000000 : ℚ) vp00110101011 := join_branches bp001101010110 bp001101010111
private noncomputable def vp0011010101011_0 : Blocks := edgeBlocks% "full/vectors/0011010101011-V-0000.bin"
noncomputable def vp0011010101011 : Blocks := vp0011010101011_0
theorem coverp0011010101011 : Covers (-1706761639/1000000 : ℚ) vp0011010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010101010_0 : Blocks := edgeBlocks% "full/vectors/0011010101010-V-0000.bin"
noncomputable def vp0011010101010 : Blocks := vp0011010101010_0
theorem coverp0011010101010 : Covers (-1705761639/1000000 : ℚ) vp0011010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp001101010101_0 : Blocks := edgeBlocks% "full/vectors/001101010101-V-0000.bin"
noncomputable def vp001101010101 : Blocks := vp001101010101_0
private theorem bp0011010101010 : Branch 0 (-1705761639/2000000 : ℚ) vp001101010101 := by
  apply branch_left_normalized (c:=vp0011010101010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1705761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1705761639/1000000 : ℚ) by norm_num]
  exact coverp0011010101010
private noncomputable def ep0011010101011_0 : Blocks := edgeBlocks% "full/vectors/0011010101011-E-0000.bin"
noncomputable def ep0011010101011 : Blocks := ep0011010101011_0
private theorem idp0011010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101010101.list =
    C ((2:ℤ)^75) * horner X vp0011010101011.list + horner X ep0011010101011.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010101011 : Branch 1 (-1705761639/2000000 : ℚ) vp001101010101 := by
  apply branch_checked idp0011010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1705761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1706761639/1000000 : ℚ) by norm_num]
  exact coverp0011010101011
theorem coverp001101010101 : Covers (-1705761639/2000000 : ℚ) vp001101010101 := join_branches bp0011010101010 bp0011010101011
private noncomputable def vp0011010101001_0 : Blocks := edgeBlocks% "full/vectors/0011010101001-V-0000.bin"
noncomputable def vp0011010101001 : Blocks := vp0011010101001_0
theorem coverp0011010101001 : Covers (-1704761639/1000000 : ℚ) vp0011010101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010101000_0 : Blocks := edgeBlocks% "full/vectors/0011010101000-V-0000.bin"
noncomputable def vp0011010101000 : Blocks := vp0011010101000_0
theorem coverp0011010101000 : Covers (-1703761639/1000000 : ℚ) vp0011010101000 := cover_leaf (by decide +kernel)
private noncomputable def vp001101010100_0 : Blocks := edgeBlocks% "full/vectors/001101010100-V-0000.bin"
noncomputable def vp001101010100 : Blocks := vp001101010100_0
private theorem bp0011010101000 : Branch 0 (-1703761639/2000000 : ℚ) vp001101010100 := by
  apply branch_left_normalized (c:=vp0011010101000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1703761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1703761639/1000000 : ℚ) by norm_num]
  exact coverp0011010101000
private noncomputable def ep0011010101001_0 : Blocks := edgeBlocks% "full/vectors/0011010101001-E-0000.bin"
noncomputable def ep0011010101001 : Blocks := ep0011010101001_0
private theorem idp0011010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101010100.list =
    C ((2:ℤ)^74) * horner X vp0011010101001.list + horner X ep0011010101001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010101001 : Branch 1 (-1703761639/2000000 : ℚ) vp001101010100 := by
  apply branch_checked idp0011010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1703761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1704761639/1000000 : ℚ) by norm_num]
  exact coverp0011010101001
theorem coverp001101010100 : Covers (-1703761639/2000000 : ℚ) vp001101010100 := join_branches bp0011010101000 bp0011010101001
private noncomputable def vp00110101010_0 : Blocks := edgeBlocks% "full/vectors/00110101010-V-0000.bin"
noncomputable def vp00110101010 : Blocks := vp00110101010_0
private theorem bp001101010100 : Branch 0 (-1703761639/4000000 : ℚ) vp00110101010 := by
  apply branch_left_normalized (c:=vp001101010100) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1703761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1703761639/2000000 : ℚ) by norm_num]
  exact coverp001101010100
private noncomputable def ep001101010101_0 : Blocks := edgeBlocks% "full/vectors/001101010101-E-0000.bin"
noncomputable def ep001101010101 : Blocks := ep001101010101_0
private theorem idp001101010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110101010.list =
    C ((2:ℤ)^129) * horner X vp001101010101.list + horner X ep001101010101.list := by
  exact edge_identity (B := (2:ℤ)^269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101010101 : Branch 1 (-1703761639/4000000 : ℚ) vp00110101010 := by
  apply branch_checked idp001101010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1703761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1705761639/2000000 : ℚ) by norm_num]
  exact coverp001101010101
theorem coverp00110101010 : Covers (-1703761639/4000000 : ℚ) vp00110101010 := join_branches bp001101010100 bp001101010101
private noncomputable def vp0011010101_0 : Blocks := edgeBlocks% "full/vectors/0011010101-V-0000.bin"
private noncomputable def vp0011010101_1 : Blocks := edgeBlocks% "full/vectors/0011010101-V-0001.bin"
noncomputable def vp0011010101 : Blocks := (Blocks.join vp0011010101_0 vp0011010101_1)
private theorem bp00110101010 : Branch 0 (-1703761639/8000000 : ℚ) vp0011010101 := by
  apply branch_left_normalized (c:=vp00110101010) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-1703761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1703761639/4000000 : ℚ) by norm_num]
  exact coverp00110101010
private noncomputable def ep00110101011_0 : Blocks := edgeBlocks% "full/vectors/00110101011-E-0000.bin"
private noncomputable def ep00110101011_1 : Blocks := edgeBlocks% "full/vectors/00110101011-E-0001.bin"
noncomputable def ep00110101011 : Blocks := (Blocks.join ep00110101011_0 ep00110101011_1)
private theorem idp00110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011010101.list =
    C ((2:ℤ)^236) * horner X vp00110101011.list + horner X ep00110101011.list := by
  exact edge_identity (B := (2:ℤ)^415) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110101011 : Branch 1 (-1703761639/8000000 : ℚ) vp0011010101 := by
  apply branch_checked idp00110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1703761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1707761639/4000000 : ℚ) by norm_num]
  exact coverp00110101011
theorem coverp0011010101 : Covers (-1703761639/8000000 : ℚ) vp0011010101 := join_branches bp00110101010 bp00110101011
private noncomputable def vp0011010100111_0 : Blocks := edgeBlocks% "full/vectors/0011010100111-V-0000.bin"
noncomputable def vp0011010100111 : Blocks := vp0011010100111_0
theorem coverp0011010100111 : Covers (-1702761639/1000000 : ℚ) vp0011010100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010100110_0 : Blocks := edgeBlocks% "full/vectors/0011010100110-V-0000.bin"
noncomputable def vp0011010100110 : Blocks := vp0011010100110_0
theorem coverp0011010100110 : Covers (-1701761639/1000000 : ℚ) vp0011010100110 := cover_leaf (by decide +kernel)
private noncomputable def vp001101010011_0 : Blocks := edgeBlocks% "full/vectors/001101010011-V-0000.bin"
noncomputable def vp001101010011 : Blocks := vp001101010011_0
private theorem bp0011010100110 : Branch 0 (-1701761639/2000000 : ℚ) vp001101010011 := by
  apply branch_left_normalized (c:=vp0011010100110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1701761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1701761639/1000000 : ℚ) by norm_num]
  exact coverp0011010100110
private noncomputable def ep0011010100111_0 : Blocks := edgeBlocks% "full/vectors/0011010100111-E-0000.bin"
noncomputable def ep0011010100111 : Blocks := ep0011010100111_0
private theorem idp0011010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101010011.list =
    C ((2:ℤ)^72) * horner X vp0011010100111.list + horner X ep0011010100111.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010100111 : Branch 1 (-1701761639/2000000 : ℚ) vp001101010011 := by
  apply branch_checked idp0011010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1701761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1702761639/1000000 : ℚ) by norm_num]
  exact coverp0011010100111
theorem coverp001101010011 : Covers (-1701761639/2000000 : ℚ) vp001101010011 := join_branches bp0011010100110 bp0011010100111
private noncomputable def vp0011010100101_0 : Blocks := edgeBlocks% "full/vectors/0011010100101-V-0000.bin"
noncomputable def vp0011010100101 : Blocks := vp0011010100101_0
theorem coverp0011010100101 : Covers (-1700761639/1000000 : ℚ) vp0011010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010100100_0 : Blocks := edgeBlocks% "full/vectors/0011010100100-V-0000.bin"
noncomputable def vp0011010100100 : Blocks := vp0011010100100_0
theorem coverp0011010100100 : Covers (-1699761639/1000000 : ℚ) vp0011010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp001101010010_0 : Blocks := edgeBlocks% "full/vectors/001101010010-V-0000.bin"
noncomputable def vp001101010010 : Blocks := vp001101010010_0
private theorem bp0011010100100 : Branch 0 (-1699761639/2000000 : ℚ) vp001101010010 := by
  apply branch_left_normalized (c:=vp0011010100100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1699761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1699761639/1000000 : ℚ) by norm_num]
  exact coverp0011010100100
private noncomputable def ep0011010100101_0 : Blocks := edgeBlocks% "full/vectors/0011010100101-E-0000.bin"
noncomputable def ep0011010100101 : Blocks := ep0011010100101_0
private theorem idp0011010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101010010.list =
    C ((2:ℤ)^75) * horner X vp0011010100101.list + horner X ep0011010100101.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010100101 : Branch 1 (-1699761639/2000000 : ℚ) vp001101010010 := by
  apply branch_checked idp0011010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1699761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1700761639/1000000 : ℚ) by norm_num]
  exact coverp0011010100101
theorem coverp001101010010 : Covers (-1699761639/2000000 : ℚ) vp001101010010 := join_branches bp0011010100100 bp0011010100101
private noncomputable def vp00110101001_0 : Blocks := edgeBlocks% "full/vectors/00110101001-V-0000.bin"
noncomputable def vp00110101001 : Blocks := vp00110101001_0
private theorem bp001101010010 : Branch 0 (-1699761639/4000000 : ℚ) vp00110101001 := by
  apply branch_left_normalized (c:=vp001101010010) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1699761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1699761639/2000000 : ℚ) by norm_num]
  exact coverp001101010010
private noncomputable def ep001101010011_0 : Blocks := edgeBlocks% "full/vectors/001101010011-E-0000.bin"
noncomputable def ep001101010011 : Blocks := ep001101010011_0
private theorem idp001101010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110101001.list =
    C ((2:ℤ)^129) * horner X vp001101010011.list + horner X ep001101010011.list := by
  exact edge_identity (B := (2:ℤ)^268) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101010011 : Branch 1 (-1699761639/4000000 : ℚ) vp00110101001 := by
  apply branch_checked idp001101010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1699761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1701761639/2000000 : ℚ) by norm_num]
  exact coverp001101010011
theorem coverp00110101001 : Covers (-1699761639/4000000 : ℚ) vp00110101001 := join_branches bp001101010010 bp001101010011
private noncomputable def vp0011010100011_0 : Blocks := edgeBlocks% "full/vectors/0011010100011-V-0000.bin"
noncomputable def vp0011010100011 : Blocks := vp0011010100011_0
theorem coverp0011010100011 : Covers (-1698761639/1000000 : ℚ) vp0011010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010100010_0 : Blocks := edgeBlocks% "full/vectors/0011010100010-V-0000.bin"
noncomputable def vp0011010100010 : Blocks := vp0011010100010_0
theorem coverp0011010100010 : Covers (-1697761639/1000000 : ℚ) vp0011010100010 := cover_leaf (by decide +kernel)
private noncomputable def vp001101010001_0 : Blocks := edgeBlocks% "full/vectors/001101010001-V-0000.bin"
noncomputable def vp001101010001 : Blocks := vp001101010001_0
private theorem bp0011010100010 : Branch 0 (-1697761639/2000000 : ℚ) vp001101010001 := by
  apply branch_left_normalized (c:=vp0011010100010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1697761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1697761639/1000000 : ℚ) by norm_num]
  exact coverp0011010100010
private noncomputable def ep0011010100011_0 : Blocks := edgeBlocks% "full/vectors/0011010100011-E-0000.bin"
noncomputable def ep0011010100011 : Blocks := ep0011010100011_0
private theorem idp0011010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101010001.list =
    C ((2:ℤ)^75) * horner X vp0011010100011.list + horner X ep0011010100011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010100011 : Branch 1 (-1697761639/2000000 : ℚ) vp001101010001 := by
  apply branch_checked idp0011010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1697761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1698761639/1000000 : ℚ) by norm_num]
  exact coverp0011010100011
theorem coverp001101010001 : Covers (-1697761639/2000000 : ℚ) vp001101010001 := join_branches bp0011010100010 bp0011010100011
private noncomputable def vp0011010100001_0 : Blocks := edgeBlocks% "full/vectors/0011010100001-V-0000.bin"
noncomputable def vp0011010100001 : Blocks := vp0011010100001_0
theorem coverp0011010100001 : Covers (-1696761639/1000000 : ℚ) vp0011010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010100000_0 : Blocks := edgeBlocks% "full/vectors/0011010100000-V-0000.bin"
noncomputable def vp0011010100000 : Blocks := vp0011010100000_0
theorem coverp0011010100000 : Covers (-1695761639/1000000 : ℚ) vp0011010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp001101010000_0 : Blocks := edgeBlocks% "full/vectors/001101010000-V-0000.bin"
noncomputable def vp001101010000 : Blocks := vp001101010000_0
private theorem bp0011010100000 : Branch 0 (-1695761639/2000000 : ℚ) vp001101010000 := by
  apply branch_left_normalized (c:=vp0011010100000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1695761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1695761639/1000000 : ℚ) by norm_num]
  exact coverp0011010100000
private noncomputable def ep0011010100001_0 : Blocks := edgeBlocks% "full/vectors/0011010100001-E-0000.bin"
noncomputable def ep0011010100001 : Blocks := ep0011010100001_0
private theorem idp0011010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101010000.list =
    C ((2:ℤ)^75) * horner X vp0011010100001.list + horner X ep0011010100001.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010100001 : Branch 1 (-1695761639/2000000 : ℚ) vp001101010000 := by
  apply branch_checked idp0011010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1695761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1696761639/1000000 : ℚ) by norm_num]
  exact coverp0011010100001
theorem coverp001101010000 : Covers (-1695761639/2000000 : ℚ) vp001101010000 := join_branches bp0011010100000 bp0011010100001
private noncomputable def vp00110101000_0 : Blocks := edgeBlocks% "full/vectors/00110101000-V-0000.bin"
noncomputable def vp00110101000 : Blocks := vp00110101000_0
private theorem bp001101010000 : Branch 0 (-1695761639/4000000 : ℚ) vp00110101000 := by
  apply branch_left_normalized (c:=vp001101010000) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1695761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1695761639/2000000 : ℚ) by norm_num]
  exact coverp001101010000
private noncomputable def ep001101010001_0 : Blocks := edgeBlocks% "full/vectors/001101010001-E-0000.bin"
noncomputable def ep001101010001 : Blocks := ep001101010001_0
private theorem idp001101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110101000.list =
    C ((2:ℤ)^130) * horner X vp001101010001.list + horner X ep001101010001.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101010001 : Branch 1 (-1695761639/4000000 : ℚ) vp00110101000 := by
  apply branch_checked idp001101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1695761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1697761639/2000000 : ℚ) by norm_num]
  exact coverp001101010001
theorem coverp00110101000 : Covers (-1695761639/4000000 : ℚ) vp00110101000 := join_branches bp001101010000 bp001101010001
private noncomputable def vp0011010100_0 : Blocks := edgeBlocks% "full/vectors/0011010100-V-0000.bin"
private noncomputable def vp0011010100_1 : Blocks := edgeBlocks% "full/vectors/0011010100-V-0001.bin"
noncomputable def vp0011010100 : Blocks := (Blocks.join vp0011010100_0 vp0011010100_1)
private theorem bp00110101000 : Branch 0 (-1695761639/8000000 : ℚ) vp0011010100 := by
  apply branch_left_normalized (c:=vp00110101000) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-1695761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1695761639/4000000 : ℚ) by norm_num]
  exact coverp00110101000
private noncomputable def ep00110101001_0 : Blocks := edgeBlocks% "full/vectors/00110101001-E-0000.bin"
private noncomputable def ep00110101001_1 : Blocks := edgeBlocks% "full/vectors/00110101001-E-0001.bin"
noncomputable def ep00110101001 : Blocks := (Blocks.join ep00110101001_0 ep00110101001_1)
private theorem idp00110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011010100.list =
    C ((2:ℤ)^238) * horner X vp00110101001.list + horner X ep00110101001.list := by
  exact edge_identity (B := (2:ℤ)^417) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110101001 : Branch 1 (-1695761639/8000000 : ℚ) vp0011010100 := by
  apply branch_checked idp00110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1695761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1699761639/4000000 : ℚ) by norm_num]
  exact coverp00110101001
theorem coverp0011010100 : Covers (-1695761639/8000000 : ℚ) vp0011010100 := join_branches bp00110101000 bp00110101001
private noncomputable def vp001101010_0 : Blocks := edgeBlocks% "full/vectors/001101010-V-0000.bin"
private noncomputable def vp001101010_1 : Blocks := edgeBlocks% "full/vectors/001101010-V-0001.bin"
private noncomputable def vp001101010_2 : Blocks := edgeBlocks% "full/vectors/001101010-V-0002.bin"
private noncomputable def vp001101010_3 : Blocks := edgeBlocks% "full/vectors/001101010-V-0003.bin"
noncomputable def vp001101010 : Blocks := (Blocks.join (Blocks.join vp001101010_0 vp001101010_1) (Blocks.join vp001101010_2 vp001101010_3))
private theorem bp0011010100 : Branch 0 (-1695761639/16000000 : ℚ) vp001101010 := by
  apply branch_left_normalized (c:=vp0011010100) (k:=0) (m:=213) (by decide +kernel)
  rw [show 2*(-1695761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1695761639/8000000 : ℚ) by norm_num]
  exact coverp0011010100
private noncomputable def ep0011010101_0 : Blocks := edgeBlocks% "full/vectors/0011010101-E-0000.bin"
private noncomputable def ep0011010101_1 : Blocks := edgeBlocks% "full/vectors/0011010101-E-0001.bin"
private noncomputable def ep0011010101_2 : Blocks := edgeBlocks% "full/vectors/0011010101-E-0002.bin"
private noncomputable def ep0011010101_3 : Blocks := edgeBlocks% "full/vectors/0011010101-E-0003.bin"
noncomputable def ep0011010101 : Blocks := (Blocks.join (Blocks.join ep0011010101_0 ep0011010101_1) (Blocks.join ep0011010101_2 ep0011010101_3))
private theorem idp0011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101010.list =
    C ((2:ℤ)^450) * horner X vp0011010101.list + horner X ep0011010101.list := by
  exact edge_identity (B := (2:ℤ)^707) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010101 : Branch 1 (-1695761639/16000000 : ℚ) vp001101010 := by
  apply branch_checked idp0011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1695761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1703761639/8000000 : ℚ) by norm_num]
  exact coverp0011010101
theorem coverp001101010 : Covers (-1695761639/16000000 : ℚ) vp001101010 := join_branches bp0011010100 bp0011010101
private noncomputable def vp00110101_0 : Blocks := edgeBlocks% "full/vectors/00110101-V-0000.bin"
private noncomputable def vp00110101_1 : Blocks := edgeBlocks% "full/vectors/00110101-V-0001.bin"
private noncomputable def vp00110101_2 : Blocks := edgeBlocks% "full/vectors/00110101-V-0002.bin"
private noncomputable def vp00110101_3 : Blocks := edgeBlocks% "full/vectors/00110101-V-0003.bin"
private noncomputable def vp00110101_4 : Blocks := edgeBlocks% "full/vectors/00110101-V-0004.bin"
private noncomputable def vp00110101_5 : Blocks := edgeBlocks% "full/vectors/00110101-V-0005.bin"
private noncomputable def vp00110101_6 : Blocks := edgeBlocks% "full/vectors/00110101-V-0006.bin"
noncomputable def vp00110101 : Blocks := (Blocks.join (Blocks.join vp00110101_0 (Blocks.join vp00110101_1 vp00110101_2)) (Blocks.join (Blocks.join vp00110101_3 vp00110101_4) (Blocks.join vp00110101_5 vp00110101_6)))
private theorem bp001101010 : Branch 0 (-1695761639/32000000 : ℚ) vp00110101 := by
  apply branch_left_normalized (c:=vp001101010) (k:=0) (m:=402) (by decide +kernel)
  rw [show 2*(-1695761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1695761639/16000000 : ℚ) by norm_num]
  exact coverp001101010
private noncomputable def ep001101011_0 : Blocks := edgeBlocks% "full/vectors/001101011-E-0000.bin"
private noncomputable def ep001101011_1 : Blocks := edgeBlocks% "full/vectors/001101011-E-0001.bin"
private noncomputable def ep001101011_2 : Blocks := edgeBlocks% "full/vectors/001101011-E-0002.bin"
private noncomputable def ep001101011_3 : Blocks := edgeBlocks% "full/vectors/001101011-E-0003.bin"
private noncomputable def ep001101011_4 : Blocks := edgeBlocks% "full/vectors/001101011-E-0004.bin"
private noncomputable def ep001101011_5 : Blocks := edgeBlocks% "full/vectors/001101011-E-0005.bin"
private noncomputable def ep001101011_6 : Blocks := edgeBlocks% "full/vectors/001101011-E-0006.bin"
noncomputable def ep001101011 : Blocks := (Blocks.join (Blocks.join ep001101011_0 (Blocks.join ep001101011_1 ep001101011_2)) (Blocks.join (Blocks.join ep001101011_3 ep001101011_4) (Blocks.join ep001101011_5 ep001101011_6)))
private theorem idp001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110101.list =
    C ((2:ℤ)^873) * horner X vp001101011.list + horner X ep001101011.list := by
  exact edge_identity (B := (2:ℤ)^1285) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101011 : Branch 1 (-1695761639/32000000 : ℚ) vp00110101 := by
  apply branch_checked idp001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1695761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1711761639/16000000 : ℚ) by norm_num]
  exact coverp001101011
theorem coverp00110101 : Covers (-1695761639/32000000 : ℚ) vp00110101 := join_branches bp001101010 bp001101011
private noncomputable def vp0011010011111_0 : Blocks := edgeBlocks% "full/vectors/0011010011111-V-0000.bin"
noncomputable def vp0011010011111 : Blocks := vp0011010011111_0
theorem coverp0011010011111 : Covers (-1694761639/1000000 : ℚ) vp0011010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010011110_0 : Blocks := edgeBlocks% "full/vectors/0011010011110-V-0000.bin"
noncomputable def vp0011010011110 : Blocks := vp0011010011110_0
theorem coverp0011010011110 : Covers (-1693761639/1000000 : ℚ) vp0011010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp001101001111_0 : Blocks := edgeBlocks% "full/vectors/001101001111-V-0000.bin"
noncomputable def vp001101001111 : Blocks := vp001101001111_0
private theorem bp0011010011110 : Branch 0 (-1693761639/2000000 : ℚ) vp001101001111 := by
  apply branch_left_normalized (c:=vp0011010011110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1693761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1693761639/1000000 : ℚ) by norm_num]
  exact coverp0011010011110
private noncomputable def ep0011010011111_0 : Blocks := edgeBlocks% "full/vectors/0011010011111-E-0000.bin"
noncomputable def ep0011010011111 : Blocks := ep0011010011111_0
private theorem idp0011010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101001111.list =
    C ((2:ℤ)^74) * horner X vp0011010011111.list + horner X ep0011010011111.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010011111 : Branch 1 (-1693761639/2000000 : ℚ) vp001101001111 := by
  apply branch_checked idp0011010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1693761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1694761639/1000000 : ℚ) by norm_num]
  exact coverp0011010011111
theorem coverp001101001111 : Covers (-1693761639/2000000 : ℚ) vp001101001111 := join_branches bp0011010011110 bp0011010011111
private noncomputable def vp0011010011101_0 : Blocks := edgeBlocks% "full/vectors/0011010011101-V-0000.bin"
noncomputable def vp0011010011101 : Blocks := vp0011010011101_0
theorem coverp0011010011101 : Covers (-1692761639/1000000 : ℚ) vp0011010011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010011100_0 : Blocks := edgeBlocks% "full/vectors/0011010011100-V-0000.bin"
noncomputable def vp0011010011100 : Blocks := vp0011010011100_0
theorem coverp0011010011100 : Covers (-1691761639/1000000 : ℚ) vp0011010011100 := cover_leaf (by decide +kernel)
private noncomputable def vp001101001110_0 : Blocks := edgeBlocks% "full/vectors/001101001110-V-0000.bin"
noncomputable def vp001101001110 : Blocks := vp001101001110_0
private theorem bp0011010011100 : Branch 0 (-1691761639/2000000 : ℚ) vp001101001110 := by
  apply branch_left_normalized (c:=vp0011010011100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1691761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1691761639/1000000 : ℚ) by norm_num]
  exact coverp0011010011100
private noncomputable def ep0011010011101_0 : Blocks := edgeBlocks% "full/vectors/0011010011101-E-0000.bin"
noncomputable def ep0011010011101 : Blocks := ep0011010011101_0
private theorem idp0011010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101001110.list =
    C ((2:ℤ)^75) * horner X vp0011010011101.list + horner X ep0011010011101.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010011101 : Branch 1 (-1691761639/2000000 : ℚ) vp001101001110 := by
  apply branch_checked idp0011010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1691761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1692761639/1000000 : ℚ) by norm_num]
  exact coverp0011010011101
theorem coverp001101001110 : Covers (-1691761639/2000000 : ℚ) vp001101001110 := join_branches bp0011010011100 bp0011010011101
private noncomputable def vp00110100111_0 : Blocks := edgeBlocks% "full/vectors/00110100111-V-0000.bin"
noncomputable def vp00110100111 : Blocks := vp00110100111_0
private theorem bp001101001110 : Branch 0 (-1691761639/4000000 : ℚ) vp00110100111 := by
  apply branch_left_normalized (c:=vp001101001110) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1691761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1691761639/2000000 : ℚ) by norm_num]
  exact coverp001101001110
private noncomputable def ep001101001111_0 : Blocks := edgeBlocks% "full/vectors/001101001111-E-0000.bin"
noncomputable def ep001101001111 : Blocks := ep001101001111_0
private theorem idp001101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110100111.list =
    C ((2:ℤ)^130) * horner X vp001101001111.list + horner X ep001101001111.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101001111 : Branch 1 (-1691761639/4000000 : ℚ) vp00110100111 := by
  apply branch_checked idp001101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1691761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1693761639/2000000 : ℚ) by norm_num]
  exact coverp001101001111
theorem coverp00110100111 : Covers (-1691761639/4000000 : ℚ) vp00110100111 := join_branches bp001101001110 bp001101001111
private noncomputable def vp0011010011011_0 : Blocks := edgeBlocks% "full/vectors/0011010011011-V-0000.bin"
noncomputable def vp0011010011011 : Blocks := vp0011010011011_0
theorem coverp0011010011011 : Covers (-1690761639/1000000 : ℚ) vp0011010011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010011010_0 : Blocks := edgeBlocks% "full/vectors/0011010011010-V-0000.bin"
noncomputable def vp0011010011010 : Blocks := vp0011010011010_0
theorem coverp0011010011010 : Covers (-1689761639/1000000 : ℚ) vp0011010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp001101001101_0 : Blocks := edgeBlocks% "full/vectors/001101001101-V-0000.bin"
noncomputable def vp001101001101 : Blocks := vp001101001101_0
private theorem bp0011010011010 : Branch 0 (-1689761639/2000000 : ℚ) vp001101001101 := by
  apply branch_left_normalized (c:=vp0011010011010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1689761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1689761639/1000000 : ℚ) by norm_num]
  exact coverp0011010011010
private noncomputable def ep0011010011011_0 : Blocks := edgeBlocks% "full/vectors/0011010011011-E-0000.bin"
noncomputable def ep0011010011011 : Blocks := ep0011010011011_0
private theorem idp0011010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101001101.list =
    C ((2:ℤ)^75) * horner X vp0011010011011.list + horner X ep0011010011011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010011011 : Branch 1 (-1689761639/2000000 : ℚ) vp001101001101 := by
  apply branch_checked idp0011010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1689761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1690761639/1000000 : ℚ) by norm_num]
  exact coverp0011010011011
theorem coverp001101001101 : Covers (-1689761639/2000000 : ℚ) vp001101001101 := join_branches bp0011010011010 bp0011010011011
private noncomputable def vp0011010011001_0 : Blocks := edgeBlocks% "full/vectors/0011010011001-V-0000.bin"
noncomputable def vp0011010011001 : Blocks := vp0011010011001_0
theorem coverp0011010011001 : Covers (-1688761639/1000000 : ℚ) vp0011010011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010011000_0 : Blocks := edgeBlocks% "full/vectors/0011010011000-V-0000.bin"
noncomputable def vp0011010011000 : Blocks := vp0011010011000_0
theorem coverp0011010011000 : Covers (-1687761639/1000000 : ℚ) vp0011010011000 := cover_leaf (by decide +kernel)
private noncomputable def vp001101001100_0 : Blocks := edgeBlocks% "full/vectors/001101001100-V-0000.bin"
noncomputable def vp001101001100 : Blocks := vp001101001100_0
private theorem bp0011010011000 : Branch 0 (-1687761639/2000000 : ℚ) vp001101001100 := by
  apply branch_left_normalized (c:=vp0011010011000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1687761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1687761639/1000000 : ℚ) by norm_num]
  exact coverp0011010011000
private noncomputable def ep0011010011001_0 : Blocks := edgeBlocks% "full/vectors/0011010011001-E-0000.bin"
noncomputable def ep0011010011001 : Blocks := ep0011010011001_0
private theorem idp0011010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101001100.list =
    C ((2:ℤ)^74) * horner X vp0011010011001.list + horner X ep0011010011001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010011001 : Branch 1 (-1687761639/2000000 : ℚ) vp001101001100 := by
  apply branch_checked idp0011010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1687761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1688761639/1000000 : ℚ) by norm_num]
  exact coverp0011010011001
theorem coverp001101001100 : Covers (-1687761639/2000000 : ℚ) vp001101001100 := join_branches bp0011010011000 bp0011010011001
private noncomputable def vp00110100110_0 : Blocks := edgeBlocks% "full/vectors/00110100110-V-0000.bin"
noncomputable def vp00110100110 : Blocks := vp00110100110_0
private theorem bp001101001100 : Branch 0 (-1687761639/4000000 : ℚ) vp00110100110 := by
  apply branch_left_normalized (c:=vp001101001100) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1687761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1687761639/2000000 : ℚ) by norm_num]
  exact coverp001101001100
private noncomputable def ep001101001101_0 : Blocks := edgeBlocks% "full/vectors/001101001101-E-0000.bin"
noncomputable def ep001101001101 : Blocks := ep001101001101_0
private theorem idp001101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110100110.list =
    C ((2:ℤ)^129) * horner X vp001101001101.list + horner X ep001101001101.list := by
  exact edge_identity (B := (2:ℤ)^269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101001101 : Branch 1 (-1687761639/4000000 : ℚ) vp00110100110 := by
  apply branch_checked idp001101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1687761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1689761639/2000000 : ℚ) by norm_num]
  exact coverp001101001101
theorem coverp00110100110 : Covers (-1687761639/4000000 : ℚ) vp00110100110 := join_branches bp001101001100 bp001101001101
private noncomputable def vp0011010011_0 : Blocks := edgeBlocks% "full/vectors/0011010011-V-0000.bin"
private noncomputable def vp0011010011_1 : Blocks := edgeBlocks% "full/vectors/0011010011-V-0001.bin"
noncomputable def vp0011010011 : Blocks := (Blocks.join vp0011010011_0 vp0011010011_1)
private theorem bp00110100110 : Branch 0 (-1687761639/8000000 : ℚ) vp0011010011 := by
  apply branch_left_normalized (c:=vp00110100110) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-1687761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1687761639/4000000 : ℚ) by norm_num]
  exact coverp00110100110
private noncomputable def ep00110100111_0 : Blocks := edgeBlocks% "full/vectors/00110100111-E-0000.bin"
private noncomputable def ep00110100111_1 : Blocks := edgeBlocks% "full/vectors/00110100111-E-0001.bin"
noncomputable def ep00110100111 : Blocks := (Blocks.join ep00110100111_0 ep00110100111_1)
private theorem idp00110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011010011.list =
    C ((2:ℤ)^236) * horner X vp00110100111.list + horner X ep00110100111.list := by
  exact edge_identity (B := (2:ℤ)^416) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110100111 : Branch 1 (-1687761639/8000000 : ℚ) vp0011010011 := by
  apply branch_checked idp00110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1687761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1691761639/4000000 : ℚ) by norm_num]
  exact coverp00110100111
theorem coverp0011010011 : Covers (-1687761639/8000000 : ℚ) vp0011010011 := join_branches bp00110100110 bp00110100111
private noncomputable def vp0011010010111_0 : Blocks := edgeBlocks% "full/vectors/0011010010111-V-0000.bin"
noncomputable def vp0011010010111 : Blocks := vp0011010010111_0
theorem coverp0011010010111 : Covers (-1686761639/1000000 : ℚ) vp0011010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010010110_0 : Blocks := edgeBlocks% "full/vectors/0011010010110-V-0000.bin"
noncomputable def vp0011010010110 : Blocks := vp0011010010110_0
theorem coverp0011010010110 : Covers (-1685761639/1000000 : ℚ) vp0011010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp001101001011_0 : Blocks := edgeBlocks% "full/vectors/001101001011-V-0000.bin"
noncomputable def vp001101001011 : Blocks := vp001101001011_0
private theorem bp0011010010110 : Branch 0 (-1685761639/2000000 : ℚ) vp001101001011 := by
  apply branch_left_normalized (c:=vp0011010010110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1685761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1685761639/1000000 : ℚ) by norm_num]
  exact coverp0011010010110
private noncomputable def ep0011010010111_0 : Blocks := edgeBlocks% "full/vectors/0011010010111-E-0000.bin"
noncomputable def ep0011010010111 : Blocks := ep0011010010111_0
private theorem idp0011010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101001011.list =
    C ((2:ℤ)^75) * horner X vp0011010010111.list + horner X ep0011010010111.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010010111 : Branch 1 (-1685761639/2000000 : ℚ) vp001101001011 := by
  apply branch_checked idp0011010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1685761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1686761639/1000000 : ℚ) by norm_num]
  exact coverp0011010010111
theorem coverp001101001011 : Covers (-1685761639/2000000 : ℚ) vp001101001011 := join_branches bp0011010010110 bp0011010010111
private noncomputable def vp0011010010101_0 : Blocks := edgeBlocks% "full/vectors/0011010010101-V-0000.bin"
noncomputable def vp0011010010101 : Blocks := vp0011010010101_0
theorem coverp0011010010101 : Covers (-1684761639/1000000 : ℚ) vp0011010010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010010100_0 : Blocks := edgeBlocks% "full/vectors/0011010010100-V-0000.bin"
noncomputable def vp0011010010100 : Blocks := vp0011010010100_0
theorem coverp0011010010100 : Covers (-1683761639/1000000 : ℚ) vp0011010010100 := cover_leaf (by decide +kernel)
private noncomputable def vp001101001010_0 : Blocks := edgeBlocks% "full/vectors/001101001010-V-0000.bin"
noncomputable def vp001101001010 : Blocks := vp001101001010_0
private theorem bp0011010010100 : Branch 0 (-1683761639/2000000 : ℚ) vp001101001010 := by
  apply branch_left_normalized (c:=vp0011010010100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1683761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1683761639/1000000 : ℚ) by norm_num]
  exact coverp0011010010100
private noncomputable def ep0011010010101_0 : Blocks := edgeBlocks% "full/vectors/0011010010101-E-0000.bin"
noncomputable def ep0011010010101 : Blocks := ep0011010010101_0
private theorem idp0011010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101001010.list =
    C ((2:ℤ)^75) * horner X vp0011010010101.list + horner X ep0011010010101.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010010101 : Branch 1 (-1683761639/2000000 : ℚ) vp001101001010 := by
  apply branch_checked idp0011010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1683761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1684761639/1000000 : ℚ) by norm_num]
  exact coverp0011010010101
theorem coverp001101001010 : Covers (-1683761639/2000000 : ℚ) vp001101001010 := join_branches bp0011010010100 bp0011010010101
private noncomputable def vp00110100101_0 : Blocks := edgeBlocks% "full/vectors/00110100101-V-0000.bin"
noncomputable def vp00110100101 : Blocks := vp00110100101_0
private theorem bp001101001010 : Branch 0 (-1683761639/4000000 : ℚ) vp00110100101 := by
  apply branch_left_normalized (c:=vp001101001010) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1683761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1683761639/2000000 : ℚ) by norm_num]
  exact coverp001101001010
private noncomputable def ep001101001011_0 : Blocks := edgeBlocks% "full/vectors/001101001011-E-0000.bin"
noncomputable def ep001101001011 : Blocks := ep001101001011_0
private theorem idp001101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110100101.list =
    C ((2:ℤ)^130) * horner X vp001101001011.list + horner X ep001101001011.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101001011 : Branch 1 (-1683761639/4000000 : ℚ) vp00110100101 := by
  apply branch_checked idp001101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1683761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1685761639/2000000 : ℚ) by norm_num]
  exact coverp001101001011
theorem coverp00110100101 : Covers (-1683761639/4000000 : ℚ) vp00110100101 := join_branches bp001101001010 bp001101001011
private noncomputable def vp0011010010011_0 : Blocks := edgeBlocks% "full/vectors/0011010010011-V-0000.bin"
noncomputable def vp0011010010011 : Blocks := vp0011010010011_0
theorem coverp0011010010011 : Covers (-1682761639/1000000 : ℚ) vp0011010010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010010010_0 : Blocks := edgeBlocks% "full/vectors/0011010010010-V-0000.bin"
noncomputable def vp0011010010010 : Blocks := vp0011010010010_0
theorem coverp0011010010010 : Covers (-1681761639/1000000 : ℚ) vp0011010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp001101001001_0 : Blocks := edgeBlocks% "full/vectors/001101001001-V-0000.bin"
noncomputable def vp001101001001 : Blocks := vp001101001001_0
private theorem bp0011010010010 : Branch 0 (-1681761639/2000000 : ℚ) vp001101001001 := by
  apply branch_left_normalized (c:=vp0011010010010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1681761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1681761639/1000000 : ℚ) by norm_num]
  exact coverp0011010010010
private noncomputable def ep0011010010011_0 : Blocks := edgeBlocks% "full/vectors/0011010010011-E-0000.bin"
noncomputable def ep0011010010011 : Blocks := ep0011010010011_0
private theorem idp0011010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101001001.list =
    C ((2:ℤ)^75) * horner X vp0011010010011.list + horner X ep0011010010011.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010010011 : Branch 1 (-1681761639/2000000 : ℚ) vp001101001001 := by
  apply branch_checked idp0011010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1681761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1682761639/1000000 : ℚ) by norm_num]
  exact coverp0011010010011
theorem coverp001101001001 : Covers (-1681761639/2000000 : ℚ) vp001101001001 := join_branches bp0011010010010 bp0011010010011
private noncomputable def vp0011010010001_0 : Blocks := edgeBlocks% "full/vectors/0011010010001-V-0000.bin"
noncomputable def vp0011010010001 : Blocks := vp0011010010001_0
theorem coverp0011010010001 : Covers (-1680761639/1000000 : ℚ) vp0011010010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010010000_0 : Blocks := edgeBlocks% "full/vectors/0011010010000-V-0000.bin"
noncomputable def vp0011010010000 : Blocks := vp0011010010000_0
theorem coverp0011010010000 : Covers (-1679761639/1000000 : ℚ) vp0011010010000 := cover_leaf (by decide +kernel)
private noncomputable def vp001101001000_0 : Blocks := edgeBlocks% "full/vectors/001101001000-V-0000.bin"
noncomputable def vp001101001000 : Blocks := vp001101001000_0
private theorem bp0011010010000 : Branch 0 (-1679761639/2000000 : ℚ) vp001101001000 := by
  apply branch_left_normalized (c:=vp0011010010000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1679761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1679761639/1000000 : ℚ) by norm_num]
  exact coverp0011010010000
private noncomputable def ep0011010010001_0 : Blocks := edgeBlocks% "full/vectors/0011010010001-E-0000.bin"
noncomputable def ep0011010010001 : Blocks := ep0011010010001_0
private theorem idp0011010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101001000.list =
    C ((2:ℤ)^75) * horner X vp0011010010001.list + horner X ep0011010010001.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010010001 : Branch 1 (-1679761639/2000000 : ℚ) vp001101001000 := by
  apply branch_checked idp0011010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1679761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1680761639/1000000 : ℚ) by norm_num]
  exact coverp0011010010001
theorem coverp001101001000 : Covers (-1679761639/2000000 : ℚ) vp001101001000 := join_branches bp0011010010000 bp0011010010001
private noncomputable def vp00110100100_0 : Blocks := edgeBlocks% "full/vectors/00110100100-V-0000.bin"
noncomputable def vp00110100100 : Blocks := vp00110100100_0
private theorem bp001101001000 : Branch 0 (-1679761639/4000000 : ℚ) vp00110100100 := by
  apply branch_left_normalized (c:=vp001101001000) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1679761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1679761639/2000000 : ℚ) by norm_num]
  exact coverp001101001000
private noncomputable def ep001101001001_0 : Blocks := edgeBlocks% "full/vectors/001101001001-E-0000.bin"
noncomputable def ep001101001001 : Blocks := ep001101001001_0
private theorem idp001101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110100100.list =
    C ((2:ℤ)^129) * horner X vp001101001001.list + horner X ep001101001001.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101001001 : Branch 1 (-1679761639/4000000 : ℚ) vp00110100100 := by
  apply branch_checked idp001101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1679761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1681761639/2000000 : ℚ) by norm_num]
  exact coverp001101001001
theorem coverp00110100100 : Covers (-1679761639/4000000 : ℚ) vp00110100100 := join_branches bp001101001000 bp001101001001
private noncomputable def vp0011010010_0 : Blocks := edgeBlocks% "full/vectors/0011010010-V-0000.bin"
private noncomputable def vp0011010010_1 : Blocks := edgeBlocks% "full/vectors/0011010010-V-0001.bin"
noncomputable def vp0011010010 : Blocks := (Blocks.join vp0011010010_0 vp0011010010_1)
private theorem bp00110100100 : Branch 0 (-1679761639/8000000 : ℚ) vp0011010010 := by
  apply branch_left_normalized (c:=vp00110100100) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-1679761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1679761639/4000000 : ℚ) by norm_num]
  exact coverp00110100100
private noncomputable def ep00110100101_0 : Blocks := edgeBlocks% "full/vectors/00110100101-E-0000.bin"
private noncomputable def ep00110100101_1 : Blocks := edgeBlocks% "full/vectors/00110100101-E-0001.bin"
noncomputable def ep00110100101 : Blocks := (Blocks.join ep00110100101_0 ep00110100101_1)
private theorem idp00110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011010010.list =
    C ((2:ℤ)^237) * horner X vp00110100101.list + horner X ep00110100101.list := by
  exact edge_identity (B := (2:ℤ)^417) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110100101 : Branch 1 (-1679761639/8000000 : ℚ) vp0011010010 := by
  apply branch_checked idp00110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1679761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1683761639/4000000 : ℚ) by norm_num]
  exact coverp00110100101
theorem coverp0011010010 : Covers (-1679761639/8000000 : ℚ) vp0011010010 := join_branches bp00110100100 bp00110100101
private noncomputable def vp001101001_0 : Blocks := edgeBlocks% "full/vectors/001101001-V-0000.bin"
private noncomputable def vp001101001_1 : Blocks := edgeBlocks% "full/vectors/001101001-V-0001.bin"
private noncomputable def vp001101001_2 : Blocks := edgeBlocks% "full/vectors/001101001-V-0002.bin"
private noncomputable def vp001101001_3 : Blocks := edgeBlocks% "full/vectors/001101001-V-0003.bin"
noncomputable def vp001101001 : Blocks := (Blocks.join (Blocks.join vp001101001_0 vp001101001_1) (Blocks.join vp001101001_2 vp001101001_3))
private theorem bp0011010010 : Branch 0 (-1679761639/16000000 : ℚ) vp001101001 := by
  apply branch_left_normalized (c:=vp0011010010) (k:=0) (m:=213) (by decide +kernel)
  rw [show 2*(-1679761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1679761639/8000000 : ℚ) by norm_num]
  exact coverp0011010010
private noncomputable def ep0011010011_0 : Blocks := edgeBlocks% "full/vectors/0011010011-E-0000.bin"
private noncomputable def ep0011010011_1 : Blocks := edgeBlocks% "full/vectors/0011010011-E-0001.bin"
private noncomputable def ep0011010011_2 : Blocks := edgeBlocks% "full/vectors/0011010011-E-0002.bin"
private noncomputable def ep0011010011_3 : Blocks := edgeBlocks% "full/vectors/0011010011-E-0003.bin"
noncomputable def ep0011010011 : Blocks := (Blocks.join (Blocks.join ep0011010011_0 ep0011010011_1) (Blocks.join ep0011010011_2 ep0011010011_3))
private theorem idp0011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101001.list =
    C ((2:ℤ)^452) * horner X vp0011010011.list + horner X ep0011010011.list := by
  exact edge_identity (B := (2:ℤ)^710) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010011 : Branch 1 (-1679761639/16000000 : ℚ) vp001101001 := by
  apply branch_checked idp0011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1679761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1687761639/8000000 : ℚ) by norm_num]
  exact coverp0011010011
theorem coverp001101001 : Covers (-1679761639/16000000 : ℚ) vp001101001 := join_branches bp0011010010 bp0011010011
private noncomputable def vp0011010001111_0 : Blocks := edgeBlocks% "full/vectors/0011010001111-V-0000.bin"
noncomputable def vp0011010001111 : Blocks := vp0011010001111_0
theorem coverp0011010001111 : Covers (-1678761639/1000000 : ℚ) vp0011010001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010001110_0 : Blocks := edgeBlocks% "full/vectors/0011010001110-V-0000.bin"
noncomputable def vp0011010001110 : Blocks := vp0011010001110_0
theorem coverp0011010001110 : Covers (-1677761639/1000000 : ℚ) vp0011010001110 := cover_leaf (by decide +kernel)
private noncomputable def vp001101000111_0 : Blocks := edgeBlocks% "full/vectors/001101000111-V-0000.bin"
noncomputable def vp001101000111 : Blocks := vp001101000111_0
private theorem bp0011010001110 : Branch 0 (-1677761639/2000000 : ℚ) vp001101000111 := by
  apply branch_left_normalized (c:=vp0011010001110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1677761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1677761639/1000000 : ℚ) by norm_num]
  exact coverp0011010001110
private noncomputable def ep0011010001111_0 : Blocks := edgeBlocks% "full/vectors/0011010001111-E-0000.bin"
noncomputable def ep0011010001111 : Blocks := ep0011010001111_0
private theorem idp0011010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101000111.list =
    C ((2:ℤ)^75) * horner X vp0011010001111.list + horner X ep0011010001111.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010001111 : Branch 1 (-1677761639/2000000 : ℚ) vp001101000111 := by
  apply branch_checked idp0011010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1677761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1678761639/1000000 : ℚ) by norm_num]
  exact coverp0011010001111
theorem coverp001101000111 : Covers (-1677761639/2000000 : ℚ) vp001101000111 := join_branches bp0011010001110 bp0011010001111
private noncomputable def vp0011010001101_0 : Blocks := edgeBlocks% "full/vectors/0011010001101-V-0000.bin"
noncomputable def vp0011010001101 : Blocks := vp0011010001101_0
theorem coverp0011010001101 : Covers (-1676761639/1000000 : ℚ) vp0011010001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010001100_0 : Blocks := edgeBlocks% "full/vectors/0011010001100-V-0000.bin"
noncomputable def vp0011010001100 : Blocks := vp0011010001100_0
theorem coverp0011010001100 : Covers (-1675761639/1000000 : ℚ) vp0011010001100 := cover_leaf (by decide +kernel)
private noncomputable def vp001101000110_0 : Blocks := edgeBlocks% "full/vectors/001101000110-V-0000.bin"
noncomputable def vp001101000110 : Blocks := vp001101000110_0
private theorem bp0011010001100 : Branch 0 (-1675761639/2000000 : ℚ) vp001101000110 := by
  apply branch_left_normalized (c:=vp0011010001100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1675761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1675761639/1000000 : ℚ) by norm_num]
  exact coverp0011010001100
private noncomputable def ep0011010001101_0 : Blocks := edgeBlocks% "full/vectors/0011010001101-E-0000.bin"
noncomputable def ep0011010001101 : Blocks := ep0011010001101_0
private theorem idp0011010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101000110.list =
    C ((2:ℤ)^75) * horner X vp0011010001101.list + horner X ep0011010001101.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010001101 : Branch 1 (-1675761639/2000000 : ℚ) vp001101000110 := by
  apply branch_checked idp0011010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1675761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1676761639/1000000 : ℚ) by norm_num]
  exact coverp0011010001101
theorem coverp001101000110 : Covers (-1675761639/2000000 : ℚ) vp001101000110 := join_branches bp0011010001100 bp0011010001101
private noncomputable def vp00110100011_0 : Blocks := edgeBlocks% "full/vectors/00110100011-V-0000.bin"
noncomputable def vp00110100011 : Blocks := vp00110100011_0
private theorem bp001101000110 : Branch 0 (-1675761639/4000000 : ℚ) vp00110100011 := by
  apply branch_left_normalized (c:=vp001101000110) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1675761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1675761639/2000000 : ℚ) by norm_num]
  exact coverp001101000110
private noncomputable def ep001101000111_0 : Blocks := edgeBlocks% "full/vectors/001101000111-E-0000.bin"
noncomputable def ep001101000111 : Blocks := ep001101000111_0
private theorem idp001101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110100011.list =
    C ((2:ℤ)^130) * horner X vp001101000111.list + horner X ep001101000111.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101000111 : Branch 1 (-1675761639/4000000 : ℚ) vp00110100011 := by
  apply branch_checked idp001101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1675761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1677761639/2000000 : ℚ) by norm_num]
  exact coverp001101000111
theorem coverp00110100011 : Covers (-1675761639/4000000 : ℚ) vp00110100011 := join_branches bp001101000110 bp001101000111
private noncomputable def vp0011010001011_0 : Blocks := edgeBlocks% "full/vectors/0011010001011-V-0000.bin"
noncomputable def vp0011010001011 : Blocks := vp0011010001011_0
theorem coverp0011010001011 : Covers (-1674761639/1000000 : ℚ) vp0011010001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010001010_0 : Blocks := edgeBlocks% "full/vectors/0011010001010-V-0000.bin"
noncomputable def vp0011010001010 : Blocks := vp0011010001010_0
theorem coverp0011010001010 : Covers (-1673761639/1000000 : ℚ) vp0011010001010 := cover_leaf (by decide +kernel)
private noncomputable def vp001101000101_0 : Blocks := edgeBlocks% "full/vectors/001101000101-V-0000.bin"
noncomputable def vp001101000101 : Blocks := vp001101000101_0
private theorem bp0011010001010 : Branch 0 (-1673761639/2000000 : ℚ) vp001101000101 := by
  apply branch_left_normalized (c:=vp0011010001010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1673761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1673761639/1000000 : ℚ) by norm_num]
  exact coverp0011010001010
private noncomputable def ep0011010001011_0 : Blocks := edgeBlocks% "full/vectors/0011010001011-E-0000.bin"
noncomputable def ep0011010001011 : Blocks := ep0011010001011_0
private theorem idp0011010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101000101.list =
    C ((2:ℤ)^74) * horner X vp0011010001011.list + horner X ep0011010001011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010001011 : Branch 1 (-1673761639/2000000 : ℚ) vp001101000101 := by
  apply branch_checked idp0011010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1673761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1674761639/1000000 : ℚ) by norm_num]
  exact coverp0011010001011
theorem coverp001101000101 : Covers (-1673761639/2000000 : ℚ) vp001101000101 := join_branches bp0011010001010 bp0011010001011
private noncomputable def vp0011010001001_0 : Blocks := edgeBlocks% "full/vectors/0011010001001-V-0000.bin"
noncomputable def vp0011010001001 : Blocks := vp0011010001001_0
theorem coverp0011010001001 : Covers (-1672761639/1000000 : ℚ) vp0011010001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010001000_0 : Blocks := edgeBlocks% "full/vectors/0011010001000-V-0000.bin"
noncomputable def vp0011010001000 : Blocks := vp0011010001000_0
theorem coverp0011010001000 : Covers (-1671761639/1000000 : ℚ) vp0011010001000 := cover_leaf (by decide +kernel)
private noncomputable def vp001101000100_0 : Blocks := edgeBlocks% "full/vectors/001101000100-V-0000.bin"
noncomputable def vp001101000100 : Blocks := vp001101000100_0
private theorem bp0011010001000 : Branch 0 (-1671761639/2000000 : ℚ) vp001101000100 := by
  apply branch_left_normalized (c:=vp0011010001000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1671761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1671761639/1000000 : ℚ) by norm_num]
  exact coverp0011010001000
private noncomputable def ep0011010001001_0 : Blocks := edgeBlocks% "full/vectors/0011010001001-E-0000.bin"
noncomputable def ep0011010001001 : Blocks := ep0011010001001_0
private theorem idp0011010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101000100.list =
    C ((2:ℤ)^75) * horner X vp0011010001001.list + horner X ep0011010001001.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010001001 : Branch 1 (-1671761639/2000000 : ℚ) vp001101000100 := by
  apply branch_checked idp0011010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1671761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1672761639/1000000 : ℚ) by norm_num]
  exact coverp0011010001001
theorem coverp001101000100 : Covers (-1671761639/2000000 : ℚ) vp001101000100 := join_branches bp0011010001000 bp0011010001001
private noncomputable def vp00110100010_0 : Blocks := edgeBlocks% "full/vectors/00110100010-V-0000.bin"
noncomputable def vp00110100010 : Blocks := vp00110100010_0
private theorem bp001101000100 : Branch 0 (-1671761639/4000000 : ℚ) vp00110100010 := by
  apply branch_left_normalized (c:=vp001101000100) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1671761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1671761639/2000000 : ℚ) by norm_num]
  exact coverp001101000100
private noncomputable def ep001101000101_0 : Blocks := edgeBlocks% "full/vectors/001101000101-E-0000.bin"
noncomputable def ep001101000101 : Blocks := ep001101000101_0
private theorem idp001101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110100010.list =
    C ((2:ℤ)^130) * horner X vp001101000101.list + horner X ep001101000101.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101000101 : Branch 1 (-1671761639/4000000 : ℚ) vp00110100010 := by
  apply branch_checked idp001101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1671761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1673761639/2000000 : ℚ) by norm_num]
  exact coverp001101000101
theorem coverp00110100010 : Covers (-1671761639/4000000 : ℚ) vp00110100010 := join_branches bp001101000100 bp001101000101
private noncomputable def vp0011010001_0 : Blocks := edgeBlocks% "full/vectors/0011010001-V-0000.bin"
private noncomputable def vp0011010001_1 : Blocks := edgeBlocks% "full/vectors/0011010001-V-0001.bin"
noncomputable def vp0011010001 : Blocks := (Blocks.join vp0011010001_0 vp0011010001_1)
private theorem bp00110100010 : Branch 0 (-1671761639/8000000 : ℚ) vp0011010001 := by
  apply branch_left_normalized (c:=vp00110100010) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-1671761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1671761639/4000000 : ℚ) by norm_num]
  exact coverp00110100010
private noncomputable def ep00110100011_0 : Blocks := edgeBlocks% "full/vectors/00110100011-E-0000.bin"
private noncomputable def ep00110100011_1 : Blocks := edgeBlocks% "full/vectors/00110100011-E-0001.bin"
noncomputable def ep00110100011 : Blocks := (Blocks.join ep00110100011_0 ep00110100011_1)
private theorem idp00110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011010001.list =
    C ((2:ℤ)^238) * horner X vp00110100011.list + horner X ep00110100011.list := by
  exact edge_identity (B := (2:ℤ)^418) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110100011 : Branch 1 (-1671761639/8000000 : ℚ) vp0011010001 := by
  apply branch_checked idp00110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1671761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1675761639/4000000 : ℚ) by norm_num]
  exact coverp00110100011
theorem coverp0011010001 : Covers (-1671761639/8000000 : ℚ) vp0011010001 := join_branches bp00110100010 bp00110100011
private noncomputable def vp0011010000111_0 : Blocks := edgeBlocks% "full/vectors/0011010000111-V-0000.bin"
noncomputable def vp0011010000111 : Blocks := vp0011010000111_0
theorem coverp0011010000111 : Covers (-1670761639/1000000 : ℚ) vp0011010000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010000110_0 : Blocks := edgeBlocks% "full/vectors/0011010000110-V-0000.bin"
noncomputable def vp0011010000110 : Blocks := vp0011010000110_0
theorem coverp0011010000110 : Covers (-1669761639/1000000 : ℚ) vp0011010000110 := cover_leaf (by decide +kernel)
private noncomputable def vp001101000011_0 : Blocks := edgeBlocks% "full/vectors/001101000011-V-0000.bin"
noncomputable def vp001101000011 : Blocks := vp001101000011_0
private theorem bp0011010000110 : Branch 0 (-1669761639/2000000 : ℚ) vp001101000011 := by
  apply branch_left_normalized (c:=vp0011010000110) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1669761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1669761639/1000000 : ℚ) by norm_num]
  exact coverp0011010000110
private noncomputable def ep0011010000111_0 : Blocks := edgeBlocks% "full/vectors/0011010000111-E-0000.bin"
noncomputable def ep0011010000111 : Blocks := ep0011010000111_0
private theorem idp0011010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101000011.list =
    C ((2:ℤ)^75) * horner X vp0011010000111.list + horner X ep0011010000111.list := by
  exact edge_identity (B := (2:ℤ)^196) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010000111 : Branch 1 (-1669761639/2000000 : ℚ) vp001101000011 := by
  apply branch_checked idp0011010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1669761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1670761639/1000000 : ℚ) by norm_num]
  exact coverp0011010000111
theorem coverp001101000011 : Covers (-1669761639/2000000 : ℚ) vp001101000011 := join_branches bp0011010000110 bp0011010000111
private noncomputable def vp0011010000101_0 : Blocks := edgeBlocks% "full/vectors/0011010000101-V-0000.bin"
noncomputable def vp0011010000101 : Blocks := vp0011010000101_0
theorem coverp0011010000101 : Covers (-1668761639/1000000 : ℚ) vp0011010000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010000100_0 : Blocks := edgeBlocks% "full/vectors/0011010000100-V-0000.bin"
noncomputable def vp0011010000100 : Blocks := vp0011010000100_0
theorem coverp0011010000100 : Covers (-1667761639/1000000 : ℚ) vp0011010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp001101000010_0 : Blocks := edgeBlocks% "full/vectors/001101000010-V-0000.bin"
noncomputable def vp001101000010 : Blocks := vp001101000010_0
private theorem bp0011010000100 : Branch 0 (-1667761639/2000000 : ℚ) vp001101000010 := by
  apply branch_left_normalized (c:=vp0011010000100) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1667761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1667761639/1000000 : ℚ) by norm_num]
  exact coverp0011010000100
private noncomputable def ep0011010000101_0 : Blocks := edgeBlocks% "full/vectors/0011010000101-E-0000.bin"
noncomputable def ep0011010000101 : Blocks := ep0011010000101_0
private theorem idp0011010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101000010.list =
    C ((2:ℤ)^75) * horner X vp0011010000101.list + horner X ep0011010000101.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010000101 : Branch 1 (-1667761639/2000000 : ℚ) vp001101000010 := by
  apply branch_checked idp0011010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1667761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1668761639/1000000 : ℚ) by norm_num]
  exact coverp0011010000101
theorem coverp001101000010 : Covers (-1667761639/2000000 : ℚ) vp001101000010 := join_branches bp0011010000100 bp0011010000101
private noncomputable def vp00110100001_0 : Blocks := edgeBlocks% "full/vectors/00110100001-V-0000.bin"
noncomputable def vp00110100001 : Blocks := vp00110100001_0
private theorem bp001101000010 : Branch 0 (-1667761639/4000000 : ℚ) vp00110100001 := by
  apply branch_left_normalized (c:=vp001101000010) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1667761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1667761639/2000000 : ℚ) by norm_num]
  exact coverp001101000010
private noncomputable def ep001101000011_0 : Blocks := edgeBlocks% "full/vectors/001101000011-E-0000.bin"
noncomputable def ep001101000011 : Blocks := ep001101000011_0
private theorem idp001101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110100001.list =
    C ((2:ℤ)^129) * horner X vp001101000011.list + horner X ep001101000011.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101000011 : Branch 1 (-1667761639/4000000 : ℚ) vp00110100001 := by
  apply branch_checked idp001101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1667761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1669761639/2000000 : ℚ) by norm_num]
  exact coverp001101000011
theorem coverp00110100001 : Covers (-1667761639/4000000 : ℚ) vp00110100001 := join_branches bp001101000010 bp001101000011
private noncomputable def vp0011010000011_0 : Blocks := edgeBlocks% "full/vectors/0011010000011-V-0000.bin"
noncomputable def vp0011010000011 : Blocks := vp0011010000011_0
theorem coverp0011010000011 : Covers (-1666761639/1000000 : ℚ) vp0011010000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010000010_0 : Blocks := edgeBlocks% "full/vectors/0011010000010-V-0000.bin"
noncomputable def vp0011010000010 : Blocks := vp0011010000010_0
theorem coverp0011010000010 : Covers (-1665761639/1000000 : ℚ) vp0011010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp001101000001_0 : Blocks := edgeBlocks% "full/vectors/001101000001-V-0000.bin"
noncomputable def vp001101000001 : Blocks := vp001101000001_0
private theorem bp0011010000010 : Branch 0 (-1665761639/2000000 : ℚ) vp001101000001 := by
  apply branch_left_normalized (c:=vp0011010000010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1665761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1665761639/1000000 : ℚ) by norm_num]
  exact coverp0011010000010
private noncomputable def ep0011010000011_0 : Blocks := edgeBlocks% "full/vectors/0011010000011-E-0000.bin"
noncomputable def ep0011010000011 : Blocks := ep0011010000011_0
private theorem idp0011010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101000001.list =
    C ((2:ℤ)^74) * horner X vp0011010000011.list + horner X ep0011010000011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010000011 : Branch 1 (-1665761639/2000000 : ℚ) vp001101000001 := by
  apply branch_checked idp0011010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1665761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1666761639/1000000 : ℚ) by norm_num]
  exact coverp0011010000011
theorem coverp001101000001 : Covers (-1665761639/2000000 : ℚ) vp001101000001 := join_branches bp0011010000010 bp0011010000011
private noncomputable def vp0011010000001_0 : Blocks := edgeBlocks% "full/vectors/0011010000001-V-0000.bin"
noncomputable def vp0011010000001 : Blocks := vp0011010000001_0
theorem coverp0011010000001 : Covers (-1664761639/1000000 : ℚ) vp0011010000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011010000000_0 : Blocks := edgeBlocks% "full/vectors/0011010000000-V-0000.bin"
noncomputable def vp0011010000000 : Blocks := vp0011010000000_0
theorem coverp0011010000000 : Covers (-1663761639/1000000 : ℚ) vp0011010000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001101000000_0 : Blocks := edgeBlocks% "full/vectors/001101000000-V-0000.bin"
noncomputable def vp001101000000 : Blocks := vp001101000000_0
private theorem bp0011010000000 : Branch 0 (-1663761639/2000000 : ℚ) vp001101000000 := by
  apply branch_left_normalized (c:=vp0011010000000) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-1663761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1663761639/1000000 : ℚ) by norm_num]
  exact coverp0011010000000
private noncomputable def ep0011010000001_0 : Blocks := edgeBlocks% "full/vectors/0011010000001-E-0000.bin"
noncomputable def ep0011010000001 : Blocks := ep0011010000001_0
private theorem idp0011010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101000000.list =
    C ((2:ℤ)^75) * horner X vp0011010000001.list + horner X ep0011010000001.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010000001 : Branch 1 (-1663761639/2000000 : ℚ) vp001101000000 := by
  apply branch_checked idp0011010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1663761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1664761639/1000000 : ℚ) by norm_num]
  exact coverp0011010000001
theorem coverp001101000000 : Covers (-1663761639/2000000 : ℚ) vp001101000000 := join_branches bp0011010000000 bp0011010000001
private noncomputable def vp00110100000_0 : Blocks := edgeBlocks% "full/vectors/00110100000-V-0000.bin"
noncomputable def vp00110100000 : Blocks := vp00110100000_0
private theorem bp001101000000 : Branch 0 (-1663761639/4000000 : ℚ) vp00110100000 := by
  apply branch_left_normalized (c:=vp001101000000) (k:=0) (m:=68) (by decide +kernel)
  rw [show 2*(-1663761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1663761639/2000000 : ℚ) by norm_num]
  exact coverp001101000000
private noncomputable def ep001101000001_0 : Blocks := edgeBlocks% "full/vectors/001101000001-E-0000.bin"
noncomputable def ep001101000001 : Blocks := ep001101000001_0
private theorem idp001101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110100000.list =
    C ((2:ℤ)^130) * horner X vp001101000001.list + horner X ep001101000001.list := by
  exact edge_identity (B := (2:ℤ)^270) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101000001 : Branch 1 (-1663761639/4000000 : ℚ) vp00110100000 := by
  apply branch_checked idp001101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1663761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1665761639/2000000 : ℚ) by norm_num]
  exact coverp001101000001
theorem coverp00110100000 : Covers (-1663761639/4000000 : ℚ) vp00110100000 := join_branches bp001101000000 bp001101000001
private noncomputable def vp0011010000_0 : Blocks := edgeBlocks% "full/vectors/0011010000-V-0000.bin"
private noncomputable def vp0011010000_1 : Blocks := edgeBlocks% "full/vectors/0011010000-V-0001.bin"
noncomputable def vp0011010000 : Blocks := (Blocks.join vp0011010000_0 vp0011010000_1)
private theorem bp00110100000 : Branch 0 (-1663761639/8000000 : ℚ) vp0011010000 := by
  apply branch_left_normalized (c:=vp00110100000) (k:=0) (m:=117) (by decide +kernel)
  rw [show 2*(-1663761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1663761639/4000000 : ℚ) by norm_num]
  exact coverp00110100000
private noncomputable def ep00110100001_0 : Blocks := edgeBlocks% "full/vectors/00110100001-E-0000.bin"
private noncomputable def ep00110100001_1 : Blocks := edgeBlocks% "full/vectors/00110100001-E-0001.bin"
noncomputable def ep00110100001 : Blocks := (Blocks.join ep00110100001_0 ep00110100001_1)
private theorem idp00110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011010000.list =
    C ((2:ℤ)^238) * horner X vp00110100001.list + horner X ep00110100001.list := by
  exact edge_identity (B := (2:ℤ)^418) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110100001 : Branch 1 (-1663761639/8000000 : ℚ) vp0011010000 := by
  apply branch_checked idp00110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1663761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1667761639/4000000 : ℚ) by norm_num]
  exact coverp00110100001
theorem coverp0011010000 : Covers (-1663761639/8000000 : ℚ) vp0011010000 := join_branches bp00110100000 bp00110100001
private noncomputable def vp001101000_0 : Blocks := edgeBlocks% "full/vectors/001101000-V-0000.bin"
private noncomputable def vp001101000_1 : Blocks := edgeBlocks% "full/vectors/001101000-V-0001.bin"
private noncomputable def vp001101000_2 : Blocks := edgeBlocks% "full/vectors/001101000-V-0002.bin"
private noncomputable def vp001101000_3 : Blocks := edgeBlocks% "full/vectors/001101000-V-0003.bin"
noncomputable def vp001101000 : Blocks := (Blocks.join (Blocks.join vp001101000_0 vp001101000_1) (Blocks.join vp001101000_2 vp001101000_3))
private theorem bp0011010000 : Branch 0 (-1663761639/16000000 : ℚ) vp001101000 := by
  apply branch_left_normalized (c:=vp0011010000) (k:=0) (m:=214) (by decide +kernel)
  rw [show 2*(-1663761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1663761639/8000000 : ℚ) by norm_num]
  exact coverp0011010000
private noncomputable def ep0011010001_0 : Blocks := edgeBlocks% "full/vectors/0011010001-E-0000.bin"
private noncomputable def ep0011010001_1 : Blocks := edgeBlocks% "full/vectors/0011010001-E-0001.bin"
private noncomputable def ep0011010001_2 : Blocks := edgeBlocks% "full/vectors/0011010001-E-0002.bin"
private noncomputable def ep0011010001_3 : Blocks := edgeBlocks% "full/vectors/0011010001-E-0003.bin"
noncomputable def ep0011010001 : Blocks := (Blocks.join (Blocks.join ep0011010001_0 ep0011010001_1) (Blocks.join ep0011010001_2 ep0011010001_3))
private theorem idp0011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101000.list =
    C ((2:ℤ)^453) * horner X vp0011010001.list + horner X ep0011010001.list := by
  exact edge_identity (B := (2:ℤ)^712) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011010001 : Branch 1 (-1663761639/16000000 : ℚ) vp001101000 := by
  apply branch_checked idp0011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1663761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1671761639/8000000 : ℚ) by norm_num]
  exact coverp0011010001
theorem coverp001101000 : Covers (-1663761639/16000000 : ℚ) vp001101000 := join_branches bp0011010000 bp0011010001
private noncomputable def vp00110100_0 : Blocks := edgeBlocks% "full/vectors/00110100-V-0000.bin"
private noncomputable def vp00110100_1 : Blocks := edgeBlocks% "full/vectors/00110100-V-0001.bin"
private noncomputable def vp00110100_2 : Blocks := edgeBlocks% "full/vectors/00110100-V-0002.bin"
private noncomputable def vp00110100_3 : Blocks := edgeBlocks% "full/vectors/00110100-V-0003.bin"
private noncomputable def vp00110100_4 : Blocks := edgeBlocks% "full/vectors/00110100-V-0004.bin"
private noncomputable def vp00110100_5 : Blocks := edgeBlocks% "full/vectors/00110100-V-0005.bin"
private noncomputable def vp00110100_6 : Blocks := edgeBlocks% "full/vectors/00110100-V-0006.bin"
noncomputable def vp00110100 : Blocks := (Blocks.join (Blocks.join vp00110100_0 (Blocks.join vp00110100_1 vp00110100_2)) (Blocks.join (Blocks.join vp00110100_3 vp00110100_4) (Blocks.join vp00110100_5 vp00110100_6)))
private theorem bp001101000 : Branch 0 (-1663761639/32000000 : ℚ) vp00110100 := by
  apply branch_left_normalized (c:=vp001101000) (k:=0) (m:=406) (by decide +kernel)
  rw [show 2*(-1663761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1663761639/16000000 : ℚ) by norm_num]
  exact coverp001101000
private noncomputable def ep001101001_0 : Blocks := edgeBlocks% "full/vectors/001101001-E-0000.bin"
private noncomputable def ep001101001_1 : Blocks := edgeBlocks% "full/vectors/001101001-E-0001.bin"
private noncomputable def ep001101001_2 : Blocks := edgeBlocks% "full/vectors/001101001-E-0002.bin"
private noncomputable def ep001101001_3 : Blocks := edgeBlocks% "full/vectors/001101001-E-0003.bin"
private noncomputable def ep001101001_4 : Blocks := edgeBlocks% "full/vectors/001101001-E-0004.bin"
private noncomputable def ep001101001_5 : Blocks := edgeBlocks% "full/vectors/001101001-E-0005.bin"
private noncomputable def ep001101001_6 : Blocks := edgeBlocks% "full/vectors/001101001-E-0006.bin"
noncomputable def ep001101001 : Blocks := (Blocks.join (Blocks.join ep001101001_0 (Blocks.join ep001101001_1 ep001101001_2)) (Blocks.join (Blocks.join ep001101001_3 ep001101001_4) (Blocks.join ep001101001_5 ep001101001_6)))
private theorem idp001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110100.list =
    C ((2:ℤ)^878) * horner X vp001101001.list + horner X ep001101001.list := by
  exact edge_identity (B := (2:ℤ)^1295) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101001 : Branch 1 (-1663761639/32000000 : ℚ) vp00110100 := by
  apply branch_checked idp001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1663761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1679761639/16000000 : ℚ) by norm_num]
  exact coverp001101001
theorem coverp00110100 : Covers (-1663761639/32000000 : ℚ) vp00110100 := join_branches bp001101000 bp001101001
private noncomputable def vp0011010_0 : Blocks := edgeBlocks% "full/vectors/0011010-V-0000.bin"
private noncomputable def vp0011010_1 : Blocks := edgeBlocks% "full/vectors/0011010-V-0001.bin"
private noncomputable def vp0011010_2 : Blocks := edgeBlocks% "full/vectors/0011010-V-0002.bin"
private noncomputable def vp0011010_3 : Blocks := edgeBlocks% "full/vectors/0011010-V-0003.bin"
private noncomputable def vp0011010_4 : Blocks := edgeBlocks% "full/vectors/0011010-V-0004.bin"
private noncomputable def vp0011010_5 : Blocks := edgeBlocks% "full/vectors/0011010-V-0005.bin"
private noncomputable def vp0011010_6 : Blocks := edgeBlocks% "full/vectors/0011010-V-0006.bin"
private noncomputable def vp0011010_7 : Blocks := edgeBlocks% "full/vectors/0011010-V-0007.bin"
private noncomputable def vp0011010_8 : Blocks := edgeBlocks% "full/vectors/0011010-V-0008.bin"
private noncomputable def vp0011010_9 : Blocks := edgeBlocks% "full/vectors/0011010-V-0009.bin"
private noncomputable def vp0011010_10 : Blocks := edgeBlocks% "full/vectors/0011010-V-0010.bin"
private noncomputable def vp0011010_11 : Blocks := edgeBlocks% "full/vectors/0011010-V-0011.bin"
noncomputable def vp0011010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0011010_0 (Blocks.join vp0011010_1 vp0011010_2)) (Blocks.join vp0011010_3 (Blocks.join vp0011010_4 vp0011010_5))) (Blocks.join (Blocks.join vp0011010_6 (Blocks.join vp0011010_7 vp0011010_8)) (Blocks.join vp0011010_9 (Blocks.join vp0011010_10 vp0011010_11))))
private theorem bp00110100 : Branch 0 (-1663761639/64000000 : ℚ) vp0011010 := by
  apply branch_left_normalized (c:=vp00110100) (k:=0) (m:=785) (by decide +kernel)
  rw [show 2*(-1663761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1663761639/32000000 : ℚ) by norm_num]
  exact coverp00110100
private noncomputable def ep00110101_0 : Blocks := edgeBlocks% "full/vectors/00110101-E-0000.bin"
private noncomputable def ep00110101_1 : Blocks := edgeBlocks% "full/vectors/00110101-E-0001.bin"
private noncomputable def ep00110101_2 : Blocks := edgeBlocks% "full/vectors/00110101-E-0002.bin"
private noncomputable def ep00110101_3 : Blocks := edgeBlocks% "full/vectors/00110101-E-0003.bin"
private noncomputable def ep00110101_4 : Blocks := edgeBlocks% "full/vectors/00110101-E-0004.bin"
private noncomputable def ep00110101_5 : Blocks := edgeBlocks% "full/vectors/00110101-E-0005.bin"
private noncomputable def ep00110101_6 : Blocks := edgeBlocks% "full/vectors/00110101-E-0006.bin"
private noncomputable def ep00110101_7 : Blocks := edgeBlocks% "full/vectors/00110101-E-0007.bin"
private noncomputable def ep00110101_8 : Blocks := edgeBlocks% "full/vectors/00110101-E-0008.bin"
private noncomputable def ep00110101_9 : Blocks := edgeBlocks% "full/vectors/00110101-E-0009.bin"
private noncomputable def ep00110101_10 : Blocks := edgeBlocks% "full/vectors/00110101-E-0010.bin"
private noncomputable def ep00110101_11 : Blocks := edgeBlocks% "full/vectors/00110101-E-0011.bin"
noncomputable def ep00110101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00110101_0 (Blocks.join ep00110101_1 ep00110101_2)) (Blocks.join ep00110101_3 (Blocks.join ep00110101_4 ep00110101_5))) (Blocks.join (Blocks.join ep00110101_6 (Blocks.join ep00110101_7 ep00110101_8)) (Blocks.join ep00110101_9 (Blocks.join ep00110101_10 ep00110101_11))))
private theorem idp00110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011010.list =
    C ((2:ℤ)^1715) * horner X vp00110101.list + horner X ep00110101.list := by
  exact edge_identity (B := (2:ℤ)^2444) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110101 : Branch 1 (-1663761639/64000000 : ℚ) vp0011010 := by
  apply branch_checked idp00110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1663761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1695761639/32000000 : ℚ) by norm_num]
  exact coverp00110101
theorem coverp0011010 : Covers (-1663761639/64000000 : ℚ) vp0011010 := join_branches bp00110100 bp00110101
private noncomputable def vp001101_0 : Blocks := edgeBlocks% "full/vectors/001101-V-0000.bin"
private noncomputable def vp001101_1 : Blocks := edgeBlocks% "full/vectors/001101-V-0001.bin"
private noncomputable def vp001101_2 : Blocks := edgeBlocks% "full/vectors/001101-V-0002.bin"
private noncomputable def vp001101_3 : Blocks := edgeBlocks% "full/vectors/001101-V-0003.bin"
private noncomputable def vp001101_4 : Blocks := edgeBlocks% "full/vectors/001101-V-0004.bin"
private noncomputable def vp001101_5 : Blocks := edgeBlocks% "full/vectors/001101-V-0005.bin"
private noncomputable def vp001101_6 : Blocks := edgeBlocks% "full/vectors/001101-V-0006.bin"
private noncomputable def vp001101_7 : Blocks := edgeBlocks% "full/vectors/001101-V-0007.bin"
private noncomputable def vp001101_8 : Blocks := edgeBlocks% "full/vectors/001101-V-0008.bin"
private noncomputable def vp001101_9 : Blocks := edgeBlocks% "full/vectors/001101-V-0009.bin"
private noncomputable def vp001101_10 : Blocks := edgeBlocks% "full/vectors/001101-V-0010.bin"
private noncomputable def vp001101_11 : Blocks := edgeBlocks% "full/vectors/001101-V-0011.bin"
private noncomputable def vp001101_12 : Blocks := edgeBlocks% "full/vectors/001101-V-0012.bin"
private noncomputable def vp001101_13 : Blocks := edgeBlocks% "full/vectors/001101-V-0013.bin"
private noncomputable def vp001101_14 : Blocks := edgeBlocks% "full/vectors/001101-V-0014.bin"
private noncomputable def vp001101_15 : Blocks := edgeBlocks% "full/vectors/001101-V-0015.bin"
private noncomputable def vp001101_16 : Blocks := edgeBlocks% "full/vectors/001101-V-0016.bin"
private noncomputable def vp001101_17 : Blocks := edgeBlocks% "full/vectors/001101-V-0017.bin"
private noncomputable def vp001101_18 : Blocks := edgeBlocks% "full/vectors/001101-V-0018.bin"
private noncomputable def vp001101_19 : Blocks := edgeBlocks% "full/vectors/001101-V-0019.bin"
private noncomputable def vp001101_20 : Blocks := edgeBlocks% "full/vectors/001101-V-0020.bin"
private noncomputable def vp001101_21 : Blocks := edgeBlocks% "full/vectors/001101-V-0021.bin"
private noncomputable def vp001101_22 : Blocks := edgeBlocks% "full/vectors/001101-V-0022.bin"
private noncomputable def vp001101_23 : Blocks := edgeBlocks% "full/vectors/001101-V-0023.bin"
noncomputable def vp001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp001101_0 (Blocks.join vp001101_1 vp001101_2)) (Blocks.join vp001101_3 (Blocks.join vp001101_4 vp001101_5))) (Blocks.join (Blocks.join vp001101_6 (Blocks.join vp001101_7 vp001101_8)) (Blocks.join vp001101_9 (Blocks.join vp001101_10 vp001101_11)))) (Blocks.join (Blocks.join (Blocks.join vp001101_12 (Blocks.join vp001101_13 vp001101_14)) (Blocks.join vp001101_15 (Blocks.join vp001101_16 vp001101_17))) (Blocks.join (Blocks.join vp001101_18 (Blocks.join vp001101_19 vp001101_20)) (Blocks.join vp001101_21 (Blocks.join vp001101_22 vp001101_23)))))
private theorem bp0011010 : Branch 0 (-1663761639/128000000 : ℚ) vp001101 := by
  apply branch_left_normalized (c:=vp0011010) (k:=0) (m:=1530) (by decide +kernel)
  rw [show 2*(-1663761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-1663761639/64000000 : ℚ) by norm_num]
  exact coverp0011010
private noncomputable def ep0011011_0 : Blocks := edgeBlocks% "full/vectors/0011011-E-0000.bin"
private noncomputable def ep0011011_1 : Blocks := edgeBlocks% "full/vectors/0011011-E-0001.bin"
private noncomputable def ep0011011_2 : Blocks := edgeBlocks% "full/vectors/0011011-E-0002.bin"
private noncomputable def ep0011011_3 : Blocks := edgeBlocks% "full/vectors/0011011-E-0003.bin"
private noncomputable def ep0011011_4 : Blocks := edgeBlocks% "full/vectors/0011011-E-0004.bin"
private noncomputable def ep0011011_5 : Blocks := edgeBlocks% "full/vectors/0011011-E-0005.bin"
private noncomputable def ep0011011_6 : Blocks := edgeBlocks% "full/vectors/0011011-E-0006.bin"
private noncomputable def ep0011011_7 : Blocks := edgeBlocks% "full/vectors/0011011-E-0007.bin"
private noncomputable def ep0011011_8 : Blocks := edgeBlocks% "full/vectors/0011011-E-0008.bin"
private noncomputable def ep0011011_9 : Blocks := edgeBlocks% "full/vectors/0011011-E-0009.bin"
private noncomputable def ep0011011_10 : Blocks := edgeBlocks% "full/vectors/0011011-E-0010.bin"
private noncomputable def ep0011011_11 : Blocks := edgeBlocks% "full/vectors/0011011-E-0011.bin"
private noncomputable def ep0011011_12 : Blocks := edgeBlocks% "full/vectors/0011011-E-0012.bin"
private noncomputable def ep0011011_13 : Blocks := edgeBlocks% "full/vectors/0011011-E-0013.bin"
private noncomputable def ep0011011_14 : Blocks := edgeBlocks% "full/vectors/0011011-E-0014.bin"
private noncomputable def ep0011011_15 : Blocks := edgeBlocks% "full/vectors/0011011-E-0015.bin"
private noncomputable def ep0011011_16 : Blocks := edgeBlocks% "full/vectors/0011011-E-0016.bin"
private noncomputable def ep0011011_17 : Blocks := edgeBlocks% "full/vectors/0011011-E-0017.bin"
private noncomputable def ep0011011_18 : Blocks := edgeBlocks% "full/vectors/0011011-E-0018.bin"
private noncomputable def ep0011011_19 : Blocks := edgeBlocks% "full/vectors/0011011-E-0019.bin"
private noncomputable def ep0011011_20 : Blocks := edgeBlocks% "full/vectors/0011011-E-0020.bin"
private noncomputable def ep0011011_21 : Blocks := edgeBlocks% "full/vectors/0011011-E-0021.bin"
private noncomputable def ep0011011_22 : Blocks := edgeBlocks% "full/vectors/0011011-E-0022.bin"
private noncomputable def ep0011011_23 : Blocks := edgeBlocks% "full/vectors/0011011-E-0023.bin"
noncomputable def ep0011011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0011011_0 (Blocks.join ep0011011_1 ep0011011_2)) (Blocks.join ep0011011_3 (Blocks.join ep0011011_4 ep0011011_5))) (Blocks.join (Blocks.join ep0011011_6 (Blocks.join ep0011011_7 ep0011011_8)) (Blocks.join ep0011011_9 (Blocks.join ep0011011_10 ep0011011_11)))) (Blocks.join (Blocks.join (Blocks.join ep0011011_12 (Blocks.join ep0011011_13 ep0011011_14)) (Blocks.join ep0011011_15 (Blocks.join ep0011011_16 ep0011011_17))) (Blocks.join (Blocks.join ep0011011_18 (Blocks.join ep0011011_19 ep0011011_20)) (Blocks.join ep0011011_21 (Blocks.join ep0011011_22 ep0011011_23)))))
private def ptsp0011011 : List ℤ := [((2:ℤ)^4045+0),((2:ℤ)^4045+1)]
private theorem boundp0011011 : 2^vp001101.size*absSum vp001101.list + ((2:ℤ)^3337*absSum vp0011011.list+absSum ep0011011.list) < (2:ℤ)^4678 := by decide +kernel
private theorem pointp0011011_0 : fastHom 1 ((2:ℤ)^4045+0) vp001101 = ((2:ℤ)^3337)*vp0011011.subst ((2:ℤ)^4045+0)+ep0011011.subst ((2:ℤ)^4045+0) := by decide +kernel
private theorem pointp0011011_1 : fastHom 1 ((2:ℤ)^4045+1) vp001101 = ((2:ℤ)^3337)*vp0011011.subst ((2:ℤ)^4045+1)+ep0011011.subst ((2:ℤ)^4045+1) := by decide +kernel
private theorem checkp0011011 (x:ℤ) (hx:x ∈ ptsp0011011) : fastHom 1 x vp001101 = ((2:ℤ)^3337)*vp0011011.subst x+ep0011011.subst x := by
  simp only [ptsp0011011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp0011011_0
  · exact pointp0011011_1
private theorem idp0011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101.list =
    C ((2:ℤ)^3337) * horner X vp0011011.list + horner X ep0011011.list := by
  apply edge_identity (B := (2:ℤ)^4678) (by decide) (by positivity) (by positivity) boundp0011011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0011011 (by decide +kernel)
  · have h : ptsp0011011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0011011.trans_le (by decide +kernel)
  · exact checkp0011011
private theorem bp0011011 : Branch 1 (-1663761639/128000000 : ℚ) vp001101 := by
  apply branch_checked idp0011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1663761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-1727761639/64000000 : ℚ) by norm_num]
  exact coverp0011011
theorem coverp001101 : Covers (-1663761639/128000000 : ℚ) vp001101 := join_branches bp0011010 bp0011011
end NextProof.EdgeFull

