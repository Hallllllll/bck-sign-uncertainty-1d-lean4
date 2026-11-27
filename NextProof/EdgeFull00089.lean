import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00088

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0010010111111_0 : Blocks := edgeBlocks% "full/vectors/0010010111111-V-0000.bin"
noncomputable def vp0010010111111 : Blocks := vp0010010111111_0
theorem coverp0010010111111 : Covers (-1214761639/1000000 : ℚ) vp0010010111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010111110_0 : Blocks := edgeBlocks% "full/vectors/0010010111110-V-0000.bin"
noncomputable def vp0010010111110 : Blocks := vp0010010111110_0
theorem coverp0010010111110 : Covers (-1213761639/1000000 : ℚ) vp0010010111110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001011111_0 : Blocks := edgeBlocks% "full/vectors/001001011111-V-0000.bin"
noncomputable def vp001001011111 : Blocks := vp001001011111_0
private theorem bp0010010111110 : Branch 0 (-1213761639/2000000 : ℚ) vp001001011111 := by
  apply branch_left_normalized (c:=vp0010010111110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1213761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1213761639/1000000 : ℚ) by norm_num]
  exact coverp0010010111110
private noncomputable def ep0010010111111_0 : Blocks := edgeBlocks% "full/vectors/0010010111111-E-0000.bin"
noncomputable def ep0010010111111 : Blocks := ep0010010111111_0
private theorem idp0010010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001011111.list =
    C ((2:ℤ)^83) * horner X vp0010010111111.list + horner X ep0010010111111.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010111111 : Branch 1 (-1213761639/2000000 : ℚ) vp001001011111 := by
  apply branch_checked idp0010010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1213761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1214761639/1000000 : ℚ) by norm_num]
  exact coverp0010010111111
theorem coverp001001011111 : Covers (-1213761639/2000000 : ℚ) vp001001011111 := join_branches bp0010010111110 bp0010010111111
private noncomputable def vp0010010111101_0 : Blocks := edgeBlocks% "full/vectors/0010010111101-V-0000.bin"
noncomputable def vp0010010111101 : Blocks := vp0010010111101_0
theorem coverp0010010111101 : Covers (-1212761639/1000000 : ℚ) vp0010010111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010111100_0 : Blocks := edgeBlocks% "full/vectors/0010010111100-V-0000.bin"
noncomputable def vp0010010111100 : Blocks := vp0010010111100_0
theorem coverp0010010111100 : Covers (-1211761639/1000000 : ℚ) vp0010010111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001011110_0 : Blocks := edgeBlocks% "full/vectors/001001011110-V-0000.bin"
noncomputable def vp001001011110 : Blocks := vp001001011110_0
private theorem bp0010010111100 : Branch 0 (-1211761639/2000000 : ℚ) vp001001011110 := by
  apply branch_left_normalized (c:=vp0010010111100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1211761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1211761639/1000000 : ℚ) by norm_num]
  exact coverp0010010111100
private noncomputable def ep0010010111101_0 : Blocks := edgeBlocks% "full/vectors/0010010111101-E-0000.bin"
noncomputable def ep0010010111101 : Blocks := ep0010010111101_0
private theorem idp0010010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001011110.list =
    C ((2:ℤ)^83) * horner X vp0010010111101.list + horner X ep0010010111101.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010111101 : Branch 1 (-1211761639/2000000 : ℚ) vp001001011110 := by
  apply branch_checked idp0010010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1211761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1212761639/1000000 : ℚ) by norm_num]
  exact coverp0010010111101
theorem coverp001001011110 : Covers (-1211761639/2000000 : ℚ) vp001001011110 := join_branches bp0010010111100 bp0010010111101
private noncomputable def vp00100101111_0 : Blocks := edgeBlocks% "full/vectors/00100101111-V-0000.bin"
private noncomputable def vp00100101111_1 : Blocks := edgeBlocks% "full/vectors/00100101111-V-0001.bin"
noncomputable def vp00100101111 : Blocks := (Blocks.join vp00100101111_0 vp00100101111_1)
private theorem bp001001011110 : Branch 0 (-1211761639/4000000 : ℚ) vp00100101111 := by
  apply branch_left_normalized (c:=vp001001011110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1211761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1211761639/2000000 : ℚ) by norm_num]
  exact coverp001001011110
private noncomputable def ep001001011111_0 : Blocks := edgeBlocks% "full/vectors/001001011111-E-0000.bin"
private noncomputable def ep001001011111_1 : Blocks := edgeBlocks% "full/vectors/001001011111-E-0001.bin"
noncomputable def ep001001011111 : Blocks := (Blocks.join ep001001011111_0 ep001001011111_1)
private theorem idp001001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100101111.list =
    C ((2:ℤ)^147) * horner X vp001001011111.list + horner X ep001001011111.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001011111 : Branch 1 (-1211761639/4000000 : ℚ) vp00100101111 := by
  apply branch_checked idp001001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1211761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1213761639/2000000 : ℚ) by norm_num]
  exact coverp001001011111
theorem coverp00100101111 : Covers (-1211761639/4000000 : ℚ) vp00100101111 := join_branches bp001001011110 bp001001011111
private noncomputable def vp0010010111011_0 : Blocks := edgeBlocks% "full/vectors/0010010111011-V-0000.bin"
noncomputable def vp0010010111011 : Blocks := vp0010010111011_0
theorem coverp0010010111011 : Covers (-1210761639/1000000 : ℚ) vp0010010111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010111010_0 : Blocks := edgeBlocks% "full/vectors/0010010111010-V-0000.bin"
noncomputable def vp0010010111010 : Blocks := vp0010010111010_0
theorem coverp0010010111010 : Covers (-1209761639/1000000 : ℚ) vp0010010111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001011101_0 : Blocks := edgeBlocks% "full/vectors/001001011101-V-0000.bin"
noncomputable def vp001001011101 : Blocks := vp001001011101_0
private theorem bp0010010111010 : Branch 0 (-1209761639/2000000 : ℚ) vp001001011101 := by
  apply branch_left_normalized (c:=vp0010010111010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1209761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1209761639/1000000 : ℚ) by norm_num]
  exact coverp0010010111010
private noncomputable def ep0010010111011_0 : Blocks := edgeBlocks% "full/vectors/0010010111011-E-0000.bin"
noncomputable def ep0010010111011 : Blocks := ep0010010111011_0
private theorem idp0010010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001011101.list =
    C ((2:ℤ)^84) * horner X vp0010010111011.list + horner X ep0010010111011.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010111011 : Branch 1 (-1209761639/2000000 : ℚ) vp001001011101 := by
  apply branch_checked idp0010010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1209761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1210761639/1000000 : ℚ) by norm_num]
  exact coverp0010010111011
theorem coverp001001011101 : Covers (-1209761639/2000000 : ℚ) vp001001011101 := join_branches bp0010010111010 bp0010010111011
private noncomputable def vp0010010111001_0 : Blocks := edgeBlocks% "full/vectors/0010010111001-V-0000.bin"
noncomputable def vp0010010111001 : Blocks := vp0010010111001_0
theorem coverp0010010111001 : Covers (-1208761639/1000000 : ℚ) vp0010010111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010111000_0 : Blocks := edgeBlocks% "full/vectors/0010010111000-V-0000.bin"
noncomputable def vp0010010111000 : Blocks := vp0010010111000_0
theorem coverp0010010111000 : Covers (-1207761639/1000000 : ℚ) vp0010010111000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001011100_0 : Blocks := edgeBlocks% "full/vectors/001001011100-V-0000.bin"
noncomputable def vp001001011100 : Blocks := vp001001011100_0
private theorem bp0010010111000 : Branch 0 (-1207761639/2000000 : ℚ) vp001001011100 := by
  apply branch_left_normalized (c:=vp0010010111000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1207761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1207761639/1000000 : ℚ) by norm_num]
  exact coverp0010010111000
private noncomputable def ep0010010111001_0 : Blocks := edgeBlocks% "full/vectors/0010010111001-E-0000.bin"
noncomputable def ep0010010111001 : Blocks := ep0010010111001_0
private theorem idp0010010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001011100.list =
    C ((2:ℤ)^84) * horner X vp0010010111001.list + horner X ep0010010111001.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010111001 : Branch 1 (-1207761639/2000000 : ℚ) vp001001011100 := by
  apply branch_checked idp0010010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1207761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1208761639/1000000 : ℚ) by norm_num]
  exact coverp0010010111001
theorem coverp001001011100 : Covers (-1207761639/2000000 : ℚ) vp001001011100 := join_branches bp0010010111000 bp0010010111001
private noncomputable def vp00100101110_0 : Blocks := edgeBlocks% "full/vectors/00100101110-V-0000.bin"
private noncomputable def vp00100101110_1 : Blocks := edgeBlocks% "full/vectors/00100101110-V-0001.bin"
noncomputable def vp00100101110 : Blocks := (Blocks.join vp00100101110_0 vp00100101110_1)
private theorem bp001001011100 : Branch 0 (-1207761639/4000000 : ℚ) vp00100101110 := by
  apply branch_left_normalized (c:=vp001001011100) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1207761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1207761639/2000000 : ℚ) by norm_num]
  exact coverp001001011100
private noncomputable def ep001001011101_0 : Blocks := edgeBlocks% "full/vectors/001001011101-E-0000.bin"
private noncomputable def ep001001011101_1 : Blocks := edgeBlocks% "full/vectors/001001011101-E-0001.bin"
noncomputable def ep001001011101 : Blocks := (Blocks.join ep001001011101_0 ep001001011101_1)
private theorem idp001001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100101110.list =
    C ((2:ℤ)^148) * horner X vp001001011101.list + horner X ep001001011101.list := by
  exact edge_identity (B := (2:ℤ)^297) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001011101 : Branch 1 (-1207761639/4000000 : ℚ) vp00100101110 := by
  apply branch_checked idp001001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1207761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1209761639/2000000 : ℚ) by norm_num]
  exact coverp001001011101
theorem coverp00100101110 : Covers (-1207761639/4000000 : ℚ) vp00100101110 := join_branches bp001001011100 bp001001011101
private noncomputable def vp0010010111_0 : Blocks := edgeBlocks% "full/vectors/0010010111-V-0000.bin"
private noncomputable def vp0010010111_1 : Blocks := edgeBlocks% "full/vectors/0010010111-V-0001.bin"
noncomputable def vp0010010111 : Blocks := (Blocks.join vp0010010111_0 vp0010010111_1)
private theorem bp00100101110 : Branch 0 (-1207761639/8000000 : ℚ) vp0010010111 := by
  apply branch_left_normalized (c:=vp00100101110) (k:=0) (m:=135) (by decide +kernel)
  rw [show 2*(-1207761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1207761639/4000000 : ℚ) by norm_num]
  exact coverp00100101110
private noncomputable def ep00100101111_0 : Blocks := edgeBlocks% "full/vectors/00100101111-E-0000.bin"
private noncomputable def ep00100101111_1 : Blocks := edgeBlocks% "full/vectors/00100101111-E-0001.bin"
noncomputable def ep00100101111 : Blocks := (Blocks.join ep00100101111_0 ep00100101111_1)
private theorem idp00100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010010111.list =
    C ((2:ℤ)^273) * horner X vp00100101111.list + horner X ep00100101111.list := by
  exact edge_identity (B := (2:ℤ)^470) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100101111 : Branch 1 (-1207761639/8000000 : ℚ) vp0010010111 := by
  apply branch_checked idp00100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1207761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1211761639/4000000 : ℚ) by norm_num]
  exact coverp00100101111
theorem coverp0010010111 : Covers (-1207761639/8000000 : ℚ) vp0010010111 := join_branches bp00100101110 bp00100101111
private noncomputable def vp0010010110111_0 : Blocks := edgeBlocks% "full/vectors/0010010110111-V-0000.bin"
noncomputable def vp0010010110111 : Blocks := vp0010010110111_0
theorem coverp0010010110111 : Covers (-1206761639/1000000 : ℚ) vp0010010110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010110110_0 : Blocks := edgeBlocks% "full/vectors/0010010110110-V-0000.bin"
noncomputable def vp0010010110110 : Blocks := vp0010010110110_0
theorem coverp0010010110110 : Covers (-1205761639/1000000 : ℚ) vp0010010110110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001011011_0 : Blocks := edgeBlocks% "full/vectors/001001011011-V-0000.bin"
noncomputable def vp001001011011 : Blocks := vp001001011011_0
private theorem bp0010010110110 : Branch 0 (-1205761639/2000000 : ℚ) vp001001011011 := by
  apply branch_left_normalized (c:=vp0010010110110) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1205761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1205761639/1000000 : ℚ) by norm_num]
  exact coverp0010010110110
private noncomputable def ep0010010110111_0 : Blocks := edgeBlocks% "full/vectors/0010010110111-E-0000.bin"
noncomputable def ep0010010110111 : Blocks := ep0010010110111_0
private theorem idp0010010110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001011011.list =
    C ((2:ℤ)^84) * horner X vp0010010110111.list + horner X ep0010010110111.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010110111 : Branch 1 (-1205761639/2000000 : ℚ) vp001001011011 := by
  apply branch_checked idp0010010110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1205761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1206761639/1000000 : ℚ) by norm_num]
  exact coverp0010010110111
theorem coverp001001011011 : Covers (-1205761639/2000000 : ℚ) vp001001011011 := join_branches bp0010010110110 bp0010010110111
private noncomputable def vp0010010110101_0 : Blocks := edgeBlocks% "full/vectors/0010010110101-V-0000.bin"
noncomputable def vp0010010110101 : Blocks := vp0010010110101_0
theorem coverp0010010110101 : Covers (-1204761639/1000000 : ℚ) vp0010010110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010110100_0 : Blocks := edgeBlocks% "full/vectors/0010010110100-V-0000.bin"
noncomputable def vp0010010110100 : Blocks := vp0010010110100_0
theorem coverp0010010110100 : Covers (-1203761639/1000000 : ℚ) vp0010010110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001011010_0 : Blocks := edgeBlocks% "full/vectors/001001011010-V-0000.bin"
noncomputable def vp001001011010 : Blocks := vp001001011010_0
private theorem bp0010010110100 : Branch 0 (-1203761639/2000000 : ℚ) vp001001011010 := by
  apply branch_left_normalized (c:=vp0010010110100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1203761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1203761639/1000000 : ℚ) by norm_num]
  exact coverp0010010110100
private noncomputable def ep0010010110101_0 : Blocks := edgeBlocks% "full/vectors/0010010110101-E-0000.bin"
noncomputable def ep0010010110101 : Blocks := ep0010010110101_0
private theorem idp0010010110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001011010.list =
    C ((2:ℤ)^84) * horner X vp0010010110101.list + horner X ep0010010110101.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010110101 : Branch 1 (-1203761639/2000000 : ℚ) vp001001011010 := by
  apply branch_checked idp0010010110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1203761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1204761639/1000000 : ℚ) by norm_num]
  exact coverp0010010110101
theorem coverp001001011010 : Covers (-1203761639/2000000 : ℚ) vp001001011010 := join_branches bp0010010110100 bp0010010110101
private noncomputable def vp00100101101_0 : Blocks := edgeBlocks% "full/vectors/00100101101-V-0000.bin"
private noncomputable def vp00100101101_1 : Blocks := edgeBlocks% "full/vectors/00100101101-V-0001.bin"
noncomputable def vp00100101101 : Blocks := (Blocks.join vp00100101101_0 vp00100101101_1)
private theorem bp001001011010 : Branch 0 (-1203761639/4000000 : ℚ) vp00100101101 := by
  apply branch_left_normalized (c:=vp001001011010) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1203761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1203761639/2000000 : ℚ) by norm_num]
  exact coverp001001011010
private noncomputable def ep001001011011_0 : Blocks := edgeBlocks% "full/vectors/001001011011-E-0000.bin"
private noncomputable def ep001001011011_1 : Blocks := edgeBlocks% "full/vectors/001001011011-E-0001.bin"
noncomputable def ep001001011011 : Blocks := (Blocks.join ep001001011011_0 ep001001011011_1)
private theorem idp001001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100101101.list =
    C ((2:ℤ)^147) * horner X vp001001011011.list + horner X ep001001011011.list := by
  exact edge_identity (B := (2:ℤ)^298) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001011011 : Branch 1 (-1203761639/4000000 : ℚ) vp00100101101 := by
  apply branch_checked idp001001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1203761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1205761639/2000000 : ℚ) by norm_num]
  exact coverp001001011011
theorem coverp00100101101 : Covers (-1203761639/4000000 : ℚ) vp00100101101 := join_branches bp001001011010 bp001001011011
private noncomputable def vp0010010110011_0 : Blocks := edgeBlocks% "full/vectors/0010010110011-V-0000.bin"
noncomputable def vp0010010110011 : Blocks := vp0010010110011_0
theorem coverp0010010110011 : Covers (-1202761639/1000000 : ℚ) vp0010010110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010110010_0 : Blocks := edgeBlocks% "full/vectors/0010010110010-V-0000.bin"
noncomputable def vp0010010110010 : Blocks := vp0010010110010_0
theorem coverp0010010110010 : Covers (-1201761639/1000000 : ℚ) vp0010010110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001011001_0 : Blocks := edgeBlocks% "full/vectors/001001011001-V-0000.bin"
noncomputable def vp001001011001 : Blocks := vp001001011001_0
private theorem bp0010010110010 : Branch 0 (-1201761639/2000000 : ℚ) vp001001011001 := by
  apply branch_left_normalized (c:=vp0010010110010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1201761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1201761639/1000000 : ℚ) by norm_num]
  exact coverp0010010110010
private noncomputable def ep0010010110011_0 : Blocks := edgeBlocks% "full/vectors/0010010110011-E-0000.bin"
noncomputable def ep0010010110011 : Blocks := ep0010010110011_0
private theorem idp0010010110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001011001.list =
    C ((2:ℤ)^82) * horner X vp0010010110011.list + horner X ep0010010110011.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010110011 : Branch 1 (-1201761639/2000000 : ℚ) vp001001011001 := by
  apply branch_checked idp0010010110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1201761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1202761639/1000000 : ℚ) by norm_num]
  exact coverp0010010110011
theorem coverp001001011001 : Covers (-1201761639/2000000 : ℚ) vp001001011001 := join_branches bp0010010110010 bp0010010110011
private noncomputable def vp0010010110001_0 : Blocks := edgeBlocks% "full/vectors/0010010110001-V-0000.bin"
noncomputable def vp0010010110001 : Blocks := vp0010010110001_0
theorem coverp0010010110001 : Covers (-1200761639/1000000 : ℚ) vp0010010110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010110000_0 : Blocks := edgeBlocks% "full/vectors/0010010110000-V-0000.bin"
noncomputable def vp0010010110000 : Blocks := vp0010010110000_0
theorem coverp0010010110000 : Covers (-1199761639/1000000 : ℚ) vp0010010110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001011000_0 : Blocks := edgeBlocks% "full/vectors/001001011000-V-0000.bin"
noncomputable def vp001001011000 : Blocks := vp001001011000_0
private theorem bp0010010110000 : Branch 0 (-1199761639/2000000 : ℚ) vp001001011000 := by
  apply branch_left_normalized (c:=vp0010010110000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1199761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1199761639/1000000 : ℚ) by norm_num]
  exact coverp0010010110000
private noncomputable def ep0010010110001_0 : Blocks := edgeBlocks% "full/vectors/0010010110001-E-0000.bin"
noncomputable def ep0010010110001 : Blocks := ep0010010110001_0
private theorem idp0010010110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001011000.list =
    C ((2:ℤ)^84) * horner X vp0010010110001.list + horner X ep0010010110001.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010110001 : Branch 1 (-1199761639/2000000 : ℚ) vp001001011000 := by
  apply branch_checked idp0010010110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1199761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1200761639/1000000 : ℚ) by norm_num]
  exact coverp0010010110001
theorem coverp001001011000 : Covers (-1199761639/2000000 : ℚ) vp001001011000 := join_branches bp0010010110000 bp0010010110001
private noncomputable def vp00100101100_0 : Blocks := edgeBlocks% "full/vectors/00100101100-V-0000.bin"
private noncomputable def vp00100101100_1 : Blocks := edgeBlocks% "full/vectors/00100101100-V-0001.bin"
noncomputable def vp00100101100 : Blocks := (Blocks.join vp00100101100_0 vp00100101100_1)
private theorem bp001001011000 : Branch 0 (-1199761639/4000000 : ℚ) vp00100101100 := by
  apply branch_left_normalized (c:=vp001001011000) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1199761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1199761639/2000000 : ℚ) by norm_num]
  exact coverp001001011000
private noncomputable def ep001001011001_0 : Blocks := edgeBlocks% "full/vectors/001001011001-E-0000.bin"
private noncomputable def ep001001011001_1 : Blocks := edgeBlocks% "full/vectors/001001011001-E-0001.bin"
noncomputable def ep001001011001 : Blocks := (Blocks.join ep001001011001_0 ep001001011001_1)
private theorem idp001001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100101100.list =
    C ((2:ℤ)^148) * horner X vp001001011001.list + horner X ep001001011001.list := by
  exact edge_identity (B := (2:ℤ)^298) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001011001 : Branch 1 (-1199761639/4000000 : ℚ) vp00100101100 := by
  apply branch_checked idp001001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1199761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1201761639/2000000 : ℚ) by norm_num]
  exact coverp001001011001
theorem coverp00100101100 : Covers (-1199761639/4000000 : ℚ) vp00100101100 := join_branches bp001001011000 bp001001011001
private noncomputable def vp0010010110_0 : Blocks := edgeBlocks% "full/vectors/0010010110-V-0000.bin"
private noncomputable def vp0010010110_1 : Blocks := edgeBlocks% "full/vectors/0010010110-V-0001.bin"
noncomputable def vp0010010110 : Blocks := (Blocks.join vp0010010110_0 vp0010010110_1)
private theorem bp00100101100 : Branch 0 (-1199761639/8000000 : ℚ) vp0010010110 := by
  apply branch_left_normalized (c:=vp00100101100) (k:=0) (m:=135) (by decide +kernel)
  rw [show 2*(-1199761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1199761639/4000000 : ℚ) by norm_num]
  exact coverp00100101100
private noncomputable def ep00100101101_0 : Blocks := edgeBlocks% "full/vectors/00100101101-E-0000.bin"
private noncomputable def ep00100101101_1 : Blocks := edgeBlocks% "full/vectors/00100101101-E-0001.bin"
noncomputable def ep00100101101 : Blocks := (Blocks.join ep00100101101_0 ep00100101101_1)
private theorem idp00100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010010110.list =
    C ((2:ℤ)^273) * horner X vp00100101101.list + horner X ep00100101101.list := by
  exact edge_identity (B := (2:ℤ)^472) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100101101 : Branch 1 (-1199761639/8000000 : ℚ) vp0010010110 := by
  apply branch_checked idp00100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1199761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1203761639/4000000 : ℚ) by norm_num]
  exact coverp00100101101
theorem coverp0010010110 : Covers (-1199761639/8000000 : ℚ) vp0010010110 := join_branches bp00100101100 bp00100101101
private noncomputable def vp001001011_0 : Blocks := edgeBlocks% "full/vectors/001001011-V-0000.bin"
private noncomputable def vp001001011_1 : Blocks := edgeBlocks% "full/vectors/001001011-V-0001.bin"
private noncomputable def vp001001011_2 : Blocks := edgeBlocks% "full/vectors/001001011-V-0002.bin"
private noncomputable def vp001001011_3 : Blocks := edgeBlocks% "full/vectors/001001011-V-0003.bin"
noncomputable def vp001001011 : Blocks := (Blocks.join (Blocks.join vp001001011_0 vp001001011_1) (Blocks.join vp001001011_2 vp001001011_3))
private theorem bp0010010110 : Branch 0 (-1199761639/16000000 : ℚ) vp001001011 := by
  apply branch_left_normalized (c:=vp0010010110) (k:=0) (m:=249) (by decide +kernel)
  rw [show 2*(-1199761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1199761639/8000000 : ℚ) by norm_num]
  exact coverp0010010110
private noncomputable def ep0010010111_0 : Blocks := edgeBlocks% "full/vectors/0010010111-E-0000.bin"
private noncomputable def ep0010010111_1 : Blocks := edgeBlocks% "full/vectors/0010010111-E-0001.bin"
private noncomputable def ep0010010111_2 : Blocks := edgeBlocks% "full/vectors/0010010111-E-0002.bin"
private noncomputable def ep0010010111_3 : Blocks := edgeBlocks% "full/vectors/0010010111-E-0003.bin"
noncomputable def ep0010010111 : Blocks := (Blocks.join (Blocks.join ep0010010111_0 ep0010010111_1) (Blocks.join ep0010010111_2 ep0010010111_3))
private theorem idp0010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001011.list =
    C ((2:ℤ)^521) * horner X vp0010010111.list + horner X ep0010010111.list := by
  exact edge_identity (B := (2:ℤ)^817) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010111 : Branch 1 (-1199761639/16000000 : ℚ) vp001001011 := by
  apply branch_checked idp0010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1199761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1207761639/8000000 : ℚ) by norm_num]
  exact coverp0010010111
theorem coverp001001011 : Covers (-1199761639/16000000 : ℚ) vp001001011 := join_branches bp0010010110 bp0010010111
private noncomputable def vp0010010101111_0 : Blocks := edgeBlocks% "full/vectors/0010010101111-V-0000.bin"
noncomputable def vp0010010101111 : Blocks := vp0010010101111_0
theorem coverp0010010101111 : Covers (-1198761639/1000000 : ℚ) vp0010010101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010101110_0 : Blocks := edgeBlocks% "full/vectors/0010010101110-V-0000.bin"
noncomputable def vp0010010101110 : Blocks := vp0010010101110_0
theorem coverp0010010101110 : Covers (-1197761639/1000000 : ℚ) vp0010010101110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001010111_0 : Blocks := edgeBlocks% "full/vectors/001001010111-V-0000.bin"
noncomputable def vp001001010111 : Blocks := vp001001010111_0
private theorem bp0010010101110 : Branch 0 (-1197761639/2000000 : ℚ) vp001001010111 := by
  apply branch_left_normalized (c:=vp0010010101110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1197761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1197761639/1000000 : ℚ) by norm_num]
  exact coverp0010010101110
private noncomputable def ep0010010101111_0 : Blocks := edgeBlocks% "full/vectors/0010010101111-E-0000.bin"
noncomputable def ep0010010101111 : Blocks := ep0010010101111_0
private theorem idp0010010101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001010111.list =
    C ((2:ℤ)^84) * horner X vp0010010101111.list + horner X ep0010010101111.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010101111 : Branch 1 (-1197761639/2000000 : ℚ) vp001001010111 := by
  apply branch_checked idp0010010101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1197761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1198761639/1000000 : ℚ) by norm_num]
  exact coverp0010010101111
theorem coverp001001010111 : Covers (-1197761639/2000000 : ℚ) vp001001010111 := join_branches bp0010010101110 bp0010010101111
private noncomputable def vp0010010101101_0 : Blocks := edgeBlocks% "full/vectors/0010010101101-V-0000.bin"
noncomputable def vp0010010101101 : Blocks := vp0010010101101_0
theorem coverp0010010101101 : Covers (-1196761639/1000000 : ℚ) vp0010010101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010101100_0 : Blocks := edgeBlocks% "full/vectors/0010010101100-V-0000.bin"
noncomputable def vp0010010101100 : Blocks := vp0010010101100_0
theorem coverp0010010101100 : Covers (-1195761639/1000000 : ℚ) vp0010010101100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001010110_0 : Blocks := edgeBlocks% "full/vectors/001001010110-V-0000.bin"
noncomputable def vp001001010110 : Blocks := vp001001010110_0
private theorem bp0010010101100 : Branch 0 (-1195761639/2000000 : ℚ) vp001001010110 := by
  apply branch_left_normalized (c:=vp0010010101100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1195761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1195761639/1000000 : ℚ) by norm_num]
  exact coverp0010010101100
private noncomputable def ep0010010101101_0 : Blocks := edgeBlocks% "full/vectors/0010010101101-E-0000.bin"
noncomputable def ep0010010101101 : Blocks := ep0010010101101_0
private theorem idp0010010101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001010110.list =
    C ((2:ℤ)^83) * horner X vp0010010101101.list + horner X ep0010010101101.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010101101 : Branch 1 (-1195761639/2000000 : ℚ) vp001001010110 := by
  apply branch_checked idp0010010101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1195761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1196761639/1000000 : ℚ) by norm_num]
  exact coverp0010010101101
theorem coverp001001010110 : Covers (-1195761639/2000000 : ℚ) vp001001010110 := join_branches bp0010010101100 bp0010010101101
private noncomputable def vp00100101011_0 : Blocks := edgeBlocks% "full/vectors/00100101011-V-0000.bin"
private noncomputable def vp00100101011_1 : Blocks := edgeBlocks% "full/vectors/00100101011-V-0001.bin"
noncomputable def vp00100101011 : Blocks := (Blocks.join vp00100101011_0 vp00100101011_1)
private theorem bp001001010110 : Branch 0 (-1195761639/4000000 : ℚ) vp00100101011 := by
  apply branch_left_normalized (c:=vp001001010110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1195761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1195761639/2000000 : ℚ) by norm_num]
  exact coverp001001010110
private noncomputable def ep001001010111_0 : Blocks := edgeBlocks% "full/vectors/001001010111-E-0000.bin"
private noncomputable def ep001001010111_1 : Blocks := edgeBlocks% "full/vectors/001001010111-E-0001.bin"
noncomputable def ep001001010111 : Blocks := (Blocks.join ep001001010111_0 ep001001010111_1)
private theorem idp001001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100101011.list =
    C ((2:ℤ)^147) * horner X vp001001010111.list + horner X ep001001010111.list := by
  exact edge_identity (B := (2:ℤ)^298) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001010111 : Branch 1 (-1195761639/4000000 : ℚ) vp00100101011 := by
  apply branch_checked idp001001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1195761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1197761639/2000000 : ℚ) by norm_num]
  exact coverp001001010111
theorem coverp00100101011 : Covers (-1195761639/4000000 : ℚ) vp00100101011 := join_branches bp001001010110 bp001001010111
private noncomputable def vp0010010101011_0 : Blocks := edgeBlocks% "full/vectors/0010010101011-V-0000.bin"
noncomputable def vp0010010101011 : Blocks := vp0010010101011_0
theorem coverp0010010101011 : Covers (-1194761639/1000000 : ℚ) vp0010010101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010101010_0 : Blocks := edgeBlocks% "full/vectors/0010010101010-V-0000.bin"
noncomputable def vp0010010101010 : Blocks := vp0010010101010_0
theorem coverp0010010101010 : Covers (-1193761639/1000000 : ℚ) vp0010010101010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001010101_0 : Blocks := edgeBlocks% "full/vectors/001001010101-V-0000.bin"
noncomputable def vp001001010101 : Blocks := vp001001010101_0
private theorem bp0010010101010 : Branch 0 (-1193761639/2000000 : ℚ) vp001001010101 := by
  apply branch_left_normalized (c:=vp0010010101010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1193761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1193761639/1000000 : ℚ) by norm_num]
  exact coverp0010010101010
private noncomputable def ep0010010101011_0 : Blocks := edgeBlocks% "full/vectors/0010010101011-E-0000.bin"
noncomputable def ep0010010101011 : Blocks := ep0010010101011_0
private theorem idp0010010101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001010101.list =
    C ((2:ℤ)^84) * horner X vp0010010101011.list + horner X ep0010010101011.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010101011 : Branch 1 (-1193761639/2000000 : ℚ) vp001001010101 := by
  apply branch_checked idp0010010101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1193761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1194761639/1000000 : ℚ) by norm_num]
  exact coverp0010010101011
theorem coverp001001010101 : Covers (-1193761639/2000000 : ℚ) vp001001010101 := join_branches bp0010010101010 bp0010010101011
private noncomputable def vp0010010101001_0 : Blocks := edgeBlocks% "full/vectors/0010010101001-V-0000.bin"
noncomputable def vp0010010101001 : Blocks := vp0010010101001_0
theorem coverp0010010101001 : Covers (-1192761639/1000000 : ℚ) vp0010010101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010101000_0 : Blocks := edgeBlocks% "full/vectors/0010010101000-V-0000.bin"
noncomputable def vp0010010101000 : Blocks := vp0010010101000_0
theorem coverp0010010101000 : Covers (-1191761639/1000000 : ℚ) vp0010010101000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001010100_0 : Blocks := edgeBlocks% "full/vectors/001001010100-V-0000.bin"
noncomputable def vp001001010100 : Blocks := vp001001010100_0
private theorem bp0010010101000 : Branch 0 (-1191761639/2000000 : ℚ) vp001001010100 := by
  apply branch_left_normalized (c:=vp0010010101000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1191761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1191761639/1000000 : ℚ) by norm_num]
  exact coverp0010010101000
private noncomputable def ep0010010101001_0 : Blocks := edgeBlocks% "full/vectors/0010010101001-E-0000.bin"
noncomputable def ep0010010101001 : Blocks := ep0010010101001_0
private theorem idp0010010101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001010100.list =
    C ((2:ℤ)^85) * horner X vp0010010101001.list + horner X ep0010010101001.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010101001 : Branch 1 (-1191761639/2000000 : ℚ) vp001001010100 := by
  apply branch_checked idp0010010101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1191761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1192761639/1000000 : ℚ) by norm_num]
  exact coverp0010010101001
theorem coverp001001010100 : Covers (-1191761639/2000000 : ℚ) vp001001010100 := join_branches bp0010010101000 bp0010010101001
private noncomputable def vp00100101010_0 : Blocks := edgeBlocks% "full/vectors/00100101010-V-0000.bin"
private noncomputable def vp00100101010_1 : Blocks := edgeBlocks% "full/vectors/00100101010-V-0001.bin"
noncomputable def vp00100101010 : Blocks := (Blocks.join vp00100101010_0 vp00100101010_1)
private theorem bp001001010100 : Branch 0 (-1191761639/4000000 : ℚ) vp00100101010 := by
  apply branch_left_normalized (c:=vp001001010100) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-1191761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1191761639/2000000 : ℚ) by norm_num]
  exact coverp001001010100
private noncomputable def ep001001010101_0 : Blocks := edgeBlocks% "full/vectors/001001010101-E-0000.bin"
private noncomputable def ep001001010101_1 : Blocks := edgeBlocks% "full/vectors/001001010101-E-0001.bin"
noncomputable def ep001001010101 : Blocks := (Blocks.join ep001001010101_0 ep001001010101_1)
private theorem idp001001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100101010.list =
    C ((2:ℤ)^148) * horner X vp001001010101.list + horner X ep001001010101.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001010101 : Branch 1 (-1191761639/4000000 : ℚ) vp00100101010 := by
  apply branch_checked idp001001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1191761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1193761639/2000000 : ℚ) by norm_num]
  exact coverp001001010101
theorem coverp00100101010 : Covers (-1191761639/4000000 : ℚ) vp00100101010 := join_branches bp001001010100 bp001001010101
private noncomputable def vp0010010101_0 : Blocks := edgeBlocks% "full/vectors/0010010101-V-0000.bin"
private noncomputable def vp0010010101_1 : Blocks := edgeBlocks% "full/vectors/0010010101-V-0001.bin"
noncomputable def vp0010010101 : Blocks := (Blocks.join vp0010010101_0 vp0010010101_1)
private theorem bp00100101010 : Branch 0 (-1191761639/8000000 : ℚ) vp0010010101 := by
  apply branch_left_normalized (c:=vp00100101010) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-1191761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1191761639/4000000 : ℚ) by norm_num]
  exact coverp00100101010
private noncomputable def ep00100101011_0 : Blocks := edgeBlocks% "full/vectors/00100101011-E-0000.bin"
private noncomputable def ep00100101011_1 : Blocks := edgeBlocks% "full/vectors/00100101011-E-0001.bin"
noncomputable def ep00100101011 : Blocks := (Blocks.join ep00100101011_0 ep00100101011_1)
private theorem idp00100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010010101.list =
    C ((2:ℤ)^274) * horner X vp00100101011.list + horner X ep00100101011.list := by
  exact edge_identity (B := (2:ℤ)^473) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100101011 : Branch 1 (-1191761639/8000000 : ℚ) vp0010010101 := by
  apply branch_checked idp00100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1191761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1195761639/4000000 : ℚ) by norm_num]
  exact coverp00100101011
theorem coverp0010010101 : Covers (-1191761639/8000000 : ℚ) vp0010010101 := join_branches bp00100101010 bp00100101011
private noncomputable def vp0010010100111_0 : Blocks := edgeBlocks% "full/vectors/0010010100111-V-0000.bin"
noncomputable def vp0010010100111 : Blocks := vp0010010100111_0
theorem coverp0010010100111 : Covers (-1190761639/1000000 : ℚ) vp0010010100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010100110_0 : Blocks := edgeBlocks% "full/vectors/0010010100110-V-0000.bin"
noncomputable def vp0010010100110 : Blocks := vp0010010100110_0
theorem coverp0010010100110 : Covers (-1189761639/1000000 : ℚ) vp0010010100110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001010011_0 : Blocks := edgeBlocks% "full/vectors/001001010011-V-0000.bin"
noncomputable def vp001001010011 : Blocks := vp001001010011_0
private theorem bp0010010100110 : Branch 0 (-1189761639/2000000 : ℚ) vp001001010011 := by
  apply branch_left_normalized (c:=vp0010010100110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1189761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1189761639/1000000 : ℚ) by norm_num]
  exact coverp0010010100110
private noncomputable def ep0010010100111_0 : Blocks := edgeBlocks% "full/vectors/0010010100111-E-0000.bin"
noncomputable def ep0010010100111 : Blocks := ep0010010100111_0
private theorem idp0010010100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001010011.list =
    C ((2:ℤ)^85) * horner X vp0010010100111.list + horner X ep0010010100111.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010100111 : Branch 1 (-1189761639/2000000 : ℚ) vp001001010011 := by
  apply branch_checked idp0010010100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1189761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1190761639/1000000 : ℚ) by norm_num]
  exact coverp0010010100111
theorem coverp001001010011 : Covers (-1189761639/2000000 : ℚ) vp001001010011 := join_branches bp0010010100110 bp0010010100111
private noncomputable def vp0010010100101_0 : Blocks := edgeBlocks% "full/vectors/0010010100101-V-0000.bin"
noncomputable def vp0010010100101 : Blocks := vp0010010100101_0
theorem coverp0010010100101 : Covers (-1188761639/1000000 : ℚ) vp0010010100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010100100_0 : Blocks := edgeBlocks% "full/vectors/0010010100100-V-0000.bin"
noncomputable def vp0010010100100 : Blocks := vp0010010100100_0
theorem coverp0010010100100 : Covers (-1187761639/1000000 : ℚ) vp0010010100100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001010010_0 : Blocks := edgeBlocks% "full/vectors/001001010010-V-0000.bin"
noncomputable def vp001001010010 : Blocks := vp001001010010_0
private theorem bp0010010100100 : Branch 0 (-1187761639/2000000 : ℚ) vp001001010010 := by
  apply branch_left_normalized (c:=vp0010010100100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1187761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1187761639/1000000 : ℚ) by norm_num]
  exact coverp0010010100100
private noncomputable def ep0010010100101_0 : Blocks := edgeBlocks% "full/vectors/0010010100101-E-0000.bin"
noncomputable def ep0010010100101 : Blocks := ep0010010100101_0
private theorem idp0010010100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001010010.list =
    C ((2:ℤ)^84) * horner X vp0010010100101.list + horner X ep0010010100101.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010100101 : Branch 1 (-1187761639/2000000 : ℚ) vp001001010010 := by
  apply branch_checked idp0010010100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1187761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1188761639/1000000 : ℚ) by norm_num]
  exact coverp0010010100101
theorem coverp001001010010 : Covers (-1187761639/2000000 : ℚ) vp001001010010 := join_branches bp0010010100100 bp0010010100101
private noncomputable def vp00100101001_0 : Blocks := edgeBlocks% "full/vectors/00100101001-V-0000.bin"
private noncomputable def vp00100101001_1 : Blocks := edgeBlocks% "full/vectors/00100101001-V-0001.bin"
noncomputable def vp00100101001 : Blocks := (Blocks.join vp00100101001_0 vp00100101001_1)
private theorem bp001001010010 : Branch 0 (-1187761639/4000000 : ℚ) vp00100101001 := by
  apply branch_left_normalized (c:=vp001001010010) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-1187761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1187761639/2000000 : ℚ) by norm_num]
  exact coverp001001010010
private noncomputable def ep001001010011_0 : Blocks := edgeBlocks% "full/vectors/001001010011-E-0000.bin"
private noncomputable def ep001001010011_1 : Blocks := edgeBlocks% "full/vectors/001001010011-E-0001.bin"
noncomputable def ep001001010011 : Blocks := (Blocks.join ep001001010011_0 ep001001010011_1)
private theorem idp001001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100101001.list =
    C ((2:ℤ)^148) * horner X vp001001010011.list + horner X ep001001010011.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001010011 : Branch 1 (-1187761639/4000000 : ℚ) vp00100101001 := by
  apply branch_checked idp001001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1187761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1189761639/2000000 : ℚ) by norm_num]
  exact coverp001001010011
theorem coverp00100101001 : Covers (-1187761639/4000000 : ℚ) vp00100101001 := join_branches bp001001010010 bp001001010011
private noncomputable def vp0010010100011_0 : Blocks := edgeBlocks% "full/vectors/0010010100011-V-0000.bin"
noncomputable def vp0010010100011 : Blocks := vp0010010100011_0
theorem coverp0010010100011 : Covers (-1186761639/1000000 : ℚ) vp0010010100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010100010_0 : Blocks := edgeBlocks% "full/vectors/0010010100010-V-0000.bin"
noncomputable def vp0010010100010 : Blocks := vp0010010100010_0
theorem coverp0010010100010 : Covers (-1185761639/1000000 : ℚ) vp0010010100010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001010001_0 : Blocks := edgeBlocks% "full/vectors/001001010001-V-0000.bin"
noncomputable def vp001001010001 : Blocks := vp001001010001_0
private theorem bp0010010100010 : Branch 0 (-1185761639/2000000 : ℚ) vp001001010001 := by
  apply branch_left_normalized (c:=vp0010010100010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1185761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1185761639/1000000 : ℚ) by norm_num]
  exact coverp0010010100010
private noncomputable def ep0010010100011_0 : Blocks := edgeBlocks% "full/vectors/0010010100011-E-0000.bin"
noncomputable def ep0010010100011 : Blocks := ep0010010100011_0
private theorem idp0010010100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001010001.list =
    C ((2:ℤ)^84) * horner X vp0010010100011.list + horner X ep0010010100011.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010100011 : Branch 1 (-1185761639/2000000 : ℚ) vp001001010001 := by
  apply branch_checked idp0010010100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1185761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1186761639/1000000 : ℚ) by norm_num]
  exact coverp0010010100011
theorem coverp001001010001 : Covers (-1185761639/2000000 : ℚ) vp001001010001 := join_branches bp0010010100010 bp0010010100011
private noncomputable def vp0010010100001_0 : Blocks := edgeBlocks% "full/vectors/0010010100001-V-0000.bin"
noncomputable def vp0010010100001 : Blocks := vp0010010100001_0
theorem coverp0010010100001 : Covers (-1184761639/1000000 : ℚ) vp0010010100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010100000_0 : Blocks := edgeBlocks% "full/vectors/0010010100000-V-0000.bin"
noncomputable def vp0010010100000 : Blocks := vp0010010100000_0
theorem coverp0010010100000 : Covers (-1183761639/1000000 : ℚ) vp0010010100000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001010000_0 : Blocks := edgeBlocks% "full/vectors/001001010000-V-0000.bin"
noncomputable def vp001001010000 : Blocks := vp001001010000_0
private theorem bp0010010100000 : Branch 0 (-1183761639/2000000 : ℚ) vp001001010000 := by
  apply branch_left_normalized (c:=vp0010010100000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1183761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1183761639/1000000 : ℚ) by norm_num]
  exact coverp0010010100000
private noncomputable def ep0010010100001_0 : Blocks := edgeBlocks% "full/vectors/0010010100001-E-0000.bin"
noncomputable def ep0010010100001 : Blocks := ep0010010100001_0
private theorem idp0010010100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001010000.list =
    C ((2:ℤ)^83) * horner X vp0010010100001.list + horner X ep0010010100001.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010100001 : Branch 1 (-1183761639/2000000 : ℚ) vp001001010000 := by
  apply branch_checked idp0010010100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1183761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1184761639/1000000 : ℚ) by norm_num]
  exact coverp0010010100001
theorem coverp001001010000 : Covers (-1183761639/2000000 : ℚ) vp001001010000 := join_branches bp0010010100000 bp0010010100001
private noncomputable def vp00100101000_0 : Blocks := edgeBlocks% "full/vectors/00100101000-V-0000.bin"
private noncomputable def vp00100101000_1 : Blocks := edgeBlocks% "full/vectors/00100101000-V-0001.bin"
noncomputable def vp00100101000 : Blocks := (Blocks.join vp00100101000_0 vp00100101000_1)
private theorem bp001001010000 : Branch 0 (-1183761639/4000000 : ℚ) vp00100101000 := by
  apply branch_left_normalized (c:=vp001001010000) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1183761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1183761639/2000000 : ℚ) by norm_num]
  exact coverp001001010000
private noncomputable def ep001001010001_0 : Blocks := edgeBlocks% "full/vectors/001001010001-E-0000.bin"
private noncomputable def ep001001010001_1 : Blocks := edgeBlocks% "full/vectors/001001010001-E-0001.bin"
noncomputable def ep001001010001 : Blocks := (Blocks.join ep001001010001_0 ep001001010001_1)
private theorem idp001001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100101000.list =
    C ((2:ℤ)^148) * horner X vp001001010001.list + horner X ep001001010001.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001010001 : Branch 1 (-1183761639/4000000 : ℚ) vp00100101000 := by
  apply branch_checked idp001001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1183761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1185761639/2000000 : ℚ) by norm_num]
  exact coverp001001010001
theorem coverp00100101000 : Covers (-1183761639/4000000 : ℚ) vp00100101000 := join_branches bp001001010000 bp001001010001
private noncomputable def vp0010010100_0 : Blocks := edgeBlocks% "full/vectors/0010010100-V-0000.bin"
private noncomputable def vp0010010100_1 : Blocks := edgeBlocks% "full/vectors/0010010100-V-0001.bin"
noncomputable def vp0010010100 : Blocks := (Blocks.join vp0010010100_0 vp0010010100_1)
private theorem bp00100101000 : Branch 0 (-1183761639/8000000 : ℚ) vp0010010100 := by
  apply branch_left_normalized (c:=vp00100101000) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-1183761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1183761639/4000000 : ℚ) by norm_num]
  exact coverp00100101000
private noncomputable def ep00100101001_0 : Blocks := edgeBlocks% "full/vectors/00100101001-E-0000.bin"
private noncomputable def ep00100101001_1 : Blocks := edgeBlocks% "full/vectors/00100101001-E-0001.bin"
noncomputable def ep00100101001 : Blocks := (Blocks.join ep00100101001_0 ep00100101001_1)
private theorem idp00100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010010100.list =
    C ((2:ℤ)^274) * horner X vp00100101001.list + horner X ep00100101001.list := by
  exact edge_identity (B := (2:ℤ)^473) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100101001 : Branch 1 (-1183761639/8000000 : ℚ) vp0010010100 := by
  apply branch_checked idp00100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1183761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1187761639/4000000 : ℚ) by norm_num]
  exact coverp00100101001
theorem coverp0010010100 : Covers (-1183761639/8000000 : ℚ) vp0010010100 := join_branches bp00100101000 bp00100101001
private noncomputable def vp001001010_0 : Blocks := edgeBlocks% "full/vectors/001001010-V-0000.bin"
private noncomputable def vp001001010_1 : Blocks := edgeBlocks% "full/vectors/001001010-V-0001.bin"
private noncomputable def vp001001010_2 : Blocks := edgeBlocks% "full/vectors/001001010-V-0002.bin"
private noncomputable def vp001001010_3 : Blocks := edgeBlocks% "full/vectors/001001010-V-0003.bin"
noncomputable def vp001001010 : Blocks := (Blocks.join (Blocks.join vp001001010_0 vp001001010_1) (Blocks.join vp001001010_2 vp001001010_3))
private theorem bp0010010100 : Branch 0 (-1183761639/16000000 : ℚ) vp001001010 := by
  apply branch_left_normalized (c:=vp0010010100) (k:=0) (m:=250) (by decide +kernel)
  rw [show 2*(-1183761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1183761639/8000000 : ℚ) by norm_num]
  exact coverp0010010100
private noncomputable def ep0010010101_0 : Blocks := edgeBlocks% "full/vectors/0010010101-E-0000.bin"
private noncomputable def ep0010010101_1 : Blocks := edgeBlocks% "full/vectors/0010010101-E-0001.bin"
private noncomputable def ep0010010101_2 : Blocks := edgeBlocks% "full/vectors/0010010101-E-0002.bin"
private noncomputable def ep0010010101_3 : Blocks := edgeBlocks% "full/vectors/0010010101-E-0003.bin"
noncomputable def ep0010010101 : Blocks := (Blocks.join (Blocks.join ep0010010101_0 ep0010010101_1) (Blocks.join ep0010010101_2 ep0010010101_3))
private theorem idp0010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001010.list =
    C ((2:ℤ)^523) * horner X vp0010010101.list + horner X ep0010010101.list := by
  exact edge_identity (B := (2:ℤ)^820) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010101 : Branch 1 (-1183761639/16000000 : ℚ) vp001001010 := by
  apply branch_checked idp0010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1183761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1191761639/8000000 : ℚ) by norm_num]
  exact coverp0010010101
theorem coverp001001010 : Covers (-1183761639/16000000 : ℚ) vp001001010 := join_branches bp0010010100 bp0010010101
private noncomputable def vp00100101_0 : Blocks := edgeBlocks% "full/vectors/00100101-V-0000.bin"
private noncomputable def vp00100101_1 : Blocks := edgeBlocks% "full/vectors/00100101-V-0001.bin"
private noncomputable def vp00100101_2 : Blocks := edgeBlocks% "full/vectors/00100101-V-0002.bin"
private noncomputable def vp00100101_3 : Blocks := edgeBlocks% "full/vectors/00100101-V-0003.bin"
private noncomputable def vp00100101_4 : Blocks := edgeBlocks% "full/vectors/00100101-V-0004.bin"
private noncomputable def vp00100101_5 : Blocks := edgeBlocks% "full/vectors/00100101-V-0005.bin"
private noncomputable def vp00100101_6 : Blocks := edgeBlocks% "full/vectors/00100101-V-0006.bin"
private noncomputable def vp00100101_7 : Blocks := edgeBlocks% "full/vectors/00100101-V-0007.bin"
noncomputable def vp00100101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00100101_0 vp00100101_1) (Blocks.join vp00100101_2 vp00100101_3)) (Blocks.join (Blocks.join vp00100101_4 vp00100101_5) (Blocks.join vp00100101_6 vp00100101_7)))
private theorem bp001001010 : Branch 0 (-1183761639/32000000 : ℚ) vp00100101 := by
  apply branch_left_normalized (c:=vp001001010) (k:=0) (m:=476) (by decide +kernel)
  rw [show 2*(-1183761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1183761639/16000000 : ℚ) by norm_num]
  exact coverp001001010
private noncomputable def ep001001011_0 : Blocks := edgeBlocks% "full/vectors/001001011-E-0000.bin"
private noncomputable def ep001001011_1 : Blocks := edgeBlocks% "full/vectors/001001011-E-0001.bin"
private noncomputable def ep001001011_2 : Blocks := edgeBlocks% "full/vectors/001001011-E-0002.bin"
private noncomputable def ep001001011_3 : Blocks := edgeBlocks% "full/vectors/001001011-E-0003.bin"
private noncomputable def ep001001011_4 : Blocks := edgeBlocks% "full/vectors/001001011-E-0004.bin"
private noncomputable def ep001001011_5 : Blocks := edgeBlocks% "full/vectors/001001011-E-0005.bin"
private noncomputable def ep001001011_6 : Blocks := edgeBlocks% "full/vectors/001001011-E-0006.bin"
private noncomputable def ep001001011_7 : Blocks := edgeBlocks% "full/vectors/001001011-E-0007.bin"
noncomputable def ep001001011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep001001011_0 ep001001011_1) (Blocks.join ep001001011_2 ep001001011_3)) (Blocks.join (Blocks.join ep001001011_4 ep001001011_5) (Blocks.join ep001001011_6 ep001001011_7)))
private theorem idp001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100101.list =
    C ((2:ℤ)^1018) * horner X vp001001011.list + horner X ep001001011.list := by
  exact edge_identity (B := (2:ℤ)^1510) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001011 : Branch 1 (-1183761639/32000000 : ℚ) vp00100101 := by
  apply branch_checked idp001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1183761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1199761639/16000000 : ℚ) by norm_num]
  exact coverp001001011
theorem coverp00100101 : Covers (-1183761639/32000000 : ℚ) vp00100101 := join_branches bp001001010 bp001001011
private noncomputable def vp0010010011111_0 : Blocks := edgeBlocks% "full/vectors/0010010011111-V-0000.bin"
noncomputable def vp0010010011111 : Blocks := vp0010010011111_0
theorem coverp0010010011111 : Covers (-1182761639/1000000 : ℚ) vp0010010011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010011110_0 : Blocks := edgeBlocks% "full/vectors/0010010011110-V-0000.bin"
noncomputable def vp0010010011110 : Blocks := vp0010010011110_0
theorem coverp0010010011110 : Covers (-1181761639/1000000 : ℚ) vp0010010011110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001001111_0 : Blocks := edgeBlocks% "full/vectors/001001001111-V-0000.bin"
noncomputable def vp001001001111 : Blocks := vp001001001111_0
private theorem bp0010010011110 : Branch 0 (-1181761639/2000000 : ℚ) vp001001001111 := by
  apply branch_left_normalized (c:=vp0010010011110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1181761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1181761639/1000000 : ℚ) by norm_num]
  exact coverp0010010011110
private noncomputable def ep0010010011111_0 : Blocks := edgeBlocks% "full/vectors/0010010011111-E-0000.bin"
noncomputable def ep0010010011111 : Blocks := ep0010010011111_0
private theorem idp0010010011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001001111.list =
    C ((2:ℤ)^85) * horner X vp0010010011111.list + horner X ep0010010011111.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010011111 : Branch 1 (-1181761639/2000000 : ℚ) vp001001001111 := by
  apply branch_checked idp0010010011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1181761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1182761639/1000000 : ℚ) by norm_num]
  exact coverp0010010011111
theorem coverp001001001111 : Covers (-1181761639/2000000 : ℚ) vp001001001111 := join_branches bp0010010011110 bp0010010011111
private noncomputable def vp0010010011101_0 : Blocks := edgeBlocks% "full/vectors/0010010011101-V-0000.bin"
noncomputable def vp0010010011101 : Blocks := vp0010010011101_0
theorem coverp0010010011101 : Covers (-1180761639/1000000 : ℚ) vp0010010011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010011100_0 : Blocks := edgeBlocks% "full/vectors/0010010011100-V-0000.bin"
noncomputable def vp0010010011100 : Blocks := vp0010010011100_0
theorem coverp0010010011100 : Covers (-1179761639/1000000 : ℚ) vp0010010011100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001001110_0 : Blocks := edgeBlocks% "full/vectors/001001001110-V-0000.bin"
noncomputable def vp001001001110 : Blocks := vp001001001110_0
private theorem bp0010010011100 : Branch 0 (-1179761639/2000000 : ℚ) vp001001001110 := by
  apply branch_left_normalized (c:=vp0010010011100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1179761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1179761639/1000000 : ℚ) by norm_num]
  exact coverp0010010011100
private noncomputable def ep0010010011101_0 : Blocks := edgeBlocks% "full/vectors/0010010011101-E-0000.bin"
noncomputable def ep0010010011101 : Blocks := ep0010010011101_0
private theorem idp0010010011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001001110.list =
    C ((2:ℤ)^84) * horner X vp0010010011101.list + horner X ep0010010011101.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010011101 : Branch 1 (-1179761639/2000000 : ℚ) vp001001001110 := by
  apply branch_checked idp0010010011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1179761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1180761639/1000000 : ℚ) by norm_num]
  exact coverp0010010011101
theorem coverp001001001110 : Covers (-1179761639/2000000 : ℚ) vp001001001110 := join_branches bp0010010011100 bp0010010011101
private noncomputable def vp00100100111_0 : Blocks := edgeBlocks% "full/vectors/00100100111-V-0000.bin"
private noncomputable def vp00100100111_1 : Blocks := edgeBlocks% "full/vectors/00100100111-V-0001.bin"
noncomputable def vp00100100111 : Blocks := (Blocks.join vp00100100111_0 vp00100100111_1)
private theorem bp001001001110 : Branch 0 (-1179761639/4000000 : ℚ) vp00100100111 := by
  apply branch_left_normalized (c:=vp001001001110) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-1179761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1179761639/2000000 : ℚ) by norm_num]
  exact coverp001001001110
private noncomputable def ep001001001111_0 : Blocks := edgeBlocks% "full/vectors/001001001111-E-0000.bin"
private noncomputable def ep001001001111_1 : Blocks := edgeBlocks% "full/vectors/001001001111-E-0001.bin"
noncomputable def ep001001001111 : Blocks := (Blocks.join ep001001001111_0 ep001001001111_1)
private theorem idp001001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100100111.list =
    C ((2:ℤ)^148) * horner X vp001001001111.list + horner X ep001001001111.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001001111 : Branch 1 (-1179761639/4000000 : ℚ) vp00100100111 := by
  apply branch_checked idp001001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1179761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1181761639/2000000 : ℚ) by norm_num]
  exact coverp001001001111
theorem coverp00100100111 : Covers (-1179761639/4000000 : ℚ) vp00100100111 := join_branches bp001001001110 bp001001001111
private noncomputable def vp0010010011011_0 : Blocks := edgeBlocks% "full/vectors/0010010011011-V-0000.bin"
noncomputable def vp0010010011011 : Blocks := vp0010010011011_0
theorem coverp0010010011011 : Covers (-1178761639/1000000 : ℚ) vp0010010011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010011010_0 : Blocks := edgeBlocks% "full/vectors/0010010011010-V-0000.bin"
noncomputable def vp0010010011010 : Blocks := vp0010010011010_0
theorem coverp0010010011010 : Covers (-1177761639/1000000 : ℚ) vp0010010011010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001001101_0 : Blocks := edgeBlocks% "full/vectors/001001001101-V-0000.bin"
noncomputable def vp001001001101 : Blocks := vp001001001101_0
private theorem bp0010010011010 : Branch 0 (-1177761639/2000000 : ℚ) vp001001001101 := by
  apply branch_left_normalized (c:=vp0010010011010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1177761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1177761639/1000000 : ℚ) by norm_num]
  exact coverp0010010011010
private noncomputable def ep0010010011011_0 : Blocks := edgeBlocks% "full/vectors/0010010011011-E-0000.bin"
noncomputable def ep0010010011011 : Blocks := ep0010010011011_0
private theorem idp0010010011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001001101.list =
    C ((2:ℤ)^85) * horner X vp0010010011011.list + horner X ep0010010011011.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010011011 : Branch 1 (-1177761639/2000000 : ℚ) vp001001001101 := by
  apply branch_checked idp0010010011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1177761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1178761639/1000000 : ℚ) by norm_num]
  exact coverp0010010011011
theorem coverp001001001101 : Covers (-1177761639/2000000 : ℚ) vp001001001101 := join_branches bp0010010011010 bp0010010011011
private noncomputable def vp0010010011001_0 : Blocks := edgeBlocks% "full/vectors/0010010011001-V-0000.bin"
noncomputable def vp0010010011001 : Blocks := vp0010010011001_0
theorem coverp0010010011001 : Covers (-1176761639/1000000 : ℚ) vp0010010011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010011000_0 : Blocks := edgeBlocks% "full/vectors/0010010011000-V-0000.bin"
noncomputable def vp0010010011000 : Blocks := vp0010010011000_0
theorem coverp0010010011000 : Covers (-1175761639/1000000 : ℚ) vp0010010011000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001001100_0 : Blocks := edgeBlocks% "full/vectors/001001001100-V-0000.bin"
noncomputable def vp001001001100 : Blocks := vp001001001100_0
private theorem bp0010010011000 : Branch 0 (-1175761639/2000000 : ℚ) vp001001001100 := by
  apply branch_left_normalized (c:=vp0010010011000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1175761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1175761639/1000000 : ℚ) by norm_num]
  exact coverp0010010011000
private noncomputable def ep0010010011001_0 : Blocks := edgeBlocks% "full/vectors/0010010011001-E-0000.bin"
noncomputable def ep0010010011001 : Blocks := ep0010010011001_0
private theorem idp0010010011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001001100.list =
    C ((2:ℤ)^84) * horner X vp0010010011001.list + horner X ep0010010011001.list := by
  exact edge_identity (B := (2:ℤ)^210) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010011001 : Branch 1 (-1175761639/2000000 : ℚ) vp001001001100 := by
  apply branch_checked idp0010010011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1175761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1176761639/1000000 : ℚ) by norm_num]
  exact coverp0010010011001
theorem coverp001001001100 : Covers (-1175761639/2000000 : ℚ) vp001001001100 := join_branches bp0010010011000 bp0010010011001
private noncomputable def vp00100100110_0 : Blocks := edgeBlocks% "full/vectors/00100100110-V-0000.bin"
private noncomputable def vp00100100110_1 : Blocks := edgeBlocks% "full/vectors/00100100110-V-0001.bin"
noncomputable def vp00100100110 : Blocks := (Blocks.join vp00100100110_0 vp00100100110_1)
private theorem bp001001001100 : Branch 0 (-1175761639/4000000 : ℚ) vp00100100110 := by
  apply branch_left_normalized (c:=vp001001001100) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-1175761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1175761639/2000000 : ℚ) by norm_num]
  exact coverp001001001100
private noncomputable def ep001001001101_0 : Blocks := edgeBlocks% "full/vectors/001001001101-E-0000.bin"
private noncomputable def ep001001001101_1 : Blocks := edgeBlocks% "full/vectors/001001001101-E-0001.bin"
noncomputable def ep001001001101 : Blocks := (Blocks.join ep001001001101_0 ep001001001101_1)
private theorem idp001001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100100110.list =
    C ((2:ℤ)^148) * horner X vp001001001101.list + horner X ep001001001101.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001001101 : Branch 1 (-1175761639/4000000 : ℚ) vp00100100110 := by
  apply branch_checked idp001001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1175761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1177761639/2000000 : ℚ) by norm_num]
  exact coverp001001001101
theorem coverp00100100110 : Covers (-1175761639/4000000 : ℚ) vp00100100110 := join_branches bp001001001100 bp001001001101
private noncomputable def vp0010010011_0 : Blocks := edgeBlocks% "full/vectors/0010010011-V-0000.bin"
private noncomputable def vp0010010011_1 : Blocks := edgeBlocks% "full/vectors/0010010011-V-0001.bin"
noncomputable def vp0010010011 : Blocks := (Blocks.join vp0010010011_0 vp0010010011_1)
private theorem bp00100100110 : Branch 0 (-1175761639/8000000 : ℚ) vp0010010011 := by
  apply branch_left_normalized (c:=vp00100100110) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-1175761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1175761639/4000000 : ℚ) by norm_num]
  exact coverp00100100110
private noncomputable def ep00100100111_0 : Blocks := edgeBlocks% "full/vectors/00100100111-E-0000.bin"
private noncomputable def ep00100100111_1 : Blocks := edgeBlocks% "full/vectors/00100100111-E-0001.bin"
noncomputable def ep00100100111 : Blocks := (Blocks.join ep00100100111_0 ep00100100111_1)
private theorem idp00100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010010011.list =
    C ((2:ℤ)^275) * horner X vp00100100111.list + horner X ep00100100111.list := by
  exact edge_identity (B := (2:ℤ)^474) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100100111 : Branch 1 (-1175761639/8000000 : ℚ) vp0010010011 := by
  apply branch_checked idp00100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1175761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1179761639/4000000 : ℚ) by norm_num]
  exact coverp00100100111
theorem coverp0010010011 : Covers (-1175761639/8000000 : ℚ) vp0010010011 := join_branches bp00100100110 bp00100100111
private noncomputable def vp0010010010111_0 : Blocks := edgeBlocks% "full/vectors/0010010010111-V-0000.bin"
noncomputable def vp0010010010111 : Blocks := vp0010010010111_0
theorem coverp0010010010111 : Covers (-1174761639/1000000 : ℚ) vp0010010010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010010110_0 : Blocks := edgeBlocks% "full/vectors/0010010010110-V-0000.bin"
noncomputable def vp0010010010110 : Blocks := vp0010010010110_0
theorem coverp0010010010110 : Covers (-1173761639/1000000 : ℚ) vp0010010010110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001001011_0 : Blocks := edgeBlocks% "full/vectors/001001001011-V-0000.bin"
noncomputable def vp001001001011 : Blocks := vp001001001011_0
private theorem bp0010010010110 : Branch 0 (-1173761639/2000000 : ℚ) vp001001001011 := by
  apply branch_left_normalized (c:=vp0010010010110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1173761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1173761639/1000000 : ℚ) by norm_num]
  exact coverp0010010010110
private noncomputable def ep0010010010111_0 : Blocks := edgeBlocks% "full/vectors/0010010010111-E-0000.bin"
noncomputable def ep0010010010111 : Blocks := ep0010010010111_0
private theorem idp0010010010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001001011.list =
    C ((2:ℤ)^83) * horner X vp0010010010111.list + horner X ep0010010010111.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010010111 : Branch 1 (-1173761639/2000000 : ℚ) vp001001001011 := by
  apply branch_checked idp0010010010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1173761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1174761639/1000000 : ℚ) by norm_num]
  exact coverp0010010010111
theorem coverp001001001011 : Covers (-1173761639/2000000 : ℚ) vp001001001011 := join_branches bp0010010010110 bp0010010010111
private noncomputable def vp0010010010101_0 : Blocks := edgeBlocks% "full/vectors/0010010010101-V-0000.bin"
noncomputable def vp0010010010101 : Blocks := vp0010010010101_0
theorem coverp0010010010101 : Covers (-1172761639/1000000 : ℚ) vp0010010010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010010100_0 : Blocks := edgeBlocks% "full/vectors/0010010010100-V-0000.bin"
noncomputable def vp0010010010100 : Blocks := vp0010010010100_0
theorem coverp0010010010100 : Covers (-1171761639/1000000 : ℚ) vp0010010010100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001001010_0 : Blocks := edgeBlocks% "full/vectors/001001001010-V-0000.bin"
noncomputable def vp001001001010 : Blocks := vp001001001010_0
private theorem bp0010010010100 : Branch 0 (-1171761639/2000000 : ℚ) vp001001001010 := by
  apply branch_left_normalized (c:=vp0010010010100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1171761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1171761639/1000000 : ℚ) by norm_num]
  exact coverp0010010010100
private noncomputable def ep0010010010101_0 : Blocks := edgeBlocks% "full/vectors/0010010010101-E-0000.bin"
noncomputable def ep0010010010101 : Blocks := ep0010010010101_0
private theorem idp0010010010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001001010.list =
    C ((2:ℤ)^84) * horner X vp0010010010101.list + horner X ep0010010010101.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010010101 : Branch 1 (-1171761639/2000000 : ℚ) vp001001001010 := by
  apply branch_checked idp0010010010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1171761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1172761639/1000000 : ℚ) by norm_num]
  exact coverp0010010010101
theorem coverp001001001010 : Covers (-1171761639/2000000 : ℚ) vp001001001010 := join_branches bp0010010010100 bp0010010010101
private noncomputable def vp00100100101_0 : Blocks := edgeBlocks% "full/vectors/00100100101-V-0000.bin"
private noncomputable def vp00100100101_1 : Blocks := edgeBlocks% "full/vectors/00100100101-V-0001.bin"
noncomputable def vp00100100101 : Blocks := (Blocks.join vp00100100101_0 vp00100100101_1)
private theorem bp001001001010 : Branch 0 (-1171761639/4000000 : ℚ) vp00100100101 := by
  apply branch_left_normalized (c:=vp001001001010) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1171761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1171761639/2000000 : ℚ) by norm_num]
  exact coverp001001001010
private noncomputable def ep001001001011_0 : Blocks := edgeBlocks% "full/vectors/001001001011-E-0000.bin"
private noncomputable def ep001001001011_1 : Blocks := edgeBlocks% "full/vectors/001001001011-E-0001.bin"
noncomputable def ep001001001011 : Blocks := (Blocks.join ep001001001011_0 ep001001001011_1)
private theorem idp001001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100100101.list =
    C ((2:ℤ)^149) * horner X vp001001001011.list + horner X ep001001001011.list := by
  exact edge_identity (B := (2:ℤ)^299) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001001011 : Branch 1 (-1171761639/4000000 : ℚ) vp00100100101 := by
  apply branch_checked idp001001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1171761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1173761639/2000000 : ℚ) by norm_num]
  exact coverp001001001011
theorem coverp00100100101 : Covers (-1171761639/4000000 : ℚ) vp00100100101 := join_branches bp001001001010 bp001001001011
private noncomputable def vp0010010010011_0 : Blocks := edgeBlocks% "full/vectors/0010010010011-V-0000.bin"
noncomputable def vp0010010010011 : Blocks := vp0010010010011_0
theorem coverp0010010010011 : Covers (-1170761639/1000000 : ℚ) vp0010010010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010010010_0 : Blocks := edgeBlocks% "full/vectors/0010010010010-V-0000.bin"
noncomputable def vp0010010010010 : Blocks := vp0010010010010_0
theorem coverp0010010010010 : Covers (-1169761639/1000000 : ℚ) vp0010010010010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001001001_0 : Blocks := edgeBlocks% "full/vectors/001001001001-V-0000.bin"
noncomputable def vp001001001001 : Blocks := vp001001001001_0
private theorem bp0010010010010 : Branch 0 (-1169761639/2000000 : ℚ) vp001001001001 := by
  apply branch_left_normalized (c:=vp0010010010010) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1169761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1169761639/1000000 : ℚ) by norm_num]
  exact coverp0010010010010
private noncomputable def ep0010010010011_0 : Blocks := edgeBlocks% "full/vectors/0010010010011-E-0000.bin"
noncomputable def ep0010010010011 : Blocks := ep0010010010011_0
private theorem idp0010010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001001001.list =
    C ((2:ℤ)^86) * horner X vp0010010010011.list + horner X ep0010010010011.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010010011 : Branch 1 (-1169761639/2000000 : ℚ) vp001001001001 := by
  apply branch_checked idp0010010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1169761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1170761639/1000000 : ℚ) by norm_num]
  exact coverp0010010010011
theorem coverp001001001001 : Covers (-1169761639/2000000 : ℚ) vp001001001001 := join_branches bp0010010010010 bp0010010010011
private noncomputable def vp0010010010001_0 : Blocks := edgeBlocks% "full/vectors/0010010010001-V-0000.bin"
noncomputable def vp0010010010001 : Blocks := vp0010010010001_0
theorem coverp0010010010001 : Covers (-1168761639/1000000 : ℚ) vp0010010010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010010000_0 : Blocks := edgeBlocks% "full/vectors/0010010010000-V-0000.bin"
noncomputable def vp0010010010000 : Blocks := vp0010010010000_0
theorem coverp0010010010000 : Covers (-1167761639/1000000 : ℚ) vp0010010010000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001001000_0 : Blocks := edgeBlocks% "full/vectors/001001001000-V-0000.bin"
noncomputable def vp001001001000 : Blocks := vp001001001000_0
private theorem bp0010010010000 : Branch 0 (-1167761639/2000000 : ℚ) vp001001001000 := by
  apply branch_left_normalized (c:=vp0010010010000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1167761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1167761639/1000000 : ℚ) by norm_num]
  exact coverp0010010010000
private noncomputable def ep0010010010001_0 : Blocks := edgeBlocks% "full/vectors/0010010010001-E-0000.bin"
noncomputable def ep0010010010001 : Blocks := ep0010010010001_0
private theorem idp0010010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001001000.list =
    C ((2:ℤ)^85) * horner X vp0010010010001.list + horner X ep0010010010001.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010010001 : Branch 1 (-1167761639/2000000 : ℚ) vp001001001000 := by
  apply branch_checked idp0010010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1167761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1168761639/1000000 : ℚ) by norm_num]
  exact coverp0010010010001
theorem coverp001001001000 : Covers (-1167761639/2000000 : ℚ) vp001001001000 := join_branches bp0010010010000 bp0010010010001
private noncomputable def vp00100100100_0 : Blocks := edgeBlocks% "full/vectors/00100100100-V-0000.bin"
private noncomputable def vp00100100100_1 : Blocks := edgeBlocks% "full/vectors/00100100100-V-0001.bin"
noncomputable def vp00100100100 : Blocks := (Blocks.join vp00100100100_0 vp00100100100_1)
private theorem bp001001001000 : Branch 0 (-1167761639/4000000 : ℚ) vp00100100100 := by
  apply branch_left_normalized (c:=vp001001001000) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-1167761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1167761639/2000000 : ℚ) by norm_num]
  exact coverp001001001000
private noncomputable def ep001001001001_0 : Blocks := edgeBlocks% "full/vectors/001001001001-E-0000.bin"
private noncomputable def ep001001001001_1 : Blocks := edgeBlocks% "full/vectors/001001001001-E-0001.bin"
noncomputable def ep001001001001 : Blocks := (Blocks.join ep001001001001_0 ep001001001001_1)
private theorem idp001001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100100100.list =
    C ((2:ℤ)^150) * horner X vp001001001001.list + horner X ep001001001001.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001001001 : Branch 1 (-1167761639/4000000 : ℚ) vp00100100100 := by
  apply branch_checked idp001001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1167761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1169761639/2000000 : ℚ) by norm_num]
  exact coverp001001001001
theorem coverp00100100100 : Covers (-1167761639/4000000 : ℚ) vp00100100100 := join_branches bp001001001000 bp001001001001
private noncomputable def vp0010010010_0 : Blocks := edgeBlocks% "full/vectors/0010010010-V-0000.bin"
private noncomputable def vp0010010010_1 : Blocks := edgeBlocks% "full/vectors/0010010010-V-0001.bin"
noncomputable def vp0010010010 : Blocks := (Blocks.join vp0010010010_0 vp0010010010_1)
private theorem bp00100100100 : Branch 0 (-1167761639/8000000 : ℚ) vp0010010010 := by
  apply branch_left_normalized (c:=vp00100100100) (k:=0) (m:=137) (by decide +kernel)
  rw [show 2*(-1167761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1167761639/4000000 : ℚ) by norm_num]
  exact coverp00100100100
private noncomputable def ep00100100101_0 : Blocks := edgeBlocks% "full/vectors/00100100101-E-0000.bin"
private noncomputable def ep00100100101_1 : Blocks := edgeBlocks% "full/vectors/00100100101-E-0001.bin"
noncomputable def ep00100100101 : Blocks := (Blocks.join ep00100100101_0 ep00100100101_1)
private theorem idp00100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010010010.list =
    C ((2:ℤ)^277) * horner X vp00100100101.list + horner X ep00100100101.list := by
  exact edge_identity (B := (2:ℤ)^477) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100100101 : Branch 1 (-1167761639/8000000 : ℚ) vp0010010010 := by
  apply branch_checked idp00100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1167761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1171761639/4000000 : ℚ) by norm_num]
  exact coverp00100100101
theorem coverp0010010010 : Covers (-1167761639/8000000 : ℚ) vp0010010010 := join_branches bp00100100100 bp00100100101
private noncomputable def vp001001001_0 : Blocks := edgeBlocks% "full/vectors/001001001-V-0000.bin"
private noncomputable def vp001001001_1 : Blocks := edgeBlocks% "full/vectors/001001001-V-0001.bin"
private noncomputable def vp001001001_2 : Blocks := edgeBlocks% "full/vectors/001001001-V-0002.bin"
private noncomputable def vp001001001_3 : Blocks := edgeBlocks% "full/vectors/001001001-V-0003.bin"
noncomputable def vp001001001 : Blocks := (Blocks.join (Blocks.join vp001001001_0 vp001001001_1) (Blocks.join vp001001001_2 vp001001001_3))
private theorem bp0010010010 : Branch 0 (-1167761639/16000000 : ℚ) vp001001001 := by
  apply branch_left_normalized (c:=vp0010010010) (k:=0) (m:=252) (by decide +kernel)
  rw [show 2*(-1167761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1167761639/8000000 : ℚ) by norm_num]
  exact coverp0010010010
private noncomputable def ep0010010011_0 : Blocks := edgeBlocks% "full/vectors/0010010011-E-0000.bin"
private noncomputable def ep0010010011_1 : Blocks := edgeBlocks% "full/vectors/0010010011-E-0001.bin"
private noncomputable def ep0010010011_2 : Blocks := edgeBlocks% "full/vectors/0010010011-E-0002.bin"
private noncomputable def ep0010010011_3 : Blocks := edgeBlocks% "full/vectors/0010010011-E-0003.bin"
noncomputable def ep0010010011 : Blocks := (Blocks.join (Blocks.join ep0010010011_0 ep0010010011_1) (Blocks.join ep0010010011_2 ep0010010011_3))
private theorem idp0010010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001001.list =
    C ((2:ℤ)^528) * horner X vp0010010011.list + horner X ep0010010011.list := by
  exact edge_identity (B := (2:ℤ)^827) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010011 : Branch 1 (-1167761639/16000000 : ℚ) vp001001001 := by
  apply branch_checked idp0010010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1167761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1175761639/8000000 : ℚ) by norm_num]
  exact coverp0010010011
theorem coverp001001001 : Covers (-1167761639/16000000 : ℚ) vp001001001 := join_branches bp0010010010 bp0010010011
private noncomputable def vp0010010001111_0 : Blocks := edgeBlocks% "full/vectors/0010010001111-V-0000.bin"
noncomputable def vp0010010001111 : Blocks := vp0010010001111_0
theorem coverp0010010001111 : Covers (-1166761639/1000000 : ℚ) vp0010010001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010001110_0 : Blocks := edgeBlocks% "full/vectors/0010010001110-V-0000.bin"
noncomputable def vp0010010001110 : Blocks := vp0010010001110_0
theorem coverp0010010001110 : Covers (-1165761639/1000000 : ℚ) vp0010010001110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001000111_0 : Blocks := edgeBlocks% "full/vectors/001001000111-V-0000.bin"
noncomputable def vp001001000111 : Blocks := vp001001000111_0
private theorem bp0010010001110 : Branch 0 (-1165761639/2000000 : ℚ) vp001001000111 := by
  apply branch_left_normalized (c:=vp0010010001110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1165761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1165761639/1000000 : ℚ) by norm_num]
  exact coverp0010010001110
private noncomputable def ep0010010001111_0 : Blocks := edgeBlocks% "full/vectors/0010010001111-E-0000.bin"
noncomputable def ep0010010001111 : Blocks := ep0010010001111_0
private theorem idp0010010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001000111.list =
    C ((2:ℤ)^83) * horner X vp0010010001111.list + horner X ep0010010001111.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010001111 : Branch 1 (-1165761639/2000000 : ℚ) vp001001000111 := by
  apply branch_checked idp0010010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1165761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1166761639/1000000 : ℚ) by norm_num]
  exact coverp0010010001111
theorem coverp001001000111 : Covers (-1165761639/2000000 : ℚ) vp001001000111 := join_branches bp0010010001110 bp0010010001111
private noncomputable def vp0010010001101_0 : Blocks := edgeBlocks% "full/vectors/0010010001101-V-0000.bin"
noncomputable def vp0010010001101 : Blocks := vp0010010001101_0
theorem coverp0010010001101 : Covers (-1164761639/1000000 : ℚ) vp0010010001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010001100_0 : Blocks := edgeBlocks% "full/vectors/0010010001100-V-0000.bin"
noncomputable def vp0010010001100 : Blocks := vp0010010001100_0
theorem coverp0010010001100 : Covers (-1163761639/1000000 : ℚ) vp0010010001100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001000110_0 : Blocks := edgeBlocks% "full/vectors/001001000110-V-0000.bin"
noncomputable def vp001001000110 : Blocks := vp001001000110_0
private theorem bp0010010001100 : Branch 0 (-1163761639/2000000 : ℚ) vp001001000110 := by
  apply branch_left_normalized (c:=vp0010010001100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1163761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1163761639/1000000 : ℚ) by norm_num]
  exact coverp0010010001100
private noncomputable def ep0010010001101_0 : Blocks := edgeBlocks% "full/vectors/0010010001101-E-0000.bin"
noncomputable def ep0010010001101 : Blocks := ep0010010001101_0
private theorem idp0010010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001000110.list =
    C ((2:ℤ)^83) * horner X vp0010010001101.list + horner X ep0010010001101.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010001101 : Branch 1 (-1163761639/2000000 : ℚ) vp001001000110 := by
  apply branch_checked idp0010010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1163761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1164761639/1000000 : ℚ) by norm_num]
  exact coverp0010010001101
theorem coverp001001000110 : Covers (-1163761639/2000000 : ℚ) vp001001000110 := join_branches bp0010010001100 bp0010010001101
private noncomputable def vp00100100011_0 : Blocks := edgeBlocks% "full/vectors/00100100011-V-0000.bin"
private noncomputable def vp00100100011_1 : Blocks := edgeBlocks% "full/vectors/00100100011-V-0001.bin"
noncomputable def vp00100100011 : Blocks := (Blocks.join vp00100100011_0 vp00100100011_1)
private theorem bp001001000110 : Branch 0 (-1163761639/4000000 : ℚ) vp00100100011 := by
  apply branch_left_normalized (c:=vp001001000110) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1163761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1163761639/2000000 : ℚ) by norm_num]
  exact coverp001001000110
private noncomputable def ep001001000111_0 : Blocks := edgeBlocks% "full/vectors/001001000111-E-0000.bin"
private noncomputable def ep001001000111_1 : Blocks := edgeBlocks% "full/vectors/001001000111-E-0001.bin"
noncomputable def ep001001000111 : Blocks := (Blocks.join ep001001000111_0 ep001001000111_1)
private theorem idp001001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100100011.list =
    C ((2:ℤ)^146) * horner X vp001001000111.list + horner X ep001001000111.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001000111 : Branch 1 (-1163761639/4000000 : ℚ) vp00100100011 := by
  apply branch_checked idp001001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1163761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1165761639/2000000 : ℚ) by norm_num]
  exact coverp001001000111
theorem coverp00100100011 : Covers (-1163761639/4000000 : ℚ) vp00100100011 := join_branches bp001001000110 bp001001000111
private noncomputable def vp0010010001011_0 : Blocks := edgeBlocks% "full/vectors/0010010001011-V-0000.bin"
noncomputable def vp0010010001011 : Blocks := vp0010010001011_0
theorem coverp0010010001011 : Covers (-1162761639/1000000 : ℚ) vp0010010001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010001010_0 : Blocks := edgeBlocks% "full/vectors/0010010001010-V-0000.bin"
noncomputable def vp0010010001010 : Blocks := vp0010010001010_0
theorem coverp0010010001010 : Covers (-1161761639/1000000 : ℚ) vp0010010001010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001000101_0 : Blocks := edgeBlocks% "full/vectors/001001000101-V-0000.bin"
noncomputable def vp001001000101 : Blocks := vp001001000101_0
private theorem bp0010010001010 : Branch 0 (-1161761639/2000000 : ℚ) vp001001000101 := by
  apply branch_left_normalized (c:=vp0010010001010) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1161761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1161761639/1000000 : ℚ) by norm_num]
  exact coverp0010010001010
private noncomputable def ep0010010001011_0 : Blocks := edgeBlocks% "full/vectors/0010010001011-E-0000.bin"
noncomputable def ep0010010001011 : Blocks := ep0010010001011_0
private theorem idp0010010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001000101.list =
    C ((2:ℤ)^83) * horner X vp0010010001011.list + horner X ep0010010001011.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010001011 : Branch 1 (-1161761639/2000000 : ℚ) vp001001000101 := by
  apply branch_checked idp0010010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1161761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1162761639/1000000 : ℚ) by norm_num]
  exact coverp0010010001011
theorem coverp001001000101 : Covers (-1161761639/2000000 : ℚ) vp001001000101 := join_branches bp0010010001010 bp0010010001011
private noncomputable def vp0010010001001_0 : Blocks := edgeBlocks% "full/vectors/0010010001001-V-0000.bin"
noncomputable def vp0010010001001 : Blocks := vp0010010001001_0
theorem coverp0010010001001 : Covers (-1160761639/1000000 : ℚ) vp0010010001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010001000_0 : Blocks := edgeBlocks% "full/vectors/0010010001000-V-0000.bin"
noncomputable def vp0010010001000 : Blocks := vp0010010001000_0
theorem coverp0010010001000 : Covers (-1159761639/1000000 : ℚ) vp0010010001000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001000100_0 : Blocks := edgeBlocks% "full/vectors/001001000100-V-0000.bin"
noncomputable def vp001001000100 : Blocks := vp001001000100_0
private theorem bp0010010001000 : Branch 0 (-1159761639/2000000 : ℚ) vp001001000100 := by
  apply branch_left_normalized (c:=vp0010010001000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1159761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1159761639/1000000 : ℚ) by norm_num]
  exact coverp0010010001000
private noncomputable def ep0010010001001_0 : Blocks := edgeBlocks% "full/vectors/0010010001001-E-0000.bin"
noncomputable def ep0010010001001 : Blocks := ep0010010001001_0
private theorem idp0010010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001000100.list =
    C ((2:ℤ)^83) * horner X vp0010010001001.list + horner X ep0010010001001.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010001001 : Branch 1 (-1159761639/2000000 : ℚ) vp001001000100 := by
  apply branch_checked idp0010010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1159761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1160761639/1000000 : ℚ) by norm_num]
  exact coverp0010010001001
theorem coverp001001000100 : Covers (-1159761639/2000000 : ℚ) vp001001000100 := join_branches bp0010010001000 bp0010010001001
private noncomputable def vp00100100010_0 : Blocks := edgeBlocks% "full/vectors/00100100010-V-0000.bin"
private noncomputable def vp00100100010_1 : Blocks := edgeBlocks% "full/vectors/00100100010-V-0001.bin"
noncomputable def vp00100100010 : Blocks := (Blocks.join vp00100100010_0 vp00100100010_1)
private theorem bp001001000100 : Branch 0 (-1159761639/4000000 : ℚ) vp00100100010 := by
  apply branch_left_normalized (c:=vp001001000100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-1159761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1159761639/2000000 : ℚ) by norm_num]
  exact coverp001001000100
private noncomputable def ep001001000101_0 : Blocks := edgeBlocks% "full/vectors/001001000101-E-0000.bin"
private noncomputable def ep001001000101_1 : Blocks := edgeBlocks% "full/vectors/001001000101-E-0001.bin"
noncomputable def ep001001000101 : Blocks := (Blocks.join ep001001000101_0 ep001001000101_1)
private theorem idp001001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100100010.list =
    C ((2:ℤ)^148) * horner X vp001001000101.list + horner X ep001001000101.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001000101 : Branch 1 (-1159761639/4000000 : ℚ) vp00100100010 := by
  apply branch_checked idp001001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1159761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1161761639/2000000 : ℚ) by norm_num]
  exact coverp001001000101
theorem coverp00100100010 : Covers (-1159761639/4000000 : ℚ) vp00100100010 := join_branches bp001001000100 bp001001000101
private noncomputable def vp0010010001_0 : Blocks := edgeBlocks% "full/vectors/0010010001-V-0000.bin"
private noncomputable def vp0010010001_1 : Blocks := edgeBlocks% "full/vectors/0010010001-V-0001.bin"
noncomputable def vp0010010001 : Blocks := (Blocks.join vp0010010001_0 vp0010010001_1)
private theorem bp00100100010 : Branch 0 (-1159761639/8000000 : ℚ) vp0010010001 := by
  apply branch_left_normalized (c:=vp00100100010) (k:=0) (m:=135) (by decide +kernel)
  rw [show 2*(-1159761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1159761639/4000000 : ℚ) by norm_num]
  exact coverp00100100010
private noncomputable def ep00100100011_0 : Blocks := edgeBlocks% "full/vectors/00100100011-E-0000.bin"
private noncomputable def ep00100100011_1 : Blocks := edgeBlocks% "full/vectors/00100100011-E-0001.bin"
noncomputable def ep00100100011 : Blocks := (Blocks.join ep00100100011_0 ep00100100011_1)
private theorem idp00100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010010001.list =
    C ((2:ℤ)^275) * horner X vp00100100011.list + horner X ep00100100011.list := by
  exact edge_identity (B := (2:ℤ)^473) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100100011 : Branch 1 (-1159761639/8000000 : ℚ) vp0010010001 := by
  apply branch_checked idp00100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1159761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1163761639/4000000 : ℚ) by norm_num]
  exact coverp00100100011
theorem coverp0010010001 : Covers (-1159761639/8000000 : ℚ) vp0010010001 := join_branches bp00100100010 bp00100100011
private noncomputable def vp0010010000111_0 : Blocks := edgeBlocks% "full/vectors/0010010000111-V-0000.bin"
noncomputable def vp0010010000111 : Blocks := vp0010010000111_0
theorem coverp0010010000111 : Covers (-1158761639/1000000 : ℚ) vp0010010000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010000110_0 : Blocks := edgeBlocks% "full/vectors/0010010000110-V-0000.bin"
noncomputable def vp0010010000110 : Blocks := vp0010010000110_0
theorem coverp0010010000110 : Covers (-1157761639/1000000 : ℚ) vp0010010000110 := cover_leaf (by decide +kernel)
private noncomputable def vp001001000011_0 : Blocks := edgeBlocks% "full/vectors/001001000011-V-0000.bin"
noncomputable def vp001001000011 : Blocks := vp001001000011_0
private theorem bp0010010000110 : Branch 0 (-1157761639/2000000 : ℚ) vp001001000011 := by
  apply branch_left_normalized (c:=vp0010010000110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1157761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1157761639/1000000 : ℚ) by norm_num]
  exact coverp0010010000110
private noncomputable def ep0010010000111_0 : Blocks := edgeBlocks% "full/vectors/0010010000111-E-0000.bin"
noncomputable def ep0010010000111 : Blocks := ep0010010000111_0
private theorem idp0010010000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001000011.list =
    C ((2:ℤ)^85) * horner X vp0010010000111.list + horner X ep0010010000111.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010000111 : Branch 1 (-1157761639/2000000 : ℚ) vp001001000011 := by
  apply branch_checked idp0010010000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1157761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1158761639/1000000 : ℚ) by norm_num]
  exact coverp0010010000111
theorem coverp001001000011 : Covers (-1157761639/2000000 : ℚ) vp001001000011 := join_branches bp0010010000110 bp0010010000111
private noncomputable def vp0010010000101_0 : Blocks := edgeBlocks% "full/vectors/0010010000101-V-0000.bin"
noncomputable def vp0010010000101 : Blocks := vp0010010000101_0
theorem coverp0010010000101 : Covers (-1156761639/1000000 : ℚ) vp0010010000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010000100_0 : Blocks := edgeBlocks% "full/vectors/0010010000100-V-0000.bin"
noncomputable def vp0010010000100 : Blocks := vp0010010000100_0
theorem coverp0010010000100 : Covers (-1155761639/1000000 : ℚ) vp0010010000100 := cover_leaf (by decide +kernel)
private noncomputable def vp001001000010_0 : Blocks := edgeBlocks% "full/vectors/001001000010-V-0000.bin"
noncomputable def vp001001000010 : Blocks := vp001001000010_0
private theorem bp0010010000100 : Branch 0 (-1155761639/2000000 : ℚ) vp001001000010 := by
  apply branch_left_normalized (c:=vp0010010000100) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1155761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1155761639/1000000 : ℚ) by norm_num]
  exact coverp0010010000100
private noncomputable def ep0010010000101_0 : Blocks := edgeBlocks% "full/vectors/0010010000101-E-0000.bin"
noncomputable def ep0010010000101 : Blocks := ep0010010000101_0
private theorem idp0010010000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001000010.list =
    C ((2:ℤ)^81) * horner X vp0010010000101.list + horner X ep0010010000101.list := by
  exact edge_identity (B := (2:ℤ)^207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010000101 : Branch 1 (-1155761639/2000000 : ℚ) vp001001000010 := by
  apply branch_checked idp0010010000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1155761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1156761639/1000000 : ℚ) by norm_num]
  exact coverp0010010000101
theorem coverp001001000010 : Covers (-1155761639/2000000 : ℚ) vp001001000010 := join_branches bp0010010000100 bp0010010000101
private noncomputable def vp00100100001_0 : Blocks := edgeBlocks% "full/vectors/00100100001-V-0000.bin"
private noncomputable def vp00100100001_1 : Blocks := edgeBlocks% "full/vectors/00100100001-V-0001.bin"
noncomputable def vp00100100001 : Blocks := (Blocks.join vp00100100001_0 vp00100100001_1)
private theorem bp001001000010 : Branch 0 (-1155761639/4000000 : ℚ) vp00100100001 := by
  apply branch_left_normalized (c:=vp001001000010) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1155761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1155761639/2000000 : ℚ) by norm_num]
  exact coverp001001000010
private noncomputable def ep001001000011_0 : Blocks := edgeBlocks% "full/vectors/001001000011-E-0000.bin"
private noncomputable def ep001001000011_1 : Blocks := edgeBlocks% "full/vectors/001001000011-E-0001.bin"
noncomputable def ep001001000011 : Blocks := (Blocks.join ep001001000011_0 ep001001000011_1)
private theorem idp001001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100100001.list =
    C ((2:ℤ)^147) * horner X vp001001000011.list + horner X ep001001000011.list := by
  exact edge_identity (B := (2:ℤ)^297) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001000011 : Branch 1 (-1155761639/4000000 : ℚ) vp00100100001 := by
  apply branch_checked idp001001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1155761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1157761639/2000000 : ℚ) by norm_num]
  exact coverp001001000011
theorem coverp00100100001 : Covers (-1155761639/4000000 : ℚ) vp00100100001 := join_branches bp001001000010 bp001001000011
private noncomputable def vp0010010000011_0 : Blocks := edgeBlocks% "full/vectors/0010010000011-V-0000.bin"
noncomputable def vp0010010000011 : Blocks := vp0010010000011_0
theorem coverp0010010000011 : Covers (-1154761639/1000000 : ℚ) vp0010010000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010000010_0 : Blocks := edgeBlocks% "full/vectors/0010010000010-V-0000.bin"
noncomputable def vp0010010000010 : Blocks := vp0010010000010_0
theorem coverp0010010000010 : Covers (-1153761639/1000000 : ℚ) vp0010010000010 := cover_leaf (by decide +kernel)
private noncomputable def vp001001000001_0 : Blocks := edgeBlocks% "full/vectors/001001000001-V-0000.bin"
noncomputable def vp001001000001 : Blocks := vp001001000001_0
private theorem bp0010010000010 : Branch 0 (-1153761639/2000000 : ℚ) vp001001000001 := by
  apply branch_left_normalized (c:=vp0010010000010) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1153761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1153761639/1000000 : ℚ) by norm_num]
  exact coverp0010010000010
private noncomputable def ep0010010000011_0 : Blocks := edgeBlocks% "full/vectors/0010010000011-E-0000.bin"
noncomputable def ep0010010000011 : Blocks := ep0010010000011_0
private theorem idp0010010000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001000001.list =
    C ((2:ℤ)^80) * horner X vp0010010000011.list + horner X ep0010010000011.list := by
  exact edge_identity (B := (2:ℤ)^202) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010000011 : Branch 1 (-1153761639/2000000 : ℚ) vp001001000001 := by
  apply branch_checked idp0010010000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1153761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1154761639/1000000 : ℚ) by norm_num]
  exact coverp0010010000011
theorem coverp001001000001 : Covers (-1153761639/2000000 : ℚ) vp001001000001 := join_branches bp0010010000010 bp0010010000011
private noncomputable def vp0010010000001_0 : Blocks := edgeBlocks% "full/vectors/0010010000001-V-0000.bin"
noncomputable def vp0010010000001 : Blocks := vp0010010000001_0
theorem coverp0010010000001 : Covers (-1152761639/1000000 : ℚ) vp0010010000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010010000000_0 : Blocks := edgeBlocks% "full/vectors/0010010000000-V-0000.bin"
noncomputable def vp0010010000000 : Blocks := vp0010010000000_0
theorem coverp0010010000000 : Covers (-1151761639/1000000 : ℚ) vp0010010000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001001000000_0 : Blocks := edgeBlocks% "full/vectors/001001000000-V-0000.bin"
noncomputable def vp001001000000 : Blocks := vp001001000000_0
private theorem bp0010010000000 : Branch 0 (-1151761639/2000000 : ℚ) vp001001000000 := by
  apply branch_left_normalized (c:=vp0010010000000) (k:=0) (m:=44) (by decide +kernel)
  rw [show 2*(-1151761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1151761639/1000000 : ℚ) by norm_num]
  exact coverp0010010000000
private noncomputable def ep0010010000001_0 : Blocks := edgeBlocks% "full/vectors/0010010000001-E-0000.bin"
noncomputable def ep0010010000001 : Blocks := ep0010010000001_0
private theorem idp0010010000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001000000.list =
    C ((2:ℤ)^80) * horner X vp0010010000001.list + horner X ep0010010000001.list := by
  exact edge_identity (B := (2:ℤ)^199) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010000001 : Branch 1 (-1151761639/2000000 : ℚ) vp001001000000 := by
  apply branch_checked idp0010010000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1151761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1152761639/1000000 : ℚ) by norm_num]
  exact coverp0010010000001
theorem coverp001001000000 : Covers (-1151761639/2000000 : ℚ) vp001001000000 := join_branches bp0010010000000 bp0010010000001
private noncomputable def vp00100100000_0 : Blocks := edgeBlocks% "full/vectors/00100100000-V-0000.bin"
private noncomputable def vp00100100000_1 : Blocks := edgeBlocks% "full/vectors/00100100000-V-0001.bin"
noncomputable def vp00100100000 : Blocks := (Blocks.join vp00100100000_0 vp00100100000_1)
private theorem bp001001000000 : Branch 0 (-1151761639/4000000 : ℚ) vp00100100000 := by
  apply branch_left_normalized (c:=vp001001000000) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-1151761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1151761639/2000000 : ℚ) by norm_num]
  exact coverp001001000000
private noncomputable def ep001001000001_0 : Blocks := edgeBlocks% "full/vectors/001001000001-E-0000.bin"
private noncomputable def ep001001000001_1 : Blocks := edgeBlocks% "full/vectors/001001000001-E-0001.bin"
noncomputable def ep001001000001 : Blocks := (Blocks.join ep001001000001_0 ep001001000001_1)
private theorem idp001001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100100000.list =
    C ((2:ℤ)^143) * horner X vp001001000001.list + horner X ep001001000001.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001000001 : Branch 1 (-1151761639/4000000 : ℚ) vp00100100000 := by
  apply branch_checked idp001001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1151761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1153761639/2000000 : ℚ) by norm_num]
  exact coverp001001000001
theorem coverp00100100000 : Covers (-1151761639/4000000 : ℚ) vp00100100000 := join_branches bp001001000000 bp001001000001
private noncomputable def vp0010010000_0 : Blocks := edgeBlocks% "full/vectors/0010010000-V-0000.bin"
private noncomputable def vp0010010000_1 : Blocks := edgeBlocks% "full/vectors/0010010000-V-0001.bin"
noncomputable def vp0010010000 : Blocks := (Blocks.join vp0010010000_0 vp0010010000_1)
private theorem bp00100100000 : Branch 0 (-1151761639/8000000 : ℚ) vp0010010000 := by
  apply branch_left_normalized (c:=vp00100100000) (k:=0) (m:=132) (by decide +kernel)
  rw [show 2*(-1151761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1151761639/4000000 : ℚ) by norm_num]
  exact coverp00100100000
private noncomputable def ep00100100001_0 : Blocks := edgeBlocks% "full/vectors/00100100001-E-0000.bin"
private noncomputable def ep00100100001_1 : Blocks := edgeBlocks% "full/vectors/00100100001-E-0001.bin"
noncomputable def ep00100100001 : Blocks := (Blocks.join ep00100100001_0 ep00100100001_1)
private theorem idp00100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010010000.list =
    C ((2:ℤ)^267) * horner X vp00100100001.list + horner X ep00100100001.list := by
  exact edge_identity (B := (2:ℤ)^465) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100100001 : Branch 1 (-1151761639/8000000 : ℚ) vp0010010000 := by
  apply branch_checked idp00100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1151761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1155761639/4000000 : ℚ) by norm_num]
  exact coverp00100100001
theorem coverp0010010000 : Covers (-1151761639/8000000 : ℚ) vp0010010000 := join_branches bp00100100000 bp00100100001
private noncomputable def vp001001000_0 : Blocks := edgeBlocks% "full/vectors/001001000-V-0000.bin"
private noncomputable def vp001001000_1 : Blocks := edgeBlocks% "full/vectors/001001000-V-0001.bin"
private noncomputable def vp001001000_2 : Blocks := edgeBlocks% "full/vectors/001001000-V-0002.bin"
private noncomputable def vp001001000_3 : Blocks := edgeBlocks% "full/vectors/001001000-V-0003.bin"
noncomputable def vp001001000 : Blocks := (Blocks.join (Blocks.join vp001001000_0 vp001001000_1) (Blocks.join vp001001000_2 vp001001000_3))
private theorem bp0010010000 : Branch 0 (-1151761639/16000000 : ℚ) vp001001000 := by
  apply branch_left_normalized (c:=vp0010010000) (k:=0) (m:=248) (by decide +kernel)
  rw [show 2*(-1151761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1151761639/8000000 : ℚ) by norm_num]
  exact coverp0010010000
private noncomputable def ep0010010001_0 : Blocks := edgeBlocks% "full/vectors/0010010001-E-0000.bin"
private noncomputable def ep0010010001_1 : Blocks := edgeBlocks% "full/vectors/0010010001-E-0001.bin"
private noncomputable def ep0010010001_2 : Blocks := edgeBlocks% "full/vectors/0010010001-E-0002.bin"
private noncomputable def ep0010010001_3 : Blocks := edgeBlocks% "full/vectors/0010010001-E-0003.bin"
noncomputable def ep0010010001 : Blocks := (Blocks.join (Blocks.join ep0010010001_0 ep0010010001_1) (Blocks.join ep0010010001_2 ep0010010001_3))
private theorem idp0010010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001000.list =
    C ((2:ℤ)^520) * horner X vp0010010001.list + horner X ep0010010001.list := by
  exact edge_identity (B := (2:ℤ)^818) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010010001 : Branch 1 (-1151761639/16000000 : ℚ) vp001001000 := by
  apply branch_checked idp0010010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1151761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1159761639/8000000 : ℚ) by norm_num]
  exact coverp0010010001
theorem coverp001001000 : Covers (-1151761639/16000000 : ℚ) vp001001000 := join_branches bp0010010000 bp0010010001
private noncomputable def vp00100100_0 : Blocks := edgeBlocks% "full/vectors/00100100-V-0000.bin"
private noncomputable def vp00100100_1 : Blocks := edgeBlocks% "full/vectors/00100100-V-0001.bin"
private noncomputable def vp00100100_2 : Blocks := edgeBlocks% "full/vectors/00100100-V-0002.bin"
private noncomputable def vp00100100_3 : Blocks := edgeBlocks% "full/vectors/00100100-V-0003.bin"
private noncomputable def vp00100100_4 : Blocks := edgeBlocks% "full/vectors/00100100-V-0004.bin"
private noncomputable def vp00100100_5 : Blocks := edgeBlocks% "full/vectors/00100100-V-0005.bin"
private noncomputable def vp00100100_6 : Blocks := edgeBlocks% "full/vectors/00100100-V-0006.bin"
private noncomputable def vp00100100_7 : Blocks := edgeBlocks% "full/vectors/00100100-V-0007.bin"
noncomputable def vp00100100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00100100_0 vp00100100_1) (Blocks.join vp00100100_2 vp00100100_3)) (Blocks.join (Blocks.join vp00100100_4 vp00100100_5) (Blocks.join vp00100100_6 vp00100100_7)))
private theorem bp001001000 : Branch 0 (-1151761639/32000000 : ℚ) vp00100100 := by
  apply branch_left_normalized (c:=vp001001000) (k:=0) (m:=478) (by decide +kernel)
  rw [show 2*(-1151761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1151761639/16000000 : ℚ) by norm_num]
  exact coverp001001000
private noncomputable def ep001001001_0 : Blocks := edgeBlocks% "full/vectors/001001001-E-0000.bin"
private noncomputable def ep001001001_1 : Blocks := edgeBlocks% "full/vectors/001001001-E-0001.bin"
private noncomputable def ep001001001_2 : Blocks := edgeBlocks% "full/vectors/001001001-E-0002.bin"
private noncomputable def ep001001001_3 : Blocks := edgeBlocks% "full/vectors/001001001-E-0003.bin"
private noncomputable def ep001001001_4 : Blocks := edgeBlocks% "full/vectors/001001001-E-0004.bin"
private noncomputable def ep001001001_5 : Blocks := edgeBlocks% "full/vectors/001001001-E-0005.bin"
private noncomputable def ep001001001_6 : Blocks := edgeBlocks% "full/vectors/001001001-E-0006.bin"
private noncomputable def ep001001001_7 : Blocks := edgeBlocks% "full/vectors/001001001-E-0007.bin"
noncomputable def ep001001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep001001001_0 ep001001001_1) (Blocks.join ep001001001_2 ep001001001_3)) (Blocks.join (Blocks.join ep001001001_4 ep001001001_5) (Blocks.join ep001001001_6 ep001001001_7)))
private theorem idp001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100100.list =
    C ((2:ℤ)^1016) * horner X vp001001001.list + horner X ep001001001.list := by
  exact edge_identity (B := (2:ℤ)^1515) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001001001 : Branch 1 (-1151761639/32000000 : ℚ) vp00100100 := by
  apply branch_checked idp001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1151761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1167761639/16000000 : ℚ) by norm_num]
  exact coverp001001001
theorem coverp00100100 : Covers (-1151761639/32000000 : ℚ) vp00100100 := join_branches bp001001000 bp001001001
private noncomputable def vp0010010_0 : Blocks := edgeBlocks% "full/vectors/0010010-V-0000.bin"
private noncomputable def vp0010010_1 : Blocks := edgeBlocks% "full/vectors/0010010-V-0001.bin"
private noncomputable def vp0010010_2 : Blocks := edgeBlocks% "full/vectors/0010010-V-0002.bin"
private noncomputable def vp0010010_3 : Blocks := edgeBlocks% "full/vectors/0010010-V-0003.bin"
private noncomputable def vp0010010_4 : Blocks := edgeBlocks% "full/vectors/0010010-V-0004.bin"
private noncomputable def vp0010010_5 : Blocks := edgeBlocks% "full/vectors/0010010-V-0005.bin"
private noncomputable def vp0010010_6 : Blocks := edgeBlocks% "full/vectors/0010010-V-0006.bin"
private noncomputable def vp0010010_7 : Blocks := edgeBlocks% "full/vectors/0010010-V-0007.bin"
private noncomputable def vp0010010_8 : Blocks := edgeBlocks% "full/vectors/0010010-V-0008.bin"
private noncomputable def vp0010010_9 : Blocks := edgeBlocks% "full/vectors/0010010-V-0009.bin"
private noncomputable def vp0010010_10 : Blocks := edgeBlocks% "full/vectors/0010010-V-0010.bin"
private noncomputable def vp0010010_11 : Blocks := edgeBlocks% "full/vectors/0010010-V-0011.bin"
private noncomputable def vp0010010_12 : Blocks := edgeBlocks% "full/vectors/0010010-V-0012.bin"
private noncomputable def vp0010010_13 : Blocks := edgeBlocks% "full/vectors/0010010-V-0013.bin"
private noncomputable def vp0010010_14 : Blocks := edgeBlocks% "full/vectors/0010010-V-0014.bin"
noncomputable def vp0010010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0010010_0 (Blocks.join vp0010010_1 vp0010010_2)) (Blocks.join (Blocks.join vp0010010_3 vp0010010_4) (Blocks.join vp0010010_5 vp0010010_6))) (Blocks.join (Blocks.join (Blocks.join vp0010010_7 vp0010010_8) (Blocks.join vp0010010_9 vp0010010_10)) (Blocks.join (Blocks.join vp0010010_11 vp0010010_12) (Blocks.join vp0010010_13 vp0010010_14))))
private theorem bp00100100 : Branch 0 (-1151761639/64000000 : ℚ) vp0010010 := by
  apply branch_left_normalized (c:=vp00100100) (k:=0) (m:=931) (by decide +kernel)
  rw [show 2*(-1151761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1151761639/32000000 : ℚ) by norm_num]
  exact coverp00100100
private noncomputable def ep00100101_0 : Blocks := edgeBlocks% "full/vectors/00100101-E-0000.bin"
private noncomputable def ep00100101_1 : Blocks := edgeBlocks% "full/vectors/00100101-E-0001.bin"
private noncomputable def ep00100101_2 : Blocks := edgeBlocks% "full/vectors/00100101-E-0002.bin"
private noncomputable def ep00100101_3 : Blocks := edgeBlocks% "full/vectors/00100101-E-0003.bin"
private noncomputable def ep00100101_4 : Blocks := edgeBlocks% "full/vectors/00100101-E-0004.bin"
private noncomputable def ep00100101_5 : Blocks := edgeBlocks% "full/vectors/00100101-E-0005.bin"
private noncomputable def ep00100101_6 : Blocks := edgeBlocks% "full/vectors/00100101-E-0006.bin"
private noncomputable def ep00100101_7 : Blocks := edgeBlocks% "full/vectors/00100101-E-0007.bin"
private noncomputable def ep00100101_8 : Blocks := edgeBlocks% "full/vectors/00100101-E-0008.bin"
private noncomputable def ep00100101_9 : Blocks := edgeBlocks% "full/vectors/00100101-E-0009.bin"
private noncomputable def ep00100101_10 : Blocks := edgeBlocks% "full/vectors/00100101-E-0010.bin"
private noncomputable def ep00100101_11 : Blocks := edgeBlocks% "full/vectors/00100101-E-0011.bin"
private noncomputable def ep00100101_12 : Blocks := edgeBlocks% "full/vectors/00100101-E-0012.bin"
private noncomputable def ep00100101_13 : Blocks := edgeBlocks% "full/vectors/00100101-E-0013.bin"
private noncomputable def ep00100101_14 : Blocks := edgeBlocks% "full/vectors/00100101-E-0014.bin"
noncomputable def ep00100101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00100101_0 (Blocks.join ep00100101_1 ep00100101_2)) (Blocks.join (Blocks.join ep00100101_3 ep00100101_4) (Blocks.join ep00100101_5 ep00100101_6))) (Blocks.join (Blocks.join (Blocks.join ep00100101_7 ep00100101_8) (Blocks.join ep00100101_9 ep00100101_10)) (Blocks.join (Blocks.join ep00100101_11 ep00100101_12) (Blocks.join ep00100101_13 ep00100101_14))))
private theorem idp00100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010010.list =
    C ((2:ℤ)^1997) * horner X vp00100101.list + horner X ep00100101.list := by
  exact edge_identity (B := (2:ℤ)^2888) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100101 : Branch 1 (-1151761639/64000000 : ℚ) vp0010010 := by
  apply branch_checked idp00100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1151761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1183761639/32000000 : ℚ) by norm_num]
  exact coverp00100101
theorem coverp0010010 : Covers (-1151761639/64000000 : ℚ) vp0010010 := join_branches bp00100100 bp00100101
private noncomputable def vp001001_0 : Blocks := edgeBlocks% "full/vectors/001001-V-0000.bin"
private noncomputable def vp001001_1 : Blocks := edgeBlocks% "full/vectors/001001-V-0001.bin"
private noncomputable def vp001001_2 : Blocks := edgeBlocks% "full/vectors/001001-V-0002.bin"
private noncomputable def vp001001_3 : Blocks := edgeBlocks% "full/vectors/001001-V-0003.bin"
private noncomputable def vp001001_4 : Blocks := edgeBlocks% "full/vectors/001001-V-0004.bin"
private noncomputable def vp001001_5 : Blocks := edgeBlocks% "full/vectors/001001-V-0005.bin"
private noncomputable def vp001001_6 : Blocks := edgeBlocks% "full/vectors/001001-V-0006.bin"
private noncomputable def vp001001_7 : Blocks := edgeBlocks% "full/vectors/001001-V-0007.bin"
private noncomputable def vp001001_8 : Blocks := edgeBlocks% "full/vectors/001001-V-0008.bin"
private noncomputable def vp001001_9 : Blocks := edgeBlocks% "full/vectors/001001-V-0009.bin"
private noncomputable def vp001001_10 : Blocks := edgeBlocks% "full/vectors/001001-V-0010.bin"
private noncomputable def vp001001_11 : Blocks := edgeBlocks% "full/vectors/001001-V-0011.bin"
private noncomputable def vp001001_12 : Blocks := edgeBlocks% "full/vectors/001001-V-0012.bin"
private noncomputable def vp001001_13 : Blocks := edgeBlocks% "full/vectors/001001-V-0013.bin"
private noncomputable def vp001001_14 : Blocks := edgeBlocks% "full/vectors/001001-V-0014.bin"
private noncomputable def vp001001_15 : Blocks := edgeBlocks% "full/vectors/001001-V-0015.bin"
private noncomputable def vp001001_16 : Blocks := edgeBlocks% "full/vectors/001001-V-0016.bin"
private noncomputable def vp001001_17 : Blocks := edgeBlocks% "full/vectors/001001-V-0017.bin"
private noncomputable def vp001001_18 : Blocks := edgeBlocks% "full/vectors/001001-V-0018.bin"
private noncomputable def vp001001_19 : Blocks := edgeBlocks% "full/vectors/001001-V-0019.bin"
private noncomputable def vp001001_20 : Blocks := edgeBlocks% "full/vectors/001001-V-0020.bin"
private noncomputable def vp001001_21 : Blocks := edgeBlocks% "full/vectors/001001-V-0021.bin"
private noncomputable def vp001001_22 : Blocks := edgeBlocks% "full/vectors/001001-V-0022.bin"
private noncomputable def vp001001_23 : Blocks := edgeBlocks% "full/vectors/001001-V-0023.bin"
private noncomputable def vp001001_24 : Blocks := edgeBlocks% "full/vectors/001001-V-0024.bin"
private noncomputable def vp001001_25 : Blocks := edgeBlocks% "full/vectors/001001-V-0025.bin"
private noncomputable def vp001001_26 : Blocks := edgeBlocks% "full/vectors/001001-V-0026.bin"
private noncomputable def vp001001_27 : Blocks := edgeBlocks% "full/vectors/001001-V-0027.bin"
noncomputable def vp001001 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp001001_0 (Blocks.join vp001001_1 vp001001_2)) (Blocks.join (Blocks.join vp001001_3 vp001001_4) (Blocks.join vp001001_5 vp001001_6))) (Blocks.join (Blocks.join vp001001_7 (Blocks.join vp001001_8 vp001001_9)) (Blocks.join (Blocks.join vp001001_10 vp001001_11) (Blocks.join vp001001_12 vp001001_13)))) (Blocks.join (Blocks.join (Blocks.join vp001001_14 (Blocks.join vp001001_15 vp001001_16)) (Blocks.join (Blocks.join vp001001_17 vp001001_18) (Blocks.join vp001001_19 vp001001_20))) (Blocks.join (Blocks.join vp001001_21 (Blocks.join vp001001_22 vp001001_23)) (Blocks.join (Blocks.join vp001001_24 vp001001_25) (Blocks.join vp001001_26 vp001001_27)))))
private theorem bp0010010 : Branch 0 (-1151761639/128000000 : ℚ) vp001001 := by
  apply branch_left_normalized (c:=vp0010010) (k:=0) (m:=1819) (by decide +kernel)
  rw [show 2*(-1151761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-1151761639/64000000 : ℚ) by norm_num]
  exact coverp0010010
private noncomputable def ep0010011_0 : Blocks := edgeBlocks% "full/vectors/0010011-E-0000.bin"
private noncomputable def ep0010011_1 : Blocks := edgeBlocks% "full/vectors/0010011-E-0001.bin"
private noncomputable def ep0010011_2 : Blocks := edgeBlocks% "full/vectors/0010011-E-0002.bin"
private noncomputable def ep0010011_3 : Blocks := edgeBlocks% "full/vectors/0010011-E-0003.bin"
private noncomputable def ep0010011_4 : Blocks := edgeBlocks% "full/vectors/0010011-E-0004.bin"
private noncomputable def ep0010011_5 : Blocks := edgeBlocks% "full/vectors/0010011-E-0005.bin"
private noncomputable def ep0010011_6 : Blocks := edgeBlocks% "full/vectors/0010011-E-0006.bin"
private noncomputable def ep0010011_7 : Blocks := edgeBlocks% "full/vectors/0010011-E-0007.bin"
private noncomputable def ep0010011_8 : Blocks := edgeBlocks% "full/vectors/0010011-E-0008.bin"
private noncomputable def ep0010011_9 : Blocks := edgeBlocks% "full/vectors/0010011-E-0009.bin"
private noncomputable def ep0010011_10 : Blocks := edgeBlocks% "full/vectors/0010011-E-0010.bin"
private noncomputable def ep0010011_11 : Blocks := edgeBlocks% "full/vectors/0010011-E-0011.bin"
private noncomputable def ep0010011_12 : Blocks := edgeBlocks% "full/vectors/0010011-E-0012.bin"
private noncomputable def ep0010011_13 : Blocks := edgeBlocks% "full/vectors/0010011-E-0013.bin"
private noncomputable def ep0010011_14 : Blocks := edgeBlocks% "full/vectors/0010011-E-0014.bin"
private noncomputable def ep0010011_15 : Blocks := edgeBlocks% "full/vectors/0010011-E-0015.bin"
private noncomputable def ep0010011_16 : Blocks := edgeBlocks% "full/vectors/0010011-E-0016.bin"
private noncomputable def ep0010011_17 : Blocks := edgeBlocks% "full/vectors/0010011-E-0017.bin"
private noncomputable def ep0010011_18 : Blocks := edgeBlocks% "full/vectors/0010011-E-0018.bin"
private noncomputable def ep0010011_19 : Blocks := edgeBlocks% "full/vectors/0010011-E-0019.bin"
private noncomputable def ep0010011_20 : Blocks := edgeBlocks% "full/vectors/0010011-E-0020.bin"
private noncomputable def ep0010011_21 : Blocks := edgeBlocks% "full/vectors/0010011-E-0021.bin"
private noncomputable def ep0010011_22 : Blocks := edgeBlocks% "full/vectors/0010011-E-0022.bin"
private noncomputable def ep0010011_23 : Blocks := edgeBlocks% "full/vectors/0010011-E-0023.bin"
private noncomputable def ep0010011_24 : Blocks := edgeBlocks% "full/vectors/0010011-E-0024.bin"
private noncomputable def ep0010011_25 : Blocks := edgeBlocks% "full/vectors/0010011-E-0025.bin"
private noncomputable def ep0010011_26 : Blocks := edgeBlocks% "full/vectors/0010011-E-0026.bin"
private noncomputable def ep0010011_27 : Blocks := edgeBlocks% "full/vectors/0010011-E-0027.bin"
noncomputable def ep0010011 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0010011_0 (Blocks.join ep0010011_1 ep0010011_2)) (Blocks.join (Blocks.join ep0010011_3 ep0010011_4) (Blocks.join ep0010011_5 ep0010011_6))) (Blocks.join (Blocks.join ep0010011_7 (Blocks.join ep0010011_8 ep0010011_9)) (Blocks.join (Blocks.join ep0010011_10 ep0010011_11) (Blocks.join ep0010011_12 ep0010011_13)))) (Blocks.join (Blocks.join (Blocks.join ep0010011_14 (Blocks.join ep0010011_15 ep0010011_16)) (Blocks.join (Blocks.join ep0010011_17 ep0010011_18) (Blocks.join ep0010011_19 ep0010011_20))) (Blocks.join (Blocks.join ep0010011_21 (Blocks.join ep0010011_22 ep0010011_23)) (Blocks.join (Blocks.join ep0010011_24 ep0010011_25) (Blocks.join ep0010011_26 ep0010011_27)))))
private def ptsp0010011 : List ℤ := [((2:ℤ)^3409+0),((2:ℤ)^3409+1)]
private theorem boundp0010011 : 2^vp001001.size*absSum vp001001.list + ((2:ℤ)^3881*absSum vp0010011.list+absSum ep0010011.list) < (2:ℤ)^5543 := by decide +kernel
private theorem pointp0010011_0 : fastHom 1 ((2:ℤ)^3409+0) vp001001 = ((2:ℤ)^3881)*vp0010011.subst ((2:ℤ)^3409+0)+ep0010011.subst ((2:ℤ)^3409+0) := by decide +kernel
private theorem pointp0010011_1 : fastHom 1 ((2:ℤ)^3409+1) vp001001 = ((2:ℤ)^3881)*vp0010011.subst ((2:ℤ)^3409+1)+ep0010011.subst ((2:ℤ)^3409+1) := by decide +kernel
private theorem checkp0010011 (x:ℤ) (hx:x ∈ ptsp0010011) : fastHom 1 x vp001001 = ((2:ℤ)^3881)*vp0010011.subst x+ep0010011.subst x := by
  simp only [ptsp0010011,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp0010011_0
  · exact pointp0010011_1
private theorem idp0010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001001.list =
    C ((2:ℤ)^3881) * horner X vp0010011.list + horner X ep0010011.list := by
  apply edge_identity (B := (2:ℤ)^5543) (by decide) (by positivity) (by positivity) boundp0010011
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0010011 (by decide +kernel)
  · have h : ptsp0010011.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0010011.trans_le (by decide +kernel)
  · exact checkp0010011
private theorem bp0010011 : Branch 1 (-1151761639/128000000 : ℚ) vp001001 := by
  apply branch_checked idp0010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1151761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-1215761639/64000000 : ℚ) by norm_num]
  exact coverp0010011
theorem coverp001001 : Covers (-1151761639/128000000 : ℚ) vp001001 := join_branches bp0010010 bp0010011
end NextProof.EdgeFull

