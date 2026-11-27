import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp001000111111_0 : Blocks := edgeBlocks% "full/vectors/001000111111-V-0000.bin"
noncomputable def vp001000111111 : Blocks := vp001000111111_0
theorem coverp001000111111 : Covers (-1149761639/2000000 : ℚ) vp001000111111 := cover_leaf (by decide +kernel)
private noncomputable def vp001000111110_0 : Blocks := edgeBlocks% "full/vectors/001000111110-V-0000.bin"
noncomputable def vp001000111110 : Blocks := vp001000111110_0
theorem coverp001000111110 : Covers (-1147761639/2000000 : ℚ) vp001000111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00100011111_0 : Blocks := edgeBlocks% "full/vectors/00100011111-V-0000.bin"
private noncomputable def vp00100011111_1 : Blocks := edgeBlocks% "full/vectors/00100011111-V-0001.bin"
noncomputable def vp00100011111 : Blocks := (Blocks.join vp00100011111_0 vp00100011111_1)
private theorem bp001000111110 : Branch 0 (-1147761639/4000000 : ℚ) vp00100011111 := by
  apply branch_left_normalized (c:=vp001000111110) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-1147761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1147761639/2000000 : ℚ) by norm_num]
  exact coverp001000111110
private noncomputable def ep001000111111_0 : Blocks := edgeBlocks% "full/vectors/001000111111-E-0000.bin"
private noncomputable def ep001000111111_1 : Blocks := edgeBlocks% "full/vectors/001000111111-E-0001.bin"
noncomputable def ep001000111111 : Blocks := (Blocks.join ep001000111111_0 ep001000111111_1)
private theorem idp001000111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100011111.list =
    C ((2:ℤ)^143) * horner X vp001000111111.list + horner X ep001000111111.list := by
  exact edge_identity (B := (2:ℤ)^285) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000111111 : Branch 1 (-1147761639/4000000 : ℚ) vp00100011111 := by
  apply branch_checked idp001000111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1147761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1149761639/2000000 : ℚ) by norm_num]
  exact coverp001000111111
theorem coverp00100011111 : Covers (-1147761639/4000000 : ℚ) vp00100011111 := join_branches bp001000111110 bp001000111111
private noncomputable def vp001000111101_0 : Blocks := edgeBlocks% "full/vectors/001000111101-V-0000.bin"
noncomputable def vp001000111101 : Blocks := vp001000111101_0
theorem coverp001000111101 : Covers (-1145761639/2000000 : ℚ) vp001000111101 := cover_leaf (by decide +kernel)
private noncomputable def vp001000111100_0 : Blocks := edgeBlocks% "full/vectors/001000111100-V-0000.bin"
noncomputable def vp001000111100 : Blocks := vp001000111100_0
theorem coverp001000111100 : Covers (-1143761639/2000000 : ℚ) vp001000111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00100011110_0 : Blocks := edgeBlocks% "full/vectors/00100011110-V-0000.bin"
private noncomputable def vp00100011110_1 : Blocks := edgeBlocks% "full/vectors/00100011110-V-0001.bin"
noncomputable def vp00100011110 : Blocks := (Blocks.join vp00100011110_0 vp00100011110_1)
private theorem bp001000111100 : Branch 0 (-1143761639/4000000 : ℚ) vp00100011110 := by
  apply branch_left_normalized (c:=vp001000111100) (k:=0) (m:=72) (by decide +kernel)
  rw [show 2*(-1143761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1143761639/2000000 : ℚ) by norm_num]
  exact coverp001000111100
private noncomputable def ep001000111101_0 : Blocks := edgeBlocks% "full/vectors/001000111101-E-0000.bin"
private noncomputable def ep001000111101_1 : Blocks := edgeBlocks% "full/vectors/001000111101-E-0001.bin"
noncomputable def ep001000111101 : Blocks := (Blocks.join ep001000111101_0 ep001000111101_1)
private theorem idp001000111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100011110.list =
    C ((2:ℤ)^144) * horner X vp001000111101.list + horner X ep001000111101.list := by
  exact edge_identity (B := (2:ℤ)^285) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000111101 : Branch 1 (-1143761639/4000000 : ℚ) vp00100011110 := by
  apply branch_checked idp001000111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1143761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1145761639/2000000 : ℚ) by norm_num]
  exact coverp001000111101
theorem coverp00100011110 : Covers (-1143761639/4000000 : ℚ) vp00100011110 := join_branches bp001000111100 bp001000111101
private noncomputable def vp0010001111_0 : Blocks := edgeBlocks% "full/vectors/0010001111-V-0000.bin"
private noncomputable def vp0010001111_1 : Blocks := edgeBlocks% "full/vectors/0010001111-V-0001.bin"
noncomputable def vp0010001111 : Blocks := (Blocks.join vp0010001111_0 vp0010001111_1)
private theorem bp00100011110 : Branch 0 (-1143761639/8000000 : ℚ) vp0010001111 := by
  apply branch_left_normalized (c:=vp00100011110) (k:=0) (m:=132) (by decide +kernel)
  rw [show 2*(-1143761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1143761639/4000000 : ℚ) by norm_num]
  exact coverp00100011110
private noncomputable def ep00100011111_0 : Blocks := edgeBlocks% "full/vectors/00100011111-E-0000.bin"
private noncomputable def ep00100011111_1 : Blocks := edgeBlocks% "full/vectors/00100011111-E-0001.bin"
noncomputable def ep00100011111 : Blocks := (Blocks.join ep00100011111_0 ep00100011111_1)
private theorem idp00100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010001111.list =
    C ((2:ℤ)^271) * horner X vp00100011111.list + horner X ep00100011111.list := by
  exact edge_identity (B := (2:ℤ)^463) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100011111 : Branch 1 (-1143761639/8000000 : ℚ) vp0010001111 := by
  apply branch_checked idp00100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1143761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1147761639/4000000 : ℚ) by norm_num]
  exact coverp00100011111
theorem coverp0010001111 : Covers (-1143761639/8000000 : ℚ) vp0010001111 := join_branches bp00100011110 bp00100011111
private noncomputable def vp001000111011_0 : Blocks := edgeBlocks% "full/vectors/001000111011-V-0000.bin"
noncomputable def vp001000111011 : Blocks := vp001000111011_0
theorem coverp001000111011 : Covers (-1141761639/2000000 : ℚ) vp001000111011 := cover_leaf (by decide +kernel)
private noncomputable def vp001000111010_0 : Blocks := edgeBlocks% "full/vectors/001000111010-V-0000.bin"
noncomputable def vp001000111010 : Blocks := vp001000111010_0
theorem coverp001000111010 : Covers (-1139761639/2000000 : ℚ) vp001000111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00100011101_0 : Blocks := edgeBlocks% "full/vectors/00100011101-V-0000.bin"
private noncomputable def vp00100011101_1 : Blocks := edgeBlocks% "full/vectors/00100011101-V-0001.bin"
noncomputable def vp00100011101 : Blocks := (Blocks.join vp00100011101_0 vp00100011101_1)
private theorem bp001000111010 : Branch 0 (-1139761639/4000000 : ℚ) vp00100011101 := by
  apply branch_left_normalized (c:=vp001000111010) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-1139761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1139761639/2000000 : ℚ) by norm_num]
  exact coverp001000111010
private noncomputable def ep001000111011_0 : Blocks := edgeBlocks% "full/vectors/001000111011-E-0000.bin"
private noncomputable def ep001000111011_1 : Blocks := edgeBlocks% "full/vectors/001000111011-E-0001.bin"
noncomputable def ep001000111011 : Blocks := (Blocks.join ep001000111011_0 ep001000111011_1)
private theorem idp001000111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100011101.list =
    C ((2:ℤ)^143) * horner X vp001000111011.list + horner X ep001000111011.list := by
  exact edge_identity (B := (2:ℤ)^284) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000111011 : Branch 1 (-1139761639/4000000 : ℚ) vp00100011101 := by
  apply branch_checked idp001000111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1139761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1141761639/2000000 : ℚ) by norm_num]
  exact coverp001000111011
theorem coverp00100011101 : Covers (-1139761639/4000000 : ℚ) vp00100011101 := join_branches bp001000111010 bp001000111011
private noncomputable def vp001000111001_0 : Blocks := edgeBlocks% "full/vectors/001000111001-V-0000.bin"
noncomputable def vp001000111001 : Blocks := vp001000111001_0
theorem coverp001000111001 : Covers (-1137761639/2000000 : ℚ) vp001000111001 := cover_leaf (by decide +kernel)
private noncomputable def vp001000111000_0 : Blocks := edgeBlocks% "full/vectors/001000111000-V-0000.bin"
noncomputable def vp001000111000 : Blocks := vp001000111000_0
theorem coverp001000111000 : Covers (-1135761639/2000000 : ℚ) vp001000111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00100011100_0 : Blocks := edgeBlocks% "full/vectors/00100011100-V-0000.bin"
private noncomputable def vp00100011100_1 : Blocks := edgeBlocks% "full/vectors/00100011100-V-0001.bin"
noncomputable def vp00100011100 : Blocks := (Blocks.join vp00100011100_0 vp00100011100_1)
private theorem bp001000111000 : Branch 0 (-1135761639/4000000 : ℚ) vp00100011100 := by
  apply branch_left_normalized (c:=vp001000111000) (k:=0) (m:=73) (by decide +kernel)
  rw [show 2*(-1135761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1135761639/2000000 : ℚ) by norm_num]
  exact coverp001000111000
private noncomputable def ep001000111001_0 : Blocks := edgeBlocks% "full/vectors/001000111001-E-0000.bin"
private noncomputable def ep001000111001_1 : Blocks := edgeBlocks% "full/vectors/001000111001-E-0001.bin"
noncomputable def ep001000111001 : Blocks := (Blocks.join ep001000111001_0 ep001000111001_1)
private theorem idp001000111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100011100.list =
    C ((2:ℤ)^145) * horner X vp001000111001.list + horner X ep001000111001.list := by
  exact edge_identity (B := (2:ℤ)^286) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000111001 : Branch 1 (-1135761639/4000000 : ℚ) vp00100011100 := by
  apply branch_checked idp001000111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1135761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1137761639/2000000 : ℚ) by norm_num]
  exact coverp001000111001
theorem coverp00100011100 : Covers (-1135761639/4000000 : ℚ) vp00100011100 := join_branches bp001000111000 bp001000111001
private noncomputable def vp0010001110_0 : Blocks := edgeBlocks% "full/vectors/0010001110-V-0000.bin"
private noncomputable def vp0010001110_1 : Blocks := edgeBlocks% "full/vectors/0010001110-V-0001.bin"
noncomputable def vp0010001110 : Blocks := (Blocks.join vp0010001110_0 vp0010001110_1)
private theorem bp00100011100 : Branch 0 (-1135761639/8000000 : ℚ) vp0010001110 := by
  apply branch_left_normalized (c:=vp00100011100) (k:=0) (m:=132) (by decide +kernel)
  rw [show 2*(-1135761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1135761639/4000000 : ℚ) by norm_num]
  exact coverp00100011100
private noncomputable def ep00100011101_0 : Blocks := edgeBlocks% "full/vectors/00100011101-E-0000.bin"
private noncomputable def ep00100011101_1 : Blocks := edgeBlocks% "full/vectors/00100011101-E-0001.bin"
noncomputable def ep00100011101 : Blocks := (Blocks.join ep00100011101_0 ep00100011101_1)
private theorem idp00100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010001110.list =
    C ((2:ℤ)^273) * horner X vp00100011101.list + horner X ep00100011101.list := by
  exact edge_identity (B := (2:ℤ)^464) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100011101 : Branch 1 (-1135761639/8000000 : ℚ) vp0010001110 := by
  apply branch_checked idp00100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1135761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1139761639/4000000 : ℚ) by norm_num]
  exact coverp00100011101
theorem coverp0010001110 : Covers (-1135761639/8000000 : ℚ) vp0010001110 := join_branches bp00100011100 bp00100011101
private noncomputable def vp001000111_0 : Blocks := edgeBlocks% "full/vectors/001000111-V-0000.bin"
private noncomputable def vp001000111_1 : Blocks := edgeBlocks% "full/vectors/001000111-V-0001.bin"
private noncomputable def vp001000111_2 : Blocks := edgeBlocks% "full/vectors/001000111-V-0002.bin"
private noncomputable def vp001000111_3 : Blocks := edgeBlocks% "full/vectors/001000111-V-0003.bin"
noncomputable def vp001000111 : Blocks := (Blocks.join (Blocks.join vp001000111_0 vp001000111_1) (Blocks.join vp001000111_2 vp001000111_3))
private theorem bp0010001110 : Branch 0 (-1135761639/16000000 : ℚ) vp001000111 := by
  apply branch_left_normalized (c:=vp0010001110) (k:=0) (m:=248) (by decide +kernel)
  rw [show 2*(-1135761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1135761639/8000000 : ℚ) by norm_num]
  exact coverp0010001110
private noncomputable def ep0010001111_0 : Blocks := edgeBlocks% "full/vectors/0010001111-E-0000.bin"
private noncomputable def ep0010001111_1 : Blocks := edgeBlocks% "full/vectors/0010001111-E-0001.bin"
private noncomputable def ep0010001111_2 : Blocks := edgeBlocks% "full/vectors/0010001111-E-0002.bin"
private noncomputable def ep0010001111_3 : Blocks := edgeBlocks% "full/vectors/0010001111-E-0003.bin"
noncomputable def ep0010001111 : Blocks := (Blocks.join (Blocks.join ep0010001111_0 ep0010001111_1) (Blocks.join ep0010001111_2 ep0010001111_3))
private theorem idp0010001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000111.list =
    C ((2:ℤ)^527) * horner X vp0010001111.list + horner X ep0010001111.list := by
  exact edge_identity (B := (2:ℤ)^818) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001111 : Branch 1 (-1135761639/16000000 : ℚ) vp001000111 := by
  apply branch_checked idp0010001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1135761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1143761639/8000000 : ℚ) by norm_num]
  exact coverp0010001111
theorem coverp001000111 : Covers (-1135761639/16000000 : ℚ) vp001000111 := join_branches bp0010001110 bp0010001111
private noncomputable def vp001000110111_0 : Blocks := edgeBlocks% "full/vectors/001000110111-V-0000.bin"
noncomputable def vp001000110111 : Blocks := vp001000110111_0
theorem coverp001000110111 : Covers (-1133761639/2000000 : ℚ) vp001000110111 := cover_leaf (by decide +kernel)
private noncomputable def vp001000110110_0 : Blocks := edgeBlocks% "full/vectors/001000110110-V-0000.bin"
noncomputable def vp001000110110 : Blocks := vp001000110110_0
theorem coverp001000110110 : Covers (-1131761639/2000000 : ℚ) vp001000110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00100011011_0 : Blocks := edgeBlocks% "full/vectors/00100011011-V-0000.bin"
private noncomputable def vp00100011011_1 : Blocks := edgeBlocks% "full/vectors/00100011011-V-0001.bin"
noncomputable def vp00100011011 : Blocks := (Blocks.join vp00100011011_0 vp00100011011_1)
private theorem bp001000110110 : Branch 0 (-1131761639/4000000 : ℚ) vp00100011011 := by
  apply branch_left_normalized (c:=vp001000110110) (k:=0) (m:=74) (by decide +kernel)
  rw [show 2*(-1131761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1131761639/2000000 : ℚ) by norm_num]
  exact coverp001000110110
private noncomputable def ep001000110111_0 : Blocks := edgeBlocks% "full/vectors/001000110111-E-0000.bin"
private noncomputable def ep001000110111_1 : Blocks := edgeBlocks% "full/vectors/001000110111-E-0001.bin"
noncomputable def ep001000110111 : Blocks := (Blocks.join ep001000110111_0 ep001000110111_1)
private theorem idp001000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100011011.list =
    C ((2:ℤ)^146) * horner X vp001000110111.list + horner X ep001000110111.list := by
  exact edge_identity (B := (2:ℤ)^288) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000110111 : Branch 1 (-1131761639/4000000 : ℚ) vp00100011011 := by
  apply branch_checked idp001000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1131761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1133761639/2000000 : ℚ) by norm_num]
  exact coverp001000110111
theorem coverp00100011011 : Covers (-1131761639/4000000 : ℚ) vp00100011011 := join_branches bp001000110110 bp001000110111
private noncomputable def vp001000110101_0 : Blocks := edgeBlocks% "full/vectors/001000110101-V-0000.bin"
noncomputable def vp001000110101 : Blocks := vp001000110101_0
theorem coverp001000110101 : Covers (-1129761639/2000000 : ℚ) vp001000110101 := cover_leaf (by decide +kernel)
private noncomputable def vp001000110100_0 : Blocks := edgeBlocks% "full/vectors/001000110100-V-0000.bin"
noncomputable def vp001000110100 : Blocks := vp001000110100_0
theorem coverp001000110100 : Covers (-1127761639/2000000 : ℚ) vp001000110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00100011010_0 : Blocks := edgeBlocks% "full/vectors/00100011010-V-0000.bin"
private noncomputable def vp00100011010_1 : Blocks := edgeBlocks% "full/vectors/00100011010-V-0001.bin"
noncomputable def vp00100011010 : Blocks := (Blocks.join vp00100011010_0 vp00100011010_1)
private theorem bp001000110100 : Branch 0 (-1127761639/4000000 : ℚ) vp00100011010 := by
  apply branch_left_normalized (c:=vp001000110100) (k:=0) (m:=76) (by decide +kernel)
  rw [show 2*(-1127761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1127761639/2000000 : ℚ) by norm_num]
  exact coverp001000110100
private noncomputable def ep001000110101_0 : Blocks := edgeBlocks% "full/vectors/001000110101-E-0000.bin"
private noncomputable def ep001000110101_1 : Blocks := edgeBlocks% "full/vectors/001000110101-E-0001.bin"
noncomputable def ep001000110101 : Blocks := (Blocks.join ep001000110101_0 ep001000110101_1)
private theorem idp001000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100011010.list =
    C ((2:ℤ)^149) * horner X vp001000110101.list + horner X ep001000110101.list := by
  exact edge_identity (B := (2:ℤ)^293) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000110101 : Branch 1 (-1127761639/4000000 : ℚ) vp00100011010 := by
  apply branch_checked idp001000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1127761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1129761639/2000000 : ℚ) by norm_num]
  exact coverp001000110101
theorem coverp00100011010 : Covers (-1127761639/4000000 : ℚ) vp00100011010 := join_branches bp001000110100 bp001000110101
private noncomputable def vp0010001101_0 : Blocks := edgeBlocks% "full/vectors/0010001101-V-0000.bin"
private noncomputable def vp0010001101_1 : Blocks := edgeBlocks% "full/vectors/0010001101-V-0001.bin"
noncomputable def vp0010001101 : Blocks := (Blocks.join vp0010001101_0 vp0010001101_1)
private theorem bp00100011010 : Branch 0 (-1127761639/8000000 : ℚ) vp0010001101 := by
  apply branch_left_normalized (c:=vp00100011010) (k:=0) (m:=135) (by decide +kernel)
  rw [show 2*(-1127761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1127761639/4000000 : ℚ) by norm_num]
  exact coverp00100011010
private noncomputable def ep00100011011_0 : Blocks := edgeBlocks% "full/vectors/00100011011-E-0000.bin"
private noncomputable def ep00100011011_1 : Blocks := edgeBlocks% "full/vectors/00100011011-E-0001.bin"
noncomputable def ep00100011011 : Blocks := (Blocks.join ep00100011011_0 ep00100011011_1)
private theorem idp00100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010001101.list =
    C ((2:ℤ)^279) * horner X vp00100011011.list + horner X ep00100011011.list := by
  exact edge_identity (B := (2:ℤ)^472) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100011011 : Branch 1 (-1127761639/8000000 : ℚ) vp0010001101 := by
  apply branch_checked idp00100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1127761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1131761639/4000000 : ℚ) by norm_num]
  exact coverp00100011011
theorem coverp0010001101 : Covers (-1127761639/8000000 : ℚ) vp0010001101 := join_branches bp00100011010 bp00100011011
private noncomputable def vp0010001100111_0 : Blocks := edgeBlocks% "full/vectors/0010001100111-V-0000.bin"
noncomputable def vp0010001100111 : Blocks := vp0010001100111_0
theorem coverp0010001100111 : Covers (-1126761639/1000000 : ℚ) vp0010001100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001100110_0 : Blocks := edgeBlocks% "full/vectors/0010001100110-V-0000.bin"
noncomputable def vp0010001100110 : Blocks := vp0010001100110_0
theorem coverp0010001100110 : Covers (-1125761639/1000000 : ℚ) vp0010001100110 := cover_leaf (by decide +kernel)
private noncomputable def vp001000110011_0 : Blocks := edgeBlocks% "full/vectors/001000110011-V-0000.bin"
noncomputable def vp001000110011 : Blocks := vp001000110011_0
private theorem bp0010001100110 : Branch 0 (-1125761639/2000000 : ℚ) vp001000110011 := by
  apply branch_left_normalized (c:=vp0010001100110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1125761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1125761639/1000000 : ℚ) by norm_num]
  exact coverp0010001100110
private noncomputable def ep0010001100111_0 : Blocks := edgeBlocks% "full/vectors/0010001100111-E-0000.bin"
noncomputable def ep0010001100111 : Blocks := ep0010001100111_0
private theorem idp0010001100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000110011.list =
    C ((2:ℤ)^87) * horner X vp0010001100111.list + horner X ep0010001100111.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001100111 : Branch 1 (-1125761639/2000000 : ℚ) vp001000110011 := by
  apply branch_checked idp0010001100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1125761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1126761639/1000000 : ℚ) by norm_num]
  exact coverp0010001100111
theorem coverp001000110011 : Covers (-1125761639/2000000 : ℚ) vp001000110011 := join_branches bp0010001100110 bp0010001100111
private noncomputable def vp0010001100101_0 : Blocks := edgeBlocks% "full/vectors/0010001100101-V-0000.bin"
noncomputable def vp0010001100101 : Blocks := vp0010001100101_0
theorem coverp0010001100101 : Covers (-1124761639/1000000 : ℚ) vp0010001100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001100100_0 : Blocks := edgeBlocks% "full/vectors/0010001100100-V-0000.bin"
noncomputable def vp0010001100100 : Blocks := vp0010001100100_0
theorem coverp0010001100100 : Covers (-1123761639/1000000 : ℚ) vp0010001100100 := cover_leaf (by decide +kernel)
private noncomputable def vp001000110010_0 : Blocks := edgeBlocks% "full/vectors/001000110010-V-0000.bin"
noncomputable def vp001000110010 : Blocks := vp001000110010_0
private theorem bp0010001100100 : Branch 0 (-1123761639/2000000 : ℚ) vp001000110010 := by
  apply branch_left_normalized (c:=vp0010001100100) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1123761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1123761639/1000000 : ℚ) by norm_num]
  exact coverp0010001100100
private noncomputable def ep0010001100101_0 : Blocks := edgeBlocks% "full/vectors/0010001100101-E-0000.bin"
noncomputable def ep0010001100101 : Blocks := ep0010001100101_0
private theorem idp0010001100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000110010.list =
    C ((2:ℤ)^82) * horner X vp0010001100101.list + horner X ep0010001100101.list := by
  exact edge_identity (B := (2:ℤ)^208) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001100101 : Branch 1 (-1123761639/2000000 : ℚ) vp001000110010 := by
  apply branch_checked idp0010001100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1123761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1124761639/1000000 : ℚ) by norm_num]
  exact coverp0010001100101
theorem coverp001000110010 : Covers (-1123761639/2000000 : ℚ) vp001000110010 := join_branches bp0010001100100 bp0010001100101
private noncomputable def vp00100011001_0 : Blocks := edgeBlocks% "full/vectors/00100011001-V-0000.bin"
private noncomputable def vp00100011001_1 : Blocks := edgeBlocks% "full/vectors/00100011001-V-0001.bin"
noncomputable def vp00100011001 : Blocks := (Blocks.join vp00100011001_0 vp00100011001_1)
private theorem bp001000110010 : Branch 0 (-1123761639/4000000 : ℚ) vp00100011001 := by
  apply branch_left_normalized (c:=vp001000110010) (k:=0) (m:=78) (by decide +kernel)
  rw [show 2*(-1123761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1123761639/2000000 : ℚ) by norm_num]
  exact coverp001000110010
private noncomputable def ep001000110011_0 : Blocks := edgeBlocks% "full/vectors/001000110011-E-0000.bin"
private noncomputable def ep001000110011_1 : Blocks := edgeBlocks% "full/vectors/001000110011-E-0001.bin"
noncomputable def ep001000110011 : Blocks := (Blocks.join ep001000110011_0 ep001000110011_1)
private theorem idp001000110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100011001.list =
    C ((2:ℤ)^147) * horner X vp001000110011.list + horner X ep001000110011.list := by
  exact edge_identity (B := (2:ℤ)^297) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000110011 : Branch 1 (-1123761639/4000000 : ℚ) vp00100011001 := by
  apply branch_checked idp001000110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1123761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1125761639/2000000 : ℚ) by norm_num]
  exact coverp001000110011
theorem coverp00100011001 : Covers (-1123761639/4000000 : ℚ) vp00100011001 := join_branches bp001000110010 bp001000110011
private noncomputable def vp0010001100011_0 : Blocks := edgeBlocks% "full/vectors/0010001100011-V-0000.bin"
noncomputable def vp0010001100011 : Blocks := vp0010001100011_0
theorem coverp0010001100011 : Covers (-1122761639/1000000 : ℚ) vp0010001100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001100010_0 : Blocks := edgeBlocks% "full/vectors/0010001100010-V-0000.bin"
noncomputable def vp0010001100010 : Blocks := vp0010001100010_0
theorem coverp0010001100010 : Covers (-1121761639/1000000 : ℚ) vp0010001100010 := cover_leaf (by decide +kernel)
private noncomputable def vp001000110001_0 : Blocks := edgeBlocks% "full/vectors/001000110001-V-0000.bin"
noncomputable def vp001000110001 : Blocks := vp001000110001_0
private theorem bp0010001100010 : Branch 0 (-1121761639/2000000 : ℚ) vp001000110001 := by
  apply branch_left_normalized (c:=vp0010001100010) (k:=0) (m:=45) (by decide +kernel)
  rw [show 2*(-1121761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1121761639/1000000 : ℚ) by norm_num]
  exact coverp0010001100010
private noncomputable def ep0010001100011_0 : Blocks := edgeBlocks% "full/vectors/0010001100011-E-0000.bin"
noncomputable def ep0010001100011 : Blocks := ep0010001100011_0
private theorem idp0010001100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000110001.list =
    C ((2:ℤ)^83) * horner X vp0010001100011.list + horner X ep0010001100011.list := by
  exact edge_identity (B := (2:ℤ)^205) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001100011 : Branch 1 (-1121761639/2000000 : ℚ) vp001000110001 := by
  apply branch_checked idp0010001100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1121761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1122761639/1000000 : ℚ) by norm_num]
  exact coverp0010001100011
theorem coverp001000110001 : Covers (-1121761639/2000000 : ℚ) vp001000110001 := join_branches bp0010001100010 bp0010001100011
private noncomputable def vp0010001100001_0 : Blocks := edgeBlocks% "full/vectors/0010001100001-V-0000.bin"
noncomputable def vp0010001100001 : Blocks := vp0010001100001_0
theorem coverp0010001100001 : Covers (-1120761639/1000000 : ℚ) vp0010001100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001100000_0 : Blocks := edgeBlocks% "full/vectors/0010001100000-V-0000.bin"
noncomputable def vp0010001100000 : Blocks := vp0010001100000_0
theorem coverp0010001100000 : Covers (-1119761639/1000000 : ℚ) vp0010001100000 := cover_leaf (by decide +kernel)
private noncomputable def vp001000110000_0 : Blocks := edgeBlocks% "full/vectors/001000110000-V-0000.bin"
noncomputable def vp001000110000 : Blocks := vp001000110000_0
private theorem bp0010001100000 : Branch 0 (-1119761639/2000000 : ℚ) vp001000110000 := by
  apply branch_left_normalized (c:=vp0010001100000) (k:=0) (m:=46) (by decide +kernel)
  rw [show 2*(-1119761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1119761639/1000000 : ℚ) by norm_num]
  exact coverp0010001100000
private noncomputable def ep0010001100001_0 : Blocks := edgeBlocks% "full/vectors/0010001100001-E-0000.bin"
noncomputable def ep0010001100001 : Blocks := ep0010001100001_0
private theorem idp0010001100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000110000.list =
    C ((2:ℤ)^84) * horner X vp0010001100001.list + horner X ep0010001100001.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001100001 : Branch 1 (-1119761639/2000000 : ℚ) vp001000110000 := by
  apply branch_checked idp0010001100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1119761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1120761639/1000000 : ℚ) by norm_num]
  exact coverp0010001100001
theorem coverp001000110000 : Covers (-1119761639/2000000 : ℚ) vp001000110000 := join_branches bp0010001100000 bp0010001100001
private noncomputable def vp00100011000_0 : Blocks := edgeBlocks% "full/vectors/00100011000-V-0000.bin"
private noncomputable def vp00100011000_1 : Blocks := edgeBlocks% "full/vectors/00100011000-V-0001.bin"
noncomputable def vp00100011000 : Blocks := (Blocks.join vp00100011000_0 vp00100011000_1)
private theorem bp001000110000 : Branch 0 (-1119761639/4000000 : ℚ) vp00100011000 := by
  apply branch_left_normalized (c:=vp001000110000) (k:=0) (m:=77) (by decide +kernel)
  rw [show 2*(-1119761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1119761639/2000000 : ℚ) by norm_num]
  exact coverp001000110000
private noncomputable def ep001000110001_0 : Blocks := edgeBlocks% "full/vectors/001000110001-E-0000.bin"
private noncomputable def ep001000110001_1 : Blocks := edgeBlocks% "full/vectors/001000110001-E-0001.bin"
noncomputable def ep001000110001 : Blocks := (Blocks.join ep001000110001_0 ep001000110001_1)
private theorem idp001000110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100011000.list =
    C ((2:ℤ)^149) * horner X vp001000110001.list + horner X ep001000110001.list := by
  exact edge_identity (B := (2:ℤ)^296) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000110001 : Branch 1 (-1119761639/4000000 : ℚ) vp00100011000 := by
  apply branch_checked idp001000110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1119761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1121761639/2000000 : ℚ) by norm_num]
  exact coverp001000110001
theorem coverp00100011000 : Covers (-1119761639/4000000 : ℚ) vp00100011000 := join_branches bp001000110000 bp001000110001
private noncomputable def vp0010001100_0 : Blocks := edgeBlocks% "full/vectors/0010001100-V-0000.bin"
private noncomputable def vp0010001100_1 : Blocks := edgeBlocks% "full/vectors/0010001100-V-0001.bin"
noncomputable def vp0010001100 : Blocks := (Blocks.join vp0010001100_0 vp0010001100_1)
private theorem bp00100011000 : Branch 0 (-1119761639/8000000 : ℚ) vp0010001100 := by
  apply branch_left_normalized (c:=vp00100011000) (k:=0) (m:=136) (by decide +kernel)
  rw [show 2*(-1119761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1119761639/4000000 : ℚ) by norm_num]
  exact coverp00100011000
private noncomputable def ep00100011001_0 : Blocks := edgeBlocks% "full/vectors/00100011001-E-0000.bin"
private noncomputable def ep00100011001_1 : Blocks := edgeBlocks% "full/vectors/00100011001-E-0001.bin"
noncomputable def ep00100011001 : Blocks := (Blocks.join ep00100011001_0 ep00100011001_1)
private theorem idp00100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010001100.list =
    C ((2:ℤ)^276) * horner X vp00100011001.list + horner X ep00100011001.list := by
  exact edge_identity (B := (2:ℤ)^475) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100011001 : Branch 1 (-1119761639/8000000 : ℚ) vp0010001100 := by
  apply branch_checked idp00100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1119761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1123761639/4000000 : ℚ) by norm_num]
  exact coverp00100011001
theorem coverp0010001100 : Covers (-1119761639/8000000 : ℚ) vp0010001100 := join_branches bp00100011000 bp00100011001
private noncomputable def vp001000110_0 : Blocks := edgeBlocks% "full/vectors/001000110-V-0000.bin"
private noncomputable def vp001000110_1 : Blocks := edgeBlocks% "full/vectors/001000110-V-0001.bin"
private noncomputable def vp001000110_2 : Blocks := edgeBlocks% "full/vectors/001000110-V-0002.bin"
private noncomputable def vp001000110_3 : Blocks := edgeBlocks% "full/vectors/001000110-V-0003.bin"
noncomputable def vp001000110 : Blocks := (Blocks.join (Blocks.join vp001000110_0 vp001000110_1) (Blocks.join vp001000110_2 vp001000110_3))
private theorem bp0010001100 : Branch 0 (-1119761639/16000000 : ℚ) vp001000110 := by
  apply branch_left_normalized (c:=vp0010001100) (k:=0) (m:=253) (by decide +kernel)
  rw [show 2*(-1119761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1119761639/8000000 : ℚ) by norm_num]
  exact coverp0010001100
private noncomputable def ep0010001101_0 : Blocks := edgeBlocks% "full/vectors/0010001101-E-0000.bin"
private noncomputable def ep0010001101_1 : Blocks := edgeBlocks% "full/vectors/0010001101-E-0001.bin"
private noncomputable def ep0010001101_2 : Blocks := edgeBlocks% "full/vectors/0010001101-E-0002.bin"
private noncomputable def ep0010001101_3 : Blocks := edgeBlocks% "full/vectors/0010001101-E-0003.bin"
noncomputable def ep0010001101 : Blocks := (Blocks.join (Blocks.join ep0010001101_0 ep0010001101_1) (Blocks.join ep0010001101_2 ep0010001101_3))
private theorem idp0010001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000110.list =
    C ((2:ℤ)^535) * horner X vp0010001101.list + horner X ep0010001101.list := by
  exact edge_identity (B := (2:ℤ)^833) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001101 : Branch 1 (-1119761639/16000000 : ℚ) vp001000110 := by
  apply branch_checked idp0010001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1119761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1127761639/8000000 : ℚ) by norm_num]
  exact coverp0010001101
theorem coverp001000110 : Covers (-1119761639/16000000 : ℚ) vp001000110 := join_branches bp0010001100 bp0010001101
private noncomputable def vp00100011_0 : Blocks := edgeBlocks% "full/vectors/00100011-V-0000.bin"
private noncomputable def vp00100011_1 : Blocks := edgeBlocks% "full/vectors/00100011-V-0001.bin"
private noncomputable def vp00100011_2 : Blocks := edgeBlocks% "full/vectors/00100011-V-0002.bin"
private noncomputable def vp00100011_3 : Blocks := edgeBlocks% "full/vectors/00100011-V-0003.bin"
private noncomputable def vp00100011_4 : Blocks := edgeBlocks% "full/vectors/00100011-V-0004.bin"
private noncomputable def vp00100011_5 : Blocks := edgeBlocks% "full/vectors/00100011-V-0005.bin"
private noncomputable def vp00100011_6 : Blocks := edgeBlocks% "full/vectors/00100011-V-0006.bin"
private noncomputable def vp00100011_7 : Blocks := edgeBlocks% "full/vectors/00100011-V-0007.bin"
noncomputable def vp00100011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00100011_0 vp00100011_1) (Blocks.join vp00100011_2 vp00100011_3)) (Blocks.join (Blocks.join vp00100011_4 vp00100011_5) (Blocks.join vp00100011_6 vp00100011_7)))
private theorem bp001000110 : Branch 0 (-1119761639/32000000 : ℚ) vp00100011 := by
  apply branch_left_normalized (c:=vp001000110) (k:=0) (m:=486) (by decide +kernel)
  rw [show 2*(-1119761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1119761639/16000000 : ℚ) by norm_num]
  exact coverp001000110
private noncomputable def ep001000111_0 : Blocks := edgeBlocks% "full/vectors/001000111-E-0000.bin"
private noncomputable def ep001000111_1 : Blocks := edgeBlocks% "full/vectors/001000111-E-0001.bin"
private noncomputable def ep001000111_2 : Blocks := edgeBlocks% "full/vectors/001000111-E-0002.bin"
private noncomputable def ep001000111_3 : Blocks := edgeBlocks% "full/vectors/001000111-E-0003.bin"
private noncomputable def ep001000111_4 : Blocks := edgeBlocks% "full/vectors/001000111-E-0004.bin"
private noncomputable def ep001000111_5 : Blocks := edgeBlocks% "full/vectors/001000111-E-0005.bin"
private noncomputable def ep001000111_6 : Blocks := edgeBlocks% "full/vectors/001000111-E-0006.bin"
private noncomputable def ep001000111_7 : Blocks := edgeBlocks% "full/vectors/001000111-E-0007.bin"
noncomputable def ep001000111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep001000111_0 ep001000111_1) (Blocks.join ep001000111_2 ep001000111_3)) (Blocks.join (Blocks.join ep001000111_4 ep001000111_5) (Blocks.join ep001000111_6 ep001000111_7)))
private theorem idp001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100011.list =
    C ((2:ℤ)^1045) * horner X vp001000111.list + horner X ep001000111.list := by
  exact edge_identity (B := (2:ℤ)^1540) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000111 : Branch 1 (-1119761639/32000000 : ℚ) vp00100011 := by
  apply branch_checked idp001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1119761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1135761639/16000000 : ℚ) by norm_num]
  exact coverp001000111
theorem coverp00100011 : Covers (-1119761639/32000000 : ℚ) vp00100011 := join_branches bp001000110 bp001000111
private noncomputable def vp0010001011111_0 : Blocks := edgeBlocks% "full/vectors/0010001011111-V-0000.bin"
noncomputable def vp0010001011111 : Blocks := vp0010001011111_0
theorem coverp0010001011111 : Covers (-1118761639/1000000 : ℚ) vp0010001011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001011110_0 : Blocks := edgeBlocks% "full/vectors/0010001011110-V-0000.bin"
noncomputable def vp0010001011110 : Blocks := vp0010001011110_0
theorem coverp0010001011110 : Covers (-1117761639/1000000 : ℚ) vp0010001011110 := cover_leaf (by decide +kernel)
private noncomputable def vp001000101111_0 : Blocks := edgeBlocks% "full/vectors/001000101111-V-0000.bin"
noncomputable def vp001000101111 : Blocks := vp001000101111_0
private theorem bp0010001011110 : Branch 0 (-1117761639/2000000 : ℚ) vp001000101111 := by
  apply branch_left_normalized (c:=vp0010001011110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1117761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1117761639/1000000 : ℚ) by norm_num]
  exact coverp0010001011110
private noncomputable def ep0010001011111_0 : Blocks := edgeBlocks% "full/vectors/0010001011111-E-0000.bin"
noncomputable def ep0010001011111 : Blocks := ep0010001011111_0
private theorem idp0010001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000101111.list =
    C ((2:ℤ)^84) * horner X vp0010001011111.list + horner X ep0010001011111.list := by
  exact edge_identity (B := (2:ℤ)^206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001011111 : Branch 1 (-1117761639/2000000 : ℚ) vp001000101111 := by
  apply branch_checked idp0010001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1117761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1118761639/1000000 : ℚ) by norm_num]
  exact coverp0010001011111
theorem coverp001000101111 : Covers (-1117761639/2000000 : ℚ) vp001000101111 := join_branches bp0010001011110 bp0010001011111
private noncomputable def vp0010001011101_0 : Blocks := edgeBlocks% "full/vectors/0010001011101-V-0000.bin"
noncomputable def vp0010001011101 : Blocks := vp0010001011101_0
theorem coverp0010001011101 : Covers (-1116761639/1000000 : ℚ) vp0010001011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001011100_0 : Blocks := edgeBlocks% "full/vectors/0010001011100-V-0000.bin"
noncomputable def vp0010001011100 : Blocks := vp0010001011100_0
theorem coverp0010001011100 : Covers (-1115761639/1000000 : ℚ) vp0010001011100 := cover_leaf (by decide +kernel)
private noncomputable def vp001000101110_0 : Blocks := edgeBlocks% "full/vectors/001000101110-V-0000.bin"
noncomputable def vp001000101110 : Blocks := vp001000101110_0
private theorem bp0010001011100 : Branch 0 (-1115761639/2000000 : ℚ) vp001000101110 := by
  apply branch_left_normalized (c:=vp0010001011100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1115761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1115761639/1000000 : ℚ) by norm_num]
  exact coverp0010001011100
private noncomputable def ep0010001011101_0 : Blocks := edgeBlocks% "full/vectors/0010001011101-E-0000.bin"
noncomputable def ep0010001011101 : Blocks := ep0010001011101_0
private theorem idp0010001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000101110.list =
    C ((2:ℤ)^87) * horner X vp0010001011101.list + horner X ep0010001011101.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001011101 : Branch 1 (-1115761639/2000000 : ℚ) vp001000101110 := by
  apply branch_checked idp0010001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1115761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1116761639/1000000 : ℚ) by norm_num]
  exact coverp0010001011101
theorem coverp001000101110 : Covers (-1115761639/2000000 : ℚ) vp001000101110 := join_branches bp0010001011100 bp0010001011101
private noncomputable def vp00100010111_0 : Blocks := edgeBlocks% "full/vectors/00100010111-V-0000.bin"
private noncomputable def vp00100010111_1 : Blocks := edgeBlocks% "full/vectors/00100010111-V-0001.bin"
noncomputable def vp00100010111 : Blocks := (Blocks.join vp00100010111_0 vp00100010111_1)
private theorem bp001000101110 : Branch 0 (-1115761639/4000000 : ℚ) vp00100010111 := by
  apply branch_left_normalized (c:=vp001000101110) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-1115761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1115761639/2000000 : ℚ) by norm_num]
  exact coverp001000101110
private noncomputable def ep001000101111_0 : Blocks := edgeBlocks% "full/vectors/001000101111-E-0000.bin"
private noncomputable def ep001000101111_1 : Blocks := edgeBlocks% "full/vectors/001000101111-E-0001.bin"
noncomputable def ep001000101111 : Blocks := (Blocks.join ep001000101111_0 ep001000101111_1)
private theorem idp001000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100010111.list =
    C ((2:ℤ)^153) * horner X vp001000101111.list + horner X ep001000101111.list := by
  exact edge_identity (B := (2:ℤ)^301) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000101111 : Branch 1 (-1115761639/4000000 : ℚ) vp00100010111 := by
  apply branch_checked idp001000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1115761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1117761639/2000000 : ℚ) by norm_num]
  exact coverp001000101111
theorem coverp00100010111 : Covers (-1115761639/4000000 : ℚ) vp00100010111 := join_branches bp001000101110 bp001000101111
private noncomputable def vp0010001011011_0 : Blocks := edgeBlocks% "full/vectors/0010001011011-V-0000.bin"
noncomputable def vp0010001011011 : Blocks := vp0010001011011_0
theorem coverp0010001011011 : Covers (-1114761639/1000000 : ℚ) vp0010001011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001011010_0 : Blocks := edgeBlocks% "full/vectors/0010001011010-V-0000.bin"
noncomputable def vp0010001011010 : Blocks := vp0010001011010_0
theorem coverp0010001011010 : Covers (-1113761639/1000000 : ℚ) vp0010001011010 := cover_leaf (by decide +kernel)
private noncomputable def vp001000101101_0 : Blocks := edgeBlocks% "full/vectors/001000101101-V-0000.bin"
noncomputable def vp001000101101 : Blocks := vp001000101101_0
private theorem bp0010001011010 : Branch 0 (-1113761639/2000000 : ℚ) vp001000101101 := by
  apply branch_left_normalized (c:=vp0010001011010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1113761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1113761639/1000000 : ℚ) by norm_num]
  exact coverp0010001011010
private noncomputable def ep0010001011011_0 : Blocks := edgeBlocks% "full/vectors/0010001011011-E-0000.bin"
noncomputable def ep0010001011011 : Blocks := ep0010001011011_0
private theorem idp0010001011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000101101.list =
    C ((2:ℤ)^85) * horner X vp0010001011011.list + horner X ep0010001011011.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001011011 : Branch 1 (-1113761639/2000000 : ℚ) vp001000101101 := by
  apply branch_checked idp0010001011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1113761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1114761639/1000000 : ℚ) by norm_num]
  exact coverp0010001011011
theorem coverp001000101101 : Covers (-1113761639/2000000 : ℚ) vp001000101101 := join_branches bp0010001011010 bp0010001011011
private noncomputable def vp0010001011001_0 : Blocks := edgeBlocks% "full/vectors/0010001011001-V-0000.bin"
noncomputable def vp0010001011001 : Blocks := vp0010001011001_0
theorem coverp0010001011001 : Covers (-1112761639/1000000 : ℚ) vp0010001011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001011000_0 : Blocks := edgeBlocks% "full/vectors/0010001011000-V-0000.bin"
noncomputable def vp0010001011000 : Blocks := vp0010001011000_0
theorem coverp0010001011000 : Covers (-1111761639/1000000 : ℚ) vp0010001011000 := cover_leaf (by decide +kernel)
private noncomputable def vp001000101100_0 : Blocks := edgeBlocks% "full/vectors/001000101100-V-0000.bin"
noncomputable def vp001000101100 : Blocks := vp001000101100_0
private theorem bp0010001011000 : Branch 0 (-1111761639/2000000 : ℚ) vp001000101100 := by
  apply branch_left_normalized (c:=vp0010001011000) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1111761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1111761639/1000000 : ℚ) by norm_num]
  exact coverp0010001011000
private noncomputable def ep0010001011001_0 : Blocks := edgeBlocks% "full/vectors/0010001011001-E-0000.bin"
noncomputable def ep0010001011001 : Blocks := ep0010001011001_0
private theorem idp0010001011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000101100.list =
    C ((2:ℤ)^85) * horner X vp0010001011001.list + horner X ep0010001011001.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001011001 : Branch 1 (-1111761639/2000000 : ℚ) vp001000101100 := by
  apply branch_checked idp0010001011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1111761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1112761639/1000000 : ℚ) by norm_num]
  exact coverp0010001011001
theorem coverp001000101100 : Covers (-1111761639/2000000 : ℚ) vp001000101100 := join_branches bp0010001011000 bp0010001011001
private noncomputable def vp00100010110_0 : Blocks := edgeBlocks% "full/vectors/00100010110-V-0000.bin"
private noncomputable def vp00100010110_1 : Blocks := edgeBlocks% "full/vectors/00100010110-V-0001.bin"
noncomputable def vp00100010110 : Blocks := (Blocks.join vp00100010110_0 vp00100010110_1)
private theorem bp001000101100 : Branch 0 (-1111761639/4000000 : ℚ) vp00100010110 := by
  apply branch_left_normalized (c:=vp001000101100) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-1111761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1111761639/2000000 : ℚ) by norm_num]
  exact coverp001000101100
private noncomputable def ep001000101101_0 : Blocks := edgeBlocks% "full/vectors/001000101101-E-0000.bin"
private noncomputable def ep001000101101_1 : Blocks := edgeBlocks% "full/vectors/001000101101-E-0001.bin"
noncomputable def ep001000101101 : Blocks := (Blocks.join ep001000101101_0 ep001000101101_1)
private theorem idp001000101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100010110.list =
    C ((2:ℤ)^150) * horner X vp001000101101.list + horner X ep001000101101.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000101101 : Branch 1 (-1111761639/4000000 : ℚ) vp00100010110 := by
  apply branch_checked idp001000101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1111761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1113761639/2000000 : ℚ) by norm_num]
  exact coverp001000101101
theorem coverp00100010110 : Covers (-1111761639/4000000 : ℚ) vp00100010110 := join_branches bp001000101100 bp001000101101
private noncomputable def vp0010001011_0 : Blocks := edgeBlocks% "full/vectors/0010001011-V-0000.bin"
private noncomputable def vp0010001011_1 : Blocks := edgeBlocks% "full/vectors/0010001011-V-0001.bin"
private noncomputable def vp0010001011_2 : Blocks := edgeBlocks% "full/vectors/0010001011-V-0002.bin"
noncomputable def vp0010001011 : Blocks := (Blocks.join vp0010001011_0 (Blocks.join vp0010001011_1 vp0010001011_2))
private theorem bp00100010110 : Branch 0 (-1111761639/8000000 : ℚ) vp0010001011 := by
  apply branch_left_normalized (c:=vp00100010110) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-1111761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1111761639/4000000 : ℚ) by norm_num]
  exact coverp00100010110
private noncomputable def ep00100010111_0 : Blocks := edgeBlocks% "full/vectors/00100010111-E-0000.bin"
private noncomputable def ep00100010111_1 : Blocks := edgeBlocks% "full/vectors/00100010111-E-0001.bin"
private noncomputable def ep00100010111_2 : Blocks := edgeBlocks% "full/vectors/00100010111-E-0002.bin"
noncomputable def ep00100010111 : Blocks := (Blocks.join ep00100010111_0 (Blocks.join ep00100010111_1 ep00100010111_2))
private theorem idp00100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010001011.list =
    C ((2:ℤ)^281) * horner X vp00100010111.list + horner X ep00100010111.list := by
  exact edge_identity (B := (2:ℤ)^483) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100010111 : Branch 1 (-1111761639/8000000 : ℚ) vp0010001011 := by
  apply branch_checked idp00100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1111761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1115761639/4000000 : ℚ) by norm_num]
  exact coverp00100010111
theorem coverp0010001011 : Covers (-1111761639/8000000 : ℚ) vp0010001011 := join_branches bp00100010110 bp00100010111
private noncomputable def vp0010001010111_0 : Blocks := edgeBlocks% "full/vectors/0010001010111-V-0000.bin"
noncomputable def vp0010001010111 : Blocks := vp0010001010111_0
theorem coverp0010001010111 : Covers (-1110761639/1000000 : ℚ) vp0010001010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001010110_0 : Blocks := edgeBlocks% "full/vectors/0010001010110-V-0000.bin"
noncomputable def vp0010001010110 : Blocks := vp0010001010110_0
theorem coverp0010001010110 : Covers (-1109761639/1000000 : ℚ) vp0010001010110 := cover_leaf (by decide +kernel)
private noncomputable def vp001000101011_0 : Blocks := edgeBlocks% "full/vectors/001000101011-V-0000.bin"
noncomputable def vp001000101011 : Blocks := vp001000101011_0
private theorem bp0010001010110 : Branch 0 (-1109761639/2000000 : ℚ) vp001000101011 := by
  apply branch_left_normalized (c:=vp0010001010110) (k:=0) (m:=47) (by decide +kernel)
  rw [show 2*(-1109761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1109761639/1000000 : ℚ) by norm_num]
  exact coverp0010001010110
private noncomputable def ep0010001010111_0 : Blocks := edgeBlocks% "full/vectors/0010001010111-E-0000.bin"
noncomputable def ep0010001010111 : Blocks := ep0010001010111_0
private theorem idp0010001010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000101011.list =
    C ((2:ℤ)^85) * horner X vp0010001010111.list + horner X ep0010001010111.list := by
  exact edge_identity (B := (2:ℤ)^209) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001010111 : Branch 1 (-1109761639/2000000 : ℚ) vp001000101011 := by
  apply branch_checked idp0010001010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1109761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1110761639/1000000 : ℚ) by norm_num]
  exact coverp0010001010111
theorem coverp001000101011 : Covers (-1109761639/2000000 : ℚ) vp001000101011 := join_branches bp0010001010110 bp0010001010111
private noncomputable def vp0010001010101_0 : Blocks := edgeBlocks% "full/vectors/0010001010101-V-0000.bin"
noncomputable def vp0010001010101 : Blocks := vp0010001010101_0
theorem coverp0010001010101 : Covers (-1108761639/1000000 : ℚ) vp0010001010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001010100_0 : Blocks := edgeBlocks% "full/vectors/0010001010100-V-0000.bin"
noncomputable def vp0010001010100 : Blocks := vp0010001010100_0
theorem coverp0010001010100 : Covers (-1107761639/1000000 : ℚ) vp0010001010100 := cover_leaf (by decide +kernel)
private noncomputable def vp001000101010_0 : Blocks := edgeBlocks% "full/vectors/001000101010-V-0000.bin"
noncomputable def vp001000101010 : Blocks := vp001000101010_0
private theorem bp0010001010100 : Branch 0 (-1107761639/2000000 : ℚ) vp001000101010 := by
  apply branch_left_normalized (c:=vp0010001010100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1107761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1107761639/1000000 : ℚ) by norm_num]
  exact coverp0010001010100
private noncomputable def ep0010001010101_0 : Blocks := edgeBlocks% "full/vectors/0010001010101-E-0000.bin"
noncomputable def ep0010001010101 : Blocks := ep0010001010101_0
private theorem idp0010001010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000101010.list =
    C ((2:ℤ)^86) * horner X vp0010001010101.list + horner X ep0010001010101.list := by
  exact edge_identity (B := (2:ℤ)^211) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001010101 : Branch 1 (-1107761639/2000000 : ℚ) vp001000101010 := by
  apply branch_checked idp0010001010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1107761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1108761639/1000000 : ℚ) by norm_num]
  exact coverp0010001010101
theorem coverp001000101010 : Covers (-1107761639/2000000 : ℚ) vp001000101010 := join_branches bp0010001010100 bp0010001010101
private noncomputable def vp00100010101_0 : Blocks := edgeBlocks% "full/vectors/00100010101-V-0000.bin"
private noncomputable def vp00100010101_1 : Blocks := edgeBlocks% "full/vectors/00100010101-V-0001.bin"
noncomputable def vp00100010101 : Blocks := (Blocks.join vp00100010101_0 vp00100010101_1)
private theorem bp001000101010 : Branch 0 (-1107761639/4000000 : ℚ) vp00100010101 := by
  apply branch_left_normalized (c:=vp001000101010) (k:=0) (m:=79) (by decide +kernel)
  rw [show 2*(-1107761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1107761639/2000000 : ℚ) by norm_num]
  exact coverp001000101010
private noncomputable def ep001000101011_0 : Blocks := edgeBlocks% "full/vectors/001000101011-E-0000.bin"
private noncomputable def ep001000101011_1 : Blocks := edgeBlocks% "full/vectors/001000101011-E-0001.bin"
noncomputable def ep001000101011 : Blocks := (Blocks.join ep001000101011_0 ep001000101011_1)
private theorem idp001000101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100010101.list =
    C ((2:ℤ)^152) * horner X vp001000101011.list + horner X ep001000101011.list := by
  exact edge_identity (B := (2:ℤ)^302) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000101011 : Branch 1 (-1107761639/4000000 : ℚ) vp00100010101 := by
  apply branch_checked idp001000101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1107761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1109761639/2000000 : ℚ) by norm_num]
  exact coverp001000101011
theorem coverp00100010101 : Covers (-1107761639/4000000 : ℚ) vp00100010101 := join_branches bp001000101010 bp001000101011
private noncomputable def vp0010001010011_0 : Blocks := edgeBlocks% "full/vectors/0010001010011-V-0000.bin"
noncomputable def vp0010001010011 : Blocks := vp0010001010011_0
theorem coverp0010001010011 : Covers (-1106761639/1000000 : ℚ) vp0010001010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001010010_0 : Blocks := edgeBlocks% "full/vectors/0010001010010-V-0000.bin"
noncomputable def vp0010001010010 : Blocks := vp0010001010010_0
theorem coverp0010001010010 : Covers (-1105761639/1000000 : ℚ) vp0010001010010 := cover_leaf (by decide +kernel)
private noncomputable def vp001000101001_0 : Blocks := edgeBlocks% "full/vectors/001000101001-V-0000.bin"
noncomputable def vp001000101001 : Blocks := vp001000101001_0
private theorem bp0010001010010 : Branch 0 (-1105761639/2000000 : ℚ) vp001000101001 := by
  apply branch_left_normalized (c:=vp0010001010010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1105761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1105761639/1000000 : ℚ) by norm_num]
  exact coverp0010001010010
private noncomputable def ep0010001010011_0 : Blocks := edgeBlocks% "full/vectors/0010001010011-E-0000.bin"
noncomputable def ep0010001010011 : Blocks := ep0010001010011_0
private theorem idp0010001010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000101001.list =
    C ((2:ℤ)^87) * horner X vp0010001010011.list + horner X ep0010001010011.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001010011 : Branch 1 (-1105761639/2000000 : ℚ) vp001000101001 := by
  apply branch_checked idp0010001010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1105761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1106761639/1000000 : ℚ) by norm_num]
  exact coverp0010001010011
theorem coverp001000101001 : Covers (-1105761639/2000000 : ℚ) vp001000101001 := join_branches bp0010001010010 bp0010001010011
private noncomputable def vp0010001010001_0 : Blocks := edgeBlocks% "full/vectors/0010001010001-V-0000.bin"
noncomputable def vp0010001010001 : Blocks := vp0010001010001_0
theorem coverp0010001010001 : Covers (-1104761639/1000000 : ℚ) vp0010001010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001010000_0 : Blocks := edgeBlocks% "full/vectors/0010001010000-V-0000.bin"
noncomputable def vp0010001010000 : Blocks := vp0010001010000_0
theorem coverp0010001010000 : Covers (-1103761639/1000000 : ℚ) vp0010001010000 := cover_leaf (by decide +kernel)
private noncomputable def vp001000101000_0 : Blocks := edgeBlocks% "full/vectors/001000101000-V-0000.bin"
noncomputable def vp001000101000 : Blocks := vp001000101000_0
private theorem bp0010001010000 : Branch 0 (-1103761639/2000000 : ℚ) vp001000101000 := by
  apply branch_left_normalized (c:=vp0010001010000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1103761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1103761639/1000000 : ℚ) by norm_num]
  exact coverp0010001010000
private noncomputable def ep0010001010001_0 : Blocks := edgeBlocks% "full/vectors/0010001010001-E-0000.bin"
noncomputable def ep0010001010001 : Blocks := ep0010001010001_0
private theorem idp0010001010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000101000.list =
    C ((2:ℤ)^87) * horner X vp0010001010001.list + horner X ep0010001010001.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001010001 : Branch 1 (-1103761639/2000000 : ℚ) vp001000101000 := by
  apply branch_checked idp0010001010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1103761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1104761639/1000000 : ℚ) by norm_num]
  exact coverp0010001010001
theorem coverp001000101000 : Covers (-1103761639/2000000 : ℚ) vp001000101000 := join_branches bp0010001010000 bp0010001010001
private noncomputable def vp00100010100_0 : Blocks := edgeBlocks% "full/vectors/00100010100-V-0000.bin"
private noncomputable def vp00100010100_1 : Blocks := edgeBlocks% "full/vectors/00100010100-V-0001.bin"
noncomputable def vp00100010100 : Blocks := (Blocks.join vp00100010100_0 vp00100010100_1)
private theorem bp001000101000 : Branch 0 (-1103761639/4000000 : ℚ) vp00100010100 := by
  apply branch_left_normalized (c:=vp001000101000) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-1103761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1103761639/2000000 : ℚ) by norm_num]
  exact coverp001000101000
private noncomputable def ep001000101001_0 : Blocks := edgeBlocks% "full/vectors/001000101001-E-0000.bin"
private noncomputable def ep001000101001_1 : Blocks := edgeBlocks% "full/vectors/001000101001-E-0001.bin"
noncomputable def ep001000101001 : Blocks := (Blocks.join ep001000101001_0 ep001000101001_1)
private theorem idp001000101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100010100.list =
    C ((2:ℤ)^152) * horner X vp001000101001.list + horner X ep001000101001.list := by
  exact edge_identity (B := (2:ℤ)^304) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000101001 : Branch 1 (-1103761639/4000000 : ℚ) vp00100010100 := by
  apply branch_checked idp001000101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1103761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1105761639/2000000 : ℚ) by norm_num]
  exact coverp001000101001
theorem coverp00100010100 : Covers (-1103761639/4000000 : ℚ) vp00100010100 := join_branches bp001000101000 bp001000101001
private noncomputable def vp0010001010_0 : Blocks := edgeBlocks% "full/vectors/0010001010-V-0000.bin"
private noncomputable def vp0010001010_1 : Blocks := edgeBlocks% "full/vectors/0010001010-V-0001.bin"
private noncomputable def vp0010001010_2 : Blocks := edgeBlocks% "full/vectors/0010001010-V-0002.bin"
noncomputable def vp0010001010 : Blocks := (Blocks.join vp0010001010_0 (Blocks.join vp0010001010_1 vp0010001010_2))
private theorem bp00100010100 : Branch 0 (-1103761639/8000000 : ℚ) vp0010001010 := by
  apply branch_left_normalized (c:=vp00100010100) (k:=0) (m:=139) (by decide +kernel)
  rw [show 2*(-1103761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1103761639/4000000 : ℚ) by norm_num]
  exact coverp00100010100
private noncomputable def ep00100010101_0 : Blocks := edgeBlocks% "full/vectors/00100010101-E-0000.bin"
private noncomputable def ep00100010101_1 : Blocks := edgeBlocks% "full/vectors/00100010101-E-0001.bin"
private noncomputable def ep00100010101_2 : Blocks := edgeBlocks% "full/vectors/00100010101-E-0002.bin"
noncomputable def ep00100010101 : Blocks := (Blocks.join ep00100010101_0 (Blocks.join ep00100010101_1 ep00100010101_2))
private theorem idp00100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010001010.list =
    C ((2:ℤ)^284) * horner X vp00100010101.list + horner X ep00100010101.list := by
  exact edge_identity (B := (2:ℤ)^486) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100010101 : Branch 1 (-1103761639/8000000 : ℚ) vp0010001010 := by
  apply branch_checked idp00100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1103761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1107761639/4000000 : ℚ) by norm_num]
  exact coverp00100010101
theorem coverp0010001010 : Covers (-1103761639/8000000 : ℚ) vp0010001010 := join_branches bp00100010100 bp00100010101
private noncomputable def vp001000101_0 : Blocks := edgeBlocks% "full/vectors/001000101-V-0000.bin"
private noncomputable def vp001000101_1 : Blocks := edgeBlocks% "full/vectors/001000101-V-0001.bin"
private noncomputable def vp001000101_2 : Blocks := edgeBlocks% "full/vectors/001000101-V-0002.bin"
private noncomputable def vp001000101_3 : Blocks := edgeBlocks% "full/vectors/001000101-V-0003.bin"
noncomputable def vp001000101 : Blocks := (Blocks.join (Blocks.join vp001000101_0 vp001000101_1) (Blocks.join vp001000101_2 vp001000101_3))
private theorem bp0010001010 : Branch 0 (-1103761639/16000000 : ℚ) vp001000101 := by
  apply branch_left_normalized (c:=vp0010001010) (k:=0) (m:=258) (by decide +kernel)
  rw [show 2*(-1103761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1103761639/8000000 : ℚ) by norm_num]
  exact coverp0010001010
private noncomputable def ep0010001011_0 : Blocks := edgeBlocks% "full/vectors/0010001011-E-0000.bin"
private noncomputable def ep0010001011_1 : Blocks := edgeBlocks% "full/vectors/0010001011-E-0001.bin"
private noncomputable def ep0010001011_2 : Blocks := edgeBlocks% "full/vectors/0010001011-E-0002.bin"
private noncomputable def ep0010001011_3 : Blocks := edgeBlocks% "full/vectors/0010001011-E-0003.bin"
noncomputable def ep0010001011 : Blocks := (Blocks.join (Blocks.join ep0010001011_0 ep0010001011_1) (Blocks.join ep0010001011_2 ep0010001011_3))
private theorem idp0010001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000101.list =
    C ((2:ℤ)^542) * horner X vp0010001011.list + horner X ep0010001011.list := by
  exact edge_identity (B := (2:ℤ)^846) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001011 : Branch 1 (-1103761639/16000000 : ℚ) vp001000101 := by
  apply branch_checked idp0010001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1103761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1111761639/8000000 : ℚ) by norm_num]
  exact coverp0010001011
theorem coverp001000101 : Covers (-1103761639/16000000 : ℚ) vp001000101 := join_branches bp0010001010 bp0010001011
private noncomputable def vp0010001001111_0 : Blocks := edgeBlocks% "full/vectors/0010001001111-V-0000.bin"
noncomputable def vp0010001001111 : Blocks := vp0010001001111_0
theorem coverp0010001001111 : Covers (-1102761639/1000000 : ℚ) vp0010001001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001001110_0 : Blocks := edgeBlocks% "full/vectors/0010001001110-V-0000.bin"
noncomputable def vp0010001001110 : Blocks := vp0010001001110_0
theorem coverp0010001001110 : Covers (-1101761639/1000000 : ℚ) vp0010001001110 := cover_leaf (by decide +kernel)
private noncomputable def vp001000100111_0 : Blocks := edgeBlocks% "full/vectors/001000100111-V-0000.bin"
noncomputable def vp001000100111 : Blocks := vp001000100111_0
private theorem bp0010001001110 : Branch 0 (-1101761639/2000000 : ℚ) vp001000100111 := by
  apply branch_left_normalized (c:=vp0010001001110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1101761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1101761639/1000000 : ℚ) by norm_num]
  exact coverp0010001001110
private noncomputable def ep0010001001111_0 : Blocks := edgeBlocks% "full/vectors/0010001001111-E-0000.bin"
noncomputable def ep0010001001111 : Blocks := ep0010001001111_0
private theorem idp0010001001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000100111.list =
    C ((2:ℤ)^86) * horner X vp0010001001111.list + horner X ep0010001001111.list := by
  exact edge_identity (B := (2:ℤ)^212) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001001111 : Branch 1 (-1101761639/2000000 : ℚ) vp001000100111 := by
  apply branch_checked idp0010001001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1101761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1102761639/1000000 : ℚ) by norm_num]
  exact coverp0010001001111
theorem coverp001000100111 : Covers (-1101761639/2000000 : ℚ) vp001000100111 := join_branches bp0010001001110 bp0010001001111
private noncomputable def vp0010001001101_0 : Blocks := edgeBlocks% "full/vectors/0010001001101-V-0000.bin"
noncomputable def vp0010001001101 : Blocks := vp0010001001101_0
theorem coverp0010001001101 : Covers (-1100761639/1000000 : ℚ) vp0010001001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001001100_0 : Blocks := edgeBlocks% "full/vectors/0010001001100-V-0000.bin"
noncomputable def vp0010001001100 : Blocks := vp0010001001100_0
theorem coverp0010001001100 : Covers (-1099761639/1000000 : ℚ) vp0010001001100 := cover_leaf (by decide +kernel)
private noncomputable def vp001000100110_0 : Blocks := edgeBlocks% "full/vectors/001000100110-V-0000.bin"
noncomputable def vp001000100110 : Blocks := vp001000100110_0
private theorem bp0010001001100 : Branch 0 (-1099761639/2000000 : ℚ) vp001000100110 := by
  apply branch_left_normalized (c:=vp0010001001100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1099761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1099761639/1000000 : ℚ) by norm_num]
  exact coverp0010001001100
private noncomputable def ep0010001001101_0 : Blocks := edgeBlocks% "full/vectors/0010001001101-E-0000.bin"
noncomputable def ep0010001001101 : Blocks := ep0010001001101_0
private theorem idp0010001001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000100110.list =
    C ((2:ℤ)^87) * horner X vp0010001001101.list + horner X ep0010001001101.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001001101 : Branch 1 (-1099761639/2000000 : ℚ) vp001000100110 := by
  apply branch_checked idp0010001001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1099761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1100761639/1000000 : ℚ) by norm_num]
  exact coverp0010001001101
theorem coverp001000100110 : Covers (-1099761639/2000000 : ℚ) vp001000100110 := join_branches bp0010001001100 bp0010001001101
private noncomputable def vp00100010011_0 : Blocks := edgeBlocks% "full/vectors/00100010011-V-0000.bin"
private noncomputable def vp00100010011_1 : Blocks := edgeBlocks% "full/vectors/00100010011-V-0001.bin"
noncomputable def vp00100010011 : Blocks := (Blocks.join vp00100010011_0 vp00100010011_1)
private theorem bp001000100110 : Branch 0 (-1099761639/4000000 : ℚ) vp00100010011 := by
  apply branch_left_normalized (c:=vp001000100110) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-1099761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1099761639/2000000 : ℚ) by norm_num]
  exact coverp001000100110
private noncomputable def ep001000100111_0 : Blocks := edgeBlocks% "full/vectors/001000100111-E-0000.bin"
private noncomputable def ep001000100111_1 : Blocks := edgeBlocks% "full/vectors/001000100111-E-0001.bin"
noncomputable def ep001000100111 : Blocks := (Blocks.join ep001000100111_0 ep001000100111_1)
private theorem idp001000100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100010011.list =
    C ((2:ℤ)^152) * horner X vp001000100111.list + horner X ep001000100111.list := by
  exact edge_identity (B := (2:ℤ)^304) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000100111 : Branch 1 (-1099761639/4000000 : ℚ) vp00100010011 := by
  apply branch_checked idp001000100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1099761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1101761639/2000000 : ℚ) by norm_num]
  exact coverp001000100111
theorem coverp00100010011 : Covers (-1099761639/4000000 : ℚ) vp00100010011 := join_branches bp001000100110 bp001000100111
private noncomputable def vp0010001001011_0 : Blocks := edgeBlocks% "full/vectors/0010001001011-V-0000.bin"
noncomputable def vp0010001001011 : Blocks := vp0010001001011_0
theorem coverp0010001001011 : Covers (-1098761639/1000000 : ℚ) vp0010001001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001001010_0 : Blocks := edgeBlocks% "full/vectors/0010001001010-V-0000.bin"
noncomputable def vp0010001001010 : Blocks := vp0010001001010_0
theorem coverp0010001001010 : Covers (-1097761639/1000000 : ℚ) vp0010001001010 := cover_leaf (by decide +kernel)
private noncomputable def vp001000100101_0 : Blocks := edgeBlocks% "full/vectors/001000100101-V-0000.bin"
noncomputable def vp001000100101 : Blocks := vp001000100101_0
private theorem bp0010001001010 : Branch 0 (-1097761639/2000000 : ℚ) vp001000100101 := by
  apply branch_left_normalized (c:=vp0010001001010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1097761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1097761639/1000000 : ℚ) by norm_num]
  exact coverp0010001001010
private noncomputable def ep0010001001011_0 : Blocks := edgeBlocks% "full/vectors/0010001001011-E-0000.bin"
noncomputable def ep0010001001011 : Blocks := ep0010001001011_0
private theorem idp0010001001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000100101.list =
    C ((2:ℤ)^88) * horner X vp0010001001011.list + horner X ep0010001001011.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001001011 : Branch 1 (-1097761639/2000000 : ℚ) vp001000100101 := by
  apply branch_checked idp0010001001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1097761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1098761639/1000000 : ℚ) by norm_num]
  exact coverp0010001001011
theorem coverp001000100101 : Covers (-1097761639/2000000 : ℚ) vp001000100101 := join_branches bp0010001001010 bp0010001001011
private noncomputable def vp0010001001001_0 : Blocks := edgeBlocks% "full/vectors/0010001001001-V-0000.bin"
noncomputable def vp0010001001001 : Blocks := vp0010001001001_0
theorem coverp0010001001001 : Covers (-1096761639/1000000 : ℚ) vp0010001001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001001000_0 : Blocks := edgeBlocks% "full/vectors/0010001001000-V-0000.bin"
noncomputable def vp0010001001000 : Blocks := vp0010001001000_0
theorem coverp0010001001000 : Covers (-1095761639/1000000 : ℚ) vp0010001001000 := cover_leaf (by decide +kernel)
private noncomputable def vp001000100100_0 : Blocks := edgeBlocks% "full/vectors/001000100100-V-0000.bin"
noncomputable def vp001000100100 : Blocks := vp001000100100_0
private theorem bp0010001001000 : Branch 0 (-1095761639/2000000 : ℚ) vp001000100100 := by
  apply branch_left_normalized (c:=vp0010001001000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1095761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1095761639/1000000 : ℚ) by norm_num]
  exact coverp0010001001000
private noncomputable def ep0010001001001_0 : Blocks := edgeBlocks% "full/vectors/0010001001001-E-0000.bin"
noncomputable def ep0010001001001 : Blocks := ep0010001001001_0
private theorem idp0010001001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000100100.list =
    C ((2:ℤ)^86) * horner X vp0010001001001.list + horner X ep0010001001001.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001001001 : Branch 1 (-1095761639/2000000 : ℚ) vp001000100100 := by
  apply branch_checked idp0010001001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1095761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1096761639/1000000 : ℚ) by norm_num]
  exact coverp0010001001001
theorem coverp001000100100 : Covers (-1095761639/2000000 : ℚ) vp001000100100 := join_branches bp0010001001000 bp0010001001001
private noncomputable def vp00100010010_0 : Blocks := edgeBlocks% "full/vectors/00100010010-V-0000.bin"
private noncomputable def vp00100010010_1 : Blocks := edgeBlocks% "full/vectors/00100010010-V-0001.bin"
noncomputable def vp00100010010 : Blocks := (Blocks.join vp00100010010_0 vp00100010010_1)
private theorem bp001000100100 : Branch 0 (-1095761639/4000000 : ℚ) vp00100010010 := by
  apply branch_left_normalized (c:=vp001000100100) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-1095761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1095761639/2000000 : ℚ) by norm_num]
  exact coverp001000100100
private noncomputable def ep001000100101_0 : Blocks := edgeBlocks% "full/vectors/001000100101-E-0000.bin"
private noncomputable def ep001000100101_1 : Blocks := edgeBlocks% "full/vectors/001000100101-E-0001.bin"
noncomputable def ep001000100101 : Blocks := (Blocks.join ep001000100101_0 ep001000100101_1)
private theorem idp001000100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100010010.list =
    C ((2:ℤ)^153) * horner X vp001000100101.list + horner X ep001000100101.list := by
  exact edge_identity (B := (2:ℤ)^306) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000100101 : Branch 1 (-1095761639/4000000 : ℚ) vp00100010010 := by
  apply branch_checked idp001000100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1095761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1097761639/2000000 : ℚ) by norm_num]
  exact coverp001000100101
theorem coverp00100010010 : Covers (-1095761639/4000000 : ℚ) vp00100010010 := join_branches bp001000100100 bp001000100101
private noncomputable def vp0010001001_0 : Blocks := edgeBlocks% "full/vectors/0010001001-V-0000.bin"
private noncomputable def vp0010001001_1 : Blocks := edgeBlocks% "full/vectors/0010001001-V-0001.bin"
private noncomputable def vp0010001001_2 : Blocks := edgeBlocks% "full/vectors/0010001001-V-0002.bin"
noncomputable def vp0010001001 : Blocks := (Blocks.join vp0010001001_0 (Blocks.join vp0010001001_1 vp0010001001_2))
private theorem bp00100010010 : Branch 0 (-1095761639/8000000 : ℚ) vp0010001001 := by
  apply branch_left_normalized (c:=vp00100010010) (k:=0) (m:=141) (by decide +kernel)
  rw [show 2*(-1095761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1095761639/4000000 : ℚ) by norm_num]
  exact coverp00100010010
private noncomputable def ep00100010011_0 : Blocks := edgeBlocks% "full/vectors/00100010011-E-0000.bin"
private noncomputable def ep00100010011_1 : Blocks := edgeBlocks% "full/vectors/00100010011-E-0001.bin"
private noncomputable def ep00100010011_2 : Blocks := edgeBlocks% "full/vectors/00100010011-E-0002.bin"
noncomputable def ep00100010011 : Blocks := (Blocks.join ep00100010011_0 (Blocks.join ep00100010011_1 ep00100010011_2))
private theorem idp00100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010001001.list =
    C ((2:ℤ)^284) * horner X vp00100010011.list + horner X ep00100010011.list := by
  exact edge_identity (B := (2:ℤ)^487) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100010011 : Branch 1 (-1095761639/8000000 : ℚ) vp0010001001 := by
  apply branch_checked idp00100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1095761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1099761639/4000000 : ℚ) by norm_num]
  exact coverp00100010011
theorem coverp0010001001 : Covers (-1095761639/8000000 : ℚ) vp0010001001 := join_branches bp00100010010 bp00100010011
private noncomputable def vp0010001000111_0 : Blocks := edgeBlocks% "full/vectors/0010001000111-V-0000.bin"
noncomputable def vp0010001000111 : Blocks := vp0010001000111_0
theorem coverp0010001000111 : Covers (-1094761639/1000000 : ℚ) vp0010001000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001000110_0 : Blocks := edgeBlocks% "full/vectors/0010001000110-V-0000.bin"
noncomputable def vp0010001000110 : Blocks := vp0010001000110_0
theorem coverp0010001000110 : Covers (-1093761639/1000000 : ℚ) vp0010001000110 := cover_leaf (by decide +kernel)
private noncomputable def vp001000100011_0 : Blocks := edgeBlocks% "full/vectors/001000100011-V-0000.bin"
noncomputable def vp001000100011 : Blocks := vp001000100011_0
private theorem bp0010001000110 : Branch 0 (-1093761639/2000000 : ℚ) vp001000100011 := by
  apply branch_left_normalized (c:=vp0010001000110) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1093761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1093761639/1000000 : ℚ) by norm_num]
  exact coverp0010001000110
private noncomputable def ep0010001000111_0 : Blocks := edgeBlocks% "full/vectors/0010001000111-E-0000.bin"
noncomputable def ep0010001000111 : Blocks := ep0010001000111_0
private theorem idp0010001000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000100011.list =
    C ((2:ℤ)^86) * horner X vp0010001000111.list + horner X ep0010001000111.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001000111 : Branch 1 (-1093761639/2000000 : ℚ) vp001000100011 := by
  apply branch_checked idp0010001000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1093761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1094761639/1000000 : ℚ) by norm_num]
  exact coverp0010001000111
theorem coverp001000100011 : Covers (-1093761639/2000000 : ℚ) vp001000100011 := join_branches bp0010001000110 bp0010001000111
private noncomputable def vp0010001000101_0 : Blocks := edgeBlocks% "full/vectors/0010001000101-V-0000.bin"
noncomputable def vp0010001000101 : Blocks := vp0010001000101_0
theorem coverp0010001000101 : Covers (-1092761639/1000000 : ℚ) vp0010001000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001000100_0 : Blocks := edgeBlocks% "full/vectors/0010001000100-V-0000.bin"
noncomputable def vp0010001000100 : Blocks := vp0010001000100_0
theorem coverp0010001000100 : Covers (-1091761639/1000000 : ℚ) vp0010001000100 := cover_leaf (by decide +kernel)
private noncomputable def vp001000100010_0 : Blocks := edgeBlocks% "full/vectors/001000100010-V-0000.bin"
noncomputable def vp001000100010 : Blocks := vp001000100010_0
private theorem bp0010001000100 : Branch 0 (-1091761639/2000000 : ℚ) vp001000100010 := by
  apply branch_left_normalized (c:=vp0010001000100) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1091761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1091761639/1000000 : ℚ) by norm_num]
  exact coverp0010001000100
private noncomputable def ep0010001000101_0 : Blocks := edgeBlocks% "full/vectors/0010001000101-E-0000.bin"
noncomputable def ep0010001000101 : Blocks := ep0010001000101_0
private theorem idp0010001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000100010.list =
    C ((2:ℤ)^87) * horner X vp0010001000101.list + horner X ep0010001000101.list := by
  exact edge_identity (B := (2:ℤ)^214) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001000101 : Branch 1 (-1091761639/2000000 : ℚ) vp001000100010 := by
  apply branch_checked idp0010001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1091761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1092761639/1000000 : ℚ) by norm_num]
  exact coverp0010001000101
theorem coverp001000100010 : Covers (-1091761639/2000000 : ℚ) vp001000100010 := join_branches bp0010001000100 bp0010001000101
private noncomputable def vp00100010001_0 : Blocks := edgeBlocks% "full/vectors/00100010001-V-0000.bin"
private noncomputable def vp00100010001_1 : Blocks := edgeBlocks% "full/vectors/00100010001-V-0001.bin"
noncomputable def vp00100010001 : Blocks := (Blocks.join vp00100010001_0 vp00100010001_1)
private theorem bp001000100010 : Branch 0 (-1091761639/4000000 : ℚ) vp00100010001 := by
  apply branch_left_normalized (c:=vp001000100010) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-1091761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1091761639/2000000 : ℚ) by norm_num]
  exact coverp001000100010
private noncomputable def ep001000100011_0 : Blocks := edgeBlocks% "full/vectors/001000100011-E-0000.bin"
private noncomputable def ep001000100011_1 : Blocks := edgeBlocks% "full/vectors/001000100011-E-0001.bin"
noncomputable def ep001000100011 : Blocks := (Blocks.join ep001000100011_0 ep001000100011_1)
private theorem idp001000100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100010001.list =
    C ((2:ℤ)^153) * horner X vp001000100011.list + horner X ep001000100011.list := by
  exact edge_identity (B := (2:ℤ)^305) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000100011 : Branch 1 (-1091761639/4000000 : ℚ) vp00100010001 := by
  apply branch_checked idp001000100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1091761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1093761639/2000000 : ℚ) by norm_num]
  exact coverp001000100011
theorem coverp00100010001 : Covers (-1091761639/4000000 : ℚ) vp00100010001 := join_branches bp001000100010 bp001000100011
private noncomputable def vp0010001000011_0 : Blocks := edgeBlocks% "full/vectors/0010001000011-V-0000.bin"
noncomputable def vp0010001000011 : Blocks := vp0010001000011_0
theorem coverp0010001000011 : Covers (-1090761639/1000000 : ℚ) vp0010001000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001000010_0 : Blocks := edgeBlocks% "full/vectors/0010001000010-V-0000.bin"
noncomputable def vp0010001000010 : Blocks := vp0010001000010_0
theorem coverp0010001000010 : Covers (-1089761639/1000000 : ℚ) vp0010001000010 := cover_leaf (by decide +kernel)
private noncomputable def vp001000100001_0 : Blocks := edgeBlocks% "full/vectors/001000100001-V-0000.bin"
noncomputable def vp001000100001 : Blocks := vp001000100001_0
private theorem bp0010001000010 : Branch 0 (-1089761639/2000000 : ℚ) vp001000100001 := by
  apply branch_left_normalized (c:=vp0010001000010) (k:=0) (m:=48) (by decide +kernel)
  rw [show 2*(-1089761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1089761639/1000000 : ℚ) by norm_num]
  exact coverp0010001000010
private noncomputable def ep0010001000011_0 : Blocks := edgeBlocks% "full/vectors/0010001000011-E-0000.bin"
noncomputable def ep0010001000011 : Blocks := ep0010001000011_0
private theorem idp0010001000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000100001.list =
    C ((2:ℤ)^87) * horner X vp0010001000011.list + horner X ep0010001000011.list := by
  exact edge_identity (B := (2:ℤ)^213) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001000011 : Branch 1 (-1089761639/2000000 : ℚ) vp001000100001 := by
  apply branch_checked idp0010001000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1089761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1090761639/1000000 : ℚ) by norm_num]
  exact coverp0010001000011
theorem coverp001000100001 : Covers (-1089761639/2000000 : ℚ) vp001000100001 := join_branches bp0010001000010 bp0010001000011
private noncomputable def vp0010001000001_0 : Blocks := edgeBlocks% "full/vectors/0010001000001-V-0000.bin"
noncomputable def vp0010001000001 : Blocks := vp0010001000001_0
theorem coverp0010001000001 : Covers (-1088761639/1000000 : ℚ) vp0010001000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0010001000000_0 : Blocks := edgeBlocks% "full/vectors/0010001000000-V-0000.bin"
noncomputable def vp0010001000000 : Blocks := vp0010001000000_0
theorem coverp0010001000000 : Covers (-1087761639/1000000 : ℚ) vp0010001000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001000100000_0 : Blocks := edgeBlocks% "full/vectors/001000100000-V-0000.bin"
noncomputable def vp001000100000 : Blocks := vp001000100000_0
private theorem bp0010001000000 : Branch 0 (-1087761639/2000000 : ℚ) vp001000100000 := by
  apply branch_left_normalized (c:=vp0010001000000) (k:=0) (m:=49) (by decide +kernel)
  rw [show 2*(-1087761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1087761639/1000000 : ℚ) by norm_num]
  exact coverp0010001000000
private noncomputable def ep0010001000001_0 : Blocks := edgeBlocks% "full/vectors/0010001000001-E-0000.bin"
noncomputable def ep0010001000001 : Blocks := ep0010001000001_0
private theorem idp0010001000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000100000.list =
    C ((2:ℤ)^88) * horner X vp0010001000001.list + horner X ep0010001000001.list := by
  exact edge_identity (B := (2:ℤ)^215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001000001 : Branch 1 (-1087761639/2000000 : ℚ) vp001000100000 := by
  apply branch_checked idp0010001000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1087761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1088761639/1000000 : ℚ) by norm_num]
  exact coverp0010001000001
theorem coverp001000100000 : Covers (-1087761639/2000000 : ℚ) vp001000100000 := join_branches bp0010001000000 bp0010001000001
private noncomputable def vp00100010000_0 : Blocks := edgeBlocks% "full/vectors/00100010000-V-0000.bin"
private noncomputable def vp00100010000_1 : Blocks := edgeBlocks% "full/vectors/00100010000-V-0001.bin"
noncomputable def vp00100010000 : Blocks := (Blocks.join vp00100010000_0 vp00100010000_1)
private theorem bp001000100000 : Branch 0 (-1087761639/4000000 : ℚ) vp00100010000 := by
  apply branch_left_normalized (c:=vp001000100000) (k:=0) (m:=80) (by decide +kernel)
  rw [show 2*(-1087761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1087761639/2000000 : ℚ) by norm_num]
  exact coverp001000100000
private noncomputable def ep001000100001_0 : Blocks := edgeBlocks% "full/vectors/001000100001-E-0000.bin"
private noncomputable def ep001000100001_1 : Blocks := edgeBlocks% "full/vectors/001000100001-E-0001.bin"
noncomputable def ep001000100001 : Blocks := (Blocks.join ep001000100001_0 ep001000100001_1)
private theorem idp001000100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100010000.list =
    C ((2:ℤ)^155) * horner X vp001000100001.list + horner X ep001000100001.list := by
  exact edge_identity (B := (2:ℤ)^307) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000100001 : Branch 1 (-1087761639/4000000 : ℚ) vp00100010000 := by
  apply branch_checked idp001000100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1087761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1089761639/2000000 : ℚ) by norm_num]
  exact coverp001000100001
theorem coverp00100010000 : Covers (-1087761639/4000000 : ℚ) vp00100010000 := join_branches bp001000100000 bp001000100001
private noncomputable def vp0010001000_0 : Blocks := edgeBlocks% "full/vectors/0010001000-V-0000.bin"
private noncomputable def vp0010001000_1 : Blocks := edgeBlocks% "full/vectors/0010001000-V-0001.bin"
private noncomputable def vp0010001000_2 : Blocks := edgeBlocks% "full/vectors/0010001000-V-0002.bin"
noncomputable def vp0010001000 : Blocks := (Blocks.join vp0010001000_0 (Blocks.join vp0010001000_1 vp0010001000_2))
private theorem bp00100010000 : Branch 0 (-1087761639/8000000 : ℚ) vp0010001000 := by
  apply branch_left_normalized (c:=vp00100010000) (k:=0) (m:=141) (by decide +kernel)
  rw [show 2*(-1087761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1087761639/4000000 : ℚ) by norm_num]
  exact coverp00100010000
private noncomputable def ep00100010001_0 : Blocks := edgeBlocks% "full/vectors/00100010001-E-0000.bin"
private noncomputable def ep00100010001_1 : Blocks := edgeBlocks% "full/vectors/00100010001-E-0001.bin"
private noncomputable def ep00100010001_2 : Blocks := edgeBlocks% "full/vectors/00100010001-E-0002.bin"
noncomputable def ep00100010001 : Blocks := (Blocks.join ep00100010001_0 (Blocks.join ep00100010001_1 ep00100010001_2))
private theorem idp00100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010001000.list =
    C ((2:ℤ)^285) * horner X vp00100010001.list + horner X ep00100010001.list := by
  exact edge_identity (B := (2:ℤ)^490) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100010001 : Branch 1 (-1087761639/8000000 : ℚ) vp0010001000 := by
  apply branch_checked idp00100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1087761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1091761639/4000000 : ℚ) by norm_num]
  exact coverp00100010001
theorem coverp0010001000 : Covers (-1087761639/8000000 : ℚ) vp0010001000 := join_branches bp00100010000 bp00100010001
private noncomputable def vp001000100_0 : Blocks := edgeBlocks% "full/vectors/001000100-V-0000.bin"
private noncomputable def vp001000100_1 : Blocks := edgeBlocks% "full/vectors/001000100-V-0001.bin"
private noncomputable def vp001000100_2 : Blocks := edgeBlocks% "full/vectors/001000100-V-0002.bin"
private noncomputable def vp001000100_3 : Blocks := edgeBlocks% "full/vectors/001000100-V-0003.bin"
noncomputable def vp001000100 : Blocks := (Blocks.join (Blocks.join vp001000100_0 vp001000100_1) (Blocks.join vp001000100_2 vp001000100_3))
private theorem bp0010001000 : Branch 0 (-1087761639/16000000 : ℚ) vp001000100 := by
  apply branch_left_normalized (c:=vp0010001000) (k:=0) (m:=260) (by decide +kernel)
  rw [show 2*(-1087761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1087761639/8000000 : ℚ) by norm_num]
  exact coverp0010001000
private noncomputable def ep0010001001_0 : Blocks := edgeBlocks% "full/vectors/0010001001-E-0000.bin"
private noncomputable def ep0010001001_1 : Blocks := edgeBlocks% "full/vectors/0010001001-E-0001.bin"
private noncomputable def ep0010001001_2 : Blocks := edgeBlocks% "full/vectors/0010001001-E-0002.bin"
private noncomputable def ep0010001001_3 : Blocks := edgeBlocks% "full/vectors/0010001001-E-0003.bin"
noncomputable def ep0010001001 : Blocks := (Blocks.join (Blocks.join ep0010001001_0 ep0010001001_1) (Blocks.join ep0010001001_2 ep0010001001_3))
private theorem idp0010001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001000100.list =
    C ((2:ℤ)^545) * horner X vp0010001001.list + horner X ep0010001001.list := by
  exact edge_identity (B := (2:ℤ)^853) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0010001001 : Branch 1 (-1087761639/16000000 : ℚ) vp001000100 := by
  apply branch_checked idp0010001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1087761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1095761639/8000000 : ℚ) by norm_num]
  exact coverp0010001001
theorem coverp001000100 : Covers (-1087761639/16000000 : ℚ) vp001000100 := join_branches bp0010001000 bp0010001001
private noncomputable def vp00100010_0 : Blocks := edgeBlocks% "full/vectors/00100010-V-0000.bin"
private noncomputable def vp00100010_1 : Blocks := edgeBlocks% "full/vectors/00100010-V-0001.bin"
private noncomputable def vp00100010_2 : Blocks := edgeBlocks% "full/vectors/00100010-V-0002.bin"
private noncomputable def vp00100010_3 : Blocks := edgeBlocks% "full/vectors/00100010-V-0003.bin"
private noncomputable def vp00100010_4 : Blocks := edgeBlocks% "full/vectors/00100010-V-0004.bin"
private noncomputable def vp00100010_5 : Blocks := edgeBlocks% "full/vectors/00100010-V-0005.bin"
private noncomputable def vp00100010_6 : Blocks := edgeBlocks% "full/vectors/00100010-V-0006.bin"
private noncomputable def vp00100010_7 : Blocks := edgeBlocks% "full/vectors/00100010-V-0007.bin"
noncomputable def vp00100010 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00100010_0 vp00100010_1) (Blocks.join vp00100010_2 vp00100010_3)) (Blocks.join (Blocks.join vp00100010_4 vp00100010_5) (Blocks.join vp00100010_6 vp00100010_7)))
private theorem bp001000100 : Branch 0 (-1087761639/32000000 : ℚ) vp00100010 := by
  apply branch_left_normalized (c:=vp001000100) (k:=0) (m:=497) (by decide +kernel)
  rw [show 2*(-1087761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1087761639/16000000 : ℚ) by norm_num]
  exact coverp001000100
private noncomputable def ep001000101_0 : Blocks := edgeBlocks% "full/vectors/001000101-E-0000.bin"
private noncomputable def ep001000101_1 : Blocks := edgeBlocks% "full/vectors/001000101-E-0001.bin"
private noncomputable def ep001000101_2 : Blocks := edgeBlocks% "full/vectors/001000101-E-0002.bin"
private noncomputable def ep001000101_3 : Blocks := edgeBlocks% "full/vectors/001000101-E-0003.bin"
private noncomputable def ep001000101_4 : Blocks := edgeBlocks% "full/vectors/001000101-E-0004.bin"
private noncomputable def ep001000101_5 : Blocks := edgeBlocks% "full/vectors/001000101-E-0005.bin"
private noncomputable def ep001000101_6 : Blocks := edgeBlocks% "full/vectors/001000101-E-0006.bin"
private noncomputable def ep001000101_7 : Blocks := edgeBlocks% "full/vectors/001000101-E-0007.bin"
noncomputable def ep001000101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep001000101_0 ep001000101_1) (Blocks.join ep001000101_2 ep001000101_3)) (Blocks.join (Blocks.join ep001000101_4 ep001000101_5) (Blocks.join ep001000101_6 ep001000101_7)))
private theorem idp001000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00100010.list =
    C ((2:ℤ)^1057) * horner X vp001000101.list + horner X ep001000101.list := by
  exact edge_identity (B := (2:ℤ)^1570) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001000101 : Branch 1 (-1087761639/32000000 : ℚ) vp00100010 := by
  apply branch_checked idp001000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1087761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1103761639/16000000 : ℚ) by norm_num]
  exact coverp001000101
theorem coverp00100010 : Covers (-1087761639/32000000 : ℚ) vp00100010 := join_branches bp001000100 bp001000101
private noncomputable def vp0010001_0 : Blocks := edgeBlocks% "full/vectors/0010001-V-0000.bin"
private noncomputable def vp0010001_1 : Blocks := edgeBlocks% "full/vectors/0010001-V-0001.bin"
private noncomputable def vp0010001_2 : Blocks := edgeBlocks% "full/vectors/0010001-V-0002.bin"
private noncomputable def vp0010001_3 : Blocks := edgeBlocks% "full/vectors/0010001-V-0003.bin"
private noncomputable def vp0010001_4 : Blocks := edgeBlocks% "full/vectors/0010001-V-0004.bin"
private noncomputable def vp0010001_5 : Blocks := edgeBlocks% "full/vectors/0010001-V-0005.bin"
private noncomputable def vp0010001_6 : Blocks := edgeBlocks% "full/vectors/0010001-V-0006.bin"
private noncomputable def vp0010001_7 : Blocks := edgeBlocks% "full/vectors/0010001-V-0007.bin"
private noncomputable def vp0010001_8 : Blocks := edgeBlocks% "full/vectors/0010001-V-0008.bin"
private noncomputable def vp0010001_9 : Blocks := edgeBlocks% "full/vectors/0010001-V-0009.bin"
private noncomputable def vp0010001_10 : Blocks := edgeBlocks% "full/vectors/0010001-V-0010.bin"
private noncomputable def vp0010001_11 : Blocks := edgeBlocks% "full/vectors/0010001-V-0011.bin"
private noncomputable def vp0010001_12 : Blocks := edgeBlocks% "full/vectors/0010001-V-0012.bin"
private noncomputable def vp0010001_13 : Blocks := edgeBlocks% "full/vectors/0010001-V-0013.bin"
private noncomputable def vp0010001_14 : Blocks := edgeBlocks% "full/vectors/0010001-V-0014.bin"
noncomputable def vp0010001 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0010001_0 (Blocks.join vp0010001_1 vp0010001_2)) (Blocks.join (Blocks.join vp0010001_3 vp0010001_4) (Blocks.join vp0010001_5 vp0010001_6))) (Blocks.join (Blocks.join (Blocks.join vp0010001_7 vp0010001_8) (Blocks.join vp0010001_9 vp0010001_10)) (Blocks.join (Blocks.join vp0010001_11 vp0010001_12) (Blocks.join vp0010001_13 vp0010001_14))))
private theorem bp00100010 : Branch 0 (-1087761639/64000000 : ℚ) vp0010001 := by
  apply branch_left_normalized (c:=vp00100010) (k:=0) (m:=963) (by decide +kernel)
  rw [show 2*(-1087761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1087761639/32000000 : ℚ) by norm_num]
  exact coverp00100010
private noncomputable def ep00100011_0 : Blocks := edgeBlocks% "full/vectors/00100011-E-0000.bin"
private noncomputable def ep00100011_1 : Blocks := edgeBlocks% "full/vectors/00100011-E-0001.bin"
private noncomputable def ep00100011_2 : Blocks := edgeBlocks% "full/vectors/00100011-E-0002.bin"
private noncomputable def ep00100011_3 : Blocks := edgeBlocks% "full/vectors/00100011-E-0003.bin"
private noncomputable def ep00100011_4 : Blocks := edgeBlocks% "full/vectors/00100011-E-0004.bin"
private noncomputable def ep00100011_5 : Blocks := edgeBlocks% "full/vectors/00100011-E-0005.bin"
private noncomputable def ep00100011_6 : Blocks := edgeBlocks% "full/vectors/00100011-E-0006.bin"
private noncomputable def ep00100011_7 : Blocks := edgeBlocks% "full/vectors/00100011-E-0007.bin"
private noncomputable def ep00100011_8 : Blocks := edgeBlocks% "full/vectors/00100011-E-0008.bin"
private noncomputable def ep00100011_9 : Blocks := edgeBlocks% "full/vectors/00100011-E-0009.bin"
private noncomputable def ep00100011_10 : Blocks := edgeBlocks% "full/vectors/00100011-E-0010.bin"
private noncomputable def ep00100011_11 : Blocks := edgeBlocks% "full/vectors/00100011-E-0011.bin"
private noncomputable def ep00100011_12 : Blocks := edgeBlocks% "full/vectors/00100011-E-0012.bin"
private noncomputable def ep00100011_13 : Blocks := edgeBlocks% "full/vectors/00100011-E-0013.bin"
private noncomputable def ep00100011_14 : Blocks := edgeBlocks% "full/vectors/00100011-E-0014.bin"
noncomputable def ep00100011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00100011_0 (Blocks.join ep00100011_1 ep00100011_2)) (Blocks.join (Blocks.join ep00100011_3 ep00100011_4) (Blocks.join ep00100011_5 ep00100011_6))) (Blocks.join (Blocks.join (Blocks.join ep00100011_7 ep00100011_8) (Blocks.join ep00100011_9 ep00100011_10)) (Blocks.join (Blocks.join ep00100011_11 ep00100011_12) (Blocks.join ep00100011_13 ep00100011_14))))
private theorem idp00100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0010001.list =
    C ((2:ℤ)^2067) * horner X vp00100011.list + horner X ep00100011.list := by
  exact edge_identity (B := (2:ℤ)^2982) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00100011 : Branch 1 (-1087761639/64000000 : ℚ) vp0010001 := by
  apply branch_checked idp00100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1087761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1119761639/32000000 : ℚ) by norm_num]
  exact coverp00100011
theorem coverp0010001 : Covers (-1087761639/64000000 : ℚ) vp0010001 := join_branches bp00100010 bp00100011
end NextProof.EdgeFull

