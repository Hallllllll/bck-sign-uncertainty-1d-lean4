import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp001111111111_0 : Blocks := edgeBlocks% "full/vectors/001111111111-V-0000.bin"
noncomputable def vp001111111111 : Blocks := vp001111111111_0
theorem coverp001111111111 : Covers (-2045761639/2000000 : ℚ) vp001111111111 := cover_leaf (by decide +kernel)
private noncomputable def vp001111111110_0 : Blocks := edgeBlocks% "full/vectors/001111111110-V-0000.bin"
noncomputable def vp001111111110 : Blocks := vp001111111110_0
theorem coverp001111111110 : Covers (-2043761639/2000000 : ℚ) vp001111111110 := cover_leaf (by decide +kernel)
private noncomputable def vp00111111111_0 : Blocks := edgeBlocks% "full/vectors/00111111111-V-0000.bin"
noncomputable def vp00111111111 : Blocks := vp00111111111_0
private theorem bp001111111110 : Branch 0 (-2043761639/4000000 : ℚ) vp00111111111 := by
  apply branch_left_normalized (c:=vp001111111110) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2043761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2043761639/2000000 : ℚ) by norm_num]
  exact coverp001111111110
private noncomputable def ep001111111111_0 : Blocks := edgeBlocks% "full/vectors/001111111111-E-0000.bin"
noncomputable def ep001111111111 : Blocks := ep001111111111_0
private theorem idp001111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111111111.list =
    C ((2:ℤ)^116) * horner X vp001111111111.list + horner X ep001111111111.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111111111 : Branch 1 (-2043761639/4000000 : ℚ) vp00111111111 := by
  apply branch_checked idp001111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2043761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2045761639/2000000 : ℚ) by norm_num]
  exact coverp001111111111
theorem coverp00111111111 : Covers (-2043761639/4000000 : ℚ) vp00111111111 := join_branches bp001111111110 bp001111111111
private noncomputable def vp001111111101_0 : Blocks := edgeBlocks% "full/vectors/001111111101-V-0000.bin"
noncomputable def vp001111111101 : Blocks := vp001111111101_0
theorem coverp001111111101 : Covers (-2041761639/2000000 : ℚ) vp001111111101 := cover_leaf (by decide +kernel)
private noncomputable def vp001111111100_0 : Blocks := edgeBlocks% "full/vectors/001111111100-V-0000.bin"
noncomputable def vp001111111100 : Blocks := vp001111111100_0
theorem coverp001111111100 : Covers (-2039761639/2000000 : ℚ) vp001111111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00111111110_0 : Blocks := edgeBlocks% "full/vectors/00111111110-V-0000.bin"
noncomputable def vp00111111110 : Blocks := vp00111111110_0
private theorem bp001111111100 : Branch 0 (-2039761639/4000000 : ℚ) vp00111111110 := by
  apply branch_left_normalized (c:=vp001111111100) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2039761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2039761639/2000000 : ℚ) by norm_num]
  exact coverp001111111100
private noncomputable def ep001111111101_0 : Blocks := edgeBlocks% "full/vectors/001111111101-E-0000.bin"
noncomputable def ep001111111101 : Blocks := ep001111111101_0
private theorem idp001111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111111110.list =
    C ((2:ℤ)^115) * horner X vp001111111101.list + horner X ep001111111101.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111111101 : Branch 1 (-2039761639/4000000 : ℚ) vp00111111110 := by
  apply branch_checked idp001111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2039761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2041761639/2000000 : ℚ) by norm_num]
  exact coverp001111111101
theorem coverp00111111110 : Covers (-2039761639/4000000 : ℚ) vp00111111110 := join_branches bp001111111100 bp001111111101
private noncomputable def vp0011111111_0 : Blocks := edgeBlocks% "full/vectors/0011111111-V-0000.bin"
private noncomputable def vp0011111111_1 : Blocks := edgeBlocks% "full/vectors/0011111111-V-0001.bin"
noncomputable def vp0011111111 : Blocks := (Blocks.join vp0011111111_0 vp0011111111_1)
private theorem bp00111111110 : Branch 0 (-2039761639/8000000 : ℚ) vp0011111111 := by
  apply branch_left_normalized (c:=vp00111111110) (k:=0) (m:=103) (by decide +kernel)
  rw [show 2*(-2039761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2039761639/4000000 : ℚ) by norm_num]
  exact coverp00111111110
private noncomputable def ep00111111111_0 : Blocks := edgeBlocks% "full/vectors/00111111111-E-0000.bin"
private noncomputable def ep00111111111_1 : Blocks := edgeBlocks% "full/vectors/00111111111-E-0001.bin"
noncomputable def ep00111111111 : Blocks := (Blocks.join ep00111111111_0 ep00111111111_1)
private theorem idp00111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011111111.list =
    C ((2:ℤ)^213) * horner X vp00111111111.list + horner X ep00111111111.list := by
  exact edge_identity (B := (2:ℤ)^377) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111111111 : Branch 1 (-2039761639/8000000 : ℚ) vp0011111111 := by
  apply branch_checked idp00111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2039761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2043761639/4000000 : ℚ) by norm_num]
  exact coverp00111111111
theorem coverp0011111111 : Covers (-2039761639/8000000 : ℚ) vp0011111111 := join_branches bp00111111110 bp00111111111
private noncomputable def vp001111111011_0 : Blocks := edgeBlocks% "full/vectors/001111111011-V-0000.bin"
noncomputable def vp001111111011 : Blocks := vp001111111011_0
theorem coverp001111111011 : Covers (-2037761639/2000000 : ℚ) vp001111111011 := cover_leaf (by decide +kernel)
private noncomputable def vp001111111010_0 : Blocks := edgeBlocks% "full/vectors/001111111010-V-0000.bin"
noncomputable def vp001111111010 : Blocks := vp001111111010_0
theorem coverp001111111010 : Covers (-2035761639/2000000 : ℚ) vp001111111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00111111101_0 : Blocks := edgeBlocks% "full/vectors/00111111101-V-0000.bin"
noncomputable def vp00111111101 : Blocks := vp00111111101_0
private theorem bp001111111010 : Branch 0 (-2035761639/4000000 : ℚ) vp00111111101 := by
  apply branch_left_normalized (c:=vp001111111010) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-2035761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2035761639/2000000 : ℚ) by norm_num]
  exact coverp001111111010
private noncomputable def ep001111111011_0 : Blocks := edgeBlocks% "full/vectors/001111111011-E-0000.bin"
noncomputable def ep001111111011 : Blocks := ep001111111011_0
private theorem idp001111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111111101.list =
    C ((2:ℤ)^115) * horner X vp001111111011.list + horner X ep001111111011.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111111011 : Branch 1 (-2035761639/4000000 : ℚ) vp00111111101 := by
  apply branch_checked idp001111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2035761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2037761639/2000000 : ℚ) by norm_num]
  exact coverp001111111011
theorem coverp00111111101 : Covers (-2035761639/4000000 : ℚ) vp00111111101 := join_branches bp001111111010 bp001111111011
private noncomputable def vp001111111001_0 : Blocks := edgeBlocks% "full/vectors/001111111001-V-0000.bin"
noncomputable def vp001111111001 : Blocks := vp001111111001_0
theorem coverp001111111001 : Covers (-2033761639/2000000 : ℚ) vp001111111001 := cover_leaf (by decide +kernel)
private noncomputable def vp001111111000_0 : Blocks := edgeBlocks% "full/vectors/001111111000-V-0000.bin"
noncomputable def vp001111111000 : Blocks := vp001111111000_0
theorem coverp001111111000 : Covers (-2031761639/2000000 : ℚ) vp001111111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00111111100_0 : Blocks := edgeBlocks% "full/vectors/00111111100-V-0000.bin"
noncomputable def vp00111111100 : Blocks := vp00111111100_0
private theorem bp001111111000 : Branch 0 (-2031761639/4000000 : ℚ) vp00111111100 := by
  apply branch_left_normalized (c:=vp001111111000) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2031761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2031761639/2000000 : ℚ) by norm_num]
  exact coverp001111111000
private noncomputable def ep001111111001_0 : Blocks := edgeBlocks% "full/vectors/001111111001-E-0000.bin"
noncomputable def ep001111111001 : Blocks := ep001111111001_0
private theorem idp001111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111111100.list =
    C ((2:ℤ)^116) * horner X vp001111111001.list + horner X ep001111111001.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111111001 : Branch 1 (-2031761639/4000000 : ℚ) vp00111111100 := by
  apply branch_checked idp001111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2031761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2033761639/2000000 : ℚ) by norm_num]
  exact coverp001111111001
theorem coverp00111111100 : Covers (-2031761639/4000000 : ℚ) vp00111111100 := join_branches bp001111111000 bp001111111001
private noncomputable def vp0011111110_0 : Blocks := edgeBlocks% "full/vectors/0011111110-V-0000.bin"
private noncomputable def vp0011111110_1 : Blocks := edgeBlocks% "full/vectors/0011111110-V-0001.bin"
noncomputable def vp0011111110 : Blocks := (Blocks.join vp0011111110_0 vp0011111110_1)
private theorem bp00111111100 : Branch 0 (-2031761639/8000000 : ℚ) vp0011111110 := by
  apply branch_left_normalized (c:=vp00111111100) (k:=0) (m:=103) (by decide +kernel)
  rw [show 2*(-2031761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2031761639/4000000 : ℚ) by norm_num]
  exact coverp00111111100
private noncomputable def ep00111111101_0 : Blocks := edgeBlocks% "full/vectors/00111111101-E-0000.bin"
private noncomputable def ep00111111101_1 : Blocks := edgeBlocks% "full/vectors/00111111101-E-0001.bin"
noncomputable def ep00111111101 : Blocks := (Blocks.join ep00111111101_0 ep00111111101_1)
private theorem idp00111111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011111110.list =
    C ((2:ℤ)^214) * horner X vp00111111101.list + horner X ep00111111101.list := by
  exact edge_identity (B := (2:ℤ)^375) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111111101 : Branch 1 (-2031761639/8000000 : ℚ) vp0011111110 := by
  apply branch_checked idp00111111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2031761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2035761639/4000000 : ℚ) by norm_num]
  exact coverp00111111101
theorem coverp0011111110 : Covers (-2031761639/8000000 : ℚ) vp0011111110 := join_branches bp00111111100 bp00111111101
private noncomputable def vp001111111_0 : Blocks := edgeBlocks% "full/vectors/001111111-V-0000.bin"
private noncomputable def vp001111111_1 : Blocks := edgeBlocks% "full/vectors/001111111-V-0001.bin"
private noncomputable def vp001111111_2 : Blocks := edgeBlocks% "full/vectors/001111111-V-0002.bin"
noncomputable def vp001111111 : Blocks := (Blocks.join vp001111111_0 (Blocks.join vp001111111_1 vp001111111_2))
private theorem bp0011111110 : Branch 0 (-2031761639/16000000 : ℚ) vp001111111 := by
  apply branch_left_normalized (c:=vp0011111110) (k:=0) (m:=190) (by decide +kernel)
  rw [show 2*(-2031761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2031761639/8000000 : ℚ) by norm_num]
  exact coverp0011111110
private noncomputable def ep0011111111_0 : Blocks := edgeBlocks% "full/vectors/0011111111-E-0000.bin"
private noncomputable def ep0011111111_1 : Blocks := edgeBlocks% "full/vectors/0011111111-E-0001.bin"
private noncomputable def ep0011111111_2 : Blocks := edgeBlocks% "full/vectors/0011111111-E-0002.bin"
noncomputable def ep0011111111 : Blocks := (Blocks.join ep0011111111_0 (Blocks.join ep0011111111_1 ep0011111111_2))
private theorem idp0011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111111.list =
    C ((2:ℤ)^409) * horner X vp0011111111.list + horner X ep0011111111.list := by
  exact edge_identity (B := (2:ℤ)^640) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011111111 : Branch 1 (-2031761639/16000000 : ℚ) vp001111111 := by
  apply branch_checked idp0011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2031761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2039761639/8000000 : ℚ) by norm_num]
  exact coverp0011111111
theorem coverp001111111 : Covers (-2031761639/16000000 : ℚ) vp001111111 := join_branches bp0011111110 bp0011111111
private noncomputable def vp001111110111_0 : Blocks := edgeBlocks% "full/vectors/001111110111-V-0000.bin"
noncomputable def vp001111110111 : Blocks := vp001111110111_0
theorem coverp001111110111 : Covers (-2029761639/2000000 : ℚ) vp001111110111 := cover_leaf (by decide +kernel)
private noncomputable def vp001111110110_0 : Blocks := edgeBlocks% "full/vectors/001111110110-V-0000.bin"
noncomputable def vp001111110110 : Blocks := vp001111110110_0
theorem coverp001111110110 : Covers (-2027761639/2000000 : ℚ) vp001111110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00111111011_0 : Blocks := edgeBlocks% "full/vectors/00111111011-V-0000.bin"
noncomputable def vp00111111011 : Blocks := vp00111111011_0
private theorem bp001111110110 : Branch 0 (-2027761639/4000000 : ℚ) vp00111111011 := by
  apply branch_left_normalized (c:=vp001111110110) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2027761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2027761639/2000000 : ℚ) by norm_num]
  exact coverp001111110110
private noncomputable def ep001111110111_0 : Blocks := edgeBlocks% "full/vectors/001111110111-E-0000.bin"
noncomputable def ep001111110111 : Blocks := ep001111110111_0
private theorem idp001111110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111111011.list =
    C ((2:ℤ)^116) * horner X vp001111110111.list + horner X ep001111110111.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111110111 : Branch 1 (-2027761639/4000000 : ℚ) vp00111111011 := by
  apply branch_checked idp001111110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2027761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2029761639/2000000 : ℚ) by norm_num]
  exact coverp001111110111
theorem coverp00111111011 : Covers (-2027761639/4000000 : ℚ) vp00111111011 := join_branches bp001111110110 bp001111110111
private noncomputable def vp001111110101_0 : Blocks := edgeBlocks% "full/vectors/001111110101-V-0000.bin"
noncomputable def vp001111110101 : Blocks := vp001111110101_0
theorem coverp001111110101 : Covers (-2025761639/2000000 : ℚ) vp001111110101 := cover_leaf (by decide +kernel)
private noncomputable def vp001111110100_0 : Blocks := edgeBlocks% "full/vectors/001111110100-V-0000.bin"
noncomputable def vp001111110100 : Blocks := vp001111110100_0
theorem coverp001111110100 : Covers (-2023761639/2000000 : ℚ) vp001111110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00111111010_0 : Blocks := edgeBlocks% "full/vectors/00111111010-V-0000.bin"
noncomputable def vp00111111010 : Blocks := vp00111111010_0
private theorem bp001111110100 : Branch 0 (-2023761639/4000000 : ℚ) vp00111111010 := by
  apply branch_left_normalized (c:=vp001111110100) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2023761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2023761639/2000000 : ℚ) by norm_num]
  exact coverp001111110100
private noncomputable def ep001111110101_0 : Blocks := edgeBlocks% "full/vectors/001111110101-E-0000.bin"
noncomputable def ep001111110101 : Blocks := ep001111110101_0
private theorem idp001111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111111010.list =
    C ((2:ℤ)^116) * horner X vp001111110101.list + horner X ep001111110101.list := by
  exact edge_identity (B := (2:ℤ)^242) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111110101 : Branch 1 (-2023761639/4000000 : ℚ) vp00111111010 := by
  apply branch_checked idp001111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-2023761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2025761639/2000000 : ℚ) by norm_num]
  exact coverp001111110101
theorem coverp00111111010 : Covers (-2023761639/4000000 : ℚ) vp00111111010 := join_branches bp001111110100 bp001111110101
private noncomputable def vp0011111101_0 : Blocks := edgeBlocks% "full/vectors/0011111101-V-0000.bin"
private noncomputable def vp0011111101_1 : Blocks := edgeBlocks% "full/vectors/0011111101-V-0001.bin"
noncomputable def vp0011111101 : Blocks := (Blocks.join vp0011111101_0 vp0011111101_1)
private theorem bp00111111010 : Branch 0 (-2023761639/8000000 : ℚ) vp0011111101 := by
  apply branch_left_normalized (c:=vp00111111010) (k:=0) (m:=103) (by decide +kernel)
  rw [show 2*(-2023761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2023761639/4000000 : ℚ) by norm_num]
  exact coverp00111111010
private noncomputable def ep00111111011_0 : Blocks := edgeBlocks% "full/vectors/00111111011-E-0000.bin"
private noncomputable def ep00111111011_1 : Blocks := edgeBlocks% "full/vectors/00111111011-E-0001.bin"
noncomputable def ep00111111011 : Blocks := (Blocks.join ep00111111011_0 ep00111111011_1)
private theorem idp00111111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011111101.list =
    C ((2:ℤ)^214) * horner X vp00111111011.list + horner X ep00111111011.list := by
  exact edge_identity (B := (2:ℤ)^375) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111111011 : Branch 1 (-2023761639/8000000 : ℚ) vp0011111101 := by
  apply branch_checked idp00111111011 (by positivity) (by decide +kernel)
  rw [show 2*(-2023761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2027761639/4000000 : ℚ) by norm_num]
  exact coverp00111111011
theorem coverp0011111101 : Covers (-2023761639/8000000 : ℚ) vp0011111101 := join_branches bp00111111010 bp00111111011
private noncomputable def vp001111110011_0 : Blocks := edgeBlocks% "full/vectors/001111110011-V-0000.bin"
noncomputable def vp001111110011 : Blocks := vp001111110011_0
theorem coverp001111110011 : Covers (-2021761639/2000000 : ℚ) vp001111110011 := cover_leaf (by decide +kernel)
private noncomputable def vp001111110010_0 : Blocks := edgeBlocks% "full/vectors/001111110010-V-0000.bin"
noncomputable def vp001111110010 : Blocks := vp001111110010_0
theorem coverp001111110010 : Covers (-2019761639/2000000 : ℚ) vp001111110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00111111001_0 : Blocks := edgeBlocks% "full/vectors/00111111001-V-0000.bin"
noncomputable def vp00111111001 : Blocks := vp00111111001_0
private theorem bp001111110010 : Branch 0 (-2019761639/4000000 : ℚ) vp00111111001 := by
  apply branch_left_normalized (c:=vp001111110010) (k:=0) (m:=58) (by decide +kernel)
  rw [show 2*(-2019761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2019761639/2000000 : ℚ) by norm_num]
  exact coverp001111110010
private noncomputable def ep001111110011_0 : Blocks := edgeBlocks% "full/vectors/001111110011-E-0000.bin"
noncomputable def ep001111110011 : Blocks := ep001111110011_0
private theorem idp001111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111111001.list =
    C ((2:ℤ)^116) * horner X vp001111110011.list + horner X ep001111110011.list := by
  exact edge_identity (B := (2:ℤ)^243) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111110011 : Branch 1 (-2019761639/4000000 : ℚ) vp00111111001 := by
  apply branch_checked idp001111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-2019761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2021761639/2000000 : ℚ) by norm_num]
  exact coverp001111110011
theorem coverp00111111001 : Covers (-2019761639/4000000 : ℚ) vp00111111001 := join_branches bp001111110010 bp001111110011
private noncomputable def vp001111110001_0 : Blocks := edgeBlocks% "full/vectors/001111110001-V-0000.bin"
noncomputable def vp001111110001 : Blocks := vp001111110001_0
theorem coverp001111110001 : Covers (-2017761639/2000000 : ℚ) vp001111110001 := cover_leaf (by decide +kernel)
private noncomputable def vp001111110000_0 : Blocks := edgeBlocks% "full/vectors/001111110000-V-0000.bin"
noncomputable def vp001111110000 : Blocks := vp001111110000_0
theorem coverp001111110000 : Covers (-2015761639/2000000 : ℚ) vp001111110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00111111000_0 : Blocks := edgeBlocks% "full/vectors/00111111000-V-0000.bin"
noncomputable def vp00111111000 : Blocks := vp00111111000_0
private theorem bp001111110000 : Branch 0 (-2015761639/4000000 : ℚ) vp00111111000 := by
  apply branch_left_normalized (c:=vp001111110000) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2015761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2015761639/2000000 : ℚ) by norm_num]
  exact coverp001111110000
private noncomputable def ep001111110001_0 : Blocks := edgeBlocks% "full/vectors/001111110001-E-0000.bin"
noncomputable def ep001111110001 : Blocks := ep001111110001_0
private theorem idp001111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111111000.list =
    C ((2:ℤ)^117) * horner X vp001111110001.list + horner X ep001111110001.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111110001 : Branch 1 (-2015761639/4000000 : ℚ) vp00111111000 := by
  apply branch_checked idp001111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-2015761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2017761639/2000000 : ℚ) by norm_num]
  exact coverp001111110001
theorem coverp00111111000 : Covers (-2015761639/4000000 : ℚ) vp00111111000 := join_branches bp001111110000 bp001111110001
private noncomputable def vp0011111100_0 : Blocks := edgeBlocks% "full/vectors/0011111100-V-0000.bin"
private noncomputable def vp0011111100_1 : Blocks := edgeBlocks% "full/vectors/0011111100-V-0001.bin"
noncomputable def vp0011111100 : Blocks := (Blocks.join vp0011111100_0 vp0011111100_1)
private theorem bp00111111000 : Branch 0 (-2015761639/8000000 : ℚ) vp0011111100 := by
  apply branch_left_normalized (c:=vp00111111000) (k:=0) (m:=104) (by decide +kernel)
  rw [show 2*(-2015761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2015761639/4000000 : ℚ) by norm_num]
  exact coverp00111111000
private noncomputable def ep00111111001_0 : Blocks := edgeBlocks% "full/vectors/00111111001-E-0000.bin"
private noncomputable def ep00111111001_1 : Blocks := edgeBlocks% "full/vectors/00111111001-E-0001.bin"
noncomputable def ep00111111001 : Blocks := (Blocks.join ep00111111001_0 ep00111111001_1)
private theorem idp00111111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011111100.list =
    C ((2:ℤ)^217) * horner X vp00111111001.list + horner X ep00111111001.list := by
  exact edge_identity (B := (2:ℤ)^379) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111111001 : Branch 1 (-2015761639/8000000 : ℚ) vp0011111100 := by
  apply branch_checked idp00111111001 (by positivity) (by decide +kernel)
  rw [show 2*(-2015761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2019761639/4000000 : ℚ) by norm_num]
  exact coverp00111111001
theorem coverp0011111100 : Covers (-2015761639/8000000 : ℚ) vp0011111100 := join_branches bp00111111000 bp00111111001
private noncomputable def vp001111110_0 : Blocks := edgeBlocks% "full/vectors/001111110-V-0000.bin"
private noncomputable def vp001111110_1 : Blocks := edgeBlocks% "full/vectors/001111110-V-0001.bin"
private noncomputable def vp001111110_2 : Blocks := edgeBlocks% "full/vectors/001111110-V-0002.bin"
noncomputable def vp001111110 : Blocks := (Blocks.join vp001111110_0 (Blocks.join vp001111110_1 vp001111110_2))
private theorem bp0011111100 : Branch 0 (-2015761639/16000000 : ℚ) vp001111110 := by
  apply branch_left_normalized (c:=vp0011111100) (k:=0) (m:=192) (by decide +kernel)
  rw [show 2*(-2015761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-2015761639/8000000 : ℚ) by norm_num]
  exact coverp0011111100
private noncomputable def ep0011111101_0 : Blocks := edgeBlocks% "full/vectors/0011111101-E-0000.bin"
private noncomputable def ep0011111101_1 : Blocks := edgeBlocks% "full/vectors/0011111101-E-0001.bin"
private noncomputable def ep0011111101_2 : Blocks := edgeBlocks% "full/vectors/0011111101-E-0002.bin"
noncomputable def ep0011111101 : Blocks := (Blocks.join ep0011111101_0 (Blocks.join ep0011111101_1 ep0011111101_2))
private theorem idp0011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111110.list =
    C ((2:ℤ)^415) * horner X vp0011111101.list + horner X ep0011111101.list := by
  exact edge_identity (B := (2:ℤ)^646) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011111101 : Branch 1 (-2015761639/16000000 : ℚ) vp001111110 := by
  apply branch_checked idp0011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-2015761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2023761639/8000000 : ℚ) by norm_num]
  exact coverp0011111101
theorem coverp001111110 : Covers (-2015761639/16000000 : ℚ) vp001111110 := join_branches bp0011111100 bp0011111101
private noncomputable def vp00111111_0 : Blocks := edgeBlocks% "full/vectors/00111111-V-0000.bin"
private noncomputable def vp00111111_1 : Blocks := edgeBlocks% "full/vectors/00111111-V-0001.bin"
private noncomputable def vp00111111_2 : Blocks := edgeBlocks% "full/vectors/00111111-V-0002.bin"
private noncomputable def vp00111111_3 : Blocks := edgeBlocks% "full/vectors/00111111-V-0003.bin"
private noncomputable def vp00111111_4 : Blocks := edgeBlocks% "full/vectors/00111111-V-0004.bin"
private noncomputable def vp00111111_5 : Blocks := edgeBlocks% "full/vectors/00111111-V-0005.bin"
noncomputable def vp00111111 : Blocks := (Blocks.join (Blocks.join vp00111111_0 (Blocks.join vp00111111_1 vp00111111_2)) (Blocks.join vp00111111_3 (Blocks.join vp00111111_4 vp00111111_5)))
private theorem bp001111110 : Branch 0 (-2015761639/32000000 : ℚ) vp00111111 := by
  apply branch_left_normalized (c:=vp001111110) (k:=0) (m:=366) (by decide +kernel)
  rw [show 2*(-2015761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-2015761639/16000000 : ℚ) by norm_num]
  exact coverp001111110
private noncomputable def ep001111111_0 : Blocks := edgeBlocks% "full/vectors/001111111-E-0000.bin"
private noncomputable def ep001111111_1 : Blocks := edgeBlocks% "full/vectors/001111111-E-0001.bin"
private noncomputable def ep001111111_2 : Blocks := edgeBlocks% "full/vectors/001111111-E-0002.bin"
private noncomputable def ep001111111_3 : Blocks := edgeBlocks% "full/vectors/001111111-E-0003.bin"
private noncomputable def ep001111111_4 : Blocks := edgeBlocks% "full/vectors/001111111-E-0004.bin"
private noncomputable def ep001111111_5 : Blocks := edgeBlocks% "full/vectors/001111111-E-0005.bin"
noncomputable def ep001111111 : Blocks := (Blocks.join (Blocks.join ep001111111_0 (Blocks.join ep001111111_1 ep001111111_2)) (Blocks.join ep001111111_3 (Blocks.join ep001111111_4 ep001111111_5)))
private theorem idp001111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111111.list =
    C ((2:ℤ)^806) * horner X vp001111111.list + horner X ep001111111.list := by
  exact edge_identity (B := (2:ℤ)^1176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111111 : Branch 1 (-2015761639/32000000 : ℚ) vp00111111 := by
  apply branch_checked idp001111111 (by positivity) (by decide +kernel)
  rw [show 2*(-2015761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-2031761639/16000000 : ℚ) by norm_num]
  exact coverp001111111
theorem coverp00111111 : Covers (-2015761639/32000000 : ℚ) vp00111111 := join_branches bp001111110 bp001111111
private noncomputable def vp001111101111_0 : Blocks := edgeBlocks% "full/vectors/001111101111-V-0000.bin"
noncomputable def vp001111101111 : Blocks := vp001111101111_0
theorem coverp001111101111 : Covers (-2013761639/2000000 : ℚ) vp001111101111 := cover_leaf (by decide +kernel)
private noncomputable def vp001111101110_0 : Blocks := edgeBlocks% "full/vectors/001111101110-V-0000.bin"
noncomputable def vp001111101110 : Blocks := vp001111101110_0
theorem coverp001111101110 : Covers (-2011761639/2000000 : ℚ) vp001111101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00111110111_0 : Blocks := edgeBlocks% "full/vectors/00111110111-V-0000.bin"
noncomputable def vp00111110111 : Blocks := vp00111110111_0
private theorem bp001111101110 : Branch 0 (-2011761639/4000000 : ℚ) vp00111110111 := by
  apply branch_left_normalized (c:=vp001111101110) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-2011761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2011761639/2000000 : ℚ) by norm_num]
  exact coverp001111101110
private noncomputable def ep001111101111_0 : Blocks := edgeBlocks% "full/vectors/001111101111-E-0000.bin"
noncomputable def ep001111101111 : Blocks := ep001111101111_0
private theorem idp001111101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111110111.list =
    C ((2:ℤ)^119) * horner X vp001111101111.list + horner X ep001111101111.list := by
  exact edge_identity (B := (2:ℤ)^248) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111101111 : Branch 1 (-2011761639/4000000 : ℚ) vp00111110111 := by
  apply branch_checked idp001111101111 (by positivity) (by decide +kernel)
  rw [show 2*(-2011761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2013761639/2000000 : ℚ) by norm_num]
  exact coverp001111101111
theorem coverp00111110111 : Covers (-2011761639/4000000 : ℚ) vp00111110111 := join_branches bp001111101110 bp001111101111
private noncomputable def vp001111101101_0 : Blocks := edgeBlocks% "full/vectors/001111101101-V-0000.bin"
noncomputable def vp001111101101 : Blocks := vp001111101101_0
theorem coverp001111101101 : Covers (-2009761639/2000000 : ℚ) vp001111101101 := cover_leaf (by decide +kernel)
private noncomputable def vp001111101100_0 : Blocks := edgeBlocks% "full/vectors/001111101100-V-0000.bin"
noncomputable def vp001111101100 : Blocks := vp001111101100_0
theorem coverp001111101100 : Covers (-2007761639/2000000 : ℚ) vp001111101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00111110110_0 : Blocks := edgeBlocks% "full/vectors/00111110110-V-0000.bin"
noncomputable def vp00111110110 : Blocks := vp00111110110_0
private theorem bp001111101100 : Branch 0 (-2007761639/4000000 : ℚ) vp00111110110 := by
  apply branch_left_normalized (c:=vp001111101100) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2007761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2007761639/2000000 : ℚ) by norm_num]
  exact coverp001111101100
private noncomputable def ep001111101101_0 : Blocks := edgeBlocks% "full/vectors/001111101101-E-0000.bin"
noncomputable def ep001111101101 : Blocks := ep001111101101_0
private theorem idp001111101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111110110.list =
    C ((2:ℤ)^123) * horner X vp001111101101.list + horner X ep001111101101.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111101101 : Branch 1 (-2007761639/4000000 : ℚ) vp00111110110 := by
  apply branch_checked idp001111101101 (by positivity) (by decide +kernel)
  rw [show 2*(-2007761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2009761639/2000000 : ℚ) by norm_num]
  exact coverp001111101101
theorem coverp00111110110 : Covers (-2007761639/4000000 : ℚ) vp00111110110 := join_branches bp001111101100 bp001111101101
private noncomputable def vp0011111011_0 : Blocks := edgeBlocks% "full/vectors/0011111011-V-0000.bin"
private noncomputable def vp0011111011_1 : Blocks := edgeBlocks% "full/vectors/0011111011-V-0001.bin"
noncomputable def vp0011111011 : Blocks := (Blocks.join vp0011111011_0 vp0011111011_1)
private theorem bp00111110110 : Branch 0 (-2007761639/8000000 : ℚ) vp0011111011 := by
  apply branch_left_normalized (c:=vp00111110110) (k:=0) (m:=108) (by decide +kernel)
  rw [show 2*(-2007761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-2007761639/4000000 : ℚ) by norm_num]
  exact coverp00111110110
private noncomputable def ep00111110111_0 : Blocks := edgeBlocks% "full/vectors/00111110111-E-0000.bin"
private noncomputable def ep00111110111_1 : Blocks := edgeBlocks% "full/vectors/00111110111-E-0001.bin"
noncomputable def ep00111110111 : Blocks := (Blocks.join ep00111110111_0 ep00111110111_1)
private theorem idp00111110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011111011.list =
    C ((2:ℤ)^224) * horner X vp00111110111.list + horner X ep00111110111.list := by
  exact edge_identity (B := (2:ℤ)^389) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111110111 : Branch 1 (-2007761639/8000000 : ℚ) vp0011111011 := by
  apply branch_checked idp00111110111 (by positivity) (by decide +kernel)
  rw [show 2*(-2007761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2011761639/4000000 : ℚ) by norm_num]
  exact coverp00111110111
theorem coverp0011111011 : Covers (-2007761639/8000000 : ℚ) vp0011111011 := join_branches bp00111110110 bp00111110111
private noncomputable def vp001111101011_0 : Blocks := edgeBlocks% "full/vectors/001111101011-V-0000.bin"
noncomputable def vp001111101011 : Blocks := vp001111101011_0
theorem coverp001111101011 : Covers (-2005761639/2000000 : ℚ) vp001111101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011111010101_0 : Blocks := edgeBlocks% "full/vectors/0011111010101-V-0000.bin"
noncomputable def vp0011111010101 : Blocks := vp0011111010101_0
theorem coverp0011111010101 : Covers (-2004761639/1000000 : ℚ) vp0011111010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011111010100_0 : Blocks := edgeBlocks% "full/vectors/0011111010100-V-0000.bin"
noncomputable def vp0011111010100 : Blocks := vp0011111010100_0
theorem coverp0011111010100 : Covers (-2003761639/1000000 : ℚ) vp0011111010100 := cover_leaf (by decide +kernel)
private noncomputable def vp001111101010_0 : Blocks := edgeBlocks% "full/vectors/001111101010-V-0000.bin"
noncomputable def vp001111101010 : Blocks := vp001111101010_0
private theorem bp0011111010100 : Branch 0 (-2003761639/2000000 : ℚ) vp001111101010 := by
  apply branch_left_normalized (c:=vp0011111010100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-2003761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-2003761639/1000000 : ℚ) by norm_num]
  exact coverp0011111010100
private noncomputable def ep0011111010101_0 : Blocks := edgeBlocks% "full/vectors/0011111010101-E-0000.bin"
noncomputable def ep0011111010101 : Blocks := ep0011111010101_0
private theorem idp0011111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111101010.list =
    C ((2:ℤ)^69) * horner X vp0011111010101.list + horner X ep0011111010101.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011111010101 : Branch 1 (-2003761639/2000000 : ℚ) vp001111101010 := by
  apply branch_checked idp0011111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-2003761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-2004761639/1000000 : ℚ) by norm_num]
  exact coverp0011111010101
theorem coverp001111101010 : Covers (-2003761639/2000000 : ℚ) vp001111101010 := join_branches bp0011111010100 bp0011111010101
private noncomputable def vp00111110101_0 : Blocks := edgeBlocks% "full/vectors/00111110101-V-0000.bin"
noncomputable def vp00111110101 : Blocks := vp00111110101_0
private theorem bp001111101010 : Branch 0 (-2003761639/4000000 : ℚ) vp00111110101 := by
  apply branch_left_normalized (c:=vp001111101010) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-2003761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-2003761639/2000000 : ℚ) by norm_num]
  exact coverp001111101010
private noncomputable def ep001111101011_0 : Blocks := edgeBlocks% "full/vectors/001111101011-E-0000.bin"
noncomputable def ep001111101011 : Blocks := ep001111101011_0
private theorem idp001111101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111110101.list =
    C ((2:ℤ)^119) * horner X vp001111101011.list + horner X ep001111101011.list := by
  exact edge_identity (B := (2:ℤ)^255) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111101011 : Branch 1 (-2003761639/4000000 : ℚ) vp00111110101 := by
  apply branch_checked idp001111101011 (by positivity) (by decide +kernel)
  rw [show 2*(-2003761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2005761639/2000000 : ℚ) by norm_num]
  exact coverp001111101011
theorem coverp00111110101 : Covers (-2003761639/4000000 : ℚ) vp00111110101 := join_branches bp001111101010 bp001111101011
private noncomputable def vp001111101001_0 : Blocks := edgeBlocks% "full/vectors/001111101001-V-0000.bin"
noncomputable def vp001111101001 : Blocks := vp001111101001_0
theorem coverp001111101001 : Covers (-2001761639/2000000 : ℚ) vp001111101001 := cover_leaf (by decide +kernel)
private noncomputable def vp001111101000_0 : Blocks := edgeBlocks% "full/vectors/001111101000-V-0000.bin"
noncomputable def vp001111101000 : Blocks := vp001111101000_0
theorem coverp001111101000 : Covers (-1999761639/2000000 : ℚ) vp001111101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00111110100_0 : Blocks := edgeBlocks% "full/vectors/00111110100-V-0000.bin"
noncomputable def vp00111110100 : Blocks := vp00111110100_0
private theorem bp001111101000 : Branch 0 (-1999761639/4000000 : ℚ) vp00111110100 := by
  apply branch_left_normalized (c:=vp001111101000) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-1999761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1999761639/2000000 : ℚ) by norm_num]
  exact coverp001111101000
private noncomputable def ep001111101001_0 : Blocks := edgeBlocks% "full/vectors/001111101001-E-0000.bin"
noncomputable def ep001111101001 : Blocks := ep001111101001_0
private theorem idp001111101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111110100.list =
    C ((2:ℤ)^121) * horner X vp001111101001.list + horner X ep001111101001.list := by
  exact edge_identity (B := (2:ℤ)^255) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111101001 : Branch 1 (-1999761639/4000000 : ℚ) vp00111110100 := by
  apply branch_checked idp001111101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1999761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-2001761639/2000000 : ℚ) by norm_num]
  exact coverp001111101001
theorem coverp00111110100 : Covers (-1999761639/4000000 : ℚ) vp00111110100 := join_branches bp001111101000 bp001111101001
private noncomputable def vp0011111010_0 : Blocks := edgeBlocks% "full/vectors/0011111010-V-0000.bin"
private noncomputable def vp0011111010_1 : Blocks := edgeBlocks% "full/vectors/0011111010-V-0001.bin"
noncomputable def vp0011111010 : Blocks := (Blocks.join vp0011111010_0 vp0011111010_1)
private theorem bp00111110100 : Branch 0 (-1999761639/8000000 : ℚ) vp0011111010 := by
  apply branch_left_normalized (c:=vp00111110100) (k:=0) (m:=108) (by decide +kernel)
  rw [show 2*(-1999761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1999761639/4000000 : ℚ) by norm_num]
  exact coverp00111110100
private noncomputable def ep00111110101_0 : Blocks := edgeBlocks% "full/vectors/00111110101-E-0000.bin"
private noncomputable def ep00111110101_1 : Blocks := edgeBlocks% "full/vectors/00111110101-E-0001.bin"
noncomputable def ep00111110101 : Blocks := (Blocks.join ep00111110101_0 ep00111110101_1)
private theorem idp00111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011111010.list =
    C ((2:ℤ)^220) * horner X vp00111110101.list + horner X ep00111110101.list := by
  exact edge_identity (B := (2:ℤ)^390) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111110101 : Branch 1 (-1999761639/8000000 : ℚ) vp0011111010 := by
  apply branch_checked idp00111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1999761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-2003761639/4000000 : ℚ) by norm_num]
  exact coverp00111110101
theorem coverp0011111010 : Covers (-1999761639/8000000 : ℚ) vp0011111010 := join_branches bp00111110100 bp00111110101
private noncomputable def vp001111101_0 : Blocks := edgeBlocks% "full/vectors/001111101-V-0000.bin"
private noncomputable def vp001111101_1 : Blocks := edgeBlocks% "full/vectors/001111101-V-0001.bin"
private noncomputable def vp001111101_2 : Blocks := edgeBlocks% "full/vectors/001111101-V-0002.bin"
noncomputable def vp001111101 : Blocks := (Blocks.join vp001111101_0 (Blocks.join vp001111101_1 vp001111101_2))
private theorem bp0011111010 : Branch 0 (-1999761639/16000000 : ℚ) vp001111101 := by
  apply branch_left_normalized (c:=vp0011111010) (k:=0) (m:=196) (by decide +kernel)
  rw [show 2*(-1999761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1999761639/8000000 : ℚ) by norm_num]
  exact coverp0011111010
private noncomputable def ep0011111011_0 : Blocks := edgeBlocks% "full/vectors/0011111011-E-0000.bin"
private noncomputable def ep0011111011_1 : Blocks := edgeBlocks% "full/vectors/0011111011-E-0001.bin"
private noncomputable def ep0011111011_2 : Blocks := edgeBlocks% "full/vectors/0011111011-E-0002.bin"
noncomputable def ep0011111011 : Blocks := (Blocks.join ep0011111011_0 (Blocks.join ep0011111011_1 ep0011111011_2))
private theorem idp0011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111101.list =
    C ((2:ℤ)^419) * horner X vp0011111011.list + horner X ep0011111011.list := by
  exact edge_identity (B := (2:ℤ)^658) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011111011 : Branch 1 (-1999761639/16000000 : ℚ) vp001111101 := by
  apply branch_checked idp0011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1999761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-2007761639/8000000 : ℚ) by norm_num]
  exact coverp0011111011
theorem coverp001111101 : Covers (-1999761639/16000000 : ℚ) vp001111101 := join_branches bp0011111010 bp0011111011
private noncomputable def vp001111100111_0 : Blocks := edgeBlocks% "full/vectors/001111100111-V-0000.bin"
noncomputable def vp001111100111 : Blocks := vp001111100111_0
theorem coverp001111100111 : Covers (-1997761639/2000000 : ℚ) vp001111100111 := cover_leaf (by decide +kernel)
private noncomputable def vp001111100110_0 : Blocks := edgeBlocks% "full/vectors/001111100110-V-0000.bin"
noncomputable def vp001111100110 : Blocks := vp001111100110_0
theorem coverp001111100110 : Covers (-1995761639/2000000 : ℚ) vp001111100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00111110011_0 : Blocks := edgeBlocks% "full/vectors/00111110011-V-0000.bin"
noncomputable def vp00111110011 : Blocks := vp00111110011_0
private theorem bp001111100110 : Branch 0 (-1995761639/4000000 : ℚ) vp00111110011 := by
  apply branch_left_normalized (c:=vp001111100110) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-1995761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1995761639/2000000 : ℚ) by norm_num]
  exact coverp001111100110
private noncomputable def ep001111100111_0 : Blocks := edgeBlocks% "full/vectors/001111100111-E-0000.bin"
noncomputable def ep001111100111 : Blocks := ep001111100111_0
private theorem idp001111100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111110011.list =
    C ((2:ℤ)^122) * horner X vp001111100111.list + horner X ep001111100111.list := by
  exact edge_identity (B := (2:ℤ)^257) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111100111 : Branch 1 (-1995761639/4000000 : ℚ) vp00111110011 := by
  apply branch_checked idp001111100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1995761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1997761639/2000000 : ℚ) by norm_num]
  exact coverp001111100111
theorem coverp00111110011 : Covers (-1995761639/4000000 : ℚ) vp00111110011 := join_branches bp001111100110 bp001111100111
private noncomputable def vp001111100101_0 : Blocks := edgeBlocks% "full/vectors/001111100101-V-0000.bin"
noncomputable def vp001111100101 : Blocks := vp001111100101_0
theorem coverp001111100101 : Covers (-1993761639/2000000 : ℚ) vp001111100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011111001001_0 : Blocks := edgeBlocks% "full/vectors/0011111001001-V-0000.bin"
noncomputable def vp0011111001001 : Blocks := vp0011111001001_0
theorem coverp0011111001001 : Covers (-1992761639/1000000 : ℚ) vp0011111001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011111001000_0 : Blocks := edgeBlocks% "full/vectors/0011111001000-V-0000.bin"
noncomputable def vp0011111001000 : Blocks := vp0011111001000_0
theorem coverp0011111001000 : Covers (-1991761639/1000000 : ℚ) vp0011111001000 := cover_leaf (by decide +kernel)
private noncomputable def vp001111100100_0 : Blocks := edgeBlocks% "full/vectors/001111100100-V-0000.bin"
noncomputable def vp001111100100 : Blocks := vp001111100100_0
private theorem bp0011111001000 : Branch 0 (-1991761639/2000000 : ℚ) vp001111100100 := by
  apply branch_left_normalized (c:=vp0011111001000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-1991761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1991761639/1000000 : ℚ) by norm_num]
  exact coverp0011111001000
private noncomputable def ep0011111001001_0 : Blocks := edgeBlocks% "full/vectors/0011111001001-E-0000.bin"
noncomputable def ep0011111001001 : Blocks := ep0011111001001_0
private theorem idp0011111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111100100.list =
    C ((2:ℤ)^71) * horner X vp0011111001001.list + horner X ep0011111001001.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011111001001 : Branch 1 (-1991761639/2000000 : ℚ) vp001111100100 := by
  apply branch_checked idp0011111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1991761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1992761639/1000000 : ℚ) by norm_num]
  exact coverp0011111001001
theorem coverp001111100100 : Covers (-1991761639/2000000 : ℚ) vp001111100100 := join_branches bp0011111001000 bp0011111001001
private noncomputable def vp00111110010_0 : Blocks := edgeBlocks% "full/vectors/00111110010-V-0000.bin"
noncomputable def vp00111110010 : Blocks := vp00111110010_0
private theorem bp001111100100 : Branch 0 (-1991761639/4000000 : ℚ) vp00111110010 := by
  apply branch_left_normalized (c:=vp001111100100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1991761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1991761639/2000000 : ℚ) by norm_num]
  exact coverp001111100100
private noncomputable def ep001111100101_0 : Blocks := edgeBlocks% "full/vectors/001111100101-E-0000.bin"
noncomputable def ep001111100101 : Blocks := ep001111100101_0
private theorem idp001111100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111110010.list =
    C ((2:ℤ)^123) * horner X vp001111100101.list + horner X ep001111100101.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111100101 : Branch 1 (-1991761639/4000000 : ℚ) vp00111110010 := by
  apply branch_checked idp001111100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1991761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1993761639/2000000 : ℚ) by norm_num]
  exact coverp001111100101
theorem coverp00111110010 : Covers (-1991761639/4000000 : ℚ) vp00111110010 := join_branches bp001111100100 bp001111100101
private noncomputable def vp0011111001_0 : Blocks := edgeBlocks% "full/vectors/0011111001-V-0000.bin"
private noncomputable def vp0011111001_1 : Blocks := edgeBlocks% "full/vectors/0011111001-V-0001.bin"
noncomputable def vp0011111001 : Blocks := (Blocks.join vp0011111001_0 vp0011111001_1)
private theorem bp00111110010 : Branch 0 (-1991761639/8000000 : ℚ) vp0011111001 := by
  apply branch_left_normalized (c:=vp00111110010) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-1991761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1991761639/4000000 : ℚ) by norm_num]
  exact coverp00111110010
private noncomputable def ep00111110011_0 : Blocks := edgeBlocks% "full/vectors/00111110011-E-0000.bin"
private noncomputable def ep00111110011_1 : Blocks := edgeBlocks% "full/vectors/00111110011-E-0001.bin"
noncomputable def ep00111110011 : Blocks := (Blocks.join ep00111110011_0 ep00111110011_1)
private theorem idp00111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011111001.list =
    C ((2:ℤ)^223) * horner X vp00111110011.list + horner X ep00111110011.list := by
  exact edge_identity (B := (2:ℤ)^394) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111110011 : Branch 1 (-1991761639/8000000 : ℚ) vp0011111001 := by
  apply branch_checked idp00111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1991761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1995761639/4000000 : ℚ) by norm_num]
  exact coverp00111110011
theorem coverp0011111001 : Covers (-1991761639/8000000 : ℚ) vp0011111001 := join_branches bp00111110010 bp00111110011
private noncomputable def vp0011111000111_0 : Blocks := edgeBlocks% "full/vectors/0011111000111-V-0000.bin"
noncomputable def vp0011111000111 : Blocks := vp0011111000111_0
theorem coverp0011111000111 : Covers (-1990761639/1000000 : ℚ) vp0011111000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011111000110_0 : Blocks := edgeBlocks% "full/vectors/0011111000110-V-0000.bin"
noncomputable def vp0011111000110 : Blocks := vp0011111000110_0
theorem coverp0011111000110 : Covers (-1989761639/1000000 : ℚ) vp0011111000110 := cover_leaf (by decide +kernel)
private noncomputable def vp001111100011_0 : Blocks := edgeBlocks% "full/vectors/001111100011-V-0000.bin"
noncomputable def vp001111100011 : Blocks := vp001111100011_0
private theorem bp0011111000110 : Branch 0 (-1989761639/2000000 : ℚ) vp001111100011 := by
  apply branch_left_normalized (c:=vp0011111000110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1989761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1989761639/1000000 : ℚ) by norm_num]
  exact coverp0011111000110
private noncomputable def ep0011111000111_0 : Blocks := edgeBlocks% "full/vectors/0011111000111-E-0000.bin"
noncomputable def ep0011111000111 : Blocks := ep0011111000111_0
private theorem idp0011111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111100011.list =
    C ((2:ℤ)^71) * horner X vp0011111000111.list + horner X ep0011111000111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011111000111 : Branch 1 (-1989761639/2000000 : ℚ) vp001111100011 := by
  apply branch_checked idp0011111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1989761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1990761639/1000000 : ℚ) by norm_num]
  exact coverp0011111000111
theorem coverp001111100011 : Covers (-1989761639/2000000 : ℚ) vp001111100011 := join_branches bp0011111000110 bp0011111000111
private noncomputable def vp0011111000101_0 : Blocks := edgeBlocks% "full/vectors/0011111000101-V-0000.bin"
noncomputable def vp0011111000101 : Blocks := vp0011111000101_0
theorem coverp0011111000101 : Covers (-1988761639/1000000 : ℚ) vp0011111000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011111000100_0 : Blocks := edgeBlocks% "full/vectors/0011111000100-V-0000.bin"
noncomputable def vp0011111000100 : Blocks := vp0011111000100_0
theorem coverp0011111000100 : Covers (-1987761639/1000000 : ℚ) vp0011111000100 := cover_leaf (by decide +kernel)
private noncomputable def vp001111100010_0 : Blocks := edgeBlocks% "full/vectors/001111100010-V-0000.bin"
noncomputable def vp001111100010 : Blocks := vp001111100010_0
private theorem bp0011111000100 : Branch 0 (-1987761639/2000000 : ℚ) vp001111100010 := by
  apply branch_left_normalized (c:=vp0011111000100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-1987761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1987761639/1000000 : ℚ) by norm_num]
  exact coverp0011111000100
private noncomputable def ep0011111000101_0 : Blocks := edgeBlocks% "full/vectors/0011111000101-E-0000.bin"
noncomputable def ep0011111000101 : Blocks := ep0011111000101_0
private theorem idp0011111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111100010.list =
    C ((2:ℤ)^71) * horner X vp0011111000101.list + horner X ep0011111000101.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011111000101 : Branch 1 (-1987761639/2000000 : ℚ) vp001111100010 := by
  apply branch_checked idp0011111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1987761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1988761639/1000000 : ℚ) by norm_num]
  exact coverp0011111000101
theorem coverp001111100010 : Covers (-1987761639/2000000 : ℚ) vp001111100010 := join_branches bp0011111000100 bp0011111000101
private noncomputable def vp00111110001_0 : Blocks := edgeBlocks% "full/vectors/00111110001-V-0000.bin"
noncomputable def vp00111110001 : Blocks := vp00111110001_0
private theorem bp001111100010 : Branch 0 (-1987761639/4000000 : ℚ) vp00111110001 := by
  apply branch_left_normalized (c:=vp001111100010) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1987761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1987761639/2000000 : ℚ) by norm_num]
  exact coverp001111100010
private noncomputable def ep001111100011_0 : Blocks := edgeBlocks% "full/vectors/001111100011-E-0000.bin"
noncomputable def ep001111100011 : Blocks := ep001111100011_0
private theorem idp001111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111110001.list =
    C ((2:ℤ)^122) * horner X vp001111100011.list + horner X ep001111100011.list := by
  exact edge_identity (B := (2:ℤ)^258) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111100011 : Branch 1 (-1987761639/4000000 : ℚ) vp00111110001 := by
  apply branch_checked idp001111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1987761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1989761639/2000000 : ℚ) by norm_num]
  exact coverp001111100011
theorem coverp00111110001 : Covers (-1987761639/4000000 : ℚ) vp00111110001 := join_branches bp001111100010 bp001111100011
private noncomputable def vp0011111000011_0 : Blocks := edgeBlocks% "full/vectors/0011111000011-V-0000.bin"
noncomputable def vp0011111000011 : Blocks := vp0011111000011_0
theorem coverp0011111000011 : Covers (-1986761639/1000000 : ℚ) vp0011111000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011111000010_0 : Blocks := edgeBlocks% "full/vectors/0011111000010-V-0000.bin"
noncomputable def vp0011111000010 : Blocks := vp0011111000010_0
theorem coverp0011111000010 : Covers (-1985761639/1000000 : ℚ) vp0011111000010 := cover_leaf (by decide +kernel)
private noncomputable def vp001111100001_0 : Blocks := edgeBlocks% "full/vectors/001111100001-V-0000.bin"
noncomputable def vp001111100001 : Blocks := vp001111100001_0
private theorem bp0011111000010 : Branch 0 (-1985761639/2000000 : ℚ) vp001111100001 := by
  apply branch_left_normalized (c:=vp0011111000010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1985761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1985761639/1000000 : ℚ) by norm_num]
  exact coverp0011111000010
private noncomputable def ep0011111000011_0 : Blocks := edgeBlocks% "full/vectors/0011111000011-E-0000.bin"
noncomputable def ep0011111000011 : Blocks := ep0011111000011_0
private theorem idp0011111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111100001.list =
    C ((2:ℤ)^71) * horner X vp0011111000011.list + horner X ep0011111000011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011111000011 : Branch 1 (-1985761639/2000000 : ℚ) vp001111100001 := by
  apply branch_checked idp0011111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1985761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1986761639/1000000 : ℚ) by norm_num]
  exact coverp0011111000011
theorem coverp001111100001 : Covers (-1985761639/2000000 : ℚ) vp001111100001 := join_branches bp0011111000010 bp0011111000011
private noncomputable def vp0011111000001_0 : Blocks := edgeBlocks% "full/vectors/0011111000001-V-0000.bin"
noncomputable def vp0011111000001 : Blocks := vp0011111000001_0
theorem coverp0011111000001 : Covers (-1984761639/1000000 : ℚ) vp0011111000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011111000000_0 : Blocks := edgeBlocks% "full/vectors/0011111000000-V-0000.bin"
noncomputable def vp0011111000000 : Blocks := vp0011111000000_0
theorem coverp0011111000000 : Covers (-1983761639/1000000 : ℚ) vp0011111000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001111100000_0 : Blocks := edgeBlocks% "full/vectors/001111100000-V-0000.bin"
noncomputable def vp001111100000 : Blocks := vp001111100000_0
private theorem bp0011111000000 : Branch 0 (-1983761639/2000000 : ℚ) vp001111100000 := by
  apply branch_left_normalized (c:=vp0011111000000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1983761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1983761639/1000000 : ℚ) by norm_num]
  exact coverp0011111000000
private noncomputable def ep0011111000001_0 : Blocks := edgeBlocks% "full/vectors/0011111000001-E-0000.bin"
noncomputable def ep0011111000001 : Blocks := ep0011111000001_0
private theorem idp0011111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111100000.list =
    C ((2:ℤ)^71) * horner X vp0011111000001.list + horner X ep0011111000001.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011111000001 : Branch 1 (-1983761639/2000000 : ℚ) vp001111100000 := by
  apply branch_checked idp0011111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1983761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1984761639/1000000 : ℚ) by norm_num]
  exact coverp0011111000001
theorem coverp001111100000 : Covers (-1983761639/2000000 : ℚ) vp001111100000 := join_branches bp0011111000000 bp0011111000001
private noncomputable def vp00111110000_0 : Blocks := edgeBlocks% "full/vectors/00111110000-V-0000.bin"
noncomputable def vp00111110000 : Blocks := vp00111110000_0
private theorem bp001111100000 : Branch 0 (-1983761639/4000000 : ℚ) vp00111110000 := by
  apply branch_left_normalized (c:=vp001111100000) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1983761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1983761639/2000000 : ℚ) by norm_num]
  exact coverp001111100000
private noncomputable def ep001111100001_0 : Blocks := edgeBlocks% "full/vectors/001111100001-E-0000.bin"
noncomputable def ep001111100001 : Blocks := ep001111100001_0
private theorem idp001111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111110000.list =
    C ((2:ℤ)^123) * horner X vp001111100001.list + horner X ep001111100001.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111100001 : Branch 1 (-1983761639/4000000 : ℚ) vp00111110000 := by
  apply branch_checked idp001111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1983761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1985761639/2000000 : ℚ) by norm_num]
  exact coverp001111100001
theorem coverp00111110000 : Covers (-1983761639/4000000 : ℚ) vp00111110000 := join_branches bp001111100000 bp001111100001
private noncomputable def vp0011111000_0 : Blocks := edgeBlocks% "full/vectors/0011111000-V-0000.bin"
private noncomputable def vp0011111000_1 : Blocks := edgeBlocks% "full/vectors/0011111000-V-0001.bin"
noncomputable def vp0011111000 : Blocks := (Blocks.join vp0011111000_0 vp0011111000_1)
private theorem bp00111110000 : Branch 0 (-1983761639/8000000 : ℚ) vp0011111000 := by
  apply branch_left_normalized (c:=vp00111110000) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-1983761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1983761639/4000000 : ℚ) by norm_num]
  exact coverp00111110000
private noncomputable def ep00111110001_0 : Blocks := edgeBlocks% "full/vectors/00111110001-E-0000.bin"
private noncomputable def ep00111110001_1 : Blocks := edgeBlocks% "full/vectors/00111110001-E-0001.bin"
noncomputable def ep00111110001 : Blocks := (Blocks.join ep00111110001_0 ep00111110001_1)
private theorem idp00111110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011111000.list =
    C ((2:ℤ)^222) * horner X vp00111110001.list + horner X ep00111110001.list := by
  exact edge_identity (B := (2:ℤ)^394) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111110001 : Branch 1 (-1983761639/8000000 : ℚ) vp0011111000 := by
  apply branch_checked idp00111110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1983761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1987761639/4000000 : ℚ) by norm_num]
  exact coverp00111110001
theorem coverp0011111000 : Covers (-1983761639/8000000 : ℚ) vp0011111000 := join_branches bp00111110000 bp00111110001
private noncomputable def vp001111100_0 : Blocks := edgeBlocks% "full/vectors/001111100-V-0000.bin"
private noncomputable def vp001111100_1 : Blocks := edgeBlocks% "full/vectors/001111100-V-0001.bin"
private noncomputable def vp001111100_2 : Blocks := edgeBlocks% "full/vectors/001111100-V-0002.bin"
noncomputable def vp001111100 : Blocks := (Blocks.join vp001111100_0 (Blocks.join vp001111100_1 vp001111100_2))
private theorem bp0011111000 : Branch 0 (-1983761639/16000000 : ℚ) vp001111100 := by
  apply branch_left_normalized (c:=vp0011111000) (k:=0) (m:=198) (by decide +kernel)
  rw [show 2*(-1983761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1983761639/8000000 : ℚ) by norm_num]
  exact coverp0011111000
private noncomputable def ep0011111001_0 : Blocks := edgeBlocks% "full/vectors/0011111001-E-0000.bin"
private noncomputable def ep0011111001_1 : Blocks := edgeBlocks% "full/vectors/0011111001-E-0001.bin"
private noncomputable def ep0011111001_2 : Blocks := edgeBlocks% "full/vectors/0011111001-E-0002.bin"
noncomputable def ep0011111001 : Blocks := (Blocks.join ep0011111001_0 (Blocks.join ep0011111001_1 ep0011111001_2))
private theorem idp0011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111100.list =
    C ((2:ℤ)^421) * horner X vp0011111001.list + horner X ep0011111001.list := by
  exact edge_identity (B := (2:ℤ)^664) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011111001 : Branch 1 (-1983761639/16000000 : ℚ) vp001111100 := by
  apply branch_checked idp0011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1983761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1991761639/8000000 : ℚ) by norm_num]
  exact coverp0011111001
theorem coverp001111100 : Covers (-1983761639/16000000 : ℚ) vp001111100 := join_branches bp0011111000 bp0011111001
private noncomputable def vp00111110_0 : Blocks := edgeBlocks% "full/vectors/00111110-V-0000.bin"
private noncomputable def vp00111110_1 : Blocks := edgeBlocks% "full/vectors/00111110-V-0001.bin"
private noncomputable def vp00111110_2 : Blocks := edgeBlocks% "full/vectors/00111110-V-0002.bin"
private noncomputable def vp00111110_3 : Blocks := edgeBlocks% "full/vectors/00111110-V-0003.bin"
private noncomputable def vp00111110_4 : Blocks := edgeBlocks% "full/vectors/00111110-V-0004.bin"
private noncomputable def vp00111110_5 : Blocks := edgeBlocks% "full/vectors/00111110-V-0005.bin"
noncomputable def vp00111110 : Blocks := (Blocks.join (Blocks.join vp00111110_0 (Blocks.join vp00111110_1 vp00111110_2)) (Blocks.join vp00111110_3 (Blocks.join vp00111110_4 vp00111110_5)))
private theorem bp001111100 : Branch 0 (-1983761639/32000000 : ℚ) vp00111110 := by
  apply branch_left_normalized (c:=vp001111100) (k:=0) (m:=374) (by decide +kernel)
  rw [show 2*(-1983761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1983761639/16000000 : ℚ) by norm_num]
  exact coverp001111100
private noncomputable def ep001111101_0 : Blocks := edgeBlocks% "full/vectors/001111101-E-0000.bin"
private noncomputable def ep001111101_1 : Blocks := edgeBlocks% "full/vectors/001111101-E-0001.bin"
private noncomputable def ep001111101_2 : Blocks := edgeBlocks% "full/vectors/001111101-E-0002.bin"
private noncomputable def ep001111101_3 : Blocks := edgeBlocks% "full/vectors/001111101-E-0003.bin"
private noncomputable def ep001111101_4 : Blocks := edgeBlocks% "full/vectors/001111101-E-0004.bin"
private noncomputable def ep001111101_5 : Blocks := edgeBlocks% "full/vectors/001111101-E-0005.bin"
noncomputable def ep001111101 : Blocks := (Blocks.join (Blocks.join ep001111101_0 (Blocks.join ep001111101_1 ep001111101_2)) (Blocks.join ep001111101_3 (Blocks.join ep001111101_4 ep001111101_5)))
private theorem idp001111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111110.list =
    C ((2:ℤ)^816) * horner X vp001111101.list + horner X ep001111101.list := by
  exact edge_identity (B := (2:ℤ)^1197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111101 : Branch 1 (-1983761639/32000000 : ℚ) vp00111110 := by
  apply branch_checked idp001111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1983761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1999761639/16000000 : ℚ) by norm_num]
  exact coverp001111101
theorem coverp00111110 : Covers (-1983761639/32000000 : ℚ) vp00111110 := join_branches bp001111100 bp001111101
private noncomputable def vp0011111_0 : Blocks := edgeBlocks% "full/vectors/0011111-V-0000.bin"
private noncomputable def vp0011111_1 : Blocks := edgeBlocks% "full/vectors/0011111-V-0001.bin"
private noncomputable def vp0011111_2 : Blocks := edgeBlocks% "full/vectors/0011111-V-0002.bin"
private noncomputable def vp0011111_3 : Blocks := edgeBlocks% "full/vectors/0011111-V-0003.bin"
private noncomputable def vp0011111_4 : Blocks := edgeBlocks% "full/vectors/0011111-V-0004.bin"
private noncomputable def vp0011111_5 : Blocks := edgeBlocks% "full/vectors/0011111-V-0005.bin"
private noncomputable def vp0011111_6 : Blocks := edgeBlocks% "full/vectors/0011111-V-0006.bin"
private noncomputable def vp0011111_7 : Blocks := edgeBlocks% "full/vectors/0011111-V-0007.bin"
private noncomputable def vp0011111_8 : Blocks := edgeBlocks% "full/vectors/0011111-V-0008.bin"
private noncomputable def vp0011111_9 : Blocks := edgeBlocks% "full/vectors/0011111-V-0009.bin"
private noncomputable def vp0011111_10 : Blocks := edgeBlocks% "full/vectors/0011111-V-0010.bin"
noncomputable def vp0011111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0011111_0 vp0011111_1) (Blocks.join vp0011111_2 (Blocks.join vp0011111_3 vp0011111_4))) (Blocks.join (Blocks.join vp0011111_5 (Blocks.join vp0011111_6 vp0011111_7)) (Blocks.join vp0011111_8 (Blocks.join vp0011111_9 vp0011111_10))))
private theorem bp00111110 : Branch 0 (-1983761639/64000000 : ℚ) vp0011111 := by
  apply branch_left_normalized (c:=vp00111110) (k:=0) (m:=721) (by decide +kernel)
  rw [show 2*(-1983761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1983761639/32000000 : ℚ) by norm_num]
  exact coverp00111110
private noncomputable def ep00111111_0 : Blocks := edgeBlocks% "full/vectors/00111111-E-0000.bin"
private noncomputable def ep00111111_1 : Blocks := edgeBlocks% "full/vectors/00111111-E-0001.bin"
private noncomputable def ep00111111_2 : Blocks := edgeBlocks% "full/vectors/00111111-E-0002.bin"
private noncomputable def ep00111111_3 : Blocks := edgeBlocks% "full/vectors/00111111-E-0003.bin"
private noncomputable def ep00111111_4 : Blocks := edgeBlocks% "full/vectors/00111111-E-0004.bin"
private noncomputable def ep00111111_5 : Blocks := edgeBlocks% "full/vectors/00111111-E-0005.bin"
private noncomputable def ep00111111_6 : Blocks := edgeBlocks% "full/vectors/00111111-E-0006.bin"
private noncomputable def ep00111111_7 : Blocks := edgeBlocks% "full/vectors/00111111-E-0007.bin"
private noncomputable def ep00111111_8 : Blocks := edgeBlocks% "full/vectors/00111111-E-0008.bin"
private noncomputable def ep00111111_9 : Blocks := edgeBlocks% "full/vectors/00111111-E-0009.bin"
private noncomputable def ep00111111_10 : Blocks := edgeBlocks% "full/vectors/00111111-E-0010.bin"
noncomputable def ep00111111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00111111_0 ep00111111_1) (Blocks.join ep00111111_2 (Blocks.join ep00111111_3 ep00111111_4))) (Blocks.join (Blocks.join ep00111111_5 (Blocks.join ep00111111_6 ep00111111_7)) (Blocks.join ep00111111_8 (Blocks.join ep00111111_9 ep00111111_10))))
private theorem idp00111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011111.list =
    C ((2:ℤ)^1600) * horner X vp00111111.list + horner X ep00111111.list := by
  exact edge_identity (B := (2:ℤ)^2253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111111 : Branch 1 (-1983761639/64000000 : ℚ) vp0011111 := by
  apply branch_checked idp00111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1983761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-2015761639/32000000 : ℚ) by norm_num]
  exact coverp00111111
theorem coverp0011111 : Covers (-1983761639/64000000 : ℚ) vp0011111 := join_branches bp00111110 bp00111111
end NextProof.EdgeFull

