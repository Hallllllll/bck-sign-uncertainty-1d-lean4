import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00104

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0011110111111_0 : Blocks := edgeBlocks% "full/vectors/0011110111111-V-0000.bin"
noncomputable def vp0011110111111 : Blocks := vp0011110111111_0
theorem coverp0011110111111 : Covers (-1982761639/1000000 : ℚ) vp0011110111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110111110_0 : Blocks := edgeBlocks% "full/vectors/0011110111110-V-0000.bin"
noncomputable def vp0011110111110 : Blocks := vp0011110111110_0
theorem coverp0011110111110 : Covers (-1981761639/1000000 : ℚ) vp0011110111110 := cover_leaf (by decide +kernel)
private noncomputable def vp001111011111_0 : Blocks := edgeBlocks% "full/vectors/001111011111-V-0000.bin"
noncomputable def vp001111011111 : Blocks := vp001111011111_0
private theorem bp0011110111110 : Branch 0 (-1981761639/2000000 : ℚ) vp001111011111 := by
  apply branch_left_normalized (c:=vp0011110111110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1981761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1981761639/1000000 : ℚ) by norm_num]
  exact coverp0011110111110
private noncomputable def ep0011110111111_0 : Blocks := edgeBlocks% "full/vectors/0011110111111-E-0000.bin"
noncomputable def ep0011110111111 : Blocks := ep0011110111111_0
private theorem idp0011110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111011111.list =
    C ((2:ℤ)^70) * horner X vp0011110111111.list + horner X ep0011110111111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110111111 : Branch 1 (-1981761639/2000000 : ℚ) vp001111011111 := by
  apply branch_checked idp0011110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1981761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1982761639/1000000 : ℚ) by norm_num]
  exact coverp0011110111111
theorem coverp001111011111 : Covers (-1981761639/2000000 : ℚ) vp001111011111 := join_branches bp0011110111110 bp0011110111111
private noncomputable def vp0011110111101_0 : Blocks := edgeBlocks% "full/vectors/0011110111101-V-0000.bin"
noncomputable def vp0011110111101 : Blocks := vp0011110111101_0
theorem coverp0011110111101 : Covers (-1980761639/1000000 : ℚ) vp0011110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110111100_0 : Blocks := edgeBlocks% "full/vectors/0011110111100-V-0000.bin"
noncomputable def vp0011110111100 : Blocks := vp0011110111100_0
theorem coverp0011110111100 : Covers (-1979761639/1000000 : ℚ) vp0011110111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001111011110_0 : Blocks := edgeBlocks% "full/vectors/001111011110-V-0000.bin"
noncomputable def vp001111011110 : Blocks := vp001111011110_0
private theorem bp0011110111100 : Branch 0 (-1979761639/2000000 : ℚ) vp001111011110 := by
  apply branch_left_normalized (c:=vp0011110111100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1979761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1979761639/1000000 : ℚ) by norm_num]
  exact coverp0011110111100
private noncomputable def ep0011110111101_0 : Blocks := edgeBlocks% "full/vectors/0011110111101-E-0000.bin"
noncomputable def ep0011110111101 : Blocks := ep0011110111101_0
private theorem idp0011110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111011110.list =
    C ((2:ℤ)^71) * horner X vp0011110111101.list + horner X ep0011110111101.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110111101 : Branch 1 (-1979761639/2000000 : ℚ) vp001111011110 := by
  apply branch_checked idp0011110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1979761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1980761639/1000000 : ℚ) by norm_num]
  exact coverp0011110111101
theorem coverp001111011110 : Covers (-1979761639/2000000 : ℚ) vp001111011110 := join_branches bp0011110111100 bp0011110111101
private noncomputable def vp00111101111_0 : Blocks := edgeBlocks% "full/vectors/00111101111-V-0000.bin"
noncomputable def vp00111101111 : Blocks := vp00111101111_0
private theorem bp001111011110 : Branch 0 (-1979761639/4000000 : ℚ) vp00111101111 := by
  apply branch_left_normalized (c:=vp001111011110) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1979761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1979761639/2000000 : ℚ) by norm_num]
  exact coverp001111011110
private noncomputable def ep001111011111_0 : Blocks := edgeBlocks% "full/vectors/001111011111-E-0000.bin"
noncomputable def ep001111011111 : Blocks := ep001111011111_0
private theorem idp001111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111101111.list =
    C ((2:ℤ)^123) * horner X vp001111011111.list + horner X ep001111011111.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111011111 : Branch 1 (-1979761639/4000000 : ℚ) vp00111101111 := by
  apply branch_checked idp001111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1979761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1981761639/2000000 : ℚ) by norm_num]
  exact coverp001111011111
theorem coverp00111101111 : Covers (-1979761639/4000000 : ℚ) vp00111101111 := join_branches bp001111011110 bp001111011111
private noncomputable def vp0011110111011_0 : Blocks := edgeBlocks% "full/vectors/0011110111011-V-0000.bin"
noncomputable def vp0011110111011 : Blocks := vp0011110111011_0
theorem coverp0011110111011 : Covers (-1978761639/1000000 : ℚ) vp0011110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110111010_0 : Blocks := edgeBlocks% "full/vectors/0011110111010-V-0000.bin"
noncomputable def vp0011110111010 : Blocks := vp0011110111010_0
theorem coverp0011110111010 : Covers (-1977761639/1000000 : ℚ) vp0011110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001111011101_0 : Blocks := edgeBlocks% "full/vectors/001111011101-V-0000.bin"
noncomputable def vp001111011101 : Blocks := vp001111011101_0
private theorem bp0011110111010 : Branch 0 (-1977761639/2000000 : ℚ) vp001111011101 := by
  apply branch_left_normalized (c:=vp0011110111010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1977761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1977761639/1000000 : ℚ) by norm_num]
  exact coverp0011110111010
private noncomputable def ep0011110111011_0 : Blocks := edgeBlocks% "full/vectors/0011110111011-E-0000.bin"
noncomputable def ep0011110111011 : Blocks := ep0011110111011_0
private theorem idp0011110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111011101.list =
    C ((2:ℤ)^71) * horner X vp0011110111011.list + horner X ep0011110111011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110111011 : Branch 1 (-1977761639/2000000 : ℚ) vp001111011101 := by
  apply branch_checked idp0011110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1977761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1978761639/1000000 : ℚ) by norm_num]
  exact coverp0011110111011
theorem coverp001111011101 : Covers (-1977761639/2000000 : ℚ) vp001111011101 := join_branches bp0011110111010 bp0011110111011
private noncomputable def vp0011110111001_0 : Blocks := edgeBlocks% "full/vectors/0011110111001-V-0000.bin"
noncomputable def vp0011110111001 : Blocks := vp0011110111001_0
theorem coverp0011110111001 : Covers (-1976761639/1000000 : ℚ) vp0011110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110111000_0 : Blocks := edgeBlocks% "full/vectors/0011110111000-V-0000.bin"
noncomputable def vp0011110111000 : Blocks := vp0011110111000_0
theorem coverp0011110111000 : Covers (-1975761639/1000000 : ℚ) vp0011110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp001111011100_0 : Blocks := edgeBlocks% "full/vectors/001111011100-V-0000.bin"
noncomputable def vp001111011100 : Blocks := vp001111011100_0
private theorem bp0011110111000 : Branch 0 (-1975761639/2000000 : ℚ) vp001111011100 := by
  apply branch_left_normalized (c:=vp0011110111000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-1975761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1975761639/1000000 : ℚ) by norm_num]
  exact coverp0011110111000
private noncomputable def ep0011110111001_0 : Blocks := edgeBlocks% "full/vectors/0011110111001-E-0000.bin"
noncomputable def ep0011110111001 : Blocks := ep0011110111001_0
private theorem idp0011110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111011100.list =
    C ((2:ℤ)^71) * horner X vp0011110111001.list + horner X ep0011110111001.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110111001 : Branch 1 (-1975761639/2000000 : ℚ) vp001111011100 := by
  apply branch_checked idp0011110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1975761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1976761639/1000000 : ℚ) by norm_num]
  exact coverp0011110111001
theorem coverp001111011100 : Covers (-1975761639/2000000 : ℚ) vp001111011100 := join_branches bp0011110111000 bp0011110111001
private noncomputable def vp00111101110_0 : Blocks := edgeBlocks% "full/vectors/00111101110-V-0000.bin"
noncomputable def vp00111101110 : Blocks := vp00111101110_0
private theorem bp001111011100 : Branch 0 (-1975761639/4000000 : ℚ) vp00111101110 := by
  apply branch_left_normalized (c:=vp001111011100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1975761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1975761639/2000000 : ℚ) by norm_num]
  exact coverp001111011100
private noncomputable def ep001111011101_0 : Blocks := edgeBlocks% "full/vectors/001111011101-E-0000.bin"
noncomputable def ep001111011101 : Blocks := ep001111011101_0
private theorem idp001111011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111101110.list =
    C ((2:ℤ)^122) * horner X vp001111011101.list + horner X ep001111011101.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111011101 : Branch 1 (-1975761639/4000000 : ℚ) vp00111101110 := by
  apply branch_checked idp001111011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1975761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1977761639/2000000 : ℚ) by norm_num]
  exact coverp001111011101
theorem coverp00111101110 : Covers (-1975761639/4000000 : ℚ) vp00111101110 := join_branches bp001111011100 bp001111011101
private noncomputable def vp0011110111_0 : Blocks := edgeBlocks% "full/vectors/0011110111-V-0000.bin"
private noncomputable def vp0011110111_1 : Blocks := edgeBlocks% "full/vectors/0011110111-V-0001.bin"
noncomputable def vp0011110111 : Blocks := (Blocks.join vp0011110111_0 vp0011110111_1)
private theorem bp00111101110 : Branch 0 (-1975761639/8000000 : ℚ) vp0011110111 := by
  apply branch_left_normalized (c:=vp00111101110) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-1975761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1975761639/4000000 : ℚ) by norm_num]
  exact coverp00111101110
private noncomputable def ep00111101111_0 : Blocks := edgeBlocks% "full/vectors/00111101111-E-0000.bin"
private noncomputable def ep00111101111_1 : Blocks := edgeBlocks% "full/vectors/00111101111-E-0001.bin"
noncomputable def ep00111101111 : Blocks := (Blocks.join ep00111101111_0 ep00111101111_1)
private theorem idp00111101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011110111.list =
    C ((2:ℤ)^223) * horner X vp00111101111.list + horner X ep00111101111.list := by
  exact edge_identity (B := (2:ℤ)^395) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111101111 : Branch 1 (-1975761639/8000000 : ℚ) vp0011110111 := by
  apply branch_checked idp00111101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1975761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1979761639/4000000 : ℚ) by norm_num]
  exact coverp00111101111
theorem coverp0011110111 : Covers (-1975761639/8000000 : ℚ) vp0011110111 := join_branches bp00111101110 bp00111101111
private noncomputable def vp0011110110111_0 : Blocks := edgeBlocks% "full/vectors/0011110110111-V-0000.bin"
noncomputable def vp0011110110111 : Blocks := vp0011110110111_0
theorem coverp0011110110111 : Covers (-1974761639/1000000 : ℚ) vp0011110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110110110_0 : Blocks := edgeBlocks% "full/vectors/0011110110110-V-0000.bin"
noncomputable def vp0011110110110 : Blocks := vp0011110110110_0
theorem coverp0011110110110 : Covers (-1973761639/1000000 : ℚ) vp0011110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp001111011011_0 : Blocks := edgeBlocks% "full/vectors/001111011011-V-0000.bin"
noncomputable def vp001111011011 : Blocks := vp001111011011_0
private theorem bp0011110110110 : Branch 0 (-1973761639/2000000 : ℚ) vp001111011011 := by
  apply branch_left_normalized (c:=vp0011110110110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1973761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1973761639/1000000 : ℚ) by norm_num]
  exact coverp0011110110110
private noncomputable def ep0011110110111_0 : Blocks := edgeBlocks% "full/vectors/0011110110111-E-0000.bin"
noncomputable def ep0011110110111 : Blocks := ep0011110110111_0
private theorem idp0011110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111011011.list =
    C ((2:ℤ)^71) * horner X vp0011110110111.list + horner X ep0011110110111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110110111 : Branch 1 (-1973761639/2000000 : ℚ) vp001111011011 := by
  apply branch_checked idp0011110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1973761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1974761639/1000000 : ℚ) by norm_num]
  exact coverp0011110110111
theorem coverp001111011011 : Covers (-1973761639/2000000 : ℚ) vp001111011011 := join_branches bp0011110110110 bp0011110110111
private noncomputable def vp0011110110101_0 : Blocks := edgeBlocks% "full/vectors/0011110110101-V-0000.bin"
noncomputable def vp0011110110101 : Blocks := vp0011110110101_0
theorem coverp0011110110101 : Covers (-1972761639/1000000 : ℚ) vp0011110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110110100_0 : Blocks := edgeBlocks% "full/vectors/0011110110100-V-0000.bin"
noncomputable def vp0011110110100 : Blocks := vp0011110110100_0
theorem coverp0011110110100 : Covers (-1971761639/1000000 : ℚ) vp0011110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001111011010_0 : Blocks := edgeBlocks% "full/vectors/001111011010-V-0000.bin"
noncomputable def vp001111011010 : Blocks := vp001111011010_0
private theorem bp0011110110100 : Branch 0 (-1971761639/2000000 : ℚ) vp001111011010 := by
  apply branch_left_normalized (c:=vp0011110110100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-1971761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1971761639/1000000 : ℚ) by norm_num]
  exact coverp0011110110100
private noncomputable def ep0011110110101_0 : Blocks := edgeBlocks% "full/vectors/0011110110101-E-0000.bin"
noncomputable def ep0011110110101 : Blocks := ep0011110110101_0
private theorem idp0011110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111011010.list =
    C ((2:ℤ)^71) * horner X vp0011110110101.list + horner X ep0011110110101.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110110101 : Branch 1 (-1971761639/2000000 : ℚ) vp001111011010 := by
  apply branch_checked idp0011110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1971761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1972761639/1000000 : ℚ) by norm_num]
  exact coverp0011110110101
theorem coverp001111011010 : Covers (-1971761639/2000000 : ℚ) vp001111011010 := join_branches bp0011110110100 bp0011110110101
private noncomputable def vp00111101101_0 : Blocks := edgeBlocks% "full/vectors/00111101101-V-0000.bin"
noncomputable def vp00111101101 : Blocks := vp00111101101_0
private theorem bp001111011010 : Branch 0 (-1971761639/4000000 : ℚ) vp00111101101 := by
  apply branch_left_normalized (c:=vp001111011010) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1971761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1971761639/2000000 : ℚ) by norm_num]
  exact coverp001111011010
private noncomputable def ep001111011011_0 : Blocks := edgeBlocks% "full/vectors/001111011011-E-0000.bin"
noncomputable def ep001111011011 : Blocks := ep001111011011_0
private theorem idp001111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111101101.list =
    C ((2:ℤ)^122) * horner X vp001111011011.list + horner X ep001111011011.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111011011 : Branch 1 (-1971761639/4000000 : ℚ) vp00111101101 := by
  apply branch_checked idp001111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1971761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1973761639/2000000 : ℚ) by norm_num]
  exact coverp001111011011
theorem coverp00111101101 : Covers (-1971761639/4000000 : ℚ) vp00111101101 := join_branches bp001111011010 bp001111011011
private noncomputable def vp0011110110011_0 : Blocks := edgeBlocks% "full/vectors/0011110110011-V-0000.bin"
noncomputable def vp0011110110011 : Blocks := vp0011110110011_0
theorem coverp0011110110011 : Covers (-1970761639/1000000 : ℚ) vp0011110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110110010_0 : Blocks := edgeBlocks% "full/vectors/0011110110010-V-0000.bin"
noncomputable def vp0011110110010 : Blocks := vp0011110110010_0
theorem coverp0011110110010 : Covers (-1969761639/1000000 : ℚ) vp0011110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001111011001_0 : Blocks := edgeBlocks% "full/vectors/001111011001-V-0000.bin"
noncomputable def vp001111011001 : Blocks := vp001111011001_0
private theorem bp0011110110010 : Branch 0 (-1969761639/2000000 : ℚ) vp001111011001 := by
  apply branch_left_normalized (c:=vp0011110110010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1969761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1969761639/1000000 : ℚ) by norm_num]
  exact coverp0011110110010
private noncomputable def ep0011110110011_0 : Blocks := edgeBlocks% "full/vectors/0011110110011-E-0000.bin"
noncomputable def ep0011110110011 : Blocks := ep0011110110011_0
private theorem idp0011110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111011001.list =
    C ((2:ℤ)^71) * horner X vp0011110110011.list + horner X ep0011110110011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110110011 : Branch 1 (-1969761639/2000000 : ℚ) vp001111011001 := by
  apply branch_checked idp0011110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1969761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1970761639/1000000 : ℚ) by norm_num]
  exact coverp0011110110011
theorem coverp001111011001 : Covers (-1969761639/2000000 : ℚ) vp001111011001 := join_branches bp0011110110010 bp0011110110011
private noncomputable def vp0011110110001_0 : Blocks := edgeBlocks% "full/vectors/0011110110001-V-0000.bin"
noncomputable def vp0011110110001 : Blocks := vp0011110110001_0
theorem coverp0011110110001 : Covers (-1968761639/1000000 : ℚ) vp0011110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110110000_0 : Blocks := edgeBlocks% "full/vectors/0011110110000-V-0000.bin"
noncomputable def vp0011110110000 : Blocks := vp0011110110000_0
theorem coverp0011110110000 : Covers (-1967761639/1000000 : ℚ) vp0011110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001111011000_0 : Blocks := edgeBlocks% "full/vectors/001111011000-V-0000.bin"
noncomputable def vp001111011000 : Blocks := vp001111011000_0
private theorem bp0011110110000 : Branch 0 (-1967761639/2000000 : ℚ) vp001111011000 := by
  apply branch_left_normalized (c:=vp0011110110000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1967761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1967761639/1000000 : ℚ) by norm_num]
  exact coverp0011110110000
private noncomputable def ep0011110110001_0 : Blocks := edgeBlocks% "full/vectors/0011110110001-E-0000.bin"
noncomputable def ep0011110110001 : Blocks := ep0011110110001_0
private theorem idp0011110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111011000.list =
    C ((2:ℤ)^71) * horner X vp0011110110001.list + horner X ep0011110110001.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110110001 : Branch 1 (-1967761639/2000000 : ℚ) vp001111011000 := by
  apply branch_checked idp0011110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1967761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1968761639/1000000 : ℚ) by norm_num]
  exact coverp0011110110001
theorem coverp001111011000 : Covers (-1967761639/2000000 : ℚ) vp001111011000 := join_branches bp0011110110000 bp0011110110001
private noncomputable def vp00111101100_0 : Blocks := edgeBlocks% "full/vectors/00111101100-V-0000.bin"
noncomputable def vp00111101100 : Blocks := vp00111101100_0
private theorem bp001111011000 : Branch 0 (-1967761639/4000000 : ℚ) vp00111101100 := by
  apply branch_left_normalized (c:=vp001111011000) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1967761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1967761639/2000000 : ℚ) by norm_num]
  exact coverp001111011000
private noncomputable def ep001111011001_0 : Blocks := edgeBlocks% "full/vectors/001111011001-E-0000.bin"
noncomputable def ep001111011001 : Blocks := ep001111011001_0
private theorem idp001111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111101100.list =
    C ((2:ℤ)^122) * horner X vp001111011001.list + horner X ep001111011001.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111011001 : Branch 1 (-1967761639/4000000 : ℚ) vp00111101100 := by
  apply branch_checked idp001111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1967761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1969761639/2000000 : ℚ) by norm_num]
  exact coverp001111011001
theorem coverp00111101100 : Covers (-1967761639/4000000 : ℚ) vp00111101100 := join_branches bp001111011000 bp001111011001
private noncomputable def vp0011110110_0 : Blocks := edgeBlocks% "full/vectors/0011110110-V-0000.bin"
private noncomputable def vp0011110110_1 : Blocks := edgeBlocks% "full/vectors/0011110110-V-0001.bin"
noncomputable def vp0011110110 : Blocks := (Blocks.join vp0011110110_0 vp0011110110_1)
private theorem bp00111101100 : Branch 0 (-1967761639/8000000 : ℚ) vp0011110110 := by
  apply branch_left_normalized (c:=vp00111101100) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-1967761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1967761639/4000000 : ℚ) by norm_num]
  exact coverp00111101100
private noncomputable def ep00111101101_0 : Blocks := edgeBlocks% "full/vectors/00111101101-E-0000.bin"
private noncomputable def ep00111101101_1 : Blocks := edgeBlocks% "full/vectors/00111101101-E-0001.bin"
noncomputable def ep00111101101 : Blocks := (Blocks.join ep00111101101_0 ep00111101101_1)
private theorem idp00111101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011110110.list =
    C ((2:ℤ)^223) * horner X vp00111101101.list + horner X ep00111101101.list := by
  exact edge_identity (B := (2:ℤ)^395) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111101101 : Branch 1 (-1967761639/8000000 : ℚ) vp0011110110 := by
  apply branch_checked idp00111101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1967761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1971761639/4000000 : ℚ) by norm_num]
  exact coverp00111101101
theorem coverp0011110110 : Covers (-1967761639/8000000 : ℚ) vp0011110110 := join_branches bp00111101100 bp00111101101
private noncomputable def vp001111011_0 : Blocks := edgeBlocks% "full/vectors/001111011-V-0000.bin"
private noncomputable def vp001111011_1 : Blocks := edgeBlocks% "full/vectors/001111011-V-0001.bin"
private noncomputable def vp001111011_2 : Blocks := edgeBlocks% "full/vectors/001111011-V-0002.bin"
noncomputable def vp001111011 : Blocks := (Blocks.join vp001111011_0 (Blocks.join vp001111011_1 vp001111011_2))
private theorem bp0011110110 : Branch 0 (-1967761639/16000000 : ℚ) vp001111011 := by
  apply branch_left_normalized (c:=vp0011110110) (k:=0) (m:=199) (by decide +kernel)
  rw [show 2*(-1967761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1967761639/8000000 : ℚ) by norm_num]
  exact coverp0011110110
private noncomputable def ep0011110111_0 : Blocks := edgeBlocks% "full/vectors/0011110111-E-0000.bin"
private noncomputable def ep0011110111_1 : Blocks := edgeBlocks% "full/vectors/0011110111-E-0001.bin"
private noncomputable def ep0011110111_2 : Blocks := edgeBlocks% "full/vectors/0011110111-E-0002.bin"
noncomputable def ep0011110111 : Blocks := (Blocks.join ep0011110111_0 (Blocks.join ep0011110111_1 ep0011110111_2))
private theorem idp0011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111011.list =
    C ((2:ℤ)^423) * horner X vp0011110111.list + horner X ep0011110111.list := by
  exact edge_identity (B := (2:ℤ)^666) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110111 : Branch 1 (-1967761639/16000000 : ℚ) vp001111011 := by
  apply branch_checked idp0011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1967761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1975761639/8000000 : ℚ) by norm_num]
  exact coverp0011110111
theorem coverp001111011 : Covers (-1967761639/16000000 : ℚ) vp001111011 := join_branches bp0011110110 bp0011110111
private noncomputable def vp0011110101111_0 : Blocks := edgeBlocks% "full/vectors/0011110101111-V-0000.bin"
noncomputable def vp0011110101111 : Blocks := vp0011110101111_0
theorem coverp0011110101111 : Covers (-1966761639/1000000 : ℚ) vp0011110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110101110_0 : Blocks := edgeBlocks% "full/vectors/0011110101110-V-0000.bin"
noncomputable def vp0011110101110 : Blocks := vp0011110101110_0
theorem coverp0011110101110 : Covers (-1965761639/1000000 : ℚ) vp0011110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp001111010111_0 : Blocks := edgeBlocks% "full/vectors/001111010111-V-0000.bin"
noncomputable def vp001111010111 : Blocks := vp001111010111_0
private theorem bp0011110101110 : Branch 0 (-1965761639/2000000 : ℚ) vp001111010111 := by
  apply branch_left_normalized (c:=vp0011110101110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1965761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1965761639/1000000 : ℚ) by norm_num]
  exact coverp0011110101110
private noncomputable def ep0011110101111_0 : Blocks := edgeBlocks% "full/vectors/0011110101111-E-0000.bin"
noncomputable def ep0011110101111 : Blocks := ep0011110101111_0
private theorem idp0011110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111010111.list =
    C ((2:ℤ)^71) * horner X vp0011110101111.list + horner X ep0011110101111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110101111 : Branch 1 (-1965761639/2000000 : ℚ) vp001111010111 := by
  apply branch_checked idp0011110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1965761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1966761639/1000000 : ℚ) by norm_num]
  exact coverp0011110101111
theorem coverp001111010111 : Covers (-1965761639/2000000 : ℚ) vp001111010111 := join_branches bp0011110101110 bp0011110101111
private noncomputable def vp0011110101101_0 : Blocks := edgeBlocks% "full/vectors/0011110101101-V-0000.bin"
noncomputable def vp0011110101101 : Blocks := vp0011110101101_0
theorem coverp0011110101101 : Covers (-1964761639/1000000 : ℚ) vp0011110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110101100_0 : Blocks := edgeBlocks% "full/vectors/0011110101100-V-0000.bin"
noncomputable def vp0011110101100 : Blocks := vp0011110101100_0
theorem coverp0011110101100 : Covers (-1963761639/1000000 : ℚ) vp0011110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp001111010110_0 : Blocks := edgeBlocks% "full/vectors/001111010110-V-0000.bin"
noncomputable def vp001111010110 : Blocks := vp001111010110_0
private theorem bp0011110101100 : Branch 0 (-1963761639/2000000 : ℚ) vp001111010110 := by
  apply branch_left_normalized (c:=vp0011110101100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1963761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1963761639/1000000 : ℚ) by norm_num]
  exact coverp0011110101100
private noncomputable def ep0011110101101_0 : Blocks := edgeBlocks% "full/vectors/0011110101101-E-0000.bin"
noncomputable def ep0011110101101 : Blocks := ep0011110101101_0
private theorem idp0011110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111010110.list =
    C ((2:ℤ)^70) * horner X vp0011110101101.list + horner X ep0011110101101.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110101101 : Branch 1 (-1963761639/2000000 : ℚ) vp001111010110 := by
  apply branch_checked idp0011110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1963761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1964761639/1000000 : ℚ) by norm_num]
  exact coverp0011110101101
theorem coverp001111010110 : Covers (-1963761639/2000000 : ℚ) vp001111010110 := join_branches bp0011110101100 bp0011110101101
private noncomputable def vp00111101011_0 : Blocks := edgeBlocks% "full/vectors/00111101011-V-0000.bin"
noncomputable def vp00111101011 : Blocks := vp00111101011_0
private theorem bp001111010110 : Branch 0 (-1963761639/4000000 : ℚ) vp00111101011 := by
  apply branch_left_normalized (c:=vp001111010110) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1963761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1963761639/2000000 : ℚ) by norm_num]
  exact coverp001111010110
private noncomputable def ep001111010111_0 : Blocks := edgeBlocks% "full/vectors/001111010111-E-0000.bin"
noncomputable def ep001111010111 : Blocks := ep001111010111_0
private theorem idp001111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111101011.list =
    C ((2:ℤ)^122) * horner X vp001111010111.list + horner X ep001111010111.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111010111 : Branch 1 (-1963761639/4000000 : ℚ) vp00111101011 := by
  apply branch_checked idp001111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1963761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1965761639/2000000 : ℚ) by norm_num]
  exact coverp001111010111
theorem coverp00111101011 : Covers (-1963761639/4000000 : ℚ) vp00111101011 := join_branches bp001111010110 bp001111010111
private noncomputable def vp0011110101011_0 : Blocks := edgeBlocks% "full/vectors/0011110101011-V-0000.bin"
noncomputable def vp0011110101011 : Blocks := vp0011110101011_0
theorem coverp0011110101011 : Covers (-1962761639/1000000 : ℚ) vp0011110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110101010_0 : Blocks := edgeBlocks% "full/vectors/0011110101010-V-0000.bin"
noncomputable def vp0011110101010 : Blocks := vp0011110101010_0
theorem coverp0011110101010 : Covers (-1961761639/1000000 : ℚ) vp0011110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp001111010101_0 : Blocks := edgeBlocks% "full/vectors/001111010101-V-0000.bin"
noncomputable def vp001111010101 : Blocks := vp001111010101_0
private theorem bp0011110101010 : Branch 0 (-1961761639/2000000 : ℚ) vp001111010101 := by
  apply branch_left_normalized (c:=vp0011110101010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1961761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1961761639/1000000 : ℚ) by norm_num]
  exact coverp0011110101010
private noncomputable def ep0011110101011_0 : Blocks := edgeBlocks% "full/vectors/0011110101011-E-0000.bin"
noncomputable def ep0011110101011 : Blocks := ep0011110101011_0
private theorem idp0011110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111010101.list =
    C ((2:ℤ)^71) * horner X vp0011110101011.list + horner X ep0011110101011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110101011 : Branch 1 (-1961761639/2000000 : ℚ) vp001111010101 := by
  apply branch_checked idp0011110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1961761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1962761639/1000000 : ℚ) by norm_num]
  exact coverp0011110101011
theorem coverp001111010101 : Covers (-1961761639/2000000 : ℚ) vp001111010101 := join_branches bp0011110101010 bp0011110101011
private noncomputable def vp0011110101001_0 : Blocks := edgeBlocks% "full/vectors/0011110101001-V-0000.bin"
noncomputable def vp0011110101001 : Blocks := vp0011110101001_0
theorem coverp0011110101001 : Covers (-1960761639/1000000 : ℚ) vp0011110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110101000_0 : Blocks := edgeBlocks% "full/vectors/0011110101000-V-0000.bin"
noncomputable def vp0011110101000 : Blocks := vp0011110101000_0
theorem coverp0011110101000 : Covers (-1959761639/1000000 : ℚ) vp0011110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp001111010100_0 : Blocks := edgeBlocks% "full/vectors/001111010100-V-0000.bin"
noncomputable def vp001111010100 : Blocks := vp001111010100_0
private theorem bp0011110101000 : Branch 0 (-1959761639/2000000 : ℚ) vp001111010100 := by
  apply branch_left_normalized (c:=vp0011110101000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1959761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1959761639/1000000 : ℚ) by norm_num]
  exact coverp0011110101000
private noncomputable def ep0011110101001_0 : Blocks := edgeBlocks% "full/vectors/0011110101001-E-0000.bin"
noncomputable def ep0011110101001 : Blocks := ep0011110101001_0
private theorem idp0011110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111010100.list =
    C ((2:ℤ)^70) * horner X vp0011110101001.list + horner X ep0011110101001.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110101001 : Branch 1 (-1959761639/2000000 : ℚ) vp001111010100 := by
  apply branch_checked idp0011110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1959761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1960761639/1000000 : ℚ) by norm_num]
  exact coverp0011110101001
theorem coverp001111010100 : Covers (-1959761639/2000000 : ℚ) vp001111010100 := join_branches bp0011110101000 bp0011110101001
private noncomputable def vp00111101010_0 : Blocks := edgeBlocks% "full/vectors/00111101010-V-0000.bin"
noncomputable def vp00111101010 : Blocks := vp00111101010_0
private theorem bp001111010100 : Branch 0 (-1959761639/4000000 : ℚ) vp00111101010 := by
  apply branch_left_normalized (c:=vp001111010100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1959761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1959761639/2000000 : ℚ) by norm_num]
  exact coverp001111010100
private noncomputable def ep001111010101_0 : Blocks := edgeBlocks% "full/vectors/001111010101-E-0000.bin"
noncomputable def ep001111010101 : Blocks := ep001111010101_0
private theorem idp001111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111101010.list =
    C ((2:ℤ)^122) * horner X vp001111010101.list + horner X ep001111010101.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111010101 : Branch 1 (-1959761639/4000000 : ℚ) vp00111101010 := by
  apply branch_checked idp001111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1959761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1961761639/2000000 : ℚ) by norm_num]
  exact coverp001111010101
theorem coverp00111101010 : Covers (-1959761639/4000000 : ℚ) vp00111101010 := join_branches bp001111010100 bp001111010101
private noncomputable def vp0011110101_0 : Blocks := edgeBlocks% "full/vectors/0011110101-V-0000.bin"
private noncomputable def vp0011110101_1 : Blocks := edgeBlocks% "full/vectors/0011110101-V-0001.bin"
noncomputable def vp0011110101 : Blocks := (Blocks.join vp0011110101_0 vp0011110101_1)
private theorem bp00111101010 : Branch 0 (-1959761639/8000000 : ℚ) vp0011110101 := by
  apply branch_left_normalized (c:=vp00111101010) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-1959761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1959761639/4000000 : ℚ) by norm_num]
  exact coverp00111101010
private noncomputable def ep00111101011_0 : Blocks := edgeBlocks% "full/vectors/00111101011-E-0000.bin"
private noncomputable def ep00111101011_1 : Blocks := edgeBlocks% "full/vectors/00111101011-E-0001.bin"
noncomputable def ep00111101011 : Blocks := (Blocks.join ep00111101011_0 ep00111101011_1)
private theorem idp00111101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011110101.list =
    C ((2:ℤ)^223) * horner X vp00111101011.list + horner X ep00111101011.list := by
  exact edge_identity (B := (2:ℤ)^395) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111101011 : Branch 1 (-1959761639/8000000 : ℚ) vp0011110101 := by
  apply branch_checked idp00111101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1959761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1963761639/4000000 : ℚ) by norm_num]
  exact coverp00111101011
theorem coverp0011110101 : Covers (-1959761639/8000000 : ℚ) vp0011110101 := join_branches bp00111101010 bp00111101011
private noncomputable def vp0011110100111_0 : Blocks := edgeBlocks% "full/vectors/0011110100111-V-0000.bin"
noncomputable def vp0011110100111 : Blocks := vp0011110100111_0
theorem coverp0011110100111 : Covers (-1958761639/1000000 : ℚ) vp0011110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110100110_0 : Blocks := edgeBlocks% "full/vectors/0011110100110-V-0000.bin"
noncomputable def vp0011110100110 : Blocks := vp0011110100110_0
theorem coverp0011110100110 : Covers (-1957761639/1000000 : ℚ) vp0011110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp001111010011_0 : Blocks := edgeBlocks% "full/vectors/001111010011-V-0000.bin"
noncomputable def vp001111010011 : Blocks := vp001111010011_0
private theorem bp0011110100110 : Branch 0 (-1957761639/2000000 : ℚ) vp001111010011 := by
  apply branch_left_normalized (c:=vp0011110100110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1957761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1957761639/1000000 : ℚ) by norm_num]
  exact coverp0011110100110
private noncomputable def ep0011110100111_0 : Blocks := edgeBlocks% "full/vectors/0011110100111-E-0000.bin"
noncomputable def ep0011110100111 : Blocks := ep0011110100111_0
private theorem idp0011110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111010011.list =
    C ((2:ℤ)^71) * horner X vp0011110100111.list + horner X ep0011110100111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110100111 : Branch 1 (-1957761639/2000000 : ℚ) vp001111010011 := by
  apply branch_checked idp0011110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1957761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1958761639/1000000 : ℚ) by norm_num]
  exact coverp0011110100111
theorem coverp001111010011 : Covers (-1957761639/2000000 : ℚ) vp001111010011 := join_branches bp0011110100110 bp0011110100111
private noncomputable def vp0011110100101_0 : Blocks := edgeBlocks% "full/vectors/0011110100101-V-0000.bin"
noncomputable def vp0011110100101 : Blocks := vp0011110100101_0
theorem coverp0011110100101 : Covers (-1956761639/1000000 : ℚ) vp0011110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110100100_0 : Blocks := edgeBlocks% "full/vectors/0011110100100-V-0000.bin"
noncomputable def vp0011110100100 : Blocks := vp0011110100100_0
theorem coverp0011110100100 : Covers (-1955761639/1000000 : ℚ) vp0011110100100 := cover_leaf (by decide +kernel)
private noncomputable def vp001111010010_0 : Blocks := edgeBlocks% "full/vectors/001111010010-V-0000.bin"
noncomputable def vp001111010010 : Blocks := vp001111010010_0
private theorem bp0011110100100 : Branch 0 (-1955761639/2000000 : ℚ) vp001111010010 := by
  apply branch_left_normalized (c:=vp0011110100100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1955761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1955761639/1000000 : ℚ) by norm_num]
  exact coverp0011110100100
private noncomputable def ep0011110100101_0 : Blocks := edgeBlocks% "full/vectors/0011110100101-E-0000.bin"
noncomputable def ep0011110100101 : Blocks := ep0011110100101_0
private theorem idp0011110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111010010.list =
    C ((2:ℤ)^70) * horner X vp0011110100101.list + horner X ep0011110100101.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110100101 : Branch 1 (-1955761639/2000000 : ℚ) vp001111010010 := by
  apply branch_checked idp0011110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1955761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1956761639/1000000 : ℚ) by norm_num]
  exact coverp0011110100101
theorem coverp001111010010 : Covers (-1955761639/2000000 : ℚ) vp001111010010 := join_branches bp0011110100100 bp0011110100101
private noncomputable def vp00111101001_0 : Blocks := edgeBlocks% "full/vectors/00111101001-V-0000.bin"
noncomputable def vp00111101001 : Blocks := vp00111101001_0
private theorem bp001111010010 : Branch 0 (-1955761639/4000000 : ℚ) vp00111101001 := by
  apply branch_left_normalized (c:=vp001111010010) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1955761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1955761639/2000000 : ℚ) by norm_num]
  exact coverp001111010010
private noncomputable def ep001111010011_0 : Blocks := edgeBlocks% "full/vectors/001111010011-E-0000.bin"
noncomputable def ep001111010011 : Blocks := ep001111010011_0
private theorem idp001111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111101001.list =
    C ((2:ℤ)^122) * horner X vp001111010011.list + horner X ep001111010011.list := by
  exact edge_identity (B := (2:ℤ)^259) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111010011 : Branch 1 (-1955761639/4000000 : ℚ) vp00111101001 := by
  apply branch_checked idp001111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1955761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1957761639/2000000 : ℚ) by norm_num]
  exact coverp001111010011
theorem coverp00111101001 : Covers (-1955761639/4000000 : ℚ) vp00111101001 := join_branches bp001111010010 bp001111010011
private noncomputable def vp0011110100011_0 : Blocks := edgeBlocks% "full/vectors/0011110100011-V-0000.bin"
noncomputable def vp0011110100011 : Blocks := vp0011110100011_0
theorem coverp0011110100011 : Covers (-1954761639/1000000 : ℚ) vp0011110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110100010_0 : Blocks := edgeBlocks% "full/vectors/0011110100010-V-0000.bin"
noncomputable def vp0011110100010 : Blocks := vp0011110100010_0
theorem coverp0011110100010 : Covers (-1953761639/1000000 : ℚ) vp0011110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp001111010001_0 : Blocks := edgeBlocks% "full/vectors/001111010001-V-0000.bin"
noncomputable def vp001111010001 : Blocks := vp001111010001_0
private theorem bp0011110100010 : Branch 0 (-1953761639/2000000 : ℚ) vp001111010001 := by
  apply branch_left_normalized (c:=vp0011110100010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1953761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1953761639/1000000 : ℚ) by norm_num]
  exact coverp0011110100010
private noncomputable def ep0011110100011_0 : Blocks := edgeBlocks% "full/vectors/0011110100011-E-0000.bin"
noncomputable def ep0011110100011 : Blocks := ep0011110100011_0
private theorem idp0011110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111010001.list =
    C ((2:ℤ)^71) * horner X vp0011110100011.list + horner X ep0011110100011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110100011 : Branch 1 (-1953761639/2000000 : ℚ) vp001111010001 := by
  apply branch_checked idp0011110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1953761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1954761639/1000000 : ℚ) by norm_num]
  exact coverp0011110100011
theorem coverp001111010001 : Covers (-1953761639/2000000 : ℚ) vp001111010001 := join_branches bp0011110100010 bp0011110100011
private noncomputable def vp0011110100001_0 : Blocks := edgeBlocks% "full/vectors/0011110100001-V-0000.bin"
noncomputable def vp0011110100001 : Blocks := vp0011110100001_0
theorem coverp0011110100001 : Covers (-1952761639/1000000 : ℚ) vp0011110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110100000_0 : Blocks := edgeBlocks% "full/vectors/0011110100000-V-0000.bin"
noncomputable def vp0011110100000 : Blocks := vp0011110100000_0
theorem coverp0011110100000 : Covers (-1951761639/1000000 : ℚ) vp0011110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp001111010000_0 : Blocks := edgeBlocks% "full/vectors/001111010000-V-0000.bin"
noncomputable def vp001111010000 : Blocks := vp001111010000_0
private theorem bp0011110100000 : Branch 0 (-1951761639/2000000 : ℚ) vp001111010000 := by
  apply branch_left_normalized (c:=vp0011110100000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1951761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1951761639/1000000 : ℚ) by norm_num]
  exact coverp0011110100000
private noncomputable def ep0011110100001_0 : Blocks := edgeBlocks% "full/vectors/0011110100001-E-0000.bin"
noncomputable def ep0011110100001 : Blocks := ep0011110100001_0
private theorem idp0011110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111010000.list =
    C ((2:ℤ)^71) * horner X vp0011110100001.list + horner X ep0011110100001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110100001 : Branch 1 (-1951761639/2000000 : ℚ) vp001111010000 := by
  apply branch_checked idp0011110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1951761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1952761639/1000000 : ℚ) by norm_num]
  exact coverp0011110100001
theorem coverp001111010000 : Covers (-1951761639/2000000 : ℚ) vp001111010000 := join_branches bp0011110100000 bp0011110100001
private noncomputable def vp00111101000_0 : Blocks := edgeBlocks% "full/vectors/00111101000-V-0000.bin"
noncomputable def vp00111101000 : Blocks := vp00111101000_0
private theorem bp001111010000 : Branch 0 (-1951761639/4000000 : ℚ) vp00111101000 := by
  apply branch_left_normalized (c:=vp001111010000) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1951761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1951761639/2000000 : ℚ) by norm_num]
  exact coverp001111010000
private noncomputable def ep001111010001_0 : Blocks := edgeBlocks% "full/vectors/001111010001-E-0000.bin"
noncomputable def ep001111010001 : Blocks := ep001111010001_0
private theorem idp001111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111101000.list =
    C ((2:ℤ)^123) * horner X vp001111010001.list + horner X ep001111010001.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111010001 : Branch 1 (-1951761639/4000000 : ℚ) vp00111101000 := by
  apply branch_checked idp001111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1951761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1953761639/2000000 : ℚ) by norm_num]
  exact coverp001111010001
theorem coverp00111101000 : Covers (-1951761639/4000000 : ℚ) vp00111101000 := join_branches bp001111010000 bp001111010001
private noncomputable def vp0011110100_0 : Blocks := edgeBlocks% "full/vectors/0011110100-V-0000.bin"
private noncomputable def vp0011110100_1 : Blocks := edgeBlocks% "full/vectors/0011110100-V-0001.bin"
noncomputable def vp0011110100 : Blocks := (Blocks.join vp0011110100_0 vp0011110100_1)
private theorem bp00111101000 : Branch 0 (-1951761639/8000000 : ℚ) vp0011110100 := by
  apply branch_left_normalized (c:=vp00111101000) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-1951761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1951761639/4000000 : ℚ) by norm_num]
  exact coverp00111101000
private noncomputable def ep00111101001_0 : Blocks := edgeBlocks% "full/vectors/00111101001-E-0000.bin"
private noncomputable def ep00111101001_1 : Blocks := edgeBlocks% "full/vectors/00111101001-E-0001.bin"
noncomputable def ep00111101001 : Blocks := (Blocks.join ep00111101001_0 ep00111101001_1)
private theorem idp00111101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011110100.list =
    C ((2:ℤ)^225) * horner X vp00111101001.list + horner X ep00111101001.list := by
  exact edge_identity (B := (2:ℤ)^397) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111101001 : Branch 1 (-1951761639/8000000 : ℚ) vp0011110100 := by
  apply branch_checked idp00111101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1951761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1955761639/4000000 : ℚ) by norm_num]
  exact coverp00111101001
theorem coverp0011110100 : Covers (-1951761639/8000000 : ℚ) vp0011110100 := join_branches bp00111101000 bp00111101001
private noncomputable def vp001111010_0 : Blocks := edgeBlocks% "full/vectors/001111010-V-0000.bin"
private noncomputable def vp001111010_1 : Blocks := edgeBlocks% "full/vectors/001111010-V-0001.bin"
private noncomputable def vp001111010_2 : Blocks := edgeBlocks% "full/vectors/001111010-V-0002.bin"
noncomputable def vp001111010 : Blocks := (Blocks.join vp001111010_0 (Blocks.join vp001111010_1 vp001111010_2))
private theorem bp0011110100 : Branch 0 (-1951761639/16000000 : ℚ) vp001111010 := by
  apply branch_left_normalized (c:=vp0011110100) (k:=0) (m:=200) (by decide +kernel)
  rw [show 2*(-1951761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1951761639/8000000 : ℚ) by norm_num]
  exact coverp0011110100
private noncomputable def ep0011110101_0 : Blocks := edgeBlocks% "full/vectors/0011110101-E-0000.bin"
private noncomputable def ep0011110101_1 : Blocks := edgeBlocks% "full/vectors/0011110101-E-0001.bin"
private noncomputable def ep0011110101_2 : Blocks := edgeBlocks% "full/vectors/0011110101-E-0002.bin"
noncomputable def ep0011110101 : Blocks := (Blocks.join ep0011110101_0 (Blocks.join ep0011110101_1 ep0011110101_2))
private theorem idp0011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111010.list =
    C ((2:ℤ)^425) * horner X vp0011110101.list + horner X ep0011110101.list := by
  exact edge_identity (B := (2:ℤ)^668) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110101 : Branch 1 (-1951761639/16000000 : ℚ) vp001111010 := by
  apply branch_checked idp0011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1951761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1959761639/8000000 : ℚ) by norm_num]
  exact coverp0011110101
theorem coverp001111010 : Covers (-1951761639/16000000 : ℚ) vp001111010 := join_branches bp0011110100 bp0011110101
private noncomputable def vp00111101_0 : Blocks := edgeBlocks% "full/vectors/00111101-V-0000.bin"
private noncomputable def vp00111101_1 : Blocks := edgeBlocks% "full/vectors/00111101-V-0001.bin"
private noncomputable def vp00111101_2 : Blocks := edgeBlocks% "full/vectors/00111101-V-0002.bin"
private noncomputable def vp00111101_3 : Blocks := edgeBlocks% "full/vectors/00111101-V-0003.bin"
private noncomputable def vp00111101_4 : Blocks := edgeBlocks% "full/vectors/00111101-V-0004.bin"
private noncomputable def vp00111101_5 : Blocks := edgeBlocks% "full/vectors/00111101-V-0005.bin"
noncomputable def vp00111101 : Blocks := (Blocks.join (Blocks.join vp00111101_0 (Blocks.join vp00111101_1 vp00111101_2)) (Blocks.join vp00111101_3 (Blocks.join vp00111101_4 vp00111101_5)))
private theorem bp001111010 : Branch 0 (-1951761639/32000000 : ℚ) vp00111101 := by
  apply branch_left_normalized (c:=vp001111010) (k:=0) (m:=377) (by decide +kernel)
  rw [show 2*(-1951761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1951761639/16000000 : ℚ) by norm_num]
  exact coverp001111010
private noncomputable def ep001111011_0 : Blocks := edgeBlocks% "full/vectors/001111011-E-0000.bin"
private noncomputable def ep001111011_1 : Blocks := edgeBlocks% "full/vectors/001111011-E-0001.bin"
private noncomputable def ep001111011_2 : Blocks := edgeBlocks% "full/vectors/001111011-E-0002.bin"
private noncomputable def ep001111011_3 : Blocks := edgeBlocks% "full/vectors/001111011-E-0003.bin"
private noncomputable def ep001111011_4 : Blocks := edgeBlocks% "full/vectors/001111011-E-0004.bin"
private noncomputable def ep001111011_5 : Blocks := edgeBlocks% "full/vectors/001111011-E-0005.bin"
noncomputable def ep001111011 : Blocks := (Blocks.join (Blocks.join ep001111011_0 (Blocks.join ep001111011_1 ep001111011_2)) (Blocks.join ep001111011_3 (Blocks.join ep001111011_4 ep001111011_5)))
private theorem idp001111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111101.list =
    C ((2:ℤ)^822) * horner X vp001111011.list + horner X ep001111011.list := by
  exact edge_identity (B := (2:ℤ)^1207) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111011 : Branch 1 (-1951761639/32000000 : ℚ) vp00111101 := by
  apply branch_checked idp001111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1951761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1967761639/16000000 : ℚ) by norm_num]
  exact coverp001111011
theorem coverp00111101 : Covers (-1951761639/32000000 : ℚ) vp00111101 := join_branches bp001111010 bp001111011
private noncomputable def vp0011110011111_0 : Blocks := edgeBlocks% "full/vectors/0011110011111-V-0000.bin"
noncomputable def vp0011110011111 : Blocks := vp0011110011111_0
theorem coverp0011110011111 : Covers (-1950761639/1000000 : ℚ) vp0011110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110011110_0 : Blocks := edgeBlocks% "full/vectors/0011110011110-V-0000.bin"
noncomputable def vp0011110011110 : Blocks := vp0011110011110_0
theorem coverp0011110011110 : Covers (-1949761639/1000000 : ℚ) vp0011110011110 := cover_leaf (by decide +kernel)
private noncomputable def vp001111001111_0 : Blocks := edgeBlocks% "full/vectors/001111001111-V-0000.bin"
noncomputable def vp001111001111 : Blocks := vp001111001111_0
private theorem bp0011110011110 : Branch 0 (-1949761639/2000000 : ℚ) vp001111001111 := by
  apply branch_left_normalized (c:=vp0011110011110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1949761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1949761639/1000000 : ℚ) by norm_num]
  exact coverp0011110011110
private noncomputable def ep0011110011111_0 : Blocks := edgeBlocks% "full/vectors/0011110011111-E-0000.bin"
noncomputable def ep0011110011111 : Blocks := ep0011110011111_0
private theorem idp0011110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111001111.list =
    C ((2:ℤ)^72) * horner X vp0011110011111.list + horner X ep0011110011111.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110011111 : Branch 1 (-1949761639/2000000 : ℚ) vp001111001111 := by
  apply branch_checked idp0011110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1949761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1950761639/1000000 : ℚ) by norm_num]
  exact coverp0011110011111
theorem coverp001111001111 : Covers (-1949761639/2000000 : ℚ) vp001111001111 := join_branches bp0011110011110 bp0011110011111
private noncomputable def vp0011110011101_0 : Blocks := edgeBlocks% "full/vectors/0011110011101-V-0000.bin"
noncomputable def vp0011110011101 : Blocks := vp0011110011101_0
theorem coverp0011110011101 : Covers (-1948761639/1000000 : ℚ) vp0011110011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110011100_0 : Blocks := edgeBlocks% "full/vectors/0011110011100-V-0000.bin"
noncomputable def vp0011110011100 : Blocks := vp0011110011100_0
theorem coverp0011110011100 : Covers (-1947761639/1000000 : ℚ) vp0011110011100 := cover_leaf (by decide +kernel)
private noncomputable def vp001111001110_0 : Blocks := edgeBlocks% "full/vectors/001111001110-V-0000.bin"
noncomputable def vp001111001110 : Blocks := vp001111001110_0
private theorem bp0011110011100 : Branch 0 (-1947761639/2000000 : ℚ) vp001111001110 := by
  apply branch_left_normalized (c:=vp0011110011100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1947761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1947761639/1000000 : ℚ) by norm_num]
  exact coverp0011110011100
private noncomputable def ep0011110011101_0 : Blocks := edgeBlocks% "full/vectors/0011110011101-E-0000.bin"
noncomputable def ep0011110011101 : Blocks := ep0011110011101_0
private theorem idp0011110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111001110.list =
    C ((2:ℤ)^71) * horner X vp0011110011101.list + horner X ep0011110011101.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110011101 : Branch 1 (-1947761639/2000000 : ℚ) vp001111001110 := by
  apply branch_checked idp0011110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1947761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1948761639/1000000 : ℚ) by norm_num]
  exact coverp0011110011101
theorem coverp001111001110 : Covers (-1947761639/2000000 : ℚ) vp001111001110 := join_branches bp0011110011100 bp0011110011101
private noncomputable def vp00111100111_0 : Blocks := edgeBlocks% "full/vectors/00111100111-V-0000.bin"
noncomputable def vp00111100111 : Blocks := vp00111100111_0
private theorem bp001111001110 : Branch 0 (-1947761639/4000000 : ℚ) vp00111100111 := by
  apply branch_left_normalized (c:=vp001111001110) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1947761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1947761639/2000000 : ℚ) by norm_num]
  exact coverp001111001110
private noncomputable def ep001111001111_0 : Blocks := edgeBlocks% "full/vectors/001111001111-E-0000.bin"
noncomputable def ep001111001111 : Blocks := ep001111001111_0
private theorem idp001111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111100111.list =
    C ((2:ℤ)^124) * horner X vp001111001111.list + horner X ep001111001111.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111001111 : Branch 1 (-1947761639/4000000 : ℚ) vp00111100111 := by
  apply branch_checked idp001111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1947761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1949761639/2000000 : ℚ) by norm_num]
  exact coverp001111001111
theorem coverp00111100111 : Covers (-1947761639/4000000 : ℚ) vp00111100111 := join_branches bp001111001110 bp001111001111
private noncomputable def vp0011110011011_0 : Blocks := edgeBlocks% "full/vectors/0011110011011-V-0000.bin"
noncomputable def vp0011110011011 : Blocks := vp0011110011011_0
theorem coverp0011110011011 : Covers (-1946761639/1000000 : ℚ) vp0011110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110011010_0 : Blocks := edgeBlocks% "full/vectors/0011110011010-V-0000.bin"
noncomputable def vp0011110011010 : Blocks := vp0011110011010_0
theorem coverp0011110011010 : Covers (-1945761639/1000000 : ℚ) vp0011110011010 := cover_leaf (by decide +kernel)
private noncomputable def vp001111001101_0 : Blocks := edgeBlocks% "full/vectors/001111001101-V-0000.bin"
noncomputable def vp001111001101 : Blocks := vp001111001101_0
private theorem bp0011110011010 : Branch 0 (-1945761639/2000000 : ℚ) vp001111001101 := by
  apply branch_left_normalized (c:=vp0011110011010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1945761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1945761639/1000000 : ℚ) by norm_num]
  exact coverp0011110011010
private noncomputable def ep0011110011011_0 : Blocks := edgeBlocks% "full/vectors/0011110011011-E-0000.bin"
noncomputable def ep0011110011011 : Blocks := ep0011110011011_0
private theorem idp0011110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111001101.list =
    C ((2:ℤ)^72) * horner X vp0011110011011.list + horner X ep0011110011011.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110011011 : Branch 1 (-1945761639/2000000 : ℚ) vp001111001101 := by
  apply branch_checked idp0011110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1945761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1946761639/1000000 : ℚ) by norm_num]
  exact coverp0011110011011
theorem coverp001111001101 : Covers (-1945761639/2000000 : ℚ) vp001111001101 := join_branches bp0011110011010 bp0011110011011
private noncomputable def vp0011110011001_0 : Blocks := edgeBlocks% "full/vectors/0011110011001-V-0000.bin"
noncomputable def vp0011110011001 : Blocks := vp0011110011001_0
theorem coverp0011110011001 : Covers (-1944761639/1000000 : ℚ) vp0011110011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110011000_0 : Blocks := edgeBlocks% "full/vectors/0011110011000-V-0000.bin"
noncomputable def vp0011110011000 : Blocks := vp0011110011000_0
theorem coverp0011110011000 : Covers (-1943761639/1000000 : ℚ) vp0011110011000 := cover_leaf (by decide +kernel)
private noncomputable def vp001111001100_0 : Blocks := edgeBlocks% "full/vectors/001111001100-V-0000.bin"
noncomputable def vp001111001100 : Blocks := vp001111001100_0
private theorem bp0011110011000 : Branch 0 (-1943761639/2000000 : ℚ) vp001111001100 := by
  apply branch_left_normalized (c:=vp0011110011000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1943761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1943761639/1000000 : ℚ) by norm_num]
  exact coverp0011110011000
private noncomputable def ep0011110011001_0 : Blocks := edgeBlocks% "full/vectors/0011110011001-E-0000.bin"
noncomputable def ep0011110011001 : Blocks := ep0011110011001_0
private theorem idp0011110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111001100.list =
    C ((2:ℤ)^71) * horner X vp0011110011001.list + horner X ep0011110011001.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110011001 : Branch 1 (-1943761639/2000000 : ℚ) vp001111001100 := by
  apply branch_checked idp0011110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1943761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1944761639/1000000 : ℚ) by norm_num]
  exact coverp0011110011001
theorem coverp001111001100 : Covers (-1943761639/2000000 : ℚ) vp001111001100 := join_branches bp0011110011000 bp0011110011001
private noncomputable def vp00111100110_0 : Blocks := edgeBlocks% "full/vectors/00111100110-V-0000.bin"
noncomputable def vp00111100110 : Blocks := vp00111100110_0
private theorem bp001111001100 : Branch 0 (-1943761639/4000000 : ℚ) vp00111100110 := by
  apply branch_left_normalized (c:=vp001111001100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1943761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1943761639/2000000 : ℚ) by norm_num]
  exact coverp001111001100
private noncomputable def ep001111001101_0 : Blocks := edgeBlocks% "full/vectors/001111001101-E-0000.bin"
noncomputable def ep001111001101 : Blocks := ep001111001101_0
private theorem idp001111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111100110.list =
    C ((2:ℤ)^124) * horner X vp001111001101.list + horner X ep001111001101.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111001101 : Branch 1 (-1943761639/4000000 : ℚ) vp00111100110 := by
  apply branch_checked idp001111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1943761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1945761639/2000000 : ℚ) by norm_num]
  exact coverp001111001101
theorem coverp00111100110 : Covers (-1943761639/4000000 : ℚ) vp00111100110 := join_branches bp001111001100 bp001111001101
private noncomputable def vp0011110011_0 : Blocks := edgeBlocks% "full/vectors/0011110011-V-0000.bin"
private noncomputable def vp0011110011_1 : Blocks := edgeBlocks% "full/vectors/0011110011-V-0001.bin"
noncomputable def vp0011110011 : Blocks := (Blocks.join vp0011110011_0 vp0011110011_1)
private theorem bp00111100110 : Branch 0 (-1943761639/8000000 : ℚ) vp0011110011 := by
  apply branch_left_normalized (c:=vp00111100110) (k:=0) (m:=111) (by decide +kernel)
  rw [show 2*(-1943761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1943761639/4000000 : ℚ) by norm_num]
  exact coverp00111100110
private noncomputable def ep00111100111_0 : Blocks := edgeBlocks% "full/vectors/00111100111-E-0000.bin"
private noncomputable def ep00111100111_1 : Blocks := edgeBlocks% "full/vectors/00111100111-E-0001.bin"
noncomputable def ep00111100111 : Blocks := (Blocks.join ep00111100111_0 ep00111100111_1)
private theorem idp00111100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011110011.list =
    C ((2:ℤ)^224) * horner X vp00111100111.list + horner X ep00111100111.list := by
  exact edge_identity (B := (2:ℤ)^397) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111100111 : Branch 1 (-1943761639/8000000 : ℚ) vp0011110011 := by
  apply branch_checked idp00111100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1943761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1947761639/4000000 : ℚ) by norm_num]
  exact coverp00111100111
theorem coverp0011110011 : Covers (-1943761639/8000000 : ℚ) vp0011110011 := join_branches bp00111100110 bp00111100111
private noncomputable def vp0011110010111_0 : Blocks := edgeBlocks% "full/vectors/0011110010111-V-0000.bin"
noncomputable def vp0011110010111 : Blocks := vp0011110010111_0
theorem coverp0011110010111 : Covers (-1942761639/1000000 : ℚ) vp0011110010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110010110_0 : Blocks := edgeBlocks% "full/vectors/0011110010110-V-0000.bin"
noncomputable def vp0011110010110 : Blocks := vp0011110010110_0
theorem coverp0011110010110 : Covers (-1941761639/1000000 : ℚ) vp0011110010110 := cover_leaf (by decide +kernel)
private noncomputable def vp001111001011_0 : Blocks := edgeBlocks% "full/vectors/001111001011-V-0000.bin"
noncomputable def vp001111001011 : Blocks := vp001111001011_0
private theorem bp0011110010110 : Branch 0 (-1941761639/2000000 : ℚ) vp001111001011 := by
  apply branch_left_normalized (c:=vp0011110010110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1941761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1941761639/1000000 : ℚ) by norm_num]
  exact coverp0011110010110
private noncomputable def ep0011110010111_0 : Blocks := edgeBlocks% "full/vectors/0011110010111-E-0000.bin"
noncomputable def ep0011110010111 : Blocks := ep0011110010111_0
private theorem idp0011110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111001011.list =
    C ((2:ℤ)^71) * horner X vp0011110010111.list + horner X ep0011110010111.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110010111 : Branch 1 (-1941761639/2000000 : ℚ) vp001111001011 := by
  apply branch_checked idp0011110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1941761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1942761639/1000000 : ℚ) by norm_num]
  exact coverp0011110010111
theorem coverp001111001011 : Covers (-1941761639/2000000 : ℚ) vp001111001011 := join_branches bp0011110010110 bp0011110010111
private noncomputable def vp0011110010101_0 : Blocks := edgeBlocks% "full/vectors/0011110010101-V-0000.bin"
noncomputable def vp0011110010101 : Blocks := vp0011110010101_0
theorem coverp0011110010101 : Covers (-1940761639/1000000 : ℚ) vp0011110010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110010100_0 : Blocks := edgeBlocks% "full/vectors/0011110010100-V-0000.bin"
noncomputable def vp0011110010100 : Blocks := vp0011110010100_0
theorem coverp0011110010100 : Covers (-1939761639/1000000 : ℚ) vp0011110010100 := cover_leaf (by decide +kernel)
private noncomputable def vp001111001010_0 : Blocks := edgeBlocks% "full/vectors/001111001010-V-0000.bin"
noncomputable def vp001111001010 : Blocks := vp001111001010_0
private theorem bp0011110010100 : Branch 0 (-1939761639/2000000 : ℚ) vp001111001010 := by
  apply branch_left_normalized (c:=vp0011110010100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1939761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1939761639/1000000 : ℚ) by norm_num]
  exact coverp0011110010100
private noncomputable def ep0011110010101_0 : Blocks := edgeBlocks% "full/vectors/0011110010101-E-0000.bin"
noncomputable def ep0011110010101 : Blocks := ep0011110010101_0
private theorem idp0011110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111001010.list =
    C ((2:ℤ)^72) * horner X vp0011110010101.list + horner X ep0011110010101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110010101 : Branch 1 (-1939761639/2000000 : ℚ) vp001111001010 := by
  apply branch_checked idp0011110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1939761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1940761639/1000000 : ℚ) by norm_num]
  exact coverp0011110010101
theorem coverp001111001010 : Covers (-1939761639/2000000 : ℚ) vp001111001010 := join_branches bp0011110010100 bp0011110010101
private noncomputable def vp00111100101_0 : Blocks := edgeBlocks% "full/vectors/00111100101-V-0000.bin"
noncomputable def vp00111100101 : Blocks := vp00111100101_0
private theorem bp001111001010 : Branch 0 (-1939761639/4000000 : ℚ) vp00111100101 := by
  apply branch_left_normalized (c:=vp001111001010) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1939761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1939761639/2000000 : ℚ) by norm_num]
  exact coverp001111001010
private noncomputable def ep001111001011_0 : Blocks := edgeBlocks% "full/vectors/001111001011-E-0000.bin"
noncomputable def ep001111001011 : Blocks := ep001111001011_0
private theorem idp001111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111100101.list =
    C ((2:ℤ)^124) * horner X vp001111001011.list + horner X ep001111001011.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111001011 : Branch 1 (-1939761639/4000000 : ℚ) vp00111100101 := by
  apply branch_checked idp001111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1939761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1941761639/2000000 : ℚ) by norm_num]
  exact coverp001111001011
theorem coverp00111100101 : Covers (-1939761639/4000000 : ℚ) vp00111100101 := join_branches bp001111001010 bp001111001011
private noncomputable def vp0011110010011_0 : Blocks := edgeBlocks% "full/vectors/0011110010011-V-0000.bin"
noncomputable def vp0011110010011 : Blocks := vp0011110010011_0
theorem coverp0011110010011 : Covers (-1938761639/1000000 : ℚ) vp0011110010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110010010_0 : Blocks := edgeBlocks% "full/vectors/0011110010010-V-0000.bin"
noncomputable def vp0011110010010 : Blocks := vp0011110010010_0
theorem coverp0011110010010 : Covers (-1937761639/1000000 : ℚ) vp0011110010010 := cover_leaf (by decide +kernel)
private noncomputable def vp001111001001_0 : Blocks := edgeBlocks% "full/vectors/001111001001-V-0000.bin"
noncomputable def vp001111001001 : Blocks := vp001111001001_0
private theorem bp0011110010010 : Branch 0 (-1937761639/2000000 : ℚ) vp001111001001 := by
  apply branch_left_normalized (c:=vp0011110010010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1937761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1937761639/1000000 : ℚ) by norm_num]
  exact coverp0011110010010
private noncomputable def ep0011110010011_0 : Blocks := edgeBlocks% "full/vectors/0011110010011-E-0000.bin"
noncomputable def ep0011110010011 : Blocks := ep0011110010011_0
private theorem idp0011110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111001001.list =
    C ((2:ℤ)^71) * horner X vp0011110010011.list + horner X ep0011110010011.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110010011 : Branch 1 (-1937761639/2000000 : ℚ) vp001111001001 := by
  apply branch_checked idp0011110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1937761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1938761639/1000000 : ℚ) by norm_num]
  exact coverp0011110010011
theorem coverp001111001001 : Covers (-1937761639/2000000 : ℚ) vp001111001001 := join_branches bp0011110010010 bp0011110010011
private noncomputable def vp0011110010001_0 : Blocks := edgeBlocks% "full/vectors/0011110010001-V-0000.bin"
noncomputable def vp0011110010001 : Blocks := vp0011110010001_0
theorem coverp0011110010001 : Covers (-1936761639/1000000 : ℚ) vp0011110010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110010000_0 : Blocks := edgeBlocks% "full/vectors/0011110010000-V-0000.bin"
noncomputable def vp0011110010000 : Blocks := vp0011110010000_0
theorem coverp0011110010000 : Covers (-1935761639/1000000 : ℚ) vp0011110010000 := cover_leaf (by decide +kernel)
private noncomputable def vp001111001000_0 : Blocks := edgeBlocks% "full/vectors/001111001000-V-0000.bin"
noncomputable def vp001111001000 : Blocks := vp001111001000_0
private theorem bp0011110010000 : Branch 0 (-1935761639/2000000 : ℚ) vp001111001000 := by
  apply branch_left_normalized (c:=vp0011110010000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1935761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1935761639/1000000 : ℚ) by norm_num]
  exact coverp0011110010000
private noncomputable def ep0011110010001_0 : Blocks := edgeBlocks% "full/vectors/0011110010001-E-0000.bin"
noncomputable def ep0011110010001 : Blocks := ep0011110010001_0
private theorem idp0011110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111001000.list =
    C ((2:ℤ)^72) * horner X vp0011110010001.list + horner X ep0011110010001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110010001 : Branch 1 (-1935761639/2000000 : ℚ) vp001111001000 := by
  apply branch_checked idp0011110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1935761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1936761639/1000000 : ℚ) by norm_num]
  exact coverp0011110010001
theorem coverp001111001000 : Covers (-1935761639/2000000 : ℚ) vp001111001000 := join_branches bp0011110010000 bp0011110010001
private noncomputable def vp00111100100_0 : Blocks := edgeBlocks% "full/vectors/00111100100-V-0000.bin"
noncomputable def vp00111100100 : Blocks := vp00111100100_0
private theorem bp001111001000 : Branch 0 (-1935761639/4000000 : ℚ) vp00111100100 := by
  apply branch_left_normalized (c:=vp001111001000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1935761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1935761639/2000000 : ℚ) by norm_num]
  exact coverp001111001000
private noncomputable def ep001111001001_0 : Blocks := edgeBlocks% "full/vectors/001111001001-E-0000.bin"
noncomputable def ep001111001001 : Blocks := ep001111001001_0
private theorem idp001111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111100100.list =
    C ((2:ℤ)^124) * horner X vp001111001001.list + horner X ep001111001001.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111001001 : Branch 1 (-1935761639/4000000 : ℚ) vp00111100100 := by
  apply branch_checked idp001111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1935761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1937761639/2000000 : ℚ) by norm_num]
  exact coverp001111001001
theorem coverp00111100100 : Covers (-1935761639/4000000 : ℚ) vp00111100100 := join_branches bp001111001000 bp001111001001
private noncomputable def vp0011110010_0 : Blocks := edgeBlocks% "full/vectors/0011110010-V-0000.bin"
private noncomputable def vp0011110010_1 : Blocks := edgeBlocks% "full/vectors/0011110010-V-0001.bin"
noncomputable def vp0011110010 : Blocks := (Blocks.join vp0011110010_0 vp0011110010_1)
private theorem bp00111100100 : Branch 0 (-1935761639/8000000 : ℚ) vp0011110010 := by
  apply branch_left_normalized (c:=vp00111100100) (k:=0) (m:=111) (by decide +kernel)
  rw [show 2*(-1935761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1935761639/4000000 : ℚ) by norm_num]
  exact coverp00111100100
private noncomputable def ep00111100101_0 : Blocks := edgeBlocks% "full/vectors/00111100101-E-0000.bin"
private noncomputable def ep00111100101_1 : Blocks := edgeBlocks% "full/vectors/00111100101-E-0001.bin"
noncomputable def ep00111100101 : Blocks := (Blocks.join ep00111100101_0 ep00111100101_1)
private theorem idp00111100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011110010.list =
    C ((2:ℤ)^224) * horner X vp00111100101.list + horner X ep00111100101.list := by
  exact edge_identity (B := (2:ℤ)^397) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111100101 : Branch 1 (-1935761639/8000000 : ℚ) vp0011110010 := by
  apply branch_checked idp00111100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1935761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1939761639/4000000 : ℚ) by norm_num]
  exact coverp00111100101
theorem coverp0011110010 : Covers (-1935761639/8000000 : ℚ) vp0011110010 := join_branches bp00111100100 bp00111100101
private noncomputable def vp001111001_0 : Blocks := edgeBlocks% "full/vectors/001111001-V-0000.bin"
private noncomputable def vp001111001_1 : Blocks := edgeBlocks% "full/vectors/001111001-V-0001.bin"
private noncomputable def vp001111001_2 : Blocks := edgeBlocks% "full/vectors/001111001-V-0002.bin"
noncomputable def vp001111001 : Blocks := (Blocks.join vp001111001_0 (Blocks.join vp001111001_1 vp001111001_2))
private theorem bp0011110010 : Branch 0 (-1935761639/16000000 : ℚ) vp001111001 := by
  apply branch_left_normalized (c:=vp0011110010) (k:=0) (m:=200) (by decide +kernel)
  rw [show 2*(-1935761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1935761639/8000000 : ℚ) by norm_num]
  exact coverp0011110010
private noncomputable def ep0011110011_0 : Blocks := edgeBlocks% "full/vectors/0011110011-E-0000.bin"
private noncomputable def ep0011110011_1 : Blocks := edgeBlocks% "full/vectors/0011110011-E-0001.bin"
private noncomputable def ep0011110011_2 : Blocks := edgeBlocks% "full/vectors/0011110011-E-0002.bin"
noncomputable def ep0011110011 : Blocks := (Blocks.join ep0011110011_0 (Blocks.join ep0011110011_1 ep0011110011_2))
private theorem idp0011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111001.list =
    C ((2:ℤ)^425) * horner X vp0011110011.list + horner X ep0011110011.list := by
  exact edge_identity (B := (2:ℤ)^670) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110011 : Branch 1 (-1935761639/16000000 : ℚ) vp001111001 := by
  apply branch_checked idp0011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1935761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1943761639/8000000 : ℚ) by norm_num]
  exact coverp0011110011
theorem coverp001111001 : Covers (-1935761639/16000000 : ℚ) vp001111001 := join_branches bp0011110010 bp0011110011
private noncomputable def vp0011110001111_0 : Blocks := edgeBlocks% "full/vectors/0011110001111-V-0000.bin"
noncomputable def vp0011110001111 : Blocks := vp0011110001111_0
theorem coverp0011110001111 : Covers (-1934761639/1000000 : ℚ) vp0011110001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110001110_0 : Blocks := edgeBlocks% "full/vectors/0011110001110-V-0000.bin"
noncomputable def vp0011110001110 : Blocks := vp0011110001110_0
theorem coverp0011110001110 : Covers (-1933761639/1000000 : ℚ) vp0011110001110 := cover_leaf (by decide +kernel)
private noncomputable def vp001111000111_0 : Blocks := edgeBlocks% "full/vectors/001111000111-V-0000.bin"
noncomputable def vp001111000111 : Blocks := vp001111000111_0
private theorem bp0011110001110 : Branch 0 (-1933761639/2000000 : ℚ) vp001111000111 := by
  apply branch_left_normalized (c:=vp0011110001110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1933761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1933761639/1000000 : ℚ) by norm_num]
  exact coverp0011110001110
private noncomputable def ep0011110001111_0 : Blocks := edgeBlocks% "full/vectors/0011110001111-E-0000.bin"
noncomputable def ep0011110001111 : Blocks := ep0011110001111_0
private theorem idp0011110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111000111.list =
    C ((2:ℤ)^70) * horner X vp0011110001111.list + horner X ep0011110001111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110001111 : Branch 1 (-1933761639/2000000 : ℚ) vp001111000111 := by
  apply branch_checked idp0011110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1933761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1934761639/1000000 : ℚ) by norm_num]
  exact coverp0011110001111
theorem coverp001111000111 : Covers (-1933761639/2000000 : ℚ) vp001111000111 := join_branches bp0011110001110 bp0011110001111
private noncomputable def vp0011110001101_0 : Blocks := edgeBlocks% "full/vectors/0011110001101-V-0000.bin"
noncomputable def vp0011110001101 : Blocks := vp0011110001101_0
theorem coverp0011110001101 : Covers (-1932761639/1000000 : ℚ) vp0011110001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110001100_0 : Blocks := edgeBlocks% "full/vectors/0011110001100-V-0000.bin"
noncomputable def vp0011110001100 : Blocks := vp0011110001100_0
theorem coverp0011110001100 : Covers (-1931761639/1000000 : ℚ) vp0011110001100 := cover_leaf (by decide +kernel)
private noncomputable def vp001111000110_0 : Blocks := edgeBlocks% "full/vectors/001111000110-V-0000.bin"
noncomputable def vp001111000110 : Blocks := vp001111000110_0
private theorem bp0011110001100 : Branch 0 (-1931761639/2000000 : ℚ) vp001111000110 := by
  apply branch_left_normalized (c:=vp0011110001100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1931761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1931761639/1000000 : ℚ) by norm_num]
  exact coverp0011110001100
private noncomputable def ep0011110001101_0 : Blocks := edgeBlocks% "full/vectors/0011110001101-E-0000.bin"
noncomputable def ep0011110001101 : Blocks := ep0011110001101_0
private theorem idp0011110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111000110.list =
    C ((2:ℤ)^72) * horner X vp0011110001101.list + horner X ep0011110001101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110001101 : Branch 1 (-1931761639/2000000 : ℚ) vp001111000110 := by
  apply branch_checked idp0011110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1931761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1932761639/1000000 : ℚ) by norm_num]
  exact coverp0011110001101
theorem coverp001111000110 : Covers (-1931761639/2000000 : ℚ) vp001111000110 := join_branches bp0011110001100 bp0011110001101
private noncomputable def vp00111100011_0 : Blocks := edgeBlocks% "full/vectors/00111100011-V-0000.bin"
noncomputable def vp00111100011 : Blocks := vp00111100011_0
private theorem bp001111000110 : Branch 0 (-1931761639/4000000 : ℚ) vp00111100011 := by
  apply branch_left_normalized (c:=vp001111000110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1931761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1931761639/2000000 : ℚ) by norm_num]
  exact coverp001111000110
private noncomputable def ep001111000111_0 : Blocks := edgeBlocks% "full/vectors/001111000111-E-0000.bin"
noncomputable def ep001111000111 : Blocks := ep001111000111_0
private theorem idp001111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111100011.list =
    C ((2:ℤ)^123) * horner X vp001111000111.list + horner X ep001111000111.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111000111 : Branch 1 (-1931761639/4000000 : ℚ) vp00111100011 := by
  apply branch_checked idp001111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1931761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1933761639/2000000 : ℚ) by norm_num]
  exact coverp001111000111
theorem coverp00111100011 : Covers (-1931761639/4000000 : ℚ) vp00111100011 := join_branches bp001111000110 bp001111000111
private noncomputable def vp0011110001011_0 : Blocks := edgeBlocks% "full/vectors/0011110001011-V-0000.bin"
noncomputable def vp0011110001011 : Blocks := vp0011110001011_0
theorem coverp0011110001011 : Covers (-1930761639/1000000 : ℚ) vp0011110001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110001010_0 : Blocks := edgeBlocks% "full/vectors/0011110001010-V-0000.bin"
noncomputable def vp0011110001010 : Blocks := vp0011110001010_0
theorem coverp0011110001010 : Covers (-1929761639/1000000 : ℚ) vp0011110001010 := cover_leaf (by decide +kernel)
private noncomputable def vp001111000101_0 : Blocks := edgeBlocks% "full/vectors/001111000101-V-0000.bin"
noncomputable def vp001111000101 : Blocks := vp001111000101_0
private theorem bp0011110001010 : Branch 0 (-1929761639/2000000 : ℚ) vp001111000101 := by
  apply branch_left_normalized (c:=vp0011110001010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1929761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1929761639/1000000 : ℚ) by norm_num]
  exact coverp0011110001010
private noncomputable def ep0011110001011_0 : Blocks := edgeBlocks% "full/vectors/0011110001011-E-0000.bin"
noncomputable def ep0011110001011 : Blocks := ep0011110001011_0
private theorem idp0011110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111000101.list =
    C ((2:ℤ)^71) * horner X vp0011110001011.list + horner X ep0011110001011.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110001011 : Branch 1 (-1929761639/2000000 : ℚ) vp001111000101 := by
  apply branch_checked idp0011110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1929761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1930761639/1000000 : ℚ) by norm_num]
  exact coverp0011110001011
theorem coverp001111000101 : Covers (-1929761639/2000000 : ℚ) vp001111000101 := join_branches bp0011110001010 bp0011110001011
private noncomputable def vp0011110001001_0 : Blocks := edgeBlocks% "full/vectors/0011110001001-V-0000.bin"
noncomputable def vp0011110001001 : Blocks := vp0011110001001_0
theorem coverp0011110001001 : Covers (-1928761639/1000000 : ℚ) vp0011110001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110001000_0 : Blocks := edgeBlocks% "full/vectors/0011110001000-V-0000.bin"
noncomputable def vp0011110001000 : Blocks := vp0011110001000_0
theorem coverp0011110001000 : Covers (-1927761639/1000000 : ℚ) vp0011110001000 := cover_leaf (by decide +kernel)
private noncomputable def vp001111000100_0 : Blocks := edgeBlocks% "full/vectors/001111000100-V-0000.bin"
noncomputable def vp001111000100 : Blocks := vp001111000100_0
private theorem bp0011110001000 : Branch 0 (-1927761639/2000000 : ℚ) vp001111000100 := by
  apply branch_left_normalized (c:=vp0011110001000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1927761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1927761639/1000000 : ℚ) by norm_num]
  exact coverp0011110001000
private noncomputable def ep0011110001001_0 : Blocks := edgeBlocks% "full/vectors/0011110001001-E-0000.bin"
noncomputable def ep0011110001001 : Blocks := ep0011110001001_0
private theorem idp0011110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111000100.list =
    C ((2:ℤ)^72) * horner X vp0011110001001.list + horner X ep0011110001001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110001001 : Branch 1 (-1927761639/2000000 : ℚ) vp001111000100 := by
  apply branch_checked idp0011110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1927761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1928761639/1000000 : ℚ) by norm_num]
  exact coverp0011110001001
theorem coverp001111000100 : Covers (-1927761639/2000000 : ℚ) vp001111000100 := join_branches bp0011110001000 bp0011110001001
private noncomputable def vp00111100010_0 : Blocks := edgeBlocks% "full/vectors/00111100010-V-0000.bin"
noncomputable def vp00111100010 : Blocks := vp00111100010_0
private theorem bp001111000100 : Branch 0 (-1927761639/4000000 : ℚ) vp00111100010 := by
  apply branch_left_normalized (c:=vp001111000100) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1927761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1927761639/2000000 : ℚ) by norm_num]
  exact coverp001111000100
private noncomputable def ep001111000101_0 : Blocks := edgeBlocks% "full/vectors/001111000101-E-0000.bin"
noncomputable def ep001111000101 : Blocks := ep001111000101_0
private theorem idp001111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111100010.list =
    C ((2:ℤ)^122) * horner X vp001111000101.list + horner X ep001111000101.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111000101 : Branch 1 (-1927761639/4000000 : ℚ) vp00111100010 := by
  apply branch_checked idp001111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1927761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1929761639/2000000 : ℚ) by norm_num]
  exact coverp001111000101
theorem coverp00111100010 : Covers (-1927761639/4000000 : ℚ) vp00111100010 := join_branches bp001111000100 bp001111000101
private noncomputable def vp0011110001_0 : Blocks := edgeBlocks% "full/vectors/0011110001-V-0000.bin"
private noncomputable def vp0011110001_1 : Blocks := edgeBlocks% "full/vectors/0011110001-V-0001.bin"
noncomputable def vp0011110001 : Blocks := (Blocks.join vp0011110001_0 vp0011110001_1)
private theorem bp00111100010 : Branch 0 (-1927761639/8000000 : ℚ) vp0011110001 := by
  apply branch_left_normalized (c:=vp00111100010) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-1927761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1927761639/4000000 : ℚ) by norm_num]
  exact coverp00111100010
private noncomputable def ep00111100011_0 : Blocks := edgeBlocks% "full/vectors/00111100011-E-0000.bin"
private noncomputable def ep00111100011_1 : Blocks := edgeBlocks% "full/vectors/00111100011-E-0001.bin"
noncomputable def ep00111100011 : Blocks := (Blocks.join ep00111100011_0 ep00111100011_1)
private theorem idp00111100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011110001.list =
    C ((2:ℤ)^225) * horner X vp00111100011.list + horner X ep00111100011.list := by
  exact edge_identity (B := (2:ℤ)^398) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111100011 : Branch 1 (-1927761639/8000000 : ℚ) vp0011110001 := by
  apply branch_checked idp00111100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1927761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1931761639/4000000 : ℚ) by norm_num]
  exact coverp00111100011
theorem coverp0011110001 : Covers (-1927761639/8000000 : ℚ) vp0011110001 := join_branches bp00111100010 bp00111100011
private noncomputable def vp0011110000111_0 : Blocks := edgeBlocks% "full/vectors/0011110000111-V-0000.bin"
noncomputable def vp0011110000111 : Blocks := vp0011110000111_0
theorem coverp0011110000111 : Covers (-1926761639/1000000 : ℚ) vp0011110000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110000110_0 : Blocks := edgeBlocks% "full/vectors/0011110000110-V-0000.bin"
noncomputable def vp0011110000110 : Blocks := vp0011110000110_0
theorem coverp0011110000110 : Covers (-1925761639/1000000 : ℚ) vp0011110000110 := cover_leaf (by decide +kernel)
private noncomputable def vp001111000011_0 : Blocks := edgeBlocks% "full/vectors/001111000011-V-0000.bin"
noncomputable def vp001111000011 : Blocks := vp001111000011_0
private theorem bp0011110000110 : Branch 0 (-1925761639/2000000 : ℚ) vp001111000011 := by
  apply branch_left_normalized (c:=vp0011110000110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1925761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1925761639/1000000 : ℚ) by norm_num]
  exact coverp0011110000110
private noncomputable def ep0011110000111_0 : Blocks := edgeBlocks% "full/vectors/0011110000111-E-0000.bin"
noncomputable def ep0011110000111 : Blocks := ep0011110000111_0
private theorem idp0011110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111000011.list =
    C ((2:ℤ)^71) * horner X vp0011110000111.list + horner X ep0011110000111.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110000111 : Branch 1 (-1925761639/2000000 : ℚ) vp001111000011 := by
  apply branch_checked idp0011110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1925761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1926761639/1000000 : ℚ) by norm_num]
  exact coverp0011110000111
theorem coverp001111000011 : Covers (-1925761639/2000000 : ℚ) vp001111000011 := join_branches bp0011110000110 bp0011110000111
private noncomputable def vp0011110000101_0 : Blocks := edgeBlocks% "full/vectors/0011110000101-V-0000.bin"
noncomputable def vp0011110000101 : Blocks := vp0011110000101_0
theorem coverp0011110000101 : Covers (-1924761639/1000000 : ℚ) vp0011110000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110000100_0 : Blocks := edgeBlocks% "full/vectors/0011110000100-V-0000.bin"
noncomputable def vp0011110000100 : Blocks := vp0011110000100_0
theorem coverp0011110000100 : Covers (-1923761639/1000000 : ℚ) vp0011110000100 := cover_leaf (by decide +kernel)
private noncomputable def vp001111000010_0 : Blocks := edgeBlocks% "full/vectors/001111000010-V-0000.bin"
noncomputable def vp001111000010 : Blocks := vp001111000010_0
private theorem bp0011110000100 : Branch 0 (-1923761639/2000000 : ℚ) vp001111000010 := by
  apply branch_left_normalized (c:=vp0011110000100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1923761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1923761639/1000000 : ℚ) by norm_num]
  exact coverp0011110000100
private noncomputable def ep0011110000101_0 : Blocks := edgeBlocks% "full/vectors/0011110000101-E-0000.bin"
noncomputable def ep0011110000101 : Blocks := ep0011110000101_0
private theorem idp0011110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111000010.list =
    C ((2:ℤ)^71) * horner X vp0011110000101.list + horner X ep0011110000101.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110000101 : Branch 1 (-1923761639/2000000 : ℚ) vp001111000010 := by
  apply branch_checked idp0011110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1923761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1924761639/1000000 : ℚ) by norm_num]
  exact coverp0011110000101
theorem coverp001111000010 : Covers (-1923761639/2000000 : ℚ) vp001111000010 := join_branches bp0011110000100 bp0011110000101
private noncomputable def vp00111100001_0 : Blocks := edgeBlocks% "full/vectors/00111100001-V-0000.bin"
noncomputable def vp00111100001 : Blocks := vp00111100001_0
private theorem bp001111000010 : Branch 0 (-1923761639/4000000 : ℚ) vp00111100001 := by
  apply branch_left_normalized (c:=vp001111000010) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1923761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1923761639/2000000 : ℚ) by norm_num]
  exact coverp001111000010
private noncomputable def ep001111000011_0 : Blocks := edgeBlocks% "full/vectors/001111000011-E-0000.bin"
noncomputable def ep001111000011 : Blocks := ep001111000011_0
private theorem idp001111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111100001.list =
    C ((2:ℤ)^124) * horner X vp001111000011.list + horner X ep001111000011.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111000011 : Branch 1 (-1923761639/4000000 : ℚ) vp00111100001 := by
  apply branch_checked idp001111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1923761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1925761639/2000000 : ℚ) by norm_num]
  exact coverp001111000011
theorem coverp00111100001 : Covers (-1923761639/4000000 : ℚ) vp00111100001 := join_branches bp001111000010 bp001111000011
private noncomputable def vp0011110000011_0 : Blocks := edgeBlocks% "full/vectors/0011110000011-V-0000.bin"
noncomputable def vp0011110000011 : Blocks := vp0011110000011_0
theorem coverp0011110000011 : Covers (-1922761639/1000000 : ℚ) vp0011110000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110000010_0 : Blocks := edgeBlocks% "full/vectors/0011110000010-V-0000.bin"
noncomputable def vp0011110000010 : Blocks := vp0011110000010_0
theorem coverp0011110000010 : Covers (-1921761639/1000000 : ℚ) vp0011110000010 := cover_leaf (by decide +kernel)
private noncomputable def vp001111000001_0 : Blocks := edgeBlocks% "full/vectors/001111000001-V-0000.bin"
noncomputable def vp001111000001 : Blocks := vp001111000001_0
private theorem bp0011110000010 : Branch 0 (-1921761639/2000000 : ℚ) vp001111000001 := by
  apply branch_left_normalized (c:=vp0011110000010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1921761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1921761639/1000000 : ℚ) by norm_num]
  exact coverp0011110000010
private noncomputable def ep0011110000011_0 : Blocks := edgeBlocks% "full/vectors/0011110000011-E-0000.bin"
noncomputable def ep0011110000011 : Blocks := ep0011110000011_0
private theorem idp0011110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111000001.list =
    C ((2:ℤ)^72) * horner X vp0011110000011.list + horner X ep0011110000011.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110000011 : Branch 1 (-1921761639/2000000 : ℚ) vp001111000001 := by
  apply branch_checked idp0011110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1921761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1922761639/1000000 : ℚ) by norm_num]
  exact coverp0011110000011
theorem coverp001111000001 : Covers (-1921761639/2000000 : ℚ) vp001111000001 := join_branches bp0011110000010 bp0011110000011
private noncomputable def vp0011110000001_0 : Blocks := edgeBlocks% "full/vectors/0011110000001-V-0000.bin"
noncomputable def vp0011110000001 : Blocks := vp0011110000001_0
theorem coverp0011110000001 : Covers (-1920761639/1000000 : ℚ) vp0011110000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011110000000_0 : Blocks := edgeBlocks% "full/vectors/0011110000000-V-0000.bin"
noncomputable def vp0011110000000 : Blocks := vp0011110000000_0
theorem coverp0011110000000 : Covers (-1919761639/1000000 : ℚ) vp0011110000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001111000000_0 : Blocks := edgeBlocks% "full/vectors/001111000000-V-0000.bin"
noncomputable def vp001111000000 : Blocks := vp001111000000_0
private theorem bp0011110000000 : Branch 0 (-1919761639/2000000 : ℚ) vp001111000000 := by
  apply branch_left_normalized (c:=vp0011110000000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1919761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1919761639/1000000 : ℚ) by norm_num]
  exact coverp0011110000000
private noncomputable def ep0011110000001_0 : Blocks := edgeBlocks% "full/vectors/0011110000001-E-0000.bin"
noncomputable def ep0011110000001 : Blocks := ep0011110000001_0
private theorem idp0011110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111000000.list =
    C ((2:ℤ)^71) * horner X vp0011110000001.list + horner X ep0011110000001.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110000001 : Branch 1 (-1919761639/2000000 : ℚ) vp001111000000 := by
  apply branch_checked idp0011110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1919761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1920761639/1000000 : ℚ) by norm_num]
  exact coverp0011110000001
theorem coverp001111000000 : Covers (-1919761639/2000000 : ℚ) vp001111000000 := join_branches bp0011110000000 bp0011110000001
private noncomputable def vp00111100000_0 : Blocks := edgeBlocks% "full/vectors/00111100000-V-0000.bin"
noncomputable def vp00111100000 : Blocks := vp00111100000_0
private theorem bp001111000000 : Branch 0 (-1919761639/4000000 : ℚ) vp00111100000 := by
  apply branch_left_normalized (c:=vp001111000000) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1919761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1919761639/2000000 : ℚ) by norm_num]
  exact coverp001111000000
private noncomputable def ep001111000001_0 : Blocks := edgeBlocks% "full/vectors/001111000001-E-0000.bin"
noncomputable def ep001111000001 : Blocks := ep001111000001_0
private theorem idp001111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111100000.list =
    C ((2:ℤ)^123) * horner X vp001111000001.list + horner X ep001111000001.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111000001 : Branch 1 (-1919761639/4000000 : ℚ) vp00111100000 := by
  apply branch_checked idp001111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1919761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1921761639/2000000 : ℚ) by norm_num]
  exact coverp001111000001
theorem coverp00111100000 : Covers (-1919761639/4000000 : ℚ) vp00111100000 := join_branches bp001111000000 bp001111000001
private noncomputable def vp0011110000_0 : Blocks := edgeBlocks% "full/vectors/0011110000-V-0000.bin"
private noncomputable def vp0011110000_1 : Blocks := edgeBlocks% "full/vectors/0011110000-V-0001.bin"
noncomputable def vp0011110000 : Blocks := (Blocks.join vp0011110000_0 vp0011110000_1)
private theorem bp00111100000 : Branch 0 (-1919761639/8000000 : ℚ) vp0011110000 := by
  apply branch_left_normalized (c:=vp00111100000) (k:=0) (m:=111) (by decide +kernel)
  rw [show 2*(-1919761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1919761639/4000000 : ℚ) by norm_num]
  exact coverp00111100000
private noncomputable def ep00111100001_0 : Blocks := edgeBlocks% "full/vectors/00111100001-E-0000.bin"
private noncomputable def ep00111100001_1 : Blocks := edgeBlocks% "full/vectors/00111100001-E-0001.bin"
noncomputable def ep00111100001 : Blocks := (Blocks.join ep00111100001_0 ep00111100001_1)
private theorem idp00111100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011110000.list =
    C ((2:ℤ)^226) * horner X vp00111100001.list + horner X ep00111100001.list := by
  exact edge_identity (B := (2:ℤ)^399) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111100001 : Branch 1 (-1919761639/8000000 : ℚ) vp0011110000 := by
  apply branch_checked idp00111100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1919761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1923761639/4000000 : ℚ) by norm_num]
  exact coverp00111100001
theorem coverp0011110000 : Covers (-1919761639/8000000 : ℚ) vp0011110000 := join_branches bp00111100000 bp00111100001
private noncomputable def vp001111000_0 : Blocks := edgeBlocks% "full/vectors/001111000-V-0000.bin"
private noncomputable def vp001111000_1 : Blocks := edgeBlocks% "full/vectors/001111000-V-0001.bin"
private noncomputable def vp001111000_2 : Blocks := edgeBlocks% "full/vectors/001111000-V-0002.bin"
noncomputable def vp001111000 : Blocks := (Blocks.join vp001111000_0 (Blocks.join vp001111000_1 vp001111000_2))
private theorem bp0011110000 : Branch 0 (-1919761639/16000000 : ℚ) vp001111000 := by
  apply branch_left_normalized (c:=vp0011110000) (k:=0) (m:=202) (by decide +kernel)
  rw [show 2*(-1919761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1919761639/8000000 : ℚ) by norm_num]
  exact coverp0011110000
private noncomputable def ep0011110001_0 : Blocks := edgeBlocks% "full/vectors/0011110001-E-0000.bin"
private noncomputable def ep0011110001_1 : Blocks := edgeBlocks% "full/vectors/0011110001-E-0001.bin"
private noncomputable def ep0011110001_2 : Blocks := edgeBlocks% "full/vectors/0011110001-E-0002.bin"
noncomputable def ep0011110001 : Blocks := (Blocks.join ep0011110001_0 (Blocks.join ep0011110001_1 ep0011110001_2))
private theorem idp0011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111000.list =
    C ((2:ℤ)^427) * horner X vp0011110001.list + horner X ep0011110001.list := by
  exact edge_identity (B := (2:ℤ)^672) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011110001 : Branch 1 (-1919761639/16000000 : ℚ) vp001111000 := by
  apply branch_checked idp0011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1919761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1927761639/8000000 : ℚ) by norm_num]
  exact coverp0011110001
theorem coverp001111000 : Covers (-1919761639/16000000 : ℚ) vp001111000 := join_branches bp0011110000 bp0011110001
private noncomputable def vp00111100_0 : Blocks := edgeBlocks% "full/vectors/00111100-V-0000.bin"
private noncomputable def vp00111100_1 : Blocks := edgeBlocks% "full/vectors/00111100-V-0001.bin"
private noncomputable def vp00111100_2 : Blocks := edgeBlocks% "full/vectors/00111100-V-0002.bin"
private noncomputable def vp00111100_3 : Blocks := edgeBlocks% "full/vectors/00111100-V-0003.bin"
private noncomputable def vp00111100_4 : Blocks := edgeBlocks% "full/vectors/00111100-V-0004.bin"
private noncomputable def vp00111100_5 : Blocks := edgeBlocks% "full/vectors/00111100-V-0005.bin"
noncomputable def vp00111100 : Blocks := (Blocks.join (Blocks.join vp00111100_0 (Blocks.join vp00111100_1 vp00111100_2)) (Blocks.join vp00111100_3 (Blocks.join vp00111100_4 vp00111100_5)))
private theorem bp001111000 : Branch 0 (-1919761639/32000000 : ℚ) vp00111100 := by
  apply branch_left_normalized (c:=vp001111000) (k:=0) (m:=380) (by decide +kernel)
  rw [show 2*(-1919761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1919761639/16000000 : ℚ) by norm_num]
  exact coverp001111000
private noncomputable def ep001111001_0 : Blocks := edgeBlocks% "full/vectors/001111001-E-0000.bin"
private noncomputable def ep001111001_1 : Blocks := edgeBlocks% "full/vectors/001111001-E-0001.bin"
private noncomputable def ep001111001_2 : Blocks := edgeBlocks% "full/vectors/001111001-E-0002.bin"
private noncomputable def ep001111001_3 : Blocks := edgeBlocks% "full/vectors/001111001-E-0003.bin"
private noncomputable def ep001111001_4 : Blocks := edgeBlocks% "full/vectors/001111001-E-0004.bin"
private noncomputable def ep001111001_5 : Blocks := edgeBlocks% "full/vectors/001111001-E-0005.bin"
noncomputable def ep001111001 : Blocks := (Blocks.join (Blocks.join ep001111001_0 (Blocks.join ep001111001_1 ep001111001_2)) (Blocks.join ep001111001_3 (Blocks.join ep001111001_4 ep001111001_5)))
private theorem idp001111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111100.list =
    C ((2:ℤ)^826) * horner X vp001111001.list + horner X ep001111001.list := by
  exact edge_identity (B := (2:ℤ)^1215) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001111001 : Branch 1 (-1919761639/32000000 : ℚ) vp00111100 := by
  apply branch_checked idp001111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1919761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1935761639/16000000 : ℚ) by norm_num]
  exact coverp001111001
theorem coverp00111100 : Covers (-1919761639/32000000 : ℚ) vp00111100 := join_branches bp001111000 bp001111001
private noncomputable def vp0011110_0 : Blocks := edgeBlocks% "full/vectors/0011110-V-0000.bin"
private noncomputable def vp0011110_1 : Blocks := edgeBlocks% "full/vectors/0011110-V-0001.bin"
private noncomputable def vp0011110_2 : Blocks := edgeBlocks% "full/vectors/0011110-V-0002.bin"
private noncomputable def vp0011110_3 : Blocks := edgeBlocks% "full/vectors/0011110-V-0003.bin"
private noncomputable def vp0011110_4 : Blocks := edgeBlocks% "full/vectors/0011110-V-0004.bin"
private noncomputable def vp0011110_5 : Blocks := edgeBlocks% "full/vectors/0011110-V-0005.bin"
private noncomputable def vp0011110_6 : Blocks := edgeBlocks% "full/vectors/0011110-V-0006.bin"
private noncomputable def vp0011110_7 : Blocks := edgeBlocks% "full/vectors/0011110-V-0007.bin"
private noncomputable def vp0011110_8 : Blocks := edgeBlocks% "full/vectors/0011110-V-0008.bin"
private noncomputable def vp0011110_9 : Blocks := edgeBlocks% "full/vectors/0011110-V-0009.bin"
private noncomputable def vp0011110_10 : Blocks := edgeBlocks% "full/vectors/0011110-V-0010.bin"
private noncomputable def vp0011110_11 : Blocks := edgeBlocks% "full/vectors/0011110-V-0011.bin"
noncomputable def vp0011110 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0011110_0 (Blocks.join vp0011110_1 vp0011110_2)) (Blocks.join vp0011110_3 (Blocks.join vp0011110_4 vp0011110_5))) (Blocks.join (Blocks.join vp0011110_6 (Blocks.join vp0011110_7 vp0011110_8)) (Blocks.join vp0011110_9 (Blocks.join vp0011110_10 vp0011110_11))))
private theorem bp00111100 : Branch 0 (-1919761639/64000000 : ℚ) vp0011110 := by
  apply branch_left_normalized (c:=vp00111100) (k:=0) (m:=733) (by decide +kernel)
  rw [show 2*(-1919761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1919761639/32000000 : ℚ) by norm_num]
  exact coverp00111100
private noncomputable def ep00111101_0 : Blocks := edgeBlocks% "full/vectors/00111101-E-0000.bin"
private noncomputable def ep00111101_1 : Blocks := edgeBlocks% "full/vectors/00111101-E-0001.bin"
private noncomputable def ep00111101_2 : Blocks := edgeBlocks% "full/vectors/00111101-E-0002.bin"
private noncomputable def ep00111101_3 : Blocks := edgeBlocks% "full/vectors/00111101-E-0003.bin"
private noncomputable def ep00111101_4 : Blocks := edgeBlocks% "full/vectors/00111101-E-0004.bin"
private noncomputable def ep00111101_5 : Blocks := edgeBlocks% "full/vectors/00111101-E-0005.bin"
private noncomputable def ep00111101_6 : Blocks := edgeBlocks% "full/vectors/00111101-E-0006.bin"
private noncomputable def ep00111101_7 : Blocks := edgeBlocks% "full/vectors/00111101-E-0007.bin"
private noncomputable def ep00111101_8 : Blocks := edgeBlocks% "full/vectors/00111101-E-0008.bin"
private noncomputable def ep00111101_9 : Blocks := edgeBlocks% "full/vectors/00111101-E-0009.bin"
private noncomputable def ep00111101_10 : Blocks := edgeBlocks% "full/vectors/00111101-E-0010.bin"
private noncomputable def ep00111101_11 : Blocks := edgeBlocks% "full/vectors/00111101-E-0011.bin"
noncomputable def ep00111101 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00111101_0 (Blocks.join ep00111101_1 ep00111101_2)) (Blocks.join ep00111101_3 (Blocks.join ep00111101_4 ep00111101_5))) (Blocks.join (Blocks.join ep00111101_6 (Blocks.join ep00111101_7 ep00111101_8)) (Blocks.join ep00111101_9 (Blocks.join ep00111101_10 ep00111101_11))))
private theorem idp00111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011110.list =
    C ((2:ℤ)^1613) * horner X vp00111101.list + horner X ep00111101.list := by
  exact edge_identity (B := (2:ℤ)^2287) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111101 : Branch 1 (-1919761639/64000000 : ℚ) vp0011110 := by
  apply branch_checked idp00111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1919761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1951761639/32000000 : ℚ) by norm_num]
  exact coverp00111101
theorem coverp0011110 : Covers (-1919761639/64000000 : ℚ) vp0011110 := join_branches bp00111100 bp00111101
private noncomputable def vp001111_0 : Blocks := edgeBlocks% "full/vectors/001111-V-0000.bin"
private noncomputable def vp001111_1 : Blocks := edgeBlocks% "full/vectors/001111-V-0001.bin"
private noncomputable def vp001111_2 : Blocks := edgeBlocks% "full/vectors/001111-V-0002.bin"
private noncomputable def vp001111_3 : Blocks := edgeBlocks% "full/vectors/001111-V-0003.bin"
private noncomputable def vp001111_4 : Blocks := edgeBlocks% "full/vectors/001111-V-0004.bin"
private noncomputable def vp001111_5 : Blocks := edgeBlocks% "full/vectors/001111-V-0005.bin"
private noncomputable def vp001111_6 : Blocks := edgeBlocks% "full/vectors/001111-V-0006.bin"
private noncomputable def vp001111_7 : Blocks := edgeBlocks% "full/vectors/001111-V-0007.bin"
private noncomputable def vp001111_8 : Blocks := edgeBlocks% "full/vectors/001111-V-0008.bin"
private noncomputable def vp001111_9 : Blocks := edgeBlocks% "full/vectors/001111-V-0009.bin"
private noncomputable def vp001111_10 : Blocks := edgeBlocks% "full/vectors/001111-V-0010.bin"
private noncomputable def vp001111_11 : Blocks := edgeBlocks% "full/vectors/001111-V-0011.bin"
private noncomputable def vp001111_12 : Blocks := edgeBlocks% "full/vectors/001111-V-0012.bin"
private noncomputable def vp001111_13 : Blocks := edgeBlocks% "full/vectors/001111-V-0013.bin"
private noncomputable def vp001111_14 : Blocks := edgeBlocks% "full/vectors/001111-V-0014.bin"
private noncomputable def vp001111_15 : Blocks := edgeBlocks% "full/vectors/001111-V-0015.bin"
private noncomputable def vp001111_16 : Blocks := edgeBlocks% "full/vectors/001111-V-0016.bin"
private noncomputable def vp001111_17 : Blocks := edgeBlocks% "full/vectors/001111-V-0017.bin"
private noncomputable def vp001111_18 : Blocks := edgeBlocks% "full/vectors/001111-V-0018.bin"
private noncomputable def vp001111_19 : Blocks := edgeBlocks% "full/vectors/001111-V-0019.bin"
private noncomputable def vp001111_20 : Blocks := edgeBlocks% "full/vectors/001111-V-0020.bin"
private noncomputable def vp001111_21 : Blocks := edgeBlocks% "full/vectors/001111-V-0021.bin"
noncomputable def vp001111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp001111_0 vp001111_1) (Blocks.join vp001111_2 (Blocks.join vp001111_3 vp001111_4))) (Blocks.join (Blocks.join vp001111_5 (Blocks.join vp001111_6 vp001111_7)) (Blocks.join vp001111_8 (Blocks.join vp001111_9 vp001111_10)))) (Blocks.join (Blocks.join (Blocks.join vp001111_11 vp001111_12) (Blocks.join vp001111_13 (Blocks.join vp001111_14 vp001111_15))) (Blocks.join (Blocks.join vp001111_16 (Blocks.join vp001111_17 vp001111_18)) (Blocks.join vp001111_19 (Blocks.join vp001111_20 vp001111_21)))))
private theorem bp0011110 : Branch 0 (-1919761639/128000000 : ℚ) vp001111 := by
  apply branch_left_normalized (c:=vp0011110) (k:=0) (m:=1428) (by decide +kernel)
  rw [show 2*(-1919761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-1919761639/64000000 : ℚ) by norm_num]
  exact coverp0011110
private noncomputable def ep0011111_0 : Blocks := edgeBlocks% "full/vectors/0011111-E-0000.bin"
private noncomputable def ep0011111_1 : Blocks := edgeBlocks% "full/vectors/0011111-E-0001.bin"
private noncomputable def ep0011111_2 : Blocks := edgeBlocks% "full/vectors/0011111-E-0002.bin"
private noncomputable def ep0011111_3 : Blocks := edgeBlocks% "full/vectors/0011111-E-0003.bin"
private noncomputable def ep0011111_4 : Blocks := edgeBlocks% "full/vectors/0011111-E-0004.bin"
private noncomputable def ep0011111_5 : Blocks := edgeBlocks% "full/vectors/0011111-E-0005.bin"
private noncomputable def ep0011111_6 : Blocks := edgeBlocks% "full/vectors/0011111-E-0006.bin"
private noncomputable def ep0011111_7 : Blocks := edgeBlocks% "full/vectors/0011111-E-0007.bin"
private noncomputable def ep0011111_8 : Blocks := edgeBlocks% "full/vectors/0011111-E-0008.bin"
private noncomputable def ep0011111_9 : Blocks := edgeBlocks% "full/vectors/0011111-E-0009.bin"
private noncomputable def ep0011111_10 : Blocks := edgeBlocks% "full/vectors/0011111-E-0010.bin"
private noncomputable def ep0011111_11 : Blocks := edgeBlocks% "full/vectors/0011111-E-0011.bin"
private noncomputable def ep0011111_12 : Blocks := edgeBlocks% "full/vectors/0011111-E-0012.bin"
private noncomputable def ep0011111_13 : Blocks := edgeBlocks% "full/vectors/0011111-E-0013.bin"
private noncomputable def ep0011111_14 : Blocks := edgeBlocks% "full/vectors/0011111-E-0014.bin"
private noncomputable def ep0011111_15 : Blocks := edgeBlocks% "full/vectors/0011111-E-0015.bin"
private noncomputable def ep0011111_16 : Blocks := edgeBlocks% "full/vectors/0011111-E-0016.bin"
private noncomputable def ep0011111_17 : Blocks := edgeBlocks% "full/vectors/0011111-E-0017.bin"
private noncomputable def ep0011111_18 : Blocks := edgeBlocks% "full/vectors/0011111-E-0018.bin"
private noncomputable def ep0011111_19 : Blocks := edgeBlocks% "full/vectors/0011111-E-0019.bin"
private noncomputable def ep0011111_20 : Blocks := edgeBlocks% "full/vectors/0011111-E-0020.bin"
private noncomputable def ep0011111_21 : Blocks := edgeBlocks% "full/vectors/0011111-E-0021.bin"
noncomputable def ep0011111 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0011111_0 ep0011111_1) (Blocks.join ep0011111_2 (Blocks.join ep0011111_3 ep0011111_4))) (Blocks.join (Blocks.join ep0011111_5 (Blocks.join ep0011111_6 ep0011111_7)) (Blocks.join ep0011111_8 (Blocks.join ep0011111_9 ep0011111_10)))) (Blocks.join (Blocks.join (Blocks.join ep0011111_11 ep0011111_12) (Blocks.join ep0011111_13 (Blocks.join ep0011111_14 ep0011111_15))) (Blocks.join (Blocks.join ep0011111_16 (Blocks.join ep0011111_17 ep0011111_18)) (Blocks.join ep0011111_19 (Blocks.join ep0011111_20 ep0011111_21)))))
private def ptsp0011111 : List ℤ := [((2:ℤ)^4329+0),((2:ℤ)^4329+1)]
private theorem boundp0011111 : 2^vp001111.size*absSum vp001111.list + ((2:ℤ)^3141*absSum vp0011111.list+absSum ep0011111.list) < (2:ℤ)^4374 := by decide +kernel
private theorem pointp0011111_0 : fastHom 1 ((2:ℤ)^4329+0) vp001111 = ((2:ℤ)^3141)*vp0011111.subst ((2:ℤ)^4329+0)+ep0011111.subst ((2:ℤ)^4329+0) := by decide +kernel
private theorem pointp0011111_1 : fastHom 1 ((2:ℤ)^4329+1) vp001111 = ((2:ℤ)^3141)*vp0011111.subst ((2:ℤ)^4329+1)+ep0011111.subst ((2:ℤ)^4329+1) := by decide +kernel
private theorem checkp0011111 (x:ℤ) (hx:x ∈ ptsp0011111) : fastHom 1 x vp001111 = ((2:ℤ)^3141)*vp0011111.subst x+ep0011111.subst x := by
  simp only [ptsp0011111,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp0011111_0
  · exact pointp0011111_1
private theorem idp0011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001111.list =
    C ((2:ℤ)^3141) * horner X vp0011111.list + horner X ep0011111.list := by
  apply edge_identity (B := (2:ℤ)^4374) (by decide) (by positivity) (by positivity) boundp0011111
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0011111 (by decide +kernel)
  · have h : ptsp0011111.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0011111.trans_le (by decide +kernel)
  · exact checkp0011111
private theorem bp0011111 : Branch 1 (-1919761639/128000000 : ℚ) vp001111 := by
  apply branch_checked idp0011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1919761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-1983761639/64000000 : ℚ) by norm_num]
  exact coverp0011111
theorem coverp001111 : Covers (-1919761639/128000000 : ℚ) vp001111 := join_branches bp0011110 bp0011111
end NextProof.EdgeFull

