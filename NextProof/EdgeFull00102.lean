import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0011101111111_0 : Blocks := edgeBlocks% "full/vectors/0011101111111-V-0000.bin"
noncomputable def vp0011101111111 : Blocks := vp0011101111111_0
theorem coverp0011101111111 : Covers (-1918761639/1000000 : ℚ) vp0011101111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011101111110_0 : Blocks := edgeBlocks% "full/vectors/0011101111110-V-0000.bin"
noncomputable def vp0011101111110 : Blocks := vp0011101111110_0
theorem coverp0011101111110 : Covers (-1917761639/1000000 : ℚ) vp0011101111110 := cover_leaf (by decide +kernel)
private noncomputable def vp001110111111_0 : Blocks := edgeBlocks% "full/vectors/001110111111-V-0000.bin"
noncomputable def vp001110111111 : Blocks := vp001110111111_0
private theorem bp0011101111110 : Branch 0 (-1917761639/2000000 : ℚ) vp001110111111 := by
  apply branch_left_normalized (c:=vp0011101111110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1917761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1917761639/1000000 : ℚ) by norm_num]
  exact coverp0011101111110
private noncomputable def ep0011101111111_0 : Blocks := edgeBlocks% "full/vectors/0011101111111-E-0000.bin"
noncomputable def ep0011101111111 : Blocks := ep0011101111111_0
private theorem idp0011101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110111111.list =
    C ((2:ℤ)^71) * horner X vp0011101111111.list + horner X ep0011101111111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011101111111 : Branch 1 (-1917761639/2000000 : ℚ) vp001110111111 := by
  apply branch_checked idp0011101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1917761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1918761639/1000000 : ℚ) by norm_num]
  exact coverp0011101111111
theorem coverp001110111111 : Covers (-1917761639/2000000 : ℚ) vp001110111111 := join_branches bp0011101111110 bp0011101111111
private noncomputable def vp0011101111101_0 : Blocks := edgeBlocks% "full/vectors/0011101111101-V-0000.bin"
noncomputable def vp0011101111101 : Blocks := vp0011101111101_0
theorem coverp0011101111101 : Covers (-1916761639/1000000 : ℚ) vp0011101111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011101111100_0 : Blocks := edgeBlocks% "full/vectors/0011101111100-V-0000.bin"
noncomputable def vp0011101111100 : Blocks := vp0011101111100_0
theorem coverp0011101111100 : Covers (-1915761639/1000000 : ℚ) vp0011101111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001110111110_0 : Blocks := edgeBlocks% "full/vectors/001110111110-V-0000.bin"
noncomputable def vp001110111110 : Blocks := vp001110111110_0
private theorem bp0011101111100 : Branch 0 (-1915761639/2000000 : ℚ) vp001110111110 := by
  apply branch_left_normalized (c:=vp0011101111100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1915761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1915761639/1000000 : ℚ) by norm_num]
  exact coverp0011101111100
private noncomputable def ep0011101111101_0 : Blocks := edgeBlocks% "full/vectors/0011101111101-E-0000.bin"
noncomputable def ep0011101111101 : Blocks := ep0011101111101_0
private theorem idp0011101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110111110.list =
    C ((2:ℤ)^70) * horner X vp0011101111101.list + horner X ep0011101111101.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011101111101 : Branch 1 (-1915761639/2000000 : ℚ) vp001110111110 := by
  apply branch_checked idp0011101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1915761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1916761639/1000000 : ℚ) by norm_num]
  exact coverp0011101111101
theorem coverp001110111110 : Covers (-1915761639/2000000 : ℚ) vp001110111110 := join_branches bp0011101111100 bp0011101111101
private noncomputable def vp00111011111_0 : Blocks := edgeBlocks% "full/vectors/00111011111-V-0000.bin"
noncomputable def vp00111011111 : Blocks := vp00111011111_0
private theorem bp001110111110 : Branch 0 (-1915761639/4000000 : ℚ) vp00111011111 := by
  apply branch_left_normalized (c:=vp001110111110) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1915761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1915761639/2000000 : ℚ) by norm_num]
  exact coverp001110111110
private noncomputable def ep001110111111_0 : Blocks := edgeBlocks% "full/vectors/001110111111-E-0000.bin"
noncomputable def ep001110111111 : Blocks := ep001110111111_0
private theorem idp001110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111011111.list =
    C ((2:ℤ)^123) * horner X vp001110111111.list + horner X ep001110111111.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110111111 : Branch 1 (-1915761639/4000000 : ℚ) vp00111011111 := by
  apply branch_checked idp001110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1915761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1917761639/2000000 : ℚ) by norm_num]
  exact coverp001110111111
theorem coverp00111011111 : Covers (-1915761639/4000000 : ℚ) vp00111011111 := join_branches bp001110111110 bp001110111111
private noncomputable def vp001110111101_0 : Blocks := edgeBlocks% "full/vectors/001110111101-V-0000.bin"
noncomputable def vp001110111101 : Blocks := vp001110111101_0
theorem coverp001110111101 : Covers (-1913761639/2000000 : ℚ) vp001110111101 := cover_leaf (by decide +kernel)
private noncomputable def vp001110111100_0 : Blocks := edgeBlocks% "full/vectors/001110111100-V-0000.bin"
noncomputable def vp001110111100 : Blocks := vp001110111100_0
theorem coverp001110111100 : Covers (-1911761639/2000000 : ℚ) vp001110111100 := cover_leaf (by decide +kernel)
private noncomputable def vp00111011110_0 : Blocks := edgeBlocks% "full/vectors/00111011110-V-0000.bin"
noncomputable def vp00111011110 : Blocks := vp00111011110_0
private theorem bp001110111100 : Branch 0 (-1911761639/4000000 : ℚ) vp00111011110 := by
  apply branch_left_normalized (c:=vp001110111100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1911761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1911761639/2000000 : ℚ) by norm_num]
  exact coverp001110111100
private noncomputable def ep001110111101_0 : Blocks := edgeBlocks% "full/vectors/001110111101-E-0000.bin"
noncomputable def ep001110111101 : Blocks := ep001110111101_0
private theorem idp001110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111011110.list =
    C ((2:ℤ)^122) * horner X vp001110111101.list + horner X ep001110111101.list := by
  exact edge_identity (B := (2:ℤ)^258) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110111101 : Branch 1 (-1911761639/4000000 : ℚ) vp00111011110 := by
  apply branch_checked idp001110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1911761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1913761639/2000000 : ℚ) by norm_num]
  exact coverp001110111101
theorem coverp00111011110 : Covers (-1911761639/4000000 : ℚ) vp00111011110 := join_branches bp001110111100 bp001110111101
private noncomputable def vp0011101111_0 : Blocks := edgeBlocks% "full/vectors/0011101111-V-0000.bin"
private noncomputable def vp0011101111_1 : Blocks := edgeBlocks% "full/vectors/0011101111-V-0001.bin"
noncomputable def vp0011101111 : Blocks := (Blocks.join vp0011101111_0 vp0011101111_1)
private theorem bp00111011110 : Branch 0 (-1911761639/8000000 : ℚ) vp0011101111 := by
  apply branch_left_normalized (c:=vp00111011110) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-1911761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1911761639/4000000 : ℚ) by norm_num]
  exact coverp00111011110
private noncomputable def ep00111011111_0 : Blocks := edgeBlocks% "full/vectors/00111011111-E-0000.bin"
private noncomputable def ep00111011111_1 : Blocks := edgeBlocks% "full/vectors/00111011111-E-0001.bin"
noncomputable def ep00111011111 : Blocks := (Blocks.join ep00111011111_0 ep00111011111_1)
private theorem idp00111011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011101111.list =
    C ((2:ℤ)^223) * horner X vp00111011111.list + horner X ep00111011111.list := by
  exact edge_identity (B := (2:ℤ)^395) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111011111 : Branch 1 (-1911761639/8000000 : ℚ) vp0011101111 := by
  apply branch_checked idp00111011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1911761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1915761639/4000000 : ℚ) by norm_num]
  exact coverp00111011111
theorem coverp0011101111 : Covers (-1911761639/8000000 : ℚ) vp0011101111 := join_branches bp00111011110 bp00111011111
private noncomputable def vp001110111011_0 : Blocks := edgeBlocks% "full/vectors/001110111011-V-0000.bin"
noncomputable def vp001110111011 : Blocks := vp001110111011_0
theorem coverp001110111011 : Covers (-1909761639/2000000 : ℚ) vp001110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp001110111010_0 : Blocks := edgeBlocks% "full/vectors/001110111010-V-0000.bin"
noncomputable def vp001110111010 : Blocks := vp001110111010_0
theorem coverp001110111010 : Covers (-1907761639/2000000 : ℚ) vp001110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp00111011101_0 : Blocks := edgeBlocks% "full/vectors/00111011101-V-0000.bin"
noncomputable def vp00111011101 : Blocks := vp00111011101_0
private theorem bp001110111010 : Branch 0 (-1907761639/4000000 : ℚ) vp00111011101 := by
  apply branch_left_normalized (c:=vp001110111010) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1907761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1907761639/2000000 : ℚ) by norm_num]
  exact coverp001110111010
private noncomputable def ep001110111011_0 : Blocks := edgeBlocks% "full/vectors/001110111011-E-0000.bin"
noncomputable def ep001110111011 : Blocks := ep001110111011_0
private theorem idp001110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111011101.list =
    C ((2:ℤ)^126) * horner X vp001110111011.list + horner X ep001110111011.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110111011 : Branch 1 (-1907761639/4000000 : ℚ) vp00111011101 := by
  apply branch_checked idp001110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1907761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1909761639/2000000 : ℚ) by norm_num]
  exact coverp001110111011
theorem coverp00111011101 : Covers (-1907761639/4000000 : ℚ) vp00111011101 := join_branches bp001110111010 bp001110111011
private noncomputable def vp0011101110011_0 : Blocks := edgeBlocks% "full/vectors/0011101110011-V-0000.bin"
noncomputable def vp0011101110011 : Blocks := vp0011101110011_0
theorem coverp0011101110011 : Covers (-1906761639/1000000 : ℚ) vp0011101110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011101110010_0 : Blocks := edgeBlocks% "full/vectors/0011101110010-V-0000.bin"
noncomputable def vp0011101110010 : Blocks := vp0011101110010_0
theorem coverp0011101110010 : Covers (-1905761639/1000000 : ℚ) vp0011101110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001110111001_0 : Blocks := edgeBlocks% "full/vectors/001110111001-V-0000.bin"
noncomputable def vp001110111001 : Blocks := vp001110111001_0
private theorem bp0011101110010 : Branch 0 (-1905761639/2000000 : ℚ) vp001110111001 := by
  apply branch_left_normalized (c:=vp0011101110010) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-1905761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1905761639/1000000 : ℚ) by norm_num]
  exact coverp0011101110010
private noncomputable def ep0011101110011_0 : Blocks := edgeBlocks% "full/vectors/0011101110011-E-0000.bin"
noncomputable def ep0011101110011 : Blocks := ep0011101110011_0
private theorem idp0011101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110111001.list =
    C ((2:ℤ)^69) * horner X vp0011101110011.list + horner X ep0011101110011.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011101110011 : Branch 1 (-1905761639/2000000 : ℚ) vp001110111001 := by
  apply branch_checked idp0011101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1905761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1906761639/1000000 : ℚ) by norm_num]
  exact coverp0011101110011
theorem coverp001110111001 : Covers (-1905761639/2000000 : ℚ) vp001110111001 := join_branches bp0011101110010 bp0011101110011
private noncomputable def vp001110111000_0 : Blocks := edgeBlocks% "full/vectors/001110111000-V-0000.bin"
noncomputable def vp001110111000 : Blocks := vp001110111000_0
theorem coverp001110111000 : Covers (-1903761639/2000000 : ℚ) vp001110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00111011100_0 : Blocks := edgeBlocks% "full/vectors/00111011100-V-0000.bin"
noncomputable def vp00111011100 : Blocks := vp00111011100_0
private theorem bp001110111000 : Branch 0 (-1903761639/4000000 : ℚ) vp00111011100 := by
  apply branch_left_normalized (c:=vp001110111000) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-1903761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1903761639/2000000 : ℚ) by norm_num]
  exact coverp001110111000
private noncomputable def ep001110111001_0 : Blocks := edgeBlocks% "full/vectors/001110111001-E-0000.bin"
noncomputable def ep001110111001 : Blocks := ep001110111001_0
private theorem idp001110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111011100.list =
    C ((2:ℤ)^118) * horner X vp001110111001.list + horner X ep001110111001.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110111001 : Branch 1 (-1903761639/4000000 : ℚ) vp00111011100 := by
  apply branch_checked idp001110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1903761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1905761639/2000000 : ℚ) by norm_num]
  exact coverp001110111001
theorem coverp00111011100 : Covers (-1903761639/4000000 : ℚ) vp00111011100 := join_branches bp001110111000 bp001110111001
private noncomputable def vp0011101110_0 : Blocks := edgeBlocks% "full/vectors/0011101110-V-0000.bin"
private noncomputable def vp0011101110_1 : Blocks := edgeBlocks% "full/vectors/0011101110-V-0001.bin"
noncomputable def vp0011101110 : Blocks := (Blocks.join vp0011101110_0 vp0011101110_1)
private theorem bp00111011100 : Branch 0 (-1903761639/8000000 : ℚ) vp0011101110 := by
  apply branch_left_normalized (c:=vp00111011100) (k:=0) (m:=108) (by decide +kernel)
  rw [show 2*(-1903761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1903761639/4000000 : ℚ) by norm_num]
  exact coverp00111011100
private noncomputable def ep00111011101_0 : Blocks := edgeBlocks% "full/vectors/00111011101-E-0000.bin"
private noncomputable def ep00111011101_1 : Blocks := edgeBlocks% "full/vectors/00111011101-E-0001.bin"
noncomputable def ep00111011101 : Blocks := (Blocks.join ep00111011101_0 ep00111011101_1)
private theorem idp00111011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011101110.list =
    C ((2:ℤ)^217) * horner X vp00111011101.list + horner X ep00111011101.list := by
  exact edge_identity (B := (2:ℤ)^391) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111011101 : Branch 1 (-1903761639/8000000 : ℚ) vp0011101110 := by
  apply branch_checked idp00111011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1903761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1907761639/4000000 : ℚ) by norm_num]
  exact coverp00111011101
theorem coverp0011101110 : Covers (-1903761639/8000000 : ℚ) vp0011101110 := join_branches bp00111011100 bp00111011101
private noncomputable def vp001110111_0 : Blocks := edgeBlocks% "full/vectors/001110111-V-0000.bin"
private noncomputable def vp001110111_1 : Blocks := edgeBlocks% "full/vectors/001110111-V-0001.bin"
private noncomputable def vp001110111_2 : Blocks := edgeBlocks% "full/vectors/001110111-V-0002.bin"
noncomputable def vp001110111 : Blocks := (Blocks.join vp001110111_0 (Blocks.join vp001110111_1 vp001110111_2))
private theorem bp0011101110 : Branch 0 (-1903761639/16000000 : ℚ) vp001110111 := by
  apply branch_left_normalized (c:=vp0011101110) (k:=0) (m:=199) (by decide +kernel)
  rw [show 2*(-1903761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1903761639/8000000 : ℚ) by norm_num]
  exact coverp0011101110
private noncomputable def ep0011101111_0 : Blocks := edgeBlocks% "full/vectors/0011101111-E-0000.bin"
private noncomputable def ep0011101111_1 : Blocks := edgeBlocks% "full/vectors/0011101111-E-0001.bin"
private noncomputable def ep0011101111_2 : Blocks := edgeBlocks% "full/vectors/0011101111-E-0002.bin"
noncomputable def ep0011101111 : Blocks := (Blocks.join ep0011101111_0 (Blocks.join ep0011101111_1 ep0011101111_2))
private theorem idp0011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110111.list =
    C ((2:ℤ)^422) * horner X vp0011101111.list + horner X ep0011101111.list := by
  exact edge_identity (B := (2:ℤ)^666) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011101111 : Branch 1 (-1903761639/16000000 : ℚ) vp001110111 := by
  apply branch_checked idp0011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1903761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1911761639/8000000 : ℚ) by norm_num]
  exact coverp0011101111
theorem coverp001110111 : Covers (-1903761639/16000000 : ℚ) vp001110111 := join_branches bp0011101110 bp0011101111
private noncomputable def vp001110110111_0 : Blocks := edgeBlocks% "full/vectors/001110110111-V-0000.bin"
noncomputable def vp001110110111 : Blocks := vp001110110111_0
theorem coverp001110110111 : Covers (-1901761639/2000000 : ℚ) vp001110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp001110110110_0 : Blocks := edgeBlocks% "full/vectors/001110110110-V-0000.bin"
noncomputable def vp001110110110 : Blocks := vp001110110110_0
theorem coverp001110110110 : Covers (-1899761639/2000000 : ℚ) vp001110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00111011011_0 : Blocks := edgeBlocks% "full/vectors/00111011011-V-0000.bin"
noncomputable def vp00111011011 : Blocks := vp00111011011_0
private theorem bp001110110110 : Branch 0 (-1899761639/4000000 : ℚ) vp00111011011 := by
  apply branch_left_normalized (c:=vp001110110110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-1899761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1899761639/2000000 : ℚ) by norm_num]
  exact coverp001110110110
private noncomputable def ep001110110111_0 : Blocks := edgeBlocks% "full/vectors/001110110111-E-0000.bin"
noncomputable def ep001110110111 : Blocks := ep001110110111_0
private theorem idp001110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111011011.list =
    C ((2:ℤ)^119) * horner X vp001110110111.list + horner X ep001110110111.list := by
  exact edge_identity (B := (2:ℤ)^249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110110111 : Branch 1 (-1899761639/4000000 : ℚ) vp00111011011 := by
  apply branch_checked idp001110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1899761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1901761639/2000000 : ℚ) by norm_num]
  exact coverp001110110111
theorem coverp00111011011 : Covers (-1899761639/4000000 : ℚ) vp00111011011 := join_branches bp001110110110 bp001110110111
private noncomputable def vp001110110101_0 : Blocks := edgeBlocks% "full/vectors/001110110101-V-0000.bin"
noncomputable def vp001110110101 : Blocks := vp001110110101_0
theorem coverp001110110101 : Covers (-1897761639/2000000 : ℚ) vp001110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp001110110100_0 : Blocks := edgeBlocks% "full/vectors/001110110100-V-0000.bin"
noncomputable def vp001110110100 : Blocks := vp001110110100_0
theorem coverp001110110100 : Covers (-1895761639/2000000 : ℚ) vp001110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp00111011010_0 : Blocks := edgeBlocks% "full/vectors/00111011010-V-0000.bin"
noncomputable def vp00111011010 : Blocks := vp00111011010_0
private theorem bp001110110100 : Branch 0 (-1895761639/4000000 : ℚ) vp00111011010 := by
  apply branch_left_normalized (c:=vp001110110100) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-1895761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1895761639/2000000 : ℚ) by norm_num]
  exact coverp001110110100
private noncomputable def ep001110110101_0 : Blocks := edgeBlocks% "full/vectors/001110110101-E-0000.bin"
noncomputable def ep001110110101 : Blocks := ep001110110101_0
private theorem idp001110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111011010.list =
    C ((2:ℤ)^118) * horner X vp001110110101.list + horner X ep001110110101.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110110101 : Branch 1 (-1895761639/4000000 : ℚ) vp00111011010 := by
  apply branch_checked idp001110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1895761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1897761639/2000000 : ℚ) by norm_num]
  exact coverp001110110101
theorem coverp00111011010 : Covers (-1895761639/4000000 : ℚ) vp00111011010 := join_branches bp001110110100 bp001110110101
private noncomputable def vp0011101101_0 : Blocks := edgeBlocks% "full/vectors/0011101101-V-0000.bin"
private noncomputable def vp0011101101_1 : Blocks := edgeBlocks% "full/vectors/0011101101-V-0001.bin"
noncomputable def vp0011101101 : Blocks := (Blocks.join vp0011101101_0 vp0011101101_1)
private theorem bp00111011010 : Branch 0 (-1895761639/8000000 : ℚ) vp0011101101 := by
  apply branch_left_normalized (c:=vp00111011010) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-1895761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1895761639/4000000 : ℚ) by norm_num]
  exact coverp00111011010
private noncomputable def ep00111011011_0 : Blocks := edgeBlocks% "full/vectors/00111011011-E-0000.bin"
private noncomputable def ep00111011011_1 : Blocks := edgeBlocks% "full/vectors/00111011011-E-0001.bin"
noncomputable def ep00111011011 : Blocks := (Blocks.join ep00111011011_0 ep00111011011_1)
private theorem idp00111011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011101101.list =
    C ((2:ℤ)^219) * horner X vp00111011011.list + horner X ep00111011011.list := by
  exact edge_identity (B := (2:ℤ)^385) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111011011 : Branch 1 (-1895761639/8000000 : ℚ) vp0011101101 := by
  apply branch_checked idp00111011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1895761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1899761639/4000000 : ℚ) by norm_num]
  exact coverp00111011011
theorem coverp0011101101 : Covers (-1895761639/8000000 : ℚ) vp0011101101 := join_branches bp00111011010 bp00111011011
private noncomputable def vp001110110011_0 : Blocks := edgeBlocks% "full/vectors/001110110011-V-0000.bin"
noncomputable def vp001110110011 : Blocks := vp001110110011_0
theorem coverp001110110011 : Covers (-1893761639/2000000 : ℚ) vp001110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp001110110010_0 : Blocks := edgeBlocks% "full/vectors/001110110010-V-0000.bin"
noncomputable def vp001110110010 : Blocks := vp001110110010_0
theorem coverp001110110010 : Covers (-1891761639/2000000 : ℚ) vp001110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00111011001_0 : Blocks := edgeBlocks% "full/vectors/00111011001-V-0000.bin"
noncomputable def vp00111011001 : Blocks := vp00111011001_0
private theorem bp001110110010 : Branch 0 (-1891761639/4000000 : ℚ) vp00111011001 := by
  apply branch_left_normalized (c:=vp001110110010) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-1891761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1891761639/2000000 : ℚ) by norm_num]
  exact coverp001110110010
private noncomputable def ep001110110011_0 : Blocks := edgeBlocks% "full/vectors/001110110011-E-0000.bin"
noncomputable def ep001110110011 : Blocks := ep001110110011_0
private theorem idp001110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111011001.list =
    C ((2:ℤ)^119) * horner X vp001110110011.list + horner X ep001110110011.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110110011 : Branch 1 (-1891761639/4000000 : ℚ) vp00111011001 := by
  apply branch_checked idp001110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1891761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1893761639/2000000 : ℚ) by norm_num]
  exact coverp001110110011
theorem coverp00111011001 : Covers (-1891761639/4000000 : ℚ) vp00111011001 := join_branches bp001110110010 bp001110110011
private noncomputable def vp001110110001_0 : Blocks := edgeBlocks% "full/vectors/001110110001-V-0000.bin"
noncomputable def vp001110110001 : Blocks := vp001110110001_0
theorem coverp001110110001 : Covers (-1889761639/2000000 : ℚ) vp001110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp001110110000_0 : Blocks := edgeBlocks% "full/vectors/001110110000-V-0000.bin"
noncomputable def vp001110110000 : Blocks := vp001110110000_0
theorem coverp001110110000 : Covers (-1887761639/2000000 : ℚ) vp001110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00111011000_0 : Blocks := edgeBlocks% "full/vectors/00111011000-V-0000.bin"
noncomputable def vp00111011000 : Blocks := vp00111011000_0
private theorem bp001110110000 : Branch 0 (-1887761639/4000000 : ℚ) vp00111011000 := by
  apply branch_left_normalized (c:=vp001110110000) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-1887761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1887761639/2000000 : ℚ) by norm_num]
  exact coverp001110110000
private noncomputable def ep001110110001_0 : Blocks := edgeBlocks% "full/vectors/001110110001-E-0000.bin"
noncomputable def ep001110110001 : Blocks := ep001110110001_0
private theorem idp001110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111011000.list =
    C ((2:ℤ)^117) * horner X vp001110110001.list + horner X ep001110110001.list := by
  exact edge_identity (B := (2:ℤ)^244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110110001 : Branch 1 (-1887761639/4000000 : ℚ) vp00111011000 := by
  apply branch_checked idp001110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1887761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1889761639/2000000 : ℚ) by norm_num]
  exact coverp001110110001
theorem coverp00111011000 : Covers (-1887761639/4000000 : ℚ) vp00111011000 := join_branches bp001110110000 bp001110110001
private noncomputable def vp0011101100_0 : Blocks := edgeBlocks% "full/vectors/0011101100-V-0000.bin"
private noncomputable def vp0011101100_1 : Blocks := edgeBlocks% "full/vectors/0011101100-V-0001.bin"
noncomputable def vp0011101100 : Blocks := (Blocks.join vp0011101100_0 vp0011101100_1)
private theorem bp00111011000 : Branch 0 (-1887761639/8000000 : ℚ) vp0011101100 := by
  apply branch_left_normalized (c:=vp00111011000) (k:=0) (m:=105) (by decide +kernel)
  rw [show 2*(-1887761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1887761639/4000000 : ℚ) by norm_num]
  exact coverp00111011000
private noncomputable def ep00111011001_0 : Blocks := edgeBlocks% "full/vectors/00111011001-E-0000.bin"
private noncomputable def ep00111011001_1 : Blocks := edgeBlocks% "full/vectors/00111011001-E-0001.bin"
noncomputable def ep00111011001 : Blocks := (Blocks.join ep00111011001_0 ep00111011001_1)
private theorem idp00111011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011101100.list =
    C ((2:ℤ)^219) * horner X vp00111011001.list + horner X ep00111011001.list := by
  exact edge_identity (B := (2:ℤ)^383) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111011001 : Branch 1 (-1887761639/8000000 : ℚ) vp0011101100 := by
  apply branch_checked idp00111011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1887761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1891761639/4000000 : ℚ) by norm_num]
  exact coverp00111011001
theorem coverp0011101100 : Covers (-1887761639/8000000 : ℚ) vp0011101100 := join_branches bp00111011000 bp00111011001
private noncomputable def vp001110110_0 : Blocks := edgeBlocks% "full/vectors/001110110-V-0000.bin"
private noncomputable def vp001110110_1 : Blocks := edgeBlocks% "full/vectors/001110110-V-0001.bin"
private noncomputable def vp001110110_2 : Blocks := edgeBlocks% "full/vectors/001110110-V-0002.bin"
noncomputable def vp001110110 : Blocks := (Blocks.join vp001110110_0 (Blocks.join vp001110110_1 vp001110110_2))
private theorem bp0011101100 : Branch 0 (-1887761639/16000000 : ℚ) vp001110110 := by
  apply branch_left_normalized (c:=vp0011101100) (k:=0) (m:=196) (by decide +kernel)
  rw [show 2*(-1887761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1887761639/8000000 : ℚ) by norm_num]
  exact coverp0011101100
private noncomputable def ep0011101101_0 : Blocks := edgeBlocks% "full/vectors/0011101101-E-0000.bin"
private noncomputable def ep0011101101_1 : Blocks := edgeBlocks% "full/vectors/0011101101-E-0001.bin"
private noncomputable def ep0011101101_2 : Blocks := edgeBlocks% "full/vectors/0011101101-E-0002.bin"
noncomputable def ep0011101101 : Blocks := (Blocks.join ep0011101101_0 (Blocks.join ep0011101101_1 ep0011101101_2))
private theorem idp0011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110110.list =
    C ((2:ℤ)^422) * horner X vp0011101101.list + horner X ep0011101101.list := by
  exact edge_identity (B := (2:ℤ)^659) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011101101 : Branch 1 (-1887761639/16000000 : ℚ) vp001110110 := by
  apply branch_checked idp0011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1887761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1895761639/8000000 : ℚ) by norm_num]
  exact coverp0011101101
theorem coverp001110110 : Covers (-1887761639/16000000 : ℚ) vp001110110 := join_branches bp0011101100 bp0011101101
private noncomputable def vp00111011_0 : Blocks := edgeBlocks% "full/vectors/00111011-V-0000.bin"
private noncomputable def vp00111011_1 : Blocks := edgeBlocks% "full/vectors/00111011-V-0001.bin"
private noncomputable def vp00111011_2 : Blocks := edgeBlocks% "full/vectors/00111011-V-0002.bin"
private noncomputable def vp00111011_3 : Blocks := edgeBlocks% "full/vectors/00111011-V-0003.bin"
private noncomputable def vp00111011_4 : Blocks := edgeBlocks% "full/vectors/00111011-V-0004.bin"
private noncomputable def vp00111011_5 : Blocks := edgeBlocks% "full/vectors/00111011-V-0005.bin"
noncomputable def vp00111011 : Blocks := (Blocks.join (Blocks.join vp00111011_0 (Blocks.join vp00111011_1 vp00111011_2)) (Blocks.join vp00111011_3 (Blocks.join vp00111011_4 vp00111011_5)))
private theorem bp001110110 : Branch 0 (-1887761639/32000000 : ℚ) vp00111011 := by
  apply branch_left_normalized (c:=vp001110110) (k:=0) (m:=376) (by decide +kernel)
  rw [show 2*(-1887761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1887761639/16000000 : ℚ) by norm_num]
  exact coverp001110110
private noncomputable def ep001110111_0 : Blocks := edgeBlocks% "full/vectors/001110111-E-0000.bin"
private noncomputable def ep001110111_1 : Blocks := edgeBlocks% "full/vectors/001110111-E-0001.bin"
private noncomputable def ep001110111_2 : Blocks := edgeBlocks% "full/vectors/001110111-E-0002.bin"
private noncomputable def ep001110111_3 : Blocks := edgeBlocks% "full/vectors/001110111-E-0003.bin"
private noncomputable def ep001110111_4 : Blocks := edgeBlocks% "full/vectors/001110111-E-0004.bin"
private noncomputable def ep001110111_5 : Blocks := edgeBlocks% "full/vectors/001110111-E-0005.bin"
noncomputable def ep001110111 : Blocks := (Blocks.join (Blocks.join ep001110111_0 (Blocks.join ep001110111_1 ep001110111_2)) (Blocks.join ep001110111_3 (Blocks.join ep001110111_4 ep001110111_5)))
private theorem idp001110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111011.list =
    C ((2:ℤ)^820) * horner X vp001110111.list + horner X ep001110111.list := by
  exact edge_identity (B := (2:ℤ)^1206) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110111 : Branch 1 (-1887761639/32000000 : ℚ) vp00111011 := by
  apply branch_checked idp001110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1887761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1903761639/16000000 : ℚ) by norm_num]
  exact coverp001110111
theorem coverp00111011 : Covers (-1887761639/32000000 : ℚ) vp00111011 := join_branches bp001110110 bp001110111
private noncomputable def vp001110101111_0 : Blocks := edgeBlocks% "full/vectors/001110101111-V-0000.bin"
noncomputable def vp001110101111 : Blocks := vp001110101111_0
theorem coverp001110101111 : Covers (-1885761639/2000000 : ℚ) vp001110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp001110101110_0 : Blocks := edgeBlocks% "full/vectors/001110101110-V-0000.bin"
noncomputable def vp001110101110 : Blocks := vp001110101110_0
theorem coverp001110101110 : Covers (-1883761639/2000000 : ℚ) vp001110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00111010111_0 : Blocks := edgeBlocks% "full/vectors/00111010111-V-0000.bin"
noncomputable def vp00111010111 : Blocks := vp00111010111_0
private theorem bp001110101110 : Branch 0 (-1883761639/4000000 : ℚ) vp00111010111 := by
  apply branch_left_normalized (c:=vp001110101110) (k:=0) (m:=59) (by decide +kernel)
  rw [show 2*(-1883761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1883761639/2000000 : ℚ) by norm_num]
  exact coverp001110101110
private noncomputable def ep001110101111_0 : Blocks := edgeBlocks% "full/vectors/001110101111-E-0000.bin"
noncomputable def ep001110101111 : Blocks := ep001110101111_0
private theorem idp001110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111010111.list =
    C ((2:ℤ)^119) * horner X vp001110101111.list + horner X ep001110101111.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110101111 : Branch 1 (-1883761639/4000000 : ℚ) vp00111010111 := by
  apply branch_checked idp001110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1883761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1885761639/2000000 : ℚ) by norm_num]
  exact coverp001110101111
theorem coverp00111010111 : Covers (-1883761639/4000000 : ℚ) vp00111010111 := join_branches bp001110101110 bp001110101111
private noncomputable def vp001110101101_0 : Blocks := edgeBlocks% "full/vectors/001110101101-V-0000.bin"
noncomputable def vp001110101101 : Blocks := vp001110101101_0
theorem coverp001110101101 : Covers (-1881761639/2000000 : ℚ) vp001110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp001110101100_0 : Blocks := edgeBlocks% "full/vectors/001110101100-V-0000.bin"
noncomputable def vp001110101100 : Blocks := vp001110101100_0
theorem coverp001110101100 : Covers (-1879761639/2000000 : ℚ) vp001110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00111010110_0 : Blocks := edgeBlocks% "full/vectors/00111010110-V-0000.bin"
noncomputable def vp00111010110 : Blocks := vp00111010110_0
private theorem bp001110101100 : Branch 0 (-1879761639/4000000 : ℚ) vp00111010110 := by
  apply branch_left_normalized (c:=vp001110101100) (k:=0) (m:=60) (by decide +kernel)
  rw [show 2*(-1879761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1879761639/2000000 : ℚ) by norm_num]
  exact coverp001110101100
private noncomputable def ep001110101101_0 : Blocks := edgeBlocks% "full/vectors/001110101101-E-0000.bin"
noncomputable def ep001110101101 : Blocks := ep001110101101_0
private theorem idp001110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111010110.list =
    C ((2:ℤ)^119) * horner X vp001110101101.list + horner X ep001110101101.list := by
  exact edge_identity (B := (2:ℤ)^246) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110101101 : Branch 1 (-1879761639/4000000 : ℚ) vp00111010110 := by
  apply branch_checked idp001110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1879761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1881761639/2000000 : ℚ) by norm_num]
  exact coverp001110101101
theorem coverp00111010110 : Covers (-1879761639/4000000 : ℚ) vp00111010110 := join_branches bp001110101100 bp001110101101
private noncomputable def vp0011101011_0 : Blocks := edgeBlocks% "full/vectors/0011101011-V-0000.bin"
private noncomputable def vp0011101011_1 : Blocks := edgeBlocks% "full/vectors/0011101011-V-0001.bin"
noncomputable def vp0011101011 : Blocks := (Blocks.join vp0011101011_0 vp0011101011_1)
private theorem bp00111010110 : Branch 0 (-1879761639/8000000 : ℚ) vp0011101011 := by
  apply branch_left_normalized (c:=vp00111010110) (k:=0) (m:=106) (by decide +kernel)
  rw [show 2*(-1879761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1879761639/4000000 : ℚ) by norm_num]
  exact coverp00111010110
private noncomputable def ep00111010111_0 : Blocks := edgeBlocks% "full/vectors/00111010111-E-0000.bin"
private noncomputable def ep00111010111_1 : Blocks := edgeBlocks% "full/vectors/00111010111-E-0001.bin"
noncomputable def ep00111010111 : Blocks := (Blocks.join ep00111010111_0 ep00111010111_1)
private theorem idp00111010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011101011.list =
    C ((2:ℤ)^221) * horner X vp00111010111.list + horner X ep00111010111.list := by
  exact edge_identity (B := (2:ℤ)^385) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111010111 : Branch 1 (-1879761639/8000000 : ℚ) vp0011101011 := by
  apply branch_checked idp00111010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1879761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1883761639/4000000 : ℚ) by norm_num]
  exact coverp00111010111
theorem coverp0011101011 : Covers (-1879761639/8000000 : ℚ) vp0011101011 := join_branches bp00111010110 bp00111010111
private noncomputable def vp001110101011_0 : Blocks := edgeBlocks% "full/vectors/001110101011-V-0000.bin"
noncomputable def vp001110101011 : Blocks := vp001110101011_0
theorem coverp001110101011 : Covers (-1877761639/2000000 : ℚ) vp001110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp001110101010_0 : Blocks := edgeBlocks% "full/vectors/001110101010-V-0000.bin"
noncomputable def vp001110101010 : Blocks := vp001110101010_0
theorem coverp001110101010 : Covers (-1875761639/2000000 : ℚ) vp001110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00111010101_0 : Blocks := edgeBlocks% "full/vectors/00111010101-V-0000.bin"
noncomputable def vp00111010101 : Blocks := vp00111010101_0
private theorem bp001110101010 : Branch 0 (-1875761639/4000000 : ℚ) vp00111010101 := by
  apply branch_left_normalized (c:=vp001110101010) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-1875761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1875761639/2000000 : ℚ) by norm_num]
  exact coverp001110101010
private noncomputable def ep001110101011_0 : Blocks := edgeBlocks% "full/vectors/001110101011-E-0000.bin"
noncomputable def ep001110101011 : Blocks := ep001110101011_0
private theorem idp001110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111010101.list =
    C ((2:ℤ)^120) * horner X vp001110101011.list + horner X ep001110101011.list := by
  exact edge_identity (B := (2:ℤ)^248) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110101011 : Branch 1 (-1875761639/4000000 : ℚ) vp00111010101 := by
  apply branch_checked idp001110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1875761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1877761639/2000000 : ℚ) by norm_num]
  exact coverp001110101011
theorem coverp00111010101 : Covers (-1875761639/4000000 : ℚ) vp00111010101 := join_branches bp001110101010 bp001110101011
private noncomputable def vp001110101001_0 : Blocks := edgeBlocks% "full/vectors/001110101001-V-0000.bin"
noncomputable def vp001110101001 : Blocks := vp001110101001_0
theorem coverp001110101001 : Covers (-1873761639/2000000 : ℚ) vp001110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp001110101000_0 : Blocks := edgeBlocks% "full/vectors/001110101000-V-0000.bin"
noncomputable def vp001110101000 : Blocks := vp001110101000_0
theorem coverp001110101000 : Covers (-1871761639/2000000 : ℚ) vp001110101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00111010100_0 : Blocks := edgeBlocks% "full/vectors/00111010100-V-0000.bin"
noncomputable def vp00111010100 : Blocks := vp00111010100_0
private theorem bp001110101000 : Branch 0 (-1871761639/4000000 : ℚ) vp00111010100 := by
  apply branch_left_normalized (c:=vp001110101000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-1871761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1871761639/2000000 : ℚ) by norm_num]
  exact coverp001110101000
private noncomputable def ep001110101001_0 : Blocks := edgeBlocks% "full/vectors/001110101001-E-0000.bin"
noncomputable def ep001110101001 : Blocks := ep001110101001_0
private theorem idp001110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111010100.list =
    C ((2:ℤ)^122) * horner X vp001110101001.list + horner X ep001110101001.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110101001 : Branch 1 (-1871761639/4000000 : ℚ) vp00111010100 := by
  apply branch_checked idp001110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1871761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1873761639/2000000 : ℚ) by norm_num]
  exact coverp001110101001
theorem coverp00111010100 : Covers (-1871761639/4000000 : ℚ) vp00111010100 := join_branches bp001110101000 bp001110101001
private noncomputable def vp0011101010_0 : Blocks := edgeBlocks% "full/vectors/0011101010-V-0000.bin"
private noncomputable def vp0011101010_1 : Blocks := edgeBlocks% "full/vectors/0011101010-V-0001.bin"
noncomputable def vp0011101010 : Blocks := (Blocks.join vp0011101010_0 vp0011101010_1)
private theorem bp00111010100 : Branch 0 (-1871761639/8000000 : ℚ) vp0011101010 := by
  apply branch_left_normalized (c:=vp00111010100) (k:=0) (m:=108) (by decide +kernel)
  rw [show 2*(-1871761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1871761639/4000000 : ℚ) by norm_num]
  exact coverp00111010100
private noncomputable def ep00111010101_0 : Blocks := edgeBlocks% "full/vectors/00111010101-E-0000.bin"
private noncomputable def ep00111010101_1 : Blocks := edgeBlocks% "full/vectors/00111010101-E-0001.bin"
noncomputable def ep00111010101 : Blocks := (Blocks.join ep00111010101_0 ep00111010101_1)
private theorem idp00111010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011101010.list =
    C ((2:ℤ)^225) * horner X vp00111010101.list + horner X ep00111010101.list := by
  exact edge_identity (B := (2:ℤ)^390) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111010101 : Branch 1 (-1871761639/8000000 : ℚ) vp0011101010 := by
  apply branch_checked idp00111010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1871761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1875761639/4000000 : ℚ) by norm_num]
  exact coverp00111010101
theorem coverp0011101010 : Covers (-1871761639/8000000 : ℚ) vp0011101010 := join_branches bp00111010100 bp00111010101
private noncomputable def vp001110101_0 : Blocks := edgeBlocks% "full/vectors/001110101-V-0000.bin"
private noncomputable def vp001110101_1 : Blocks := edgeBlocks% "full/vectors/001110101-V-0001.bin"
private noncomputable def vp001110101_2 : Blocks := edgeBlocks% "full/vectors/001110101-V-0002.bin"
noncomputable def vp001110101 : Blocks := (Blocks.join vp001110101_0 (Blocks.join vp001110101_1 vp001110101_2))
private theorem bp0011101010 : Branch 0 (-1871761639/16000000 : ℚ) vp001110101 := by
  apply branch_left_normalized (c:=vp0011101010) (k:=0) (m:=199) (by decide +kernel)
  rw [show 2*(-1871761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1871761639/8000000 : ℚ) by norm_num]
  exact coverp0011101010
private noncomputable def ep0011101011_0 : Blocks := edgeBlocks% "full/vectors/0011101011-E-0000.bin"
private noncomputable def ep0011101011_1 : Blocks := edgeBlocks% "full/vectors/0011101011-E-0001.bin"
private noncomputable def ep0011101011_2 : Blocks := edgeBlocks% "full/vectors/0011101011-E-0002.bin"
noncomputable def ep0011101011 : Blocks := (Blocks.join ep0011101011_0 (Blocks.join ep0011101011_1 ep0011101011_2))
private theorem idp0011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110101.list =
    C ((2:ℤ)^430) * horner X vp0011101011.list + horner X ep0011101011.list := by
  exact edge_identity (B := (2:ℤ)^668) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011101011 : Branch 1 (-1871761639/16000000 : ℚ) vp001110101 := by
  apply branch_checked idp0011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1871761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1879761639/8000000 : ℚ) by norm_num]
  exact coverp0011101011
theorem coverp001110101 : Covers (-1871761639/16000000 : ℚ) vp001110101 := join_branches bp0011101010 bp0011101011
private noncomputable def vp001110100111_0 : Blocks := edgeBlocks% "full/vectors/001110100111-V-0000.bin"
noncomputable def vp001110100111 : Blocks := vp001110100111_0
theorem coverp001110100111 : Covers (-1869761639/2000000 : ℚ) vp001110100111 := cover_leaf (by decide +kernel)
private noncomputable def vp001110100110_0 : Blocks := edgeBlocks% "full/vectors/001110100110-V-0000.bin"
noncomputable def vp001110100110 : Blocks := vp001110100110_0
theorem coverp001110100110 : Covers (-1867761639/2000000 : ℚ) vp001110100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00111010011_0 : Blocks := edgeBlocks% "full/vectors/00111010011-V-0000.bin"
noncomputable def vp00111010011 : Blocks := vp00111010011_0
private theorem bp001110100110 : Branch 0 (-1867761639/4000000 : ℚ) vp00111010011 := by
  apply branch_left_normalized (c:=vp001110100110) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-1867761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1867761639/2000000 : ℚ) by norm_num]
  exact coverp001110100110
private noncomputable def ep001110100111_0 : Blocks := edgeBlocks% "full/vectors/001110100111-E-0000.bin"
noncomputable def ep001110100111 : Blocks := ep001110100111_0
private theorem idp001110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111010011.list =
    C ((2:ℤ)^124) * horner X vp001110100111.list + horner X ep001110100111.list := by
  exact edge_identity (B := (2:ℤ)^256) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110100111 : Branch 1 (-1867761639/4000000 : ℚ) vp00111010011 := by
  apply branch_checked idp001110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1867761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1869761639/2000000 : ℚ) by norm_num]
  exact coverp001110100111
theorem coverp00111010011 : Covers (-1867761639/4000000 : ℚ) vp00111010011 := join_branches bp001110100110 bp001110100111
private noncomputable def vp001110100101_0 : Blocks := edgeBlocks% "full/vectors/001110100101-V-0000.bin"
noncomputable def vp001110100101 : Blocks := vp001110100101_0
theorem coverp001110100101 : Covers (-1865761639/2000000 : ℚ) vp001110100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011101001001_0 : Blocks := edgeBlocks% "full/vectors/0011101001001-V-0000.bin"
noncomputable def vp0011101001001 : Blocks := vp0011101001001_0
theorem coverp0011101001001 : Covers (-1864761639/1000000 : ℚ) vp0011101001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011101001000_0 : Blocks := edgeBlocks% "full/vectors/0011101001000-V-0000.bin"
noncomputable def vp0011101001000 : Blocks := vp0011101001000_0
theorem coverp0011101001000 : Covers (-1863761639/1000000 : ℚ) vp0011101001000 := cover_leaf (by decide +kernel)
private noncomputable def vp001110100100_0 : Blocks := edgeBlocks% "full/vectors/001110100100-V-0000.bin"
noncomputable def vp001110100100 : Blocks := vp001110100100_0
private theorem bp0011101001000 : Branch 0 (-1863761639/2000000 : ℚ) vp001110100100 := by
  apply branch_left_normalized (c:=vp0011101001000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1863761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1863761639/1000000 : ℚ) by norm_num]
  exact coverp0011101001000
private noncomputable def ep0011101001001_0 : Blocks := edgeBlocks% "full/vectors/0011101001001-E-0000.bin"
noncomputable def ep0011101001001 : Blocks := ep0011101001001_0
private theorem idp0011101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110100100.list =
    C ((2:ℤ)^70) * horner X vp0011101001001.list + horner X ep0011101001001.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011101001001 : Branch 1 (-1863761639/2000000 : ℚ) vp001110100100 := by
  apply branch_checked idp0011101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1863761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1864761639/1000000 : ℚ) by norm_num]
  exact coverp0011101001001
theorem coverp001110100100 : Covers (-1863761639/2000000 : ℚ) vp001110100100 := join_branches bp0011101001000 bp0011101001001
private noncomputable def vp00111010010_0 : Blocks := edgeBlocks% "full/vectors/00111010010-V-0000.bin"
noncomputable def vp00111010010 : Blocks := vp00111010010_0
private theorem bp001110100100 : Branch 0 (-1863761639/4000000 : ℚ) vp00111010010 := by
  apply branch_left_normalized (c:=vp001110100100) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1863761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1863761639/2000000 : ℚ) by norm_num]
  exact coverp001110100100
private noncomputable def ep001110100101_0 : Blocks := edgeBlocks% "full/vectors/001110100101-E-0000.bin"
noncomputable def ep001110100101 : Blocks := ep001110100101_0
private theorem idp001110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111010010.list =
    C ((2:ℤ)^122) * horner X vp001110100101.list + horner X ep001110100101.list := by
  exact edge_identity (B := (2:ℤ)^260) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110100101 : Branch 1 (-1863761639/4000000 : ℚ) vp00111010010 := by
  apply branch_checked idp001110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1863761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1865761639/2000000 : ℚ) by norm_num]
  exact coverp001110100101
theorem coverp00111010010 : Covers (-1863761639/4000000 : ℚ) vp00111010010 := join_branches bp001110100100 bp001110100101
private noncomputable def vp0011101001_0 : Blocks := edgeBlocks% "full/vectors/0011101001-V-0000.bin"
private noncomputable def vp0011101001_1 : Blocks := edgeBlocks% "full/vectors/0011101001-V-0001.bin"
noncomputable def vp0011101001 : Blocks := (Blocks.join vp0011101001_0 vp0011101001_1)
private theorem bp00111010010 : Branch 0 (-1863761639/8000000 : ℚ) vp0011101001 := by
  apply branch_left_normalized (c:=vp00111010010) (k:=0) (m:=111) (by decide +kernel)
  rw [show 2*(-1863761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1863761639/4000000 : ℚ) by norm_num]
  exact coverp00111010010
private noncomputable def ep00111010011_0 : Blocks := edgeBlocks% "full/vectors/00111010011-E-0000.bin"
private noncomputable def ep00111010011_1 : Blocks := edgeBlocks% "full/vectors/00111010011-E-0001.bin"
noncomputable def ep00111010011 : Blocks := (Blocks.join ep00111010011_0 ep00111010011_1)
private theorem idp00111010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011101001.list =
    C ((2:ℤ)^230) * horner X vp00111010011.list + horner X ep00111010011.list := by
  exact edge_identity (B := (2:ℤ)^401) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111010011 : Branch 1 (-1863761639/8000000 : ℚ) vp0011101001 := by
  apply branch_checked idp00111010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1863761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1867761639/4000000 : ℚ) by norm_num]
  exact coverp00111010011
theorem coverp0011101001 : Covers (-1863761639/8000000 : ℚ) vp0011101001 := join_branches bp00111010010 bp00111010011
private noncomputable def vp001110100011_0 : Blocks := edgeBlocks% "full/vectors/001110100011-V-0000.bin"
noncomputable def vp001110100011 : Blocks := vp001110100011_0
theorem coverp001110100011 : Covers (-1861761639/2000000 : ℚ) vp001110100011 := cover_leaf (by decide +kernel)
private noncomputable def vp001110100010_0 : Blocks := edgeBlocks% "full/vectors/001110100010-V-0000.bin"
noncomputable def vp001110100010 : Blocks := vp001110100010_0
theorem coverp001110100010 : Covers (-1859761639/2000000 : ℚ) vp001110100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00111010001_0 : Blocks := edgeBlocks% "full/vectors/00111010001-V-0000.bin"
noncomputable def vp00111010001 : Blocks := vp00111010001_0
private theorem bp001110100010 : Branch 0 (-1859761639/4000000 : ℚ) vp00111010001 := by
  apply branch_left_normalized (c:=vp001110100010) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-1859761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1859761639/2000000 : ℚ) by norm_num]
  exact coverp001110100010
private noncomputable def ep001110100011_0 : Blocks := edgeBlocks% "full/vectors/001110100011-E-0000.bin"
noncomputable def ep001110100011 : Blocks := ep001110100011_0
private theorem idp001110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111010001.list =
    C ((2:ℤ)^123) * horner X vp001110100011.list + horner X ep001110100011.list := by
  exact edge_identity (B := (2:ℤ)^258) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110100011 : Branch 1 (-1859761639/4000000 : ℚ) vp00111010001 := by
  apply branch_checked idp001110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1859761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1861761639/2000000 : ℚ) by norm_num]
  exact coverp001110100011
theorem coverp00111010001 : Covers (-1859761639/4000000 : ℚ) vp00111010001 := join_branches bp001110100010 bp001110100011
private noncomputable def vp001110100001_0 : Blocks := edgeBlocks% "full/vectors/001110100001-V-0000.bin"
noncomputable def vp001110100001 : Blocks := vp001110100001_0
theorem coverp001110100001 : Covers (-1857761639/2000000 : ℚ) vp001110100001 := cover_leaf (by decide +kernel)
private noncomputable def vp001110100000_0 : Blocks := edgeBlocks% "full/vectors/001110100000-V-0000.bin"
noncomputable def vp001110100000 : Blocks := vp001110100000_0
theorem coverp001110100000 : Covers (-1855761639/2000000 : ℚ) vp001110100000 := cover_leaf (by decide +kernel)
private noncomputable def vp00111010000_0 : Blocks := edgeBlocks% "full/vectors/00111010000-V-0000.bin"
noncomputable def vp00111010000 : Blocks := vp00111010000_0
private theorem bp001110100000 : Branch 0 (-1855761639/4000000 : ℚ) vp00111010000 := by
  apply branch_left_normalized (c:=vp001110100000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1855761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1855761639/2000000 : ℚ) by norm_num]
  exact coverp001110100000
private noncomputable def ep001110100001_0 : Blocks := edgeBlocks% "full/vectors/001110100001-E-0000.bin"
noncomputable def ep001110100001 : Blocks := ep001110100001_0
private theorem idp001110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111010000.list =
    C ((2:ℤ)^126) * horner X vp001110100001.list + horner X ep001110100001.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110100001 : Branch 1 (-1855761639/4000000 : ℚ) vp00111010000 := by
  apply branch_checked idp001110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1855761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1857761639/2000000 : ℚ) by norm_num]
  exact coverp001110100001
theorem coverp00111010000 : Covers (-1855761639/4000000 : ℚ) vp00111010000 := join_branches bp001110100000 bp001110100001
private noncomputable def vp0011101000_0 : Blocks := edgeBlocks% "full/vectors/0011101000-V-0000.bin"
private noncomputable def vp0011101000_1 : Blocks := edgeBlocks% "full/vectors/0011101000-V-0001.bin"
noncomputable def vp0011101000 : Blocks := (Blocks.join vp0011101000_0 vp0011101000_1)
private theorem bp00111010000 : Branch 0 (-1855761639/8000000 : ℚ) vp0011101000 := by
  apply branch_left_normalized (c:=vp00111010000) (k:=0) (m:=112) (by decide +kernel)
  rw [show 2*(-1855761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1855761639/4000000 : ℚ) by norm_num]
  exact coverp00111010000
private noncomputable def ep00111010001_0 : Blocks := edgeBlocks% "full/vectors/00111010001-E-0000.bin"
private noncomputable def ep00111010001_1 : Blocks := edgeBlocks% "full/vectors/00111010001-E-0001.bin"
noncomputable def ep00111010001 : Blocks := (Blocks.join ep00111010001_0 ep00111010001_1)
private theorem idp00111010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011101000.list =
    C ((2:ℤ)^229) * horner X vp00111010001.list + horner X ep00111010001.list := by
  exact edge_identity (B := (2:ℤ)^401) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111010001 : Branch 1 (-1855761639/8000000 : ℚ) vp0011101000 := by
  apply branch_checked idp00111010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1855761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1859761639/4000000 : ℚ) by norm_num]
  exact coverp00111010001
theorem coverp0011101000 : Covers (-1855761639/8000000 : ℚ) vp0011101000 := join_branches bp00111010000 bp00111010001
private noncomputable def vp001110100_0 : Blocks := edgeBlocks% "full/vectors/001110100-V-0000.bin"
private noncomputable def vp001110100_1 : Blocks := edgeBlocks% "full/vectors/001110100-V-0001.bin"
private noncomputable def vp001110100_2 : Blocks := edgeBlocks% "full/vectors/001110100-V-0002.bin"
private noncomputable def vp001110100_3 : Blocks := edgeBlocks% "full/vectors/001110100-V-0003.bin"
noncomputable def vp001110100 : Blocks := (Blocks.join (Blocks.join vp001110100_0 vp001110100_1) (Blocks.join vp001110100_2 vp001110100_3))
private theorem bp0011101000 : Branch 0 (-1855761639/16000000 : ℚ) vp001110100 := by
  apply branch_left_normalized (c:=vp0011101000) (k:=0) (m:=203) (by decide +kernel)
  rw [show 2*(-1855761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1855761639/8000000 : ℚ) by norm_num]
  exact coverp0011101000
private noncomputable def ep0011101001_0 : Blocks := edgeBlocks% "full/vectors/0011101001-E-0000.bin"
private noncomputable def ep0011101001_1 : Blocks := edgeBlocks% "full/vectors/0011101001-E-0001.bin"
private noncomputable def ep0011101001_2 : Blocks := edgeBlocks% "full/vectors/0011101001-E-0002.bin"
private noncomputable def ep0011101001_3 : Blocks := edgeBlocks% "full/vectors/0011101001-E-0003.bin"
noncomputable def ep0011101001 : Blocks := (Blocks.join (Blocks.join ep0011101001_0 ep0011101001_1) (Blocks.join ep0011101001_2 ep0011101001_3))
private theorem idp0011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110100.list =
    C ((2:ℤ)^432) * horner X vp0011101001.list + horner X ep0011101001.list := by
  exact edge_identity (B := (2:ℤ)^679) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011101001 : Branch 1 (-1855761639/16000000 : ℚ) vp001110100 := by
  apply branch_checked idp0011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1855761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1863761639/8000000 : ℚ) by norm_num]
  exact coverp0011101001
theorem coverp001110100 : Covers (-1855761639/16000000 : ℚ) vp001110100 := join_branches bp0011101000 bp0011101001
private noncomputable def vp00111010_0 : Blocks := edgeBlocks% "full/vectors/00111010-V-0000.bin"
private noncomputable def vp00111010_1 : Blocks := edgeBlocks% "full/vectors/00111010-V-0001.bin"
private noncomputable def vp00111010_2 : Blocks := edgeBlocks% "full/vectors/00111010-V-0002.bin"
private noncomputable def vp00111010_3 : Blocks := edgeBlocks% "full/vectors/00111010-V-0003.bin"
private noncomputable def vp00111010_4 : Blocks := edgeBlocks% "full/vectors/00111010-V-0004.bin"
private noncomputable def vp00111010_5 : Blocks := edgeBlocks% "full/vectors/00111010-V-0005.bin"
noncomputable def vp00111010 : Blocks := (Blocks.join (Blocks.join vp00111010_0 (Blocks.join vp00111010_1 vp00111010_2)) (Blocks.join vp00111010_3 (Blocks.join vp00111010_4 vp00111010_5)))
private theorem bp001110100 : Branch 0 (-1855761639/32000000 : ℚ) vp00111010 := by
  apply branch_left_normalized (c:=vp001110100) (k:=0) (m:=385) (by decide +kernel)
  rw [show 2*(-1855761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1855761639/16000000 : ℚ) by norm_num]
  exact coverp001110100
private noncomputable def ep001110101_0 : Blocks := edgeBlocks% "full/vectors/001110101-E-0000.bin"
private noncomputable def ep001110101_1 : Blocks := edgeBlocks% "full/vectors/001110101-E-0001.bin"
private noncomputable def ep001110101_2 : Blocks := edgeBlocks% "full/vectors/001110101-E-0002.bin"
private noncomputable def ep001110101_3 : Blocks := edgeBlocks% "full/vectors/001110101-E-0003.bin"
private noncomputable def ep001110101_4 : Blocks := edgeBlocks% "full/vectors/001110101-E-0004.bin"
private noncomputable def ep001110101_5 : Blocks := edgeBlocks% "full/vectors/001110101-E-0005.bin"
noncomputable def ep001110101 : Blocks := (Blocks.join (Blocks.join ep001110101_0 (Blocks.join ep001110101_1 ep001110101_2)) (Blocks.join ep001110101_3 (Blocks.join ep001110101_4 ep001110101_5)))
private theorem idp001110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111010.list =
    C ((2:ℤ)^843) * horner X vp001110101.list + horner X ep001110101.list := by
  exact edge_identity (B := (2:ℤ)^1231) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110101 : Branch 1 (-1855761639/32000000 : ℚ) vp00111010 := by
  apply branch_checked idp001110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1855761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1871761639/16000000 : ℚ) by norm_num]
  exact coverp001110101
theorem coverp00111010 : Covers (-1855761639/32000000 : ℚ) vp00111010 := join_branches bp001110100 bp001110101
private noncomputable def vp0011101_0 : Blocks := edgeBlocks% "full/vectors/0011101-V-0000.bin"
private noncomputable def vp0011101_1 : Blocks := edgeBlocks% "full/vectors/0011101-V-0001.bin"
private noncomputable def vp0011101_2 : Blocks := edgeBlocks% "full/vectors/0011101-V-0002.bin"
private noncomputable def vp0011101_3 : Blocks := edgeBlocks% "full/vectors/0011101-V-0003.bin"
private noncomputable def vp0011101_4 : Blocks := edgeBlocks% "full/vectors/0011101-V-0004.bin"
private noncomputable def vp0011101_5 : Blocks := edgeBlocks% "full/vectors/0011101-V-0005.bin"
private noncomputable def vp0011101_6 : Blocks := edgeBlocks% "full/vectors/0011101-V-0006.bin"
private noncomputable def vp0011101_7 : Blocks := edgeBlocks% "full/vectors/0011101-V-0007.bin"
private noncomputable def vp0011101_8 : Blocks := edgeBlocks% "full/vectors/0011101-V-0008.bin"
private noncomputable def vp0011101_9 : Blocks := edgeBlocks% "full/vectors/0011101-V-0009.bin"
private noncomputable def vp0011101_10 : Blocks := edgeBlocks% "full/vectors/0011101-V-0010.bin"
private noncomputable def vp0011101_11 : Blocks := edgeBlocks% "full/vectors/0011101-V-0011.bin"
noncomputable def vp0011101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0011101_0 (Blocks.join vp0011101_1 vp0011101_2)) (Blocks.join vp0011101_3 (Blocks.join vp0011101_4 vp0011101_5))) (Blocks.join (Blocks.join vp0011101_6 (Blocks.join vp0011101_7 vp0011101_8)) (Blocks.join vp0011101_9 (Blocks.join vp0011101_10 vp0011101_11))))
private theorem bp00111010 : Branch 0 (-1855761639/64000000 : ℚ) vp0011101 := by
  apply branch_left_normalized (c:=vp00111010) (k:=0) (m:=744) (by decide +kernel)
  rw [show 2*(-1855761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1855761639/32000000 : ℚ) by norm_num]
  exact coverp00111010
private noncomputable def ep00111011_0 : Blocks := edgeBlocks% "full/vectors/00111011-E-0000.bin"
private noncomputable def ep00111011_1 : Blocks := edgeBlocks% "full/vectors/00111011-E-0001.bin"
private noncomputable def ep00111011_2 : Blocks := edgeBlocks% "full/vectors/00111011-E-0002.bin"
private noncomputable def ep00111011_3 : Blocks := edgeBlocks% "full/vectors/00111011-E-0003.bin"
private noncomputable def ep00111011_4 : Blocks := edgeBlocks% "full/vectors/00111011-E-0004.bin"
private noncomputable def ep00111011_5 : Blocks := edgeBlocks% "full/vectors/00111011-E-0005.bin"
private noncomputable def ep00111011_6 : Blocks := edgeBlocks% "full/vectors/00111011-E-0006.bin"
private noncomputable def ep00111011_7 : Blocks := edgeBlocks% "full/vectors/00111011-E-0007.bin"
private noncomputable def ep00111011_8 : Blocks := edgeBlocks% "full/vectors/00111011-E-0008.bin"
private noncomputable def ep00111011_9 : Blocks := edgeBlocks% "full/vectors/00111011-E-0009.bin"
private noncomputable def ep00111011_10 : Blocks := edgeBlocks% "full/vectors/00111011-E-0010.bin"
private noncomputable def ep00111011_11 : Blocks := edgeBlocks% "full/vectors/00111011-E-0011.bin"
noncomputable def ep00111011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00111011_0 (Blocks.join ep00111011_1 ep00111011_2)) (Blocks.join ep00111011_3 (Blocks.join ep00111011_4 ep00111011_5))) (Blocks.join (Blocks.join ep00111011_6 (Blocks.join ep00111011_7 ep00111011_8)) (Blocks.join ep00111011_9 (Blocks.join ep00111011_10 ep00111011_11))))
private theorem idp00111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011101.list =
    C ((2:ℤ)^1645) * horner X vp00111011.list + horner X ep00111011.list := by
  exact edge_identity (B := (2:ℤ)^2320) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111011 : Branch 1 (-1855761639/64000000 : ℚ) vp0011101 := by
  apply branch_checked idp00111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1855761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1887761639/32000000 : ℚ) by norm_num]
  exact coverp00111011
theorem coverp0011101 : Covers (-1855761639/64000000 : ℚ) vp0011101 := join_branches bp00111010 bp00111011
end NextProof.EdgeFull

