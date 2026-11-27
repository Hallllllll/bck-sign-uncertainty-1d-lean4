import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic
import NextProof.EdgeFull00102

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp001110011111_0 : Blocks := edgeBlocks% "full/vectors/001110011111-V-0000.bin"
noncomputable def vp001110011111 : Blocks := vp001110011111_0
theorem coverp001110011111 : Covers (-1853761639/2000000 : ℚ) vp001110011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100111101_0 : Blocks := edgeBlocks% "full/vectors/0011100111101-V-0000.bin"
noncomputable def vp0011100111101 : Blocks := vp0011100111101_0
theorem coverp0011100111101 : Covers (-1852761639/1000000 : ℚ) vp0011100111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100111100_0 : Blocks := edgeBlocks% "full/vectors/0011100111100-V-0000.bin"
noncomputable def vp0011100111100 : Blocks := vp0011100111100_0
theorem coverp0011100111100 : Covers (-1851761639/1000000 : ℚ) vp0011100111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001110011110_0 : Blocks := edgeBlocks% "full/vectors/001110011110-V-0000.bin"
noncomputable def vp001110011110 : Blocks := vp001110011110_0
private theorem bp0011100111100 : Branch 0 (-1851761639/2000000 : ℚ) vp001110011110 := by
  apply branch_left_normalized (c:=vp0011100111100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1851761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1851761639/1000000 : ℚ) by norm_num]
  exact coverp0011100111100
private noncomputable def ep0011100111101_0 : Blocks := edgeBlocks% "full/vectors/0011100111101-E-0000.bin"
noncomputable def ep0011100111101 : Blocks := ep0011100111101_0
private theorem idp0011100111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110011110.list =
    C ((2:ℤ)^71) * horner X vp0011100111101.list + horner X ep0011100111101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100111101 : Branch 1 (-1851761639/2000000 : ℚ) vp001110011110 := by
  apply branch_checked idp0011100111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1851761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1852761639/1000000 : ℚ) by norm_num]
  exact coverp0011100111101
theorem coverp001110011110 : Covers (-1851761639/2000000 : ℚ) vp001110011110 := join_branches bp0011100111100 bp0011100111101
private noncomputable def vp00111001111_0 : Blocks := edgeBlocks% "full/vectors/00111001111-V-0000.bin"
noncomputable def vp00111001111 : Blocks := vp00111001111_0
private theorem bp001110011110 : Branch 0 (-1851761639/4000000 : ℚ) vp00111001111 := by
  apply branch_left_normalized (c:=vp001110011110) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1851761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1851761639/2000000 : ℚ) by norm_num]
  exact coverp001110011110
private noncomputable def ep001110011111_0 : Blocks := edgeBlocks% "full/vectors/001110011111-E-0000.bin"
noncomputable def ep001110011111 : Blocks := ep001110011111_0
private theorem idp001110011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111001111.list =
    C ((2:ℤ)^125) * horner X vp001110011111.list + horner X ep001110011111.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110011111 : Branch 1 (-1851761639/4000000 : ℚ) vp00111001111 := by
  apply branch_checked idp001110011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1851761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1853761639/2000000 : ℚ) by norm_num]
  exact coverp001110011111
theorem coverp00111001111 : Covers (-1851761639/4000000 : ℚ) vp00111001111 := join_branches bp001110011110 bp001110011111
private noncomputable def vp0011100111011_0 : Blocks := edgeBlocks% "full/vectors/0011100111011-V-0000.bin"
noncomputable def vp0011100111011 : Blocks := vp0011100111011_0
theorem coverp0011100111011 : Covers (-1850761639/1000000 : ℚ) vp0011100111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100111010_0 : Blocks := edgeBlocks% "full/vectors/0011100111010-V-0000.bin"
noncomputable def vp0011100111010 : Blocks := vp0011100111010_0
theorem coverp0011100111010 : Covers (-1849761639/1000000 : ℚ) vp0011100111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001110011101_0 : Blocks := edgeBlocks% "full/vectors/001110011101-V-0000.bin"
noncomputable def vp001110011101 : Blocks := vp001110011101_0
private theorem bp0011100111010 : Branch 0 (-1849761639/2000000 : ℚ) vp001110011101 := by
  apply branch_left_normalized (c:=vp0011100111010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1849761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1849761639/1000000 : ℚ) by norm_num]
  exact coverp0011100111010
private noncomputable def ep0011100111011_0 : Blocks := edgeBlocks% "full/vectors/0011100111011-E-0000.bin"
noncomputable def ep0011100111011 : Blocks := ep0011100111011_0
private theorem idp0011100111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110011101.list =
    C ((2:ℤ)^71) * horner X vp0011100111011.list + horner X ep0011100111011.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100111011 : Branch 1 (-1849761639/2000000 : ℚ) vp001110011101 := by
  apply branch_checked idp0011100111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1849761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1850761639/1000000 : ℚ) by norm_num]
  exact coverp0011100111011
theorem coverp001110011101 : Covers (-1849761639/2000000 : ℚ) vp001110011101 := join_branches bp0011100111010 bp0011100111011
private noncomputable def vp0011100111001_0 : Blocks := edgeBlocks% "full/vectors/0011100111001-V-0000.bin"
noncomputable def vp0011100111001 : Blocks := vp0011100111001_0
theorem coverp0011100111001 : Covers (-1848761639/1000000 : ℚ) vp0011100111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100111000_0 : Blocks := edgeBlocks% "full/vectors/0011100111000-V-0000.bin"
noncomputable def vp0011100111000 : Blocks := vp0011100111000_0
theorem coverp0011100111000 : Covers (-1847761639/1000000 : ℚ) vp0011100111000 := cover_leaf (by decide +kernel)
private noncomputable def vp001110011100_0 : Blocks := edgeBlocks% "full/vectors/001110011100-V-0000.bin"
noncomputable def vp001110011100 : Blocks := vp001110011100_0
private theorem bp0011100111000 : Branch 0 (-1847761639/2000000 : ℚ) vp001110011100 := by
  apply branch_left_normalized (c:=vp0011100111000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1847761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1847761639/1000000 : ℚ) by norm_num]
  exact coverp0011100111000
private noncomputable def ep0011100111001_0 : Blocks := edgeBlocks% "full/vectors/0011100111001-E-0000.bin"
noncomputable def ep0011100111001 : Blocks := ep0011100111001_0
private theorem idp0011100111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110011100.list =
    C ((2:ℤ)^72) * horner X vp0011100111001.list + horner X ep0011100111001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100111001 : Branch 1 (-1847761639/2000000 : ℚ) vp001110011100 := by
  apply branch_checked idp0011100111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1847761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1848761639/1000000 : ℚ) by norm_num]
  exact coverp0011100111001
theorem coverp001110011100 : Covers (-1847761639/2000000 : ℚ) vp001110011100 := join_branches bp0011100111000 bp0011100111001
private noncomputable def vp00111001110_0 : Blocks := edgeBlocks% "full/vectors/00111001110-V-0000.bin"
noncomputable def vp00111001110 : Blocks := vp00111001110_0
private theorem bp001110011100 : Branch 0 (-1847761639/4000000 : ℚ) vp00111001110 := by
  apply branch_left_normalized (c:=vp001110011100) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1847761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1847761639/2000000 : ℚ) by norm_num]
  exact coverp001110011100
private noncomputable def ep001110011101_0 : Blocks := edgeBlocks% "full/vectors/001110011101-E-0000.bin"
noncomputable def ep001110011101 : Blocks := ep001110011101_0
private theorem idp001110011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111001110.list =
    C ((2:ℤ)^125) * horner X vp001110011101.list + horner X ep001110011101.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110011101 : Branch 1 (-1847761639/4000000 : ℚ) vp00111001110 := by
  apply branch_checked idp001110011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1847761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1849761639/2000000 : ℚ) by norm_num]
  exact coverp001110011101
theorem coverp00111001110 : Covers (-1847761639/4000000 : ℚ) vp00111001110 := join_branches bp001110011100 bp001110011101
private noncomputable def vp0011100111_0 : Blocks := edgeBlocks% "full/vectors/0011100111-V-0000.bin"
private noncomputable def vp0011100111_1 : Blocks := edgeBlocks% "full/vectors/0011100111-V-0001.bin"
noncomputable def vp0011100111 : Blocks := (Blocks.join vp0011100111_0 vp0011100111_1)
private theorem bp00111001110 : Branch 0 (-1847761639/8000000 : ℚ) vp0011100111 := by
  apply branch_left_normalized (c:=vp00111001110) (k:=0) (m:=112) (by decide +kernel)
  rw [show 2*(-1847761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1847761639/4000000 : ℚ) by norm_num]
  exact coverp00111001110
private noncomputable def ep00111001111_0 : Blocks := edgeBlocks% "full/vectors/00111001111-E-0000.bin"
private noncomputable def ep00111001111_1 : Blocks := edgeBlocks% "full/vectors/00111001111-E-0001.bin"
noncomputable def ep00111001111 : Blocks := (Blocks.join ep00111001111_0 ep00111001111_1)
private theorem idp00111001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011100111.list =
    C ((2:ℤ)^228) * horner X vp00111001111.list + horner X ep00111001111.list := by
  exact edge_identity (B := (2:ℤ)^403) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111001111 : Branch 1 (-1847761639/8000000 : ℚ) vp0011100111 := by
  apply branch_checked idp00111001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1847761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1851761639/4000000 : ℚ) by norm_num]
  exact coverp00111001111
theorem coverp0011100111 : Covers (-1847761639/8000000 : ℚ) vp0011100111 := join_branches bp00111001110 bp00111001111
private noncomputable def vp001110011011_0 : Blocks := edgeBlocks% "full/vectors/001110011011-V-0000.bin"
noncomputable def vp001110011011 : Blocks := vp001110011011_0
theorem coverp001110011011 : Covers (-1845761639/2000000 : ℚ) vp001110011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100110101_0 : Blocks := edgeBlocks% "full/vectors/0011100110101-V-0000.bin"
noncomputable def vp0011100110101 : Blocks := vp0011100110101_0
theorem coverp0011100110101 : Covers (-1844761639/1000000 : ℚ) vp0011100110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100110100_0 : Blocks := edgeBlocks% "full/vectors/0011100110100-V-0000.bin"
noncomputable def vp0011100110100 : Blocks := vp0011100110100_0
theorem coverp0011100110100 : Covers (-1843761639/1000000 : ℚ) vp0011100110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001110011010_0 : Blocks := edgeBlocks% "full/vectors/001110011010-V-0000.bin"
noncomputable def vp001110011010 : Blocks := vp001110011010_0
private theorem bp0011100110100 : Branch 0 (-1843761639/2000000 : ℚ) vp001110011010 := by
  apply branch_left_normalized (c:=vp0011100110100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1843761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1843761639/1000000 : ℚ) by norm_num]
  exact coverp0011100110100
private noncomputable def ep0011100110101_0 : Blocks := edgeBlocks% "full/vectors/0011100110101-E-0000.bin"
noncomputable def ep0011100110101 : Blocks := ep0011100110101_0
private theorem idp0011100110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110011010.list =
    C ((2:ℤ)^73) * horner X vp0011100110101.list + horner X ep0011100110101.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100110101 : Branch 1 (-1843761639/2000000 : ℚ) vp001110011010 := by
  apply branch_checked idp0011100110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1843761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1844761639/1000000 : ℚ) by norm_num]
  exact coverp0011100110101
theorem coverp001110011010 : Covers (-1843761639/2000000 : ℚ) vp001110011010 := join_branches bp0011100110100 bp0011100110101
private noncomputable def vp00111001101_0 : Blocks := edgeBlocks% "full/vectors/00111001101-V-0000.bin"
noncomputable def vp00111001101 : Blocks := vp00111001101_0
private theorem bp001110011010 : Branch 0 (-1843761639/4000000 : ℚ) vp00111001101 := by
  apply branch_left_normalized (c:=vp001110011010) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1843761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1843761639/2000000 : ℚ) by norm_num]
  exact coverp001110011010
private noncomputable def ep001110011011_0 : Blocks := edgeBlocks% "full/vectors/001110011011-E-0000.bin"
noncomputable def ep001110011011 : Blocks := ep001110011011_0
private theorem idp001110011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111001101.list =
    C ((2:ℤ)^127) * horner X vp001110011011.list + horner X ep001110011011.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110011011 : Branch 1 (-1843761639/4000000 : ℚ) vp00111001101 := by
  apply branch_checked idp001110011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1843761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1845761639/2000000 : ℚ) by norm_num]
  exact coverp001110011011
theorem coverp00111001101 : Covers (-1843761639/4000000 : ℚ) vp00111001101 := join_branches bp001110011010 bp001110011011
private noncomputable def vp0011100110011_0 : Blocks := edgeBlocks% "full/vectors/0011100110011-V-0000.bin"
noncomputable def vp0011100110011 : Blocks := vp0011100110011_0
theorem coverp0011100110011 : Covers (-1842761639/1000000 : ℚ) vp0011100110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100110010_0 : Blocks := edgeBlocks% "full/vectors/0011100110010-V-0000.bin"
noncomputable def vp0011100110010 : Blocks := vp0011100110010_0
theorem coverp0011100110010 : Covers (-1841761639/1000000 : ℚ) vp0011100110010 := cover_leaf (by decide +kernel)
private noncomputable def vp001110011001_0 : Blocks := edgeBlocks% "full/vectors/001110011001-V-0000.bin"
noncomputable def vp001110011001 : Blocks := vp001110011001_0
private theorem bp0011100110010 : Branch 0 (-1841761639/2000000 : ℚ) vp001110011001 := by
  apply branch_left_normalized (c:=vp0011100110010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1841761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1841761639/1000000 : ℚ) by norm_num]
  exact coverp0011100110010
private noncomputable def ep0011100110011_0 : Blocks := edgeBlocks% "full/vectors/0011100110011-E-0000.bin"
noncomputable def ep0011100110011 : Blocks := ep0011100110011_0
private theorem idp0011100110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110011001.list =
    C ((2:ℤ)^72) * horner X vp0011100110011.list + horner X ep0011100110011.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100110011 : Branch 1 (-1841761639/2000000 : ℚ) vp001110011001 := by
  apply branch_checked idp0011100110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1841761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1842761639/1000000 : ℚ) by norm_num]
  exact coverp0011100110011
theorem coverp001110011001 : Covers (-1841761639/2000000 : ℚ) vp001110011001 := join_branches bp0011100110010 bp0011100110011
private noncomputable def vp0011100110001_0 : Blocks := edgeBlocks% "full/vectors/0011100110001-V-0000.bin"
noncomputable def vp0011100110001 : Blocks := vp0011100110001_0
theorem coverp0011100110001 : Covers (-1840761639/1000000 : ℚ) vp0011100110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100110000_0 : Blocks := edgeBlocks% "full/vectors/0011100110000-V-0000.bin"
noncomputable def vp0011100110000 : Blocks := vp0011100110000_0
theorem coverp0011100110000 : Covers (-1839761639/1000000 : ℚ) vp0011100110000 := cover_leaf (by decide +kernel)
private noncomputable def vp001110011000_0 : Blocks := edgeBlocks% "full/vectors/001110011000-V-0000.bin"
noncomputable def vp001110011000 : Blocks := vp001110011000_0
private theorem bp0011100110000 : Branch 0 (-1839761639/2000000 : ℚ) vp001110011000 := by
  apply branch_left_normalized (c:=vp0011100110000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1839761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1839761639/1000000 : ℚ) by norm_num]
  exact coverp0011100110000
private noncomputable def ep0011100110001_0 : Blocks := edgeBlocks% "full/vectors/0011100110001-E-0000.bin"
noncomputable def ep0011100110001 : Blocks := ep0011100110001_0
private theorem idp0011100110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110011000.list =
    C ((2:ℤ)^73) * horner X vp0011100110001.list + horner X ep0011100110001.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100110001 : Branch 1 (-1839761639/2000000 : ℚ) vp001110011000 := by
  apply branch_checked idp0011100110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1839761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1840761639/1000000 : ℚ) by norm_num]
  exact coverp0011100110001
theorem coverp001110011000 : Covers (-1839761639/2000000 : ℚ) vp001110011000 := join_branches bp0011100110000 bp0011100110001
private noncomputable def vp00111001100_0 : Blocks := edgeBlocks% "full/vectors/00111001100-V-0000.bin"
noncomputable def vp00111001100 : Blocks := vp00111001100_0
private theorem bp001110011000 : Branch 0 (-1839761639/4000000 : ℚ) vp00111001100 := by
  apply branch_left_normalized (c:=vp001110011000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1839761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1839761639/2000000 : ℚ) by norm_num]
  exact coverp001110011000
private noncomputable def ep001110011001_0 : Blocks := edgeBlocks% "full/vectors/001110011001-E-0000.bin"
noncomputable def ep001110011001 : Blocks := ep001110011001_0
private theorem idp001110011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111001100.list =
    C ((2:ℤ)^125) * horner X vp001110011001.list + horner X ep001110011001.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110011001 : Branch 1 (-1839761639/4000000 : ℚ) vp00111001100 := by
  apply branch_checked idp001110011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1839761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1841761639/2000000 : ℚ) by norm_num]
  exact coverp001110011001
theorem coverp00111001100 : Covers (-1839761639/4000000 : ℚ) vp00111001100 := join_branches bp001110011000 bp001110011001
private noncomputable def vp0011100110_0 : Blocks := edgeBlocks% "full/vectors/0011100110-V-0000.bin"
private noncomputable def vp0011100110_1 : Blocks := edgeBlocks% "full/vectors/0011100110-V-0001.bin"
noncomputable def vp0011100110 : Blocks := (Blocks.join vp0011100110_0 vp0011100110_1)
private theorem bp00111001100 : Branch 0 (-1839761639/8000000 : ℚ) vp0011100110 := by
  apply branch_left_normalized (c:=vp00111001100) (k:=0) (m:=112) (by decide +kernel)
  rw [show 2*(-1839761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1839761639/4000000 : ℚ) by norm_num]
  exact coverp00111001100
private noncomputable def ep00111001101_0 : Blocks := edgeBlocks% "full/vectors/00111001101-E-0000.bin"
private noncomputable def ep00111001101_1 : Blocks := edgeBlocks% "full/vectors/00111001101-E-0001.bin"
noncomputable def ep00111001101 : Blocks := (Blocks.join ep00111001101_0 ep00111001101_1)
private theorem idp00111001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011100110.list =
    C ((2:ℤ)^229) * horner X vp00111001101.list + horner X ep00111001101.list := by
  exact edge_identity (B := (2:ℤ)^405) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111001101 : Branch 1 (-1839761639/8000000 : ℚ) vp0011100110 := by
  apply branch_checked idp00111001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1839761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1843761639/4000000 : ℚ) by norm_num]
  exact coverp00111001101
theorem coverp0011100110 : Covers (-1839761639/8000000 : ℚ) vp0011100110 := join_branches bp00111001100 bp00111001101
private noncomputable def vp001110011_0 : Blocks := edgeBlocks% "full/vectors/001110011-V-0000.bin"
private noncomputable def vp001110011_1 : Blocks := edgeBlocks% "full/vectors/001110011-V-0001.bin"
private noncomputable def vp001110011_2 : Blocks := edgeBlocks% "full/vectors/001110011-V-0002.bin"
private noncomputable def vp001110011_3 : Blocks := edgeBlocks% "full/vectors/001110011-V-0003.bin"
noncomputable def vp001110011 : Blocks := (Blocks.join (Blocks.join vp001110011_0 vp001110011_1) (Blocks.join vp001110011_2 vp001110011_3))
private theorem bp0011100110 : Branch 0 (-1839761639/16000000 : ℚ) vp001110011 := by
  apply branch_left_normalized (c:=vp0011100110) (k:=0) (m:=205) (by decide +kernel)
  rw [show 2*(-1839761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1839761639/8000000 : ℚ) by norm_num]
  exact coverp0011100110
private noncomputable def ep0011100111_0 : Blocks := edgeBlocks% "full/vectors/0011100111-E-0000.bin"
private noncomputable def ep0011100111_1 : Blocks := edgeBlocks% "full/vectors/0011100111-E-0001.bin"
private noncomputable def ep0011100111_2 : Blocks := edgeBlocks% "full/vectors/0011100111-E-0002.bin"
private noncomputable def ep0011100111_3 : Blocks := edgeBlocks% "full/vectors/0011100111-E-0003.bin"
noncomputable def ep0011100111 : Blocks := (Blocks.join (Blocks.join ep0011100111_0 ep0011100111_1) (Blocks.join ep0011100111_2 ep0011100111_3))
private theorem idp0011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110011.list =
    C ((2:ℤ)^435) * horner X vp0011100111.list + horner X ep0011100111.list := by
  exact edge_identity (B := (2:ℤ)^684) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100111 : Branch 1 (-1839761639/16000000 : ℚ) vp001110011 := by
  apply branch_checked idp0011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1839761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1847761639/8000000 : ℚ) by norm_num]
  exact coverp0011100111
theorem coverp001110011 : Covers (-1839761639/16000000 : ℚ) vp001110011 := join_branches bp0011100110 bp0011100111
private noncomputable def vp0011100101111_0 : Blocks := edgeBlocks% "full/vectors/0011100101111-V-0000.bin"
noncomputable def vp0011100101111 : Blocks := vp0011100101111_0
theorem coverp0011100101111 : Covers (-1838761639/1000000 : ℚ) vp0011100101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100101110_0 : Blocks := edgeBlocks% "full/vectors/0011100101110-V-0000.bin"
noncomputable def vp0011100101110 : Blocks := vp0011100101110_0
theorem coverp0011100101110 : Covers (-1837761639/1000000 : ℚ) vp0011100101110 := cover_leaf (by decide +kernel)
private noncomputable def vp001110010111_0 : Blocks := edgeBlocks% "full/vectors/001110010111-V-0000.bin"
noncomputable def vp001110010111 : Blocks := vp001110010111_0
private theorem bp0011100101110 : Branch 0 (-1837761639/2000000 : ℚ) vp001110010111 := by
  apply branch_left_normalized (c:=vp0011100101110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1837761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1837761639/1000000 : ℚ) by norm_num]
  exact coverp0011100101110
private noncomputable def ep0011100101111_0 : Blocks := edgeBlocks% "full/vectors/0011100101111-E-0000.bin"
noncomputable def ep0011100101111 : Blocks := ep0011100101111_0
private theorem idp0011100101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110010111.list =
    C ((2:ℤ)^73) * horner X vp0011100101111.list + horner X ep0011100101111.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100101111 : Branch 1 (-1837761639/2000000 : ℚ) vp001110010111 := by
  apply branch_checked idp0011100101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1837761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1838761639/1000000 : ℚ) by norm_num]
  exact coverp0011100101111
theorem coverp001110010111 : Covers (-1837761639/2000000 : ℚ) vp001110010111 := join_branches bp0011100101110 bp0011100101111
private noncomputable def vp0011100101101_0 : Blocks := edgeBlocks% "full/vectors/0011100101101-V-0000.bin"
noncomputable def vp0011100101101 : Blocks := vp0011100101101_0
theorem coverp0011100101101 : Covers (-1836761639/1000000 : ℚ) vp0011100101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100101100_0 : Blocks := edgeBlocks% "full/vectors/0011100101100-V-0000.bin"
noncomputable def vp0011100101100 : Blocks := vp0011100101100_0
theorem coverp0011100101100 : Covers (-1835761639/1000000 : ℚ) vp0011100101100 := cover_leaf (by decide +kernel)
private noncomputable def vp001110010110_0 : Blocks := edgeBlocks% "full/vectors/001110010110-V-0000.bin"
noncomputable def vp001110010110 : Blocks := vp001110010110_0
private theorem bp0011100101100 : Branch 0 (-1835761639/2000000 : ℚ) vp001110010110 := by
  apply branch_left_normalized (c:=vp0011100101100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1835761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1835761639/1000000 : ℚ) by norm_num]
  exact coverp0011100101100
private noncomputable def ep0011100101101_0 : Blocks := edgeBlocks% "full/vectors/0011100101101-E-0000.bin"
noncomputable def ep0011100101101 : Blocks := ep0011100101101_0
private theorem idp0011100101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110010110.list =
    C ((2:ℤ)^73) * horner X vp0011100101101.list + horner X ep0011100101101.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100101101 : Branch 1 (-1835761639/2000000 : ℚ) vp001110010110 := by
  apply branch_checked idp0011100101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1835761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1836761639/1000000 : ℚ) by norm_num]
  exact coverp0011100101101
theorem coverp001110010110 : Covers (-1835761639/2000000 : ℚ) vp001110010110 := join_branches bp0011100101100 bp0011100101101
private noncomputable def vp00111001011_0 : Blocks := edgeBlocks% "full/vectors/00111001011-V-0000.bin"
noncomputable def vp00111001011 : Blocks := vp00111001011_0
private theorem bp001110010110 : Branch 0 (-1835761639/4000000 : ℚ) vp00111001011 := by
  apply branch_left_normalized (c:=vp001110010110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1835761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1835761639/2000000 : ℚ) by norm_num]
  exact coverp001110010110
private noncomputable def ep001110010111_0 : Blocks := edgeBlocks% "full/vectors/001110010111-E-0000.bin"
noncomputable def ep001110010111 : Blocks := ep001110010111_0
private theorem idp001110010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111001011.list =
    C ((2:ℤ)^126) * horner X vp001110010111.list + horner X ep001110010111.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110010111 : Branch 1 (-1835761639/4000000 : ℚ) vp00111001011 := by
  apply branch_checked idp001110010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1835761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1837761639/2000000 : ℚ) by norm_num]
  exact coverp001110010111
theorem coverp00111001011 : Covers (-1835761639/4000000 : ℚ) vp00111001011 := join_branches bp001110010110 bp001110010111
private noncomputable def vp0011100101011_0 : Blocks := edgeBlocks% "full/vectors/0011100101011-V-0000.bin"
noncomputable def vp0011100101011 : Blocks := vp0011100101011_0
theorem coverp0011100101011 : Covers (-1834761639/1000000 : ℚ) vp0011100101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100101010_0 : Blocks := edgeBlocks% "full/vectors/0011100101010-V-0000.bin"
noncomputable def vp0011100101010 : Blocks := vp0011100101010_0
theorem coverp0011100101010 : Covers (-1833761639/1000000 : ℚ) vp0011100101010 := cover_leaf (by decide +kernel)
private noncomputable def vp001110010101_0 : Blocks := edgeBlocks% "full/vectors/001110010101-V-0000.bin"
noncomputable def vp001110010101 : Blocks := vp001110010101_0
private theorem bp0011100101010 : Branch 0 (-1833761639/2000000 : ℚ) vp001110010101 := by
  apply branch_left_normalized (c:=vp0011100101010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1833761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1833761639/1000000 : ℚ) by norm_num]
  exact coverp0011100101010
private noncomputable def ep0011100101011_0 : Blocks := edgeBlocks% "full/vectors/0011100101011-E-0000.bin"
noncomputable def ep0011100101011 : Blocks := ep0011100101011_0
private theorem idp0011100101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110010101.list =
    C ((2:ℤ)^73) * horner X vp0011100101011.list + horner X ep0011100101011.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100101011 : Branch 1 (-1833761639/2000000 : ℚ) vp001110010101 := by
  apply branch_checked idp0011100101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1833761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1834761639/1000000 : ℚ) by norm_num]
  exact coverp0011100101011
theorem coverp001110010101 : Covers (-1833761639/2000000 : ℚ) vp001110010101 := join_branches bp0011100101010 bp0011100101011
private noncomputable def vp0011100101001_0 : Blocks := edgeBlocks% "full/vectors/0011100101001-V-0000.bin"
noncomputable def vp0011100101001 : Blocks := vp0011100101001_0
theorem coverp0011100101001 : Covers (-1832761639/1000000 : ℚ) vp0011100101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100101000_0 : Blocks := edgeBlocks% "full/vectors/0011100101000-V-0000.bin"
noncomputable def vp0011100101000 : Blocks := vp0011100101000_0
theorem coverp0011100101000 : Covers (-1831761639/1000000 : ℚ) vp0011100101000 := cover_leaf (by decide +kernel)
private noncomputable def vp001110010100_0 : Blocks := edgeBlocks% "full/vectors/001110010100-V-0000.bin"
noncomputable def vp001110010100 : Blocks := vp001110010100_0
private theorem bp0011100101000 : Branch 0 (-1831761639/2000000 : ℚ) vp001110010100 := by
  apply branch_left_normalized (c:=vp0011100101000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1831761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1831761639/1000000 : ℚ) by norm_num]
  exact coverp0011100101000
private noncomputable def ep0011100101001_0 : Blocks := edgeBlocks% "full/vectors/0011100101001-E-0000.bin"
noncomputable def ep0011100101001 : Blocks := ep0011100101001_0
private theorem idp0011100101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110010100.list =
    C ((2:ℤ)^72) * horner X vp0011100101001.list + horner X ep0011100101001.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100101001 : Branch 1 (-1831761639/2000000 : ℚ) vp001110010100 := by
  apply branch_checked idp0011100101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1831761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1832761639/1000000 : ℚ) by norm_num]
  exact coverp0011100101001
theorem coverp001110010100 : Covers (-1831761639/2000000 : ℚ) vp001110010100 := join_branches bp0011100101000 bp0011100101001
private noncomputable def vp00111001010_0 : Blocks := edgeBlocks% "full/vectors/00111001010-V-0000.bin"
noncomputable def vp00111001010 : Blocks := vp00111001010_0
private theorem bp001110010100 : Branch 0 (-1831761639/4000000 : ℚ) vp00111001010 := by
  apply branch_left_normalized (c:=vp001110010100) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1831761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1831761639/2000000 : ℚ) by norm_num]
  exact coverp001110010100
private noncomputable def ep001110010101_0 : Blocks := edgeBlocks% "full/vectors/001110010101-E-0000.bin"
noncomputable def ep001110010101 : Blocks := ep001110010101_0
private theorem idp001110010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111001010.list =
    C ((2:ℤ)^126) * horner X vp001110010101.list + horner X ep001110010101.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110010101 : Branch 1 (-1831761639/4000000 : ℚ) vp00111001010 := by
  apply branch_checked idp001110010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1831761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1833761639/2000000 : ℚ) by norm_num]
  exact coverp001110010101
theorem coverp00111001010 : Covers (-1831761639/4000000 : ℚ) vp00111001010 := join_branches bp001110010100 bp001110010101
private noncomputable def vp0011100101_0 : Blocks := edgeBlocks% "full/vectors/0011100101-V-0000.bin"
private noncomputable def vp0011100101_1 : Blocks := edgeBlocks% "full/vectors/0011100101-V-0001.bin"
noncomputable def vp0011100101 : Blocks := (Blocks.join vp0011100101_0 vp0011100101_1)
private theorem bp00111001010 : Branch 0 (-1831761639/8000000 : ℚ) vp0011100101 := by
  apply branch_left_normalized (c:=vp00111001010) (k:=0) (m:=113) (by decide +kernel)
  rw [show 2*(-1831761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1831761639/4000000 : ℚ) by norm_num]
  exact coverp00111001010
private noncomputable def ep00111001011_0 : Blocks := edgeBlocks% "full/vectors/00111001011-E-0000.bin"
private noncomputable def ep00111001011_1 : Blocks := edgeBlocks% "full/vectors/00111001011-E-0001.bin"
noncomputable def ep00111001011 : Blocks := (Blocks.join ep00111001011_0 ep00111001011_1)
private theorem idp00111001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011100101.list =
    C ((2:ℤ)^229) * horner X vp00111001011.list + horner X ep00111001011.list := by
  exact edge_identity (B := (2:ℤ)^405) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111001011 : Branch 1 (-1831761639/8000000 : ℚ) vp0011100101 := by
  apply branch_checked idp00111001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1831761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1835761639/4000000 : ℚ) by norm_num]
  exact coverp00111001011
theorem coverp0011100101 : Covers (-1831761639/8000000 : ℚ) vp0011100101 := join_branches bp00111001010 bp00111001011
private noncomputable def vp0011100100111_0 : Blocks := edgeBlocks% "full/vectors/0011100100111-V-0000.bin"
noncomputable def vp0011100100111 : Blocks := vp0011100100111_0
theorem coverp0011100100111 : Covers (-1830761639/1000000 : ℚ) vp0011100100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100100110_0 : Blocks := edgeBlocks% "full/vectors/0011100100110-V-0000.bin"
noncomputable def vp0011100100110 : Blocks := vp0011100100110_0
theorem coverp0011100100110 : Covers (-1829761639/1000000 : ℚ) vp0011100100110 := cover_leaf (by decide +kernel)
private noncomputable def vp001110010011_0 : Blocks := edgeBlocks% "full/vectors/001110010011-V-0000.bin"
noncomputable def vp001110010011 : Blocks := vp001110010011_0
private theorem bp0011100100110 : Branch 0 (-1829761639/2000000 : ℚ) vp001110010011 := by
  apply branch_left_normalized (c:=vp0011100100110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1829761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1829761639/1000000 : ℚ) by norm_num]
  exact coverp0011100100110
private noncomputable def ep0011100100111_0 : Blocks := edgeBlocks% "full/vectors/0011100100111-E-0000.bin"
noncomputable def ep0011100100111 : Blocks := ep0011100100111_0
private theorem idp0011100100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110010011.list =
    C ((2:ℤ)^73) * horner X vp0011100100111.list + horner X ep0011100100111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100100111 : Branch 1 (-1829761639/2000000 : ℚ) vp001110010011 := by
  apply branch_checked idp0011100100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1829761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1830761639/1000000 : ℚ) by norm_num]
  exact coverp0011100100111
theorem coverp001110010011 : Covers (-1829761639/2000000 : ℚ) vp001110010011 := join_branches bp0011100100110 bp0011100100111
private noncomputable def vp0011100100101_0 : Blocks := edgeBlocks% "full/vectors/0011100100101-V-0000.bin"
noncomputable def vp0011100100101 : Blocks := vp0011100100101_0
theorem coverp0011100100101 : Covers (-1828761639/1000000 : ℚ) vp0011100100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100100100_0 : Blocks := edgeBlocks% "full/vectors/0011100100100-V-0000.bin"
noncomputable def vp0011100100100 : Blocks := vp0011100100100_0
theorem coverp0011100100100 : Covers (-1827761639/1000000 : ℚ) vp0011100100100 := cover_leaf (by decide +kernel)
private noncomputable def vp001110010010_0 : Blocks := edgeBlocks% "full/vectors/001110010010-V-0000.bin"
noncomputable def vp001110010010 : Blocks := vp001110010010_0
private theorem bp0011100100100 : Branch 0 (-1827761639/2000000 : ℚ) vp001110010010 := by
  apply branch_left_normalized (c:=vp0011100100100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1827761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1827761639/1000000 : ℚ) by norm_num]
  exact coverp0011100100100
private noncomputable def ep0011100100101_0 : Blocks := edgeBlocks% "full/vectors/0011100100101-E-0000.bin"
noncomputable def ep0011100100101 : Blocks := ep0011100100101_0
private theorem idp0011100100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110010010.list =
    C ((2:ℤ)^73) * horner X vp0011100100101.list + horner X ep0011100100101.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100100101 : Branch 1 (-1827761639/2000000 : ℚ) vp001110010010 := by
  apply branch_checked idp0011100100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1827761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1828761639/1000000 : ℚ) by norm_num]
  exact coverp0011100100101
theorem coverp001110010010 : Covers (-1827761639/2000000 : ℚ) vp001110010010 := join_branches bp0011100100100 bp0011100100101
private noncomputable def vp00111001001_0 : Blocks := edgeBlocks% "full/vectors/00111001001-V-0000.bin"
noncomputable def vp00111001001 : Blocks := vp00111001001_0
private theorem bp001110010010 : Branch 0 (-1827761639/4000000 : ℚ) vp00111001001 := by
  apply branch_left_normalized (c:=vp001110010010) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1827761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1827761639/2000000 : ℚ) by norm_num]
  exact coverp001110010010
private noncomputable def ep001110010011_0 : Blocks := edgeBlocks% "full/vectors/001110010011-E-0000.bin"
noncomputable def ep001110010011 : Blocks := ep001110010011_0
private theorem idp001110010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111001001.list =
    C ((2:ℤ)^125) * horner X vp001110010011.list + horner X ep001110010011.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110010011 : Branch 1 (-1827761639/4000000 : ℚ) vp00111001001 := by
  apply branch_checked idp001110010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1827761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1829761639/2000000 : ℚ) by norm_num]
  exact coverp001110010011
theorem coverp00111001001 : Covers (-1827761639/4000000 : ℚ) vp00111001001 := join_branches bp001110010010 bp001110010011
private noncomputable def vp0011100100011_0 : Blocks := edgeBlocks% "full/vectors/0011100100011-V-0000.bin"
noncomputable def vp0011100100011 : Blocks := vp0011100100011_0
theorem coverp0011100100011 : Covers (-1826761639/1000000 : ℚ) vp0011100100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100100010_0 : Blocks := edgeBlocks% "full/vectors/0011100100010-V-0000.bin"
noncomputable def vp0011100100010 : Blocks := vp0011100100010_0
theorem coverp0011100100010 : Covers (-1825761639/1000000 : ℚ) vp0011100100010 := cover_leaf (by decide +kernel)
private noncomputable def vp001110010001_0 : Blocks := edgeBlocks% "full/vectors/001110010001-V-0000.bin"
noncomputable def vp001110010001 : Blocks := vp001110010001_0
private theorem bp0011100100010 : Branch 0 (-1825761639/2000000 : ℚ) vp001110010001 := by
  apply branch_left_normalized (c:=vp0011100100010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1825761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1825761639/1000000 : ℚ) by norm_num]
  exact coverp0011100100010
private noncomputable def ep0011100100011_0 : Blocks := edgeBlocks% "full/vectors/0011100100011-E-0000.bin"
noncomputable def ep0011100100011 : Blocks := ep0011100100011_0
private theorem idp0011100100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110010001.list =
    C ((2:ℤ)^72) * horner X vp0011100100011.list + horner X ep0011100100011.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100100011 : Branch 1 (-1825761639/2000000 : ℚ) vp001110010001 := by
  apply branch_checked idp0011100100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1825761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1826761639/1000000 : ℚ) by norm_num]
  exact coverp0011100100011
theorem coverp001110010001 : Covers (-1825761639/2000000 : ℚ) vp001110010001 := join_branches bp0011100100010 bp0011100100011
private noncomputable def vp0011100100001_0 : Blocks := edgeBlocks% "full/vectors/0011100100001-V-0000.bin"
noncomputable def vp0011100100001 : Blocks := vp0011100100001_0
theorem coverp0011100100001 : Covers (-1824761639/1000000 : ℚ) vp0011100100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100100000_0 : Blocks := edgeBlocks% "full/vectors/0011100100000-V-0000.bin"
noncomputable def vp0011100100000 : Blocks := vp0011100100000_0
theorem coverp0011100100000 : Covers (-1823761639/1000000 : ℚ) vp0011100100000 := cover_leaf (by decide +kernel)
private noncomputable def vp001110010000_0 : Blocks := edgeBlocks% "full/vectors/001110010000-V-0000.bin"
noncomputable def vp001110010000 : Blocks := vp001110010000_0
private theorem bp0011100100000 : Branch 0 (-1823761639/2000000 : ℚ) vp001110010000 := by
  apply branch_left_normalized (c:=vp0011100100000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1823761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1823761639/1000000 : ℚ) by norm_num]
  exact coverp0011100100000
private noncomputable def ep0011100100001_0 : Blocks := edgeBlocks% "full/vectors/0011100100001-E-0000.bin"
noncomputable def ep0011100100001 : Blocks := ep0011100100001_0
private theorem idp0011100100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110010000.list =
    C ((2:ℤ)^72) * horner X vp0011100100001.list + horner X ep0011100100001.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100100001 : Branch 1 (-1823761639/2000000 : ℚ) vp001110010000 := by
  apply branch_checked idp0011100100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1823761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1824761639/1000000 : ℚ) by norm_num]
  exact coverp0011100100001
theorem coverp001110010000 : Covers (-1823761639/2000000 : ℚ) vp001110010000 := join_branches bp0011100100000 bp0011100100001
private noncomputable def vp00111001000_0 : Blocks := edgeBlocks% "full/vectors/00111001000-V-0000.bin"
noncomputable def vp00111001000 : Blocks := vp00111001000_0
private theorem bp001110010000 : Branch 0 (-1823761639/4000000 : ℚ) vp00111001000 := by
  apply branch_left_normalized (c:=vp001110010000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1823761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1823761639/2000000 : ℚ) by norm_num]
  exact coverp001110010000
private noncomputable def ep001110010001_0 : Blocks := edgeBlocks% "full/vectors/001110010001-E-0000.bin"
noncomputable def ep001110010001 : Blocks := ep001110010001_0
private theorem idp001110010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111001000.list =
    C ((2:ℤ)^126) * horner X vp001110010001.list + horner X ep001110010001.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110010001 : Branch 1 (-1823761639/4000000 : ℚ) vp00111001000 := by
  apply branch_checked idp001110010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1823761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1825761639/2000000 : ℚ) by norm_num]
  exact coverp001110010001
theorem coverp00111001000 : Covers (-1823761639/4000000 : ℚ) vp00111001000 := join_branches bp001110010000 bp001110010001
private noncomputable def vp0011100100_0 : Blocks := edgeBlocks% "full/vectors/0011100100-V-0000.bin"
private noncomputable def vp0011100100_1 : Blocks := edgeBlocks% "full/vectors/0011100100-V-0001.bin"
noncomputable def vp0011100100 : Blocks := (Blocks.join vp0011100100_0 vp0011100100_1)
private theorem bp00111001000 : Branch 0 (-1823761639/8000000 : ℚ) vp0011100100 := by
  apply branch_left_normalized (c:=vp00111001000) (k:=0) (m:=113) (by decide +kernel)
  rw [show 2*(-1823761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1823761639/4000000 : ℚ) by norm_num]
  exact coverp00111001000
private noncomputable def ep00111001001_0 : Blocks := edgeBlocks% "full/vectors/00111001001-E-0000.bin"
private noncomputable def ep00111001001_1 : Blocks := edgeBlocks% "full/vectors/00111001001-E-0001.bin"
noncomputable def ep00111001001 : Blocks := (Blocks.join ep00111001001_0 ep00111001001_1)
private theorem idp00111001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011100100.list =
    C ((2:ℤ)^230) * horner X vp00111001001.list + horner X ep00111001001.list := by
  exact edge_identity (B := (2:ℤ)^406) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111001001 : Branch 1 (-1823761639/8000000 : ℚ) vp0011100100 := by
  apply branch_checked idp00111001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1823761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1827761639/4000000 : ℚ) by norm_num]
  exact coverp00111001001
theorem coverp0011100100 : Covers (-1823761639/8000000 : ℚ) vp0011100100 := join_branches bp00111001000 bp00111001001
private noncomputable def vp001110010_0 : Blocks := edgeBlocks% "full/vectors/001110010-V-0000.bin"
private noncomputable def vp001110010_1 : Blocks := edgeBlocks% "full/vectors/001110010-V-0001.bin"
private noncomputable def vp001110010_2 : Blocks := edgeBlocks% "full/vectors/001110010-V-0002.bin"
private noncomputable def vp001110010_3 : Blocks := edgeBlocks% "full/vectors/001110010-V-0003.bin"
noncomputable def vp001110010 : Blocks := (Blocks.join (Blocks.join vp001110010_0 vp001110010_1) (Blocks.join vp001110010_2 vp001110010_3))
private theorem bp0011100100 : Branch 0 (-1823761639/16000000 : ℚ) vp001110010 := by
  apply branch_left_normalized (c:=vp0011100100) (k:=0) (m:=206) (by decide +kernel)
  rw [show 2*(-1823761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1823761639/8000000 : ℚ) by norm_num]
  exact coverp0011100100
private noncomputable def ep0011100101_0 : Blocks := edgeBlocks% "full/vectors/0011100101-E-0000.bin"
private noncomputable def ep0011100101_1 : Blocks := edgeBlocks% "full/vectors/0011100101-E-0001.bin"
private noncomputable def ep0011100101_2 : Blocks := edgeBlocks% "full/vectors/0011100101-E-0002.bin"
private noncomputable def ep0011100101_3 : Blocks := edgeBlocks% "full/vectors/0011100101-E-0003.bin"
noncomputable def ep0011100101 : Blocks := (Blocks.join (Blocks.join ep0011100101_0 ep0011100101_1) (Blocks.join ep0011100101_2 ep0011100101_3))
private theorem idp0011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110010.list =
    C ((2:ℤ)^436) * horner X vp0011100101.list + horner X ep0011100101.list := by
  exact edge_identity (B := (2:ℤ)^686) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100101 : Branch 1 (-1823761639/16000000 : ℚ) vp001110010 := by
  apply branch_checked idp0011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1823761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1831761639/8000000 : ℚ) by norm_num]
  exact coverp0011100101
theorem coverp001110010 : Covers (-1823761639/16000000 : ℚ) vp001110010 := join_branches bp0011100100 bp0011100101
private noncomputable def vp00111001_0 : Blocks := edgeBlocks% "full/vectors/00111001-V-0000.bin"
private noncomputable def vp00111001_1 : Blocks := edgeBlocks% "full/vectors/00111001-V-0001.bin"
private noncomputable def vp00111001_2 : Blocks := edgeBlocks% "full/vectors/00111001-V-0002.bin"
private noncomputable def vp00111001_3 : Blocks := edgeBlocks% "full/vectors/00111001-V-0003.bin"
private noncomputable def vp00111001_4 : Blocks := edgeBlocks% "full/vectors/00111001-V-0004.bin"
private noncomputable def vp00111001_5 : Blocks := edgeBlocks% "full/vectors/00111001-V-0005.bin"
noncomputable def vp00111001 : Blocks := (Blocks.join (Blocks.join vp00111001_0 (Blocks.join vp00111001_1 vp00111001_2)) (Blocks.join vp00111001_3 (Blocks.join vp00111001_4 vp00111001_5)))
private theorem bp001110010 : Branch 0 (-1823761639/32000000 : ℚ) vp00111001 := by
  apply branch_left_normalized (c:=vp001110010) (k:=0) (m:=389) (by decide +kernel)
  rw [show 2*(-1823761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1823761639/16000000 : ℚ) by norm_num]
  exact coverp001110010
private noncomputable def ep001110011_0 : Blocks := edgeBlocks% "full/vectors/001110011-E-0000.bin"
private noncomputable def ep001110011_1 : Blocks := edgeBlocks% "full/vectors/001110011-E-0001.bin"
private noncomputable def ep001110011_2 : Blocks := edgeBlocks% "full/vectors/001110011-E-0002.bin"
private noncomputable def ep001110011_3 : Blocks := edgeBlocks% "full/vectors/001110011-E-0003.bin"
private noncomputable def ep001110011_4 : Blocks := edgeBlocks% "full/vectors/001110011-E-0004.bin"
private noncomputable def ep001110011_5 : Blocks := edgeBlocks% "full/vectors/001110011-E-0005.bin"
noncomputable def ep001110011 : Blocks := (Blocks.join (Blocks.join ep001110011_0 (Blocks.join ep001110011_1 ep001110011_2)) (Blocks.join ep001110011_3 (Blocks.join ep001110011_4 ep001110011_5)))
private theorem idp001110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111001.list =
    C ((2:ℤ)^845) * horner X vp001110011.list + horner X ep001110011.list := by
  exact edge_identity (B := (2:ℤ)^1244) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110011 : Branch 1 (-1823761639/32000000 : ℚ) vp00111001 := by
  apply branch_checked idp001110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1823761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1839761639/16000000 : ℚ) by norm_num]
  exact coverp001110011
theorem coverp00111001 : Covers (-1823761639/32000000 : ℚ) vp00111001 := join_branches bp001110010 bp001110011
private noncomputable def vp0011100011111_0 : Blocks := edgeBlocks% "full/vectors/0011100011111-V-0000.bin"
noncomputable def vp0011100011111 : Blocks := vp0011100011111_0
theorem coverp0011100011111 : Covers (-1822761639/1000000 : ℚ) vp0011100011111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100011110_0 : Blocks := edgeBlocks% "full/vectors/0011100011110-V-0000.bin"
noncomputable def vp0011100011110 : Blocks := vp0011100011110_0
theorem coverp0011100011110 : Covers (-1821761639/1000000 : ℚ) vp0011100011110 := cover_leaf (by decide +kernel)
private noncomputable def vp001110001111_0 : Blocks := edgeBlocks% "full/vectors/001110001111-V-0000.bin"
noncomputable def vp001110001111 : Blocks := vp001110001111_0
private theorem bp0011100011110 : Branch 0 (-1821761639/2000000 : ℚ) vp001110001111 := by
  apply branch_left_normalized (c:=vp0011100011110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1821761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1821761639/1000000 : ℚ) by norm_num]
  exact coverp0011100011110
private noncomputable def ep0011100011111_0 : Blocks := edgeBlocks% "full/vectors/0011100011111-E-0000.bin"
noncomputable def ep0011100011111 : Blocks := ep0011100011111_0
private theorem idp0011100011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110001111.list =
    C ((2:ℤ)^73) * horner X vp0011100011111.list + horner X ep0011100011111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100011111 : Branch 1 (-1821761639/2000000 : ℚ) vp001110001111 := by
  apply branch_checked idp0011100011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1821761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1822761639/1000000 : ℚ) by norm_num]
  exact coverp0011100011111
theorem coverp001110001111 : Covers (-1821761639/2000000 : ℚ) vp001110001111 := join_branches bp0011100011110 bp0011100011111
private noncomputable def vp0011100011101_0 : Blocks := edgeBlocks% "full/vectors/0011100011101-V-0000.bin"
noncomputable def vp0011100011101 : Blocks := vp0011100011101_0
theorem coverp0011100011101 : Covers (-1820761639/1000000 : ℚ) vp0011100011101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100011100_0 : Blocks := edgeBlocks% "full/vectors/0011100011100-V-0000.bin"
noncomputable def vp0011100011100 : Blocks := vp0011100011100_0
theorem coverp0011100011100 : Covers (-1819761639/1000000 : ℚ) vp0011100011100 := cover_leaf (by decide +kernel)
private noncomputable def vp001110001110_0 : Blocks := edgeBlocks% "full/vectors/001110001110-V-0000.bin"
noncomputable def vp001110001110 : Blocks := vp001110001110_0
private theorem bp0011100011100 : Branch 0 (-1819761639/2000000 : ℚ) vp001110001110 := by
  apply branch_left_normalized (c:=vp0011100011100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1819761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1819761639/1000000 : ℚ) by norm_num]
  exact coverp0011100011100
private noncomputable def ep0011100011101_0 : Blocks := edgeBlocks% "full/vectors/0011100011101-E-0000.bin"
noncomputable def ep0011100011101 : Blocks := ep0011100011101_0
private theorem idp0011100011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110001110.list =
    C ((2:ℤ)^73) * horner X vp0011100011101.list + horner X ep0011100011101.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100011101 : Branch 1 (-1819761639/2000000 : ℚ) vp001110001110 := by
  apply branch_checked idp0011100011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1819761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1820761639/1000000 : ℚ) by norm_num]
  exact coverp0011100011101
theorem coverp001110001110 : Covers (-1819761639/2000000 : ℚ) vp001110001110 := join_branches bp0011100011100 bp0011100011101
private noncomputable def vp00111000111_0 : Blocks := edgeBlocks% "full/vectors/00111000111-V-0000.bin"
noncomputable def vp00111000111 : Blocks := vp00111000111_0
private theorem bp001110001110 : Branch 0 (-1819761639/4000000 : ℚ) vp00111000111 := by
  apply branch_left_normalized (c:=vp001110001110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1819761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1819761639/2000000 : ℚ) by norm_num]
  exact coverp001110001110
private noncomputable def ep001110001111_0 : Blocks := edgeBlocks% "full/vectors/001110001111-E-0000.bin"
noncomputable def ep001110001111 : Blocks := ep001110001111_0
private theorem idp001110001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111000111.list =
    C ((2:ℤ)^125) * horner X vp001110001111.list + horner X ep001110001111.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110001111 : Branch 1 (-1819761639/4000000 : ℚ) vp00111000111 := by
  apply branch_checked idp001110001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1819761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1821761639/2000000 : ℚ) by norm_num]
  exact coverp001110001111
theorem coverp00111000111 : Covers (-1819761639/4000000 : ℚ) vp00111000111 := join_branches bp001110001110 bp001110001111
private noncomputable def vp0011100011011_0 : Blocks := edgeBlocks% "full/vectors/0011100011011-V-0000.bin"
noncomputable def vp0011100011011 : Blocks := vp0011100011011_0
theorem coverp0011100011011 : Covers (-1818761639/1000000 : ℚ) vp0011100011011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100011010_0 : Blocks := edgeBlocks% "full/vectors/0011100011010-V-0000.bin"
noncomputable def vp0011100011010 : Blocks := vp0011100011010_0
theorem coverp0011100011010 : Covers (-1817761639/1000000 : ℚ) vp0011100011010 := cover_leaf (by decide +kernel)
private noncomputable def vp001110001101_0 : Blocks := edgeBlocks% "full/vectors/001110001101-V-0000.bin"
noncomputable def vp001110001101 : Blocks := vp001110001101_0
private theorem bp0011100011010 : Branch 0 (-1817761639/2000000 : ℚ) vp001110001101 := by
  apply branch_left_normalized (c:=vp0011100011010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1817761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1817761639/1000000 : ℚ) by norm_num]
  exact coverp0011100011010
private noncomputable def ep0011100011011_0 : Blocks := edgeBlocks% "full/vectors/0011100011011-E-0000.bin"
noncomputable def ep0011100011011 : Blocks := ep0011100011011_0
private theorem idp0011100011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110001101.list =
    C ((2:ℤ)^73) * horner X vp0011100011011.list + horner X ep0011100011011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100011011 : Branch 1 (-1817761639/2000000 : ℚ) vp001110001101 := by
  apply branch_checked idp0011100011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1817761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1818761639/1000000 : ℚ) by norm_num]
  exact coverp0011100011011
theorem coverp001110001101 : Covers (-1817761639/2000000 : ℚ) vp001110001101 := join_branches bp0011100011010 bp0011100011011
private noncomputable def vp0011100011001_0 : Blocks := edgeBlocks% "full/vectors/0011100011001-V-0000.bin"
noncomputable def vp0011100011001 : Blocks := vp0011100011001_0
theorem coverp0011100011001 : Covers (-1816761639/1000000 : ℚ) vp0011100011001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100011000_0 : Blocks := edgeBlocks% "full/vectors/0011100011000-V-0000.bin"
noncomputable def vp0011100011000 : Blocks := vp0011100011000_0
theorem coverp0011100011000 : Covers (-1815761639/1000000 : ℚ) vp0011100011000 := cover_leaf (by decide +kernel)
private noncomputable def vp001110001100_0 : Blocks := edgeBlocks% "full/vectors/001110001100-V-0000.bin"
noncomputable def vp001110001100 : Blocks := vp001110001100_0
private theorem bp0011100011000 : Branch 0 (-1815761639/2000000 : ℚ) vp001110001100 := by
  apply branch_left_normalized (c:=vp0011100011000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1815761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1815761639/1000000 : ℚ) by norm_num]
  exact coverp0011100011000
private noncomputable def ep0011100011001_0 : Blocks := edgeBlocks% "full/vectors/0011100011001-E-0000.bin"
noncomputable def ep0011100011001 : Blocks := ep0011100011001_0
private theorem idp0011100011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110001100.list =
    C ((2:ℤ)^72) * horner X vp0011100011001.list + horner X ep0011100011001.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100011001 : Branch 1 (-1815761639/2000000 : ℚ) vp001110001100 := by
  apply branch_checked idp0011100011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1815761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1816761639/1000000 : ℚ) by norm_num]
  exact coverp0011100011001
theorem coverp001110001100 : Covers (-1815761639/2000000 : ℚ) vp001110001100 := join_branches bp0011100011000 bp0011100011001
private noncomputable def vp00111000110_0 : Blocks := edgeBlocks% "full/vectors/00111000110-V-0000.bin"
noncomputable def vp00111000110 : Blocks := vp00111000110_0
private theorem bp001110001100 : Branch 0 (-1815761639/4000000 : ℚ) vp00111000110 := by
  apply branch_left_normalized (c:=vp001110001100) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1815761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1815761639/2000000 : ℚ) by norm_num]
  exact coverp001110001100
private noncomputable def ep001110001101_0 : Blocks := edgeBlocks% "full/vectors/001110001101-E-0000.bin"
noncomputable def ep001110001101 : Blocks := ep001110001101_0
private theorem idp001110001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111000110.list =
    C ((2:ℤ)^126) * horner X vp001110001101.list + horner X ep001110001101.list := by
  exact edge_identity (B := (2:ℤ)^265) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110001101 : Branch 1 (-1815761639/4000000 : ℚ) vp00111000110 := by
  apply branch_checked idp001110001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1815761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1817761639/2000000 : ℚ) by norm_num]
  exact coverp001110001101
theorem coverp00111000110 : Covers (-1815761639/4000000 : ℚ) vp00111000110 := join_branches bp001110001100 bp001110001101
private noncomputable def vp0011100011_0 : Blocks := edgeBlocks% "full/vectors/0011100011-V-0000.bin"
private noncomputable def vp0011100011_1 : Blocks := edgeBlocks% "full/vectors/0011100011-V-0001.bin"
noncomputable def vp0011100011 : Blocks := (Blocks.join vp0011100011_0 vp0011100011_1)
private theorem bp00111000110 : Branch 0 (-1815761639/8000000 : ℚ) vp0011100011 := by
  apply branch_left_normalized (c:=vp00111000110) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-1815761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1815761639/4000000 : ℚ) by norm_num]
  exact coverp00111000110
private noncomputable def ep00111000111_0 : Blocks := edgeBlocks% "full/vectors/00111000111-E-0000.bin"
private noncomputable def ep00111000111_1 : Blocks := edgeBlocks% "full/vectors/00111000111-E-0001.bin"
noncomputable def ep00111000111 : Blocks := (Blocks.join ep00111000111_0 ep00111000111_1)
private theorem idp00111000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011100011.list =
    C ((2:ℤ)^231) * horner X vp00111000111.list + horner X ep00111000111.list := by
  exact edge_identity (B := (2:ℤ)^407) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111000111 : Branch 1 (-1815761639/8000000 : ℚ) vp0011100011 := by
  apply branch_checked idp00111000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1815761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1819761639/4000000 : ℚ) by norm_num]
  exact coverp00111000111
theorem coverp0011100011 : Covers (-1815761639/8000000 : ℚ) vp0011100011 := join_branches bp00111000110 bp00111000111
private noncomputable def vp0011100010111_0 : Blocks := edgeBlocks% "full/vectors/0011100010111-V-0000.bin"
noncomputable def vp0011100010111 : Blocks := vp0011100010111_0
theorem coverp0011100010111 : Covers (-1814761639/1000000 : ℚ) vp0011100010111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100010110_0 : Blocks := edgeBlocks% "full/vectors/0011100010110-V-0000.bin"
noncomputable def vp0011100010110 : Blocks := vp0011100010110_0
theorem coverp0011100010110 : Covers (-1813761639/1000000 : ℚ) vp0011100010110 := cover_leaf (by decide +kernel)
private noncomputable def vp001110001011_0 : Blocks := edgeBlocks% "full/vectors/001110001011-V-0000.bin"
noncomputable def vp001110001011 : Blocks := vp001110001011_0
private theorem bp0011100010110 : Branch 0 (-1813761639/2000000 : ℚ) vp001110001011 := by
  apply branch_left_normalized (c:=vp0011100010110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1813761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1813761639/1000000 : ℚ) by norm_num]
  exact coverp0011100010110
private noncomputable def ep0011100010111_0 : Blocks := edgeBlocks% "full/vectors/0011100010111-E-0000.bin"
noncomputable def ep0011100010111 : Blocks := ep0011100010111_0
private theorem idp0011100010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110001011.list =
    C ((2:ℤ)^73) * horner X vp0011100010111.list + horner X ep0011100010111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100010111 : Branch 1 (-1813761639/2000000 : ℚ) vp001110001011 := by
  apply branch_checked idp0011100010111 (by positivity) (by decide +kernel)
  rw [show 2*(-1813761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1814761639/1000000 : ℚ) by norm_num]
  exact coverp0011100010111
theorem coverp001110001011 : Covers (-1813761639/2000000 : ℚ) vp001110001011 := join_branches bp0011100010110 bp0011100010111
private noncomputable def vp0011100010101_0 : Blocks := edgeBlocks% "full/vectors/0011100010101-V-0000.bin"
noncomputable def vp0011100010101 : Blocks := vp0011100010101_0
theorem coverp0011100010101 : Covers (-1812761639/1000000 : ℚ) vp0011100010101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100010100_0 : Blocks := edgeBlocks% "full/vectors/0011100010100-V-0000.bin"
noncomputable def vp0011100010100 : Blocks := vp0011100010100_0
theorem coverp0011100010100 : Covers (-1811761639/1000000 : ℚ) vp0011100010100 := cover_leaf (by decide +kernel)
private noncomputable def vp001110001010_0 : Blocks := edgeBlocks% "full/vectors/001110001010-V-0000.bin"
noncomputable def vp001110001010 : Blocks := vp001110001010_0
private theorem bp0011100010100 : Branch 0 (-1811761639/2000000 : ℚ) vp001110001010 := by
  apply branch_left_normalized (c:=vp0011100010100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1811761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1811761639/1000000 : ℚ) by norm_num]
  exact coverp0011100010100
private noncomputable def ep0011100010101_0 : Blocks := edgeBlocks% "full/vectors/0011100010101-E-0000.bin"
noncomputable def ep0011100010101 : Blocks := ep0011100010101_0
private theorem idp0011100010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110001010.list =
    C ((2:ℤ)^72) * horner X vp0011100010101.list + horner X ep0011100010101.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100010101 : Branch 1 (-1811761639/2000000 : ℚ) vp001110001010 := by
  apply branch_checked idp0011100010101 (by positivity) (by decide +kernel)
  rw [show 2*(-1811761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1812761639/1000000 : ℚ) by norm_num]
  exact coverp0011100010101
theorem coverp001110001010 : Covers (-1811761639/2000000 : ℚ) vp001110001010 := join_branches bp0011100010100 bp0011100010101
private noncomputable def vp00111000101_0 : Blocks := edgeBlocks% "full/vectors/00111000101-V-0000.bin"
noncomputable def vp00111000101 : Blocks := vp00111000101_0
private theorem bp001110001010 : Branch 0 (-1811761639/4000000 : ℚ) vp00111000101 := by
  apply branch_left_normalized (c:=vp001110001010) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1811761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1811761639/2000000 : ℚ) by norm_num]
  exact coverp001110001010
private noncomputable def ep001110001011_0 : Blocks := edgeBlocks% "full/vectors/001110001011-E-0000.bin"
noncomputable def ep001110001011 : Blocks := ep001110001011_0
private theorem idp001110001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111000101.list =
    C ((2:ℤ)^125) * horner X vp001110001011.list + horner X ep001110001011.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110001011 : Branch 1 (-1811761639/4000000 : ℚ) vp00111000101 := by
  apply branch_checked idp001110001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1811761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1813761639/2000000 : ℚ) by norm_num]
  exact coverp001110001011
theorem coverp00111000101 : Covers (-1811761639/4000000 : ℚ) vp00111000101 := join_branches bp001110001010 bp001110001011
private noncomputable def vp0011100010011_0 : Blocks := edgeBlocks% "full/vectors/0011100010011-V-0000.bin"
noncomputable def vp0011100010011 : Blocks := vp0011100010011_0
theorem coverp0011100010011 : Covers (-1810761639/1000000 : ℚ) vp0011100010011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100010010_0 : Blocks := edgeBlocks% "full/vectors/0011100010010-V-0000.bin"
noncomputable def vp0011100010010 : Blocks := vp0011100010010_0
theorem coverp0011100010010 : Covers (-1809761639/1000000 : ℚ) vp0011100010010 := cover_leaf (by decide +kernel)
private noncomputable def vp001110001001_0 : Blocks := edgeBlocks% "full/vectors/001110001001-V-0000.bin"
noncomputable def vp001110001001 : Blocks := vp001110001001_0
private theorem bp0011100010010 : Branch 0 (-1809761639/2000000 : ℚ) vp001110001001 := by
  apply branch_left_normalized (c:=vp0011100010010) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1809761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1809761639/1000000 : ℚ) by norm_num]
  exact coverp0011100010010
private noncomputable def ep0011100010011_0 : Blocks := edgeBlocks% "full/vectors/0011100010011-E-0000.bin"
noncomputable def ep0011100010011 : Blocks := ep0011100010011_0
private theorem idp0011100010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110001001.list =
    C ((2:ℤ)^73) * horner X vp0011100010011.list + horner X ep0011100010011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100010011 : Branch 1 (-1809761639/2000000 : ℚ) vp001110001001 := by
  apply branch_checked idp0011100010011 (by positivity) (by decide +kernel)
  rw [show 2*(-1809761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1810761639/1000000 : ℚ) by norm_num]
  exact coverp0011100010011
theorem coverp001110001001 : Covers (-1809761639/2000000 : ℚ) vp001110001001 := join_branches bp0011100010010 bp0011100010011
private noncomputable def vp0011100010001_0 : Blocks := edgeBlocks% "full/vectors/0011100010001-V-0000.bin"
noncomputable def vp0011100010001 : Blocks := vp0011100010001_0
theorem coverp0011100010001 : Covers (-1808761639/1000000 : ℚ) vp0011100010001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100010000_0 : Blocks := edgeBlocks% "full/vectors/0011100010000-V-0000.bin"
noncomputable def vp0011100010000 : Blocks := vp0011100010000_0
theorem coverp0011100010000 : Covers (-1807761639/1000000 : ℚ) vp0011100010000 := cover_leaf (by decide +kernel)
private noncomputable def vp001110001000_0 : Blocks := edgeBlocks% "full/vectors/001110001000-V-0000.bin"
noncomputable def vp001110001000 : Blocks := vp001110001000_0
private theorem bp0011100010000 : Branch 0 (-1807761639/2000000 : ℚ) vp001110001000 := by
  apply branch_left_normalized (c:=vp0011100010000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1807761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1807761639/1000000 : ℚ) by norm_num]
  exact coverp0011100010000
private noncomputable def ep0011100010001_0 : Blocks := edgeBlocks% "full/vectors/0011100010001-E-0000.bin"
noncomputable def ep0011100010001 : Blocks := ep0011100010001_0
private theorem idp0011100010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110001000.list =
    C ((2:ℤ)^73) * horner X vp0011100010001.list + horner X ep0011100010001.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100010001 : Branch 1 (-1807761639/2000000 : ℚ) vp001110001000 := by
  apply branch_checked idp0011100010001 (by positivity) (by decide +kernel)
  rw [show 2*(-1807761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1808761639/1000000 : ℚ) by norm_num]
  exact coverp0011100010001
theorem coverp001110001000 : Covers (-1807761639/2000000 : ℚ) vp001110001000 := join_branches bp0011100010000 bp0011100010001
private noncomputable def vp00111000100_0 : Blocks := edgeBlocks% "full/vectors/00111000100-V-0000.bin"
noncomputable def vp00111000100 : Blocks := vp00111000100_0
private theorem bp001110001000 : Branch 0 (-1807761639/4000000 : ℚ) vp00111000100 := by
  apply branch_left_normalized (c:=vp001110001000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1807761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1807761639/2000000 : ℚ) by norm_num]
  exact coverp001110001000
private noncomputable def ep001110001001_0 : Blocks := edgeBlocks% "full/vectors/001110001001-E-0000.bin"
noncomputable def ep001110001001 : Blocks := ep001110001001_0
private theorem idp001110001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111000100.list =
    C ((2:ℤ)^127) * horner X vp001110001001.list + horner X ep001110001001.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110001001 : Branch 1 (-1807761639/4000000 : ℚ) vp00111000100 := by
  apply branch_checked idp001110001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1807761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1809761639/2000000 : ℚ) by norm_num]
  exact coverp001110001001
theorem coverp00111000100 : Covers (-1807761639/4000000 : ℚ) vp00111000100 := join_branches bp001110001000 bp001110001001
private noncomputable def vp0011100010_0 : Blocks := edgeBlocks% "full/vectors/0011100010-V-0000.bin"
private noncomputable def vp0011100010_1 : Blocks := edgeBlocks% "full/vectors/0011100010-V-0001.bin"
noncomputable def vp0011100010 : Blocks := (Blocks.join vp0011100010_0 vp0011100010_1)
private theorem bp00111000100 : Branch 0 (-1807761639/8000000 : ℚ) vp0011100010 := by
  apply branch_left_normalized (c:=vp00111000100) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-1807761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1807761639/4000000 : ℚ) by norm_num]
  exact coverp00111000100
private noncomputable def ep00111000101_0 : Blocks := edgeBlocks% "full/vectors/00111000101-E-0000.bin"
private noncomputable def ep00111000101_1 : Blocks := edgeBlocks% "full/vectors/00111000101-E-0001.bin"
noncomputable def ep00111000101 : Blocks := (Blocks.join ep00111000101_0 ep00111000101_1)
private theorem idp00111000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011100010.list =
    C ((2:ℤ)^232) * horner X vp00111000101.list + horner X ep00111000101.list := by
  exact edge_identity (B := (2:ℤ)^408) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111000101 : Branch 1 (-1807761639/8000000 : ℚ) vp0011100010 := by
  apply branch_checked idp00111000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1807761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1811761639/4000000 : ℚ) by norm_num]
  exact coverp00111000101
theorem coverp0011100010 : Covers (-1807761639/8000000 : ℚ) vp0011100010 := join_branches bp00111000100 bp00111000101
private noncomputable def vp001110001_0 : Blocks := edgeBlocks% "full/vectors/001110001-V-0000.bin"
private noncomputable def vp001110001_1 : Blocks := edgeBlocks% "full/vectors/001110001-V-0001.bin"
private noncomputable def vp001110001_2 : Blocks := edgeBlocks% "full/vectors/001110001-V-0002.bin"
private noncomputable def vp001110001_3 : Blocks := edgeBlocks% "full/vectors/001110001-V-0003.bin"
noncomputable def vp001110001 : Blocks := (Blocks.join (Blocks.join vp001110001_0 vp001110001_1) (Blocks.join vp001110001_2 vp001110001_3))
private theorem bp0011100010 : Branch 0 (-1807761639/16000000 : ℚ) vp001110001 := by
  apply branch_left_normalized (c:=vp0011100010) (k:=0) (m:=207) (by decide +kernel)
  rw [show 2*(-1807761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1807761639/8000000 : ℚ) by norm_num]
  exact coverp0011100010
private noncomputable def ep0011100011_0 : Blocks := edgeBlocks% "full/vectors/0011100011-E-0000.bin"
private noncomputable def ep0011100011_1 : Blocks := edgeBlocks% "full/vectors/0011100011-E-0001.bin"
private noncomputable def ep0011100011_2 : Blocks := edgeBlocks% "full/vectors/0011100011-E-0002.bin"
private noncomputable def ep0011100011_3 : Blocks := edgeBlocks% "full/vectors/0011100011-E-0003.bin"
noncomputable def ep0011100011 : Blocks := (Blocks.join (Blocks.join ep0011100011_0 ep0011100011_1) (Blocks.join ep0011100011_2 ep0011100011_3))
private theorem idp0011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110001.list =
    C ((2:ℤ)^439) * horner X vp0011100011.list + horner X ep0011100011.list := by
  exact edge_identity (B := (2:ℤ)^690) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100011 : Branch 1 (-1807761639/16000000 : ℚ) vp001110001 := by
  apply branch_checked idp0011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1807761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1815761639/8000000 : ℚ) by norm_num]
  exact coverp0011100011
theorem coverp001110001 : Covers (-1807761639/16000000 : ℚ) vp001110001 := join_branches bp0011100010 bp0011100011
private noncomputable def vp0011100001111_0 : Blocks := edgeBlocks% "full/vectors/0011100001111-V-0000.bin"
noncomputable def vp0011100001111 : Blocks := vp0011100001111_0
theorem coverp0011100001111 : Covers (-1806761639/1000000 : ℚ) vp0011100001111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100001110_0 : Blocks := edgeBlocks% "full/vectors/0011100001110-V-0000.bin"
noncomputable def vp0011100001110 : Blocks := vp0011100001110_0
theorem coverp0011100001110 : Covers (-1805761639/1000000 : ℚ) vp0011100001110 := cover_leaf (by decide +kernel)
private noncomputable def vp001110000111_0 : Blocks := edgeBlocks% "full/vectors/001110000111-V-0000.bin"
noncomputable def vp001110000111 : Blocks := vp001110000111_0
private theorem bp0011100001110 : Branch 0 (-1805761639/2000000 : ℚ) vp001110000111 := by
  apply branch_left_normalized (c:=vp0011100001110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1805761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1805761639/1000000 : ℚ) by norm_num]
  exact coverp0011100001110
private noncomputable def ep0011100001111_0 : Blocks := edgeBlocks% "full/vectors/0011100001111-E-0000.bin"
noncomputable def ep0011100001111 : Blocks := ep0011100001111_0
private theorem idp0011100001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110000111.list =
    C ((2:ℤ)^74) * horner X vp0011100001111.list + horner X ep0011100001111.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100001111 : Branch 1 (-1805761639/2000000 : ℚ) vp001110000111 := by
  apply branch_checked idp0011100001111 (by positivity) (by decide +kernel)
  rw [show 2*(-1805761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1806761639/1000000 : ℚ) by norm_num]
  exact coverp0011100001111
theorem coverp001110000111 : Covers (-1805761639/2000000 : ℚ) vp001110000111 := join_branches bp0011100001110 bp0011100001111
private noncomputable def vp0011100001101_0 : Blocks := edgeBlocks% "full/vectors/0011100001101-V-0000.bin"
noncomputable def vp0011100001101 : Blocks := vp0011100001101_0
theorem coverp0011100001101 : Covers (-1804761639/1000000 : ℚ) vp0011100001101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100001100_0 : Blocks := edgeBlocks% "full/vectors/0011100001100-V-0000.bin"
noncomputable def vp0011100001100 : Blocks := vp0011100001100_0
theorem coverp0011100001100 : Covers (-1803761639/1000000 : ℚ) vp0011100001100 := cover_leaf (by decide +kernel)
private noncomputable def vp001110000110_0 : Blocks := edgeBlocks% "full/vectors/001110000110-V-0000.bin"
noncomputable def vp001110000110 : Blocks := vp001110000110_0
private theorem bp0011100001100 : Branch 0 (-1803761639/2000000 : ℚ) vp001110000110 := by
  apply branch_left_normalized (c:=vp0011100001100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1803761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1803761639/1000000 : ℚ) by norm_num]
  exact coverp0011100001100
private noncomputable def ep0011100001101_0 : Blocks := edgeBlocks% "full/vectors/0011100001101-E-0000.bin"
noncomputable def ep0011100001101 : Blocks := ep0011100001101_0
private theorem idp0011100001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110000110.list =
    C ((2:ℤ)^73) * horner X vp0011100001101.list + horner X ep0011100001101.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100001101 : Branch 1 (-1803761639/2000000 : ℚ) vp001110000110 := by
  apply branch_checked idp0011100001101 (by positivity) (by decide +kernel)
  rw [show 2*(-1803761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1804761639/1000000 : ℚ) by norm_num]
  exact coverp0011100001101
theorem coverp001110000110 : Covers (-1803761639/2000000 : ℚ) vp001110000110 := join_branches bp0011100001100 bp0011100001101
private noncomputable def vp00111000011_0 : Blocks := edgeBlocks% "full/vectors/00111000011-V-0000.bin"
noncomputable def vp00111000011 : Blocks := vp00111000011_0
private theorem bp001110000110 : Branch 0 (-1803761639/4000000 : ℚ) vp00111000011 := by
  apply branch_left_normalized (c:=vp001110000110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1803761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1803761639/2000000 : ℚ) by norm_num]
  exact coverp001110000110
private noncomputable def ep001110000111_0 : Blocks := edgeBlocks% "full/vectors/001110000111-E-0000.bin"
noncomputable def ep001110000111 : Blocks := ep001110000111_0
private theorem idp001110000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111000011.list =
    C ((2:ℤ)^127) * horner X vp001110000111.list + horner X ep001110000111.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110000111 : Branch 1 (-1803761639/4000000 : ℚ) vp00111000011 := by
  apply branch_checked idp001110000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1803761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1805761639/2000000 : ℚ) by norm_num]
  exact coverp001110000111
theorem coverp00111000011 : Covers (-1803761639/4000000 : ℚ) vp00111000011 := join_branches bp001110000110 bp001110000111
private noncomputable def vp0011100001011_0 : Blocks := edgeBlocks% "full/vectors/0011100001011-V-0000.bin"
noncomputable def vp0011100001011 : Blocks := vp0011100001011_0
theorem coverp0011100001011 : Covers (-1802761639/1000000 : ℚ) vp0011100001011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100001010_0 : Blocks := edgeBlocks% "full/vectors/0011100001010-V-0000.bin"
noncomputable def vp0011100001010 : Blocks := vp0011100001010_0
theorem coverp0011100001010 : Covers (-1801761639/1000000 : ℚ) vp0011100001010 := cover_leaf (by decide +kernel)
private noncomputable def vp001110000101_0 : Blocks := edgeBlocks% "full/vectors/001110000101-V-0000.bin"
noncomputable def vp001110000101 : Blocks := vp001110000101_0
private theorem bp0011100001010 : Branch 0 (-1801761639/2000000 : ℚ) vp001110000101 := by
  apply branch_left_normalized (c:=vp0011100001010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1801761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1801761639/1000000 : ℚ) by norm_num]
  exact coverp0011100001010
private noncomputable def ep0011100001011_0 : Blocks := edgeBlocks% "full/vectors/0011100001011-E-0000.bin"
noncomputable def ep0011100001011 : Blocks := ep0011100001011_0
private theorem idp0011100001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110000101.list =
    C ((2:ℤ)^73) * horner X vp0011100001011.list + horner X ep0011100001011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100001011 : Branch 1 (-1801761639/2000000 : ℚ) vp001110000101 := by
  apply branch_checked idp0011100001011 (by positivity) (by decide +kernel)
  rw [show 2*(-1801761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1802761639/1000000 : ℚ) by norm_num]
  exact coverp0011100001011
theorem coverp001110000101 : Covers (-1801761639/2000000 : ℚ) vp001110000101 := join_branches bp0011100001010 bp0011100001011
private noncomputable def vp0011100001001_0 : Blocks := edgeBlocks% "full/vectors/0011100001001-V-0000.bin"
noncomputable def vp0011100001001 : Blocks := vp0011100001001_0
theorem coverp0011100001001 : Covers (-1800761639/1000000 : ℚ) vp0011100001001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100001000_0 : Blocks := edgeBlocks% "full/vectors/0011100001000-V-0000.bin"
noncomputable def vp0011100001000 : Blocks := vp0011100001000_0
theorem coverp0011100001000 : Covers (-1799761639/1000000 : ℚ) vp0011100001000 := cover_leaf (by decide +kernel)
private noncomputable def vp001110000100_0 : Blocks := edgeBlocks% "full/vectors/001110000100-V-0000.bin"
noncomputable def vp001110000100 : Blocks := vp001110000100_0
private theorem bp0011100001000 : Branch 0 (-1799761639/2000000 : ℚ) vp001110000100 := by
  apply branch_left_normalized (c:=vp0011100001000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1799761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1799761639/1000000 : ℚ) by norm_num]
  exact coverp0011100001000
private noncomputable def ep0011100001001_0 : Blocks := edgeBlocks% "full/vectors/0011100001001-E-0000.bin"
noncomputable def ep0011100001001 : Blocks := ep0011100001001_0
private theorem idp0011100001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110000100.list =
    C ((2:ℤ)^72) * horner X vp0011100001001.list + horner X ep0011100001001.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100001001 : Branch 1 (-1799761639/2000000 : ℚ) vp001110000100 := by
  apply branch_checked idp0011100001001 (by positivity) (by decide +kernel)
  rw [show 2*(-1799761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1800761639/1000000 : ℚ) by norm_num]
  exact coverp0011100001001
theorem coverp001110000100 : Covers (-1799761639/2000000 : ℚ) vp001110000100 := join_branches bp0011100001000 bp0011100001001
private noncomputable def vp00111000010_0 : Blocks := edgeBlocks% "full/vectors/00111000010-V-0000.bin"
noncomputable def vp00111000010 : Blocks := vp00111000010_0
private theorem bp001110000100 : Branch 0 (-1799761639/4000000 : ℚ) vp00111000010 := by
  apply branch_left_normalized (c:=vp001110000100) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1799761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1799761639/2000000 : ℚ) by norm_num]
  exact coverp001110000100
private noncomputable def ep001110000101_0 : Blocks := edgeBlocks% "full/vectors/001110000101-E-0000.bin"
noncomputable def ep001110000101 : Blocks := ep001110000101_0
private theorem idp001110000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111000010.list =
    C ((2:ℤ)^126) * horner X vp001110000101.list + horner X ep001110000101.list := by
  exact edge_identity (B := (2:ℤ)^265) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110000101 : Branch 1 (-1799761639/4000000 : ℚ) vp00111000010 := by
  apply branch_checked idp001110000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1799761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1801761639/2000000 : ℚ) by norm_num]
  exact coverp001110000101
theorem coverp00111000010 : Covers (-1799761639/4000000 : ℚ) vp00111000010 := join_branches bp001110000100 bp001110000101
private noncomputable def vp0011100001_0 : Blocks := edgeBlocks% "full/vectors/0011100001-V-0000.bin"
private noncomputable def vp0011100001_1 : Blocks := edgeBlocks% "full/vectors/0011100001-V-0001.bin"
noncomputable def vp0011100001 : Blocks := (Blocks.join vp0011100001_0 vp0011100001_1)
private theorem bp00111000010 : Branch 0 (-1799761639/8000000 : ℚ) vp0011100001 := by
  apply branch_left_normalized (c:=vp00111000010) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-1799761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1799761639/4000000 : ℚ) by norm_num]
  exact coverp00111000010
private noncomputable def ep00111000011_0 : Blocks := edgeBlocks% "full/vectors/00111000011-E-0000.bin"
private noncomputable def ep00111000011_1 : Blocks := edgeBlocks% "full/vectors/00111000011-E-0001.bin"
noncomputable def ep00111000011 : Blocks := (Blocks.join ep00111000011_0 ep00111000011_1)
private theorem idp00111000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011100001.list =
    C ((2:ℤ)^230) * horner X vp00111000011.list + horner X ep00111000011.list := by
  exact edge_identity (B := (2:ℤ)^407) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111000011 : Branch 1 (-1799761639/8000000 : ℚ) vp0011100001 := by
  apply branch_checked idp00111000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1799761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1803761639/4000000 : ℚ) by norm_num]
  exact coverp00111000011
theorem coverp0011100001 : Covers (-1799761639/8000000 : ℚ) vp0011100001 := join_branches bp00111000010 bp00111000011
private noncomputable def vp0011100000111_0 : Blocks := edgeBlocks% "full/vectors/0011100000111-V-0000.bin"
noncomputable def vp0011100000111 : Blocks := vp0011100000111_0
theorem coverp0011100000111 : Covers (-1798761639/1000000 : ℚ) vp0011100000111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100000110_0 : Blocks := edgeBlocks% "full/vectors/0011100000110-V-0000.bin"
noncomputable def vp0011100000110 : Blocks := vp0011100000110_0
theorem coverp0011100000110 : Covers (-1797761639/1000000 : ℚ) vp0011100000110 := cover_leaf (by decide +kernel)
private noncomputable def vp001110000011_0 : Blocks := edgeBlocks% "full/vectors/001110000011-V-0000.bin"
noncomputable def vp001110000011 : Blocks := vp001110000011_0
private theorem bp0011100000110 : Branch 0 (-1797761639/2000000 : ℚ) vp001110000011 := by
  apply branch_left_normalized (c:=vp0011100000110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1797761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1797761639/1000000 : ℚ) by norm_num]
  exact coverp0011100000110
private noncomputable def ep0011100000111_0 : Blocks := edgeBlocks% "full/vectors/0011100000111-E-0000.bin"
noncomputable def ep0011100000111 : Blocks := ep0011100000111_0
private theorem idp0011100000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110000011.list =
    C ((2:ℤ)^73) * horner X vp0011100000111.list + horner X ep0011100000111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100000111 : Branch 1 (-1797761639/2000000 : ℚ) vp001110000011 := by
  apply branch_checked idp0011100000111 (by positivity) (by decide +kernel)
  rw [show 2*(-1797761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1798761639/1000000 : ℚ) by norm_num]
  exact coverp0011100000111
theorem coverp001110000011 : Covers (-1797761639/2000000 : ℚ) vp001110000011 := join_branches bp0011100000110 bp0011100000111
private noncomputable def vp0011100000101_0 : Blocks := edgeBlocks% "full/vectors/0011100000101-V-0000.bin"
noncomputable def vp0011100000101 : Blocks := vp0011100000101_0
theorem coverp0011100000101 : Covers (-1796761639/1000000 : ℚ) vp0011100000101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100000100_0 : Blocks := edgeBlocks% "full/vectors/0011100000100-V-0000.bin"
noncomputable def vp0011100000100 : Blocks := vp0011100000100_0
theorem coverp0011100000100 : Covers (-1795761639/1000000 : ℚ) vp0011100000100 := cover_leaf (by decide +kernel)
private noncomputable def vp001110000010_0 : Blocks := edgeBlocks% "full/vectors/001110000010-V-0000.bin"
noncomputable def vp001110000010 : Blocks := vp001110000010_0
private theorem bp0011100000100 : Branch 0 (-1795761639/2000000 : ℚ) vp001110000010 := by
  apply branch_left_normalized (c:=vp0011100000100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1795761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1795761639/1000000 : ℚ) by norm_num]
  exact coverp0011100000100
private noncomputable def ep0011100000101_0 : Blocks := edgeBlocks% "full/vectors/0011100000101-E-0000.bin"
noncomputable def ep0011100000101 : Blocks := ep0011100000101_0
private theorem idp0011100000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110000010.list =
    C ((2:ℤ)^74) * horner X vp0011100000101.list + horner X ep0011100000101.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100000101 : Branch 1 (-1795761639/2000000 : ℚ) vp001110000010 := by
  apply branch_checked idp0011100000101 (by positivity) (by decide +kernel)
  rw [show 2*(-1795761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1796761639/1000000 : ℚ) by norm_num]
  exact coverp0011100000101
theorem coverp001110000010 : Covers (-1795761639/2000000 : ℚ) vp001110000010 := join_branches bp0011100000100 bp0011100000101
private noncomputable def vp00111000001_0 : Blocks := edgeBlocks% "full/vectors/00111000001-V-0000.bin"
noncomputable def vp00111000001 : Blocks := vp00111000001_0
private theorem bp001110000010 : Branch 0 (-1795761639/4000000 : ℚ) vp00111000001 := by
  apply branch_left_normalized (c:=vp001110000010) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1795761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1795761639/2000000 : ℚ) by norm_num]
  exact coverp001110000010
private noncomputable def ep001110000011_0 : Blocks := edgeBlocks% "full/vectors/001110000011-E-0000.bin"
noncomputable def ep001110000011 : Blocks := ep001110000011_0
private theorem idp001110000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111000001.list =
    C ((2:ℤ)^127) * horner X vp001110000011.list + horner X ep001110000011.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110000011 : Branch 1 (-1795761639/4000000 : ℚ) vp00111000001 := by
  apply branch_checked idp001110000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1795761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1797761639/2000000 : ℚ) by norm_num]
  exact coverp001110000011
theorem coverp00111000001 : Covers (-1795761639/4000000 : ℚ) vp00111000001 := join_branches bp001110000010 bp001110000011
private noncomputable def vp0011100000011_0 : Blocks := edgeBlocks% "full/vectors/0011100000011-V-0000.bin"
noncomputable def vp0011100000011 : Blocks := vp0011100000011_0
theorem coverp0011100000011 : Covers (-1794761639/1000000 : ℚ) vp0011100000011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100000010_0 : Blocks := edgeBlocks% "full/vectors/0011100000010-V-0000.bin"
noncomputable def vp0011100000010 : Blocks := vp0011100000010_0
theorem coverp0011100000010 : Covers (-1793761639/1000000 : ℚ) vp0011100000010 := cover_leaf (by decide +kernel)
private noncomputable def vp001110000001_0 : Blocks := edgeBlocks% "full/vectors/001110000001-V-0000.bin"
noncomputable def vp001110000001 : Blocks := vp001110000001_0
private theorem bp0011100000010 : Branch 0 (-1793761639/2000000 : ℚ) vp001110000001 := by
  apply branch_left_normalized (c:=vp0011100000010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1793761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1793761639/1000000 : ℚ) by norm_num]
  exact coverp0011100000010
private noncomputable def ep0011100000011_0 : Blocks := edgeBlocks% "full/vectors/0011100000011-E-0000.bin"
noncomputable def ep0011100000011 : Blocks := ep0011100000011_0
private theorem idp0011100000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110000001.list =
    C ((2:ℤ)^73) * horner X vp0011100000011.list + horner X ep0011100000011.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100000011 : Branch 1 (-1793761639/2000000 : ℚ) vp001110000001 := by
  apply branch_checked idp0011100000011 (by positivity) (by decide +kernel)
  rw [show 2*(-1793761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1794761639/1000000 : ℚ) by norm_num]
  exact coverp0011100000011
theorem coverp001110000001 : Covers (-1793761639/2000000 : ℚ) vp001110000001 := join_branches bp0011100000010 bp0011100000011
private noncomputable def vp0011100000001_0 : Blocks := edgeBlocks% "full/vectors/0011100000001-V-0000.bin"
noncomputable def vp0011100000001 : Blocks := vp0011100000001_0
theorem coverp0011100000001 : Covers (-1792761639/1000000 : ℚ) vp0011100000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011100000000_0 : Blocks := edgeBlocks% "full/vectors/0011100000000-V-0000.bin"
noncomputable def vp0011100000000 : Blocks := vp0011100000000_0
theorem coverp0011100000000 : Covers (-1791761639/1000000 : ℚ) vp0011100000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001110000000_0 : Blocks := edgeBlocks% "full/vectors/001110000000-V-0000.bin"
noncomputable def vp001110000000 : Blocks := vp001110000000_0
private theorem bp0011100000000 : Branch 0 (-1791761639/2000000 : ℚ) vp001110000000 := by
  apply branch_left_normalized (c:=vp0011100000000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1791761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1791761639/1000000 : ℚ) by norm_num]
  exact coverp0011100000000
private noncomputable def ep0011100000001_0 : Blocks := edgeBlocks% "full/vectors/0011100000001-E-0000.bin"
noncomputable def ep0011100000001 : Blocks := ep0011100000001_0
private theorem idp0011100000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110000000.list =
    C ((2:ℤ)^73) * horner X vp0011100000001.list + horner X ep0011100000001.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100000001 : Branch 1 (-1791761639/2000000 : ℚ) vp001110000000 := by
  apply branch_checked idp0011100000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1791761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1792761639/1000000 : ℚ) by norm_num]
  exact coverp0011100000001
theorem coverp001110000000 : Covers (-1791761639/2000000 : ℚ) vp001110000000 := join_branches bp0011100000000 bp0011100000001
private noncomputable def vp00111000000_0 : Blocks := edgeBlocks% "full/vectors/00111000000-V-0000.bin"
noncomputable def vp00111000000 : Blocks := vp00111000000_0
private theorem bp001110000000 : Branch 0 (-1791761639/4000000 : ℚ) vp00111000000 := by
  apply branch_left_normalized (c:=vp001110000000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1791761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1791761639/2000000 : ℚ) by norm_num]
  exact coverp001110000000
private noncomputable def ep001110000001_0 : Blocks := edgeBlocks% "full/vectors/001110000001-E-0000.bin"
noncomputable def ep001110000001 : Blocks := ep001110000001_0
private theorem idp001110000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111000000.list =
    C ((2:ℤ)^127) * horner X vp001110000001.list + horner X ep001110000001.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110000001 : Branch 1 (-1791761639/4000000 : ℚ) vp00111000000 := by
  apply branch_checked idp001110000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1791761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1793761639/2000000 : ℚ) by norm_num]
  exact coverp001110000001
theorem coverp00111000000 : Covers (-1791761639/4000000 : ℚ) vp00111000000 := join_branches bp001110000000 bp001110000001
private noncomputable def vp0011100000_0 : Blocks := edgeBlocks% "full/vectors/0011100000-V-0000.bin"
private noncomputable def vp0011100000_1 : Blocks := edgeBlocks% "full/vectors/0011100000-V-0001.bin"
noncomputable def vp0011100000 : Blocks := (Blocks.join vp0011100000_0 vp0011100000_1)
private theorem bp00111000000 : Branch 0 (-1791761639/8000000 : ℚ) vp0011100000 := by
  apply branch_left_normalized (c:=vp00111000000) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-1791761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1791761639/4000000 : ℚ) by norm_num]
  exact coverp00111000000
private noncomputable def ep00111000001_0 : Blocks := edgeBlocks% "full/vectors/00111000001-E-0000.bin"
private noncomputable def ep00111000001_1 : Blocks := edgeBlocks% "full/vectors/00111000001-E-0001.bin"
noncomputable def ep00111000001 : Blocks := (Blocks.join ep00111000001_0 ep00111000001_1)
private theorem idp00111000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011100000.list =
    C ((2:ℤ)^231) * horner X vp00111000001.list + horner X ep00111000001.list := by
  exact edge_identity (B := (2:ℤ)^408) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111000001 : Branch 1 (-1791761639/8000000 : ℚ) vp0011100000 := by
  apply branch_checked idp00111000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1791761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1795761639/4000000 : ℚ) by norm_num]
  exact coverp00111000001
theorem coverp0011100000 : Covers (-1791761639/8000000 : ℚ) vp0011100000 := join_branches bp00111000000 bp00111000001
private noncomputable def vp001110000_0 : Blocks := edgeBlocks% "full/vectors/001110000-V-0000.bin"
private noncomputable def vp001110000_1 : Blocks := edgeBlocks% "full/vectors/001110000-V-0001.bin"
private noncomputable def vp001110000_2 : Blocks := edgeBlocks% "full/vectors/001110000-V-0002.bin"
private noncomputable def vp001110000_3 : Blocks := edgeBlocks% "full/vectors/001110000-V-0003.bin"
noncomputable def vp001110000 : Blocks := (Blocks.join (Blocks.join vp001110000_0 vp001110000_1) (Blocks.join vp001110000_2 vp001110000_3))
private theorem bp0011100000 : Branch 0 (-1791761639/16000000 : ℚ) vp001110000 := by
  apply branch_left_normalized (c:=vp0011100000) (k:=0) (m:=207) (by decide +kernel)
  rw [show 2*(-1791761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1791761639/8000000 : ℚ) by norm_num]
  exact coverp0011100000
private noncomputable def ep0011100001_0 : Blocks := edgeBlocks% "full/vectors/0011100001-E-0000.bin"
private noncomputable def ep0011100001_1 : Blocks := edgeBlocks% "full/vectors/0011100001-E-0001.bin"
private noncomputable def ep0011100001_2 : Blocks := edgeBlocks% "full/vectors/0011100001-E-0002.bin"
private noncomputable def ep0011100001_3 : Blocks := edgeBlocks% "full/vectors/0011100001-E-0003.bin"
noncomputable def ep0011100001 : Blocks := (Blocks.join (Blocks.join ep0011100001_0 ep0011100001_1) (Blocks.join ep0011100001_2 ep0011100001_3))
private theorem idp0011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110000.list =
    C ((2:ℤ)^440) * horner X vp0011100001.list + horner X ep0011100001.list := by
  exact edge_identity (B := (2:ℤ)^691) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011100001 : Branch 1 (-1791761639/16000000 : ℚ) vp001110000 := by
  apply branch_checked idp0011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1791761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1799761639/8000000 : ℚ) by norm_num]
  exact coverp0011100001
theorem coverp001110000 : Covers (-1791761639/16000000 : ℚ) vp001110000 := join_branches bp0011100000 bp0011100001
private noncomputable def vp00111000_0 : Blocks := edgeBlocks% "full/vectors/00111000-V-0000.bin"
private noncomputable def vp00111000_1 : Blocks := edgeBlocks% "full/vectors/00111000-V-0001.bin"
private noncomputable def vp00111000_2 : Blocks := edgeBlocks% "full/vectors/00111000-V-0002.bin"
private noncomputable def vp00111000_3 : Blocks := edgeBlocks% "full/vectors/00111000-V-0003.bin"
private noncomputable def vp00111000_4 : Blocks := edgeBlocks% "full/vectors/00111000-V-0004.bin"
private noncomputable def vp00111000_5 : Blocks := edgeBlocks% "full/vectors/00111000-V-0005.bin"
noncomputable def vp00111000 : Blocks := (Blocks.join (Blocks.join vp00111000_0 (Blocks.join vp00111000_1 vp00111000_2)) (Blocks.join vp00111000_3 (Blocks.join vp00111000_4 vp00111000_5)))
private theorem bp001110000 : Branch 0 (-1791761639/32000000 : ℚ) vp00111000 := by
  apply branch_left_normalized (c:=vp001110000) (k:=0) (m:=392) (by decide +kernel)
  rw [show 2*(-1791761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1791761639/16000000 : ℚ) by norm_num]
  exact coverp001110000
private noncomputable def ep001110001_0 : Blocks := edgeBlocks% "full/vectors/001110001-E-0000.bin"
private noncomputable def ep001110001_1 : Blocks := edgeBlocks% "full/vectors/001110001-E-0001.bin"
private noncomputable def ep001110001_2 : Blocks := edgeBlocks% "full/vectors/001110001-E-0002.bin"
private noncomputable def ep001110001_3 : Blocks := edgeBlocks% "full/vectors/001110001-E-0003.bin"
private noncomputable def ep001110001_4 : Blocks := edgeBlocks% "full/vectors/001110001-E-0004.bin"
private noncomputable def ep001110001_5 : Blocks := edgeBlocks% "full/vectors/001110001-E-0005.bin"
noncomputable def ep001110001 : Blocks := (Blocks.join (Blocks.join ep001110001_0 (Blocks.join ep001110001_1 ep001110001_2)) (Blocks.join ep001110001_3 (Blocks.join ep001110001_4 ep001110001_5)))
private theorem idp001110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00111000.list =
    C ((2:ℤ)^851) * horner X vp001110001.list + horner X ep001110001.list := by
  exact edge_identity (B := (2:ℤ)^1254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001110001 : Branch 1 (-1791761639/32000000 : ℚ) vp00111000 := by
  apply branch_checked idp001110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1791761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1807761639/16000000 : ℚ) by norm_num]
  exact coverp001110001
theorem coverp00111000 : Covers (-1791761639/32000000 : ℚ) vp00111000 := join_branches bp001110000 bp001110001
private noncomputable def vp0011100_0 : Blocks := edgeBlocks% "full/vectors/0011100-V-0000.bin"
private noncomputable def vp0011100_1 : Blocks := edgeBlocks% "full/vectors/0011100-V-0001.bin"
private noncomputable def vp0011100_2 : Blocks := edgeBlocks% "full/vectors/0011100-V-0002.bin"
private noncomputable def vp0011100_3 : Blocks := edgeBlocks% "full/vectors/0011100-V-0003.bin"
private noncomputable def vp0011100_4 : Blocks := edgeBlocks% "full/vectors/0011100-V-0004.bin"
private noncomputable def vp0011100_5 : Blocks := edgeBlocks% "full/vectors/0011100-V-0005.bin"
private noncomputable def vp0011100_6 : Blocks := edgeBlocks% "full/vectors/0011100-V-0006.bin"
private noncomputable def vp0011100_7 : Blocks := edgeBlocks% "full/vectors/0011100-V-0007.bin"
private noncomputable def vp0011100_8 : Blocks := edgeBlocks% "full/vectors/0011100-V-0008.bin"
private noncomputable def vp0011100_9 : Blocks := edgeBlocks% "full/vectors/0011100-V-0009.bin"
private noncomputable def vp0011100_10 : Blocks := edgeBlocks% "full/vectors/0011100-V-0010.bin"
private noncomputable def vp0011100_11 : Blocks := edgeBlocks% "full/vectors/0011100-V-0011.bin"
noncomputable def vp0011100 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0011100_0 (Blocks.join vp0011100_1 vp0011100_2)) (Blocks.join vp0011100_3 (Blocks.join vp0011100_4 vp0011100_5))) (Blocks.join (Blocks.join vp0011100_6 (Blocks.join vp0011100_7 vp0011100_8)) (Blocks.join vp0011100_9 (Blocks.join vp0011100_10 vp0011100_11))))
private theorem bp00111000 : Branch 0 (-1791761639/64000000 : ℚ) vp0011100 := by
  apply branch_left_normalized (c:=vp00111000) (k:=0) (m:=758) (by decide +kernel)
  rw [show 2*(-1791761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1791761639/32000000 : ℚ) by norm_num]
  exact coverp00111000
private noncomputable def ep00111001_0 : Blocks := edgeBlocks% "full/vectors/00111001-E-0000.bin"
private noncomputable def ep00111001_1 : Blocks := edgeBlocks% "full/vectors/00111001-E-0001.bin"
private noncomputable def ep00111001_2 : Blocks := edgeBlocks% "full/vectors/00111001-E-0002.bin"
private noncomputable def ep00111001_3 : Blocks := edgeBlocks% "full/vectors/00111001-E-0003.bin"
private noncomputable def ep00111001_4 : Blocks := edgeBlocks% "full/vectors/00111001-E-0004.bin"
private noncomputable def ep00111001_5 : Blocks := edgeBlocks% "full/vectors/00111001-E-0005.bin"
private noncomputable def ep00111001_6 : Blocks := edgeBlocks% "full/vectors/00111001-E-0006.bin"
private noncomputable def ep00111001_7 : Blocks := edgeBlocks% "full/vectors/00111001-E-0007.bin"
private noncomputable def ep00111001_8 : Blocks := edgeBlocks% "full/vectors/00111001-E-0008.bin"
private noncomputable def ep00111001_9 : Blocks := edgeBlocks% "full/vectors/00111001-E-0009.bin"
private noncomputable def ep00111001_10 : Blocks := edgeBlocks% "full/vectors/00111001-E-0010.bin"
private noncomputable def ep00111001_11 : Blocks := edgeBlocks% "full/vectors/00111001-E-0011.bin"
noncomputable def ep00111001 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00111001_0 (Blocks.join ep00111001_1 ep00111001_2)) (Blocks.join ep00111001_3 (Blocks.join ep00111001_4 ep00111001_5))) (Blocks.join (Blocks.join ep00111001_6 (Blocks.join ep00111001_7 ep00111001_8)) (Blocks.join ep00111001_9 (Blocks.join ep00111001_10 ep00111001_11))))
private theorem idp00111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011100.list =
    C ((2:ℤ)^1662) * horner X vp00111001.list + horner X ep00111001.list := by
  exact edge_identity (B := (2:ℤ)^2362) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00111001 : Branch 1 (-1791761639/64000000 : ℚ) vp0011100 := by
  apply branch_checked idp00111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1791761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1823761639/32000000 : ℚ) by norm_num]
  exact coverp00111001
theorem coverp0011100 : Covers (-1791761639/64000000 : ℚ) vp0011100 := join_branches bp00111000 bp00111001
private noncomputable def vp001110_0 : Blocks := edgeBlocks% "full/vectors/001110-V-0000.bin"
private noncomputable def vp001110_1 : Blocks := edgeBlocks% "full/vectors/001110-V-0001.bin"
private noncomputable def vp001110_2 : Blocks := edgeBlocks% "full/vectors/001110-V-0002.bin"
private noncomputable def vp001110_3 : Blocks := edgeBlocks% "full/vectors/001110-V-0003.bin"
private noncomputable def vp001110_4 : Blocks := edgeBlocks% "full/vectors/001110-V-0004.bin"
private noncomputable def vp001110_5 : Blocks := edgeBlocks% "full/vectors/001110-V-0005.bin"
private noncomputable def vp001110_6 : Blocks := edgeBlocks% "full/vectors/001110-V-0006.bin"
private noncomputable def vp001110_7 : Blocks := edgeBlocks% "full/vectors/001110-V-0007.bin"
private noncomputable def vp001110_8 : Blocks := edgeBlocks% "full/vectors/001110-V-0008.bin"
private noncomputable def vp001110_9 : Blocks := edgeBlocks% "full/vectors/001110-V-0009.bin"
private noncomputable def vp001110_10 : Blocks := edgeBlocks% "full/vectors/001110-V-0010.bin"
private noncomputable def vp001110_11 : Blocks := edgeBlocks% "full/vectors/001110-V-0011.bin"
private noncomputable def vp001110_12 : Blocks := edgeBlocks% "full/vectors/001110-V-0012.bin"
private noncomputable def vp001110_13 : Blocks := edgeBlocks% "full/vectors/001110-V-0013.bin"
private noncomputable def vp001110_14 : Blocks := edgeBlocks% "full/vectors/001110-V-0014.bin"
private noncomputable def vp001110_15 : Blocks := edgeBlocks% "full/vectors/001110-V-0015.bin"
private noncomputable def vp001110_16 : Blocks := edgeBlocks% "full/vectors/001110-V-0016.bin"
private noncomputable def vp001110_17 : Blocks := edgeBlocks% "full/vectors/001110-V-0017.bin"
private noncomputable def vp001110_18 : Blocks := edgeBlocks% "full/vectors/001110-V-0018.bin"
private noncomputable def vp001110_19 : Blocks := edgeBlocks% "full/vectors/001110-V-0019.bin"
private noncomputable def vp001110_20 : Blocks := edgeBlocks% "full/vectors/001110-V-0020.bin"
private noncomputable def vp001110_21 : Blocks := edgeBlocks% "full/vectors/001110-V-0021.bin"
private noncomputable def vp001110_22 : Blocks := edgeBlocks% "full/vectors/001110-V-0022.bin"
noncomputable def vp001110 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join vp001110_0 vp001110_1) (Blocks.join vp001110_2 (Blocks.join vp001110_3 vp001110_4))) (Blocks.join (Blocks.join vp001110_5 (Blocks.join vp001110_6 vp001110_7)) (Blocks.join vp001110_8 (Blocks.join vp001110_9 vp001110_10)))) (Blocks.join (Blocks.join (Blocks.join vp001110_11 (Blocks.join vp001110_12 vp001110_13)) (Blocks.join vp001110_14 (Blocks.join vp001110_15 vp001110_16))) (Blocks.join (Blocks.join vp001110_17 (Blocks.join vp001110_18 vp001110_19)) (Blocks.join vp001110_20 (Blocks.join vp001110_21 vp001110_22)))))
private theorem bp0011100 : Branch 0 (-1791761639/128000000 : ℚ) vp001110 := by
  apply branch_left_normalized (c:=vp0011100) (k:=0) (m:=1476) (by decide +kernel)
  rw [show 2*(-1791761639/128000000 : ℚ) - ((0:ℤ):ℚ) = (-1791761639/64000000 : ℚ) by norm_num]
  exact coverp0011100
private noncomputable def ep0011101_0 : Blocks := edgeBlocks% "full/vectors/0011101-E-0000.bin"
private noncomputable def ep0011101_1 : Blocks := edgeBlocks% "full/vectors/0011101-E-0001.bin"
private noncomputable def ep0011101_2 : Blocks := edgeBlocks% "full/vectors/0011101-E-0002.bin"
private noncomputable def ep0011101_3 : Blocks := edgeBlocks% "full/vectors/0011101-E-0003.bin"
private noncomputable def ep0011101_4 : Blocks := edgeBlocks% "full/vectors/0011101-E-0004.bin"
private noncomputable def ep0011101_5 : Blocks := edgeBlocks% "full/vectors/0011101-E-0005.bin"
private noncomputable def ep0011101_6 : Blocks := edgeBlocks% "full/vectors/0011101-E-0006.bin"
private noncomputable def ep0011101_7 : Blocks := edgeBlocks% "full/vectors/0011101-E-0007.bin"
private noncomputable def ep0011101_8 : Blocks := edgeBlocks% "full/vectors/0011101-E-0008.bin"
private noncomputable def ep0011101_9 : Blocks := edgeBlocks% "full/vectors/0011101-E-0009.bin"
private noncomputable def ep0011101_10 : Blocks := edgeBlocks% "full/vectors/0011101-E-0010.bin"
private noncomputable def ep0011101_11 : Blocks := edgeBlocks% "full/vectors/0011101-E-0011.bin"
private noncomputable def ep0011101_12 : Blocks := edgeBlocks% "full/vectors/0011101-E-0012.bin"
private noncomputable def ep0011101_13 : Blocks := edgeBlocks% "full/vectors/0011101-E-0013.bin"
private noncomputable def ep0011101_14 : Blocks := edgeBlocks% "full/vectors/0011101-E-0014.bin"
private noncomputable def ep0011101_15 : Blocks := edgeBlocks% "full/vectors/0011101-E-0015.bin"
private noncomputable def ep0011101_16 : Blocks := edgeBlocks% "full/vectors/0011101-E-0016.bin"
private noncomputable def ep0011101_17 : Blocks := edgeBlocks% "full/vectors/0011101-E-0017.bin"
private noncomputable def ep0011101_18 : Blocks := edgeBlocks% "full/vectors/0011101-E-0018.bin"
private noncomputable def ep0011101_19 : Blocks := edgeBlocks% "full/vectors/0011101-E-0019.bin"
private noncomputable def ep0011101_20 : Blocks := edgeBlocks% "full/vectors/0011101-E-0020.bin"
private noncomputable def ep0011101_21 : Blocks := edgeBlocks% "full/vectors/0011101-E-0021.bin"
private noncomputable def ep0011101_22 : Blocks := edgeBlocks% "full/vectors/0011101-E-0022.bin"
noncomputable def ep0011101 : Blocks := (Blocks.join (Blocks.join (Blocks.join (Blocks.join ep0011101_0 ep0011101_1) (Blocks.join ep0011101_2 (Blocks.join ep0011101_3 ep0011101_4))) (Blocks.join (Blocks.join ep0011101_5 (Blocks.join ep0011101_6 ep0011101_7)) (Blocks.join ep0011101_8 (Blocks.join ep0011101_9 ep0011101_10)))) (Blocks.join (Blocks.join (Blocks.join ep0011101_11 (Blocks.join ep0011101_12 ep0011101_13)) (Blocks.join ep0011101_14 (Blocks.join ep0011101_15 ep0011101_16))) (Blocks.join (Blocks.join ep0011101_17 (Blocks.join ep0011101_18 ep0011101_19)) (Blocks.join ep0011101_20 (Blocks.join ep0011101_21 ep0011101_22)))))
private def ptsp0011101 : List ℤ := [((2:ℤ)^4189+0),((2:ℤ)^4189+1)]
private theorem boundp0011101 : 2^vp001110.size*absSum vp001110.list + ((2:ℤ)^3235*absSum vp0011101.list+absSum ep0011101.list) < (2:ℤ)^4519 := by decide +kernel
private theorem pointp0011101_0 : fastHom 1 ((2:ℤ)^4189+0) vp001110 = ((2:ℤ)^3235)*vp0011101.subst ((2:ℤ)^4189+0)+ep0011101.subst ((2:ℤ)^4189+0) := by decide +kernel
private theorem pointp0011101_1 : fastHom 1 ((2:ℤ)^4189+1) vp001110 = ((2:ℤ)^3235)*vp0011101.subst ((2:ℤ)^4189+1)+ep0011101.subst ((2:ℤ)^4189+1) := by decide +kernel
private theorem checkp0011101 (x:ℤ) (hx:x ∈ ptsp0011101) : fastHom 1 x vp001110 = ((2:ℤ)^3235)*vp0011101.subst x+ep0011101.subst x := by
  simp only [ptsp0011101,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl | rfl
  · exact pointp0011101_0
  · exact pointp0011101_1
private theorem idp0011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001110.list =
    C ((2:ℤ)^3235) * horner X vp0011101.list + horner X ep0011101.list := by
  apply edge_identity (B := (2:ℤ)^4519) (by decide) (by positivity) (by positivity) boundp0011101
  apply edge_scalar_of_shards (by decide) (by positivity) ptsp0011101 (by decide +kernel)
  · have h : ptsp0011101.all (fun x => decide (0 < x)) = true := by decide +kernel
    simpa only [List.all_eq_true,decide_eq_true_eq] using h
  · exact boundp0011101.trans_le (by decide +kernel)
  · exact checkp0011101
private theorem bp0011101 : Branch 1 (-1791761639/128000000 : ℚ) vp001110 := by
  apply branch_checked idp0011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1791761639/128000000 : ℚ) - ((1:ℤ):ℚ) = (-1855761639/64000000 : ℚ) by norm_num]
  exact coverp0011101
theorem coverp001110 : Covers (-1791761639/128000000 : ℚ) vp001110 := join_branches bp0011100 bp0011101
end NextProof.EdgeFull

