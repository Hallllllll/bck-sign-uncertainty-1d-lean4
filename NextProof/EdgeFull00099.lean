import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp0011011111111_0 : Blocks := edgeBlocks% "full/vectors/0011011111111-V-0000.bin"
noncomputable def vp0011011111111 : Blocks := vp0011011111111_0
theorem coverp0011011111111 : Covers (-1790761639/1000000 : ℚ) vp0011011111111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011011111110_0 : Blocks := edgeBlocks% "full/vectors/0011011111110-V-0000.bin"
noncomputable def vp0011011111110 : Blocks := vp0011011111110_0
theorem coverp0011011111110 : Covers (-1789761639/1000000 : ℚ) vp0011011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp001101111111_0 : Blocks := edgeBlocks% "full/vectors/001101111111-V-0000.bin"
noncomputable def vp001101111111 : Blocks := vp001101111111_0
private theorem bp0011011111110 : Branch 0 (-1789761639/2000000 : ℚ) vp001101111111 := by
  apply branch_left_normalized (c:=vp0011011111110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1789761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1789761639/1000000 : ℚ) by norm_num]
  exact coverp0011011111110
private noncomputable def ep0011011111111_0 : Blocks := edgeBlocks% "full/vectors/0011011111111-E-0000.bin"
noncomputable def ep0011011111111 : Blocks := ep0011011111111_0
private theorem idp0011011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101111111.list =
    C ((2:ℤ)^73) * horner X vp0011011111111.list + horner X ep0011011111111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011111111 : Branch 1 (-1789761639/2000000 : ℚ) vp001101111111 := by
  apply branch_checked idp0011011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1789761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1790761639/1000000 : ℚ) by norm_num]
  exact coverp0011011111111
theorem coverp001101111111 : Covers (-1789761639/2000000 : ℚ) vp001101111111 := join_branches bp0011011111110 bp0011011111111
private noncomputable def vp0011011111101_0 : Blocks := edgeBlocks% "full/vectors/0011011111101-V-0000.bin"
noncomputable def vp0011011111101 : Blocks := vp0011011111101_0
theorem coverp0011011111101 : Covers (-1788761639/1000000 : ℚ) vp0011011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011011111100_0 : Blocks := edgeBlocks% "full/vectors/0011011111100-V-0000.bin"
noncomputable def vp0011011111100 : Blocks := vp0011011111100_0
theorem coverp0011011111100 : Covers (-1787761639/1000000 : ℚ) vp0011011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp001101111110_0 : Blocks := edgeBlocks% "full/vectors/001101111110-V-0000.bin"
noncomputable def vp001101111110 : Blocks := vp001101111110_0
private theorem bp0011011111100 : Branch 0 (-1787761639/2000000 : ℚ) vp001101111110 := by
  apply branch_left_normalized (c:=vp0011011111100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1787761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1787761639/1000000 : ℚ) by norm_num]
  exact coverp0011011111100
private noncomputable def ep0011011111101_0 : Blocks := edgeBlocks% "full/vectors/0011011111101-E-0000.bin"
noncomputable def ep0011011111101 : Blocks := ep0011011111101_0
private theorem idp0011011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101111110.list =
    C ((2:ℤ)^72) * horner X vp0011011111101.list + horner X ep0011011111101.list := by
  exact edge_identity (B := (2:ℤ)^192) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011111101 : Branch 1 (-1787761639/2000000 : ℚ) vp001101111110 := by
  apply branch_checked idp0011011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1787761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1788761639/1000000 : ℚ) by norm_num]
  exact coverp0011011111101
theorem coverp001101111110 : Covers (-1787761639/2000000 : ℚ) vp001101111110 := join_branches bp0011011111100 bp0011011111101
private noncomputable def vp00110111111_0 : Blocks := edgeBlocks% "full/vectors/00110111111-V-0000.bin"
noncomputable def vp00110111111 : Blocks := vp00110111111_0
private theorem bp001101111110 : Branch 0 (-1787761639/4000000 : ℚ) vp00110111111 := by
  apply branch_left_normalized (c:=vp001101111110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1787761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1787761639/2000000 : ℚ) by norm_num]
  exact coverp001101111110
private noncomputable def ep001101111111_0 : Blocks := edgeBlocks% "full/vectors/001101111111-E-0000.bin"
noncomputable def ep001101111111 : Blocks := ep001101111111_0
private theorem idp001101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110111111.list =
    C ((2:ℤ)^126) * horner X vp001101111111.list + horner X ep001101111111.list := by
  exact edge_identity (B := (2:ℤ)^265) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101111111 : Branch 1 (-1787761639/4000000 : ℚ) vp00110111111 := by
  apply branch_checked idp001101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1787761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1789761639/2000000 : ℚ) by norm_num]
  exact coverp001101111111
theorem coverp00110111111 : Covers (-1787761639/4000000 : ℚ) vp00110111111 := join_branches bp001101111110 bp001101111111
private noncomputable def vp0011011111011_0 : Blocks := edgeBlocks% "full/vectors/0011011111011-V-0000.bin"
noncomputable def vp0011011111011 : Blocks := vp0011011111011_0
theorem coverp0011011111011 : Covers (-1786761639/1000000 : ℚ) vp0011011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0011011111010_0 : Blocks := edgeBlocks% "full/vectors/0011011111010-V-0000.bin"
noncomputable def vp0011011111010 : Blocks := vp0011011111010_0
theorem coverp0011011111010 : Covers (-1785761639/1000000 : ℚ) vp0011011111010 := cover_leaf (by decide +kernel)
private noncomputable def vp001101111101_0 : Blocks := edgeBlocks% "full/vectors/001101111101-V-0000.bin"
noncomputable def vp001101111101 : Blocks := vp001101111101_0
private theorem bp0011011111010 : Branch 0 (-1785761639/2000000 : ℚ) vp001101111101 := by
  apply branch_left_normalized (c:=vp0011011111010) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1785761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1785761639/1000000 : ℚ) by norm_num]
  exact coverp0011011111010
private noncomputable def ep0011011111011_0 : Blocks := edgeBlocks% "full/vectors/0011011111011-E-0000.bin"
noncomputable def ep0011011111011 : Blocks := ep0011011111011_0
private theorem idp0011011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101111101.list =
    C ((2:ℤ)^74) * horner X vp0011011111011.list + horner X ep0011011111011.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011111011 : Branch 1 (-1785761639/2000000 : ℚ) vp001101111101 := by
  apply branch_checked idp0011011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1785761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1786761639/1000000 : ℚ) by norm_num]
  exact coverp0011011111011
theorem coverp001101111101 : Covers (-1785761639/2000000 : ℚ) vp001101111101 := join_branches bp0011011111010 bp0011011111011
private noncomputable def vp0011011111001_0 : Blocks := edgeBlocks% "full/vectors/0011011111001-V-0000.bin"
noncomputable def vp0011011111001 : Blocks := vp0011011111001_0
theorem coverp0011011111001 : Covers (-1784761639/1000000 : ℚ) vp0011011111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011011111000_0 : Blocks := edgeBlocks% "full/vectors/0011011111000-V-0000.bin"
noncomputable def vp0011011111000 : Blocks := vp0011011111000_0
theorem coverp0011011111000 : Covers (-1783761639/1000000 : ℚ) vp0011011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp001101111100_0 : Blocks := edgeBlocks% "full/vectors/001101111100-V-0000.bin"
noncomputable def vp001101111100 : Blocks := vp001101111100_0
private theorem bp0011011111000 : Branch 0 (-1783761639/2000000 : ℚ) vp001101111100 := by
  apply branch_left_normalized (c:=vp0011011111000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1783761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1783761639/1000000 : ℚ) by norm_num]
  exact coverp0011011111000
private noncomputable def ep0011011111001_0 : Blocks := edgeBlocks% "full/vectors/0011011111001-E-0000.bin"
noncomputable def ep0011011111001 : Blocks := ep0011011111001_0
private theorem idp0011011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101111100.list =
    C ((2:ℤ)^74) * horner X vp0011011111001.list + horner X ep0011011111001.list := by
  exact edge_identity (B := (2:ℤ)^194) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011111001 : Branch 1 (-1783761639/2000000 : ℚ) vp001101111100 := by
  apply branch_checked idp0011011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1783761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1784761639/1000000 : ℚ) by norm_num]
  exact coverp0011011111001
theorem coverp001101111100 : Covers (-1783761639/2000000 : ℚ) vp001101111100 := join_branches bp0011011111000 bp0011011111001
private noncomputable def vp00110111110_0 : Blocks := edgeBlocks% "full/vectors/00110111110-V-0000.bin"
noncomputable def vp00110111110 : Blocks := vp00110111110_0
private theorem bp001101111100 : Branch 0 (-1783761639/4000000 : ℚ) vp00110111110 := by
  apply branch_left_normalized (c:=vp001101111100) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-1783761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1783761639/2000000 : ℚ) by norm_num]
  exact coverp001101111100
private noncomputable def ep001101111101_0 : Blocks := edgeBlocks% "full/vectors/001101111101-E-0000.bin"
noncomputable def ep001101111101 : Blocks := ep001101111101_0
private theorem idp001101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110111110.list =
    C ((2:ℤ)^127) * horner X vp001101111101.list + horner X ep001101111101.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101111101 : Branch 1 (-1783761639/4000000 : ℚ) vp00110111110 := by
  apply branch_checked idp001101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1783761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1785761639/2000000 : ℚ) by norm_num]
  exact coverp001101111101
theorem coverp00110111110 : Covers (-1783761639/4000000 : ℚ) vp00110111110 := join_branches bp001101111100 bp001101111101
private noncomputable def vp0011011111_0 : Blocks := edgeBlocks% "full/vectors/0011011111-V-0000.bin"
private noncomputable def vp0011011111_1 : Blocks := edgeBlocks% "full/vectors/0011011111-V-0001.bin"
noncomputable def vp0011011111 : Blocks := (Blocks.join vp0011011111_0 vp0011011111_1)
private theorem bp00110111110 : Branch 0 (-1783761639/8000000 : ℚ) vp0011011111 := by
  apply branch_left_normalized (c:=vp00110111110) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-1783761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1783761639/4000000 : ℚ) by norm_num]
  exact coverp00110111110
private noncomputable def ep00110111111_0 : Blocks := edgeBlocks% "full/vectors/00110111111-E-0000.bin"
private noncomputable def ep00110111111_1 : Blocks := edgeBlocks% "full/vectors/00110111111-E-0001.bin"
noncomputable def ep00110111111 : Blocks := (Blocks.join ep00110111111_0 ep00110111111_1)
private theorem idp00110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011011111.list =
    C ((2:ℤ)^233) * horner X vp00110111111.list + horner X ep00110111111.list := by
  exact edge_identity (B := (2:ℤ)^409) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110111111 : Branch 1 (-1783761639/8000000 : ℚ) vp0011011111 := by
  apply branch_checked idp00110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-1783761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1787761639/4000000 : ℚ) by norm_num]
  exact coverp00110111111
theorem coverp0011011111 : Covers (-1783761639/8000000 : ℚ) vp0011011111 := join_branches bp00110111110 bp00110111111
private noncomputable def vp0011011110111_0 : Blocks := edgeBlocks% "full/vectors/0011011110111-V-0000.bin"
noncomputable def vp0011011110111 : Blocks := vp0011011110111_0
theorem coverp0011011110111 : Covers (-1782761639/1000000 : ℚ) vp0011011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0011011110110_0 : Blocks := edgeBlocks% "full/vectors/0011011110110-V-0000.bin"
noncomputable def vp0011011110110 : Blocks := vp0011011110110_0
theorem coverp0011011110110 : Covers (-1781761639/1000000 : ℚ) vp0011011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp001101111011_0 : Blocks := edgeBlocks% "full/vectors/001101111011-V-0000.bin"
noncomputable def vp001101111011 : Blocks := vp001101111011_0
private theorem bp0011011110110 : Branch 0 (-1781761639/2000000 : ℚ) vp001101111011 := by
  apply branch_left_normalized (c:=vp0011011110110) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1781761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1781761639/1000000 : ℚ) by norm_num]
  exact coverp0011011110110
private noncomputable def ep0011011110111_0 : Blocks := edgeBlocks% "full/vectors/0011011110111-E-0000.bin"
noncomputable def ep0011011110111 : Blocks := ep0011011110111_0
private theorem idp0011011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101111011.list =
    C ((2:ℤ)^72) * horner X vp0011011110111.list + horner X ep0011011110111.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011110111 : Branch 1 (-1781761639/2000000 : ℚ) vp001101111011 := by
  apply branch_checked idp0011011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1781761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1782761639/1000000 : ℚ) by norm_num]
  exact coverp0011011110111
theorem coverp001101111011 : Covers (-1781761639/2000000 : ℚ) vp001101111011 := join_branches bp0011011110110 bp0011011110111
private noncomputable def vp0011011110101_0 : Blocks := edgeBlocks% "full/vectors/0011011110101-V-0000.bin"
noncomputable def vp0011011110101 : Blocks := vp0011011110101_0
theorem coverp0011011110101 : Covers (-1780761639/1000000 : ℚ) vp0011011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011011110100_0 : Blocks := edgeBlocks% "full/vectors/0011011110100-V-0000.bin"
noncomputable def vp0011011110100 : Blocks := vp0011011110100_0
theorem coverp0011011110100 : Covers (-1779761639/1000000 : ℚ) vp0011011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp001101111010_0 : Blocks := edgeBlocks% "full/vectors/001101111010-V-0000.bin"
noncomputable def vp001101111010 : Blocks := vp001101111010_0
private theorem bp0011011110100 : Branch 0 (-1779761639/2000000 : ℚ) vp001101111010 := by
  apply branch_left_normalized (c:=vp0011011110100) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1779761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1779761639/1000000 : ℚ) by norm_num]
  exact coverp0011011110100
private noncomputable def ep0011011110101_0 : Blocks := edgeBlocks% "full/vectors/0011011110101-E-0000.bin"
noncomputable def ep0011011110101 : Blocks := ep0011011110101_0
private theorem idp0011011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101111010.list =
    C ((2:ℤ)^72) * horner X vp0011011110101.list + horner X ep0011011110101.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011110101 : Branch 1 (-1779761639/2000000 : ℚ) vp001101111010 := by
  apply branch_checked idp0011011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1779761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1780761639/1000000 : ℚ) by norm_num]
  exact coverp0011011110101
theorem coverp001101111010 : Covers (-1779761639/2000000 : ℚ) vp001101111010 := join_branches bp0011011110100 bp0011011110101
private noncomputable def vp00110111101_0 : Blocks := edgeBlocks% "full/vectors/00110111101-V-0000.bin"
noncomputable def vp00110111101 : Blocks := vp00110111101_0
private theorem bp001101111010 : Branch 0 (-1779761639/4000000 : ℚ) vp00110111101 := by
  apply branch_left_normalized (c:=vp001101111010) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1779761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1779761639/2000000 : ℚ) by norm_num]
  exact coverp001101111010
private noncomputable def ep001101111011_0 : Blocks := edgeBlocks% "full/vectors/001101111011-E-0000.bin"
noncomputable def ep001101111011 : Blocks := ep001101111011_0
private theorem idp001101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110111101.list =
    C ((2:ℤ)^124) * horner X vp001101111011.list + horner X ep001101111011.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101111011 : Branch 1 (-1779761639/4000000 : ℚ) vp00110111101 := by
  apply branch_checked idp001101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1779761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1781761639/2000000 : ℚ) by norm_num]
  exact coverp001101111011
theorem coverp00110111101 : Covers (-1779761639/4000000 : ℚ) vp00110111101 := join_branches bp001101111010 bp001101111011
private noncomputable def vp001101111001_0 : Blocks := edgeBlocks% "full/vectors/001101111001-V-0000.bin"
noncomputable def vp001101111001 : Blocks := vp001101111001_0
theorem coverp001101111001 : Covers (-1777761639/2000000 : ℚ) vp001101111001 := cover_leaf (by decide +kernel)
private noncomputable def vp001101111000_0 : Blocks := edgeBlocks% "full/vectors/001101111000-V-0000.bin"
noncomputable def vp001101111000 : Blocks := vp001101111000_0
theorem coverp001101111000 : Covers (-1775761639/2000000 : ℚ) vp001101111000 := cover_leaf (by decide +kernel)
private noncomputable def vp00110111100_0 : Blocks := edgeBlocks% "full/vectors/00110111100-V-0000.bin"
noncomputable def vp00110111100 : Blocks := vp00110111100_0
private theorem bp001101111000 : Branch 0 (-1775761639/4000000 : ℚ) vp00110111100 := by
  apply branch_left_normalized (c:=vp001101111000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1775761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1775761639/2000000 : ℚ) by norm_num]
  exact coverp001101111000
private noncomputable def ep001101111001_0 : Blocks := edgeBlocks% "full/vectors/001101111001-E-0000.bin"
noncomputable def ep001101111001 : Blocks := ep001101111001_0
private theorem idp001101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110111100.list =
    C ((2:ℤ)^125) * horner X vp001101111001.list + horner X ep001101111001.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101111001 : Branch 1 (-1775761639/4000000 : ℚ) vp00110111100 := by
  apply branch_checked idp001101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1775761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1777761639/2000000 : ℚ) by norm_num]
  exact coverp001101111001
theorem coverp00110111100 : Covers (-1775761639/4000000 : ℚ) vp00110111100 := join_branches bp001101111000 bp001101111001
private noncomputable def vp0011011110_0 : Blocks := edgeBlocks% "full/vectors/0011011110-V-0000.bin"
private noncomputable def vp0011011110_1 : Blocks := edgeBlocks% "full/vectors/0011011110-V-0001.bin"
noncomputable def vp0011011110 : Blocks := (Blocks.join vp0011011110_0 vp0011011110_1)
private theorem bp00110111100 : Branch 0 (-1775761639/8000000 : ℚ) vp0011011110 := by
  apply branch_left_normalized (c:=vp00110111100) (k:=0) (m:=113) (by decide +kernel)
  rw [show 2*(-1775761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1775761639/4000000 : ℚ) by norm_num]
  exact coverp00110111100
private noncomputable def ep00110111101_0 : Blocks := edgeBlocks% "full/vectors/00110111101-E-0000.bin"
private noncomputable def ep00110111101_1 : Blocks := edgeBlocks% "full/vectors/00110111101-E-0001.bin"
noncomputable def ep00110111101 : Blocks := (Blocks.join ep00110111101_0 ep00110111101_1)
private theorem idp00110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011011110.list =
    C ((2:ℤ)^229) * horner X vp00110111101.list + horner X ep00110111101.list := by
  exact edge_identity (B := (2:ℤ)^404) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110111101 : Branch 1 (-1775761639/8000000 : ℚ) vp0011011110 := by
  apply branch_checked idp00110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-1775761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1779761639/4000000 : ℚ) by norm_num]
  exact coverp00110111101
theorem coverp0011011110 : Covers (-1775761639/8000000 : ℚ) vp0011011110 := join_branches bp00110111100 bp00110111101
private noncomputable def vp001101111_0 : Blocks := edgeBlocks% "full/vectors/001101111-V-0000.bin"
private noncomputable def vp001101111_1 : Blocks := edgeBlocks% "full/vectors/001101111-V-0001.bin"
private noncomputable def vp001101111_2 : Blocks := edgeBlocks% "full/vectors/001101111-V-0002.bin"
private noncomputable def vp001101111_3 : Blocks := edgeBlocks% "full/vectors/001101111-V-0003.bin"
noncomputable def vp001101111 : Blocks := (Blocks.join (Blocks.join vp001101111_0 vp001101111_1) (Blocks.join vp001101111_2 vp001101111_3))
private theorem bp0011011110 : Branch 0 (-1775761639/16000000 : ℚ) vp001101111 := by
  apply branch_left_normalized (c:=vp0011011110) (k:=0) (m:=206) (by decide +kernel)
  rw [show 2*(-1775761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1775761639/8000000 : ℚ) by norm_num]
  exact coverp0011011110
private noncomputable def ep0011011111_0 : Blocks := edgeBlocks% "full/vectors/0011011111-E-0000.bin"
private noncomputable def ep0011011111_1 : Blocks := edgeBlocks% "full/vectors/0011011111-E-0001.bin"
private noncomputable def ep0011011111_2 : Blocks := edgeBlocks% "full/vectors/0011011111-E-0002.bin"
private noncomputable def ep0011011111_3 : Blocks := edgeBlocks% "full/vectors/0011011111-E-0003.bin"
noncomputable def ep0011011111 : Blocks := (Blocks.join (Blocks.join ep0011011111_0 ep0011011111_1) (Blocks.join ep0011011111_2 ep0011011111_3))
private theorem idp0011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101111.list =
    C ((2:ℤ)^436) * horner X vp0011011111.list + horner X ep0011011111.list := by
  exact edge_identity (B := (2:ℤ)^689) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011111 : Branch 1 (-1775761639/16000000 : ℚ) vp001101111 := by
  apply branch_checked idp0011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-1775761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1783761639/8000000 : ℚ) by norm_num]
  exact coverp0011011111
theorem coverp001101111 : Covers (-1775761639/16000000 : ℚ) vp001101111 := join_branches bp0011011110 bp0011011111
private noncomputable def vp001101110111_0 : Blocks := edgeBlocks% "full/vectors/001101110111-V-0000.bin"
noncomputable def vp001101110111 : Blocks := vp001101110111_0
theorem coverp001101110111 : Covers (-1773761639/2000000 : ℚ) vp001101110111 := cover_leaf (by decide +kernel)
private noncomputable def vp001101110110_0 : Blocks := edgeBlocks% "full/vectors/001101110110-V-0000.bin"
noncomputable def vp001101110110 : Blocks := vp001101110110_0
theorem coverp001101110110 : Covers (-1771761639/2000000 : ℚ) vp001101110110 := cover_leaf (by decide +kernel)
private noncomputable def vp00110111011_0 : Blocks := edgeBlocks% "full/vectors/00110111011-V-0000.bin"
noncomputable def vp00110111011 : Blocks := vp00110111011_0
private theorem bp001101110110 : Branch 0 (-1771761639/4000000 : ℚ) vp00110111011 := by
  apply branch_left_normalized (c:=vp001101110110) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1771761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1771761639/2000000 : ℚ) by norm_num]
  exact coverp001101110110
private noncomputable def ep001101110111_0 : Blocks := edgeBlocks% "full/vectors/001101110111-E-0000.bin"
noncomputable def ep001101110111 : Blocks := ep001101110111_0
private theorem idp001101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110111011.list =
    C ((2:ℤ)^126) * horner X vp001101110111.list + horner X ep001101110111.list := by
  exact edge_identity (B := (2:ℤ)^263) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101110111 : Branch 1 (-1771761639/4000000 : ℚ) vp00110111011 := by
  apply branch_checked idp001101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1771761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1773761639/2000000 : ℚ) by norm_num]
  exact coverp001101110111
theorem coverp00110111011 : Covers (-1771761639/4000000 : ℚ) vp00110111011 := join_branches bp001101110110 bp001101110111
private noncomputable def vp001101110101_0 : Blocks := edgeBlocks% "full/vectors/001101110101-V-0000.bin"
noncomputable def vp001101110101 : Blocks := vp001101110101_0
theorem coverp001101110101 : Covers (-1769761639/2000000 : ℚ) vp001101110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0011011101001_0 : Blocks := edgeBlocks% "full/vectors/0011011101001-V-0000.bin"
noncomputable def vp0011011101001 : Blocks := vp0011011101001_0
theorem coverp0011011101001 : Covers (-1768761639/1000000 : ℚ) vp0011011101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011011101000_0 : Blocks := edgeBlocks% "full/vectors/0011011101000-V-0000.bin"
noncomputable def vp0011011101000 : Blocks := vp0011011101000_0
theorem coverp0011011101000 : Covers (-1767761639/1000000 : ℚ) vp0011011101000 := cover_leaf (by decide +kernel)
private noncomputable def vp001101110100_0 : Blocks := edgeBlocks% "full/vectors/001101110100-V-0000.bin"
noncomputable def vp001101110100 : Blocks := vp001101110100_0
private theorem bp0011011101000 : Branch 0 (-1767761639/2000000 : ℚ) vp001101110100 := by
  apply branch_left_normalized (c:=vp0011011101000) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-1767761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1767761639/1000000 : ℚ) by norm_num]
  exact coverp0011011101000
private noncomputable def ep0011011101001_0 : Blocks := edgeBlocks% "full/vectors/0011011101001-E-0000.bin"
noncomputable def ep0011011101001 : Blocks := ep0011011101001_0
private theorem idp0011011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101110100.list =
    C ((2:ℤ)^70) * horner X vp0011011101001.list + horner X ep0011011101001.list := by
  exact edge_identity (B := (2:ℤ)^189) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011101001 : Branch 1 (-1767761639/2000000 : ℚ) vp001101110100 := by
  apply branch_checked idp0011011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1767761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1768761639/1000000 : ℚ) by norm_num]
  exact coverp0011011101001
theorem coverp001101110100 : Covers (-1767761639/2000000 : ℚ) vp001101110100 := join_branches bp0011011101000 bp0011011101001
private noncomputable def vp00110111010_0 : Blocks := edgeBlocks% "full/vectors/00110111010-V-0000.bin"
noncomputable def vp00110111010 : Blocks := vp00110111010_0
private theorem bp001101110100 : Branch 0 (-1767761639/4000000 : ℚ) vp00110111010 := by
  apply branch_left_normalized (c:=vp001101110100) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1767761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1767761639/2000000 : ℚ) by norm_num]
  exact coverp001101110100
private noncomputable def ep001101110101_0 : Blocks := edgeBlocks% "full/vectors/001101110101-E-0000.bin"
noncomputable def ep001101110101 : Blocks := ep001101110101_0
private theorem idp001101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110111010.list =
    C ((2:ℤ)^122) * horner X vp001101110101.list + horner X ep001101110101.list := by
  exact edge_identity (B := (2:ℤ)^262) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101110101 : Branch 1 (-1767761639/4000000 : ℚ) vp00110111010 := by
  apply branch_checked idp001101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1767761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1769761639/2000000 : ℚ) by norm_num]
  exact coverp001101110101
theorem coverp00110111010 : Covers (-1767761639/4000000 : ℚ) vp00110111010 := join_branches bp001101110100 bp001101110101
private noncomputable def vp0011011101_0 : Blocks := edgeBlocks% "full/vectors/0011011101-V-0000.bin"
private noncomputable def vp0011011101_1 : Blocks := edgeBlocks% "full/vectors/0011011101-V-0001.bin"
noncomputable def vp0011011101 : Blocks := (Blocks.join vp0011011101_0 vp0011011101_1)
private theorem bp00110111010 : Branch 0 (-1767761639/8000000 : ℚ) vp0011011101 := by
  apply branch_left_normalized (c:=vp00110111010) (k:=0) (m:=113) (by decide +kernel)
  rw [show 2*(-1767761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1767761639/4000000 : ℚ) by norm_num]
  exact coverp00110111010
private noncomputable def ep00110111011_0 : Blocks := edgeBlocks% "full/vectors/00110111011-E-0000.bin"
private noncomputable def ep00110111011_1 : Blocks := edgeBlocks% "full/vectors/00110111011-E-0001.bin"
noncomputable def ep00110111011 : Blocks := (Blocks.join ep00110111011_0 ep00110111011_1)
private theorem idp00110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011011101.list =
    C ((2:ℤ)^230) * horner X vp00110111011.list + horner X ep00110111011.list := by
  exact edge_identity (B := (2:ℤ)^405) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110111011 : Branch 1 (-1767761639/8000000 : ℚ) vp0011011101 := by
  apply branch_checked idp00110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-1767761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1771761639/4000000 : ℚ) by norm_num]
  exact coverp00110111011
theorem coverp0011011101 : Covers (-1767761639/8000000 : ℚ) vp0011011101 := join_branches bp00110111010 bp00110111011
private noncomputable def vp001101110011_0 : Blocks := edgeBlocks% "full/vectors/001101110011-V-0000.bin"
noncomputable def vp001101110011 : Blocks := vp001101110011_0
theorem coverp001101110011 : Covers (-1765761639/2000000 : ℚ) vp001101110011 := cover_leaf (by decide +kernel)
private noncomputable def vp001101110010_0 : Blocks := edgeBlocks% "full/vectors/001101110010-V-0000.bin"
noncomputable def vp001101110010 : Blocks := vp001101110010_0
theorem coverp001101110010 : Covers (-1763761639/2000000 : ℚ) vp001101110010 := cover_leaf (by decide +kernel)
private noncomputable def vp00110111001_0 : Blocks := edgeBlocks% "full/vectors/00110111001-V-0000.bin"
noncomputable def vp00110111001 : Blocks := vp00110111001_0
private theorem bp001101110010 : Branch 0 (-1763761639/4000000 : ℚ) vp00110111001 := by
  apply branch_left_normalized (c:=vp001101110010) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-1763761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1763761639/2000000 : ℚ) by norm_num]
  exact coverp001101110010
private noncomputable def ep001101110011_0 : Blocks := edgeBlocks% "full/vectors/001101110011-E-0000.bin"
noncomputable def ep001101110011 : Blocks := ep001101110011_0
private theorem idp001101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110111001.list =
    C ((2:ℤ)^122) * horner X vp001101110011.list + horner X ep001101110011.list := by
  exact edge_identity (B := (2:ℤ)^256) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101110011 : Branch 1 (-1763761639/4000000 : ℚ) vp00110111001 := by
  apply branch_checked idp001101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1763761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1765761639/2000000 : ℚ) by norm_num]
  exact coverp001101110011
theorem coverp00110111001 : Covers (-1763761639/4000000 : ℚ) vp00110111001 := join_branches bp001101110010 bp001101110011
private noncomputable def vp001101110001_0 : Blocks := edgeBlocks% "full/vectors/001101110001-V-0000.bin"
noncomputable def vp001101110001 : Blocks := vp001101110001_0
theorem coverp001101110001 : Covers (-1761761639/2000000 : ℚ) vp001101110001 := cover_leaf (by decide +kernel)
private noncomputable def vp001101110000_0 : Blocks := edgeBlocks% "full/vectors/001101110000-V-0000.bin"
noncomputable def vp001101110000 : Blocks := vp001101110000_0
theorem coverp001101110000 : Covers (-1759761639/2000000 : ℚ) vp001101110000 := cover_leaf (by decide +kernel)
private noncomputable def vp00110111000_0 : Blocks := edgeBlocks% "full/vectors/00110111000-V-0000.bin"
noncomputable def vp00110111000 : Blocks := vp00110111000_0
private theorem bp001101110000 : Branch 0 (-1759761639/4000000 : ℚ) vp00110111000 := by
  apply branch_left_normalized (c:=vp001101110000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-1759761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1759761639/2000000 : ℚ) by norm_num]
  exact coverp001101110000
private noncomputable def ep001101110001_0 : Blocks := edgeBlocks% "full/vectors/001101110001-E-0000.bin"
noncomputable def ep001101110001 : Blocks := ep001101110001_0
private theorem idp001101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110111000.list =
    C ((2:ℤ)^122) * horner X vp001101110001.list + horner X ep001101110001.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101110001 : Branch 1 (-1759761639/4000000 : ℚ) vp00110111000 := by
  apply branch_checked idp001101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1759761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1761761639/2000000 : ℚ) by norm_num]
  exact coverp001101110001
theorem coverp00110111000 : Covers (-1759761639/4000000 : ℚ) vp00110111000 := join_branches bp001101110000 bp001101110001
private noncomputable def vp0011011100_0 : Blocks := edgeBlocks% "full/vectors/0011011100-V-0000.bin"
private noncomputable def vp0011011100_1 : Blocks := edgeBlocks% "full/vectors/0011011100-V-0001.bin"
noncomputable def vp0011011100 : Blocks := (Blocks.join vp0011011100_0 vp0011011100_1)
private theorem bp00110111000 : Branch 0 (-1759761639/8000000 : ℚ) vp0011011100 := by
  apply branch_left_normalized (c:=vp00110111000) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-1759761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1759761639/4000000 : ℚ) by norm_num]
  exact coverp00110111000
private noncomputable def ep00110111001_0 : Blocks := edgeBlocks% "full/vectors/00110111001-E-0000.bin"
private noncomputable def ep00110111001_1 : Blocks := edgeBlocks% "full/vectors/00110111001-E-0001.bin"
noncomputable def ep00110111001 : Blocks := (Blocks.join ep00110111001_0 ep00110111001_1)
private theorem idp00110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011011100.list =
    C ((2:ℤ)^226) * horner X vp00110111001.list + horner X ep00110111001.list := by
  exact edge_identity (B := (2:ℤ)^396) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110111001 : Branch 1 (-1759761639/8000000 : ℚ) vp0011011100 := by
  apply branch_checked idp00110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-1759761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1763761639/4000000 : ℚ) by norm_num]
  exact coverp00110111001
theorem coverp0011011100 : Covers (-1759761639/8000000 : ℚ) vp0011011100 := join_branches bp00110111000 bp00110111001
private noncomputable def vp001101110_0 : Blocks := edgeBlocks% "full/vectors/001101110-V-0000.bin"
private noncomputable def vp001101110_1 : Blocks := edgeBlocks% "full/vectors/001101110-V-0001.bin"
private noncomputable def vp001101110_2 : Blocks := edgeBlocks% "full/vectors/001101110-V-0002.bin"
private noncomputable def vp001101110_3 : Blocks := edgeBlocks% "full/vectors/001101110-V-0003.bin"
noncomputable def vp001101110 : Blocks := (Blocks.join (Blocks.join vp001101110_0 vp001101110_1) (Blocks.join vp001101110_2 vp001101110_3))
private theorem bp0011011100 : Branch 0 (-1759761639/16000000 : ℚ) vp001101110 := by
  apply branch_left_normalized (c:=vp0011011100) (k:=0) (m:=203) (by decide +kernel)
  rw [show 2*(-1759761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1759761639/8000000 : ℚ) by norm_num]
  exact coverp0011011100
private noncomputable def ep0011011101_0 : Blocks := edgeBlocks% "full/vectors/0011011101-E-0000.bin"
private noncomputable def ep0011011101_1 : Blocks := edgeBlocks% "full/vectors/0011011101-E-0001.bin"
private noncomputable def ep0011011101_2 : Blocks := edgeBlocks% "full/vectors/0011011101-E-0002.bin"
private noncomputable def ep0011011101_3 : Blocks := edgeBlocks% "full/vectors/0011011101-E-0003.bin"
noncomputable def ep0011011101 : Blocks := (Blocks.join (Blocks.join ep0011011101_0 ep0011011101_1) (Blocks.join ep0011011101_2 ep0011011101_3))
private theorem idp0011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101110.list =
    C ((2:ℤ)^431) * horner X vp0011011101.list + horner X ep0011011101.list := by
  exact edge_identity (B := (2:ℤ)^682) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011101 : Branch 1 (-1759761639/16000000 : ℚ) vp001101110 := by
  apply branch_checked idp0011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-1759761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1767761639/8000000 : ℚ) by norm_num]
  exact coverp0011011101
theorem coverp001101110 : Covers (-1759761639/16000000 : ℚ) vp001101110 := join_branches bp0011011100 bp0011011101
private noncomputable def vp00110111_0 : Blocks := edgeBlocks% "full/vectors/00110111-V-0000.bin"
private noncomputable def vp00110111_1 : Blocks := edgeBlocks% "full/vectors/00110111-V-0001.bin"
private noncomputable def vp00110111_2 : Blocks := edgeBlocks% "full/vectors/00110111-V-0002.bin"
private noncomputable def vp00110111_3 : Blocks := edgeBlocks% "full/vectors/00110111-V-0003.bin"
private noncomputable def vp00110111_4 : Blocks := edgeBlocks% "full/vectors/00110111-V-0004.bin"
private noncomputable def vp00110111_5 : Blocks := edgeBlocks% "full/vectors/00110111-V-0005.bin"
noncomputable def vp00110111 : Blocks := (Blocks.join (Blocks.join vp00110111_0 (Blocks.join vp00110111_1 vp00110111_2)) (Blocks.join vp00110111_3 (Blocks.join vp00110111_4 vp00110111_5)))
private theorem bp001101110 : Branch 0 (-1759761639/32000000 : ℚ) vp00110111 := by
  apply branch_left_normalized (c:=vp001101110) (k:=0) (m:=389) (by decide +kernel)
  rw [show 2*(-1759761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1759761639/16000000 : ℚ) by norm_num]
  exact coverp001101110
private noncomputable def ep001101111_0 : Blocks := edgeBlocks% "full/vectors/001101111-E-0000.bin"
private noncomputable def ep001101111_1 : Blocks := edgeBlocks% "full/vectors/001101111-E-0001.bin"
private noncomputable def ep001101111_2 : Blocks := edgeBlocks% "full/vectors/001101111-E-0002.bin"
private noncomputable def ep001101111_3 : Blocks := edgeBlocks% "full/vectors/001101111-E-0003.bin"
private noncomputable def ep001101111_4 : Blocks := edgeBlocks% "full/vectors/001101111-E-0004.bin"
private noncomputable def ep001101111_5 : Blocks := edgeBlocks% "full/vectors/001101111-E-0005.bin"
noncomputable def ep001101111 : Blocks := (Blocks.join (Blocks.join ep001101111_0 (Blocks.join ep001101111_1 ep001101111_2)) (Blocks.join ep001101111_3 (Blocks.join ep001101111_4 ep001101111_5)))
private theorem idp001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110111.list =
    C ((2:ℤ)^847) * horner X vp001101111.list + horner X ep001101111.list := by
  exact edge_identity (B := (2:ℤ)^1249) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101111 : Branch 1 (-1759761639/32000000 : ℚ) vp00110111 := by
  apply branch_checked idp001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1759761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1775761639/16000000 : ℚ) by norm_num]
  exact coverp001101111
theorem coverp00110111 : Covers (-1759761639/32000000 : ℚ) vp00110111 := join_branches bp001101110 bp001101111
private noncomputable def vp001101101111_0 : Blocks := edgeBlocks% "full/vectors/001101101111-V-0000.bin"
noncomputable def vp001101101111 : Blocks := vp001101101111_0
theorem coverp001101101111 : Covers (-1757761639/2000000 : ℚ) vp001101101111 := cover_leaf (by decide +kernel)
private noncomputable def vp001101101110_0 : Blocks := edgeBlocks% "full/vectors/001101101110-V-0000.bin"
noncomputable def vp001101101110 : Blocks := vp001101101110_0
theorem coverp001101101110 : Covers (-1755761639/2000000 : ℚ) vp001101101110 := cover_leaf (by decide +kernel)
private noncomputable def vp00110110111_0 : Blocks := edgeBlocks% "full/vectors/00110110111-V-0000.bin"
noncomputable def vp00110110111 : Blocks := vp00110110111_0
private theorem bp001101101110 : Branch 0 (-1755761639/4000000 : ℚ) vp00110110111 := by
  apply branch_left_normalized (c:=vp001101101110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-1755761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1755761639/2000000 : ℚ) by norm_num]
  exact coverp001101101110
private noncomputable def ep001101101111_0 : Blocks := edgeBlocks% "full/vectors/001101101111-E-0000.bin"
noncomputable def ep001101101111 : Blocks := ep001101101111_0
private theorem idp001101101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110110111.list =
    C ((2:ℤ)^122) * horner X vp001101101111.list + horner X ep001101101111.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101101111 : Branch 1 (-1755761639/4000000 : ℚ) vp00110110111 := by
  apply branch_checked idp001101101111 (by positivity) (by decide +kernel)
  rw [show 2*(-1755761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1757761639/2000000 : ℚ) by norm_num]
  exact coverp001101101111
theorem coverp00110110111 : Covers (-1755761639/4000000 : ℚ) vp00110110111 := join_branches bp001101101110 bp001101101111
private noncomputable def vp001101101101_0 : Blocks := edgeBlocks% "full/vectors/001101101101-V-0000.bin"
noncomputable def vp001101101101 : Blocks := vp001101101101_0
theorem coverp001101101101 : Covers (-1753761639/2000000 : ℚ) vp001101101101 := cover_leaf (by decide +kernel)
private noncomputable def vp001101101100_0 : Blocks := edgeBlocks% "full/vectors/001101101100-V-0000.bin"
noncomputable def vp001101101100 : Blocks := vp001101101100_0
theorem coverp001101101100 : Covers (-1751761639/2000000 : ℚ) vp001101101100 := cover_leaf (by decide +kernel)
private noncomputable def vp00110110110_0 : Blocks := edgeBlocks% "full/vectors/00110110110-V-0000.bin"
noncomputable def vp00110110110 : Blocks := vp00110110110_0
private theorem bp001101101100 : Branch 0 (-1751761639/4000000 : ℚ) vp00110110110 := by
  apply branch_left_normalized (c:=vp001101101100) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-1751761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1751761639/2000000 : ℚ) by norm_num]
  exact coverp001101101100
private noncomputable def ep001101101101_0 : Blocks := edgeBlocks% "full/vectors/001101101101-E-0000.bin"
noncomputable def ep001101101101 : Blocks := ep001101101101_0
private theorem idp001101101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110110110.list =
    C ((2:ℤ)^121) * horner X vp001101101101.list + horner X ep001101101101.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101101101 : Branch 1 (-1751761639/4000000 : ℚ) vp00110110110 := by
  apply branch_checked idp001101101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1751761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1753761639/2000000 : ℚ) by norm_num]
  exact coverp001101101101
theorem coverp00110110110 : Covers (-1751761639/4000000 : ℚ) vp00110110110 := join_branches bp001101101100 bp001101101101
private noncomputable def vp0011011011_0 : Blocks := edgeBlocks% "full/vectors/0011011011-V-0000.bin"
private noncomputable def vp0011011011_1 : Blocks := edgeBlocks% "full/vectors/0011011011-V-0001.bin"
noncomputable def vp0011011011 : Blocks := (Blocks.join vp0011011011_0 vp0011011011_1)
private theorem bp00110110110 : Branch 0 (-1751761639/8000000 : ℚ) vp0011011011 := by
  apply branch_left_normalized (c:=vp00110110110) (k:=0) (m:=109) (by decide +kernel)
  rw [show 2*(-1751761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1751761639/4000000 : ℚ) by norm_num]
  exact coverp00110110110
private noncomputable def ep00110110111_0 : Blocks := edgeBlocks% "full/vectors/00110110111-E-0000.bin"
private noncomputable def ep00110110111_1 : Blocks := edgeBlocks% "full/vectors/00110110111-E-0001.bin"
noncomputable def ep00110110111 : Blocks := (Blocks.join ep00110110111_0 ep00110110111_1)
private theorem idp00110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011011011.list =
    C ((2:ℤ)^226) * horner X vp00110110111.list + horner X ep00110110111.list := by
  exact edge_identity (B := (2:ℤ)^394) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110110111 : Branch 1 (-1751761639/8000000 : ℚ) vp0011011011 := by
  apply branch_checked idp00110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1751761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1755761639/4000000 : ℚ) by norm_num]
  exact coverp00110110111
theorem coverp0011011011 : Covers (-1751761639/8000000 : ℚ) vp0011011011 := join_branches bp00110110110 bp00110110111
private noncomputable def vp001101101011_0 : Blocks := edgeBlocks% "full/vectors/001101101011-V-0000.bin"
noncomputable def vp001101101011 : Blocks := vp001101101011_0
theorem coverp001101101011 : Covers (-1749761639/2000000 : ℚ) vp001101101011 := cover_leaf (by decide +kernel)
private noncomputable def vp001101101010_0 : Blocks := edgeBlocks% "full/vectors/001101101010-V-0000.bin"
noncomputable def vp001101101010 : Blocks := vp001101101010_0
theorem coverp001101101010 : Covers (-1747761639/2000000 : ℚ) vp001101101010 := cover_leaf (by decide +kernel)
private noncomputable def vp00110110101_0 : Blocks := edgeBlocks% "full/vectors/00110110101-V-0000.bin"
noncomputable def vp00110110101 : Blocks := vp00110110101_0
private theorem bp001101101010 : Branch 0 (-1747761639/4000000 : ℚ) vp00110110101 := by
  apply branch_left_normalized (c:=vp001101101010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-1747761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1747761639/2000000 : ℚ) by norm_num]
  exact coverp001101101010
private noncomputable def ep001101101011_0 : Blocks := edgeBlocks% "full/vectors/001101101011-E-0000.bin"
noncomputable def ep001101101011 : Blocks := ep001101101011_0
private theorem idp001101101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110110101.list =
    C ((2:ℤ)^121) * horner X vp001101101011.list + horner X ep001101101011.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101101011 : Branch 1 (-1747761639/4000000 : ℚ) vp00110110101 := by
  apply branch_checked idp001101101011 (by positivity) (by decide +kernel)
  rw [show 2*(-1747761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1749761639/2000000 : ℚ) by norm_num]
  exact coverp001101101011
theorem coverp00110110101 : Covers (-1747761639/4000000 : ℚ) vp00110110101 := join_branches bp001101101010 bp001101101011
private noncomputable def vp001101101001_0 : Blocks := edgeBlocks% "full/vectors/001101101001-V-0000.bin"
noncomputable def vp001101101001 : Blocks := vp001101101001_0
theorem coverp001101101001 : Covers (-1745761639/2000000 : ℚ) vp001101101001 := cover_leaf (by decide +kernel)
private noncomputable def vp001101101000_0 : Blocks := edgeBlocks% "full/vectors/001101101000-V-0000.bin"
noncomputable def vp001101101000 : Blocks := vp001101101000_0
theorem coverp001101101000 : Covers (-1743761639/2000000 : ℚ) vp001101101000 := cover_leaf (by decide +kernel)
private noncomputable def vp00110110100_0 : Blocks := edgeBlocks% "full/vectors/00110110100-V-0000.bin"
noncomputable def vp00110110100 : Blocks := vp00110110100_0
private theorem bp001101101000 : Branch 0 (-1743761639/4000000 : ℚ) vp00110110100 := by
  apply branch_left_normalized (c:=vp001101101000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-1743761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1743761639/2000000 : ℚ) by norm_num]
  exact coverp001101101000
private noncomputable def ep001101101001_0 : Blocks := edgeBlocks% "full/vectors/001101101001-E-0000.bin"
noncomputable def ep001101101001 : Blocks := ep001101101001_0
private theorem idp001101101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110110100.list =
    C ((2:ℤ)^123) * horner X vp001101101001.list + horner X ep001101101001.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101101001 : Branch 1 (-1743761639/4000000 : ℚ) vp00110110100 := by
  apply branch_checked idp001101101001 (by positivity) (by decide +kernel)
  rw [show 2*(-1743761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1745761639/2000000 : ℚ) by norm_num]
  exact coverp001101101001
theorem coverp00110110100 : Covers (-1743761639/4000000 : ℚ) vp00110110100 := join_branches bp001101101000 bp001101101001
private noncomputable def vp0011011010_0 : Blocks := edgeBlocks% "full/vectors/0011011010-V-0000.bin"
private noncomputable def vp0011011010_1 : Blocks := edgeBlocks% "full/vectors/0011011010-V-0001.bin"
noncomputable def vp0011011010 : Blocks := (Blocks.join vp0011011010_0 vp0011011010_1)
private theorem bp00110110100 : Branch 0 (-1743761639/8000000 : ℚ) vp0011011010 := by
  apply branch_left_normalized (c:=vp00110110100) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-1743761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1743761639/4000000 : ℚ) by norm_num]
  exact coverp00110110100
private noncomputable def ep00110110101_0 : Blocks := edgeBlocks% "full/vectors/00110110101-E-0000.bin"
private noncomputable def ep00110110101_1 : Blocks := edgeBlocks% "full/vectors/00110110101-E-0001.bin"
noncomputable def ep00110110101 : Blocks := (Blocks.join ep00110110101_0 ep00110110101_1)
private theorem idp00110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011011010.list =
    C ((2:ℤ)^229) * horner X vp00110110101.list + horner X ep00110110101.list := by
  exact edge_identity (B := (2:ℤ)^396) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110110101 : Branch 1 (-1743761639/8000000 : ℚ) vp0011011010 := by
  apply branch_checked idp00110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-1743761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1747761639/4000000 : ℚ) by norm_num]
  exact coverp00110110101
theorem coverp0011011010 : Covers (-1743761639/8000000 : ℚ) vp0011011010 := join_branches bp00110110100 bp00110110101
private noncomputable def vp001101101_0 : Blocks := edgeBlocks% "full/vectors/001101101-V-0000.bin"
private noncomputable def vp001101101_1 : Blocks := edgeBlocks% "full/vectors/001101101-V-0001.bin"
private noncomputable def vp001101101_2 : Blocks := edgeBlocks% "full/vectors/001101101-V-0002.bin"
private noncomputable def vp001101101_3 : Blocks := edgeBlocks% "full/vectors/001101101-V-0003.bin"
noncomputable def vp001101101 : Blocks := (Blocks.join (Blocks.join vp001101101_0 vp001101101_1) (Blocks.join vp001101101_2 vp001101101_3))
private theorem bp0011011010 : Branch 0 (-1743761639/16000000 : ℚ) vp001101101 := by
  apply branch_left_normalized (c:=vp0011011010) (k:=0) (m:=204) (by decide +kernel)
  rw [show 2*(-1743761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1743761639/8000000 : ℚ) by norm_num]
  exact coverp0011011010
private noncomputable def ep0011011011_0 : Blocks := edgeBlocks% "full/vectors/0011011011-E-0000.bin"
private noncomputable def ep0011011011_1 : Blocks := edgeBlocks% "full/vectors/0011011011-E-0001.bin"
private noncomputable def ep0011011011_2 : Blocks := edgeBlocks% "full/vectors/0011011011-E-0002.bin"
private noncomputable def ep0011011011_3 : Blocks := edgeBlocks% "full/vectors/0011011011-E-0003.bin"
noncomputable def ep0011011011 : Blocks := (Blocks.join (Blocks.join ep0011011011_0 ep0011011011_1) (Blocks.join ep0011011011_2 ep0011011011_3))
private theorem idp0011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101101.list =
    C ((2:ℤ)^439) * horner X vp0011011011.list + horner X ep0011011011.list := by
  exact edge_identity (B := (2:ℤ)^683) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011011 : Branch 1 (-1743761639/16000000 : ℚ) vp001101101 := by
  apply branch_checked idp0011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-1743761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1751761639/8000000 : ℚ) by norm_num]
  exact coverp0011011011
theorem coverp001101101 : Covers (-1743761639/16000000 : ℚ) vp001101101 := join_branches bp0011011010 bp0011011011
private noncomputable def vp001101100111_0 : Blocks := edgeBlocks% "full/vectors/001101100111-V-0000.bin"
noncomputable def vp001101100111 : Blocks := vp001101100111_0
theorem coverp001101100111 : Covers (-1741761639/2000000 : ℚ) vp001101100111 := cover_leaf (by decide +kernel)
private noncomputable def vp001101100110_0 : Blocks := edgeBlocks% "full/vectors/001101100110-V-0000.bin"
noncomputable def vp001101100110 : Blocks := vp001101100110_0
theorem coverp001101100110 : Covers (-1739761639/2000000 : ℚ) vp001101100110 := cover_leaf (by decide +kernel)
private noncomputable def vp00110110011_0 : Blocks := edgeBlocks% "full/vectors/00110110011-V-0000.bin"
noncomputable def vp00110110011 : Blocks := vp00110110011_0
private theorem bp001101100110 : Branch 0 (-1739761639/4000000 : ℚ) vp00110110011 := by
  apply branch_left_normalized (c:=vp001101100110) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-1739761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1739761639/2000000 : ℚ) by norm_num]
  exact coverp001101100110
private noncomputable def ep001101100111_0 : Blocks := edgeBlocks% "full/vectors/001101100111-E-0000.bin"
noncomputable def ep001101100111 : Blocks := ep001101100111_0
private theorem idp001101100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110110011.list =
    C ((2:ℤ)^123) * horner X vp001101100111.list + horner X ep001101100111.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101100111 : Branch 1 (-1739761639/4000000 : ℚ) vp00110110011 := by
  apply branch_checked idp001101100111 (by positivity) (by decide +kernel)
  rw [show 2*(-1739761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1741761639/2000000 : ℚ) by norm_num]
  exact coverp001101100111
theorem coverp00110110011 : Covers (-1739761639/4000000 : ℚ) vp00110110011 := join_branches bp001101100110 bp001101100111
private noncomputable def vp001101100101_0 : Blocks := edgeBlocks% "full/vectors/001101100101-V-0000.bin"
noncomputable def vp001101100101 : Blocks := vp001101100101_0
theorem coverp001101100101 : Covers (-1737761639/2000000 : ℚ) vp001101100101 := cover_leaf (by decide +kernel)
private noncomputable def vp001101100100_0 : Blocks := edgeBlocks% "full/vectors/001101100100-V-0000.bin"
noncomputable def vp001101100100 : Blocks := vp001101100100_0
theorem coverp001101100100 : Covers (-1735761639/2000000 : ℚ) vp001101100100 := cover_leaf (by decide +kernel)
private noncomputable def vp00110110010_0 : Blocks := edgeBlocks% "full/vectors/00110110010-V-0000.bin"
noncomputable def vp00110110010 : Blocks := vp00110110010_0
private theorem bp001101100100 : Branch 0 (-1735761639/4000000 : ℚ) vp00110110010 := by
  apply branch_left_normalized (c:=vp001101100100) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-1735761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1735761639/2000000 : ℚ) by norm_num]
  exact coverp001101100100
private noncomputable def ep001101100101_0 : Blocks := edgeBlocks% "full/vectors/001101100101-E-0000.bin"
noncomputable def ep001101100101 : Blocks := ep001101100101_0
private theorem idp001101100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110110010.list =
    C ((2:ℤ)^124) * horner X vp001101100101.list + horner X ep001101100101.list := by
  exact edge_identity (B := (2:ℤ)^255) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101100101 : Branch 1 (-1735761639/4000000 : ℚ) vp00110110010 := by
  apply branch_checked idp001101100101 (by positivity) (by decide +kernel)
  rw [show 2*(-1735761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1737761639/2000000 : ℚ) by norm_num]
  exact coverp001101100101
theorem coverp00110110010 : Covers (-1735761639/4000000 : ℚ) vp00110110010 := join_branches bp001101100100 bp001101100101
private noncomputable def vp0011011001_0 : Blocks := edgeBlocks% "full/vectors/0011011001-V-0000.bin"
private noncomputable def vp0011011001_1 : Blocks := edgeBlocks% "full/vectors/0011011001-V-0001.bin"
noncomputable def vp0011011001 : Blocks := (Blocks.join vp0011011001_0 vp0011011001_1)
private theorem bp00110110010 : Branch 0 (-1735761639/8000000 : ℚ) vp0011011001 := by
  apply branch_left_normalized (c:=vp00110110010) (k:=0) (m:=111) (by decide +kernel)
  rw [show 2*(-1735761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1735761639/4000000 : ℚ) by norm_num]
  exact coverp00110110010
private noncomputable def ep00110110011_0 : Blocks := edgeBlocks% "full/vectors/00110110011-E-0000.bin"
private noncomputable def ep00110110011_1 : Blocks := edgeBlocks% "full/vectors/00110110011-E-0001.bin"
noncomputable def ep00110110011 : Blocks := (Blocks.join ep00110110011_0 ep00110110011_1)
private theorem idp00110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011011001.list =
    C ((2:ℤ)^232) * horner X vp00110110011.list + horner X ep00110110011.list := by
  exact edge_identity (B := (2:ℤ)^400) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110110011 : Branch 1 (-1735761639/8000000 : ℚ) vp0011011001 := by
  apply branch_checked idp00110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-1735761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1739761639/4000000 : ℚ) by norm_num]
  exact coverp00110110011
theorem coverp0011011001 : Covers (-1735761639/8000000 : ℚ) vp0011011001 := join_branches bp00110110010 bp00110110011
private noncomputable def vp001101100011_0 : Blocks := edgeBlocks% "full/vectors/001101100011-V-0000.bin"
noncomputable def vp001101100011 : Blocks := vp001101100011_0
theorem coverp001101100011 : Covers (-1733761639/2000000 : ℚ) vp001101100011 := cover_leaf (by decide +kernel)
private noncomputable def vp001101100010_0 : Blocks := edgeBlocks% "full/vectors/001101100010-V-0000.bin"
noncomputable def vp001101100010 : Blocks := vp001101100010_0
theorem coverp001101100010 : Covers (-1731761639/2000000 : ℚ) vp001101100010 := cover_leaf (by decide +kernel)
private noncomputable def vp00110110001_0 : Blocks := edgeBlocks% "full/vectors/00110110001-V-0000.bin"
noncomputable def vp00110110001 : Blocks := vp00110110001_0
private theorem bp001101100010 : Branch 0 (-1731761639/4000000 : ℚ) vp00110110001 := by
  apply branch_left_normalized (c:=vp001101100010) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-1731761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1731761639/2000000 : ℚ) by norm_num]
  exact coverp001101100010
private noncomputable def ep001101100011_0 : Blocks := edgeBlocks% "full/vectors/001101100011-E-0000.bin"
noncomputable def ep001101100011 : Blocks := ep001101100011_0
private theorem idp001101100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110110001.list =
    C ((2:ℤ)^128) * horner X vp001101100011.list + horner X ep001101100011.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101100011 : Branch 1 (-1731761639/4000000 : ℚ) vp00110110001 := by
  apply branch_checked idp001101100011 (by positivity) (by decide +kernel)
  rw [show 2*(-1731761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1733761639/2000000 : ℚ) by norm_num]
  exact coverp001101100011
theorem coverp00110110001 : Covers (-1731761639/4000000 : ℚ) vp00110110001 := join_branches bp001101100010 bp001101100011
private noncomputable def vp001101100001_0 : Blocks := edgeBlocks% "full/vectors/001101100001-V-0000.bin"
noncomputable def vp001101100001 : Blocks := vp001101100001_0
theorem coverp001101100001 : Covers (-1729761639/2000000 : ℚ) vp001101100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011011000001_0 : Blocks := edgeBlocks% "full/vectors/0011011000001-V-0000.bin"
noncomputable def vp0011011000001 : Blocks := vp0011011000001_0
theorem coverp0011011000001 : Covers (-1728761639/1000000 : ℚ) vp0011011000001 := cover_leaf (by decide +kernel)
private noncomputable def vp0011011000000_0 : Blocks := edgeBlocks% "full/vectors/0011011000000-V-0000.bin"
noncomputable def vp0011011000000 : Blocks := vp0011011000000_0
theorem coverp0011011000000 : Covers (-1727761639/1000000 : ℚ) vp0011011000000 := cover_leaf (by decide +kernel)
private noncomputable def vp001101100000_0 : Blocks := edgeBlocks% "full/vectors/001101100000-V-0000.bin"
noncomputable def vp001101100000 : Blocks := vp001101100000_0
private theorem bp0011011000000 : Branch 0 (-1727761639/2000000 : ℚ) vp001101100000 := by
  apply branch_left_normalized (c:=vp0011011000000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-1727761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-1727761639/1000000 : ℚ) by norm_num]
  exact coverp0011011000000
private noncomputable def ep0011011000001_0 : Blocks := edgeBlocks% "full/vectors/0011011000001-E-0000.bin"
noncomputable def ep0011011000001 : Blocks := ep0011011000001_0
private theorem idp0011011000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101100000.list =
    C ((2:ℤ)^71) * horner X vp0011011000001.list + horner X ep0011011000001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011000001 : Branch 1 (-1727761639/2000000 : ℚ) vp001101100000 := by
  apply branch_checked idp0011011000001 (by positivity) (by decide +kernel)
  rw [show 2*(-1727761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-1728761639/1000000 : ℚ) by norm_num]
  exact coverp0011011000001
theorem coverp001101100000 : Covers (-1727761639/2000000 : ℚ) vp001101100000 := join_branches bp0011011000000 bp0011011000001
private noncomputable def vp00110110000_0 : Blocks := edgeBlocks% "full/vectors/00110110000-V-0000.bin"
noncomputable def vp00110110000 : Blocks := vp00110110000_0
private theorem bp001101100000 : Branch 0 (-1727761639/4000000 : ℚ) vp00110110000 := by
  apply branch_left_normalized (c:=vp001101100000) (k:=0) (m:=66) (by decide +kernel)
  rw [show 2*(-1727761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-1727761639/2000000 : ℚ) by norm_num]
  exact coverp001101100000
private noncomputable def ep001101100001_0 : Blocks := edgeBlocks% "full/vectors/001101100001-E-0000.bin"
noncomputable def ep001101100001 : Blocks := ep001101100001_0
private theorem idp001101100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110110000.list =
    C ((2:ℤ)^125) * horner X vp001101100001.list + horner X ep001101100001.list := by
  exact edge_identity (B := (2:ℤ)^264) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101100001 : Branch 1 (-1727761639/4000000 : ℚ) vp00110110000 := by
  apply branch_checked idp001101100001 (by positivity) (by decide +kernel)
  rw [show 2*(-1727761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-1729761639/2000000 : ℚ) by norm_num]
  exact coverp001101100001
theorem coverp00110110000 : Covers (-1727761639/4000000 : ℚ) vp00110110000 := join_branches bp001101100000 bp001101100001
private noncomputable def vp0011011000_0 : Blocks := edgeBlocks% "full/vectors/0011011000-V-0000.bin"
private noncomputable def vp0011011000_1 : Blocks := edgeBlocks% "full/vectors/0011011000-V-0001.bin"
noncomputable def vp0011011000 : Blocks := (Blocks.join vp0011011000_0 vp0011011000_1)
private theorem bp00110110000 : Branch 0 (-1727761639/8000000 : ℚ) vp0011011000 := by
  apply branch_left_normalized (c:=vp00110110000) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-1727761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-1727761639/4000000 : ℚ) by norm_num]
  exact coverp00110110000
private noncomputable def ep00110110001_0 : Blocks := edgeBlocks% "full/vectors/00110110001-E-0000.bin"
private noncomputable def ep00110110001_1 : Blocks := edgeBlocks% "full/vectors/00110110001-E-0001.bin"
noncomputable def ep00110110001 : Blocks := (Blocks.join ep00110110001_0 ep00110110001_1)
private theorem idp00110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011011000.list =
    C ((2:ℤ)^236) * horner X vp00110110001.list + horner X ep00110110001.list := by
  exact edge_identity (B := (2:ℤ)^410) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110110001 : Branch 1 (-1727761639/8000000 : ℚ) vp0011011000 := by
  apply branch_checked idp00110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-1727761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-1731761639/4000000 : ℚ) by norm_num]
  exact coverp00110110001
theorem coverp0011011000 : Covers (-1727761639/8000000 : ℚ) vp0011011000 := join_branches bp00110110000 bp00110110001
private noncomputable def vp001101100_0 : Blocks := edgeBlocks% "full/vectors/001101100-V-0000.bin"
private noncomputable def vp001101100_1 : Blocks := edgeBlocks% "full/vectors/001101100-V-0001.bin"
private noncomputable def vp001101100_2 : Blocks := edgeBlocks% "full/vectors/001101100-V-0002.bin"
private noncomputable def vp001101100_3 : Blocks := edgeBlocks% "full/vectors/001101100-V-0003.bin"
noncomputable def vp001101100 : Blocks := (Blocks.join (Blocks.join vp001101100_0 vp001101100_1) (Blocks.join vp001101100_2 vp001101100_3))
private theorem bp0011011000 : Branch 0 (-1727761639/16000000 : ℚ) vp001101100 := by
  apply branch_left_normalized (c:=vp0011011000) (k:=0) (m:=210) (by decide +kernel)
  rw [show 2*(-1727761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-1727761639/8000000 : ℚ) by norm_num]
  exact coverp0011011000
private noncomputable def ep0011011001_0 : Blocks := edgeBlocks% "full/vectors/0011011001-E-0000.bin"
private noncomputable def ep0011011001_1 : Blocks := edgeBlocks% "full/vectors/0011011001-E-0001.bin"
private noncomputable def ep0011011001_2 : Blocks := edgeBlocks% "full/vectors/0011011001-E-0002.bin"
private noncomputable def ep0011011001_3 : Blocks := edgeBlocks% "full/vectors/0011011001-E-0003.bin"
noncomputable def ep0011011001 : Blocks := (Blocks.join (Blocks.join ep0011011001_0 ep0011011001_1) (Blocks.join ep0011011001_2 ep0011011001_3))
private theorem idp0011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp001101100.list =
    C ((2:ℤ)^450) * horner X vp0011011001.list + horner X ep0011011001.list := by
  exact edge_identity (B := (2:ℤ)^698) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0011011001 : Branch 1 (-1727761639/16000000 : ℚ) vp001101100 := by
  apply branch_checked idp0011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-1727761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-1735761639/8000000 : ℚ) by norm_num]
  exact coverp0011011001
theorem coverp001101100 : Covers (-1727761639/16000000 : ℚ) vp001101100 := join_branches bp0011011000 bp0011011001
private noncomputable def vp00110110_0 : Blocks := edgeBlocks% "full/vectors/00110110-V-0000.bin"
private noncomputable def vp00110110_1 : Blocks := edgeBlocks% "full/vectors/00110110-V-0001.bin"
private noncomputable def vp00110110_2 : Blocks := edgeBlocks% "full/vectors/00110110-V-0002.bin"
private noncomputable def vp00110110_3 : Blocks := edgeBlocks% "full/vectors/00110110-V-0003.bin"
private noncomputable def vp00110110_4 : Blocks := edgeBlocks% "full/vectors/00110110-V-0004.bin"
private noncomputable def vp00110110_5 : Blocks := edgeBlocks% "full/vectors/00110110-V-0005.bin"
private noncomputable def vp00110110_6 : Blocks := edgeBlocks% "full/vectors/00110110-V-0006.bin"
noncomputable def vp00110110 : Blocks := (Blocks.join (Blocks.join vp00110110_0 (Blocks.join vp00110110_1 vp00110110_2)) (Blocks.join (Blocks.join vp00110110_3 vp00110110_4) (Blocks.join vp00110110_5 vp00110110_6)))
private theorem bp001101100 : Branch 0 (-1727761639/32000000 : ℚ) vp00110110 := by
  apply branch_left_normalized (c:=vp001101100) (k:=0) (m:=397) (by decide +kernel)
  rw [show 2*(-1727761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-1727761639/16000000 : ℚ) by norm_num]
  exact coverp001101100
private noncomputable def ep001101101_0 : Blocks := edgeBlocks% "full/vectors/001101101-E-0000.bin"
private noncomputable def ep001101101_1 : Blocks := edgeBlocks% "full/vectors/001101101-E-0001.bin"
private noncomputable def ep001101101_2 : Blocks := edgeBlocks% "full/vectors/001101101-E-0002.bin"
private noncomputable def ep001101101_3 : Blocks := edgeBlocks% "full/vectors/001101101-E-0003.bin"
private noncomputable def ep001101101_4 : Blocks := edgeBlocks% "full/vectors/001101101-E-0004.bin"
private noncomputable def ep001101101_5 : Blocks := edgeBlocks% "full/vectors/001101101-E-0005.bin"
private noncomputable def ep001101101_6 : Blocks := edgeBlocks% "full/vectors/001101101-E-0006.bin"
noncomputable def ep001101101 : Blocks := (Blocks.join (Blocks.join ep001101101_0 (Blocks.join ep001101101_1 ep001101101_2)) (Blocks.join (Blocks.join ep001101101_3 ep001101101_4) (Blocks.join ep001101101_5 ep001101101_6)))
private theorem idp001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00110110.list =
    C ((2:ℤ)^870) * horner X vp001101101.list + horner X ep001101101.list := by
  exact edge_identity (B := (2:ℤ)^1269) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp001101101 : Branch 1 (-1727761639/32000000 : ℚ) vp00110110 := by
  apply branch_checked idp001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-1727761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-1743761639/16000000 : ℚ) by norm_num]
  exact coverp001101101
theorem coverp00110110 : Covers (-1727761639/32000000 : ℚ) vp00110110 := join_branches bp001101100 bp001101101
private noncomputable def vp0011011_0 : Blocks := edgeBlocks% "full/vectors/0011011-V-0000.bin"
private noncomputable def vp0011011_1 : Blocks := edgeBlocks% "full/vectors/0011011-V-0001.bin"
private noncomputable def vp0011011_2 : Blocks := edgeBlocks% "full/vectors/0011011-V-0002.bin"
private noncomputable def vp0011011_3 : Blocks := edgeBlocks% "full/vectors/0011011-V-0003.bin"
private noncomputable def vp0011011_4 : Blocks := edgeBlocks% "full/vectors/0011011-V-0004.bin"
private noncomputable def vp0011011_5 : Blocks := edgeBlocks% "full/vectors/0011011-V-0005.bin"
private noncomputable def vp0011011_6 : Blocks := edgeBlocks% "full/vectors/0011011-V-0006.bin"
private noncomputable def vp0011011_7 : Blocks := edgeBlocks% "full/vectors/0011011-V-0007.bin"
private noncomputable def vp0011011_8 : Blocks := edgeBlocks% "full/vectors/0011011-V-0008.bin"
private noncomputable def vp0011011_9 : Blocks := edgeBlocks% "full/vectors/0011011-V-0009.bin"
private noncomputable def vp0011011_10 : Blocks := edgeBlocks% "full/vectors/0011011-V-0010.bin"
private noncomputable def vp0011011_11 : Blocks := edgeBlocks% "full/vectors/0011011-V-0011.bin"
noncomputable def vp0011011 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp0011011_0 (Blocks.join vp0011011_1 vp0011011_2)) (Blocks.join vp0011011_3 (Blocks.join vp0011011_4 vp0011011_5))) (Blocks.join (Blocks.join vp0011011_6 (Blocks.join vp0011011_7 vp0011011_8)) (Blocks.join vp0011011_9 (Blocks.join vp0011011_10 vp0011011_11))))
private theorem bp00110110 : Branch 0 (-1727761639/64000000 : ℚ) vp0011011 := by
  apply branch_left_normalized (c:=vp00110110) (k:=0) (m:=769) (by decide +kernel)
  rw [show 2*(-1727761639/64000000 : ℚ) - ((0:ℤ):ℚ) = (-1727761639/32000000 : ℚ) by norm_num]
  exact coverp00110110
private noncomputable def ep00110111_0 : Blocks := edgeBlocks% "full/vectors/00110111-E-0000.bin"
private noncomputable def ep00110111_1 : Blocks := edgeBlocks% "full/vectors/00110111-E-0001.bin"
private noncomputable def ep00110111_2 : Blocks := edgeBlocks% "full/vectors/00110111-E-0002.bin"
private noncomputable def ep00110111_3 : Blocks := edgeBlocks% "full/vectors/00110111-E-0003.bin"
private noncomputable def ep00110111_4 : Blocks := edgeBlocks% "full/vectors/00110111-E-0004.bin"
private noncomputable def ep00110111_5 : Blocks := edgeBlocks% "full/vectors/00110111-E-0005.bin"
private noncomputable def ep00110111_6 : Blocks := edgeBlocks% "full/vectors/00110111-E-0006.bin"
private noncomputable def ep00110111_7 : Blocks := edgeBlocks% "full/vectors/00110111-E-0007.bin"
private noncomputable def ep00110111_8 : Blocks := edgeBlocks% "full/vectors/00110111-E-0008.bin"
private noncomputable def ep00110111_9 : Blocks := edgeBlocks% "full/vectors/00110111-E-0009.bin"
private noncomputable def ep00110111_10 : Blocks := edgeBlocks% "full/vectors/00110111-E-0010.bin"
private noncomputable def ep00110111_11 : Blocks := edgeBlocks% "full/vectors/00110111-E-0011.bin"
noncomputable def ep00110111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep00110111_0 (Blocks.join ep00110111_1 ep00110111_2)) (Blocks.join ep00110111_3 (Blocks.join ep00110111_4 ep00110111_5))) (Blocks.join (Blocks.join ep00110111_6 (Blocks.join ep00110111_7 ep00110111_8)) (Blocks.join ep00110111_9 (Blocks.join ep00110111_10 ep00110111_11))))
private theorem idp00110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0011011.list =
    C ((2:ℤ)^1693) * horner X vp00110111.list + horner X ep00110111.list := by
  exact edge_identity (B := (2:ℤ)^2398) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00110111 : Branch 1 (-1727761639/64000000 : ℚ) vp0011011 := by
  apply branch_checked idp00110111 (by positivity) (by decide +kernel)
  rw [show 2*(-1727761639/64000000 : ℚ) - ((1:ℤ):ℚ) = (-1759761639/32000000 : ℚ) by norm_num]
  exact coverp00110111
theorem coverp0011011 : Covers (-1727761639/64000000 : ℚ) vp0011011 := join_branches bp00110110 bp00110111
end NextProof.EdgeFull

