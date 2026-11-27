import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00010111111111_0 : Blocks := edgeBlocks% "full/vectors/00010111111111-V-0000.bin"
noncomputable def vp00010111111111 : Blocks := vp00010111111111_0
theorem coverp00010111111111 : Covers (-767261639/500000 : ℚ) vp00010111111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00010111111110_0 : Blocks := edgeBlocks% "full/vectors/00010111111110-V-0000.bin"
noncomputable def vp00010111111110 : Blocks := vp00010111111110_0
theorem coverp00010111111110 : Covers (-766761639/500000 : ℚ) vp00010111111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011111111_0 : Blocks := edgeBlocks% "full/vectors/0001011111111-V-0000.bin"
noncomputable def vp0001011111111 : Blocks := vp0001011111111_0
private theorem bp00010111111110 : Branch 0 (-766761639/1000000 : ℚ) vp0001011111111 := by
  apply branch_left_normalized (c:=vp00010111111110) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-766761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-766761639/500000 : ℚ) by norm_num]
  exact coverp00010111111110
private noncomputable def ep00010111111111_0 : Blocks := edgeBlocks% "full/vectors/00010111111111-E-0000.bin"
noncomputable def ep00010111111111 : Blocks := ep00010111111111_0
private theorem idp00010111111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011111111.list =
    C ((2:ℤ)^56) * horner X vp00010111111111.list + horner X ep00010111111111.list := by
  exact edge_identity (B := (2:ℤ)^173) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010111111111 : Branch 1 (-766761639/1000000 : ℚ) vp0001011111111 := by
  apply branch_checked idp00010111111111 (by positivity) (by decide +kernel)
  rw [show 2*(-766761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-767261639/500000 : ℚ) by norm_num]
  exact coverp00010111111111
theorem coverp0001011111111 : Covers (-766761639/1000000 : ℚ) vp0001011111111 := join_branches bp00010111111110 bp00010111111111
private noncomputable def vp0001011111110_0 : Blocks := edgeBlocks% "full/vectors/0001011111110-V-0000.bin"
noncomputable def vp0001011111110 : Blocks := vp0001011111110_0
theorem coverp0001011111110 : Covers (-765761639/1000000 : ℚ) vp0001011111110 := cover_leaf (by decide +kernel)
private noncomputable def vp000101111111_0 : Blocks := edgeBlocks% "full/vectors/000101111111-V-0000.bin"
noncomputable def vp000101111111 : Blocks := vp000101111111_0
private theorem bp0001011111110 : Branch 0 (-765761639/2000000 : ℚ) vp000101111111 := by
  apply branch_left_normalized (c:=vp0001011111110) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-765761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-765761639/1000000 : ℚ) by norm_num]
  exact coverp0001011111110
private noncomputable def ep0001011111111_0 : Blocks := edgeBlocks% "full/vectors/0001011111111-E-0000.bin"
noncomputable def ep0001011111111 : Blocks := ep0001011111111_0
private theorem idp0001011111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101111111.list =
    C ((2:ℤ)^97) * horner X vp0001011111111.list + horner X ep0001011111111.list := by
  exact edge_identity (B := (2:ℤ)^229) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011111111 : Branch 1 (-765761639/2000000 : ℚ) vp000101111111 := by
  apply branch_checked idp0001011111111 (by positivity) (by decide +kernel)
  rw [show 2*(-765761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-766761639/1000000 : ℚ) by norm_num]
  exact coverp0001011111111
theorem coverp000101111111 : Covers (-765761639/2000000 : ℚ) vp000101111111 := join_branches bp0001011111110 bp0001011111111
private noncomputable def vp0001011111101_0 : Blocks := edgeBlocks% "full/vectors/0001011111101-V-0000.bin"
noncomputable def vp0001011111101 : Blocks := vp0001011111101_0
theorem coverp0001011111101 : Covers (-764761639/1000000 : ℚ) vp0001011111101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011111100_0 : Blocks := edgeBlocks% "full/vectors/0001011111100-V-0000.bin"
noncomputable def vp0001011111100 : Blocks := vp0001011111100_0
theorem coverp0001011111100 : Covers (-763761639/1000000 : ℚ) vp0001011111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000101111110_0 : Blocks := edgeBlocks% "full/vectors/000101111110-V-0000.bin"
noncomputable def vp000101111110 : Blocks := vp000101111110_0
private theorem bp0001011111100 : Branch 0 (-763761639/2000000 : ℚ) vp000101111110 := by
  apply branch_left_normalized (c:=vp0001011111100) (k:=0) (m:=54) (by decide +kernel)
  rw [show 2*(-763761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-763761639/1000000 : ℚ) by norm_num]
  exact coverp0001011111100
private noncomputable def ep0001011111101_0 : Blocks := edgeBlocks% "full/vectors/0001011111101-E-0000.bin"
noncomputable def ep0001011111101 : Blocks := ep0001011111101_0
private theorem idp0001011111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101111110.list =
    C ((2:ℤ)^97) * horner X vp0001011111101.list + horner X ep0001011111101.list := by
  exact edge_identity (B := (2:ℤ)^228) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011111101 : Branch 1 (-763761639/2000000 : ℚ) vp000101111110 := by
  apply branch_checked idp0001011111101 (by positivity) (by decide +kernel)
  rw [show 2*(-763761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-764761639/1000000 : ℚ) by norm_num]
  exact coverp0001011111101
theorem coverp000101111110 : Covers (-763761639/2000000 : ℚ) vp000101111110 := join_branches bp0001011111100 bp0001011111101
private noncomputable def vp00010111111_0 : Blocks := edgeBlocks% "full/vectors/00010111111-V-0000.bin"
private noncomputable def vp00010111111_1 : Blocks := edgeBlocks% "full/vectors/00010111111-V-0001.bin"
noncomputable def vp00010111111 : Blocks := (Blocks.join vp00010111111_0 vp00010111111_1)
private theorem bp000101111110 : Branch 0 (-763761639/4000000 : ℚ) vp00010111111 := by
  apply branch_left_normalized (c:=vp000101111110) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-763761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-763761639/2000000 : ℚ) by norm_num]
  exact coverp000101111110
private noncomputable def ep000101111111_0 : Blocks := edgeBlocks% "full/vectors/000101111111-E-0000.bin"
private noncomputable def ep000101111111_1 : Blocks := edgeBlocks% "full/vectors/000101111111-E-0001.bin"
noncomputable def ep000101111111 : Blocks := (Blocks.join ep000101111111_0 ep000101111111_1)
private theorem idp000101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010111111.list =
    C ((2:ℤ)^175) * horner X vp000101111111.list + horner X ep000101111111.list := by
  exact edge_identity (B := (2:ℤ)^338) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101111111 : Branch 1 (-763761639/4000000 : ℚ) vp00010111111 := by
  apply branch_checked idp000101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-763761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-765761639/2000000 : ℚ) by norm_num]
  exact coverp000101111111
theorem coverp00010111111 : Covers (-763761639/4000000 : ℚ) vp00010111111 := join_branches bp000101111110 bp000101111111
private noncomputable def vp0001011111011_0 : Blocks := edgeBlocks% "full/vectors/0001011111011-V-0000.bin"
noncomputable def vp0001011111011 : Blocks := vp0001011111011_0
theorem coverp0001011111011 : Covers (-762761639/1000000 : ℚ) vp0001011111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010111110101_0 : Blocks := edgeBlocks% "full/vectors/00010111110101-V-0000.bin"
noncomputable def vp00010111110101 : Blocks := vp00010111110101_0
theorem coverp00010111110101 : Covers (-762261639/500000 : ℚ) vp00010111110101 := cover_leaf (by decide +kernel)
private noncomputable def vp00010111110100_0 : Blocks := edgeBlocks% "full/vectors/00010111110100-V-0000.bin"
noncomputable def vp00010111110100 : Blocks := vp00010111110100_0
theorem coverp00010111110100 : Covers (-761761639/500000 : ℚ) vp00010111110100 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011111010_0 : Blocks := edgeBlocks% "full/vectors/0001011111010-V-0000.bin"
noncomputable def vp0001011111010 : Blocks := vp0001011111010_0
private theorem bp00010111110100 : Branch 0 (-761761639/1000000 : ℚ) vp0001011111010 := by
  apply branch_left_normalized (c:=vp00010111110100) (k:=0) (m:=35) (by decide +kernel)
  rw [show 2*(-761761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-761761639/500000 : ℚ) by norm_num]
  exact coverp00010111110100
private noncomputable def ep00010111110101_0 : Blocks := edgeBlocks% "full/vectors/00010111110101-E-0000.bin"
noncomputable def ep00010111110101 : Blocks := ep00010111110101_0
private theorem idp00010111110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011111010.list =
    C ((2:ℤ)^58) * horner X vp00010111110101.list + horner X ep00010111110101.list := by
  exact edge_identity (B := (2:ℤ)^176) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010111110101 : Branch 1 (-761761639/1000000 : ℚ) vp0001011111010 := by
  apply branch_checked idp00010111110101 (by positivity) (by decide +kernel)
  rw [show 2*(-761761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-762261639/500000 : ℚ) by norm_num]
  exact coverp00010111110101
theorem coverp0001011111010 : Covers (-761761639/1000000 : ℚ) vp0001011111010 := join_branches bp00010111110100 bp00010111110101
private noncomputable def vp000101111101_0 : Blocks := edgeBlocks% "full/vectors/000101111101-V-0000.bin"
noncomputable def vp000101111101 : Blocks := vp000101111101_0
private theorem bp0001011111010 : Branch 0 (-761761639/2000000 : ℚ) vp000101111101 := by
  apply branch_left_normalized (c:=vp0001011111010) (k:=0) (m:=55) (by decide +kernel)
  rw [show 2*(-761761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-761761639/1000000 : ℚ) by norm_num]
  exact coverp0001011111010
private noncomputable def ep0001011111011_0 : Blocks := edgeBlocks% "full/vectors/0001011111011-E-0000.bin"
noncomputable def ep0001011111011 : Blocks := ep0001011111011_0
private theorem idp0001011111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101111101.list =
    C ((2:ℤ)^99) * horner X vp0001011111011.list + horner X ep0001011111011.list := by
  exact edge_identity (B := (2:ℤ)^232) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011111011 : Branch 1 (-761761639/2000000 : ℚ) vp000101111101 := by
  apply branch_checked idp0001011111011 (by positivity) (by decide +kernel)
  rw [show 2*(-761761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-762761639/1000000 : ℚ) by norm_num]
  exact coverp0001011111011
theorem coverp000101111101 : Covers (-761761639/2000000 : ℚ) vp000101111101 := join_branches bp0001011111010 bp0001011111011
private noncomputable def vp00010111110011_0 : Blocks := edgeBlocks% "full/vectors/00010111110011-V-0000.bin"
noncomputable def vp00010111110011 : Blocks := vp00010111110011_0
theorem coverp00010111110011 : Covers (-761261639/500000 : ℚ) vp00010111110011 := cover_leaf (by decide +kernel)
private noncomputable def vp00010111110010_0 : Blocks := edgeBlocks% "full/vectors/00010111110010-V-0000.bin"
noncomputable def vp00010111110010 : Blocks := vp00010111110010_0
theorem coverp00010111110010 : Covers (-760761639/500000 : ℚ) vp00010111110010 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011111001_0 : Blocks := edgeBlocks% "full/vectors/0001011111001-V-0000.bin"
noncomputable def vp0001011111001 : Blocks := vp0001011111001_0
private theorem bp00010111110010 : Branch 0 (-760761639/1000000 : ℚ) vp0001011111001 := by
  apply branch_left_normalized (c:=vp00010111110010) (k:=0) (m:=34) (by decide +kernel)
  rw [show 2*(-760761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-760761639/500000 : ℚ) by norm_num]
  exact coverp00010111110010
private noncomputable def ep00010111110011_0 : Blocks := edgeBlocks% "full/vectors/00010111110011-E-0000.bin"
noncomputable def ep00010111110011 : Blocks := ep00010111110011_0
private theorem idp00010111110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011111001.list =
    C ((2:ℤ)^56) * horner X vp00010111110011.list + horner X ep00010111110011.list := by
  exact edge_identity (B := (2:ℤ)^172) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010111110011 : Branch 1 (-760761639/1000000 : ℚ) vp0001011111001 := by
  apply branch_checked idp00010111110011 (by positivity) (by decide +kernel)
  rw [show 2*(-760761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-761261639/500000 : ℚ) by norm_num]
  exact coverp00010111110011
theorem coverp0001011111001 : Covers (-760761639/1000000 : ℚ) vp0001011111001 := join_branches bp00010111110010 bp00010111110011
private noncomputable def vp0001011111000_0 : Blocks := edgeBlocks% "full/vectors/0001011111000-V-0000.bin"
noncomputable def vp0001011111000 : Blocks := vp0001011111000_0
theorem coverp0001011111000 : Covers (-759761639/1000000 : ℚ) vp0001011111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000101111100_0 : Blocks := edgeBlocks% "full/vectors/000101111100-V-0000.bin"
noncomputable def vp000101111100 : Blocks := vp000101111100_0
private theorem bp0001011111000 : Branch 0 (-759761639/2000000 : ℚ) vp000101111100 := by
  apply branch_left_normalized (c:=vp0001011111000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-759761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-759761639/1000000 : ℚ) by norm_num]
  exact coverp0001011111000
private noncomputable def ep0001011111001_0 : Blocks := edgeBlocks% "full/vectors/0001011111001-E-0000.bin"
noncomputable def ep0001011111001 : Blocks := ep0001011111001_0
private theorem idp0001011111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101111100.list =
    C ((2:ℤ)^95) * horner X vp0001011111001.list + horner X ep0001011111001.list := by
  exact edge_identity (B := (2:ℤ)^225) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011111001 : Branch 1 (-759761639/2000000 : ℚ) vp000101111100 := by
  apply branch_checked idp0001011111001 (by positivity) (by decide +kernel)
  rw [show 2*(-759761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-760761639/1000000 : ℚ) by norm_num]
  exact coverp0001011111001
theorem coverp000101111100 : Covers (-759761639/2000000 : ℚ) vp000101111100 := join_branches bp0001011111000 bp0001011111001
private noncomputable def vp00010111110_0 : Blocks := edgeBlocks% "full/vectors/00010111110-V-0000.bin"
private noncomputable def vp00010111110_1 : Blocks := edgeBlocks% "full/vectors/00010111110-V-0001.bin"
noncomputable def vp00010111110 : Blocks := (Blocks.join vp00010111110_0 vp00010111110_1)
private theorem bp000101111100 : Branch 0 (-759761639/4000000 : ℚ) vp00010111110 := by
  apply branch_left_normalized (c:=vp000101111100) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-759761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-759761639/2000000 : ℚ) by norm_num]
  exact coverp000101111100
private noncomputable def ep000101111101_0 : Blocks := edgeBlocks% "full/vectors/000101111101-E-0000.bin"
private noncomputable def ep000101111101_1 : Blocks := edgeBlocks% "full/vectors/000101111101-E-0001.bin"
noncomputable def ep000101111101 : Blocks := (Blocks.join ep000101111101_0 ep000101111101_1)
private theorem idp000101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010111110.list =
    C ((2:ℤ)^170) * horner X vp000101111101.list + horner X ep000101111101.list := by
  exact edge_identity (B := (2:ℤ)^335) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101111101 : Branch 1 (-759761639/4000000 : ℚ) vp00010111110 := by
  apply branch_checked idp000101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-759761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-761761639/2000000 : ℚ) by norm_num]
  exact coverp000101111101
theorem coverp00010111110 : Covers (-759761639/4000000 : ℚ) vp00010111110 := join_branches bp000101111100 bp000101111101
private noncomputable def vp0001011111_0 : Blocks := edgeBlocks% "full/vectors/0001011111-V-0000.bin"
private noncomputable def vp0001011111_1 : Blocks := edgeBlocks% "full/vectors/0001011111-V-0001.bin"
private noncomputable def vp0001011111_2 : Blocks := edgeBlocks% "full/vectors/0001011111-V-0002.bin"
noncomputable def vp0001011111 : Blocks := (Blocks.join vp0001011111_0 (Blocks.join vp0001011111_1 vp0001011111_2))
private theorem bp00010111110 : Branch 0 (-759761639/8000000 : ℚ) vp0001011111 := by
  apply branch_left_normalized (c:=vp00010111110) (k:=0) (m:=162) (by decide +kernel)
  rw [show 2*(-759761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-759761639/4000000 : ℚ) by norm_num]
  exact coverp00010111110
private noncomputable def ep00010111111_0 : Blocks := edgeBlocks% "full/vectors/00010111111-E-0000.bin"
private noncomputable def ep00010111111_1 : Blocks := edgeBlocks% "full/vectors/00010111111-E-0001.bin"
private noncomputable def ep00010111111_2 : Blocks := edgeBlocks% "full/vectors/00010111111-E-0002.bin"
noncomputable def ep00010111111 : Blocks := (Blocks.join ep00010111111_0 (Blocks.join ep00010111111_1 ep00010111111_2))
private theorem idp00010111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011111.list =
    C ((2:ℤ)^325) * horner X vp00010111111.list + horner X ep00010111111.list := by
  exact edge_identity (B := (2:ℤ)^553) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010111111 : Branch 1 (-759761639/8000000 : ℚ) vp0001011111 := by
  apply branch_checked idp00010111111 (by positivity) (by decide +kernel)
  rw [show 2*(-759761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-763761639/4000000 : ℚ) by norm_num]
  exact coverp00010111111
theorem coverp0001011111 : Covers (-759761639/8000000 : ℚ) vp0001011111 := join_branches bp00010111110 bp00010111111
private noncomputable def vp0001011110111_0 : Blocks := edgeBlocks% "full/vectors/0001011110111-V-0000.bin"
noncomputable def vp0001011110111 : Blocks := vp0001011110111_0
theorem coverp0001011110111 : Covers (-758761639/1000000 : ℚ) vp0001011110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011110110_0 : Blocks := edgeBlocks% "full/vectors/0001011110110-V-0000.bin"
noncomputable def vp0001011110110 : Blocks := vp0001011110110_0
theorem coverp0001011110110 : Covers (-757761639/1000000 : ℚ) vp0001011110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000101111011_0 : Blocks := edgeBlocks% "full/vectors/000101111011-V-0000.bin"
noncomputable def vp000101111011 : Blocks := vp000101111011_0
private theorem bp0001011110110 : Branch 0 (-757761639/2000000 : ℚ) vp000101111011 := by
  apply branch_left_normalized (c:=vp0001011110110) (k:=0) (m:=52) (by decide +kernel)
  rw [show 2*(-757761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-757761639/1000000 : ℚ) by norm_num]
  exact coverp0001011110110
private noncomputable def ep0001011110111_0 : Blocks := edgeBlocks% "full/vectors/0001011110111-E-0000.bin"
noncomputable def ep0001011110111 : Blocks := ep0001011110111_0
private theorem idp0001011110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101111011.list =
    C ((2:ℤ)^94) * horner X vp0001011110111.list + horner X ep0001011110111.list := by
  exact edge_identity (B := (2:ℤ)^221) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011110111 : Branch 1 (-757761639/2000000 : ℚ) vp000101111011 := by
  apply branch_checked idp0001011110111 (by positivity) (by decide +kernel)
  rw [show 2*(-757761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-758761639/1000000 : ℚ) by norm_num]
  exact coverp0001011110111
theorem coverp000101111011 : Covers (-757761639/2000000 : ℚ) vp000101111011 := join_branches bp0001011110110 bp0001011110111
private noncomputable def vp0001011110101_0 : Blocks := edgeBlocks% "full/vectors/0001011110101-V-0000.bin"
noncomputable def vp0001011110101 : Blocks := vp0001011110101_0
theorem coverp0001011110101 : Covers (-756761639/1000000 : ℚ) vp0001011110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011110100_0 : Blocks := edgeBlocks% "full/vectors/0001011110100-V-0000.bin"
noncomputable def vp0001011110100 : Blocks := vp0001011110100_0
theorem coverp0001011110100 : Covers (-755761639/1000000 : ℚ) vp0001011110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000101111010_0 : Blocks := edgeBlocks% "full/vectors/000101111010-V-0000.bin"
noncomputable def vp000101111010 : Blocks := vp000101111010_0
private theorem bp0001011110100 : Branch 0 (-755761639/2000000 : ℚ) vp000101111010 := by
  apply branch_left_normalized (c:=vp0001011110100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-755761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-755761639/1000000 : ℚ) by norm_num]
  exact coverp0001011110100
private noncomputable def ep0001011110101_0 : Blocks := edgeBlocks% "full/vectors/0001011110101-E-0000.bin"
noncomputable def ep0001011110101 : Blocks := ep0001011110101_0
private theorem idp0001011110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101111010.list =
    C ((2:ℤ)^93) * horner X vp0001011110101.list + horner X ep0001011110101.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011110101 : Branch 1 (-755761639/2000000 : ℚ) vp000101111010 := by
  apply branch_checked idp0001011110101 (by positivity) (by decide +kernel)
  rw [show 2*(-755761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-756761639/1000000 : ℚ) by norm_num]
  exact coverp0001011110101
theorem coverp000101111010 : Covers (-755761639/2000000 : ℚ) vp000101111010 := join_branches bp0001011110100 bp0001011110101
private noncomputable def vp00010111101_0 : Blocks := edgeBlocks% "full/vectors/00010111101-V-0000.bin"
private noncomputable def vp00010111101_1 : Blocks := edgeBlocks% "full/vectors/00010111101-V-0001.bin"
noncomputable def vp00010111101 : Blocks := (Blocks.join vp00010111101_0 vp00010111101_1)
private theorem bp000101111010 : Branch 0 (-755761639/4000000 : ℚ) vp00010111101 := by
  apply branch_left_normalized (c:=vp000101111010) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-755761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-755761639/2000000 : ℚ) by norm_num]
  exact coverp000101111010
private noncomputable def ep000101111011_0 : Blocks := edgeBlocks% "full/vectors/000101111011-E-0000.bin"
private noncomputable def ep000101111011_1 : Blocks := edgeBlocks% "full/vectors/000101111011-E-0001.bin"
noncomputable def ep000101111011 : Blocks := (Blocks.join ep000101111011_0 ep000101111011_1)
private theorem idp000101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010111101.list =
    C ((2:ℤ)^170) * horner X vp000101111011.list + horner X ep000101111011.list := by
  exact edge_identity (B := (2:ℤ)^328) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101111011 : Branch 1 (-755761639/4000000 : ℚ) vp00010111101 := by
  apply branch_checked idp000101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-755761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-757761639/2000000 : ℚ) by norm_num]
  exact coverp000101111011
theorem coverp00010111101 : Covers (-755761639/4000000 : ℚ) vp00010111101 := join_branches bp000101111010 bp000101111011
private noncomputable def vp0001011110011_0 : Blocks := edgeBlocks% "full/vectors/0001011110011-V-0000.bin"
noncomputable def vp0001011110011 : Blocks := vp0001011110011_0
theorem coverp0001011110011 : Covers (-754761639/1000000 : ℚ) vp0001011110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011110010_0 : Blocks := edgeBlocks% "full/vectors/0001011110010-V-0000.bin"
noncomputable def vp0001011110010 : Blocks := vp0001011110010_0
theorem coverp0001011110010 : Covers (-753761639/1000000 : ℚ) vp0001011110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000101111001_0 : Blocks := edgeBlocks% "full/vectors/000101111001-V-0000.bin"
noncomputable def vp000101111001 : Blocks := vp000101111001_0
private theorem bp0001011110010 : Branch 0 (-753761639/2000000 : ℚ) vp000101111001 := by
  apply branch_left_normalized (c:=vp0001011110010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-753761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-753761639/1000000 : ℚ) by norm_num]
  exact coverp0001011110010
private noncomputable def ep0001011110011_0 : Blocks := edgeBlocks% "full/vectors/0001011110011-E-0000.bin"
noncomputable def ep0001011110011 : Blocks := ep0001011110011_0
private theorem idp0001011110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101111001.list =
    C ((2:ℤ)^94) * horner X vp0001011110011.list + horner X ep0001011110011.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011110011 : Branch 1 (-753761639/2000000 : ℚ) vp000101111001 := by
  apply branch_checked idp0001011110011 (by positivity) (by decide +kernel)
  rw [show 2*(-753761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-754761639/1000000 : ℚ) by norm_num]
  exact coverp0001011110011
theorem coverp000101111001 : Covers (-753761639/2000000 : ℚ) vp000101111001 := join_branches bp0001011110010 bp0001011110011
private noncomputable def vp0001011110001_0 : Blocks := edgeBlocks% "full/vectors/0001011110001-V-0000.bin"
noncomputable def vp0001011110001 : Blocks := vp0001011110001_0
theorem coverp0001011110001 : Covers (-752761639/1000000 : ℚ) vp0001011110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011110000_0 : Blocks := edgeBlocks% "full/vectors/0001011110000-V-0000.bin"
noncomputable def vp0001011110000 : Blocks := vp0001011110000_0
theorem coverp0001011110000 : Covers (-751761639/1000000 : ℚ) vp0001011110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000101111000_0 : Blocks := edgeBlocks% "full/vectors/000101111000-V-0000.bin"
noncomputable def vp000101111000 : Blocks := vp000101111000_0
private theorem bp0001011110000 : Branch 0 (-751761639/2000000 : ℚ) vp000101111000 := by
  apply branch_left_normalized (c:=vp0001011110000) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-751761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-751761639/1000000 : ℚ) by norm_num]
  exact coverp0001011110000
private noncomputable def ep0001011110001_0 : Blocks := edgeBlocks% "full/vectors/0001011110001-E-0000.bin"
noncomputable def ep0001011110001 : Blocks := ep0001011110001_0
private theorem idp0001011110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101111000.list =
    C ((2:ℤ)^93) * horner X vp0001011110001.list + horner X ep0001011110001.list := by
  exact edge_identity (B := (2:ℤ)^216) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011110001 : Branch 1 (-751761639/2000000 : ℚ) vp000101111000 := by
  apply branch_checked idp0001011110001 (by positivity) (by decide +kernel)
  rw [show 2*(-751761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-752761639/1000000 : ℚ) by norm_num]
  exact coverp0001011110001
theorem coverp000101111000 : Covers (-751761639/2000000 : ℚ) vp000101111000 := join_branches bp0001011110000 bp0001011110001
private noncomputable def vp00010111100_0 : Blocks := edgeBlocks% "full/vectors/00010111100-V-0000.bin"
private noncomputable def vp00010111100_1 : Blocks := edgeBlocks% "full/vectors/00010111100-V-0001.bin"
noncomputable def vp00010111100 : Blocks := (Blocks.join vp00010111100_0 vp00010111100_1)
private theorem bp000101111000 : Branch 0 (-751761639/4000000 : ℚ) vp00010111100 := by
  apply branch_left_normalized (c:=vp000101111000) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-751761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-751761639/2000000 : ℚ) by norm_num]
  exact coverp000101111000
private noncomputable def ep000101111001_0 : Blocks := edgeBlocks% "full/vectors/000101111001-E-0000.bin"
private noncomputable def ep000101111001_1 : Blocks := edgeBlocks% "full/vectors/000101111001-E-0001.bin"
noncomputable def ep000101111001 : Blocks := (Blocks.join ep000101111001_0 ep000101111001_1)
private theorem idp000101111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010111100.list =
    C ((2:ℤ)^170) * horner X vp000101111001.list + horner X ep000101111001.list := by
  exact edge_identity (B := (2:ℤ)^326) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101111001 : Branch 1 (-751761639/4000000 : ℚ) vp00010111100 := by
  apply branch_checked idp000101111001 (by positivity) (by decide +kernel)
  rw [show 2*(-751761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-753761639/2000000 : ℚ) by norm_num]
  exact coverp000101111001
theorem coverp00010111100 : Covers (-751761639/4000000 : ℚ) vp00010111100 := join_branches bp000101111000 bp000101111001
private noncomputable def vp0001011110_0 : Blocks := edgeBlocks% "full/vectors/0001011110-V-0000.bin"
private noncomputable def vp0001011110_1 : Blocks := edgeBlocks% "full/vectors/0001011110-V-0001.bin"
private noncomputable def vp0001011110_2 : Blocks := edgeBlocks% "full/vectors/0001011110-V-0002.bin"
noncomputable def vp0001011110 : Blocks := (Blocks.join vp0001011110_0 (Blocks.join vp0001011110_1 vp0001011110_2))
private theorem bp00010111100 : Branch 0 (-751761639/8000000 : ℚ) vp0001011110 := by
  apply branch_left_normalized (c:=vp00010111100) (k:=0) (m:=159) (by decide +kernel)
  rw [show 2*(-751761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-751761639/4000000 : ℚ) by norm_num]
  exact coverp00010111100
private noncomputable def ep00010111101_0 : Blocks := edgeBlocks% "full/vectors/00010111101-E-0000.bin"
private noncomputable def ep00010111101_1 : Blocks := edgeBlocks% "full/vectors/00010111101-E-0001.bin"
private noncomputable def ep00010111101_2 : Blocks := edgeBlocks% "full/vectors/00010111101-E-0002.bin"
noncomputable def ep00010111101 : Blocks := (Blocks.join ep00010111101_0 (Blocks.join ep00010111101_1 ep00010111101_2))
private theorem idp00010111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011110.list =
    C ((2:ℤ)^323) * horner X vp00010111101.list + horner X ep00010111101.list := by
  exact edge_identity (B := (2:ℤ)^544) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010111101 : Branch 1 (-751761639/8000000 : ℚ) vp0001011110 := by
  apply branch_checked idp00010111101 (by positivity) (by decide +kernel)
  rw [show 2*(-751761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-755761639/4000000 : ℚ) by norm_num]
  exact coverp00010111101
theorem coverp0001011110 : Covers (-751761639/8000000 : ℚ) vp0001011110 := join_branches bp00010111100 bp00010111101
private noncomputable def vp000101111_0 : Blocks := edgeBlocks% "full/vectors/000101111-V-0000.bin"
private noncomputable def vp000101111_1 : Blocks := edgeBlocks% "full/vectors/000101111-V-0001.bin"
private noncomputable def vp000101111_2 : Blocks := edgeBlocks% "full/vectors/000101111-V-0002.bin"
private noncomputable def vp000101111_3 : Blocks := edgeBlocks% "full/vectors/000101111-V-0003.bin"
private noncomputable def vp000101111_4 : Blocks := edgeBlocks% "full/vectors/000101111-V-0004.bin"
noncomputable def vp000101111 : Blocks := (Blocks.join (Blocks.join vp000101111_0 vp000101111_1) (Blocks.join vp000101111_2 (Blocks.join vp000101111_3 vp000101111_4)))
private theorem bp0001011110 : Branch 0 (-751761639/16000000 : ℚ) vp000101111 := by
  apply branch_left_normalized (c:=vp0001011110) (k:=0) (m:=301) (by decide +kernel)
  rw [show 2*(-751761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-751761639/8000000 : ℚ) by norm_num]
  exact coverp0001011110
private noncomputable def ep0001011111_0 : Blocks := edgeBlocks% "full/vectors/0001011111-E-0000.bin"
private noncomputable def ep0001011111_1 : Blocks := edgeBlocks% "full/vectors/0001011111-E-0001.bin"
private noncomputable def ep0001011111_2 : Blocks := edgeBlocks% "full/vectors/0001011111-E-0002.bin"
private noncomputable def ep0001011111_3 : Blocks := edgeBlocks% "full/vectors/0001011111-E-0003.bin"
private noncomputable def ep0001011111_4 : Blocks := edgeBlocks% "full/vectors/0001011111-E-0004.bin"
noncomputable def ep0001011111 : Blocks := (Blocks.join (Blocks.join ep0001011111_0 ep0001011111_1) (Blocks.join ep0001011111_2 (Blocks.join ep0001011111_3 ep0001011111_4)))
private theorem idp0001011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101111.list =
    C ((2:ℤ)^625) * horner X vp0001011111.list + horner X ep0001011111.list := by
  exact edge_identity (B := (2:ℤ)^979) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011111 : Branch 1 (-751761639/16000000 : ℚ) vp000101111 := by
  apply branch_checked idp0001011111 (by positivity) (by decide +kernel)
  rw [show 2*(-751761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-759761639/8000000 : ℚ) by norm_num]
  exact coverp0001011111
theorem coverp000101111 : Covers (-751761639/16000000 : ℚ) vp000101111 := join_branches bp0001011110 bp0001011111
private noncomputable def vp0001011101111_0 : Blocks := edgeBlocks% "full/vectors/0001011101111-V-0000.bin"
noncomputable def vp0001011101111 : Blocks := vp0001011101111_0
theorem coverp0001011101111 : Covers (-750761639/1000000 : ℚ) vp0001011101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011101110_0 : Blocks := edgeBlocks% "full/vectors/0001011101110-V-0000.bin"
noncomputable def vp0001011101110 : Blocks := vp0001011101110_0
theorem coverp0001011101110 : Covers (-749761639/1000000 : ℚ) vp0001011101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000101110111_0 : Blocks := edgeBlocks% "full/vectors/000101110111-V-0000.bin"
noncomputable def vp000101110111 : Blocks := vp000101110111_0
private theorem bp0001011101110 : Branch 0 (-749761639/2000000 : ℚ) vp000101110111 := by
  apply branch_left_normalized (c:=vp0001011101110) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-749761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-749761639/1000000 : ℚ) by norm_num]
  exact coverp0001011101110
private noncomputable def ep0001011101111_0 : Blocks := edgeBlocks% "full/vectors/0001011101111-E-0000.bin"
noncomputable def ep0001011101111 : Blocks := ep0001011101111_0
private theorem idp0001011101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101110111.list =
    C ((2:ℤ)^93) * horner X vp0001011101111.list + horner X ep0001011101111.list := by
  exact edge_identity (B := (2:ℤ)^216) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011101111 : Branch 1 (-749761639/2000000 : ℚ) vp000101110111 := by
  apply branch_checked idp0001011101111 (by positivity) (by decide +kernel)
  rw [show 2*(-749761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-750761639/1000000 : ℚ) by norm_num]
  exact coverp0001011101111
theorem coverp000101110111 : Covers (-749761639/2000000 : ℚ) vp000101110111 := join_branches bp0001011101110 bp0001011101111
private noncomputable def vp0001011101101_0 : Blocks := edgeBlocks% "full/vectors/0001011101101-V-0000.bin"
noncomputable def vp0001011101101 : Blocks := vp0001011101101_0
theorem coverp0001011101101 : Covers (-748761639/1000000 : ℚ) vp0001011101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011101100_0 : Blocks := edgeBlocks% "full/vectors/0001011101100-V-0000.bin"
noncomputable def vp0001011101100 : Blocks := vp0001011101100_0
theorem coverp0001011101100 : Covers (-747761639/1000000 : ℚ) vp0001011101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000101110110_0 : Blocks := edgeBlocks% "full/vectors/000101110110-V-0000.bin"
noncomputable def vp000101110110 : Blocks := vp000101110110_0
private theorem bp0001011101100 : Branch 0 (-747761639/2000000 : ℚ) vp000101110110 := by
  apply branch_left_normalized (c:=vp0001011101100) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-747761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-747761639/1000000 : ℚ) by norm_num]
  exact coverp0001011101100
private noncomputable def ep0001011101101_0 : Blocks := edgeBlocks% "full/vectors/0001011101101-E-0000.bin"
noncomputable def ep0001011101101 : Blocks := ep0001011101101_0
private theorem idp0001011101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101110110.list =
    C ((2:ℤ)^94) * horner X vp0001011101101.list + horner X ep0001011101101.list := by
  exact edge_identity (B := (2:ℤ)^216) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011101101 : Branch 1 (-747761639/2000000 : ℚ) vp000101110110 := by
  apply branch_checked idp0001011101101 (by positivity) (by decide +kernel)
  rw [show 2*(-747761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-748761639/1000000 : ℚ) by norm_num]
  exact coverp0001011101101
theorem coverp000101110110 : Covers (-747761639/2000000 : ℚ) vp000101110110 := join_branches bp0001011101100 bp0001011101101
private noncomputable def vp00010111011_0 : Blocks := edgeBlocks% "full/vectors/00010111011-V-0000.bin"
private noncomputable def vp00010111011_1 : Blocks := edgeBlocks% "full/vectors/00010111011-V-0001.bin"
noncomputable def vp00010111011 : Blocks := (Blocks.join vp00010111011_0 vp00010111011_1)
private theorem bp000101110110 : Branch 0 (-747761639/4000000 : ℚ) vp00010111011 := by
  apply branch_left_normalized (c:=vp000101110110) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-747761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-747761639/2000000 : ℚ) by norm_num]
  exact coverp000101110110
private noncomputable def ep000101110111_0 : Blocks := edgeBlocks% "full/vectors/000101110111-E-0000.bin"
private noncomputable def ep000101110111_1 : Blocks := edgeBlocks% "full/vectors/000101110111-E-0001.bin"
noncomputable def ep000101110111 : Blocks := (Blocks.join ep000101110111_0 ep000101110111_1)
private theorem idp000101110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010111011.list =
    C ((2:ℤ)^172) * horner X vp000101110111.list + horner X ep000101110111.list := by
  exact edge_identity (B := (2:ℤ)^326) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101110111 : Branch 1 (-747761639/4000000 : ℚ) vp00010111011 := by
  apply branch_checked idp000101110111 (by positivity) (by decide +kernel)
  rw [show 2*(-747761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-749761639/2000000 : ℚ) by norm_num]
  exact coverp000101110111
theorem coverp00010111011 : Covers (-747761639/4000000 : ℚ) vp00010111011 := join_branches bp000101110110 bp000101110111
private noncomputable def vp0001011101011_0 : Blocks := edgeBlocks% "full/vectors/0001011101011-V-0000.bin"
noncomputable def vp0001011101011 : Blocks := vp0001011101011_0
theorem coverp0001011101011 : Covers (-746761639/1000000 : ℚ) vp0001011101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011101010_0 : Blocks := edgeBlocks% "full/vectors/0001011101010-V-0000.bin"
noncomputable def vp0001011101010 : Blocks := vp0001011101010_0
theorem coverp0001011101010 : Covers (-745761639/1000000 : ℚ) vp0001011101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000101110101_0 : Blocks := edgeBlocks% "full/vectors/000101110101-V-0000.bin"
noncomputable def vp000101110101 : Blocks := vp000101110101_0
private theorem bp0001011101010 : Branch 0 (-745761639/2000000 : ℚ) vp000101110101 := by
  apply branch_left_normalized (c:=vp0001011101010) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-745761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-745761639/1000000 : ℚ) by norm_num]
  exact coverp0001011101010
private noncomputable def ep0001011101011_0 : Blocks := edgeBlocks% "full/vectors/0001011101011-E-0000.bin"
noncomputable def ep0001011101011 : Blocks := ep0001011101011_0
private theorem idp0001011101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101110101.list =
    C ((2:ℤ)^93) * horner X vp0001011101011.list + horner X ep0001011101011.list := by
  exact edge_identity (B := (2:ℤ)^216) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011101011 : Branch 1 (-745761639/2000000 : ℚ) vp000101110101 := by
  apply branch_checked idp0001011101011 (by positivity) (by decide +kernel)
  rw [show 2*(-745761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-746761639/1000000 : ℚ) by norm_num]
  exact coverp0001011101011
theorem coverp000101110101 : Covers (-745761639/2000000 : ℚ) vp000101110101 := join_branches bp0001011101010 bp0001011101011
private noncomputable def vp0001011101001_0 : Blocks := edgeBlocks% "full/vectors/0001011101001-V-0000.bin"
noncomputable def vp0001011101001 : Blocks := vp0001011101001_0
theorem coverp0001011101001 : Covers (-744761639/1000000 : ℚ) vp0001011101001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011101000_0 : Blocks := edgeBlocks% "full/vectors/0001011101000-V-0000.bin"
noncomputable def vp0001011101000 : Blocks := vp0001011101000_0
theorem coverp0001011101000 : Covers (-743761639/1000000 : ℚ) vp0001011101000 := cover_leaf (by decide +kernel)
private noncomputable def vp000101110100_0 : Blocks := edgeBlocks% "full/vectors/000101110100-V-0000.bin"
noncomputable def vp000101110100 : Blocks := vp000101110100_0
private theorem bp0001011101000 : Branch 0 (-743761639/2000000 : ℚ) vp000101110100 := by
  apply branch_left_normalized (c:=vp0001011101000) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-743761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-743761639/1000000 : ℚ) by norm_num]
  exact coverp0001011101000
private noncomputable def ep0001011101001_0 : Blocks := edgeBlocks% "full/vectors/0001011101001-E-0000.bin"
noncomputable def ep0001011101001 : Blocks := ep0001011101001_0
private theorem idp0001011101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101110100.list =
    C ((2:ℤ)^94) * horner X vp0001011101001.list + horner X ep0001011101001.list := by
  exact edge_identity (B := (2:ℤ)^216) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011101001 : Branch 1 (-743761639/2000000 : ℚ) vp000101110100 := by
  apply branch_checked idp0001011101001 (by positivity) (by decide +kernel)
  rw [show 2*(-743761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-744761639/1000000 : ℚ) by norm_num]
  exact coverp0001011101001
theorem coverp000101110100 : Covers (-743761639/2000000 : ℚ) vp000101110100 := join_branches bp0001011101000 bp0001011101001
private noncomputable def vp00010111010_0 : Blocks := edgeBlocks% "full/vectors/00010111010-V-0000.bin"
private noncomputable def vp00010111010_1 : Blocks := edgeBlocks% "full/vectors/00010111010-V-0001.bin"
noncomputable def vp00010111010 : Blocks := (Blocks.join vp00010111010_0 vp00010111010_1)
private theorem bp000101110100 : Branch 0 (-743761639/4000000 : ℚ) vp00010111010 := by
  apply branch_left_normalized (c:=vp000101110100) (k:=0) (m:=87) (by decide +kernel)
  rw [show 2*(-743761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-743761639/2000000 : ℚ) by norm_num]
  exact coverp000101110100
private noncomputable def ep000101110101_0 : Blocks := edgeBlocks% "full/vectors/000101110101-E-0000.bin"
private noncomputable def ep000101110101_1 : Blocks := edgeBlocks% "full/vectors/000101110101-E-0001.bin"
noncomputable def ep000101110101 : Blocks := (Blocks.join ep000101110101_0 ep000101110101_1)
private theorem idp000101110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010111010.list =
    C ((2:ℤ)^172) * horner X vp000101110101.list + horner X ep000101110101.list := by
  exact edge_identity (B := (2:ℤ)^327) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101110101 : Branch 1 (-743761639/4000000 : ℚ) vp00010111010 := by
  apply branch_checked idp000101110101 (by positivity) (by decide +kernel)
  rw [show 2*(-743761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-745761639/2000000 : ℚ) by norm_num]
  exact coverp000101110101
theorem coverp00010111010 : Covers (-743761639/4000000 : ℚ) vp00010111010 := join_branches bp000101110100 bp000101110101
private noncomputable def vp0001011101_0 : Blocks := edgeBlocks% "full/vectors/0001011101-V-0000.bin"
private noncomputable def vp0001011101_1 : Blocks := edgeBlocks% "full/vectors/0001011101-V-0001.bin"
private noncomputable def vp0001011101_2 : Blocks := edgeBlocks% "full/vectors/0001011101-V-0002.bin"
noncomputable def vp0001011101 : Blocks := (Blocks.join vp0001011101_0 (Blocks.join vp0001011101_1 vp0001011101_2))
private theorem bp00010111010 : Branch 0 (-743761639/8000000 : ℚ) vp0001011101 := by
  apply branch_left_normalized (c:=vp00010111010) (k:=0) (m:=159) (by decide +kernel)
  rw [show 2*(-743761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-743761639/4000000 : ℚ) by norm_num]
  exact coverp00010111010
private noncomputable def ep00010111011_0 : Blocks := edgeBlocks% "full/vectors/00010111011-E-0000.bin"
private noncomputable def ep00010111011_1 : Blocks := edgeBlocks% "full/vectors/00010111011-E-0001.bin"
private noncomputable def ep00010111011_2 : Blocks := edgeBlocks% "full/vectors/00010111011-E-0002.bin"
noncomputable def ep00010111011 : Blocks := (Blocks.join ep00010111011_0 (Blocks.join ep00010111011_1 ep00010111011_2))
private theorem idp00010111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011101.list =
    C ((2:ℤ)^326) * horner X vp00010111011.list + horner X ep00010111011.list := by
  exact edge_identity (B := (2:ℤ)^546) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010111011 : Branch 1 (-743761639/8000000 : ℚ) vp0001011101 := by
  apply branch_checked idp00010111011 (by positivity) (by decide +kernel)
  rw [show 2*(-743761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-747761639/4000000 : ℚ) by norm_num]
  exact coverp00010111011
theorem coverp0001011101 : Covers (-743761639/8000000 : ℚ) vp0001011101 := join_branches bp00010111010 bp00010111011
private noncomputable def vp0001011100111_0 : Blocks := edgeBlocks% "full/vectors/0001011100111-V-0000.bin"
noncomputable def vp0001011100111 : Blocks := vp0001011100111_0
theorem coverp0001011100111 : Covers (-742761639/1000000 : ℚ) vp0001011100111 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011100110_0 : Blocks := edgeBlocks% "full/vectors/0001011100110-V-0000.bin"
noncomputable def vp0001011100110 : Blocks := vp0001011100110_0
theorem coverp0001011100110 : Covers (-741761639/1000000 : ℚ) vp0001011100110 := cover_leaf (by decide +kernel)
private noncomputable def vp000101110011_0 : Blocks := edgeBlocks% "full/vectors/000101110011-V-0000.bin"
noncomputable def vp000101110011 : Blocks := vp000101110011_0
private theorem bp0001011100110 : Branch 0 (-741761639/2000000 : ℚ) vp000101110011 := by
  apply branch_left_normalized (c:=vp0001011100110) (k:=0) (m:=50) (by decide +kernel)
  rw [show 2*(-741761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-741761639/1000000 : ℚ) by norm_num]
  exact coverp0001011100110
private noncomputable def ep0001011100111_0 : Blocks := edgeBlocks% "full/vectors/0001011100111-E-0000.bin"
noncomputable def ep0001011100111 : Blocks := ep0001011100111_0
private theorem idp0001011100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101110011.list =
    C ((2:ℤ)^94) * horner X vp0001011100111.list + horner X ep0001011100111.list := by
  exact edge_identity (B := (2:ℤ)^217) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011100111 : Branch 1 (-741761639/2000000 : ℚ) vp000101110011 := by
  apply branch_checked idp0001011100111 (by positivity) (by decide +kernel)
  rw [show 2*(-741761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-742761639/1000000 : ℚ) by norm_num]
  exact coverp0001011100111
theorem coverp000101110011 : Covers (-741761639/2000000 : ℚ) vp000101110011 := join_branches bp0001011100110 bp0001011100111
private noncomputable def vp0001011100101_0 : Blocks := edgeBlocks% "full/vectors/0001011100101-V-0000.bin"
noncomputable def vp0001011100101 : Blocks := vp0001011100101_0
theorem coverp0001011100101 : Covers (-740761639/1000000 : ℚ) vp0001011100101 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011100100_0 : Blocks := edgeBlocks% "full/vectors/0001011100100-V-0000.bin"
noncomputable def vp0001011100100 : Blocks := vp0001011100100_0
theorem coverp0001011100100 : Covers (-739761639/1000000 : ℚ) vp0001011100100 := cover_leaf (by decide +kernel)
private noncomputable def vp000101110010_0 : Blocks := edgeBlocks% "full/vectors/000101110010-V-0000.bin"
noncomputable def vp000101110010 : Blocks := vp000101110010_0
private theorem bp0001011100100 : Branch 0 (-739761639/2000000 : ℚ) vp000101110010 := by
  apply branch_left_normalized (c:=vp0001011100100) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-739761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-739761639/1000000 : ℚ) by norm_num]
  exact coverp0001011100100
private noncomputable def ep0001011100101_0 : Blocks := edgeBlocks% "full/vectors/0001011100101-E-0000.bin"
noncomputable def ep0001011100101 : Blocks := ep0001011100101_0
private theorem idp0001011100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101110010.list =
    C ((2:ℤ)^95) * horner X vp0001011100101.list + horner X ep0001011100101.list := by
  exact edge_identity (B := (2:ℤ)^218) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011100101 : Branch 1 (-739761639/2000000 : ℚ) vp000101110010 := by
  apply branch_checked idp0001011100101 (by positivity) (by decide +kernel)
  rw [show 2*(-739761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-740761639/1000000 : ℚ) by norm_num]
  exact coverp0001011100101
theorem coverp000101110010 : Covers (-739761639/2000000 : ℚ) vp000101110010 := join_branches bp0001011100100 bp0001011100101
private noncomputable def vp00010111001_0 : Blocks := edgeBlocks% "full/vectors/00010111001-V-0000.bin"
private noncomputable def vp00010111001_1 : Blocks := edgeBlocks% "full/vectors/00010111001-V-0001.bin"
noncomputable def vp00010111001 : Blocks := (Blocks.join vp00010111001_0 vp00010111001_1)
private theorem bp000101110010 : Branch 0 (-739761639/4000000 : ℚ) vp00010111001 := by
  apply branch_left_normalized (c:=vp000101110010) (k:=0) (m:=88) (by decide +kernel)
  rw [show 2*(-739761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-739761639/2000000 : ℚ) by norm_num]
  exact coverp000101110010
private noncomputable def ep000101110011_0 : Blocks := edgeBlocks% "full/vectors/000101110011-E-0000.bin"
private noncomputable def ep000101110011_1 : Blocks := edgeBlocks% "full/vectors/000101110011-E-0001.bin"
noncomputable def ep000101110011 : Blocks := (Blocks.join ep000101110011_0 ep000101110011_1)
private theorem idp000101110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010111001.list =
    C ((2:ℤ)^173) * horner X vp000101110011.list + horner X ep000101110011.list := by
  exact edge_identity (B := (2:ℤ)^329) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101110011 : Branch 1 (-739761639/4000000 : ℚ) vp00010111001 := by
  apply branch_checked idp000101110011 (by positivity) (by decide +kernel)
  rw [show 2*(-739761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-741761639/2000000 : ℚ) by norm_num]
  exact coverp000101110011
theorem coverp00010111001 : Covers (-739761639/4000000 : ℚ) vp00010111001 := join_branches bp000101110010 bp000101110011
private noncomputable def vp0001011100011_0 : Blocks := edgeBlocks% "full/vectors/0001011100011-V-0000.bin"
noncomputable def vp0001011100011 : Blocks := vp0001011100011_0
theorem coverp0001011100011 : Covers (-738761639/1000000 : ℚ) vp0001011100011 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011100010_0 : Blocks := edgeBlocks% "full/vectors/0001011100010-V-0000.bin"
noncomputable def vp0001011100010 : Blocks := vp0001011100010_0
theorem coverp0001011100010 : Covers (-737761639/1000000 : ℚ) vp0001011100010 := cover_leaf (by decide +kernel)
private noncomputable def vp000101110001_0 : Blocks := edgeBlocks% "full/vectors/000101110001-V-0000.bin"
noncomputable def vp000101110001 : Blocks := vp000101110001_0
private theorem bp0001011100010 : Branch 0 (-737761639/2000000 : ℚ) vp000101110001 := by
  apply branch_left_normalized (c:=vp0001011100010) (k:=0) (m:=51) (by decide +kernel)
  rw [show 2*(-737761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-737761639/1000000 : ℚ) by norm_num]
  exact coverp0001011100010
private noncomputable def ep0001011100011_0 : Blocks := edgeBlocks% "full/vectors/0001011100011-E-0000.bin"
noncomputable def ep0001011100011 : Blocks := ep0001011100011_0
private theorem idp0001011100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101110001.list =
    C ((2:ℤ)^95) * horner X vp0001011100011.list + horner X ep0001011100011.list := by
  exact edge_identity (B := (2:ℤ)^220) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011100011 : Branch 1 (-737761639/2000000 : ℚ) vp000101110001 := by
  apply branch_checked idp0001011100011 (by positivity) (by decide +kernel)
  rw [show 2*(-737761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-738761639/1000000 : ℚ) by norm_num]
  exact coverp0001011100011
theorem coverp000101110001 : Covers (-737761639/2000000 : ℚ) vp000101110001 := join_branches bp0001011100010 bp0001011100011
private noncomputable def vp0001011100001_0 : Blocks := edgeBlocks% "full/vectors/0001011100001-V-0000.bin"
noncomputable def vp0001011100001 : Blocks := vp0001011100001_0
theorem coverp0001011100001 : Covers (-736761639/1000000 : ℚ) vp0001011100001 := cover_leaf (by decide +kernel)
private noncomputable def vp0001011100000_0 : Blocks := edgeBlocks% "full/vectors/0001011100000-V-0000.bin"
noncomputable def vp0001011100000 : Blocks := vp0001011100000_0
theorem coverp0001011100000 : Covers (-735761639/1000000 : ℚ) vp0001011100000 := cover_leaf (by decide +kernel)
private noncomputable def vp000101110000_0 : Blocks := edgeBlocks% "full/vectors/000101110000-V-0000.bin"
noncomputable def vp000101110000 : Blocks := vp000101110000_0
private theorem bp0001011100000 : Branch 0 (-735761639/2000000 : ℚ) vp000101110000 := by
  apply branch_left_normalized (c:=vp0001011100000) (k:=0) (m:=53) (by decide +kernel)
  rw [show 2*(-735761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-735761639/1000000 : ℚ) by norm_num]
  exact coverp0001011100000
private noncomputable def ep0001011100001_0 : Blocks := edgeBlocks% "full/vectors/0001011100001-E-0000.bin"
noncomputable def ep0001011100001 : Blocks := ep0001011100001_0
private theorem idp0001011100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101110000.list =
    C ((2:ℤ)^98) * horner X vp0001011100001.list + horner X ep0001011100001.list := by
  exact edge_identity (B := (2:ℤ)^224) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011100001 : Branch 1 (-735761639/2000000 : ℚ) vp000101110000 := by
  apply branch_checked idp0001011100001 (by positivity) (by decide +kernel)
  rw [show 2*(-735761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-736761639/1000000 : ℚ) by norm_num]
  exact coverp0001011100001
theorem coverp000101110000 : Covers (-735761639/2000000 : ℚ) vp000101110000 := join_branches bp0001011100000 bp0001011100001
private noncomputable def vp00010111000_0 : Blocks := edgeBlocks% "full/vectors/00010111000-V-0000.bin"
private noncomputable def vp00010111000_1 : Blocks := edgeBlocks% "full/vectors/00010111000-V-0001.bin"
noncomputable def vp00010111000 : Blocks := (Blocks.join vp00010111000_0 vp00010111000_1)
private theorem bp000101110000 : Branch 0 (-735761639/4000000 : ℚ) vp00010111000 := by
  apply branch_left_normalized (c:=vp000101110000) (k:=0) (m:=90) (by decide +kernel)
  rw [show 2*(-735761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-735761639/2000000 : ℚ) by norm_num]
  exact coverp000101110000
private noncomputable def ep000101110001_0 : Blocks := edgeBlocks% "full/vectors/000101110001-E-0000.bin"
private noncomputable def ep000101110001_1 : Blocks := edgeBlocks% "full/vectors/000101110001-E-0001.bin"
noncomputable def ep000101110001 : Blocks := (Blocks.join ep000101110001_0 ep000101110001_1)
private theorem idp000101110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010111000.list =
    C ((2:ℤ)^177) * horner X vp000101110001.list + horner X ep000101110001.list := by
  exact edge_identity (B := (2:ℤ)^335) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101110001 : Branch 1 (-735761639/4000000 : ℚ) vp00010111000 := by
  apply branch_checked idp000101110001 (by positivity) (by decide +kernel)
  rw [show 2*(-735761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-737761639/2000000 : ℚ) by norm_num]
  exact coverp000101110001
theorem coverp00010111000 : Covers (-735761639/4000000 : ℚ) vp00010111000 := join_branches bp000101110000 bp000101110001
private noncomputable def vp0001011100_0 : Blocks := edgeBlocks% "full/vectors/0001011100-V-0000.bin"
private noncomputable def vp0001011100_1 : Blocks := edgeBlocks% "full/vectors/0001011100-V-0001.bin"
private noncomputable def vp0001011100_2 : Blocks := edgeBlocks% "full/vectors/0001011100-V-0002.bin"
noncomputable def vp0001011100 : Blocks := (Blocks.join vp0001011100_0 (Blocks.join vp0001011100_1 vp0001011100_2))
private theorem bp00010111000 : Branch 0 (-735761639/8000000 : ℚ) vp0001011100 := by
  apply branch_left_normalized (c:=vp00010111000) (k:=0) (m:=162) (by decide +kernel)
  rw [show 2*(-735761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-735761639/4000000 : ℚ) by norm_num]
  exact coverp00010111000
private noncomputable def ep00010111001_0 : Blocks := edgeBlocks% "full/vectors/00010111001-E-0000.bin"
private noncomputable def ep00010111001_1 : Blocks := edgeBlocks% "full/vectors/00010111001-E-0001.bin"
private noncomputable def ep00010111001_2 : Blocks := edgeBlocks% "full/vectors/00010111001-E-0002.bin"
noncomputable def ep00010111001 : Blocks := (Blocks.join ep00010111001_0 (Blocks.join ep00010111001_1 ep00010111001_2))
private theorem idp00010111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0001011100.list =
    C ((2:ℤ)^335) * horner X vp00010111001.list + horner X ep00010111001.list := by
  exact edge_identity (B := (2:ℤ)^557) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00010111001 : Branch 1 (-735761639/8000000 : ℚ) vp0001011100 := by
  apply branch_checked idp00010111001 (by positivity) (by decide +kernel)
  rw [show 2*(-735761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-739761639/4000000 : ℚ) by norm_num]
  exact coverp00010111001
theorem coverp0001011100 : Covers (-735761639/8000000 : ℚ) vp0001011100 := join_branches bp00010111000 bp00010111001
private noncomputable def vp000101110_0 : Blocks := edgeBlocks% "full/vectors/000101110-V-0000.bin"
private noncomputable def vp000101110_1 : Blocks := edgeBlocks% "full/vectors/000101110-V-0001.bin"
private noncomputable def vp000101110_2 : Blocks := edgeBlocks% "full/vectors/000101110-V-0002.bin"
private noncomputable def vp000101110_3 : Blocks := edgeBlocks% "full/vectors/000101110-V-0003.bin"
private noncomputable def vp000101110_4 : Blocks := edgeBlocks% "full/vectors/000101110-V-0004.bin"
noncomputable def vp000101110 : Blocks := (Blocks.join (Blocks.join vp000101110_0 vp000101110_1) (Blocks.join vp000101110_2 (Blocks.join vp000101110_3 vp000101110_4)))
private theorem bp0001011100 : Branch 0 (-735761639/16000000 : ℚ) vp000101110 := by
  apply branch_left_normalized (c:=vp0001011100) (k:=0) (m:=307) (by decide +kernel)
  rw [show 2*(-735761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-735761639/8000000 : ℚ) by norm_num]
  exact coverp0001011100
private noncomputable def ep0001011101_0 : Blocks := edgeBlocks% "full/vectors/0001011101-E-0000.bin"
private noncomputable def ep0001011101_1 : Blocks := edgeBlocks% "full/vectors/0001011101-E-0001.bin"
private noncomputable def ep0001011101_2 : Blocks := edgeBlocks% "full/vectors/0001011101-E-0002.bin"
private noncomputable def ep0001011101_3 : Blocks := edgeBlocks% "full/vectors/0001011101-E-0003.bin"
private noncomputable def ep0001011101_4 : Blocks := edgeBlocks% "full/vectors/0001011101-E-0004.bin"
noncomputable def ep0001011101 : Blocks := (Blocks.join (Blocks.join ep0001011101_0 ep0001011101_1) (Blocks.join ep0001011101_2 (Blocks.join ep0001011101_3 ep0001011101_4)))
private theorem idp0001011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000101110.list =
    C ((2:ℤ)^645) * horner X vp0001011101.list + horner X ep0001011101.list := by
  exact edge_identity (B := (2:ℤ)^996) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0001011101 : Branch 1 (-735761639/16000000 : ℚ) vp000101110 := by
  apply branch_checked idp0001011101 (by positivity) (by decide +kernel)
  rw [show 2*(-735761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-743761639/8000000 : ℚ) by norm_num]
  exact coverp0001011101
theorem coverp000101110 : Covers (-735761639/16000000 : ℚ) vp000101110 := join_branches bp0001011100 bp0001011101
private noncomputable def vp00010111_0 : Blocks := edgeBlocks% "full/vectors/00010111-V-0000.bin"
private noncomputable def vp00010111_1 : Blocks := edgeBlocks% "full/vectors/00010111-V-0001.bin"
private noncomputable def vp00010111_2 : Blocks := edgeBlocks% "full/vectors/00010111-V-0002.bin"
private noncomputable def vp00010111_3 : Blocks := edgeBlocks% "full/vectors/00010111-V-0003.bin"
private noncomputable def vp00010111_4 : Blocks := edgeBlocks% "full/vectors/00010111-V-0004.bin"
private noncomputable def vp00010111_5 : Blocks := edgeBlocks% "full/vectors/00010111-V-0005.bin"
private noncomputable def vp00010111_6 : Blocks := edgeBlocks% "full/vectors/00010111-V-0006.bin"
private noncomputable def vp00010111_7 : Blocks := edgeBlocks% "full/vectors/00010111-V-0007.bin"
private noncomputable def vp00010111_8 : Blocks := edgeBlocks% "full/vectors/00010111-V-0008.bin"
private noncomputable def vp00010111_9 : Blocks := edgeBlocks% "full/vectors/00010111-V-0009.bin"
noncomputable def vp00010111 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00010111_0 vp00010111_1) (Blocks.join vp00010111_2 (Blocks.join vp00010111_3 vp00010111_4))) (Blocks.join (Blocks.join vp00010111_5 vp00010111_6) (Blocks.join vp00010111_7 (Blocks.join vp00010111_8 vp00010111_9))))
private theorem bp000101110 : Branch 0 (-735761639/32000000 : ℚ) vp00010111 := by
  apply branch_left_normalized (c:=vp000101110) (k:=0) (m:=593) (by decide +kernel)
  rw [show 2*(-735761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-735761639/16000000 : ℚ) by norm_num]
  exact coverp000101110
private noncomputable def ep000101111_0 : Blocks := edgeBlocks% "full/vectors/000101111-E-0000.bin"
private noncomputable def ep000101111_1 : Blocks := edgeBlocks% "full/vectors/000101111-E-0001.bin"
private noncomputable def ep000101111_2 : Blocks := edgeBlocks% "full/vectors/000101111-E-0002.bin"
private noncomputable def ep000101111_3 : Blocks := edgeBlocks% "full/vectors/000101111-E-0003.bin"
private noncomputable def ep000101111_4 : Blocks := edgeBlocks% "full/vectors/000101111-E-0004.bin"
private noncomputable def ep000101111_5 : Blocks := edgeBlocks% "full/vectors/000101111-E-0005.bin"
private noncomputable def ep000101111_6 : Blocks := edgeBlocks% "full/vectors/000101111-E-0006.bin"
private noncomputable def ep000101111_7 : Blocks := edgeBlocks% "full/vectors/000101111-E-0007.bin"
private noncomputable def ep000101111_8 : Blocks := edgeBlocks% "full/vectors/000101111-E-0008.bin"
private noncomputable def ep000101111_9 : Blocks := edgeBlocks% "full/vectors/000101111-E-0009.bin"
noncomputable def ep000101111 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000101111_0 ep000101111_1) (Blocks.join ep000101111_2 (Blocks.join ep000101111_3 ep000101111_4))) (Blocks.join (Blocks.join ep000101111_5 ep000101111_6) (Blocks.join ep000101111_7 (Blocks.join ep000101111_8 ep000101111_9))))
private theorem idp000101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00010111.list =
    C ((2:ℤ)^1256) * horner X vp000101111.list + horner X ep000101111.list := by
  exact edge_identity (B := (2:ℤ)^1866) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000101111 : Branch 1 (-735761639/32000000 : ℚ) vp00010111 := by
  apply branch_checked idp000101111 (by positivity) (by decide +kernel)
  rw [show 2*(-735761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-751761639/16000000 : ℚ) by norm_num]
  exact coverp000101111
theorem coverp00010111 : Covers (-735761639/32000000 : ℚ) vp00010111 := join_branches bp000101110 bp000101111
end NextProof.EdgeFull

