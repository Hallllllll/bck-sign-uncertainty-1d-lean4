import NextProof.CompactEdge
import NextProof.EdgeInput
import NextProof.EdgeArithmetic

namespace NextProof.EdgeFull
open NextProof.Tail NextProof.Compact Polynomial
set_option maxRecDepth 150000
set_option maxHeartbeats 0
set_option exponentiation.threshold 1000000

private noncomputable def vp00001101111111_0 : Blocks := edgeBlocks% "full/vectors/00001101111111-V-0000.bin"
noncomputable def vp00001101111111 : Blocks := vp00001101111111_0
theorem coverp00001101111111 : Covers (-447261639/500000 : ℚ) vp00001101111111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101111110_0 : Blocks := edgeBlocks% "full/vectors/00001101111110-V-0000.bin"
noncomputable def vp00001101111110 : Blocks := vp00001101111110_0
theorem coverp00001101111110 : Covers (-446761639/500000 : ℚ) vp00001101111110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110111111_0 : Blocks := edgeBlocks% "full/vectors/0000110111111-V-0000.bin"
noncomputable def vp0000110111111 : Blocks := vp0000110111111_0
private theorem bp00001101111110 : Branch 0 (-446761639/1000000 : ℚ) vp0000110111111 := by
  apply branch_left_normalized (c:=vp00001101111110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-446761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-446761639/500000 : ℚ) by norm_num]
  exact coverp00001101111110
private noncomputable def ep00001101111111_0 : Blocks := edgeBlocks% "full/vectors/00001101111111-E-0000.bin"
noncomputable def ep00001101111111 : Blocks := ep00001101111111_0
private theorem idp00001101111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110111111.list =
    C ((2:ℤ)^66) * horner X vp00001101111111.list + horner X ep00001101111111.list := by
  exact edge_identity (B := (2:ℤ)^188) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101111111 : Branch 1 (-446761639/1000000 : ℚ) vp0000110111111 := by
  apply branch_checked idp00001101111111 (by positivity) (by decide +kernel)
  rw [show 2*(-446761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-447261639/500000 : ℚ) by norm_num]
  exact coverp00001101111111
theorem coverp0000110111111 : Covers (-446761639/1000000 : ℚ) vp0000110111111 := join_branches bp00001101111110 bp00001101111111
private noncomputable def vp00001101111101_0 : Blocks := edgeBlocks% "full/vectors/00001101111101-V-0000.bin"
noncomputable def vp00001101111101 : Blocks := vp00001101111101_0
theorem coverp00001101111101 : Covers (-446261639/500000 : ℚ) vp00001101111101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101111100_0 : Blocks := edgeBlocks% "full/vectors/00001101111100-V-0000.bin"
noncomputable def vp00001101111100 : Blocks := vp00001101111100_0
theorem coverp00001101111100 : Covers (-445761639/500000 : ℚ) vp00001101111100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110111110_0 : Blocks := edgeBlocks% "full/vectors/0000110111110-V-0000.bin"
noncomputable def vp0000110111110 : Blocks := vp0000110111110_0
private theorem bp00001101111100 : Branch 0 (-445761639/1000000 : ℚ) vp0000110111110 := by
  apply branch_left_normalized (c:=vp00001101111100) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-445761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-445761639/500000 : ℚ) by norm_num]
  exact coverp00001101111100
private noncomputable def ep00001101111101_0 : Blocks := edgeBlocks% "full/vectors/00001101111101-E-0000.bin"
noncomputable def ep00001101111101 : Blocks := ep00001101111101_0
private theorem idp00001101111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110111110.list =
    C ((2:ℤ)^67) * horner X vp00001101111101.list + horner X ep00001101111101.list := by
  exact edge_identity (B := (2:ℤ)^185) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101111101 : Branch 1 (-445761639/1000000 : ℚ) vp0000110111110 := by
  apply branch_checked idp00001101111101 (by positivity) (by decide +kernel)
  rw [show 2*(-445761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-446261639/500000 : ℚ) by norm_num]
  exact coverp00001101111101
theorem coverp0000110111110 : Covers (-445761639/1000000 : ℚ) vp0000110111110 := join_branches bp00001101111100 bp00001101111101
private noncomputable def vp000011011111_0 : Blocks := edgeBlocks% "full/vectors/000011011111-V-0000.bin"
noncomputable def vp000011011111 : Blocks := vp000011011111_0
private theorem bp0000110111110 : Branch 0 (-445761639/2000000 : ℚ) vp000011011111 := by
  apply branch_left_normalized (c:=vp0000110111110) (k:=0) (m:=64) (by decide +kernel)
  rw [show 2*(-445761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-445761639/1000000 : ℚ) by norm_num]
  exact coverp0000110111110
private noncomputable def ep0000110111111_0 : Blocks := edgeBlocks% "full/vectors/0000110111111-E-0000.bin"
noncomputable def ep0000110111111 : Blocks := ep0000110111111_0
private theorem idp0000110111111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011011111.list =
    C ((2:ℤ)^115) * horner X vp0000110111111.list + horner X ep0000110111111.list := by
  exact edge_identity (B := (2:ℤ)^257) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110111111 : Branch 1 (-445761639/2000000 : ℚ) vp000011011111 := by
  apply branch_checked idp0000110111111 (by positivity) (by decide +kernel)
  rw [show 2*(-445761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-446761639/1000000 : ℚ) by norm_num]
  exact coverp0000110111111
theorem coverp000011011111 : Covers (-445761639/2000000 : ℚ) vp000011011111 := join_branches bp0000110111110 bp0000110111111
private noncomputable def vp00001101111011_0 : Blocks := edgeBlocks% "full/vectors/00001101111011-V-0000.bin"
noncomputable def vp00001101111011 : Blocks := vp00001101111011_0
theorem coverp00001101111011 : Covers (-445261639/500000 : ℚ) vp00001101111011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101111010_0 : Blocks := edgeBlocks% "full/vectors/00001101111010-V-0000.bin"
noncomputable def vp00001101111010 : Blocks := vp00001101111010_0
theorem coverp00001101111010 : Covers (-444761639/500000 : ℚ) vp00001101111010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110111101_0 : Blocks := edgeBlocks% "full/vectors/0000110111101-V-0000.bin"
noncomputable def vp0000110111101 : Blocks := vp0000110111101_0
private theorem bp00001101111010 : Branch 0 (-444761639/1000000 : ℚ) vp0000110111101 := by
  apply branch_left_normalized (c:=vp00001101111010) (k:=0) (m:=38) (by decide +kernel)
  rw [show 2*(-444761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-444761639/500000 : ℚ) by norm_num]
  exact coverp00001101111010
private noncomputable def ep00001101111011_0 : Blocks := edgeBlocks% "full/vectors/00001101111011-E-0000.bin"
noncomputable def ep00001101111011 : Blocks := ep00001101111011_0
private theorem idp00001101111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110111101.list =
    C ((2:ℤ)^66) * horner X vp00001101111011.list + horner X ep00001101111011.list := by
  exact edge_identity (B := (2:ℤ)^183) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101111011 : Branch 1 (-444761639/1000000 : ℚ) vp0000110111101 := by
  apply branch_checked idp00001101111011 (by positivity) (by decide +kernel)
  rw [show 2*(-444761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-445261639/500000 : ℚ) by norm_num]
  exact coverp00001101111011
theorem coverp0000110111101 : Covers (-444761639/1000000 : ℚ) vp0000110111101 := join_branches bp00001101111010 bp00001101111011
private noncomputable def vp0000110111100_0 : Blocks := edgeBlocks% "full/vectors/0000110111100-V-0000.bin"
noncomputable def vp0000110111100 : Blocks := vp0000110111100_0
theorem coverp0000110111100 : Covers (-443761639/1000000 : ℚ) vp0000110111100 := cover_leaf (by decide +kernel)
private noncomputable def vp000011011110_0 : Blocks := edgeBlocks% "full/vectors/000011011110-V-0000.bin"
noncomputable def vp000011011110 : Blocks := vp000011011110_0
private theorem bp0000110111100 : Branch 0 (-443761639/2000000 : ℚ) vp000011011110 := by
  apply branch_left_normalized (c:=vp0000110111100) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-443761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-443761639/1000000 : ℚ) by norm_num]
  exact coverp0000110111100
private noncomputable def ep0000110111101_0 : Blocks := edgeBlocks% "full/vectors/0000110111101-E-0000.bin"
noncomputable def ep0000110111101 : Blocks := ep0000110111101_0
private theorem idp0000110111101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011011110.list =
    C ((2:ℤ)^115) * horner X vp0000110111101.list + horner X ep0000110111101.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110111101 : Branch 1 (-443761639/2000000 : ℚ) vp000011011110 := by
  apply branch_checked idp0000110111101 (by positivity) (by decide +kernel)
  rw [show 2*(-443761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-444761639/1000000 : ℚ) by norm_num]
  exact coverp0000110111101
theorem coverp000011011110 : Covers (-443761639/2000000 : ℚ) vp000011011110 := join_branches bp0000110111100 bp0000110111101
private noncomputable def vp00001101111_0 : Blocks := edgeBlocks% "full/vectors/00001101111-V-0000.bin"
private noncomputable def vp00001101111_1 : Blocks := edgeBlocks% "full/vectors/00001101111-V-0001.bin"
noncomputable def vp00001101111 : Blocks := (Blocks.join vp00001101111_0 vp00001101111_1)
private theorem bp000011011110 : Branch 0 (-443761639/4000000 : ℚ) vp00001101111 := by
  apply branch_left_normalized (c:=vp000011011110) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-443761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-443761639/2000000 : ℚ) by norm_num]
  exact coverp000011011110
private noncomputable def ep000011011111_0 : Blocks := edgeBlocks% "full/vectors/000011011111-E-0000.bin"
private noncomputable def ep000011011111_1 : Blocks := edgeBlocks% "full/vectors/000011011111-E-0001.bin"
noncomputable def ep000011011111 : Blocks := (Blocks.join ep000011011111_0 ep000011011111_1)
private theorem idp000011011111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001101111.list =
    C ((2:ℤ)^212) * horner X vp000011011111.list + horner X ep000011011111.list := by
  exact edge_identity (B := (2:ℤ)^395) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011011111 : Branch 1 (-443761639/4000000 : ℚ) vp00001101111 := by
  apply branch_checked idp000011011111 (by positivity) (by decide +kernel)
  rw [show 2*(-443761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-445761639/2000000 : ℚ) by norm_num]
  exact coverp000011011111
theorem coverp00001101111 : Covers (-443761639/4000000 : ℚ) vp00001101111 := join_branches bp000011011110 bp000011011111
private noncomputable def vp0000110111011_0 : Blocks := edgeBlocks% "full/vectors/0000110111011-V-0000.bin"
noncomputable def vp0000110111011 : Blocks := vp0000110111011_0
theorem coverp0000110111011 : Covers (-442761639/1000000 : ℚ) vp0000110111011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110111010_0 : Blocks := edgeBlocks% "full/vectors/0000110111010-V-0000.bin"
noncomputable def vp0000110111010 : Blocks := vp0000110111010_0
theorem coverp0000110111010 : Covers (-441761639/1000000 : ℚ) vp0000110111010 := cover_leaf (by decide +kernel)
private noncomputable def vp000011011101_0 : Blocks := edgeBlocks% "full/vectors/000011011101-V-0000.bin"
noncomputable def vp000011011101 : Blocks := vp000011011101_0
private theorem bp0000110111010 : Branch 0 (-441761639/2000000 : ℚ) vp000011011101 := by
  apply branch_left_normalized (c:=vp0000110111010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-441761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-441761639/1000000 : ℚ) by norm_num]
  exact coverp0000110111010
private noncomputable def ep0000110111011_0 : Blocks := edgeBlocks% "full/vectors/0000110111011-E-0000.bin"
noncomputable def ep0000110111011 : Blocks := ep0000110111011_0
private theorem idp0000110111011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011011101.list =
    C ((2:ℤ)^116) * horner X vp0000110111011.list + horner X ep0000110111011.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110111011 : Branch 1 (-441761639/2000000 : ℚ) vp000011011101 := by
  apply branch_checked idp0000110111011 (by positivity) (by decide +kernel)
  rw [show 2*(-441761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-442761639/1000000 : ℚ) by norm_num]
  exact coverp0000110111011
theorem coverp000011011101 : Covers (-441761639/2000000 : ℚ) vp000011011101 := join_branches bp0000110111010 bp0000110111011
private noncomputable def vp0000110111001_0 : Blocks := edgeBlocks% "full/vectors/0000110111001-V-0000.bin"
noncomputable def vp0000110111001 : Blocks := vp0000110111001_0
theorem coverp0000110111001 : Covers (-440761639/1000000 : ℚ) vp0000110111001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110111000_0 : Blocks := edgeBlocks% "full/vectors/0000110111000-V-0000.bin"
noncomputable def vp0000110111000 : Blocks := vp0000110111000_0
theorem coverp0000110111000 : Covers (-439761639/1000000 : ℚ) vp0000110111000 := cover_leaf (by decide +kernel)
private noncomputable def vp000011011100_0 : Blocks := edgeBlocks% "full/vectors/000011011100-V-0000.bin"
noncomputable def vp000011011100 : Blocks := vp000011011100_0
private theorem bp0000110111000 : Branch 0 (-439761639/2000000 : ℚ) vp000011011100 := by
  apply branch_left_normalized (c:=vp0000110111000) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-439761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-439761639/1000000 : ℚ) by norm_num]
  exact coverp0000110111000
private noncomputable def ep0000110111001_0 : Blocks := edgeBlocks% "full/vectors/0000110111001-E-0000.bin"
noncomputable def ep0000110111001 : Blocks := ep0000110111001_0
private theorem idp0000110111001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011011100.list =
    C ((2:ℤ)^115) * horner X vp0000110111001.list + horner X ep0000110111001.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110111001 : Branch 1 (-439761639/2000000 : ℚ) vp000011011100 := by
  apply branch_checked idp0000110111001 (by positivity) (by decide +kernel)
  rw [show 2*(-439761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-440761639/1000000 : ℚ) by norm_num]
  exact coverp0000110111001
theorem coverp000011011100 : Covers (-439761639/2000000 : ℚ) vp000011011100 := join_branches bp0000110111000 bp0000110111001
private noncomputable def vp00001101110_0 : Blocks := edgeBlocks% "full/vectors/00001101110-V-0000.bin"
private noncomputable def vp00001101110_1 : Blocks := edgeBlocks% "full/vectors/00001101110-V-0001.bin"
noncomputable def vp00001101110 : Blocks := (Blocks.join vp00001101110_0 vp00001101110_1)
private theorem bp000011011100 : Branch 0 (-439761639/4000000 : ℚ) vp00001101110 := by
  apply branch_left_normalized (c:=vp000011011100) (k:=0) (m:=109) (by decide +kernel)
  rw [show 2*(-439761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-439761639/2000000 : ℚ) by norm_num]
  exact coverp000011011100
private noncomputable def ep000011011101_0 : Blocks := edgeBlocks% "full/vectors/000011011101-E-0000.bin"
private noncomputable def ep000011011101_1 : Blocks := edgeBlocks% "full/vectors/000011011101-E-0001.bin"
noncomputable def ep000011011101 : Blocks := (Blocks.join ep000011011101_0 ep000011011101_1)
private theorem idp000011011101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001101110.list =
    C ((2:ℤ)^213) * horner X vp000011011101.list + horner X ep000011011101.list := by
  exact edge_identity (B := (2:ℤ)^393) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011011101 : Branch 1 (-439761639/4000000 : ℚ) vp00001101110 := by
  apply branch_checked idp000011011101 (by positivity) (by decide +kernel)
  rw [show 2*(-439761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-441761639/2000000 : ℚ) by norm_num]
  exact coverp000011011101
theorem coverp00001101110 : Covers (-439761639/4000000 : ℚ) vp00001101110 := join_branches bp000011011100 bp000011011101
private noncomputable def vp0000110111_0 : Blocks := edgeBlocks% "full/vectors/0000110111-V-0000.bin"
private noncomputable def vp0000110111_1 : Blocks := edgeBlocks% "full/vectors/0000110111-V-0001.bin"
private noncomputable def vp0000110111_2 : Blocks := edgeBlocks% "full/vectors/0000110111-V-0002.bin"
private noncomputable def vp0000110111_3 : Blocks := edgeBlocks% "full/vectors/0000110111-V-0003.bin"
noncomputable def vp0000110111 : Blocks := (Blocks.join (Blocks.join vp0000110111_0 vp0000110111_1) (Blocks.join vp0000110111_2 vp0000110111_3))
private theorem bp00001101110 : Branch 0 (-439761639/8000000 : ℚ) vp0000110111 := by
  apply branch_left_normalized (c:=vp00001101110) (k:=0) (m:=202) (by decide +kernel)
  rw [show 2*(-439761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-439761639/4000000 : ℚ) by norm_num]
  exact coverp00001101110
private noncomputable def ep00001101111_0 : Blocks := edgeBlocks% "full/vectors/00001101111-E-0000.bin"
private noncomputable def ep00001101111_1 : Blocks := edgeBlocks% "full/vectors/00001101111-E-0001.bin"
private noncomputable def ep00001101111_2 : Blocks := edgeBlocks% "full/vectors/00001101111-E-0002.bin"
private noncomputable def ep00001101111_3 : Blocks := edgeBlocks% "full/vectors/00001101111-E-0003.bin"
noncomputable def ep00001101111 : Blocks := (Blocks.join (Blocks.join ep00001101111_0 ep00001101111_1) (Blocks.join ep00001101111_2 ep00001101111_3))
private theorem idp00001101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110111.list =
    C ((2:ℤ)^410) * horner X vp00001101111.list + horner X ep00001101111.list := by
  exact edge_identity (B := (2:ℤ)^678) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101111 : Branch 1 (-439761639/8000000 : ℚ) vp0000110111 := by
  apply branch_checked idp00001101111 (by positivity) (by decide +kernel)
  rw [show 2*(-439761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-443761639/4000000 : ℚ) by norm_num]
  exact coverp00001101111
theorem coverp0000110111 : Covers (-439761639/8000000 : ℚ) vp0000110111 := join_branches bp00001101110 bp00001101111
private noncomputable def vp0000110110111_0 : Blocks := edgeBlocks% "full/vectors/0000110110111-V-0000.bin"
noncomputable def vp0000110110111 : Blocks := vp0000110110111_0
theorem coverp0000110110111 : Covers (-438761639/1000000 : ℚ) vp0000110110111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110110110_0 : Blocks := edgeBlocks% "full/vectors/0000110110110-V-0000.bin"
noncomputable def vp0000110110110 : Blocks := vp0000110110110_0
theorem coverp0000110110110 : Covers (-437761639/1000000 : ℚ) vp0000110110110 := cover_leaf (by decide +kernel)
private noncomputable def vp000011011011_0 : Blocks := edgeBlocks% "full/vectors/000011011011-V-0000.bin"
noncomputable def vp000011011011 : Blocks := vp000011011011_0
private theorem bp0000110110110 : Branch 0 (-437761639/2000000 : ℚ) vp000011011011 := by
  apply branch_left_normalized (c:=vp0000110110110) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-437761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-437761639/1000000 : ℚ) by norm_num]
  exact coverp0000110110110
private noncomputable def ep0000110110111_0 : Blocks := edgeBlocks% "full/vectors/0000110110111-E-0000.bin"
noncomputable def ep0000110110111 : Blocks := ep0000110110111_0
private theorem idp0000110110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011011011.list =
    C ((2:ℤ)^114) * horner X vp0000110110111.list + horner X ep0000110110111.list := by
  exact edge_identity (B := (2:ℤ)^248) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110110111 : Branch 1 (-437761639/2000000 : ℚ) vp000011011011 := by
  apply branch_checked idp0000110110111 (by positivity) (by decide +kernel)
  rw [show 2*(-437761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-438761639/1000000 : ℚ) by norm_num]
  exact coverp0000110110111
theorem coverp000011011011 : Covers (-437761639/2000000 : ℚ) vp000011011011 := join_branches bp0000110110110 bp0000110110111
private noncomputable def vp0000110110101_0 : Blocks := edgeBlocks% "full/vectors/0000110110101-V-0000.bin"
noncomputable def vp0000110110101 : Blocks := vp0000110110101_0
theorem coverp0000110110101 : Covers (-436761639/1000000 : ℚ) vp0000110110101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110110100_0 : Blocks := edgeBlocks% "full/vectors/0000110110100-V-0000.bin"
noncomputable def vp0000110110100 : Blocks := vp0000110110100_0
theorem coverp0000110110100 : Covers (-435761639/1000000 : ℚ) vp0000110110100 := cover_leaf (by decide +kernel)
private noncomputable def vp000011011010_0 : Blocks := edgeBlocks% "full/vectors/000011011010-V-0000.bin"
noncomputable def vp000011011010 : Blocks := vp000011011010_0
private theorem bp0000110110100 : Branch 0 (-435761639/2000000 : ℚ) vp000011011010 := by
  apply branch_left_normalized (c:=vp0000110110100) (k:=0) (m:=61) (by decide +kernel)
  rw [show 2*(-435761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-435761639/1000000 : ℚ) by norm_num]
  exact coverp0000110110100
private noncomputable def ep0000110110101_0 : Blocks := edgeBlocks% "full/vectors/0000110110101-E-0000.bin"
noncomputable def ep0000110110101 : Blocks := ep0000110110101_0
private theorem idp0000110110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011011010.list =
    C ((2:ℤ)^116) * horner X vp0000110110101.list + horner X ep0000110110101.list := by
  exact edge_identity (B := (2:ℤ)^250) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110110101 : Branch 1 (-435761639/2000000 : ℚ) vp000011011010 := by
  apply branch_checked idp0000110110101 (by positivity) (by decide +kernel)
  rw [show 2*(-435761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-436761639/1000000 : ℚ) by norm_num]
  exact coverp0000110110101
theorem coverp000011011010 : Covers (-435761639/2000000 : ℚ) vp000011011010 := join_branches bp0000110110100 bp0000110110101
private noncomputable def vp00001101101_0 : Blocks := edgeBlocks% "full/vectors/00001101101-V-0000.bin"
private noncomputable def vp00001101101_1 : Blocks := edgeBlocks% "full/vectors/00001101101-V-0001.bin"
noncomputable def vp00001101101 : Blocks := (Blocks.join vp00001101101_0 vp00001101101_1)
private theorem bp000011011010 : Branch 0 (-435761639/4000000 : ℚ) vp00001101101 := by
  apply branch_left_normalized (c:=vp000011011010) (k:=0) (m:=109) (by decide +kernel)
  rw [show 2*(-435761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-435761639/2000000 : ℚ) by norm_num]
  exact coverp000011011010
private noncomputable def ep000011011011_0 : Blocks := edgeBlocks% "full/vectors/000011011011-E-0000.bin"
private noncomputable def ep000011011011_1 : Blocks := edgeBlocks% "full/vectors/000011011011-E-0001.bin"
noncomputable def ep000011011011 : Blocks := (Blocks.join ep000011011011_0 ep000011011011_1)
private theorem idp000011011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001101101.list =
    C ((2:ℤ)^216) * horner X vp000011011011.list + horner X ep000011011011.list := by
  exact edge_identity (B := (2:ℤ)^394) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011011011 : Branch 1 (-435761639/4000000 : ℚ) vp00001101101 := by
  apply branch_checked idp000011011011 (by positivity) (by decide +kernel)
  rw [show 2*(-435761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-437761639/2000000 : ℚ) by norm_num]
  exact coverp000011011011
theorem coverp00001101101 : Covers (-435761639/4000000 : ℚ) vp00001101101 := join_branches bp000011011010 bp000011011011
private noncomputable def vp0000110110011_0 : Blocks := edgeBlocks% "full/vectors/0000110110011-V-0000.bin"
noncomputable def vp0000110110011 : Blocks := vp0000110110011_0
theorem coverp0000110110011 : Covers (-434761639/1000000 : ℚ) vp0000110110011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110110010_0 : Blocks := edgeBlocks% "full/vectors/0000110110010-V-0000.bin"
noncomputable def vp0000110110010 : Blocks := vp0000110110010_0
theorem coverp0000110110010 : Covers (-433761639/1000000 : ℚ) vp0000110110010 := cover_leaf (by decide +kernel)
private noncomputable def vp000011011001_0 : Blocks := edgeBlocks% "full/vectors/000011011001-V-0000.bin"
noncomputable def vp000011011001 : Blocks := vp000011011001_0
private theorem bp0000110110010 : Branch 0 (-433761639/2000000 : ℚ) vp000011011001 := by
  apply branch_left_normalized (c:=vp0000110110010) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-433761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-433761639/1000000 : ℚ) by norm_num]
  exact coverp0000110110010
private noncomputable def ep0000110110011_0 : Blocks := edgeBlocks% "full/vectors/0000110110011-E-0000.bin"
noncomputable def ep0000110110011 : Blocks := ep0000110110011_0
private theorem idp0000110110011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011011001.list =
    C ((2:ℤ)^116) * horner X vp0000110110011.list + horner X ep0000110110011.list := by
  exact edge_identity (B := (2:ℤ)^251) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110110011 : Branch 1 (-433761639/2000000 : ℚ) vp000011011001 := by
  apply branch_checked idp0000110110011 (by positivity) (by decide +kernel)
  rw [show 2*(-433761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-434761639/1000000 : ℚ) by norm_num]
  exact coverp0000110110011
theorem coverp000011011001 : Covers (-433761639/2000000 : ℚ) vp000011011001 := join_branches bp0000110110010 bp0000110110011
private noncomputable def vp0000110110001_0 : Blocks := edgeBlocks% "full/vectors/0000110110001-V-0000.bin"
noncomputable def vp0000110110001 : Blocks := vp0000110110001_0
theorem coverp0000110110001 : Covers (-432761639/1000000 : ℚ) vp0000110110001 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110110000_0 : Blocks := edgeBlocks% "full/vectors/0000110110000-V-0000.bin"
noncomputable def vp0000110110000 : Blocks := vp0000110110000_0
theorem coverp0000110110000 : Covers (-431761639/1000000 : ℚ) vp0000110110000 := cover_leaf (by decide +kernel)
private noncomputable def vp000011011000_0 : Blocks := edgeBlocks% "full/vectors/000011011000-V-0000.bin"
noncomputable def vp000011011000 : Blocks := vp000011011000_0
private theorem bp0000110110000 : Branch 0 (-431761639/2000000 : ℚ) vp000011011000 := by
  apply branch_left_normalized (c:=vp0000110110000) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-431761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-431761639/1000000 : ℚ) by norm_num]
  exact coverp0000110110000
private noncomputable def ep0000110110001_0 : Blocks := edgeBlocks% "full/vectors/0000110110001-E-0000.bin"
noncomputable def ep0000110110001 : Blocks := ep0000110110001_0
private theorem idp0000110110001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011011000.list =
    C ((2:ℤ)^117) * horner X vp0000110110001.list + horner X ep0000110110001.list := by
  exact edge_identity (B := (2:ℤ)^252) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110110001 : Branch 1 (-431761639/2000000 : ℚ) vp000011011000 := by
  apply branch_checked idp0000110110001 (by positivity) (by decide +kernel)
  rw [show 2*(-431761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-432761639/1000000 : ℚ) by norm_num]
  exact coverp0000110110001
theorem coverp000011011000 : Covers (-431761639/2000000 : ℚ) vp000011011000 := join_branches bp0000110110000 bp0000110110001
private noncomputable def vp00001101100_0 : Blocks := edgeBlocks% "full/vectors/00001101100-V-0000.bin"
private noncomputable def vp00001101100_1 : Blocks := edgeBlocks% "full/vectors/00001101100-V-0001.bin"
noncomputable def vp00001101100 : Blocks := (Blocks.join vp00001101100_0 vp00001101100_1)
private theorem bp000011011000 : Branch 0 (-431761639/4000000 : ℚ) vp00001101100 := by
  apply branch_left_normalized (c:=vp000011011000) (k:=0) (m:=110) (by decide +kernel)
  rw [show 2*(-431761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-431761639/2000000 : ℚ) by norm_num]
  exact coverp000011011000
private noncomputable def ep000011011001_0 : Blocks := edgeBlocks% "full/vectors/000011011001-E-0000.bin"
private noncomputable def ep000011011001_1 : Blocks := edgeBlocks% "full/vectors/000011011001-E-0001.bin"
noncomputable def ep000011011001 : Blocks := (Blocks.join ep000011011001_0 ep000011011001_1)
private theorem idp000011011001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001101100.list =
    C ((2:ℤ)^217) * horner X vp000011011001.list + horner X ep000011011001.list := by
  exact edge_identity (B := (2:ℤ)^396) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011011001 : Branch 1 (-431761639/4000000 : ℚ) vp00001101100 := by
  apply branch_checked idp000011011001 (by positivity) (by decide +kernel)
  rw [show 2*(-431761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-433761639/2000000 : ℚ) by norm_num]
  exact coverp000011011001
theorem coverp00001101100 : Covers (-431761639/4000000 : ℚ) vp00001101100 := join_branches bp000011011000 bp000011011001
private noncomputable def vp0000110110_0 : Blocks := edgeBlocks% "full/vectors/0000110110-V-0000.bin"
private noncomputable def vp0000110110_1 : Blocks := edgeBlocks% "full/vectors/0000110110-V-0001.bin"
private noncomputable def vp0000110110_2 : Blocks := edgeBlocks% "full/vectors/0000110110-V-0002.bin"
private noncomputable def vp0000110110_3 : Blocks := edgeBlocks% "full/vectors/0000110110-V-0003.bin"
noncomputable def vp0000110110 : Blocks := (Blocks.join (Blocks.join vp0000110110_0 vp0000110110_1) (Blocks.join vp0000110110_2 vp0000110110_3))
private theorem bp00001101100 : Branch 0 (-431761639/8000000 : ℚ) vp0000110110 := by
  apply branch_left_normalized (c:=vp00001101100) (k:=0) (m:=204) (by decide +kernel)
  rw [show 2*(-431761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-431761639/4000000 : ℚ) by norm_num]
  exact coverp00001101100
private noncomputable def ep00001101101_0 : Blocks := edgeBlocks% "full/vectors/00001101101-E-0000.bin"
private noncomputable def ep00001101101_1 : Blocks := edgeBlocks% "full/vectors/00001101101-E-0001.bin"
private noncomputable def ep00001101101_2 : Blocks := edgeBlocks% "full/vectors/00001101101-E-0002.bin"
private noncomputable def ep00001101101_3 : Blocks := edgeBlocks% "full/vectors/00001101101-E-0003.bin"
noncomputable def ep00001101101 : Blocks := (Blocks.join (Blocks.join ep00001101101_0 ep00001101101_1) (Blocks.join ep00001101101_2 ep00001101101_3))
private theorem idp00001101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110110.list =
    C ((2:ℤ)^417) * horner X vp00001101101.list + horner X ep00001101101.list := by
  exact edge_identity (B := (2:ℤ)^685) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101101 : Branch 1 (-431761639/8000000 : ℚ) vp0000110110 := by
  apply branch_checked idp00001101101 (by positivity) (by decide +kernel)
  rw [show 2*(-431761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-435761639/4000000 : ℚ) by norm_num]
  exact coverp00001101101
theorem coverp0000110110 : Covers (-431761639/8000000 : ℚ) vp0000110110 := join_branches bp00001101100 bp00001101101
private noncomputable def vp000011011_0 : Blocks := edgeBlocks% "full/vectors/000011011-V-0000.bin"
private noncomputable def vp000011011_1 : Blocks := edgeBlocks% "full/vectors/000011011-V-0001.bin"
private noncomputable def vp000011011_2 : Blocks := edgeBlocks% "full/vectors/000011011-V-0002.bin"
private noncomputable def vp000011011_3 : Blocks := edgeBlocks% "full/vectors/000011011-V-0003.bin"
private noncomputable def vp000011011_4 : Blocks := edgeBlocks% "full/vectors/000011011-V-0004.bin"
private noncomputable def vp000011011_5 : Blocks := edgeBlocks% "full/vectors/000011011-V-0005.bin"
noncomputable def vp000011011 : Blocks := (Blocks.join (Blocks.join vp000011011_0 (Blocks.join vp000011011_1 vp000011011_2)) (Blocks.join vp000011011_3 (Blocks.join vp000011011_4 vp000011011_5)))
private theorem bp0000110110 : Branch 0 (-431761639/16000000 : ℚ) vp000011011 := by
  apply branch_left_normalized (c:=vp0000110110) (k:=0) (m:=392) (by decide +kernel)
  rw [show 2*(-431761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-431761639/8000000 : ℚ) by norm_num]
  exact coverp0000110110
private noncomputable def ep0000110111_0 : Blocks := edgeBlocks% "full/vectors/0000110111-E-0000.bin"
private noncomputable def ep0000110111_1 : Blocks := edgeBlocks% "full/vectors/0000110111-E-0001.bin"
private noncomputable def ep0000110111_2 : Blocks := edgeBlocks% "full/vectors/0000110111-E-0002.bin"
private noncomputable def ep0000110111_3 : Blocks := edgeBlocks% "full/vectors/0000110111-E-0003.bin"
private noncomputable def ep0000110111_4 : Blocks := edgeBlocks% "full/vectors/0000110111-E-0004.bin"
private noncomputable def ep0000110111_5 : Blocks := edgeBlocks% "full/vectors/0000110111-E-0005.bin"
noncomputable def ep0000110111 : Blocks := (Blocks.join (Blocks.join ep0000110111_0 (Blocks.join ep0000110111_1 ep0000110111_2)) (Blocks.join ep0000110111_3 (Blocks.join ep0000110111_4 ep0000110111_5)))
private theorem idp0000110111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011011.list =
    C ((2:ℤ)^812) * horner X vp0000110111.list + horner X ep0000110111.list := by
  exact edge_identity (B := (2:ℤ)^1256) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110111 : Branch 1 (-431761639/16000000 : ℚ) vp000011011 := by
  apply branch_checked idp0000110111 (by positivity) (by decide +kernel)
  rw [show 2*(-431761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-439761639/8000000 : ℚ) by norm_num]
  exact coverp0000110111
theorem coverp000011011 : Covers (-431761639/16000000 : ℚ) vp000011011 := join_branches bp0000110110 bp0000110111
private noncomputable def vp0000110101111_0 : Blocks := edgeBlocks% "full/vectors/0000110101111-V-0000.bin"
noncomputable def vp0000110101111 : Blocks := vp0000110101111_0
theorem coverp0000110101111 : Covers (-430761639/1000000 : ℚ) vp0000110101111 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110101110_0 : Blocks := edgeBlocks% "full/vectors/0000110101110-V-0000.bin"
noncomputable def vp0000110101110 : Blocks := vp0000110101110_0
theorem coverp0000110101110 : Covers (-429761639/1000000 : ℚ) vp0000110101110 := cover_leaf (by decide +kernel)
private noncomputable def vp000011010111_0 : Blocks := edgeBlocks% "full/vectors/000011010111-V-0000.bin"
noncomputable def vp000011010111 : Blocks := vp000011010111_0
private theorem bp0000110101110 : Branch 0 (-429761639/2000000 : ℚ) vp000011010111 := by
  apply branch_left_normalized (c:=vp0000110101110) (k:=0) (m:=62) (by decide +kernel)
  rw [show 2*(-429761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-429761639/1000000 : ℚ) by norm_num]
  exact coverp0000110101110
private noncomputable def ep0000110101111_0 : Blocks := edgeBlocks% "full/vectors/0000110101111-E-0000.bin"
noncomputable def ep0000110101111 : Blocks := ep0000110101111_0
private theorem idp0000110101111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011010111.list =
    C ((2:ℤ)^117) * horner X vp0000110101111.list + horner X ep0000110101111.list := by
  exact edge_identity (B := (2:ℤ)^253) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110101111 : Branch 1 (-429761639/2000000 : ℚ) vp000011010111 := by
  apply branch_checked idp0000110101111 (by positivity) (by decide +kernel)
  rw [show 2*(-429761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-430761639/1000000 : ℚ) by norm_num]
  exact coverp0000110101111
theorem coverp000011010111 : Covers (-429761639/2000000 : ℚ) vp000011010111 := join_branches bp0000110101110 bp0000110101111
private noncomputable def vp0000110101101_0 : Blocks := edgeBlocks% "full/vectors/0000110101101-V-0000.bin"
noncomputable def vp0000110101101 : Blocks := vp0000110101101_0
theorem coverp0000110101101 : Covers (-428761639/1000000 : ℚ) vp0000110101101 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110101100_0 : Blocks := edgeBlocks% "full/vectors/0000110101100-V-0000.bin"
noncomputable def vp0000110101100 : Blocks := vp0000110101100_0
theorem coverp0000110101100 : Covers (-427761639/1000000 : ℚ) vp0000110101100 := cover_leaf (by decide +kernel)
private noncomputable def vp000011010110_0 : Blocks := edgeBlocks% "full/vectors/000011010110-V-0000.bin"
noncomputable def vp000011010110 : Blocks := vp000011010110_0
private theorem bp0000110101100 : Branch 0 (-427761639/2000000 : ℚ) vp000011010110 := by
  apply branch_left_normalized (c:=vp0000110101100) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-427761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-427761639/1000000 : ℚ) by norm_num]
  exact coverp0000110101100
private noncomputable def ep0000110101101_0 : Blocks := edgeBlocks% "full/vectors/0000110101101-E-0000.bin"
noncomputable def ep0000110101101 : Blocks := ep0000110101101_0
private theorem idp0000110101101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011010110.list =
    C ((2:ℤ)^118) * horner X vp0000110101101.list + horner X ep0000110101101.list := by
  exact edge_identity (B := (2:ℤ)^254) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110101101 : Branch 1 (-427761639/2000000 : ℚ) vp000011010110 := by
  apply branch_checked idp0000110101101 (by positivity) (by decide +kernel)
  rw [show 2*(-427761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-428761639/1000000 : ℚ) by norm_num]
  exact coverp0000110101101
theorem coverp000011010110 : Covers (-427761639/2000000 : ℚ) vp000011010110 := join_branches bp0000110101100 bp0000110101101
private noncomputable def vp00001101011_0 : Blocks := edgeBlocks% "full/vectors/00001101011-V-0000.bin"
private noncomputable def vp00001101011_1 : Blocks := edgeBlocks% "full/vectors/00001101011-V-0001.bin"
noncomputable def vp00001101011 : Blocks := (Blocks.join vp00001101011_0 vp00001101011_1)
private theorem bp000011010110 : Branch 0 (-427761639/4000000 : ℚ) vp00001101011 := by
  apply branch_left_normalized (c:=vp000011010110) (k:=0) (m:=111) (by decide +kernel)
  rw [show 2*(-427761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-427761639/2000000 : ℚ) by norm_num]
  exact coverp000011010110
private noncomputable def ep000011010111_0 : Blocks := edgeBlocks% "full/vectors/000011010111-E-0000.bin"
private noncomputable def ep000011010111_1 : Blocks := edgeBlocks% "full/vectors/000011010111-E-0001.bin"
noncomputable def ep000011010111 : Blocks := (Blocks.join ep000011010111_0 ep000011010111_1)
private theorem idp000011010111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001101011.list =
    C ((2:ℤ)^219) * horner X vp000011010111.list + horner X ep000011010111.list := by
  exact edge_identity (B := (2:ℤ)^400) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011010111 : Branch 1 (-427761639/4000000 : ℚ) vp00001101011 := by
  apply branch_checked idp000011010111 (by positivity) (by decide +kernel)
  rw [show 2*(-427761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-429761639/2000000 : ℚ) by norm_num]
  exact coverp000011010111
theorem coverp00001101011 : Covers (-427761639/4000000 : ℚ) vp00001101011 := join_branches bp000011010110 bp000011010111
private noncomputable def vp0000110101011_0 : Blocks := edgeBlocks% "full/vectors/0000110101011-V-0000.bin"
noncomputable def vp0000110101011 : Blocks := vp0000110101011_0
theorem coverp0000110101011 : Covers (-426761639/1000000 : ℚ) vp0000110101011 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110101010_0 : Blocks := edgeBlocks% "full/vectors/0000110101010-V-0000.bin"
noncomputable def vp0000110101010 : Blocks := vp0000110101010_0
theorem coverp0000110101010 : Covers (-425761639/1000000 : ℚ) vp0000110101010 := cover_leaf (by decide +kernel)
private noncomputable def vp000011010101_0 : Blocks := edgeBlocks% "full/vectors/000011010101-V-0000.bin"
noncomputable def vp000011010101 : Blocks := vp000011010101_0
private theorem bp0000110101010 : Branch 0 (-425761639/2000000 : ℚ) vp000011010101 := by
  apply branch_left_normalized (c:=vp0000110101010) (k:=0) (m:=63) (by decide +kernel)
  rw [show 2*(-425761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-425761639/1000000 : ℚ) by norm_num]
  exact coverp0000110101010
private noncomputable def ep0000110101011_0 : Blocks := edgeBlocks% "full/vectors/0000110101011-E-0000.bin"
noncomputable def ep0000110101011 : Blocks := ep0000110101011_0
private theorem idp0000110101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011010101.list =
    C ((2:ℤ)^119) * horner X vp0000110101011.list + horner X ep0000110101011.list := by
  exact edge_identity (B := (2:ℤ)^257) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110101011 : Branch 1 (-425761639/2000000 : ℚ) vp000011010101 := by
  apply branch_checked idp0000110101011 (by positivity) (by decide +kernel)
  rw [show 2*(-425761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-426761639/1000000 : ℚ) by norm_num]
  exact coverp0000110101011
theorem coverp000011010101 : Covers (-425761639/2000000 : ℚ) vp000011010101 := join_branches bp0000110101010 bp0000110101011
private noncomputable def vp0000110101001_0 : Blocks := edgeBlocks% "full/vectors/0000110101001-V-0000.bin"
noncomputable def vp0000110101001 : Blocks := vp0000110101001_0
theorem coverp0000110101001 : Covers (-424761639/1000000 : ℚ) vp0000110101001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101010001_0 : Blocks := edgeBlocks% "full/vectors/00001101010001-V-0000.bin"
noncomputable def vp00001101010001 : Blocks := vp00001101010001_0
theorem coverp00001101010001 : Covers (-424261639/500000 : ℚ) vp00001101010001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101010000_0 : Blocks := edgeBlocks% "full/vectors/00001101010000-V-0000.bin"
noncomputable def vp00001101010000 : Blocks := vp00001101010000_0
theorem coverp00001101010000 : Covers (-423761639/500000 : ℚ) vp00001101010000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110101000_0 : Blocks := edgeBlocks% "full/vectors/0000110101000-V-0000.bin"
noncomputable def vp0000110101000 : Blocks := vp0000110101000_0
private theorem bp00001101010000 : Branch 0 (-423761639/1000000 : ℚ) vp0000110101000 := by
  apply branch_left_normalized (c:=vp00001101010000) (k:=0) (m:=39) (by decide +kernel)
  rw [show 2*(-423761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-423761639/500000 : ℚ) by norm_num]
  exact coverp00001101010000
private noncomputable def ep00001101010001_0 : Blocks := edgeBlocks% "full/vectors/00001101010001-E-0000.bin"
noncomputable def ep00001101010001 : Blocks := ep00001101010001_0
private theorem idp00001101010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110101000.list =
    C ((2:ℤ)^70) * horner X vp00001101010001.list + horner X ep00001101010001.list := by
  exact edge_identity (B := (2:ℤ)^187) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101010001 : Branch 1 (-423761639/1000000 : ℚ) vp0000110101000 := by
  apply branch_checked idp00001101010001 (by positivity) (by decide +kernel)
  rw [show 2*(-423761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-424261639/500000 : ℚ) by norm_num]
  exact coverp00001101010001
theorem coverp0000110101000 : Covers (-423761639/1000000 : ℚ) vp0000110101000 := join_branches bp00001101010000 bp00001101010001
private noncomputable def vp000011010100_0 : Blocks := edgeBlocks% "full/vectors/000011010100-V-0000.bin"
noncomputable def vp000011010100 : Blocks := vp000011010100_0
private theorem bp0000110101000 : Branch 0 (-423761639/2000000 : ℚ) vp000011010100 := by
  apply branch_left_normalized (c:=vp0000110101000) (k:=0) (m:=65) (by decide +kernel)
  rw [show 2*(-423761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-423761639/1000000 : ℚ) by norm_num]
  exact coverp0000110101000
private noncomputable def ep0000110101001_0 : Blocks := edgeBlocks% "full/vectors/0000110101001-E-0000.bin"
noncomputable def ep0000110101001 : Blocks := ep0000110101001_0
private theorem idp0000110101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011010100.list =
    C ((2:ℤ)^122) * horner X vp0000110101001.list + horner X ep0000110101001.list := by
  exact edge_identity (B := (2:ℤ)^261) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110101001 : Branch 1 (-423761639/2000000 : ℚ) vp000011010100 := by
  apply branch_checked idp0000110101001 (by positivity) (by decide +kernel)
  rw [show 2*(-423761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-424761639/1000000 : ℚ) by norm_num]
  exact coverp0000110101001
theorem coverp000011010100 : Covers (-423761639/2000000 : ℚ) vp000011010100 := join_branches bp0000110101000 bp0000110101001
private noncomputable def vp00001101010_0 : Blocks := edgeBlocks% "full/vectors/00001101010-V-0000.bin"
private noncomputable def vp00001101010_1 : Blocks := edgeBlocks% "full/vectors/00001101010-V-0001.bin"
noncomputable def vp00001101010 : Blocks := (Blocks.join vp00001101010_0 vp00001101010_1)
private theorem bp000011010100 : Branch 0 (-423761639/4000000 : ℚ) vp00001101010 := by
  apply branch_left_normalized (c:=vp000011010100) (k:=0) (m:=114) (by decide +kernel)
  rw [show 2*(-423761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-423761639/2000000 : ℚ) by norm_num]
  exact coverp000011010100
private noncomputable def ep000011010101_0 : Blocks := edgeBlocks% "full/vectors/000011010101-E-0000.bin"
private noncomputable def ep000011010101_1 : Blocks := edgeBlocks% "full/vectors/000011010101-E-0001.bin"
noncomputable def ep000011010101 : Blocks := (Blocks.join ep000011010101_0 ep000011010101_1)
private theorem idp000011010101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001101010.list =
    C ((2:ℤ)^224) * horner X vp000011010101.list + horner X ep000011010101.list := by
  exact edge_identity (B := (2:ℤ)^407) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011010101 : Branch 1 (-423761639/4000000 : ℚ) vp00001101010 := by
  apply branch_checked idp000011010101 (by positivity) (by decide +kernel)
  rw [show 2*(-423761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-425761639/2000000 : ℚ) by norm_num]
  exact coverp000011010101
theorem coverp00001101010 : Covers (-423761639/4000000 : ℚ) vp00001101010 := join_branches bp000011010100 bp000011010101
private noncomputable def vp0000110101_0 : Blocks := edgeBlocks% "full/vectors/0000110101-V-0000.bin"
private noncomputable def vp0000110101_1 : Blocks := edgeBlocks% "full/vectors/0000110101-V-0001.bin"
private noncomputable def vp0000110101_2 : Blocks := edgeBlocks% "full/vectors/0000110101-V-0002.bin"
private noncomputable def vp0000110101_3 : Blocks := edgeBlocks% "full/vectors/0000110101-V-0003.bin"
noncomputable def vp0000110101 : Blocks := (Blocks.join (Blocks.join vp0000110101_0 vp0000110101_1) (Blocks.join vp0000110101_2 vp0000110101_3))
private theorem bp00001101010 : Branch 0 (-423761639/8000000 : ℚ) vp0000110101 := by
  apply branch_left_normalized (c:=vp00001101010) (k:=0) (m:=209) (by decide +kernel)
  rw [show 2*(-423761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-423761639/4000000 : ℚ) by norm_num]
  exact coverp00001101010
private noncomputable def ep00001101011_0 : Blocks := edgeBlocks% "full/vectors/00001101011-E-0000.bin"
private noncomputable def ep00001101011_1 : Blocks := edgeBlocks% "full/vectors/00001101011-E-0001.bin"
private noncomputable def ep00001101011_2 : Blocks := edgeBlocks% "full/vectors/00001101011-E-0002.bin"
private noncomputable def ep00001101011_3 : Blocks := edgeBlocks% "full/vectors/00001101011-E-0003.bin"
noncomputable def ep00001101011 : Blocks := (Blocks.join (Blocks.join ep00001101011_0 ep00001101011_1) (Blocks.join ep00001101011_2 ep00001101011_3))
private theorem idp00001101011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110101.list =
    C ((2:ℤ)^427) * horner X vp00001101011.list + horner X ep00001101011.list := by
  exact edge_identity (B := (2:ℤ)^698) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101011 : Branch 1 (-423761639/8000000 : ℚ) vp0000110101 := by
  apply branch_checked idp00001101011 (by positivity) (by decide +kernel)
  rw [show 2*(-423761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-427761639/4000000 : ℚ) by norm_num]
  exact coverp00001101011
theorem coverp0000110101 : Covers (-423761639/8000000 : ℚ) vp0000110101 := join_branches bp00001101010 bp00001101011
private noncomputable def vp00001101001111_0 : Blocks := edgeBlocks% "full/vectors/00001101001111-V-0000.bin"
noncomputable def vp00001101001111 : Blocks := vp00001101001111_0
theorem coverp00001101001111 : Covers (-423261639/500000 : ℚ) vp00001101001111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101001110_0 : Blocks := edgeBlocks% "full/vectors/00001101001110-V-0000.bin"
noncomputable def vp00001101001110 : Blocks := vp00001101001110_0
theorem coverp00001101001110 : Covers (-422761639/500000 : ℚ) vp00001101001110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110100111_0 : Blocks := edgeBlocks% "full/vectors/0000110100111-V-0000.bin"
noncomputable def vp0000110100111 : Blocks := vp0000110100111_0
private theorem bp00001101001110 : Branch 0 (-422761639/1000000 : ℚ) vp0000110100111 := by
  apply branch_left_normalized (c:=vp00001101001110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-422761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-422761639/500000 : ℚ) by norm_num]
  exact coverp00001101001110
private noncomputable def ep00001101001111_0 : Blocks := edgeBlocks% "full/vectors/00001101001111-E-0000.bin"
noncomputable def ep00001101001111 : Blocks := ep00001101001111_0
private theorem idp00001101001111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110100111.list =
    C ((2:ℤ)^71) * horner X vp00001101001111.list + horner X ep00001101001111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101001111 : Branch 1 (-422761639/1000000 : ℚ) vp0000110100111 := by
  apply branch_checked idp00001101001111 (by positivity) (by decide +kernel)
  rw [show 2*(-422761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-423261639/500000 : ℚ) by norm_num]
  exact coverp00001101001111
theorem coverp0000110100111 : Covers (-422761639/1000000 : ℚ) vp0000110100111 := join_branches bp00001101001110 bp00001101001111
private noncomputable def vp00001101001101_0 : Blocks := edgeBlocks% "full/vectors/00001101001101-V-0000.bin"
noncomputable def vp00001101001101 : Blocks := vp00001101001101_0
theorem coverp00001101001101 : Covers (-422261639/500000 : ℚ) vp00001101001101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101001100_0 : Blocks := edgeBlocks% "full/vectors/00001101001100-V-0000.bin"
noncomputable def vp00001101001100 : Blocks := vp00001101001100_0
theorem coverp00001101001100 : Covers (-421761639/500000 : ℚ) vp00001101001100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110100110_0 : Blocks := edgeBlocks% "full/vectors/0000110100110-V-0000.bin"
noncomputable def vp0000110100110 : Blocks := vp0000110100110_0
private theorem bp00001101001100 : Branch 0 (-421761639/1000000 : ℚ) vp0000110100110 := by
  apply branch_left_normalized (c:=vp00001101001100) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-421761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-421761639/500000 : ℚ) by norm_num]
  exact coverp00001101001100
private noncomputable def ep00001101001101_0 : Blocks := edgeBlocks% "full/vectors/00001101001101-E-0000.bin"
noncomputable def ep00001101001101 : Blocks := ep00001101001101_0
private theorem idp00001101001101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110100110.list =
    C ((2:ℤ)^76) * horner X vp00001101001101.list + horner X ep00001101001101.list := by
  exact edge_identity (B := (2:ℤ)^198) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101001101 : Branch 1 (-421761639/1000000 : ℚ) vp0000110100110 := by
  apply branch_checked idp00001101001101 (by positivity) (by decide +kernel)
  rw [show 2*(-421761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-422261639/500000 : ℚ) by norm_num]
  exact coverp00001101001101
theorem coverp0000110100110 : Covers (-421761639/1000000 : ℚ) vp0000110100110 := join_branches bp00001101001100 bp00001101001101
private noncomputable def vp000011010011_0 : Blocks := edgeBlocks% "full/vectors/000011010011-V-0000.bin"
noncomputable def vp000011010011 : Blocks := vp000011010011_0
private theorem bp0000110100110 : Branch 0 (-421761639/2000000 : ℚ) vp000011010011 := by
  apply branch_left_normalized (c:=vp0000110100110) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-421761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-421761639/1000000 : ℚ) by norm_num]
  exact coverp0000110100110
private noncomputable def ep0000110100111_0 : Blocks := edgeBlocks% "full/vectors/0000110100111-E-0000.bin"
noncomputable def ep0000110100111 : Blocks := ep0000110100111_0
private theorem idp0000110100111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011010011.list =
    C ((2:ℤ)^129) * horner X vp0000110100111.list + horner X ep0000110100111.list := by
  exact edge_identity (B := (2:ℤ)^272) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110100111 : Branch 1 (-421761639/2000000 : ℚ) vp000011010011 := by
  apply branch_checked idp0000110100111 (by positivity) (by decide +kernel)
  rw [show 2*(-421761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-422761639/1000000 : ℚ) by norm_num]
  exact coverp0000110100111
theorem coverp000011010011 : Covers (-421761639/2000000 : ℚ) vp000011010011 := join_branches bp0000110100110 bp0000110100111
private noncomputable def vp00001101001011_0 : Blocks := edgeBlocks% "full/vectors/00001101001011-V-0000.bin"
noncomputable def vp00001101001011 : Blocks := vp00001101001011_0
theorem coverp00001101001011 : Covers (-421261639/500000 : ℚ) vp00001101001011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101001010_0 : Blocks := edgeBlocks% "full/vectors/00001101001010-V-0000.bin"
noncomputable def vp00001101001010 : Blocks := vp00001101001010_0
theorem coverp00001101001010 : Covers (-420761639/500000 : ℚ) vp00001101001010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110100101_0 : Blocks := edgeBlocks% "full/vectors/0000110100101-V-0000.bin"
noncomputable def vp0000110100101 : Blocks := vp0000110100101_0
private theorem bp00001101001010 : Branch 0 (-420761639/1000000 : ℚ) vp0000110100101 := by
  apply branch_left_normalized (c:=vp00001101001010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-420761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-420761639/500000 : ℚ) by norm_num]
  exact coverp00001101001010
private noncomputable def ep00001101001011_0 : Blocks := edgeBlocks% "full/vectors/00001101001011-E-0000.bin"
noncomputable def ep00001101001011 : Blocks := ep00001101001011_0
private theorem idp00001101001011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110100101.list =
    C ((2:ℤ)^70) * horner X vp00001101001011.list + horner X ep00001101001011.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101001011 : Branch 1 (-420761639/1000000 : ℚ) vp0000110100101 := by
  apply branch_checked idp00001101001011 (by positivity) (by decide +kernel)
  rw [show 2*(-420761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-421261639/500000 : ℚ) by norm_num]
  exact coverp00001101001011
theorem coverp0000110100101 : Covers (-420761639/1000000 : ℚ) vp0000110100101 := join_branches bp00001101001010 bp00001101001011
private noncomputable def vp00001101001001_0 : Blocks := edgeBlocks% "full/vectors/00001101001001-V-0000.bin"
noncomputable def vp00001101001001 : Blocks := vp00001101001001_0
theorem coverp00001101001001 : Covers (-420261639/500000 : ℚ) vp00001101001001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101001000_0 : Blocks := edgeBlocks% "full/vectors/00001101001000-V-0000.bin"
noncomputable def vp00001101001000 : Blocks := vp00001101001000_0
theorem coverp00001101001000 : Covers (-419761639/500000 : ℚ) vp00001101001000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110100100_0 : Blocks := edgeBlocks% "full/vectors/0000110100100-V-0000.bin"
noncomputable def vp0000110100100 : Blocks := vp0000110100100_0
private theorem bp00001101001000 : Branch 0 (-419761639/1000000 : ℚ) vp0000110100100 := by
  apply branch_left_normalized (c:=vp00001101001000) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-419761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-419761639/500000 : ℚ) by norm_num]
  exact coverp00001101001000
private noncomputable def ep00001101001001_0 : Blocks := edgeBlocks% "full/vectors/00001101001001-E-0000.bin"
noncomputable def ep00001101001001 : Blocks := ep00001101001001_0
private theorem idp00001101001001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110100100.list =
    C ((2:ℤ)^70) * horner X vp00001101001001.list + horner X ep00001101001001.list := by
  exact edge_identity (B := (2:ℤ)^191) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101001001 : Branch 1 (-419761639/1000000 : ℚ) vp0000110100100 := by
  apply branch_checked idp00001101001001 (by positivity) (by decide +kernel)
  rw [show 2*(-419761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-420261639/500000 : ℚ) by norm_num]
  exact coverp00001101001001
theorem coverp0000110100100 : Covers (-419761639/1000000 : ℚ) vp0000110100100 := join_branches bp00001101001000 bp00001101001001
private noncomputable def vp000011010010_0 : Blocks := edgeBlocks% "full/vectors/000011010010-V-0000.bin"
noncomputable def vp000011010010 : Blocks := vp000011010010_0
private theorem bp0000110100100 : Branch 0 (-419761639/2000000 : ℚ) vp000011010010 := by
  apply branch_left_normalized (c:=vp0000110100100) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-419761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-419761639/1000000 : ℚ) by norm_num]
  exact coverp0000110100100
private noncomputable def ep0000110100101_0 : Blocks := edgeBlocks% "full/vectors/0000110100101-E-0000.bin"
noncomputable def ep0000110100101 : Blocks := ep0000110100101_0
private theorem idp0000110100101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011010010.list =
    C ((2:ℤ)^121) * horner X vp0000110100101.list + horner X ep0000110100101.list := by
  exact edge_identity (B := (2:ℤ)^266) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110100101 : Branch 1 (-419761639/2000000 : ℚ) vp000011010010 := by
  apply branch_checked idp0000110100101 (by positivity) (by decide +kernel)
  rw [show 2*(-419761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-420761639/1000000 : ℚ) by norm_num]
  exact coverp0000110100101
theorem coverp000011010010 : Covers (-419761639/2000000 : ℚ) vp000011010010 := join_branches bp0000110100100 bp0000110100101
private noncomputable def vp00001101001_0 : Blocks := edgeBlocks% "full/vectors/00001101001-V-0000.bin"
private noncomputable def vp00001101001_1 : Blocks := edgeBlocks% "full/vectors/00001101001-V-0001.bin"
noncomputable def vp00001101001 : Blocks := (Blocks.join vp00001101001_0 vp00001101001_1)
private theorem bp000011010010 : Branch 0 (-419761639/4000000 : ℚ) vp00001101001 := by
  apply branch_left_normalized (c:=vp000011010010) (k:=0) (m:=116) (by decide +kernel)
  rw [show 2*(-419761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-419761639/2000000 : ℚ) by norm_num]
  exact coverp000011010010
private noncomputable def ep000011010011_0 : Blocks := edgeBlocks% "full/vectors/000011010011-E-0000.bin"
private noncomputable def ep000011010011_1 : Blocks := edgeBlocks% "full/vectors/000011010011-E-0001.bin"
noncomputable def ep000011010011 : Blocks := (Blocks.join ep000011010011_0 ep000011010011_1)
private theorem idp000011010011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001101001.list =
    C ((2:ℤ)^219) * horner X vp000011010011.list + horner X ep000011010011.list := by
  exact edge_identity (B := (2:ℤ)^412) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011010011 : Branch 1 (-419761639/4000000 : ℚ) vp00001101001 := by
  apply branch_checked idp000011010011 (by positivity) (by decide +kernel)
  rw [show 2*(-419761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-421761639/2000000 : ℚ) by norm_num]
  exact coverp000011010011
theorem coverp00001101001 : Covers (-419761639/4000000 : ℚ) vp00001101001 := join_branches bp000011010010 bp000011010011
private noncomputable def vp00001101000111_0 : Blocks := edgeBlocks% "full/vectors/00001101000111-V-0000.bin"
noncomputable def vp00001101000111 : Blocks := vp00001101000111_0
theorem coverp00001101000111 : Covers (-419261639/500000 : ℚ) vp00001101000111 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101000110_0 : Blocks := edgeBlocks% "full/vectors/00001101000110-V-0000.bin"
noncomputable def vp00001101000110 : Blocks := vp00001101000110_0
theorem coverp00001101000110 : Covers (-418761639/500000 : ℚ) vp00001101000110 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110100011_0 : Blocks := edgeBlocks% "full/vectors/0000110100011-V-0000.bin"
noncomputable def vp0000110100011 : Blocks := vp0000110100011_0
private theorem bp00001101000110 : Branch 0 (-418761639/1000000 : ℚ) vp0000110100011 := by
  apply branch_left_normalized (c:=vp00001101000110) (k:=0) (m:=40) (by decide +kernel)
  rw [show 2*(-418761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-418761639/500000 : ℚ) by norm_num]
  exact coverp00001101000110
private noncomputable def ep00001101000111_0 : Blocks := edgeBlocks% "full/vectors/00001101000111-E-0000.bin"
noncomputable def ep00001101000111 : Blocks := ep00001101000111_0
private theorem idp00001101000111 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110100011.list =
    C ((2:ℤ)^70) * horner X vp00001101000111.list + horner X ep00001101000111.list := by
  exact edge_identity (B := (2:ℤ)^190) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101000111 : Branch 1 (-418761639/1000000 : ℚ) vp0000110100011 := by
  apply branch_checked idp00001101000111 (by positivity) (by decide +kernel)
  rw [show 2*(-418761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-419261639/500000 : ℚ) by norm_num]
  exact coverp00001101000111
theorem coverp0000110100011 : Covers (-418761639/1000000 : ℚ) vp0000110100011 := join_branches bp00001101000110 bp00001101000111
private noncomputable def vp00001101000101_0 : Blocks := edgeBlocks% "full/vectors/00001101000101-V-0000.bin"
noncomputable def vp00001101000101 : Blocks := vp00001101000101_0
theorem coverp00001101000101 : Covers (-418261639/500000 : ℚ) vp00001101000101 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101000100_0 : Blocks := edgeBlocks% "full/vectors/00001101000100-V-0000.bin"
noncomputable def vp00001101000100 : Blocks := vp00001101000100_0
theorem coverp00001101000100 : Covers (-417761639/500000 : ℚ) vp00001101000100 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110100010_0 : Blocks := edgeBlocks% "full/vectors/0000110100010-V-0000.bin"
noncomputable def vp0000110100010 : Blocks := vp0000110100010_0
private theorem bp00001101000100 : Branch 0 (-417761639/1000000 : ℚ) vp0000110100010 := by
  apply branch_left_normalized (c:=vp00001101000100) (k:=0) (m:=41) (by decide +kernel)
  rw [show 2*(-417761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-417761639/500000 : ℚ) by norm_num]
  exact coverp00001101000100
private noncomputable def ep00001101000101_0 : Blocks := edgeBlocks% "full/vectors/00001101000101-E-0000.bin"
noncomputable def ep00001101000101 : Blocks := ep00001101000101_0
private theorem idp00001101000101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110100010.list =
    C ((2:ℤ)^72) * horner X vp00001101000101.list + horner X ep00001101000101.list := by
  exact edge_identity (B := (2:ℤ)^193) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101000101 : Branch 1 (-417761639/1000000 : ℚ) vp0000110100010 := by
  apply branch_checked idp00001101000101 (by positivity) (by decide +kernel)
  rw [show 2*(-417761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-418261639/500000 : ℚ) by norm_num]
  exact coverp00001101000101
theorem coverp0000110100010 : Covers (-417761639/1000000 : ℚ) vp0000110100010 := join_branches bp00001101000100 bp00001101000101
private noncomputable def vp000011010001_0 : Blocks := edgeBlocks% "full/vectors/000011010001-V-0000.bin"
noncomputable def vp000011010001 : Blocks := vp000011010001_0
private theorem bp0000110100010 : Branch 0 (-417761639/2000000 : ℚ) vp000011010001 := by
  apply branch_left_normalized (c:=vp0000110100010) (k:=0) (m:=67) (by decide +kernel)
  rw [show 2*(-417761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-417761639/1000000 : ℚ) by norm_num]
  exact coverp0000110100010
private noncomputable def ep0000110100011_0 : Blocks := edgeBlocks% "full/vectors/0000110100011-E-0000.bin"
noncomputable def ep0000110100011 : Blocks := ep0000110100011_0
private theorem idp0000110100011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011010001.list =
    C ((2:ℤ)^124) * horner X vp0000110100011.list + horner X ep0000110100011.list := by
  exact edge_identity (B := (2:ℤ)^267) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110100011 : Branch 1 (-417761639/2000000 : ℚ) vp000011010001 := by
  apply branch_checked idp0000110100011 (by positivity) (by decide +kernel)
  rw [show 2*(-417761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-418761639/1000000 : ℚ) by norm_num]
  exact coverp0000110100011
theorem coverp000011010001 : Covers (-417761639/2000000 : ℚ) vp000011010001 := join_branches bp0000110100010 bp0000110100011
private noncomputable def vp00001101000011_0 : Blocks := edgeBlocks% "full/vectors/00001101000011-V-0000.bin"
noncomputable def vp00001101000011 : Blocks := vp00001101000011_0
theorem coverp00001101000011 : Covers (-417261639/500000 : ℚ) vp00001101000011 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101000010_0 : Blocks := edgeBlocks% "full/vectors/00001101000010-V-0000.bin"
noncomputable def vp00001101000010 : Blocks := vp00001101000010_0
theorem coverp00001101000010 : Covers (-416761639/500000 : ℚ) vp00001101000010 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110100001_0 : Blocks := edgeBlocks% "full/vectors/0000110100001-V-0000.bin"
noncomputable def vp0000110100001 : Blocks := vp0000110100001_0
private theorem bp00001101000010 : Branch 0 (-416761639/1000000 : ℚ) vp0000110100001 := by
  apply branch_left_normalized (c:=vp00001101000010) (k:=0) (m:=42) (by decide +kernel)
  rw [show 2*(-416761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-416761639/500000 : ℚ) by norm_num]
  exact coverp00001101000010
private noncomputable def ep00001101000011_0 : Blocks := edgeBlocks% "full/vectors/00001101000011-E-0000.bin"
noncomputable def ep00001101000011 : Blocks := ep00001101000011_0
private theorem idp00001101000011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110100001.list =
    C ((2:ℤ)^73) * horner X vp00001101000011.list + horner X ep00001101000011.list := by
  exact edge_identity (B := (2:ℤ)^195) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101000011 : Branch 1 (-416761639/1000000 : ℚ) vp0000110100001 := by
  apply branch_checked idp00001101000011 (by positivity) (by decide +kernel)
  rw [show 2*(-416761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-417261639/500000 : ℚ) by norm_num]
  exact coverp00001101000011
theorem coverp0000110100001 : Covers (-416761639/1000000 : ℚ) vp0000110100001 := join_branches bp00001101000010 bp00001101000011
private noncomputable def vp00001101000001_0 : Blocks := edgeBlocks% "full/vectors/00001101000001-V-0000.bin"
noncomputable def vp00001101000001 : Blocks := vp00001101000001_0
theorem coverp00001101000001 : Covers (-416261639/500000 : ℚ) vp00001101000001 := cover_leaf (by decide +kernel)
private noncomputable def vp00001101000000_0 : Blocks := edgeBlocks% "full/vectors/00001101000000-V-0000.bin"
noncomputable def vp00001101000000 : Blocks := vp00001101000000_0
theorem coverp00001101000000 : Covers (-415761639/500000 : ℚ) vp00001101000000 := cover_leaf (by decide +kernel)
private noncomputable def vp0000110100000_0 : Blocks := edgeBlocks% "full/vectors/0000110100000-V-0000.bin"
noncomputable def vp0000110100000 : Blocks := vp0000110100000_0
private theorem bp00001101000000 : Branch 0 (-415761639/1000000 : ℚ) vp0000110100000 := by
  apply branch_left_normalized (c:=vp00001101000000) (k:=0) (m:=43) (by decide +kernel)
  rw [show 2*(-415761639/1000000 : ℚ) - ((0:ℤ):ℚ) = (-415761639/500000 : ℚ) by norm_num]
  exact coverp00001101000000
private noncomputable def ep00001101000001_0 : Blocks := edgeBlocks% "full/vectors/00001101000001-E-0000.bin"
noncomputable def ep00001101000001 : Blocks := ep00001101000001_0
private theorem idp00001101000001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110100000.list =
    C ((2:ℤ)^73) * horner X vp00001101000001.list + horner X ep00001101000001.list := by
  exact edge_identity (B := (2:ℤ)^197) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101000001 : Branch 1 (-415761639/1000000 : ℚ) vp0000110100000 := by
  apply branch_checked idp00001101000001 (by positivity) (by decide +kernel)
  rw [show 2*(-415761639/1000000 : ℚ) - ((1:ℤ):ℚ) = (-416261639/500000 : ℚ) by norm_num]
  exact coverp00001101000001
theorem coverp0000110100000 : Covers (-415761639/1000000 : ℚ) vp0000110100000 := join_branches bp00001101000000 bp00001101000001
private noncomputable def vp000011010000_0 : Blocks := edgeBlocks% "full/vectors/000011010000-V-0000.bin"
noncomputable def vp000011010000 : Blocks := vp000011010000_0
private theorem bp0000110100000 : Branch 0 (-415761639/2000000 : ℚ) vp000011010000 := by
  apply branch_left_normalized (c:=vp0000110100000) (k:=0) (m:=69) (by decide +kernel)
  rw [show 2*(-415761639/2000000 : ℚ) - ((0:ℤ):ℚ) = (-415761639/1000000 : ℚ) by norm_num]
  exact coverp0000110100000
private noncomputable def ep0000110100001_0 : Blocks := edgeBlocks% "full/vectors/0000110100001-E-0000.bin"
noncomputable def ep0000110100001 : Blocks := ep0000110100001_0
private theorem idp0000110100001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011010000.list =
    C ((2:ℤ)^126) * horner X vp0000110100001.list + horner X ep0000110100001.list := by
  exact edge_identity (B := (2:ℤ)^272) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110100001 : Branch 1 (-415761639/2000000 : ℚ) vp000011010000 := by
  apply branch_checked idp0000110100001 (by positivity) (by decide +kernel)
  rw [show 2*(-415761639/2000000 : ℚ) - ((1:ℤ):ℚ) = (-416761639/1000000 : ℚ) by norm_num]
  exact coverp0000110100001
theorem coverp000011010000 : Covers (-415761639/2000000 : ℚ) vp000011010000 := join_branches bp0000110100000 bp0000110100001
private noncomputable def vp00001101000_0 : Blocks := edgeBlocks% "full/vectors/00001101000-V-0000.bin"
private noncomputable def vp00001101000_1 : Blocks := edgeBlocks% "full/vectors/00001101000-V-0001.bin"
noncomputable def vp00001101000 : Blocks := (Blocks.join vp00001101000_0 vp00001101000_1)
private theorem bp000011010000 : Branch 0 (-415761639/4000000 : ℚ) vp00001101000 := by
  apply branch_left_normalized (c:=vp000011010000) (k:=0) (m:=118) (by decide +kernel)
  rw [show 2*(-415761639/4000000 : ℚ) - ((0:ℤ):ℚ) = (-415761639/2000000 : ℚ) by norm_num]
  exact coverp000011010000
private noncomputable def ep000011010001_0 : Blocks := edgeBlocks% "full/vectors/000011010001-E-0000.bin"
private noncomputable def ep000011010001_1 : Blocks := edgeBlocks% "full/vectors/000011010001-E-0001.bin"
noncomputable def ep000011010001 : Blocks := (Blocks.join ep000011010001_0 ep000011010001_1)
private theorem idp000011010001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001101000.list =
    C ((2:ℤ)^230) * horner X vp000011010001.list + horner X ep000011010001.list := by
  exact edge_identity (B := (2:ℤ)^420) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011010001 : Branch 1 (-415761639/4000000 : ℚ) vp00001101000 := by
  apply branch_checked idp000011010001 (by positivity) (by decide +kernel)
  rw [show 2*(-415761639/4000000 : ℚ) - ((1:ℤ):ℚ) = (-417761639/2000000 : ℚ) by norm_num]
  exact coverp000011010001
theorem coverp00001101000 : Covers (-415761639/4000000 : ℚ) vp00001101000 := join_branches bp000011010000 bp000011010001
private noncomputable def vp0000110100_0 : Blocks := edgeBlocks% "full/vectors/0000110100-V-0000.bin"
private noncomputable def vp0000110100_1 : Blocks := edgeBlocks% "full/vectors/0000110100-V-0001.bin"
private noncomputable def vp0000110100_2 : Blocks := edgeBlocks% "full/vectors/0000110100-V-0002.bin"
private noncomputable def vp0000110100_3 : Blocks := edgeBlocks% "full/vectors/0000110100-V-0003.bin"
noncomputable def vp0000110100 : Blocks := (Blocks.join (Blocks.join vp0000110100_0 vp0000110100_1) (Blocks.join vp0000110100_2 vp0000110100_3))
private theorem bp00001101000 : Branch 0 (-415761639/8000000 : ℚ) vp0000110100 := by
  apply branch_left_normalized (c:=vp00001101000) (k:=0) (m:=215) (by decide +kernel)
  rw [show 2*(-415761639/8000000 : ℚ) - ((0:ℤ):ℚ) = (-415761639/4000000 : ℚ) by norm_num]
  exact coverp00001101000
private noncomputable def ep00001101001_0 : Blocks := edgeBlocks% "full/vectors/00001101001-E-0000.bin"
private noncomputable def ep00001101001_1 : Blocks := edgeBlocks% "full/vectors/00001101001-E-0001.bin"
private noncomputable def ep00001101001_2 : Blocks := edgeBlocks% "full/vectors/00001101001-E-0002.bin"
private noncomputable def ep00001101001_3 : Blocks := edgeBlocks% "full/vectors/00001101001-E-0003.bin"
noncomputable def ep00001101001 : Blocks := (Blocks.join (Blocks.join ep00001101001_0 ep00001101001_1) (Blocks.join ep00001101001_2 ep00001101001_3))
private theorem idp00001101001 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp0000110100.list =
    C ((2:ℤ)^435) * horner X vp00001101001.list + horner X ep00001101001.list := by
  exact edge_identity (B := (2:ℤ)^714) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp00001101001 : Branch 1 (-415761639/8000000 : ℚ) vp0000110100 := by
  apply branch_checked idp00001101001 (by positivity) (by decide +kernel)
  rw [show 2*(-415761639/8000000 : ℚ) - ((1:ℤ):ℚ) = (-419761639/4000000 : ℚ) by norm_num]
  exact coverp00001101001
theorem coverp0000110100 : Covers (-415761639/8000000 : ℚ) vp0000110100 := join_branches bp00001101000 bp00001101001
private noncomputable def vp000011010_0 : Blocks := edgeBlocks% "full/vectors/000011010-V-0000.bin"
private noncomputable def vp000011010_1 : Blocks := edgeBlocks% "full/vectors/000011010-V-0001.bin"
private noncomputable def vp000011010_2 : Blocks := edgeBlocks% "full/vectors/000011010-V-0002.bin"
private noncomputable def vp000011010_3 : Blocks := edgeBlocks% "full/vectors/000011010-V-0003.bin"
private noncomputable def vp000011010_4 : Blocks := edgeBlocks% "full/vectors/000011010-V-0004.bin"
private noncomputable def vp000011010_5 : Blocks := edgeBlocks% "full/vectors/000011010-V-0005.bin"
private noncomputable def vp000011010_6 : Blocks := edgeBlocks% "full/vectors/000011010-V-0006.bin"
noncomputable def vp000011010 : Blocks := (Blocks.join (Blocks.join vp000011010_0 (Blocks.join vp000011010_1 vp000011010_2)) (Blocks.join (Blocks.join vp000011010_3 vp000011010_4) (Blocks.join vp000011010_5 vp000011010_6)))
private theorem bp0000110100 : Branch 0 (-415761639/16000000 : ℚ) vp000011010 := by
  apply branch_left_normalized (c:=vp0000110100) (k:=0) (m:=407) (by decide +kernel)
  rw [show 2*(-415761639/16000000 : ℚ) - ((0:ℤ):ℚ) = (-415761639/8000000 : ℚ) by norm_num]
  exact coverp0000110100
private noncomputable def ep0000110101_0 : Blocks := edgeBlocks% "full/vectors/0000110101-E-0000.bin"
private noncomputable def ep0000110101_1 : Blocks := edgeBlocks% "full/vectors/0000110101-E-0001.bin"
private noncomputable def ep0000110101_2 : Blocks := edgeBlocks% "full/vectors/0000110101-E-0002.bin"
private noncomputable def ep0000110101_3 : Blocks := edgeBlocks% "full/vectors/0000110101-E-0003.bin"
private noncomputable def ep0000110101_4 : Blocks := edgeBlocks% "full/vectors/0000110101-E-0004.bin"
private noncomputable def ep0000110101_5 : Blocks := edgeBlocks% "full/vectors/0000110101-E-0005.bin"
private noncomputable def ep0000110101_6 : Blocks := edgeBlocks% "full/vectors/0000110101-E-0006.bin"
noncomputable def ep0000110101 : Blocks := (Blocks.join (Blocks.join ep0000110101_0 (Blocks.join ep0000110101_1 ep0000110101_2)) (Blocks.join (Blocks.join ep0000110101_3 ep0000110101_4) (Blocks.join ep0000110101_5 ep0000110101_6)))
private theorem idp0000110101 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp000011010.list =
    C ((2:ℤ)^839) * horner X vp0000110101.list + horner X ep0000110101.list := by
  exact edge_identity (B := (2:ℤ)^1297) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp0000110101 : Branch 1 (-415761639/16000000 : ℚ) vp000011010 := by
  apply branch_checked idp0000110101 (by positivity) (by decide +kernel)
  rw [show 2*(-415761639/16000000 : ℚ) - ((1:ℤ):ℚ) = (-423761639/8000000 : ℚ) by norm_num]
  exact coverp0000110101
theorem coverp000011010 : Covers (-415761639/16000000 : ℚ) vp000011010 := join_branches bp0000110100 bp0000110101
private noncomputable def vp00001101_0 : Blocks := edgeBlocks% "full/vectors/00001101-V-0000.bin"
private noncomputable def vp00001101_1 : Blocks := edgeBlocks% "full/vectors/00001101-V-0001.bin"
private noncomputable def vp00001101_2 : Blocks := edgeBlocks% "full/vectors/00001101-V-0002.bin"
private noncomputable def vp00001101_3 : Blocks := edgeBlocks% "full/vectors/00001101-V-0003.bin"
private noncomputable def vp00001101_4 : Blocks := edgeBlocks% "full/vectors/00001101-V-0004.bin"
private noncomputable def vp00001101_5 : Blocks := edgeBlocks% "full/vectors/00001101-V-0005.bin"
private noncomputable def vp00001101_6 : Blocks := edgeBlocks% "full/vectors/00001101-V-0006.bin"
private noncomputable def vp00001101_7 : Blocks := edgeBlocks% "full/vectors/00001101-V-0007.bin"
private noncomputable def vp00001101_8 : Blocks := edgeBlocks% "full/vectors/00001101-V-0008.bin"
private noncomputable def vp00001101_9 : Blocks := edgeBlocks% "full/vectors/00001101-V-0009.bin"
private noncomputable def vp00001101_10 : Blocks := edgeBlocks% "full/vectors/00001101-V-0010.bin"
private noncomputable def vp00001101_11 : Blocks := edgeBlocks% "full/vectors/00001101-V-0011.bin"
noncomputable def vp00001101 : Blocks := (Blocks.join (Blocks.join (Blocks.join vp00001101_0 (Blocks.join vp00001101_1 vp00001101_2)) (Blocks.join vp00001101_3 (Blocks.join vp00001101_4 vp00001101_5))) (Blocks.join (Blocks.join vp00001101_6 (Blocks.join vp00001101_7 vp00001101_8)) (Blocks.join vp00001101_9 (Blocks.join vp00001101_10 vp00001101_11))))
private theorem bp000011010 : Branch 0 (-415761639/32000000 : ℚ) vp00001101 := by
  apply branch_left_normalized (c:=vp000011010) (k:=0) (m:=786) (by decide +kernel)
  rw [show 2*(-415761639/32000000 : ℚ) - ((0:ℤ):ℚ) = (-415761639/16000000 : ℚ) by norm_num]
  exact coverp000011010
private noncomputable def ep000011011_0 : Blocks := edgeBlocks% "full/vectors/000011011-E-0000.bin"
private noncomputable def ep000011011_1 : Blocks := edgeBlocks% "full/vectors/000011011-E-0001.bin"
private noncomputable def ep000011011_2 : Blocks := edgeBlocks% "full/vectors/000011011-E-0002.bin"
private noncomputable def ep000011011_3 : Blocks := edgeBlocks% "full/vectors/000011011-E-0003.bin"
private noncomputable def ep000011011_4 : Blocks := edgeBlocks% "full/vectors/000011011-E-0004.bin"
private noncomputable def ep000011011_5 : Blocks := edgeBlocks% "full/vectors/000011011-E-0005.bin"
private noncomputable def ep000011011_6 : Blocks := edgeBlocks% "full/vectors/000011011-E-0006.bin"
private noncomputable def ep000011011_7 : Blocks := edgeBlocks% "full/vectors/000011011-E-0007.bin"
private noncomputable def ep000011011_8 : Blocks := edgeBlocks% "full/vectors/000011011-E-0008.bin"
private noncomputable def ep000011011_9 : Blocks := edgeBlocks% "full/vectors/000011011-E-0009.bin"
private noncomputable def ep000011011_10 : Blocks := edgeBlocks% "full/vectors/000011011-E-0010.bin"
private noncomputable def ep000011011_11 : Blocks := edgeBlocks% "full/vectors/000011011-E-0011.bin"
noncomputable def ep000011011 : Blocks := (Blocks.join (Blocks.join (Blocks.join ep000011011_0 (Blocks.join ep000011011_1 ep000011011_2)) (Blocks.join ep000011011_3 (Blocks.join ep000011011_4 ep000011011_5))) (Blocks.join (Blocks.join ep000011011_6 (Blocks.join ep000011011_7 ep000011011_8)) (Blocks.join ep000011011_9 (Blocks.join ep000011011_10 ep000011011_11))))
private theorem idp000011011 : halfForm (X:ℤ[X]) (C (1:ℤ)) vp00001101.list =
    C ((2:ℤ)^1634) * horner X vp000011011.list + horner X ep000011011.list := by
  exact edge_identity (B := (2:ℤ)^2445) (by decide) (by positivity) (by positivity)
    (by decide +kernel) (by decide +kernel)
private theorem bp000011011 : Branch 1 (-415761639/32000000 : ℚ) vp00001101 := by
  apply branch_checked idp000011011 (by positivity) (by decide +kernel)
  rw [show 2*(-415761639/32000000 : ℚ) - ((1:ℤ):ℚ) = (-431761639/16000000 : ℚ) by norm_num]
  exact coverp000011011
theorem coverp00001101 : Covers (-415761639/32000000 : ℚ) vp00001101 := join_branches bp000011010 bp000011011
end NextProof.EdgeFull

